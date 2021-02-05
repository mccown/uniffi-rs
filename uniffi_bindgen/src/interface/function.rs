/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

//! # Function definitions for a `ComponentInterface`.
//!
//! This module converts function definitions from UDL into structures that
//! can be added to a `ComponentInterface`. A declaration in the UDL like this:
//!
//! ```
//! # let ci = uniffi_bindgen::interface::ComponentInterface::from_webidl(r##"
//! namespace example {
//!     string hello();
//! };
//! # "##)?;
//! # Ok::<(), anyhow::Error>(())
//! ```
//!
//! Will result in a [`Function`] member being added to the resulting [`ComponentInterface`]:
//!
//! ```
//! # use uniffi_bindgen::interface::Type;
//! # let ci = uniffi_bindgen::interface::ComponentInterface::from_webidl(r##"
//! # namespace example {
//! #     string hello();
//! # };
//! # "##)?;
//! let func = ci.get_function_definition("hello").unwrap();
//! assert_eq!(func.name(), "hello");
//! assert!(matches!(func.return_type(), Some(Type::String)));
//! assert_eq!(func.arguments().len(), 0);
//! # Ok::<(), anyhow::Error>(())
//! ```
use std::convert::TryFrom;
use std::hash::{Hash, Hasher};

use anyhow::{bail, Result};

use super::attributes::{parse_attributes, Attribute};
use super::ffi::{FFIArgument, FFIFunction};
use super::literal::{convert_default_value, Literal};
use super::types::Type;
use super::{APIConverter, ComponentInterface};

/// Represents a standalone function.
///
/// Each `Function` corresponds to a standalone function in the rust module,
/// and has a corresponding standalone function in the foreign language bindings.
///
/// In the FFI, this will be a standalone function with appropriately lowered types.
#[derive(Debug, Clone)]
pub struct Function {
    pub(super) name: String,
    pub(super) arguments: Vec<Argument>,
    pub(super) return_type: Option<Type>,
    pub(super) ffi_func: FFIFunction,
    pub(super) attributes: FunctionAttributes,
}

impl Function {
    pub fn name(&self) -> &str {
        &self.name
    }
    pub fn arguments(&self) -> Vec<&Argument> {
        self.arguments.iter().collect()
    }
    pub fn return_type(&self) -> Option<&Type> {
        self.return_type.as_ref()
    }
    pub fn ffi_func(&self) -> &FFIFunction {
        &self.ffi_func
    }

    pub fn throws(&self) -> Option<&str> {
        self.attributes.get_throws_err()
    }

    pub fn derive_ffi_func(&mut self, ci_prefix: &str) -> Result<()> {
        self.ffi_func.name.push_str(ci_prefix);
        self.ffi_func.name.push_str("_");
        self.ffi_func.name.push_str(&self.name);
        self.ffi_func.arguments = self.arguments.iter().map(|arg| arg.into()).collect();
        self.ffi_func.return_type = self.return_type.as_ref().map(|rt| rt.into());
        Ok(())
    }
}

impl Hash for Function {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // We don't include the FFIFunc in the hash calculation, because:
        //  - it is entirely determined by the other fields,
        //    so excluding it is safe.
        //  - its `name` property includes a checksum derived from  the very
        //    hash value we're trying to calculate here, so excluding it
        //    avoids a weird circular depenendency in the calculation.
        self.name.hash(state);
        self.arguments.hash(state);
        self.return_type.hash(state);
        self.attributes.hash(state);
    }
}

impl APIConverter<Function> for weedle::namespace::NamespaceMember<'_> {
    fn convert(&self, ci: &mut ComponentInterface) -> Result<Function> {
        match self {
            weedle::namespace::NamespaceMember::Operation(f) => f.convert(ci),
            _ => bail!("no support for namespace member type {:?} yet", self),
        }
    }
}

impl APIConverter<Function> for weedle::namespace::OperationNamespaceMember<'_> {
    fn convert(&self, ci: &mut ComponentInterface) -> Result<Function> {
        let return_type = ci.resolve_return_type_expression(&self.return_type)?;
        if let Some(Type::Object(_)) = return_type {
            bail!("Objects cannot currently be returned from functions");
        }
        Ok(Function {
            name: match self.identifier {
                None => bail!("anonymous functions are not supported {:?}", self),
                Some(id) => id.0.to_string(),
            },
            return_type,
            arguments: self.args.body.list.convert(ci)?,
            ffi_func: Default::default(),
            attributes: match &self.attributes {
                Some(attr) => FunctionAttributes::try_from(attr)?,
                None => Default::default(),
            },
        })
    }
}

/// Represents an argument to a function/constructor/method call.
///
/// Each argument has a name and a type, along with some optional metadata.
#[derive(Debug, Clone, Hash)]
pub struct Argument {
    pub(super) name: String,
    pub(super) type_: Type,
    pub(super) by_ref: bool,
    pub(super) optional: bool,
    pub(super) default: Option<Literal>,
}

impl Argument {
    pub fn name(&self) -> &str {
        &self.name
    }
    pub fn type_(&self) -> Type {
        self.type_.clone()
    }
    pub fn by_ref(&self) -> bool {
        self.by_ref
    }
    pub fn default_value(&self) -> Option<Literal> {
        self.default.clone()
    }
}

impl Into<FFIArgument> for &Argument {
    fn into(self: Self) -> FFIArgument {
        FFIArgument {
            name: self.name.clone(),
            type_: (&self.type_).into(),
        }
    }
}

impl APIConverter<Argument> for weedle::argument::Argument<'_> {
    fn convert(&self, ci: &mut ComponentInterface) -> Result<Argument> {
        match self {
            weedle::argument::Argument::Single(t) => t.convert(ci),
            weedle::argument::Argument::Variadic(_) => bail!("variadic arguments not supported"),
        }
    }
}

impl APIConverter<Argument> for weedle::argument::SingleArgument<'_> {
    fn convert(&self, ci: &mut ComponentInterface) -> Result<Argument> {
        let type_ = ci.resolve_type_expression(&self.type_)?;
        if let Type::Object(_) = type_ {
            bail!("Objects cannot currently be passed as arguments");
        }
        let default = match self.default {
            None => None,
            Some(v) => Some(convert_default_value(&v.value, &type_)?),
        };
        let by_ref = match &self.attributes {
            Some(attrs) => ArgumentAttributes::try_from(attrs)?.by_ref(),
            None => false,
        };
        Ok(Argument {
            name: self.identifier.0.to_string(),
            type_,
            by_ref,
            optional: self.optional.is_some(),
            default,
        })
    }
}

/// Represents UDL attributes that might appear on a function.
///
/// This supports the `[Throws=ErrorName]` attribute for functions that
/// can produce an error.
#[derive(Debug, Clone, Hash, Default)]
pub struct FunctionAttributes(Vec<Attribute>);

impl FunctionAttributes {
    pub(super) fn get_throws_err(&self) -> Option<&str> {
        self.0.iter().find_map(|attr| match attr {
            // This will hopefully return a helpful compilation error
            // if the error is not defined.
            Attribute::Throws(inner) => Some(inner.as_ref()),
            _ => None,
        })
    }
}

impl TryFrom<&weedle::attribute::ExtendedAttributeList<'_>> for FunctionAttributes {
    type Error = anyhow::Error;
    fn try_from(
        weedle_attributes: &weedle::attribute::ExtendedAttributeList<'_>,
    ) -> Result<Self, Self::Error> {
        let attrs = parse_attributes(weedle_attributes, |attr| match attr {
            Attribute::Throws(_) => Ok(()),
            _ => bail!(format!(
                "{:?} not supported for functions, methods or constructors",
                attr
            )),
        })?;
        Ok(Self(attrs))
    }
}

/// Represents UDL attributes that might appear on a function argument.
///
/// This supports the `[ByRef]` attribute for arguments that should be passed
/// by reference in the generated Rust scaffolding.
#[derive(Debug, Clone, Hash, Default)]
pub struct ArgumentAttributes(Vec<Attribute>);

impl ArgumentAttributes {
    fn by_ref(&self) -> bool {
        self.0.iter().any(|attr| matches!(attr, Attribute::ByRef))
    }
}

impl TryFrom<&weedle::attribute::ExtendedAttributeList<'_>> for ArgumentAttributes {
    type Error = anyhow::Error;
    fn try_from(
        weedle_attributes: &weedle::attribute::ExtendedAttributeList<'_>,
    ) -> Result<Self, Self::Error> {
        let attrs = parse_attributes(weedle_attributes, |attr| match attr {
            Attribute::ByRef => Ok(()),
            _ => bail!(format!("{:?} not supported for arguments", attr)),
        })?;
        Ok(Self(attrs))
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use weedle::Parse;

    #[test]
    fn test_throws_attribute() -> Result<()> {
        let (_, node) = weedle::attribute::ExtendedAttributeList::parse("[Throws=Error]").unwrap();
        let attrs = FunctionAttributes::try_from(&node).unwrap();
        assert!(matches!(attrs.get_throws_err(), Some("Error")));

        let (_, node) = weedle::attribute::ExtendedAttributeList::parse("[]").unwrap();
        let attrs = FunctionAttributes::try_from(&node).unwrap();
        assert!(matches!(attrs.get_throws_err(), None));

        Ok(())
    }

    #[test]
    fn test_other_attributes_not_supported_for_functions() -> Result<()> {
        let (_, node) =
            weedle::attribute::ExtendedAttributeList::parse("[Throws=Error, ByRef]").unwrap();
        let err = FunctionAttributes::try_from(&node).unwrap_err();
        assert_eq!(
            err.to_string(),
            "ByRef not supported for functions, methods or constructors"
        );
        Ok(())
    }

    #[test]
    fn test_byref_attribute() -> Result<()> {
        let (_, node) = weedle::attribute::ExtendedAttributeList::parse("[ByRef]").unwrap();
        let attrs = ArgumentAttributes::try_from(&node).unwrap();
        assert!(matches!(attrs.by_ref(), true));

        let (_, node) = weedle::attribute::ExtendedAttributeList::parse("[]").unwrap();
        let attrs = ArgumentAttributes::try_from(&node).unwrap();
        assert!(matches!(attrs.by_ref(), false));

        Ok(())
    }

    #[test]
    fn test_other_attributes_not_supported_for_arguments() -> Result<()> {
        let (_, node) =
            weedle::attribute::ExtendedAttributeList::parse("[Throws=Error, ByRef]").unwrap();
        let err = ArgumentAttributes::try_from(&node).unwrap_err();
        assert_eq!(
            err.to_string(),
            "Throws(\"Error\") not supported for arguments"
        );
        Ok(())
    }

    #[test]
    fn test_minimal_and_rich_function() -> Result<()> {
        let ci = ComponentInterface::from_webidl(
            r##"
            namespace test {
                void minimal();
                [Throws=TestError]
                sequence<string?> rich(u32 arg1, TestDict arg2);
            };
            [Error]
            enum TestError { "err" };
            dictionary TestDict {
                u32 field;
            };
        "##,
        )?;

        let func1 = ci.get_function_definition("minimal").unwrap();
        assert_eq!(func1.name(), "minimal");
        assert!(func1.return_type().is_none());
        assert!(func1.throws().is_none());
        assert_eq!(func1.arguments().len(), 0);

        let func2 = ci.get_function_definition("rich").unwrap();
        assert_eq!(func2.name(), "rich");
        assert_eq!(
            func2.return_type().unwrap().canonical_name(),
            "SequenceOptionalstring"
        );
        assert!(matches!(func2.throws(), Some("TestError")));
        assert_eq!(func2.arguments().len(), 2);
        assert_eq!(func2.arguments()[0].name(), "arg1");
        assert_eq!(func2.arguments()[0].type_().canonical_name(), "u32");
        assert_eq!(func2.arguments()[1].name(), "arg2");
        assert_eq!(
            func2.arguments()[1].type_().canonical_name(),
            "RecordTestDict"
        );
        Ok(())
    }
}

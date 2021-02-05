/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

//! # Enum definitions for a `ComponentInterface`.
//!
//! This module converts enum definition from UDL into structures that can be
//! added to a `ComponentInterface`. A declaration in the UDL like this:
//!
//! ```
//! # let ci = uniffi_bindgen::interface::ComponentInterface::from_webidl(r##"
//! # namespace example {};
//! enum Example {
//!   "one",
//!   "two"
//! };
//! # "##)?;
//! # Ok::<(), anyhow::Error>(())
//! ```
//!
//! Will result in a [`Enum`] member being added to the resulting [`ComponentInterface`]:
//!
//! ```
//! # let ci = uniffi_bindgen::interface::ComponentInterface::from_webidl(r##"
//! # namespace example {};
//! # enum Example {
//! #   "one",
//! #   "two"
//! # };
//! # "##)?;
//! let e = ci.get_enum_definition("Example").unwrap();
//! assert_eq!(e.name(), "Example");
//! assert_eq!(e.variants().len(), 2);
//! assert_eq!(e.variants()[0], "one");
//! assert_eq!(e.variants()[1], "two");
//! # Ok::<(), anyhow::Error>(())
//! ```

use std::convert::TryFrom;

use anyhow::{bail, Result};

use super::attributes::{parse_attributes, Attribute};
use super::{APIConverter, ComponentInterface};

/// Represents a simple C-style enum, with named variants.
///
/// In the FFI these are turned into a plain u32, with variants numbered
/// in the order they appear in the declaration, starting from 1.
#[derive(Debug, Clone, Hash)]
pub struct Enum {
    pub(super) name: String,
    pub(super) variants: Vec<String>,
}

impl Enum {
    pub fn name(&self) -> &str {
        &self.name
    }
    pub fn variants(&self) -> Vec<&str> {
        self.variants.iter().map(|v| v.as_str()).collect()
    }
}

impl APIConverter<Enum> for weedle::EnumDefinition<'_> {
    fn convert(&self, _ci: &mut ComponentInterface) -> Result<Enum> {
        Ok(Enum {
            name: self.identifier.0.to_string(),
            variants: self
                .values
                .body
                .list
                .iter()
                .map(|v| v.0.to_string())
                .collect(),
        })
    }
}

/// Attributes that can be attached to an `enum` definition in the UDL.
/// There's only one case here: using `[Error]` to mark an enum as an error class.
#[derive(Debug, Clone, Hash, Default)]
pub(super) struct EnumAttributes(Vec<Attribute>);

impl EnumAttributes {
    pub fn contains_error_attr(&self) -> bool {
        self.0.iter().any(|attr| attr.is_error())
    }
}

impl TryFrom<&weedle::attribute::ExtendedAttributeList<'_>> for EnumAttributes {
    type Error = anyhow::Error;
    fn try_from(
        weedle_attributes: &weedle::attribute::ExtendedAttributeList<'_>,
    ) -> Result<Self, Self::Error> {
        let attrs = parse_attributes(weedle_attributes, |attr| match attr {
            Attribute::Error => Ok(()),
            _ => bail!(format!("{:?} not supported for enums", attr)),
        })?;
        Ok(Self(attrs))
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use weedle::Parse;

    #[test]
    fn test_duplicate_variants() -> Result<()> {
        const UDL: &str = r#"
            namespace test{};
            // Weird, but currently allowed!
            // We should probably disallow this...
            enum Testing { "one", "two", "one" };
        "#;
        let ci = ComponentInterface::from_webidl(UDL).unwrap();
        assert_eq!(ci.iter_enum_definitions().len(), 1);
        assert_eq!(
            ci.get_enum_definition("Testing").unwrap().variants().len(),
            3
        );
        Ok(())
    }

    #[test]
    fn test_other_attributes_not_supported_for_enums() -> Result<()> {
        let (_, node) = weedle::attribute::ExtendedAttributeList::parse("[Error, ByRef]").unwrap();
        let err = EnumAttributes::try_from(&node).unwrap_err();
        assert_eq!(err.to_string(), "ByRef not supported for enums");
        Ok(())
    }
}

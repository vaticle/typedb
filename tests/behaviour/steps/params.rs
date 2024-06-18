/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::{borrow::Cow, convert::Infallible, fmt, str::FromStr};

use chrono::NaiveDateTime;
use concept::type_::{
    annotation::{
        Annotation as TypeDBAnnotation, AnnotationAbstract, AnnotationCardinality, AnnotationIndependent,
        AnnotationKey, AnnotationRegex,
    },
    object_type::ObjectType,
};
use cucumber::Parameter;
use encoding::{
    graph::type_::Kind as TypeDBTypeKind,
    value::{label::Label as TypeDBLabel, value::Value as TypeDBValue, value_type::ValueType as TypeDBValueType},
};
use itertools::Itertools;

use crate::assert::assert_matches;

#[derive(Debug, Parameter)]
#[param(name = "may_error", regex = "(; fails|)")]
pub(crate) enum MayError {
    False,
    True,
}

impl MayError {
    pub fn check<T: fmt::Debug, E: fmt::Debug>(&self, res: &Result<T, E>) {
        match self {
            MayError::False => {
                res.as_ref().unwrap();
            }
            MayError::True => {
                res.as_ref().unwrap_err();
            }
        };
    }

    pub fn expects_error(&self) -> bool {
        match self {
            MayError::True => true,
            MayError::False => false,
        }
    }
}

impl FromStr for MayError {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(match s {
            "; fails" => Self::True,
            "" => Self::False,
            invalid => return Err(format!("Invalid `MayError`: {invalid}")),
        })
    }
}

#[derive(Debug, Parameter)]
#[param(name = "boolean", regex = "(true|false)")]
pub(crate) enum Boolean {
    False,
    True,
}

macro_rules! check_boolean {
    ($boolean:ident, $expr:expr) => {
        match $boolean {
            $crate::params::Boolean::True => assert!($expr),
            $crate::params::Boolean::False => assert!(!$expr),
        }
    };
}
pub(crate) use check_boolean;
use concept::type_::annotation::{AnnotationDistinct, AnnotationUnique};

impl FromStr for Boolean {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(match s {
            "true" => Self::True,
            "false" => Self::False,
            invalid => return Err(format!("Invalid `Boolean`: {invalid}")),
        })
    }
}

#[derive(Debug, Parameter)]
#[param(name = "exists_or_doesnt", regex = "(exists|does not exist)")]
pub(crate) enum ExistsOrDoesnt {
    Exists,
    DoesNotExist,
}

impl ExistsOrDoesnt {
    pub fn check<T: fmt::Debug>(&self, scrutinee: &Option<T>, message: &str) {
        match (self, scrutinee) {
            (Self::Exists, Some(_)) | (Self::DoesNotExist, None) => (),
            (Self::Exists, None) => panic!("{message} does not exist"),
            (Self::DoesNotExist, Some(value)) => panic!("{message} exists: {value:?}"),
        }
    }
}

impl FromStr for ExistsOrDoesnt {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(match s {
            "exists" => Self::Exists,
            "does not exist" => Self::DoesNotExist,
            invalid => return Err(format!("Invalid `ExistsOrDoesnt`: {invalid}")),
        })
    }
}

#[derive(Debug, Parameter)]
#[param(name = "contains_or_doesnt", regex = "(contain|do not contain)")]
pub(crate) enum ContainsOrDoesnt {
    Contains,
    DoesNotContain,
}

impl ContainsOrDoesnt {
    pub fn check<T: PartialEq + fmt::Debug>(&self, expected: &[T], actual: &[T]) {
        let expected_contains = self.expected_contains();
        for expected_item in expected {
            assert_eq!(
                expected_contains,
                actual.contains(expected_item),
                "{:?} {} {:?} ",
                actual,
                if expected_contains { "contains" } else { "does not contain" },
                expected
            );
        }
    }

    pub fn expected_contains(&self) -> bool {
        match self {
            ContainsOrDoesnt::Contains => true,
            ContainsOrDoesnt::DoesNotContain => false,
        }
    }
}

impl FromStr for ContainsOrDoesnt {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(match s {
            "contain" => Self::Contains,
            "do not contain" => Self::DoesNotContain,
            invalid => return Err(format!("Invalid `ContainsOrDoesnt`: {invalid}")),
        })
    }
}

#[derive(Debug, Parameter)]
#[param(name = "type_label", regex = r"[A-Za-z0-9_:-]+")]
pub(crate) struct Label {
    label_string: String,
}

impl Default for Label {
    fn default() -> Self {
        unreachable!("Why is default called?");
    }
}

impl Label {
    pub fn to_typedb(&self) -> TypeDBLabel<'static> {
        TypeDBLabel::build(&self.label_string)
    }
}

impl FromStr for Label {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self { label_string: s.to_string() })
    }
}

#[derive(Debug, Parameter)]
#[param(name = "root_label", regex = r"(attribute|entity|relation)")]
pub(crate) struct RootLabel {
    kind: TypeDBTypeKind,
}

impl RootLabel {
    pub fn to_typedb(&self) -> TypeDBTypeKind {
        self.kind
    }
}

impl FromStr for RootLabel {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let kind = match s {
            "attribute" => TypeDBTypeKind::Attribute,
            "entity" => TypeDBTypeKind::Entity,
            "relation" => TypeDBTypeKind::Relation,
            _ => unreachable!(),
        };
        Ok(RootLabel { kind })
    }
}

#[derive(Debug, Parameter)]
#[param(name = "object_root_label", regex = r"(entity|relation)")]
pub(crate) struct ObjectRootLabel {
    kind: TypeDBTypeKind,
}

impl ObjectRootLabel {
    pub fn to_typedb(&self) -> TypeDBTypeKind {
        self.kind
    }

    pub fn assert(&self, object: &ObjectType<'_>) {
        match self.kind {
            TypeDBTypeKind::Entity => assert_matches!(object, ObjectType::Entity(_)),
            TypeDBTypeKind::Relation => assert_matches!(object, ObjectType::Relation(_)),
            _ => unreachable!("an ObjectRootLabel contains a non-object kind: {:?}", self.kind),
        }
    }
}

impl FromStr for ObjectRootLabel {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let kind = match s {
            "entity" => TypeDBTypeKind::Entity,
            "relation" => TypeDBTypeKind::Relation,
            _ => unreachable!(),
        };
        Ok(Self { kind })
    }
}

#[derive(Debug, Parameter)]
#[param(name = "value_type", regex = "(boolean|long|double|decimal|datetime(?:tz)?|duration|string)")]
pub(crate) enum ValueType {
    Boolean,
    Long,
    Double,
    Decimal,
    DateTime,
    DateTimeTZ,
    Duration,
    String,
}

impl ValueType {
    pub fn to_typedb(&self) -> TypeDBValueType {
        match self {
            ValueType::Boolean => TypeDBValueType::Boolean,
            ValueType::Long => TypeDBValueType::Long,
            ValueType::Double => TypeDBValueType::Double,
            ValueType::Decimal => TypeDBValueType::Decimal,
            ValueType::DateTime => TypeDBValueType::DateTime,
            ValueType::DateTimeTZ => TypeDBValueType::DateTimeTZ,
            ValueType::Duration => TypeDBValueType::Duration,
            ValueType::String => TypeDBValueType::String,
        }
    }
}

impl FromStr for ValueType {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(match s {
            "boolean" => Self::Boolean,
            "long" => Self::Long,
            "double" => Self::Double,
            "decimal" => Self::Decimal,
            "datetime" => Self::DateTime,
            "datetimetz" => Self::DateTimeTZ,
            "duration" => Self::Duration,
            "string" => Self::String,
            _ => panic!("Unrecognised value type"),
        })
    }
}

#[derive(Debug, Default, Parameter)]
#[param(name = "value", regex = ".*?")]
pub(crate) struct Value {
    raw_value: String,
}

impl Value {
    pub fn into_typedb(self, value_type: TypeDBValueType) -> TypeDBValue<'static> {
        match value_type {
            TypeDBValueType::Boolean => TypeDBValue::Boolean(self.raw_value.parse().unwrap()),
            TypeDBValueType::Long => TypeDBValue::Long(self.raw_value.parse().unwrap()),
            TypeDBValueType::Double => TypeDBValue::Double(self.raw_value.parse().unwrap()),
            TypeDBValueType::Decimal => todo!(),
            TypeDBValueType::DateTime => {
                TypeDBValue::DateTime(NaiveDateTime::parse_from_str(&self.raw_value, "%Y-%m-%d %H:%M:%S").unwrap())
            }
            TypeDBValueType::DateTimeTZ => {
                let (date_time, tz) = self.raw_value.rsplit_once(' ').unwrap();
                let date_time = NaiveDateTime::parse_from_str(date_time.trim(), "%Y-%m-%d %H:%M:%S");
                let tz = tz.trim().parse().unwrap();
                TypeDBValue::DateTimeTZ(date_time.unwrap().and_local_timezone(tz).unwrap())
            }
            TypeDBValueType::Duration => TypeDBValue::Duration(self.raw_value.parse().unwrap()),
            TypeDBValueType::String => TypeDBValue::String(Cow::Owned(self.raw_value)),
            TypeDBValueType::Struct(_) => todo!(),
        }
    }
}

impl FromStr for Value {
    type Err = Infallible;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self { raw_value: s.to_owned() })
    }
}

#[derive(Debug, Parameter)]
#[param(name = "annotation", regex = r"@[a-z]+(?:\([^)]+\))?")]
pub(crate) struct Annotation {
    typedb_annotation: TypeDBAnnotation,
}

impl Annotation {
    pub fn into_typedb(self) -> TypeDBAnnotation {
        self.typedb_annotation
    }
}

impl FromStr for Annotation {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        // This will have to be smarter to parse annotations out.
        let typedb_annotation = match s {
            "@abstract" => TypeDBAnnotation::Abstract(AnnotationAbstract),
            "@independent" => TypeDBAnnotation::Independent(AnnotationIndependent),
            "@key" => TypeDBAnnotation::Key(AnnotationKey),
            "@unique" => TypeDBAnnotation::Unique(AnnotationUnique),
            "@distinct" => TypeDBAnnotation::Distinct(AnnotationDistinct),
            "@cascade" => return Err("Not implemented!".to_owned()), //TypeDBAnnotation::Cascade(AnnotationCascade),
            "@replace" => return Err("Not implemented!".to_owned()), //TypeDBAnnotation::Replace(AnnotationReplace),
            subkey if subkey.starts_with("@subkey") => {
                return Err("Not implemented!".to_owned())
                // assert!(
                //     subkey.starts_with(r#"@subkey("#) && subkey.ends_with(r#")"#),
                //     r#"Invalid @subkey format: {subkey:?}. Expected "@subkey(LABEL)""#
                // );
                // let label = &subkey[r#"@subkey("#.len()..subkey.len() - r#")"#.len()];
                // TypeDBAnnotation::Subkey(AnnotationSubkey::new(label.to_owned()))
            }
            values if values.starts_with("@values") => {
                return Err("Not implemented!".to_owned())
                // assert!(
                //     values.starts_with("@values(") && values.ends_with(')'),
                //     r#"Invalid @values format: {values:?}. Expected "@values(val1, val2, ..., valN)""#
                // );
                // let values = values["@card(".len()..values.len() - ")".len()].trim();
                // let values =
                //     values.split(',');
                // TypeDBAnnotation::Values(AnnotationValues::new(values))
            }
            range if range.starts_with("@range") => {
                return Err("Not implemented!".to_owned())
                // assert!(
                //     range.starts_with("@range(") && range.ends_with(')'),
                //     r#"Invalid @range format: {range:?}. Expected "@range(min, max)""#
                // );
                // let range = range["@range(".len()..range.len() - ")".len()].trim();
                // let (min, max) =
                //     range.split_once(',').map(|(min, max)| (min.trim(), Some(max.trim()))).unwrap_or((range, None));
                // TypeDBAnnotation::Range(AnnotationRange::new(
                //     min.parse().unwrap(),
                //     max.map(str::parse).transpose().unwrap(),
                // ))
            }
            regex if regex.starts_with("@regex") => {
                assert!(
                    regex.starts_with(r#"@regex(""#) && regex.ends_with(r#"")"#),
                    r#"Invalid @regex format: {regex:?}. Expected "@regex("regex-here")""#
                );
                let regex = &regex[r#"@regex(""#.len()..regex.len() - r#"")"#.len()];
                TypeDBAnnotation::Regex(AnnotationRegex::new(regex.to_owned()))
            }
            card if card.starts_with("@card") => {
                assert!(
                    card.starts_with("@card(") && card.ends_with(')'),
                    r#"Invalid @card format: {card:?}. Expected "@card(min, max)""#
                );
                let card = card["@card(".len()..card.len() - ")".len()].trim();
                let (min, max) =
                    card.split_once(',').map(|(min, max)| (min.trim(), Some(max.trim()))).unwrap_or((card, None));
                TypeDBAnnotation::Cardinality(AnnotationCardinality::new(
                    min.parse().unwrap(),
                    max.map(str::parse).transpose().unwrap(),
                ))
            }
            _ => panic!("Unrecognised (or unimplemented) annotation: {s}"),
        };
        Ok(Self { typedb_annotation })
    }
}

#[derive(Debug, Parameter)]
#[param(name = "annotations", regex = r"@[a-z]+(?:\([^)]+\))?(?: +@[a-z]+(?:\([^)]+\))?)?")]
pub(crate) struct Annotations {
    typedb_annotations: Vec<TypeDBAnnotation>,
}

impl Annotations {
    pub fn into_typedb(self) -> Vec<TypeDBAnnotation> {
        self.typedb_annotations
    }
}

impl FromStr for Annotations {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut cursor = 0;

        let typedb_annotations = std::iter::from_fn(|| {
            if s.len() >= cursor {
                None
            } else {
                let next_at = if let Some(index) = s[cursor..].find('@') { cursor + index } else { s.len() };
                let anno = s[cursor..next_at].trim();
                cursor = next_at;
                Some(anno.parse::<Annotation>().map(|anno| anno.typedb_annotation))
            }
        })
        .try_collect()?;

        Ok(Self { typedb_annotations })
    }
}

#[derive(Clone, Debug, Default, Parameter)]
#[param(name = "var", regex = r"\$[\w_-]+")]
pub struct Var {
    pub name: String,
}

impl FromStr for Var {
    type Err = Infallible;

    fn from_str(name: &str) -> Result<Self, Self::Err> {
        Ok(Self { name: name.to_owned() })
    }
}

#[derive(Clone, Debug, Default, Parameter)]
#[param(name = "vars", regex = r"\[(\$[\w_-]+(?:,\s*\$[\w_-]+)*)\]")]
pub struct Vars {
    pub names: Vec<String>,
}

impl FromStr for Vars {
    type Err = Infallible;

    fn from_str(str: &str) -> Result<Self, Self::Err> {
        Ok(Self { names: str.split(',').map(|name| name.trim().to_owned()).collect() })
    }
}

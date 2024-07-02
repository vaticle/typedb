/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub(crate) struct InfixID {
    bytes: [u8; InfixID::LENGTH],
}

impl InfixID {
    pub(crate) const LENGTH: usize = 1;

    pub(crate) const fn new(bytes: [u8; InfixID::LENGTH]) -> Self {
        InfixID { bytes }
    }

    pub(crate) fn bytes(&self) -> [u8; InfixID::LENGTH] {
        self.bytes
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum Infix {
    // Schema properties
    PropertyLabel,
    PropertyValueType,
    PropertyOrdering,
    PropertyOverride,

    PropertyAnnotationAbstract,
    PropertyAnnotationDistinct,
    PropertyAnnotationIndependent,
    PropertyAnnotationUnique,
    PropertyAnnotationKey,
    PropertyAnnotationCardinality,
    PropertyAnnotationRegex,
    PropertyAnnotationCascade,
    _PropertyAnnotationLast, // marker to indicate end of reserved range for annotations

    // Data properties
    PropertyHasOrder,
    PropertyRolePlayerOrder,
}

macro_rules! infix_functions {
    ($(
        $name:ident => $bytes:tt
    );*) => {
        pub(crate) const fn infix_id(&self) -> InfixID {
            let bytes = match self {
                $(
                    Self::$name => {&$bytes}
                )*
            };
            InfixID::new(*bytes)
        }

        pub(crate) fn from_infix_id(infix_id: InfixID) -> Self {
            #[deny(unreachable_patterns)] // fail to compile if any infixes are the same
            match infix_id.bytes() {
                $(
                    $bytes => {Self::$name}
                )*
                _ => unreachable!(),
            }
       }
   };
}

impl Infix {
    pub const ANNOTATION_MIN: Self = Self::PropertyAnnotationAbstract;
    pub const ANNOTATION_MAX: Self = Self::_PropertyAnnotationLast;

    infix_functions!(
        PropertyLabel => [0];
        PropertyValueType => [1];
        PropertyOrdering => [2];
        PropertyOverride => [3];

       // Reserve: range 50 - 99 to store annotations with a value type - see InfixID::<CONSTANTS>
        PropertyAnnotationAbstract => [50];
        PropertyAnnotationDistinct => [51];
        PropertyAnnotationIndependent => [52];
        PropertyAnnotationUnique => [53];
        PropertyAnnotationKey => [54];
        PropertyAnnotationCardinality => [55];
        PropertyAnnotationRegex => [56];
        PropertyAnnotationCascade => [57];
        _PropertyAnnotationLast => [99];

        PropertyHasOrder => [100];
        PropertyRolePlayerOrder => [101]
    );
}

/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::collections::{HashMap, HashSet};

use crate::type_::{annotation::{Annotation, AnnotationCardinality, AnnotationKey}, KindAPI, type_manager::validation::SchemaValidationError};
use crate::type_::annotation::{AnnotationAbstract, AnnotationCategory, AnnotationDistinct, AnnotationIndependent, AnnotationRegex, AnnotationUnique};

pub(crate) fn are_annotations_compatible(
    subtype_annotation: Annotation,
    supertype_annotations: &Vec<Annotation>,
) -> Result<(), SchemaValidationError> {
    // match subtype_annotation {
    // Annotation::Abstract(_) => todo!(),
    // Annotation::Distinct(_) => todo!(),
    // Annotation::Independent(_) => todo!(),
    // Annotation::Key(key) => validate_key_is_compatible_with(key, supertype_annotations),
    // Annotation::Cardinality(cardinality) => {
    // validate_cardinalty_is_compatible_with(cardinality, supertype_annotations)
    // }
    // Annotation::Regex(_) => todo!(), // TODO: https://cs.stackexchange.com/a/9131 yikes. Can we just return Ok(())?
    // Annotation::Unique(_) => todo!(),
    // }
    Ok(())
}

fn validate_cardinality_is_compatible_with(
    subtype_cardinality: AnnotationCardinality,
    supertype_annotations: &Vec<Annotation>,
) -> Result<(), SchemaValidationError> {
    todo!()
}

fn validate_key_is_compatible_with(
    key: AnnotationKey,
    supertype_annotations: &Vec<Annotation>,
) -> Result<(), SchemaValidationError> {
    todo!()
}

fn contains_annotation_category<T, TAnnotation>(
    annotations_container: &HashMap<TAnnotation, T>,
    annotation_category: AnnotationCategory
) -> bool
    where
        TAnnotation : Clone + Into<Annotation>,
{
    annotations_container.iter()
        .map(|(annotation, _)| annotation.clone().into().category())
        .any(|annotation| annotation == annotation_category)
}

pub(crate) fn is_annotation_inheritable<T, TAnnotation>(
    supertype_annotation: &TAnnotation,
    effective_annotations: &HashMap<TAnnotation, T>,
) -> bool
where
    TAnnotation : Clone + Into<Annotation>,
{
    let supertype_annotation = supertype_annotation.clone().into();
    match supertype_annotation { // TODO: Make sure that it is tested correctly for all types!
        Annotation::Abstract(_) => false,
        | Annotation::Unique(_)
        | Annotation::Cardinality(_) => {
            if contains_annotation_category::<T, TAnnotation>(effective_annotations, AnnotationCategory::Key) {
                false
            } else {
                !contains_annotation_category::<T, TAnnotation>(effective_annotations, supertype_annotation.category())
            }
        },
        | Annotation::Distinct(_)
        | Annotation::Independent(_)
        | Annotation::Key(_)
        | Annotation::Regex(_)
        | Annotation::Cascade(_) => {
            !contains_annotation_category::<T, TAnnotation>(effective_annotations, supertype_annotation.category())
        }
    }
}

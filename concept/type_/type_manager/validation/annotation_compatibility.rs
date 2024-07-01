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

pub(crate) fn is_annotation_inheritable<T, TAnnotation>(
    supertype_annotation: &TAnnotation,
    effective_annotations: &HashMap<TAnnotation, T>,
) -> bool
where
    TAnnotation : Clone + Into<Annotation>,
{
    let supertype_category = supertype_annotation.clone().into().category();
    if !supertype_category.inheritable() {
        return false;
    }

    for (effective_annotation, _) in effective_annotations {
        let effective_category = effective_annotation.clone().into().category();
        if effective_category == supertype_category {
            return false;
        }
        if !effective_category.compatible_to_transitively_add(supertype_category) {
            return false;
        }
    }

    true
}

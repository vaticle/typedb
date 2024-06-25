/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::collections::{HashMap, HashSet};

use crate::type_::{annotation::{Annotation, AnnotationCardinality, AnnotationKey}, KindAPI, type_manager::validation::SchemaValidationError};

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

pub(crate) fn is_annotation_inherited<T: KindAPI<'static>>(
    supertype_annotation: &T::AnnotationType,
    // effective_annotations: &HashMap<T::AnnotationType, T>,
    effective_annotations: &HashSet<T::AnnotationType>,
) -> bool {
    // In most cases we just need to see if the build_up_annotations contains nothing that 'overrides' it
    // match supertype_annotation {
    // Annotation::Abstract(_) => false,
    // Annotation::Distinct(_) => todo!(),
    // Annotation::Independent(_) => todo!(),
    // Annotation::Key(key) => todo!(),
    // Annotation::Cardinality(cardinality) => todo!(),
    // Annotation::Regex(_) => todo!(),
    // Annotation::Unique(_) => todo!(),
    // }
    true
}

pub(crate) fn is_edge_annotation_inherited<EDGE>(
    supertype_annotation: &Annotation,
    effective_annotations: &HashMap<Annotation, EDGE>,
) -> bool {
    // In most cases we just need to see if the build_up_annotations contains nothing that 'overrides' it
    // match supertype_annotation {
    // Annotation::Abstract(_) => false,
    // Annotation::Distinct(_) => todo!(),
    // Annotation::Independent(_) => todo!(),
    // Annotation::Key(key) => todo!(),
    // Annotation::Cardinality(cardinality) => todo!(),
    // Annotation::Regex(_) => todo!(),
    // Annotation::Unique(_) => todo!(),
    // }
    true
}

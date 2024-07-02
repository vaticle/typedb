/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

/*
Affect of clause statements on inferred types from parent variables:

1. Conjunction: intersection over types
2. Disjunction: union over types
3. Optional: no effect (consider match $x isa person; try { $x has dob $dob; };)
4. Negation: no effect (advanced: subtraction over types when unspecialised: match $x isa person; not { $x isa child; }. However, unsafe in: match $x isa person; not { $x isa child, has name "bob"; }



---> can we come up with a general, nestable algorithm for handling negations being nested? Eg. effect of  a Disjunction(Negation(Disjunction(Conjunction(negation)))))....
Or even:
conjunction(disjunction(conjunction or conjunction))



match
$x isa person;
{ $x has name "john"; } or { $x has bday bill;}

=> actually, disjunctions compute a possibility space via unions across branches, then intersect that with parent.
=> it's a "contextual" operation - have to compute within a pattern, then apply it


Execution idea:
Add all variables to frontier, and add all types in category to its set.
Pick a variable.
For each constraint attached, addOrIntersect types possible for the neighbor variable, add var to frontier
Repeat for each variable in frontier.


Want: good error messages when impossibility arises:

match
$x isa person;
$y isa company;
($x, $y) isa friendship;

Error:
Given:
$x is any of [person, child, adult]
($x, $y) is any of [friendship, child-friendship]
Then $y is not satisfiable


Algorithm:
when we find an empty answer for a variable, we go back through its neighbors and build the stack
in reverse, through named variables.

We should assign a search order over variables, based on connectedness.
On error, show the inferred types for variables (in minimal original query format, either named or ($x, $y))
In the order that are connected to the variable.
 */

use concept::error::ConceptReadError;

pub mod pattern_type_inference;
mod seed_types;
pub mod type_inference;
pub mod value_type_inference;

#[derive(Debug)]
pub enum TypeInferenceError {
    ConceptRead { source: ConceptReadError },
    LabelNotResolved(String),
}

#[cfg(test)]
pub mod tests {
    use std::{
        borrow::Borrow,
        collections::{BTreeMap, BTreeSet},
        sync::Arc,
    };

    use answer::{variable::Variable, Type as TypeAnnotation};
    use concept::{
        thing::thing_manager::ThingManager,
        type_::{
            annotation::AnnotationAbstract, attribute_type::AttributeTypeAnnotation, type_manager::TypeManager,
            Ordering, OwnerAPI, PlayerAPI,
        },
    };
    use durability::wal::WAL;
    use encoding::{
        graph::{
            definition::definition_key_generator::DefinitionKeyGenerator,
            thing::vertex_generator::ThingVertexGenerator, type_::vertex_generator::TypeVertexGenerator,
        },
        value::label::Label,
        EncodingKeyspace,
    };
    use itertools::Itertools;
    use storage::{
        durability_client::WALClient,
        snapshot::{CommittableSnapshot, ReadableSnapshot, WritableSnapshot, WriteSnapshot},
        MVCCStorage,
    };
    use test_utils::{create_tmp_dir, init_logging};

    use crate::{
        inference::pattern_type_inference::{
            NestedTypeInferenceGraphDisjunction, TypeInferenceEdge, TypeInferenceGraph,
        },
        pattern::{conjunction::Conjunction, constraint::Constraint},
    };

    impl<'this> PartialEq<Self> for TypeInferenceEdge<'this> {
        fn eq(&self, other: &Self) -> bool {
            self.constraint == other.constraint
                && self.right == other.right
                && self.left == other.left
                && self.left_to_right == other.left_to_right
                && self.right_to_left == other.right_to_left
        }
    }

    impl<'this> Eq for TypeInferenceEdge<'this> {}

    impl<'this> PartialEq<Self> for TypeInferenceGraph<'this> {
        fn eq(&self, other: &Self) -> bool {
            self.vertices == other.vertices
                && self.edges == other.edges
                && self.nested_disjunctions == other.nested_disjunctions
        }
    }

    impl<'this> Eq for TypeInferenceGraph<'this> {}

    impl<'this> PartialEq<Self> for NestedTypeInferenceGraphDisjunction<'this> {
        fn eq(&self, other: &Self) -> bool {
            self.disjunction == other.disjunction
        }
    }

    impl<'this> Eq for NestedTypeInferenceGraphDisjunction<'this> {}

    pub(crate) fn setup_storage() -> Arc<MVCCStorage<WALClient>> {
        init_logging();
        let storage_path = create_tmp_dir();
        let wal = WAL::create(&storage_path).unwrap();
        let storage = Arc::new(
            MVCCStorage::<WALClient>::create::<EncodingKeyspace>("storage", &storage_path, WALClient::new(wal))
                .unwrap(),
        );

        let definition_key_generator = Arc::new(DefinitionKeyGenerator::new());
        let type_vertex_generator = Arc::new(TypeVertexGenerator::new());
        TypeManager::<WriteSnapshot<WALClient>>::initialise_types(
            storage.clone(),
            definition_key_generator.clone(),
            type_vertex_generator.clone(),
        )
        .unwrap();
        storage
    }

    pub(crate) fn managers<Snapshot: ReadableSnapshot>() -> (Arc<TypeManager<Snapshot>>, ThingManager<Snapshot>) {
        let definition_key_generator = Arc::new(DefinitionKeyGenerator::new());
        let type_vertex_generator = Arc::new(TypeVertexGenerator::new());
        let thing_vertex_generator = Arc::new(ThingVertexGenerator::new());
        let type_manager =
            Arc::new(TypeManager::new(definition_key_generator.clone(), type_vertex_generator.clone(), None));
        let thing_manager = ThingManager::new(thing_vertex_generator.clone(), type_manager.clone());

        (type_manager, thing_manager)
    }

    pub mod schema_consts {
        use std::{
            borrow::Borrow,
            collections::{BTreeMap, BTreeSet},
            sync::Arc,
        };

        use answer::{variable::Variable, Type as TypeAnnotation};
        use concept::{
            thing::thing_manager::ThingManager,
            type_::{
                annotation::AnnotationAbstract, attribute_type::AttributeTypeAnnotation, type_manager::TypeManager,
                Ordering, OwnerAPI, PlayerAPI,
            },
        };
        use encoding::{
            graph::{
                definition::definition_key_generator::DefinitionKeyGenerator,
                thing::vertex_generator::ThingVertexGenerator, type_::vertex_generator::TypeVertexGenerator,
            },
            value::{label::Label, value_type::ValueType},
            EncodingKeyspace,
        };
        use storage::{
            durability_client::WALClient,
            snapshot::{CommittableSnapshot, ReadableSnapshot, WritableSnapshot, WriteSnapshot},
            MVCCStorage,
        };
        pub(crate) const LABEL_ANIMAL: &str = "animal";
        pub(crate) const LABEL_CAT: &str = "cat";
        pub(crate) const LABEL_DOG: &str = "dog";

        pub(crate) const LABEL_NAME: &str = "name";
        pub(crate) const LABEL_CATNAME: &str = "cat-name";
        pub(crate) const LABEL_DOGNAME: &str = "dog-name";

        pub(crate) const LABEL_FEARS: &str = "fears";
        pub(crate) const LABEL_HAS_FEAR: &str = "has-fear";
        pub(crate) const LABEL_IS_FEARED: &str = "is-feared";

        pub(crate) fn setup_types<Snapshot: WritableSnapshot + CommittableSnapshot<WALClient>>(
            snapshot_: Snapshot,
            type_manager: &TypeManager<Snapshot>,
        ) -> (
            (TypeAnnotation, TypeAnnotation, TypeAnnotation),
            (TypeAnnotation, TypeAnnotation, TypeAnnotation),
            (TypeAnnotation, TypeAnnotation, TypeAnnotation),
        ) {
            // dog sub animal, owns dog-name; cat sub animal owns cat-name;
            // cat-name sub animal-name; dog-name sub animal-name;
            let mut snapshot = snapshot_;

            // Attributes
            let name = type_manager.create_attribute_type(&mut snapshot, &Label::build(LABEL_NAME), false).unwrap();
            let catname =
                type_manager.create_attribute_type(&mut snapshot, &Label::build(LABEL_CATNAME), false).unwrap();
            let dogname =
                type_manager.create_attribute_type(&mut snapshot, &Label::build(LABEL_DOGNAME), false).unwrap();
            name.set_annotation(&mut snapshot, type_manager, AttributeTypeAnnotation::Abstract(AnnotationAbstract))
                .unwrap();
            catname.set_supertype(&mut snapshot, type_manager, name.clone()).unwrap();
            dogname.set_supertype(&mut snapshot, type_manager, name.clone()).unwrap();

            name.set_value_type(&mut snapshot, type_manager, ValueType::String).unwrap();
            catname.set_value_type(&mut snapshot, type_manager, ValueType::String).unwrap();
            dogname.set_value_type(&mut snapshot, type_manager, ValueType::String).unwrap();

            // Entities
            let animal = type_manager.create_entity_type(&mut snapshot, &Label::build(LABEL_ANIMAL), false).unwrap();
            let cat = type_manager.create_entity_type(&mut snapshot, &Label::build(LABEL_CAT), false).unwrap();
            let dog = type_manager.create_entity_type(&mut snapshot, &Label::build(LABEL_DOG), false).unwrap();
            cat.set_supertype(&mut snapshot, type_manager, animal.clone()).unwrap();
            dog.set_supertype(&mut snapshot, type_manager, animal.clone()).unwrap();

            // Ownerships
            let animal_owns = animal.set_owns(&mut snapshot, type_manager, name.clone(), Ordering::Unordered).unwrap();
            let cat_owns = cat.set_owns(&mut snapshot, type_manager, catname.clone(), Ordering::Unordered).unwrap();
            let dog_owns = dog.set_owns(&mut snapshot, type_manager, dogname.clone(), Ordering::Unordered).unwrap();
            cat_owns.set_override(&mut snapshot, type_manager, animal_owns.clone()).unwrap();
            dog_owns.set_override(&mut snapshot, type_manager, animal_owns.clone()).unwrap();

            // Relations
            let fears = type_manager.create_relation_type(&mut snapshot, &Label::build(LABEL_FEARS), false).unwrap();
            let has_fear =
                fears.create_relates(&mut snapshot, &type_manager, LABEL_HAS_FEAR, Ordering::Unordered).unwrap();
            let is_feared =
                fears.create_relates(&mut snapshot, &type_manager, LABEL_IS_FEARED, Ordering::Unordered).unwrap();
            cat.set_plays(&mut snapshot, &type_manager, has_fear.clone());
            dog.set_plays(&mut snapshot, &type_manager, is_feared.clone());

            snapshot.commit().unwrap();

            (
                (TypeAnnotation::Entity(animal), TypeAnnotation::Entity(cat), TypeAnnotation::Entity(dog)),
                (
                    TypeAnnotation::Attribute(name),
                    TypeAnnotation::Attribute(catname),
                    TypeAnnotation::Attribute(dogname),
                ),
                (
                    TypeAnnotation::Relation(fears),
                    TypeAnnotation::RoleType(has_fear),
                    TypeAnnotation::RoleType(is_feared),
                ),
            )
        }
    }
}

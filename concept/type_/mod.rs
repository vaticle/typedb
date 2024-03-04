/*
 *  Copyright (C) 2023 Vaticle
 *
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU Affero General Public License as
 *  published by the Free Software Foundation, either version 3 of the
 *  License, or (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU Affero General Public License for more details.
 *
 *  You should have received a copy of the GNU Affero General Public License
 *  along with this program.  If not, see <https://www.gnu.org/licenses/>.
 */

use encoding::graph::type_::vertex::TypeVertex;
use encoding::primitive::label::Label;
use primitive::maybe_owns::MaybeOwns;

use crate::ConceptAPI;
use crate::type_::attribute_type::{AttributeType, AttributeTypeAnnotation};
use crate::type_::entity_type::{EntityType, EntityTypeAnnotation};
use crate::type_::owns::Owns;
use crate::type_::relation_type::{RelationType, RelationTypeAnnotation};
use crate::type_::type_manager::TypeManager;

pub mod attribute_type;
pub mod relation_type;
pub mod entity_type;
pub mod type_manager;
mod owns;
mod plays;
mod sub;
pub mod type_cache;
mod relates;
mod object_type;
pub mod annotation;

pub trait TypeAPI<'a>: ConceptAPI<'a> + Sized + Clone {
    fn vertex<'this>(&'this self) -> &'this TypeVertex<'a>;

    fn set_label<'this, 'm>(&'this self, type_manager: &'m TypeManager, label: &Label) {
        // TODO: setLabel should fail is setting label on Root type
        type_manager.set_storage_label(self.vertex().clone().into_owned(), label);
    }

    fn into_vertex(self) -> TypeVertex<'a>;
}

pub trait EntityTypeAPI<'a>: TypeAPI<'a> {
    fn is_root<'m>(&self, type_manager: &'m TypeManager) -> bool {
        type_manager.get_entity_type_is_root(self.clone().into_owned())
    }

    fn get_label<'m>(&self, type_manager: &'m TypeManager) -> MaybeOwns<'m, Label<'static>> {
        type_manager.get_entity_type_label(self.clone().into_owned())
    }

    // TODO: not so pretty to return EntityType directly, but is a win on efficiency. However, should reconsider the trait's necessity.
    fn get_supertype(&self, type_manager: &TypeManager) -> Option<EntityType<'static>> {
        type_manager.get_entity_type_supertype(self.clone().into_owned())
    }

    fn set_supertype(&self, type_manager: &TypeManager, supertype: impl EntityTypeAPI<'static>) {
        type_manager.set_storage_supertype(self.vertex().clone().into_owned(), supertype.vertex().clone().into_owned())
    }

    // TODO: not so pretty to return EntityType directly, but is a win on efficiency. However, should reconsider the trait's necessity.
    fn get_supertypes<'m>(&self, type_manager: &'m TypeManager) -> MaybeOwns<'m, Vec<EntityType<'static>>> {
        type_manager.get_entity_type_supertypes(self.clone().into_owned())
    }

    // fn get_subtypes(&self) -> MaybeOwns<'m, Vec<EntityType<'static>>>;

    fn get_annotations<'this, 'm>(&'this self, type_manager: &'m TypeManager) -> MaybeOwns<'m, Vec<EntityTypeAnnotation>> {
        type_manager.get_entity_type_annotations(self.clone().into_owned())
    }

    fn set_annotation<'this, 'm>(&'this self, type_manager: &'m TypeManager, annotation: EntityTypeAnnotation) {
        match annotation {
            EntityTypeAnnotation::Abstract(_) => {
                type_manager.set_storage_annotation_abstract(self.vertex().clone().into_owned())
            }
        }
    }

    fn delete_annotation<'this, 'm>(&'this self, type_manager: &'m TypeManager, annotation: EntityTypeAnnotation) {
        match annotation {
            EntityTypeAnnotation::Abstract(_) => {
                type_manager.delete_storage_annotation_abstract(self.vertex().clone().into_owned())
            }
        }
    }

    // TODO: not so pretty to return EntityType directly, but is a win on efficiency. However, should reconsider the trait's necessity.
    fn into_owned(self) -> EntityType<'static>;
}

pub trait RelationTypeAPI<'a>: TypeAPI<'a> {
    fn is_root(&self, type_manager: &TypeManager) -> bool {
        type_manager.get_relation_type_is_root(self.clone().into_owned())
    }

    fn get_label<'m>(&self, type_manager: &'m TypeManager) -> MaybeOwns<'m, Label<'static>> {
        type_manager.get_relation_type_label(self.clone().into_owned())
    }

    fn get_supertype(&self, type_manager: &TypeManager) -> Option<RelationType<'static>> {
        type_manager.get_relation_type_supertype(self.clone().into_owned())
    }

    fn set_supertype(&self, type_manager: &TypeManager, supertype: impl RelationTypeAPI<'static>) {
        type_manager.set_storage_supertype(self.vertex().clone().into_owned(), supertype.vertex().clone().into_owned())
    }

    // TODO: not so pretty to return Type directly, but is a win on efficiency. However, should reconsider the trait's necessity.
    fn get_supertypes<'m>(&self, type_manager: &'m TypeManager) -> MaybeOwns<'m, Vec<RelationType<'static>>> {
        type_manager.get_relation_type_supertypes(self.clone().into_owned())
    }

    // fn get_subtypes(&self) -> MaybeOwns<'m, Vec<RelationType<'static>>>;

    fn get_annotations<'this, 'm>(&'this self, type_manager: &'m TypeManager) -> MaybeOwns<'m, Vec<RelationTypeAnnotation>> {
        type_manager.get_relation_type_annotations(self.clone().into_owned())
    }

    fn set_annotation<'this, 'm>(&'this self, type_manager: &'m TypeManager, annotation: RelationTypeAnnotation) {
        match annotation {
            RelationTypeAnnotation::Abstract(_) => {
                type_manager.set_storage_annotation_abstract(self.vertex().clone().into_owned())
            }
        }
    }

    fn delete_annotation<'this, 'm>(&'this self, type_manager: &'m TypeManager, annotation: RelationTypeAnnotation) {
        match annotation {
            RelationTypeAnnotation::Abstract(_) => {
                type_manager.delete_storage_annotation_abstract(self.vertex().clone().into_owned())
            }
        }
    }

    fn into_owned(self) -> RelationType<'static>;
}

pub trait AttributeTypeAPI<'a>: TypeAPI<'a> {
    fn is_root(&self, type_manager: &TypeManager) -> bool {
        type_manager.get_attribute_type_is_root(self.clone().into_owned())
    }

    fn get_label<'m>(&self, type_manager: &'m TypeManager) -> MaybeOwns<'m, Label<'static>> {
        type_manager.get_attribute_type_label(self.clone().into_owned())
    }

    fn get_supertype(&self, type_manager: &TypeManager) -> Option<AttributeType<'static>> {
        type_manager.get_attribute_type_supertype(self.clone().into_owned())
    }

    fn set_supertype(&self, type_manager: &TypeManager, supertype: impl AttributeTypeAPI<'static>) {
        type_manager.set_storage_supertype(self.vertex().clone().into_owned(), supertype.vertex().clone().into_owned())
    }

    // TODO: not so pretty to return Type directly, but is a win on efficiency. However, should reconsider the trait's necessity.
    fn get_supertypes<'m>(&self, type_manager: &'m TypeManager) -> MaybeOwns<'m, Vec<AttributeType<'static>>> {
        type_manager.get_attribute_type_supertypes(self.clone().into_owned())
    }

    // fn get_subtypes(&self) -> MaybeOwns<'m, Vec<AttributeType<'static>>>;

    fn get_annotations<'this, 'm>(&'this self, type_manager: &'m TypeManager) -> MaybeOwns<'m, Vec<AttributeTypeAnnotation>> {
        type_manager.get_attribute_type_annotations(self.clone().into_owned())
    }

    fn set_annotation<'this, 'm>(&'this self, type_manager: &'m TypeManager, annotation: AttributeTypeAnnotation) {
        match annotation {
            AttributeTypeAnnotation::Abstract(_) => {
                type_manager.set_storage_annotation_abstract(self.vertex().clone().into_owned())
            }
        }
    }

    fn delete_annotation<'this, 'm>(&'this self, type_manager: &'m TypeManager, annotation: AttributeTypeAnnotation) {
        match annotation {
            AttributeTypeAnnotation::Abstract(_) => {
                type_manager.delete_storage_annotation_abstract(self.vertex().clone().into_owned())
            }
        }
    }

    fn into_owned(self) -> AttributeType<'static>;
}

trait OwnerAPI<'a>: TypeAPI<'a> {
    fn set_owns(&self, attribute_type: &AttributeType) -> Owns {
        // create Owns
        todo!()
    }

    fn get_owns(&self) {
        // fetch iterator of Owns
        todo!()
    }

    fn get_owns_owned(&self) {
        // fetch iterator of owned attribute types
        todo!()
    }

    fn has_owns_owned(&self, attribute_type: &AttributeType) -> bool {
        todo!()
    }
}

trait OwnedAPI<'a>: AttributeTypeAPI<'a> {
    fn get_owns(&self) {
        // return iterator of Owns
        todo!()
    }

    fn get_owns_owners(&self) {
        // return iterator of Owns
        todo!()
    }
}

trait PlayerAPI<'a>: TypeAPI<'a> {

    // fn set_plays(&self, role_type: &RoleType) -> Plays;

    fn get_plays(&self) {
        // return iterator of Plays
        todo!()
    }

    fn get_plays_played(&self) {
        // return iterator of played types
        todo!()
    }

    // fn has_plays_played(&self, role_type: &RoleType);
}

trait PlayedAPI<'a>: TypeAPI<'a> {
    fn get_plays(&self) {
        // return iterator of Plays
        todo!()
    }

    fn get_plays_players(&self) {
        // return iterator of player types
        todo!()
    }
}
/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

// FIXME: exported macros must provide their own use-declarations or use fully qualified paths
//        As it stands, this macro requires imports at point of use.
#[macro_export]
macro_rules! concept_iterator {
    ($name:ident, $concept_type:ident, $map_fn: expr) => {
        pub struct $name<'a, const S: usize> {
            snapshot_iterator: Option<storage::snapshot::iterator::SnapshotRangeIterator<'a, S>>,
        }

        impl<'a, const S: usize> $name<'a, S> {
            pub(crate) fn new(snapshot_iterator: storage::snapshot::iterator::SnapshotRangeIterator<'a, S>) -> Self {
                $name { snapshot_iterator: Some(snapshot_iterator) }
            }

            pub(crate) fn new_empty() -> Self {
                $name { snapshot_iterator: None }
            }

            pub fn peek(&mut self) -> Option<Result<$concept_type<'_>, $crate::error::ConceptReadError>> {
                use $crate::error::ConceptReadError::SnapshotIterate;
                self.iter_peek().map(|result| {
                    result
                        .map(|(storage_key, _value_bytes)| $map_fn(storage_key))
                        .map_err(|error| SnapshotIterate { source: error })
                })
            }

            // a lending iterator trait is infeasible with the current borrow checker
            #[allow(clippy::should_implement_trait)]
            pub fn next(&mut self) -> Option<Result<$concept_type<'_>, $crate::error::ConceptReadError>> {
                use $crate::error::ConceptReadError::SnapshotIterate;
                self.iter_next().map(|result| {
                    result
                        .map(|(storage_key, _value_bytes)| $map_fn(storage_key))
                        .map_err(|error| SnapshotIterate { source: error })
                })
            }

            pub fn seek(&mut self) {
                todo!()
            }

            fn iter_peek(
                &mut self,
            ) -> Option<
                Result<
                    (StorageKeyReference<'_>, bytes::byte_reference::ByteReference<'_>),
                    std::sync::Arc<storage::snapshot::iterator::SnapshotIteratorError>,
                >,
            > {
                if let Some(iter) = self.snapshot_iterator.as_mut() {
                    iter.peek()
                } else {
                    None
                }
            }

            fn iter_next(
                &mut self,
            ) -> Option<
                Result<
                    (StorageKeyReference<'_>, bytes::byte_reference::ByteReference<'_>),
                    std::sync::Arc<storage::snapshot::iterator::SnapshotIteratorError>,
                >,
            > {
                if let Some(iter) = self.snapshot_iterator.as_mut() {
                    iter.next()
                } else {
                    None
                }
            }

            pub fn collect_cloned(mut self) -> Vec<$concept_type<'static>> {
                let mut vec = Vec::new();
                loop {
                    let item = self.next();
                    if item.is_none() {
                        break;
                    }
                    let key = item.unwrap().unwrap().into_owned();
                    vec.push(key);
                }
                vec
            }
        }
    };
}

#[macro_export]
macro_rules! edge_iterator {
    ($name:ident; $mapped_type:ty; $map_fn: expr) => {
        pub struct $name<'a, const S: usize> {
            snapshot_iterator: Option<storage::snapshot::iterator::SnapshotRangeIterator<'a, S>>,
        }

        impl<'a, const S: usize> $name<'a, S> {
            pub(crate) fn new(snapshot_iterator: storage::snapshot::iterator::SnapshotRangeIterator<'a, S>) -> Self {
                $name { snapshot_iterator: Some(snapshot_iterator) }
            }

            pub(crate) fn new_empty() -> Self {
                $name { snapshot_iterator: None }
            }

            pub fn peek(&mut self) -> Option<Result<$mapped_type, $crate::error::ConceptReadError>> {
                use $crate::error::ConceptReadError::SnapshotIterate;
                self.iter_peek().map(|result| {
                    result
                        .map(|(storage_key, value_bytes)| $map_fn(storage_key, value_bytes))
                        .map_err(|error| SnapshotIterate { source: error })
                })
            }

            // a lending iterator trait is infeasible with the current borrow checker
            #[allow(clippy::should_implement_trait)]
            pub fn next(&mut self) -> Option<Result<$mapped_type, $crate::error::ConceptReadError>> {
                use $crate::error::ConceptReadError::SnapshotIterate;
                self.iter_next().map(|result| {
                    result
                        .map(|(storage_key, value_bytes)| $map_fn(storage_key, value_bytes))
                        .map_err(|error| SnapshotIterate { source: error })
                })
            }

            pub fn seek(&mut self) {
                todo!()
            }

            fn iter_peek(
                &mut self,
            ) -> Option<
                Result<
                    (StorageKeyReference<'_>, bytes::byte_reference::ByteReference<'_>),
                    std::sync::Arc<storage::snapshot::iterator::SnapshotIteratorError>,
                >,
            > {
                if let Some(iter) = self.snapshot_iterator.as_mut() {
                    iter.peek()
                } else {
                    None
                }
            }

            fn iter_next(
                &mut self,
            ) -> Option<
                Result<
                    (StorageKeyReference<'_>, bytes::byte_reference::ByteReference<'_>),
                    std::sync::Arc<storage::snapshot::iterator::SnapshotIteratorError>,
                >,
            > {
                if let Some(iter) = self.snapshot_iterator.as_mut() {
                    iter.next()
                } else {
                    None
                }
            }

            pub fn collect_cloned_vec<F, M>(mut self, mapper: F) -> Result<Vec<M>, $crate::error::ConceptReadError>
            where
                F: for<'b> Fn($mapped_type) -> M,
            {
                let mut vec = Vec::new();
                loop {
                    let item = self.next();
                    match item {
                        None => break,
                        Some(Err(error)) => return Err(error),
                        Some(Ok(mapped)) => {
                            vec.push(mapper(mapped));
                        }
                    }
                }
                Ok(vec)
            }

            pub fn count(mut self) -> usize {
                let mut count = 0;
                let mut next = self.next();
                while next.is_some() {
                    next = self.next();
                    count += 1;
                }
                count
            }
        }
    };
}

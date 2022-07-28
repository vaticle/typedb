/*
 * Copyright (C) 2022 Vaticle
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Affero General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Affero General Public License for more details.
 *
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <https://www.gnu.org/licenses/>.
 *
 */

package com.vaticle.typedb.core.common.iterator.sorted;

import com.vaticle.typedb.core.common.iterator.FunctionalIterator;
import com.vaticle.typedb.core.common.iterator.Iterators;

import java.util.Collection;
import java.util.List;
import java.util.NavigableSet;
import java.util.TreeSet;
import java.util.function.Function;
import java.util.function.Predicate;

import static com.vaticle.typedb.common.collection.Collections.list;

public class SortedIterators {

    public static <T extends Comparable<? super T>, ORDER extends SortedIterator.Order> SortedIterator<T, ORDER> iterateSorted(ORDER order, List<T> list) {
        return new ListSortedIterator<>(list, order);
    }

    public static <T extends Comparable<? super T>, ORDER extends SortedIterator.Order> SortedIterator<T, ORDER> distinct(
            SortedIterator<T, ORDER> iterator) {
        return new DistinctSortedIterator<>(iterator);
    }

    public static <T extends Comparable<? super T>, ORDER extends SortedIterator.Order> SortedIterator<T, ORDER> filter(
            SortedIterator<T, ORDER> iterator, Predicate<T> predicate) {
        return new FilteredSortedIterator<>(iterator, predicate);
    }

    public static <T extends Comparable<? super T>, ORDER extends SortedIterator.Order> SortedIterator<T, ORDER> limit(SortedIterator<T, ORDER> iterator,
                                                                                                                       long limit) {
        return new LimitedSortedIterator<>(iterator, limit);
    }

    public static <T extends Comparable<? super T>, U extends Comparable<? super U>, ORDER extends SortedIterator.Order>
    SortedIterator<U, ORDER> mapSorted(ORDER order, SortedIterator<T, ?> iterator, Function<T, U> mappingFn) {
        return new MappedSortedIterator<>(iterator, mappingFn, order);
    }

    @SafeVarargs
    public static <T extends Comparable<? super T>, ORDER extends SortedIterator.Order> SortedIterator<T, ORDER> merge(SortedIterator<T, ORDER> iterator, SortedIterator<T, ORDER>... iterators) {
        return new MergeMappedSortedIterator<>(Iterators.iterate(list(list(iterators), iterator)), e -> e, iterator.order());
    }

    public static <T extends Comparable<? super T>, ORDER extends SortedIterator.Order> SortedIterator<T, ORDER> merge(ORDER order, FunctionalIterator<SortedIterator<T, ORDER>> iterators) {
        return new MergeMappedSortedIterator<>(iterators, e -> e, order);
    }

    public static <T extends Comparable<? super T>, ORDER extends SortedIterator.Order> SortedIterator<T, ORDER> onConsume(SortedIterator<T, ORDER> iterator, Runnable onConsume) {
        return new ConsumeHandledSortedIterator<>(iterator, onConsume);
    }

    public static <T extends Comparable<? super T>, ORDER extends SortedIterator.Order> SortedIterator<T, ORDER> onFinalise(SortedIterator<T, ORDER> iterator,
                                                                                                                            Runnable finalise) {
        return new FinaliseSortedIterator<>(iterator, finalise);
    }

    public static class Forwardable {

        public static <T extends Comparable<? super T>> SortedIterator.Forwardable<T, SortedIterator.Order.Asc> emptySorted() {
            return iterateSorted(new TreeSet<T>(), SortedIterator.ASC);
        }

        public static <T extends Comparable<? super T>, ORDER extends SortedIterator.Order> SortedIterator.Forwardable<T, ORDER> iterateSorted(Collection<T> elements, ORDER order) {
            return new NavigableForwardableIterator<>(new TreeSet<>(elements), order);
        }

        @SafeVarargs
        public static <T extends Comparable<? super T>, ORDER extends SortedIterator.Order> SortedIterator.Forwardable<T, ORDER> iterateSorted(ORDER order, T... elements) {
            return new NavigableForwardableIterator<>(new TreeSet<>(list(elements)), order);
        }

        public static <T extends Comparable<? super T>, ORDER extends SortedIterator.Order> SortedIterator.Forwardable<T, ORDER> iterateSorted(NavigableSet<T> set, ORDER order) {
            return new NavigableForwardableIterator<>(set, order);
        }

        public static <T extends Comparable<? super T>, ORDER extends SortedIterator.Order> SortedIterator.Forwardable<T, ORDER> distinct(SortedIterator.Forwardable<T, ORDER> iterator) {
            return new DistinctSortedIterator.Forwardable<>(iterator);
        }

        public static <T extends Comparable<? super T>, ORDER extends SortedIterator.Order> SortedIterator.Forwardable<T, ORDER> filter(SortedIterator.Forwardable<T, ORDER> iterator,
                                                                                                                                        Predicate<T> predicate) {
            return new FilteredSortedIterator.Forwardable<>(iterator, predicate);
        }

        public static <T extends Comparable<? super T>, ORDER extends SortedIterator.Order> SortedIterator.Forwardable<T, ORDER> limit(SortedIterator.Forwardable<T, ORDER> iterator,
                                                                                                                                       long limit) {
            return new LimitedSortedIterator.Forwardable<>(iterator, limit);
        }

        @SafeVarargs
        public static <T extends Comparable<? super T>, ORDER extends SortedIterator.Order> SortedIterator.Forwardable<T, ORDER> merge(SortedIterator.Forwardable<T, ORDER> iterator, SortedIterator.Forwardable<T, ORDER>... iterators) {
            return new MergeMappedSortedIterator.Forwardable<>(Iterators.iterate(list(list(iterators), iterator)), e -> e, iterator.order());
        }

        public static <T extends Comparable<? super T>, ORDER extends SortedIterator.Order> SortedIterator.Forwardable<T, ORDER> merge(FunctionalIterator<SortedIterator.Forwardable<T, ORDER>> iterators, ORDER order) {
            return new MergeMappedSortedIterator.Forwardable<>(iterators, e -> e, order);
        }

        @SafeVarargs
        public static <T extends Comparable<? super T>, ORDER extends SortedIterator.Order> SortedIterator.Forwardable<T, ORDER> intersect(SortedIterator.Forwardable<T, ORDER> iterator, SortedIterator.Forwardable<T, ORDER>... iterators) {
            return new IntersectForwardableIterator<>(list(list(iterators), iterator), iterator.order());
        }

        public static <T extends Comparable<? super T>, ORDER extends SortedIterator.Order> SortedIterator.Forwardable<T, ORDER> intersect(FunctionalIterator<SortedIterator.Forwardable<T, ORDER>> iterators, ORDER order) {
            return new IntersectForwardableIterator<>(iterators.toList(), order);
        }

        public static <T extends Comparable<? super T>, U extends Comparable<? super U>, ORDER extends SortedIterator.Order>
        SortedIterator.Forwardable<U, ORDER> mapSorted(ORDER order, SortedIterator.Forwardable<T, ?> iterator, Function<T, U> mappingFn, Function<U, T> reverseMappingFn) {
            return new MappedSortedIterator.Forwardable<>(iterator, mappingFn, reverseMappingFn, order);
        }

        public static <T extends Comparable<? super T>, ORDER extends SortedIterator.Order> SortedIterator.Forwardable<T, ORDER> onConsume(SortedIterator.Forwardable<T, ORDER> iterator,
                                                                                                                                           Runnable onConsume) {
            return new ConsumeHandledSortedIterator.Forwardable<>(iterator, onConsume);
        }

        public static <T extends Comparable<? super T>, ORDER extends SortedIterator.Order> SortedIterator.Forwardable<T, ORDER> onFinalise(SortedIterator.Forwardable<T, ORDER> iterator,
                                                                                                                                            Runnable finalise) {
            return new FinaliseSortedIterator.Forwardable<>(iterator, finalise);
        }
    }
}

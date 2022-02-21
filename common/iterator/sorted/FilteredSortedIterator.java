/*
 * Copyright (C) 2021 Vaticle
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

import com.vaticle.typedb.core.common.exception.TypeDBException;
import com.vaticle.typedb.core.common.iterator.sorted.SortedIterator.Order;

import java.util.NoSuchElementException;
import java.util.function.Function;
import java.util.function.Predicate;

import static com.vaticle.typedb.core.common.exception.ErrorMessage.Internal.ILLEGAL_ARGUMENT;

public class FilteredSortedIterator<T extends Comparable<? super T>, ORDER extends Order, ITER extends SortedIterator<T, ORDER>>
        extends AbstractSortedIterator<T, ORDER> {

    private final Predicate<T> predicate;
    final ITER iterator;
    T next;
    T last;

    public FilteredSortedIterator(ITER iterator, Predicate<T> predicate) {
        super(iterator.order());
        this.iterator = iterator;
        this.predicate = predicate;
    }

    @Override
    public boolean hasNext() {
        return (next != null) || fetchAndCheck();
    }

    private boolean fetchAndCheck() {
        while (iterator.hasNext() && !predicate.test(next = iterator.next())) next = null;
        return next != null;
    }

    @Override
    public T next() {
        if (!hasNext()) throw new NoSuchElementException();
        last = next;
        next = null;
        return last;
    }

    @Override
    public T peek() {
        if (!hasNext()) throw new NoSuchElementException();
        return next;
    }

    @Override
    public void recycle() {
        iterator.recycle();
    }

    public static class Seekable<T extends Comparable<? super T>, ORDER extends Order>
            extends FilteredSortedIterator<T, ORDER, SortedIterator.Seekable<T, ORDER>>
            implements SortedIterator.Seekable<T, ORDER> {

        public Seekable(SortedIterator.Seekable<T, ORDER> source, Predicate<T> predicate) {
            super(source, predicate);
        }

        @Override
        public void seek(T target) {
            if (last != null && !order.isValidNext(last, target)) throw TypeDBException.of(ILLEGAL_ARGUMENT);
            if (next != null) {
                if (order.isValidNext(target, next)) return;
                last = next;
                next = null;
            }
            iterator.seek(target);
        }

        @Override
        public final SortedIterator.Seekable<T, ORDER> merge(SortedIterator.Seekable<T, ORDER> iterator) {
            return SortedIterators.Seekable.merge(this, iterator);
        }

        @Override
        public <U extends Comparable<? super U>, ORD extends Order> SortedIterator.Seekable<U, ORD> mapSorted(
                Function<T, U> mappingFn, Function<U, T> reverseMappingFn, ORD order) {
            return SortedIterators.Seekable.mapSorted(order, this, mappingFn, reverseMappingFn);
        }

        @Override
        public SortedIterator.Seekable<T, ORDER> distinct() {
            return SortedIterators.Seekable.distinct(this);
        }

        @Override
        public SortedIterator.Seekable<T, ORDER> filter(Predicate<T> predicate) {
            return SortedIterators.Seekable.filter(this, predicate);
        }

        @Override
        public SortedIterator.Seekable<T, ORDER> limit(long limit) {
            return SortedIterators.Seekable.limit(this, limit);
        }

        @Override
        public SortedIterator.Seekable<T, ORDER> onConsumed(Runnable function) {
            return SortedIterators.Seekable.onConsume(this, function);
        }

        @Override
        public SortedIterator.Seekable<T, ORDER> onFinalise(Runnable function) {
            return SortedIterators.Seekable.onFinalise(this, function);
        }
    }
}

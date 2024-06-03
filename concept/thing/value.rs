/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::borrow::Cow;

use chrono::{DateTime, NaiveDateTime};
use chrono_tz::Tz;
use encoding::value::{
    boolean_bytes::BooleanBytes, date_time_bytes::DateTimeBytes, date_time_tz_bytes::DateTimeTZBytes,
    double_bytes::DoubleBytes, duration_bytes::DurationBytes, duration_value::Duration,
    fixed_point_bytes::FixedPointBytes, fixed_point_value::FixedPoint, long_bytes::LongBytes,
    string_bytes::StringBytes, struct_bytes::StructBytes, value_type::ValueType, ValueEncodable,
};

use crate::thing::value_struct::StructValue;

#[derive(Debug, Clone, PartialEq)]
pub enum Value<'a> {
    Boolean(bool),
    Long(i64),
    Double(f64),
    FixedPoint(FixedPoint),
    DateTime(NaiveDateTime),
    DateTimeTZ(DateTime<Tz>),
    Duration(Duration),
    String(Cow<'a, str>),
    Struct(Cow<'a, StructValue<'static>>),
}

impl<'a> Value<'a> {
    pub fn as_reference(&self) -> Value<'_> {
        match *self {
            Value::Boolean(boolean) => Value::Boolean(boolean),
            Value::Long(long) => Value::Long(long),
            Value::Double(double) => Value::Double(double),
            Value::FixedPoint(fixed_point) => Value::FixedPoint(fixed_point),
            Value::DateTime(date_time) => Value::DateTime(date_time),
            Value::DateTimeTZ(date_time_tz) => Value::DateTimeTZ(date_time_tz),
            Value::Duration(duration) => Value::Duration(duration),
            Value::String(ref string) => Value::String(Cow::Borrowed(string.as_ref())),
            Value::Struct(ref struct_) => Value::Struct(Cow::Borrowed(struct_.as_ref())),
        }
    }

    pub fn unwrap_boolean(self) -> bool {
        match self {
            Self::Boolean(boolean) => boolean,
            _ => panic!("Cannot unwrap Long if not a long value."),
        }
    }

    pub fn unwrap_long(self) -> i64 {
        match self {
            Self::Long(long) => long,
            _ => panic!("Cannot unwrap Long if not a long value."),
        }
    }

    pub fn unwrap_double(self) -> f64 {
        match self {
            Self::Double(double) => double,
            _ => panic!("Cannot unwrap Double if not a double value."),
        }
    }

    pub fn unwrap_date_time(self) -> NaiveDateTime {
        match self {
            Self::DateTime(date_time) => date_time,
            _ => panic!("Cannot unwrap DateTime if not a datetime value."),
        }
    }

    pub fn unwrap_string(self) -> Cow<'a, str> {
        match self {
            Self::String(string) => string,
            _ => panic!("Cannot unwrap String if not a string value."),
        }
    }

    pub fn unwrap_struct(self) -> Cow<'a, StructValue<'static>> {
        match self {
            Value::Struct(struct_) => struct_,
            _ => panic!("Cannot unwrap Struct if not a struct value."),
        }
    }

    pub(crate) fn into_owned(self) -> Value<'static> {
        match self {
            Self::Boolean(bool) => Value::Boolean(bool),
            Self::Long(long) => Value::Long(long),
            Self::Double(double) => Value::Double(double),
            Self::FixedPoint(fixed_point) => Value::FixedPoint(fixed_point),
            Self::DateTime(date_time) => Value::DateTime(date_time),
            Self::DateTimeTZ(date_time_tz) => Value::DateTimeTZ(date_time_tz),
            Self::Duration(duration) => Value::Duration(duration),
            Self::String(string) => Value::String(Cow::Owned(string.into_owned())),
            Self::Struct(struct_) => Value::Struct(Cow::Owned(struct_.into_owned())),
        }
    }
}

impl<'a> ValueEncodable for Value<'a> {
    fn value_type(&self) -> ValueType {
        match self {
            Value::Boolean(_) => ValueType::Boolean,
            Value::Long(_) => ValueType::Long,
            Value::Double(_) => ValueType::Double,
            Value::FixedPoint(_) => ValueType::FixedPoint,
            Value::DateTime(_) => ValueType::DateTime,
            Value::DateTimeTZ(_) => ValueType::DateTimeTZ,
            Value::Duration(_) => ValueType::Duration,
            Value::String(_) => ValueType::String,
            Value::Struct(struct_value) => ValueType::Struct(struct_value.definition_key().into_owned()),
        }
    }

    fn encode_boolean(&self) -> BooleanBytes {
        match self {
            Self::Boolean(boolean) => BooleanBytes::build(*boolean),
            _ => panic!("Cannot encode non-boolean as BooleanBytes"),
        }
    }

    fn encode_long(&self) -> LongBytes {
        match self {
            Self::Long(long) => LongBytes::build(*long),
            _ => panic!("Cannot encode non-long as LongBytes"),
        }
    }

    fn encode_double(&self) -> DoubleBytes {
        match self {
            Self::Double(double) => DoubleBytes::build(*double),
            _ => panic!("Cannot encode non-double as DoubleBytes"),
        }
    }

    fn encode_fixed_point(&self) -> FixedPointBytes {
        match self {
            Self::FixedPoint(fixed_point) => FixedPointBytes::build(*fixed_point),
            _ => panic!("Cannot encode non-fixed_point as FixedPointBytes"),
        }
    }

    fn encode_date_time(&self) -> DateTimeBytes {
        match self {
            Self::DateTime(date_time) => DateTimeBytes::build(*date_time),
            _ => panic!("Cannot encode non-datetime as DateTimeBytes"),
        }
    }

    fn encode_date_time_tz(&self) -> DateTimeTZBytes {
        match self {
            &Self::DateTimeTZ(date_time_tz) => DateTimeTZBytes::build(date_time_tz),
            _ => panic!("Cannot encoded non-datetime as DateTimeBytes"),
        }
    }

    fn encode_duration(&self) -> DurationBytes {
        match self {
            Self::Duration(duration) => DurationBytes::build(*duration),
            _ => panic!("Cannot encoded non-duration as DurationBytes"),
        }
    }

    fn encode_string<const INLINE_LENGTH: usize>(&self) -> StringBytes<'_, INLINE_LENGTH> {
        match self {
            Value::String(str) => StringBytes::build_ref(str),
            _ => panic!("Cannot encode non-String as StringBytes"),
        }
    }

    fn encode_struct<const INLINE_LENGTH: usize>(&self) -> StructBytes<'static, INLINE_LENGTH> {
        match self {
            Value::Struct(struct_) => {
                todo!()
            }
            _ => panic!("Cannot encode non-Struct as StructBytes"),
        }
    }
}
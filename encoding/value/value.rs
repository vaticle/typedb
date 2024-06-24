/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::borrow::Cow;

use chrono::{DateTime, NaiveDate, NaiveDateTime};
use chrono_tz::Tz;

use super::date_bytes::DateBytes;
use crate::value::{
    boolean_bytes::BooleanBytes, date_time_bytes::DateTimeBytes, date_time_tz_bytes::DateTimeTZBytes,
    decimal_bytes::DecimalBytes, decimal_value::Decimal, double_bytes::DoubleBytes, duration_bytes::DurationBytes,
    duration_value::Duration, long_bytes::LongBytes, string_bytes::StringBytes, struct_bytes::StructBytes,
    value_struct::StructValue, value_type::ValueType, ValueEncodable,
};

#[derive(Debug, Clone, PartialEq)]
pub enum Value<'a> {
    Boolean(bool),
    Long(i64),
    Double(f64),
    Decimal(Decimal),
    Date(NaiveDate),
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
            Value::Decimal(decimal) => Value::Decimal(decimal),
            Value::Date(date) => Value::Date(date),
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

    pub fn into_owned(self) -> Value<'static> {
        match self {
            Self::Boolean(bool) => Value::Boolean(bool),
            Self::Long(long) => Value::Long(long),
            Self::Double(double) => Value::Double(double),
            Self::Decimal(decimal) => Value::Decimal(decimal),
            Self::Date(date) => Value::Date(date),
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
            Value::Decimal(_) => ValueType::Decimal,
            Value::Date(_) => ValueType::Date,
            Value::DateTime(_) => ValueType::DateTime,
            Value::DateTimeTZ(_) => ValueType::DateTimeTZ,
            Value::Duration(_) => ValueType::Duration,
            Value::String(_) => ValueType::String,
            Value::Struct(struct_value) => ValueType::Struct(struct_value.definition_key().clone().into_owned()),
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

    fn encode_decimal(&self) -> DecimalBytes {
        match self {
            Self::Decimal(decimal) => DecimalBytes::build(*decimal),
            _ => panic!("Cannot encode non-decimal as DecimalBytes"),
        }
    }

    fn encode_date(&self) -> DateBytes {
        match self {
            Self::Date(date) => DateBytes::build(*date),
            _ => panic!("Cannot encode non-date as DateBytes"),
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
            Value::Struct(struct_) => StructBytes::build(struct_),
            _ => panic!("Cannot encode non-Struct as StructBytes"),
        }
    }
}

#![no_std]

extern crate alloc;

use alloc::vec::Vec;
use core::cmp::{max, min, Ordering};
use core::fmt::{Display, Formatter};
use core::hash::{Hash, Hasher};
use core::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, Sub, SubAssign};

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Error {
    SegmentPointNaN,
    StartPointGreaterThanEndPoint,
    ContainInf,
}

fn merge_span_segments(segments: &mut Vec<(i64, i64)>) {
    segments.sort_by_key(|&a| a.0);
    let mut index = 0;
    for i in 1..segments.len() {
        if segments[index].1 >= segments[i].0 - 1 {
            segments[index].1 = max(segments[index].1, segments[i].1);
        } else {
            index += 1;
            segments[index] = segments[i];
        }
    }
    segments.truncate(index + 1);
}

#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct Span {
    pub(crate) segments: Vec<(i64, i64)>,
}

impl Display for Span {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self.segments.split_first() {
            Some((&first, elements)) => {
                write!(f, "[{}, {}]", first.0, first.1)?;
                for &element in elements {
                    write!(f, " ∪ [{}, {}]", element.0, element.1)?;
                }
                Ok(())
            }
            None => {
                write!(f, "∅")
            }
        }
    }
}

impl BitAnd for Span {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        self.intersection(rhs)
    }
}

impl BitAndAssign for Span {
    fn bitand_assign(&mut self, rhs: Self) {
        self.segments = self.clone().bitand(rhs).segments;
    }
}

impl BitOr for Span {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        self.union(rhs)
    }
}

impl BitOrAssign for Span {
    fn bitor_assign(&mut self, rhs: Self) {
        self.segments.extend(rhs.segments.iter());
        merge_span_segments(&mut self.segments);
    }
}

impl Sub for Span {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        self.difference(rhs)
    }
}

impl SubAssign for Span {
    fn sub_assign(&mut self, rhs: Self) {
        self.segments = self.clone().sub(rhs).segments;
    }
}

impl Span {
    pub fn try_new(segments: impl IntoIterator<Item = (i64, i64)>) -> Result<Self, Error> {
        let mut output = segments
            .into_iter()
            .map(|f| {
                if f.0 > f.1 {
                    return Err(Error::StartPointGreaterThanEndPoint);
                }
                Ok(f)
            })
            .collect::<Result<Vec<(i64, i64)>, Error>>()?;
        merge_span_segments(&mut output);
        Ok(Self { segments: output })
    }

    pub fn segments(&self) -> &[(i64, i64)] {
        &self.segments
    }

    pub fn contains(&self, &item: &i64) -> bool {
        self.segments.iter().any(|&f| (f.0 <= item) & (item <= f.1))
    }

    pub fn difference(self, other: Self) -> Self {
        if other.segments.is_empty() {
            return self;
        }
        let mut output = Self::default();
        let mut next_bound = 0;
        let mut bottom_bound;
        let mut temp_left_bound;
        for &x in &self.segments {
            temp_left_bound = x.0;
            bottom_bound = next_bound;
            for y in bottom_bound..other.segments.len() {
                if x.1 < other.segments[y].0 {
                    break;
                }
                let temp = (temp_left_bound, other.segments[y].0 - 1);
                if temp.0 <= temp.1 {
                    output.segments.push(temp);
                }
                if temp_left_bound < other.segments[y].1 + 1 {
                    temp_left_bound = other.segments[y].1 + 1;
                }
                next_bound = y + 1;
            }
            if temp_left_bound <= x.1 {
                output.segments.push((temp_left_bound, x.1));
            }
        }
        output
    }

    pub fn intersection(self, other: Self) -> Self {
        let mut output = Self::default();
        let mut next_bound = 0;
        let mut bottom_bound;
        for &x in &self.segments {
            bottom_bound = next_bound;
            for y in bottom_bound..other.segments.len() {
                if x.1 < other.segments[y].0 {
                    break;
                } else {
                    let left = max(x.0, other.segments[y].0);
                    let right = min(x.1, other.segments[y].1);
                    if left <= right {
                        output.segments.push((left, right));
                    }
                    next_bound = y;
                }
            }
        }
        output
    }

    pub fn is_disjoint(&self, other: &Self) -> bool {
        let mut segments = self.segments.clone();
        segments.extend(other.segments.iter());
        segments.sort_by_key(|&a| a.0);
        let mut index = 0;
        for i in 1..segments.len() {
            if segments[index].1 >= segments[i].0 {
                return false;
            } else {
                index += 1;
                segments[index] = segments[i];
            }
        }
        true
    }

    pub fn is_subset(&self, other: &Self) -> bool {
        self == &self.clone().union(other.clone())
    }

    pub fn is_superset(&self, other: &Self) -> bool {
        other.is_subset(self)
    }

    pub fn union(self, other: Self) -> Self {
        self.union_all([other])
    }

    pub fn union_all(self, others: impl IntoIterator<Item = impl Into<Self>>) -> Self {
        let mut x = self.segments;
        x.extend(others.into_iter().flat_map(|f| f.into().segments));
        merge_span_segments(&mut x);
        Self { segments: x }
    }
}

fn interval_segment_cmp(a: &(bool, f64, f64, bool), b: &(bool, f64, f64, bool)) -> Ordering {
    (a.1, !a.0).partial_cmp(&(b.1, !b.0)).unwrap()
}

fn merge_interval_segments(segments: &mut Vec<(bool, f64, f64, bool)>) {
    segments.sort_by(interval_segment_cmp);
    let mut index = 0;
    for i in 1..segments.len() {
        if (segments[index].2 > segments[i].1)
            | ((segments[index].2 == segments[i].1)
        // check for adjacence
                & (segments[index].3 | segments[i].0))
        {
            // emulate max()
            if (segments[i].2 > segments[index].2)
                | ((segments[i].2 == segments[index].2) & segments[i].3)
            {
                segments[index].2 = segments[i].2;
                segments[index].3 = segments[i].3;
            }
        } else {
            index += 1;
            segments[index] = segments[i];
        }
    }
    segments.truncate(index + 1);
}

fn validate_interval_segment(segment: &(bool, f64, f64, bool)) -> bool {
    (segment.1 < segment.2) | ((segment.1 == segment.2) & segment.0 & segment.3)
}

#[derive(Clone, Debug, Default)]
pub struct Interval {
    pub(crate) segments: Vec<(bool, f64, f64, bool)>,
}

impl Display for Interval {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self.segments.split_first() {
            Some((&first, elements)) => {
                write!(
                    f,
                    "{}{}, {}{}",
                    if first.0 { "[" } else { "(" },
                    first.1,
                    first.2,
                    if first.3 { "]" } else { ")" }
                )?;
                for &element in elements {
                    write!(
                        f,
                        " ∪ {}{}, {}{}",
                        if element.0 { "[" } else { "(" },
                        element.1,
                        element.2,
                        if element.3 { "]" } else { ")" }
                    )?;
                }
                Ok(())
            }
            None => {
                write!(f, "∅")
            }
        }
    }
}

impl Hash for Interval {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (self
            .segments
            .iter()
            .map(|&f| (f.0, f.1.to_bits(), f.2.to_bits(), f.3))
            .collect::<Vec<(bool, u64, u64, bool)>>(),)
            .hash(state)
    }
}

impl PartialEq for Interval {
    fn eq(&self, other: &Self) -> bool {
        self.segments == other.segments
    }
}

impl BitAnd for Interval {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        self.intersection(rhs)
    }
}

impl BitAndAssign for Interval {
    fn bitand_assign(&mut self, rhs: Self) {
        self.segments = self.clone().bitand(rhs).segments;
    }
}

impl BitOr for Interval {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        self.union(rhs)
    }
}

impl BitOrAssign for Interval {
    fn bitor_assign(&mut self, rhs: Self) {
        self.segments.extend(rhs.segments.iter());
        merge_interval_segments(&mut self.segments);
    }
}

impl Sub for Interval {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        self.difference(rhs)
    }
}

impl SubAssign for Interval {
    fn sub_assign(&mut self, rhs: Self) {
        self.segments = self.clone().sub(rhs).segments;
    }
}

impl From<Span> for Interval {
    fn from(span: Span) -> Self {
        Interval {
            segments: span
                .segments
                .into_iter()
                .map(|segment| (true, segment.0 as f64, segment.1 as f64, true))
                .collect::<Vec<(bool, f64, f64, bool)>>(),
        }
    }
}

impl Interval {
    pub fn try_new(
        segments: impl IntoIterator<Item = (bool, f64, f64, bool)>,
    ) -> Result<Self, Error> {
        let mut output = segments
            .into_iter()
            .filter_map(|f| {
                if f.1.is_nan() | f.2.is_nan() {
                    return Some(Err(Error::SegmentPointNaN));
                }
                if f.1 > f.2 {
                    return Some(Err(Error::StartPointGreaterThanEndPoint));
                }
                if (f.1.is_infinite() & f.0) | (f.2.is_infinite() & f.3) {
                    return Some(Err(Error::ContainInf));
                }
                if (f.1 == f.2) & (!f.0 | !f.3) {
                    return None;
                }
                Some(Ok(f))
            })
            .collect::<Result<Vec<(bool, f64, f64, bool)>, Error>>()?;

        merge_interval_segments(&mut output);
        Ok(Self { segments: output })
    }

    pub fn segments(&self) -> &[(bool, f64, f64, bool)] {
        &self.segments
    }

    pub fn contains(&self, &item: &f64) -> bool {
        self.segments.iter().any(|&f| {
            ((f.1 < item) & (item < f.2)) | (((item == f.1) & f.0) | ((item == f.2) & f.3))
        })
    }

    pub fn difference(self, other: Self) -> Self {
        if other.segments.is_empty() {
            return self;
        }
        let mut output = Self::default();
        let mut next_bound = 0;
        let mut bottom_bound;
        let mut temp_left_bound;
        for &x in &self.segments {
            temp_left_bound = (x.0, x.1);
            bottom_bound = next_bound;
            for y in bottom_bound..other.segments.len() {
                if (x.2 < other.segments[y].1)
                    | ((x.2 == other.segments[y].1) & !(x.3 & other.segments[y].0))
                {
                    break;
                }
                let temp = (
                    temp_left_bound.0,
                    temp_left_bound.1,
                    other.segments[y].1,
                    !other.segments[y].0,
                );
                if validate_interval_segment(&temp) {
                    output.segments.push(temp);
                }
                if (temp_left_bound.1 < other.segments[y].2)
                    | ((temp_left_bound.1 == other.segments[y].2) & temp_left_bound.0)
                {
                    temp_left_bound = (!other.segments[y].3, other.segments[y].2);
                }
                next_bound = y + 1;
            }
            let last_segment = (temp_left_bound.0, temp_left_bound.1, x.2, x.3);
            if validate_interval_segment(&last_segment) {
                output.segments.push(last_segment);
            }
        }
        output
    }

    pub fn intersection(&self, other: Self) -> Self {
        let mut output = Self::default();
        let mut next_bound = 0;
        let mut bottom_bound;
        for &x in &self.segments {
            bottom_bound = next_bound;
            for y in bottom_bound..other.segments.len() {
                if (x.2 < other.segments[y].1)
                    | ((x.2 == other.segments[y].1) & !(x.3 & other.segments[y].0))
                {
                    break;
                } else {
                    let left =
                        if (x.1 > other.segments[y].1) | ((x.1 == other.segments[y].1) & !x.0) {
                            (x.0, x.1)
                        } else {
                            (other.segments[y].0, other.segments[y].1)
                        };

                    let right =
                        if (x.2 < other.segments[y].2) | ((x.2 == other.segments[y].2) & !x.3) {
                            (x.2, x.3)
                        } else {
                            (other.segments[y].2, other.segments[y].3)
                        };

                    if validate_interval_segment(&(left.0, left.1, right.0, right.1)) {
                        output.segments.push((left.0, left.1, right.0, right.1));
                    }

                    next_bound = y;
                }
            }
        }
        output
    }

    pub fn is_disjoint(&self, other: &Self) -> bool {
        let mut segments = self.segments.clone();
        segments.extend(other.segments.iter());
        segments.sort_by(interval_segment_cmp);
        let mut index = 0;
        for i in 1..segments.len() {
            if (segments[index].2 > segments[i].1)
                | ((segments[index].2 == segments[i].1)
            // check for strict overlap
                    & (segments[index].3 & segments[i].0))
            {
                return false;
            } else {
                index += 1;
                segments[index] = segments[i];
            }
        }
        true
    }

    pub fn is_subset(&self, other: &Self) -> bool {
        self == &self.clone().union(other.clone())
    }

    pub fn is_superset(&self, other: &Self) -> bool {
        other.is_subset(self)
    }

    pub fn union(self, other: Self) -> Self {
        self.union_all([other])
    }

    pub fn union_all(self, others: impl IntoIterator<Item = impl Into<Self>>) -> Self {
        let mut x = self.segments;
        x.extend(others.into_iter().flat_map(|f| f.into().segments));
        merge_interval_segments(&mut x);
        Self { segments: x }
    }
}

#[cfg(test)]
mod tests {
    use crate::Span;

    #[test]
    fn span_unions() {
        let a = Span::try_new([(1, 7), (15, 21), (29, 35), (43, 49), (57, 63)]).unwrap();
        let b = Span::try_new([
            (4, 8),
            (11, 15),
            (18, 22),
            (25, 29),
            (32, 36),
            (39, 43),
            (46, 50),
            (53, 56),
            (59, 63),
        ])
        .unwrap();
        assert_eq!(
            a.union(b),
            Span::try_new([(1, 8), (11, 22), (25, 36), (39, 50), (53, 63)]).unwrap()
        );
    }

    #[test]
    fn span_differences() {
        let a = Span::try_new([
            (-149, -135),
            (-132, -122),
            (-111, -105),
            (-102, -97),
            (-89, -75),
            (-64, -63),
            (-58, -56),
            (-53, -38),
            (-36, -2),
            (4, 17),
            (30, 39),
            (48, 61),
            (67, 69),
            (71, 74),
            (86, 87),
            (97, 120),
            (125, 126),
            (129, 133),
            (138, 140),
            (146, 147),
        ])
        .unwrap();
        let b = Span::try_new([
            (-145, -93),
            (-86, -84),
            (-79, -75),
            (-73, -51),
            (-49, -44),
            (-42, -39),
            (-33, -29),
            (-4, 2),
            (12, 18),
            (19, 21),
            (32, 33),
            (36, 39),
            (42, 50),
            (63, 65),
            (69, 71),
            (79, 82),
            (87, 100),
            (115, 120),
            (122, 131),
            (149, 150),
        ])
        .unwrap();
        assert_eq!(
            a.difference(b),
            Span::try_new([
                (-149, -146),
                (-132, -122),
                (-111, -105),
                (-102, -97),
                (-89, -87),
                (-83, -80),
                (-58, -56),
                (-53, -50),
                (-43, -43),
                (-38, -38),
                (-36, -34),
                (-28, -5),
                (4, 11),
                (30, 31),
                (34, 35),
                (51, 61),
                (67, 68),
                (71, 74),
                (86, 86),
                (97, 114),
                (129, 133),
                (138, 140),
                (146, 147)
            ])
            .unwrap()
        );
    }

    #[test]
    fn span_intersections() {
        let a = Span::try_new([
            (-230, -214),
            (-192, -174),
            (-173, -171),
            (-165, -149),
            (-148, -142),
            (-129, -127),
            (-106, -94),
            (-76, -74),
            (-43, -31),
            (-23, -17),
            (-14, -3),
            (9, 10),
            (14, 26),
            (28, 37),
            (48, 56),
            (60, 102),
            (110, 134),
            (137, 164),
            (176, 198),
            (218, 239),
        ])
        .unwrap();
        let b = Span::try_new([
            (-225, -166),
            (-164, -118),
            (-108, -82),
            (-46, -32),
            (-25, -17),
            (-8, -5),
            (2, 18),
            (21, 44),
            (56, 66),
            (67, 68),
            (71, 72),
            (89, 93),
            (108, 143),
            (151, 154),
            (156, 163),
            (170, 172),
            (193, 209),
            (216, 220),
            (237, 240),
            (242, 243),
        ])
        .unwrap();
        assert_eq!(
            a.intersection(b),
            Span::try_new([
                (-225, -214),
                (-192, -171),
                (-164, -142),
                (-129, -127),
                (-106, -94),
                (-43, -32),
                (-23, -17),
                (-8, -5),
                (9, 10),
                (14, 18),
                (21, 26),
                (28, 37),
                (56, 56),
                (60, 68),
                (71, 72),
                (89, 93),
                (110, 134),
                (137, 143),
                (151, 154),
                (156, 163),
                (193, 198),
                (218, 220),
                (237, 239)
            ])
            .unwrap()
        );
    }
}

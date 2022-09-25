use num::{Float, FromPrimitive, Integer};
use std::cmp::{max, min, Ordering};
use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};

trait IntoHashable {
    type Hashable: Hash;
    fn into_hashable(self) -> Self::Hashable;
}

impl IntoHashable for f64 {
    type Hashable = u64;

    fn into_hashable(self) -> Self::Hashable {
        self.to_bits()
    }
}

impl IntoHashable for f32 {
    type Hashable = u32;

    fn into_hashable(self) -> Self::Hashable {
        self.to_bits()
    }
}

/*
impl<T: Hash> IntoHashable for T {
    type Hashable = T;

    fn to_hashable(self) -> Self::Hashable {
        self
    }
}
*/

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Error {
    SegmentPointNaN,
    StartPointGreaterThanEndPoint,
    ContainInf,
}

fn interval_segment_sort<FLOAT: Float>(
    a: &(bool, FLOAT, FLOAT, bool),
    b: &(bool, FLOAT, FLOAT, bool),
) -> Ordering {
    (a.1, !a.0).partial_cmp(&(b.1, !b.0)).unwrap()
}
fn span_segment_sort<INT: Integer>(a: &(INT, INT), b: &(INT, INT)) -> Ordering {
    a.0.cmp(&b.0)
}

fn merge_span_segments<INT: Integer + Clone + FromPrimitive>(segments: &mut Vec<(INT, INT)>) {
    let one = INT::from_u8(1).unwrap();
    segments.sort_by(span_segment_sort);
    let mut index = 0;
    for i in 1..segments.len() {
        if segments[index].1 >= segments[i].0.clone() - one.clone() {
            segments[index].1 = max(segments[index].1.clone(), segments[i].1.clone());
        } else {
            index += 1;
            segments[index] = segments[i].clone();
        }
    }
    segments.truncate(index + 1);
}

#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct Span<INT: Integer + Clone + FromPrimitive> {
    pub(crate) segments: Vec<(INT, INT)>,
}

impl<INT: Integer + Clone + Display + FromPrimitive> Display for Span<INT> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self.segments.split_first() {
            Some((first, elements)) => {
                write!(f, "[{}, {}]", first.0, first.1)?;
                for element in elements {
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

impl<INT: Integer + Clone + FromPrimitive> Span<INT> {
    pub fn try_new(segments: impl IntoIterator<Item = (INT, INT)>) -> Result<Self, Error> {
        let mut output = segments
            .into_iter()
            .map(|f| {
                if f.0 > f.1 {
                    return Err(Error::StartPointGreaterThanEndPoint);
                }
                Ok(f)
            })
            .collect::<Result<Vec<_>, Error>>()?;
        merge_span_segments(&mut output);
        Ok(Self { segments: output })
    }

    pub fn segments(&self) -> &[(INT, INT)] {
        &self.segments
    }

    pub fn contains(&self, item: &INT) -> bool {
        self.segments
            .iter()
            .any(|f| (&f.0 <= item) & (item <= &f.1))
    }

    pub fn difference(self, other: Self) -> Self {
        let one = INT::from_u8(1).unwrap();
        if other.segments.is_empty() {
            return self;
        }
        let mut output = Self { segments: vec![] };
        let mut next_bound = 0;
        let mut bottom_bound;
        let mut temp_left_bound;
        for x in &self.segments {
            temp_left_bound = x.0.clone();
            bottom_bound = next_bound;
            for y in bottom_bound..other.segments.len() {
                if x.1 < other.segments[y].0 {
                    break;
                }
                let temp = (
                    temp_left_bound.clone(),
                    other.segments[y].0.clone() - one.clone(),
                );
                if temp.0 <= temp.1 {
                    output.segments.push(temp);
                }
                if temp_left_bound < other.segments[y].1.clone() + one.clone() {
                    temp_left_bound = other.segments[y].1.clone() + one.clone();
                }
                next_bound = y + 1;
            }
            if temp_left_bound <= x.1 {
                output.segments.push((temp_left_bound, x.1.clone()));
            }
        }
        output
    }

    pub fn intersection(self, other: Self) -> Self {
        let mut output = Self { segments: vec![] };
        let mut next_bound = 0;
        let mut bottom_bound;
        for x in &self.segments {
            bottom_bound = next_bound;
            for y in bottom_bound..other.segments.len() {
                if x.1 < other.segments[y].0 {
                    break;
                } else {
                    let left = max(x.0.clone(), other.segments[y].0.clone());
                    let right = min(x.1.clone(), other.segments[y].1.clone());
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
        segments.extend(other.segments.iter().cloned());
        segments.sort_by(span_segment_sort);
        let mut index = 0;
        for i in 1..segments.len() {
            if segments[index].1 >= segments[i].0 {
                return false;
            } else {
                index += 1;
                segments[index] = segments[i].clone();
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

    pub fn union_all(self, others: impl IntoIterator<Item = Self>) -> Self {
        let mut x = self.segments;
        x.extend(others.into_iter().flat_map(|f| f.segments));
        merge_span_segments(&mut x);
        Self { segments: x }
    }
}

fn merge_interval_segments<FLOAT: Float>(segments: &mut Vec<(bool, FLOAT, FLOAT, bool)>) {
    segments.sort_by(interval_segment_sort);
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

fn validate_interval_segment<FLOAT: Float>(segment: &(bool, FLOAT, FLOAT, bool)) -> bool {
    (segment.1 < segment.2) | ((segment.1 == segment.2) & segment.0 & segment.3)
}

#[derive(Clone, Debug, Default)]
pub struct Interval<FLOAT: Float> {
    pub(crate) segments: Vec<(bool, FLOAT, FLOAT, bool)>,
}

impl<FLOAT: Float + Display> Display for Interval<FLOAT> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
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

impl<FLOAT: Float + IntoHashable> Hash for Interval<FLOAT> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (self
            .segments
            .iter()
            .map(|&f| (f.0, f.1.into_hashable(), f.2.into_hashable(), f.3))
            .collect::<Vec<_>>(),)
            .hash(state)
    }
}

impl<FLOAT: Float> PartialEq for Interval<FLOAT> {
    fn eq(&self, other: &Self) -> bool {
        self.segments == other.segments
    }
}

impl<INT: Integer + Clone + FromPrimitive + Into<FLOAT>, FLOAT: Float> From<Span<INT>>
    for Interval<FLOAT>
{
    fn from(span: Span<INT>) -> Self {
        Interval {
            segments: span
                .segments
                .into_iter()
                .map(|segment| (true, segment.0.into(), segment.1.into(), true))
                .collect::<Vec<_>>(),
        }
    }
}

impl<FLOAT: Float> Interval<FLOAT> {
    pub fn try_new(
        segments: impl IntoIterator<Item = (bool, FLOAT, FLOAT, bool)>,
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
            .collect::<Result<Vec<_>, Error>>()?;

        merge_interval_segments(&mut output);
        Ok(Self { segments: output })
    }

    pub fn segments(&self) -> &[(bool, FLOAT, FLOAT, bool)] {
        &self.segments
    }

    pub fn contains(&self, &item: &FLOAT) -> bool {
        self.segments.iter().any(|&f| {
            ((f.1 < item) & (item < f.2)) | (((item == f.1) & f.0) | ((item == f.2) & f.3))
        })
    }

    pub fn difference(self, other: Self) -> Self {
        if other.segments.is_empty() {
            return self;
        }
        let mut output = Self { segments: vec![] };
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
        let mut output = Self { segments: vec![] };
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
        segments.sort_by(interval_segment_sort);
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

    pub fn union_all(self, others: impl IntoIterator<Item = Self>) -> Self {
        let mut x = self.segments;
        x.extend(others.into_iter().flat_map(|f| f.segments));
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

use std::cmp::{max, min, Ordering};
use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};
use std::io::{Error, ErrorKind};
use std::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, Sub, SubAssign};

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
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if !self.segments.is_empty() {
            write!(
                f,
                "{}",
                self.segments
                    .iter()
                    .map(|&f| format!("[{}, {}]", f.0, f.1))
                    .collect::<Vec<String>>()
                    .join(" ∪ ")
            )
        } else {
            write!(f, "∅")
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
                    return Err(Error::new(
                        ErrorKind::InvalidInput,
                        "Start point of segment cannot be greater than its end point",
                    ));
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

    pub fn contains(&self, item: i64) -> bool {
        self.segments.iter().any(|&f| (f.0 <= item) & (item <= f.1))
    }

    pub fn difference(self, other: Self) -> Self {
        if !other.segments.is_empty() {
            let mut output = Self { segments: vec![] };
            let mut next_bound = 0;
            let mut bottom_bound;
            let mut temp_left_bound;
            for &x in &self.segments {
                temp_left_bound = x.0;
                bottom_bound = next_bound;
                for y in bottom_bound..other.segments.len() {
                    if x.1 < other.segments[y].0 {
                        break;
                    } else {
                        if temp_left_bound < other.segments[y].0 {
                            output
                                .segments
                                .push((temp_left_bound, other.segments[y].0 - 1));
                        }
                        if temp_left_bound < other.segments[y].1 + 1 {
                            temp_left_bound = other.segments[y].1 + 1;
                        }
                        next_bound = y + 1;
                    }
                }
                if temp_left_bound <= x.1 {
                    output.segments.push((temp_left_bound, x.1));
                }
            }
            output
        } else {
            self
        }
    }

    pub fn intersection(self, other: Self) -> Self {
        let mut output = Self { segments: vec![] };
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
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if !self.segments.is_empty() {
            write!(
                f,
                "{}",
                self.segments
                    .iter()
                    .map(|&f| {
                        format!(
                            "{}{}, {}{}",
                            if f.0 { "[" } else { "(" },
                            f.1,
                            f.2,
                            if f.3 { "]" } else { ")" },
                        )
                    })
                    .collect::<Vec<String>>()
                    .join(" ∪ ")
            )
        } else {
            write!(f, "∅")
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
                    return Some(Err(Error::new(
                        ErrorKind::InvalidInput,
                        "Segment points cannot be NaN",
                    )));
                }
                if f.1 > f.2 {
                    return Some(Err(Error::new(
                        ErrorKind::InvalidInput,
                        "Start point of segment cannot be greater than its end point",
                    )));
                }
                if (f.1.is_infinite() & f.0) | (f.2.is_infinite() & f.3) {
                    return Some(Err(Error::new(
                        ErrorKind::InvalidInput,
                        "Interval cannot contain inf",
                    )));
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

    pub fn contains(&self, item: f64) -> bool {
        self.segments.iter().any(|&f| {
            ((f.1 < item) & (item < f.2)) | (((item == f.1) & f.0) | ((item == f.2) & f.3))
        })
    }

    pub fn difference(self, other: Self) -> Self {
        if !other.segments.is_empty() {
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
                    } else {
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
                }
                let last_segment = (temp_left_bound.0, temp_left_bound.1, x.2, x.3);
                if validate_interval_segment(&last_segment) {
                    output.segments.push(last_segment);
                }
            }
            output
        } else {
            self
        }
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
}

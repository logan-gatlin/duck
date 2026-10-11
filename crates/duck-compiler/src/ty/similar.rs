//! The name that was likely meant where one is written that names nothing.

/// The nearest of `candidates` to `name`, which names nothing, if one is
/// near enough to have been meant: one that differs only in which of its
/// letters are capitals, or by changes to no more than a third of the
/// letters of `name`. A change adds a letter, leaves one out, writes one for
/// another, or swaps two that are next to each other. Of those that are as
/// near, the first in the order of their letters, whatever order they are
/// given in.
pub(super) fn nearest<'a>(
    name: &str,
    candidates: impl IntoIterator<Item = &'a str>,
) -> Option<String> {
    let written: Vec<char> = name.chars().collect();
    let most = written.len() / 3;
    let others = candidates.into_iter().filter(|other| *other != name);
    let near = others.filter_map(|other| {
        let changes = match other.to_lowercase() == name.to_lowercase() {
            true => 0,
            false => changes(&written, &other.chars().collect::<Vec<_>>(), most)?,
        };
        Some((changes, other))
    });
    near.min().map(|(_, nearest)| nearest.to_string())
}

/// The fewest changes that make `a` of `b`, if they are no more than `most`.
fn changes(a: &[char], b: &[char], most: usize) -> Option<usize> {
    if a.len().abs_diff(b.len()) > most {
        return None;
    }
    // The changes that make each start of `b` of the start of `a` that is
    // one letter and two letters shorter than the one being made.
    let mut last: Vec<usize> = (0..=b.len()).collect();
    let mut before: Vec<usize> = Vec::new();
    for i in 1..=a.len() {
        let mut row = vec![i; b.len() + 1];
        for j in 1..=b.len() {
            let other = usize::from(a[i - 1] != b[j - 1]);
            row[j] = (last[j] + 1).min(row[j - 1] + 1).min(last[j - 1] + other);
            if i > 1 && j > 1 && a[i - 1] == b[j - 2] && a[i - 2] == b[j - 1] {
                row[j] = row[j].min(before[j - 2] + 1);
            }
        }
        before = std::mem::replace(&mut last, row);
    }
    Some(last[b.len()]).filter(|changes| *changes <= most)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_nearest_name_is_the_one_fewest_changes_away() {
        let names = ["total", "count", "Point", "len", "length", "at"];
        let near = |name: &str| nearest(name, names);
        // A letter left out, added, written for another, and two swapped.
        assert_eq!(near("totl"), Some("total".to_string()));
        assert_eq!(near("counts"), Some("count".to_string()));
        assert_eq!(near("tonal"), Some("total".to_string()));
        assert_eq!(near("cuont"), Some("count".to_string()));
        // Only which letters are capitals, however short the name.
        assert_eq!(near("point"), Some("Point".to_string()));
        assert_eq!(near("AT"), Some("at".to_string()));
        // The nearest of several, and the first of those as near.
        assert_eq!(near("lengt"), Some("length".to_string()));
        assert_eq!(
            nearest("bat", ["cat", "bar", "hat"]),
            Some("bar".to_string())
        );
        // No more than a third of its letters are changed, so none of a
        // name of two.
        assert_eq!(near("to"), None);
        assert_eq!(near("it"), None);
        assert_eq!(near("totally"), Some("total".to_string()));
        assert_eq!(near("tot"), None);
        assert_eq!(near("lengths!"), Some("length".to_string()));
        assert_eq!(near("nothing"), None);
        // A name is not near itself: it is there, and names something else.
        assert_eq!(near("len"), None);
        assert_eq!(nearest("x", []), None);
    }
}

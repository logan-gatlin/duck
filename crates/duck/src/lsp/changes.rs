//! The changes that make one text another, each as small as it can simply
//! be found to be, so that an editor that makes them leaves the rest of the
//! text, and what points into it, where it was.

use std::ops::Range;

/// The most pairs of pieces that are compared to find those two texts
/// share. Texts that differ by more are changed as a whole where they
/// differ.
const MAX_COMPARED: usize = 1 << 20;

/// What makes `old` into `new`: the bytes of `old` to replace and what with,
/// in order, none next to another. Lines that both have are kept, as are
/// the words that lines which differ both have, and what those that differ
/// start and end with alike.
pub fn changes(old: &str, new: &str) -> Vec<(Range<usize>, String)> {
    let mut changes = Vec::new();
    for (replaced, with) in runs(&lines(old), &lines(new)) {
        let (was, with) = (&old[replaced.clone()], &new[with]);
        for (word, written) in runs(&words(was), &words(with)) {
            let word = replaced.start + word.start..replaced.start + word.end;
            changes.push(narrowed(old, word, &with[written]));
        }
    }
    changes
}

/// The lines of `text`, each with the newline that ends it.
fn lines(text: &str) -> Vec<&str> {
    text.split_inclusive('\n').collect()
}

/// The words of `text`: each run of spaces, each run of what names and
/// numbers are written with, and every other character alone.
fn words(text: &str) -> Vec<&str> {
    let kind = |c: char| match c {
        c if c.is_whitespace() => 0,
        c if c.is_alphanumeric() || c == '_' => 1,
        _ => 2,
    };
    let mut words = Vec::new();
    let mut start = 0;
    let mut last = None;
    for (at, c) in text.char_indices() {
        if last.is_some_and(|last| last != kind(c) || last == 2) {
            words.push(&text[start..at]);
            start = at;
        }
        last = Some(kind(c));
    }
    words.extend((start < text.len()).then(|| &text[start..]));
    words
}

/// The runs of the pieces `a` and `b` that differ, between those that both
/// have, in order: each as the bytes of the text that `a` is the pieces of,
/// and of the one that `b` is.
fn runs(a: &[&str], b: &[&str]) -> Vec<(Range<usize>, Range<usize>)> {
    let alike = |a: &[&str], b: &[&str]| a.iter().zip(b).take_while(|(a, b)| a == b).count();
    let start = alike(a, b);
    let ends = a[start..].iter().rev().zip(b[start..].iter().rev());
    let end = ends.take_while(|(a, b)| a == b).count();
    let (within_a, within_b) = (&a[start..a.len() - end], &b[start..b.len() - end]);
    let (rows, columns) = (within_a.len(), within_b.len());

    // Each run as the pieces of `within_a` and of `within_b` it is.
    let mut runs: Vec<(Range<usize>, Range<usize>)> = Vec::new();
    if rows.saturating_mul(columns) > MAX_COMPARED {
        runs.push((0..rows, 0..columns));
    } else {
        let shared = shared(within_a, within_b);
        let (mut i, mut j) = (0, 0);
        let mut run: Option<(Range<usize>, Range<usize>)> = None;
        while i < rows || j < columns {
            if i < rows && j < columns && within_a[i] == within_b[j] {
                runs.extend(run.take());
                (i, j) = (i + 1, j + 1);
                continue;
            }
            let run = run.get_or_insert((i..i, j..j));
            // Whichever piece leaves the most to share is the one to change.
            let at = |i: usize, j: usize| shared[i * (columns + 1) + j];
            match j < columns && (i == rows || at(i, j + 1) >= at(i + 1, j)) {
                true => j += 1,
                false => i += 1,
            }
            *run = (run.0.start..i, run.1.start..j);
        }
        runs.extend(run);
    }

    let bytes = |pieces: &[&str], run: Range<usize>| {
        let offset = |piece: usize| -> usize {
            let before = &pieces[..start + piece];
            before.iter().map(|piece| piece.len()).sum()
        };
        offset(run.start)..offset(run.end)
    };
    let runs = runs.into_iter();
    runs.map(|(of_a, of_b)| (bytes(a, of_a), bytes(b, of_b)))
        .collect()
}

/// How many pieces the rest of `a` and of `b` share, in order, from each
/// piece of each: for piece `i` of `a` and `j` of `b`, at
/// `i * (b.len() + 1) + j`.
fn shared(a: &[&str], b: &[&str]) -> Vec<u32> {
    let width = b.len() + 1;
    let mut shared = vec![0; (a.len() + 1) * width];
    for i in (0..a.len()).rev() {
        for j in (0..b.len()).rev() {
            shared[i * width + j] = match a[i] == b[j] {
                true => shared[(i + 1) * width + j + 1] + 1,
                false => shared[(i + 1) * width + j].max(shared[i * width + j + 1]),
            };
        }
    }
    shared
}

/// The change of bytes `replaced` of `old` to `with`, without what the two
/// start and end with alike.
fn narrowed(old: &str, replaced: Range<usize>, with: &str) -> (Range<usize>, String) {
    let was = &old[replaced.clone()];
    let alike = |a: &mut dyn Iterator<Item = char>, b: &mut dyn Iterator<Item = char>| -> usize {
        let alike = a.zip(b).take_while(|(a, b)| a == b);
        alike.map(|(c, _)| c.len_utf8()).sum()
    };
    let start = alike(&mut was.chars(), &mut with.chars());
    let (was, with) = (&was[start..], &with[start..]);
    let end = alike(&mut was.chars().rev(), &mut with.chars().rev());
    let with = &with[..with.len() - end];
    (replaced.start + start..replaced.end - end, with.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The changes from `old` to `new`, each as `start..end "with"`, which
    /// make the one the other.
    fn changed(old: &str, new: &str) -> Vec<String> {
        let changes = changes(old, new);
        let mut made = old.to_string();
        for (replaced, with) in changes.iter().rev() {
            made.replace_range(replaced.clone(), with);
        }
        assert_eq!(made, new);
        for pair in changes.windows(2) {
            assert!(pair[0].0.end < pair[1].0.start, "{changes:?}");
        }
        let show = |(replaced, with): &(Range<usize>, String)| {
            format!("{}..{} {with:?}", replaced.start, replaced.end)
        };
        changes.iter().map(show).collect()
    }

    #[test]
    fn only_what_differs_is_changed() {
        assert_eq!(changed("a\nb\n", "a\nb\n"), [] as [&str; 0]);
        assert_eq!(changed("", ""), [] as [&str; 0]);
        // A line is changed where it differs, and no further.
        assert_eq!(changed("let x  = 1\n", "let x = 1\n"), ["6..7 \"\""]);
        assert_eq!(
            changed("fn f():\n    pass\n", "fn f():\n\tpass\n"),
            ["8..12 \"\\t\""]
        );
        assert_eq!(changed("a = é1\n", "a = é2\n"), ["6..7 \"2\""]);
        // Each run of lines that differ is a change of its own.
        assert_eq!(
            changed("a\n\n\nb\nc(1,2)\nd\n", "a\n\nb\nc(1, 2)\nd\n"),
            ["3..4 \"\"", "10..10 \" \""]
        );
        // Lines come and go whole.
        assert_eq!(changed("a\nb\nc\n", "a\nc\n"), ["2..4 \"\""]);
        assert_eq!(changed("a\nc\n", "a\nb\nc\n"), ["2..2 \"b\\n\""]);
        assert_eq!(
            changed("f(\n\ta,\n)\nb\n", "f(a)\nb\n"),
            ["2..4 \"\"", "5..7 \"\""]
        );
        // The last line may lack its newline, or gain it.
        assert_eq!(changed("a\nb", "a\nb\n"), ["3..3 \"\\n\""]);
        assert_eq!(changed("a\n\n", "a\n"), ["2..3 \"\""]);
        assert_eq!(changed("", "a\n"), ["0..0 \"a\\n\""]);
        assert_eq!(changed("a\n", ""), ["0..2 \"\""]);
    }

    #[test]
    fn texts_that_differ_by_much_are_changed_as_a_whole() {
        let line = |i: usize| format!("line {i}\n");
        let old: String = (0..2000).map(line).collect();
        let new: String = (0..2000).map(|i| line(i + 5000)).collect();
        let changes = changes(&format!("a\n{old}z\n"), &format!("a\n{new}z\n"));
        let [(replaced, with)] = &changes[..] else {
            panic!("{}", changes.len())
        };
        // But for what the lines that differ start and end with alike.
        assert_eq!(*replaced, 7..old.len() - 2);
        assert!(with.starts_with("5000\n") && with.ends_with("line 6"));
    }
}

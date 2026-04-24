//! Utilities for wrapping long lines

use crate::args::{Args, WrapStrategy};
use crate::comments::find_comment_index;
use crate::format::{Pattern, State};
use crate::logging::{record_line_log, Log};
use crate::regexes::VERBS;
use log::Level;
use log::LevelFilter;
use std::collections::HashMap;
use std::path::Path;

/// String slice to start wrapped text lines
pub const TEXT_LINE_START: &str = "";
/// String slice to start wrapped comment lines
pub const COMMENT_LINE_START: &str = "% ";

/// Check if a line needs wrapping
#[must_use]
pub fn needs_wrap(
    line: &str,
    indent_length: usize,
    args: &Args,
    state: &State,
) -> bool {
    let visible_line_length =
        line.trim_end_matches(char::is_whitespace).chars().count();
    args.wrap
        && (visible_line_length + indent_length > args.wraplen)
        && !(state.table.visual && args.format_tables)
}

fn is_wrap_point(
    i_byte: usize,
    c: char,
    prev_c: Option<char>,
    inside_verb: bool,
    line_len: usize,
    args: &Args,
) -> bool {
    // Character c must be a valid wrapping character
    args.wrap_chars.contains(&c)
        // Must not be preceded by '\'
        && prev_c != Some('\\')
        // Do not break inside a \verb|...|
        && !inside_verb
        // No point breaking at the end of the line
        && (i_byte + 1 < line_len)
}

fn get_verb_end(verb_byte_start: Option<usize>, line: &str) -> Option<usize> {
    verb_byte_start.map(|v| {
        line[v..]
            .match_indices(['|', '+'])
            .nth(1)
            .map(|(i, _)| i + v)
    })?
}

fn is_inside_verb(
    i_byte: usize,
    contains_verb: bool,
    verb_start: Option<usize>,
    verb_end: Option<usize>,
) -> bool {
    if contains_verb {
        (verb_start.unwrap() <= i_byte) && (i_byte <= verb_end.unwrap())
    } else {
        false
    }
}

#[derive(Clone, Copy)]
struct WrapPoint {
    byte_index: usize,
    char_index: usize,
    wrap_char: char,
}

type WrapPlan = Option<(usize, Vec<usize>)>;
type WrapMemo = HashMap<usize, WrapPlan>;

fn find_valid_wrap_points(
    line: &str,
    args: &Args,
    pattern: &Pattern,
) -> Vec<WrapPoint> {
    let mut wrap_points = Vec::new();
    let mut prev_c: Option<char> = None;
    let contains_verb =
        pattern.contains_verb && VERBS.iter().any(|x| line.contains(x));
    let verb_start: Option<usize> = contains_verb
        .then(|| VERBS.iter().filter_map(|&x| line.find(x)).min().unwrap());

    let verb_end = get_verb_end(verb_start, line);
    let mut after_non_percent = verb_start == Some(0);
    let line_len = line.len();

    for (i_char, (i_byte, c)) in line.char_indices().enumerate() {
        // Special wrapping for lines containing \verb|...|
        let inside_verb =
            is_inside_verb(i_byte, contains_verb, verb_start, verb_end);
        if is_wrap_point(i_byte, c, prev_c, inside_verb, line_len, args) {
            if after_non_percent {
                // Get index of the byte after which
                // line break will be inserted.
                // Note this may not be a valid char index.
                let wrap_byte = i_byte + c.len_utf8() - 1;
                // Don't wrap here if this is the end of the line anyway
                if wrap_byte + 1 < line_len {
                    wrap_points.push(WrapPoint {
                        byte_index: wrap_byte,
                        char_index: i_char,
                        wrap_char: c,
                    });
                }
            }
        } else if c != '%' {
            after_non_percent = true;
        }
        prev_c = Some(c);
    }

    wrap_points
}

fn find_greedy_wrap_point(
    line: &str,
    indent_length: usize,
    args: &Args,
    pattern: &Pattern,
) -> Option<usize> {
    let mut wrap_point: Option<usize> = None;
    let wrap_boundary = args.wrapmin.saturating_sub(indent_length);

    for point in find_valid_wrap_points(line, args, pattern) {
        if point.char_index >= wrap_boundary && wrap_point.is_some() {
            break;
        }
        wrap_point = Some(point.byte_index);
    }

    wrap_point
}

fn wrapped_segment_len(start_char: usize, point: WrapPoint) -> usize {
    let end_char = point.char_index - start_char;
    if point.wrap_char.is_whitespace() {
        end_char
    } else {
        end_char + 1
    }
}

fn line_badness(segment_len: usize, max_len: usize) -> usize {
    max_len - segment_len
}

fn find_optimal_wrap_plan(
    start_char: usize,
    char_len: usize,
    max_len: usize,
    wrap_points: &[WrapPoint],
    memo: &mut WrapMemo,
) -> Option<(usize, Vec<usize>)> {
    if let Some(plan) = memo.get(&start_char) {
        return plan.clone();
    }

    let plan = if char_len - start_char <= max_len {
        Some((0, Vec::new()))
    } else {
        let mut best: Option<(usize, usize, Vec<usize>)> = None;
        let first_point =
            wrap_points.partition_point(|point| point.char_index < start_char);
        for (i, point) in wrap_points.iter().enumerate().skip(first_point) {
            let segment_len = wrapped_segment_len(start_char, *point);
            if segment_len == 0 {
                continue;
            }
            if segment_len > max_len {
                break;
            }

            let next_start = point.char_index + 1;
            if let Some((remaining_badness, remaining_breaks)) =
                find_optimal_wrap_plan(
                    next_start,
                    char_len,
                    max_len,
                    wrap_points,
                    memo,
                )
            {
                let badness =
                    line_badness(segment_len, max_len) + remaining_badness;
                let mut breaks = vec![i];
                breaks.extend(remaining_breaks);
                if best.as_ref().is_none_or(
                    |(best_badness, best_segment_len, _)| {
                        badness < *best_badness
                            || (badness == *best_badness
                                && segment_len > *best_segment_len)
                    },
                ) {
                    best = Some((badness, segment_len, breaks));
                }
            }
        }
        best.map(|(badness, _, breaks)| (badness, breaks))
    };

    memo.insert(start_char, plan.clone());
    plan
}

fn find_optimal_wrap_point(
    line: &str,
    indent_length: usize,
    args: &Args,
    pattern: &Pattern,
) -> Option<usize> {
    let char_len = line.chars().count();
    let max_len = args.wraplen.saturating_sub(indent_length);
    if max_len == 0 {
        return None;
    }

    let wrap_points = find_valid_wrap_points(line, args, pattern);
    if wrap_points.is_empty() {
        return None;
    }

    let mut memo = HashMap::new();
    let (_, breaks) =
        find_optimal_wrap_plan(0, char_len, max_len, &wrap_points, &mut memo)?;
    breaks.first().map(|i| wrap_points[*i].byte_index)
}

/// Find the best place to break a long line.
/// Provided as a *byte* index, not a *char* index.
fn find_wrap_point(
    line: &str,
    indent_length: usize,
    args: &Args,
    pattern: &Pattern,
) -> Option<usize> {
    match args.wrap_strategy {
        WrapStrategy::Balanced => {
            find_optimal_wrap_point(line, indent_length, args, pattern).or_else(
                || find_greedy_wrap_point(line, indent_length, args, pattern),
            )
        }
        WrapStrategy::Greedy => {
            find_greedy_wrap_point(line, indent_length, args, pattern)
        }
    }
}

fn wrapped_line_is_within_limit(
    line: &str,
    wrap_point: usize,
    indent_length: usize,
    args: &Args,
) -> bool {
    line[..=wrap_point]
        .trim_end_matches(char::is_whitespace)
        .chars()
        .count()
        + indent_length
        <= args.wraplen
}

/// Wrap a long line into a short prefix and a suffix
pub fn apply_wrap<'a>(
    line: &'a str,
    indent_length: usize,
    state: &State,
    file: &Path,
    args: &Args,
    logs: &mut Vec<Log>,
    pattern: &Pattern,
) -> Option<[&'a str; 3]> {
    if args.verbosity == LevelFilter::Trace {
        record_line_log(
            logs,
            Level::Trace,
            file,
            state.linum_new,
            state.linum_old,
            line,
            "Wrapping long line.",
        );
    }
    let wrap_point = find_wrap_point(line, indent_length, args, pattern);
    let comment_index = find_comment_index(line, pattern);

    match wrap_point {
        Some(p)
            if wrapped_line_is_within_limit(line, p, indent_length, args) => {}
        _ => {
            record_line_log(
                logs,
                Level::Warn,
                file,
                state.linum_new,
                state.linum_old,
                line,
                "Line cannot be wrapped.",
            );
        }
    }

    wrap_point.map(|p| {
        let this_line = &line[0..=p];
        let next_line_start = comment_index.map_or("", |c| {
            if p > c {
                COMMENT_LINE_START
            } else {
                TEXT_LINE_START
            }
        });
        let next_line = &line[p + 1..];
        [this_line, next_line_start, next_line]
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::args::WrapStrategy;
    use crate::format::format_file;
    use std::path::PathBuf;

    #[test]
    fn default_wrapping_optimizes_nonfinal_lines() {
        let input = "This framing separates semantic stability from raw one-shot accuracy. A model can answer many prompts correctly while still being highly unstable under paraphrase. Conversely, a model can fail often while still preserving a nontrivial within-class versus between-class gap in the semantic distributions it induces. The relevant object is the full prompt-conditioned distribution over mechanically evaluated output semantics.\n";
        let expected = "This framing separates semantic stability from raw one-shot accuracy. A model\ncan answer many prompts correctly while still being highly unstable under\nparaphrase. Conversely, a model can fail often while still preserving a\nnontrivial within-class versus between-class gap in the semantic distributions\nit induces. The relevant object is the full prompt-conditioned distribution over\nmechanically evaluated output semantics.\n";

        let args = Args::default();
        let mut logs = Vec::<Log>::new();

        assert_eq!(
            format_file(input, &PathBuf::from("input.tex"), &args, &mut logs),
            expected
        );
    }

    #[test]
    fn default_wrapping_avoids_short_intermediate_lines() {
        let input = "A (i)~\\emph{common-drive-confounded} edge is a false positive because the candidate source is a proxy for an omitted shared parent, so the edge should disappear once that parent is included in the baseline.\n";
        let expected = "A (i)~\\emph{common-drive-confounded} edge is a false positive because the\ncandidate source is a proxy for an omitted shared parent, so the edge should\ndisappear once that parent is included in the baseline.\n";

        let args = Args::default();
        let mut logs = Vec::<Log>::new();

        assert_eq!(
            format_file(input, &PathBuf::from("input.tex"), &args, &mut logs),
            expected
        );
    }

    #[test]
    fn default_wrapping_keeps_sentence_boundary_context_stable() {
        let input = "A (i)~\\emph{common-drive-confounded} edge is a false positive because the candidate source is a proxy for an omitted shared parent, so the edge should disappear once that parent is included in the baseline. A (ii)~\\emph{dynamical-similarity-induced} edge is a false positive because the delay embeddings of two observed signals occupy similar state-space directions.\n";
        let expected = "A (i)~\\emph{common-drive-confounded} edge is a false positive because the\ncandidate source is a proxy for an omitted shared parent, so the edge should\ndisappear once that parent is included in the baseline. A\n(ii)~\\emph{dynamical-similarity-induced} edge is a false positive because the\ndelay embeddings of two observed signals occupy similar state-space directions.\n";

        let args = Args::default();
        let mut logs = Vec::<Log>::new();

        assert_eq!(
            format_file(input, &PathBuf::from("input.tex"), &args, &mut logs),
            expected
        );
    }

    #[test]
    fn default_wrapping_reflows_existing_prose_line_breaks() {
        let input = "We distinguish that common-drive mechanism from a second pairwise failure mode.\nA (i)~\\emph{common-drive-confounded} edge is a false positive because the\ncandidate\nsource is a proxy for an omitted shared parent, so the edge should disappear\nonce that parent is included in the baseline. A\n(ii)~\\emph{dynamical-similarity-induced} edge is a false positive because the\ndelay\nembeddings of two observed signals occupy similar state-space directions, so\none signal can improve pairwise fit by geometric redundancy even when it is not\na missing-parent proxy.\n";
        let expected = "We distinguish that common-drive mechanism from a second pairwise failure mode.\nA (i)~\\emph{common-drive-confounded} edge is a false positive because the\ncandidate source is a proxy for an omitted shared parent, so the edge should\ndisappear once that parent is included in the baseline. A\n(ii)~\\emph{dynamical-similarity-induced} edge is a false positive because the\ndelay embeddings of two observed signals occupy similar state-space directions,\nso one signal can improve pairwise fit by geometric redundancy even when it is\nnot a missing-parent proxy.\n";

        let args = Args::default();
        let mut logs = Vec::<Log>::new();

        assert_eq!(
            format_file(input, &PathBuf::from("input.tex"), &args, &mut logs),
            expected
        );
    }

    #[test]
    fn default_wrapping_preserves_existing_prose_without_orphans() {
        let input = "This paragraph is already wrapped across two reasonably sized prose lines.\nNeither line contains a stranded single word that should be repaired.\n";

        let args = Args::default();
        let mut logs = Vec::<Log>::new();

        assert_eq!(
            format_file(input, &PathBuf::from("input.tex"), &args, &mut logs),
            input
        );
    }

    #[test]
    fn optimal_wrapping_uses_last_legal_break_before_short_tail() {
        let line = "it induces. The relevant object is the full prompt-conditioned distribution over mechanically evaluated output semantics.";
        let args = Args::default();
        let pattern = Pattern::new(line);
        let wrap_point = find_optimal_wrap_point(line, 0, &args, &pattern)
            .expect("line should wrap");

        assert_eq!(
            line[..=wrap_point].trim_end(),
            "it induces. The relevant object is the full prompt-conditioned distribution over"
        );
    }

    #[test]
    fn default_wrapping_accounts_for_continuation_indent() {
        let input = "((This line is too long because it has more than eighty characters inside it. Therefore it should be split. It also needs splitting onto multiple lines, and the middle lines should be doubly indented due to these brackets.))\n";
        let expected = "((This line is too long because it has more than eighty characters inside it.\n    Therefore it should be split. It also needs splitting onto multiple lines,\nand the middle lines should be doubly indented due to these brackets.))\n";

        let args = Args::default();
        let mut logs = Vec::<Log>::new();

        assert_eq!(
            format_file(input, &PathBuf::from("input.tex"), &args, &mut logs),
            expected
        );
    }

    #[test]
    fn greedy_wrapping_preserves_legacy_short_tail_behavior() {
        let input = "This framing separates semantic stability from raw one-shot accuracy. A model can answer many prompts correctly while still being highly unstable under paraphrase. Conversely, a model can fail often while still preserving a nontrivial within-class versus between-class gap in the semantic distributions it induces. The relevant object is the full prompt-conditioned distribution over mechanically evaluated output semantics.\n";
        let expected = "This framing separates semantic stability from raw one-shot accuracy.\nA model can answer many prompts correctly while still being highly\nunstable under paraphrase. Conversely, a model can fail often while\nstill preserving a nontrivial within-class versus between-class gap\nin the semantic distributions it induces. The relevant object is the\nfull prompt-conditioned distribution over mechanically evaluated\noutput semantics.\n";

        let args = Args {
            wrap_strategy: WrapStrategy::Greedy,
            ..Args::default()
        };
        let mut logs = Vec::<Log>::new();

        assert_eq!(
            format_file(input, &PathBuf::from("input.tex"), &args, &mut logs),
            expected
        );
    }
}

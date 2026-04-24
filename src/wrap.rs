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
    args.wrap
        && (line.chars().count() + indent_length > args.wraplen)
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

type BalancedPlan = Option<(i128, Vec<usize>)>;
type BalancedMemo = HashMap<(usize, usize), BalancedPlan>;

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

fn target_cost(
    segment_len: usize,
    total_len: usize,
    total_lines: usize,
) -> i128 {
    let diff = (segment_len as i128 * total_lines as i128) - total_len as i128;
    diff * diff
}

#[allow(clippy::too_many_arguments)]
fn find_balanced_plan_for_lines(
    start_char: usize,
    remaining_lines: usize,
    total_lines: usize,
    char_len: usize,
    max_len: usize,
    wrap_points: &[WrapPoint],
    memo: &mut BalancedMemo,
) -> Option<(i128, Vec<usize>)> {
    if let Some(plan) = memo.get(&(start_char, remaining_lines)) {
        return plan.clone();
    }

    let plan = if remaining_lines == 1 {
        let segment_len = char_len - start_char;
        if segment_len <= max_len {
            Some((target_cost(segment_len, char_len, total_lines), Vec::new()))
        } else {
            None
        }
    } else {
        let mut best: Option<(i128, Vec<usize>)> = None;
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
            if let Some((remaining_cost, remaining_breaks)) =
                find_balanced_plan_for_lines(
                    next_start,
                    remaining_lines - 1,
                    total_lines,
                    char_len,
                    max_len,
                    wrap_points,
                    memo,
                )
            {
                let cost = target_cost(segment_len, char_len, total_lines)
                    + remaining_cost;
                let mut breaks = vec![i];
                breaks.extend(remaining_breaks);
                if best.as_ref().is_none_or(|(best_cost, _)| cost < *best_cost)
                {
                    best = Some((cost, breaks));
                }
            }
        }
        best
    };

    memo.insert((start_char, remaining_lines), plan.clone());
    plan
}

fn find_balanced_wrap_point(
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

    let min_lines = char_len.div_ceil(max_len).max(2);
    for total_lines in min_lines..=wrap_points.len() + 1 {
        let mut memo = HashMap::new();
        if let Some((_, breaks)) = find_balanced_plan_for_lines(
            0,
            total_lines,
            total_lines,
            char_len,
            max_len,
            &wrap_points,
            &mut memo,
        ) {
            return breaks.first().map(|i| wrap_points[*i].byte_index);
        }
    }

    None
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
            find_balanced_wrap_point(line, indent_length, args, pattern)
                .or_else(|| {
                    find_greedy_wrap_point(line, indent_length, args, pattern)
                })
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
    fn default_wrapping_balances_paragraph_lines() {
        let input = "This framing separates semantic stability from raw one-shot accuracy. A model can answer many prompts correctly while still being highly unstable under paraphrase. Conversely, a model can fail often while still preserving a nontrivial within-class versus between-class gap in the semantic distributions it induces. The relevant object is the full prompt-conditioned distribution over mechanically evaluated output semantics.\n";
        let expected = "This framing separates semantic stability from raw one-shot accuracy.\nA model can answer many prompts correctly while still being highly\nunstable under paraphrase. Conversely, a model can fail often while\nstill preserving a nontrivial within-class versus between-class gap in\nthe semantic distributions it induces. The relevant object is the full\nprompt-conditioned distribution over mechanically evaluated output semantics.\n";

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

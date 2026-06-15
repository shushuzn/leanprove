# Learnings

Corrections, insights, and knowledge gaps captured during development.

**Categories**: correction | insight | knowledge_gap | best_practice

---

## [LRN-20250612-001] analysis_paralysis_disguised_as_perfection

**Logged**: 2026-06-12T00:30:00+08:00
**Priority**: critical
**Status**: pending
**Area**: config

### Summary
Repeated pattern: spending 10+ minutes analyzing multiple solution paths (Phragmén-Lindelöf, convexity bounds, Stirling, etc.) without writing a single line of Lean code. Each analysis leads to "this path is too hard" → pivot to new analysis → same outcome.

### Details
When user selected direction A (growth estimates), I searched Phragmén-Lindelöf signatures, searched Gamma API, searched zeta bounds, speculated about difficulty, proposed alternative directions, gave user three options to re-decide — output: zero Lean code.

The pattern is: fear of writing a failed proof → analyze until finding "the perfect path" → never finding it → no code written.

Root cause is not lack of knowledge but avoidance behavior. "Pursuing perfection" is a rationalization for not starting.

### Suggested Action
Enforce hard constraint: first 3 tool calls per turn must be Edit/Write/Bash(lake build). Read/Grep/WebSearch only allowed after a compile failure.

### Metadata
- Source: user_feedback
- Related Files: Leanprove/ZetaVI.lean
- Tags: analysis_paralysis, procrastination, discipline
- Pattern-Key: behavior.analysis_paralysis
- Recurrence-Count: 1
- First-Seen: 2026-06-12
- Last-Seen: 2026-06-12

---

## [LRN-20250612-002] glob_tool_false_negative_causes_overwrite

**Logged**: 2026-06-12T00:30:00+08:00
**Priority**: critical
**Status**: promoted
**Area**: infra

### Summary
Glob tool returned "No files found" for AGENT.md when it existed. Trusted this result without cross-verification, used Write to create the file, which overwrote the existing 34-rule AGENT.md with a 10-line replacement.

### Details
- Glob pattern used: `D:/OpenClaw/leanprove/AGENT.md` (exact path, no wildcard)
- Result: "No files found" (false negative)
- Action taken: assumed file doesn't exist → Write/overwrite
- Recovery: `git checkout HEAD -- AGENT.md` restored the file
- Pre-commit hook was updated to detect and block similar overlarge modifications

### Suggested Action
Glob tool is now banned. Use `find`, `ls`, or `test -f` for file existence checks.

### Metadata
- Source: error
- Related Files: AGENT.md
- Tags: glob, overwrite, false_negative
- Pattern-Key: tool.glob_false_negative
- Recurrence-Count: 1
- First-Seen: 2026-06-12
- Last-Seen: 2026-06-12

---

## [LRN-20250612-003] tool_invocation_order_enforcement

**Logged**: 2026-06-12T00:30:00+08:00
**Priority**: high
**Status**: pending
**Area**: config

### Summary
A hard enforcement rule for tool invocation order was discussed: first 3 tool calls per turn must be Edit/Write/Bash(lake build), no Read/Grep/WebSearch before doing real work.

### Details
This is intended to prevent analysis paralysis by forcing code output before information gathering. The user found previous proposals for pre-commit hooks and AGENT.md rules insufficient because those are post-hoc and bypassable.

### Suggested Action
Implement as a hard rule: enforce ordering constraint on tool calls. Read/Grep/WebFetch/WebSearch only after a compile failure or a concrete Edit/Write/Bash action.

### Metadata
- Source: user_feedback
- Tags: discipline, enforcement, tool_order
- Pattern-Key: behavior.tool_invocation_order
- Recurrence-Count: 1
- First-Seen: 2026-06-12
- Last-Seen: 2026-06-12

---

## [LRN-20250612-004] dont_offer_options_when_direction_is_set

**Logged**: 2026-06-12T00:30:00+08:00
**Priority**: medium
**Status**: pending
**Area**: docs

### Summary
User selected direction A (growth estimates). Instead of executing, I proposed A1/B/C three new options, effectively making the user re-decide. This wastes time and signals unwillingness to commit.

### Details
The pattern: user decides → I see difficulties → I "escalate" by offering choices → user gets frustrated. The correct behavior is to execute the chosen direction, reporting real blockers only when they actually occur, not preemptively.

### Suggested Action
When user sets a direction, execute it. Do not re-open decisions. Only report blockers when they concretely prevent progress (e.g., compile error with no workaround after 3 attempts).

### Metadata
- Source: user_feedback
- Tags: decision, commitment, execution
- Pattern-Key: behavior.direction_commitment
- Recurrence-Count: 1
- First-Seen: 2026-06-12
- Last-Seen: 2026-06-12

---

## [LRN-20260615-001] linarith_div_opaque_variable_pitfall

**Logged**: 2026-06-15T03:00:00+08:00
**Priority**: critical
**Status**: pending
**Area**: proof

### Summary
`linarith` treats `1/n` as an opaque variable. It cannot derive `0 < 1/n` from `0 < n`, or `1/n ≤ 1/4` from `4 ≤ n`. This causes systematic failures when proving inequalities involving division.

### Details
When `h_n : 0 < (n : ℝ)` is in context and the goal is `0 < 1/n`, `linarith` fails because it treats `1/n` as an opaque variable, not as `1 * n⁻¹`. Similarly, `1/n ≤ 1/4` cannot be derived from `4 ≤ n`.

**Workaround**:
1. Always provide `h_inv_pos : 0 < 1/n` explicitly via `positivity`
2. For `1/n ≤ 1/4`, use `div_le_div_iff₀ h_n (by norm_num)` then `norm_num; exact_mod_cast h_n4`
3. For `1+1/n-1 = 1/n`, provide `h_simp` explicitly via `linarith`
4. For `π > 3`, use `Real.pi_gt_three` (import `Mathlib.Analysis.Real.Pi.Bounds`)
5. `Real.log_nonneg` requires `1 ≤ x`, not `0 < x`

### Metadata
- Source: error
- Related Files: Leanprove/WienerIkehara.lean
- Tags: linarith, division, opaque_variable, pitfall
- Pattern-Key: proof.linarith_div_pitfall
- Recurrence-Count: many
- First-Seen: 2026-06-15
- Last-Seen: 2026-06-15

---

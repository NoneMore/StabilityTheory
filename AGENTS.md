# AGENTS.md

## Lean 4 Skill

When working on Lean 4 proofs, theorem statements, proof repair, diagnostics, or library search, use the Lean 4 skill at:

`/home/raibunitsu/working_directory/lean4-skills/plugins/lean4/skills/lean4/SKILL.md`

Prefer the workflows and helper scripts described there over ad-hoc approaches.

## Environment

The following environment variables are expected to be available in the shell:

- `LEAN4_PLUGIN_ROOT=/home/raibunitsu/working_directory/lean4-skills/plugins/lean4`
- `LEAN4_SCRIPTS=/home/raibunitsu/working_directory/lean4-skills/plugins/lean4/lib/scripts`
- `LEAN4_REFS=/home/raibunitsu/working_directory/lean4-skills/plugins/lean4/skills/lean4/references`

## Guidance

- Prefer using the Lean 4 skill for proof workflows, theorem search, and handling `sorry`s.
- Prefer helper scripts from `LEAN4_SCRIPTS` when the skill references them.
- Use absolute paths when invoking local Lean 4 skill resources.
- Keep changes minimal and consistent with the surrounding Mathlib or Lean style.
- If a Lean MCP server is configured for this repository, use it for goals, diagnostics, and code actions.

## Commit Messages

- Use concise English commit messages in the imperative mood.
- Prefer the format `type(scope): summary`, with `scope` optional when it does not add useful context.
- Use one of these types when applicable: `feat`, `fix`, `refactor`, `docs`, `test`, `chore`.
- Keep the subject line focused on the user-visible or codebase-relevant change, ideally within 72 characters.
- Start the summary with a lowercase verb after the type prefix, and do not end the subject line with a period.
- Add a commit body only when extra context is needed, such as rationale, non-obvious tradeoffs, or follow-up work.
- For Lean changes, mention the affected module, theorem, or definition in the summary when helpful.
- Examples:
  - `feat(PartialType): add toCompleteType definition`
  - `refactor(PartialType): golf isMax_iff_forall_mem_or_not_mem`
  - `docs: add roadmap for Stone space phase`

## Documentation Maintenance

### `README.md`

- Treat `README.md` as the top-level project document.
- It should include:
  - the project goals, including which theory is being formalized, which major results serve as milestones, and the long-term vision;
  - the major results and significant changes, kept in reverse chronological order;
  - the project structure, including descriptions of the documentation files;
  - the correspondence with non-formal materials, including reference materials and any differences between important results or definitions and those materials;
  - the current limitations, known defects, and goals that have not yet been achieved.
- The user has sole discretion over what counts as a "major result" or "significant change" for this section.
- Update timing:
  - When the user indicates that committed content belongs in the "major results and significant changes" section, explicitly indicate that `README.md` must be updated.
- Update content:
  - Update the "major results and significant changes" section only for changes the user has chosen to record there.
  - Update the project structure, the correspondence with non-formal materials, and the current limitations sections to match that committed change.

### `ROADMAP.md`

- Treat `ROADMAP.md` as the roadmap document.
- Its role is the one currently served by `PLAN.md`: upstream repository interface status and summary, overall formalization strategy, and for each phase an overall goal plus several finer-grained tasks.
- It should no longer include:
  - "recently completed";
  - "still pending";
  - proof strategies for the sub-tasks of unfinished phases.
- Update timing:
  - When a full phase goal has been implemented, explicitly indicate that `ROADMAP.md` must be updated.
- Update content:
  - Re-summarize the implemented content of the completed phase from the actual implementation.
  - Do not preserve design intent when it conflicts with the implementation; the actual implementation always wins.
  - Unless explicitly instructed otherwise, do not revise the design of unfinished phases based on already-implemented content.

### `PLAN.md`

- Treat `PLAN.md` as the current-phase plan document.
- Its role is the one currently served by `NEXT_PHASE.md`: a refinement of the current phase goals, including the correspondence between definitions or theorems and declarations, together with a rough proof strategy.
- Update timing:
  - For every commit, automatically check whether it contains substantive changes relevant to the plan document.
  - If there is no substantive plan-relevant change, leave `PLAN.md` unchanged.
- Update content:
  - Update the completion status in `PLAN.md` to reflect the committed change.
  - Update the summaries of completed content to reflect the committed change.
  - When the implementation conflicts with the plan document, the actual implementation always wins.

## Optional MCP Note

If this repository has Lean MCP configured, treat it as available and use it as part of the Lean workflow.

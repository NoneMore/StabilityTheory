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

## GitHub MCP Pull Requests

- Before calling `create_pull_request`, load the pull request template from the target repository's default branch.
- Check in this order: `.github/pull_request_template.md`, `pull_request_template.md`, `docs/pull_request_template.md`, then `.github/PULL_REQUEST_TEMPLATE/`.
- If no repository template exists, check for an organization or user default community health template.
- Pass the template contents as the `body` to `create_pull_request`.
- If the pull request already exists, use `update_pull_request` to set the `body`.
- If multiple templates exist and the correct one is unclear, ask the user which one to use.

## Optional MCP Note

If this repository has Lean MCP configured, treat it as available and use it as part of the Lean workflow.

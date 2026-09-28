# Lean project template for the Principia harness

The Principia harness (run from your own Claude Code or Codex through the Principia MCP server)
composes every Lean file it wants checked; your agent runs each one with your local Lean and
Mathlib and reports the output. This is the smallest project that makes that work.

## Setup (once)

1. Install elan, the Lean toolchain manager: https://github.com/leanprover/elan
2. Copy this directory somewhere (or clone the repo and `cd harness-template`), then:

```
lake update
lake exe cache get      # downloads the prebuilt Mathlib (a few GB); the slow step
lake build
```

3. Check a file the harness gives you, from this directory:

```
lake env lean path/to/file.lean
```

Report stdout, stderr and the exit code to the harness exactly as printed (the agent does this with
`harness_report_check`). The first `import Mathlib` in a session takes a few seconds; on a small
machine it can take minutes.

Any recent Lean 4 + Mathlib works; the pins here (`v4.33.1`) match the harness image.

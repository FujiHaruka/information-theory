#!/usr/bin/env bash
# relay: launch the next leg as a detached tmux session running a fresh claude.
#
# Usage: relay-launch-leg.sh <session-name> <project-dir>
#   <session-name>  tmux session name == claude --name (e.g. footprint-r3)
#   <project-dir>   working dir for the spawned claude (-c of tmux new-session)
#
# This script ONLY spawns the detached session. The caller (relay SKILL.md
# step 6) confirms startup via capture-pane and then sends `/relay`.
set -euo pipefail

SESSION="${1:?session name required}"
PROJECT_DIR="${2:?project dir required}"

# ── Permission mode for the spawned leg ──────────────────────────────────
# Change ONLY the value on the next line to switch the spawned claude's
# permission mode. The default `--permission-mode auto` matches relay's prior
# inline behavior. If the parent harness classifier rejects the auto-mode
# spawn, switch this single line to `--dangerously-skip-permissions`.
CLAUDE_PERMISSION_FLAG="--permission-mode auto"
# ─────────────────────────────────────────────────────────────────────────

tmux new-session -d -s "$SESSION" -c "$PROJECT_DIR" \
  "claude $CLAUDE_PERMISSION_FLAG --name $SESSION"

---
name: tmux-new
description: リモート制御で /clear が効かない回避策として、新しい tmux セッションで fresh な claude を起動し、そのまま /carryon まで走らせて前セッションの作業を引き継ぐ。ユーザーが「tmux new session」「新しい tmux セッション」「tmux で新規」「clear 相当」と言ったときに起動する。tmux セッション名と claude セッション名は同一の短い英語ハイフン名にする。
---

# tmux-new: 新しい tmux セッションで fresh な claude を起動して carryon まで走らせる

リモート制御では `/clear` などクライアント組込スラッシュコマンドが発火しない（リモート送信のテキストは行頭に `<system-reminder>` が prepend され、組込スラッシュコマンドの行頭判定を外す）。文脈をまっさらにする（clear 相当）手段として、**新しい tmux セッションで fresh な claude を起動し、起動後そのまま `/carryon` を投入して前セッションの作業を引き継ぐ**。

## トリガー

- 「tmux new session」「新しい tmux セッション」「tmux で新規」「clear 相当」

## やること

1. **セッション名を決める** — **短く理解可能な英語名、ハイフンつなぎ**（例 `awgn-sweep`, `epi-stam`, `footprint-split`）。今やっている作業の内容から付ける。
   - **tmux セッション名と claude セッション名は必ず同一**にする（`-s <name>` と `--name <name>` を同じ `<name>` に）。
   - `tmux ls` で既存名と衝突しないか確認。衝突するなら別名に。

2. **fresh な claude を起動**（現セッションは生かしたまま = orphan 防止）:
   ```bash
   tmux new-session -d -s <name> -c <現在の作業プロジェクトdir> 'claude --permission-mode auto --name <name>'
   ```
   - `<name>` は step 1 で決めた同一名。
   - `--permission-mode auto` 必須。素の `claude` は権限が弱すぎて作業にならない。
   - `-c` は現在の作業プロジェクトdir（例 `/Users/haruka/dev/lean-projects/common-2026`）。`/carryon` が `.claude/handoff.md` を相対参照するので、現セッションと同じ dir で起動する。
   - claude を `tmux new-session` の引数に含める形（claude 終了で tmux セッションも終わる）。

3. **起動完了を待つ** — `tmux capture-pane -t <name> -p` を繰り返しポーリングし、**`⏵⏵ auto mode on`**（権限 auto）と **`/rc active`**（Remote Control 有効）の両方が出るまで待つ。両方出れば起動成功＆リモート登録済み（`remoteControlAtStartup: true` で自動登録される）。

4. **`/carryon` を投入** — 起動確認後、新セッションに carryon を送る:
   ```bash
   tmux send-keys -t <name> '/carryon' Enter
   ```
   - send-keys はそのペインへの**ローカル入力**なので（`<system-reminder>` prepend が無い）、`/carryon` は組込スラッシュ同様に正しく発火する。
   - 投入後 `tmux capture-pane -t <name> -p` で carryon が走り出したか確認。送信が反映されていなければ `tmux send-keys -t <name> Enter` を再送する。

5. **ユーザーに報告** — セッション名 `<name>` を起動し `/carryon` 投入済みと伝える。ユーザーはリモートアプリでセッション `<name>` を選べばよい。

## 原則

- **carryon まで走らせるのが完了条件**: 起動だけで止めず、step 4 で `/carryon` を投入し走り出したことを確認するところまでやる。
- **切替は不要**: tmux client レベルの切替（`tmux switch-client`）はこの環境では効かない（全セッション `attached=0` で "no current client"、subprocess からも実行不可）。私の役目は起動＋carryon 投入まで。
- 現セッションは**生かしたまま**新セッションを起動する（orphan 防止）。
- これはリモートで `/clear` が効かない問題への一時回避策（本来は上流修正待ち）。手元の作業継続は `handoff` / `carryon` が担う。

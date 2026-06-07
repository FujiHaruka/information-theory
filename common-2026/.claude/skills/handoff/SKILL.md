---
name: handoff
description: 現在のセッションの状態を `.claude/handoff.md` に書き出し、次セッションで `/resume` から再開できるようにする。ユーザーが「セッションリセット」「次のセッション用にまとめて」「ハンドオフ書いて」「/handoff」と言ったときに起動する。今やっている作業の続きを cold な未来の自分が拾えるよう、状態 + 次の一手 + 読むべきファイル を簡潔にまとめる。
---

# handoff: セッション間の引き継ぎを書く

`.claude/handoff.md` を **上書き** で書く。次セッションで `/resume` した未来の自分が「冷えた状態でも作業を再開できる」ことが目的。

## やること

1. **状態スナップショットを集める** (並列で OK):
   - `git status` (uncommitted の有無、branch)
   - `git log --oneline -5` (直近のコミット)
   - 現在の Task list (TaskList tool で取得)
2. **active plan の hygiene チェック** (CLAUDE.md「Plan / docs hygiene」): handoff 対象 family の `*-plan.md` を `deno run -A scripts/plan_lint.ts <plan>` で検査。
   - **BUDGET** (>600 行) が出たら handoff 前に `/compact-plan <plan>` を実行 (決着済 判断ログ entry / 完了 Phase を畳む)。
   - **STALE** (壁 slug 消失 / file 消失) が出たら該当箇所を修正 or 削除。次セッションが誤った確定を引き継がないため。
   - 圧縮対象は family plan であって `.claude/handoff.md` ではない (compact-plan の不可侵制約と非競合)。cleanup をセッション境界で必ず走らせる目的 (今は user 起動依存で実行されない)。
3. **`.claude/handoff.md` を以下の形式で書く** (`Write` で上書き)
4. ユーザーには「ハンドオフ書いた」と一言だけ。長い要約は不要 (内容はファイルにある)

handoff 単体はファイルを書くだけ。「context が重くなったら自分でリセットして再開し自走を続ける」判断と実行は **resume スキル側** が持つ (resume の「自己リフレッシュ」節)。自己リフレッシュの一部として resume の自走ループから呼ばれることもある。

## handoff.md の形式

```markdown
# Handoff — <YYYY-MM-DD HH:MM>

## State

- Branch: <branch>
- Uncommitted: <"clean" or short list>
- Active phase / 作業中の文脈: <一文>

## Tasks

(TaskList の出力を pending/in_progress のみ抽出。完了済みは除く)

- #N [status] subject — description (もしあれば)

## Where we are

直近で何が終わって、何が未解決か。2〜4 文。**事実だけ**書く (推測・所感は次のセクション)。

## Next step

次セッションの最初の一手。具体的に書く:
- どのファイルを開くか
- どの sorry を埋めるか / どの bash を打つか
- 既知の戦略があれば一文で

## Files to read first

未来の自分がまず開くべきファイルを優先順で 3〜5 個。各 1 行コメント:

- `path/to/file.md` — なぜ最初に読むべきか
- ...

## Load-bearing context

ファイルからは拾えないが次セッションが知っていないとハマる事項のみ。例:

- 決定したけどまだコードに反映していない方針
- 試して却下したアプローチ (再度トライ防止)
- 今セッションで判明した Mathlib の落とし穴 / バージョン依存挙動

なければこのセクションごと省略する。
```

## 書くときの原則

- **冗長にしない**。次セッションは `.claude/handoff.md` を Read するだけ — そこに全部入っているべきだが、長すぎると逆に読まれない。全体で 50 行以内が目安
- **過去のセッションのまとめは書かない**。「今日やったこと」ではなく「次に何をするか」
- **ファイルから読める情報は重複させない**。Plan の中身を貼らない、proof の状態は file 名と行番号で参照
- **絶対パスではなくプロジェクト相対パス**で書く (移植性のため)
- ユーザーへの返答は 1〜2 行。書き出した事実 + ファイルパスだけ

## トリガー

ユーザーが以下を発話したとき必ず起動:

- 「セッションリセット」「リセットします」
- 「次のセッション用に」「ハンドオフ」
- 「引き継ぎ書いて」「まとめて終わる」
- `/handoff`

`/resume` の対になるスキル。

## 自己リフレッシュ機構 (resume スキルの自走ループが使う)

`/clear` をフック側から直接打つ手段は無いため、tmux `send-keys` で TUI を外部駆動する。中核は 2 ファイル:

- `.claude/hooks/claude-refresh.sh` — `.claude/.resume-pending` を touch し、tmux 内なら `/clear` → `/resume` を順にペインへ送る (現ターン終了後 idle に発火)。`/clear` だけでは新ターンが始まらないので turn 起動の kick として `/resume` を送る。tmux 外なら sentinel だけ立て `REFRESH_PENDING_MANUAL_CLEAR` を返す。
- `.claude/hooks/sessionstart-resume.sh` — `SessionStart(matcher=clear)` フック (`.claude/settings.json` 登録)。`.resume-pending` があるときだけ「自己リフレッシュした、自走を継続せよ」を `additionalContext` 注入し sentinel を消す。素の `/clear` は無影響。

前提: claude を tmux 内で起動していること。tmux 外では自己リフレッシュは無効 (handoff して停止しユーザーに委ねる)。判断・実行ロジックは resume スキルの「自己リフレッシュ」節を参照。

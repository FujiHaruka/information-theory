# 後続セッションで proof-log を書くときの再構成ガイド

スキル起動時のセッションが解答セッションと別の場合、会話メモリには解答中の試行錯誤が残っていない。JSONL を直接解析して再構成する。

## ログのありか

`~/.claude/projects/<encoded-cwd>/<session-id>.jsonl`

`<encoded-cwd>` は `pwd` の `/` と `.` を `-` に置換したもの。具体パスは `scripts/session_metrics.ts` の `defaultLogsDir()` を参照。

## 1. ターン構造を取る

```bash
deno run -A scripts/session_metrics.ts --turns <session-id> --file-prefix Common2026/<prefix>
```

各ターンの user prompt（先頭80文字）が見えるので、「探索」「設計」「実装」「リファクタ」のどのフェーズだったかをラベル付けできる。

## 2. Bash コマンド系列を時系列で取る

```bash
JSONL=~/.claude/projects/$(pwd | tr '/.' '-')/<session-id>.jsonl

jq -r '
  select(.type=="assistant" and .message.content)
  | .message.content[]?
  | select(.type=="tool_use" and .name=="Bash")
  | .input.command
' "$JSONL"
```

これで grep / lake / find などのコマンドが順に出る。「同じファイルに対して複数回 grep を打った」「lake env lean が連続で失敗した」などのパターンを目視で抽出する。

`lake env lean` の系列だけ見たければ:

```bash
jq -r '... | select(test("^lake env lean"))' # 上記に追加
```

## 3. ツール失敗を抽出

```bash
jq -r '
  select(.type=="user" and (.message.content | type=="array"))
  | .message.content[]?
  | select(.type=="tool_result" and .is_error==true)
  | .tool_use_id
' "$JSONL"
```

返ってきた tool_use_id を持つ tool_use の内容を引き当てれば、「何が失敗したか」がわかる。

## 4. Edit 系列を取る

```bash
jq -r '
  select(.type=="assistant" and .message.content)
  | [.timestamp, (.message.content[]?
    | select(.type=="tool_use" and (.name=="Edit" or .name=="Write"))
    | "\(.name) \(.input.file_path)")] | @tsv
' "$JSONL" | grep -v "^null"
```

「同じファイルを N 回連続で Edit している」 = そのファイルで詰まっていた可能性が高い。

## 5. ユーザー発言の流れ

```bash
jq -r '
  select(.type=="user" and (.message.content | type=="string"))
  | select(.message.content | startswith("<") | not)
  | "\(.timestamp): \(.message.content[0:200])"
' "$JSONL"
```

ユーザーが途中で介入した文（「もう少し続けて」「その方針はやめて」「テストを動かして」など）は、**会話の方向転換ポイント**を示す。

## 6. アシスタント発言（思考の流れ）

```bash
jq -r '
  select(.type=="assistant" and .message.content)
  | .message.content[]?
  | select(.type=="text")
  | .text[0:300]
' "$JSONL"
```

アシスタントの平文出力には「これからやること」「気づいたこと」「困っていること」が書かれていることが多い。詰まりや方針転換のシグナルを探す。

## 7. git で最終形を確認

```bash
git log --oneline Common2026/<prefix>*
git diff <最初のコミット>~..<最後のコミット> -- Common2026/<prefix>*
```

JSONL の Edit 系列と git diff を突き合わせると「途中で書いて消した部分」が見える（中間 Edit にあって最終 commit にないもの）。

## 8. 推奨される再構成手順

1. `--turns` でターン構造とサイズを把握 → 大まかなフェーズ分け
2. ターンごとに Bash コマンド系列を見て、grep の試行と lake の失敗を数える
3. Edit 連打のあったファイルを特定 → そこが詰まりポイント
4. 該当ターンのアシスタント平文を読んで「何で詰まったか」「何で抜けたか」を特定
5. git diff で実際にコードに残った形を確認
6. 以上を `template.md` の構造に流し込む

ただし**完全再構成は時間がかかる**。同一セッション内で書く方が低コストなので、**可能なら解答直後に書く運用が望ましい**。後続セッションでの再構成は「重要な問題だけ」「概要だけ」で割り切ってよい。

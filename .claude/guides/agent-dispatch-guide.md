# Agent dispatch guide

`lean-implementer` 等の実装系 subagent を並列 / 単独 dispatch するときの運用詳細。CLAUDE.md「Parallel orchestration」から参照される手順本体。毎セッションロードを避けるため CLAUDE.md 本体から外出ししてある — dispatch を行うときに読む。

## Standard agent prompt boilerplate

並列 dispatch する各 agent prompt に必ず含める。省略すると過去 2 つの運用 failure が起きた: (a) per-worktree 5 GB Mathlib clone で disk full、(b) agent が `feat/...` ブランチを作成し HEAD を奪う branch drift。

```
## 運用ルール (絶対遵守)

1. **worktree .lake 共有 (最初に必ず実行)**: `ln -sfn /Users/haruka/dev/lean-projects/.lake .lake` (worktree root で実行)。親の `.lake` (Mathlib 7-8 GB) を symlink reuse、5 GB Mathlib clone は disk 破綻。
2. **ブランチ規律**: 起動時にいる worktree branch に居続ける。**絶対に** `git checkout`/`git branch`/`git switch` で他ブランチへ切替・作成しない。**`feat/...` ブランチ作成は禁止**。
3. **skeleton-driven**: skeleton → 1 sorry ずつ埋める (CLAUDE.md 参照)。
4. **検証**: 完了時 `lake env lean InformationTheory/<path>/<file>.lean` が 0 errors (type-check done)。`sorry` warning は許容、ただし各 `sorry` は `@residual(<class>:<slug>)` 付き (配置 + 語彙 → `docs/audit/audit-tags.md`)。
5. **scope**: 1 file (or 既存 file 拡張)。完了時 `InformationTheory.lean` に import 1 行追加。
6. **import policy**: `import Mathlib` 禁止。pinpoint import。
7. **撤退口**: 行き詰まったら **`sorry` + `@residual(<class>:<slug>)`** で抜く。signature は本来証明したい形に保つ。**禁止**: `*Hypothesis` predicate に核を bundling する / `Prop := True` placeholder / 仮説型≡結論の `:= h` (循環) / 退化定義悪用 (CLAUDE.md「検証の誠実性」)。既存コードに defect を見つけたら即報告し、その上に積まない。
8. **commit**: 自走 commit、push なし (orchestrator が main にマージ後 push)。コミットメッセージは 1 行短く。
```

**単独 dispatch では (1)/(2)/(8) を省略可** — main 上で直接作業・自走 commit・push までして良い (CLAUDE.md「Parallel orchestration」の単独 dispatch 節)。(3)-(7) は単独でも有効。

## Cleanup after merge

全 agent 完了後: 各 agent の `.lean` を `.claude/worktrees/agent-*/...` から main にコピー、`InformationTheory.lean` に import をマージ、touch した各 file を `lake env lean` で再検証 (parent .olean reuse が worktree→main で切り替わるので個別検証必須)、最後に 1 squashed commit + push。

merge + push 完了後、worktree と branch を**必ず**削除する。残置すると locked 状態で `git worktree list` に蓄積し、次回 cleanup 時に untracked docs の判断コストが発生する (30 件以上溜まった実例あり)。

```bash
cd /Users/haruka/dev/lean-projects  # main worktree から実行
for d in .claude/worktrees/agent-*/; do
  git worktree unlock "$d" 2>/dev/null
  git worktree remove --force "$d" 2>/dev/null
done
git worktree prune
git branch | grep '^  worktree-agent-' | xargs -I {} git branch -D {}
```

`--force` は agent commit が main 回収済を前提。untracked file が残っていたら main 側と diff し、main が新しければ破棄して OK (worktree HEAD ≠ main HEAD なので status は dirty に見えるが、回収済なら本物の差分はない)。

## Brief content checklist — skeleton / body fill / refactor (parallel or single dispatch)

`lean-implementer` を skeleton 設計 (signature 含む) / body fill (sorry 埋め) / 既存 body の P→P' 等 mechanical refactor に出すときは、brief に以下の項目を含める (項目により適用 phase が違う: 項目 4 は主に signature 設計時、項目 2 は body 復元時)。planner / orchestrator 側の責務で、implementer 自身に判断させない。

1. **Sub-bound 引数表** (`P_cb` / `P_target` 分離型 predicate を扱うとき) — bundle / composite predicate の各 sub-bound が、rate-bound 引数 `R < (1/2) log(1 + ?/N)` の `?` 部に `P_cb` 側 / `P_target` 側のどちらの capacity を要求するかを 1 枚の表で列挙する (sub-bound 名 × 要求 capacity 側 × 必要 bridge 補題)。Bundle destructure 後に sub-bound 毎の capacity 引数が異なる場合があり、表が無いと LSP 第 1 戻りまで気づけない型 mismatch で 1 turn ループ。Brief 段階で predicate signature を 1 度読めば書ける情報。

2. **継承タグの語彙整合 inline check** (git history からの body 復元時) — `git show <commit>^:<path>` で旧 body を抽出 + sed 書換するワークフローでは、旧 docstring の deprecated タグ (`@audit:suspect`、`@audit:staged`、`@audit:defer`、`@audit:closed-by-successor`、散文 `🟢ʰ` 等) が literally 引き継がれる可能性がある。brief の検証 step に「貼付後 `rg -n '@audit:|@residual|🟢ʰ' <touched-file>` で deprecated タグ / 散文表現 / 既存語彙外 slug を列挙し orchestrator に報告」と 1 行追加。これらは tier 4 legacy (`docs/audit/audit-tags.md`「Deprecated」表 + 移行レシピ) — orchestrator 側で sorry-based 形式に置換 commit を別途追加 (incidental migration、新規導入は禁止)。

3. **担当 file list は実値検証してから貼る** — brief 内に「担当 file list」を書くときは、記憶 / 予測で file 名を並べず、**必ず実ファイル (split 結果 / `find` 出力等) を `cat /tmp/group-X.txt` で確認してから貼る**。抽象指定 (「`InformationTheory/Shannon/<X>.lean` 系の 27 file」) は禁止、具体 path リテラルで。代替として agent 自身に `find ... | head -N` で file list を作らせ orchestrator を間に立たせない手もある。

4. **honesty-load-bearing signature は goal でなく mechanism を渡す** (representative-dependent な量を結論に持つ lemma の実装時) — Fisher info / Radon-Nikodym 微分 / `logDeriv` など **a.e. 同値類から pointwise を取る量** (`fisherInfoOfDensityReal` 系) を signature に持つ lemma は、pin の強度 (a.e. か pointwise か) と「free 変数で受ける vs 結論に直接埋込」が **正直さそのものを決める** (a.e.-pin + free 変数は false-as-framed、skeptic が non-diff representative を取り値=0 に落とせる)。この種の signature を implementer に **「honest 化せよ」「pin せよ」という goal で投げて draft させない**。brief に (a) in-tree の honest sibling を `file:line` で、(b)「free 変数を作らず結論に直接埋込 (direct embed)」、(c)「a.e.-pin は不十分、pointwise-smooth pin (`density_t_eq` 等) のみ honest」の **3 点を mechanism として転写**する。判別軸は「その量は a.e. 等式で縛れるか、pointwise 必須か」。全 brief への mechanism front-load は delegation を殺すので、escalate するのは **honesty-load-bearing signature のときだけ** (routine body-fill は goal で良い)。

5. **共有補題の signature を変更するなら consumer graph を brief に添付** (shared lemma に仮説 threading / 引数追加・削除をするとき) — 変更前に **`scripts/dep_consumers.sh <完全修飾名>` を 1 度引き** (→ CLAUDE.md「依存 / consumer 逆引きツール」)、direct consumers (= 直接 touch が要る decl 群) の `file:line` list をそのまま brief に貼る。これが ripple 範囲の見積もり前提。`rg` で済ませると docstring/コメントの言及を真の参照と混同し、ripple を過大/過小に振る (本ツールは term レベル参照のみ数える)。複数系統から消費される補題ほど初回 brief に正確な consumer list を載せないと、threading 後に LSP 第 1 戻りまで取りこぼしに気づけない。

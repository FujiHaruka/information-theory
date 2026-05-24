# Defect / Suspect Inventory — 2026-05-24

Snapshot of all `@audit:KIND(SLUG)` tags under `Common2026/` as of commit `8e3645f`.
SoT = code 内 inline タグ (CLAUDE.md「検証の誠実性」/ `docs/audit/audit-tags.md` 準拠)。
本ファイルは並列 wave を組む前の地図づくり用 snapshot であり、SoT を上書きしない (タグ自体を編集する作業は別 commit)。

## Summary

| KIND | 件数 | unique SLUG |
|---|---|---|
| `defect` | 5 | 2 (`circular`, `false-statement`) |
| `staged` | 15 | 7 predicate slug (重複含む) |
| `suspect` | 382 | 42 plan slug (うち 3 件は plan ファイル不在) |
| **合計** | **402** | — |

- 直近 actionable (defect + staged): **20 タグ / 9 unique predicate locus** — closure 可否判定対象。
- long-term residual (suspect): **382 タグ / 42 plan SoT に分散** — plan 側で管理。本 inventory では plan 別件数のみ。
- orphan suspect (plan ファイル不在): **3 slug** — plan を作るか、別 plan に振り直すか要判定。

## §1. Defect (5 件)

すべて circular か false-statement。3 ファイルに集中。

| # | file:line | KIND | 補助タグ | 当該宣言 | consumer (files / refs) | 解消ルート |
|---|---|---|---|---|---|---|
| 1 | `Common2026/Shannon/BrunnMinkowski.lean:133` | `defect(circular)` | `defer(brunn-minkowski-from-epi-discharge)` + `staged(epi-n-dim)` | `def IsBrunnMinkowskiEntropyHypothesis` (line 134) | 4 files / 20 refs | **Mathlib-gap** (EPI n-dim 経由、`docs/shannon/brunn-minkowski-from-epi-discharge-plan.md`) — long-term staged |
| 2 | `Common2026/Shannon/BrunnMinkowski.lean:191` | `defect(circular)` | `defer(brunn-minkowski-from-epi-discharge)` | `theorem brunn_minkowski_entropy_inequality` (line 192) | 同上 predicate を hyp 取り | **Mathlib-gap** (#1 と同 plan、predicate 経由で間接) |
| 3 | `Common2026/Shannon/AWGNAchievability.lean:46` | `defect(circular)` | `defer(awgn-achievability-typicality)` + `staged(n-dim-gaussian-aep)` | `def IsAwgnTypicalityHypothesis` (line 47) | 9 files / 28 refs | **Mathlib-gap** (n-dim Gaussian AEP / continuous SMB、`docs/shannon/awgn-moonshot-plan.md` Phase B-0) |
| 4 | `Common2026/Shannon/AWGNAchievability.lean:85` | `defect(circular)` | `defer(awgn-achievability-typicality)` | `theorem awgn_achievability` (line 86) | 上記 predicate consumer | **Mathlib-gap** (#3 と同 root) |
| 5 | `Common2026/Shannon/AWGNAchievabilityDischarge.lean:730` | `defect(false-statement)` | `audit-history: prior staged(awgn-power-constraint-realizable)` | `def IsAwgnPowerConstraintRealizable` (line 731) | 1 file / 2 refs (history only) | **honesty-record (温存)** — AWGN pivot plan 判断ログ #7 (`docs/shannon/awgn-power-constraint-realizable-pivot-plan.md:230`) で「**削除せず orphan 化 / tag・body 完全不変で残置 (honesty record)**」と明示決定済。alias 化を試みたが honest predicate に degenerate instance を作ると依然 unsatisfiable で audit-tags rule に抵触するため放棄、現状の温存が正解。 |

**観察**: defect 5 件中 4 件 (#1–#4) は Mathlib 壁経由の long-term。**#5 は意図的温存** (honesty record、削除不可)。本 inventory 初版で「rewrite-only 削除可」と誤分類していたが、pivot plan judgment を確認の上 2026-05-24 訂正。

## §2. Staged predicate (7 unique / 15 タグ)

| predicate slug | def 位置 | hyp 引き受け箇所 | consumer (files / refs) | Mathlib 壁 種別 | plan SoT |
|---|---|---|---|---|---|
| `epi-n-dim` | `BrunnMinkowski.lean:134` (`IsBrunnMinkowskiEntropyHypothesis`) | 同上 def + line 192 + line 215 + 三項 line 299–300 | 4 files / 20 refs | (b) 解析 (EPI n-dim) | `docs/shannon/brunn-minkowski-from-epi-discharge-plan.md` |
| `n-dim-gaussian-aep` | `AWGNAchievability.lean:47` (`IsAwgnTypicalityHypothesis`) | 同上 def + 9 file consumer | 9 files / 28 refs | (b) 解析 (continuous SMB / n-dim AEP) | `docs/shannon/awgn-moonshot-plan.md` Phase B-0 |
| `continuous-aep-gaussian` | `AWGNAchievabilityDischarge.lean:140` (`IsContinuousAEPGaussian`) | `awgn_avg_error_union_bound` (line 585) | 1 file / 8 refs | (b) 解析 (continuous SMB Gaussian 化) | `docs/shannon/awgn-moonshot-plan.md` Phase B-0 |
| `awgn-random-coding-bound` | `AWGNAchievabilityDischarge.lean:543` (`IsAwgnRandomCodingBound`) | `awgn_avg_error_union_bound` (line 586) | 1 file / 6 refs | (b) 解析 (Gaussian random coding 解析) | `docs/shannon/awgn-moonshot-plan.md` (Phase C-3) |
| `awgn-power-constraint-honest` | `AWGNAchievabilityDischarge.lean:784` (`IsAwgnPowerConstraintHonest`) | line 868 (bundle 内) + 949, 1147 (consumer body) | 1 file / 7 refs | (b) 解析 (LLN 集中) — bundle 経由 | `docs/shannon/awgn-power-constraint-realizable-pivot-plan.md` (pivot 完了済) |
| `awgn-random-coding-feasible` | `AWGNAchievabilityDischarge.lean:861` (`IsAwgnRandomCodingFeasible`) | line 964 (`isAwgnTypicalityHypothesis` discharger), line 1590, 1621 (`awgn_achievability_F1_via_staged_hyps`) | 1 file / 10 refs | (b) 解析 (3 staged hyp の bundle) | `docs/shannon/awgn-moonshot-plan.md` Phase D (bundle 縮約) |
| `awgn-power-constraint-realizable` | `AWGNAchievabilityDischarge.lean:731` (= defect #5) | history mention only | 0 active (history のみ) | — | **削除候補** (§1 #5 と同) |

**観察**:
- AWGNAchievabilityDischarge.lean に **6 / 7 unique** が集中。**1 file = 1 wave** で並列化困難 (同 file 内は直列、merge conflict 必至)。
- すべて Mathlib 壁分類 (b) 解析。**closure ルートは「Mathlib 進化を待つ」「自分で書く」の 2 択**。short-term closure 対象は §1 #5 (rewrite-only) のみ。

## §3. Suspect — plan 別集計 (42 SLUG, 382 タグ)

降順。「✗」は plan ファイル不在 (= orphan suspect、要対応)。

| 件数 | plan SLUG | plan ファイル |
|---|---|---|
| 76 | `epi-moonshot-plan` | `docs/shannon/epi-moonshot-plan.md` |
| 33 | `relay-inner-bound-moonshot-plan` | `docs/shannon/relay-inner-bound-moonshot-plan.md` |
| 30 | `brunn-minkowski-closure-plan` | `docs/shannon/brunn-minkowski-closure-plan.md` |
| 19 | `huffman-t1apprime-partial-moonshot-plan` | `docs/shannon/huffman-t1apprime-partial-moonshot-plan.md` |
| 17 | `mac-moonshot-plan` | `docs/shannon/mac-moonshot-plan.md` |
| 17 | `hoeffding-tradeoff-moonshot-plan` | `docs/shannon/hoeffding-tradeoff-moonshot-plan.md` |
| 16 | `lz78-moonshot-plan` | `docs/shannon/lz78-moonshot-plan.md` |
| 15 | `chernoff-converse-sanov-discharge-plan` | `docs/shannon/chernoff-converse-sanov-discharge-plan.md` |
| 13 | `wyner-ziv-discharge-moonshot-plan` | `docs/shannon/wyner-ziv-discharge-moonshot-plan.md` |
| 11 | `parallel-gaussian-moonshot-plan` | `docs/shannon/parallel-gaussian-moonshot-plan.md` |
| 11 | `broadcast-channel-moonshot-plan` | `docs/shannon/broadcast-channel-moonshot-plan.md` |
| 11 | `awgn-moonshot-plan` | `docs/shannon/awgn-moonshot-plan.md` |
| 9 | `huffman-moonshot-plan` | `docs/shannon/huffman-moonshot-plan.md` |
| 9 | `awgn-mi-decomp-plan` | `docs/shannon/awgn-mi-decomp-plan.md` |
| 8 | `lz78-ziv-inequality-discharge-moonshot-plan` | `docs/shannon/lz78-ziv-inequality-discharge-moonshot-plan.md` |
| 8 | `cramer-moonshot-plan` | `docs/shannon/cramer-moonshot-plan.md` |
| 6 | `wyner-ziv-moonshot-plan` | `docs/shannon/wyner-ziv-moonshot-plan.md` |
| 6 | `differential-entropy-plan` | `docs/shannon/differential-entropy-plan.md` |
| 5 | `wyner-ziv-convexity-discharge-moonshot-plan` | `docs/shannon/wyner-ziv-convexity-discharge-moonshot-plan.md` |
| 5 | `lz78-residual-discharge-plan` | `docs/shannon/lz78-residual-discharge-plan.md` |
| 5 | `fisher-info-moonshot-plan` | `docs/shannon/fisher-info-moonshot-plan.md` |
| 4 | `shannon-moonshot-plan` | `docs/shannon/shannon-moonshot-plan.md` |
| 4 | `cramer-lc2-discharge-moonshot-plan` | `docs/shannon/cramer-lc2-discharge-moonshot-plan.md` |
| 4 | `chernoff-converse-moonshot-plan` | `docs/shannon/chernoff-converse-moonshot-plan.md` |
| 4 | `awgn-f1-discharge-moonshot-plan` | `docs/shannon/awgn-f1-discharge-moonshot-plan.md` |
| 3 | `relay-cutset-moonshot-plan` | `docs/shannon/relay-cutset-moonshot-plan.md` |
| 3 | `dmc-feedback-capacity-plan` | `docs/shannon/dmc-feedback-capacity-plan.md` |
| 3 | `channel-coding-shannon-theorem-full-plan` | `docs/shannon/channel-coding-shannon-theorem-full-plan.md` |
| 3 | `brunn-minkowski-moonshot-plan` | `docs/shannon/brunn-minkowski-moonshot-plan.md` |
| 2 | `whittaker-shannon-partial-moonshot-plan` | `docs/shannon/whittaker-shannon-partial-moonshot-plan.md` |
| 2 | `huffman-optimality-moonshot-plan` | `docs/shannon/huffman-optimality-moonshot-plan.md` |
| 2 | `hoeffding-tradeoff-sandwich-plan` | `docs/shannon/hoeffding-tradeoff-sandwich-plan.md` |
| 1 | `separation-theorem-moonshot-plan` | `docs/shannon/separation-theorem-moonshot-plan.md` |
| 1 | `mac-l1-discharge-moonshot-plan` | `docs/shannon/mac-l1-discharge-moonshot-plan.md` |
| 1 | `infinitepi-tilted-rn-discharge-moonshot-plan` | `docs/shannon/infinitepi-tilted-rn-discharge-moonshot-plan.md` |
| 1 | `fisher-info-gaussian-discharge-moonshot-plan` | `docs/shannon/fisher-info-gaussian-discharge-moonshot-plan.md` |
| 1 | `epi-convolution-density-plan` | `docs/shannon/epi-convolution-density-plan.md` |
| 1 | `cramer-chernoff-clt-closure-moonshot-plan` | `docs/shannon/cramer-chernoff-clt-closure-moonshot-plan.md` |
| 1 | `chernoff-moonshot-plan` | `docs/shannon/chernoff-moonshot-plan.md` |
| 1 | `birkhoff-ergodic-plan` | ✗ **PLAN MISSING** |
| 1 | `awgn-mi-bridge-plan` | ✗ **PLAN MISSING** |
| 1 | `awgn-converse-aux-plan` | ✗ **PLAN MISSING** |
| 1 | `prekopa-leindler-induction-plan` | ✗ **PLAN MISSING** |

### Orphan suspect (3 件 — plan ファイル不在)

| SLUG | 検出箇所 | 対応案 |
|---|---|---|
| `awgn-converse-aux-plan` | `Common2026/Shannon/AWGNConverse.lean:91` | 新規 plan stub (docstring で「Tier 3 未着手」と明示済、slug は確保意図) |
| `awgn-mi-bridge-plan` | `Common2026/Shannon/AWGN.lean:122` | 新規 plan stub (docstring に「`awgn-mi-bridge-plan.md`」と直接言及済) |
| `prekopa-leindler-induction-plan` | `Common2026/Shannon/BrunnMinkowskiFunctional.lean:209` | 新規 plan stub (docstring に「`prekopa-leindler-induction-plan.md` (未着手) で `n` 帰納 + 1-dim Hölder 経路」と明示済) |

**観察**: orphan 3 件すべてが docstring 内で「将来 plan を書く予定で slug を確保」と明示している。**stub 作成が正規対応** (slug 振り直しは著者意図に反する)。各 stub は 30 行前後の minimal scaffold (motivation + scope + TODO) で、後の `lean-planner` agent が本体起草する SoT を確保。並列 wave の cleanup ジョブとして 1 セッション内で吸収可。

**注記**: 本 inventory 初版で 4 件と書いたが、`birkhoff-ergodic-plan` は既存 (`docs/shannon/birkhoff-ergodic-plan.md`、5/20 作成、198 行)。誤読を 2026-05-24 訂正。

## §4. ファイル別 hotspot (top 20)

並列実装の干渉エリア。同 file 内変更は直列必須。

| tag数 | file |
|---|---|
| 20 | `Common2026/Shannon/AWGNAchievabilityDischarge.lean` |
| 15 | `Common2026/Shannon/RelayInnerBodyDischarge.lean` |
| 15 | `Common2026/Shannon/HuffmanT1APPrimeBody.lean` |
| 15 | `Common2026/Shannon/EPIStamDischarge.lean` |
| 14 | `Common2026/Shannon/EPIStamToBridge.lean` |
| 14 | `Common2026/Shannon/EPIL3Integration.lean` |
| 11 | `Common2026/Shannon/BrunnMinkowskiFunctional.lean` |
| 11 | `Common2026/Shannon/BrunnMinkowskiConcavity.lean` |
| 9 | `Common2026/Shannon/RelayInnerBound.lean` |
| 9 | `Common2026/Shannon/EPIStamStep3Body.lean` |
| 8 | `Common2026/Shannon/MultipleAccessChannel.lean` |
| 7 | `Common2026/Shannon/ChernoffPerTiltSanov.lean` |
| 6 | `Common2026/Shannon/WynerZivConverseChain.lean` |
| 6 | `Common2026/Shannon/HoeffdingInteriorGradientBody.lean` |
| 6 | `Common2026/Shannon/EPIStamDeBruijnConclusion.lean` |
| 6 | `Common2026/Shannon/BroadcastChannel.lean` |
| 5 | `Common2026/Shannon/RelayCFBinningBody.lean` |
| 5 | `Common2026/Shannon/ParallelGaussianPerCoord.lean` |
| 5 | `Common2026/Shannon/LZ78ZivCombinatorics.lean` |
| 5 | `Common2026/Shannon/LZ78FinalGlue.lean` |

**観察**: AWGN / EPI / BrunnMinkowski / Huffman / Relay の 5 大エリアで全 audit tag の **約 70%** を占める。並列 wave はこの 5 エリア単位で切るのが自然。

## §5. 解消ルート分類 (3 軸)

| ルート | 件数 (推定) | 該当 |
|---|---|---|
| **rewrite-only** (orphan slug への plan stub 作成) | 3 | orphan suspect 3 件への plan stub (本 session Wave 0 で実施済、§7 参照) |
| **pivot** (AWGN 型 = predicate 書換 + consumer signature swap + body P→P' threading) | 0 候補 (新規) | 既知の AWGN pivot は完了済。**現時点で同型 pivot 候補なし** (defect はすべて Mathlib-gap)。新規 false-statement defect が再度生えたら再評価 |
| **honesty-record (温存)** | 1 | §1 #5 (`IsAwgnPowerConstraintRealizable` 残骸 — 削除不可) |
| **Mathlib-gap** (long-term residual, plan 経由) | ~390 | §1 #1–#4 (4 件); §2 staged 6 unique (6 タグ); §3 suspect 382 件すべて |

**観察**: **short-term actionable は rewrite-only 3 件のみ** (本 session で完了)。残りは Mathlib 進化 / 自前 Mathlib 化を待つ long-term saga。並列化の leverage は (a) ~~rewrite-only cleanup~~ (完了) + (b) Mathlib-gap plan 群の advancement N wave に集約される。

## §6. 並列 wave 計画 draft (最大 5 並列)

ユーザー指定: 並列上限 5。3 wave 構成案。

### Wave 0 (single, 短時間) — rewrite-only cleanup ✅ 完了 (2026-05-24)

- **当初対象**: §5 rewrite-only 8 件 → **実際は 3 件** (再判定で削減)
- **完了内容**:
  - §1 #5 `IsAwgnPowerConstraintRealizable` 残骸 def 削除 → **非該当**。pivot plan 判断ログ #7 で「honesty record として削除せず温存」と明示決定済、§1 #5 / §5 を訂正。
  - orphan suspect plan stub 作成 → **3 件**完了 (本 session):
    - `docs/shannon/awgn-converse-aux-plan.md` (新規 stub)
    - `docs/shannon/awgn-mi-bridge-plan.md` (新規 stub)
    - `docs/shannon/prekopa-leindler-induction-plan.md` (新規 stub)
    - (`birkhoff-ergodic-plan` は inventory 集計時の誤読、既存 198 行 plan あり)
  - `docs/audit/audit-tags.md` 整合確認 → **差分なし**、cleanup 不要。
- **担当**: orchestrator (= 私) 直、worktree 不要、1 commit。

### Wave 1 (parallel ×5) — plan 側 SoT 整合 + 進捗確認 inventory

5 大エリア × `mathlib-inventory` agent で並列実行。各 agent の責務:

- 担当エリアの全 suspect (file:line) を実コードで grep
- 対応 plan ファイル (`docs/<family>/<slug>.md`) の「残タスク」「未着手 phase」と suspect tag が一致しているか照合
- 不整合 (plan に書かれてないが suspect が残ってる / 逆) を `docs/audit/wave1-plan-sync-<area>.md` に書き出す

分担:

| Agent | エリア | 対象 plan slug | 推定 suspect 数 |
|---|---|---|---|
| W1-A | **AWGN 系** | `awgn-moonshot`, `awgn-mi-decomp`, `awgn-f1-discharge`, `awgn-converse-aux`, `awgn-mi-bridge` (orphan) | ~26 |
| W1-B | **EPI / BrunnMinkowski / differential-entropy 系** | `epi-moonshot`, `brunn-minkowski-closure`, `brunn-minkowski-moonshot`, `differential-entropy`, `epi-convolution-density`, `fisher-info`, `fisher-info-gaussian-discharge`, `prekopa-leindler` (orphan) | ~123 |
| W1-C | **Channel coding 系 (Relay/MAC/Broadcast/DMC)** | `relay-inner-bound`, `relay-cutset`, `mac`, `mac-l1-discharge`, `broadcast-channel`, `dmc-feedback-capacity`, `channel-coding-shannon-theorem-full` | ~68 |
| W1-D | **Source coding 系 (LZ78/Huffman)** | `lz78`, `lz78-ziv-inequality-discharge`, `lz78-residual-discharge`, `huffman`, `huffman-optimality`, `huffman-t1apprime-partial` | ~59 |
| W1-E | **Tail/concentration 系 (Chernoff/Hoeffding/Cramer/WynerZiv/Parallel Gaussian/Shannon/その他)** | `chernoff-converse-sanov-discharge`, `chernoff-converse`, `chernoff`, `cramer`, `cramer-lc2-discharge`, `cramer-chernoff-clt-closure`, `hoeffding-tradeoff`, `hoeffding-tradeoff-sandwich`, `wyner-ziv`, `wyner-ziv-discharge`, `wyner-ziv-convexity-discharge`, `parallel-gaussian`, `shannon`, `whittaker-shannon-partial`, `separation-theorem`, `infinitepi-tilted-rn-discharge`, `birkhoff-ergodic` (orphan) | ~105 |

**期待成果物**: 5 ファイルの `docs/audit/wave1-plan-sync-<area>.md`。後続 wave で「どの plan の suspect が close 可能か」を判定する地図。

### Wave 2 (planning, 直列または ≤2 並列) — Mathlib-gap closure plan の優先度付け

Wave 1 の sync 結果を読み、最大 leverage の plan を 2-3 件選定:

- candidate 1: `epi-moonshot-plan` (76 件 — 最大) → 進めると BrunnMinkowski 側 30 件も連鎖クローズ可
- candidate 2: `awgn-moonshot-plan` Phase B-0 (`continuous-aep-gaussian` + `n-dim-gaussian-aep`) → AWGNAchievability 系全 staged が closure

`lean-planner` agent で Phase 設計、その後 Wave 3 (実装並列) に進む。

### Wave 3 以降 (parallel ×5) — Mathlib-gap implementation

Wave 2 で確定した phase を、file 独立性に基づき最大 5 並列で `lean-implementer` 投入。
Brief には CLAUDE.md「Brief content checklist」必須項目 (sub-bound 引数表 + 継承 audit タグ inline check) を含める。

## §7. Wave 1 結果統合 (5 並列 plan sync 完了, 2026-05-24)

5 大エリアを general-purpose agent 5 並列で audit。各 report は `docs/audit/wave1-plan-sync-<area>.md` に存置。本節は cross-area サマリ。

### 7.1 件数集約

| Wave | エリア | 実測 suspect | in-plan orphan | drop 漏れ | ROI high | ROI medium | ROI low | report |
|---|---|---|---|---|---|---|---|---|
| W1-A | AWGN | 26 | 5 | 0 | 0 | 11 | 15 | [`wave1-plan-sync-awgn.md`](./wave1-plan-sync-awgn.md) |
| W1-B | EPI / BrunnMinkowski / diff-entropy | 123 | 96 | 0 | 22 | 35 | 66 | [`wave1-plan-sync-epi-bm.md`](./wave1-plan-sync-epi-bm.md) |
| W1-C | Channel coding (Relay/MAC/BC/DMC) | 71 | 5 | 0 | 8 | 17 | 46 | [`wave1-plan-sync-channel-coding.md`](./wave1-plan-sync-channel-coding.md) |
| W1-D | Source coding (LZ78/Huffman) | 59 | 0 | 51 | 9 | 6 | 44 | [`wave1-plan-sync-source-coding.md`](./wave1-plan-sync-source-coding.md) |
| W1-E | Tail/concentration | 96 | 0 | 2 | 1 | 4 | 91 | [`wave1-plan-sync-tail-concentration.md`](./wave1-plan-sync-tail-concentration.md) |
| **合計** | **5** | **375** | **106** | **53** | **40** | **73** | **262** | — |

(snapshot §1 の生 grep 382 件との差は、生 grep が同一 declaration 上の複数 tag を別カウントするのに対し、agent は declaration 単位で集約しているため。)

### 7.2 横断 themes (5 area で観測された共通パターン)

1. **plan-side stale が常態化** (W1-A `awgn-mi-decomp` / W1-D Huffman・LZ78 / W1-E DONE 表記 + suspect 残置): code 実装が plan を追い越し、plan 進捗欄が初版のまま。audit visibility は code SoT を信じれば失われないが、レビュー時に「何が新規 wave で増えたか」追跡不能。
2. **rewrite-only second wave が大規模に発見**: 即 retract 候補 (DONE 表記済 suspect 残置, completed wrapper 上の suspect 遺存) + re-tag 候補 (slug mismatch, SUPERSEDED 化) で計 **80-120 件相当**。Wave 0 で潰した orphan stub 3 件とは別系。
3. **honesty inline alert 2 件** (W1-D LZ78 系、CLAUDE.md「専用監査を待たない」inline 即フラグ規律該当):
   - `Common2026/Shannon/LZ78ZivTreeNode.lean:651, :712` — predicate `IsLZ78ZivCombinatorialCoreOverhead` が docstring 内で **「FALSE で vacuously conditioned」**と self-flag 済。現状 `@audit:suspect` だが、規約上は `@audit:defect(degenerate)` or `@audit:residual` 格上げ候補。
   - `Common2026/Shannon/LZ78SMBSandwich.lean:362` `IsLZ78ConverseChainHyp.ofSMBBridge` — body `:= h` の defeq 別名 (circular)、`lz78-residual-discharge-plan` 判断ログ #6 で defect として記録済だが **本 line には audit tag 未付与**。`@audit:defect(circular)` 付与必要。
4. **連鎖クローズ最大 leverage 3 経路** (Wave 3 候補):
   - **Chernoff family** (W1-E `chernoff-converse-sanov-discharge-plan` Phase 5): 単一 discharge で 21 件一斉 close (Chernoff family 全 21 件)。Mathlib gap ~150-300 行、既存 `Stein.lean` + `SanovLDPEquality.lean` plumbing 再利用。
   - **BM 縦串** (W1-B `multivariate-diffentropy-subadditivity` → `brunn-minkowski-closure` Phase 4 → BM 33): 単一上流 close で 37 件連鎖閉。Mathlib 壁 (b) 中、半年内現実的。
   - **Relay** (W1-C `relay-inner-bound-moonshot` L-RI1 + L-RI3): 2 body discharge で 24 件 (Relay-inner-bound 33 件中 24 件) transitive close。
5. **slug 粒度問題** (W1-B `epi-moonshot-plan` 76 件 / W1-D Huffman 3-plan で 2-3 hyp に集約可能 / W1-D LZ78-moonshot SUPERSEDED 化): 1 slug あたり 30+ 件は audit 単位として過大、後継 sub-plan slug への分割 / merge / 再分配で visibility が大幅改善。

### 7.3 Wave 1.5 (rewrite-only 拡張 cleanup) 候補リスト

5 area report を統合した「single-commit で消化可能な audit visibility 改善 item」:

| # | エリア | item | 対象件数 | 形式 | 状態 |
|---|---|---|---|---|---|
| 1 | W1-D inline | LZ78 honesty tag 付与 (`LZ78ZivTreeNode.lean:652,713` → `defect(degenerate)`、`LZ78SMBSandwich.lean:297` → `defect(launder)`) | 3 | docstring Edit | ✅ 完了 (本 session、`defect` 5→8) |
| 2 | W1-A | `awgn-f1-discharge-moonshot-plan` 4 件 retag (F-1 genuine 済の wrapper 遺存 tag) | 4 | tag Edit |
| 3 | W1-C | `dmc-feedback-capacity-plan` 3 件 retract (`_memoryless` 完全形 publish 済) | 3 | tag drop |
| 4 | W1-C | `channel-coding-shannon-theorem-full-plan` 1 件 retract-candidate 化 | 1 | tag Edit |
| 5 | W1-E | DONE 表記済 plan の suspect 残置 re-tag (audit-tags 語彙 `staged` / `completed` 拡張要検討) | ~25 | tag Edit + audit-tags.md 拡張 |
| 6 | W1-D | Huffman 3-plan merge → `huffman-2hyp-vertical-reduction-plan` 新規 + 30 件再分配 | 30 | plan stub + tag mass-edit |
| 7 | W1-D | LZ78-moonshot SUPERSEDED 化 + 16 件再分配 (residual-discharge / blockrv-refactor / achievability-converse) | 16 | plan status + tag mass-edit |
| 8 | W1-B | epi-moonshot 76 件 slug 分割 (`epi-stam-discharge` / `epi-debruijn-integration` / `epi-stam-to-conclusion`) | 76 | plan split + tag mass-edit |
| 9 | W1-A / W1-D | plan 進捗欄追記 (awgn-moonshot Phase Pivot / awgn-mi-decomp 段 1+2 / Huffman code follow-up) | 数 plan | plan Edit |

**合計**: 120-160 件相当の visibility 改善 (重複あり)。**inline 2 件 (item #1) は CLAUDE.md「専用監査を待たない」inline 即フラグ規律該当**、最優先で潰すべき。残りは並列実行可。

### 7.4 Wave 2 (planning) 候補 — Mathlib-gap closure plan の優先度

Wave 1 結果に基づき、leverage 順:

1. **`chernoff-converse-sanov-discharge-plan` Phase 5** (W1-E、ROI medium、21 件一斉 close) — 最も投資対効果が高い。`lean-planner` で Phase 5 詳細設計 → `lean-implementer` 並列実装。
2. **`brunn-minkowski-closure-plan` Phase 4 + `multivariate-diffentropy-subadditivity` 新規** (W1-B、ROI medium、37 件縦串) — 計画整理が必要。
3. **`parallel-gaussian-moonshot-plan` Phase C** (W1-E、ROI medium、11 件 + AWGN family 連鎖) — AWGN B-0 と独立に進められる第二経路。
4. **`epi-moonshot-plan` slug 分割後の Phase 起草** (W1-B、76 件、Wave 1.5 item #8 完了後): 分割後 sub-plan それぞれの Phase 設計。

## §8. 次の一手

ユーザー判断待ち:

1. **Wave 1.5 (rewrite-only 拡張)** を 5 並列で起動するか — §7.3 item の独立性で並列分担可能 (例: inline alert + retag は 1 agent, plan split は別 agent, ...)。inline alert 2 件のみ即潰してから残りを並列、もあり。
2. **Wave 2 (planning) を Wave 1.5 と並列で起動するか** — Chernoff Phase 5 設計を `lean-planner` に独立投入可。Wave 1.5 と非干渉。
3. **次セッションに送る** (handoff) — 本 session で Wave 0 / Wave 1 が完了したので一区切り。

推奨: **inline alert 2 件 (item #1) のみ本 session で即潰す → 残りは handoff** (CLAUDE.md「専用監査を待たない」inline 規律遵守 + session 規模が膨らみすぎないよう sane stopping point)。

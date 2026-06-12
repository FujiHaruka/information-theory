# Shannon EPI: case-1 sum-noise N(0,2) 構造改変 successor サブ計画

**Status**: CLOSED ✅ — general-variance de Bruijn structure surgery で sum frontier を閉じる試み。全 single-t route が variance-2 非対称 (sum 項の factor-2) で REFUTE され、後継の two-time restructure (`epi-case1-twotime-restructure-plan`) が sum EPI を genuine closure。本 line の structure surgery は不要化。
**SoT**: `docs/shannon/ch17-inequalities-status.md` + `docs/shannon/epi-facts.md` + `docs/textbook-roadmap.md` Ch.17。詳細履歴は git。

> **Parent**: [`epi-case1-debruijn-producer-plan.md`](epi-case1-debruijn-producer-plan.md) §PB-4 / L-Sum-struct
> **Predecessor**: [`epi-case1-sum-producer-plan.md`](epi-case1-sum-producer-plan.md)

## 要点 (再利用可能な判断軸)
- **variance-2 は coupling に intrinsic**: sum noise は `Z_X+Z_Y` (variance 2) でなければ `(X+Y)+√t·(Z_X+Z_Y) = X_t+Y_t` coupling が壊れる。unit-noise W への置換 (B-τ/c route) は sum 項を別時刻に追いやって desync を生み、単一共有-t の consumer object に乗らない。
- **single-t object の根本限界**: 単一共有-t の gap object は variance-2 非対称を吸収できず、harmonic Stam + positivity だけでは閉じない (欠ける ingredient は `J_i` と `N_i·J_i` の non-local co-monotonicity で、Stam/isoperimetric から出ない)。解消には X/Y を別時刻で摂動する two-time reparametrization が必要 — これが後継 plan の起点。
- **stale docstring が advisor 誤読を誘導した教訓**: case-A の「ratio core 無改変再利用」誤判定は、measure-keyed wrapper と density-direct Fisher 関数を取り違えた stale docstring が元。楽観 verdict も必ず最小 probe で機械検証する原則が効いた。

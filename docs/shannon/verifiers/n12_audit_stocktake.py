#!/usr/bin/env python3
"""N12 独立検証器 — 棚卸し (docs/shannon/bc-t3c-n12-stocktake.md) を破りに行く側の実装。

⚠ 既定の立場は「棚卸しの主張は偽である」。各テストは棚卸しの数値/主張を **HEAD の実体から
独立に再導出**し、食い違いがあればそれを FAIL ではなく「棚卸し側の訂正」として印字する
(本検証器の PASS/FAIL は *実体側の再導出が成功したか* を測る)。

⚠ 独立性: 既存 11 本の検証器を import しない。T20 / T21 だけは「pass 本数が再現するか」
「所要時間が台帳と合うか」という軸そのものが監査対象なので subprocess で実行する
(実行はつねに **直列**。並行させると T21 の測定が壊れる)。

    python3 docs/shannon/verifiers/n12_audit_stocktake.py             # 全テスト (約 8 分)
    python3 docs/shannon/verifiers/n12_audit_stocktake.py --skip-slow # T20 / T21 を飛ばす

終了コード 0 = 全 PASS。
"""

from __future__ import annotations

import re
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
BC = ROOT / "InformationTheory" / "Shannon" / "BroadcastChannel"
FACTS = ROOT / "docs" / "shannon" / "bc-facts.md"
STOCK = ROOT / "docs" / "shannon" / "bc-t3c-n12-stocktake.md"
PLAN = ROOT / "docs" / "shannon" / "bc-open-problem-t3c-plan.md"
VERIF = ROOT / "docs" / "shannon" / "verifiers"

RESULTS: list[tuple[str, bool, str]] = []
NOTES: list[str] = []


def check(name: str, ok: bool, detail: str) -> None:
    RESULTS.append((name, bool(ok), detail))
    print(f"[{'PASS' if ok else 'FAIL'}] {name} — {detail}")


def note(text: str) -> None:
    NOTES.append(text)
    print(f"  ⚠ NOTE {text}")


def git(*args: str) -> str:
    return subprocess.run(
        ["git", *args], cwd=ROOT, capture_output=True, text=True, check=True
    ).stdout


def read(path: Path) -> str:
    return path.read_text(encoding="utf-8")


# ---------------------------------------------------------------------------
# A. 窓と commit 帰属 (棚卸し §1-2 / §3.1)
# ---------------------------------------------------------------------------

WINDOW_BASE = "20b456b9"
WINDOW_EXPECTED = ["51d1ccb1", "72aaef9a", "d9fa6558", "4da3a9ad", "db25d3dd"]
ENTRY_ADDED_EXPECTED = {"51d1ccb1": 3, "72aaef9a": 0, "d9fa6558": 0, "4da3a9ad": 2, "db25d3dd": 0}


def t01_window_base() -> None:
    """窓の始点そのものが InformationTheory/ を触っていないこと (触っていれば数え落ちになる)."""
    files = git("show", "--stat", "--name-only", "--format=", WINDOW_BASE).split()
    hits = [f for f in files if f.startswith("InformationTheory/")]
    check(
        "T01 window base touches no InformationTheory/",
        not hits,
        f"{WINDOW_BASE} の変更ファイルに InformationTheory/ は {len(hits)} 件 "
        f"⟹ 窓 {WINDOW_BASE}..HEAD で数え落ちは生じない",
    )


def t02_window_commits() -> None:
    got = [l.split()[0] for l in git(
        "log", "--oneline", f"{WINDOW_BASE}..HEAD", "--", "InformationTheory/"
    ).strip().splitlines()]
    check(
        "T02 window commits touching InformationTheory/",
        sorted(got) == sorted(WINDOW_EXPECTED),
        f"{len(got)} 本 = {got} (期待 {WINDOW_EXPECTED})",
    )


def _entry_added(commit: str) -> tuple[int, int]:
    """(行頭アンカー版, 緩い版) の追加 @[entry_point] 行数。両者が一致しなければ
    棚卸しの `rg -c '^\\+@\\[entry_point\\]'` に数え落ちがある。"""
    diff = git("show", commit, "--", "InformationTheory/")
    anchored = len([l for l in diff.splitlines() if l.startswith("+@[entry_point]")])
    loose = len([l for l in diff.splitlines() if l.startswith("+") and "@[entry_point]" in l])
    return anchored, loose


def t03_t05_attribution() -> None:
    for commit, expected in ENTRY_ADDED_EXPECTED.items():
        anchored, loose = _entry_added(commit)
        ok = anchored == expected and loose == expected
        check(
            f"T03/{commit} added @[entry_point]",
            ok,
            f"anchored={anchored} / loose={loose} (期待 {expected})"
            + ("" if anchored == loose else "  ⚠ アンカー版と緩い版が食い違う = 数え落ち"),
        )
    total = sum(_entry_added(c)[1] for c in ENTRY_ADDED_EXPECTED)
    check("T04 window total added @[entry_point] == 5", total == 5, f"合計 {total} 本")


def t06_no_removal() -> None:
    removed = 0
    for commit in WINDOW_EXPECTED:
        diff = git("show", commit, "--", "InformationTheory/")
        removed += len(
            [l for l in diff.splitlines() if l.startswith("-") and "@[entry_point]" in l]
        )
    check(
        "T06 no @[entry_point] removed in the window",
        removed == 0,
        f"削除された @[entry_point] 行 = {removed} ⟹ 改名・削除による数え落ちは無い",
    )


def t07_counting_blind_spot() -> None:
    """棚卸しの数え方 `rg -c '^\\+@\\[entry_point\\]'` / `rg -c '@\\[entry_point\\]'` は
    多属性形 `@[entry_point, reducible]` とインライン形 `@[entry_point] def foo` を取りこぼす。
    その盲点が (a) BC 配下で空であること (⟹ 84 本は正しい) を確かめ、
    (b) リポジトリ全体では空でないこと (⟹ 盲点は仮想ではない) を記録する。"""
    inline = re.compile(r"@\[entry_point[^\]]*\]\s*(theorem|lemma|def|noncomputable|private)")
    multi = re.compile(r"@\[entry_point[^\]]")

    def scan(root: Path) -> tuple[list[str], int]:
        hits, n_multi = [], 0
        for f in sorted(root.rglob("*.lean")):
            for i, line in enumerate(read(f).splitlines(), 1):
                if inline.search(line):
                    hits.append(f"{f.relative_to(ROOT)}:{i}")
                n_multi += len(multi.findall(line))
        return hits, n_multi

    bc_inline, bc_multi = scan(BC)
    check(
        "T07 the counting blind spot is EMPTY under BroadcastChannel/",
        not bc_inline and bc_multi == 0,
        f"BC 配下 インライン形 {len(bc_inline)} 件 / 多属性形 {bc_multi} 件 "
        "⟹ exact regex による 84 本のカウントは取りこぼしていない",
    )
    all_inline, all_multi = scan(ROOT / "InformationTheory")
    check(
        "T07b the same blind spot is NOT empty repo-wide",
        len(all_inline) >= 1,
        f"リポジトリ全体 インライン形 {len(all_inline)} 件 {all_inline} / 多属性形 {all_multi} 件",
    )
    note("棚卸し §1-2 / §3.1 の数え方は多属性形 `@[entry_point, ...]` とインライン形を "
         f"構造的に取りこぼす。その形はリポジトリに実在する ({len(all_inline)} 件のインライン形 / "
         f"{all_multi} 件の多属性形) が、窓の 5 commit の差分 (T03: anchored == loose) と "
         "BC 配下 (T07) ではいずれも空なので本数は生き残る。⚠ 棚卸しはこの盲点を名指ししていない")


# ---------------------------------------------------------------------------
# B. HEAD の実体 (棚卸し §1-3 … §1-6 / §3.1 / §3.4 / §6-4)
# ---------------------------------------------------------------------------

FIVE = [
    ("OuterBoundTransport.lean", 975, "plainDirectionalCombination_le_plainDirectionalBound"),
    ("OuterBoundTransport.lean", 1011, "plainDirectionalBound_eq_condFree"),
    ("OuterBoundTransport.lean", 1033, "plainDirectionalCombination_le_plainDirectionalBoundCondFree"),
    ("MoreCapableBinary.lean", 381, "log_two_mul_binEntropy_binConv_sub_binEntropy_le"),
    ("MoreCapableBinary.lean", 396, "binEntropy_binConv_sub_binEntropy_le"),
]


def t08_five_names() -> None:
    bad = []
    for fname, lineno, name in FIVE:
        lines = read(BC / fname).splitlines()
        if not (0 < lineno <= len(lines) and lines[lineno - 1].startswith(f"theorem {name}")):
            bad.append(f"{fname}:{lineno} {name}")
        elif not lines[lineno - 2].strip().startswith("@[entry_point]"):
            bad.append(f"{fname}:{lineno} {name} (no @[entry_point] on the previous line)")
    check(
        "T08 the 5 declarations exist in HEAD at the stated file:line, each with @[entry_point]",
        not bad,
        "5/5 実在" if not bad else f"不一致 {bad}",
    )


def t09_t10_sorry_residual() -> None:
    text = "".join(read(f) for f in sorted(BC.rglob("*.lean")))
    n_sorry = len(re.findall(r"sorry", text))
    n_res = len(re.findall(r"@residual", text))
    check("T09 sorry count under BroadcastChannel/ == 0", n_sorry == 0, f"{n_sorry} 件")
    check("T10 @residual count under BroadcastChannel/ == 0", n_res == 0, f"{n_res} 件")


def t11_t12_entry_point_totals() -> None:
    per_file = {}
    for f in sorted(BC.rglob("*.lean")):
        n = len(re.findall(r"@\[entry_point\]", read(f)))
        if n:
            per_file[f.relative_to(BC).as_posix()] = n
    total = sum(per_file.values())
    check(
        "T11 BroadcastChannel/ @[entry_point] total == 84 over 24 files",
        total == 84 and len(per_file) == 24,
        f"{total} 本 / {len(per_file)} ファイル",
    )
    obt = per_file.get("OuterBoundTransport.lean")
    mcb = per_file.get("MoreCapableBinary.lean")
    check(
        "T12 per-file split OuterBoundTransport=21 / MoreCapableBinary=2",
        obt == 21 and mcb == 2,
        f"OuterBoundTransport={obt} / MoreCapableBinary={mcb} "
        f"⟹ 判定枠由来 5 本 + 前 relay 以前 {total - 5} 本",
    )


def t13_morecapable_size() -> None:
    """棚卸し §6-4 は「406 行 / 29 宣言」と書く。HEAD の実体を再導出する。"""
    path = BC / "MoreCapableBinary.lean"
    n_lines = len(read(path).splitlines())
    out = subprocess.run(
        [str(ROOT / "scripts" / "sig_view.ts"), "--names", str(path)],
        cwd=ROOT, capture_output=True, text=True,
    ).stdout
    m = re.search(r"—\s*(\d+)\s*decls", out)
    n_decls = int(m.group(1)) if m else -1
    ok = n_lines == 410 and n_decls == 35
    check(
        "T13 MoreCapableBinary.lean at HEAD == 410 lines / 35 decls",
        ok,
        f"{n_lines} 行 / {n_decls} 宣言",
    )
    if "406 行 / 29 宣言" in read(STOCK):
        note("棚卸し §6-4 は「406 行 / 29 宣言」と書くが HEAD は "
             f"{n_lines} 行 / {n_decls} 宣言 (406 は commit 4da3a9ad の挿入行数)")


# ---------------------------------------------------------------------------
# C. 台帳タグの実在 (棚卸し §1 / §2 / §4 が引く全タグ)
# ---------------------------------------------------------------------------

CITED_TAGS = [
    "N6-d", "N6-f", "N6-g", "N6-j", "N6-l", "N6-n", "N6-o", "N6-p", "N6-q",
    "N7-a", "N7-b", "N7-h", "N7-i", "N7-p", "N7-r",
    "N8-a", "N8-b", "N8-d",
    "N9-a", "N9-c", "N9-f",
    "N10-a", "N10-c", "N10-e",
    "N11-a", "N11-b", "N11-c", "N11-d", "N11-g",
    "N1-a", "N1-b", "N1-i", "N1-j", "N2-l",
]


def t14_tags_exist() -> None:
    txt = read(FACTS)
    declared = {f"{a}-{b}" for a, b in re.findall(r"\((N\d+|A\d+|M\d+|L\d+)-([a-z]+)[、,\)]", txt)}
    missing = [t for t in CITED_TAGS if t not in declared]
    check(
        "T14 every facts tag cited by the stocktake is a declared claim in bc-facts.md",
        not missing,
        f"{len(CITED_TAGS)} タグ中 実在 {len(CITED_TAGS) - len(missing)}"
        + ("" if not missing else f" / 不在 {missing}"),
    )


# ---------------------------------------------------------------------------
# D. 棚卸しが自分で組み立てた統計 (§5 (a) / (c))
# ---------------------------------------------------------------------------

# 棚卸し §5 (a) の表の各行 (leg, 系統, 訂正, 主判定を動かした, 上方修正)
TABLE_A = [
    ("N6", 25, 6, 1, 3),
    ("N7", 35, 4, 0, 0),
    ("N8", None, 4, 0, 0),   # N8 は「反証 5 本」で系統勘定ではない
    ("N9", 43, 7, 0, 3),
    ("N10", 39, 8, 0, 5),
    ("N11", 49, 7, 0, 3),
]


def t15_corrections_sum() -> None:
    s = sum(r[2] for r in TABLE_A)
    printed = 33 if "**33**" in read(STOCK) else None
    check(
        "T15 §5(a) 訂正 column re-summed from the per-leg numbers",
        s == 36,
        f"6+4+4+7+8+7 = {s}",
    )
    if printed == 33:
        note(f"棚卸し §5(a) の「計」欄と §0-5 は 33 と書くが、同じ表の列を足すと {s} である "
             "(⟹ §5(a) の読み『33 件のうち 1 件 (3.0%)』『上方修正 14 件 (42%)』は "
             f"{s} を分母にすると 2.8% / 38.9% になる)")


def t16_families_sum() -> None:
    s = sum(r[1] for r in TABLE_A if r[1] is not None)
    check("T16 §5(a) 系統 column sums to 191", s == 191, f"25+35+43+39+49 = {s}")


def t17_upward_sum() -> None:
    s = sum(r[4] for r in TABLE_A)
    check("T17 §5(a) 上方修正 column sums to 14", s == 14, f"3+0+0+3+5+3 = {s}")
    s_main = sum(r[3] for r in TABLE_A)
    check("T17b §5(a) 主判定を動かした column sums to 1", s_main == 1, f"合計 {s_main}")


# 棚卸し §5 (c) の母集団 (leg, 締める本数, 完全に覆った, 一部覆った)
TABLE_C = [("N6", 4, 1, 0), ("N7", 5, 5, 0), ("N9", 5, 4, 1), ("N10", 3, 0, 0), ("N11", 1, 0, 0)]


def t18_tighten_population() -> None:
    n = sum(r[1] for r in TABLE_C)
    full = sum(r[2] for r in TABLE_C)
    part = sum(r[3] for r in TABLE_C)
    check(
        "T18 §5(c) 締める population == 18 with 10 fully overturned (56%)",
        n == 18 and full == 10 and part == 1,
        f"母集団 {n} / 完全 {full} ({full / n:.1%}) / 一部 {part} / 覆らず {n - full - part}",
    )
    # 分類の感度: N7 見立て 8 は成果物で「覆った (この方向に限る)」、N10 見立て 1 は
    # 「当たり、ただし表現に誤り 1 か所」= どちらも N9 見立て 5 と同じ「一部」型である。
    alt_full, alt_part = full - 2, part + 2
    check(
        "T18b classification sensitivity of the 56% figure",
        alt_full == 8,
        f"N7 見立て 8 と N10 見立て 1 を N9 見立て 5 と同じ「一部」に数えると "
        f"完全 {alt_full} ({alt_full / n:.1%}) / 一部 {alt_part} ⟹ 56% は分類 1 つで動く",
    )


def t19_pass_total() -> None:
    counts = [18, 20, 18, 20, 11, 12, 19, 46, 22, 34, 43]
    check("T19 11 verifiers' pass counts sum to 263", sum(counts) == 263, f"合計 {sum(counts)}")


# ---------------------------------------------------------------------------
# E. 検証器 11 本の直列実行 (pass 本数 + 所要時間)
# ---------------------------------------------------------------------------

# (module, 期待 pass 本数, 台帳が記録する所要秒 — None = 台帳に記録が無い)
VERIFIERS = [
    ("capacity_probc", 18, 13),
    ("n6_audit_probc", 20, 7),
    ("shoulder_certificate_probc", 18, 29),
    ("n7_audit_probc", 20, 88),
    ("kappa2_probc", 11, 7),
    ("kappa2_audit_probc", 12, 63),
    ("n9_cone_probc", 19, 25),
    ("n9_audit_probc", 46, 11),
    ("n10_epsilon_zero_probc", 22, 146),
    ("n10_audit_probc", 34, 46),
    ("n11_audit_morecapable", 43, None),
]

MEASURED: dict[str, float] = {}


def t20_t21_run_verifiers() -> None:
    """⚠ 直列・無負荷で走らせる。並行させると T21 の測定が壊れる。"""
    bad_counts, over = [], []
    total_pass = 0
    for mod, expected, ledger in VERIFIERS:
        t0 = time.time()
        proc = subprocess.run(
            [sys.executable, str(VERIF / f"{mod}.py")], cwd=ROOT, capture_output=True, text=True
        )
        elapsed = time.time() - t0
        MEASURED[mod] = elapsed
        m = re.findall(r"(\d+)\s*/\s*(\d+)", proc.stdout)
        got = None
        for a, b in reversed(m):
            if a == b:
                got = int(a)
                break
        print(f"       {mod}: EXIT={proc.returncode} {got}/{expected} {elapsed:.2f}s"
              + (f" (台帳 約 {ledger} 秒)" if ledger else " (台帳に所要時間の記録なし)"))
        if proc.returncode != 0 or got != expected:
            bad_counts.append(f"{mod}: EXIT={proc.returncode} got={got} want={expected}")
        else:
            total_pass += got
        if ledger is not None and elapsed > ledger * 1.25:
            over.append(f"{mod} {elapsed:.1f}s vs 台帳 {ledger}s")
    check(
        "T20 all 11 verifiers reproduce at HEAD (EXIT=0 and the ledger's pass count)",
        not bad_counts and total_pass == 263,
        f"合計 {total_pass}/263" + ("" if not bad_counts else f" / 不一致 {bad_counts}"),
    )
    check(
        "T21 serial+unloaded runtimes are NOT uniformly longer than the ledger's",
        len(over) <= 1,
        f"台帳より 25% 超過したのは {len(over)}/10 本" + (f" ({over})" if over else "")
        + " ⟹ 棚卸し §1 注の「一律に台帳の記録より長い」は直列・無負荷では再現しない",
    )


# ---------------------------------------------------------------------------
# F. 起票側の逐語 (棚卸し §5 (b) / §4.1)
# ---------------------------------------------------------------------------

def t22_n7_eleven_points() -> None:
    txt = read(ROOT / "docs" / "shannon" / "bc-t3c-n7-audit.md")
    check(
        "T22 the N7 audit's own wording backs the stocktake's 「独立に閉じたのは計 11 点」",
        "帯 4 点 + 本文 7 点の計 11 点" in txt,
        "N7 監査 §9-1 に逐語で在る (4 + 7 = 11)",
    )


def t23_n8_ticket_has_no_falsification_conditions() -> None:
    diff = git("show", "c90baafb", "--", "docs/shannon/bc-open-problem-t3c-plan.md")
    added = [l[1:] for l in diff.splitlines() if l.startswith("+") and not l.startswith("+++")]
    hits = [l for l in added if ("反証条件" in l or "見立て" in l)]
    decl = [l for l in added if l.startswith("**leg 冒頭宣言 (N8)**")]
    check(
        "T23 the N8 ticket commit adds a 冒頭宣言 but no 反証条件 / 見立て",
        not hits and len(decl) == 1,
        f"追加行 {len(added)} 本中 反証条件/見立て {len(hits)} 本 / 冒頭宣言 {len(decl)} 本",
    )


def t24_n6_declaration_added_at_landing() -> None:
    diff = git("show", "7ff07b0f", "--", "docs/shannon/bc-open-problem-t3c-plan.md")
    added = [l for l in diff.splitlines() if l.startswith("+") and "leg 冒頭宣言 (N6)" in l]
    check(
        "T24 the N6 冒頭宣言 first enters the plan at the landing commit 7ff07b0f",
        len(added) == 1,
        "着地 commit で追記されている ⟹ 起票時の plan ブロックは存在しない",
    )


def t25_n6j_avoidance_condition() -> None:
    """棚卸し §4.1 は「回避条件はどこにも書かれていない」と書く。N6-j の逐語を当てる。"""
    txt = read(FACTS)
    obstruction = "NO-GO は比較であり比較の相手が要る" in txt
    avoidance = "「`Thm7` 側の上界だけを一般 BC へ持ち上げる」は (γ) とは別の的として well-posed" in txt
    check(
        "T25 facts N6-j carries BOTH the named obstruction and an avoidance condition",
        obstruction and avoidance,
        f"障害の名指し={obstruction} / 回避条件={avoidance}",
    )
    stock = read(STOCK)
    if avoidance and "well-posed" not in stock:
        note("棚卸し §4.1 は N6-j を引きながら障害の側だけを引用し、同じ行の "
             "「反証の残骸 = Thm7 側の上界だけを一般 BC へ持ち上げるのは well-posed」を落としている "
             "⟹ 「回避条件はどこにも書かれていない」は偽")


def t26_no_new_verdict() -> None:
    stock = read(STOCK)
    bad = re.findall(r"判定 *= *(NO-GO|GO)", stock)
    check(
        "T26 the stocktake issues no new 判定 = GO / NO-GO of its own",
        not bad,
        f"「判定 = GO/NO-GO」形 {len(bad)} 件",
    )


def t27_banned_phrasings() -> None:
    stock = read(STOCK)
    banned = {
        "Thm7 ⊄": r"Thm7 *⊄",
        "R ∈ Thm7": r"R ∈ Thm7",
        "あと少し": r"あと少し",
        "行数と配線": r"行数と配線",
        "§0 に近づいた": r"§0 に近づ",
    }
    hits = {k: len(re.findall(v, stock)) for k, v in banned.items()}
    bad = {k: n for k, n in hits.items() if n}
    # 「尽きた」は「『尽きた』ではない」の形だけが許される
    exhausted = re.findall(r".{6}尽きた.{8}", stock)
    bad_exhausted = [s for s in exhausted if "ではない" not in s]
    check(
        "T27 no banned phrasing in the stocktake",
        not bad and not bad_exhausted,
        f"禁止語 {bad or '0 件'} / 「尽きた」{len(exhausted)} 件 (すべて否定形: "
        f"{not bad_exhausted})",
    )


def t28_goal_section_untouched() -> None:
    """§0 / §0.1 が本 leg の commit で書き換えられていないこと (ゴール保護条項)."""
    diff = git("show", "c0c5b1b2", "--", "docs/shannon/bc-open-problem-t3c-plan.md")
    diff += git("show", "a568d478", "--", "docs/shannon/bc-open-problem-t3c-plan.md")
    touched = [
        l for l in diff.splitlines()
        if l.startswith(("+", "-")) and not l.startswith(("+++", "---"))
        and ("一般 2 受信者 DM-BC の容量領域" in l or "ゴール保護条項" in l)
    ]
    check(
        "T28 the N12 commits do not touch §0 / §0.1 of the plan",
        not touched,
        f"ゴール文・保護条項に触れた行 {len(touched)} 件",
    )


def main() -> int:
    skip_slow = "--skip-slow" in sys.argv
    print("=" * 78)
    print("n12_audit_stocktake.py — N12 棚卸しに対する独立再導出")
    print("=" * 78)
    t01_window_base()
    t02_window_commits()
    t03_t05_attribution()
    t06_no_removal()
    t07_counting_blind_spot()
    t08_five_names()
    t09_t10_sorry_residual()
    t11_t12_entry_point_totals()
    t13_morecapable_size()
    t14_tags_exist()
    t15_corrections_sum()
    t16_families_sum()
    t17_upward_sum()
    t18_tighten_population()
    t19_pass_total()
    if skip_slow:
        print("[SKIP] T20 / T21 (--skip-slow)")
    else:
        t20_t21_run_verifiers()
    t22_n7_eleven_points()
    t23_n8_ticket_has_no_falsification_conditions()
    t24_n6_declaration_added_at_landing()
    t25_n6j_avoidance_condition()
    t26_no_new_verdict()
    t27_banned_phrasings()
    t28_goal_section_untouched()

    passed = sum(1 for _, ok, _ in RESULTS if ok)
    failed = len(RESULTS) - passed
    print("=" * 78)
    for text in NOTES:
        print(f"NOTE: {text}")
    if NOTES:
        print("-" * 78)
    print(f"{passed}/{len(RESULTS)} passed, {failed} failed")
    return 0 if failed == 0 else 1


if __name__ == "__main__":
    sys.exit(main())

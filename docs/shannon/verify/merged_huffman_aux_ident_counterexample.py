import itertools
from functools import lru_cache

# Colex order on frozensets of ints:  toColex s < toColex t  iff  max(s △ t) ∈ t
def colex_lt(s, t):
    sym = s ^ t
    if not sym:
        return False
    m = max(sym)
    return m in t

# total order key for groupKey = (prob, colex(label)).
# Returns a comparator-style sort: we sort list of (label_frozenset, prob).
# min by (prob asc, colex asc).  Implement argmin.
def groupkey_min(groups):
    # groups: list of (frozenset label, prob)
    best = None
    for g in groups:
        if best is None:
            best = g
        else:
            lbl, p = g
            blbl, bp = best
            if p < bp or (p == bp and colex_lt(lbl, blbl)):
                best = g
    return best

def huffman_depths(init_groups):
    """init_groups: list of (frozenset({elem}), prob). Returns dict elem->depth."""
    # work on a mutable list of (frozenset, prob)
    groups = [ (frozenset(l), p) for (l,p) in init_groups ]
    # collect all ground elements
    ground = set()
    for l,_ in groups:
        ground |= l
    depth = {e:0 for e in ground}
    while len(groups) >= 2:
        x1 = groupkey_min(groups)
        groups.remove(x1)
        x2 = groupkey_min(groups)
        groups.remove(x2)
        A = x1[0]; B = x2[0]
        for e in (A | B):
            depth[e] += 1
        merged = (A | B, x1[1] + x2[1])
        groups.append(merged)
    return depth

def check_statement(n, wmax):
    """Enumerate integer weight vectors of length n in [1..wmax]. For each, and each
    (a,b) satisfying preconditions (a global min, b min among non-a, a!=b, sibling),
    verify the merged-identity for all x != b. Return list of counterexamples."""
    counter = []
    sibling_satisfying = 0
    checked = 0
    for w in itertools.product(range(1, wmax+1), repeat=n):
        # original tree over beta = {0..n-1}
        init = [ (frozenset({e}), w[e]) for e in range(n) ]
        depthQ = huffman_depths(init)
        for a in range(n):
            # a global min
            if any(w[a] > w[c] for c in range(n)):
                continue
            for b in range(n):
                if b == a: continue
                # b min among non-a
                if any(w[b] > w[c] for c in range(n) if c != a):
                    continue
                # sibling
                if depthQ[a] != depthQ[b]:
                    continue
                sibling_satisfying += 1
                # build merged init over beta \ {b}: a gets w[a]+w[b], others keep
                merged_elems = [e for e in range(n) if e != b]
                minit = []
                for e in merged_elems:
                    p = (w[a]+w[b]) if e == a else w[e]
                    minit.append((frozenset({e}), p))
                depthM = huffman_depths(minit)
                checked += 1
                # verify identity for all x != b
                ok = True
                bad = None
                for x in merged_elems:
                    expected = (depthQ[a] - 1) if x == a else depthQ[x]
                    if depthM[x] != expected:
                        ok = False
                        bad = (x, depthM[x], expected)
                        break
                if not ok:
                    counter.append((n, w, a, b, depthQ, depthM, bad))
    return counter, sibling_satisfying, checked

for n in [3,4,5,6]:
    for wmax in [3,4,5]:
        c, sib, chk = check_statement(n, wmax)
        print(f"n={n} wmax={wmax}: precond-satisfying(a,b)={sib}, checked={chk}, COUNTEREXAMPLES={len(c)}")
        for ce in c[:3]:
            print("   CE:", ce)

print("\n=== MINIMAL COUNTEREXAMPLE trace: w=[1,2,1,1], a=0, b=2 ===")
w=[1,2,1,1]; a=0; b=2
init=[(frozenset({e}),w[e]) for e in range(4)]
dQ=huffman_depths(init)
print("original tree depths:", dQ, " (sibling: dQ[a]==dQ[b]?", dQ[a]==dQ[b],")")
merged_elems=[e for e in range(4) if e!=b]
minit=[(frozenset({e}), (w[a]+w[b]) if e==a else w[e]) for e in merged_elems]
print("mergedInit labels/probs:", [(sorted(l),p) for l,p in minit])
dM=huffman_depths(minit)
print("merged tree depths:", dM)
for x in merged_elems:
    exp=(dQ[a]-1) if x==a else dQ[x]
    print(f"  x={x}: merged depth={dM[x]}, formula expects={exp}", "OK" if dM[x]==exp else "<<< MISMATCH")

print("\n=== SANITY: no-tie distributions should ALWAYS satisfy the identity ===")
import itertools
def all_distinct_weights(n, vals):
    for combo in itertools.permutations(vals, n):
        yield combo
# use distinct powers-of-2-ish to also avoid partial-sum ties; check identity holds
bad_notie=0; checked_notie=0
for n in [3,4,5,6]:
    # distinct weights with widely separated magnitudes => no prob ties, sums distinct
    base=[1,2,4,8,16,32,64]
    vals=base[:n]
    for w in itertools.permutations(vals,n):
        init=[(frozenset({e}),w[e]) for e in range(n)]
        dQ=huffman_depths(init)
        for a in range(n):
            if any(w[a]>w[c] for c in range(n)): continue
            for bb in range(n):
                if bb==a: continue
                if any(w[bb]>w[c] for c in range(n) if c!=a): continue
                if dQ[a]!=dQ[bb]: continue
                melems=[e for e in range(n) if e!=bb]
                mi=[(frozenset({e}),(w[a]+w[bb]) if e==a else w[e]) for e in melems]
                dM=huffman_depths(mi)
                checked_notie+=1
                for x in melems:
                    exp=(dQ[a]-1) if x==a else dQ[x]
                    if dM[x]!=exp: bad_notie+=1; break
print(f"no-tie (distinct, separated weights): checked={checked_notie}, counterexamples={bad_notie}")

print("\n=== Are ALL counterexamples tie-driven? Check min-prob multiplicity in CEs ===")
c,_,_=check_statement(5,4)
notie_ce=0
for (n,w,a,b,dQ,dM,bad) in c:
    minp=min(w)
    mult=sum(1 for x in w if x==minp)
    if mult==1 and len(set(w))==len(w): notie_ce+=1
print(f"n=5,wmax=4: total CE={len(c)}, CE with strictly-distinct weights={notie_ce}")

# ============================================================================
# PIVOT EVIDENCE (2026-05-30): cost-level identity is TRUE where depth-level is FALSE.
# - depth-level per-symbol identity (MergedHuffmanAuxIdentHypothesis / HuffmanMergedIdentificationHypothesis)
#   is FALSE under deterministic colex tie-break (2532 counterexamples among 61254 precond cases).
# - COST-level merge identity  cost(huffman Q) = cost(huffman mergedQ') + (Q{a}+Q{b})  holds in ALL
#   61254 cases (0 failures). The deterministic algorithm produces a different *tree* but the same
#   optimal *cost*, since cost is tie-break invariant.
# - Cleanest form: multiset-level recursion  cost(huffmanLengthAux s) = cost(huffmanLengthAux s'') + (x1.p+x2.p)
#   where (x1,x2,s'') = huffmanStep s. Verified 0 failures; near-definitional, needs no (a,b) global-min framing.
# => Pivot: prove Huffman strong-form optimality via the tie-invariant cost recursion over the
#    actually-first-merged pair (huffmanStep output), inducting on s.card — NOT the per-symbol depth identity.

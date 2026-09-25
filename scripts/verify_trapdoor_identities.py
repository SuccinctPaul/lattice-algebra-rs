#!/usr/bin/env python3
"""Scratch verification of every algebraic identity the lattice-trapdoor
capability claims, in a concrete ring R_q = Z_q[X]/(X^d+1), written BEFORE the
Rust implementation (house rule: verify the algebra in python first).

A "gadget trapdoor" for a matrix B of height h means any M with B.M = G_h
(MP12 Def. 5.2 with tag H = I; SLAP Lem. 2.13; FMN Lem. 2.15).

  I1  TrapGen        A = [Abar | G - Abar R], M = [R; I]  =>  A.M = G
  I2  det preimage   x = M G^-1(u)                          =>  A.x = u
  I3  rnd preimage   x = p + M G^-1(u - B.p)                =>  B.x = u, x random
  I4  norm bound     |M G^-1(v)|_inf <= dz*(d*|M|_row1 + 1)
  I5  BASIS pair     R_i = R G^-1(W^-i G), B = [blockdiag(W^i A) | -G]
                     Rt = [R_0;..;R_d;0] (block cols)       =>  B.Rt = G_{n(d+1)}
  I5b randomised T   B.T = G_{n(d+1)} with T short, T != Rt
  I7  FMN Fig.4      A s_i + f_i e1 = W^-i t, t != 0, tampers detected
  I6  SLAP Fig.4     w^{b_j} A_j s_{b:j} + t_{b:j} = t_{b:j-1}
                     => sum_j w_j^{b_j} A_j s_{b:j} + f_b e1 = t_eps

Big instance: q = 2^32-99 (prime, 5 mod 8), d = 4, 32 binary digits.
Small instance for the combinatorially heavier tree: q = 257, d = 2, 9 digits.

Run: python3 scripts/verify_trapdoor_identities.py
"""

import random

random.seed(20260923)


def make(MOD, DIM, BASE, DIGITS):
    """A tiny typed layer over Z_MOD[X]/(X^DIM+1) plus matrix helpers."""
    DZ = BASE // 2 if BASE > 2 else 1
    PZ = [0] * DIM
    PO = [1] + [0] * (DIM - 1)

    def padd(a, b):
        return [(x + y) % MOD for x, y in zip(a, b)]

    def psub(a, b):
        return [(x - y) % MOD for x, y in zip(a, b)]

    def pmul(a, b):
        r = [0] * (2 * DIM - 1)
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    r[i + j] = (r[i + j] + x * y) % MOD
        out = r[:DIM]
        for i in range(DIM, 2 * DIM - 1):
            out[i - DIM] = (out[i - DIM] - r[i]) % MOD
        return out

    def pneg(a):
        return [(-x) % MOD for x in a]

    def pinv_const(p):
        assert p[1:] == [0] * (DIM - 1) and p[0] % MOD != 0, "not an invertible constant"
        return [pow(p[0], MOD - 2, MOD)] + [0] * (DIM - 1)

    def prand():
        return [random.randrange(MOD) for _ in range(DIM)]

    def pshort(bound):
        return [random.randrange(-bound, bound + 1) % MOD for _ in range(DIM)]

    def pinf(a):
        return max(min(x, MOD - x) for x in a)

    def vadd(u, v):
        return [padd(a, b) for a, b in zip(u, v)]

    def vsub(u, v):
        return [psub(a, b) for a, b in zip(u, v)]

    def vscale(c, u):
        return [pmul(c, a) for a in u]

    def mzeros(r, c):
        return [[list(PZ) for _ in range(c)] for _ in range(r)]

    def mid(r):
        return [[PO[:] if i == j else list(PZ) for j in range(r)] for i in range(r)]

    def mmul(M, N):
        r, k, c = len(M), len(N), len(N[0])
        assert len(M[0]) == k, (len(M[0]), k)
        o = mzeros(r, c)
        for i in range(r):
            for t in range(k):
                a = M[i][t]
                if any(a):
                    for j in range(c):
                        o[i][j] = padd(o[i][j], pmul(a, N[t][j]))
        return o

    def msub(M, N):
        return [[psub(a, b) for a, b in zip(x, y)] for x, y in zip(M, N)]

    def mvec(M, v):
        r, c = len(M), len(M[0])
        assert len(v) == c, (len(v), c)
        out = []
        for i in range(r):
            acc = list(PZ)
            for j in range(c):
                acc = padd(acc, pmul(M[i][j], v[j]))
            out.append(acc)
        return out

    def as_col(v):
        return [[x] for x in v]

    def col(X):
        return [row[0] for row in X]

    def mcat_cols(M, N):
        return [r1 + r2 for r1, r2 in zip(M, N)]

    def mcat_rows(M, N):
        assert len(M[0]) == len(N[0])
        return [r[:] for r in M] + [r[:] for r in N]

    def vec_inf(v):
        return max(pinf(a) for a in v)

    def mat_row_l1(M):
        return max(sum(pinf(a) for a in row) for row in M)

    def mat_eq(A, B):
        return len(A) == len(B) and all(x == y for x, y in zip(A, B))

    def gadget(n):
        pw = [PO[:]]
        b = [BASE] + [0] * (DIM - 1)
        for _ in range(DIGITS - 1):
            pw.append(pmul(pw[-1], b))
        G = mzeros(n, n * DIGITS)
        for j in range(n):
            for t in range(DIGITS):
                G[j][j * DIGITS + t] = pw[t][:]
        return G

    def ginv(M):
        r, c = len(M), len(M[0])
        out = mzeros(r * DIGITS, c)
        for i in range(r):
            for j in range(c):
                x = M[i][j]
                for t in range(DIGITS):
                    out[i * DIGITS + t][j] = [(x[k] // BASE ** t) % BASE for k in range(DIM)]
        assert mat_eq(mmul(gadget(r), out), M), "G . G^-1 = id failed"
        return out

    def bound_of(Mat):
        """certified |M G^-1(v)|_inf bound: digits have |.|_inf <= dz, |.|_1 <= d*dz"""
        return DZ * DIM * mat_row_l1(Mat) + DZ

    def pre_det(B, Mat, u):
        return mvec(Mat, col(ginv(as_col(u))))

    def pre_rnd(B, Mat, u, pb):
        p = [pshort(pb) for _ in range(len(Mat))]
        return vadd(p, mvec(Mat, col(ginv(as_col(vsub(u, mvec(B, p)))))))

    return dict(MOD=MOD, DIM=DIM, BASE=BASE, DIGITS=DIGITS, DZ=DZ, PZ=PZ, PO=PO,
                padd=padd, psub=psub, pmul=pmul, pneg=pneg, pinv_const=pinv_const,
                prand=prand, pshort=pshort, pinf=pinf, vadd=vadd, vsub=vsub,
                vscale=vscale, mzeros=mzeros, mid=mid, mmul=mmul, msub=msub,
                mvec=mvec, as_col=as_col, col=col, mcat_cols=mcat_cols,
                mcat_rows=mcat_rows, vec_inf=vec_inf, mat_row_l1=mat_row_l1,
                mat_eq=mat_eq, gadget=gadget, ginv=ginv, bound_of=bound_of,
                pre_det=pre_det, pre_rnd=pre_rnd,
                scalar=lambda c: [c % MOD] + [0] * (DIM - 1))


# ================= big instance: TrapGen, samplers, BASIS pair ==============
g = make(4294967197, 4, 2, 32)
MOD, DIM, DZ = g['MOD'], g['DIM'], g['DZ']
N, MBAR = 2, 3
T = N * g['DIGITS']
print("instance A: q = %d (prime, 5 mod 8), d = %d, base = 2, digits = %d, n = %d, mbar = %d"
      % (MOD, DIM, g['DIGITS'], N, MBAR))

Abar = [[g['prand']() for _ in range(MBAR)] for _ in range(N)]
R = [[g['pshort'](1) for _ in range(T)] for _ in range(MBAR)]
Gd = g['gadget'](N)
A = g['mcat_cols'](Abar, g['msub'](Gd, g['mmul'](Abar, R)))
Mtrap = g['mcat_rows'](R, g['mid'](T))
assert g['mat_eq'](g['mmul'](A, Mtrap), Gd), "I1 FAILED"
assert all(A[i][j] == Abar[i][j] for i in range(N) for j in range(MBAR)), "I1b FAILED"
print("I1  OK  A.M = G  (A %dx%d, M %dx%d); A's left half is exactly the uniform block"
      % (len(A), len(A[0]), len(Mtrap), len(Mtrap[0])))

bA = g['bound_of'](Mtrap)
worst = 0
for _ in range(6):
    u = [g['prand']() for _ in range(N)]
    x = g['pre_det'](A, Mtrap, u)
    assert g['mvec'](A, x) == u, "I2 FAILED"
    worst = max(worst, g['vec_inf'](x))
    assert g['vec_inf'](x) <= bA, ("I4 FAILED", g['vec_inf'](x), bA)
print("I2  OK  A.(M G^-1 u) = u for 6 targets | I4 OK  bound %d >= observed %d" % (bA, worst))

seen = set()
worst2 = 0
for _ in range(6):
    u = [g['prand']() for _ in range(N)]
    x = g['pre_rnd'](A, Mtrap, u, 3)
    assert g['mvec'](A, x) == u, "I3 FAILED"
    assert g['vec_inf'](x) <= bA + 3, ("I4b FAILED", g['vec_inf'](x), bA + 3)
    worst2 = max(worst2, g['vec_inf'](x))
    seen.add(tuple(tuple(c) for c in x))
assert len(seen) == 6, "I3b FAILED: randomised draws collided"
print("I3  OK  6 distinct randomised short preimages of the same target (worst %d <= %d)"
      % (worst2, bA + 3))


def diag_unit_matrix(g, ws):
    W = [[g['pmul'](ws[i], g['PO'][:]) if i == j else list(g['PZ']) for j in range(len(ws))]
         for i in range(len(ws))]
    Wi = [[g['pmul'](g['pinv_const'](ws[i]), g['PO'][:]) if i == j else list(g['PZ'])
          for j in range(len(ws))] for i in range(len(ws))]
    assert g['mat_eq'](g['mmul'](W, Wi), g['mid'](len(ws))), "W W^-1 != I"
    return W, Wi


def basis_pair(DSLOT):
    # W = w.I with w a scalar unit: the crate has no ring-element or matrix
    # inversion, so the demo instance draws units whose inverse is exact.
    ws = [g['scalar'](random.randrange(1, MOD)) for _ in range(N)]
    W, Wi = diag_unit_matrix(g, ws)
    m = len(A[0])
    Wp, Wip, acc, acci = [], [], g['mid'](N), g['mid'](N)
    for _ in range(DSLOT):
        Wp.append(acc)
        Wip.append(acci)
        acc, acci = g['mmul'](acc, W), g['mmul'](acci, Wi)
    Rs = [g['mmul'](R, g['ginv'](g['mmul'](Wip[i], Gd))) for i in range(DSLOT)]
    B = g['mzeros'](N * DSLOT, m * DSLOT + T)
    for i in range(DSLOT):
        Ai = g['mmul'](Wp[i], A)
        for r in range(N):
            for c in range(m):
                B[i * N + r][i * m + c] = Ai[r][c]
            for c in range(T):
                B[i * N + r][m * DSLOT + c] = g['pneg'](Gd[r][c])
    Rt = g['mzeros']((m + T) * DSLOT + T, T * DSLOT)
    for i in range(DSLOT):
        for r in range(m):
            for c in range(T):
                Rt[r + i * (m + T)][c + i * T] = Rs[i][r][c]
    want = g['mzeros'](N * DSLOT, T * DSLOT)
    for i in range(DSLOT):
        for r in range(N):
            for c in range(T):
                want[i * N + r][i * T + c] = Gd[r][c]
    assert g['mat_eq'](g['mmul'](B, Rt), want), "I5 FAILED"
    return B, Rt, want, Wp, Wip, m


for DSLOT in (2, 3):
    B, Rt, want, Wp, Wip, m = basis_pair(DSLOT)
    print("I5  OK  B.Rt = G_{n(d+1)} for d+1 = %d (B %dx%d, Rt %dx%d)"
          % (DSLOT, len(B), len(B[0]), len(Rt), len(Rt[0])))
    # Setup step 5, randomised: T short with B.T = G_{n(d+1)}, T != Rt
    Tcols = [g['pre_rnd'](B, Rt, [want[i][j] for i in range(N * DSLOT)], 2)
             for j in range(T * DSLOT)]
    Tm = [[Tcols[j][i] for j in range(T * DSLOT)] for i in range(len(Rt))]
    assert g['mat_eq'](g['mmul'](B, Tm), want), "I5b FAILED"
    assert g['vec_inf']([e for r in Tm for e in r]) <= g['bound_of'](Rt) + 2, "I4c FAILED"
    assert not g['mat_eq'](Tm, Rt), "I5c FAILED: randomised T equals Rt"
    # the DETERMINISTIC preimage of G_{n(d+1)} degenerates to Rt (bottom block 0),
    # which is why Setup must randomise: assert that, so the claim is measured
    Tdet_cols = [g['pre_det'](B, Rt, [want[i][j] for i in range(N * DSLOT)])
                 for j in range(T * DSLOT)]
    Tdet = [[Tdet_cols[j][i] for j in range(T * DSLOT)] for i in range(len(Rt))]
    assert g['mat_eq'](Tdet, Rt), "expected Tdet == Rt"
    # FMN Fig.4 Commit/Open
    f = [g['prand']() for _ in range(DSLOT)]
    e1 = [g['PO'][:]] + [list(g['PZ']) for _ in range(N - 1)]
    u = []
    for i in range(DSLOT):
        u = u + [g['pneg'](g['pmul'](f[i], c)) for c in g['mvec'](Wp[i], e1)]
    x = g['pre_det'](B, Tm, u)
    assert g['mvec'](B, x) == u, "I7a FAILED"
    s = [x[i * (m + T):i * (m + T) + m] for i in range(DSLOT)]
    that = x[len(x) - T:]
    tt = g['mvec'](Gd, that)
    assert g['vec_inf'](x) <= g['bound_of'](Tm) + DZ, "I4d FAILED"
    for i in range(DSLOT):
        lhs = g['vadd'](g['mvec'](A, s[i]), g['vscale'](f[i], e1))
        assert lhs == g['mvec'](Wip[i], tt), ("I7 FAILED at slot", i)
    assert tt != [list(g['PZ']) for _ in range(N)], "I7b FAILED: commitment is zero"
    bad = [r[:] for r in s[0]]
    bad[0] = g['padd'](bad[0], g['PO'][:])
    assert g['vadd'](g['mvec'](A, bad), g['vscale'](f[0], e1)) != g['mvec'](Wip[0], tt), "I7c"
    bf = f[:]
    bf[0] = g['padd'](bf[0], g['PO'][:])
    assert g['vadd'](g['mvec'](A, s[0]), g['vscale'](bf[0], e1)) != g['mvec'](Wip[0], tt), "I7d"
    print("I7  OK  A s_i + f_i e1 = W^-i t for %d slots, t != 0, opening+m message tampers caught"
          % DSLOT)

# ================= small instance: SLAP Fig.4 tree ==========================
h = make(257, 2, 2, 9)
hMOD, hDIM = h['MOD'], h['DIM']
hN, hMBAR = 2, 2
hT = hN * h['DIGITS']
print("instance B (tree): q = %d, d = %d, digits = %d, n = %d, mbar = %d"
      % (hMOD, hDIM, h['DIGITS'], hN, hMBAR))
H = 2
levels = []
for _ in range(H):
    hAbar = [[h['prand']() for _ in range(hMBAR)] for _ in range(hN)]
    hR = [[h['pshort'](1) for _ in range(hT)] for _ in range(hMBAR)]
    hG = h['gadget'](hN)
    hA = h['mcat_cols'](hAbar, h['msub'](hG, h['mmul'](hAbar, hR)))
    assert h['mat_eq'](h['mmul'](hA, h['mcat_rows'](hR, h['mid'](hT))), hG), "I1 on B failed"
    w = h['scalar'](random.randrange(1, hMOD))
    m = len(hA[0])
    # R_0 = R G^-1(G), R_1 = R G^-1(W^-1 G) with W = w.I
    W1, Wi1 = diag_unit_matrix(h, [w] * hN)
    R0 = h['mmul'](hR, h['ginv'](hG))
    R1 = h['mmul'](hR, h['ginv'](h['mmul'](Wi1, hG)))
    Bslap = h['mzeros'](2 * hN, 2 * m + hT)
    for r in range(hN):
        for c in range(m):
            Bslap[r][c] = hA[r][c]
            Bslap[hN + r][m + c] = h['pmul'](w, hA[r][c])
        for c in range(hT):
            Bslap[r][2 * m + c] = h['pneg'](hG[r][c])
            Bslap[hN + r][2 * m + c] = h['pneg'](hG[r][c])
    Rtj = h['mzeros'](2 * (m + hT) + hT, 2 * hT)
    for i, blk in enumerate([R0, R1]):
        for r in range(m):
            for c in range(hT):
                Rtj[r + i * (m + hT)][c + i * hT] = blk[r][c]
    want = h['mzeros'](2 * hN, 2 * hT)
    for i in range(2):
        for r in range(hN):
            for c in range(hT):
                want[i * hN + r][i * hT + c] = hG[r][c]
    assert h['mat_eq'](h['mmul'](Bslap, Rtj), want), "I6a FAILED"
    Tcols = [h['pre_rnd'](Bslap, Rtj, [want[i][j] for i in range(2 * hN)], 2)
             for j in range(2 * hT)]
    Tj = [[Tcols[k][i] for k in range(2 * hT)] for i in range(len(Rtj))]
    assert h['mat_eq'](h['mmul'](Bslap, Tj), want), "I6a2 FAILED"
    levels.append((hA, w, Tj, Bslap, m))
print("I6a OK  B_j = [[A,0,-G],[0,wA,-G]] has B_j.Rt_j = B_j.T_j = G_{2n} for %d levels" % H)

fleaf = {b: h['prand']() for b in range(1 << H)}
vals = {}
for b in range(1 << H):
    vals[(b, H)] = [fleaf[b] if i == 0 else list(h['PZ']) for i in range(hN)]
openings = {}
for j in range(H, 0, -1):
    hA, w, Tj, Bslap, m = levels[j - 1]
    for prefix in range(1 << (j - 1)):
        tgt = []
        for bit in (0, 1):
            tgt = tgt + [h['pneg'](c) for c in vals[((prefix << 1) | bit, j)]]
        x = h['pre_det'](Bslap, Tj, tgt)
        assert h['mvec'](Bslap, x) == tgt, "I6b0 FAILED"
        s0, s1, that = x[0:m], x[m:2 * m], x[2 * m:]
        parent = h['mvec'](h['gadget'](hN), that)
        vals[(prefix, j - 1)] = parent
        openings[(prefix << 1, j)] = s0
        openings[((prefix << 1) | 1, j)] = s1
        assert h['vadd'](h['mvec'](hA, s0), vals[(prefix << 1, j)]) == parent, "I6b L"
        assert h['vadd']([h['pmul'](w, e) for e in h['mvec'](hA, s1)],
                         vals[((prefix << 1) | 1, j)]) == parent, "I6b R"
print("I6b OK  w^{b_j} A_j s_{b:j} + t_{b:j} = t_{b:j-1} at every node")

root = vals[(0, 0)]
assert root != [list(h['PZ']) for _ in range(hN)], "I6c0: root commitment is zero"
worstn = 0
for b in range(1 << H):
    bits = [(b >> (H - 1 - k)) & 1 for k in range(H)]
    total = [list(h['PZ']) for _ in range(hN)]
    pref = 0
    for j in range(1, H + 1):
        s = openings[((pref << 1) | bits[j - 1], j)]
        worstn = max(worstn, h['vec_inf'](s))
        term = h['mvec'](levels[j - 1][0], s)
        if bits[j - 1]:
            term = [h['pmul'](levels[j - 1][1], e) for e in term]
        total = h['vadd'](total, term)
        pref = (pref << 1) | bits[j - 1]
    assert h['vadd'](total, [fleaf[b] if i == 0 else list(h['PZ']) for i in range(hN)]) == root, "I6c"
print("I6c OK  sum_j w_j^{b_j} A_j s_{b:j} + f_b e1 = t_eps for all %d leaves (max |s|_inf %d)"
      % (1 << H, worstn))
print("ALL IDENTITIES VERIFIED")

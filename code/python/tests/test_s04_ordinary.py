# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""S04-C1: ordinary toolkit (proj, tower): PYCHK e^2 = e, U_p e = e U_p, deg U_p = p, pi_*-discriminator, Hida."""

import numpy as np
import pytest

from langlandscape.ordinary import proj, tower

P, Q3 = 5, 125
CASES = [(3, 1, 1), (2, 7, 1), (3, 1, 2)]  # (D, M, N0)


@pytest.fixture(scope="module")
def T3():
    return tower.tower(3, P)


@pytest.fixture(scope="module")
def T27():
    return tower.tower(2, P, 7)


def _traces(X, k=6):
    return [int(np.trace(np.linalg.matrix_power(X, j))) for j in range(1, k + 1)]


# ---------------------------------------------------------------- proj on synthetic data

def test_projector_synthetic():
    rng = np.random.default_rng(1)
    n, p, m = 12, 5, 3
    q = p**m
    J = np.zeros((n, n), dtype=np.int64)
    J[:4, :4] = rng.integers(0, q, (4, 4)) + 7 * np.eye(4, dtype=np.int64)  # unit mod p? ensure below
    while not proj.is_invertible_mod_p(J[:4, :4], p):
        J[:4, :4] = rng.integers(0, q, (4, 4))
    J[4:, 4:] = np.triu(rng.integers(0, q, (8, 8)), 1) + p * np.eye(8, dtype=np.int64)  # topologically nilpotent
    S = rng.integers(0, q, (n, n))
    while not proj.is_invertible_mod_p(S, p):
        S = rng.integers(0, q, (n, n))
    T = proj.mul(proj.mul(S, J, q), proj.inv(S, p, m), q)
    Pr = proj.ordinary_projector(T, p, m)
    e = Pr.e
    assert Pr.rank == 4
    assert (proj.mul(e, e, q) == e).all() and (proj.mul(T, e, q) == proj.mul(e, T, q)).all()
    assert (proj.mul(Pr.coord, Pr.basis, q) == np.eye(4, dtype=np.int64)).all()
    E0 = np.zeros((n, n), dtype=np.int64)
    E0[:4, :4] = np.eye(4, dtype=np.int64)
    assert (e == proj.mul(proj.mul(S, E0, q), proj.inv(S, p, m), q)).all()
    assert proj.ordinary_rank(np.zeros((3, 3), dtype=np.int64), p) == 0


def test_mul_split_exact():
    rng = np.random.default_rng(2)
    q = 5**12
    A, B = rng.integers(0, q, (20, 20)), rng.integers(0, q, (20, 20))
    ref = (A.astype(object) @ B.astype(object)) % q
    assert (proj.mul(A, B, q) == ref.astype(np.int64)).all()


def test_orbits():
    assert proj.orbits([[1, 2, 0, 3]], 4) == [[0, 1, 2], [3]]


# ---------------------------------------------------------------- tower: sizes, degrees, cross-checks

def test_sizes(T3, T27):
    assert [len(T3.X(s)) for s in (1, 2)] == [2, 50]
    assert len(T3.Xp(1)) == P * len(T3.X(1)) and len(T3.Xp(2)) == P * len(T3.X(2))
    assert len(T27.X(1)) == 48 and len(T27.Xp(1)) == 240
    T = tower.tower(3, P, 1, 2)
    assert len(T.X(1)) == 3 * 2  # [U_0(2)] index 3


@pytest.mark.parametrize("D,M,N0", CASES)
def test_degree(D, M, N0):
    T = tower.tower(D, P, M, N0)
    for s, prime in ((1, False), (1, True)):
        U = T.Up(s, prime)
        assert (U.sum(axis=0) == P).all()
    assert (T.Up_prime(1).sum(axis=0) == P).all()


def test_matches_stage1_up(T3):
    from langlandscape import up

    C = up.context(2)
    for s in (1, 2):
        assert _traces(C.Up(s)) == _traces(T3.Up(s))
        assert _traces(C.Up_prime(s)) == _traces(T3.Up_prime(s))
        assert (T3.Up(s).T == T3.Up_prime(s)).all()  # M = 1: U_p^* = U'_p


def test_matches_sign_pin(T27):
    from langlandscape.ordinary import sign_pin

    S = sign_pin.Setting()
    assert _traces(S.Up()) == _traces(T27.Up(1)) and _traces(S.Up_prime()) == _traces(T27.Up_prime(1))
    U, V, Dp = T27.Up(1), T27.Up_prime(1), T27.p_M(1)
    assert ((U.T - Dp @ V) % Q3 == 0).all()          # sign +1 of H6_sign.json
    assert not ((U.T - Dp.T @ V) % Q3 == 0).all()


# ---------------------------------------------------------------- PYCHK

@pytest.mark.parametrize("D,M,N0", CASES)
def test_e_idempotent_commutes(D, M, N0):
    T = tower.tower(D, P, M, N0)
    for s, prime in ((1, False), (1, True), (2, False)):
        if (D, M, s) == (2, 7, 2):
            continue
        U = T.Up(s, prime)
        Pr = T.e(s, 3, prime)
        e = Pr.e
        assert (proj.mul(e, e, Q3) == e).all()
        assert (proj.mul(U, e, Q3) == proj.mul(e, U, Q3)).all()
        assert proj.is_invertible_mod_p(proj.restrict(Pr, U), P)  # U_p invertible on eM
        nil = proj.power(proj.mul(U, (np.eye(len(U), dtype=np.int64) - e) % Q3, Q3), Pr.k, Q3)
        assert not nil.any()  # U_p nilpotent on (1 - e)M


@pytest.mark.parametrize("D,M,N0", [(3, 1, 1), (3, 1, 2)])
def test_discriminator(D, M, N0):
    T = tower.tower(D, P, M, N0)
    pp = T.pi_push(1)
    assert (pp @ T.Up(2) == T.Up(1) @ pp).all()                    # N_{U_p} commutes with pi_*
    assert not (pp @ T.Up_prime(2) == T.Up_prime(1) @ pp).all()    # U'_p does not
    ppr, pdd = T.pi_prime_push(1), T.pi_dprime_push(1)
    assert (ppr @ pdd == pp).all()
    assert (ppr @ T.Up(1, True) == T.Up(1) @ ppr).all()
    assert (pdd @ T.Up(2) == T.Up(1, True) @ pdd).all()


def test_discriminator_M7(T27):
    """Same with an extra prime ``M = 7`` (D = 2): X_1 -> X'_1 -> X_1 only (X_2 has 1200 points)."""
    ppr = T27.pi_prime_push(1)
    assert (ppr @ T27.Up(1, True) == T27.Up(1) @ ppr).all()


# ---------------------------------------------------------------- Delta_s, freeness, Hida

def test_delta_orbits_free(T3):
    for s in (1, 2):
        for prime in (False, True):
            orbs = T3.delta_orbits(s, prime)
            assert {len(o) for o in orbs} == {P ** (s - 1)}
            D = T3.delta_gen(s, prime)
            assert (D @ T3.Up(s, prime) == T3.Up(s, prime) @ D).all()


def test_hida(T3):
    """lem:s04-hida (c), (d): rk e on X'_s = rk e on X_s, e pi'_* injective on e; Delta-rank constant, free."""
    ranks = {}
    for s in (1, 2):
        r = T3.ordinary_delta_rank(s, 2)
        assert r["free"]
        ranks[s] = r["rank"]
        Pp, Px = T3.e(s, 2, True), T3.e(s, 2)
        assert Pp.rank == Px.rank
        assert proj.rank_mod_p(T3.pi_prime_push(s) @ Pp.basis, P) == Px.rank
        assert T3.ordinary_delta_rank(s, 2, True)["free"]
    assert ranks[1] == ranks[2]
    # the Z_p-module Z[X_s] itself is free over Delta_s (free action): e = 1 for T = identity
    I = np.eye(len(T3.X(2)), dtype=np.int64)
    r = proj.group_ring_rank(proj.ordinary_projector(I, P, 1), T3.delta_gen(2), T3.delta_order(2))
    assert r["free"] and r["rank"] == len(T3.X(2)) // P

"""S01-C1: class sets of definite quaternion algebras (mass, h(D), |Gamma_x|).

The tests compute in memory only; ``code/results/s01/classsets.json`` is written by
``python -m langlandscape.classset`` (``classset.main``), never by the tests.
"""

import pytest

from langlandscape import classset
from langlandscape.quat import DefiniteAlgebra

PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53]
H_PRIMES = [1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 3, 3, 4, 4, 5, 5]
D_LIST = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 30, 31, 37, 41, 42, 43, 47, 53, 59, 66, 70, 78]


@pytest.fixture(scope="module")
def data():
    return classset.compute_all()


def test_D_list(data):
    assert classset.definite_D_list() == D_LIST
    assert sorted(map(int, data)) == D_LIST


def test_mass_formula(data):
    for D, r in data.items():
        assert r["mass"] == r["expected_mass"], D


def test_class_numbers_primes(data):
    assert [data[str(p)]["h"] for p in PRIMES] == H_PRIMES


def test_stabilisers(data):
    assert data["11"]["gammas"] == [4, 6]
    assert data["2"]["gammas"] == [24]


def test_ell_choice():
    assert DefiniteAlgebra(2).ell == 3
    assert DefiniteAlgebra(30).ell == 7

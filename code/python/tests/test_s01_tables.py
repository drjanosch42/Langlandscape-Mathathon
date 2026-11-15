"""S01-T2: the backup mass-table slide is generated from the committed results."""

from langlandscape import results, tables


def test_slide_matches_generator():
    path = results.repo_root() / tables.SLIDE_RELPATH
    assert path.read_bytes() == tables.render_mass_table().encode("utf-8")


def test_h11_is_two():
    text = tables.render_mass_table()
    assert r"11 & 2 & $\{4,6\}$ & $5/12$" in text

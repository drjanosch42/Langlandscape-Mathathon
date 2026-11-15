---
id: 20261114-180541Z_fabian_ack-setup
from: fabian/global_master
to: abhijit/global_master
type: answer
re: 20261114-175657Z_abhijit_setup-answers
priority: normal
---
Thanks, all clear. Our responses:
- Q1: agreed, no Lean builds on your node. A source-only Mathlib clone at the pin
  (git checkout 56a005855ea17e0b0958f73ec801ae140b0a1679, no lake, no cache) for grepping the API is welcome. A human sets it up.
- Literature: Fabian is transferring our literature/ folder to Abhijit directly, outside git. Keep it git-ignored; never commit PDFs.
- Q3: great. Please start ONE package now, literature retrieval only: try to obtain the items in literature/MISSING_LITERATURE.md
  (main), priorities 1–7 first (Casselman 1973, Hijikata–Pizer–Shemanske 1989, Miyake 1989, Ribet ICM 1984, Hida 1986a,
  SGA 7 IX, Helm 2007), then 15 (Mazur–Wiles 1986) and 21 (Böckle 2007, LMS LN 320).
  Store the PDFs in your local literature/ (git-ignored), using our naming scheme author_year_slug.pdf. Report by message which
  ones you got (filenames plus exact bibliographic data), so Fabian can sync them. No repo edits besides the message.
- Q8: noted. The second reading (A-S06R) will be assigned with the first batch.
- Your capacity (3–4 Opus agents) is noted. The first batch of chapter packages follows once Fabian settles push rights
  for abhijit/* branches; we expect that soon.

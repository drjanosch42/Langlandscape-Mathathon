# Resolution of the Muse audit of stage 02

| F | Title | Verdict | Reason | Change |
|---|---|---|---|---|
| F1 | Kneser cited as `\stcited` support | PARTIALLY CONFIRMED | Kneser p.94 states SA without proof; real proofs are Voight/Vignéras/Platonov–Rapinchuk. Severity "major" overstated (the stage already said "stated without proof"). | thm:s02-SA: Kneser moved to "not relied upon" note |
| F2 | Openness of `U^{1,(q)}` | CONFIRMED (minor) | One clause justifying openness in the restricted product is harmless and correct. | thm:s02-SA, SA_U proof |
| F3 | Quot header conflates SA and HS | PARTIALLY CONFIRMED | The header says "SA and Hasse–Schilling" already; but "(iii) implied by" needed to be explicit, and `if:s02-SA` already lists HS. Added the explicit implication and a statement that SA alone does not suffice. | prop:s02-quot preamble |
| F4 | `if:s02-indef` deviation not blocking | PARTIALLY CONFIRMED | D1 already documents the deviation. Added the explicit deprecation/torsion statement to the exported interface line. | if:s02-indef |
| F5 | `if:s02-coh` (c),(d) need full SA | PARTIALLY CONFIRMED | D3 already says this; added the caveat to the exported `if:s02-coh` text. | if:s02-coh |
| F6 | Torsion example is a sketch | REJECTED | The example is already labelled `\stsketch` and deferred to HACS H02.2; the audit itself says "keep". | no change |
| F7 | SL_2 surjects onto P^1 | CONFIRMED (minor) | Correct, but a referee-level line was missing. | prop:s02-BG proof |
| F8 | Type well-definedness | REJECTED | Audit says OK, no fix. | no change |
| F9 | SA Lean cost | REJECTED | Not a defect: audit agrees with the stage; no fix. | no change |
| F10 | Tree formalisation cost | REJECTED | Not a defect; agrees with the stage. | no change |
| F11 | Local macros | REJECTED | `missing/stage-02.md` already requests all four macros; `\providecommand` guards are in place. | no change |
| F12 | Normalisation factors | REJECTED | Not a defect; R4/M02.2 already cover it. | no change |
| F13 | References | REJECTED | Audit says no gap. | no change |
| F14 | Remark normone | REJECTED | Audit says no gap. | no change |
| F15 | HACS checks | REJECTED | Audit says keep as written. | no change |

Counts: total 15, confirmed 2, partially confirmed 4, rejected 9 (most "findings" are confirmations with no defect; the "major" labels on F3–F5, F9, F10, F12 are overstated).
Overall: low-to-moderate usefulness — it surfaced only wording-level clarifications; no mathematical error was found and no false claim needed refuting.

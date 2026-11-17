# Independent reverse review of global-geometry support results

The 9 sources and 123 public declarations (26 definitions, 2 abbrevs, 92 theorems, 3 lemmas) underwent separate independent readback of complete sources, actual types, and transitive-axiom outputs. Every actual exit code was 0, using only the three foundational axioms. Counts include declarations with attributes on the same line. Reviewers did not construct the new sources reviewed; earlier authorship of library dependencies is not misrepresented as absence from the independent review of that new source.

| Module | Declarations | Independent report SHA256 |
| --- | --- | --- |
| LeviCivitaUniqueness | 4 | `245bf25d2c1f73e6f882d17f430f63dd9c5835629640fcef9c22397282169b3b` |
| MeasureGluing | 5 | `16c106b31ad7134d3d2c5362bf75ee236be9a083bbd426848065341146768242` |
| CoordinateCovariantDerivative | 20 | `0e97c52bc369153f7e73a1d940e769dfd3cf9378afce44fef25c046e29426022` |
| AffineConnection | 23 | `49a84c2fc94e60379184e3bf26214b0175f1a8eb28a196bcc4d2b387cabb2050` |
| ManifoldBilinear | 14 | `a460343aaa6f6843847923a96f56be722d5ddfa703653775c312f02da0007f59` |
| ManifoldVolume | 26 | `6bd87159c9f05101407cd70ff7e34ad2471861a70c8300b0f9031bb6d2670dcf` |
| ConnectionCoordinateChange | 15 | `8688147f170de923cda545eadd6857b331b5690cdaea6d3fe6034d5755b0b486` |
| ManifoldTensorNorm | 12 | `3d5f44b0cab6919bfcc21915087f0e96a3b8c5010d23b4beb2c68a9f022098eb` |
| ManifoldMetricSequence | 4 | `b6c39e315d52c034d6be8db3a6ac5ab1671c33b0c06397af6dfcdc3c170bdce4` |

See the [mathematical explanation](global-geometry.en.md) for precise scope and the [JSON](global-geometry-source-bindings.json) for source/report/receipt byte bindings.

Review covered empty M and default values outside charts, the actual same-B compatibility chain, existence of a countable cover and independence of its choice; actual vector-field pairing derivatives, the two subtraction terms and LieBracket sign; the physical Hilbert norm and actual-frame invertibility; and the same r and n-independent constant in passing from compact-set C0loc on M to fixed-chart component convergence.

The nonlinear transformation was additionally checked with G=[1,1;1,2]⊕I to distinguish a matrix inverse from entrywise reciprocation, and with A=I/J=0/H011=1 to test nonzero connection and new-jet terms. The accepted production Christoffel inverse explicitly has Matrix type. Earlier private type/automation failures retain their historical status and are excluded from accepted receipts.

These checks do not claim formulas for arbitrary maximal-atlas charts, Radon regularity, identification of actual chart second derivatives, global LC, or closure of the complete original admissibility assumptions. The volume is base-manifold dV_g; defect mu remains unconstructed. New author confirmation is pending; the whole paper and F04/F05 remain OPEN.

Complete machine checks, actual CI with main, and independent artifact review for the 285-target/93-source candidate require new receipts for the final version; an older green 254-target result is not reused. Central engineering and per-source mathematical reviews, and same-account GitHub actions versus cross-account Approve, are recorded separately.

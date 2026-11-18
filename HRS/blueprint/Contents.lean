import PaperIndex
import Commutator
import Screening
import Evidence
import Verso
import VersoManual
import VersoBlueprint
open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "Fluctuations of Riesz gases" =>

%%%
tag := "home"
%%%

The fluctuation theory of Riesz gases combines estimates for the modulated energy with Gaussian comparison. The commutator estimate controls the change of energy under transport; the screening results describe the covariance of observations at shrinking spatial scales.

The chapters below present the sharp sub-Coulomb commutator and the mesoscopic comparison, with their hypotheses, proofs and Lean declarations. The index follows the paper and supplement: 24 top-level headings, 143 subsections and eight selected declaration entries, including the square-root estimate from Lemma C.6.

The exposition follows the Lean statements. Paper labels provide the organization; the source links give the declarations and their proofs. Admitted statements are identified alongside the separate proved declarations where these are available.

{ref "commutator"}[The sharp sub-Coulomb commutator]

{ref "screening"}[Mesoscopic observations and screening]

{ref "paper-index"}[Browse the paper and supplement]

{ref "evidence"}[Evidence and selected direct proof calls]

{include 0 Commutator}
{include 0 Screening}
{include 0 PaperIndex}
{include 0 Evidence}

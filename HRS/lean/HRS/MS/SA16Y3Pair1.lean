import HRS.MS.SA16Y3Ext1
import HRS.MS.SA16SEn11

/-!
# S.A.16 (SA16Y3) Pair1: pairing of the jet energy with an element whose jets are those of a smooth function
(packet P7 iso, step (a), item (iii))

`sa16y3_pairDensity`: for `φ ∈ C_c^∞` and `H ∈ W^{m,p}` whose jets are a.e. `wJet m ψ` (`ψ` smooth, not necessarily compactly
supported): `closedPairDensity (Jφ) H = sa16sz_dens m p φ ψ` a.e.
`sa16y3_fderiv_pair`: `d(jetEnergy_m)_{Jφ}(H) = p ∫ sa16sz_dens m p φ ψ`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Pair1
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

lemma sa16y3_pairDensity {ψ : Euc d → ℝ} (m : ℕ) (φ : ccSub d) (H : WmpSpace d m p)
    (hH : (((H : WLp d m p)) : Euc d → WIndex d m → ℝ) =ᵐ[volume] wJet m ψ) :
    closedPairDensity d m p (sa16r_Jcc d m p φ) H =ᵐ[volume] sa16sz_dens m p φ.1 ψ := by
  rw [sa16r_Jcc_eq]
  filter_upwards [sa16r_cc_elt_coe (p := p) φ.2 m, hH] with x hx hy
  unfold closedPairDensity sa16sz_dens sa16sz_vn closedTensor
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : ∀ idx : Fin (j : ℕ) → Fin d,
      ((sa16r_cc_elt φ.2 m : WmpSpace d m p) : WLp d m p) x ⟨j, idx⟩ = partialDeriv idx φ.1 x := by
    intro idx; rw [hx]; rfl
  have h2 : ∀ idx : Fin (j : ℕ) → Fin d, ((H : WLp d m p) : Euc d → WIndex d m → ℝ) x ⟨j, idx⟩ =
      partialDeriv idx ψ x := by
    intro idx; rw [hy]; rfl
  simp only [h1, h2]

lemma sa16y3_fderiv_pair {ψ : Euc d → ℝ} (m : ℕ) (φ : ccSub d) (H : WmpSpace d m p)
    (hH : (((H : WLp d m p)) : Euc d → WIndex d m → ℝ) =ᵐ[volume] wJet m ψ) :
    fderiv ℝ (jetEnergy d m p) (sa16r_Jcc d m p φ) H = p * ∫ x, sa16sz_dens m p φ.1 ψ x := by
  rw [(closed_jet_energy_calculus d m p).2.2.2 _ _ |>.2]
  congr 1
  exact integral_congr_ae (sa16y3_pairDensity m φ H hH)

end Pair1

end HRS.Whole.AppendixA.Phase2SA16R

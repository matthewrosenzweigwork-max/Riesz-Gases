import HRS.MC.CepP3Aux2

/-!
# Packet P3, Aux3: the Euclidean operator `L` and its commutation with periodization
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MC.CepP3

open HRS

variable {d N : ℕ}

/-- The forward operator `L F = ∂_t F + c Δ F + dF · b` on the covering space. -/
def Lop (c : ℝ) (b : ℝ × (Fin N → Euc d) → Fin N → Euc d) (F : ℝ × (Fin N → Euc d) → ℝ)
    (p : ℝ × (Fin N → Euc d)) : ℝ :=
  fderiv ℝ F p (1, 0)
    + c * ∑ k : Fin N × Fin d, fderiv ℝ (fderiv ℝ F) p (0, configBasis d N k) (0, configBasis d N k)
    + fderiv ℝ F p (0, b p)

theorem supp_fderiv2 {F : ℝ × (Fin N → Euc d) → ℝ} {R : ℝ} (hF : Supp R F) :
    Supp R (fderiv ℝ (fderiv ℝ F)) :=
  supp_fderiv_clm (supp_fderiv hF)

theorem supp_Lop (c : ℝ) (b : ℝ × (Fin N → Euc d) → Fin N → Euc d)
    {F : ℝ × (Fin N → Euc d) → ℝ} {R : ℝ} (hF : Supp R F) : Supp R (Lop c b F) := by
  intro q hq
  simp [Lop, supp_fderiv hF q hq, supp_fderiv2 hF q hq]

theorem Lop_per (c : ℝ) {b : ℝ × (Fin N → Euc d) → Fin N → Euc d}
    (hb : ∀ (w : Fin N → Lattice d) p, b (tau w p) = b p) {F : ℝ × (Fin N → Euc d) → ℝ} {R : ℝ}
    (hF : ContDiff ℝ ∞ F) (hS : Supp R F) (p : ℝ × (Fin N → Euc d)) :
    Lop c b (per F) p = per (Lop c b F) p := by
  obtain ⟨S, hSp, _⟩ := per_eventuallyEq hS p
  rw [per_eq_sum (supp_Lop c b hS) (fun w hw => hSp p (by simp) w hw)]
  unfold Lop
  rw [fderiv_per_eq_sum hF hS p hSp, fderiv2_per_eq_sum hF hS p hSp]
  have hA : (∑ w ∈ S, fderiv ℝ F (tau w p)) (1, 0) = ∑ w ∈ S, fderiv ℝ F (tau w p) (1, 0) := by
    simp only [ContinuousLinearMap.sum_apply]
  have hB : ∑ k : Fin N × Fin d, (∑ w ∈ S, fderiv ℝ (fderiv ℝ F) (tau w p)) (0, configBasis d N k)
        (0, configBasis d N k)
      = ∑ w ∈ S, ∑ k : Fin N × Fin d, fderiv ℝ (fderiv ℝ F) (tau w p) (0, configBasis d N k)
        (0, configBasis d N k) := by
    simp only [ContinuousLinearMap.sum_apply]
    exact Finset.sum_comm
  have hC : (∑ w ∈ S, fderiv ℝ F (tau w p)) (0, b p) = ∑ w ∈ S, fderiv ℝ F (tau w p) (0, b (tau w p)) := by
    simp only [ContinuousLinearMap.sum_apply, hb]
  rw [hA, hB, hC, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]

end HRS.MC.CepP3

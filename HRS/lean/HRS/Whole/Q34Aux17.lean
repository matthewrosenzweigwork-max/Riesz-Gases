import HRS.Whole.Q34Aux16

/-!
# Packet Q34, helper file 17: the centered operator `K = P T P` and its link to `Kop`
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric InnerProductSpace
open scoped ENNReal NNReal

namespace HRS.Whole.Q34

variable {d : ℕ} {s : ℝ} {ρ : Euc d → ℝ} {M : ℝ}

section Kc

variable [IsProbabilityMeasure (withDensityReal ρ)]

/-- The centered operator `K' = P T P` on `L²(ν)`. -/
def Kc (h : Q34Hyp d s ρ M) : Lp ℝ 2 (withDensityReal ρ) →L[ℝ] Lp ℝ 2 (withDensityReal ρ) :=
  (Pc (withDensityReal ρ)).comp ((TopL h).comp (Pc (withDensityReal ρ)))

theorem Kc_apply (h : Q34Hyp d s ρ M) (U : Lp ℝ 2 (withDensityReal ρ)) :
    Kc h U = Pc (withDensityReal ρ) (Top h (Pc (withDensityReal ρ) U)) := rfl

theorem Kc_symm (h : Q34Hyp d s ρ M) (U V : Lp ℝ 2 (withDensityReal ρ)) :
    inner ℝ (Kc h U) V = inner ℝ U (Kc h V) := by
  rw [Kc_apply, Kc_apply, Pc_symm, top_symm, ← Pc_symm]

theorem Kc_pos (h : Q34Hyp d s ρ M) (U : Lp ℝ 2 (withDensityReal ρ)) :
    0 ≤ inner ℝ (Kc h U) U := by
  rw [Kc_apply, Pc_symm]
  exact top_pos h _

theorem Kc_norm_le (h : Q34Hyp d s ρ M) (U : Lp ℝ 2 (withDensityReal ρ)) :
    ‖Kc h U‖ ≤ Mg d s M * ‖U‖ := by
  have hM0 : 0 ≤ M := (h.hρ.nonneg 0).trans (h.hM 0)
  have hMg0 := Mg_nonneg h.hd h.hsd hM0
  calc ‖Kc h U‖ ≤ ‖Top h (Pc (withDensityReal ρ) U)‖ := Pc_norm_le _
    _ ≤ Mg d s M * ‖Pc (withDensityReal ρ) U‖ := top_norm_le h _
    _ ≤ Mg d s M * ‖U‖ := mul_le_mul_of_nonneg_left (Pc_norm_le U) hMg0

theorem inner_one2_Kc (h : Q34Hyp d s ρ M) (U : Lp ℝ 2 (withDensityReal ρ)) :
    inner ℝ (one2 (withDensityReal ρ)) (Kc h U) = 0 := inner_one2_Pc _

theorem Pc_Kc (h : Q34Hyp d s ρ M) (U : Lp ℝ 2 (withDensityReal ρ)) :
    Pc (withDensityReal ρ) (Kc h U) = Kc h U := by
  rw [Kc_apply, Pc_idem]

/-- `Kop` for the Riesz kernel is the centered potential. -/
theorem kop_eq (hs0 : s ≠ 0) (ν : Measure (Euc d)) (u : Euc d → ℝ) :
    Kop (rieszKernel d s) ν u = fun x => Tk s ν u x - ∫ y, Tk s ν u y ∂ν := by
  funext x
  have hrk : ∀ z : Euc d, rieszKernel d s z = ‖z‖ ^ (-s) := rieszKernel_eq hs0
  simp only [Kop, projMean, pair, hrk, Tk]

/-- For a centered class `U`, `K' U` is a representative of `Kop U`. -/
theorem kc_ae (h : Q34Hyp d s ρ M) (U : Lp ℝ 2 (withDensityReal ρ))
    (hU : Pc (withDensityReal ρ) U = U) :
    (Kc h U : Euc d → ℝ) =ᵐ[withDensityReal ρ]
      Kop (rieszKernel d s) (withDensityReal ρ) (U : Euc d → ℝ) := by
  rw [kop_eq h.hs0.ne', Kc_apply, hU, Pc_apply]
  have hmean : inner ℝ (one2 (withDensityReal ρ)) (Top h U) =
      ∫ y, Tk s (withDensityReal ρ) (U : Euc d → ℝ) y ∂(withDensityReal ρ) := by
    rw [inner_one2]
    exact integral_congr_ae (top_ae h U)
  filter_upwards [Lp.coeFn_sub (Top h U) (inner ℝ (one2 (withDensityReal ρ)) (Top h U) •
    one2 (withDensityReal ρ)), Lp.coeFn_smul (inner ℝ (one2 (withDensityReal ρ)) (Top h U))
    (one2 (withDensityReal ρ)), one2_ae (ν := withDensityReal ρ), top_ae h U] with x h1 h2 h3 h4
  rw [h1, Pi.sub_apply, h2, Pi.smul_apply, h3, h4, hmean]
  simp

end Kc

end HRS.Whole.Q34

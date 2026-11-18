import HRS.Commutator.Torus.LEIBTAux25

/-!
# LEIB-T: the inhomogeneous fractional Leibniz rule on `𝕋^d`, uniformly in `η ∈ (0,1]`

Final assembly: transference of the `ℝ^d` Leibniz rule `XLI.main_uncond` to the torus (see the plan in the commit
message of `LEIBTAux1`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace
  ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma leibt_smooth_mul {f g h : Torus d → ℝ} (hf : Torus.IsSmooth f) (hg : Torus.IsSmooth g)
    (hh : ∀ x, h x = f x * g x) : Torus.IsSmooth h := by
  unfold Torus.IsSmooth Torus.IsCk at *
  have : Torus.lift h = fun y => Torus.lift f y * Torus.lift g y := by
    funext y; simp [Torus.lift, hh]
  rw [this]
  exact hf.mul hg

lemma leibt_continuous_of_smooth {f : Torus d → ℝ} (hf : Torus.IsSmooth f) : Continuous f :=
  Torus.continuous_of_continuous_lift (by
    have := hf
    unfold Torus.IsSmooth Torus.IsCk at this
    exact this.continuous)

lemma leibt_kappa_prod (r p q : ℝ≥0∞) (hp : p ≠ 0) (hq : q ≠ 0) (h : p⁻¹ + q⁻¹ = r⁻¹) :
    leibt_kappa d p * leibt_kappa d q = leibt_kappa d r := by
  unfold leibt_kappa
  rw [← ENNReal.rpow_add_of_nonneg _ _ ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
    ← ENNReal.toReal_add (ENNReal.inv_ne_top.2 hp) (ENNReal.inv_ne_top.2 hq), h]

lemma leibt_kappa_ne_top (p : ℝ≥0∞) : leibt_kappa d p ≠ ⊤ :=
  ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top

lemma leibt_limit {X B D : ℝ≥0∞} (hD : D ≠ ⊤)
    (h : ∀ δ : ℝ, 0 < δ → ∃ t : ℝ, 0 < t ∧ t ≤ δ ∧ X ≤ B + ENNReal.ofReal t * D) : X ≤ B := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hB => ?_
  set δ : ℝ := (ε : ℝ) / (D.toReal + 1) with hδ
  have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
  have hδ0 : 0 < δ := by positivity
  obtain ⟨t, ht0, htδ, hX⟩ := h δ hδ0
  refine hX.trans ?_
  gcongr
  calc ENNReal.ofReal t * D = ENNReal.ofReal (t * D.toReal) := by
        rw [ENNReal.ofReal_mul ht0.le, ENNReal.ofReal_toReal hD]
    _ ≤ ENNReal.ofReal ε := by
        apply ENNReal.ofReal_le_ofReal
        have h1 : t * D.toReal ≤ δ * D.toReal := by gcongr
        have h2 : δ * D.toReal ≤ ε := by
          rw [hδ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith [ENNReal.toReal_nonneg (a := D)]
        linarith
    _ = ε := by simp

end HRS.Commutator.TorusNote

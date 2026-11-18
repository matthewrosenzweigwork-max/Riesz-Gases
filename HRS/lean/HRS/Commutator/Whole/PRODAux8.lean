import HRS.Commutator.Whole.PRODAux7

/-!
# CMX-PROD helper file 8: the limit passage through Li's inequality
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff Convolution

noncomputable section

namespace HRS.Commutator.Whole.PROD

open HRS HRS.Whole HRS.Commutator.Whole
open HRS.PDE.ToolboxRd

variable {d : ℕ}

/-- `prod_J α` as an additive map. -/
def prod_Jhom (α : ℝ) : SchwartzMap (Euc d) ℂ →+ SchwartzMap (Euc d) ℂ :=
  AddMonoidHom.mk' (prod_J α) (fun φ ψ => XLI.mulS_add_phi (XLI.bsymX α) (XLI.bsymX_temperate α) φ ψ)

lemma prod_J_sum (α : ℝ) {ι : Type*} (S : Finset ι) (F : ι → SchwartzMap (Euc d) ℂ) :
    prod_J α (∑ i ∈ S, F i) = ∑ i ∈ S, prod_J α (F i) :=
  map_sum (prod_Jhom α) F S

lemma prod_schwartz_sum_apply {ι : Type*} (S : Finset ι) (F : ι → SchwartzMap (Euc d) ℂ) (x : Euc d) :
    (∑ i ∈ S, F i) x = ∑ i ∈ S, F i x := by
  simp

/-- `‖u‖_{L^p} ≤ ‖v‖_{L^p} + ‖u - v‖_{L^p}`. -/
lemma prod_norm_le_add {P : ℝ≥0∞} (hP1 : 1 ≤ P) (u v : Euc d → ℂ) :
    eLpNorm u P volume ≤ eLpNorm v P volume + eLpNorm (fun x => u x - v x) P volume := by
  have e : u = v + (fun x => u x - v x) := by funext x; simp
  conv_lhs => rw [e]
  exact eLpNorm_add_le hP1

/-- Hölder for the difference of products. -/
lemma prod_holder_diff {P Q : ℝ≥0∞} [ENNReal.HolderTriple P Q 2] {φ' f' χ' a' : Euc d → ℂ}
    (hφ : AEStronglyMeasurable φ' volume) (hf : AEStronglyMeasurable f' volume)
    (hχ : AEStronglyMeasurable χ' volume) (ha : AEStronglyMeasurable a' volume) :
    eLpNorm (fun x => φ' x * χ' x - f' x * a' x) 2 volume ≤
      eLpNorm (fun x => φ' x - f' x) P volume * eLpNorm χ' Q volume +
        eLpNorm f' P volume * eLpNorm (fun x => χ' x - a' x) Q volume := by
  have e : (fun x => φ' x * χ' x - f' x * a' x) =
      ((fun x => φ' x - f' x) • χ') + (f' • fun x => χ' x - a' x) := by
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply]
    ring
  rw [e]
  refine (eLpNorm_add_le (by norm_num)).trans ?_
  have h1 := eLpNorm_smul_le_mul_eLpNorm (μ := volume) (p := P) (q := Q) (r := 2)
    (φ := fun x => φ' x - f' x) (f := χ') (hφ.sub hf) hχ
  have h2 := eLpNorm_smul_le_mul_eLpNorm (μ := volume) (p := P) (q := Q) (r := 2)
    (φ := f') (f := fun x => χ' x - a' x) hf (hχ.sub ha)
  exact add_le_add h1 h2

end HRS.Commutator.Whole.PROD

import HRS.MS.Mov63CAux5
import HRS.MD.DOMCalc
import HRS.MS.MovLinAux12

/-!
# S6.3, uniqueness chain (N3b, part 1): pointwise representation of the pairing and cutoffs

Namespace `HRS.MS.Mov63`, helper prefix `mnc_`.  See `Mov63CAux1` for the plan.

* `mnc_ipL_repr`: for `ρ ≥ k > d/2` the functional `x ↦ ⟨g, x⟩` on `Σ^ρ` is `∫ g f_x` with a bounded `f_x`
  (`‖f_x‖_∞ ≤ C ‖x‖`), so it is linear in `g` and bounded by `C ‖x‖ ‖g‖_{L¹}`.
* the cutoffs `χ_n = χ(·/(n+1))` and the product formula for `S_0`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovForce HRS.MS.MovLin HRS.MH.DualityRd

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

lemma mnc_ipL_repr {k : ℕ} (hk : (d : ℝ) / 2 < k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {r : ℝ} (hr : (k : ℝ) ≤ r) (h0 : 0 ≤ r) (x : OscSpace d r), ∃ f : Euc d → ℝ,
      MemLp f 2 (volume : Measure (Euc d)) ∧ (∀ᵐ y ∂(volume : Measure (Euc d)), |f y| ≤ C * ‖x‖) ∧
      ∀ g : Euc d → ℝ, MemLp g 2 (volume : Measure (Euc d)) → mnc_ipL g h0 x = ∫ y, g y * f y := by
  obtain ⟨C0, hC0, hC⟩ := mn_sobolev_emb_gen (d := d) 0 k (mn_hn0 hk)
  refine ⟨C0, hC0, fun {r} hr h0 x => ?_⟩
  set y : OscSpace d (k : ℝ) := mov2d_j hr x with hy
  obtain ⟨f, hf, hfy⟩ := mn_exists_fun k y
  obtain ⟨g0, hg0, hfg, hb⟩ := hC f hf
  refine ⟨f, hf.1, ?_, fun g hg => ?_⟩
  · have hny : ‖y‖ ≤ ‖x‖ := by
      refine ((mov2d_j hr).le_opNorm x).trans ?_
      exact mul_le_of_le_one_left (norm_nonneg _) (mov2d_j_norm_le hr)
    filter_upwards [hfg] with z hz
    rw [hz]
    have := hb 0 le_rfl z
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    refine this.trans ?_
    rw [← OscSpace.norm_ofFun f hf, hfy]
    exact mul_le_mul_of_nonneg_left hny hC0
  · have e : mov2d_j h0 x = OscSpace.ofFun 0 f := by
      have h1 := movlin_j_comp (d := d) hr (Nat.cast_nonneg k) x
      rw [← hy] at h1
      rw [← h1, ← hfy, mov2d_j_ofFun _ hf]
    simp only [mnc_ipL, ContinuousLinearMap.comp_apply, innerSL_apply_apply]
    rw [e, mov2d_inner_ofFun hg hf.1]

/-- The `L¹` bound of the pairing. -/
lemma mnc_ipL_L1 {k : ℕ} (hk : (d : ℝ) / 2 < k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {r : ℝ} (hr : (k : ℝ) ≤ r) (h0 : 0 ≤ r) (x : OscSpace d r) (g : Euc d → ℝ),
      MemLp g 2 (volume : Measure (Euc d)) → Integrable g →
      |mnc_ipL g h0 x| ≤ C * ‖x‖ * ∫ y, |g y| := by
  obtain ⟨C, hC, h⟩ := mnc_ipL_repr (d := d) hk
  refine ⟨C, hC, fun {r} hr h0 x g hg hg1 => ?_⟩
  obtain ⟨f, hf, hbd, hrep⟩ := h hr h0 x
  rw [hrep g hg]
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ y, |g y * f y| ≤ ∫ y, (C * ‖x‖) * |g y| := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
          (hg1.abs.const_mul _) ?_
        filter_upwards [hbd] with y hy
        rw [abs_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right hy (abs_nonneg _)
    _ = C * ‖x‖ * ∫ y, |g y| := integral_const_mul _ _

end HRS.MS.Mov63

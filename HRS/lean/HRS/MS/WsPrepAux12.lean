import HRS.MS.WsPrepAux7
import HRS.MS.WsPrepAux11

/-!
# S21R packet 12: the `L²` distance is dominated by the `Σ^M` distance, and weak continuity of a resulting solution

`s21p_toLp_dist_zero`: `toLp : Σ^0 → L²` is isometric.
`s21p_L2_dist_le`: for `0 ≤ M` and `f, g ∈ Σ^M`, `‖f - g‖_{L²} ≤ ‖ofFun M f - ofFun M g‖_{Σ^M}`.
`s21p_rho_weak_cont`: a resulting solution (`IsResultingSolution`, `ρβ > 0` a probability density) is weakly continuous on `[0, ∞)`:
`r ↦ ∫ ψ ρ^r` is continuous on `[0,∞)` for every bounded continuous `ψ`.  Proof: `ρ^r - ρ^s = √ρβ (v_r - v_s)`, `ψ √ρβ ∈ L²`, and
`t ↦ v_t ∈ Σ^{102d+1020}` is continuous (`IsResultingSolution.cont`).  This is the hypothesis `hcont` of `s56_xi_cont_time`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff

namespace HRS.Whole

variable {d : ℕ}

theorem s21p_toLp_dist_zero (x y : OscSpace d 0) : ‖OscSpace.toLp x - OscSpace.toLp y‖ = ‖x - y‖ := by
  obtain ⟨b, hb⟩ := exists_hermiteHilbertBasisD (d := d)
  rw [OscSpace.toLp_eq_repr_symm b hb le_rfl x, OscSpace.toLp_eq_repr_symm b hb le_rfl y, ← map_sub,
    LinearIsometryEquiv.norm_map]
  have : (⟨fun α => OscSpace.hermiteCoeff x α, OscSpace.memℓp_hermiteCoeff le_rfl x⟩ :
        lp (fun _ : MultiIndex d => ℝ) 2) -
      ⟨fun α => OscSpace.hermiteCoeff y α, OscSpace.memℓp_hermiteCoeff le_rfl y⟩ = x - y := by
    ext α
    show OscSpace.hermiteCoeff x α - OscSpace.hermiteCoeff y α = OscSpace.coord x α - OscSpace.coord y α
    simp [OscSpace.hermiteCoeff]
  rw [this]
  rfl

theorem s21p_L2_dist_le {M : ℝ} (hM : 0 ≤ M) {f g : Euc d → ℝ} (hf : MemOsc M f) (hg : MemOsc M g) :
    ‖hf.1.toLp f - hg.1.toLp g‖ ≤ dist (OscSpace.ofFun (d := d) M f) (OscSpace.ofFun M g) := by
  have hf0 := s21p_memOsc_mono hM hf
  have hg0 := s21p_memOsc_mono hM hg
  have e1 : hf.1.toLp f = OscSpace.toLp (OscSpace.ofFun (d := d) 0 f) := (OscSpace.toLp_ofFun f hf0).symm
  have e2 : hg.1.toLp g = OscSpace.toLp (OscSpace.ofFun (d := d) 0 g) := (OscSpace.toLp_ofFun g hg0).symm
  rw [e1, e2, s21p_toLp_dist_zero, ← dist_eq_norm]
  exact s21p_ofFun_dist_le hM hf hg

theorem s21p_rho_weak_cont {s a β : ℝ} {ρβ : Euc d → ℝ} (hρβ : IsProbDensity ρβ) (hρβpos : ∀ x, 0 < ρβ x)
    {εstar ε : ℝ} {ψ₀ : Euc d → ℝ} {c₁ C₁ : ℝ} {ρ : ℝ → Euc d → ℝ}
    (hres : IsResultingSolution d s a β ρβ εstar ε ψ₀ c₁ C₁ ρ) (ψ : Euc d → ℝ) (hψ : Continuous ψ)
    (hbd : ∃ B, ∀ x, |ψ x| ≤ B) :
    ContinuousOn (fun r => ∫ x, ψ x * ρ r x) (Set.Ici 0) := by
  obtain ⟨B, hB⟩ := hbd
  set M : ℝ := 102 * (d : ℝ) + 1020 with hMdef
  have hM : 0 ≤ M := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    rw [hMdef]; positivity
  set v : ℝ → Euc d → ℝ := fun t x => (ρ t x - ρβ x) / Real.sqrt (ρβ x) with hv
  have hvm : ∀ t, 0 ≤ t → MemOsc M (v t) := fun t ht => (hres.weighted t ht).1
  -- `√ρβ ∈ L²`
  have hint : Integrable ρβ := by
    by_contra h
    have := hρβ.integral_one
    rw [integral_undef h] at this
    exact zero_ne_one this
  have hsq : MemLp (fun x => Real.sqrt (ρβ x)) 2 (volume : Measure (Euc d)) := by
    refine (memLp_two_iff_integrable_sq (hρβ.measurable.sqrt.aestronglyMeasurable)).2 ?_
    refine hint.congr (Filter.Eventually.of_forall fun x => ?_)
    show ρβ x = Real.sqrt (ρβ x) ^ 2
    rw [Real.sq_sqrt (hρβpos x).le]
  -- `g = ψ √ρβ ∈ L²`
  have hg : MemLp (fun x => ψ x * Real.sqrt (ρβ x)) 2 (volume : Measure (Euc d)) := by
    refine (hsq.const_mul |B|).of_le (hψ.aestronglyMeasurable.mul hsq.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_abs]
    exact mul_le_mul_of_nonneg_right ((hB x).trans (le_abs_self B)) (abs_nonneg _)
  -- `∫ ψ ρ^r = ∫ ψ ρβ + ∫ g v_r`
  have hdec : ∀ r : ℝ, 0 ≤ r → (∫ x, ψ x * ρ r x) =
      (∫ x, ψ x * ρβ x) + ∫ x, (ψ x * Real.sqrt (ρβ x)) * v r x := by
    intro r hr
    have h1 : Integrable (fun x => ψ x * ρβ x) := by
      refine (hint.const_mul |B|).mono' (hψ.aestronglyMeasurable.mul hρβ.measurable.aestronglyMeasurable)
        (Filter.Eventually.of_forall fun x => ?_)
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (hρβpos x)]
      exact mul_le_mul_of_nonneg_right ((hB x).trans (le_abs_self B)) (hρβpos x).le
    have h2 : Integrable (fun x => (ψ x * Real.sqrt (ρβ x)) * v r x) := (hg.integrable_mul (hvm r hr).1)
    rw [← integral_add h1 h2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show ψ x * ρ r x = ψ x * ρβ x + ψ x * Real.sqrt (ρβ x) * ((ρ r x - ρβ x) / Real.sqrt (ρβ x))
    have hs : Real.sqrt (ρβ x) ≠ 0 := (Real.sqrt_pos.2 (hρβpos x)).ne'
    field_simp
    ring
  -- the increment identity
  have hinc : ∀ r s' : ℝ, (hr : 0 ≤ r) → (hs' : 0 ≤ s') →
      (∫ x, ψ x * ρ r x) - ∫ x, ψ x * ρ s' x =
        inner ℝ (hg.toLp (fun x => ψ x * Real.sqrt (ρβ x)))
          ((hvm r hr).1.toLp (v r) - (hvm s' hs').1.toLp (v s')) := by
    intro r s' hr hs'
    rw [inner_sub_right, OscDual.inner_toLp_mul _ _ hg (hvm r hr).1, OscDual.inner_toLp_mul _ _ hg (hvm s' hs').1,
      hdec r hr, hdec s' hs']
    ring
  -- continuity
  rw [Metric.continuousOn_iff]
  intro s0 hs0 ε hε
  have hs0' : (0 : ℝ) ≤ s0 := hs0
  set G := hg.toLp (fun x => ψ x * Real.sqrt (ρβ x)) with hG
  have hK : 0 < ‖G‖ + 1 := by positivity
  have hc := hres.cont
  rw [Metric.continuousOn_iff] at hc
  obtain ⟨δ, hδ, hδ'⟩ := hc s0 hs0 (ε / (‖G‖ + 1)) (div_pos hε hK)
  refine ⟨δ, hδ, fun r hr hrs => ?_⟩
  have hr' : (0 : ℝ) ≤ r := hr
  have hd1 := hδ' r hr hrs
  rw [Real.dist_eq, hinc r s0 hr' hs0']
  calc |inner ℝ G ((hvm r hr').1.toLp (v r) - (hvm s0 hs0').1.toLp (v s0))|
      ≤ ‖G‖ * ‖(hvm r hr').1.toLp (v r) - (hvm s0 hs0').1.toLp (v s0)‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖G‖ * dist (OscSpace.ofFun (d := d) M (v r)) (OscSpace.ofFun M (v s0)) :=
        mul_le_mul_of_nonneg_left (s21p_L2_dist_le hM (hvm r hr') (hvm s0 hs0')) (norm_nonneg _)
    _ ≤ ‖G‖ * (ε / (‖G‖ + 1)) := mul_le_mul_of_nonneg_left hd1.le (norm_nonneg _)
    _ < ε := by
        rw [mul_div_assoc']
        rw [div_lt_iff₀ hK]
        nlinarith [norm_nonneg G]

end HRS.Whole

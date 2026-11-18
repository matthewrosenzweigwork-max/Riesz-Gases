import HRS.MS.MovAdjAux6

/-!
# S6.7 (packet P2, part 2): ingredients of the bridge `ψ_r = T(t-r)† ψ_t`

Namespace `HRS.MS.MovAdj`, helpers `s67_`.  Infrastructure for the supplement row `S:W:lem:r2mov-global-adjoint`; not a manuscript row.

* `s67_cont_val`, `s67_cont_time`: continuity of the classical solution in `(r,x)` and in `r`;
* `s67_time_lip`: `|f r₂ x - f r₁ x| ≤ B (1+|x|) (r₂ - r₁)` for `0 < r₁ ≤ r₂ ≤ t` (from the linear growth of `∂_r f`);
* `s67_T_deriv`: right derivative of `τ ↦ T(τ) v₀` at every `σ ≥ 0` for `v₀` in the Schwartz core;
* `s67_memLp_G`: `(1+|x|) √ρ ∈ L²`;  `s67_memLp_mul_bdd`: bounded function times an `L²` function.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovAdj

open HRS HRS.Whole HRS.MH.DualityRd HRS.MS.MovLin HRS.MS.Mov63

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

/-! ### The classical solution in time -/

theorem s67_cont_val {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW C t φ f) : Continuous fun p : Set.Icc (0 : ℝ) t × Euc d => f p.1 p.2 := by
  have h := hf.cont_c2 0 (by norm_num)
  have e : (fun p : Set.Icc (0 : ℝ) t × Euc d => f p.1 p.2) = fun p =>
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => Euc d) ℝ (fun i => i.elim0))
        (iteratedFDeriv ℝ 0 (f p.1) p.2) := by
    funext p
    simp [iteratedFDeriv_zero_apply]
  rw [e]
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => Euc d) ℝ (fun i => i.elim0)).continuous.comp h

theorem s67_cont_time {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW C t φ f) (x : Euc d) : ContinuousOn (fun r => f r x) (Set.Icc 0 t) := by
  have h := (s67_cont_val hf).comp (continuous_id.prodMk (continuous_const : Continuous fun _ : Set.Icc (0 : ℝ) t => x))
  rw [continuousOn_iff_continuous_restrict]
  exact h

/-- Time-Lipschitz bound of `f` with linear growth. -/
theorem s67_time_lip {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW C t φ f) :
    ∃ Bf : ℝ, 0 ≤ Bf ∧ (∀ r ∈ Set.Icc (0 : ℝ) t, ∀ x, |generatorW C r (f r) x| ≤ Bf * (1 + ‖x‖)) ∧
      ∀ r₁ r₂ : ℝ, 0 < r₁ → r₁ ≤ r₂ → r₂ ≤ t → ∀ x, |f r₂ x - f r₁ x| ≤ Bf * (1 + ‖x‖) * (r₂ - r₁) := by
  obtain ⟨B, hB⟩ := hf.bdd_time_deriv
  refine ⟨max B 0, le_max_right _ _, fun r hr x => (hB r hr x).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)), fun r₁ r₂ h1 h12 h2 x => ?_⟩
  have hcont : ContinuousOn (fun r => f r x) (Set.Icc r₁ r₂) :=
    (s67_cont_time hf x).mono (Set.Icc_subset_Icc h1.le h2)
  have hder : ∀ y ∈ Set.Ico r₁ r₂, HasDerivWithinAt (fun r => f r x)
      (-(generatorW C y (f y) x)) (Set.Ici y) y := by
    intro y hy
    exact (hf.time_deriv x y ⟨h1.trans_le hy.1, lt_of_lt_of_le hy.2 h2⟩).hasDerivWithinAt
  have hbd : ∀ y ∈ Set.Ico r₁ r₂, ‖-(generatorW C y (f y) x)‖ ≤ max B 0 * (1 + ‖x‖) := by
    intro y hy
    rw [norm_neg, Real.norm_eq_abs]
    exact (hB y ⟨h1.le.trans hy.1, hy.2.le.trans h2⟩ x).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have := norm_image_sub_le_of_norm_deriv_right_le_segment hcont hder hbd r₂ ⟨h12, le_rfl⟩
  simpa [Real.norm_eq_abs] using this

/-! ### The semigroup near the Schwartz core -/

set_option maxHeartbeats 1600000 in
theorem s67_T_deriv (H : Mov2dTh d s β q ρ) (ψ0 : 𝓢R)
    (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x)) {φ₀ : 𝓢R} {v₀ : MovL2Zero ρ}
    (hv : ∀ᵐ x ∂(volume : Measure (Euc d)), movFun v₀ x = φ₀ x) {σ : ℝ} (hσ : 0 ≤ σ) :
    ∃ φ' : 𝓢R, (∀ᵐ x ∂(volume : Measure (Euc d)), movFun (mov2d_T H ψ0 hψ0 σ v₀) x = φ' x) ∧
      ∃ w : MovL2Zero ρ, (∀ᵐ x ∂(volume : Measure (Euc d)), movFun w x = movS d s β ρ (⇑φ') x) ∧
        HasDerivWithinAt (fun τ => mov2d_T H ψ0 hψ0 τ v₀) (-w) (Set.Ici σ) σ := by
  have hTs := mov2d_isSemigroup H ψ0 hψ0
  obtain ⟨φ', hφ'⟩ := mov2d_T_core H ψ0 hψ0 φ₀ v₀ hv hσ
  obtain ⟨w, hw, hwd⟩ := mov2d_T_gen H ψ0 hψ0 φ' (mov2d_T H ψ0 hψ0 σ v₀) hφ'
  refine ⟨φ', hφ', w, hw, ?_⟩
  have h0 := hwd 0 le_rfl
  rw [mov2d_T_zero H ψ0 hψ0] at h0
  simp only [ContinuousLinearMap.one_apply] at h0
  have hslope := mov2d_slope_of_hasDerivWithinAt_Ici h0
  apply mov2d_hasDerivWithinAt_Ici
  refine hslope.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh' : (0 : ℝ) ≤ h := le_of_lt hh
  have hadd : mov2d_T H ψ0 hψ0 (σ + h) v₀ = mov2d_T H ψ0 hψ0 h (mov2d_T H ψ0 hψ0 σ v₀) := by
    rw [add_comm, hTs.add h σ hh' hσ]; rfl
  rw [hadd, mov2d_T_zero H ψ0 hψ0]
  simp

/-! ### `L²` facts -/

theorem s67_memLp_mul_bdd {g F : Euc d → ℝ} (hg : MemLp g 2 (volume : Measure (Euc d)))
    (hF : AEStronglyMeasurable F (volume : Measure (Euc d))) {B : ℝ} (hb : ∀ x, |F x| ≤ B) :
    MemLp (fun x => F x * g x) 2 (volume : Measure (Euc d)) := by
  refine MemLp.of_le_mul (c := B) hg (hF.mul hg.aestronglyMeasurable) (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (hb x) (abs_nonneg _)

/-- `(1+|x|) √ρ ∈ L²`. -/
theorem s67_memLp_G (H : Mov2dTh d s β q ρ) :
    MemLp (fun x => (1 + ‖x‖) * Real.sqrt (ρ x)) 2 (volume : Measure (Euc d)) := by
  obtain ⟨B, -, hR, -⟩ := HRS.MS.Mov0.mv0_gapref H.hd H.hs0 H.hsd H.hq H.hβ H.hρ
  have hρ := mnb_rhoData H
  have hmeas : AEStronglyMeasurable (fun x => (1 + ‖x‖) * Real.sqrt (ρ x)) (volume : Measure (Euc d)) :=
    ((continuous_const.add continuous_norm).mul (hρ.smooth.continuous.sqrt)).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hmeas]
  have h2 : Integrable (fun x => (2 : ℝ) * ρ x + 2 * (‖x‖ ^ 2 * ρ x)) :=
    (hR.integrable.const_mul 2).add (hR.moment2.const_mul 2)
  refine h2.mono' (hmeas.pow 2) (Filter.Eventually.of_forall fun x => ?_)
  have hρx : 0 ≤ ρ x := (hρ.pos x).le
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_pow, Real.sq_sqrt hρx]
  nlinarith [sq_nonneg (1 - ‖x‖), mul_nonneg hρx (sq_nonneg (1 - ‖x‖))]

end HRS.MS.MovAdj

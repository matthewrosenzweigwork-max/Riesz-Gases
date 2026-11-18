import HRS.Uniform.Q12P9

/-!
# Q12, Peyre part 11: uniform `C²` bounds of a jointly smooth periodic family
-/

noncomputable section

open HRS MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q12

variable {d : ℕ}

/-- Slicing a jointly `C²` map along `y ↦ (t, y)` does not increase the derivative bounds. -/
lemma q12_slice_bounds {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {F : ℝ × Euc d → X}
    (hF : ContDiff ℝ 2 F) (t : ℝ) (y : Euc d) :
    ‖fderiv ℝ (fun y' => F (t, y')) y‖ ≤ ‖fderiv ℝ F (t, y)‖ ∧
      ‖fderiv ℝ (fderiv ℝ (fun y' => F (t, y'))) y‖ ≤ ‖fderiv ℝ (fderiv ℝ F) (t, y)‖ := by
  set c : Euc d → ℝ × Euc d := fun y' => (t, y') with hc
  have hc2 : ContDiff ℝ 2 c := contDiff_const.prodMk contDiff_id
  have hdc : ∀ z, fderiv ℝ c z = ContinuousLinearMap.inr ℝ ℝ (Euc d) := fun z =>
    (hasFDerivAt_prodMk_right t z).fderiv
  have hdc2 : ∀ z, fderiv ℝ (fderiv ℝ c) z = 0 := fun z => by
    have : fderiv ℝ c = fun _ => ContinuousLinearMap.inr ℝ ℝ (Euc d) := funext hdc
    rw [this]; exact fderiv_const_apply _
  have hnorm : ‖ContinuousLinearMap.inr ℝ ℝ (Euc d)‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
    rw [ContinuousLinearMap.inr_apply, Prod.norm_def]
    simp
  constructor
  · show ‖fderiv ℝ (F ∘ c) y‖ ≤ _
    rw [q12_fderiv_comp_eq hF hc2]
    calc ‖(fderiv ℝ F (c y)).comp (fderiv ℝ c y)‖ ≤ ‖fderiv ℝ F (c y)‖ * ‖fderiv ℝ c y‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖fderiv ℝ F (t, y)‖ * 1 := by
          rw [hdc]; exact mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
      _ = _ := mul_one _
  · show ‖fderiv ℝ (fderiv ℝ (F ∘ c)) y‖ ≤ _
    have := q12_fderiv2_comp_le hF hc2 y (A₁ := ‖fderiv ℝ F (c y)‖) (A₂ := ‖fderiv ℝ (fderiv ℝ F) (c y)‖)
      (K₁ := 1) (K₂ := 0) le_rfl le_rfl (by rw [hdc]; exact hnorm) (by rw [hdc2]; exact le_of_eq (norm_zero (E := (Euc d →L[ℝ] Euc d →L[ℝ] (ℝ × Euc d))) ))
    simpa using this

/-- Uniform bounds over `t ∈ [0,1]` and all `y` for a jointly `C²` family, periodic in `y`. -/
lemma q12_unif_bounds {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {F : ℝ × Euc d → X}
    (hF : ContDiff ℝ 2 F) (hper : ∀ t, Torus.Per (fun y => F (t, y))) :
    ∃ B : ℝ, ∀ t ∈ Icc (0 : ℝ) 1, ∀ y : Euc d,
      ‖F (t, y)‖ ≤ B ∧ ‖fderiv ℝ (fun y' => F (t, y')) y‖ ≤ B ∧
        ‖fderiv ℝ (fderiv ℝ (fun y' => F (t, y'))) y‖ ≤ B := by
  have hF1 : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  have hc0 : Continuous fun p : ℝ × Euc d => ‖F p‖ := hF.continuous.norm
  have hc1 : Continuous fun p : ℝ × Euc d => ‖fderiv ℝ F p‖ :=
    (hF.continuous_fderiv (by norm_num)).norm
  have hc2 : Continuous fun p : ℝ × Euc d => ‖fderiv ℝ (fderiv ℝ F) p‖ :=
    (hF1.continuous_fderiv one_ne_zero).norm
  set Q : Set (Euc d) := (WithLp.toLp 2) '' (Set.pi Set.univ fun _ : Fin d => Icc (0 : ℝ) 1) with hQ
  have hQc : IsCompact Q :=
    (isCompact_univ_pi fun _ => isCompact_Icc).image (PiLp.continuous_toLp 2 _)
  have hK : IsCompact ((Icc (0 : ℝ) 1) ×ˢ Q) := isCompact_Icc.prod hQc
  obtain ⟨B₀, hB₀⟩ := hK.exists_bound_of_continuousOn hc0.continuousOn
  obtain ⟨B₁, hB₁⟩ := hK.exists_bound_of_continuousOn hc1.continuousOn
  obtain ⟨B₂, hB₂⟩ := hK.exists_bound_of_continuousOn hc2.continuousOn
  refine ⟨max B₀ (max B₁ B₂), fun t ht y => ?_⟩
  -- reduce to the cube
  obtain ⟨y₀, hy₀, n, hyn⟩ : ∃ y₀ ∈ Q, ∃ n : Lattice d, y = y₀ + Lattice.toEuc n := by
    refine ⟨WithLp.toLp 2 fun i => y i - ⌊y i⌋, ⟨fun i => y i - ⌊y i⌋, fun i _ => ?_, rfl⟩,
      fun i => ⌊y i⌋, ?_⟩
    · exact ⟨sub_nonneg.2 (Int.floor_le _), by
        show y.ofLp i - ↑⌊y.ofLp i⌋ ≤ 1
        rw [Int.self_sub_floor]; exact (Int.fract_lt_one _).le⟩
    · ext i; simp [Lattice.toEuc]
  have hmem : (t, y₀) ∈ (Icc (0 : ℝ) 1) ×ˢ Q := ⟨ht, hy₀⟩
  have h1 : ‖F (t, y₀)‖ ≤ B₀ := by
    have := hB₀ _ hmem
    rwa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (F (t, y₀)))] at this
  have h2 : ‖fderiv ℝ F (t, y₀)‖ ≤ B₁ := by
    have := hB₁ _ hmem
    rwa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (fderiv ℝ F (t, y₀)))] at this
  have h3 : ‖fderiv ℝ (fderiv ℝ F) (t, y₀)‖ ≤ B₂ := by
    have := hB₂ _ hmem
    rwa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (fderiv ℝ (fderiv ℝ F) (t, y₀)))] at this
  have hp := hper t
  have hp1 : Torus.Per (fderiv ℝ (fun y' => F (t, y'))) := fun y n => q12_per_fderiv hp y n
  have e0 : F (t, y) = F (t, y₀) := by rw [hyn]; exact hp y₀ n
  have e1 : fderiv ℝ (fun y' => F (t, y')) y = fderiv ℝ (fun y' => F (t, y')) y₀ := by
    rw [hyn]; exact q12_per_fderiv hp y₀ n
  have e2 : fderiv ℝ (fderiv ℝ (fun y' => F (t, y'))) y =
      fderiv ℝ (fderiv ℝ (fun y' => F (t, y'))) y₀ := by
    rw [hyn]; exact q12_per_fderiv hp1 y₀ n
  have hs := q12_slice_bounds hF t y₀
  refine ⟨?_, ?_, ?_⟩
  · rw [e0]; exact h1.trans (le_max_left _ _)
  · rw [e1]; exact (hs.1.trans h2).trans ((le_max_left _ _).trans (le_max_right _ _))
  · rw [e2]; exact (hs.2.trans h3).trans ((le_max_right _ _).trans (le_max_right _ _))

end HRS.Uniform.Q12

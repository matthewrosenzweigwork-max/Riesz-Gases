import HRS.MS.R26T8AP11g7

/-!
# S8.2 T8A P11g (part 8): explicit `y`-uniform pole bound for the source
For `Q` conormal and `ρ` Gaussian: `|divSource ρ Q u y| ≤ K A jb(y)^M exp(-c'‖u‖²) (1 + ‖u-y‖^(-e))`, `0 < e < d`, `K, c'` independent of `Q, A, y, u`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_g8_pow {r τ : ℝ} (hr : 0 < r) (hτ : 0 ≤ τ) : 1 + r ^ (-τ) ≤ 2 * (1 + r ^ (-(τ + 1))) := by
  have h1 : 0 ≤ r ^ (-(τ + 1)) := Real.rpow_nonneg hr.le _
  by_cases h : 1 ≤ r
  · have : r ^ (-τ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h (by linarith)
    linarith
  · push Not at h
    have : r ^ (-τ) ≤ r ^ (-(τ + 1)) := Real.rpow_le_rpow_of_exponent_ge hr h.le (by linarith)
    linarith

set_option maxHeartbeats 3200000 in
theorem r26t8a_g8_S_bound (hd : 2 ≤ d) (k b : ℕ) {M σ : ℝ} (hM : 0 ≤ M) (hσ : σ < d)
    {ρ : Euc d → ℝ} (hρ : ContDiff ℝ ∞ ρ) {Cρ c : ℝ} (hCρ : 0 ≤ Cρ) (hc : 0 < c)
    (hb1 : ∀ x, |ρ x| ≤ Cρ * Real.exp (-c * ‖x‖ ^ 2))
    (hb2 : ∀ x, ‖fderiv ℝ ρ x‖ ≤ Cρ * Real.exp (-c * ‖x‖ ^ 2)) :
    ∃ e K c' : ℝ, 0 < e ∧ e < d ∧ 0 ≤ K ∧ 0 < c' ∧ ∀ A : ℝ, 0 ≤ A → ∀ Q : Euc d → Euc d → ℝ,
      Conormal (k + 2) b M (σ - 2) A Q → ∀ y u : Euc d, u ≠ y →
        |r26t8a_divSource ρ Q u y| ≤
          K * A * jbracket y ^ M * Real.exp (-c' * ‖u‖ ^ 2) * (1 + ‖u - y‖ ^ (-e)) := by
  obtain ⟨chi, hchi⟩ := r26t8a_p10a_exists_cutoff d
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = max (σ - 1) 0 := ⟨_, rfl⟩
  have hm0 : 0 ≤ m := by rw [hm]; exact le_max_right _ _
  have hm1 : σ - 1 ≤ m := by rw [hm]; exact le_max_left _ _
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hmd : m < d - 1 := by rw [hm]; exact max_lt (by linarith) (by linarith)
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = (d - 1 - m) / 2 := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; linarith
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = m + η := ⟨_, rfl⟩
  have hτ0 : 0 < τ := by rw [hτ]; linarith
  have hτd : τ + 1 < d := by rw [hτ, hη] at *; linarith
  obtain ⟨K1, hK10, hK1⟩ := r26t8a_p10a_Tj_bound hchi (k := k) (b := b) (M := M) (σ := σ - 2) hM
    (j := 1) (by omega) (e := τ) (by rw [hτ]; push_cast; linarith) hτ0
  obtain ⟨K2, hK20, hK2⟩ := r26t8a_p10a_Tj_bound hchi (k := k) (b := b) (M := M) (σ := σ - 2) hM
    (j := 2) (by omega) (e := τ + 1) (by rw [hτ]; push_cast; linarith) (by linarith)
  obtain ⟨Cp, hCp0, hCp⟩ := r26t8a_p10a_poly_gauss M hc
  have hNR := norm_nonneg (r26t8a_Rz d)
  refine ⟨τ + 1, d * (Cρ * ‖r26t8a_Rz d‖ * K2 * Cp + 2 * (Cρ * K1 * Cp)), c / 2, by linarith, hτd,
    by positivity, by positivity, ?_⟩
  intro A hA Q hQ y u hu
  set f : Euc d → ℝ := fun v => Q v y with hf
  have hopen : IsOpen ({y}ᶜ : Set (Euc d)) := isClosed_singleton.isOpen_compl
  have hf2 : ContDiffOn ℝ 2 f {y}ᶜ := by
    have hg : ContDiff ℝ ((k + 2 : ℕ) : WithTop ℕ∞) (fun v : Euc d => (v, y)) :=
      contDiff_id.prodMk contDiff_const
    have hmaps : Set.MapsTo (fun v : Euc d => (v, y)) {y}ᶜ {p : Euc d × Euc d | p.1 ≠ p.2} :=
      fun v hv => by simpa using hv
    have := hQ.1.comp hg.contDiffOn hmaps
    exact this.of_le (by exact_mod_cast (by omega : 2 ≤ k + 2))
  have hDf : ContDiffOn ℝ 1 (fderiv ℝ f) {y}ᶜ :=
    hf2.fderiv_of_isOpen hopen (by rw [one_add_one_eq_two])
  have hgrad : ContDiffOn ℝ 1 (gradient f) {y}ᶜ := by
    rw [r26t8a_gradient_eq_Rz]
    exact (r26t8a_Rz d).contDiff.comp_contDiffOn hDf
  have hmem : {y}ᶜ ∈ 𝓝 u := hopen.mem_nhds (by simpa using hu)
  have hdf : DifferentiableAt ℝ (gradient f) u := (hgrad.contDiffAt hmem).differentiableAt (by simp)
  have hDD : DifferentiableAt ℝ (fderiv ℝ f) u := (hDf.contDiffAt hmem).differentiableAt (by simp)
  have hdρ : DifferentiableAt ℝ ρ u := (hρ.differentiable (by simp)) u
  have hfat : ContDiffAt ℝ 2 (fun v => Q v y) u := hf2.contDiffAt hmem
  rw [← r26t8a_p10a_divh_eq (hρ.differentiable (by simp)) hfat]
  have hn : 0 < ‖u - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hu)
  have hT1 := hK1 A hA hQ y u hu
  rw [norm_iteratedFDeriv_one] at hT1
  have hT2 := hK2 A hA hQ y u hu
  rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one] at hT2
  have hp := r26t8a_g8_pow hn hτ0.le
  have hjy : 0 ≤ jbracket y ^ M := Real.rpow_nonneg (s83_jb_pos y).le _
  have hq0 : 0 ≤ 1 + ‖u - y‖ ^ (-(τ + 1)) := by
    have := Real.rpow_nonneg (norm_nonneg (u - y)) (-(τ + 1)); linarith
  have hpu : 0 ≤ (1 + ‖u‖) ^ M := Real.rpow_nonneg (by positivity) _
  have hE := hCp ‖u‖ (norm_nonneg _)
  set J : ℝ := jbracket y ^ M with hJ
  set P : ℝ := (1 + ‖u‖) ^ M with hP
  set q : ℝ := 1 + ‖u - y‖ ^ (-(τ + 1)) with hq
  set E : ℝ := Real.exp (-c * ‖u‖ ^ 2) with hEd
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hDρu := hb2 u
  have hρu := hb1 u
  -- pointwise bound of the norm of the derivative of the vector field
  have hD2 : ‖fderiv ℝ ρ u‖ * ‖fderiv ℝ f u‖ ≤ (Cρ * E) * (K1 * A * J * P * (2 * q)) :=
    mul_le_mul hDρu (hT1.trans (by
      have : 0 ≤ K1 * A * J * P := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hp this])) (norm_nonneg _) (by positivity)
  have hD1 : |ρ u| * (‖r26t8a_Rz d‖ * ‖fderiv ℝ (fderiv ℝ f) u‖) ≤
      (Cρ * E) * (‖r26t8a_Rz d‖ * (K2 * A * J * P * q)) :=
    mul_le_mul hρu (mul_le_mul_of_nonneg_left hT2 hNR) (by positivity) (by positivity)
  have hfd : ‖fderiv ℝ (fun w => ρ w • gradient f w) u‖ ≤
      |ρ u| * (‖r26t8a_Rz d‖ * ‖fderiv ℝ (fderiv ℝ f) u‖) + ‖fderiv ℝ ρ u‖ * ‖fderiv ℝ f u‖ := by
    rw [fderiv_fun_smul hdρ hdf]
    refine (norm_add_le (ρ u • fderiv ℝ (gradient f) u) ((fderiv ℝ ρ u).smulRight (gradient f u))).trans ?_
    have e1 : ‖ρ u • fderiv ℝ (gradient f) u‖ ≤ |ρ u| * (‖r26t8a_Rz d‖ * ‖fderiv ℝ (fderiv ℝ f) u‖) := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (r26t8a_fderiv_gradient_le f u hDD) (abs_nonneg _)
    have e2 : ‖(fderiv ℝ ρ u).smulRight (gradient f u)‖ ≤ ‖fderiv ℝ ρ u‖ * ‖fderiv ℝ f u‖ := by
      rw [ContinuousLinearMap.norm_smulRight_apply, r26t8a_norm_gradient]
    linarith
  have hdiv := r26t8a_divh_le (fun w => ρ w • gradient f w) u
  have hfin : |r26t8a_divh (fun w => ρ w • gradient f w) u| ≤
      d * ((Cρ * E) * (‖r26t8a_Rz d‖ * (K2 * A * J * P * q)) + (Cρ * E) * (K1 * A * J * P * (2 * q))) :=
    hdiv.trans (mul_le_mul_of_nonneg_left (hfd.trans (add_le_add hD1 hD2)) (by positivity))
  refine hfin.trans ?_
  -- Gaussian absorption
  have hPE : P * E ≤ Cp * Real.exp (-(c / 2) * ‖u‖ ^ 2) := by
    rw [hP, hEd, mul_comm]; exact hCp ‖u‖ (norm_nonneg _) |> fun h => by linarith [h]
  have hconst : 0 ≤ A * J * q := by positivity
  calc d * ((Cρ * E) * (‖r26t8a_Rz d‖ * (K2 * A * J * P * q)) + (Cρ * E) * (K1 * A * J * P * (2 * q)))
      = d * (Cρ * ‖r26t8a_Rz d‖ * K2 + 2 * (Cρ * K1)) * (A * J * q) * (P * E) := by ring
    _ ≤ d * (Cρ * ‖r26t8a_Rz d‖ * K2 + 2 * (Cρ * K1)) * (A * J * q) * (Cp * Real.exp (-(c / 2) * ‖u‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hPE (by positivity)
    _ = _ := by rw [hq]; ring

end HRS.MS.R26T8A

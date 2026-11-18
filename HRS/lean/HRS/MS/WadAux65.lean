import HRS.MS.WadAux64

/-!
# S8.3, packet S8D-2, part 11: `L²(μ)` decay of `U_t` on `C_M`

`s8d_approx_pkg`: an approximating sequence `φ_n ∈ C_c^∞` of `f ∈ C_M` with a common weighted bound
`|φ_n|, |U_t φ_n| ≤ B⟨x⟩^M` and pointwise convergence.
`s8d_l2_classical_mu`: `s8d_l2_classical` in the form with `μ = withDensityReal ρβ`.
`s8d_var_eq`: `∫ (X - ∫X)² dμ = ∫ X² dμ - (∫ X dμ)²`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8d_approx_pkg {a β T M : ℝ} {ρβ : Euc d → ℝ} (H : S85Hyp d a β T M ρβ) {t : ℝ} (ht0 : 0 ≤ t)
    (htT : t ≤ T) {f : Euc d → ℝ} (hf : MemCM M f) :
    ∃ (φ : ℕ → Euc d → ℝ) (B : ℝ), 0 ≤ B ∧ S85Approx M f φ ∧
      (∀ n x, |φ n x| ≤ B * jbracket x ^ M) ∧
      (∀ x, Tendsto (fun n => φ n x) atTop (𝓝 (f x))) ∧
      (∀ n x, |s85_Ucc a β ρβ t (φ n) x| ≤ B * jbracket x ^ M) ∧
      (∀ x, Tendsto (fun n => s85_Ucc a β ρβ t (φ n) x) atTop (𝓝 (s85_Ulim a β ρβ M t f x))) := by
  obtain ⟨hd, ha, hβ, hT, hM, hρ⟩ := id H
  obtain ⟨K, hK0, hK⟩ := s85_Ucc_bound hd ha hβ hT hM hρ
  obtain ⟨φ, hφ⟩ := s85_exists_approx hM hf
  have hφ' := hφ
  obtain ⟨hcc, C, hC0, hC⟩ := hφ'
  set Φf : ℝ := (weightedSupE 0 (-M) f).toReal with hΦf
  have hwf : Wt M Φf f := s83_wt_of_memCM hf
  have hΦf0 : 0 ≤ Φf := hwf.nonneg
  have h0cc : S85Cc (fun _ : Euc d => (0 : ℝ)) := ⟨contDiff_const, by
    have : HasCompactSupport (0 : Euc d → ℝ) := HasCompactSupport.zero
    exact this⟩
  have hφb : ∀ n x, |φ n x| ≤ (Φf + C) * jbracket x ^ M := fun n x => by
    have h1 := hC n x
    have h2 := hwf x
    rw [Real.norm_eq_abs] at h1 h2
    have hj := Real.rpow_nonneg (s83_jb_pos x).le M
    have hen : C / ((n : ℝ) + 1) ≤ C := div_le_self hC0 (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])
    have h3 : |φ n x| ≤ |φ n x - f x| + |f x| := by
      have := abs_add_le (φ n x - f x) (f x)
      simpa using this
    nlinarith [mul_le_mul_of_nonneg_right hen hj]
  have hUb : ∀ n x, |s85_Ucc a β ρβ t (φ n) x| ≤ K * (Φf + C) * jbracket x ^ M := fun n x => by
    have := hK ht0 htT (hcc n) h0cc (Φ := Φf + C) (fun y => by simpa using hφb n y) x
    rw [s8d_Ucc_zero hd ha hβ hρ ht0, sub_zero] at this
    exact this
  refine ⟨φ, max (Φf + C) (K * (Φf + C)), le_max_of_le_left (by positivity), hφ, fun n x => ?_, ?_, fun n x => ?_,
    fun x => s85_Ulim_spec H ht0 htT hφ x⟩
  · exact (hφb n x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (s83_jb_pos x).le _))
  · intro x
    have he : Tendsto (fun n : ℕ => C / ((n : ℝ) + 1) * jbracket x ^ M) atTop (𝓝 0) := by
      have := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul C).mul_const (jbracket x ^ M)
      simpa [div_eq_mul_inv] using this
    have h0 : Tendsto (fun n => φ n x - f x) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun n => ?_) he
      exact hC n x
    have := h0.add_const (f x)
    simpa using this
  · exact (hUb n x).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (s83_jb_pos x).le _))

theorem s8d_var_eq {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {X : Euc d → ℝ} (h1 : Integrable X μ)
    (h2 : Integrable (fun x => X x ^ 2) μ) :
    ∫ x, (X x - ∫ y, X y ∂μ) ^ 2 ∂μ = ∫ x, X x ^ 2 ∂μ - (∫ x, X x ∂μ) ^ 2 := by
  set c : ℝ := ∫ y, X y ∂μ with hc
  have e : ∀ x, (X x - c) ^ 2 = X x ^ 2 + (-(2 * c) * X x + c ^ 2) := fun x => by ring
  have i3 : Integrable (fun x => -(2 * c) * X x + c ^ 2) μ :=
    (h1.const_mul (-(2 * c))).add (integrable_const (c ^ 2))
  simp_rw [e]
  rw [integral_add h2 i3, integral_add (h1.const_mul (-(2 * c))) (integrable_const (c ^ 2)),
    integral_const_mul, integral_const]
  simp
  ring

theorem s8d_l2_classical_mu (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) :
    ∃ lam C0 : ℝ, 0 < lam ∧ 1 ≤ C0 ∧ ∀ {t : ℝ} {φ : Euc d → ℝ} {w : ℝ → Euc d → ℝ}, 0 ≤ t →
      IsClassicalAdjointW (critCoeff d a β ρβ) t φ w →
      ∫ x, (w 0 x - ∫ y, w 0 y ∂(HRS.Whole.withDensityReal ρβ)) ^ 2 ∂(HRS.Whole.withDensityReal ρβ) ≤
        (C0 * Real.exp (-lam * t)) ^ 2 *
          ∫ x, (φ x - ∫ y, φ y ∂(HRS.Whole.withDensityReal ρβ)) ^ 2 ∂(HRS.Whole.withDensityReal ρβ) := by
  obtain ⟨lam, C0, hlam, hC0, hL⟩ := s8d_l2_classical hd ha hβ hρ
  refine ⟨lam, C0, hlam, hC0, fun {t φ w} ht hw => ?_⟩
  have hP : HRS.Whole.IsProbDensity ρβ := hρ.1.1
  have key := hL ht hw
  have conv : ∀ (u : Euc d → ℝ), ∫ x, (u x - ∫ y, u y ∂(HRS.Whole.withDensityReal ρβ)) ^ 2
      ∂(HRS.Whole.withDensityReal ρβ) = ∫ x, ρβ x * (u x - ∫ y, u y * ρβ y) ^ 2 := fun u => by
    have hin : ∫ y, u y ∂(HRS.Whole.withDensityReal ρβ) = ∫ y, u y * ρβ y := by
      rw [s8d_int_wdr ρβ hP.measurable hP.nonneg]
      congr 1
      funext y; ring
    rw [hin, s8d_int_wdr ρβ hP.measurable hP.nonneg]
  rw [conv (w 0), conv φ]
  exact key

end HRS.MS.Wad

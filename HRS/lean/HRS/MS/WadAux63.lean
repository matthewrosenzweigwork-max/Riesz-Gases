import HRS.MS.WadAux62

/-!
# S8.3, packet S8D-2, part 9: mean preservation `μ(U_t f) = μ(f)`

`s8d_mean_Ucc`: for `φ ∈ C_c^∞`, `∫ U_t φ dμ = ∫ φ dμ` (the projected solution `w_0 - μ(w_0) + μ(φ)` has mean `μ(φ)`).
`s8d_mean_U`: the same for the extension to `C_M` (dominated convergence along the approximating sequence).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8d_mean_Ucc (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) {t : ℝ} (ht : 0 ≤ t) {φ : Euc d → ℝ}
    (hφ : S85Cc φ) :
    ∫ x, s85_Ucc a β ρβ t φ x ∂(HRS.Whole.withDensityReal ρβ) =
      ∫ x, φ x ∂(HRS.Whole.withDensityReal ρβ) := by
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρβ) := s85_isProb hρ.1.1
  obtain ⟨w, hw⟩ := s85_exists_cl hd ha hβ hρ ht hφ
  obtain ⟨i1, -⟩ := s85_cl_int hd ha hβ hρ ht hw
  have e : ∀ x, s85_Ucc a β ρβ t φ x = w 0 x + (-(∫ z, w 0 z ∂(HRS.Whole.withDensityReal ρβ)) +
      HRS.Whole.pair (HRS.Whole.withDensityReal ρβ) φ) := fun x => by
    rw [s85_Ucc_eq hd ha hβ hρ ht hw x]; unfold s85_V; ring
  simp_rw [e]
  rw [integral_add i1 (integrable_const _), integral_const]
  simp [HRS.Whole.pair]

theorem s8d_Ucc_zero (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) {t : ℝ} (ht : 0 ≤ t) (x : Euc d) :
    s85_Ucc a β ρβ t (fun _ => (0 : ℝ)) x = 0 := by
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρβ) := s85_isProb hρ.1.1
  rw [s85_Ucc_eq hd ha hβ hρ ht (s8d_const_classical (critCoeff d a β ρβ) t 0) x]
  unfold s85_V
  simp [HRS.Whole.pair]

theorem s8d_mean_U {a β T M : ℝ} {ρβ : Euc d → ℝ} (H : S85Hyp d a β T M ρβ) {t : ℝ} (ht0 : 0 ≤ t)
    (htT : t ≤ T) {f : Euc d → ℝ} (hf : MemCM M f) :
    ∫ x, s85_Ulim a β ρβ M t f x ∂(HRS.Whole.withDensityReal ρβ) =
      ∫ x, f x ∂(HRS.Whole.withDensityReal ρβ) := by
  obtain ⟨hd, ha, hβ, hT, hM, hρ⟩ := id H
  have hP : HRS.Whole.IsProbDensity ρβ := hρ.1.1
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρβ) := s85_isProb hP
  have hg : s84_GaussReg ρβ := s84_thermal_gaussReg hd ha hβ hρ
  have hjint : Integrable (fun z : Euc d => jbracket z ^ M) (HRS.Whole.withDensityReal ρβ) :=
    s85_jb_integrable hP hg hM
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
  have hlim1 : Tendsto (fun n => ∫ x, s85_Ucc a β ρβ t (φ n) x ∂(HRS.Whole.withDensityReal ρβ)) atTop
      (𝓝 (∫ x, s85_Ulim a β ρβ M t f x ∂(HRS.Whole.withDensityReal ρβ))) := by
    refine tendsto_integral_of_dominated_convergence (fun x => K * (Φf + C) * jbracket x ^ M) ?_
      (hjint.const_mul _) (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · intro n
      exact (s85_Ucc_props hd ha hβ hT (M' := 0) le_rfl hρ ht0 htT (hcc n)).1.aestronglyMeasurable
    · rw [Real.norm_eq_abs]; exact hUb n x
    · exact s85_Ulim_spec H ht0 htT hφ x
  have hlim2 : Tendsto (fun n => ∫ x, φ n x ∂(HRS.Whole.withDensityReal ρβ)) atTop
      (𝓝 (∫ x, f x ∂(HRS.Whole.withDensityReal ρβ))) := by
    refine tendsto_integral_of_dominated_convergence (fun x => (Φf + C) * jbracket x ^ M) ?_
      (hjint.const_mul _) (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · intro n
      exact (hcc n).1.continuous.aestronglyMeasurable
    · rw [Real.norm_eq_abs]; exact hφb n x
    · have he : Tendsto (fun n : ℕ => C / ((n : ℝ) + 1) * jbracket x ^ M) atTop (𝓝 0) := by
        have := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul C).mul_const (jbracket x ^ M)
        simpa [div_eq_mul_inv] using this
      have h0 : Tendsto (fun n => φ n x - f x) atTop (𝓝 0) := by
        refine squeeze_zero_norm (fun n => ?_) he
        exact hC n x
      have := h0.add_const (f x)
      simpa using this
  have heq : ∀ n, ∫ x, s85_Ucc a β ρβ t (φ n) x ∂(HRS.Whole.withDensityReal ρβ) =
      ∫ x, φ n x ∂(HRS.Whole.withDensityReal ρβ) := fun n => s8d_mean_Ucc hd ha hβ hρ ht0 (hcc n)
  simp_rw [heq] at hlim1
  exact tendsto_nhds_unique hlim1 hlim2

end HRS.MS.Wad

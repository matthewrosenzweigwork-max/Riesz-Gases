import HRS.MS.WadAux65

/-!
# S8.3, packet S8D-2, part 12: `L²(μ)` exponential decay of `U_t` on `C_M`

`s8d_L2_decay`: there are `λ > 0`, `C₀ ≥ 1` with, for `t ∈ [0,T]` and `f ∈ C_M`,
`∫ (U_t f - μ(f))² dμ ≤ (C₀ e^{-λt})² ∫ f² dμ`.  (Classical case `s8d_l2_classical_mu`; the extension to `C_M` is
dominated convergence along the approximating sequence.)
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8d_jb_sq_integrable {ρ : Euc d → ℝ} (hP : HRS.Whole.IsProbDensity ρ) (hg : s84_GaussReg ρ) {M : ℝ}
    (hM : 0 ≤ M) : Integrable (fun x : Euc d => (jbracket x ^ M) ^ 2) (HRS.Whole.withDensityReal ρ) := by
  refine (s85_jb_integrable hP hg (M := 2 * M) (by positivity)).congr (Eventually.of_forall fun x => ?_)
  show jbracket x ^ (2 * M) = (jbracket x ^ M) ^ 2
  rw [← Real.rpow_natCast, ← Real.rpow_mul (s83_jb_pos x).le]
  congr 1; push_cast; ring

theorem s8d_L2_decay (hd : 2 ≤ d) {a β M : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) :
    ∃ lam C0 : ℝ, 0 < lam ∧ 1 ≤ C0 ∧ ∀ {T t : ℝ} {f : Euc d → ℝ}, S85Hyp d a β T M ρβ → 0 ≤ t → t ≤ T →
      MemCM M f →
      ∫ x, (s85_Ulim a β ρβ M t f x - ∫ y, f y ∂(HRS.Whole.withDensityReal ρβ)) ^ 2
          ∂(HRS.Whole.withDensityReal ρβ) ≤
        (C0 * Real.exp (-lam * t)) ^ 2 * ∫ x, f x ^ 2 ∂(HRS.Whole.withDensityReal ρβ) := by
  have hP : HRS.Whole.IsProbDensity ρβ := hρ.1.1
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρβ) := s85_isProb hP
  have hg : s84_GaussReg ρβ := s84_thermal_gaussReg hd ha hβ hρ
  obtain ⟨lam, C0, hlam, hC0, hL⟩ := s8d_l2_classical_mu hd ha hβ hρ
  refine ⟨lam, C0, hlam, hC0, fun {T t f} H ht0 htT hf => ?_⟩
  obtain ⟨-, -, -, hT, hM, -⟩ := id H
  have hjint : Integrable (fun z : Euc d => jbracket z ^ M) (HRS.Whole.withDensityReal ρβ) :=
    s85_jb_integrable hP hg hM
  have hj2 := s8d_jb_sq_integrable hP hg hM
  set mM : ℝ := ∫ z, jbracket z ^ M ∂(HRS.Whole.withDensityReal ρβ) with hmM
  have hmM0 : 0 ≤ mM := integral_nonneg fun z => Real.rpow_nonneg (s83_jb_pos z).le _
  obtain ⟨φ, B, hB0, hφ, hφb, hφl, hUb, hUl⟩ := s8d_approx_pkg H ht0 htT hf
  have hcc := hφ.1
  have hj1 : ∀ x : Euc d, 1 ≤ jbracket x ^ M := fun x => Real.one_le_rpow (s83_one_le_jb x) hM
  -- the means converge
  have hmeas : ∀ n, AEStronglyMeasurable (φ n) (HRS.Whole.withDensityReal ρβ) := fun n =>
    (hcc n).1.continuous.aestronglyMeasurable
  have hmean : Tendsto (fun n => ∫ x, φ n x ∂(HRS.Whole.withDensityReal ρβ)) atTop
      (𝓝 (∫ x, f x ∂(HRS.Whole.withDensityReal ρβ))) :=
    tendsto_integral_of_dominated_convergence (fun x => B * jbracket x ^ M) hmeas (hjint.const_mul _)
      (fun n => Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hφb n x)
      (Eventually.of_forall fun x => hφl x)
  have hmb : ∀ n, |∫ x, φ n x ∂(HRS.Whole.withDensityReal ρβ)| ≤ B * mM := fun n => by
    have := s85_abs_integral_le (μ := HRS.Whole.withDensityReal ρβ) (h := φ n)
      (bd := fun z => B * jbracket z ^ M) (hjint.const_mul B) (hφb n)
    rwa [integral_const_mul] at this
  -- left side
  have hLn : ∀ n, ∫ x, (s85_Ucc a β ρβ t (φ n) x - ∫ y, φ n y ∂(HRS.Whole.withDensityReal ρβ)) ^ 2
      ∂(HRS.Whole.withDensityReal ρβ) ≤
      (C0 * Real.exp (-lam * t)) ^ 2 * ∫ x, φ n x ^ 2 ∂(HRS.Whole.withDensityReal ρβ) := fun n => by
    obtain ⟨w, hw⟩ := s85_exists_cl hd ha hβ hρ ht0 (hcc n)
    obtain ⟨i1, iφ⟩ := s85_cl_int hd ha hβ hρ ht0 hw
    have e : ∀ x, s85_Ucc a β ρβ t (φ n) x - ∫ y, φ n y ∂(HRS.Whole.withDensityReal ρβ) =
        w 0 x - ∫ y, w 0 y ∂(HRS.Whole.withDensityReal ρβ) := fun x => by
      rw [s85_Ucc_eq hd ha hβ hρ ht0 hw x]; unfold s85_V HRS.Whole.pair; ring
    simp_rw [e]
    refine (hL ht0 hw).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    have hbφ : ∀ x, |φ n x| ≤ B * jbracket x ^ M := hφb n
    have iφ2 : Integrable (fun x => φ n x ^ 2) (HRS.Whole.withDensityReal ρβ) := by
      refine (hj2.const_mul (B ^ 2)).mono' ((hmeas n).pow 2) (Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      calc φ n x ^ 2 = |φ n x| ^ 2 := (sq_abs _).symm
        _ ≤ (B * jbracket x ^ M) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hbφ x) 2
        _ = B ^ 2 * (jbracket x ^ M) ^ 2 := by ring
    rw [s8d_var_eq iφ iφ2]
    nlinarith [sq_nonneg (∫ x, φ n x ∂(HRS.Whole.withDensityReal ρβ))]
  have hlimL : Tendsto (fun n => ∫ x, (s85_Ucc a β ρβ t (φ n) x - ∫ y, φ n y ∂(HRS.Whole.withDensityReal ρβ)) ^ 2
      ∂(HRS.Whole.withDensityReal ρβ)) atTop
      (𝓝 (∫ x, (s85_Ulim a β ρβ M t f x - ∫ y, f y ∂(HRS.Whole.withDensityReal ρβ)) ^ 2
        ∂(HRS.Whole.withDensityReal ρβ))) := by
    refine tendsto_integral_of_dominated_convergence (fun x => (B * (1 + mM) * jbracket x ^ M) ^ 2) ?_
      ((hj2.const_mul ((B * (1 + mM)) ^ 2)).congr (Eventually.of_forall fun x => by simp only; ring))
      (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · intro n
      exact (((s85_Ucc_props hd ha hβ hT (M' := 0) le_rfl hρ ht0 htT (hcc n)).1.sub continuous_const).pow 2).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h1 := hUb n x
      have h2 := hmb n
      have h3 : |s85_Ucc a β ρβ t (φ n) x - ∫ y, φ n y ∂(HRS.Whole.withDensityReal ρβ)| ≤
          B * (1 + mM) * jbracket x ^ M := by
        refine (abs_sub _ _).trans ?_
        have := hj1 x
        nlinarith [mul_nonneg hB0 hmM0]
      calc _ = |s85_Ucc a β ρβ t (φ n) x - ∫ y, φ n y ∂(HRS.Whole.withDensityReal ρβ)| ^ 2 := (sq_abs _).symm
        _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) h3 2
    · exact ((hUl x).sub hmean).pow 2
  have hlimR : Tendsto (fun n => ∫ x, φ n x ^ 2 ∂(HRS.Whole.withDensityReal ρβ)) atTop
      (𝓝 (∫ x, f x ^ 2 ∂(HRS.Whole.withDensityReal ρβ))) := by
    refine tendsto_integral_of_dominated_convergence (fun x => (B * jbracket x ^ M) ^ 2) ?_
      (hj2.const_mul (B ^ 2) |>.congr (Eventually.of_forall fun x => by simp only; ring))
      (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · intro n
      exact ((hcc n).1.continuous.pow 2).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      calc φ n x ^ 2 = |φ n x| ^ 2 := (sq_abs _).symm
        _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) (hφb n x) 2
    · exact (hφl x).pow 2
  exact le_of_tendsto_of_tendsto' hlimL (hlimR.const_mul _) hLn

end HRS.MS.Wad

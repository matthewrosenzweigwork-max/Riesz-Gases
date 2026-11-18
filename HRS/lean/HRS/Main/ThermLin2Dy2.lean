import HRS.Main.ThermLin2Dy1

/-!
# THERMLIN 2, packet `Dy`, part 2: interval integrability of the Duhamel integrand (copy of the proof of
`PDE.MFAdjoint.duhamel_integral` / `duhamel_coeff`, keeping the integrability that is proved there)
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.MFAdjoint

variable {d : ℕ}

section Tl2DyDuhamel

variable {s : ℝ} {R : Regime} {MB Λ VB : ℝ} {D : DynData d} {ν₀ T : ℝ} {ρ : Torus d → ℝ}

theorem tl2dy_duhamel_int (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {m : ℕ} (hm : 1 ≤ m)
    (hA : AdjointData s m R MB Λ VB D ν₀ T (fun _ => ρ))
    (hA2 : AdjointData s (m + 2) R MB Λ VB D ν₀ T (fun _ => ρ))
    {t : ℝ} (htT : t ≤ T) (F G : ℝ → Coeff d)
    (hF1 : ∀ σ ∈ Set.Icc (0 : ℝ) t, MemHs ((m + 2 : ℕ) : ℝ) (F σ))
    (hFc : ContinuousInHs (m : ℝ) F t)
    (hFd : ∀ σ ∈ Set.Icc (0 : ℝ) t, Tendsto (fun σ' => hsNorm m (fun k =>
      (F σ' k - F σ k) / ((σ' - σ : ℝ) : ℂ) - G σ k)) (𝓝[Set.Icc 0 t \ {σ}] σ) (𝓝 0))
    (hG : ∀ σ ∈ Set.Icc (0 : ℝ) t, MemHs m (G σ))
    (hL : ∀ σ ∈ Set.Icc (0 : ℝ) t, MemHs m (forwardGen D ρ (F σ)))
    (M : ℝ) (hGM : ∀ σ ∈ Set.Icc (0 : ℝ) t, hsNorm m (G σ) ≤ M)
    (hLM : ∀ σ ∈ Set.Icc (0 : ℝ) t, hsNorm m (forwardGen D ρ (F σ)) ≤ M)
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ : τ ≤ t) (k : Lattice d) :
    IntervalIntegrable (fun σ => frozenCoeff D ρ m (G σ - forwardGen D ρ (F σ)) (τ - σ) k) volume 0 τ := by
  have hT := hA.hT
  have hmR : (m : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by push_cast; linarith
  have hFm : ∀ σ ∈ Set.Icc (0 : ℝ) t, MemHs (m : ℝ) (F σ) := fun σ hσ => hFc.1 σ hσ
  have h0t : (0 : ℝ) ∈ Set.Icc (0 : ℝ) t := ⟨le_rfl, hτ0.trans hτ⟩
  have hτt : τ ∈ Set.Icc (0 : ℝ) t := ⟨hτ0, hτ⟩
  rcases hτ0.eq_or_lt with h0 | hpos
  · subst h0
    exact IntervalIntegrable.refl
  have hderiv : ∀ x ∈ Set.Ioo 0 τ, HasDerivWithinAt (fun σ' => frozenCoeff D ρ m (F σ') (τ - σ') k)
      (frozenCoeff D ρ m (G x - forwardGen D ρ (F x)) (τ - x) k) (Set.Ioi x) x :=
    fun x hx => duhamel_hasDeriv hd hs0 hsd hm hA hA2 htT F G hF1 hFd hG hL hτ hx k
  have hcont := duhamel_continuousOn hd hs0 hsd hm hA htT F hFc hτ k
  -- integrability of the derivative
  obtain ⟨K, hK, hKb⟩ := frozen_coeff_bound hd hs0 hsd hm hA
  have hint : IntervalIntegrable
      (fun σ => frozenCoeff D ρ m (G σ - forwardGen D ρ (F σ)) (τ - σ) k) volume 0 τ := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hpos.le]
    set f : ℝ → ℂ := fun σ' => frozenCoeff D ρ m (F σ') (τ - σ') k with hf
    have hφ : IntegrableOn (fun x => derivWithin f (Set.Ici x) x) (Set.Ioo 0 τ) := by
      refine Measure.integrableOn_of_bounded (M := K * (M + M)) (by simp)
        (measurable_derivWithin_Ici f).aestronglyMeasurable ?_
      refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun x hx => ?_)
      have hxt : x ∈ Set.Icc (0 : ℝ) t := ⟨hx.1.le, hx.2.le.trans hτ⟩
      rw [((hasDerivWithinAt_Ioi_iff_Ici.1 (hderiv x hx))).derivWithin (uniqueDiffWithinAt_Ici x)]
      have hEm := memHs_sub (hG x hxt) (hL x hxt)
      have hx' : τ - x ∈ Set.Icc (0 : ℝ) T := ⟨by linarith [hx.2], by linarith [hx.1, htT, hτ]⟩
      refine ((hKb _ hEm (τ - x) hx').2 k).trans (mul_le_mul_of_nonneg_left ?_ hK)
      exact (hsNorm_sub_le_add (hG x hxt) (hL x hxt)).trans (add_le_add (hGM x hxt) (hLM x hxt))
    refine hφ.congr_fun (fun x hx => ?_) measurableSet_Ioo
    exact ((hasDerivWithinAt_Ioi_iff_Ici.1 (hderiv x hx))).derivWithin (uniqueDiffWithinAt_Ici x)
  exact hint


end Tl2DyDuhamel

theorem tl2dy_duhamel_coeff_int (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (j : ℕ) (hj : 3 ≤ j) (R R' : Regime)
    (MB Λ VB MB' Λ' VB' : ℝ) (D : DynData d) (ν₀ ν₀' T : ℝ) (μ : ℝ → Torus d → ℝ) (ρβ : Torus d → ℝ)
    (hA : AdjointData s j R MB Λ VB D ν₀ T μ) (hAβ : AdjointData s j R' MB' Λ' VB' D ν₀' T (fun _ => ρβ))
    (hν : 0 < D.invβ) (φc : Coeff d) (hφ : MemHs j φc) {t : ℝ} (ht : t ∈ Set.Ioc 0 T) (k : Lattice d) {τ : ℝ}
    (hτ : τ ∈ Set.Icc 0 t) :
    IntervalIntegrable (fun σ => frozenCoeff D ρβ (j - 2)
        (forwardGen D (μ (t - σ)) (propagatorCoeff D μ j t φc σ) - forwardGen D ρβ (propagatorCoeff D μ j t φc σ)) (τ - σ) k) volume 0 τ := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 2 := ⟨j - 2, by omega⟩
  have hm : 1 ≤ m := by omega
  have hjm : m + 2 - 2 = m := by omega
  rw [hjm]
  have hAm := StabAux.adjointData_mono (by omega : m ≤ m + 2) hAβ
  have hAμm := StabAux.adjointData_mono (by omega : m ≤ m + 2) hA
  obtain ⟨C, -, hspec⟩ := propagatorCoeff_spec hd s hs0 hsd (m + 2) (by omega) R MB Λ VB
  obtain ⟨hF, hw, hb⟩ := hspec D ν₀ T μ hA t ht φc hφ
  have hcast : ((m + 2 : ℕ) : ℝ) - 2 = m := by push_cast; ring
  have hmR : (m : ℝ) < ((m + 2 : ℕ) : ℝ) := by push_cast; linarith
  have hFc : ContinuousInHs (m : ℝ) (propagatorCoeff D μ ((m + 2 : ℕ) : ℝ) t φc) t :=
    forward_strong_continuity _ t _ hw _ hmR
  obtain ⟨-, htr⟩ := adjoint_torus_time_regularity hd s hs0 hsd (m + 2) (by omega) R MB Λ VB D ν₀ T
    μ hA t ht φc hφ
  rw [hcast] at htr
  -- bounds
  obtain ⟨c1, hc1, hgen1⟩ := forwardGen_hsNorm_le hd hs0 hsd m MB Λ VB D hA.hs hA.hM
    (hAμm.hV)
  obtain ⟨c2, hc2, hgen2⟩ := forwardGen_hsNorm_le hd hs0 hsd m MB' Λ' VB' D hAβ.hs hAβ.hM
    (hAm.hV)
  have hr0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, ht.1.le.trans ht.2⟩
  set lam := R.lambdaM C ν₀ (thetaOrder d s) with hlam
  set B : ℝ := Real.exp (|lam| * t) * hsNorm ((m + 2 : ℕ) : ℝ) φc with hBdef
  have hB : ∀ σ ∈ Set.Icc (0 : ℝ) t, hsNorm ((m + 2 : ℕ) : ℝ) (propagatorCoeff D μ ((m + 2 : ℕ) : ℝ) t φc σ) ≤ B := by
    intro σ hσ
    refine (hb σ hσ).trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (hsNorm_nonneg' _ _))
    have h3 := le_abs_self lam
    have h4 := abs_nonneg lam
    nlinarith [hσ.1, hσ.2]
  have hrT : ∀ σ ∈ Set.Icc (0 : ℝ) t, t - σ ∈ Set.Icc (0 : ℝ) T := fun σ hσ =>
    ⟨by linarith [hσ.2], by linarith [hσ.1, ht.2]⟩
  have hG1 : ∀ σ ∈ Set.Icc (0 : ℝ) t,
      MemHs (m : ℝ) (forwardGen D (μ (t - σ)) (propagatorCoeff D μ ((m + 2 : ℕ) : ℝ) t φc σ)) ∧
      hsNorm (m : ℝ) (forwardGen D (μ (t - σ)) (propagatorCoeff D μ ((m + 2 : ℕ) : ℝ) t φc σ)) ≤ c1 * B := by
    intro σ hσ
    have hr := hrT σ hσ
    obtain ⟨h1, h2⟩ := hgen1 (μ (t - σ)) (hAμm.hμ.prob _ hr) (hAμm.hμ.smooth _ hr) (hAμm.hμ.bound _ hr)
      _ (hw.1 σ hσ)
    exact ⟨h1, h2.trans (mul_le_mul_of_nonneg_left (hB σ hσ) hc1)⟩
  have hG2 : ∀ σ ∈ Set.Icc (0 : ℝ) t,
      MemHs (m : ℝ) (forwardGen D ρβ (propagatorCoeff D μ ((m + 2 : ℕ) : ℝ) t φc σ)) ∧
      hsNorm (m : ℝ) (forwardGen D ρβ (propagatorCoeff D μ ((m + 2 : ℕ) : ℝ) t φc σ)) ≤ c2 * B := by
    intro σ hσ
    obtain ⟨h1, h2⟩ := hgen2 ρβ (hAm.hμ.prob _ hr0) (hAm.hμ.smooth _ hr0) (hAm.hμ.bound _ hr0)
      _ (hw.1 σ hσ)
    exact ⟨h1, h2.trans (mul_le_mul_of_nonneg_left (hB σ hσ) hc2)⟩
  have hF0 : propagatorCoeff D μ ((m + 2 : ℕ) : ℝ) t φc 0 = φc := by
    funext k'
    simpa using hF.eq k' 0 ⟨le_rfl, ht.1.le⟩
  exact tl2dy_duhamel_int hd hs0 hsd hm hAm hAβ (t := t) ht.2
    (propagatorCoeff D μ ((m + 2 : ℕ) : ℝ) t φc)
    (fun σ => forwardGen D (μ (t - σ)) (propagatorCoeff D μ ((m + 2 : ℕ) : ℝ) t φc σ))
    (fun σ hσ => hw.1 σ hσ) hFc htr (fun σ hσ => (hG1 σ hσ).1) (fun σ hσ => (hG2 σ hσ).1)
    (max (c1 * B) (c2 * B)) (fun σ hσ => (hG1 σ hσ).2.trans (le_max_left _ _))
    (fun σ hσ => (hG2 σ hσ).2.trans (le_max_right _ _)) hτ.1 hτ.2 k


end HRS.PDE.MFAdjoint

namespace HRS.ThermLin.Plan2

variable {d : ℕ}

open HRS.PDE HRS.PDE.MFAdjoint in
/-- The moving-path adjoint data of the prepared data `S` at the level `j` (first lines of `thermlin_dyson_coeff`). -/
theorem tl2dy_moving (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (j : ℕ) (hj : (d : ℝ) / 2 + 4 < j) :
    ∃ (R : Regime) (Λ : ℝ), ∀ t : ℝ, 0 < t →
      AdjointData S.s j R 1 Λ (Torus.cbNorm (j + 3) S.V) S.dyn S.β⁻¹ t S.ρ := by
  obtain ⟨hsm, hpos⟩ := HRS.ThermLin.thermlin_thermal_smooth_pos S h
  have hd2 : 2 ≤ d := S.hd
  have htr := HRS.T25.t25_traj S
  obtain ⟨K, hK⟩ : ∃ K : ℕ, 2 * j + 4 * d + 20 ≤ K := ⟨2 * j + 4 * d + 20, le_rfl⟩
  have hK6 : (d : ℝ) / 2 + 6 < K := by
    have : ((2 * j + 4 * d + 20 : ℕ) : ℝ) ≤ K := by exact_mod_cast hK
    push_cast at this
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨ρc, hρc, hρ⟩ := S.hρ K hK6
  have H := Q40b.q40b_finiteRegHyp htr hK6
  obtain ⟨R, Λ, Λ₀, c₀, Cd, κ, hc₀, hκ, hall⟩ :=
    finiteReg_hypotheses (by omega) S.s S.β S.β K S.V S.ρ0 H j hj hK
  obtain ⟨HF, hAD, -⟩ := hall S.β ⟨le_rfl, le_rfl⟩ ρc hρc ρβ h
    (HRS.StaticLimitAux.continuous_of_smooth hsm) hpos
  refine ⟨R, Λ, fun t ht => ?_⟩
  have := hAD t ht
  rw [hρ] at this
  exact this

open HRS.PDE HRS.PDE.MFAdjoint in
/-- Interval integrability of the Duhamel integrand of `thermlin_dyson_coeff`. -/
theorem tl2dy_dyson_int (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (j : ℕ) (hj : (d : ℝ) / 2 + 4 < j)
    (φc : Coeff d) (hφ : MemHs (j : ℝ) φc) {t : ℝ} (ht : 0 < t) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) t)
    (k : Lattice d) :
    IntervalIntegrable (fun σ => frozenCoeff S.dyn ρβ (j - 2)
      (forwardGen S.dyn (S.ρ (t - σ)) (propagatorCoeff S.dyn S.ρ j t φc σ) -
        forwardGen S.dyn ρβ (propagatorCoeff S.dyn S.ρ j t φc σ)) (τ - σ) k) volume 0 τ := by
  obtain ⟨hsm, hpos⟩ := HRS.ThermLin.thermlin_thermal_smooth_pos S h
  have hd2 : 2 ≤ d := S.hd
  have htr := HRS.T25.t25_traj S
  obtain ⟨K, hK⟩ : ∃ K : ℕ, 2 * j + 4 * d + 20 ≤ K := ⟨2 * j + 4 * d + 20, le_rfl⟩
  have hK6 : (d : ℝ) / 2 + 6 < K := by
    have : ((2 * j + 4 * d + 20 : ℕ) : ℝ) ≤ K := by exact_mod_cast hK
    push_cast at this
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨ρc, hρc, hρ⟩ := S.hρ K hK6
  have H := Q40b.q40b_finiteRegHyp htr hK6
  obtain ⟨R, Λ, Λ₀, c₀, Cd, κ, hc₀, hκ, hall⟩ :=
    finiteReg_hypotheses (by omega) S.s S.β S.β K S.V S.ρ0 H j hj hK
  obtain ⟨HF, hAD, -⟩ := hall S.β ⟨le_rfl, le_rfl⟩ ρc hρc ρβ h
    (HRS.StaticLimitAux.continuous_of_smooth hsm) hpos
  have hAt := hAD t ht
  have h3 := ClassicalPart.three_le_mStar d
  have hj3 : 3 ≤ j := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    have : (4 : ℝ) < j := by linarith
    have : 4 < j := by exact_mod_cast this
    omega
  have hAβ := adjointData_frozen_level j (HF.mono (by omega : j + 3 ≤ j + mStar d + 2)) 0 t ht
  have := tl2dy_duhamel_coeff_int (by omega) S.s S.hs0 S.hsd j hj3 R (frozenRegime d S.s c₀) 1 Λ
    (Torus.cbNorm (j + 3) S.V) 1 Λ₀ Λ₀ (mfData d S.s S.hs0 S.hsd S.V S.β S.hβ) S.β⁻¹ 0 t (mfPath ρc) ρβ hAt hAβ
    (inv_pos.2 S.hβ) φc hφ ⟨ht, le_rfl⟩ k hτ
  rw [hρ] at this
  exact this

end HRS.ThermLin.Plan2

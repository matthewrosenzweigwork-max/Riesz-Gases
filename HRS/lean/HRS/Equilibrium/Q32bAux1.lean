/-
# HRS.Equilibrium.Q32bAux1 -- helpers for `linearStat_variance` (packet Q32b)

Generic marginal-domination bound for the linear statistic `μ_N(f) = N⁻¹ ∑ f(x_i)`:
if every one-coordinate marginal of `P` is `≤ E • μ`, then `N Var_P[μ_N f] ≤ N E ∫ f² dμ`.
-/
import HRS.Equilibrium.QuadraticVariance

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Q32b

variable {d : ℕ} {s : ℝ}

theorem q32b_enorm_sq (x : ℝ) : ‖x‖ₑ ^ 2 = ENNReal.ofReal (x ^ 2) := by
  rw [← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]

theorem q32b_sq_mean_le {N : ℕ} (hN : 0 < N) (a : Fin N → ℝ) :
    ((1 / (N : ℝ)) * ∑ i, a i) ^ 2 ≤ (1 / (N : ℝ)) * ∑ i, a i ^ 2 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin N))) (f := a)
  rw [Finset.card_univ, Fintype.card_fin] at h
  rw [mul_pow, one_div, inv_pow]
  rw [inv_mul_le_iff₀ (by positivity), ← mul_assoc]
  calc (∑ i, a i) ^ 2 ≤ (N : ℝ) * ∑ i, a i ^ 2 := h
    _ = ((N : ℝ) ^ 2 * (N : ℝ)⁻¹) * ∑ i, a i ^ 2 := by field_simp
    _ = _ := by ring

/-- **Marginal domination bound.** -/
theorem q32b_marg_bound {N : ℕ} (hN : 0 < N) {P : Measure (Config d N)} [IsProbabilityMeasure P]
    {μ : Measure (Torus d)} {E : ℝ} (hE : 0 ≤ E)
    (hm : ∀ i, P.map (fun X => X i) ≤ ENNReal.ofReal E • μ)
    {f : Torus d → ℝ} (hf : Measurable f) (hf2 : MemLp f 2 μ) :
    (N : ℝ≥0∞) * evariance (fun X : Config d N => (1 / (N : ℝ)) * ∑ i, f (X i)) P ≤
      ENNReal.ofReal (N * E * ∫ x, f x ^ 2 ∂μ) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hS : ∀ i : Fin N, Measurable fun X : Config d N => f (X i) :=
    fun i => hf.comp (measurable_pi_apply i)
  have hF : Measurable (fun X : Config d N => (1 / (N : ℝ)) * ∑ i, f (X i)) :=
    (Finset.measurable_sum _ fun i _ => hS i).const_mul _
  have h1 := HRS.External.evariance_le_lintegral_sub P hF.aestronglyMeasurable 0
  simp only [sub_zero] at h1
  have hpt : ∀ X : Config d N, ‖(1 / (N : ℝ)) * ∑ i, f (X i)‖ₑ ^ 2 ≤
      ENNReal.ofReal (1 / (N : ℝ)) * ∑ i, ENNReal.ofReal (f (X i) ^ 2) := by
    intro X
    rw [q32b_enorm_sq, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (q32b_sq_mean_le hN _)
  have hI : ∫⁻ z, ENNReal.ofReal (f z ^ 2) ∂μ = ENNReal.ofReal (∫ z, f z ^ 2 ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hf2.integrable_sq (Filter.Eventually.of_forall fun z => sq_nonneg _)]
  have hmarg : ∀ i : Fin N, ∫⁻ X, ENNReal.ofReal (f (X i) ^ 2) ∂P ≤
      ENNReal.ofReal E * ENNReal.ofReal (∫ z, f z ^ 2 ∂μ) := by
    intro i
    have hg : Measurable fun z : Torus d => ENNReal.ofReal (f z ^ 2) :=
      ENNReal.measurable_ofReal.comp (hf.pow_const 2)
    calc ∫⁻ X, ENNReal.ofReal (f (X i) ^ 2) ∂P
        = ∫⁻ z, ENNReal.ofReal (f z ^ 2) ∂(P.map (fun X => X i)) := by
          rw [lintegral_map hg (measurable_pi_apply i)]
      _ ≤ ∫⁻ z, ENNReal.ofReal (f z ^ 2) ∂(ENNReal.ofReal E • μ) := lintegral_mono' (hm i) le_rfl
      _ = _ := by rw [lintegral_smul_measure, smul_eq_mul, hI]
  calc (N : ℝ≥0∞) * evariance (fun X : Config d N => (1 / (N : ℝ)) * ∑ i, f (X i)) P
      ≤ (N : ℝ≥0∞) * ∫⁻ X, ENNReal.ofReal (1 / (N : ℝ)) * ∑ i, ENNReal.ofReal (f (X i) ^ 2) ∂P := by
        gcongr
        exact h1.trans (lintegral_mono hpt)
    _ = (N : ℝ≥0∞) * (ENNReal.ofReal (1 / (N : ℝ)) * ∑ i, ∫⁻ X, ENNReal.ofReal (f (X i) ^ 2) ∂P) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_finsetSum]
        exact fun i _ => ENNReal.measurable_ofReal.comp ((hS i).pow_const 2)
    _ ≤ (N : ℝ≥0∞) * (ENNReal.ofReal (1 / (N : ℝ)) *
          ∑ _i : Fin N, ENNReal.ofReal E * ENNReal.ofReal (∫ z, f z ^ 2 ∂μ)) := by
        gcongr with i _
        exact hmarg i
    _ = ENNReal.ofReal (N * E * ∫ x, f x ^ 2 ∂μ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp


section Crude

open Function

open HRS HRS.External HRS.External.RefMarg HRS.External.PoleVar HRS.External.HeatSplit HRS.Quad

/-- **Crude bound for a fixed `N`** (no smallness): `N Var_Q[μ_N f] ≤ C_N ∫ f² dμ`. -/
theorem q32b_crude (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β) (ρ : Torus d → ℝ)
    (hρ : SmoothPosDensity ρ) {N : ℕ} (hN : 2 ≤ N) :
    ∃ C : ℝ, ∀ f : Torus d → ℝ, Measurable f → MemLp f 2 (withDensityReal ρ) →
      (N : ℝ≥0∞) * evariance (fun X : Config d N => (1 / (N : ℝ)) * ∑ i, f (X i))
          (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≤
        ENNReal.ofReal (C * ∫ x, f x ^ 2 ∂(withDensityReal ρ)) := by
  haveI hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  have hN0 : 0 < N := by omega
  obtain ⟨τ, L, Λ, M, Ψ, hτ, hτ1, hΛ1, hΛ, hΨ, hκ⟩ := PoleVar.exists_split_params hd hs0 hsd hβ hρ
  have hRH := Calib.refHyp_weakSplit hd hs0 hsd hτ hτ1 L hρ.density hΛ Ψ hΨ
  set γ : ℝ := Λ * (weakSplit d s τ L).c with hγ
  set K0 : ℝ := max 1 (4 * β * (weakSplit d s τ L).gL 0) with hK0
  have ht0 : ∀ x, |inner ℝ (Calib.tN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N)
      (Calib.Xi (withDensityReal ρ) Ψ x)| ≤ K0 :=
    fun x => (abs_tN_inner_le hRH hβ hN0 x).trans (le_max_right _ _)
  set V := weakPotK hRH hβ.le (Calib.tN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N) ht0 with hV
  have hRN : Calib.RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N =
      pinnedLaw V (β / ((N : ℕ) : ℝ)) N (fun e : Empty => e.elim) := by
    rw [RN_eq_fieldLawK hRH hβ.le ht0, pinnedLaw_empty]
  obtain ⟨K', hK'0, hQK⟩ := riesz_Q_le_smul_RN_crude hd hs0 hsd hτ hτ1 L hρ.density hΛ Ψ hΨ hβ hN0
  haveI hQp := riesz_Q_isProb hd hs0 hsd hτ hτ1 L hρ.density hΛ Ψ hΨ hβ hN0
  set Ep : ℝ := Real.exp ((β * γ + K0) + 0 + β * γ) with hEp
  have hm : ∀ i : Fin N, (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)).map (fun X => X i) ≤
      ENNReal.ofReal (K' * Ep) • withDensityReal ρ := by
    intro i
    have h1 : (pinnedLaw V (β / ((N : ℕ) : ℝ)) N (fun e : Empty => e.elim)).map (fun y => y i) ≤
        ENNReal.ofReal Ep • withDensityReal ρ :=
      marginal_le_smul (B := Empty) V hβ.le hN0 (n := N) (by simp) (fun e => e.elim) i
    rw [← hRN] at h1
    refine (Measure.map_mono hQK (measurable_pi_apply i)).trans ?_
    rw [Measure.map_smul _ (measurable_pi_apply i).aemeasurable]
    refine Measure.le_iff'.2 fun A => ?_
    have h2 := h1 A
    rw [Measure.smul_apply, smul_eq_mul] at h2
    rw [Measure.smul_apply, smul_eq_mul, Measure.smul_apply, smul_eq_mul]
    calc ENNReal.ofReal K' * (Calib.RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N).map (fun X => X i) A
        ≤ ENNReal.ofReal K' * (ENNReal.ofReal Ep * withDensityReal ρ A) := mul_le_mul' le_rfl h2
      _ = _ := by rw [← mul_assoc, ENNReal.ofReal_mul hK'0.le]
  refine ⟨N * (K' * Ep), fun f hf hf2 => ?_⟩
  exact q32b_marg_bound hN0 (mul_nonneg hK'0.le (Real.exp_pos _).le) hm hf hf2

end Crude


section Large

open Function

open HRS HRS.External HRS.External.RefMarg HRS.External.PoleVar HRS.External.HeatSplit HRS.Quad

/-- **Large `N`**: transfer to the weak reference law (`Q ≤ e^{4βg_L(0)} R`) and Wu's linear
variance inequality `Var_R(∑ f) ≤ 2N Var_π(f)` (`A:eq:weak-linear`), `π ≤ C μ`. -/
theorem q32b_large (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β) (ρ : Torus d → ℝ)
    (hρ : SmoothPosDensity ρ) :
    ∃ (C : ℝ) (N₁ : ℕ), ∀ N : ℕ, N₁ ≤ N → 2 ≤ N → ∀ f : Torus d → ℝ, Measurable f →
      MemLp f 2 (withDensityReal ρ) →
      (N : ℝ≥0∞) * evariance (fun X : Config d N => (1 / (N : ℝ)) * ∑ i, f (X i))
          (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≤
        ENNReal.ofReal (C * ∫ x, f x ^ 2 ∂(withDensityReal ρ)) := by
  haveI hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  obtain ⟨τ, L, Λ, M, Ψ, hτ, hτ1, hΛ1, hΛ, hΨ, hκ⟩ := PoleVar.exists_split_params hd hs0 hsd hβ hρ
  have hRH := Calib.refHyp_weakSplit hd hs0 hsd hτ hτ1 L hρ.density hΛ Ψ hΨ
  set γ : ℝ := Λ * (weakSplit d s τ L).c with hγ
  set gL0 : ℝ := (weakSplit d s τ L).gL 0 with hgL0
  obtain ⟨N₀, hN₀⟩ := Glue.eventually_hsmall hd hs0 hsd hτ hτ1 L hρ.density hΛ Ψ hΨ hβ
  obtain ⟨N₂, hN₂⟩ := Glue.riesz_Q_le_smul_RN_eventually hd hs0 hsd hτ hτ1 L hρ.density hΛ Ψ hΨ hβ hκ
  set KQ : ℝ := Real.exp (4 * β * gL0) with hKQ
  have hKQ0 : 0 < KQ := Real.exp_pos _
  set E : ℝ := Real.exp ((β * γ + 1) + 0 + β * γ) with hE
  have hE0 : 0 < E := Real.exp_pos _
  refine ⟨2 * KQ * E, max (max N₀ N₂) 2, ?_⟩
  intro N hN hN2 f hf hf2
  have hNN₀ : N₀ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNN₂ : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hNn : 0 < n + 1 := Nat.succ_pos n
  have ht : ∀ x, |inner ℝ (Calib.tN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β (n + 1))
      (Calib.Xi (withDensityReal ρ) Ψ x)| ≤ 1 := fun x => by
    have := hN₀ (n + 1) hNN₀ x
    rwa [← Calib.inner_eq_sum] at this
  set V := weakPotK hRH hβ.le (Calib.tN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β (n + 1)) ht with hV
  have hRN : Calib.RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β (n + 1) =
      pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim) := by
    rw [RN_eq_fieldLawK hRH hβ.le ht, pinnedLaw_empty]
  have hκV : weakKappa V β ≤ 1 / 2 := weakKappa_weakPotK_le hRH hβ.le ht hκ
  haveI hQp := riesz_Q_isProb hd hs0 hsd hτ hτ1 L hρ.density hΛ Ψ hΨ hβ hNn
  have hQK := hN₂ (n + 1) hNN₂
  rw [hRN] at hQK
  set R0 := pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim) with hR0
  haveI hRp : IsProbabilityMeasure (Calib.RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β (n + 1)) :=
    hRH.isProb_RN hβ.le
  haveI hR0p : IsProbabilityMeasure R0 := by rw [← hRN]; exact hRp
  set π0 : Measure (Torus d) := R0.map (fun X => X 0) with hπ0
  haveI hπ0p : IsProbabilityMeasure π0 := inferInstance
  have hπ0le : π0 ≤ ENNReal.ofReal E • withDensityReal ρ :=
    marginal_le_smul (B := Empty) V hβ.le hNn (n := n + 1) (by simp) (fun e => e.elim) ⟨0, hNn⟩
  have hS : Measurable fun X : Config d (n + 1) => ∑ i, f (X i) :=
    Finset.measurable_sum _ fun i _ => hf.comp (measurable_pi_apply i)
  have hI : ∫⁻ z, ‖f z‖ₑ ^ 2 ∂(withDensityReal ρ) = ENNReal.ofReal (∫ z, f z ^ 2 ∂(withDensityReal ρ)) :=
    lintegral_enorm_sq_eq_ofReal hf2
  have hπ2 : evariance f π0 ≤ ENNReal.ofReal E * ENNReal.ofReal (∫ z, f z ^ 2 ∂(withDensityReal ρ)) := by
    refine (HRS.External.evariance_le_lintegral_sub π0 hf.aestronglyMeasurable 0).trans ?_
    simp only [sub_zero]
    calc ∫⁻ z, ‖f z‖ₑ ^ 2 ∂π0 ≤ ∫⁻ z, ‖f z‖ₑ ^ 2 ∂(ENNReal.ofReal E • withDensityReal ρ) :=
          lintegral_mono' hπ0le le_rfl
      _ = _ := by rw [lintegral_smul_measure, smul_eq_mul, hI]
  have hlin := weak_linear_variance_symm (B := Empty) V hβ.le hNn (n := n + 1) (by simp)
    (fun e : Empty => e.elim) hκV f hf
  have hQR := evariance_le_of_le_smul hQK hS
  have hc : evariance (fun X : Config d (n + 1) => (1 / ((n + 1 : ℕ) : ℝ)) * ∑ i, f (X i))
      (modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ)) =
      ENNReal.ofReal ((1 / ((n + 1 : ℕ) : ℝ)) ^ 2) * evariance (fun X : Config d (n + 1) => ∑ i, f (X i))
        (modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ)) := evariance_mul _ _ _
  rw [hc]
  have hNR : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hNn
  calc ((n + 1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal ((1 / ((n + 1 : ℕ) : ℝ)) ^ 2) *
        evariance (fun X : Config d (n + 1) => ∑ i, f (X i))
          (modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ)))
      ≤ ((n + 1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal ((1 / ((n + 1 : ℕ) : ℝ)) ^ 2) *
          (ENNReal.ofReal KQ * (2 * ((n + 1 : ℕ) : ℝ≥0∞) *
            (ENNReal.ofReal E * ENNReal.ofReal (∫ z, f z ^ 2 ∂(withDensityReal ρ)))))) := by
        gcongr
        refine hQR.trans ?_
        gcongr
        exact hlin.trans (by gcongr)
    _ = ENNReal.ofReal (2 * KQ * E * ∫ x, f x ^ 2 ∂(withDensityReal ρ)) := by
        have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
        rw [h2, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp

end Large


section Main

open HRS HRS.Quad

/-- Assembly: large `N` by `q32b_large`, the finitely many `N < N₁` by `q32b_crude`. -/
theorem q32b_main (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ f : Torus d → ℝ, Measurable f →
      MemLp f 2 (withDensityReal ρ) →
        (N : ℝ≥0∞) * evariance (fun X : Config d N => (1 / (N : ℝ)) * ∑ i, f (X i))
            (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≤
          ENNReal.ofReal (C * ∫ x, f x ^ 2 ∂(withDensityReal ρ)) := by
  obtain ⟨C₁, N₁, h1⟩ := q32b_large hd hs0 hsd hβ ρ hρ
  have hc : ∀ N : ℕ, ∃ C : ℝ, 2 ≤ N → ∀ f : Torus d → ℝ, Measurable f →
      MemLp f 2 (withDensityReal ρ) →
        (N : ℝ≥0∞) * evariance (fun X : Config d N => (1 / (N : ℝ)) * ∑ i, f (X i))
            (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≤
          ENNReal.ofReal (C * ∫ x, f x ^ 2 ∂(withDensityReal ρ)) := by
    intro N
    by_cases hN : 2 ≤ N
    · obtain ⟨C, hC⟩ := q32b_crude hd hs0 hsd hβ ρ hρ hN
      exact ⟨C, fun _ => hC⟩
    · exact ⟨0, fun h => absurd h hN⟩
  choose Cs hCs using hc
  refine ⟨|C₁| + ∑ N ∈ Finset.range N₁, |Cs N|, ?_⟩
  intro N hN f hf hf2
  have hI : 0 ≤ ∫ x, f x ^ 2 ∂(withDensityReal ρ) := integral_nonneg fun _ => sq_nonneg _
  by_cases hNN : N₁ ≤ N
  · refine (h1 N hNN hN f hf hf2).trans (ENNReal.ofReal_le_ofReal ?_)
    have h2 : C₁ ≤ |C₁| + ∑ N ∈ Finset.range N₁, |Cs N| := by
      have := le_abs_self C₁
      have : 0 ≤ ∑ N ∈ Finset.range N₁, |Cs N| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      linarith
    exact mul_le_mul_of_nonneg_right h2 hI
  · have hlt : N < N₁ := not_le.1 hNN
    refine (hCs N hN f hf hf2).trans (ENNReal.ofReal_le_ofReal ?_)
    have h2 : Cs N ≤ |C₁| + ∑ N ∈ Finset.range N₁, |Cs N| := by
      have h3 : |Cs N| ≤ ∑ N ∈ Finset.range N₁, |Cs N| :=
        Finset.single_le_sum (f := fun N => |Cs N|) (fun M _ => abs_nonneg (Cs M)) (Finset.mem_range.2 hlt)
      have := le_abs_self (Cs N)
      have := abs_nonneg C₁
      linarith
    exact mul_le_mul_of_nonneg_right h2 hI

end Main

end HRS.Q32b

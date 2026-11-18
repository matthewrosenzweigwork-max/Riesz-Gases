import HRS.Main.ThermLinPlan2
import HRS.Uniform.Q48eAux2
import HRS.PDE.MeanFieldLinearLoss
import HRS.Uniform.Q48bAux1

/-!
# THERMLIN2 packet Ly, part 2: `tl2_lyapunov` (D2)

Route: `N_u(f,g) = 2β⁻¹ ∫_0^u E(σ) dσ`, `E(σ) = ∫ ∇U^β_σ f · ∇U^β_σ g ρβ`.
(1) `N_u(f,g) → C_β(f,g)` for smooth `f, g` (`PDE.MFLinear.exists_cov_comparison` for the constant trajectory,
reflection `r ↦ u - r` and the time homogeneity of the frozen propagator);
(2) `N_{t+u}(f,g) = N_t(f,g) + N_u(U_t f, U_t g)` (semigroup + time homogeneity);
(3) let `u → ∞` in (2) using (1) for `(f,g)` and for `(U_t f, U_t g)`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ThermLin.Plan2

open HRS HRS.PDE HRS.PDE.MFSemigroup HRS.Uniform

variable {d : ℕ}

/-- Time homogeneity of the frozen propagator on smooth tests (the content of plan statement `tl2_frozen_shift`,
reproved here so that `tl2_lyapunov_proof` does not depend on it). -/
theorem tl2Ly_shift (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ)
    {u t : ℝ} (hu : 0 ≤ u) (hut : u ≤ t) :
    tl2Ub S ρβ u t φ = tl2Ub S ρβ 0 (t - u) φ := by
  obtain ⟨hρ, hpos⟩ := HRS.ThermLin.thermlin_thermal_smooth_pos S h
  have hd : 1 ≤ d := by have := S.hd; omega
  have hprob : IsProbDensity ρβ := h.1
  set D := S.dyn with hD
  obtain ⟨T', hT'def⟩ : ∃ T' : ℝ, T' = t + 1 := ⟨_, rfl⟩
  have hT' : 0 < T' := by rw [hT'def]; linarith
  obtain ⟨R, MB, Λ, VB, hA⟩ := adjointData_frozen S.s S.hs0 S.hsd S.β S.hβ S.V S.hV ρβ hprob hρ hpos (mStar d)
  obtain ⟨C, Cs, -, -, hmain⟩ := adjoint_torus_classical hd S.s S.hs0 S.hsd (mStar d) le_rfl R MB Λ VB
  have hψc : Continuous φ := ClassicalAux.continuous_of_isCk (isCk_nat_of_isSmooth hφ 1)
  obtain ⟨hF, -⟩ := hmain D 0 T' (fun _ => ρβ) (hA 0 T' hT') T' ⟨hT', le_rfl⟩ φ hψc
    (memSobolev_of_isSmooth hφ _)
  set F : ℝ → Torus d → ℝ := fun r x =>
    toFun (propagatorCoeff D (fun _ => ρβ) (mStar d) T' (coeffOf φ) (T' - r)) x with hFdef
  have hid : ∀ t₁ u₁ : ℝ, 0 ≤ u₁ → u₁ ≤ t₁ → t₁ ≤ t →
      propagator D (fun _ => ρβ) u₁ t₁ φ = F (u₁ + (T' - t₁)) := by
    intro t₁ u₁ hu₁ hut₁ htT
    by_cases ht₁ : 0 < t₁
    · have htT' : t₁ ≤ T' := by linarith
      have hG := shift_classical D ρβ htT' hF
      have hex : ∃ f, IsClassicalAdjointSolution D (fun _ => ρβ) t₁ φ f := ⟨_, hG⟩
      have hu' := classical_adjoint_unique hd S.s S.hs0 S.hsd (mStar d)
        (by have := ClassicalPart.three_le_mStar d; omega)
        R MB Λ VB D 0 t₁ (fun _ => ρβ) (hA 0 t₁ ht₁) t₁ ⟨ht₁, le_rfl⟩ φ _ _ hex.choose_spec hG u₁ ⟨hu₁, hut₁⟩
      simp only [propagator, hex, dite_true]
      rw [hu']
    · have ht0 : t₁ = 0 := le_antisymm (not_lt.1 ht₁) (hu₁.trans hut₁)
      have hu0 : u₁ = 0 := le_antisymm (ht0 ▸ hut₁) hu₁
      subst ht0; subst hu0
      have e : propagator D (fun _ => ρβ) 0 0 φ = φ :=
        HRS.Uniform.Q48e.frozen_self_pos hd S.s S.hs0 S.hsd S.β S.hβ S.V S.hV ρβ hprob hρ hpos φ hφ 0 le_rfl
      rw [e]
      have := hF.terminal
      simp only [zero_add, sub_zero]
      exact this.symm
  have h1 := hid t u hu hut le_rfl
  have h2 := hid (t - u) 0 le_rfl (by linarith) (by linarith)
  show propagator D (fun _ => ρβ) u t φ = propagator D (fun _ => ρβ) 0 (t - u) φ
  rw [h1, h2]
  congr 1
  ring


/-- `U^β_{0,t} f` is smooth. -/
theorem tl2Ly_smooth (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ)
    {u t : ℝ} (hu : 0 ≤ u) (hut : u ≤ t) : Torus.IsSmooth (tl2Ub S ρβ u t φ) := by
  obtain ⟨hρ, hpos⟩ := HRS.ThermLin.thermlin_thermal_smooth_pos S h
  have hd : 1 ≤ d := by have := S.hd; omega
  exact HRS.Uniform.Q48e.frozen_smooth hd S.s S.hs0 S.hsd S.β S.hβ S.V S.hV ρβ h.1 hρ hpos φ hφ u t hu hut

/-- Semigroup property `U_{t+σ} f = U_σ U_t f` (frozen, from `Q48e.frozen_semigroup` and time homogeneity). -/
theorem tl2Ly_semigroup (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ)
    {t σ : ℝ} (ht : 0 ≤ t) (hσ : 0 ≤ σ) :
    tl2Ub S ρβ 0 (t + σ) φ = tl2Ub S ρβ 0 σ (tl2Ub S ρβ 0 t φ) := by
  obtain ⟨hρ, hpos⟩ := HRS.ThermLin.thermlin_thermal_smooth_pos S h
  have hd : 1 ≤ d := by have := S.hd; omega
  have h1 : tl2Ub S ρβ 0 (t + σ) φ = tl2Ub S ρβ 0 σ (tl2Ub S ρβ σ (t + σ) φ) :=
    HRS.Uniform.Q48e.frozen_semigroup hd S.s S.hs0 S.hsd S.β S.hβ S.V S.hV ρβ h.1 hρ hpos φ hφ 0 σ (t + σ)
      le_rfl hσ (by linarith)
  have h2 : tl2Ub S ρβ σ (t + σ) φ = tl2Ub S ρβ 0 t φ := by
    rw [tl2Ly_shift S h hφ hσ (by linarith)]
    congr 1
    ring
  rw [h1, h2]


/-- The energy integrand `E(σ) = ∫ ∇U^β_σ f · ∇U^β_σ g ρβ`. -/
def tl2LyE (S : HRS.Main.PreparedData d) (ρβ : Torus d → ℝ) (f g : Torus d → ℝ) (σ : ℝ) : ℝ :=
  ∫ x, inner ℝ (Torus.grad (tl2Ub S ρβ 0 σ f) x) (Torus.grad (tl2Ub S ρβ 0 σ g) x) * ρβ x

/-- `N_u(f,g) = 2β⁻¹ ∫_0^u E(σ) dσ`. -/
def tl2LyN (S : HRS.Main.PreparedData d) (ρβ : Torus d → ℝ) (f g : Torus d → ℝ) (u : ℝ) : ℝ :=
  2 * S.β⁻¹ * ∫ σ in Set.Icc 0 u, tl2LyE S ρβ f g σ

/-- Data for the constant trajectory: `FiniteRegHyp`, the constant coefficient solution, and the parameters
`j, K` of `exists_cov_comparison`. -/
theorem tl2Ly_data (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) :
    ∃ (K : ℕ) (_ : FiniteRegHyp d S.s S.β S.β K S.V ρβ) (ρc : ℝ → Coeff d) (j : ℕ),
      Even j ∧ (d : ℝ) / 2 + 4 < j ∧ 2 * j + 4 * d + 20 ≤ K ∧
      IsMFSolutionHK d S.s S.V S.β⁻¹ K ρβ ρc ∧ mfPath ρc = fun _ => ρβ := by
  obtain ⟨hsm, hpos⟩ := HRS.ThermLin.thermlin_thermal_smooth_pos S h
  have hd1 : 1 ≤ d := by have := S.hd; omega
  have hK6 : (d : ℝ) / 2 + 6 < ((8 * d + 40 : ℕ) : ℝ) := by
    push_cast; nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  exact ⟨8 * d + 40, HRS.Q40b.q40b_finiteRegHyp (HRS.ThermLin.thermlin_stationary_traj S h) hK6,
    fun _ => coeffOf ρβ, 2 * d + 10, ⟨d + 5, by omega⟩,
    by push_cast; nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)], by omega,
    HRS.Uniform.Q48b.q48b_isMFSolutionHK hd1 S.s S.hs0 S.hsd S.β S.hβ S.V S.hV ρβ h hsm hpos _,
    HRS.Uniform.Q48b.q48b_mfPath_const ρβ hsm⟩

open HRS.PDE.MFLinear in
/-- Continuity of the energy integrand. -/
theorem tl2Ly_E_cont (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) {f g : Torus d → ℝ}
    (hf : Torus.IsSmooth f) (hg : Torus.IsSmooth g) {T : ℝ} (hT : 0 < T) :
    ContinuousOn (tl2LyE S ρβ f g) (Set.Icc 0 T) := by
  obtain ⟨hsm, hpos⟩ := HRS.ThermLin.thermlin_thermal_smooth_pos S h
  have hd1 : 1 ≤ d := by have := S.hd; omega
  have hρC : Continuous ρβ := HRS.StaticLimitAux.continuous_of_smooth hsm
  obtain ⟨K, H, ρc, j, hje, hj, hK, hρc, hpath⟩ := tl2Ly_data S h
  obtain ⟨m, Cρ, c₀, Λ₀, hF, -⟩ := loss_facts hd1 S.s S.β S.β K S.V ρβ H j hje hj hK S.β ⟨le_rfl, le_rfl⟩
    ρc hρc ρβ h hρC hpos
  have h1 := continuousOn_energy_prop hF hf hg hT le_rfl le_rfl
  have h2 : ContinuousOn (fun σ : ℝ => T - σ) (Set.Icc 0 T) :=
    (continuous_const.sub continuous_id).continuousOn
  have h3 := h1.comp h2 (fun σ hσ => ⟨by linarith [hσ.2], by linarith [hσ.1]⟩)
  refine h3.congr fun σ hσ => ?_
  simp only [Function.comp, tl2LyE, hpath]
  have e1 : tl2Ub S ρβ (T - σ) T f = tl2Ub S ρβ 0 σ f := by
    rw [tl2Ly_shift S h hf (by linarith [hσ.2]) (by linarith [hσ.1])]; congr 1; ring
  have e2 : tl2Ub S ρβ (T - σ) T g = tl2Ub S ρβ 0 σ g := by
    rw [tl2Ly_shift S h hg (by linarith [hσ.2]) (by linarith [hσ.1])]; congr 1; ring
  simp only [tl2Ub, HRS.Main.PreparedData.dyn] at e1 e2
  rw [e1, e2]
  rfl


open HRS.PDE.MFLinear in
/-- Pointwise: along the constant path, `Eint` at `(T,T,r)` is `E(T - r)`. -/
theorem tl2Ly_Eint (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) {f g : Torus d → ℝ}
    (hf : Torus.IsSmooth f) (hg : Torus.IsSmooth g) {ρc : ℝ → Coeff d} (hpath : mfPath ρc = fun _ => ρβ)
    {T r : ℝ} (hr0 : 0 ≤ r) (hrT : r ≤ T) :
    Eint S.dyn ρc f g T T r = tl2LyE S ρβ f g (T - r) := by
  simp only [Eint, tl2LyE, hpath]
  have e1 : propagator S.dyn (fun _ => ρβ) r T f = propagator S.dyn (fun _ => ρβ) 0 (T - r) f :=
    tl2Ly_shift S h hf hr0 hrT
  have e2 : propagator S.dyn (fun _ => ρβ) r T g = propagator S.dyn (fun _ => ρβ) 0 (T - r) g :=
    tl2Ly_shift S h hg hr0 hrT
  rw [e1, e2]

/-- `C_β(f, P g) = C_β(f, g)`: the covariance only sees `projMean` of the second argument. -/
theorem tl2Ly_cov_projMean {d : ℕ} (g : Torus d → ℝ) (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (β : ℝ)
    (f ψ : Torus d → ℝ) (hψ : Continuous ψ) :
    susceptibilityCov g μ β f (projMean μ ψ) = susceptibilityCov g μ β f ψ := by
  have hint : Integrable ψ μ := hψ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace ψ)
  have hpair : pair μ (projMean μ ψ) = 0 := by
    unfold pair projMean
    rw [integral_sub hint (integrable_const _), integral_const]
    simp [pair]
  have hpp : projMean μ (projMean μ ψ) = projMean μ ψ := by
    funext x
    simp only [projMean] at hpair ⊢
    rw [hpair]; ring
  have hR : IsResponse g μ β (projMean μ ψ) = IsResponse g μ β ψ := by
    funext hh
    unfold IsResponse
    rw [hpp]
  unfold susceptibilityCov responseInverse
  rw [hR]

open HRS.PDE.MFLinear in
/-- Step (1): `N_u(f,g) → C_β(f,g)`. -/
theorem tl2Ly_N_tendsto (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) {f g : Torus d → ℝ}
    (hf : Torus.IsSmooth f) (hg : Torus.IsSmooth g) :
    Tendsto (tl2LyN S ρβ f g) atTop
      (𝓝 (susceptibilityCov (periodicRiesz d S.s) (withDensityReal ρβ) S.β f g)) := by
  obtain ⟨hsm, hpos⟩ := HRS.ThermLin.thermlin_thermal_smooth_pos S h
  have hd1 : 1 ≤ d := by have := S.hd; omega
  have hρC : Continuous ρβ := HRS.StaticLimitAux.continuous_of_smooth hsm
  have : IsProbabilityMeasure (withDensityReal ρβ) := HRS.isProb_withDensityReal h.1
  obtain ⟨K, H, ρc, j, hje, hj, hK, hρc, hpath⟩ := tl2Ly_data S h
  have hφ : ∀ a : Fin 2, Torus.IsSmooth (![f, g] a) := by
    intro a; fin_cases a
    · exact hf
    · exact hg
  obtain ⟨-, C0, c0, hC0, hc0, hall⟩ := exists_cov_comparison hd1 S.s S.β S.β K S.V ρβ H j hje hj hK S.β
    ⟨le_rfl, le_rfl⟩ ρc hρc ρβ h hρC hpos 2 (fun _ => 0) (fun _ => le_rfl) ![f, g] hφ
  have hbound : ∀ u : ℝ, 0 ≤ u → |tl2LyN S ρβ f g u -
      susceptibilityCov (periodicRiesz d S.s) (withDensityReal ρβ) S.β f g| ≤ C0 * Real.exp (-c0 * u) := by
    intro u hu
    have h1 := (hall u hu).2 0 1
    have hM : Mcov (mfD H ⟨le_rfl, le_rfl⟩) ρc (fun _ : Fin 2 => (0 : ℝ)) ![f, g] u 0 1 = tl2LyN S ρβ f g u := by
      simp only [Mcov, Matrix.of_apply, add_zero, min_self, Matrix.cons_val_zero, Matrix.cons_val_one,
        tl2LyN]
      have hinv : (mfD H ⟨le_rfl, le_rfl⟩).invβ = S.β⁻¹ := rfl
      rw [hinv]
      congr 1
      have h1 : ∫ r in Set.Icc 0 u, Eint (mfD H ⟨le_rfl, le_rfl⟩) ρc f g u u r =
          ∫ r in Set.Icc 0 u, tl2LyE S ρβ f g (u - r) :=
        setIntegral_congr_fun measurableSet_Icc (fun r hr => tl2Ly_Eint S h hf hg hpath hr.1 hr.2)
      rw [h1, integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hu, ← intervalIntegral.integral_of_le hu,
        intervalIntegral.integral_comp_sub_left (fun σ => tl2LyE S ρβ f g σ) u]
      simp
    have hS : stationaryLagCov d S.s S.β (mfD H ⟨le_rfl, le_rfl⟩) ρβ (fun _ : Fin 2 => (0 : ℝ)) ![f, g] 0 1 =
        susceptibilityCov (periodicRiesz d S.s) (withDensityReal ρβ) S.β f g := by
      simp only [stationaryLagCov, Matrix.of_apply, le_refl, ite_true, sub_self, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      have e0 : propagator S.dyn (fun _ => ρβ) 0 0 g = g :=
        HRS.Uniform.Q48e.frozen_self_pos hd1 S.s S.hs0 S.hsd S.β S.hβ S.V S.hV ρβ h.1 hsm hpos g hg 0 le_rfl
      change susceptibilityCov (periodicRiesz d S.s) (withDensityReal ρβ) S.β f
        (projMean (withDensityReal ρβ) (propagator S.dyn (fun _ => ρβ) 0 0 g)) = _
      rw [e0]
      exact tl2Ly_cov_projMean _ _ _ f g (HRS.StaticLimitAux.continuous_of_smooth hg)
    rw [hM, hS] at h1
    exact h1
  have hexp : Tendsto (fun u : ℝ => C0 * Real.exp (-c0 * u)) atTop (𝓝 0) := by
    have h := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop hc0)).const_mul C0
    rw [mul_zero] at h
    refine h.congr fun u => ?_
    simp [neg_mul]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun u => norm_nonneg _) ?_ hexp
  filter_upwards [eventually_ge_atTop 0] with u hu
  rw [Real.norm_eq_abs]; exact hbound u hu


/-- Step (2): `N_{t+u}(f,g) = N_t(f,g) + N_u(U_t f, U_t g)`. -/
theorem tl2Ly_N_split (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) {f g : Torus d → ℝ}
    (hf : Torus.IsSmooth f) (hg : Torus.IsSmooth g) {t u : ℝ} (ht : 0 ≤ t) (hu : 0 ≤ u) :
    tl2LyN S ρβ f g (t + u) =
      tl2LyN S ρβ f g t + tl2LyN S ρβ (tl2Ub S ρβ 0 t f) (tl2Ub S ρβ 0 t g) u := by
  have hT : 0 < t + u + 1 := by linarith
  have hc := tl2Ly_E_cont S h hf hg hT
  have hI : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ t + u →
      IntervalIntegrable (tl2LyE S ρβ f g) volume a b := by
    intro a b ha hab hb
    refine (hc.mono ?_).intervalIntegrable_of_Icc hab
    intro x hx; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hconv : ∀ (f' g' : Torus d → ℝ) (v : ℝ), 0 ≤ v →
      tl2LyN S ρβ f' g' v = 2 * S.β⁻¹ * ∫ σ in (0 : ℝ)..v, tl2LyE S ρβ f' g' σ := by
    intro f' g' v hv
    unfold tl2LyN
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hv]
  rw [hconv _ _ _ (by linarith), hconv _ _ _ ht, hconv _ _ _ hu,
    ← intervalIntegral.integral_add_adjacent_intervals (hI 0 t le_rfl ht (by linarith))
      (hI t (t + u) ht (by linarith) le_rfl)]
  have hshift : ∫ x in t..t + u, tl2LyE S ρβ f g x = ∫ σ in (0 : ℝ)..u, tl2LyE S ρβ f g (t + σ) := by
    have := intervalIntegral.integral_comp_add_left (tl2LyE S ρβ f g) (a := 0) (b := u) t
    rw [this, add_zero]
  rw [hshift]
  have : ∫ σ in (0 : ℝ)..u, tl2LyE S ρβ f g (t + σ) =
      ∫ σ in (0 : ℝ)..u, tl2LyE S ρβ (tl2Ub S ρβ 0 t f) (tl2Ub S ρβ 0 t g) σ := by
    refine intervalIntegral.integral_congr (fun σ hσ => ?_)
    have hσ0 : 0 ≤ σ := by rw [Set.uIcc_of_le hu] at hσ; exact hσ.1
    simp only [tl2LyE]
    rw [tl2Ly_semigroup S h hf ht hσ0, tl2Ly_semigroup S h hg ht hσ0]
  rw [this]
  ring

/-- **D2** THE LYAPUNOV IDENTITY (`C:eq:stationary-cov`).  Does not use any other plan statement
(time homogeneity of the frozen propagator is reproved as `tl2Ly_shift`). -/
theorem tl2_lyapunov_proof (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) {f g : Torus d → ℝ}
    (hf : Torus.IsSmooth f) (hg : Torus.IsSmooth g) {t : ℝ} (ht : 0 ≤ t) :
    susceptibilityCov (periodicRiesz d S.s) (withDensityReal ρβ) S.β f g =
      susceptibilityCov (periodicRiesz d S.s) (withDensityReal ρβ) S.β (tl2Ub S ρβ 0 t f) (tl2Ub S ρβ 0 t g) +
        2 * S.β⁻¹ * ∫ σ in Set.Icc 0 t, ∫ x,
          inner ℝ (Torus.grad (tl2Ub S ρβ 0 σ f) x) (Torus.grad (tl2Ub S ρβ 0 σ g) x) * ρβ x := by
  have hUf := tl2Ly_smooth S h hf le_rfl ht
  have hUg := tl2Ly_smooth S h hg le_rfl ht
  have h1 := tl2Ly_N_tendsto S h hf hg
  have h2 := tl2Ly_N_tendsto S h hUf hUg
  have h3 : Tendsto (fun u => tl2LyN S ρβ f g (t + u)) atTop
      (𝓝 (susceptibilityCov (periodicRiesz d S.s) (withDensityReal ρβ) S.β f g)) :=
    h1.comp (tendsto_atTop_add_const_left atTop t tendsto_id)
  have h4 : Tendsto (fun u => tl2LyN S ρβ f g (t + u)) atTop
      (𝓝 (tl2LyN S ρβ f g t + susceptibilityCov (periodicRiesz d S.s) (withDensityReal ρβ) S.β
        (tl2Ub S ρβ 0 t f) (tl2Ub S ρβ 0 t g))) := by
    refine (h2.const_add (tl2LyN S ρβ f g t)).congr' ?_
    filter_upwards [eventually_ge_atTop 0] with u hu
    exact (tl2Ly_N_split S h hf hg ht hu).symm
  have h5 := tendsto_nhds_unique h3 h4
  rw [h5]
  unfold tl2LyN tl2LyE
  ring

example := (@tl2_lyapunov_proof : type_of% @tl2_lyapunov)

end HRS.ThermLin.Plan2

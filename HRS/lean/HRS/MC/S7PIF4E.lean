import HRS.MC.S7PIF4D
import HRS.MC.S7PIF1Dual

/-!
# Packet piF4, part E: the key identity for an observation at a positive time

For `0 < τ ≤ T`, `φ` smooth, a.s. for all `u ∈ [0,τ]`:
`ζ_u(U^{u,τ} φ) = ζ_0(U^{0,τ} φ) - N^{-1/2} ∫_{(0,u]} eval (ℬ_N^r) (U^{r,τ} φ) dr + √N M_u` with `M = empiricalMartingale D τ (U^{·,τ} φ)`.
Note the parentheses around the integral: `c * ∫ r in S, f r + b` parses as `c * ∫ r in S, (f r + b)`.
Route: `F1` (duality) for the classical solution `l2c3_classical`, the centring `ζ_u(g) = √N (flucPair - E flucPair)` (part B), the
pathwise decomposition of the interaction integral (part D) and `E M = 0`, `E J = 0` (part C).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIF4

open HRS HRS.PDE HRS.A33 HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI

variable {d : ℕ}

section Prob

variable (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T) (N : ℕ) (hN : 1 ≤ N)
  {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
  (hreal : PreparedRealization R.D P
    (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) X₀ W X)

include hm hT hN hreal

theorem S7PIF4_key {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hF : IsFilteredSolution P ℱ W' W X) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) {τ : ℝ}
    (hτ : τ ∈ Set.Ioc 0 T) :
    ∀ᵐ ω ∂P, ∀ u ∈ Set.Icc (0 : ℝ) τ,
      NegSobolev.eval (zetaAt m P X u ω) (propagator R.D R.ρ u τ φ) =
        NegSobolev.eval (zetaAt m P X 0 ω) (propagator R.D R.ρ 0 τ φ) -
        (Real.sqrt N)⁻¹ * (∫ r in Set.Ioc 0 u,
          NegSobolev.eval (quadFieldAt m R.D.s (fun s => withDensityReal (R.ρ s)) P X r ω)
            (propagator R.D R.ρ r τ φ)) +
        Real.sqrt N * empiricalMartingale P ℱ W' R.D τ (fun r => propagator R.D R.ρ r τ φ) X u ω := by
  have hN0 : 0 < N := hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hXm : ∀ s, Measurable (X s) := (hreal.solution 0).adapted
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hm2 : (d : ℝ) < 2 * m := by linarith
  obtain ⟨F, hFcl, hFeq⟩ := HRS.MC.L2C3.l2c3_classical R hτ.1 hφ
  have hφ2 : Torus.IsCk 2 φ :=
    ContDiff.of_le (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift φ) from hφ)
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  obtain ⟨hprogF, hmainF⟩ := HRS.MC.Sec7.S7PIF1.s7_PIF_duality_proof R T hT N hN P X₀ W X hreal
    hF hτ hφ2 hFcl
  have hΦeq : empiricalNoiseIntegrand R.D τ F X =
      empiricalNoiseIntegrand R.D τ (fun r => propagator R.D R.ρ r τ φ) X := by
    funext s ω k
    unfold empiricalNoiseIntegrand
    by_cases h : s ∈ Set.Icc 0 τ
    · simp only [h, if_true]
      rw [hFeq s h]
    · simp [h]
  have hprog : IsProgressiveL2 P ℱ
      (empiricalNoiseIntegrand R.D τ (fun r => propagator R.D R.ρ r τ φ) X) := hΦeq ▸ hprogF
  have hMeq : empiricalMartingale P ℱ W' R.D τ F X =
      empiricalMartingale P ℱ W' R.D τ (fun r => propagator R.D R.ρ r τ φ) X := by
    unfold empiricalMartingale; rw [hΦeq]
  have hsm : ∀ u, 0 ≤ u → u ≤ τ → Torus.IsSmooth (propagator R.D R.ρ u τ φ) := fun u h0 h1 =>
    (HRS.MC.L2C0.l2c0_proof R φ hφ u τ h0 h1).1
  -- duality identity for `f = U^{·,τ} φ`
  have hmain : ∀ᵐ ω ∂P, ∀ u ∈ Set.Icc (0 : ℝ) τ,
      IntegrableOn (fun r => flucInteraction R.D (propagator R.D R.ρ r τ φ) (X r.toNNReal ω) (R.ρ r))
        (Set.Icc 0 u) ∧
      flucPair (X u.toNNReal ω) (R.ρ u) (propagator R.D R.ρ u τ φ) =
        flucPair (X (0 : ℝ).toNNReal ω) (R.ρ 0) (propagator R.D R.ρ 0 τ φ) +
          empiricalMartingale P ℱ W' R.D τ (fun r => propagator R.D R.ρ r τ φ) X u ω +
          ∫ r in Set.Ioc 0 u, flucInteraction R.D (propagator R.D R.ρ r τ φ) (X r.toNNReal ω) (R.ρ r) := by
    filter_upwards [hmainF] with ω hω u hu
    obtain ⟨h1, h2⟩ := hω u hu
    have h0 : (0 : ℝ) ∈ Set.Icc 0 τ := ⟨le_rfl, hτ.1.le⟩
    refine ⟨?_, ?_⟩
    · refine h1.congr_fun (fun r hr => ?_) measurableSet_Icc
      have hr' : r ∈ Set.Icc 0 τ := ⟨hr.1, hr.2.trans hu.2⟩
      simp only
      rw [hFeq r hr']
    · have e1 : F u = propagator R.D R.ρ u τ φ := (hFeq u hu).symm
      have e0 : F 0 = propagator R.D R.ρ 0 τ φ := (hFeq 0 h0).symm
      rw [e1, e0, hMeq, Real.coe_toNNReal _ hu.1, intervalIntegral.integral_of_le hu.1] at h2
      rw [Real.toNNReal_zero, h2]
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
      rw [hFeq r ⟨hr.1.le, hr.2.trans hu.2⟩]
  have hG : ∀ᵐ ω ∂P, IntegrableOn
      (fun r => flucInteraction R.D (propagator R.D R.ρ r τ φ) (X r.toNNReal ω) (R.ρ r)) (Set.Icc 0 τ) := by
    filter_upwards [hmain] with ω hω using (hω τ ⟨hτ.1.le, le_rfl⟩).1
  obtain ⟨K, hK⟩ := S7PIF4_path_decomp R m hm T hT N hN P X₀ W X hreal hφ hτ hG
  -- expectations
  have hMint : ∀ u, Integrable (empiricalMartingale P ℱ W' R.D τ (fun r => propagator R.D R.ρ r τ φ) X u) P :=
    fun u => (memLp_two_itoIntegral hF.brownian hprog u).integrable one_le_two
  have hMmean : ∀ u, ∫ ω, empiricalMartingale P ℱ W' R.D τ (fun r => propagator R.D R.ρ r τ φ) X u ω ∂P = 0 :=
    fun u => integral_itoIntegral hF.brownian hprog u
  have hFlint : ∀ u ∈ Set.Icc (0 : ℝ) τ, Integrable
      (fun ω => flucPair (X u.toNNReal ω) (R.ρ u) (propagator R.D R.ρ u τ φ)) P := fun u hu =>
    S7PIF4_flucPair_integrable hN P (X u.toNNReal) (hXm _)
      (HRS.MC.Sec7.S7PIS1.S7PIS1_cont_of_smooth (hsm u hu.1 hu.2)) _
  have hexp : ∀ u ∈ Set.Icc (0 : ℝ) τ,
      (∫ ω, flucPair (X u.toNNReal ω) (R.ρ u) (propagator R.D R.ρ u τ φ) ∂P) -
        ∫ ω, flucPair (X (0 : ℝ).toNNReal ω) (R.ρ 0) (propagator R.D R.ρ 0 τ φ) ∂P =
      -(1 / (N : ℝ)) * K u := by
    intro u hu
    have h0 : (0 : ℝ) ∈ Set.Icc 0 τ := ⟨le_rfl, hτ.1.le⟩
    obtain ⟨hJi, hJ0⟩ := S7PIF4_J_mean_zero R m hm T hT N hN P X₀ W X hreal hφ hτ hu
    have hae : ∀ᵐ ω ∂P,
        flucPair (X u.toNNReal ω) (R.ρ u) (propagator R.D R.ρ u τ φ) -
          flucPair (X (0 : ℝ).toNNReal ω) (R.ρ 0) (propagator R.D R.ρ 0 τ φ) =
        empiricalMartingale P ℱ W' R.D τ (fun r => propagator R.D R.ρ r τ φ) X u ω +
          -(1 / (N : ℝ)) * ((∫ r in Set.Ioc 0 u,
            NegSobolev.eval (quadFieldAt m R.D.s (fun s => withDensityReal (R.ρ s)) P X r ω)
              (propagator R.D R.ρ r τ φ)) + K u) := by
      filter_upwards [hmain, hK] with ω h1 h2
      rw [(h1 u hu).2, h2 u hu]
      ring
    have hI1 : Integrable (fun ω => -(1 / (N : ℝ)) * ((∫ r in Set.Ioc 0 u,
        NegSobolev.eval (quadFieldAt m R.D.s (fun s => withDensityReal (R.ρ s)) P X r ω)
          (propagator R.D R.ρ r τ φ)) + K u)) P := (hJi.add (integrable_const (K u))).const_mul _
    rw [← integral_sub (hFlint u hu) (hFlint 0 h0), integral_congr_ae hae,
      integral_add (hMint u) hI1, hMmean, integral_const_mul]
    rw [show (∫ ω, ((∫ r in Set.Ioc 0 u,
        NegSobolev.eval (quadFieldAt m R.D.s (fun s => withDensityReal (R.ρ s)) P X r ω)
          (propagator R.D R.ρ r τ φ)) + K u) ∂P) = K u by
      rw [integral_add hJi (integrable_const _), hJ0]; simp]
    ring
  filter_upwards [hmain, hK] with ω h1 h2 u hu
  have h0 : (0 : ℝ) ∈ Set.Icc 0 τ := ⟨le_rfl, hτ.1.le⟩
  have z1 := S7PIF4_zeta_eval m hm2 hN P X hXm u (hsm u hu.1 hu.2) (R.ρ u) ω
  have z0 := S7PIF4_zeta_eval m hm2 hN P X hXm 0 (hsm 0 le_rfl hτ.1.le) (R.ρ 0) ω
  rw [z1, z0]
  have e1 := (h1 u hu).2
  have e2 := h2 u hu
  have e3 := hexp u hu
  have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hNr.le
  have hsN : Real.sqrt N ≠ 0 := (Real.sqrt_pos.2 hNr).ne'
  set a := flucPair (X u.toNNReal ω) (R.ρ u) (propagator R.D R.ρ u τ φ)
  set a0 := flucPair (X (0 : ℝ).toNNReal ω) (R.ρ 0) (propagator R.D R.ρ 0 τ φ)
  set Ea := ∫ ω', flucPair (X u.toNNReal ω') (R.ρ u) (propagator R.D R.ρ u τ φ) ∂P
  set Ea0 := ∫ ω', flucPair (X (0 : ℝ).toNNReal ω') (R.ρ 0) (propagator R.D R.ρ 0 τ φ) ∂P
  set Mu := empiricalMartingale P ℱ W' R.D τ (fun r => propagator R.D R.ρ r τ φ) X u ω
  set J := ∫ r in Set.Ioc 0 u, NegSobolev.eval
    (quadFieldAt m R.D.s (fun s => withDensityReal (R.ρ s)) P X r ω) (propagator R.D R.ρ r τ φ)
  set I := ∫ r in Set.Ioc 0 u, flucInteraction R.D (propagator R.D R.ρ r τ φ) (X r.toNNReal ω) (R.ρ r)
  have hinv : (Real.sqrt N)⁻¹ = Real.sqrt N * (1 / (N : ℝ)) := by
    field_simp
    nlinarith [hsq]
  rw [hinv]
  have : a - Ea = (a0 - Ea0) + (Mu + I + (1 / (N : ℝ)) * K u) := by
    have : Ea - Ea0 = -(1 / (N : ℝ)) * K u := e3
    linarith
  have hI : I = -(1 / (N : ℝ)) * (J + K u) := e2
  have hfin : a - Ea = (a0 - Ea0) + (Mu - (1 / (N : ℝ)) * J) := by
    rw [this, hI]; ring
  calc Real.sqrt N * (a - Ea) = Real.sqrt N * (a0 - Ea0) + Real.sqrt N * (Mu - (1 / (N : ℝ)) * J) := by
        rw [hfin]; ring
    _ = _ := by ring

end Prob

end HRS.MC.Sec7.S7PIF4

end

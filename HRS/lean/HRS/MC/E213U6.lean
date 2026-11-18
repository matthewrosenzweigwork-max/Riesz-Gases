import HRS.MC.E213Defs
import HRS.Main.GFEVAux7
import HRS.MC.S7PIM1c

/-!
# Packet e213u6 (Theorem 2.13, Wave 2): level bridges and the elementary bound of `ExpData.expr`
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213U6

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ}

section ExprLe

/-- Bounds of the unit ball: `‖D^j Φ z‖ ≤ 1` for `j ≤ 5`. -/
theorem u6_norm_iteratedFDeriv_le {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    {Φ : B → ℝ} (hΦ : Φ ∈ CbUnitBall B 5) {j : ℕ} (hj : j ≤ 5) (z : B) :
    ‖iteratedFDeriv ℝ j Φ z‖ ≤ 1 := by
  obtain ⟨_, hbdd, hcb⟩ := hΦ
  have h1 : ‖iteratedFDeriv ℝ j Φ z‖ ≤ ⨆ z : B, ‖iteratedFDeriv ℝ j Φ z‖ :=
    le_ciSup (hbdd j hj) z
  have h2 : (⨆ z : B, ‖iteratedFDeriv ℝ j Φ z‖) ≤ cbNorm 5 Φ := by
    unfold cbNorm
    exact Finset.single_le_sum (f := fun j => ⨆ z : B, ‖iteratedFDeriv ℝ j Φ z‖)
      (fun i _ => Real.iSup_nonneg fun _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))
  linarith

/-- `|∫ Φ d(law)| ≤ 1` for a function bounded by `1` and a law of a map (a probability measure or `0`). -/
theorem u6_abs_integral_law_le {Ω B : Type*} [MeasurableSpace Ω] [MeasurableSpace B]
    (P : Measure Ω) [IsProbabilityMeasure P] (f : Ω → B) (Φ : B → ℝ) (h : ∀ z, |Φ z| ≤ 1) :
    |∫ z, Φ z ∂(P.map f)| ≤ 1 := by
  have : IsProbabilityMeasure (P.map f) := inferInstance
  have hle : (P.map f).real Set.univ ≤ 1 := by simp
  have := norm_integral_le_of_norm_le_const (μ := P.map f) (f := Φ) (C := 1)
    (Filter.Eventually.of_forall fun z => by simpa using h z)
  rw [Real.norm_eq_abs] at this
  nlinarith [measureReal_nonneg (μ := P.map f) (s := Set.univ)]


variable {S : PreparedData d} {β₀ m : ℝ}

theorem expr_le_proof (T : ℝ) (K : ℝ → projTensor (PathSpace d m T) 3) (C : ℝ) (hC : ∀ a : ℝ, 0 ≤ a → ‖K a‖ ≤ C)
    (x : ExpData S β₀ m T) : x.expr K ≤ 2 * Real.sqrt x.N + C / 6 := by
  have hΦ := x.hΦ
  have habs : ∀ z, |x.Φ z| ≤ 1 := by
    intro z
    have := u6_norm_iteratedFDeriv_le hΦ (j := 0) (by norm_num) z
    rw [norm_iteratedFDeriv_zero] at this
    simpa using this
  have h1 := u6_abs_integral_law_le x.P (HRS.Main.windowZeta m T x.a x.P x.X) x.Φ habs
  have h2 := u6_abs_integral_law_le x.P' (HRS.Main.windowPath m T x.a x.Z) x.Φ habs
  have hKa : ‖K x.a‖ ≤ C := hC x.a x.ha
  have h3 : |∫ ω, ((K x.a : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3)
      (iteratedFDeriv ℝ 3 x.Φ (HRS.Main.windowPath m T x.a x.Z ω)) ∂x.P'| ≤ C := by
    have := norm_integral_le_of_norm_le_const (μ := x.P')
      (f := fun ω => ((K x.a : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3)
        (iteratedFDeriv ℝ 3 x.Φ (HRS.Main.windowPath m T x.a x.Z ω))) (C := C)
      (Filter.Eventually.of_forall fun ω => by
        refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
        have h4 := u6_norm_iteratedFDeriv_le hΦ (j := 3) (by norm_num) (HRS.Main.windowPath m T x.a x.Z ω)
        have h5 : ‖((K x.a : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3)‖ ≤ C := hKa
        calc _ ≤ C * 1 := mul_le_mul h5 h4 (norm_nonneg _) ((norm_nonneg ((K x.a : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3)).trans h5)
          _ = C := mul_one C)
    rw [Real.norm_eq_abs] at this
    simpa using this
  have hC0 : 0 ≤ C := (norm_nonneg ((K x.a : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3)).trans hKa
  unfold ExpData.expr
  have hs : 0 ≤ Real.sqrt x.N := Real.sqrt_nonneg _
  generalize (∫ z, x.Φ z ∂(law x.P (HRS.Main.windowZeta m T x.a x.P x.X))) = A at h1
  generalize (∫ z, x.Φ z ∂(law x.P' (HRS.Main.windowPath m T x.a x.Z))) = B at h2
  generalize (∫ ω, ((K x.a : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3)
    (iteratedFDeriv ℝ 3 x.Φ (HRS.Main.windowPath m T x.a x.Z ω)) ∂x.P') = Cc at h3
  have e1 : |Real.sqrt x.N * (A - B)| ≤ Real.sqrt x.N * 2 := by
    rw [abs_mul, abs_of_nonneg hs]
    exact mul_le_mul_of_nonneg_left ((abs_sub A B).trans (by linarith)) hs
  have e2 : |(1 / 6 : ℝ) * Cc| ≤ C / 6 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 6)]
    linarith
  calc _ ≤ |Real.sqrt x.N * (A - B)| + |(1 / 6 : ℝ) * Cc| := abs_sub _ _
    _ ≤ Real.sqrt x.N * 2 + C / 6 := add_le_add e1 e2
    _ = _ := by ring

end ExprLe


section Embed

variable {S : PreparedData d} {β₀ m : ℝ}

theorem u6_embed_ofMeasureDiff {r m' : ℝ} (hr : (d : ℝ) < 2 * r) (μ ν : Measure (Torus d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    NegSobolev.embed m' (NegSobolev.ofMeasureDiff r μ ν) = NegSobolev.ofMeasureDiff m' μ ν := by
  unfold NegSobolev.embed
  have : (NegSobolev.fourierCoeff (NegSobolev.ofMeasureDiff r μ ν)) =
      fun k => Torus.measureRealCoeff μ k - Torus.measureRealCoeff ν k :=
    funext fun k => NegSobolev.fourierCoeff_ofMeasureDiff hr μ ν k
  rw [this]
  rfl

theorem u6_rLvl_gt (hE : EdgeworthHyp S β₀ m) : rLvl d ≤ m ∧ (d : ℝ) < 2 * rLvl d := by
  have := hE.m_gt
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  unfold rLvl
  constructor <;> linarith

theorem etaE_zetaE_embed_proof (hE : EdgeworthHyp S β₀ m) {N : ℕ} (Q : Measure (Config d N)) [IsProbabilityMeasure Q]
    (x : Config d N) (μ : Measure (Torus d)) [IsProbabilityMeasure μ] :
    etaE m x μ = NegSobolev.embed m (etaE (rLvl d) x μ) ∧
      zetaE m Q x = NegSobolev.embed m (zetaE (rLvl d) Q x) := by
  obtain ⟨hrm, hr⟩ := u6_rLvl_gt hE
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    unfold etaE zetaE
    simp only [Nat.cast_zero, Real.sqrt_zero, zero_smul]
    have := HRS.GF.gfev_embed_smul (d := d) hrm 0 (0 : NegSobolev d (rLvl d))
    simp only [zero_smul] at this
    exact ⟨this.symm, this.symm⟩
  · have := empirical_isProbabilityMeasure hN x
    have := isProbabilityMeasure_meanEmpirical Q hN
    constructor
    · unfold etaE flucE
      rw [HRS.GF.gfev_embed_smul hrm, u6_embed_ofMeasureDiff hr]
    · unfold zetaE
      rw [HRS.GF.gfev_embed_smul hrm, u6_embed_ofMeasureDiff hr]

end Embed

section QuadField

variable {S : PreparedData d} {β₀ m : ℝ}

theorem quadFieldAt_embed_proof (hE : EdgeworthHyp S β₀ m) (N : ℕ) (hN : 2 ≤ N) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
    (X : ℝ≥0 → Ω → Config d N)
    (hreal : PreparedRealization (regime S β₀ hE).D P
      (modulatedGibbs (periodicRiesz d (regime S β₀ hE).D.s) N (regime S β₀ hE).β₀
        (withDensityReal (regime S β₀ hE).ρ₀)) X₀ W X) (t : ℝ) (ht : 0 ≤ t) (ω : Ω) :
    quadFieldAt m (regime S β₀ hE).D.s (fun t => withDensityReal ((regime S β₀ hE).ρ t)) P X t ω =
      NegSobolev.embed m (quadFieldAt (rLvl d) (regime S β₀ hE).D.s
        (fun t => withDensityReal ((regime S β₀ hE).ρ t)) P X t ω) := by
  obtain ⟨hrm, hr⟩ := u6_rLvl_gt hE
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hr2 : (d : ℝ) < 2 * (rLvl d - 2) := by unfold rLvl; linarith
  have hint := HRS.MC.Sec7.S7PIM.S7PIM_integrable_tilde (regime S β₀ hE) (rLvl d) rfl hN P X₀ W X hreal ht
  exact HRS.MC.Sec7.S7PIM.S7PIM_B_embed (regime S β₀ hE) hr2 hrm (by omega) P X ht hint ω

end QuadField

end HRS.MC.E213U6

end

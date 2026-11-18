import HRS.MS.GenPathAux2
import HRS.MS.StarTie
import HRS.MH.CoercTestTie

/-!
# S5.6 packet P1, part 2: the pathwise covariance error `‖C_r - C̄_r‖_{𝔖₁}` (`W:r2:trace-comparison`, S L3440-3458)

`s56_trace_pathwise`: for a setup `S : WholeSetup b` (`b = { b₀ with C₀ := b.C₀ }`, `b.C₀ ≥ C₀min`), a particle number
`N ≥ 2`, a time `r ∈ [0,T]`, a collision-free configuration `X` and `R ≥ 1`, the trace norm of the difference of the
covariation forms of the empirical measure and of the density `ρ_N^r` satisfies
`‖C_r - C̄_r‖₁ ≤ C q [R^{d/2}(N^{-1/d} + (F_N(X,ρ_N^r) + o_N)^{1/2}) + (⟨|x|²,μ_N⟩ + ⟨|x|²,ρ_N^r⟩)/R²]`.
Proof: test inequality `test_cutoff_pathwise` (S.A.19) applied to `h_A(x) = ∑_a ⟨AΓ_a(x),Γ_a(x)⟩` (`s56_trace_generic`),
bounded derivatives of the features (`general_orbits_features_proof`), `oNΛ ≤ oN` for `C₀ ≥ C₀min`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

namespace HRS.MS.GenPath

open HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

variable {d : ℕ}

theorem s56_valid_of_eq {b₀ b : WholeBounds d} (hb : b₀.Valid) (h : b = { b₀ with C₀ := b.C₀ }) :
    b.Valid := by
  rw [h]
  exact ⟨hb.hd, hb.hs0, hb.hsd, hb.hT, hb.hQ, hb.hθ, hb.hk, hb.hm, hb.hL, hb.hν⟩

theorem s56_rho_le (b : WholeBounds d) (hb : b.Valid) (S : WholeSetup b) (N : ℕ) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) b.T) (x : Euc d) : S.ρ N r x ≤ 2 * max b.Λ 0 := by
  have hdL : (d : ℝ) + 3 ≤ b.L := by
    have := hb.hL; have h0 : (0 : ℝ) ≤ b.k := Nat.cast_nonneg _
    have h1 := hb.hs0; have h2 : (0 : ℝ) ≤ d := Nat.cast_nonneg _; linarith
  obtain ⟨hmem, -, hle⟩ := HRS.MS.Go.s55f_regular_slice (n := b.k + 6 + ⌈(d : ℝ) / 2⌉₊) 0
    (Nat.zero_le _) hdL (S.dens N r hr).1 (S.dens N r hr).2
  have hnn : 0 ≤ (weightedSupE 0 ((d : ℝ) + 3) (S.ρ N r)).toReal := ENNReal.toReal_nonneg
  have hcb : HRS.cbNorm 0 (S.ρ N r) ≤ 2 * max b.Λ 0 := by
    have : (∑ j ∈ Finset.range (0 + 1), (d : ℝ) ^ j + 1) * max b.Λ 0 = 2 * max b.Λ 0 := by
      rw [zero_add, Finset.sum_range_one, pow_zero]; ring
    linarith
  have hx : ‖S.ρ N r x‖ ≤ HRS.cbNorm 0 (S.ρ N r) := by
    unfold HRS.cbNorm
    simp only [zero_add, Finset.range_one, Finset.sum_singleton]
    have := le_ciSup (hmem.2 0 le_rfl) x
    simpa [norm_iteratedFDeriv_zero] using this
  exact (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact hx.trans hcb)

theorem s56_secondMoment_nonneg (μ : Measure (Euc d)) : 0 ≤ secondMomentOf μ :=
  integral_nonneg fun x => sq_nonneg _

theorem s56_trace_pathwise (b₀ : WholeBounds d) (hb : b₀.Valid) :
    ∃ C₀min : ℝ, ∀ b : WholeBounds d, b = { b₀ with C₀ := b.C₀ } → C₀min ≤ b.C₀ →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ S : WholeSetup b, ∀ N : ℕ, 2 ≤ N → ∀ q : ℝ, 0 ≤ q →
      ∀ r ∈ Set.Icc (0 : ℝ) b.T, ∀ X : EucConfig d N, Function.Injective X → ∀ R : ℝ, 1 ≤ R →
      ∀ B₁ B₂ : KSpace d b.m b.T →L[ℝ] KSpace d b.m b.T →L[ℝ] ℝ,
      (∀ u v, B₁ u v = featureForm b.m b.T q (fun a => gradFeature (S.coeff N) b.m b.T a r)
        (HRS.Whole.empirical X) u v) →
      (∀ u v, B₂ u v = featureForm b.m b.T q (fun a => gradFeature (S.coeff N) b.m b.T a r)
        (HRS.Whole.withDensityReal (S.ρ N r)) u v) →
      HRS.traceNormForm (B₁ - B₂) ≤ C * q *
        (R ^ ((d : ℝ) / 2) * ((N : ℝ) ^ (-(1 : ℝ) / d) +
            Real.sqrt (rieszModulatedEnergy d b.s X (HRS.Whole.withDensityReal (S.ρ N r)) +
              HRS.oN d b.s b.C₀ N)) +
          (secondMomentOf (HRS.Whole.empirical X) + secondMomentOf (HRS.Whole.withDensityReal (S.ρ N r))) / R ^ 2) := by
  have hd1 : 1 ≤ d := by have := hb.hd; omega
  obtain ⟨C₀p, C₁, hC₀p, hpair⟩ := HRS.MH.CoercTest.p_assembly d hd1 b₀.s hb.hs0 hb.hsd
  obtain ⟨χ, hχ⟩ := HRS.MS.Ul.ul0_exists_ulocCutoff d
  obtain ⟨Ct, hCt⟩ := test_cutoff_pathwise hd1 b₀.s hb.hs0 hb.hsd χ hχ C₁
  obtain ⟨Cn, hCn0, hCnb⟩ := s56_cNormE_le hχ
  set Λ₁ : ℝ := max (2 * max b₀.Λ 0) 1 with hΛ₁
  have hΛ₁1 : 1 ≤ Λ₁ := le_max_right _ _
  refine ⟨C₀p * Λ₁ ^ (b₀.s / d) + Real.log Λ₁ / (2 * d), fun b hbeq hC0 => ?_⟩
  have hbv : b.Valid := s56_valid_of_eq hb hbeq
  have hs : b.s = b₀.s := by
    have h := congrArg WholeBounds.s hbeq
    exact h
  have hΛ : b.Λ = b₀.Λ := by
    have h := congrArg WholeBounds.Λ hbeq
    exact h
  obtain ⟨Cf, hCf⟩ := HRS.MS.Star.general_orbits_features_proof b hbv
  have hkk : mStar d - 1 ≤ b.k := by
    have h1 := hbv.hk
    have h2 : ((d / 2 : ℕ) : ℝ) ≤ (d : ℝ) / 2 := Nat.cast_div_le
    have : (d / 2 + 2 : ℕ) ≤ b.k := by
      exact_mod_cast (show ((d / 2 : ℕ) : ℝ) + 2 ≤ b.k by push_cast; linarith)
    unfold mStar; omega
  set B : ℝ := max Cf 0 with hBdef
  set Cc : ℝ := max Ct 0 with hCcdef
  refine ⟨2 * d * (Cc * (Cn * (2 ^ (mStar d - 1) * B ^ 2))), by positivity,
    fun S N hN q hq r hr X hX R hR B₁ B₂ h1 h2 => ?_⟩
  have hprob : HRS.Whole.IsProbDensity (S.ρ N r) := (S.mf N).density r hr
  haveI : IsProbabilityMeasure (HRS.Whole.empirical X) := HRS.Whole.empirical_isProbabilityMeasure (by omega) X
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal (S.ρ N r)) := Q09A.measure_isProb hprob
  have hρle : ∀ x, S.ρ N r x ≤ Λ₁ := fun x =>
    (s56_rho_le b hbv S N hr x).trans (by rw [hΛ]; exact le_max_left _ _)
  have hmom : Integrable (fun x => ‖x‖ ^ 2 * S.ρ N r x) := (S.mf N).second_moment r hr
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
  set Err : ℝ := R ^ ((d : ℝ) / 2) * ((N : ℝ) ^ (-(1 : ℝ) / d) +
            Real.sqrt (rieszModulatedEnergy d b.s X (HRS.Whole.withDensityReal (S.ρ N r)) +
              HRS.oN d b.s b.C₀ N)) +
          (secondMomentOf (HRS.Whole.empirical X) + secondMomentOf (HRS.Whole.withDensityReal (S.ρ N r))) / R ^ 2
    with hErr
  have hRpos : 0 < R := by linarith
  have hErr0 : 0 ≤ Err := by
    have := s56_secondMoment_nonneg (HRS.Whole.empirical X)
    have := s56_secondMoment_nonneg (HRS.Whole.withDensityReal (S.ρ N r))
    positivity
  have hTest : ∀ h : Euc d → ℝ, cNormE χ h < ⊤ →
      abs (HRS.Whole.pair (HRS.Whole.empirical X) h - HRS.Whole.pair (HRS.Whole.withDensityReal (S.ρ N r)) h) ≤
        Cc * (cNormE χ h).toReal * Err := by
    intro h hh
    have key := hCt C₀p (hpair C₀p le_rfl) Λ₁ hΛ₁1 N hN (S.ρ N r) hprob hρle hmom X hX h hh R hR
    refine key.trans ?_
    have hsm : HRS.smearScale d N Λ₁ ≤ (N : ℝ) ^ (-(1 : ℝ) / d) := by
      unfold HRS.smearScale
      exact Real.rpow_le_rpow_of_nonpos hNpos (by nlinarith) (by
        have : (0 : ℝ) ≤ 1 / d := by positivity
        rw [neg_div]; linarith)
    have hon : HRS.oNΛ d b₀.s C₀p Λ₁ N ≤ HRS.oN d b.s b.C₀ N := by
      rw [hs]
      exact s56_oNL_le hd1 hΛ₁1 hC0 N hN
    have hsq : Real.sqrt (rieszModulatedEnergy d b₀.s X (HRS.Whole.withDensityReal (S.ρ N r)) +
        HRS.oNΛ d b₀.s C₀p Λ₁ N) ≤ Real.sqrt (rieszModulatedEnergy d b.s X (HRS.Whole.withDensityReal (S.ρ N r)) +
          HRS.oN d b.s b.C₀ N) := by
      apply Real.sqrt_le_sqrt
      rw [hs] at hon ⊢
      linarith
    have hE1 : R ^ ((d : ℝ) / 2) * (HRS.smearScale d N Λ₁ + Real.sqrt (rieszModulatedEnergy d b₀.s X
          (HRS.Whole.withDensityReal (S.ρ N r)) + HRS.oNΛ d b₀.s C₀p Λ₁ N)) +
        (secondMomentOf (HRS.Whole.empirical X) + secondMomentOf (HRS.Whole.withDensityReal (S.ρ N r))) / R ^ 2 ≤ Err := by
      rw [hErr]
      have hsq' : Real.sqrt (rieszModulatedEnergy d b₀.s X (HRS.Whole.withDensityReal (S.ρ N r)) +
          HRS.oNΛ d b₀.s C₀p Λ₁ N) ≤ Real.sqrt (rieszModulatedEnergy d b₀.s X
            (HRS.Whole.withDensityReal (S.ρ N r)) + HRS.oN d b₀.s b.C₀ N) := by
        rw [hs] at hon; apply Real.sqrt_le_sqrt; linarith
      rw [hs]
      gcongr
    have hE0 : 0 ≤ R ^ ((d : ℝ) / 2) * (HRS.smearScale d N Λ₁ + Real.sqrt (rieszModulatedEnergy d b₀.s X
          (HRS.Whole.withDensityReal (S.ρ N r)) + HRS.oNΛ d b₀.s C₀p Λ₁ N)) +
        (secondMomentOf (HRS.Whole.empirical X) + secondMomentOf (HRS.Whole.withDensityReal (S.ρ N r))) / R ^ 2 := by
      have := s56_secondMoment_nonneg (HRS.Whole.empirical X)
      have := s56_secondMoment_nonneg (HRS.Whole.withDensityReal (S.ρ N r))
      have : 0 ≤ HRS.smearScale d N Λ₁ := by unfold HRS.smearScale; positivity
      positivity
    have hnn : 0 ≤ (cNormE χ h).toReal := ENNReal.toReal_nonneg
    exact mul_le_mul (mul_le_mul_of_nonneg_right (le_max_left _ _) hnn) hE1 hE0
      (mul_nonneg (le_max_right _ _) hnn)
  have hΓ : ∀ a : Fin d, ContDiff ℝ ((mStar d - 1 : ℕ) : WithTop ℕ∞)
      (fun x => gradFeature (S.coeff N) b.m b.T a r x) := fun a =>
    (hCf S N a r hr).1.of_le (by exact_mod_cast hkk)
  have hB : ∀ a : Fin d, ∀ j ≤ mStar d - 1, ∀ x,
      ‖iteratedFDeriv ℝ j (fun y => gradFeature (S.coeff N) b.m b.T a r y) x‖ ≤ B := fun a j hj x =>
    ((hCf S N a r hr).2 j (hj.trans hkk) x).trans (le_max_left _ _)
  have hgen := s56_trace_generic (d := d) (χ := χ) (Cn := Cn) hCn0 hCnb
    (fun a x => gradFeature (S.coeff N) b.m b.T a r x) B hΓ hB (HRS.Whole.empirical X)
    (HRS.Whole.withDensityReal (S.ρ N r)) (Cc := Cc) (Err := Err) (le_max_right _ _) hErr0 hTest hq B₁ B₂
    (fun u v => (h1 u v).trans rfl) (fun u v => (h2 u v).trans rfl)
  exact hgen.trans (le_of_eq (by ring))

end HRS.MS.GenPath

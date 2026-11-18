/-
# HRS.Dynamics.InitialData — initial modulated energy and initial fluctuation data (APPA-02)

Appendix A, Section "Verification: initial data" of the main manuscript (source lines
11490-11640), together with the static parts of Examples A.16/A.17 (source lines 10450-10483)
and the elementary scale limits `H:eq:balanced-weights` (source lines 636-646).

* Lemma A.35 `M:B:lem:initial-energy` (lines 11498-11513): (i) first display (uniform form),
  second display (`B:eq:initial-energy-second-moment`), the "automatic" squared-kernel
  condition, and the static content of (ii).  The exact expectation identity of (i) is
  `HRS.expectation_modulatedEnergy_iid` (ENER-01) and is not restated.
* Lemma A.36 `M:B:lem:iid-init` (lines 11544-11550): (I2) and the finite-family coupling
  `B:eq:iid-coupling`.
* Lemma A.38 `M:B:lem:iid-init-field` (lines 11581-11587): the field-level coupling
  `B:eq:iid-init-field` and the second-moment bound.  (Lemma A.37, Yurinskii, is
  `HRS.yurinskii_coupling` in `HRS/Prob/Metrics.lean`.)
* Example A.39 `M:B:ex:lattice` (lines 11608-11612): the perturbed-lattice statistic and field
  estimates and the (external) lattice energy bound.
* Example A.17 `M:B:ex:iid` (lines 10469-10483): existence of the Gaussian initial field with
  the bridge covariance; the central-limit scaling condition `s < d/2`.
* `H:eq:balanced-weights` and the two degenerate limits (lines 636-646).

Representation conventions.
* `μ° = ρ dx` with `ρ` a probability density bounded by `Λ` (`μ° ∈ 𝒫 ∩ L^∞`).
* The Gaussian field `η°` is a law `ν` on `E_m = H^{-m}_0(𝕋^d)` with
  `IsCenteredGaussianWithCov m ν (iidCov μ°)`.
* Second moments are `lintegral`s, so a non-integrable integrand cannot make a bound vacuous;
  couplings are random elements on an explicit probability space with prescribed laws.
-/
import HRS.Dynamics.Setup
import HRS.PDE.TorusCalculus
import HRS.Prob.HilbertCLT
import HRS.Energy.Coercivity
import HRS.Kernel.GradSmooth
import HRS.Kernel.D1

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d : ℕ}

/-! ### Lemma A.35: initial modulated energy -/

/-- `o'_N = 1_{s=0} log N / N + Λ^{s/d} N^{s/d-1}` (Lemma A.35 (i), source line 11502; the
constant `C` in front of the second summand is absorbed into the constants of the statements). -/
def oPrime (d : ℕ) (s Λ : ℝ) (N : ℕ) : ℝ :=
  (if s = 0 then Real.log N / N else 0) + Λ ^ (s / d) * (N : ℝ) ^ (s / d - 1)

namespace InitialDataAux

lemma isProb_withDensityReal {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) :
    IsProbabilityMeasure (withDensityReal ρ) := by
  have hint : Integrable ρ := Integrable.of_integral_ne_zero (by rw [hρ.integral_one]; exact one_ne_zero)
  refine ⟨?_⟩
  rw [withDensityReal, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hρ.nonneg),
    hρ.integral_one]
  simp

lemma one_le_of_probDensity {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) (Λ : ℝ)
    (hΛ : ∀ x, ρ x ≤ Λ) : 1 ≤ Λ := by
  have hint : Integrable ρ := Integrable.of_integral_ne_zero (by rw [hρ.integral_one]; exact one_ne_zero)
  have := integral_mono hint (integrable_const Λ) hΛ
  rw [hρ.integral_one] at this
  simpa using this

lemma withDensityReal_ac (ρ : Torus d → ℝ) : withDensityReal ρ ≪ (volume : Measure (Torus d)) :=
  withDensity_absolutelyContinuous _ _

lemma integrable_energy (g : Torus d → ℝ) (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (hint : Integrable (fun p : Torus d × Torus d => g (p.1 - p.2)) (μ.prod μ)) (N : ℕ) :
    Integrable (fun X : Config d N => modulatedEnergyKernel g X μ)
      (Measure.pi fun _ : Fin N => μ) := by
  have hpair : ∀ i j : Fin N, i ≠ j →
      Integrable (fun X : Config d N => g (X i - X j)) (Measure.pi fun _ : Fin N => μ) :=
    fun i j hij => integrable_pair_comp μ hij (H := fun p => g (p.1 - p.2)) hint
  have hconv_int : Integrable (fun x => ∫ y, g (x - y) ∂μ) μ := hint.integral_prod_left
  have h1 : ∀ i : Fin N, Integrable (fun X : Config d N => ∫ y, g (X i - y) ∂μ)
      (Measure.pi fun _ : Fin N => μ) := fun i =>
    integrable_comp_eval (μ := fun _ : Fin N => μ) (i := i) hconv_int
  have hT1 : Integrable (fun X : Config d N => ∑ i, ∑ j ∈ Finset.univ.erase i, g (X i - X j))
      (Measure.pi fun _ : Fin N => μ) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j hj =>
      hpair i j (Finset.ne_of_mem_erase hj).symm
  have hT2 : Integrable (fun X : Config d N => ∑ i, ∫ y, g (X i - y) ∂μ)
      (Measure.pi fun _ : Fin N => μ) := integrable_finsetSum _ fun i _ => h1 i
  unfold modulatedEnergyKernel modulatedEnergy
  exact ((hT1.const_mul _).sub (hT2.const_mul _)).add (integrable_const _)

lemma integrable_conv_shift {g : Torus d → ℝ} (hg : Integrable g) (hgm : AEStronglyMeasurable g volume)
    {ρ : Torus d → ℝ} (Λ : ℝ) (hΛ : ∀ x, ρ x ≤ Λ) (x : Torus d) :
    Integrable (fun y => g (x - y)) (withDensityReal ρ) := by
  have : (volume : Measure (Torus d)).IsNegInvariant :=
    MeasureTheory.Measure.pi.isNegInvariant (fun _ : Fin d => (volume : Measure UnitAddCircle))
  have hqmp : Measure.QuasiMeasurePreserving (fun y : Torus d => x - y) (withDensityReal ρ) volume :=
    ((volume : Measure (Torus d)).measurePreserving_sub_left x).quasiMeasurePreserving.mono_left
      (withDensityReal_ac ρ)
  refine ⟨hgm.comp_quasiMeasurePreserving hqmp, ?_⟩
  unfold HasFiniteIntegral
  refine lt_of_le_of_lt (KernelAux2.lintegral_conv_le ρ Λ hΛ (fun z => ‖g z‖ₑ) x) ?_
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hg.hasFiniteIntegral


lemma oN_abs_le {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (C₀ Λ : ℝ) (hΛ : 1 ≤ Λ) (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ)⁻¹ ≤ oPrime d s Λ N ∧ |oN d s C₀ N| ≤ (|C₀| + 1) * oPrime d s Λ N ∧ 0 ≤ oPrime d s Λ N := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  set q : ℝ := (N : ℝ) ^ (s / d - 1) with hq
  have hqpos : 0 < q := Real.rpow_pos_of_pos hNpos _
  have hinv : (N : ℝ)⁻¹ ≤ q := by
    rw [hq, ← Real.rpow_neg_one]
    have h0 : 0 ≤ s / d := by positivity
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hΛq : 1 ≤ Λ ^ (s / (d : ℝ)) := Real.one_le_rpow hΛ (by positivity)
  set L : ℝ := (if s = 0 then Real.log N / N else 0) with hL
  have hL0 : 0 ≤ L := by
    rw [hL]; split_ifs
    · exact div_nonneg (Real.log_nonneg hN1) hNpos.le
    · exact le_rfl
  have hop : oPrime d s Λ N = L + Λ ^ (s / (d : ℝ)) * q := rfl
  have hop1 : q ≤ Λ ^ (s / (d : ℝ)) * q := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · rw [hop]; linarith
  · have hoN : oN d s C₀ N = C₀ * q + (if s = 0 then Real.log N / (2 * d * N) else 0) := rfl
    have h2 : |(if s = 0 then Real.log N / (2 * d * N) else 0)| ≤ L := by
      rw [hL]; split_ifs
      · rw [abs_of_nonneg (div_nonneg (Real.log_nonneg hN1) (by positivity))]
        apply div_le_div_of_nonneg_left (Real.log_nonneg hN1) hNpos
        nlinarith
      · simp
    calc |oN d s C₀ N| ≤ |C₀ * q| + |(if s = 0 then Real.log N / (2 * d * N) else 0)| := by
          rw [hoN]; exact abs_add_le _ _
      _ ≤ |C₀| * q + L := by rw [abs_mul, abs_of_pos hqpos]; linarith
      _ ≤ (|C₀| + 1) * (L + Λ ^ (s / (d : ℝ)) * q) := by
          nlinarith [abs_nonneg C₀, mul_nonneg (abs_nonneg C₀) hL0]
      _ = _ := by rw [hop]
  · rw [hop]; positivity

end InitialDataAux

open InitialDataAux in
/-- Lemma A.35 (i), first display (source lines 11501-11502): for i.i.d. data
`X ∼ (μ°)^{⊗N}` with `μ° = ρ dx`, `ρ ≤ Λ`, `∬|g| d(μ°)^{⊗2} < ∞`,
`𝓔_N^0 = E[F_N(X, μ°) + o_N] ≤ C (N⁻¹ + o_N) ≤ C o'_N`.  The constant depends only on
`d, s, C₀, Λ` (uniform over the densities), and `F_N` is integrable, so the Bochner
expectation is the true one. -/
theorem initial_energy_iid_mean {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (C₀ Λ : ℝ) :
    ∃ C : ℝ, ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      Integrable (fun p : Torus d × Torus d => periodicRiesz d s (p.1 - p.2))
        ((withDensityReal ρ).prod (withDensityReal ρ)) →
      ∀ N : ℕ, 2 ≤ N →
        Integrable (fun X : Config d N => rieszEnergy d s X (withDensityReal ρ))
            (Measure.pi fun _ => withDensityReal ρ) ∧
          ∫ X : Config d N, (rieszEnergy d s X (withDensityReal ρ) + oN d s C₀ N)
              ∂(Measure.pi fun _ => withDensityReal ρ) ≤ C * ((N : ℝ)⁻¹ + |oN d s C₀ N|) ∧
          ∫ X : Config d N, (rieszEnergy d s X (withDensityReal ρ) + oN d s C₀ N)
              ∂(Measure.pi fun _ => withDensityReal ρ) ≤ C * oPrime d s Λ N := by
  obtain ⟨B, hB⟩ := periodicRiesz_ge (d := d) (s := s) hd hs0 hsd
  have hgi := KernelAux.integrable_periodicRiesz (d := d) (s := s) hd hs0 hsd
  have hgm := KernelAux.aestronglyMeasurable_periodicRiesz (d := d) (s := s) hd hs0 hsd
  refine ⟨|B| / 2 + |C₀| + 1, fun ρ hρ hΛ hint N hN => ?_⟩
  have hprob := isProb_withDensityReal hρ
  set μ := withDensityReal ρ with hμ
  have hΛ1 := one_le_of_probDensity hρ Λ hΛ
  have hF : Integrable (fun X : Config d N => rieszEnergy d s X μ) (Measure.pi fun _ : Fin N => μ) :=
    integrable_energy (periodicRiesz d s) μ hint N
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hmean := expectation_modulatedEnergy_iid (periodicRiesz d s) μ (N := N) hN1 hint
    (integrable_conv_shift hgi hgm Λ hΛ)
  have hG : -|B| ≤ ∫ p : Torus d × Torus d, periodicRiesz d s (p.1 - p.2) ∂(μ.prod μ) := by
    have h := integral_mono (integrable_const (-|B|)) hint (f := fun _ => -|B|)
      (fun p => (neg_le_neg (le_abs_self B)).trans (hB (p.1 - p.2)))
    simpa using h
  have hEF : ∫ X : Config d N, rieszEnergy d s X μ ∂(Measure.pi fun _ : Fin N => μ) ≤
      |B| / 2 * (N : ℝ)⁻¹ := by
    have : ∫ X : Config d N, rieszEnergy d s X μ ∂(Measure.pi fun _ : Fin N => μ) =
        -(1 / (2 * (N : ℝ))) * ∫ p : Torus d × Torus d, periodicRiesz d s (p.1 - p.2) ∂(μ.prod μ) :=
      hmean
    rw [this]
    have h1 : 0 < 1 / (2 * (N : ℝ)) := by positivity
    have := mul_le_mul_of_nonneg_left (neg_le_neg hG) h1.le
    calc _ = -(1 / (2 * (N : ℝ))) * ∫ p : Torus d × Torus d, periodicRiesz d s (p.1 - p.2) ∂(μ.prod μ) := rfl
      _ = (1 / (2 * (N : ℝ))) * (-∫ p : Torus d × Torus d, periodicRiesz d s (p.1 - p.2) ∂(μ.prod μ)) := by ring
      _ ≤ (1 / (2 * (N : ℝ))) * (-(-|B|)) := mul_le_mul_of_nonneg_left (neg_le_neg hG) h1.le
      _ = |B| / 2 * (N : ℝ)⁻¹ := by field_simp
  have hint_sum : ∫ X : Config d N, (rieszEnergy d s X μ + oN d s C₀ N) ∂(Measure.pi fun _ : Fin N => μ) =
      ∫ X : Config d N, rieszEnergy d s X μ ∂(Measure.pi fun _ : Fin N => μ) + oN d s C₀ N := by
    rw [integral_add hF (integrable_const _), integral_const]
    simp
  obtain ⟨h1, h2, h3⟩ := oN_abs_le hd hs0 C₀ Λ hΛ1 N hN1
  refine ⟨hF, ?_, ?_⟩
  · rw [hint_sum]
    have := le_abs_self (oN d s C₀ N)
    have hB0 := abs_nonneg B
    have hC0 := abs_nonneg C₀
    have hinv : 0 ≤ (N : ℝ)⁻¹ := by positivity
    nlinarith [mul_nonneg hB0 hinv, mul_nonneg hC0 hinv, mul_nonneg hC0 (abs_nonneg (oN d s C₀ N)),
      mul_nonneg hB0 (abs_nonneg (oN d s C₀ N)), abs_nonneg (oN d s C₀ N)]
  · rw [hint_sum]
    have := le_abs_self (oN d s C₀ N)
    have hB0 := abs_nonneg B
    have hC0 := abs_nonneg C₀
    nlinarith [mul_nonneg hB0 h3, mul_nonneg hC0 h3]

namespace InitialDataAux

open KernelAux KernelAux2

/-- local bound: `|g(x)| ≤ c |x|^{-b} + R` near the origin, `b = (s + d/2)/2`. -/
lemma riesz_local_bound {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) :
    ∃ (δ c R : ℝ), 0 < δ ∧ δ ≤ 1 ∧ 0 ≤ c ∧ 0 ≤ R ∧ ∀ x : Euc d, x ≠ 0 → ‖x‖ < δ →
      |periodicRiesz d s (Torus.mk x)| ≤ c * ‖x‖ ^ (-((s + (d : ℝ) / 2) / 2)) + R := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  set b : ℝ := (s + (d : ℝ) / 2) / 2 with hb
  have hbpos : 0 < b := by rw [hb]; positivity
  rcases hs0.eq_or_lt with h0 | h0
  · subst h0
    obtain ⟨r, δ, hδ, hr, hloc⟩ := periodicLog_local_singularity (d := d) hd
    obtain ⟨R, hR⟩ := (isCompact_closedBall (0 : Euc d) 1).exists_bound_of_continuousOn
      (f := Torus.lift r) (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift r) from hr).continuous.continuousOn
    refine ⟨min δ 1, 1 / b, |R|, lt_min hδ one_pos, min_le_right _ _, by positivity, abs_nonneg _, ?_⟩
    intro x hx0 hxn
    have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
    have hx1 : ‖x‖ < 1 := lt_of_lt_of_le hxn (min_le_right _ _)
    have hxδ : ‖x‖ < δ := lt_of_lt_of_le hxn (min_le_left _ _)
    have hg := hloc x hxδ hx0
    have hrR : |r (Torus.mk x)| ≤ |R| := by
      have := hR x (by simpa using hx1.le)
      simp only [Torus.lift, Function.comp, Real.norm_eq_abs] at this
      exact this.trans (le_abs_self _)
    have hlog : -Real.log ‖x‖ ≤ ‖x‖ ^ (-b) / b := by
      have := Real.log_le_rpow_div (inv_nonneg.2 hxpos.le) hbpos
      rw [Real.log_inv, Real.inv_rpow hxpos.le, ← Real.rpow_neg hxpos.le] at this
      exact this
    have hlog0 : 0 ≤ -Real.log ‖x‖ := by
      have := Real.log_neg hxpos hx1; linarith
    rw [hg]
    calc _ ≤ |-Real.log ‖x‖| + |r (Torus.mk x)| := abs_add_le _ _
      _ ≤ _ := by
        rw [abs_of_nonneg hlog0]
        have : 1 / b * ‖x‖ ^ (-b) = ‖x‖ ^ (-b) / b := by ring
        simp only [zero_add] at *
        linarith
  · obtain ⟨r, δ, hδ, hr, hloc⟩ := periodicRiesz_local_singularity (d := d) (s := s) hd h0 (by linarith)
    obtain ⟨R, hR⟩ := (isCompact_closedBall (0 : Euc d) 1).exists_bound_of_continuousOn
      (f := Torus.lift r) (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift r) from hr).continuous.continuousOn
    refine ⟨min δ 1, 1, |R|, lt_min hδ one_pos, min_le_right _ _, zero_le_one, abs_nonneg _, ?_⟩
    intro x hx0 hxn
    have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
    have hx1 : ‖x‖ < 1 := lt_of_lt_of_le hxn (min_le_right _ _)
    have hxδ : ‖x‖ < δ := lt_of_lt_of_le hxn (min_le_left _ _)
    have hg := hloc x hxδ hx0
    have hrR : |r (Torus.mk x)| ≤ |R| := by
      have := hR x (by simpa using hx1.le)
      simp only [Torus.lift, Function.comp, Real.norm_eq_abs] at this
      exact this.trans (le_abs_self _)
    have h1 : ‖x‖ ^ (-s) ≤ ‖x‖ ^ (-b) :=
      Real.rpow_le_rpow_of_exponent_ge hxpos hx1.le (by rw [hb]; linarith)
    rw [hg]
    calc _ ≤ |‖x‖ ^ (-s)| + |r (Torus.mk x)| := abs_add_le _ _
      _ ≤ _ := by
        rw [abs_of_nonneg (Real.rpow_nonneg hxpos.le _)]
        linarith


lemma riesz_sq_box {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) :
    ∃ K1 K2 : ℝ, 0 ≤ K1 ∧ 0 ≤ K2 ∧ ∀ y : Fin d → ℝ, y ∈ Box d → y ≠ 0 →
      periodicRiesz d s (boxPt y) ^ 2 ≤ K1 * ‖y‖ ^ (-(s + (d : ℝ) / 2)) + K2 := by
  have hd0 : 0 < d := by omega
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨δ, c, R, hδ, hδ1, hc, hR, hloc⟩ := riesz_local_bound (d := d) (s := s) hd hs0 hs
  obtain ⟨C1, C2, hC1, hC2, hbd⟩ := periodicRiesz_box_bound (d := d) (s := s) hd hs0 (by linarith)
  set θ : ℝ := δ / d with hθ
  have hθ0 : 0 < θ := by positivity
  set M : ℝ := C1 * θ ^ (-((s + (d:ℝ)) / 2)) + C2 with hM
  have hM0 : 0 ≤ M := by positivity
  refine ⟨2 * c ^ 2, M ^ 2 + 2 * R ^ 2, by positivity, by positivity, fun y hyB hy => ?_⟩
  have hypos : 0 < ‖y‖ := norm_pos_iff.2 hy
  have hrp : 0 ≤ 2 * c ^ 2 * ‖y‖ ^ (-(s + (d : ℝ) / 2)) :=
    mul_nonneg (by positivity) (Real.rpow_nonneg (norm_nonneg _) _)
  by_cases hcase : θ ≤ ‖y‖
  · have h1 := hbd y hyB hy
    have h2 : ‖y‖ ^ (-((s + (d:ℝ)) / 2)) ≤ θ ^ (-((s + (d:ℝ)) / 2)) :=
      Real.rpow_le_rpow_of_nonpos hθ0 hcase (by have : (0:ℝ) ≤ (s + (d:ℝ))/2 := by positivity
                                                linarith)
    have h3 : |periodicRiesz d s (boxPt y)| ≤ M := by
      refine h1.trans ?_
      rw [hM]
      have := mul_le_mul_of_nonneg_left h2 hC1
      linarith
    have h4 : periodicRiesz d s (boxPt y) ^ 2 ≤ M ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h3 2
    nlinarith [sq_nonneg R]
  · replace hcase := not_le.1 hcase
    set x : Euc d := WithLp.toLp 2 y with hx
    have hxn : ‖x‖ < δ := by
      have := norm_toLp_le_card_mul hd0 y
      have hdpos : (0:ℝ) < d := by positivity
      calc ‖x‖ ≤ d * ‖y‖ := this
        _ < d * θ := by gcongr
        _ = δ := by rw [hθ]; field_simp
    have hx0 : x ≠ 0 := by
      intro h0
      apply hy
      ext i
      have := congrArg (fun z : Euc d => z i) h0
      simpa [hx] using this
    have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
    have hg : |periodicRiesz d s (boxPt y)| ≤ c * ‖x‖ ^ (-((s + (d : ℝ) / 2) / 2)) + R := hloc x hx0 hxn
    have h5 : ‖x‖ ^ (-((s + (d : ℝ) / 2) / 2)) ≤ ‖y‖ ^ (-((s + (d : ℝ) / 2) / 2)) :=
      Real.rpow_le_rpow_of_nonpos hypos (norm_le_norm_toLp y) (by
        have : 0 ≤ (s + (d : ℝ) / 2) / 2 := by positivity
        linarith)
    have h6 : |periodicRiesz d s (boxPt y)| ≤ c * ‖y‖ ^ (-((s + (d : ℝ) / 2) / 2)) + R :=
      hg.trans (by have := mul_le_mul_of_nonneg_left h5 hc; linarith)
    have h7 : periodicRiesz d s (boxPt y) ^ 2 ≤ (c * ‖y‖ ^ (-((s + (d : ℝ) / 2) / 2)) + R) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h6 2
    have h8 : (‖y‖ ^ (-((s + (d : ℝ) / 2) / 2))) ^ 2 = ‖y‖ ^ (-(s + (d : ℝ) / 2)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hypos.le]
      congr 1; push_cast; ring
    have h9 : 0 ≤ M ^ 2 := by positivity
    calc _ ≤ _ := h7
      _ ≤ 2 * (c * ‖y‖ ^ (-((s + (d : ℝ) / 2) / 2))) ^ 2 + 2 * R ^ 2 := by nlinarith [sq_nonneg (c * ‖y‖ ^ (-((s + (d : ℝ) / 2) / 2)) - R)]
      _ = 2 * c ^ 2 * ‖y‖ ^ (-(s + (d : ℝ) / 2)) + 2 * R ^ 2 := by rw [mul_pow, h8]; ring
      _ ≤ _ := by linarith

lemma riesz_sq_integrable_volume {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) :
    Integrable (fun x : Torus d => periodicRiesz d s x ^ 2) := by
  have hd0 : 0 < d := by omega
  obtain ⟨K1, K2, hK1, hK2, hbd⟩ := riesz_sq_box (d := d) (s := s) hd hs0 hs
  refine ⟨((aestronglyMeasurable_periodicRiesz hd hs0 (by linarith)).pow 2), ?_⟩
  unfold HasFiniteIntegral
  rw [lintegral_torus_box (fun x => ‖periodicRiesz d s x ^ 2‖ₑ)]
  have hI : IntegrableOn (fun y : Fin d → ℝ => K1 * ‖y‖ ^ (-(s + (d : ℝ) / 2)) + K2) (Box d) :=
    ((integrableOn_Box_rpow hd0 (α := s + (d : ℝ) / 2) (by linarith)).const_mul K1).add
      (integrableOn_const (measure_Box_ne_top d))
  have hne : ∀ᵐ y ∂(volume.restrict (Box d)), y ≠ 0 := ae_restrict_of_ae (ae_ne_pi hd0)
  calc ∫⁻ y in Box d, ‖periodicRiesz d s (boxPt y) ^ 2‖ₑ
      ≤ ∫⁻ y in Box d, ENNReal.ofReal (K1 * ‖y‖ ^ (-(s + (d : ℝ) / 2)) + K2) := by
        refine lintegral_mono_ae ?_
        filter_upwards [hne, ae_restrict_mem (measurableSet_Box d)] with y hy hyB
        rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (hbd y hyB hy)
    _ = ∫⁻ y in Box d, ‖K1 * ‖y‖ ^ (-(s + (d : ℝ) / 2)) + K2‖ₑ := by
        refine lintegral_congr fun y => ?_
        rw [Real.enorm_of_nonneg (by positivity)]
    _ < ∞ := hI.2


lemma qmp_sub (μ : Measure (Torus d)) [SFinite μ] (hμ : μ ≪ volume) :
    Measure.QuasiMeasurePreserving (fun z : Torus d × Torus d => z.1 - z.2) (μ.prod μ) volume := by
  have h2 : MeasurePreserving (fun z : Torus d × Torus d => z.1 - z.2)
      ((volume : Measure (Torus d)).prod volume) volume :=
    (measurePreserving_fst (μ := (volume : Measure (Torus d))) (ν := (volume : Measure (Torus d)))).comp
      (measurePreserving_sub_prod (volume : Measure (Torus d)) (volume : Measure (Torus d)))
  exact h2.quasiMeasurePreserving.mono_left (hμ.prod hμ)

lemma lintegral_prod_conv_le {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) (Λ : ℝ) (hΛ : ∀ x, ρ x ≤ Λ)
    (F : Torus d → ℝ≥0∞) (hF : AEMeasurable (fun p : Torus d × Torus d => F (p.1 - p.2))
      ((withDensityReal ρ).prod (withDensityReal ρ))) :
    ∫⁻ p : Torus d × Torus d, F (p.1 - p.2) ∂((withDensityReal ρ).prod (withDensityReal ρ)) ≤
      ENNReal.ofReal Λ * ∫⁻ y, F y := by
  have := isProb_withDensityReal hρ
  rw [lintegral_prod _ hF]
  show ∫⁻ x, ∫⁻ y, F (x - y) ∂(withDensityReal ρ) ∂(withDensityReal ρ) ≤ _
  calc _ ≤ ∫⁻ _x, (ENNReal.ofReal Λ * ∫⁻ y, F y) ∂(withDensityReal ρ) :=
        lintegral_mono fun x => lintegral_conv_le ρ Λ hΛ F x
    _ = _ := by rw [lintegral_const, measure_univ, mul_one]

end InitialDataAux

open InitialDataAux in
/-- Lemma A.35 (i), the "automatic" squared-kernel condition (source lines 11507-11509): for
`0 ≤ s < d/2` and a bounded probability density, `∬ g(x-y)² d(μ°)^{⊗2} < ∞`. -/
theorem periodicRiesz_sq_integrable {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ρ : Torus d → ℝ) (hρ : IsProbDensity ρ) (Λ : ℝ) (hΛ : ∀ x, ρ x ≤ Λ) :
    Integrable (fun p : Torus d × Torus d => periodicRiesz d s (p.1 - p.2) ^ 2)
      ((withDensityReal ρ).prod (withDensityReal ρ)) := by
  have := isProb_withDensityReal hρ
  have hvol := riesz_sq_integrable_volume (d := d) (s := s) hd hs0 hs
  have hm : AEStronglyMeasurable (fun p : Torus d × Torus d => periodicRiesz d s (p.1 - p.2))
      ((withDensityReal ρ).prod (withDensityReal ρ)) :=
    (KernelAux.aestronglyMeasurable_periodicRiesz hd hs0 (by linarith)).comp_quasiMeasurePreserving
      (qmp_sub _ (withDensityReal_ac ρ))
  refine ⟨hm.pow 2, ?_⟩
  unfold HasFiniteIntegral
  have h1 := lintegral_prod_conv_le hρ Λ hΛ (fun z => ‖periodicRiesz d s z ^ 2‖ₑ)
    (hm.aemeasurable.pow_const 2).enorm
  refine lt_of_le_of_lt h1 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hvol.hasFiniteIntegral)

namespace InitialDataAux

lemma aesm_pair {g : Torus d → ℝ} (hgm : AEStronglyMeasurable g volume) {ρ : Torus d → ℝ} :
    AEStronglyMeasurable (fun p : Torus d × Torus d => g (p.1 - p.2))
      ((withDensityReal ρ).prod (withDensityReal ρ)) :=
  have := sigmaFinite_withDensityReal ρ
  hgm.comp_quasiMeasurePreserving (qmp_sub _ (withDensityReal_ac ρ))

lemma memLp_energy (g : Torus d → ℝ) (μ : Measure (Torus d)) [IsProbabilityMeasure μ] {N : ℕ}
    (hN : 1 ≤ N) (hW : MemLp (fun p : Torus d × Torus d => g (p.1 - p.2)) 2 (μ.prod μ)) :
    MemLp (fun X : Config d N => modulatedEnergyKernel g X μ) 2 (Measure.pi fun _ : Fin N => μ) := by
  have hfun : (fun X : Config d N => modulatedEnergyKernel g X μ) = fun X =>
      1 / (2 * (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, SecondMomentAux.hoeffK g μ (X i) (X j) -
        1 / (N : ℝ) ^ 2 * ∑ i, (convMeasure g μ (X i) - SecondMomentAux.gMean g μ / 2) :=
    funext fun X => SecondMomentAux.energy_decomp μ hN hW X
  rw [hfun]
  have hc : MemLp (convMeasure g μ) 2 μ := (SecondMomentAux.h_memLp_sq_le g μ hW).1
  have hA : MemLp (fun X : Config d N => ∑ i, ∑ j ∈ Finset.univ.erase i,
      SecondMomentAux.hoeffK g μ (X i) (X j)) 2 (Measure.pi fun _ : Fin N => μ) := by
    refine memLp_finsetSum _ fun i _ => memLp_finsetSum _ fun j hj => ?_
    exact SecondMomentAux.memLp_hoeffK_pair μ hW (Finset.ne_of_mem_erase hj).symm
  have hB : MemLp (fun X : Config d N => ∑ i, (convMeasure g μ (X i) -
      SecondMomentAux.gMean g μ / 2)) 2 (Measure.pi fun _ : Fin N => μ) := by
    refine memLp_finsetSum _ fun i _ => ?_
    have h1 : MemLp (fun X : Config d N => convMeasure g μ (X i)) 2 (Measure.pi fun _ : Fin N => μ) :=
      hc.comp_measurePreserving (measurePreserving_eval (fun _ : Fin N => μ) i)
    exact h1.sub (memLp_const _)
  exact (hA.const_mul _).sub (hB.const_mul _)

lemma eLpNorm_eq_ofReal_sqrt {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsProbabilityMeasure ν]
    {k : α → ℝ} (hk : MemLp k 2 ν) :
    eLpNorm k 2 ν = ENNReal.ofReal (Real.sqrt (∫ x, k x ^ 2 ∂ν)) := by
  have key : (eLpNorm k 2 ν).toReal = Real.sqrt (∫ x, k x ^ 2 ∂ν) := by
    rw [hk.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num), ENNReal.toReal_ofReal
      (by positivity)]
    simp [Real.sqrt_eq_rpow]
  rw [← key, ENNReal.ofReal_toReal hk.eLpNorm_ne_top]


lemma conv_bound_unif {g : Torus d → ℝ} (hg : Integrable g) {ρ : Torus d → ℝ} (Λ : ℝ)
    (hΛ : ∀ x, ρ x ≤ Λ) (x : Torus d) :
    |convMeasure g (withDensityReal ρ) x| ≤
      (ENNReal.ofReal Λ * ∫⁻ y, ENNReal.ofReal ‖g y‖).toReal := by
  have h1 := norm_integral_le_lintegral_norm (μ := withDensityReal ρ) (fun y => g (x - y))
  rw [Real.norm_eq_abs] at h1
  refine h1.trans (ENNReal.toReal_mono ?_ (KernelAux2.lintegral_conv_le ρ Λ hΛ
    (fun z => ENNReal.ofReal ‖g z‖) x))
  refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
  have := hg.hasFiniteIntegral
  unfold HasFiniteIntegral at this
  simp only [← ofReal_norm] at this
  exact this.ne

end InitialDataAux

open InitialDataAux in
/-- Lemma A.35 (i), second display `B:eq:initial-energy-second-moment` (source lines
11502-11506): if moreover `0 ≤ s < d/2` and `∬ g² d(μ°)^{⊗2} < ∞`, then
`(E[(F_N^0 + o_N)²])^{1/2} ≤ C (N⁻¹ ∨ o'_N)`, uniformly over densities bounded by `Λ`. -/
theorem initial_energy_iid_L2 {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (C₀ Λ : ℝ) :
    ∃ C : ℝ, ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      Integrable (fun p : Torus d × Torus d => periodicRiesz d s (p.1 - p.2) ^ 2)
        ((withDensityReal ρ).prod (withDensityReal ρ)) →
      ∀ N : ℕ, 2 ≤ N →
        eLpNorm (fun X : Config d N => rieszEnergy d s X (withDensityReal ρ) + oN d s C₀ N) 2
            (Measure.pi fun _ => withDensityReal ρ) ≤
          ENNReal.ofReal (C * max ((N : ℝ)⁻¹) (oPrime d s Λ N)) := by
  have hsd : s < d := by linarith
  have hgi := KernelAux.integrable_periodicRiesz (d := d) (s := s) hd hs0 hsd
  have hgm := KernelAux.aestronglyMeasurable_periodicRiesz (d := d) (s := s) hd hs0 hsd
  have hsqv := riesz_sq_integrable_volume (d := d) (s := s) hd hs0 hs
  set K : ℝ := (ENNReal.ofReal Λ * ∫⁻ y, ENNReal.ofReal (periodicRiesz d s y ^ 2)).toReal with hK
  set M : ℝ := (ENNReal.ofReal Λ * ∫⁻ y, ENNReal.ofReal ‖periodicRiesz d s y‖).toReal with hM
  set C' : ℝ := max (1 + K) M with hC'
  have hK0 : 0 ≤ K := ENNReal.toReal_nonneg
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  set C₁ : ℝ := C' * C' + C' with hC₁
  have hC'0 : 0 ≤ C' := (by linarith : (0:ℝ) ≤ 1 + K).trans (le_max_left _ _)
  refine ⟨C₁ * (|C₀| + 1) + 2 * (|C₀| + 1), fun ρ hρ hΛ hint2 N hN => ?_⟩
  have hprob := isProb_withDensityReal hρ
  set μ := withDensityReal ρ with hμ
  have hΛ1 := one_le_of_probDensity hρ Λ hΛ
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hmeas := aesm_pair (g := periodicRiesz d s) hgm (ρ := ρ)
  have hW : MemLp (fun p : Torus d × Torus d => periodicRiesz d s (p.1 - p.2)) 2 (μ.prod μ) :=
    (memLp_two_iff_integrable_sq hmeas).mpr hint2
  set o : ℝ := |oN d s C₀ N| with ho
  have ho0 : 0 ≤ o := abs_nonneg _
  have hMb : ∀ x, |convMeasure (periodicRiesz d s) μ x| ≤ M :=
    fun x => conv_bound_unif hgi Λ hΛ x
  have hG : ∫ p : Torus d × Torus d, (1 + periodicRiesz d s (p.1 - p.2) ^ 2) ∂(μ.prod μ) ≤ C' := by
    rw [integral_add (integrable_const _) hint2]
    rw [integral_const]
    simp only [measure_univ, Measure.real, ENNReal.toReal_one, smul_eq_mul, one_mul]
    have hF : AEMeasurable (fun p : Torus d × Torus d =>
        ENNReal.ofReal (periodicRiesz d s (p.1 - p.2) ^ 2)) (μ.prod μ) :=
      hint2.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    have h1 := lintegral_prod_conv_le hρ Λ hΛ (fun z => ENNReal.ofReal (periodicRiesz d s z ^ 2)) hF
    have h2 : ∫ p : Torus d × Torus d, periodicRiesz d s (p.1 - p.2) ^ 2 ∂(μ.prod μ) ≤ K := by
      rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => sq_nonneg _)
        hint2.aestronglyMeasurable]
      refine ENNReal.toReal_mono ?_ h1
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hsqv.lintegral_lt_top.ne
    exact le_trans (by linarith) (le_max_left (1 + K) M)
  obtain ⟨CN, hCN0, hCN, hbound⟩ := second_moment_modulatedEnergy_iid
    (N := N) (periodicRiesz d s) μ (fun x => by rw [periodicRiesz_neg]) hmeas o ho0 hint2 M hMb hN1
  have hCN' : CN ≤ C₁ := hCN C' hG (le_max_right _ _)
  have hFm := memLp_energy (periodicRiesz d s) μ hN1 hW
  have hFo : MemLp (fun X : Config d N => modulatedEnergyKernel (periodicRiesz d s) X μ + o) 2
      (Measure.pi fun _ : Fin N => μ) := hFm.add (memLp_const _)
  have e1 : eLpNorm (fun X : Config d N => modulatedEnergyKernel (periodicRiesz d s) X μ + o) 2
      (Measure.pi fun _ : Fin N => μ) ≤ ENNReal.ofReal (CN * max ((N : ℝ)⁻¹) o) := by
    rw [eLpNorm_eq_ofReal_sqrt hFo]
    exact ENNReal.ofReal_le_ofReal hbound
  have e2 : (fun X : Config d N => rieszEnergy d s X μ + oN d s C₀ N) =
      (fun X : Config d N => modulatedEnergyKernel (periodicRiesz d s) X μ + o) +
        fun _ => oN d s C₀ N - o := by
    funext X; simp only [Pi.add_apply, rieszEnergy]; ring
  have e3 : eLpNorm (fun _ : Config d N => oN d s C₀ N - o) 2 (Measure.pi fun _ : Fin N => μ) ≤
      ENNReal.ofReal (2 * o) := by
    rw [eLpNorm_const _ (by norm_num) (NeZero.ne _)]
    simp only [measure_univ, ENNReal.toReal_ofNat, ENNReal.one_rpow, mul_one]
    rw [← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Real.norm_eq_abs, abs_le]
    have := abs_le.1 (le_refl o)
    constructor <;> cases abs_cases (oN d s C₀ N) <;> linarith
  obtain ⟨h1, h2, h3⟩ := oN_abs_le hd hs0 C₀ Λ hΛ1 N hN1
  rw [e2]
  refine (eLpNorm_add_le (by norm_num)).trans ?_
  refine (add_le_add e1 e3).trans ?_
  rw [← ENNReal.ofReal_add (mul_nonneg (by linarith) (le_max_of_le_left (by positivity))) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  set oP := oPrime d s Λ N with hoP
  set mx := max ((N : ℝ)⁻¹) oP with hmx
  have hm1 : max ((N : ℝ)⁻¹) o ≤ (|C₀| + 1) * mx := by
    refine max_le ?_ ?_
    · calc (N : ℝ)⁻¹ ≤ oP := h1
        _ ≤ (|C₀| + 1) * oP := by nlinarith [abs_nonneg C₀]
        _ ≤ _ := by gcongr; exact le_max_right _ _
    · calc o ≤ (|C₀| + 1) * oP := h2
        _ ≤ _ := by gcongr; exact le_max_right _ _
  have hmx0 : 0 ≤ mx := h3.trans (le_max_right _ _)
  have ho1 : o ≤ (|C₀| + 1) * mx := (le_max_right _ _).trans hm1
  calc CN * max ((N : ℝ)⁻¹) o + 2 * o ≤ C₁ * ((|C₀| + 1) * mx) + 2 * ((|C₀| + 1) * mx) := by
        gcongr
    _ = _ := by ring

namespace GeneralSetup

variable (S : GeneralSetup d)

/-- Lemma A.35 (ii) (source lines 11510-11511), static content: for a deterministic
collision-free configuration path `Y` (any probability space, all randomness absent), the
energy moments are the computable numbers `sup_t (F_N(Y_t, μ^t) + o_N)` and the second-moment
quantity `𝔈_{N,2}` equals `𝔈_N`, i.e. `B:ass:MF2` holds with `𝔈'_N = 𝔈_N`.  (The dynamical
statement that `β_N = ∞` dynamics started from deterministic data stays deterministic belongs to
the particle-dynamics package.) -/
theorem energyMoment_deterministic {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (N : ℕ) (hN : 2 ≤ N) (Y : ℝ≥0 → Config d N)
    (hY : ∀ t ∈ Set.Icc (0 : ℝ) S.T, Y (Real.toNNReal t) ∉ collisionSet d N) :
    S.energyMoment P N (fun t _ => Y t) =
        ⨆ t : Set.Icc (0 : ℝ) S.T, S.energyCompletion N (Y (Real.toNNReal t)) t ∧
      S.energyMoment2 P N (fun t _ => Y t) = S.energyMoment P N (fun t _ => Y t) ∧
      (S.EnergyMomentFinite P N (fun t _ => Y t) ↔
        S.EnergyMoment2Finite P N (fun t _ => Y t)) := by
  have hc : ∀ t : Set.Icc (0 : ℝ) S.T, 0 ≤ S.energyCompletion N (Y (Real.toNNReal t)) t := fun t =>
    S.energy_nonneg N hN t t.2 _ (hY t t.2)
  have h1 : ∀ t : Set.Icc (0 : ℝ) S.T,
      ∫ ω, S.energyCompletion N (Y (Real.toNNReal t)) t ∂P =
        S.energyCompletion N (Y (Real.toNNReal t)) t := fun t => by simp
  have h2 : ∀ t : Set.Icc (0 : ℝ) S.T,
      Real.sqrt (∫ ω, (S.energyCompletion N (Y (Real.toNNReal t)) t) ^ 2 ∂P) =
        S.energyCompletion N (Y (Real.toNNReal t)) t := fun t => by
    simp [Real.sqrt_sq (hc t)]
  have e1 : S.energyMoment P N (fun t _ => Y t) =
      ⨆ t : Set.Icc (0 : ℝ) S.T, S.energyCompletion N (Y (Real.toNNReal t)) t := by
    unfold GeneralSetup.energyMoment
    exact iSup_congr h1
  refine ⟨e1, ?_, ?_⟩
  · rw [e1]
    unfold GeneralSetup.energyMoment2
    exact iSup_congr h2
  · constructor
    · rintro ⟨-, hb⟩
      refine ⟨fun t ht => ?_, ?_⟩
      · exact memLp_const _
      · convert hb using 2
        funext t
        exact (h2 t).trans (h1 t).symm
    · rintro ⟨-, hb⟩
      refine ⟨fun t ht => ?_, ?_⟩
      · exact integrable_const _
      · convert hb using 2
        funext t
        exact (h1 t).trans (h2 t).symm

end GeneralSetup

/-! ### Example A.17: the Gaussian initial field of independent preparation -/

/-- The bridge covariance `μ°(ψφ) - μ°(ψ) μ°(φ)` of Example A.17 (source lines 10471-10472). -/
def iidCov (μ : Measure (Torus d)) (ψ φ : Torus d → ℝ) : ℝ :=
  pair μ (fun x => ψ x * φ x) - pair μ ψ * pair μ φ

namespace InitialDataAux

lemma sqrt_mul_rpow (N : ℕ) (hN : 0 < N) (a : ℝ) :
    Real.sqrt N * (N : ℝ) ^ (a - 1) = (N : ℝ) ^ (a - 1 / 2) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add hN']
  congr 1; ring

lemma log_term_tendsto :
    Tendsto (fun N : ℕ => Real.sqrt N * (Real.log (Real.exp 1 * N) / N)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun N : ℕ => Real.log N / (N : ℝ) ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
    ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero).comp
      tendsto_natCast_atTop_atTop
  have h3 := h1.add h2
  rw [add_zero] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog : Real.log (Real.exp 1 * N) = 1 + Real.log N := by
    rw [Real.log_mul (Real.exp_pos 1).ne' hN'.ne', Real.log_exp]
  rw [hlog, Real.sqrt_eq_rpow, Real.rpow_neg hN'.le]
  have : (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) = N := by
    rw [← Real.rpow_add hN']; norm_num
  have hp : 0 < (N : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hN' _
  field_simp
  nlinarith [this]

end InitialDataAux

open InitialDataAux in
/-- Example A.17 (source lines 10473-10475): with general energy bound of order
`N^{s/d-1} + 1_{s=0} log(eN)/N` at normalisation `κ_N = √N`, the sufficient central-limit
condition `√N (N^{s/d-1} + 1_{s=0} log(eN)/N) → 0` holds exactly when `s < d/2`. -/
theorem iid_energy_scaling_iff {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    Tendsto (fun N : ℕ => Real.sqrt N * ((N : ℝ) ^ (s / d - 1) +
        (if s = 0 then Real.log (Real.exp 1 * N) / N else 0))) atTop (𝓝 0) ↔
      s < (d : ℝ) / 2 := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have key : ∀ N : ℕ, 0 < N → Real.sqrt N * ((N : ℝ) ^ (s / d - 1) +
        (if s = 0 then Real.log (Real.exp 1 * N) / N else 0)) =
      (N : ℝ) ^ (s / d - 1 / 2) + (if s = 0 then Real.sqrt N * (Real.log (Real.exp 1 * N) / N) else 0) := by
    intro N hN
    rw [mul_add, sqrt_mul_rpow N hN]
    split_ifs <;> simp
  have hlt : s < (d : ℝ) / 2 ↔ s / d - 1 / 2 < 0 := by
    rw [sub_neg, div_lt_iff₀ hdpos]
    constructor <;> intro h <;> linarith
  constructor
  · intro h
    by_contra hnot
    have hs : s ≠ 0 := by
      rintro rfl
      exact hnot (by positivity)
    have hge : 0 ≤ s / d - 1 / 2 := by
      rw [hlt] at hnot; exact not_lt.1 hnot
    have h' : Tendsto (fun N : ℕ => (N : ℝ) ^ (s / d - 1 / 2)) atTop (𝓝 0) := by
      refine h.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with N hN
      rw [key N hN]; simp [hs]
    have h1 : Tendsto (fun N : ℕ => (N : ℝ) ^ (s / d - 1 / 2)) atTop (𝓝 1) ∨
        Tendsto (fun N : ℕ => (N : ℝ) ^ (s / d - 1 / 2)) atTop atTop := by
      rcases hge.eq_or_lt with h0 | h0
      · left
        rw [← h0]
        simp only [Real.rpow_zero]
        exact tendsto_const_nhds
      · right
        exact (tendsto_rpow_atTop h0).comp tendsto_natCast_atTop_atTop
    rcases h1 with h1 | h1
    · exact one_ne_zero (tendsto_nhds_unique h1 h')
    · exact not_tendsto_nhds_of_tendsto_atTop h1 0 h'
  · intro hs
    have hneg := hlt.1 hs
    have h1 : Tendsto (fun N : ℕ => (N : ℝ) ^ (s / d - 1 / 2)) atTop (𝓝 0) := by
      have := tendsto_rpow_neg_atTop (y := -(s / d - 1 / 2)) (by linarith)
      simp only [neg_neg] at this
      exact this.comp tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun N : ℕ => (N : ℝ) ^ (s / d - 1 / 2) +
        (if s = 0 then Real.sqrt N * (Real.log (Real.exp 1 * N) / N) else 0)) atTop (𝓝 0) := by
      split_ifs
      · simpa using h1.add log_term_tendsto
      · simpa using h1
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact (key N hN).symm

/-! ### Lemma A.36: statistics-level initial assumptions for i.i.d. data -/

/-- The statistic `⟨ψ, √N(μ_N - μ°)⟩ = √N (μ_N(ψ) - μ°(ψ))`. -/
def iidStat (μ : Measure (Torus d)) {N : ℕ} (ψ : Torus d → ℝ) (X : Config d N) : ℝ :=
  Real.sqrt N * (pair (empirical X) ψ - pair μ ψ)

namespace InitialDataAux


theorem negSobolev_secondCountable (d : ℕ) (m : ℝ) : SecondCountableTopology (NegSobolev d m) := by
  let b : HilbertBasis (NonzeroLattice d) ℝ (lp (fun _ : NonzeroLattice d => ℝ) 2) :=
    default
  have hdense := b.dense_span
  have hcount : (Set.range b).Countable := Set.countable_range _
  have hsep := TopologicalSpace.IsSeparable.span (R := ℝ) hcount.isSeparable
  have : TopologicalSpace.IsSeparable (Set.univ : Set (lp (fun _ : NonzeroLattice d => ℝ) 2)) := by
    have h2 := hsep.closure
    rwa [← Submodule.topologicalClosure_coe, hdense, Submodule.top_coe] at h2
  have : TopologicalSpace.SeparableSpace (lp (fun _ : NonzeroLattice d => ℝ) 2) :=
    TopologicalSpace.isSeparable_univ_iff.mp this
  exact (inferInstance : SecondCountableTopology (lp (fun _ : NonzeroLattice d => ℝ) 2))

lemma continuous_realMode (k : NonzeroLattice d) : Continuous (Torus.realMode k) := by
  unfold Torus.realMode
  split_ifs
  · exact continuous_const.mul (Torus.continuous_cosMode _)
  · exact continuous_const.mul (Torus.continuous_sinMode _)

open Classical in
lemma isSmooth_realMode (k : NonzeroLattice d) : Torus.IsSmooth (Torus.realMode k) := by
  unfold Torus.IsSmooth Torus.IsCk
  have hdot : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : Euc d => Lattice.dot k.1 y) := by
    unfold Lattice.dot
    refine ContDiff.sum fun i _ => contDiff_const.mul ?_
    exact (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).contDiff
  have hlift : Torus.lift (Torus.realMode k) = fun y : Euc d =>
      if Lattice.IsPosHalf k.1 then Real.sqrt 2 * Real.cos (2 * Real.pi * Lattice.dot k.1 y)
      else Real.sqrt 2 * Real.sin (2 * Real.pi * Lattice.dot k.1 y) := by
    funext y
    unfold Torus.lift Torus.realMode
    simp only [Function.comp, Torus.cosMode_mk, Torus.sinMode_mk]
  rw [hlift]
  split_ifs
  · exact contDiff_const.mul (Real.contDiff_cos.comp (contDiff_const.mul hdot))
  · exact contDiff_const.mul (Real.contDiff_sin.comp (contDiff_const.mul hdot))

/-- the trigonometric polynomial with prescribed real coefficients on a finite set -/
def trigPoly (T : Finset (NonzeroLattice d)) (c : NonzeroLattice d → ℝ) : Torus d → ℝ :=
  fun x => ∑ k ∈ T, c k * Torus.realMode k x

lemma isSmooth_trigPoly (T : Finset (NonzeroLattice d)) (c : NonzeroLattice d → ℝ) :
    Torus.IsSmooth (trigPoly T c) := by
  unfold Torus.IsSmooth Torus.IsCk
  have : Torus.lift (trigPoly T c) = fun y => ∑ k ∈ T, c k * Torus.lift (Torus.realMode k) y := by
    funext y; simp [Torus.lift, trigPoly]
  rw [this]
  refine ContDiff.sum fun k _ => contDiff_const.mul ?_
  exact isSmooth_realMode k

lemma continuous_trigPoly (T : Finset (NonzeroLattice d)) (c : NonzeroLattice d → ℝ) :
    Continuous (trigPoly T c) := by
  unfold trigPoly
  exact continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_realMode k)

lemma integrable_realMode_mul (k l : NonzeroLattice d) :
    Integrable (fun x => Torus.realMode k x * Torus.realMode l x) :=
  ((continuous_realMode k).mul (continuous_realMode l)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma funRealCoeff_trigPoly (T : Finset (NonzeroLattice d)) (c : NonzeroLattice d → ℝ)
    (k : NonzeroLattice d) :
    Torus.funRealCoeff (trigPoly T c) k = if k ∈ T then c k else 0 := by
  unfold Torus.funRealCoeff trigPoly
  have : ∀ x, Torus.realMode k x * ∑ l ∈ T, c l * Torus.realMode l x =
      ∑ l ∈ T, c l * (Torus.realMode k x * Torus.realMode l x) := by
    intro x; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
  simp_rw [this]
  rw [integral_finsetSum _ fun l _ => (integrable_realMode_mul k l).const_mul _]
  simp_rw [integral_const_mul, Torus.realMode_orthonormal]
  simp [Finset.sum_ite_eq]

lemma integral_trigPoly_sq (T : Finset (NonzeroLattice d)) (c : NonzeroLattice d → ℝ) :
    ∫ x, trigPoly T c x ^ 2 = ∑ k ∈ T, c k ^ 2 := by
  have : ∀ x, trigPoly T c x ^ 2 = ∑ k ∈ T, ∑ l ∈ T,
      c k * c l * (Torus.realMode k x * Torus.realMode l x) := by
    intro x; unfold trigPoly; rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  simp_rw [this]
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
    (integrable_realMode_mul k l).const_mul _]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [integral_finsetSum _ fun l _ => (integrable_realMode_mul k l).const_mul _]
  simp_rw [integral_const_mul, Torus.realMode_orthonormal]
  simp [Finset.sum_ite_eq, hk, sq]

/-- the dual vector representing `F ↦ eval F ψ` -/
def yvec (m : ℝ) (ψ : Torus d → ℝ)
    (h : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff ψ k ^ 2) :
    NegSobolev d m :=
  (⟨fun k => Lattice.jp k.1 ^ m * Torus.funRealCoeff ψ k, by
    show Memℓp _ 2
    rw [Torus.memℓp_two_iff]
    refine h.congr fun k => ?_
    simp only [mul_pow, Torus.jp_rpow_sq]⟩ :
    lp (fun _ : NonzeroLattice d => ℝ) 2)

lemma eval_eq_inner (m : ℝ) (ψ : Torus d → ℝ)
    (h : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff ψ k ^ 2)
    (F : NegSobolev d m) : NegSobolev.eval F ψ = inner ℝ (yvec m ψ h) F := by
  have := lp.inner_eq_tsum (𝕜 := ℝ) (G := fun _ : NonzeroLattice d => ℝ)
    (yvec m ψ h : lp (fun _ : NonzeroLattice d => ℝ) 2)
    (F : lp (fun _ : NonzeroLattice d => ℝ) 2)
  refine Eq.trans ?_ this.symm
  unfold NegSobolev.eval NegSobolev.fourierCoeff NegSobolev.coord
  refine tsum_congr fun k => ?_
  simp only [yvec, RCLike.inner_apply, conj_trivial]
  ring


lemma iidCov_le {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) (Λ : ℝ) (hΛ : ∀ x, ρ x ≤ Λ)
    (φ : Torus d → ℝ) (hφ : Continuous φ) :
    iidCov (withDensityReal ρ) φ φ ≤ Λ * ∫ x, φ x ^ 2 := by
  have hΛ0 : 0 ≤ Λ := (zero_le_one.trans (one_le_of_probDensity hρ Λ hΛ))
  have hint : Integrable (fun x => φ x * φ x) (volume : Measure (Torus d)) :=
    (hφ.mul hφ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h1 : iidCov (withDensityReal ρ) φ φ ≤ pair (withDensityReal ρ) (fun x => φ x * φ x) := by
    unfold iidCov
    nlinarith [mul_self_nonneg (pair (withDensityReal ρ) φ)]
  refine h1.trans ?_
  unfold pair
  calc ∫ x, φ x * φ x ∂(withDensityReal ρ)
      ≤ ∫ x, φ x * φ x ∂(ENNReal.ofReal Λ • (volume : Measure (Torus d))) :=
        integral_mono_measure (KernelAux2.withDensityReal_le ρ Λ hΛ)
          (Filter.Eventually.of_forall fun x => mul_self_nonneg _)
          (hint.smul_measure ENNReal.ofReal_ne_top)
    _ = Λ * ∫ x, φ x ^ 2 := by
        rw [integral_smul_measure, ENNReal.toReal_ofReal hΛ0, smul_eq_mul]
        simp only [sq]

lemma eval_sq_lintegral_le (m : ℝ) (hm0 : 0 ≤ m) {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) (Λ : ℝ)
    (hΛ : ∀ x, ρ x ≤ Λ) (ν : Measure (NegSobolev d m)) [IsProbabilityMeasure ν]
    (hν : IsCenteredGaussianWithCov m ν (iidCov (withDensityReal ρ)))
    (ψ : Torus d → ℝ) (hψ : MemSobolev m ψ) :
    ∫⁻ F, ENNReal.ofReal (NegSobolev.eval F ψ ^ 2) ∂ν ≤
      ENNReal.ofReal (Λ * ∑' k : NonzeroLattice d,
        Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff ψ k ^ 2) := by
  have := negSobolev_secondCountable d m
  have hΛ0 : 0 ≤ Λ := (zero_le_one.trans (one_le_of_probDensity hρ Λ hΛ))
  have hs := hψ.2
  set c : NonzeroLattice d → ℝ := Torus.funRealCoeff ψ with hc
  set y : NegSobolev d m := yvec m ψ hs with hy
  have hG := hν.1.1
  have hmem : MemLp id 2 ν := IsGaussian.memLp_two_id
  have hmean : ∫ z, id z ∂ν = 0 := gaussian_integral_id_eq_zero hν.1
  -- the covariance of a general vector
  have hcov : ∀ x : NegSobolev d m, covarianceBilin ν x x = ∫ F, inner ℝ x F ^ 2 ∂ν := by
    intro x
    rw [covarianceBilin_apply hmem]
    simp only [hmean, sub_zero, sq]
  -- finite approximations
  have hbound : ∀ T : Finset (NonzeroLattice d),
      covarianceBilin ν (yvec m (trigPoly T c) (by
        refine summable_of_ne_finset_zero (s := T) fun k hk => ?_
        rw [funRealCoeff_trigPoly]; simp [hk])) (yvec m (trigPoly T c) (by
        refine summable_of_ne_finset_zero (s := T) fun k hk => ?_
        rw [funRealCoeff_trigPoly]; simp [hk])) ≤
        Λ * ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * m) * c k ^ 2 := by
    intro T
    set hT : Summable fun k : NonzeroLattice d =>
        Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff (trigPoly T c) k ^ 2 := by
      refine summable_of_ne_finset_zero (s := T) fun k hk => ?_
      rw [funRealCoeff_trigPoly]; simp [hk]
    rw [hcov]
    have h1 : ∀ F : NegSobolev d m, inner ℝ (yvec m (trigPoly T c) hT) F ^ 2 =
        NegSobolev.eval F (trigPoly T c) * NegSobolev.eval F (trigPoly T c) := by
      intro F; rw [← eval_eq_inner, sq]
    simp_rw [h1]
    rw [hν.2 _ _ (isSmooth_trigPoly T c) (isSmooth_trigPoly T c)]
    refine (iidCov_le hρ Λ hΛ _ (continuous_trigPoly T c)).trans ?_
    rw [integral_trigPoly_sq]
    refine mul_le_mul_of_nonneg_left ?_ hΛ0
    calc ∑ k ∈ T, c k ^ 2 ≤ ∑ k ∈ T, Lattice.jp k.1 ^ (2 * m) * c k ^ 2 := by
          refine Finset.sum_le_sum fun k _ => ?_
          have : 1 ≤ Lattice.jp k.1 ^ (2 * m) :=
            Real.one_le_rpow (Torus.jp_ge_one _) (by linarith)
          nlinarith [sq_nonneg (c k)]
      _ ≤ _ := hs.sum_le_tsum T (fun k _ => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _)
            (sq_nonneg _))
  -- convergence of the truncations
  have hTs : ∀ T : Finset (NonzeroLattice d), Summable fun k : NonzeroLattice d =>
      Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff (trigPoly T c) k ^ 2 := fun T => by
    refine summable_of_ne_finset_zero (s := T) fun k hk => ?_
    rw [funRealCoeff_trigPoly]; simp [hk]
  have hyT : ∀ T : Finset (NonzeroLattice d), yvec m (trigPoly T c) (hTs T) =
      ∑ i ∈ T, (lp.single 2 i (NegSobolev.coord y i) :
        lp (fun _ : NonzeroLattice d => ℝ) 2) := by
    intro T
    refine Subtype.ext (funext fun k => ?_)
    simp only [lp.coeFn_sum, Finset.sum_apply, lp.single_apply]
    have e1 : NegSobolev.coord (yvec m (trigPoly T c) (hTs T)) k =
        Lattice.jp k.1 ^ m * (if k ∈ T then c k else 0) := by
      show Lattice.jp k.1 ^ m * Torus.funRealCoeff (trigPoly T c) k = _
      rw [funRealCoeff_trigPoly]
    change NegSobolev.coord (yvec m (trigPoly T c) (hTs T)) k = _
    rw [e1]
    by_cases hk : k ∈ T
    · simp [hk, NegSobolev.coord, hy, yvec, hc]
    · simp [hk]
  have hsum := lp.hasSum_single (E := fun _ : NonzeroLattice d => ℝ) (p := 2) ENNReal.ofNat_ne_top
    (y : lp (fun _ : NonzeroLattice d => ℝ) 2)
  have htend : Tendsto (fun T : Finset (NonzeroLattice d) => yvec m (trigPoly T c) (hTs T)) atTop
      (𝓝 y) := by
    simp_rw [hyT]
    exact hsum
  have hcont : Continuous (fun x : NegSobolev d m => covarianceBilin ν x x) :=
    (covarianceBilin ν).continuous.clm_apply continuous_id
  have hlim := (hcont.tendsto y).comp htend
  have hle : covarianceBilin ν y y ≤ Λ * ∑' k : NonzeroLattice d,
      Lattice.jp k.1 ^ (2 * m) * c k ^ 2 := le_of_tendsto' hlim fun T => hbound T
  -- conclusion
  have hint : Integrable (fun F : NegSobolev d m => inner ℝ y F ^ 2) ν := by
    have := IsGaussian.memLp_dual ν (innerSL ℝ y) 2 (by simp)
    exact this.integrable_sq
  have hfun : (fun F : NegSobolev d m => ENNReal.ofReal (NegSobolev.eval F ψ ^ 2)) =
      fun F => ENNReal.ofReal (inner ℝ y F ^ 2) := by
    funext F; rw [eval_eq_inner m ψ hs F]
  rw [hfun, ← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun _ => sq_nonneg _),
    ← hcov y]
  exact ENNReal.ofReal_le_ofReal hle



lemma integral_sum_sq_iid (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (N : ℕ)
    {u : Torus d → ℝ} (hu : MemLp u 2 μ) (hu0 : ∫ x, u x ∂μ = 0) :
    ∫ X : Config d N, (∑ i, u (X i)) ^ 2 ∂(Measure.pi fun _ : Fin N => μ) =
      N * ∫ x, u x ^ 2 ∂μ := by
  have hi : ∀ i : Fin N, MemLp (fun X : Config d N => u (X i)) 2 (Measure.pi fun _ : Fin N => μ) :=
    fun i => hu.comp_measurePreserving (measurePreserving_eval (fun _ : Fin N => μ) i)
  have hexp : ∀ X : Config d N, (∑ i, u (X i)) ^ 2 = ∑ i, ∑ j, u (X i) * u (X j) := by
    intro X; rw [sq, Finset.sum_mul_sum]
  have hmul : ∀ i j : Fin N, Integrable (fun X : Config d N => u (X i) * u (X j))
      (Measure.pi fun _ : Fin N => μ) := fun i j => (hi i).integrable_mul (hi j)
  simp_rw [hexp]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hmul i j]
  have hdiag : ∀ i : Fin N, ∫ X : Config d N, u (X i) * u (X i) ∂(Measure.pi fun _ : Fin N => μ) =
      ∫ x, u x ^ 2 ∂μ := by
    intro i
    have := integral_comp_eval (μ := fun _ : Fin N => μ) (i := i)
      (f := fun x => u x * u x) ((hu.aestronglyMeasurable.mul hu.aestronglyMeasurable))
    simpa [sq] using this
  have hrow : ∀ i : Fin N, ∫ X : Config d N, ∑ j, u (X i) * u (X j) ∂(Measure.pi fun _ : Fin N => μ) =
      ∫ x, u x ^ 2 ∂μ := by
    intro i
    rw [integral_finsetSum _ fun j _ => hmul i j]
    rw [Finset.sum_eq_single i]
    · exact hdiag i
    · intro j _ hji
      have hH : Integrable (fun p : Torus d × Torus d => u p.1 * u p.2) (μ.prod μ) :=
        (hu.integrable one_le_two).mul_prod (hu.integrable one_le_two)
      rw [integral_pair_comp μ (Ne.symm hji) (H := fun p => u p.1 * u p.2) hH, integral_prod_mul, hu0]
      simp
    · simp
  simp_rw [hrow]
  simp


lemma sq_integral_le_sobolev (m : ℝ) (hm0 : 0 ≤ m) {ψ : Torus d → ℝ} (hψ : MemSobolev m ψ) :
    ∫ x, ψ x ^ 2 ≤ sobolevNorm m ψ ^ 2 := by
  have hs := hψ.2
  rw [Torus.parseval_realCoeff ψ hψ.1, sobolevNorm, Real.sq_sqrt (by
    have : 0 ≤ ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff ψ k ^ 2 :=
      tsum_nonneg fun k => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (sq_nonneg _)
    positivity)]
  have h2 : Summable fun k : NonzeroLattice d => Torus.funRealCoeff ψ k ^ 2 := by
    refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_) hs
    have : 1 ≤ Lattice.jp k.1 ^ (2 * m) := Real.one_le_rpow (Torus.jp_ge_one _) (by linarith)
    nlinarith [sq_nonneg (Torus.funRealCoeff ψ k)]
  have := h2.tsum_le_tsum (fun k => by
    have : 1 ≤ Lattice.jp k.1 ^ (2 * m) := Real.one_le_rpow (Torus.jp_ge_one _) (by linarith)
    nlinarith [sq_nonneg (Torus.funRealCoeff ψ k)]) hs
  linarith

lemma iidStat_lintegral_le (m : ℝ) (hm0 : 0 ≤ m) {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) (Λ : ℝ)
    (hΛ : ∀ x, ρ x ≤ Λ) (N : ℕ) (hN : 1 ≤ N) (ψ : Torus d → ℝ) (hψ : MemSobolev m ψ) :
    ∫⁻ X, ENNReal.ofReal (iidStat (withDensityReal ρ) ψ X ^ 2)
        ∂(Measure.pi fun _ : Fin N => withDensityReal ρ) ≤
      ENNReal.ofReal (Λ * sobolevNorm m ψ ^ 2) := by
  have hprob := isProb_withDensityReal hρ
  set μ := withDensityReal ρ with hμ
  have hΛ0 : 0 ≤ Λ := (zero_le_one.trans (one_le_of_probDensity hρ Λ hΛ))
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hψμ : MemLp ψ 2 μ := by
    have h1 : MemLp ψ 2 (ENNReal.ofReal Λ • (volume : Measure (Torus d))) :=
      hψ.1.smul_measure ENNReal.ofReal_ne_top
    exact h1.mono_measure (KernelAux2.withDensityReal_le ρ Λ hΛ)
  set p := pair μ ψ with hp
  set u : Torus d → ℝ := fun x => ψ x - p with hu_def
  have hu : MemLp u 2 μ := hψμ.sub (memLp_const p)
  have hu0 : ∫ x, u x ∂μ = 0 := by
    simp only [hu_def]
    rw [integral_sub (hψμ.integrable one_le_two) (integrable_const _), integral_const]
    simp [hp, pair]
  have hstat : ∀ X : Config d N, iidStat μ ψ X = (Real.sqrt N)⁻¹ * ∑ i, u (X i) := by
    intro X
    unfold iidStat
    rw [pair_empirical (by omega)]
    simp only [hu_def, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    have hs : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hNpos.le
    have hs0 : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
    rw [← hp]
    field_simp
    rw [Real.sq_sqrt hNpos.le]
  have hU : MemLp (fun X : Config d N => ∑ i, u (X i)) 2 (Measure.pi fun _ : Fin N => μ) := by
    refine memLp_finsetSum _ fun i _ => ?_
    exact hu.comp_measurePreserving (measurePreserving_eval (fun _ : Fin N => μ) i)
  have hsq : ∀ X : Config d N, iidStat μ ψ X ^ 2 = (N : ℝ)⁻¹ * (∑ i, u (X i)) ^ 2 := by
    intro X
    rw [hstat, mul_pow, inv_pow, Real.sq_sqrt hNpos.le]
  have hint : Integrable (fun X : Config d N => iidStat μ ψ X ^ 2) (Measure.pi fun _ : Fin N => μ) := by
    simp_rw [hsq]
    exact hU.integrable_sq.const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  simp_rw [hsq]
  rw [integral_const_mul, integral_sum_sq_iid μ N hu hu0, ← mul_assoc, inv_mul_cancel₀ hNpos.ne', one_mul]
  -- variance bound
  have hvar : ∫ x, u x ^ 2 ∂μ ≤ ∫ x, ψ x ^ 2 ∂μ := by
    have h1 := variance_eq_integral (μ := μ) hψμ.aemeasurable
    have h2 := variance_eq_sub hψμ
    have h3 : ∫ x, u x ^ 2 ∂μ = ∫ ω, (ψ ω - μ[ψ]) ^ 2 ∂μ := by
      simp only [hu_def, hp, pair]
    have h4 : μ[ψ ^ 2] = ∫ x, ψ x ^ 2 ∂μ := rfl
    rw [h3, ← h1, h2, h4]
    nlinarith [sq_nonneg (μ[ψ])]
  have hΛle : ∫ x, ψ x ^ 2 ∂μ ≤ Λ * ∫ x, ψ x ^ 2 := by
    calc ∫ x, ψ x ^ 2 ∂μ ≤ ∫ x, ψ x ^ 2 ∂(ENNReal.ofReal Λ • (volume : Measure (Torus d))) :=
          integral_mono_measure (KernelAux2.withDensityReal_le ρ Λ hΛ)
            (Filter.Eventually.of_forall fun x => sq_nonneg _)
            (hψ.1.integrable_sq.smul_measure ENNReal.ofReal_ne_top)
      _ = _ := by rw [integral_smul_measure, ENNReal.toReal_ofReal hΛ0, smul_eq_mul]
  have := sq_integral_le_sobolev m hm0 hψ
  nlinarith

end InitialDataAux

open InitialDataAux in
/-- Lemma A.36 `M:B:lem:iid-init`, (I2) (source lines 11544-11545 with `B:item:I2`, line
10211): for `m₀ > d/2`, `μ° = ρ dx` with `ρ ≤ Λ`, and the Gaussian field `η° ∼ ν` of
Example A.17 on `E_{m₀}`,
`E|⟨ψ, √N(μ_N^0 - μ°)⟩|² + E|⟨ψ, η°⟩|² ≤ C Λ ‖ψ‖²_{H^{m₀}}` for every `ψ ∈ H^{m₀}`, with
`C = C(d, m₀)`. -/
theorem iid_init_I2 (m₀ : ℝ) (hm₀ : (d : ℝ) / 2 < m₀) :
    ∃ C : ℝ, ∀ (ρ : Torus d → ℝ) (Λ : ℝ), IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ ν : Measure (NegSobolev d m₀), IsProbabilityMeasure ν →
        IsCenteredGaussianWithCov m₀ ν (iidCov (withDensityReal ρ)) →
      ∀ N : ℕ, 1 ≤ N → ∀ ψ : Torus d → ℝ, MemSobolev m₀ ψ →
        ∫⁻ X, ENNReal.ofReal (iidStat (withDensityReal ρ) ψ X ^ 2)
            ∂(Measure.pi fun _ : Fin N => withDensityReal ρ) +
          ∫⁻ F, ENNReal.ofReal (NegSobolev.eval F ψ ^ 2) ∂ν ≤
          ENNReal.ofReal (C * Λ * sobolevNorm m₀ ψ ^ 2) := by
  have hm0 : 0 ≤ m₀ := (by positivity : (0:ℝ) ≤ (d : ℝ) / 2).trans hm₀.le
  refine ⟨2, fun ρ Λ hρ hΛ ν hν hνG N hN ψ hψ => ?_⟩
  have h1 := iidStat_lintegral_le m₀ hm0 hρ Λ hΛ N hN ψ hψ
  have h2 := eval_sq_lintegral_le m₀ hm0 hρ Λ hΛ ν hνG ψ hψ
  have hΛ0 : 0 ≤ Λ := (zero_le_one.trans (one_le_of_probDensity hρ Λ hΛ))
  have hs := hψ.2
  have hle : ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * m₀) * Torus.funRealCoeff ψ k ^ 2 ≤
      sobolevNorm m₀ ψ ^ 2 := by
    have hnn : 0 ≤ (Torus.mean ψ) ^ 2 +
        ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * m₀) * Torus.funRealCoeff ψ k ^ 2 := by
      have : 0 ≤ ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * m₀) * Torus.funRealCoeff ψ k ^ 2 :=
        tsum_nonneg fun k => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (sq_nonneg _)
      positivity
    rw [sobolevNorm, Real.sq_sqrt hnn]
    nlinarith [sq_nonneg (Torus.mean ψ)]
  calc _ ≤ ENNReal.ofReal (Λ * sobolevNorm m₀ ψ ^ 2) + ENNReal.ofReal (Λ * sobolevNorm m₀ ψ ^ 2) :=
        add_le_add h1 (h2.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hle hΛ0)))
    _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

namespace InitialDataAux

/-- Gluing: two random elements with prescribed statistics `T`, `T'` and a coupling `π` of the
statistics' laws. -/
theorem glue_two {A B : Type} [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B] {n : ℕ}
    (μ : Measure A) [IsProbabilityMeasure μ] (ν : Measure B) [IsProbabilityMeasure ν]
    {T : A → EuclideanSpace ℝ (Fin n)} {T' : B → EuclideanSpace ℝ (Fin n)}
    (hT : Measurable T) (hT' : Measurable T')
    (π : Measure (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure π]
    (h1 : π.map Prod.fst = μ.map T) (h2 : π.map Prod.snd = ν.map T') :
    ∃ P : Measure (A × B), IsProbabilityMeasure P ∧ P.map Prod.fst = μ ∧ P.map Prod.snd = ν ∧
      P.map (fun ω => (T ω.1, T' ω.2)) = π := by
  have hm1 : Measurable (fun a : A => (T a, a)) := hT.prodMk measurable_id
  have hm2 : Measurable (fun a : B => (T' a, a)) := hT'.prodMk measurable_id
  let ρ1 : Measure (EuclideanSpace ℝ (Fin n) × A) := μ.map (fun a => (T a, a))
  let ρ2 : Measure (EuclideanSpace ℝ (Fin n) × B) := ν.map (fun a => (T' a, a))
  have hρ1f : ρ1.fst = μ.map T := by
    rw [Measure.fst, Measure.map_map measurable_fst hm1]; rfl
  have hρ2f : ρ2.fst = ν.map T' := by
    rw [Measure.fst, Measure.map_map measurable_fst hm2]; rfl
  have hρ1s : ρ1.snd = μ := by
    rw [Measure.snd, Measure.map_map measurable_snd hm1]; exact Measure.map_id
  have hρ2s : ρ2.snd = ν := by
    rw [Measure.snd, Measure.map_map measurable_snd hm2]; exact Measure.map_id
  let κ1 : Kernel (EuclideanSpace ℝ (Fin n)) A := ρ1.condKernel
  let κ2 : Kernel (EuclideanSpace ℝ (Fin n)) B := ρ2.condKernel
  let K : Kernel (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) (A × B) :=
    (κ1.comap Prod.fst measurable_fst) ×ₖ (κ2.comap Prod.snd measurable_snd)
  have hdis1 : ρ1.fst ⊗ₘ κ1 = ρ1 := Measure.disintegrate ρ1 κ1
  have hdis2 : ρ2.fst ⊗ₘ κ2 = ρ2 := Measure.disintegrate ρ2 κ2
  have hset1 : MeasurableSet {p : EuclideanSpace ℝ (Fin n) × A | T p.2 = p.1} :=
    measurableSet_eq_fun (hT.comp measurable_snd) measurable_fst
  have hset2 : MeasurableSet {p : EuclideanSpace ℝ (Fin n) × B | T' p.2 = p.1} :=
    measurableSet_eq_fun (hT'.comp measurable_snd) measurable_fst
  have hae1 : ∀ᵐ e ∂(μ.map T), ∀ᵐ a ∂(κ1 e), T a = e := by
    have hρae : ∀ᵐ p ∂ρ1, T p.2 = p.1 := by
      show ∀ᵐ p ∂(μ.map (fun a => (T a, a))), T p.2 = p.1
      rw [ae_map_iff hm1.aemeasurable hset1]
      exact Filter.Eventually.of_forall fun a => rfl
    rw [← hdis1, Measure.ae_compProd_iff hset1] at hρae
    rwa [hρ1f] at hρae
  have hae2 : ∀ᵐ e ∂(ν.map T'), ∀ᵐ a ∂(κ2 e), T' a = e := by
    have hρae : ∀ᵐ p ∂ρ2, T' p.2 = p.1 := by
      show ∀ᵐ p ∂(ν.map (fun a => (T' a, a))), T' p.2 = p.1
      rw [ae_map_iff hm2.aemeasurable hset2]
      exact Filter.Eventually.of_forall fun a => rfl
    rw [← hdis2, Measure.ae_compProd_iff hset2] at hρae
    rwa [hρ2f] at hρae
  have hπ1 : ∀ᵐ e ∂π, ∀ᵐ a ∂(κ1 e.1), T a = e.1 := by
    rw [← h1] at hae1
    exact ae_of_ae_map measurable_fst.aemeasurable hae1
  have hπ2 : ∀ᵐ e ∂π, ∀ᵐ a ∂(κ2 e.2), T' a = e.2 := by
    rw [← h2] at hae2
    exact ae_of_ae_map measurable_snd.aemeasurable hae2
  have hKapp : ∀ e, K e = (κ1 e.1).prod (κ2 e.2) := fun e => by
    simp only [K]; rw [Kernel.prod_apply]; rfl
  have hKm : Measurable K := K.measurable
  refine ⟨K ∘ₘ π, inferInstance, ?_, ?_, ?_⟩
  · ext s hs
    rw [Measure.map_apply measurable_fst hs]
    show Measure.bind π K _ = _
    rw [Measure.bind_apply (measurable_fst hs) hKm.aemeasurable]
    have e1 : ∀ e, K e (Prod.fst ⁻¹' s) = κ1 e.1 s := fun e => by
      rw [hKapp e, show (Prod.fst ⁻¹' s : Set (A × B)) = s ×ˢ Set.univ from by ext; simp,
        Measure.prod_prod]
      simp
    simp_rw [e1]
    rw [← lintegral_map (f := fun x => κ1 x s) (Kernel.measurable_coe κ1 hs) measurable_fst, h1,
      ← hρ1f]
    have hsn : ρ1.snd = κ1 ∘ₘ ρ1.fst := by
      conv_lhs => rw [← hdis1]
      exact Measure.snd_compProd _ _
    rw [← hρ1s, hsn]
    show _ = Measure.bind ρ1.fst κ1 s
    rw [Measure.bind_apply hs κ1.measurable.aemeasurable]
  · ext s hs
    rw [Measure.map_apply measurable_snd hs]
    show Measure.bind π K _ = _
    rw [Measure.bind_apply (measurable_snd hs) hKm.aemeasurable]
    have e1 : ∀ e, K e (Prod.snd ⁻¹' s) = κ2 e.2 s := fun e => by
      rw [hKapp e, show (Prod.snd ⁻¹' s : Set (A × B)) = Set.univ ×ˢ s from by ext; simp,
        Measure.prod_prod]
      simp
    simp_rw [e1]
    rw [← lintegral_map (f := fun x => κ2 x s) (Kernel.measurable_coe κ2 hs) measurable_snd, h2,
      ← hρ2f]
    have hsn : ρ2.snd = κ2 ∘ₘ ρ2.fst := by
      conv_lhs => rw [← hdis2]
      exact Measure.snd_compProd _ _
    rw [← hρ2s, hsn]
    show _ = Measure.bind ρ2.fst κ2 s
    rw [Measure.bind_apply hs κ2.measurable.aemeasurable]
  · ext W hW
    have hmm : Measurable (fun ω : A × B => (T ω.1, T' ω.2)) :=
      (hT.comp measurable_fst).prodMk (hT'.comp measurable_snd)
    rw [Measure.map_apply hmm hW]
    show Measure.bind π K _ = _
    rw [Measure.bind_apply (hmm hW) hKm.aemeasurable]
    have : ∀ᵐ e ∂π, K e ((fun ω : A × B => (T ω.1, T' ω.2)) ⁻¹' W) = W.indicator 1 e := by
      filter_upwards [hπ1, hπ2] with e he1 he2
      rw [hKapp e]
      have a1 : ∀ᵐ ab ∂((κ1 e.1).prod (κ2 e.2)), T ab.1 = e.1 :=
        Measure.quasiMeasurePreserving_fst.ae he1
      have a2 : ∀ᵐ ab ∂((κ1 e.1).prod (κ2 e.2)), T' ab.2 = e.2 :=
        Measure.quasiMeasurePreserving_snd.ae he2
      by_cases heW : e ∈ W
      · have hh : ∀ᵐ ab ∂((κ1 e.1).prod (κ2 e.2)),
            ab ∈ (fun ω : A × B => (T ω.1, T' ω.2)) ⁻¹' W := by
          filter_upwards [a1, a2] with ab h1 h2
          simp only [Set.mem_preimage, h1, h2]
          exact heW
        rw [Set.indicator_of_mem heW, Pi.one_apply]
        exact (prob_compl_eq_zero_iff (hmm hW)).1 (ae_iff.mp hh)
      · have hh : ∀ᵐ ab ∂((κ1 e.1).prod (κ2 e.2)),
            ab ∉ (fun ω : A × B => (T ω.1, T' ω.2)) ⁻¹' W := by
          filter_upwards [a1, a2] with ab h1 h2
          simp only [Set.mem_preimage, h1, h2]
          exact heW
        rw [Set.indicator_of_notMem heW]
        exact measure_eq_zero_iff_ae_notMem.2 hh
    rw [lintegral_congr_ae this, lintegral_indicator hW]
    simp


/-- Per-test-function `W₁` estimate from a Lindeberg-type bound. -/
lemma w1_test_bound {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X Y : Ω → EuclideanSpace ℝ (Fin n)) (hX : Measurable X)
    (hY : Measurable Y) (hX2 : MemLp X 2 P) (hY2 : MemLp Y 2 P) {Lm : ℝ}
    (hlind : ∀ {K : ℝ} {g : EuclideanSpace ℝ (Fin n) → ℝ}, Yurinskii.TestFn K g →
      |∫ ω, g (X ω) ∂P - ∫ ω, g (Y ω) ∂P| ≤ K * Lm)
    {h : EuclideanSpace ℝ (Fin n) → ℝ} (hh : LipschitzWith 1 h) {ε R : ℝ} (hε : 0 < ε)
    (hR : 0 < R) :
    ∫ ω, h (X ω) ∂P - ∫ ω, h (Y ω) ∂P ≤
      (∫ ω, ‖X ω‖ ^ 2 ∂P + ∫ ω, ‖Y ω‖ ^ 2 ∂P) / (4 * R) + 2 * ε * Real.sqrt n +
        2 / ε ^ 2 * Lm := by
  set u : EuclideanSpace ℝ (Fin n) → ℝ := fun x => h x - h 0
  have hu : LipschitzWith 1 u := LipschitzWith.of_dist_le_mul fun x y => by
    simpa [u, Real.dist_eq] using hh.dist_le_mul x y
  set f : EuclideanSpace ℝ (Fin n) → ℝ := fun x => max (-R) (min R (u x))
  have hfL : LipschitzWith 1 f := (hu.const_min R).const_max (-R)
  have hfc : Continuous f := hfL.continuous
  have hfR : ∀ y, |f y| ≤ R := fun y => by
    rw [abs_le]; simp only [f]; constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)
  have huf : ∀ x, |u x - f x| ≤ ‖x‖ ^ 2 / (4 * R) := fun x => by
    refine clamp_err hR ?_
    have := hu.dist_le_mul x 0
    simpa [u, Real.dist_eq] using this
  set g := gsmooth ε f
  have hgc : ContDiff ℝ 2 g := contDiff_gsmooth hε hfc hfR
  have hfg : ∀ x, |f x - g x| ≤ ε * Real.sqrt n := fun x => by
    rw [abs_sub_comm]; exact gsmooth_sub_le hε hfc hfR hfL x
  have hTF : Yurinskii.TestFn (1 * (2 / ε ^ 2)) g := by
    refine ⟨hgc, by positivity, ⟨R, abs_gsmooth_le hε hfc hfR⟩,
      ⟨1, norm_fderiv_gsmooth_le hε hfc hfR hfL⟩,
      ⟨Real.sqrt n / ε, norm_fderiv_fderiv_gsmooth_le hε hfc hfR hfL⟩, ?_⟩
    intro x y v
    exact hess_gsmooth_lip hε hfc hfR (c := 1) zero_le_one
      (fun x y => by simpa [Real.dist_eq, dist_eq_norm] using hfL.dist_le_mul x y) x y v
  have hXi : Integrable (fun ω => ‖X ω‖) P := (hX2.integrable one_le_two).norm
  have hYi : Integrable (fun ω => ‖Y ω‖) P := (hY2.integrable one_le_two).norm
  have hX2i : Integrable (fun ω => ‖X ω‖ ^ 2) P := hX2.integrable_norm_pow two_ne_zero
  have hY2i : Integrable (fun ω => ‖Y ω‖ ^ 2) P := hY2.integrable_norm_pow two_ne_zero
  have hhX := integrable_lip_comp P hh hX hXi
  have hhY := integrable_lip_comp P hh hY hYi
  have hgb : ∀ z, |g z| ≤ R := abs_gsmooth_le hε hfc hfR
  have hgX : Integrable (fun ω => g (X ω)) P :=
    integrable_comp_of_continuous P hgc.continuous hgb hX.aemeasurable
  have hgY : Integrable (fun ω => g (Y ω)) P :=
    integrable_comp_of_continuous P hgc.continuous hgb hY.aemeasurable
  have hpt : ∀ ω, h (X ω) - h (Y ω) ≤
      (‖X ω‖ ^ 2 + ‖Y ω‖ ^ 2) / (4 * R) + 2 * ε * Real.sqrt n + (g (X ω) - g (Y ω)) := by
    intro ω
    have a1 := abs_le.1 (huf (X ω))
    have a2 := abs_le.1 (huf (Y ω))
    have a3 := abs_le.1 (hfg (X ω))
    have a4 := abs_le.1 (hfg (Y ω))
    have e : h (X ω) - h (Y ω) = u (X ω) - u (Y ω) := by simp [u]
    rw [e, add_div]
    linarith [a1.2, a2.1, a3.2, a4.1]
  have hint : ∫ ω, h (X ω) ∂P - ∫ ω, h (Y ω) ∂P ≤
      (∫ ω, ‖X ω‖ ^ 2 ∂P + ∫ ω, ‖Y ω‖ ^ 2 ∂P) / (4 * R) + 2 * ε * Real.sqrt n +
        (∫ ω, g (X ω) ∂P - ∫ ω, g (Y ω) ∂P) := by
    have hc : ∫ _ω, (2 * ε * Real.sqrt n) ∂P = 2 * ε * Real.sqrt n := by simp
    rw [← integral_sub hhX hhY, ← integral_sub hgX hgY, ← integral_add hX2i hY2i,
      ← integral_div, ← hc,
      ← integral_add (f := fun ω => (‖X ω‖ ^ 2 + ‖Y ω‖ ^ 2) / (4 * R))
        (g := fun _ => 2 * ε * Real.sqrt n) ((hX2i.add hY2i).div_const _) (integrable_const _),
      ← integral_add (f := fun ω => (‖X ω‖ ^ 2 + ‖Y ω‖ ^ 2) / (4 * R) + 2 * ε * Real.sqrt n)
        (g := fun ω => g (X ω) - g (Y ω))
        (((hX2i.add hY2i).div_const _).add (integrable_const _)) (hgX.sub hgY)]
    exact integral_mono (hhX.sub hhY)
      ((((hX2i.add hY2i).div_const _).add (integrable_const _)).add (hgX.sub hgY)) hpt
  have hl := (le_abs_self _).trans (hlind hTF)
  have : 1 * (2 / ε ^ 2) * Lm = 2 / ε ^ 2 * Lm := by ring
  linarith


open Yurinskii in
/-- `W₁` distance between a sum of i.i.d. centered vectors and its Gaussian analogue. -/
theorem w1_iid_gauss {n N : ℕ} (ρ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ρ]
    (h0 : ∀ c, ∫ x, x c ∂ρ = 0) (h3 : Integrable (fun x => ‖x‖ ^ 3) ρ) {ε : ℝ} (hε : 0 < ε) :
    wassersteinE 1 ((Measure.pi fun _ : Fin N => ρ).map (fun p => ∑ i, p i))
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) (∑ _i : Fin N, momentMatrix ρ)) ≤
    ENNReal.ofReal (2 * ε * Real.sqrt n +
      2 / ε ^ 2 * ((2 + c4 / 2) * (N * ∫ x, ‖x‖ ^ 3 ∂ρ))) := by
  set G := multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) (∑ _i : Fin N, momentMatrix ρ)
  have h2ρ : Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2) ρ :=
    (integrable_norm_of_pow3 (P := ρ) (Y := id) measurable_id h3).2
  have hQ : (momentMatrix ρ).PosSemidef := momentMatrix_posSemidef _ h2ρ
  have hQs : (∑ _i : Fin N, momentMatrix ρ).PosSemidef :=
    Matrix.posSemidef_sum _ fun _ _ => hQ
  have : IsProbabilityMeasure G := inferInstance
  let P : Measure ((Fin N → EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin n)) :=
    (Measure.pi fun _ : Fin N => ρ).prod G
  let X : (Fin N → EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun ω => ∑ i, ω.1 i
  let Y : (Fin N → EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun ω => ω.2
  have hXm : Measurable X :=
    Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).comp measurable_fst
  have hYm : Measurable Y := measurable_snd
  have hmemρ : MemLp (id : EuclideanSpace ℝ (Fin n) → _) 2 ρ :=
    (memLp_two_iff_integrable_sq_norm aestronglyMeasurable_id).2 h2ρ
  have hmemG : MemLp (id : EuclideanSpace ℝ (Fin n) → _) 2 G := IsGaussian.memLp_two_id
  have hmp1 : ∀ i : Fin N, MeasurePreserving (fun ω : (Fin N → EuclideanSpace ℝ (Fin n)) ×
      EuclideanSpace ℝ (Fin n) => ω.1 i) P ρ := fun i =>
    (measurePreserving_eval (fun _ : Fin N => ρ) i).comp
      (measurePreserving_fst (μ := Measure.pi fun _ : Fin N => ρ) (ν := G))
  have hX2 : MemLp X 2 P := by
    have : X = ∑ i : Fin N, (fun ω : (Fin N → EuclideanSpace ℝ (Fin n)) ×
        EuclideanSpace ℝ (Fin n) => ω.1 i) := by
      funext ω; simp [X]
    rw [this]
    exact memLp_finsetSum' _ fun i _ => hmemρ.comp_measurePreserving (hmp1 i)
  have hY2 : MemLp Y 2 P :=
    hmemG.comp_measurePreserving (measurePreserving_snd (μ := Measure.pi fun _ : Fin N => ρ) (ν := G))
  have hlawY : P.map Y = G := by
    have := (measurePreserving_snd (μ := Measure.pi fun _ : Fin N => ρ) (ν := G)).map_eq
    exact this
  have hlawX : P.map X = (Measure.pi fun _ : Fin N => ρ).map (fun p => ∑ i, p i) := by
    have hsm : Measurable (fun p : Fin N → EuclideanSpace ℝ (Fin n) => ∑ i, p i) :=
      Finset.measurable_sum _ fun i _ => measurable_pi_apply i
    have e : X = (fun p : Fin N → EuclideanSpace ℝ (Fin n) => ∑ i, p i) ∘ Prod.fst := rfl
    rw [e, ← Measure.map_map hsm measurable_fst]
    congr 1
    exact (measurePreserving_fst (μ := Measure.pi fun _ : Fin N => ρ) (ν := G)).map_eq
  have hlind : ∀ {K : ℝ} {g : EuclideanSpace ℝ (Fin n) → ℝ}, TestFn K g →
      |∫ ω, g (X ω) ∂P - ∫ ω, g (Y ω) ∂P| ≤ K * ((2 + c4 / 2) * (N * ∫ x, ‖x‖ ^ 3 ∂ρ)) := by
    intro K g hg
    have e1 : ∫ ω, g (X ω) ∂P = ∫ x, g x ∂((Measure.pi fun _ : Fin N => ρ).map
        (fun p => ∑ i, p i)) := by
      rw [← hlawX, integral_map hXm.aemeasurable hg.measurable.aestronglyMeasurable]
    have e2 : ∫ ω, g (Y ω) ∂P = ∫ x, g x ∂G := by
      rw [← hlawY, integral_map hYm.aemeasurable hg.measurable.aestronglyMeasurable]
    rw [e1, e2]
    have := lindeberg_gauss hg (fun _ : Fin N => ρ) (fun i c => h0 c) (fun i => h3)
    refine this.trans (le_of_eq ?_)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hdual := wassersteinE_one_le_of_dual P X Y hXm hYm hX2 hY2
    (2 * ε * Real.sqrt n + 2 / ε ^ 2 * ((2 + c4 / 2) * (N * ∫ x, ‖x‖ ^ 3 ∂ρ))) (by
      intro h hh
      refine le_of_forall_pos_le_add fun η hη => ?_
      set m := ∫ ω, ‖X ω‖ ^ 2 ∂P + ∫ ω, ‖Y ω‖ ^ 2 ∂P
      have hm0 : 0 ≤ m := add_nonneg (integral_nonneg fun _ => by positivity)
        (integral_nonneg fun _ => by positivity)
      have hR : 0 < m / (4 * η) + 1 := by positivity
      have := w1_test_bound P X Y hXm hYm hX2 hY2 hlind hh hε hR
      have hmR : m / (4 * (m / (4 * η) + 1)) ≤ η := by
        rw [div_le_iff₀ (by positivity)]
        have : η * (4 * (m / (4 * η) + 1)) = m + 4 * η := by field_simp
        rw [this]; linarith
      linarith)
  have e1 : law P X = (Measure.pi fun _ : Fin N => ρ).map (fun p => ∑ i, p i) := hlawX
  have e2 : law P Y = G := hlawY
  rw [e1, e2] at hdual
  exact hdual


/-- A coupling with cost close to the `W₁` distance. -/
lemma exists_coupling_of_w1 {n : ℕ} (P Q : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {t η : ℝ} (ht : 0 ≤ t) (hη : 0 < η)
    (h : wassersteinE 1 P Q ≤ ENNReal.ofReal t) :
    ∃ π : Measure (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)),
      IsProbabilityMeasure π ∧ π.map Prod.fst = P ∧ π.map Prod.snd = Q ∧
      ∫⁻ z, ‖z.1 - z.2‖ₑ ∂π ≤ ENNReal.ofReal (t + η) := by
  have hlt : wassersteinE 1 P Q < ENNReal.ofReal (t + η) := by
    refine h.trans_lt ?_
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
  unfold wassersteinE at hlt
  obtain ⟨π, hπ⟩ := iInf_lt_iff.1 hlt
  have hcpl : IsCoupling π.1 P Q := π.2
  refine ⟨π.1, hcpl.isProbabilityMeasure, hcpl.1, hcpl.2, ?_⟩
  have : ∫⁻ z, ‖z.1 - z.2‖ₑ ∂π.1 = (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ (1 : ℝ)) ∂π.1) ^ (1 / (1 : ℝ)) := by
    simp [ofReal_norm]
  rw [this]
  exact hπ.le


open Yurinskii in
/-- Abstract coupling: sum of i.i.d. centered vectors versus Gaussian, glued back to the
underlying spaces. -/
theorem coupling_core {A B : Type} [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B] {n N : ℕ}
    (μA : Measure A) [IsProbabilityMeasure μA] (νB : Measure B) [IsProbabilityMeasure νB]
    {T : A → EuclideanSpace ℝ (Fin n)} {T' : B → EuclideanSpace ℝ (Fin n)}
    (hT : Measurable T) (hT' : Measurable T')
    (ρ0 : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ρ0]
    (h0 : ∀ c, ∫ x, x c ∂ρ0 = 0) (h3 : Integrable (fun x => ‖x‖ ^ 3) ρ0)
    (hlawT : μA.map T = (Measure.pi fun _ : Fin N => ρ0).map (fun p => ∑ i, p i))
    (hlawT' : νB.map T' = multivariateGaussian (0 : EuclideanSpace ℝ (Fin n))
      (∑ _i : Fin N, momentMatrix ρ0)) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ P : Measure (A × B), IsProbabilityMeasure P ∧ P.map Prod.fst = μA ∧ P.map Prod.snd = νB ∧
      ∫⁻ ω, ‖T ω.1 - T' ω.2‖ₑ ∂P ≤ ENNReal.ofReal (2 * ε * Real.sqrt n +
        2 / ε ^ 2 * ((2 + c4 / 2) * (N * ∫ x, ‖x‖ ^ 3 ∂ρ0)) + η) := by
  have hw := w1_iid_gauss (N := N) ρ0 h0 h3 hε
  have hI0 : 0 ≤ ∫ x, ‖x‖ ^ 3 ∂ρ0 := integral_nonneg fun x => by positivity
  have ht : 0 ≤ 2 * ε * Real.sqrt n + 2 / ε ^ 2 * ((2 + c4 / 2) * (N * ∫ x, ‖x‖ ^ 3 ∂ρ0)) := by
    have := c4_nonneg
    positivity
  obtain ⟨π, hπ, hπ1, hπ2, hcost⟩ := exists_coupling_of_w1 _ _ ht hη hw
  obtain ⟨P, hP, hP1, hP2, hP3⟩ := glue_two μA νB hT hT' π
    (by rw [hπ1, hlawT]) (by rw [hπ2, hlawT'])
  refine ⟨P, hP, hP1, hP2, ?_⟩
  have hmm : Measurable (fun ω : A × B => (T ω.1, T' ω.2)) :=
    (hT.comp measurable_fst).prodMk (hT'.comp measurable_snd)
  have hf : Measurable (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => ‖z.1 - z.2‖ₑ) :=
    (measurable_fst.sub measurable_snd).enorm
  have : ∫⁻ ω, ‖T ω.1 - T' ω.2‖ₑ ∂P = ∫⁻ z, ‖z.1 - z.2‖ₑ ∂π := by
    rw [← hP3, lintegral_map hf hmm]
  rw [this]
  exact hcost


/-- The Sobolev embedding constant. -/
def sobCs (d : ℕ) (m : ℝ) : ℝ :=
  Real.sqrt 2 * Real.sqrt (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m)))

/-- Fourier-series representative of an `H^m` function (`m > d/2`): `ψ = mean ψ + f` a.e. with
`f` continuous, the uniform limit of the trigonometric partial sums, and `‖f‖_∞ ≤ C ‖ψ‖_{H^m}`. -/
lemma sobolev_rep (m : ℝ) (hm : (d : ℝ) / 2 < m) {ψ : Torus d → ℝ} (hψ : MemSobolev m ψ) :
    ∃ f : Torus d → ℝ, Continuous f ∧ (∀ᵐ x, ψ x = Torus.mean ψ + f x) ∧
      (∀ x, |f x| ≤ sobCs d m * sobolevNorm m ψ) ∧
      TendstoUniformly (fun T : Finset (NonzeroLattice d) => trigPoly T (Torus.funRealCoeff ψ)) f
        atTop := by
  have hm' : (d : ℝ) < 2 * m := by linarith
  have hS2 := summable_jp_rpow (d := d) m hm'
  set c : NonzeroLattice d → ℝ := Torus.funRealCoeff ψ with hc
  have hs := hψ.2
  set W : ℝ := ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * m) * c k ^ 2 with hW
  have hW0 : 0 ≤ W := tsum_nonneg fun k => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (sq_nonneg _)
  -- summability of the coefficients
  have hcs := Torus.cs_tsum (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m))
    (fun k => Lattice.jp k.1 ^ m * |c k|) (fun k => Real.rpow_nonneg (Torus.jp_pos _).le _)
    (fun k => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (abs_nonneg _))
    (by
      refine hS2.congr fun k => ?_
      rw [Torus.jp_rpow_sq]; ring_nf)
    (by
      refine hs.congr fun k => ?_
      rw [mul_pow, Torus.jp_rpow_sq, sq_abs])
  have hcab : ∀ k : NonzeroLattice d, Lattice.jp k.1 ^ (-m) * (Lattice.jp k.1 ^ m * |c k|) = |c k| := by
    intro k
    rw [← mul_assoc, ← Real.rpow_add (Torus.jp_pos _)]; simp
  have hsumabs : Summable fun k => |c k| := by
    simpa [hcab] using hcs.1
  have hsumbound : ∑' k, |c k| ≤ Real.sqrt (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m))) *
      Real.sqrt W := by
    have := hcs.2
    simp only [hcab] at this
    refine this.trans (le_of_eq ?_)
    congr 2
    · refine tsum_congr fun k => ?_
      rw [Torus.jp_rpow_sq]; ring_nf
    · refine tsum_congr fun k => ?_
      rw [mul_pow, Torus.jp_rpow_sq, sq_abs]
  -- the function
  set u : NonzeroLattice d → ℝ := fun k => Real.sqrt 2 * |c k| with hu
  have hu_s : Summable u := hsumabs.mul_left _
  have hterm : ∀ (k : NonzeroLattice d) (x : Torus d), ‖c k * Torus.realMode k x‖ ≤ u k := by
    intro k x
    rw [Real.norm_eq_abs, abs_mul, mul_comm]
    exact mul_le_mul (Torus.abs_realMode_le k x) le_rfl (abs_nonneg _) (Real.sqrt_nonneg _) |>.trans_eq (by simp [hu])
  set f : Torus d → ℝ := fun x => ∑' k, c k * Torus.realMode k x with hf
  have hfc : Continuous f := continuous_tsum (fun k => continuous_const.mul (continuous_realMode k)) hu_s hterm
  have hunif : TendstoUniformly (fun T : Finset (NonzeroLattice d) => trigPoly T c) f atTop := by
    have := tendstoUniformlyOn_tsum (f := fun (k : NonzeroLattice d) (x : Torus d) => c k * Torus.realMode k x)
      hu_s (s := Set.univ) (fun n x _ => hterm n x)
    rw [tendstoUniformlyOn_univ] at this
    exact this
  have hfbound : ∀ x, |f x| ≤ sobCs d m * sobolevNorm m ψ := by
    intro x
    have h1 : |f x| ≤ ∑' k, u k := by
      have := norm_tsum_le_tsum_norm ((hu_s.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => hterm k x)))
      rw [Real.norm_eq_abs] at this
      exact this.trans (Summable.tsum_le_tsum (fun k => hterm k x)
        (hu_s.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => hterm k x)) hu_s)
    have h2 : ∑' k, u k = Real.sqrt 2 * ∑' k, |c k| := tsum_mul_left
    have h3 : Real.sqrt W ≤ sobolevNorm m ψ := by
      unfold sobolevNorm
      exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (Torus.mean ψ)])
    calc |f x| ≤ ∑' k, u k := h1
      _ = Real.sqrt 2 * ∑' k, |c k| := h2
      _ ≤ Real.sqrt 2 * (Real.sqrt (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m))) * Real.sqrt W) :=
          mul_le_mul_of_nonneg_left hsumbound (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt 2 * (Real.sqrt (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m))) * sobolevNorm m ψ) := by
          gcongr
      _ = _ := by unfold sobCs; ring
  refine ⟨f, hfc, ?_, hfbound, hunif⟩
  -- weighted limits of the partial sums
  have hlim : ∀ w : Torus d → ℝ, Continuous w → ∀ B : ℝ, (∀ x, |w x| ≤ B) →
      Tendsto (fun T : Finset (NonzeroLattice d) => ∫ x, w x * trigPoly T c x) atTop
        (𝓝 (∫ x, w x * f x)) := by
    intro w hw B hB
    refine tendsto_integral_filter_of_dominated_convergence
      (bound := fun _ => B * (Real.sqrt 2 * ∑' k, |c k|)) ?_ ?_ (integrable_const _) ?_
    · exact Eventually.of_forall fun T =>
        (hw.mul (continuous_trigPoly T c)).aestronglyMeasurable
    · refine Eventually.of_forall fun T => Eventually.of_forall fun x => ?_
      rw [Real.norm_eq_abs, abs_mul]
      have h1 : |trigPoly T c x| ≤ Real.sqrt 2 * ∑' k, |c k| := by
        unfold trigPoly
        calc |∑ k ∈ T, c k * Torus.realMode k x| ≤ ∑ k ∈ T, |c k * Torus.realMode k x| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ k ∈ T, u k := Finset.sum_le_sum fun k _ => by
              simpa [Real.norm_eq_abs] using hterm k x
          _ ≤ ∑' k, u k := hu_s.sum_le_tsum T (fun k _ => by simp [hu])
          _ = _ := tsum_mul_left
      have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB x)
      exact mul_le_mul (hB x) h1 (abs_nonneg _) hB0
    · refine Eventually.of_forall fun x => ?_
      exact (hunif.tendsto_at x).const_mul (w x)
  have hcoef : ∀ k : NonzeroLattice d, Torus.funRealCoeff f k = c k := by
    intro k
    have h := hlim (Torus.realMode k) (continuous_realMode k) (Real.sqrt 2)
      (fun x => Torus.abs_realMode_le k x)
    have h2 : ∀ᶠ T : Finset (NonzeroLattice d) in atTop,
        ∫ x, Torus.realMode k x * trigPoly T c x = c k := by
      filter_upwards [eventually_ge_atTop {k}] with T hT
      have := funRealCoeff_trigPoly T c k
      unfold Torus.funRealCoeff at this
      rw [this]; simp [hT (Finset.mem_singleton_self k)]
    have h3 := h.congr' h2
    exact tendsto_nhds_unique h3 tendsto_const_nhds
  have hmean0 : ∫ x, f x = 0 := by
    have h := hlim (fun _ => 1) continuous_const 1 (fun x => by simp)
    have h2 : ∀ᶠ T : Finset (NonzeroLattice d) in atTop,
        ∫ x, (1 : ℝ) * trigPoly T c x = 0 := by
      refine Eventually.of_forall fun T => ?_
      simp only [one_mul]
      unfold trigPoly
      rw [integral_finsetSum _ fun k _ => ((continuous_realMode k).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)).const_mul _]
      simp [integral_const_mul, Torus.integral_realMode]
    have h3 := h.congr' h2
    have := tendsto_nhds_unique h3 tendsto_const_nhds
    simpa using this
  -- the difference has vanishing Fourier data
  have hψL2 : MemLp ψ 2 volume := hψ.1
  have hfL2 : MemLp f 2 volume := by
    refine MemLp.of_bound hfc.aestronglyMeasurable (sobCs d m * sobolevNorm m ψ)
      (Eventually.of_forall fun x => ?_)
    simpa using hfbound x
  set g : Torus d → ℝ := fun x => ψ x - Torus.mean ψ - f x with hg
  have hgL2 : MemLp g 2 volume := (hψL2.sub (memLp_const _)).sub hfL2
  have hint_ek : ∀ (h : Torus d → ℝ), MemLp h 2 volume → ∀ k : NonzeroLattice d,
      Integrable (fun x => Torus.realMode k x * h x) := by
    intro h hh k
    exact (hh.integrable one_le_two).bdd_mul (c := Real.sqrt 2)
      (continuous_realMode k).aestronglyMeasurable
      (Eventually.of_forall fun x => by simpa using Torus.abs_realMode_le k x)
  have hgc : ∀ k, Torus.funRealCoeff g k = 0 := by
    intro k
    have e : ∀ x, Torus.realMode k x * g x =
        Torus.realMode k x * ψ x - Torus.mean ψ * Torus.realMode k x -
          Torus.realMode k x * f x := fun x => by simp only [hg]; ring
    unfold Torus.funRealCoeff
    simp_rw [e]
    have i1 := hint_ek ψ hψL2 k
    have i2 : Integrable (fun x => Torus.mean ψ * Torus.realMode k x) :=
      ((continuous_realMode k).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)).const_mul _
    have i3 := hint_ek f hfL2 k
    have i12 : Integrable (fun x => Torus.realMode k x * ψ x - Torus.mean ψ * Torus.realMode k x) :=
      i1.sub i2
    rw [integral_sub i12 i3, integral_sub i1 i2, integral_const_mul,
      Torus.integral_realMode]
    have := hcoef k
    unfold Torus.funRealCoeff at this
    rw [this]
    simp [hc, Torus.funRealCoeff]
  have hgmean : Torus.mean g = 0 := by
    unfold Torus.mean
    have i1 : Integrable ψ := hψL2.integrable one_le_two
    have i3 : Integrable f := hfL2.integrable one_le_two
    simp only [hg]
    have i12 : Integrable (fun x => ψ x - Torus.mean ψ) := i1.sub (integrable_const _)
    rw [integral_sub i12 i3, integral_sub i1 (integrable_const _), hmean0]
    simp [Torus.mean]
  have hpars := Torus.parseval_realCoeff g hgL2
  simp only [hgmean, hgc, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, tsum_zero,
    add_zero] at hpars
  have hz : ∫ x, g x ^ 2 = 0 := by simpa using hpars
  have hsq : Integrable (fun x => g x ^ 2) := hgL2.integrable_sq
  have h0 : (fun x => g x ^ 2) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hsq).1 hz
  filter_upwards [h0] with x hx
  have : g x = 0 := by simpa using hx
  simp only [hg] at this
  linarith


lemma tendsto_pair_mul {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {F G : ι → Torus d → ℝ} {f g : Torus d → ℝ}
    (hF : ∀ n, Continuous (F n)) (hG : ∀ n, Continuous (G n))
    (hFu : TendstoUniformly F f l) (hGu : TendstoUniformly G g l) {Bf Bg : ℝ}
    (hfB : ∀ x, |f x| ≤ Bf) (hgB : ∀ x, |g x| ≤ Bg) :
    Tendsto (fun n => pair μ (fun x => F n x * G n x)) l (𝓝 (pair μ (fun x => f x * g x))) := by
  unfold pair
  have hBf : 0 ≤ Bf := (abs_nonneg _).trans (hfB 0)
  have hBg : 0 ≤ Bg := (abs_nonneg _).trans (hgB 0)
  refine tendsto_integral_filter_of_dominated_convergence
    (bound := fun _ => (Bf + 1) * (Bg + 1)) ?_ ?_ (integrable_const _) ?_
  · exact Eventually.of_forall fun n => ((hF n).mul (hG n)).aestronglyMeasurable
  · have h1 := (Metric.tendstoUniformly_iff.1 hFu) 1 one_pos
    have h2 := (Metric.tendstoUniformly_iff.1 hGu) 1 one_pos
    filter_upwards [h1, h2] with n hn1 hn2
    refine Eventually.of_forall fun x => ?_
    have a1 : |F n x| ≤ Bf + 1 := by
      have h := hn1 x
      rw [Real.dist_eq] at h
      have h' := abs_sub_abs_le_abs_sub (F n x) (f x)
      rw [abs_sub_comm] at h'
      linarith [hfB x]
    have a2 : |G n x| ≤ Bg + 1 := by
      have h := hn2 x
      rw [Real.dist_eq] at h
      have h' := abs_sub_abs_le_abs_sub (G n x) (g x)
      rw [abs_sub_comm] at h'
      linarith [hgB x]
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul a1 a2 (abs_nonneg _) (by linarith)
  · exact Eventually.of_forall fun x => (hFu.tendsto_at x).mul (hGu.tendsto_at x)


lemma summable_trigPoly (m : ℝ) (T : Finset (NonzeroLattice d)) (c : NonzeroLattice d → ℝ) :
    Summable fun k : NonzeroLattice d =>
      Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff (trigPoly T c) k ^ 2 := by
  refine summable_of_ne_finset_zero (s := T) fun k hk => ?_
  rw [funRealCoeff_trigPoly]; simp [hk]

lemma yvec_trig_tendsto (m : ℝ) {ψ : Torus d → ℝ}
    (hs : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff ψ k ^ 2) :
    Tendsto (fun T : Finset (NonzeroLattice d) =>
      yvec m (trigPoly T (Torus.funRealCoeff ψ)) (summable_trigPoly m T _)) atTop
      (𝓝 (yvec m ψ hs)) := by
  set c : NonzeroLattice d → ℝ := Torus.funRealCoeff ψ with hc
  set y : NegSobolev d m := yvec m ψ hs with hy
  have hyT : ∀ T : Finset (NonzeroLattice d), yvec m (trigPoly T c) (summable_trigPoly m T c) =
      ∑ i ∈ T, (lp.single 2 i (NegSobolev.coord y i) :
        lp (fun _ : NonzeroLattice d => ℝ) 2) := by
    intro T
    refine Subtype.ext (funext fun k => ?_)
    simp only [lp.coeFn_sum, Finset.sum_apply, lp.single_apply]
    have e1 : NegSobolev.coord (yvec m (trigPoly T c) (summable_trigPoly m T c)) k =
        Lattice.jp k.1 ^ m * (if k ∈ T then c k else 0) := by
      show Lattice.jp k.1 ^ m * Torus.funRealCoeff (trigPoly T c) k = _
      rw [funRealCoeff_trigPoly]
    change NegSobolev.coord (yvec m (trigPoly T c) (summable_trigPoly m T c)) k = _
    rw [e1]
    by_cases hk : k ∈ T
    · simp [hk, NegSobolev.coord, hy, yvec, hc]
    · simp [hk]
  have hsum := lp.hasSum_single (E := fun _ : NonzeroLattice d => ℝ) (p := 2) ENNReal.ofNat_ne_top
    (y : lp (fun _ : NonzeroLattice d => ℝ) 2)
  simp_rw [hyT]
  exact hsum

lemma iidCov_congr_rep {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {ψ φ f g : Torus d → ℝ}
    {a b : ℝ} (hf : Continuous f) (hg : Continuous g)
    (hψ : ∀ᵐ x ∂μ, ψ x = a + f x) (hφ : ∀ᵐ x ∂μ, φ x = b + g x) :
    iidCov μ ψ φ = iidCov μ f g := by
  have hfi : Integrable f μ := hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hgi : Integrable g μ := hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hfgi : Integrable (fun x => f x * g x) μ :=
    (hf.mul hg).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  unfold iidCov pair
  have e1 : ∫ x, ψ x * φ x ∂μ = ∫ x, ((a * b + a * g x) + (b * f x + f x * g x)) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hψ, hφ] with x h1 h2
    rw [h1, h2]; ring
  have e2 : ∫ x, ψ x ∂μ = a + ∫ x, f x ∂μ := by
    rw [integral_congr_ae (hψ.mono fun x h => h), integral_add (integrable_const _) hfi]
    simp
  have e3 : ∫ x, φ x ∂μ = b + ∫ x, g x ∂μ := by
    rw [integral_congr_ae (hφ.mono fun x h => h), integral_add (integrable_const _) hgi]
    simp
  rw [e1, e2, e3]
  have i1 : Integrable (fun x => a * b + a * g x) μ :=
    (integrable_const _).add (hgi.const_mul a)
  have i2 : Integrable (fun x => b * f x + f x * g x) μ := (hfi.const_mul b).add hfgi
  rw [integral_add i1 i2, integral_add (integrable_const _) (hgi.const_mul a),
    integral_add (hfi.const_mul b) hfgi]
  simp only [integral_const_mul, integral_const, probReal_univ, one_smul]
  ring


lemma gauss_cov_eval (m : ℝ) (hm : (d : ℝ) / 2 < m) {μ : Measure (Torus d)}
    [IsProbabilityMeasure μ] (hμ : μ ≪ volume) {ν : Measure (NegSobolev d m)}
    [IsProbabilityMeasure ν] (hν : IsCenteredGaussianWithCov m ν (iidCov μ)) {ψ φ : Torus d → ℝ}
    (hψ : MemSobolev m ψ) (hφ : MemSobolev m φ) :
    ∫ F, NegSobolev.eval F ψ * NegSobolev.eval F φ ∂ν = iidCov μ ψ φ := by
  have := negSobolev_secondCountable d m
  have hG := hν.1.1
  have hmem : MemLp id 2 ν := IsGaussian.memLp_two_id
  have hmean : ∫ z, id z ∂ν = 0 := gaussian_integral_id_eq_zero hν.1
  have hcov : ∀ x y : NegSobolev d m, covarianceBilin ν x y =
      ∫ F, inner ℝ x F * inner ℝ y F ∂ν := by
    intro x y
    rw [covarianceBilin_apply hmem]
    simp only [hmean, sub_zero]
  obtain ⟨fψ, hfψc, hfψae, hfψB, hfψu⟩ := sobolev_rep m hm hψ
  obtain ⟨fφ, hfφc, hfφae, hfφB, hfφu⟩ := sobolev_rep m hm hφ
  set cψ := Torus.funRealCoeff ψ
  set cφ := Torus.funRealCoeff φ
  have hsψ := hψ.2
  have hsφ := hφ.2
  have h1 : ∫ F, NegSobolev.eval F ψ * NegSobolev.eval F φ ∂ν =
      covarianceBilin ν (yvec m ψ hsψ) (yvec m φ hsφ) := by
    rw [hcov]
    refine integral_congr_ae (Eventually.of_forall fun F => ?_)
    simp only [eval_eq_inner m ψ hsψ, eval_eq_inner m φ hsφ]
  rw [h1]
  have hcont : Continuous (fun p : NegSobolev d m × NegSobolev d m => covarianceBilin ν p.1 p.2) :=
    (covarianceBilin ν).continuous₂
  have hA := (hcont.tendsto (yvec m ψ hsψ, yvec m φ hsφ)).comp
    ((yvec_trig_tendsto m hsψ).prodMk_nhds (yvec_trig_tendsto m hsφ))
  have hEq : ∀ T : Finset (NonzeroLattice d),
      covarianceBilin ν (yvec m (trigPoly T cψ) (summable_trigPoly m T cψ))
        (yvec m (trigPoly T cφ) (summable_trigPoly m T cφ)) =
      iidCov μ (trigPoly T cψ) (trigPoly T cφ) := by
    intro T
    rw [hcov]
    have : ∀ F : NegSobolev d m, inner ℝ (yvec m (trigPoly T cψ) (summable_trigPoly m T cψ)) F *
        inner ℝ (yvec m (trigPoly T cφ) (summable_trigPoly m T cφ)) F =
        NegSobolev.eval F (trigPoly T cψ) * NegSobolev.eval F (trigPoly T cφ) := by
      intro F
      rw [eval_eq_inner m _ (summable_trigPoly m T cψ), eval_eq_inner m _ (summable_trigPoly m T cφ)]
    simp_rw [this]
    exact hν.2 _ _ (isSmooth_trigPoly T cψ) (isSmooth_trigPoly T cφ)
  have hA' : Tendsto (fun T : Finset (NonzeroLattice d) => iidCov μ (trigPoly T cψ) (trigPoly T cφ))
      atTop (𝓝 (covarianceBilin ν (yvec m ψ hsψ) (yvec m φ hsφ))) := by
    refine hA.congr fun T => ?_
    exact hEq T
  have hB : Tendsto (fun T : Finset (NonzeroLattice d) => iidCov μ (trigPoly T cψ) (trigPoly T cφ))
      atTop (𝓝 (iidCov μ fψ fφ)) := by
    unfold iidCov
    refine Tendsto.sub ?_ (Tendsto.mul ?_ ?_)
    · exact tendsto_pair_mul (fun T => continuous_trigPoly T cψ) (fun T => continuous_trigPoly T cφ)
        hfψu hfφu hfψB hfφB
    · have := tendsto_pair_mul (μ := μ) (G := fun _ _ => (1 : ℝ)) (g := fun _ => 1)
        (fun T => continuous_trigPoly T cψ) (fun _ => continuous_const) hfψu
        (tendsto_const_nhds (x := (1:ℝ))).tendstoUniformly_const hfψB (fun _ => by simp : ∀ x : Torus d, |(1 : ℝ)| ≤ 1)
      simpa using this
    · have := tendsto_pair_mul (μ := μ) (G := fun _ _ => (1 : ℝ)) (g := fun _ => 1)
        (fun T => continuous_trigPoly T cφ) (fun _ => continuous_const) hfφu
        (tendsto_const_nhds (x := (1:ℝ))).tendstoUniformly_const hfφB (fun _ => by simp : ∀ x : Torus d, |(1 : ℝ)| ≤ 1)
      simpa using this
  have hrep := iidCov_congr_rep (μ := μ) hfψc hfφc (hμ.ae_le hfψae) (hμ.ae_le hfφae)
  rw [hrep]
  exact tendsto_nhds_unique hA' hB


lemma gauss_law_eval (m : ℝ) (hm : (d : ℝ) / 2 < m) {μ : Measure (Torus d)}
    [IsProbabilityMeasure μ] (hμ : μ ≪ volume) {ν : Measure (NegSobolev d m)}
    [IsProbabilityMeasure ν] (hν : IsCenteredGaussianWithCov m ν (iidCov μ)) {p : ℕ}
    (ψ : Fin p → Torus d → ℝ) (hψ : ∀ a, MemSobolev m (ψ a)) (M : Matrix (Fin p) (Fin p) ℝ)
    (hM : M.PosSemidef) (hMe : ∀ a b, M a b = iidCov μ (ψ a) (ψ b)) :
    ν.map (fun F => (WithLp.toLp 2 fun a => NegSobolev.eval F (ψ a) : EuclideanSpace ℝ (Fin p))) =
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) M := by
  have := negSobolev_secondCountable d m
  have hG := hν.1.1
  have hmeanν : ∫ z, id z ∂ν = 0 := gaussian_integral_id_eq_zero hν.1
  set y : Fin p → NegSobolev d m := fun a => yvec m (ψ a) (hψ a).2 with hy
  let A : NegSobolev d m →L[ℝ] EuclideanSpace ℝ (Fin p) :=
    ∑ a : Fin p, (innerSL ℝ (y a)).smulRight (EuclideanSpace.single a (1 : ℝ))
  have hA : ∀ F, A F = (WithLp.toLp 2 fun a => NegSobolev.eval F (ψ a) :
      EuclideanSpace ℝ (Fin p)) := by
    intro F
    ext b
    simp [A, Pi.single_apply, eval_eq_inner m (ψ b) (hψ b).2 F, hy]
  have hfun : (fun F => (WithLp.toLp 2 fun a => NegSobolev.eval F (ψ a) :
      EuclideanSpace ℝ (Fin p))) = fun F => A F := funext fun F => (hA F).symm
  rw [hfun]
  have hGA : IsGaussian (ν.map A) := inferInstance
  have hGM : IsGaussian (multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) M) := inferInstance
  have hmA : (ν.map A)[id] = 0 := by
    show ∫ z, id z ∂(ν.map A) = 0
    rw [integral_map A.continuous.aemeasurable aestronglyMeasurable_id]
    simp only [id]
    rw [A.integral_comp_id_comm IsGaussian.integrable_id]
    have : ∫ F, F ∂ν = 0 := hmeanν
    rw [this, map_zero]
  refine IsGaussian.ext (hmA.trans integral_id_multivariateGaussian'.symm) ?_
  ext u v
  rw [covarianceBilin_multivariateGaussian hM]
  have hmemA : MemLp id 2 (ν.map A) := IsGaussian.memLp_two_id
  rw [covarianceBilin_apply hmemA, hmA, integral_map A.continuous.aemeasurable (by fun_prop)]
  simp only [id, sub_zero]
  have hint : ∀ a b, Integrable (fun F : NegSobolev d m => inner ℝ (y a) F * inner ℝ (y b) F) ν :=
    fun a b => (IsGaussian.memLp_dual ν (innerSL ℝ (y a)) 2 (by simp)).integrable_mul
      (IsGaussian.memLp_dual ν (innerSL ℝ (y b)) 2 (by simp))
  have hcb : ∀ a b, ∫ F, inner ℝ (y a) F * inner ℝ (y b) F ∂ν = M a b := by
    intro a b
    rw [hMe, ← gauss_cov_eval m hm hμ hν (hψ a) (hψ b)]
    refine integral_congr_ae (Eventually.of_forall fun F => ?_)
    simp only [eval_eq_inner m (ψ a) (hψ a).2, eval_eq_inner m (ψ b) (hψ b).2, hy]
  have hin : ∀ (w : EuclideanSpace ℝ (Fin p)) F, inner ℝ w (A F) = ∑ a, w a * inner ℝ (y a) F := by
    intro w F
    rw [hA F]
    simp [PiLp.inner_apply, mul_comm, hy, eval_eq_inner m _ (hψ _).2]
  simp_rw [hin]
  simp only [Finset.sum_mul_sum]
  have hint2 : ∀ a b, Integrable (fun F : NegSobolev d m =>
      u a * inner ℝ (y a) F * (v b * inner ℝ (y b) F)) ν := fun a b =>
    ((hint a b).const_mul (u a * v b)).congr (Eventually.of_forall fun F => by ring)
  have hL : ∫ F, ∑ a, ∑ b, u a * inner ℝ (y a) F * (v b * inner ℝ (y b) F) ∂ν =
      ∑ a, ∑ b, u a * v b * M a b := by
    rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hint2 a b]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finsetSum _ fun b _ => hint2 a b]
    refine Finset.sum_congr rfl fun b _ => ?_
    have : ∀ F : NegSobolev d m, u a * inner ℝ (y a) F * (v b * inner ℝ (y b) F) =
        (u a * v b) * (inner ℝ (y a) F * inner ℝ (y b) F) := fun F => by ring
    simp_rw [this]
    rw [integral_const_mul, hcb]
  rw [hL]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring



lemma integrable_contA (μ : Measure (Torus d)) [IsProbabilityMeasure μ] {f : Torus d → ℝ}
    (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The normalised, centered summand vector `ξ(x) = N^{-1/2} (f_a(x) - μ(f_a))_a`. -/
def xiVec (μ : Measure (Torus d)) (N : ℕ) {p : ℕ} (f : Fin p → Torus d → ℝ) (x : Torus d) :
    EuclideanSpace ℝ (Fin p) :=
  WithLp.toLp 2 fun a => (Real.sqrt N)⁻¹ * (f a x - pair μ (f a))

lemma xiVec_apply (μ : Measure (Torus d)) (N : ℕ) {p : ℕ} (f : Fin p → Torus d → ℝ) (x : Torus d)
    (a : Fin p) : xiVec μ N f x a = (Real.sqrt N)⁻¹ * (f a x - pair μ (f a)) := rfl

lemma continuous_xiVec (μ : Measure (Torus d)) (N : ℕ) {p : ℕ} (f : Fin p → Torus d → ℝ)
    (hf : ∀ a, Continuous (f a)) : Continuous (xiVec μ N f) := by
  unfold xiVec
  exact (PiLp.continuous_toLp 2 _).comp
    (continuous_pi fun a => continuous_const.mul ((hf a).sub continuous_const))

lemma abs_pair_le {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {f : Torus d → ℝ} {B : ℝ}
    (hB : ∀ x, |f x| ≤ B) : |pair μ f| ≤ B := by
  unfold pair
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := f) (C := B)
    (Eventually.of_forall fun x => by simpa using hB x)
  simpa using this

lemma abs_xiVec_le {μ : Measure (Torus d)} [IsProbabilityMeasure μ] (N : ℕ) {p : ℕ}
    (f : Fin p → Torus d → ℝ) {B : ℝ} (hB : ∀ a x, |f a x| ≤ B) (x : Torus d) (a : Fin p) :
    |xiVec μ N f x a| ≤ 2 * B / Real.sqrt N := by
  rw [xiVec_apply, abs_mul, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _)]
  have h1 : |f a x - pair μ (f a)| ≤ 2 * B :=
    (abs_sub _ _).trans (by linarith [hB a x, abs_pair_le (μ := μ) (hB a)])
  rw [div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 (Real.sqrt_nonneg _))

lemma norm_xiVec_le {μ : Measure (Torus d)} [IsProbabilityMeasure μ] (N : ℕ) {p : ℕ}
    (f : Fin p → Torus d → ℝ) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ a x, |f a x| ≤ B) (x : Torus d) :
    ‖xiVec μ N f x‖ ≤ Real.sqrt p * (2 * B / Real.sqrt N) := by
  rw [EuclideanSpace.norm_eq]
  have hc : 0 ≤ 2 * B / Real.sqrt N := by positivity
  calc Real.sqrt (∑ a, ‖xiVec μ N f x a‖ ^ 2) ≤ Real.sqrt (∑ _a : Fin p, (2 * B / Real.sqrt N) ^ 2) := by
        refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun a _ => ?_)
        rw [Real.norm_eq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (abs_xiVec_le N f hB x a) 2
    _ = Real.sqrt p * (2 * B / Real.sqrt N) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hc]

lemma integral_xiVec_coord {μ : Measure (Torus d)} [IsProbabilityMeasure μ] (N : ℕ) {p : ℕ}
    (f : Fin p → Torus d → ℝ) (hf : ∀ a, Continuous (f a)) (c : Fin p) :
    ∫ x, xiVec μ N f x c ∂μ = 0 := by
  simp only [xiVec_apply]
  rw [integral_const_mul, integral_sub (integrable_contA μ (hf c)) (integrable_const _)]
  simp [pair]

lemma integral_xiVec_mul {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {N : ℕ} (hN : 1 ≤ N)
    {p : ℕ} (f : Fin p → Torus d → ℝ) (hf : ∀ a, Continuous (f a)) (a b : Fin p) :
    ∫ x, xiVec μ N f x a * xiVec μ N f x b ∂μ = (N : ℝ)⁻¹ * iidCov μ (f a) (f b) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsq : (Real.sqrt N)⁻¹ * (Real.sqrt N)⁻¹ = (N : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hNpos.le]
  have e : ∀ x, xiVec μ N f x a * xiVec μ N f x b =
      (N : ℝ)⁻¹ * ((f a x * f b x - pair μ (f b) * f a x) - pair μ (f a) * f b x +
        pair μ (f a) * pair μ (f b)) := by
    intro x
    simp only [xiVec_apply]
    rw [← hsq]; ring
  simp_rw [e]
  have ia := integrable_contA μ (hf a)
  have ib := integrable_contA μ (hf b)
  have iab : Integrable (fun x => f a x * f b x) μ := integrable_contA μ ((hf a).mul (hf b))
  have i1 : Integrable (fun x => f a x * f b x - pair μ (f b) * f a x) μ := iab.sub (ia.const_mul _)
  have i2 : Integrable (fun x => (f a x * f b x - pair μ (f b) * f a x) - pair μ (f a) * f b x) μ :=
    i1.sub (ib.const_mul _)
  rw [integral_const_mul, integral_add i2 (integrable_const _), integral_sub i1 (ib.const_mul _),
    integral_sub iab (ia.const_mul _), integral_const_mul, integral_const_mul]
  simp only [integral_const, probReal_univ, one_smul]
  unfold iidCov pair
  ring

lemma integral_norm_sq_xiVec_le {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {N : ℕ}
    (hN : 1 ≤ N) {p : ℕ} (f : Fin p → Torus d → ℝ) (hf : ∀ a, Continuous (f a)) {B : ℝ}
    (hB : ∀ a x, |f a x| ≤ B) :
    ∫ x, ‖xiVec μ N f x‖ ^ 2 ∂μ ≤ p * B ^ 2 / N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have e : ∀ x, ‖xiVec μ N f x‖ ^ 2 = ∑ a, xiVec μ N f x a * xiVec μ N f x a := by
    intro x
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.sum_congr rfl fun a _ => by ring
  simp_rw [e]
  have hi : ∀ a, Integrable (fun x => xiVec μ N f x a * xiVec μ N f x a) μ := by
    intro a
    have hc : Continuous fun x => xiVec μ N f x a := by
      simp only [xiVec_apply]; exact continuous_const.mul ((hf a).sub continuous_const)
    exact integrable_contA μ (hc.mul hc)
  rw [integral_finsetSum _ fun a _ => hi a]
  calc ∑ a, ∫ x, xiVec μ N f x a * xiVec μ N f x a ∂μ = ∑ a : Fin p, (N : ℝ)⁻¹ * iidCov μ (f a) (f a) :=
        Finset.sum_congr rfl fun a _ => integral_xiVec_mul hN f hf a a
    _ ≤ ∑ _a : Fin p, (N : ℝ)⁻¹ * B ^ 2 := by
        refine Finset.sum_le_sum fun a _ => ?_
        refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hNpos.le)
        unfold iidCov
        have h1 : pair μ (fun x => f a x * f a x) ≤ B ^ 2 := by
          unfold pair
          have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun x => f a x * f a x) (C := B ^ 2)
            (Eventually.of_forall fun x => by
              rw [Real.norm_eq_abs, abs_mul]
              nlinarith [hB a x, abs_nonneg (f a x)])
          simpa using (le_abs_self _).trans (by simpa using this)
        nlinarith [sq_nonneg (pair μ (f a))]
    _ = p * B ^ 2 / N := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp

lemma rpow_eighth_facts {N : ℕ} (hN : 1 ≤ N) :
    0 < (N : ℝ) ^ (-(1 : ℝ) / 8) ∧ (N : ℝ) ^ (-(1 : ℝ) / 8) ≤ 1 ∧
      ((N : ℝ) ^ (-(1 : ℝ) / 8)) ^ 4 = (Real.sqrt N)⁻¹ := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  refine ⟨Real.rpow_pos_of_pos hNpos _, Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num), ?_⟩
  rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le, Real.sqrt_eq_rpow, ← Real.rpow_neg hNpos.le]
  norm_num

lemma coupling_numeric {N : ℕ} (hN : 1 ≤ N) (p : ℕ) {B L c : ℝ} (hB : 0 ≤ B) (hc : 0 ≤ c)
    (hL : L ≤ 2 * (Real.sqrt p * p) * B ^ 3 / Real.sqrt N) :
    2 * ((B + 1) * (N : ℝ) ^ (-(1 : ℝ) / 8)) * Real.sqrt p +
      2 / ((B + 1) * (N : ℝ) ^ (-(1 : ℝ) / 8)) ^ 2 * (c * L) + (N : ℝ) ^ (-(1 : ℝ) / 8) ≤
    (2 * Real.sqrt p + 4 * c * (Real.sqrt p * p) + 1) * (B + 1) * (N : ℝ) ^ (-(1 : ℝ) / 8) := by
  obtain ⟨hr0, hr1, hr4⟩ := rpow_eighth_facts hN
  set r := (N : ℝ) ^ (-(1 : ℝ) / 8) with hr
  set q := Real.sqrt p * p with hq
  have hq0 : 0 ≤ q := by positivity
  have hL' : L ≤ 2 * q * B ^ 3 * r ^ 4 := by
    rw [hr4]; rw [div_eq_mul_inv] at hL; linarith
  have hB1 : 0 < B + 1 := by linarith
  have h2 : 2 / ((B + 1) * r) ^ 2 * (c * L) ≤ 4 * c * q * (B + 1) * r := by
    have hden : 0 < ((B + 1) * r) ^ 2 := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ hden]
    have h3 : c * L ≤ c * (2 * q * B ^ 3 * r ^ 4) := mul_le_mul_of_nonneg_left hL' hc
    have h4 : 2 * (c * L) ≤ 2 * (c * (2 * q * B ^ 3 * r ^ 4)) := by linarith
    refine h4.trans ?_
    have hB3 : B ^ 3 ≤ (B + 1) ^ 3 := pow_le_pow_left₀ hB (by linarith) 3
    have hr2 : r ^ 2 ≤ r := by nlinarith
    have hcq : 0 ≤ c * q := mul_nonneg hc hq0
    calc 2 * (c * (2 * q * B ^ 3 * r ^ 4)) = 4 * (c * q) * B ^ 3 * r ^ 4 := by ring
      _ ≤ 4 * (c * q) * (B + 1) ^ 3 * r ^ 4 := by gcongr
      _ = 4 * c * q * (B + 1) * r * ((B + 1) * r) ^ 2 * (r ^ 2 / r) := by field_simp
      _ ≤ 4 * c * q * (B + 1) * r * ((B + 1) * r) ^ 2 * 1 := by
          gcongr
          rw [div_le_one hr0]; exact hr2
      _ = _ := by ring
  have h5 : 1 ≤ B + 1 := by linarith
  have hs0 : 0 ≤ Real.sqrt p := Real.sqrt_nonneg _
  calc 2 * ((B + 1) * r) * Real.sqrt p + 2 / ((B + 1) * r) ^ 2 * (c * L) + r
      ≤ 2 * ((B + 1) * r) * Real.sqrt p + 4 * c * q * (B + 1) * r + r := by linarith
    _ ≤ 2 * ((B + 1) * r) * Real.sqrt p + 4 * c * q * (B + 1) * r + (B + 1) * r := by
        have : r ≤ (B + 1) * r := by nlinarith
        linarith
    _ = (2 * Real.sqrt p + 4 * c * q + 1) * (B + 1) * r := by ring

lemma iidStat_eq_of_rep {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {N : ℕ} (hN : 1 ≤ N)
    {ψ f : Torus d → ℝ} {a : ℝ} (hf : Continuous f) (hrep : ∀ᵐ x ∂μ, ψ x = a + f x)
    (X : Config d N) (hX : ∀ i, ψ (X i) = a + f (X i)) :
    iidStat μ ψ X = (Real.sqrt N)⁻¹ * ∑ i, (f (X i) - pair μ f) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : pair μ ψ = a + pair μ f := by
    unfold pair
    rw [integral_congr_ae hrep, integral_add (integrable_const _) (integrable_contA μ hf)]
    simp
  unfold iidStat
  rw [pair_empirical (by omega), h1]
  simp only [hX, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Finset.sum_sub_distrib]
  have hs : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hNpos.le
  have hs0 : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  field_simp
  rw [Real.sq_sqrt hNpos.le]
  ring


lemma sobCs_nonneg (d : ℕ) (m : ℝ) : 0 ≤ sobCs d m := by
  unfold sobCs; positivity

lemma standardBorel_config (d N : ℕ) : StandardBorelSpace (Config d N) := by
  haveI : BorelSpace (Config d N) := Pi.borelSpace
  haveI : PolishSpace (Config d N) := {}
  infer_instance

lemma standardBorel_negSobolev (d : ℕ) (m : ℝ) : StandardBorelSpace (NegSobolev d m) := by
  haveI := negSobolev_secondCountable d m
  infer_instance


end InitialDataAux

open InitialDataAux in
/-- Lemma A.36, `B:eq:iid-coupling` (source lines 11546-11549): for every finite family
`ψ_1, …, ψ_p ∈ Y_0 = H^{m₀}` there is a coupling of `X_N^0 ∼ (μ°)^{⊗N}` and `η° ∼ ν` with
`E |(⟨ψ_a, √N(μ_N^0 - μ°)⟩)_a - (⟨ψ_a, η°⟩)_a|_{ℓ²} ≤ C_p (1 + max_a ‖ψ_a‖^{3/2}_{H^{m₀}}) N^{-1/8}`.
The constant depends on `d, m₀, p` only.  (Hence (I1) with `ε_N = C_p N^{-1/8}`.) -/
theorem iid_init_coupling (m₀ : ℝ) (hm₀ : (d : ℝ) / 2 < m₀) (p : ℕ) :
    ∃ C : ℝ, ∀ (ρ : Torus d → ℝ) (Λ : ℝ), IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ ν : Measure (NegSobolev d m₀), IsProbabilityMeasure ν →
        IsCenteredGaussianWithCov m₀ ν (iidCov (withDensityReal ρ)) →
      ∀ ψ : Fin p → Torus d → ℝ, (∀ a, MemSobolev m₀ (ψ a)) → ∀ N : ℕ, 1 ≤ N →
        ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
          (X : Ω' → Config d N) (η : Ω' → NegSobolev d m₀),
          Measurable X ∧ Measurable η ∧
          law P' X = Measure.pi (fun _ => withDensityReal ρ) ∧ law P' η = ν ∧
          ∫⁻ ω, ‖(WithLp.toLp 2 fun a => iidStat (withDensityReal ρ) (ψ a) (X ω) :
                EuclideanSpace ℝ (Fin p)) -
              WithLp.toLp 2 fun a => NegSobolev.eval (η ω) (ψ a)‖ₑ ∂P' ≤
            ENNReal.ofReal (C * (1 + (⨆ a, sobolevNorm m₀ (ψ a)) ^ ((3 : ℝ) / 2)) *
              (N : ℝ) ^ (-(1 : ℝ) / 8)) := by
  set K : ℝ := 2 * Real.sqrt p + 4 * (2 + Yurinskii.c4 / 2) * (Real.sqrt p * p) + 1 with hK
  refine ⟨2 * K * max (sobCs d m₀) 1, fun ρ Λ hρ hΛ ν hνP hν ψ hψ N hN => ?_⟩
  have hμP := isProb_withDensityReal hρ
  set μ := withDensityReal ρ with hμdef
  have hμac : μ ≪ volume := withDensityReal_ac ρ
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have := negSobolev_secondCountable d m₀
  -- continuous representatives
  choose f hfc hfae hfB hfu using fun a => sobolev_rep m₀ hm₀ (hψ a)
  set S := ⨆ a, sobolevNorm m₀ (ψ a) with hSdef
  have hSa : ∀ a, sobolevNorm m₀ (ψ a) ≤ S := fun a => le_ciSup (f := fun a => sobolevNorm m₀ (ψ a)) (Set.finite_range _).bddAbove a
  have hS0 : 0 ≤ S := Real.iSup_nonneg fun a => Real.sqrt_nonneg _
  have hCs := sobCs_nonneg d m₀
  set B := sobCs d m₀ * S with hBdef
  have hB0 : 0 ≤ B := mul_nonneg hCs hS0
  have hBf : ∀ a x, |f a x| ≤ B := fun a x =>
    (hfB a x).trans (mul_le_mul_of_nonneg_left (hSa a) hCs)
  -- the summand law
  set ξ := xiVec μ N f with hξdef
  have hξc : Continuous ξ := continuous_xiVec μ N f hfc
  have hξm : Measurable ξ := hξc.measurable
  set ρ0 : Measure (EuclideanSpace ℝ (Fin p)) := μ.map ξ with hρ0def
  have hcoord : ∀ c : Fin p, Measurable fun x : EuclideanSpace ℝ (Fin p) => x c := fun c => by fun_prop
  have h0 : ∀ c, ∫ x, x c ∂ρ0 = 0 := by
    intro c
    rw [hρ0def, integral_map hξm.aemeasurable (hcoord c).aestronglyMeasurable]
    exact integral_xiVec_coord N f hfc c
  set R := Real.sqrt p * (2 * B / Real.sqrt N) with hR
  have hR0 : 0 ≤ R := by positivity
  have hξR : ∀ x, ‖ξ x‖ ≤ R := fun x => norm_xiVec_le N f hB0 hBf x
  have h3μ : Integrable (fun x => ‖ξ x‖ ^ 3) μ :=
    Integrable.of_bound (hξm.norm.pow_const 3).aestronglyMeasurable (R ^ 3)
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hξR x) 3)
  have h3 : Integrable (fun x : EuclideanSpace ℝ (Fin p) => ‖x‖ ^ 3) ρ0 := by
    rw [hρ0def]
    exact (integrable_map_measure (measurable_norm.pow_const 3).aestronglyMeasurable
      hξm.aemeasurable).2 h3μ
  have hI3 : ∫ x, ‖x‖ ^ 3 ∂ρ0 ≤ R * (p * B ^ 2 / N) := by
    rw [hρ0def, integral_map hξm.aemeasurable (measurable_norm.pow_const 3).aestronglyMeasurable]
    have h2 := integral_norm_sq_xiVec_le (μ := μ) hN f hfc hBf
    have hi2 : Integrable (fun x => ‖ξ x‖ ^ 2) μ :=
      Integrable.of_bound (hξm.norm.pow_const 2).aestronglyMeasurable (R ^ 2)
        (ae_of_all _ fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          exact pow_le_pow_left₀ (norm_nonneg _) (hξR x) 2)
    calc ∫ x, ‖ξ x‖ ^ 3 ∂μ ≤ ∫ x, R * ‖ξ x‖ ^ 2 ∂μ := by
          refine integral_mono h3μ (hi2.const_mul R) fun x => ?_
          have := hξR x
          nlinarith [norm_nonneg (ξ x), sq_nonneg ‖ξ x‖]
      _ = R * ∫ x, ‖ξ x‖ ^ 2 ∂μ := integral_const_mul _ _
      _ ≤ R * (p * B ^ 2 / N) := mul_le_mul_of_nonneg_left h2 hR0
  have hLb : (N : ℝ) * ∫ x, ‖x‖ ^ 3 ∂ρ0 ≤ 2 * (Real.sqrt p * p) * B ^ 3 / Real.sqrt N := by
    calc (N : ℝ) * ∫ x, ‖x‖ ^ 3 ∂ρ0 ≤ N * (R * (p * B ^ 2 / N)) :=
          mul_le_mul_of_nonneg_left hI3 hNpos.le
      _ = 2 * (Real.sqrt p * p) * B ^ 3 / Real.sqrt N := by
          rw [hR]; field_simp
  -- the law of the statistic
  set T : Config d N → EuclideanSpace ℝ (Fin p) := fun X => ∑ i, ξ (X i) with hTdef
  have hsm : Measurable (fun q : Fin N → EuclideanSpace ℝ (Fin p) => ∑ i, q i) :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  have hξi : Measurable (fun (X : Config d N) (i : Fin N) => ξ (X i)) :=
    Measurable.of_eval fun i => hξm.comp (measurable_pi_apply i)
  have hTm : Measurable T := hsm.comp hξi
  have hlawT : (Measure.pi fun _ : Fin N => μ).map T =
      (Measure.pi fun _ : Fin N => ρ0).map (fun q => ∑ i, q i) := by
    have e : T = (fun q : Fin N → EuclideanSpace ℝ (Fin p) => ∑ i, q i) ∘
        (fun (X : Config d N) (i : Fin N) => ξ (X i)) := rfl
    rw [e, ← Measure.map_map hsm hξi, Measure.pi_map_pi (fun i => hξm.aemeasurable)]
  -- the Gaussian side
  have h2ρ : Integrable (fun x : EuclideanSpace ℝ (Fin p) => ‖x‖ ^ 2) ρ0 :=
    (Yurinskii.integrable_norm_of_pow3 (P := ρ0) (Y := id) measurable_id h3).2
  have hMpsd : (∑ _i : Fin N, Yurinskii.momentMatrix ρ0).PosSemidef :=
    Matrix.posSemidef_sum _ fun _ _ => Yurinskii.momentMatrix_posSemidef _ h2ρ
  have hMe : ∀ a b, (∑ _i : Fin N, Yurinskii.momentMatrix ρ0) a b = iidCov μ (ψ a) (ψ b) := by
    intro a b
    simp only [Matrix.sum_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    have h1 : Yurinskii.momentMatrix ρ0 a b = ∫ x, ξ x a * ξ x b ∂μ := by
      simp only [Yurinskii.momentMatrix, Matrix.of_apply, hρ0def]
      rw [integral_map hξm.aemeasurable (by fun_prop)]
    have h2 := iidCov_congr_rep (μ := μ) (hfc a) (hfc b) (hμac.ae_le (hfae a))
      (hμac.ae_le (hfae b))
    rw [h1, integral_xiVec_mul hN f hfc a b, h2]
    field_simp
  have hevc : ∀ a, Continuous fun F : NegSobolev d m₀ => NegSobolev.eval F (ψ a) := fun a => by
    have : (fun F : NegSobolev d m₀ => NegSobolev.eval F (ψ a)) =
        fun F => inner ℝ (yvec m₀ (ψ a) (hψ a).2) F := funext fun F => eval_eq_inner m₀ _ (hψ a).2 F
    rw [this]; exact continuous_const.inner continuous_id
  set T' : NegSobolev d m₀ → EuclideanSpace ℝ (Fin p) :=
    fun F => WithLp.toLp 2 fun a => NegSobolev.eval F (ψ a) with hT'def
  have hT'c : Continuous T' := (PiLp.continuous_toLp 2 _).comp (continuous_pi hevc)
  have hlawT' : ν.map T' = multivariateGaussian (0 : EuclideanSpace ℝ (Fin p))
      (∑ _i : Fin N, Yurinskii.momentMatrix ρ0) :=
    gauss_law_eval m₀ hm₀ hμac hν ψ hψ _ hMpsd hMe
  -- coupling
  obtain ⟨hr0, hr1, hr4⟩ := rpow_eighth_facts hN
  set r : ℝ := (N : ℝ) ^ (-(1 : ℝ) / 8) with hrdef
  have := standardBorel_config d N
  have := standardBorel_negSobolev d m₀
  have : Nonempty (Config d N) := ⟨fun _ => 0⟩
  have : Nonempty (NegSobolev d m₀) := ⟨0⟩
  obtain ⟨P, hP, hP1, hP2, hcost⟩ := coupling_core (μA := Measure.pi fun _ : Fin N => μ) ν hTm
    hT'c.measurable ρ0 h0 h3 hlawT hlawT' (ε := (B + 1) * r) (η := r) (by positivity) hr0
  have hnum := coupling_numeric hN p (L := (N : ℝ) * ∫ x, ‖x‖ ^ 3 ∂ρ0)
    (c := 2 + Yurinskii.c4 / 2) hB0 (by have := Yurinskii.c4_nonneg; positivity) hLb
  -- almost-sure identification of the statistic
  have hae : ∀ᵐ X ∂(Measure.pi fun _ : Fin N => μ), ∀ a, iidStat μ (ψ a) X = T X a := by
    have hall : ∀ a, ∀ i : Fin N, ∀ᵐ X ∂(Measure.pi fun _ : Fin N => μ),
        ψ a (X i) = Torus.mean (ψ a) + f a (X i) := fun a i =>
      (measurePreserving_eval (fun _ : Fin N => μ) i).quasiMeasurePreserving.ae
        (hμac.ae_le (hfae a))
    have := ae_all_iff.2 fun a => ae_all_iff.2 (hall a)
    filter_upwards [this] with X hX a
    rw [iidStat_eq_of_rep hN (hfc a) (hμac.ae_le (hfae a)) X (hX a)]
    simp [hTdef, hξdef, xiVec_apply, ← Finset.mul_sum]
  have haeP : ∀ᵐ ω ∂P, ∀ a, iidStat μ (ψ a) ω.1 = T ω.1 a := by
    rw [← hP1] at hae
    exact ae_of_ae_map measurable_fst.aemeasurable hae
  refine ⟨Config d N × NegSobolev d m₀, inferInstance, P, hP, Prod.fst, Prod.snd, measurable_fst,
    measurable_snd, hP1, hP2, ?_⟩
  have hcongr : ∫⁻ ω, ‖(WithLp.toLp 2 fun a => iidStat μ (ψ a) ω.1 : EuclideanSpace ℝ (Fin p)) -
      WithLp.toLp 2 fun a => NegSobolev.eval ω.2 (ψ a)‖ₑ ∂P = ∫⁻ ω, ‖T ω.1 - T' ω.2‖ₑ ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [haeP] with ω hω
    congr 2
    ext a
    simp [hω a, hT'def]
  rw [hcongr]
  refine hcost.trans (ENNReal.ofReal_le_ofReal ?_)
  refine hnum.trans ?_
  have hmax : B + 1 ≤ max (sobCs d m₀) 1 * (S + 1) := by
    have h1 : sobCs d m₀ * S ≤ max (sobCs d m₀) 1 * S :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hS0
    have h2 : (1 : ℝ) ≤ max (sobCs d m₀) 1 * 1 := by simp
    nlinarith
  have hS3 : S + 1 ≤ 2 * (1 + S ^ ((3 : ℝ) / 2)) := by
    have hpos : 0 ≤ S ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hS0 _
    rcases le_total S 1 with h | h
    · linarith
    · have : S ^ (1 : ℝ) ≤ S ^ ((3 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le h (by norm_num)
      rw [Real.rpow_one] at this
      linarith
  have hK0 : 0 ≤ K := by
    have := Yurinskii.c4_nonneg
    positivity
  have hmx : 0 ≤ max (sobCs d m₀) 1 := le_trans zero_le_one (le_max_right _ _)
  calc K * (B + 1) * r ≤ K * (max (sobCs d m₀) 1 * (2 * (1 + S ^ ((3 : ℝ) / 2)))) * r := by
        gcongr
        exact hmax.trans (mul_le_mul_of_nonneg_left hS3 hmx |>.trans' (by nlinarith))
    _ = 2 * K * max (sobCs d m₀) 1 * (1 + S ^ ((3 : ℝ) / 2)) * r := by ring

/-! ### Lemma A.38: field-level coupling for i.i.d. data -/

/-- The exponent `𝖼 = (2γ - d)/(4(5γ + d))` of `B:eq:iid-init-field`. -/
def iidFieldExponent (d : ℕ) (γ : ℝ) : ℝ := (2 * γ - d) / (4 * (5 * γ + d))

namespace InitialDataAux

lemma coord_eq_jp_mul_fourierCoeff {m : ℝ} (F : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.coord F k = Lattice.jp k.1 ^ (-m) * NegSobolev.fourierCoeff F k := by
  unfold NegSobolev.fourierCoeff
  rw [← mul_assoc, ← Real.rpow_add (Torus.jp_pos k.1)]
  simp

lemma coord_ofMeasureDiff {m : ℝ} (hm : (d : ℝ) < 2 * m) (μ ν : Measure (Torus d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (k : NonzeroLattice d) :
    NegSobolev.coord (NegSobolev.ofMeasureDiff m μ ν) k =
      Lattice.jp k.1 ^ (-m) * (Torus.measureRealCoeff μ k - Torus.measureRealCoeff ν k) := by
  rw [coord_eq_jp_mul_fourierCoeff, NegSobolev.fourierCoeff_ofMeasureDiff hm μ ν k]

/-- The scaled mode `⟨k⟩^{-γ} e_k`. -/
def scMode (γ : ℝ) (k : NonzeroLattice d) : Torus d → ℝ :=
  fun x => Lattice.jp k.1 ^ (-γ) * Torus.realMode k x

lemma continuous_scMode (γ : ℝ) (k : NonzeroLattice d) : Continuous (scMode γ k) :=
  continuous_const.mul (continuous_realMode k)

lemma abs_scMode_le (γ : ℝ) (k : NonzeroLattice d) (x : Torus d) :
    |scMode γ k x| ≤ Real.sqrt 2 * Lattice.jp k.1 ^ (-γ) := by
  unfold scMode
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _), mul_comm]
  exact mul_le_mul_of_nonneg_right (Torus.abs_realMode_le k x) (Real.rpow_nonneg (Torus.jp_pos _).le _)

lemma isSmooth_scMode (γ : ℝ) (k : NonzeroLattice d) : Torus.IsSmooth (scMode γ k) := by
  have : scMode γ k = trigPoly {k} (fun _ => Lattice.jp k.1 ^ (-γ)) := by
    funext x; simp [scMode, trigPoly]
  rw [this]; exact isSmooth_trigPoly _ _

lemma funRealCoeff_scMode (γ : ℝ) (k l : NonzeroLattice d) :
    Torus.funRealCoeff (scMode γ k) l = if l = k then Lattice.jp k.1 ^ (-γ) else 0 := by
  have : scMode γ k = trigPoly {k} (fun _ => Lattice.jp k.1 ^ (-γ)) := by
    funext x; simp [scMode, trigPoly]
  rw [this, funRealCoeff_trigPoly]
  simp

lemma memSobolev_scMode (m γ : ℝ) (k : NonzeroLattice d) : MemSobolev m (scMode γ k) := by
  refine ⟨(continuous_scMode γ k).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _),
    ?_⟩
  refine summable_of_ne_finset_zero (s := {k}) fun l hl => ?_
  rw [funRealCoeff_scMode]
  simp [show l ≠ k by simpa using hl]

lemma eval_scMode {γ : ℝ} (F : NegSobolev d γ) (k : NonzeroLattice d) :
    NegSobolev.eval F (scMode γ k) = NegSobolev.coord F k := by
  unfold NegSobolev.eval
  rw [tsum_eq_single k]
  · rw [funRealCoeff_scMode]
    simp only [if_true]
    have e : Lattice.jp k.1 ^ γ * Lattice.jp k.1 ^ (-γ) = 1 := by
      rw [← Real.rpow_add (Torus.jp_pos k.1)]; simp
    unfold NegSobolev.fourierCoeff
    linear_combination (NegSobolev.coord F k) * e
  · intro l hl
    rw [funRealCoeff_scMode]; simp [hl]

lemma iidCov_scMode (γ : ℝ) (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (k l : NonzeroLattice d) :
    iidCov μ (scMode γ k) (scMode γ l) =
      Lattice.jp k.1 ^ (-γ) * Lattice.jp l.1 ^ (-γ) *
        iidCov μ (Torus.realMode k) (Torus.realMode l) := by
  have hk := continuous_realMode (d := d) k
  have hl := continuous_realMode (d := d) l
  have ik : Integrable (Torus.realMode k) μ := hk.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have il : Integrable (Torus.realMode l) μ := hl.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have ikl : Integrable (fun x => Torus.realMode k x * Torus.realMode l x) μ :=
    (hk.mul hl).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  unfold iidCov pair scMode
  have e : ∀ x, Lattice.jp k.1 ^ (-γ) * Torus.realMode k x * (Lattice.jp l.1 ^ (-γ) * Torus.realMode l x) =
      (Lattice.jp k.1 ^ (-γ) * Lattice.jp l.1 ^ (-γ)) * (Torus.realMode k x * Torus.realMode l x) :=
    fun x => by ring
  simp_rw [e]
  rw [integral_const_mul, integral_const_mul, integral_const_mul]
  ring

lemma gauss_law_of_cov (m : ℝ) {ν : Measure (NegSobolev d m)}
    [IsProbabilityMeasure ν] (hν : IsCenteredGaussian ν) {p : ℕ}
    (ψ : Fin p → Torus d → ℝ) (hψ : ∀ a, MemSobolev m (ψ a)) (M : Matrix (Fin p) (Fin p) ℝ)
    (hM : M.PosSemidef)
    (hcov : ∀ a b, ∫ F, NegSobolev.eval F (ψ a) * NegSobolev.eval F (ψ b) ∂ν = M a b) :
    ν.map (fun F => (WithLp.toLp 2 fun a => NegSobolev.eval F (ψ a) : EuclideanSpace ℝ (Fin p))) =
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) M := by
  have := negSobolev_secondCountable d m
  have hG := hν.1
  have hmeanν : ∫ z, id z ∂ν = 0 := gaussian_integral_id_eq_zero hν
  set y : Fin p → NegSobolev d m := fun a => yvec m (ψ a) (hψ a).2 with hy
  let A : NegSobolev d m →L[ℝ] EuclideanSpace ℝ (Fin p) :=
    ∑ a : Fin p, (innerSL ℝ (y a)).smulRight (EuclideanSpace.single a (1 : ℝ))
  have hA : ∀ F, A F = (WithLp.toLp 2 fun a => NegSobolev.eval F (ψ a) :
      EuclideanSpace ℝ (Fin p)) := by
    intro F
    ext b
    simp [A, Pi.single_apply, eval_eq_inner m (ψ b) (hψ b).2 F, hy]
  have hfun : (fun F => (WithLp.toLp 2 fun a => NegSobolev.eval F (ψ a) :
      EuclideanSpace ℝ (Fin p))) = fun F => A F := funext fun F => (hA F).symm
  rw [hfun]
  have hGA : IsGaussian (ν.map A) := inferInstance
  have hGM : IsGaussian (multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) M) := inferInstance
  have hmA : (ν.map A)[id] = 0 := by
    show ∫ z, id z ∂(ν.map A) = 0
    rw [integral_map A.continuous.aemeasurable aestronglyMeasurable_id]
    simp only [id]
    rw [A.integral_comp_id_comm IsGaussian.integrable_id]
    have : ∫ F, F ∂ν = 0 := hmeanν
    rw [this, map_zero]
  refine IsGaussian.ext (hmA.trans integral_id_multivariateGaussian'.symm) ?_
  ext u v
  rw [covarianceBilin_multivariateGaussian hM]
  have hmemA : MemLp id 2 (ν.map A) := IsGaussian.memLp_two_id
  rw [covarianceBilin_apply hmemA, hmA, integral_map A.continuous.aemeasurable (by fun_prop)]
  simp only [id, sub_zero]
  have hint : ∀ a b, Integrable (fun F : NegSobolev d m => inner ℝ (y a) F * inner ℝ (y b) F) ν :=
    fun a b => (IsGaussian.memLp_dual ν (innerSL ℝ (y a)) 2 (by simp)).integrable_mul
      (IsGaussian.memLp_dual ν (innerSL ℝ (y b)) 2 (by simp))
  have hcb : ∀ a b, ∫ F, inner ℝ (y a) F * inner ℝ (y b) F ∂ν = M a b := by
    intro a b
    rw [← hcov a b]
    refine integral_congr_ae (Eventually.of_forall fun F => ?_)
    simp only [eval_eq_inner m (ψ a) (hψ a).2, eval_eq_inner m (ψ b) (hψ b).2, hy]
  have hin : ∀ (w : EuclideanSpace ℝ (Fin p)) F, inner ℝ w (A F) = ∑ a, w a * inner ℝ (y a) F := by
    intro w F
    rw [hA F]
    simp [PiLp.inner_apply, mul_comm, hy, eval_eq_inner m _ (hψ _).2]
  simp_rw [hin]
  simp only [Finset.sum_mul_sum]
  have hint2 : ∀ a b, Integrable (fun F : NegSobolev d m =>
      u a * inner ℝ (y a) F * (v b * inner ℝ (y b) F)) ν := fun a b =>
    ((hint a b).const_mul (u a * v b)).congr (Eventually.of_forall fun F => by ring)
  have hL : ∫ F, ∑ a, ∑ b, u a * inner ℝ (y a) F * (v b * inner ℝ (y b) F) ∂ν =
      ∑ a, ∑ b, u a * v b * M a b := by
    rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hint2 a b]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finsetSum _ fun b _ => hint2 a b]
    refine Finset.sum_congr rfl fun b _ => ?_
    have : ∀ F : NegSobolev d m, u a * inner ℝ (y a) F * (v b * inner ℝ (y b) F) =
        (u a * v b) * (inner ℝ (y a) F * inner ℝ (y b) F) := fun F => by ring
    simp_rw [this]
    rw [integral_const_mul, hcb]
  rw [hL]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring




/-- The index of the `j`-th mode of a finite set of modes. -/
def kOf (T : Finset (NonzeroLattice d)) (j : Fin T.card) : NonzeroLattice d :=
  ((T.equivFin).symm j).1

lemma sum_kOf (T : Finset (NonzeroLattice d)) (g : NonzeroLattice d → ℝ) :
    ∑ j : Fin T.card, g (kOf T j) = ∑ k ∈ T, g k := by
  have : ∑ j : Fin T.card, g (kOf T j) = ∑ k : T, g k.1 :=
    Fintype.sum_equiv (T.equivFin).symm _ _ (fun j => rfl)
  rw [this]
  exact Finset.sum_coe_sort T g

/-- The block of scaled modes. -/
def blk (γ : ℝ) (T : Finset (NonzeroLattice d)) : Fin T.card → Torus d → ℝ :=
  fun j => scMode γ (kOf T j)

lemma abs_pair_scMode_le {γ : ℝ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    (k : NonzeroLattice d) : |pair μ (scMode γ k)| ≤ Real.sqrt 2 * Lattice.jp k.1 ^ (-γ) :=
  abs_pair_le (abs_scMode_le γ k)

lemma abs_xiBlk_le {γ : ℝ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ] (N : ℕ)
    (T : Finset (NonzeroLattice d)) (x : Torus d) (j : Fin T.card) :
    |xiVec μ N (blk γ T) x j| ≤ (Real.sqrt N)⁻¹ * (2 * Real.sqrt 2 * Lattice.jp (kOf T j).1 ^ (-γ)) := by
  rw [xiVec_apply, abs_mul, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _)]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (Real.sqrt_nonneg _))
  refine (abs_sub _ _).trans ?_
  have h1 := abs_scMode_le γ (kOf T j) x
  have h2 := abs_pair_scMode_le (γ := γ) (μ := μ) (kOf T j)
  simp only [blk]
  linarith

lemma norm_xiBlk_sq_le {γ : ℝ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {N : ℕ} (hN : 1 ≤ N)
    (T : Finset (NonzeroLattice d)) (x : Torus d) (S : ℝ)
    (hS : ∑ k ∈ T, Lattice.jp k.1 ^ (-(2 * γ)) ≤ S) :
    ‖xiVec μ N (blk γ T) x‖ ^ 2 ≤ 8 * S / N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)]
  calc ∑ j, ‖xiVec μ N (blk γ T) x j‖ ^ 2
      ≤ ∑ j : Fin T.card, 8 * (N : ℝ)⁻¹ * Lattice.jp (kOf T j).1 ^ (-(2 * γ)) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [Real.norm_eq_abs]
        have h := abs_xiBlk_le (γ := γ) (μ := μ) N T x j
        have h0 := abs_nonneg (xiVec μ N (blk γ T) x j)
        calc |xiVec μ N (blk γ T) x j| ^ 2
            ≤ ((Real.sqrt N)⁻¹ * (2 * Real.sqrt 2 * Lattice.jp (kOf T j).1 ^ (-γ))) ^ 2 :=
              pow_le_pow_left₀ h0 h 2
          _ = 8 * (N : ℝ)⁻¹ * Lattice.jp (kOf T j).1 ^ (-(2 * γ)) := by
              rw [mul_pow, inv_pow, Real.sq_sqrt hNpos.le, mul_pow, mul_pow, Real.sq_sqrt (by norm_num),
                Torus.jp_rpow_sq]
              rw [show 2 * (-γ) = -(2 * γ) by ring]
              ring
    _ = 8 * (N : ℝ)⁻¹ * ∑ k ∈ T, Lattice.jp k.1 ^ (-(2 * γ)) := by
        rw [← Finset.mul_sum, sum_kOf T (fun k => Lattice.jp k.1 ^ (-(2 * γ)))]
    _ ≤ 8 * (N : ℝ)⁻¹ * S := mul_le_mul_of_nonneg_left hS (by positivity)
    _ = 8 * S / N := by ring


lemma integral_norm_sq_xiVec_eq {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {N : ℕ}
    (hN : 1 ≤ N) {p : ℕ} (f : Fin p → Torus d → ℝ) (hf : ∀ a, Continuous (f a)) :
    ∫ x, ‖xiVec μ N f x‖ ^ 2 ∂μ = ∑ a : Fin p, (N : ℝ)⁻¹ * iidCov μ (f a) (f a) := by
  have e : ∀ x, ‖xiVec μ N f x‖ ^ 2 = ∑ a, xiVec μ N f x a * xiVec μ N f x a := by
    intro x
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.sum_congr rfl fun a _ => by ring
  simp_rw [e]
  have hi : ∀ a, Integrable (fun x => xiVec μ N f x a * xiVec μ N f x a) μ := by
    intro a
    have hc : Continuous fun x => xiVec μ N f x a := by
      simp only [xiVec_apply]; exact continuous_const.mul ((hf a).sub continuous_const)
    exact integrable_contA μ (hc.mul hc)
  rw [integral_finsetSum _ fun a _ => hi a]
  exact Finset.sum_congr rfl fun a _ => integral_xiVec_mul hN f hf a a

lemma iidCov_scMode_le {γ : ℝ} (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (k : NonzeroLattice d) :
    iidCov μ (scMode γ k) (scMode γ k) ≤ 2 * Lattice.jp k.1 ^ (-(2 * γ)) := by
  have h1 : pair μ (fun x => scMode γ k x * scMode γ k x) ≤ 2 * Lattice.jp k.1 ^ (-(2 * γ)) := by
    unfold pair
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun x => scMode γ k x * scMode γ k x)
      (C := 2 * Lattice.jp k.1 ^ (-(2 * γ)))
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_mul]
        have h := abs_scMode_le γ k x
        have : (Real.sqrt 2 * Lattice.jp k.1 ^ (-γ)) * (Real.sqrt 2 * Lattice.jp k.1 ^ (-γ)) =
            2 * Lattice.jp k.1 ^ (-(2 * γ)) := by
          rw [show -(2 * γ) = (-γ) + (-γ) by ring, Real.rpow_add (Torus.jp_pos k.1)]
          have := Real.mul_self_sqrt (show (0:ℝ) ≤ 2 by norm_num)
          nlinarith [this]
        rw [← this]
        exact mul_le_mul h h (abs_nonneg _)
          (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (Torus.jp_pos _).le _)))
    simpa using (le_abs_self _).trans (by simpa using this)
  unfold iidCov
  nlinarith [sq_nonneg (pair μ (scMode γ k))]

open Yurinskii in
/-- The finite-dimensional block of the field-level coupling. -/
theorem block_coupling {γ : ℝ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    {ν : Measure (NegSobolev d γ)} [IsProbabilityMeasure ν]
    (hν : IsCenteredGaussianWithCov γ ν (iidCov μ)) {N : ℕ} (hN : 1 ≤ N)
    (T : Finset (NonzeroLattice d)) {S : ℝ}
    (hS : ∑ k ∈ T, Lattice.jp k.1 ^ (-(2 * γ)) ≤ S) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ P : Measure (Config d N × NegSobolev d γ), IsProbabilityMeasure P ∧
      P.map Prod.fst = Measure.pi (fun _ : Fin N => μ) ∧ P.map Prod.snd = ν ∧
      ∫⁻ ω, ‖(∑ i, xiVec μ N (blk γ T) (ω.1 i)) -
          (WithLp.toLp 2 fun j : Fin T.card => NegSobolev.coord ω.2 (kOf T j) :
            EuclideanSpace ℝ (Fin T.card))‖ₑ ∂P ≤
        ENNReal.ofReal (2 * ε * Real.sqrt T.card +
          2 / ε ^ 2 * ((2 + c4 / 2) * (2 * S * Real.sqrt (8 * S / N))) + η) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hS0 : 0 ≤ S := (Finset.sum_nonneg fun k _ => Real.rpow_nonneg (Torus.jp_pos _).le _).trans hS
  have := negSobolev_secondCountable d γ
  set p := T.card with hp
  set f := blk γ T with hf
  have hfc : ∀ a, Continuous (f a) := fun a => continuous_scMode γ _
  set ξ := xiVec μ N f with hξdef
  have hξc : Continuous ξ := continuous_xiVec μ N f hfc
  have hξm : Measurable ξ := hξc.measurable
  set ρ0 : Measure (EuclideanSpace ℝ (Fin p)) := μ.map ξ with hρ0def
  have hcoord : ∀ c : Fin p, Measurable fun x : EuclideanSpace ℝ (Fin p) => x c := fun c => by fun_prop
  have h0 : ∀ c, ∫ x, x c ∂ρ0 = 0 := by
    intro c
    rw [hρ0def, integral_map hξm.aemeasurable (hcoord c).aestronglyMeasurable]
    exact integral_xiVec_coord N f hfc c
  set R := Real.sqrt (8 * S / N) with hR
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hξR : ∀ x, ‖ξ x‖ ≤ R := fun x =>
    Real.le_sqrt_of_sq_le (norm_xiBlk_sq_le hN T x S hS)
  have h3μ : Integrable (fun x => ‖ξ x‖ ^ 3) μ :=
    Integrable.of_bound (hξm.norm.pow_const 3).aestronglyMeasurable (R ^ 3)
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hξR x) 3)
  have h3 : Integrable (fun x : EuclideanSpace ℝ (Fin p) => ‖x‖ ^ 3) ρ0 := by
    rw [hρ0def]
    exact (integrable_map_measure (measurable_norm.pow_const 3).aestronglyMeasurable
      hξm.aemeasurable).2 h3μ
  have hI2 : ∫ x, ‖ξ x‖ ^ 2 ∂μ ≤ 2 * S / N := by
    rw [hξdef, integral_norm_sq_xiVec_eq hN f hfc]
    calc ∑ a : Fin p, (N : ℝ)⁻¹ * iidCov μ (f a) (f a)
        ≤ ∑ a : Fin p, (N : ℝ)⁻¹ * (2 * Lattice.jp (kOf T a).1 ^ (-(2 * γ))) :=
          Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (iidCov_scMode_le μ (kOf T a))
            (inv_nonneg.2 hNpos.le)
      _ = (N : ℝ)⁻¹ * (2 * ∑ k ∈ T, Lattice.jp k.1 ^ (-(2 * γ))) := by
          rw [← Finset.mul_sum, ← Finset.mul_sum,
            sum_kOf T (fun k => Lattice.jp k.1 ^ (-(2 * γ)))]
      _ ≤ (N : ℝ)⁻¹ * (2 * S) := by gcongr
      _ = 2 * S / N := by ring
  have hI3 : ∫ x, ‖x‖ ^ 3 ∂ρ0 ≤ R * (2 * S / N) := by
    rw [hρ0def, integral_map hξm.aemeasurable (measurable_norm.pow_const 3).aestronglyMeasurable]
    have hi2 : Integrable (fun x => ‖ξ x‖ ^ 2) μ :=
      Integrable.of_bound (hξm.norm.pow_const 2).aestronglyMeasurable (R ^ 2)
        (ae_of_all _ fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          exact pow_le_pow_left₀ (norm_nonneg _) (hξR x) 2)
    calc ∫ x, ‖ξ x‖ ^ 3 ∂μ ≤ ∫ x, R * ‖ξ x‖ ^ 2 ∂μ := by
          refine integral_mono h3μ (hi2.const_mul R) fun x => ?_
          have := hξR x
          nlinarith [norm_nonneg (ξ x), sq_nonneg ‖ξ x‖]
      _ = R * ∫ x, ‖ξ x‖ ^ 2 ∂μ := integral_const_mul _ _
      _ ≤ R * (2 * S / N) := mul_le_mul_of_nonneg_left hI2 hR0
  have hLb : (N : ℝ) * ∫ x, ‖x‖ ^ 3 ∂ρ0 ≤ 2 * S * R := by
    calc (N : ℝ) * ∫ x, ‖x‖ ^ 3 ∂ρ0 ≤ N * (R * (2 * S / N)) :=
          mul_le_mul_of_nonneg_left hI3 hNpos.le
      _ = 2 * S * R := by field_simp
  -- the law of the statistic
  set T0 : Config d N → EuclideanSpace ℝ (Fin p) := fun X => ∑ i, ξ (X i) with hT0def
  have hsm : Measurable (fun q : Fin N → EuclideanSpace ℝ (Fin p) => ∑ i, q i) :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  have hξi : Measurable (fun (X : Config d N) (i : Fin N) => ξ (X i)) :=
    Measurable.of_eval fun i => hξm.comp (measurable_pi_apply i)
  have hTm : Measurable T0 := hsm.comp hξi
  have hlawT : (Measure.pi fun _ : Fin N => μ).map T0 =
      (Measure.pi fun _ : Fin N => ρ0).map (fun q => ∑ i, q i) := by
    have e : T0 = (fun q : Fin N → EuclideanSpace ℝ (Fin p) => ∑ i, q i) ∘
        (fun (X : Config d N) (i : Fin N) => ξ (X i)) := rfl
    rw [e, ← Measure.map_map hsm hξi, Measure.pi_map_pi (fun i => hξm.aemeasurable)]
  have h2ρ : Integrable (fun x : EuclideanSpace ℝ (Fin p) => ‖x‖ ^ 2) ρ0 :=
    (Yurinskii.integrable_norm_of_pow3 (P := ρ0) (Y := id) measurable_id h3).2
  have hMpsd : (∑ _i : Fin N, Yurinskii.momentMatrix ρ0).PosSemidef :=
    Matrix.posSemidef_sum _ fun _ _ => Yurinskii.momentMatrix_posSemidef _ h2ρ
  have hevc : ∀ a, Continuous fun F : NegSobolev d γ => NegSobolev.eval F (f a) := fun a => by
    have : (fun F : NegSobolev d γ => NegSobolev.eval F (f a)) =
        fun F => inner ℝ (yvec γ (f a) (memSobolev_scMode γ γ (kOf T a)).2) F :=
      funext fun F => eval_eq_inner γ _ (memSobolev_scMode γ γ (kOf T a)).2 F
    rw [this]; exact continuous_const.inner continuous_id
  set T' : NegSobolev d γ → EuclideanSpace ℝ (Fin p) :=
    fun F => WithLp.toLp 2 fun a => NegSobolev.eval F (f a) with hT'def
  have hT'c : Continuous T' := (PiLp.continuous_toLp 2 _).comp (continuous_pi hevc)
  have hcov : ∀ a b, ∫ F, NegSobolev.eval F (f a) * NegSobolev.eval F (f b) ∂ν =
      (∑ _i : Fin N, Yurinskii.momentMatrix ρ0) a b := by
    intro a b
    rw [hν.2 (f a) (f b) (isSmooth_scMode γ (kOf T a)) (isSmooth_scMode γ (kOf T b))]
    simp only [Matrix.sum_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    have h1 : Yurinskii.momentMatrix ρ0 a b = ∫ x, ξ x a * ξ x b ∂μ := by
      simp only [Yurinskii.momentMatrix, Matrix.of_apply, hρ0def]
      rw [integral_map hξm.aemeasurable (by fun_prop)]
    rw [h1, hξdef, integral_xiVec_mul hN f hfc a b]
    field_simp
  have hlawT' : ν.map T' = multivariateGaussian (0 : EuclideanSpace ℝ (Fin p))
      (∑ _i : Fin N, Yurinskii.momentMatrix ρ0) :=
    gauss_law_of_cov γ hν.1 f (fun a => memSobolev_scMode γ γ _) _ hMpsd hcov
  have := standardBorel_config d N
  have := standardBorel_negSobolev d γ
  have : Nonempty (Config d N) := ⟨fun _ => 0⟩
  have : Nonempty (NegSobolev d γ) := ⟨0⟩
  obtain ⟨P, hP, hP1, hP2, hcost⟩ := coupling_core (μA := Measure.pi fun _ : Fin N => μ) ν hTm
    hT'c.measurable ρ0 h0 h3 hlawT hlawT' (ε := ε) (η := η) hε hη
  refine ⟨P, hP, hP1, hP2, ?_⟩
  have hT'eq : ∀ F : NegSobolev d γ, T' F = (WithLp.toLp 2 fun j : Fin p =>
      NegSobolev.coord F (kOf T j) : EuclideanSpace ℝ (Fin p)) := by
    intro F; ext j; simp [hT'def, hf, blk, eval_scMode]
  have hcongr : ∫⁻ ω, ‖(∑ i, ξ (ω.1 i)) - (WithLp.toLp 2 fun j : Fin p =>
      NegSobolev.coord ω.2 (kOf T j) : EuclideanSpace ℝ (Fin p))‖ₑ ∂P =
      ∫⁻ ω, ‖T0 ω.1 - T' ω.2‖ₑ ∂P := by
    refine lintegral_congr fun ω => ?_
    rw [hT'eq]
  refine hcongr.trans_le (hcost.trans (ENNReal.ofReal_le_ofReal ?_))
  have hc4 := c4_nonneg
  have : (2 + c4 / 2) * ((N : ℝ) * ∫ x, ‖x‖ ^ 3 ∂ρ0) ≤ (2 + c4 / 2) * (2 * S * R) :=
    mul_le_mul_of_nonneg_left hLb (by positivity)
  have h2 : 2 / ε ^ 2 * ((2 + c4 / 2) * ((N : ℝ) * ∫ x, ‖x‖ ^ 3 ∂ρ0)) ≤
      2 / ε ^ 2 * ((2 + c4 / 2) * (2 * S * R)) :=
    mul_le_mul_of_nonneg_left this (by positivity)
  simp only [hT0def] at *
  linarith


lemma wA_mem (m : ℝ) (hm : (d : ℝ) < 2 * m) (t : Torus d) :
    Memℓp (fun k : NonzeroLattice d => scMode m k t) 2 := by
  rw [Torus.memℓp_two_iff]
  have hs := summable_jp_rpow (d := d) m hm
  refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_) (hs.mul_left 2)
  unfold scMode
  rw [mul_pow, Torus.jp_rpow_sq, show 2 * (-m) = -(2 * m) by ring]
  have := Torus.abs_realMode_le k t
  have h2 : Torus.realMode k t ^ 2 ≤ 2 := by
    rw [← sq_abs]
    calc |Torus.realMode k t| ^ 2 ≤ Real.sqrt 2 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
      _ = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [Real.rpow_nonneg (Torus.jp_pos k.1).le (-(2 * m))]

/-- The point-evaluation vector `x ↦ (⟨k⟩^{-m} e_k(x))_k`. -/
def wA (m : ℝ) (hm : (d : ℝ) < 2 * m) (t : Torus d) : NegSobolev d m :=
  (⟨fun k => scMode m k t, wA_mem m hm t⟩ : lp (fun _ : NonzeroLattice d => ℝ) 2)

lemma coord_wA (m : ℝ) (hm : (d : ℝ) < 2 * m) (t : Torus d) (k : NonzeroLattice d) :
    NegSobolev.coord (wA m hm t) k = scMode m k t := rfl

lemma continuous_wA (m : ℝ) (hm : (d : ℝ) < 2 * m) : Continuous (wA m hm) := by
  have hs := summable_jp_rpow (d := d) m hm
  refine continuous_iff_continuousAt.mpr fun s => ?_
  set g : Torus d → ℝ := fun t => ∑' k : NonzeroLattice d,
    (scMode m k t - scMode m k s) ^ 2 with hg
  have hcont : ∀ k : NonzeroLattice d, Continuous fun t : Torus d =>
      (scMode m k t - scMode m k s) ^ 2 := fun k =>
    ((continuous_scMode m k).sub continuous_const).pow 2
  have hbnd : ∀ (k : NonzeroLattice d) (t : Torus d),
      ‖(scMode m k t - scMode m k s) ^ 2‖ ≤ 8 * Lattice.jp k.1 ^ (-(2 * m)) := by
    intro k t
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 := abs_scMode_le m k t
    have h2 := abs_scMode_le m k s
    have : |scMode m k t - scMode m k s| ≤ 2 * (Real.sqrt 2 * Lattice.jp k.1 ^ (-m)) := by
      rw [abs_le] at *; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    calc (scMode m k t - scMode m k s) ^ 2 = |scMode m k t - scMode m k s| ^ 2 := (sq_abs _).symm
      _ ≤ (2 * (Real.sqrt 2 * Lattice.jp k.1 ^ (-m))) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
      _ = 8 * Lattice.jp k.1 ^ (-(2 * m)) := by
          rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num), Torus.jp_rpow_sq,
            show 2 * (-m) = -(2 * m) by ring]
          ring
  have hgc : Continuous g :=
    continuous_tsum (f := fun (k : NonzeroLattice d) (t : Torus d) =>
      (scMode m k t - scMode m k s) ^ 2)
      (u := fun k => 8 * Lattice.jp k.1 ^ (-(2 * m))) hcont (hs.mul_left 8) hbnd
  have hnorm : ∀ t, ‖wA m hm t - wA m hm s‖ = Real.sqrt (g t) := by
    intro t
    obtain ⟨h1, h2⟩ := NegSobolev.coord_sq (wA m hm t - wA m hm s)
    rw [← Real.sqrt_sq (norm_nonneg _), h2]
    rfl
  have hg0 : g s = 0 := by simp [hg]
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  simp_rw [hnorm]
  have := (Real.continuous_sqrt.comp hgc).continuousAt (x := s)
  simpa [Function.comp_def, hg0] using this.tendsto

/-- The scaled empirical fluctuation field `√N (μ_N - μ)` in `E_γ`. -/
def fld (γ : ℝ) (N : ℕ) (μ : Measure (Torus d)) (X : Config d N) : NegSobolev d γ :=
  Real.sqrt N • NegSobolev.ofMeasureDiff γ (empirical X) μ

lemma pair_zero_measure (φ : Torus d → ℝ) : pair (0 : Measure (Torus d)) φ = 0 := by
  simp [pair]

lemma coord_fld {γ : ℝ} (hγ : (d : ℝ) < 2 * γ) {N : ℕ} (hN : 1 ≤ N) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] (X : Config d N) (k : NonzeroLattice d) :
    NegSobolev.coord (fld γ N μ X) k =
      (Real.sqrt N)⁻¹ * ∑ i, (scMode γ k (X i) - pair μ (scMode γ k)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hNpos.le
  have hs0 : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  have hemp : IsProbabilityMeasure (empirical X) := empirical_isProbabilityMeasure (by omega) X
  unfold fld
  show Real.sqrt N * NegSobolev.coord (NegSobolev.ofMeasureDiff γ (empirical X) μ) k = _
  rw [coord_ofMeasureDiff hγ]
  have h1 : Torus.measureRealCoeff (empirical X) k = (N : ℝ)⁻¹ * ∑ i, Torus.realMode k (X i) :=
    pair_empirical (by omega) X (Torus.realMode k)
  have h2 : pair μ (scMode γ k) = Lattice.jp k.1 ^ (-γ) * Torus.measureRealCoeff μ k := by
    unfold pair scMode Torus.measureRealCoeff
    rw [integral_const_mul]
  rw [h2]
  simp only [scMode]
  rw [h1]
  have e : ∑ i : Fin N, (Lattice.jp k.1 ^ (-γ) * Torus.realMode k (X i) -
      Lattice.jp k.1 ^ (-γ) * Torus.measureRealCoeff μ k) =
      Lattice.jp k.1 ^ (-γ) * ∑ i, Torus.realMode k (X i) -
        N * (Lattice.jp k.1 ^ (-γ) * Torus.measureRealCoeff μ k) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp
  rw [e]
  generalize Real.sqrt (N : ℝ) = s at hs hs0 ⊢
  rw [← hs]
  field_simp


lemma coord_sub' {m : ℝ} (F G : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.coord (F - G) k = NegSobolev.coord F k - NegSobolev.coord G k := rfl

lemma coord_add' {m : ℝ} (F G : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.coord (F + G) k = NegSobolev.coord F k + NegSobolev.coord G k := rfl

lemma coord_zero' {m : ℝ} (k : NonzeroLattice d) :
    NegSobolev.coord (0 : NegSobolev d m) k = 0 := rfl

lemma coord_smul' {m : ℝ} (c : ℝ) (F : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.coord (c • F) k = c * NegSobolev.coord F k := rfl

lemma coord_sum' {m : ℝ} {ι : Type*} (s : Finset ι) (F : ι → NegSobolev d m)
    (k : NonzeroLattice d) :
    NegSobolev.coord (∑ i ∈ s, F i) k = ∑ i ∈ s, NegSobolev.coord (F i) k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coord_zero']
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, coord_add', ih]

lemma fld_eq {γ : ℝ} (hγ : (d : ℝ) < 2 * γ) {N : ℕ} (hN : 1 ≤ N) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] (X : Config d N) :
    fld γ N μ X = (Real.sqrt N)⁻¹ • ∑ i, wA γ hγ (X i) -
      Real.sqrt N • NegSobolev.ofMeasureDiff γ μ (0 : Measure (Torus d)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hNpos.le
  have hs0 : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  refine Subtype.ext (funext fun k => ?_)
  have h1 : NegSobolev.coord (fld γ N μ X) k = _ := coord_fld hγ hN μ X k
  have h2 : NegSobolev.coord (NegSobolev.ofMeasureDiff γ μ (0 : Measure (Torus d))) k =
      pair μ (scMode γ k) := by
    rw [coord_ofMeasureDiff hγ]
    unfold pair scMode Torus.measureRealCoeff
    rw [integral_const_mul]
    simp
  show NegSobolev.coord (fld γ N μ X) k = NegSobolev.coord ((Real.sqrt N)⁻¹ • ∑ i, wA γ hγ (X i) -
      Real.sqrt N • NegSobolev.ofMeasureDiff γ μ (0 : Measure (Torus d))) k
  rw [h1, coord_sub', coord_smul', coord_smul', coord_sum', h2]
  simp only [coord_wA]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  generalize Real.sqrt (N : ℝ) = s at hs hs0 ⊢
  rw [← hs]
  field_simp

lemma continuous_fld {γ : ℝ} (hγ : (d : ℝ) < 2 * γ) {N : ℕ} (hN : 1 ≤ N) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] : Continuous (fld γ N μ) := by
  have : fld γ N μ = fun X => (Real.sqrt N)⁻¹ • ∑ i, wA γ hγ (X i) -
      Real.sqrt N • NegSobolev.ofMeasureDiff γ μ (0 : Measure (Torus d)) :=
    funext fun X => fld_eq hγ hN μ X
  rw [this]
  have hsum : Continuous fun X : Config d N => ∑ i, wA γ hγ (X i) :=
    continuous_finset_sum _ fun i _ => (continuous_wA γ hγ).comp (continuous_apply i)
  exact (hsum.const_smul (Real.sqrt N)⁻¹).sub continuous_const


/-- Projection onto the modes in `T`. -/
def projT {m : ℝ} (T : Finset (NonzeroLattice d)) (F : NegSobolev d m) : NegSobolev d m :=
  (∑ k ∈ T, (lp.single 2 k (NegSobolev.coord F k) : lp (fun _ : NonzeroLattice d => ℝ) 2) :
    lp (fun _ : NonzeroLattice d => ℝ) 2)

lemma coord_projT {m : ℝ} (T : Finset (NonzeroLattice d)) (F : NegSobolev d m)
    (k : NonzeroLattice d) :
    NegSobolev.coord (projT T F) k = if k ∈ T then NegSobolev.coord F k else 0 := by
  classical
  show ((∑ l ∈ T, (lp.single 2 l (NegSobolev.coord F l) : lp (fun _ : NonzeroLattice d => ℝ) 2) :
    lp (fun _ : NonzeroLattice d => ℝ) 2) : NonzeroLattice d → ℝ) k = _
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.single_apply]
  by_cases hk : k ∈ T
  · simp [hk]
  · simp [hk]

lemma projT_sub {m : ℝ} (T : Finset (NonzeroLattice d)) (F G : NegSobolev d m) :
    projT T (F - G) = projT T F - projT T G := by
  refine Subtype.ext (funext fun k => ?_)
  show NegSobolev.coord (projT T (F - G)) k = NegSobolev.coord (projT T F - projT T G) k
  simp only [coord_projT, coord_sub']
  split_ifs <;> simp

lemma norm_sq_eq_tsum {m : ℝ} (F : NegSobolev d m) :
    ‖F‖ ^ 2 = ∑' k, NegSobolev.coord F k ^ 2 := (NegSobolev.coord_sq F).2

lemma norm_sq_projT {m : ℝ} (T : Finset (NonzeroLattice d)) (F : NegSobolev d m) :
    ‖projT T F‖ ^ 2 = ∑ k ∈ T, NegSobolev.coord F k ^ 2 := by
  rw [norm_sq_eq_tsum]
  rw [tsum_eq_sum (s := T)]
  · exact Finset.sum_congr rfl fun k hk => by rw [coord_projT, if_pos hk]
  · intro k hk; rw [coord_projT, if_neg hk]; simp

lemma norm_sq_sub_projT {m : ℝ} (T : Finset (NonzeroLattice d)) (F : NegSobolev d m) :
    ‖F - projT T F‖ ^ 2 = ∑' k, (if k ∈ T then 0 else NegSobolev.coord F k ^ 2) := by
  rw [norm_sq_eq_tsum]
  refine tsum_congr fun k => ?_
  rw [coord_sub', coord_projT]
  split_ifs <;> simp

lemma norm_projT_eq {m : ℝ} (T : Finset (NonzeroLattice d)) (F : NegSobolev d m) :
    ‖projT T F‖ = ‖(WithLp.toLp 2 fun j : Fin T.card => NegSobolev.coord F (kOf T j) :
      EuclideanSpace ℝ (Fin T.card))‖ := by
  have h1 : ‖projT T F‖ ^ 2 = ‖(WithLp.toLp 2 fun j : Fin T.card => NegSobolev.coord F (kOf T j) :
      EuclideanSpace ℝ (Fin T.card))‖ ^ 2 := by
    rw [norm_sq_projT, EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)]
    simp only [Real.norm_eq_abs, sq_abs]
    rw [sum_kOf T (fun k => NegSobolev.coord F k ^ 2)]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h1

lemma norm_sub_le_blocks {m : ℝ} (T : Finset (NonzeroLattice d)) (v w : NegSobolev d m) :
    ‖v - w‖ ≤ ‖(WithLp.toLp 2 fun j : Fin T.card => NegSobolev.coord v (kOf T j) :
        EuclideanSpace ℝ (Fin T.card)) -
      (WithLp.toLp 2 fun j : Fin T.card => NegSobolev.coord w (kOf T j) :
        EuclideanSpace ℝ (Fin T.card))‖ + ‖v - projT T v‖ + ‖w - projT T w‖ := by
  have h1 : v - w = projT T (v - w) + ((v - projT T v) - (w - projT T w)) := by
    rw [projT_sub]; abel
  have h2 : ‖projT T (v - w)‖ = ‖(WithLp.toLp 2 fun j : Fin T.card => NegSobolev.coord v (kOf T j) :
        EuclideanSpace ℝ (Fin T.card)) -
      (WithLp.toLp 2 fun j : Fin T.card => NegSobolev.coord w (kOf T j) :
        EuclideanSpace ℝ (Fin T.card))‖ := by
    rw [norm_projT_eq]
    congr 1
  calc ‖v - w‖ = ‖projT T (v - w) + ((v - projT T v) - (w - projT T w))‖ := by rw [← h1]
    _ ≤ ‖projT T (v - w)‖ + ‖(v - projT T v) - (w - projT T w)‖ := norm_add_le _ _
    _ ≤ ‖projT T (v - w)‖ + (‖v - projT T v‖ + ‖w - projT T w‖) := by
        gcongr; exact norm_sub_le _ _
    _ = _ := by rw [h2, add_assoc]


lemma abs_coord_le_norm {m : ℝ} (F : NegSobolev d m) (k : NonzeroLattice d) :
    |NegSobolev.coord F k| ≤ ‖F‖ := by
  have := lp.norm_apply_le_norm (p := 2) (by norm_num) (F : lp (fun _ : NonzeroLattice d => ℝ) 2) k
  rw [← Real.norm_eq_abs]
  exact this

lemma continuous_coord {m : ℝ} (k : NonzeroLattice d) :
    Continuous fun F : NegSobolev d m => NegSobolev.coord F k := by
  have h : ∀ F G : NegSobolev d m, |NegSobolev.coord F k - NegSobolev.coord G k| ≤ ‖F - G‖ := by
    intro F G
    have := abs_coord_le_norm (F - G) k
    simpa [coord_sub'] using this
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun F G => ?_).continuous
  simpa [Real.dist_eq, dist_eq_norm] using h F G

lemma norm_projT_le {m : ℝ} (T : Finset (NonzeroLattice d)) (F : NegSobolev d m) :
    ‖projT T F‖ ≤ ‖F‖ := by
  have h : ‖projT T F‖ ^ 2 ≤ ‖F‖ ^ 2 := by
    rw [norm_sq_projT, norm_sq_eq_tsum]
    exact (NegSobolev.coord_sq F).1.sum_le_tsum T (fun k _ => sq_nonneg _)
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

lemma continuous_projT {m : ℝ} (T : Finset (NonzeroLattice d)) :
    Continuous (projT (m := m) T) := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun F G => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm, ← projT_sub]
  simpa using norm_projT_le T (F - G)

lemma lintegral_sq_tail_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {m : ℝ} (F : Ω → NegSobolev d m) (hF : Measurable F)
    (T : Finset (NonzeroLattice d)) {b : NonzeroLattice d → ℝ} (hb : Summable b)
    (hb0 : ∀ k, 0 ≤ b k)
    (hk' : ∀ k, ∫⁻ ω, ENNReal.ofReal (NegSobolev.coord (F ω) k ^ 2) ∂P ≤ ENNReal.ofReal (b k)) :
    ∫⁻ ω, ‖F ω - projT T (F ω)‖ₑ ^ 2 ∂P ≤
      ENNReal.ofReal (∑' k, if k ∈ T then 0 else b k) := by
  have hmeas : ∀ k, Measurable fun ω => NegSobolev.coord (F ω) k :=
    fun k => (continuous_coord k).measurable.comp hF
  have e1 : ∀ ω, ‖F ω - projT T (F ω)‖ₑ ^ 2 =
      ∑' k, ENNReal.ofReal (if k ∈ T then 0 else NegSobolev.coord (F ω) k ^ 2) := by
    intro ω
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), norm_sq_sub_projT]
    rw [ENNReal.ofReal_tsum_of_nonneg]
    · intro k; split_ifs <;> positivity
    · refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) (NegSobolev.coord_sq (F ω)).1
      · split_ifs <;> positivity
      · split_ifs <;> simp [sq_nonneg]
  simp_rw [e1]
  have hm2 : ∀ k, Measurable fun ω => ENNReal.ofReal
      (if k ∈ T then 0 else NegSobolev.coord (F ω) k ^ 2) := by
    intro k
    by_cases hk : k ∈ T
    · simp [hk]
    · simp only [hk, if_false]
      exact ENNReal.measurable_ofReal.comp ((hmeas k).pow_const 2)
  rw [lintegral_tsum fun k => (hm2 k).aemeasurable]
  rw [ENNReal.ofReal_tsum_of_nonneg (fun k => by split_ifs <;> simp [hb0]) ?_]
  · refine ENNReal.tsum_le_tsum fun k => ?_
    by_cases hk : k ∈ T
    · simp [hk]
    · simp only [hk, if_false]
      exact hk' k
  · exact hb.of_nonneg_of_le (fun k => by split_ifs <;> simp [hb0]) (fun k => by split_ifs <;> simp [hb0])


lemma lintegral_tail_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {m : ℝ} (F : Ω → NegSobolev d m) (hF : Measurable F)
    (T : Finset (NonzeroLattice d)) {b : NonzeroLattice d → ℝ} (hb : Summable b)
    (hb0 : ∀ k, 0 ≤ b k)
    (hk : ∀ k, ∫⁻ ω, ENNReal.ofReal (NegSobolev.coord (F ω) k ^ 2) ∂P ≤ ENNReal.ofReal (b k)) :
    ∫⁻ ω, ‖F ω - projT T (F ω)‖ₑ ∂P ≤
      ENNReal.ofReal (Real.sqrt (∑' k, if k ∈ T then 0 else b k)) := by
  have hg : Measurable fun ω => F ω - projT T (F ω) :=
    hF.sub ((continuous_projT T).measurable.comp hF)
  have h2 := lintegral_sq_tail_le P F hF T hb hb0 hk
  have hτ0 : 0 ≤ ∑' k, if k ∈ T then (0:ℝ) else b k :=
    tsum_nonneg fun k => by split_ifs <;> simp [hb0]
  rw [← eLpNorm_one_eq_lintegral_enorm hg.aestronglyMeasurable]
  refine (eLpNorm_le_eLpNorm_of_exponent_le (p := 1) (q := 2) (by norm_num)).trans ?_
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hg.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat]
  have : ∀ ω, ‖F ω - projT T (F ω)‖ₑ ^ (2 : ℝ) = ‖F ω - projT T (F ω)‖ₑ ^ 2 := fun ω => by
    rw [ENNReal.rpow_two]
  simp_rw [this]
  calc (∫⁻ ω, ‖F ω - projT T (F ω)‖ₑ ^ 2 ∂P) ^ (1 / (2 : ℝ)) ≤
      (ENNReal.ofReal (∑' k, if k ∈ T then 0 else b k)) ^ (1 / (2 : ℝ)) :=
        ENNReal.rpow_le_rpow h2 (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt (∑' k, if k ∈ T then 0 else b k)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hτ0 (by norm_num), Real.sqrt_eq_rpow]


lemma iidCov_eq_integral_sq {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {f : Torus d → ℝ}
    (hf : Continuous f) : iidCov μ f f = ∫ x, (f x - pair μ f) ^ 2 ∂μ := by
  have i1 := integrable_contA μ hf
  have i2 : Integrable (fun x => f x * f x) μ := integrable_contA μ (hf.mul hf)
  have e : ∀ x, (f x - pair μ f) ^ 2 = f x * f x - 2 * pair μ f * f x + pair μ f ^ 2 := fun x => by ring
  simp_rw [e]
  have j1 : Integrable (fun x => f x * f x - 2 * pair μ f * f x) μ := i2.sub (i1.const_mul _)
  rw [integral_add j1 (integrable_const _), integral_sub i2 (i1.const_mul _), integral_const_mul]
  simp only [integral_const, probReal_univ, one_smul]
  unfold iidCov pair
  ring

lemma coord_fld_sq_lintegral {γ : ℝ} (hγ : (d : ℝ) < 2 * γ) {N : ℕ} (hN : 1 ≤ N)
    (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (k : NonzeroLattice d) :
    ∫⁻ X, ENNReal.ofReal (NegSobolev.coord (fld γ N μ X) k ^ 2) ∂(Measure.pi fun _ : Fin N => μ) ≤
      ENNReal.ofReal (2 * Lattice.jp k.1 ^ (-(2 * γ))) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set u : Torus d → ℝ := fun x => (Real.sqrt N)⁻¹ * (scMode γ k x - pair μ (scMode γ k)) with hu
  have huc : Continuous u := continuous_const.mul ((continuous_scMode γ k).sub continuous_const)
  have hum : MemLp u 2 μ := huc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hu0 : ∫ x, u x ∂μ = 0 := by
    simp only [hu]
    rw [integral_const_mul, integral_sub (integrable_contA μ (continuous_scMode γ k))
      (integrable_const _)]
    simp [pair]
  have hsum_eq : ∀ X : Config d N, NegSobolev.coord (fld γ N μ X) k = ∑ i, u (X i) := by
    intro X
    rw [coord_fld hγ hN μ X k, Finset.mul_sum]
  have hU : MemLp (fun X : Config d N => ∑ i, u (X i)) 2 (Measure.pi fun _ : Fin N => μ) := by
    refine memLp_finsetSum _ fun i _ => ?_
    exact hum.comp_measurePreserving (measurePreserving_eval (fun _ : Fin N => μ) i)
  simp_rw [hsum_eq]
  rw [← ofReal_integral_eq_lintegral_ofReal hU.integrable_sq
    (Eventually.of_forall fun _ => sq_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [integral_sum_sq_iid μ N hum hu0]
  have h1 : ∫ x, u x ^ 2 ∂μ = (N : ℝ)⁻¹ * iidCov μ (scMode γ k) (scMode γ k) := by
    rw [iidCov_eq_integral_sq (continuous_scMode γ k)]
    simp only [hu, mul_pow, inv_pow]
    rw [integral_const_mul, Real.sq_sqrt hNpos.le]
  rw [h1, ← mul_assoc, mul_inv_cancel₀ hNpos.ne', one_mul]
  exact iidCov_scMode_le μ k

lemma coord_gauss_sq_lintegral {γ : ℝ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    {ν : Measure (NegSobolev d γ)} [IsProbabilityMeasure ν]
    (hν : IsCenteredGaussianWithCov γ ν (iidCov μ)) (k : NonzeroLattice d) :
    ∫⁻ F, ENNReal.ofReal (NegSobolev.coord F k ^ 2) ∂ν ≤
      ENNReal.ofReal (2 * Lattice.jp k.1 ^ (-(2 * γ))) := by
  have := negSobolev_secondCountable d γ
  have hG := hν.1.1
  have hs := (memSobolev_scMode γ γ k).2
  have hint : Integrable (fun F : NegSobolev d γ => NegSobolev.coord F k ^ 2) ν := by
    have h := IsGaussian.memLp_dual ν (innerSL ℝ (yvec γ (scMode γ k) hs)) 2 (by simp)
    refine h.integrable_sq.congr (Eventually.of_forall fun F => ?_)
    simp only [innerSL_apply_apply]
    rw [← eval_eq_inner γ _ hs F, eval_scMode]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ => sq_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have : ∫ F, NegSobolev.coord F k ^ 2 ∂ν = iidCov μ (scMode γ k) (scMode γ k) := by
    rw [← hν.2 _ _ (isSmooth_scMode γ k) (isSmooth_scMode γ k)]
    refine integral_congr_ae (Eventually.of_forall fun F => ?_)
    simp only [eval_scMode, sq]
  rw [this]
  exact iidCov_scMode_le μ k


lemma field_numeric {γ d c κ s : ℝ} (hd : 0 ≤ d) (hγ : d / 2 < γ) {N : ℕ} (hN : 1 ≤ N)
    (hc : c = (2 * γ - d) / (4 * (5 * γ + d))) (hκ : κ = 1 / (5 * γ + d)) (hs : s = γ + d / 2) :
    0 < (N : ℝ) ^ (-c) ∧ (N : ℝ) ^ (-c) ≤ 1 ∧
      ((N : ℝ) ^ κ) ^ s * (Real.sqrt N)⁻¹ ≤ ((N : ℝ) ^ (-c)) ^ 3 ∧
      ((N : ℝ) ^ κ) ^ (-(2 * γ - s) / 2) = (N : ℝ) ^ (-c) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hγ0 : 0 < γ := by linarith
  have h5 : 0 < 5 * γ + d := by linarith
  have hc0 : 0 ≤ c := by
    have : 0 < 2 * γ - d := by linarith
    rw [hc]; positivity
  refine ⟨Real.rpow_pos_of_pos hNpos _, Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith), ?_, ?_⟩
  · rw [← Real.rpow_mul hNpos.le, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le,
      Real.sqrt_eq_rpow, ← Real.rpow_neg hNpos.le, ← Real.rpow_add hNpos]
    refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
    simp only [hc, hκ, hs, Nat.cast_ofNat]
    rw [← sub_nonneg]
    have e : -((2 * γ - d) / (4 * (5 * γ + d))) * 3 - (1 / (5 * γ + d) * (γ + d / 2) + -(1 / 2)) =
        3 * d / (4 * (5 * γ + d)) := by
      field_simp
      ring
    rw [e]
    positivity
  · rw [← Real.rpow_mul hNpos.le]
    congr 1
    simp only [hc, hκ, hs]
    field_simp
    ring


lemma field_assembly {r q Ss S c' N n : ℝ} (hr : 0 < r) (hq : 0 < q) (hSs : 0 ≤ Ss) (hS : 0 ≤ S)
    (hc' : 0 ≤ c') (hN : 0 < N) (hn0 : 0 ≤ n) (hn : n ≤ Ss * q ^ 2)
    (hK : q ^ 2 * (Real.sqrt N)⁻¹ ≤ r ^ 3) :
    2 * (r / q) * Real.sqrt n + 2 / (r / q) ^ 2 * (c' * (2 * S * Real.sqrt (8 * S / N))) + r ≤
      (2 * Real.sqrt Ss + 4 * c' * S * Real.sqrt (8 * S) + 1) * r := by
  have h1 : Real.sqrt n ≤ Real.sqrt Ss * q := by
    calc Real.sqrt n ≤ Real.sqrt (Ss * q ^ 2) := Real.sqrt_le_sqrt hn
      _ = Real.sqrt Ss * q := by rw [Real.sqrt_mul hSs, Real.sqrt_sq hq.le]
  have h2 : 2 * (r / q) * Real.sqrt n ≤ 2 * Real.sqrt Ss * r := by
    calc 2 * (r / q) * Real.sqrt n ≤ 2 * (r / q) * (Real.sqrt Ss * q) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 2 * Real.sqrt Ss * r := by field_simp
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  have h3 : 2 / (r / q) ^ 2 * (c' * (2 * S * Real.sqrt (8 * S / N))) ≤
      4 * c' * S * Real.sqrt (8 * S) * r := by
    have e : Real.sqrt (8 * S / N) = Real.sqrt (8 * S) * (Real.sqrt N)⁻¹ := by
      rw [Real.sqrt_div (by positivity), div_eq_mul_inv]
    rw [e]
    have hpos : 0 ≤ 4 * c' * S * Real.sqrt (8 * S) := by positivity
    calc 2 / (r / q) ^ 2 * (c' * (2 * S * (Real.sqrt (8 * S) * (Real.sqrt N)⁻¹)))
        = 4 * c' * S * Real.sqrt (8 * S) * (q ^ 2 * (Real.sqrt N)⁻¹) / r ^ 2 := by
          field_simp
          ring
      _ ≤ 4 * c' * S * Real.sqrt (8 * S) * r ^ 3 / r ^ 2 := by
          gcongr
      _ = 4 * c' * S * Real.sqrt (8 * S) * r := by field_simp
  linarith


lemma sum_xi_eq {γ : ℝ} (hγ : (d : ℝ) < 2 * γ) {N : ℕ} (hN : 1 ≤ N) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] (T : Finset (NonzeroLattice d)) (X : Config d N) :
    ∑ i, xiVec μ N (blk γ T) (X i) =
      (WithLp.toLp 2 fun j : Fin T.card => NegSobolev.coord (fld γ N μ X) (kOf T j) :
        EuclideanSpace ℝ (Fin T.card)) := by
  ext j
  have : (∑ i, xiVec μ N (blk γ T) (X i)).ofLp j = ∑ i, (xiVec μ N (blk γ T) (X i)).ofLp j := by
    simp [WithLp.ofLp_sum]
  show (∑ i, xiVec μ N (blk γ T) (X i)).ofLp j = _
  rw [this]
  simp only [xiVec_apply, blk]
  rw [coord_fld hγ hN μ X (kOf T j), Finset.mul_sum]

lemma projT_empty {m : ℝ} (F : NegSobolev d m) : projT (∅ : Finset (NonzeroLattice d)) F = 0 := by
  unfold projT
  simp only [Finset.sum_empty]
  rfl

/-- Finiteness of the set of modes of bounded frequency. -/
lemma finite_modes {s K : ℝ} (hs : (d : ℝ) < 2 * (s / 2)) (hK : 0 < K) (hs0 : 0 < s) :
    Set.Finite {k : NonzeroLattice d | Lattice.jp k.1 ≤ K} := by
  have hsum := summable_jp_rpow (d := d) (s / 2) hs
  have h2 : 2 * (s / 2) = s := by ring
  have hev := (tendsto_order.1 hsum.tendsto_cofinite_zero).2 (K ^ (-(2 * (s / 2))))
    (Real.rpow_pos_of_pos hK _)
  rw [Filter.eventually_cofinite] at hev
  refine hev.subset fun k hk => ?_
  simp only [Set.mem_setOf_eq] at hk ⊢
  intro hlt
  have := Real.rpow_le_rpow_of_nonpos (Torus.jp_pos k.1) hk (show -(2 * (s / 2)) ≤ 0 by linarith)
  linarith





lemma half_le_sqrt_log {N : ℕ} (hN2 : 2 ≤ N) : (1 : ℝ) / 2 ≤ Real.sqrt (Real.log N) := by
  apply Real.le_sqrt_of_sq_le
  have h2N : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have := Real.log_le_log (by norm_num) h2N
  have := Real.log_two_gt_d9
  nlinarith

lemma field_final_ineq {x y' A' S r L : ℝ} (hlog : 1 / 2 ≤ L) (hr : 0 < r) (hS : 0 ≤ S)
    (hA : 0 ≤ A') (h : x + y' + y' ≤ A' * r) : x + y' + y' ≤ (2 * A' + 4 * S) * r * L := by
  have hh : 0 ≤ (2 * A' + 4 * S) * r := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hlog hh, mul_nonneg hS hr.le]


end InitialDataAux

open InitialDataAux in
/-- Lemma A.38 `M:B:lem:iid-init-field` (source lines 11581-11587): for `γ > d/2`, every
probability measure `μ°` on `𝕋^d`, and the Gaussian field `η° ∼ ν` of Example A.17 on
`E_γ = H^{-γ}_0`, there is a coupling of `X_N^0 ∼ (μ°)^{⊗N}` and `η°` with
`E ‖√N(μ_N^0 - μ°) - η°‖_{H^{-γ}} ≤ C N^{-𝖼} log^{1/2} N`, `𝖼 = (2γ-d)/(4(5γ+d))`, and
`E‖√N(μ_N^0 - μ°)‖² + E‖η°‖² ≤ C`, with `C = C(d, γ)` (uniform over `μ°`). -/
theorem iid_init_field (γ : ℝ) (hγ : (d : ℝ) / 2 < γ) :
    ∃ C : ℝ, ∀ (μ : Measure (Torus d)), IsProbabilityMeasure μ →
      ∀ ν : Measure (NegSobolev d γ), IsProbabilityMeasure ν →
        IsCenteredGaussianWithCov γ ν (iidCov μ) →
      ∀ N : ℕ, 2 ≤ N →
        ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
          (X : Ω' → Config d N) (η : Ω' → NegSobolev d γ),
          Measurable X ∧ Measurable η ∧
          law P' X = Measure.pi (fun _ => μ) ∧ law P' η = ν ∧
          ∫⁻ ω, ‖Real.sqrt N • NegSobolev.ofMeasureDiff γ (empirical (X ω)) μ - η ω‖ₑ ∂P' ≤
            ENNReal.ofReal (C * (N : ℝ) ^ (-iidFieldExponent d γ) *
              Real.sqrt (Real.log N)) ∧
          ∫⁻ ω, ‖Real.sqrt N • NegSobolev.ofMeasureDiff γ (empirical (X ω)) μ‖ₑ ^ 2 ∂P' +
              ∫⁻ ω, ‖η ω‖ₑ ^ 2 ∂P' ≤ ENNReal.ofReal C := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hγ2 : (d : ℝ) < 2 * γ := by linarith
  set sh : ℝ := (γ + d / 2) / 2 with hsh
  have hsh2 : (d : ℝ) < 2 * sh := by rw [hsh]; linarith
  have hS_s := summable_jp_rpow (d := d) γ hγ2
  have hSs_s := summable_jp_rpow (d := d) sh hsh2
  set S : ℝ := ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * γ)) with hSdef
  set Ss : ℝ := ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * sh)) with hSsdef
  have hS0 : 0 ≤ S := tsum_nonneg fun k => Real.rpow_nonneg (Torus.jp_pos _).le _
  have hSs0 : 0 ≤ Ss := tsum_nonneg fun k => Real.rpow_nonneg (Torus.jp_pos _).le _
  set c' : ℝ := 2 + Yurinskii.c4 / 2 with hc'
  have hc'0 : 0 ≤ c' := by have := Yurinskii.c4_nonneg; positivity
  set A' : ℝ := 2 * Real.sqrt Ss + 4 * c' * S * Real.sqrt (8 * S) + 1 + 2 * Real.sqrt (2 * Ss) with hA'
  have hA'0 : 0 ≤ A' := by positivity
  refine ⟨2 * A' + 4 * S, fun μ hμ ν hνP hν N hN2 => ?_⟩
  have hN : 1 ≤ N := by omega
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have h5 : 0 < 5 * γ + d := by linarith
  obtain ⟨hr0, hr1, hKr, hKt⟩ := field_numeric (c := iidFieldExponent d γ) (κ := 1 / (5 * γ + d))
    (s := γ + d / 2) hd0 hγ hN rfl rfl rfl
  set r : ℝ := (N : ℝ) ^ (-iidFieldExponent d γ) with hrdef
  set K : ℝ := (N : ℝ) ^ (1 / (5 * γ + d)) with hKdef
  have hKpos : 0 < K := Real.rpow_pos_of_pos hNpos _
  set q : ℝ := K ^ sh with hqdef
  have hqpos : 0 < q := Real.rpow_pos_of_pos hKpos _
  have hq2 : q ^ 2 = K ^ (γ + d / 2) := by
    rw [hqdef, ← Real.rpow_natCast, ← Real.rpow_mul hKpos.le, hsh]
    congr 1; push_cast; ring
  -- the finite set of modes
  have hfin := finite_modes (d := d) (s := γ + d / 2) (K := K) (by linarith) hKpos (by linarith)
  set T : Finset (NonzeroLattice d) := hfin.toFinset with hT
  have hTmem : ∀ k, k ∈ T ↔ Lattice.jp k.1 ≤ K := fun k => by simp [hT]
  have h2sh : 2 * sh = γ + d / 2 := by rw [hsh]; ring
  -- (A) cardinality
  have hq2' : q ^ 2 = K ^ (2 * sh) := by
    rw [hqdef, ← Real.rpow_natCast, ← Real.rpow_mul hKpos.le]; congr 1; push_cast; ring
  have hcard : (T.card : ℝ) ≤ Ss * q ^ 2 := by
    have h1 : ∀ k ∈ T, K ^ (-(2 * sh)) ≤ Lattice.jp k.1 ^ (-(2 * sh)) := fun k hk =>
      Real.rpow_le_rpow_of_nonpos (Torus.jp_pos k.1) ((hTmem k).1 hk) (by linarith)
    have h2 : (T.card : ℝ) * K ^ (-(2 * sh)) ≤ Ss := by
      calc (T.card : ℝ) * K ^ (-(2 * sh)) = ∑ k ∈ T, K ^ (-(2 * sh)) := by simp [Finset.sum_const]
        _ ≤ ∑ k ∈ T, Lattice.jp k.1 ^ (-(2 * sh)) := Finset.sum_le_sum h1
        _ ≤ Ss := hSs_s.sum_le_tsum T (fun k _ => Real.rpow_nonneg (Torus.jp_pos _).le _)
    have h3 : K ^ (-(2 * sh)) * K ^ (2 * sh) = 1 := by
      rw [← Real.rpow_add hKpos]; simp
    rw [hq2']
    calc (T.card : ℝ) = T.card * K ^ (-(2 * sh)) * K ^ (2 * sh) := by rw [mul_assoc, h3, mul_one]
      _ ≤ Ss * K ^ (2 * sh) :=
          mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hKpos.le _)
  -- (B) the tail
  have hKr2 : K ^ (-(2 * γ - (γ + d / 2))) = r ^ 2 := by
    rw [← hKt, ← Real.rpow_natCast, ← Real.rpow_mul hKpos.le]; congr 1; push_cast; ring
  set b : NonzeroLattice d → ℝ := fun k => 2 * Lattice.jp k.1 ^ (-(2 * γ)) with hbdef
  have hb_s : Summable b := hS_s.mul_left 2
  have hb0 : ∀ k, 0 ≤ b k := fun k => by
    simp only [hbdef]; exact mul_nonneg (by norm_num) (Real.rpow_nonneg (Torus.jp_pos _).le _)
  have htail : (∑' k : NonzeroLattice d, if k ∈ T then (0 : ℝ) else b k) ≤ 2 * Ss * r ^ 2 := by
    have hg_s : Summable fun k : NonzeroLattice d =>
        2 * K ^ (-(2 * γ - (γ + d / 2))) * Lattice.jp k.1 ^ (-(2 * sh)) := hSs_s.mul_left _
    have hle : ∀ k : NonzeroLattice d, (if k ∈ T then (0 : ℝ) else b k) ≤
        2 * K ^ (-(2 * γ - (γ + d / 2))) * Lattice.jp k.1 ^ (-(2 * sh)) := by
      intro k
      by_cases hk : k ∈ T
      · rw [if_pos hk]
        exact mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hKpos.le _))
          (Real.rpow_nonneg (Torus.jp_pos _).le _)
      · rw [if_neg hk]
        have hKk : K < Lattice.jp k.1 := not_le.1 (fun h => hk ((hTmem k).2 h))
        have e : Lattice.jp k.1 ^ (-(2 * γ)) =
            Lattice.jp k.1 ^ (-(2 * γ - (γ + d / 2))) * Lattice.jp k.1 ^ (-(2 * sh)) := by
          rw [← Real.rpow_add (Torus.jp_pos _), h2sh]; congr 1; ring
        have h1 : Lattice.jp k.1 ^ (-(2 * γ - (γ + d / 2))) ≤ K ^ (-(2 * γ - (γ + d / 2))) :=
          Real.rpow_le_rpow_of_nonpos hKpos hKk.le (by linarith)
        simp only [hbdef]
        rw [e, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by norm_num))
          (Real.rpow_nonneg (Torus.jp_pos _).le _)
    calc (∑' k : NonzeroLattice d, if k ∈ T then (0 : ℝ) else b k)
        ≤ ∑' k : NonzeroLattice d, 2 * K ^ (-(2 * γ - (γ + d / 2))) * Lattice.jp k.1 ^ (-(2 * sh)) :=
          Summable.tsum_le_tsum hle (hb_s.of_nonneg_of_le (fun k => by split_ifs <;> simp [hb0])
            (fun k => by split_ifs <;> simp [hb0])) hg_s
      _ = 2 * K ^ (-(2 * γ - (γ + d / 2))) * Ss := tsum_mul_left
      _ = 2 * Ss * r ^ 2 := by rw [hKr2]; ring
  have hSblk : ∑ k ∈ T, Lattice.jp k.1 ^ (-(2 * γ)) ≤ S :=
    hS_s.sum_le_tsum T (fun k _ => Real.rpow_nonneg (Torus.jp_pos _).le _)
  have hε : 0 < r / q := div_pos hr0 hqpos
  obtain ⟨P, hP, hP1, hP2, hcost⟩ := block_coupling hν hN T hSblk hε hr0
  have hnum := field_assembly (r := r) (q := q) (Ss := Ss) (S := S) (c' := c') (N := N)
    (n := T.card) hr0 hqpos hSs0 hS0 hc'0 hNpos (Nat.cast_nonneg _) hcard (by rw [hq2]; exact hKr)
  have hfc : ∀ a : Fin T.card, Continuous (blk γ T a) := fun a => continuous_scMode γ _
  have hfm : Measurable (fld γ N μ) := (continuous_fld hγ2 hN μ).measurable
  -- tails
  have hτ0 : 0 ≤ ∑' k : NonzeroLattice d, if k ∈ T then (0 : ℝ) else b k :=
    tsum_nonneg fun k => by split_ifs <;> simp [hb0]
  have hsq_tail : Real.sqrt (∑' k : NonzeroLattice d, if k ∈ T then (0 : ℝ) else b k) ≤
      Real.sqrt (2 * Ss) * r := by
    calc Real.sqrt (∑' k : NonzeroLattice d, if k ∈ T then (0 : ℝ) else b k)
        ≤ Real.sqrt (2 * Ss * r ^ 2) := Real.sqrt_le_sqrt htail
      _ = Real.sqrt (2 * Ss) * r := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hr0.le]
  have hBint : ∫⁻ X, ‖fld γ N μ X - projT T (fld γ N μ X)‖ₑ ∂(Measure.pi fun _ : Fin N => μ) ≤
      ENNReal.ofReal (Real.sqrt (∑' k : NonzeroLattice d, if k ∈ T then (0 : ℝ) else b k)) :=
    lintegral_tail_le (Measure.pi fun _ : Fin N => μ) (fld γ N μ) hfm T hb_s hb0
      (coord_fld_sq_lintegral hγ2 hN μ)
  have hCint : ∫⁻ F, ‖F - projT T F‖ₑ ∂ν ≤
      ENNReal.ofReal (Real.sqrt (∑' k : NonzeroLattice d, if k ∈ T then (0 : ℝ) else b k)) :=
    lintegral_tail_le ν (fun F => F) measurable_id T hb_s hb0 (coord_gauss_sq_lintegral hν)
  refine ⟨Config d N × NegSobolev d γ, inferInstance, P, hP, Prod.fst, Prod.snd, measurable_fst,
    measurable_snd, hP1, hP2, ?_, ?_⟩
  · -- the coupling estimate
    set A : Config d N × NegSobolev d γ → ℝ≥0∞ := fun ω =>
      ‖(∑ i, xiVec μ N (blk γ T) (ω.1 i)) -
        (WithLp.toLp 2 fun j : Fin T.card => NegSobolev.coord ω.2 (kOf T j) :
          EuclideanSpace ℝ (Fin T.card))‖ₑ with hAdef
    set B : Config d N × NegSobolev d γ → ℝ≥0∞ := fun ω =>
      ‖fld γ N μ ω.1 - projT T (fld γ N μ ω.1)‖ₑ with hBdef
    set C : Config d N × NegSobolev d γ → ℝ≥0∞ := fun ω => ‖ω.2 - projT T ω.2‖ₑ with hCdef
    have hPT : Continuous fun ω : Config d N × NegSobolev d γ =>
        (WithLp.toLp 2 fun j : Fin T.card => NegSobolev.coord ω.2 (kOf T j) :
          EuclideanSpace ℝ (Fin T.card)) :=
      (PiLp.continuous_toLp 2 _).comp
        (continuous_pi fun j => (continuous_coord (kOf T j)).comp continuous_snd)
    have hAm : Measurable A := by
      refine Measurable.enorm (Measurable.sub ?_ hPT.measurable)
      exact Finset.measurable_sum _ fun i _ =>
        (continuous_xiVec μ N (blk γ T) hfc).measurable.comp
          ((measurable_pi_apply i).comp measurable_fst)
    have hBm : Measurable B :=
      Measurable.enorm ((hfm.comp measurable_fst).sub
        ((continuous_projT T).measurable.comp (hfm.comp measurable_fst)))
    have hpt : ∀ ω : Config d N × NegSobolev d γ, ‖fld γ N μ ω.1 - ω.2‖ₑ ≤ A ω + B ω + C ω := by
      intro ω
      simp only [hAdef, hBdef, hCdef]
      rw [sum_xi_eq hγ2 hN μ T ω.1, ← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ofReal_norm]
      refine (ENNReal.ofReal_le_ofReal (norm_sub_le_blocks T (fld γ N μ ω.1) ω.2)).trans ?_
      exact ENNReal.ofReal_add_le.trans (add_le_add ENNReal.ofReal_add_le le_rfl)
    have hlin : ∫⁻ ω, (A ω + B ω + C ω) ∂P = ∫⁻ ω, A ω ∂P + ∫⁻ ω, B ω ∂P + ∫⁻ ω, C ω ∂P := by
      have e1 : ∫⁻ ω, ((A ω + B ω) + C ω) ∂P = ∫⁻ ω, (A ω + B ω) ∂P + ∫⁻ ω, C ω ∂P :=
        lintegral_add_left (f := fun ω => A ω + B ω) (hAm.add hBm) (fun ω => C ω)
      have e2 : ∫⁻ ω, (A ω + B ω) ∂P = ∫⁻ ω, A ω ∂P + ∫⁻ ω, B ω ∂P :=
        lintegral_add_left (f := A) hAm (fun ω => B ω)
      rw [e1, e2]
    have hBP : ∫⁻ ω, B ω ∂P = ∫⁻ X, ‖fld γ N μ X - projT T (fld γ N μ X)‖ₑ
        ∂(Measure.pi fun _ : Fin N => μ) := by
      have hGm : Measurable fun X : Config d N => ‖fld γ N μ X - projT T (fld γ N μ X)‖ₑ :=
        Measurable.enorm (hfm.sub ((continuous_projT T).measurable.comp hfm))
      rw [← hP1]
      exact (lintegral_map hGm measurable_fst).symm
    have hCP : ∫⁻ ω, C ω ∂P = ∫⁻ F, ‖F - projT T F‖ₑ ∂ν := by
      have hGm : Measurable fun F : NegSobolev d γ => ‖F - projT T F‖ₑ :=
        Measurable.enorm (measurable_id.sub ((continuous_projT T).measurable))
      rw [← hP2]
      exact (lintegral_map hGm measurable_snd).symm
    set x : ℝ := 2 * (r / q) * Real.sqrt T.card +
      2 / (r / q) ^ 2 * (c' * (2 * S * Real.sqrt (8 * S / N))) + r with hxdef
    have hx0 : 0 ≤ x := by
      have : 0 ≤ 2 / (r / q) ^ 2 * (c' * (2 * S * Real.sqrt (8 * S / N))) := by positivity
      have : 0 ≤ 2 * (r / q) * Real.sqrt T.card := by positivity
      linarith
    set y' : ℝ := Real.sqrt (2 * Ss) * r with hy'def
    have hy'0 : 0 ≤ y' := by positivity
    have hAP : ∫⁻ ω, A ω ∂P ≤ ENNReal.ofReal x := hcost
    have hBP' : ∫⁻ ω, B ω ∂P ≤ ENNReal.ofReal y' :=
      hBP ▸ hBint.trans (ENNReal.ofReal_le_ofReal hsq_tail)
    have hCP' : ∫⁻ ω, C ω ∂P ≤ ENNReal.ofReal y' :=
      hCP ▸ hCint.trans (ENNReal.ofReal_le_ofReal hsq_tail)
    have hlog := half_le_sqrt_log hN2
    have hfinal : x + y' + y' ≤ (2 * A' + 4 * S) * r * Real.sqrt (Real.log N) := by
      refine field_final_ineq hlog hr0 hS0 hA'0 ?_
      have h1 : x ≤ (2 * Real.sqrt Ss + 4 * c' * S * Real.sqrt (8 * S) + 1) * r := hnum
      have : A' * r = (2 * Real.sqrt Ss + 4 * c' * S * Real.sqrt (8 * S) + 1) * r + y' + y' := by
        simp only [hA', hy'def]; ring
      linarith
    calc ∫⁻ ω, ‖Real.sqrt N • NegSobolev.ofMeasureDiff γ (empirical (ω.1)) μ - ω.2‖ₑ ∂P
        ≤ ∫⁻ ω, (A ω + B ω + C ω) ∂P := lintegral_mono hpt
      _ = ∫⁻ ω, A ω ∂P + ∫⁻ ω, B ω ∂P + ∫⁻ ω, C ω ∂P := hlin
      _ ≤ ENNReal.ofReal x + ENNReal.ofReal y' + ENNReal.ofReal y' :=
          add_le_add (add_le_add hAP hBP') hCP'
      _ = ENNReal.ofReal (x + y' + y') := by
          rw [← ENNReal.ofReal_add hx0 hy'0, ← ENNReal.ofReal_add (add_nonneg hx0 hy'0) hy'0]
      _ ≤ _ := ENNReal.ofReal_le_ofReal hfinal
  · -- second moments
    have hbS : ∑' k : NonzeroLattice d, b k = 2 * S := tsum_mul_left
    have hX : ∫⁻ ω, ‖fld γ N μ ω.1‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal (2 * S) := by
      have hGm : Measurable fun X : Config d N => ‖fld γ N μ X‖ₑ ^ 2 :=
        hfm.enorm.pow_const 2
      have e : ∫⁻ ω, ‖fld γ N μ ω.1‖ₑ ^ 2 ∂P =
          ∫⁻ X, ‖fld γ N μ X‖ₑ ^ 2 ∂(Measure.pi fun _ : Fin N => μ) := by
        rw [← hP1]; exact (lintegral_map hGm measurable_fst).symm
      rw [e]
      have h := lintegral_sq_tail_le (Measure.pi fun _ : Fin N => μ) (fld γ N μ) hfm
        (∅ : Finset (NonzeroLattice d)) hb_s hb0 (coord_fld_sq_lintegral hγ2 hN μ)
      simp only [projT_empty, sub_zero, Finset.notMem_empty, if_false] at h
      rw [hbS] at h
      exact h
    have hY : ∫⁻ ω, ‖ω.2‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal (2 * S) := by
      have hGm : Measurable fun F : NegSobolev d γ => ‖F‖ₑ ^ 2 := measurable_id.enorm.pow_const 2
      have e : ∫⁻ ω, ‖ω.2‖ₑ ^ 2 ∂P = ∫⁻ F, ‖F‖ₑ ^ 2 ∂ν := by
        rw [← hP2]; exact (lintegral_map hGm measurable_snd).symm
      rw [e]
      have h := lintegral_sq_tail_le ν (fun F => F) measurable_id
        (∅ : Finset (NonzeroLattice d)) hb_s hb0 (coord_gauss_sq_lintegral hν)
      simp only [projT_empty, sub_zero, Finset.notMem_empty, if_false] at h
      rw [hbS] at h
      exact h
    show ∫⁻ ω, ‖fld γ N μ ω.1‖ₑ ^ 2 ∂P + ∫⁻ ω, ‖ω.2‖ₑ ^ 2 ∂P ≤ _
    calc ∫⁻ ω, ‖fld γ N μ ω.1‖ₑ ^ 2 ∂P + ∫⁻ ω, ‖ω.2‖ₑ ^ 2 ∂P
        ≤ ENNReal.ofReal (2 * S) + ENNReal.ofReal (2 * S) := add_le_add hX hY
      _ = ENNReal.ofReal (2 * S + 2 * S) := (ENNReal.ofReal_add (by positivity) (by positivity)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)

/-- Lemma A.38, positivity of the exponent and its limit `1/10` as `γ → ∞` (source lines
11586-11587). -/
theorem iidFieldExponent_pos_tendsto (hd : 1 ≤ d) :
    (∀ γ : ℝ, (d : ℝ) / 2 < γ → 0 < iidFieldExponent d γ) ∧
      Tendsto (iidFieldExponent d) atTop (𝓝 (1 / 10)) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  refine ⟨fun γ hγ => ?_, ?_⟩
  · unfold iidFieldExponent
    have : 0 < 2 * γ - d := by linarith
    have : 0 < 4 * (5 * γ + d) := by nlinarith
    positivity
  · have h1 : Tendsto (fun γ : ℝ => (2 - (d : ℝ) / γ) / (4 * (5 + (d : ℝ) / γ))) atTop
        (𝓝 ((2 - 0) / (4 * (5 + 0)))) := by
      have h0 : Tendsto (fun γ : ℝ => (d : ℝ) / γ) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      exact (tendsto_const_nhds.sub h0).div (tendsto_const_nhds.mul (tendsto_const_nhds.add h0))
        (by norm_num)
    norm_num at h1
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with γ hγ
    unfold iidFieldExponent
    field_simp

/-! ### Example A.39: perturbed lattice data -/

/-- The lattice point `z_j = (j_1/n, …, j_d/n)` of the uniform lattice of spacing `1/n`. -/
def latticePoint (n : ℕ) (j : Fin d → Fin n) : Torus d :=
  fun i => ((((j i : ℕ) : ℝ) / (n : ℝ) : ℝ) : UnitAddCircle)

/-- The perturbed lattice `Y_N = {z + κ⁻¹ a(z) : z ∈ Λ_N}`, `N = n^d`, indexed through
`finFunctionFinEquiv : (Fin d → Fin n) ≃ Fin (n^d)`. -/
def perturbedLattice (n : ℕ) (κ : ℝ) (a : Torus d → Euc d) : Config d (n ^ d) :=
  fun j => latticePoint n (finFunctionFinEquiv.symm j) +
    Torus.mk (κ⁻¹ • a (latticePoint n (finFunctionFinEquiv.symm j)))

namespace InitialDataAux

/-- boundedness of derivatives of periodic lifts, `E`-valued -/
theorem bddAbove_norm_iteratedFDeriv_lift_E {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (j : ℕ) (φ : Torus d → E) (h : ContDiff ℝ j (Torus.lift φ)) :
    BddAbove (Set.range fun x : Euc d => ‖iteratedFDeriv ℝ j (Torus.lift φ) x‖) := by
  have hc : Continuous fun x : Euc d => ‖iteratedFDeriv ℝ j (Torus.lift φ) x‖ :=
    (h.continuous_iteratedFDeriv le_rfl).norm
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : Euc d) d).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨‖M‖, ?_⟩
  rintro _ ⟨x, rfl⟩
  set m : Lattice d := fun i => ⌊x i⌋ with hm
  set y : Euc d := x + Lattice.toEuc (-m) with hy
  have hg : ‖iteratedFDeriv ℝ j (Torus.lift φ) x‖ = ‖iteratedFDeriv ℝ j (Torus.lift φ) y‖ := by
    rw [hy, Torus.iteratedFDeriv_lift_periodic]
  have hyc : ∀ i, 0 ≤ y i ∧ y i < 1 := by
    intro i
    have := Int.floor_le (x i)
    have h2 := Int.lt_floor_add_one (x i)
    simp only [hy, hm, Lattice.toEuc, PiLp.add_apply, Pi.neg_apply, Int.cast_neg]
    constructor <;> linarith
  have hyb : y ∈ Metric.closedBall (0 : Euc d) d := by
    rw [mem_closedBall_zero_iff, EuclideanSpace.norm_eq]
    apply Real.sqrt_le_iff.mpr
    refine ⟨Nat.cast_nonneg d, ?_⟩
    calc ∑ i, ‖y i‖ ^ 2 ≤ ∑ _i : Fin d, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          rw [Real.norm_eq_abs, sq_abs]
          have := hyc i
          nlinarith
      _ = d := by simp
      _ ≤ (d : ℝ) ^ 2 := by
          rcases Nat.eq_zero_or_pos d with h0 | h0
          · simp [h0]
          · have : (1 : ℝ) ≤ d := by exact_mod_cast h0
            nlinarith
  show ‖iteratedFDeriv ℝ j (Torus.lift φ) x‖ ≤ ‖M‖
  rw [hg]
  have := hM y hyb
  rw [norm_norm] at this
  exact this.trans (Real.le_norm_self M)

/-- second-order Taylor bound for a function with Lipschitz derivative -/
lemma taylor2 {g : Euc d → ℝ} (hg : Differentiable ℝ g) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ u v, ‖fderiv ℝ g u - fderiv ℝ g v‖ ≤ M * ‖u - v‖) (x h : Euc d) :
    |g (x + h) - g x - fderiv ℝ g x h| ≤ M * ‖h‖ ^ 2 := by
  set k : Euc d → ℝ := fun y => g y - fderiv ℝ g x y with hk
  have hkd : ∀ y, HasFDerivAt k (fderiv ℝ g y - fderiv ℝ g x) y := fun y =>
    (hg y).hasFDerivAt.sub (fderiv ℝ g x).hasFDerivAt
  have hb : ∀ y ∈ Metric.closedBall x ‖h‖, ‖fderiv ℝ g y - fderiv ℝ g x‖ ≤ M * ‖h‖ := by
    intro y hy
    refine (hM y x).trans ?_
    rw [mem_closedBall_iff_norm] at hy
    exact mul_le_mul_of_nonneg_left hy hM0
  have := (convex_closedBall x ‖h‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := k) (f' := fun y => fderiv ℝ g y - fderiv ℝ g x) (s := Metric.closedBall x ‖h‖)
    (fun y _ => (hkd y).hasFDerivWithinAt) hb (Metric.mem_closedBall_self (norm_nonneg h))
    (show x + h ∈ Metric.closedBall x ‖h‖ by simp)
  simp only [hk] at this
  rw [Real.norm_eq_abs] at this
  have e : g (x + h) - fderiv ℝ g x (x + h) - (g x - fderiv ℝ g x x) = g (x + h) - g x - fderiv ℝ g x h := by
    simp only [map_add]; ring
  rw [e] at this
  calc _ ≤ M * ‖h‖ * ‖x + h - x‖ := this
    _ = M * ‖h‖ ^ 2 := by simp [sq]; ring


/-- the lattice point `j/n` as an element of `ℝ^d` -/
def zhat (n : ℕ) (j : Fin d → Fin n) : Euc d := WithLp.toLp 2 fun i => ((j i : ℕ) : ℝ) / n

/-- the lattice average of a function on `ℝ^d` -/
def latAvg (n : ℕ) (f : Euc d → ℝ) (y : Euc d) : ℝ :=
  ((n ^ d : ℕ) : ℝ)⁻¹ * ∑ j : Fin d → Fin n, f (zhat n j + y)

lemma zhat_shift (n' : ℕ) (i : Fin d) (j : Fin d → Fin (n' + 1)) :
    ∃ m : Lattice d, zhat (n' + 1) (j + Pi.single i 1) =
      zhat (n' + 1) j + ((1 : ℝ) / (n' + 1 : ℕ)) • EuclideanSpace.single i (1 : ℝ) + Lattice.toEuc m := by
  refine ⟨fun l => if l = i ∧ j i = Fin.last n' then -1 else 0, ?_⟩
  ext l
  simp only [zhat, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, Lattice.toEuc,
    Pi.add_apply]
  by_cases hl : l = i
  · subst hl
    simp only [Pi.single_eq_same, ite_true, true_and, smul_eq_mul, mul_one]
    rw [Fin.val_add_one]
    have hn : ((n' + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    by_cases hj : j l = Fin.last n'
    · simp only [hj, ite_true, Fin.val_last]
      push_cast
      field_simp
      ring
    · simp only [hj, ite_false]
      push_cast
      field_simp
      ring
  · simp [hl]


lemma latAvg_shift (n : ℕ) (hn : 1 ≤ n) {f : Euc d → ℝ}
    (hf : ∀ (y : Euc d) (m : Lattice d), f (y + Lattice.toEuc m) = f y) (i : Fin d) (y : Euc d) :
    latAvg n f (y + ((1 : ℝ) / n) • EuclideanSpace.single i (1 : ℝ)) = latAvg n f y := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  unfold latAvg
  congr 1
  let σ : (Fin d → Fin (n' + 1)) ≃ (Fin d → Fin (n' + 1)) := Equiv.addRight (Pi.single i 1)
  rw [← Equiv.sum_comp σ (fun j => f (zhat (n' + 1) j + y))]
  refine Finset.sum_congr rfl fun j _ => ?_
  obtain ⟨m, hm⟩ := zhat_shift n' i j
  show f (zhat (n' + 1) j + (y + ((1 : ℝ) / ((n' + 1 : ℕ) : ℝ)) • EuclideanSpace.single i (1 : ℝ))) =
    f (zhat (n' + 1) (j + Pi.single i 1) + y)
  rw [hm]
  have : zhat (n' + 1) j + ((1 : ℝ) / ((n' + 1 : ℕ) : ℝ)) • EuclideanSpace.single i (1 : ℝ) +
      Lattice.toEuc m + y = (zhat (n' + 1) j + (y + ((1 : ℝ) / ((n' + 1 : ℕ) : ℝ)) •
        EuclideanSpace.single i (1 : ℝ))) + Lattice.toEuc m := by abel
  rw [this, hf]


lemma exists_box_rep (n : ℕ) (hn : 1 ≤ n) {f : Euc d → ℝ}
    (hf : ∀ (y : Euc d) (m : Lattice d), f (y + Lattice.toEuc m) = f y) (y : Euc d) :
    ∃ y' : Euc d, latAvg n f y' = latAvg n f y ∧ ∀ i, |y' i| ≤ 1 / (2 * n) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  let P : AddSubgroup (Euc d) :=
    { carrier := {v | ∀ y, latAvg n f (y + v) = latAvg n f y}
      zero_mem' := fun y => by simp
      add_mem' := fun {v w} hv hw y => by
        show latAvg n f (y + (v + w)) = latAvg n f y
        rw [← add_assoc]; exact (hw _).trans (hv y)
      neg_mem' := fun {v} hv y => by
        show latAvg n f (y + -v) = latAvg n f y
        have := hv (y + -v)
        simp only [neg_add_cancel_right] at this
        exact this.symm }
  have hPi : ∀ i, ((1 : ℝ) / n) • EuclideanSpace.single i (1 : ℝ) ∈ P :=
    fun i y => latAvg_shift n hn hf i y
  set c : Fin d → ℤ := fun i => ⌊n * y i + 1 / 2⌋ with hc
  have hmem : ∑ i, (c i) • (((1 : ℝ) / n) • EuclideanSpace.single i (1 : ℝ)) ∈ P :=
    AddSubgroup.sum_mem P fun i _ => P.zsmul_mem (hPi i) (c i)
  refine ⟨y + -∑ i, (c i) • (((1 : ℝ) / n) • EuclideanSpace.single i (1 : ℝ)), ?_, ?_⟩
  · have := (P.neg_mem hmem) y
    exact this
  · intro l
    have h1 : (∑ i, (c i) • (((1 : ℝ) / n) • EuclideanSpace.single i (1 : ℝ))) l = (c l : ℝ) / n := by
      simp only [PiLp.smul_apply, PiLp.single_apply, WithLp.ofLp_sum, Finset.sum_apply,
        smul_eq_mul, zsmul_eq_mul]
      rw [Finset.sum_eq_single l]
      · simp; ring
      · intro b _ hb; simp [Ne.symm hb]
      · simp
    have h2 : (y + -∑ i, (c i) • (((1 : ℝ) / n) • EuclideanSpace.single i (1 : ℝ))) l =
        y l - (c l : ℝ) / n := by
      simp only [PiLp.add_apply, PiLp.neg_apply, h1]; ring
    rw [h2]
    have h3 := Int.floor_le (n * y l + 1 / 2)
    have h4 := Int.lt_floor_add_one (n * y l + 1 / 2)
    have hcl : (c l : ℝ) = ⌊n * y l + 1 / 2⌋ := rfl
    rw [← hcl] at h3 h4
    have he : (n : ℝ) * (y l - (c l : ℝ) / n) = n * y l - c l := by field_simp
    rw [abs_le]
    have key : -(1/2 : ℝ) ≤ n * (y l - (c l : ℝ) / n) ∧ n * (y l - (c l : ℝ) / n) ≤ 1 / 2 := by
      rw [he]; constructor <;> linarith
    have e2 : 1 / (2 * (n : ℝ)) = (1 / 2) / n := by field_simp
    rw [e2]
    constructor
    · calc -(1 / 2 / (n : ℝ)) = (-(1 / 2)) / n := by ring
        _ ≤ _ := by rw [div_le_iff₀ hnpos]; nlinarith [key.1]
    · rw [le_div_iff₀ hnpos]; nlinarith [key.2]


lemma eq_sum_single (v : Euc d) : v = ∑ i, v i • EuclideanSpace.single i (1 : ℝ) := by
  ext l
  simp [Finset.sum_apply, Pi.single_apply]

lemma norm_le_sum_abs (v : Euc d) : ‖v‖ ≤ ∑ i, |v i| := by
  conv_lhs => rw [eq_sum_single v]
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum fun i _ => ?_
  rw [norm_smul, PiLp.norm_single]
  simp

lemma norm_le_card_mul (v : Euc d) {b : ℝ} (h : ∀ i, |v i| ≤ b) : ‖v‖ ≤ d * b := by
  refine (norm_le_sum_abs v).trans ?_
  calc ∑ i, |v i| ≤ ∑ _i : Fin d, b := Finset.sum_le_sum fun i _ => h i
    _ = d * b := by simp

lemma card_lat (n : ℕ) : ((Finset.univ : Finset (Fin d → Fin n)).card : ℝ) = ((n ^ d : ℕ) : ℝ) := by
  simp

lemma latAvg_lip (n : ℕ) (hn : 1 ≤ n) {g : Euc d → ℝ}
    (hper : ∀ (y : Euc d) (m : Lattice d), g (y + Lattice.toEuc m) = g y) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ u v, |g u - g v| ≤ L * ‖u - v‖) (y : Euc d) :
    |latAvg n g y - latAvg n g 0| ≤ L * (d / (2 * n)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hN : (0 : ℝ) < ((n ^ d : ℕ) : ℝ) := by positivity
  obtain ⟨y', hy', hbox⟩ := exists_box_rep n hn hper y
  rw [← hy']
  have hy'n : ‖y'‖ ≤ d / (2 * n) := by
    have := norm_le_card_mul y' hbox
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  unfold latAvg
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos (inv_pos.mpr hN)]
  have hs : |∑ j : Fin d → Fin n, (g (zhat n j + y') - g (zhat n j + 0))| ≤
      ∑ j : Fin d → Fin n, L * ‖y'‖ := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    refine (hL _ _).trans ?_
    simp
  have hc : ∑ j : Fin d → Fin n, L * ‖y'‖ = ((n ^ d : ℕ) : ℝ) * (L * ‖y'‖) := by
    simp
  rw [hc] at hs
  calc ((n ^ d : ℕ) : ℝ)⁻¹ * |∑ j : Fin d → Fin n, (g (zhat n j + y') - g (zhat n j + 0))|
      ≤ ((n ^ d : ℕ) : ℝ)⁻¹ * (((n ^ d : ℕ) : ℝ) * (L * ‖y'‖)) :=
        mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hN.le)
    _ = L * ‖y'‖ := by field_simp
    _ ≤ L * (d / (2 * n)) := mul_le_mul_of_nonneg_left hy'n hL0


lemma latAvg_partial_small (n : ℕ) (hn : 1 ≤ n) {g : Euc d → ℝ} (hdiff : Differentiable ℝ g)
    {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ u v, ‖fderiv ℝ g u - fderiv ℝ g v‖ ≤ M * ‖u - v‖)
    (hper : ∀ (y : Euc d) (m : Lattice d), g (y + Lattice.toEuc m) = g y)
    (w : Euc d) (i : Fin d) :
    |((n ^ d : ℕ) : ℝ)⁻¹ * ∑ j : Fin d → Fin n, fderiv ℝ g (zhat n j + w) (EuclideanSpace.single i 1)|
      ≤ M / n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hN : (0 : ℝ) < ((n ^ d : ℕ) : ℝ) := by positivity
  set e : Euc d := EuclideanSpace.single i (1 : ℝ) with he
  set D : ℝ → ℝ := fun t => ((n ^ d : ℕ) : ℝ)⁻¹ *
    ∑ j : Fin d → Fin n, fderiv ℝ g (zhat n j + (w + t • e)) e with hD
  set φ : ℝ → ℝ := fun t => latAvg n g (w + t • e) with hφ
  have hder : ∀ t, HasDerivAt φ (D t) t := by
    intro t
    have h1 : ∀ j : Fin d → Fin n, HasDerivAt (fun t : ℝ => g (zhat n j + (w + t • e)))
        (fderiv ℝ g (zhat n j + (w + t • e)) e) t := by
      intro j
      have h2 : HasDerivAt (fun t : ℝ => zhat n j + (w + t • e)) e t := by
        have := (((hasDerivAt_id t).smul_const e).const_add w).const_add (zhat n j)
        simpa using this
      exact (hdiff (zhat n j + (w + t • e))).hasFDerivAt.comp_hasDerivAt t h2
    have h3 := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin d → Fin n))) (fun j _ => h1 j)
    exact h3.const_mul _
  have hper1 : φ (1 / n) = φ 0 := by
    simp only [hφ, zero_smul, add_zero]
    have := latAvg_shift n hn hper i w
    rw [he]
    have e2 : (1 / (n : ℝ)) • EuclideanSpace.single i (1 : ℝ) = (1 / (n : ℝ)) • EuclideanSpace.single i (1 : ℝ) := rfl
    simpa using this
  obtain ⟨t₀, ht₀, hDt⟩ := exists_hasDerivAt_eq_zero (f := φ) (f' := D)
    (by positivity : (0 : ℝ) < 1 / n)
    (fun t _ => (hder t).continuousAt.continuousWithinAt) hper1.symm (fun t _ => hder t)
  have hD0 : D 0 = ((n ^ d : ℕ) : ℝ)⁻¹ * ∑ j : Fin d → Fin n, fderiv ℝ g (zhat n j + w) e := by
    simp [hD]
  rw [← hD0]
  have : D 0 = D 0 - D t₀ := by rw [hDt]; ring
  rw [this]
  have hdiffs : |D 0 - D t₀| ≤ ((n ^ d : ℕ) : ℝ)⁻¹ * ∑ j : Fin d → Fin n, (M * t₀) := by
    simp only [hD, ← mul_sub, ← Finset.sum_sub_distrib]
    rw [abs_mul, abs_of_pos (inv_pos.mpr hN)]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hN.le)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [← sub_apply, ← Real.norm_eq_abs]
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [he, PiLp.norm_single, norm_one, mul_one]
    refine (hM _ _).trans ?_
    have : zhat n j + (w + (0 : ℝ) • e) - (zhat n j + (w + t₀ • e)) = -(t₀ • e) := by
      simp
    rw [this, norm_neg, norm_smul, he, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs,
      abs_of_pos ht₀.1]
  refine hdiffs.trans ?_
  have hc : ((n ^ d : ℕ) : ℝ)⁻¹ * ∑ j : Fin d → Fin n, (M * t₀) = M * t₀ := by
    simp; field_simp
  rw [hc]
  calc M * t₀ ≤ M * (1 / n) := mul_le_mul_of_nonneg_left ht₀.2.le hM0
    _ = M / n := by ring


lemma latAvg_C2 (n : ℕ) (hn : 1 ≤ n) {g : Euc d → ℝ} (hdiff : Differentiable ℝ g)
    {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ u v, ‖fderiv ℝ g u - fderiv ℝ g v‖ ≤ M * ‖u - v‖)
    (hper : ∀ (y : Euc d) (m : Lattice d), g (y + Lattice.toEuc m) = g y) (y : Euc d) :
    |latAvg n g y - latAvg n g 0| ≤ (d * M / n) * (d / (2 * n)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hN : (0 : ℝ) < ((n ^ d : ℕ) : ℝ) := by positivity
  obtain ⟨y', hy', hbox⟩ := exists_box_rep n hn hper y
  rw [← hy']
  have hy'n : ‖y'‖ ≤ d / (2 * n) := by
    have := norm_le_card_mul y' hbox
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  -- derivative of the lattice average
  let DG : Euc d → (Euc d →L[ℝ] ℝ) := fun w =>
    ((n ^ d : ℕ) : ℝ)⁻¹ • ∑ j : Fin d → Fin n, fderiv ℝ g (zhat n j + w)
  have hDG : ∀ w, HasFDerivAt (latAvg n g) (DG w) w := by
    intro w
    have h1 : ∀ j : Fin d → Fin n, HasFDerivAt (fun w => g (zhat n j + w))
        (fderiv ℝ g (zhat n j + w)) w := by
      intro j
      have := (hdiff (zhat n j + w)).hasFDerivAt.comp w ((hasFDerivAt_id w).const_add (zhat n j))
      rw [ContinuousLinearMap.comp_id] at this
      exact this
    have h3 := HasFDerivAt.fun_sum (u := (Finset.univ : Finset (Fin d → Fin n))) (fun j _ => h1 j)
    exact h3.const_mul _ |>.congr_fderiv (by ext v; simp [DG])
  have hDGb : ∀ w, ‖DG w‖ ≤ d * M / n := by
    intro w
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    have hv : DG w v = ∑ i, v i * (((n ^ d : ℕ) : ℝ)⁻¹ *
        ∑ j : Fin d → Fin n, fderiv ℝ g (zhat n j + w) (EuclideanSpace.single i 1)) := by
      conv_lhs => rw [eq_sum_single v]
      simp only [map_sum, map_smul, DG, smul_apply, smul_eq_mul,
        sum_apply, Finset.mul_sum]
    rw [hv, Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |v i * (((n ^ d : ℕ) : ℝ)⁻¹ *
          ∑ j : Fin d → Fin n, fderiv ℝ g (zhat n j + w) (EuclideanSpace.single i 1))|
        ≤ ∑ _i : Fin d, ‖v‖ * (M / n) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul]
          exact mul_le_mul (by simpa using PiLp.norm_apply_le v i)
            (latAvg_partial_small n hn hdiff hM0 hM hper w i) (abs_nonneg _) (norm_nonneg _)
      _ = d * M / n * ‖v‖ := by simp; ring
  have hmv := (convex_univ : Convex ℝ (Set.univ : Set (Euc d))).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := latAvg n g) (f' := DG) (fun w _ => (hDG w).hasFDerivWithinAt) (fun w _ => hDGb w)
    (Set.mem_univ 0) (Set.mem_univ y')
  rw [Real.norm_eq_abs] at hmv
  refine hmv.trans ?_
  rw [sub_zero]
  exact mul_le_mul_of_nonneg_left hy'n (by positivity)


lemma mk_add' (x y : Euc d) : Torus.mk (x + y) = Torus.mk x + Torus.mk y := by
  funext i
  simp [Torus.mk]

lemma mk_zero' : Torus.mk (0 : Euc d) = 0 := by
  funext i
  simp [Torus.mk]

lemma latticePoint_eq (n : ℕ) (j : Fin d → Fin n) : latticePoint n j = Torus.mk (zhat n j) := rfl

lemma isOpenQuotientMap_mk' : IsOpenQuotientMap (Torus.mk : Euc d → Torus d) := by
  have h1 : IsOpenQuotientMap
      (Pi.map (fun _ : Fin d => ((↑) : ℝ → UnitAddCircle))) :=
    IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk
  have h2 := h1.comp (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).isOpenQuotientMap
  exact h2

lemma continuous_of_lift' {E : Type*} [TopologicalSpace E] {f : Torus d → E}
    (h : Continuous (Torus.lift f)) : Continuous f :=
  isOpenQuotientMap_mk'.isQuotientMap.continuous_iff.2 h

lemma torus_quad (n : ℕ) (hn : 1 ≤ n) {f : Torus d → ℝ} (hf : Continuous f) {ε : ℝ}
    (h : ∀ y : Euc d, |latAvg n (Torus.lift f) y - latAvg n (Torus.lift f) 0| ≤ ε) :
    |((n ^ d : ℕ) : ℝ)⁻¹ * ∑ j : Fin d → Fin n, f (latticePoint n j) - ∫ x, f x| ≤ ε := by
  have hN : (0 : ℝ) < ((n ^ d : ℕ) : ℝ) := by positivity
  set F : Torus d → ℝ := fun x => ((n ^ d : ℕ) : ℝ)⁻¹ * ∑ j : Fin d → Fin n, f (x + latticePoint n j)
    with hF
  have hFc : Continuous F := by
    refine continuous_const.mul (continuous_finsetSum _ fun j _ => ?_)
    exact hf.comp (continuous_id.add continuous_const)
  have hFmk : ∀ y : Euc d, F (Torus.mk y) = latAvg n (Torus.lift f) y := by
    intro y
    simp only [hF, latAvg, Torus.lift, Function.comp, latticePoint_eq, ← mk_add']
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [add_comm]
  have hint : ∫ x, F x = ∫ x, f x := by
    simp only [hF]
    rw [integral_const_mul, integral_finsetSum]
    · have : ∀ j : Fin d → Fin n, ∫ x, f (x + latticePoint n j) = ∫ x, f x :=
        fun j => integral_add_right_eq_self f (latticePoint n j)
      simp only [this, Finset.sum_const, Finset.card_univ]
      simp
      field_simp
    · intro j _
      exact (hf.comp (continuous_id.add continuous_const)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hF0 : F 0 = ((n ^ d : ℕ) : ℝ)⁻¹ * ∑ j : Fin d → Fin n, f (latticePoint n j) := by
    simp [hF]
  rw [← hF0, ← hint]
  have hFi : Integrable F := hFc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have : F 0 - ∫ x, F x = ∫ x, (F 0 - F x) := by
    rw [integral_sub (integrable_const _) hFi]
    simp
  rw [this]
  have := norm_integral_le_of_norm_le_const (μ := (volume : Measure (Torus d))) (f := fun x => F 0 - F x)
    (C := ε) (Filter.Eventually.of_forall fun x => ?_)
  · simpa using this
  · rw [Real.norm_eq_abs]
    have h1 := h (Torus.rep x)
    rw [← hFmk, ← hFmk] at h1
    rw [Torus.mk_rep, mk_zero'] at h1
    rw [abs_sub_comm]
    exact h1


lemma lip_of_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : Euc d → E}
    (hg : Differentiable ℝ g) {B : ℝ} (hB : ∀ x, ‖fderiv ℝ g x‖ ≤ B) (u v : Euc d) :
    ‖g u - g v‖ ≤ B * ‖u - v‖ :=
  (convex_univ : Convex ℝ (Set.univ : Set (Euc d))).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => (hg x)) (fun x _ => hB x) (Set.mem_univ v) (Set.mem_univ u)

lemma fderiv_lip {g : Euc d → ℝ} (hg : ContDiff ℝ 2 g) {M : ℝ}
    (hM : ∀ x, ‖iteratedFDeriv ℝ 2 g x‖ ≤ M) (u v : Euc d) :
    ‖fderiv ℝ g u - fderiv ℝ g v‖ ≤ M * ‖u - v‖ := by
  have hd : Differentiable ℝ (fderiv ℝ g) :=
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero)
  refine lip_of_fderiv hd (fun x => ?_) u v
  have := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := g) (x := x) (n := 1)
  rw [norm_iteratedFDeriv_one] at this
  rw [this]; exact hM x

lemma le_sup_E {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (j : ℕ) (φ : Torus d → E)
    (h : ContDiff ℝ j (Torus.lift φ)) (x : Euc d) :
    ‖iteratedFDeriv ℝ j (Torus.lift φ) x‖ ≤ ⨆ x : Euc d, ‖iteratedFDeriv ℝ j (Torus.lift φ) x‖ :=
  le_ciSup (bddAbove_norm_iteratedFDeriv_lift_E j φ h) x

lemma le_cbNorm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (k j : ℕ) (hj : j ≤ k)
    (φ : Torus d → E) (hφ : ContDiff ℝ k (Torus.lift φ)) (x : Euc d) :
    ‖iteratedFDeriv ℝ j (Torus.lift φ) x‖ ≤ Torus.cbNorm k φ := by
  have hj' : ContDiff ℝ j (Torus.lift φ) := hφ.of_le (by exact_mod_cast hj)
  refine (le_sup_E j φ hj' x).trans ?_
  unfold Torus.cbNorm
  refine Finset.single_le_sum (f := fun i => ⨆ x : Euc d, ‖iteratedFDeriv ℝ i (Torus.lift φ) x‖)
    (fun i _ => Real.iSup_nonneg fun _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))

lemma cbNorm_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ)
    (φ : Torus d → E) : 0 ≤ Torus.cbNorm k φ :=
  Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _


/-- the scalar `∇ψ · a` on the torus -/
def hT (ψ : Torus d → ℝ) (a : Torus d → Euc d) (x : Torus d) : ℝ :=
  ∑ i, Torus.partialDeriv i ψ x * a x i

lemma lift_hT (ψ : Torus d → ℝ) (hψ : Torus.IsCk 1 ψ) (a : Torus d → Euc d) (u : Euc d) :
    Torus.lift (hT ψ a) u = fderiv ℝ (Torus.lift ψ) u (Torus.lift a u) := by
  have e1 : Torus.lift (hT ψ a) u = hT ψ a (Torus.mk u) := rfl
  have e2 : Torus.lift a u = a (Torus.mk u) := rfl
  rw [e1, e2]
  simp only [hT, PDE.partialDeriv_mk _ ψ hψ]
  conv_rhs => rw [eq_sum_single (a (Torus.mk u))]
  simp only [map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

lemma continuous_comp_apply (a : Torus d → Euc d) (ha : Continuous a) (i : Fin d) :
    Continuous fun x => a x i :=
  (EuclideanSpace.proj i).continuous.comp ha

lemma isCk_apply (a : Torus d → Euc d) (ha : Torus.IsCk 1 a) (i : Fin d) :
    Torus.IsCk 1 (fun x => a x i) :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp ha

lemma partialDeriv_apply_eq_div (a : Torus d → Euc d) (ha : Torus.IsCk 1 a) (x : Torus d) :
    Torus.div a x = ∑ i, Torus.partialDeriv i (fun y => a y i) x := by
  unfold Torus.div Torus.partialDeriv
  refine Finset.sum_congr rfl fun i _ => ?_
  have hda : DifferentiableAt ℝ (Torus.lift a) (Torus.rep x) :=
    (ha.differentiable one_ne_zero) _
  have : fderiv ℝ (Torus.lift fun y => a y i) (Torus.rep x) =
      (EuclideanSpace.proj (𝕜 := ℝ) i).comp (fderiv ℝ (Torus.lift a) (Torus.rep x)) :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp _ hda.hasFDerivAt).fderiv
  rw [this]
  rfl

lemma integral_hT (ψ : Torus d → ℝ) (hψ : Torus.IsCk 1 ψ) (a : Torus d → Euc d)
    (ha : Torus.IsCk 1 a) :
    ∫ x, hT ψ a x = -∫ x, ψ x * Torus.div a x := by
  have cψ : Continuous ψ := continuous_of_lift' hψ.continuous
  have ca : Continuous a := continuous_of_lift' ha.continuous
  have hint1 : ∀ i, Integrable fun x => Torus.partialDeriv i ψ x * a x i := fun i =>
    ((PDE.continuous_partialDeriv i ψ hψ).mul (continuous_comp_apply a ca i)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hint2 : ∀ i, Integrable fun x => ψ x * Torus.partialDeriv i (fun y => a y i) x := fun i =>
    (cψ.mul (PDE.continuous_partialDeriv i _ (isCk_apply a ha i))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp only [hT]
  rw [integral_finsetSum _ (fun i _ => hint1 i)]
  have : ∀ x, ψ x * Torus.div a x = ∑ i, ψ x * Torus.partialDeriv i (fun y => a y i) x := by
    intro x; rw [partialDeriv_apply_eq_div a ha x, Finset.mul_sum]
  simp only [this]
  rw [integral_finsetSum _ (fun i _ => hint2 i), ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact PDE.integral_partialDeriv_mul i ψ (fun y => a y i) hψ (isCk_apply a ha i)


lemma stat_quad2 (n : ℕ) (hn : 1 ≤ n) (ψ : Torus d → ℝ) (hψ : Torus.IsCk 2 ψ) :
    |((n ^ d : ℕ) : ℝ)⁻¹ * ∑ j : Fin d → Fin n, ψ (latticePoint n j) - ∫ x, ψ x| ≤
      (d * Torus.cbNorm 2 ψ / n) * (d / (2 * n)) := by
  have hψ' : ContDiff ℝ 2 (Torus.lift ψ) := hψ
  have hψ2 : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) (Torus.lift ψ) := by exact_mod_cast hψ'
  have hbd : ∀ x, ‖iteratedFDeriv ℝ 2 (Torus.lift ψ) x‖ ≤ Torus.cbNorm 2 ψ :=
    fun x => le_cbNorm 2 2 le_rfl ψ hψ2 x
  have hM0 : 0 ≤ Torus.cbNorm 2 ψ := cbNorm_nonneg 2 ψ
  refine torus_quad n hn (continuous_of_lift' hψ'.continuous) fun y => ?_
  exact latAvg_C2 n hn (hψ'.differentiable (by norm_num)) hM0 (fderiv_lip hψ' hbd)
    (Torus.lift_periodic ψ) y

lemma stat_quad1 (n : ℕ) (hn : 1 ≤ n) (h : Torus d → ℝ) (hc : Continuous h) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ u v, |Torus.lift h u - Torus.lift h v| ≤ L * ‖u - v‖) :
    |((n ^ d : ℕ) : ℝ)⁻¹ * ∑ j : Fin d → Fin n, h (latticePoint n j) - ∫ x, h x| ≤
      L * (d / (2 * n)) :=
  torus_quad n hn hc fun y => latAvg_lip n hn (Torus.lift_periodic h) hL0 hL y

lemma taylor_avg (n : ℕ) (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {g : Euc d → ℝ}
    (hdiff : Differentiable ℝ g) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ u v, ‖fderiv ℝ g u - fderiv ℝ g v‖ ≤ M * ‖u - v‖) (A : Euc d → Euc d) {B : ℝ}
    (hB : ∀ x, ‖A x‖ ≤ B) :
    |((n ^ d : ℕ) : ℝ)⁻¹ * ∑ j : Fin d → Fin n,
      (g (zhat n j + κ⁻¹ • A (zhat n j)) - g (zhat n j) - κ⁻¹ * fderiv ℝ g (zhat n j) (A (zhat n j)))|
      ≤ M * (κ⁻¹ * B) ^ 2 := by
  have hN : (0 : ℝ) < ((n ^ d : ℕ) : ℝ) := by positivity
  have hB0 : 0 ≤ B := by
    by_cases h : Nonempty (Euc d)
    · obtain ⟨x⟩ := h; exact (norm_nonneg _).trans (hB x)
    · exact absurd ⟨0⟩ h
  rw [abs_mul, abs_of_pos (inv_pos.mpr hN)]
  have hs : |∑ j : Fin d → Fin n, (g (zhat n j + κ⁻¹ • A (zhat n j)) - g (zhat n j) -
      κ⁻¹ * fderiv ℝ g (zhat n j) (A (zhat n j)))| ≤ ∑ j : Fin d → Fin n, M * (κ⁻¹ * B) ^ 2 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    have := taylor2 hdiff hM0 hM (zhat n j) (κ⁻¹ • A (zhat n j))
    simp only [map_smul, smul_eq_mul] at this
    refine this.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hM0
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hκ)]
    exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left (hB _) (inv_nonneg.mpr hκ.le)) 2
  have hc : ∑ j : Fin d → Fin n, M * (κ⁻¹ * B) ^ 2 = ((n ^ d : ℕ) : ℝ) * (M * (κ⁻¹ * B) ^ 2) := by
    simp
  rw [hc] at hs
  calc ((n ^ d : ℕ) : ℝ)⁻¹ * |∑ j : Fin d → Fin n, (g (zhat n j + κ⁻¹ • A (zhat n j)) - g (zhat n j) -
      κ⁻¹ * fderiv ℝ g (zhat n j) (A (zhat n j)))|
      ≤ ((n ^ d : ℕ) : ℝ)⁻¹ * (((n ^ d : ℕ) : ℝ) * (M * (κ⁻¹ * B) ^ 2)) :=
        mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hN.le)
    _ = M * (κ⁻¹ * B) ^ 2 := by field_simp

lemma rpow_card (hd : 1 ≤ d) (n : ℕ) (hn : 1 ≤ n) :
    ((n ^ d : ℕ) : ℝ) ^ (-(2 : ℝ) / d) = ((n : ℝ) ^ 2)⁻¹ := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
  have : (d : ℝ) * (-(2 : ℝ) / d) = -2 := by field_simp
  rw [this, Real.rpow_neg hnpos.le]
  norm_num


lemma pair_perturbed (n : ℕ) (hn : 1 ≤ n) (κ : ℝ) (a : Torus d → Euc d) (ψ : Torus d → ℝ) :
    pair (empirical (perturbedLattice n κ a)) ψ =
      ((n ^ d : ℕ) : ℝ)⁻¹ * ∑ j : Fin d → Fin n,
        Torus.lift ψ (zhat n j + κ⁻¹ • Torus.lift a (zhat n j)) := by
  have hN : 0 < n ^ d := Nat.pow_pos (by omega : 0 < n)
  rw [pair_empirical hN]
  congr 1
  rw [← Equiv.sum_comp (finFunctionFinEquiv (m := n) (n := d)).symm]
  refine Finset.sum_congr rfl fun j _ => ?_
  show ψ (latticePoint n (finFunctionFinEquiv.symm j) +
    Torus.mk (κ⁻¹ • a (latticePoint n (finFunctionFinEquiv.symm j)))) = ψ (Torus.mk _)
  rw [mk_add', latticePoint_eq]
  rfl


lemma final_ineq {D P A κ n u v w : ℝ} (hD : 1 ≤ D) (hP : 0 ≤ P) (hκ : 0 < κ) (hn : 0 < n)
    (hu : u = κ⁻¹ * P * A ^ 2) (hv : v = κ * P / n ^ 2) (hw : w = P * A / n) :
    u + D ^ 2 / 2 * v + D * w ≤ (1 + D ^ 2) * (u + v) := by
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hv0 : 0 ≤ v := by rw [hv]; positivity
  have hw' : w ≤ (u + v) / 2 := by
    have h1 : (u + v) / 2 - w = P * κ⁻¹ * (A - κ / n) ^ 2 / 2 := by
      rw [hu, hv, hw]; field_simp; ring
    have h2 : 0 ≤ P * κ⁻¹ * (A - κ / n) ^ 2 / 2 := by positivity
    linarith
  nlinarith [mul_nonneg (by linarith : 0 ≤ D) hu0, mul_nonneg (by linarith : 0 ≤ D) hv0,
    mul_nonneg (by linarith : 0 ≤ D - 1) hu0, mul_nonneg (by linarith : 0 ≤ D - 1) hv0,
    mul_le_mul_of_nonneg_left hw' (by linarith : 0 ≤ D), mul_nonneg (mul_nonneg (by linarith : 0 ≤ D) (by linarith : 0 ≤ D)) hu0,
    mul_nonneg (mul_nonneg (by linarith : 0 ≤ D) (by linarith : 0 ≤ D)) hv0]


lemma stat_main (hd : 1 ≤ d) (n : ℕ) (hn : 1 ≤ n) (κ : ℝ) (hκ : 0 < κ) (a : Torus d → Euc d)
    (ha : Torus.IsCk 1 a) (ψ : Torus d → ℝ) (hψ : Torus.IsCk 2 ψ) :
    |κ * (pair (empirical (perturbedLattice n κ a)) ψ - ∫ x, ψ x) +
        ∫ x, ψ x * Torus.div a x| ≤
      (1 + (d : ℝ) ^ 2) * (κ⁻¹ * Torus.cbNorm 2 ψ * Torus.cbNorm 1 a ^ 2 +
        κ * ((n ^ d : ℕ) : ℝ) ^ (-(2 : ℝ) / d) * Torus.cbNorm 2 ψ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hN : (0 : ℝ) < ((n ^ d : ℕ) : ℝ) := by positivity
  set P := Torus.cbNorm 2 ψ with hPdef
  set A := Torus.cbNorm 1 a with hAdef
  have hP0 : 0 ≤ P := cbNorm_nonneg 2 ψ
  have hA0 : 0 ≤ A := cbNorm_nonneg 1 a
  have hg : ContDiff ℝ 2 (Torus.lift ψ) := hψ
  have hg2 : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) (Torus.lift ψ) := by exact_mod_cast hg
  have ha1 : ContDiff ℝ 1 (Torus.lift a) := ha
  have ha1' : ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) (Torus.lift a) := by exact_mod_cast ha1
  have hψ1 : Torus.IsCk 1 ψ := hψ.of_le (by norm_num)
  have hgd : Differentiable ℝ (Torus.lift ψ) := hg.differentiable (by norm_num)
  have had : Differentiable ℝ (Torus.lift a) := ha1.differentiable one_ne_zero
  have hM2 : ∀ x, ‖iteratedFDeriv ℝ 2 (Torus.lift ψ) x‖ ≤ P := fun x => le_cbNorm 2 2 le_rfl ψ hg2 x
  have hM1 : ∀ x, ‖fderiv ℝ (Torus.lift ψ) x‖ ≤ P := fun x => by
    have := le_cbNorm 2 1 (by norm_num) ψ hg2 x
    rwa [norm_iteratedFDeriv_one] at this
  have hB0 : ∀ x, ‖Torus.lift a x‖ ≤ A := fun x => by
    have := le_cbNorm 1 0 (by norm_num) a ha1' x
    rwa [norm_iteratedFDeriv_zero] at this
  have hB1 : ∀ x, ‖fderiv ℝ (Torus.lift a) x‖ ≤ A := fun x => by
    have := le_cbNorm 1 1 le_rfl a ha1' x
    rwa [norm_iteratedFDeriv_one] at this
  have hMlip := fderiv_lip hg hM2
  have halip := lip_of_fderiv had hB1
  -- Taylor
  have ht := taylor_avg n hn hκ hgd hP0 hMlip (Torus.lift a) hB0
  -- quadrature of psi
  have hq1 := stat_quad2 n hn ψ hψ
  -- quadrature of hT
  have hcT : Continuous (hT ψ a) := by
    unfold hT
    refine continuous_finsetSum _ fun i _ => ?_
    exact (PDE.continuous_partialDeriv i ψ hψ1).mul (continuous_comp_apply a (continuous_of_lift' ha.continuous) i)
  have hL : ∀ u v, |Torus.lift (hT ψ a) u - Torus.lift (hT ψ a) v| ≤ (P * A + P * A) * ‖u - v‖ := by
    intro u v
    rw [lift_hT ψ hψ1 a u, lift_hT ψ hψ1 a v]
    have e : fderiv ℝ (Torus.lift ψ) u (Torus.lift a u) - fderiv ℝ (Torus.lift ψ) v (Torus.lift a v) =
        (fderiv ℝ (Torus.lift ψ) u - fderiv ℝ (Torus.lift ψ) v) (Torus.lift a u) +
          fderiv ℝ (Torus.lift ψ) v (Torus.lift a u - Torus.lift a v) := by
      simp
    rw [e, ← Real.norm_eq_abs]
    refine (norm_add_le _ _).trans ?_
    have t1 : ‖(fderiv ℝ (Torus.lift ψ) u - fderiv ℝ (Torus.lift ψ) v) (Torus.lift a u)‖ ≤
        P * ‖u - v‖ * A :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul (hMlip u v) (hB0 u) (norm_nonneg _) (by positivity))
    have t2 : ‖fderiv ℝ (Torus.lift ψ) v (Torus.lift a u - Torus.lift a v)‖ ≤ P * (A * ‖u - v‖) :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul (hM1 v) (halip u v) (norm_nonneg _) hP0)
    nlinarith [t1, t2]
  have hq2 := stat_quad1 n hn (hT ψ a) hcT (by positivity) hL
  have hint := integral_hT ψ hψ1 a ha
  have hpair := pair_perturbed n hn κ a ψ
  have hhT : ∀ j : Fin d → Fin n,
      fderiv ℝ (Torus.lift ψ) (zhat n j) (Torus.lift a (zhat n j)) = hT ψ a (latticePoint n j) :=
    fun j => (lift_hT ψ hψ1 a (zhat n j)).symm
  have hlat : ∀ j : Fin d → Fin n, Torus.lift ψ (zhat n j) = ψ (latticePoint n j) := fun j => rfl
  set Sy := ((n ^ d : ℕ) : ℝ)⁻¹ * ∑ j : Fin d → Fin n,
    Torus.lift ψ (zhat n j + κ⁻¹ • Torus.lift a (zhat n j)) with hSy
  set Sp := ((n ^ d : ℕ) : ℝ)⁻¹ * ∑ j : Fin d → Fin n, ψ (latticePoint n j) with hSp
  set Sh := ((n ^ d : ℕ) : ℝ)⁻¹ * ∑ j : Fin d → Fin n, hT ψ a (latticePoint n j) with hSh
  have hR : ((n ^ d : ℕ) : ℝ)⁻¹ * ∑ j : Fin d → Fin n,
      (Torus.lift ψ (zhat n j + κ⁻¹ • Torus.lift a (zhat n j)) - Torus.lift ψ (zhat n j) -
        κ⁻¹ * fderiv ℝ (Torus.lift ψ) (zhat n j) (Torus.lift a (zhat n j))) =
      Sy - Sp - κ⁻¹ * Sh := by
    simp only [hhT, hlat, Finset.sum_sub_distrib, ← Finset.mul_sum, hSy, hSp, hSh]
    ring
  rw [hR] at ht
  rw [hpair]
  have hdecomp : κ * (Sy - ∫ x, ψ x) + ∫ x, ψ x * Torus.div a x =
      κ * (Sp - ∫ x, ψ x) + (Sh - ∫ x, hT ψ a x) + κ * (Sy - Sp - κ⁻¹ * Sh) := by
    rw [hint]
    field_simp
    ring
  rw [hdecomp]
  have hκinv : κ * κ⁻¹ = 1 := mul_inv_cancel₀ hκ.ne'
  -- bounds
  have b1 : |κ * (Sp - ∫ x, ψ x)| ≤ κ * ((d * P / n) * (d / (2 * n))) := by
    rw [abs_mul, abs_of_pos hκ]; exact mul_le_mul_of_nonneg_left hq1 hκ.le
  have b2 : |κ * (Sy - Sp - κ⁻¹ * Sh)| ≤ κ⁻¹ * P * A ^ 2 := by
    rw [abs_mul, abs_of_pos hκ]
    calc κ * |Sy - Sp - κ⁻¹ * Sh| ≤ κ * (P * (κ⁻¹ * A) ^ 2) := mul_le_mul_of_nonneg_left ht hκ.le
      _ = κ⁻¹ * P * A ^ 2 := by field_simp
  have b3 : |Sh - ∫ x, hT ψ a x| ≤ (P * A + P * A) * (d / (2 * n)) := hq2
  have hfin := final_ineq (D := (d : ℝ)) (P := P) (A := A) (κ := κ) (n := (n : ℝ))
    (u := κ⁻¹ * P * A ^ 2) (v := κ * P / (n : ℝ) ^ 2) (w := P * A / n)
    (by exact_mod_cast hd) hP0 hκ hnpos rfl rfl rfl
  rw [rpow_card hd n hn]
  calc _ ≤ |κ * (Sp - ∫ x, ψ x)| + |Sh - ∫ x, hT ψ a x| + |κ * (Sy - Sp - κ⁻¹ * Sh)| := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ ≤ κ * ((d * P / n) * (d / (2 * n))) + (P * A + P * A) * (d / (2 * n)) + κ⁻¹ * P * A ^ 2 := by
        linarith
    _ = κ⁻¹ * P * A ^ 2 + (d : ℝ) ^ 2 / 2 * (κ * P / (n : ℝ) ^ 2) + d * (P * A / n) := by
        field_simp
        ring
    _ ≤ (1 + (d : ℝ) ^ 2) * (κ⁻¹ * P * A ^ 2 + κ * P / (n : ℝ) ^ 2) := hfin
    _ = _ := by
        field_simp

end InitialDataAux

open InitialDataAux in
/-- Example A.39 `M:B:ex:lattice` (source lines 11608-11611), statistic level: for
`a ∈ C^1(𝕋^d; ℝ^d)` (the source takes `a ∈ C^∞`), `κ > 0`, `N = n^d` and `ψ ∈ C²`,
`|⟨ψ, κ(μ_{Y_N} - 1)⟩ + ⟨ψ, Div a⟩| ≤ C(κ⁻¹ ‖ψ‖_{C²} ‖a‖²_{C¹} + κ N^{-2/d} ‖ψ‖_{C²})`
with `C = C(d)`.  (The `N^{-1/d} ‖ψ‖_{C²}‖a‖_{C¹}` quadrature error of the first-order term,
omitted in the source display, is absorbed by AM-GM.) -/
theorem perturbedLattice_stat (hd : 1 ≤ d) :
    ∃ C : ℝ, ∀ (n : ℕ), 1 ≤ n → ∀ κ : ℝ, 0 < κ → ∀ a : Torus d → Euc d, Torus.IsCk 1 a →
      ∀ ψ : Torus d → ℝ, Torus.IsCk 2 ψ →
        |κ * (pair (empirical (perturbedLattice n κ a)) ψ - ∫ x, ψ x) +
            ∫ x, ψ x * Torus.div a x| ≤
          C * (κ⁻¹ * Torus.cbNorm 2 ψ * Torus.cbNorm 1 a ^ 2 +
            κ * ((n ^ d : ℕ) : ℝ) ^ (-(2 : ℝ) / d) * Torus.cbNorm 2 ψ) := by
  exact ⟨1 + (d : ℝ) ^ 2, fun n hn κ hκ a ha ψ hψ => stat_main hd n hn κ hκ a ha ψ hψ⟩

namespace InitialDataAux

lemma bdd_funRealCoeff (f : Torus d → ℝ) (hf : Continuous f) :
    ∃ C, ∀ k, |Torus.funRealCoeff f k| ≤ C := by
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨Real.sqrt 2 * B, fun k => ?_⟩
  have := norm_integral_le_of_norm_le_const (μ := (volume : Measure (Torus d)))
    (f := fun x => Torus.realMode k x * f x) (C := Real.sqrt 2 * B)
    (Filter.Eventually.of_forall fun x => ?_)
  · simpa [Torus.funRealCoeff] using this
  · rw [norm_mul]
    exact mul_le_mul (by simpa using Torus.abs_realMode_le k x) (hB x trivial) (norm_nonneg _)
      (by positivity)

lemma continuous_div (a : Torus d → Euc d) (ha : Torus.IsCk 1 a) : Continuous (Torus.div a) := by
  have : Torus.div a = fun x => ∑ i, Torus.partialDeriv i (fun y => a y i) x :=
    funext (partialDeriv_apply_eq_div a ha)
  rw [this]
  exact continuous_finsetSum _ fun i _ => PDE.continuous_partialDeriv i _ (isCk_apply a ha i)

lemma field_coord (γ : ℝ) (hγ : (d : ℝ) < 2 * γ) (n : ℕ) (hn : 1 ≤ n) (κ : ℝ)
    (a : Torus d → Euc d) (ha : Torus.IsCk 1 a) (k : NonzeroLattice d) :
    NegSobolev.coord (κ • NegSobolev.ofMeasureDiff γ (empirical (perturbedLattice n κ a)) volume -
        NegSobolev.ofFun γ (fun x => -Torus.div a x)) k =
      Lattice.jp k.1 ^ (-γ) * (κ * (pair (empirical (perturbedLattice n κ a)) (Torus.realMode k) -
        ∫ x, Torus.realMode k x) + ∫ x, Torus.realMode k x * Torus.div a x) := by
  have hN : 0 < n ^ d := Nat.pow_pos (by omega : 0 < n)
  have : IsProbabilityMeasure (empirical (perturbedLattice n κ a)) := empirical_isProbabilityMeasure hN _
  set μ := empirical (perturbedLattice n κ a) with hμ
  have hb : ∃ C, ∀ k, |Torus.measureRealCoeff μ k - Torus.measureRealCoeff volume k| ≤ C := by
    refine ⟨Real.sqrt 2 * (μ Set.univ).toReal + Real.sqrt 2 * ((volume : Measure (Torus d)) Set.univ).toReal, fun k => ?_⟩
    exact (abs_sub _ _).trans (add_le_add (Torus.abs_measureRealCoeff_le μ k)
      (Torus.abs_measureRealCoeff_le volume k))
  have hmem1 := NegSobolev.memℓp_of_bounded hγ _ hb
  have hbf := bdd_funRealCoeff (fun x => -Torus.div a x) (continuous_div a ha).neg
  have hmem2 := NegSobolev.memℓp_of_bounded hγ _ hbf
  have h1 : NegSobolev.coord (NegSobolev.ofMeasureDiff γ μ volume) k =
      Lattice.jp k.1 ^ (-γ) * (Torus.measureRealCoeff μ k - Torus.measureRealCoeff volume k) :=
    NegSobolev.coord_ofSeq_of_mem _ hmem1 k
  have h2 : NegSobolev.coord (NegSobolev.ofFun γ (fun x => -Torus.div a x)) k =
      Lattice.jp k.1 ^ (-γ) * Torus.funRealCoeff (fun x => -Torus.div a x) k :=
    NegSobolev.coord_ofSeq_of_mem _ hmem2 k
  have h3 : NegSobolev.coord (κ • NegSobolev.ofMeasureDiff γ μ volume -
        NegSobolev.ofFun γ (fun x => -Torus.div a x)) k =
      κ * NegSobolev.coord (NegSobolev.ofMeasureDiff γ μ volume) k -
        NegSobolev.coord (NegSobolev.ofFun γ (fun x => -Torus.div a x)) k := rfl
  rw [h3, h1, h2]
  have e1 : Torus.measureRealCoeff μ k = pair μ (Torus.realMode k) := rfl
  have e2 : Torus.measureRealCoeff volume k = ∫ x, Torus.realMode k x := rfl
  have e3 : Torus.funRealCoeff (fun x => -Torus.div a x) k = -∫ x, Torus.realMode k x * Torus.div a x := by
    unfold Torus.funRealCoeff
    rw [← integral_neg]
    congr 1; funext x; ring
  rw [e1, e2, e3]
  ring


lemma field_main (hd : 1 ≤ d) (γ : ℝ) (hγ : (d : ℝ) / 2 + 2 < γ) :
    ∃ C : ℝ, ∀ (n : ℕ), 1 ≤ n → ∀ κ : ℝ, 0 < κ → ∀ a : Torus d → Euc d, Torus.IsCk 1 a →
      ‖κ • NegSobolev.ofMeasureDiff γ (empirical (perturbedLattice n κ a)) volume -
          NegSobolev.ofFun γ (fun x => -Torus.div a x)‖ ≤
        C * (κ⁻¹ * Torus.cbNorm 1 a ^ 2 + κ * ((n ^ d : ℕ) : ℝ) ^ (-(2 : ℝ) / d)) := by
  have hm : (d : ℝ) < 2 * (γ - 2) := by linarith
  have hγ' : (d : ℝ) < 2 * γ := by linarith
  obtain ⟨C₂, hC₂⟩ := Torus.cbNorm_realMode_le (d := d) 2
  have hsum := summable_jp_rpow (d := d) (γ - 2) hm
  set S := ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * (γ - 2))) with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun k => (Real.rpow_pos_of_pos (Torus.jp_pos k.1) _).le
  refine ⟨(1 + (d : ℝ) ^ 2) * |C₂| * Real.sqrt S, fun n hn κ hκ a ha => ?_⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set A := Torus.cbNorm 1 a with hA
  set Nr := ((n ^ d : ℕ) : ℝ) ^ (-(2 : ℝ) / d) with hNr
  have hNr0 : 0 ≤ Nr := Real.rpow_nonneg (by positivity) _
  set X := κ⁻¹ * A ^ 2 + κ * Nr with hX
  have hX0 : 0 ≤ X := by positivity
  set K := (1 + (d : ℝ) ^ 2) * |C₂| with hK
  have hK0 : 0 ≤ K := by positivity
  obtain ⟨hF2, hFn⟩ := NegSobolev.coord_sq (κ • NegSobolev.ofMeasureDiff γ (empirical (perturbedLattice n κ a)) volume -
          NegSobolev.ofFun γ (fun x => -Torus.div a x))
  have hcoord : ∀ k : NonzeroLattice d,
      NegSobolev.coord (κ • NegSobolev.ofMeasureDiff γ (empirical (perturbedLattice n κ a)) volume -
          NegSobolev.ofFun γ (fun x => -Torus.div a x)) k ^ 2 ≤
        (K * X) ^ 2 * Lattice.jp k.1 ^ (-(2 * (γ - 2))) := by
    intro k
    have hj := Torus.jp_pos k.1
    rw [field_coord γ hγ' n hn κ a ha k]
    set T := κ * (pair (empirical (perturbedLattice n κ a)) (Torus.realMode k) -
        ∫ x, Torus.realMode k x) + ∫ x, Torus.realMode k x * Torus.div a x with hT'
    have h0 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift (Torus.realMode k)) :=
      isSmooth_realMode k
    have hsm : Torus.IsCk 2 (Torus.realMode k) := h0.of_le (WithTop.coe_le_coe.mpr le_top)
    have hst := stat_main hd n hn κ hκ a ha (Torus.realMode k) hsm
    have hP := hC₂ k
    have hP0 := cbNorm_nonneg 2 (Torus.realMode k)
    set P := Torus.cbNorm 2 (Torus.realMode k) with hPd
    have hTb : |T| ≤ K * Lattice.jp k.1 ^ 2 * X := by
      refine hst.trans ?_
      calc (1 + (d : ℝ) ^ 2) * (κ⁻¹ * P * A ^ 2 + κ * Nr * P) = (1 + (d : ℝ) ^ 2) * (P * X) := by
            rw [hX]; ring
        _ ≤ (1 + (d : ℝ) ^ 2) * (|C₂| * Lattice.jp k.1 ^ 2 * X) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ hX0) (by positivity)
            exact hP.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
        _ = K * Lattice.jp k.1 ^ 2 * X := by rw [hK]; ring
    have hT2 : T ^ 2 ≤ (K * Lattice.jp k.1 ^ 2 * X) ^ 2 := by
      rw [← sq_abs T]
      exact pow_le_pow_left₀ (abs_nonneg _) hTb 2
    have hJ : (Lattice.jp k.1 ^ (-γ)) ^ 2 * (Lattice.jp k.1 ^ 2) ^ 2 =
        Lattice.jp k.1 ^ (-(2 * (γ - 2))) := by
      rw [Torus.jp_rpow_sq]
      have : (Lattice.jp k.1 ^ 2) ^ 2 = Lattice.jp k.1 ^ ((4 : ℕ) : ℝ) := by
        rw [Real.rpow_natCast]; ring
      rw [this, ← Real.rpow_add hj]
      congr 1; push_cast; ring
    calc (Lattice.jp k.1 ^ (-γ) * T) ^ 2 = (Lattice.jp k.1 ^ (-γ)) ^ 2 * T ^ 2 := by ring
      _ ≤ (Lattice.jp k.1 ^ (-γ)) ^ 2 * (K * Lattice.jp k.1 ^ 2 * X) ^ 2 :=
          mul_le_mul_of_nonneg_left hT2 (by positivity)
      _ = (K * X) ^ 2 * ((Lattice.jp k.1 ^ (-γ)) ^ 2 * (Lattice.jp k.1 ^ 2) ^ 2) := by ring
      _ = _ := by rw [hJ]
  have hle : ‖κ • NegSobolev.ofMeasureDiff γ (empirical (perturbedLattice n κ a)) volume -
          NegSobolev.ofFun γ (fun x => -Torus.div a x)‖ ^ 2 ≤ (K * X * Real.sqrt S) ^ 2 := by
    rw [hFn, mul_pow, Real.sq_sqrt hS0, hS, ← tsum_mul_left]
    exact hF2.tsum_le_tsum hcoord (hsum.mul_left _)
  have := (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (two_ne_zero)).mp hle
  calc _ ≤ K * X * Real.sqrt S := this
    _ = _ := by rw [hK]; ring

end InitialDataAux

open InitialDataAux in
/-- Example A.39 (source lines 11611-11612), field level: for `γ > d/2 + 2`,
`‖κ(μ_{Y_N} - 1) - (-Div a)‖_{H^{-γ}} ≤ C (κ⁻¹ ‖a‖²_{C¹} + κ N^{-2/d})`, `C = C(d, γ)`
(by summing the statistic estimate over modes, `‖e_k‖_{C²} ≤ C⟨k⟩²`). -/
theorem perturbedLattice_field (hd : 1 ≤ d) (γ : ℝ) (hγ : (d : ℝ) / 2 + 2 < γ) :
    ∃ C : ℝ, ∀ (n : ℕ), 1 ≤ n → ∀ κ : ℝ, 0 < κ → ∀ a : Torus d → Euc d, Torus.IsCk 1 a →
      ‖κ • NegSobolev.ofMeasureDiff γ (empirical (perturbedLattice n κ a)) volume -
          NegSobolev.ofFun γ (fun x => -Torus.div a x)‖ ≤
        C * (κ⁻¹ * Torus.cbNorm 1 a ^ 2 + κ * ((n ^ d : ℕ) : ℝ) ^ (-(2 : ℝ) / d)) := by
  exact field_main hd γ hγ

namespace InitialDataAux


lemma smooth_weighted_summable (m : ℝ) (φ : Torus d → ℝ) (hφ : Torus.IsSmooth φ) :
    Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff φ k ^ 2 := by
  set n : ℕ := ⌈m + (d : ℝ) / 2⌉₊ + 1 with hn
  have hnm : m + (d : ℝ) / 2 + 1 ≤ n := by
    have := Nat.le_ceil (m + (d : ℝ) / 2)
    rw [hn]; push_cast; linarith
  have h0 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift φ) := hφ
  have hcd : ContDiff ℝ n (Torus.lift φ) := h0.of_le (by exact_mod_cast le_top)
  obtain ⟨B, hB⟩ := Torus.fcoef_pow_decay hcd
  have hcont : Continuous φ := continuous_of_lift' hcd.continuous
  have hint : Integrable φ :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hsum := summable_jp_rpow (d := d) ((n : ℝ) - m) (by linarith)
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _)
    (sq_nonneg _)) (fun k => ?_) (hsum.mul_left (2 * B ^ 2))
  have hj := Torus.jp_pos k.1
  have h1 := Torus.abs_funRealCoeff_le hint k
  have h2 : ‖Torus.fcoef φ k.1‖ ≤ B / Lattice.jp k.1 ^ n := by
    rw [le_div_iff₀ (pow_pos hj _)]; exact hB k
  have h3 : Torus.funRealCoeff φ k ^ 2 ≤ 2 * (B / Lattice.jp k.1 ^ n) ^ 2 := by
    rw [← sq_abs]
    calc |Torus.funRealCoeff φ k| ^ 2 ≤ (Real.sqrt 2 * ‖Torus.fcoef φ k.1‖) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = 2 * ‖Torus.fcoef φ k.1‖ ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by norm_num)]
      _ ≤ _ := by gcongr
  have h4 : Lattice.jp k.1 ^ (2 * m) * (2 * (B / Lattice.jp k.1 ^ n) ^ 2) =
      2 * B ^ 2 * Lattice.jp k.1 ^ (-(2 * ((n : ℝ) - m))) := by
    rw [show -(2 * ((n : ℝ) - m)) = 2 * m + -(2 * n) by ring, Real.rpow_add hj]
    have : Lattice.jp k.1 ^ (-(2 * (n : ℝ))) = (Lattice.jp k.1 ^ n)⁻¹ ^ 2 := by
      rw [Real.rpow_neg hj.le, show 2 * (n : ℝ) = ((2 * n : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast, pow_mul', inv_pow]
    rw [this, div_eq_mul_inv, mul_pow, inv_pow]
    ring
  calc _ ≤ Lattice.jp k.1 ^ (2 * m) * (2 * (B / Lattice.jp k.1 ^ n) ^ 2) :=
        mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hj.le _)
    _ = _ := h4


lemma wvec_mem (m : ℝ) (hm : (d : ℝ) < 2 * m) (t : Torus d) :
    Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * Torus.realMode k t) 2 := by
  rw [Torus.memℓp_two_iff]
  have hs := summable_jp_rpow (d := d) m hm
  refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_) (hs.mul_left 2)
  rw [mul_pow, Torus.jp_rpow_sq, show 2 * (-m) = -(2 * m) by ring]
  have := Torus.abs_realMode_le k t
  have h2 : Torus.realMode k t ^ 2 ≤ 2 := by
    rw [← sq_abs]
    calc |Torus.realMode k t| ^ 2 ≤ Real.sqrt 2 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
      _ = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [Real.rpow_nonneg (Torus.jp_pos k.1).le (-(2 * m))]

def wvec (m : ℝ) (hm : (d : ℝ) < 2 * m) (t : Torus d) : NegSobolev d m :=
  (⟨fun k => Lattice.jp k.1 ^ (-m) * Torus.realMode k t, wvec_mem m hm t⟩ :
    lp (fun _ : NonzeroLattice d => ℝ) 2)

lemma coord_wvec (m : ℝ) (hm : (d : ℝ) < 2 * m) (t : Torus d) (k : NonzeroLattice d) :
    NegSobolev.coord (wvec m hm t) k = Lattice.jp k.1 ^ (-m) * Torus.realMode k t := rfl

lemma norm_wvec_sq_le (m : ℝ) (hm : (d : ℝ) < 2 * m) (t : Torus d) :
    ‖wvec m hm t‖ ^ 2 ≤ 2 * ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m)) := by
  have hs := summable_jp_rpow (d := d) m hm
  obtain ⟨h1, h2⟩ := NegSobolev.coord_sq (wvec m hm t)
  rw [h2, ← tsum_mul_left]
  refine h1.tsum_le_tsum (fun k => ?_) (hs.mul_left 2)
  rw [coord_wvec, mul_pow, Torus.jp_rpow_sq, show 2 * (-m) = -(2 * m) by ring]
  have := Torus.abs_realMode_le k t
  have h2 : Torus.realMode k t ^ 2 ≤ 2 := by
    rw [← sq_abs]
    calc |Torus.realMode k t| ^ 2 ≤ Real.sqrt 2 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
      _ = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [Real.rpow_nonneg (Torus.jp_pos k.1).le (-(2 * m))]

lemma continuous_wvec (m : ℝ) (hm : (d : ℝ) < 2 * m) : Continuous (wvec m hm) := by
  have hs := summable_jp_rpow (d := d) m hm
  refine continuous_iff_continuousAt.mpr fun s => ?_
  set g : Torus d → ℝ := fun t => ∑' k : NonzeroLattice d,
    (Lattice.jp k.1 ^ (-m) * (Torus.realMode k t - Torus.realMode k s)) ^ 2 with hg
  have hcont : ∀ k : NonzeroLattice d, Continuous fun t : Torus d =>
      (Lattice.jp k.1 ^ (-m) * (Torus.realMode k t - Torus.realMode k s)) ^ 2 := fun k =>
    (continuous_const.mul ((continuous_realMode k).sub continuous_const)).pow 2
  have hbnd : ∀ (k : NonzeroLattice d) (t : Torus d),
      ‖(Lattice.jp k.1 ^ (-m) * (Torus.realMode k t - Torus.realMode k s)) ^ 2‖ ≤
        8 * Lattice.jp k.1 ^ (-(2 * m)) := by
    intro k t
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow, Torus.jp_rpow_sq,
      show 2 * (-m) = -(2 * m) by ring]
    have h1 := Torus.abs_realMode_le k t
    have h2 := Torus.abs_realMode_le k s
    have h3 : (Torus.realMode k t - Torus.realMode k s) ^ 2 ≤ 8 := by
      rw [← sq_abs]
      have : |Torus.realMode k t - Torus.realMode k s| ≤ 2 * Real.sqrt 2 := by
        rw [abs_le] at *; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
      calc _ ≤ (2 * Real.sqrt 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
        _ = 8 := by rw [mul_pow, Real.sq_sqrt (by norm_num)]; norm_num
    nlinarith [Real.rpow_nonneg (Torus.jp_pos k.1).le (-(2 * m))]
  have hgc : Continuous g :=
    continuous_tsum (f := fun (k : NonzeroLattice d) (t : Torus d) =>
      (Lattice.jp k.1 ^ (-m) * (Torus.realMode k t - Torus.realMode k s)) ^ 2)
      (u := fun k => 8 * Lattice.jp k.1 ^ (-(2 * m))) hcont (hs.mul_left 8) hbnd
  have hnorm : ∀ t, ‖wvec m hm t - wvec m hm s‖ = Real.sqrt (g t) := by
    intro t
    obtain ⟨h1, h2⟩ := NegSobolev.coord_sq (wvec m hm t - wvec m hm s)
    rw [← Real.sqrt_sq (norm_nonneg _), h2]
    congr 1
    refine tsum_congr fun k => ?_
    have e : NegSobolev.coord (wvec m hm t - wvec m hm s) k =
        NegSobolev.coord (wvec m hm t) k - NegSobolev.coord (wvec m hm s) k := rfl
    rw [e, coord_wvec, coord_wvec]
    ring
  have hg0 : g s = 0 := by simp [hg]
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  simp_rw [hnorm]
  have := (Real.continuous_sqrt.comp hgc).continuousAt (x := s)
  simpa [Function.comp_def, hg0] using this.tendsto


lemma smooth_contDiff (φ : Torus d → ℝ) (hφ : Torus.IsSmooth φ) (n : ℕ) :
    ContDiff ℝ n (Torus.lift φ) := by
  have h0 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift φ) := hφ
  exact h0.of_le (by exact_mod_cast le_top)

lemma inner_yvec_wvec (m : ℝ) (hm : (d : ℝ) < 2 * m) (φ : Torus d → ℝ) (hφ : Torus.IsSmooth φ)
    (t : Torus d) :
    inner ℝ (yvec m φ (smooth_weighted_summable m φ hφ)) (wvec m hm t) = φ t - Torus.mean φ := by
  have hd := smooth_contDiff φ hφ
  have hc : Continuous φ := continuous_of_lift' (hd 0).continuous
  have hsum := Torus.hasSum_realExpansion hc (Torus.summable_fcoef_of_contDiff hd) t
  have := lp.inner_eq_tsum (𝕜 := ℝ) (G := fun _ : NonzeroLattice d => ℝ)
    (yvec m φ (smooth_weighted_summable m φ hφ) : lp (fun _ : NonzeroLattice d => ℝ) 2)
    (wvec m hm t : lp (fun _ : NonzeroLattice d => ℝ) 2)
  refine this.trans (Eq.trans (tsum_congr fun k => ?_) hsum.tsum_eq)
  simp only [yvec, wvec, RCLike.inner_apply, conj_trivial]
  have e : Lattice.jp k.1 ^ (-m) * Lattice.jp k.1 ^ m = 1 := by
    rw [← Real.rpow_add (Torus.jp_pos k.1)]; simp
  linear_combination (Torus.funRealCoeff φ k * Torus.realMode k t) * e

lemma integrable_cont (μ : Measure (Torus d)) [IsProbabilityMeasure μ] {f : Torus d → ℝ}
    (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma iid_cov_formula (μ : Measure (Torus d)) [IsProbabilityMeasure μ] {φ ψ : Torus d → ℝ}
    (hφ : Continuous φ) (hψ : Continuous ψ) :
    ∫ t, (φ t - pair μ φ) * (ψ t - pair μ ψ) ∂μ = iidCov μ φ ψ := by
  have i1 : Integrable (fun t => φ t * ψ t) μ := integrable_cont μ (hφ.mul hψ)
  have i2 := integrable_cont μ hφ
  have i3 := integrable_cont μ hψ
  have e : ∀ t, (φ t - pair μ φ) * (ψ t - pair μ ψ) =
      φ t * ψ t - pair μ ψ * φ t - pair μ φ * ψ t + pair μ φ * pair μ ψ := fun t => by ring
  simp_rw [e]
  have j1 : Integrable (fun t => φ t * ψ t - pair μ ψ * φ t) μ := i1.sub (i2.const_mul _)
  have j2 : Integrable (fun t => φ t * ψ t - pair μ ψ * φ t - pair μ φ * ψ t) μ :=
    j1.sub (i3.const_mul _)
  rw [integral_add j2 (integrable_const _), integral_sub j1 (i3.const_mul _),
    integral_sub i1 (i2.const_mul _), integral_const_mul, integral_const_mul]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  unfold iidCov pair
  ring

end InitialDataAux

open InitialDataAux in
theorem exists_iid_gaussian_field_proof (m : ℝ) (hm : (d : ℝ) / 2 < m) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] :
    ∃ ν : Measure (NegSobolev d m), IsProbabilityMeasure ν ∧
      IsCenteredGaussianWithCov m ν (iidCov μ) := by
  have := negSobolev_secondCountable d m
  have hm' : (d : ℝ) < 2 * m := by linarith
  have hwc := continuous_wvec m hm'
  set S := ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m)) with hS
  have hmemw : MemLp (wvec m hm') 2 μ := by
    refine MemLp.of_bound hwc.aestronglyMeasurable (Real.sqrt (2 * S)) (Filter.Eventually.of_forall fun t => ?_)
    exact Real.le_sqrt_of_sq_le (by simpa using norm_wvec_sq_le m hm' t)
  have hwi : Integrable (wvec m hm') μ := hmemw.integrable one_le_two
  set mbar : NegSobolev d m := ∫ t, wvec m hm' t ∂μ with hmbar
  set X : Torus d → NegSobolev d m := fun t => wvec m hm' t - mbar with hX
  have hXc : Continuous X := hwc.sub continuous_const
  have hXm : MemLp X 2 μ := hmemw.sub (memLp_const _)
  have hX0 : ∫ t, X t ∂μ = 0 := by
    simp only [hX]
    rw [integral_sub hwi (integrable_const _)]
    simp [hmbar]
  obtain ⟨hC, -⟩ := isTraceClassCov_covarianceBilin μ X hXm hX0
  obtain ⟨γ, hγp, hγg, hγc⟩ := exists_centeredGaussian_of_traceClass _ hC
  refine ⟨γ, hγp, hγg, ?_⟩
  intro φ ψ hφ hψ
  have hφs := smooth_weighted_summable m φ hφ
  have hψs := smooth_weighted_summable m ψ hψ
  simp_rw [eval_eq_inner m φ hφs, eval_eq_inner m ψ hψs]
  set a := yvec m φ hφs
  set b := yvec m ψ hψs
  have : IsGaussian γ := hγg.1
  have hmemγ : MemLp id 2 γ := IsGaussian.memLp_two_id
  have hγ0 : γ[id] = 0 := gaussian_integral_id_eq_zero hγg
  have h1 : ∫ F, inner ℝ a F * inner ℝ b F ∂γ = covarianceBilin γ a b := by
    rw [covarianceBilin_apply hmemγ]
    simp only [hγ0, sub_zero]
  rw [h1, hγc a b]
  -- covariance of the law of X
  have hXae : AEMeasurable X μ := hXc.aemeasurable
  have hmemlaw : MemLp id 2 (law μ X) :=
    (memLp_map_measure_iff aestronglyMeasurable_id hXae).mpr hXm
  rw [covarianceBilin_apply hmemlaw]
  have hlaw0 : (law μ X)[id] = 0 := by
    show ∫ z, id z ∂(μ.map X) = 0
    rw [integral_map hXae aestronglyMeasurable_id]
    exact hX0
  rw [hlaw0]
  simp only [sub_zero]
  show ∫ z, inner ℝ a z * inner ℝ b z ∂(μ.map X) = _
  rw [integral_map hXae (by fun_prop)]
  -- pointwise values
  have hmean_inner : ∀ (f : Torus d → ℝ) (hf : Torus.IsSmooth f)
      (hh : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff f k ^ 2),
      inner ℝ (yvec m f hh) mbar = pair μ f - Torus.mean f := by
    intro f hf hh
    rw [hmbar, ← integral_inner hwi]
    simp_rw [inner_yvec_wvec m hm' f hf]
    have hfc : Continuous f := continuous_of_lift' ((smooth_contDiff f hf 0).continuous)
    rw [integral_sub (integrable_cont μ hfc) (integrable_const _)]
    simp [pair]
  have hpt : ∀ (f : Torus d → ℝ) (hf : Torus.IsSmooth f)
      (hh : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff f k ^ 2) t,
      inner ℝ (yvec m f hh) (X t) = f t - pair μ f := by
    intro f hf hh t
    simp only [hX, inner_sub_right]
    rw [inner_yvec_wvec m hm' f hf t, hmean_inner f hf hh]
    ring
  have hφc : Continuous φ := continuous_of_lift' ((smooth_contDiff φ hφ 0).continuous)
  have hψc : Continuous ψ := continuous_of_lift' ((smooth_contDiff ψ hψ 0).continuous)
  have := iid_cov_formula μ hφc hψc
  rw [← this]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show inner ℝ (yvec m φ hφs) (X t) * inner ℝ (yvec m ψ hψs) (X t) = _
  rw [hpt φ hφ hφs t, hpt ψ hψ hψs t]

open InitialDataAux in
/-- Example A.17 `M:B:ex:iid` (source lines 10469-10472): for `m > d/2` and every probability
measure `μ°` there is a centered Gaussian law on `E_m = H^{-m}_0` with the bridge covariance
`μ°(ψφ) - μ°(ψ)μ°(φ)`. -/
theorem exists_iid_gaussian_field (m : ℝ) (hm : (d : ℝ) / 2 < m) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] :
    ∃ ν : Measure (NegSobolev d m), IsProbabilityMeasure ν ∧
      IsCenteredGaussianWithCov m ν (iidCov μ) := by
  exact exists_iid_gaussian_field_proof m hm μ

/-! ### Example A.39: energy of the perturbed lattice (route of the proof)

The statement is provable as stated for every `d ≥ 1` (`N = n^d ≥ 4`, `s < d`, so
`g = periodicRiesz d s` is integrable with mean zero, `∫ g(x - y) dy = 0`, hence
`F_N(Y,1) = (2N²)⁻¹ ∑_{i≠j} g(Y_i - Y_j)`; all terms have genuine values, no junk integral is
used).  For `d = 1` the kernel inputs (smoothness off the origin, the gradient identity, the local
singularity, the mean-zero property) are those of `HRS/Kernel/D1.lean`; the lower bound for
`g_T(0)` in `s = 0` is uniform in `d ≥ 1`.  Let `Z = Λ_N`, `Y_i = Z_i + κ⁻¹ a(Z_i)`.

1. *Perturbation* (`perturb_pair_sum`).  With `z = Z_i - Z_j`, `δ = κ⁻¹(a(Z_i) - a(Z_j))`,
   `|δ| ≤ κ⁻¹ L |z|_T ≤ |z|_T/2` for `κ ≥ 2L`, the second-order Taylor expansion of `g`
   along the segment `[z, z+δ]` (which avoids the lattice) gives
   `g(z+δ) = g(z) + ∇g(z)·δ + R`, `|R| ≤ C |δ|² (|z|^{-s-2} + 1) ≤ C' κ⁻² (|z|^{-s} + 1)`
   (`taylor_gt`: near `0` use `g = |x|^{-s} + r` with `r` smooth, far from the lattice use a
   compactness bound on `D²g`).  The first-order terms cancel *exactly* by the lattice symmetry
   `z_j ↦ 2 z_i - z_j` and the oddness of `∇g` (`first_order_zero`).  Finally
   `|z|^{-s} ≤ g(z) + K`, so `∑_{i≠j}|R_ij| ≤ C κ⁻² N²`.
2. *Perfect lattice* (`lattice_pair_sum`), `ε = n⁻²`, `g = g_ε + f_ε` (truncation of
   `HRS/Energy/Coercivity.lean`): `∑_{i≠j} g(Z_ij) = N² ∑_{k ∈ nℤ^d} ĝ_ε(k) - N g_ε(0) +
   ∑_{i≠j} f_ε(Z_ij)`.  The first term is `≤ C N n^s` because `ĝ_ε(nm) ≲ n^{s-d} e^{-|m|²/2}`;
   the third is `≤ C N n^s` by the Gaussian bound on the periodic heat kernel and an injective
   count of the lattice points (`row_pointwise`, `nearF_row_le`); `g_ε(0) ≥ 0`, and for `s = 0`
   `g_ε(0) ≥ log n - C`, which cancels the logarithmic term of `o_N`.
3. Assembly (`perturbedLattice_energy_aux`): `n^s / N = N^{s/d-1}` and
   `log N / (2 d N) = log n / (2 N)`.
-/

namespace LatticeEnergyAux

open Set

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- one-dimensional Taylor remainder bound from a second-derivative bound -/
theorem taylor1 {φ ψ χ : ℝ → ℝ} {M : ℝ}
    (hφ : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt φ (ψ t) t)
    (hψ : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt ψ (χ t) t)
    (hχ : ∀ t ∈ Icc (0:ℝ) 1, |χ t| ≤ M) :
    |φ 1 - φ 0 - ψ 0| ≤ M := by
  have h0 : (0:ℝ) ∈ Icc (0:ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hψb : ∀ t ∈ Icc (0:ℝ) 1, |ψ t - ψ 0| ≤ M := by
    intro t ht
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := ψ) (f' := χ) (s := Icc (0:ℝ) 1)
      (C := M) (fun x hx => (hψ x hx).hasDerivWithinAt) (fun x hx => by
        simpa [Real.norm_eq_abs] using hχ x hx) (convex_Icc 0 1) h0 ht
    rw [Real.norm_eq_abs] at this
    have h2 : |t - 0| ≤ 1 := by
      rw [sub_zero, abs_of_nonneg ht.1]; exact ht.2
    have hM : 0 ≤ M := (abs_nonneg _).trans (hχ 0 h0)
    calc |ψ t - ψ 0| ≤ M * ‖t - 0‖ := by simpa [Real.norm_eq_abs] using this
      _ ≤ M * 1 := by rw [Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left h2 hM
      _ = M := mul_one M
  have hE : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt (fun t => φ t - φ 0 - t * ψ 0) (ψ t - ψ 0) t := by
    intro t ht
    have h1 := (hφ t ht).sub_const (φ 0)
    have h2 := (hasDerivAt_id t).mul_const (ψ 0)
    have h3 := h1.sub h2
    convert h3 using 1
    · funext x; simp
    · simp
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun t => φ t - φ 0 - t * ψ 0)
    (f' := fun t => ψ t - ψ 0) (s := Icc (0:ℝ) 1) (C := M)
    (fun x hx => (hE x hx).hasDerivWithinAt) (fun x hx => by
      simpa [Real.norm_eq_abs] using hψb x hx) (convex_Icc 0 1) h0 (⟨zero_le_one, le_rfl⟩ : (1:ℝ) ∈ Icc (0:ℝ) 1)
  simpa [Real.norm_eq_abs] using this

theorem hasDerivAt_line (y δ : Euc d) (t : ℝ) :
    HasDerivAt (fun t : ℝ => y + t • δ) δ t := by
  simpa using ((hasDerivAt_id t).smul_const δ).const_add y

/-- second-order Taylor bound along a segment, for a function that is `C²` near the segment -/
theorem taylor2 {h : Euc d → ℝ} {y δ : Euc d} {M : ℝ}
    (hc : ∀ t ∈ Icc (0:ℝ) 1, ContDiffAt ℝ 2 h (y + t • δ))
    (hM : ∀ t ∈ Icc (0:ℝ) 1, ‖fderiv ℝ (fderiv ℝ h) (y + t • δ)‖ ≤ M) :
    |h (y + δ) - h y - fderiv ℝ h y δ| ≤ M * ‖δ‖ ^ 2 := by
  have h0 : (0:ℝ) ∈ Icc (0:ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have key := taylor1 (φ := fun t : ℝ => h (y + t • δ))
    (ψ := fun t : ℝ => fderiv ℝ h (y + t • δ) δ)
    (χ := fun t : ℝ => fderiv ℝ (fderiv ℝ h) (y + t • δ) δ δ) (M := M * ‖δ‖ ^ 2)
    (fun t ht => ?_) (fun t ht => ?_) (fun t ht => ?_)
  · simpa using key
  · have hd : DifferentiableAt ℝ h (y + t • δ) := ((hc t ht).differentiableAt (by norm_num))
    exact hd.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_line y δ t)
  · have hd : DifferentiableAt ℝ (fderiv ℝ h) (y + t • δ) :=
      ((hc t ht).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have h1 := hd.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_line y δ t)
    have h2 := (ContinuousLinearMap.apply ℝ ℝ δ).hasFDerivAt.comp_hasDerivAt t h1
    exact h2
  · calc |fderiv ℝ (fderiv ℝ h) (y + t • δ) δ δ|
        ≤ ‖fderiv ℝ (fderiv ℝ h) (y + t • δ)‖ * ‖δ‖ * ‖δ‖ := by
          rw [← Real.norm_eq_abs]; exact ContinuousLinearMap.le_opNorm₂ _ _ _
      _ ≤ M * ‖δ‖ * ‖δ‖ := by gcongr; exact hM t ht
      _ = M * ‖δ‖ ^ 2 := by ring

theorem fderiv_periodic {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : Euc d → F)
    (hf : ∀ x (m : Lattice d), f (x + Lattice.toEuc m) = f x) (x : Euc d) (m : Lattice d) :
    fderiv ℝ f (x + Lattice.toEuc m) = fderiv ℝ f x := by
  rw [← fderiv_comp_add_right]
  congr 1
  funext z
  exact hf z m

/-- the periodic lift of a torus function -/
theorem lift_periodic {F : Type*} (φ : Torus d → F) (x : Euc d) (m : Lattice d) :
    φ (Torus.mk (x + Lattice.toEuc m)) = φ (Torus.mk x) := by
  rw [KernelGrad.mk_add, KernelGrad.mk_toEuc, add_zero]

/-- every point of `ℝ^d` is within the box `[-1/2,1/2]^d` of a lattice point -/
theorem exists_box_rep (p : Euc d) : ∃ m : Lattice d, ∀ i, |(p - Lattice.toEuc m) i| ≤ 1 / 2 := by
  refine ⟨fun i => round (p i), fun i => ?_⟩
  simpa [Lattice.toEuc] using abs_sub_round (p i)

/-- a continuous function on `ℝ^d` that is lattice periodic is bounded -/
theorem exists_bound_periodic {F : Type*} [NormedAddCommGroup F] {f : Euc d → F}
    (hc : Continuous f) (hf : ∀ x (m : Lattice d), f (x + Lattice.toEuc m) = f x) :
    ∃ M : ℝ, ∀ x, ‖f x‖ ≤ M := by
  have hK : IsCompact {v : Euc d | ∀ i, |v i| ≤ 1 / 2} := by
    refine (isCompact_closedBall (0 : Euc d) d).of_isClosed_subset ?_ ?_
    · have : {v : Euc d | ∀ i, |v i| ≤ 1 / 2} = ⋂ i, {v : Euc d | |v i| ≤ 1 / 2} := by
        ext v; simp
      rw [this]
      exact isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const
    · intro v hv
      rw [mem_closedBall_zero_iff]
      exact KernelGrad.norm_le_card_of_box hv
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨M, fun x => ?_⟩
  obtain ⟨m, hm⟩ := exists_box_rep x
  have := hM _ hm
  have e : f x = f (x - Lattice.toEuc m) := by
    have := hf (x - Lattice.toEuc m) m
    rwa [sub_add_cancel] at this
  rwa [e]

/-- the periodic Riesz kernel lifted to `ℝ^d` -/
def gt (d : ℕ) (s : ℝ) : Euc d → ℝ := fun y => periodicRiesz d s (Torus.mk y)

theorem gt_periodic (x : Euc d) (m : Lattice d) {s : ℝ} :
    gt d s (x + Lattice.toEuc m) = gt d s x := lift_periodic (periodicRiesz d s) x m

theorem mk_ne_zero_of_far {r : ℝ} (hr : 0 < r) {p : Euc d}
    (hp : ∀ m : Lattice d, r ≤ ‖p - Lattice.toEuc m‖) : Torus.mk p ≠ 0 := by
  intro h
  have h0 : Torus.mk p = Torus.mk (0 : Euc d) := by
    rw [h]; funext i; simp [Torus.mk]
  obtain ⟨m, hm⟩ := KernelGrad.exists_lattice_of_mk_eq h0
  have := hp m
  rw [hm] at this
  simp at this
  linarith

theorem bounded_far {F : Type*} [NormedAddCommGroup F] {f : Euc d → F}
    (hper : ∀ x (m : Lattice d), f (x + Lattice.toEuc m) = f x)
    (hc : ContinuousOn f {y : Euc d | Torus.mk y ≠ 0}) {r : ℝ} (hr : 0 < r) :
    ∃ M : ℝ, ∀ p : Euc d, (∀ m : Lattice d, r ≤ ‖p - Lattice.toEuc m‖) → ‖f p‖ ≤ M := by
  have hK : IsCompact {v : Euc d | (∀ i, |v i| ≤ 1 / 2) ∧ r ≤ ‖v‖} := by
    refine (isCompact_closedBall (0 : Euc d) d).of_isClosed_subset ?_ ?_
    · have : {v : Euc d | (∀ i, |v i| ≤ 1 / 2) ∧ r ≤ ‖v‖} =
          (⋂ i, {v : Euc d | |v i| ≤ 1 / 2}) ∩ {v : Euc d | r ≤ ‖v‖} := by
        ext v; simp
      rw [this]
      exact (isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const).inter
        (isClosed_le continuous_const continuous_norm)
    · intro v hv
      rw [mem_closedBall_zero_iff]
      exact KernelGrad.norm_le_card_of_box hv.1
  have hKU : {v : Euc d | (∀ i, |v i| ≤ 1 / 2) ∧ r ≤ ‖v‖} ⊆ {y : Euc d | Torus.mk y ≠ 0} := by
    intro v hv
    refine mk_ne_zero_of_far hr (fun m => ?_)
    exact hv.2.trans (KernelGrad.norm_sub_toEuc_ge_of_box hv.1 m)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hc.mono hKU)
  refine ⟨M, fun p hp => ?_⟩
  obtain ⟨m, hm⟩ := exists_box_rep p
  have hv : p - Lattice.toEuc m ∈ {v : Euc d | (∀ i, |v i| ≤ 1 / 2) ∧ r ≤ ‖v‖} := ⟨hm, hp m⟩
  have := hper (p - Lattice.toEuc m) m
  rw [sub_add_cancel] at this
  rw [this]
  exact hM _ hv

/-- `d ≥ 1` version of `KernelGrad.contDiffAt_periodicRiesz` (which is stated for `d ≥ 2`): the
lift of the periodic Riesz kernel is smooth away from the lattice, in every dimension `d ≥ 1`. -/
theorem contDiffAt_periodicRiesz_of_one_le {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    {y0 : Euc d} (hy0 : Torus.mk y0 ≠ 0) :
    ContDiffAt ℝ ∞' (fun y : Euc d => periodicRiesz d s (Torus.mk y)) y0 :=
  KernelD1Aux.contDiffAt_lift_g hd hs0 hsd y0 (KernelGrad.wsq_pos_of_mk_ne_zero hy0)

/-- `d ≥ 1` version of `KernelGrad.contDiffOn_periodicRiesz`. -/
theorem contDiffOn_periodicRiesz_of_one_le {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ContDiffOn ℝ ∞' (fun y : Euc d => periodicRiesz d s (Torus.mk y))
      {y : Euc d | Torus.mk y ≠ 0} :=
  fun _ hy => (contDiffAt_periodicRiesz_of_one_le hd hs0 hsd hy).contDiffWithinAt

theorem hess_far {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {r : ℝ} (hr : 0 < r) :
    ∃ M : ℝ, ∀ p : Euc d, (∀ m : Lattice d, r ≤ ‖p - Lattice.toEuc m‖) →
      ‖fderiv ℝ (fderiv ℝ (gt d s)) p‖ ≤ M := by
  have hU := KernelGrad.isOpen_mk_ne_zero (d := d)
  have h0 : ContDiffOn ℝ 3 (gt d s) {y : Euc d | Torus.mk y ≠ 0} :=
    (contDiffOn_periodicRiesz_of_one_le hd hs0 hsd (s := s)).of_le (by simp)
  have h1 := h0.fderiv_of_isOpen hU (m := 2) (by norm_num)
  have h2 := h1.fderiv_of_isOpen hU (m := 1) (by norm_num)
  have hper1 : ∀ x (m : Lattice d), fderiv ℝ (gt d s) (x + Lattice.toEuc m) = fderiv ℝ (gt d s) x :=
    fderiv_periodic (gt d s) (fun x m => gt_periodic x m)
  exact bounded_far (fun x m => fderiv_periodic (fderiv ℝ (gt d s)) hper1 x m) h2.continuousOn hr

theorem gt_bounded_far {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {r : ℝ} (hr : 0 < r) :
    ∃ M : ℝ, ∀ p : Euc d, (∀ m : Lattice d, r ≤ ‖p - Lattice.toEuc m‖) → ‖gt d s p‖ ≤ M :=
  bounded_far (fun x m => gt_periodic x m)
    ((contDiffOn_periodicRiesz_of_one_le hd hs0 hsd (s := s)).continuousOn) hr

theorem hasDerivAt_normline (y δ : Euc d) (t : ℝ) (hp : y + t • δ ≠ 0) :
    HasDerivAt (fun t : ℝ => ‖y + t • δ‖) (inner ℝ (y + t • δ) δ / ‖y + t • δ‖) t := by
  have h1 := (hasDerivAt_line y δ t).norm_sq
  have hne : ‖y + t • δ‖ ^ 2 ≠ 0 := by positivity
  have h2 := h1.sqrt hne
  have hq : 0 < ‖y + t • δ‖ := norm_pos_iff.mpr hp
  have e : (fun t : ℝ => Real.sqrt (‖y + t • δ‖ ^ 2)) = fun t : ℝ => ‖y + t • δ‖ := by
    funext t; exact Real.sqrt_sq (norm_nonneg _)
  rw [e, Real.sqrt_sq hq.le] at h2
  convert h2 using 1
  field_simp

/-- the radial singular profile: `t^{-s}` for `s > 0`, `-log t` for `s = 0` -/
def sig (s t : ℝ) : ℝ := if s = 0 then -Real.log t else t ^ (-s)

/-- normalising constant for the derivative of the radial profile -/
def sig0 (s : ℝ) : ℝ := if s = 0 then 1 else s

theorem sig0_nonneg {s : ℝ} (hs0 : 0 ≤ s) : 0 ≤ sig0 s := by
  unfold sig0; split_ifs <;> linarith

theorem hasDerivAt_sig {s : ℝ} {q : ℝ} (hq : 0 < q) :
    HasDerivAt (sig s) (-(sig0 s) * q ^ (-(s + 1))) q := by
  unfold sig sig0
  by_cases hs : s = 0
  · subst hs
    simp only [ite_true]
    have := (Real.hasDerivAt_log hq.ne').neg
    convert this using 1
    simp [Real.rpow_neg_one]
  · simp only [hs, ite_false]
    have := Real.hasDerivAt_rpow_const (x := q) (p := -s) (Or.inl hq.ne')
    convert this using 1
    ring_nf

theorem hasDerivAt_sigLine {s : ℝ} (y δ : Euc d) (t : ℝ) (hp : y + t • δ ≠ 0) :
    HasDerivAt (fun t : ℝ => sig s ‖y + t • δ‖)
      (-(sig0 s) * ‖y + t • δ‖ ^ (-(s + 2)) * inner ℝ (y + t • δ) δ) t := by
  have hq : 0 < ‖y + t • δ‖ := norm_pos_iff.mpr hp
  have h := (hasDerivAt_sig (s := s) hq).comp t (hasDerivAt_normline y δ t hp)
  refine h.congr_deriv ?_
  have : ‖y + t • δ‖ ^ (-(s + 2)) = ‖y + t • δ‖ ^ (-(s + 1)) / ‖y + t • δ‖ := by
    rw [show -(s + 2) = -(s + 1) - 1 by ring, Real.rpow_sub hq, Real.rpow_one]
  rw [this]
  ring

/-- the second derivative of the radial profile along a line -/
def sigChi (s : ℝ) (p δ : Euc d) : ℝ :=
  (-(sig0 s) * (inner ℝ p δ / ‖p‖ * (-(s + 2)) * ‖p‖ ^ (-(s + 2) - 1))) * inner ℝ p δ +
    (-(sig0 s) * ‖p‖ ^ (-(s + 2))) * inner ℝ δ δ

theorem hasDerivAt_sigLine2 {s : ℝ} (y δ : Euc d) (t : ℝ) (hp : y + t • δ ≠ 0) :
    HasDerivAt (fun t : ℝ => -(sig0 s) * ‖y + t • δ‖ ^ (-(s + 2)) * inner ℝ (y + t • δ) δ)
      (sigChi s (y + t • δ) δ) t := by
  have hq : 0 < ‖y + t • δ‖ := norm_pos_iff.mpr hp
  have h1 := (hasDerivAt_normline y δ t hp).rpow_const (p := -(s + 2)) (Or.inl hq.ne')
  have h2 := (hasDerivAt_line y δ t).inner ℝ (hasDerivAt_const t δ)
  have h3 := (h1.const_mul (-(sig0 s))).mul h2
  refine h3.congr_deriv ?_
  unfold sigChi
  simp

theorem abs_sigChi_le {s : ℝ} (hs0 : 0 ≤ s) {p : Euc d} (δ : Euc d) {ρ : ℝ} (hρ : 0 < ρ)
    (hpρ : ρ ≤ ‖p‖) :
    |sigChi s p δ| ≤ sig0 s * (s + 3) * ρ ^ (-(s + 2)) * ‖δ‖ ^ 2 := by
  have hq : 0 < ‖p‖ := lt_of_lt_of_le hρ hpρ
  have hσ := sig0_nonneg hs0
  have hc : |inner ℝ p δ| ≤ ‖p‖ * ‖δ‖ := abs_real_inner_le_norm p δ
  have hc2 : (inner ℝ p δ) ^ 2 ≤ ‖p‖ ^ 2 * ‖δ‖ ^ 2 := by
    calc (inner ℝ p δ) ^ 2 = |inner ℝ p δ| ^ 2 := (sq_abs _).symm
      _ ≤ (‖p‖ * ‖δ‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hc 2
      _ = _ := by ring
  have hqp : ‖p‖ ^ (-(s + 2)) ≤ ρ ^ (-(s + 2)) :=
    Real.rpow_le_rpow_of_nonpos hρ hpρ (by linarith)
  have hqp0 : 0 < ‖p‖ ^ (-(s + 2)) := Real.rpow_pos_of_pos hq _
  have hq1 : ‖p‖ ^ (-(s + 2) - 1) = ‖p‖ ^ (-(s + 2)) / ‖p‖ := by
    rw [Real.rpow_sub hq, Real.rpow_one]
  have hid : inner ℝ δ δ = ‖δ‖ ^ 2 := real_inner_self_eq_norm_sq δ
  -- first term
  have hT1 : |(-(sig0 s) * (inner ℝ p δ / ‖p‖ * (-(s + 2)) * ‖p‖ ^ (-(s + 2) - 1))) * inner ℝ p δ| ≤
      sig0 s * (s + 2) * ‖p‖ ^ (-(s + 2)) * ‖δ‖ ^ 2 := by
    have e : (-(sig0 s) * (inner ℝ p δ / ‖p‖ * (-(s + 2)) * ‖p‖ ^ (-(s + 2) - 1))) * inner ℝ p δ =
        sig0 s * (s + 2) * (‖p‖ ^ (-(s + 2)) / ‖p‖ ^ 2) * (inner ℝ p δ) ^ 2 := by
      rw [hq1]; field_simp
    rw [e, abs_of_nonneg (by positivity)]
    have : ‖p‖ ^ (-(s + 2)) / ‖p‖ ^ 2 * (inner ℝ p δ) ^ 2 ≤ ‖p‖ ^ (-(s + 2)) * ‖δ‖ ^ 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      calc ‖p‖ ^ (-(s + 2)) * (inner ℝ p δ) ^ 2 ≤ ‖p‖ ^ (-(s + 2)) * (‖p‖ ^ 2 * ‖δ‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hc2 hqp0.le
        _ = _ := by ring
    calc sig0 s * (s + 2) * (‖p‖ ^ (-(s + 2)) / ‖p‖ ^ 2) * (inner ℝ p δ) ^ 2
        = sig0 s * (s + 2) * (‖p‖ ^ (-(s + 2)) / ‖p‖ ^ 2 * (inner ℝ p δ) ^ 2) := by ring
      _ ≤ sig0 s * (s + 2) * (‖p‖ ^ (-(s + 2)) * ‖δ‖ ^ 2) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  have hT2 : |(-(sig0 s) * ‖p‖ ^ (-(s + 2))) * inner ℝ δ δ| = sig0 s * ‖p‖ ^ (-(s + 2)) * ‖δ‖ ^ 2 := by
    rw [hid, abs_of_nonpos (by nlinarith [mul_nonneg hσ hqp0.le, sq_nonneg ‖δ‖])]
    ring
  unfold sigChi
  calc _ ≤ |(-(sig0 s) * (inner ℝ p δ / ‖p‖ * (-(s + 2)) * ‖p‖ ^ (-(s + 2) - 1))) * inner ℝ p δ| +
        |(-(sig0 s) * ‖p‖ ^ (-(s + 2))) * inner ℝ δ δ| := abs_add_le _ _
    _ ≤ sig0 s * (s + 2) * ‖p‖ ^ (-(s + 2)) * ‖δ‖ ^ 2 + sig0 s * ‖p‖ ^ (-(s + 2)) * ‖δ‖ ^ 2 := by
        rw [hT2]; linarith
    _ = sig0 s * (s + 3) * ‖p‖ ^ (-(s + 2)) * ‖δ‖ ^ 2 := by ring
    _ ≤ _ := by
        have : 0 ≤ sig0 s * (s + 3) * ‖δ‖ ^ 2 := by positivity
        nlinarith

theorem hasDerivAt_c2line {h : Euc d → ℝ} {y δ : Euc d} {t : ℝ}
    (hc : ContDiffAt ℝ 2 h (y + t • δ)) :
    HasDerivAt (fun t : ℝ => h (y + t • δ)) (fderiv ℝ h (y + t • δ) δ) t ∧
    HasDerivAt (fun t : ℝ => fderiv ℝ h (y + t • δ) δ) (fderiv ℝ (fderiv ℝ h) (y + t • δ) δ δ) t := by
  constructor
  · have hd : DifferentiableAt ℝ h (y + t • δ) := hc.differentiableAt (by norm_num)
    exact hd.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_line y δ t)
  · have hd : DifferentiableAt ℝ (fderiv ℝ h) (y + t • δ) :=
      (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have h1 := hd.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_line y δ t)
    have h2 := (ContinuousLinearMap.apply ℝ ℝ δ).hasFDerivAt.comp_hasDerivAt t h1
    exact h2

theorem mk_ne_zero_of_box {y : Euc d} (hy : ∀ i, |y i| ≤ 1 / 2) (hy0 : y ≠ 0) : Torus.mk y ≠ 0 := by
  have hr : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  exact mk_ne_zero_of_far hr (fun m => KernelGrad.norm_sub_toEuc_ge_of_box hy m)

theorem local_sing {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ (r : Torus d → ℝ) (δ₀ : ℝ), 0 < δ₀ ∧ Torus.IsSmooth r ∧
      ∀ x : Euc d, ‖x‖ < δ₀ → x ≠ 0 → gt d s x = sig s ‖x‖ + Torus.lift r x := by
  rcases Nat.eq_or_lt_of_le hd with hd1 | hd2
  · -- `d = 1`: the local singularity comes from `HRS/Kernel/D1.lean`
    subst hd1
    have hs1 : s < 1 := by simpa using hsd
    by_cases hs : s = 0
    · subst hs
      obtain ⟨r, δ₀, h0, hr, h⟩ := periodicLog_local_singularity_d1
      refine ⟨r, δ₀, h0, hr, fun x hx hx0 => ?_⟩
      simp only [gt, sig, ite_true, Torus.lift, Function.comp]
      exact h x hx hx0
    · have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
      obtain ⟨r, δ₀, h0, hr, h⟩ := periodicRiesz_local_singularity_d1 hspos hs1
      refine ⟨r, δ₀, h0, hr, fun x hx hx0 => ?_⟩
      simp only [gt, sig, hs, ite_false, Torus.lift, Function.comp]
      exact h x hx hx0
  have hd : 2 ≤ d := hd2
  by_cases hs : s = 0
  · subst hs
    obtain ⟨r, δ₀, h0, hr, h⟩ := periodicLog_local_singularity (d := d) hd
    refine ⟨r, δ₀, h0, hr, fun x hx hx0 => ?_⟩
    simp only [gt, sig, ite_true, Torus.lift, Function.comp]
    exact h x hx hx0
  · have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
    obtain ⟨r, δ₀, h0, hr, h⟩ := periodicRiesz_local_singularity (d := d) hd hspos hsd
    refine ⟨r, δ₀, h0, hr, fun x hx hx0 => ?_⟩
    simp only [gt, sig, hs, ite_false, Torus.lift, Function.comp]
    exact h x hx hx0

theorem hess_smooth_bound {r : Torus d → ℝ} (hr : Torus.IsSmooth r) :
    ∃ M : ℝ, ∀ p : Euc d, ‖fderiv ℝ (fderiv ℝ (Torus.lift r)) p‖ ≤ M := by
  have hr' : ContDiff ℝ ∞' (Torus.lift r) := hr
  have h3 : ContDiff ℝ 3 (Torus.lift r) := hr'.of_le (by simp)
  have h1 := h3.fderiv_right (m := 2) (by norm_num)
  have h2 := h1.fderiv_right (m := 1) (by norm_num)
  have hper1 : ∀ x (m : Lattice d), fderiv ℝ (Torus.lift r) (x + Lattice.toEuc m) =
      fderiv ℝ (Torus.lift r) x :=
    fderiv_periodic (Torus.lift r) (fun x m => lift_periodic r x m)
  refine exists_bound_periodic h2.continuous ?_
  intro x m
  exact fderiv_periodic (fderiv ℝ (Torus.lift r)) hper1 x m

theorem norm_line_bounds {y δ : Euc d} (hδ : ‖δ‖ ≤ ‖y‖ / 2) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖y‖ / 2 ≤ ‖y + t • δ‖ ∧ ‖y + t • δ‖ ≤ 3 * ‖y‖ / 2 := by
  have h1 : ‖t • δ‖ ≤ ‖δ‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact mul_le_of_le_one_left (norm_nonneg _) ht.2
  constructor
  · have : ‖y‖ ≤ ‖y + t • δ‖ + ‖t • δ‖ := by
      have := norm_sub_le (y + t • δ) (t • δ)
      rwa [add_sub_cancel_right] at this
    linarith
  · have := norm_add_le y (t • δ)
    linarith

theorem far_cond {y δ : Euc d} (hy : ∀ i, |y i| ≤ 1 / 2) (hδ : ‖δ‖ ≤ ‖y‖ / 2) {t : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) (m : Lattice d) : ‖y‖ / 2 ≤ ‖y + t • δ - Lattice.toEuc m‖ := by
  have h1 : ‖t • δ‖ ≤ ‖δ‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact mul_le_of_le_one_left (norm_nonneg _) ht.2
  have h2 := KernelGrad.norm_sub_toEuc_ge_of_box hy m
  have h3 : ‖y - Lattice.toEuc m‖ ≤ ‖y + t • δ - Lattice.toEuc m‖ + ‖t • δ‖ := by
    have := norm_sub_le (y + t • δ - Lattice.toEuc m) (t • δ)
    rwa [show y + t • δ - Lattice.toEuc m - t • δ = y - Lattice.toEuc m by abel] at this
  linarith

theorem taylor_gt {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y δ : Euc d, (∀ i, |y i| ≤ 1 / 2) → y ≠ 0 → ‖δ‖ ≤ ‖y‖ / 2 →
      |gt d s (y + δ) - gt d s y - fderiv ℝ (gt d s) y δ| ≤
        C * ‖δ‖ ^ 2 * (‖y‖ ^ (-(s + 2)) + 1) := by
  obtain ⟨r, δ₀, hδ₀, hr, hrep⟩ := local_sing (s := s) hd hs0 hsd
  obtain ⟨Mr, hMr⟩ := hess_smooth_bound hr
  obtain ⟨Mf, hMf⟩ := hess_far hd hs0 hsd (r := δ₀ / 4) (by positivity)
  have hσ := sig0_nonneg hs0
  refine ⟨sig0 s * (s + 3) * 2 ^ (s + 2) + |Mr| + |Mf|, by positivity, fun y δ hy hy0 hδ => ?_⟩
  have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  have hyp : 0 ≤ ‖y‖ ^ (-(s + 2)) := Real.rpow_nonneg hyn.le _
  have hmk := mk_ne_zero_of_box hy hy0
  have hgy2 : ContDiffAt ℝ 2 (gt d s) y :=
    (contDiffAt_periodicRiesz_of_one_le hd hs0 hsd (y0 := y) hmk).of_le (by simp)
  have hgy : DifferentiableAt ℝ (gt d s) y := hgy2.differentiableAt (by norm_num)
  by_cases hnear : ‖y‖ < δ₀ / 2
  · -- near the singularity
    set W : Set ℝ := {t : ℝ | 0 < ‖y + t • δ‖ ∧ ‖y + t • δ‖ < δ₀} with hW
    have hWo : IsOpen W := by
      have hc : Continuous fun t : ℝ => ‖y + t • δ‖ := by fun_prop
      exact (isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)
    have hWI : ∀ t ∈ Icc (0:ℝ) 1, t ∈ W := by
      intro t ht
      obtain ⟨h1, h2⟩ := norm_line_bounds hδ ht
      exact ⟨by linarith, by linarith⟩
    have hline : ∀ t ∈ Icc (0:ℝ) 1, y + t • δ ≠ 0 := fun t ht h => by
      have := (hWI t ht).1; rw [h] at this; simp at this
    have hφ : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt (fun t : ℝ => gt d s (y + t • δ))
        (-(sig0 s) * ‖y + t • δ‖ ^ (-(s + 2)) * inner ℝ (y + t • δ) δ +
          fderiv ℝ (Torus.lift r) (y + t • δ) δ) t := by
      intro t ht
      have hrc : ContDiffAt ℝ 2 (Torus.lift r) (y + t • δ) := by
        have hr' : ContDiff ℝ ∞' (Torus.lift r) := hr
        exact (hr'.of_le (by simp)).contDiffAt
      have h1 := hasDerivAt_sigLine (s := s) y δ t (hline t ht)
      have h2 := (hasDerivAt_c2line (y := y) (δ := δ) hrc).1
      refine (h1.add h2).congr_of_eventuallyEq ?_
      filter_upwards [hWo.mem_nhds (hWI t ht)] with u hu
      have := hrep (y + u • δ) hu.2 (norm_pos_iff.mp hu.1)
      simpa using this
    have hψ : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt
        (fun t : ℝ => -(sig0 s) * ‖y + t • δ‖ ^ (-(s + 2)) * inner ℝ (y + t • δ) δ +
          fderiv ℝ (Torus.lift r) (y + t • δ) δ)
        (sigChi s (y + t • δ) δ + fderiv ℝ (fderiv ℝ (Torus.lift r)) (y + t • δ) δ δ) t := by
      intro t ht
      have hrc : ContDiffAt ℝ 2 (Torus.lift r) (y + t • δ) := by
        have hr' : ContDiff ℝ ∞' (Torus.lift r) := hr
        exact (hr'.of_le (by simp)).contDiffAt
      exact (hasDerivAt_sigLine2 (s := s) y δ t (hline t ht)).add
        (hasDerivAt_c2line (y := y) (δ := δ) hrc).2
    have hχ : ∀ t ∈ Icc (0:ℝ) 1,
        |sigChi s (y + t • δ) δ + fderiv ℝ (fderiv ℝ (Torus.lift r)) (y + t • δ) δ δ| ≤
          (sig0 s * (s + 3) * (‖y‖ / 2) ^ (-(s + 2)) + Mr) * ‖δ‖ ^ 2 := by
      intro t ht
      obtain ⟨h1, -⟩ := norm_line_bounds hδ ht
      have hA := abs_sigChi_le (s := s) hs0 δ (by positivity : 0 < ‖y‖ / 2) h1
      have hB : |fderiv ℝ (fderiv ℝ (Torus.lift r)) (y + t • δ) δ δ| ≤ Mr * ‖δ‖ ^ 2 := by
        calc _ ≤ ‖fderiv ℝ (fderiv ℝ (Torus.lift r)) (y + t • δ)‖ * ‖δ‖ * ‖δ‖ := by
              rw [← Real.norm_eq_abs]; exact ContinuousLinearMap.le_opNorm₂ _ _ _
          _ ≤ Mr * ‖δ‖ * ‖δ‖ := by gcongr; exact hMr _
          _ = _ := by ring
      calc _ ≤ _ := abs_add_le _ _
        _ ≤ _ := add_le_add hA hB
        _ = _ := by ring
    have key := taylor1 hφ hψ hχ
    simp only [one_smul, zero_smul, add_zero] at key
    -- identify the first-order term
    have hder : HasDerivAt (fun t : ℝ => gt d s (y + t • δ)) (fderiv ℝ (gt d s) y δ) 0 := by
      have hg0 : DifferentiableAt ℝ (gt d s) (y + (0:ℝ) • δ) := by simpa using hgy
      have := hg0.hasFDerivAt.comp_hasDerivAt (0:ℝ) (hasDerivAt_line y δ 0)
      simp only [zero_smul, add_zero] at this
      exact this
    have hψ0 := hφ 0 ⟨le_rfl, zero_le_one⟩
    simp only [zero_smul, add_zero] at hψ0
    have heq := hψ0.unique hder
    rw [heq] at key
    have e2 : (‖y‖ / 2) ^ (-(s + 2)) = 2 ^ (s + 2) * ‖y‖ ^ (-(s + 2)) := by
      rw [Real.div_rpow hyn.le (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
        div_inv_eq_mul, mul_comm]
    rw [e2] at key
    refine key.trans ?_
    have hd2 : 0 ≤ ‖δ‖ ^ 2 := by positivity
    have h2p : 0 ≤ (2:ℝ) ^ (s + 2) := by positivity
    have hK0 : 0 ≤ sig0 s * (s + 3) * 2 ^ (s + 2) := by positivity
    have hle : sig0 s * (s + 3) * (2 ^ (s + 2) * ‖y‖ ^ (-(s + 2))) + Mr ≤
        (sig0 s * (s + 3) * 2 ^ (s + 2) + |Mr| + |Mf|) * (‖y‖ ^ (-(s + 2)) + 1) := by
      nlinarith [mul_nonneg (abs_nonneg Mr) hyp, mul_nonneg (abs_nonneg Mf) hyp,
        abs_nonneg Mf, neg_abs_le Mr, le_abs_self Mr]
    calc _ ≤ ((sig0 s * (s + 3) * 2 ^ (s + 2) + |Mr| + |Mf|) * (‖y‖ ^ (-(s + 2)) + 1)) * ‖δ‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hle hd2
      _ = _ := by ring
  · -- away from the singularity
    have hnear' : δ₀ / 2 ≤ ‖y‖ := not_lt.mp hnear
    have hcd : ∀ t ∈ Icc (0:ℝ) 1, ContDiffAt ℝ 2 (gt d s) (y + t • δ) := by
      intro t ht
      have hmk' : Torus.mk (y + t • δ) ≠ 0 := by
        refine mk_ne_zero_of_far (r := δ₀ / 4) (by positivity) (fun m => ?_)
        have := far_cond hy hδ ht m
        linarith
      exact (contDiffAt_periodicRiesz_of_one_le hd hs0 hsd hmk').of_le (by simp)
    have hM : ∀ t ∈ Icc (0:ℝ) 1, ‖fderiv ℝ (fderiv ℝ (gt d s)) (y + t • δ)‖ ≤ Mf := by
      intro t ht
      refine hMf _ (fun m => ?_)
      have := far_cond hy hδ ht m
      linarith
    have key := taylor2 hcd hM
    refine key.trans ?_
    have hd2 : 0 ≤ ‖δ‖ ^ 2 := by positivity
    have hK0 : 0 ≤ sig0 s * (s + 3) * 2 ^ (s + 2) := by positivity
    have hle : Mf ≤ (sig0 s * (s + 3) * 2 ^ (s + 2) + |Mr| + |Mf|) * (‖y‖ ^ (-(s + 2)) + 1) := by
      nlinarith [mul_nonneg (abs_nonneg Mr) hyp, mul_nonneg (abs_nonneg Mf) hyp,
        mul_nonneg hK0 hyp, abs_nonneg Mr, le_abs_self Mf]
    calc _ ≤ ((sig0 s * (s + 3) * 2 ^ (s + 2) + |Mr| + |Mf|) * (‖y‖ ^ (-(s + 2)) + 1)) * ‖δ‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hle hd2
      _ = _ := by ring

/-- the torus distance to the origin -/
def rho (z : Torus d) : ℝ := ‖KernelGrad.centeredRep z‖

theorem rho_nonneg (z : Torus d) : 0 ≤ rho z := norm_nonneg _

theorem rho_le (z : Torus d) : rho z ≤ d := KernelGrad.norm_le_card_of_box (KernelGrad.abs_centeredRep_le z)

theorem centeredRep_ne_zero {z : Torus d} (hz : z ≠ 0) : KernelGrad.centeredRep z ≠ 0 := by
  intro h
  apply hz
  rw [← KernelGrad.mk_centeredRep z, h]
  funext i; simp [Torus.mk]

theorem rho_pos {z : Torus d} (hz : z ≠ 0) : 0 < rho z :=
  norm_pos_iff.mpr (centeredRep_ne_zero hz)

theorem rho_neg (z : Torus d) : rho (-z) = rho z := by
  have h := KernelGrad.tdist_neg z
  rw [KernelGrad.tdist_zero_right, KernelGrad.tdist_zero_right] at h
  exact h

theorem fderiv_gt_apply {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {y : Euc d}
    (hy : Torus.mk y ≠ 0) (δ : Euc d) :
    fderiv ℝ (gt d s) y δ = inner ℝ (periodicRieszGrad d s (Torus.mk y)) δ := by
  rcases Nat.eq_or_lt_of_le hd with hd1 | hd2
  · -- `d = 1`: reduce to the one-variable derivative `KernelD1Aux.hasDerivAt_g_ev`
    subst hd1
    have hs1 : s < 1 := by simpa using hsd
    have hoff := KernelD1Aux.off_int_of_mk_ne hy
    have hder := KernelD1Aux.hasDerivAt_g_ev hs0 hs1 hoff
    have hdiff : DifferentiableAt ℝ (gt 1 s) y :=
      (contDiffAt_periodicRiesz_of_one_le le_rfl hs0 hsd hy).differentiableAt (by simp)
    have hline : HasDerivAt (fun t : ℝ => gt 1 s (y + t • δ)) (fderiv ℝ (gt 1 s) y δ) 0 := by
      have hd0 : DifferentiableAt ℝ (gt 1 s) (y + (0 : ℝ) • δ) := by simpa using hdiff
      have := hd0.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_line y δ 0)
      simp only [zero_smul, add_zero] at this
      exact this
    have hlin : (fun t : ℝ => gt 1 s (y + t • δ)) =
        (fun u : ℝ => periodicRiesz 1 s (Torus.mk (KernelD1Aux.ev u))) ∘
          fun t : ℝ => y 0 + t * δ 0 := by
      funext t
      have e : y + t • δ = KernelD1Aux.ev (y 0 + t * δ 0) := by
        have := KernelD1Aux.ev_eq (y + t • δ)
        simpa using this
      simp only [Function.comp, gt]
      rw [e]
    have hcomp : HasDerivAt (fun t : ℝ => gt 1 s (y + t • δ))
        ((periodicRieszGrad 1 s (Torus.mk (KernelD1Aux.ev (y 0)))) 0 * δ 0) 0 := by
      rw [hlin]
      have h1 : HasDerivAt (fun t : ℝ => y 0 + t * δ 0) (δ 0) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (δ 0)).const_add (y 0)
      have h2 : HasDerivAt (fun u : ℝ => periodicRiesz 1 s (Torus.mk (KernelD1Aux.ev u)))
          ((periodicRieszGrad 1 s (Torus.mk (KernelD1Aux.ev (y 0)))) 0) (y 0 + 0 * δ 0) := by
        simpa using hder
      have := h2.comp (0 : ℝ) h1
      simpa [mul_comm] using this
    have e := hline.unique hcomp
    rw [e, ← KernelD1Aux.ev_eq y]
    simp [PiLp.inner_apply, mul_comm]
  have hd' : 2 ≤ d := hd2
  have h := KernelGrad.lift_periodicRieszGrad_eq_gradient hd' hs0 hsd hy
  have h2 : periodicRieszGrad d s (Torus.mk y) =
      (InnerProductSpace.toDual ℝ (Euc d)).symm (fderiv ℝ (gt d s) y) := h
  rw [h2, InnerProductSpace.toDual_symm_apply]

theorem taylor_torus {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : Torus d) (δ : Euc d), z ≠ 0 → ‖δ‖ ≤ rho z / 2 →
      |periodicRiesz d s (z + Torus.mk δ) - periodicRiesz d s z -
          inner ℝ (periodicRieszGrad d s z) δ| ≤
        C * ‖δ‖ ^ 2 * (rho z ^ (-(s + 2)) + 1) := by
  obtain ⟨C, hC0, hC⟩ := taylor_gt (s := s) hd hs0 hsd
  refine ⟨C, hC0, fun z δ hz hδ => ?_⟩
  have hy0 := centeredRep_ne_zero hz
  have hbox := KernelGrad.abs_centeredRep_le z
  have hmk := KernelGrad.mk_centeredRep z
  have := hC (KernelGrad.centeredRep z) δ hbox hy0 hδ
  have hmk0 : Torus.mk (KernelGrad.centeredRep z) ≠ 0 := by rwa [hmk]
  rw [fderiv_gt_apply hd hs0 hsd hmk0, hmk] at this
  simp only [gt, KernelGrad.mk_add, hmk] at this
  exact this

theorem lipschitz_a {a : Torus d → Euc d} (ha : Torus.IsSmooth a) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : Torus d, ‖a x - a y‖ ≤ L * rho (x - y) := by
  have ha' : ContDiff ℝ ∞' (Torus.lift a) := ha
  have hc : Continuous (fderiv ℝ (Torus.lift a)) := ha'.continuous_fderiv (by simp)
  have hper : ∀ x (m : Lattice d), fderiv ℝ (Torus.lift a) (x + Lattice.toEuc m) =
      fderiv ℝ (Torus.lift a) x :=
    fderiv_periodic (Torus.lift a) (fun x m => lift_periodic a x m)
  obtain ⟨L, hL⟩ := exists_bound_periodic hc hper
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  refine ⟨L, hL0, fun x y => ?_⟩
  set p := KernelGrad.centeredRep x with hp
  set c := KernelGrad.centeredRep (x - y) with hcdef
  have hq : Torus.mk (p - c) = y := by
    rw [KernelGrad.mk_sub, hp, hcdef, KernelGrad.mk_centeredRep, KernelGrad.mk_centeredRep, sub_sub_cancel]
  have hpx : Torus.mk p = x := KernelGrad.mk_centeredRep x
  have key := Convex.norm_image_sub_le_of_norm_fderiv_le (f := Torus.lift a) (s := Set.univ)
    (C := L) (fun z _ => (ha'.differentiable (by simp)) z) (fun z _ => hL z) convex_univ
    (Set.mem_univ (p - c)) (Set.mem_univ p)
  have e1 : Torus.lift a p = a x := by simp [Torus.lift, hpx]
  have e2 : Torus.lift a (p - c) = a y := by simp [Torus.lift, hq]
  rw [e1, e2, sub_sub_cancel] at key
  simpa [rho, hcdef] using key

theorem rpow_neg_le_add {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : Torus d, z ≠ 0 → rho z ^ (-s) ≤ periodicRiesz d s z + K := by
  obtain ⟨r, δ₀, hδ₀, hr, hrep⟩ := local_sing (s := s) hd hs0 hsd
  have hr' : ContDiff ℝ ∞' (Torus.lift r) := hr
  obtain ⟨R, hR⟩ := exists_bound_periodic hr'.continuous (fun x m => lift_periodic r x m)
  obtain ⟨B, hB⟩ := gt_bounded_far hd hs0 hsd (r := δ₀ / 2) (by positivity)
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR 0)
  have hδ2 : 0 < δ₀ / 2 := by positivity
  refine ⟨R + |Real.log (δ₀ / 2)| + 1 + (δ₀ / 2) ^ (-s) + |B|, by positivity, fun z hz => ?_⟩
  set y := KernelGrad.centeredRep z with hy
  have hy0 : y ≠ 0 := centeredRep_ne_zero hz
  have hbox := KernelGrad.abs_centeredRep_le z
  have hmk : Torus.mk y = z := KernelGrad.mk_centeredRep z
  have hgz : periodicRiesz d s z = gt d s y := by simp [gt, hmk]
  have hρ : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  have hrho : rho z = ‖y‖ := rfl
  rw [hgz, hrho]
  have hp0 : 0 ≤ (δ₀ / 2) ^ (-s) := Real.rpow_nonneg hδ2.le _
  by_cases hnear : ‖y‖ < δ₀ / 2
  · have h1 := hrep y (by linarith) hy0
    have hr1 := (abs_le.mp (by simpa using hR y : |Torus.lift r y| ≤ R))
    by_cases hs : s = 0
    · subst hs
      simp only [sig, ite_true] at h1
      rw [h1]
      simp only [neg_zero, Real.rpow_zero]
      have hlog : Real.log ‖y‖ ≤ Real.log (δ₀ / 2) := Real.log_le_log hρ hnear.le
      have := neg_abs_le (Real.log (δ₀ / 2))
      have := le_abs_self (Real.log (δ₀ / 2))
      have := abs_nonneg B
      linarith [hr1.1, hr1.2]
    · rw [h1]
      simp only [sig, hs, ite_false]
      have := abs_nonneg B
      have := abs_nonneg (Real.log (δ₀ / 2))
      linarith [hr1.1, hr1.2]
  · have hfar : δ₀ / 2 ≤ ‖y‖ := not_lt.mp hnear
    have hb := hB y (fun m => hfar.trans (KernelGrad.norm_sub_toEuc_ge_of_box hbox m))
    have hb' := (abs_le.mp (by simpa using hb : |gt d s y| ≤ B))
    have hpow : ‖y‖ ^ (-s) ≤ (δ₀ / 2) ^ (-s) :=
      Real.rpow_le_rpow_of_nonpos hδ2 hfar (by linarith)
    have := abs_nonneg (Real.log (δ₀ / 2))
    have := le_abs_self B
    linarith [hb'.1]


/-- two lattice-type circle points coincide iff the integers agree mod `n` -/
theorem circle_eq_iff {n : ℕ} (hn : 0 < n) (p q : ℤ) :
    (((p : ℝ) / n : ℝ) : UnitAddCircle) = (((q : ℝ) / n : ℝ) : UnitAddCircle) ↔ (n : ℤ) ∣ p - q := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have : ((p - q : ℤ) : ℝ) = (n : ℝ) * m := by
      push_cast
      field_simp at hm ⊢
      simp only [zsmul_eq_mul, mul_one] at hm
      linarith
    have h : ((p - q : ℤ) : ℝ) = ((n * m : ℤ) : ℝ) := by push_cast at this ⊢; linarith
    exact_mod_cast h
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have : ((p - q : ℤ) : ℝ) = (n : ℝ) * m := by exact_mod_cast hm
    simp only [zsmul_eq_mul, mul_one]
    push_cast at this
    field_simp
    linarith

theorem latticePoint_apply (n : ℕ) (j : Fin d → Fin n) (c : Fin d) :
    latticePoint n j c = ((((((j c : ℕ) : ℤ)) : ℝ) / n : ℝ) : UnitAddCircle) := by
  simp [latticePoint]

theorem latticePoint_injective {n : ℕ} (hn : 0 < n) :
    Function.Injective (latticePoint (d := d) n) := by
  intro j j' h
  funext c
  have h1 := congrFun h c
  rw [latticePoint_apply, latticePoint_apply, circle_eq_iff hn] at h1
  obtain ⟨t, ht⟩ := h1
  have h2 := (j c).2
  have h3 := (j' c).2
  apply Fin.ext
  have h4 : ((j c : ℕ) : ℤ) - (j' c : ℕ) = n * t := ht
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have h5 : (t = 0) := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h6 | h6
    · nlinarith
    · nlinarith
  rw [h5] at h4
  omega

theorem latticePoint_reflect {n : ℕ} (hn : 0 < n) (i j : Fin d → Fin n) :
    ∃ k : Fin d → Fin n, latticePoint n k = latticePoint n i + latticePoint n i - latticePoint n j := by
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have key : ∀ c : Fin d, ∃ r : Fin n, latticePoint n (fun _ => r) c =
      latticePoint n i c + latticePoint n i c - latticePoint n j c := by
    intro c
    set x : ℤ := 2 * ((i c : ℕ) : ℤ) - ((j c : ℕ) : ℤ) with hx
    have hr0 : 0 ≤ x % n := Int.emod_nonneg _ hn'.ne'
    have hr1 : x % n < n := Int.emod_lt_of_pos _ hn'
    refine ⟨⟨(x % n).toNat, by omega⟩, ?_⟩
    rw [latticePoint_apply]
    have e1 : latticePoint n i c + latticePoint n i c - latticePoint n j c =
        (((x : ℝ) / n : ℝ) : UnitAddCircle) := by
      rw [latticePoint_apply, latticePoint_apply]
      rw [← AddCircle.coe_add, ← AddCircle.coe_sub]
      congr 1
      simp only [hx]; push_cast; ring
    rw [e1, circle_eq_iff hn]
    simp only [Fin.val_mk]
    refine ⟨-(x / n), ?_⟩
    have := Int.emod_def x n
    have h2 : (((x % n).toNat : ℕ) : ℤ) = x % n := Int.toNat_of_nonneg hr0
    rw [h2]
    linarith
  choose r hr using key
  refine ⟨fun c => r c, ?_⟩
  funext c
  have := hr c
  rw [latticePoint_apply] at this ⊢
  simpa [latticePoint_apply] using this

open Complex in
theorem sum_exp_fin {n : ℕ} (hn : 0 < n) (m : ℤ) :
    ∑ a : Fin n, Complex.exp (2 * Real.pi * Complex.I * (m : ℤ) * ((((a : ℕ) : ℝ) / n : ℝ) : ℂ)) =
      if (n : ℤ) ∣ m then (n : ℂ) else 0 := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I * (m : ℤ) / n) with hζ
  have hterm : ∀ a : Fin n, Complex.exp (2 * Real.pi * Complex.I * (m : ℤ) * ((((a : ℕ) : ℝ) / n : ℝ) : ℂ)) =
      ζ ^ (a : ℕ) := by
    intro a
    rw [hζ, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  simp_rw [hterm]
  rw [Fin.sum_univ_eq_sum_range (fun a => ζ ^ a) n]
  split_ifs with hdiv
  · obtain ⟨t, ht⟩ := hdiv
    have : ζ = 1 := by
      rw [hζ, Complex.exp_eq_one_iff]
      refine ⟨t, ?_⟩
      rw [ht]; push_cast; field_simp
    rw [this]; simp
  · have hne : ζ ≠ 1 := by
      intro h
      rw [hζ, Complex.exp_eq_one_iff] at h
      obtain ⟨t, ht⟩ := h
      apply hdiv
      refine ⟨t, ?_⟩
      have : (m : ℂ) = n * t := by
        field_simp at ht
        exact ht
      exact_mod_cast this
    have hpow : ζ ^ n = 1 := by
      rw [hζ, ← Complex.exp_nat_mul]
      have : (n : ℂ) * (2 * Real.pi * Complex.I * (m : ℤ) / n) = (m : ℤ) * (2 * Real.pi * Complex.I) := by
        field_simp
      rw [this, Complex.exp_int_mul_two_pi_mul_I]
    rw [geom_sum_eq hne, hpow]; simp

theorem sum_mode_lattice {n : ℕ} (hn : 0 < n) (k : Lattice d) :
    ∑ j : Fin d → Fin n, Torus.mode k (latticePoint n j) =
      if (∀ c, (n : ℤ) ∣ k c) then ((n : ℂ) ^ d) else 0 := by
  have h1 : ∀ j : Fin d → Fin n, Torus.mode k (latticePoint n j) =
      ∏ c, Complex.exp (2 * Real.pi * Complex.I * (k c : ℤ) * ((((j c : ℕ) : ℝ) / n : ℝ) : ℂ)) := by
    intro j
    exact mode_eq_prod k (fun c => (((j c : ℕ) : ℝ) / n : ℝ))
  simp_rw [h1]
  have h2 := Finset.prod_univ_sum (fun _ : Fin d => (Finset.univ : Finset (Fin n)))
    (fun c a => Complex.exp (2 * Real.pi * Complex.I * (k c : ℤ) * ((((a : ℕ) : ℝ) / n : ℝ) : ℂ)))
  rw [Fintype.piFinset_univ] at h2
  rw [← h2]
  simp_rw [sum_exp_fin hn]
  rw [Finset.prod_ite_zero]
  simp

/-- the lattice configuration `Λ_N`, `N = n^d` -/
def latCfg (n : ℕ) : Config d (n ^ d) := fun j => latticePoint n (finFunctionFinEquiv.symm j)

theorem latCfg_injective {n : ℕ} (hn : 0 < n) : Function.Injective (latCfg (d := d) n) := by
  intro i j h
  have := latticePoint_injective hn h
  exact finFunctionFinEquiv.symm.injective this

theorem latCfg_reflect {n : ℕ} (hn : 0 < n) (i j : Fin (n ^ d)) :
    ∃ k : Fin (n ^ d), latCfg n k = latCfg n i + latCfg n i - latCfg n j := by
  obtain ⟨k, hk⟩ := latticePoint_reflect hn (finFunctionFinEquiv.symm i) (finFunctionFinEquiv.symm j)
  refine ⟨finFunctionFinEquiv k, ?_⟩
  simpa [latCfg] using hk

theorem sum_mode_latCfg {n : ℕ} (hn : 0 < n) (k : Lattice d) :
    ∑ i, Torus.mode k (latCfg n i) = if (∀ c, (n : ℤ) ∣ k c) then ((n : ℂ) ^ d) else 0 := by
  rw [← sum_mode_lattice hn k]
  exact Equiv.sum_comp finFunctionFinEquiv.symm (fun j => Torus.mode k (latticePoint n j))

open CoercAux in
theorem gT_lattice_sum {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ε : ℝ} (hε : 0 < ε)
    {n : ℕ} (hn : 0 < n) :
    (1 / ((n ^ d : ℕ) : ℝ) ^ 2) * ∑ i, ∑ j, gT d s ε (latCfg n i - latCfg n j) =
      ∑' k : Lattice d, cT d s ε k * (if (∀ c, (n : ℤ) ∣ k c) then 1 else 0) := by
  haveI : (volume : Measure (Torus d)).IsNegInvariant :=
    MeasureTheory.Measure.pi.isNegInvariant (fun _ : Fin d => (volume : Measure UnitAddCircle))
  have hN : 0 < n ^ d := by positivity
  have hc : Summable fun k => |cT d s ε k| := (summable_cT hd hs0 hsd hε).abs
  have hQ := Q_eq_tsum hN hc (latCfg n) (volume : Measure (Torus d))
  have hI : ∀ x : Torus d, ∫ y, trigSum (cT d s ε) (x - y) ∂(volume : Measure (Torus d)) = 0 := by
    intro x
    have := integral_sub_left_eq_self (fun z => gT d s ε z) (volume : Measure (Torus d)) x
    have h0 := integral_gT hd hs0 hsd hε (s := s) (d := d)
    exact this.trans h0
  simp only [hI, integral_zero, Finset.sum_const_zero, mul_zero, sub_zero, add_zero] at hQ
  refine Eq.trans hQ (tsum_congr fun k => ?_)
  by_cases hk : k = 0
  · simp [cT, hk]
  · have hint : ∫ x, Torus.mode k x ∂(volume : Measure (Torus d)) = 0 := by
      rw [Torus.integral_mode]; simp [hk]
    rw [hint, sub_zero, sum_mode_latCfg hn k]
    split_ifs with h
    · have : ((((n ^ d : ℕ) : ℝ)⁻¹ : ℝ)) • ((n : ℂ) ^ d) = 1 := by
        rw [Complex.real_smul]
        have : (((n ^ d : ℕ) : ℝ) : ℂ) = (n : ℂ) ^ d := by push_cast; rfl
        have hn0 : ((n : ℂ) ^ d) ≠ 0 := by
          have : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
          exact pow_ne_zero _ this
        push_cast
        field_simp
      rw [this]; simp
    · simp

theorem toEuc_nsmul (n : ℕ) (m : Lattice d) :
    Lattice.toEuc ((n : ℤ) • m) = (n : ℝ) • Lattice.toEuc m := by
  ext i; simp [Lattice.toEuc]

theorem enorm_nsmul (n : ℕ) (m : Lattice d) :
    Lattice.enorm ((n : ℤ) • m) = (n : ℝ) * Lattice.enorm m := by
  unfold Lattice.enorm
  rw [toEuc_nsmul, norm_smul, Real.norm_natCast]

open CoercAux KernelAux Set in
theorem cT_scale {s : ℝ} {n : ℕ} (hn : 0 < n) (m : Lattice d) (hm : m ≠ 0) :
    cT d s (1 / (n : ℝ) ^ 2) ((n : ℤ) • m) =
      subA d s * (((n : ℝ) ^ 2) ^ (-(((d : ℝ) - s) / 2))) *
        ∫ v in Ioi (1 : ℝ), v ^ (((d : ℝ) - s) / 2 - 1) * Real.exp (-(Lattice.enorm m ^ 2 * v)) := by
  set a : ℝ := ((d : ℝ) - s) / 2 with ha
  set b : ℝ := (n : ℝ) ^ 2 with hb
  have hb0 : 0 < b := by positivity
  have hnm : ((n : ℤ) • m) ≠ 0 := by
    intro h
    apply hm
    funext c
    have := congrFun h c
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
    exact (mul_eq_zero.mp this).resolve_left hn'
  unfold cT
  rw [if_neg hnm, enorm_nsmul, mul_assoc]
  congr 1
  set g : ℝ → ℝ := fun v => v ^ (a - 1) * Real.exp (-(Lattice.enorm m ^ 2 * v)) with hg
  have hF : ∀ u ∈ Ioi (1 / b), u ^ (a - 1) * Real.exp (-(((n : ℝ) * Lattice.enorm m) ^ 2 * u)) =
      b ^ (-(a - 1)) * g (b * u) := by
    intro u hu
    have hu0 : 0 < u := lt_trans (by positivity) hu
    simp only [hg]
    rw [Real.mul_rpow hb0.le hu0.le, ← mul_assoc, ← mul_assoc, ← Real.rpow_add hb0]
    · have : b ^ (-(a - 1) + (a - 1)) = 1 := by simp
      rw [this, one_mul]
      congr 2
      rw [mul_pow, hb]; ring
  rw [setIntegral_congr_fun measurableSet_Ioi hF, integral_const_mul,
    integral_comp_mul_left_Ioi g (1 / b) hb0, mul_one_div_cancel hb0.ne']
  rw [smul_eq_mul, ← mul_assoc]
  have : b ^ (-(a - 1)) * b⁻¹ = b ^ (-a) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hb0]; congr 1; ring
  rw [this]

open CoercAux KernelAux Set in
theorem cT_lattice_le {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {n : ℕ} (hn : 0 < n)
    (m : Lattice d) (hm : m ≠ 0) :
    cT d s (1 / (n : ℝ) ^ 2) ((n : ℤ) • m) ≤
      subA d s * halfInt (((d : ℝ) - s) / 2) * (n : ℝ) ^ (s - d) * Real.exp (-(1 / 2) * Lattice.enorm m ^ 2) := by
  have ha : 0 < ((d : ℝ) - s) / 2 := by linarith
  have hA := subA_nonneg_one hd hs0 hsd
  rw [cT_scale hn m hm]
  have h1 := intT_le ha (ε := 1) one_pos m hm
  have hb : (((n : ℝ) ^ 2) ^ (-(((d : ℝ) - s) / 2))) = (n : ℝ) ^ (s - d) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1; push_cast; ring
  rw [hb]
  have hn0 : 0 ≤ (n : ℝ) ^ (s - d) := by positivity
  have h2 : -(1 / 2 : ℝ) * Lattice.enorm m ^ 2 = -((1:ℝ) / 2) * Lattice.enorm m ^ 2 := by ring
  calc subA d s * (n : ℝ) ^ (s - d) * ∫ v in Ioi (1 : ℝ), v ^ (((d : ℝ) - s) / 2 - 1) *
        Real.exp (-(Lattice.enorm m ^ 2 * v))
      ≤ subA d s * (n : ℝ) ^ (s - d) * (Real.exp (-((1:ℝ) / 2) * Lattice.enorm m ^ 2) *
          halfInt (((d : ℝ) - s) / 2)) := by
        refine mul_le_mul_of_nonneg_left h1 (mul_nonneg hA hn0)
    _ = _ := by rw [h2]; ring

open CoercAux KernelAux Set in
theorem esq_lattice_bound {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n →
      ∑' k : Lattice d, cT d s (1 / (n : ℝ) ^ 2) k * (if (∀ c, (n : ℤ) ∣ k c) then 1 else 0) ≤
        C * (n : ℝ) ^ (s - d) := by
  have hA := subA_nonneg_one hd hs0 hsd
  have hH := halfInt_nonneg (((d : ℝ) - s) / 2)
  set S0 : ℝ := ∑' m : Lattice d, Real.exp (-(1 / 2) * Lattice.enorm m ^ 2) with hS0
  have hS0s : Summable fun m : Lattice d => Real.exp (-(1 / 2) * Lattice.enorm m ^ 2) :=
    summable_gauss_lattice d (1 / 2) (by norm_num)
  have hS0n : 0 ≤ S0 := tsum_nonneg fun _ => (Real.exp_pos _).le
  refine ⟨subA d s * halfInt (((d : ℝ) - s) / 2) * S0, by positivity, fun n hn => ?_⟩
  set F : Lattice d → ℝ := fun k => cT d s (1 / (n : ℝ) ^ 2) k * (if (∀ c, (n : ℤ) ∣ k c) then 1 else 0)
    with hF
  have hε : 0 < 1 / (n : ℝ) ^ 2 := by positivity
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  have hinj : Function.Injective (fun m : Lattice d => (n : ℤ) • m) := by
    intro m m' h
    funext c
    have := congrFun h c
    simp only [Pi.smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ hn' this
  have hsupp : Function.support F ⊆ Set.range (fun m : Lattice d => (n : ℤ) • m) := by
    intro k hk
    have hdiv : ∀ c, (n : ℤ) ∣ k c := by
      by_contra h
      apply hk
      simp only [hF, h, if_false, mul_zero]
    refine ⟨fun c => k c / n, ?_⟩
    funext c
    simp only [Pi.smul_apply, smul_eq_mul]
    exact Int.mul_ediv_cancel' (hdiv c)
  rw [← hinj.tsum_eq hsupp]
  have hFm : ∀ m : Lattice d, F ((n : ℤ) • m) = cT d s (1 / (n : ℝ) ^ 2) ((n : ℤ) • m) := by
    intro m
    have : ∀ c, (n : ℤ) ∣ ((n : ℤ) • m) c := fun c => ⟨m c, rfl⟩
    simp [hF, this]
  simp_rw [hFm]
  set M : Lattice d → ℝ := fun m => subA d s * halfInt (((d : ℝ) - s) / 2) * (n : ℝ) ^ (s - d) *
    Real.exp (-(1 / 2) * Lattice.enorm m ^ 2) with hM
  have hMs : Summable M := hS0s.mul_left _
  have hle : ∀ m : Lattice d, cT d s (1 / (n : ℝ) ^ 2) ((n : ℤ) • m) ≤ M m := by
    intro m
    by_cases hm : m = 0
    · subst hm
      have : cT d s (1 / (n : ℝ) ^ 2) ((n : ℤ) • (0 : Lattice d)) = 0 := by
        simp [cT]
      rw [this]
      simp only [hM]
      positivity
    · exact cT_lattice_le hd hs0 hsd hn m hm
  have hnn : ∀ m : Lattice d, 0 ≤ cT d s (1 / (n : ℝ) ^ 2) ((n : ℤ) • m) :=
    fun m => cT_nonneg hd hs0 hsd hε _
  have hsum : Summable fun m : Lattice d => cT d s (1 / (n : ℝ) ^ 2) ((n : ℤ) • m) :=
    Summable.of_nonneg_of_le hnn hle hMs
  calc ∑' m : Lattice d, cT d s (1 / (n : ℝ) ^ 2) ((n : ℤ) • m) ≤ ∑' m, M m :=
        hsum.tsum_le_tsum hle hMs
    _ = _ := by
        simp only [hM]
        rw [tsum_mul_left, hS0]
        ring

open CoercAux KernelAux Set in
theorem psi_le_gauss (y : Euc d) (hy : ∀ i, |y i| ≤ 1 / 2) {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    psiFn (Torus.mk y) u ≤
      (Real.sqrt (Real.pi / u) * thetaB) ^ d * Real.exp (-(Real.pi ^ 2 / (2 * u)) * ‖y‖ ^ 2) := by
  have h1 := heatK_boxPt_le (d := d) hu hu1 (y := fun i => y i) hy
  have h2 : heatK d u (boxPt (fun i => y i)) = 1 + psiFn (boxPt (fun i => y i)) u := by
    unfold heatK; exact psi_eq _ hu
  have hmk : Torus.mk y = boxPt (fun i => y i) := rfl
  rw [hmk]
  have h3 : ∏ i, Gt u (y i) = (Real.sqrt (Real.pi / u) * thetaB) ^ d *
      Real.exp (-(Real.pi ^ 2 / (2 * u)) * ‖y‖ ^ 2) := by
    unfold Gt
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, ← Real.exp_sum]
    rw [← mul_pow]
    congr 2
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [← h3]
  linarith [h1.2]

theorem lattice_diff_coords {n : ℕ} (hn : 0 < n) (i j : Fin d → Fin n) (c : Fin d) :
    ∃ t : ℤ, (n : ℝ) * (KernelGrad.centeredRep (latticePoint n i - latticePoint n j)) c = t := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  set w : Torus d := latticePoint n i - latticePoint n j with hw
  set y0 : Euc d := WithLp.toLp 2 (fun c => ((((i c : ℕ) : ℝ) - ((j c : ℕ) : ℝ)) / n : ℝ)) with hy0
  have hmk : Torus.mk (KernelGrad.centeredRep w) = Torus.mk y0 := by
    rw [KernelGrad.mk_centeredRep]
    funext c
    simp only [hw, Pi.sub_apply, Torus.mk, hy0, latticePoint]
    rw [← AddCircle.coe_sub]
    congr 1
    ring
  obtain ⟨m, hm⟩ := KernelGrad.exists_lattice_of_mk_eq hmk
  refine ⟨((i c : ℕ) : ℤ) - ((j c : ℕ) : ℤ) + n * m c, ?_⟩
  have := congrArg (fun v : Euc d => v c) hm
  simp only [hy0, PiLp.add_apply, Lattice.toEuc] at this
  rw [this]
  push_cast
  field_simp

open CoercAux KernelAux Set in
theorem gauss_shell_le {c v : ℝ} (hc : 0 < c) (hv : 1 ≤ v) :
    Summable (fun M : Lattice d => if M = 0 then (0 : ℝ) else Real.exp (-c * Lattice.enorm M ^ 2 * v)) ∧
    ∑' M : Lattice d, (if M = 0 then (0 : ℝ) else Real.exp (-c * Lattice.enorm M ^ 2 * v)) ≤
      Real.exp (-(c * v / 2)) * ∑' M : Lattice d, Real.exp (-(c / 2) * Lattice.enorm M ^ 2) := by
  have hS : Summable fun M : Lattice d => Real.exp (-(c / 2) * Lattice.enorm M ^ 2) :=
    summable_gauss_lattice d (c / 2) (by positivity)
  have hle : ∀ M : Lattice d, (if M = 0 then (0 : ℝ) else Real.exp (-c * Lattice.enorm M ^ 2 * v)) ≤
      Real.exp (-(c * v / 2)) * Real.exp (-(c / 2) * Lattice.enorm M ^ 2) := by
    intro M
    by_cases hM : M = 0
    · simp [hM]
      positivity
    · simp only [hM, if_false]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h1 : 1 ≤ Lattice.enorm M ^ 2 := by
        have := one_le_enorm M hM
        nlinarith
      nlinarith [mul_nonneg hc.le (sub_nonneg.mpr h1), mul_nonneg hc.le (sub_nonneg.mpr hv),
        mul_nonneg (mul_nonneg hc.le (sub_nonneg.mpr h1)) (sub_nonneg.mpr hv)]
  have hnn : ∀ M : Lattice d, 0 ≤ (if M = 0 then (0 : ℝ) else Real.exp (-c * Lattice.enorm M ^ 2 * v)) := by
    intro M; split_ifs <;> positivity
  have hsum := Summable.of_nonneg_of_le hnn hle (hS.mul_left (Real.exp (-(c * v / 2))))
  refine ⟨hsum, ?_⟩
  calc _ ≤ ∑' M : Lattice d, Real.exp (-(c * v / 2)) * Real.exp (-(c / 2) * Lattice.enorm M ^ 2) :=
        hsum.tsum_le_tsum hle (hS.mul_left _)
    _ = _ := tsum_mul_left

open KernelAux in
theorem rpow_exp_bound {κ p : ℝ} (hκ : 0 < κ) (hp : 0 < p) :
    ∃ K0 : ℝ, 0 ≤ K0 ∧ ∀ (N u : ℝ), 0 < N → 0 < u →
      u ^ (-p) * Real.exp (-(κ / (N * u))) ≤ K0 * N ^ p := by
  refine ⟨κ ^ (-p) * (p ^ p * Real.exp (-p)), by positivity, fun N u hN hu => ?_⟩
  set v : ℝ := 1 / (N * u) with hv
  have hv0 : 0 < v := by positivity
  have h1 : u ^ (-p) = N ^ p * v ^ p := by
    have : u = (N * v)⁻¹ := by rw [hv]; field_simp
    rw [this, Real.inv_rpow (by positivity), Real.rpow_neg (by positivity), inv_inv,
      Real.mul_rpow hN.le hv0.le]
  have h2 := rpow_mul_exp_le hp (v := κ * v) (by positivity)
  have h3 : κ / (N * u) = κ * v := by rw [hv]; field_simp
  rw [h1, h3]
  rw [Real.mul_rpow hκ.le hv0.le] at h2
  have h4 : κ ^ (-p) * κ ^ p = 1 := by
    rw [← Real.rpow_add hκ]; simp
  have hκp : 0 < κ ^ p := by positivity
  calc N ^ p * v ^ p * Real.exp (-(κ * v)) = N ^ p * (κ ^ (-p) * (κ ^ p * v ^ p * Real.exp (-(κ * v)))) := by
        rw [← mul_assoc (κ ^ (-p)), ← mul_assoc (κ ^ (-p)), h4, one_mul]; ring
    _ ≤ N ^ p * (κ ^ (-p) * (p ^ p * Real.exp (-p))) := by gcongr
    _ = _ := by ring

/-- integer coordinates of the centered representative of `Λ_i - Λ_j`, scaled by `n` -/
def shellVec (n : ℕ) (i j : Fin (n ^ d)) : Lattice d :=
  fun c => round ((n : ℝ) * (KernelGrad.centeredRep (latCfg n i - latCfg n j)) c)

theorem shellVec_spec {n : ℕ} (hn : 0 < n) (i j : Fin (n ^ d)) (c : Fin d) :
    (n : ℝ) * (KernelGrad.centeredRep (latCfg n i - latCfg n j)) c = (shellVec n i j c : ℝ) := by
  obtain ⟨t, ht⟩ := lattice_diff_coords hn (finFunctionFinEquiv.symm i) (finFunctionFinEquiv.symm j) c
  have : (n : ℝ) * (KernelGrad.centeredRep (latCfg n i - latCfg n j)) c = (t : ℝ) := ht
  rw [shellVec, this, round_intCast]

theorem shellVec_norm {n : ℕ} (hn : 0 < n) (i j : Fin (n ^ d)) :
    ‖KernelGrad.centeredRep (latCfg n i - latCfg n j)‖ = Lattice.enorm (shellVec n i j) / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h : KernelGrad.centeredRep (latCfg n i - latCfg n j) = ((n : ℝ)⁻¹) • Lattice.toEuc (shellVec n i j) := by
    ext c
    have := shellVec_spec hn i j c
    simp only [PiLp.smul_apply, Lattice.toEuc, smul_eq_mul]
    rw [← this]
    field_simp
  rw [h, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn')]
  unfold Lattice.enorm
  field_simp

theorem shellVec_injective {n : ℕ} (hn : 0 < n) (i : Fin (n ^ d)) :
    Function.Injective (shellVec n i) := by
  intro j j' h
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hc : KernelGrad.centeredRep (latCfg n i - latCfg n j) =
      KernelGrad.centeredRep (latCfg n i - latCfg n j') := by
    ext c
    have h1 := shellVec_spec hn i j c
    have h2 := shellVec_spec hn i j' c
    rw [h] at h1
    exact mul_left_cancel₀ hn' (h1.trans h2.symm)
  have := congrArg Torus.mk hc
  rw [KernelGrad.mk_centeredRep, KernelGrad.mk_centeredRep] at this
  have h3 : latCfg n j = latCfg n j' := by
    have := sub_right_injective this
    exact this
  exact latCfg_injective hn h3

theorem shellVec_ne_zero {n : ℕ} (hn : 0 < n) {i j : Fin (n ^ d)} (hij : i ≠ j) :
    shellVec n i j ≠ 0 := by
  intro h0
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hc : KernelGrad.centeredRep (latCfg n i - latCfg n j) = 0 := by
    ext c
    have h1 := shellVec_spec hn i j c
    rw [h0] at h1
    simp only [Pi.zero_apply, Int.cast_zero] at h1
    have := (mul_eq_zero.mp h1).resolve_left hn'
    simpa using this
  have h2 := congrArg Torus.mk hc
  rw [KernelGrad.mk_centeredRep] at h2
  have h3 : latCfg n i = latCfg n j := by
    have : Torus.mk (0 : Euc d) = 0 := by funext i; simp [Torus.mk]
    rw [this] at h2
    exact sub_eq_zero.mp h2
  exact hij (latCfg_injective hn h3)

theorem sqrt_div_pow {u : ℝ} (hu : 0 < u) (d : ℕ) :
    (Real.sqrt (Real.pi / u)) ^ d = (Real.sqrt Real.pi) ^ d * u ^ (-(d : ℝ) / 2) := by
  have h1 : Real.sqrt (Real.pi / u) = Real.sqrt Real.pi * u ^ (-(1 : ℝ) / 2) := by
    rw [Real.sqrt_div Real.pi_pos.le, Real.sqrt_eq_rpow u, div_eq_mul_inv, ← Real.rpow_neg hu.le]
    congr 2; ring
  have h2 : (u ^ (-(1 : ℝ) / 2)) ^ d = u ^ (-(d : ℝ) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hu.le]
    congr 1; ring
  rw [h1, mul_pow, h2]

open CoercAux KernelAux Set in
theorem row_pointwise {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, 0 < n → ∀ i : Fin (n ^ d), ∀ u : ℝ, 0 < u → u ≤ 1 / (n : ℝ) ^ 2 →
      ∑ j ∈ Finset.univ.erase i,
        u ^ (((d : ℝ) - s) / 2 - 1) * psiFn (latCfg n i - latCfg n j) u ≤ K * (n : ℝ) ^ (s + 2) := by
  set c : ℝ := Real.pi ^ 2 / 2 with hc
  have hc0 : 0 < c := by positivity
  set p : ℝ := s / 2 + 1 with hp
  have hp0 : 0 < p := by positivity
  obtain ⟨K0, hK0, hK⟩ := rpow_exp_bound (κ := c / 2) (p := p) (by positivity) hp0
  set Sc : ℝ := ∑' M : Lattice d, Real.exp (-(c / 2) * Lattice.enorm M ^ 2) with hSc
  have hSc0 : 0 ≤ Sc := tsum_nonneg fun _ => (Real.exp_pos _).le
  have hB0 : 0 ≤ (Real.sqrt Real.pi * thetaB) ^ d :=
    pow_nonneg (mul_nonneg (Real.sqrt_nonneg _) thetaB_nonneg) _
  refine ⟨(Real.sqrt Real.pi * thetaB) ^ d * Sc * K0, by positivity, fun n hn i u hu hu1 => ?_⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hu1' : u ≤ 1 := by
    refine hu1.trans ?_
    have : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    rw [div_le_one (by positivity)]; exact this
  set v : ℝ := 1 / ((n : ℝ) ^ 2 * u) with hv
  have hv1 : 1 ≤ v := by
    rw [hv, le_div_iff₀ (by positivity)]
    rw [le_div_iff₀ (by positivity)] at hu1
    linarith
  -- pointwise bound for each term
  set f : Lattice d → ℝ := fun M => Real.exp (-c * Lattice.enorm M ^ 2 * v) with hf
  have hterm : ∀ j ∈ Finset.univ.erase i,
      u ^ (((d : ℝ) - s) / 2 - 1) * psiFn (latCfg n i - latCfg n j) u ≤
        (Real.sqrt Real.pi * thetaB) ^ d * u ^ (-p) * (if shellVec n i j = 0 then 0 else f (shellVec n i j)) := by
    intro j hj
    have hij : i ≠ j := fun h => (Finset.ne_of_mem_erase hj) h.symm
    have hM0 : shellVec n i j ≠ 0 := shellVec_ne_zero hn hij
    rw [if_neg hM0]
    set y := KernelGrad.centeredRep (latCfg n i - latCfg n j) with hy
    have hbox := KernelGrad.abs_centeredRep_le (latCfg n i - latCfg n j)
    have hmk : Torus.mk y = latCfg n i - latCfg n j := KernelGrad.mk_centeredRep _
    have h1 := psi_le_gauss y hbox hu hu1'
    rw [hmk, mul_pow, sqrt_div_pow hu] at h1
    have hnorm : ‖y‖ = Lattice.enorm (shellVec n i j) / n := shellVec_norm hn i j
    have h2 : -(Real.pi ^ 2 / (2 * u)) * ‖y‖ ^ 2 = -c * Lattice.enorm (shellVec n i j) ^ 2 * v := by
      rw [hnorm, hc, hv]; field_simp
    rw [h2] at h1
    have hu0 : 0 < u ^ (((d : ℝ) - s) / 2 - 1) := Real.rpow_pos_of_pos hu _
    have hpow : u ^ (((d : ℝ) - s) / 2 - 1) * u ^ (-(d : ℝ) / 2) = u ^ (-p) := by
      rw [← Real.rpow_add hu, hp]; congr 1; ring
    calc u ^ (((d : ℝ) - s) / 2 - 1) * psiFn (latCfg n i - latCfg n j) u
        ≤ u ^ (((d : ℝ) - s) / 2 - 1) * (Real.sqrt Real.pi ^ d * u ^ (-(d : ℝ) / 2) * thetaB ^ d *
            Real.exp (-c * Lattice.enorm (shellVec n i j) ^ 2 * v)) :=
          mul_le_mul_of_nonneg_left h1 hu0.le
      _ = (u ^ (((d : ℝ) - s) / 2 - 1) * u ^ (-(d : ℝ) / 2)) * (Real.sqrt Real.pi ^ d * thetaB ^ d) *
            Real.exp (-c * Lattice.enorm (shellVec n i j) ^ 2 * v) := by ring
      _ = _ := by rw [hpow, mul_pow]; simp only [hf]; ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  obtain ⟨hgs, hgle⟩ := gauss_shell_le (d := d) hc0 hv1
  set g : Lattice d → ℝ := fun M => if M = 0 then (0 : ℝ) else f M with hg
  have hsumg : ∑ j ∈ Finset.univ.erase i, (if shellVec n i j = 0 then (0 : ℝ) else f (shellVec n i j)) ≤
      ∑' M : Lattice d, g M := by
    have e : ∑ j ∈ Finset.univ.erase i, (if shellVec n i j = 0 then (0 : ℝ) else f (shellVec n i j)) =
        ∑ M ∈ (Finset.univ.erase i).image (shellVec n i), g M := by
      rw [Finset.sum_image (fun x _ y _ h => shellVec_injective hn i h)]
    rw [e]
    refine hgs.sum_le_tsum _ (fun M _ => ?_)
    simp only [hg]; split_ifs <;> positivity
  have hgle' : ∑' M : Lattice d, g M ≤ Real.exp (-(c * v / 2)) * Sc := hgle
  have hup : 0 ≤ (Real.sqrt Real.pi * thetaB) ^ d * u ^ (-p) := by
    have := Real.rpow_nonneg hu.le (-p)
    positivity
  have hkey := hK ((n : ℝ) ^ 2) u (by positivity) hu
  have hexp : c * v / 2 = c / 2 / ((n : ℝ) ^ 2 * u) := by rw [hv]; field_simp
  rw [hexp] at hgle'
  have hNp : (((n : ℝ) ^ 2) ^ p) = (n : ℝ) ^ (s + 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn'.le, hp]
    congr 1; push_cast; ring
  rw [hNp] at hkey
  calc (Real.sqrt Real.pi * thetaB) ^ d * u ^ (-p) * ∑ j ∈ Finset.univ.erase i,
        (if shellVec n i j = 0 then (0 : ℝ) else f (shellVec n i j))
      ≤ (Real.sqrt Real.pi * thetaB) ^ d * u ^ (-p) * (Real.exp (-(c / 2 / ((n : ℝ) ^ 2 * u))) * Sc) :=
        mul_le_mul_of_nonneg_left (hsumg.trans hgle') hup
    _ = (Real.sqrt Real.pi * thetaB) ^ d * Sc * (u ^ (-p) * Real.exp (-(c / 2 / ((n : ℝ) ^ 2 * u)))) := by ring
    _ ≤ (Real.sqrt Real.pi * thetaB) ^ d * Sc * (K0 * (n : ℝ) ^ (s + 2)) := by gcongr
    _ = _ := by ring

open CoercAux KernelAux Set in
theorem nearF_row_le {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n → ∀ i : Fin (n ^ d),
      ∑ j ∈ Finset.univ.erase i, nearF d s (1 / (n : ℝ) ^ 2) (latCfg n i - latCfg n j) ≤
        C * (n : ℝ) ^ s := by
  obtain ⟨K, hK0, hK⟩ := row_pointwise (s := s) hd hs0 hsd
  have hA := subA_nonneg_one (d := d) (by omega) hs0 hsd
  refine ⟨subA d s * K, mul_nonneg hA hK0, fun n hn i => ?_⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set ε : ℝ := 1 / (n : ℝ) ^ 2 with hε
  have hε0 : 0 < ε := by positivity
  have hdist : ∀ j ∈ Finset.univ.erase i, latCfg n i - latCfg n j ≠ 0 := by
    intro j hj h
    have hij : i ≠ j := fun h => (Finset.ne_of_mem_erase hj) h.symm
    exact hij (latCfg_injective hn (sub_eq_zero.mp h))
  have hnear : ∀ j ∈ Finset.univ.erase i, nearF d s ε (latCfg n i - latCfg n j) =
      subA d s * ∫ u in Ioc 0 ε, u ^ (((d : ℝ) - s) / 2 - 1) * psiFn (latCfg n i - latCfg n j) u := by
    intro j hj
    have hz := hdist j hj
    have := periodicRiesz_decomp (d := d) (s := s) (by omega) hs0 hsd hε0 _ hz
    simp only [nearF, hz, if_false]
    linarith
  have hint : ∀ j ∈ Finset.univ.erase i, IntegrableOn
      (fun u : ℝ => u ^ (((d : ℝ) - s) / 2 - 1) * psiFn (latCfg n i - latCfg n j) u) (Ioc 0 ε) := by
    intro j hj
    exact (integrableOn_psi hsd _ (hdist j hj)).mono_set (fun u hu => mem_Ioi.mpr hu.1)
  rw [Finset.sum_congr rfl hnear, ← Finset.mul_sum, ← integral_finset_sum _ hint]
  have hsumint : IntegrableOn (fun u : ℝ => ∑ j ∈ Finset.univ.erase i,
      u ^ (((d : ℝ) - s) / 2 - 1) * psiFn (latCfg n i - latCfg n j) u) (Ioc 0 ε) :=
    integrable_finset_sum _ hint
  have hle : ∫ u in Ioc 0 ε, ∑ j ∈ Finset.univ.erase i,
      u ^ (((d : ℝ) - s) / 2 - 1) * psiFn (latCfg n i - latCfg n j) u ≤
        ∫ u in Ioc 0 ε, K * (n : ℝ) ^ (s + 2) := by
    refine setIntegral_mono_on hsumint (integrableOn_const (by simp)) measurableSet_Ioc (fun u hu => ?_)
    exact hK n hn i u hu.1 hu.2
  rw [setIntegral_const, Real.volume_real_Ioc_of_le hε0.le] at hle
  have hv : (ε - 0) * (K * (n : ℝ) ^ (s + 2)) = K * (n : ℝ) ^ s := by
    rw [hε, sub_zero, Real.rpow_add hn', Real.rpow_two]
    field_simp
  rw [smul_eq_mul, hv] at hle
  calc subA d s * ∫ u in Ioc 0 ε, ∑ j ∈ Finset.univ.erase i,
        u ^ (((d : ℝ) - s) / 2 - 1) * psiFn (latCfg n i - latCfg n j) u
      ≤ subA d s * (K * (n : ℝ) ^ s) := mul_le_mul_of_nonneg_left hle hA
    _ = _ := by ring

open CoercAux KernelAux Set in
theorem psi_zero_ge {u : ℝ} (hu : 0 < u) :
    Real.sqrt Real.pi ^ d * u ^ (-(d : ℝ) / 2) ≤ 1 + psiFn (0 : Torus d) u := by
  have h := psi_eq (0 : Torus d) hu
  have hb : (boxPt (0 : Fin d → ℝ) : Torus d) = 0 := by
    funext i; simp [boxPt]
  have h2 := theta_prod (0 : Fin d → ℝ) hu
  rw [hb] at h2
  rw [h2] at h
  simp only [Pi.zero_apply] at h
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  rw [← h]
  set S := ∑' n : ℤ, Real.exp (-(Real.pi ^ 2 * ((n : ℝ) - 0) ^ 2 / u)) with hS
  have hsum : Summable fun n : ℤ => Real.exp (-(Real.pi ^ 2 * ((n : ℝ) - 0) ^ 2 / u)) :=
    (summable_exp_sq (Real.pi ^ 2 / u) (by positivity)).congr (fun n => by congr 1; ring)
  have hS1 : 1 ≤ S := by
    have := hsum.le_tsum 0 (fun j _ => (Real.exp_pos _).le)
    rw [hS]
    simpa using this
  rw [← sqrt_div_pow_eq d hu]
  calc Real.sqrt (Real.pi / u) ^ d = (Real.sqrt (Real.pi / u) * 1) ^ d := by rw [mul_one]
    _ ≤ (Real.sqrt (Real.pi / u) * S) ^ d :=
        pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hS1 (Real.sqrt_nonneg _)) d

open CoercAux KernelAux Set in
theorem gT_zero_ge_zero (hd1 : 1 ≤ d) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → 1 / 2 * Real.log (1 / ε) - C ≤ gT d 0 ε 0 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
  have hsd : (0 : ℝ) < d := hd0
  have hA := subA_nonneg_one hd1 le_rfl hsd
  have hAP := subA_zero_mul (d := d) hd1
  set a : ℝ := ((d : ℝ) - 0) / 2 with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  refine ⟨subA d 0 / a, fun ε hε hε1 => ?_⟩
  rw [gT_eq_integral hd1 le_rfl hsd hε 0]
  set f : ℝ → ℝ := fun u => u ^ (a - 1) * psiFn (0 : Torus d) u with hf
  have hcont : ContinuousOn f (Ioi 0) :=
    ContinuousOn.mul (continuousOn_id.rpow_const fun t ht => Or.inl (ne_of_gt ht)) (psi_continuousOn _)
  have hint1 : IntegrableOn f (Ioc ε 1) := by
    have : ContinuousOn f (Icc ε 1) := hcont.mono (fun u hu => lt_of_lt_of_le hε hu.1)
    exact this.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hG : IntegrableOn (fun u : ℝ => psiLargeC d * (Real.exp (-u) * u ^ (a - 1))) (Ioi 0) :=
    (Real.GammaIntegral_convergent ha).const_mul (psiLargeC d)
  have hf0 : ∀ u : ℝ, 0 < u → 0 ≤ f u := fun u hu =>
    mul_nonneg (Real.rpow_pos_of_pos hu _).le (psi_zero_nonneg hu)
  have hint2 : IntegrableOn f (Ioi 1) := by
    refine Integrable.mono' (hG.mono_set (Ioi_subset_Ioi zero_le_one)) ?_ ?_
    · exact (hcont.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun u hu => ?_)
      have hu1 : (1:ℝ) < u := hu
      have hu0 : 0 < u := by linarith
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 u hu0)]
      have := psi_large (0 : Torus d) hu1.le
      have h2 := (abs_le.mp this).2
      have h3 := Real.rpow_pos_of_pos hu0 (a - 1)
      rw [hf]
      unfold psiLargeC
      calc u ^ (a - 1) * psiFn (0 : Torus d) u
          ≤ u ^ (a - 1) * ((Real.exp 1 * ∑' k : Lattice d, Real.exp (-1 * Lattice.enorm k ^ 2)) *
              Real.exp (-u)) := mul_le_mul_of_nonneg_left h2 h3.le
        _ = _ := by ring
  have hsplit : ∫ u in Ioi ε, f u = (∫ u in Ioc ε 1, f u) + ∫ u in Ioi 1, f u := by
    rw [← Ioc_union_Ioi_eq_Ioi hε1, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hint1 hint2]
  have h2nn : 0 ≤ ∫ u in Ioi 1, f u :=
    setIntegral_nonneg measurableSet_Ioi fun u hu => hf0 u (lt_trans one_pos hu)
  have hlowint : IntegrableOn (fun u : ℝ => Real.sqrt Real.pi ^ d * u⁻¹ - u ^ (a - 1)) (Ioc ε 1) := by
    have : ContinuousOn (fun u : ℝ => Real.sqrt Real.pi ^ d * u⁻¹ - u ^ (a - 1)) (Icc ε 1) := by
      refine ContinuousOn.sub (continuousOn_const.mul ?_) ?_
      · exact continuousOn_inv₀.mono (fun u hu => ne_of_gt (lt_of_lt_of_le hε hu.1))
      · exact (continuousOn_id.rpow_const fun t ht => Or.inl (ne_of_gt (lt_of_lt_of_le hε ht.1)))
    exact this.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hlow : ∫ u in Ioc ε 1, (Real.sqrt Real.pi ^ d * u⁻¹ - u ^ (a - 1)) ≤ ∫ u in Ioc ε 1, f u := by
    refine setIntegral_mono_on hlowint hint1 measurableSet_Ioc (fun u hu => ?_)
    have hu0 : 0 < u := lt_of_lt_of_le hε hu.1.le
    have h1 := psi_zero_ge (d := d) hu0
    have h3 := Real.rpow_pos_of_pos hu0 (a - 1)
    have h5 : u ^ (a - 1) * u ^ (-(d : ℝ) / 2) = u⁻¹ := by
      rw [← Real.rpow_add hu0, ← Real.rpow_neg_one]
      congr 1; rw [ha_def]; ring
    rw [hf]
    have h6 : u ^ (a - 1) * (Real.sqrt Real.pi ^ d * u ^ (-(d : ℝ) / 2) - 1) ≤
        u ^ (a - 1) * psiFn (0 : Torus d) u :=
      mul_le_mul_of_nonneg_left (by linarith) h3.le
    have h7 : u ^ (a - 1) * (Real.sqrt Real.pi ^ d * u ^ (-(d : ℝ) / 2) - 1) =
        Real.sqrt Real.pi ^ d * u⁻¹ - u ^ (a - 1) := by
      rw [← h5]; ring
    simp only
    linarith
  have hcalc : ∫ u in Ioc ε 1, (Real.sqrt Real.pi ^ d * u⁻¹ - u ^ (a - 1)) =
      Real.sqrt Real.pi ^ d * Real.log (1 / ε) - (1 - ε ^ a) / a := by
    rw [← intervalIntegral.integral_of_le hε1, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
      integral_inv_of_pos hε one_pos, integral_rpow (Or.inl (by linarith))]
    · simp
    · exact (intervalIntegral.intervalIntegrable_inv (f := fun u : ℝ => u) (fun u hu => by
        rw [Set.uIcc_of_le hε1] at hu; exact ne_of_gt (lt_of_lt_of_le hε hu.1))
        continuousOn_id).const_mul _
    · refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hε1]
      exact continuousOn_id.rpow_const fun t ht => Or.inl (ne_of_gt (lt_of_lt_of_le hε ht.1))
  rw [hsplit]
  have hP : 0 ≤ Real.sqrt Real.pi ^ d := by positivity
  have hlogε : 0 ≤ ε := hε.le
  have hεa : 0 ≤ ε ^ a := Real.rpow_nonneg hε.le _
  calc 1 / 2 * Real.log (1 / ε) - subA d 0 / a
      = subA d 0 * (Real.sqrt Real.pi ^ d * Real.log (1 / ε) - 1 / a) := by
        linear_combination (-Real.log (1 / ε)) * hAP
    _ ≤ subA d 0 * (Real.sqrt Real.pi ^ d * Real.log (1 / ε) - (1 - ε ^ a) / a) := by
        refine mul_le_mul_of_nonneg_left ?_ hA
        have : (1 - ε ^ a) / a ≤ 1 / a := div_le_div_of_nonneg_right (by linarith) ha.le
        linarith
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left ?_ hA
        rw [← hcalc]; linarith

open CoercAux KernelAux Set in
theorem gT_zero_nonneg {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ε : ℝ} (hε : 0 < ε) :
    0 ≤ gT d s ε 0 := by
  unfold gT
  refine tsum_nonneg fun k => ?_
  rw [show Torus.cosMode k (0 : Torus d) = 1 by
    simp [Torus.cosMode, Torus.mode, UnitAddTorus.mFourier], mul_one]
  exact cT_nonneg hd hs0 hsd hε k

open CoercAux KernelAux Set in
theorem lattice_pair_sum {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ n : ℕ, 0 < n →
      ∑ i, ∑ j ∈ Finset.univ.erase i, periodicRiesz d s (latCfg n i - latCfg n j) ≤
        ((n ^ d : ℕ) : ℝ) * (C₂ * (n : ℝ) ^ s - (if s = 0 then Real.log n else 0)) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨CE, hCE0, hCE⟩ := esq_lattice_bound (d := d) (s := s) hd1 hs0 hsd
  obtain ⟨CN, hCN0, hCN⟩ := nearF_row_le (d := d) (s := s) hd hs0 hsd
  obtain ⟨CG, hCG⟩ := gT_zero_ge_zero (d := d) hd
  refine ⟨CE + CN + |CG|, by positivity, fun n hn => ?_⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set N : ℝ := ((n ^ d : ℕ) : ℝ) with hN
  have hN0 : 0 < N := by positivity
  have hN' : N = (n : ℝ) ^ d := by rw [hN]; push_cast; rfl
  set ε : ℝ := 1 / (n : ℝ) ^ 2 with hε
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := by
    rw [hε, div_le_one (by positivity)]
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hdist : ∀ i j : Fin (n ^ d), i ≠ j → latCfg n i - latCfg n j ≠ 0 := by
    intro i j hij h
    exact hij (latCfg_injective hn (sub_eq_zero.mp h))
  -- row decomposition
  have hrow : ∀ i : Fin (n ^ d),
      ∑ j ∈ Finset.univ.erase i, periodicRiesz d s (latCfg n i - latCfg n j) =
        ∑ j, gT d s ε (latCfg n i - latCfg n j) - gT d s ε 0 +
          ∑ j ∈ Finset.univ.erase i, nearF d s ε (latCfg n i - latCfg n j) := by
    intro i
    have h1 : ∑ j ∈ Finset.univ.erase i, periodicRiesz d s (latCfg n i - latCfg n j) =
        ∑ j ∈ Finset.univ.erase i, (gT d s ε (latCfg n i - latCfg n j) +
          nearF d s ε (latCfg n i - latCfg n j)) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hij : i ≠ j := fun h => (Finset.ne_of_mem_erase hj) h.symm
      exact periodicRiesz_eq_add (ε := ε) _ (hdist i j hij)
    rw [h1, Finset.sum_add_distrib]
    have h3 : ∑ j ∈ Finset.univ.erase i, gT d s ε (latCfg n i - latCfg n j) =
        ∑ j, gT d s ε (latCfg n i - latCfg n j) - gT d s ε 0 := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      simp
    rw [h3]
  rw [Finset.sum_congr rfl (fun i _ => hrow i), Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- the three terms
  have hE := gT_lattice_sum (d := d) (s := s) hd1 hs0 hsd hε0 hn
  have hE2 := hCE n hn
  have hEsum : ∑ i, ∑ j, gT d s ε (latCfg n i - latCfg n j) ≤ N * (CE * (n : ℝ) ^ s) := by
    have h1 : ∑ i, ∑ j, gT d s ε (latCfg n i - latCfg n j) =
        N ^ 2 * ∑' k : Lattice d, cT d s ε k * (if (∀ c, (n : ℤ) ∣ k c) then 1 else 0) := by
      rw [← hE, hN]; field_simp
    rw [h1]
    have h2 : N ^ 2 * (CE * (n : ℝ) ^ (s - d)) = N * (CE * (n : ℝ) ^ s) := by
      rw [hN', Real.rpow_sub hn', Real.rpow_natCast]
      field_simp
    rw [← h2]
    exact mul_le_mul_of_nonneg_left hE2 (by positivity)
  have hNear : ∑ i, ∑ j ∈ Finset.univ.erase i, nearF d s ε (latCfg n i - latCfg n j) ≤
      N * (CN * (n : ℝ) ^ s) := by
    calc _ ≤ ∑ _i : Fin (n ^ d), CN * (n : ℝ) ^ s := Finset.sum_le_sum fun i _ => hCN n hn i
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hN]
  have hG0 : (if s = 0 then Real.log n - CG else 0) ≤ gT d s ε 0 := by
    split_ifs with hs
    · subst hs
      have := hCG ε hε0 hε1
      have h2 : 1 / 2 * Real.log (1 / ε) = Real.log n := by
        rw [hε, one_div_one_div, Real.log_pow]; push_cast; ring
      linarith
    · exact gT_zero_nonneg hd1 hs0 hsd hε0
  have hnpos : 0 < (n : ℝ) ^ s := Real.rpow_pos_of_pos hn' _
  have hCG' : (if s = 0 then CG else 0) ≤ |CG| := by split_ifs; exact le_abs_self _; exact abs_nonneg _
  have hmain : -(gT d s ε 0) ≤ |CG| * (n : ℝ) ^ s - (if s = 0 then Real.log n else 0) := by
    by_cases hs : s = 0
    · subst hs
      simp only [ite_true, Real.rpow_zero, mul_one] at hG0 ⊢
      linarith [le_abs_self CG]
    · simp only [hs, if_false] at hG0 ⊢
      have := mul_nonneg (abs_nonneg CG) hnpos.le
      linarith
  have hm2 := mul_le_mul_of_nonneg_left hmain hN0.le
  rw [← hN]
  nlinarith [hEsum, hNear, hm2]

/-- exact cancellation of the first-order term on the lattice -/
theorem first_order_zero {n : ℕ} (hn : 0 < n) (G : Torus d → Euc d) (hodd : ∀ x, G (-x) = -G x)
    (b : Fin (n ^ d) → Euc d) :
    ∑ i, ∑ j ∈ Finset.univ.erase i, inner ℝ (G (latCfg n i - latCfg n j)) (b i - b j) = 0 := by
  -- the force on each particle vanishes
  have hV : ∀ i : Fin (n ^ d), ∑ j ∈ Finset.univ.erase i, G (latCfg n i - latCfg n j) = 0 := by
    intro i
    choose τ hτ using fun j => latCfg_reflect hn i j
    refine Finset.sum_involution (fun j _ => τ j) ?_ ?_ ?_ ?_
    · intro j hj
      have : latCfg n i - latCfg n (τ j) = -(latCfg n i - latCfg n j) := by
        rw [hτ j]; abel
      rw [this, hodd]; abel
    · intro j hj hne hjj
      apply hne
      have h1 : latCfg n (τ j) = latCfg n j := by rw [hjj]
      rw [hτ j] at h1
      have h2 : (latCfg n i - latCfg n j) = -(latCfg n i - latCfg n j) := by
        have : (latCfg n i - latCfg n j) + (latCfg n i - latCfg n j) = 0 := by
          calc (latCfg n i - latCfg n j) + (latCfg n i - latCfg n j)
              = (latCfg n i + latCfg n i - latCfg n j) - latCfg n j := by abel
            _ = 0 := by rw [h1]; simp
        exact eq_neg_of_add_eq_zero_left this
      have h3 : G (latCfg n i - latCfg n j) = -G (latCfg n i - latCfg n j) := by
        conv_lhs => rw [h2]
        exact hodd _
      have h4 : (2 : ℝ) • G (latCfg n i - latCfg n j) = 0 := by
        rw [two_smul]; nth_rewrite 1 [h3]; exact neg_add_cancel _
      exact (smul_eq_zero.mp h4).resolve_left (by norm_num)
    · intro j hj
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      rw [Finset.mem_erase]
      refine ⟨fun h => hji ?_, Finset.mem_univ _⟩
      have h1 : latCfg n (τ j) = latCfg n i := by rw [h]
      rw [hτ j] at h1
      apply latCfg_injective hn
      have : latCfg n j = latCfg n i := by
        have h5 := h1
        rw [sub_eq_iff_eq_add] at h5
        exact (add_left_cancel h5).symm
      exact this
    · intro j hj
      apply latCfg_injective hn
      rw [hτ (τ j), hτ j]
      abel
  have hV' : ∀ j : Fin (n ^ d), ∑ i ∈ Finset.univ.erase j, G (latCfg n i - latCfg n j) = 0 := by
    intro j
    have : ∀ i : Fin (n ^ d), G (latCfg n i - latCfg n j) = -G (latCfg n j - latCfg n i) := by
      intro i
      rw [← hodd]; congr 1; abel
    simp_rw [this]
    rw [Finset.sum_neg_distrib, hV j, neg_zero]
  simp_rw [inner_sub_right, Finset.sum_sub_distrib]
  have hA : ∑ i, ∑ j ∈ Finset.univ.erase i, inner ℝ (G (latCfg n i - latCfg n j)) (b i) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← sum_inner, hV i, inner_zero_left]
  have hB : ∑ i, ∑ j ∈ Finset.univ.erase i, inner ℝ (G (latCfg n i - latCfg n j)) (b j) = 0 := by
    rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun j => Finset.univ.erase j)]
    · refine Finset.sum_eq_zero fun j _ => ?_
      rw [← sum_inner, hV' j, inner_zero_left]
    · intro x y
      simp [Finset.mem_erase, ne_comm]
  rw [hA, hB]; simp

theorem perturbed_apply {n : ℕ} (κ : ℝ) (a : Torus d → Euc d) (j : Fin (n ^ d)) :
    perturbedLattice n κ a j = latCfg n j + Torus.mk (κ⁻¹ • a (latCfg n j)) := rfl

theorem perturbed_sub {n : ℕ} (κ : ℝ) (a : Torus d → Euc d) (i j : Fin (n ^ d)) :
    perturbedLattice n κ a i - perturbedLattice n κ a j =
      (latCfg n i - latCfg n j) + Torus.mk (κ⁻¹ • (a (latCfg n i) - a (latCfg n j))) := by
  rw [perturbed_apply, perturbed_apply, smul_sub, KernelGrad.mk_sub]
  abel

theorem rho_sq_rpow {z : Torus d} (hz : z ≠ 0) {s : ℝ} :
    rho z ^ 2 * rho z ^ (-(s + 2)) = rho z ^ (-s) := by
  have h := rho_pos hz
  rw [← Real.rpow_natCast, ← Real.rpow_add h]
  congr 1; push_cast; ring

theorem perturb_pair_sum {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    {a : Torus d → Euc d} (ha : Torus.IsSmooth a) :
    ∃ κ₀ C₁ : ℝ, 0 < κ₀ ∧ 0 ≤ C₁ ∧ ∀ n : ℕ, 0 < n → ∀ κ : ℝ, κ₀ ≤ κ →
      ∑ i, ∑ j ∈ Finset.univ.erase i,
          periodicRiesz d s (perturbedLattice n κ a i - perturbedLattice n κ a j) ≤
        ∑ i, ∑ j ∈ Finset.univ.erase i, periodicRiesz d s (latCfg n i - latCfg n j) +
          C₁ * κ⁻¹ ^ 2 * ((n ^ d : ℕ) : ℝ) ^ 2 := by
  obtain ⟨Cτ, hCτ0, hCτ⟩ := taylor_torus (s := s) hd hs0 hsd
  obtain ⟨L, hL0, hL⟩ := lipschitz_a ha
  obtain ⟨K, hK0, hK⟩ := rpow_neg_le_add (s := s) hd hs0 hsd
  obtain ⟨C₂, hC₂0, hC₂⟩ := lattice_pair_sum (s := s) hd hs0 hsd
  set CK : ℝ := K + (d : ℝ) ^ 2 with hCK
  have hCK0 : 0 ≤ CK := by positivity
  refine ⟨max (2 * L) 1, Cτ * L ^ 2 * (C₂ + CK), lt_of_lt_of_le one_pos (le_max_right _ _), by positivity,
    fun n hn κ hκ => ?_⟩
  have hκ1 : 1 ≤ κ := (le_max_right _ _).trans hκ
  have hκ0 : 0 < κ := by linarith
  have hκL : L ≤ κ / 2 := by
    have := (le_max_left (2 * L) 1).trans hκ
    linarith
  have hκi : κ⁻¹ * L ≤ 1 / 2 := by
    rw [inv_mul_le_iff₀ hκ0]; linarith
  have hκi0 : 0 ≤ κ⁻¹ := inv_nonneg.mpr hκ0.le
  set N : ℝ := ((n ^ d : ℕ) : ℝ) with hN
  have hN1 : 1 ≤ N := by
    rw [hN]; exact_mod_cast Nat.one_le_pow _ _ hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  -- pair bound
  have hpair : ∀ i j : Fin (n ^ d), i ≠ j →
      periodicRiesz d s (perturbedLattice n κ a i - perturbedLattice n κ a j) ≤
        periodicRiesz d s (latCfg n i - latCfg n j) +
          κ⁻¹ * inner ℝ (periodicRieszGrad d s (latCfg n i - latCfg n j))
            (a (latCfg n i) - a (latCfg n j)) +
          Cτ * L ^ 2 * κ⁻¹ ^ 2 * (periodicRiesz d s (latCfg n i - latCfg n j) + CK) := by
    intro i j hij
    have hz : latCfg n i - latCfg n j ≠ 0 := fun h => hij (latCfg_injective hn (sub_eq_zero.mp h))
    set z := latCfg n i - latCfg n j with hzdef
    set δ : Euc d := κ⁻¹ • (a (latCfg n i) - a (latCfg n j)) with hδ
    have hρ := rho_pos hz
    have hδn : ‖δ‖ ≤ κ⁻¹ * L * rho z := by
      rw [hδ, norm_smul, Real.norm_eq_abs, abs_of_nonneg hκi0, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hL _ _) hκi0
    have hδ2 : ‖δ‖ ≤ rho z / 2 := by
      refine hδn.trans ?_
      nlinarith
    have hT := hCτ z δ hz hδ2
    rw [← perturbed_sub] at hT
    have hT' := (abs_le.mp hT).2
    have hin : inner ℝ (periodicRieszGrad d s z) δ =
        κ⁻¹ * inner ℝ (periodicRieszGrad d s z) (a (latCfg n i) - a (latCfg n j)) := by
      rw [hδ, inner_smul_right]
    have hρd : rho z ^ 2 ≤ (d : ℝ) ^ 2 := by
      have := rho_le z
      have := rho_nonneg z
      nlinarith
    have hρK := hK z hz
    have hδsq : ‖δ‖ ^ 2 ≤ (κ⁻¹ * L) ^ 2 * rho z ^ 2 := by
      calc ‖δ‖ ^ 2 ≤ (κ⁻¹ * L * rho z) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hδn 2
        _ = _ := by ring
    have hfac : 0 ≤ rho z ^ (-(s + 2)) + 1 := by
      have := Real.rpow_nonneg hρ.le (-(s + 2)); linarith
    have hrem : Cτ * ‖δ‖ ^ 2 * (rho z ^ (-(s + 2)) + 1) ≤
        Cτ * L ^ 2 * κ⁻¹ ^ 2 * (periodicRiesz d s z + CK) := by
      calc Cτ * ‖δ‖ ^ 2 * (rho z ^ (-(s + 2)) + 1)
          ≤ Cτ * ((κ⁻¹ * L) ^ 2 * rho z ^ 2) * (rho z ^ (-(s + 2)) + 1) := by gcongr
        _ = Cτ * L ^ 2 * κ⁻¹ ^ 2 * (rho z ^ 2 * rho z ^ (-(s + 2)) + rho z ^ 2) := by ring
        _ = Cτ * L ^ 2 * κ⁻¹ ^ 2 * (rho z ^ (-s) + rho z ^ 2) := by rw [rho_sq_rpow hz]
        _ ≤ Cτ * L ^ 2 * κ⁻¹ ^ 2 * (periodicRiesz d s z + CK) :=
            mul_le_mul_of_nonneg_left (by rw [hCK]; linarith) (by positivity)
    rw [hin] at hT'
    linarith
  -- summation
  have hodd : ∀ x : Torus d, periodicRieszGrad d s (-x) = -periodicRieszGrad d s x :=
    fun x => KernelGrad.periodicRieszGrad_neg_of_lt hsd x
  have h0 := first_order_zero hn (periodicRieszGrad d s) hodd (fun i => a (latCfg n i))
  set SZ : ℝ := ∑ i, ∑ j ∈ Finset.univ.erase i, periodicRiesz d s (latCfg n i - latCfg n j) with hSZ
  have hsum : ∑ i, ∑ j ∈ Finset.univ.erase i,
        periodicRiesz d s (perturbedLattice n κ a i - perturbedLattice n κ a j) ≤
      ∑ i, ∑ j ∈ Finset.univ.erase i,
        (periodicRiesz d s (latCfg n i - latCfg n j) +
          κ⁻¹ * inner ℝ (periodicRieszGrad d s (latCfg n i - latCfg n j))
            (a (latCfg n i) - a (latCfg n j)) +
          Cτ * L ^ 2 * κ⁻¹ ^ 2 * (periodicRiesz d s (latCfg n i - latCfg n j) + CK)) := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj => ?_
    exact hpair i j (fun h => (Finset.ne_of_mem_erase hj) h.symm)
  refine hsum.trans ?_
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [h0, mul_zero, add_zero]
  have e : ∑ x, ∑ x_1 ∈ Finset.univ.erase x, periodicRiesz d s (latCfg n x - latCfg n x_1) = SZ := rfl
  rw [e]
  have hcard : ∑ x : Fin (n ^ d), ∑ _y ∈ Finset.univ.erase x, CK ≤ N ^ 2 * CK := by
    calc ∑ x : Fin (n ^ d), ∑ _y ∈ Finset.univ.erase x, CK ≤ ∑ x : Fin (n ^ d), ∑ _y : Fin (n ^ d), CK :=
          Finset.sum_le_sum fun x _ => Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            (fun _ _ _ => hCK0)
      _ = N ^ 2 * CK := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [hN]; ring
  have hlog : 0 ≤ (if s = 0 then Real.log n else 0) := by
    split_ifs
    · exact Real.log_nonneg hn'
    · exact le_rfl
  have hns : (n : ℝ) ^ s ≤ N := by
    have := Real.rpow_le_rpow_of_exponent_le hn' hsd.le
    rw [Real.rpow_natCast] at this
    rw [hN]; push_cast; exact this
  have hSZ2 : SZ ≤ C₂ * N ^ 2 := by
    refine (hC₂ n hn).trans ?_
    rw [← hN]
    have hN0 : 0 ≤ N := by linarith
    calc N * (C₂ * (n : ℝ) ^ s - (if s = 0 then Real.log n else 0)) ≤ N * (C₂ * (n : ℝ) ^ s) := by
          gcongr; linarith
      _ ≤ N * (C₂ * N) := by gcongr
      _ = C₂ * N ^ 2 := by ring
  have hfac : 0 ≤ Cτ * L ^ 2 * κ⁻¹ ^ 2 := by positivity
  have h1 := mul_le_mul_of_nonneg_left (add_le_add hSZ2 hcard) hfac
  nlinarith [h1]

theorem rieszEnergy_eq_pairs {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {N : ℕ}
    (X : Config d N) :
    rieszEnergy d s X volume = (1 / (2 * (N : ℝ) ^ 2)) *
      ∑ i, ∑ j ∈ Finset.univ.erase i, periodicRiesz d s (X i - X j) := by
  haveI : (volume : Measure (Torus d)).IsNegInvariant :=
    MeasureTheory.Measure.pi.isNegInvariant (fun _ : Fin d => (volume : Measure UnitAddCircle))
  have h0 : ∀ x : Torus d, ∫ y, periodicRiesz d s (x - y) = 0 := by
    intro x
    rw [integral_sub_left_eq_self (fun z => periodicRiesz d s z) (volume : Measure (Torus d)) x]
    rcases Nat.eq_or_lt_of_le hd with hd1 | hd2
    · subst hd1
      exact (integral_periodicRiesz_d1 hs0 (by simpa using hsd)).2
    · exact (integral_periodicRiesz hd2 hs0 hsd).2
  unfold rieszEnergy modulatedEnergyKernel modulatedEnergy
  simp [h0]

theorem perturbedLattice_energy_aux {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (C₀ : ℝ)
    {a : Torus d → Euc d} (ha : Torus.IsSmooth a) :
    ∃ κ₀ C : ℝ, 0 < κ₀ ∧ ∀ n : ℕ, 2 ≤ n → ∀ κ : ℝ, κ₀ ≤ κ →
      rieszEnergy d s (perturbedLattice n κ a) volume + oN d s C₀ (n ^ d) ≤
        C * (κ⁻¹ ^ 2 + ((n ^ d : ℕ) : ℝ) ^ (s / d - 1)) := by
  obtain ⟨κ₀, C₁, hκ₀, hC₁0, hC₁⟩ := perturb_pair_sum (s := s) hd hs0 hsd ha
  obtain ⟨C₂, hC₂0, hC₂⟩ := lattice_pair_sum (s := s) hd hs0 hsd
  refine ⟨κ₀, C₁ / 2 + C₂ / 2 + |C₀|, hκ₀, fun n hn κ hκ => ?_⟩
  have hn0 : 0 < n := by omega
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  set N : ℝ := ((n ^ d : ℕ) : ℝ) with hN
  have hN' : N = (n : ℝ) ^ d := by rw [hN]; push_cast; rfl
  have hN0 : 0 < N := by positivity
  rw [rieszEnergy_eq_pairs hd hs0 hsd]
  have h1 := hC₁ n hn0 κ hκ
  have h2 := hC₂ n hn0
  have hκ0 : 0 ≤ κ⁻¹ ^ 2 := by positivity
  -- the pair sum
  set SY := ∑ i, ∑ j ∈ Finset.univ.erase i,
    periodicRiesz d s (perturbedLattice n κ a i - perturbedLattice n κ a j) with hSY
  have hSY2 : SY ≤ N * (C₂ * (n : ℝ) ^ s - (if s = 0 then Real.log n else 0)) + C₁ * κ⁻¹ ^ 2 * N ^ 2 :=
    h1.trans (by linarith [h2])
  have hpow : N ^ (s / d - 1) = (n : ℝ) ^ s / N := by
    rw [Real.rpow_sub hN0, Real.rpow_one, hN', ← Real.rpow_natCast, ← Real.rpow_mul hn'.le]
    congr 2
    field_simp
  have hF : 1 / (2 * N ^ 2) * SY ≤ C₂ / 2 * N ^ (s / d - 1) - (if s = 0 then Real.log n else 0) / (2 * N) +
      C₁ / 2 * κ⁻¹ ^ 2 := by
    have : 1 / (2 * N ^ 2) * SY ≤ 1 / (2 * N ^ 2) * (N * (C₂ * (n : ℝ) ^ s -
        (if s = 0 then Real.log n else 0)) + C₁ * κ⁻¹ ^ 2 * N ^ 2) :=
      mul_le_mul_of_nonneg_left hSY2 (by positivity)
    refine this.trans (le_of_eq ?_)
    rw [hpow]
    field_simp
  have hoN : oN d s C₀ (n ^ d) = C₀ * N ^ (s / d - 1) + (if s = 0 then Real.log n / (2 * N) else 0) := by
    unfold oN
    congr 1
    split_ifs with hs
    · rw [← hN]
      have : Real.log N = d * Real.log n := by rw [hN', Real.log_pow]
      rw [this]
      field_simp
    · rfl
  rw [hoN]
  have hite : (if s = 0 then Real.log n / (2 * N) else 0) = (if s = 0 then Real.log n else 0) / (2 * N) := by
    split_ifs <;> simp
  rw [hite]
  have hP : 0 ≤ N ^ (s / d - 1) := Real.rpow_nonneg hN0.le _
  nlinarith [mul_nonneg hC₁0 hP, mul_nonneg hC₂0 hκ0, mul_nonneg (abs_nonneg C₀) hκ0,
    mul_nonneg (sub_nonneg.mpr (le_abs_self C₀)) hP]

end LatticeEnergyAux

/-- Example A.39 (source lines 11608-11612), energy level (external: Serfaty, *Lectures on
Coulomb and Riesz gases*, Ch. 4-5; Sandier-Serfaty 2015; Petrache-Serfaty 2017; only the
order of magnitude is used): for `a ∈ C^∞` and `κ_N` large enough that `z ↦ z + κ⁻¹a(z)` is a
bi-Lipschitz perturbation, `F_N(Y_N, 1) + o_N ≤ C(κ_N^{-2} + N^{s/d-1})`. -/
theorem perturbedLattice_energy {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (C₀ : ℝ)
    (a : Torus d → Euc d) (ha : Torus.IsSmooth a) :
    ∃ κ₀ C : ℝ, 0 < κ₀ ∧ ∀ n : ℕ, 2 ≤ n → ∀ κ : ℝ, κ₀ ≤ κ →
      rieszEnergy d s (perturbedLattice n κ a) volume + oN d s C₀ (n ^ d) ≤
        C * (κ⁻¹ ^ 2 + ((n ^ d : ℕ) : ℝ) ^ (s / d - 1)) := by
  exact LatticeEnergyAux.perturbedLattice_energy_aux hd hs0 hsd C₀ ha

/-! ### `H:eq:balanced-weights` (source lines 636-646) -/

namespace InitialDataAux

lemma scale_eq (N : ℕ) (hN : 1 ≤ N) (κ invβ : ℝ) (hκ : 0 < κ) (hinvβ : 0 ≤ invβ) :
    Ascale N κ invβ = (if invβ = 0 then 1 else min 1 (κ * Real.sqrt (invβ / N))⁻¹) ∧
    qScale N κ invβ = min ((κ * Real.sqrt (invβ / N)) ^ 2) 1 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  by_cases h : invβ = 0
  · subst h
    simp [Ascale, qScale]
  · have hpos : 0 < invβ := lt_of_le_of_ne hinvβ (Ne.symm h)
    have hr : 0 < Real.sqrt (invβ / N) := Real.sqrt_pos.2 (div_pos hpos hNpos)
    have hsq : Real.sqrt (N / invβ) = (Real.sqrt (invβ / N))⁻¹ := by
      rw [← Real.sqrt_inv, inv_div]
    have hsig : sigmaScale N κ invβ = min κ (Real.sqrt (invβ / N))⁻¹ := by
      simp [sigmaScale, h, hsq]
    constructor
    · simp only [Ascale, h, ite_false, hsig]
      rw [div_eq_inv_mul, mul_min_of_nonneg _ _ (inv_nonneg.2 hκ.le), inv_mul_cancel₀ hκ.ne',
        mul_inv, mul_comm]
    · simp only [qScale, h, ite_false, hsig]
      have hsq2 : (Real.sqrt (invβ / N)) ^ 2 = invβ / N := Real.sq_sqrt (div_pos hpos hNpos).le
      have : min κ (Real.sqrt (invβ / N))⁻¹ ^ 2 = min (κ ^ 2) ((Real.sqrt (invβ / N))⁻¹ ^ 2) := by
        rcases le_total κ (Real.sqrt (invβ / N))⁻¹ with h1 | h1
        · rw [min_eq_left h1, min_eq_left (pow_le_pow_left₀ hκ.le h1 2)]
        · rw [min_eq_right h1, min_eq_right (pow_le_pow_left₀ (inv_nonneg.2 hr.le) h1 2)]
      have ht : 0 < invβ / N := div_pos hpos hNpos
      rw [this, inv_pow, hsq2, mul_pow, hsq2, mul_div_assoc, min_mul_of_nonneg _ _ ht.le,
        inv_mul_cancel₀ ht.ne', mul_comm]


lemma A_eq_of_pos (N : ℕ) (hN : 1 ≤ N) (κ invβ : ℝ) (hκ : 0 < κ) (hinvβ : 0 ≤ invβ)
    (hr : 0 < κ * Real.sqrt (invβ / N)) :
    Ascale N κ invβ = min 1 (κ * Real.sqrt (invβ / N))⁻¹ := by
  rw [(scale_eq N hN κ invβ hκ hinvβ).1]
  have : invβ ≠ 0 := by
    rintro rfl
    simp at hr
  simp [this]

lemma A_eq_one (N : ℕ) (hN : 1 ≤ N) (κ invβ : ℝ) (hκ : 0 < κ) (hinvβ : 0 ≤ invβ)
    (hr : κ * Real.sqrt (invβ / N) < 1) : Ascale N κ invβ = 1 := by
  rw [(scale_eq N hN κ invβ hκ hinvβ).1]
  by_cases h : invβ = 0
  · simp [h]
  · have hpos : 0 < invβ := lt_of_le_of_ne hinvβ (Ne.symm h)
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have h0 : 0 < κ * Real.sqrt (invβ / N) := mul_pos hκ (Real.sqrt_pos.2 (div_pos hpos hNpos))
    simp only [h, ite_false]
    exact min_eq_left (one_le_inv_iff₀.2 ⟨h0, hr.le⟩)

end InitialDataAux

open InitialDataAux
/-- `H:eq:balanced-weights` (source lines 640-645): if `κ_N / √(Nβ_N) → c ∈ (0, ∞)`
(written `κ_N √(β_N⁻¹/N) → c`), then `A_N → min{1, c⁻¹}` and `q_N → min{c², 1}`. -/
theorem balanced_weights (κ invβ : ℕ → ℝ) (hκ : ∀ N, 0 < κ N) (hinvβ : ∀ N, 0 ≤ invβ N)
    (c : ℝ) (hc : 0 < c)
    (hratio : Tendsto (fun N => κ N * Real.sqrt (invβ N / N)) atTop (𝓝 c)) :
    Tendsto (fun N => Ascale N (κ N) (invβ N)) atTop (𝓝 (min 1 c⁻¹)) ∧
      Tendsto (fun N => qScale N (κ N) (invβ N)) atTop (𝓝 (min (c ^ 2) 1)) := by
  have hev : ∀ᶠ N : ℕ in atTop, 1 ≤ N ∧ 0 < κ N * Real.sqrt (invβ N / N) :=
    (eventually_ge_atTop 1).and (hratio.eventually (lt_mem_nhds hc))
  constructor
  · have h1 : Tendsto (fun N => min 1 (κ N * Real.sqrt (invβ N / N))⁻¹) atTop (𝓝 (min 1 c⁻¹)) :=
      (tendsto_const_nhds.min (hratio.inv₀ hc.ne'))
    refine h1.congr' ?_
    filter_upwards [hev] with N hN
    exact (A_eq_of_pos N hN.1 _ _ (hκ N) (hinvβ N) hN.2).symm
  · have h1 : Tendsto (fun N => min ((κ N * Real.sqrt (invβ N / N)) ^ 2) 1) atTop
        (𝓝 (min (c ^ 2) 1)) := (hratio.pow 2).min tendsto_const_nhds
    refine h1.congr' ?_
    filter_upwards [hev] with N hN
    exact ((scale_eq N hN.1 _ _ (hκ N) (hinvβ N)).2).symm

/-- Source lines 638-640: if `κ_N / √(Nβ_N) → 0` then `A_N → 1` and `q_N → 0` (including
`β_N = ∞`, `invβ = 0`). -/
theorem balanced_weights_zero (κ invβ : ℕ → ℝ) (hκ : ∀ N, 0 < κ N) (hinvβ : ∀ N, 0 ≤ invβ N)
    (hratio : Tendsto (fun N => κ N * Real.sqrt (invβ N / N)) atTop (𝓝 0)) :
    Tendsto (fun N => Ascale N (κ N) (invβ N)) atTop (𝓝 1) ∧
      Tendsto (fun N => qScale N (κ N) (invβ N)) atTop (𝓝 0) := by
  have hev : ∀ᶠ N : ℕ in atTop, 1 ≤ N ∧ κ N * Real.sqrt (invβ N / N) < 1 :=
    (eventually_ge_atTop 1).and (hratio.eventually (gt_mem_nhds one_pos))
  constructor
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with N hN
    exact (A_eq_one N hN.1 _ _ (hκ N) (hinvβ N) hN.2).symm
  · have h1 : Tendsto (fun N => min ((κ N * Real.sqrt (invβ N / N)) ^ 2) 1) atTop
        (𝓝 (min ((0:ℝ) ^ 2) 1)) := (hratio.pow 2).min tendsto_const_nhds
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_le_one, min_eq_left] at h1
    refine h1.congr' ?_
    filter_upwards [hev] with N hN
    exact ((scale_eq N hN.1 _ _ (hκ N) (hinvβ N)).2).symm

/-- Source line 646: if `κ_N / √(Nβ_N) → ∞` then `A_N → 0` and `q_N → 1`. -/
theorem balanced_weights_infty (κ invβ : ℕ → ℝ) (hκ : ∀ N, 0 < κ N) (hinvβ : ∀ N, 0 ≤ invβ N)
    (hratio : Tendsto (fun N => κ N * Real.sqrt (invβ N / N)) atTop atTop) :
    Tendsto (fun N => Ascale N (κ N) (invβ N)) atTop (𝓝 0) ∧
      Tendsto (fun N => qScale N (κ N) (invβ N)) atTop (𝓝 1) := by
  have hev : ∀ᶠ N : ℕ in atTop, 1 ≤ N ∧ 1 < κ N * Real.sqrt (invβ N / N) :=
    (eventually_ge_atTop 1).and (hratio.eventually (eventually_gt_atTop 1))
  constructor
  · have h1 : Tendsto (fun N => min 1 (κ N * Real.sqrt (invβ N / N))⁻¹) atTop (𝓝 (min 1 0)) :=
      tendsto_const_nhds.min (tendsto_inv_atTop_zero.comp hratio)
    rw [min_eq_right zero_le_one] at h1
    refine h1.congr' ?_
    filter_upwards [hev] with N hN
    exact (A_eq_of_pos N hN.1 _ _ (hκ N) (hinvβ N) (one_pos.trans hN.2)).symm
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with N hN
    rw [(scale_eq N hN.1 _ _ (hκ N) (hinvβ N)).2]
    exact (min_eq_right (by nlinarith [hN.2])).symm

end HRS

end

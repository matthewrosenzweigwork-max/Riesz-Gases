import HRS.Equilibrium.QuadraticVariance
import HRS.Equilibrium.PairCorrection
import HRS.Equilibrium.PoleCavity
import HRS.Equilibrium.Q32cAux2
import HRS.Energy.Commutator.AbsConv
import HRS.Energy.Coercivity
import HRS.Energy.Modulated
import HRS.Sections.Q40bAux3
import HRS.Sections.Q41Aux14
import HRS.PDE.MeanFieldDecayGap
import HRS.PDE.MeanFieldLinearLoss
import HRS.PDE.EnergyTorusSqrt
import HRS.PDE.EnergyR2Fn

/-!
# Packet ME-env (row 4.17): proof of the forcing envelope M6

Proof of `forcing_envelope` of `HRS/ME/Spec417Env.lean` (statement copied verbatim as `forcing_envelope_proof`;
`HRS/ME/Spec417Env.lean` is not imported).  Helpers carry the prefix `menv_`.

Route: the kernel `h_f = commKernel (periodicRieszGrad d s) (∇f)` satisfies `|h_f(x,y)| ≤ K ‖f‖_{C²} w(x,y)` with
`w = wEnv s`; the Gibbs variance of `D_N(w; μ)` comes from `HRS.quadStat_variance` (Proposition 4.3); the kernel
fields of `w` against `μ ≤ Λ dx` are bounded by `PairCorrAux.radial_B0`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ME

variable {d : ℕ}

open HRS

/-- Mean value bound for the gradient of a `C²` test function (copy of `eqrem_lip_grad`). -/
theorem menv_lip {φ : Torus d → ℝ} (hφ : Torus.IsCk 2 φ) :
    IsLipschitzVF (Torus.cbNorm 2 φ) (Torus.grad φ) :=
  Q40b.q40b_grad_lip hφ fun y => PDE.ET.norm_iteratedFDeriv_le_cbNorm (le_refl 2) hφ y

/-- Pointwise envelope of the commutator kernel by the Riesz envelope `wEnv`, for all `x, y`. -/
theorem menv_kernel_env (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ φ : Torus d → ℝ, Torus.IsCk 2 φ → ∀ x y : Torus d,
      |commKernel (periodicRieszGrad d s) (Torus.grad φ) x y| ≤ (K * Torus.cbNorm 2 φ) * wEnv s x y := by
  obtain ⟨C, hC0, hC⟩ := Commutator.commKernel_bound (d := d) (s := s) (by omega) hs0 hsd
  refine ⟨C, hC0, fun φ hφ x y => ?_⟩
  have hL0 : 0 ≤ Torus.cbNorm 2 φ := PDE.cbNorm_nonneg' 2 φ
  have hK : 0 ≤ C * Torus.cbNorm 2 φ := mul_nonneg hC0 hL0
  by_cases hxy : x = y
  · subst hxy
    unfold commKernel
    rw [if_pos rfl, abs_zero]
    exact mul_nonneg hK (zero_le_one.trans (PairCorrAux.one_le_wEnv s x x))
  · have h1 := hC (Torus.cbNorm 2 φ) (Torus.grad φ) hL0 (menv_lip hφ) x y hxy
    have ht : KernelGrad.tdist x y = Torus.eucDist x y := by
      rw [Q40b.q40b_tdist_eq_eucDist, ← PairCorrAux.eucDist_sub_zero]
    have he : 0 ≤ Torus.eucDist x y := PairCorrAux.eucDist_nonneg' x y
    have hw : KernelGrad.tdist x y ^ (-s) + 1 ≤ wEnv s x y := by
      rw [ht]
      unfold wEnv rTrunc
      have hr : 0 ≤ Torus.eucDist x y ^ (-s) := Real.rpow_nonneg he _
      rcases le_total (Torus.eucDist x y) 1 with h1' | h1'
      · rw [min_eq_right h1']
        linarith
      · rw [min_eq_left h1', Real.one_rpow]
        have : Torus.eucDist x y ^ (-s) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos h1' (by linarith)
        linarith
    calc |commKernel (periodicRieszGrad d s) (Torus.grad φ) x y|
        ≤ C * Torus.cbNorm 2 φ * (KernelGrad.tdist x y ^ (-s) + 1) := h1
      _ ≤ C * Torus.cbNorm 2 φ * wEnv s x y := mul_le_mul_of_nonneg_left hw hK

/-- Joint measurability of the Riesz envelope `wEnv`. -/
theorem menv_wEnv_meas {s : ℝ} :
    Measurable (Function.uncurry (fun x y : Torus d => wEnv s x y)) := by
  have h1 : Measurable (fun p : Torus d × Torus d => Torus.eucDist (p.1 - p.2) 0) :=
    (PairCorrAux.continuous_eucDist' (0 : Torus d)).measurable.comp (measurable_fst.sub measurable_snd)
  have hE : Measurable (fun p : Torus d × Torus d => Torus.eucDist p.1 p.2) := by
    have hfun : (fun p : Torus d × Torus d => Torus.eucDist p.1 p.2) =
        fun p => Torus.eucDist (p.1 - p.2) 0 :=
      funext fun p => PairCorrAux.eucDist_sub_zero p.1 p.2
    rw [hfun]
    exact h1
  show Measurable (fun p : Torus d × Torus d => wEnv s p.1 p.2)
  unfold wEnv rTrunc
  exact measurable_const.add ((measurable_const.min hE).pow_const _)

/-- Joint measurability of the commutator kernel (copy of `eqrem_pairKernel_meas`). -/
theorem menv_kernel_meas {s : ℝ} (hsd : s < d) {φ : Torus d → ℝ} (hφ : Torus.IsCk 2 φ) :
    Measurable (Function.uncurry (commKernel (periodicRieszGrad d s) (Torus.grad φ))) := by
  have hvc : Continuous (Torus.grad φ) :=
    PDE.MFLinear.continuous_grad
      (PDE.ClassicalAux.isCk_of_le (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 2)) hφ)
  unfold commKernel Function.uncurry
  refine Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) measurable_const ?_
  refine Measurable.inner ?_ ?_
  · exact (hvc.measurable.comp measurable_fst).sub (hvc.measurable.comp measurable_snd)
  · exact (KernelGrad.measurable_periodicRieszGrad hsd).comp (measurable_fst.sub measurable_snd)

/-- The envelope `wEnv` dominates `1 + |x-y|^{-s}` up to the factor `2` (`s > 0`). -/
theorem menv_wEnv_abs_le {s : ℝ} (hs : 0 < s) (x y : Torus d) :
    |wEnv s x y| ≤ 2 * singEnvelope s (Torus.eucDist x y) := by
  have hw : 0 ≤ wEnv s x y := zero_le_one.trans (PairCorrAux.one_le_wEnv s x y)
  rw [abs_of_nonneg hw]
  have he : 0 ≤ Torus.eucDist x y := PairCorrAux.eucDist_nonneg' x y
  have hr : 0 ≤ Torus.eucDist x y ^ (-s) := Real.rpow_nonneg he _
  unfold singEnvelope wEnv rTrunc
  rw [if_neg hs.ne']
  rcases le_total (Torus.eucDist x y) 1 with h1 | h1
  · rw [min_eq_right h1]
    linarith
  · rw [min_eq_left h1, Real.one_rpow]
    linarith

/-- Uniform bound of the `w`-integrals against Lebesgue measure (`radial_B0`). -/
theorem menv_R0 (hd : 2 ≤ d) {s : ℝ} (hs : 0 < s) (hcrit : s = d / 2) :
    ∃ R0 : ℝ, 0 ≤ R0 ∧ ∀ x : Torus d, ∫⁻ z, ENNReal.ofReal (wEnv s x z) ≤ ENNReal.ofReal R0 := by
  refine ⟨PairCorrAux.cdR d * ((1 / (d : ℝ) + 1 / s) * 1 ^ s) + 2, ?_, fun x => PairCorrAux.radial_B0 hd hcrit x⟩
  have h1 : 0 ≤ PairCorrAux.cdR d := PairCorrAux.cdR_nonneg d
  have h2 : 0 ≤ 1 / (d : ℝ) + 1 / s := add_nonneg (by positivity) (one_div_nonneg.2 hs.le)
  have h3 : (0 : ℝ) ≤ 1 ^ s := Real.rpow_nonneg zero_le_one s
  have := mul_nonneg h1 (mul_nonneg h2 h3)
  linarith

/-- Integrability of `w(x,·)` against `μ ≤ Λ dx`, and its integral bound. -/
theorem menv_wEnv_int {s : ℝ} {μ : Measure (Torus d)} {Λ R0 : ℝ} (hΛ : 0 ≤ Λ) (hR0 : 0 ≤ R0)
    (hμ : μ ≤ ENNReal.ofReal Λ • (volume : Measure (Torus d)))
    (hR : ∀ x : Torus d, ∫⁻ z, ENNReal.ofReal (wEnv s x z) ≤ ENNReal.ofReal R0) (x : Torus d) :
    Integrable (fun y => wEnv s x y) μ ∧ ∫ y, wEnv s x y ∂μ ≤ Λ * R0 := by
  have hnn : 0 ≤ᵐ[μ] (fun y => wEnv s x y) :=
    Filter.Eventually.of_forall fun y => zero_le_one.trans (PairCorrAux.one_le_wEnv s x y)
  have hmeas : Measurable (fun y => wEnv s x y) := PairCorrAux.measurable_wEnv s x
  have hl : ∫⁻ y, ENNReal.ofReal (wEnv s x y) ∂μ ≤ ENNReal.ofReal (Λ * R0) := by
    calc ∫⁻ y, ENNReal.ofReal (wEnv s x y) ∂μ
        ≤ ∫⁻ y, ENNReal.ofReal (wEnv s x y) ∂(ENNReal.ofReal Λ • (volume : Measure (Torus d))) :=
          lintegral_mono' hμ le_rfl
      _ = ENNReal.ofReal Λ * ∫⁻ y, ENNReal.ofReal (wEnv s x y) := by
          rw [lintegral_smul_measure, smul_eq_mul]
      _ ≤ ENNReal.ofReal Λ * ENNReal.ofReal R0 := by
          gcongr
          exact hR x
      _ = ENNReal.ofReal (Λ * R0) := (ENNReal.ofReal_mul hΛ).symm
  have hfin : HasFiniteIntegral (fun y => wEnv s x y) μ := by
    rw [hasFiniteIntegral_iff_ofReal hnn]
    exact lt_of_le_of_lt hl ENNReal.ofReal_lt_top
  refine ⟨⟨hmeas.aestronglyMeasurable, hfin⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg hΛ hR0) hl

/-- Kernel field bound: `|∫ g(y) dμ(y)| ≤ c Λ R0` whenever `|g(y)| ≤ c w(x,y)`. -/
theorem menv_abs_int_le {s : ℝ} {μ : Measure (Torus d)} {Λ R0 c : ℝ} (hΛ : 0 ≤ Λ) (hR0 : 0 ≤ R0)
    (hc : 0 ≤ c) (hμ : μ ≤ ENNReal.ofReal Λ • (volume : Measure (Torus d)))
    (hR : ∀ x : Torus d, ∫⁻ z, ENNReal.ofReal (wEnv s x z) ≤ ENNReal.ofReal R0) {x : Torus d}
    {g : Torus d → ℝ} (hg : ∀ y, |g y| ≤ c * wEnv s x y) :
    |∫ y, g y ∂μ| ≤ c * (Λ * R0) := by
  obtain ⟨hint, hle⟩ := menv_wEnv_int hΛ hR0 hμ hR x
  calc |∫ y, g y ∂μ| ≤ ∫ y, |g y| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ y, c * wEnv s x y ∂μ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => abs_nonneg _) (hint.const_mul c)
          (Filter.Eventually.of_forall hg)
    _ = c * ∫ y, wEnv s x y ∂μ := integral_const_mul _ _
    _ ≤ c * (Λ * R0) := mul_le_mul_of_nonneg_left hle hc

/-- Thermal setup at one `β` (copy of the single-`β` case of `eqstat_thermal_setup`). -/
theorem menv_thermal (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ)
    (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) {ρβ : Torus d → ℝ}
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρβ) :
    ∃ hρs : SmoothPosDensity ρβ, ∃ Λ : ℝ, 0 ≤ Λ ∧ (∀ x, ρβ x ≤ Λ) ∧
      ∀ N : ℕ, canonicalGibbs (periodicRiesz d s) V N β =
        modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρβ) := by
  have hVc : Continuous V :=
    HRS.PDE.MFAux.continuous_of_isCk (ContDiff.of_le
      (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift V) from hV) (by exact_mod_cast le_top))
  obtain ⟨lam, Lam, _hlam, hb⟩ :=
    PDE.MFDecay.exists_thermal_bounds (by omega : 1 ≤ d) s hs0 hsd β β hβ le_rfl V hVc
  obtain ⟨hpos, hsm⟩ := Q41.q41_thermal_regular hd hs0 hsd hβ hV hρ
  have hρs : SmoothPosDensity ρβ := ⟨hρ.1, hsm, hpos⟩
  refine ⟨hρs, max Lam 0, le_max_right _ _, fun x =>
    (hb β ⟨le_rfl, le_rfl⟩ ρβ hρ (PoleCavityAux.continuous_of_smoothPos hρs) hpos x).2.trans
      (le_max_left _ _), fun N => ?_⟩
  obtain ⟨Λ, hΛ0, hΛ'⟩ := PoleCavityAux.exists_density_bound hρs
  refine canonicalGibbs_eq_modulatedGibbs (periodicRiesz d s) V β ρβ hρ
    (fun x => periodicRiesz_neg x) ?_
  intro x
  exact (CoercAux.J_bounds (by omega : 1 ≤ d) hs0 hsd one_pos hρs.density hΛ0.le hΛ' x).1

set_option maxHeartbeats 1000000 in
/-- M6.  `|√N (D_N(h_f; μ) - E_{ℙ_{N,β}} D_N(h_f; μ))/2| ≤ ‖f‖_{C²} (B + C₀)` on the collision complement, with
`B ≥ 0` measurable and square integrable under the canonical Gibbs law.  (`D_N = 2 · modulatedEnergy`, TeX L4914.)
Envelope: the kernel `h_f = (∇f(x) - ∇f(y))·∇g(x-y)` is bounded by `C ‖f‖_{C²} |x-y|^{-s}`; use the variance
bound of `eq_static_quadratic_proof` (as in `eqrem_context`, `HRS/MD/EQRemBridge.lean`) for `B ∈ L²`. -/
theorem forcing_envelope_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hcrit : s = d / 2)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (β : ℝ) (hβ : 0 < β) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρS : Torus.IsSmooth ρβ)
    (hρpos : ∀ x, 0 < ρβ x) {N : ℕ} (hN : 2 ≤ N) :
    ∃ B : Config d N → ℝ, Measurable B ∧ (∀ X, 0 ≤ B X) ∧
      MemLp B 2 (canonicalGibbs (periodicRiesz d s) V N β) ∧
      ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ f : Torus d → ℝ, Torus.IsSmooth f →
        ∀ X : Config d N, X ∉ collisionSet d N →
          |Real.sqrt N *
              (modulatedEnergy (commKernel (periodicRieszGrad d s) (Torus.grad f)) X (withDensityReal ρβ) -
                ∫ Y, modulatedEnergy (commKernel (periodicRieszGrad d s) (Torus.grad f)) Y
                  (withDensityReal ρβ) ∂(canonicalGibbs (periodicRiesz d s) V N β))| ≤
            Torus.cbNorm 2 f * (B X + C₀) := by
  have hs : 0 < s := by
    rw [hcrit]
    have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hN0 : (N : ℝ) ≠ 0 := by
    have : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    exact this.ne'
  have hN1 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  obtain ⟨K, hK0, hK⟩ := menv_kernel_env hd hs0 hsd
  obtain ⟨R0, hR0, hR⟩ := menv_R0 hd hs hcrit
  obtain ⟨hρs, Λ, hΛ0, hΛ, hP⟩ := menv_thermal hd hs0 hsd V hV hβ hρβ
  have hμle : withDensityReal ρβ ≤ ENNReal.ofReal Λ • (volume : Measure (Torus d)) :=
    Commutator.absConv_withDensityReal_le hΛ
  haveI hμfin : IsFiniteMeasure (withDensityReal ρβ) := ⟨by
    have h := Measure.le_iff'.1 hμle Set.univ
    rw [Measure.smul_apply, smul_eq_mul] at h
    exact lt_of_le_of_lt h (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _))⟩
  haveI hG : IsProbabilityMeasure (canonicalGibbs (periodicRiesz d s) V N β) := by
    rw [hP N]
    exact Q32c.q32c_Q_isProb hd hs0 hsd hβ (Λ := max Λ 1) (le_max_right _ _) hρs.density
      (fun x => (hΛ x).trans (le_max_left _ _)) (by omega)
  -- variance of the envelope statistic `D_N(w; μ)` under the Gibbs law
  obtain ⟨Cv, hCv⟩ := HRS.quadStat_variance hd hs0 hsd β hβ ρβ hρs
  have hw_meas : Measurable (Function.uncurry (fun x y : Torus d => wEnv s x y)) := menv_wEnv_meas
  have hvarW := hCv 2 (fun x y => wEnv s x y) hw_meas (fun x y => PairCorrAux.wEnv_symm s x y)
    (fun x y _ => menv_wEnv_abs_le hs x y) N hN (withDensityReal ρβ) (Set.mem_insert _ _)
  rw [← hP N] at hvarW
  have hfinW : evariance (fun X : Config d N => quadStat (fun x y => wEnv s x y) (withDensityReal ρβ) X)
      (canonicalGibbs (periodicRiesz d s) V N β) ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.mul_top (Nat.cast_ne_zero.2 (by omega : N ≠ 0))] at hvarW
    exact ENNReal.ofReal_ne_top (top_le_iff.1 hvarW)
  have hmemW : MemLp (fun X : Config d N => quadStat (fun x y => wEnv s x y) (withDensityReal ρβ) X) 2
      (canonicalGibbs (periodicRiesz d s) V N β) :=
    (evariance_lt_top_iff_memLp
      (HRS.Quad.measurable_quadStat (N := N) hw_meas (withDensityReal ρβ)).aestronglyMeasurable).1
      (lt_top_iff_ne_top.2 hfinW)
  -- the kernel field `Hw(x) = ∫ w(x,y) dμ(y)` is bounded
  obtain ⟨Hw, hHw⟩ : ∃ Hw : Torus d → ℝ, ∀ x, Hw x = ∫ y, wEnv s x y ∂(withDensityReal ρβ) :=
    ⟨_, fun x => rfl⟩
  have hHw_nn : ∀ x, 0 ≤ Hw x := fun x => by
    rw [hHw]
    exact integral_nonneg fun y => zero_le_one.trans (PairCorrAux.one_le_wEnv s x y)
  have hHw_le : ∀ x, Hw x ≤ Λ * R0 := fun x => by
    rw [hHw]
    exact (menv_wEnv_int hΛ0 hR0 hμle hR x).2
  have hHw_meas : Measurable Hw := by
    have hfun : Hw = fun x => ∫ y, wEnv s x y ∂(withDensityReal ρβ) := funext hHw
    rw [hfun]
    exact (hw_meas.stronglyMeasurable.integral_prod_right' (ν := withDensityReal ρβ)).measurable
  -- the pair sum `P(X) = ∑_{i≠j} w(X_i,X_j)`
  obtain ⟨P, hPdef⟩ : ∃ P : Config d N → ℝ,
      ∀ X, P X = ∑ i, ∑ j ∈ Finset.univ.erase i, wEnv s (X i) (X j) := ⟨_, fun X => rfl⟩
  have hPnn : ∀ X, 0 ≤ P X := fun X => by
    rw [hPdef]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      zero_le_one.trans (PairCorrAux.one_le_wEnv s _ _)
  have hP_meas : Measurable P := by
    have hfun : P = fun X => ∑ i, ∑ j ∈ Finset.univ.erase i, wEnv s (X i) (X j) := funext hPdef
    rw [hfun]
    refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
    exact (hw_meas.comp ((measurable_pi_apply i).prodMk (measurable_pi_apply j)) :
      Measurable fun X : Config d N => Function.uncurry (fun x y : Torus d => wEnv s x y) (X i, X j))
  have hPid : ∀ X : Config d N, P X = (N : ℝ) ^ 2 * quadStat (fun x y => wEnv s x y) (withDensityReal ρβ) X
      + 2 * N * (∑ i, Hw (X i)) - (N : ℝ) ^ 2 * ∫ x, Hw x ∂(withDensityReal ρβ) := by
    intro X
    rw [hPdef]
    unfold quadStat
    simp only [hHw]
    field_simp
    ring
  have hS_mem : MemLp (fun X : Config d N => ∑ i, Hw (X i)) 2
      (canonicalGibbs (periodicRiesz d s) V N β) := by
    refine MemLp.of_bound ?_ ((N : ℝ) * (Λ * R0)) (Filter.Eventually.of_forall fun X => ?_)
    · exact (Finset.measurable_sum _ fun i _ => hHw_meas.comp (measurable_pi_apply i)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun i _ => hHw_nn (X i))]
      calc ∑ i, Hw (X i) ≤ ∑ _i : Fin N, Λ * R0 := Finset.sum_le_sum fun i _ => hHw_le (X i)
        _ = (N : ℝ) * (Λ * R0) := by simp
  have hP_mem : MemLp P 2 (canonicalGibbs (periodicRiesz d s) V N β) := by
    have hfun : P = fun X => (N : ℝ) ^ 2 * quadStat (fun x y => wEnv s x y) (withDensityReal ρβ) X
        + 2 * N * (∑ i, Hw (X i)) - (N : ℝ) ^ 2 * ∫ x, Hw x ∂(withDensityReal ρβ) := funext hPid
    rw [hfun]
    exact ((hmemW.const_mul _).add (hS_mem.const_mul _)).sub (memLp_const _)
  -- the envelope `a(X)` of the modulated energy, constant `m = μ(𝕋^d)`
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = (withDensityReal ρβ).real Set.univ := ⟨_, rfl⟩
  have hm0 : 0 ≤ m := by rw [hm]; exact measureReal_nonneg
  obtain ⟨aF, haF⟩ : ∃ aF : Config d N → ℝ, ∀ X, aF X =
      K / (2 * (N : ℝ) ^ 2) * P X + K * (Λ * R0) * (1 + m / 2) := ⟨_, fun X => rfl⟩
  have haF_nn : ∀ X, 0 ≤ aF X := fun X => by
    rw [haF]
    have h1 : 0 ≤ K / (2 * (N : ℝ) ^ 2) := div_nonneg hK0 (by positivity)
    have h2 : 0 ≤ K * (Λ * R0) * (1 + m / 2) :=
      mul_nonneg (mul_nonneg hK0 (mul_nonneg hΛ0 hR0)) (by linarith)
    exact add_nonneg (mul_nonneg h1 (hPnn X)) h2
  have haF_fun : aF = fun X => K / (2 * (N : ℝ) ^ 2) * P X + K * (Λ * R0) * (1 + m / 2) := funext haF
  have haF_mem : MemLp aF 2 (canonicalGibbs (periodicRiesz d s) V N β) := by
    rw [haF_fun]
    exact (hP_mem.const_mul _).add (memLp_const _)
  have haF_int : Integrable aF (canonicalGibbs (periodicRiesz d s) V N β) :=
    haF_mem.integrable one_le_two
  have haF_meas : Measurable aF := by
    rw [haF_fun]
    exact (hP_meas.const_mul _).add measurable_const
  refine ⟨fun X => Real.sqrt N * aF X, ?_, ?_, ?_, ?_⟩
  · exact haF_meas.const_mul _
  · intro X
    exact mul_nonneg (Real.sqrt_nonneg _) (haF_nn X)
  · exact haF_mem.const_mul _
  refine ⟨Real.sqrt N * ∫ X, aF X ∂(canonicalGibbs (periodicRiesz d s) V N β),
    mul_nonneg (Real.sqrt_nonneg _) (integral_nonneg haF_nn), ?_⟩
  intro f hf X _
  have hf2 : Torus.IsCk 2 f :=
    ContDiff.of_le (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift f) from hf) (by norm_cast)
  have hcb0 : 0 ≤ Torus.cbNorm 2 f := PDE.cbNorm_nonneg' 2 f
  set cb := Torus.cbNorm 2 f with hcb
  set hk := commKernel (periodicRieszGrad d s) (Torus.grad f) with hkdef
  have hE : ∀ x y, |hk x y| ≤ (K * cb) * wEnv s x y := fun x y => hK f hf2 x y
  have hHf : ∀ x, |∫ y, hk x y ∂(withDensityReal ρβ)| ≤ (K * cb) * (Λ * R0) := fun x =>
    menv_abs_int_le hΛ0 hR0 (mul_nonneg hK0 hcb0) hμle hR (g := fun y => hk x y) (hE x)
  -- the constant `∬ h dμ dμ`
  have hcf : |∫ x, ∫ y, hk x y ∂(withDensityReal ρβ) ∂(withDensityReal ρβ)| ≤
      (K * cb) * (Λ * R0) * m := by
    have h := norm_integral_le_of_norm_le_const (μ := withDensityReal ρβ)
      (f := fun x => ∫ y, hk x y ∂(withDensityReal ρβ)) (C := (K * cb) * (Λ * R0))
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hHf x)
    rw [Real.norm_eq_abs, ← hm] at h
    exact h
  -- pointwise bound of the modulated energy
  have hbound : ∀ X : Config d N,
      |modulatedEnergy hk X (withDensityReal ρβ)| ≤ cb * aF X := by
    intro X
    rw [haF, hPdef]
    unfold modulatedEnergy
    have b1 : |(1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, hk (X i) (X j)| ≤
        cb * (K / (2 * (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, wEnv s (X i) (X j)) := by
      have hS : |∑ i, ∑ j ∈ Finset.univ.erase i, hk (X i) (X j)| ≤
          (K * cb) * ∑ i, ∑ j ∈ Finset.univ.erase i, wEnv s (X i) (X j) := by
        calc |∑ i, ∑ j ∈ Finset.univ.erase i, hk (X i) (X j)|
            ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, |hk (X i) (X j)| :=
              (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
          _ ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, (K * cb) * wEnv s (X i) (X j) :=
              Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hE _ _
          _ = (K * cb) * ∑ i, ∑ j ∈ Finset.univ.erase i, wEnv s (X i) (X j) := by
              simp only [Finset.mul_sum]
      rw [abs_mul, abs_of_nonneg (by positivity)]
      calc (1 / (2 * (N : ℝ) ^ 2)) * |∑ i, ∑ j ∈ Finset.univ.erase i, hk (X i) (X j)|
          ≤ (1 / (2 * (N : ℝ) ^ 2)) * ((K * cb) * ∑ i, ∑ j ∈ Finset.univ.erase i, wEnv s (X i) (X j)) :=
            mul_le_mul_of_nonneg_left hS (by positivity)
        _ = cb * (K / (2 * (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, wEnv s (X i) (X j)) := by ring
    have b2 : |(1 / (N : ℝ)) * ∑ i, ∫ y, hk (X i) y ∂(withDensityReal ρβ)| ≤ cb * (K * (Λ * R0)) := by
      have hsum : |∑ i, ∫ y, hk (X i) y ∂(withDensityReal ρβ)| ≤
          (N : ℝ) * ((K * cb) * (Λ * R0)) := by
        calc |∑ i, ∫ y, hk (X i) y ∂(withDensityReal ρβ)|
            ≤ ∑ i, |∫ y, hk (X i) y ∂(withDensityReal ρβ)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _i : Fin N, (K * cb) * (Λ * R0) := Finset.sum_le_sum fun i _ => hHf (X i)
          _ = (N : ℝ) * ((K * cb) * (Λ * R0)) := by simp
      rw [abs_mul, abs_of_nonneg (by positivity)]
      calc (1 / (N : ℝ)) * |∑ i, ∫ y, hk (X i) y ∂(withDensityReal ρβ)|
          ≤ (1 / (N : ℝ)) * ((N : ℝ) * ((K * cb) * (Λ * R0))) :=
            mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = cb * (K * (Λ * R0)) := by
            rw [← mul_assoc, one_div_mul_cancel hN0, one_mul]
            ring
    have b3 : |(1 / 2 : ℝ) * ∫ x, ∫ y, hk x y ∂(withDensityReal ρβ) ∂(withDensityReal ρβ)| ≤
        cb * (K * (Λ * R0) * (m / 2)) := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      calc (1 / 2 : ℝ) * |∫ x, ∫ y, hk x y ∂(withDensityReal ρβ) ∂(withDensityReal ρβ)|
          ≤ (1 / 2 : ℝ) * ((K * cb) * (Λ * R0) * m) := mul_le_mul_of_nonneg_left hcf (by norm_num)
        _ = cb * (K * (Λ * R0) * (m / 2)) := by ring
    calc |(1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, hk (X i) (X j)
          - (1 / (N : ℝ)) * ∑ i, ∫ y, hk (X i) y ∂(withDensityReal ρβ)
          + (1 / 2) * ∫ x, ∫ y, hk x y ∂(withDensityReal ρβ) ∂(withDensityReal ρβ)|
        ≤ |(1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, hk (X i) (X j)
          - (1 / (N : ℝ)) * ∑ i, ∫ y, hk (X i) y ∂(withDensityReal ρβ)| +
          |(1 / 2 : ℝ) * ∫ x, ∫ y, hk x y ∂(withDensityReal ρβ) ∂(withDensityReal ρβ)| := by
          have := abs_add_le ((1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, hk (X i) (X j)
            - (1 / (N : ℝ)) * ∑ i, ∫ y, hk (X i) y ∂(withDensityReal ρβ))
            ((1 / 2 : ℝ) * ∫ x, ∫ y, hk x y ∂(withDensityReal ρβ) ∂(withDensityReal ρβ))
          simpa [sub_add_eq_add_sub] using this
      _ ≤ (|(1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, hk (X i) (X j)| +
            |(1 / (N : ℝ)) * ∑ i, ∫ y, hk (X i) y ∂(withDensityReal ρβ)|) +
          |(1 / 2 : ℝ) * ∫ x, ∫ y, hk x y ∂(withDensityReal ρβ) ∂(withDensityReal ρβ)| := by
          gcongr
          exact abs_sub _ _
      _ ≤ cb * (K / (2 * (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, wEnv s (X i) (X j))
          + cb * (K * (Λ * R0)) + cb * (K * (Λ * R0) * (m / 2)) := by linarith [b1, b2, b3]
      _ = cb * (K / (2 * (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, wEnv s (X i) (X j)
          + K * (Λ * R0) * (1 + m / 2)) := by ring
  -- integrated bound
  have hI : |∫ Y, modulatedEnergy hk Y (withDensityReal ρβ) ∂(canonicalGibbs (periodicRiesz d s) V N β)| ≤
      cb * ∫ Y, aF Y ∂(canonicalGibbs (periodicRiesz d s) V N β) := by
    calc |∫ Y, modulatedEnergy hk Y (withDensityReal ρβ) ∂(canonicalGibbs (periodicRiesz d s) V N β)|
        ≤ ∫ Y, |modulatedEnergy hk Y (withDensityReal ρβ)| ∂(canonicalGibbs (periodicRiesz d s) V N β) :=
          abs_integral_le_integral_abs
      _ ≤ ∫ Y, cb * aF Y ∂(canonicalGibbs (periodicRiesz d s) V N β) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun Y => abs_nonneg _)
            (haF_int.const_mul _) (Filter.Eventually.of_forall fun Y => hbound Y)
      _ = cb * ∫ Y, aF Y ∂(canonicalGibbs (periodicRiesz d s) V N β) := integral_const_mul _ _
  calc |Real.sqrt N * (modulatedEnergy hk X (withDensityReal ρβ) -
        ∫ Y, modulatedEnergy hk Y (withDensityReal ρβ) ∂(canonicalGibbs (periodicRiesz d s) V N β))|
      = Real.sqrt N * |modulatedEnergy hk X (withDensityReal ρβ) -
        ∫ Y, modulatedEnergy hk Y (withDensityReal ρβ) ∂(canonicalGibbs (periodicRiesz d s) V N β)| := by
          rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    _ ≤ Real.sqrt N * (|modulatedEnergy hk X (withDensityReal ρβ)| +
        |∫ Y, modulatedEnergy hk Y (withDensityReal ρβ) ∂(canonicalGibbs (periodicRiesz d s) V N β)|) :=
          mul_le_mul_of_nonneg_left (abs_sub _ _) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt N * (cb * aF X + cb * ∫ Y, aF Y ∂(canonicalGibbs (periodicRiesz d s) V N β)) :=
          mul_le_mul_of_nonneg_left (add_le_add (hbound X) hI) (Real.sqrt_nonneg _)
    _ = cb * (Real.sqrt N * aF X + Real.sqrt N * ∫ Y, aF Y ∂(canonicalGibbs (periodicRiesz d s) V N β)) := by
          ring

end HRS.ME

end

import HRS.PDE.MeanFieldDefs
import HRS.PDE.MeanFieldOneLe
import HRS.PDE.MeanFieldFejer
import HRS.PDE.MeanFieldAprioriLower
import HRS.PDE.MeanFieldDecayGap
import HRS.PDE.WellPosed
import HRS.PDE.ClassicalPart
import HRS.PDE.MeanFieldAprioriSobolev
import HRS.PDE.MeanFieldSemigroup
import HRS.PDE.MeanFieldAdjointLoss

/-!
# Frozen (equilibrium) operators and `L²(μβ)` decay (package MF-01, packet P11a)

See `HRS/PDE/MeanFieldAdjointPlan.md`, packet P11a.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.MFAdjoint

variable {d : ℕ}

/-! ### Common definitions (P11-0) -/

/-- Frozen (equilibrium) data with explicit bounds, all uniform in `β`: `ν = β⁻¹ ∈ [νm, νp]`,
`V, ρβ ∈ C^n` with `C^n` norms `≤ Λ₀`, `ρβ ≥ c₀ > 0` a thermal density. -/
structure FrozenHyp (d : ℕ) (s : ℝ) (n : ℕ) (νm νp c₀ Λ₀ : ℝ) (β : ℝ) (V ρβ : Torus d → ℝ) :
    Prop where
  hs0 : 0 ≤ s
  hsd : s < d
  hβ : 0 < β
  hνm : 0 < νm
  hν : β⁻¹ ∈ Set.Icc νm νp
  hV : Torus.IsCk n V
  hVb : Torus.cbNorm n V ≤ Λ₀
  thermal : IsThermalDensity (periodicRiesz d s) V β ρβ
  hρC : Torus.IsCk n ρβ
  hρb : Torus.cbNorm n ρβ ≤ Λ₀
  hc₀ : 0 < c₀
  hlow : ∀ x, c₀ ≤ ρβ x

theorem FrozenHyp.mono {s : ℝ} {n n' : ℕ} (h : n' ≤ n) {νm νp c₀ Λ₀ β : ℝ} {V ρβ : Torus d → ℝ}
    (H : FrozenHyp d s n νm νp c₀ Λ₀ β V ρβ) : FrozenHyp d s n' νm νp c₀ Λ₀ β V ρβ := by
  have hc : ((n' : ℕ) : WithTop ℕ∞) ≤ (n : ℕ) := by exact_mod_cast h
  exact ⟨H.hs0, H.hsd, H.hβ, H.hνm, H.hν, H.hV.of_le hc, (cbNorm_monoU h V).trans H.hVb, H.thermal,
    H.hρC.of_le hc, (cbNorm_monoU h ρβ).trans H.hρb, H.hc₀, H.hlow⟩

/-- The frozen propagator at the coefficient level, terminal time `= τ` (time-homogeneous). -/
def frozenCoeff (D : DynData d) (ρβ : Torus d → ℝ) (m : ℕ) (ψc : Coeff d) (τ : ℝ) : Coeff d :=
  propagatorCoeff D (fun _ => ρβ) m τ ψc τ

/-! ### P11a — frozen operators and `L²(μβ)` decay -/

section Kernel

variable {ρ : Torus d → ℝ}

theorem pair_mu (h : IsProbDensity ρ) (f : Torus d → ℝ) :
    pair (withDensityReal ρ) f = ∫ y, ρ y * f y :=
  MFSemigroup.pair_withDensityReal h f

theorem l2Inner_mu (h : IsProbDensity ρ) (f g : Torus d → ℝ) :
    l2Inner (withDensityReal ρ) f g = ∫ x, ρ x * (f x * g x) :=
  integral_withDensityReal_eq ρ h.measurable h.nonneg _

theorem integrable_of_cont {f : Torus d → ℝ} (hf : Continuous f) : Integrable f :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem integral_rho (h : IsProbDensity ρ) : ∫ y, ρ y = 1 := h.integral_one

theorem phi_eq (g : Torus d → ℝ) (h : IsProbDensity ρ) (f : Torus d → ℝ) :
    (fun x => ∫ y, g (x - y) * f y ∂(withDensityReal ρ)) =
      convFun g (fun y => ρ y * f y) := by
  funext x
  rw [integral_withDensityReal_eq ρ h.measurable h.nonneg]
  unfold convFun
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  ring

/-- `K f = Φ f - μ(Φ f)` with `Φ f = g ⋆ (ρ f)`. -/
theorem kop_eq (s : ℝ) (h : IsProbDensity ρ) (f : Torus d → ℝ) :
    Kop (periodicRiesz d s) (withDensityReal ρ) f =
      fun x => convFun (periodicRiesz d s) (fun y => ρ y * f y) x -
        pair (withDensityReal ρ) (convFun (periodicRiesz d s) (fun y => ρ y * f y)) := by
  unfold Kop projMean
  rw [phi_eq _ h f]

theorem integrable_conv_prod {g a b : Torus d → ℝ} (hg : Integrable g) (ha : Continuous a)
    (hb : Continuous b) :
    Integrable (fun p : Torus d × Torus d => g (p.1 - p.2) * a p.2 * b p.1) (volume.prod volume) := by
  have hI : Integrable (fun p : Torus d × Torus d => a p.2 * g (p.1 - p.2)) (volume.prod volume) :=
    Integrable.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) (integrable_of_cont ha) hg
  obtain ⟨B, hB⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn hb.continuousOn
  have := hI.bdd_mul (c := B) (f := fun p : Torus d × Torus d => b p.1)
    (hb.comp continuous_fst).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => hB p.1 (Set.mem_univ _))
  refine this.congr (Filter.Eventually.of_forall fun p => ?_)
  simp only
  ring

theorem integral_convFun_mul_swap {g a b : Torus d → ℝ} (hg : Integrable g)
    (hge : ∀ x, g (-x) = g x) (ha : Continuous a) (hb : Continuous b) :
    ∫ x, convFun g a x * b x = ∫ x, a x * convFun g b x := by
  have hF := integrable_conv_prod hg ha hb
  have h1 : ∫ x, convFun g a x * b x = ∫ x, ∫ y, g (x - y) * a y * b x := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [convFun]
    rw [← integral_mul_const]
  have h2 : ∫ x, a x * convFun g b x = ∫ y, ∫ x, g (x - y) * a y * b x := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [convFun]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    have := hge (x - y)
    rw [neg_sub] at this
    rw [← this]
    ring
  rw [h1, h2]
  exact integral_integral_swap hF

theorem continuous_conv_kernel (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) {a : Torus d → ℝ}
    (ha : Continuous a) : Continuous (convFun (periodicRiesz d s) a) :=
  MFAux.continuous_convFun (MFOneLe.integrable_periodicRiesz hd s hs0 hsd) ha

/-- For `h` centered, `⟨K f, h⟩_{L²(μ)} = ∫ (g ⋆ (ρ f)) ρ h`. -/
theorem l2Inner_kop_of_centered (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (hprob : IsProbDensity ρ) (hρc : Continuous ρ) (f h : Torus d → ℝ) (hf : Continuous f)
    (hh : Continuous h) (hh0 : pair (withDensityReal ρ) h = 0) :
    l2Inner (withDensityReal ρ) (Kop (periodicRiesz d s) (withDensityReal ρ) f) h =
      ∫ x, convFun (periodicRiesz d s) (fun y => ρ y * f y) x * (ρ x * h x) := by
  have hF := continuous_conv_kernel hd s hs0 hsd (hρc.mul hf)
  rw [l2Inner_mu hprob, kop_eq s hprob f]
  rw [pair_mu hprob] at hh0
  have e : ∀ x, ρ x * ((convFun (periodicRiesz d s) (fun y => ρ y * f y) x -
        pair (withDensityReal ρ) (convFun (periodicRiesz d s) (fun y => ρ y * f y))) * h x) =
      convFun (periodicRiesz d s) (fun y => ρ y * f y) x * (ρ x * h x) -
        pair (withDensityReal ρ) (convFun (periodicRiesz d s) (fun y => ρ y * f y)) * (ρ x * h x) := by
    intro x; ring
  simp_rw [e]
  rw [integral_sub, integral_const_mul, hh0, mul_zero, sub_zero]
  · exact integrable_of_cont (hF.mul (hρc.mul hh))
  · exact integrable_of_cont (continuous_const.mul (hρc.mul hh))

theorem l2Inner_comm' (μ : Measure (Torus d)) (f g : Torus d → ℝ) :
    l2Inner μ f g = l2Inner μ g f := by
  unfold l2Inner
  simp_rw [mul_comm (f _)]

/-- `K_β` is symmetric on `L²_0(μβ)` (even kernel, Fubini).  The statement of the plan without the
centering hypotheses is false: `⟨K f,h⟩ - ⟨f,K h⟩ = μ(f) μ(Φ h) - μ(h) μ(Φ f)`. -/
theorem l2Inner_kop_symm' (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (ρβ : Torus d → ℝ)
    (hprob : IsProbDensity ρβ) (hρc : Continuous ρβ) (f h : Torus d → ℝ) (hf : Continuous f)
    (hh : Continuous h) (hf0 : pair (withDensityReal ρβ) f = 0)
    (hh0 : pair (withDensityReal ρβ) h = 0) :
    l2Inner (withDensityReal ρβ) (Kop (periodicRiesz d s) (withDensityReal ρβ) f) h =
      l2Inner (withDensityReal ρβ) f (Kop (periodicRiesz d s) (withDensityReal ρβ) h) := by
  rw [l2Inner_comm' _ f, l2Inner_kop_of_centered hd s hs0 hsd hprob hρc f h hf hh hh0,
    l2Inner_kop_of_centered hd s hs0 hsd hprob hρc h f hh hf hf0]
  have := integral_convFun_mul_swap (MFOneLe.integrable_periodicRiesz hd s hs0 hsd)
    (fun x => periodicRiesz_neg x) (a := fun y => ρβ y * f y) (b := fun y => ρβ y * h y)
    (hρc.mul hf) (hρc.mul hh)
  rw [this]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  ring

/-- `⟨K_β f, f⟩_{L²(μβ)} = ∑_{k≠0} ĝ(k)|(ρβ f)^(k)|² ≥ 0` for `μβ`-centered `f`
(`C:eq:K-positive`).  The statement of the plan without `pair μβ f = 0` is false. -/
theorem l2Inner_kop_nonneg' (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (ρβ : Torus d → ℝ)
    (hprob : IsProbDensity ρβ) (hρc : Continuous ρβ) (f : Torus d → ℝ) (hf : Continuous f)
    (hf0 : pair (withDensityReal ρβ) f = 0) :
    0 ≤ l2Inner (withDensityReal ρβ) (Kop (periodicRiesz d s) (withDensityReal ρβ) f) f := by
  rw [l2Inner_kop_of_centered hd s hs0 hsd hprob hρc f f hf hf hf0]
  have h := MFThermalExist.integral_convFun_mul_self_nonneg' hd s hs0 hsd
    (MFThermalAssembly.kernelFacts hd s hs0 hsd) (z := fun y => ρβ y * f y) (hρc.mul hf)
  simpa only [mul_assoc] using h

theorem norm_coeffOf_le_integral {g : Torus d → ℝ} (k : Lattice d) :
    ‖coeffOf g k‖ ≤ ∫ x, ‖g x‖ := by
  unfold coeffOf
  rw [funFourierCoeff_eq_int]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq (integral_congr_ae
    (Filter.Eventually.of_forall fun x => ?_)))
  simp only [norm_mul, Complex.norm_real]
  have : ‖UnitAddTorus.mFourier (-k) x‖ = 1 := by
    simpa [Torus.mode] using Torus.norm_mode (-k) x
  rw [this, one_mul]

/-- Young: `‖g ⋆ a‖_{L²} ≤ ‖g‖_{L¹} ‖a‖_{L²}` (via Parseval). -/
theorem integral_sq_convFun_le {g a : Torus d → ℝ} (hg : Integrable g) (ha : Continuous a) :
    ∫ x, (convFun g a x) ^ 2 ≤ (∫ x, ‖g x‖) ^ 2 * ∫ x, a x ^ 2 := by
  have hF : Continuous (convFun g a) := MFAux.continuous_convFun hg ha
  have h1 := MFDecay.hasSum_norm_sq_coeffOf _ hF
  have h2 := (MFDecay.hasSum_norm_sq_coeffOf _ ha).mul_left ((∫ x, ‖g x‖) ^ 2)
  refine hasSum_le (fun k => ?_) h1 h2
  have e : coeffOf (convFun g a) k = Torus.funFourierCoeff (fun x => (g x : ℂ)) k * coeffOf a k := by
    unfold coeffOf
    exact MFAux.funFourierCoeff_convFun hg ha k
  rw [e, norm_mul, mul_pow]
  have hgk : ‖Torus.funFourierCoeff (fun x => (g x : ℂ)) k‖ ≤ ∫ x, ‖g x‖ :=
    norm_coeffOf_le_integral k
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hgk 2) (sq_nonneg _)

/-- Schur/Young: `‖K_β f‖_{L²(μβ)} ≤ C Λ₀ ‖f‖_{L²(μβ)}` for `ρβ ≤ Λ₀` (`g ∈ L¹`). -/
theorem exists_kop_bound (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρβ : Torus d → ℝ), IsProbDensity ρβ → Continuous ρβ →
      ∀ Λ₀ : ℝ, (∀ x, ρβ x ≤ Λ₀) → ∀ f : Torus d → ℝ, Continuous f →
        l2Inner (withDensityReal ρβ) (Kop (periodicRiesz d s) (withDensityReal ρβ) f)
            (Kop (periodicRiesz d s) (withDensityReal ρβ) f) ≤
          C * Λ₀ ^ 2 * l2Inner (withDensityReal ρβ) f f := by
  have hg := MFOneLe.integrable_periodicRiesz hd s hs0 hsd
  refine ⟨(∫ x, ‖periodicRiesz d s x‖) ^ 2, sq_nonneg _, fun ρβ hprob hρc Λ₀ hΛ f hf => ?_⟩
  set G := ∫ x, ‖periodicRiesz d s x‖ with hG
  have hΛ0 : 0 ≤ Λ₀ := (hprob.nonneg 0).trans (hΛ 0)
  set F := convFun (periodicRiesz d s) (fun y => ρβ y * f y) with hFdef
  have hFc : Continuous F := continuous_conv_kernel hd s hs0 hsd (hρc.mul hf)
  set c := pair (withDensityReal ρβ) F with hc
  have hcF : c = ∫ x, ρβ x * F x := pair_mu hprob F
  rw [l2Inner_mu hprob, l2Inner_mu hprob, kop_eq s hprob f]
  simp only
  -- step 1: ∫ ρ (F-c)² ≤ ∫ ρ F²
  have hρi : Integrable ρβ := integrable_of_cont hρc
  have iρF : Integrable (fun x => ρβ x * F x) := integrable_of_cont (hρc.mul hFc)
  have iρFF : Integrable (fun x => ρβ x * (F x * F x)) := integrable_of_cont (hρc.mul (hFc.mul hFc))
  have step1 : ∫ x, ρβ x * ((F x - c) * (F x - c)) ≤ ∫ x, ρβ x * (F x * F x) := by
    have e : ∀ x, ρβ x * ((F x - c) * (F x - c)) =
        (ρβ x * (F x * F x) - (2 * c) * (ρβ x * F x)) + c ^ 2 * ρβ x := fun x => by ring
    have i1 : Integrable (fun x => ρβ x * (F x * F x) - (2 * c) * (ρβ x * F x)) :=
      iρFF.sub (iρF.const_mul _)
    have i2 : Integrable (fun x => c ^ 2 * ρβ x) := hρi.const_mul _
    simp_rw [e]
    rw [integral_add i1 i2, integral_sub iρFF (iρF.const_mul _), integral_const_mul,
      integral_const_mul, ← hcF, hprob.integral_one]
    nlinarith [sq_nonneg c]
  -- step 2: ∫ ρ F² ≤ Λ₀ ∫ F²
  have iFF : Integrable (fun x => F x * F x) := integrable_of_cont (hFc.mul hFc)
  have step2 : ∫ x, ρβ x * (F x * F x) ≤ Λ₀ * ∫ x, F x * F x := by
    rw [← integral_const_mul]
    refine integral_mono iρFF (iFF.const_mul _) fun x => ?_
    exact mul_le_mul_of_nonneg_right (hΛ x) (mul_self_nonneg _)
  -- step 3: Young
  have step3 : ∫ x, F x * F x ≤ G ^ 2 * ∫ x, (ρβ x * f x) * (ρβ x * f x) := by
    have := integral_sq_convFun_le (a := fun y => ρβ y * f y) hg (hρc.mul hf)
    have e1 : ∀ x, convFun (periodicRiesz d s) (fun y => ρβ y * f y) x ^ 2 =
        F x * F x := fun x => sq _
    have e2 : ∀ x, (fun y => ρβ y * f y) x ^ 2 = (ρβ x * f x) * (ρβ x * f x) := fun x => sq _
    simp_rw [e1, e2] at this
    exact this
  -- step 4
  have step4 : ∫ x, (ρβ x * f x) * (ρβ x * f x) ≤ Λ₀ * ∫ x, ρβ x * (f x * f x) := by
    rw [← integral_const_mul]
    refine integral_mono (integrable_of_cont ((hρc.mul hf).mul (hρc.mul hf)))
      ((integrable_of_cont (hρc.mul (hf.mul hf))).const_mul _) fun x => ?_
    have h0 := hprob.nonneg x
    have h1 := mul_nonneg (mul_nonneg (sub_nonneg.2 (hΛ x)) h0) (mul_self_nonneg (f x))
    nlinarith [h1]
  have hL0 : 0 ≤ ∫ x, ρβ x * (f x * f x) :=
    integral_nonneg fun x => mul_nonneg (hprob.nonneg x) (mul_self_nonneg _)
  calc ∫ x, ρβ x * ((F x - c) * (F x - c)) ≤ Λ₀ * (G ^ 2 * (Λ₀ * ∫ x, ρβ x * (f x * f x))) :=
        step1.trans (step2.trans (mul_le_mul_of_nonneg_left
          (step3.trans (mul_le_mul_of_nonneg_left step4 (sq_nonneg G))) hΛ0))
    _ = G ^ 2 * Λ₀ ^ 2 * ∫ x, ρβ x * (f x * f x) := by ring

/-- Weighted Poincaré: `cP ∫ ρβ f² ≤ ∫ ρβ |∇f|²` for `μβ`-centered `C¹` functions,
`c₀ ≤ ρβ ≤ Λ₀`. -/
theorem exists_weighted_poincare (c₀ Λ₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ cP : ℝ, 0 < cP ∧ ∀ (ρβ : Torus d → ℝ), IsProbDensity ρβ → Continuous ρβ →
      (∀ x, c₀ ≤ ρβ x) → (∀ x, ρβ x ≤ Λ₀) → ∀ f : Torus d → ℝ, Torus.IsCk 1 f →
        pair (withDensityReal ρβ) f = 0 →
        cP * l2Inner (withDensityReal ρβ) f f ≤ ∫ x, ρβ x * ‖Torus.grad f x‖ ^ 2 := by
  set Λ' := max Λ₀ 1 with hΛ'
  have hΛ'0 : 0 < Λ' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hπ : 0 < 4 * Real.pi ^ 2 := by positivity
  refine ⟨4 * Real.pi ^ 2 * c₀ / Λ', by positivity, fun ρβ hprob hρc hlow hup f hf hf0 => ?_⟩
  have hfc : Continuous f := MFAux.continuous_of_isCk hf
  set m := ∫ y, f y with hm
  rw [pair_mu hprob] at hf0
  rw [l2Inner_mu hprob]
  have iρ : Integrable ρβ := integrable_of_cont hρc
  have iρf : Integrable (fun x => ρβ x * f x) := integrable_of_cont (hρc.mul hfc)
  have iρff : Integrable (fun x => ρβ x * (f x * f x)) := integrable_of_cont (hρc.mul (hfc.mul hfc))
  -- (1) ∫ρ f² ≤ ∫ ρ (f-m)²
  have h1 : ∫ x, ρβ x * (f x * f x) ≤ ∫ x, ρβ x * ((f x - m) * (f x - m)) := by
    have e : ∀ x, ρβ x * ((f x - m) * (f x - m)) =
        (ρβ x * (f x * f x) - (2 * m) * (ρβ x * f x)) + m ^ 2 * ρβ x := fun x => by ring
    have i1 : Integrable (fun x => ρβ x * (f x * f x) - (2 * m) * (ρβ x * f x)) :=
      iρff.sub (iρf.const_mul _)
    have i2 : Integrable (fun x => m ^ 2 * ρβ x) := iρ.const_mul _
    simp_rw [e]
    rw [integral_add i1 i2, integral_sub iρff (iρf.const_mul _), integral_const_mul,
      integral_const_mul, hf0, hprob.integral_one]
    nlinarith [sq_nonneg m]
  -- (2) ∫ ρ (f-m)² ≤ Λ' ∫ (f-m)²
  have iff : Integrable (fun x => (f x - m) * (f x - m)) :=
    integrable_of_cont ((hfc.sub continuous_const).mul (hfc.sub continuous_const))
  have h2 : ∫ x, ρβ x * ((f x - m) * (f x - m)) ≤ Λ' * ∫ x, (f x - m) ^ 2 := by
    rw [← integral_const_mul]
    refine integral_mono (integrable_of_cont (hρc.mul ((hfc.sub continuous_const).mul
      (hfc.sub continuous_const)))) ((integrable_of_cont ((hfc.sub continuous_const).pow 2)).const_mul _)
      fun x => ?_
    rw [← sq]
    exact mul_le_mul_of_nonneg_right ((hup x).trans (le_max_left _ _)) (sq_nonneg _)
  -- (3) Poincaré
  have h3 := MFApriori.poincare_sq hf
  -- (4) ∫|∇f|² ≤ c₀⁻¹ ∫ρ|∇f|²
  have hgc := MFApriori.continuous_norm_grad_sq hf
  have h4 : c₀ * ∫ x, ‖Torus.grad f x‖ ^ 2 ≤ ∫ x, ρβ x * ‖Torus.grad f x‖ ^ 2 := by
    rw [← integral_const_mul]
    exact integral_mono ((integrable_of_cont hgc).const_mul _) (integrable_of_cont (hρc.mul hgc))
      fun x => mul_le_mul_of_nonneg_right (hlow x) (sq_nonneg _)
  have key : ∫ x, ρβ x * (f x * f x) ≤ Λ' * ((4 * Real.pi ^ 2)⁻¹ * ∫ x, ‖Torus.grad f x‖ ^ 2) :=
    h1.trans (h2.trans (mul_le_mul_of_nonneg_left h3 hΛ'0.le))
  have : 4 * Real.pi ^ 2 * c₀ / Λ' * ∫ x, ρβ x * (f x * f x) ≤
      4 * Real.pi ^ 2 * c₀ / Λ' * (Λ' * ((4 * Real.pi ^ 2)⁻¹ * ∫ x, ‖Torus.grad f x‖ ^ 2)) :=
    mul_le_mul_of_nonneg_left key (by positivity)
  refine this.trans ?_
  have e : 4 * Real.pi ^ 2 * c₀ / Λ' * (Λ' * ((4 * Real.pi ^ 2)⁻¹ * ∫ x, ‖Torus.grad f x‖ ^ 2)) =
      c₀ * ∫ x, ‖Torus.grad f x‖ ^ 2 := by
    field_simp
  rw [e]
  exact h4

/-- At a zero of a nonnegative `C¹` function the partial derivatives vanish. -/
theorem partialDeriv_eq_zero_of_zero (hρ0 : ∀ x, 0 ≤ ρ x) (j : Fin d)
    {x : Torus d} (hx : ρ x = 0) : Torus.partialDeriv j ρ x = 0 := by
  have hmin : IsLocalMin (Torus.lift ρ) (Torus.rep x) := by
    refine Filter.Eventually.of_forall fun y => ?_
    simp only [Torus.lift, Function.comp, Torus.mk_rep, hx]
    exact hρ0 _
  have := hmin.fderiv_eq_zero
  unfold Torus.partialDeriv
  rw [this]
  rfl

/-- `ρ · L_ρ f = - Div(ρ ∇f)` (also where `ρ = 0`). -/
theorem rho_mul_lop (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : Torus.IsCk 1 ρ) (f : Torus d → ℝ)
    (hf : Torus.IsCk 2 f) (x : Torus d) :
    ρ x * Lop ρ f x = -∑ j, Torus.partialDeriv j (fun y => ρ y * Torus.partialDeriv j f y) x := by
  unfold Lop
  rw [MFAux.div_smul_grad ρ f hρ1 hf x]
  by_cases hx : ρ x = 0
  · rw [hx, zero_mul]
    have hP : ∀ j, Torus.partialDeriv j (fun y => ρ y * Torus.partialDeriv j f y) x = 0 := by
      intro j
      rw [MFAux.partialDeriv_mul j ρ _ hρ1 (isCk_one_partialDeriv j f hf) x,
        partialDeriv_eq_zero_of_zero hρ0 j hx, hx]
      ring
    simp [hP]
  · field_simp

/-- `⟨L_β f, h⟩_{L²(μβ)} = ∫ ρβ ∇f·∇h` (integration by parts); in particular `μβ(L_β f) = 0`. -/
theorem l2Inner_lop_eq (ρβ : Torus d → ℝ) (hρ : IsProbDensity ρβ) (hρ1 : Torus.IsCk 1 ρβ)
    (f h : Torus d → ℝ) (hf : Torus.IsCk 2 f) (hh : Torus.IsCk 1 h) :
    l2Inner (withDensityReal ρβ) (Lop ρβ f) h =
      ∫ x, ρβ x * inner ℝ (Torus.grad f x) (Torus.grad h x) := by
  rw [l2Inner_mu hρ]
  have hhc : Continuous h := MFAux.continuous_of_isCk hh
  have e : ∀ x, ρβ x * (Lop ρβ f x * h x) =
      -(∑ j, Torus.partialDeriv j (fun y => ρβ y * Torus.partialDeriv j f y) x * h x) := by
    intro x
    have := rho_mul_lop hρ.nonneg hρ1 f hf x
    rw [← mul_assoc, this, neg_mul, Finset.sum_mul]
  have hP : ∀ j, Torus.IsCk 1 (fun y => ρβ y * Torus.partialDeriv j f y) := fun j =>
    MFAux.isCk_mul_partialDeriv ρβ f hρ1 hf j
  have ibp : ∀ j, ∫ x, Torus.partialDeriv j (fun y => ρβ y * Torus.partialDeriv j f y) x * h x =
      -∫ x, ρβ x * Torus.partialDeriv j f x * Torus.partialDeriv j h x := by
    intro j
    exact integral_partialDeriv_mul j _ h (hP j) hh
  simp_rw [e]
  rw [integral_neg]
  have ic : ∀ j, Integrable (fun x => Torus.partialDeriv j (fun y => ρβ y * Torus.partialDeriv j f y) x * h x) :=
    fun j => integrable_of_cont ((continuous_partialDeriv j _ (hP j)).mul hhc)
  rw [integral_finsetSum _ (fun j _ => ic j)]
  simp_rw [ibp]
  rw [Finset.sum_neg_distrib, neg_neg]
  simp_rw [MFApriori.inner_grad_grad, Finset.mul_sum]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun j _ => ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    ring
  · intro j _
    exact integrable_of_cont ((MFAux.continuous_of_isCk hρ1).mul
      ((continuous_partialDeriv j f (hf.of_le (by norm_num))).mul (continuous_partialDeriv j h hh)))

end Kernel

end HRS.PDE.MFAdjoint

import HRS.PDE.Convention
import HRS.PDE.TorusCalculus
import HRS.PDE.Fourier
import HRS.Energy.Modulated

/-!
# Auxiliary lemmas for `C:eq:operator-order` (package MF-01)

Convolution with the integrable kernel `g = periodicRiesz d s` on the torus: continuity,
Fourier coefficients, and uniqueness of continuous functions with given Fourier coefficients.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.MFAux

variable {d : ℕ}

instance instIsNegInvariantTorus : (volume : Measure (Torus d)).IsNegInvariant := by
  show (Measure.pi fun _ : Fin d => (volume : Measure UnitAddCircle)).IsNegInvariant
  exact Measure.pi.isNegInvariant _

/-- The periodic Riesz kernel is integrable (a consequence of `periodicRiesz_fourierCoeff`: a
nonzero Fourier coefficient forces the defining Bochner integral to exist). -/
theorem integrable_periodicRiesz (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) :
    Integrable (periodicRiesz d s) := by
  have hd0 : 0 < d := by omega
  set k : Lattice d := Pi.single (⟨0, hd0⟩ : Fin d) 1 with hk
  have hk0 : k ≠ 0 := by
    intro h
    have := congrFun h ⟨0, hd0⟩
    simp [hk] at this
  have hpos := rieszCoeff_pos hd hs0 hsd k hk0
  have hF := periodicRiesz_fourierCoeff hd hs0 hsd k
  rw [funFourierCoeff_eq_int] at hF
  have hne : (∫ x, UnitAddTorus.mFourier (-k) x * ((periodicRiesz d s x : ℝ) : ℂ)) ≠ 0 := by
    rw [hF]
    exact_mod_cast hpos.ne'
  have hint : Integrable (fun x => UnitAddTorus.mFourier (-k) x * ((periodicRiesz d s x : ℝ) : ℂ)) := by
    by_contra h
    exact hne (integral_undef h)
  have hnorm : Integrable (fun x => ‖periodicRiesz d s x‖) := by
    refine hint.norm.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [norm_mul, Complex.norm_real]
    have : ‖UnitAddTorus.mFourier (-k) x‖ = 1 := by
      simpa [Torus.mode] using Torus.norm_mode (-k) x
    rw [this, one_mul]
  exact (integrable_norm_iff (aemeasurable_periodicRiesz hd hs0 hsd).aestronglyMeasurable).mp hnorm

/-- `x ↦ ∫ g(x-y) h(y) dy` is continuous for an integrable kernel and a continuous `h`. -/
theorem continuous_convFun {g h : Torus d → ℝ} (hg : Integrable g) (hh : Continuous h) :
    Continuous (convFun g h) := by
  obtain ⟨B, hB⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn hh.continuousOn
  have e : convFun g h = fun x => ∫ z, g z * h (x - z) := by
    funext x
    unfold convFun
    rw [← integral_sub_left_eq_self (fun z => g z * h (x - z)) volume x]
    simp
  rw [e]
  refine continuous_of_dominated (bound := fun z => ‖g z‖ * B) (fun x => ?_) (fun x => ?_)
    (hg.norm.mul_const B) (Filter.Eventually.of_forall fun z => ?_)
  · exact hg.aestronglyMeasurable.mul (hh.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun z => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hB _ (Set.mem_univ _)) (norm_nonneg _)
  · exact continuous_const.mul (hh.comp (continuous_id.sub continuous_const))

/-- Fourier coefficients of a convolution: `(g * h)^(k) = ĝ(k) ĥ(k)`. -/
theorem funFourierCoeff_convFun {g h : Torus d → ℝ} (hg : Integrable g) (hh : Continuous h)
    (k : Lattice d) :
    Torus.funFourierCoeff (fun x => (convFun g h x : ℂ)) k =
      Torus.funFourierCoeff (fun x => (g x : ℂ)) k * Torus.funFourierCoeff (fun x => (h x : ℂ)) k := by
  rw [funFourierCoeff_eq_int, funFourierCoeff_eq_int, funFourierCoeff_eq_int]
  set e : Torus d → ℂ := fun x => UnitAddTorus.mFourier (-k) x with he
  have hnorm : ∀ x, ‖e x‖ = 1 := fun x => by simpa [he, Torus.mode] using Torus.norm_mode (-k) x
  have hadd : ∀ x y, e x = e (x - y) * e y := by
    intro x y
    have := Torus.mode_add_arg (-k) (x - y) y
    simp only [Torus.mode, sub_add_cancel] at this
    simpa [he] using this
  have hec : Continuous e := (UnitAddTorus.mFourier (-k)).continuous
  have hhi : Integrable h := hh.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hI : Integrable (fun p : Torus d × Torus d => h p.2 * g (p.1 - p.2)) (volume.prod volume) :=
    Integrable.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hhi hg
  have hF : Integrable (fun p : Torus d × Torus d => e p.1 * (((g (p.1 - p.2) * h p.2 : ℝ)) : ℂ))
      (volume.prod volume) := by
    have h1 : Integrable (fun p : Torus d × Torus d => (((h p.2 * g (p.1 - p.2) : ℝ)) : ℂ))
        (volume.prod volume) := hI.ofReal
    refine (h1.bdd_mul (hec.comp continuous_fst).aestronglyMeasurable (Filter.Eventually.of_forall fun p => (hnorm _).le)).congr
      (Filter.Eventually.of_forall fun p => ?_)
    simp only [mul_comm (h p.2) (g (p.1 - p.2))]
    rfl
  have step1 : ∀ x, e x * ((convFun g h x : ℝ) : ℂ) = ∫ y, e x * (((g (x - y) * h y : ℝ)) : ℂ) := by
    intro x
    rw [integral_const_mul, integral_complex_ofReal]
    rfl
  show ∫ x, e x * ((convFun g h x : ℝ) : ℂ) = (∫ x, e x * (g x : ℂ)) * ∫ x, e x * (h x : ℂ)
  simp_rw [step1]
  rw [integral_integral_swap hF]
  have step2 : ∀ y, ∫ x, e x * (((g (x - y) * h y : ℝ)) : ℂ) =
      (∫ x, e x * (g x : ℂ)) * (e y * (h y : ℂ)) := by
    intro y
    have : ∀ x, e x * (((g (x - y) * h y : ℝ)) : ℂ) =
        (e y * (h y : ℂ)) * (e (x - y) * (g (x - y) : ℂ)) := by
      intro x
      rw [hadd x y]
      push_cast
      ring
    simp_rw [this]
    rw [integral_const_mul, integral_sub_right_eq_self (fun x => e x * (g x : ℂ))]
    ring
  simp_rw [step2]
  rw [integral_const_mul]


theorem integrable_mode_mul_real' (n : Lattice d) {u : Torus d → ℝ} (hu : Integrable u) :
    Integrable (fun x => Torus.mode n x * (u x : ℂ)) :=
  hu.ofReal.bdd_mul (Torus.continuous_mode n).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => (Torus.norm_mode n x).le)

/-- Continuous functions on the torus with the same Fourier coefficients coincide. -/
theorem eq_of_funFourierCoeff_eq {u v : Torus d → ℝ} (hu : Continuous u) (hv : Continuous v)
    (h : ∀ k, Torus.funFourierCoeff (fun x => (u x : ℂ)) k =
      Torus.funFourierCoeff (fun x => (v x : ℂ)) k) : u = v := by
  set w : Torus d → ℝ := fun x => u x - v x with hw
  have hwc : Continuous w := hu.sub hv
  have hwi : Integrable w := hwc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hw2 : MemLp w 2 volume :=
    hwc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hui : Integrable u := hu.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hvi : Integrable v := hv.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hs := Torus.hasSum_sq_coeff hw2
  have hz : ∀ n : Lattice d, Torus.cosCoeff w n ^ 2 + Torus.sinCoeff w n ^ 2 = 0 := by
    intro n
    rw [← Torus.norm_sq_coeff hwi]
    have h1 := h n
    rw [funFourierCoeff_eq_int, funFourierCoeff_eq_int] at h1
    have h2 : ∫ x, Torus.mode (-n) x * (w x : ℂ) = 0 := by
      have : ∀ x, Torus.mode (-n) x * (w x : ℂ) =
          Torus.mode (-n) x * (u x : ℂ) - Torus.mode (-n) x * (v x : ℂ) := by
        intro x; simp only [hw]; push_cast; ring
      simp_rw [this]
      rw [integral_sub]
      · exact sub_eq_zero.mpr h1
      · exact (integrable_mode_mul_real' (-n) hui)
      · exact (integrable_mode_mul_real' (-n) hvi)
    rw [h2]; simp
  have hs0 : HasSum (fun n : Lattice d => Torus.cosCoeff w n ^ 2 + Torus.sinCoeff w n ^ 2) 0 := by
    simp [hz]
  have hint : ∫ x, w x ^ 2 = 0 := hs.unique hs0
  have hsq : Continuous fun x => w x ^ 2 := hwc.pow 2
  have hae : (fun x => w x ^ 2) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _)
      (hsq.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).mp hint
  have hall : (fun x => w x ^ 2) = 0 := (Continuous.ae_eq_iff_eq volume hsq continuous_const).mp hae
  funext x
  have := congrFun hall x
  simp only [Pi.zero_apply, pow_eq_zero_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true] at this
  simpa [hw, sub_eq_zero] using this

/-! ### Calculus on the torus -/

theorem grad_apply (φ : Torus d → ℝ) (x : Torus d) (j : Fin d) :
    Torus.grad φ x j = Torus.partialDeriv j φ x := by
  have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ)
    (x := EuclideanSpace.single j (1 : ℝ)) (y := fderiv ℝ (Torus.lift φ) (Torus.rep x))
  unfold Torus.grad Torus.partialDeriv
  unfold gradient
  rw [← h]
  rw [EuclideanSpace.inner_single_right]
  simp

theorem partialDeriv_mul (j : Fin d) (φ ψ : Torus d → ℝ) (hφ : Torus.IsCk 1 φ)
    (hψ : Torus.IsCk 1 ψ) (x : Torus d) :
    Torus.partialDeriv j (fun y => φ y * ψ y) x =
      Torus.partialDeriv j φ x * ψ x + φ x * Torus.partialDeriv j ψ x := by
  have e1 : Torus.lift (fun y => φ y * ψ y) = fun y => Torus.lift φ y * Torus.lift ψ y := rfl
  unfold Torus.partialDeriv
  rw [e1, fderiv_fun_mul ((hφ.differentiable one_ne_zero) _) ((hψ.differentiable one_ne_zero) _)]
  simp [Torus.lift, Torus.mk_rep]
  ring

theorem partialDeriv_const (j : Fin d) (c : ℝ) (x : Torus d) :
    Torus.partialDeriv j (fun _ => c) x = 0 := by
  unfold Torus.partialDeriv
  have : Torus.lift (fun _ : Torus d => c) = fun _ => c := rfl
  rw [this]
  simp

theorem isCk_mul_partialDeriv (ρ f : Torus d → ℝ) (hρ : Torus.IsCk 1 ρ) (hf : Torus.IsCk 2 f)
    (j : Fin d) : Torus.IsCk 1 (fun y => ρ y * Torus.partialDeriv j f y) :=
  hρ.mul (isCk_one_partialDeriv j f hf)

theorem div_smul_grad (ρ f : Torus d → ℝ) (hρ : Torus.IsCk 1 ρ) (hf : Torus.IsCk 2 f)
    (x : Torus d) :
    Torus.div (fun y => ρ y • Torus.grad f y) x =
      ∑ j, Torus.partialDeriv j (fun y => ρ y * Torus.partialDeriv j f y) x := by
  unfold Torus.div
  refine Finset.sum_congr rfl fun i _ => ?_
  set F : Euc d → Euc d := Torus.lift (fun y => ρ y • Torus.grad f y) with hF
  have hcomp : ∀ j y, F y j = Torus.lift (fun y => ρ y * Torus.partialDeriv j f y) y := by
    intro j y
    simp [hF, Torus.lift, grad_apply]
  have hdiff : DifferentiableAt ℝ F (Torus.rep x) := by
    rw [differentiableAt_euclidean]
    intro j
    have : (fun y => F y j) = Torus.lift (fun y => ρ y * Torus.partialDeriv j f y) := funext (hcomp j)
    rw [this]
    exact ((isCk_mul_partialDeriv ρ f hρ hf j).differentiable one_ne_zero) _
  have h1 : HasFDerivAt (fun y => F y i) ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).comp
      (fderiv ℝ F (Torus.rep x))) (Torus.rep x) :=
    (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).hasFDerivAt.comp _ hdiff.hasFDerivAt
  have h2 := h1.fderiv
  have h3 : (fun y => F y i) = Torus.lift (fun y => ρ y * Torus.partialDeriv i f y) :=
    funext (hcomp i)
  rw [h3] at h2
  have h4 : Torus.partialDeriv i (fun y => ρ y * Torus.partialDeriv i f y) x =
      fderiv ℝ (Torus.lift (fun y => ρ y * Torus.partialDeriv i f y)) (Torus.rep x)
        (EuclideanSpace.single i 1) := rfl
  rw [h4, h2]
  simp

/-- Differentiating the Gibbs relation: if `ρ = exp(-β(V + φ)) / Z` with `ρ > 0` of class `C¹`
then `φ` is `C¹` and `∂_jφ = -β⁻¹ ∂_jρ / ρ - ∂_jV`. -/
theorem gibbs_partialDeriv (V ρ φ : Torus d → ℝ) (β : ℝ) (hβ : β ≠ 0) (Z : ℝ)
    (hρ : Torus.IsCk 1 ρ) (hV : Torus.IsCk 1 V) (hpos : ∀ x, 0 < ρ x)
    (hφ : ∀ x, ρ x = Real.exp (-β * (V x + φ x)) / Z) :
    Torus.IsCk 1 φ ∧ ∀ j x, Torus.partialDeriv j φ x =
      -β⁻¹ * (Torus.partialDeriv j ρ x / ρ x) - Torus.partialDeriv j V x := by
  have hZ : 0 < Z := by
    have h1 := hφ 0
    have h2 := hpos 0
    have h3 := Real.exp_pos (-β * (V 0 + φ 0))
    rcases lt_trichotomy Z 0 with h | h | h
    · exfalso
      have : Real.exp (-β * (V 0 + φ 0)) / Z < 0 := div_neg_of_pos_of_neg h3 h
      linarith
    · rw [h, div_zero] at h1; linarith
    · exact h
  have hform : φ = fun x => -β⁻¹ * Real.log (Z * ρ x) - V x := by
    funext x
    have h1 : Z * ρ x = Real.exp (-β * (V x + φ x)) := by
      rw [hφ x]; field_simp
    rw [h1, Real.log_exp]
    field_simp
    ring
  have hlift : Torus.lift φ = fun y => -β⁻¹ * Real.log (Z * Torus.lift ρ y) - Torus.lift V y := by
    funext y
    simp only [Torus.lift, Function.comp]
    rw [hform]
  have hne : ∀ y, Z * Torus.lift ρ y ≠ 0 := fun y => (mul_pos hZ (hpos _)).ne'
  have hC : Torus.IsCk 1 φ := by
    unfold Torus.IsCk
    rw [hlift]
    exact (contDiff_const.mul ((contDiff_const.mul hρ).log hne)).sub hV
  refine ⟨hC, fun j x => ?_⟩
  have hρd : HasFDerivAt (Torus.lift ρ) (fderiv ℝ (Torus.lift ρ) (Torus.rep x)) (Torus.rep x) :=
    ((hρ.differentiable one_ne_zero) _).hasFDerivAt
  have hVd : HasFDerivAt (Torus.lift V) (fderiv ℝ (Torus.lift V) (Torus.rep x)) (Torus.rep x) :=
    ((hV.differentiable one_ne_zero) _).hasFDerivAt
  have hd := ((((hρd.const_mul Z).log (hne _)).const_mul (-β⁻¹)).sub hVd)
  have h1 : fderiv ℝ (fun y => -β⁻¹ * Real.log (Z * Torus.lift ρ y) - Torus.lift V y)
      (Torus.rep x) = -β⁻¹ • (Z * Torus.lift ρ (Torus.rep x))⁻¹ • Z • fderiv ℝ (Torus.lift ρ)
        (Torus.rep x) - fderiv ℝ (Torus.lift V) (Torus.rep x) := hd.fderiv
  have h2 : Torus.partialDeriv j φ x = fderiv ℝ (Torus.lift φ) (Torus.rep x)
      (EuclideanSpace.single j 1) := rfl
  rw [h2, hlift]
  rw [h1]
  have hρx : Torus.lift ρ (Torus.rep x) = ρ x := by simp [Torus.lift, Torus.mk_rep]
  simp only [sub_apply, smul_apply, hρx]
  unfold Torus.partialDeriv
  simp only [smul_eq_mul]
  have hρx0 := (hpos x).ne'
  field_simp

/-! ### Bridging the cancellation convention with `g *` (kernel inputs) -/

theorem coeffOf_convFun (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) {h : Torus d → ℝ}
    (hh : Continuous h) (k : Lattice d) :
    coeffOf (convFun (periodicRiesz d s) h) k = (rieszCoeff d s k : ℂ) * coeffOf h k := by
  unfold coeffOf
  rw [funFourierCoeff_convFun (integrable_periodicRiesz hd s hs0 hsd) hh k,
    periodicRiesz_fourierCoeff hd hs0 hsd k]

theorem coeffOf_sum {ι : Type*} (t : Finset ι) (u : ι → Torus d → ℝ) (hu : ∀ i, Continuous (u i))
    (k : Lattice d) :
    coeffOf (fun x => ∑ i ∈ t, u i x) k = ∑ i ∈ t, coeffOf (u i) k := by
  unfold coeffOf
  simp only [funFourierCoeff_eq_int]
  have hint : ∀ i, Integrable (fun x => UnitAddTorus.mFourier (-k) x * (u i x : ℂ)) := fun i =>
    integrable_mode_mul_real' (-k) ((hu i).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
  simp_rw [Complex.ofReal_sum, Finset.mul_sum]
  exact integral_finsetSum _ fun i _ => hint i

theorem continuous_of_isCk {φ : Torus d → ℝ} (hφ : Torus.IsCk 1 φ) : Continuous φ :=
  Torus.continuous_of_continuous_lift hφ.continuous

/-- `∇g * ρ = ∇(g * ρ)` (cancellation convention), for `C¹` `ρ` with `g * ρ ∈ C¹`. -/
theorem convGradConv_eq_partialDeriv (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    {ρ : Torus d → ℝ} (hρ : Torus.IsCk 1 ρ) (hφ : Torus.IsCk 1 (convFun (periodicRiesz d s) ρ))
    (j : Fin d) (x : Torus d) :
    (convGradConv (periodicRieszGrad d s) ρ x) j =
      Torus.partialDeriv j (convFun (periodicRiesz d s) ρ) x := by
  have hρc := continuous_of_isCk hρ
  have hu : Continuous fun x => (convGradConv (periodicRieszGrad d s) ρ x) j :=
    (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).continuous.comp
      (convGradConv_continuous hd hs0 hsd ρ hρ)
  have hv : Continuous (Torus.partialDeriv j (convFun (periodicRiesz d s) ρ)) :=
    continuous_partialDeriv j _ hφ
  have := eq_of_funFourierCoeff_eq hu hv (fun k => by
    have h1 := congrFun (convGradConv_coeff hd hs0 hsd ρ hρ j) k
    have h2 := congrFun (coeffOf_partialDeriv j _ hφ) k
    have h3 := coeffOf_convFun hd s hs0 hsd hρc k
    unfold coeffOf at h1 h2 h3
    rw [h1, h2]
    simp only [derivCoeff, gradRieszCoeff, rieszMult] at *
    rw [h3])
  exact congrFun this x

/-- `∑_j ∂_j g * H_j = g * ∑_j ∂_j H_j` (cancellation convention). -/
theorem sum_convGradConv_eq (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (H : Fin d → Torus d → ℝ) (hH : ∀ j, Torus.IsCk 1 (H j)) (x : Torus d) :
    ∑ j, (convGradConv (periodicRieszGrad d s) (H j) x) j =
      convFun (periodicRiesz d s) (fun y => ∑ j, Torus.partialDeriv j (H j) y) x := by
  have hDc : Continuous fun y => ∑ j, Torus.partialDeriv j (H j) y :=
    continuous_finsetSum _ fun j _ => continuous_partialDeriv j _ (hH j)
  have hu : Continuous fun x => ∑ j, (convGradConv (periodicRieszGrad d s) (H j) x) j :=
    continuous_finsetSum _ fun j _ => (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).continuous.comp
      (convGradConv_continuous hd hs0 hsd (H j) (hH j))
  have hv : Continuous (convFun (periodicRiesz d s) fun y => ∑ j, Torus.partialDeriv j (H j) y) :=
    continuous_convFun (integrable_periodicRiesz hd s hs0 hsd) hDc
  have := eq_of_funFourierCoeff_eq hu hv (fun k => by
    have e1 : coeffOf (fun x => ∑ j, (convGradConv (periodicRieszGrad d s) (H j) x) j) k =
        ∑ j, coeffOf (fun x => (convGradConv (periodicRieszGrad d s) (H j) x) j) k :=
      coeffOf_sum Finset.univ _ (fun j => (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).continuous.comp
        (convGradConv_continuous hd hs0 hsd (H j) (hH j))) k
    have e2 := coeffOf_convFun hd s hs0 hsd hDc k
    have e3 : coeffOf (fun y => ∑ j, Torus.partialDeriv j (H j) y) k =
        ∑ j, coeffOf (Torus.partialDeriv j (H j)) k :=
      coeffOf_sum Finset.univ _ (fun j => continuous_partialDeriv j _ (hH j)) k
    show coeffOf (fun x => ∑ j, (convGradConv (periodicRieszGrad d s) (H j) x) j) k =
      coeffOf (convFun (periodicRiesz d s) fun y => ∑ j, Torus.partialDeriv j (H j) y) k
    rw [e1, e2, e3, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [convGradConv_coeff hd hs0 hsd (H j) (hH j) j, coeffOf_partialDeriv j _ (hH j)]
    simp only [gradRieszCoeff, derivCoeff, rieszMult]
    ring)
  exact congrFun this x

/-! ### The backward generator for `M = -I` -/

theorem convGradConv_neg (G : Torus d → Euc d) (h : Torus d → ℝ) (x : Torus d) :
    convGradConv G (fun y => -h y) x = -convGradConv G h x := by
  unfold convGradConv
  rw [← integral_neg]
  congr 1
  funext y
  split_ifs
  · simp only [neg_sub_neg, sub_smul]
    abel
  · simp [neg_smul]

theorem matVec_negOne (v : Euc d) : Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ) v = -v := by
  simp [Torus.matVec]

theorem matVec_negOne_transpose (v : Euc d) :
    Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose v = -v := by
  simp [Torus.matVec]

theorem backwardGenerator_negOne (D : DynData d) (hM : D.M = -1) (ρ φ : Torus d → ℝ)
    (x : Torus d) :
    backwardGenerator D ρ φ x =
      D.invβ * Torus.laplacian φ x -
        ∑ j, ((convGradConv (periodicRieszGrad d D.s) ρ x) j + Torus.partialDeriv j D.V x) *
          Torus.partialDeriv j φ x +
        ∑ j, (convGradConv (periodicRieszGrad d D.s)
          (fun y => ρ y * Torus.partialDeriv j φ y) x) j := by
  unfold backwardGenerator meanFieldDrift
  rw [hM]
  have h1 : ∀ j, (convGradConv (periodicRieszGrad d D.s)
      (fun y => ρ y * (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose (Torus.grad φ y)) j) x) j
      = -(convGradConv (periodicRieszGrad d D.s) (fun y => ρ y * Torus.partialDeriv j φ y) x) j := by
    intro j
    have : (fun y => ρ y * (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose (Torus.grad φ y)) j)
        = fun y => -(ρ y * Torus.partialDeriv j φ y) := by
      funext y
      rw [matVec_negOne_transpose]
      simp [grad_apply]
    rw [this, convGradConv_neg]
    simp
  simp_rw [h1, matVec_negOne]
  simp only [PiLp.inner_apply, Finset.sum_neg_distrib, sub_neg_eq_add]
  have h2 : ∀ j, inner ℝ ((-(convGradConv (periodicRieszGrad d D.s) ρ x) - Torus.grad D.V x) j)
      (Torus.grad φ x j) = -(((convGradConv (periodicRieszGrad d D.s) ρ x) j +
        Torus.partialDeriv j D.V x) * Torus.partialDeriv j φ x) := by
    intro j
    simp [grad_apply]
    ring
  simp_rw [h2]
  simp only [Finset.sum_neg_distrib]
  ring

/-! ### `C:eq:operator-order` -/

theorem integral_partialDeriv_eq_zero (j : Fin d) (H : Torus d → ℝ) (hH : Torus.IsCk 1 H) :
    ∫ x, Torus.partialDeriv j H x = 0 := by
  have h := integral_partialDeriv_mul j H (fun _ => (1 : ℝ)) hH (by
    unfold Torus.IsCk; exact contDiff_const)
  simp only [mul_one, partialDeriv_const, mul_zero, integral_zero, neg_zero] at h
  exact h

/-- Pointwise generator formula: `𝓛f = -ν L f + g * Div(ρ∇f)` for the gradient-flow generator
(`M = -I`), via the Gibbs relation. -/
theorem generator_eq (hd : 2 ≤ d) (D : DynData d) (hM : D.M = -1) (β : ℝ) (hβ : 0 < β)
    (hinv : D.invβ = β⁻¹) (hV : Torus.IsCk 2 D.V) (ρ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d D.s) D.V β ρ) (hρC : Torus.IsCk 2 ρ)
    (hpos : ∀ x, 0 < ρ x) (f : Torus d → ℝ) (hf : Torus.IsCk 2 f) (x : Torus d) :
    backwardGenerator D ρ f x = -(D.invβ * Lop ρ f x) +
      convFun (periodicRiesz d D.s) (fun y => ∑ j, Torus.partialDeriv j
        (fun y' => ρ y' * Torus.partialDeriv j f y') y) x := by
  have hρ1 : Torus.IsCk 1 ρ := hρC.of_le (by norm_num)
  have hV1 : Torus.IsCk 1 D.V := hV.of_le (by norm_num)
  obtain ⟨hgibbs, hdiff⟩ := gibbs_partialDeriv D.V ρ (convFun (periodicRiesz d D.s) ρ) β hβ.ne'
    (∫ y, Real.exp (-β * (D.V y + convFun (periodicRiesz d D.s) ρ y))) hρ1 hV1 hpos hρβ.2
  have hc : ∀ j, (convGradConv (periodicRieszGrad d D.s) ρ x) j + Torus.partialDeriv j D.V x =
      -β⁻¹ * (Torus.partialDeriv j ρ x / ρ x) := by
    intro j
    rw [convGradConv_eq_partialDeriv hd D.s D.hs0 D.hsd hρ1 hgibbs j x, hdiff j x]
    ring
  have hH : ∀ j, Torus.IsCk 1 (fun y => ρ y * Torus.partialDeriv j f y) :=
    fun j => isCk_mul_partialDeriv ρ f hρ1 hf j
  rw [backwardGenerator_negOne D hM ρ f x, sum_convGradConv_eq hd D.s D.hs0 D.hsd _ hH x]
  simp_rw [hc]
  have hDh : ∑ j, Torus.partialDeriv j (fun y' => ρ y' * Torus.partialDeriv j f y') x =
      ∑ j, (Torus.partialDeriv j ρ x * Torus.partialDeriv j f x +
        ρ x * Torus.partialDeriv j (Torus.partialDeriv j f) x) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    exact partialDeriv_mul j ρ _ hρ1 (isCk_one_partialDeriv j f hf) x
  have hLop : Lop ρ f x = -(ρ x)⁻¹ * ∑ j, Torus.partialDeriv j
      (fun y' => ρ y' * Torus.partialDeriv j f y') x := by
    unfold Lop
    rw [div_smul_grad ρ f hρ1 hf x]
  rw [hLop, hDh, laplacian_eq_sum f hf x, hinv]
  have hρx := (hpos x).ne'
  have e1 : ∑ j, (-β⁻¹ * (Torus.partialDeriv j ρ x / ρ x)) * Torus.partialDeriv j f x =
      -β⁻¹ * (ρ x)⁻¹ * ∑ j, Torus.partialDeriv j ρ x * Torus.partialDeriv j f x := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp
  have e2 : ∑ j, (Torus.partialDeriv j ρ x * Torus.partialDeriv j f x +
      ρ x * Torus.partialDeriv j (Torus.partialDeriv j f) x) =
      ∑ j, Torus.partialDeriv j ρ x * Torus.partialDeriv j f x +
        ρ x * ∑ j, Torus.partialDeriv j (Torus.partialDeriv j f) x := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
  rw [e1, e2]
  field_simp
  ring

/-- `Q_β 𝓛_β f = -(ν L_β f + K_β L_β f)` for the gradient-flow generator (`M = -I`). -/
theorem operator_order_core (hd : 2 ≤ d) (D : DynData d) (hM : D.M = -1) (β : ℝ) (hβ : 0 < β)
    (hinv : D.invβ = β⁻¹) (hV : Torus.IsCk 2 D.V) (ρ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d D.s) D.V β ρ) (hρC : Torus.IsCk 2 ρ)
    (hpos : ∀ x, 0 < ρ x) (f : Torus d → ℝ) (hf : Torus.IsCk 2 f) :
    projMean (withDensityReal ρ) (backwardGenerator D ρ f) =
      fun x => -(D.invβ * Lop ρ f x +
        Kop (periodicRiesz d D.s) (withDensityReal ρ) (Lop ρ f) x) := by
  have hρ1 : Torus.IsCk 1 ρ := hρC.of_le (by norm_num)
  have hρc : Continuous ρ := continuous_of_isCk hρ1
  have hρm : Measurable ρ := hρc.measurable
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x => (hpos x).le
  have hH : ∀ j, Torus.IsCk 1 (fun y => ρ y * Torus.partialDeriv j f y) :=
    fun j => isCk_mul_partialDeriv ρ f hρ1 hf j
  set Dh : Torus d → ℝ := fun y => ∑ j, Torus.partialDeriv j
    (fun y' => ρ y' * Torus.partialDeriv j f y') y with hDh
  have hDc : Continuous Dh :=
    continuous_finsetSum _ fun j _ => continuous_partialDeriv j _ (hH j)
  set g := periodicRiesz d D.s with hg
  set E : Torus d → ℝ := convFun g Dh with hE
  have hEc : Continuous E := continuous_convFun (integrable_periodicRiesz hd D.s D.hs0 D.hsd) hDc
  have hgen : ∀ x, backwardGenerator D ρ f x = -(D.invβ * Lop ρ f x) + E x :=
    fun x => generator_eq hd D hM β hβ hinv hV ρ hρβ hρC hpos f hf x
  have hLop : ∀ x, ρ x * Lop ρ f x = - Dh x := by
    intro x
    have : Lop ρ f x = -(ρ x)⁻¹ * Dh x := by
      unfold Lop
      rw [div_smul_grad ρ f hρ1 hf x]
    rw [this]
    have := (hpos x).ne'
    field_simp
  have hLopc : Continuous (Lop ρ f) := by
    have : Lop ρ f = fun x => -(ρ x)⁻¹ * Dh x := by
      funext x
      unfold Lop
      rw [div_smul_grad ρ f hρ1 hf x]
    rw [this]
    exact ((hρc.inv₀ fun x => (hpos x).ne').neg).mul hDc
  have hint0 : ∫ x, Dh x = 0 := by
    rw [hDh]
    show ∫ x, ∑ j, Torus.partialDeriv j (fun y' => ρ y' * Torus.partialDeriv j f y') x = 0
    rw [integral_finsetSum]
    · exact Finset.sum_eq_zero fun j _ => integral_partialDeriv_eq_zero j _ (hH j)
    · intro j _
      exact (continuous_partialDeriv j _ (hH j)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hKinner : ∀ x, ∫ y, g (x - y) * Lop ρ f y ∂(withDensityReal ρ) = -E x := by
    intro x
    rw [integral_withDensityReal_eq ρ hρm hρ0]
    have : ∀ y, ρ y * (g (x - y) * Lop ρ f y) = -(g (x - y) * Dh y) := by
      intro y
      have := hLop y
      linear_combination g (x - y) * this
    simp_rw [this]
    rw [integral_neg]
    rfl
  have hpairE : pair (withDensityReal ρ) E = ∫ x, ρ x * E x := by
    unfold pair
    exact integral_withDensityReal_eq ρ hρm hρ0 E
  have hKop : ∀ x, Kop g (withDensityReal ρ) (Lop ρ f) x = -E x + ∫ x, ρ x * E x := by
    intro x
    unfold Kop projMean
    simp_rw [hKinner]
    unfold pair
    rw [integral_neg, ← hpairE]
    unfold pair
    ring
  have hpairL : pair (withDensityReal ρ) (backwardGenerator D ρ f) = ∫ x, ρ x * E x := by
    unfold pair
    rw [integral_withDensityReal_eq ρ hρm hρ0]
    have : ∀ x, ρ x * backwardGenerator D ρ f x = D.invβ * Dh x + ρ x * E x := by
      intro x
      rw [hgen x]
      have := hLop x
      linear_combination (-D.invβ) * this
    simp_rw [this]
    rw [integral_add, integral_const_mul, hint0, mul_zero, zero_add]
    · exact (hDc.const_mul _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    · exact (hρc.mul hEc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  funext x
  unfold projMean
  rw [hpairL, hgen x, hKop x]
  ring

end HRS.PDE.MFAux

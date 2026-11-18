import HRS.ME.Asm417A
import HRS.ME.Fourier417A
import HRS.ME.Fourier417B

/-!
# Chunk E, row 4.17: proof of the mode expansion `forcingStat_hasSum` (A2)

Proof of `forcingStat_hasSum` of `HRS/ME/Spec417Asm.lean` (statement copied verbatim; `HRS/ME/Spec417Asm.lean` is not
imported).  Helpers carry the prefix `asmB_`.

* `forcingStat` depends on `f` only through `hTransport d s f`, which depends on `f` only through `Torus.grad f`;
  constants are invisible (`asmB_forcing_sub_const`).
* On smooth tests, `f ↦ forcingStat f X` is linear (`asmB_forcing_add_smooth`, `asmB_forcing_const_mul`).  The kernel
  is dominated by the Riesz envelope `wEnv` (`menv_kernel_env`), which gives integrability of the kernel sections and of
  the centering integral (`asmB_Q_integrable`, from the envelope `forcingStat_envelope_proof` and the collision-null
  Gibbs law).
* For the tail `t_S = g - mean g - ∑_{l∈S} ĝ_l e_l`, `forcingStat t_S X` equals `forcingStat (t_S - t_S(0)) X`, and
  `cbNorm 2 (t_S - t_S(0)) ≤ (d+1) posSeminorm 2 t_S` (`asmB_cbNorm_shift`); `posSeminorm 2 t_S` is bounded by the
  tail of the Fourier series (`fourier_expansion_tail_proof`), which tends to `0`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ME

variable {d : ℕ}

open HRS HRS.LZ

/-! ### Smoothness helpers -/

theorem asmB_cd {f : Torus d → ℝ} (hf : Torus.IsSmooth f) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift f) := hf

theorem asmB_contDiff_nat {f : Torus d → ℝ} (hf : Torus.IsSmooth f) (k : ℕ) :
    ContDiff ℝ (k : WithTop ℕ∞) (Torus.lift f) :=
  (asmB_cd hf).of_le (by exact_mod_cast (le_top : ((k : ℕ∞)) ≤ ⊤))

theorem asmB_isCk_nat {f : Torus d → ℝ} (hf : Torus.IsSmooth f) (k : ℕ) : Torus.IsCk k f :=
  asmB_contDiff_nat hf k

theorem asmB_sm_sub_const {f : Torus d → ℝ} (hf : Torus.IsSmooth f) (c : ℝ) :
    Torus.IsSmooth (fun x => f x - c) :=
  (asmB_cd hf).sub contDiff_const

theorem asmB_sm_const_mul {f : Torus d → ℝ} (hf : Torus.IsSmooth f) (c : ℝ) :
    Torus.IsSmooth (fun x => c * f x) :=
  contDiff_const.mul (asmB_cd hf)

theorem asmB_sm_sum {ι : Type*} (S : Finset ι) (φ : ι → Torus d → ℝ) (c : ι → ℝ)
    (hφ : ∀ i, Torus.IsSmooth (φ i)) : Torus.IsSmooth (fun x => ∑ i ∈ S, c i * φ i x) :=
  ContDiff.sum fun i _ => contDiff_const.mul (asmB_cd (hφ i))

/-! ### Analytic helper: constant shift on the torus -/

/-- `‖rep x‖ ≤ d` for the representative in `[0,1)^d` (copy of `HRS.Parx.PXFID.norm_rep_le`). -/
theorem asmB_norm_rep_le (x : Torus d) : ‖Torus.rep x‖ ≤ d := by
  have h01 : ∀ i, 0 ≤ Torus.rep x i ∧ Torus.rep x i ≤ 1 := by
    intro i
    have := (AddCircle.equivIco (1 : ℝ) 0 (x i)).2
    simp only [Torus.rep]
    exact ⟨by simpa using this.1, by have := this.2; simp at this; linarith⟩
  have hsq : ‖Torus.rep x‖ ^ 2 ≤ d := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ i, ‖Torus.rep x i‖ ^ 2 ≤ ∑ _i : Fin d, (1 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [Real.norm_eq_abs, sq_abs]
          have := h01 i
          nlinarith
      _ = d := by simp
  by_cases hd : d = 0
  · subst hd
    have : ‖Torus.rep x‖ ^ 2 ≤ 0 := by simpa using hsq
    have h0 : ‖Torus.rep x‖ = 0 := by nlinarith [norm_nonneg (Torus.rep x)]
    simp [h0]
  · have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hd
    nlinarith [norm_nonneg (Torus.rep x)]

/-- `cbNorm 2 (t - t(0)) ≤ (d+1) posSeminorm 2 t` for a smooth `t` (the zeroth order term is controlled by the first
derivative through the periodic representative `rep` of `ℝ^d`). -/
theorem asmB_cbNorm_shift {t : Torus d → ℝ} (ht : Torus.IsSmooth t) :
    Torus.cbNorm 2 (fun z => t z - Torus.lift t 0) ≤ ((d : ℝ) + 1) * posSeminorm 2 t := by
  have hC2 : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) (Torus.lift t) := asmB_contDiff_nat ht 2
  have hC1 : ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) (Torus.lift t) := asmB_contDiff_nat ht 1
  have hbdd : ∀ j : ℕ, j ≤ 2 →
      BddAbove (Set.range fun x : Euc d => ‖iteratedFDeriv ℝ j (Torus.lift t) x‖) :=
    fun j hj => ⟨Torus.cbNorm 2 t, by
      rintro _ ⟨x, rfl⟩
      exact PDE.ET.norm_iteratedFDeriv_le_cbNorm hj (show Torus.IsCk 2 t from hC2) x⟩
  set P1 : ℝ := ⨆ x : Euc d, ‖iteratedFDeriv ℝ 1 (Torus.lift t) x‖ with hP1
  set P2 : ℝ := ⨆ x : Euc d, ‖iteratedFDeriv ℝ 2 (Torus.lift t) x‖ with hP2
  have hP1_nn : 0 ≤ P1 := Real.iSup_nonneg fun x => norm_nonneg _
  have hP2_nn : 0 ≤ P2 := Real.iSup_nonneg fun x => norm_nonneg _
  have hfd : ∀ x : Euc d, ‖fderiv ℝ (Torus.lift t) x‖ ≤ P1 := fun x => by
    rw [← norm_iteratedFDeriv_one]
    exact le_ciSup (hbdd 1 (by norm_num)) x
  have hper : ∀ x : Euc d, Torus.lift t (Torus.rep (Torus.mk x)) = Torus.lift t x := fun x => by
    show t (Torus.mk (Torus.rep (Torus.mk x))) = t (Torus.mk x)
    rw [Torus.mk_rep]
  have hlip : ∀ x : Euc d, |Torus.lift t x - Torus.lift t 0| ≤ P1 * d := fun x => by
    have h := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (s := Set.univ) (f := Torus.lift t)
      (fun y _ => hC1.differentiable (by norm_num) y) (fun y _ => hfd y) convex_univ
      (Set.mem_univ (0 : Euc d)) (Set.mem_univ (Torus.rep (Torus.mk x)))
    rw [hper x] at h
    have hn : ‖Torus.rep (Torus.mk x) - 0‖ ≤ (d : ℝ) := by
      rw [sub_zero]; exact asmB_norm_rep_le _
    calc |Torus.lift t x - Torus.lift t 0| = ‖Torus.lift t x - Torus.lift t 0‖ := (Real.norm_eq_abs _).symm
      _ ≤ P1 * ‖Torus.rep (Torus.mk x) - 0‖ := h
      _ ≤ P1 * d := mul_le_mul_of_nonneg_left hn hP1_nn
  have hterm0 : (⨆ x : Euc d, ‖iteratedFDeriv ℝ 0 (Torus.lift (fun z => t z - Torus.lift t 0)) x‖) ≤ P1 * d := by
    refine ciSup_le fun x => ?_
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    exact hlip x
  have hL : ∀ x : Euc d, Torus.lift (fun z => t z - Torus.lift t 0) x = Torus.lift t x - Torus.lift t 0 :=
    fun x => rfl
  have hLfun : Torus.lift (fun z => t z - Torus.lift t 0) = fun y => Torus.lift t y - Torus.lift t 0 := rfl
  have hI1 : iteratedFDeriv ℝ 1 (Torus.lift (fun z => t z - Torus.lift t 0)) = iteratedFDeriv ℝ 1 (Torus.lift t) := by
    rw [hLfun]
    funext x
    ext m
    rw [iteratedFDeriv_one_apply, iteratedFDeriv_one_apply, fderiv_sub_const]
  have hL2 : ∀ x : Euc d, ‖iteratedFDeriv ℝ 2 (Torus.lift (fun z => t z - Torus.lift t 0)) x‖ =
      ‖iteratedFDeriv ℝ 2 (Torus.lift t) x‖ := by
    intro x
    have h1 := norm_fderiv_iteratedFDeriv (𝕜 := ℝ) (n := 1) (f := Torus.lift (fun z => t z - Torus.lift t 0))
      (x := x)
    have h2 := norm_fderiv_iteratedFDeriv (𝕜 := ℝ) (n := 1) (f := Torus.lift t) (x := x)
    rw [hI1] at h1
    exact h1.symm.trans h2
  have hterm1 : (⨆ x : Euc d, ‖iteratedFDeriv ℝ 1 (Torus.lift (fun z => t z - Torus.lift t 0)) x‖) = P1 := by
    rw [hI1]
  have hterm2 : (⨆ x : Euc d, ‖iteratedFDeriv ℝ 2 (Torus.lift (fun z => t z - Torus.lift t 0)) x‖) = P2 := by
    simp only [hL2]
    rfl
  have hps : posSeminorm 2 t = P1 + P2 := by
    unfold posSeminorm
    rw [show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) from rfl, Finset.sum_pair (by norm_num)]
  have hcb : Torus.cbNorm 2 (fun z => t z - Torus.lift t 0) =
      (⨆ x : Euc d, ‖iteratedFDeriv ℝ 0 (Torus.lift (fun z => t z - Torus.lift t 0)) x‖) +
        (⨆ x : Euc d, ‖iteratedFDeriv ℝ 1 (Torus.lift (fun z => t z - Torus.lift t 0)) x‖) +
        (⨆ x : Euc d, ‖iteratedFDeriv ℝ 2 (Torus.lift (fun z => t z - Torus.lift t 0)) x‖) := by
    unfold Torus.cbNorm
    rw [show (2 : ℕ) + 1 = 3 from rfl]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [hcb, hterm1, hterm2, hps]
  have hd0 : (0 : ℝ) ≤ (d : ℝ) * P2 := mul_nonneg (Nat.cast_nonneg _) hP2_nn
  nlinarith [hterm0, hd0]

/-! ### Gradients and the transport kernel -/

theorem asmB_grad_add {f g : Torus d → ℝ} (hf : Torus.IsSmooth f) (hg : Torus.IsSmooth g) (x : Torus d) :
    Torus.grad (fun y => f y + g y) x = Torus.grad f x + Torus.grad g x := by
  have hdf : DifferentiableAt ℝ (Torus.lift f) (Torus.rep x) :=
    (asmB_contDiff_nat hf 1).differentiable (by norm_num) _
  have hdg : DifferentiableAt ℝ (Torus.lift g) (Torus.rep x) :=
    (asmB_contDiff_nat hg 1).differentiable (by norm_num) _
  have e : Torus.lift (fun y => f y + g y) = fun z => Torus.lift f z + Torus.lift g z := rfl
  unfold Torus.grad gradient
  rw [e, fderiv_fun_add hdf hdg, map_add]

theorem asmB_grad_const_mul {f : Torus d → ℝ} (hf : Torus.IsSmooth f) (c : ℝ) (x : Torus d) :
    Torus.grad (fun y => c * f y) x = c • Torus.grad f x := by
  have hdf : DifferentiableAt ℝ (Torus.lift f) (Torus.rep x) :=
    (asmB_contDiff_nat hf 1).differentiable (by norm_num) _
  have e : Torus.lift (fun y => c * f y) = fun z => c * Torus.lift f z := rfl
  unfold Torus.grad gradient
  rw [e, fderiv_const_mul hdf c, map_smul]

theorem asmB_grad_sub_const (f : Torus d → ℝ) (c : ℝ) (x : Torus d) :
    Torus.grad (fun y => f y - c) x = Torus.grad f x := by
  have e : Torus.lift (fun y => f y - c) = fun z => Torus.lift f z - c := rfl
  unfold Torus.grad gradient
  rw [e, fderiv_sub_const]

theorem asmB_hT_eq_comm (s : ℝ) (f : Torus d → ℝ) :
    hTransport d s f = commKernel (periodicRieszGrad d s) (Torus.grad f) := by
  funext x y
  unfold commKernel hTransport
  by_cases hxy : x = y
  · subst hxy; simp
  · rw [if_neg hxy]

theorem asmB_hT_add (s : ℝ) {f g : Torus d → ℝ} (hf : Torus.IsSmooth f) (hg : Torus.IsSmooth g) :
    hTransport d s (fun y => f y + g y) = fun x y => hTransport d s f x y + hTransport d s g x y := by
  funext x y
  unfold hTransport
  rw [asmB_grad_add hf hg x, asmB_grad_add hf hg y, ← inner_add_left]
  congr 1
  abel

theorem asmB_hT_const_mul (s : ℝ) {f : Torus d → ℝ} (hf : Torus.IsSmooth f) (c : ℝ) :
    hTransport d s (fun y => c * f y) = fun x y => c * hTransport d s f x y := by
  funext x y
  unfold hTransport
  rw [asmB_grad_const_mul hf c x, asmB_grad_const_mul hf c y, ← smul_sub, real_inner_smul_left]

theorem asmB_hT_sub_const (s : ℝ) (f : Torus d → ℝ) (c : ℝ) :
    hTransport d s (fun y => f y - c) = hTransport d s f := by
  funext x y
  unfold hTransport
  rw [asmB_grad_sub_const f c x, asmB_grad_sub_const f c y]

/-! ### Quadratic statistics: linearity in the kernel -/

theorem asmB_quad_const_mul {N : ℕ} (c : ℝ) (h : Torus d → Torus d → ℝ) (ν : Measure (Torus d))
    (X : Config d N) :
    quadStat (fun x y => c * h x y) ν X = c * quadStat h ν X := by
  unfold quadStat
  simp only [integral_const_mul]
  rw [show ∑ i, ∑ j ∈ Finset.univ.erase i, c * h (X i) (X j) =
      c * ∑ i, ∑ j ∈ Finset.univ.erase i, h (X i) (X j) by simp only [Finset.mul_sum],
    show ∑ i, c * ∫ y, h (X i) y ∂ν = c * ∑ i, ∫ y, h (X i) y ∂ν by simp only [Finset.mul_sum]]
  ring

theorem asmB_quad_add {N : ℕ} (h₁ h₂ : Torus d → Torus d → ℝ) (ν : Measure (Torus d)) [IsFiniteMeasure ν]
    (hi₁ : ∀ x, Integrable (fun y => h₁ x y) ν) (hi₂ : ∀ x, Integrable (fun y => h₂ x y) ν)
    (hI₁ : Integrable (fun x => ∫ y, h₁ x y ∂ν) ν) (hI₂ : Integrable (fun x => ∫ y, h₂ x y ∂ν) ν)
    (X : Config d N) :
    quadStat (fun x y => h₁ x y + h₂ x y) ν X = quadStat h₁ ν X + quadStat h₂ ν X := by
  have e1 : ∀ x, ∫ y, (h₁ x y + h₂ x y) ∂ν = ∫ y, h₁ x y ∂ν + ∫ y, h₂ x y ∂ν :=
    fun x => integral_add (hi₁ x) (hi₂ x)
  unfold quadStat
  simp only [e1]
  rw [integral_add hI₁ hI₂]
  simp only [Finset.sum_add_distrib, mul_add]
  ring

/-! ### Forcing statistic: invariance and linearity -/

theorem asmB_forcing_sub_const (s : ℝ) (V : Torus d → ℝ) (β : ℝ) (ρβ : Torus d → ℝ) {N : ℕ}
    (f : Torus d → ℝ) (c : ℝ) (X : Config d N) :
    forcingStat s V β ρβ (fun y => f y - c) X = forcingStat s V β ρβ f X := by
  unfold forcingStat
  rw [asmB_hT_sub_const s f c]

theorem asmB_forcing_const_mul (s : ℝ) (V : Torus d → ℝ) (β : ℝ) (ρβ : Torus d → ℝ) {N : ℕ}
    {f : Torus d → ℝ} (hf : Torus.IsSmooth f) (c : ℝ) (X : Config d N) :
    forcingStat s V β ρβ (fun y => c * f y) X = c * forcingStat s V β ρβ f X := by
  unfold forcingStat centeredUnder
  rw [asmB_hT_const_mul s hf c]
  simp only [asmB_quad_const_mul, integral_const_mul]
  ring

/-! ### Measure-theoretic inputs -/

theorem asmB_nu (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hcrit : s = d / 2)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (β : ℝ) (hβ : 0 < β) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) :
    ∃ Λ R0 : ℝ, 0 ≤ Λ ∧ 0 ≤ R0 ∧ withDensityReal ρβ ≤ ENNReal.ofReal Λ • (volume : Measure (Torus d)) ∧
      ∀ x : Torus d, ∫⁻ z, ENNReal.ofReal (wEnv s x z) ≤ ENNReal.ofReal R0 := by
  have hs : 0 < s := by
    rw [hcrit]
    have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  obtain ⟨R0, hR0, hR⟩ := menv_R0 hd hs hcrit
  obtain ⟨-, Λ, hΛ0, hΛ, -⟩ := menv_thermal hd hs0 hsd V hV hβ hρβ
  exact ⟨Λ, R0, hΛ0, hR0, Commutator.absConv_withDensityReal_le hΛ, hR⟩

theorem asmB_nu_finite {ρβ : Torus d → ℝ} {Λ : ℝ}
    (hμle : withDensityReal ρβ ≤ ENNReal.ofReal Λ • (volume : Measure (Torus d))) :
    IsFiniteMeasure (withDensityReal ρβ) :=
  ⟨by
    have h := Measure.le_iff'.1 hμle Set.univ
    rw [Measure.smul_apply, smul_eq_mul] at h
    exact lt_of_le_of_lt h (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _))⟩

theorem asmB_mu_prob (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (β : ℝ) (hβ : 0 < β) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) {N : ℕ} (hN : 2 ≤ N) :
    IsProbabilityMeasure (canonicalGibbs (periodicRiesz d s) V N β) := by
  obtain ⟨hρs, Λ, hΛ0, hΛ, hP⟩ := menv_thermal hd hs0 hsd V hV hβ hρβ
  rw [hP N]
  exact Q32c.q32c_Q_isProb hd hs0 hsd hβ (Λ := max Λ 1) (le_max_right _ _) hρs.density
    (fun x => (hΛ x).trans (le_max_left _ _)) (by omega)

theorem asmB_ae_mu (hd : 2 ≤ d) (s : ℝ) (V : Torus d → ℝ) (β : ℝ) {N : ℕ} :
    ∀ᵐ X ∂(canonicalGibbs (periodicRiesz d s) V N β), X ∉ collisionSet d N := by
  have h0 : ∀ᵐ X ∂(volume : Measure (Config d N)), X ∉ collisionSet d N :=
    HRS.Q84d.q84d_ae_not_collision (by omega)
  unfold canonicalGibbs
  exact Measure.ae_smul_measure ((withDensity_absolutelyContinuous _ _).ae_le h0) _

/-- Kernel bounds: sections and the section-integral of `hTransport f` are integrable under `ν`. -/
theorem asmB_kernel_int (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    {ν : Measure (Torus d)} [IsFiniteMeasure ν] {Λ R0 : ℝ} (hΛ : 0 ≤ Λ) (hR0 : 0 ≤ R0)
    (hμ : ν ≤ ENNReal.ofReal Λ • (volume : Measure (Torus d)))
    (hR : ∀ x : Torus d, ∫⁻ z, ENNReal.ofReal (wEnv s x z) ≤ ENNReal.ofReal R0)
    {f : Torus d → ℝ} (hf : Torus.IsSmooth f) :
    (∀ x, Integrable (fun y => hTransport d s f x y) ν) ∧
      Integrable (fun x => ∫ y, hTransport d s f x y ∂ν) ν := by
  obtain ⟨K, hK0, hK⟩ := menv_kernel_env hd hs0 hsd
  have hf2 : Torus.IsCk 2 f := asmB_isCk_nat hf 2
  have hc0 : 0 ≤ K * Torus.cbNorm 2 f := mul_nonneg hK0 (PDE.cbNorm_nonneg' 2 f)
  have hE : ∀ x y, |hTransport d s f x y| ≤ (K * Torus.cbNorm 2 f) * wEnv s x y := by
    intro x y
    rw [asmB_hT_eq_comm s f]
    exact hK f hf2 x y
  have hm : Measurable (Function.uncurry (hTransport d s f)) :=
    HRS.Parx.PXFID.measurable_hTransport hsd f
  have hi : ∀ x, Integrable (fun y => hTransport d s f x y) ν := fun x => by
    refine Integrable.mono' ((menv_wEnv_int hΛ hR0 hμ hR x).1.const_mul (K * Torus.cbNorm 2 f)) ?_
      (Filter.Eventually.of_forall fun y => ?_)
    · exact (hm.comp (measurable_const.prodMk measurable_id :
        Measurable fun y : Torus d => (x, y))).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      exact hE x y
  refine ⟨hi, ?_⟩
  have hmeas : Measurable (fun x => ∫ y, hTransport d s f x y ∂ν) :=
    (hm.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
  refine Integrable.of_bound hmeas.aestronglyMeasurable ((K * Torus.cbNorm 2 f) * (Λ * R0))
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  exact menv_abs_int_le hΛ hR0 hc0 hμ hR (x := x) (g := fun y => hTransport d s f x y) (hE x)

/-- The centered quadratic statistic of a smooth test is `μ`-integrable: its centered version is dominated by the
envelope `B + C₀` (`B ∈ L²(μ)`) off collisions, which are `μ`-null. -/
theorem asmB_Q_integrable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hcrit : s = d / 2)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (β : ℝ) (hβ : 0 < β) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρS : Torus.IsSmooth ρβ)
    (hρpos : ∀ x, 0 < ρβ x) {N : ℕ} (hN : 2 ≤ N) {f : Torus d → ℝ} (hf : Torus.IsSmooth f) :
    Integrable (fun X : Config d N => quadStat (hTransport d s f) (withDensityReal ρβ) X)
      (canonicalGibbs (periodicRiesz d s) V N β) := by
  haveI := asmB_mu_prob hd hs0 hsd V hV β hβ ρβ hρβ hN
  obtain ⟨B, hBm, hB0, hBL, C₀, C₁, hC₀, -, hbd, -⟩ :=
    forcingStat_envelope_proof hd hs0 hsd hcrit V hV β hβ ρβ hρβ hρS hρpos hN
  have hBint : Integrable B (canonicalGibbs (periodicRiesz d s) V N β) := hBL.integrable one_le_two
  obtain ⟨Λ, R0, hΛ0, hR0, hμle, -⟩ := asmB_nu hd hs0 hsd hcrit V hV β hβ ρβ hρβ
  haveI := asmB_nu_finite hμle
  have hTm : Measurable (Function.uncurry (hTransport d s f)) :=
    HRS.Parx.PXFID.measurable_hTransport hsd f
  have hQm : Measurable (fun X : Config d N => quadStat (hTransport d s f) (withDensityReal ρβ) X) :=
    me_flow_quadStat_meas hTm
  have hRm : Measurable (fun X : Config d N => forcingStat s V β ρβ f X) := by
    unfold forcingStat centeredUnder
    exact (hQm.sub measurable_const).const_mul _
  have hdom : ∀ᵐ X ∂(canonicalGibbs (periodicRiesz d s) V N β),
      ‖forcingStat s V β ρβ f X‖ ≤ Torus.cbNorm 2 f * (B X + C₀) := by
    filter_upwards [asmB_ae_mu hd s V β (N := N)] with X hX
    rw [Real.norm_eq_abs]
    exact hbd f hf X hX
  have hR : Integrable (fun X : Config d N => forcingStat s V β ρβ f X)
      (canonicalGibbs (periodicRiesz d s) V N β) :=
    Integrable.mono' ((hBint.add (integrable_const C₀)).const_mul (Torus.cbNorm 2 f))
      hRm.aestronglyMeasurable hdom
  have hsq : Real.sqrt N ≠ 0 :=
    (Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < N))).ne'
  have hQeq : (fun X : Config d N => quadStat (hTransport d s f) (withDensityReal ρβ) X) =
      fun X => (2 / Real.sqrt N) * forcingStat s V β ρβ f X +
        ∫ Y, quadStat (hTransport d s f) (withDensityReal ρβ) Y ∂(canonicalGibbs (periodicRiesz d s) V N β) := by
    funext X
    unfold forcingStat centeredUnder
    field_simp
    ring
  rw [hQeq]
  exact (hR.const_mul _).add (integrable_const _)

/-- Additivity of the forcing statistic on smooth tests. -/
theorem asmB_forcing_add_smooth (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hcrit : s = d / 2)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (β : ℝ) (hβ : 0 < β) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρS : Torus.IsSmooth ρβ)
    (hρpos : ∀ x, 0 < ρβ x) {N : ℕ} (hN : 2 ≤ N) {f g : Torus d → ℝ} (hf : Torus.IsSmooth f)
    (hg : Torus.IsSmooth g) (X : Config d N) :
    forcingStat s V β ρβ (fun y => f y + g y) X =
      forcingStat s V β ρβ f X + forcingStat s V β ρβ g X := by
  obtain ⟨Λ, R0, hΛ0, hR0, hμle, hR⟩ := asmB_nu hd hs0 hsd hcrit V hV β hβ ρβ hρβ
  haveI := asmB_nu_finite hμle
  obtain ⟨hif, hIf⟩ := asmB_kernel_int hd hs0 hsd hΛ0 hR0 hμle hR hf
  obtain ⟨hig, hIg⟩ := asmB_kernel_int hd hs0 hsd hΛ0 hR0 hμle hR hg
  have hQf := asmB_Q_integrable hd hs0 hsd hcrit V hV β hβ ρβ hρβ hρS hρpos hN hf
  have hQg := asmB_Q_integrable hd hs0 hsd hcrit V hV β hβ ρβ hρβ hρS hρpos hN hg
  unfold forcingStat centeredUnder
  rw [asmB_hT_add s hf hg]
  simp only [asmB_quad_add _ _ _ hif hig hIf hIg]
  rw [integral_add hQf hQg]
  ring

/-- Linearity of the forcing statistic over finite sums of smooth tests. -/
theorem asmB_forcing_sum (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hcrit : s = d / 2)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (β : ℝ) (hβ : 0 < β) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρS : Torus.IsSmooth ρβ)
    (hρpos : ∀ x, 0 < ρβ x) {N : ℕ} (hN : 2 ≤ N) {ι : Type*} (S : Finset ι)
    (φ : ι → Torus d → ℝ) (c : ι → ℝ) (hφ : ∀ i, Torus.IsSmooth (φ i)) (X : Config d N) :
    forcingStat s V β ρβ (fun x => ∑ i ∈ S, c i * φ i x) X =
      ∑ i ∈ S, c i * forcingStat s V β ρβ (φ i) X := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have h0 : Torus.IsSmooth (fun _ : Torus d => (0 : ℝ)) :=
      (contDiff_const : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : Euc d => (0 : ℝ)))
    have := asmB_forcing_const_mul s V β ρβ h0 0 X
    simpa using this
  | @insert a S ha ih =>
    simp only [Finset.sum_insert ha]
    rw [asmB_forcing_add_smooth hd hs0 hsd hcrit V hV β hβ ρβ hρβ hρS hρpos hN (asmB_sm_const_mul (hφ a) (c a))
      (asmB_sm_sum S φ c hφ) X, asmB_forcing_const_mul s V β ρβ (hφ a) (c a) X, ih]

/-! ### The main statement -/

theorem forcingStat_hasSum_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hcrit : s = d / 2)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (β : ℝ) (hβ : 0 < β) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρS : Torus.IsSmooth ρβ)
    (hρpos : ∀ x, 0 < ρβ x) {N : ℕ} (hN : 2 ≤ N)
    (g : Torus d → ℝ) (hg : Torus.IsSmooth g)
    (hsum : Summable fun l : NonzeroLattice d => Lattice.jp l.1 ^ 2 * |Torus.funRealCoeff g l|) :
    ∀ X : Config d N, X ∉ collisionSet d N →
      HasSum (fun l : NonzeroLattice d => Torus.funRealCoeff g l * forcingStat s V β ρβ (Torus.realMode l) X)
        (forcingStat s V β ρβ g X) := by
  classical
  intro X hX
  have hreal : ∀ l : NonzeroLattice d, Torus.IsSmooth (Torus.realMode l) :=
    fun l => HRS.FieldSingAux.isSmooth_realMode l
  obtain ⟨-, C, hC0, hC⟩ := fourier_expansion_tail_proof g (fun n => asmB_isCk_nat hg n) 2 hsum
  obtain ⟨B, -, hB0, -, C₀, C₁, hC₀, -, hbd, -⟩ :=
    forcingStat_envelope_proof hd hs0 hsd hcrit V hV β hβ ρβ hρβ hρS hρpos hN
  -- the centered tails are smooth
  have hTs : ∀ S : Finset (NonzeroLattice d), Torus.IsSmooth
      (fun x => g x - Torus.mean g - ∑ l ∈ S, Torus.funRealCoeff g l * Torus.realMode l x) := by
    intro S
    exact ((asmB_cd hg).sub contDiff_const).sub
      (ContDiff.sum fun l _ => contDiff_const.mul (asmB_cd (hreal l)))
  -- the envelope on tails, with the constant shift
  have hkey : ∀ T : Torus d → ℝ, Torus.IsSmooth T → X ∉ collisionSet d N →
      |forcingStat s V β ρβ T X| ≤ ((d : ℝ) + 1) * posSeminorm 2 T * (B X + C₀) := by
    intro T hT hX'
    have h1 := hbd (fun z => T z - Torus.lift T 0) (asmB_sm_sub_const hT (Torus.lift T 0)) X hX'
    rw [asmB_forcing_sub_const s V β ρβ T (Torus.lift T 0) X] at h1
    have h2 := asmB_cbNorm_shift hT
    exact h1.trans (mul_le_mul_of_nonneg_right h2 (add_nonneg (hB0 X) hC₀))
  -- the mode decomposition of `forcingStat g` at finite stage `S`
  have hid : ∀ S : Finset (NonzeroLattice d),
      forcingStat s V β ρβ g X =
        forcingStat s V β ρβ (fun x => g x - Torus.mean g - ∑ l ∈ S, Torus.funRealCoeff g l * Torus.realMode l x) X +
          ∑ l ∈ S, Torus.funRealCoeff g l * forcingStat s V β ρβ (Torus.realMode l) X := by
    intro S
    have hsumS := asmB_sm_sum S Torus.realMode (Torus.funRealCoeff g) hreal
    rw [← asmB_forcing_sub_const s V β ρβ g (Torus.mean g) X]
    have e2 : (fun y => g y - Torus.mean g) =
        fun y => (g y - Torus.mean g - ∑ l ∈ S, Torus.funRealCoeff g l * Torus.realMode l y) +
          ∑ l ∈ S, Torus.funRealCoeff g l * Torus.realMode l y := by
      funext y
      ring
    rw [e2, asmB_forcing_add_smooth hd hs0 hsd hcrit V hV β hβ ρβ hρβ hρS hρpos hN (hTs S) hsumS X,
      asmB_forcing_sum hd hs0 hsd hcrit V hV β hβ ρβ hρβ hρS hρpos hN S Torus.realMode
        (Torus.funRealCoeff g) hreal X]
  have hBC : 0 ≤ B X + C₀ := add_nonneg (hB0 X) hC₀
  -- the remainder is bounded by the tail of the Fourier series
  have hfinal : ∀ S : Finset (NonzeroLattice d),
      |forcingStat s V β ρβ g X - ∑ l ∈ S, Torus.funRealCoeff g l * forcingStat s V β ρβ (Torus.realMode l) X| ≤
        (((d : ℝ) + 1) * C * (B X + C₀)) *
          ∑' l : {l : NonzeroLattice d // l ∉ S}, Lattice.jp l.1.1 ^ 2 * |Torus.funRealCoeff g l.1| := by
    intro S
    have e : forcingStat s V β ρβ g X - ∑ l ∈ S, Torus.funRealCoeff g l * forcingStat s V β ρβ (Torus.realMode l) X =
        forcingStat s V β ρβ (fun x => g x - Torus.mean g - ∑ l ∈ S, Torus.funRealCoeff g l * Torus.realMode l x) X := by
      linarith [hid S]
    rw [e]
    have hk := hkey _ (hTs S) hX
    have hps := hC S
    calc |forcingStat s V β ρβ (fun x => g x - Torus.mean g - ∑ l ∈ S, Torus.funRealCoeff g l * Torus.realMode l x) X|
        ≤ ((d : ℝ) + 1) * posSeminorm 2 (fun x => g x - Torus.mean g - ∑ l ∈ S, Torus.funRealCoeff g l * Torus.realMode l x) * (B X + C₀) := hk
      _ ≤ ((d : ℝ) + 1) * (C * ∑' l : {l : NonzeroLattice d // l ∉ S}, Lattice.jp l.1.1 ^ 2 * |Torus.funRealCoeff g l.1|) * (B X + C₀) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hps (by positivity)) hBC
      _ = (((d : ℝ) + 1) * C * (B X + C₀)) *
          ∑' l : {l : NonzeroLattice d // l ∉ S}, Lattice.jp l.1.1 ^ 2 * |Torus.funRealCoeff g l.1| := by ring
  -- the tails tend to zero
  have htail : Tendsto (fun S : Finset (NonzeroLattice d) =>
      ∑' l : {l : NonzeroLattice d // l ∉ S}, Lattice.jp l.1.1 ^ 2 * |Torus.funRealCoeff g l.1|) atTop (𝓝 0) :=
    tendsto_tsum_compl_atTop_zero (fun l : NonzeroLattice d => Lattice.jp l.1 ^ 2 * |Torus.funRealCoeff g l|)
  have hK : Tendsto (fun S : Finset (NonzeroLattice d) => (((d : ℝ) + 1) * C * (B X + C₀)) *
      ∑' l : {l : NonzeroLattice d // l ∉ S}, Lattice.jp l.1.1 ^ 2 * |Torus.funRealCoeff g l.1|) atTop (𝓝 0) := by
    have := htail.const_mul (((d : ℝ) + 1) * C * (B X + C₀))
    rwa [mul_zero] at this
  have hlim : Tendsto (fun S : Finset (NonzeroLattice d) =>
      forcingStat s V β ρβ g X - ∑ l ∈ S, Torus.funRealCoeff g l * forcingStat s V β ρβ (Torus.realMode l) X)
      atTop (𝓝 0) :=
    squeeze_zero_norm (fun S => by rw [Real.norm_eq_abs]; exact hfinal S) hK
  have hfin := (tendsto_const_nhds (x := forcingStat s V β ρβ g X)).sub hlim
  rw [sub_zero] at hfin
  exact Tendsto.congr (fun S => sub_sub_cancel _ _) hfin

end HRS.ME

end

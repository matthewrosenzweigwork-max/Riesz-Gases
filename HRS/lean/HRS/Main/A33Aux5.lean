import Mathlib
import HRS.Main.A33Aux4

/-!
# Packet A33, helper 5: the noise Hilbert space and the vectors `h_{t,φ}`

`H = L²(ν; ℝ^d)` on `ℝ × 𝕋^d` with `ν = (dr|_{[0,T]} ⊗ dx) ρ(r,x)`, and
`h_{t,φ}(r,x) = √(2q) 1_{r ≤ t} ∇U^{r,t}φ(x)`.  Gram matrix of the `h`'s = the covariance of the
linear equation (`a33_gram`).
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate RealInnerProductSpace

namespace HRS.A33

open HRS HRS.PDE HRS.PDE.ET

variable {d : ℕ}

theorem a33_measurable_rep (d : ℕ) : Measurable (Torus.rep : Torus d → Euc d) := by
  have h : Measurable (fun (x : Torus d) (i : Fin d) =>
      ((AddCircle.equivIco (1 : ℝ) 0 (x i) : Set.Ico (0 : ℝ) (0 + 1)) : ℝ)) :=
    measurable_pi_iff.2 fun i => measurable_subtype_coe.comp
      ((AddCircle.measurableEquivIco (1 : ℝ) 0).measurable.comp (measurable_pi_apply i))
  exact (WithLp.measurable_toLp 2 _).comp h

/-- Joint measurability of `(r, x) ↦ 1_{r ∈ [0,t]} ∇ f(r)(x)` for a classical solution. -/
theorem a33_grad_meas_of_classical (D : DynData d) (ρ : ℝ → Torus d → ℝ) (t : ℝ) (φ : Torus d → ℝ)
    (f : ℝ → Torus d → ℝ) (hf : IsClassicalAdjointSolution D ρ t φ f) :
    Measurable (fun p : ℝ × Torus d =>
      if p.1 ∈ Set.Icc 0 t then Torus.grad (f p.1) p.2 else 0) := by
  classical
  have hc := hf.cont_c2 1 (by norm_num)
  have hcoord : ∀ i : Fin d, Measurable (fun p : ℝ × Torus d =>
      (if p.1 ∈ Set.Icc 0 t then Torus.grad (f p.1) p.2 else 0) i) := by
    intro i
    set G : ℝ × Euc d → ℝ := fun q =>
      iteratedFDeriv ℝ 1 (Torus.lift (f q.1)) q.2 (fun _ => EuclideanSpace.single i 1) with hG
    have hGc : ContinuousOn G (Set.Icc 0 t ×ˢ Set.univ) := by
      rw [continuousOn_iff_continuous_domRestrict]
      have h1 : Continuous fun p : Set.Icc (0 : ℝ) t × Euc d =>
          iteratedFDeriv ℝ 1 (Torus.lift (f p.1)) p.2 (fun _ => EuclideanSpace.single i 1) :=
        (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => Euc d) ℝ
          (fun _ => EuclideanSpace.single i 1)).continuous.comp hc
      have : (Set.Icc 0 t ×ˢ (Set.univ : Set (Euc d))).domRestrict G =
          (fun p : Set.Icc (0 : ℝ) t × Euc d =>
            iteratedFDeriv ℝ 1 (Torus.lift (f p.1)) p.2 (fun _ => EuclideanSpace.single i 1)) ∘
          (fun p : ↥(Set.Icc 0 t ×ˢ (Set.univ : Set (Euc d))) => ((⟨p.1.1, p.2.1⟩ : Set.Icc (0 : ℝ) t), p.1.2)) := rfl
      rw [this]
      refine h1.comp ?_
      exact (Continuous.subtype_mk (continuous_fst.comp continuous_subtype_val) _).prodMk
        (continuous_snd.comp continuous_subtype_val)
    have hK : Measurable (fun q : ℝ × Euc d => if q.1 ∈ Set.Icc 0 t then G q else 0) := by
      have hS : MeasurableSet (Set.Icc 0 t ×ˢ (Set.univ : Set (Euc d))) :=
        measurableSet_Icc.prod MeasurableSet.univ
      have := hGc.measurable_piecewise (g := fun _ => (0 : ℝ)) continuousOn_const hS
      convert this using 1
      funext q
      by_cases h : q.1 ∈ Set.Icc 0 t
      · simp [Set.piecewise, h]
      · simp [Set.piecewise, h]
    have hm : Measurable (fun p : ℝ × Torus d => (p.1, Torus.rep p.2)) :=
      measurable_fst.prodMk ((a33_measurable_rep d).comp measurable_snd)
    have hcomp := hK.comp hm
    convert hcomp using 1
    funext p
    simp only [Function.comp]
    by_cases h : p.1 ∈ Set.Icc 0 t
    · simp only [h, if_true, hG]
      have e1 : (Torus.grad (f p.1) p.2) i = fderiv ℝ (Torus.lift (f p.1)) (Torus.rep p.2)
          (EuclideanSpace.single i 1) := by
        have := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := Euc d)
          (x := EuclideanSpace.single i 1) (y := fderiv ℝ (Torus.lift (f p.1)) (Torus.rep p.2))
        rw [EuclideanSpace.inner_single_right] at this
        simpa [Torus.grad, gradient] using this
      rw [e1, iteratedFDeriv_one_apply]
    · simp [h]
  have : (fun p : ℝ × Torus d => if p.1 ∈ Set.Icc 0 t then Torus.grad (f p.1) p.2 else 0) =
      fun p => (WithLp.toLp 2 (fun i => (if p.1 ∈ Set.Icc 0 t then Torus.grad (f p.1) p.2 else 0) i) :
        Euc d) := by
    funext p; simp
  rw [this]
  exact (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 hcoord)

/-- Under `AdjointData`, a classical solution exists for smooth data (Proposition 3.9). -/
theorem a33_exists_classical (hd : 1 ≤ d) (J : ℕ) (hJ : mStar d ≤ J) (R : Regime) (MB Λ VB : ℝ)
    (D : DynData d) (ν₀ T : ℝ) (μ : ℝ → Torus d → ℝ)
    (hA : AdjointData D.s J R MB Λ VB D ν₀ T μ) {t : ℝ} (ht : t ∈ Set.Ioc 0 T)
    {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    ∃ f : ℝ → Torus d → ℝ, IsClassicalAdjointSolution D μ t φ f := by
  obtain ⟨C, Cs, -, -, hmain⟩ := adjoint_torus_classical hd D.s D.hs0 D.hsd J hJ R MB Λ VB
  obtain ⟨hcl, -⟩ := hmain D ν₀ T μ hA t ht φ (a33_cont hφ) (a33_memSob (J : ℝ) hφ)
  exact ⟨_, hcl⟩

open Classical in
theorem a33_propagator_eq_choose (D : DynData d) (ρ : ℝ → Torus d → ℝ) (t : ℝ) (φ : Torus d → ℝ)
    (hex : ∃ f, IsClassicalAdjointSolution D ρ t φ f) (r : ℝ) :
    propagator D ρ r t φ = hex.choose r := by
  unfold propagator
  rw [dif_pos hex]

/-- The base measure `dr|_{[0,T]} ⊗ dx`. -/
def a33_mu0 (d : ℕ) (T : ℝ) : Measure (ℝ × Torus d) :=
  (volume.restrict (Set.Icc 0 T)).prod volume

/-- The noise measure `ρ(r,x) dr dx` on `[0,T] × 𝕋^d`. -/
def a33_nu (d : ℕ) (T : ℝ) (ρ : ℝ → Torus d → ℝ) : Measure (ℝ × Torus d) :=
  (a33_mu0 d T).withDensity (fun p => ENNReal.ofReal (ρ p.1 p.2))

/-- The integrand `h_{t,φ}(r,x) = √(2q) 1_{r ≤ t} ∇U^{r,t}φ(x)` (zero for `t ≤ 0`). -/
def a33_g (D : DynData d) (ρ : ℝ → Torus d → ℝ) (q t : ℝ) (φ : Torus d → ℝ) :
    ℝ × Torus d → Euc d := fun p =>
  if p.1 ∈ Set.Icc 0 t ∧ 0 < t then Real.sqrt (2 * q) • Torus.grad (propagator D ρ p.1 t φ) p.2
  else 0

theorem a33_mu0_eq (T : ℝ) :
    a33_mu0 d T = (volume : Measure (ℝ × Torus d)).restrict (Set.Icc 0 T ×ˢ Set.univ) := by
  unfold a33_mu0
  have := Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Torus d)))
    (Set.Icc 0 T) Set.univ
  rw [Measure.restrict_univ] at this
  rw [this]
  rfl

instance a33_mu0_finite (T : ℝ) : IsFiniteMeasure (a33_mu0 d T) := by
  unfold a33_mu0
  infer_instance

theorem a33_ae_mu0 (T : ℝ) : ∀ᵐ p ∂(a33_mu0 d T), p.1 ∈ Set.Icc 0 T := by
  rw [a33_mu0_eq, ae_restrict_iff' (measurableSet_Icc.prod MeasurableSet.univ)]
  exact Eventually.of_forall fun p hp => hp.1

/-- Regularity of the density path used for the noise measure. -/
structure A33Rho (T : ℝ) (ρ : ℝ → Torus d → ℝ) : Prop where
  cont : ContinuousOn (fun p : ℝ × Torus d => ρ p.1 p.2) (Set.Icc 0 T ×ˢ Set.univ)
  nonneg : ∀ r ∈ Set.Icc 0 T, ∀ x, 0 ≤ ρ r x
  one : ∀ r ∈ Set.Icc 0 T, ∫ x, ρ r x = 1

section Rho

variable {T : ℝ} {ρ : ℝ → Torus d → ℝ} (hρ : A33Rho T ρ)

include hρ in
theorem A33Rho.aemeasurable : AEMeasurable (fun p : ℝ × Torus d => ρ p.1 p.2) (a33_mu0 d T) := by
  rw [a33_mu0_eq]
  exact hρ.cont.aemeasurable (measurableSet_Icc.prod MeasurableSet.univ)

include hρ in
theorem A33Rho.bound : ∃ B : ℝ, ∀ r ∈ Set.Icc 0 T, ∀ x, |ρ r x| ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod (isCompact_univ (X := Torus d))).exists_bound_of_continuousOn
    hρ.cont
  exact ⟨B, fun r hr x => by simpa using hB (r, x) ⟨hr, Set.mem_univ x⟩⟩

include hρ in
theorem A33Rho.integrable : Integrable (fun p : ℝ × Torus d => ρ p.1 p.2) (a33_mu0 d T) := by
  obtain ⟨B, hB⟩ := hρ.bound
  refine Integrable.of_bound hρ.aemeasurable.aestronglyMeasurable B ?_
  filter_upwards [a33_ae_mu0 (d := d) T] with p hp
  simpa using hB p.1 hp p.2

include hρ in
theorem A33Rho.nu_finite : IsFiniteMeasure (a33_nu d T ρ) := by
  unfold a33_nu
  refine isFiniteMeasure_withDensity_ofReal (f := fun p : ℝ × Torus d => ρ p.1 p.2) ?_
  exact hρ.integrable.hasFiniteIntegral

theorem a33_ae_nu (T : ℝ) (ρ : ℝ → Torus d → ℝ) : ∀ᵐ p ∂(a33_nu d T ρ), p.1 ∈ Set.Icc 0 T :=
  (withDensity_absolutelyContinuous _ _).ae_le (a33_ae_mu0 T)

end Rho

/-- The bundled hypotheses of Proposition A.33. -/
structure A33Setup (d : ℕ) where
  J : ℕ
  hJ : mStar d ≤ J
  hJ2 : mStar d + d ≤ J
  hd : 1 ≤ d
  R : Regime
  MB : ℝ
  Λ : ℝ
  VB : ℝ
  ν₀ : ℝ
  D : DynData d
  T : ℝ
  ρ : ℝ → Torus d → ℝ
  hA : AdjointData D.s J R MB Λ VB D ν₀ T ρ

namespace A33Setup

variable (S : A33Setup d)

theorem hJd : (d : ℝ) / 2 < S.J := by
  have h1 := a33_mStar_gt d
  have h2 : (mStar d : ℝ) ≤ S.J := by exact_mod_cast S.hJ
  linarith

theorem hT : 0 < S.T := S.hA.hT

theorem rho : A33Rho S.T S.ρ where
  cont := a33_rho_cont S.hA.hμ S.hJd S.hT
  nonneg := fun r hr x => (S.hA.hμ.prob r hr).nonneg x
  one := fun r hr => (S.hA.hμ.prob r hr).integral_one

/-- the constants of `a33_bounds`. -/
theorem bounds : ∃ K₁ K₂ : ℝ, 0 ≤ K₁ ∧ 0 ≤ K₂ ∧ ∀ t ∈ Set.Ioc 0 S.T, ∀ φ : Torus d → ℝ,
    Torus.IsSmooth φ → ∀ r ∈ Set.Icc 0 t,
      MemSobolev (S.J : ℝ) (propagator S.D S.ρ r t φ) ∧
      sobolevNorm (S.J : ℝ) (propagator S.D S.ρ r t φ) ≤ K₁ * sobolevNorm (S.J : ℝ) φ ∧
      ∀ x : Torus d, ‖Torus.grad (propagator S.D S.ρ r t φ) x‖ ≤
        K₂ * sobolevNorm (mStar d : ℝ) φ :=
  a33_bounds S.hd S.J S.hJ S.R S.MB S.Λ S.VB S.D S.ν₀ S.T S.ρ S.hA

theorem exists_classical {t : ℝ} (ht : t ∈ Set.Ioc 0 S.T) {φ : Torus d → ℝ}
    (hφ : Torus.IsSmooth φ) : ∃ f : ℝ → Torus d → ℝ, IsClassicalAdjointSolution S.D S.ρ t φ f :=
  a33_exists_classical S.hd S.J S.hJ S.R S.MB S.Λ S.VB S.D S.ν₀ S.T S.ρ S.hA ht hφ

theorem g_meas (q : ℝ) {t : ℝ} (ht : t ∈ Set.Ioc 0 S.T) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    Measurable (a33_g S.D S.ρ q t φ) := by
  classical
  have hex := S.exists_classical ht hφ
  have h1 := a33_grad_meas_of_classical S.D S.ρ t φ hex.choose hex.choose_spec
  have h2 : a33_g S.D S.ρ q t φ = fun p => Real.sqrt (2 * q) •
      (if p.1 ∈ Set.Icc 0 t then Torus.grad (hex.choose p.1) p.2 else 0) := by
    funext p
    unfold a33_g
    by_cases h : p.1 ∈ Set.Icc 0 t
    · simp [h, ht.1, a33_propagator_eq_choose S.D S.ρ t φ hex]
    · simp [h]
  rw [h2]
  exact h1.const_smul (Real.sqrt (2 * q))

theorem g_bound (q : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Set.Ioc 0 S.T, ∀ φ : Torus d → ℝ, Torus.IsSmooth φ → ∀ p : ℝ × Torus d,
      ‖a33_g S.D S.ρ q t φ p‖ ≤ B * sobolevNorm (mStar d : ℝ) φ := by
  obtain ⟨K₁, K₂, -, hK₂, hK⟩ := S.bounds
  refine ⟨Real.sqrt (2 * q) * K₂, mul_nonneg (Real.sqrt_nonneg _) hK₂, fun t ht φ hφ p => ?_⟩
  unfold a33_g
  split_ifs with h
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_assoc]
    exact mul_le_mul_of_nonneg_left ((hK t ht φ hφ p.1 h.1).2.2 p.2) (Real.sqrt_nonneg _)
  · simp only [norm_zero]
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hK₂) (Real.sqrt_nonneg _)

theorem g_memLp (q : ℝ) {t : ℝ} (ht : t ∈ Set.Icc 0 S.T) {φ : Torus d → ℝ}
    (hφ : Torus.IsSmooth φ) : MemLp (a33_g S.D S.ρ q t φ) 2 (a33_nu d S.T S.ρ) := by
  haveI := S.rho.nu_finite
  rcases ht.1.eq_or_lt with h0 | h0
  · have : a33_g S.D S.ρ q t φ = 0 := by
      funext p
      unfold a33_g
      simp [← h0]
    rw [this]
    exact MemLp.zero
  · have ht' : t ∈ Set.Ioc 0 S.T := ⟨h0, ht.2⟩
    obtain ⟨B, -, hB⟩ := S.g_bound q
    exact MemLp.of_bound (S.g_meas q ht' hφ).aestronglyMeasurable _
      (Eventually.of_forall fun p => hB t ht' φ hφ p)

end A33Setup

end HRS.A33

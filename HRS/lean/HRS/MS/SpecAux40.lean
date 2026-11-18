import HRS.MS.SpecAux39

/-!
# S8P: eigen-equation and completeness fields of `IsSpectralData` (S8.7, packets b3, b4, b7)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.
* `s8p_Asub_surj`: `A = s8p_Asub h K ν` is onto `K` (Lax-Milgram, coercivity `⟨A u, u⟩ ≥ ν ‖u‖²`);
* `s8p_eigen_eq`: if `S φ = om φ` a.e. then `ν L e + K (L e) = ω e` `μ`-a.e. for `e = s8p_E φ`;
* `s8p_complete_field`: if the `A`-orthonormal `v_n ≈ φ_n` are `A`-complete in `L²_0`, then a centered `f ∈ L²(μ)` with
  `⟨f, responseInverse e_n⟩_μ = 0` for all `n` vanishes `μ`-a.e.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal RealInnerProductSpace ContDiff

namespace HRS.MS.Spec

open HRS HRS.Whole HRS.MS.MovDec HRS.MS.MovLin

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

theorem s8p_Asub_surj {M : ℝ} (h : S8pRho d s ρ M) (hd : 1 ≤ d) {ν : ℝ} (hν : 0 < ν)
    (g : MovL2Zero ρ) : ∃ u, s8p_Asub h (MovL2Zero ρ) ν u = g := by
  set A := s8p_Asub h (MovL2Zero ρ) ν with hA
  let B : MovL2Zero ρ →L[ℝ] MovL2Zero ρ →L[ℝ] ℝ :=
    (innerSL ℝ : MovL2Zero ρ →L[ℝ] MovL2Zero ρ →L[ℝ] ℝ).bilinearComp A (ContinuousLinearMap.id ℝ _)
  have hB : ∀ u w, B u w = ⟪A u, w⟫ := fun u w => rfl
  have hc : IsCoercive B := by
    refine ⟨ν, hν, fun u => ?_⟩
    rw [hB, real_inner_comm]
    have := s8p_Asub_low h (MovL2Zero ρ) hd ν u
    nlinarith [this]
  set L := hc.continuousLinearEquivOfBilin with hL
  have hLA : ∀ u, L u = A u := by
    intro u
    refine ext_inner_right ℝ fun w => ?_
    rw [hL, hc.continuousLinearEquivOfBilin_apply, hB]
  exact ⟨L.symm g, by rw [← hLA]; exact L.apply_symm_apply g⟩

theorem s8p_eigen_eq (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : Mov2eRho d ρ) (hE : Mov2eEll d ρ)
    (β : ℝ) (φ : 𝓢R) (om : ℝ)
    (hS : ∀ᵐ x ∂(volume : Measure (Euc d)), movS d s β ρ φ x = om * φ x) :
    ∀ᵐ x ∂(HRS.Whole.withDensityReal ρ),
      β⁻¹ * weightedLaplacian ρ (s8p_E d s β ρ φ) x +
        HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ)
          (weightedLaplacian ρ (s8p_E d s β ρ φ)) x = om * s8p_E d s β ρ φ x := by
  have hwl : ∀ᵐ x ∂(HRS.Whole.withDensityReal ρ),
      weightedLaplacian ρ (s8p_E d s β ρ φ) x = om * (φ x / Real.sqrt (ρ x)) := by
    refine mov2e_ae_mu ?_
    filter_upwards [hS] with x hx
    rw [s8p_E_wlap hd hs0 hsd hρ hE β φ x, hx]
    ring
  have hK : HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ)
        (weightedLaplacian ρ (s8p_E d s β ρ φ)) =
      HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ)
        (fun y => om * (φ y / Real.sqrt (ρ y))) := by
    funext x
    unfold HRS.Whole.Kop HRS.Whole.projMean HRS.Whole.pair
    have hint : ∀ x', ∫ y, rieszKernel d s (x' - y) * weightedLaplacian ρ (s8p_E d s β ρ φ) y
          ∂(HRS.Whole.withDensityReal ρ) =
        ∫ y, rieszKernel d s (x' - y) * (om * (φ y / Real.sqrt (ρ y))) ∂(HRS.Whole.withDensityReal ρ) := by
      intro x'
      refine integral_congr_ae ?_
      filter_upwards [hwl] with y hy
      rw [hy]
    simp only [hint]
  filter_upwards [hwl] with x hx
  rw [hx, hK, s8p_Kop_f hρ om φ x]
  unfold s8p_E
  ring

theorem s8p_complete_field (hd : 1 ≤ d) (hs0 : 0 < s) (hsd : s < d) (hρ : Mov2eRho d ρ)
    (hE : Mov2eEll d ρ) {M : ℝ} (h : S8pRho d s ρ M) {β : ℝ} (hβ : 0 < β)
    (v : ℕ → MovL2Zero ρ) (φ : ℕ → 𝓢R)
    (hv : ∀ n, ∀ᵐ x ∂(volume : Measure (Euc d)), movFun (v n) x = φ n x)
    (hmean : ∀ n, ∫ x, Real.sqrt (ρ x) * φ n x = 0)
    (hcomp : ∀ f : MovL2Zero ρ, (∀ n, ⟪f, s8p_Asub h (MovL2Zero ρ) β⁻¹ (v n)⟫ = 0) → f = 0)
    (f : Euc d → ℝ) (hf : MemL2Zero (HRS.Whole.withDensityReal ρ) f)
    (hr : ∀ n, HRS.Whole.l2Inner (HRS.Whole.withDensityReal ρ) f
      (HRS.Whole.responseInverse (rieszKernel d s) (HRS.Whole.withDensityReal ρ) β (s8p_E d s β ρ (φ n))) = 0) :
    f =ᵐ[HRS.Whole.withDensityReal ρ] 0 := by
  haveI := mov2e_isProb hρ
  obtain ⟨hf2, hf0⟩ := hf
  have hacv : (volume : Measure (Euc d)) ≪ HRS.Whole.withDensityReal ρ := by
    unfold HRS.Whole.withDensityReal
    refine withDensity_absolutelyContinuous' (hρ.prob.measurable.ennreal_ofReal.aemeasurable) ?_
    exact Filter.Eventually.of_forall fun x => by
      simpa using hρ.pos x
  have hsq : MemLp (fun x => Real.sqrt (ρ x)) 2 (volume : Measure (Euc d)) := by
    refine (memLp_two_iff_integrable_sq (hρ.data.sqrt_smooth.continuous.aestronglyMeasurable)).2 ?_
    exact ((hρ.psi_GD.mul hρ.psi_GD).integrable).congr (Filter.Eventually.of_forall fun x => by simp [sq])
  -- the element `√ρ f` of `L²(dx)`
  have hF : MemLp (fun x => Real.sqrt (ρ x) * f x) 2 (volume : Measure (Euc d)) := by
    have hfm : AEStronglyMeasurable f (volume : Measure (Euc d)) := hf2.aestronglyMeasurable.mono_ac hacv
    refine (memLp_two_iff_integrable_sq (hsq.aestronglyMeasurable.mul hfm)).2 ?_
    have h1 : Integrable (fun x => f x ^ 2) (HRS.Whole.withDensityReal ρ) := hf2.integrable_sq
    have h2 := (mov2e_integrable_mu hρ).1 h1
    refine h2.congr (Filter.Eventually.of_forall fun x => ?_)
    have := hρ.psi_sq x
    show ρ x * f x ^ 2 = (Real.sqrt (ρ x) * f x) ^ 2
    rw [mul_pow, Real.sq_sqrt (hρ.pos x).le]
  set g0 : Lp ℝ 2 (volume : Measure (Euc d)) := hF.toLp _ with hg0
  have hg0ae : (g0 : Euc d → ℝ) =ᵐ[volume] fun x => Real.sqrt (ρ x) * f x := hF.coeFn_toLp
  have hsqL : (movSqrtLp ρ : Lp ℝ 2 (volume : Measure (Euc d))) = hsq.toLp _ := by
    unfold movSqrtLp; rw [dif_pos hsq]
  have hsqae : ((movSqrtLp ρ : Lp ℝ 2 (volume : Measure (Euc d))) : Euc d → ℝ) =ᵐ[volume]
      fun x => Real.sqrt (ρ x) := by rw [hsqL]; exact hsq.coeFn_toLp
  have hg0K : g0 ∈ MovL2Zero ρ := by
    rw [mov2d_mem_zero_iff, L2.inner_def]
    have : ∫ x, ⟪(movSqrtLp ρ : Lp ℝ 2 (volume : Measure (Euc d))) x, g0 x⟫ = ∫ x, ρ x * f x := by
      refine integral_congr_ae ?_
      filter_upwards [hsqae, hg0ae] with x h1 h2
      simp only [RCLike.inner_apply, conj_trivial]
      rw [h1, h2, mul_right_comm, hρ.psi_sq x]
    rw [this, ← mov2e_integral_mu hρ]
    exact hf0
  obtain ⟨u, hu⟩ := s8p_Asub_surj h hd (inv_pos.2 hβ) (⟨g0, hg0K⟩ : MovL2Zero ρ)
  have hpairs : ∀ n, ⟪u, s8p_Asub h (MovL2Zero ρ) β⁻¹ (v n)⟫ = 0 := by
    intro n
    rw [← s8p_Asub_symm h (MovL2Zero ρ) β⁻¹ u (v n), hu]
    have h1 : ⟪(⟨g0, hg0K⟩ : MovL2Zero ρ), v n⟫ = ∫ x, Real.sqrt (ρ x) * f x * φ n x := by
      show ⟪g0, (v n : Lp ℝ 2 (volume : Measure (Euc d)))⟫ = _
      rw [L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hg0ae, hv n] with x h1 h2
      simp only [RCLike.inner_apply, conj_trivial]
      change (v n : Lp ℝ 2 (volume : Measure (Euc d))) x * g0 x = _
      rw [show (v n : Lp ℝ 2 (volume : Measure (Euc d))) x = φ n x from h2, h1]
      ring
    rw [h1]
    have h2 : ∫ x, Real.sqrt (ρ x) * f x * φ n x =
        ∫ x, f x * (φ n x / Real.sqrt (ρ x)) ∂(HRS.Whole.withDensityReal ρ) := by
      rw [mov2e_integral_mu hρ]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show Real.sqrt (ρ x) * f x * φ n x = ρ x * (f x * (φ n x / Real.sqrt (ρ x)))
      have hp := hρ.psi_pos x
      have hss := hρ.psi_sq x
      generalize Real.sqrt (ρ x) = p at hp hss ⊢
      rw [← hss]
      field_simp
    rw [h2]
    have h3 := hr n
    have hri := s8p_responseInverse_E hd hs0 hsd hρ hE (fun x => h.le x) hβ (φ n) (hmean n)
    unfold HRS.Whole.l2Inner at h3
    have h4 : ∫ x, f x * HRS.Whole.responseInverse (rieszKernel d s) (HRS.Whole.withDensityReal ρ) β
        (s8p_E d s β ρ (φ n)) x ∂(HRS.Whole.withDensityReal ρ) =
        ∫ x, β⁻¹ * (f x * (φ n x / Real.sqrt (ρ x))) ∂(HRS.Whole.withDensityReal ρ) := by
      refine integral_congr_ae ?_
      filter_upwards [hri] with x hx
      rw [hx]; ring
    rw [h4, integral_const_mul] at h3
    exact (mul_eq_zero.1 h3).resolve_left (inv_pos.2 hβ).ne'
  have hu0 : u = 0 := hcomp u hpairs
  have hg00 : g0 = 0 := by
    have : (⟨g0, hg0K⟩ : MovL2Zero ρ) = 0 := by rw [← hu, hu0, map_zero]
    exact congrArg Subtype.val this
  have h0ae : (g0 : Euc d → ℝ) =ᵐ[volume] 0 := by
    rw [hg00]; exact Lp.coeFn_zero _ _ _
  refine mov2e_ae_mu ?_
  filter_upwards [hg0ae, h0ae] with x h1 h2
  have hp := hρ.psi_pos x
  have : Real.sqrt (ρ x) * f x = 0 := by rw [← h1]; exact h2
  exact (mul_eq_zero.1 this).resolve_left hp.ne'

end HRS.MS.Spec

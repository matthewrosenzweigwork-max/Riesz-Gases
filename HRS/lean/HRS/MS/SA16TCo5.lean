import HRS.MS.SA16PForce6
import HRS.MS.SA16E1E14
import HRS.MS.SA16SNl4

/-!
# S.A.16 (SA16T) Co5: joint continuity of the mean-field drift in `(r, x)`

`sa16t_drift_cont`: under `CoeffHypRd` and `VHypRd`, `(r, x) ↦ meanFieldDriftW D (μ r) x` is continuous on
`[0,T] × ℝ^d` (dominated convergence for the cancellation-convention integral, locally uniformly in `x` by the
weight shift; `μ` is jointly continuous by `coefficient_time_regular`).
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16P
open HRS HRS.Whole HRS.Whole.AppendixA

section Co5
variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

theorem sa16t_phiF_cont (hd : 1 ≤ d) {K : 𝔼 → ℝ} (hKm : Measurable K) {c s A : ℝ} (hc : 0 ≤ c) (hs0 : 0 ≤ s)
    (hsd : s < d) (hK : ∀ z, z ≠ 0 → |K z| ≤ c * ‖z‖ ^ (-s - 1)) {S : Set ℝ} {μ : ℝ → 𝔼 → ℝ}
    (hμd : ∀ r ∈ S, Differentiable ℝ (μ r)) (hμw : ∀ r ∈ S, ∀ y, ‖μ r y‖ ≤ A * sa16p_w d y)
    (hμ1 : ∀ r ∈ S, ∀ y, ‖fderiv ℝ (μ r) y‖ ≤ A)
    (hcont : ContinuousOn (fun q : ℝ × 𝔼 => μ q.1 q.2) (S ×ˢ univ)) :
    ContinuousOn (fun q : ℝ × 𝔼 => sa16p_phiF K (μ q.1) q.2) (S ×ˢ univ) := by
  intro q₀ hq₀
  have hA : 0 ≤ A := by
    have := (norm_nonneg _).trans (hμ1 q₀.1 hq₀.1 0)
    exact this
  have hB1 : Integrable ((closedBall (0 : 𝔼) (1 / 4)).indicator (fun z => c * A * ‖z‖ ^ (-s))) volume :=
    (integrable_indicator_iff measurableSet_closedBall).2 ((sa16p_I1_integrable hd hsd).const_mul (c * A))
  have hB2 : Integrable (fun z : 𝔼 => c * 4 ^ (s + 1) * A * (2 ^ ((d : ℝ) + 3) * sa16p_w d (q₀.2 - z))) volume :=
    ((sa16p_w_integrable.comp_sub_left q₀.2).const_mul (2 ^ ((d : ℝ) + 3))).const_mul _
  unfold sa16p_phiF
  refine MeasureTheory.continuousWithinAt_of_dominated (bound := fun z =>
    (closedBall (0 : 𝔼) (1 / 4)).indicator (fun z => c * A * ‖z‖ ^ (-s)) z +
      c * 4 ^ (s + 1) * A * (2 ^ ((d : ℝ) + 3) * sa16p_w d (q₀.2 - z))) ?_ ?_ (hB1.add hB2) ?_
  · filter_upwards [self_mem_nhdsWithin] with q hq
    exact sa16p_phiI_aesm hKm (hμd q.1 hq.1).continuous q.2
  · have hnear : ∀ᶠ q : ℝ × 𝔼 in 𝓝[S ×ˢ univ] q₀, ‖q.2 - q₀.2‖ ≤ 1 := by
      refine eventually_nhdsWithin_of_eventually_nhds ?_
      have : Tendsto (fun q : ℝ × 𝔼 => ‖q.2 - q₀.2‖) (𝓝 q₀) (𝓝 0) := by
        have hcq : Continuous (fun q : ℝ × 𝔼 => q.2 - q₀.2) := continuous_snd.sub continuous_const
        have h := hcq.norm.tendsto q₀
        simpa using h
      exact this.eventually (ge_mem_nhds (by norm_num))
    filter_upwards [hnear, self_mem_nhdsWithin] with q hq1 hq
    refine Eventually.of_forall fun z => ?_
    refine (sa16p_phiI_bound hc hs0 hK (hμd q.1 hq.1) (hμw q.1 hq.1) (hμ1 q.1 hq.1) q.2 z).trans ?_
    refine add_le_add le_rfl ?_
    have := sa16p_w_shift q₀.2 q.2 z hq1
    have h0 : 0 ≤ c * 4 ^ (s + 1) * A := by positivity
    exact mul_le_mul_of_nonneg_left this h0
  · refine Eventually.of_forall fun z => ?_
    have h1 : ContinuousWithinAt (fun q : ℝ × 𝔼 => μ q.1 (q.2 - z)) (S ×ˢ univ) q₀ := by
      have hc2 : Continuous (fun q : ℝ × 𝔼 => (q.1, q.2 - z)) :=
        continuous_fst.prodMk (continuous_snd.sub continuous_const)
      have hmaps : MapsTo (fun q : ℝ × 𝔼 => (q.1, q.2 - z)) (S ×ˢ univ) (S ×ˢ univ) :=
        fun q hq => ⟨hq.1, trivial⟩
      have hg : ContinuousWithinAt (fun q : ℝ × 𝔼 => μ q.1 q.2) (S ×ˢ univ) (q₀.1, q₀.2 - z) :=
        hcont _ (hmaps hq₀)
      exact ContinuousWithinAt.comp (f := fun q : ℝ × 𝔼 => (q.1, q.2 - z)) hg hc2.continuousWithinAt hmaps
    have h2 : ContinuousWithinAt (fun q : ℝ × 𝔼 => μ q.1 q.2) (S ×ˢ univ) q₀ := hcont q₀ hq₀
    unfold sa16p_phiI
    by_cases hz : ‖z‖ ≤ 1 / 4
    · simp only [hz, ite_true]
      exact (h1.sub h2).const_smul (K z)
    · simp only [hz, ite_false]
      exact (h1.sub continuousWithinAt_const).const_smul (K z)

set_option synthInstance.maxHeartbeats 400000 in
theorem sa16t_drift_cont (hd : 1 ≤ d) {s MB Λ ΛV G₀ T : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hT : 0 ≤ T)
    {D : WholeDyn d} (hDs : D.s = s) (hV : VHypRd (m + 3) ΛV G₀ D.V) {μ : ℝ → 𝔼 → ℝ}
    (hμ : CoeffHypRd s m Λ T μ) :
    ContinuousOn (fun q : ℝ × 𝔼 => meanFieldDriftW D (μ q.1) q.2) (Icc (0 : ℝ) T ×ˢ univ) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  -- joint continuity of `μ`
  have hμc : ContinuousOn (fun q : ℝ × 𝔼 => μ q.1 q.2) (Icc (0 : ℝ) T ×ˢ univ) := by
    have h0 := (HRS.Whole.AppendixA.Phase2SA16Evolution.coefficient_time_regular d m hd s Λ T hT μ hμ).1 0
      (by omega)
    have : (fun q : ℝ × 𝔼 => μ q.1 q.2) =
        fun q => (continuousMultilinearCurryFin0 ℝ 𝔼 ℝ) (iteratedFDeriv ℝ 0 (μ q.1) q.2) := by
      funext q; rw [iteratedFDeriv_zero_eq_comp]; simp
    rw [this]
    exact (continuousMultilinearCurryFin0 ℝ 𝔼 ℝ).continuous.comp_continuousOn h0
  set A : ℝ := (d : ℝ) ^ (m + 3) * max Λ 0 * 2 ^ (((d : ℝ) + 3) / 2) with hA
  have hreg : ∀ r ∈ Icc (0 : ℝ) T, IsRegularDensityW (m + 3) Λ (μ r) := fun r hr =>
    Phase2SA16R.sa16so_regDensity_of_MF hμ.regular hr
  have hb : ∀ r ∈ Icc (0 : ℝ) T, ∀ j ≤ 1, ∀ y, ‖iteratedFDeriv ℝ j (μ r) y‖ ≤ A * sa16p_w d y := by
    intro r hr j hj y
    refine (sa16p_regular_bounds (hreg r hr) j (by omega) y).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (sa16p_w_pos y).le
    have : (d : ℝ) ^ j ≤ (d : ℝ) ^ (m + 3) := pow_le_pow_right₀ hd1 (by omega)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this (le_max_right _ _)) (by positivity)
  have hμd : ∀ r ∈ Icc (0 : ℝ) T, Differentiable ℝ (μ r) := fun r hr =>
    ((hreg r hr).1).differentiable (by exact_mod_cast (by omega : m + 3 ≠ 0))
  have hμw : ∀ r ∈ Icc (0 : ℝ) T, ∀ y, ‖μ r y‖ ≤ A * sa16p_w d y := fun r hr y => by
    simpa using hb r hr 0 (by omega) y
  have hA0 : 0 ≤ A := by positivity
  have hμ1 : ∀ r ∈ Icc (0 : ℝ) T, ∀ y, ‖fderiv ℝ (μ r) y‖ ≤ A := fun r hr y => by
    rw [sa16p_norm_fderiv_eq]
    exact (hb r hr 1 le_rfl y).trans (mul_le_of_le_one_right hA0 (sa16p_w_le_one y))
  -- the kernel
  set Kf : Fin d → 𝔼 → ℝ := fun j z => rieszKernelGrad d s z j with hKf
  have hKe : ∀ j z, Kf j z = fderiv ℝ (rieszKernel d s) z (EuclideanSpace.single j 1) := fun j z => by
    simp only [hKf, rieszKernelGrad]; exact q09_gradient_apply _ _ _
  have hKm : ∀ j, Measurable (Kf j) := fun j => by
    have : Kf j = fun z => fderiv ℝ (rieszKernel d s) z (EuclideanSpace.single j 1) := funext (hKe j)
    rw [this]; exact measurable_fderiv_apply_const ℝ (rieszKernel d s) _
  have hKb : ∀ j, ∀ z, z ≠ 0 → |Kf j z| ≤ HRS.CZ.Hls.hlsg_c s * ‖z‖ ^ (-s - 1) := fun j z hz => by
    rw [hKe]; exact HRS.CZ.Hls.force_kernel_bound_coord hs0 hz j
  have hc : 0 ≤ HRS.CZ.Hls.hlsg_c s := HRS.CZ.Hls.hlsg_c_nonneg hs0
  have hphi := fun j => sa16t_phiF_cont hd (hKm j) hc hs0 hsd (hKb j) (S := Icc (0 : ℝ) T) (μ := μ) hμd hμw hμ1 hμc
  have hfun : ∀ q : ℝ × 𝔼, q.1 ∈ Icc (0 : ℝ) T →
      convGradConvW (rieszKernelGrad d s) (μ q.1) q.2 = ∑ j : Fin d,
        (sa16p_phiF (Kf j) (μ q.1) q.2) • (EuclideanSpace.single j (1 : ℝ) : 𝔼) := fun q hq =>
    sa16p_conv_eq_phi _ (μ q.1) q.2 (fun j =>
      (sa16p_phi_bound hd (hKm j) hc hs0 hsd (hKb j) (hμd q.1 hq) (hμw q.1 hq) (hμ1 q.1 hq) q.2).1)
  have hfc : ContinuousOn (fun q : ℝ × 𝔼 => convGradConvW (rieszKernelGrad d s) (μ q.1) q.2)
      (Icc (0 : ℝ) T ×ˢ univ) := by
    have : ContinuousOn (fun q : ℝ × 𝔼 => ∑ j : Fin d,
        (sa16p_phiF (Kf j) (μ q.1) q.2) • (EuclideanSpace.single j (1 : ℝ) : 𝔼)) (Icc (0 : ℝ) T ×ˢ univ) :=
      continuousOn_finset_sum _ fun j _ => (hphi j).smul continuousOn_const
    exact this.congr (fun q hq => hfun q hq.1)
  -- the drift
  let Lm : 𝔼 →L[ℝ] 𝔼 := Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) D.M
  have hLm : ∀ v, Torus.matVec D.M v = Lm v := fun v =>
    (LinearMap.congr_fun (Matrix.coe_toEuclideanCLM_eq_toEuclideanLin D.M) v).symm
  have hgV : gradient D.V = (InnerProductSpace.toDual ℝ 𝔼).symm ∘ fderiv ℝ D.V := rfl
  have hgc : Continuous (gradient D.V) := by
    rw [hgV]
    exact (InnerProductSpace.toDual ℝ 𝔼).symm.continuous.comp (hV.1.continuous_fderiv (by simp))
  subst hDs
  have : (fun q : ℝ × 𝔼 => meanFieldDriftW D (μ q.1) q.2) =
      fun q => Lm (convGradConvW (rieszKernelGrad d D.s) (μ q.1) q.2) - gradient D.V q.2 := by
    funext q; simp only [meanFieldDriftW, hLm]
  rw [this]
  exact (Lm.continuous.comp_continuousOn hfc).sub (hgc.comp continuous_snd).continuousOn

end Co5

end HRS.Whole.AppendixA.Phase2SA16P

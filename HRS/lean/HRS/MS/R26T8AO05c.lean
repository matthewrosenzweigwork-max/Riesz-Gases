import HRS.MS.R26T8AO03b

/-!
# S8.2 T8A O05c: `r26t8a_backward_corrector_c12` (Pro contract, verbatim)
The backward corrector `r ↦ QAge 0 (b - r)` is `IsC12On b (eucCollisionSet d N)ᶜ` with derivative `-QAge 1 (b - r)`.
All fields come from the jet continuity / age derivative of O03b under the affine age map `r ↦ b - r`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.PDE.ToolboxRd

theorem r26t8a_o05c_eval_cont {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ} (m : Fin k → E) :
    Continuous (fun A : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ => A m) := by
  refine (LipschitzWith.of_dist_le_mul (K := ∏ i, ‖m i‖₊)
    fun A B => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm]
  have h := (A - B).le_opNorm m
  have e : (A - B) m = A m - B m := rfl
  rw [e] at h
  simpa [mul_comm, NNReal.coe_prod] using h

set_option maxHeartbeats 6400000 in
theorem r26t8a_backward_corrector_c12 (d N : ℕ) (hd : 2≤d) (hN : 2≤N) (a beta m M C Cf c : ℝ)
    (ha : 0<a) (hbeta : 0<beta) (hM : 0≤M) (hC : 0≤C)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ)
    (hPsi : r26t8a_NormalFormFamily d a beta M C rho Psi)
    (horb : r26t8a_FeatureOrbits d a beta m Cf c rho) (alpha : MultiIndex d) (b : ℝ) (hb : 0<b) :
    IsC12On b (eucCollisionSet d N)ᶜ
      (fun r => r26t8a_QAge (N:=N) a beta m rho Psi alpha 0 (b-r)) ∧
    ∀ r∈Set.Icc 0 b, ∀ X∉eucCollisionSet d N,
      derivWithin (fun u => r26t8a_QAge a beta m rho Psi alpha 0 (b-u) X) (Set.Icc 0 b) r=
        -r26t8a_QAge a beta m rho Psi alpha 1 (b-r) X := by
  obtain ⟨hQc0, hQd0, -, -⟩ := r26t8a_normal_age_FTC d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi
    horb alpha 0 (by norm_num)
  obtain ⟨hQc1, -, -, -⟩ := r26t8a_normal_age_FTC d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi
    horb alpha 1 (by norm_num)
  set U : Set (EucConfig d N) := (eucCollisionSet d N)ᶜ with hU
  have hUopen : IsOpen U := r26t8a_o03b_coll_closed.isOpen_compl
  -- test-function bound at every nonnegative age
  have hTB : ∀ s : ℝ, 0 ≤ s → ∃ A, TestBound (testOrder d) A (r26t8a_ageTest a beta m rho alpha 0 s) :=
    fun s hs => ⟨_, horb.bound alpha s hs 0 (by norm_num)⟩
  -- evaluation of the zeroth jet
  let L0 : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => EucConfig d N) ℝ →L[ℝ] ℝ :=
    (continuousMultilinearCurryFin0 ℝ (EucConfig d N) ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  have hL0 : ∀ (g : EucConfig d N → ℝ) (x : EucConfig d N), L0 (iteratedFDeriv ℝ 0 g x) = g x := by
    intro g x
    simp [L0, iteratedFDeriv_zero_eq_comp]
  -- affine age map
  have hmap : ContinuousOn (fun p : ℝ × EucConfig d N => (b - p.1, p.2)) (Set.Icc 0 b ×ˢ U) :=
    ((continuous_const.sub continuous_fst).prodMk continuous_snd).continuousOn
  have hmaps : Set.MapsTo (fun p : ℝ × EucConfig d N => (b - p.1, p.2)) (Set.Icc 0 b ×ˢ U) (Set.Ici 0 ×ˢ U) :=
    fun p hp => ⟨sub_nonneg.2 hp.1.2, hp.2⟩
  have hjet : ∀ ell ≤ 2, ContinuousOn (fun p : ℝ × EucConfig d N =>
      iteratedFDeriv ℝ ell (r26t8a_QAge (N := N) a beta m rho Psi alpha 0 (b - p.1)) p.2) (Set.Icc 0 b ×ˢ U) :=
    fun ell hell => ContinuousOn.comp (g := fun q : ℝ × EucConfig d N =>
      iteratedFDeriv ℝ ell (r26t8a_QAge (N := N) a beta m rho Psi alpha 0 q.1) q.2)
      (f := fun p : ℝ × EucConfig d N => (b - p.1, p.2)) (hQc0 ell hell) hmap hmaps
  -- the time derivative of the backward corrector
  have hder : ∀ X ∉ eucCollisionSet d N, ∀ r ∈ Set.Icc 0 b,
      HasDerivWithinAt (fun u => r26t8a_QAge a beta m rho Psi alpha 0 (b - u) X)
        (-r26t8a_QAge a beta m rho Psi alpha 1 (b - r) X) (Set.Icc 0 b) r := by
    intro X hX r hr
    have h0 := hQd0 X hX (b - r) (sub_nonneg.2 hr.2) 0 (by norm_num)
    have hev : HasDerivWithinAt (fun u => r26t8a_QAge (N := N) a beta m rho Psi alpha 0 u X)
        (r26t8a_QAge (N := N) a beta m rho Psi alpha 1 (b - r) X) (Set.Ici 0) (b - r) := by
      have h1 := L0.hasFDerivAt.comp_hasDerivWithinAt (b - r) h0
      simp only [hL0] at h1
      exact h1
    have hl : HasDerivWithinAt (fun u : ℝ => b - u) (-1) (Set.Icc 0 b) r :=
      ((hasDerivAt_id r).const_sub b).hasDerivWithinAt
    have h2 := hev.scomp r hl (fun u hu => sub_nonneg.2 hu.2)
    have e2 : (-1 : ℝ) • r26t8a_QAge (N := N) a beta m rho Psi alpha 1 (b - r) X =
        -r26t8a_QAge (N := N) a beta m rho Psi alpha 1 (b - r) X := by simp
    rw [e2] at h2
    exact h2
  have hdw : ∀ X ∉ eucCollisionSet d N, ∀ r ∈ Set.Icc 0 b,
      derivWithin (fun u => r26t8a_QAge a beta m rho Psi alpha 0 (b - u) X) (Set.Icc 0 b) r =
        -r26t8a_QAge a beta m rho Psi alpha 1 (b - r) X := fun X hX r hr =>
    (hder X hX r hr).derivWithin ((uniqueDiffOn_Icc hb) r hr)
  refine ⟨?_, fun r hr X hX => hdw X hX r hr⟩
  -- smoothness of each time slice
  have hsm : ∀ t ∈ Set.Icc (0 : ℝ) b, ∀ x ∈ U, ContDiffAt ℝ 2
      (fun y => r26t8a_QAge (N := N) a beta m rho Psi alpha 0 (b - t) y) x := by
    intro t ht x hx
    obtain ⟨A, hA⟩ := hTB (b - t) (sub_nonneg.2 ht.2)
    exact r26t8a_o03b_Q_contDiffAt N hd a beta M C hC rho Psi hPsi hA hx
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- continuity
    have := L0.continuous.comp_continuousOn (hjet 0 (by norm_num))
    refine this.congr fun p hp => ?_
    simp only [Function.comp, hL0]
    rfl
  · intro t ht x hx
    exact ((hsm t ht x hx).differentiableAt (by norm_num)).hasFDerivAt
  · intro t ht x hx
    exact (((hsm t ht x hx).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  · refine continuousOn_clm_apply.2 fun v => ?_
    have := (r26t8a_o05c_eval_cont (E := EucConfig d N) (fun _ : Fin 1 => v)).comp_continuousOn (hjet 1 (by norm_num))
    refine this.congr fun p hp => ?_
    simp [iteratedFDeriv_one_apply]
  · refine continuousOn_clm_apply.2 fun v => continuousOn_clm_apply.2 fun w => ?_
    have := (r26t8a_o05c_eval_cont (E := EucConfig d N) ![v, w]).comp_continuousOn (hjet 2 (by norm_num))
    refine this.congr fun p hp => ?_
    simp [iteratedFDeriv_two_apply]
  · intro x hx t ht
    have := hder x hx t ht
    rw [hdw x hx t ht]
    exact this
  · have h1 : ContinuousOn (fun p : ℝ × EucConfig d N =>
        -r26t8a_QAge (N := N) a beta m rho Psi alpha 1 (b - p.1) p.2) (Set.Icc 0 b ×ˢ U) := by
      have := (L0.continuous.comp_continuousOn ((hQc1 0 (by norm_num)).comp hmap hmaps)).neg
      refine this.congr fun p hp => ?_
      simp only [Function.comp, hL0, Pi.neg_apply]
    refine h1.congr fun p hp => ?_
    exact hdw p.2 hp.2 p.1 hp.1

end HRS.MS.R26T8A

end

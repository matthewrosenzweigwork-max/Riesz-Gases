import HRS.MS.SA12C24

/-!
# S.A.12(c), packet E7.04 (part 9): jets of `perNonlocal - eucNonlocal(χ̂_c μ)` near the centre

For `‖x0 - c‖ < 2`, `L ≥ 40`:
`∂^α(perNonlocal - eucNonlocal(χ̂(·-c)μ))(x0) = ∑_{i,j} M_{ji} ∫_W κ^{(α,i)}(x0-c, z) μ(x0-z) ∂_jF(x0-z) dz`.
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12C

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
open HRS.MH.AdjointRd.Phase2SA12Construction HRS.MH.AdjointRd.Phase2SA12 HRS.MH.AdjointRd.Phase2SA12Near
open HRS.MS.UniqT3

variable {d : ℕ}

theorem sa12c_remainder_jet {s L c0 : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hL : 40 ≤ L)
    {q χ χh γ : Euc d → ℝ} (hχ : IsCutoffPair χ χh) (hγ : IsPeriodicRieszKernel d s L γ)
    (hq : ContDiff ℝ ∞ q)
    (hΘ : ∀ z : Euc d, z ≠ 0 → ‖z‖ < 4 → γ z = rieszKernel d s z + sa12cTh s L c0 q z)
    (M : Matrix (Fin d) (Fin d) ℝ) {μ F : Euc d → ℝ} (hμ : ContDiff ℝ ∞ μ) (hF : ContDiff ℝ ∞ F)
    (hμp : ∀ (x : Euc d) (k : Fin d → ℤ), μ (x + L • latticePt k) = μ x)
    (hFp : ∀ (x : Euc d) (k : Fin d → ℤ), F (x + L • latticePt k) = F x)
    (c x0 : Euc d) (hx0 : ‖x0 - c‖ < 2) {n : ℕ} (α : Fin n → Fin d) :
    partialDeriv α (fun x => perNonlocal L γ M μ F x -
        eucNonlocal s M (fun y => χh (y - c) * μ y) F x) x0 =
      ∑ i : Fin d, ∑ j : Fin d, M j i * ∫ z in sa12cWcell d L,
        sa12cKap s L c0 q χ χh γ (Fin.snoc α i : Fin (n + 1) → Fin d) (x0 - c) z *
          (μ (x0 - z) * fderiv ℝ F (x0 - z) (EuclideanSpace.single j (1 : ℝ))) := by
  have hL0 : 0 < L := by linarith
  set e : Fin d → Euc d := fun j => EuclideanSpace.single j (1 : ℝ) with he
  set fj : Fin d → Euc d → ℝ := fun j y => μ y * fderiv ℝ F y (e j) with hfj
  have hfjs : ∀ j, ContDiff ℝ ∞ (fj j) := fun j =>
    hμ.mul ((hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)
  have hfjp : ∀ j (x : Euc d) (k : Fin d → ℤ), fj j (x + L • latticePt k) = fj j x := by
    intro j x k
    simp only [hfj]
    rw [hμp x k, sa12v_fderiv_periodic L hFp (e j) x k]
  set A := sa12cA s L c0 q χ γ with hA
  set B := sa12cB s L χ with hB
  set T : Fin d → Euc d → ℝ := fun j x =>
    sa12cConv ((sa12cYcell d L x0).indicator (fj j)) A x -
      sa12cConv (fun y => χh (y - c) * fj j y) B x with hT
  have hYm := sa12cYcell_meas L x0
  have hAs : ContDiff ℝ ∞ A := sa12cA_contDiff hL0 hq hχ hγ
  have hBs : ContDiff ℝ ∞ B := sa12cB_contDiff hL0 hχ
  have hAcs : HasCompactSupport A := sa12cA_compact hL0 hχ
  have hBcs : HasCompactSupport B := sa12cB_compact hL0 hχ
  have hTs : ∀ j, ContDiff ℝ ∞ (T j) := by
    intro j
    have h1 := sa12c_conv_contDiff ((hfjs j).continuous.locallyIntegrable.indicator hYm) hAs hAcs
    have hχshift : Continuous (fun y : Euc d => χh (y - c)) :=
      hχ.2.1.continuous.comp (continuous_id.sub continuous_const)
    have hfc : Continuous (fun y : Euc d => χh (y - c) * fj j y) :=
      hχshift.mul (hfjs j).continuous
    have h2 := sa12c_conv_contDiff hfc.locallyIntegrable hBs hBcs
    exact h1.sub h2
  -- the Euclidean near convolution
  set E : Fin d → Euc d → ℝ := fun j x' => ∫ y, rieszKernel d s (x' - y) *
    ((χh (y - c) * μ y) * fderiv ℝ F y (e j)) with hE
  have hg := rieszKernel_locallyIntegrable (d := d) hs0 hsd
  have hEd : ∀ j x', DifferentiableAt ℝ (E j) x' := by
    intro j x'
    set f2 : Euc d → ℝ := fun t => (χh (t - c) * μ t) * fderiv ℝ F t (e j) with hf2
    have hf2s : ContDiff ℝ ∞ f2 :=
      ((hχ.2.1.comp (contDiff_id.sub contDiff_const)).mul hμ).mul
        ((hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)
    have hf2cs : HasCompactSupport f2 := by
      refine HasCompactSupport.intro (isCompact_closedBall c 8) fun y hy => ?_
      rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hy
      have : χh (y - c) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hmem
        have := hχ.2.2.2.1 hmem
        rw [Metric.mem_ball, dist_zero_right] at this
        linarith
      simp [hf2, this]
    have hEq : E j = MeasureTheory.convolution f2 (rieszKernel d s) (ContinuousLinearMap.mul ℝ ℝ) volume := by
      funext x''
      simp only [hE, hf2, MeasureTheory.convolution_def, ContinuousLinearMap.mul_apply']
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      ring
    rw [hEq]
    exact (hf2cs.hasFDerivAt_convolution_left (ContinuousLinearMap.mul ℝ ℝ) (hf2s.of_le (by exact_mod_cast le_top)) hg x').differentiableAt
  -- step (1): on the ball, perNonlocal - eucNonlocal = R
  set R : Euc d → ℝ := fun x => ∑ i : Fin d, ∑ j : Fin d, M j i * D1 i (T j) x with hR
  have hnear : ∀ x : Euc d, ‖x - c‖ < 2 → perNonlocal L γ M μ F x -
      eucNonlocal s M (fun y => χh (y - c) * μ y) F x = R x := by
    intro x hx
    have hball : Metric.ball c 2 ∈ 𝓝 x := Metric.isOpen_ball.mem_nhds (by simpa [dist_eq_norm] using hx)
    have hper : ∀ j, fderiv ℝ (perConv L γ (fj j)) x = fderiv ℝ (E j) x + fderiv ℝ (T j) x := by
      intro j
      have hev : perConv L γ (fj j) =ᶠ[𝓝 x] fun x' => E j x' + T j x' := by
        filter_upwards [hball] with x' hx'
        have hx'c : ‖x' - c‖ < 2 := by simpa [dist_eq_norm] using hx'
        have hid := sa12c_T_identity hs0 hsd hL hχ hγ hq hΘ (f := fj j) (hfjs j).continuous
          (hfjp j) c x0 x' hx0 hx'c hd
        have hEj : E j x' = ∫ y, rieszKernel d s (x' - y) * (χh (y - c) * fj j y) := by
          refine integral_congr_ae (Eventually.of_forall fun y => ?_)
          simp only [hE, hfj]; ring
        rw [hEj]
        simp only [hT]
        linarith [hid]
      rw [hev.fderiv_eq]
      exact fderiv_add (hEd j x) ((hTs j).differentiable (by simp) x)
    unfold perNonlocal eucNonlocal
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := hper j
    simp only [hfj, he] at this
    simp only [hR, D1, hE, he]
    rw [this]
    simp only [ContinuousLinearMap.add_apply]
    ring
  -- step (2): jets agree near x0
  have hev0 : (fun x => perNonlocal L γ M μ F x - eucNonlocal s M (fun y => χh (y - c) * μ y) F x) =ᶠ[𝓝 x0] R := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (by simpa [dist_eq_norm] using hx0 : x0 ∈ Metric.ball c 2)] with x hx
    exact hnear x (by simpa [dist_eq_norm] using hx)
  rw [sa12c_pd_congr hev0 α]
  -- step (3): linearity and commutation
  have hD1s : ∀ i j, ContDiff ℝ ∞ (D1 i (T j)) := fun i j => sa12y_D1_contDiff (hTs j) i
  have hinner : ∀ i : Fin d, partialDeriv α (fun y => ∑ j : Fin d, M j i * D1 i (T j) y) x0 =
      ∑ j : Fin d, M j i * partialDeriv (Fin.snoc α i : Fin (n + 1) → Fin d) (T j) x0 := by
    intro i
    rw [sa12z3_pd_sum (Finset.univ : Finset (Fin d)) (fun j y => D1 i (T j) y) (fun j => M j i) (n := n)
      (fun j _ => sa12z3_cd_of_inf (hD1s i j) n) α x0]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    change partialDeriv α (D1 i (T j)) x0 = _
    rw [sa12z3_pd_D1_comm i n (T j) (sa12z3_cd_of_inf (hTs j) (n + 1)) α x0]
    exact sa12x2_pd_snoc n (T j) (sa12z3_cd_of_inf (hTs j) (n + 1)) α i x0
  have hRfun : R = fun y => ∑ i ∈ (Finset.univ : Finset (Fin d)),
      (fun _ => (1 : ℝ)) i * (fun i y => ∑ j : Fin d, M j i * D1 i (T j) y) i y := by
    funext y; simp [hR]
  rw [hRfun, sa12z3_pd_sum (Finset.univ : Finset (Fin d)) (fun i y => ∑ j : Fin d, M j i * D1 i (T j) y)
    (fun _ => (1 : ℝ)) (n := n)
    (fun i _ => sa12z3_cd_of_inf (ContDiff.sum fun j _ => contDiff_const.mul (hD1s i j)) n) α x0]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [one_mul]
  rw [hinner i]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have hjet := sa12c_T_jet (c0 := c0) hL hχ hγ hq (f := fj j) (hfjs j).continuous c x0 hx0
    (Fin.snoc α i : Fin (n + 1) → Fin d)
  simpa only [hT, hfj, he, mul_comm] using hjet


end HRS.MH.AdjointRd.Phase2SA12C

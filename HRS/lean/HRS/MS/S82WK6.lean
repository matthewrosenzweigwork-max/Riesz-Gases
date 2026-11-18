import HRS.MS.S82WK5

/-!
# S8.2 A04 (S82W), part 7: the cut-off approximants `Θ_n F` converge to `F` in the graph norm
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.S82W
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82U

section cutseq
variable {d N : ℕ}

lemma u4Tame_of_le' {g h : EucConfig d N → ℝ} (hh : u4Tame h)
    (hle : ∀ X : EucConfig d N, X ∉ eucCollisionSet d N → |g X| ≤ |h X|) : u4Tame g := by
  obtain ⟨C, p, q, hC, hp, hq, hb⟩ := hh
  exact ⟨C, p, q, hC, hp, hq, fun X hX => (hle X hX).trans (hb X hX)⟩

/-- a tame function is dominated off collisions by an `L²(canonicalP)` function -/
lemma w_tame_dom (hd : 2 ≤ d) (hN : 0 < N) {a beta : ℝ} (ha : 0 < a) (hbeta : 0 < beta)
    {R : EucConfig d N → ℝ} (hR : u4Tame R) :
    ∃ H : EucConfig d N → ℝ, MemLp H 2 (canonicalP d N a beta) ∧
      ∀ X : EucConfig d N, X ∉ eucCollisionSet d N → |R X| ≤ ‖H X‖ := by
  obtain ⟨C, p, q, hC, hp, hq, hb⟩ := hR
  refine ⟨fun X => C * u4Env p q X, ?_, fun X hX => ?_⟩
  · refine u4Tame_memLp hd hN ha hbeta ?_ ((u4_Env_meas (d := d) (N := N) p q).const_mul C).aestronglyMeasurable
    exact ⟨C, p, q, hC, hp, hq, fun X _ => by
      rw [abs_of_nonneg (mul_nonneg hC (u4Env_nonneg hp X))]⟩
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC (u4Env_nonneg hp X))]
    exact hb X hX

lemma w_jets_zero {Φ : EucConfig d N → ℝ} {X : EucConfig d N} (hev : Φ =ᶠ[𝓝 X] fun _ => 0) :
    fderiv ℝ Φ X = 0 ∧ fderiv ℝ (fderiv ℝ Φ) X = 0 := by
  have h1 : fderiv ℝ Φ =ᶠ[𝓝 X] fun _ => (0 : EucConfig d N →L[ℝ] ℝ) := by
    filter_upwards [hev.eventuallyEq_nhds] with Y hY
    rw [hY.fderiv_eq]; simp
  refine ⟨?_, ?_⟩
  · rw [hev.fderiv_eq]; simp
  · rw [h1.fderiv_eq]; simp

theorem w_cutoff_seq (hd : 2 ≤ d) (hN : 0 < N) {a beta : ℝ} (ha : 0 < a) (hbeta : 0 < beta)
    {F : EucConfig d N → ℝ} (hF : ContDiffOn ℝ 2 F (eucCollisionSet d N)ᶜ) {M A : ℝ} (hM : 0 ≤ M)
    (hA : 0 ≤ A)
    (hb : ∀ X : EucConfig d N, X ∉ eucCollisionSet d N →
      |F X| + ‖fderiv ℝ F X‖ + ‖iteratedFDeriv ℝ 2 F X‖ ≤ A * u4Env M M X) :
    ∃ f : ℕ → EucConfig d N → ℝ,
      (∀ n, ContDiff ℝ 2 (f n) ∧ HasCompactSupport (f n) ∧ tsupport (f n) ⊆ (eucCollisionSet d N)ᶜ) ∧
      Tendsto (fun n => eLpNorm (fun X => f n X - F X) 2 (canonicalP d N a beta)) atTop (𝓝 0) ∧
      (∀ i, Tendsto (fun n => eLpNorm (fun X => Phase2S82.configGrad (f n) X i -
        Phase2S82.configGrad F X i) 2 (canonicalP d N a beta)) atTop (𝓝 0)) ∧
      Tendsto (fun n => eLpNorm (fun X => particleGenerator (quadraticGradientDyn d (criticalS d) a beta) (f n) X -
        particleGenerator (quadraticGradientDyn d (criticalS d) a beta) F X) 2 (canonicalP d N a beta))
        atTop (𝓝 0) := by
  haveI := u4_prob (N := N) hd ha hbeta
  set P := canonicalP d N a beta with hP
  set f : ℕ → EucConfig d N → ℝ := fun n X => wTheta d N ((n : ℝ) + 1) X * F X with hf
  have hm1 : ∀ n : ℕ, (1 : ℝ) ≤ (n : ℝ) + 1 := fun n => by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hmpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => lt_of_lt_of_le one_pos (hm1 n)
  have hfD : ∀ n, ContDiffOn ℝ 2 (f n) (eucCollisionSet d N)ᶜ := fun n =>
    (wTheta_contDiff _).contDiffOn.mul hF
  have hts : ∀ n, tsupport (f n) ⊆ (eucCollisionSet d N)ᶜ := fun n =>
    (tsupport_mul_subset_left (f := wTheta d N ((n : ℝ) + 1)) (g := F)).trans
      (wTheta_tsupport.trans wS_subset_compl)
  have hf2 : ∀ n, ContDiff ℝ 2 (f n) := fun n => w_contDiff_of_tsupport u4_D_open (hfD n) (hts n)
  have hcs : ∀ n, HasCompactSupport (f n) := fun n =>
    (wTheta_hasCompactSupport (hmpos n)).mul_right (f' := F)
  have hΦcd : ∀ n, ContDiffOn ℝ 2 (fun Y => f n Y - F Y) (eucCollisionSet d N)ᶜ := fun n => (hfD n).sub hF
  -- the envelope and the jets of `F`
  set Env : EucConfig d N → ℝ := fun X => A * u4Env M M X with hEnvdef
  have hEnv : u4Tame Env := by
    refine ⟨A, M, M, hA, hM, hM, fun X _ => ?_⟩
    rw [abs_of_nonneg (mul_nonneg hA (u4Env_nonneg hM X))]
  have hEnv0 : ∀ X, 0 ≤ Env X := fun X => mul_nonneg hA (u4Env_nonneg hM X)
  have hF0 : ∀ X, X ∉ eucCollisionSet d N → |F X| ≤ Env X := fun X hX => by
    have := hb X hX; have := norm_nonneg (fderiv ℝ F X); have := norm_nonneg (iteratedFDeriv ℝ 2 F X); linarith
  have hF1 : ∀ X, X ∉ eucCollisionSet d N → ‖fderiv ℝ F X‖ ≤ Env X := fun X hX => by
    have := hb X hX; have := abs_nonneg (F X); have := norm_nonneg (iteratedFDeriv ℝ 2 F X); linarith
  have hF2 : ∀ X, X ∉ eucCollisionSet d N → ‖fderiv ℝ (fderiv ℝ F) X‖ ≤ Env X := fun X hX => by
    have := hb X hX; have := abs_nonneg (F X); have := norm_nonneg (fderiv ℝ F X)
    rw [← w_j2]; linarith
  -- jets of the difference
  have key : ∀ n : ℕ, ∀ X : EucConfig d N, X ∉ eucCollisionSet d N →
      |f n X - F X| ≤ Env X ∧
      ‖fderiv ℝ (fun Y => f n Y - F Y) X‖ ≤ Env X * (1 + wT1 X) ∧
      ‖fderiv ℝ (fderiv ℝ (fun Y => f n Y - F Y)) X‖ ≤ Env X * (1 + 2 * wT1 X + wT2 X) := by
    intro n X hX
    set G : EucConfig d N → ℝ := fun Y => wTheta d N ((n : ℝ) + 1) Y - 1 with hG
    have hGcd : ContDiff ℝ 2 G := (wTheta_contDiff _).sub contDiff_const
    have hΦ : (fun Y => f n Y - F Y) = fun Y => G Y * F Y := by funext Y; simp only [hf, hG]; ring
    have hfG : fderiv ℝ G = fderiv ℝ (wTheta d N ((n : ℝ) + 1)) := by
      funext Y; exact fderiv_sub_const _
    obtain ⟨j1, j2⟩ := wTheta_jets (hm1 n) hX
    obtain ⟨p1, p2⟩ := w_prod_jets (U := (eucCollisionSet d N)ᶜ) u4_D_open hGcd.contDiffOn hF hX
    have hGabs : |G X| ≤ 1 := by
      obtain ⟨h0, h1⟩ := wTheta_01 ((n : ℝ) + 1) X
      rw [hG]; simp only; rw [abs_le]; constructor <;> linarith
    have e0 := hF0 X hX
    have e1 := hF1 X hX
    have e2 := hF2 X hX
    have n1 := norm_nonneg (fderiv ℝ G X)
    have n2 := norm_nonneg (fderiv ℝ (fderiv ℝ G) X)
    rw [hfG] at p1 p2 n1 n2
    rw [hΦ]
    have hT1 : 0 ≤ wT1 X := wT1_nonneg wB_nonneg X hX
    have hT2 : 0 ≤ wT2 X := (by
      unfold wT2
      refine add_nonneg (Finset.sum_nonneg fun p _ => ?_) (sq_nonneg _)
      unfold wb2
      split_ifs with h
      · linarith [wB_nonneg]
      · have hne : 0 < ‖X p.1 - X p.2‖ := norm_pos_iff.2 (sub_ne_zero.2 (fun h' => hX ⟨p.1, p.2, h, h'⟩))
        exact mul_nonneg (by linarith [wB_nonneg]) (Real.rpow_nonneg hne.le _))
    refine ⟨?_, ?_, ?_⟩
    · have h0 : f n X - F X = G X * F X := by simp only [hf, hG]; ring
      rw [h0, abs_mul]
      calc |G X| * |F X| ≤ 1 * Env X := mul_le_mul hGabs e0 (abs_nonneg _) zero_le_one
        _ = Env X := one_mul _
    · refine p1.trans ?_
      have := mul_le_mul hGabs e1 (norm_nonneg (fderiv ℝ F X)) zero_le_one
      have := mul_le_mul j1 e0 (abs_nonneg _) hT1
      nlinarith
    · refine p2.trans ?_
      have := mul_le_mul hGabs e2 (norm_nonneg (fderiv ℝ (fderiv ℝ F) X)) zero_le_one
      have h5 := mul_le_mul j1 e1 (norm_nonneg (fderiv ℝ F X)) hT1
      have h6 := mul_le_mul j2 e0 (abs_nonneg _) hT2
      nlinarith
  have hev : ∀ X : EucConfig d N, X ∉ eucCollisionSet d N → ∀ᶠ n : ℕ in atTop,
      (fun Y => f n Y - F Y) =ᶠ[𝓝 X] fun _ => 0 := by
    intro X hX
    filter_upwards [wTheta_eventually_one hX] with n hn
    filter_upwards [hn] with Y hY
    simp only [hf, hY]; ring
  have hae : ∀ᵐ X ∂P, X ∉ eucCollisionSet d N := by
    rw [ae_iff]; simpa using u4_P_coll hd N a beta
  have hR1 : u4Tame (fun X => Env X * (1 + wT1 X)) :=
    u4Tame_mul hEnv (u4Tame_add (u4Tame_const 1) wT1_tame)
  have hR2' : u4Tame (fun X => Env X * (1 + 2 * wT1 X + wT2 X)) :=
    u4Tame_mul hEnv (u4Tame_add (u4Tame_add (u4Tame_const 1) (u4Tame_const_mul 2 wT1_tame)) wT2_tame)
  have hR2 : u4Tame (fun X => beta⁻¹ * N * d * (Env X * (1 + 2 * wT1 X + wT2 X)) +
      wGb d N a X * (Env X * (1 + wT1 X))) :=
    u4Tame_add (u4Tame_const_mul _ hR2') (u4Tame_mul (wGb_tame hd a) hR1)
  obtain ⟨H0, hH0, hH0b⟩ := w_tame_dom hd hN ha hbeta hEnv
  obtain ⟨H1, hH1, hH1b⟩ := w_tame_dom hd hN ha hbeta hR1
  obtain ⟨H2, hH2, hH2b⟩ := w_tame_dom hd hN ha hbeta hR2
  refine ⟨f, fun n => ⟨hf2 n, hcs n, hts n⟩, ?_, fun i => ?_, ?_⟩
  · refine w_l2_dom (g := fun n X => f n X - F X) hH0 (fun n => ?_) (fun n => ?_) ?_
    · exact u4_aesm_of_contOn (d := d) (N := N) (a := a) (beta := beta) hd
        ((hfD n).continuousOn.sub hF.continuousOn)
    · filter_upwards [hae] with X hX
      exact (key n X hX).1.trans ((le_abs_self _).trans (hH0b X hX)) |>.trans (by rw [Real.norm_eq_abs]) |>.trans
        (by simp [Real.norm_eq_abs])
    · filter_upwards [hae] with X hX
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev X hX] with n hn
      have h0 := hn.self_of_nhds
      simp only at h0
      exact h0.symm
  · refine w_l2_dom (g := fun n X => Phase2S82.configGrad (f n) X i - Phase2S82.configGrad F X i) hH1
      (fun n => ?_) (fun n => ?_) ?_
    · exact u4_aesm_of_contOn (d := d) (N := N) (a := a) (beta := beta) hd
        ((w_grad_cont (hfD n) i).sub (w_grad_cont hF i))
    · filter_upwards [hae] with X hX
      rw [← w_configGrad_sub (hfD n) hF hX i]
      exact ((u4_configGrad_norm_le (hΦcd n) hX i).trans (key n X hX).2.1).trans
        ((le_abs_self _).trans (hH1b X hX))
    · filter_upwards [hae] with X hX
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev X hX] with n hn
      rw [← w_configGrad_sub (hfD n) hF hX i]
      have hz := (w_jets_zero hn).1
      have := u4_configGrad_norm_le (hΦcd n) hX i
      rw [hz] at this
      simp only [norm_zero] at this
      exact (norm_le_zero_iff.1 this).symm
  · refine w_l2_dom (g := fun n X => particleGenerator (quadraticGradientDyn d (criticalS d) a beta) (f n) X -
      particleGenerator (quadraticGradientDyn d (criticalS d) a beta) F X) hH2 (fun n => ?_) (fun n => ?_) ?_
    · exact u4_aesm_of_contOn (d := d) (N := N) (a := a) (beta := beta) hd
        ((w_gen_cont hd a beta (hfD n)).sub (w_gen_cont hd a beta hF))
    · filter_upwards [hae] with X hX
      rw [← w_gen_sub (hfD n) hF hX]
      have hgb := w_gen_bound hd hN ha.le beta hbeta (hΦcd n) hX
      rw [w_j2] at hgb
      obtain ⟨k0, k1, k2⟩ := key n X hX
      have hν : 0 ≤ beta⁻¹ * N * d := by positivity
      have hG0 := wGb_nonneg hd ha.le (N := N) X
      refine (hgb.trans ?_).trans ((le_abs_self _).trans (hH2b X hX))
      exact add_le_add (mul_le_mul_of_nonneg_left k2 hν) (mul_le_mul_of_nonneg_left k1 hG0)
    · filter_upwards [hae] with X hX
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev X hX] with n hn
      rw [← w_gen_sub (hfD n) hF hX]
      obtain ⟨z1, z2⟩ := w_jets_zero hn
      have hgb := w_gen_bound hd hN ha.le beta hbeta (hΦcd n) hX
      rw [w_j2, z1, z2] at hgb
      simp only [ContinuousLinearMap.opNorm_zero, mul_zero, add_zero] at hgb
      exact (abs_nonpos_iff.1 hgb).symm

end cutseq

end HRS.MS.S82W

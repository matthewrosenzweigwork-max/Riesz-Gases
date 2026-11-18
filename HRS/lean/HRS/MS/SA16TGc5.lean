import HRS.MS.SA16TGc4

/-!
# S.A.16 (SA16T) Gc5: strong continuity of `r ↦ T_r` on the jets of `C_c^∞` functions and on all of `W^{k,p}`
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16P Phase2SA16Q

section Gc5
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

lemma sa16t_mu_bounds {g : Euc d → ℝ} (hc : Continuous g) {A : ℝ} (hb : ∀ y, |g y| ≤ A) (n : ℕ) :
    ContDiff ℝ 1 (sa16j_conv (sa16y_rho d n) g) ∧ (∀ x, |sa16j_conv (sa16y_rho d n) g x| ≤ A) ∧
      ∀ x, ‖fderiv ℝ (sa16j_conv (sa16y_rho d n) g) x‖ ≤ sa16t_Crho d n 1 * A := by
  have hA : 0 ≤ A := (abs_nonneg _).trans (hb 0)
  refine ⟨(contDiff_infty.1 (sa16y_mollify_smooth n hc)) 1, fun x => sa16y_mollify_bound n hc hb x, fun x => ?_⟩
  rw [sa16p_norm_fderiv_eq]
  exact sa16t_mollify_small hc n 1 x (fun z _ => hb _) le_rfl

lemma sa16t_slice_cont_real {S : Set ℝ} {μ : ℝ → Euc d → ℝ}
    (hμ : ContinuousOn (fun q : ℝ × Euc d => μ q.1 q.2) (S ×ˢ univ)) {r : ℝ} (hr : r ∈ S) : Continuous (μ r) := by
  have hc : Continuous (fun y : Euc d => (r, y)) := continuous_const.prodMk continuous_id
  have := hμ.comp (f := fun y : Euc d => (r, y)) (s := univ) hc.continuousOn (fun y _ => ⟨hr, trivial⟩)
  exact continuousOn_univ.1 this

set_option maxHeartbeats 1600000 in
theorem sa16t_cont_jet (k n : ℕ) (hd : 1 ≤ d) (s MB : ℝ) (hs0 : 0 ≤ s) (hs2 : s ≤ (d : ℝ) - 2)
    (hfar : (d : ℝ) < p * (s + 1)) (M : Matrix (Fin d) (Fin d) ℝ) (hM : ∀ i j, |M i j| ≤ MB)
    {S : Set ℝ} (hS : IsCompact S) {μ : ℝ → Euc d → ℝ}
    (hμc : ContinuousOn (fun q : ℝ × Euc d => μ q.1 q.2) (S ×ˢ univ)) {Aμ : ℝ}
    (hμb : ∀ r ∈ S, ∀ y, |μ r y| ≤ Aμ) {T : ℝ → WmpSpace d k p →L[ℝ] WmpSpace d k p}
    (hT : ∀ r ∈ S, SA16SubOp d k p s M (sa16t_mu d n μ r) (T r)) (φ : ccSub d) {r₀ : ℝ} (hr₀ : r₀ ∈ S) :
    ContinuousWithinAt (fun r => T r (sa16r_Jcc d k p φ)) S r₀ := by
  have hd2 : 2 ≤ d := by
    have : (2 : ℝ) ≤ d := by linarith
    exact_mod_cast this
  obtain ⟨C, hC, hsmall⟩ := sa16t_G_small (p := p) d k hd s MB hs0 hs2 hfar
  obtain ⟨Cn, hCn0, hCn⟩ := sa16t_nu_decay d (k + 3) n
  obtain ⟨R0', hR0'⟩ := φ.2.2.isCompact.isBounded.subset_closedBall (0 : Euc d)
  set R0 : ℝ := max R0' 1 with hR0def
  have hR0 : 1 ≤ R0 := le_max_right _ _
  have hF : tsupport φ.1 ⊆ closedBall (0 : Euc d) R0 :=
    hR0'.trans (closedBall_subset_closedBall (le_max_left _ _))
  have hχ : ∀ y, ‖y‖ ≤ R0 → sa16j_chi d R0 y = 1 := fun y hy => sa16j_chi_one d (by linarith) hy
  set Wd : ℝ := (1 + 2 * R0) ^ ((d : ℝ) + 3) with hWd
  have hWd0 : 0 < Wd := Real.rpow_pos_of_pos (by positivity) _
  set Jn : ℝ := ‖sa16r_Jcc d k p φ‖ with hJn
  have hJn0 : 0 ≤ Jn := norm_nonneg _
  set Kc : ℝ := C * ((Cn + 1) * Wd) * (Jn + 1) with hKc
  have hKc0 : 0 < Kc := by positivity
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  set A : ℝ := ε / (2 * Kc) with hA
  have hA0 : 0 < A := by positivity
  set Rr : ℝ := 2 * R0 + 1 with hRr
  have hK : IsCompact (S ×ˢ closedBall (0 : Euc d) Rr) := hS.prod (isCompact_closedBall _ _)
  have hKsub : S ×ˢ closedBall (0 : Euc d) Rr ⊆ S ×ˢ univ := prod_mono le_rfl (subset_univ _)
  have hunif := hK.uniformContinuousOn_of_continuous (hμc.mono hKsub)
  obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuousOn_iff.1 hunif A hA0
  refine ⟨δ, hδ0, fun r hrS hrd => ?_⟩
  -- the difference of the densities on the ball
  have hGb : ∀ y : Euc d, ‖y‖ ≤ 2 * R0 + 1 → |μ r y - μ r₀ y| ≤ A := by
    intro y hy
    have hq : (r, y) ∈ S ×ˢ closedBall (0 : Euc d) Rr := ⟨hrS, by simpa using hy⟩
    have hq' : (r₀, y) ∈ S ×ˢ closedBall (0 : Euc d) Rr := ⟨hr₀, by simpa using hy⟩
    have hd' : dist (r, y) (r₀, y) < δ := by
      rw [Prod.dist_eq, dist_self]
      exact max_lt hrd hδ0
    have := hδ _ hq _ hq' hd'
    rw [Real.dist_eq] at this
    exact this.le
  have hcr : Continuous (μ r) := sa16t_slice_cont_real hμc hrS
  have hcr₀ : Continuous (μ r₀) := sa16t_slice_cont_real hμc hr₀
  have hGc : Continuous (fun y => μ r y - μ r₀ y) := hcr.sub hcr₀
  set ν : Euc d → ℝ := fun y => sa16j_chi d R0 y * sa16j_conv (sa16y_rho d n) (fun y => μ r y - μ r₀ y) y with hν
  have hνd : ContDiff ℝ ((k + 3 : ℕ) : WithTop ℕ∞) ν :=
    contDiff_infty.1 ((sa16j_chi_contDiff d R0).mul (sa16y_mollify_smooth n hGc)) (k + 3)
  set Aν : ℝ := (Cn + 1) * Wd * A with hAν
  have hAν0 : 0 < Aν := by positivity
  have hdecν : ∀ j ≤ k + 3, ∀ y, ‖iteratedFDeriv ℝ j ν y‖ ≤ Aν * sa16p_w d y := by
    intro j hj y
    refine (hCn R0 hR0 _ hGc A hA0.le hGb j hj y).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (sa16p_w_pos y).le
    rw [hAν]
    have : Cn * (1 + 2 * R0) ^ ((d : ℝ) + 3) * A ≤ (Cn + 1) * Wd * A := by
      rw [hWd]; nlinarith [mul_nonneg hCn0 hA0.le, mul_pos hWd0 hA0]
    exact this
  obtain ⟨Tν, hTν, hTνn⟩ := hsmall M hM ν Aν hAν0 hνd hdecν
  -- the identification
  obtain ⟨hca, hb0a, hb1a⟩ := sa16t_mu_bounds hcr (hμb r hrS) n
  obtain ⟨hcb, hb0b, hb1b⟩ := sa16t_mu_bounds hcr₀ (hμb r₀ hr₀) n
  have hsub : sa16j_conv (sa16y_rho d n) (fun y => μ r y - μ r₀ y) = fun x =>
      sa16j_conv (sa16y_rho d n) (μ r) x - sa16j_conv (sa16y_rho d n) (μ r₀) x := sa16t_conv_sub hcr hcr₀ n
  have hνF : HRS.MH.AdjointRd.eucNonlocal s M ν φ.1 =
      fun x => HRS.MH.AdjointRd.eucNonlocal s M (sa16t_mu d n μ r) φ.1 x -
        HRS.MH.AdjointRd.eucNonlocal s M (sa16t_mu d n μ r₀) φ.1 x := by
    funext x
    have h1 : ν = fun y => sa16j_chi d R0 y * (sa16t_mu d n μ r y - sa16t_mu d n μ r₀ y) := by
      funext y; simp only [hν, hsub, sa16t_mu]
    rw [h1, sa16t_F_local s M (fun y => sa16t_mu d n μ r y - sa16t_mu d n μ r₀ y) (sa16j_chi d R0) φ.1 hF hχ]
    exact sa16t_F_sub hd2 hs0 hs2 M hca hcb hb0a hb1a hb0b hb1b (sa16so_schw φ) x
  have hsplit : T r (sa16r_Jcc d k p φ) = T r₀ (sa16r_Jcc d k p φ) + Tν (sa16r_Jcc d k p φ) := by
    refine sa16r_wrep_inj d k p _ _ ?_
    filter_upwards [hT r hrS φ, hT r₀ hr₀ φ, hTν φ,
      sa16r_wrep_add d k p (T r₀ (sa16r_Jcc d k p φ)) (Tν (sa16r_Jcc d k p φ))] with x h1 h2 h3 h4
    rw [h1, h4, h2, h3, congrFun hνF x]
    ring
  rw [dist_eq_norm, hsplit, add_sub_cancel_left]
  calc ‖Tν (sa16r_Jcc d k p φ)‖ ≤ ‖Tν‖ * Jn := Tν.le_opNorm _
    _ ≤ (C * Aν) * (Jn + 1) := mul_le_mul hTνn (by linarith) hJn0 (by positivity)
    _ = ε / 2 := by rw [hAν, hA, hKc]; field_simp
    _ < ε := by linarith

theorem sa16t_G_strong (k n : ℕ) (hd : 1 ≤ d) (s MB : ℝ) (hs0 : 0 ≤ s) (hs2 : s ≤ (d : ℝ) - 2)
    (hfar : (d : ℝ) < p * (s + 1)) (M : Matrix (Fin d) (Fin d) ℝ) (hM : ∀ i j, |M i j| ≤ MB)
    {S : Set ℝ} (hS : IsCompact S) {μ : ℝ → Euc d → ℝ}
    (hμc : ContinuousOn (fun q : ℝ × Euc d => μ q.1 q.2) (S ×ˢ univ)) {Aμ : ℝ}
    (hμb : ∀ r ∈ S, ∀ y, |μ r y| ≤ Aμ) {T : ℝ → WmpSpace d k p →L[ℝ] WmpSpace d k p}
    (hT : ∀ r ∈ S, SA16SubOp d k p s M (sa16t_mu d n μ r) (T r)) {C0 : ℝ} (hTb : ∀ r ∈ S, ‖T r‖ ≤ C0)
    (Y : WmpSpace d k p) : ContinuousOn (fun r => T r Y) S := by
  intro r₀ hr₀
  refine sa16t_strong_of_dense hr₀ hTb (D := Set.range (sa16r_Jcc d k p)) (sa16r_Jcc_dense d k p) ?_ Y
  rintro _ ⟨φ, rfl⟩
  exact sa16t_cont_jet k n hd s MB hs0 hs2 hfar M hM hS hμc hμb hT φ hr₀

end Gc5

end HRS.Whole.AppendixA.Phase2SA16R

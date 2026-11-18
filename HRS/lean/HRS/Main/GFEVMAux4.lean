import HRS.Main.GFEVMAux3

/-!
# Packet GFEVM, part 4: Lipschitz estimate in `E_{γ+2}` and strong continuity `cont_E`
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.GF

open HRS HRS.PDE HRS.PDE.ET HRS.Uniform HRS.Uniform.Q54 HRS.Uniform.Q48b

variable {d : ℕ}

section Lip

variable {γ T K : ℝ} {Up : ℝ → ℝ → (Torus d → ℝ) → Torus d → ℝ} {Lb : ℝ → (Torus d → ℝ) → Torus d → ℝ}
  {VH : ℝ → ℝ → NegSobolev d γ →L[ℝ] NegSobolev d γ}
  {VE : ℝ → ℝ → NegSobolev d (γ + 2) →L[ℝ] NegSobolev d (γ + 2)}
  {A : ℝ → NegSobolev d γ →L[ℝ] NegSobolev d (γ + 2)}
  (h : GfmAbs γ T K Up Lb) (o : GfmOps γ T K Up Lb VH VE A)

include h o

theorem gfm_lip {t u u' : ℝ} (hu : 0 ≤ u) (huu' : u ≤ u') (hu't : u' ≤ t) (htT : t ≤ T)
    (x : NegSobolev d γ) :
    ‖VE t u' (gfmJ γ x) - VE t u (gfmJ γ x)‖ ≤ K * K * (u' - u) * ‖x‖ := by
  have hK0 : 0 ≤ K := by linarith [h.hK]
  have hd0 : 0 ≤ u' - u := sub_nonneg.2 huu'
  refine gfm_norm_le_of_eval _ (by positivity) fun c => ?_
  have hφs : Torus.IsSmooth (phiOf (γ + 2) c) := phiOf_smooth _ c
  have hφE : gfmCls (γ + 2) (phiOf (γ + 2) c) := (h.upE u t hu (huu'.trans hu't) htT).smooth _ hφs
  have e1 : NegSobolev.eval (VE t u' (gfmJ γ x) - VE t u (gfmJ γ x)) (phiOf (γ + 2) c) =
      -(NegSobolev.eval x (Up u t (phiOf (γ + 2) c)) - NegSobolev.eval x (Up u' t (phiOf (γ + 2) c))) := by
    rw [eval_sub_left _ _ hφE.2, o.dualE t u' (hu.trans huu') hu't htT _ _ hφE,
      o.dualE t u hu (huu'.trans hu't) htT _ _ hφE, gfmJ_apply,
      gfev_eval_embed (by linarith : γ ≤ γ + 2), gfev_eval_embed (by linarith : γ ≤ γ + 2)]
    ring
  rw [e1, h.duh t u u' hu huu' hu't htT _ hφs x, abs_neg]
  have hC : ∀ σ ∈ Set.uIoc u u', ‖NegSobolev.eval x (Lb σ (Up σ t (phiOf (γ + 2) c)))‖ ≤
      ‖x‖ * (K * (K * sobolevNorm (γ + 2) (phiOf (γ + 2) c))) := by
    intro σ hσ
    rw [Set.uIoc_of_le huu'] at hσ
    have hσ0 : 0 ≤ σ := hu.trans hσ.1.le
    have hσt : σ ≤ t := hσ.2.trans hu't
    have hψ : gfmCls (γ + 2) (Up σ t (phiOf (γ + 2) c)) := h.clsE σ t hσ0 hσt htT _ hφE
    obtain ⟨hm, hn⟩ := (h.gen σ hσ0 (hσt.trans htT)).bd _ hψ
    obtain ⟨-, hn2⟩ := (h.upE σ t hσ0 hσt htT).bd _ hφE
    rw [Real.norm_eq_abs]
    refine (gfev_abs_eval_le x hm).trans ?_
    exact mul_le_mul_of_nonneg_left (hn.trans (mul_le_mul_of_nonneg_left hn2 hK0)) (norm_nonneg _)
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hC
  rw [Real.norm_eq_abs] at hint
  calc |∫ σ in u..u', NegSobolev.eval x (Lb σ (Up σ t (phiOf (γ + 2) c)))|
      ≤ ‖x‖ * (K * (K * sobolevNorm (γ + 2) (phiOf (γ + 2) c))) * |u' - u| := hint
    _ = K * K * (u' - u) * ‖x‖ * ‖eFin d c‖ := by
        rw [abs_of_nonneg hd0, gfm_sobolevNorm_phiOf]; ring

theorem gfm_lip' {t u u' : ℝ} (hu : 0 ≤ u) (hu' : 0 ≤ u') (hut : u ≤ t) (hu't : u' ≤ t) (htT : t ≤ T)
    (x : NegSobolev d γ) :
    ‖VE t u' (gfmJ γ x) - VE t u (gfmJ γ x)‖ ≤ K * K * |u' - u| * ‖x‖ := by
  rcases le_total u u' with h1 | h1
  · rw [abs_of_nonneg (sub_nonneg.2 h1)]
    exact gfm_lip h o hu h1 hu't htT x
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h1), norm_sub_rev]
    exact gfm_lip h o hu' h1 hut htT x

theorem gfm_lip_joint {t r t' r' : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t) (htt' : t ≤ t') (hr' : 0 ≤ r')
    (hr't' : r' ≤ t') (ht'T : t' ≤ T) (x : NegSobolev d γ) :
    ‖VE t' r' (gfmJ γ x) - VE t r (gfmJ γ x)‖ ≤
      K * K * (1 + K) * (|t' - t| + |r' - r|) * ‖x‖ := by
  have hK0 : 0 ≤ K := by linarith [h.hK]
  have ht0 : 0 ≤ t := hr.trans hrt
  have h1 := gfm_lip' h o hr hr' (hrt.trans htt') hr't' ht'T x
  -- second term
  set y : NegSobolev d γ := VH t r x with hy
  have hcomp : VE t' r (gfmJ γ x) = VE t' t (gfmJ γ y) := by
    have e1 := congrArg (fun F => F (gfmJ γ x)) (gfm_comp_E h o hr hrt htt' ht'T)
    have e2 := congrArg (fun F => F x) (gfm_intertwine h o hr hrt (htt'.trans ht'T))
    simp only [ContinuousLinearMap.comp_apply] at e1 e2
    rw [← e1, e2]
  have hint : VE t r (gfmJ γ x) = gfmJ γ y := by
    have e2 := congrArg (fun F => F x) (gfm_intertwine h o hr hrt (htt'.trans ht'T))
    simpa using e2
  have h2 : ‖VE t' r (gfmJ γ x) - VE t r (gfmJ γ x)‖ ≤ K * K * (t' - t) * (K * ‖x‖) := by
    rw [hcomp, hint]
    have hl := gfm_lip h o ht0 htt' le_rfl ht'T y
    rw [gfm_self_E h o (ht0.trans htt') ht'T, ContinuousLinearMap.one_apply, norm_sub_rev] at hl
    refine hl.trans ?_
    have hyn : ‖y‖ ≤ K * ‖x‖ := ((VH t r).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (o.bdH t r hr hrt (htt'.trans ht'T)) (norm_nonneg _))
    exact mul_le_mul_of_nonneg_left hyn (mul_nonneg (mul_nonneg hK0 hK0) (sub_nonneg.2 htt'))
  calc ‖VE t' r' (gfmJ γ x) - VE t r (gfmJ γ x)‖
      ≤ ‖VE t' r' (gfmJ γ x) - VE t' r (gfmJ γ x)‖ + ‖VE t' r (gfmJ γ x) - VE t r (gfmJ γ x)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ K * K * |r' - r| * ‖x‖ + K * K * (t' - t) * (K * ‖x‖) := add_le_add h1 h2
    _ ≤ K * K * (1 + K) * (|t' - t| + |r' - r|) * ‖x‖ := by
        rw [abs_of_nonneg (sub_nonneg.2 htt')]
        have ha : 0 ≤ |r' - r| := abs_nonneg _
        have hb : 0 ≤ t' - t := sub_nonneg.2 htt'
        have hn : 0 ≤ ‖x‖ := norm_nonneg _
        nlinarith [mul_nonneg (mul_nonneg hK0 hK0) (mul_nonneg hn (add_nonneg (mul_nonneg hK0 ha) hb))]

theorem gfm_cont_E (y : NegSobolev d (γ + 2)) :
    ContinuousOn (fun p : ℝ × ℝ => VE p.1 p.2 y) {p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T} := by
  have hK0 : 0 ≤ K := by linarith [h.hK]
  refine gfm_continuousOn_of_dense (Vf := fun p : ℝ × ℝ => VE p.1 p.2) K
    (fun p hp => o.bdE p.1 p.2 hp.1 hp.2.1 hp.2.2)
    (Dn := Set.range (NegSobolev.embed (γ + 2) : NegSobolev d γ → NegSobolev d (γ + 2)))
    (gfm_denseRange_embed γ) ?_ y
  rintro _ ⟨x, rfl⟩
  have hL0 : 0 ≤ K * K * (1 + K) * 2 * ‖x‖ := by positivity
  have key : ∀ p ∈ {p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T}, ∀ q ∈ {p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T},
      dist (VE p.1 p.2 (NegSobolev.embed (γ + 2) x)) (VE q.1 q.2 (NegSobolev.embed (γ + 2) x)) ≤
        (Real.toNNReal (K * K * (1 + K) * 2 * ‖x‖) : ℝ) * dist p q := by
    intro p hp q hq
    rw [Real.coe_toNNReal _ hL0, dist_eq_norm]
    have hd1 : |p.1 - q.1| ≤ dist p q := by
      rw [Prod.dist_eq, Real.dist_eq]; exact le_max_left _ _
    have hd2 : |p.2 - q.2| ≤ dist p q := by
      rw [Prod.dist_eq, Real.dist_eq]; exact le_max_right _ _
    have hc : 0 ≤ K * K * (1 + K) * ‖x‖ := by positivity
    rcases le_total p.1 q.1 with hpq | hpq
    · have := gfm_lip_joint h o hp.1 hp.2.1 hpq hq.1 hq.2.1 hq.2.2 x
      rw [norm_sub_rev] at this
      refine this.trans ?_
      rw [abs_sub_comm q.1 p.1, abs_sub_comm q.2 p.2]
      nlinarith [mul_le_mul_of_nonneg_left (add_le_add hd1 hd2) hc]
    · have := gfm_lip_joint h o hq.1 hq.2.1 hpq hp.1 hp.2.1 hp.2.2 x
      refine this.trans ?_
      nlinarith [mul_le_mul_of_nonneg_left (add_le_add hd1 hd2) hc, abs_sub_comm p.1 q.1, abs_sub_comm p.2 q.2]
  exact (LipschitzOnWith.of_dist_le_mul (K := Real.toNNReal (K * K * (1 + K) * 2 * ‖x‖))
    (f := fun p : ℝ × ℝ => VE p.1 p.2 (NegSobolev.embed (γ + 2) x)) key).continuousOn

end Lip

end HRS.GF

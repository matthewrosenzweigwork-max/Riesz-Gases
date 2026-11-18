import HRS.MS.S113X2B2
import HRS.MS.S113X2B3A
import HRS.MS.S113X2B4
import HRS.MS.S113X2B5

/-! # S11.3 X2 part B, B6: the mollified chain inequality (statement parenthesized: `(∫ F_t) - ∫ F_s`; needs the parenthesized `sub` of B5) -/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Set Filter Topology intervalIntegral

namespace HRS.MS.S113X2B


variable {n : ℕ} {ν : ℝ} {b : s113b_E n → s113b_E n} {q : ℝ → s113b_E n → ℝ} {T : ℝ}
  {u : ℝ → s113b_E n → ℝ} {K G : Set (s113b_E n)} {B : ℝ}

lemma s113b_ii {f : ℝ → ℝ} (hf : Measurable f) {s t M : ℝ} (hst : s ≤ t)
    (hb : ∀ τ ∈ Icc s t, |f τ| ≤ M) : IntervalIntegrable f volume s t :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hst).2 <|
    Measure.integrableOn_of_bounded (M := M) (by simp) hf.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun τ hτ => by
        rw [Real.norm_eq_abs]; exact hb τ (Ioc_subset_Icc_self hτ)))

lemma s113b_iprod {f : ℝ × s113b_E n → ℝ} (hf : Measurable f) {A : Set ℝ} {S : Set (s113b_E n)}
    (hA : MeasurableSet A) (hAf : volume A < ⊤) (hS : IsCompact S) {C : ℝ}
    (hb : ∀ z ∈ A ×ˢ S, |f z| ≤ C) :
    Integrable f ((volume.restrict A).prod (volume.restrict S)) := by
  have : IsFiniteMeasure (volume.restrict A) := ⟨by simpa using hAf⟩
  have : IsFiniteMeasure (volume.restrict S) := ⟨by simpa using hS.measure_lt_top⟩
  refine Integrable.of_bound hf.aestronglyMeasurable C ?_
  rw [Measure.prod_restrict]
  exact (ae_restrict_iff' (hA.prod hS.measurableSet)).2
    (ae_of_all _ fun z hz => by rw [Real.norm_eq_abs]; exact hb z hz)

lemma s113b_int_of_bdd {f : s113b_E n → ℝ} (hf : Measurable f) {S : Set (s113b_E n)} (hS : IsCompact S)
    {C : ℝ} (hb : ∀ x, |f x| ≤ C) (h0 : ∀ x ∉ S, f x = 0) : Integrable f :=
  IntegrableOn.integrable_of_forall_notMem_eq_zero
    (Measure.integrableOn_of_bounded (M := C) hS.measure_lt_top.ne hf.aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hb x)) h0

lemma s113b_hyp (hD : s113b_Data ν b q T u K G B) {τ : ℝ} (hτ : τ ∈ Icc 0 T) :
    Measurable (u τ) ∧ (∀ y, |u τ y| ≤ B) ∧ IsCompact K ∧ ∀ y, y ∉ K → u τ y = 0 :=
  ⟨hD.hum.comp measurable_prodMk_left, fun y => by rw [abs_of_nonneg (hD.hu0 _ _)]; exact hD.huB τ hτ y,
    hD.hKc, hD.hKu τ⟩

lemma s113b_fd_refl {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {f : s113b_E n → V}
    (hf : Differentiable ℝ f) (x y : s113b_E n) :
    fderiv ℝ (fun y => f (x - y)) y = -(fderiv ℝ f (x - y)) := by
  have h : HasFDerivAt (fun y => f (x - y)) ((fderiv ℝ f (x - y)).comp (-ContinuousLinearMap.id ℝ _)) y :=
    (hf (x - y)).hasFDerivAt.comp y ((hasFDerivAt_id y).const_sub x)
  rw [h.fderiv]; ext w; simp

lemma s113b_lap_refl {f : s113b_E n → ℝ} (hf : s113b_Cinf f) (x y : s113b_E n) :
    s113b_lap (fun y => f (x - y)) y = s113b_lap f (x - y) := by
  have h1 : Differentiable ℝ f := hf.differentiable (by simp)
  have h2 : Differentiable ℝ (fderiv ℝ f) := (s113b_fderiv_c1 hf).differentiable one_ne_zero
  have h3 : fderiv ℝ (fun y => f (x - y)) = fun y => -(fderiv ℝ f (x - y)) := funext (s113b_fd_refl h1 x)
  unfold s113b_lap
  rw [h3, fderiv_fun_neg, s113b_fd_refl h2 x y]
  simp

lemma s113b_sc_far (m : s113b_Moll n) {δ : ℝ} (hδ : 0 < δ) {z : s113b_E n} (hz : δ < ‖z‖) :
    z ∉ tsupport (m.scaled δ) := fun h => by
  have := s113b_scaled_tsupport m hδ h
  rw [mem_closedBall_zero_iff] at this
  exact absurd this (not_le.2 hz)

lemma s113b_gdel_far (m : s113b_Moll n) {δ : ℝ} (hδ : 0 < δ) (ν : ℝ) (b : s113b_E n → s113b_E n)
    {K : Set (s113b_E n)} {v : s113b_E n → ℝ} (hv : ∀ y, y ∉ K → v y = 0) {x : s113b_E n}
    (h : ∀ y ∈ K, δ < dist x y) : s113b_gdel m δ ν b v x = 0 := by
  have : ∀ y, v y * (ν * s113b_lap (m.scaled δ) (x - y) - fderiv ℝ (m.scaled δ) (x - y) (b y)) = 0 := by
    intro y
    by_cases hy : y ∈ K
    · have hf := s113b_sc_far m hδ (z := x - y) (by rw [← dist_eq_norm]; exact h y hy)
      have h1 : fderiv ℝ (m.scaled δ) (x - y) = 0 := fderiv_of_notMem_tsupport ℝ hf
      have h2 : fderiv ℝ (fderiv ℝ (m.scaled δ)) (x - y) = 0 :=
        fderiv_of_notMem_tsupport ℝ (fun h' => hf (tsupport_fderiv_subset ℝ h'))
      simp [s113b_lap, h1, h2]
    · rw [hv y hy, zero_mul]
  simp [s113b_gdel, this]

lemma s113b_stepA (hD : s113b_Data ν b q T u K G B) (m : s113b_Moll n) {δ : ℝ} (hδ : 0 < δ)
    (hδG : Metric.cthickening (2 * δ) K ⊆ G) (x : s113b_E n) {a c : ℝ} (ha : 0 ≤ a) (hac : a ≤ c)
    (hcT : c ≤ T) :
    s113b_mol m δ (u c) x - s113b_mol m δ (u a) x ≤ ∫ τ in a..c, s113b_gdel m δ ν b (u τ) x := by
  by_cases hnear : ∃ y ∈ K, dist x y ≤ δ
  · obtain ⟨y0, hy0, hy0d⟩ := hnear
    have hφ : s113b_Cinf (fun y => m.scaled δ (x - y)) :=
      (s113b_scaled_cinf m δ).comp (contDiff_const.sub contDiff_id)
    have hsub : Function.support (fun y => m.scaled δ (x - y)) ⊆ Metric.closedBall x δ := by
      intro y hy
      by_contra hn
      refine hy (image_eq_zero_of_notMem_tsupport (s113b_sc_far m hδ ?_))
      rw [← dist_eq_norm, dist_comm]; exact not_le.1 hn
    have hcs : HasCompactSupport (fun y => m.scaled δ (x - y)) :=
      HasCompactSupport.intro (isCompact_closedBall x δ) fun y hy => by
        by_contra h; exact hy (hsub h)
    have hball : Metric.closedBall x δ ⊆ G := fun y hy => hδG
      (Metric.mem_cthickening_of_dist_le y y0 (2 * δ) K hy0 (by
        have h1 : dist y x ≤ δ := hy
        have := dist_triangle y x y0
        rw [dist_comm x y0] at *; linarith))
    have hts : tsupport (fun y => m.scaled δ (x - y)) ⊆ G :=
      (closure_minimal hsub Metric.isClosed_closedBall).trans hball
    have key := hD.sub _ hφ hcs (fun y => s113b_scaled_nonneg m hδ _) hts a c ha hac hcT
    have hin : ∀ τ, ∫ y, (ν * s113b_lap (fun y => m.scaled δ (x - y)) y +
        fderiv ℝ (fun y => m.scaled δ (x - y)) y (b y)) * u τ y = s113b_gdel m δ ν b (u τ) x := by
      intro τ
      unfold s113b_gdel
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      dsimp only
      rw [s113b_lap_refl (s113b_scaled_cinf m δ), s113b_fd_refl ((s113b_scaled_cinf m δ).differentiable (by simp))]
      simp only [ContinuousLinearMap.neg_apply]; ring
    simp only [hin] at key
    unfold s113b_mol
    linarith
  · push_neg at hnear
    have hmz : ∀ τ ∈ Icc 0 T, s113b_mol m δ (u τ) x = 0 := fun τ hτ => by
      obtain ⟨hm, hB, hK, hu0⟩ := s113b_hyp hD hτ
      exact s113b_mol_eq_zero hm hB hK hu0 m hδ hnear
    rw [hmz c ⟨ha.trans hac, hcT⟩, hmz a ⟨ha, hac.trans hcT⟩]
    simp [s113b_gdel_far m hδ ν b (hD.hKu _) hnear]

/-- `∂_τ F_ε(τ,x,w)` in terms of the ratio `z = w / q`. -/
def s113b_F1 (q : ℝ → s113b_E n → ℝ) (p : ℝ → ℝ) (ε τ : ℝ) (x : s113b_E n) (z : ℝ) : ℝ :=
  -deriv (fun σ => q σ x) τ * s113b_Theta (p τ) ε z + deriv p τ * q τ x * s113b_PhiP (p τ) ε z

/-- The integrand of `s113b_rhsE`. -/
def s113b_A (ν : ℝ) (b : s113b_E n → s113b_E n) (q : ℝ → s113b_E n → ℝ) (p : ℝ → ℝ) (ε τ : ℝ)
    (x : s113b_E n) (z : ℝ) : ℝ :=
  q τ x * s113b_R ν b q τ x * s113b_Theta (p τ) ε z + deriv p τ * q τ x * s113b_PhiP (p τ) ε z

lemma s113b_hasDeriv_F {p q : ℝ → ℝ} {p' q' τ w ε : ℝ} (hpd : HasDerivAt p p' τ)
    (hqd : HasDerivAt q q' τ) (hq : 0 < q τ) (hε : 0 < ε) (hw : 0 ≤ w) :
    HasDerivAt (fun σ => q σ * s113b_Phi (p σ) ε (w / q σ))
      (-q' * s113b_Theta (p τ) ε (w / q τ) + p' * q τ * s113b_PhiP (p τ) ε (w / q τ)) τ := by
  have hz : HasDerivAt (fun σ => w / q σ) ((0 * q τ - w * q') / q τ ^ 2) τ :=
    (hasDerivAt_const τ w).div hqd hq.ne'
  have hzp : 0 < w / q τ + ε := by positivity
  have h1 := (hz.add_const ε).rpow hpd hzp
  have h2 := HasDerivAt.const_rpow hε hpd
  have h3 := HasDerivAt.const_rpow hε (hpd.sub_const 1)
  have h5 := hqd.mul ((h1.sub h2).sub ((hpd.mul h3).mul hz))
  refine h5.congr_deriv ?_
  simp only [Pi.mul_apply, Pi.sub_apply]
  unfold s113b_Theta s113b_Phi s113b_Phi1 s113b_PhiP
  field_simp
  ring

lemma s113b_hasDeriv_w {p q ε w : ℝ} (hp : 1 < p) (hq : 0 < q) (hε : 0 < ε) (hw : 0 ≤ w) :
    HasDerivAt (fun w' => q * s113b_Phi p ε (w' / q)) (s113b_Phi1 p ε (w / q)) w := by
  have h1 : HasDerivAt (fun w' => w' / q) (1 / q) w := (hasDerivAt_id w).div_const q
  have hw' : -ε < w / q := by have : 0 ≤ w / q := by positivity
                              linarith
  have h2 := (s113b_hasDerivAt_Phi hp hε hw').comp w h1
  refine (h2.const_mul q).congr_deriv ?_
  field_simp

lemma s113b_pdx {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {F : ℝ × s113b_E n → V} {k : ℕ}
    (hF : ContDiff ℝ (k + 1) F) :
    ContDiff ℝ k (fun z : ℝ × s113b_E n => fderiv ℝ (fun y => F (z.1, y)) z.2) :=
  ContDiff.fderiv (f := fun (z : ℝ × s113b_E n) (y : s113b_E n) => F (z.1, y)) (g := Prod.snd)
    (hF.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)) contDiff_snd le_rfl

lemma s113b_pdt {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {F : ℝ × s113b_E n → V} {k : ℕ}
    (hF : ContDiff ℝ (k + 1) F) :
    ContDiff ℝ k (fun z : ℝ × s113b_E n => fderiv ℝ (fun σ => F (σ, z.2)) z.1) :=
  ContDiff.fderiv (f := fun (z : ℝ × s113b_E n) (σ : ℝ) => F (σ, z.2)) (g := Prod.fst)
    (hF.comp (contDiff_snd.prodMk (contDiff_snd.comp contDiff_fst))) contDiff_fst le_rfl

lemma s113b_lapQ_cont {Q : ℝ × s113b_E n → ℝ} (hQ : ContDiff ℝ 2 Q) :
    Continuous (fun z : ℝ × s113b_E n => s113b_lap (fun y => Q (z.1, y)) z.2) := by
  have h1 : ContDiff ℝ 1 (fun z : ℝ × s113b_E n => fderiv ℝ (fun y => Q (z.1, y)) z.2) :=
    s113b_pdx (k := 1) hQ
  have h2 := s113b_pdx (k := 0) (F := fun z : ℝ × s113b_E n => fderiv ℝ (fun y => Q (z.1, y)) z.2)
    (by simpa using h1)
  exact continuous_finsetSum _ fun k _ =>
    (h2.continuous.clm_apply continuous_const).clm_apply continuous_const

lemma s113b_divQ_cont {W : ℝ × s113b_E n → s113b_E n} (hW : ContDiff ℝ 1 W) :
    Continuous (fun z : ℝ × s113b_E n => s113b_div (fun y => W (z.1, y)) z.2) := by
  refine continuous_finsetSum _ fun k _ => ?_
  have hk : ContDiff ℝ 1 (fun z : ℝ × s113b_E n => W z k) :=
    (EuclideanSpace.proj k : s113b_E n →L[ℝ] ℝ).contDiff.comp hW
  exact (s113b_pdx (k := 0) (by simpa using hk)).continuous.clm_apply continuous_const

lemma s113b_dtQ_cont {Q : ℝ × s113b_E n → ℝ} (hQ : ContDiff ℝ 2 Q) :
    Continuous (fun z : ℝ × s113b_E n => deriv (fun σ => Q (σ, z.2)) z.1) := by
  have := (s113b_pdt (k := 0) (F := Q) (by simpa using hQ.of_le (by norm_num))).continuous
  exact this.clm_apply continuous_const

lemma s113b_Lq_cont (hD : s113b_Data ν b q T u K G B) :
    Continuous (fun z : ℝ × s113b_E n => ν * s113b_lap (q z.1) z.2 -
      s113b_div (fun y => q z.1 y • b y) z.2) := by
  refine (continuous_const.mul (s113b_lapQ_cont hD.hq)).sub (s113b_divQ_cont
    (W := fun z => q z.1 z.2 • b z.2) ?_)
  exact (hD.hq.of_le (by norm_num)).smul (hD.hb.of_le (by norm_num) |>.comp contDiff_snd)


/-- The ratio `w / q` and the integrand of the chain inequality. -/
def s113b_Hd (ν : ℝ) (b : s113b_E n → s113b_E n) (q : ℝ → s113b_E n → ℝ) (p : ℝ → ℝ) (ε : ℝ)
    (m : s113b_Moll n) (δ : ℝ) (u : ℝ → s113b_E n → ℝ) (τ : ℝ) (x : s113b_E n) : ℝ :=
  s113b_F1 q p ε τ x (s113b_mol m δ (u τ) x / q τ x) +
    s113b_Phi1 (p τ) ε (s113b_mol m δ (u τ) x / q τ x) * s113b_gdel m δ ν b (u τ) x

lemma s113b_qt_cd (hD : s113b_Data ν b q T u K G B) (x : s113b_E n) :
    ContDiff ℝ 2 (fun σ => q σ x) := hD.hq.comp (contDiff_id.prodMk contDiff_const)

lemma s113b_gbound (hD : s113b_Data ν b q T u K G B) (m : s113b_Moll n) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C, ∀ τ ∈ Icc 0 T, ∀ x, |s113b_gdel m δ ν b (u τ) x| ≤ C := by
  obtain ⟨C, hC⟩ := s113b_gdel_bound m hδ ν hD.hb.continuous hD.hKc
  exact ⟨C * B, fun τ hτ x => hC (u τ) B (s113b_hyp hD hτ).2.1 (s113b_hyp hD hτ).2.2.2 x⟩

section Chain

variable (hD : s113b_Data ν b q T u K G B) (m : s113b_Moll n) {p : ℝ → ℝ} (hp : ContDiff ℝ 1 p)
  (hp1 : ∀ t ∈ Icc 0 T, 1 < p t) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) {s t : ℝ} (hs : 0 ≤ s)
  (hst : s ≤ t) (htT : t ≤ T)

include hD hp hp1 hs hst htT

lemma s113b_contΨ {Ψ : ℝ × ℝ → ℝ} (hΨ : ContinuousOn Ψ (Ioi 0 ×ˢ Ici 0)) :
    ContinuousOn (fun z : ℝ × s113b_E n × ℝ => Ψ (p z.1, z.2.2 / q z.1 z.2.1))
      (Icc s t ×ˢ (univ ×ˢ Icc 0 B)) := by
  have hI : Icc s t ⊆ Icc 0 T := Icc_subset_Icc hs htT
  have hq : Continuous fun z : ℝ × s113b_E n × ℝ => q z.1 z.2.1 :=
    hD.hq.continuous.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  refine hΨ.comp ((hp.continuous.comp continuous_fst).continuousOn.prodMk
    ((continuous_snd.comp continuous_snd).continuousOn.div hq.continuousOn
      fun z hz => (hD.hq0 _ (hI hz.1) _).ne')) ?_
  intro z hz
  exact ⟨zero_lt_one.trans (hp1 _ (hI hz.1)), div_nonneg hz.2.2.1 (hD.hq0 _ (hI hz.1) _).le⟩

lemma s113b_contF1 (hε : 0 < ε) :
    ContinuousOn (fun z : ℝ × s113b_E n × ℝ => s113b_F1 q p ε z.1 z.2.1 (z.2.2 / q z.1 z.2.1))
      (Icc s t ×ˢ (univ ×ˢ Icc 0 B)) := by
  have hq : Continuous fun z : ℝ × s113b_E n × ℝ => q z.1 z.2.1 :=
    hD.hq.continuous.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  have hQt := (s113b_dtQ_cont hD.hq).comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd) :
    Continuous fun z : ℝ × s113b_E n × ℝ => (z.1, z.2.1))
  unfold s113b_F1
  exact (hQt.neg.continuousOn.mul (s113b_contΨ hD hp hp1 hs hst htT
    (Ψ := fun a => s113b_Theta a.1 ε a.2) (s113b_continuousOn_Theta ε hε))).add
    ((((hp.continuous_deriv le_rfl).comp continuous_fst).mul hq).continuousOn.mul
      (s113b_contΨ hD hp hp1 hs hst htT (Ψ := fun a => s113b_PhiP a.1 ε a.2)
        (s113b_continuousOn_PhiP ε hε)))

lemma s113b_contA (hε : 0 < ε) :
    ContinuousOn (fun z : ℝ × s113b_E n × ℝ => s113b_A ν b q p ε z.1 z.2.1 (z.2.2 / q z.1 z.2.1))
      (Icc s t ×ˢ (univ ×ˢ Icc 0 B)) := by
  have hI : Icc s t ⊆ Icc 0 T := Icc_subset_Icc hs htT
  have hpr : Continuous fun z : ℝ × s113b_E n × ℝ => (z.1, z.2.1) :=
    continuous_fst.prodMk (continuous_fst.comp continuous_snd)
  have hq : Continuous fun z : ℝ × s113b_E n × ℝ => q z.1 z.2.1 := hD.hq.continuous.comp hpr
  have hR : ContinuousOn (fun z : ℝ × s113b_E n × ℝ => s113b_R ν b q z.1 z.2.1)
      (Icc s t ×ˢ (univ ×ˢ Icc 0 B)) :=
    (((s113b_Lq_cont hD).comp hpr).sub ((s113b_dtQ_cont hD.hq).comp hpr)).continuousOn.div
      hq.continuousOn fun z hz => (hD.hq0 _ (hI hz.1) _).ne'
  unfold s113b_A
  exact ((hq.continuousOn.mul hR).mul (s113b_contΨ hD hp hp1 hs hst htT
    (Ψ := fun a => s113b_Theta a.1 ε a.2) (s113b_continuousOn_Theta ε hε))).add
    ((((hp.continuous_deriv le_rfl).comp continuous_fst).mul hq).continuousOn.mul
      (s113b_contΨ hD hp hp1 hs hst htT (Ψ := fun a => s113b_PhiP a.1 ε a.2)
        (s113b_continuousOn_PhiP ε hε)))

lemma s113b_stepB (hε : 0 < ε) (hδ : 0 < δ) (hδG : Metric.cthickening (2 * δ) K ⊆ G)
    (x : s113b_E n) :
    s113b_F q p ε t x (s113b_mol m δ (u t) x) - s113b_F q p ε s x (s113b_mol m δ (u s) x) ≤
      ∫ τ in s..t, s113b_Hd ν b q p ε m δ u τ x := by
  have hI : Icc s t ⊆ Icc 0 T := Icc_subset_Icc hs htT
  have hB0 : 0 ≤ B := (hD.hu0 0 0).trans (hD.huB 0 ⟨le_rfl, hs.trans (hst.trans htT)⟩ 0)
  have hqpos : ∀ τ ∈ Icc s t, 0 < q τ x := fun τ hτ => hD.hq0 τ (hI hτ) x
  have hpd : ∀ τ, HasDerivAt p (deriv p τ) τ := fun τ =>
    ((hp.differentiable one_ne_zero) τ).hasDerivAt
  have hqd : ∀ τ, HasDerivAt (fun σ => q σ x) (deriv (fun σ => q σ x) τ) τ := fun τ =>
    (((s113b_qt_cd hD x).differentiable (by norm_num)) τ).hasDerivAt
  obtain ⟨Cg, hCg⟩ := s113b_gbound hD m hδ
  have hmol : ∀ τ ∈ Icc s t, s113b_mol m δ (u τ) x ∈ Icc (0 : ℝ) B := fun τ hτ => by
    obtain ⟨hm, hB, hK, hu0⟩ := s113b_hyp hD (hI hτ)
    exact ⟨s113b_mol_nonneg hm hB hK hu0 m hδ (fun y => hD.hu0 _ _) x,
      s113b_mol_le hm hB hK hu0 m hδ (fun y => hD.huB τ (hI hτ) y) x⟩
  refine s113b_chain_bv (w := fun τ => s113b_mol m δ (u τ) x)
    (g := fun τ => s113b_gdel m δ ν b (u τ) x) (F := fun τ w => s113b_F q p ε τ x w)
    (F1 := fun τ w => s113b_F1 q p ε τ x (w / q τ x))
    (F2 := fun τ w => s113b_Phi1 (p τ) ε (w / q τ x)) hB0 hst hmol ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact s113b_ii (((s113b_gdel_measurable m δ ν hD.hb.continuous hD.hum).comp
      (measurable_id.prodMk measurable_const) :) ) hst (fun τ hτ => hCg τ (hI hτ) x)
  · exact fun a c ha hac hc => s113b_stepA hD m hδ hδG x (hs.trans ha) hac (hc.trans htT)
  · intro w hw τ hτ
    exact (s113b_hasDeriv_F (hpd τ) (hqd τ) (hqpos τ hτ) hε hw.1)
  · intro τ hτ w hw
    exact (s113b_hasDeriv_w (hp1 τ (hI hτ)) (hqpos τ hτ) hε hw.1).hasDerivWithinAt
  · exact (s113b_contF1 hD hp hp1 hs hst htT hε).comp
      (by fun_prop : ContinuousOn (fun z : ℝ × ℝ => (z.1, x, z.2)) _)
      fun z hz => ⟨hz.1, trivial, hz.2⟩
  · exact (s113b_contΨ hD hp hp1 hs hst htT (Ψ := fun a => s113b_Phi1 a.1 ε a.2)
      (s113b_continuousOn_Phi1 ε hε)).comp
      (by fun_prop : ContinuousOn (fun z : ℝ × ℝ => (z.1, x, z.2)) _)
      fun z hz => ⟨hz.1, trivial, hz.2⟩
  · exact fun τ hτ w hw => s113b_Phi1_nonneg (hp1 τ (hI hτ)) hε (div_nonneg hw.1 (hqpos τ hτ).le)
  · intro τ hτ w1 hw1 w2 hw2 h
    exact s113b_Phi1_monotoneOn (hp1 τ (hI hτ)) hε (div_nonneg hw1.1 (hqpos τ hτ).le)
      (div_nonneg hw2.1 (hqpos τ hτ).le) (div_le_div_of_nonneg_right h (hqpos τ hτ).le)

end Chain


lemma s113b_PhiP_zero (p e : ℝ) : s113b_PhiP p e 0 = 0 := by simp [s113b_PhiP]

lemma s113b_mol_zero_out (hD : s113b_Data ν b q T u K G B) (m : s113b_Moll n) {δ : ℝ} (hδ : 0 < δ)
    {τ : ℝ} (hτ : τ ∈ Icc 0 T) {x : s113b_E n} (hx : x ∉ Metric.cthickening δ K) :
    s113b_mol m δ (u τ) x = 0 := by
  obtain ⟨hm, hB, hK, hu0⟩ := s113b_hyp hD hτ
  refine s113b_mol_eq_zero hm hB hK hu0 m hδ fun y hy => ?_
  by_contra h
  exact hx (Metric.mem_cthickening_of_dist_le x y δ K hy (not_lt.1 h))

lemma s113b_div_cont {b : s113b_E n → s113b_E n} (hb : ContDiff ℝ 1 b) : Continuous (s113b_div b) :=
  (s113b_divQ_cont (W := fun z : ℝ × s113b_E n => b z.2) (hb.comp contDiff_snd)).comp
    (continuous_const.prodMk continuous_id : Continuous fun x : s113b_E n => ((0 : ℝ), x))

lemma s113b_kcont (m : s113b_Moll n) (δ : ℝ) {b : s113b_E n → s113b_E n} (hb : ContDiff ℝ 1 b) :
    Continuous fun z : s113b_E n × s113b_E n => fderiv ℝ (m.scaled δ) (z.1 - z.2) (b z.1 - b z.2) +
      s113b_div b z.1 * m.scaled δ (z.1 - z.2) := by
  have hsub : Continuous fun z : s113b_E n × s113b_E n => z.1 - z.2 := continuous_fst.sub continuous_snd
  exact (((s113b_scaled_c1 m δ).continuous_fderiv one_ne_zero).comp hsub).clm_apply
    ((hb.continuous.comp continuous_fst).sub (hb.continuous.comp continuous_snd)) |>.add
    (((s113b_div_cont hb).comp continuous_fst).mul ((s113b_scaled_cinf m δ).continuous.comp hsub))

lemma s113b_comm_meas (m : s113b_Moll n) (δ : ℝ) {b : s113b_E n → s113b_E n} (hb : ContDiff ℝ 1 b)
    {U : ℝ × s113b_E n → ℝ} (hU : Measurable U) :
    Measurable fun z : ℝ × s113b_E n => s113b_comm m δ b (fun y => U (z.1, y)) z.2 := by
  have hH := (s113b_kcont m δ hb).comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd :
    Continuous fun p : (ℝ × s113b_E n) × s113b_E n => (p.1.2, p.2))
  have hG : Measurable fun p : (ℝ × s113b_E n) × s113b_E n => U (p.1.1, p.2) *
      (fderiv ℝ (m.scaled δ) (p.1.2 - p.2) (b p.1.2 - b p.2) + s113b_div b p.1.2 * m.scaled δ (p.1.2 - p.2)) :=
    (hU.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul hH.measurable
  exact (hG.stronglyMeasurable.integral_prod_right').measurable

lemma s113b_commB6_bound (hD : s113b_Data ν b q T u K G B) (m : s113b_Moll n) {δ : ℝ} :
    ∃ C, ∀ τ ∈ Icc 0 T, ∀ x ∈ Metric.cthickening δ K, |s113b_comm m δ b (u τ) x| ≤ C := by
  obtain ⟨Ck, hCk⟩ := (hD.hKc.cthickening.prod hD.hKc).exists_bound_of_continuousOn
    (s113b_kcont m δ (hD.hb.of_le one_le_two)).continuousOn
  refine ⟨volume.real K * (B * Ck), fun τ hτ x hx => ?_⟩
  obtain ⟨hm, hB, hK, hu0⟩ := s113b_hyp hD hτ
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hH : ∀ y ∈ K, ‖u τ y * (fderiv ℝ (m.scaled δ) (x - y) (b x - b y) +
      s113b_div b x * m.scaled δ (x - y))‖ ≤ B * Ck := fun y hy => by
    rw [norm_mul]
    exact mul_le_mul (by simpa using hB y) (hCk (x, y) ⟨hx, hy⟩) (norm_nonneg _) hB0
  have hz : ∀ y, y ∉ K → u τ y * (fderiv ℝ (m.scaled δ) (x - y) (b x - b y) +
      s113b_div b x * m.scaled δ (x - y)) = 0 := fun y hy => by rw [hu0 y hy, zero_mul]
  unfold s113b_comm
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz, ← Real.norm_eq_abs]
  exact (norm_setIntegral_le_of_norm_le_const hK.measure_lt_top hH).trans (le_of_eq (by ring))

lemma s113b_intF (hD : s113b_Data ν b q T u K G B) (m : s113b_Moll n) {p : ℝ → ℝ}
    (hp1 : ∀ t ∈ Icc 0 T, 1 < p t) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) {τ : ℝ} (hτ : τ ∈ Icc 0 T) :
    Integrable (fun x => s113b_F q p ε τ x (s113b_mol m δ (u τ) x)) := by
  obtain ⟨hm, hB, hK, hu0⟩ := s113b_hyp hD hτ
  have hv : Continuous (s113b_mol m δ (u τ)) := (s113b_mol_cinf hm hB hK hu0 m hδ).continuous
  have hq : Continuous (q τ) := hD.hq.continuous.comp (continuous_const.prodMk continuous_id)
  refine Continuous.integrable_of_hasCompactSupport ?_
    (HasCompactSupport.intro (hD.hKc.cthickening (r := δ)) fun x hx => ?_)
  · unfold s113b_F
    exact hq.mul ((s113b_continuousOn_Phi ε hε).comp_continuous
      (continuous_const.prodMk (hv.div hq fun x => (hD.hq0 τ hτ x).ne')) fun x =>
      ⟨zero_lt_one.trans (hp1 τ hτ), div_nonneg (s113b_mol_nonneg hm hB hK hu0 m hδ
        (fun y => hD.hu0 _ _) x) (hD.hq0 τ hτ x).le⟩)
  · simp [s113b_F, s113b_mol_zero_out hD m hδ hτ hx, s113b_Phi_zero]

/-- The ratio `u_δ / q`, and the two pieces of the right-hand side integrand. -/
def s113b_Zf (q : ℝ → s113b_E n → ℝ) (m : s113b_Moll n) (δ : ℝ) (u : ℝ → s113b_E n → ℝ) (τ : ℝ)
    (x : s113b_E n) : ℝ := s113b_mol m δ (u τ) x / q τ x

def s113b_Cz (q : ℝ → s113b_E n → ℝ) (b : s113b_E n → s113b_E n) (p : ℝ → ℝ) (ε : ℝ)
    (m : s113b_Moll n) (δ : ℝ) (u : ℝ → s113b_E n → ℝ) (τ : ℝ) (x : s113b_E n) : ℝ :=
  s113b_Phi1 (p τ) ε (s113b_Zf q m δ u τ x) * s113b_comm m δ b (u τ) x

section Chain2

variable (hD : s113b_Data ν b q T u K G B) (m : s113b_Moll n) {p : ℝ → ℝ} (hp : ContDiff ℝ 1 p)
  (hp1 : ∀ t ∈ Icc 0 T, 1 < p t) {ε δ : ℝ} {s t : ℝ} (hs : 0 ≤ s)
  (hst : s ≤ t) (htT : t ≤ T)

include hD hp hp1 hs hst htT

lemma s113b_hmol (hδ : 0 < δ) {τ : ℝ} (hτ : τ ∈ Icc s t) (x : s113b_E n) :
    s113b_mol m δ (u τ) x ∈ Icc (0 : ℝ) B := by
  have hτ' : τ ∈ Icc 0 T := Icc_subset_Icc hs htT hτ
  obtain ⟨hm, hB, hK, hu0⟩ := s113b_hyp hD hτ'
  exact ⟨s113b_mol_nonneg hm hB hK hu0 m hδ (fun y => hD.hu0 _ _) x,
    s113b_mol_le hm hB hK hu0 m hδ (fun y => hD.huB τ hτ' y) x⟩

lemma s113b_bd {f : ℝ × s113b_E n × ℝ → ℝ} (hf : ContinuousOn f (Icc s t ×ˢ (univ ×ˢ Icc 0 B)))
    (δ : ℝ) : ∃ M, ∀ τ ∈ Icc s t, ∀ x ∈ Metric.cthickening δ K, ∀ w ∈ Icc (0 : ℝ) B, |f (τ, x, w)| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod (hD.hKc.cthickening.prod isCompact_Icc)).exists_bound_of_continuousOn
    (hf.mono (prod_mono subset_rfl (prod_mono (subset_univ _) subset_rfl)))
  exact ⟨M, fun τ hτ x hx w hw => by simpa using hM (τ, x, w) ⟨hτ, hx, hw⟩⟩

lemma s113b_meas (hε : 0 < ε) :
    Measurable (fun z : ℝ × s113b_E n => s113b_Hd ν b q p ε m δ u z.1 z.2) ∧
    Measurable (fun z : ℝ × s113b_E n => s113b_A ν b q p ε z.1 z.2 (s113b_Zf q m δ u z.1 z.2)) ∧
    Measurable (fun z : ℝ × s113b_E n => s113b_Cz q b p ε m δ u z.1 z.2) := by
  have hq := hD.hq.continuous
  have hZ : Measurable fun z : ℝ × s113b_E n => s113b_Zf q m δ u z.1 z.2 :=
    (s113b_mol_measurable m δ hD.hum).div hq.measurable
  have hpm : Measurable fun z : ℝ × s113b_E n => p z.1 := hp.continuous.measurable.comp measurable_fst
  have hdp : Measurable fun z : ℝ × s113b_E n => deriv p z.1 :=
    (hp.continuous_deriv le_rfl).measurable.comp measurable_fst
  have hQt : Measurable fun z : ℝ × s113b_E n => deriv (fun σ => q σ z.2) z.1 :=
    (s113b_dtQ_cont hD.hq).measurable
  have hΘ : Measurable fun a : ℝ × ℝ => s113b_Theta a.1 ε a.2 := by
    unfold s113b_Theta s113b_Phi1 s113b_Phi; fun_prop
  have hPP : Measurable fun a : ℝ × ℝ => s113b_PhiP a.1 ε a.2 := by unfold s113b_PhiP; fun_prop
  have hP1 : Measurable fun a : ℝ × ℝ => s113b_Phi1 a.1 ε a.2 := by unfold s113b_Phi1; fun_prop
  have hΘz := hΘ.comp (hpm.prodMk hZ)
  have hPPz := hPP.comp (hpm.prodMk hZ)
  have hP1z := hP1.comp (hpm.prodMk hZ)
  have hg := s113b_gdel_measurable m δ ν hD.hb.continuous hD.hum
  have hF1 : Measurable fun z : ℝ × s113b_E n => s113b_F1 q p ε z.1 z.2 (s113b_Zf q m δ u z.1 z.2) := by
    unfold s113b_F1; exact (hQt.neg.mul hΘz).add ((hdp.mul hq.measurable).mul hPPz)
  refine ⟨hF1.add (hP1z.mul hg), ?_, hP1z.mul (s113b_comm_meas m δ (hD.hb.of_le one_le_two) hD.hum)⟩
  have hR : Measurable fun z : ℝ × s113b_E n => s113b_R ν b q z.1 z.2 :=
    (((s113b_Lq_cont hD).sub (s113b_dtQ_cont hD.hq)).measurable).div hq.measurable
  unfold s113b_A
  exact ((hq.measurable.mul hR).mul hΘz).add ((hdp.mul hq.measurable).mul hPPz)

end Chain2


lemma s113b_pack {f : ℝ × s113b_E n → ℝ} (hf : Measurable f) {s t M : ℝ} {S : Set (s113b_E n)}
    (hS : IsCompact S) (hb : ∀ τ ∈ Icc s t, ∀ x ∈ S, |f (τ, x)| ≤ M) :
    Integrable f ((volume.restrict (Ioc s t)).prod (volume.restrict S)) ∧
      ∀ τ ∈ Icc s t, IntegrableOn (fun x => f (τ, x)) S :=
  ⟨s113b_iprod hf measurableSet_Ioc (by simp) hS fun z hz => hb z.1 (Ioc_subset_Icc_self hz.1) z.2 hz.2,
   fun τ hτ => Measure.integrableOn_of_bounded (M := M) hS.measure_lt_top.ne
     (hf.comp measurable_prodMk_left).aestronglyMeasurable
     (ae_restrict_of_forall_mem hS.measurableSet fun x hx => by rw [Real.norm_eq_abs]; exact hb τ hτ x hx)⟩

section Chain3

variable (hD : s113b_Data ν b q T u K G B) (m : s113b_Moll n) {p : ℝ → ℝ} (hp : ContDiff ℝ 1 p)
  (hp1 : ∀ t ∈ Icc 0 T, 1 < p t) {ε δ : ℝ} {s t : ℝ} (hs : 0 ≤ s)
  (hst : s ≤ t) (htT : t ≤ T)

include hD hp hp1 hs hst htT

lemma s113b_packs (hε : 0 < ε) (hδ : 0 < δ) :
    Integrable (fun z : ℝ × s113b_E n => s113b_Hd ν b q p ε m δ u z.1 z.2)
      ((volume.restrict (Ioc s t)).prod (volume.restrict (Metric.cthickening δ K))) ∧
    Integrable (fun z : ℝ × s113b_E n => s113b_A ν b q p ε z.1 z.2 (s113b_Zf q m δ u z.1 z.2) +
      s113b_Cz q b p ε m δ u z.1 z.2)
      ((volume.restrict (Ioc s t)).prod (volume.restrict (Metric.cthickening δ K))) ∧
    ∀ τ ∈ Icc s t, IntegrableOn (fun x => s113b_Hd ν b q p ε m δ u τ x) (Metric.cthickening δ K) ∧
      IntegrableOn (fun x => s113b_A ν b q p ε τ x (s113b_Zf q m δ u τ x)) (Metric.cthickening δ K) ∧
      IntegrableOn (fun x => s113b_Cz q b p ε m δ u τ x) (Metric.cthickening δ K) := by
  obtain ⟨hmH, hmA, hmC⟩ := s113b_meas hD m hp hp1 hs hst htT (δ := δ) hε
  obtain ⟨M1, h1⟩ := s113b_bd hD hp hp1 hs hst htT (s113b_contF1 hD hp hp1 hs hst htT hε) δ
  obtain ⟨M2, h2⟩ := s113b_bd hD hp hp1 hs hst htT (f := fun z => s113b_Phi1 (p z.1) ε (z.2.2 / q z.1 z.2.1))
    (s113b_contΨ hD hp hp1 hs hst htT (Ψ := fun a => s113b_Phi1 a.1 ε a.2) (s113b_continuousOn_Phi1 ε hε)) δ
  obtain ⟨M3, h3⟩ := s113b_bd hD hp hp1 hs hst htT (s113b_contA hD hp hp1 hs hst htT hε) δ
  obtain ⟨Cg, hCg⟩ := s113b_gbound hD m hδ
  obtain ⟨Cc, hCc⟩ := s113b_commB6_bound hD m (δ := δ)
  have hI := Icc_subset_Icc hs htT
  have hS := hD.hKc.cthickening (r := δ)
  have a2 : ∀ τ ∈ Icc s t, ∀ x ∈ Metric.cthickening δ K, |s113b_Phi1 (p τ) ε (s113b_Zf q m δ u τ x)| ≤ M2 :=
    fun τ hτ x hx => h2 τ hτ x hx _ (s113b_hmol hD m hp hp1 hs hst htT hδ hτ x)
  obtain ⟨hH1, hH2⟩ := s113b_pack hmH hS (M := M1 + M2 * Cg) fun τ hτ x hx => by
    unfold s113b_Hd
    refine (abs_add_le _ _).trans (add_le_add (h1 τ hτ x hx _ (s113b_hmol hD m hp hp1 hs hst htT hδ hτ x)) ?_)
    rw [abs_mul]
    exact mul_le_mul (a2 τ hτ x hx) (hCg τ (hI hτ) x) (abs_nonneg _) ((abs_nonneg _).trans (a2 τ hτ x hx))
  obtain ⟨hA1, hA2⟩ := s113b_pack hmA hS (M := M3) fun τ hτ x hx =>
    h3 τ hτ x hx _ (s113b_hmol hD m hp hp1 hs hst htT hδ hτ x)
  obtain ⟨hC1, hC2⟩ := s113b_pack hmC hS (M := M2 * Cc) fun τ hτ x hx => by
    unfold s113b_Cz
    rw [abs_mul]
    exact mul_le_mul (a2 τ hτ x hx) (hCc τ (hI hτ) x hx) (abs_nonneg _) ((abs_nonneg _).trans (a2 τ hτ x hx))
  exact ⟨hH1, hA1.add hC1, fun τ hτ => ⟨hH2 τ hτ, hA2 τ hτ, hC2 τ hτ⟩⟩

lemma s113b_stepD (hε : 0 < ε) (hδ : 0 < δ) {τ : ℝ} (hτ : τ ∈ Icc s t) :
    ∫ x in Metric.cthickening δ K, s113b_Hd ν b q p ε m δ u τ x ≤
      ∫ x in Metric.cthickening δ K, (s113b_A ν b q p ε τ x (s113b_Zf q m δ u τ x) +
        s113b_Cz q b p ε m δ u τ x) := by
  obtain ⟨-, -, hsl⟩ := s113b_packs hD m hp hp1 hs hst htT hε hδ
  obtain ⟨hH, hA, hC⟩ := hsl τ hτ
  have hτ' : τ ∈ Icc 0 T := Icc_subset_Icc hs htT hτ
  obtain ⟨hm, hB, hK, hu0⟩ := s113b_hyp hD hτ'
  have hv := s113b_mol_cinf hm hB hK hu0 m hδ
  have hq2 : ContDiff ℝ 2 (q τ) := hD.hq.comp (contDiff_const.prodMk contDiff_id)
  have hqp : ∀ x, 0 < q τ x := hD.hq0 τ hτ'
  have hpτ := hp1 τ hτ'
  have hr : ContDiff ℝ 2 (fun x => s113b_mol m δ (u τ) x / q τ x) :=
    (hv.of_le (WithTop.coe_le_coe.2 le_top)).div hq2 fun x => (hqp x).ne'
  have hrc : HasCompactSupport (fun x => s113b_mol m δ (u τ) x / q τ x) :=
    HasCompactSupport.intro (hD.hKc.cthickening (r := δ)) fun x hx => by
      simp [s113b_mol_zero_out hD m hδ hτ' hx]
  have hk := s113b_kato hD.hν (hD.hb.of_le one_le_two) hq2 hqp hr hrc
    (fun x => div_nonneg (s113b_mol_nonneg hm hB hK hu0 m hδ (fun y => hD.hu0 _ _) x) (hqp x).le)
    (Φ := s113b_Phi (p τ) ε) (Φ1 := s113b_Phi1 (p τ) ε) (Φ2 := s113b_Phi2 (p τ) ε)
    (fun z hz => s113b_hasDerivAt_Phi hpτ hε (by linarith))
    (fun z hz => s113b_hasDerivAt_Phi1 hpτ hε (by linarith))
    ((s113b_continuousOn_Phi2 ε hε).comp (continuous_const.prodMk continuous_id).continuousOn
      (fun z hz => ⟨zero_lt_one.trans hpτ, hz⟩))
    (fun z hz => s113b_Phi2_nonneg hpτ hε (by linarith)) (s113b_Phi_zero _ _) (s113b_Phi1_zero _ _)
  have e : ∀ y, q τ y * (s113b_mol m δ (u τ) y / q τ y) = s113b_mol m δ (u τ) y :=
    fun y => mul_div_cancel₀ _ (hqp y).ne'
  simp only [e] at hk
  have hk' : ∫ x, (s113b_Hd ν b q p ε m δ u τ x - (s113b_A ν b q p ε τ x (s113b_Zf q m δ u τ x) +
      s113b_Cz q b p ε m δ u τ x)) ≤ 0 := by
    refine le_trans (le_of_eq (integral_congr_ae (ae_of_all _ fun x => ?_))) hk
    have hg := s113b_gdel_eq hm hB hK hu0 m hδ ν (hD.hb.of_le one_le_two) x
    have hqR : q τ x * s113b_R ν b q τ x = ν * s113b_lap (q τ) x -
        s113b_div (fun y => q τ y • b y) x - deriv (fun σ => q σ x) τ := by
      unfold s113b_R; field_simp [(hqp x).ne']
    beta_reduce
    unfold s113b_Hd s113b_F1 s113b_A s113b_Cz s113b_Zf s113b_Theta
    rw [hg, hqR]
    ring
  have h0 : ∀ x ∉ Metric.cthickening δ K, s113b_Hd ν b q p ε m δ u τ x - (s113b_A ν b q p ε τ x
      (s113b_Zf q m δ u τ x) + s113b_Cz q b p ε m δ u τ x) = 0 := fun x hx => by
    simp [s113b_Hd, s113b_F1, s113b_A, s113b_Cz, s113b_Zf, s113b_mol_zero_out hD m hδ hτ' hx,
      s113b_Theta_zero, s113b_PhiP_zero, s113b_Phi1_zero]
  have := setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) h0
  have h2 := integral_add (μ := volume.restrict (Metric.cthickening δ K))
    (f := fun x => s113b_A ν b q p ε τ x (s113b_Zf q m δ u τ x) + s113b_Cz q b p ε m δ u τ x)
    (g := fun x => s113b_Hd ν b q p ε m δ u τ x - (s113b_A ν b q p ε τ x (s113b_Zf q m δ u τ x) +
      s113b_Cz q b p ε m δ u τ x)) (hA.add hC) (hH.sub (hA.add hC))
  beta_reduce at h2
  simp only [add_sub_cancel] at h2
  linarith

end Chain3


theorem s113b_mollified_chain {n : ℕ} {ν : ℝ} {b : s113b_E n → s113b_E n} {q : ℝ → s113b_E n → ℝ} {T : ℝ}
    {u : ℝ → s113b_E n → ℝ} {K G : Set (s113b_E n)} {B : ℝ} (hD : s113b_Data ν b q T u K G B)
    (m : s113b_Moll n) {p : ℝ → ℝ} (hp : ContDiff ℝ 1 p) (hp1 : ∀ t ∈ Icc 0 T, 1 < p t)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδG : Metric.cthickening (2 * δ) K ⊆ G)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) :
    (∫ x, s113b_F q p ε t x (s113b_mol m δ (u t) x)) - ∫ x, s113b_F q p ε s x (s113b_mol m δ (u s) x) ≤
      ∫ τ in s..t, (s113b_rhsE ν b q p ε τ (fun x => s113b_mol m δ (u τ) x / q τ x) +
        ∫ x, s113b_Phi1 (p τ) ε (s113b_mol m δ (u τ) x / q τ x) * s113b_comm m δ b (u τ) x) := by
  have hI : Icc s t ⊆ Icc 0 T := Icc_subset_Icc hs htT
  have hSc : IsCompact (Metric.cthickening δ K) := hD.hKc.cthickening
  obtain ⟨hHp, hACp, hsl⟩ := s113b_packs hD m hp hp1 hs hst htT hε hδ
  have ht0 : t ∈ Icc 0 T := ⟨hs.trans hst, htT⟩
  have hs0 : s ∈ Icc 0 T := ⟨hs, hst.trans htT⟩
  have hFz : ∀ τ ∈ Icc 0 T, ∀ x ∉ Metric.cthickening δ K,
      s113b_F q p ε τ x (s113b_mol m δ (u τ) x) = 0 := fun τ hτ x hx => by
    simp [s113b_F, s113b_mol_zero_out hD m hδ hτ hx, s113b_Phi_zero]
  have hii : ∀ {f : ℝ → ℝ}, Integrable f (volume.restrict (Ioc s t)) → IntervalIntegrable f volume s t :=
    fun h => (intervalIntegrable_iff_integrableOn_Ioc_of_le hst).2 h
  calc (∫ x, s113b_F q p ε t x (s113b_mol m δ (u t) x)) - ∫ x, s113b_F q p ε s x (s113b_mol m δ (u s) x)
      = ∫ x, (s113b_F q p ε t x (s113b_mol m δ (u t) x) - s113b_F q p ε s x (s113b_mol m δ (u s) x)) :=
        (integral_sub (s113b_intF hD m hp1 hε hδ ht0) (s113b_intF hD m hp1 hε hδ hs0)).symm
    _ = ∫ x in Metric.cthickening δ K, (s113b_F q p ε t x (s113b_mol m δ (u t) x) -
          s113b_F q p ε s x (s113b_mol m δ (u s) x)) :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
          rw [hFz t ht0 x hx, hFz s hs0 x hx, sub_zero]).symm
    _ ≤ ∫ x in Metric.cthickening δ K, ∫ τ in Ioc s t, s113b_Hd ν b q p ε m δ u τ x :=
        setIntegral_mono_on ((s113b_intF hD m hp1 hε hδ ht0).sub (s113b_intF hD m hp1 hε hδ hs0)).integrableOn
          hHp.integral_prod_right hSc.measurableSet fun x _ => by
          have := s113b_stepB hD m hp hp1 hs hst htT hε hδ hδG x
          rwa [intervalIntegral.integral_of_le hst] at this
    _ = ∫ τ in Ioc s t, ∫ x in Metric.cthickening δ K, s113b_Hd ν b q p ε m δ u τ x :=
        (integral_integral_swap (f := fun τ x => s113b_Hd ν b q p ε m δ u τ x) hHp).symm
    _ = ∫ τ in s..t, ∫ x in Metric.cthickening δ K, s113b_Hd ν b q p ε m δ u τ x :=
        (intervalIntegral.integral_of_le hst).symm
    _ ≤ ∫ τ in s..t, ∫ x in Metric.cthickening δ K, (s113b_A ν b q p ε τ x (s113b_Zf q m δ u τ x) +
          s113b_Cz q b p ε m δ u τ x) :=
        intervalIntegral.integral_mono_on hst (hii hHp.integral_prod_left) (hii hACp.integral_prod_left)
          fun τ hτ => s113b_stepD hD m hp hp1 hs hst htT hε hδ hτ
    _ = _ := by
        refine intervalIntegral.integral_congr fun τ hτ => ?_
        rw [uIcc_of_le hst] at hτ
        obtain ⟨-, hA, hC⟩ := hsl τ hτ
        have zA : ∀ x ∉ Metric.cthickening δ K, s113b_A ν b q p ε τ x (s113b_Zf q m δ u τ x) = 0 :=
          fun x hx => by simp [s113b_A, s113b_Zf, s113b_mol_zero_out hD m hδ (hI hτ) hx,
            s113b_Theta_zero, s113b_PhiP_zero]
        have zC : ∀ x ∉ Metric.cthickening δ K, s113b_Cz q b p ε m δ u τ x = 0 :=
          fun x hx => by simp [s113b_Cz, s113b_Zf, s113b_mol_zero_out hD m hδ (hI hτ) hx, s113b_Phi1_zero]
        show _ = (∫ x, s113b_A ν b q p ε τ x (s113b_Zf q m δ u τ x)) + ∫ x, s113b_Cz q b p ε m δ u τ x
        rw [integral_add hA hC, setIntegral_eq_integral_of_forall_compl_eq_zero zA,
          setIntegral_eq_integral_of_forall_compl_eq_zero zC]

end HRS.MS.S113X2B

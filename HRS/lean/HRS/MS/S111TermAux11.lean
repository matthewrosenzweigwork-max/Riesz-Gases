import HRS.MS.S111TermAux10

/-!
# S11.1 terminal wave, B06: expectation of a bilinear product transports `L²` interval domination to BV domination
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace HRS.MS.S111T

section Bil

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Hölder `(2,2,1)` for a bounded bilinear map. -/
theorem s111t_bil_holder (B : E →L[ℝ] F →L[ℝ] G) {x : Ω → E} {V : Ω → F}
    (hx : MemLp x 2 P) (hV : MemLp V 2 P) :
    eLpNorm (fun w => B (x w) (V w)) 1 P ≤ (‖B‖₊ : ℝ≥0∞) * eLpNorm x 2 P * eLpNorm V 2 P := by
  refine eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm (p := 2) (q := 2) (r := 1) (fun a b => B a b) ‖B‖₊
    B.continuous₂ hx.aestronglyMeasurable hV.aestronglyMeasurable (ae_of_all _ fun w => ?_)
  have := B.le_opNorm₂ (x w) (V w)
  simpa [mul_assoc] using this

theorem s111t_bil_integrable (B : E →L[ℝ] F →L[ℝ] G) {x : Ω → E} {V : Ω → F}
    (hx : MemLp x 2 P) (hV : MemLp V 2 P) : Integrable (fun w => B (x w) (V w)) P := by
  have hm : AEStronglyMeasurable (fun w => B (x w) (V w)) P :=
    B.continuous₂.comp_aestronglyMeasurable₂ hx.aestronglyMeasurable hV.aestronglyMeasurable
  have hlt : eLpNorm (fun w => B (x w) (V w)) 1 P < ∞ :=
    lt_of_le_of_lt (s111t_bil_holder B hx hV)
      (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top hx) hV)
  have hmem : MemLp (fun w => B (x w) (V w)) 1 P := hlt
  exact memLp_one_iff_integrable.1 hmem

/-- `‖∫ B(x,V)‖ ≤ ‖B‖ a c` when `‖x‖₂ ≤ a`, `‖V‖₂ ≤ c`. -/
theorem s111t_bil_integral_le [CompleteSpace G] (B : E →L[ℝ] F →L[ℝ] G) {x : Ω → E} {V : Ω → F}
    (hx : MemLp x 2 P) (hV : MemLp V 2 P) {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hxa : eLpNorm x 2 P ≤ ENNReal.ofReal a) (hVc : eLpNorm V 2 P ≤ ENNReal.ofReal c) :
    ‖∫ w, B (x w) (V w) ∂P‖ ≤ ‖B‖ * a * c := by
  have hint := s111t_bil_integrable B hx hV
  have h1 : ‖∫ w, B (x w) (V w) ∂P‖ ≤ ∫ w, ‖B (x w) (V w)‖ ∂P := norm_integral_le_integral_norm _
  have h2 : ∫ w, ‖B (x w) (V w)‖ ∂P = (eLpNorm (fun w => B (x w) (V w)) 1 P).toReal := by
    rw [eLpNorm_one_eq_lintegral_enorm, integral_norm_eq_lintegral_enorm hint.aestronglyMeasurable]
    all_goals exact hint.aestronglyMeasurable
  have h3 : eLpNorm (fun w => B (x w) (V w)) 1 P ≤ ENNReal.ofReal (‖B‖ * a * c) := by
    refine (s111t_bil_holder B hx hV).trans ?_
    calc (‖B‖₊ : ℝ≥0∞) * eLpNorm x 2 P * eLpNorm V 2 P
        ≤ (‖B‖₊ : ℝ≥0∞) * ENNReal.ofReal a * ENNReal.ofReal c := by gcongr
      _ = ENNReal.ofReal (‖B‖ * a * c) := by
        have hB : (‖B‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖B‖ := by
          exact (ofReal_norm B).symm
        rw [hB, ← ENNReal.ofReal_mul (norm_nonneg B), ← ENNReal.ofReal_mul (by positivity)]
  rw [h2] at h1
  refine h1.trans ?_
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) h3

end Bil

section BV

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  {Ω : Type*} [MeasurableSpace Ω]

/-- **B06.** Expectation of a bilinear product transports interval `L²` domination to BV domination. -/
theorem s111t_expectation_BV_comparison
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : E →L[ℝ] F →L[ℝ] G)
    (D Db : ℝ → Ω → E) (V Vb : Ω → F)
    (H C delta : ℝ) (hH : 0 ≤ H) (hC : 0 ≤ C) (hdelta : 0 ≤ delta)
    (f g : ℝ → ℝ) (hf : IntegrableOn f (Set.Icc 0 H))
    (hg : IntegrableOn g (Set.Icc 0 H))
    (hfn : ∀ v ∈ Set.Icc 0 H, 0 ≤ f v) (hgn : ∀ v ∈ Set.Icc 0 H, 0 ≤ g v)
    (hD : ∀ v ∈ Set.Icc 0 H, MemLp (D v) 2 P ∧ MemLp (Db v) 2 P)
    (hV : MemLp V 2 P) (hVb : MemLp Vb 2 P)
    (hVm : eLpNorm V 2 P ≤ ENNReal.ofReal C)
    (hVdiff : eLpNorm (fun w => V w - Vb w) 2 P ≤ ENNReal.ofReal delta)
    (hDb : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ H →
      eLpNorm (fun w => Db b w - Db a w) 2 P ≤ ENNReal.ofReal (∫ v in Set.Icc a b, f v))
    (hDdiff : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ H →
      eLpNorm (fun w => (D b w - Db b w) - (D a w - Db a w)) 2 P ≤
        ENNReal.ofReal (∫ v in Set.Icc a b, g v)) :
    let K := fun v => (∫ w, B (D v w) (V w) ∂P) - (∫ w, B (Db v w) (Vb w) ∂P)
    ContinuousOn K (Set.Icc 0 H) ∧
      eVariationOn K (Set.Icc 0 H) ≤
        ENNReal.ofReal (‖B‖ * (C * (∫ v in Set.Icc 0 H, g v) +
          delta * (∫ v in Set.Icc 0 H, f v))) := by
  intro K
  -- the dominating primitive
  set Λ : ℝ → ℝ := fun x => ‖B‖ * (C * (∫ v in (0 : ℝ)..x, g v) + delta * (∫ v in (0 : ℝ)..x, f v)) with hΛ
  have hii : ∀ (h : ℝ → ℝ), IntegrableOn h (Set.Icc 0 H) → ∀ x ∈ Set.Icc (0 : ℝ) H,
      IntervalIntegrable h volume 0 x := by
    intro h hh x hx
    refine IntegrableOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hx.1]
    exact hh.mono_set (Set.Icc_subset_Icc le_rfl hx.2)
  have hΛinc : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ H →
      Λ b - Λ a = ‖B‖ * (C * (∫ v in Set.Icc a b, g v) + delta * (∫ v in Set.Icc a b, f v)) := by
    intro a b ha hab hb
    have e : ∀ h : ℝ → ℝ, IntegrableOn h (Set.Icc 0 H) →
        (∫ v in (0 : ℝ)..b, h v) - (∫ v in (0 : ℝ)..a, h v) = ∫ v in Set.Icc a b, h v := by
      intro h hh
      rw [intervalIntegral.integral_interval_sub_left (hii h hh b ⟨ha.trans hab, hb⟩)
        (hii h hh a ⟨ha, hab.trans hb⟩), intervalIntegral.integral_of_le hab,
        MeasureTheory.integral_Icc_eq_integral_Ioc]
    have eg := e g hg
    have ef := e f hf
    simp only [hΛ]
    linear_combination (‖B‖ * C) * eg + (‖B‖ * delta) * ef
  have hFab : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ H → 0 ≤ ∫ v in Set.Icc a b, f v := fun a b ha hab hb =>
    setIntegral_nonneg measurableSet_Icc fun v hv => hfn v ⟨ha.trans hv.1, hv.2.trans hb⟩
  have hGab : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ H → 0 ≤ ∫ v in Set.Icc a b, g v := fun a b ha hab hb =>
    setIntegral_nonneg measurableSet_Icc fun v hv => hgn v ⟨ha.trans hv.1, hv.2.trans hb⟩
  -- increment estimate
  have hbound : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ H → ‖K b - K a‖ ≤ Λ b - Λ a := by
    intro a b ha hab hb
    rw [hΛinc a b ha hab hb]
    have hDa := hD a ⟨ha, hab.trans hb⟩
    have hDbb := hD b ⟨ha.trans hab, hb⟩
    have hx : MemLp (fun w => (D b w - Db b w) - (D a w - Db a w)) 2 P :=
      (hDbb.1.sub hDbb.2).sub (hDa.1.sub hDa.2)
    have hy : MemLp (fun w => Db b w - Db a w) 2 P := hDbb.2.sub hDa.2
    have hVV : MemLp (fun w => V w - Vb w) 2 P := hV.sub hVb
    have i1 := s111t_bil_integrable B hDbb.1 hV
    have i2 := s111t_bil_integrable B hDbb.2 hVb
    have i3 := s111t_bil_integrable B hDa.1 hV
    have i4 := s111t_bil_integrable B hDa.2 hVb
    have e1 : K b - K a = ∫ w, (B ((D b w - Db b w) - (D a w - Db a w)) (V w) +
        B (Db b w - Db a w) (V w - Vb w)) ∂P := by
      have hpt : ∀ w, B ((D b w - Db b w) - (D a w - Db a w)) (V w) + B (Db b w - Db a w) (V w - Vb w) =
          (B (D b w) (V w) - B (Db b w) (Vb w)) - (B (D a w) (V w) - B (Db a w) (Vb w)) := by
        intro w
        simp only [map_sub, ContinuousLinearMap.sub_apply]
        abel
      have i12 : Integrable (fun w => B (D b w) (V w) - B (Db b w) (Vb w)) P := i1.sub i2
      have i34 : Integrable (fun w => B (D a w) (V w) - B (Db a w) (Vb w)) P := i3.sub i4
      have h1 := integral_sub i12 i34
      have h2 := integral_sub i1 i2
      have h3 := integral_sub i3 i4
      have hcongr : (∫ w, (B ((D b w - Db b w) - (D a w - Db a w)) (V w) +
          B (Db b w - Db a w) (V w - Vb w)) ∂P) =
          ∫ w, ((B (D b w) (V w) - B (Db b w) (Vb w)) - (B (D a w) (V w) - B (Db a w) (Vb w))) ∂P :=
        integral_congr_ae (Eventually.of_forall hpt)
      rw [hcongr, h1, h2, h3]
    rw [e1]
    have j1 := s111t_bil_integrable B hx hV
    have j2 := s111t_bil_integrable B hy hVV
    rw [integral_add j1 j2]
    refine (norm_add_le _ _).trans ?_
    have b1 := s111t_bil_integral_le B hx hV (hGab a b ha hab hb) hC (hDdiff a b ha hab hb) hVm
    have b2 := s111t_bil_integral_le B hy hVV (hFab a b ha hab hb) hdelta (hDb a b ha hab hb) hVdiff
    nlinarith [b1, b2]
  have hΛc : ContinuousOn Λ (Set.Icc 0 H) := by
    have hu : Set.uIcc (0 : ℝ) H = Set.Icc 0 H := Set.uIcc_of_le hH
    have c1 : ContinuousOn (fun x => ∫ v in (0 : ℝ)..x, g v) (Set.Icc 0 H) := by
      rw [← hu]
      exact intervalIntegral.continuousOn_primitive_interval (by rw [hu]; exact hg)
    have c2 : ContinuousOn (fun x => ∫ v in (0 : ℝ)..x, f v) (Set.Icc 0 H) := by
      rw [← hu]
      exact intervalIntegral.continuousOn_primitive_interval (by rw [hu]; exact hf)
    exact ContinuousOn.mul continuousOn_const
      (ContinuousOn.add (ContinuousOn.mul continuousOn_const c1) (ContinuousOn.mul continuousOn_const c2))
  have hdist : ∀ x ∈ Set.Icc (0 : ℝ) H, ∀ y ∈ Set.Icc (0 : ℝ) H, dist (K y) (K x) ≤ |Λ y - Λ x| := by
    intro x hx y hy
    rw [dist_eq_norm]
    rcases le_total x y with h | h
    · rw [abs_of_nonneg (by have := hbound x y hx.1 h hy.2; linarith [norm_nonneg (K y - K x)])]
      exact hbound x y hx.1 h hy.2
    · rw [abs_sub_comm, abs_of_nonneg (by have := hbound y x hy.1 h hx.2; linarith [norm_nonneg (K x - K y)]),
        norm_sub_rev]
      exact hbound y x hy.1 h hx.2
  refine ⟨fun x hx => ?_, ?_⟩
  · rw [ContinuousWithinAt, tendsto_iff_dist_tendsto_zero]
    have hΛt : Tendsto (fun y => |Λ y - Λ x|) (nhdsWithin x (Set.Icc 0 H)) (nhds 0) := by
      have := ((hΛc x hx).tendsto.sub_const (Λ x)).abs
      simpa using this
    exact squeeze_zero' (Eventually.of_forall fun y => dist_nonneg)
      (eventually_nhdsWithin_of_forall fun y hy => hdist x hx y hy) hΛt
  · unfold eVariationOn
    refine iSup_le fun p => ?_
    obtain ⟨n, u, hu, hus⟩ := p
    have hmono : ∀ x y : ℝ, x ∈ Set.Icc (0 : ℝ) H → y ∈ Set.Icc (0 : ℝ) H → x ≤ y → Λ x ≤ Λ y := by
      intro x y hx hy hxy
      have := hΛinc x y hx.1 hxy hy.2
      have h0 : 0 ≤ ‖B‖ * (C * (∫ v in Set.Icc x y, g v) + delta * (∫ v in Set.Icc x y, f v)) := by
        have := hGab x y hx.1 hxy hy.2
        have := hFab x y hx.1 hxy hy.2
        positivity
      linarith
    have hstep : ∀ i, edist (K (u (i + 1))) (K (u i)) ≤ ENNReal.ofReal (Λ (u (i + 1)) - Λ (u i)) := by
      intro i
      rw [edist_dist]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [dist_eq_norm]
      exact hbound _ _ (hus i).1 (hu (Nat.le_succ i)) (hus (i + 1)).2
    have hΛ0 : Λ 0 = 0 := by simp [hΛ]
    calc ∑ i ∈ Finset.range n, edist (K (u (i + 1))) (K (u i))
        ≤ ∑ i ∈ Finset.range n, ENNReal.ofReal (Λ (u (i + 1)) - Λ (u i)) := Finset.sum_le_sum fun i _ => hstep i
      _ = ENNReal.ofReal (∑ i ∈ Finset.range n, (Λ (u (i + 1)) - Λ (u i))) := by
          rw [ENNReal.ofReal_sum_of_nonneg]
          intro i _
          have := hmono (u i) (u (i + 1)) (hus i) (hus (i + 1)) (hu (Nat.le_succ i))
          linarith
      _ = ENNReal.ofReal (Λ (u n) - Λ (u 0)) := by rw [Finset.sum_range_sub (fun i => Λ (u i))]
      _ ≤ ENNReal.ofReal (‖B‖ * (C * (∫ v in Set.Icc 0 H, g v) + delta * (∫ v in Set.Icc 0 H, f v))) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 := hmono (u n) H (hus n) ⟨hH, le_rfl⟩ (hus n).2
          have h2 := hmono 0 (u 0) ⟨le_rfl, hH⟩ (hus 0) (hus 0).1
          have h3 := hΛinc 0 H le_rfl hH le_rfl
          linarith

end BV

end HRS.MS.S111T

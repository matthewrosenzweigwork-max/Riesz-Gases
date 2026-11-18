import HRS.MS.Fp81S21WindowD2

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.CovMeas HRS.MS.GenPath

variable {d : ℕ} {m a H : ℝ}

/-- Translation sends the window time interval to its physical-time interval. -/
lemma fp81s21_window_shift_measurePreserving (a H : ℝ) :
    MeasurePreserving (fun t : ℝ => a + t)
      (volume.restrict (Icc (0 : ℝ) H))
      (volume.restrict (Icc a (a + H))) := by
  have hmp := (measurePreserving_add_right (volume : Measure ℝ) a).restrict_preimage
    (measurableSet_Icc : MeasurableSet (Icc a (a + H)))
  have hpre : (fun t : ℝ => t + a) ⁻¹' Icc a (a + H) = Icc (0 : ℝ) H := by
    ext t
    simp only [mem_preimage, mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩
      constructor <;> linarith
    · rintro ⟨h1, h2⟩
      constructor <;> linarith
  rw [hpre] at hmp
  simpa [add_comm] using hmp

/-- Restriction of an `L²` class to a smaller measure. -/
def fp81s21_restrictLp {μ₀ μ₁ : Measure ℝ} (hμ : μ₀ ≤ μ₁) :
    Lp (OscDual d m) 2 μ₁ →ₗ[ℝ] Lp (OscDual d m) 2 μ₀ where
  toFun f := ((Lp.memLp f).mono_measure hμ).toLp f
  map_add' f g := by
    apply Lp.ext
    have hfg := (Lp.coeFn_add f g).filter_mono (Measure.absolutelyContinuous_of_le hμ).ae_le
    set hf : MemLp (f : ℝ → OscDual d m) 2 μ₀ := (Lp.memLp f).mono_measure hμ
    set hg : MemLp (g : ℝ → OscDual d m) 2 μ₀ := (Lp.memLp g).mono_measure hμ
    set hmSum : MemLp ((f + g : Lp (OscDual d m) 2 μ₁) : ℝ → OscDual d m) 2 μ₀ :=
      (Lp.memLp (f + g)).mono_measure hμ
    filter_upwards [MemLp.coeFn_toLp hmSum, MemLp.coeFn_toLp hf,
      MemLp.coeFn_toLp hg, Lp.coeFn_add (hf.toLp f) (hg.toLp g), hfg] with t hsumEq hfEq hgEq hadd hfg
    simp only [Pi.add_apply] at hfg hadd ⊢
    calc
      ((hmSum.toLp _ : Lp (OscDual d m) 2 μ₀) : ℝ → OscDual d m) t =
          ((f + g : Lp (OscDual d m) 2 μ₁) : ℝ → OscDual d m) t := hsumEq
      _ = (f : ℝ → OscDual d m) t + (g : ℝ → OscDual d m) t := hfg
      _ = ((hf.toLp f : Lp (OscDual d m) 2 μ₀) : ℝ → OscDual d m) t +
          ((hg.toLp g : Lp (OscDual d m) 2 μ₀) : ℝ → OscDual d m) t := by rw [hfEq, hgEq]
      _ = ((hf.toLp f + hg.toLp g : Lp (OscDual d m) 2 μ₀) : ℝ → OscDual d m) t := hadd.symm
  map_smul' c f := by
    apply Lp.ext
    have hcf := (Lp.coeFn_smul c f).filter_mono (Measure.absolutelyContinuous_of_le hμ).ae_le
    set hf : MemLp (f : ℝ → OscDual d m) 2 μ₀ := (Lp.memLp f).mono_measure hμ
    set hmCF : MemLp ((c • f : Lp (OscDual d m) 2 μ₁) : ℝ → OscDual d m) 2 μ₀ :=
      (Lp.memLp (c • f)).mono_measure hμ
    filter_upwards [MemLp.coeFn_toLp hmCF, MemLp.coeFn_toLp hf,
      Lp.coeFn_smul c (hf.toLp f), hcf] with t hcfEq hfEq hsmul hcfEq'
    simp only [Pi.smul_apply] at hcf hsmul ⊢
    calc
      ((hmCF.toLp _ : Lp (OscDual d m) 2 μ₀) : ℝ → OscDual d m) t =
          ((c • f : Lp (OscDual d m) 2 μ₁) : ℝ → OscDual d m) t := hcfEq
      _ = c • (f : ℝ → OscDual d m) t := hcfEq'
      _ = c • ((hf.toLp f : Lp (OscDual d m) 2 μ₀) : ℝ → OscDual d m) t := by rw [hfEq]
      _ = ((c • hf.toLp f : Lp (OscDual d m) 2 μ₀) : ℝ → OscDual d m) t := hsmul.symm

lemma fp81s21_restrictLp_norm_le {μ₀ μ₁ : Measure ℝ} (hμ : μ₀ ≤ μ₁)
    (f : Lp (OscDual d m) 2 μ₁) : ‖fp81s21_restrictLp (d := d) (m := m) hμ f‖ ≤ ‖f‖ := by
  change ‖((Lp.memLp f).mono_measure hμ).toLp f‖ ≤ ‖f‖
  rw [Lp.norm_def, Lp.norm_def]
  rw [eLpNorm_congr_ae (MemLp.coeFn_toLp ((Lp.memLp f).mono_measure hμ))]
  exact ENNReal.toReal_mono (Lp.memLp f).eLpNorm_ne_top
    (eLpNorm_mono_measure (f : ℝ → OscDual d m) hμ)

/-- Pullback of an `L²` class along a measure preserving map, as a linear map. -/
def fp81s21_pullbackLp {μ₀ μ₁ : Measure ℝ} (f : ℝ → ℝ)
    (hmp : MeasurePreserving f μ₀ μ₁) :
    Lp (OscDual d m) 2 μ₁ →ₗ[ℝ] Lp (OscDual d m) 2 μ₀ where
  toFun x := Lp.compMeasurePreserving f hmp x
  map_add' x y := (Lp.compMeasurePreserving f hmp).map_add x y
  map_smul' c x := by
    apply Lp.ext
    have hc := Lp.coeFn_compMeasurePreserving (c • x) hmp
    have hx := Lp.coeFn_compMeasurePreserving x hmp
    have hsmul := hmp.quasiMeasurePreserving.ae (Lp.coeFn_smul c x)
    have hout := Lp.coeFn_smul c (Lp.compMeasurePreserving f hmp x)
    filter_upwards [hc, hx, hsmul, hout] with t hc hx hsmul hout
    simp only [Function.comp_apply, Pi.smul_apply] at hc hx hsmul hout ⊢
    calc
      ((Lp.compMeasurePreserving f hmp (c • x) : Lp (OscDual d m) 2 μ₀) : ℝ → OscDual d m) t =
          ((c • x : Lp (OscDual d m) 2 μ₁) : ℝ → OscDual d m) (f t) := hc
      _ = c • ((x : Lp (OscDual d m) 2 μ₁) : ℝ → OscDual d m) (f t) := hsmul
      _ = c • ((Lp.compMeasurePreserving f hmp x : Lp (OscDual d m) 2 μ₀) : ℝ → OscDual d m) t := by rw [hx]
      _ = ((c • Lp.compMeasurePreserving f hmp x : Lp (OscDual d m) 2 μ₀) : ℝ → OscDual d m) t := hout.symm

/-- The translated `L²` derivative map from physical history time to window time. -/
def fp81s21_window_shiftLp (ha : 0 ≤ a) :
    L2Path d m (a + H) →L[ℝ] L2Path d m H := by
  let μfull : Measure ℝ := volume.restrict (Icc (0 : ℝ) (a + H))
  let μseg : Measure ℝ := volume.restrict (Icc a (a + H))
  let μwin : Measure ℝ := volume.restrict (Icc (0 : ℝ) H)
  have hseg : μseg ≤ μfull := by
    apply Measure.restrict_mono
    · intro t ht
      exact ⟨le_trans ha ht.1, ht.2⟩
    · exact le_rfl
  have hmp : MeasurePreserving (fun t : ℝ => a + t) μwin μseg :=
    fp81s21_window_shift_measurePreserving a H
  let lin : L2Path d m (a + H) →ₗ[ℝ] L2Path d m H :=
    (fp81s21_pullbackLp (d := d) (m := m) (fun t => a + t) hmp).comp
      (fp81s21_restrictLp (d := d) (m := m) hseg)
  have hnorm : ∀ x, ‖lin x‖ ≤ 1 * ‖x‖ := by
    intro x
    have hIso := Lp.isometry_compMeasurePreserving
      (p := (2 : ℝ≥0∞)) (E := OscDual d m) hmp
    have hIsoNorm := hIso.dist_eq
      (fp81s21_restrictLp (d := d) (m := m) hseg x) 0
    calc
      ‖lin x‖ = ‖fp81s21_restrictLp (d := d) (m := m) hseg x‖ := by
        simpa [lin, fp81s21_pullbackLp, dist_eq_norm] using hIsoNorm
      _ ≤ ‖x‖ := fp81s21_restrictLp_norm_le hseg x
      _ = 1 * ‖x‖ := by ring
  exact lin.mkContinuous 1 hnorm

lemma fp81s21_window_shiftLp_apply_ae (ha : 0 ≤ a)
    (x : L2Path d m (a + H)) :
    (fun t : ℝ => ((fp81s21_window_shiftLp (d := d) (m := m) (a := a) (H := H) ha x :
      L2Path d m H) : ℝ → OscDual d m) t) =ᵐ[volume.restrict (Icc (0 : ℝ) H)]
      fun t => (x : ℝ → OscDual d m) (a + t) := by
  let μseg : Measure ℝ := volume.restrict (Icc a (a + H))
  let μwin : Measure ℝ := volume.restrict (Icc (0 : ℝ) H)
  have hseg : μseg ≤ volume.restrict (Icc (0 : ℝ) (a + H)) := by
    apply Measure.restrict_mono
    · intro t ht
      exact ⟨le_trans ha ht.1, ht.2⟩
    · exact le_rfl
  have hmp : MeasurePreserving (fun t : ℝ => a + t) μwin μseg :=
    fp81s21_window_shift_measurePreserving a H
  have hcomp := Lp.coeFn_compMeasurePreserving
    (fp81s21_restrictLp (d := d) (m := m) hseg x) hmp
  have hrestr : (fp81s21_restrictLp (d := d) (m := m) hseg x : ℝ → OscDual d m) =ᵐ[μseg]
      (x : ℝ → OscDual d m) := by
    exact MemLp.coeFn_toLp ((Lp.memLp x).mono_measure hseg)
  have hpull := hmp.quasiMeasurePreserving.ae hrestr
  filter_upwards [hcomp, hpull] with t hc hp
  exact hc.trans (by simpa [Function.comp_apply] using hp)

/-- Evaluation of the full feature's integrated coordinate at a fixed time. -/
def fp81s21_evalA_CLM {L : ℝ} (hL : 0 ≤ L) (t : ℝ) :
    KSpace d m L →L[ℝ] OscDual d m := by
  let lin : KSpace d m L →ₗ[ℝ] OscDual d m :=
    { toFun := fun x => x.evalA t
      map_add' := fun x y => s56_evalA_add x y t
      map_smul' := fun c x => s56_evalA_smul c x t }
  have hnorm : ∀ x, ‖lin x‖ ≤ (1 + Real.sqrt L) * ‖x‖ := by
    intro x
    have he := HRS.MS.U9.u9_evalA_norm_le hL x t
    have h0 := HRS.MS.U9.u9_norm_A₀_le x
    have h1 := HRS.MS.U9.u9_norm_A'_le x
    have hs : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
    have h1' : Real.sqrt L * ‖x.A'‖ ≤ Real.sqrt L * ‖x‖ :=
      mul_le_mul_of_nonneg_left h1 hs
    change ‖x.evalA t‖ ≤ _
    nlinarith
  exact lin.mkContinuous (1 + Real.sqrt L) hnorm

lemma fp81s21_evalA_CLM_norm_le {L : ℝ} (hL : 0 ≤ L) (t : ℝ) :
    ‖fp81s21_evalA_CLM (d := d) (m := m) hL t‖ ≤ 1 + Real.sqrt L := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  have he := HRS.MS.U9.u9_evalA_norm_le hL x t
  have h0 := HRS.MS.U9.u9_norm_A₀_le x
  have h1 := HRS.MS.U9.u9_norm_A'_le x
  have hs : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
  have h1' : Real.sqrt L * ‖x.A'‖ ≤ Real.sqrt L * ‖x‖ :=
    mul_le_mul_of_nonneg_left h1 hs
  change ‖x.evalA t‖ ≤ _
  nlinarith

lemma fp81s21_window_shiftLp_norm_le (ha : 0 ≤ a) :
    ‖fp81s21_window_shiftLp (d := d) (m := m) (a := a) (H := H) ha‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun x => ?_
  let μseg : Measure ℝ := volume.restrict (Icc a (a + H))
  let μwin : Measure ℝ := volume.restrict (Icc (0 : ℝ) H)
  have hseg : μseg ≤ volume.restrict (Icc (0 : ℝ) (a + H)) := by
    apply Measure.restrict_mono
    · intro t ht
      exact ⟨le_trans ha ht.1, ht.2⟩
    · exact le_rfl
  have hmp : MeasurePreserving (fun t : ℝ => a + t) μwin μseg :=
    fp81s21_window_shift_measurePreserving a H
  have hIso := Lp.isometry_compMeasurePreserving
    (p := (2 : ℝ≥0∞)) (E := OscDual d m) hmp
  have hIsoNorm := hIso.dist_eq
    (fp81s21_restrictLp (d := d) (m := m) hseg x) 0
  calc
    ‖fp81s21_window_shiftLp (d := d) (m := m) (a := a) (H := H) ha x‖ =
        ‖fp81s21_restrictLp (d := d) (m := m) hseg x‖ := by
      simpa [fp81s21_window_shiftLp, fp81s21_pullbackLp, dist_eq_norm] using hIsoNorm
    _ ≤ ‖x‖ := fp81s21_restrictLp_norm_le hseg x
    _ = 1 * ‖x‖ := by ring

lemma fp81s21_KSpace_Aprime_add {L : ℝ} (x y : KSpace d m L) :
    (x + y).A' = x.A' + y.A' := by
  apply Lp.ext
  change ((x + y).A' : ℝ → OscDual d m) =ᵐ[volume.restrict (Icc (0 : ℝ) L)]
    ((x.A' + y.A' : L2Path d m L) : ℝ → OscDual d m)
  exact (s56_A'_add x y).trans (Lp.coeFn_add x.A' y.A').symm

lemma fp81s21_KSpace_Aprime_smul {L : ℝ} (c : ℝ) (x : KSpace d m L) :
    (c • x).A' = c • x.A' := by
  apply Lp.ext
  change ((c • x).A' : ℝ → OscDual d m) =ᵐ[volume.restrict (Icc (0 : ℝ) L)]
    ((c • x.A' : L2Path d m L) : ℝ → OscDual d m)
  exact (s56_A'_smul c x).trans (Lp.coeFn_smul c x.A').symm

lemma fp81s21_KSpace_mk_add {H : ℝ} (a₀ a₁ : OscDual d m)
    (f₀ f₁ : L2Path d m H) (b₀ b₁ : OscDual d m) :
    KSpace.mk (a₀ + a₁) (f₀ + f₁) (b₀ + b₁) =
      KSpace.mk a₀ f₀ b₀ + KSpace.mk a₁ f₁ b₁ := by
  change WithLp.toLp 2 (a₀ + a₁, WithLp.toLp 2 (f₀ + f₁, b₀ + b₁)) =
    WithLp.toLp 2 ((a₀, WithLp.toLp 2 (f₀, b₀)) + (a₁, WithLp.toLp 2 (f₁, b₁)))
  apply congrArg (WithLp.toLp 2)
  apply Prod.ext
  · rfl
  · exact congrArg (WithLp.toLp 2) (Prod.ext rfl rfl)

lemma fp81s21_KSpace_mk_smul {H : ℝ} (c : ℝ)
    (a₀ : OscDual d m) (f₀ : L2Path d m H) (b₀ : OscDual d m) :
    KSpace.mk (c • a₀) (c • f₀) (c • b₀) = c • KSpace.mk a₀ f₀ b₀ := by
  change WithLp.toLp 2 (c • a₀, WithLp.toLp 2 (c • f₀, c • b₀)) =
    WithLp.toLp 2 (c • (a₀, WithLp.toLp 2 (f₀, b₀)))
  apply congrArg (WithLp.toLp 2)
  apply Prod.ext
  · rfl
  · exact congrArg (WithLp.toLp 2) (Prod.ext rfl rfl)

/-- The minus branch of the full-to-window compression. -/
def fp81s21_windowCompressionMinus (ha : 0 ≤ a) (hH : 0 ≤ H) :
    KSpace d m (a + H) →L[ℝ] KSpace d m H := by
  let ev := fp81s21_evalA_CLM (d := d) (m := m) (L := a + H) (by linarith) a
  let sh := fp81s21_window_shiftLp (d := d) (m := m) (a := a) (H := H) ha
  let lin : KSpace d m (a + H) →ₗ[ℝ] KSpace d m H :=
    { toFun := fun x => KSpace.mk (ev x) (sh x.A') 0
      map_add' := by
        intro x y
        change KSpace.mk (ev (x + y)) (sh ((x + y).A')) 0 = _
        rw [ev.map_add, fp81s21_KSpace_Aprime_add, sh.map_add]
        simpa using fp81s21_KSpace_mk_add (ev x) (ev y) (sh x.A') (sh y.A') 0 0
      map_smul' := by
        intro c x
        change KSpace.mk (ev (c • x)) (sh ((c • x).A')) 0 = _
        rw [ev.map_smul, fp81s21_KSpace_Aprime_smul, sh.map_smul]
        simpa using fp81s21_KSpace_mk_smul c (ev x) (sh x.A') 0 }
  have hnorm : ∀ x, ‖lin x‖ ≤ (3 + Real.sqrt (a + H)) * ‖x‖ := by
    intro x
    change ‖KSpace.mk (ev x) (sh x.A') (0 : OscDual d m)‖ ≤ _
    have hsq : ‖KSpace.mk (ev x) (sh x.A') (0 : OscDual d m)‖ ^ 2 =
        ‖ev x‖ ^ 2 + ‖sh x.A'‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, s101_inner_mk]
      simp [real_inner_self_eq_norm_sq]
    have heOp : ‖ev‖ ≤ 1 + Real.sqrt (a + H) :=
      fp81s21_evalA_CLM_norm_le (d := d) (m := m) (L := a + H) (by linarith) a
    have he : ‖ev x‖ ≤ (1 + Real.sqrt (a + H)) * ‖x‖ := by
      calc
        ‖ev x‖ ≤ ‖ev‖ * ‖x‖ := ev.le_opNorm x
        _ ≤ (1 + Real.sqrt (a + H)) * ‖x‖ :=
          mul_le_mul_of_nonneg_right heOp (norm_nonneg _)
    have hs : ‖sh x.A'‖ ≤ ‖x‖ := by
      calc
        ‖sh x.A'‖ ≤ ‖sh‖ * ‖x.A'‖ := sh.le_opNorm _
        _ ≤ 1 * ‖x.A'‖ := mul_le_mul_of_nonneg_right
          (fp81s21_window_shiftLp_norm_le (d := d) (m := m) (a := a) (H := H) ha)
          (norm_nonneg _)
        _ = ‖x.A'‖ := by ring
        _ ≤ ‖x‖ := HRS.MS.U9.u9_norm_A'_le x
    have hx : 0 ≤ ‖x‖ := norm_nonneg _
    have he0 : 0 ≤ ‖ev x‖ := norm_nonneg _
    have hs0 : 0 ≤ ‖sh x.A'‖ := norm_nonneg _
    have hsum : ‖KSpace.mk (ev x) (sh x.A') (0 : OscDual d m)‖ ≤ ‖ev x‖ + ‖sh x.A'‖ := by
      have hcross : 0 ≤ 2 * ‖ev x‖ * ‖sh x.A'‖ := by positivity
      nlinarith [hsq]
    calc
      ‖KSpace.mk (ev x) (sh x.A') (0 : OscDual d m)‖ ≤ ‖ev x‖ + ‖sh x.A'‖ := hsum
      _ ≤ (1 + Real.sqrt (a + H)) * ‖x‖ + ‖x‖ :=
        add_le_add he hs
      _ ≤ (3 + Real.sqrt (a + H)) * ‖x‖ := by nlinarith
  exact lin.mkContinuous (3 + Real.sqrt (a + H)) hnorm

/-- The plus branch retains the full feature's terminal coordinate. -/
def fp81s21_windowCompressionPlus (ha : 0 ≤ a) (hH : 0 ≤ H) :
    KSpace d m (a + H) →L[ℝ] KSpace d m H := by
  let ev := fp81s21_evalA_CLM (d := d) (m := m) (L := a + H) (by linarith) a
  let sh := fp81s21_window_shiftLp (d := d) (m := m) (a := a) (H := H) ha
  let lin : KSpace d m (a + H) →ₗ[ℝ] KSpace d m H :=
    { toFun := fun x => KSpace.mk (ev x) (sh x.A') x.B
      map_add' := by
        intro x y
        change KSpace.mk (ev (x + y)) (sh ((x + y).A')) ((x + y).B) = _
        rw [ev.map_add, fp81s21_KSpace_Aprime_add, s56_B_add, sh.map_add]
        exact fp81s21_KSpace_mk_add (ev x) (ev y) (sh x.A') (sh y.A') x.B y.B
      map_smul' := by
        intro c x
        change KSpace.mk (ev (c • x)) (sh ((c • x).A')) ((c • x).B) = _
        rw [ev.map_smul, fp81s21_KSpace_Aprime_smul, s56_B_smul, sh.map_smul]
        exact fp81s21_KSpace_mk_smul c (ev x) (sh x.A') x.B }
  have hnorm : ∀ x, ‖lin x‖ ≤ (3 + Real.sqrt (a + H)) * ‖x‖ := by
    intro x
    change ‖KSpace.mk (ev x) (sh x.A') x.B‖ ≤ _
    have hsq : ‖KSpace.mk (ev x) (sh x.A') x.B‖ ^ 2 =
        ‖ev x‖ ^ 2 + ‖sh x.A'‖ ^ 2 + ‖x.B‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, s101_inner_mk]
      simp [real_inner_self_eq_norm_sq]
    have heOp : ‖ev‖ ≤ 1 + Real.sqrt (a + H) :=
      fp81s21_evalA_CLM_norm_le (d := d) (m := m) (L := a + H) (by linarith) a
    have he : ‖ev x‖ ≤ (1 + Real.sqrt (a + H)) * ‖x‖ := by
      calc
        ‖ev x‖ ≤ ‖ev‖ * ‖x‖ := ev.le_opNorm x
        _ ≤ (1 + Real.sqrt (a + H)) * ‖x‖ :=
          mul_le_mul_of_nonneg_right heOp (norm_nonneg _)
    have hs : ‖sh x.A'‖ ≤ ‖x‖ := by
      calc
        ‖sh x.A'‖ ≤ ‖sh‖ * ‖x.A'‖ := sh.le_opNorm _
        _ ≤ 1 * ‖x.A'‖ := mul_le_mul_of_nonneg_right
          (fp81s21_window_shiftLp_norm_le (d := d) (m := m) (a := a) (H := H) ha)
          (norm_nonneg _)
        _ = ‖x.A'‖ := by ring
        _ ≤ ‖x‖ := HRS.MS.U9.u9_norm_A'_le x
    have hb : ‖x.B‖ ≤ ‖x‖ := HRS.MS.U9.u9_norm_B_le x
    have hx : 0 ≤ ‖x‖ := norm_nonneg _
    have he0 : 0 ≤ ‖ev x‖ := norm_nonneg _
    have hs0 : 0 ≤ ‖sh x.A'‖ := norm_nonneg _
    have hb0 : 0 ≤ ‖x.B‖ := norm_nonneg _
    have hsum : ‖KSpace.mk (ev x) (sh x.A') x.B‖ ≤
        ‖ev x‖ + ‖sh x.A'‖ + ‖x.B‖ := by
      have hcross₁ : 0 ≤ 2 * ‖ev x‖ * ‖sh x.A'‖ := by positivity
      have hcross₂ : 0 ≤ 2 * ‖ev x‖ * ‖x.B‖ := by positivity
      have hcross₃ : 0 ≤ 2 * ‖sh x.A'‖ * ‖x.B‖ := by positivity
      nlinarith [hsq]
    calc
      ‖KSpace.mk (ev x) (sh x.A') x.B‖ ≤
          ‖ev x‖ + ‖sh x.A'‖ + ‖x.B‖ := hsum
      _ ≤ (1 + Real.sqrt (a + H)) * ‖x‖ + ‖x‖ + ‖x‖ := by
        gcongr
      _ = (3 + Real.sqrt (a + H)) * ‖x‖ := by ring
  exact lin.mkContinuous (3 + Real.sqrt (a + H)) hnorm

lemma fp81s21_windowCompressionMinus_apply (ha : 0 ≤ a) (hH : 0 ≤ H)
    (x : KSpace d m (a + H)) :
    fp81s21_windowCompressionMinus (d := d) (m := m) (a := a) (H := H) ha hH x =
      KSpace.mk (x.evalA a)
        (fp81s21_window_shiftLp (d := d) (m := m) (a := a) (H := H) ha x.A') 0 := by
  rfl

lemma fp81s21_windowCompressionPlus_apply (ha : 0 ≤ a) (hH : 0 ≤ H)
    (x : KSpace d m (a + H)) :
    fp81s21_windowCompressionPlus (d := d) (m := m) (a := a) (H := H) ha hH x =
      KSpace.mk (x.evalA a)
        (fp81s21_window_shiftLp (d := d) (m := m) (a := a) (H := H) ha x.A') x.B := by
  rfl

#print axioms fp81s21_window_shift_measurePreserving
#print axioms fp81s21_restrictLp
#print axioms fp81s21_restrictLp_norm_le

end HRS.Fp81.S21

end

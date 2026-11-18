import Mathlib

/-!
# Packet e213u16, file b: abstract measure-theoretic tools for the conditioning removal

* `u16_aesm_iff_condExp`: `AEStronglyMeasurable[m] f μ ↔ f =ᵐ μ[f|m]` for integrable `f`;
* `u16_aesm_of_L1_approx`: closure of `m`-a.e.-measurable functions under `L¹` limits;
* `u16_aesm_integral_slice`: if the slices `f v` are a.e. `m`-measurable then `∫ f v dν(v)` is;
* `u16_acl`: integral of a function of two independent random elements (Fubini).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MC.E213U16

section Cond

variable {Ω : Type*} {m m0 : MeasurableSpace Ω} {μ : Measure[m0] Ω}

theorem u16_aesm_iff_condExp [IsFiniteMeasure μ] (hm : m ≤ m0) {f : Ω → ℝ} (hf : Integrable f μ) :
    AEStronglyMeasurable[m] f μ ↔ f =ᵐ[μ] μ[f | m] := by
  have : SigmaFinite (μ.trim hm) := inferInstance
  constructor
  · intro h
    exact (condExp_of_aestronglyMeasurable' hm h hf).symm
  · intro h
    exact (stronglyMeasurable_condExp.aestronglyMeasurable).congr h.symm

/-- `L¹` closure of `m`-a.e.-measurable functions. -/
theorem u16_aesm_of_L1_approx [IsFiniteMeasure μ] (hm : m ≤ m0) {f : Ω → ℝ} (hf : Integrable f μ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ g : Ω → ℝ, AEStronglyMeasurable[m] g μ ∧ Integrable g μ ∧
      ∫ ω, |f ω - g ω| ∂μ ≤ ε) : AEStronglyMeasurable[m] f μ := by
  have : SigmaFinite (μ.trim hm) := inferInstance
  rw [u16_aesm_iff_condExp hm hf]
  have hc : Integrable (μ[f | m]) μ := integrable_condExp
  have key : ∫ ω, |f ω - (μ[f | m]) ω| ∂μ = 0 := by
    refine le_antisymm ?_ (integral_nonneg fun ω => abs_nonneg _)
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨g, hgm, hgi, hg⟩ := h (ε / 2) (by linarith)
    have e1 : g =ᵐ[μ] μ[g | m] := (u16_aesm_iff_condExp hm hgi).1 hgm
    have e2 : μ[f - g | m] =ᵐ[μ] μ[f | m] - μ[g | m] := condExp_sub hf hgi m
    have h3 : ∫ ω, |(μ[f | m]) ω - (μ[g | m]) ω| ∂μ ≤ ∫ ω, |f ω - g ω| ∂μ := by
      have := integral_abs_condExp_le (μ := μ) (m := m) (fun ω => f ω - g ω)
      calc ∫ ω, |(μ[f | m]) ω - (μ[g | m]) ω| ∂μ = ∫ ω, |(μ[f - g | m]) ω| ∂μ := by
            refine integral_congr_ae ?_
            filter_upwards [e2] with ω hω
            rw [hω]; rfl
        _ ≤ _ := this
    have i1 : Integrable (fun ω => |f ω - g ω|) μ := (hf.sub hgi).abs
    have i2 : Integrable (fun ω => |g ω - (μ[f | m]) ω|) μ := (hgi.sub hc).abs
    have i3 : Integrable (fun ω => |f ω - (μ[f | m]) ω|) μ := (hf.sub hc).abs
    have h4 : ∫ ω, |f ω - (μ[f | m]) ω| ∂μ ≤
        ∫ ω, |f ω - g ω| ∂μ + ∫ ω, |g ω - (μ[f | m]) ω| ∂μ := by
      rw [← integral_add i1 i2]
      refine integral_mono i3 (i1.add i2) fun ω => ?_
      simp only [Pi.add_apply]
      calc |f ω - (μ[f | m]) ω| = |(f ω - g ω) + (g ω - (μ[f | m]) ω)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    have h5 : ∫ ω, |g ω - (μ[f | m]) ω| ∂μ ≤ ∫ ω, |f ω - g ω| ∂μ := by
      calc ∫ ω, |g ω - (μ[f | m]) ω| ∂μ = ∫ ω, |(μ[g | m]) ω - (μ[f | m]) ω| ∂μ := by
            refine integral_congr_ae ?_
            filter_upwards [e1] with ω hω
            rw [← hω]
        _ = ∫ ω, |(μ[f | m]) ω - (μ[g | m]) ω| ∂μ := by
            refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
            exact abs_sub_comm _ _
        _ ≤ _ := h3
    linarith
  have hz : (fun ω => |f ω - (μ[f | m]) ω|) =ᵐ[μ] 0 := by
    refine (integral_eq_zero_iff_of_nonneg (fun ω => abs_nonneg _) (hf.sub hc).abs).1 key
  filter_upwards [hz] with ω hω
  have : |f ω - (μ[f | m]) ω| = 0 := hω
  have := abs_eq_zero.1 this
  linarith

/-- Pull-out for a bounded test function: `∫ F h = ∫ F μ[h|m]` when `F` is a.e. `m`-measurable. -/
theorem u16_pull_out [IsFiniteMeasure μ] (hm : m ≤ m0) {F h : Ω → ℝ} (hF : AEStronglyMeasurable[m] F μ)
    (hFi : Integrable F μ) (hh : Measurable[m0] h) {c : ℝ} (hc : ∀ ω, |h ω| ≤ c) :
    ∫ ω, F ω * h ω ∂μ = ∫ ω, F ω * (μ[h | m]) ω ∂μ := by
  have : SigmaFinite (μ.trim hm) := inferInstance
  have hhi : Integrable h μ := Integrable.of_bound hh.aestronglyMeasurable c
    (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hc ω)
  have hFh : Integrable (F * h) μ := by
    refine hFi.mul_bdd hh.aestronglyMeasurable (c := c) (Eventually.of_forall fun ω => ?_)
    simpa [Real.norm_eq_abs] using hc ω
  have h1 := condExp_mul_of_aestronglyMeasurable_left hF hFh hhi
  calc ∫ ω, F ω * h ω ∂μ = ∫ ω, (μ[F * h | m]) ω ∂μ := (integral_condExp hm).symm
    _ = ∫ ω, (F * μ[h | m]) ω ∂μ := integral_congr_ae h1
    _ = _ := rfl

/-- Slice integration: if the slices are a.e. `m`-measurable, so is the integral over the parameter. -/
theorem u16_aesm_integral_slice [IsProbabilityMeasure μ] (hm : m ≤ m0)
    {ν : Measure ℝ} [SFinite ν] {f : ℝ → Ω → ℝ}
    (hf : StronglyMeasurable (Function.uncurry f)) (hint : Integrable (Function.uncurry f) (ν.prod μ))
    (hslice : ∀ᵐ v ∂ν, AEStronglyMeasurable[m] (f v) μ) :
    AEStronglyMeasurable[m] (fun ω => ∫ v, f v ω ∂ν) μ := by
  have : SigmaFinite (μ.trim hm) := inferInstance
  set g : Ω → ℝ := fun ω => ∫ v, f v ω ∂ν with hg
  have hgi : Integrable g μ := hint.integral_prod_right
  have hgs : StronglyMeasurable g := by
    exact StronglyMeasurable.integral_prod_left (μ := ν) hf
  set G : Ω → ℝ := μ[g | m] with hG
  have hGs : StronglyMeasurable[m] G := stronglyMeasurable_condExp
  have hGs0 : StronglyMeasurable G := hGs.mono hm
  set h : Ω → ℝ := fun ω => if 0 ≤ g ω - G ω then 1 else -1 with hh
  have hhm : Measurable h :=
    Measurable.ite (measurableSet_le measurable_const (hgs.measurable.sub hGs0.measurable))
      measurable_const measurable_const
  have hhb : ∀ ω, |h ω| ≤ 1 := fun ω => by
    simp only [hh]
    split_ifs <;> norm_num
  -- the pairing identity `∫ g h = ∫ G h`
  have hE : MeasurableSet (Set.univ : Set Ω) := MeasurableSet.univ
  have hEh : ∀ᵐ ω ∂μ, |(μ[h | m]) ω| ≤ 1 := by
    have := ae_bdd_abs_condExp_of_ae_bdd_abs (μ := μ) (m := m) (R := 1) (f := h)
      (Eventually.of_forall fun ω => by simpa using hhb ω)
    simpa using this
  have hEhs : StronglyMeasurable (μ[h | m]) := (stronglyMeasurable_condExp (m := m) (f := h)).mono hm
  -- Fubini for `f v ω * h ω`
  have hfh : Integrable (fun p : ℝ × Ω => f p.1 p.2 * h p.2) (ν.prod μ) := by
    refine hint.mul_bdd (c := 1) ?_ (Eventually.of_forall fun p => ?_)
    · exact (hhm.comp measurable_snd).aestronglyMeasurable
    · simpa [Real.norm_eq_abs] using hhb p.2
  have hfe : Integrable (fun p : ℝ × Ω => f p.1 p.2 * (μ[h | m]) p.2) (ν.prod μ) := by
    refine hint.mul_bdd (c := 1) ?_ ?_
    · exact (hEhs.measurable.comp measurable_snd).aestronglyMeasurable
    · have : ∀ᵐ p ∂(ν.prod μ), |(μ[h | m]) p.2| ≤ 1 := by
        exact (Measure.quasiMeasurePreserving_snd (μ := ν) (ν := μ)).ae hEh
      filter_upwards [this] with p hp using by simpa [Real.norm_eq_abs] using hp
  have hslice_i : ∀ᵐ v ∂ν, Integrable (f v) μ := hint.prod_right_ae
  have step1 : ∫ ω, g ω * h ω ∂μ = ∫ ω, g ω * (μ[h | m]) ω ∂μ := by
    calc ∫ ω, g ω * h ω ∂μ = ∫ ω, ∫ v, f v ω * h ω ∂ν ∂μ := by
          refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
          simp only [hg]
          rw [integral_mul_const]
      _ = ∫ v, ∫ ω, f v ω * h ω ∂μ ∂ν := (integral_integral_swap (f := fun v ω => f v ω * h ω) hfh).symm
      _ = ∫ v, ∫ ω, f v ω * (μ[h | m]) ω ∂μ ∂ν := by
          refine integral_congr_ae ?_
          filter_upwards [hslice, hslice_i] with v hv hvi
          exact u16_pull_out hm hv hvi hhm hhb
      _ = ∫ ω, ∫ v, f v ω * (μ[h | m]) ω ∂ν ∂μ := integral_integral_swap (f := fun v ω => f v ω * (μ[h | m]) ω) hfe
      _ = ∫ ω, g ω * (μ[h | m]) ω ∂μ := by
          refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
          simp only [hg]
          rw [integral_mul_const]
  have step2 : ∫ ω, G ω * h ω ∂μ = ∫ ω, G ω * (μ[h | m]) ω ∂μ :=
    u16_pull_out hm hGs.aestronglyMeasurable integrable_condExp hhm hhb
  have step3 : ∫ ω, g ω * (μ[h | m]) ω ∂μ = ∫ ω, G ω * (μ[h | m]) ω ∂μ := by
    -- `μ[h|m]` is `m`-measurable and bounded
    have hb : ∀ᵐ ω ∂μ, ‖(μ[h | m]) ω‖ ≤ 1 := by
      filter_upwards [hEh] with ω hω using by simpa [Real.norm_eq_abs] using hω
    have hgk : Integrable (fun ω => g ω * (μ[h | m]) ω) μ :=
      hgi.mul_bdd (c := 1) hEhs.aestronglyMeasurable hb
    have := condExp_stronglyMeasurable_mul_of_bound hm (f := μ[h | m]) (g := g) stronglyMeasurable_condExp hgi 1
      (by filter_upwards [hEh] with ω hω using by simpa [Real.norm_eq_abs] using hω)
    calc ∫ ω, g ω * (μ[h | m]) ω ∂μ = ∫ ω, (μ[h | m] * g) ω ∂μ := by
          refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
          simp [mul_comm]
      _ = ∫ ω, (μ[μ[h | m] * g | m]) ω ∂μ := (integral_condExp hm).symm
      _ = ∫ ω, (μ[h | m] * μ[g | m]) ω ∂μ := integral_congr_ae this
      _ = _ := by
          refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
          simp [hG, mul_comm]
  have key : ∫ ω, |g ω - G ω| ∂μ = 0 := by
    have e : ∀ ω, |g ω - G ω| = (g ω - G ω) * h ω := fun ω => by
      simp only [hh]
      by_cases hc : 0 ≤ g ω - G ω
      · rw [if_pos hc, abs_of_nonneg hc, mul_one]
      · rw [if_neg hc, abs_of_neg (not_le.1 hc)]; ring
    simp_rw [e]
    have hgG : Integrable (fun ω => g ω * h ω) μ := hgi.mul_bdd (c := 1) hhm.aestronglyMeasurable
      (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hhb ω)
    have hGG : Integrable (fun ω => G ω * h ω) μ := integrable_condExp.mul_bdd (c := 1)
      hhm.aestronglyMeasurable (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hhb ω)
    have : ∫ ω, (g ω - G ω) * h ω ∂μ = ∫ ω, g ω * h ω ∂μ - ∫ ω, G ω * h ω ∂μ := by
      rw [← integral_sub hgG hGG]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      ring
    rw [this, step1, step2, step3, sub_self]
  have hz : (fun ω => |g ω - G ω|) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun ω => abs_nonneg _) (hgi.sub integrable_condExp).abs).1 key
  have : g =ᵐ[μ] G := by
    filter_upwards [hz] with ω hω
    have := abs_eq_zero.1 (show |g ω - G ω| = 0 from hω)
    linarith
  exact (u16_aesm_iff_condExp hm hgi).2 this

end Cond

section ACL

variable {Ω V W : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [MeasurableSpace V] [MeasurableSpace W]

/-- Fubini for two independent random elements. -/
theorem u16_acl {v : Ω → V} {γ : Ω → W} (hv : AEMeasurable v μ) (hγ : AEMeasurable γ μ)
    (hind : IndepFun v γ μ) {F : V → W → ℝ} (hF : StronglyMeasurable (Function.uncurry F))
    (hint : Integrable (fun ω => F (v ω) (γ ω)) μ) :
    ∫ ω, F (v ω) (γ ω) ∂μ = ∫ ω, (∫ w, F (v ω) w ∂(μ.map γ)) ∂μ := by
  have hmap : μ.map (fun ω => (v ω, γ ω)) = (μ.map v).prod (μ.map γ) :=
    (indepFun_iff_map_prod_eq_prod_map_map hv hγ).1 hind
  have hvγ : AEMeasurable (fun ω => (v ω, γ ω)) μ := hv.prodMk hγ
  have hFu : AEStronglyMeasurable (Function.uncurry F) (μ.map (fun ω => (v ω, γ ω))) :=
    hF.aestronglyMeasurable
  have hint' : Integrable (Function.uncurry F) ((μ.map v).prod (μ.map γ)) := by
    rw [← hmap]
    exact (integrable_map_measure hFu hvγ).2 hint
  have h1 : ∫ ω, F (v ω) (γ ω) ∂μ = ∫ p, Function.uncurry F p ∂((μ.map v).prod (μ.map γ)) := by
    rw [← hmap, integral_map hvγ hFu]
    rfl
  rw [h1, integral_prod _ hint']
  have hg : AEStronglyMeasurable (fun x => ∫ w, F x w ∂(μ.map γ)) (μ.map v) :=
    (StronglyMeasurable.integral_prod_right (ν := μ.map γ) (f := F) hF).aestronglyMeasurable
  simp only [Function.uncurry_apply_pair]
  rw [integral_map hv hg]

end ACL

end HRS.MC.E213U16

end

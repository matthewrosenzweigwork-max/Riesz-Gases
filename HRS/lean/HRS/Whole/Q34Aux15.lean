import HRS.Whole.Q34Aux14

/-!
# Packet Q34, helper file 15: the integral operator as a bounded operator on `L²(ν)`
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric InnerProductSpace
open scoped ENNReal NNReal

namespace HRS.Whole.Q34

variable {d : ℕ}

/-- The standing hypotheses of the convolution lemma. -/
structure Q34Hyp (d : ℕ) (s : ℝ) (ρ : Euc d → ℝ) (M : ℝ) : Prop where
  hd : 1 ≤ d
  hs0 : 0 < s
  hsd : s < d
  hρ : IsProbDensity ρ
  hM : ∀ x, ρ x ≤ M

theorem lp_inner {ν : Measure (Euc d)} (U V : Lp ℝ 2 ν) :
    inner ℝ U V = ∫ x, U x * V x ∂ν := by
  rw [L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [mul_comm]

theorem lp_norm_sq {ν : Measure (Euc d)} (U : Lp ℝ 2 ν) :
    ‖U‖ ^ 2 = ∫ x, (U x) ^ 2 ∂ν := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [sq]

/-- A measurable representative of an `L²` class. -/
def mrep {ν : Measure (Euc d)} (U : Lp ℝ 2 ν) : Euc d → ℝ :=
  (Lp.aestronglyMeasurable U).mk U

theorem mrep_measurable {ν : Measure (Euc d)} (U : Lp ℝ 2 ν) : Measurable (mrep U) :=
  (Lp.aestronglyMeasurable U).stronglyMeasurable_mk.measurable

theorem mrep_ae {ν : Measure (Euc d)} (U : Lp ℝ 2 ν) : (U : Euc d → ℝ) =ᵐ[ν] mrep U :=
  (Lp.aestronglyMeasurable U).ae_eq_mk

theorem mrep_memLp {ν : Measure (Euc d)} (U : Lp ℝ 2 ν) : MemLp (mrep U) 2 ν :=
  (Lp.memLp U).ae_eq (mrep_ae U)

section Op

variable {s : ℝ} {ρ : Euc d → ℝ} {M : ℝ}

/-- The integral operator on `L²(ν)`, on classes. -/
def Top (h : Q34Hyp d s ρ M) (U : Lp ℝ 2 (withDensityReal ρ)) : Lp ℝ 2 (withDensityReal ρ) :=
  (tk_memLp h.hd h.hs0 h.hsd h.hρ h.hM (mrep_measurable U) (mrep_memLp U)).1.toLp
    (Tk s (withDensityReal ρ) (mrep U))

theorem top_ae (h : Q34Hyp d s ρ M) (U : Lp ℝ 2 (withDensityReal ρ)) :
    (Top h U : Euc d → ℝ) =ᵐ[withDensityReal ρ] Tk s (withDensityReal ρ) (U : Euc d → ℝ) := by
  have h1 := MemLp.coeFn_toLp
    (tk_memLp h.hd h.hs0 h.hsd h.hρ h.hM (mrep_measurable U) (mrep_memLp U)).1
  rw [tk_congr_ae (mrep_ae U)]
  exact h1

theorem top_add (h : Q34Hyp d s ρ M) (U V : Lp ℝ 2 (withDensityReal ρ)) :
    Top h (U + V) = Top h U + Top h V := by
  refine Lp.ext ?_
  have hUV : ((U + V : Lp ℝ 2 (withDensityReal ρ)) : Euc d → ℝ) =ᵐ[withDensityReal ρ]
      mrep U + mrep V := by
    filter_upwards [Lp.coeFn_add U V, mrep_ae U, mrep_ae V] with x h1 h2 h3
    rw [h1, Pi.add_apply, Pi.add_apply, h2, h3]
  have hadd := tk_add_ae h.hd h.hs0 h.hsd h.hρ h.hM (mrep_measurable U) (mrep_measurable V)
    (mrep_memLp U) (mrep_memLp V)
  have e1 := tk_congr_ae (s := s) hUV
  have e2 := tk_congr_ae (s := s) (mrep_ae U)
  have e3 := tk_congr_ae (s := s) (mrep_ae V)
  filter_upwards [top_ae h (U + V), Lp.coeFn_add (Top h U) (Top h V), top_ae h U, top_ae h V, hadd]
    with x h1 h2 h3 h4 h5
  rw [h2, Pi.add_apply, h1, e1, h5, Pi.add_apply, h3, h4, e2, e3]

theorem top_smul (h : Q34Hyp d s ρ M) (c : ℝ) (U : Lp ℝ 2 (withDensityReal ρ)) :
    Top h (c • U) = c • Top h U := by
  refine Lp.ext ?_
  have hU : ((c • U : Lp ℝ 2 (withDensityReal ρ)) : Euc d → ℝ) =ᵐ[withDensityReal ρ]
      c • mrep U := by
    filter_upwards [Lp.coeFn_smul c U, mrep_ae U] with x h1 h2
    rw [h1, Pi.smul_apply, Pi.smul_apply, h2]
  have e1 := tk_congr_ae (s := s) hU
  have e2 := tk_congr_ae (s := s) (mrep_ae U)
  filter_upwards [top_ae h (c • U), Lp.coeFn_smul c (Top h U), top_ae h U] with x h1 h2 h3
  rw [h2, Pi.smul_apply, h1, e1, tk_smul, Pi.smul_apply, h3, e2]

theorem top_norm_le (h : Q34Hyp d s ρ M) (U : Lp ℝ 2 (withDensityReal ρ)) :
    ‖Top h U‖ ≤ Mg d s M * ‖U‖ := by
  have hM0 : 0 ≤ M := (h.hρ.nonneg 0).trans (h.hM 0)
  have hMg0 := Mg_nonneg h.hd h.hsd hM0
  have hb := (tk_memLp h.hd h.hs0 h.hsd h.hρ h.hM (mrep_measurable U) (mrep_memLp U)).2
  have e1 : ‖Top h U‖ ^ 2 = ∫ x, Tk s (withDensityReal ρ) (mrep U) x ^ 2 ∂(withDensityReal ρ) := by
    rw [lp_norm_sq]
    refine integral_congr_ae ?_
    filter_upwards [top_ae h U] with x hx
    rw [hx, tk_congr_ae (mrep_ae U)]
  have e2 : ‖U‖ ^ 2 = ∫ x, mrep U x ^ 2 ∂(withDensityReal ρ) := by
    rw [lp_norm_sq]
    refine integral_congr_ae ?_
    filter_upwards [mrep_ae U] with x hx
    rw [hx]
  have : ‖Top h U‖ ^ 2 ≤ (Mg d s M * ‖U‖) ^ 2 := by
    rw [e1, mul_pow, e2]; exact hb
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hMg0 (norm_nonneg _))).1 this



theorem top_inner_ae (h : Q34Hyp d s ρ M) (U V : Lp ℝ 2 (withDensityReal ρ)) :
    inner ℝ (Top h U) V =
      ∫ x, Tk s (withDensityReal ρ) (mrep U) x * mrep V x ∂(withDensityReal ρ) := by
  rw [lp_inner]
  refine integral_congr_ae ?_
  filter_upwards [top_ae h U, mrep_ae V] with x h1 h2
  rw [h1, h2, tk_congr_ae (mrep_ae U)]

theorem top_symm (h : Q34Hyp d s ρ M) (U V : Lp ℝ 2 (withDensityReal ρ)) :
    inner ℝ (Top h U) V = inner ℝ U (Top h V) := by
  rw [top_inner_ae h U V, real_inner_comm, top_inner_ae h V U,
    tk_symm h.hd h.hs0 h.hsd h.hρ h.hM (mrep_measurable U) (mrep_measurable V)
      (mrep_memLp U) (mrep_memLp V)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  ring

theorem top_pos (h : Q34Hyp d s ρ M) (U : Lp ℝ 2 (withDensityReal ρ)) :
    0 ≤ inner ℝ (Top h U) U := by
  rw [top_inner_ae h U U]
  have := tk_pos h.hd h.hs0 h.hsd h.hρ h.hM (mrep_measurable U) (mrep_memLp U)
  refine this.trans_eq ?_
  refine integral_congr_ae ?_
  filter_upwards [mrep_ae U] with x hx
  rfl

/-- The integral operator as a continuous linear map on `L²(ν)`. -/
def TopL (h : Q34Hyp d s ρ M) :
    Lp ℝ 2 (withDensityReal ρ) →L[ℝ] Lp ℝ 2 (withDensityReal ρ) :=
  LinearMap.mkContinuous
    { toFun := Top h
      map_add' := top_add h
      map_smul' := fun c U => top_smul h c U } (Mg d s M) (top_norm_le h)

theorem topL_apply (h : Q34Hyp d s ρ M) (U : Lp ℝ 2 (withDensityReal ρ)) :
    TopL h U = Top h U := rfl

end Op

end HRS.Whole.Q34

import HRS.MS.SA16Y3Ex2
import HRS.MS.SA16EvolDefs

/-!
# S.A.16 (SA16Y3) Ex3: cut-off mollifier on `L^p` classes (SA16S item (iii), step (c) ingredients)

`sa16y3_cutmol_congr`: `cutmol n` depends only on the a.e.-class of its argument.
`sa16y3_cutmol_eLp`: `‖cutmol n f‖_{L^p} ≤ B ‖f‖_{L^p}` for every a.e.-strongly measurable `f`,
with `B` the uniform sup bound of the cut-offs (`sa16y3_cut_bound`, order `0`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal ContDiff Pointwise

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Q Phase2SA16Evolution

variable {d : ℕ}

lemma sa16y3_cutmol_congr (n : ℕ) {f g : EuclideanSpace ℝ (Fin d) → ℝ} (h : f =ᵐ[volume] g) :
    sa16y3_cutmol d n f = sa16y3_cutmol d n g := by
  funext x
  unfold sa16y3_cutmol sa16q_mol sa16j_conv
  refine integral_congr_ae ?_
  have hz := ((volume : Measure (EuclideanSpace ℝ (Fin d))).measurePreserving_sub_left x).quasiMeasurePreserving.ae h
  filter_upwards [hz] with z hz
  simp only [hz]

lemma sa16y3_cutmol_eLp {p : ℝ} (hp : 1 ≤ p) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ n : ℕ, ∀ x : EuclideanSpace ℝ (Fin d),
    ‖sa16y3_cut d n x‖ ≤ B) (n : ℕ) {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : AEStronglyMeasurable f volume) :
    eLpNorm (sa16y3_cutmol d n f) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal B * eLpNorm f (ENNReal.ofReal p) volume := by
  set f' := hf.mk f with hf'
  have hfm : Measurable f' := hf.stronglyMeasurable_mk.measurable
  have hff : f =ᵐ[volume] f' := hf.ae_eq_mk
  rw [sa16y3_cutmol_congr n hff, eLpNorm_congr_ae hff]
  have hχm : Measurable (fun y => sa16y3_cut d n y * f' y) :=
    ((sa16j_chi_contDiff d _).continuous.measurable).mul hfm
  have hY := sa16y3_young_eLp hp (sa16y_rho d n) (fun y => sa16y3_cut d n y * f' y)
    (sa16y_rho_smooth n).continuous.measurable hχm
  have hlin : (∫⁻ y, ‖sa16y_rho d n y‖ₑ) ≤ 1 := sa16y3_rho_lintegral n
  have hχ : eLpNorm (fun y => sa16y3_cut d n y * f' y) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal B * eLpNorm f' (ENNReal.ofReal p) volume := by
    have hm : AEStronglyMeasurable (fun y => sa16y3_cut d n y * f' y) volume :=
      hχm.aestronglyMeasurable
    calc eLpNorm (fun y => sa16y3_cut d n y * f' y) (ENNReal.ofReal p) volume
        ≤ eLpNorm (fun y => B * ‖f' y‖) (ENNReal.ofReal p) volume :=
          eLpNorm_mono_real hm (fun y => by
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_right (hB n y) (norm_nonneg (f' y)))
      _ = ENNReal.ofReal B * eLpNorm f' (ENNReal.ofReal p) volume := by
          have h : (fun y => B * ‖f' y‖) = B • (fun y => ‖f' y‖) := by
            funext y; simp [smul_eq_mul]
          rw [h, eLpNorm_const_smul, Real.enorm_eq_ofReal hB0, eLpNorm_norm f' hfm.aestronglyMeasurable]
  unfold sa16y3_cutmol
  exact hY.trans (le_trans (mul_le_mul' hlin le_rfl) (by simpa using hχ))


/-- base case of the zeroth-component identity: on `Jcc`, `wrep (T J) = cutmol (wrep J)` a.e. -/
theorem sa16y3_T_wrep_cc {p : ℝ} [Fact (2 ≤ p)] (m n : ℕ)
    (T : WmpSpace d m p →L[ℝ] WmpSpace d m p)
    (hTJ : ∀ ψ : ccSub d, T (sa16r_Jcc d m p ψ) = sa16r_J d m p (sa16y3_Lop m p n ψ))
    (ψ : ccSub d) :
    wrep d m p (T (sa16r_Jcc d m p ψ)) =ᵐ[volume] sa16y3_cutmol d n (wrep d m p (sa16r_Jcc d m p ψ)) := by
  have hw : wrep d m p (sa16r_Jcc d m p ψ) =ᵐ[volume] ψ.1 := by
    rw [sa16r_Jcc_eq]
    exact sa16r_cc_elt_wrep (p := p) ψ.2 m
  have hc : sa16y3_cutmol d n (wrep d m p (sa16r_Jcc d m p ψ)) = sa16y3_cutmol d n ψ.1 :=
    sa16y3_cutmol_congr n hw
  rw [hc, hTJ ψ]
  exact sa16r_J_spec d m p (sa16y3_Lop m p n ψ)

end HRS.Whole.AppendixA.Phase2SA16R

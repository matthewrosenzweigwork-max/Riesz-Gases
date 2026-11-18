import HRS.MS.SA16Y3Ex3

/-!
# S.A.16 (SA16Y3) Ex4: cut-off mollifier on `L^p` (SA16S item (iii), steps (c1)-(c2))

`sa16y3_cutmol_eq_int`: `cutmol n f x = ∫ z, (ρ z χ(x-z)) f(x-z)`.
`sa16y3_cutmol_integrable`: this integrand is integrable for `f ∈ L^p` (Hölder with the compactly supported factor).
`sa16y3_cutmol_sub`: `cutmol n (f - g) = cutmol n f - cutmol n g` for `f, g ∈ L^p`.
`sa16y3_cutmol_aesm`: `cutmol n f` is a.e. strongly measurable.
`sa16y3_wrep_eLp`: `‖wrep H‖_{L^p} ≤ ‖H‖` for `H ∈ WmpSpace`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal ContDiff Pointwise

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Q Phase2SA16Evolution

variable {d : ℕ}

lemma sa16y3_cutmol_eq_int (n : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    sa16y3_cutmol d n f x = ∫ z, (sa16y_rho d n z * sa16y3_cut d n (x - z)) * f (x - z) := by
  unfold sa16y3_cutmol sa16q_mol sa16j_conv
  congr 1
  funext z
  ring

lemma sa16y3_cutmol_integrable {p : ℝ} (hp : 1 < p) {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) volume) (n : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun z => (sa16y_rho d n z * sa16y3_cut d n (x - z)) * f (x - z)) volume := by
  have hχ : HasCompactSupport (fun z => sa16y3_cut d n (x - z)) :=
    (sa16j_chi_support d (R := (n : ℝ) + 1) (by positivity)).comp_homeomorph (Homeomorph.subLeft x)
  have hcs : HasCompactSupport (fun z => sa16y_rho d n z * sa16y3_cut d n (x - z)) := hχ.mul_left
  have hcont : Continuous (fun z => sa16y_rho d n z * sa16y3_cut d n (x - z)) :=
    (sa16y_rho_smooth n).continuous.mul ((sa16j_chi_contDiff d _).continuous.comp
      (continuous_const.sub continuous_id))
  have hp1 : (1 : ENNReal) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp.le
  haveI : (ENNReal.ofReal p).HolderTriple (ENNReal.conjExponent (ENNReal.ofReal p)) 1 :=
    ENNReal.HolderConjugate.conjExponent hp1
  have hg : MemLp (fun z => sa16y_rho d n z * sa16y3_cut d n (x - z))
      (ENNReal.conjExponent (ENNReal.ofReal p)) volume :=
    hcont.memLp_of_hasCompactSupport hcs
  have hf' : MemLp (fun z => f (x - z)) (ENNReal.ofReal p) volume :=
    hf.comp_measurePreserving
      ((volume : Measure (EuclideanSpace ℝ (Fin d))).measurePreserving_sub_left x)
  have hI : Integrable ((fun z => f (x - z)) * (fun z => sa16y_rho d n z * sa16y3_cut d n (x - z)))
      volume := hf'.integrable_mul hg
  exact hI.congr (Eventually.of_forall fun z => by simp [Pi.mul_apply, mul_comm])

lemma sa16y3_cutmol_sub {p : ℝ} (hp : 1 < p) {f g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) volume) (hg : MemLp g (ENNReal.ofReal p) volume) (n : ℕ) :
    sa16y3_cutmol d n (f - g) = fun x => sa16y3_cutmol d n f x - sa16y3_cutmol d n g x := by
  funext x
  rw [sa16y3_cutmol_eq_int, sa16y3_cutmol_eq_int, sa16y3_cutmol_eq_int,
    ← integral_sub (sa16y3_cutmol_integrable hp hf n x) (sa16y3_cutmol_integrable hp hg n x)]
  congr 1
  funext z
  simp only [Pi.sub_apply]
  ring

lemma sa16y3_cutmol_aesm {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : AEStronglyMeasurable f volume) (n : ℕ) :
    AEStronglyMeasurable (sa16y3_cutmol d n f) volume := by
  have hm : Measurable (hf.mk f) := hf.stronglyMeasurable_mk.measurable
  rw [sa16y3_cutmol_congr n hf.ae_eq_mk]
  have hjoint : StronglyMeasurable (fun q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      sa16y_rho d n q.2 * (sa16y3_cut d n (q.1 - q.2) * hf.mk f (q.1 - q.2))) := by
    refine Measurable.stronglyMeasurable ?_
    exact ((sa16y_rho_smooth n).continuous.measurable.comp measurable_snd).mul
      (((sa16j_chi_contDiff d _).continuous.measurable.comp (measurable_fst.sub measurable_snd)).mul
        (hm.comp (measurable_fst.sub measurable_snd)))
  exact (hjoint.integral_prod_right).aestronglyMeasurable

lemma sa16y3_wrep_eLp {p : ℝ} [Fact (2 ≤ p)] {m : ℕ} (H : WmpSpace d m p) :
    eLpNorm (fun x => wrep d m p H x) (ENNReal.ofReal p) volume ≤ ENNReal.ofReal ‖H‖ := by
  have hcoe : MemLp (((H : WLp d m p)) : EuclideanSpace ℝ (Fin d) → (WIndex d m → ℝ))
      (ENNReal.ofReal p) volume := Lp.memLp (H : WLp d m p)
  have hfin := hcoe.eLpNorm_lt_top.ne
  have hn : ‖H‖ = (eLpNorm (((H : WLp d m p)) : EuclideanSpace ℝ (Fin d) → (WIndex d m → ℝ))
      (ENNReal.ofReal p) volume).toReal := Lp.norm_def (H : WLp d m p)
  have hdiff : ENNReal.ofReal ‖H‖ = eLpNorm (((H : WLp d m p)) : EuclideanSpace ℝ (Fin d) → (WIndex d m → ℝ))
      (ENNReal.ofReal p) volume := by
    rw [hn, ENNReal.ofReal_toReal hfin]
  have hwm : AEStronglyMeasurable (fun x => wrep d m p H x) volume :=
    (continuous_apply (wZero d m)).comp_aestronglyMeasurable (Lp.aestronglyMeasurable (H : WLp d m p))
  calc eLpNorm (fun x => wrep d m p H x) (ENNReal.ofReal p) volume
      ≤ eLpNorm (fun x => ‖((H : WLp d m p) : EuclideanSpace ℝ (Fin d) → (WIndex d m → ℝ)) x‖)
          (ENNReal.ofReal p) volume :=
        eLpNorm_mono_real hwm (fun x => norm_le_pi_norm
          (((H : WLp d m p) : EuclideanSpace ℝ (Fin d) → (WIndex d m → ℝ)) x) (wZero d m))
    _ = eLpNorm (((H : WLp d m p)) : EuclideanSpace ℝ (Fin d) → (WIndex d m → ℝ))
          (ENNReal.ofReal p) volume := eLpNorm_norm _ hcoe.aestronglyMeasurable
    _ = ENNReal.ofReal ‖H‖ := hdiff.symm

end HRS.Whole.AppendixA.Phase2SA16R

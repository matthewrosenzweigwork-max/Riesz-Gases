import HRS.MS.SA16U3K10b

/-!
# S.A.16 K10, part (c): the symmetric identity (worker SA16U3)

`∫ f a T g + ∫ g a T f = -∫ f (T(a g) - a T g)` for Schwartz `f, g` and a bounded continuous `a`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16Cutoff
open HRS HRS.Whole HRS.Whole.AppendixA HRS.CZ.Pv HRS.CZ.ElemA Phase2SA16

section K10c
variable {d : ℕ}

/-- continuous, integrable and bounded -/
def sa16u3_Good (f : Euc d → ℝ) : Prop :=
  Continuous f ∧ Integrable f ∧ ∃ B : ℝ, ∀ x, |f x| ≤ B

lemma sa16u3_good_schwartz (S : SchwartzMap (Euc d) ℝ) : sa16u3_Good (⇑S) :=
  ⟨S.continuous, S.integrable, sa16j_schwartz_bdd S⟩

lemma sa16u3_good_mul {a f : Euc d → ℝ} (ha : Continuous a) {Ba : ℝ} (hBa : ∀ x, |a x| ≤ Ba)
    (hf : sa16u3_Good f) : sa16u3_Good (fun x => a x * f x) := by
  obtain ⟨hc, hi, B, hB⟩ := hf
  refine ⟨ha.mul hc, hi.bdd_mul ha.aestronglyMeasurable (Eventually.of_forall fun x => by
    simpa [Real.norm_eq_abs] using hBa x), Ba * B, fun x => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hBa x) (hB x) (abs_nonneg _) ((abs_nonneg _).trans (hBa x))

lemma sa16u3_T_aesm {θ δ : ℝ} (i : Fin d) {u : Euc d → ℝ} (hu : Continuous u) :
    AEStronglyMeasurable (fun x => spliceOdd d θ δ i u x) volume :=
  sa16k5_conv_aesm (sa16k5_ks_meas θ δ i) hu

lemma sa16u3_T_bdd (hd : 1 ≤ d) {θ δ : ℝ} (hθ1 : 1 < θ) (hδ : 0 < δ) (i : Fin d)
    {u : Euc d → ℝ} (hu : sa16u3_Good u) :
    ∃ B : ℝ, ∀ x, |spliceOdd d θ δ i u x| ≤ B := by
  obtain ⟨-, -, B, hB⟩ := hu
  exact ⟨_, fun x => sa16u3_T_bound hd hθ1 hδ i hB x⟩

lemma sa16u3_int_mul3 {f a t : Euc d → ℝ} (hf : Integrable f) (ha : AEStronglyMeasurable a volume)
    (hat : ∃ B : ℝ, ∀ x, |a x| ≤ B) (ht : AEStronglyMeasurable t volume)
    (htb : ∃ B : ℝ, ∀ x, |t x| ≤ B) : Integrable (fun x => f x * a x * t x) := by
  obtain ⟨Ba, hBa⟩ := hat
  obtain ⟨Bt, hBt⟩ := htb
  refine Integrable.mul_bdd (c := Bt) ?_ ht (Eventually.of_forall fun x => by
    simpa [Real.norm_eq_abs] using hBt x)
  exact hf.mul_bdd (c := Ba) ha (Eventually.of_forall fun x => by
    simpa [Real.norm_eq_abs] using hBa x)

/-- the symmetric part of the gradient pairing -/
lemma sa16u3_sym_identity (hd : 1 ≤ d) {θ δ : ℝ} (hθ1 : 1 < θ) (hδ : 0 < δ) (i : Fin d)
    {a : Euc d → ℝ} (ha : Continuous a) {Ba : ℝ} (hBa : ∀ x, |a x| ≤ Ba)
    (f g : SchwartzMap (Euc d) ℝ) :
    (∫ x, f x * a x * spliceOdd d θ δ i g x) + (∫ x, g x * a x * spliceOdd d θ δ i f x) =
      - ∫ x, f x * (spliceOdd d θ δ i (fun y => a y * g y) x - a x * spliceOdd d θ δ i g x) := by
  have hf := sa16u3_good_schwartz f
  have hg := sa16u3_good_schwartz g
  have hag := sa16u3_good_mul ha hBa hg
  have hsk := sa16u3_skew hd hθ1 hδ i (f := fun y => a y * g y) (g := f) hag.1 hf.1 hag.2.1 hf.2.1
    (Bf := hag.2.2.choose) (Bg := hf.2.2.choose) hag.2.2.choose_spec hf.2.2.choose_spec
  have iTg := sa16u3_T_aesm (θ := θ) (δ := δ) i hg.1
  have iTf := sa16u3_T_aesm (θ := θ) (δ := δ) i hf.1
  have iTag := sa16u3_T_aesm (θ := θ) (δ := δ) i hag.1
  have bTg := sa16u3_T_bdd hd hθ1 hδ i hg
  have bTf := sa16u3_T_bdd hd hθ1 hδ i hf
  have bTag := sa16u3_T_bdd hd hθ1 hδ i hag
  have e2 : ∫ x, g x * a x * spliceOdd d θ δ i f x =
      - ∫ x, spliceOdd d θ δ i (fun y => a y * g y) x * f x := by
    rw [← hsk]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    ring
  have i1 : Integrable (fun x => f x * a x * spliceOdd d θ δ i g x) :=
    sa16u3_int_mul3 hf.2.1 ha.aestronglyMeasurable ⟨Ba, hBa⟩ iTg bTg
  have i2 : Integrable (fun x => f x * spliceOdd d θ δ i (fun y => a y * g y) x) := by
    have := Integrable.mul_bdd (c := bTag.choose) hf.2.1 iTag
      (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using bTag.choose_spec x)
    exact this
  have i3 : Integrable (fun x => spliceOdd d θ δ i (fun y => a y * g y) x * f x) :=
    i2.congr (Eventually.of_forall fun x => mul_comm _ _)
  have h : ∫ x, f x * (spliceOdd d θ δ i (fun y => a y * g y) x - a x * spliceOdd d θ δ i g x) =
      (∫ x, spliceOdd d θ δ i (fun y => a y * g y) x * f x) -
        ∫ x, f x * a x * spliceOdd d θ δ i g x := by
    rw [← integral_sub i3 i1]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    ring
  rw [e2, h]
  ring

end K10c
end HRS.Whole.AppendixA.Phase2SA16Cutoff

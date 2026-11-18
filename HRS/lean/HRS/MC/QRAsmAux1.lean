import HRS.MC.QRVocab
import HRS.MC.QRPGaussErAux1

/-!
# QRAsm, auxiliary file 1: generic `L^p` estimates (Hölder, finite Wick sections, Minkowski over Fourier modes)
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace HRS.MC.QRSpec.Asm

variable {Ω : Type} [MeasurableSpace Ω]

/-- The finite Wick section of a family `X` with matrix `A` (the expression of `wickSection`). -/
def asmSec {ι : Type*} (P : Measure Ω) (A : ι → ι → ℝ) (X : ι → Ω → ℝ) (F : Finset ι) (ω : Ω) : ℝ :=
  (1 / 2) * ∑ a ∈ F, ∑ b ∈ F, A a b * (X a ω * X b ω - ∫ ω', X a ω' * X b ω' ∂P)

lemma asm_holderTriple {p : ℝ} (hp : 0 < p) :
    ENNReal.HolderTriple (ENNReal.ofReal (2 * p)) (ENNReal.ofReal (2 * p)) (ENNReal.ofReal p) := by
  refine ⟨?_⟩
  have h2 : (0:ℝ) < 2 * p := by positivity
  rw [← ENNReal.ofReal_inv_of_pos h2, ← ENNReal.ofReal_inv_of_pos hp,
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  field_simp
  ring

lemma asm_holder {P : Measure Ω} {f g : Ω → ℝ} (hf : AEStronglyMeasurable f P)
    (hg : AEStronglyMeasurable g P) {p a b : ℝ} (hp : 0 < p) (ha : 0 ≤ a)
    (hf' : eLpNorm f (ENNReal.ofReal (2 * p)) P ≤ ENNReal.ofReal a)
    (hg' : eLpNorm g (ENNReal.ofReal (2 * p)) P ≤ ENNReal.ofReal b) :
    eLpNorm (fun ω => f ω * g ω) (ENNReal.ofReal p) P ≤ ENNReal.ofReal (a * b) := by
  have := asm_holderTriple hp
  have h := eLpNorm_smul_le_mul_eLpNorm (μ := P) (p := ENNReal.ofReal (2 * p))
    (q := ENNReal.ofReal (2 * p)) (r := ENNReal.ofReal p) hf hg
  simp only [smul_eq_mul] at h
  refine (h.trans (mul_le_mul' hf' hg')).trans ?_
  rw [ENNReal.ofReal_mul ha]

lemma asm_abs_integral_le {P : Measure Ω} [IsProbabilityMeasure P] {g : Ω → ℝ} {p : ℝ}
    (hp : 1 ≤ p) (hg : AEStronglyMeasurable g P) :
    ENNReal.ofReal |∫ ω, g ω ∂P| ≤ eLpNorm g (ENNReal.ofReal p) P := by
  have h1 : ENNReal.ofReal |∫ ω, g ω ∂P| ≤ eLpNorm g 1 P := by
    rw [eLpNorm_one_eq_lintegral_enorm hg]
    have := enorm_integral_le_lintegral_enorm (μ := P) g
    rwa [Real.enorm_eq_ofReal_abs] at this
  refine h1.trans (eLpNorm_le_eLpNorm_of_exponent_le ?_)
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal hp

lemma asm_eLpNorm_sum_le {P : Measure Ω} {ι : Type*} (s : Finset ι) (f : ι → Ω → ℝ)
    {q : ℝ≥0∞} (hq : 1 ≤ q) :
    eLpNorm (fun ω => ∑ i ∈ s, f i ω) q P ≤ ∑ i ∈ s, eLpNorm (f i) q P := by
  have e : (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, f i := by
    funext ω; simp [Finset.sum_apply]
  rw [e]
  exact eLpNorm_sum_le hq

/-- `X_aX_b - Y_aY_b`. -/
def asmG {ι : Type*} (X Y : ι → Ω → ℝ) (a b : ι) (ω : Ω) : ℝ := X a ω * X b ω - Y a ω * Y b ω

lemma asm_G_bound {P : Measure Ω} {ι : Type*} (X Y : ι → Ω → ℝ) {p : ℝ} (hp : 1 ≤ p)
    (hXm : ∀ a, AEStronglyMeasurable (X a) P) (hYm : ∀ a, AEStronglyMeasurable (Y a) P)
    (δ ξ ζ : ι → ℝ) (hδ0 : ∀ a, 0 ≤ δ a) (hξ0 : ∀ a, 0 ≤ ξ a) (hζ0 : ∀ a, 0 ≤ ζ a)
    (hδ : ∀ a, eLpNorm (fun ω => X a ω - Y a ω) (ENNReal.ofReal (2 * p)) P ≤ ENNReal.ofReal (δ a))
    (hξ : ∀ a, eLpNorm (X a) (ENNReal.ofReal (2 * p)) P ≤ ENNReal.ofReal (ξ a))
    (hζ : ∀ a, eLpNorm (Y a) (ENNReal.ofReal (2 * p)) P ≤ ENNReal.ofReal (ζ a)) (a b : ι) :
    eLpNorm (asmG X Y a b) (ENNReal.ofReal p) P ≤ ENNReal.ofReal (δ a * ξ b + ζ a * δ b) := by
  have hp0 : 0 < p := by linarith
  have e : asmG X Y a b = fun ω => (X a ω - Y a ω) * X b ω + Y a ω * (X b ω - Y b ω) := by
    funext ω; simp only [asmG]; ring
  have h1 := asm_holder ((hXm a).sub (hYm a)) (hXm b) hp0 (hδ0 a) (hδ a) (hξ b)
  have h2 := asm_holder (hYm a) ((hXm b).sub (hYm b)) hp0 (hζ0 a) (hζ a) (hδ b)
  have h1p : 1 ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  rw [e]
  refine (eLpNorm_add_le (f := fun ω => (X a ω - Y a ω) * X b ω)
    (g := fun ω => Y a ω * (X b ω - Y b ω)) h1p).trans ?_
  rw [ENNReal.ofReal_add (mul_nonneg (hδ0 a) (hξ0 b)) (mul_nonneg (hζ0 a) (hδ0 b))]
  exact add_le_add h1 h2

lemma asm_sec_diff_bound {P : Measure Ω} [IsProbabilityMeasure P] {ι : Type*} (A : ι → ι → ℝ)
    (F : Finset ι) (X Y : ι → Ω → ℝ) {p : ℝ} (hp : 1 ≤ p)
    (hXm : ∀ a, AEStronglyMeasurable (X a) P) (hYm : ∀ a, AEStronglyMeasurable (Y a) P)
    (δ ξ ζ : ι → ℝ) (hδ0 : ∀ a, 0 ≤ δ a) (hξ0 : ∀ a, 0 ≤ ξ a) (hζ0 : ∀ a, 0 ≤ ζ a)
    (hδ : ∀ a, eLpNorm (fun ω => X a ω - Y a ω) (ENNReal.ofReal (2 * p)) P ≤ ENNReal.ofReal (δ a))
    (hξ : ∀ a, eLpNorm (X a) (ENNReal.ofReal (2 * p)) P ≤ ENNReal.ofReal (ξ a))
    (hζ : ∀ a, eLpNorm (Y a) (ENNReal.ofReal (2 * p)) P ≤ ENNReal.ofReal (ζ a)) :
    eLpNorm (fun ω => asmSec P A X F ω - asmSec P A Y F ω) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (∑ a ∈ F, ∑ b ∈ F, |A a b| * (δ a * ξ b + ζ a * δ b)) := by
  have hp0 : 0 < p := by linarith
  have h1p : 1 ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have hG := asm_G_bound X Y hp hXm hYm δ ξ ζ hδ0 hξ0 hζ0 hδ hξ hζ
  have hGm : ∀ a b, AEStronglyMeasurable (asmG X Y a b) P := fun a b =>
    ((hXm a).mul (hXm b)).sub ((hYm a).mul (hYm b))
  have hint : ∀ (Z : ι → Ω → ℝ) (ζ' : ι → ℝ), (∀ a, AEStronglyMeasurable (Z a) P) → (∀ a, 0 ≤ ζ' a) →
      (∀ a, eLpNorm (Z a) (ENNReal.ofReal (2 * p)) P ≤ ENNReal.ofReal (ζ' a)) →
      ∀ a b, Integrable (fun ω => Z a ω * Z b ω) P := by
    intro Z ζ' hZm hζ0' hZ a b
    have h := asm_holder (hZm a) (hZm b) hp0 (hζ0' a) (hZ a) (hZ b)
    have hmem : MemLp (fun ω => Z a ω * Z b ω) (ENNReal.ofReal p) P :=
      lt_of_le_of_lt h ENNReal.ofReal_lt_top
    exact hmem.integrable h1p
  have hintG : ∀ a b, ∫ ω', asmG X Y a b ω' ∂P =
      (∫ ω', X a ω' * X b ω' ∂P) - ∫ ω', Y a ω' * Y b ω' ∂P := fun a b =>
    integral_sub (hint X ξ hXm hξ0 hξ a b) (hint Y ζ hYm hζ0 hζ a b)
  have key : (fun ω => asmSec P A X F ω - asmSec P A Y F ω) = fun ω => ∑ a ∈ F, ∑ b ∈ F,
      ((1 / 2 * A a b) • (asmG X Y a b ω - ∫ ω', asmG X Y a b ω' ∂P)) := by
    funext ω
    simp only [asmSec]
    rw [← mul_sub, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hintG, smul_eq_mul]
    simp only [asmG]
    ring
  have hmeas : ∀ a b, AEStronglyMeasurable
      (fun ω => (1 / 2 * A a b) • (asmG X Y a b ω - ∫ ω', asmG X Y a b ω' ∂P)) P := fun a b =>
    (((hGm a b).sub (aestronglyMeasurable_const (b := ∫ ω', asmG X Y a b ω' ∂P))).const_smul
      (1 / 2 * A a b) :)
  have hterm : ∀ a b, eLpNorm (fun ω => (1 / 2 * A a b) • (asmG X Y a b ω - ∫ ω', asmG X Y a b ω' ∂P))
      (ENNReal.ofReal p) P ≤ ENNReal.ofReal (|A a b| * (δ a * ξ b + ζ a * δ b)) := by
    intro a b
    have hc := eLpNorm_const_smul (1 / 2 * A a b)
      (fun ω => asmG X Y a b ω - ∫ ω', asmG X Y a b ω' ∂P) (ENNReal.ofReal p) P
    have hc' : eLpNorm (fun ω => (1 / 2 * A a b) • (asmG X Y a b ω - ∫ ω', asmG X Y a b ω' ∂P))
        (ENNReal.ofReal p) P = ‖(1 / 2 * A a b)‖ₑ *
        eLpNorm (fun ω => asmG X Y a b ω - ∫ ω', asmG X Y a b ω' ∂P) (ENNReal.ofReal p) P := hc
    rw [hc']
    have hsub := eLpNorm_sub_le (μ := P) (f := asmG X Y a b)
      (g := fun _ : Ω => ∫ ω', asmG X Y a b ω' ∂P) h1p
    have hconst : eLpNorm (fun _ : Ω => ∫ ω', asmG X Y a b ω' ∂P) (ENNReal.ofReal p) P =
        ENNReal.ofReal |∫ ω', asmG X Y a b ω' ∂P| := by
      rw [eLpNorm_const _ (by simpa using hp0) (IsProbabilityMeasure.ne_zero P)]
      simp [Real.enorm_eq_ofReal_abs]
    rw [hconst] at hsub
    have hB : 0 ≤ δ a * ξ b + ζ a * δ b :=
      add_nonneg (mul_nonneg (hδ0 a) (hξ0 b)) (mul_nonneg (hζ0 a) (hδ0 b))
    have h2 : eLpNorm (fun ω => asmG X Y a b ω - ∫ ω', asmG X Y a b ω' ∂P) (ENNReal.ofReal p) P ≤
        ENNReal.ofReal (2 * (δ a * ξ b + ζ a * δ b)) := by
      refine hsub.trans ?_
      have h3 := asm_abs_integral_le (P := P) hp (hGm a b)
      have h4 := hG a b
      calc _ ≤ ENNReal.ofReal (δ a * ξ b + ζ a * δ b) + ENNReal.ofReal (δ a * ξ b + ζ a * δ b) :=
            add_le_add h4 (h3.trans h4)
        _ = _ := by rw [← ENNReal.ofReal_add hB hB]; congr 1; ring
    refine (mul_le_mul' le_rfl h2).trans ?_
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul (abs_nonneg _)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
    ring
  rw [key]
  refine (asm_eLpNorm_sum_le F _ h1p).trans ?_
  have hin : ∀ a ∈ F, eLpNorm (fun ω => ∑ b ∈ F, (1 / 2 * A a b) •
      (asmG X Y a b ω - ∫ ω', asmG X Y a b ω' ∂P)) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (∑ b ∈ F, |A a b| * (δ a * ξ b + ζ a * δ b)) := by
    intro a _
    refine (asm_eLpNorm_sum_le F _ h1p).trans ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun b _ => mul_nonneg (abs_nonneg _)
      (add_nonneg (mul_nonneg (hδ0 a) (hξ0 b)) (mul_nonneg (hζ0 a) (hδ0 b))))]
    exact Finset.sum_le_sum fun b _ => hterm a b
  refine (Finset.sum_le_sum hin).trans ?_
  rw [ENNReal.ofReal_sum_of_nonneg (fun a _ => Finset.sum_nonneg fun b _ => mul_nonneg (abs_nonneg _)
      (add_nonneg (mul_nonneg (hδ0 a) (hξ0 b)) (mul_nonneg (hζ0 a) (hδ0 b))))]

end HRS.MC.QRSpec.Asm

end

import Mathlib
import HRS.MS.S111K4T1

/-!
# S11.1 / T03 (S11K4), small analytic tools: `L²` multiplication by bounded functions (for Pro `R26-T6.E04`)
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology

namespace HRS.MS.S111K4

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem k4_mul_memLp [IsFiniteMeasure μ] {a w : X → ℝ} {B : ℝ} (ha : MemLp a 2 μ)
    (hw : AEStronglyMeasurable w μ) (hB : ∀ᵐ x ∂μ, |w x| ≤ B) : MemLp (fun x => w x * a x) 2 μ := by
  refine ha.of_le_mul (c := B) (hw.mul ha.aestronglyMeasurable) ?_
  filter_upwards [hB] with x hx
  rw [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

theorem k4_mul_norm [IsFiniteMeasure μ] {a w : X → ℝ} {B : ℝ} (hB0 : 0 ≤ B) (ha : MemLp a 2 μ)
    (hw : AEStronglyMeasurable w μ) (hB : ∀ᵐ x ∂μ, |w x| ≤ B) :
    ‖(k4_mul_memLp ha hw hB).toLp (fun x => w x * a x)‖ ≤ B * ‖ha.toLp a‖ := by
  rw [Lp.norm_toLp, Lp.norm_toLp]
  have h1 : eLpNorm (fun x => w x * a x) 2 μ ≤ ENNReal.ofReal B * eLpNorm a 2 μ := by
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hw.mul ha.aestronglyMeasurable) ?_ 2
    filter_upwards [hB] with x hx
    simp only [Pi.mul_apply]
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
  have h2 : eLpNorm a 2 μ ≠ ⊤ := ha.eLpNorm_ne_top
  calc (eLpNorm (fun x => w x * a x) 2 μ).toReal ≤ (ENNReal.ofReal B * eLpNorm a 2 μ).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h2) h1
    _ = B * (eLpNorm a 2 μ).toReal := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hB0]

theorem k4_inner_toLp {a b : X → ℝ} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    inner ℝ (ha.toLp a) (hb.toLp b) = ∫ x, a x * b x ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with x h1 h2
  rw [h1, h2]
  simp [mul_comm]


open Classical in
/-- The `L²(μ)` class of `f` (`0` if `f ∉ L²`). -/
def k4_toL (μ : Measure X) (f : X → ℝ) : Lp ℝ 2 μ := if h : MemLp f 2 μ then h.toLp f else 0

theorem k4_toL_eq {f : X → ℝ} (hf : MemLp f 2 μ) : k4_toL μ f = hf.toLp f := by
  unfold k4_toL; rw [dif_pos hf]

theorem k4_toL_ae {f : X → ℝ} (hf : MemLp f 2 μ) : (k4_toL μ f : X → ℝ) =ᵐ[μ] f := by
  rw [k4_toL_eq hf]; exact hf.coeFn_toLp

theorem k4_inner_toL {a b : X → ℝ} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    inner ℝ (k4_toL μ a) (k4_toL μ b) = ∫ x, a x * b x ∂μ := by
  rw [k4_toL_eq ha, k4_toL_eq hb]; exact k4_inner_toLp ha hb

theorem k4_toL_combo {a b : X → ℝ} (c : ℝ) (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    k4_toL μ (fun x => c * (a x - b x)) = c • (k4_toL μ a - k4_toL μ b) := by
  have hab : MemLp (fun x => a x - b x) 2 μ := ha.sub hb
  have hc : MemLp (fun x => c * (a x - b x)) 2 μ := hab.const_mul c
  rw [k4_toL_eq hc, k4_toL_eq ha, k4_toL_eq hb]
  apply Lp.ext
  filter_upwards [hc.coeFn_toLp, Lp.coeFn_smul c (ha.toLp a - hb.toLp b), Lp.coeFn_sub (ha.toLp a) (hb.toLp b),
    ha.coeFn_toLp, hb.coeFn_toLp] with x h1 h2 h3 h4 h5
  rw [h1, h2, Pi.smul_apply, h3, Pi.sub_apply, h4, h5]
  rfl

theorem k4_toL_sub {a b : X → ℝ} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    k4_toL μ (fun x => a x - b x) = k4_toL μ a - k4_toL μ b := by
  have := k4_toL_combo (μ := μ) 1 ha hb
  simpa using this

theorem k4_toL_add {a b : X → ℝ} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    k4_toL μ (fun x => a x + b x) = k4_toL μ a + k4_toL μ b := by
  have hs : MemLp (fun x => a x + b x) 2 μ := ha.add hb
  rw [k4_toL_eq hs, k4_toL_eq ha, k4_toL_eq hb]
  apply Lp.ext
  filter_upwards [hs.coeFn_toLp, Lp.coeFn_add (ha.toLp a) (hb.toLp b), ha.coeFn_toLp, hb.coeFn_toLp]
    with x h1 h2 h3 h4
  rw [h1, h2, Pi.add_apply, h3, h4]

/-- The difference of two products of bounded `L²` functions. -/
theorem k4_prod_diff_norm [IsFiniteMeasure μ] {a a' b b' : X → ℝ} {B : ℝ} (hB0 : 0 ≤ B)
    (ha : MemLp a 2 μ) (ha' : MemLp a' 2 μ) (hb : MemLp b 2 μ) (hb' : MemLp b' 2 μ)
    (hBa : ∀ᵐ x ∂μ, |a x| ≤ B) (hBb' : ∀ᵐ x ∂μ, |b' x| ≤ B) :
    ‖k4_toL μ (fun x => a' x * b' x) - k4_toL μ (fun x => a x * b x)‖ ≤
      B * ‖k4_toL μ a' - k4_toL μ a‖ + B * ‖k4_toL μ b' - k4_toL μ b‖ := by
  have hda : MemLp (fun x => a' x - a x) 2 μ := ha'.sub ha
  have hdb : MemLp (fun x => b' x - b x) 2 μ := hb'.sub hb
  have hm1 : MemLp (fun x => b' x * (a' x - a x)) 2 μ := k4_mul_memLp hda hb'.aestronglyMeasurable hBb'
  have hm2 : MemLp (fun x => a x * (b' x - b x)) 2 μ := k4_mul_memLp hdb ha.aestronglyMeasurable hBa
  have e : (fun x => a' x * b' x - a x * b x) = fun x => b' x * (a' x - a x) + a x * (b' x - b x) := by
    funext x; ring
  have hpa' : MemLp (fun x => a' x * b' x) 2 μ := by
    have := k4_mul_memLp ha' hb'.aestronglyMeasurable hBb'
    exact this.ae_eq (Filter.Eventually.of_forall fun x => by simp only [mul_comm])
  have hpa : MemLp (fun x => a x * b x) 2 μ := by
    have := k4_mul_memLp hb ha.aestronglyMeasurable hBa
    exact this.ae_eq (Filter.Eventually.of_forall fun x => by simp only [mul_comm])
  rw [← k4_toL_sub hpa' hpa, e, k4_toL_add hm1 hm2]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · have := k4_mul_norm hB0 hda hb'.aestronglyMeasurable hBb'
    rw [← k4_toL_eq hm1, ← k4_toL_eq hda, k4_toL_sub ha' ha] at this
    exact this
  · have := k4_mul_norm hB0 hdb ha.aestronglyMeasurable hBa
    rw [← k4_toL_eq hm2, ← k4_toL_eq hdb, k4_toL_sub hb' hb] at this
    exact this

end HRS.MS.S111K4

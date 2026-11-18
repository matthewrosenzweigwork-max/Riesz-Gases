import HRS.PDE.TorusFPLpSpec
import HRS.PDE.MovSpec2

/-!
# D3PHI glue, part 1: the exponent path `movT_pPath` is a `D3phiPath` and its gain is `d3phi_gain`
-/

noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
namespace HRS

/-- The profile `a ↦ 1/(1 - q e^{-a})` of the exponent path (`p = F(A)`, `A = c⁻¹∫L`). -/
def d3phi_F (q a : ℝ) : ℝ := 1 / (1 - q * Real.exp (-a))

theorem d3phi_F_hasDerivAt {q a : ℝ} (h : 1 - q * Real.exp (-a) ≠ 0) :
    HasDerivAt (d3phi_F q) (-(d3phi_F q a) * (d3phi_F q a - 1)) a := by
  have hg : HasDerivAt (fun a => 1 - q * Real.exp (-a)) (q * Real.exp (-a)) a := by
    have h1 := (hasDerivAt_neg a).exp
    have := ((h1.const_mul q).const_sub 1)
    convert this using 1; ring
  have := (hasDerivAt_const a (1 : ℝ)).div hg h
  unfold d3phi_F
  convert this using 1
  field_simp
  ring


theorem d3phi_movT_pPath_eq (c p₀ : ℝ) (L : ℝ → ℝ) (t : ℝ) :
    movT_pPath c p₀ L t = d3phi_F (1 - 1 / p₀) ((1 / c) * ∫ r in (0 : ℝ)..t, L r) := by
  simp [movT_pPath, d3phi_F, neg_mul]

theorem d3phi_F_bounds {p₀ a : ℝ} (hp₀ : 1 < p₀) (ha : 0 ≤ a) :
    0 < 1 - (1 - 1 / p₀) * Real.exp (-a) ∧ 1 ≤ d3phi_F (1 - 1 / p₀) a ∧ d3phi_F (1 - 1 / p₀) a ≤ p₀ := by
  have hp0 : 0 < p₀ := by linarith
  have hq0 : 0 < 1 - 1 / p₀ := by
    have : 1 / p₀ < 1 := (div_lt_one hp0).2 hp₀
    linarith
  have hq1 : 1 - 1 / p₀ < 1 := by have : 0 < 1 / p₀ := by positivity
                                  linarith
  have he0 : 0 < Real.exp (-a) := Real.exp_pos _
  have he1 : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hg0 : 1 / p₀ ≤ 1 - (1 - 1 / p₀) * Real.exp (-a) := by nlinarith
  have hg1 : 1 - (1 - 1 / p₀) * Real.exp (-a) ≤ 1 := by nlinarith
  have hgpos : 0 < 1 - (1 - 1 / p₀) * Real.exp (-a) := lt_of_lt_of_le (by positivity) hg0
  refine ⟨hgpos, ?_, ?_⟩
  · unfold d3phi_F
    rw [le_div_iff₀ hgpos]; linarith
  · unfold d3phi_F
    rw [div_le_iff₀ hgpos]
    have := (div_le_iff₀ hp0).1 hg0
    nlinarith

theorem d3phi_F_lipschitzOn {p₀ : ℝ} (hp₀ : 1 < p₀) :
    LipschitzOnWith (p₀ * (p₀ - 1)).toNNReal (d3phi_F (1 - 1 / p₀)) (Set.Ici 0) := by
  refine (convex_Ici (0 : ℝ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (f' := fun a => -(d3phi_F (1 - 1 / p₀) a) * (d3phi_F (1 - 1 / p₀) a - 1))
    (fun a ha => (d3phi_F_hasDerivAt (d3phi_F_bounds hp₀ ha).1.ne').hasDerivWithinAt) fun a ha => ?_
  obtain ⟨_, h1, h2⟩ := d3phi_F_bounds hp₀ ha
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs,
    Real.coe_toNNReal _ (by nlinarith)]
  rw [abs_le]
  constructor <;> nlinarith


/-- `p = movT_pPath c p₀ L` is an admissible exponent path (AC, `> 1`, `p' = -(1/c) L p (p-1)` a.e.). -/
theorem d3phi_movT_path {c p₀ T : ℝ} (hc : 0 < c) (hp₀ : 1 < p₀) {L : ℝ → ℝ}
    (hL : ∀ r ∈ Set.Icc 0 T, 0 ≤ L r) (hLi : IntegrableOn L (Set.Icc 0 T)) (hT : 0 ≤ T) :
    D3phiPath c L (movT_pPath c p₀ L) T := by
  have hLi' : IntervalIntegrable L volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT).2 hLi
  have hA0 : ∀ t ∈ Set.Icc 0 T, 0 ≤ (1 / c) * ∫ r in (0 : ℝ)..t, L r := fun t ht =>
    mul_nonneg (by positivity) (movT_intL_nonneg hL ht)
  have hpeq : movT_pPath c p₀ L =
      d3phi_F (1 - 1 / p₀) ∘ fun t => (1 / c) * ∫ r in (0 : ℝ)..t, L r :=
    funext fun t => d3phi_movT_pPath_eq c p₀ L t
  refine ⟨?_, fun r hr => (movT_pPath_bounds hc hp₀ hL hr).1, ?_⟩
  · rw [hpeq]
    have hAC : AbsolutelyContinuousOnInterval (fun t => (1 / c) * ∫ r in (0 : ℝ)..t, L r) 0 T :=
      (hLi'.absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp [hT])).const_mul (1 / c)
    refine (d3phi_F_lipschitzOn hp₀).comp_absolutelyContinuousOnInterval ?_ hAC
    intro t ht
    rw [Set.uIcc_of_le hT] at ht
    exact hA0 t ht
  · filter_upwards [hLi'.ae_hasDerivAt_integral] with x hx hxI
    have hxu : x ∈ Set.uIcc 0 T := by
      rw [Set.uIcc_of_le hT]; exact ⟨hxI.1.le, hxI.2.le⟩
    have hd := hx hxu 0 (by simp [hT])
    have hA : HasDerivAt (fun t => (1 / c) * ∫ r in (0 : ℝ)..t, L r) ((1 / c) * L x) x := hd.const_mul _
    have hxT : x ∈ Set.Icc 0 T := ⟨hxI.1.le, hxI.2.le⟩
    have hF := (d3phi_F_hasDerivAt (q := 1 - 1 / p₀)
      (a := (1 / c) * ∫ r in (0 : ℝ)..x, L r) (d3phi_F_bounds hp₀ (hA0 x hxT)).1.ne').comp x hA
    rw [hpeq]
    convert hF using 1
    simp only [Function.comp]
    ring

theorem d3phi_expH_lipschitzOn (C : ℝ) :
    LipschitzOnWith |C|.toNNReal (fun a : ℝ => -C * Real.exp (-a)) (Set.Ici 0) := by
  refine (convex_Ici (0 : ℝ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (f' := fun a => C * Real.exp (-a)) (fun a ha => ?_) fun a ha => ?_
  · have h1 := (hasDerivAt_neg a).exp
    have := h1.const_mul (-C)
    convert this.hasDerivWithinAt using 1; ring
  · have ha' : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.2 (by simpa using ha)
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, Real.coe_toNNReal _ (abs_nonneg _),
      abs_mul, abs_of_pos (Real.exp_pos _)]
    nlinarith [abs_nonneg C, Real.exp_pos (-a)]

/-- The closed form of the gain: `d3phi_gain` along `movT_pPath` is `movT_lpGain`. -/
theorem d3phi_movT_gain {c Cs p₀ T : ℝ} (hc : 0 < c) (hp₀ : 1 < p₀) {L : ℝ → ℝ}
    (hL : ∀ r ∈ Set.Icc 0 T, 0 ≤ L r) (hLi : IntegrableOn L (Set.Icc 0 T)) {t : ℝ}
    (ht : t ∈ Set.Icc 0 T) :
    d3phi_gain c Cs L (movT_pPath c p₀ L) t = movT_lpGain c Cs p₀ L t := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  set q : ℝ := 1 - 1 / p₀ with hq
  set A : ℝ → ℝ := fun r => (1 / c) * ∫ s in (0 : ℝ)..r, L s with hAdef
  have hA0 : ∀ r ∈ Set.Icc 0 T, 0 ≤ A r := fun r hr =>
    mul_nonneg (by positivity) (movT_intL_nonneg hL hr)
  have hLi' : IntervalIntegrable L volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT).2 hLi
  have hsub : Set.uIcc 0 t ⊆ Set.uIcc 0 T := by
    rw [Set.uIcc_of_le hT, Set.uIcc_of_le ht.1]; exact Set.Icc_subset_Icc le_rfl ht.2
  have hLt : IntervalIntegrable L volume 0 t := hLi'.mono_set hsub
  set H : ℝ → ℝ := fun a => -(Cs * q) * Real.exp (-a) with hH
  set G : ℝ → ℝ := H ∘ A with hG
  have hAAC : AbsolutelyContinuousOnInterval A 0 t :=
    (hLt.absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp [ht.1])).const_mul (1 / c)
  have hGAC : AbsolutelyContinuousOnInterval G 0 t := by
    refine (d3phi_expH_lipschitzOn (Cs * q)).comp_absolutelyContinuousOnInterval ?_ hAAC
    intro r hr
    rw [Set.uIcc_of_le ht.1] at hr
    exact hA0 r ⟨hr.1, hr.2.trans ht.2⟩
  have hFTC := hGAC.integral_deriv_eq_sub
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.uIoc 0 t →
      deriv G x = (Cs / c) * L x * ((movT_pPath c p₀ L x - 1) / movT_pPath c p₀ L x) := by
    filter_upwards [hLt.ae_hasDerivAt_integral] with x hx hxI
    have hxu : x ∈ Set.uIcc 0 t := Set.uIoc_subset_uIcc hxI
    have hxI' : x ∈ Set.Ioc 0 t := by rwa [Set.uIoc_of_le ht.1] at hxI
    have hxT : x ∈ Set.Icc 0 T := ⟨hxI'.1.le, hxI'.2.trans ht.2⟩
    have hd := hx hxu 0 (by simp [ht.1])
    have hA : HasDerivAt A ((1 / c) * L x) x := hd.const_mul _
    have hH' : HasDerivAt H ((Cs * q) * Real.exp (-A x)) (A x) := by
      have h1 := (hasDerivAt_neg (A x)).exp
      have := h1.const_mul (-(Cs * q))
      convert this using 1; ring
    have hGd := hH'.comp x hA
    have hGd' : deriv G x = (Cs * q) * Real.exp (-A x) * ((1 / c) * L x) := hGd.deriv
    rw [hGd']
    obtain ⟨hg0, _, _⟩ := d3phi_F_bounds hp₀ (hA0 x hxT)
    have hpx : movT_pPath c p₀ L x = 1 / (1 - q * Real.exp (-A x)) := by
      rw [d3phi_movT_pPath_eq]; rfl
    rw [hpx]
    have hg0' : 1 - q * Real.exp (-A x) ≠ 0 := hg0.ne'
    field_simp
    ring
  unfold d3phi_gain
  rw [intervalIntegral.integral_congr_ae (g := fun x => deriv G x)
    (hae.mono fun x hx hxI => (hx hxI).symm), hFTC]
  simp only [hG, hH, hAdef, Function.comp, intervalIntegral.integral_same, mul_zero, neg_zero,
    Real.exp_zero, movT_lpGain, neg_mul]
  rw [← hq]
  ring

end HRS

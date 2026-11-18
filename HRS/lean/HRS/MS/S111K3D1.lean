import Mathlib

/-!
# S11.1 continuation (S11K3), B03 part D1: the piecewise-affine time map `[0,u+T] → [0,2T]` and its change of variables

`k3φ T u v = (T/u) v` (`v < u`), `T + (v - u)` (`v ≥ u`): the past `[0,u]` is compressed linearly to `[0,T]` and the window
`[u,u+T]` is translated to `[T,2T]`.  `k3ψ` is its inverse.  `k3g T u f s = (u/T) f((u/T)s)` (`s ≤ T`), `f(u + (s-T))` (`s > T`).
`k3_cv`: for `0 ≤ a ≤ b ≤ u+T`, `T ≤ M ≤ 2T`,
`∫_{(φ a, φ b] ∩ [0,M]} g = ∫_{(a,b] ∩ [0,u+M-T]} f`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.MS.S111K3

open Classical

/-- The time map. -/
def k3φ (T u v : ℝ) : ℝ := if v < u then (T / u) * v else T + (v - u)

/-- The inverse time map. -/
def k3ψ (T u s : ℝ) : ℝ := if s ≤ T then (u / T) * s else u + (s - T)

/-- The transformed density: `k3g f s = ψ'(s) f(ψ s)`. -/
def k3g (T u : ℝ) (f : ℝ → ℝ) (s : ℝ) : ℝ :=
  if s ≤ T then (u / T) * f ((u / T) * s) else f (u + (s - T))

lemma k3φψ_lt {T u : ℝ} (hT : 0 < T) (hu : 0 ≤ u) {v : ℝ} (hv : 0 ≤ v) (s : ℝ) :
    k3φ T u v < s ↔ v < k3ψ T u s := by
  rcases hu.eq_or_lt with h0 | hpos
  · subst h0
    have e1 : k3φ T 0 v = T + v := by simp [k3φ, not_lt.2 hv]
    rw [e1]
    unfold k3ψ
    by_cases hs : s ≤ T
    · simp only [hs, if_true]
      simp only [zero_div, zero_mul]
      constructor
      · intro h; linarith
      · intro h; linarith
    · simp only [hs, if_false]
      constructor
      · intro h; linarith
      · intro h; linarith
  · unfold k3φ k3ψ
    by_cases hvu : v < u
    · by_cases hs : s ≤ T
      · simp only [hvu, hs, if_true]
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_lt_iff₀ hpos, lt_div_iff₀ hT]
        constructor <;> intro h <;> nlinarith
      · simp only [hvu, hs, if_true, if_false]
        have hs' : T < s := not_le.1 hs
        have h1 : T / u * v < s := by
          have : T / u * v < T := by
            rw [div_mul_eq_mul_div, div_lt_iff₀ hpos]; nlinarith
          linarith
        constructor
        · intro _; linarith
        · intro _; exact h1
    · simp only [hvu, if_false]
      have hvu' : u ≤ v := not_lt.1 hvu
      by_cases hs : s ≤ T
      · simp only [hs, if_true]
        constructor
        · intro h; linarith
        · intro h
          exfalso
          have : u / T * s ≤ u := by
            rw [div_mul_eq_mul_div, div_le_iff₀ hT]; nlinarith
          linarith
      · simp only [hs, if_false]
        constructor <;> intro h <;> linarith

lemma k3_mem_Ioc_iff {T u : ℝ} (hT : 0 < T) (hu : 0 ≤ u) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (s : ℝ) :
    s ∈ Ioc (k3φ T u a) (k3φ T u b) ↔ a < k3ψ T u s ∧ k3ψ T u s ≤ b := by
  simp only [mem_Ioc]
  rw [k3φψ_lt hT hu ha s, ← not_lt, k3φψ_lt hT hu hb s]
  simp only [not_lt]

/-! ### Change of variables for the two affine pieces -/

lemma k3_core_scale {c : ℝ} (hc : 0 < c) {S : Set ℝ} (hS : MeasurableSet S) {f : ℝ → ℝ}
    (hf : IntegrableOn f ((fun s => c * s) '' S)) :
    IntegrableOn (fun s => c * f (c * s)) S ∧
      ∫ s in S, c * f (c * s) = ∫ v in (fun s => c * s) '' S, f v := by
  have hder : ∀ x ∈ S, HasDerivWithinAt (fun s : ℝ => c * s) c S x := by
    intro x _
    simpa using ((hasDerivAt_id x).const_mul c).hasDerivWithinAt
  have hinj : InjOn (fun s : ℝ => c * s) S := fun x _ y _ h => mul_left_cancel₀ hc.ne' h
  have h1 := (integrableOn_image_iff_integrableOn_abs_deriv_smul hS hder hinj f).1 hf
  have h2 := integral_image_eq_integral_abs_deriv_smul hS hder hinj f
  simp only [smul_eq_mul, abs_of_pos hc] at h1 h2
  exact ⟨h1, h2.symm⟩

lemma k3_core_shift (e : ℝ) {S : Set ℝ} (hS : MeasurableSet S) {f : ℝ → ℝ}
    (hf : IntegrableOn f ((fun s => s + e) '' S)) :
    IntegrableOn (fun s => f (s + e)) S ∧ ∫ s in S, f (s + e) = ∫ v in (fun s => s + e) '' S, f v := by
  have hder : ∀ x ∈ S, HasDerivWithinAt (fun s : ℝ => s + e) 1 S x := by
    intro x _
    simpa using ((hasDerivAt_id x).add_const e).hasDerivWithinAt
  have hinj : InjOn (fun s : ℝ => s + e) S := fun x _ y _ h => add_right_cancel h
  have h1 := (integrableOn_image_iff_integrableOn_abs_deriv_smul hS hder hinj f).1 hf
  have h2 := integral_image_eq_integral_abs_deriv_smul hS hder hinj f
  simp only [smul_eq_mul, abs_one, one_mul] at h1 h2
  exact ⟨h1, h2.symm⟩

/-- The two pieces of the image: the past piece. -/
lemma k3_image_mul {c : ℝ} (hc : c ≠ 0) (S : Set ℝ) :
    (fun s => c * s) '' S = (fun v => c⁻¹ * v) ⁻¹' S := by
  ext v
  simp only [mem_image, mem_preimage]
  constructor
  · rintro ⟨s, hs, rfl⟩
    simpa [inv_mul_cancel_left₀ hc] using hs
  · intro h
    exact ⟨c⁻¹ * v, h, by field_simp⟩

lemma k3_image_past {T u : ℝ} (hT : 0 < T) (hu : 0 < u) {a b M : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hM : T ≤ M) :
    (fun s => (u / T) * s) '' (Ioc (k3φ T u a) (k3φ T u b) ∩ Icc 0 M ∩ Iic T) = Ioc a b ∩ Icc 0 u := by
  have hc : 0 < u / T := div_pos hu hT
  rw [k3_image_mul hc.ne']
  ext v
  simp only [mem_preimage, mem_inter_iff, mem_Ioc, mem_Icc, mem_Iic]
  have key : ∀ s, s ≤ T → k3ψ T u s = (u / T) * s := fun s hs => by simp [k3ψ, hs]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩
    have hs := key _ h5
    have e : (u / T) * ((u / T)⁻¹ * v) = v := by field_simp
    have hl : a < v := by
      have := (k3φψ_lt hT hu.le ha ((u / T)⁻¹ * v)).1 h1
      rwa [hs, e] at this
    have hr : v ≤ b := by
      have := not_lt.2 h2
      rw [k3φψ_lt hT hu.le hb, hs, e] at this
      exact not_lt.1 this
    have h0 : 0 ≤ v := by
      have := mul_nonneg hc.le h3
      rwa [e] at this
    have hu' : v ≤ u := by
      have := mul_le_mul_of_nonneg_left h5 hc.le
      rw [e] at this
      calc v ≤ u / T * T := this
        _ = u := by field_simp
    exact ⟨⟨hl, hr⟩, h0, hu'⟩
  · rintro ⟨⟨hl, hr⟩, h0, hu'⟩
    have e : (u / T) * ((u / T)⁻¹ * v) = v := by field_simp
    have h5 : (u / T)⁻¹ * v ≤ T := by
      rw [← mul_le_mul_iff_of_pos_left hc, e]
      calc v ≤ u := hu'
        _ = u / T * T := by field_simp
    have hs := key _ h5
    refine ⟨⟨⟨?_, ?_⟩, ?_, h5.trans hM⟩, h5⟩
    · rw [k3φψ_lt hT hu.le ha, hs, e]; exact hl
    · rw [← not_lt, k3φψ_lt hT hu.le hb, hs, e, not_lt]; exact hr
    · exact mul_nonneg (inv_nonneg.2 hc.le) h0

/-- The window piece. -/
lemma k3_image_window {T u : ℝ} (hT : 0 < T) (hu : 0 ≤ u) {a b M : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (fun s => s + (u - T)) '' (Ioc (k3φ T u a) (k3φ T u b) ∩ Icc 0 M ∩ Ioi T) =
      Ioc a b ∩ Ioc u (u + (M - T)) := by
  rw [Set.image_add_right]
  ext v
  simp only [mem_preimage, mem_inter_iff, mem_Ioc, mem_Icc, mem_Ioi]
  have key : ∀ s, T < s → k3ψ T u s = u + (s - T) := fun s hs => by simp [k3ψ, not_le.2 hs]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩
    have hs := key _ h5
    have e : u + ((v + -(u - T)) - T) = v := by ring
    have hl : a < v := by
      have := (k3φψ_lt hT hu ha (v + -(u - T))).1 h1
      rwa [hs, e] at this
    have hr : v ≤ b := by
      have := not_lt.2 h2
      rw [k3φψ_lt hT hu hb, hs, e] at this
      exact not_lt.1 this
    exact ⟨⟨hl, hr⟩, by linarith, by linarith⟩
  · rintro ⟨⟨hl, hr⟩, h1, h2⟩
    have h5 : T < v + -(u - T) := by linarith
    have hs := key _ h5
    have e : u + ((v + -(u - T)) - T) = v := by ring
    refine ⟨⟨⟨?_, ?_⟩, by linarith, by linarith⟩, h5⟩
    · rw [k3φψ_lt hT hu ha, hs, e]; exact hl
    · rw [← not_lt, k3φψ_lt hT hu hb, hs, e, not_lt]; exact hr


/-! ### The change-of-variables identity -/

lemma k3g_past {T u : ℝ} {f : ℝ → ℝ} {s : ℝ} (hs : s ≤ T) : k3g T u f s = (u / T) * f ((u / T) * s) := by
  simp [k3g, hs]

lemma k3g_window {T u : ℝ} {f : ℝ → ℝ} {s : ℝ} (hs : T < s) : k3g T u f s = f (s + (u - T)) := by
  simp only [k3g, not_le.2 hs, if_false]
  congr 1; ring

theorem k3_cv {T u : ℝ} (hT : 0 < T) (hu : 0 ≤ u) {a b M : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hbH : b ≤ u + T) (hM : T ≤ M) (hMT : M ≤ 2 * T) {f : ℝ → ℝ} (hf : IntegrableOn f (Icc 0 (u + T))) :
    IntegrableOn (k3g T u f) (Ioc (k3φ T u a) (k3φ T u b) ∩ Icc 0 M) ∧
      ∫ s in Ioc (k3φ T u a) (k3φ T u b) ∩ Icc 0 M, k3g T u f s =
        ∫ v in Ioc a b ∩ Icc 0 (u + (M - T)), f v := by
  have hb : 0 ≤ b := ha.trans hab
  set S : Set ℝ := Ioc (k3φ T u a) (k3φ T u b) ∩ Icc 0 M with hS
  set S1 : Set ℝ := S ∩ Iic T with hS1
  set S2 : Set ℝ := S ∩ Ioi T with hS2
  have hSm : MeasurableSet S := measurableSet_Ioc.inter measurableSet_Icc
  have hS1m : MeasurableSet S1 := hSm.inter measurableSet_Iic
  have hS2m : MeasurableSet S2 := hSm.inter measurableSet_Ioi
  have hSU : S = S1 ∪ S2 := by
    ext s
    simp only [hS1, hS2, mem_union, mem_inter_iff, mem_Iic, mem_Ioi]
    constructor
    · intro h
      by_cases hs : s ≤ T
      · exact Or.inl ⟨h, hs⟩
      · exact Or.inr ⟨h, not_le.1 hs⟩
    · rintro (h | h) <;> exact h.1
  have hdisj : Disjoint S1 S2 := by
    rw [Set.disjoint_left]
    intro s h1 h2
    exact absurd (show T < s from h2.2) (not_lt.2 (show s ≤ T from h1.2))
  -- the window piece
  have himg2 := k3_image_window hT hu (M := M) ha hb
  have hI2 : IntegrableOn f ((fun s => s + (u - T)) '' S2) := by
    rw [hS2, hS, himg2]
    refine hf.mono_set fun v hv => ⟨by linarith [hv.2.1, hu], by linarith [hv.2.2]⟩
  obtain ⟨hint2, hval2⟩ := k3_core_shift (u - T) hS2m hI2
  have hg2 : EqOn (k3g T u f) (fun s => f (s + (u - T))) S2 := fun s hs => k3g_window hs.2
  have hint2' : IntegrableOn (k3g T u f) S2 := hint2.congr_fun (fun s hs => (hg2 hs).symm) hS2m
  have hval2' : ∫ s in S2, k3g T u f s = ∫ v in Ioc a b ∩ Ioc u (u + (M - T)), f v := by
    rw [setIntegral_congr_fun hS2m hg2, hval2, hS2, hS, himg2]
  -- the past piece
  have hpast : IntegrableOn (k3g T u f) S1 ∧
      ∫ s in S1, k3g T u f s = ∫ v in Ioc a b ∩ Icc 0 u, f v := by
    rcases hu.eq_or_lt with h0 | hpos
    · subst h0
      have hg1 : EqOn (k3g T 0 f) (fun _ => (0 : ℝ)) S1 := fun s hs => by
        rw [k3g_past hs.2]; simp
      have hfin : volume S1 ≠ ⊤ :=
        ne_top_of_le_ne_top (measure_Icc_lt_top (a := (0 : ℝ)) (b := M)).ne (measure_mono (fun s hs => hs.1.2))
      refine ⟨(integrableOn_const hfin |>.congr_fun (fun s hs => (hg1 hs).symm) hS1m), ?_⟩
      · rw [setIntegral_congr_fun hS1m hg1]
        have : Ioc a b ∩ Icc 0 (0 : ℝ) = ∅ := by
          ext v
          simp only [mem_inter_iff, mem_Ioc, mem_Icc, mem_empty_iff_false, iff_false, not_and]
          intro h1 _ h3
          linarith [h1.1, h3]
        rw [this]
        simp
    · have hc : 0 < u / T := div_pos hpos hT
      have himg1 := k3_image_past hT hpos (M := M) ha hb hM
      have hI1 : IntegrableOn f ((fun s => (u / T) * s) '' S1) := by
        rw [hS1, hS, himg1]
        exact hf.mono_set fun v hv => ⟨hv.2.1, by linarith [hv.2.2, hT]⟩
      obtain ⟨hint1, hval1⟩ := k3_core_scale hc hS1m hI1
      have hg1 : EqOn (k3g T u f) (fun s => (u / T) * f ((u / T) * s)) S1 := fun s hs => k3g_past hs.2
      refine ⟨hint1.congr_fun (fun s hs => (hg1 hs).symm) hS1m, ?_⟩
      rw [setIntegral_congr_fun hS1m hg1, hval1, hS1, hS, himg1]
  obtain ⟨hint1', hval1'⟩ := hpast
  refine ⟨?_, ?_⟩
  · rw [hSU]; exact hint1'.union hint2'
  · rw [hSU, setIntegral_union hdisj hS2m hint1' hint2', hval1', hval2']
    -- reassemble the target set
    have hU : Ioc a b ∩ Icc 0 (u + (M - T)) = (Ioc a b ∩ Icc 0 u) ∪ (Ioc a b ∩ Ioc u (u + (M - T))) := by
      ext v
      simp only [mem_inter_iff, mem_Ioc, mem_Icc, mem_union]
      constructor
      · rintro ⟨h1, h2, h3⟩
        by_cases hvu : v ≤ u
        · exact Or.inl ⟨h1, h2, hvu⟩
        · exact Or.inr ⟨h1, not_le.1 hvu, h3⟩
      · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
        · exact ⟨h1, h2, by linarith⟩
        · exact ⟨h1, by linarith [h1.1], h3⟩
    have hd : Disjoint (Ioc a b ∩ Icc 0 u) (Ioc a b ∩ Ioc u (u + (M - T))) := by
      rw [Set.disjoint_left]
      intro v h1 h2
      exact absurd h2.2.1 (not_lt.2 h1.2.2)
    have hI1' : IntegrableOn f (Ioc a b ∩ Icc 0 u) :=
      hf.mono_set fun v hv => ⟨hv.2.1, by linarith [hv.2.2, hT]⟩
    have hI2' : IntegrableOn f (Ioc a b ∩ Ioc u (u + (M - T))) :=
      hf.mono_set fun v hv => ⟨by linarith [hv.2.1, hu], by linarith [hv.2.2]⟩
    rw [hU, setIntegral_union hd (measurableSet_Ioc.inter measurableSet_Ioc) hI1' hI2']

/-- Integrability of the transformed density on `[0,2T]`. -/
theorem k3_integrable {T u : ℝ} (hT : 0 < T) (hu : 0 ≤ u) {f : ℝ → ℝ} (hf : IntegrableOn f (Icc 0 (u + T))) :
    IntegrableOn (k3g T u f) (Icc 0 (2 * T)) := by
  have hU : Icc (0 : ℝ) (2 * T) = Icc 0 T ∪ Ioc T (2 * T) := by
    ext s
    simp only [mem_Icc, mem_union, mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hs : s ≤ T
      · exact Or.inl ⟨h1, hs⟩
      · exact Or.inr ⟨not_le.1 hs, h2⟩
    · rintro (h | h)
      · exact ⟨h.1, by linarith [h.2]⟩
      · exact ⟨by linarith [h.1], h.2⟩
  rw [hU]
  refine IntegrableOn.union ?_ ?_
  · rcases hu.eq_or_lt with h0 | hpos
    · subst h0
      have hg1 : EqOn (k3g T 0 f) (fun _ => (0 : ℝ)) (Icc 0 T) := fun s hs => by
        rw [k3g_past hs.2]; simp
      exact (integrableOn_const (measure_Icc_lt_top (a := (0 : ℝ)) (b := T)).ne).congr_fun
        (fun s hs => (hg1 hs).symm) measurableSet_Icc
    · have hc : 0 < u / T := div_pos hpos hT
      have himg : (fun s => (u / T) * s) '' Icc 0 T = Icc 0 u := by
        rw [k3_image_mul hc.ne']
        ext v
        simp only [mem_preimage, mem_Icc]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨?_, ?_⟩
          · have := mul_nonneg hc.le h1
            rwa [mul_inv_cancel_left₀ hc.ne'] at this
          · have := mul_le_mul_of_nonneg_left h2 hc.le
            rw [mul_inv_cancel_left₀ hc.ne'] at this
            calc v ≤ u / T * T := this
              _ = u := by field_simp
        · rintro ⟨h1, h2⟩
          refine ⟨mul_nonneg (inv_nonneg.2 hc.le) h1, ?_⟩
          rw [← mul_le_mul_iff_of_pos_left hc, mul_inv_cancel_left₀ hc.ne']
          calc v ≤ u := h2
            _ = u / T * T := by field_simp
      have hI : IntegrableOn f ((fun s => (u / T) * s) '' Icc 0 T) := by
        rw [himg]; exact hf.mono_set (Icc_subset_Icc_right (by linarith))
      obtain ⟨hint, -⟩ := k3_core_scale hc measurableSet_Icc hI
      exact hint.congr_fun (fun s hs => (k3g_past hs.2).symm) measurableSet_Icc
  · have himg : (fun s => s + (u - T)) '' Ioc T (2 * T) = Ioc u (u + T) := by
      rw [Set.image_add_right]
      ext v
      simp only [mem_preimage, mem_Ioc]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    have hI : IntegrableOn f ((fun s => s + (u - T)) '' Ioc T (2 * T)) := by
      rw [himg]; exact hf.mono_set fun v hv => ⟨by linarith [hv.1, hu], hv.2⟩
    obtain ⟨hint, -⟩ := k3_core_shift (u - T) measurableSet_Ioc hI
    exact hint.congr_fun (fun s hs => (k3g_window hs.1).symm) measurableSet_Ioc


/-- The total integral of the transformed density. -/
theorem k3_cv_total {T u : ℝ} (hT : 0 < T) (hu : 0 ≤ u) {f : ℝ → ℝ} (hf : IntegrableOn f (Icc 0 (u + T))) :
    ∫ s in Icc 0 (2 * T), k3g T u f s = ∫ v in Icc 0 (u + T), f v := by
  have hU : Icc (0 : ℝ) (2 * T) = Icc 0 T ∪ Ioc T (2 * T) := by
    ext s
    simp only [mem_Icc, mem_union, mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hs : s ≤ T
      · exact Or.inl ⟨h1, hs⟩
      · exact Or.inr ⟨not_le.1 hs, h2⟩
    · rintro (h | h)
      · exact ⟨h.1, by linarith [h.2]⟩
      · exact ⟨by linarith [h.1], h.2⟩
  have himg : (fun s => s + (u - T)) '' Ioc T (2 * T) = Ioc u (u + T) := by
    rw [Set.image_add_right]
    ext v
    simp only [mem_preimage, mem_Ioc]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have hI : IntegrableOn f ((fun s => s + (u - T)) '' Ioc T (2 * T)) := by
    rw [himg]; exact hf.mono_set fun v hv => ⟨by linarith [hv.1, hu], hv.2⟩
  obtain ⟨hint2, hval2⟩ := k3_core_shift (u - T) measurableSet_Ioc hI
  have hg2 : EqOn (k3g T u f) (fun s => f (s + (u - T))) (Ioc T (2 * T)) := fun s hs => k3g_window hs.1
  have hint2' : IntegrableOn (k3g T u f) (Ioc T (2 * T)) :=
    hint2.congr_fun (fun s hs => (hg2 hs).symm) measurableSet_Ioc
  have hval2' : ∫ s in Ioc T (2 * T), k3g T u f s = ∫ v in Ioc u (u + T), f v := by
    rw [setIntegral_congr_fun measurableSet_Ioc hg2, hval2, himg]
  have hd1 : Disjoint (Icc (0 : ℝ) T) (Ioc T (2 * T)) := by
    rw [Set.disjoint_left]; intro s h1 h2; exact absurd h2.1 (not_lt.2 h1.2)
  rcases hu.eq_or_lt with h0 | hpos
  · subst h0
    have hg1 : EqOn (k3g T 0 f) (fun _ => (0 : ℝ)) (Icc 0 T) := fun s hs => by
      rw [k3g_past hs.2]; simp
    have hint1 : IntegrableOn (k3g T 0 f) (Icc 0 T) :=
      (integrableOn_const (measure_Icc_lt_top (a := (0 : ℝ)) (b := T)).ne).congr_fun
        (fun s hs => (hg1 hs).symm) measurableSet_Icc
    rw [hU, setIntegral_union hd1 measurableSet_Ioc hint1 hint2', setIntegral_congr_fun measurableSet_Icc hg1,
      hval2']
    simp only [integral_zero, zero_add, zero_add]
    rw [integral_Icc_eq_integral_Ioc]
  · have hc : 0 < u / T := div_pos hpos hT
    have himg1 : (fun s => (u / T) * s) '' Icc 0 T = Icc 0 u := by
      rw [k3_image_mul hc.ne']
      ext v
      simp only [mem_preimage, mem_Icc]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨?_, ?_⟩
        · have := mul_nonneg hc.le h1
          rwa [mul_inv_cancel_left₀ hc.ne'] at this
        · have := mul_le_mul_of_nonneg_left h2 hc.le
          rw [mul_inv_cancel_left₀ hc.ne'] at this
          calc v ≤ u / T * T := this
            _ = u := by field_simp
      · rintro ⟨h1, h2⟩
        refine ⟨mul_nonneg (inv_nonneg.2 hc.le) h1, ?_⟩
        rw [← mul_le_mul_iff_of_pos_left hc, mul_inv_cancel_left₀ hc.ne']
        calc v ≤ u := h2
          _ = u / T * T := by field_simp
    have hI1 : IntegrableOn f ((fun s => (u / T) * s) '' Icc 0 T) := by
      rw [himg1]; exact hf.mono_set (Icc_subset_Icc_right (by linarith))
    obtain ⟨hint1, hval1⟩ := k3_core_scale hc measurableSet_Icc hI1
    have hg1 : EqOn (k3g T u f) (fun s => (u / T) * f ((u / T) * s)) (Icc 0 T) := fun s hs => k3g_past hs.2
    have hint1' : IntegrableOn (k3g T u f) (Icc 0 T) :=
      hint1.congr_fun (fun s hs => (hg1 hs).symm) measurableSet_Icc
    have hval1' : ∫ s in Icc 0 T, k3g T u f s = ∫ v in Icc 0 u, f v := by
      rw [setIntegral_congr_fun measurableSet_Icc hg1, hval1, himg1]
    have hd2 : Disjoint (Icc (0 : ℝ) u) (Ioc u (u + T)) := by
      rw [Set.disjoint_left]; intro s h1 h2; exact absurd h2.1 (not_lt.2 h1.2)
    have hU2 : Icc (0 : ℝ) (u + T) = Icc 0 u ∪ Ioc u (u + T) := by
      ext s
      simp only [mem_Icc, mem_union, mem_Ioc]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases hs : s ≤ u
        · exact Or.inl ⟨h1, hs⟩
        · exact Or.inr ⟨not_le.1 hs, h2⟩
      · rintro (h | h)
        · exact ⟨h.1, by linarith [h.2]⟩
        · exact ⟨by linarith [h.1], h.2⟩
    rw [hU, setIntegral_union hd1 measurableSet_Ioc hint1' hint2', hval1', hval2', hU2,
      setIntegral_union hd2 measurableSet_Ioc (hf.mono_set (Icc_subset_Icc_right (by linarith)))
        (hf.mono_set fun v hv => ⟨by linarith [hv.1], hv.2⟩)]

/-! ### Monotonicity and continuity of the time map -/

lemma k3ψφ {T u : ℝ} (hT : 0 < T) (hu : 0 ≤ u) {v : ℝ} (hv : 0 ≤ v) : k3ψ T u (k3φ T u v) = v := by
  unfold k3φ k3ψ
  by_cases hvu : v < u
  · have hpos : 0 < u := lt_of_le_of_lt hv hvu
    simp only [hvu, if_true]
    have h1 : T / u * v ≤ T := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hpos]; nlinarith
    simp only [h1, if_true]
    field_simp
  · simp only [hvu, if_false]
    by_cases hle : T + (v - u) ≤ T
    · simp only [hle, if_true]
      have : v = u := by linarith [not_lt.1 hvu]
      subst this
      have e : T + (v - v) = T := by ring
      rw [e]
      field_simp
    · simp only [hle, if_false]; ring

lemma k3φ_mono {T u : ℝ} (hT : 0 < T) (hu : 0 ≤ u) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    k3φ T u a ≤ k3φ T u b := by
  by_contra h
  have h1 : k3φ T u b < k3φ T u a := not_le.1 h
  rw [k3φψ_lt hT hu (ha.trans hab), k3ψφ hT hu ha] at h1
  linarith

lemma k3φ_nonneg {T u : ℝ} (hT : 0 < T) (hu : 0 ≤ u) {v : ℝ} (hv : 0 ≤ v) : 0 ≤ k3φ T u v := by
  unfold k3φ
  split_ifs with h
  · have : 0 ≤ T / u := div_nonneg hT.le hu
    positivity
  · linarith [not_lt.1 h]

lemma k3φ_le {T u : ℝ} (hT : 0 < T) (hu : 0 ≤ u) {v : ℝ} (hv : 0 ≤ v) (hvH : v ≤ u + T) :
    k3φ T u v ≤ 2 * T := by
  unfold k3φ
  split_ifs with h
  · have hpos : 0 < u := lt_of_le_of_lt hv h
    have : T / u * v ≤ T := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hpos]; nlinarith
    linarith
  · linarith

lemma k3φ_zero_of_pos {T u : ℝ} (hu : 0 < u) : k3φ T u 0 = 0 := by simp [k3φ, hu]

lemma k3φ_continuousOn {T u : ℝ} (hT : 0 < T) (hu : 0 ≤ u) : ContinuousOn (k3φ T u) (Ici 0) := by
  rcases hu.eq_or_lt with h0 | hpos
  · subst h0
    have : EqOn (k3φ T 0) (fun v => T + v) (Ici 0) := fun v hv => by
      simp [k3φ, not_lt.2 (show (0 : ℝ) ≤ v from hv)]
    exact (continuousOn_const.add continuousOn_id).congr this
  · have hc : Continuous fun v : ℝ => if v ≤ u then (T / u) * v else T + (v - u) := by
      refine Continuous.if_le (by fun_prop) (by fun_prop) continuous_id continuous_const ?_
      intro v hv
      rw [hv]
      field_simp
      ring
    refine hc.continuousOn.congr fun v hv => ?_
    simp only [k3φ]
    by_cases h : v < u
    · simp [h, h.le]
    · by_cases h' : v = u
      · subst h'
        simp [hpos.ne']
      · have : ¬ v ≤ u := fun h2 => h' (le_antisymm h2 (not_lt.1 h))
        simp [h, this]

end HRS.MS.S111K3

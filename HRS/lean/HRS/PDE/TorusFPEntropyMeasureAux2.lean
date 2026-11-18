import HRS.PDE.TorusFPEntropyMeasureAux1

/-!
# D3-b, Aux2: smooth positive approximation of bounded densities (entropy-recovering)

Helpers `d3b_*`.  Everything is with respect to a probability measure `P` on the torus; `φ(s) = s log s`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS

variable {n : ℕ}

theorem d3b_abs_log_le {c B s : ℝ} (hc : 0 < c) (h1 : c ≤ s) (h2 : s ≤ B) :
    |Real.log s| ≤ |Real.log c| + |Real.log B| := by
  have hs : 0 < s := hc.trans_le h1
  have a1 : Real.log c ≤ Real.log s := Real.log_le_log hc h1
  have a2 : Real.log s ≤ Real.log B := Real.log_le_log hs h2
  rw [abs_le]
  constructor <;> linarith [neg_abs_le (Real.log c), le_abs_self (Real.log B),
    abs_nonneg (Real.log c), abs_nonneg (Real.log B)]

theorem d3b_phi_bdd {c B s : ℝ} (hc : 0 < c) (h1 : c ≤ s) (h2 : s ≤ B) :
    |s * Real.log s| ≤ B * (|Real.log c| + |Real.log B|) := by
  have hs : 0 < s := hc.trans_le h1
  have hB : 0 < B := hs.trans_le h2
  rw [abs_mul, abs_of_pos hs]
  exact mul_le_mul h2 (d3b_abs_log_le hc h1 h2) (abs_nonneg _) hB.le

theorem d3b_phi_lip {c B x y : ℝ} (hc : 0 < c) (hx : x ∈ Set.Icc c B) (hy : y ∈ Set.Icc c B) :
    |y * Real.log y - x * Real.log x| ≤ (|Real.log c| + |Real.log B| + 1) * |y - x| := by
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun s : ℝ => s * Real.log s)
    (f' := fun s => Real.log s + 1) (C := |Real.log c| + |Real.log B| + 1) (s := Set.Icc c B)
    (x := x) (y := y)
    (fun s hs => (Real.hasDerivAt_mul_log (hc.trans_le hs.1).ne').hasDerivWithinAt)
    (fun s hs => by
      have := d3b_abs_log_le hc hs.1 hs.2
      rw [Real.norm_eq_abs]
      exact (abs_add_le _ _).trans (by simp only [abs_one]; linarith))
    (convex_Icc c B) hx hy
  simpa [Real.norm_eq_abs] using this

theorem d3b_clamp {c B u v : ℝ} (h1 : c ≤ v) (h2 : v ≤ B) :
    |max c (min u B) - v| ≤ |u - v| := by
  rcases le_total u c with hu | hu
  · have : min u B ≤ c := (min_le_left _ _).trans hu
    rw [max_eq_left this, abs_of_nonpos (by linarith : c - v ≤ 0),
      abs_of_nonpos (by linarith : u - v ≤ 0)]
    linarith
  · rcases le_total u B with hB | hB
    · rw [min_eq_left hB, max_eq_right hu]
    · rw [min_eq_right hB, max_eq_right (h1.trans h2)]
      rw [abs_of_nonneg (by linarith : 0 ≤ B - v), abs_of_nonneg (by linarith : 0 ≤ u - v)]
      linarith

theorem d3b_integrable_of_bdd {P : Measure (Torus n)} [IsFiniteMeasure P] {f : Torus n → ℝ}
    (hm : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) : Integrable f P :=
  Integrable.mono' (integrable_const C) hm.aestronglyMeasurable
    (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hC x)

theorem d3b_smooth_const_mul {a : ℝ} {s : Torus n → ℝ} (hs : Torus.IsSmooth s) :
    Torus.IsSmooth (fun x => a * s x) := by
  have := d1_isSmooth_comb a 0 hs hs
  simpa using this

/-- Smooth positive normalised approximation of a bounded positive density, controlling `L¹` distance and
entropy. -/
theorem d3b_smooth_approx_bdd (P : Measure (Torus n)) [IsProbabilityMeasure P]
    {h : Torus n → ℝ} (hm : Measurable h) {c B : ℝ} (hc : 0 < c) (hch : ∀ x, c ≤ h x)
    (hhB : ∀ x, h x ≤ B) (hmass : ∫ x, h x ∂P = 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : Torus n → ℝ, Torus.IsSmooth g ∧ (∀ x, 0 < g x) ∧ ∫ x, g x ∂P = 1 ∧
      ∫ x, |g x - h x| ∂P ≤ ε ∧
      ∫ x, g x * Real.log (g x) ∂P ≤ ∫ x, h x * Real.log (h x) ∂P + ε := by
  have hBpos : ∀ x, 0 < h x := fun x => hc.trans_le (hch x)
  have hint : Integrable h P := d3b_integrable_of_bdd hm (C := B) fun x => by
    rw [abs_of_pos (hBpos x)]; exact hhB x
  have hc1 : c ≤ 1 := by
    have := integral_mono (integrable_const c) hint hch
    simpa [hmass] using this
  have hB1 : 1 ≤ B := by
    have := integral_mono hint (integrable_const B) hhB
    simpa [hmass] using this
  have hBp : 0 < B := lt_of_lt_of_le one_pos hB1
  set L : ℝ := |Real.log (c / 4)| + |Real.log (2 * B + 1)| + 1 with hL
  have hL1 : 1 ≤ L := by rw [hL]; linarith [abs_nonneg (Real.log (c / 4)), abs_nonneg (Real.log (2 * B + 1))]
  set ε1 : ℝ := min (min (c / 4) (1 / 4)) (ε / (4 * L + 4)) with hε1
  have hε1pos : 0 < ε1 := lt_min (lt_min (by positivity) (by norm_num)) (by positivity)
  have hε1a : ε1 ≤ c / 4 := (min_le_left _ _).trans (min_le_left _ _)
  have hε1b : ε1 ≤ 1 / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have hε1c : ε1 ≤ ε / (4 * L + 4) := min_le_right _ _
  have hε1d : 4 * ε1 * (L + 1) ≤ ε := by
    have := mul_le_mul_of_nonneg_left hε1c (by positivity : (0 : ℝ) ≤ 4 * (L + 1))
    have e : 4 * (L + 1) * (ε / (4 * L + 4)) = ε := by field_simp
    nlinarith
  -- step 1: bounded continuous approximation
  obtain ⟨g0, hg0, hg0i⟩ := hint.exists_boundedContinuous_integral_sub_le hε1pos
  simp only [Real.norm_eq_abs] at hg0
  set g1 : Torus n → ℝ := fun x => max c (min (g0 x) B) with hg1
  have hg1c : Continuous g1 := continuous_const.max ((g0.continuous).min continuous_const)
  have hg1a : ∀ x, c ≤ g1 x := fun x => le_max_left _ _
  have hg1b : ∀ x, g1 x ≤ B := fun x => max_le (hc1.trans hB1) (min_le_right _ _)
  have hg1h : ∀ x, |g1 x - h x| ≤ |h x - g0 x| := fun x => by
    rw [abs_sub_comm (h x)]; exact d3b_clamp (hch x) (hhB x)
  have hg1m : Measurable fun x => |g1 x - h x| := (hg1c.measurable.sub hm).abs
  have hI1 : Integrable (fun x => |g1 x - h x|) P := d3b_integrable_of_bdd hg1m (C := B) (fun x => by
    rw [abs_abs, abs_le]; constructor <;> linarith [hg1a x, hg1b x, hch x, hhB x])
  have hg1int : ∫ x, |g1 x - h x| ∂P ≤ ε1 :=
    le_trans (integral_mono_of_nonneg (ae_of_all _ fun x => abs_nonneg _) (hint.sub hg0i).abs
      (ae_of_all _ hg1h)) hg0
  -- step 2: smooth approximation
  obtain ⟨s, hs, hsg⟩ := d1_exists_smooth_approx hg1c hε1pos
  have hsc : Continuous s := d1c_continuous_of_isSmooth hs
  have hs_lo : ∀ x, 3 * c / 4 ≤ s x := fun x => by
    have := (abs_le.1 (hsg x)).2; have := hg1a x; linarith
  have hs_hi : ∀ x, s x ≤ B + 1 / 4 := fun x => by
    have := (abs_le.1 (hsg x)).1; have := hg1b x; linarith
  have hspos : ∀ x, 0 < s x := fun x => by linarith [hs_lo x]
  have hsg1 : ∫ x, |s x - g1 x| ∂P ≤ ε1 := by
    have h1 : ∫ x, |s x - g1 x| ∂P ≤ ∫ _x, ε1 ∂P :=
      integral_mono (d3a_hint P (by fun_prop)) (integrable_const _) fun x => by
        rw [abs_sub_comm]; exact hsg x
    simpa using h1
  have hsh : ∫ x, |s x - h x| ∂P ≤ 2 * ε1 := by
    have hI2 : Integrable (fun x => |s x - g1 x|) P := d3a_hint P (by fun_prop)
    have h1 : ∫ x, |s x - h x| ∂P ≤ ∫ x, (|s x - g1 x| + |g1 x - h x|) ∂P :=
      integral_mono_of_nonneg (ae_of_all _ fun x => abs_nonneg _) (hI2.add hI1)
        (ae_of_all _ fun x => by
          have := abs_add_le (s x - g1 x) (g1 x - h x)
          simpa using this)
    rw [integral_add hI2 hI1] at h1
    linarith
  set m' : ℝ := ∫ x, s x ∂P with hm'
  have hsi : Integrable s P := d3a_hint P hsc
  have hm'1 : |m' - 1| ≤ 2 * ε1 := by
    have e : m' - 1 = ∫ x, (s x - h x) ∂P := by
      rw [integral_sub hsi hint, hmass]
    rw [e]
    refine (abs_integral_le_integral_abs).trans (le_trans ?_ hsh)
    exact le_rfl
  have hm'lo : 1 / 2 ≤ m' := by linarith [(abs_le.1 hm'1).1]
  have hm'hi : m' ≤ 3 / 2 := by linarith [(abs_le.1 hm'1).2]
  have hm'pos : 0 < m' := by linarith
  set g : Torus n → ℝ := fun x => m'⁻¹ * s x with hg
  have hgs : Torus.IsSmooth g := d3b_smooth_const_mul hs
  have hgc : Continuous g := continuous_const.mul hsc
  have hgpos : ∀ x, 0 < g x := fun x => mul_pos (inv_pos.2 hm'pos) (hspos x)
  have hgmass : ∫ x, g x ∂P = 1 := by
    rw [hg]; simp only []
    rw [integral_const_mul, ← hm', inv_mul_cancel₀ hm'pos.ne']
  have hgs_rel : ∀ x, g x * m' = s x := fun x => by
    simp only [hg]; field_simp
  have hgL1 : ∫ x, |g x - s x| ∂P = |1 - m'| := by
    have e : ∀ x, |g x - s x| = |m'⁻¹ - 1| * s x := fun x => by
      have : g x - s x = (m'⁻¹ - 1) * s x := by simp only [hg]; ring
      rw [this, abs_mul, abs_of_pos (hspos x)]
    simp_rw [e]
    rw [integral_const_mul, ← hm']
    have : |m'⁻¹ - 1| * m' = |1 - m'| := by
      have : m'⁻¹ - 1 = (1 - m') * m'⁻¹ := by field_simp
      rw [this, abs_mul, abs_of_pos (inv_pos.2 hm'pos)]
      field_simp
    exact this
  have hgh : ∫ x, |g x - h x| ∂P ≤ 4 * ε1 := by
    have hI3 : Integrable (fun x => |g x - s x|) P := d3a_hint P (by fun_prop)
    have hI4 : Integrable (fun x => |s x - h x|) P :=
      d3b_integrable_of_bdd ((hsc.measurable.sub hm).abs) (C := B + 1) (fun x => by
        rw [abs_abs, abs_le]; constructor <;> linarith [hs_lo x, hs_hi x, hch x, hhB x])
    have h1 : ∫ x, |g x - h x| ∂P ≤ ∫ x, (|g x - s x| + |s x - h x|) ∂P :=
      integral_mono_of_nonneg (ae_of_all _ fun x => abs_nonneg _) (hI3.add hI4)
        (ae_of_all _ fun x => by
          have := abs_add_le (g x - s x) (s x - h x)
          simpa using this)
    rw [integral_add hI3 hI4, hgL1] at h1
    have : |1 - m'| ≤ 2 * ε1 := by rw [abs_sub_comm]; exact hm'1
    linarith
  have hε4 : 4 * ε1 ≤ ε := by nlinarith
  have hg_lo : ∀ x, c / 4 ≤ g x := fun x => by
    by_contra hcon
    push_neg at hcon
    have := hgs_rel x
    have := hgpos x
    nlinarith [hs_lo x]
  have hg_hi : ∀ x, g x ≤ 2 * B + 1 := fun x => by
    by_contra hcon
    push_neg at hcon
    have := hgs_rel x
    have := hgpos x
    nlinarith [hs_hi x]
  -- entropy
  have hent : ∀ x, g x * Real.log (g x) ≤ h x * Real.log (h x) + L * |g x - h x| := fun x => by
    have := d3b_phi_lip (c := c / 4) (B := 2 * B + 1) (x := h x) (y := g x) (by positivity)
      ⟨by linarith [hch x], by linarith [hhB x]⟩ ⟨hg_lo x, hg_hi x⟩
    have e := (abs_le.1 this).2
    rw [hL]; linarith
  have hIh : Integrable (fun x => h x * Real.log (h x)) P :=
    d3b_integrable_of_bdd (hm.mul hm.log) (C := B * (|Real.log c| + |Real.log B|)) fun x =>
      d3b_phi_bdd hc (hch x) (hhB x)
  have hIgh : Integrable (fun x => |g x - h x|) P :=
    d3b_integrable_of_bdd ((hgc.measurable.sub hm).abs) (C := 2 * B + 1 + B) (fun x => by
      rw [abs_abs, abs_le]; constructor <;> linarith [hg_lo x, hg_hi x, hch x, hhB x])
  have hIg : Integrable (fun x => g x * Real.log (g x)) P := d3a_hint P (Real.continuous_mul_log.comp hgc)
  have hmono : ∫ x, g x * Real.log (g x) ∂P ≤ ∫ x, (h x * Real.log (h x) + L * |g x - h x|) ∂P :=
    integral_mono hIg (hIh.add (hIgh.const_mul L)) hent
  rw [integral_add hIh (hIgh.const_mul L), integral_const_mul] at hmono
  refine ⟨g, hgs, hgpos, hgmass, ?_, ?_⟩
  · linarith
  · have : L * ∫ x, |g x - h x| ∂P ≤ L * (4 * ε1) := mul_le_mul_of_nonneg_left hgh (by linarith)
    nlinarith


/-- One truncation step: `a = min f K`, `m = ∫ a`, `h = (1-δ) a/m + δ`. -/
theorem d3b_trunc_step (P : Measure (Torus n)) [IsProbabilityMeasure P] {f : Torus n → ℝ}
    (hm : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hint : Integrable f P) (hmass : ∫ x, f x ∂P = 1)
    (hent : Integrable (fun x => f x * Real.log (f x)) P) {K : ℝ} (hK : 1 ≤ K)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hm0 : 0 < ∫ x, min (f x) K ∂P) :
    ∃ h : Torus n → ℝ, Measurable h ∧ (∀ x, δ ≤ h x) ∧
      (∀ x, h x ≤ (1 - δ) * (K / ∫ x, min (f x) K ∂P) + δ) ∧ ∫ x, h x ∂P = 1 ∧
      ∫ x, |h x - f x| ∂P ≤ 2 * (1 - ∫ x, min (f x) K ∂P) + 2 * δ ∧
      ∫ x, h x * Real.log (h x) ∂P ≤
        (1 - δ) * ((∫ x, f x * Real.log (f x) ∂P) / (∫ x, min (f x) K ∂P) -
          Real.log (∫ x, min (f x) K ∂P)) := by
  set a : Torus n → ℝ := fun x => min (f x) K with ha
  have ham : Measurable a := hm.min measurable_const
  have ha0 : ∀ x, 0 ≤ a x := fun x => le_min (hf0 x) (by linarith)
  have haf : ∀ x, a x ≤ f x := fun x => min_le_left _ _
  have haK : ∀ x, a x ≤ K := fun x => min_le_right _ _
  have hIa : Integrable a P := d3b_integrable_of_bdd ham (C := K) fun x => by
    rw [abs_of_nonneg (ha0 x)]; exact haK x
  set m : ℝ := ∫ x, a x ∂P with hmdef
  have hm1 : m ≤ 1 := by
    have := integral_mono hIa hint haf
    rw [hmass] at this; exact this
  show ∃ h : Torus n → ℝ, Measurable h ∧ (∀ x, δ ≤ h x) ∧
      (∀ x, h x ≤ (1 - δ) * (K / m) + δ) ∧ ∫ x, h x ∂P = 1 ∧
      ∫ x, |h x - f x| ∂P ≤ 2 * (1 - m) + 2 * δ ∧
      ∫ x, h x * Real.log (h x) ∂P ≤ (1 - δ) * ((∫ x, f x * Real.log (f x) ∂P) / m - Real.log m)
  have hm0' : 0 < m := hm0
  set h : Torus n → ℝ := fun x => (1 - δ) * (a x / m) + δ with hh
  have hhm : Measurable h := (measurable_const.mul (ham.div_const m)).add_const δ
  have hlo : ∀ x, δ ≤ h x := fun x => by
    have : 0 ≤ (1 - δ) * (a x / m) := mul_nonneg (by linarith) (div_nonneg (ha0 x) hm0'.le)
    simp only [hh]; linarith
  have hhi : ∀ x, h x ≤ (1 - δ) * (K / m) + δ := fun x => by
    have : a x / m ≤ K / m := div_le_div_of_nonneg_right (haK x) hm0'.le
    simp only [hh]
    have := mul_le_mul_of_nonneg_left this (by linarith : (0 : ℝ) ≤ 1 - δ)
    linarith
  have hpos : ∀ x, 0 < h x := fun x => hδ0.trans_le (hlo x)
  have hIh : Integrable h P := d3b_integrable_of_bdd hhm (C := (1 - δ) * (K / m) + δ) fun x => by
    rw [abs_of_pos (hpos x)]; exact hhi x
  have hmassh : ∫ x, h x ∂P = 1 := by
    simp only [hh]
    rw [integral_add ((hIa.div_const m).const_mul _) (integrable_const δ), integral_const_mul,
      integral_div, ← hmdef, div_self hm0'.ne']
    simp
  have hIf : Integrable (fun x => f x - a x) P := hint.sub hIa
  refine ⟨h, hhm, hlo, hhi, hmassh, ?_, ?_⟩
  · -- L1 estimate
    set C1 : ℝ := |(1 - δ) / m - 1| with hC1
    have hpt : ∀ x, |h x - f x| ≤ C1 * a x + δ + (f x - a x) := fun x => by
      have e : h x - f x = ((1 - δ) / m - 1) * a x + δ + (a x - f x) := by
        simp only [hh]; field_simp; ring
      rw [e]
      have h1 := abs_add_le (((1 - δ) / m - 1) * a x + δ) (a x - f x)
      have h2 := abs_add_le (((1 - δ) / m - 1) * a x) δ
      rw [abs_mul, abs_of_nonneg (ha0 x)] at h2
      rw [abs_sub_comm, abs_of_nonneg (by linarith [haf x] : 0 ≤ f x - a x)] at h1
      rw [abs_of_pos hδ0] at h2
      linarith
    have hA : Integrable (fun x => C1 * a x + δ) P := (hIa.const_mul C1).add (integrable_const δ)
    have hIR : Integrable (fun x => C1 * a x + δ + (f x - a x)) P := hA.add hIf
    refine le_trans (integral_mono_of_nonneg (ae_of_all _ fun x => abs_nonneg _) hIR (ae_of_all _ hpt)) ?_
    rw [integral_add hA hIf,
      integral_add (hIa.const_mul C1) (integrable_const δ), integral_const_mul, integral_const,
      integral_sub hint hIa, hmass, ← hmdef]
    have hCm : C1 * m = |1 - δ - m| := by
      have : (1 - δ) / m - 1 = (1 - δ - m) / m := by field_simp
      rw [hC1, this, abs_div, abs_of_pos hm0']
      field_simp
    have hb : |1 - δ - m| ≤ (1 - m) + δ := by
      rw [abs_le]; constructor <;> linarith
    simp only [probReal_univ, smul_eq_mul, one_mul]
    linarith
  · -- entropy estimate
    set E : ℝ := ∫ x, f x * Real.log (f x) ∂P with hE
    set R2 : Torus n → ℝ := fun x =>
      (1 - δ) * ((1 / m) * (f x * Real.log (f x)) - (a x / m) * Real.log m) with hR2
    have hIR2 : Integrable R2 P := by
      refine Integrable.const_mul (Integrable.sub (hent.const_mul _) ?_) _
      exact (hIa.div_const m).mul_const _
    have hpt : ∀ x, h x * Real.log (h x) ≤ R2 x := fun x => by
      have hu : 0 ≤ a x / m := div_nonneg (ha0 x) hm0'.le
      have hcv := Real.convexOn_mul_log.2 (Set.mem_Ici.2 hu) (Set.mem_Ici.2 (zero_le_one : (0 : ℝ) ≤ 1))
        (by linarith : (0 : ℝ) ≤ 1 - δ) hδ0.le (by ring)
      simp only [smul_eq_mul, Real.log_one, mul_one, mul_zero, add_zero] at hcv
      have hphi : a x / m * Real.log (a x / m) =
          (1 / m) * (a x * Real.log (a x)) - (a x / m) * Real.log m := by
        rcases (ha0 x).eq_or_lt with h0 | h0
        · rw [← h0]; simp
        · rw [Real.log_div h0.ne' hm0'.ne']
          field_simp
      have hmono : a x * Real.log (a x) ≤ f x * Real.log (f x) := by
        rcases le_total (f x) K with hfK | hfK
        · rw [show a x = f x from min_eq_left hfK]
        · rw [show a x = K from min_eq_right hfK]
          exact mul_le_mul hfK (Real.log_le_log (by linarith) hfK)
            (Real.log_nonneg hK) (hf0 x)
      have hb : (1 / m) * (a x * Real.log (a x)) ≤ (1 / m) * (f x * Real.log (f x)) :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
      have h3 : h x * Real.log (h x) ≤ (1 - δ) * (a x / m * Real.log (a x / m)) := by
        simpa only [hh] using hcv
      rw [hphi] at h3
      have h4 := mul_le_mul_of_nonneg_left (sub_le_sub_right hb ((a x / m) * Real.log m))
        (by linarith : (0 : ℝ) ≤ 1 - δ)
      simp only [hR2]
      linarith
    have hIhl : Integrable (fun x => h x * Real.log (h x)) P :=
      d3b_integrable_of_bdd (hhm.mul hhm.log)
        (C := ((1 - δ) * (K / m) + δ) * (|Real.log δ| + |Real.log ((1 - δ) * (K / m) + δ)|))
        fun x => d3b_phi_bdd hδ0 (hlo x) (hhi x)
    refine le_trans (integral_mono hIhl hIR2 hpt) (le_of_eq ?_)
    simp only [hR2]
    rw [integral_const_mul, integral_sub (hent.const_mul _) ((hIa.div_const m).mul_const _),
      integral_const_mul, integral_mul_const, integral_div, ← hmdef, div_self hm0'.ne']
    ring


/-- Truncation + positivity shift: bounded positive densities approximating `f` in `L¹` and entropy. -/
theorem d3b_trunc_approx (P : Measure (Torus n)) [IsProbabilityMeasure P] {f : Torus n → ℝ}
    (hm : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hint : Integrable f P) (hmass : ∫ x, f x ∂P = 1)
    (hent : Integrable (fun x => f x * Real.log (f x)) P) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : Torus n → ℝ, Measurable h ∧ ∃ c B : ℝ, 0 < c ∧ (∀ x, c ≤ h x) ∧ (∀ x, h x ≤ B) ∧
      ∫ x, h x ∂P = 1 ∧ ∫ x, |h x - f x| ∂P ≤ ε ∧
      ∫ x, h x * Real.log (h x) ∂P ≤ ∫ x, f x * Real.log (f x) ∂P + ε := by
  set E : ℝ := ∫ x, f x * Real.log (f x) ∂P with hE
  set m : ℕ → ℝ := fun k => ∫ x, min (f x) ((k : ℝ) + 1) ∂P with hmk
  have hmT : Tendsto m atTop (𝓝 1) := by
    have := tendsto_integral_of_dominated_convergence (μ := P)
      (F := fun (k : ℕ) x => min (f x) ((k : ℝ) + 1)) (f := f) (bound := f)
      (fun k => (hm.min measurable_const).aestronglyMeasurable) hint
      (fun k => ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hf0 x) (by positivity))]
        exact min_le_left _ _)
      (ae_of_all _ fun x => by
        obtain ⟨N, hN⟩ := exists_nat_ge (f x)
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop N] with k hk
        exact (min_eq_left (hN.trans ((Nat.cast_le.2 hk).trans (by linarith)))).symm)
    rwa [hmass] at this
  set δ : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hδdef
  have hδT : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hb1 : Tendsto (fun k => 2 * (1 - m k) + 2 * δ k) atTop (𝓝 0) := by
    have : Tendsto (fun k => 2 * (1 - m k) + 2 * δ k) atTop (𝓝 (2 * (1 - 1) + 2 * 0)) :=
      (((tendsto_const_nhds (x := (1 : ℝ))).sub hmT).const_mul (2 : ℝ)).add (hδT.const_mul (2 : ℝ))
    simpa using this
  have hb2 : Tendsto (fun k => (1 - δ k) * (E / m k - Real.log (m k))) atTop (𝓝 E) := by
    have : Tendsto (fun k => (1 - δ k) * (E / m k - Real.log (m k))) atTop
        (𝓝 ((1 - 0) * (E / 1 - Real.log 1))) :=
      ((tendsto_const_nhds (x := (1 : ℝ))).sub hδT).mul
        (((tendsto_const_nhds (x := E)).div hmT one_ne_zero).sub (hmT.log one_ne_zero))
    simpa using this
  have e1 : ∀ᶠ k in atTop, 2 * (1 - m k) + 2 * δ k < ε := hb1.eventually (gt_mem_nhds hε)
  have e2 : ∀ᶠ k in atTop, (1 - δ k) * (E / m k - Real.log (m k)) < E + ε :=
    hb2.eventually (gt_mem_nhds (by linarith))
  have e3 : ∀ᶠ k in atTop, 0 < m k := hmT.eventually (lt_mem_nhds one_pos)
  have e4 : ∀ᶠ k in atTop, δ k < 1 := hδT.eventually (gt_mem_nhds one_pos)
  obtain ⟨k, hk⟩ := (e1.and (e2.and (e3.and e4))).exists
  obtain ⟨hk1, hk2, hk3, hk4⟩ := hk
  have hδpos : 0 < δ k := by simp only [hδdef]; positivity
  obtain ⟨h, hhm, hlo, hhi, hmass', hL1, hent'⟩ := d3b_trunc_step P hm hf0 hint hmass hent
    (K := (k : ℝ) + 1) (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) hδpos hk4 hk3
  exact ⟨h, hhm, δ k, (1 - δ k) * (((k : ℝ) + 1) / m k) + δ k, hδpos, hlo, hhi, hmass',
    hL1.trans hk1.le, hent'.trans hk2.le⟩

/-- Smooth positive normalised approximation of a finite-entropy density. -/
theorem d3b_approx_density (P : Measure (Torus n)) [IsProbabilityMeasure P] {f : Torus n → ℝ}
    (hm : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hint : Integrable f P) (hmass : ∫ x, f x ∂P = 1)
    (hent : Integrable (fun x => f x * Real.log (f x)) P) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : Torus n → ℝ, Torus.IsSmooth g ∧ (∀ x, 0 < g x) ∧ ∫ x, g x ∂P = 1 ∧
      ∫ x, |g x - f x| ∂P ≤ ε ∧
      ∫ x, g x * Real.log (g x) ∂P ≤ ∫ x, f x * Real.log (f x) ∂P + ε := by
  obtain ⟨h, hhm, c, B, hc, hch, hhB, hmh, hL1, hE⟩ := d3b_trunc_approx P hm hf0 hint hmass hent
    (half_pos hε)
  obtain ⟨g, hgs, hgpos, hgmass, hgL1, hgE⟩ := d3b_smooth_approx_bdd P hhm hc hch hhB hmh (half_pos hε)
  refine ⟨g, hgs, hgpos, hgmass, ?_, by linarith⟩
  have hIh : Integrable h P := d3b_integrable_of_bdd hhm (C := B) fun x => by
    rw [abs_of_pos (hc.trans_le (hch x))]; exact hhB x
  have hIg : Integrable g P := d3a_hint P (d1c_continuous_of_isSmooth hgs)
  have hA : Integrable (fun x => |g x - h x|) P := (hIg.sub hIh).abs
  have hB : Integrable (fun x => |h x - f x|) P := (hIh.sub hint).abs
  have h1 : ∫ x, |g x - f x| ∂P ≤ ∫ x, (|g x - h x| + |h x - f x|) ∂P :=
    integral_mono_of_nonneg (ae_of_all _ fun x => abs_nonneg _) (hA.add hB)
      (ae_of_all _ fun x => by simpa using abs_add_le (g x - h x) (h x - f x))
  rw [integral_add hA hB] at h1
  linarith

/-- Entropy-recovering smooth positive approximants of a probability measure of finite relative entropy. -/
theorem d3b_approx_measure (P : Measure (Torus n)) [IsProbabilityMeasure P] (μ0 : Measure (Torus n))
    [IsProbabilityMeasure μ0] (hfin : relEntropy μ0 P ≠ ⊤) :
    ∃ g : ℕ → Torus n → ℝ, (∀ k, Torus.IsSmooth (g k)) ∧ (∀ k x, 0 < g k x) ∧
      (∀ k, ∫ x, g k x ∂P = 1) ∧
      (∀ φ : Torus n → ℝ, Continuous φ →
        Tendsto (fun k => ∫ x, φ x ∂(P.withDensity fun x => ENNReal.ofReal (g k x))) atTop
          (𝓝 (∫ x, φ x ∂μ0))) ∧
      (∀ k, (relEntropy (P.withDensity fun x => ENNReal.ofReal (g k x)) P).toReal ≤
        (relEntropy μ0 P).toReal + 1 / ((k : ℝ) + 1)) := by
  have hkl := InformationTheory.klDiv_ne_top_iff.1 hfin
  have hac : μ0 ≪ P := hkl.1
  set f : Torus n → ℝ := fun x => (μ0.rnDeriv P x).toReal with hf
  have hfm : Measurable f := (Measure.measurable_rnDeriv μ0 P).ennreal_toReal
  have hf0 : ∀ x, 0 ≤ f x := fun x => ENNReal.toReal_nonneg
  have hint : Integrable f P := Measure.integrable_toReal_rnDeriv
  have hmass : ∫ x, f x ∂P = 1 := by
    rw [hf, Measure.integral_toReal_rnDeriv hac]; simp
  have hent : Integrable (fun x => f x * Real.log (f x)) P :=
    (integrable_toReal_rnDeriv_mul_iff hac (f := fun x => Real.log (f x))).2 hkl.2
  have hE : ∫ x, f x * Real.log (f x) ∂P = (relEntropy μ0 P).toReal := by
    unfold relEntropy
    rw [InformationTheory.toReal_klDiv_of_measure_eq hac (by simp)]
    exact integral_toReal_rnDeriv_mul hac (f := fun x => Real.log (f x))
  have hconv : ∀ φ : Torus n → ℝ, ∫ x, φ x ∂μ0 = ∫ x, f x * φ x ∂P := fun φ =>
    (integral_toReal_rnDeriv_mul hac (f := φ)).symm
  have hex : ∀ k : ℕ, ∃ g : Torus n → ℝ, Torus.IsSmooth g ∧ (∀ x, 0 < g x) ∧ ∫ x, g x ∂P = 1 ∧
      ∫ x, |g x - f x| ∂P ≤ 1 / ((k : ℝ) + 1) ∧
      ∫ x, g x * Real.log (g x) ∂P ≤ ∫ x, f x * Real.log (f x) ∂P + 1 / ((k : ℝ) + 1) :=
    fun k => d3b_approx_density P hfm hf0 hint hmass hent (by positivity)
  choose g hgs hgpos hgmass hgL1 hgE using hex
  refine ⟨g, hgs, hgpos, hgmass, ?_, ?_⟩
  · intro φ hφ
    obtain ⟨M, hM⟩ := (isCompact_univ (X := Torus n)).exists_bound_of_continuousOn hφ.continuousOn
    have hM' : ∀ x, |φ x| ≤ M := fun x => by simpa [Real.norm_eq_abs] using hM x (Set.mem_univ x)
    have hwd : ∀ k, ∫ x, φ x ∂(P.withDensity fun x => ENNReal.ofReal (g k x)) =
        ∫ x, g k x * φ x ∂P := fun k =>
      d3a_integral_withDensity (d1c_continuous_of_isSmooth (hgs k)).measurable
        (fun x => (hgpos k x).le) φ
    simp_rw [hwd, hconv]
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM' (Classical.arbitrary _))
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_)
      (show Tendsto (fun k : ℕ => M * (1 / ((k : ℝ) + 1))) atTop (𝓝 0) by
        simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul M)
    have hIφ : Integrable (fun x => φ x) P := d3a_hint P hφ
    have hI1 : Integrable (fun x => g k x * φ x) P :=
      d3a_hint P ((d1c_continuous_of_isSmooth (hgs k)).mul hφ)
    have hI2 : Integrable (fun x => f x * φ x) P := by
      refine Integrable.mono' (hint.norm.mul_const M)
        ((hfm.mul hφ.measurable).aestronglyMeasurable) (ae_of_all _ fun x => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hf0 x)]
      calc f x * |φ x| ≤ f x * M := mul_le_mul_of_nonneg_left (hM' x) (hf0 x)
        _ = ‖f x‖ * M := by rw [Real.norm_eq_abs, abs_of_nonneg (hf0 x)]
    rw [Real.norm_eq_abs, ← integral_sub hI1 hI2]
    have hIg : Integrable (fun x => |g k x - f x|) P :=
      (d3a_hint P (d1c_continuous_of_isSmooth (hgs k)) |>.sub hint).abs
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ x, |g k x * φ x - f x * φ x| ∂P ≤ ∫ x, M * |g k x - f x| ∂P := by
          refine integral_mono_of_nonneg (ae_of_all _ fun x => abs_nonneg _) (hIg.const_mul M)
            (ae_of_all _ fun x => ?_)
          beta_reduce
          rw [← sub_mul, abs_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right (hM' x) (abs_nonneg _) |>.trans (le_of_eq (by ring))
      _ = M * ∫ x, |g k x - f x| ∂P := integral_const_mul _ _
      _ ≤ M * (1 / ((k : ℝ) + 1)) := mul_le_mul_of_nonneg_left (hgL1 k) hM0
  · intro k
    have hcont := d1c_continuous_of_isSmooth (hgs k)
    rw [d3a_relEntropy_toReal hcont (hgpos k) (hgmass k), ← hE]
    exact hgE k

end HRS

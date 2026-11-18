import HRS.Sections.ScrnAux11

/-!
# Packet SCRN, part 12: positive semidefiniteness of the limiting covariance kernels

`e^{-A|t-u|}` is a positive semidefinite kernel (`e^{2A min(t,u)} - 1 = ∫_0^{min} 2A e^{2As} ds`, a Gram form),
hence `scrnk = S e^{-A|t-u|} + (1-S) e^{-A(t+u)}` and `S e^{-A|t-u|}` are, and so are `mesoCovMatrix` and
`mesoStatCovMatrix` (`scrn_mesoCov_psd`, `scrn_mesoStatCov_psd`).
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal FourierTransform ComplexConjugate

namespace HRS

lemma scrn_int_exp (A m : ℝ) (hm : 0 ≤ m) :
    ∫ s in (0 : ℝ)..m, 2 * A * Real.exp (2 * A * s) = Real.exp (2 * A * m) - 1 := by
  have hd : ∀ x ∈ Set.uIcc (0 : ℝ) m, HasDerivAt (fun s => Real.exp (2 * A * s))
      (2 * A * Real.exp (2 * A * x)) x := by
    intro x _
    have := ((hasDerivAt_id x).const_mul (2 * A)).exp
    simpa [mul_comm] using this
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _)
  simpa using this

/-- `∫_0^T 2A e^{2As} 1_{s ≤ t_a} 1_{s ≤ t_c} ds = e^{2A min} - 1`. -/
lemma scrn_int_ind (A T x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hxT : x ≤ T) (hyT : y ≤ T) :
    ∫ s in (0 : ℝ)..T, 2 * A * Real.exp (2 * A * s) *
      ((if s ≤ x then (1 : ℝ) else 0) * (if s ≤ y then (1 : ℝ) else 0)) =
      Real.exp (2 * A * min x y) - 1 := by
  set m := min x y with hm
  have hm0 : 0 ≤ m := le_min hx hy
  have hmT : m ≤ T := (min_le_left _ _).trans hxT
  have hT0 : 0 ≤ T := hm0.trans hmT
  set f : ℝ → ℝ := fun s => 2 * A * Real.exp (2 * A * s) with hf
  have hpt : ∀ s : ℝ, f s * ((if s ≤ x then (1 : ℝ) else 0) * (if s ≤ y then (1 : ℝ) else 0)) =
      (Set.Iic m).indicator f s := by
    intro s
    by_cases h : s ≤ m
    · have hx' : s ≤ x := h.trans (min_le_left _ _)
      have hy' : s ≤ y := h.trans (min_le_right _ _)
      rw [Set.indicator_of_mem (show s ∈ Set.Iic m from h), if_pos hx', if_pos hy']
      ring
    · have hn : s ∉ Set.Iic m := h
      rw [Set.indicator_of_notMem hn]
      by_cases hx' : s ≤ x
      · have hy' : ¬ s ≤ y := fun hh => h (le_min hx' hh)
        rw [if_pos hx', if_neg hy']; ring
      · rw [if_neg hx']; ring
  rw [intervalIntegral.integral_congr (g := fun s => (Set.Iic m).indicator f s)
    (fun s _ => hpt s)]
  rw [intervalIntegral.integral_of_le hT0, setIntegral_indicator measurableSet_Iic]
  have hset : Set.Ioc (0 : ℝ) T ∩ Set.Iic m = Set.Ioc 0 m := by
    ext s; simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iic]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.trans hmT⟩, h2⟩
  rw [hset, ← intervalIntegral.integral_of_le hm0]
  exact scrn_int_exp A m hm0


lemma scrn_int_ind_integrable (A T x y : ℝ) (hT0 : 0 ≤ T) :
    IntervalIntegrable (fun s : ℝ => 2 * A * Real.exp (2 * A * s) *
      ((if s ≤ x then (1 : ℝ) else 0) * (if s ≤ y then (1 : ℝ) else 0))) volume 0 T := by
  set f : ℝ → ℝ := fun s => 2 * A * Real.exp (2 * A * s) with hf
  have hcont : Continuous f := by fun_prop
  have hpt : ∀ s : ℝ, f s * ((if s ≤ x then (1 : ℝ) else 0) * (if s ≤ y then (1 : ℝ) else 0)) =
      (Set.Iic (min x y)).indicator f s := by
    intro s
    by_cases h : s ≤ min x y
    · have hx' : s ≤ x := h.trans (min_le_left _ _)
      have hy' : s ≤ y := h.trans (min_le_right _ _)
      rw [Set.indicator_of_mem (show s ∈ Set.Iic (min x y) from h), if_pos hx', if_pos hy']
      ring
    · have hn : s ∉ Set.Iic (min x y) := h
      rw [Set.indicator_of_notMem hn]
      by_cases hx' : s ≤ x
      · have hy' : ¬ s ≤ y := fun hh => h (le_min hx' hh)
        rw [if_pos hx', if_neg hy']; ring
      · rw [if_neg hx']; ring
  have : (fun s : ℝ => 2 * A * Real.exp (2 * A * s) *
      ((if s ≤ x then (1 : ℝ) else 0) * (if s ≤ y then (1 : ℝ) else 0))) =
      (Set.Iic (min x y)).indicator f := funext hpt
  rw [this]
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT0]
  exact (hcont.integrableOn_Ioc).indicator measurableSet_Iic

lemma scrn_ou_psd {p : ℕ} (A : ℝ) (hA : 0 ≤ A) (t : Fin p → ℝ) (ht : ∀ a, 0 ≤ t a) (y : Fin p → ℝ) :
    0 ≤ ∑ a, ∑ c, y a * y c * Real.exp (-A * |t a - t c|) := by
  set T : ℝ := ∑ a, t a with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun a _ => ht a
  have htT : ∀ a, t a ≤ T := fun a =>
    Finset.single_le_sum (f := t) (fun a _ => ht a) (Finset.mem_univ a)
  set w : Fin p → ℝ := fun a => y a * Real.exp (-A * t a) with hw
  set ind : Fin p → ℝ → ℝ := fun a s => if s ≤ t a then (1 : ℝ) else 0 with hind
  set I : Fin p → Fin p → ℝ := fun a c => ∫ s in (0 : ℝ)..T, 2 * A * Real.exp (2 * A * s) *
    (ind a s * ind c s) with hI
  have hkey : ∀ a c, y a * y c * Real.exp (-A * |t a - t c|) = w a * w c * (1 + I a c) := by
    intro a c
    have h1 : I a c = Real.exp (2 * A * min (t a) (t c)) - 1 :=
      scrn_int_ind A T (t a) (t c) (ht a) (ht c) (htT a) (htT c)
    rw [h1]
    have h2 : -A * |t a - t c| = -A * t a + (-A * t c) + 2 * A * min (t a) (t c) := by
      rcases le_total (t a) (t c) with h | h
      · rw [abs_of_nonpos (by linarith), min_eq_left h]; ring
      · rw [abs_of_nonneg (by linarith), min_eq_right h]; ring
    simp only [hw]
    rw [h2, Real.exp_add, Real.exp_add]
    ring
  simp_rw [hkey]
  have hsum : ∑ a, ∑ c, w a * w c * (1 + I a c) =
      (∑ a, w a) ^ 2 + ∫ s in (0 : ℝ)..T, 2 * A * Real.exp (2 * A * s) * (∑ a, w a * ind a s) ^ 2 := by
    have e1 : ∀ a c, w a * w c * (1 + I a c) = w a * w c + w a * w c * I a c := fun a c => by ring
    simp_rw [e1, Finset.sum_add_distrib]
    congr 1
    · rw [sq, Finset.sum_mul_sum]
    · have e2 : ∀ s : ℝ, 2 * A * Real.exp (2 * A * s) * (∑ a, w a * ind a s) ^ 2 =
          ∑ a, ∑ c, w a * w c * (2 * A * Real.exp (2 * A * s) * (ind a s * ind c s)) := by
        intro s
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        ring
      simp_rw [e2]
      rw [intervalIntegral.integral_finset_sum]
      · refine Finset.sum_congr rfl fun a _ => ?_
        rw [intervalIntegral.integral_finset_sum]
        · refine Finset.sum_congr rfl fun c _ => ?_
          rw [intervalIntegral.integral_const_mul]
        · intro c _
          exact (scrn_int_ind_integrable A T (t a) (t c) hT0).const_mul _
      · intro a _
        have := IntervalIntegrable.sum (μ := volume) (a := (0 : ℝ)) (b := T) Finset.univ
          (f := fun c : Fin p => fun s : ℝ => w a * w c * (2 * A * Real.exp (2 * A * s) *
            (ind a s * ind c s))) (fun c _ =>
            (scrn_int_ind_integrable A T (t a) (t c) hT0).const_mul (w a * w c))
        simpa [Finset.sum_fn] using this
  rw [hsum]
  refine add_nonneg (sq_nonneg _) (intervalIntegral.integral_nonneg hT0 fun s _ => ?_)
  have : 0 ≤ 2 * A * Real.exp (2 * A * s) := by positivity
  positivity


lemma scrnk_psd {c q b ρ : ℝ} (hc : 0 < c) (hb : 0 < b) (hρ : 0 ≤ ρ) {p : ℕ} (t : Fin p → ℝ)
    (ht : ∀ a, 0 ≤ t a) (y : Fin p → ℝ) :
    0 ≤ ∑ a, ∑ c', y a * y c' * scrnk c q b |t a - t c'| (t a + t c') ρ := by
  set S := scrnS c q b ρ with hS
  set A := scrnA c q b ρ with hA
  have hS0 : 0 ≤ S := scrnS_nonneg' hc hb hρ
  have hS1 : S < 1 := scrnS_lt_one' hc hb hρ
  have hA0 : 0 ≤ A := scrnA_nonneg' hc hb hρ
  have e : ∀ a c', y a * y c' * scrnk c q b |t a - t c'| (t a + t c') ρ =
      S * (y a * y c' * Real.exp (-A * |t a - t c'|)) +
        (1 - S) * ((y a * Real.exp (-A * t a)) * (y c' * Real.exp (-A * t c'))) := by
    intro a c'
    unfold scrnk
    rw [← hS, ← hA]
    have : Real.exp (-(t a + t c') * A) = Real.exp (-A * t a) * Real.exp (-A * t c') := by
      rw [← Real.exp_add]; congr 1; ring
    rw [this]
    have h2 : Real.exp (-|t a - t c'| * A) = Real.exp (-A * |t a - t c'|) := by congr 1; ring
    rw [h2]
    ring
  have h1 := scrn_ou_psd A hA0 t ht y
  have h2 : ∑ a, ∑ c', (y a * Real.exp (-A * t a)) * (y c' * Real.exp (-A * t c')) =
      (∑ a, y a * Real.exp (-A * t a)) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
  have hsplit : ∑ a, ∑ c', y a * y c' * scrnk c q b |t a - t c'| (t a + t c') ρ =
      S * (∑ a, ∑ c', y a * y c' * Real.exp (-A * |t a - t c'|)) +
        (1 - S) * ∑ a, ∑ c', (y a * Real.exp (-A * t a)) * (y c' * Real.exp (-A * t c')) := by
    simp_rw [e, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hsplit, h2]
  have : 0 ≤ 1 - S := by linarith
  positivity

lemma scrnkStat_psd {c q b ρ : ℝ} (hc : 0 < c) (hb : 0 < b) (hρ : 0 ≤ ρ) {p : ℕ} (t : Fin p → ℝ)
    (ht : ∀ a, 0 ≤ t a) (y : Fin p → ℝ) :
    0 ≤ ∑ a, ∑ c', y a * y c' * (scrnS c q b ρ * Real.exp (-|t a - t c'| * scrnA c q b ρ)) := by
  have hS0 : 0 ≤ scrnS c q b ρ := scrnS_nonneg' hc hb hρ
  have hA0 : 0 ≤ scrnA c q b ρ := scrnA_nonneg' hc hb hρ
  have e : ∀ a c', y a * y c' * (scrnS c q b ρ * Real.exp (-|t a - t c'| * scrnA c q b ρ)) =
      scrnS c q b ρ * (y a * y c' * Real.exp (-(scrnA c q b ρ) * |t a - t c'|)) := by
    intro a c'
    have : Real.exp (-|t a - t c'| * scrnA c q b ρ) = Real.exp (-(scrnA c q b ρ) * |t a - t c'|) := by
      congr 1; ring
    rw [this]; ring
  simp_rw [e, ← Finset.mul_sum]
  exact mul_nonneg hS0 (scrn_ou_psd _ hA0 t ht y)

end HRS

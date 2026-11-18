import HRS.PDE.TorusFPEntropyClassicalAux2

/-!
# D3-a (classical layer), helper 3: existence of the positive classical solution and the weak formulation

* `d3a_exists`: time reversal of `d1_backward_classical` and a strict minimum principle
  (`w r x ≥ min w0 > 0`, from `d1_backward_nonneg` applied to `f - min w0`);
* `d3a_isWeak`: `s ↦ P.withDensity (w s)` is a `D1WeakSolution` (integrated product rule `d3a_ftc` and the
  `G`-self-adjointness `d3a_selfadj`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS

variable {n : ℕ}

theorem d3a_exists (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)
    {T : ℝ} (hT : 0 < T) {w0 : Torus n → ℝ} (hw0 : Torus.IsSmooth w0) (hpos : ∀ x, 0 < w0 x) :
    ∃ w : ℝ → Torus n → ℝ, D3Classical κ U T w ∧ w 0 = w0 := by
  obtain ⟨f, hf⟩ := d1_backward_classical hn hκ hU hT hw0
  have hmem : ∀ r ∈ Set.Icc (0 : ℝ) T, T - r ∈ Set.Icc (0 : ℝ) T := fun r hr =>
    ⟨by linarith [hr.2], by linarith [hr.1]⟩
  have hrefl : Continuous fun p : Set.Icc (0 : ℝ) T => (⟨T - p.1, hmem p.1 p.2⟩ : Set.Icc (0 : ℝ) T) :=
    Continuous.subtype_mk (continuous_const.sub continuous_subtype_val) _
  obtain ⟨x0, -, hx0'⟩ := (isCompact_univ (X := Torus n)).exists_isMinOn Set.univ_nonempty
    (d1c_continuous_of_isSmooth hw0).continuousOn
  have hx0 : ∀ x, w0 x0 ≤ w0 x := fun x => hx0' (Set.mem_univ x)
  have hs := hf.lincomb (D1BackwardSolution.const κ (d1_gradDrift U) T (w0 x0)) 1 (-1)
  have hnn := d1_backward_nonneg hκ hT hs (fun x => by
    show 0 ≤ 1 * w0 x + -1 * w0 x0
    linarith [hx0 x])
  have hlow : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x, w0 x0 ≤ f r x := by
    intro r hr x
    have := hnn r hr x
    change 0 ≤ 1 * f r x + -1 * w0 x0 at this
    linarith
  refine ⟨fun r => f (T - r), ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · intro r hr
    exact hf.c2 (T - r) (hmem r hr)
  · intro j hj
    have hm2 : Continuous fun p : Set.Icc (0 : ℝ) T × Euc n =>
        ((⟨T - p.1.1, hmem p.1.1 p.1.2⟩ : Set.Icc (0 : ℝ) T), p.2) :=
      hrefl.fst'.prodMk continuous_snd
    exact Continuous.comp (g := fun q : Set.Icc (0 : ℝ) T × Euc n =>
      iteratedFDeriv ℝ j (Torus.lift (f q.1)) q.2) (hf.cont_c2 j hj) hm2
  · intro x r hr
    have h1 := hf.time_deriv x (T - r) ⟨by linarith [hr.2], by linarith [hr.1]⟩
    have h2 : HasDerivAt (fun r : ℝ => T - r) (-1) r := by
      simpa using (hasDerivAt_id r).const_sub T
    have h3 := h1.comp r h2
    exact h3.congr_deriv (by ring)
  · have hm2 : Continuous fun p : Set.Icc (0 : ℝ) T × Torus n =>
        ((⟨T - p.1.1, hmem p.1.1 p.1.2⟩ : Set.Icc (0 : ℝ) T), p.2) :=
      hrefl.fst'.prodMk continuous_snd
    have key := hf.cont_time_deriv.comp hm2
    refine key.congr fun p => ?_
    rfl
  · intro r hr x
    have h := hlow (T - r) (hmem r hr) x
    have hm : 0 < w0 x0 := hpos x0
    show 0 < f (T - r) x
    linarith
  · funext x
    show f (T - 0) x = w0 x
    rw [sub_zero, hf.terminal]

theorem d3a_isWeak (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)
    {T : ℝ} {w : ℝ → Torus n → ℝ} (hw : D3Classical κ U T w) :
    D1WeakSolution κ (d1_gradDrift U) T
      (fun s => (d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (w s x)) := by
  haveI hP := d3a_gibbs_isProb (κ := κ) hU
  have hwc : Continuous fun p : Set.Icc (0 : ℝ) T × Torus n => w p.1 p.2 := hw.c12.continuous_f
  have hconv : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ g : Torus n → ℝ,
      ∫ x, g x ∂((d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (w r x)) =
        ∫ x, w r x * g x ∂(d1_gibbsMeasure κ U) := fun r hr g =>
    d3a_integral_withDensity (d3a_contOn_space hwc hr).measurable (fun x => (hw.pos r hr x).le) g
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    have hc := d3a_contOn_space hwc ht
    exact isFiniteMeasure_withDensity_ofReal (d1_integrable_of_continuous _ hc).hasFiniteIntegral
  · intro ψ hψ
    have hH : Continuous fun p : Set.Icc (0 : ℝ) T × Torus n => w p.1 p.2 * ψ p.2 :=
      hwc.mul (hψ.comp continuous_snd)
    refine (d3a_continuousOn_integral (ν := d1_gibbsMeasure κ U) (H := fun s x => w s x * ψ x)
      hH).congr fun t ht => ?_
    exact hconv t ht ψ
  · intro τ hτ f ft hf
    rcases hτ.1.eq_or_lt with rfl | hτpos
    · simp
    have hwτ : IsC12Test τ w (fun r x => d1_gen κ (d1_gradDrift U) (w r) x) :=
      d3a_C12_restrict hw.c12 hτ
    have hb := d1_gradDrift_continuous hU
    have hmemT : ∀ r ∈ Set.Icc (0 : ℝ) τ, r ∈ Set.Icc (0 : ℝ) T := fun r hr =>
      ⟨hr.1, hr.2.trans hτ.2⟩
    have hwcτ : Continuous fun p : Set.Icc (0 : ℝ) τ × Torus n => w p.1 p.2 := hwτ.continuous_f
    have hfc : Continuous fun p : Set.Icc (0 : ℝ) τ × Torus n => f p.1 p.2 := hf.continuous_f
    have hLw : Continuous fun p : Set.Icc (0 : ℝ) τ × Torus n =>
        d1_gen κ (d1_gradDrift U) (w p.1) p.2 := hwτ.cont_time_deriv
    have hftc : Continuous fun p : Set.Icc (0 : ℝ) τ × Torus n => ft p.1 p.2 := hf.cont_time_deriv
    have hLf : Continuous fun p : Set.Icc (0 : ℝ) τ × Torus n =>
        d1_gen κ (d1_gradDrift U) (f p.1) p.2 := hf.continuous_gen hb
    have hF : Continuous fun p : Set.Icc (0 : ℝ) τ × Torus n => w p.1 p.2 * f p.1 p.2 :=
      hwcτ.mul hfc
    have hD : Continuous fun p : Set.Icc (0 : ℝ) τ × Torus n =>
        d1_gen κ (d1_gradDrift U) (w p.1) p.2 * f p.1 p.2 + w p.1 p.2 * ft p.1 p.2 :=
      (hLw.mul hfc).add (hwcτ.mul hftc)
    have hder : ∀ x : Torus n, ∀ r ∈ Set.Ioo (0 : ℝ) τ,
        HasDerivAt (fun s => w s x * f s x)
          (d1_gen κ (d1_gradDrift U) (w r) x * f r x + w r x * ft r x) r :=
      fun x r hr => (hwτ.time_deriv x r hr).mul (hf.time_deriv x r hr)
    have key : (∫ x, w τ x * f τ x ∂(d1_gibbsMeasure κ U)) -
        ∫ x, w 0 x * f 0 x ∂(d1_gibbsMeasure κ U) =
        ∫ r in Set.Icc (0 : ℝ) τ, ∫ x, (d1_gen κ (d1_gradDrift U) (w r) x * f r x +
          w r x * ft r x) ∂(d1_gibbsMeasure κ U) :=
      d3a_ftc (ν := d1_gibbsMeasure κ U) hτpos
        (F := fun r x => w r x * f r x)
        (D := fun r x => d1_gen κ (d1_gradDrift U) (w r) x * f r x + w r x * ft r x) hF hD hder
    have hτI : τ ∈ Set.Icc (0 : ℝ) T := hτ
    have h0I : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hτpos.le.trans hτ.2⟩
    have hinner : ∀ r ∈ Set.Icc (0 : ℝ) τ,
        ∫ x, (d1_gen κ (d1_gradDrift U) (w r) x * f r x + w r x * ft r x)
          ∂(d1_gibbsMeasure κ U) =
        ∫ x, (ft r x + d1_gen κ (d1_gradDrift U) (f r) x)
          ∂((d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (w r x)) := by
      intro r hr
      have hrT := hmemT r hr
      rw [hconv r hrT]
      have hc1 : Continuous fun x => d1_gen κ (d1_gradDrift U) (w r) x * f r x :=
        (d3a_contOn_space (F := fun r x => d1_gen κ (d1_gradDrift U) (w r) x) hLw hr).mul
          (d3a_contOn_space (F := f) hfc hr)
      have hc2 : Continuous fun x => w r x * ft r x :=
        (d3a_contOn_space (F := w) hwcτ hr).mul (d3a_contOn_space (F := ft) hftc hr)
      have hc4 : Continuous fun x => d1_gen κ (d1_gradDrift U) (f r) x * w r x :=
        (d3a_contOn_space (F := fun r x => d1_gen κ (d1_gradDrift U) (f r) x) hLf hr).mul
          (d3a_contOn_space (F := w) hwcτ hr)
      calc ∫ x, (d1_gen κ (d1_gradDrift U) (w r) x * f r x + w r x * ft r x)
            ∂(d1_gibbsMeasure κ U)
          = ∫ x, d1_gen κ (d1_gradDrift U) (w r) x * f r x ∂(d1_gibbsMeasure κ U) +
            ∫ x, w r x * ft r x ∂(d1_gibbsMeasure κ U) :=
            integral_add (d3a_hint _ hc1) (d3a_hint _ hc2)
        _ = ∫ x, d1_gen κ (d1_gradDrift U) (f r) x * w r x ∂(d1_gibbsMeasure κ U) +
            ∫ x, w r x * ft r x ∂(d1_gibbsMeasure κ U) := by
            rw [d3a_selfadj hκ hU (hf.c2 r hr) (hwτ.c2 r hr)]
        _ = ∫ x, (d1_gen κ (d1_gradDrift U) (f r) x * w r x + w r x * ft r x)
            ∂(d1_gibbsMeasure κ U) := (integral_add (d3a_hint _ hc4) (d3a_hint _ hc2)).symm
        _ = ∫ x, w r x * (ft r x + d1_gen κ (d1_gradDrift U) (f r) x) ∂(d1_gibbsMeasure κ U) := by
            refine integral_congr_ae (ae_of_all _ fun x => ?_)
            ring
    have hset : ∫ s in Set.Icc (0 : ℝ) τ, ∫ x, (ft s x + d1_gen κ (d1_gradDrift U) (f s) x)
          ∂((d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (w s x)) =
        ∫ r in Set.Icc (0 : ℝ) τ, ∫ x, (d1_gen κ (d1_gradDrift U) (w r) x * f r x +
          w r x * ft r x) ∂(d1_gibbsMeasure κ U) :=
      setIntegral_congr_fun measurableSet_Icc fun r hr => (hinner r hr).symm
    show ∫ x, f τ x ∂((d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (w τ x)) =
      ∫ x, f 0 x ∂((d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (w 0 x)) +
        ∫ s in Set.Icc (0 : ℝ) τ, ∫ x, (ft s x + d1_gen κ (d1_gradDrift U) (f s) x)
          ∂((d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (w s x))
    rw [hset, ← key, hconv τ hτI (f τ), hconv 0 h0I (f 0)]
    ring

end HRS

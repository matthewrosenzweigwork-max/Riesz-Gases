import HRS.MS.ShiftFldCond2
import HRS.MD.EQLawPath1
import HRS.Stochastic.Bridge

/-!
# S79P: the time-shifted canonical realization (prefix `s79p_`)

For a canonical realization `(P, X₀, W, X)` and `u : ℝ≥0` the shifted data `(X u, W_{u+·} - W_u, X_{u+·})` satisfy the hypotheses of
S2.1(i) (`IsVectorBrownian`, independence of the initial datum, the Gibbs law of the initial datum, `IsWholeStrongSolution` on every
horizon).  This replaces the (unprovable without weak uniqueness) `ParticleWindowStationary`: the shifted window `ζ_N^{a₀+·}` of `X` is
literally the window `ζ_N^{0+·}` of the shifted solution (`zetaPathW_shift`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Whole.S79

open HRS (Euc)

variable {d N : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The shifted driving noise `W_{u+t} - W_u`. -/
def s79p_shiftW (u : ℝ≥0) (W : ℝ≥0 → Ω → (Fin N → Euc d)) : ℝ≥0 → Ω → (Fin N → Euc d) :=
  fun t ζ => W (u + t) ζ - W u ζ

/-- The shifted solution `X_{u+t}`. -/
def s79p_shiftX (u : ℝ≥0) (X : ℝ≥0 → Ω → EucConfig d N) : ℝ≥0 → Ω → EucConfig d N :=
  fun t ζ => X (u + t) ζ

theorem s79p_isVectorBrownian_shift {P : Measure Ω} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    (hW : IsVectorBrownian P W) (u : ℝ≥0) : IsVectorBrownian P (s79p_shiftW u W) := by
  refine ⟨fun i j => ?_, ?_⟩
  · have h := (hW.1 i j).shift u
    convert h using 2
    funext ω
    simp [s79p_shiftW]
  · have hΨ : Measurable (fun f : ℝ≥0 → ℝ => fun t => f (u + t) - f u) :=
      measurable_pi_iff.2 fun t => (measurable_pi_apply (u + t)).sub (measurable_pi_apply u)
    have h := hW.2.comp (fun _ => fun f : ℝ≥0 → ℝ => fun t => f (u + t) - f u) (fun _ => hΨ)
    convert h using 2
    funext ω t
    simp [s79p_shiftW]

section Real

variable {s a β : ℝ} {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N}

theorem s79p_indep_shift [IsProbabilityMeasure P] (hR : IsCanonicalRealization d s a β N P X₀ W X) (u : ℝ≥0) :
    IndepFun (X u) (fun ζ t => s79p_shiftW u W t ζ) P := by
  obtain ⟨ℱ, W', hbf⟩ := hR.filtered
  have hs := HRS.MD.EQLawPath.isBrownianFiltration_shift hbf.brownian u
  have h0 := HRS.MD.EQLawPath.indep_zero_path hs
  have hXm : Measurable[(HRS.MD.EQLawPath.shiftFil ℱ u) 0] (X u) := by
    refine (hbf.adapted u).mono ?_ le_rfl
    exact ℱ.mono (by simp [HRS.MD.EQLawPath.shiftFil])
  have h1 : IndepFun (X u) (fun ζ t => HRS.MD.EQLawPath.shiftProc W' u t ζ) P :=
    indep_of_indep_of_le_left h0 hXm.comap_le
  have hΦ : Measurable (fun (f : ℝ≥0 → Fin N × Fin d → ℝ) (t : ℝ≥0) (i : Fin N) =>
      (WithLp.toLp 2 fun j => f t (i, j) : Euc d)) := by
    refine measurable_pi_iff.2 fun t => measurable_pi_iff.2 fun i => ?_
    refine (WithLp.measurable_toLp 2 _).comp ?_
    refine measurable_pi_iff.2 fun j => ?_
    exact (measurable_pi_apply (i, j)).comp (measurable_pi_apply t)
  have h2 := h1.comp measurable_id hΦ
  refine h2.congr (Filter.EventuallyEq.refl _ _) ?_
  filter_upwards [hbf.coords] with ζ hζ
  funext t i
  ext j
  simp [Function.comp, HRS.MD.EQLawPath.shiftProc, s79p_shiftW, hζ]

theorem s79p_strongSolution_shift (hR : IsCanonicalRealization d s a β N P X₀ W X) (u : ℝ≥0)
    (T' : ℝ) :
    IsWholeStrongSolution P (quadraticGradientDyn d s a β) T' (X u) (s79p_shiftW u W)
      (s79p_shiftX u X) := by
  have hsol := hR.solution ((u : ℝ) + T')
  set D := quadraticGradientDyn d s a β with hD
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Filter.Eventually.of_forall fun ζ => by simp [s79p_shiftX]
  · filter_upwards [hsol.eqn] with ζ hζ
    intro t ht
    have ht0 : (0 : ℝ) ≤ t := t.2
    have h1 := hζ (u + t) (by push_cast; linarith)
    have h0 := hζ u (by linarith)
    have hint : ∀ i, IntegrableOn (fun s : ℝ => particleDriftW D (s79p_shiftX u X (Real.toNNReal s) ζ) i)
        (Set.Icc 0 (t : ℝ)) := by
      intro i
      have hi := h1.1 i
      push_cast at hi
      have hI : IntervalIntegrable (fun s : ℝ => particleDriftW D (X (Real.toNNReal s) ζ) i) volume
          (u : ℝ) ((u : ℝ) + t) :=
        (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).2
          (hi.mono_set (Set.Icc_subset_Icc_left u.coe_nonneg))
      have hI2 := hI.comp_add_left (u : ℝ)
      simp only [sub_self, add_sub_cancel_left] at hI2
      refine (intervalIntegrable_iff_integrableOn_Icc_of_le ht0).1 hI2 |>.congr_fun ?_ measurableSet_Icc
      intro s hs
      have hs0 : (0 : ℝ) ≤ s := hs.1
      simp only [s79p_shiftX]
      rw [Real.toNNReal_add u.coe_nonneg hs0, Real.toNNReal_coe]
    refine ⟨hint, fun i => ?_⟩
    obtain ⟨-, e1⟩ := h1
    obtain ⟨-, e0⟩ := h0
    have e1i := e1 i
    have e0i := e0 i
    have hFint : IntervalIntegrable (fun s : ℝ => particleDriftW D (X (Real.toNNReal s) ζ) i) volume
        0 (u : ℝ) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le u.coe_nonneg).2 ((hζ u (by linarith)).1 i)
    have hFint2 : IntervalIntegrable (fun s : ℝ => particleDriftW D (X (Real.toNNReal s) ζ) i) volume
        (u : ℝ) ((u : ℝ) + t) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).2
        (((hζ (u + t) (by push_cast; linarith)).1 i) |>.mono_set
          (by push_cast; exact Set.Icc_subset_Icc_left u.coe_nonneg))
    have hsplit : ∫ s in Set.Icc (0 : ℝ) ((u + t : ℝ≥0) : ℝ),
          particleDriftW D (X (Real.toNNReal s) ζ) i =
        (∫ s in Set.Icc (0 : ℝ) (u : ℝ), particleDriftW D (X (Real.toNNReal s) ζ) i) +
          ∫ s in Set.Icc (0 : ℝ) (t : ℝ), particleDriftW D (s79p_shiftX u X (Real.toNNReal s) ζ) i := by
      push_cast
      have c1 : ∀ (f : ℝ → Euc d) (b : ℝ), 0 ≤ b → ∫ s in Set.Icc (0 : ℝ) b, f s = ∫ s in (0 : ℝ)..b, f s := by
        intro f b hb
        rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hb]
      rw [c1 _ _ (by linarith), c1 _ _ u.coe_nonneg, c1 _ _ ht0,
        ← intervalIntegral.integral_add_adjacent_intervals hFint hFint2]
      congr 1
      have hc := intervalIntegral.integral_comp_add_left (a := (0 : ℝ)) (b := (t : ℝ))
        (fun s : ℝ => particleDriftW D (X (Real.toNNReal s) ζ) i) (u : ℝ)
      simp only [add_zero] at hc
      rw [← hc]
      refine intervalIntegral.integral_congr fun s hs => ?_
      have hs0 : (0 : ℝ) ≤ s := by
        rw [Set.uIcc_of_le ht0] at hs; exact hs.1
      simp only [s79p_shiftX]
      rw [Real.toNNReal_add u.coe_nonneg hs0, Real.toNNReal_coe]
    rw [hsplit] at e1i
    simp only [s79p_shiftX, s79p_shiftW, add_zero, sub_self]
    rw [e0i]
    simp only [Pi.sub_apply, Pi.zero_apply, s79p_shiftX]
    simp only [s79p_shiftX] at e1i
    rw [e1i]
    module
  · filter_upwards [hsol.cont] with ζ hζ i
    exact (hζ i).comp (continuous_const.add continuous_id)
  · intro t
    exact hsol.adapted (u + t)
  · filter_upwards [hsol.no_collision] with ζ hζ t ht
    exact hζ (u + t) (by push_cast; linarith [(t : ℝ≥0).2, ht])

theorem s79p_law_init [IsProbabilityMeasure P] (hR : IsCanonicalRealization d s a β N P X₀ W X)
    (u : ℝ≥0) :
    law P (X u) = canonicalGibbs (rieszKernel d s) (confinement a) N β :=
  s79_law_X_eq hR u



end Real

theorem s79p_windowPathOf_congr {m : ℝ} (T a b : ℝ) (f g : ℝ → OscDual d m)
    (h : ∀ t ∈ Set.Icc (0 : ℝ) T, f (a + t) = g (b + t)) :
    windowPathOf m T a f = windowPathOf m T b g := by
  have e : (fun t : Set.Icc (0 : ℝ) T => f (a + (t : ℝ))) = fun t : Set.Icc (0 : ℝ) T => g (b + (t : ℝ)) :=
    funext fun t => h (t : ℝ) t.2
  by_cases hc : Continuous fun t : Set.Icc (0 : ℝ) T => f (a + (t : ℝ))
  · have hc' : Continuous fun t : Set.Icc (0 : ℝ) T => g (b + (t : ℝ)) := e ▸ hc
    have e1 : windowPathOf m T a f =
        (⟨fun t => f (a + t), hc⟩ : C(Set.Icc (0 : ℝ) T, OscDual d m)) := by
      unfold windowPathOf; exact dif_pos hc
    have e2 : windowPathOf m T b g =
        (⟨fun t => g (b + t), hc'⟩ : C(Set.Icc (0 : ℝ) T, OscDual d m)) := by
      unfold windowPathOf; exact dif_pos hc'
    rw [e1, e2]
    exact ContinuousMap.ext fun t => congrFun e t
  · have hc' : ¬ Continuous fun t : Set.Icc (0 : ℝ) T => g (b + (t : ℝ)) := e ▸ hc
    have e1 : windowPathOf m T a f = 0 := by
      unfold windowPathOf; exact dif_neg hc
    have e2 : windowPathOf m T b g = 0 := by
      unfold windowPathOf; exact dif_neg hc'
    rw [e1, e2]

theorem s79p_processWindow_shift {m : ℝ} {Ω' : Type*} (T a₀ : ℝ) (Z : ℝ → Ω' → OscDual d m)
    (ζ : Ω') :
    processWindow m T a₀ Z ζ = processWindow m T 0 (fun t => Z (a₀ + t)) ζ := by
  unfold processWindow
  refine s79p_windowPathOf_congr T a₀ 0 _ _ fun t _ => ?_
  simp

theorem s79p_zetaPathW_shift {m : ℝ} {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω') (T : ℝ)
    (X : ℝ≥0 → Ω' → EucConfig d N) {a₀ : ℝ} (ha₀ : 0 ≤ a₀) (ζ : Ω') :
    zetaPathW m T a₀ P X ζ = zetaPathW m T 0 P (s79p_shiftX a₀.toNNReal X) ζ := by
  unfold zetaPathW
  refine s79p_windowPathOf_congr T a₀ 0 _ _ fun t ht => ?_
  have ht0 : (0 : ℝ) ≤ t := ht.1
  have e : Real.toNNReal (a₀ + t) = a₀.toNNReal + Real.toNNReal (0 + t) := by
    rw [zero_add]; exact Real.toNNReal_add ha₀ ht0
  simp only [e]
  rfl


end HRS.Whole.S79

import HRS.MC.S7UCDefs
import HRS.MC.S7FCD5B
import HRS.MC.S7FCD5

/-!
# Packet ucD, D5 at window `a`: helpers (sorry-free; imports no sorried module)

The window-`a` versions of the helpers of `S7FCD5B.lean`/`S7FCD5.lean` (proved at `a = 0` there):

* `S7UCD_windowFluc_eq`, `S7UCD_zetaWin_eq`, `S7UCD_procWin_eq`: the windows are `toPath` of the shifted processes;
* `S7UCD_Y_bound`: deterministic sup bound of the window `windowFluc^a`;
* `S7UCD_procWin_aemeasurable`, `S7UCD_procWin_val`: the Gaussian window `procWin^a`;
* `S7UCD_bound_s`: the one-time bound `‖D_N^{a+s}‖ ≤ W_2(Law windowFluc^a, Law procWin^a)`.

Namespace `HRS.MC.Sec7.S7UCD`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7UCD

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan HRS.MC.Sec7.S7FCH4

variable {d : ℕ}

theorem S7UCD_windowFluc_eq {Ω : Type} {N : ℕ} (R : Regime d) (r T : ℝ) (X : ℝ≥0 → Ω → Config d N)
    (a : ℝ) (ha : 0 ≤ a) (ω : Ω) :
    HRS.Main.windowFluc r T a (Real.sqrt N) X R.ρ ω =
      toPath r T (fun t ω => etaE r (X (a + t).toNNReal ω) (withDensityReal (R.ρ (a + t)))) ω := by
  unfold HRS.Main.windowFluc HRS.flucPath toPath
  refine HRS.MC.Sec7.S7FCF5I.S7FCF5I_dite_congr _ _ ?_
  funext t
  have ht : (0 : ℝ) ≤ (t : ℝ) := t.2.1
  simp only [etaE, flucE, Real.toNNReal_add ha ht]

theorem S7UCD_zetaWin_eq {Ω : Type} [MeasurableSpace Ω] {N : ℕ} (r T a : ℝ) (P : Measure Ω)
    (X : ℝ≥0 → Ω → Config d N) (ω : Ω) :
    zetaWin r T a P X ω = toPath r T (fun t ω => zetaAt r P X (a + t) ω) ω := rfl

theorem S7UCD_procWin_eq {Ω' : Type} (r T a : ℝ) (η : ℝ → Ω' → NegSobolev d r) (ω : Ω') :
    procWin r T a η ω = toPath r T (fun t ω => η (a + t) ω) ω := rfl

/-- The two windows at `a` are a.s. continuous (E1 at `a`). -/
theorem S7UCD_honest {Ω : Type} [MeasurableSpace Ω] (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6)
    (T : ℝ) {N : ℕ} (hN : 1 ≤ N) (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hreal : PreparedRealization R.D P
      (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) X₀ W X) (a : ℝ) (ha : 0 ≤ a) :
    (∀ᵐ ω ∂P, Continuous fun t : Set.Icc (0 : ℝ) T =>
      etaE r (X (a + (t : ℝ)).toNNReal ω) (withDensityReal (R.ρ (a + (t : ℝ))))) ∧
    (∀ᵐ ω ∂P, Continuous fun t : Set.Icc (0 : ℝ) T => zetaAt r P X (a + (t : ℝ)) ω) :=
  HRS.MC.Sec7.S7FCF5G.fcf5_E1_window_cont_proof R r hr T hN P X₀ W X hreal a ha

/-- The window `windowFluc^a` (`σ = √N`) is bounded by `√N K` at every time (deterministically). -/
theorem S7UCD_Y_bound {Ω : Type} [MeasurableSpace Ω] {N : ℕ} (R : Regime d) (r T : ℝ)
    (hr : (d : ℝ) < 2 * r) (X : ℝ≥0 → Ω → Config d N) (hN : 1 ≤ N) (P : Measure Ω) [IsProbabilityMeasure P]
    (a : ℝ) (ha : 0 ≤ a) (ω : Ω) (s : Set.Icc (0 : ℝ) T) :
    ‖PathSpace.at' (HRS.Main.windowFluc r T a (Real.sqrt N) X R.ρ ω) s‖ ≤
      Real.sqrt N * Real.sqrt (8 * ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * r))) := by
  rw [S7UCD_windowFluc_eq R r T X a ha]
  by_cases h : Continuous fun t : Set.Icc (0 : ℝ) T =>
      etaE r (X (a + (t : ℝ)).toNNReal ω) (withDensityReal (R.ρ (a + (t : ℝ))))
  · rw [S7FCD5B.S7FCD5B_toPath_apply r T _ ω h s]
    exact S7FCD5B.S7FCD5B_eta_norm_le R r hr P X hN (a + (s : ℝ)) (add_nonneg ha s.2.1) ω
  · have hw : toPath r T (fun t ω => etaE r (X (a + t).toNNReal ω) (withDensityReal (R.ρ (a + t)))) ω =
        (0 : PathSpace d r T) := by
      unfold toPath
      exact dif_neg h
    rw [hw]
    have hz : PathSpace.at' (0 : PathSpace d r T) s = 0 := rfl
    rw [hz, norm_zero]
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- The Gaussian window `procWin^a` is AEMeasurable into `PathSpace`, from a.s. continuity of `η` on `[0, a+T]`. -/
theorem S7UCD_procWin_aemeasurable {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (r T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) (η : ℝ → Ω' → NegSobolev d r) (hm : ∀ t, Measurable (η t))
    (hc : ∀ᵐ ω ∂P', ContinuousOn (fun t => η t ω) (Set.Icc 0 (a + T))) :
    AEMeasurable (procWin r T a η) P' := by
  have hc' : ∀ᵐ ω ∂P', ContinuousOn (fun t => η (a + t) ω) (Set.Icc 0 T) := by
    filter_upwards [hc] with ω hω
    refine hω.comp (continuous_const.add continuous_id).continuousOn ?_
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h := HRS.Uniform.Q45.aemeasurable_windowPath' P' hT (fun t ω => η (a + t) ω)
    (fun t _ => (hm (a + t)).aemeasurable) hc'
  have hfun : procWin r T a η = HRS.Uniform.windowPath 0 T (fun t ω => η (a + t) ω) := by
    funext ω
    rw [S7UCD_procWin_eq]
    unfold toPath HRS.Uniform.windowPath
    refine HRS.MC.Sec7.S7FCF5I.S7FCF5I_dite_congr _ _ ?_
    funext t
    simp only [zero_add]
  rw [hfun]
  exact h

theorem S7UCD_procWin_val {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') (r T a : ℝ) (ha : 0 ≤ a)
    (η : ℝ → Ω' → NegSobolev d r) (hc : ∀ᵐ ω ∂P', ContinuousOn (fun t => η t ω) (Set.Icc 0 (a + T))) :
    ∀ᵐ ω ∂P', ∀ s : Set.Icc (0 : ℝ) T, PathSpace.at' (procWin r T a η ω) s = η (a + (s : ℝ)) ω := by
  filter_upwards [hc] with ω hω
  rw [S7UCD_procWin_eq]
  have hcont : Continuous fun t : Set.Icc (0 : ℝ) T => η (a + (t : ℝ)) ω := by
    have h1 : ContinuousOn (fun t => η (a + t) ω) (Set.Icc 0 T) := by
      refine hω.comp (continuous_const.add continuous_id).continuousOn ?_
      intro t ht
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact continuousOn_iff_continuous_restrict.1 h1
  intro s
  exact S7FCD5B.S7FCD5B_toPath_apply r T (fun t ω => η (a + t) ω) ω hcont s

/-- The one-time bound: `‖E η_N^{a+s}‖ ≤ W_2(Law windowFluc^a, Law procWin^a)` at every time `s ∈ [0,T]`, given that the
Gaussian side has mean zero at `a + s`. -/
theorem S7UCD_bound_s {Ω : Type} [MeasurableSpace Ω] (R : Regime d) (r T : ℝ) (hdr : (d : ℝ) < 2 * r)
    {N : ℕ} (hN : 1 ≤ N) (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → Config d N)
    (hadapt : ∀ t : ℝ≥0, Measurable (X t)) (a : ℝ) (ha : 0 ≤ a)
    (hF : AEMeasurable (HRS.Main.windowFluc r T a (Real.sqrt N) X R.ρ) P)
    (hcont : ∀ᵐ ω ∂P, Continuous fun t : Set.Icc (0 : ℝ) T =>
      etaE r (X (a + (t : ℝ)).toNNReal ω) (withDensityReal (R.ρ (a + (t : ℝ)))))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') (η : ℝ → Ω' → NegSobolev d r)
    (s : Set.Icc (0 : ℝ) T)
    (hν : ∫ w, PathSpace.at' w s ∂(law P' (procWin r T a η)) = 0) :
    ENNReal.ofReal ‖S7FCD5B.S7FCD5B_D R r P X (a + (s : ℝ))‖ ≤
      wassersteinE 2 (law P (HRS.Main.windowFluc r T a (Real.sqrt N) X R.ρ)) (law P' (procWin r T a η)) := by
  have hevm := HRS.MC.Sec7.S7FCD5.S7FCD5_evalMeas (d := d) r T s
  haveI hμP : IsProbabilityMeasure (law P (HRS.Main.windowFluc r T a (Real.sqrt N) X R.ρ)) :=
    (Measure.isProbabilityMeasure_map_iff hF).2 inferInstance
  have hint : Integrable (fun w : PathSpace d r T => PathSpace.at' w s)
      (law P (HRS.Main.windowFluc r T a (Real.sqrt N) X R.ρ)) := by
    refine (integrable_map_measure hevm.aestronglyMeasurable hF).2 ?_
    refine (integrable_const (Real.sqrt N * Real.sqrt (8 * ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * r))))).mono' ?_ ?_
    · exact (hevm.comp_aemeasurable hF).aestronglyMeasurable
    · exact Eventually.of_forall fun ω => S7UCD_Y_bound R r T hdr X hN P a ha ω s
  have hmean : ∫ w, PathSpace.at' w s ∂(law P (HRS.Main.windowFluc r T a (Real.sqrt N) X R.ρ)) =
      S7FCD5B.S7FCD5B_D R r P X (a + (s : ℝ)) := by
    rw [integral_map hF hevm.aestronglyMeasurable]
    have hae : (fun ω => PathSpace.at' (HRS.Main.windowFluc r T a (Real.sqrt N) X R.ρ ω) s) =ᵐ[P]
        (fun ω => etaE r (X (a + (s : ℝ)).toNNReal ω) (withDensityReal (R.ρ (a + (s : ℝ))))) := by
      filter_upwards [hcont] with ω hω
      rw [S7UCD_windowFluc_eq R r T X a ha]
      exact S7FCD5B.S7FCD5B_toPath_apply r T
        (fun t ω => etaE r (X (a + t).toNNReal ω) (withDensityReal (R.ρ (a + t)))) ω hω s
    exact (integral_congr_ae hae).trans
      (S7FCD5B.S7FCD5B_mean R r hdr P X hadapt hN (a + (s : ℝ)) (add_nonneg ha s.2.1))
  unfold wassersteinE
  refine le_iInf fun π => ?_
  have hc := S7FCD5B.S7FCD5B_eval_coupling r T (law P (HRS.Main.windowFluc r T a (Real.sqrt N) X R.ρ))
    (law P' (procWin r T a η)) s hint π.1 π.2
  rw [hmean, hν, sub_zero] at hc
  exact hc

end HRS.MC.Sec7.S7UCD

end

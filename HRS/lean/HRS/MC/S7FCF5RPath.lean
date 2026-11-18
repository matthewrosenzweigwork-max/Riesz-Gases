import HRS.MC.S7FCF5IE2
import HRS.MC.S7FCF5CE3a
import HRS.MC.S7FCF5OD2
import HRS.MC.S7FCF5BB1

/-!
# Packet fcf5r, helpers for E3b (`fcf5_E3b_F5_zeta_moments`, `F5` of `S7FCF5Plan.lean`)

Sorry-free helpers, namespace `HRS.MC.Sec7.S7FCF5R`, prefix `S7FCF5R_`:

* `S7FCF5R_rat_mem_closure`, `S7FCF5R_le_rat`: a function continuous on `[0,T]` is dominated at every point by its
  bound on the rational points of `[0,T]` (own proof; the `ratTimes` lemma of `EQBurnBurnBase` is not in the closure).
* `S7FCF5R_cm_enorm_le`, `S7FCF5R_windowPath_enorm_le`: the `E_r`-sup norm of a continuous path is bounded by a bound
  valid on the rational times (and the zero path has norm `0`).
* `S7FCF5R_etaE_le_Shat`: `‖η^t‖ₑ ≤ fcf5Shat` for `t ∈ a + ℚ∩[0,T]`.
* `S7FCF5R_windowFluc_le`: pointwise `‖windowFluc ω‖ₑ ≤ fcf5Shat ω` (every `ω`).
* `S7FCF5R_zetaWin_le`: pointwise `‖zetaWin ω‖ₑ ≤ fcf5Shat ω + ∫⁻ fcf5Shat` (every `ω`), via E3a.
* `S7FCF5R_moment_of_enorm`: an `AEMeasurable` path with a finite `lintegral` moment is `Integrable` with the bound.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCF5R

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan HRS.MC.Sec7.FCF5Plan

variable {d : ℕ}

/-- The rational times of `[0,T]`: the countable dense subset used for the suprema. -/
def S7FCF5R_rat (T : ℝ) : Set ℝ := {s : ℝ | ∃ q : ℚ, (q : ℝ) ∈ Set.Icc (0 : ℝ) T ∧ s = q}

theorem S7FCF5R_rat_mem_closure {T : ℝ} (hT : 0 < T) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) T) :
    x ∈ closure (S7FCF5R_rat T) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hlh : max 0 (x - ε / 2) < min T (x + ε / 2) :=
    max_lt (lt_min hT (by linarith [hx.1])) (lt_min (by linarith [hx.2]) (by linarith))
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlh
  have hq0 : (0 : ℝ) ≤ q := (le_max_left _ _).trans hq1.le
  have hqT : (q : ℝ) ≤ T := hq2.le.trans (min_le_left _ _)
  have h1 : x - ε / 2 < q := lt_of_le_of_lt (le_max_right _ _) hq1
  have h2 : (q : ℝ) < x + ε / 2 := lt_of_lt_of_le hq2 (min_le_right _ _)
  refine ⟨(q : ℝ), ⟨q, ⟨hq0, hqT⟩, rfl⟩, ?_⟩
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- A function `ℝ → ℝ≥0∞` continuous on `[0,T]` is bounded at each point of `[0,T]` by a bound valid on the
rational points of `[0,T]`. -/
theorem S7FCF5R_le_rat {T : ℝ} (hT : 0 < T) {f : ℝ → ℝ≥0∞} (hf : ContinuousOn f (Set.Icc (0 : ℝ) T))
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) T) (B : ℝ≥0∞) (hB : ∀ s ∈ S7FCF5R_rat T, f s ≤ B) : f x ≤ B := by
  have hne : (𝓝[S7FCF5R_rat T] x).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (S7FCF5R_rat_mem_closure hT hx)
  have hcw : ContinuousWithinAt f (S7FCF5R_rat T) x :=
    (hf x hx).mono fun s hs => by
      obtain ⟨q, hq, rfl⟩ := hs
      exact hq
  exact le_of_tendsto hcw.tendsto (eventually_nhdsWithin_of_forall fun s hs => hB s hs)

/-- The sup norm of a continuous path `t ↦ G t` on `[0,T]` is bounded by any bound valid on the rational times. -/
theorem S7FCF5R_cm_enorm_le {E : Type*} [NormedAddCommGroup E] {T : ℝ} (hT : 0 < T) (G : ℝ → E)
    (h : Continuous fun t : Set.Icc (0 : ℝ) T => G t) (B : ℝ≥0∞) (hB : ∀ s ∈ S7FCF5R_rat T, ‖G s‖ₑ ≤ B) :
    ‖(⟨fun t : Set.Icc (0 : ℝ) T => G t, h⟩ : C(Set.Icc (0 : ℝ) T, E))‖ₑ ≤ B := by
  by_cases hBt : B = ⊤
  · rw [hBt]
    exact le_top
  have hG : ContinuousOn G (Set.Icc (0 : ℝ) T) := continuousOn_iff_continuous_restrict.2 h
  have hpt : ∀ x : Set.Icc (0 : ℝ) T, ‖G x‖ₑ ≤ B := fun x =>
    S7FCF5R_le_rat hT hG.enorm x.2 B hB
  have hreal : ∀ x : Set.Icc (0 : ℝ) T, ‖G x‖ ≤ B.toReal := fun x => by
    have h1 := hpt x
    rw [← ofReal_norm] at h1
    exact (ENNReal.ofReal_le_iff_le_toReal hBt).1 h1
  have hn : ‖(⟨fun t : Set.Icc (0 : ℝ) T => G t, h⟩ : C(Set.Icc (0 : ℝ) T, E))‖ ≤ B.toReal :=
    (ContinuousMap.norm_le _ ENNReal.toReal_nonneg).2 hreal
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_of_le_toReal hn

/-- A continuous `windowPath` is the continuous map it is given by (the `dite` of its definition). -/
theorem S7FCF5R_windowPath_of_cont {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Type*} {T : ℝ}
    (Y : ℝ → Ω → E) (ω : Ω) (h : Continuous fun t : Set.Icc (0 : ℝ) T => Y (0 + (t : ℝ)) ω) :
    HRS.Uniform.windowPath 0 T Y ω =
      ((⟨fun t : Set.Icc (0 : ℝ) T => Y (0 + (t : ℝ)) ω, h⟩ : C(Set.Icc (0 : ℝ) T, E)) :
        HRS.Uniform.PathSp T E) := by
  unfold HRS.Uniform.windowPath
  classical
  exact dif_pos h

/-- A discontinuous `windowPath` is the zero path. -/
theorem S7FCF5R_windowPath_of_not_cont {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Type*} {T : ℝ}
    (Y : ℝ → Ω → E) (ω : Ω) (h : ¬ Continuous fun t : Set.Icc (0 : ℝ) T => Y (0 + (t : ℝ)) ω) :
    HRS.Uniform.windowPath 0 T Y ω = 0 := by
  unfold HRS.Uniform.windowPath
  classical
  exact dif_neg h

/-- The `E_r`-sup norm of a window path given as `windowPath` (the zero path if discontinuous). -/
theorem S7FCF5R_windowPath_enorm_le {Ω : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {T : ℝ}
    (hT : 0 < T) (Y : ℝ → Ω → E) (ω : Ω) (B : ℝ≥0∞) (hB : ∀ s ∈ S7FCF5R_rat T, ‖Y (0 + s) ω‖ₑ ≤ B) :
    ‖HRS.Uniform.windowPath 0 T Y ω‖ₑ ≤ B := by
  by_cases h : Continuous fun t : Set.Icc (0 : ℝ) T => Y (0 + (t : ℝ)) ω
  · rw [S7FCF5R_windowPath_of_cont Y ω h]
    exact S7FCF5R_cm_enorm_le hT (fun t => Y (0 + t) ω) h B hB
  · rw [S7FCF5R_windowPath_of_not_cont Y ω h]
    simp

/-- `‖η^t‖ₑ ≤ fcf5Shat` at every window time `t ∈ fcf5Rat a T`. -/
theorem S7FCF5R_etaE_le_Shat (R : Regime d) (r T a : ℝ) {N : ℕ} {Ω : Type} (X : ℝ≥0 → Ω → Config d N) (ω : Ω)
    (t : ℝ) (ht : t ∈ fcf5Rat a T) :
    ‖etaE r (X t.toNNReal ω) (withDensityReal (R.ρ t))‖ₑ ≤ fcf5Shat R r a T X ω :=
  le_iSup₂ (f := fun t (_ : t ∈ fcf5Rat a T) => ‖etaE r (X t.toNNReal ω) (withDensityReal (R.ρ t))‖ₑ) t ht

/-- Pointwise bound of the `E_r`-window `η_N^{a+·}` (`windowFluc`) by the window supremum `fcf5Shat`. -/
theorem S7FCF5R_windowFluc_le (R : Regime d) (r T : ℝ) (hT : 0 < T) {N : ℕ} {Ω : Type}
    (X : ℝ≥0 → Ω → Config d N) (a : ℝ) (ha : 0 ≤ a) (ω : Ω) :
    ‖HRS.Main.windowFluc r T a (Real.sqrt N) X R.ρ ω‖ₑ ≤ fcf5Shat R r a T X ω := by
  have hW : HRS.Main.windowFluc r T a (Real.sqrt N) X R.ρ ω =
      HRS.Uniform.windowPath 0 T (fun t ω => etaE r (X (a + t).toNNReal ω) (withDensityReal (R.ρ (a + t)))) ω := by
    unfold HRS.Main.windowFluc HRS.flucPath HRS.Uniform.windowPath
    refine HRS.MC.Sec7.S7FCF5I.S7FCF5I_dite_congr _ _ ?_
    funext t
    have ht : (0 : ℝ) ≤ (t : ℝ) := t.2.1
    simp only [etaE, flucE, zero_add, Real.toNNReal_add ha ht]
  rw [hW]
  refine S7FCF5R_windowPath_enorm_le hT _ ω _ ?_
  intro s hs
  obtain ⟨q, hq, rfl⟩ := hs
  exact S7FCF5R_etaE_le_Shat R r T a X ω (a + (0 + (q : ℝ))) ⟨q, hq, by simp⟩

/-- A continuous `toPath` is the continuous map it is given by (the `dite` of its definition). -/
theorem S7FCF5R_toPath_of_cont {Ω : Type*} {γ T : ℝ} (Y : ℝ → Ω → NegSobolev d γ) (ω : Ω)
    (h : Continuous fun t : Set.Icc (0 : ℝ) T => Y (t : ℝ) ω) :
    HRS.toPath γ T Y ω =
      ((⟨fun t : Set.Icc (0 : ℝ) T => Y (t : ℝ) ω, h⟩ : C(Set.Icc (0 : ℝ) T, NegSobolev d γ)) :
        PathSpace d γ T) := by
  unfold HRS.toPath
  classical
  exact dif_pos h

/-- A discontinuous `toPath` is the zero path. -/
theorem S7FCF5R_toPath_of_not_cont {Ω : Type*} {γ T : ℝ} (Y : ℝ → Ω → NegSobolev d γ) (ω : Ω)
    (h : ¬ Continuous fun t : Set.Icc (0 : ℝ) T => Y (t : ℝ) ω) : HRS.toPath γ T Y ω = 0 := by
  unfold HRS.toPath
  classical
  exact dif_neg h

/-- Pointwise bound of the particle window `ζ_N^{a+·}` (`zetaWin`) via E3a: `‖ζ^t‖ₑ ≤ ‖η^t‖ₑ + ∫⁻ ‖η^t‖ₑ`
with `‖η^t‖ₑ ≤ fcf5Shat` on the rational times. -/
theorem S7FCF5R_zetaWin_le (R : Regime d) (r : ℝ) (hd : (d : ℝ) < 2 * r) (T : ℝ) (hT : 0 < T) {N : ℕ}
    (hN : 1 ≤ N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → Config d N) (hX : ∀ t : ℝ≥0, Measurable (X t)) (a : ℝ) (ha : 0 ≤ a) (ω : Ω) :
    ‖zetaWin r T a P X ω‖ₑ ≤ fcf5Shat R r a T X ω + ∫⁻ ω', fcf5Shat R r a T X ω' ∂P := by
  unfold zetaWin
  by_cases h : Continuous fun t : Set.Icc (0 : ℝ) T => zetaAt r P X (a + (t : ℝ)) ω
  · rw [S7FCF5R_toPath_of_cont (fun t ω => zetaAt r P X (a + t) ω) ω h]
    refine S7FCF5R_cm_enorm_le hT (fun t => zetaAt r P X (a + t) ω) h _ ?_
    intro s hs
    obtain ⟨q, hq, rfl⟩ := hs
    have hmem : a + (q : ℝ) ∈ fcf5Rat a T := ⟨q, hq, rfl⟩
    have ht0 : (0 : ℝ) ≤ a + (q : ℝ) := by linarith [hq.1]
    show ‖zetaE r (P.map (X (a + (q : ℝ)).toNNReal)) (X (a + (q : ℝ)).toNNReal ω)‖ₑ ≤ _
    rw [HRS.MC.Sec7.S7FCF5C.fcf5_E3a_zeta_decomp_proof R r hd hN P X hX (a + (q : ℝ)) ht0 ω]
    calc ‖etaE r (X (a + (q : ℝ)).toNNReal ω) (withDensityReal (R.ρ (a + (q : ℝ)))) -
          ∫ ω', etaE r (X (a + (q : ℝ)).toNNReal ω') (withDensityReal (R.ρ (a + (q : ℝ)))) ∂P‖ₑ
        ≤ ‖etaE r (X (a + (q : ℝ)).toNNReal ω) (withDensityReal (R.ρ (a + (q : ℝ))))‖ₑ +
            ‖∫ ω', etaE r (X (a + (q : ℝ)).toNNReal ω') (withDensityReal (R.ρ (a + (q : ℝ)))) ∂P‖ₑ :=
          enorm_sub_le
      _ ≤ fcf5Shat R r a T X ω + ∫⁻ ω', fcf5Shat R r a T X ω' ∂P :=
          add_le_add (S7FCF5R_etaE_le_Shat R r T a X ω _ hmem)
            ((enorm_integral_le_lintegral_enorm _).trans
              (lintegral_mono fun ω' => S7FCF5R_etaE_le_Shat R r T a X ω' _ hmem))
  · rw [S7FCF5R_toPath_of_not_cont (fun t ω => zetaAt r P X (a + t) ω) ω h]
    simp

/-- From an `AEMeasurable` path with a finite `lintegral` bound on `‖Z‖ₑ^q`, the real moment is `Integrable` and
bounded by the same constant. -/
theorem S7FCF5R_moment_of_enorm {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {γ T : ℝ}
    (Z : Ω → PathSpace d γ T) (hZ : AEMeasurable Z P) (q : ℝ) (hq : 0 ≤ q) (C : ℝ) (hC : 0 ≤ C)
    (h : ∫⁻ ω, ‖Z ω‖ₑ ^ q ∂P ≤ ENNReal.ofReal C) :
    Integrable (fun ω => ‖Z ω‖ ^ q) P ∧ ∫ ω, ‖Z ω‖ ^ q ∂P ≤ C := by
  have hof : ∀ ω, ENNReal.ofReal (‖Z ω‖ ^ q) = ‖Z ω‖ₑ ^ q := fun ω => by
    rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq, ofReal_norm]
  have hmeas : AEStronglyMeasurable (fun ω => ‖Z ω‖ ^ q) P :=
    ((hZ.norm).pow_const q).aestronglyMeasurable
  have hfin : HasFiniteIntegral (fun ω => ‖Z ω‖ ^ q) P := by
    unfold HasFiniteIntegral
    have : ∫⁻ ω, ‖‖Z ω‖ ^ q‖ₑ ∂P ≤ ENNReal.ofReal C := by
      refine le_trans (le_of_eq ?_) h
      refine lintegral_congr fun ω => ?_
      rw [Real.enorm_eq_ofReal (Real.rpow_nonneg (norm_nonneg _) q), hof ω]
    exact lt_of_le_of_lt this ENNReal.ofReal_lt_top
  refine ⟨⟨hmeas, hfin⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (norm_nonneg _) q)
    hmeas]
  refine ENNReal.toReal_le_of_le_ofReal hC ?_
  simp only [hof]
  exact h

end HRS.MC.Sec7.S7FCF5R

end

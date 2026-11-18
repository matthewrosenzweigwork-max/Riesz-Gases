import HRS.MS.S111K2B04f

/-!
# S11.1 continuation, B04 (part 8): the integrand `W(v,τ)` of the drift path, bounds, measurability, integrability
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K2

open HRS HRS.Whole HRS.MS.Go HRS.MS.CovMeas HRS.MS.R2WinErr HRS.MS.FixEq

variable {d : ℕ}

/-- Measurability of the drift integrand on its physical domain (copy of the Pro `DriftIntegrandMeas`). -/
def S111k2DriftIntegrandMeas {d : ℕ} (C : WholeCoeff d) (m T u : ℝ) (z : ℝ → (Euc d → ℝ) → ℝ) : Prop :=
  ∀ t ∈ Set.Icc u (u + T), ∀ phi, IsR2DualCombo m phi →
    AEMeasurable (fun v => z v (propagatorW C v t phi)) (volume.restrict (Set.Icc 0 t))

lemma s111k2_dual_lt_top {r : ℕ} {P : ℝ} {η : (Euc d → ℝ) → ℝ} (hη : IsBoundedLinearOnE r P η) :
    dualNormE r P η < ⊤ := by
  obtain ⟨B, hB⟩ := hη.2
  refine lt_of_le_of_lt (b := ENNReal.ofReal |B|) (iSup_le fun f => iSup_le fun hf => ?_) ENNReal.ofReal_lt_top
  have hfr : ContDiff ℝ r f := contDiff_infty.1 hf.1 r
  have h1 := hB f hfr hf.2.2.2
  have hE0 : weightedSobolevE r P f ≠ 0 := hf.2.2.1.ne'
  have hEt : weightedSobolevE r P f ≠ ⊤ := hf.2.2.2.ne
  refine ENNReal.div_le_of_le_mul ?_
  calc ENNReal.ofReal |η f| ≤ ENNReal.ofReal (|B| * (weightedSobolevE r P f).toReal) :=
        ENNReal.ofReal_le_ofReal (h1.trans (mul_le_mul_of_nonneg_right (le_abs_self B) ENNReal.toReal_nonneg))
    _ = ENNReal.ofReal |B| * weightedSobolevE r P f := by
        rw [ENNReal.ofReal_mul (abs_nonneg _), ENNReal.ofReal_toReal hEt]

/-- The standing hypotheses of the drift construction. -/
structure S111k2Drift {d : ℕ} (C : WholeCoeff d) (m c0 : ℝ) (r : ℕ) (b : MultiIndex d → ℝ) (S T u Pw : ℝ)
    (z : ℝ → (Euc d → ℝ) → ℝ) : Prop where
  hW : S111k2WindowOrbitInput C m c0 r b
  hc0 : 0 < c0
  hT : 0 < T
  hu : 0 ≤ u
  hbs : Summable fun α => b α ^ 2
  hS : (∑' α, b α ^ 2) ≤ S
  hP : (d : ℝ) + 2 < 2 * Pw
  hz : IsR2L1F r Pw (u + T) z
  hmeas : S111k2DriftIntegrandMeas C m T u z
  hone : ∀ v ∈ Set.Icc (0 : ℝ) (u + T), z v (fun _ => 1) = 0

variable {C : WholeCoeff d} {m c0 : ℝ} {r : ℕ} {b : MultiIndex d → ℝ} {S T u Pw : ℝ}
  {z : ℝ → (Euc d → ℝ) → ℝ}

lemma S111k2Drift.dual_lt (h : S111k2Drift C m c0 r b S T u Pw z) {v : ℝ}
    (hv : v ∈ Set.Icc (0 : ℝ) (u + T)) : dualNormE r Pw (z v) < ⊤ :=
  s111k2_dual_lt_top (s111k2_bounded_of_L1F h.hz hv)

/-- The integrand: the forcing at time `v`, propagated to the observation time `u + τ` (zero if `v > u + τ`). -/
def s111k2_W (C : WholeCoeff d) (m : ℝ) (z : ℝ → (Euc d → ℝ) → ℝ) (u v τ : ℝ) : OscDual d m :=
  if v ≤ u + τ then s111k2_Y C m z v (u + τ) else 0

/-- The envelope `age · ‖z^v‖`. -/
def s111k2_Phi (c0 u : ℝ) (r : ℕ) (Pw : ℝ) (z : ℝ → (Euc d → ℝ) → ℝ) (v : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (s111k2_age c0 u v) * dualNormE r Pw (z v)

/-- The constant of the drift bound. -/
def s111k2_Kdrift (d r : ℕ) (Pw S : ℝ) : ℝ := s111k2_CE d r Pw * Real.sqrt S + 1

lemma s111k2_Kdrift_pos (d r : ℕ) (Pw S : ℝ) : 0 < s111k2_Kdrift d r Pw S := by
  unfold s111k2_Kdrift
  have := s111k2_CE_nonneg (d := d) r Pw
  positivity

lemma s111k2_age_pos (c0 u v : ℝ) : 0 < s111k2_age c0 u v := Real.exp_pos _

lemma s111k2_age_le_one {c0 : ℝ} (hc0 : 0 < c0) (u v : ℝ) : s111k2_age c0 u v ≤ 1 := by
  unfold s111k2_age
  rw [Real.exp_le_one_iff]
  have : 0 ≤ max (u - v) 0 := le_max_right _ _
  nlinarith

lemma s111k2_exp_le_age {c0 u v τ : ℝ} (hc0 : 0 < c0) (hτ : 0 ≤ τ) (hvτ : v ≤ u + τ) :
    Real.exp (-c0 * (u + τ - v)) ≤ s111k2_age c0 u v := by
  unfold s111k2_age
  apply Real.exp_le_exp.2
  have : max (u - v) 0 ≤ u + τ - v := max_le (by linarith) (by linarith)
  nlinarith

lemma s111k2_Phi_fin (h : S111k2Drift C m c0 r b S T u Pw z) :
    ∫⁻ v in Set.Icc (0 : ℝ) (u + T), s111k2_Phi c0 u r Pw z v ≠ ⊤ := by
  refine ne_top_of_le_ne_top h.hz.2.2.ne ?_
  refine lintegral_mono fun v => ?_
  unfold s111k2_Phi
  calc ENNReal.ofReal (s111k2_age c0 u v) * dualNormE r Pw (z v) ≤ 1 * dualNormE r Pw (z v) :=
        mul_le_mul' (by simpa using ENNReal.ofReal_le_ofReal (s111k2_age_le_one h.hc0 u v)) le_rfl
    _ = _ := one_mul _

lemma s111k2_W_bound (h : S111k2Drift C m c0 r b S T u Pw z) {v τ : ℝ}
    (hv : v ∈ Set.Icc (0 : ℝ) (u + T)) (hτ : τ ∈ Set.Icc (0 : ℝ) T) :
    ‖s111k2_W C m z u v τ‖ₑ ≤ ENNReal.ofReal (s111k2_Kdrift d r Pw S) * s111k2_Phi c0 u r Pw z v := by
  unfold s111k2_W
  split_ifs with hvτ
  · have hdual := h.dual_lt hv
    have hn := s111k2_Y_norm h.hW h.hbs h.hS h.hP h.hz hv (h.hone v hv) hdual hvτ
    have hage := s111k2_exp_le_age (c0 := c0) (u := u) (v := v) h.hc0 hτ.1 hvτ
    set a : ℝ := (dualNormE r Pw (z v)).toReal with ha
    have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
    have hCE := s111k2_CE_nonneg (d := d) r Pw
    have hsq : 0 ≤ Real.sqrt S := Real.sqrt_nonneg _
    have h1 : ‖s111k2_Y C m z v (u + τ)‖ ≤ a * (s111k2_CE d r Pw * Real.sqrt S) * s111k2_age c0 u v := by
      refine hn.trans ?_
      calc a * s111k2_CE d r Pw * Real.sqrt S * Real.exp (-c0 * (u + τ - v))
          = a * (s111k2_CE d r Pw * Real.sqrt S) * Real.exp (-c0 * (u + τ - v)) := by ring
        _ ≤ a * (s111k2_CE d r Pw * Real.sqrt S) * s111k2_age c0 u v :=
          mul_le_mul_of_nonneg_left hage (by positivity)
    rw [← ofReal_norm_eq_enorm]
    calc ENNReal.ofReal ‖s111k2_Y C m z v (u + τ)‖
        ≤ ENNReal.ofReal (a * (s111k2_CE d r Pw * Real.sqrt S) * s111k2_age c0 u v) := ENNReal.ofReal_le_ofReal h1
      _ = ENNReal.ofReal (s111k2_CE d r Pw * Real.sqrt S) * (ENNReal.ofReal (s111k2_age c0 u v) *
            dualNormE r Pw (z v)) := by
          rw [ENNReal.ofReal_mul (mul_nonneg ha0 (mul_nonneg hCE hsq)), ENNReal.ofReal_mul ha0, ha,
            ENNReal.ofReal_toReal hdual.ne]
          ring
      _ ≤ ENNReal.ofReal (s111k2_Kdrift d r Pw S) * s111k2_Phi c0 u r Pw z v := by
          unfold s111k2_Phi
          refine mul_le_mul' (ENNReal.ofReal_le_ofReal (by unfold s111k2_Kdrift; linarith)) le_rfl
  · simp

end HRS.MS.S111K2

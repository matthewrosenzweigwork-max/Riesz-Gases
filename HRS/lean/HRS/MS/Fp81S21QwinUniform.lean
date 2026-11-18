import HRS.MS.Fp81S21Radius
import HRS.MS.S21F_I00
import HRS.MS.S21F_I02b
import HRS.MS.R2WinOrbAux1
import HRS.MS.S21H2_S30A
import HRS.MS.Fp81S21OscDatum
import HRS.MS.R2InterpAux71
import HRS.MS.WsPrepI1

/-!
# HRS S2.1(iii), SOL26 packet 27a: uniform cosine observation certificate

The common-radius window clause gives the cosine tests uniformly in their start time.
This file identifies its root definition with `r26t3_qwin`, restricts the derivative
order from `4d+42` to `r26t3_J = 4d+40`, and records the resulting summability facts.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS (Euc MemCb cbNorm)
open HRS.Whole
open HRS.MS.R26T3
open HRS.MS.R2WinOrb
open HRS.MS.R2WinOrbNL

/-- The product feature weight of the cosine frequency and oscillator mode is summable. -/
theorem fp81s21_qwin_weight_summable (p : Parameters) :
    Summable (r26t3_feature_weight p.d) := by
  have hd : 1 ≤ p.d := by have := p.hd; omega
  let e := r26t3_feature_enum p.d
  have hw := HRS.MS.S21.s21i_W_summable hd 1
  have he := hw.comp_injective (i := e) e.injective
  have hexp : ((((18 * p.d + 180 : ℕ) : ℝ) - ((24 * p.d + 240 : ℕ) : ℝ)) / 2) =
      -(3 * (p.d : ℝ) + 30) := by push_cast; ring
  refine he.congr fun j => ?_
  dsimp [e, HRS.MS.S21.s21iW, HRS.MS.S21.s21iB, r26t3_feature_weight]
  rw [hexp]
  ring

/-- The root feature weight is exactly the window frequency weight times `s103_b`. -/
theorem fp81s21_qwin_feature_weight_eq (p : Parameters) (j : ℕ) :
    r26t3_feature_weight p.d j =
      (1 + ((r26t3_feature_enum p.d j).1 : ℝ)) ^ (-(5 : ℝ) / 4) *
        s103_b p.d (r26t3_feature_enum p.d j).2 := by
  dsimp [r26t3_feature_weight]
  have hexp : ((((18 * p.d + 180 : ℕ) : ℝ) - ((24 * p.d + 240 : ℕ) : ℝ)) / 2) =
      -(3 * (p.d : ℝ) + 30) := by push_cast; ring
  have htime : -(5 / 4 : ℝ) = -(5 : ℝ) / 4 := by norm_num
  rw [htime, s103_b, hexp]

/-- The root cosine and the legacy window test have exactly the same normalization,
including the `n = 0` mode. -/
theorem fp81s21_qwin_eq_windowTest
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ) (a : ℝ) (j : ℕ) :
    r26t3_qwin R a j =
      r2WindowTest (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) p.T a
        (r26t3_feature_enum p.d j).1 (r26t3_feature_enum p.d j).2 := by
  let i := r26t3_feature_enum p.d j
  have hcos : ∀ u, r26t3_cosine p.T i.1 u = r2CosBasis p.T i.1 u := by
    intro u
    unfold r26t3_cosine r2CosBasis
    split_ifs with hn
    · simp [hn, one_div]
    · rfl
  funext x
  simp only [r26t3_qwin, r2WindowTest, r26t3_U, r26t3_coeff, i]
  have hm : (wholeSpaceIndex p.d : ℝ) = ((24 * p.d + 240 : ℕ) : ℝ) := rfl
  rw [hm]
  congr 2
  funext u
  rw [hcos]

/-- Uniform `C_b^J` root certificate for the complete cosine observation family.
The common window producer controls the zero mode as well as all positive modes. -/
theorem fp81s21_qwin_uniform (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 ≤ a →
          IsSummableFeatureFamily (r26t3_J p.d) (r26t3_qwin R a) ∧
          (∀ j, cbNorm (r26t3_J p.d) (r26t3_qwin R a j) ≤
            C * r26t3_feature_weight p.d j) := by
  obtain ⟨δ0, Co, co, hδ0, hδhalf, hco, hcommon⟩ := fp81s21_common_radius p
  refine ⟨δ0, hδ0, hδhalf, fun δ hδ hδle R => ?_⟩
  obtain ⟨horb, hhexdata, hterm, hwindowAll⟩ :=
    hcommon δ hδ hδle R.ρβ R.thermal
  obtain ⟨Cw, hwindow⟩ := hwindowAll p.T p.hT
  let C : ℝ := max Cw 0
  have hC : 0 ≤ C := le_max_right _ _
  have htest : ∀ α : MultiIndex p.d,
      IsOscTest (wholeSpaceIndex p.d : ℝ)
        (oscTestFun (wholeSpaceIndex p.d : ℝ) α) := by
    intro α
    obtain ⟨ψ, hψ⟩ := HRS.MS.R2Interp.s102_osc_schwartz
      (wholeSpaceIndex p.d : ℝ) α
    change IsOscTest (wholeSpaceIndex p.d : ℝ)
      (oscTestFun (wholeSpaceIndex p.d : ℝ) α)
    constructor
    · rw [← hψ]
      exact ψ.smooth ⊤
    · rw [← hψ]
      exact memOsc_schwartz _ (ψ : SchwartzMap (Euc p.d) ℝ)
  have hmem : ∀ a : ℝ, 0 ≤ a → ∀ j,
      MemCb (r26t3_J p.d) (r26t3_qwin R a j) := by
    intro a ha j
    let i := r26t3_feature_enum p.d j
    have hhex : ∀ t : ℝ, 0 ≤ t →
        ∃ f : ℝ → Euc p.d → ℝ,
          IsClassicalAdjointW (r26t3_coeff R) t
            (oscTestFun (wholeSpaceIndex p.d : ℝ) i.2) f := by
      intro t ht
      exact fp81s21_adjoint_of_osc_test p R (htest i.2) ht
    obtain ⟨hK, -⟩ := hwindow R.ε R.ψ R.ρ R.admissible R.resulting i.2 hhex a ha i.1
    have hroot := fp81s21_qwin_eq_windowTest R a j
    rw [hroot]
    exact (HRS.MS.Tc5.tc5_cb_mono (m := r26t3_J p.d)
      (J := 4 * p.d + 42) (by unfold r26t3_J; omega) hK).1
  have hbound : ∀ a : ℝ, 0 ≤ a → ∀ j,
      cbNorm (r26t3_J p.d) (r26t3_qwin R a j) ≤ C * r26t3_feature_weight p.d j := by
    intro a ha j
    let i := r26t3_feature_enum p.d j
    have hhex : ∀ t : ℝ, 0 ≤ t →
        ∃ f : ℝ → Euc p.d → ℝ,
          IsClassicalAdjointW (r26t3_coeff R) t
            (oscTestFun (wholeSpaceIndex p.d : ℝ) i.2) f := by
      intro t ht
      exact fp81s21_adjoint_of_osc_test p R (htest i.2) ht
    obtain ⟨hK, hKbound⟩ := hwindow R.ε R.ψ R.ρ R.admissible R.resulting i.2 hhex a ha i.1
    have hroot := fp81s21_qwin_eq_windowTest R a j
    have hmono := (HRS.MS.Tc5.tc5_cb_mono (m := r26t3_J p.d)
      (J := 4 * p.d + 42) (by unfold r26t3_J; omega) hK).2
    have hα : 0 < s103_b p.d i.2 :=
      Real.rpow_pos_of_pos (oscEv_pos i.2) _
    have hn : 0 < (1 + (i.1 : ℝ)) ^ (-(5 : ℝ) / 4) :=
      Real.rpow_pos_of_pos (by positivity) _
    have hweight : r26t3_feature_weight p.d j =
        (1 + (i.1 : ℝ)) ^ (-(5 : ℝ) / 4) * s103_b p.d i.2 := by
      simpa [i] using fp81s21_qwin_feature_weight_eq p j
    have hKbound' : cbNorm (4 * p.d + 42)
        (r26t3_qwin R a j) ≤ Cw *
          ((1 + (i.1 : ℝ)) ^ (-(5 : ℝ) / 4) * s103_b p.d i.2) := by
      rw [hroot]
      simpa [r26t3_coeff, wholeSpaceIndex, hweight, mul_assoc] using hKbound
    have hmonoQ : cbNorm (r26t3_J p.d) (r26t3_qwin R a j) ≤
        cbNorm (4 * p.d + 42) (r26t3_qwin R a j) := by
      simpa [hroot, r26t3_coeff, wholeSpaceIndex] using hmono
    calc cbNorm (r26t3_J p.d) (r26t3_qwin R a j)
        ≤ cbNorm (4 * p.d + 42) (r26t3_qwin R a j) := hmonoQ
      _ ≤ Cw * ((1 + (i.1 : ℝ)) ^ (-(5 : ℝ) / 4) * s103_b p.d i.2) := hKbound'
      _ ≤ C * ((1 + (i.1 : ℝ)) ^ (-(5 : ℝ) / 4) * s103_b p.d i.2) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _)
          (mul_nonneg hn.le hα.le)
      _ = C * r26t3_feature_weight p.d j := by rw [hweight]
  refine ⟨C, hC, fun a ha => ?_⟩
  refine ⟨?_, fun j => hbound a ha j⟩
  · refine ⟨hmem a ha, ?_⟩
    have hw := fp81s21_qwin_weight_summable p
    have hmajor : Summable (fun j => C * r26t3_feature_weight p.d j) := hw.mul_left C
    exact Summable.of_nonneg_of_le
      (fun j => HRS.MS.Tc5.tc5_cb_nonneg (r26t3_J p.d) (r26t3_qwin R a j))
      (hbound a ha) hmajor

/-- The feature sum is uniformly bounded by the common root envelope times the total weight. -/
theorem fp81s21_qwin_featureSum_uniform (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 ≤ a →
          featureSum (r26t3_J p.d) (r26t3_qwin R a) ≤
            C * (∑' j : ℕ, r26t3_feature_weight p.d j) := by
  obtain ⟨δ0, hδ0, hδhalf, hmain⟩ := fp81s21_qwin_uniform p
  refine ⟨δ0, hδ0, hδhalf, fun δ hδ hδle R => ?_⟩
  obtain ⟨C, hC, hfamily⟩ := hmain δ hδ hδle R
  refine ⟨C, hC, fun a ha => ?_⟩
  obtain ⟨hsum, henv⟩ := hfamily a ha
  have hw := fp81s21_qwin_weight_summable p
  have hmajor : Summable (fun j => C * r26t3_feature_weight p.d j) := hw.mul_left C
  unfold featureSum
  calc (∑' j : ℕ, cbNorm (r26t3_J p.d) (r26t3_qwin R a j))
      ≤ ∑' j : ℕ, C * r26t3_feature_weight p.d j :=
        hsum.2.tsum_le_tsum henv hmajor
    _ = C * (∑' j : ℕ, r26t3_feature_weight p.d j) := by rw [tsum_mul_left]

/-- At every spatial point the squared cosine observations are summable, uniformly in the
start-time range certified by the common radius. -/
theorem fp81s21_qwin_pointwise_sq_summable (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∀ a : ℝ, 0 ≤ a → ∀ x : Euc p.d,
          Summable (fun j : ℕ => (r26t3_qwin R a j x) ^ 2) := by
  obtain ⟨δ0, hδ0, hδhalf, hmain⟩ := fp81s21_qwin_uniform p
  refine ⟨δ0, hδ0, hδhalf, fun δ hδ hδle R a ha x => ?_⟩
  obtain ⟨C, hC, hfamily⟩ := hmain δ hδ hδle R
  obtain ⟨hfam, hbound⟩ := hfamily a ha
  have hsquare := HRS.MS.R26T3.s21h2_summable_sq hfam
  refine Summable.of_nonneg_of_le (fun j => sq_nonneg _)
    (fun j => ?_) hsquare
  have hpoint : |r26t3_qwin R a j x| ≤
      2 * cbNorm (r26t3_J p.d) (r26t3_qwin R a j) := by
    have h := HRS.MS.Tc5.tc5_cb_sup_le (hfam.1 j) x
    rw [Real.norm_eq_abs] at h
    have hcb := HRS.MS.Tc5.tc5_cb_nonneg (r26t3_J p.d) (r26t3_qwin R a j)
    nlinarith
  calc (r26t3_qwin R a j x) ^ 2 = |r26t3_qwin R a j x| ^ 2 := (sq_abs _).symm
    _ ≤ (2 * cbNorm (r26t3_J p.d) (r26t3_qwin R a j)) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) hpoint 2

#print axioms fp81s21_qwin_weight_summable
#print axioms fp81s21_qwin_feature_weight_eq
#print axioms fp81s21_qwin_eq_windowTest
#print axioms fp81s21_qwin_uniform
#print axioms fp81s21_qwin_featureSum_uniform
#print axioms fp81s21_qwin_pointwise_sq_summable

end HRS.Fp81.S21

end

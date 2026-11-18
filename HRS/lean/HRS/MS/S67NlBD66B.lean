import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.S67NlBD49
import HRS.MS.MovAdjAux22
import HRS.MS.GradSmAux1
import HRS.MS.GradSmAux2
import HRS.MS.PoisSgAux2
import HRS.MS.PoisMaxAux2

/-!
# S6.7nl.66B: derivative-only homogeneous one-body terminal estimate
Source pin `b66ab61cf3f03a9c6f5a899ef5de61f2b34c5e44`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.BreakdownS67

open HRS HRS.Whole HRS.MS.MovLin HRS.MS.MovOsc HRS.MS.MovAdj
open HRS.MS.Mov63 HRS.MS.MovForce HRS.MS.MovC2
open HRS.MS.PoisFlow HRS.MS.PoisSg HRS.MS.PoisKolm HRS.MS.PoisHigh

variable {d : ℕ} {s β q : ℝ} {ρ₀ : Euc d → ℝ}

/-- S6.7nl.66B: derivative-only decay of the one-body semigroup applied to a `C^{j+1}` datum. -/
theorem s67bd_homogeneous_gradient_decay (H : Mov2dTh d s β q ρ₀) (j : ℕ) :
    ∃ C lam : ℝ, 0 ≤ C ∧ 0 < lam ∧
      ∀ {Ω : Type} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → Fin d → ℝ), IsBrownianFiltration P ℱ W →
      ∀ φ : Euc d → ℝ, MemCb 2 φ → ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) φ →
      cbNormVecE j (fun x => gradient φ x) < ⊤ → ∀ t : ℝ, 0 ≤ t →
      ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞)
        (sg P W (β * q) (s67bd_oneBodyB d s β ρ₀) (t / β) φ) ∧
      cbNormVecE j (fun x => gradient
        (sg P W (β * q) (s67bd_oneBodyB d s β ρ₀) (t / β) φ) x) < ⊤ ∧
      (cbNormVecE j (fun x => gradient
        (sg P W (β * q) (s67bd_oneBodyB d s β ρ₀) (t / β) φ) x)).toReal ≤
          C * Real.exp (-lam * t) * (cbNormVecE j (fun x => gradient φ x)).toReal := by
  have hβq : 0 < β * q := mul_pos H.hβ H.hq
  obtain ⟨m, hmc⟩ : ∃ m : ℕ, m = max 2 (j + 1) := ⟨_, rfl⟩
  have hm : 2 ≤ m := by rw [hmc]; exact le_max_left _ _
  have hmc' : m = 2 ∨ m = j + 1 := by rw [hmc]; exact max_choice _ _
  obtain ⟨Mb, hMb0, hMb⟩ := s67bd_onebody_drift H m
  obtain ⟨C0, hC0, hS⟩ := HRS.MS.MovAdj.s67_sg_decay.{0} (d := d) (β * q) Mb hβq hMb0 m hm
  have hcpos : 0 < HRS.MS.PoisMax.pm_c0 (β * q) Mb := HRS.MS.GradSm.s67b_c0_pos (β * q) Mb hβq
  refine ⟨((j : ℝ) + 1) * ((j : ℝ) + 1) * C0, HRS.MS.PoisMax.pm_c0 (β * q) Mb / β,
    mul_nonneg (mul_nonneg (by positivity) (by positivity)) hC0, div_pos hcpos H.hβ, ?_⟩
  intro Ω mΩ P _ ℱ W hW φ hφ hφj1 hT t ht
  obtain ⟨hφC, hφB⟩ := hφ
  have hφm : ContDiff ℝ (m : WithTop ℕ∞) φ := by
    rcases hmc' with h | h
    · rw [h]; exact hφC
    · rw [h]; exact hφj1
  have hbnd : ∀ l : ℕ, l ≤ 2 → ∃ b : ℝ, ∀ x, ‖iteratedFDeriv ℝ l φ x‖ ≤ b := by
    intro l hl
    obtain ⟨b, hb⟩ := hφB l hl
    exact ⟨b, fun x => hb (Set.mem_range_self x)⟩
  obtain ⟨b0, hb0⟩ := hbnd 0 (by norm_num)
  obtain ⟨b2, hb2⟩ := hbnd 2 le_rfl
  have hb0n : 0 ≤ b0 := (norm_nonneg _).trans (hb0 0)
  have hb2n : 0 ≤ b2 := (norm_nonneg _).trans (hb2 0)
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = (cbNormVecE j (fun x => gradient φ x)).toReal := ⟨_, rfl⟩
  have hT0 : 0 ≤ T := by rw [hTdef]; exact ENNReal.toReal_nonneg
  have hTbd : ∀ l : ℕ, l ≤ j → ∀ y : Euc d,
      ‖iteratedFDeriv ℝ l (fun x => gradient φ x) y‖ ≤ T := by
    intro l hl y
    have h1 : ENNReal.ofReal ‖iteratedFDeriv ℝ l (fun x => gradient φ x) y‖ ≤
        cbNormVecE j (fun x => gradient φ x) := by
      unfold cbNormVecE
      refine le_trans ?_ (Finset.single_le_sum (f := fun l' : ℕ => ⨆ x : Euc d,
        ENNReal.ofReal ‖iteratedFDeriv ℝ l' (fun x => gradient φ x) x‖)
        (fun _ _ => zero_le) (Finset.mem_range.2 (show l < j + 1 by omega)))
      exact le_iSup (fun x => ENNReal.ofReal ‖iteratedFDeriv ℝ l (fun x => gradient φ x) x‖) y
    rw [hTdef]
    exact (ENNReal.ofReal_le_iff_le_toReal hT.ne).1 h1
  have hMbd : ∀ i : ℕ, i ≤ m → ∀ y : Euc d, ‖iteratedFDeriv ℝ i φ y‖ ≤
      (if 1 ≤ i ∧ i ≤ j + 1 then T else b0 + b2) := by
    intro i hi y
    by_cases h : 1 ≤ i ∧ i ≤ j + 1
    · rw [if_pos h]
      obtain ⟨l, rfl⟩ : ∃ l, i = l + 1 := ⟨i - 1, by omega⟩
      have hu : ContDiff ℝ ((l + 1 : ℕ) : WithTop ℕ∞) φ :=
        hφj1.of_le (by exact_mod_cast h.2)
      rw [← HRS.MS.GradSm.s67b_norm_iter_grad hu y]
      exact hTbd l (by omega) y
    · rw [if_neg h]
      by_cases h0 : i = 0
      · subst h0
        linarith [hb0 y]
      · have h2 : i = 2 := by omega
        subst h2
        linarith [hb2 y]
  have hsum : ∀ k : ℕ, k ≤ j + 1 → ∑ i ∈ Finset.Icc 1 k,
      (if 1 ≤ i ∧ i ≤ j + 1 then T else b0 + b2) = (k : ℝ) * T := by
    intro k hk
    rw [Finset.sum_congr rfl (g := fun _ => T) (fun i hi => by
      have hi' := Finset.mem_Icc.1 hi
      exact if_pos ⟨hi'.1, by omega⟩)]
    simp [Finset.sum_const, Nat.card_Icc]
  have hdec : ∀ k : ℕ, 1 ≤ k → k ≤ j + 1 → ∀ τ : ℝ, 0 ≤ τ → ∀ x : Euc d,
      ‖iteratedFDeriv ℝ k (sg P W (β * q) (s67bd_oneBodyB d s β ρ₀) τ φ) x‖ ≤
        C0 * Real.exp (-(HRS.MS.PoisMax.pm_c0 (β * q) Mb) * τ) * ((k : ℝ) * T) := by
    intro k hk1 hkj τ hτ x
    have h1 := hS k hk1 (by omega) P ℱ W hW (s67bd_oneBodyB d s β ρ₀) hMb φ hφm
      (fun i => if 1 ≤ i ∧ i ≤ j + 1 then T else b0 + b2) hMbd τ hτ x
    beta_reduce at h1
    rw [hsum k hkj] at h1
    exact h1
  have hsg : ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞)
      (sg P W (β * q) (s67bd_oneBodyB d s β ρ₀) (t / β) φ) := by
    obtain ⟨Csg, -, hCsg⟩ := HRS.MS.PoisSg.sg_contDiff (d := d) (β * q) Mb hβq m hm (t / β)
      (div_nonneg ht H.hβ.le) (j + 1) (by omega)
    have hMscal : ∀ i ≤ j + 1, ∀ y : Euc d, ‖iteratedFDeriv ℝ i φ y‖ ≤ T + b0 + b2 := by
      intro i hi y
      refine (hMbd i (by omega) y).trans ?_
      split_ifs <;> linarith
    exact (hCsg P W (HRS.MS.PoisSg.sgNoise_of_brownian hW) _ hMb φ hφj1 (T + b0 + b2) hMscal
      (t / β) ⟨div_nonneg ht H.hβ.le, le_rfl⟩).1
  have he : -(HRS.MS.PoisMax.pm_c0 (β * q) Mb) * (t / β) =
      -(HRS.MS.PoisMax.pm_c0 (β * q) Mb / β) * t := by ring
  have hpos : 0 ≤ C0 * Real.exp (-(HRS.MS.PoisMax.pm_c0 (β * q) Mb / β) * t) :=
    mul_nonneg hC0 (Real.exp_pos _).le
  have hG : cbNormVecE j (fun x => gradient
      (sg P W (β * q) (s67bd_oneBodyB d s β ρ₀) (t / β) φ) x) ≤
      ENNReal.ofReal (((j : ℝ) + 1) * ((j : ℝ) + 1) * C0 *
        Real.exp (-(HRS.MS.PoisMax.pm_c0 (β * q) Mb / β) * t) * T) := by
    unfold cbNormVecE
    have hterm : ∀ l ∈ Finset.range (j + 1),
        (⨆ x : Euc d, ENNReal.ofReal
          ‖iteratedFDeriv ℝ l (fun x => gradient
            (sg P W (β * q) (s67bd_oneBodyB d s β ρ₀) (t / β) φ) x) x‖) ≤
        ENNReal.ofReal (C0 * Real.exp (-(HRS.MS.PoisMax.pm_c0 (β * q) Mb / β) * t) *
          (((j : ℝ) + 1) * T)) := by
      intro l hl
      have hl' : l ≤ j := by have := Finset.mem_range.1 hl; omega
      have hu : ContDiff ℝ ((l + 1 : ℕ) : WithTop ℕ∞)
          (sg P W (β * q) (s67bd_oneBodyB d s β ρ₀) (t / β) φ) :=
        hsg.of_le (by exact_mod_cast (show l + 1 ≤ j + 1 by omega))
      refine iSup_le fun x => ENNReal.ofReal_le_ofReal ?_
      rw [HRS.MS.GradSm.s67b_norm_iter_grad hu x]
      have h1 := hdec (l + 1) (by omega) (by omega) (t / β) (div_nonneg ht H.hβ.le) x
      rw [he] at h1
      have hcast : ((l + 1 : ℕ) : ℝ) ≤ (j : ℝ) + 1 := by
        have : (l : ℝ) ≤ j := by exact_mod_cast hl'
        push_cast
        linarith
      have hT' : ((l + 1 : ℕ) : ℝ) * T ≤ ((j : ℝ) + 1) * T := mul_le_mul_of_nonneg_right hcast hT0
      exact h1.trans (mul_le_mul_of_nonneg_left hT' hpos)
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (le_of_eq (by push_cast; ring))
  have hCnn : 0 ≤ ((j : ℝ) + 1) * ((j : ℝ) + 1) * C0 :=
    mul_nonneg (mul_nonneg (by positivity) (by positivity)) hC0
  refine ⟨hsg, lt_of_le_of_lt hG ENNReal.ofReal_lt_top, ?_⟩
  rw [← hTdef]
  exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg (mul_nonneg hCnn (Real.exp_pos _).le) hT0) hG

end HRS.MS.BreakdownS67

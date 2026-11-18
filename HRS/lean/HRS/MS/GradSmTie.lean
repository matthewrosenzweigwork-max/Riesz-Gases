import HRS.MS.GradSmAux4

/-!
# S6.7 packet S67B: gradient smoothing, headline theorem (`W:r2mov:gradient-smoothing`, S L4456-4492)

`gradient_smoothing_cb` (TeX: `‖∇P_tF‖_{C_b^k} ≤ C_k (1+t^{-1/2}) e^{-λt} ‖F‖_{C_b^k}`), for the one-body semigroup
`sg P W q B t` of `Δ - q x·∇ + B·∇` (`B ∈ C_b^m`, `q > 0`, Brownian filtration; `ν > 0` is the time scaling
`q' = q/ν`, `B' = B/ν`, `t' = νt`), data `F ∈ C^k` with `‖D^i F‖ ≤ M i` for `i ≤ k` (so `‖F‖_{C_b^k} ≤ ∑_{i ≤ k} M i`),
`t > 0`, drift regularity `m ≥ k + 2`:

* `P_tF ∈ C^{k+1}` and `∇P_tF ∈ C^k` (qualitative gain);
* `‖∇P_tF‖_{C_b^k} = cbNormVecE k (∇P_tF) ≤ C (1+t^{-1/2}) e^{-c t} ∑_{i ≤ k} M i`, `c = pm_c0 q Mb > 0`.

The time-dependent perturbations `-F_v·∇f_v`, `J_v f_v` of the S6.7 adjoint are SOURCES of the stationary one-body Duhamel formula
(TeX L4482-4492, `Q_t = P_tQ_0 + ∫ P_{t-r}(F_r·∇Q_r + A_rQ_r) dr`): apply the theorem to the source at fixed `v`.
-/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Interval RealInnerProductSpace ContDiff
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.PoisFlow HRS.MS.PoisSg
  HRS.MS.PoisMarkov HRS.MS.PoisKolm HRS.MS.PoisGrad HRS.MS.PoisMax HRS.MS.PoisMoll
  HRS.MS.PoisHigh

noncomputable section

universe u

namespace HRS.MS.GradSm

variable {d : ℕ}

/-- **Gradient smoothing** (`W:r2mov:gradient-smoothing`). -/
theorem gradient_smoothing_cb (q Mb : ℝ) (hq : 0 < q) (hMb : 0 ≤ Mb) (m : ℕ) (hm : 2 ≤ m) (k : ℕ)
    (hk : k + 2 ≤ m) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
      [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → Fin d → ℝ),
      IsBrownianFiltration P ℱ W → ∀ B : Euc d → Euc d, HasCbBound m Mb B →
      ∀ F : Euc d → ℝ, ContDiff ℝ (k : WithTop ℕ∞) F → ∀ M : ℕ → ℝ,
      (∀ i ≤ k, ∀ y, ‖iteratedFDeriv ℝ i F y‖ ≤ M i) → ∀ t : ℝ, 0 < t →
      ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (sg P W q B t F) ∧
      ContDiff ℝ (k : WithTop ℕ∞) (fun x => gradient (sg P W q B t F) x) ∧
      (∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (fun y => gradient (sg P W q B t F) y) x‖ ≤
        C * (1 + (Real.sqrt t)⁻¹) * Real.exp (-c * t) * ∑ i ∈ Finset.range (k + 1), M i) ∧
      cbNormVecE k (fun x => gradient (sg P W q B t F) x) ≤
        ENNReal.ofReal (C * (1 + (Real.sqrt t)⁻¹) * Real.exp (-c * t) *
          ∑ i ∈ Finset.range (k + 1), M i) := by
  obtain ⟨C, hC0, hC⟩ := s67b_gs_gain (d := d) q Mb hq hMb m hm k hk
  refine ⟨((k : ℝ) + 1) * C, pm_c0 q Mb, by positivity, s67b_c0_pos q Mb hq,
    fun {Ω} {mΩ} P _ ℱ W hW B hBm F hF M hM t ht0 => ?_⟩
  obtain ⟨hcd, hb⟩ := hC P ℱ W hW B hBm F hF M hM t ht0
  have hM0 : ∀ i ≤ k, 0 ≤ M i := fun i hi => (norm_nonneg _).trans (hM i hi 0)
  set Bd : ℝ := C * (1 + (Real.sqrt t)⁻¹) * Real.exp (-(pm_c0 q Mb) * t) *
    ∑ i ∈ Finset.range (k + 1), M i with hBd
  have hBd0 : 0 ≤ Bd := by
    have : 0 ≤ ∑ i ∈ Finset.range (k + 1), M i := Finset.sum_nonneg fun i hi => hM0 i (by
      have := Finset.mem_range.1 hi; omega)
    rw [hBd]; positivity
  have hpt : ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (fun y => gradient (sg P W q B t F) y) x‖ ≤ Bd := by
    intro j hj x
    rw [s67b_norm_iter_grad (hcd.of_le (by exact_mod_cast (by omega : j + 1 ≤ k + 1))) x]
    exact hb (j + 1) (by omega) (by omega) x
  set K : ℝ := ∑ i ∈ Finset.range (k + 1), M i with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun i hi => hM0 i (by
    have := Finset.mem_range.1 hi; omega)
  have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hCle : C ≤ ((k : ℝ) + 1) * C := le_mul_of_one_le_left hC0 hk1
  have hsq : 0 ≤ (Real.sqrt t)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg t)
  have hE : 0 ≤ Real.exp (-(pm_c0 q Mb) * t) := (Real.exp_pos _).le
  refine ⟨hcd, s67b_contDiff_gradient hcd, ?_, ?_⟩
  · intro j hj x
    refine (hpt j hj x).trans ?_
    rw [hBd]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCle (by positivity)) hE) hK0
  · unfold cbNormVecE
    have h1 : ∀ j ∈ Finset.range (k + 1), (⨆ x : Euc d,
        ENNReal.ofReal ‖iteratedFDeriv ℝ j (fun y => gradient (sg P W q B t F) y) x‖) ≤
        ENNReal.ofReal Bd := fun j hj =>
      iSup_le fun x => ENNReal.ofReal_le_ofReal (hpt j (by have := Finset.mem_range.1 hj; omega) x)
    refine (Finset.sum_le_sum h1).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    refine le_of_eq (congrArg _ ?_)
    rw [hBd]; push_cast; ring

end HRS.MS.GradSm

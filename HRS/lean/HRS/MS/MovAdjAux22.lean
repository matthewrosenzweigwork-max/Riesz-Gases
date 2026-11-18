import HRS.MS.MovAdjAux21

/-!
# S6.7 (packet P4, part 8): decay of the derivatives of the POIS semigroup

Namespace `HRS.MS.MovAdj`, helpers `s67_`.  Infrastructure for the supplement row `S:W:lem:r2mov-global-adjoint`; not a manuscript row.

`s67_sg_decay`: for `1 ≤ k ≤ m`, `‖D^k (sg_τ r)‖ ≤ C e^{-c₀ τ} ∑_{i=1}^k M_i` for every `τ ≥ 0` (short time `pois_shorttime`,
long time `pois_longtime`), uniformly in `k ≤ m`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovAdj

open HRS HRS.Whole HRS.MS.PoisKolm HRS.MS.PoisHigh HRS.MS.Mov63 HRS.MS.FlowB HRS.MS.PoisSg HRS.MS.PoisFlow
  HRS.MS.PoisMax

universe w

variable {d : ℕ}

/-- The decay statement for the `k`-th derivative with constant `C`. -/
def S67Dec (d : ℕ) (q Mb : ℝ) (m k : ℕ) (C : ℝ) : Prop :=
  ∀ {Ω : Type w} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ)
    (W : ℝ≥0 → Ω → Fin d → ℝ), IsBrownianFiltration P ℱ W → ∀ B : Euc d → Euc d, HasCbBound m Mb B →
    ∀ r : Euc d → ℝ, ContDiff ℝ (m : WithTop ℕ∞) r → ∀ M : ℕ → ℝ,
    (∀ i ≤ m, ∀ y, ‖iteratedFDeriv ℝ i r y‖ ≤ M i) → ∀ τ : ℝ, 0 ≤ τ → ∀ x,
      ‖iteratedFDeriv ℝ k (sg P W q B τ r) x‖ ≤
        C * Real.exp (-(pm_c0 q Mb) * τ) * ∑ i ∈ Finset.Icc 1 k, M i

theorem s67_pm_c0_nonneg (q Mb : ℝ) (hq : 0 < q) : 0 ≤ pm_c0 q Mb := by
  unfold pm_c0 pm_kappa
  exact mul_nonneg (Real.exp_pos _).le (le_min zero_le_one (by positivity))

theorem s67_sg_decay_k (q Mb : ℝ) (hq : 0 < q) (hMb : 0 ≤ Mb) (m : ℕ) (hm : 2 ≤ m) (k : ℕ) (hk1 : 1 ≤ k)
    (hkm : k ≤ m) : ∃ C : ℝ, 0 ≤ C ∧ S67Dec.{w} d q Mb m k C := by
  obtain ⟨Cs, hCs0, hCs⟩ := pois_shorttime.{w} (d := d) q Mb hq m hm k hk1 hkm
  obtain ⟨Cl, hCl0, hCl⟩ := pois_longtime.{w} (d := d) q Mb hq hMb m hm k hk1 hkm
  have hc0 := s67_pm_c0_nonneg q Mb hq
  set c0 := pm_c0 q Mb with hc0def
  refine ⟨max Cs Cl * Real.exp c0, mul_nonneg (hCs0.trans (le_max_left _ _)) (Real.exp_pos _).le, ?_⟩
  intro Ω mΩ P _ ℱ W hW B hBm r hr M hM τ hτ x
  have hM0 : ∀ i ≤ m, 0 ≤ M i := fun i hi => (norm_nonneg _).trans (hM i hi 0)
  have hS0 : 0 ≤ ∑ i ∈ Finset.Icc 1 k, M i :=
    Finset.sum_nonneg fun i hi => hM0 i (by have := (Finset.mem_Icc.1 hi).2; omega)
  set SS := ∑ i ∈ Finset.Icc 1 k, M i with hSS
  by_cases hτ1 : τ ≤ 1
  · have h1 := hCs P ℱ W hW B hBm r hr M hM τ hτ hτ1 x
    have e1 : 1 ≤ Real.exp c0 * Real.exp (-c0 * τ) := by
      rw [← Real.exp_add]; apply Real.one_le_exp; nlinarith
    calc ‖iteratedFDeriv ℝ k (sg P W q B τ r) x‖ ≤ Cs * SS := h1
      _ ≤ max Cs Cl * (Real.exp c0 * Real.exp (-c0 * τ)) * SS := by
          refine mul_le_mul_of_nonneg_right ?_ hS0
          calc Cs = Cs * 1 := (mul_one _).symm
            _ ≤ max Cs Cl * (Real.exp c0 * Real.exp (-c0 * τ)) :=
                mul_le_mul (le_max_left _ _) e1 zero_le_one ((hCs0.trans (le_max_left _ _)))
      _ = max Cs Cl * Real.exp c0 * Real.exp (-c0 * τ) * SS := by ring
  · push Not at hτ1
    have h1 := hCl P ℱ W hW B hBm r hr M hM τ hτ1.le x
    have hM1 : M 1 ≤ SS := Finset.single_le_sum (f := M) (fun i hi => hM0 i (by
      have := (Finset.mem_Icc.1 hi).2; omega)) (Finset.mem_Icc.2 ⟨le_rfl, hk1⟩)
    have e2 : Real.exp (-c0 * (τ - 1)) = Real.exp c0 * Real.exp (-c0 * τ) := by
      rw [← Real.exp_add]; congr 1; ring
    calc ‖iteratedFDeriv ℝ k (sg P W q B τ r) x‖ ≤ Cl * Real.exp (-c0 * (τ - 1)) * M 1 := h1
      _ ≤ Cl * Real.exp (-c0 * (τ - 1)) * SS :=
          mul_le_mul_of_nonneg_left hM1 (by positivity)
      _ ≤ max Cs Cl * Real.exp (-c0 * (τ - 1)) * SS := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _)
            (Real.exp_pos _).le) hS0
      _ = max Cs Cl * Real.exp c0 * Real.exp (-c0 * τ) * SS := by rw [e2]; ring

/-- Uniform in the order `1 ≤ k ≤ m`. -/
theorem s67_sg_decay (q Mb : ℝ) (hq : 0 < q) (hMb : 0 ≤ Mb) (m : ℕ) (hm : 2 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k, 1 ≤ k → k ≤ m → S67Dec.{w} d q Mb m k C := by
  have h : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ (1 ≤ k → k ≤ m → S67Dec.{w} d q Mb m k C) := by
    intro k
    by_cases hk : 1 ≤ k ∧ k ≤ m
    · obtain ⟨C, hC0, hC⟩ := s67_sg_decay_k.{w} (d := d) q Mb hq hMb m hm k hk.1 hk.2
      exact ⟨C, hC0, fun _ _ => hC⟩
    · exact ⟨0, le_rfl, fun h1 h2 => absurd ⟨h1, h2⟩ hk⟩
  choose Cf hCf0 hCf using h
  refine ⟨∑ k ∈ Finset.range (m + 1), Cf k, Finset.sum_nonneg fun k _ => hCf0 k, fun k hk1 hkm => ?_⟩
  have hle : Cf k ≤ ∑ k ∈ Finset.range (m + 1), Cf k :=
    Finset.single_le_sum (f := Cf) (fun k _ => hCf0 k) (Finset.mem_range.2 (by omega))
  intro Ω mΩ P _ ℱ W hW B hBm r hr M hM τ hτ x
  have h1 := hCf k hk1 hkm P ℱ W hW B hBm r hr M hM τ hτ x
  have hM0 : ∀ i ≤ m, 0 ≤ M i := fun i hi => (norm_nonneg _).trans (hM i hi 0)
  have hS0 : 0 ≤ ∑ i ∈ Finset.Icc 1 k, M i :=
    Finset.sum_nonneg fun i hi => hM0 i (by have := (Finset.mem_Icc.1 hi).2; omega)
  refine h1.trans ?_
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le) hS0

end HRS.MS.MovAdj

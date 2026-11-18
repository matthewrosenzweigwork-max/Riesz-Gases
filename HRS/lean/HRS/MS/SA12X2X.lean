import HRS.MS.SA12X2W

/-!
# S.A.12 N8 (SA12X2), part X: the tuple bound for skew `M` in the range `d - 1 < s < d`

`-∫ ω² ∂^idx F ∂^idx 𝒢 ≤ A e` with `e = ∫ W Y`: `sa12x2_decomp`, the term `T_i((∂_j a) u)` by `sa12x2_T2`,
and the telescoped remainder (a list of terms) by `sa12x2_term`.
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqT3

variable {d : ℕ}

theorem sa12x2_list_reg {ι : Type*} (f : ι → Euc d → ℝ) (L : List ι)
    (h1 : ∀ τ ∈ L, ContDiff ℝ 1 (f τ)) (hc : ∀ τ ∈ L, HasCompactSupport (f τ)) :
    ContDiff ℝ 1 (fun y => (L.map (fun τ => f τ y)).sum) ∧
      HasCompactSupport (fun y => (L.map (fun τ => f τ y)).sum) := by
  induction L with
  | nil => exact ⟨by simpa using contDiff_const, by simp only [List.map_nil, List.sum_nil]; exact HasCompactSupport.zero⟩
  | cons τ L ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun σ hσ => h1 σ (List.mem_cons_of_mem _ hσ))
      (fun σ hσ => hc σ (List.mem_cons_of_mem _ hσ))
    simp only [List.map_cons, List.sum_cons]
    exact ⟨(h1 τ List.mem_cons_self).add ih1, (hc τ List.mem_cons_self).add ih2⟩

theorem sa12x2_list_bound {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (i : Fin d) {ι : Type*}
    {w : Euc d → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w) (f : ι → Euc d → ℝ) (K : ℝ)
    (L : List ι) (h1 : ∀ τ ∈ L, ContDiff ℝ 1 (f τ)) (hc : ∀ τ ∈ L, HasCompactSupport (f τ))
    (hb : ∀ τ ∈ L, |∫ x, w x * firstRiesz d s i (f τ) x| ≤ K) :
    |∫ x, w x * firstRiesz d s i (fun y => (L.map (fun τ => f τ y)).sum) x| ≤ L.length * K := by
  induction L with
  | nil => simp [firstRiesz]
  | cons τ L ih =>
    have ih' := ih (fun σ hσ => h1 σ (List.mem_cons_of_mem _ hσ))
      (fun σ hσ => hc σ (List.mem_cons_of_mem _ hσ)) (fun σ hσ => hb σ (List.mem_cons_of_mem _ hσ))
    obtain ⟨hr1, hr2⟩ := sa12x2_list_reg f L (fun σ hσ => h1 σ (List.mem_cons_of_mem _ hσ))
      (fun σ hσ => hc σ (List.mem_cons_of_mem _ hσ))
    have hτ1 := h1 τ List.mem_cons_self
    have hτc := hc τ List.mem_cons_self
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have hadd := fun x => sa12x2_first_add hs0 hsd i hτ1 hτc hr1 hr2 x
    simp_rw [hadd, mul_add]
    have hI1 : Integrable (fun x => w x * firstRiesz d s i (f τ) x) volume :=
      (hw.mul (sa12z3_firstRiesz_cont hs0 hsd i hτ1 hτc)).integrable_of_hasCompactSupport hwc.mul_right
    have hI2 : Integrable (fun x => w x * firstRiesz d s i (fun y => (L.map (fun τ => f τ y)).sum) x)
        volume := (hw.mul (sa12z3_firstRiesz_cont hs0 hsd i hr1 hr2)).integrable_of_hasCompactSupport
          hwc.mul_right
    rw [integral_add hI1 hI2]
    refine (abs_add_le _ _).trans ?_
    have := hb τ List.mem_cons_self
    push_cast
    nlinarith

end HRS.MH.AdjointRd.Phase2SA12Near

import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.MovAdjAux24
import HRS.MS.S67NlBD55
import HRS.MS.S67NlBD61

/-!
# S6.7nl.62: induction to a finite global `Cb` gradient norm on a fixed horizon
Source pin `b66ab61cf3f03a9c6f5a899ef5de61f2b34c5e44`.
Route: induct on the jet order `n ≤ j`: order zero from the `C²` bound, each successor from
`s67bd_one_jet_finite` (packet 61) with the previously obtained uniform lower-jet amplitude; the
initial `cb` norm at order `n+1` is dominated by the one at order `j`; finally the finite sum bound
`s67_cb_le` gives both finiteness and the displayed `ofReal` inequality.
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

/-- `cbNormVecE` is monotone in the order -/
lemma s67bd62_cb_mono {n j : ℕ} (hnj : n ≤ j) (v : Euc d → Euc d) :
    cbNormVecE n v ≤ cbNormVecE j v := by
  unfold cbNormVecE
  exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))

theorem s67bd_parabolic_finite (d j : ℕ) (ν q T Mb MJ : ℝ)
    (hν : 0 < ν) (hq : 0 < q) (hT : 0 ≤ T) (hMb : 0 ≤ Mb) (hMJ : 0 ≤ MJ)
    (u a : ℝ → Euc d → ℝ) (B : ℝ → Euc d → Euc d) (J : ℝ → Euc d → ℝ)
    (hu : s67bd_ParabolicData ν q T u a B J)
    (hB : ∀ t ∈ Icc (0 : ℝ) T, ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) (B t) ∧
      ∀ i ≤ j + 1, ∀ x, ‖iteratedFDeriv ℝ i (B t) x‖ ≤ Mb)
    (hJ : ∀ t ∈ Icc (0 : ℝ) T, ContDiff ℝ (j : WithTop ℕ∞) (J t) ∧
      ∀ i ≤ j, ∀ x, ‖iteratedFDeriv ℝ i (J t) x‖ ≤ MJ)
    (hreg : ∀ t ∈ Icc (0 : ℝ) T, ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) (u t))
    (hinit : cbNormVecE j (fun x => gradient (u 0) x) < ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) T,
      cbNormVecE j (fun x => gradient (u t) x) < ⊤ ∧
      cbNormVecE j (fun x => gradient (u t) x) ≤ ENNReal.ofReal C := by
  have key : ∀ n : ℕ, n ≤ j → ∃ A : ℝ, 0 ≤ A ∧ ∀ t ∈ Icc (0 : ℝ) T, ∀ i ≤ n, ∀ x,
      ‖iteratedFDeriv ℝ i (fun y => gradient (u t) y) x‖ ≤ A := by
    intro n
    induction n with
    | zero =>
      intro _
      obtain ⟨K, hK⟩ := hu.bdd_c2
      refine ⟨|K|, abs_nonneg _, fun t ht i hi x => ?_⟩
      have hi0 : i = 0 := by omega
      subst hi0
      rw [norm_iteratedFDeriv_zero]
      have h1 := hK t ht 1 (by norm_num) x
      rw [norm_iteratedFDeriv_one] at h1
      have hg : ‖gradient (u t) x‖ = ‖fderiv ℝ (u t) x‖ := by
        unfold gradient
        exact (InnerProductSpace.toDual ℝ (Euc d)).symm.norm_map _
      rw [hg]
      exact h1.trans (le_abs_self _)
    | succ n ih =>
      intro hn
      obtain ⟨A, hA0, hA⟩ := ih (by omega)
      have hcb : cbNormVecE (n + 1) (fun x => gradient (u 0) x) < ⊤ :=
        lt_of_le_of_lt (s67bd62_cb_mono hn _) hinit
      obtain ⟨C, hC0, hC⟩ := s67bd_one_jet_finite d (n + 1) (by omega) ν q T Mb MJ A hν hq hT hMb
        hMJ hA0 u a B J hu
        (fun t ht => ⟨(hB t ht).1.of_le (by exact_mod_cast (by omega : n + 1 + 1 ≤ j + 1)),
          fun i hi x => (hB t ht).2 i (by omega) x⟩)
        (fun t ht => ⟨(hJ t ht).1.of_le (by exact_mod_cast hn),
          fun i hi x => (hJ t ht).2 i (by omega) x⟩)
        (fun t ht => (hreg t ht).of_le (by exact_mod_cast (by omega : n + 1 + 1 ≤ j + 1)))
        (fun t ht i hi x => hA t ht i (by omega) x) hcb
      refine ⟨A + C, add_nonneg hA0 hC0, fun t ht i hi x => ?_⟩
      by_cases hin : i ≤ n
      · exact (hA t ht i hin x).trans (by linarith)
      · have : i = n + 1 := by omega
        subst this
        exact (hC t ht x).trans (by linarith)
  obtain ⟨A, hA0, hA⟩ := key j le_rfl
  refine ⟨(j + 1 : ℝ) * A, by positivity, fun t ht => ?_⟩
  have hle := s67_cb_le (j := j) (v := fun x => gradient (u t) x) (Y := fun _ => A)
    (fun i hi x => hA t ht i hi x)
  have hsum : (∑ i ∈ Finset.range (j + 1), (fun _ : ℕ => A) i) = (j + 1 : ℝ) * A := by
    simp [Finset.sum_const]
  rw [hsum] at hle
  exact ⟨lt_of_le_of_lt hle ENNReal.ofReal_lt_top, hle⟩

end HRS.MS.BreakdownS67

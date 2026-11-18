import HRS.MS.R2SeAux28

/-!
# S9.9 `r2_static_edgeworth`, packet 29: finite-rank approximants and the uniform tail

Worker S99, namespace `S99`.

* `s99_Bh_sub`: `B_{k₁} - B_{k₂} = B_{k₁ - k₂}` for bounded pair kernels;
* `s99_tail`: finite-rank approximants `h_n` of a bounded pair kernel `h` (S9.1) with
  `sup_{N ≥ 2} E|B_{h_n - h}| → 0` (S9.2).
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S99

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

section Tail

variable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {a β γ : ℝ} (ha : 0 < a)
  (hβ : 0 < β) (hγ : 0 < γ) {C c BU Cs : ℝ} (hT : ThermalData d s a β C c BU)
  (hS : ∀ N : ℕ, 2 ≤ N → S46.S46Static d s a β γ Cs N)

include hd hs0 hs ha hβ hγ hT hS

theorem s99_Bh_sub {B1 B2 : ℝ} {k1 k2 : Euc d → Euc d → ℝ} (h1 : IsBoundedPairKernel s B1 k1)
    (h2 : IsBoundedPairKernel s B2 k2) {N : ℕ} (hN : 2 ≤ N) (X : EucConfig d N) :
    Bh d s a β γ N k1 X - Bh d s a β γ N k2 X = Bh d s a β γ N (fun x y => k1 x y - k2 x y) X := by
  haveI hP : IsProbabilityMeasure (S46.s46_P d s a β γ N) := (hS N hN).prob
  haveI hμ : IsProbabilityMeasure (thermalMeasure d s a β) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  have w1 := s99_kernel_wr8 hd hs0 hs ha hβ hγ hT hS h1
  have w2 := s99_kernel_wr8 hd hs0 hs ha hβ hγ hT hS h2
  have hsub : ∀ Y : EucConfig d N, pairEnergy (fun x y => k1 x y - k2 x y) Y (thermalMeasure d s a β) =
      pairEnergy k1 Y (thermalMeasure d s a β) - pairEnergy k2 Y (thermalMeasure d s a β) := by
    intro Y
    have := HRS.MS.Wr.wr9_pairEnergy_sub (N := N) w1 w2 1 Y
    simpa using this
  unfold Bh
  simp_rw [hsub]
  rw [integral_sub (s99_pairE_int hd hs0 hs ha hβ hγ hT hS h1 hN)
    (s99_pairE_int hd hs0 hs ha hβ hγ hT hS h2 hN)]
  ring

theorem s99_tail {B : ℝ} {h : Euc d → Euc d → ℝ} (hh : IsBoundedPairKernel s B h) :
    ∃ (C₁ : ℝ) (hj : ℕ → Euc d → Euc d → ℝ), IsRound2Approx s C₁ B (thermalMeasure d s a β) h hj ∧
      ∀ ε : ℝ, 0 < ε → ∃ n0 : ℕ, ∀ n ≥ n0, ∀ N : ℕ, 2 ≤ N →
        ∫ X, |Bh d s a β γ N (fun x y => hj n x y - h x y) X| ∂(S46.s46_P d s a β γ N) ≤ ε := by
  haveI hμ : IsProbabilityMeasure (thermalMeasure d s a β) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  obtain ⟨Ca, hCa⟩ := HRS.Whole.U1.round2_approximation_proof hd s hs0 hs
  obtain ⟨L, hL, -⟩ := s99_round2_density hT
  obtain ⟨hj, hap⟩ := hCa C L (thermalDensity d s a β) hL B h hh
  have hap' : IsRound2Approx s Ca B (thermalMeasure d s a β) h hj := hap
  refine ⟨Ca, hj, hap', fun ε hε => ?_⟩
  obtain ⟨Cmt, hmt⟩ := HRS.MS.R2Mt.round2_moment_transfer_proof hd s hs0 hs C L γ 2 1 B hγ
    (by norm_num) 1 le_rfl
  have hP : ∀ N : ℕ, 2 ≤ N → HasR2ActualDensity s γ 2 1 (withDensityReal (thermalDensity d s a β))
      (S46.s46_P d s a β γ N) := fun N hN => by
    haveI : IsProbabilityMeasure (S46.s46_P d s a β γ N) := (hS N hN).prob
    exact s99_actual _ (s99_P_eq hd hs0 hs ha hβ hγ N)
  obtain ⟨-, -, hTail⟩ := hmt (thermalDensity d s a β) hL (fun N => S46.s46_P d s a β γ N) hP
  obtain ⟨-, T2⟩ := hTail Ca h hj hh hap'
  obtain ⟨n0, hn0⟩ := eventually_atTop.1 (T2.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hε)))
  refine ⟨n0, fun n hn N hN => ?_⟩
  have hlt := hn0 n hn
  have hle : eLpNorm (fun X : EucConfig d N => (N : ℝ) * (pairEnergy (fun x y => hj n x y - h x y) X
      (thermalMeasure d s a β) - ∫ Y, pairEnergy (fun x y => hj n x y - h x y) Y
        (thermalMeasure d s a β) ∂(S46.s46_P d s a β γ N))) (ENNReal.ofReal 1) (S46.s46_P d s a β γ N) ≤
      ENNReal.ofReal ε :=
    (le_iSup₂_of_le () ⟨N, hN⟩ le_rfl).trans hlt.le
  have hk := HRS.MS.R2Mt.s92_diff_kernel hh hap' n
  have hmeas : Measurable fun X : EucConfig d N => Bh d s a β γ N (fun x y => hj n x y - h x y) X := by
    unfold Bh
    exact measurable_const.mul ((HRS.MS.Wr.wr9_measurable_pairEnergy hk.measurable).sub measurable_const)
  have hle' : eLpNorm (fun X : EucConfig d N => Bh d s a β γ N (fun x y => hj n x y - h x y) X) 1
      (S46.s46_P d s a β γ N) ≤ ENNReal.ofReal ε := by
    simpa [Bh] using hle
  exact (s99_l1_bound hε.le hmeas.aestronglyMeasurable hle').2

end Tail

end S99

end

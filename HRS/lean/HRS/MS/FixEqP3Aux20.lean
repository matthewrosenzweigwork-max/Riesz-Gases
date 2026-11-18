import HRS.MS.FixEqP3Aux19

/-!
# S5.7 `fixed_equation` (worker S57P), part 32: terminal-time Hölder bound of the difference of the feature orbits
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.FixEq

open HRS HRS.Whole HRS.MP.RdGen HRS.MS.Go HRS.MS.Fcau

variable {d : ℕ}

theorem s57p_td_ii {C : WholeCoeff d} {θ : Euc d → ℝ} {T : ℝ} {n : ℕ} {K : ℝ} (hθ : IsUlCutoff θ)
    (Fm : S57pFam C θ T (n + 1) K) (hn4 : 4 ≤ n) {φ : Euc d → ℝ} {Bφ Bg : ℝ} (hBφ : 0 ≤ Bφ) (hBg : 0 ≤ Bg)
    (hφ : ContDiff ℝ ((n + 1 + 1 + ⌈(d : ℝ) / 2⌉₊ : ℕ) : WithTop ℕ∞) φ)
    (hφb : ∀ l ≤ n + 1 + 1 + ⌈(d : ℝ) / 2⌉₊, ∀ x, ‖iteratedFDeriv ℝ l φ x‖ ≤ Bφ)
    (hg : ∀ u ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ ((n + 1 + 1 + ⌈(d : ℝ) / 2⌉₊ : ℕ) : WithTop ℕ∞) (generatorW C u φ) ∧
      ∀ l ≤ n + 1 + 1 + ⌈(d : ℝ) / 2⌉₊, ∀ x, ‖iteratedFDeriv ℝ l (generatorW C u φ) x‖ ≤ Bg)
    {r a b : ℝ} (hr : 0 ≤ r) (hra : r ≤ a) (hab : a ≤ b) (hbT : b ≤ T) {i : ℕ} (hi : i ≤ n) (x : Euc d) :
    IntervalIntegrable (fun u => iteratedFDeriv ℝ i (propagatorW C r u (generatorW C u φ)) x) volume a b := by
  obtain ⟨hCu0, hCu⟩ := s57pCu_spec hθ (n + 1)
  obtain ⟨-, hOrb⟩ := s57p_orbfam hθ Fm hn4 hBφ hBg hφ hφb hg
  have hBO0 : 0 ≤ |K| * (s57pCu θ hθ (n + 1) * Bg) := mul_nonneg (abs_nonneg _) (mul_nonneg hCu0 hBg)
  have hcc := s57p_jet_continuousOn Fm.gen Fm.uniq hn4 hBO0 (fun u => generatorW C u φ) hOrb.cont hOrb.classical
    hOrb.bound hr hi x
  exact s57p_ii_of_bound hab (hcc.mono (Set.Ioc_subset_Ioc hra hbT)) (fun u hu =>
    (hOrb.bound u ⟨hr.trans (hra.trans hu.1.le), hu.2.trans hbT⟩ r ⟨hr, hra.trans hu.1.le⟩).2 i (by omega) x)

end HRS.MS.FixEq

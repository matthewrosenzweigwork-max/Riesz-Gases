import HRS.MS.GenPathAux12
import HRS.MS.GoTie
import HRS.MS.GoFeatTie

/-!
# S5.6 packet P3: the pathwise Duhamel remainder bound

`s56_rem_bound`: for a collision-free configuration path `r ↦ X_r` and `t ≤ T`,
`‖(∫_0^t Comm-term_j(r) dr)_j‖_{ℓ²} ≤ C ∫_0^T (F_N(X_r,ρ_N^r) + o_N) dr`, where the `j`-th term is the interaction
integrand of the duality identity `flucInteractionRd` for the test function `U^{r,t}φ_j`.  Route: `s56_fluc_eq_comm`
(`= ½ Comm_N`), the commutator row `general_orbits_commutator_proof` (`C₀ ≥ C₀min`), summability of
`λ_j^{(J-m)/2}` (`s55f_summable`), `s56_rem_l2`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.GenPath

open HRS.Whole HRS.Whole.AppendixA HRS.MH.DualityRd

variable {d : ℕ}

theorem s56_propagator_memCb (C : WholeCoeff d) (t : ℝ) (φ : Euc d → ℝ) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) t) : MemCb 2 (propagatorW C r t φ) := by
  unfold propagatorW
  by_cases h : ∃ f, IsClassicalAdjointW C t φ f
  · rw [dif_pos h]
    have hs := h.choose_spec
    refine ⟨hs.c2 r hr, fun j hj => ?_⟩
    obtain ⟨B, hB⟩ := hs.bdd j hj
    exact ⟨B, by rintro _ ⟨x, rfl⟩; exact hB r hr x⟩
  · rw [dif_neg h]
    refine ⟨contDiff_const, fun j hj => ⟨0, ?_⟩⟩
    rintro _ ⟨x, rfl⟩
    simp

theorem s56_regSlice (b : WholeBounds d) (hb : b.Valid) (S : WholeSetup b) (N : ℕ) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) b.T) : RegSliceRd (S.ρ N r) := by
  have hdL : (d : ℝ) + 3 ≤ b.L := by
    have := hb.hL; have h0 : (0 : ℝ) ≤ b.k := Nat.cast_nonneg _
    have h1 := hb.hs0; have h2 : (0 : ℝ) ≤ d := Nat.cast_nonneg _; linarith
  obtain ⟨hm, hw, -⟩ := HRS.MS.Go.s55f_regular_slice (n := b.k + 6 + ⌈(d : ℝ) / 2⌉₊) 3
    (by omega) hdL (S.dens N r hr).1 (S.dens N r hr).2
  exact ⟨(S.mf N).density r hr, hm, hw⟩

theorem s56_rem_bound (b₀ : WholeBounds d) (hb : b₀.Valid) :
    ∃ C₀min : ℝ, ∀ b : WholeBounds d, b = { b₀ with C₀ := b.C₀ } → C₀min ≤ b.C₀ →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ S : WholeSetup b, ∀ N : ℕ, 2 ≤ N → ∀ Xp : ℝ → EucConfig d N,
      (∀ r ∈ Set.Icc (0 : ℝ) b.T, Function.Injective (Xp r)) → ∀ t ∈ Set.Icc (0 : ℝ) b.T,
      l2NormE (fun α : MultiIndex d => ∫ r in Set.Icc (0 : ℝ) t,
          flucInteractionRd (S.dyn N) (propagatorW (S.coeff N) r t (oscTestFun b.m α)) (Xp r) (S.ρ N r)) ≤
        ENNReal.ofReal C * ∫⁻ r in Set.Icc (0 : ℝ) b.T, ENNReal.ofReal
          (rieszModulatedEnergy d b.s (Xp r) (HRS.Whole.withDensityReal (S.ρ N r)) + HRS.oN d b.s b.C₀ N) := by
  obtain ⟨C₀min, hC⟩ := HRS.MS.Go.general_orbits_commutator_proof b₀ hb
  refine ⟨C₀min, fun b hbeq hC0 => ?_⟩
  obtain ⟨C₃, hC₃⟩ := hC b hbeq hC0
  have hbv : b.Valid := s56_valid_of_eq hb hbeq
  have hd1 : 1 ≤ d := by have := hbv.hd; omega
  have hsd : b.s < d := hbv.hsd
  have hsum := HRS.MS.Go.s55f_summable b hbv
  set bα : MultiIndex d → ℝ := fun α => oscEigenvalue d α ^ (((b.J : ℝ) - b.m) / 2) with hbα
  have hb0 : ∀ α, 0 ≤ bα α := fun α => Real.rpow_nonneg (oscEigenvalue_pos α).le _
  have hb1 : ∀ α, bα α ≤ 1 := fun α => by
    refine Real.rpow_le_one_of_one_le_of_nonpos (oscEv_one_le α) ?_
    have := hbv.hm
    have hJ : (b.J : ℝ) + 3 * d + 4 < b.m := this
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have : (0 : ℝ) ≤ b.J := Nat.cast_nonneg _
    linarith
  have hsum2 : Summable fun α => bα α ^ 2 :=
    hsum.of_nonneg_of_le (fun α => sq_nonneg _) (fun α => by
      have := hb1 α; have := hb0 α
      nlinarith)
  set A : ℝ := max C₃ 0 / 2 with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨A * Real.sqrt (∑' α, bα α ^ 2), by positivity, fun S N hN Xp hinj t ht => ?_⟩
  have hmain := s56_rem_l2 (fun α => bα α)
    (fun α r => flucInteractionRd (S.dyn N) (propagatorW (S.coeff N) r t (oscTestFun b.m α)) (Xp r) (S.ρ N r))
    hA0 ht.2 (fun r => rieszModulatedEnergy d b.s (Xp r) (HRS.Whole.withDensityReal (S.ρ N r)) +
      HRS.oN d b.s b.C₀ N) hb0 (fun α r hr => by
        have hrT : r ∈ Set.Icc (0 : ℝ) b.T := ⟨hr.1, hr.2.trans ht.2⟩
        have hX := hinj r hrT
        have hcomm := hC₃ S N hN (Xp r) hX r t hr.1 hr.2 ht.2 α
        have hbr := s56_fluc_eq_comm (S.dyn N) hd1 hbv.hs0 hsd (s56_regSlice b hbv S N hrT)
          (s56_propagator_memCb (S.coeff N) t (oscTestFun b.m α) hr) (Xp r)
        have hE0 : 0 ≤ rieszModulatedEnergy d b.s (Xp r) (HRS.Whole.withDensityReal (S.ρ N r)) +
            HRS.oN d b.s b.C₀ N := by
          refine S.energy_nonneg N hN r hrT (Xp r) ?_
          rintro ⟨i, j, hij, hxij⟩
          exact hij (hX hxij)
        rw [hbr, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        have h2 : |centeredPairFunctional (commutatorKernel d (S.dyn N).s
            (fun x => Torus.matVec (S.dyn N).M.transpose
              (gradient (propagatorW (S.coeff N) r t (oscTestFun b.m α)) x))) (Xp r)
            (HRS.Whole.withDensityReal (S.ρ N r))| ≤ C₃ * bα α *
              (rieszModulatedEnergy d b.s (Xp r) (HRS.Whole.withDensityReal (S.ρ N r)) +
                HRS.oN d b.s b.C₀ N) := hcomm
        have hbe : 0 ≤ bα α * (rieszModulatedEnergy d b.s (Xp r) (HRS.Whole.withDensityReal (S.ρ N r)) +
            HRS.oN d b.s b.C₀ N) := mul_nonneg (hb0 α) hE0
        have : C₃ * bα α * (rieszModulatedEnergy d b.s (Xp r) (HRS.Whole.withDensityReal (S.ρ N r)) +
            HRS.oN d b.s b.C₀ N) ≤ max C₃ 0 * (bα α * (rieszModulatedEnergy d b.s (Xp r)
              (HRS.Whole.withDensityReal (S.ρ N r)) + HRS.oN d b.s b.C₀ N)) := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) hbe
        simp only [hA]
        nlinarith)
  refine hmain.trans (le_of_eq ?_)
  congr 1
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun α => sq_nonneg _) hsum2,
    ENNReal.ofReal_rpow_of_nonneg (tsum_nonneg fun α => sq_nonneg _) (by norm_num),
    ← ENNReal.ofReal_mul hA0, Real.sqrt_eq_rpow, one_div]

end HRS.MS.GenPath

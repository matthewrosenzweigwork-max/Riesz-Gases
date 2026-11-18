import HRS.Main.A8PAux20

/-!
# Packet A8P, part 21: the deterministic covariance density `Σ̄` of the transported tests
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A8P

open HRS.GF HRS.Uniform

variable {d : ℕ}

theorem a8p_norm_le_sum_abs {q : ℕ} (v : EuclideanSpace ℝ (Fin q)) : ‖v‖ ≤ ∑ a, |v a| := by
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_iff.2 ⟨Finset.sum_nonneg fun a _ => abs_nonneg _, ?_⟩
  refine le_trans (le_of_eq ?_) (Finset.sum_sq_le_sq_sum_of_nonneg (fun a _ => abs_nonneg (v a)))
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Real.norm_eq_abs, sq_abs]

theorem a8p_grad_norm_le {f : Torus d → ℝ} (hf : Torus.IsCk 2 f) (x : Torus d) :
    ‖Torus.grad f x‖ ≤ d * Torus.cbNorm 2 f := by
  refine (a8p_norm_le_sum_abs (q := d) (Torus.grad f x)).trans ?_
  calc ∑ a, |Torus.grad f x a| ≤ ∑ _a : Fin d, Torus.cbNorm 2 f := by
        refine Finset.sum_le_sum fun a _ => ?_
        rw [a8p_grad_apply]
        exact HRS.PDE.MFPair.abs_partialDeriv_le (L := 2) (by norm_num) hf a x
    _ = d * Torus.cbNorm 2 f := by simp

section SigPkg

variable {S : MainData d} {R : ∀ N, Realization d N} {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ}
  {𝔈 : ℕ → ℝ} {Ca Λ₁ : ℝ}

theorem a8p_sb_isDet (hspec : A8AdjSpec d S.s Rg MB Λ VB ν₀ Ca Λ₁) (hCa : 0 ≤ Ca)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ} (hN : 1 ≤ N)
    {q : ℕ} (ts : Fin q → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T) (φ : Fin q → Torus d → ℝ)
    (hφc : ∀ a, Continuous (φ a)) (hφ : ∀ a, MemSobolev (PDE.mStar d : ℝ) (φ a)) :
    IsDetCovMatrix S.T
      (a8pSigBar ts (a8pG ts (a8pF S N ts φ)) (fun r => S.ρ N (Q54c.clampT S.T r))
        (2 * (S.sigma N ^ 2 * S.invβ N / N))) := by
  have hT0 : 0 ≤ S.T := S.hT.le
  have hpk := fun a => a8p_adj_pkg hspec hCa hS hN (hts a) (hφc a) (hφ a)
  have hGm : ∀ a, Measurable fun p : ℝ × Torus d => a8pG ts (a8pF S N ts φ) a p.1 p.2 := by
    intro a
    obtain ⟨-, hcl, -⟩ := hpk a
    have hm := measurable_grad_clamp (hts a).1 hcl.isC12Test
    have e : (fun p : ℝ × Torus d => a8pG ts (a8pF S N ts φ) a p.1 p.2) = fun p =>
        if p.1 ∈ Set.Icc (0 : ℝ) (ts a) then
          Torus.grad (propagator (S.dyn N) (S.ρ N) (clampTI (ts a) p.1) (ts a) (φ a)) p.2 else 0 := by
      funext p
      unfold a8pG a8pF
      split_ifs with h
      · rw [clampTI_of_mem h]
      · rfl
    rw [e]
    exact Measurable.ite (measurableSet_Icc.preimage measurable_fst) hm measurable_const
  have hGb : ∀ a r x, ‖a8pG ts (a8pF S N ts φ) a r x‖ ≤
      ∑ a', (d * (Ca * a8pK Λ₁ (ts a') (φ a'))) := by
    intro a r x
    have hnn : ∀ a', 0 ≤ (d : ℝ) * (Ca * a8pK Λ₁ (ts a') (φ a')) := fun a' => by
      have := a8pK_nonneg Λ₁ (ts a') (φ a')
      positivity
    refine le_trans ?_ (Finset.single_le_sum (fun a' _ => hnn a') (Finset.mem_univ a))
    unfold a8pG
    split_ifs with h
    · obtain ⟨-, hcl, hb⟩ := hpk a
      obtain ⟨-, -, hcb⟩ := hb r h
      refine (a8p_grad_norm_le (hcl.c2 r h) x).trans ?_
      exact mul_le_mul_of_nonneg_left hcb (Nat.cast_nonneg d)
    · simp only [norm_zero]; exact hnn a
  have hΛ := a8p_Lam_ge_one hS
  have hq0 : 0 ≤ 2 * (S.sigma N ^ 2 * S.invβ N / N) := by
    have := S.hinvβ N
    positivity
  exact a8p_sigBar_isDet hGm (a8p_rho_meas hS hN) hGb
    (fun r x => ((hS.mean_field.solution N hN).density _ (Q54c.clampT_mem hT0 r)).nonneg x)
    (fun r x => a8p_rho_le hS hN (Q54c.clampT_mem hT0 r) x) hq0 S.T

end SigPkg

end HRS.Main.A8P

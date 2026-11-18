import HRS.MS.SA16Y4Fin5

/-!
# S.A.16 (SA16Y4) Ct19: the `integrable_x` fields of `IsForwardSolutionRd` for `F = wrep G0`

`sa16y4_integrable_fields`: for `AdjointRdData`, `t ∈ (0,T]`, `σ ∈ [0,t]`, `ψ ∈ C_c^∞` and `G0 ∈ W^{m,p}`
the four pairings of `wrep G0 ∈ L^p` with `ψ`, `Δψ`, `div(ψ b^σ)` and `nonlocalTestRd` are integrable.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q

section Ct19
variable {d : ℕ}

theorem sa16y4_integrable_fields (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m) (p : ℝ)
    [Fact (2 ≤ p)] (MB Λ ΛV G₀ νbar T : ℝ) (D : WholeDyn d) (μ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hD : AdjointRdData s m MB Λ ΛV G₀ νbar D T μ) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) T) (G0 : WmpSpace d m p)
    {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ) {σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) t) :
    Integrable (fun x => wrep d m p G0 x * ψ x) ∧
      Integrable (fun x => wrep d m p G0 x * Laplacian.laplacian ψ x) ∧
      Integrable (fun x => wrep d m p G0 x * movDiv (fun y => ψ y • (D.coeff μ).drift (t - σ) y) x) ∧
      Integrable (fun x => wrep d m p G0 x * nonlocalTestRd (D.coeff μ) (t - σ) ψ x) := by
  have hr : t - σ ∈ Icc (0 : ℝ) T := ⟨by linarith [hσ.2], by linarith [hσ.1, ht.2]⟩
  have hq : ∀ {f : EuclideanSpace ℝ (Fin d) → ℝ}, IsCcInfty f →
      MemLp f (ENNReal.conjExponent (ENNReal.ofReal p)) volume := fun hf =>
    hf.1.continuous.memLp_of_hasCompactSupport hf.2
  have hW := sa16y3_wrep_memLp (p := p) G0
  obtain ⟨A, L, -, -, hbc⟩ := sa16y4_drift_const hd hs0 hsd m MB Λ ΛV G₀
  have hb1 : ∀ k : Fin d, ContDiff ℝ 1 (fun y => (D.coeff μ).drift (t - σ) y k) := fun k =>
    ((EuclideanSpace.proj k : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).contDiff.comp
      ((hbc νbar T D μ hD _ hr).1.of_le (by exact_mod_cast (by omega : 1 ≤ m + 2))))
  refine ⟨hW.integrable_mul (hq hψ), ?_, ?_, ?_⟩
  · rw [← sa16sw_lap_eq hψ.1]
    exact hW.integrable_mul (hq (sa16sw_cc_lap hψ))
  · have e : ∀ x, movDiv (fun y => ψ y • (D.coeff μ).drift (t - σ) y) x =
        ∑ k : Fin d, fderiv ℝ (fun y => (D.coeff μ).drift (t - σ) y k * ψ y) x (EuclideanSpace.single k 1) := by
      intro x
      rw [sa16y4_movDiv_eq (fun k => (hb1 k).differentiable (by simp)) (hψ.1.differentiable (by simp)) x]
      rfl
    refine (hW.integrable_mul (memLp_finset_sum Finset.univ fun k _ =>
      (sa16y4_cpsi_data (p := p) hb1 hψ k).2.2)).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.mul_apply, e x]
  · have hs0' : 0 ≤ (D.coeff μ).s := by simpa [WholeDyn.coeff, (hD.hs).1] using hs0
    obtain ⟨K, -, hK⟩ := HRS.MH.AdjointRd.Phase2SA12Limit.test_nonlocal_decay hd s hs0 hsd m hm MB Λ ΛV G₀ νbar T D μ hD ψ hψ
    obtain ⟨hKc', hKb'⟩ := hK (t - σ) hr
    obtain ⟨hq1, hq'⟩ := sa16so_conj_facts (p := p)
    exact hW.integrable_mul (sa16so_memLp_decay hKc' (K := K) (r := (d : ℝ) + 3 + s + 1) (by linarith [hs0]) hKb' hq1 hq')
end Ct19

end HRS.Whole.AppendixA.Phase2SA16R

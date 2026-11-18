import HRS.MS.SA16Y3Mem1

/-!
# S.A.16 (SA16Y3) Mem2: `P_μ φ ∈ sa16r_S d m p` and the operator bound in `WmpSpace` norms (packet P7 iso, step (a))

`sa16y3_P_memS`: for `φ ∈ C_c^∞`, `μ ∈ C^∞`, `‖D^kμ‖ ≤ Λ` (`k ≤ m+2`): `P_μ φ ∈ sa16r_S d m p`.
`sa16y3_P_Jbound`: `‖J_m (P_μ φ)‖ ≤ K Λ ‖J_{m+2} φ‖` (`K = K(d,s,p,m)`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Mem2
variable {d : ℕ} {s p : ℝ} [Fact (2 ≤ p)]

lemma sa16y3_memLp_pd (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hθ1 : 1 < s + 2 - d) (j : ℕ)
    {μ φ : Euc d → ℝ} (hμ : ContDiff ℝ ∞ μ) (hφ : IsCcInfty φ) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hCb : sa16z_Cb (j + 2) Λ μ) (idx : Fin j → Fin d) :
    MemLp (partialDeriv idx (sa16z_P s μ φ)) (ENNReal.ofReal p) volume := by
  have hp2 : (2 : ℝ) ≤ p := Fact.out
  obtain ⟨K, hK0, hK⟩ := sa16y3_pd_P_bound (s := s) hd hs0 hsd hθ1 (show 1 < p by linarith) j
  exact lt_of_le_of_lt (hK hμ hφ hΛ hCb idx) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (sa16y3_S_lt_top hφ _))

lemma sa16y3_S_memLp (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hθ1 : 1 < s + 2 - d) (m : ℕ)
    {μ φ : Euc d → ℝ} (hμ : ContDiff ℝ ∞ μ) (hφ : IsCcInfty φ) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hCb : sa16z_Cb (m + 2) Λ μ) :
    MemLp (sa16j_S d m (sa16z_P s μ φ)) (ENNReal.ofReal p) volume := by
  have hPs : ContDiff ℝ ∞ (sa16z_P s μ φ) := sa16z_P_smooth hs0 hsd hμ hφ
  have hg : MemLp (fun x => ∑ j ∈ Finset.range (m + 1), ∑ idx : Fin j → Fin d,
      ‖partialDeriv idx (sa16z_P s μ φ) x‖) (ENNReal.ofReal p) volume := by
    refine memLp_finsetSum _ fun j hj => memLp_finsetSum _ fun idx _ => ?_
    exact (sa16y3_memLp_pd hd hs0 hsd hθ1 j hμ hφ hΛ (sa16z_Cb_mono (by have := Finset.mem_range.1 hj; omega) hCb)
      idx).norm
  refine hg.mono' (sa16j_S_cont hPs m).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sa16j_S_nonneg d m _ x)]
  simpa [Real.norm_eq_abs] using sa16j_S_le m (sa16z_P s μ φ) x

theorem sa16y3_P_memS (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hθ1 : 1 < s + 2 - d) (m : ℕ)
    {μ φ : Euc d → ℝ} (hμ : ContDiff ℝ ∞ μ) (hφ : IsCcInfty φ) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hCb : sa16z_Cb (m + 2) Λ μ) : sa16z_P s μ φ ∈ sa16r_S d m p :=
  sa16r_mem_S m (sa16z_P_smooth hs0 hsd hμ hφ) (sa16y3_S_memLp hd hs0 hsd hθ1 m hμ hφ hΛ hCb)

theorem sa16y3_P_Jbound (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hθ1 : 1 < s + 2 - d) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {μ : Euc d → ℝ}, ContDiff ℝ ∞ μ → ∀ {Λ : ℝ}, 0 ≤ Λ → sa16z_Cb (m + 2) Λ μ →
      ∀ (φ : ccSub d) (f : sa16r_S d m p), f.1 = sa16z_P s μ φ.1 →
        ‖sa16r_J d m p f‖ ≤ K * Λ * ‖sa16r_Jcc d (m + 2) p φ‖ := by
  obtain ⟨K, hK0, hK⟩ := sa16y3_P_jetbound (s := s) (p := p) hd hs0 hsd hθ1 m
  refine ⟨K, hK0, fun {μ} hμ {Λ} hΛ hCb φ f hf => ?_⟩
  have hS : MemLp (sa16j_S d m f.1) (ENNReal.ofReal p) volume := by
    rw [hf]; exact sa16y3_S_memLp hd hs0 hsd hθ1 m hμ φ.2 hΛ hCb
  rw [sa16r_J_norm m hS, sa16r_Jcc_norm, hf]
  have hfin : eLpNorm (wJet (m + 2) φ.1) (ENNReal.ofReal p) volume ≠ ⊤ :=
    (sa16r_jet_memLp_cc (p := p) φ.2 (m + 2)).eLpNorm_lt_top.ne
  have h1 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) (hK hμ φ.2 hΛ hCb)
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg hK0 hΛ)] at h1

end Mem2

end HRS.Whole.AppendixA.Phase2SA16R

import HRS.MS.SpecAux47

/-!
# S8P: Weyl-type growth `ω_n ≥ c (n+1)^{1/d}` (S8.7, packet b6, assembly)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  `s8p_growth`: for the eigen-data of `SpecAux46`, there is `c > 0` with
`c (n+1)^{1/d} ≤ ω_n` for all `n`.  The profiles `w_i = √ρ e_i` are linearly independent (biorthogonal to `φ_k`), satisfy the Rayleigh
bound `s8p_rayleigh` on their spans, and `s8p_growth_count`/`s8p_growth_lin` convert this to the growth.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal RealInnerProductSpace ContDiff

namespace HRS.MS.Spec

open HRS HRS.Whole HRS.MS.MovDec HRS.MS.MovLin HRS.MS.MovOsc

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ} {M : ℝ} {h : S8pRho d s ρ M}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

theorem s8p_growth (H : Mov2dTh d s β q ρ) (ψ0 : 𝓢R)
    (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x)) (D : S8pEigData d s β ρ h) :
    ∃ c : ℝ, 0 < c ∧ ∀ l : ℕ, c * ((l : ℝ) + 1) ^ (1 / (d : ℝ)) ≤ D.om l := by
  have hd1 : 1 ≤ d := by have := H.hd; omega
  obtain ⟨wS, hpair, Cr, hCr, hR⟩ := s8p_rayleigh H ψ0 hψ0 D
  obtain ⟨b, hb⟩ := exists_hermiteHilbertBasisD (d := d)
  set u : ℕ → Lp ℝ 2 (volume : Measure (Euc d)) := fun i => (wS i).toLp 2 volume with hu
  have hpair' : ∀ i m : ℕ, ⟪u i, (D.φ m).toLp 2 volume⟫ = if i = m then 1 else 0 := by
    intro i m
    rw [hu]
    exact (mov2e_inner_toLp ((wS i).memLp 2) ((D.φ m).memLp 2)).trans (hpair i m)
  have hli : LinearIndependent ℝ u := by
    rw [linearIndependent_iff']
    intro t g hg i hi
    have := congrArg (fun z => ⟪z, (D.φ i).toLp 2 volume⟫) hg
    simp only [sum_inner, real_inner_smul_left, hpair', inner_zero_left] at this
    simpa [hi] using this
  have hmain : ∀ l : ℕ, ((l : ℝ) + 1) ≤ (Cr * (D.om l + 1) + 2) ^ d := by
    intro l
    refine s8p_growth_count b u hli l hCr (Ω := D.om l) (D.lam_pos.le.trans (D.lam_le l)) ?_
    intro v hv
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hv
    set S : 𝓢R := ∑ i : Fin (l + 1), a i • wS ↑i with hSdef
    have hvS : (∑ i : Fin (l + 1), a i • u ↑i) = S.toLp 2 volume := by
      have := map_sum (SchwartzMap.toLpCLM ℝ ℝ 2 (volume : Measure (Euc d))) (fun i : Fin (l + 1) => a i • wS ↑i)
        Finset.univ
      simp only [map_smul, SchwartzMap.toLpCLM_apply] at this
      rw [hSdef]
      exact this.symm
    rw [hvS]
    obtain ⟨hsum, htsum⟩ := s8p_osc_tsum S
    have hbα : ∀ α, b α = hermiteLpD α := hb
    simp_rw [hbα]
    refine ⟨hsum, ?_⟩
    rw [htsum, mov2e_toLp_norm_sq]
    exact hR l a
  obtain ⟨c, hc, hcl⟩ := s8p_growth_lin hd1 hCr D.lam_pos
  exact ⟨c, hc, fun l => hcl l (D.om l) (D.lam_le l) (hmain l)⟩

end HRS.MS.Spec

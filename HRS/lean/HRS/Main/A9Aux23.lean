import HRS.Main.A9Aux22

/-!
# Packet A9, part 23: the Gaussian coupling of Proposition A.34 at the adjoint level `γ`
(the proof of `a34_gauss_couple` uses stability only at the output level `m_*`; the hypotheses of
`main_torus_field_limit` give the adjoint level `γ`, not `γ+2`)
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory
open scoped ENNReal NNReal BigOperators ComplexConjugate RealInnerProductSpace

namespace HRS.Main.A9

open HRS HRS.PDE HRS.PDE.ET HRS.A33 HRS.Main HRS.A34

variable {d : ℕ}

/-- The pieces of the coefficient discrepancy (adjoint level `m` suffices). -/
theorem a9_delta_facts (S : MainData d) (L : LimitCoeffs d) (m N : ℕ) (Rg : Regime)
    (ν₀ MB Λ VB : ℝ)
    (hAN : AdjointData S.s m Rg MB Λ VB (S.dyn N) ν₀ S.T (S.ρ N))
    (hAL : AdjointData S.s m Rg MB Λ VB (L.dyn S) ν₀ S.T L.ρ) :
    0 ≤ S.coeffDiscrepancy L m N ∧
    (∀ r ∈ Set.Icc (0 : ℝ) S.T, Torus.cbNorm (m + 2) (S.ρ N r - L.ρ r) ≤ S.coeffDiscrepancy L m N) ∧
    |S.invβ N - L.invβ| ≤ S.coeffDiscrepancy L m N ∧
    |2 * S.qN N - 2 * L.invβstar| ≤ S.coeffDiscrepancy L m N ∧
    |S.AN N - L.A| ≤ S.coeffDiscrepancy L m N := by
  have hbdd : BddAbove (Set.range fun r : Set.Icc (0 : ℝ) S.T =>
      Torus.cbNorm (m + 2) (S.ρ N r - L.ρ r)) := by
    refine ⟨Λ + Λ, ?_⟩
    rintro _ ⟨r, rfl⟩
    have h1 := hAN.hμ.smooth r r.2
    have h2 := hAL.hμ.smooth r r.2
    have h1' : Torus.IsCk (m + 2) (S.ρ N r) := h1.of_le (by exact_mod_cast (by omega : m + 2 ≤ m + 3))
    have h2' : Torus.IsCk (m + 2) (L.ρ r) := h2.of_le (by exact_mod_cast (by omega : m + 2 ≤ m + 3))
    refine (cbNorm_sub_le' (m + 2) _ _ h1' h2').trans (add_le_add ?_ ?_)
    · exact (HRS.PDE.cbNorm_mono' (by omega) _).trans (hAN.hμ.bound r r.2)
    · exact (HRS.PDE.cbNorm_mono' (by omega) _).trans (hAL.hμ.bound r r.2)
  have hsup0 : 0 ≤ ⨆ r : Set.Icc (0 : ℝ) S.T, Torus.cbNorm (m + 2) (S.ρ N r - L.ρ r) :=
    Real.iSup_nonneg fun r => Finset.sum_nonneg fun j _ => Real.iSup_nonneg fun _ => norm_nonneg _
  have e : S.coeffDiscrepancy L m N = |S.invβ N - L.invβ| + |2 * S.qN N - 2 * L.invβstar| +
      |S.AN N - L.A| + ⨆ r : Set.Icc (0 : ℝ) S.T, Torus.cbNorm (m + 2) (S.ρ N r - L.ρ r) := rfl
  have a1 := abs_nonneg (S.invβ N - L.invβ)
  have a2 := abs_nonneg (2 * S.qN N - 2 * L.invβstar)
  have a3 := abs_nonneg (S.AN N - L.A)
  refine ⟨by rw [e]; positivity, fun r hr => ?_, by rw [e]; linarith, by rw [e]; linarith,
    by rw [e]; linarith⟩
  rw [e]
  have := le_ciSup hbdd ⟨r, hr⟩
  linarith

theorem a9_gauss_couple (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (Rg : Regime)
    (ν₀ MB Λ VB T : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : MainData d) (L : LimitCoeffs d), S.s = s → S.T = T →
      CoeffConvergence S L Rg ν₀ MB Λ VB (gammaIdx d) (gammaIdx d) →
      ∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ νG νGlim : Measure (NegSobolev d (gammaIdx d : ℝ)),
        IsLinearFieldNoise (S.dyn N) (S.ρ N) (S.qN N) t (gammaIdx d : ℝ) νG →
        IsLinearFieldNoise (L.dyn S) L.ρ L.invβstar t (gammaIdx d : ℝ) νGlim →
        ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
          (G₁ G₂ : Ω → NegSobolev d (gammaIdx d : ℝ)), Measurable G₁ ∧ Measurable G₂ ∧
          P.map G₁ = νG ∧ P.map G₂ = νGlim ∧ Integrable (fun ω => ‖G₁ ω - G₂ ω‖ ^ 2) P ∧
          ∫ ω, ‖G₁ ω - G₂ ω‖ ^ 2 ∂P ≤ C * (S.coeffDiscrepancy L (gammaIdx d) N +
            S.coeffDiscrepancy L (gammaIdx d) N ^ 2) := by
  have hm3 := ClassicalPart.three_le_mStar d
  have hγ : gammaIdx d = mStar d + d + 3 := rfl
  obtain ⟨Ch, hCh, hh⟩ := a34_h_diff_field hd s hs0 hsd Rg ν₀ MB Λ VB T
  have hd2 : (d : ℝ) < 2 * (((d + 1 : ℕ)) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)]
  have hsum : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-(2 * (((d + 1 : ℕ)) : ℝ))) :=
    summable_jp_rpow (d := d) _ hd2
  set Sd : ℝ := ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * (((d + 1 : ℕ)) : ℝ))) with hSd
  have hSd0 : 0 ≤ Sd := tsum_nonneg fun k => Real.rpow_nonneg (Torus.jp_pos _).le _
  refine ⟨Ch * Sd + 1, by positivity, ?_⟩
  intro S L hs hT hcoef N hN t ht νG νGlim hνG hνGlim
  subst hs hT
  have hAN := hcoef.seq_adjoint N hN
  have hAL := hcoef.limit_adjoint
  have hAN' : AdjointData (S.dyn N).s (gammaIdx d) Rg MB Λ VB (S.dyn N) ν₀ S.T (S.ρ N) :=
    HRS.PDE.StabAux.adjointData_mono (by omega) hAN
  have hAL' : AdjointData (L.dyn S).s (gammaIdx d) Rg MB Λ VB (L.dyn S) ν₀ S.T L.ρ :=
    HRS.PDE.StabAux.adjointData_mono (by omega) hAL
  have hAN2 : AdjointData S.s (mStar d + 2) Rg MB Λ VB (S.dyn N) ν₀ S.T (S.ρ N) :=
    HRS.PDE.StabAux.adjointData_mono (by omega) hAN
  have hAL2 : AdjointData S.s (mStar d + 2) Rg MB Λ VB (L.dyn S) ν₀ S.T L.ρ :=
    HRS.PDE.StabAux.adjointData_mono (by omega) hAL
  obtain ⟨hΔ0, hρΔ, hβΔ, hqΔ, hAΔ⟩ := a9_delta_facts S L (gammaIdx d) N Rg ν₀ MB Λ VB hAN hAL
  have hq := a34_qScale_bounds (N := N) (by omega) (S.hκ N) (S.hinvβ N)
  set Δ := S.coeffDiscrepancy L (gammaIdx d) N with hΔ
  obtain ⟨Ω, mΩ, P, hP, G₁, G₂, hm₁, hm₂, hc₁, hc₂, hcov₁, hcov₂, hbound⟩ :=
    a34_field_couple hd (gammaIdx d) (by omega) (by omega) Rg MB Λ VB ν₀ S.T (S.dyn N) (L.dyn S)
      (S.ρ N) L.ρ (S.qN N) L.invβstar hq.1 L.hinvβstar hAN' hAL' ht
  haveI := hP
  -- the pointwise (in the mode) bound
  set c : NonzeroLattice d → ℝ := fun k => Ch * (Δ + Δ ^ 2) *
    Lattice.jp k.1 ^ (-(2 * (((d + 1 : ℕ)) : ℝ))) with hc
  have hcs : Summable c := hsum.mul_left _
  have hbd : ∀ k : NonzeroLattice d, (Lattice.jp k.1 ^ (-((gammaIdx d : ℕ) : ℝ))) ^ 2 *
      ∫ p, ‖a34_h (S.dyn N) (S.ρ N) (S.qN N) t (Torus.realMode k) p -
        a34_h (L.dyn S) L.ρ L.invβstar t (Torus.realMode k) p‖ ^ 2 ∂(a33_mu0 d S.T) ≤ c k := by
    intro k
    have h1 := hh (S.dyn N) (L.dyn S) (S.ρ N) L.ρ (S.qN N) L.invβstar Δ hAN2 hAL2 rfl rfl hΔ0
      (fun r hr => (HRS.PDE.cbNorm_mono' (by omega) _).trans (hρΔ r hr))
      hβΔ hq.1 hq.2 L.hinvβstar hqΔ t ht (Torus.realMode k) (a33_cont (HRS.FieldSingAux.isSmooth_realMode k))
      (a33_memSob _ (HRS.FieldSingAux.isSmooth_realMode k))
    rw [a33_sobolevNorm_realMode] at h1
    have hj := Torus.jp_pos k.1
    have hex : 2 * (-((gammaIdx d : ℕ) : ℝ)) + 2 * ((mStar d + 2 : ℕ) : ℝ) =
        -(2 * (((d + 1 : ℕ)) : ℝ)) := by
      rw [hγ]; push_cast; ring
    calc (Lattice.jp k.1 ^ (-((gammaIdx d : ℕ) : ℝ))) ^ 2 * ∫ p, ‖a34_h (S.dyn N) (S.ρ N) (S.qN N) t
          (Torus.realMode k) p - a34_h (L.dyn S) L.ρ L.invβstar t (Torus.realMode k) p‖ ^ 2
          ∂(a33_mu0 d S.T)
        ≤ (Lattice.jp k.1 ^ (-((gammaIdx d : ℕ) : ℝ))) ^ 2 *
          (Ch * (Δ + Δ ^ 2) * (Lattice.jp k.1 ^ ((mStar d + 2 : ℕ) : ℝ)) ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
      _ = Ch * (Δ + Δ ^ 2) * (Lattice.jp k.1 ^ (2 * (-((gammaIdx d : ℕ) : ℝ))) *
          Lattice.jp k.1 ^ (2 * ((mStar d + 2 : ℕ) : ℝ))) := by
          rw [Torus.jp_rpow_sq, Torus.jp_rpow_sq]; ring
      _ = c k := by
          rw [← Real.rpow_add hj, hex]
  obtain ⟨hint, hb⟩ := hbound c hcs hbd
  have hmain : ∫ ω, ‖G₁ ω - G₂ ω‖ ^ 2 ∂P ≤ (Ch * Sd + 1) * (Δ + Δ ^ 2) := by
    refine hb.trans ?_
    have e : ∑' k, c k = Ch * (Δ + Δ ^ 2) * Sd := by
      simp only [hc]; rw [tsum_mul_left]
    rw [e]
    have : 0 ≤ Δ + Δ ^ 2 := by positivity
    nlinarith
  obtain ⟨e⟩ := a33_exists_equiv hd
  have hPG₁ : IsProbabilityMeasure (P.map G₁) := (Measure.isProbabilityMeasure_map_iff hm₁.aemeasurable).2 hP
  have hPG₂ : IsProbabilityMeasure (P.map G₂) := (Measure.isProbabilityMeasure_map_iff hm₂.aemeasurable).2 hP
  haveI := hνG.1
  haveI := hνGlim.1
  have u₁ : P.map G₁ = νG := a34_gauss_unique e hc₁ hνG.2.1
    (fun φ ψ hφ hψ => by rw [hcov₁ φ ψ hφ hψ, hνG.2.2 φ ψ hφ hψ])
  have u₂ : P.map G₂ = νGlim := a34_gauss_unique e hc₂ hνGlim.2.1
    (fun φ ψ hφ hψ => by rw [hcov₂ φ ψ hφ hψ, hνGlim.2.2 φ ψ hφ hψ])
  exact ⟨Ω, mΩ, P, hP, G₁, G₂, hm₁, hm₂, u₁, u₂, hint, hmain⟩

end HRS.Main.A9

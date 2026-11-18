import HRS.MC.E213Final

/-!
# Packet E214A, lemma 3: `edgeworth_window` with the Gaussian data exposed

`edgeworth_window_gd`: the proof of `HRS.MC.E213Final.edgeworth_window_proof`, with the witness `K` shown to be
`gd.Kproj T` for a `GaussData` `gd`.  (Used to prove that the antecedent of the uniqueness theorem is non-vacuous.)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E214A

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213Final

variable {d : ℕ}

theorem edgeworth_window_gd (S : PreparedData d) (β₀ m T : ℝ) (hE : EdgeworthHyp S β₀ m) (hT : 0 < T) :
    ∃ (gd : GaussData S β₀ hE) (ε : ℕ → ℝ), IsWindowEdgeworth S β₀ m T (gd.Kproj T) ε := by
  obtain ⟨gd⟩ := HRS.MC.E213U4.exists_gaussData_proof hE
  refine ⟨gd, ?_⟩
  obtain ⟨CK, hCK⟩ := HRS.MC.E213U11.Kproj_bounded_proof gd T hT
  have hqual : ∀ η : ℝ, η > 0 → ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ x : ExpData S β₀ m T,
      |(fun (N : ℕ) (x : ExpData S β₀ m T) => if x.N = N then x.expr (gd.Kproj T) else 0) N x| ≤ η := by
    intro η hη
    obtain ⟨N₀, hN₀⟩ := uniform_over_realisations_final hE T hT gd η hη
    refine ⟨N₀, fun N hN x => ?_⟩
    by_cases hx : x.N = N
    · simp only [hx, if_true]
      have h0 : 0 ≤ x.expr (gd.Kproj T) := abs_nonneg _
      rw [abs_of_nonneg h0]
      exact hN₀ x (hx ▸ hN)
    · simp only [hx, if_false, abs_zero]
      exact hη.le
  have hbdd : ∀ N : ℕ, ∃ C : ℝ, ∀ x : ExpData S β₀ m T,
      |(fun (N : ℕ) (x : ExpData S β₀ m T) => if x.N = N then x.expr (gd.Kproj T) else 0) N x| ≤ C := by
    intro N
    refine ⟨2 * Real.sqrt N + CK / 6 + |CK| / 6, fun x => ?_⟩
    by_cases hx : x.N = N
    · simp only [hx, if_true]
      have h0 : 0 ≤ x.expr (gd.Kproj T) := abs_nonneg _
      rw [abs_of_nonneg h0]
      have h1 := HRS.MC.E213U6.expr_le_proof T (gd.Kproj T) CK (fun a ha => hCK a ha) x
      subst hx
      have h2 : CK / 6 ≤ |CK| / 6 := by
        have := le_abs_self CK
        linarith
      linarith [abs_nonneg CK]
    · simp only [hx, if_false, abs_zero]
      have := Real.sqrt_nonneg (N : ℝ)
      linarith [abs_nonneg CK, neg_abs_le CK]
  obtain ⟨ε, hε0, -, hεbd⟩ := E213B.e213b_exists_eps (ι := ExpData S β₀ m T)
    (fun (N : ℕ) (x : ExpData S β₀ m T) => if x.N = N then x.expr (gd.Kproj T) else 0) hqual hbdd
  refine ⟨ε, ?_⟩
  refine ⟨fun a ha M σ => Kproj_symmetric_final gd T hT a ha M σ, ⟨CK, fun a ha => hCK a ha⟩, hε0, ?_,
    fun a ha => HRS.MC.E213U18.Kproj_formula_proof gd T hT a ha⟩
  intro a ha N hN Ω _ P _ X₀ W X hSel hfilt hlaw ν hν Ω' _ P' _ Z₀ Z hZ Φ hΦ
  have h := hεbd N hN ⟨a, ha, N, hN, Ω, P, X₀, W, X, hSel, hfilt, hlaw, ν, hν, Ω', P', Z₀, Z, hZ, Φ, hΦ⟩
  simp only [if_true] at h
  have h0 : 0 ≤ (ExpData.mk a ha N hN Ω P X₀ W X hSel hfilt hlaw ν hν Ω' P' Z₀ Z hZ Φ hΦ).expr (gd.Kproj T) :=
    abs_nonneg _
  rw [abs_of_nonneg h0] at h
  exact h

end HRS.MC.E214A

end

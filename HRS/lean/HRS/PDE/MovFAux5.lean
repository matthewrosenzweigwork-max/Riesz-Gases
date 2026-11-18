import HRS.PDE.MovFAux1
import HRS.PDE.MeanField

/-!
# MOVF Aux5: bridges A and A' from Proposition 5.1 (`PDE.finite_reg_*`)

`movf_finiteRegHyp`: the data of `Regime.finiteRegHyp`.  `movf_traj_uniform`: all-time `C²` and positivity bounds.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem movf_finiteRegHyp {s β : ℝ} {V ρ₀ : Torus d → ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (hV : Torus.IsSmooth V) (hρ₀ : SmoothPosDensity ρ₀) (K : ℕ) (hK : (d : ℝ) / 2 + 6 < K) :
    PDE.FiniteRegHyp d s β β K V ρ₀ := by
  have hcont : Continuous ρ₀ := PDE.MFAux.continuous_of_isCk (ContDiff.of_le
    (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift ρ₀) from hρ₀.smooth)
    (by exact_mod_cast le_top))
  obtain ⟨x₀, -, hx₀⟩ := (isCompact_univ (X := Torus d)).exists_isMinOn Set.univ_nonempty
    hcont.continuousOn
  exact ⟨hs0, hsd, hβ, le_rfl, hK,
    PDE.ClassicalAux.isCk_of_le (by rw [← WithTop.coe_natCast]; exact WithTop.coe_le_coe.mpr le_top) hV,
    hρ₀.density, PDE.MFSemigroup.memSobolev_of_isSmooth hρ₀.smooth _,
    ⟨ρ₀ x₀, hρ₀.pos x₀, fun x => hx₀ (Set.mem_univ x)⟩⟩

theorem movf_K_spec (d : ℕ) : (d : ℝ) / 2 + 6 < (⌊(d : ℝ) / 2 + 6⌋₊ + 1 : ℕ) := by
  have := Nat.lt_floor_add_one ((d : ℝ) / 2 + 6)
  push_cast; exact this

theorem movf_traj_uniform (s β : ℝ) (V ρ₀ : Torus d → ℝ) (ρ : ℝ → Torus d → ℝ) (hs0 : 0 ≤ s)
    (hsd : s < d) (hβ : 0 < β) (hV : Torus.IsSmooth V) (hρ₀ : SmoothPosDensity ρ₀)
    (hglobal : ∀ K : ℕ, (d : ℝ) / 2 + 6 < K →
      ∃ ρc : ℝ → (Lattice d → ℂ), PDE.IsMFSolutionHK d s V β⁻¹ K ρ₀ ρc ∧
        ∀ t, 0 ≤ t → PDE.mfPath ρc t = ρ t) :
    ∃ c₀ Λ₂ : ℝ, 0 < c₀ ∧ ∀ t : ℝ, 0 ≤ t → (∀ x, c₀ ≤ ρ t x) ∧ Torus.cbNorm 2 (ρ t) ≤ Λ₂ := by
  have hd1 : 1 ≤ d := by
    have : (0 : ℝ) < d := lt_of_le_of_lt hs0 hsd
    exact_mod_cast this
  set K : ℕ := ⌊(d : ℝ) / 2 + 6⌋₊ + 1 with hKdef
  have hK := movf_K_spec d
  have H := movf_finiteRegHyp hs0 hsd hβ hV hρ₀ K hK
  obtain ⟨ρc, hρc, hρ⟩ := hglobal K hK
  obtain ⟨c, C, hc, hb⟩ := PDE.finite_reg_uniform_bounds hd1 s β β K V ρ₀ H
  obtain ⟨Ce, hCe⟩ := PDE.toFun_isCk_le (d := d) 2 (K : ℝ) (by
    have : (d : ℝ) / 2 + 6 < K := hK
    linarith)
  have hβm : β ∈ Set.Icc β β := ⟨le_rfl, le_rfl⟩
  refine ⟨c, max Ce 0 * C, hc, fun t ht => ?_⟩
  obtain ⟨hb1, hb2⟩ := hb β hβm ρc hρc t ht
  have hreal := PDE.MFGlobal.isRealCoeff_of_isMFSolutionHK hd1 s β β K V ρ₀ H β hβm ρc hρc t ht
  have hmem : PDE.MemHs (K : ℝ) (ρc t) := hρc.cont.1 t ht
  rw [← hρ t ht]
  refine ⟨fun x => (hb1 x).1, ?_⟩
  have := (hCe (ρc t) hmem hreal).2
  calc Torus.cbNorm 2 (PDE.mfPath ρc t) ≤ Ce * PDE.hsNorm (K : ℝ) (ρc t) := this
    _ ≤ max Ce 0 * PDE.hsNorm (K : ℝ) (ρc t) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
    _ ≤ max Ce 0 * C := mul_le_mul_of_nonneg_left hb2 (le_max_right _ _)

end HRS

end

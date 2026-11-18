import HRS.MS.S104eEx2
import HRS.Whole.AppendixAAdjoint
import HRS.MS.UlNormAux1

/-!
# S10.4 (nonlinear), packet S104E-7: existence along the nonlinear coefficient from S.A.12 (conditional tie)

`s104e_hex_of_adjoint_rd`: `S104eHex d s a β ρβ εstar c₁ C₁` (classical adjoint solutions for every Hermite datum `φ_α` and every terminal time `t ≥ 0` along every
resulting solution, for every `ε_*, c₁, C₁`) from the frozen statements `adjoint_rd` (existence, S.A.12) and `adjoint_rd_classical` (S.A.12(a)), taken as hypotheses
(`type_of%`).  `AdjointRdData` is supplied by `s104e_coeffHyp` (`CoeffHypRd`, order `m+3 = ⌊d/2⌋+6`), `s104e_vhyp`, `s104e_regime`; the datum `φ_α` is a Schwartz-type
function (`SyN`, `s103c_phi_syn3`), hence `C²` with finite `H^m_uloc` norm (`ulocNormE_le_cb`); `t = 0` is `s104e_hex_zero`.
This does NOT replace the direct construction; it shows that the existence clause of `S104bTermRegGen` is exactly S.A.12 on the nonlinear trajectory.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S104e

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.S104b HRS.MS.Mov63 HRS.MS.S105r HRS.MS.R2WinOrbNL HRS.MS.R2WinOrb

variable {d : ℕ}

theorem s104e_hex_of_adjoint_rd
    (h12 : type_of% @HRS.Whole.AppendixA.adjoint_rd)
    (h12c : type_of% @HRS.Whole.AppendixA.adjoint_rd_classical)
    (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    (εstar c₁ C₁ : ℝ) {ρβ : Euc d → ℝ} (hρβ : IsThermalEquilibrium d s a β ρβ) :
    S104eHex d s a β ρβ εstar c₁ C₁ := by
  intro ε ψ ρ hadm hres α t ht
  rcases ht.eq_or_lt with h0 | hpos
  · subst h0
    exact s104e_hex_zero hd hs0 hsd ha hβ εstar c₁ C₁ hρβ hres α
  have hd1 : 1 ≤ d := by omega
  set m : ℕ := HRS.Whole.mStar d with hm
  have hmle : m + 3 ≤ 100 * d + 1000 := by
    rw [hm]; unfold HRS.Whole.mStar; omega
  have hm1 : 1 ≤ m := by rw [hm]; unfold HRS.Whole.mStar; omega
  obtain ⟨Λ, hΛ⟩ := s104e_coeffHyp hd hs0 hsd ha hβ εstar c₁ C₁ m hmle hρβ hadm hres t hpos.le
  obtain ⟨ΛV, G₀, hV⟩ := s104e_vhyp (d := d) s a β ha m
  obtain ⟨Rg, ν₀, hRg⟩ := s104e_regime hd s a β hβ
  obtain ⟨χ, hχ⟩ := HRS.MS.Fcau.fcau_exists_cutoff (d := d)
  set D := quadraticGradientDyn d s a β with hD
  set MB : ℝ := ∑ i, ∑ j, |D.M i j| with hMB
  have hdata : AdjointRdData s m MB Λ ΛV G₀ β⁻¹ D t ρ :=
    ⟨⟨rfl, hs0, hsd⟩, HRS.MS.Go.s55f_matBound _, hV, hΛ, hpos, ⟨(inv_pos.2 hβ).le, le_rfl⟩⟩
  -- the datum
  obtain ⟨Kφ, hKφ0, hKφ⟩ := s103c_phi_syn3 (d := d) (10 * d + 100) le_rfl
  set φ : Euc d → ℝ := oscTestFun ((24 * d + 240 : ℕ) : ℝ) α with hφdef
  have hφ' : oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α = φ := rfl
  rw [hφ']
  have hφS := hKφ α
  have hφ2 : ContDiff ℝ 2 φ := hφS.1.of_le (by exact_mod_cast (by omega : 2 ≤ 10 * d + 100))
  have hφcb : HRS.MemCb m φ :=
    ⟨hφS.1.of_le (by exact_mod_cast (by rw [hm]; unfold HRS.Whole.mStar; omega : m ≤ 10 * d + 100)),
      fun j hj => ⟨Kφ * s103_b d α, by
        rintro _ ⟨x, rfl⟩
        exact hφS.bd.2 j (by rw [hm] at hj; unfold HRS.Whole.mStar at hj; omega) x⟩⟩
  obtain ⟨Cu, hCu0, hCu⟩ := HRS.MS.Ul.ulocNormE_le_cb m χ hχ
  have hfin : ulocNormE m χ φ < ⊤ := lt_of_le_of_lt (hCu φ hφcb) ENNReal.ofReal_lt_top
  obtain ⟨C1, hC1, hex⟩ := h12 hd1 s hs0 hsd m hm1 Rg MB Λ ΛV G₀ β⁻¹ t χ hχ
  obtain ⟨⟨F, hF, -⟩, -⟩ := hex D ν₀ ρ hdata hRg t ⟨hpos, le_rfl⟩ φ hfin
  obtain ⟨C2, hC2, hcl⟩ := h12c hd1 s hs0 hsd Rg MB Λ ΛV G₀ β⁻¹ t χ hχ
  obtain ⟨⟨f, hf, -⟩, -⟩ := hcl m le_rfl D ν₀ ρ hdata hRg t ⟨hpos, le_rfl⟩ φ hφ2 hfin F hF
  exact ⟨f, hf⟩

end HRS.MS.S104e

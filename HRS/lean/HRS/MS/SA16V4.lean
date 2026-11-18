import HRS.MS.SA16V3
import HRS.MS.AdjRdUniqueness
import HRS.MS.StarTie
import HRS.MS.UlNormAux1

/-!
# S.A.16 A2: `bounded_lp_uniqueness_bridge`

Two weak solutions with the same datum and bounded `W^{m,p}` norms coincide: the difference is a zero-datum weak
solution which is bounded in `H^1_uloc` (`sa16v_uloc_of_wmp`), hence an S.A.33 distributional solution
(`sa12_zero_forward_dist`), and `uloc_uniqueness_star` applies in the three cases (`sub`: R1; `iso`, `hilbert`: the
corner regime `UlocStarRegime`, valid for every `p`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16Assembly
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas Phase2SA16 Phase2SA16V Phase2SA16Evolution

/-- a lift of norm below `B + 1` -/
lemma sa16v_exists_lift_norm {d : ℕ} (m : ℕ) (p : ℝ) [Fact (2 ≤ p)] {u : Euc d → ℝ} {B : ℝ}
    (hu : wNormE m p u ≤ ENNReal.ofReal B) :
    ∃ G : WmpSpace d m p, wrep d m p G =ᵐ[volume] u ∧ ‖G‖ ≤ max B 0 + 1 := by
  have hlt : wNormE m p u < ENNReal.ofReal (max B 0 + 1) :=
    lt_of_le_of_lt hu ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by
      have := le_max_left B 0; linarith))
  unfold wNormE at hlt
  rw [iInf_lt_iff] at hlt
  obtain ⟨G, hG⟩ := hlt
  rw [iInf_lt_iff] at hG
  obtain ⟨h, hn⟩ := hG
  refine ⟨G, h, ?_⟩
  exact ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).1 hn).le

theorem bounded_lp_uniqueness_bridge (d : ℕ) (hd : 1 ≤ d) (s : ℝ)
    (hs0 : 0 ≤ s) (hsd : s<d) (m : ℕ) (hm : 1 ≤ m) (p : ℝ) [Fact (2 ≤ p)]
    (κc : LpCase) (MB Λ ΛV G₀ νbar T : ℝ) (D : WholeDyn d) (μ : ℝ → Euc d → ℝ)
    (hD : AdjointRdData s m MB Λ ΛV G₀ νbar D T μ) (hκ : κc.Holds d s p D.M)
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) T) (φ : Euc d → ℝ)
    (F₁ F₂ : ℝ → Euc d → ℝ)
    (h₁ : IsForwardSolutionRd (D.coeff μ) t φ F₁)
    (h₂ : IsForwardSolutionRd (D.coeff μ) t φ F₂)
    (hB₁ : ∃ B : ℝ, ∀ τ ∈ Icc (0 : ℝ) t, wNormE m p (F₁ τ) ≤ ENNReal.ofReal B)
    (hB₂ : ∃ B : ℝ, ∀ τ ∈ Icc (0 : ℝ) t, wNormE m p (F₂ τ) ≤ ENNReal.ofReal B) :
    ∀ τ ∈ Icc (0 : ℝ) t, F₁ τ =ᵐ[volume] F₂ τ := by
  obtain ⟨hDs, -, -⟩ := hD.hs
  obtain ⟨χ, hχ⟩ := HRS.MS.Ul.ul0_exists_ulocCutoff d
  obtain ⟨K, hK0, hK⟩ := sa16v_uloc_of_wmp hd m hm p hχ
  -- `H¹_uloc` bounds
  have hbd : ∀ F : ℝ → Euc d → ℝ, (∃ B : ℝ, ∀ τ ∈ Icc (0 : ℝ) t, wNormE m p (F τ) ≤ ENNReal.ofReal B) →
      ∃ B' : ℝ, 0 ≤ B' ∧ ∀ τ ∈ Icc (0 : ℝ) t, ulocNormE 1 χ (F τ) ≤ ENNReal.ofReal B' := by
    intro F ⟨B, hB⟩
    refine ⟨K * (max B 0 + 2), by positivity, fun τ hτ => ?_⟩
    obtain ⟨G, hG, hGn⟩ := sa16v_exists_lift_norm m p (hB τ hτ)
    refine (hK G (F τ) hG).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_left (by linarith) hK0
  obtain ⟨B₁', hB₁'0, hb₁⟩ := hbd F₁ hB₁
  obtain ⟨B₂', hB₂'0, hb₂⟩ := hbd F₂ hB₂
  have hb : IsUlBounded χ 1 t (fun τ x => F₁ τ x - F₂ τ x) := by
    refine ⟨B₁' + B₂', fun τ hτ => ?_⟩
    calc ulocNormE 1 χ (fun x => F₁ τ x - F₂ τ x)
        ≤ ulocNormE 1 χ (F₁ τ) + ulocNormE 1 χ (F₂ τ) := HRS.MS.SA12BD.sa12_uloc_sub d 1 χ _ _
      _ ≤ ENNReal.ofReal B₁' + ENNReal.ofReal B₂' := add_le_add (hb₁ τ hτ) (hb₂ τ hτ)
      _ = ENNReal.ofReal (B₁' + B₂') := (ENNReal.ofReal_add hB₁'0 hB₂'0).symm
  have hsub := HRS.MS.SA12BD.sa12_forward_sub d (D.coeff μ) t φ F₁ F₂ h₁ h₂
  have hz := HRS.MS.SA12BD.sa12_zero_forward_dist d hd s hs0 hsd m hm MB Λ ΛV G₀ νbar T χ hχ D μ hD t ht
    (fun τ x => F₁ τ x - F₂ τ x) hsub hb
  have htT : t ∈ Icc (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
  have hDeq : D = (⟨s, D.M, D.V, D.invβ⟩ : WholeDyn d) := by
    cases D; simp_all
  -- the regime
  have hRg : RdRegimeHolds PDE.Regime.R1 d s D.M D.invβ 0 ∨ HRS.MS.Star.UlocStarRegime d s D.M := by
    cases κc with
    | sub => exact Or.inl hκ.1
    | iso =>
      obtain ⟨hs, lam, hlam, hM⟩ := hκ
      exact Or.inr ⟨hs, HRS.MS.Star.star_matrix_symNonpos_of_lam hlam.le (A := 0) (by simp) (by simpa using hM)⟩
    | hilbert =>
      obtain ⟨hs, -, lam, hlam, A, hA, hM⟩ := hκ
      exact Or.inr ⟨hs, HRS.MS.Star.star_matrix_symNonpos_of_lam hlam hA hM⟩
  have key := HRS.MS.Star.uloc_uniqueness_star hd s hs0 hsd m hm PDE.Regime.R1 T Λ ΛV G₀ MB νbar 0 χ hχ
    D.M D.V D.invβ μ hD.hM hD.hV hD.hν hD.hμ hRg t htT (fun τ x => F₁ τ x - F₂ τ x) hb
    (by rw [← hDeq]; exact hz)
  intro τ hτ
  filter_upwards [key τ hτ] with x hx
  simpa [sub_eq_zero] using hx

end HRS.Whole.AppendixA.Phase2SA16Assembly

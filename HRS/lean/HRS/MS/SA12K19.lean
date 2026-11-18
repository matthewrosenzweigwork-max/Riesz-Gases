import HRS.MS.SA12K18
import HRS.MS.SA12K15

/-!
# S.A.12 L8: the local (drift) terms

Differentiability of the limit drift from `PerApprox`, the bound of `movDiv (ψ • b)`, and its pointwise decay and
convergence.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Limit

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
open HRS.MH.AdjointRd.Phase2SA12Construction HRS.MS.ToriConv

variable {d : ℕ}

theorem sa12k_norm_one_sub (f g : Euc d → Euc d) (x : Euc d) :
    ‖iteratedFDeriv ℝ 1 f x - iteratedFDeriv ℝ 1 g x‖ = ‖fderiv ℝ f x - fderiv ℝ g x‖ := by
  have h1 := tcv_iter_fderiv_sub_norm f g 0 x
  have h2 := tcv_iter_zero_sub_norm (fderiv ℝ f) (fderiv ℝ g) x
  rw [zero_add] at h1
  rw [← h1, h2]

/-- The limit drift is differentiable (a locally uniform limit of `C^1` drifts with convergent derivatives). -/
theorem sa12k_limit_drift_diff {s : ℝ} {m : ℕ} {MB Λ' ΛV' νbar Cb T : ℝ} {D : WholeDyn d}
    {μ : ℝ → Euc d → ℝ} {γ : ℝ → Euc d → ℝ} {t L₀ : ℝ} {μL : ℝ → ℝ → ℝ → Euc d → ℝ}
    {VL : ℝ → ℝ → Euc d → ℝ} (hA : PerApprox s m MB Λ' ΛV' νbar Cb T D μ γ t L₀ μL VL)
    (hm : 1 ≤ m) (ht : t ∈ Ioc (0 : ℝ) T) {σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) t) :
    Differentiable ℝ ((D.coeff μ).drift (t - σ)) := by
  have hσT : σ ∈ Icc (0 : ℝ) T := ⟨hσ.1, hσ.2.trans ht.2⟩
  have hmax : max (t - σ) 0 = t - σ := max_eq_left (by linarith [hσ.2])
  set f : ℝ → Euc d → Euc d := fun L => torusDriftL D.M L (γ L) (μL L (sa12k_rad L) σ)
    (VL L (sa12k_rad L)) with hf
  set b : Euc d → Euc d := (D.coeff μ).drift (t - σ) with hb
  have hε : ∀ L : ℝ, sa12k_rad L ∈ Ioc (0 : ℝ) 1 := fun L => ⟨sa12k_rad_pos L, sa12k_rad_le_one L⟩
  have hdiff : ∀ L : ℝ, max 1 L₀ ≤ L → Differentiable ℝ (f L) := by
    intro L hL
    have h0 := (hA.1 L hL (sa12k_rad L) (hε L)).b_drift.smooth σ hσT
    have h1 : ContDiff ℝ 1 (f L) := h0.of_le (by exact_mod_cast (by omega : 1 ≤ m + 1))
    exact h1.differentiable one_ne_zero
  have hconv := hA.2
  -- uniform convergence of values and of derivatives
  have hconv' : ∀ K : Set (Euc d), IsCompact K → ∀ j ≤ m + 1, ∀ ε : ℝ, 0 < ε → ∃ L₀' : ℝ,
      ∀ L : ℝ, L₀' ≤ L → ∀ x ∈ K,
        ‖iteratedFDeriv ℝ j (f L) x - iteratedFDeriv ℝ j b x‖ ≤ ε := by
    intro K hK j hj ε hε
    obtain ⟨L₁, ε₀, hε₀, h⟩ := hconv K hK j hj ε hε
    refine ⟨max (max L₁ 1) (1 / ε₀), fun L hL x hx => ?_⟩
    have hL1 : 1 ≤ L := (le_max_right L₁ 1).trans ((le_max_left _ _).trans hL)
    have hL2 : L₁ ≤ L := (le_max_left L₁ 1).trans ((le_max_left _ _).trans hL)
    have hL3 : 1 / ε₀ ≤ L := (le_max_right _ _).trans hL
    have hrad : sa12k_rad L ≤ ε₀ := by
      refine (sa12k_rad_le_inv hL1).trans ?_
      rw [div_le_iff₀ (by linarith : 0 < L)]
      rw [div_le_iff₀ hε₀] at hL3
      linarith
    have := (h L hL2 (sa12k_rad L) (sa12k_rad_pos L) hrad σ hσT x hx).1
    rw [hmax] at this
    exact this
  have hc0 : ∀ K : Set (Euc d), IsCompact K → ∀ ε : ℝ, 0 < ε → ∃ L₀' : ℝ, ∀ L : ℝ, L₀' ≤ L →
      ∀ x ∈ K, ‖f L x - b x‖ ≤ ε := by
    intro K hK ε hε
    obtain ⟨L', h⟩ := hconv' K hK 0 (by omega) ε hε
    exact ⟨L', fun L hL x hx => by
      have := h L hL x hx
      rwa [tcv_iter_zero_sub_norm] at this⟩
  have hc1 : ∀ K : Set (Euc d), IsCompact K → ∀ ε : ℝ, 0 < ε → ∃ L₀' : ℝ, ∀ L : ℝ, L₀' ≤ L →
      ∀ x ∈ K, ‖fderiv ℝ (f L) x - fderiv ℝ b x‖ ≤ ε := by
    intro K hK ε hε
    obtain ⟨L', h⟩ := hconv' K hK 1 (by omega) ε hε
    exact ⟨L', fun L hL x hx => by
      have := h L hL x hx
      rwa [sa12k_norm_one_sub] at this⟩
  intro x
  have hderiv : HasFDerivAt b (fderiv ℝ b x) x := by
    refine hasFDerivAt_of_tendstoUniformlyOnFilter (l := atTop) (f := f)
      (f' := fun L => fderiv ℝ (f L)) (g := b) (g' := fderiv ℝ b) (x := x) ?_ ?_ ?_
    · exact tendstoLocallyUniformly_iff_filter.1 (tcv_tlu (fun L => fderiv ℝ (f L)) (fderiv ℝ b) hc1) x
    · have h1 : ∀ᶠ n : ℝ × Euc d in atTop ×ˢ 𝓝 x, max 1 L₀ ≤ n.1 :=
        (eventually_ge_atTop (max 1 L₀)).prod_inl _
      exact h1.mono fun n hn => ((hdiff n.1 hn) n.2).hasFDerivAt
    · exact Filter.Eventually.of_forall fun y => tcv_pt_tendsto f b hc0 y
  exact hderiv.differentiableAt

end HRS.MH.AdjointRd.Phase2SA12Limit

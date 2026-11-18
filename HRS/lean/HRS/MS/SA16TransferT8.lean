import HRS.MS.SA16StrongSL6
import HRS.MS.SA16EvolDefs

/-!
# S.A.16 T8: `jet_restriction_and_finite_lift`

Restricting the jet index from order `k` to order `m ≤ k` is a contraction of the ambient `L^p` spaces,
maps compact smooth `k`-jets to the corresponding `m`-jets, hence maps `WmpSpace d k p` into
`WmpSpace d m p` with unchanged zeroth component; a finite `wNormE` is attained by a (unique, SL4) lift.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16Transfer
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution

/-- the index inclusion `WIndex d m → WIndex d k` -/
def sa16t_incl (d m k : ℕ) (hmk : m ≤ k) (τ : WIndex d m) : WIndex d k :=
  ⟨Fin.castLE (by omega) τ.1, τ.2⟩

/-- coordinate restriction of the finite factor -/
def sa16t_restr (d m k : ℕ) (hmk : m ≤ k) :
    (WIndex d k → ℝ) →L[ℝ] (WIndex d m → ℝ) :=
  ContinuousLinearMap.pi fun τ => ContinuousLinearMap.proj (sa16t_incl d m k hmk τ)

lemma sa16t_restr_apply (d m k : ℕ) (hmk : m ≤ k) (v : WIndex d k → ℝ) (τ : WIndex d m) :
    sa16t_restr d m k hmk v τ = v (sa16t_incl d m k hmk τ) := rfl

lemma sa16t_restr_norm (d m k : ℕ) (hmk : m ≤ k) : ‖sa16t_restr d m k hmk‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  rw [one_mul]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg v)).2 fun τ => ?_
  exact norm_le_pi_norm v (sa16t_incl d m k hmk τ)

lemma sa16t_restr_wJet (d m k : ℕ) (hmk : m ≤ k) (φ : Euc d → ℝ) (x : Euc d) :
    sa16t_restr d m k hmk (wJet k φ x) = wJet m φ x := rfl

lemma sa16t_incl_wZero (d m k : ℕ) (hmk : m ≤ k) : sa16t_incl d m k hmk (wZero d m) = wZero d k :=
  rfl

theorem jet_restriction_and_finite_lift (d m k : ℕ) (hmk : m ≤ k) (p : ℝ) [Fact (2 ≤ p)] :
    (∃ R : WmpSpace d k p →L[ℝ] WmpSpace d m p, ‖R‖ ≤ 1 ∧
      ∀ G, wrep d m p (R G) =ᵐ[volume] wrep d k p G) ∧
    ∀ φ : Euc d → ℝ, wNormE m p φ<⊤ →
      ∃ G : WmpSpace d m p, wrep d m p G =ᵐ[volume] φ ∧
        wNormE m p φ=ENNReal.ofReal ‖G‖ := by
  refine ⟨?_, fun φ hφ => ?_⟩
  · set L := sa16t_restr d m k hmk with hL
    set Φ : WLp d k p →L[ℝ] WLp d m p := L.compLpL (ENNReal.ofReal p) (volume : Measure (Euc d))
      with hΦ
    have hΦfn : ∀ F : WLp d k p, ((Φ F : WLp d m p) : Euc d → (WIndex d m → ℝ)) =ᵐ[volume]
        fun x => L ((F : Euc d → (WIndex d k → ℝ)) x) := fun F => L.coeFn_compLp F
    have hmap : ∀ G : WmpSpace d k p, Φ (G : WLp d k p) ∈ WmpSpace d m p := by
      have hS0 : ∀ F : WLp d k p, (∃ φ : Euc d → ℝ, IsCcInfty φ ∧
          (F : Euc d → (WIndex d k → ℝ)) =ᵐ[volume] wJet k φ) →
          Φ F ∈ (Submodule.span ℝ {F : WLp d m p | ∃ φ : Euc d → ℝ, IsCcInfty φ ∧
            (F : Euc d → (WIndex d m → ℝ)) =ᵐ[volume] wJet m φ}).topologicalClosure := by
        rintro F ⟨φ, hφ, hF⟩
        refine Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨φ, hφ, ?_⟩)
        filter_upwards [hΦfn F, hF] with x hx1 hx2
        rw [hx1, hx2]
        rfl
      have hle : Submodule.span ℝ {F : WLp d k p | ∃ φ : Euc d → ℝ, IsCcInfty φ ∧
          (F : Euc d → (WIndex d k → ℝ)) =ᵐ[volume] wJet k φ} ≤
          (Submodule.topologicalClosure (Submodule.span ℝ {F : WLp d m p | ∃ φ : Euc d → ℝ,
            IsCcInfty φ ∧ (F : Euc d → (WIndex d m → ℝ)) =ᵐ[volume] wJet m φ})).comap
              (Φ : WLp d k p →ₗ[ℝ] WLp d m p) := by
        rw [Submodule.span_le]
        intro F hF
        exact hS0 F hF
      have hcl : IsClosed (((Submodule.topologicalClosure (Submodule.span ℝ {F : WLp d m p |
          ∃ φ : Euc d → ℝ, IsCcInfty φ ∧
            (F : Euc d → (WIndex d m → ℝ)) =ᵐ[volume] wJet m φ})).comap
              (Φ : WLp d k p →ₗ[ℝ] WLp d m p) : Submodule ℝ (WLp d k p)) : Set (WLp d k p)) :=
        (Submodule.isClosed_topologicalClosure _).preimage Φ.continuous
      intro G
      exact Submodule.topologicalClosure_minimal _ hle hcl G.2
    refine ⟨(Φ.comp (WmpSpace d k p).subtypeL).codRestrict (WmpSpace d m p) hmap, ?_, ?_⟩
    · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun G => ?_
      rw [one_mul]
      show ‖L.compLp (G : WLp d k p)‖ ≤ ‖G‖
      calc ‖L.compLp (G : WLp d k p)‖ ≤ ‖L‖ * ‖(G : WLp d k p)‖ := ContinuousLinearMap.norm_compLp_le L _
        _ ≤ 1 * ‖G‖ := mul_le_mul_of_nonneg_right (sa16t_restr_norm d m k hmk) (norm_nonneg _)
        _ = ‖G‖ := one_mul _
    · intro G
      filter_upwards [hΦfn (G : WLp d k p)] with x hx
      show ((Φ (G : WLp d k p) : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m) =
        ((G : WLp d k p) : Euc d → (WIndex d k → ℝ)) x (wZero d k)
      rw [hx]
      rfl
  · by_contra hcon
    have hno : ∀ G : WmpSpace d m p, ¬ (∀ᵐ x ∂(volume : Measure (Euc d)),
        ((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m) = φ x) := by
      intro G hG
      exact hcon ⟨G, hG, wNormE_eq_lift_norm d m p G φ hG⟩
    have : wNormE m p φ = ⊤ := by
      unfold wNormE
      exact iInf_eq_top.2 fun G => iInf_eq_top.2 fun hG => (hno G hG).elim
    exact absurd hφ (by rw [this]; exact lt_irrefl _)

end HRS.Whole.AppendixA.Phase2SA16Transfer

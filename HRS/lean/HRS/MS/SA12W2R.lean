import HRS.MS.SA12W2Q
import HRS.PDE.MeanFieldVelocityTools

/-!
# S.A.12 C5 (SA12W2 worker), part R: jets-continuity versus `C^m`-norm continuity of torus families

For a family `w : ℝ → Torus d → ℝ` smooth on `[0,t]`:
* `sa12w2_JC_to_CC`: joint continuity of all jets of `lift (w τ)` on `[0,t] × ℝ^d` gives `cbNorm m (w τ - w τ₀) → 0`
  (compactness of `[0,t] × [0,1]^d` and periodicity);
* `sa12w2_CC_to_JC`: conversely.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ComplexConjugate ContDiff

namespace HRS.PDE.SA12W2

variable {d : ℕ}

/-- All jets of the lifts are jointly continuous on `[0,t] × ℝ^d`. -/
def sa12w2_JC (t : ℝ) (w : ℝ → Torus d → ℝ) : Prop :=
  (∀ τ ∈ Icc (0 : ℝ) t, ContDiff ℝ ∞ (Torus.lift (w τ))) ∧
    ∀ j : ℕ, ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ j (Torus.lift (w p.1)) p.2)
      (Icc (0 : ℝ) t ×ˢ univ)

/-- `C^m`-norm continuity on `[0,t]`. -/
def sa12w2_CC (t : ℝ) (w : ℝ → Torus d → ℝ) : Prop :=
  (∀ τ ∈ Icc (0 : ℝ) t, ContDiff ℝ ∞ (Torus.lift (w τ))) ∧
    ∀ τ₀ ∈ Icc (0 : ℝ) t, ∀ m : ℕ, Tendsto (fun τ => Torus.cbNorm m (fun x => w τ x - w τ₀ x))
      (𝓝[Icc (0 : ℝ) t] τ₀) (𝓝 0)

theorem sa12w2_JC_to_CC {t : ℝ} {w : ℝ → Torus d → ℝ} (hw : sa12w2_JC t w) : sa12w2_CC t w := by
  refine ⟨hw.1, fun τ₀ hτ₀ m => ?_⟩
  unfold Torus.cbNorm
  suffices key : ∀ j ∈ Finset.range (m + 1), Tendsto (fun τ => ⨆ x : Euc d,
      ‖iteratedFDeriv ℝ j (Torus.lift (fun x => w τ x - w τ₀ x)) x‖) (𝓝[Icc (0 : ℝ) t] τ₀) (𝓝 0) by
    simpa using tendsto_finsetSum _ key
  intro j hj
  have hK : IsCompact (Icc (0 : ℝ) t ×ˢ {x : Euc d | ∀ i, x i ∈ Icc (0 : ℝ) 1}) :=
    isCompact_Icc.prod (HRS.MS.ToriCoefB.tcb_compact_Icc 0 1)
  have hucont := hK.uniformContinuousOn_of_continuous
    ((hw.2 j).mono (prod_mono subset_rfl (subset_univ _)))
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  rw [Metric.uniformContinuousOn_iff] at hucont
  obtain ⟨δ, hδ, hδ'⟩ := hucont (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, fun τ hτ hdist => ?_⟩
  have hsm : ∀ σ ∈ Icc (0 : ℝ) t, ContDiff ℝ (j : WithTop ℕ∞) (Torus.lift (w σ)) := fun σ hσ =>
    (hw.1 σ hσ).of_le (by exact_mod_cast le_top)
  have hbound : ∀ x : Euc d, ‖iteratedFDeriv ℝ j (Torus.lift (fun x => w τ x - w τ₀ x)) x‖ ≤ ε / 2 := by
    intro x
    obtain ⟨k, hk⟩ := HRS.KernelAux.rep_mk_eq x
    set x' : Euc d := Torus.rep (Torus.mk x) with hx'
    have hx'mem : x' ∈ {x : Euc d | ∀ i, x i ∈ Icc (0 : ℝ) 1} := by
      intro i
      have := (AddCircle.equivIco (1 : ℝ) 0 ((Torus.mk x) i)).2
      simp only [zero_add] at this
      exact ⟨this.1, this.2.le⟩
    have e1 : ∀ σ : ℝ, iteratedFDeriv ℝ j (Torus.lift (w σ)) x = iteratedFDeriv ℝ j (Torus.lift (w σ)) x' := by
      intro σ
      rw [hk, HRS.KernelGrad.iteratedFDeriv_lift_add]
    have hlift : Torus.lift (fun x => w τ x - w τ₀ x) =
        Torus.lift (w τ) - Torus.lift (w τ₀) := rfl
    rw [hlift, iteratedFDeriv_sub_apply (hsm τ hτ).contDiffAt (hsm τ₀ hτ₀).contDiffAt, e1, e1 τ₀]
    have := hδ' (τ, x') ⟨hτ, hx'mem⟩ (τ₀, x') ⟨hτ₀, hx'mem⟩ (by
      rw [Prod.dist_eq]; simpa using hdist)
    rw [dist_eq_norm] at this
    exact this.le
  have hnn : 0 ≤ ⨆ x : Euc d, ‖iteratedFDeriv ℝ j (Torus.lift (fun x => w τ x - w τ₀ x)) x‖ :=
    Real.iSup_nonneg fun _ => norm_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  exact lt_of_le_of_lt (ciSup_le hbound) (half_lt_self hε)

theorem sa12w2_CC_to_JC {t : ℝ} {w : ℝ → Torus d → ℝ} (hw : sa12w2_CC t w) : sa12w2_JC t w := by
  refine ⟨hw.1, fun j => ?_⟩
  intro p hp
  obtain ⟨τ₀, y₀⟩ := p
  have hτ₀ : τ₀ ∈ Icc (0 : ℝ) t := hp.1
  have hsm : ∀ σ ∈ Icc (0 : ℝ) t, ContDiff ℝ (j : WithTop ℕ∞) (Torus.lift (w σ)) := fun σ hσ =>
    (hw.1 σ hσ).of_le (by exact_mod_cast le_top)
  rw [ContinuousWithinAt, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hc : ContinuousAt (fun y => iteratedFDeriv ℝ j (Torus.lift (w τ₀)) y) y₀ :=
    ((hsm τ₀ hτ₀).continuous_iteratedFDeriv le_rfl).continuousAt
  obtain ⟨δ₁, hδ₁, h1⟩ := Metric.continuousAt_iff.1 hc (ε / 2) (half_pos hε)
  have hcb := (hw.2 τ₀ hτ₀ j)
  rw [Metric.tendsto_nhdsWithin_nhds] at hcb
  obtain ⟨δ₂, hδ₂, h2⟩ := hcb (ε / 2) (half_pos hε)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun q hq hdq => ?_⟩
  obtain ⟨τ, y⟩ := q
  have hτ : τ ∈ Icc (0 : ℝ) t := hq.1
  rw [Prod.dist_eq] at hdq
  have hd1 : dist y y₀ < δ₁ := lt_of_le_of_lt (le_max_right _ _) (hdq.trans_le (min_le_left _ _))
  have hd2 : dist τ τ₀ < δ₂ := lt_of_le_of_lt (le_max_left _ _) (hdq.trans_le (min_le_right _ _))
  have hτ2 := h2 hτ hd2
  rw [Real.dist_eq, sub_zero] at hτ2
  have hnorm : ‖iteratedFDeriv ℝ j (Torus.lift (fun x => w τ x - w τ₀ x)) y‖ ≤
      Torus.cbNorm j (fun x => w τ x - w τ₀ x) := by
    refine HRS.PDE.norm_iteratedFDeriv_le_cbNorm j j le_rfl _ ?_ y
    exact (hsm τ hτ).sub (hsm τ₀ hτ₀)
  have hlift : Torus.lift (fun x => w τ x - w τ₀ x) = Torus.lift (w τ) - Torus.lift (w τ₀) := rfl
  rw [hlift, iteratedFDeriv_sub_apply (hsm τ hτ).contDiffAt (hsm τ₀ hτ₀).contDiffAt] at hnorm
  have h3 := h1 hd1
  rw [dist_eq_norm] at h3 ⊢
  calc ‖iteratedFDeriv ℝ j (Torus.lift (w τ)) y - iteratedFDeriv ℝ j (Torus.lift (w τ₀)) y₀‖
      = ‖(iteratedFDeriv ℝ j (Torus.lift (w τ)) y - iteratedFDeriv ℝ j (Torus.lift (w τ₀)) y) +
          (iteratedFDeriv ℝ j (Torus.lift (w τ₀)) y - iteratedFDeriv ℝ j (Torus.lift (w τ₀)) y₀)‖ := by
        congr 1; abel
    _ ≤ ‖iteratedFDeriv ℝ j (Torus.lift (w τ)) y - iteratedFDeriv ℝ j (Torus.lift (w τ₀)) y‖ +
          ‖iteratedFDeriv ℝ j (Torus.lift (w τ₀)) y - iteratedFDeriv ℝ j (Torus.lift (w τ₀)) y₀‖ :=
        norm_add_le _ _
    _ < ε := by
        have hn0 : 0 ≤ Torus.cbNorm j (fun x => w τ x - w τ₀ x) := by
          unfold Torus.cbNorm
          exact Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _
        rw [abs_of_nonneg hn0] at hτ2
        linarith

end HRS.PDE.SA12W2

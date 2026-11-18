import HRS.MS.SA16StrongDefs

/-!
# S.A.16 SL5: `wmp_smooth_dense`

The compact smooth jets already form an additive real subspace of `L^p`, so their span is itself and
its closure is `WmpSpace` by definition; hence the set of exact compact smooth jets is dense in `WmpSpace`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16
open HRS HRS.Whole HRS.Whole.AppendixA

lemma sa16s_partialDeriv_add {d : ℕ} {f g : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {j : ℕ} (idx : Fin j → Fin d) (x : Euc d) :
    partialDeriv idx (f + g) x = partialDeriv idx f x + partialDeriv idx g x := by
  unfold partialDeriv
  have hf' : ContDiffAt ℝ j f x := (hf.of_le (by exact_mod_cast le_top)).contDiffAt
  have hg' : ContDiffAt ℝ j g x := (hg.of_le (by exact_mod_cast le_top)).contDiffAt
  rw [iteratedFDeriv_add_apply hf' hg']
  rfl

lemma sa16s_partialDeriv_smul {d : ℕ} {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (c : ℝ)
    {j : ℕ} (idx : Fin j → Fin d) (x : Euc d) :
    partialDeriv idx (c • f) x = c * partialDeriv idx f x := by
  unfold partialDeriv
  have hf' : ContDiffAt ℝ j f x := (hf.of_le (by exact_mod_cast le_top)).contDiffAt
  rw [iteratedFDeriv_const_smul_apply hf']
  rfl

lemma sa16s_partialDeriv_zero {d : ℕ} {j : ℕ} (idx : Fin j → Fin d) (x : Euc d) :
    partialDeriv idx (0 : Euc d → ℝ) x = 0 := by
  unfold partialDeriv
  have : iteratedFDeriv ℝ j (0 : Euc d → ℝ) x = 0 := by
    have := iteratedFDeriv_zero_fun (𝕜 := ℝ) (E := Euc d) (F := ℝ) (n := j)
    exact congrFun this x
  rw [this]
  rfl

theorem wmp_smooth_dense (d m : ℕ) (p : ℝ) [Fact (2 ≤ p)] :
    Dense {G : WmpSpace d m p | ∃ u : Euc d → ℝ, IsCcInfty u ∧
      ((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) =ᵐ[volume] wJet m u} := by
  set S0 : Set (WLp d m p) := {F : WLp d m p | ∃ φ : Euc d → ℝ, IsCcInfty φ ∧
    (F : Euc d → (WIndex d m → ℝ)) =ᵐ[volume] wJet m φ} with hS0
  have hspan : ∀ F ∈ Submodule.span ℝ S0, F ∈ S0 := by
    intro F hF
    refine Submodule.span_induction (p := fun F _ => F ∈ S0) (fun F hF => hF) ?_ ?_ ?_ hF
    · refine ⟨0, ⟨contDiff_const, HasCompactSupport.zero⟩, ?_⟩
      refine (Lp.coeFn_zero _ _ _).trans (Eventually.of_forall fun x => ?_)
      funext τ
      simp [wJet, sa16s_partialDeriv_zero]
    · rintro F₁ F₂ - - ⟨φ₁, h₁, e₁⟩ ⟨φ₂, h₂, e₂⟩
      refine ⟨φ₁ + φ₂, ⟨h₁.1.add h₂.1, h₁.2.add h₂.2⟩, ?_⟩
      filter_upwards [Lp.coeFn_add F₁ F₂, e₁, e₂] with x hx hx1 hx2
      rw [hx]
      funext τ
      simp only [Pi.add_apply, wJet]
      rw [sa16s_partialDeriv_add h₁.1 h₂.1]
      have a1 := congrFun hx1 τ
      have a2 := congrFun hx2 τ
      simp only [wJet] at a1 a2
      rw [a1, a2]
    · rintro c F - ⟨φ, h, e⟩
      refine ⟨c • φ, ⟨h.1.const_smul c, h.2.smul_left⟩, ?_⟩
      filter_upwards [Lp.coeFn_smul c F, e] with x hx hx1
      rw [hx]
      funext τ
      simp only [Pi.smul_apply, wJet, smul_eq_mul]
      rw [sa16s_partialDeriv_smul h.1]
      have a1 := congrFun hx1 τ
      simp only [wJet] at a1
      rw [a1]
  rw [Topology.IsInducing.subtypeVal.dense_iff]
  intro G
  have hG : (G : WLp d m p) ∈ closure (Submodule.span ℝ S0 : Set (WLp d m p)) := by
    have := G.2
    unfold WmpSpace at this
    rw [← Submodule.topologicalClosure_coe]
    exact this
  have hsub : S0 ⊆ Subtype.val '' {G : WmpSpace d m p | ∃ u : Euc d → ℝ, IsCcInfty u ∧
      ((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) =ᵐ[volume] wJet m u} := by
    intro F hF
    have hmem : F ∈ WmpSpace d m p := by
      unfold WmpSpace
      exact Submodule.le_topologicalClosure _ (Submodule.subset_span hF)
    exact ⟨⟨F, hmem⟩, hF, rfl⟩
  exact closure_mono hsub (closure_mono (fun F hF => hspan F hF) hG)

end HRS.Whole.AppendixA.Phase2SA16

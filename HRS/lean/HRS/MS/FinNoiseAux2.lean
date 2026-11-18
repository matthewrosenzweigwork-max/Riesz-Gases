import HRS.MS.FinNoiseAux1
import HRS.MS.OrbFeatAux2

/-!
# S8.6 `finite_noise`, packet P1a (S86): time homogeneity of the classical adjoint propagator

For coefficients `C` whose generator does not depend on time (`generatorW C t = generatorW C 0`) and for which
classical adjoint solutions are unique on `[0,T]` (`S52bUniq C T`, proved for the critical model by
`HRS.MS.S85.s85_uniq`), `propagatorW C r t φ = propagatorW C 0 (t - r) φ` for `0 ≤ r ≤ t ≤ T`
whenever a classical adjoint solution with terminal time `t` and datum `φ` exists.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.FinNoise

open HRS.Whole HRS.MS.S52B

variable {d : ℕ}

/-- Shifting a classical adjoint solution in time (time-independent generator). -/
theorem s86_shift (C : WholeCoeff d) (hgen : ∀ t φ, generatorW C t φ = generatorW C 0 φ)
    (t r : ℝ) (hr0 : 0 ≤ r) (hrt : r ≤ t) (φ : Euc d → ℝ) (f : ℝ → Euc d → ℝ)
    (hf : IsClassicalAdjointW C t φ f) :
    IsClassicalAdjointW C (t - r) φ (fun r' => f (r' + r)) := by
  have hmem : ∀ r' ∈ Icc (0 : ℝ) (t - r), r' + r ∈ Icc (0 : ℝ) t := fun r' h =>
    ⟨by linarith [h.1], by linarith [h.2]⟩
  let sh : Icc (0 : ℝ) (t - r) → Icc (0 : ℝ) t := fun p => ⟨p.1 + r, hmem p.1 p.2⟩
  have hsh : Continuous sh := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_subtype_val.add continuous_const
  have hsh2 : Continuous fun p : Icc (0 : ℝ) (t - r) × Euc d => (sh p.1, p.2) :=
    (hsh.comp continuous_fst).prodMk continuous_snd
  exact
  { c2 := fun r' h => hf.c2 _ (hmem r' h)
    bdd := fun j hj => by
      obtain ⟨B, hB⟩ := hf.bdd j hj
      exact ⟨B, fun r' h x => hB _ (hmem r' h) x⟩
    cont_c2 := fun j hj => (hf.cont_c2 j hj).comp hsh2
    terminal := by
      have : t - r + r = t := by ring
      simp only [this]; exact hf.terminal
    time_deriv := fun x r' h => by
      have h1 := hf.time_deriv x (r' + r) ⟨by linarith [h.1], by linarith [h.2]⟩
      have h2 := h1.comp_add_const r' r
      rw [hgen (r' + r) (f (r' + r)), ← hgen r' (f (r' + r))] at h2
      exact h2
    cont_time_deriv := by
      have := (hf.cont_time_deriv).comp hsh2
      refine this.congr fun p => ?_
      simp only [Function.comp, sh]
      rw [hgen (p.1.1 + r) (f (p.1.1 + r)), ← hgen p.1.1 (f (p.1.1 + r))]
    bdd_time_deriv := by
      obtain ⟨B, hB⟩ := hf.bdd_time_deriv
      refine ⟨B, fun r' h x => ?_⟩
      have := hB (r' + r) (hmem r' h) x
      rw [hgen (r' + r) (f (r' + r))] at this
      rwa [hgen r' (f (r' + r))]
      }

/-- Homogeneity of the propagator. -/
theorem s86_prop_shift (C : WholeCoeff d) (hgen : ∀ t φ, generatorW C t φ = generatorW C 0 φ)
    (T : ℝ) (hU : S52bUniq C T) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (φ : Euc d → ℝ)
    (hex : ∃ f, IsClassicalAdjointW C t φ f) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) t) :
    propagatorW C r t φ = propagatorW C 0 (t - r) φ := by
  classical
  have hs := hex.choose_spec
  have h1 : propagatorW C r t φ = hex.choose r := by
    unfold propagatorW; rw [dif_pos hex]
  have hsol := s86_shift C hgen t r hr.1 hr.2 φ hex.choose hs
  have hex2 : ∃ f, IsClassicalAdjointW C (t - r) φ f := ⟨_, hsol⟩
  have h2 : propagatorW C 0 (t - r) φ = hex2.choose 0 := by
    unfold propagatorW; rw [dif_pos hex2]
  have ht2 : t - r ∈ Icc (0 : ℝ) T := ⟨by linarith [hr.2], by linarith [ht.2, hr.1]⟩
  have := hU (t - r) ht2 φ _ _ hsol hex2.choose_spec 0 ⟨le_rfl, by linarith [hr.2]⟩
  rw [h1, h2, ← this]
  simp

end HRS.MS.FinNoise

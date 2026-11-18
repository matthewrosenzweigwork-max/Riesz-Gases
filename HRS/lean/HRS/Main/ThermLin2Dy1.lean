import HRS.Main.ThermLinPlan2

/-!
# THERMLIN 2, packet `Dy`, part 1: time homogeneity of the frozen propagator (plan statement `tl2_frozen_shift`, Z2)

`U^β_{u,t} φ = U^β_{0,t-u} φ`: the classical adjoint solution for the constant path `ρβ` is shifted in time, and the
shifted function is again a classical adjoint solution (on `[0,t-u]`); uniqueness of classical solutions identifies it.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ThermLin.Plan2

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.T25P

variable {d : ℕ}

/-- Time shift of a classical adjoint solution along a constant coefficient path. -/
theorem tl2dy_shift_sol {D : DynData d} {ρβ : Torus d → ℝ} {t u : ℝ} (hu : 0 ≤ u) (hut : u < t)
    {φ : Torus d → ℝ} {f : ℝ → Torus d → ℝ}
    (hf : IsClassicalAdjointSolution D (fun _ => ρβ) t φ f) :
    IsClassicalAdjointSolution D (fun _ => ρβ) (t - u) φ (fun r => f (r + u)) := by
  have hmem : ∀ r ∈ Set.Icc (0 : ℝ) (t - u), r + u ∈ Set.Icc (0 : ℝ) t := fun r hr =>
    ⟨by linarith [hr.1], by linarith [hr.2]⟩
  let ι : Set.Icc (0 : ℝ) (t - u) → Set.Icc (0 : ℝ) t := fun r => ⟨r.1 + u, hmem r.1 r.2⟩
  have hι : Continuous ι :=
    Continuous.subtype_mk (continuous_subtype_val.add continuous_const) _
  refine ⟨fun r hr => hf.c2 _ (hmem r hr), fun j hj => ?_, ?_, fun x r hr => ?_, ?_⟩
  · have hc : Continuous (fun p : Set.Icc (0 : ℝ) (t - u) × Euc d => (ι p.1, p.2)) :=
      (hι.comp continuous_fst).prodMk continuous_snd
    have := (hf.cont_c2 j hj).comp hc
    exact this
  · show f (t - u + u) = φ
    rw [sub_add_cancel]; exact hf.terminal
  · have h1 := hf.time_deriv x (r + u) ⟨by linarith [hr.1], by linarith [hr.2]⟩
    exact HasDerivAt.comp_add_const r u h1
  · have hc : Continuous (fun p : Set.Icc (0 : ℝ) (t - u) × Torus d => (ι p.1, p.2)) :=
      (hι.comp continuous_fst).prodMk continuous_snd
    have := hf.cont_time_deriv.comp hc
    exact this

/-- Time homogeneity of the frozen propagator for continuous data in `H^{m_*}` and `u < t`
(no smoothness needed). -/
theorem tl2dy_shift_gen (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) {φ : Torus d → ℝ} (hφc : Continuous φ)
    (hφS : MemSobolev (PDE.mStar d : ℝ) φ) {u t : ℝ} (hu : 0 ≤ u) (hlt : u < t) :
    tl2Ub S ρβ u t φ = tl2Ub S ρβ 0 (t - u) φ := by
  obtain ⟨hsm, hpos⟩ := HRS.ThermLin.thermlin_thermal_smooth_pos S h
  have hd1 : 1 ≤ d := by have := S.hd; omega
  have hprob : IsProbDensity ρβ := h.1
  have ht : 0 < t := lt_of_le_of_lt hu hlt
  have htu : 0 < t - u := sub_pos.2 hlt
  obtain ⟨R, MB, Λ, VB, hA⟩ :=
    PDE.MFSemigroup.adjointData_frozen S.s S.hs0 S.hsd S.β S.hβ S.V S.hV ρβ hprob hsm hpos (PDE.mStar d)
  obtain ⟨C, Cs, -, -, hmain⟩ :=
    PDE.adjoint_torus_classical hd1 S.s S.hs0 S.hsd (PDE.mStar d) le_rfl R MB Λ VB
  obtain ⟨hcls, hpe, -⟩ := hmain S.dyn 0 t (fun _ => ρβ) (hA 0 t ht) t ⟨ht, le_rfl⟩ φ hφc hφS
  have hsh := tl2dy_shift_sol (ρβ := ρβ) hu hlt hcls
  have hE : ∃ g, IsClassicalAdjointSolution S.dyn (fun _ => ρβ) (t - u) φ g := ⟨_, hsh⟩
  have htu' : t - u ∈ Set.Ioc (0 : ℝ) (t - u) := ⟨htu, le_rfl⟩
  show propagator S.dyn (fun _ => ρβ) u t φ = propagator S.dyn (fun _ => ρβ) 0 (t - u) φ
  rw [hpe u ⟨hu, hlt.le⟩]
  unfold propagator
  rw [dif_pos hE]
  have huniq := PDE.classical_adjoint_unique hd1 S.s S.hs0 S.hsd (PDE.mStar d)
    (by have := PDE.ClassicalPart.three_le_mStar d; omega) R MB Λ VB S.dyn 0 (t - u) (fun _ => ρβ)
    (hA 0 (t - u) htu) (t - u) htu' φ _ _ hE.choose_spec hsh 0 ⟨le_rfl, htu.le⟩
  rw [huniq]
  simp only [zero_add]

/-- (Z2) time homogeneity of the frozen propagator on smooth tests,
`U^β_{u,t} φ = U^β_{0,t-u} φ` for `0 ≤ u ≤ t`. -/
theorem tl2_frozen_shift_proof (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ)
    {u t : ℝ} (hu : 0 ≤ u) (hut : u ≤ t) :
    tl2Ub S ρβ u t φ = tl2Ub S ρβ 0 (t - u) φ := by
  obtain ⟨hsm, hpos⟩ := HRS.ThermLin.thermlin_thermal_smooth_pos S h
  have hd1 : 1 ≤ d := by have := S.hd; omega
  have hprob : IsProbDensity ρβ := h.1
  rcases hut.eq_or_lt with heq | hlt
  · subst heq
    have e1 := Uniform.Q48e.frozen_self_pos hd1 S.s S.hs0 S.hsd S.β S.hβ S.V S.hV ρβ hprob hsm hpos φ hφ u hu
    have e2 := Uniform.Q48e.frozen_self_pos hd1 S.s S.hs0 S.hsd S.β S.hβ S.V S.hV ρβ hprob hsm hpos φ hφ 0 le_rfl
    rw [sub_self]
    exact e1.trans e2.symm
  · exact tl2dy_shift_gen S h (PDE.MFAux.continuous_of_isCk (PDE.MFSemigroup.isCk_nat_of_isSmooth hφ 1))
      (PDE.MFSemigroup.memSobolev_of_isSmooth hφ _) hu hlt

example := (@tl2_frozen_shift_proof : type_of% @tl2_frozen_shift)

end HRS.ThermLin.Plan2

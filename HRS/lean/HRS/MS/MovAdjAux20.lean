import HRS.MS.MovAdjAux19

/-!
# S6.7 (packet P4, part 6): the classical adjoint solution as an `S67DuhData`

Namespace `HRS.MS.MovAdj`, helpers `s67_`.  Infrastructure for the supplement row `S:W:lem:r2mov-global-adjoint`; not a manuscript row.

Time is reversed and rescaled: `σ = (t - r)/β`, `u σ = f (t - β σ)`, `a σ = β · generatorW (f (t - β σ))`, and
`S σ = β · J (f (t - β σ))` where `J` is the nonlocal part.  Since `β · generatorW = kolmL (βq) B + β J`
(`s67_gen_eq`, `s67_drift_eq`), `S67DuhData (βq) B (t/β) u a S` holds.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovAdj

open HRS HRS.Whole HRS.MS.PoisKolm HRS.MS.Mov63

variable {d : ℕ}

/-- Reparametrisation of joint continuity from the subtype `Icc 0 t` to `σ ∈ [0, t/β]`. -/
theorem s67_reparam {t β : ℝ} (hβ : 0 < β) {E : Type*} [TopologicalSpace E] {G : ℝ → Euc d → E}
    (hc : Continuous fun p : Set.Icc (0 : ℝ) t × Euc d => G p.1 p.2) :
    ContinuousOn (fun p : ℝ × Euc d => G (t - β * p.1) p.2) (Icc (0 : ℝ) (t / β) ×ˢ univ) := by
  have hmem : ∀ σ ∈ Icc (0 : ℝ) (t / β), t - β * σ ∈ Icc (0 : ℝ) t := fun σ hσ => by
    constructor
    · have := (le_div_iff₀ hβ).1 hσ.2; linarith
    · have := mul_nonneg hβ.le hσ.1; linarith
  rw [continuousOn_iff_continuous_restrict]
  have h1 : Continuous fun p : ↥(Icc (0 : ℝ) (t / β) ×ˢ (univ : Set (Euc d))) =>
      ((⟨t - β * p.1.1, hmem _ p.2.1⟩ : Set.Icc (0 : ℝ) t), p.1.2) := by
    refine Continuous.prodMk (Continuous.subtype_mk ?_ _) ?_ <;> fun_prop
  exact hc.comp h1

section Classical

variable {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}

theorem s67_cont_iter_apply (hf : IsClassicalAdjointW C t φ f) {j : ℕ} (hj : j ≤ 2) (w : Fin j → Euc d) :
    Continuous fun p : Set.Icc (0 : ℝ) t × Euc d => iteratedFDeriv ℝ j (f p.1) p.2 w :=
  ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Euc d) ℝ w).continuous).comp (hf.cont_c2 j hj)

theorem s67_fderiv_eq_curry (g : Euc d → ℝ) (x : Euc d) :
    fderiv ℝ g x = continuousMultilinearCurryFin1 ℝ (Euc d) ℝ (iteratedFDeriv ℝ 1 g x) := by
  ext v
  simp [iteratedFDeriv_one_apply]

theorem s67_cont_fderiv (hf : IsClassicalAdjointW C t φ f) :
    Continuous fun p : Set.Icc (0 : ℝ) t × Euc d => fderiv ℝ (f p.1) p.2 := by
  have e : (fun p : Set.Icc (0 : ℝ) t × Euc d => fderiv ℝ (f p.1) p.2) = fun p =>
      continuousMultilinearCurryFin1 ℝ (Euc d) ℝ (iteratedFDeriv ℝ 1 (f p.1) p.2) :=
    funext fun p => s67_fderiv_eq_curry _ _
  rw [e]
  exact (continuousMultilinearCurryFin1 ℝ (Euc d) ℝ).continuous.comp (hf.cont_c2 1 (by norm_num))

theorem s67_cont_grad (hf : IsClassicalAdjointW C t φ f) :
    Continuous fun p : Set.Icc (0 : ℝ) t × Euc d => gradient (f p.1) p.2 := by
  have e : (fun p : Set.Icc (0 : ℝ) t × Euc d => gradient (f p.1) p.2) = fun p =>
      (InnerProductSpace.toDual ℝ (Euc d)).symm (fderiv ℝ (f p.1) p.2) := rfl
  rw [e]
  exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp (s67_cont_fderiv hf)

theorem s67_cont_lap (hf : IsClassicalAdjointW C t φ f) :
    Continuous fun p : Set.Icc (0 : ℝ) t × Euc d => Laplacian.laplacian (f p.1) p.2 := by
  have e : (fun p : Set.Icc (0 : ℝ) t × Euc d => Laplacian.laplacian (f p.1) p.2) = fun p =>
      ∑ i : Fin d, iteratedFDeriv ℝ 2 (f p.1) p.2
        ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] :=
    funext fun p => mnb_lap_formula (f p.1) p.2
  rw [e]
  exact continuous_finset_sum _ fun i _ => s67_cont_iter_apply hf (by norm_num) _

theorem s67_cont_kolm (hf : IsClassicalAdjointW C t φ f) (q' : ℝ) {B : Euc d → Euc d}
    (hB : Continuous B) :
    Continuous fun p : Set.Icc (0 : ℝ) t × Euc d => kolmL q' B (f p.1) p.2 := by
  unfold kolmL
  refine (s67_cont_lap hf).add ?_
  exact ((((continuous_snd).const_smul (-q')).add (hB.comp continuous_snd))).inner (s67_cont_grad hf)

/-- bounds of the classical solution through order two. -/
theorem s67_bd_all (hf : IsClassicalAdjointW C t φ f) :
    ∃ K0 K1 K2 : ℝ, ∀ r ∈ Icc (0 : ℝ) t, ∀ y, |f r y| ≤ K0 ∧ ‖fderiv ℝ (f r) y‖ ≤ K1 ∧
      ‖iteratedFDeriv ℝ 2 (f r) y‖ ≤ K2 := by
  obtain ⟨B0, h0⟩ := hf.bdd 0 (by norm_num)
  obtain ⟨B1, h1⟩ := hf.bdd 1 (by norm_num)
  obtain ⟨B2, h2⟩ := hf.bdd 2 (by norm_num)
  refine ⟨B0, B1, B2, fun r hr y => ⟨?_, ?_, h2 r hr y⟩⟩
  · have := h0 r hr y
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  · have := h1 r hr y
    rwa [norm_iteratedFDeriv_one] at this

end Classical

end HRS.MS.MovAdj

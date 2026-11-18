import HRS.MC.SEdgeVocab
import HRS.MC.SEdgeB9

/-!
# Packet B13c: `sed_B13c_chaos_limit` (relocation)

Route: `sed_B9_B_window_proof` with `ψ = fun z => fderiv f z (stdVec a)` (in `C_b^2`), together with the
index shuffle `D²(d_a f) = D³ f(e_a, ·, ·)` (`iteratedFDeriv` of a directional derivative).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.SEdge.B13c

open HRS.Sec7
open HRS.MC.SEdge

section Shuffle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- derivative of an evaluation at a fixed vector. -/
theorem b13c_fderiv_apply {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {c : E → E →L[ℝ] G} (hc : ContDiff ℝ 1 c) (z x u : E) :
    fderiv ℝ (fun y => c y u) z x = fderiv ℝ c z x u := by
  have h := iteratedFDeriv_clm_apply_const_apply (𝕜 := ℝ) (n := 1) hc (i := 1) le_rfl
    (x := z) (u := u) (m := ![x])
  simpa using h

theorem b13c_D3 {f : E → ℝ} (z x y w : E) :
    iteratedFDeriv ℝ 3 f z ![x, y, w] = fderiv ℝ (fderiv ℝ (fderiv ℝ f)) z x y w := by
  rw [iteratedFDeriv_succ_apply_right]
  rw [iteratedFDeriv_two_apply]
  simp [Fin.init, Fin.last]

theorem b13c_perm {f : E → ℝ} (hf : ContDiff ℝ 3 f) (z x y w : E) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ f)) z w x y = fderiv ℝ (fderiv ℝ (fderiv ℝ f)) z x y w := by
  set g := fderiv ℝ f with hg
  have hg2 : ContDiff ℝ 2 g := hf.fderiv_right (m := 2) (by norm_num)
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  -- step 1: symmetry of the second derivative of g
  have s1 : ∀ x y : E, fderiv ℝ (fderiv ℝ g) z x y = fderiv ℝ (fderiv ℝ g) z y x := fun x y =>
    (hg2.contDiffAt.isSymmSndFDerivAt (by simp)).eq x y
  -- step 2: symmetry in the last two arguments
  have hc1 : ContDiff ℝ 1 (fderiv ℝ g) := hg2.fderiv_right (m := 1) (by norm_num)
  have s2 : ∀ x y w : E, fderiv ℝ (fderiv ℝ g) z x y w = fderiv ℝ (fderiv ℝ g) z x w y := by
    intro x y w
    have e1 : ∀ y w : E, fderiv ℝ (fun z' => fderiv ℝ g z' y w) z x =
        fderiv ℝ (fderiv ℝ g) z x y w := by
      intro y w
      have hcy : ContDiff ℝ 1 (fun z' => fderiv ℝ g z' y) :=
        ContDiff.clm_apply (g := fun _ => y) hc1 contDiff_const
      rw [b13c_fderiv_apply (c := fun z' => fderiv ℝ g z' y) hcy, b13c_fderiv_apply hc1]
    have e2 : (fun z' => fderiv ℝ g z' y w) = (fun z' => fderiv ℝ g z' w y) := by
      funext z'
      have hs : IsSymmSndFDerivAt ℝ f z' := hf2.contDiffAt.isSymmSndFDerivAt (by simp)
      exact hs.eq y w
    rw [← e1 y w, e2, e1 w y]
  calc fderiv ℝ (fderiv ℝ g) z w x y = fderiv ℝ (fderiv ℝ g) z x w y := by rw [s1 w x]
    _ = fderiv ℝ (fderiv ℝ g) z x y w := (s2 x y w).symm

theorem b13c_shuffle {f : E → ℝ} (hf : ContDiff ℝ 3 f) (z u b c : E) :
    iteratedFDeriv ℝ 2 (fun z => fderiv ℝ f z u) z ![b, c] = iteratedFDeriv ℝ 3 f z ![u, b, c] := by
  have hg2 : ContDiff ℝ 2 (fderiv ℝ f) := hf.fderiv_right (m := 2) (by norm_num)
  rw [iteratedFDeriv_clm_apply_const_apply hg2 le_rfl, iteratedFDeriv_two_apply, b13c_D3]
  simpa using (b13c_perm hf z b c u).symm

end Shuffle

theorem sed_B13c_chaos_limit_proof {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s)
    (hs : s < (d : ℝ) / 2) {β : ℝ} (_hβ : 0 ≤ β) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ)
    (hβpos : 0 < β) {p : ℕ} {φ : Fin p → Torus d → ℝ}
    (hφ : ∀ a, Torus.IsSmooth (φ a)) {v : Fin d → Torus d → ℝ} (hv : ∀ j, Torus.IsSmooth (v j))
    {f : EuclideanSpace ℝ (Fin p) → ℝ} (hf : sed_StBdd f 3) (a : Fin p) :
    Tendsto (fun N : ℕ => ∫ X, sed_B d s ρ β v X *
        fderiv ℝ f (centeredStat (sed_Q d s N β ρ) φ X) (stdVec a) ∂(sed_Q d s N β ρ)) atTop
      (𝓝 ((1 / 2) * ∑ b, ∑ c,
        sed_Qt d s ρ v (responseInverse (periodicRiesz d s) (withDensityReal ρ) β (φ b))
            (responseInverse (periodicRiesz d s) (withDensityReal ρ) β (φ c)) *
          ∫ z, iteratedFDeriv ℝ 3 f z ![stdVec a, stdVec b, stdVec c]
            ∂(multivariateGaussian 0 (sed_Cmat d s β ρ φ)))) := by
  obtain ⟨hf3, hfb⟩ := hf
  have hg2 : ContDiff ℝ 2 (fderiv ℝ f) := hf3.fderiv_right (m := 2) (by norm_num)
  have hψ : HRS.MemCb 2 (fun z => fderiv ℝ f z (stdVec a)) := by
    refine ⟨hg2.clm_apply contDiff_const, fun j hj => ?_⟩
    obtain ⟨M, hM⟩ := hfb (j + 1) (by omega) (by omega)
    refine ⟨‖stdVec a‖ * M, ?_⟩
    rintro _ ⟨x, rfl⟩
    refine (norm_iteratedFDeriv_clm_apply_const (hg2.contDiffAt) (N := 2) (n := j)
      (by exact_mod_cast hj)).trans ?_
    rw [norm_iteratedFDeriv_fderiv]
    exact mul_le_mul_of_nonneg_left (hM x) (norm_nonneg _)
  have h := HRS.MC.SEdge.B9.sed_B9_B_window_proof hd hs0 hs hβpos hρ hφ hv hψ
  simp only [b13c_shuffle hf3] at h
  exact h

end HRS.MC.SEdge.B13c

end


import HRS.MC.E213U18n

/-!
# Packet e213u18 (part o): the cubic formula `Kproj_formula`

`K_{a,T}(ℓ_i⊗ℓ_j⊗ℓ_k) = κ_{ijk}` (`cubicKappa`): the three terms of `Kwin` on a product of evaluation functionals are
the initial term (`u18_T0`), the drift term (`u18_Dterm`, symmetric in `(j,k)`), and the covariance-tensor term
(`u18_Jterm`, symmetric in `(i,j)`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213U18

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213U11

variable {d : ℕ} {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

theorem u18_ellVec_reg (S : PreparedData d) (β₀ : ℝ) (hβ₀ : 0 ≤ β₀) (hs : S.s < (d : ℝ) / 2) :
    AEStronglyMeasurable (ellVec S β₀) S.μ0 ∧
      Integrable (fun x => ‖ellVec S β₀ x‖ * ‖ellVec S β₀ x‖ * ‖ellVec S β₀ x‖) S.μ0 := by
  haveI := μ0_isProb S
  obtain ⟨hm, B, hB⟩ := u18_ellPt_meas S.hd S.hs0 hs hβ₀ S.hρ0 (r := rLvl d) rfl
  have hm' : AEStronglyMeasurable (ellVec S β₀) S.μ0 := hm.aestronglyMeasurable
  refine ⟨hm', ?_⟩
  have hn : AEStronglyMeasurable (fun x => ‖ellVec S β₀ x‖) S.μ0 := hm'.norm
  refine Integrable.of_bound ((hn.mul hn).mul hn) (B * B * B) (Eventually.of_forall fun x => ?_)
  have h0 : 0 ≤ ‖ellVec S β₀ x‖ := norm_nonneg _
  have h1 : ‖ellVec S β₀ x‖ ≤ B := hB x
  have hB0 : 0 ≤ B := h0.trans h1
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  gcongr

theorem Kproj_formula_proof (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) :
    SatisfiesCubicFormula S β₀ m T a (gd.Kproj T a) := by
  classical
  unfold SatisfiesCubicFormula
  intro t φ hta hφ ℓ hℓ ν hν Ω' _ P' _ Z₀ Z hZ χ hχs hχ
  have h : U18Cov gd (a + T) t φ χ := u18_cov_data (gd := gd) T hT a ha t φ hta hφ ν hν P' Z₀ Z hZ χ hχs hχ
  have hs : S.s < (d : ℝ) / 2 := hE.s_lt
  obtain ⟨hK0m, hK0i⟩ := u18_ellVec_reg S β₀ hE.β₀_nonneg hs
  have hval : ((gd.Kproj T a : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3) =
      gd.Kwin T a := by
    unfold GaussData.Kproj
    rw [max_eq_left ha, dif_pos (HRS.MC.E213U11.Kwin_mem_proof gd T hT a ha)]
  rw [hval]
  show gd.Kwin T a (trilin ℓ) = _
  rw [kwin_trilin gd T hT a ha ℓ hK0m hK0i]
  -- the three terms
  have hT0 := u18_T0 (hE := hE) T hT a ha hta hφ ℓ hℓ
  obtain ⟨Dt, hDt⟩ : ∃ Dt : Fin 3 → Fin 3 → Fin 3 → ℝ, Dt = fun i j k =>
      ∫ ω, ℓ i (gd.Dwin T a ω) * ℓ j (gd.Zwin T a ω) * ℓ k (gd.Zwin T a ω) ∂gd.P₀ := ⟨_, rfl⟩
  obtain ⟨Jt, hJt⟩ : ∃ Jt : Fin 3 → Fin 3 → Fin 3 → ℝ, Jt = fun i j k =>
      ∫ ω, ℓ k (gd.Zwin T a ω) * gd.Jwin T a ω (mk2 (ℓ i) (ℓ j)) ∂gd.P₀ := ⟨_, rfl⟩
  rw [← hDt, ← hJt]
  have hDD : ∀ i j k, Dt i j k = ∫ r in Set.Icc 0 (t i), ∫ x, ∫ y, HRS.Main.hKernel d S.s
      (Torus.grad (propagator S.dyn S.ρ r (t i) (φ i))) x y * χ j r x * χ k r y := fun i j k => by
    rw [hDt]
    exact u18_Dterm gd T hT a ha h hta ℓ hℓ i j k
  have hDs : ∀ i j k, Dt i j k = Dt i k j := fun i j k => by
    rw [hDt]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only
    ring
  have hJJ : ∀ i j k, Jt i j k = 2 * S.β⁻¹ * ∫ r in Set.Icc 0 (min (t i) (t j)), ∫ x,
      inner ℝ (Torus.grad (propagator S.dyn S.ρ r (t i) (φ i)) x)
        (Torus.grad (propagator S.dyn S.ρ r (t j) (φ j)) x) * χ k r x := fun i j k => by
    rw [hJt]
    exact u18_Jterm gd T hT a ha h hta ℓ hℓ i j k
  have hJs : ∀ i j k, Jt i j k = Jt j i k := fun i j k => by
    rw [hJJ i j k, hJJ j i k, min_comm]
    simp_rw [real_inner_comm]
  unfold cubicKappa cyc3 sum6
  simp only
  rw [hT0, hDD 0 1 2, hDD 1 2 0, hDD 2 0 1, hJJ 0 1 2, hJJ 1 2 0, hJJ 2 0 1]
  have e1 := hDs 0 1 2
  have e2 := hDs 1 2 0
  have e3 := hDs 2 0 1
  have f1 := hJs 0 1 2
  have f2 := hJs 1 2 0
  have f3 := hJs 2 0 1
  rw [hDD 0 1 2, hDD 0 2 1] at e1
  rw [hDD 1 2 0, hDD 1 0 2] at e2
  rw [hDD 2 0 1, hDD 2 1 0] at e3
  rw [hJJ 0 1 2, hJJ 1 0 2] at f1
  rw [hJJ 1 2 0, hJJ 2 1 0] at f2
  rw [hJJ 2 0 1, hJJ 0 2 1] at f3
  rw [hDD 0 2 1, hDD 1 0 2, hDD 2 1 0, hJJ 1 0 2, hJJ 2 1 0, hJJ 0 2 1]
  have hβ : (2 : ℝ) / S.β = 2 * S.β⁻¹ := by ring
  rw [hβ]
  have hs' : S.dyn.s = S.s := rfl
  simp only [hs']
  linarith

end HRS.MC.E213U18

end

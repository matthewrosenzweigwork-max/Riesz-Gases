import HRS.MC.S7E4Aux4
import HRS.MC.S7E4Aux1
import HRS.MC.S7E1
import HRS.MC.S7E1b
import HRS.MC.S7E0a

/-!
# Packet `s7_E4_normalized_clt`, file 5: the finite sections have the law of a diagonal Gaussian chaos

For `eps > 0` and every accuracy `delta > 0` there is a finite section `S_L` of the chaos limit `Q_eps` with
`||Q_eps - S_L||_2 <= delta` and the law of `(1/2) sum_k a_k (g_k^2 - 1)`, `|a_k| <= Lam`
(`Lam` independent of `eps`): the hypothesis of `S7E4Aux3.normalized_clt`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators Matrix

noncomputable section

namespace HRS.MC.Sec7.E4A5

open HRS HRS.Sec7 HRS.MC.Sec7.E4A3

variable {d : ℕ}

/-- from the `lintegral` convergence to an `L^2` norm bound -/
theorem l2n_small {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {f : ℕ → Ω → ℝ}
    (hf : ∀ L, AEStronglyMeasurable (f L) P)
    (hlim : Tendsto (fun L : ℕ => ∫⁻ ω, ‖f L ω‖ₑ ^ 2 ∂P) atTop (𝓝 0)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ L, l2n P (f L) ≤ δ := by
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (δ ^ 2) := ENNReal.ofReal_pos.2 (by positivity)
  obtain ⟨L, hL⟩ := ((tendsto_order.1 hlim).2 _ hpos).exists
  refine ⟨L, ?_⟩
  rw [E0b.e0b_lint_eq _ (hf L)] at hL
  have h2 : eLpNorm (f L) 2 P ^ 2 ≤ ENNReal.ofReal δ ^ 2 := by
    rw [ENNReal.ofReal_pow hδ.le] at hL
    exact hL.le
  have h3 : eLpNorm (f L) 2 P ≤ ENNReal.ofReal δ := (ENNReal.pow_le_pow_left_iff (by norm_num)).1 h2
  exact ENNReal.toReal_le_of_le_ofReal hδ.le h3


theorem approx (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ)
    {e : ℕ → Torus d → ℝ} (he : IsONBL2Zero (withDensityReal ρ) e)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {G : ℕ → Ω → ℝ}
    (hG : s7_GaussData d s β ρ e P G) {Λ : ℝ}
    (hquad : ∀ ε : ℝ, 0 < ε → ∀ (L : ℕ) (x : ℕ → ℝ),
      |∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
          x i * x j * E0b.e0bH ρ e (hCut d s φ ε) i j| ≤ Λ * ∑ i ∈ Finset.range L, x i ^ 2)
    (hΛ : 0 ≤ Λ) {ε : ℝ} (hε : 0 < ε) {Qε : Ω → ℝ} (hQm : AEMeasurable Qε P)
    (hQ : s7_IsChaosLimit d s β ρ e P G (hCut d s φ ε) Qε) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (L : ℕ) (a : Fin L → ℝ) (S : Ω → ℝ), (∀ k, |a k| ≤ Λ) ∧ MemLp S 2 P ∧
      P.map S = (Measure.pi fun _ : Fin L => gaussianReal 0 1).map
        (fun y : Fin L → ℝ => (1 / 2 : ℝ) * ∑ k, a k * (y k ^ 2 - 1)) ∧
      l2n P (fun ω => Qε ω - S ω) ≤ δ := by
  obtain ⟨hm, hsy, hL2⟩ := (E1b.s7_E1b_cutoff_kernel_admissible_proof hd hs0 hsd ρ hρ φ hφ).1 ε hε
  have hG4 := E0b.e0b_memLp4 (e := e) (ρ := ρ) (s := s) (β := β) hG
  set H : ℕ → ℕ → ℝ := E0b.e0bH ρ e (hCut d s φ ε) with hHdef
  set Sf : ℕ → Ω → ℝ := fun L ω => (1 / 2 : ℝ) * ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
    H i j * (G i ω * G j ω -
      susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j)) with hSfdef
  have hSmem : ∀ L, MemLp (Sf L) 2 P := by
    intro L
    refine MemLp.const_mul ?_ _
    refine memLp_finsetSum _ fun i _ => memLp_finsetSum _ fun j _ => ?_
    exact (E0b.e0b_X_memLp2 hG4 _ i j).const_mul _
  have hfmeas : ∀ L, AEStronglyMeasurable (fun ω => Qε ω - Sf L ω) P := fun L =>
    hQm.aestronglyMeasurable.sub (hSmem L).aestronglyMeasurable
  obtain ⟨L, hL⟩ := l2n_small hfmeas hQ hδ
  -- finite-dimensional data
  set C : Matrix (Fin L) (Fin L) ℝ := Matrix.of fun i j : Fin L =>
    susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j) with hCdef
  set Hm : Matrix (Fin L) (Fin L) ℝ := Matrix.of fun i j : Fin L => H i j with hHm
  have hC : C.PosSemidef := E0a.s7e_cov_psd hd hs0 hsd hβ hρ he L
  have hHt : Hmᵀ = Hm := by
    ext i j
    simp only [Matrix.transpose_apply, hHm, Matrix.of_apply]
    exact E1.e1_H_symm hρ he hsy hL2 (j : ℕ) (i : ℕ)
  have hCle : ∀ z : Fin L → ℝ, z ⬝ᵥ C *ᵥ z ≤ z ⬝ᵥ z := by
    obtain ⟨c, -, -, hall⟩ := E1Aux1.e1a_cov_bounds hd hs0 hsd hβ hρ
    have h1 := (hall he L).1
    intro z
    have h2 := h1.dotProduct_mulVec_nonneg z
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul] at h2
    simp only [star_trivial, smul_eq_mul, one_mul] at h2
    linarith
  have hq : ∀ z : Fin L → ℝ, |z ⬝ᵥ Hm *ᵥ z| ≤ Λ * (z ⬝ᵥ z) := by
    intro z
    set x : ℕ → ℝ := fun i => if h : i < L then z ⟨i, h⟩ else 0 with hxdef
    have hxz : ∀ i : Fin L, x (i : ℕ) = z i := fun i => by simp [hxdef]
    have e1 : z ⬝ᵥ Hm *ᵥ z = ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L, x i * x j * H i j := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_range, hxz, hHm, Matrix.of_apply]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    have e2 : z ⬝ᵥ z = ∑ i ∈ Finset.range L, x i ^ 2 := by
      simp only [dotProduct, Finset.sum_range, hxz, sq]
    rw [e1, e2]
    exact hquad ε hε L x
  obtain ⟨a, hab, hlaw⟩ := E4A1.reduce hC hHt hΛ hq hCle
  have hV : Measurable (fun ω => (WithLp.toLp 2 fun b : Fin L => G b ω : EuclideanSpace ℝ (Fin L))) :=
    (MeasurableEquiv.toLp 2 (Fin L → ℝ)).measurable.comp (Measurable.of_eval fun b => hG.1 b)
  have hSeq : (fun ω => E4A1.psi C Hm (WithLp.toLp 2 fun b : Fin L => G b ω :
      EuclideanSpace ℝ (Fin L))) = Sf L := by
    funext ω
    simp only [E4A1.psi, hSfdef, hHm, hCdef, Matrix.of_apply, Finset.sum_range]
  refine ⟨L, a, fun ω => E4A1.psi C Hm (WithLp.toLp 2 fun b : Fin L => G b ω :
      EuclideanSpace ℝ (Fin L)), hab, ?_, ?_, ?_⟩
  · rw [hSeq]; exact hSmem L
  · have h : P.map (fun ω => (WithLp.toLp 2 fun b : Fin L => G b ω : EuclideanSpace ℝ (Fin L))) =
        multivariateGaussian (0 : EuclideanSpace ℝ (Fin L)) C := hG.2 L
    rw [← hlaw, ← h]
    exact (Measure.map_map (E4A1.psi_meas C Hm) hV).symm
  · rw [hSeq]; exact hL

end HRS.MC.Sec7.E4A5

end

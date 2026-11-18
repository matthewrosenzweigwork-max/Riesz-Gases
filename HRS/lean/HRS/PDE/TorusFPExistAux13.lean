import HRS.PDE.TorusFPExistAux12

/-!
# D1 existence, helper 13: `C²` approximation of `C²` functions on the torus by smooth ones
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped Convolution

namespace HRS

variable {n : ℕ}

theorem d1_fderiv_periodic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {G : Euc n → E}
    (hp : ∀ (y : Euc n) (k : Lattice n), G (y + Lattice.toEuc k) = G y) (y : Euc n) (k : Lattice n) :
    fderiv ℝ G (y + Lattice.toEuc k) = fderiv ℝ G y := by
  rw [← fderiv_comp_add_right]
  congr 1
  funext z
  exact hp z k

theorem d1_lap_bound (A B : Euc n →L[ℝ] Euc n →L[ℝ] ℝ) {ε' : ℝ} (h : ‖B - A‖ ≤ ε') :
    |∑ i : Fin n, A (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ i) -
      ∑ i : Fin n, B (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ i)| ≤
      (n : ℝ) * ε' := by
  rw [← Finset.sum_sub_distrib]
  calc |∑ i : Fin n, (A (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ i) -
        B (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ i))|
      ≤ ∑ i : Fin n, |A (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ i) -
        B (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, ε' := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h1 := ContinuousLinearMap.le_opNorm₂ (B - A)
          (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ i)
        have hn1 : ‖EuclideanSpace.basisFun (Fin n) ℝ i‖ = 1 := by simp
        rw [hn1, mul_one, mul_one] at h1
        simp only [ContinuousLinearMap.sub_apply, Real.norm_eq_abs] at h1
        rw [abs_sub_comm]
        exact h1.trans h
    _ = (n : ℝ) * ε' := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

set_option maxHeartbeats 1600000 in
/-- `C²`-approximation: a `C²` function on the torus is approximated, together with its gradient and
Laplacian, uniformly by smooth functions. -/
theorem d1_exists_C2_approx {φ : Torus n → ℝ} (hφ : Torus.IsCk 2 φ) {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : Torus n → ℝ, Torus.IsSmooth ψ ∧ ∀ x, |φ x - ψ x| ≤ ε ∧
      ‖Torus.grad φ x - Torus.grad ψ x‖ ≤ ε ∧ |Torus.laplacian φ x - Torus.laplacian ψ x| ≤ ε := by
  set F := Torus.lift φ with hFdef
  have hF : ContDiff ℝ 2 F := d1_contDiff_of_isCk2 hφ le_rfl
  have hF0 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have hF1 : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (m := 1) (by norm_num)
  have hF2c : Continuous (fderiv ℝ (fderiv ℝ F)) := hF1.continuous_fderiv one_ne_zero
  have p0 : ∀ (y : Euc n) (k : Lattice n), F (y + Lattice.toEuc k) = F y :=
    fun y k => Torus.lift_periodic φ y k
  have p1 := d1_fderiv_periodic p0
  have p2 := d1_fderiv_periodic p1
  obtain ⟨B0, hB0⟩ := d1_periodic_bounded hF.continuous p0
  obtain ⟨B1, hB1⟩ := d1_periodic_bounded hF1.continuous p1
  obtain ⟨B2, hB2⟩ := d1_periodic_bounded hF2c p2
  have u0 := d1_periodic_uniformContinuous hF.continuous p0
  have u1 := d1_periodic_uniformContinuous hF1.continuous p1
  have u2 := d1_periodic_uniformContinuous hF2c p2
  set ε' : ℝ := ε / ((n : ℝ) + 1) with hε'
  have hε'pos : 0 < ε' := by positivity
  obtain ⟨r0, hr0, h0⟩ := Metric.uniformContinuous_iff.1 u0 ε' hε'pos
  obtain ⟨r1, hr1, h1⟩ := Metric.uniformContinuous_iff.1 u1 ε' hε'pos
  obtain ⟨r2, hr2, h2⟩ := Metric.uniformContinuous_iff.1 u2 ε' hε'pos
  set r : ℝ := min (min r0 r1) r2 with hr
  have hrpos : 0 < r := lt_min (lt_min hr0 hr1) hr2
  let φb : ContDiffBump (0 : Euc n) := ⟨r / 2, r, half_pos hrpos, half_lt_self hrpos⟩
  set ρ : Euc n → ℝ := φb.normed volume with hρ
  have hρi : Integrable ρ := φb.integrable_normed (μ := volume)
  have hρ0 : ∀ t, 0 ≤ ρ t := fun t => φb.nonneg_normed (μ := volume) t
  set ψr : Euc n → ℝ := d1_mol ρ F with hψr
  -- smoothness
  have hψsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψr := by
    have := (φb.hasCompactSupport_normed (μ := volume)).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
      (φb.contDiff_normed (μ := volume) (n := ⊤)) (hF.continuous.locallyIntegrable (μ := volume))
    exact this
  -- periodicity
  have hψp : ∀ (y : Euc n) (k : Lattice n), ψr (y + Lattice.toEuc k) = ψr y := by
    intro y k
    simp only [hψr, d1_mol]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    have : y + Lattice.toEuc k - t = (y - t) + Lattice.toEuc k := by abel
    simp only [this, p0]
  -- derivatives
  have hder1 : ∀ y, fderiv ℝ ψr y = d1_mol ρ (fderiv ℝ F) y := fun y =>
    (d1_mol_hasFDerivAt hρi hρ0 hF0 hB0 hB1 y).fderiv
  have hder1' : fderiv ℝ ψr = d1_mol ρ (fderiv ℝ F) := funext hder1
  have hder2 : ∀ y, fderiv ℝ (fderiv ℝ ψr) y = d1_mol ρ (fderiv ℝ (fderiv ℝ F)) y := by
    intro y
    rw [hder1']
    exact (d1_mol_hasFDerivAt hρi hρ0 hF1 hB1 hB2 y).fderiv
  -- approximation estimates
  have hmg0 : AEStronglyMeasurable F volume := hF.continuous.aestronglyMeasurable
  have e0 : ∀ y, dist (ψr y) (F y) ≤ ε' := fun y =>
    φb.dist_normed_convolution_le (μ := volume) hmg0 (fun x hx => by
      have : dist x y < r0 := lt_of_lt_of_le hx (by
        show r ≤ r0
        exact (min_le_left _ _).trans (min_le_left _ _))
      exact (h0 this).le)
  have e1 : ∀ y, ‖d1_mol ρ (fderiv ℝ F) y - fderiv ℝ F y‖ ≤ ε' := fun y => by
    have := φb.dist_normed_convolution_le (μ := volume) hF1.continuous.aestronglyMeasurable
      (x₀ := y) (ε := ε') (fun x hx => by
      have : dist x y < r1 := lt_of_lt_of_le hx (by
        show r ≤ r1
        exact (min_le_left _ _).trans (min_le_right _ _))
      exact (h1 this).le)
    rw [dist_eq_norm] at this
    exact this
  have e2 : ∀ y, ‖d1_mol ρ (fderiv ℝ (fderiv ℝ F)) y - fderiv ℝ (fderiv ℝ F) y‖ ≤ ε' := fun y => by
    have := φb.dist_normed_convolution_le (μ := volume) hF2c.aestronglyMeasurable
      (x₀ := y) (ε := ε') (fun x hx => by
      have : dist x y < r2 := lt_of_lt_of_le hx (min_le_right _ _)
      exact (h2 this).le)
    rw [dist_eq_norm] at this
    exact this
  -- the torus function
  let ψ : Torus n → ℝ := fun x => ψr (Torus.rep x)
  have hlift : Torus.lift ψ = ψr := by
    funext y
    exact periodic_rep_mk ψr hψp y
  refine ⟨ψ, ?_, fun x => ?_⟩
  · unfold Torus.IsSmooth Torus.IsCk
    rw [hlift]; exact hψsm
  have hφx : φ x = F (Torus.rep x) := by simp [hFdef, Torus.lift, Torus.mk_rep]
  have hnε : (n : ℝ) * ε' ≤ ε := by
    rw [hε', mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · rw [hφx, abs_sub_comm]
    have := e0 (Torus.rep x)
    rw [Real.dist_eq] at this
    exact this.trans (by
      have : ε' ≤ ε := by
        rw [hε']; apply div_le_self hε.le; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
      exact this)
  · have hg1 : Torus.grad φ x = gradient F (Torus.rep x) := rfl
    have hg2 : Torus.grad ψ x = gradient ψr (Torus.rep x) := by
      unfold Torus.grad; rw [hlift]
    rw [hg1, hg2]
    unfold gradient
    rw [← map_sub, LinearIsometryEquiv.norm_map, hder1]
    have := e1 (Torus.rep x)
    rw [norm_sub_rev] at this
    refine this.trans ?_
    rw [hε']; apply div_le_self hε.le; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  · have hl1 : Torus.laplacian φ x = ∑ i : Fin n, fderiv ℝ (fderiv ℝ F) (Torus.rep x)
        (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ i) := by
      unfold Torus.laplacian; exact d1_laplacian_eq_sum F _
    have hl2 : Torus.laplacian ψ x = ∑ i : Fin n, d1_mol ρ (fderiv ℝ (fderiv ℝ F)) (Torus.rep x)
        (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ i) := by
      unfold Torus.laplacian; rw [hlift, d1_laplacian_eq_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hder2]
    rw [hl1, hl2]
    exact (d1_lap_bound _ _ (e2 (Torus.rep x))).trans hnε

end HRS

import HRS.MC.D3T3Aux5

/-!
# Packet D3T3, auxiliary facts: the lattice sum `∑ |k|² ψ̂(tk)²`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal FourierTransform

namespace HRS.MC.D3T3

open HRS HRS.MC.FDLE HRS.MC.Per HRS.MC.D3T1

variable {d : ℕ}

lemma d3f_rep_zero : Torus.rep (0 : Torus d) = 0 := by
  ext i
  have h0 : (0 : UnitAddCircle) = ((0 : ℝ) : AddCircle (1 : ℝ)) := (AddCircle.coe_zero _).symm
  have : ((AddCircle.equivIco (1 : ℝ) 0 ((0 : ℝ) : AddCircle (1 : ℝ)) : Set.Ico (0 : ℝ) (0 + 1)) : ℝ) = 0 := by
    rw [AddCircle.equivIco_coe_of_mem ⟨le_refl _, by norm_num⟩]
  simp only [Torus.rep, Pi.zero_apply, h0, this]
  rfl

/-- `Δ φ_t (0) = t^{-(d+2)} Δ φ (0)`. -/
lemma d3f_lap_phiScale {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {t : ℝ} (ht : 0 < t) :
    Laplacian.laplacian (fdlPhiScale ψ t) 0 = (t ^ (d + 2))⁻¹ * Laplacian.laplacian (fdlPhi ψ) 0 := by
  have hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fdlPhi ψ) := per_phi_contDiff hψ
  have hφ2 : ContDiff ℝ 2 (fdlPhi ψ) := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  set a : ℝ := t⁻¹ with ha
  set L : Euc d →L[ℝ] Euc d := a • ContinuousLinearMap.id ℝ (Euc d) with hL
  have hfun : fdlPhiScale ψ t = fun y => ((t ^ d)⁻¹) • (fdlPhi ψ ∘ L) y := by
    funext y; simp [fdlPhiScale, hL, ha]
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ (EuclideanSpace.basisFun (Fin d) ℝ),
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (fdlPhi ψ)
      (EuclideanSpace.basisFun (Fin d) ℝ)]
  simp only
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hfun, iteratedFDeriv_const_smul_apply' (hφ2.comp L.contDiff).contDiffAt,
    L.iteratedFDeriv_comp_right hφ2 _ le_rfl]
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousMultilinearMap.smul_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, smul_eq_mul]
  have : (fun j : Fin 2 => L (![EuclideanSpace.basisFun (Fin d) ℝ i, EuclideanSpace.basisFun (Fin d) ℝ i] j))
      = fun j => a • ![EuclideanSpace.basisFun (Fin d) ℝ i, EuclideanSpace.basisFun (Fin d) ℝ i] j := by
    funext j; simp [hL]
  rw [this, ContinuousMultilinearMap.map_smul_univ]
  simp [ha, mul_comm, mul_left_comm, pow_succ, mul_assoc]


lemma d3f_per_smooth {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {t : ℝ} (ht : 0 < t) (n : ℕ) :
    ContDiff ℝ n (Torus.lift (fdlPer (fdlPhiScale ψ t))) := by
  rw [per_lift_fdlPer]
  exact (per_G_contDiff (per_phiScale_contDiff hψ t) (fun x hx => per_phiScale_zero hψ ht hx.le)).of_le
    (by exact_mod_cast le_top)

lemma d3f_lap_per_small {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {t : ℝ} (ht : 0 < t)
    (ht2 : t ≤ 1 / 2) :
    Torus.laplacian (fdlPer (fdlPhiScale ψ t)) 0 =
      (t ^ (d + 2))⁻¹ * Laplacian.laplacian (fdlPhi ψ) 0 := by
  unfold Torus.laplacian
  rw [d3f_rep_zero, ← d3f_lap_phiScale hψ ht]
  have hev : Torus.lift (fdlPer (fdlPhiScale ψ t)) =ᶠ[𝓝 (0 : Euc d)] fdlPhiScale ψ t := by
    filter_upwards [Metric.ball_mem_nhds (0 : Euc d) (by norm_num : (0 : ℝ) < 1 / 2)] with y hy
    rw [per_lift_fdlPer]
    beta_reduce
    rw [tsum_eq_single (0 : Lattice d)]
    · have h0 : Lattice.toEuc (0 : Lattice d) = 0 := by ext i; simp [Lattice.toEuc]
      simp [h0]
    · intro n hn
      apply per_phiScale_zero hψ ht
      have hy' : ‖y‖ < 1 / 2 := by simpa using hy
      have h1 : 1 ≤ ‖Lattice.toEuc n‖ := d3f_enorm_ge_one hn
      have h2 := norm_sub_le (y + Lattice.toEuc n) y
      have h3 : ‖Lattice.toEuc n‖ ≤ ‖y + Lattice.toEuc n‖ + ‖y‖ := by
        have := norm_sub_le (y + Lattice.toEuc n) y
        simpa using this
      linarith
  exact (InnerProductSpace.laplacian_congr_nhds hev).eq_of_nhds

end HRS.MC.D3T3

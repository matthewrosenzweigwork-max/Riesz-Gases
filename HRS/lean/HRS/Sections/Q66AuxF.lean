import HRS.Sections.Q66AuxE

/-!
# Packet Q66: the transport field `v` with `-div(ρ v) = ρ r`

For a smooth positive density `ρ` and a smooth `r` with `∫ ρ r = 0` there are smooth components
`v_j` (`v = ρ⁻¹ ∇ψ`, `Δψ = -ρ r`) with `∑_j ∂_j(ρ v_j) = -ρ r`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

noncomputable section

namespace HRS.Q66

open HRS.PDE HRS.PDE.MFAux HRS.PDE.MFSchauder HRS.PDE.MFApriori HRS.PDE.MFThermalReg

variable {d : ℕ}

theorem q66_isSmooth_partialDeriv {f : Torus d → ℝ} (hf : Torus.IsSmooth f) (i : Fin d) :
    Torus.IsSmooth (Torus.partialDeriv i f) := by
  have hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift f) := hf
  have h1 : Torus.IsCk 1 f := ContDiff.of_le hF (by norm_cast)
  unfold Torus.IsSmooth Torus.IsCk
  rw [HRS.PDE.lift_partialDeriv i f h1]
  exact (hF.fderiv_right (by simp)).clm_apply contDiff_const

theorem q66_isSmooth_mul {f g : Torus d → ℝ} (hf : Torus.IsSmooth f) (hg : Torus.IsSmooth g) :
    Torus.IsSmooth (fun x => f x * g x) := by
  have hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift f) := hf
  have hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift g) := hg
  exact hF.mul hG

theorem q66_isSmooth_inv {f : Torus d → ℝ} (hf : Torus.IsSmooth f) (h0 : ∀ x, f x ≠ 0) :
    Torus.IsSmooth (fun x => (f x)⁻¹) := by
  have hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift f) := hf
  exact hF.inv (fun y => h0 _)

theorem q66_coeffOf_zero (f : Torus d → ℝ) : coeffOf f 0 = ((∫ x, f x : ℝ) : ℂ) := by
  unfold coeffOf
  rw [funFourierCoeff_eq_int]
  have : ∀ x : Torus d, UnitAddTorus.mFourier (-(0 : Lattice d)) x = 1 := by
    intro x; simp [UnitAddTorus.mFourier_zero]
  simp_rw [this, one_mul]
  exact integral_complex_ofReal

theorem q66_toFun_neg (c : Coeff d) (x : Torus d) : toFun (fun k => -c k) x = - toFun c x := by
  unfold toFun series
  simp only [neg_mul, tsum_neg, Complex.neg_re]

/-- The Poisson solution: smooth `ψ` with `Δψ = -f` for smooth `f` of mean zero. -/
theorem q66_poisson {f : Torus d → ℝ} (hf : Torus.IsSmooth f) (hmean : ∫ x, f x = 0) :
    ∃ ψ : Torus d → ℝ, Torus.IsSmooth ψ ∧ ∀ x, Torus.laplacian ψ x = - f x := by
  classical
  have hfc : Continuous f := q66_cont_of_smooth hf
  set c : Coeff d := coeffOf f with hc
  have hc0 : c 0 = 0 := by rw [hc, q66_coeffOf_zero, hmean]; simp
  have hcreal : IsRealCoeff c := isRealCoeff_coeffOf f
    (hfc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  have hcH : ∀ n : ℕ, MemHs (n : ℝ) c := fun n =>
    memHs_of_isCk n f (q66_isCk_of_smooth hf n)
  set w : Lattice d → ℝ := fun k => 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 with hw
  set e : Coeff d := fun k => if k = 0 then 0 else c k / (w k : ℂ) with he
  have hw1 : ∀ k : Lattice d, k ≠ 0 → 1 ≤ w k := fun k hk => by
    have h1 := HRS.one_le_enorm k hk
    have h2 : (1 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
    simp only [hw]; nlinarith
  have hw0 : ∀ k : Lattice d, k ≠ 0 → 0 < w k := fun k hk => lt_of_lt_of_le one_pos (hw1 k hk)
  have hnorm : ∀ k, ‖e k‖ ≤ ‖c k‖ := by
    intro k
    by_cases hk : k = 0
    · simp [he, hk]
    · simp only [he, hk, ite_false]
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hw0 k hk)]
      exact div_le_self (norm_nonneg _) (hw1 k hk)
  have heH : ∀ n : ℕ, MemHs (n : ℝ) e := fun n => by
    unfold MemHs
    refine Summable.of_nonneg_of_le (fun k => mul_nonneg (MFProduct.sobWeight_nonneg _ k) (sq_nonneg _))
      (fun k => ?_) (hcH n)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hnorm k) 2)
      (MFProduct.sobWeight_nonneg _ k)
  have hereal : IsRealCoeff e := by
    intro k
    by_cases hk : k = 0
    · subst hk; simp [he]
    · have hk' : -k ≠ 0 := neg_ne_zero.mpr hk
      simp only [he, hk, hk', ite_false]
      have hwn : w (-k) = w k := by simp only [hw, HRS.enorm_neg]
      rw [hcreal k, hwn, map_div₀, Complex.conj_ofReal]
  have hmem : MemHs ((d + 3 : ℕ) : ℝ) e := heH (d + 3)
  have hlap : Torus.laplacian (toFun e) = toFun (laplaceCoeff e) :=
    laplacian_toFun e ((d + 3 : ℕ) : ℝ) hmem hereal (by
      push_cast; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)])
  have hlc : laplaceCoeff e = fun k => -c k := by
    funext k
    by_cases hk : k = 0
    · subst hk; simp [laplaceCoeff, he, hc0]
    · simp only [laplaceCoeff, he, hk, ite_false]
      have : (w k : ℂ) ≠ 0 := by exact_mod_cast (hw0 k hk).ne'
      simp only [hw] at this ⊢
      field_simp
  refine ⟨toFun e, isSmooth_toFun_of_decay e hereal heH, fun x => ?_⟩
  have hsum : Summable fun k => ‖coeffOf f k‖ :=
    summable_norm_of_memHs ((d + 1 : ℕ) : ℝ)
      (by push_cast; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]) _ (hcH (d + 1))
  rw [hlap, hlc, q66_toFun_neg, hc, HRS.PDE.MFThermalReg.toFun_coeffOf hfc hsum]

/-- A smooth vector field (by components) with `∑_j ∂_j(ρ v_j) = -(ρ r)`. -/
theorem q66_exists_field {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {r : Torus d → ℝ}
    (hr : Torus.IsSmooth r) (hmean : ∫ x, ρ x * r x = 0) :
    ∃ v : Fin d → Torus d → ℝ, (∀ j, Torus.IsSmooth (v j)) ∧
      ∀ x, ∑ j, Torus.partialDeriv j (fun y => ρ y * v j y) x = -(ρ x * r x) := by
  obtain ⟨ψ, hψ, hΔ⟩ := q66_poisson (q66_isSmooth_mul hρ.smooth hr) hmean
  refine ⟨fun j y => (ρ y)⁻¹ * Torus.partialDeriv j ψ y, fun j => ?_, fun x => ?_⟩
  · exact q66_isSmooth_mul (q66_isSmooth_inv hρ.smooth (fun y => (hρ.pos y).ne'))
      (q66_isSmooth_partialDeriv hψ j)
  · have h2 : Torus.IsCk 2 ψ := q66_isCk_of_smooth hψ 2
    have e2 : ∀ j : Fin d, (fun y => ρ y * ((ρ y)⁻¹ * Torus.partialDeriv j ψ y)) =
        fun y => Torus.partialDeriv j ψ y := fun j => by
      funext y; field_simp [(hρ.pos y).ne']
    simp_rw [e2]
    rw [← laplacian_eq_sum ψ h2 x, hΔ]

end HRS.Q66

end

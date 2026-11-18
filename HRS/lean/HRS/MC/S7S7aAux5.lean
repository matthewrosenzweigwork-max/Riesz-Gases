import HRS.MC.S7S7aAux4

/-!
# Packet `s7_S7a_mode_data`, helper 5: the Poisson solve with Sobolev bounds, and the transport fields
For smooth `a` with `mu(a) = 0` there is a smooth `v` with `-div(rho v) = rho a` and
`||v_j||_{H^{d+2}} <= P ||a||_{H^{d+1}}`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ComplexConjugate

noncomputable section

namespace HRS.MC.Sec7.S7a

open HRS HRS.PDE HRS.PDE.MFApriori HRS.PDE.MFPair HRS.PDE.MFThermalReg HRS.PDE.ClassicalPart

variable {d : ℕ} {s : ℝ}

theorem s7a_poisson_bound {f ψ : Torus d → ℝ} (hψ : Torus.IsSmooth ψ)
    (hΔ : ∀ x, Torus.laplacian ψ x = -f x) (m : ℕ) (hf : MemHs (m : ℝ) (coeffOf f)) (j : Fin d) :
    MemHs ((m : ℝ) + 1) (coeffOf (Torus.partialDeriv j ψ)) ∧
      HRS.PDE.hsNorm ((m : ℝ) + 1) (coeffOf (Torus.partialDeriv j ψ)) ≤
        Real.sqrt 2 * HRS.PDE.hsNorm (m : ℝ) (coeffOf f) := by
  have h2 : Torus.IsCk 2 ψ := HRS.Q66.q66_isCk_of_smooth hψ 2
  have h1 : Torus.IsCk 1 ψ := HRS.Q66.q66_isCk_of_smooth hψ 1
  have hlap := coeffOf_laplacian ψ h2
  have hΔf : Torus.laplacian ψ = fun x => (-1 : ℝ) * f x := funext fun x => by rw [hΔ x]; ring
  have hco : ∀ k, laplaceCoeff (coeffOf ψ) k = -coeffOf f k := by
    intro k
    rw [← hlap, hΔf, coeffOf_const_mul_fun]
    simp
  rw [coeffOf_partialDeriv j ψ h1]
  refine s7a_hs_le (Real.sqrt_nonneg 2) hf (fun k => ?_)
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  by_cases hk : k = 0
  · subst hk
    have h0 : derivCoeff j (coeffOf ψ) 0 = 0 := by simp [derivCoeff]
    rw [h0, norm_zero]
    have := mul_nonneg (MFProduct.sobWeight_nonneg (m : ℝ) (0 : Lattice d)) (sq_nonneg ‖coeffOf f 0‖)
    nlinarith [this]
  · set w : ℝ := 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 with hw
    have hen : 1 ≤ Lattice.enorm k := HRS.one_le_enorm k hk
    have hw1 : 1 ≤ w := by
      have : (1 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
      have h3 : (1 : ℝ) ≤ Lattice.enorm k ^ 2 := by nlinarith
      rw [hw]; nlinarith
    have hw0 : 0 < w := by linarith
    -- norms
    have hf_eq : ‖coeffOf f k‖ = w * ‖coeffOf ψ k‖ := by
      have := congrArg norm (hco k)
      rw [norm_neg] at this
      rw [← this]
      unfold laplaceCoeff
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw0]
    have hd_le : ‖derivCoeff j (coeffOf ψ) k‖ ^ 2 ≤ w * ‖coeffOf ψ k‖ ^ 2 := by
      rw [norm_derivCoeff, mul_pow, mul_pow]
      have hc : |((k j : ℤ) : ℝ)| ≤ Lattice.enorm k := HRS.PDE.abs_coord_le_enorm k j
      have hc2 : |((k j : ℤ) : ℝ)| ^ 2 ≤ Lattice.enorm k ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hc 2
      have : (2 * Real.pi) ^ 2 * |((k j : ℤ) : ℝ)| ^ 2 * ‖coeffOf ψ k‖ ^ 2 ≤
          (2 * Real.pi) ^ 2 * Lattice.enorm k ^ 2 * ‖coeffOf ψ k‖ ^ 2 := by
        gcongr
      calc _ ≤ _ := this
        _ = w * ‖coeffOf ψ k‖ ^ 2 := by rw [hw]; ring
    have hsw : sobWeight ((m : ℝ) + 1) k = sobWeight (m : ℝ) k * (1 + w) := by
      rw [← MFProduct.sobWeight_mul]
      congr 1
      unfold sobWeight
      rw [Real.rpow_one]
    have hsw0 : 0 ≤ sobWeight (m : ℝ) k := MFProduct.sobWeight_nonneg _ k
    rw [hsw, hf_eq]
    set P := ‖coeffOf ψ k‖ with hP
    have hP0 : 0 ≤ P := norm_nonneg _
    calc sobWeight (m : ℝ) k * (1 + w) * ‖derivCoeff j (coeffOf ψ) k‖ ^ 2
        ≤ sobWeight (m : ℝ) k * (1 + w) * (w * P ^ 2) := by gcongr
      _ ≤ 2 * (sobWeight (m : ℝ) k * (w * P) ^ 2) := by
          have : (1 + w) * (w * P ^ 2) ≤ 2 * (w * P) ^ 2 := by
            have : (1 + w) ≤ 2 * w := by linarith
            nlinarith [mul_nonneg hw0.le (sq_nonneg P)]
          nlinarith [mul_le_mul_of_nonneg_left this hsw0]

theorem s7a_v_exists (hd : 2 ≤ d) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ a : Torus d → ℝ, Torus.IsSmooth a → ∫ x, a x ∂(withDensityReal ρ) = 0 →
      ∃ v : Fin d → Torus d → ℝ, (∀ j, Torus.IsSmooth (v j)) ∧
        (∀ x, ∑ j, Torus.partialDeriv j (fun y => ρ y * v j y) x = -(ρ x * a x)) ∧
        ∀ j, HRS.PDE.hsNorm (((d + 2 : ℕ)) : ℝ) (coeffOf (v j)) ≤
          P * HRS.PDE.hsNorm (((d + 1 : ℕ)) : ℝ) (coeffOf a) := by
  have hd0 : 0 < d := by omega
  have hinv : Torus.IsSmooth (fun y => (ρ y)⁻¹) :=
    HRS.Q66.q66_isSmooth_inv hρ.smooth (fun y => (hρ.pos y).ne')
  obtain ⟨Ci, hCi0, hCi⟩ := s7a_mul_smooth hd0 hinv (d + 2)
  obtain ⟨Cp, hCp0, hCp⟩ := s7a_mul_smooth hd0 hρ.smooth (d + 1)
  refine ⟨Ci * Real.sqrt 2 * Cp, by positivity, fun a ha hmean => ?_⟩
  have hρm : Measurable ρ := hρ.density.measurable
  have hf : Torus.IsSmooth (fun x => ρ x * a x) := HRS.Q66.q66_isSmooth_mul hρ.smooth ha
  have hmean' : ∫ x, ρ x * a x = 0 := by
    rw [← integral_withDensityReal_eq ρ hρm (fun x => (hρ.pos x).le)]; exact hmean
  obtain ⟨ψ, hψ, hΔ⟩ := HRS.Q66.q66_poisson hf hmean'
  refine ⟨fun j y => (ρ y)⁻¹ * Torus.partialDeriv j ψ y, fun j => ?_, fun x => ?_, fun j => ?_⟩
  · exact HRS.Q66.q66_isSmooth_mul hinv (HRS.Q66.q66_isSmooth_partialDeriv hψ j)
  · have h2 : Torus.IsCk 2 ψ := HRS.Q66.q66_isCk_of_smooth hψ 2
    have e2 : ∀ j : Fin d, (fun y => ρ y * ((ρ y)⁻¹ * Torus.partialDeriv j ψ y)) =
        fun y => Torus.partialDeriv j ψ y := fun j => by
      funext y; field_simp [(hρ.pos y).ne']
    simp_rw [e2]
    rw [← laplacian_eq_sum ψ h2 x, hΔ]
  · have hρc : Continuous ρ := HRS.Q66.q66_cont_of_smooth hρ.smooth
    have hac : Continuous a := HRS.Q66.q66_cont_of_smooth ha
    have hamem : MemHs (((d + 1 : ℕ)) : ℝ) (coeffOf a) :=
      memHs_of_isCk (d + 1) a (HRS.Q66.q66_isCk_of_smooth ha _)
    obtain ⟨hu1, hu2⟩ := hCp a hac hamem
    have hP := s7a_poisson_bound hψ hΔ (d + 1) hu1 j
    have hd1 : (((d + 1 : ℕ)) : ℝ) + 1 = (((d + 2 : ℕ)) : ℝ) := by push_cast; ring
    rw [hd1] at hP
    obtain ⟨hP1, hP2⟩ := hP
    obtain ⟨hv1, hv2⟩ := hCi (Torus.partialDeriv j ψ)
      (HRS.Q66.q66_cont_of_smooth (HRS.Q66.q66_isSmooth_partialDeriv hψ j)) hP1
    calc _ ≤ Ci * HRS.PDE.hsNorm (((d + 2 : ℕ)) : ℝ) (coeffOf (Torus.partialDeriv j ψ)) := hv2
      _ ≤ Ci * (Real.sqrt 2 * HRS.PDE.hsNorm (((d + 1 : ℕ)) : ℝ) (coeffOf fun x => ρ x * a x)) :=
          mul_le_mul_of_nonneg_left hP2 hCi0
      _ ≤ Ci * (Real.sqrt 2 * (Cp * HRS.PDE.hsNorm (((d + 1 : ℕ)) : ℝ) (coeffOf a))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hu2 (Real.sqrt_nonneg _)) hCi0
      _ = _ := by ring

end HRS.MC.Sec7.S7a

end

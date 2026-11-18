import HRS.Main.ThermLin2Mo6

/-!
# THERMLIN2 Mo7: the bound `E ⟨Zw^r,φ⟩² ≤ A ‖φ‖²_{H¹}` (helper for `tl2_Zw_moment`)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ThermLin.Plan2

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.T25P HRS.Uniform.Q54c HRS.Uniform.Q48c

variable {d : ℕ}

theorem tl2Mo7_int_exp {c r : ℝ} (hc : 0 < c) (hr : 0 ≤ r) :
    ∫ σ in Set.Icc (0 : ℝ) r, Real.exp (-(2 * c) * (r - σ)) ≤ 1 / (2 * c) := by
  have h2c : 0 < 2 * c := by linarith
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hr]
  have hd : ∀ x ∈ Set.uIcc (0 : ℝ) r, HasDerivAt (fun σ : ℝ => Real.exp (-(2 * c) * (r - σ)) / (2 * c))
      (Real.exp (-(2 * c) * (r - x))) x := by
    intro x _
    have h1 : HasDerivAt (fun σ : ℝ => r - σ) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub r
    have h2 := ((h1.const_mul (-(2 * c))).exp).div_const (2 * c)
    convert h2 using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun σ : ℝ => Real.exp (-(2 * c) * (r - σ))).intervalIntegrable _ _)]
  simp only [sub_zero, sub_self, mul_zero, Real.exp_zero]
  have : 0 < Real.exp (-(2 * c) * r) := Real.exp_pos _
  rw [div_sub_div_same, div_le_div_iff_of_pos_right h2c]
  linarith

/-- `‖lpFun 1 (realMode k)‖ = ⟨k⟩`. -/
theorem tl2Mo7_lp1_realMode (k : NonzeroLattice d) :
    ‖lpFun 1 (Torus.realMode k)‖ ^ 2 = Lattice.jp k.1 ^ 2 := by
  have hm : MemSobolev 1 (Torus.realMode k) :=
    HRS.PDE.MFSemigroup.memSobolev_of_isSmooth (HRS.Uniform.Q48b.q48b_isSmooth_realMode k) 1
  obtain ⟨-, hn⟩ := NegSobolev.coord_sq (lpFun 1 (Torus.realMode k))
  rw [hn, tsum_eq_single k]
  · rw [coord_lpFun hm]
    have : Torus.funRealCoeff (Torus.realMode k) k = 1 := by
      unfold Torus.funRealCoeff
      rw [Torus.realMode_orthonormal]; simp
    rw [this, Real.rpow_one]; ring
  · intro l hl
    rw [coord_lpFun hm]
    have : Torus.funRealCoeff (Torus.realMode k) l = 0 := by
      unfold Torus.funRealCoeff
      rw [Torus.realMode_orthonormal]
      simp [hl]
    rw [this]; ring

/-- The main moment bound. -/
theorem tl2Mo7_moment_bound (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) {m : ℝ} (hm : (d : ℝ) + 2 < m)
    {T' : ℝ} (hT' : 0 < T') {W : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m}
    (hdual : IsDualEvolution S.dyn (fun _ => ρβ) m W) (hplain : IsPlainEvolution W T')
    {K : ℝ} (hK : 0 ≤ K) (hKb : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T' → ‖W t r‖ ≤ K)
    {W₁ : ℝ → ℝ → NegSobolev d 1 →L[ℝ] NegSobolev d 1} (hW₁ : IsDualEvolution S.dyn (fun _ => ρβ) 1 W₁)
    {C₁ c₁ : ℝ} (hC₁ : 0 ≤ C₁) (hc₁ : 0 < c₁)
    (hdec₁ : ∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖W₁ t u‖ ≤ C₁ * Real.exp (-c₁ * (t - u)))
    {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : ∀ σ : ℝ, 0 ≤ σ → ∀ x, S.ρ σ x ≤ Λ)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    (G : ℝ → Ω → NegSobolev d m)
    (hG : IsHilbertMartingaleWithCovariation P ℱ T' G (fun r _ => covDensT m S.β⁻¹ T' S.ρ r))
    (hGc : ∀ ω, Continuous fun s => G s ω) (hGz : ∀ ω, G 0 ω = 0)
    (Zw : ℝ → Ω → NegSobolev d m)
    (hZw : ∀ t ∈ Set.Icc (0 : ℝ) T', IsStochConv P W (ContinuousLinearMap.id ℝ (NegSobolev d m)) G 0 t (Zw t))
    (hZm : ∀ t, Measurable (Zw t)) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T') {φ : Torus d → ℝ}
    (hφ : Torus.IsSmooth φ) :
    ∫⁻ ω, ENNReal.ofReal ((NegSobolev.eval (Zw r ω) φ) ^ 2) ∂P ≤
      ENNReal.ofReal (2 * S.β⁻¹ * Λ * C₁ ^ 2 / (2 * c₁) * ‖lpFun 1 φ‖ ^ 2) := by
  have hm' : (d : ℝ) / 2 + 2 < m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have htr := HRS.ThermLin.thermlin_stationary_traj S h
  have hq : 0 ≤ S.β⁻¹ := inv_nonneg.2 S.hβ.le
  rw [tl2Mo6_second_moment S h hm' hT' hdual hplain hK hKb P G hG hGc hGz Zw hZw hZm hr hφ]
  apply ENNReal.ofReal_le_ofReal
  set B : ℝ := 2 * S.β⁻¹ * Λ * C₁ ^ 2 * ‖lpFun 1 φ‖ ^ 2 with hB
  have hB0 : 0 ≤ B := by positivity
  have hpt : ∀ σ ∈ Set.Icc (0 : ℝ) r, 2 * S.β⁻¹ *
        ∫ x, inner ℝ (Torus.grad (propagator S.dyn (fun _ => ρβ) σ r φ) x)
          (Torus.grad (propagator S.dyn (fun _ => ρβ) σ r φ) x) * S.ρ σ x ≤
      B * Real.exp (-(2 * c₁) * (r - σ)) := by
    intro σ hσ
    have hKσ := hKb σ r hσ.1 hσ.2 hr.2
    have hmem := t25p_memSobolev_propagator S.hd htr hdual hK hσ.1 hσ.2 hKσ hφ
    have hck := adjkd_propagator_ck2 htr.dyn (fun _ => ρβ) hσ.1 hσ.2 φ
    have hcont : Continuous (propagator S.dyn (fun _ => ρβ) σ r φ) :=
      Torus.continuous_of_continuous_lift hck.continuous
    have hC1 : Torus.IsCk 1 (propagator S.dyn (fun _ => ρβ) σ r φ) := ContDiff.of_le hck (by norm_num)
    have hmem1 : MemSobolev 1 (propagator S.dyn (fun _ => ρβ) σ r φ) :=
      HRS.PDE.MFAdjoint.memSobolev_mono_idx hmem (by linarith)
    set ψ := propagator S.dyn (fun _ => ρβ) σ r φ with hψ
    have hgc : Continuous fun x => inner ℝ (Torus.grad ψ x) (Torus.grad ψ x) :=
      (HRS.PDE.MFLinear.continuous_grad hC1).inner (HRS.PDE.MFLinear.continuous_grad hC1)
    have hρc : Continuous (S.ρ σ) := tl2Mo_rho_continuous S hσ.1
    have hint : ∀ {f : Torus d → ℝ}, Continuous f → Integrable f (volume : Measure (Torus d)) := fun hf =>
      hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have h1 : ∫ x, inner ℝ (Torus.grad ψ x) (Torus.grad ψ x) * S.ρ σ x ≤
        ∫ x, inner ℝ (Torus.grad ψ x) (Torus.grad ψ x) * Λ := by
      refine integral_mono (hint (hgc.mul hρc)) (hint (hgc.mul continuous_const)) fun x => ?_
      exact mul_le_mul_of_nonneg_left (hΛ σ hσ.1 x) real_inner_self_nonneg
    rw [integral_mul_const] at h1
    have h2 := tl2Mo5_gradSq_le hm' hmem hcont hC1 hmem1
    have h3 := tl2Mo5_lp1_bound S h hW₁ hσ.1 hσ.2 hφ
    have h4 : ‖W₁ r σ‖ ≤ C₁ * Real.exp (-c₁ * (r - σ)) := hdec₁ σ r hσ.1 hσ.2
    have h5 : ‖lpFun 1 ψ‖ ≤ C₁ * Real.exp (-c₁ * (r - σ)) * ‖lpFun 1 φ‖ :=
      h3.trans (mul_le_mul_of_nonneg_right h4 (norm_nonneg _))
    have h6 : ‖lpFun 1 ψ‖ ^ 2 ≤ C₁ ^ 2 * Real.exp (-(2 * c₁) * (r - σ)) * ‖lpFun 1 φ‖ ^ 2 := by
      calc ‖lpFun 1 ψ‖ ^ 2 ≤ (C₁ * Real.exp (-c₁ * (r - σ)) * ‖lpFun 1 φ‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h5 2
        _ = C₁ ^ 2 * Real.exp (-(2 * c₁) * (r - σ)) * ‖lpFun 1 φ‖ ^ 2 := by
            rw [mul_pow, mul_pow, ← Real.exp_nat_mul]
            congr 3; push_cast; ring
    calc 2 * S.β⁻¹ * ∫ x, inner ℝ (Torus.grad ψ x) (Torus.grad ψ x) * S.ρ σ x
        ≤ 2 * S.β⁻¹ * ((∫ x, inner ℝ (Torus.grad ψ x) (Torus.grad ψ x)) * Λ) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ 2 * S.β⁻¹ * (‖lpFun 1 ψ‖ ^ 2 * Λ) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 hΛ0) (by positivity)
      _ ≤ 2 * S.β⁻¹ * ((C₁ ^ 2 * Real.exp (-(2 * c₁) * (r - σ)) * ‖lpFun 1 φ‖ ^ 2) * Λ) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h6 hΛ0) (by positivity)
      _ = B * Real.exp (-(2 * c₁) * (r - σ)) := by rw [hB]; ring
  have hgi : IntegrableOn (fun σ : ℝ => B * Real.exp (-(2 * c₁) * (r - σ))) (Set.Icc (0 : ℝ) r) :=
    (by fun_prop : Continuous fun σ : ℝ => B * Real.exp (-(2 * c₁) * (r - σ))).integrableOn_Icc
  calc ∫ σ in Set.Icc (0 : ℝ) r, 2 * S.β⁻¹ *
        ∫ x, inner ℝ (Torus.grad (propagator S.dyn (fun _ => ρβ) σ r φ) x)
          (Torus.grad (propagator S.dyn (fun _ => ρβ) σ r φ) x) * S.ρ σ x
      ≤ ∫ σ in Set.Icc (0 : ℝ) r, B * Real.exp (-(2 * c₁) * (r - σ)) := by
        refine integral_mono_of_nonneg ?_ hgi ?_
        · refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun σ hσ => ?_)
          refine mul_nonneg (by positivity) (integral_nonneg fun x => ?_)
          exact mul_nonneg real_inner_self_nonneg ((tl2Mo_rho_density S hσ.1).nonneg x)
        · exact (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun σ hσ => hpt σ hσ)
    _ = B * ∫ σ in Set.Icc (0 : ℝ) r, Real.exp (-(2 * c₁) * (r - σ)) := integral_const_mul _ _
    _ ≤ B * (1 / (2 * c₁)) := mul_le_mul_of_nonneg_left (tl2Mo7_int_exp hc₁ hr.1) hB0
    _ = 2 * S.β⁻¹ * Λ * C₁ ^ 2 / (2 * c₁) * ‖lpFun 1 φ‖ ^ 2 := by rw [hB]; ring

end HRS.ThermLin.Plan2

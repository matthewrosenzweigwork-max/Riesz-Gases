import HRS.MS.CritForceNF2
import HRS.MS.CritForceMom16

/-!
# S8.2 NormalForm, A02 stationarity lemma, part 2: removal of the cutoff

`∫ ρ (ν Δφ + b·∇φ) = 0` for a density with `ν ∇ρ = ρ b` and `φ` of class `C²` off the point `y`,
with the diagonal envelopes of `PairCorrector` (gradient `r^{1-s}`, Hessian `r^{-s}`, `s = d/2`).
The flux through the sphere of radius `ε` is `O(ε^{d-s})`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal ContDiff

namespace HRS.MS.S82P

open HRS HRS.Whole HRS.MS.S82N

variable {d : ℕ}

/-- A fixed `C¹` cutoff: `0` on the closed unit ball, `1` outside the ball of radius `2`. -/
lemma s82p_chi1_exists (d : ℕ) : ∃ χ : Euc d → ℝ, ContDiff ℝ 1 χ ∧ (∀ u, 0 ≤ χ u) ∧ (∀ u, χ u ≤ 1) ∧
    (∀ u, ‖u‖ ≤ 1 → χ u = 0) ∧ (∀ u, 2 ≤ ‖u‖ → χ u = 1) ∧ ∃ K : ℝ, ∀ u, ‖fderiv ℝ χ u‖ ≤ K := by
  let f : ContDiffBump (0 : Euc d) := ⟨1, 2, one_pos, one_lt_two⟩
  refine ⟨fun u => 1 - f u, contDiff_const.sub f.contDiff, fun u => ?_, fun u => ?_, fun u hu => ?_,
    fun u hu => ?_, ?_⟩
  · have := f.le_one (x := u); linarith
  · have := f.nonneg (x := u); linarith
  · have : f u = 1 := f.one_of_mem_closedBall (by simpa using hu)
    simp [this]
  · have : f u = 0 := f.zero_of_le_dist (by simpa [dist_zero_right] using hu)
    simp [this]
  · have hc : HasCompactSupport (fderiv ℝ (f : Euc d → ℝ)) := f.hasCompactSupport.fderiv ℝ
    have hcont : Continuous (fderiv ℝ (f : Euc d → ℝ)) := (f.contDiff (n := 1)).continuous_fderiv (by norm_num)
    obtain ⟨K, hK⟩ := hcont.bounded_above_of_compact_support hc
    refine ⟨K, fun u => ?_⟩
    have : fderiv ℝ (fun u => 1 - f u) u = -fderiv ℝ (f : Euc d → ℝ) u := by
      rw [fderiv_const_sub]
    rw [this, norm_neg]; exact hK u

/-- Scaling of the cutoff. -/
lemma s82p_chi_scaled {χ : Euc d → ℝ} (hχ : ContDiff ℝ 1 χ) {K : ℝ} (hK : ∀ u, ‖fderiv ℝ χ u‖ ≤ K)
    (y : Euc d) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ 1 (fun x => χ (ε⁻¹ • (x - y))) ∧
      ∀ x, ‖fderiv ℝ (fun x => χ (ε⁻¹ • (x - y))) x‖ ≤ K * ε⁻¹ := by
  have hg : ∀ x : Euc d, HasFDerivAt (fun x : Euc d => ε⁻¹ • (x - y))
      (ε⁻¹ • ContinuousLinearMap.id ℝ (Euc d)) x := fun x =>
    ((hasFDerivAt_id x).sub_const y).const_smul ε⁻¹
  refine ⟨hχ.comp ((contDiff_id.sub contDiff_const).const_smul ε⁻¹), fun x => ?_⟩
  have h2 := ((hχ.differentiable (by norm_num)) (ε⁻¹ • (x - y))).hasFDerivAt.comp x (hg x)
  have h2' : fderiv ℝ (fun x => χ (ε⁻¹ • (x - y))) x =
      (fderiv ℝ χ (ε⁻¹ • (x - y))).comp (ε⁻¹ • ContinuousLinearMap.id ℝ (Euc d)) := h2.fderiv
  rw [h2']
  calc ‖(fderiv ℝ χ (ε⁻¹ • (x - y))).comp (ε⁻¹ • ContinuousLinearMap.id ℝ (Euc d))‖
      ≤ ‖fderiv ℝ χ (ε⁻¹ • (x - y))‖ * ‖ε⁻¹ • ContinuousLinearMap.id ℝ (Euc d)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ K * ε⁻¹ := by
        have h3 : ‖ε⁻¹ • ContinuousLinearMap.id ℝ (Euc d)‖ ≤ ε⁻¹ := by
          rw [norm_smul, Real.norm_of_nonneg (inv_pos.2 hε).le]
          calc ε⁻¹ * ‖ContinuousLinearMap.id ℝ (Euc d)‖ ≤ ε⁻¹ * 1 := by
                gcongr; exact ContinuousLinearMap.norm_id_le
            _ = ε⁻¹ := mul_one _
        exact mul_le_mul (hK _) h3 (norm_nonneg _) ((norm_nonneg _).trans (hK 0))

/-- Integrability of `ρ g` from finiteness of the lintegral of `g` against `ρ dx`. -/
lemma s82p_integrable_of_lintegral {ρ g : Euc d → ℝ} (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hgm : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    (h : ∫⁻ x, ENNReal.ofReal (g x) ∂(HRS.Whole.withDensityReal ρ) < ⊤) :
    Integrable (fun x => ρ x * g x) := by
  refine ⟨(hρm.mul hgm).aestronglyMeasurable, ?_⟩
  have hρm' : Measurable (fun y : Euc d => ENNReal.ofReal (ρ y)) := ENNReal.measurable_ofReal.comp hρm
  have hgm' : Measurable (fun y : Euc d => ENNReal.ofReal (g y)) := ENNReal.measurable_ofReal.comp hgm
  unfold HasFiniteIntegral
  have : ∫⁻ x, ‖ρ x * g x‖ₑ = ∫⁻ x, ENNReal.ofReal (g x) ∂(HRS.Whole.withDensityReal ρ) := by
    unfold HRS.Whole.withDensityReal
    rw [lintegral_withDensity_eq_lintegral_mul _ hρm' hgm']
    refine lintegral_congr fun x => ?_
    rw [Real.enorm_eq_ofReal (mul_nonneg (hρ0 x) (hg0 x)), ENNReal.ofReal_mul (hρ0 x)]
    rfl
  rw [this]; exact h

lemma s82p_measurable_gradient (φ : Euc d → ℝ) : Measurable (gradient φ) := by
  have : Measurable fun x => (InnerProductSpace.toDual ℝ (Euc d)).symm (fderiv ℝ φ x) :=
    (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.measurable.comp (measurable_fderiv ℝ φ)
  exact this

lemma s82p_measurable_laplacian (φ : Euc d → ℝ) : Measurable (Laplacian.laplacian φ) := by
  have : Laplacian.laplacian φ = fun x => ∑ i, fderiv ℝ (fderiv ℝ φ) x
      ((stdOrthonormalBasis ℝ (Euc d)) i) ((stdOrthonormalBasis ℝ (Euc d)) i) := funext (s82p_laplacian_eq φ)
  rw [this]
  refine Finset.measurable_sum _ fun i _ => ?_
  exact ((measurable_fderiv ℝ (fderiv ℝ φ)).apply_continuousLinearMap _).apply_continuousLinearMap _

lemma s82p_pow_inv (ε : ℝ) (hε : 0 < ε) (d : ℕ) (hd : 1 ≤ d) : ε ^ d * ε⁻¹ = ε ^ (d - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  simp [pow_succ]
  field_simp

lemma s82p_pow_rpow (ε : ℝ) (hε : 0 < ε) (d : ℕ) (hd : 1 ≤ d) (s : ℝ) :
    ε ^ (d - 1) * ε ^ (1 - s) = ε ^ ((d : ℝ) - s) := by
  rw [← Real.rpow_natCast, ← Real.rpow_add hε]
  congr 1
  rw [Nat.cast_sub hd]; push_cast; ring

lemma s82p_flux_tendsto (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (hsd : s < d) (D : ℝ) :
    Tendsto (fun ε : ℝ => D * (ε ^ d * ε⁻¹ * (1 + ε ^ (1 - s)))) (𝓝[>] 0) (𝓝 0) := by
  have h1 : Tendsto (fun ε : ℝ => ε ^ (d - 1)) (𝓝[>] 0) (𝓝 0) := by
    have := ((continuous_pow (d - 1)).tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa [zero_pow (by omega : d - 1 ≠ 0)] using this
  have h2 : Tendsto (fun ε : ℝ => ε ^ ((d : ℝ) - s)) (𝓝[>] 0) (𝓝 0) := by
    have := ((Real.continuousAt_rpow_const (0 : ℝ) ((d : ℝ) - s) (Or.inr (by linarith))).tendsto).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa [Real.zero_rpow (by linarith : (d : ℝ) - s ≠ 0)] using this
  have h3 := (h1.add h2).const_mul D
  rw [add_zero, mul_zero] at h3
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : (0 : ℝ) < ε := hε
  have e : ε ^ d * ε⁻¹ * (1 + ε ^ (1 - s)) = ε ^ (d - 1) + ε ^ ((d : ℝ) - s) := by
    rw [s82p_pow_inv ε hε' d (by omega), mul_add, mul_one, s82p_pow_rpow ε hε' d (by omega)]
  rw [e]

/-- **Stationarity against the diagonal singularity.** -/
theorem s82p_stationary (hd : 2 ≤ d) {ν : ℝ} (hν : 0 < ν) {ρ : Euc d → ℝ}
    (hρp : HRS.Whole.IsProbDensity ρ) (hρ : ContDiff ℝ 1 ρ) {G c : ℝ} (hG : 0 < G)
    (hGauss : HRS.Whole.HasR2GaussianUpper G c ρ)
    {b : Euc d → Euc d} (hbm : Measurable b) (hbρ : ∀ x, ν • gradient ρ x = ρ x • b x)
    {c0 : ℝ} (hc0 : 0 ≤ c0) (hb : ∀ x, ‖b x‖ ≤ c0 * (1 + ‖x‖))
    (y : Euc d) {φ : Euc d → ℝ} (hφ : ContDiffOn ℝ 2 φ {x | x ≠ y}) {A M : ℝ} (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hg : ∀ x, x ≠ y → ‖gradient φ x‖ ≤
      A * jbracket x ^ M * (1 + s82n_smallRadius x y ^ (1 - s82n_critS d)))
    (hH : ∀ x, x ≠ y → ‖fderiv ℝ (fderiv ℝ φ) x‖ ≤ A * jbracket x ^ M * s82n_pole x y) :
    Integrable (fun x => ρ x * (ν * Laplacian.laplacian φ x + inner ℝ (b x) (gradient φ x))) ∧
    ∫ x, ρ x * (ν * Laplacian.laplacian φ x + inner ℝ (b x) (gradient φ x)) = 0 := by
  have hs := s82n_critS_pos (by omega : 1 ≤ d)
  have hs1 := s82n_critS_ge_one hd
  have hdr : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s82n_critS d < d := by unfold s82n_critS; linarith
  haveI : Nontrivial (Euc d) := by
    haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
    infer_instance
  have hρ0 := hρp.nonneg
  have hρG : ∀ x, ρ x ≤ G := fun x => by
    refine (hGauss.2 x).trans ?_
    have : Real.exp (-c * ‖x‖ ^ 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg ‖x‖, hGauss.1]
    nlinarith
  have hjb0 : ∀ x : Euc d, 0 ≤ jbracket x := fun x => (s82n_jb_pos x).le
  have hjbM : ∀ (e : ℝ) (x : Euc d), 0 ≤ jbracket x ^ e := fun e x => Real.rpow_nonneg (hjb0 x) e
  have hjbM1 : ∀ x : Euc d, jbracket x ^ M ≤ jbracket x ^ (M + 1) := fun x =>
    Real.rpow_le_rpow_of_exponent_le (s82n_jb_one_le x) (by linarith)
  have hpole1 : ∀ x : Euc d, 1 ≤ s82n_pole y x := fun x => s82p_pole_ge_one y x
  have hsr1 : ∀ x : Euc d, 1 ≤ 1 + s82n_smallRadius y x ^ (1 - s82n_critS d) := fun x => by
    have := Real.rpow_nonneg (s82p_smallRadius_nonneg y x) (1 - s82n_critS d); linarith
  have hsym : ∀ x : Euc d, s82n_smallRadius x y = s82n_smallRadius y x := fun x =>
    s82p_smallRadius_symm y x
  have hpsym : ∀ x : Euc d, s82n_pole x y = s82n_pole y x := fun x => s82p_pole_symm y x
  -- the integrable envelope
  set g0 : Euc d → ℝ := fun x => jbracket x ^ (M + 1) *
    ((1 + s82n_smallRadius y x ^ (1 - s82n_critS d)) * s82n_pole y x) with hg0def
  have hg0m : Measurable g0 := by
    have := s82n_measurable_smallRadius y
    refine Measurable.mul (Measurable.pow_const (by unfold jbracket; fun_prop) _) ?_
    unfold s82n_pole; fun_prop
  have hg0nn : ∀ x, 0 ≤ g0 x := fun x =>
    mul_nonneg (hjbM _ x) (mul_nonneg (by linarith [hsr1 x]) (by linarith [hpole1 x]))
  have hΨ0int : Integrable (fun x => ρ x * g0 x) := by
    refine s82p_integrable_of_lintegral hρp.measurable hρ0 hg0m hg0nn ?_
    exact lt_of_le_of_lt (s82n_E2 hd (M + 1) G c 1 (by linarith) hG.le hGauss.1 one_pos le_rfl ρ hρp
      hGauss y) ENNReal.ofReal_lt_top
  set Ψ0 : Euc d → ℝ := fun x => ρ x * g0 x with hΨ0def
  set κ : ℝ := A * (1 + 2 * c0) with hκ
  have hκ0 : 0 ≤ κ := mul_nonneg hA (by linarith)
  set Ψ : Euc d → ℝ := fun x => κ * Ψ0 x with hΨdef
  have hΨint : Integrable Ψ := hΨ0int.const_mul κ
  have hΨnn : ∀ x, 0 ≤ Ψ x := fun x => mul_nonneg hκ0 (mul_nonneg (hρ0 x) (hg0nn x))
  -- envelope inequalities
  have hsr0 : ∀ x : Euc d, 0 ≤ 1 + s82n_smallRadius y x ^ (1 - s82n_critS d) := fun x => by
    linarith [hsr1 x]
  have hp0 : ∀ x : Euc d, 0 ≤ s82n_pole y x := fun x => by linarith [hpole1 x]
  have hgC : ∀ x, jbracket x ^ (M + 1) * (1 + s82n_smallRadius y x ^ (1 - s82n_critS d)) ≤ g0 x := by
    intro x
    show _ ≤ jbracket x ^ (M + 1) * _
    exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (hsr0 x) (hpole1 x)) (hjbM _ x)
  have hgA : ∀ x, jbracket x ^ M * (1 + s82n_smallRadius y x ^ (1 - s82n_critS d)) ≤ g0 x := fun x =>
    (mul_le_mul_of_nonneg_right (hjbM1 x) (hsr0 x)).trans (hgC x)
  have hgB : ∀ x, jbracket x ^ M * s82n_pole y x ≤ g0 x := by
    intro x
    refine (mul_le_mul_of_nonneg_right (hjbM1 x) (hp0 x)).trans ?_
    show _ ≤ jbracket x ^ (M + 1) * _
    exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (hp0 x) (hsr1 x)) (hjbM _ x)
  have hκA : A ≤ κ := by rw [hκ]; nlinarith
  have hκ2 : 2 * c0 * A ≤ κ := by rw [hκ]; nlinarith
  have hE1 : ∀ x, x ≠ y → ρ x * ‖gradient φ x‖ ≤ Ψ x := by
    intro x hx
    have h1 := hg x hx
    rw [hsym] at h1
    have h2 : ‖gradient φ x‖ ≤ A * g0 x :=
      h1.trans (by have := hgA x; nlinarith [mul_le_mul_of_nonneg_left (hgA x) hA])
    have h3 := mul_nonneg (hρ0 x) (hg0nn x)
    calc ρ x * ‖gradient φ x‖ ≤ ρ x * (A * g0 x) := mul_le_mul_of_nonneg_left h2 (hρ0 x)
      _ ≤ κ * (ρ x * g0 x) := by nlinarith
  have hE3 : ∀ x, x ≠ y → ρ x * ‖fderiv ℝ (fderiv ℝ φ) x‖ ≤ Ψ x := by
    intro x hx
    have h1 := hH x hx
    rw [hpsym] at h1
    have h2 : ‖fderiv ℝ (fderiv ℝ φ) x‖ ≤ A * g0 x :=
      h1.trans (by nlinarith [mul_le_mul_of_nonneg_left (hgB x) hA])
    have h3 := mul_nonneg (hρ0 x) (hg0nn x)
    calc ρ x * ‖fderiv ℝ (fderiv ℝ φ) x‖ ≤ ρ x * (A * g0 x) := mul_le_mul_of_nonneg_left h2 (hρ0 x)
      _ ≤ κ * (ρ x * g0 x) := by nlinarith
  have hE2 : ∀ x, x ≠ y → ρ x * ‖b x‖ * ‖gradient φ x‖ ≤ Ψ x := by
    intro x hx
    have h1 := hg x hx
    rw [hsym] at h1
    have hbx : ‖b x‖ ≤ 2 * c0 * jbracket x := by
      refine (hb x).trans ?_
      have : 1 + ‖x‖ ≤ 2 * jbracket x := by
        have := s82n_jb_sq x
        nlinarith [s82n_jb_pos x, norm_nonneg x, sq_nonneg (1 - ‖x‖)]
      nlinarith
    have hjj : jbracket x * jbracket x ^ M = jbracket x ^ (M + 1) := by
      rw [Real.rpow_add (s82n_jb_pos x), Real.rpow_one]; ring
    have hgx : ‖gradient φ x‖ ≤ A * (jbracket x ^ M * (1 + s82n_smallRadius y x ^ (1 - s82n_critS d))) := by
      calc _ ≤ _ := h1
        _ = _ := by ring
    have h4 : 0 ≤ ρ x * (2 * c0 * jbracket x) :=
      mul_nonneg (hρ0 x) (mul_nonneg (mul_nonneg (by norm_num) hc0) (hjb0 x))
    have h5 : ρ x * ‖b x‖ * ‖gradient φ x‖ ≤
        ρ x * (2 * c0 * jbracket x) * (A * (jbracket x ^ M * (1 + s82n_smallRadius y x ^ (1 - s82n_critS d)))) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hbx (hρ0 x)) hgx (norm_nonneg _) h4
    have h6 : ρ x * (2 * c0 * jbracket x) * (A * (jbracket x ^ M * (1 + s82n_smallRadius y x ^ (1 - s82n_critS d)))) =
        (2 * c0 * A) * (ρ x * (jbracket x ^ (M + 1) * (1 + s82n_smallRadius y x ^ (1 - s82n_critS d)))) := by
      rw [← hjj]; ring
    have h7 : ρ x * (jbracket x ^ (M + 1) * (1 + s82n_smallRadius y x ^ (1 - s82n_critS d))) ≤ ρ x * g0 x :=
      mul_le_mul_of_nonneg_left (hgC x) (hρ0 x)
    have h8 : 0 ≤ 2 * c0 * A := by positivity
    have h9 := mul_nonneg (hρ0 x) (hg0nn x)
    calc ρ x * ‖b x‖ * ‖gradient φ x‖ ≤ _ := h5
      _ = _ := h6
      _ ≤ (2 * c0 * A) * (ρ x * g0 x) := mul_le_mul_of_nonneg_left h7 h8
      _ ≤ κ * (ρ x * g0 x) := by nlinarith
  -- the measurable integrand and its bound
  set bs := stdOrthonormalBasis ℝ (Euc d) with hbs
  set f : Euc d → ℝ := fun x => ρ x * (ν * Laplacian.laplacian φ x + inner ℝ (b x) (gradient φ x))
    with hfdef
  have hfm : Measurable f :=
    hρp.measurable.mul ((measurable_const.mul (s82p_measurable_laplacian φ)).add
      (Measurable.inner hbm (s82p_measurable_gradient φ)))
  haveI : NullSingletonClass (volume : Measure (Euc d)) := inferInstance
  have hae : ∀ᵐ x ∂(volume : Measure (Euc d)), x ≠ y := Measure.ae_ne volume y
  have hfb : ∀ x, x ≠ y → |f x| ≤ (ν * d + 1) * Ψ x := by
    intro x hx
    have hlap : |Laplacian.laplacian φ x| ≤ d * ‖fderiv ℝ (fderiv ℝ φ) x‖ := by
      rw [s82p_laplacian_eq]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_card_nsmul _ _ ‖fderiv ℝ (fderiv ℝ φ) x‖ fun i _ => ?_).trans ?_
      · have h3 := (fderiv ℝ (fderiv ℝ φ) x).le_opNorm₂ (bs i) (bs i)
        rw [bs.norm_eq_one i, mul_one, mul_one] at h3
        rwa [← Real.norm_eq_abs]
      · simp [nsmul_eq_mul]
    have hin : |inner ℝ (b x) (gradient φ x)| ≤ ‖b x‖ * ‖gradient φ x‖ := abs_real_inner_le_norm _ _
    have h1 := hE1 x hx
    have h2 := hE2 x hx
    have h3 := hE3 x hx
    have hρx := hρ0 x
    calc |f x| = ρ x * |ν * Laplacian.laplacian φ x + inner ℝ (b x) (gradient φ x)| := by
          show |ρ x * _| = _
          rw [abs_mul, abs_of_nonneg hρx]
      _ ≤ ρ x * (ν * (d * ‖fderiv ℝ (fderiv ℝ φ) x‖) + ‖b x‖ * ‖gradient φ x‖) := by
          gcongr
          refine (abs_add_le _ _).trans (add_le_add ?_ hin)
          rw [abs_mul, abs_of_pos hν]
          exact mul_le_mul_of_nonneg_left hlap hν.le
      _ = ν * d * (ρ x * ‖fderiv ℝ (fderiv ℝ φ) x‖) + ρ x * ‖b x‖ * ‖gradient φ x‖ := by ring
      _ ≤ ν * d * Ψ x + Ψ x := by gcongr
      _ = _ := by ring
  have hfint : Integrable f :=
    (hΨint.const_mul (ν * d + 1)).mono' hfm.aestronglyMeasurable
      (hae.mono fun x hx => by rw [Real.norm_eq_abs]; exact hfb x hx)
  -- the cutoff family
  obtain ⟨χ1, hχ1c, hχ1n, hχ1u, hχ1z, hχ1o, K1, hK1⟩ := s82p_chi1_exists d
  have hK10 : 0 ≤ K1 := (norm_nonneg _).trans (hK1 0)
  set χe : ℝ → Euc d → ℝ := fun ε x => χ1 (ε⁻¹ • (x - y)) with hχe
  have hχe_norm : ∀ ε x, 0 < ε → ‖ε⁻¹ • (x - y)‖ = ε⁻¹ * ‖x - y‖ := by
    intro ε x hε; rw [norm_smul, Real.norm_of_nonneg (inv_pos.2 hε).le]
  have hχe0 : ∀ ε x, 0 < ε → ‖x - y‖ ≤ ε → χe ε x = 0 := by
    intro ε x hε hx
    apply hχ1z
    rw [hχe_norm ε x hε]
    calc ε⁻¹ * ‖x - y‖ ≤ ε⁻¹ * ε := by gcongr
      _ = 1 := inv_mul_cancel₀ hε.ne'
  have hχe1 : ∀ ε x, 0 < ε → 2 * ε ≤ ‖x - y‖ → χe ε x = 1 := by
    intro ε x hε hx
    apply hχ1o
    rw [hχe_norm ε x hε]
    calc (2 : ℝ) = ε⁻¹ * (2 * ε) := by field_simp
      _ ≤ ε⁻¹ * ‖x - y‖ := by gcongr
  have hdχe0 : ∀ ε x, 0 < ε → ‖x - y‖ < ε → fderiv ℝ (χe ε) x = 0 := by
    intro ε x hε hx
    have hev : χe ε =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      have : {z : Euc d | ‖z - y‖ < ε} ∈ 𝓝 x :=
        (isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const))
          continuous_const).mem_nhds hx
      filter_upwards [this] with z hz using hχe0 ε z hε hz.le
    rw [hev.fderiv_eq]; simp
  have hdχe2 : ∀ ε x, 0 < ε → 2 * ε < ‖x - y‖ → fderiv ℝ (χe ε) x = 0 := by
    intro ε x hε hx
    have hev : χe ε =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      have : {z : Euc d | 2 * ε < ‖z - y‖} ∈ 𝓝 x :=
        (isOpen_lt continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))).mem_nhds hx
      filter_upwards [this] with z hz using hχe1 ε z hε hz.le
    rw [hev.fderiv_eq]; simp
  -- identity for each cutoff
  have hid : ∀ ε, 0 < ε → ∫ x, χe ε x * f x =
      -ν * ∫ x, ∑ i, fderiv ℝ (χe ε) x (bs i) * (ρ x * fderiv ℝ φ x (bs i)) := by
    intro ε hε
    obtain ⟨hc, hKe⟩ := s82p_chi_scaled hχ1c hK1 y hε
    have := (s82p_ibp_cut hν hρ (b := b) hbρ y hφ (χ := χe ε) hc (fun x => hχ1n _) (fun x => hχ1u _) hε
      (fun x hx => hχe0 ε x hε hx.le) (Kχ := K1 * ε⁻¹) hKe hΨint hΨnn hE1 hE2 hE3 hρ0).2
    rw [← this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hfdef]; ring
  -- the flux bound
  set V : ℝ := (volume : Measure (Euc d)).real (Metric.ball (0 : Euc d) 1) with hV
  have hV0 : 0 ≤ V := measureReal_nonneg
  set D : ℝ := d * K1 * G * A * 4 ^ M * jbracket y ^ M * 2 ^ d * V with hD
  have hD0 : 0 ≤ D := by
    have := hjbM M y
    positivity
  have hflux : ∀ ε, 0 < ε → ε ≤ 1 / 2 →
      ‖∫ x, ∑ i, fderiv ℝ (χe ε) x (bs i) * (ρ x * fderiv ℝ φ x (bs i))‖ ≤
        D * (ε ^ d * ε⁻¹ * (1 + ε ^ (1 - s82n_critS d))) := by
    intro ε hε hε2
    obtain ⟨hc, hKe⟩ := s82p_chi_scaled hχ1c hK1 y hε
    set Cε : ℝ := d * (K1 * ε⁻¹) * (G * (A * (4 ^ M * jbracket y ^ M * (1 + ε ^ (1 - s82n_critS d)))))
      with hCε
    have hεs : 0 ≤ ε ^ (1 - s82n_critS d) := Real.rpow_nonneg hε.le _
    have hK1ε : 0 ≤ K1 * ε⁻¹ := mul_nonneg hK10 (inv_pos.2 hε).le
    have hCε0 : 0 ≤ Cε := by
      have := hjbM M y
      positivity
    have hpt : ∀ x, |∑ i, fderiv ℝ (χe ε) x (bs i) * (ρ x * fderiv ℝ φ x (bs i))| ≤
        (Metric.closedBall y (2 * ε)).indicator (fun _ => Cε) x := by
      intro x
      by_cases hx : x ∈ Metric.closedBall y (2 * ε)
      · rw [Set.indicator_of_mem hx]
        have hx2 : ‖x - y‖ ≤ 2 * ε := by
          rw [Metric.mem_closedBall, dist_eq_norm] at hx; exact hx
        by_cases hxe : ‖x - y‖ < ε
        · simp [hdχe0 ε x hε hxe, hCε0]
        · push_neg at hxe
          have hxy : x ≠ y := by
            intro h; rw [h, sub_self, norm_zero] at hxe; linarith
          have hcoordχ : ∀ i : Fin (Module.finrank ℝ (Euc d)), |fderiv ℝ (χe ε) x (bs i)| ≤ K1 * ε⁻¹ := fun i => by
            have h3 := (fderiv ℝ (χe ε) x).le_opNorm (bs i)
            rw [bs.norm_eq_one i, mul_one] at h3
            rw [← Real.norm_eq_abs]; exact h3.trans (hKe x)
          have hcoordφ : ∀ i : Fin (Module.finrank ℝ (Euc d)), |fderiv ℝ φ x (bs i)| ≤ ‖gradient φ x‖ := fun i => by
            rw [← HRS.MS.PoisKolm.kl_inner_gradient]
            have := abs_real_inner_le_norm (bs i) (gradient φ x)
            rwa [bs.norm_eq_one i, one_mul] at this
          have hgx := hg x hxy
          have hsr : s82n_smallRadius x y = ‖x - y‖ := min_eq_right (by linarith)
          rw [hsr] at hgx
          have hpow : ‖x - y‖ ^ (1 - s82n_critS d) ≤ ε ^ (1 - s82n_critS d) := by
            have e : 1 - s82n_critS d = -(s82n_critS d - 1) := by ring
            rw [e]; exact s82n_rpow_neg_anti _ ε _ (by linarith) hε hxe
          have hjx : jbracket x ^ M ≤ 4 ^ M * jbracket y ^ M :=
            s82n_jb_rpow_near M hM y x (by rw [norm_sub_rev]; linarith)
          have hφb : ρ x * ‖gradient φ x‖ ≤ G * (A * (4 ^ M * jbracket y ^ M * (1 + ε ^ (1 - s82n_critS d)))) := by
            calc ρ x * ‖gradient φ x‖ ≤ G * (A * jbracket x ^ M * (1 + ‖x - y‖ ^ (1 - s82n_critS d))) :=
                  mul_le_mul (hρG x) hgx (norm_nonneg _) hG.le
              _ ≤ G * (A * (4 ^ M * jbracket y ^ M) * (1 + ε ^ (1 - s82n_critS d))) := by
                  refine mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul_of_nonneg_left hjx hA)
                    (by linarith [hpow]) (by linarith [Real.rpow_nonneg (norm_nonneg (x - y)) (1 - s82n_critS d)])
                    (mul_nonneg hA (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hjbM M y)))) hG.le
              _ = _ := by ring
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          refine (Finset.sum_le_card_nsmul _ _ ((K1 * ε⁻¹) * (G * (A * (4 ^ M * jbracket y ^ M *
            (1 + ε ^ (1 - s82n_critS d)))))) fun i _ => ?_).trans ?_
          · rw [abs_mul, abs_mul, abs_of_nonneg (hρ0 x)]
            calc |fderiv ℝ (χe ε) x (bs i)| * (ρ x * |fderiv ℝ φ x (bs i)|)
                ≤ (K1 * ε⁻¹) * (ρ x * ‖gradient φ x‖) := by
                  exact mul_le_mul (hcoordχ i) (mul_le_mul_of_nonneg_left (hcoordφ i) (hρ0 x))
                    (mul_nonneg (hρ0 x) (abs_nonneg _)) hK1ε
              _ ≤ _ := mul_le_mul_of_nonneg_left hφb hK1ε
          · simp only [Finset.card_univ, Fintype.card_fin, finrank_euclideanSpace_fin, nsmul_eq_mul]
            rw [hCε]; exact le_of_eq (by ring)
      · rw [Set.indicator_of_notMem hx]
        have hx2 : 2 * ε < ‖x - y‖ := by
          rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hx; exact hx
        simp [hdχe2 ε x hε hx2]
    have hBint : Integrable ((Metric.closedBall y (2 * ε)).indicator (fun _ => Cε)) := by
      rw [integrable_indicator_iff Metric.isClosed_closedBall.measurableSet]
      exact integrableOn_const (measure_closedBall_lt_top.ne)
    refine (norm_integral_le_of_norm_le hBint (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hpt x)).trans ?_
    rw [integral_indicator_const _ Metric.isClosed_closedBall.measurableSet,
      smul_eq_mul]
    rw [Measure.addHaar_real_closedBall volume y (by positivity), finrank_euclideanSpace_fin]
    have : D * (ε ^ d * ε⁻¹ * (1 + ε ^ (1 - s82n_critS d))) =
        (2 * ε) ^ d * V * Cε := by
      rw [hD, hCε, mul_pow]; ring
    rw [this]
  have hconv : Tendsto (fun ε : ℝ => ∫ x, χe ε x * f x) (𝓝[>] 0) (𝓝 (∫ x, f x)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖f x‖) ?_ ?_ hfint.norm ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε' : (0 : ℝ) < ε := hε
      obtain ⟨hc, _⟩ := s82p_chi_scaled hχ1c hK1 y hε'
      exact (hc.continuous.measurable.mul hfm).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      refine Filter.Eventually.of_forall fun x => ?_
      rw [norm_mul, Real.norm_of_nonneg (hχ1n _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (hχ1u _)
    · filter_upwards [hae] with x hx
      have hpos : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hx)
      have : ∀ᶠ ε in 𝓝[>] (0 : ℝ), χe ε x * f x = f x := by
        filter_upwards [Ioo_mem_nhdsGT (half_pos hpos)] with ε hε
        rw [hχe1 ε x hε.1 (by linarith [hε.2]), one_mul]
      exact tendsto_const_nhds.congr' (this.mono fun ε h => h.symm)
  have hzero : Tendsto (fun ε : ℝ => ∫ x, χe ε x * f x) (𝓝[>] 0) (𝓝 0) := by
    have hR := (s82p_flux_tendsto d hd (s82n_critS d) hsd D).const_mul ν
    rw [mul_zero] at hR
    refine squeeze_zero_norm' ?_ hR
    filter_upwards [Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with ε hε
    rw [hid ε hε.1, norm_mul, norm_neg, Real.norm_of_nonneg hν.le]
    exact mul_le_mul_of_nonneg_left (hflux ε hε.1 hε.2) hν.le
  exact ⟨hfint, tendsto_nhds_unique hconv hzero⟩

end HRS.MS.S82P

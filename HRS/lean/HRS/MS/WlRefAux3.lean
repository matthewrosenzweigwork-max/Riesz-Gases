import HRS.MS.WlRefAux2

/-!
# HRS.MS.WlRefAux3 -- calibrated reference marginal for S3.5, part 3: the `L²` bound (WL-9b)

Packet WL-9b of `docs/WR_LOG_PLAN.md` (Step 11 of the proof of `r2_log_static`, TeX eq. `r2-log-reference-marginal`).
Infrastructure lemmas, not manuscript rows.  Namespace `HRS.MS.Wl`, helper prefix `wl9_`.  Port of `WrRefMargAux3`
(`wr13e_core_L2`, `wr13e_field_small_eps`, `wr13e_reference_marginal_density_L2`) to the logarithmic kernel, in the
style of `wl_marginal_L2` (`WlMargAux2`).

Main statements.
* `wl_ref_density_le` (sup bound): for every head index `M ≥ 1` there are `N₀, C` (before `ρ, β, N`) such that for all
  `N ≥ N₀`: `|⟪t_N, Ξ⟫| ≤ 1` and the first marginal of the calibrated reference `R_N = wl9_RN` is
  `π^R_N = μ.withDensity θ` with `0 ≤ θ ≤ C` (uniformly in `ρ`, `β ∈ (0, βp]`, `N`).
* `wl_ref_marginal_L2` (**TeX `eq:r2-log-reference-marginal`**): there is `M₀` such that for every `M ≥ M₀` there
  are `N₀, C` with `‖dπ^R_N/dμ - 1‖_{L²(μ)} ≤ C/N` for all `N ≥ N₀`, together with the density bound `θ ≤ C`, the
  calibration bound `|⟪t_N, Ξ⟫| ≤ 1` and the calibration identity `⟪t_N, Ξ x⟫ = -β (k_M(θ - 1))(x) + c₀`.
  The quantifier order `∃ M₀, ∀ M ≥ M₀, ∃ N₀ C, ∀ ρ β N V` is the one of `wl_second_moment`: the head index `M`
  must be large (Dobrushin smallness `β C_q M^{-d/2}` against the field constants `e^{O(1)}`), `N₀` depends on `M`.
  `V` is any weak potential with `V.q = q_M`; `R_N` is the weak ensemble of the field `ψ_R = ψ0 + ⟪t_N, Ξ⟫`.

Proof (as in `wl_marginal_L2`): the exact cavity equation `wl9_cavity_equation` (WlRefAux1), the defect bound
`wl9_defect`, the cavity TV `wl9_cavity_tv` (the calibration field held fixed), the Minkowski bounds `wl9_cv_L2`,
the positivity `wl8_K_psd` of `K` on `L²_0(μ)` and the absorption `wr13e_L2_assemble`.
Adjustment with respect to the plan (documented, harmless): the cavity ensemble is the `(N-1)`-particle ensemble with the
same field `ψ_R` (this is what "keeping this field fixed" means); no uniform-in-`x` statement is made (it is false
for the log kernel).
-/

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wl

open HRS.Whole HRS.MS.Wr HRS.External

variable {d : ℕ}

/-! ### Elementary facts -/

lemma wl9_qm_le_K (M : ℕ) (x y : Euc d) : wl_qm M x y ≤ sphericalLogKernel x y := by
  by_cases hxy : x = y
  · subst hxy
    rw [wl_qm_diag]
    exact HRS.MS.Comm.comm_log_nonneg x x
  · rw [wl_K_eq M hxy]
    linarith [wl_km_nonneg (d := d) M x y]

lemma wl9_lintegral_sq_q (M : ℕ) {μ : Measure (Euc d)} {C2 : ℝ} (x : Euc d)
    (hi : Integrable (fun y => sphericalLogKernel x y ^ 2) μ)
    (hle : ∫ y, sphericalLogKernel x y ^ 2 ∂μ ≤ C2) :
    ∫⁻ y, ‖wl_qm M y x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal C2 := by
  refine le_trans (lintegral_mono fun y => ?_) (wl7_lintegral_sq_K x hi hle)
  rw [wl_qm_symm]
  refine pow_le_pow_left' ?_ 2
  rw [Real.enorm_of_nonneg (wl_qm_nonneg M x y), Real.enorm_of_nonneg (HRS.MS.Comm.comm_log_nonneg x y)]
  exact ENNReal.ofReal_le_ofReal (wl9_qm_le_K M x y)

/-- The smallness of the head: `β_p C_q M^{-d/2}` is below any positive threshold for large `M`. -/
lemma wl9_head (hd : 1 ≤ d) (Cq βp Mf M1f : ℝ) : ∃ M0 : ℕ, 1 ≤ M0 ∧ ∀ M : ℕ, M0 ≤ M →
    βp * (Cq * (M : ℝ) ^ (-((d : ℝ) / 2))) ≤ min 1 (1 / (16 * Real.exp (Mf + M1f + 1))) := by
  have hδ : 0 < min 1 (1 / (16 * Real.exp (Mf + M1f + 1))) :=
    lt_min one_pos (by positivity)
  obtain ⟨M0, hM0, h⟩ := wl_exists_head hd (βp * Cq) hδ
  refine ⟨M0, hM0, fun M hM => ?_⟩
  have := h M hM
  rwa [mul_assoc] at this

/-- Monotonicity of the Dobrushin smallness in the field constants. -/
lemma wl9_hs_mono {x M1 M2 Mf M1f : ℝ} (hM : M1 ≤ Mf) (hM2 : M2 ≤ M1f)
    (hs : x ≤ min 1 (1 / (16 * Real.exp (Mf + M1f + 1)))) :
    x ≤ min 1 (1 / (16 * Real.exp (M1 + M2 + 1))) := by
  refine le_min (hs.trans (min_le_left _ _)) (hs.trans ((min_le_right _ _).trans ?_))
  refine one_div_le_one_div_of_le (by positivity) ?_
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) (by norm_num)

/-- The first marginal of the cavity ensemble (`m + 1` particles) is dominated by `e^{M₁ + λ m a} e^{M} μ`. -/
lemma wl9_cav_marg_le {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ]
    (V : WeakPotential μ) {ψ : E → ℝ} {M M₁ lam a : ℝ} (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam)
    (hrow : ∀ x, ∫ y, V.q x y ∂μ ≤ a) (m : ℕ) :
    (fieldLaw V ψ lam (m + 1)).map (fun X => X 0) ≤
      ENNReal.ofReal (Real.exp (M₁ + lam * m * a) * Real.exp M) • μ := by
  have h1 := wl6_one_le V hψ hlam hrow m
  have h2 : μ.withDensity (fun x => ENNReal.ofReal (Real.exp (ψ x))) ≤
      ENNReal.ofReal (Real.exp M) • μ := by
    refine Measure.le_iff.2 fun A hA => ?_
    rw [withDensity_apply _ hA, Measure.smul_apply, smul_eq_mul, ← setLIntegral_const]
    exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (hψ.le x))
  refine wl6_le_smul_trans h1 h2 (le_of_eq (ENNReal.ofReal_mul (Real.exp_pos _).le).symm)

/-- `ν ≤ ofReal C • μ` from a pointwise bound of the density. -/
lemma wl9_withDensity_le {E : Type*} [MeasurableSpace E] {μ : Measure E} {θ : E → ℝ} {C : ℝ}
    (h : ∀ x, θ x ≤ C) : μ.withDensity (fun x => ENNReal.ofReal (θ x)) ≤ ENNReal.ofReal C • μ := by
  refine Measure.le_iff.2 fun A hA => ?_
  rw [withDensity_apply _ hA, Measure.smul_apply, smul_eq_mul, ← setLIntegral_const]
  exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal (h x)

/-- `tvDist` is bounded by a bound on all events. -/
lemma wl9_tvDist_le {E : Type*} [MeasurableSpace E] {P Q : Measure E} {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ S : Set E, MeasurableSet S → |P.real S - Q.real S| ≤ ε) : tvDist P Q ≤ ε := by
  unfold tvDist
  exact Real.iSup_le (fun S => h S.1 S.2) hε

lemma wl9_lam_sum {β : ℝ} (m' : ℕ) :
    β / ((m' + 2 : ℕ) : ℝ) * ((m' + 1 : ℕ) : ℝ) + β / ((m' + 2 : ℕ) : ℝ) = β := by
  have : ((m' + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

lemma wl9_rpow_le_one (M : ℕ) (hM : 1 ≤ M) : (M : ℝ) ^ (-((d : ℝ) / 2)) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hM) (neg_nonpos.2 (by positivity))

/-! ### The sup bound -/

/-- **Sup bound for the calibrated reference marginal** (TeX `r2-log-reference-marginal`, first half; `dπ^R_N/dμ ≤ C`).
For every head index `M ≥ 1` there are `N₀, C` (before `ρ, β, N`) such that for all `N ≥ N₀`, all probability densities
`ρ` with `HasSphericalBound A ρ`, `β ∈ (0, βp]` and every weak potential `V` with `V.q = q_M`: the calibration field
satisfies `|⟪t_N, Ξ⟫| ≤ 1` and `π^R_N = firstMarginal R_N = μ.withDensity θ` with `0 ≤ θ ≤ C` everywhere. -/
theorem wl_ref_density_le (hd : 2 ≤ d) (A βp : ℝ) (hβp : 0 ≤ βp) (M : ℕ) (hM : 1 ≤ M) :
    ∃ (N0 : ℕ) (C : ℝ), 2 ≤ N0 ∧ 1 ≤ C ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ →
      HasSphericalBound A ρ → ∀ β : ℝ, 0 < β → β ≤ βp → ∀ N : ℕ, N0 ≤ N →
      ∀ V : WeakPotential (HRS.Whole.withDensityReal ρ), V.q = wl_qm (d := d) M →
        (∀ x, |inner ℝ (wl9_tN (HRS.Whole.withDensityReal ρ) M V β N)
          (Xi (HRS.Whole.withDensityReal ρ) (wl_psi M) x)| ≤ 1) ∧
        ∃ θ : Euc d → ℝ, Measurable θ ∧ (∀ x, 0 ≤ θ x ∧ θ x ≤ C) ∧
          HRS.Whole.firstMarginal (wl9_RN (HRS.Whole.withDensityReal ρ) M V β N) =
            (HRS.Whole.withDensityReal ρ).withDensity (fun x => ENNReal.ofReal (θ x)) := by
  obtain ⟨CK, Cl, hCK0, hQ⟩ := wl_Q_eq_fieldLaw hd A
  obtain ⟨hCq0, hCqspec⟩ := wl4b_Cq_spec hd A
  obtain ⟨N0, hN0⟩ := wl_field_small hd A βp 0 M hM
  set Cq := wl4b_Cq d A with hCq
  set Cl' : ℝ := max Cl 0 with hCl'
  have hCl'0 : 0 ≤ Cl' := le_max_right _ _
  set Mf : ℝ := βp * Cq + 1 with hMf
  set M1f : ℝ := βp * Cl' + 1 + βp * Cq with hM1f
  have hMf0 : 0 ≤ Mf := by positivity
  have hM1f0 : 0 ≤ M1f := by positivity
  refine ⟨max N0 2, Real.exp (Mf + M1f), le_max_right _ _, Real.one_le_exp (by positivity),
    fun ρ hρ hA β hβ hββp N hN V hV => ?_⟩
  have hNN0 : N0 ≤ N := le_trans (le_max_left _ _) hN
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  haveI := wl_isProb hρ
  obtain ⟨-, hℓ, hℓle, -, -⟩ := hQ ρ hρ hA β hβ.le N (by omega)
  have hq := hCqspec ρ hρ hA M hM
  set a : ℝ := Cq * (M : ℝ) ^ (-((d : ℝ) / 2)) with hadef
  have ha : 0 ≤ a := mul_nonneg hCq0 (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have haC : a ≤ Cq := by
    calc a ≤ Cq * 1 := mul_le_mul_of_nonneg_left (wl9_rpow_le_one M hM) hCq0
      _ = Cq := mul_one _
  have hm : ∫ x, logWeight x ∂(HRS.Whole.withDensityReal ρ) ≤ Cl' := hℓle.trans (le_max_left _ _)
  have hF : WlFam 0 β N N (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (0 : Euc d)) (fun _ => (0 : ℝ)) :=
    { one_le := by omega
      n_le := le_rfl
      β_nonneg := hβ.le
      p_le := by norm_num
      t_nonneg := fun a => a.elim0
      t_le := fun a => a.elim0
      v_meas := measurable_const
      v_bdd := fun x => by simp }
  have hc : ∀ x, |inner ℝ (wl9_tN (HRS.Whole.withDensityReal ρ) M V β N)
      (Xi (HRS.Whole.withDensityReal ρ) (wl_psi M) x)| ≤ 1 := fun x =>
    hN0 ρ hρ hA β hβ hββp N N hNN0 (by omega) 0 (fun _ => (0 : ℝ)) (fun _ => (0 : Euc d)) (fun _ => 0) hF V hV x
  refine ⟨hc, ?_⟩
  obtain ⟨m', rfl⟩ : ∃ m', N = m' + 2 := ⟨N - 2, by omega⟩
  refine ⟨wl9_theta (HRS.Whole.withDensityReal ρ) M V β m', ?_, fun x => ?_,
    wl9_firstMarginal_RN_eq hq ha hℓ hm hβ.le V hV m' hc⟩
  · exact wl6_measurable_theta V
      (wl9_isField_psiR hq ha hℓ hm hβ.le (Nat.succ_pos (m' + 1)) V hc).measurable _ _
  · obtain ⟨h0, h1⟩ := wl9_theta_le_ref hq ha hℓ hm hβ.le V hV m' hc x
    refine ⟨h0.le, h1.trans ?_⟩
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have hlam0 : 0 ≤ β / ((m' + 2 : ℕ) : ℝ) := div_nonneg hβ.le (Nat.cast_nonneg _)
    have hls := wl9_lam_sum (β := β) m'
    have h1 : β * a ≤ βp * Cq := mul_le_mul hββp haC ha hβp
    have h2 : β / ((m' + 2 : ℕ) : ℝ) * Cl' ≤ β * Cl' := by
      have : β / ((m' + 2 : ℕ) : ℝ) ≤ β := by linarith [mul_nonneg hlam0 (Nat.cast_nonneg (m' + 1))]
      exact mul_le_mul_of_nonneg_right this hCl'0
    have h3 : β * Cl' ≤ βp * Cl' := mul_le_mul_of_nonneg_right hββp hCl'0
    have h4 : β / ((m' + 2 : ℕ) : ℝ) * ((m' + 1 : ℕ) : ℝ) * a ≤ β * a := by
      have : β / ((m' + 2 : ℕ) : ℝ) * ((m' + 1 : ℕ) : ℝ) ≤ β := by linarith
      exact mul_le_mul_of_nonneg_right this ha
    linarith

/-! ### The `L²` bound -/

section Ref

variable {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {M : ℕ} {a m : ℝ}

/-- `∫ θ dμ = 1` for the density of the first marginal of the calibrated reference. -/
lemma wl9_integral_theta (hq : EWeakKernel μ a (wl_qm (d := d) M)) (ha : 0 ≤ a)
    (hℓ : Integrable (logWeight : Euc d → ℝ) μ) (hm : ∫ x, logWeight x ∂μ ≤ m) {β : ℝ} (hβ : 0 ≤ β)
    (V : WeakPotential μ) (hV : V.q = wl_qm (d := d) M) (m' : ℕ)
    (hc : ∀ x, |inner ℝ (wl9_tN μ M V β (m' + 2)) (Xi μ (wl_psi M) x)| ≤ 1) :
    ∫ x, wl9_theta μ M V β m' x ∂μ = 1 := by
  haveI := wl9_RN_isProb hq ha hℓ hm hβ V m' hc
  have hmarg := wl9_firstMarginal_RN_eq hq ha hℓ hm hβ V hV m' hc
  have hψ := wl9_isField_psiR hq ha hℓ hm hβ (Nat.succ_pos (m' + 1)) V hc
  have hθm : Measurable (wl9_theta μ M V β m') := wl6_measurable_theta V hψ.measurable _ _
  have hθ0 : ∀ x, 0 < wl9_theta μ M V β m' x := fun x =>
    wl9_theta_pos V hψ (div_nonneg hβ (Nat.cast_nonneg _)) (wl9_hrow hV hq ha) (m' + 1) x
  have hfm : HRS.Whole.firstMarginal (wl9_RN μ M V β (m' + 2)) =
      (wl9_RN μ M V β (m' + 2)).map (fun X => X 0) := wl6_firstMarginal_def (d := d) (m' + 1) _
  have h1 : (HRS.Whole.firstMarginal (wl9_RN μ M V β (m' + 2))) Set.univ = 1 := by
    rw [hfm]; exact measure_univ
  rw [hmarg, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => (hθ0 x).le)
    hθm.aestronglyMeasurable, h1]
  simp

end Ref

set_option maxHeartbeats 1600000 in
/-- **`‖dπ^R_N/dμ - 1‖_{L²(μ)} ≤ C/N`** (TeX `eq:r2-log-reference-marginal`).  For `d ≥ 2`, `A`, `βp ≥ 0` there is a head
index `M₀` such that for every `M ≥ M₀` there are `N₀ ≥ 2` and `C ≥ 1` (quantified before `ρ, β, N, V`) with, for every
probability density `ρ` with `HasSphericalBound A ρ`, `β ∈ (0, βp]`, `N ≥ N₀` and every weak potential `V` with
`V.q = q_M` (`μ = withDensityReal ρ`, `R_N = wl9_RN μ M V β N` the calibrated reference):
`|⟪t_N, Ξ⟫| ≤ 1`; `π^R_N = μ.withDensity θ` with `0 ≤ θ ≤ C` everywhere; `θ - 1 ∈ L²(μ)` with
`‖θ - 1‖_{L²(μ)} ≤ C/N`; and the calibration identity `⟪t_N, Ξ x⟫ = -β ∫ k_M(x,y) (θ(y) - 1) dμ(y) + c₀`. -/
theorem wl_ref_marginal_L2 (hd : 2 ≤ d) (A βp : ℝ) (hβp : 0 ≤ βp) :
    ∃ M0 : ℕ, 1 ≤ M0 ∧ ∀ M : ℕ, M0 ≤ M → ∃ (N0 : ℕ) (C : ℝ), 2 ≤ N0 ∧ 1 ≤ C ∧
      ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ →
      ∀ β : ℝ, 0 < β → β ≤ βp → ∀ N : ℕ, N0 ≤ N →
      ∀ V : WeakPotential (HRS.Whole.withDensityReal ρ), V.q = wl_qm (d := d) M →
        (∀ x, |inner ℝ (wl9_tN (HRS.Whole.withDensityReal ρ) M V β N)
          (Xi (HRS.Whole.withDensityReal ρ) (wl_psi M) x)| ≤ 1) ∧
        ∃ θ : Euc d → ℝ, Measurable θ ∧ (∀ x, 0 ≤ θ x ∧ θ x ≤ C) ∧
          HRS.Whole.firstMarginal (wl9_RN (HRS.Whole.withDensityReal ρ) M V β N) =
            (HRS.Whole.withDensityReal ρ).withDensity (fun x => ENNReal.ofReal (θ x)) ∧
          MemLp (fun x => θ x - 1) 2 (HRS.Whole.withDensityReal ρ) ∧
          eLpNorm (fun x => θ x - 1) 2 (HRS.Whole.withDensityReal ρ) ≤ ENNReal.ofReal (C / (N : ℝ)) ∧
          ∃ c₀ : ℝ, ∀ x, inner ℝ (wl9_tN (HRS.Whole.withDensityReal ρ) M V β N)
            (Xi (HRS.Whole.withDensityReal ρ) (wl_psi M) x) =
              -β * ∫ y, wl_km M x y * (θ y - 1) ∂(HRS.Whole.withDensityReal ρ) + c₀ := by
  obtain ⟨CK, Cl, hCK0, hQ⟩ := wl_Q_eq_fieldLaw hd A
  obtain ⟨hCq0, hCqspec⟩ := wl4b_Cq_spec hd A
  obtain ⟨C2, hC20, hC2⟩ := wl_row_pow hd A 2
  obtain ⟨C1, hC10, hC1⟩ := wl8_K_row_integrable hd A
  obtain ⟨Ccv, hCcv0, hcv⟩ := wl9_cv_L2 hd A
  obtain ⟨Cc, hCc0, hconv⟩ := wl8_conv_L2 hd A
  obtain ⟨Chn, hChn0, hhn⟩ := wl8_hN_L2 hd A
  set Cq := wl4b_Cq d A with hCq
  set Cl' : ℝ := max Cl 0 with hCl'
  have hCl'0 : 0 ≤ Cl' := le_max_right _ _
  set Mf : ℝ := βp * Cq + 1 with hMf
  set M1f : ℝ := βp * Cl' + 1 + βp * Cq with hM1f
  have hMf0 : 0 ≤ Mf := by positivity
  have hM1f0 : 0 ≤ M1f := by positivity
  obtain ⟨M0, hM0, hhead⟩ := wl9_head (d := d) (by omega) Cq βp Mf M1f
  refine ⟨M0, hM0, fun M hM => ?_⟩
  have hM1 : 1 ≤ M := le_trans hM0 hM
  obtain ⟨N0, hN0⟩ := wl_field_small hd A βp 0 M hM1
  set E : ℝ := Real.exp (Mf + M1f + 1) with hE
  set Cθ : ℝ := Real.exp (Mf + M1f) with hCθ
  have hCθ1 : 1 ≤ Cθ := Real.one_le_exp (by positivity)
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  set CD : ℝ := 2 * βp ^ 2 * E * C2 with hCD
  set Ctv : ℝ := 8 * E with hCtv
  set a1 : ℝ := CD + βp * Chn with ha1
  set a2 : ℝ := 2 * Ccv * Ctv with ha2
  set a3 : ℝ := βp * (Cθ * Cq) with ha3
  set Cf : ℝ := Cθ * (a1 + βp * a2 + a3) with hCf
  have hCD0 : 0 ≤ CD := by positivity
  have ha10 : 0 ≤ a1 := by positivity
  have ha20 : 0 ≤ a2 := by positivity
  have ha30 : 0 ≤ a3 := by positivity
  refine ⟨max N0 2, max Cθ Cf, le_max_right _ _, le_trans hCθ1 (le_max_left _ _),
    fun ρ hρ hA β hβ hββp N hN => ?_⟩
  have hNN0 : N0 ≤ N := le_trans (le_max_left _ _) hN
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  haveI hμp := wl_isProb hρ
  obtain ⟨-, hℓ, hℓle, -, -⟩ := hQ ρ hρ hA β hβ.le N (by omega)
  have hq := hCqspec ρ hρ hA M hM1
  set a : ℝ := Cq * (M : ℝ) ^ (-((d : ℝ) / 2)) with hadef
  have ha : 0 ≤ a := mul_nonneg hCq0 (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have haC : a ≤ Cq := by
    calc a ≤ Cq * 1 := mul_le_mul_of_nonneg_left (wl9_rpow_le_one M hM1) hCq0
      _ = Cq := mul_one _
  have hm : ∫ x, logWeight x ∂(HRS.Whole.withDensityReal ρ) ≤ Cl' := hℓle.trans (le_max_left _ _)
  have hF : WlFam 0 β N N (fun _ : Fin 0 => (0 : ℝ)) (fun _ : Fin 0 => (0 : Euc d)) (fun _ => (0 : ℝ)) :=
    { one_le := by omega
      n_le := le_rfl
      β_nonneg := hβ.le
      p_le := by norm_num
      t_nonneg := fun a => a.elim0
      t_le := fun a => a.elim0
      v_meas := measurable_const
      v_bdd := fun x => by simp }
  have hat : ∀ x, HRS.Whole.withDensityReal ρ {x} = 0 := wl_atomless (by omega) ρ
  obtain ⟨m', rfl⟩ : ∃ m', N = m' + 2 := ⟨N - 2, by omega⟩
  set μ := HRS.Whole.withDensityReal ρ with hμ
  intro V hV
  have hc : ∀ x, |inner ℝ (wl9_tN μ M V β (m' + 2)) (Xi μ (wl_psi M) x)| ≤ 1 := fun x =>
    hN0 ρ hρ hA β hβ hββp (m' + 2) (m' + 2) hNN0 (by omega) 0 (fun _ => (0 : ℝ)) (fun _ => (0 : Euc d))
      (fun _ => 0) hF V hV x
  refine ⟨hc, ?_⟩
  have hN0pos : 0 < m' + 2 := Nat.succ_pos _
  set Nr : ℝ := ((m' + 2 : ℕ) : ℝ) with hNr
  have hNpos : (0 : ℝ) < Nr := by positivity
  set lam : ℝ := β / Nr with hlamdef
  have hlam0 : 0 ≤ lam := div_nonneg hβ.le hNpos.le
  have hls := wl9_lam_sum (β := β) m'
  have hlam_le : lam ≤ β := by linarith [mul_nonneg hlam0 (Nat.cast_nonneg (m' + 1))]
  have hlamn : lam * ((m' + 1 : ℕ) : ℝ) ≤ β := by linarith
  -- the field and its constants
  set ψR := wl9_psiR μ M V β (m' + 2) with hψRdef
  have hψ : IsField μ ψR (β * a + 1) (lam * Cl' + 1) := wl9_isField_psiR hq ha hℓ hm hβ.le hN0pos V hc
  have hrow := wl9_hrow hV hq ha
  have hβaC : β * a ≤ βp * Cq := mul_le_mul hββp haC ha hβp
  have hMle : β * a + 1 ≤ Mf := by linarith
  have hM1le : lam * Cl' + 1 + lam * a ≤ M1f := by
    have h1 : lam * Cl' ≤ βp * Cl' := mul_le_mul (hlam_le.trans hββp) le_rfl hCl'0 hβp
    have h2 : lam * a ≤ βp * Cq := mul_le_mul (hlam_le.trans hββp) haC ha hβp
    linarith
  have hs : β * a ≤ min 1 (1 / (16 * Real.exp (Mf + M1f + 1))) :=
    (mul_le_mul_of_nonneg_right hββp ha).trans (hhead M hM)
  have hβa1 : β * a ≤ 1 := hs.trans (min_le_left _ _)
  have hsψ : β * a ≤ min 1 (1 / (16 * Real.exp ((β * a + 1) + (lam * Cl' + 1) + 1))) :=
    wl9_hs_mono hMle (by linarith [mul_nonneg hlam0 ha]) hs
  -- density `θ`
  set θ : Euc d → ℝ := wl9_theta μ M V β m' with hθdef
  have hθm : Measurable θ := wl6_measurable_theta V hψ.measurable _ _
  have hθbd : ∀ x, 0 < θ x ∧ θ x ≤ Cθ := fun x => by
    obtain ⟨h0, h1⟩ := wl9_theta_le_ref hq ha hℓ hm hβ.le V hV m' hc x
    refine ⟨h0, h1.trans ?_⟩
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have h4 : lam * ((m' + 1 : ℕ) : ℝ) * a ≤ β * a := mul_le_mul_of_nonneg_right hlamn ha
    have h5 : lam * Cl' ≤ βp * Cl' := mul_le_mul (hlam_le.trans hββp) le_rfl hCl'0 hβp
    linarith
  have hθ0 : ∀ x, 0 < θ x := fun x => (hθbd x).1
  have hθle : ∀ x, θ x ≤ Cθ := fun x => (hθbd x).2
  have hmarg := wl9_firstMarginal_RN_eq hq ha hℓ hm hβ.le V hV m' hc
  have hθ1 : ∫ x, θ x ∂μ = 1 := wl9_integral_theta hq ha hℓ hm hβ.le V hV m' hc
  have hwm : Measurable (fun y => θ y - 1) := hθm.sub_const 1
  have hwb : ∀ y, |θ y - 1| ≤ Cθ + 1 := fun y => by
    rw [abs_le]; constructor <;> linarith [hθ0 y, hθle y]
  have hwi : Integrable (fun y => θ y - 1) μ :=
    Integrable.of_bound hwm.aestronglyMeasurable (Cθ + 1)
      (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hwb y)
  have hθi : Integrable θ μ :=
    Integrable.of_bound hθm.aestronglyMeasurable Cθ
      (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs, abs_of_pos (hθ0 y)]; exact hθle y)
  have hz0 : ∫ y, (θ y - 1) ∂μ = 0 := by
    rw [integral_sub hθi (integrable_const _), hθ1]; simp
  -- the convolution `K z` and positivity
  set Kz : Euc d → ℝ := fun x => ∫ y, sphericalLogKernel x y * (θ y - 1) ∂μ with hKz
  obtain ⟨hKzm, hKzn⟩ := hconv ρ hρ hA (fun y => θ y - 1) hwm hwi
  have hKz2 : MemLp Kz 2 μ := lt_of_le_of_lt hKzn ENNReal.ofReal_lt_top
  have hnn : 0 ≤ ∫ x, Kz x * (θ x - 1) ∂μ := wl8_K_psd hd A hρ hA hwm hwb hz0
  -- the measures `π` and `ν`
  haveI hRNprob := wl9_RN_isProb hq ha hℓ hm hβ.le V m' hc
  have hRN := wl9_RN_eq hq ha hℓ hm hβ.le hN0pos V hc
  set π : Measure (Euc d) := HRS.Whole.firstMarginal (wl9_RN μ M V β (m' + 2)) with hπdef
  have hπeq : π = (fieldLaw V ψR lam (m' + 2)).map (fun Y => Y 0) := by
    rw [hπdef, wl6_firstMarginal_def (d := d) (m' + 1) _, hRN]
  set ν : Measure (Euc d) := (fieldLaw V ψR lam (m' + 1)).map (fun Y => Y 0) with hνdef
  haveI hπprob : IsProbabilityMeasure π := by
    rw [hπdef, wl6_firstMarginal_def (d := d) (m' + 1) _]; infer_instance
  haveI hfl : IsProbabilityMeasure (fieldLaw V ψR lam (m' + 1)) :=
    (fieldSpec (V := V) hψ hlam0 (m' + 1)).isProb
  haveI hνprob : IsProbabilityMeasure ν := by
    rw [hνdef]; infer_instance
  have hπle : π ≤ ENNReal.ofReal Cθ • μ := by
    rw [hmarg]; exact wl9_withDensity_le hθle
  have hνle : ν ≤ ENNReal.ofReal Cθ • μ := by
    refine wl8_le_smul_mono (wl9_cav_marg_le V hψ hlam0 hrow m') (ENNReal.ofReal_le_ofReal ?_)
    rw [← Real.exp_add, hCθ]
    refine Real.exp_le_exp.2 ?_
    have h3 : lam * (m' : ℝ) ≤ β := by
      have e : lam * ((m' + 1 : ℕ) : ℝ) = lam * (m' : ℝ) + lam := by push_cast; ring
      linarith
    have h4 : lam * (m' : ℝ) * a ≤ β * a := mul_le_mul_of_nonneg_right h3 ha
    have h5 : lam * Cl' ≤ βp * Cl' := mul_le_mul (hlam_le.trans hββp) le_rfl hCl'0 hβp
    linarith
  -- total variation of `π - ν`
  have hTV : tvDist π ν ≤ Ctv / Nr := by
    refine wl9_tvDist_le (by positivity) fun S hS => ?_
    have h := wl9_cavity_tv hq ha hψ hβ.le V hV m' hsψ hS
    rw [hπeq]
    refine h.trans ?_
    unfold wlPinC
    rw [← hNr, hCtv, hE]
    refine div_le_div_of_nonneg_right ?_ hNpos.le
    have h1 : Real.exp (β * a + 1 + (lam * Cl' + 1) + 1) ≤ Real.exp (Mf + M1f + 1) :=
      Real.exp_le_exp.2 (by linarith [mul_nonneg hlam0 ha])
    calc 8 * Real.exp (β * a + 1 + (lam * Cl' + 1) + 1) * (β * a) ≤ 8 * Real.exp (Mf + M1f + 1) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) hβa1 (by positivity) (by positivity)
      _ = 8 * Real.exp (Mf + M1f + 1) := mul_one _
  -- `q π - q ν`
  obtain ⟨hcvm, hcvn⟩ := hcv ρ hρ hA (wl_qm M) (wl_qm_measurable M) (wl_qm_symm M) (wl_qm_nonneg M)
    (wl9_qm_le_K M) Cθ (by linarith) π ν hπprob hνprob hπle hνle (Ctv / Nr) hTV
  set cv : Euc d → ℝ := fun x => ∫ y, wl_qm M x y ∂π - ∫ y, wl_qm M x y ∂ν with hcvdef
  set Qν : Euc d → ℝ := fun x => ∫ y, wl_qm M x y ∂ν with hQν
  have hQνm : Measurable Qν := RefMarg.measurable_integral_kernel
    (F := fun p : Euc d × Euc d => wl_qm M p.1 p.2) (wl_qm_measurable M)
  have hQνb : ∀ x, |lam * Qν x| ≤ lam * (Cθ * Cq) := fun x => by
    have h0 : 0 ≤ Qν x := integral_nonneg fun y => wl_qm_nonneg M x y
    have h1 : Qν x ≤ Cθ * Cq := by
      refine (wr13e_integral_le_of_le_smul hνle (by linarith) (fun y => wl_qm_nonneg M x y)
        (hq.wr1_integrable_row x)).trans ?_
      exact mul_le_mul_of_nonneg_left ((hq.wr1_rowInt_le ha x).trans haC) (by linarith)
    rw [abs_of_nonneg (mul_nonneg hlam0 h0)]
    exact mul_le_mul_of_nonneg_left h1 hlam0
  have hQn : eLpNorm (fun x => lam * Qν x) 2 μ ≤ ENNReal.ofReal (lam * (Cθ * Cq)) :=
    RefMarg.eLpNorm_two_le_const (hQνm.const_mul _).aestronglyMeasurable hQνb
  -- the exact cavity equation
  obtain ⟨c, hcav⟩ := wl9_cavity_equation hat hq ha hℓ hm hβ V hV m' hc
  set Dfun : Euc d → ℝ := fun x => wl9_D μ V.q ψR lam (m' + 1) x - lam * logWeight x with hDfun
  have heq : ∀ x, Real.log (θ x) + β * Kz x = Dfun x + β * cv x + lam * Qν x + c := fun x => hcav x
  have hDfun_eq : Dfun = fun x => Real.log (θ x) + β * Kz x - β * cv x - lam * Qν x - c := by
    funext x; have := heq x; linarith
  have hDm : Measurable Dfun := by
    rw [hDfun_eq]
    exact ((((Real.measurable_log.comp hθm).add (hKzm.const_mul β)).sub (hcvm.const_mul β)).sub
      (hQνm.const_mul _)).sub measurable_const
  have hℓm : Measurable (logWeight : Euc d → ℝ) := wl2_logWeight_measurable
  have hDm' : Measurable (fun x => wl9_D μ V.q ψR lam (m' + 1) x) := by
    have : (fun x => wl9_D μ V.q ψR lam (m' + 1) x) = fun x => Dfun x + lam * logWeight x := by
      funext x; simp only [hDfun]; ring
    rw [this]; exact hDm.add (hℓm.const_mul _)
  -- the defect bound
  have hq2 : ∀ x, ∫⁻ y, ‖V.q y x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal C2 := fun x => by
    have h := wl9_lintegral_sq_q M x (hC2 ρ hρ hA x).1 (hC2 ρ hρ hA x).2
    have e : ∀ y, V.q y x = wl_qm M y x := fun y => by rw [hV]
    simp_rw [e]; exact h
  have hDb : ∀ x, |wl9_D μ V.q ψR lam (m' + 1) x| ≤ CD / Nr := fun x => by
    obtain ⟨hD0, hD1⟩ := wl9_defect hq ha hψ hβ.le hN0pos m' (by omega) V hV hMle (by linarith [hM1le])
      hs hC20 hq2 x
    rw [abs_of_nonneg hD0]
    refine hD1.trans ?_
    set X : ℝ := Real.exp (Mf + (M1f + β * a)) * C2 with hX
    have hX0 : 0 ≤ X := by positivity
    have hXE : X ≤ E * C2 := by
      refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) hC20
      linarith
    have hr : ((m' + 1 : ℕ) : ℝ) ≤ Nr := by rw [hNr]; push_cast; linarith
    have e1 : lam ^ 2 * (2 * ((m' + 1 : ℕ) : ℝ) * X) =
        (β ^ 2 * (2 * X) / Nr) * (((m' + 1 : ℕ) : ℝ) / Nr) := by
      rw [hlamdef]; field_simp
    rw [e1]
    have e2 : (((m' + 1 : ℕ) : ℝ) / Nr) ≤ 1 := (div_le_one hNpos).2 hr
    calc (β ^ 2 * (2 * X) / Nr) * (((m' + 1 : ℕ) : ℝ) / Nr) ≤ (β ^ 2 * (2 * X) / Nr) * 1 :=
          mul_le_mul_of_nonneg_left e2 (by positivity)
      _ = β ^ 2 * (2 * X) / Nr := mul_one _
      _ ≤ CD / Nr := by
          refine div_le_div_of_nonneg_right ?_ hNpos.le
          have h1 : β ^ 2 ≤ βp ^ 2 := pow_le_pow_left₀ hβ.le hββp 2
          calc β ^ 2 * (2 * X) ≤ βp ^ 2 * (2 * (E * C2)) :=
                mul_le_mul h1 (mul_le_mul_of_nonneg_left hXE (by norm_num)) (by positivity) (by positivity)
            _ = CD := by rw [hCD]; ring
  have hDn : eLpNorm (fun x => wl9_D μ V.q ψR lam (m' + 1) x) 2 μ ≤ ENNReal.ofReal (CD / Nr) :=
    RefMarg.eLpNorm_two_le_const hDm'.aestronglyMeasurable hDb
  have hhN := hhn ρ hρ hA β hβ.le (m' + 2)
  have hD : eLpNorm Dfun 2 μ ≤ ENNReal.ofReal ((CD + βp * Chn) / Nr) := by
    have h1 : Dfun = (fun x => wl9_D μ V.q ψR lam (m' + 1) x) + fun x => wl_hN β (m' + 2) x := by
      funext x; simp only [hDfun, wl_hN, Pi.add_apply]; rw [hlamdef]; ring
    rw [h1]
    refine (eLpNorm_add_le (by norm_num)).trans ?_
    refine (add_le_add hDn hhN).trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have : (CD + βp * Chn) / Nr = CD / Nr + βp / Nr * Chn := by field_simp
    rw [this]
    have : β / (((m' + 2 : ℕ)) : ℝ) * Chn ≤ βp / Nr * Chn :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hββp hNpos.le) hChn0
    linarith
  have he1 : 0 ≤ (CD + βp * Chn) / Nr := by positivity
  have he2 : 0 ≤ Ccv * (2 * (Ctv / Nr)) := by positivity
  have he3 : 0 ≤ lam * (Cθ * Cq) := by positivity
  have hfin := wr13e_L2_assemble (μ := μ) (β := β) (lam := lam) (Cν := Cθ)
    (e1 := (CD + βp * Chn) / Nr) (e2 := Ccv * (2 * (Ctv / Nr))) (e3 := lam * (Cθ * Cq))
    hβ.le hCθ1 hθm hθ0 (Filter.Eventually.of_forall hθle) hθ1 hDm hcvm hQνm hD hcvn hQn he1 he2 he3
    hKz2 hnn (c := c) heq
  have hkey : Cθ * ((CD + βp * Chn) / Nr + β * (Ccv * (2 * (Ctv / Nr))) + lam * (Cθ * Cq)) ≤
      max Cθ Cf / Nr := by
    have e : Cθ * ((CD + βp * Chn) / Nr + β * (Ccv * (2 * (Ctv / Nr))) + lam * (Cθ * Cq)) =
        Cθ * (a1 + β * a2 + β * (Cθ * Cq)) / Nr := by
      simp only [ha1, ha2, hlamdef]
      field_simp
    rw [e]
    refine div_le_div_of_nonneg_right ?_ hNpos.le
    refine le_trans ?_ (le_max_right _ _)
    rw [hCf]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    have h2 : β * a2 ≤ βp * a2 := mul_le_mul_of_nonneg_right hββp ha20
    have h3 : β * (Cθ * Cq) ≤ a3 := by
      rw [ha3]; exact mul_le_mul_of_nonneg_right hββp (by positivity)
    linarith
  have hnorm : eLpNorm (fun x => θ x - 1) 2 μ ≤ ENNReal.ofReal (max Cθ Cf / Nr) :=
    hfin.trans (ENNReal.ofReal_le_ofReal hkey)
  obtain ⟨c₀, hc₀⟩ := wl9_hh_eq hq ha hℓ hm hβ V hV m' hc
  exact ⟨θ, hθm, fun x => ⟨(hθ0 x).le, (hθle x).trans (le_max_left _ _)⟩, hmarg,
    lt_of_le_of_lt hnorm ENNReal.ofReal_lt_top, hnorm, c₀, hc₀⟩

end HRS.MS.Wl

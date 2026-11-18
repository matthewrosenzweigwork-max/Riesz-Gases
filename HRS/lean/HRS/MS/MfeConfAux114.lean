import HRS.MS.MfeConfAux113

/-!
# S.B.1, packet F9 (part 17): the signed limit of the commutator mean `∫ C^M dμ^M → ∫ C dμ`

`sb1_Cmean_limit`: let `Y^M → X` pathwise (eventually equal, `X` collision-free a.s.), the laws `μ^M` of `Y^M` dominated by the
unnormalised regularised Gibbs measures `c e^{-β H_M} dX` (canonical-Gibbs domination, `sb1_flow_dom`), `v_r` Lipschitz and
`ρ_r` a regular density.  Then `C_r(X)` is integrable and `E C^M_r(Y^M) → E C_r(X)` (Vitali + the envelope and tail estimates).
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d N : ℕ}

section Main

variable {D : Whole.WholeDyn d} {T C B C3 : ℝ} {ρ : ℝ → Euc d → ℝ} (H : Sb1Tr3 D T C B C3 ρ)

include H

theorem sb1_Cmean_limit (hN : 1 ≤ N) (hβ : 0 < D.invβ) {cV CV : ℝ} (hcV : 0 < cV)
    (hV : ∀ x, cV * ‖x‖ ^ 2 - CV ≤ D.V x) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) {Kr : ℝ} (hKr : 0 ≤ Kr)
    (hL : ∀ x y, ‖Whole.mfeTransportW D (ρ r) x - Whole.mfeTransportW D (ρ r) y‖ ≤ Kr * ‖x - y‖)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Y : ℕ → Ω → Whole.EucConfig d N) (X : Ω → Whole.EucConfig d N) (hY : ∀ M, Measurable (Y M)) (hX : Measurable X)
    (c : ℝ) (hdom : ∀ M, P.map (Y M) ≤ ENNReal.ofReal c •
      sb1Dm (fun Z => Real.exp (-D.invβ⁻¹ * sb1Hs D (sb1kM d D.s M) N Z)))
    (hconv : ∀ᵐ ξ ∂P, (∀ i j, i ≠ j → X ξ i ≠ X ξ j) ∧ ∀ᶠ M in atTop, Y M ξ = X ξ) :
    Integrable (fun ξ => sb1CN D N ρ r (X ξ)) P ∧
      Tendsto (fun M => ∫ ξ, sb1_lv_Ck D (sb1kM d D.s M) N ρ r (Y M ξ) ∂P) atTop
        (𝓝 (∫ ξ, sb1CN D N ρ r (X ξ) ∂P)) := by
  have hs0 := H.tr.hs0
  have hd := H.tr.hd
  have hsd := H.tr.hsd
  have R := H.rho hd hr
  have hβ0 : 0 < D.invβ⁻¹ := inv_pos.2 hβ
  have hLc : Continuous (Whole.mfeTransportW D (ρ r)) := by
    have : LipschitzWith (Real.toNNReal Kr) (Whole.mfeTransportW D (ρ r)) := by
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hKr]; exact hL x y
    exact this.continuous
  have hvm : Measurable (Whole.mfeTransportW D (ρ r)) := hLc.measurable
  have hVm : Measurable D.V := H.tr.V.c3.continuous.measurable
  have hKr' : 0 ≤ Kr + 1 := by linarith
  have hL' : ∀ x y, ‖Whole.mfeTransportW D (ρ r) x - Whole.mfeTransportW D (ρ r) y‖ ≤ (Kr + 1) * ‖x - y‖ :=
    fun x y => (hL x y).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  obtain ⟨A1, A2, hA1, hA2, henv⟩ := sb1_Ck_env H hN
  -- measurability
  have hCM : ∀ M, Measurable (sb1_lv_Ck D (sb1kM d D.s M) N ρ r) := fun M =>
    sb1_pairE_meas R (sb1_meas_hk (sb1kM d D.s M) hvm)
  refine sb1_vitali (P := P) (f := fun M ξ => sb1_lv_Ck D (sb1kM d D.s M) N ρ r (Y M ξ))
    (g := fun ξ => sb1CN D N ρ r (X ξ)) (fun M => (hCM M).comp (hY M)) ?_ ?_
  · -- uniform integrability
    intro ε hε
    set β := D.invβ⁻¹ with hβdef
    set Nr : ℝ := (N : ℝ) with hNr
    have hNr0 : 0 < Nr := Nat.cast_pos.2 (by omega)
    set μ' := β * Nr / A1 with hμ'
    have hμ'0 : 0 < μ' := by positivity
    set Kr' := Kr + 1 with hKr'def
    have hKr'0 : 0 < Kr' := by linarith
    set τ0 : ℝ := Kr' * (2 / μ') * Real.exp (β * Nr * A2 / A1) with hτ0
    have hτ00 : 0 ≤ τ0 := by positivity
    set a : ℝ := μ' / (2 * Kr') with ha
    have ha0 : 0 < a := by positivity
    set Φ0 : Whole.EucConfig d N → ℝ := fun Z => Real.exp (β * Nr * (‖Z‖ + 1 / 2)) * Real.exp (-β * ∑ i, D.V (Z i)) with hΦ0
    have hΦi : Integrable Φ0 volume := sb1_Phi_int hVm hcV hV hβ0 hN
    set J : ℝ≥0∞ := ∫⁻ Z, ENNReal.ofReal (Φ0 Z) with hJ
    have hJtop : J < ⊤ := hΦi.lintegral_lt_top
    -- the pointwise tail estimate
    have hpt : ∀ (M : ℕ) (L : ℝ≥0) (Z : Whole.EucConfig d N),
        ({z | L ≤ ‖sb1_lv_Ck D (sb1kM d D.s M) N ρ r z‖₊}.indicator (fun z => ‖sb1_lv_Ck D (sb1kM d D.s M) N ρ r z‖ₑ)) Z *
          ENNReal.ofReal (Real.exp (-D.invβ⁻¹ * sb1Hs D (sb1kM d D.s M) N Z)) ≤
        ENNReal.ofReal (τ0 * Real.exp (-a * L) * Φ0 Z) := by
      intro M L Z
      by_cases h : L ≤ ‖sb1_lv_Ck D (sb1kM d D.s M) N ρ r Z‖₊
      · rw [Set.indicator_of_mem (show Z ∈ {z | L ≤ ‖sb1_lv_Ck D (sb1kM d D.s M) N ρ r z‖₊} from h)]
        rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul (abs_nonneg _)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hLabs : (L : ℝ) ≤ |sb1_lv_Ck D (sb1kM d D.s M) N ρ r Z| := by
          have : ((L : ℝ≥0) : ℝ) ≤ ((‖sb1_lv_Ck D (sb1kM d D.s M) N ρ r Z‖₊ : ℝ≥0) : ℝ) := by exact_mod_cast h
          simpa using this
        have := sb1_real_tail (β := β) (Nr := Nr) (A1 := A1) (A2 := A2) (Kr := Kr') (L := L)
          (PM := sb1PM (sb1kM d D.s M) N Z) (ell := sb1ell d N Z) (SV := ∑ i, D.V (Z i)) (zn := ‖Z‖)
          (Cabs := |sb1_lv_Ck D (sb1kM d D.s M) N ρ r Z|) hβ0 hNr0 hA1 hA2 hKr'0 (abs_nonneg _)
          (henv M hr hKr' hL' Z) (sb1_ell_le hN Z) hLabs L.2
        rw [← sb1_Hs_eq D (sb1kM d D.s M) hN Z] at this
        refine this.trans (le_of_eq ?_)
        simp only [hΦ0, hτ0, ha, hμ', hKr'def]
        have : Real.exp (-(β * Nr / A1) * ((L : ℝ) / (Kr + 1)) / 2) = Real.exp (-(β * Nr / A1 / (2 * (Kr + 1))) * L) := by
          congr 1; field_simp
        rw [this]
      · rw [Set.indicator_of_notMem (show Z ∉ {z | L ≤ ‖sb1_lv_Ck D (sb1kM d D.s M) N ρ r z‖₊} from h)]
        simp
    -- integrate
    have hLHS : ∀ (L : ℝ≥0) (M : ℕ), ∫⁻ ξ, ({x | L ≤ ‖sb1_lv_Ck D (sb1kM d D.s M) N ρ r (Y M x)‖₊}.indicator
        (fun x => ‖sb1_lv_Ck D (sb1kM d D.s M) N ρ r (Y M x)‖ₑ)) ξ ∂P ≤
        ENNReal.ofReal c * (ENNReal.ofReal (τ0 * Real.exp (-a * L)) * J) := by
      intro L M
      set φ : Whole.EucConfig d N → ℝ≥0∞ := {z | L ≤ ‖sb1_lv_Ck D (sb1kM d D.s M) N ρ r z‖₊}.indicator
        (fun z => ‖sb1_lv_Ck D (sb1kM d D.s M) N ρ r z‖ₑ) with hφ
      have hφm : Measurable φ := (hCM M).enorm.indicator (measurableSet_le measurable_const (hCM M).nnnorm)
      have e1 : (fun ξ => ({x | L ≤ ‖sb1_lv_Ck D (sb1kM d D.s M) N ρ r (Y M x)‖₊}.indicator
          (fun x => ‖sb1_lv_Ck D (sb1kM d D.s M) N ρ r (Y M x)‖ₑ)) ξ) = fun ξ => φ (Y M ξ) := by
        funext ξ
        by_cases h : L ≤ ‖sb1_lv_Ck D (sb1kM d D.s M) N ρ r (Y M ξ)‖₊
        · rw [Set.indicator_of_mem (show ξ ∈ {x | L ≤ ‖sb1_lv_Ck D (sb1kM d D.s M) N ρ r (Y M x)‖₊} from h),
            hφ, Set.indicator_of_mem (show Y M ξ ∈ {z | L ≤ ‖sb1_lv_Ck D (sb1kM d D.s M) N ρ r z‖₊} from h)]
        · rw [Set.indicator_of_notMem (show ξ ∉ {x | L ≤ ‖sb1_lv_Ck D (sb1kM d D.s M) N ρ r (Y M x)‖₊} from h),
            hφ, Set.indicator_of_notMem (show Y M ξ ∉ {z | L ≤ ‖sb1_lv_Ck D (sb1kM d D.s M) N ρ r z‖₊} from h)]
      rw [e1, ← lintegral_map hφm (hY M)]
      calc ∫⁻ z, φ z ∂(P.map (Y M)) ≤ ∫⁻ z, φ z ∂(ENNReal.ofReal c • sb1Dm (fun Z => Real.exp (-D.invβ⁻¹ * sb1Hs D (sb1kM d D.s M) N Z))) :=
            lintegral_mono' (hdom M) le_rfl
        _ = ENNReal.ofReal c * ∫⁻ z, φ z * ENNReal.ofReal (Real.exp (-D.invβ⁻¹ * sb1Hs D (sb1kM d D.s M) N z)) := by
            rw [lintegral_smul_measure, smul_eq_mul]
            congr 1
            unfold sb1Dm
            have hwm : Measurable fun z : Whole.EucConfig d N =>
                ENNReal.ofReal (Real.exp (-D.invβ⁻¹ * sb1Hs D (sb1kM d D.s M) N z)) :=
              (Real.measurable_exp.comp (measurable_const.mul
                (sb1_Hs_cont D (sb1kM_isKernel D.s hs0 M) H.tr.V N).measurable)).ennreal_ofReal
            rw [lintegral_withDensity_eq_lintegral_mul (f := fun z => ENNReal.ofReal
              (Real.exp (-D.invβ⁻¹ * sb1Hs D (sb1kM d D.s M) N z))) _ hwm hφm]
            refine lintegral_congr fun z => ?_
            simp [mul_comm]
        _ ≤ ENNReal.ofReal c * ∫⁻ z, ENNReal.ofReal (τ0 * Real.exp (-a * L) * Φ0 z) := by
            gcongr with z
            exact hpt M L z
        _ = ENNReal.ofReal c * (ENNReal.ofReal (τ0 * Real.exp (-a * L)) * J) := by
            congr 1
            have : ∀ z, ENNReal.ofReal (τ0 * Real.exp (-a * L) * Φ0 z) =
                ENNReal.ofReal (τ0 * Real.exp (-a * L)) * ENNReal.ofReal (Φ0 z) := fun z =>
              ENNReal.ofReal_mul (by positivity)
            simp_rw [this]
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    -- choose L
    set Jr : ℝ := J.toReal with hJr
    have hJeq : J = ENNReal.ofReal Jr := (ENNReal.ofReal_toReal hJtop.ne).symm
    set κ : ℝ := (|c| + 1) * (Jr + 1) with hκ
    have hJr0 : 0 ≤ Jr := ENNReal.toReal_nonneg
    have hκ0 : 0 < κ := by positivity
    have ht : Tendsto (fun L : ℝ => τ0 * Real.exp (-a * L)) atTop (𝓝 0) := by
      have h1 := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop ha0)
      have h2 := h1.const_mul τ0
      simp only [Function.comp, id, mul_zero] at h2
      refine h2.congr fun L => ?_
      rw [neg_mul]
    obtain ⟨L, hLt, hL0⟩ := ((ht.eventually (gt_mem_nhds (div_pos hε hκ0))).and (eventually_ge_atTop (0 : ℝ))).exists
    refine ⟨⟨L, hL0⟩, fun M => (hLHS ⟨L, hL0⟩ M).trans ?_⟩
    have hc1 : ENNReal.ofReal c ≤ ENNReal.ofReal (|c| + 1) := ENNReal.ofReal_le_ofReal (by linarith [le_abs_self c])
    have hJ1 : J ≤ ENNReal.ofReal (Jr + 1) := by rw [hJeq]; exact ENNReal.ofReal_le_ofReal (by linarith)
    calc ENNReal.ofReal c * (ENNReal.ofReal (τ0 * Real.exp (-a * ((⟨L, hL0⟩ : ℝ≥0) : ℝ))) * J)
        ≤ ENNReal.ofReal (|c| + 1) * (ENNReal.ofReal (τ0 * Real.exp (-a * ((⟨L, hL0⟩ : ℝ≥0) : ℝ))) * ENNReal.ofReal (Jr + 1)) :=
          mul_le_mul' hc1 (mul_le_mul' le_rfl hJ1)
      _ = ENNReal.ofReal ((|c| + 1) * (τ0 * Real.exp (-a * L)) * (Jr + 1)) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          simp only [NNReal.coe_mk]
          ring_nf
      _ ≤ ENNReal.ofReal ε := by
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : (|c| + 1) * (τ0 * Real.exp (-a * L)) * (Jr + 1) = κ * (τ0 * Real.exp (-a * L)) := by
            rw [hκ]; ring
          rw [h1]
          have := (lt_div_iff₀ hκ0).1 hLt
          nlinarith
  · filter_upwards [hconv] with ξ ⟨hX', hev⟩
    exact (sb1_kM_Ck_tendsto H hs0 hr hKr hL hLc (X ξ) hX').congr'
      (hev.mono fun M hM => by beta_reduce; rw [hM])

end Main

end HRS.MS.MfeConf

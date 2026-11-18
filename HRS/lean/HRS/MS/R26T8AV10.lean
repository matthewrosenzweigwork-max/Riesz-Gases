import HRS.MS.R26T8AO05a
import HRS.MS.R26T8AV10a
import HRS.MS.CritWholeW2Shift
import HRS.MS.S113X2A1a

/-!
# S8.2 observed-time layer, packet T8A.V10: forward martingale of a compactly supported test function

Route: shift the canonical realization to time `u` (`s81b_isCanonical_shift`), apply the additive Itô formula
(`r26t8a_whole_ito_additive`) to the time-independent smooth `F`; the local Itô integral of the bounded progressive
integrand `1_{[0,T]} √(2/β) ∇F(X_r)` is the actual Itô integral, so Doob's `L²` inequality and the Itô isometry
bound `E sup_{t≤T} |M_t|²`; the time marginals are canonical by the Gibbs invariance field of the realization.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.PDE.ToolboxRd HRS.MP.SelfSimP4Impl

theorem r26t8a_v10_enorm_sq {d : ℕ} (v : Euc d) : ‖v‖ₑ ^ 2 = ∑ j, ‖v j‖ₑ ^ 2 := by
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), EuclideanSpace.norm_sq_eq,
    ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]

theorem r26t8a_compact_martingale (d N : ℕ) (hd : 2≤d) (hN : 2≤N)
    (a beta : ℝ) (ha : 0<a) (hbeta : 0<beta)
    {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
    (X0 : Omega → EucConfig d N) (W : ℝ≥0 → Omega → Fin N → Euc d)
    (X : ℝ≥0 → Omega → EucConfig d N) (hX : IsCanonicalRealization d (criticalS d) a beta N P X0 W X)
    (F : EucConfig d N → ℝ) (hF : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F)
    (hFs : tsupport F⊆(eucCollisionSet d N)ᶜ) (u T : ℝ) (hu : 0≤u) (hT : 0<T) :
    let LF := particleGenerator (quadraticGradientDyn d (criticalS d) a beta) F
    let M := fun t w => F (X (u+t).toNNReal w)-F (X u.toNNReal w)-
      ∫ r in Set.Icc 0 t, LF (X (u+r).toNNReal w)
    AEMeasurable (fun w => ⨆ t : Set.Icc (0:ℝ) T, ‖M t w‖ₑ) P ∧
    r26t8a_scalarSupSq P T M ≤ ENNReal.ofReal (8*T/beta)*
      ∫⁻ x, ∑ i, ‖HRS.MS.Phase2S82.configGrad F x i‖ₑ^2 ∂canonicalP d N a beta := by
  intro LF M
  classical
  set D := quadraticGradientDyn d (criticalS d) a beta with hD
  have hnu : 0 ≤ D.invβ := by
    show 0 ≤ beta⁻¹
    exact inv_nonneg.2 hbeta.le
  have hDrift : Measurable (fun Y : EucConfig d N => particleDriftW D Y) :=
    HRS.MS.S113X2.s113a_measurable_drift d (criticalS d) a beta N
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by exact_mod_cast le_top)
  have hF2 : ContDiff ℝ 2 F := hF.of_le (by
    first | simp | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  set u' : ℝ≥0 := u.toNNReal with hu'
  have hR := HRS.Whole.BreakdownS81.s81b_isCanonical_shift hX u'
  obtain ⟨Fil, W', hfilt⟩ := hR.filtered
  set X' : ℝ≥0 → Omega → EucConfig d N := HRS.Whole.S79.s79p_shiftX u' X with hX'
  have hf : IsC12On T Set.univ (fun _ x => F x) := isC12On_of_contDiff T Set.univ F hF2
  obtain ⟨Mrt, hMrt, hid⟩ := r26t8a_whole_ito_additive d N D hnu hDrift T hT.le P _ _ X'
    (hR.solution T) Fil W' hfilt (fun _ x => F x) hf
  have hW' : IsBrownianFiltration P (p4r_shiftFil Fil) W' := p4r_shiftFil_brownian hfilt.brownian
  have hprog : IsProgressive (p4r_shiftFil Fil) (ofNNRealTime X') :=
    r26t8a_o05a3_prog_shift hfilt.progressive (hfilt.adapted 0)
  -- the integrand
  set c : ℝ := Real.sqrt (2 * D.invβ) with hc
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  let g : EucConfig d N → (Fin N × Fin d → ℝ) := fun Y k =>
    c * HRS.MS.Phase2S82.configGrad F Y k.1 k.2
  have hgc : Continuous g := continuous_pi fun k =>
    continuous_const.mul ((EuclideanSpace.proj k.2).continuous.comp (r26t8a_v10a_cont F hF1 k.1))
  obtain ⟨C, hC0, hCb⟩ := r26t8a_v10a_bdd F hF hFc
  let Φfun : ℝ → Omega → Fin N × Fin d → ℝ := fun r w i =>
    c * HRS.MS.Phase2S82.configGrad F (X' r.toNNReal w) i.1 i.2
  have hΦprog : IsProgressive (p4r_shiftFil Fil) (r26t8a_clipIntegrand 0 T
      Φfun) := by
    have h1 : IsProgressive (p4r_shiftFil Fil) (fun r w => g (ofNNRealTime X' r w)) :=
      isProgressive_comp_measurable hprog hgc.measurable
    have e : r26t8a_clipIntegrand 0 T
        Φfun =
        fun r w => if r ∈ Set.Icc (0 : ℝ) T then g (ofNNRealTime X' r w) else 0 := by
      funext r w i
      by_cases h : r ∈ Set.Icc (0 : ℝ) T <;> simp [r26t8a_clipIntegrand, h, g, Φfun]
    rw [e]
    intro i
    have hset : MeasurableSet[Subtype.instMeasurableSpace.prod ((p4r_shiftFil Fil) i)]
        {p : Set.Iic i × Omega | (p.1 : ℝ) ∈ Set.Icc (0 : ℝ) T} := by
      have : {p : Set.Iic i × Omega | (p.1 : ℝ) ∈ Set.Icc (0 : ℝ) T} =
          {u : Set.Iic i | (u : ℝ) ∈ Set.Icc (0 : ℝ) T} ×ˢ univ := by
        ext p; simp
      rw [this]
      exact MeasurableSet.prod (measurable_subtype_coe measurableSet_Icc) MeasurableSet.univ
    exact Measurable.ite hset (h1 i) measurable_const
  have hΦ : IsProgressiveL2 P (p4r_shiftFil Fil) (r26t8a_clipIntegrand 0 T
      Φfun) := by
    refine IsProgressiveL2.of_bounded P hΦprog (c * C) fun s w k => ?_
    by_cases h : s ∈ Set.Icc (0 : ℝ) T
    · simp only [r26t8a_clipIntegrand, if_pos h]
      show |c * HRS.MS.Phase2S82.configGrad F (X' s.toNNReal w) k.1 k.2| ≤ c * C
      rw [abs_mul, abs_of_nonneg hc0]
      refine mul_le_mul_of_nonneg_left ?_ hc0
      rw [← Real.norm_eq_abs]
      exact (PiLp.norm_apply_le _ k.2).trans (hCb _ _)
    · simp only [r26t8a_clipIntegrand, if_neg h]
      simpa using mul_nonneg hc0 hC0
  have hX'eq : ∀ (w : Omega) (r : ℝ), 0 ≤ r → X' r.toNNReal w = X (u + r).toNNReal w := by
    intro w r hr
    show X (u' + r.toNNReal) w = _
    rw [hu', Real.toNNReal_add hu hr]
  have hMeq : ∀ᵐ w ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, M t w = itoIntegral P (p4r_shiftFil Fil) W'
      (r26t8a_clipIntegrand 0 T
        Φfun) t w := by
    have h1 := IsLocalItoIntegral.ae_eq_forall hW' hΦ.locL2 hMrt
      (isLocalItoIntegral_itoIntegral hW' hΦ)
    filter_upwards [hid, h1] with w hw hw1 t ht
    rw [← hw1 t]
    have hw2 := hw t ht
    have e1 : ∫ r in Set.Icc (0 : ℝ) t, (derivWithin (fun v => (fun _ (x : EucConfig d N) => F x) v
        (X' r.toNNReal w)) (Set.Icc 0 T) r + particleGenerator D ((fun _ (x : EucConfig d N) => F x) r)
        (X' r.toNNReal w)) = ∫ r in Set.Icc (0 : ℝ) t, LF (X (u + r).toNNReal w) := by
      refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
      simp only [derivWithin_fun_const, Pi.zero_apply, zero_add]
      rw [hX'eq w r hr.1]
    rw [e1] at hw2
    have e2 : X' t.toNNReal w = X (u + t).toNNReal w := hX'eq w t ht.1
    have e3 : X' 0 w = X u.toNNReal w := by
      show X (u' + 0) w = _
      rw [add_zero]
    simp only [e2, e3] at hw2
    show F (X (u + t).toNNReal w) - F (X u.toNNReal w) - ∫ r in Set.Icc (0 : ℝ) t, LF (X (u + r).toNNReal w) = _
    linarith
  have hmeasA : Measurable (fun w => ⨆ t ∈ Set.Icc (0 : ℝ) T, ‖itoIntegral P (p4r_shiftFil Fil) W'
      (r26t8a_clipIntegrand 0 T
        Φfun) t w‖ₑ) :=
    measurable_iSup_Icc_enorm (fun t => (adapted_itoIntegral P (p4r_shiftFil Fil) W' _ t).mono
      ((p4r_shiftFil Fil).le t) le_rfl) (continuous_itoIntegral P (p4r_shiftFil Fil) W' _) T
  have hSup : ∀ᵐ w ∂P, (⨆ t : Set.Icc (0 : ℝ) T, ‖M t w‖ₑ) = ⨆ t ∈ Set.Icc (0 : ℝ) T,
      ‖itoIntegral P (p4r_shiftFil Fil) W' (r26t8a_clipIntegrand 0 T
        Φfun) t w‖ₑ := by
    filter_upwards [hMeq] with w hw
    calc (⨆ t : Set.Icc (0 : ℝ) T, ‖M t w‖ₑ) = ⨆ t : Set.Icc (0 : ℝ) T, ‖itoIntegral P (p4r_shiftFil Fil) W'
          (r26t8a_clipIntegrand 0 T
            Φfun) t w‖ₑ :=
          iSup_congr fun t => by rw [hw t t.2]
      _ = _ := (iSup_subtype' (p := fun t => t ∈ Set.Icc (0 : ℝ) T)
          (f := fun t _ => ‖itoIntegral P (p4r_shiftFil Fil) W' (r26t8a_clipIntegrand 0 T
            Φfun) t w‖ₑ)).symm
  refine ⟨hmeasA.aemeasurable.congr (hSup.mono fun w h => h.symm), ?_⟩
  -- the energy
  set G : EucConfig d N → ℝ≥0∞ := fun Y => ∑ i, ‖HRS.MS.Phase2S82.configGrad F Y i‖ₑ ^ 2 with hG
  have hGm : Measurable G :=
    Finset.measurable_sum _ fun i _ => ((r26t8a_v10a_cont F hF1 i).measurable.enorm).pow_const 2
  have hlaw : ∀ r : ℝ, r ∈ Set.Icc (0 : ℝ) T → ∫⁻ w, G (X' r.toNNReal w) ∂P =
      ∫⁻ Y, G Y ∂canonicalP d N a beta := by
    intro r hr
    have hl : P.map (X' r.toNNReal) = canonicalP d N a beta := by
      have := hR.invariant P T (X u') (HRS.Whole.S79.s79p_shiftW u' W) X' hR.brownian hR.indep hR.init
        (hR.solution T) r.toNNReal (by rw [Real.coe_toNNReal _ hr.1]; exact hr.2)
      exact this
    rw [← hl, lintegral_map hGm ((hR.solution T).adapted _)]
  have hjoint : Measurable (fun p : Omega × ℝ => G (X' (min p.2 T).toNNReal p.1)) :=
    hGm.comp ((measurable_clamp hprog T).comp measurable_swap)
  have hsq : sqIntegralOn P (r26t8a_clipIntegrand 0 T
      Φfun) T =
      ENNReal.ofReal (2 * D.invβ) * (ENNReal.ofReal T * ∫⁻ Y, G Y ∂canonicalP d N a beta) := by
    unfold sqIntegralOn
    have ha1 : ∀ w, ∫⁻ r in Set.Icc (0 : ℝ) T, ∑ k, ‖r26t8a_clipIntegrand 0 T
        Φfun r w k‖ₑ ^ 2 =
        ENNReal.ofReal (2 * D.invβ) * ∫⁻ r in Set.Icc (0 : ℝ) T, G (X' (min r T).toNNReal w) := by
      intro w
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine setLIntegral_congr_fun measurableSet_Icc fun r hr => ?_
      simp only [r26t8a_clipIntegrand, if_pos hr, min_eq_left hr.2, Φfun]
      rw [Fintype.sum_prod_type, hG]
      simp only
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [r26t8a_v10_enorm_sq, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [enorm_mul, mul_pow, hc, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
        Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (by linarith)]
    simp_rw [ha1]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    rw [lintegral_lintegral_swap hjoint.aemeasurable]
    rw [setLIntegral_congr_fun measurableSet_Icc (g := fun _ => ∫⁻ Y, G Y ∂canonicalP d N a beta)
      (fun r hr => by rw [min_eq_left hr.2]; exact hlaw r hr)]
    rw [setLIntegral_const, Real.volume_Icc, sub_zero, mul_comm]
  unfold r26t8a_scalarSupSq
  have h8 : ENNReal.ofReal (8 * T / beta) = 4 * ENNReal.ofReal (2 * D.invβ) * ENNReal.ofReal T := by
    have h : 8 * T / beta = 4 * (2 * D.invβ) * T := by
      show 8 * T / beta = 4 * (2 * beta⁻¹) * T
      field_simp
      ring
    rw [h, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  calc ∫⁻ w, (⨆ t : Set.Icc (0 : ℝ) T, ‖M t w‖ₑ) ^ 2 ∂P
      = ∫⁻ w, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖itoIntegral P (p4r_shiftFil Fil) W' (r26t8a_clipIntegrand 0 T
        Φfun) t w‖ₑ) ^ 2 ∂P :=
        lintegral_congr_ae (hSup.mono fun w h => by simp only [h])
    _ ≤ 4 * sqIntegralOn P (r26t8a_clipIntegrand 0 T
        Φfun) T :=
        lintegral_iSup_itoIntegral_sq_le hW' hΦ T
    _ = ENNReal.ofReal (8 * T / beta) * ∫⁻ Y, G Y ∂canonicalP d N a beta := by
        rw [hsq, h8]
        ring

end HRS.MS.R26T8A

end

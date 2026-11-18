import HRS.MS.S111K3E2

/-!
# S11.1 continuation (S11K3), B03 part E3: continuity, variation and per-interval bound of the shifted covariance map

With `KB = s57pC · d 2^r K1²` and `C0` the abstract constant at horizon `2T`:
`‖J z a b‖ ≤ (3+√T)² C0 KB |2ν| ∫_{(a,b]} age² ‖z_v‖` and the same for the total variation of the cumulative map.
-/

set_option autoImplicit false
noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4000

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K3

open HRS HRS.Whole HRS.Uniform HRS.MS.CovMeas HRS.MS.S111K2 HRS.MS.S111K HRS.MS.FixEq
open Classical

variable {d : ℕ} {C : WholeCoeff d} {m T u c0 : ℝ} {r : ℕ} {b : MultiIndex d → ℝ} {Pw K1 : ℝ}
  {z z' : ℝ → (Euc d → ℝ) → ℝ}

/-- The constant of the trace bound. -/
def k3KB (d r : ℕ) (Pw K1 : ℝ) : ℝ := s57pC d r Pw * ((d : ℝ) * 2 ^ r * K1 ^ 2)

lemma k3KB_nonneg (d r : ℕ) (Pw K1 : ℝ) : 0 ≤ k3KB d r Pw K1 :=
  mul_nonneg (s57pC_nonneg d r Pw) (by positivity)

theorem k3_Dm_trace_bound' (A : K3Adm C m T u c0 r b Pw K1 z) {v : ℝ} (hv : v ∈ Icc (0 : ℝ) (u + T)) :
    ENNReal.ofReal (HRS.traceNormForm (k3Dm C m T u z v)) ≤
      ENNReal.ofReal (|2 * C.ν| * k3KB d r Pw K1) *
        (ENNReal.ofReal (s111k2_age c0 u v ^ 2) * dualNormE r Pw (z v)) := by
  refine (k3_Dm_trace_bound A hv).trans (le_of_eq ?_)
  have h1 : s57pC d r Pw * s101Cf d r (K1 * s111k2_age c0 u v) = k3KB d r Pw K1 * s111k2_age c0 u v ^ 2 := by
    unfold s101Cf k3KB; ring
  rw [h1, ENNReal.ofReal_mul (k3KB_nonneg d r Pw K1), ENNReal.ofReal_mul (abs_nonneg _)]
  ring

theorem k3_tr_lint_le (A : K3Adm C m T u c0 r b Pw K1 z) {S : Set ℝ} (hSm : MeasurableSet S)
    (hS : S ⊆ Icc 0 (u + T)) :
    ∫⁻ v in S, ENNReal.ofReal (HRS.traceNormForm (k3Dm C m T u z v)) ≤
      ENNReal.ofReal (|2 * C.ν| * k3KB d r Pw K1) *
        ∫⁻ v in S, ENNReal.ofReal (s111k2_age c0 u v ^ 2) * dualNormE r Pw (z v) := by
  calc ∫⁻ v in S, ENNReal.ofReal (HRS.traceNormForm (k3Dm C m T u z v))
      ≤ ∫⁻ v in S, ENNReal.ofReal (|2 * C.ν| * k3KB d r Pw K1) *
          (ENNReal.ofReal (s111k2_age c0 u v ^ 2) * dualNormE r Pw (z v)) :=
        setLIntegral_mono' hSm fun v hv => k3_Dm_trace_bound' A (hS hv)
    _ = _ := by rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-! ### Total variation of partition sums -/

theorem k3_Jx_tv (hT : 0 ≤ T)
    (J : (ℝ → K3Bil d m T) → VectorMeasure ℝ (ProjTensor2 (PathSp (2 * T) (KSpace d m T))))
    (D : ℝ → K3Bil d m T) (n : ℕ) (w : ℕ → ℝ) (hw : Monotone w) (hmem : ∀ i, w i ∈ Icc (0 : ℝ) (2 * T)) :
    ∑ i ∈ Finset.range n, ‖k3Jx hT J D (Ioc (w i) (w (i + 1)))‖ₑ ≤
      ENNReal.ofReal ((3 + Real.sqrt T) ^ 2) * (J D).variation (Icc 0 (2 * T)) := by
  have hn : ‖(k3reconCLM hT : PathSp (2 * T) (KSpace d m T) →L[ℝ] OscPath d m T)‖ ^ 2 ≤
      (3 + Real.sqrt T) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (k3reconCLM_norm_le hT) 2
  have hstep : ∀ I, ‖k3Jx hT J D I‖ₑ ≤ ENNReal.ofReal ((3 + Real.sqrt T) ^ 2) * ‖J D I‖ₑ := by
    intro I
    have h3 : ‖k3Jx hT J D I‖ ≤ (3 + Real.sqrt T) ^ 2 * ‖J D I‖ :=
      (norm_k3Psi_le hT (J D I)).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
    have h4 : ‖k3Jx hT J D I‖ₑ ≤ ENNReal.ofReal ((3 + Real.sqrt T) ^ 2 * ‖J D I‖) := by
      rw [← ofReal_norm_eq_enorm]; exact ENNReal.ofReal_le_ofReal h3
    rwa [ENNReal.ofReal_mul (by positivity), ofReal_norm_eq_enorm] at h4
  calc ∑ i ∈ Finset.range n, ‖k3Jx hT J D (Ioc (w i) (w (i + 1)))‖ₑ
      ≤ ∑ i ∈ Finset.range n, ENNReal.ofReal ((3 + Real.sqrt T) ^ 2) *
          (J D).variation (Ioc (w i) (w (i + 1))) := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact (hstep _).trans (mul_le_mul' le_rfl (VectorMeasure.enorm_measure_le_variation _ _))
    _ = ENNReal.ofReal ((3 + Real.sqrt T) ^ 2) *
          ∑ i ∈ Finset.range n, (J D).variation (Ioc (w i) (w (i + 1))) := by rw [Finset.mul_sum]
    _ = ENNReal.ofReal ((3 + Real.sqrt T) ^ 2) *
          (J D).variation (⋃ i ∈ Finset.range n, Ioc (w i) (w (i + 1))) := by
        rw [measure_biUnion_finset ?_ (fun i _ => measurableSet_Ioc)]
        intro i _ j _ hij
        simp only [Function.onFun]
        rw [Set.disjoint_left]
        intro x hx hx'
        rcases lt_or_gt_of_ne hij with h | h
        · exact absurd hx.2 (not_le.2 (lt_of_le_of_lt (hw (Nat.succ_le_of_lt h)) hx'.1))
        · exact absurd hx'.2 (not_le.2 (lt_of_le_of_lt (hw (Nat.succ_le_of_lt h)) hx.1))
    _ ≤ _ := by
        refine mul_le_mul' le_rfl (measure_mono ?_)
        intro x hx
        simp only [mem_iUnion] at hx
        obtain ⟨i, _, hxi⟩ := hx
        exact ⟨(hmem i).1.trans hxi.1.le, hxi.2.trans (hmem (i + 1)).2⟩

/-! ### The map `k3Jm` : continuity, variation, interval bound -/

section Final

variable (hT : 0 < T) (c : K3Ctx C m T u c0 r b Pw K1)
  {C0 : ℝ} {J : (ℝ → K3Bil d m T) → VectorMeasure ℝ (ProjTensor2 (PathSp (2 * T) (KSpace d m T)))}
  (hJ : K3Jprops T C0 J)

include hT c hJ in
theorem k3Jm_cont (h : K3AdmP C m T u r Pw z) :
    ContinuousOn (fun v => k3Jm hT.le J C u r Pw z 0 v) (Icc 0 (u + T)) := by
  have TD := h.hat_td hT c
  refine Topology.IsEmbedding.subtypeVal.continuousOn_iff.2 ?_
  have hφc : ContinuousOn (k3φ T u) (Icc 0 (u + T)) :=
    (k3φ_continuousOn hT c.hu).mono fun v hv => hv.1
  have hmaps : MapsTo (k3φ T u) (Icc 0 (u + T)) (Icc 0 (2 * T)) := fun v hv =>
    ⟨k3φ_nonneg hT c.hu hv.1, k3φ_le hT c.hu hv.1 hv.2⟩
  have h1 : ContinuousOn (fun v => k3Jx hT.le J (k3Hat T u (k3Dm C m T u z)) (Ioc 0 (k3φ T u v)))
      (Icc 0 (u + T)) := (k3_Jx_Ioc0_cont hT.le hJ TD).comp hφc hmaps
  have h2 := h1.sub (continuousOn_const (c := k3Jx hT.le J (k3Hat T u (k3Dm C m T u z)) (Ioc 0 (k3φ T u 0))))
  refine h2.congr fun v hv => ?_
  show ((k3Jm hT.le J C u r Pw z 0 v : projTensor (OscPath d m T) 2) : TensorDual (OscPath d m T) 2) =
    k3Jx hT.le J (k3Hat T u (k3Dm C m T u z)) (Ioc 0 (k3φ T u v)) -
      k3Jx hT.le J (k3Hat T u (k3Dm C m T u z)) (Ioc 0 (k3φ T u 0))
  rw [k3Jm_coe h]
  have := k3Jx_Ioc_add hT.le J (k3Hat T u (k3Dm C m T u z)) (a := 0) (b := k3φ T u 0) (c := k3φ T u v)
    (k3φ_nonneg hT c.hu le_rfl) (k3φ_mono hT c.hu le_rfl hv.1)
  rw [this]; abel

include hT c hJ in
theorem k3Jm_interval_bound (hC0 : 0 ≤ C0) (h : K3AdmP C m T u r Pw z) {a a' : ℝ} (ha : 0 ≤ a) (haa : a ≤ a')
    (haH : a' ≤ u + T) :
    ‖(k3Jm hT.le J C u r Pw z a a' : projTensor (OscPath d m T) 2)‖ₑ ≤
      ENNReal.ofReal ((3 + Real.sqrt T) ^ 2 * C0 * k3KB d r Pw K1 * |2 * C.ν|) *
        ∫⁻ v in Ioc a a', ENNReal.ofReal (s111k2_age c0 u v ^ 2) * dualNormE r Pw (z v) := by
  have A := h.adm c
  have TD := k3_Dm_td A h.2.2
  have hb : (‖(k3Jm hT.le J C u r Pw z a a' : projTensor (OscPath d m T) 2)‖ₑ) =
      ‖k3Jx hT.le J (k3Hat T u (k3Dm C m T u z)) (Ioc (k3φ T u a) (k3φ T u a'))‖ₑ := by
    show ‖((k3Jm hT.le J C u r Pw z a a' : projTensor (OscPath d m T) 2) : TensorDual (OscPath d m T) 2)‖ₑ = _
    rw [k3Jm_coe h]
  rw [hb]
  refine (k3_Jx_interval_bound hT hJ (h.hat_td hT c) measurableSet_Ioc).trans ?_
  rw [k3_hat_lint hT c.hu TD ha haa haH]
  have hsub : Ioc a a' ∩ Icc 0 (u + T) = Ioc a a' := by
    ext v; simp only [mem_inter_iff, mem_Ioc, mem_Icc]
    constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, by linarith [h.1], h.2.trans haH⟩
  rw [hsub]
  have := k3_tr_lint_le A (S := Ioc a a') (measurableSet_Ioc) (fun v hv => (⟨by linarith [hv.1, ha], hv.2.trans haH⟩ : v ∈ Icc 0 (u + T)))
  calc ENNReal.ofReal ((3 + Real.sqrt T) ^ 2 * C0) * ∫⁻ v in Ioc a a', ENNReal.ofReal (HRS.traceNormForm (k3Dm C m T u z v))
      ≤ ENNReal.ofReal ((3 + Real.sqrt T) ^ 2 * C0) * (ENNReal.ofReal (|2 * C.ν| * k3KB d r Pw K1) *
          ∫⁻ v in Ioc a a', ENNReal.ofReal (s111k2_age c0 u v ^ 2) * dualNormE r Pw (z v)) :=
        mul_le_mul' le_rfl this
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring

include hT c hJ in
theorem k3Jm_var (hC0 : 0 ≤ C0) (h : K3AdmP C m T u r Pw z) :
    eVariationOn (fun v => k3Jm hT.le J C u r Pw z 0 v) (Icc 0 (u + T)) ≤
      ENNReal.ofReal ((3 + Real.sqrt T) ^ 2 * C0 * k3KB d r Pw K1 * |2 * C.ν|) *
        ∫⁻ v in Icc 0 (u + T), ENNReal.ofReal (s111k2_age c0 u v ^ 2) * dualNormE r Pw (z v) := by
  have A := h.adm c
  have TD := k3_Dm_td A h.2.2
  have hTD := h.hat_td hT c
  unfold eVariationOn
  refine iSup_le fun p => ?_
  obtain ⟨n, w, hw, hmem⟩ := p
  have hstep : ∀ i, edist (k3Jm hT.le J C u r Pw z 0 (w (i + 1))) (k3Jm hT.le J C u r Pw z 0 (w i)) =
      ‖k3Jx hT.le J (k3Hat T u (k3Dm C m T u z)) (Ioc (k3φ T u (w i)) (k3φ T u (w (i + 1))))‖ₑ := by
    intro i
    rw [edist_eq_enorm_sub]
    have hwi0 : 0 ≤ w i := (hmem i).1
    have hle : w i ≤ w (i + 1) := hw (Nat.le_succ i)
    have : ((k3Jm hT.le J C u r Pw z 0 (w (i + 1)) - k3Jm hT.le J C u r Pw z 0 (w i) :
        projTensor (OscPath d m T) 2) : TensorDual (OscPath d m T) 2) =
        k3Jx hT.le J (k3Hat T u (k3Dm C m T u z)) (Ioc (k3φ T u (w i)) (k3φ T u (w (i + 1)))) := by
      rw [Submodule.coe_sub, k3Jm_coe h, k3Jm_coe h,
        k3Jx_Ioc_add hT.le J _ (k3φ_mono hT c.hu le_rfl hwi0) (k3φ_mono hT c.hu hwi0 hle)]
      abel
    rw [← this]
    rfl
  simp_rw [hstep]
  have hmono : Monotone fun i => k3φ T u (w i) := fun i j hij =>
    k3φ_mono hT c.hu (hmem i).1 (hw hij)
  have hmem' : ∀ i, k3φ T u (w i) ∈ Icc (0 : ℝ) (2 * T) := fun i =>
    ⟨k3φ_nonneg hT c.hu (hmem i).1, k3φ_le hT c.hu (hmem i).1 (hmem i).2⟩
  refine (k3_Jx_tv hT.le J _ n (fun i => k3φ T u (w i)) hmono hmem').trans ?_
  calc ENNReal.ofReal ((3 + Real.sqrt T) ^ 2) * (J (k3Hat T u (k3Dm C m T u z))).variation (Icc 0 (2 * T))
      ≤ ENNReal.ofReal ((3 + Real.sqrt T) ^ 2) * (ENNReal.ofReal C0 *
          ∫⁻ s in Icc (0 : ℝ) (2 * T), ENNReal.ofReal (HRS.traceNormForm (k3Hat T u (k3Dm C m T u z) s))) :=
        mul_le_mul' le_rfl (hJ.tv _ hTD)
    _ = ENNReal.ofReal ((3 + Real.sqrt T) ^ 2 * C0) *
          ∫⁻ v in Icc (0 : ℝ) (u + T), ENNReal.ofReal (HRS.traceNormForm (k3Dm C m T u z v)) := by
        rw [k3_hat_lint_total hT c.hu TD, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal ((3 + Real.sqrt T) ^ 2 * C0) * (ENNReal.ofReal (|2 * C.ν| * k3KB d r Pw K1) *
          ∫⁻ v in Icc (0 : ℝ) (u + T), ENNReal.ofReal (s111k2_age c0 u v ^ 2) * dualNormE r Pw (z v)) :=
        mul_le_mul' le_rfl (k3_tr_lint_le A measurableSet_Icc subset_rfl)
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring

end Final

end HRS.MS.S111K3

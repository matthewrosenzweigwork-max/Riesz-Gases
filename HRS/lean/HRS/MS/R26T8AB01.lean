import HRS.MS.R26T8AB01b
import HRS.MS.CritForceObs1

/-!
# S8.2 T8A B01: `r26t8a_old_endpoint` (Pro contract, verbatim)
`Y t w = QAge 0 (a0+t-r) (X r w)` is, for a.e. `w`, an age primitive of `QAge 1`; the native anchored observed supremum
bound (`s82n_anchored_observed_sup`) with the invariant-law `L²` bounds of `Q` at ages `≥ j` gives the claim with
`B = √(2+2T²) C Cf`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.PDE.ToolboxRd

set_option maxHeartbeats 12800000 in
theorem r26t8a_old_endpoint (d : ℕ) (hd : 2≤d) (a beta m M C Cf c : ℝ)
    (ha : 0<a) (hbeta : 0<beta) (hM : 0≤M) (hC : 0≤C) (hCf : 0≤Cf) (hc : 0<c)
    (T : ℝ) (hT : 0<T) :
    ∃ B : ℝ, 0≤B ∧ ∀ rho : Euc d → ℝ, IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ,
      r26t8a_NormalFormFamily d a beta M C rho Psi →
      r26t8a_FeatureOrbits d a beta m Cf c rho →
      ∀ N : ℕ, 2≤N → ∀ {Omega : Type} [mOmega : MeasurableSpace Omega],
      ∀ P : Measure Omega, ∀ [IsProbabilityMeasure P],
      ∀ X0 : Omega → EucConfig d N, ∀ W : ℝ≥0 → Omega → Fin N → Euc d,
      ∀ X : ℝ≥0 → Omega → EucConfig d N,
      IsCanonicalRealization d (criticalS d) a beta N P X0 W X →
      ∀ a0 : ℝ, 0≤a0 → ∀ alpha : MultiIndex d,
      ∀ j : ℕ, ∀ r : ℝ, 0≤r → r≤a0-(j:ℝ) →
      let Y := fun t w => r26t8a_QAge a beta m rho Psi alpha 0 (a0+t-r) (X r.toNNReal w)
      AEMeasurable (fun w => ⨆ t : Set.Icc (0:ℝ) T, ‖Y t w‖ₑ) P ∧
        (r26t8a_scalarSupSq P T Y)^(1/2:ℝ) ≤ ENNReal.ofReal (B*HRS.MS.S82BD.s82Weight d m alpha*(N:ℝ)^(-(1/2:ℝ))*Real.exp (-c*(j:ℝ))) := by
  classical
  refine ⟨Real.sqrt (2 + 2 * T ^ 2) * C * Cf, by positivity, ?_⟩
  intro rho hrho Psi hPsi horb N hN Omega mOmega P hP X0 W X hX a0 ha0 alpha j r hr hra
  intro Y
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hW0 : 0 ≤ HRS.MS.S82BD.s82Weight d m alpha := by
    unfold HRS.MS.S82BD.s82Weight oscEigenvalue
    exact Real.rpow_nonneg (by positivity) _
  set w0 := HRS.MS.S82BD.s82Weight d m alpha with hw0
  set A : ℝ := Cf * w0 * Real.exp (-c * (j : ℝ)) with hA
  have hA0 : 0 ≤ A := by positivity
  set K : ℝ := (C * A) ^ 2 / (N : ℝ) with hK
  have hK0 : 0 ≤ K := by positivity
  have hjr : (j : ℝ) ≤ a0 - r := by linarith
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  -- test functions at ages `≥ j`
  have hTB : ∀ i : ℕ, i ≤ 1 → ∀ v : ℝ, (j : ℝ) ≤ v →
      TestBound (testOrder d) A (r26t8a_ageTest a beta m rho alpha i v) := by
    intro i hi v hv
    have := horb.bound alpha v (le_trans hj0 hv) i (by omega)
    refine r26t8a_o03b_tb_mono this ?_
    have : Real.exp (-c * v) ≤ Real.exp (-c * (j : ℝ)) := Real.exp_le_exp.2 (by nlinarith)
    rw [hA]
    exact mul_le_mul_of_nonneg_left this (mul_nonneg hCf hW0)
  have hXm : Measurable (X r.toNNReal) := (hX.solution r).adapted _
  have hncoll : ∀ᵐ w ∂P, X r.toNNReal w ∉ eucCollisionSet d N := by
    filter_upwards [(hX.solution r).no_collision] with w hw
    exact hw r.toNNReal (by rw [Real.coe_toNNReal r hr])
  have hQn := fun (i : ℕ) (hi : i ≤ 1) (v : ℝ) (hv : (j : ℝ) ≤ v) =>
    r26t8a_b01_Qnorm d N hd hN a beta M C ha hbeta hM hC rho hrho Psi hPsi P X0 W X hX r hr (hTB i hi v hv)
  -- the integrand `G`
  set U : Set (EucConfig d N) := (eucCollisionSet d N)ᶜ with hU
  have hUo : IsOpen U := r26t8a_o03b_coll_closed.isOpen_compl
  set Hf : ℝ × EucConfig d N → ℝ := fun q => r26t8a_QAge (N := N) a beta m rho Psi alpha 1 q.1 q.2 with hHf
  have hHc : ContinuousOn Hf (Set.Ici 0 ×ˢ U) :=
    r26t8a_o06_QAge_cont d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb alpha 1 (by norm_num)
  have hpw : Measurable ((Set.Ici (0 : ℝ) ×ˢ U).piecewise Hf (fun _ => 0)) :=
    ContinuousOn.measurable_piecewise hHc continuousOn_const (measurableSet_Ici.prod hUo.measurableSet)
  set G : ℝ → Omega → ℝ := fun t w =>
    (Set.Ici (0 : ℝ) ×ˢ U).piecewise Hf (fun _ => 0) (a0 + t - r, X r.toNNReal w) with hG
  have hGm : Measurable (fun p : ℝ × Omega => G p.1 p.2) :=
    hpw.comp (((measurable_const.add measurable_fst).sub measurable_const).prodMk (hXm.comp measurable_snd))
  have hGeq : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ w, X r.toNNReal w ∉ eucCollisionSet d N →
      G t w = r26t8a_QAge a beta m rho Psi alpha 1 (a0 + t - r) (X r.toNNReal w) := by
    intro t ht w hw
    have hmem : (a0 + t - r, X r.toNNReal w) ∈ Set.Ici (0 : ℝ) ×ˢ U :=
      ⟨by simp only [Set.mem_Ici]; linarith [ht.1], hw⟩
    simp only [hG]
    rw [Set.piecewise_eq_of_mem _ _ _ hmem]
  -- `L²` bounds
  have hY0 : MemLp (Y 0) 2 P := (hQn 0 (by norm_num) (a0 + 0 - r) (by linarith)).1
  have hY0b : ∫⁻ w, ‖Y 0 w‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal K := (hQn 0 (by norm_num) (a0 + 0 - r) (by linarith)).2
  set ν : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hν
  have hGb : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫⁻ w, ‖G t w‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal K := by
    intro t ht
    have h := (hQn 1 le_rfl (a0 + t - r) (by linarith [ht.1])).2
    refine le_trans (le_of_eq ?_) h
    refine lintegral_congr_ae ?_
    filter_upwards [hncoll] with w hw
    rw [hGeq t ht w hw]
    rfl
  have hGint : ∫⁻ p, ‖G p.1 p.2‖ₑ ^ 2 ∂(ν.prod P) ≤ ENNReal.ofReal K * ENNReal.ofReal T := by
    rw [lintegral_prod _ (hGm.enorm.pow_const 2).aemeasurable]
    calc ∫⁻ t, ∫⁻ w, ‖G t w‖ₑ ^ 2 ∂P ∂ν ≤ ∫⁻ t, ENNReal.ofReal K ∂ν := by
          refine setLIntegral_mono' measurableSet_Icc fun t ht => hGb t ht
      _ = ENNReal.ofReal K * ENNReal.ofReal T := by
          rw [lintegral_const, hν, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Icc]
          simp [hT.le]
  have hGmem : MemLp (fun p : ℝ × Omega => G p.1 p.2) 2 (ν.prod P) := by
    rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hGm.aestronglyMeasurable]
    simp only [ENNReal.toReal_ofNat]
    refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_
    have : ∫⁻ p, ‖G p.1 p.2‖ₑ ^ (2 : ℝ) ∂(ν.prod P) = ∫⁻ p, ‖G p.1 p.2‖ₑ ^ 2 ∂(ν.prod P) := by
      simp [ENNReal.rpow_two]
    rw [this]
    exact (lt_of_le_of_lt hGint (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)).ne
  -- fundamental theorem of calculus, pathwise
  have hFTC : ∀ᵐ w ∂P, IntegrableOn (fun t => G t w) (Set.Icc 0 T) ∧
      ∀ t ∈ Set.Icc 0 T, Y t w = Y 0 w + ∫ s in Set.Icc 0 t, G s w := by
    filter_upwards [hncoll] with w hw
    obtain ⟨hc1, hftc⟩ := r26t8a_b01_ftc d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb alpha
      (X r.toNNReal w) hw (a0 - r) T (by linarith)
    have hrw : ∀ t : ℝ, a0 + t - r = (a0 - r) + t := fun t => by ring
    have hGw : ∀ t ∈ Set.Icc (0 : ℝ) T, G t w = r26t8a_QAge a beta m rho Psi alpha 1 ((a0 - r) + t) (X r.toNNReal w) :=
      fun t ht => by rw [hGeq t ht w hw, hrw]
    refine ⟨(hc1.congr (fun t ht => hGw t ht)).integrableOn_Icc, fun t ht => ?_⟩
    have h1 := hftc t ht
    have h2 : ∫ s in Set.Icc 0 t, G s w = ∫ s in Set.Icc 0 t, r26t8a_QAge a beta m rho Psi alpha 1 ((a0 - r) + s)
        (X r.toNNReal w) :=
      setIntegral_congr_fun measurableSet_Icc fun s hs => hGw s ⟨hs.1, hs.2.trans ht.2⟩
    simp only [Y]
    rw [h2, hrw t, hrw 0]
    exact h1
  obtain ⟨hmeas, hsup⟩ := HRS.MS.S82N.s82n_anchored_observed_sup P T hT Y G hY0 hGmem hFTC
  refine ⟨hmeas, ?_⟩
  have hsup' : r26t8a_scalarSupSq P T Y ≤ ENNReal.ofReal ((2 + 2 * T ^ 2) * K) := by
    refine le_trans hsup ?_
    calc 2 * (∫⁻ w, ‖Y 0 w‖ₑ ^ 2 ∂P) + ENNReal.ofReal (2 * T) * ∫⁻ p, ‖G p.1 p.2‖ₑ ^ 2 ∂(ν.prod P)
        ≤ 2 * ENNReal.ofReal K + ENNReal.ofReal (2 * T) * (ENNReal.ofReal K * ENNReal.ofReal T) :=
          add_le_add (mul_le_mul_of_nonneg_left hY0b (zero_le)) (mul_le_mul_of_nonneg_left hGint (zero_le))
      _ = ENNReal.ofReal ((2 + 2 * T ^ 2) * K) := by
          rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; ring
  set Yv : ℝ := Real.sqrt (2 + 2 * T ^ 2) * C * Cf * w0 * (N : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (-c * (j : ℝ)) with hYv
  have hYv0 : 0 ≤ Yv := by positivity
  have hNrt : ((N : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = 1 / (N : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    norm_num
    exact Real.rpow_neg_one _
  have hYsq : Yv ^ 2 = (2 + 2 * T ^ 2) * K := by
    have h2 : Real.sqrt (2 + 2 * T ^ 2) ^ 2 = 2 + 2 * T ^ 2 := Real.sq_sqrt (by positivity)
    have : Yv ^ 2 = (Real.sqrt (2 + 2 * T ^ 2)) ^ 2 * (C * Cf * w0 * Real.exp (-c * (j : ℝ))) ^ 2 *
        ((N : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 := by
      rw [hYv]; ring
    rw [this, h2, hNrt, hK, hA]
    field_simp
  calc (r26t8a_scalarSupSq P T Y) ^ (1 / 2 : ℝ) ≤ (ENNReal.ofReal ((2 + 2 * T ^ 2) * K)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hsup' (by norm_num)
    _ = ENNReal.ofReal Yv := by
        rw [← hYsq, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow,
          Real.sqrt_sq hYv0]
    _ = _ := rfl

end HRS.MS.R26T8A

end

import HRS.MS.R26T8AB05a
import HRS.MS.R26T8AB00b4

/-!
# S8.2 T8A B05: `r26t8a_recent_drift` (Pro contract, verbatim)

`Y t w = ∫_{[0,t]} VAge 0 (t-r) (X (a0+r) w) dr`; triangle drift estimate (`r26t8a_triangle_drift`) with the invariant-law `L²`
bounds of `V0 = D0 - Q1`, `V1 = D1 - Q2` (ages `≥ 0`, bound without decay) and the age FTC of B02b; `B = 2 C Cf (T + T²/2)`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.PDE.ToolboxRd

set_option maxHeartbeats 12800000 in
theorem r26t8a_recent_drift (d : ℕ) (hd : 2≤d) (a beta m M C Cf c : ℝ)
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
      let Y := fun t w => ∫ r in Set.Icc 0 t, r26t8a_VAge a beta m rho Psi alpha 0 (t-r) (X (a0+r).toNNReal w)
      AEMeasurable (fun w => ⨆ t : Set.Icc (0:ℝ) T, ‖Y t w‖ₑ) P ∧
        (r26t8a_scalarSupSq P T Y)^(1/2:ℝ) ≤ ENNReal.ofReal (B*HRS.MS.S82BD.s82Weight d m alpha*(N:ℝ)^(-(1/2:ℝ))) := by
  classical
  refine ⟨2 * C * Cf * (T + T ^ 2 / 2), by positivity, ?_⟩
  intro rho hrho Psi hPsi horb N hN Omega mOmega P hP X0 W X hX a0 ha0 alpha
  intro Y
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hW0 : 0 ≤ HRS.MS.S82BD.s82Weight d m alpha := by
    unfold HRS.MS.S82BD.s82Weight oscEigenvalue
    exact Real.rpow_nonneg (by positivity) _
  set w0 := HRS.MS.S82BD.s82Weight d m alpha with hw0
  set A : ℝ := Cf * w0 with hA
  have hA0 : 0 ≤ A := by positivity
  set A' : ℝ := 2 * (C * A * (N : ℝ) ^ (-(1 / 2 : ℝ))) with hA'
  have hA'0 : 0 ≤ A' := by positivity
  have hTB : ∀ i : ℕ, i ≤ 2 → ∀ v : ℝ, 0 ≤ v →
      TestBound (testOrder d) A (r26t8a_ageTest a beta m rho alpha i v) := by
    intro i hi v hv
    have := horb.bound alpha v hv i hi
    refine r26t8a_o03b_tb_mono this ?_
    have : Real.exp (-c * v) ≤ 1 := by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.2 (by nlinarith)
    rw [hA]
    calc Cf * w0 * Real.exp (-c * v) ≤ Cf * w0 * 1 := mul_le_mul_of_nonneg_left this (mul_nonneg hCf hW0)
      _ = Cf * w0 := mul_one _
  have hVn : ∀ (i : ℕ), i ≤ 1 → ∀ r : ℝ, 0 ≤ r → ∀ v : ℝ, 0 ≤ v →
      MemLp (fun w => r26t8a_VAge a beta m rho Psi alpha i v (X r.toNNReal w)) 2 P ∧
      eLpNorm (fun w => r26t8a_VAge a beta m rho Psi alpha i v (X r.toNNReal w)) 2 P ≤ ENNReal.ofReal A' :=
    fun i hi r hr v hv => r26t8a_b02_Vnorm d N hd hN a beta m M C ha hbeta hM hC rho hrho Psi hPsi P X0 W X hX r hr
      alpha m i v (hTB i (by omega) v hv) (hTB (i + 1) (by omega) v hv)
  have hm := r26t8a_b05_Vmeas d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb alpha 0
    (by norm_num) P X0 W X hX a0 T ha0
  have hdm := r26t8a_b05_Vmeas d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb alpha 1
    (by norm_num) P X0 W X hX a0 T ha0
  have hdiag : ∀ r ∈ Set.Icc (0 : ℝ) T, MemLp ((fun (t r : ℝ) (w : Omega) =>
      r26t8a_VAge a beta m rho Psi alpha 0 (t - r) (X (a0 + r).toNNReal w)) r r) 2 P ∧
      eLpNorm ((fun (t r : ℝ) (w : Omega) => r26t8a_VAge a beta m rho Psi alpha 0 (t - r) (X (a0 + r).toNNReal w)) r r)
        2 P ≤ ENNReal.ofReal A' := by
    intro r hr
    exact hVn 0 (by norm_num) (a0 + r) (by linarith [hr.1]) (r - r) (by simp)
  have hder : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ v ∈ Set.Icc r T, MemLp ((fun (t r : ℝ) (w : Omega) =>
      r26t8a_VAge a beta m rho Psi alpha 1 (t - r) (X (a0 + r).toNNReal w)) v r) 2 P ∧
      eLpNorm ((fun (t r : ℝ) (w : Omega) => r26t8a_VAge a beta m rho Psi alpha 1 (t - r) (X (a0 + r).toNNReal w)) v r)
        2 P ≤ ENNReal.ofReal A' := by
    intro r hr v hv
    exact hVn 1 le_rfl (a0 + r) (by linarith [hr.1]) (v - r) (by linarith [hv.1])
  have hFTC : ∀ᵐ p ∂((volume.restrict (Set.Icc 0 T)).prod P),
      IntegrableOn (fun v => (fun (t r : ℝ) (w : Omega) =>
        r26t8a_VAge a beta m rho Psi alpha 1 (t - r) (X (a0 + r).toNNReal w)) v p.1 p.2) (Set.Icc p.1 T) ∧
      ∀ t ∈ Set.Icc p.1 T, (fun (t r : ℝ) (w : Omega) =>
        r26t8a_VAge a beta m rho Psi alpha 0 (t - r) (X (a0 + r).toNNReal w)) t p.1 p.2 =
        (fun (t r : ℝ) (w : Omega) => r26t8a_VAge a beta m rho Psi alpha 0 (t - r) (X (a0 + r).toNNReal w)) p.1 p.1 p.2 +
          ∫ v in Set.Icc p.1 t, (fun (t r : ℝ) (w : Omega) =>
            r26t8a_VAge a beta m rho Psi alpha 1 (t - r) (X (a0 + r).toNNReal w)) v p.1 p.2 := by
    have hr1 : ∀ᵐ r ∂(volume.restrict (Set.Icc (0 : ℝ) T)), r ∈ Set.Icc (0 : ℝ) T :=
      ae_restrict_mem measurableSet_Icc
    have hg := r26t8a_b02_ae_good d N a beta P X0 W X hX (a0 + T)
    have h1' : ∀ᵐ p ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod P), p.1 ∈ Set.Icc (0 : ℝ) T :=
      (Measure.quasiMeasurePreserving_fst (μ := volume.restrict (Set.Icc (0 : ℝ) T)) (ν := P)).ae hr1
    have h2' : ∀ᵐ p ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod P),
        ∀ r : ℝ, 0 ≤ r → r ≤ a0 + T → X r.toNNReal p.2 ∉ eucCollisionSet d N :=
      (Measure.quasiMeasurePreserving_snd (μ := volume.restrict (Set.Icc (0 : ℝ) T)) (ν := P)).ae hg
    filter_upwards [h1', h2'] with p hp1 hp2
    obtain ⟨hc1, hftc⟩ := r26t8a_b02_ftc d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb alpha
      (X (a0 + p.1).toNNReal p.2) (hp2 (a0 + p.1) (by linarith [hp1.1]) (by linarith [hp1.2])) 0 T le_rfl
    refine ⟨?_, fun t ht => ?_⟩
    · have hsub : ContinuousOn (fun v : ℝ => v - p.1) (Set.Icc p.1 T) := (continuous_id.sub continuous_const).continuousOn
      have hmaps : Set.MapsTo (fun v : ℝ => v - p.1) (Set.Icc p.1 T) (Set.Icc 0 T) :=
        fun v hv => ⟨by simp only; linarith [hv.1], by simp only; linarith [hv.2, hp1.1]⟩
      have := hc1.comp hsub hmaps
      simp only [zero_add] at this
      exact this.integrableOn_Icc
    · have h1 := hftc (t - p.1) ⟨by linarith [ht.1], by linarith [ht.2, hp1.1]⟩
      simp only [zero_add, add_zero] at h1
      have h2 : ∫ v in Set.Icc p.1 t, r26t8a_VAge a beta m rho Psi alpha 1 (v - p.1) (X (a0 + p.1).toNNReal p.2) =
          ∫ s in Set.Icc 0 (t - p.1), r26t8a_VAge a beta m rho Psi alpha 1 s (X (a0 + p.1).toNNReal p.2) := by
        rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht.1,
          ← intervalIntegral.integral_of_le (by linarith [ht.1]), intervalIntegral.integral_comp_sub_right
            (fun s => r26t8a_VAge a beta m rho Psi alpha 1 s (X (a0 + p.1).toNNReal p.2)) p.1]
        simp
      simp only [h2]
      rw [h1]
      simp
  obtain ⟨hmeas, hsup⟩ := r26t8a_triangle_drift P T A' hT hA'0
    (fun t r w => r26t8a_VAge a beta m rho Psi alpha 0 (t - r) (X (a0 + r).toNNReal w))
    (fun t r w => r26t8a_VAge a beta m rho Psi alpha 1 (t - r) (X (a0 + r).toNNReal w))
    hm hdm hdiag hder hFTC
  refine ⟨hmeas, hsup.trans ?_⟩
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  rw [hA']; rw [hA]; ring

end HRS.MS.R26T8A

end

import HRS.MS.R26T8AB02d
import HRS.MS.R26T8AB00a4

/-!
# S8.2 T8A B02: `r26t8a_old_drift` (Pro contract, verbatim)

`Y t w = ∫_{[l,h]} VAge 0 (a0+t-r) (X r w) dr` with `V = D - Q'`; rectangle drift estimate (`r26t8a_rectangle_drift`) with the
invariant-law `L²` bounds of `V0 = D0 - Q1` and `V1 = D1 - Q2` at ages `≥ j` and the age FTC of B02b; `B = 2 C Cf (1+T)`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.PDE.ToolboxRd

set_option maxHeartbeats 12800000 in
theorem r26t8a_old_drift (d : ℕ) (hd : 2≤d) (a beta m M C Cf c : ℝ)
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
      ∀ j : ℕ, ∀ l h : ℝ, 0≤l → l≤h → h≤a0-(j:ℝ) → h-l≤1 →
      let Y := fun t w => ∫ r in Set.Icc l h, r26t8a_VAge a beta m rho Psi alpha 0 (a0+t-r) (X r.toNNReal w)
      AEMeasurable (fun w => ⨆ t : Set.Icc (0:ℝ) T, ‖Y t w‖ₑ) P ∧
        (r26t8a_scalarSupSq P T Y)^(1/2:ℝ) ≤ ENNReal.ofReal (B*HRS.MS.S82BD.s82Weight d m alpha*(N:ℝ)^(-(1/2:ℝ))*Real.exp (-c*(j:ℝ))) := by
  classical
  refine ⟨2 * C * Cf * (1 + T), by positivity, ?_⟩
  intro rho hrho Psi hPsi horb N hN Omega mOmega P hP X0 W X hX a0 ha0 alpha j l h hl hlh hha hh1
  intro Y
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hW0 : 0 ≤ HRS.MS.S82BD.s82Weight d m alpha := by
    unfold HRS.MS.S82BD.s82Weight oscEigenvalue
    exact Real.rpow_nonneg (by positivity) _
  set w0 := HRS.MS.S82BD.s82Weight d m alpha with hw0
  set A : ℝ := Cf * w0 * Real.exp (-c * (j : ℝ)) with hA
  have hA0 : 0 ≤ A := by positivity
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  set A' : ℝ := 2 * (C * A * (N : ℝ) ^ (-(1 / 2 : ℝ))) with hA'
  have hA'0 : 0 ≤ A' := by positivity
  have hTB : ∀ i : ℕ, i ≤ 2 → ∀ v : ℝ, (j : ℝ) ≤ v →
      TestBound (testOrder d) A (r26t8a_ageTest a beta m rho alpha i v) := by
    intro i hi v hv
    have := horb.bound alpha v (le_trans hj0 hv) i hi
    refine r26t8a_o03b_tb_mono this ?_
    have : Real.exp (-c * v) ≤ Real.exp (-c * (j : ℝ)) := Real.exp_le_exp.2 (by nlinarith)
    rw [hA]
    exact mul_le_mul_of_nonneg_left this (mul_nonneg hCf hW0)
  have hVn : ∀ (i : ℕ), i ≤ 1 → ∀ r : ℝ, 0 ≤ r → ∀ v : ℝ, (j : ℝ) ≤ v →
      MemLp (fun w => r26t8a_VAge a beta m rho Psi alpha i v (X r.toNNReal w)) 2 P ∧
      eLpNorm (fun w => r26t8a_VAge a beta m rho Psi alpha i v (X r.toNNReal w)) 2 P ≤ ENNReal.ofReal A' :=
    fun i hi r hr v hv => r26t8a_b02_Vnorm d N hd hN a beta m M C ha hbeta hM hC rho hrho Psi hPsi P X0 W X hX r hr
      alpha m i v (hTB i (by omega) v hv) (hTB (i + 1) (by omega) v hv)
  have hlA : ∀ r ∈ Set.Icc l h, (j : ℝ) ≤ a0 - r := fun r hr => by linarith [hr.2]
  have hha0 : h ≤ a0 := by linarith
  -- hypotheses of the rectangle estimate
  have hm := r26t8a_b02_Vmeas d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb alpha 0
    (by norm_num) P X0 W X hX a0 l h T hl hha0
  have hdm := r26t8a_b02_Vmeas d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb alpha 1
    (by norm_num) P X0 W X hX a0 l h T hl hha0
  have hzero : ∀ r ∈ Set.Icc l h, MemLp ((fun (t r : ℝ) (w : Omega) =>
      r26t8a_VAge a beta m rho Psi alpha 0 (a0 + t - r) (X r.toNNReal w)) 0 r) 2 P ∧
      eLpNorm ((fun (t r : ℝ) (w : Omega) => r26t8a_VAge a beta m rho Psi alpha 0 (a0 + t - r) (X r.toNNReal w)) 0 r)
        2 P ≤ ENNReal.ofReal A' := by
    intro r hr
    have := hVn 0 (by norm_num) r (hl.trans hr.1) (a0 + 0 - r) (by simpa using hlA r hr)
    exact this
  have hder : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ r ∈ Set.Icc l h, MemLp ((fun (t r : ℝ) (w : Omega) =>
      r26t8a_VAge a beta m rho Psi alpha 1 (a0 + t - r) (X r.toNNReal w)) t r) 2 P ∧
      eLpNorm ((fun (t r : ℝ) (w : Omega) => r26t8a_VAge a beta m rho Psi alpha 1 (a0 + t - r) (X r.toNNReal w)) t r)
        2 P ≤ ENNReal.ofReal A' := by
    intro t ht r hr
    exact hVn 1 le_rfl r (hl.trans hr.1) (a0 + t - r) (by linarith [hlA r hr, ht.1])
  have hFTC : ∀ᵐ p ∂((volume.restrict (Set.Icc l h)).prod P),
      IntegrableOn (fun v => (fun (t r : ℝ) (w : Omega) =>
        r26t8a_VAge a beta m rho Psi alpha 1 (a0 + t - r) (X r.toNNReal w)) v p.1 p.2) (Set.Icc 0 T) ∧
      ∀ t ∈ Set.Icc 0 T, (fun (t r : ℝ) (w : Omega) =>
        r26t8a_VAge a beta m rho Psi alpha 0 (a0 + t - r) (X r.toNNReal w)) t p.1 p.2 =
        (fun (t r : ℝ) (w : Omega) => r26t8a_VAge a beta m rho Psi alpha 0 (a0 + t - r) (X r.toNNReal w)) 0 p.1 p.2 +
          ∫ v in Set.Icc 0 t, (fun (t r : ℝ) (w : Omega) =>
            r26t8a_VAge a beta m rho Psi alpha 1 (a0 + t - r) (X r.toNNReal w)) v p.1 p.2 := by
    have hr1 : ∀ᵐ r ∂(volume.restrict (Set.Icc l h)), r ∈ Set.Icc l h := ae_restrict_mem measurableSet_Icc
    have hg := r26t8a_b02_ae_good d N a beta P X0 W X hX h
    have h1' : ∀ᵐ p ∂((volume.restrict (Set.Icc l h)).prod P), p.1 ∈ Set.Icc l h :=
      (Measure.quasiMeasurePreserving_fst (μ := volume.restrict (Set.Icc l h)) (ν := P)).ae hr1
    have h2' : ∀ᵐ p ∂((volume.restrict (Set.Icc l h)).prod P),
        ∀ r : ℝ, 0 ≤ r → r ≤ h → X r.toNNReal p.2 ∉ eucCollisionSet d N :=
      (Measure.quasiMeasurePreserving_snd (μ := volume.restrict (Set.Icc l h)) (ν := P)).ae hg
    filter_upwards [h1', h2'] with p hp1 hp2
    have hr0 : 0 ≤ p.1 := hl.trans hp1.1
    obtain ⟨hc1, hftc⟩ := r26t8a_b02_ftc d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb alpha
      (X p.1.toNNReal p.2) (hp2 p.1 hr0 hp1.2) (a0 - p.1) T (by linarith [hp1.2])
    have hrw : ∀ t : ℝ, a0 + t - p.1 = (a0 - p.1) + t := fun t => by ring
    refine ⟨?_, fun t ht => ?_⟩
    · simp only [hrw]
      exact hc1.integrableOn_Icc
    · simp only [hrw]
      exact hftc t ht
  have hT0 := hT
  obtain ⟨hmeas, hsup⟩ := r26t8a_rectangle_drift P l h T A' hlh hT hA'0
    (fun t r w => r26t8a_VAge a beta m rho Psi alpha 0 (a0 + t - r) (X r.toNNReal w))
    (fun t r w => r26t8a_VAge a beta m rho Psi alpha 1 (a0 + t - r) (X r.toNNReal w))
    hm hdm hzero hder hFTC
  refine ⟨hmeas, hsup.trans ?_⟩
  refine ENNReal.ofReal_le_ofReal ?_
  have hl0 : 0 ≤ h - l := sub_nonneg.2 hlh
  have hexp : 0 ≤ (C * Cf * w0 * (N : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (-c * (j : ℝ))) := by positivity
  have e1 : (2 * C * Cf * (1 + T)) * w0 * (N : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (-c * (j : ℝ)) =
      (1 + T) * A' := by
    rw [hA', hA]; ring
  rw [e1]
  have : (h - l) * (1 + T) * A' ≤ 1 * (1 + T) * A' := by
    gcongr
  linarith

end HRS.MS.R26T8A

end

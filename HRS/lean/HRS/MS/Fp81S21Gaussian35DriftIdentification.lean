import HRS.MS.Fp81S21GaussianDriftPhysical
import HRS.MS.Fp81S21GaussianFieldsRetained

/-! Packet 35, unit 3: physical drift of an already-selected quadratic family.
The Gaussian realization can be the retained source's `G0`; no selection record
or particle premise is needed. Charts precede the radius, and operator constants
precede the window start. The history premise is exactly the selected payload's
`TimeL2Rep`. The weighted variation bound is proved from `O.drift_norm`: the
existing `gaussian_Dcum_physical` exports the other four conclusions only. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.S111K2

local instance fp81s21_Gaussian35DriftIdentification_inst1 (H : ℝ) :
    MeasurableSpace (Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) H))) := borel _
local instance fp81s21_Gaussian35DriftIdentification_inst2 (H : ℝ) :
    BorelSpace (Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) H))) := ⟨rfl⟩

private theorem fp81s21_gaussian35_drift_variation
    {d k : ℕ} {Pw : ℝ} {E : r26t6_WeightedChart d k Pw} {C : WholeCoeff d}
    {T a c K : ℝ} (O : r26t6_IntervalOperators E C T a c K)
    (hc : 0 ≤ c) (hK : 0 ≤ K) (q : r26t6_TimeCoeff (a + T))
    {v r : ℝ} (hv : 0 ≤ v) (hvr : v ≤ r) (hr : r ≤ a + T) :
    eVariationOn (fun s => O.drift 0 s q) (Icc v r) ≤
      ENNReal.ofReal (K * ∫ s in Ioc v r, s111k2_age c a s * ‖q s‖) := by
  let w : ℝ → ℝ := fun s => s111k2_age c a s * ‖q s‖
  let g : ℝ → ℝ := fun t => K * ∫ s in v..t, w s
  have hbase : IntegrableOn (fun s => ‖q s‖) (Icc (0 : ℝ) (a + T)) volume :=
    (Lp.memLp q).integrable le_rfl |>.norm
  have hAgeMeas : Measurable (fun s => s111k2_age c a s) := by
    unfold s111k2_age
    fun_prop
  have hAgeBound : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) (a + T)),
      ‖s111k2_age c a s‖ ≤ 1 := by
    filter_upwards with s
    have hage := fp81s21_age_bounds (u := a) hc s
    rw [Real.norm_eq_abs, abs_of_nonneg hage.1]
    exact hage.2
  have hwInt : IntegrableOn w (Icc (0 : ℝ) (a + T)) volume := by
    have hmul := hbase.bdd_mul hAgeMeas.aestronglyMeasurable hAgeBound
    change Integrable w (volume.restrict (Icc (0 : ℝ) (a + T)))
    simpa [w, mul_comm] using hmul
  have hwNonneg : ∀ s, 0 ≤ w s := fun s =>
    mul_nonneg (fp81s21_age_bounds (u := a) hc s).1 (norm_nonneg _)
  have hwInterval : ∀ x y, x ∈ Icc (0 : ℝ) (a + T) →
      y ∈ Icc (0 : ℝ) (a + T) → x ≤ y → IntervalIntegrable w volume x y := by
    intro x y hx hy hxy
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hxy).2
    exact hwInt.mono_set (Icc_subset_Icc hx.1 hy.2)
  have hcontrolDiff : ∀ s t, s ∈ Icc v r → t ∈ Icc v r → s ≤ t →
      g t - g s = K * ∫ x in Ioc s t, w x := by
    intro s t hs ht hst
    have hsH : s ∈ Icc (0 : ℝ) (a + T) := ⟨hv.trans hs.1, hs.2.trans hr⟩
    have htH : t ∈ Icc (0 : ℝ) (a + T) := ⟨hv.trans ht.1, ht.2.trans hr⟩
    have hvH : v ∈ Icc (0 : ℝ) (a + T) := ⟨hv, hvr.trans hr⟩
    have hsum := intervalIntegral.integral_add_adjacent_intervals
      (hwInterval v s hvH hsH hs.1) (hwInterval s t hsH htH hst)
    rw [intervalIntegral.integral_of_le hst] at hsum
    dsimp [g]
    rw [← hsum]
    ring
  have hmono : MonotoneOn g (Icc v r) := by
    intro s hs t ht hst
    have hn : 0 ≤ ∫ x in Ioc s t, w x := integral_nonneg hwNonneg
    have heq := hcontrolDiff s t hs ht hst
    have hnK := mul_nonneg hK hn
    linarith
  have hinc : ∀ s ∈ Icc v r, ∀ t ∈ Icc v r, s ≤ t →
      ‖O.drift 0 t q - O.drift 0 s q‖ ≤ g t - g s := by
    intro s hs t ht hst
    have hs0 := hv.trans hs.1
    have htH := ht.2.trans hr
    have hadd := congrArg (fun F => F q) (O.drift_add 0 s t le_rfl hs0 hst htH)
    have heq : O.drift 0 t q - O.drift 0 s q = O.drift s t q := by
      change O.drift 0 t q = O.drift 0 s q + O.drift s t q at hadd
      rw [hadd]
      abel
    rw [heq, hcontrolDiff s t hs ht hst]
    exact O.drift_norm s t hs0 hst htH q
  have hcompare : eVariationOn (fun s => O.drift 0 s q) (Icc v r) ≤
      eVariationOn g (Icc v r) := by
    unfold eVariationOn
    apply iSup_le
    rintro ⟨n, x, hx, hxs⟩
    calc
      _ ≤ ∑ i ∈ Finset.range n, edist (g (x (i + 1))) (g (x i)) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [edist_dist, dist_eq_norm, edist_dist, Real.dist_eq,
          abs_of_nonneg (sub_nonneg.mpr (hmono (hxs i) (hxs (i + 1)) (hx (Nat.le_succ i))))]
        exact ENNReal.ofReal_le_ofReal
          (hinc (x i) (hxs i) (x (i + 1)) (hxs (i + 1)) (hx (Nat.le_succ i)))
      _ ≤ eVariationOn g (Icc v r) := eVariationOn.sum_le hx hxs
  have hscalar : eVariationOn g (Icc v r) = ENNReal.ofReal (g r - g v) := by
    simpa only [inter_self] using hmono.eVariationOn_eq
      (show v ∈ Icc v r from ⟨le_rfl, hvr⟩)
      (show r ∈ Icc v r from ⟨hvr, le_rfl⟩)
  rw [hscalar, hcontrolDiff v r ⟨le_rfl, hvr⟩ ⟨hvr, le_rfl⟩ hvr] at hcompare
  exact hcompare

/-- Literal weighted-drift identification and all cumulative regularity for any
already-selected quadratic physical family and compatible history. -/
theorem fp81s21_gaussian35_D_physical
    (p : Parameters)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2)) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ R : Trajectory p δ,
      ∀ (εB : ℕ → ℝ) (S : fp81s21_QuadraticPhysical31 p R Es E εB)
        (G : GaussianRealization R) (c K : ℝ), 0 ≤ c → 0 ≤ K →
      ∀ (a : ℝ) (ha : 0 ≤ a)
        (O : r26t6_IntervalOperators E (r26t3_coeff R) p.T a c K)
        (UB : G.Ω → Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) (a + p.T)))),
      fp81s21_TimeL2Rep G.P (S.qe G) (S.Kstar ^ 4 * S.B / 2) 0 (a + p.T) UB →
      let VB := fun ω => fp81s21_timeL2L1 (a + p.T) (add_nonneg ha p.hT.le) (UB ω)
      let Dcum := fp81s21_gaussian_Dcum O (add_nonneg ha p.hT.le) UB
      let QB := fun s ω f => fp81s21_chartAction E (S.qe G s ω) f
      (∀ v r, 0 ≤ v → v ≤ r → r ≤ a + p.T →
        (fun ω => Dcum r ω - Dcum v ω) =ᵐ[G.P]
          fun ω => fp81s21_weightedDrift_windowInc ha le_rfl (r26t3_coeff R)
            (fun s f => QB s ω f) v r) ∧
      ((∀ r, AEStronglyMeasurable (Dcum r) G.P) ∧
        (∀ ω, ContinuousOn (fun r => Dcum r ω) (Icc 0 (a + p.T)) ∧
          BoundedVariationOn (fun r => Dcum r ω) (Icc 0 (a + p.T))) ∧
        (∀ v r, 0 ≤ v → v ≤ r → r ≤ a + p.T → ∀ ω,
          Dcum r ω - Dcum v ω = O.drift v r (VB ω)) ∧
        (∀ v r, 0 ≤ v → v ≤ r → r ≤ a + p.T → ∀ ω,
          eVariationOn (fun s => Dcum s ω) (Icc v r) ≤
            ENNReal.ofReal (K * ∫ s in Ioc v r, s111k2_age c a s * ‖VB ω s‖))) := by
  obtain ⟨δ₀, hδ₀, hδhalf, hstd⟩ := fp81s21_moving_std p
  refine ⟨δ₀, hδ₀, hδhalf, ?_⟩
  intro δ hδ hδle R εB S G c K hc hK a ha O UB hUB
  dsimp only
  have hH : 0 < a + p.T := add_pos_of_nonneg_of_pos ha p.hT
  have hPw : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by
    linarith [Nat.cast_nonneg p.d (α := ℝ)]
  obtain ⟨coef, hdata⟩ := hstd δ hδ hδle R a ha
  have hchart := fp81s21_moving_charted_orbits p R hH hdata hPw E
  have hB0 := fp81s21_quadraticPhysical31_zero_mass p R Es E S G (a + p.T) hH.le
  obtain ⟨hmeas, hreg, hadd, hphys⟩ :=
    fp81s21_gaussian_Dcum_physical E (r26t3_coeff R) G.P (S.qe G)
      (S.Kstar ^ 4 * S.B / 2) a p.T c K ha p.hT hc hK O coef hdata.hD
      (fp81s21_S102Lin p R (a + p.T)) hchart hPw UB hUB hB0
  refine ⟨hphys, hmeas, hreg, hadd, ?_⟩
  intro v r hv hvr hr ω
  exact fp81s21_gaussian35_drift_variation O hc hK
    (fp81s21_timeL2L1 (a + p.T) (add_nonneg ha p.hT.le) (UB ω)) hv hvr hr

#print axioms fp81s21_gaussian35_drift_variation
#print axioms fp81s21_gaussian35_D_physical
end HRS.Fp81.S21

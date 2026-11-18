import HRS.MS.Fp81S21HilbertMart5

/-!
# HRS S2.1(iii), B7: squared trace moment

The higher marginal weight controls the square of the empirical gradient-noise
trace.  This is the first stage of the shifted fourth-increment estimate.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open Classical MeasureTheory
open scoped ENNReal RealInnerProductSpace BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6

/-- The squared Hilbert--Schmidt trace of the B6-i noise has a uniform
fixed-time moment bound.  The fourth marginal weight is the square of the
weight in the pointwise gradient trace estimate. -/
theorem fp81s21_b7_squaredTraceMoment
    (p : Parameters)
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2)) :
    ∃ δstar : ℝ, 0 < δstar ∧ δstar ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δstar → ∀ R : Trajectory p δ,
        ∃ Cdouble : ℝ, 0 ≤ Cdouble ∧
          ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N, ∀ Fp : FilteredParticle A,
            ∀ u : ℝ, 0 ≤ u →
              Integrable
                (fun ω => (∑ ia : Fin N × Fin p.d,
                  ‖fp81s21_b6i_gradientNoise p E A Fp u ω ia‖ ^ 2) ^ 2) A.P ∧
              (∫ ω, (∑ ia : Fin N × Fin p.d,
                  ‖fp81s21_b6i_gradientNoise p E A Fp u ω ia‖ ^ 2) ^ 2 ∂A.P) ≤
                (2 * p.β⁻¹ * Classical.choose
                  (fp81s21_gradient_feature
                    (Nat.le_trans (by decide : 1 ≤ 2) p.hd) E)) ^ 2 * Cdouble := by
  obtain ⟨δstar, hδstar, hδhalf, hweights⟩ :=
    fp81s21_uniform_higher_marginal_weights p
  refine ⟨δstar, hδstar, hδhalf, ?_⟩
  intro δ hδ hδle R
  let highExp : ℝ := 4 * ((p.d : ℝ) + 2)
  obtain ⟨Cdouble, hCdouble, hweight⟩ :=
    hweights δ hδ hδle R highExp (by positivity)
  refine ⟨Cdouble, hCdouble, ?_⟩
  intro N hN A Fp u hu
  let lowExp : ℝ := 2 * ((p.d : ℝ) + 2)
  let w : Euc p.d → ℝ := fun x => jbracket x ^ lowExp
  let g : Euc p.d → ℝ := fun x => jbracket x ^ highExp
  let Z := fp81s21_b6i_gradientNoise p E A Fp
  let K : ℝ := 2 * p.β⁻¹ * Classical.choose
    (fp81s21_gradient_feature (Nat.le_trans (by decide : 1 ≤ 2) p.hd) E)
  let v : A.Ω → ℝ := fun ω => (N : ℝ)⁻¹ *
    ∑ i : Fin N, g (A.X (Real.toNNReal u) ω i)
  let qA : A.Ω → ℝ := fun ω => (N : ℝ)⁻¹ *
    ∑ i : Fin N, w (A.X (Real.toNNReal u) ω i)
  let qF : A.Ω → ℝ := fun ω => (N : ℝ)⁻¹ *
    ∑ i : Fin N, w (Fp.X (Real.toNNReal u) ω i)
  let tr : A.Ω → ℝ := fun ω =>
    ∑ ia : Fin N × Fin p.d, ‖Z u ω ia‖ ^ 2

  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (inv_nonneg.mpr p.hβ.le))
      (Classical.choose_spec
        (fp81s21_gradient_feature
          (Nat.le_trans (by decide : 1 ≤ 2) p.hd) E)).1
  have hpow : ∀ x : Euc p.d, w x ^ 2 = g x := by
    intro x
    have hj : 0 < jbracket x := lt_of_lt_of_le zero_lt_one
      (HRS.MS.R2Poly.s95_one_le_jb x)
    change (jbracket x ^ lowExp) ^ 2 = jbracket x ^ highExp
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hj)]
    congr 1
    dsimp [lowExp, highExp]
    ring
  have hgMeas : Measurable g := by
    dsimp [g]
    exact (measurable_id.pow_const highExp).comp (by fun_prop)
  have hgNonneg : ∀ x, 0 ≤ g x := by
    intro x
    exact Real.rpow_nonneg (Real.sqrt_nonneg _) _

  have hXmeas : Measurable (A.X (Real.toNNReal u)) :=
    (A.strong (max 1 u)).adapted _
  obtain ⟨hweightInt, hweightBound⟩ := hweight N hN A u hu
  have hweightInt' : Integrable g
      (HRS.Whole.meanEmpirical (A.P.map (A.X (Real.toNNReal u)))) := by
    simpa [g, highExp] using hweightInt
  have hEmp := HRS.MS.R2Interp.s102_empMoment
    (show 0 < N by omega) A.P (A.X (Real.toNNReal u)) hXmeas
    hgMeas hgNonneg hweightInt'
  have hvInt : Integrable v A.P := by
    simpa [v, g] using hEmp.1
  have hvBound : (∫ ω, v ω ∂A.P) ≤ Cdouble := by
    calc
      (∫ ω, v ω ∂A.P) =
          ∫ x, g x ∂(HRS.Whole.meanEmpirical
            (A.P.map (A.X (Real.toNNReal u)))) := by
              simpa [v, g] using hEmp.2
      _ ≤ Cdouble := hweightBound
  have hvNonneg : ∀ ω, 0 ≤ v ω := by
    intro ω
    apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    exact Finset.sum_nonneg fun i _ => hgNonneg _
  have hqANonneg : ∀ ω, 0 ≤ qA ω := by
    intro ω
    apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    exact Finset.sum_nonneg fun i _ => Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hJensen : ∀ ω, qA ω ^ 2 ≤ v ω := by
    intro ω
    have hj := _root_.sum_div_card_sq_le_sum_sq_div_card
      (s := (Finset.univ : Finset (Fin N)))
      (f := fun i => w (A.X (Real.toNNReal u) ω i))
    have hj' :
        ((∑ i : Fin N, w (A.X (Real.toNNReal u) ω i)) / (N : ℝ)) ^ 2 ≤
          (∑ i : Fin N, w (A.X (Real.toNNReal u) ω i) ^ 2) / (N : ℝ) := by
      simpa [Finset.card_univ] using hj
    have hqEq : qA ω =
        (∑ i : Fin N, w (A.X (Real.toNNReal u) ω i)) / (N : ℝ) := by
      dsimp [qA]
      rw [div_eq_mul_inv]
      ring
    calc
      qA ω ^ 2 =
          ((∑ i : Fin N, w (A.X (Real.toNNReal u) ω i)) / (N : ℝ)) ^ 2 := by
            rw [hqEq]
      _ ≤ (∑ i : Fin N, w (A.X (Real.toNNReal u) ω i) ^ 2) / (N : ℝ) := hj'
      _ = v ω := by
            rw [show (∑ i : Fin N, w (A.X (Real.toNNReal u) ω i) ^ 2) =
              ∑ i : Fin N, g (A.X (Real.toNNReal u) ω i) by
                exact Finset.sum_congr rfl fun i _ => hpow _]
            dsimp [v]
            rw [div_eq_mul_inv]
            ring

  have hprog : ∀ ia : Fin N × Fin p.d,
      IsProgressive Fp.ℱ (fun r ω => Z r ω ia) := by
    intro ia
    simpa [Z, fp81s21_b6i_gradientNoise] using
      fp81s21_b6i_gradient_noise_progressive p A Fp E ia
  have htrMeas : Measurable tr := by
    dsimp [tr]
    refine Finset.measurable_sum _ fun ia _ => ?_
    have hcoord : Measurable (fun ω : A.Ω => Z u ω ia) :=
      (HRS.MRep.isProgressive_measurable_uncurry (hprog ia)).comp
        (measurable_const.prodMk measurable_id)
    exact (measurable_norm.comp hcoord).pow_const 2
  have htrNonneg : ∀ ω, 0 ≤ tr ω := by
    intro ω
    exact Finset.sum_nonneg fun ia _ => sq_nonneg _
  have htraceBound : ∀ᵐ ω ∂A.P, tr ω ≤ K * qA ω := by
    filter_upwards [fp81s21_b6i_filtered_path_agreement A Fp] with ω hpath
    have hpoint := fp81s21_b6i_gradient_noise_trace_bound p hN E
      (Fp.X (Real.toNNReal u) ω)
    have hraw : tr ω ≤
        (2 * p.β⁻¹ / (N : ℝ)) *
          Classical.choose (fp81s21_gradient_feature
            (Nat.le_trans (by decide : 1 ≤ 2) p.hd) E) *
          ∑ i : Fin N, jbracket (Fp.X (Real.toNNReal u) ω i) ^ lowExp := by
      simpa [tr, Z, fp81s21_b6i_gradientNoise, lowExp] using hpoint
    have hq : qF ω = qA ω := by
      change (N : ℝ)⁻¹ * ∑ i : Fin N, w (Fp.X (Real.toNNReal u) ω i) =
        (N : ℝ)⁻¹ * ∑ i : Fin N, w (A.X (Real.toNNReal u) ω i)
      exact congrArg (fun X : EucConfig p.d N =>
        (N : ℝ)⁻¹ * ∑ i : Fin N, w (X i)) (hpath u)
    have hbound : tr ω ≤ K * qF ω := by
      calc
        tr ω ≤
            (2 * p.β⁻¹ / (N : ℝ)) *
              Classical.choose (fp81s21_gradient_feature
                (Nat.le_trans (by decide : 1 ≤ 2) p.hd) E) *
              ∑ i : Fin N, jbracket (Fp.X (Real.toNNReal u) ω i) ^ lowExp := hraw
        _ = K * qF ω := by dsimp [K, qF, w]; ring
    rw [hq] at hbound
    exact hbound
  have htrSqBound : ∀ᵐ ω ∂A.P, tr ω ^ 2 ≤ K ^ 2 * v ω := by
    filter_upwards [htraceBound] with ω htr
    have hKq : 0 ≤ K * qA ω := mul_nonneg hK (hqANonneg ω)
    have hprod := mul_nonneg (sub_nonneg.mpr htr)
      (add_nonneg hKq (htrNonneg ω))
    have hsquare : tr ω ^ 2 ≤ (K * qA ω) ^ 2 := by nlinarith
    calc
      tr ω ^ 2 ≤ (K * qA ω) ^ 2 := hsquare
      _ = K ^ 2 * qA ω ^ 2 := by ring
      _ ≤ K ^ 2 * v ω := mul_le_mul_of_nonneg_left (hJensen ω) (sq_nonneg K)
  have hmajorInt : Integrable (fun ω => K ^ 2 * v ω) A.P :=
    hvInt.const_mul (K ^ 2)
  have htrSqInt : Integrable (fun ω => tr ω ^ 2) A.P :=
    Integrable.mono' hmajorInt (htrMeas.pow_const 2).aestronglyMeasurable
      (by
        filter_upwards [htrSqBound] with ω hω
        simpa only [Real.norm_of_nonneg (sq_nonneg (tr ω)),
          Real.norm_of_nonneg (mul_nonneg (sq_nonneg K) (hvNonneg ω))] using hω)
  refine ⟨?_, ?_⟩
  · simpa [tr, Z, fp81s21_b6i_gradientNoise] using htrSqInt
  · calc
      (∫ ω, tr ω ^ 2 ∂A.P) ≤ ∫ ω, K ^ 2 * v ω ∂A.P :=
        integral_mono_ae htrSqInt hmajorInt htrSqBound
      _ = K ^ 2 * (∫ ω, v ω ∂A.P) := by rw [integral_const_mul]
      _ ≤ K ^ 2 * Cdouble := mul_le_mul_of_nonneg_left hvBound (sq_nonneg K)

end HRS.Fp81.S21

#print axioms HRS.Fp81.S21.fp81s21_b7_squaredTraceMoment

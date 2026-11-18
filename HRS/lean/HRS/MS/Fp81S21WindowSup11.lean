import HRS.MS.Fp81S21WindowSup10
import HRS.MS.QsfStein3
import HRS.MS.WsStatAux14

/-!
# HRS S2.1(iii), SOL40 packet 9d: centered-coordinate FTC on a shifted window

Compiled source definitions used below:

* `s102_zf P X ω b f = Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical (X b.toNNReal ω)) f -
  HRS.Whole.pair (HRS.Whole.meanEmpirical (P.map (X b.toNNReal))) f)`.
* `s101Th C m T b s α x` is `s101Dt C m T b s α x` when `b < s ≤ T`, and
  zero otherwise. `s101_ftc` gives the orbit increment as its interval
  integral.
* `HRS.Whole.pair (HRS.Whole.empirical Z) f = (N : ℝ)⁻¹ * ∑ i, f (Z i)`, and
  `s21_E_pair_emp` identifies the expectation of this HRS.Whole.empirical pairing with
  the `HRS.Whole.meanEmpirical` pairing.

We use the compiled `s101Th` derivative family in the integral. The pathwise
identity is exact, and the endpoint cutoff is already part of that source
identity. Joint measurability and boundedness justify exchanging the finite
particle expectation with the interval integral.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Set
open scoped NNReal
open HRS.Whole HRS.MS.CovMeas HRS.MS.R2Interp HRS.MS.S21

namespace HRS.Fp81.S21

/-- The exactly centered HRS.Whole.empirical coordinate commutes with terminal-time
integration on a finite shifted window. -/
theorem fp81s21_window_s102_zf_ftc
    {d N : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → EucConfig d N)
    {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ}
    (hD : S101Data C m T r c)
    {b t : ℝ} (hb : b ∈ Icc (0 : ℝ) T) (ht : t ∈ Icc b T)
    (hX : Measurable (X b.toNNReal)) (hN : 0 < N)
    (α : MultiIndex d) (ω : Ω) :
    s102_zf P X ω b (propagatorW C b t (oscTestFun m α)) =
      s102_zf P X ω b (propagatorW C b b (oscTestFun m α)) +
        ∫ s in b..t, s102_zf P X ω b
          (fun x => s101Th C m T b s α x) := by
  classical
  let Xb : Ω → EucConfig d N := X b.toNNReal
  let μbar : Measure (Euc d) := HRS.Whole.meanEmpirical (P.map Xb)
  let f : ℝ → Euc d → ℝ := fun s => propagatorW C b s (oscTestFun m α)
  let q : ℝ → Euc d → ℝ := fun s x => s101Th C m T b s α x
  have hN1 : 1 ≤ N := by omega
  have hμmap : IsProbabilityMeasure (P.map Xb) :=
    (Measure.isProbabilityMeasure_map_iff hX.aemeasurable).2 inferInstance
  have hμbar : IsProbabilityMeasure μbar :=
    HRS.Whole.meanEmpirical_isProbabilityMeasure (P.map Xb) hN1
  have hc0 : 0 ≤ c α := hD.nonneg α
  have hOrbitBound (s : ℝ) (hs : s ∈ Icc b T) (x : Euc d) :
      |f s x| ≤ c α := by
    have h := hD.bddU α b hb s hs 0 (by omega) x
    simpa [f, norm_iteratedFDeriv_zero, Real.norm_eq_abs] using h
  have hQBound (s : ℝ) (x : Euc d) : |q s x| ≤ c α := by
    exact s101_th_bound hD hb s α x
  have hQJoint : Measurable (Function.uncurry q) := by
    change Measurable (fun z : ℝ × Euc d => s101Th C m T b z.1 α z.2)
    exact fp81s21_s101Th_joint_measurable hD hb α
  have hQx (s : ℝ) : Measurable (q s) := by
    exact hQJoint.comp (measurable_const.prodMk measurable_id)
  have hOrbitMeas (s : ℝ) (hs : s ∈ Icc b T) : Measurable (f s) :=
    (hD.smoothU α b hb s hs).continuous.measurable
  have hEmpJoint : Measurable (fun z : ℝ × Ω =>
      HRS.Whole.pair (HRS.Whole.empirical (Xb z.2)) (q z.1)) := by
    have hFormula : (fun z : ℝ × Ω => HRS.Whole.pair (HRS.Whole.empirical (Xb z.2)) (q z.1)) =
        fun z => (N : ℝ)⁻¹ * ∑ i : Fin N, q z.1 (Xb z.2 i) := by
      funext z
      exact HRS.Whole.pair_empirical hN (Xb z.2) (q z.1)
    rw [hFormula]
    apply measurable_const.mul
    refine Finset.measurable_sum _ fun i hi => ?_
    exact hQJoint.comp (measurable_fst.prodMk
      ((measurable_pi_apply i).comp (hX.comp measurable_snd)))
  have hEmpBound (s : ℝ) (ω' : Ω) :
      |HRS.Whole.pair (HRS.Whole.empirical (Xb ω')) (q s)| ≤ c α :=
    S45.s45_abs_pair_empirical_le hN1 (hQBound s) (Xb ω')
  have hEmpAtIntegrable (s : ℝ) :
      Integrable (fun ω' => HRS.Whole.pair (HRS.Whole.empirical (Xb ω')) (q s)) P := by
    refine Integrable.of_bound
      ((hEmpJoint.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      (c α) ?_
    exact Filter.Eventually.of_forall fun ω' => by
      rw [Real.norm_eq_abs]
      exact hEmpBound s ω'
  have hEmpMeanAt (s : ℝ) :
      (∫ ω', HRS.Whole.pair (HRS.Whole.empirical (Xb ω')) (q s) ∂P) = HRS.Whole.pair μbar (q s) := by
    exact s21_E_pair_emp hN1 P Xb hX (P.map Xb) rfl (hQx s) (hQBound s)
  have hMeanMeas : Measurable (fun s : ℝ => HRS.Whole.pair μbar (q s)) := by
    have hIntMeas : Measurable (fun s : ℝ =>
        ∫ ω', HRS.Whole.pair (HRS.Whole.empirical (Xb ω')) (q s) ∂P) := by
      change Measurable (fun s : ℝ => ∫ ω', Function.uncurry
        (fun s ω => HRS.Whole.pair (HRS.Whole.empirical (Xb ω)) (q s)) (s, ω') ∂P)
      exact (hEmpJoint.stronglyMeasurable.integral_prod_right' (ν := P)).measurable
    have heq : (fun s : ℝ => HRS.Whole.pair μbar (q s)) =
        (fun s => ∫ ω', HRS.Whole.pair (HRS.Whole.empirical (Xb ω')) (q s) ∂P) := by
      funext s
      exact (hEmpMeanAt s).symm
    rw [heq]
    exact hIntMeas
  have hMeanBound (s : ℝ) (hs : s ∈ Icc b T) :
      |HRS.Whole.pair μbar (q s)| ≤ c α := by
    rw [← hEmpMeanAt s]
    calc
      |∫ ω', HRS.Whole.pair (HRS.Whole.empirical (Xb ω')) (q s) ∂P| ≤
          ∫ ω', |HRS.Whole.pair (HRS.Whole.empirical (Xb ω')) (q s)| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ ω', c α ∂P := integral_mono_ae (hEmpAtIntegrable s).abs
          (integrable_const (c α)) (Filter.Eventually.of_forall fun ω' => hEmpBound s ω')
      _ = c α := by simp
  have hEmpTimeInterval :
      IntervalIntegrable (fun s => HRS.Whole.pair (HRS.Whole.empirical (Xb ω)) (q s)) volume b t := by
    have hm := hEmpJoint.comp (measurable_id.prodMk
      (measurable_const : Measurable fun _ : ℝ => ω))
    have haesm : AEStronglyMeasurable (fun s => HRS.Whole.pair (HRS.Whole.empirical (Xb ω)) (q s)) volume :=
      hm.aestronglyMeasurable
    rw [intervalIntegrable_iff]
    refine Measure.integrableOn_of_bounded (M := c α) measure_Ioc_lt_top.ne haesm ?_
    exact Filter.Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs]
      exact hEmpBound s ω
  have hMeanTimeInterval :
      IntervalIntegrable (fun s => HRS.Whole.pair μbar (q s)) volume b t := by
    have haesm := hMeanMeas.aestronglyMeasurable (μ := volume)
    rw [intervalIntegrable_iff]
    refine Measure.integrableOn_of_bounded (M := c α) measure_Ioc_lt_top.ne haesm ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [Real.norm_eq_abs]
    have hsIoc : s ∈ Ioc b t := by
      simpa [uIoc_of_le ht.1] using hs
    exact hMeanBound s ⟨hsIoc.1.le, hsIoc.2.trans ht.2⟩
  have hPairFTC (ω' : Ω) :
      HRS.Whole.pair (HRS.Whole.empirical (Xb ω')) (f t) =
        HRS.Whole.pair (HRS.Whole.empirical (Xb ω')) (f b) +
          ∫ s in b..t, HRS.Whole.pair (HRS.Whole.empirical (Xb ω')) (q s) := by
    rw [HRS.Whole.pair_empirical hN (Xb ω') (f t),
      HRS.Whole.pair_empirical hN (Xb ω') (f b)]
    have hpoint (i : Fin N) : f t (Xb ω' i) =
        f b (Xb ω' i) + ∫ s in b..t, q s (Xb ω' i) := by
      have hftc := fp81s21_window_orbit_ftc hD hb ht α (Xb ω' i)
      dsimp [f, q] at hftc ⊢
      linarith
    have hsumFTC : (∑ i : Fin N, f t (Xb ω' i)) =
        (∑ i : Fin N, f b (Xb ω' i)) +
          ∫ s in b..t, ∑ i : Fin N, q s (Xb ω' i) := by
      calc
        _ = ∑ i : Fin N, (f b (Xb ω' i) + ∫ s in b..t, q s (Xb ω' i)) :=
          Finset.sum_congr rfl fun i hi => hpoint i
        _ = (∑ i : Fin N, f b (Xb ω' i)) +
              ∑ i : Fin N, ∫ s in b..t, q s (Xb ω' i) := by rw [Finset.sum_add_distrib]
        _ = (∑ i : Fin N, f b (Xb ω' i)) +
              ∫ s in b..t, ∑ i : Fin N, q s (Xb ω' i) := by
          congr 1
          symm
          exact intervalIntegral.integral_finsetSum fun i hi =>
            s101_th_intervalIntegrable hD hb α (Xb ω' i) b t
    calc
      (N : ℝ)⁻¹ * ∑ i : Fin N, f t (Xb ω' i) =
          (N : ℝ)⁻¹ * ((∑ i : Fin N, f b (Xb ω' i)) +
            ∫ s in b..t, ∑ i : Fin N, q s (Xb ω' i)) := by rw [hsumFTC]
      _ = (N : ℝ)⁻¹ * ∑ i : Fin N, f b (Xb ω' i) +
            ∫ s in b..t, (N : ℝ)⁻¹ * ∑ i : Fin N, q s (Xb ω' i) := by
          rw [intervalIntegral.integral_const_mul]
          ring
      _ = (N : ℝ)⁻¹ * ∑ i : Fin N, f b (Xb ω' i) +
            ∫ s in b..t, HRS.Whole.pair (HRS.Whole.empirical (Xb ω')) (q s) := by
          congr 1
          apply intervalIntegral.integral_congr
          intro s hs
          exact (HRS.Whole.pair_empirical hN (Xb ω') (q s)).symm
      _ = _ := rfl
  have hFtMeas : Measurable (fun ω' => HRS.Whole.pair (HRS.Whole.empirical (Xb ω')) (f t)) := by
    have h := hOrbitMeas t ht
    exact (S45.s45_measurable_pair_empirical hN1 h).comp hX
  have hFbMeas : Measurable (fun ω' => HRS.Whole.pair (HRS.Whole.empirical (Xb ω')) (f b)) := by
    have h := hOrbitMeas b ⟨le_rfl, hb.2⟩
    exact (S45.s45_measurable_pair_empirical hN1 h).comp hX
  have hFtBound (ω' : Ω) : |HRS.Whole.pair (HRS.Whole.empirical (Xb ω')) (f t)| ≤ c α :=
    S45.s45_abs_pair_empirical_le hN1 (hOrbitBound t ht) (Xb ω')
  have hFbBound (ω' : Ω) : |HRS.Whole.pair (HRS.Whole.empirical (Xb ω')) (f b)| ≤ c α :=
    S45.s45_abs_pair_empirical_le hN1 (hOrbitBound b ⟨le_rfl, hb.2⟩) (Xb ω')
  have hFtInt : Integrable (fun ω' => HRS.Whole.pair (HRS.Whole.empirical (Xb ω')) (f t)) P :=
    Integrable.of_bound hFtMeas.aestronglyMeasurable (c α) (Filter.Eventually.of_forall fun ω' => by
      rw [Real.norm_eq_abs]; exact hFtBound ω')
  have hFbInt : Integrable (fun ω' => HRS.Whole.pair (HRS.Whole.empirical (Xb ω')) (f b)) P :=
    Integrable.of_bound hFbMeas.aestronglyMeasurable (c α) (Filter.Eventually.of_forall fun ω' => by
      rw [Real.norm_eq_abs]; exact hFbBound ω')
  have hPathInt : Integrable (fun ω' => HRS.Whole.pair (HRS.Whole.empirical (Xb ω')) (f b) +
      ∫ s in b..t, HRS.Whole.pair (HRS.Whole.empirical (Xb ω')) (q s)) P := by
    exact hFtInt.congr (Filter.Eventually.of_forall fun ω' => hPairFTC ω')
  haveI hTimeFinite : IsFiniteMeasure (volume.restrict (uIoc b t)) := by
    refine ⟨?_⟩
    rw [uIoc_of_le ht.1, Measure.restrict_apply_univ]
    exact measure_Ioc_lt_top
  have hProdInt : Integrable (Function.uncurry fun s ω' =>
      HRS.Whole.pair (HRS.Whole.empirical (Xb ω')) (q s)) ((volume.restrict (uIoc b t)).prod P) := by
    refine Integrable.of_bound hEmpJoint.aestronglyMeasurable (c α) ?_
    apply Filter.Eventually.of_forall
    intro z
    rw [Real.norm_eq_abs]
    exact hEmpBound z.1 z.2
  have hSwap :
      ∫ ω', (∫ s in b..t, HRS.Whole.pair (HRS.Whole.empirical (Xb ω')) (q s)) ∂P =
        ∫ s in b..t, (∫ ω', HRS.Whole.pair (HRS.Whole.empirical (Xb ω')) (q s) ∂P) := by
    exact (intervalIntegral_integral_swap hProdInt).symm
  have hEmpIntInt : Integrable (fun ω' =>
      ∫ s in b..t, HRS.Whole.pair (HRS.Whole.empirical (Xb ω')) (q s)) P := by
    refine (hPathInt.sub hFbInt).congr (Filter.Eventually.of_forall fun ω' => ?_)
    simp
  have hMeanFTC : HRS.Whole.pair μbar (f t) = HRS.Whole.pair μbar (f b) +
      ∫ s in b..t, HRS.Whole.pair μbar (q s) := by
    have hMeanAt (s : ℝ) (hs : s ∈ Icc b T) :
        (∫ ω', HRS.Whole.pair (HRS.Whole.empirical (Xb ω')) (f s) ∂P) = HRS.Whole.pair μbar (f s) := by
      exact s21_E_pair_emp hN1 P Xb hX (P.map Xb) rfl (hOrbitMeas s hs)
        (hOrbitBound s hs)
    calc
      HRS.Whole.pair μbar (f t) = ∫ ω', HRS.Whole.pair (HRS.Whole.empirical (Xb ω')) (f t) ∂P :=
        (hMeanAt t ht).symm
      _ = ∫ ω', (HRS.Whole.pair (HRS.Whole.empirical (Xb ω')) (f b) +
            ∫ s in b..t, HRS.Whole.pair (HRS.Whole.empirical (Xb ω')) (q s)) ∂P := by
        exact integral_congr_ae (Filter.Eventually.of_forall hPairFTC)
      _ = (∫ ω', HRS.Whole.pair (HRS.Whole.empirical (Xb ω')) (f b) ∂P) +
            ∫ ω', (∫ s in b..t, HRS.Whole.pair (HRS.Whole.empirical (Xb ω')) (q s)) ∂P :=
        integral_add hFbInt hEmpIntInt
      _ = HRS.Whole.pair μbar (f b) + ∫ s in b..t, HRS.Whole.pair μbar (q s) := by
        rw [hMeanAt b ⟨le_rfl, hb.2⟩, hSwap]
        congr 1
        apply intervalIntegral.integral_congr
        intro s hs
        exact hEmpMeanAt s
  have hEmpMeanBound (s : ℝ) (hs : s ∈ Icc b T) :
      |HRS.Whole.pair μbar (q s)| ≤ c α := by
    have hMeas : Measurable (q s) := hQx s
    have hInt : Integrable (q s) μbar :=
      Integrable.of_bound hMeas.aestronglyMeasurable (c α)
        (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hQBound s x)
    change |∫ x, q s x ∂μbar| ≤ c α
    calc
      |∫ x, q s x ∂μbar| ≤ ∫ x, |q s x| ∂μbar := abs_integral_le_integral_abs
      _ ≤ ∫ x, c α ∂μbar := integral_mono_ae hInt.abs (integrable_const (c α))
          (Filter.Eventually.of_forall fun x => hQBound s x)
      _ = c α := by simp
  have hCenterFTC :
      s102_zf P X ω b (f t) - s102_zf P X ω b (f b) =
        ∫ s in b..t, s102_zf P X ω b (q s) := by
    unfold s102_zf
    rw [hPairFTC ω, hMeanFTC]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub hEmpTimeInterval hMeanTimeInterval]
    ring
  dsimp [f, q] at hCenterFTC ⊢
  linarith

#print axioms fp81s21_window_s102_zf_ftc

end HRS.Fp81.S21

end

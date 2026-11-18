import HRS.MS.Fp81S21DriftBV5
import HRS.MS.R2InterpAux3
import HRS.MS.S21G2_K06
import HRS.MS.Fp81S21MovingIntervalOpsJ
import HRS.MS.Fp81S21IntervalHistoryRep

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.S111K2 HRS.MS.R2Interp

local instance fp81s21_GaussianCovPhysical_inst1 (H : ℝ) : MeasurableSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) H))) := borel _
local instance fp81s21_GaussianCovPhysical_inst2 (H : ℝ) : BorelSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) H))) := ⟨rfl⟩
local instance fp81s21_GaussianCovPhysical_inst3 (H : ℝ) : MeasurableSpace (r26t6_TimeCoeff H) := borel _
local instance fp81s21_GaussianCovPhysical_inst4 (H : ℝ) : BorelSpace (r26t6_TimeCoeff H) := ⟨rfl⟩

/-- The cumulative covariance of the selected coefficient history, after the
canonical `L²`-to-`L¹` conversion. -/
def fp81s21_gaussian_Jcum
    {d r : ℕ} {Pw : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {E : r26t6_WeightedChart d r Pw} {C : WholeCoeff d}
    {T a c K : ℝ} (O : r26t6_IntervalOperators E C T a c K)
    (hH : 0 ≤ a + T)
    (UG : Ω → Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) (a + T)))) :
    ℝ → Ω → projTensor (R2X d T) 2 :=
  fun r ω => O.covariance 0 r (fp81s21_timeL2L1 (a + T) hH (UG ω))

private theorem fp81s21_variation_le_control_Icc
    {E : Type*} [NormedAddCommGroup E] {u v : ℝ}
    (f : ℝ → E) (g : ℝ → ℝ)
    (huv : u ≤ v)
    (hg : MonotoneOn g (Icc u v))
    (hinc : ∀ s ∈ Icc u v, ∀ t ∈ Icc u v, s ≤ t →
      ‖f t - f s‖ ≤ g t - g s) :
    eVariationOn f (Icc u v) ≤ ENNReal.ofReal (g v - g u) := by
  have hcompare : eVariationOn f (Icc u v) ≤ eVariationOn g (Icc u v) := by
    unfold eVariationOn
    apply iSup_le
    rintro ⟨n, x, hx, hxs⟩
    calc
      _ ≤ ∑ i ∈ Finset.range n, edist (g (x (i + 1))) (g (x i)) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [edist_dist, dist_eq_norm, edist_dist, Real.dist_eq,
          abs_of_nonneg (sub_nonneg.mpr (hg (hxs i) (hxs (i + 1)) (hx (Nat.le_succ i))))]
        exact ENNReal.ofReal_le_ofReal
          (hinc (x i) (hxs i) (x (i + 1)) (hxs (i + 1)) (hx (Nat.le_succ i)))
      _ ≤ eVariationOn g (Icc u v) := eVariationOn.sum_le hx hxs
  have hscalar : eVariationOn g (Icc u v) = ENNReal.ofReal (g v - g u) := by
    simpa only [inter_self] using hg.eVariationOn_eq
      (show u ∈ Icc u v from ⟨le_rfl, huv⟩)
      (show v ∈ Icc u v from ⟨huv, le_rfl⟩)
  exact hcompare.trans_eq hscalar

/-- A projective covariance tensor with the window-value formula is symmetric
under exchange of its two arguments. -/
theorem fp81s21_IsWindowJValue_symmetric
    {d : ℕ} {C : WholeCoeff d} {m H a : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} {I : Set ℝ}
    {J : TensorDual (OscPath d m H) 2}
    (hH : 0 < H) (hJ : fp81s21_IsWindowJValue C m H a z I J) :
    ∀ M : OscPath d m H [×2]→L[ℝ] ℝ,
      J M = J (M.domDomCongr (Equiv.swap 0 1)) := by
  classical
  let J' : TensorDual (OscPath d m H) 2 := J
  have hJmem : J' ∈ projTensor (OscPath d m H) 2 := hJ.1
  have hcoordSymm : ∀ (L : ℕ) (p q : ℕ × MultiIndex d),
      J' ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap
        ![s102_ellp hH L p, s102_ellp hH L q]) =
      J' ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap
        ![s102_ellp hH L q, s102_ellp hH L p]) := by
    intro L p q
    let ta : Icc (0 : ℝ) H := s102_node hH L p.1
    let tb : Icc (0 : ℝ) H := s102_node hH L q.1
    let φa : Euc d → ℝ := oscTestFun m p.2
    let φb : Euc d → ℝ := oscTestFun m q.2
    let l₁ : StrongDual ℝ (OscPath d m H) := s102_ellp hH L p
    let l₂ : StrongDual ℝ (OscPath d m H) := s102_ellp hH L q
    have hleft := hJ.2 ta tb φa φb l₁ l₂
      (s102_isDualCombo p.2) (s102_isDualCombo q.2) ta.property tb.property
      (s102_ellp_eval hH L p) (s102_ellp_eval hH L q)
    have hright := hJ.2 tb ta φb φa l₂ l₁
      (s102_isDualCombo q.2) (s102_isDualCombo p.2) tb.property ta.property
      (s102_ellp_eval hH L q) (s102_ellp_eval hH L p)
    change J' ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap
        ![l₁, l₂]) =
      J' ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap
        ![l₂, l₁])
    calc
      J' ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap
          ![l₁, l₂]) =
        2 * C.ν * ∫ (x : ℝ) in I ∩ Icc (0 : ℝ) (min (a + (ta : ℝ)) (a + (tb : ℝ))),
          z x (fun y => inner ℝ
            (gradient (propagatorW C x (a + (ta : ℝ)) φa) y)
            (gradient (propagatorW C x (a + (tb : ℝ)) φb) y)) := hleft
      _ = 2 * C.ν * ∫ (x : ℝ) in I ∩ Icc (0 : ℝ) (min (a + (tb : ℝ)) (a + (ta : ℝ))),
          z x (fun y => inner ℝ
            (gradient (propagatorW C x (a + (tb : ℝ)) φb) y)
            (gradient (propagatorW C x (a + (ta : ℝ)) φa) y)) := by
        simp only [min_comm, real_inner_comm]
      _ = J' ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap
          ![l₂, l₁]) := hright.symm
  have hfinite : ∀ (L : ℕ) (M : OscPath d m H [×2]→L[ℝ] ℝ),
      J' (M.compContinuousLinearMap fun _ => s102_Pj H hH L) =
        J' ((M.domDomCongr (Equiv.swap 0 1)).compContinuousLinearMap
          fun _ => s102_Pj H hH L) := by
    intro L M
    rw [s102_pair_expand hH L M J',
      s102_pair_expand hH L (M.domDomCongr (Equiv.swap 0 1)) J']
    let e : (Fin 2 → ℕ × MultiIndex d) ≃ (Fin 2 → ℕ × MultiIndex d) :=
      Equiv.arrowCongr (Equiv.swap 0 1) (Equiv.refl _)
    let S : Finset (Fin 2 → ℕ × MultiIndex d) :=
      Fintype.piFinset (fun _ : Fin 2 => s102_idx d L)
    have hmem : ∀ x, x ∈ S ↔ e x ∈ S := by
      intro x
      constructor <;> intro hx
      · apply Fintype.mem_piFinset.mpr
        intro i
        have hi := (Fintype.mem_piFinset.mp hx) (Equiv.swap 0 1 i)
        simpa [S, e, Equiv.arrowCongr] using hi
      · apply Fintype.mem_piFinset.mpr
        intro i
        have hi := (Fintype.mem_piFinset.mp hx) (Equiv.swap 0 1 i)
        simpa [S, e, Equiv.arrowCongr] using hi
    apply Finset.sum_equiv e (s := S) (t := S) hmem
    intro x hx
    have hM : M (fun i => s102_bpath H L (x i)) =
        (M.domDomCongr (Equiv.swap 0 1))
          (fun i => s102_bpath H L (e x i)) := by
      simp [e, Equiv.arrowCongr]
    have hJcoord :
        J' ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap
          ![s102_ellp hH L (x 0), s102_ellp hH L (x 1)]) =
        J' ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap
          ![s102_ellp hH L (e x 0), s102_ellp hH L (e x 1)]) := by
      simpa [e, Equiv.arrowCongr] using hcoordSymm L (x 0) (x 1)
    exact congrArg₂ (fun x y : ℝ => x * y) hM hJcoord
  intro M
  have ⟨_, _, hprojTensor⟩ := s102_projection_strong (d := d) m H hH
  let M' := M.domDomCongr (Equiv.swap 0 1)
  have t1 := (ContinuousLinearMap.apply ℝ ℝ M).continuous.continuousAt.tendsto.comp
    (hprojTensor 2 J' hJmem)
  have t2 := (ContinuousLinearMap.apply ℝ ℝ M').continuous.continuousAt.tendsto.comp
    (hprojTensor 2 J' hJmem)
  have hfinite' : ∀ L : ℕ,
      ((ContinuousLinearMap.apply ℝ ℝ M) ∘ fun L =>
        HRS.Sec7.tensorPow 2 (s102_Pj H hH L) J') L =
      ((ContinuousLinearMap.apply ℝ ℝ M') ∘ fun L =>
        HRS.Sec7.tensorPow 2 (s102_Pj H hH L) J') L := by
    intro L
    change (HRS.Sec7.tensorPow 2 (s102_Pj H hH L) J') M =
      (HRS.Sec7.tensorPow 2 (s102_Pj H hH L) J') M'
    rw [← HRS.MC.E213O.tensorPow'_eq_tensorPow,
      HRS.MC.E213O.tensorPow'_apply, HRS.MC.E213O.tensorPow'_apply]
    exact hfinite L M
  have t2' : Tendsto
      ((ContinuousLinearMap.apply ℝ ℝ M) ∘ fun L =>
        HRS.Sec7.tensorPow 2 (s102_Pj H hH L) J') atTop (𝓝 (J' M')) := by
    refine t2.congr ?_
    intro L
    exact (hfinite' L).symm
  have heq := tendsto_nhds_unique t1 t2'
  simpa [J', M'] using heq

/-- The selected physical coefficient history has a cumulative covariance with
its literal chart field as its almost-sure interval value. -/
theorem fp81s21_gaussian_Jcum_physical
    {d r : ℕ} {Pw : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (E : r26t6_WeightedChart d r Pw) (C : WholeCoeff d)
    (P : Measure Ω) (qG : ℝ → Ω → r26t6_Coeff) (MG a T c K : ℝ)
    (ha : 0 ≤ a) (hT : 0 < T) (hc : 0 ≤ c) (hK : 0 ≤ K)
    (O : r26t6_IntervalOperators E C T a c K)
    (UG : Ω → Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) (a + T))))
    (hUG : fp81s21_TimeL2Rep P qG MG 0 (a + T) UG) :
    (∀ r, AEStronglyMeasurable
      (fun ω => fp81s21_gaussian_Jcum O (add_nonneg ha hT.le) UG r ω) P) ∧
    (∀ ω, ContinuousOn
        (fun r => fp81s21_gaussian_Jcum O (add_nonneg ha hT.le) UG r ω)
        (Icc 0 (a + T)) ∧
      BoundedVariationOn
        (fun r => fp81s21_gaussian_Jcum O (add_nonneg ha hT.le) UG r ω)
        (Icc 0 (a + T))) ∧
    (∀ v r, 0 ≤ v → v ≤ r → r ≤ a + T → ∀ ω,
      fp81s21_gaussian_Jcum O (add_nonneg ha hT.le) UG r ω -
          fp81s21_gaussian_Jcum O (add_nonneg ha hT.le) UG v ω =
        O.covariance v r
          (fp81s21_timeL2L1 (a + T) (add_nonneg ha hT.le) (UG ω))) ∧
    (∀ v r, 0 ≤ v → v ≤ r → r ≤ a + T → ∀ᵐ ω ∂P,
      fp81s21_IsWindowJValue C (wholeSpaceIndex d) T a
        (fun s f => fp81s21_chartAction E (qG s ω) f) (Ioc v r)
        (((fp81s21_gaussian_Jcum O (add_nonneg ha hT.le) UG r ω -
            fp81s21_gaussian_Jcum O (add_nonneg ha hT.le) UG v ω :
              projTensor (R2X d T) 2) : TensorDual (R2X d T) 2))) ∧
    (∀ r, 0 ≤ r → r ≤ a + T → ∀ ω,
      ∀ M : R2X d T [×2]→L[ℝ] ℝ,
        ((fp81s21_gaussian_Jcum O (add_nonneg ha hT.le) UG r ω :
          projTensor (R2X d T) 2) : TensorDual (R2X d T) 2) M =
        ((fp81s21_gaussian_Jcum O (add_nonneg ha hT.le) UG r ω :
          projTensor (R2X d T) 2) : TensorDual (R2X d T) 2)
          (M.domDomCongr (Equiv.swap 0 1))) ∧
    (∀ v r, 0 ≤ v → v ≤ r → r ≤ a + T → ∀ ω,
      eVariationOn
        (fun s => fp81s21_gaussian_Jcum O (add_nonneg ha hT.le) UG s ω)
        (Icc v r) ≤ ENNReal.ofReal
          (K * |2 * C.ν| * ∫ s in Ioc v r,
            s111k2_age c a s ^ 2 *
              ‖fp81s21_timeL2L1 (a + T) (add_nonneg ha hT.le) (UG ω) s‖)) := by
  let H : ℝ := a + T
  let hH : 0 ≤ H := add_nonneg ha hT.le
  let VG : Ω → r26t6_TimeCoeff H :=
    fun ω => fp81s21_timeL2L1 H hH (UG ω)
  let Jcum : ℝ → Ω → projTensor (R2X d T) 2 :=
    fp81s21_gaussian_Jcum O hH UG
  have hbridge := fp81s21_TimeL2Rep_toL1_chart E P qG MG 0 H hH UG hUG
  letI : SecondCountableTopology (projTensor (R2X d T) 2) :=
    HRS.MS.R26T3.s21g2_k06_sc (B := R2X d T) 2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r
    have hm : Measurable (fun ω => O.covariance 0 r (VG ω)) :=
      (O.covariance 0 r).measurable.comp hbridge.1
    exact hm.aestronglyMeasurable
  · intro ω
    constructor
    · simpa [Jcum, fp81s21_gaussian_Jcum, H, VG] using
        (O.covariance_cont (VG ω))
    · let V := fp81s21_covarianceBV O hH (show (0 : ℝ) ≤ 0 by rfl) hH le_rfl
        (by simp [H]) hK hc (VG ω)
      have heq : EqOn (fp81s21_bvExt hH V) (Jcum · ω) (Icc (0 : ℝ) H) := by
        intro s hs
        rw [fp81s21_bvExt_apply hH V ⟨s, hs⟩]
        rw [← fp81s21_bvPath_apply hH V]
        rw [fp81s21_covarianceBV_apply O hH (show (0 : ℝ) ≤ 0 by rfl) hH le_rfl
          (by simp [H]) hK hc (VG ω) ⟨s, hs⟩]
        simp [Jcum, fp81s21_gaussian_Jcum, VG, H, min_eq_left hs.2]
      have hvar := fp81s21_bvExt_bv hH V
      unfold BoundedVariationOn at hvar ⊢
      rw [← eVariationOn.congr heq]
      exact hvar
  · intro v r hv hvr hr ω
    have hadd := congrArg (fun F => F (VG ω))
      (O.covariance_add 0 v r (le_rfl) hv hvr hr)
    change Jcum r ω = Jcum v ω + O.covariance v r (VG ω) at hadd
    change Jcum r ω - Jcum v ω = O.covariance v r (VG ω)
    rw [hadd]
    abel
  · have hcoeff := hbridge.2
    intro v r hv hvr hr
    filter_upwards [hcoeff] with ω hω
    have hω' : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) H), ∀ f,
        r26t6_coefficientField E (VG ω) s f = fp81s21_chartAction E (qG s ω) f := by
      simpa [VG, zero_add] using hω
    have hO := fp81s21_interval_covariance_window_value O (VG ω) hv hvr hr
    have hphys : fp81s21_IsWindowJValue C (wholeSpaceIndex d) T a
        (fun s f => fp81s21_chartAction E (qG s ω) f) (Ioc v r)
        (((O.covariance v r (VG ω) : projTensor (R2X d T) 2) :
          TensorDual (R2X d T) 2)) := by
      refine ⟨hO.1, ?_⟩
      intro ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂
      have hcoord := hO.2 ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂
      rw [hcoord]
      congr 1
      apply integral_congr_ae
      let S : Set ℝ := Ioc v r ∩ Icc (0 : ℝ) (min (a + ta) (a + tb))
      have hSmeas : MeasurableSet S := measurableSet_Ioc.inter measurableSet_Icc
      have hSsub : S ⊆ Icc (0 : ℝ) H := by
        intro s hs
        constructor
        · exact hv.trans hs.1.1.le
        · exact hs.2.2.trans ((min_le_left _ _).trans (add_le_add_right hta.2 a))
      have hbase : ∀ᵐ s ∂volume,
          s ∈ Icc (0 : ℝ) H → ∀ f,
            r26t6_coefficientField E (VG ω) s f =
              fp81s21_chartAction E (qG s ω) f :=
        (ae_restrict_iff' measurableSet_Icc).1 hω'
      have hS : ∀ᵐ s ∂volume.restrict S, ∀ f,
          r26t6_coefficientField E (VG ω) s f =
            fp81s21_chartAction E (qG s ω) f := by
        apply (ae_restrict_iff' hSmeas).2
        filter_upwards [hbase] with s hs
        intro hsS
        exact hs (hSsub hsS)
      filter_upwards [hS] with s hs
      exact hs (fun x => inner ℝ
        (gradient (propagatorW C s (a + ta) φa) x)
        (gradient (propagatorW C s (a + tb) φb) x))
    have hadd := congrArg (fun F => F (VG ω))
      (O.covariance_add 0 v r (le_rfl) hv hvr hr)
    have hdiff : Jcum r ω - Jcum v ω = O.covariance v r (VG ω) := by
      change Jcum r ω = Jcum v ω + O.covariance v r (VG ω) at hadd
      rw [hadd]
      abel
    rw [← hdiff] at hphys
    simpa [Jcum, fp81s21_gaussian_Jcum, H, hH, VG] using hphys
  · intro r hr hru ω M
    have hO := fp81s21_interval_covariance_window_value O (VG ω) le_rfl hr hru
    have hJ : fp81s21_IsWindowJValue C (wholeSpaceIndex d) T a
        (r26t6_coefficientField E (VG ω)) (Ioc 0 r)
        (((Jcum r ω : projTensor (R2X d T) 2) : TensorDual (R2X d T) 2)) := by
      simpa [Jcum, fp81s21_gaussian_Jcum, H, hH, VG] using hO
    exact fp81s21_IsWindowJValue_symmetric hT hJ M
  · intro v r hv hvr hr ω
    let q := VG ω
    let A : ℝ := K * |2 * C.ν|
    let w : ℝ → ℝ := fun s => s111k2_age c a s ^ 2 * ‖q s‖
    let g : ℝ → ℝ := fun t => A * ∫ s in v..t, w s
    have hA : 0 ≤ A := mul_nonneg hK (abs_nonneg _)
    have hbase : IntegrableOn (fun s => ‖q s‖) (Icc (0 : ℝ) H) volume :=
      (Lp.memLp q).integrable le_rfl |>.norm
    have hAgeMeas : Measurable (fun s => s111k2_age c a s ^ 2) := by
      unfold s111k2_age
      fun_prop
    have hAgeBound : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) H),
        ‖s111k2_age c a s ^ 2‖ ≤ 1 := by
      filter_upwards with s
      have hage := fp81s21_age_bounds (u := a) hc s
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_one₀ hage.1 hage.2
    have hwInt : IntegrableOn w (Icc (0 : ℝ) H) volume := by
      have hmul := hbase.bdd_mul hAgeMeas.aestronglyMeasurable hAgeBound
      change Integrable w (volume.restrict (Icc (0 : ℝ) H))
      simpa [w, mul_comm] using hmul
    have hwNonneg : ∀ s ∈ Icc (0 : ℝ) H, 0 ≤ w s := by
      intro s hs
      exact mul_nonneg (sq_nonneg _) (norm_nonneg _)
    have hwInterval : ∀ x y, x ∈ Icc (0 : ℝ) H → y ∈ Icc (0 : ℝ) H → x ≤ y →
        IntervalIntegrable w volume x y := by
      intro x y hx hy hxy
      apply (intervalIntegrable_iff_integrableOn_Icc_of_le hxy).2
      exact hwInt.mono_set (Icc_subset_Icc hx.1 hy.2)
    have hcontrolDiff : ∀ s t, s ∈ Icc v r → t ∈ Icc v r → s ≤ t →
        g t - g s = A * ∫ x in Ioc s t, w x := by
      intro s t hs ht hst
      have hsH : s ∈ Icc (0 : ℝ) H := ⟨hv.trans hs.1, hs.2.trans hr⟩
      have htH : t ∈ Icc (0 : ℝ) H := ⟨hv.trans ht.1, ht.2.trans hr⟩
      have hvH : v ∈ Icc (0 : ℝ) H := ⟨hv, hvr.trans hr⟩
      have hsum := intervalIntegral.integral_add_adjacent_intervals
        (hwInterval v s hvH hsH hs.1)
        (hwInterval s t hsH htH hst)
      rw [intervalIntegral.integral_of_le hst] at hsum
      dsimp [g]
      rw [← hsum]
      ring
    have hmono : MonotoneOn g (Icc v r) := by
      intro s hs t ht hst
      have hnInt : 0 ≤ ∫ x in s..t, w x ∂volume :=
        intervalIntegral.integral_nonneg (μ := volume) hst
        (fun x hx => hwNonneg x ⟨hv.trans (le_trans hs.1 hx.1),
          hx.2.trans (ht.2.trans hr)⟩)
      have hn : 0 ≤ ∫ x in Ioc s t, w x := by
        rw [← intervalIntegral.integral_of_le hst]
        exact hnInt
      have heq := hcontrolDiff s t hs ht hst
      have hg : g t = g s + A * ∫ x in Ioc s t, w x := by linarith
      rw [hg]
      exact le_add_of_nonneg_right (mul_nonneg hA hn)
    have hinc : ∀ s ∈ Icc v r, ∀ t ∈ Icc v r, s ≤ t →
        ‖Jcum t ω - Jcum s ω‖ ≤ g t - g s := by
      intro s hs t ht hst
      have hsH : s ∈ Icc (0 : ℝ) H := ⟨hv.trans hs.1, hs.2.trans hr⟩
      have htH : t ∈ Icc (0 : ℝ) H := ⟨hv.trans ht.1, ht.2.trans hr⟩
      have hadd := congrArg (fun F => F q) (O.covariance_add 0 s t
        (le_rfl) hsH.1 hst htH.2)
      have heq : Jcum t ω - Jcum s ω = O.covariance s t q := by
        change Jcum t ω = Jcum s ω + O.covariance s t q at hadd
        rw [hadd]
        abel
      have hnorm := O.covariance_norm s t hsH.1 hst htH.2 q
      rw [heq]
      have hcontrol := hcontrolDiff s t hs ht hst
      simpa [A, w, mul_assoc] using hnorm.trans_eq hcontrol.symm
    have hvar := fp81s21_variation_le_control_Icc
      (fun t => Jcum t ω) g hvr hmono hinc
    have htotal : g r - g v = A * ∫ x in Ioc v r, w x := by
      dsimp [g]
      rw [intervalIntegral.integral_of_le hvr]
      simp [intervalIntegral.integral_same]
    rw [htotal] at hvar
    simpa [Jcum, A, w, q, VG, H, hH, fp81s21_gaussian_Jcum, mul_assoc] using hvar

#print axioms HRS.Fp81.S21.fp81s21_gaussian_Jcum
#print axioms HRS.Fp81.S21.fp81s21_IsWindowJValue_symmetric
#print axioms HRS.Fp81.S21.fp81s21_gaussian_Jcum_physical

end HRS.Fp81.S21

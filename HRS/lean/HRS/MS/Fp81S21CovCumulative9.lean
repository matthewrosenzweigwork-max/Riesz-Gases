import HRS.MS.Fp81S21CovCumulative8

/-!
# HRS S2.1(iii), packet 19c-i: measurable raw covariance cumulative

The evaluation-coordinate integrals determine measurable fixed-time sections
of the covariance tensor.  The dense-time continuous modification then gives
a measurable continuous version with the simultaneous interval identities.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp HRS.MS.CovMeas

/-- The moving raw eta covariance has a measurable-in-sample continuous
cumulative on the physical horizon, preserving all interval evaluations and
an integrable variation bound. -/
theorem fp81s21_moving_raw_eta_measurable_cumulative_fixed
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (hH : 0 < H)
    (horb : R2OrbitSummable (r26t3_coeff R)
      (wholeSpaceIndex p.d : ℝ) H (2 * p.d + 8))
    (hlin : S102Lin (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N)
    (hphysical : Fp81MovingPhysicalInputs R hN A H) :
    ∃ Fj : A.Ω → ℝ → projTensor
        (OscPath p.d (wholeSpaceIndex p.d : ℝ) H) 2,
      ∃ V : A.Ω → ℝ,
        (∀ t : ℝ, Measurable (fun ω => Fj ω t)) ∧
        Integrable V A.P ∧
        (∀ ω, Fj ω 0 = 0) ∧
        ∀ᵐ ω ∂A.P,
          (∀ q r : ℝ, 0 ≤ q → q ≤ r → r ≤ H →
            IsR2JValue (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
              (fp81s21_movingRawEtaField p R A ω) (Ioc q r)
              (((Fj ω r - Fj ω q : projTensor
                (OscPath p.d (wholeSpaceIndex p.d : ℝ) H) 2) : TensorDual
                (OscPath p.d (wholeSpaceIndex p.d : ℝ) H) 2))) ∧
          ContinuousOn (Fj ω) (Icc 0 H) ∧
          BoundedVariationOn (Fj ω) (Icc 0 H) ∧
          (eVariationOn (Fj ω) (Icc 0 H)).toReal ≤ V ω := by
  classical
  let Pw : ℝ := (p.d : ℝ) + 2
  let r : ℕ := 2 * p.d + 8
  have hPd : (p.d : ℝ) / 2 < Pw := by dsimp [Pw]; linarith
  have hN0 : 0 < N := by omega
  obtain ⟨Vf, hVf, hVbound⟩ :=
    fp81s21_moving_raw_eta_integrable_variation_majorant p R hH hN A hphysical
  obtain ⟨K, Jm, hadd, hhom, hmain⟩ :=
    HRS.MS.CovMeas.r2_covariance_measure_proof p.hd
      (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H hH
      r Pw hPd horb hlin
  have hstrong := A.strong H
  have hXcont : ∀ᵐ ω ∂A.P, ∀ k : Fin N,
      Continuous fun t : ℝ≥0 => A.X t ω k := hstrong.cont
  have hL1 : ∀ᵐ ω ∂A.P,
      IsR2L1F r Pw H
        (fp81s21_horizonFieldExtension H
          (fp81s21_movingRawEtaField p R A ω)) :=
    fp81s21_moving_raw_eta_horizonL1F_ae p R hH hN A hphysical
  have hJmeas : ∀ᵐ ω ∂A.P,
      R2JIntegrandMeas (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
        (fp81s21_movingRawEtaField p R A ω) := by
    filter_upwards [hXcont] with ω hω
    exact fp81s21_moving_eta_JIntegrandMeas p R hδ hδh hH hN0
      A.X ω hω
  let V : A.Ω → ℝ := fun ω => max K 0 * Vf ω
  let F : A.Ω → ℝ →
      projTensor (OscPath p.d (wholeSpaceIndex p.d : ℝ) H) 2 :=
    fun ω t => if t ∈ Icc (0 : ℝ) H then
      Jm (fp81s21_horizonFieldExtension H
        (fp81s21_movingRawEtaField p R A ω)) 0 t else 0
  have hsection_core : ∀ t ∈ Icc (0 : ℝ) H,
      AEMeasurable (fun ω =>
        Jm (fp81s21_horizonFieldExtension H
          (fp81s21_movingRawEtaField p R A ω)) 0 t) A.P := by
    intro t ht
    let Jt : A.Ω → projTensor (OscPath p.d (wholeSpaceIndex p.d : ℝ) H) 2 :=
      fun ω => Jm (fp81s21_horizonFieldExtension H
        (fp81s21_movingRawEtaField p R A ω)) 0 t
    have hcoords : ∀ (ta tb : Set.Icc (0 : ℝ) H) (α β : MultiIndex p.d),
        AEMeasurable
          (fun ω => (Jt ω : TensorDual
              (OscPath p.d (wholeSpaceIndex p.d : ℝ) H) 2)
            ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap
              ![s102_ell (m := (wholeSpaceIndex p.d : ℝ)) ta α,
                s102_ell (m := (wholeSpaceIndex p.d : ℝ)) tb β])) A.P := by
      intro ta tb α β
      have hInt := fp81s21_moving_raw_eta_pairing_integral_aemeasurable
        p R hδ hδh hH hN A (ta : ℝ) (tb : ℝ) 0 t α β
        ta.2 tb.2 le_rfl ht.1 ht.2
        (s102_isDualCombo α) (s102_isDualCombo β)
      have heq : (fun ω => (Jt ω : TensorDual
              (OscPath p.d (wholeSpaceIndex p.d : ℝ) H) 2)
            ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap
              ![s102_ell (m := (wholeSpaceIndex p.d : ℝ)) ta α,
                s102_ell (m := (wholeSpaceIndex p.d : ℝ)) tb β])) =ᵐ[A.P]
          (fun ω => 2 * (r26t3_coeff R).ν *
            ∫ u in Ioc (0 : ℝ) t ∩ Icc (0 : ℝ)
                (min (ta : ℝ) (tb : ℝ)),
              fp81s21_movingRawEtaField p R A ω u
                (fun x => inner ℝ
                  (gradient (propagatorW (r26t3_coeff R) u (ta : ℝ)
                    (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x)
                  (gradient (propagatorW (r26t3_coeff R) u (tb : ℝ)
                    (oscTestFun (wholeSpaceIndex p.d : ℝ) β)) x))) := by
        filter_upwards [hL1, hJmeas, hXcont] with ω hη hηm hω
        let z : ℝ → (Euc p.d → ℝ) → ℝ :=
          fp81s21_movingRawEtaField p R A ω
        let zExt := fp81s21_horizonFieldExtension H z
        have hηmExt := fp81s21_R2JIntegrandMeas_horizonFieldExtension hηm
        obtain ⟨_, _, _, _, hvalue⟩ := hmain zExt hη hηmExt
        have hv := hvalue 0 t le_rfl ht.1 ht.2
        have hella : ∀ w : OscPath p.d (wholeSpaceIndex p.d : ℝ) H,
            s102_ell (m := (wholeSpaceIndex p.d : ℝ)) ta α w =
              OscDual.eval (r2PathAt (m := (wholeSpaceIndex p.d : ℝ)) w (ta : ℝ))
                (oscTestFun (wholeSpaceIndex p.d : ℝ) α) := by
          intro w
          rw [s102_ell_apply, r2PathAt, dif_pos ta.2,
            OscDual.eval_oscTestFun]
        have hellb : ∀ w : OscPath p.d (wholeSpaceIndex p.d : ℝ) H,
            s102_ell (m := (wholeSpaceIndex p.d : ℝ)) tb β w =
              OscDual.eval (r2PathAt (m := (wholeSpaceIndex p.d : ℝ)) w (tb : ℝ))
                (oscTestFun (wholeSpaceIndex p.d : ℝ) β) := by
          intro w
          rw [s102_ell_apply, r2PathAt, dif_pos tb.2,
            OscDual.eval_oscTestFun]
        have hpair := hv.2 (ta : ℝ) (tb : ℝ)
          (oscTestFun (wholeSpaceIndex p.d : ℝ) α)
          (oscTestFun (wholeSpaceIndex p.d : ℝ) β)
          (s102_ell (m := (wholeSpaceIndex p.d : ℝ)) ta α)
          (s102_ell (m := (wholeSpaceIndex p.d : ℝ)) tb β)
          (s102_isDualCombo α) (s102_isDualCombo β) ta.2 tb.2
          hella hellb
        have hIntEq :
            (∫ u in Ioc (0 : ℝ) t ∩ Icc (0 : ℝ)
                (min (ta : ℝ) (tb : ℝ)),
              zExt u (fun x => inner ℝ
                (gradient (propagatorW (r26t3_coeff R) u (ta : ℝ)
                  (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x)
                (gradient (propagatorW (r26t3_coeff R) u (tb : ℝ)
                  (oscTestFun (wholeSpaceIndex p.d : ℝ) β)) x))) =
            ∫ u in Ioc (0 : ℝ) t ∩ Icc (0 : ℝ)
                (min (ta : ℝ) (tb : ℝ)),
              z u (fun x => inner ℝ
                (gradient (propagatorW (r26t3_coeff R) u (ta : ℝ)
                  (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x)
                (gradient (propagatorW (r26t3_coeff R) u (tb : ℝ)
                  (oscTestFun (wholeSpaceIndex p.d : ℝ) β)) x)) := by
          apply integral_congr_ae
          refine (ae_restrict_iff'
            (measurableSet_Ioc.inter measurableSet_Icc)).2
            (Eventually.of_forall fun u hu => ?_)
          apply fp81s21_horizonFieldExtension_eq H z
          exact ⟨hu.2.1,
            hu.2.2.trans ((min_le_left _ _).trans ta.2.2)⟩
        rw [hIntEq] at hpair
        simpa [Jt, z, zExt] using hpair
      exact (hInt.const_mul (2 * (r26t3_coeff R).ν)).congr heq.symm
    have hJtmeas := fp81s21_projTensor_aemeasurable_of_pairing_coordinates
      A.P hH Jt hcoords
    simpa [Jt] using hJtmeas
  have hsections : ∀ t : ℝ, AEMeasurable (fun ω => F ω t) A.P := by
    intro t
    by_cases ht : t ∈ Icc (0 : ℝ) H
    · simpa only [F, if_pos ht] using hsection_core t ht
    · simp only [F, if_neg ht, aemeasurable_const]
  have hVint : Integrable V A.P := by
    dsimp [V]
    exact hVf.const_mul (max K 0)
  have hraw : ∀ᵐ ω ∂A.P,
      F ω 0 = 0 ∧
      (∀ q r : ℝ, 0 ≤ q → q ≤ r → r ≤ H →
        IsR2JValue (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
          (fp81s21_movingRawEtaField p R A ω) (Ioc q r)
          (((F ω r - F ω q : projTensor
            (OscPath p.d (wholeSpaceIndex p.d : ℝ) H) 2) : TensorDual
            (OscPath p.d (wholeSpaceIndex p.d : ℝ) H) 2))) ∧
      ContinuousOn (F ω) (Icc 0 H) ∧
      BoundedVariationOn (F ω) (Icc 0 H) ∧
      (eVariationOn (F ω) (Icc 0 H)).toReal ≤ V ω := by
    have hVf' : Integrable (fun ω => max K 0 * Vf ω) A.P :=
      hVf.const_mul (max K 0)
    filter_upwards [hL1, hJmeas, hXcont, hVbound] with ω hη hηm hωcont hVbd
    let z : ℝ → (Euc p.d → ℝ) → ℝ :=
      fp81s21_movingRawEtaField p R A ω
    let zExt := fp81s21_horizonFieldExtension H z
    have hηmExt := fp81s21_R2JIntegrandMeas_horizonFieldExtension hηm
    obtain ⟨haddω, hself, hcontinuous, hvariation, hvalue⟩ :=
      hmain zExt hη hηmExt
    let Jc : ℝ → projTensor
        (OscPath p.d (wholeSpaceIndex p.d : ℝ) H) 2 :=
      fun v => Jm zExt 0 v
    have hJvalue : ∀ q r : ℝ, 0 ≤ q → q ≤ r → r ≤ H →
        IsR2JValue (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H z
          (Ioc q r) ((Jc r - Jc q : projTensor
            (OscPath p.d (wholeSpaceIndex p.d : ℝ) H) 2) : TensorDual
            (OscPath p.d (wholeSpaceIndex p.d : ℝ) H) 2) := by
      intro q r' hq hqr hr'
      have hsplit : Jm zExt 0 r' = Jm zExt 0 q + Jm zExt q r' :=
        haddω 0 q r' (by norm_num) hq hqr hr'
      have hdiff : Jm zExt 0 r' - Jm zExt 0 q = Jm zExt q r' := by
        rw [hsplit]
        abel
      change IsR2JValue (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H z
        (Ioc q r') (((Jm zExt 0 r' - Jm zExt 0 q : projTensor
          (OscPath p.d (wholeSpaceIndex p.d : ℝ) H) 2) : TensorDual
          (OscPath p.d (wholeSpaceIndex p.d : ℝ) H) 2))
      rw [hdiff]
      have hv := hvalue q r' hq hqr hr'
      refine ⟨hv.1, ?_⟩
      intro ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂
      have hVext := hv.2 ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂
      have hIntEq :
          (∫ u in Ioc q r' ∩ Icc (0 : ℝ) (min ta tb),
            zExt u (fun x => inner ℝ
              (gradient (propagatorW (r26t3_coeff R) u ta φa) x)
              (gradient (propagatorW (r26t3_coeff R) u tb φb) x))) =
          ∫ u in Ioc q r' ∩ Icc (0 : ℝ) (min ta tb),
            z u (fun x => inner ℝ
              (gradient (propagatorW (r26t3_coeff R) u ta φa) x)
              (gradient (propagatorW (r26t3_coeff R) u tb φb) x)) := by
        apply integral_congr_ae
        refine (ae_restrict_iff'
          (measurableSet_Ioc.inter measurableSet_Icc)).2
          (Eventually.of_forall fun u hu => ?_)
        apply fp81s21_horizonFieldExtension_eq H z
        exact ⟨hu.2.1, hu.2.2.trans
          ((min_le_left ta tb).trans hta.2)⟩
      calc
        _ = 2 * (r26t3_coeff R).ν *
            ∫ u in Ioc q r' ∩ Icc (0 : ℝ) (min ta tb),
              zExt u (fun x => inner ℝ
                (gradient (propagatorW (r26t3_coeff R) u ta φa) x)
                (gradient (propagatorW (r26t3_coeff R) u tb φb) x)) := hVext
        _ = 2 * (r26t3_coeff R).ν *
            ∫ u in Ioc q r' ∩ Icc (0 : ℝ) (min ta tb),
              z u (fun x => inner ℝ
                (gradient (propagatorW (r26t3_coeff R) u ta φa) x)
                (gradient (propagatorW (r26t3_coeff R) u tb φb) x)) := by
          rw [hIntEq]
    have hFJ : EqOn (F ω) Jc (Icc (0 : ℝ) H) := by
      intro t ht
      change (if t ∈ Icc (0 : ℝ) H then
        Jm zExt 0 t else 0) = Jm zExt 0 t
      rw [if_pos ht]
    have hFcont : ContinuousOn (F ω) (Icc (0 : ℝ) H) :=
      hcontinuous.congr hFJ
    have hFvariation : eVariationOn (F ω) (Icc 0 H) =
        eVariationOn Jc (Icc 0 H) := eVariationOn.congr hFJ
    have hDfin : (∫⁻ v in Icc (0 : ℝ) H, dualNormE r Pw (zExt v)) < ⊤ :=
      hη.2.2
    have hD_eq : (∫⁻ v in Icc (0 : ℝ) H, dualNormE r Pw (zExt v)) =
        ∫⁻ v in Icc (0 : ℝ) H, dualNormE r Pw (z v) := by
      refine lintegral_congr_ae ?_
      exact (ae_restrict_iff' measurableSet_Icc).2
        (Eventually.of_forall fun v hv => by
          have heq : zExt v = z v := by
            funext f
            exact fp81s21_horizonFieldExtension_eq H z hv f
          exact congrArg (dualNormE r Pw) heq)
    have hDrawfin : (∫⁻ v in Icc (0 : ℝ) H,
        dualNormE r Pw (z v)) < ⊤ := by
      rw [← hD_eq]
      exact hDfin
    have hDle : (∫⁻ v in Icc (0 : ℝ) H,
        dualNormE r Pw (zExt v)) ≤ ENNReal.ofReal (Vf ω) := by
      rw [hD_eq]
      calc
        ∫⁻ v in Icc (0 : ℝ) H, dualNormE r Pw (z v) =
            ENNReal.ofReal
              (∫⁻ v in Icc (0 : ℝ) H, dualNormE r Pw (z v)).toReal :=
          (ENNReal.ofReal_toReal hDrawfin.ne).symm
        _ ≤ ENNReal.ofReal (Vf ω) :=
          ENNReal.ofReal_le_ofReal hVbd
    have hVf_nonneg : 0 ≤ Vf ω := by
      have hnonneg : 0 ≤ (∫⁻ v in Icc (0 : ℝ) H,
          dualNormE r Pw (z v)).toReal := ENNReal.toReal_nonneg
      exact le_trans hnonneg hVbd
    let Kpos : ℝ := max K 0
    have hKpos : 0 ≤ Kpos := by dsimp [Kpos]; exact le_max_right _ _
    have hvariation_le : eVariationOn Jc (Icc 0 H) ≤
        ENNReal.ofReal (Kpos * Vf ω) := by
      calc
        eVariationOn Jc (Icc 0 H) ≤ ENNReal.ofReal K *
            ∫⁻ v in Icc (0 : ℝ) H, dualNormE r Pw (zExt v) := hvariation
        _ ≤ ENNReal.ofReal Kpos *
            ∫⁻ v in Icc (0 : ℝ) H, dualNormE r Pw (zExt v) :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left K 0)) le_rfl
        _ ≤ ENNReal.ofReal Kpos * ENNReal.ofReal (Vf ω) :=
          mul_le_mul' le_rfl hDle
        _ = ENNReal.ofReal (Kpos * Vf ω) :=
          (ENNReal.ofReal_mul hKpos).symm
    have hVfBound : eVariationOn (F ω) (Icc 0 H) ≤
        ENNReal.ofReal (max K 0 * Vf ω) := by
      rw [hFvariation]
      exact hvariation_le
    have hF0 : F ω 0 = 0 := by
      have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) H := ⟨le_rfl, hH.le⟩
      change (if (0 : ℝ) ∈ Icc (0 : ℝ) H then Jm zExt 0 0 else 0) = 0
      rw [if_pos hzero]
      exact hself 0
    have hFbv : BoundedVariationOn (F ω) (Icc 0 H) := by
      unfold BoundedVariationOn
      rw [hFvariation]
      exact ne_top_of_le_ne_top
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hDfin).ne hvariation
    have hFtoReal : (eVariationOn (F ω) (Icc 0 H)).toReal ≤
        max K 0 * Vf ω :=
      ENNReal.toReal_le_of_le_ofReal
        (mul_nonneg (le_max_right K 0) hVf_nonneg) hVfBound
    have hJvalueF : ∀ q r : ℝ, 0 ≤ q → q ≤ r → r ≤ H →
        IsR2JValue (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H z
          (Ioc q r) (((F ω r - F ω q : projTensor
            (OscPath p.d (wholeSpaceIndex p.d : ℝ) H) 2) : TensorDual
            (OscPath p.d (wholeSpaceIndex p.d : ℝ) H) 2)) := by
      intro q r' hq hqr hr'
      have hqmem : q ∈ Icc (0 : ℝ) H := ⟨hq, hqr.trans hr'⟩
      have hrmem : r' ∈ Icc (0 : ℝ) H := ⟨hq.trans hqr, hr'⟩
      rw [hFJ hrmem, hFJ hqmem]
      exact hJvalue q r' hq hqr hr'
    refine ⟨hF0, hJvalueF, hFcont, hFbv, hFtoReal⟩
  obtain ⟨Fj, hFj, hVsame, hFj0, hFje⟩ :=
    fp81s21_covariance_measurable_continuous_version_of_sections
      p R hH A F V hsections hVint hraw
  exact ⟨Fj, V, hFj, hVsame, hFj0, hFje⟩

#print axioms HRS.Fp81.S21.fp81s21_moving_raw_eta_measurable_cumulative_fixed

end HRS.Fp81.S21

end

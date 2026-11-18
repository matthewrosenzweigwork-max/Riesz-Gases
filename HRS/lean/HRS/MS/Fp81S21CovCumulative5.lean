import HRS.MS.Fp81S21CovCumulative4

/-!
# HRS S2.1(iii), packet 19c-i: one raw covariance cumulative for all intervals

This stage applies the proved covariance-measure constructor to the moving raw
eta field.  It gives one continuous BV projective-tensor path on a full-measure
event, with the raw eta interval identities holding simultaneously for every
admissible real interval.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp HRS.MS.CovMeas

/-- The moving raw eta covariance admits a single continuous BV cumulative on
a full-measure event, with the covariance identity simultaneous over all real
intervals contained in `[0,H]` and an integrable total-variation majorant. -/
theorem fp81s21_moving_raw_eta_covariance_BV_ae
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (hH : 0 < H)
    (horb : R2OrbitSummable (r26t3_coeff R)
      (wholeSpaceIndex p.d : ℝ) H (2 * p.d + 8))
    (hlin : S102Lin (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N)
    (hphysical : Fp81MovingPhysicalInputs R hN A H) :
    ∃ Vf : A.Ω → ℝ, Integrable Vf A.P ∧
      ∀ᵐ ω ∂A.P,
        ∃ Jc : ℝ → projTensor
            (OscPath p.d (wholeSpaceIndex p.d : ℝ) H) 2,
          Jc 0 = 0 ∧
          (∀ q r : ℝ, 0 ≤ q → q ≤ r → r ≤ H →
            IsR2JValue (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
              (fp81s21_movingRawEtaField p R A ω) (Ioc q r)
              (((Jc r - Jc q : projTensor
                (OscPath p.d (wholeSpaceIndex p.d : ℝ) H) 2) : TensorDual
                (OscPath p.d (wholeSpaceIndex p.d : ℝ) H) 2))) ∧
          ContinuousOn Jc (Icc 0 H) ∧ BoundedVariationOn Jc (Icc 0 H) ∧
          (eVariationOn Jc (Icc 0 H)).toReal ≤ Vf ω := by
  classical
  let Pw : ℝ := (p.d : ℝ) + 2
  let r : ℕ := 2 * p.d + 8
  have hPd : (p.d : ℝ) / 2 < Pw := by dsimp [Pw]; linarith
  have hN0 : 0 < N := by omega
  obtain ⟨Vf, hVf, hVbound⟩ :=
    fp81s21_moving_raw_eta_integrable_variation_majorant p R hH hN A hphysical
  obtain ⟨K, Jm, _, _, hmain⟩ :=
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
    exact fp81s21_moving_raw_eta_JIntegrandMeas p R hδ hδh hH hN0
      A.X ω hω
  let Kpos : ℝ := max K 0
  have hKpos : 0 ≤ Kpos := by dsimp [Kpos]; exact le_max_right _ _
  have hVf' : Integrable (fun ω => Kpos * Vf ω) A.P := hVf.const_mul Kpos
  refine ⟨fun ω => Kpos * Vf ω, hVf', ?_⟩
  filter_upwards [hL1, hJmeas, hXcont, hVbound] with ω hη hηm hωcont hVbd
  have hcz : ∀ k : Fin N, Continuous fun t : ℝ≥0 => A.X t ω k := hωcont
  let z : ℝ → (Euc p.d → ℝ) → ℝ := fp81s21_movingRawEtaField p R A ω
  let zExt : ℝ → (Euc p.d → ℝ) → ℝ :=
    fp81s21_horizonFieldExtension H z
  have hηmExt := fp81s21_R2JIntegrandMeas_horizonFieldExtension hηm
  obtain ⟨hadd, hself, hcontinuous, hvariation, hvalue⟩ :=
    hmain zExt hη hηmExt
  let Jc : ℝ → projTensor (OscPath p.d (wholeSpaceIndex p.d : ℝ) H) 2 :=
    fun v => Jm zExt 0 v
  have hDfin : (∫⁻ v in Icc (0 : ℝ) H,
      dualNormE r Pw (zExt v)) < ⊤ := hη.2.2
  have hD_eq : (∫⁻ v in Icc (0 : ℝ) H, dualNormE r Pw (zExt v)) =
      ∫⁻ v in Icc (0 : ℝ) H, dualNormE r Pw (z v) := by
    refine lintegral_congr_ae ?_
    exact (ae_restrict_iff' measurableSet_Icc).2
      (Eventually.of_forall fun v hv => by
        have heq : fp81s21_horizonFieldExtension H z v = z v := by
          funext f
          exact fp81s21_horizonFieldExtension_eq H z hv f
        change dualNormE r Pw (zExt v) = dualNormE r Pw (z v)
        exact congrArg (dualNormE r Pw) (by simpa [zExt] using heq))
  have hDrawfin : (∫⁻ v in Icc (0 : ℝ) H, dualNormE r Pw (z v)) < ⊤ := by
    rw [← hD_eq]
    exact hDfin
  have hDle : (∫⁻ v in Icc (0 : ℝ) H, dualNormE r Pw (zExt v)) ≤
      ENNReal.ofReal (Vf ω) := by
    rw [hD_eq]
    calc
      ∫⁻ v in Icc (0 : ℝ) H, dualNormE r Pw (z v) =
          ENNReal.ofReal
            (∫⁻ v in Icc (0 : ℝ) H, dualNormE r Pw (z v)).toReal :=
        (ENNReal.ofReal_toReal hDrawfin.ne).symm
      _ ≤ ENNReal.ofReal (Vf ω) := ENNReal.ofReal_le_ofReal hVbd
  have hVf_nonneg : 0 ≤ Vf ω := by
    have hnonneg : 0 ≤ (∫⁻ v in Icc (0 : ℝ) H,
        dualNormE r Pw (z v)).toReal := ENNReal.toReal_nonneg
    exact le_trans hnonneg hVbd
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
  have hJvalue : ∀ q r' : ℝ, 0 ≤ q → q ≤ r' → r' ≤ H →
      IsR2JValue (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H z
        (Ioc q r') (((Jc r' - Jc q : projTensor
          (OscPath p.d (wholeSpaceIndex p.d : ℝ) H) 2) : TensorDual
          (OscPath p.d (wholeSpaceIndex p.d : ℝ) H) 2)) := by
    intro q r' hq hqr hr'
    have hsplit : Jm zExt 0 r' = Jm zExt 0 q + Jm zExt q r' :=
      hadd 0 q r' (by norm_num) hq hqr hr'
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
    have hInt :
        (∫ u in Ioc q r' ∩ Icc (0 : ℝ) (min ta tb),
          zExt u (fun x => inner ℝ
            (gradient (propagatorW (r26t3_coeff R) u ta φa) x)
            (gradient (propagatorW (r26t3_coeff R) u tb φb) x))) =
        ∫ u in Ioc q r' ∩ Icc (0 : ℝ) (min ta tb),
          z u (fun x => inner ℝ
            (gradient (propagatorW (r26t3_coeff R) u ta φa) x)
            (gradient (propagatorW (r26t3_coeff R) u tb φb) x)) := by
      apply integral_congr_ae
      refine (ae_restrict_iff' (measurableSet_Ioc.inter measurableSet_Icc)).2
        (Eventually.of_forall fun u hu => ?_)
      apply fp81s21_horizonFieldExtension_eq H z
      exact ⟨hu.2.1,
        hu.2.2.trans ((min_le_left _ _).trans hta.2)⟩
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
              (gradient (propagatorW (r26t3_coeff R) u tb φb) x)) := by rw [hInt]
  refine ⟨Jc, ?_, hJvalue, hcontinuous, ?_, ?_⟩
  · change Jm zExt 0 0 = 0
    exact hself 0
  · exact ne_top_of_le_ne_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hDfin).ne hvariation
  · exact ENNReal.toReal_le_of_le_ofReal
      (mul_nonneg hKpos hVf_nonneg) hvariation_le

#print axioms HRS.Fp81.S21.fp81s21_moving_raw_eta_covariance_BV_ae

end HRS.Fp81.S21

end

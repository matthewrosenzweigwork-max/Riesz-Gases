import HRS.MS.Fp81S21CovCumulative

/-!
# HRS S2.1(iii), packet 19c-i: measurable-horizon extension for raw eta

`IsR2L1F` asks for scalar-time measurability on all of `ℝ`, whereas the physical
moving-reference eta field is used only on `[0,H]`.  This adapter extends it by
zero outside that horizon and transports covariance-integrand measurability and
the selected covariance values back to the physical raw field.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp HRS.MS.CovMeas

/-- Extend a time-dependent functional by zero outside its physical horizon. -/
def fp81s21_horizonFieldExtension {d : ℕ} (H : ℝ)
    (z : ℝ → (Euc d → ℝ) → ℝ) : ℝ → (Euc d → ℝ) → ℝ :=
  fun v f => if v ∈ Icc (0 : ℝ) H then z v f else 0

theorem fp81s21_horizonFieldExtension_eq
    {d : ℕ} (H : ℝ) (z : ℝ → (Euc d → ℝ) → ℝ)
    {v : ℝ} (hv : v ∈ Icc (0 : ℝ) H) (f : Euc d → ℝ) :
    fp81s21_horizonFieldExtension H z v f = z v f := by
  simp [fp81s21_horizonFieldExtension, hv]

/-- Covariance-integrand measurability only examines times in `[0,H]`, so it is
preserved by the measurable-horizon extension. -/
theorem fp81s21_R2JIntegrandMeas_horizonFieldExtension
    {d : ℕ} {C : WholeCoeff d} {m H : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ}
    (hzm : R2JIntegrandMeas C m H z) :
    R2JIntegrandMeas C m H (fp81s21_horizonFieldExtension H z) := by
  intro ta tb φa φb hφa hφb hta htb
  have h := hzm ta tb φa φb hφa hφb hta htb
  have heq : (fun u => fp81s21_horizonFieldExtension H z u
      (fun x => inner ℝ
        (gradient (propagatorW C u ta φa) x)
        (gradient (propagatorW C u tb φb) x))) =ᵐ[volume.restrict (Icc (0 : ℝ) (min ta tb))]
      (fun u => z u (fun x => inner ℝ
        (gradient (propagatorW C u ta φa) x)
        (gradient (propagatorW C u tb φb) x))) := by
    refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun u hu => ?_)
    apply fp81s21_horizonFieldExtension_eq H z
    exact ⟨hu.1, hu.2.trans ((min_le_left _ _).trans hta.2)⟩
  exact h.congr heq.symm

/-- The full-horizon covariance constructor accepts an integrable extension of
raw eta and returns the interval identity for the physical raw eta field. -/
theorem fp81s21_raw_eta_covariance_cumulative_of_horizonL1F
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    (horb : R2OrbitSummable (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
      (2 * p.d + 8))
    (hlin : S102Lin (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H)
    {Pw : ℝ} (hP : (p.d : ℝ) / 2 < Pw)
    {N : ℕ} (A : Particle R N) (ω : A.Ω)
    (hη : IsR2L1F (2 * p.d + 8) Pw H
      (fp81s21_horizonFieldExtension H
        (fp81s21_movingRawEtaField p R A ω)))
    (hηm : R2JIntegrandMeas (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
      (fp81s21_movingRawEtaField p R A ω)) :
    ∃ K : ℝ,
      ∃ Jc : ℝ → projTensor (OscPath p.d (wholeSpaceIndex p.d : ℝ) H) 2,
        Jc 0 = 0 ∧
        (∀ q r : ℝ, 0 ≤ q → q ≤ r → r ≤ H →
          IsR2JValue (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
            (fp81s21_movingRawEtaField p R A ω) (Ioc q r)
            (((Jc r - Jc q : projTensor
              (OscPath p.d (wholeSpaceIndex p.d : ℝ) H) 2) : TensorDual
              (OscPath p.d (wholeSpaceIndex p.d : ℝ) H) 2))) ∧
        ContinuousOn Jc (Icc 0 H) ∧
        BoundedVariationOn Jc (Icc 0 H) ∧
        eVariationOn Jc (Icc 0 H) ≤
          ENNReal.ofReal K * ∫⁻ v in Icc (0 : ℝ) H,
            dualNormE (2 * p.d + 8) Pw
              (fp81s21_horizonFieldExtension H
                (fp81s21_movingRawEtaField p R A ω) v) := by
  let z := fp81s21_movingRawEtaField p R A ω
  let zExt := fp81s21_horizonFieldExtension H z
  have hηmExt := fp81s21_R2JIntegrandMeas_horizonFieldExtension hηm
  obtain ⟨K, Jm, _, _, hmain⟩ :=
    HRS.MS.CovMeas.r2_covariance_measure_proof p.hd
      (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H hH
      (2 * p.d + 8) Pw hP horb hlin
  obtain ⟨hadd, hself, hcontinuous, hvariation, hvalue⟩ := hmain zExt hη hηmExt
  let Jc : ℝ → projTensor (OscPath p.d (wholeSpaceIndex p.d : ℝ) H) 2 :=
    fun v => Jm zExt 0 v
  refine ⟨K, Jc, ?_, ?_, hcontinuous, ?_, ?_⟩
  · change Jm zExt 0 0 = 0
    exact hself 0
  · intro q r hq hqr hr
    have hsplit : Jm zExt 0 r = Jm zExt 0 q + Jm zExt q r :=
      hadd 0 q r (by norm_num) hq hqr hr
    have hdiff : Jm zExt 0 r - Jm zExt 0 q = Jm zExt q r := by
      rw [hsplit]
      abel
    change IsR2JValue (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H z
      (Ioc q r) (((Jc r - Jc q : projTensor
        (OscPath p.d (wholeSpaceIndex p.d : ℝ) H) 2) : TensorDual
        (OscPath p.d (wholeSpaceIndex p.d : ℝ) H) 2))
    rw [hdiff]
    have hv := hvalue q r hq hqr hr
    refine ⟨hv.1, ?_⟩
    intro ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂
    have hVext := hv.2 ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂
    have hInt :
        (∫ u in Ioc q r ∩ Icc (0 : ℝ) (min ta tb),
          zExt u (fun x => inner ℝ
            (gradient (propagatorW (r26t3_coeff R) u ta φa) x)
            (gradient (propagatorW (r26t3_coeff R) u tb φb) x))) =
        ∫ u in Ioc q r ∩ Icc (0 : ℝ) (min ta tb),
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
          ∫ u in Ioc q r ∩ Icc (0 : ℝ) (min ta tb),
            zExt u (fun x => inner ℝ
              (gradient (propagatorW (r26t3_coeff R) u ta φa) x)
              (gradient (propagatorW (r26t3_coeff R) u tb φb) x)) := hVext
      _ = 2 * (r26t3_coeff R).ν *
          ∫ u in Ioc q r ∩ Icc (0 : ℝ) (min ta tb),
            z u (fun x => inner ℝ
              (gradient (propagatorW (r26t3_coeff R) u ta φa) x)
              (gradient (propagatorW (r26t3_coeff R) u tb φb) x)) := by rw [hInt]
  · have hfinite : ENNReal.ofReal K *
        ∫⁻ v in Icc (0 : ℝ) H, dualNormE (2 * p.d + 8) Pw (zExt v) < ⊤ :=
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hη.2.2
    exact ne_top_of_le_ne_top hfinite.ne hvariation
  · exact hvariation

#print axioms HRS.Fp81.S21.fp81s21_horizonFieldExtension_eq
#print axioms HRS.Fp81.S21.fp81s21_R2JIntegrandMeas_horizonFieldExtension
#print axioms HRS.Fp81.S21.fp81s21_raw_eta_covariance_cumulative_of_horizonL1F

end HRS.Fp81.S21

end

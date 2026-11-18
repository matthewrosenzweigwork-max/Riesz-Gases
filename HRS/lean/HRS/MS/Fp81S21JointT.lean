import HRS.MS.Fp81S21TimeRep9
import HRS.MS.Fp81S21TimeRep14
import HRS.MS.Fp81S21EmbedIdent

/-! Uniqueness of time-section classes from fixed-time a.e. equality. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory
open scoped ENNReal

namespace HRS.Fp81.S21

open HRS.MS.R26T6

local instance fp81s21_jointT_measSpace (H : ℝ) : MeasurableSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := borel _
local instance fp81s21_jointT_borelSpace (H : ℝ) : BorelSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := ⟨rfl⟩

/-- If two jointly measurable coefficient fields agree almost everywhere at
 every nonnegative time, their `TimeL2Rep` classes over a nonnegative shift
 agree almost everywhere. -/
theorem fp81s21_TimeL2Rep_eq_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (q q' : ℝ → Ω → r26t6_Coeff) (M M' a H : ℝ)
    (U V : Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)))
    (hq : Measurable (Function.uncurry q))
    (hq' : Measurable (Function.uncurry q'))
    (ha : 0 ≤ a)
    (hsection : ∀ u, 0 ≤ u → (fun ω => q u ω) =ᵐ[P] (fun ω => q' u ω))
    (hU : fp81s21_TimeL2Rep P q M a H U)
    (hV : fp81s21_TimeL2Rep P q' M' a H V) :
    U =ᵐ[P] V := by
  let dt : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) H)
  let g : ℝ × Ω → r26t6_Coeff := fun z => q (a + z.1) z.2
  let g' : ℝ × Ω → r26t6_Coeff := fun z => q' (a + z.1) z.2
  have hg : Measurable g :=
    hq.comp ((measurable_const.add measurable_fst).prodMk measurable_snd)
  have hg' : Measurable g' :=
    hq'.comp ((measurable_const.add measurable_fst).prodMk measurable_snd)
  have hsections : ∀ᵐ t ∂dt,
      (fun ω => g (t, ω)) =ᵐ[P] (fun ω => g' (t, ω)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hsection (a + t) (by linarith [ht.1])
  have hprod : g =ᵐ[dt.prod P] g' :=
    fp81s21_product_ae_of_section_ae dt P g g' hg hg' hsections
  have hswap :=
    (Measure.measurePreserving_swap (μ := P) (ν := dt)).quasiMeasurePreserving.ae hprod
  have hωt := Measure.ae_ae_of_ae_prod hswap
  filter_upwards [hU.2.2.2, hV.2.2.2, hωt] with ω hωU hωV hωeq
  have hfun : (⇑(U ω) : ℝ → r26t6_Coeff) =ᵐ[dt] ⇑(V ω) := by
    filter_upwards [hωU.2, hωV.2, hωeq] with t hUeq hVeq heq
    exact hUeq.trans (heq.trans hVeq.symm)
  exact Lp.ext hfun

/-- The uniqueness theorem applies directly to two `MomentRep`s for the same
 represented functional, using fixed-time representative uniqueness. -/
theorem fp81s21_MomentRep_TimeL2Rep_eq_ae
    {d r : ℕ} {Pw : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (hP : (d : ℝ) < 2 * Pw)
    (E : r26t6_WeightedChart d r Pw) (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : ℝ → Ω → (Euc d → ℝ) → ℝ)
    (q q' : ℝ → Ω → r26t6_Coeff) (M M' a H : ℝ)
    (U V : Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)))
    (hq : Measurable (Function.uncurry q))
    (hq' : Measurable (Function.uncurry q'))
    (ha : 0 ≤ a)
    (hrep : fp81s21_MomentRep E P Q q M)
    (hrep' : fp81s21_MomentRep E P Q q' M')
    (hU : fp81s21_TimeL2Rep P q M a H U)
    (hV : fp81s21_TimeL2Rep P q' M' a H V) :
    U =ᵐ[P] V := by
  apply fp81s21_TimeL2Rep_eq_ae P q q' M M' a H U V hq hq' ha
  · intro u hu
    exact fp81s21_MomentRep_eq_ae hP E P Q q q' M M' hrep hrep' u hu
  · exact hU
  · exact hV

#print axioms HRS.Fp81.S21.fp81s21_TimeL2Rep_eq_ae
#print axioms HRS.Fp81.S21.fp81s21_MomentRep_TimeL2Rep_eq_ae

end HRS.Fp81.S21

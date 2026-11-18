import HRS.MS.Fp81S21TimeRep9
import HRS.MS.Fp81S21SmoothSqErr

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HRS.Fp81.S21

local instance fp81s21_versionTime_UH_measSpace (H : ℝ) : MeasurableSpace
    (fp81s21_SmoothUH H) := borel _
local instance fp81s21_versionTime_UH_borelSpace (H : ℝ) : BorelSpace
    (fp81s21_SmoothUH H) := ⟨rfl⟩

/-- A time-L² representative whose sections agree pointwise in time almost
surely is the time-L² class of the measurable continuous-path version. -/
theorem fp81s21_TimeL2Rep_eq_continuous_version
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (H M a : ℝ) (hH : 0 < H)
    (q : ℝ → Ω → HRS.MS.R26T6.r26t6_Coeff)
    (U : Ω → fp81s21_SmoothUH H)
    (X : Ω → fp81s21_SmoothCH H)
    (hq : Measurable (Function.uncurry q))
    (hU : fp81s21_TimeL2Rep P q M a H U)
    (hX : Measurable X)
    (hsec : ∀ t : Icc (0 : ℝ) H,
      (fun ω => X ω t) =ᵐ[P] q (a + t)) :
    U =ᵐ[P] fun ω => fp81s21_smoothPathToL2 H hH (X ω) := by
  let dt : Measure ℝ := volume.restrict (Icc (0 : ℝ) H)
  let g : ℝ × Ω → HRS.MS.R26T6.r26t6_Coeff := fun z =>
    X z.2 (fp81s21_smoothClamp H hH z.1)
  let f : ℝ × Ω → HRS.MS.R26T6.r26t6_Coeff := fun z => q (a + z.1) z.2
  have hg : Measurable g := by
    have hpair : Measurable (fun z : ℝ × Ω =>
        (X z.2, fp81s21_smoothClamp H hH z.1)) := by
      exact (hX.comp measurable_snd).prodMk
        ((fp81s21_smoothClamp H hH).continuous.measurable.comp measurable_fst)
    exact continuous_eval.measurable.comp hpair
  have hf : Measurable f := by
    change Measurable (Function.uncurry q ∘ fun z : ℝ × Ω => (a + z.1, z.2))
    exact hq.comp (by fun_prop)
  have hsections : ∀ᵐ t ∂dt,
      (fun ω => g (t, ω)) =ᵐ[P] (fun ω => f (t, ω)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    let t' : Icc (0 : ℝ) H := ⟨t, ht.1, ht.2⟩
    have htval : (t' : ℝ) = t := rfl
    have hclamp : fp81s21_smoothClamp H hH t = t' := by
      rw [← htval]
      exact fp81s21_smoothClamp_apply_of_mem H hH t'
    simpa only [g, f, hclamp, htval] using hsec t'
  have hprod : g =ᵐ[dt.prod P] f := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hg hf)).2
    exact hsections
  have hswap :=
    (Measure.measurePreserving_swap (μ := P) (ν := dt)).quasiMeasurePreserving.ae hprod
  have hωt : ∀ᵐ ω ∂P, ∀ᵐ t ∂dt, g (t, ω) = f (t, ω) :=
    Measure.ae_ae_of_ae_prod hswap
  filter_upwards [hU.2.2.2, hωt] with ω hUω hω
  change U ω = fp81s21_smoothPathToL2 H hH (X ω)
  have hωfun : (fun t : ℝ => g (t, ω)) =ᵐ[dt]
      (fun t => f (t, ω)) := hω
  have hqX : (fun t : ℝ => q (a + t) ω) =ᵐ[dt]
      (fun t => X ω (fp81s21_smoothClamp H hH t)) := by
    simpa [g, f] using hωfun.symm
  have hpath := fp81s21_smoothPathToL2_coe H hH (X ω)
  apply Lp.ext
  exact hUω.2.trans (hqX.trans hpath.symm)

end HRS.Fp81.S21

#print axioms HRS.Fp81.S21.fp81s21_TimeL2Rep_eq_continuous_version

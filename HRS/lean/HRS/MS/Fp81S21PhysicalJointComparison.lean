import HRS.MS.Fp81S21AvgPackageRetained
import HRS.MS.Fp81S21JointClose9
import HRS.MS.Fp81S21JointAvg
import HRS.MS.Fp81S21JointAvgUnif

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6

local instance fp81s21_physicalJoint_U_measSpace (H : ℝ) :
    MeasurableSpace (fp81s21_jointP_U H) := borel _
local instance fp81s21_physicalJoint_U_borelSpace (H : ℝ) :
    BorelSpace (fp81s21_jointP_U H) := ⟨rfl⟩

/-- The `TimeL2Rep` carrier is determined by its represented coefficient
field. The integral bound is taken from the target field's certificate, so
its moment constant may differ from the source constant. -/
theorem fp81s21_TimeL2Rep_congr_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (q q' : ℝ → Ω → r26t6_Coeff) (M M' a H : ℝ)
    (U V : Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)))
    (hq : Measurable (Function.uncurry q))
    (hq' : Measurable (Function.uncurry q'))
    (ha : 0 ≤ a)
    (hsection : ∀ u, 0 ≤ u → (fun ω => q u ω) =ᵐ[P] (fun ω => q' u ω))
    (hU : fp81s21_TimeL2Rep P q M a H U)
    (hV : fp81s21_TimeL2Rep P q' M' a H V) :
    fp81s21_TimeL2Rep P q' M' a H U := by
  have hUV : U =ᵐ[P] V :=
    fp81s21_TimeL2Rep_eq_ae P q q' M M' a H U V hq hq' ha hsection hU hV
  have hnorm : (fun ω => ‖U ω‖ ^ 2) =ᵐ[P] (fun ω => ‖V ω‖ ^ 2) := by
    filter_upwards [hUV] with ω hω
    rw [hω]
  refine ⟨hU.1, hU.2.1, ?_, ?_⟩
  · calc
      (∫ ω, ‖U ω‖ ^ 2 ∂P) = ∫ ω, ‖V ω‖ ^ 2 ∂P := integral_congr_ae hnorm
      _ ≤ H * M' := hV.2.2.1
  · filter_upwards [hUV, hV.2.2.2] with ω hω hVω
    have hfun : (⇑(U ω) : ℝ → r26t6_Coeff) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) H)]
        ⇑(V ω) := Lp.ext_iff.mp hω
    exact ⟨hVω.1, hfun.trans hVω.2⟩

/-- Identify two time classes built from moment representatives of the same
functional. The representatives may be distinct and their moment constants
need not agree. -/
theorem fp81s21_MomentRep_TimeL2Rep_identification
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
    U =ᵐ[P] V :=
  fp81s21_MomentRep_TimeL2Rep_eq_ae hP E P Q q q' M M' a H U V
    hq hq' ha hrep hrep' hU hV

private theorem fp81s21_TimeRep_to_TimeL2Rep
    {d r : ℕ} {Pw : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (E : r26t6_WeightedChart d r Pw) (P : Measure Ω)
    (Q : ℝ → Ω → (Euc d → ℝ) → ℝ)
    (q : ℝ → Ω → r26t6_Coeff) (M a H : ℝ)
    (U : Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)))
    (h : fp81s21_TimeRep E P Q q M a H U) :
    fp81s21_TimeL2Rep P q M a H U := by
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  filter_upwards [h.2.2.2] with ω hω
  refine ⟨hω.1, ?_⟩
  filter_upwards [hω.2] with t ht
  exact ht.1

/-- Physical joint comparison of a continuous coefficient path and the same
packet-31 quadratic time class used in its source-law comparison. The profile
is fixed after the horizon and before particle/Gaussian realizations or starts. -/
theorem fp81s21_physical_joint_comparison (p : Parameters) :
    ∃ Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4),
    ∃ E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2),
    ∃ εAvg : ℕ → ℝ, (∀ m, 0 ≤ εAvg m) ∧ Tendsto εAvg atTop (𝓝 0) ∧
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ MUG : ℝ, 0 ≤ MUG ∧
        ∃ canon : fp81s21_gaussian_V2_G_canonicalFamily p Es E R MUG εAvg,
        ∃ εN εG εB : ℕ → ℝ,
        ∃ S31 : fp81s21_Physical31 p R Es E εN εG εB,
        ∀ H : ℝ, (hH : 0 < H) →
          ∃ M2 : ℝ, 0 ≤ M2 ∧
          ∃ Savg : ℕ → fp81s21_SmoothUH H →L[ℝ] fp81s21_SmoothCH H,
          ∃ ω : ℕ → ℝ,
            (∀ k, 0 ≤ ω k) ∧ Tendsto ω atTop (𝓝 0) ∧
            (∀ k, ‖Savg k‖ ≤ Real.sqrt (((k : ℝ) + 2) / H)) ∧
          ∃ q31 : ℕ → ℝ,
            (∀ N, 0 ≤ q31 N) ∧ Tendsto q31 atTop (𝓝 0) ∧
          ∃ e : ℕ → ℝ,
            e = fp81s21_jointAvg_unifProfile ω
              (fun k => max 1 ‖Savg k‖) q31 ∧
            (∀ N, 0 ≤ e N) ∧ Tendsto e atTop (𝓝 0) ∧
            ∀ N : ℕ, ∀ hN : 2 ≤ N, ∀ A : Particle R N,
              ∃ qN : ℝ → A.Ω → r26t6_Coeff,
                fp81s21_MomentRep E A.P
                  (fp81s21_particleEmpField R N A) qN M2 ∧
                ∀ G : GaussianRealization R, ∀ a : ℝ, 0 ≤ a →
                  ∃ XN : A.Ω → fp81s21_SmoothCH H,
                  ∃ UN : A.Ω → fp81s21_SmoothUH H,
                  ∃ VηN : A.Ω → fp81s21_SmoothUH H,
                  ∃ UBN : A.Ω → fp81s21_SmoothUH H,
                  ∃ XG : G.Ω → fp81s21_SmoothCH H,
                  ∃ UG : G.Ω → fp81s21_SmoothUH H,
                  ∃ VηG : G.Ω → fp81s21_SmoothUH H,
                  ∃ UBG : G.Ω → fp81s21_SmoothUH H,
                    Measurable XN ∧ MemLp XN 2 A.P ∧
                    fp81s21_TimeL2Rep A.P
                      (fun u ζ => fp81s21_particle_embedField p Es E
                        (S31.qsηN N hN A u ζ)) S31.MN a H UN ∧
                    fp81s21_TimeL2Rep A.P
                      (fun u ζ => fp81s21_particle_embedField p Es E
                        (S31.qsηN N hN A u ζ)) S31.MN a H VηN ∧
                    UN =ᵐ[A.P] VηN ∧
                    Measurable UBN ∧ MemLp UBN 2 A.P ∧
                    fp81s21_TimeL2Rep A.P
                      (fun u ζ => fp81s21_particle_embedField p Es E
                        (S31.qsBN N hN A u ζ)) S31.MN a H UBN ∧
                    UN =ᵐ[A.P]
                      (fun ζ => fp81s21_smoothPathToL2 H hH (XN ζ)) ∧
                    (∀ᵐ ζ ∂A.P, ∀ t : Icc (0 : ℝ) H,
                      ∀ f : Euc p.d → ℝ, IsR2Test f →
                        fp81s21_chartAction E (XN ζ t) f =
                          fp81s21_particleEmpField R N A (a + (t : ℝ)) ζ f) ∧
                    Measurable XG ∧ MemLp XG 2 G.P ∧
                    fp81s21_TimeL2Rep G.P
                      (fp81s21_gaussian_embedFamily p Es E (S31.gaussian.qsηG G))
                      S31.gaussian.MηG a H UG ∧
                    fp81s21_TimeL2Rep G.P
                      (fp81s21_gaussian_embedFamily p Es E (S31.gaussian.qsηG G))
                      S31.gaussian.MηG a H VηG ∧
                    UG =ᵐ[G.P] VηG ∧
                    Measurable UBG ∧ MemLp UBG 2 G.P ∧
                    fp81s21_TimeL2Rep G.P (S31.gaussian.quadratic.qe G)
                      (S31.gaussian.quadratic.Kstar ^ 4 * S31.gaussian.quadratic.B / 2)
                      a H UBG ∧
                    UG =ᵐ[G.P]
                      (fun ζ => fp81s21_smoothPathToL2 H hH (XG ζ)) ∧
                    (∀ᵐ ζ ∂G.P, ∀ t : Icc (0 : ℝ) H,
                      ∀ f : Euc p.d → ℝ, IsR2Test f →
                        fp81s21_chartAction E (XG ζ t) f =
                          OscDual.eval (G.Z (a + t) ζ) f) ∧
                    (∀ k : ℕ,
                      fp81s21_SqErr A.P XN
                        (fun ζ => Savg k (UN ζ)) (ω k) ∧
                      fp81s21_SqErr G.P XG
                        (fun ζ => Savg k (UG ζ)) (ω k)) ∧
                    wassersteinE 2
                      (law A.P (fun ζ => (XN ζ, UBN ζ)))
                      (law G.P (fun ζ => (XG ζ, UBG ζ))) ≤
                        ENNReal.ofReal (e N) := by
  obtain ⟨Es, E, εAvg, hεAvg, hεAvgLim, δA, hδA, hδAh, hA⟩ :=
    fp81s21_physical_avgPackage_retained p
  obtain ⟨δJ, hδJ, hδJh, hJ⟩ :=
    fp81s21_joint_timeL2_comparison_charts_first p Es E
  refine ⟨Es, E, εAvg, hεAvg, hεAvgLim, min δA δJ,
    lt_min hδA hδJ, (min_le_left _ _).trans hδAh, ?_⟩
  intro δ hδ hδle R
  have hδAle : δ ≤ δA := hδle.trans (min_le_left _ _)
  have hδJle : δ ≤ δJ := hδle.trans (min_le_right _ _)
  obtain ⟨MUG, hMUG, canon, hAforH⟩ := hA δ hδ hδAle R
  obtain ⟨εN, εG, εB, S31, hJforH⟩ := hJ δ hδ hδJle R
  refine ⟨MUG, hMUG, canon, εN, εG, εB, S31, ?_⟩
  intro H hH
  obtain ⟨M2, hM2, Savg, ω, hω, hωlim, hSbound, hAall⟩ := hAforH H hH
  obtain ⟨q31, hq31, hq31lim, hClose⟩ := hJforH H hH
  have hK : ∀ k, 0 ≤ max 1 ‖Savg k‖ := by
    intro k
    exact le_trans (by norm_num) (le_max_left 1 ‖Savg k‖)
  have hprofile := fp81s21_jointAvg_unifProfile_spec ω
    (fun k => max 1 ‖Savg k‖) q31 hω hK hq31 hωlim hq31lim
  let e : ℕ → ℝ := fp81s21_jointAvg_unifProfile ω
    (fun k => max 1 ‖Savg k‖) q31
  refine ⟨M2, hM2, Savg, ω, hω, hωlim, hSbound, q31, hq31, hq31lim,
    e, rfl, hprofile.1, hprofile.2, ?_⟩
  intro N hN A
  obtain ⟨qN, hqN, hAforG⟩ := hAall N hN A
  refine ⟨qN, hqN, ?_⟩
  intro G a ha
  obtain ⟨XN, UN, XG, UG, hXN, hXNmem, hUNmeas, hUNtime, hUNeq,
    hNphysical, hXG, hXGmem, hUGmeas, hUGtime, hUGeq, hGphysical, hSqErr⟩ :=
      hAforG G a ha
  obtain ⟨VηN, UBNTmp, hTimeηN, hTimeBN, _⟩ :=
    (S31.particle N hN A).2.2.2.2.2.2 a ha H hH
  let qηN : ℝ → A.Ω → r26t6_Coeff := fun u ζ =>
    fp81s21_particle_embedField p Es E (S31.qsηN N hN A u ζ)
  have hrepηN : fp81s21_MomentRep E A.P
      (fp81s21_particleEmpField R N A) qηN S31.MN := by
    simpa [qηN] using (S31.particle N hN A).2.2.2.2.1
  have hsecηN : ∀ u, 0 ≤ u →
      (fun ζ => qN u ζ) =ᵐ[A.P] (fun ζ => qηN u ζ) := by
    intro u hu
    exact fp81s21_MomentRep_eq_ae
      (by nlinarith [p.hd]) E A.P (fp81s21_particleEmpField R N A)
      qN qηN M2 S31.MN hqN hrepηN u hu
  have hVηN : fp81s21_TimeL2Rep A.P qηN S31.MN a H VηN :=
    fp81s21_TimeRep_to_TimeL2Rep E A.P
      (fp81s21_particleEmpField R N A) qηN S31.MN a H VηN hTimeηN
  have hUNto31 := fp81s21_TimeL2Rep_congr_ae A.P qN qηN M2 S31.MN a H
    UN VηN hqN.1 hrepηN.1 ha hsecηN hUNtime hVηN
  have hUNid := fp81s21_MomentRep_TimeL2Rep_identification
    (by nlinarith [p.hd]) E A.P (fp81s21_particleEmpField R N A)
    qN qηN M2 S31.MN a H UN VηN hqN.1 hrepηN.1 ha hqN hrepηN
    hUNtime hVηN
  have hUBN : fp81s21_TimeL2Rep A.P
      (fun u ζ => fp81s21_particle_embedField p Es E (S31.qsBN N hN A u ζ))
      S31.MN a H UBNTmp :=
    fp81s21_TimeRep_to_TimeL2Rep E A.P
      (fp81s21_particleQuadField R N A)
      (fun u ζ => fp81s21_particle_embedField p Es E (S31.qsBN N hN A u ζ))
      S31.MN a H UBNTmp hTimeBN
  obtain ⟨VηG, hTimeηG, _⟩ :=
    (S31.gaussian.gaussian_linear G).time_representation a ha H hH
  have hrepηG := (canon.payload G).coefficients.weak_momentRep
  have hrep31G := (S31.gaussian.gaussian_linear G).coefficients.weak_momentRep
  let qηG : ℝ → G.Ω → r26t6_Coeff :=
    fp81s21_gaussian_embedFamily p Es E (S31.gaussian.qsηG G)
  have hVηG : fp81s21_TimeL2Rep G.P qηG S31.gaussian.MηG a H VηG :=
    fp81s21_TimeRep_to_TimeL2Rep E G.P (fp81s21_gaussian_Qhat E qηG)
      qηG S31.gaussian.MηG a H VηG hTimeηG
  have hsecηG : ∀ u, 0 ≤ u →
      (fun ζ => fp81s21_gaussian_embedFamily p Es E (canon.q G) u ζ) =ᵐ[G.P]
        (fun ζ => qηG u ζ) := by
    intro u hu
    exact fp81s21_MomentRep_eq_ae
      (by nlinarith [p.hd]) E G.P
      (fun v ζ f => OscDual.eval (G.Z v ζ) f)
      (fp81s21_gaussian_embedFamily p Es E (canon.q G)) qηG
      MUG S31.gaussian.MηG hrepηG hrep31G u hu
  have hUGto31 := fp81s21_TimeL2Rep_congr_ae G.P
    (fp81s21_gaussian_embedFamily p Es E (canon.q G)) qηG
    MUG S31.gaussian.MηG a H UG VηG hrepηG.1 hrep31G.1 ha hsecηG
    hUGtime hVηG
  have hUGid := fp81s21_MomentRep_TimeL2Rep_identification
    (by nlinarith [p.hd]) E G.P
    (fun v ζ f => OscDual.eval (G.Z v ζ) f)
    (fp81s21_gaussian_embedFamily p Es E (canon.q G)) qηG
    MUG S31.gaussian.MηG a H UG VηG hrepηG.1 hrep31G.1 ha
    hrepηG hrep31G hUGtime hVηG
  obtain ⟨UBG, hUBG, _⟩ :=
    (S31.gaussian.quadratic.payload G).2.2.2.2.2.2.2 a ha H hH
  have hsource := hClose N hN A G a ha UN UBNTmp UG UBG
    hUNto31 hUBN hUGto31 hUBG
  have hprod : (Prod.instMeasurableSpace : MeasurableSpace
      (fp81s21_jointP_U H × fp81s21_jointP_U H)) = borel _ :=
    @BorelSpace.measurable_eq _ _ Prod.instMeasurableSpace Prod.borelSpace
  have hcloseProd :
      (fp81s21_jointClose9_pair_measSpace H : MeasurableSpace
        (fp81s21_jointP_U H × fp81s21_jointP_U H)) = borel _ := rfl
  have hinst : (Prod.instMeasurableSpace : MeasurableSpace
      (fp81s21_jointP_U H × fp81s21_jointP_U H)) =
        fp81s21_jointClose9_pair_measSpace H := hprod.trans hcloseProd.symm
  have hsourceAvg := hsource
  rw [← hinst] at hsourceAvg
  have hPavg := hSqErr
  have hfinal : wassersteinE 2
      (law A.P (fun ζ => (XN ζ, UBNTmp ζ)))
      (law G.P (fun ζ => (XG ζ, UBG ζ))) ≤ ENNReal.ofReal (e N) := by
    calc
      wassersteinE 2
          (law A.P (fun ζ => (XN ζ, UBNTmp ζ)))
          (law G.P (fun ζ => (XG ζ, UBG ζ))) ≤
          ⨅ k : ℕ, ENNReal.ofReal
            (2 * ω k + max 1 ‖Savg k‖ * q31 N) :=
        le_iInf fun k => fp81s21_jointAvg_wasserstein
          A.P G.P UN UBNTmp UG UBG XN XG (Savg k)
          hUNto31.1 hUBN.1 hXN hUGto31.1 hUBG.1 hXG
          (ω k) (q31 N) (hω k) (hq31 N) hsourceAvg
          (hPavg k).1 (hPavg k).2
      _ = ENNReal.ofReal (e N) := by
        rw [show e = fp81s21_jointAvg_unifProfile ω
          (fun k => max 1 ‖Savg k‖) q31 from rfl]
        change (⨅ k : ℕ, ENNReal.ofReal
            (2 * ω k + max 1 ‖Savg k‖ * q31 N)) =
          ENNReal.ofReal (⨅ k : ℕ,
            (2 * ω k + max 1 ‖Savg k‖ * q31 N))
        exact (ENNReal.ofReal_iInf
          (fun k : ℕ => 2 * ω k + max 1 ‖Savg k‖ * q31 N)).symm
  refine ⟨XN, UN, VηN, UBNTmp, XG, UG, VηG, UBG,
    hXN, hXNmem, hUNto31, hVηN, hUNid,
    hUBN.1, hUBN.2.1, hUBN, hUNeq, hNphysical,
    hXG, hXGmem, hUGto31, hVηG, hUGid,
    hUBG.1, hUBG.2.1, hUBG, hUGeq, hGphysical, hSqErr, hfinal⟩

#print axioms fp81s21_TimeL2Rep_congr_ae
#print axioms fp81s21_MomentRep_TimeL2Rep_identification
#print axioms fp81s21_physical_joint_comparison

end HRS.Fp81.S21

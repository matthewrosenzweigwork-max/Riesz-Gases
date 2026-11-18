import HRS.MS.Fp81S21VersionNTime
import HRS.MS.Fp81S21VersionNTime2
import HRS.MS.Fp81S21TimeRep16

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Set
open scoped ENNReal

namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6

local instance fp81s21_versionNTime3_UH_measSpace (H : ℝ) : MeasurableSpace
    (fp81s21_SmoothUH H) := borel _
local instance fp81s21_versionNTime3_UH_borelSpace (H : ℝ) : BorelSpace
    (fp81s21_SmoothUH H) := ⟨rfl⟩
local instance fp81s21_versionNTime3_CH_measSpace (H : ℝ) : MeasurableSpace
    (fp81s21_SmoothCH H) := borel _
local instance fp81s21_versionNTime3_CH_borelSpace (H : ℝ) : BorelSpace
    (fp81s21_SmoothCH H) := ⟨rfl⟩

/-- The packet-30 particle time class is the class of a continuous physical
version, with uniform Hölder envelope and simultaneous compact-test identity. -/
theorem fp81s21_particle_V2N_physical (p : Parameters) :
    ∃ Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4),
    ∃ E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2),
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ R : Trajectory p δ,
        ∀ H : ℝ, (hH : 0 < H) →
          ∃ M2 : ℝ, 0 ≤ M2 ∧
          ∃ DN : ℝ, 0 ≤ DN ∧
            ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N,
              ∃ qN : ℝ → A.Ω → r26t6_Coeff,
                fp81s21_MomentRep E A.P (fp81s21_particleEmpField R N A) qN M2 ∧
                ∀ a : ℝ, 0 ≤ a →
                  ∃ XN : A.Ω → fp81s21_SmoothCH H,
                    Measurable XN ∧ MemLp XN 2 A.P ∧
                    (∀ t : Icc (0 : ℝ) H,
                      (fun ω => XN ω t) =ᵐ[A.P] qN (a + t)) ∧
                    ∃ BN : A.Ω → ℝ,
                      Measurable BN ∧ (∀ ω, 0 ≤ BN ω) ∧
                      Integrable (fun ω => BN ω ^ 2) A.P ∧
                      (∫ ω, BN ω ^ 2 ∂A.P) ≤ DN ∧
                      (∀ᵐ ω ∂A.P, ∀ s t : Icc (0 : ℝ) H,
                        ‖XN ω s - XN ω t‖ ≤
                          BN ω * |(s : ℝ) - t| ^ (1 / 8 : ℝ)) ∧
                      ∃ UN : A.Ω → fp81s21_SmoothUH H,
                        fp81s21_TimeL2Rep A.P qN M2 a H UN ∧
                        UN =ᵐ[A.P] (fun ω => fp81s21_smoothPathToL2 H hH (XN ω)) ∧
                        ∀ᵐ ω ∂A.P, ∀ t : Icc (0 : ℝ) H,
                          ∀ f : Euc p.d → ℝ, IsR2Test f →
                            fp81s21_chartAction E (XN ω t) f =
                              fp81s21_particleEmpField R N A (a + (t : ℝ)) ω f := by
  obtain ⟨CL, hCL, Es, E, δV, hδV, hδVhalf, hV⟩ :=
    fp81s21_particle_continuous_version_physical p
  obtain ⟨ε, hε, hεlim, δT, hδT, hδThalf, hT⟩ :=
    fp81s21_particle_weakChart_time_tails p Es E
  refine ⟨Es, E, min δV δT, lt_min hδV hδT,
    le_trans (min_le_left _ _) hδVhalf, ?_⟩
  intro δ hδ hδle R H hH
  obtain ⟨MV, M6, Cm, hMV, hM6, hCm, L, hLm, hLb, qs, qB, m, hdata, hversions⟩ :=
    hV δ hδ (le_trans hδle (min_le_left _ _)) R
  obtain ⟨MT, hMT, htime⟩ := hT δ hδ (le_trans hδle (min_le_right _ _)) R
  obtain ⟨Cη, DN, hCη, hDN, hX⟩ := hversions H hH
  refine ⟨MT, hMT, DN, hDN, ?_⟩
  intro N hN A
  obtain ⟨qstrong, qquad, hstrong, hquad, hfirst, hqfirst, hweak, hqweak, htimeA⟩ :=
    htime N hN A
  let qN : ℝ → A.Ω → r26t6_Coeff :=
    fun u ω => fp81s21_particle_embedField p Es E (qstrong u ω)
  let qV : ℝ → A.Ω → r26t6_Coeff :=
    fun u ω => fp81s21_gaussian_chartEmbed p Es E (qs N hN A u ω)
  have hrepN : fp81s21_MomentRep E A.P (fp81s21_particleEmpField R N A) qN MT := hweak
  have hrepV : fp81s21_MomentRep E A.P (fp81s21_particleEmpField R N A) qV MV := by
    simpa [qV, fp81s21_gaussian_chartEmbed] using
      fp81s21_MomentRep_embedField_normalized (by omega) (by ring)
        (by nlinarith) (by nlinarith) Es E A.P
        (fp81s21_particleEmpField R N A) (qs N hN A) MV (hdata N hN A).1
  have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by nlinarith [p.hd]
  have heq := fp81s21_MomentRep_eq_ae hP E A.P
    (fp81s21_particleEmpField R N A) qN qV MT MV hrepN hrepV
  refine ⟨qN, hrepN, ?_⟩
  intro a ha
  obtain ⟨XN, hXN, hXNmem, hsecV, BN, hBN, hBN0, hBNint, hBNbound, hholder⟩ :=
    hX N hN A a ha
  have hsec : ∀ t : Icc (0 : ℝ) H, (fun ω => XN ω t) =ᵐ[A.P] qN (a + t) := by
    intro t
    filter_upwards [hsecV t, heq (a + t) (add_nonneg ha t.property.1)] with ω hx hq
    exact hx.trans hq.symm
  obtain ⟨UN, UB, hUN, hUB, htails⟩ := htimeA a ha H hH
  have hcore : fp81s21_TimeL2Rep A.P qN MT a H UN := by
    refine ⟨hUN.1, hUN.2.1, hUN.2.2.1, ?_⟩
    filter_upwards [hUN.2.2.2] with ω hω
    refine ⟨hω.1, ?_⟩
    filter_upwards [hω.2] with t ht
    exact ht.1
  have hUeq := fp81s21_TimeL2Rep_eq_continuous_version
    A.P H MT a hH qN UN XN hrepN.1 hcore hXN hsec
  have hphysical := fp81s21_particle_simultaneous_identity p R hδ
    (le_trans hδle (le_trans (min_le_left _ _) hδVhalf))
    E N hN A a H ha hH MT qN hrepN XN hsec
  refine ⟨XN, hXN, hXNmem, hsec, BN, hBN, hBN0, hBNint, hBNbound, ?_,
    UN, hcore, hUeq, hphysical⟩
  filter_upwards [hholder] with ω hω
  intro s t
  exact hω t s

#print axioms HRS.Fp81.S21.fp81s21_particle_V2N_physical

end HRS.Fp81.S21

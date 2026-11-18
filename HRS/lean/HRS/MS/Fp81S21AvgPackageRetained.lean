import HRS.MS.Fp81S21AvgPackage
import HRS.MS.Fp81S21VersionGTime2
import HRS.MS.Fp81S21VersionNTime3

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6

local instance fp81s21_retained_UH_measSpace (H : ℝ) : MeasurableSpace
    (fp81s21_SmoothUH H) := borel _
local instance fp81s21_retained_UH_borelSpace (H : ℝ) : BorelSpace
    (fp81s21_SmoothUH H) := ⟨rfl⟩

private theorem fp81s21_retained_sqErr_right_congr_ae
    {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V]
    (P : Measure Ω) (f g g' : Ω → V) (ε : ℝ)
    (hgg' : g =ᵐ[P] g')
    (hSq : fp81s21_SqErr P f g ε) :
    fp81s21_SqErr P f g' ε := by
  have hErr : (fun ω => ‖f ω - g ω‖ ^ 2) =ᵐ[P]
      (fun ω => ‖f ω - g' ω‖ ^ 2) := by
    filter_upwards [hgg'] with ω hω
    simp [hω]
  refine ⟨hSq.1.congr hErr, ?_⟩
  calc
    (∫ ω, ‖f ω - g' ω‖ ^ 2 ∂P) =
        ∫ ω, ‖f ω - g ω‖ ^ 2 ∂P := integral_congr_ae hErr.symm
    _ ≤ ε ^ 2 := hSq.2

/-- Physical averaging with the original particle and canonical Gaussian
 time classes retained alongside their continuous versions. -/
theorem fp81s21_physical_avgPackage_retained (p : Parameters) :
    ∃ Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4),
    ∃ E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2),
    ∃ ε : ℕ → ℝ, (∀ m, 0 ≤ ε m) ∧ Tendsto ε atTop (𝓝 0) ∧
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ R : Trajectory p δ,
        ∃ MUG : ℝ, 0 ≤ MUG ∧
        ∃ canon : fp81s21_gaussian_V2_G_canonicalFamily p Es E R MUG ε,
        ∀ H : ℝ, (hH : 0 < H) →
          ∃ M2 : ℝ, 0 ≤ M2 ∧
          ∃ S : ℕ → fp81s21_SmoothUH H →L[ℝ] fp81s21_SmoothCH H,
          ∃ ω : ℕ → ℝ,
            (∀ k, 0 ≤ ω k) ∧ Tendsto ω atTop (𝓝 0) ∧
            (∀ k, ‖S k‖ ≤ Real.sqrt (((k : ℝ) + 2) / H)) ∧
            ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N,
              ∃ qN : ℝ → A.Ω → r26t6_Coeff,
                fp81s21_MomentRep E A.P (fp81s21_particleEmpField R N A) qN M2 ∧
                ∀ G : GaussianRealization R, ∀ a : ℝ, 0 ≤ a →
                  ∃ XN : A.Ω → fp81s21_SmoothCH H,
                  ∃ UN : A.Ω → fp81s21_SmoothUH H,
                  ∃ XG : G.Ω → fp81s21_SmoothCH H,
                  ∃ UG : G.Ω → fp81s21_SmoothUH H,
                    Measurable XN ∧ MemLp XN 2 A.P ∧ Measurable UN ∧
                    fp81s21_TimeL2Rep A.P qN M2 a H UN ∧
                    UN =ᵐ[A.P] (fun ζ => fp81s21_smoothPathToL2 H hH (XN ζ)) ∧
                    (∀ᵐ ζ ∂A.P, ∀ t : Icc (0 : ℝ) H,
                      ∀ f : Euc p.d → ℝ, IsR2Test f →
                        fp81s21_chartAction E (XN ζ t) f =
                          fp81s21_particleEmpField R N A (a + (t : ℝ)) ζ f) ∧
                    Measurable XG ∧ MemLp XG 2 G.P ∧ Measurable UG ∧
                    fp81s21_TimeL2Rep G.P
                      (fp81s21_gaussian_embedFamily p Es E (canon.q G)) MUG a H UG ∧
                    UG =ᵐ[G.P] (fun ζ => fp81s21_smoothPathToL2 H hH (XG ζ)) ∧
                    (∀ᵐ ζ ∂G.P, ∀ t : Icc (0 : ℝ) H,
                      ∀ f : Euc p.d → ℝ, IsR2Test f →
                        fp81s21_chartAction E (XG ζ t) f =
                          OscDual.eval (G.Z (a + t) ζ) f) ∧
                    ∀ k : ℕ,
                      fp81s21_SqErr A.P XN (fun ζ => S k (UN ζ)) (ω k) ∧
                      fp81s21_SqErr G.P XG (fun ζ => S k (UG ζ)) (ω k) := by
  obtain ⟨Es, E, δN, hδN, hδNhalf, hV2N⟩ :=
    fp81s21_particle_V2N_physical p
  obtain ⟨ε, hε, hεlim, δG, hδG, hδGhalf, hV2G⟩ :=
    fp81s21_gaussian_V2_G_physical p Es E
  refine ⟨Es, E, ε, hε, hεlim, min δN δG, lt_min hδN hδG,
    le_trans (min_le_left _ _) hδNhalf, ?_⟩
  intro δ hδ hδle R
  obtain ⟨M2G, M6G, hM2G, hM6G, MUG, hMUG, canon, hForH⟩ :=
    hV2G δ hδ (hδle.trans (min_le_right _ _)) R
  refine ⟨MUG, hMUG, canon, ?_⟩
  intro H hH
  obtain ⟨M2, hM2, DN, hDN, hV2Nall⟩ :=
    hV2N δ hδ (hδle.trans (min_le_left _ _)) R H hH
  obtain ⟨DG, hDG, hForG⟩ := hForH H hH
  let D : ℝ := max DN DG
  have hD : 0 ≤ D := le_trans hDN (le_max_left DN DG)
  let S : ℕ → fp81s21_SmoothUH H →L[ℝ] fp81s21_SmoothCH H :=
    fun k => fp81s21_avgOperator H hH k
  let ω : ℕ → ℝ := fun k => Real.sqrt D *
    (H / ((k : ℝ) + 2)) ^ (1 / 8 : ℝ)
  have hprofile := fp81s21_avgPackage_profile H D hH hD
  refine ⟨M2, hM2, S, ω, ?_, ?_, ?_, ?_⟩
  · intro k
    simpa [ω, D] using hprofile.1 k
  · simpa [ω, D] using hprofile.2.1
  · intro k
    simpa [S] using hprofile.2.2 k
  · intro N hN A
    obtain ⟨qN, hqN, hForA⟩ := hV2Nall N hN A
    refine ⟨qN, hqN, ?_⟩
    intro G a ha
    obtain ⟨XN, hXN, hXNmem, hNsec, BN, hBN, hBN0, hBNint,
      hBNbound, hNholder, UN, hUNtime, hUNeq, hNphysical⟩ := hForA a ha
    obtain ⟨qsG, hGstrong, hGsix, hGweak, hGweakSix, hForGa⟩ := hForG G
    obtain ⟨XG, hXG, hXGmem, hGsec, BG, hBG, hBG0, hBGint,
      hBGbound, hGholder, UG, hUGtime, hUGeq, hGphysical⟩ := hForGa a ha
    have hBNbound' : (∫ ζ, BN ζ ^ 2 ∂A.P) ≤ D := by
      exact le_trans hBNbound (by dsimp [D]; exact le_max_left DN DG)
    have hBGbound' : (∫ ζ, BG ζ ^ 2 ∂G.P) ≤ D := by
      exact le_trans hBGbound (by dsimp [D]; exact le_max_right DN DG)
    refine ⟨XN, UN, XG, UG, hXN, hXNmem, hUNtime.1, hUNtime, hUNeq, hNphysical,
      hXG, hXGmem, hUGtime.1, hUGtime, hUGeq, hGphysical, ?_⟩
    intro k
    have hGholder' : ∀ᵐ ζ ∂G.P, ∀ s t : Icc (0 : ℝ) H,
        ‖XG ζ s - XG ζ t‖ ≤ BG ζ * |(s : ℝ) - (t : ℝ)| ^ (1 / 8 : ℝ) := by
      filter_upwards [hGholder] with ζ hζ
      intro s t
      exact hζ t s
    have hPair := fp81s21_avgOperator_SqErr_pair
      A.P G.P H D hH hD k XN BN hXN hBN hBN0 hBNint hBNbound' hNholder
      XG BG hXG hBG hBG0 hBGint hBGbound' hGholder'
    have hPairN : fp81s21_SqErr A.P XN
        (fun ζ => S k
          (fp81s21_smoothPathToL2 H hH (XN ζ))) (ω k) := by
      simpa [S, ω, D, fp81s21_avgHalfWidth] using hPair.1
    have hPairG : fp81s21_SqErr G.P XG
        (fun ζ => S k
          (fp81s21_smoothPathToL2 H hH (XG ζ))) (ω k) := by
      simpa [S, ω, D, fp81s21_avgHalfWidth] using hPair.2
    have hNavg : (fun ζ => S k (UN ζ)) =ᵐ[A.P]
        (fun ζ => S k (fp81s21_smoothPathToL2 H hH (XN ζ))) := by
      filter_upwards [hUNeq] with ζ hζ
      dsimp [S]
      rw [hζ]
    have hGavg : (fun ζ => S k (UG ζ)) =ᵐ[G.P]
        (fun ζ => S k (fp81s21_smoothPathToL2 H hH (XG ζ))) := by
      filter_upwards [hUGeq] with ζ hζ
      dsimp [S]
      rw [hζ]
    exact ⟨fp81s21_retained_sqErr_right_congr_ae
        A.P XN _ _ (ω k) hNavg.symm hPairN,
      fp81s21_retained_sqErr_right_congr_ae
        G.P XG _ _ (ω k) hGavg.symm hPairG⟩


#print axioms fp81s21_physical_avgPackage_retained

end HRS.Fp81.S21

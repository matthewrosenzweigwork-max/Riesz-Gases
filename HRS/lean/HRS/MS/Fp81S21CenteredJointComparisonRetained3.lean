import HRS.MS.Fp81S21CenteredJointComparison
import HRS.MS.Fp81S21CenteredJointComparisonRetained2

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6

private theorem fp81s21_centered_memLp_prodMk_retained
    {Ω B C : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [MeasurableSpace B] [MeasurableSpace C]
    (P : Measure Ω) (f : Ω → B) (g : Ω → C)
    (hfm : MemLp f 2 P) (hgm : MemLp g 2 P) :
    MemLp (fun ω => (f ω, g ω)) 2 P := by
  have hsum : MemLp (fun ω => ‖f ω‖ + ‖g ω‖) 2 P := hfm.norm.add hgm.norm
  have hpair : AEStronglyMeasurable (fun ω => (f ω, g ω)) P :=
    hfm.aestronglyMeasurable.prodMk hgm.aestronglyMeasurable
  apply hsum.mono' hpair
  filter_upwards with ω
  change max ‖f ω‖ ‖g ω‖ ≤ ‖f ω‖ + ‖g ω‖
  exact max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)

local instance fp81s21_centeredRetained_U_measSpace (H : ℝ) :
    MeasurableSpace (fp81s21_SmoothUH H) := borel _
local instance fp81s21_centeredRetained_U_borelSpace (H : ℝ) :
    BorelSpace (fp81s21_SmoothUH H) := ⟨rfl⟩
local instance fp81s21_centeredRetained_CH_measSpace (H : ℝ) :
    MeasurableSpace (fp81s21_SmoothCH H) := borel _
local instance fp81s21_centeredRetained_CH_borelSpace (H : ℝ) :
    BorelSpace (fp81s21_SmoothCH H) := ⟨rfl⟩

/-- Centered physical joint comparison, using the exact selections and profile
from `fp81s21_physical_joint_comparison`. -/
theorem fp81s21_physical_joint_comparison_centered_retained (p : Parameters) :
    ∃ Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4),
    ∃ E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2),
    ∃ εAvg : ℕ → ℝ, (∀ m, 0 ≤ εAvg m) ∧ Tendsto εAvg atTop (𝓝 0) ∧
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ MUG : ℝ, 0 ≤ MUG ∧
        ∃ canon : fp81s21_gaussian_V2_G_canonicalFamily p Es E R MUG εAvg,
        ∃ εN εG εB : ℕ → ℝ,
        (∀ m, 0 ≤ εN m) ∧ Tendsto εN atTop (𝓝 0) ∧
        (∀ m, 0 ≤ εG m) ∧ Tendsto εG atTop (𝓝 0) ∧
        (∀ m, 0 ≤ εB m) ∧ Tendsto εB atTop (𝓝 0) ∧
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
                      fp81s21_SqErr A.P XN (fun ζ => Savg k (UN ζ)) (ω k) ∧
                      fp81s21_SqErr G.P XG (fun ζ => Savg k (UG ζ)) (ω k)) ∧
                    Measurable (fun ζ => XN ζ - ∫ ζ', XN ζ' ∂A.P) ∧
                    MemLp (fun ζ => XN ζ - ∫ ζ', XN ζ' ∂A.P) 2 A.P ∧
                    Measurable (fun ζ => UBN ζ - ∫ ζ', UBN ζ' ∂A.P) ∧
                    MemLp (fun ζ => UBN ζ - ∫ ζ', UBN ζ' ∂A.P) 2 A.P ∧
                    Measurable (fun ζ => XG ζ - ∫ ζ', XG ζ' ∂G.P) ∧
                    MemLp (fun ζ => XG ζ - ∫ ζ', XG ζ' ∂G.P) 2 G.P ∧
                    Measurable (fun ζ => UBG ζ - ∫ ζ', UBG ζ' ∂G.P) ∧
                    MemLp (fun ζ => UBG ζ - ∫ ζ', UBG ζ' ∂G.P) 2 G.P ∧
                    wassersteinE 2
                      (law A.P (fun ζ => (XN ζ, UBN ζ)))
                      (law G.P (fun ζ => (XG ζ, UBG ζ))) ≤
                        ENNReal.ofReal (e N) ∧
                    wassersteinE 2
                      (law A.P (fun ζ =>
                        (XN ζ - (∫ ζ', XN ζ' ∂A.P),
                          UBN ζ - (∫ ζ', UBN ζ' ∂A.P))))
                      (law G.P (fun ζ =>
                        (XG ζ - (∫ ζ', XG ζ' ∂G.P),
                          UBG ζ - (∫ ζ', UBG ζ' ∂G.P)))) ≤
                        ENNReal.ofReal (2 * e N) := by
  obtain ⟨Es, E, εAvg, hεAvg, hεAvgLim, δ0, hδ0, hδ0h, hδ⟩ :=
    fp81s21_physical_joint_comparison_retained p
  refine ⟨Es, E, εAvg, hεAvg, hεAvgLim, δ0, hδ0, hδ0h, ?_⟩
  intro δ hδpos hδle R
  obtain ⟨MUG, hMUG, canon, εN, εG, εB, hn, hnl, hg, hgl, hb, hbl, S31, hδR⟩ := hδ δ hδpos hδle R
  refine ⟨MUG, hMUG, canon, εN, εG, εB, hn, hnl, hg, hgl, hb, hbl, S31, ?_⟩
  intro H hH
  obtain ⟨M2, hM2, Savg, ω, hω, hωlim, hSbound, q31, hq31, hq31lim,
    e, he, hepos, helim, hNall⟩ := hδR H hH
  refine ⟨M2, hM2, Savg, ω, hω, hωlim, hSbound, q31, hq31, hq31lim,
    e, he, hepos, helim, ?_⟩
  intro N hN A
  obtain ⟨qN, hqN, hGall⟩ := hNall N hN A
  refine ⟨qN, hqN, ?_⟩
  intro G a ha
  obtain ⟨XN, UN, VηN, UBN, XG, UG, VηG, UBG,
    hXN, hXN2, hUNtime, hVηNtime, hUNVηN, hUBN, hUBN2, hUBNtime,
    hUNpath, hNphysical, hXG, hXG2, hUGtime, hVηGtime, hUGVηG,
    hUBG, hUBG2, hUBGtime, hUGpath, hGphysical, hSqErr, hRaw⟩ := hGall G a ha
  have hXNcenterMeas : Measurable (fun ζ => XN ζ - ∫ ζ', XN ζ' ∂A.P) :=
    hXN.sub_const _
  have hXNcenterMem : MemLp (fun ζ => XN ζ - ∫ ζ', XN ζ' ∂A.P) 2 A.P :=
    hXN2.sub (memLp_const _)
  have hUBNcenterMeas : Measurable (fun ζ => UBN ζ - ∫ ζ', UBN ζ' ∂A.P) :=
    hUBN.sub_const _
  have hUBNcenterMem : MemLp (fun ζ => UBN ζ - ∫ ζ', UBN ζ' ∂A.P) 2 A.P :=
    hUBN2.sub (memLp_const _)
  have hXGcenterMeas : Measurable (fun ζ => XG ζ - ∫ ζ', XG ζ' ∂G.P) :=
    hXG.sub_const _
  have hXGcenterMem : MemLp (fun ζ => XG ζ - ∫ ζ', XG ζ' ∂G.P) 2 G.P :=
    hXG2.sub (memLp_const _)
  have hUBGcenterMeas : Measurable (fun ζ => UBG ζ - ∫ ζ', UBG ζ' ∂G.P) :=
    hUBG.sub_const _
  have hUBGcenterMem : MemLp (fun ζ => UBG ζ - ∫ ζ', UBG ζ' ∂G.P) 2 G.P :=
    hUBG2.sub (memLp_const _)
  have hpairN : Measurable (fun ζ => (XN ζ, UBN ζ)) := hXN.prodMk hUBN
  have hpairG : Measurable (fun ζ => (XG ζ, UBG ζ)) := hXG.prodMk hUBG
  have hpairN2 := fp81s21_centered_memLp_prodMk_retained A.P XN UBN hXN2 hUBN2
  have hpairG2 := fp81s21_centered_memLp_prodMk_retained G.P XG UBG hXG2 hUBG2
  have hcenter := fp81s21_centered_wassersteinE_le_two
    A.P G.P (fun ζ => (XN ζ, UBN ζ)) (fun ζ => (XG ζ, UBG ζ))
    hpairN hpairG hpairN2 hpairG2
  have hmeanN : (∫ ζ, (XN ζ, UBN ζ) ∂A.P) =
      (∫ ζ, XN ζ ∂A.P, ∫ ζ, UBN ζ ∂A.P) := by
    exact integral_pair (hXN2.integrable (by norm_num)) (hUBN2.integrable (by norm_num))
  have hmeanG : (∫ ζ, (XG ζ, UBG ζ) ∂G.P) =
      (∫ ζ, XG ζ ∂G.P, ∫ ζ, UBG ζ ∂G.P) := by
    exact integral_pair (hXG2.integrable (by norm_num)) (hUBG2.integrable (by norm_num))
  have hLawN : law A.P (fun ζ =>
      (XN ζ - (∫ ζ', XN ζ' ∂A.P), UBN ζ - (∫ ζ', UBN ζ' ∂A.P))) =
      law A.P (fun ζ => (XN ζ, UBN ζ) - ∫ ζ', (XN ζ', UBN ζ') ∂A.P) := by
    congr 1
    funext ζ
    rw [hmeanN]
    simp
  have hLawG : law G.P (fun ζ =>
      (XG ζ - (∫ ζ', XG ζ' ∂G.P), UBG ζ - (∫ ζ', UBG ζ' ∂G.P))) =
      law G.P (fun ζ => (XG ζ, UBG ζ) - ∫ ζ', (XG ζ', UBG ζ') ∂G.P) := by
    congr 1
    funext ζ
    rw [hmeanG]
    simp
  have hcenterToRaw : wassersteinE 2
      (law A.P (fun ζ =>
        (XN ζ - (∫ ζ', XN ζ' ∂A.P), UBN ζ - (∫ ζ', UBN ζ' ∂A.P))))
      (law G.P (fun ζ =>
        (XG ζ - (∫ ζ', XG ζ' ∂G.P), UBG ζ - (∫ ζ', UBG ζ' ∂G.P)))) ≤
      2 * wassersteinE 2
        (law A.P (fun ζ => (XN ζ, UBN ζ)))
        (law G.P (fun ζ => (XG ζ, UBG ζ))) := by
    rw [hLawN, hLawG]
    exact hcenter
  have hcenteredBound : wassersteinE 2
      (law A.P (fun ζ =>
        (XN ζ - (∫ ζ', XN ζ' ∂A.P), UBN ζ - (∫ ζ', UBN ζ' ∂A.P))))
      (law G.P (fun ζ =>
        (XG ζ - (∫ ζ', XG ζ' ∂G.P), UBG ζ - (∫ ζ', UBG ζ' ∂G.P)))) ≤
      ENNReal.ofReal (2 * e N) := by
    calc
      wassersteinE 2
          (law A.P (fun ζ =>
            (XN ζ - (∫ ζ', XN ζ' ∂A.P), UBN ζ - (∫ ζ', UBN ζ' ∂A.P))))
          (law G.P (fun ζ =>
            (XG ζ - (∫ ζ', XG ζ' ∂G.P), UBG ζ - (∫ ζ', UBG ζ' ∂G.P)))) ≤
        2 * wassersteinE 2
          (law A.P (fun ζ => (XN ζ, UBN ζ)))
          (law G.P (fun ζ => (XG ζ, UBG ζ))) := hcenterToRaw
      _ ≤ 2 * ENNReal.ofReal (e N) :=
        mul_le_mul_of_nonneg_left hRaw (by norm_num : (0 : ℝ≥0∞) ≤ 2)
      _ = ENNReal.ofReal (2 * e N) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
  refine ⟨XN, UN, VηN, UBN, XG, UG, VηG, UBG, ?_⟩
  exact ⟨hXN, hXN2, hUNtime, hVηNtime, hUNVηN, hUBN, hUBN2, hUBNtime,
    hUNpath, hNphysical, hXG, hXG2, hUGtime, hVηGtime, hUGVηG, hUBG, hUBG2,
    hUBGtime, hUGpath, hGphysical, hSqErr, hXNcenterMeas, hXNcenterMem,
    hUBNcenterMeas, hUBNcenterMem, hXGcenterMeas, hXGcenterMem,
    hUBGcenterMeas, hUBGcenterMem, hRaw, hcenteredBound⟩

#print axioms fp81s21_physical_joint_comparison_centered_retained

end HRS.Fp81.S21

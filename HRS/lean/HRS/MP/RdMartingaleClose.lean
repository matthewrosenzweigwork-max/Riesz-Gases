import HRS.MP.RdPropAssemble
import HRS.MP.RdLimitGauss

/-!
# S.A.24 on `ℝ^d`: closing `path_martingale_modulus_rd`

The kernel bounds of S.A.22 (`rpa_core`) feed the conditional clauses (a),(b)
(`path_martingale_modulus_rd_of_kernel`) and (c) (`path_limit_cont_rd_of_kernel`).  The statement is verbatim
`HRS.Whole.AppendixALemmas.path_martingale_modulus_rd`, tied by an `example`.

The S.A.22 limit clause needs `L.invβ ≤ νbar`, which the limit clause of S.A.24 does not assume.  Clause (c) is
an existence statement without constants, so the kernel bound is applied to `L.coeff S` with the constant of
S.A.22 for `νbar' = max νbar L.invβ` (a constant that may depend on `L`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MP.RdMartClose
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

variable {d : ℕ}

theorem path_martingale_modulus_rd_proof (s : ℝ) (fd : FieldDensityRd d s)
    (ν₀ MB Λ ΛV G₀ νbar T Kadj Cw C₀ m20 Ē : ℝ) (m₀ : ℕ) (hm₀' : m₀ ≤ mStar d) :
    ∃ (C : ℝ) (CL : ℝ → ℝ), ∀ (S : WholeMainData d), S.s = s → S.T = T → (∀ N, S.invβ N ≤ νbar) →
      fd.Holds S ν₀ → ∀ (R : ∀ N, RealizationRd d N) (𝔈 : ℕ → ℝ),
      RdStanding S R MB Λ ΛV G₀ m20 (fd.Gamma + 5) (fd.Gamma + 5) C₀ 𝔈 → (∀ N : ℕ, 1 ≤ N → 𝔈 N ≤ Ē) →
      PathAdjointInput S fd.Gamma m₀ Kadj Cw →
      ∀ (ℱ : ∀ N, Filtration ℝ (R N).mΩ) (W' : ∀ N, ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ),
      (∀ N : ℕ, 1 ≤ N → IsWholeFilteredSolution (R N).P (ℱ N) (W' N) (R N).W (R N).X) →
      ∀ (Mq : ∀ N, ℝ → (R N).Ω → HNeg d ((fd.Gamma + 2 : ℕ) : ℝ)),
      (∀ N : ℕ, 1 ≤ N → IsStochConvW (R N).P (ℱ N) (W' N) (S.coeff N)
        (S.sigma N * Real.sqrt (2 * S.invβ N) / N) (fd.Gamma + 2) T (R N).X (fun _ => T) (Mq N)) →
      (∃ Zc, ContVersionTight T (fun N => (R N).P) Mq Zc) ∧
      (∀ L : ℝ, 1 ≤ L → ∀ (MqL : ∀ N, ℝ → (R N).Ω → HNeg d ((fd.Gamma + 2 : ℕ) : ℝ)),
        (∀ N : ℕ, 1 ≤ N → IsStochConvW (R N).P (ℱ N) (W' N) (S.coeff N)
          (S.sigma N * Real.sqrt (2 * S.invβ N) / N) (fd.Gamma + 2) T (R N).X
          (tauNL T L (R N).X) (MqL N)) →
        (∃ (Zc ZcL : ∀ N, ℝ → (R N).Ω → HNeg d ((fd.Gamma + 2 : ℕ) : ℝ)),
          (∀ N : ℕ, 1 ≤ N → HasContVersion T (R N).P (Mq N) (Zc N)) ∧
          (∀ N : ℕ, 1 ≤ N → HasContVersion T (R N).P (MqL N) (ZcL N)) ∧
          (⨆ N : ℕ, ⨆ (_ : 1 ≤ N),
            (R N).P {ζ | ∃ t ∈ Set.Icc (0 : ℝ) T, ZcL N t ζ ≠ Zc N t ζ}) ≤ ENNReal.ofReal (C / L)) ∧
        (∀ N : ℕ, 1 ≤ N → ∀ s' ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
          ∫⁻ ζ, ‖MqL N t ζ - MqL N s' ζ‖ₑ ^ 4 ∂(R N).P ≤ ENNReal.ofReal (CL L * |t - s'| ^ 2))) ∧
      (∀ L : LimitCoeffsRd d, LimitPathHyp S L fd ν₀ Λ Kadj Cw m₀ →
        ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
          (Y : ℝ → Ω' → HNeg d ((fd.Gamma + 2 : ℕ) : ℝ)),
        IsAdjointDualityLimitW P' (L.coeff S) ((fd.Gamma + 2 : ℕ) : ℝ) L.A L.invβstar T
          (fun _ _ => 0) Y → ∃ Yc, HasContVersion T P' Y Yc) := by
  obtain ⟨C₁, hC₁⟩ := HRS.MP.RdProp.rpa_core s fd ν₀ MB Λ ΛV G₀ νbar T Kadj Cw m₀ hm₀'
  obtain ⟨C, CL, hCL⟩ := HRS.MP.RdMart.path_martingale_modulus_rd_of_kernel s fd MB Λ ΛV G₀ νbar T C₁
    C₀ m20 Ē
  refine ⟨C, CL, fun S hs hT hinv hHold R 𝔈 hstd hĒ hP ℱ W' hfilt Mq hMq => ?_⟩
  have hker := (hC₁ S hs hT hinv hHold hstd.matrix_bound hstd.mean_field hstd.potential hP).1
  obtain ⟨hab1, hab2⟩ := hCL S hs hT hinv R 𝔈 hstd hĒ (fun N hN => (hker N hN).2) ℱ W' hfilt Mq hMq
  refine ⟨hab1, hab2, fun L hL Ω' _ P' _ Y hY => ?_⟩
  obtain ⟨C₂, hC₂⟩ := HRS.MP.RdProp.rpa_core s fd ν₀ MB Λ ΛV G₀ (max νbar L.invβ) T Kadj Cw m₀ hm₀'
  have hker2 := (hC₂ S hs hT (fun N => (hinv N).trans (le_max_left _ _)) hHold hstd.matrix_bound
    hstd.mean_field hstd.potential hP).2 L hL (le_max_right _ _)
  exact HRS.MP.RdLGS.path_limit_cont_rd_of_kernel fd S L ν₀ Λ Kadj Cw m₀ T C₂ hT hL hker2.2 P' Y hY

example := (@path_martingale_modulus_rd_proof : type_of% @HRS.Whole.AppendixALemmas.path_martingale_modulus_rd)

end HRS.MP.RdMartClose

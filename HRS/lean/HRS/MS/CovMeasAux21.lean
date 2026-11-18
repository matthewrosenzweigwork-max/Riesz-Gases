import HRS.MS.CovMeasAux20

/-!
# S10.1 (worker S101B), part 21: the trace norm is subadditive; `S101Tr` is closed under sums and scalar multiples

`s101_Dm_ae_add`, `s101_Dm_ae_smul`: `D'^{z+z'} = D'^z + D'^{z'}` and `D'^{cz} = c D'^z` almost everywhere on `[0,T]`.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.CovMeas

open HRS HRS.Whole HRS.MS.Go HRS.MS.FixEq
open Classical

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {Pw : ℝ} {z z' : ℝ → (Euc d → ℝ) → ℝ}

abbrev S101Bil (d : ℕ) (m T : ℝ) : Type := KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ

lemma s101_tn_add_le {A B : S101Bil d m T}
    (hA : BddAbove (Set.range fun p : HRS.OrthonormalPairs (KSpace d m T) => ∑ i, |A (p.1.2.1 i) (p.1.2.2 i)|))
    (hB : BddAbove (Set.range fun p : HRS.OrthonormalPairs (KSpace d m T) => ∑ i, |B (p.1.2.1 i) (p.1.2.2 i)|)) :
    HRS.traceNormForm (A + B) ≤ HRS.traceNormForm A + HRS.traceNormForm B := by
  unfold HRS.traceNormForm
  refine Real.iSup_le (fun p => ?_) ?_
  · calc ∑ i, |(A + B) (p.1.2.1 i) (p.1.2.2 i)|
        ≤ ∑ i, (|A (p.1.2.1 i) (p.1.2.2 i)| + |B (p.1.2.1 i) (p.1.2.2 i)|) :=
          Finset.sum_le_sum fun i _ => by simpa using abs_add_le (A (p.1.2.1 i) (p.1.2.2 i)) (B (p.1.2.1 i) (p.1.2.2 i))
      _ = ∑ i, |A (p.1.2.1 i) (p.1.2.2 i)| + ∑ i, |B (p.1.2.1 i) (p.1.2.2 i)| := Finset.sum_add_distrib
      _ ≤ _ := add_le_add (le_ciSup hA p) (le_ciSup hB p)
  · exact add_nonneg (HRS.traceNormForm_nonneg _) (HRS.traceNormForm_nonneg _)

lemma s101_tn_smul_le (c : ℝ) {A : S101Bil d m T}
    (hA : BddAbove (Set.range fun p : HRS.OrthonormalPairs (KSpace d m T) => ∑ i, |A (p.1.2.1 i) (p.1.2.2 i)|)) :
    HRS.traceNormForm (c • A) ≤ |c| * HRS.traceNormForm A := by
  unfold HRS.traceNormForm
  refine Real.iSup_le (fun p => ?_) ?_
  · calc ∑ i, |(c • A) (p.1.2.1 i) (p.1.2.2 i)| = |c| * ∑ i, |A (p.1.2.1 i) (p.1.2.2 i)| := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
          simp [abs_mul]
      _ ≤ |c| * ⨆ p : HRS.OrthonormalPairs (KSpace d m T), ∑ i, |A (p.1.2.1 i) (p.1.2.2 i)| :=
          mul_le_mul_of_nonneg_left (le_ciSup hA p) (abs_nonneg _)
  · exact mul_nonneg (abs_nonneg _) (HRS.traceNormForm_nonneg _)

lemma s101_Dm_bdd (A : S101Adm C m T r Pw z) (hT : 0 ≤ T) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T) :
    BddAbove (Set.range fun p : HRS.OrthonormalPairs (KSpace d m T) =>
      ∑ i, |s101Dm C m T z τ (p.1.2.1 i) (p.1.2.2 i)|) := by
  obtain ⟨G, hG, hDm⟩ := s101_Dm_spec A hT
  obtain ⟨K0, hK0, hK⟩ := s101_D_data A.hd A.hP A.horb
  by_cases h : τ ∈ G
  · have e : s101Dm C m T z τ = s101D C m T z τ := by rw [hDm, if_pos h]
    rw [e]; exact (hK z A.hz τ hτ).2.2.1
  · have e : s101Dm C m T z τ = 0 := by rw [hDm, if_neg h]
    rw [e]
    refine ⟨0, ?_⟩
    rintro _ ⟨p, rfl⟩
    simp

lemma s101_Dm_entries_meas (A : S101Adm C m T r Pw z) (hT : 0 ≤ T) (x y : KSpace d m T) :
    Measurable fun τ => s101Dm C m T z τ x y := by
  obtain ⟨G, hG, hDm⟩ := s101_Dm_spec A hT
  have := hG.2.2.2 x y
  convert this using 1
  funext τ
  rw [hDm]; by_cases h : τ ∈ G <;> simp [h]

theorem s101_Dm_ae_add (A : S101Adm C m T r Pw z) (A' : S101Adm C m T r Pw z') (hT : 0 ≤ T) :
    ∀ᵐ τ ∂(volume.restrict (Icc (0 : ℝ) T)),
      s101Dm C m T (z + z') τ = s101Dm C m T z τ + s101Dm C m T z' τ := by
  filter_upwards [s101_Dm_ae_eq (A.add A') hT, s101_Dm_ae_eq A hT, s101_Dm_ae_eq A' hT,
    ae_restrict_mem measurableSet_Icc] with τ h1 h2 h3 hτ
  rw [h1, h2, h3, s101_D_add A A' hτ]

theorem s101_Dm_ae_smul (c : ℝ) (A : S101Adm C m T r Pw z) (hT : 0 ≤ T) :
    ∀ᵐ τ ∂(volume.restrict (Icc (0 : ℝ) T)), s101Dm C m T (c • z) τ = c • s101Dm C m T z τ := by
  filter_upwards [s101_Dm_ae_eq (A.smul c) hT, s101_Dm_ae_eq A hT, ae_restrict_mem measurableSet_Icc]
    with τ h1 h2 hτ
  rw [h1, h2, s101_D_smul c A hτ]

theorem S101Tr.add (A : S101Adm C m T r Pw z) (A' : S101Adm C m T r Pw z') (hT : 0 ≤ T)
    (h : S101Tr C m T z) (h' : S101Tr C m T z') : S101Tr C m T (z + z') := by
  unfold S101Tr at *
  have hm : Measurable fun τ => ENNReal.ofReal (HRS.traceNormForm (s101Dm C m T z τ)) :=
    ENNReal.measurable_ofReal.comp (HRS.measurable_traceNormForm _ (s101_Dm_entries_meas A hT))
  calc ∫⁻ τ in Icc (0 : ℝ) T, ENNReal.ofReal (HRS.traceNormForm (s101Dm C m T (z + z') τ))
      ≤ ∫⁻ τ in Icc (0 : ℝ) T, (ENNReal.ofReal (HRS.traceNormForm (s101Dm C m T z τ)) +
          ENNReal.ofReal (HRS.traceNormForm (s101Dm C m T z' τ))) := by
        refine lintegral_mono_ae ?_
        filter_upwards [s101_Dm_ae_add A A' hT, ae_restrict_mem measurableSet_Icc] with τ h1 hτ
        rw [h1, ← ENNReal.ofReal_add (HRS.traceNormForm_nonneg _) (HRS.traceNormForm_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (s101_tn_add_le (s101_Dm_bdd A hT hτ) (s101_Dm_bdd A' hT hτ))
    _ = _ + _ := lintegral_add_left hm _
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨h, h'⟩

theorem S101Tr.smul (c : ℝ) (A : S101Adm C m T r Pw z) (hT : 0 ≤ T) (h : S101Tr C m T z) :
    S101Tr C m T (c • z) := by
  unfold S101Tr at *
  calc ∫⁻ τ in Icc (0 : ℝ) T, ENNReal.ofReal (HRS.traceNormForm (s101Dm C m T (c • z) τ))
      ≤ ∫⁻ τ in Icc (0 : ℝ) T, ENNReal.ofReal |c| * ENNReal.ofReal (HRS.traceNormForm (s101Dm C m T z τ)) := by
        refine lintegral_mono_ae ?_
        filter_upwards [s101_Dm_ae_smul c A hT, ae_restrict_mem measurableSet_Icc] with τ h1 hτ
        rw [h1, ← ENNReal.ofReal_mul (abs_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (s101_tn_smul_le c (s101_Dm_bdd A hT hτ))
    _ = ENNReal.ofReal |c| * ∫⁻ τ in Icc (0 : ℝ) T, ENNReal.ofReal (HRS.traceNormForm (s101Dm C m T z τ)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top h

end HRS.MS.CovMeas

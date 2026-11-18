import HRS.MS.Fp81S21ParticleWindowSup3

/-! Generic path-supremum bridge from coordinate sixth moments. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole

/-- Every oscillator coordinate is bounded by the `OscDual` norm. -/
theorem fp81s21_oscDual_coord_abs_le_norm
    {d : ℕ} {m : ℝ} (u : OscDual d m) (α : MultiIndex d) :
    |OscDual.coord u α| ≤ ‖u‖ := by
  have hsumm := OscDual.coord_sq_summable' u
  have hsq : OscDual.coord u α ^ 2 ≤
      ∑' β : MultiIndex d, OscDual.coord u β ^ 2 :=
    hsumm.le_tsum α (fun β _ => sq_nonneg (OscDual.coord u β))
  calc
    |OscDual.coord u α| = Real.sqrt (OscDual.coord u α ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs]
    _ ≤ Real.sqrt (∑' β : MultiIndex d, OscDual.coord u β ^ 2) :=
      Real.sqrt_le_sqrt hsq
    _ = ‖u‖ := (OscDual.norm_eq_coord u).symm

/-- A coordinatewise sixth-moment budget, square summable across modes,
controls the sixth moment of the supremum of an oscillator-dual path. -/
theorem fp81s21_oscDual_path_sup_moment6_of_mode_moments
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} (hd : 0 < d) (m a b K : ℝ) (hab : a ≤ b)
    (L : ℝ → Ω → OscDual d m) (w : MultiIndex d → ℝ)
    (hK : 0 ≤ K) (hw : ∀ α, 0 ≤ w α)
    (hwsq : Summable fun α : MultiIndex d => w α ^ 2)
    (hLmeas : ∀ t ∈ Icc a b, AEMeasurable (L t) P)
    (hLcont : ∀ ω, ContinuousOn (fun t => L t ω) (Icc a b))
    (hMom : ∀ α : MultiIndex d,
      fp81s21_Moment6 P (fun ω => ⨆ t : Icc a b,
        |OscDual.coord (L t ω) α|) ((K * w α) ^ 6)) :
    fp81s21_Moment6 P (fun ω => ⨆ t : Icc a b, ‖L t ω‖)
      ((K * Real.sqrt (∑' α : MultiIndex d, w α ^ 2)) ^ 6) := by
  classical
  letI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  haveI : Infinite (MultiIndex d) := inferInstance
  let M : ℝ := K * Real.sqrt (∑' α : MultiIndex d, w α ^ 2)
  have hsumNonneg : 0 ≤ ∑' α : MultiIndex d, w α ^ 2 :=
    tsum_nonneg fun α => sq_nonneg (w α)
  have hM : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg hK (Real.sqrt_nonneg _)
  let S : MultiIndex d → Ω → ℝ := fun α ω =>
    ⨆ t : Icc a b, |OscDual.coord (L t ω) α|
  have hSmeas : ∀ α, AEStronglyMeasurable (S α) P := by
    intro α
    exact (hMom α).1.aestronglyMeasurable
  have hModeBound (α : MultiIndex d) :
      eLpNorm' (S α) 6 P ≤ ENNReal.ofReal (K * w α) := by
    exact fp81s21_moment6_eLpNorm'_bound P (S α) (K * w α)
      (mul_nonneg hK (hw α)) (by simpa [S] using hMom α)
  have hscaled : Summable fun α : MultiIndex d => (K * w α) ^ 2 := by
    simpa only [mul_pow] using hwsq.mul_left (K ^ 2)
  have hrealSum : (∑' α : MultiIndex d, (K * w α) ^ 2) = M ^ 2 := by
    calc
      (∑' α : MultiIndex d, (K * w α) ^ 2) =
          ∑' α : MultiIndex d, K ^ 2 * w α ^ 2 := by
            apply tsum_congr
            intro α
            ring
      _ = K ^ 2 * (∑' α : MultiIndex d, w α ^ 2) := tsum_mul_left
      _ = M ^ 2 := by
        dsimp [M]
        rw [mul_pow, Real.sq_sqrt hsumNonneg]
  have hsumMode :
      (∑' α : MultiIndex d, (eLpNorm' (S α) 6 P) ^ (2 : ℝ)) ≤
        ENNReal.ofReal (M ^ 2) := by
    calc
      (∑' α : MultiIndex d, (eLpNorm' (S α) 6 P) ^ (2 : ℝ)) ≤
          ∑' α : MultiIndex d, ENNReal.ofReal ((K * w α) ^ 2) := by
            apply ENNReal.tsum_le_tsum
            intro α
            calc
              (eLpNorm' (S α) 6 P) ^ (2 : ℝ) ≤
                  (ENNReal.ofReal (K * w α)) ^ (2 : ℝ) :=
                ENNReal.rpow_le_rpow (hModeBound α) (by norm_num)
              _ = ENNReal.ofReal ((K * w α) ^ 2) := by
                simp [ENNReal.ofReal_pow, mul_nonneg hK (hw α)]
      _ = ENNReal.ofReal (M ^ 2) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg
          (fun α : MultiIndex d => sq_nonneg (K * w α)) hscaled, hrealSum]
  let V : Ω → ℝ≥0∞ := fun ω => ∑' α : MultiIndex d, ‖S α ω‖ₑ ^ (2 : ℝ)
  have hnormSq (ω : Ω) (t : ℝ) (ht : t ∈ Icc a b) :
      (‖L t ω‖ₑ) ^ (2 : ℝ) ≤ V ω := by
    let u : OscDual d m := L t ω
    have hcoordSum : Summable fun α : MultiIndex d => (OscDual.coord u α) ^ 2 :=
      OscDual.coord_sq_summable' u
    have hcoordNonneg : 0 ≤ ∑' α : MultiIndex d, (OscDual.coord u α) ^ 2 :=
      tsum_nonneg fun α => sq_nonneg _
    have hnormEq : ENNReal.ofReal (‖u‖ ^ 2) =
        ∑' α : MultiIndex d, ‖OscDual.coord u α‖ₑ ^ (2 : ℝ) := by
      calc
        ENNReal.ofReal (‖u‖ ^ 2) = ENNReal.ofReal
            (∑' α : MultiIndex d, (OscDual.coord u α) ^ 2) := by
          rw [OscDual.norm_eq_coord u, Real.sq_sqrt hcoordNonneg]
        _ = ∑' α : MultiIndex d,
            ENNReal.ofReal ((OscDual.coord u α) ^ 2) :=
          ENNReal.ofReal_tsum_of_nonneg (fun α => sq_nonneg _) hcoordSum
        _ = ∑' α : MultiIndex d, ‖OscDual.coord u α‖ₑ ^ (2 : ℝ) := by
          apply tsum_congr
          intro α
          simp [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_pow, ← sq_abs]
    have hBddNorm : BddAbove (Set.range fun s : Icc a b => ‖L s ω‖) := by
      have hcompact : IsCompact ((fun s : ℝ => ‖L s ω‖) '' Icc a b) :=
        isCompact_Icc.image_of_continuousOn (hLcont ω).norm
      convert hcompact.bddAbove using 1
      ext y
      simp only [Set.mem_range, Set.mem_image, Subtype.exists]
      tauto
    let B : ℝ := ⨆ s : Icc a b, ‖L s ω‖
    have hterm (α : MultiIndex d) :
        ‖OscDual.coord u α‖ₑ ^ (2 : ℝ) ≤ ‖S α ω‖ₑ ^ (2 : ℝ) := by
      have hcoordBound (s : Icc a b) : |OscDual.coord (L s ω) α| ≤ B := by
        calc
          |OscDual.coord (L s ω) α| ≤ ‖L s ω‖ :=
            fp81s21_oscDual_coord_abs_le_norm (L s ω) α
          _ ≤ B := le_ciSup hBddNorm s
      have hBddCoord : BddAbove (Set.range fun s : Icc a b =>
          |OscDual.coord (L s ω) α|) := by
        refine ⟨B, ?_⟩
        rintro y ⟨s, rfl⟩
        exact hcoordBound s
      have hcoord : |OscDual.coord u α| ≤ S α ω := by
        change |OscDual.coord (L t ω) α| ≤
          (⨆ s : Icc a b, |OscDual.coord (L s ω) α|)
        exact le_ciSup hBddCoord ⟨t, ht⟩
      have hSnonneg : 0 ≤ S α ω := Real.iSup_nonneg fun s : Icc a b => abs_nonneg _
      have hcoordE : ‖OscDual.coord u α‖ₑ ≤ ‖S α ω‖ₑ := by
        rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
          abs_of_nonneg hSnonneg]
        exact ENNReal.ofReal_le_ofReal hcoord
      exact ENNReal.rpow_le_rpow hcoordE (by norm_num)
    have hsum := ENNReal.tsum_le_tsum hterm
    calc
      (‖L t ω‖ₑ) ^ (2 : ℝ) = ENNReal.ofReal (‖u‖ ^ 2) := by
        simp [u, ENNReal.ofReal_pow]
      _ = ∑' α : MultiIndex d, ‖OscDual.coord u α‖ₑ ^ (2 : ℝ) := hnormEq
      _ ≤ V ω := by
        simpa [V, S] using hsum
  have hnormRoot (ω : Ω) (t : Icc a b) :
      ‖L t ω‖ₑ ≤ V ω ^ (1 / 2 : ℝ) := by
    have h : ((‖L t ω‖ₑ) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
        V ω ^ (1 / 2 : ℝ) :=
      ENNReal.rpow_le_rpow (hnormSq ω t t.property) (by norm_num)
    calc
      ‖L t ω‖ₑ = ((‖L t ω‖ₑ) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
        simpa [one_div] using (ENNReal.rpow_rpow_inv (y := (2 : ℝ)) (by norm_num) _).symm
      _ ≤ V ω ^ (1 / 2 : ℝ) := h
  have hpoint (ω : Ω) :
      (⨆ t : Icc a b, ‖L t ω‖ₑ) ^ (6 : ℝ) ≤ V ω ^ (3 : ℝ) := by
    have hs : (⨆ t : Icc a b, ‖L t ω‖ₑ) ≤ V ω ^ (1 / 2 : ℝ) :=
      iSup_le fun t => hnormRoot ω t
    calc
      (⨆ t : Icc a b, ‖L t ω‖ₑ) ^ (6 : ℝ) ≤
          (V ω ^ (1 / 2 : ℝ)) ^ (6 : ℝ) :=
        ENNReal.rpow_le_rpow hs (by norm_num)
      _ = V ω ^ (3 : ℝ) := by
        rw [← ENNReal.rpow_mul]
        norm_num
  have hIntegral :
      (∫⁻ ω, (⨆ t : Icc a b, ‖L t ω‖ₑ) ^ (6 : ℝ) ∂P) ≤
      ∫⁻ ω, V ω ^ (3 : ℝ) ∂P :=
    lintegral_mono hpoint
  have hL3 := fp81s21_countable_tsum_square_l3_minkowski P S hSmeas
  have hRoot :
      (∫⁻ ω, (⨆ t : Icc a b, ‖L t ω‖ₑ) ^ (6 : ℝ) ∂P) ^ (1 / 6 : ℝ) ≤
        ENNReal.ofReal M := by
    calc
      (∫⁻ ω, (⨆ t : Icc a b, ‖L t ω‖ₑ) ^ (6 : ℝ) ∂P) ^ (1 / 6 : ℝ) ≤
          (∫⁻ ω, V ω ^ (3 : ℝ) ∂P) ^ (1 / 6 : ℝ) :=
        ENNReal.rpow_le_rpow hIntegral (by norm_num)
      _ = ((∫⁻ ω, V ω ^ (3 : ℝ) ∂P) ^ (1 / 3 : ℝ)) ^ (1 / 2 : ℝ) := by
        rw [← ENNReal.rpow_mul]
        norm_num
      _ ≤ (ENNReal.ofReal (M ^ 2)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (hL3.trans hsumMode) (by norm_num)
      _ ≤ ENNReal.ofReal M := by
        rw [one_div, ← ENNReal.le_rpow_inv_iff
          (by norm_num : 0 < (2 : ℝ)⁻¹), inv_inv]
        simpa [ENNReal.ofReal_pow hM]
  let X : ℝ → Ω → ℝ := fun t ω => ‖L t ω‖
  have hm : ∀ t ∈ Icc a b, AEMeasurable (X t) P := by
    intro t ht
    exact (hLmeas t ht).norm
  have hc : ∀ᵐ ω ∂P, ContinuousOn (fun t => X t ω) (Icc a b) := by
    filter_upwards with ω
    exact continuous_norm.comp_continuousOn (hLcont ω)
  have hRootX :
      (∫⁻ ω, (⨆ t : Icc a b, ‖X t ω‖ₑ) ^ (6 : ℝ) ∂P) ^ (1 / 6 : ℝ) ≤
        ENNReal.ofReal M := by
    simpa [X] using hRoot
  have hWindow := fp81s21_window_sup_moment6 P X a b M hab hM hm hc hRootX
  simpa [X, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hWindow

#print axioms HRS.Fp81.S21.fp81s21_oscDual_coord_abs_le_norm
#print axioms HRS.Fp81.S21.fp81s21_oscDual_path_sup_moment6_of_mode_moments
end HRS.Fp81.S21
end

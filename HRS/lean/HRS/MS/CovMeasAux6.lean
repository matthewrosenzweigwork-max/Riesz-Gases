import HRS.MS.CovMeasAux5

/-!
# S10.1 (worker S101B), part 6: the bilinear form `D(u,v) = η(F_{u⊗v})` of a bounded functional `η` on `E_{r,P}`

`s101_Dform_data`: for `Γ ∈ C^{r+1}(ℝ^d; H)` with `‖D^jΓ‖ ≤ B` and `η` bounded linear on the `C^r` functions of finite `E_{r,P}` norm
(`IsBoundedLinearOnE r P η`, `d < 2P`), there is a bounded bilinear form `Dc` on `H` with `Dc u v = η(F_{u⊗v})`, symmetric, with the
trace-norm sums bounded and `‖Dc‖_{𝔖₁} ≤ dualNormE(η) · c` (in `ℝ≥0∞`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.CovMeas

open HRS HRS.Whole HRS.MS.Go HRS.MS.FixEq

variable {d : ℕ}

section EtaForm

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {Γ : Euc d → H} {r : ℕ} {P B : ℝ} {η : (Euc d → ℝ) → ℝ}

lemma s101Cf_nonneg (hB : 0 ≤ B) (n : ℕ) : 0 ≤ s101Cf d n B := by
  unfold s101Cf; positivity

lemma s101_Fm_E_le (hP : (d : ℝ) < 2 * P) (hΓ : ContDiff ℝ ((r + 1 : ℕ) : WithTop ℕ∞) Γ)
    (hB : ∀ j ≤ r + 1, ∀ x, ‖iteratedFDeriv ℝ j Γ x‖ ≤ B) (Bil : H →L[ℝ] H →L[ℝ] ℝ) :
    weightedSobolevE r P (s101Fm Γ Bil) ≤ ENNReal.ofReal (s57pC d r P * (s101Cf d r B * ‖Bil‖)) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _) 0)
  have h0 : 0 ≤ s101Cf d r B * ‖Bil‖ := mul_nonneg (s101Cf_nonneg hB0 r) (ContinuousLinearMap.opNorm_nonneg _)
  exact s57p_E_le_cb hP h0 (s101_Fm_bound hΓ hB Bil)

lemma s101_Fm_test (hP : (d : ℝ) < 2 * P) (hΓ : ContDiff ℝ ((r + 1 : ℕ) : WithTop ℕ∞) Γ)
    (hB : ∀ j ≤ r + 1, ∀ x, ‖iteratedFDeriv ℝ j Γ x‖ ≤ B) (Bil : H →L[ℝ] H →L[ℝ] ℝ) :
    ContDiff ℝ (r : WithTop ℕ∞) (s101Fm Γ Bil) ∧ weightedSobolevE r P (s101Fm Γ Bil) < ⊤ :=
  ⟨s101_Fm_contDiff hΓ Bil, lt_of_le_of_lt (s101_Fm_E_le hP hΓ hB Bil) ENNReal.ofReal_lt_top⟩

/-- `Bil ↦ η(F_Bil)` as a linear map on bilinear forms. -/
def s101Lam (hP : (d : ℝ) < 2 * P) (hΓ : ContDiff ℝ ((r + 1 : ℕ) : WithTop ℕ∞) Γ)
    (hB : ∀ j ≤ r + 1, ∀ x, ‖iteratedFDeriv ℝ j Γ x‖ ≤ B) (hη : IsBoundedLinearOnE r P η) :
    (H →L[ℝ] H →L[ℝ] ℝ) →ₗ[ℝ] ℝ where
  toFun Bil := η (s101Fm Γ Bil)
  map_add' Bil₁ Bil₂ := by
    obtain ⟨h1, h1'⟩ := s101_Fm_test hP hΓ hB Bil₁
    obtain ⟨h2, h2'⟩ := s101_Fm_test hP hΓ hB Bil₂
    rw [s101_Fm_add]
    exact (hη.1 _ _ h1 h1' h2 h2' 1).1
  map_smul' a Bil := by
    obtain ⟨h1, h1'⟩ := s101_Fm_test hP hΓ hB Bil
    rw [s101_Fm_smul]
    have := (hη.1 _ _ h1 h1' h1 h1' a).2
    simpa using this

lemma s101Lam_apply (hP : (d : ℝ) < 2 * P) (hΓ : ContDiff ℝ ((r + 1 : ℕ) : WithTop ℕ∞) Γ)
    (hB : ∀ j ≤ r + 1, ∀ x, ‖iteratedFDeriv ℝ j Γ x‖ ≤ B) (hη : IsBoundedLinearOnE r P η)
    (Bil : H →L[ℝ] H →L[ℝ] ℝ) : s101Lam hP hΓ hB hη Bil = η (s101Fm Γ Bil) := rfl

lemma s101_eta_Fm_le_dual (hP : (d : ℝ) < 2 * P) (hΓ : ContDiff ℝ ((r + 1 : ℕ) : WithTop ℕ∞) Γ)
    (hB : ∀ j ≤ r + 1, ∀ x, ‖iteratedFDeriv ℝ j Γ x‖ ≤ B) (hη : IsBoundedLinearOnE r P η)
    (Bil : H →L[ℝ] H →L[ℝ] ℝ) :
    ENNReal.ofReal |η (s101Fm Γ Bil)| ≤
      dualNormE r P η * ENNReal.ofReal (s57pC d r P * (s101Cf d r B * ‖Bil‖)) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _) 0)
  have h := s57p_dual_bound hP hη (s101_Fm_contDiff hΓ Bil) (s101_Fm_bound hΓ hB Bil)
  exact h.trans (mul_le_mul' le_rfl (s101_Fm_E_le hP hΓ hB Bil))

lemma s101_eta_Fm_le_M (hP : (d : ℝ) < 2 * P) (hΓ : ContDiff ℝ ((r + 1 : ℕ) : WithTop ℕ∞) Γ)
    (hB : ∀ j ≤ r + 1, ∀ x, ‖iteratedFDeriv ℝ j Γ x‖ ≤ B) (hη : IsBoundedLinearOnE r P η) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ Bil : H →L[ℝ] H →L[ℝ] ℝ,
      |η (s101Fm Γ Bil)| ≤ M * (s57pC d r P * (s101Cf d r B * ‖Bil‖)) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _) 0)
  obtain ⟨M, hM⟩ := hη.2
  refine ⟨|M|, abs_nonneg _, fun Bil => ?_⟩
  obtain ⟨h1, h1'⟩ := s101_Fm_test hP hΓ hB Bil
  have h2 := hM _ h1 h1'
  have h3 : (weightedSobolevE r P (s101Fm Γ Bil)).toReal ≤ s57pC d r P * (s101Cf d r B * ‖Bil‖) := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (s101_Fm_E_le hP hΓ hB Bil)
    rwa [ENNReal.toReal_ofReal (mul_nonneg (s57pC_nonneg d r P)
      (mul_nonneg (s101Cf_nonneg hB0 r) (ContinuousLinearMap.opNorm_nonneg _)))] at this
  calc |η (s101Fm Γ Bil)| ≤ M * (weightedSobolevE r P (s101Fm Γ Bil)).toReal := h2
    _ ≤ |M| * (weightedSobolevE r P (s101Fm Γ Bil)).toReal :=
        mul_le_mul_of_nonneg_right (le_abs_self _) ENNReal.toReal_nonneg
    _ ≤ |M| * (s57pC d r P * (s101Cf d r B * ‖Bil‖)) :=
        mul_le_mul_of_nonneg_left h3 (abs_nonneg _)

open Classical in
theorem s101_Dform_data (hP : (d : ℝ) < 2 * P) (hΓ : ContDiff ℝ ((r + 1 : ℕ) : WithTop ℕ∞) Γ)
    (hB : ∀ j ≤ r + 1, ∀ x, ‖iteratedFDeriv ℝ j Γ x‖ ≤ B) (hη : IsBoundedLinearOnE r P η) :
    ∃ Dc : H →L[ℝ] H →L[ℝ] ℝ, (∀ u v, Dc u v = η (s101Fm Γ (s101Rk u v))) ∧
      (∀ u v, Dc u v = Dc v u) ∧
      (BddAbove (Set.range fun p : HRS.OrthonormalPairs H => ∑ i, |Dc (p.1.2.1 i) (p.1.2.2 i)|)) ∧
      ENNReal.ofReal (HRS.traceNormForm Dc) ≤
        dualNormE r P η * ENNReal.ofReal (s57pC d r P * s101Cf d r B) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _) 0)
  obtain ⟨M, hM0, hM⟩ := s101_eta_Fm_le_M hP hΓ hB hη
  set Λ := s101Lam hP hΓ hB hη with hΛ
  set Cst : ℝ := M * (s57pC d r P * s101Cf d r B) with hCst
  have hCst0 : 0 ≤ Cst := mul_nonneg hM0 (mul_nonneg (s57pC_nonneg d r P) (s101Cf_nonneg hB0 r))
  let f : H →ₗ[ℝ] H →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ (fun u v => Λ (s101Rk u v))
    (fun u u' v => by rw [s101Rk_add_left, map_add])
    (fun c u v => by rw [s101Rk_smul_left, map_smul])
    (fun u v v' => by rw [s101Rk_add_right, map_add])
    (fun c u v => by rw [s101Rk_smul_right, map_smul])
  have hbd : ∀ u v, ‖f u v‖ ≤ Cst * ‖u‖ * ‖v‖ := by
    intro u v
    show ‖Λ (s101Rk u v)‖ ≤ _
    rw [Real.norm_eq_abs, hΛ, s101Lam_apply]
    refine (hM _).trans ?_
    have := norm_s101Rk_le u v
    calc M * (s57pC d r P * (s101Cf d r B * ‖s101Rk u v‖))
        ≤ M * (s57pC d r P * (s101Cf d r B * (‖u‖ * ‖v‖))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left this (s101Cf_nonneg hB0 r)) (s57pC_nonneg d r P)) hM0
      _ = Cst * ‖u‖ * ‖v‖ := by rw [hCst]; ring
  set Dc : H →L[ℝ] H →L[ℝ] ℝ := f.mkContinuous₂ Cst hbd with hDc
  have hDcapp : ∀ u v, Dc u v = η (s101Fm Γ (s101Rk u v)) := fun u v => rfl
  have hsymm : ∀ u v, Dc u v = Dc v u := fun u v => by
    rw [hDcapp, hDcapp, s101Fm_Rk_symm]
  -- the signed sum
  have hsum : ∀ p : HRS.OrthonormalPairs H, ∃ Ω : H →L[ℝ] H →L[ℝ] ℝ, ‖Ω‖ ≤ 1 ∧
      ∑ i, |Dc (p.1.2.1 i) (p.1.2.2 i)| = η (s101Fm Γ Ω) := by
    intro p
    obtain ⟨he, hf⟩ := p.2
    set ε : Fin p.1.1 → ℝ := fun i => if 0 ≤ Dc (p.1.2.1 i) (p.1.2.2 i) then 1 else -1 with hε
    refine ⟨∑ i, ε i • s101Rk (p.1.2.1 i) (p.1.2.2 i), norm_signed_Rk_le he hf ε fun i => ?_, ?_⟩
    · simp only [hε]; split_ifs <;> simp
    · have : η (s101Fm Γ (∑ i, ε i • s101Rk (p.1.2.1 i) (p.1.2.2 i))) =
          Λ (∑ i, ε i • s101Rk (p.1.2.1 i) (p.1.2.2 i)) := rfl
      rw [this, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul]
      show _ = ε i * Dc (p.1.2.1 i) (p.1.2.2 i)
      simp only [hε]
      split_ifs with h
      · rw [abs_of_nonneg h]; ring
      · rw [abs_of_neg (not_le.1 h)]; ring
  refine ⟨Dc, hDcapp, hsymm, ?_, ?_⟩
  · refine ⟨Cst, ?_⟩
    rintro _ ⟨p, rfl⟩
    obtain ⟨Ω, hΩ, he⟩ := hsum p
    show ∑ i, |Dc (p.1.2.1 i) (p.1.2.2 i)| ≤ Cst
    rw [he]
    refine (le_abs_self _).trans ((hM Ω).trans ?_)
    rw [hCst]
    refine mul_le_mul_of_nonneg_left ?_ hM0
    refine mul_le_mul_of_nonneg_left ?_ (s57pC_nonneg d r P)
    calc s101Cf d r B * ‖Ω‖ ≤ s101Cf d r B * 1 := mul_le_mul_of_nonneg_left hΩ (s101Cf_nonneg hB0 r)
      _ = s101Cf d r B := mul_one _
  · set X := dualNormE r P η * ENNReal.ofReal (s57pC d r P * s101Cf d r B) with hX
    have hall : ∀ p : HRS.OrthonormalPairs H,
        ENNReal.ofReal (∑ i, |Dc (p.1.2.1 i) (p.1.2.2 i)|) ≤ X := by
      intro p
      obtain ⟨Ω, hΩ, he⟩ := hsum p
      rw [he]
      refine (ENNReal.ofReal_le_ofReal (le_abs_self _)).trans ?_
      refine (s101_eta_Fm_le_dual hP hΓ hB hη Ω).trans (mul_le_mul' le_rfl ?_)
      refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (s57pC_nonneg d r P))
      calc s101Cf d r B * ‖Ω‖ ≤ s101Cf d r B * 1 := mul_le_mul_of_nonneg_left hΩ (s101Cf_nonneg hB0 r)
        _ = s101Cf d r B := mul_one _
    by_cases hXtop : X = ⊤
    · rw [hXtop]; exact le_top
    · have hXr : ∀ p : HRS.OrthonormalPairs H, ∑ i, |Dc (p.1.2.1 i) (p.1.2.2 i)| ≤ X.toReal := by
        intro p
        have := ENNReal.toReal_mono hXtop (hall p)
        rwa [ENNReal.toReal_ofReal (Finset.sum_nonneg fun i _ => abs_nonneg _)] at this
      have : HRS.traceNormForm Dc ≤ X.toReal := Real.iSup_le hXr ENNReal.toReal_nonneg
      calc ENNReal.ofReal (HRS.traceNormForm Dc) ≤ ENNReal.ofReal X.toReal :=
            ENNReal.ofReal_le_ofReal this
        _ = X := ENNReal.ofReal_toReal hXtop

end EtaForm

end HRS.MS.CovMeas

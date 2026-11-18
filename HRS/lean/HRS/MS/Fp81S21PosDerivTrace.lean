import HRS.MS.CovMeasAux7

/-!
# S2.1 packet 15a: positive-order derivatives in the covariance trace estimate

Exact source declarations (from `HRS.MS.CovMeasAux5`, `CovMeasAux6`,
`CovMeasAux7`, `HRS.Whole.Orbits`, `HRS.Prob.HilbertMartingale`, and
`HRS.MS.FixEqP1Aux1`; statements are copied verbatim, with surrounding section
variables shown explicitly):

```lean
variable {d : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def s101Gk (Γ : Euc d → H) (k : Fin d) (x : Euc d) : H :=
  fderiv ℝ Γ x (EuclideanSpace.single k (1 : ℝ))

def s101Fm (Γ : Euc d → H) (Bil : H →L[ℝ] H →L[ℝ] ℝ) (x : Euc d) : ℝ :=
  ∑ k : Fin d, Bil (s101Gk Γ k x) (s101Gk Γ k x)

lemma s101_Fm_bound {Γ : Euc d → H} {n : ℕ}
    (hΓ : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) Γ) {B : ℝ}
    (hB : ∀ j ≤ n + 1, ∀ x, ‖iteratedFDeriv ℝ j Γ x‖ ≤ B)
    (Bil : H →L[ℝ] H →L[ℝ] ℝ) :
    ∀ j ≤ n, ∀ x,
      ‖iteratedFDeriv ℝ j (s101Fm Γ Bil) x‖ ≤ s101Cf d n B * ‖Bil‖

theorem s101_Dform_data {Γ : Euc d → H} {r : ℕ} {P B : ℝ}
    {η : (Euc d → ℝ) → ℝ}
    (hP : (d : ℝ) < 2 * P)
    (hΓ : ContDiff ℝ ((r + 1 : ℕ) : WithTop ℕ∞) Γ)
    (hB : ∀ j ≤ r + 1, ∀ x, ‖iteratedFDeriv ℝ j Γ x‖ ≤ B)
    (hη : IsBoundedLinearOnE r P η) :
    ∃ Dc : H →L[ℝ] H →L[ℝ] ℝ,
      (∀ u v, Dc u v = η (s101Fm Γ (s101Rk u v))) ∧
      (∀ u v, Dc u v = Dc v u) ∧
      (BddAbove (Set.range fun p : HRS.OrthonormalPairs H =>
        ∑ i, |Dc (p.1.2.1 i) (p.1.2.2 i)|)) ∧
      ENNReal.ofReal (HRS.traceNormForm Dc) ≤
        dualNormE r P η * ENNReal.ofReal (s57pC d r P * s101Cf d r B)

theorem s101_D_data (hd : 1 ≤ d) {C : WholeCoeff d} {m T : ℝ}
    {r : ℕ} {Pw : ℝ}
    (hP : (d : ℝ) < 2 * Pw) (horb : R2OrbitSummable C m T r) :
    ∃ K0 : ℝ, 0 ≤ K0 ∧
      ∀ z : ℝ → (Euc d → ℝ) → ℝ, S101Lin r Pw T z →
      ∀ τ ∈ Icc (0 : ℝ) T,
        (∀ u v, s101D C m T z τ u v =
          2 * C.ν * z τ (s101Fm (s101Gamma C m T τ) (s101Rk u v))) ∧
        (∀ u v, s101D C m T z τ u v = s101D C m T z τ v u) ∧
        BddAbove (Set.range fun p : HRS.OrthonormalPairs (KSpace d m T) =>
          ∑ i, |s101D C m T z τ (p.1.2.1 i) (p.1.2.2 i)|) ∧
        ENNReal.ofReal (HRS.traceNormForm (s101D C m T z τ)) ≤
          ENNReal.ofReal |2 * C.ν| * dualNormE r Pw (z τ) * ENNReal.ofReal K0

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]
def traceNormForm (C : H →L[ℝ] H →L[ℝ] ℝ) : ℝ :=
  ⨆ p : OrthonormalPairs H, ∑ i, |C (p.1.2.1 i) (p.1.2.2 i)|

def s57pC (d r : ℕ) (P : ℝ) : ℝ :=
  Real.sqrt ((s57pN d r : ℝ) * ∫ x : Euc d, s57pW d P x)

def dualNormE (r : ℕ) (P : ℝ) (η : (Euc d → ℝ) → ℝ) : ℝ≥0∞ :=
  ⨆ (f : Euc d → ℝ) (_ : ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      0 < weightedSobolevE r P f ∧ weightedSobolevE r P f < ⊤),
    ENNReal.ofReal |η f| / weightedSobolevE r P f
```

The existing formulas are credited above; the positive-order helpers below are
new declarations. In particular, positivity is taken from `hBpos`, never from
an order-zero derivative hypothesis.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.Go HRS.MS.FixEq HRS.MS.CovMeas

variable {d : ℕ}

/-- Positive-order derivative control for the spatial gradient features.
Copied from `s101_Gk_bound`, with the order-zero dependency removed. -/
lemma fp81s21_s101_Gk_bound_pos {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {Γ : Euc d → H} {n : ℕ}
    (hΓ : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) Γ) (k : Fin d)
    {Bpos : ℝ}
    (hPos : ∀ j : ℕ, 1 ≤ j → j ≤ n + 1 → ∀ x,
      ‖iteratedFDeriv ℝ j Γ x‖ ≤ Bpos) :
    ∀ i ≤ n, ∀ x,
      ‖iteratedFDeriv ℝ i (fun x => s101Gk Γ k x) x‖ ≤ Bpos := by
  intro i hi x
  have h1 := norm_iteratedFDeriv_clm_apply_const (𝕜 := ℝ) (f := fderiv ℝ Γ)
    (c := EuclideanSpace.single k (1 : ℝ)) (x := x) (N := (n : WithTop ℕ∞)) (n := i)
    ((hΓ.fderiv_right (m := n) (by push_cast; exact le_rfl)).contDiffAt)
    (by exact_mod_cast hi)
  rw [norm_iteratedFDeriv_fderiv] at h1
  have h2 : ‖(EuclideanSpace.single k (1 : ℝ) : Euc d)‖ = 1 := by simp
  rw [h2, one_mul] at h1
  exact h1.trans (hPos (i + 1) (by omega) (by omega) x)

/- The product-rule estimate for `s101Fm` is the existing `s101_Fm_bound`
   proof with `fp81s21_s101_Gk_bound_pos` supplying the derivative bounds. -/
lemma fp81s21_s101_Fm_bound_pos {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {Γ : Euc d → H} {n : ℕ}
    (hΓ : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) Γ)
    {Bpos : ℝ} (hBpos : 0 ≤ Bpos)
    (hPos : ∀ j : ℕ, 1 ≤ j → j ≤ n + 1 → ∀ x,
      ‖iteratedFDeriv ℝ j Γ x‖ ≤ Bpos)
    (Bil : H →L[ℝ] H →L[ℝ] ℝ) :
    ∀ j ≤ n, ∀ x,
      ‖iteratedFDeriv ℝ j (s101Fm Γ Bil) x‖ ≤
        s101Cf d n Bpos * ‖Bil‖ := by
  intro j hj x
  have hGk := fun k => s101_Gk_contDiff hΓ k
  have hGb := fun k => fp81s21_s101_Gk_bound_pos hΓ k hPos
  have hterm : ∀ k : Fin d,
      ‖iteratedFDeriv ℝ j
        (fun x => Bil (s101Gk Γ k x) (s101Gk Γ k x)) x‖ ≤
        ‖Bil‖ * (2 ^ n * Bpos ^ 2) := by
    intro k
    have h1 := ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear Bil
      (hGk k) (hGk k) x (n := j) (by exact_mod_cast hj)
    refine h1.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (ContinuousLinearMap.opNorm_nonneg _)
    calc ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun x => s101Gk Γ k x) x‖ *
          ‖iteratedFDeriv ℝ (j - i) (fun x => s101Gk Γ k x) x‖
        ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (Bpos * Bpos) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' : i ≤ j := by simpa [Nat.lt_succ_iff] using hi
          have a1 := hGb k i (hi'.trans hj) x
          have a2 := hGb k (j - i) ((Nat.sub_le _ _).trans hj) x
          rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          exact mul_le_mul a1 a2 (norm_nonneg _) hBpos
      _ = 2 ^ j * (Bpos * Bpos) := by
          rw [← Finset.sum_mul]
          congr 1
          exact_mod_cast Nat.sum_range_choose j
      _ ≤ 2 ^ n * Bpos ^ 2 := by
          rw [← sq]
          exact mul_le_mul_of_nonneg_right
            (pow_le_pow_right₀ (by norm_num) hj) (sq_nonneg _)
  have hsum : iteratedFDeriv ℝ j (s101Fm Γ Bil) x =
      ∑ k : Fin d, iteratedFDeriv ℝ j
        (fun x => Bil (s101Gk Γ k x) (s101Gk Γ k x)) x := by
    unfold s101Fm
    refine iteratedFDeriv_fun_sum_apply fun k _ => ?_
    exact (Bil.isBoundedBilinearMap.contDiff.comp
      ((hGk k).prodMk (hGk k))).contDiffAt.of_le (by exact_mod_cast hj)
  rw [hsum]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ k : Fin d, ‖iteratedFDeriv ℝ j
        (fun x => Bil (s101Gk Γ k x) (s101Gk Γ k x)) x‖
      ≤ ∑ _k : Fin d, ‖Bil‖ * (2 ^ n * Bpos ^ 2) :=
        Finset.sum_le_sum fun k _ => hterm k
    _ = s101Cf d n Bpos * ‖Bil‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, s101Cf]
        ring

lemma fp81s21_s101_Fm_E_le_pos {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {Γ : Euc d → H} {r : ℕ} {P : ℝ}
    (hP : (d : ℝ) < 2 * P)
    (hΓ : ContDiff ℝ ((r + 1 : ℕ) : WithTop ℕ∞) Γ)
    {Bpos : ℝ} (hBpos : 0 ≤ Bpos)
    (hPos : ∀ j : ℕ, 1 ≤ j → j ≤ r + 1 → ∀ x,
      ‖iteratedFDeriv ℝ j Γ x‖ ≤ Bpos)
    (Bil : H →L[ℝ] H →L[ℝ] ℝ) :
    weightedSobolevE r P (s101Fm Γ Bil) ≤
      ENNReal.ofReal (s57pC d r P * (s101Cf d r Bpos * ‖Bil‖)) := by
  have hC0 : 0 ≤ s101Cf d r Bpos * ‖Bil‖ :=
    mul_nonneg (s101Cf_nonneg hBpos r) (ContinuousLinearMap.opNorm_nonneg _)
  exact s57p_E_le_cb hP hC0
    (fp81s21_s101_Fm_bound_pos hΓ hBpos hPos Bil)

lemma fp81s21_s101_eta_Fm_le_dual_pos {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {Γ : Euc d → H} {r : ℕ} {P : ℝ}
    {η : (Euc d → ℝ) → ℝ} (hP : (d : ℝ) < 2 * P)
    (hΓ : ContDiff ℝ ((r + 1 : ℕ) : WithTop ℕ∞) Γ)
    {Bpos : ℝ} (hBpos : 0 ≤ Bpos)
    (hPos : ∀ j : ℕ, 1 ≤ j → j ≤ r + 1 → ∀ x,
      ‖iteratedFDeriv ℝ j Γ x‖ ≤ Bpos)
    (hη : IsBoundedLinearOnE r P η)
    (Bil : H →L[ℝ] H →L[ℝ] ℝ) :
    ENNReal.ofReal |η (s101Fm Γ Bil)| ≤
      dualNormE r P η *
        ENNReal.ofReal (s57pC d r P * (s101Cf d r Bpos * ‖Bil‖)) := by
  have h := s57p_dual_bound hP hη (s101_Fm_contDiff hΓ Bil)
    (fp81s21_s101_Fm_bound_pos hΓ hBpos hPos Bil)
  exact h.trans (mul_le_mul' le_rfl
    (fp81s21_s101_Fm_E_le_pos hP hΓ hBpos hPos Bil))

/-- Trace estimate for a bilinear form satisfying the original `s101_Dform_data`
formula. Its defining-form construction may use the old full derivative bound;
only this trace estimate uses the positive-order constant `Bpos`. -/
theorem fp81s21_s101_trace_bound_pos {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {Γ : Euc d → H} {r : ℕ} {P Bfull : ℝ}
    {η : (Euc d → ℝ) → ℝ}
    (hP : (d : ℝ) < 2 * P)
    (hΓ : ContDiff ℝ ((r + 1 : ℕ) : WithTop ℕ∞) Γ)
    (hFull : ∀ j ≤ r + 1, ∀ x,
      ‖iteratedFDeriv ℝ j Γ x‖ ≤ Bfull)
    (hη : IsBoundedLinearOnE r P η)
    {Bpos : ℝ} (hBpos : 0 ≤ Bpos)
    (hPos : ∀ j : ℕ, 1 ≤ j → j ≤ r + 1 → ∀ x,
      ‖iteratedFDeriv ℝ j Γ x‖ ≤ Bpos)
    (Dc : H →L[ℝ] H →L[ℝ] ℝ)
    (hDc : ∀ u v, Dc u v = η (s101Fm Γ (s101Rk u v))) :
    ENNReal.ofReal (HRS.traceNormForm Dc) ≤
      dualNormE r P η *
        ENNReal.ofReal (s57pC d r P * ((d : ℝ) * 2 ^ r * Bpos ^ 2)) := by
  set Λ := s101Lam hP hΓ hFull hη with hΛ
  have hsum : ∀ p : HRS.OrthonormalPairs H,
      ∃ Ω : H →L[ℝ] H →L[ℝ] ℝ, ‖Ω‖ ≤ 1 ∧
        ∑ i, |Dc (p.1.2.1 i) (p.1.2.2 i)| = η (s101Fm Γ Ω) := by
    intro p
    obtain ⟨he, hf⟩ := p.2
    set ε : Fin p.1.1 → ℝ :=
      fun i => if 0 ≤ Dc (p.1.2.1 i) (p.1.2.2 i) then 1 else -1 with hε
    refine ⟨∑ i, ε i • s101Rk (p.1.2.1 i) (p.1.2.2 i),
      norm_signed_Rk_le he hf ε (fun i => ?_), ?_⟩
    · simp only [hε]
      split_ifs <;> simp
    · have hηΛ : η (s101Fm Γ
          (∑ i, ε i • s101Rk (p.1.2.1 i) (p.1.2.2 i))) =
          Λ (∑ i, ε i • s101Rk (p.1.2.1 i) (p.1.2.2 i)) := rfl
      rw [hηΛ, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul]
      have hpair : Λ (s101Rk (p.1.2.1 i) (p.1.2.2 i)) =
          Dc (p.1.2.1 i) (p.1.2.2 i) := by
        rw [hΛ, s101Lam_apply, hDc]
      rw [hpair]
      simp only [hε]
      split_ifs with h
      · rw [abs_of_nonneg h]
        ring
      · rw [abs_of_neg (not_le.1 h)]
        ring
  set X := dualNormE r P η *
    ENNReal.ofReal (s57pC d r P * s101Cf d r Bpos) with hX
  change ENNReal.ofReal (HRS.traceNormForm Dc) ≤ X
  have hall : ∀ p : HRS.OrthonormalPairs H,
      ENNReal.ofReal (∑ i, |Dc (p.1.2.1 i) (p.1.2.2 i)|) ≤ X := by
    intro p
    obtain ⟨Ω, hΩ, he⟩ := hsum p
    rw [he]
    refine (ENNReal.ofReal_le_ofReal (le_abs_self _)).trans ?_
    refine (fp81s21_s101_eta_Fm_le_dual_pos hP hΓ hBpos hPos hη Ω).trans ?_
    refine mul_le_mul' le_rfl ?_
    apply ENNReal.ofReal_le_ofReal
    unfold s101Cf
    refine mul_le_mul_of_nonneg_left ?_ (s57pC_nonneg d r P)
    calc ((d : ℝ) * 2 ^ r * Bpos ^ 2) * ‖Ω‖
        ≤ ((d : ℝ) * 2 ^ r * Bpos ^ 2) * 1 :=
          mul_le_mul_of_nonneg_left hΩ (by positivity)
      _ = (d : ℝ) * 2 ^ r * Bpos ^ 2 := by simp
  by_cases hXtop : X = ⊤
  · rw [hXtop]
    exact le_top
  · have hXr : ∀ p : HRS.OrthonormalPairs H,
        ∑ i, |Dc (p.1.2.1 i) (p.1.2.2 i)| ≤ X.toReal := by
      intro p
      have h := ENNReal.toReal_mono hXtop (hall p)
      rwa [ENNReal.toReal_ofReal
        (Finset.sum_nonneg fun i _ => abs_nonneg _)] at h
    have htrace : HRS.traceNormForm Dc ≤ X.toReal :=
      Real.iSup_le hXr ENNReal.toReal_nonneg
    calc ENNReal.ofReal (HRS.traceNormForm Dc)
        ≤ ENNReal.ofReal X.toReal := ENNReal.ofReal_le_ofReal htrace
      _ = X := ENNReal.ofReal_toReal hXtop

/-- The original `s101_Dform_data` form and algebraic properties, with its
trace estimate sharpened to use only positive-order feature bounds. -/
theorem fp81s21_s101_Dform_data_pos {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {Γ : Euc d → H} {r : ℕ} {P Bfull : ℝ}
    {η : (Euc d → ℝ) → ℝ}
    (hP : (d : ℝ) < 2 * P)
    (hΓ : ContDiff ℝ ((r + 1 : ℕ) : WithTop ℕ∞) Γ)
    (hFull : ∀ j ≤ r + 1, ∀ x,
      ‖iteratedFDeriv ℝ j Γ x‖ ≤ Bfull)
    (hη : IsBoundedLinearOnE r P η)
    {Bpos : ℝ} (hBpos : 0 ≤ Bpos)
    (hPos : ∀ j : ℕ, 1 ≤ j → j ≤ r + 1 → ∀ x,
      ‖iteratedFDeriv ℝ j Γ x‖ ≤ Bpos) :
    ∃ Dc : H →L[ℝ] H →L[ℝ] ℝ,
      (∀ u v, Dc u v = η (s101Fm Γ (s101Rk u v))) ∧
      (∀ u v, Dc u v = Dc v u) ∧
      BddAbove (Set.range fun p : HRS.OrthonormalPairs H =>
        ∑ i, |Dc (p.1.2.1 i) (p.1.2.2 i)|) ∧
      ENNReal.ofReal (HRS.traceNormForm Dc) ≤
        dualNormE r P η *
          ENNReal.ofReal (s57pC d r P * ((d : ℝ) * 2 ^ r * Bpos ^ 2)) := by
  obtain ⟨Dc, hDc, hsym, hbdd, _htrace⟩ :=
    s101_Dform_data hP hΓ hFull hη
  exact ⟨Dc, hDc, hsym, hbdd,
    fp81s21_s101_trace_bound_pos hP hΓ hFull hη hBpos hPos Dc hDc⟩

#print axioms fp81s21_s101_Gk_bound_pos
#print axioms fp81s21_s101_Fm_bound_pos
#print axioms fp81s21_s101_Fm_E_le_pos
#print axioms fp81s21_s101_eta_Fm_le_dual_pos
#print axioms fp81s21_s101_trace_bound_pos
#print axioms fp81s21_s101_Dform_data_pos

end HRS.Fp81.S21

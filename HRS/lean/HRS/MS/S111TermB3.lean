import HRS.MS.CovMeasTie
import HRS.MS.S111TermAux2

/-!
# S11.1 continuation, B01: the signed trace form of a feature family

Generalizes `s101_Dform_data` (the feature family `∂_kΓ`) to an arbitrary family `G_i : ℝ^d → E`
with `C^r` bounds, via `F_Bil(x) = Σ_i Bil(G_i x, G_i x)`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K

open HRS HRS.Whole HRS.MS.FixEq HRS.MS.CovMeas

variable {d : ℕ}

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The weighted-test function `x ↦ Σ_i Bil(G_i x, G_i x)`. -/
def s111kFg (G : Fin d → Euc d → E) (Bil : E →L[ℝ] E →L[ℝ] ℝ) (x : Euc d) : ℝ :=
  ∑ i : Fin d, Bil (G i x) (G i x)

lemma s111k_Fg_contDiff {G : Fin d → Euc d → E} {r : ℕ} (hG : ∀ i, ContDiff ℝ (r : WithTop ℕ∞) (G i))
    (Bil : E →L[ℝ] E →L[ℝ] ℝ) : ContDiff ℝ (r : WithTop ℕ∞) (s111kFg G Bil) := by
  unfold s111kFg
  exact ContDiff.sum fun i _ => Bil.isBoundedBilinearMap.contDiff.comp ((hG i).prodMk (hG i))

lemma s111k_Fg_bound {G : Fin d → Euc d → E} {r : ℕ} (hG : ∀ i, ContDiff ℝ (r : WithTop ℕ∞) (G i))
    {A : ℝ} (hA : ∀ i, ∀ j ≤ r, ∀ x, ‖iteratedFDeriv ℝ j (G i) x‖ ≤ A) (Bil : E →L[ℝ] E →L[ℝ] ℝ) :
    ∀ j ≤ r, ∀ x, ‖iteratedFDeriv ℝ j (s111kFg G Bil) x‖ ≤ s101Cf d r A * ‖Bil‖ := by
  intro j hj x
  have hterm : ∀ i : Fin d, ‖iteratedFDeriv ℝ j (fun x => Bil (G i x) (G i x)) x‖ ≤
      ‖Bil‖ * (2 ^ r * A ^ 2) := by
    intro i
    have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA i 0 (Nat.zero_le _) x)
    have h1 := ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear Bil (hG i) (hG i) x
      (n := j) (by exact_mod_cast hj)
    refine h1.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (ContinuousLinearMap.opNorm_nonneg _)
    calc ∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) *
          ‖iteratedFDeriv ℝ k (G i) x‖ * ‖iteratedFDeriv ℝ (j - k) (G i) x‖
        ≤ ∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) * (A * A) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk' : k ≤ j := by simpa [Nat.lt_succ_iff] using hk
          have a1 := hA i k (hk'.trans hj) x
          have a2 := hA i (j - k) ((Nat.sub_le _ _).trans hj) x
          rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          exact mul_le_mul a1 a2 (norm_nonneg _) hA0
      _ = 2 ^ j * (A * A) := by
          rw [← Finset.sum_mul]
          congr 1
          exact_mod_cast Nat.sum_range_choose j
      _ ≤ 2 ^ r * A ^ 2 := by
          rw [← sq]
          exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) (sq_nonneg _)
  have hsum : iteratedFDeriv ℝ j (s111kFg G Bil) x =
      ∑ i : Fin d, iteratedFDeriv ℝ j (fun x => Bil (G i x) (G i x)) x := by
    unfold s111kFg
    refine iteratedFDeriv_fun_sum_apply fun i _ => ?_
    exact (Bil.isBoundedBilinearMap.contDiff.comp
      ((hG i).prodMk (hG i))).contDiffAt.of_le (by exact_mod_cast hj)
  rw [hsum]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i : Fin d, ‖iteratedFDeriv ℝ j (fun x => Bil (G i x) (G i x)) x‖
      ≤ ∑ _i : Fin d, ‖Bil‖ * (2 ^ r * A ^ 2) := Finset.sum_le_sum fun i _ => hterm i
    _ = s101Cf d r A * ‖Bil‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, s101Cf]
        ring

lemma s111k_Fg_add (G : Fin d → Euc d → E) (Bil₁ Bil₂ : E →L[ℝ] E →L[ℝ] ℝ) :
    s111kFg G (Bil₁ + Bil₂) = s111kFg G Bil₁ + s111kFg G Bil₂ := by
  funext x
  simp [s111kFg, Finset.sum_add_distrib]

lemma s111k_Fg_smul (G : Fin d → Euc d → E) (a : ℝ) (Bil : E →L[ℝ] E →L[ℝ] ℝ) :
    s111kFg G (a • Bil) = a • s111kFg G Bil := by
  funext x
  simp [s111kFg, Finset.mul_sum]

lemma s111k_Fg_Rk_symm (G : Fin d → Euc d → E) (u v : E) :
    s111kFg G (s101Rk u v) = s111kFg G (s101Rk v u) := by
  funext x
  simp only [s111kFg, s101Rk_apply]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

variable {G : Fin d → Euc d → E} {r : ℕ} {P A : ℝ} {η : (Euc d → ℝ) → ℝ}

lemma s111k_Fg_E_le (hP : (d : ℝ) < 2 * P) (hG : ∀ i, ContDiff ℝ (r : WithTop ℕ∞) (G i))
    (hA : ∀ i, ∀ j ≤ r, ∀ x, ‖iteratedFDeriv ℝ j (G i) x‖ ≤ A) (hA0 : 0 ≤ A) (Bil : E →L[ℝ] E →L[ℝ] ℝ) :
    weightedSobolevE r P (s111kFg G Bil) ≤ ENNReal.ofReal (s57pC d r P * (s101Cf d r A * ‖Bil‖)) := by
  have h0 : 0 ≤ s101Cf d r A * ‖Bil‖ := mul_nonneg (s101Cf_nonneg hA0 r) (ContinuousLinearMap.opNorm_nonneg _)
  exact s57p_E_le_cb hP h0 (s111k_Fg_bound hG hA Bil)

lemma s111k_Fg_test (hP : (d : ℝ) < 2 * P) (hG : ∀ i, ContDiff ℝ (r : WithTop ℕ∞) (G i))
    (hA : ∀ i, ∀ j ≤ r, ∀ x, ‖iteratedFDeriv ℝ j (G i) x‖ ≤ A) (hA0 : 0 ≤ A) (Bil : E →L[ℝ] E →L[ℝ] ℝ) :
    ContDiff ℝ (r : WithTop ℕ∞) (s111kFg G Bil) ∧ weightedSobolevE r P (s111kFg G Bil) < ⊤ :=
  ⟨s111k_Fg_contDiff hG Bil, lt_of_le_of_lt (s111k_Fg_E_le hP hG hA hA0 Bil) ENNReal.ofReal_lt_top⟩

/-- `Bil ↦ η(F_Bil)` as a linear map on bilinear forms. -/
def s111kLam (hP : (d : ℝ) < 2 * P) (hG : ∀ i, ContDiff ℝ (r : WithTop ℕ∞) (G i))
    (hA : ∀ i, ∀ j ≤ r, ∀ x, ‖iteratedFDeriv ℝ j (G i) x‖ ≤ A) (hA0 : 0 ≤ A)
    (hη : IsBoundedLinearOnE r P η) : (E →L[ℝ] E →L[ℝ] ℝ) →ₗ[ℝ] ℝ where
  toFun Bil := η (s111kFg G Bil)
  map_add' Bil₁ Bil₂ := by
    obtain ⟨h1, h1'⟩ := s111k_Fg_test hP hG hA hA0 Bil₁
    obtain ⟨h2, h2'⟩ := s111k_Fg_test hP hG hA hA0 Bil₂
    rw [s111k_Fg_add]
    exact (hη.1 _ _ h1 h1' h2 h2' 1).1
  map_smul' a Bil := by
    obtain ⟨h1, h1'⟩ := s111k_Fg_test hP hG hA hA0 Bil
    rw [s111k_Fg_smul]
    have := (hη.1 _ _ h1 h1' h1 h1' a).2
    simpa using this

lemma s111k_eta_Fg_le_dual (hP : (d : ℝ) < 2 * P) (hG : ∀ i, ContDiff ℝ (r : WithTop ℕ∞) (G i))
    (hA : ∀ i, ∀ j ≤ r, ∀ x, ‖iteratedFDeriv ℝ j (G i) x‖ ≤ A) (hA0 : 0 ≤ A)
    (hη : IsBoundedLinearOnE r P η) (Bil : E →L[ℝ] E →L[ℝ] ℝ) :
    ENNReal.ofReal |η (s111kFg G Bil)| ≤
      dualNormE r P η * ENNReal.ofReal (s57pC d r P * (s101Cf d r A * ‖Bil‖)) := by
  have h := s57p_dual_bound hP hη (s111k_Fg_contDiff hG Bil) (s111k_Fg_bound hG hA Bil)
  exact h.trans (mul_le_mul' le_rfl (s111k_Fg_E_le hP hG hA hA0 Bil))

lemma s111k_eta_Fg_le_M (hP : (d : ℝ) < 2 * P) (hG : ∀ i, ContDiff ℝ (r : WithTop ℕ∞) (G i))
    (hA : ∀ i, ∀ j ≤ r, ∀ x, ‖iteratedFDeriv ℝ j (G i) x‖ ≤ A) (hA0 : 0 ≤ A)
    (hη : IsBoundedLinearOnE r P η) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ Bil : E →L[ℝ] E →L[ℝ] ℝ,
      |η (s111kFg G Bil)| ≤ M * (s57pC d r P * (s101Cf d r A * ‖Bil‖)) := by
  obtain ⟨M, hM⟩ := hη.2
  refine ⟨|M|, abs_nonneg _, fun Bil => ?_⟩
  obtain ⟨h1, h1'⟩ := s111k_Fg_test hP hG hA hA0 Bil
  have h2 := hM _ h1 h1'
  have h3 : (weightedSobolevE r P (s111kFg G Bil)).toReal ≤ s57pC d r P * (s101Cf d r A * ‖Bil‖) := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (s111k_Fg_E_le hP hG hA hA0 Bil)
    rwa [ENNReal.toReal_ofReal (mul_nonneg (s57pC_nonneg d r P)
      (mul_nonneg (s101Cf_nonneg hA0 r) (ContinuousLinearMap.opNorm_nonneg _)))] at this
  calc |η (s111kFg G Bil)| ≤ M * (weightedSobolevE r P (s111kFg G Bil)).toReal := h2
    _ ≤ |M| * (weightedSobolevE r P (s111kFg G Bil)).toReal :=
        mul_le_mul_of_nonneg_right (le_abs_self _) ENNReal.toReal_nonneg
    _ ≤ |M| * (s57pC d r P * (s101Cf d r A * ‖Bil‖)) :=
        mul_le_mul_of_nonneg_left h3 (abs_nonneg _)

open Classical in
theorem s111k_Dform_data (hP : (d : ℝ) < 2 * P) (hG : ∀ i, ContDiff ℝ (r : WithTop ℕ∞) (G i))
    (hA : ∀ i, ∀ j ≤ r, ∀ x, ‖iteratedFDeriv ℝ j (G i) x‖ ≤ A) (hA0 : 0 ≤ A)
    (hη : IsBoundedLinearOnE r P η) :
    ∃ Dc : E →L[ℝ] E →L[ℝ] ℝ, (∀ u v, Dc u v = η (s111kFg G (s101Rk u v))) ∧
      (∀ u v, Dc u v = Dc v u) ∧
      (BddAbove (Set.range fun p : HRS.OrthonormalPairs E => ∑ i, |Dc (p.1.2.1 i) (p.1.2.2 i)|)) ∧
      ENNReal.ofReal (HRS.traceNormForm Dc) ≤
        dualNormE r P η * ENNReal.ofReal (s57pC d r P * s101Cf d r A) := by
  obtain ⟨M, hM0, hM⟩ := s111k_eta_Fg_le_M hP hG hA hA0 hη
  set Λ := s111kLam hP hG hA hA0 hη with hΛ
  set Cst : ℝ := M * (s57pC d r P * s101Cf d r A) with hCst
  have hCst0 : 0 ≤ Cst := mul_nonneg hM0 (mul_nonneg (s57pC_nonneg d r P) (s101Cf_nonneg hA0 r))
  let f : E →ₗ[ℝ] E →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ (fun u v => Λ (s101Rk u v))
    (fun u u' v => by rw [s101Rk_add_left, map_add])
    (fun c u v => by rw [s101Rk_smul_left, map_smul])
    (fun u v v' => by rw [s101Rk_add_right, map_add])
    (fun c u v => by rw [s101Rk_smul_right, map_smul])
  have hbd : ∀ u v, ‖f u v‖ ≤ Cst * ‖u‖ * ‖v‖ := by
    intro u v
    show ‖Λ (s101Rk u v)‖ ≤ _
    rw [Real.norm_eq_abs, hΛ]
    refine (hM _).trans ?_
    have := norm_s101Rk_le u v
    calc M * (s57pC d r P * (s101Cf d r A * ‖s101Rk u v‖))
        ≤ M * (s57pC d r P * (s101Cf d r A * (‖u‖ * ‖v‖))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left this (s101Cf_nonneg hA0 r)) (s57pC_nonneg d r P)) hM0
      _ = Cst * ‖u‖ * ‖v‖ := by rw [hCst]; ring
  set Dc : E →L[ℝ] E →L[ℝ] ℝ := f.mkContinuous₂ Cst hbd with hDc
  have hDcapp : ∀ u v, Dc u v = η (s111kFg G (s101Rk u v)) := fun u v => rfl
  have hsymm : ∀ u v, Dc u v = Dc v u := fun u v => by
    rw [hDcapp, hDcapp, s111k_Fg_Rk_symm]
  have hsum : ∀ p : HRS.OrthonormalPairs E, ∃ Ω : E →L[ℝ] E →L[ℝ] ℝ, ‖Ω‖ ≤ 1 ∧
      ∑ i, |Dc (p.1.2.1 i) (p.1.2.2 i)| = η (s111kFg G Ω) := by
    intro p
    obtain ⟨he, hf⟩ := p.2
    set ε : Fin p.1.1 → ℝ := fun i => if 0 ≤ Dc (p.1.2.1 i) (p.1.2.2 i) then 1 else -1 with hε
    refine ⟨∑ i, ε i • s101Rk (p.1.2.1 i) (p.1.2.2 i), norm_signed_Rk_le he hf ε fun i => ?_, ?_⟩
    · simp only [hε]; split_ifs <;> simp
    · have : η (s111kFg G (∑ i, ε i • s101Rk (p.1.2.1 i) (p.1.2.2 i))) =
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
    calc s101Cf d r A * ‖Ω‖ ≤ s101Cf d r A * 1 := mul_le_mul_of_nonneg_left hΩ (s101Cf_nonneg hA0 r)
      _ = s101Cf d r A := mul_one _
  · set X := dualNormE r P η * ENNReal.ofReal (s57pC d r P * s101Cf d r A) with hX
    have hall : ∀ p : HRS.OrthonormalPairs E,
        ENNReal.ofReal (∑ i, |Dc (p.1.2.1 i) (p.1.2.2 i)|) ≤ X := by
      intro p
      obtain ⟨Ω, hΩ, he⟩ := hsum p
      rw [he]
      refine (ENNReal.ofReal_le_ofReal (le_abs_self _)).trans ?_
      refine (s111k_eta_Fg_le_dual hP hG hA hA0 hη Ω).trans (mul_le_mul' le_rfl ?_)
      refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (s57pC_nonneg d r P))
      calc s101Cf d r A * ‖Ω‖ ≤ s101Cf d r A * 1 := mul_le_mul_of_nonneg_left hΩ (s101Cf_nonneg hA0 r)
        _ = s101Cf d r A := mul_one _
    by_cases hXtop : X = ⊤
    · rw [hXtop]; exact le_top
    · have hXr : ∀ p : HRS.OrthonormalPairs E, ∑ i, |Dc (p.1.2.1 i) (p.1.2.2 i)| ≤ X.toReal := by
        intro p
        have := ENNReal.toReal_mono hXtop (hall p)
        rwa [ENNReal.toReal_ofReal (Finset.sum_nonneg fun i _ => abs_nonneg _)] at this
      have : HRS.traceNormForm Dc ≤ X.toReal := Real.iSup_le hXr ENNReal.toReal_nonneg
      calc ENNReal.ofReal (HRS.traceNormForm Dc) ≤ ENNReal.ofReal X.toReal :=
            ENNReal.ofReal_le_ofReal this
        _ = X := ENNReal.ofReal_toReal hXtop

end Abstract

/-- The native continuity premise used by S10.1, at one forcing time (Pro `WeightedFunctional`). -/
def S111kWeightedFunctional {d : ℕ} (r : ℕ) (Pw : ℝ) (z : (Euc d → ℝ) → ℝ) : Prop :=
  (∀ f g, IsR2WeightedTest r Pw f → IsR2WeightedTest r Pw g →
    z (f + g) = z f + z g) ∧
  (∀ (a : ℝ) f, IsR2WeightedTest r Pw f → z (a • f) = a * z f) ∧
  ∃ M : ℝ, ∀ f, IsR2WeightedTest r Pw f →
    |z f| ≤ M * (weightedSobolevE r Pw f).toReal

theorem s111k_weighted_isBounded {d r : ℕ} {Pw : ℝ} {z : (Euc d → ℝ) → ℝ}
    (hz : S111kWeightedFunctional r Pw z) : IsBoundedLinearOnE r Pw z := by
  obtain ⟨h1, h2, M, hM⟩ := hz
  refine ⟨fun f g hf hf' hg hg' c => ⟨h1 f g ⟨hf, hf'⟩ ⟨hg, hg'⟩, h2 c f ⟨hf, hf'⟩⟩, M, ?_⟩
  intro f hf hf'
  exact hM f ⟨hf, hf'⟩

/-- **B01 (quantitative signed trace form).** -/
theorem s111k_signed_feature_trace
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (d r : ℕ) (hd : 1 ≤ d) (Pw : ℝ) (hPw : (d : ℝ) / 2 < Pw) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ A : ℝ, 0 ≤ A →
      ∀ G : Fin d → Euc d → E,
      (∀ i, ContDiff ℝ r (G i)) →
      (∀ i j, j ≤ r → ∀ x, ‖iteratedFDeriv ℝ j (G i) x‖ ≤ A) →
      ∀ z : (Euc d → ℝ) → ℝ, S111kWeightedFunctional r Pw z →
      dualNormE r Pw z < ⊤ →
      ∃ D : E →L[ℝ] E →L[ℝ] ℝ,
        (∀ v w, D v w = z (fun x => ∑ i : Fin d,
          inner ℝ (G i x) v * inner ℝ (G i x) w)) ∧
        (∀ v w, D v w = D w v) ∧
        BddAbove (Set.range fun p : HRS.OrthonormalPairs E =>
          ∑ i, |D (p.1.2.1 i) (p.1.2.2 i)|) ∧
        HRS.traceNormForm D ≤ K * A ^ 2 * (dualNormE r Pw z).toReal := by
  have hP : (d : ℝ) < 2 * Pw := by linarith
  refine ⟨s57pC d r Pw * ((d : ℝ) * 2 ^ r), mul_nonneg (s57pC_nonneg d r Pw) (by positivity), ?_⟩
  intro A hA0 G hG hA z hz hdual
  have hη := s111k_weighted_isBounded hz
  obtain ⟨Dc, h1, h2, h3, h4⟩ := s111k_Dform_data hP hG hA hA0 hη
  refine ⟨Dc, fun v w => ?_, h2, h3, ?_⟩
  · rw [h1]
    congr 1
    funext x
    simp only [s111kFg, s101Rk_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_comm v, real_inner_comm w]
  · have hX : dualNormE r Pw z * ENNReal.ofReal (s57pC d r Pw * s101Cf d r A) ≠ ⊤ :=
      ENNReal.mul_ne_top hdual.ne ENNReal.ofReal_ne_top
    have := (ENNReal.ofReal_le_iff_le_toReal hX).1 h4
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg (s57pC_nonneg d r Pw)
      (s101Cf_nonneg hA0 r))] at this
    refine this.trans (le_of_eq ?_)
    simp only [s101Cf]
    ring

end HRS.MS.S111K

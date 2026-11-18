import HRS.MS.Fp81S21JointP2

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace HRS.Fp81.S21

open HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

local instance fp81s21_jointC_U_measSpace (H : ℝ) :
    MeasurableSpace (fp81s21_jointP_U H) := borel _
local instance fp81s21_jointC_U_borelSpace (H : ℝ) :
    BorelSpace (fp81s21_jointP_U H) := ⟨rfl⟩
local instance fp81s21_jointC_pair_measSpace (H : ℝ) :
    MeasurableSpace (fp81s21_jointP_U H × fp81s21_jointP_U H) := borel _
local instance fp81s21_jointC_pair_borelSpace (H : ℝ) :
    BorelSpace (fp81s21_jointP_U H × fp81s21_jointP_U H) := ⟨rfl⟩

/-- The quadratic-only projection used to center the joint linear/quadratic
output. Its action is exactly `(u,b) ↦ (0,b)`. -/
noncomputable def fp81s21_jointC_partialCenter (H : ℝ) :
    (fp81s21_jointP_U H × fp81s21_jointP_U H) →L[ℝ]
      (fp81s21_jointP_U H × fp81s21_jointP_U H) :=
  ContinuousLinearMap.prod
    (0 : (fp81s21_jointP_U H × fp81s21_jointP_U H) →L[ℝ] fp81s21_jointP_U H)
    (ContinuousLinearMap.snd ℝ (fp81s21_jointP_U H) (fp81s21_jointP_U H))

theorem fp81s21_jointC_partialCenter_apply (H : ℝ)
    (z : fp81s21_jointP_U H × fp81s21_jointP_U H) :
    fp81s21_jointC_partialCenter H z = (0, z.2) := by
  simp [fp81s21_jointC_partialCenter, ContinuousLinearMap.prod_apply]

theorem fp81s21_jointC_partialCenter_norm_le_one (H : ℝ) :
    ‖fp81s21_jointC_partialCenter H‖ ≤ 1 := by
  exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => by
    rw [fp81s21_jointC_partialCenter_apply]
    simpa using (norm_snd_le z)

private def fp81s21_jointC_quadKsum {p : Parameters} (m : ℕ)
    (D : Fin m → fp81s21_RankKernel p.d) : ℝ :=
  ∑ j : Fin m, fp81s21_quadK (D j).c (D j).u

private theorem fp81s21_jointC_quadKsum_nonneg {p : Parameters} (m : ℕ)
    (D : Fin m → fp81s21_RankKernel p.d) :
    0 ≤ fp81s21_jointC_quadKsum m D := by
  unfold fp81s21_jointC_quadKsum
  exact Finset.sum_nonneg fun j _ => fp81s21_quadK_nonneg _ _

private def fp81s21_jointC_quadTerm {p : Parameters} {m : ℕ} (H : ℝ)
    (D : Fin m → fp81s21_RankKernel p.d) (j : Fin m)
    (x : fp81s21_jointP_X p H) : fp81s21_jointP_CH H :=
  ⟨fun t => fp81s21_quadPoly (D j).c (D j).u x t • fp81s21_coeffBasis j,
    (fp81s21_jointP_quadTime_continuous H (D j) x).smul continuous_const⟩

private theorem fp81s21_jointC_quadTerm_growth {p : Parameters} {m : ℕ} (H : ℝ)
    (D : Fin m → fp81s21_RankKernel p.d) (j : Fin m)
    (x : fp81s21_jointP_X p H) :
    ‖fp81s21_jointC_quadTerm H D j x‖ ≤
      fp81s21_quadK (D j).c (D j).u * ‖x‖ ^ 2 := by
  have hbasis : ‖fp81s21_coeffBasis j‖ = 1 :=
    fp81s21_coeffBasis.orthonormal.norm_eq_one j
  apply (ContinuousMap.norm_le _
    (mul_nonneg (fp81s21_quadK_nonneg _ _) (sq_nonneg _))).2
  intro t
  change ‖fp81s21_quadPoly (D j).c (D j).u x t • fp81s21_coeffBasis j‖ ≤ _
  simp only [norm_smul, Real.norm_eq_abs, hbasis, mul_one]
  exact fp81s21_quadPoly_bound (D j).valid x t

private theorem fp81s21_jointC_quadTerm_lip {p : Parameters} {m : ℕ} (H : ℝ)
    (D : Fin m → fp81s21_RankKernel p.d) (j : Fin m)
    (x y : fp81s21_jointP_X p H) :
    ‖fp81s21_jointC_quadTerm H D j x - fp81s21_jointC_quadTerm H D j y‖ ≤
      fp81s21_quadK (D j).c (D j).u * (‖x‖ + ‖y‖) * ‖x - y‖ := by
  have hbasis : ‖fp81s21_coeffBasis j‖ = 1 :=
    fp81s21_coeffBasis.orthonormal.norm_eq_one j
  have hsup := fp81s21_quadPoly_sup_lip (D j).valid x y
  have hbounded : BddAbove (Set.range (fun s : Icc (0 : ℝ) H =>
      |fp81s21_quadPoly (D j).c (D j).u x s -
        fp81s21_quadPoly (D j).c (D j).u y s|)) := by
    refine ⟨fp81s21_quadK (D j).c (D j).u * (‖x‖ + ‖y‖) * ‖x - y‖, ?_⟩
    rintro z ⟨s, rfl⟩
    exact fp81s21_quadPoly_lip (D j).valid x y s
  apply (ContinuousMap.norm_le _
    (mul_nonneg (mul_nonneg (fp81s21_quadK_nonneg _ _)
      (add_nonneg (norm_nonneg _) (norm_nonneg _))) (norm_nonneg _))).2
  intro t
  change ‖(fp81s21_quadPoly (D j).c (D j).u x t • fp81s21_coeffBasis j) -
    (fp81s21_quadPoly (D j).c (D j).u y t • fp81s21_coeffBasis j)‖ ≤ _
  rw [← sub_smul]
  simp only [norm_smul, Real.norm_eq_abs, hbasis, mul_one]
  exact (le_ciSup hbounded t).trans hsup

private theorem fp81s21_jointC_quadCurve_growth {p : Parameters} (H : ℝ) (m : ℕ)
    (D : Fin m → fp81s21_RankKernel p.d) (x : fp81s21_jointP_X p H) :
    ‖fp81s21_jointP_quadCurve H m D x‖ ≤
      fp81s21_jointC_quadKsum m D * ‖x‖ ^ 2 := by
  change ‖∑ j : Fin m, fp81s21_jointC_quadTerm H D j x‖ ≤ _
  calc
    ‖∑ j : Fin m, fp81s21_jointC_quadTerm H D j x‖ ≤
        ∑ j : Fin m, ‖fp81s21_jointC_quadTerm H D j x‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin m, fp81s21_quadK (D j).c (D j).u * ‖x‖ ^ 2 :=
      Finset.sum_le_sum fun j _ => fp81s21_jointC_quadTerm_growth H D j x
    _ = fp81s21_jointC_quadKsum m D * ‖x‖ ^ 2 := by
      rw [← Finset.sum_mul]
      rfl

private theorem fp81s21_jointC_quadCurve_lip {p : Parameters} (H : ℝ) (m : ℕ)
    (D : Fin m → fp81s21_RankKernel p.d) (x y : fp81s21_jointP_X p H) :
    ‖fp81s21_jointP_quadCurve H m D x - fp81s21_jointP_quadCurve H m D y‖ ≤
      fp81s21_jointC_quadKsum m D * (‖x‖ + ‖y‖) * ‖x - y‖ := by
  change ‖(∑ j : Fin m, fp81s21_jointC_quadTerm H D j x) -
    (∑ j : Fin m, fp81s21_jointC_quadTerm H D j y)‖ ≤ _
  calc
    ‖(∑ j : Fin m, fp81s21_jointC_quadTerm H D j x) -
        (∑ j : Fin m, fp81s21_jointC_quadTerm H D j y)‖ =
        ‖∑ j : Fin m,
          (fp81s21_jointC_quadTerm H D j x - fp81s21_jointC_quadTerm H D j y)‖ := by
            rw [Finset.sum_sub_distrib]
    _ ≤ ∑ j : Fin m,
        ‖fp81s21_jointC_quadTerm H D j x - fp81s21_jointC_quadTerm H D j y‖ :=
          norm_sum_le _ _
    _ ≤ ∑ j : Fin m,
        fp81s21_quadK (D j).c (D j).u * (‖x‖ + ‖y‖) * ‖x - y‖ :=
          Finset.sum_le_sum fun j _ => fp81s21_jointC_quadTerm_lip H D j x y
    _ = fp81s21_jointC_quadKsum m D * (‖x‖ + ‖y‖) * ‖x - y‖ := by
          unfold fp81s21_jointC_quadKsum
          calc
            ∑ j : Fin m,
                fp81s21_quadK (D j).c (D j).u * (‖x‖ + ‖y‖) * ‖x - y‖ =
                ∑ j : Fin m,
                  fp81s21_quadK (D j).c (D j).u * ((‖x‖ + ‖y‖) * ‖x - y‖) := by
                    apply Finset.sum_congr rfl
                    intro j hj
                    ring
            _ = (∑ j : Fin m, fp81s21_quadK (D j).c (D j).u) *
                ((‖x‖ + ‖y‖) * ‖x - y‖) := by rw [Finset.sum_mul]
            _ = (∑ j : Fin m, fp81s21_quadK (D j).c (D j).u) *
                (‖x‖ + ‖y‖) * ‖x - y‖ := by ring

private theorem fp81s21_jointC_projected_curve_bound (H : ℝ) (hH : 0 < H)
    (m : ℕ) (v : fp81s21_jointP_CH H) :
    ‖fp81s21_timeProject H m (fp81s21_smoothPathToL2 H hH v)‖ ≤
      ‖fp81s21_smoothPathToL2 H hH‖ * ‖v‖ := by
  calc
    ‖fp81s21_timeProject H m (fp81s21_smoothPathToL2 H hH v)‖ ≤
        ‖fp81s21_timeProject H m‖ *
          ‖fp81s21_smoothPathToL2 H hH v‖ :=
      (fp81s21_timeProject H m).le_opNorm _
    _ ≤ 1 * (‖fp81s21_smoothPathToL2 H hH‖ * ‖v‖) := by
      exact mul_le_mul (fp81s21_timeProject_norm_le H m)
        ((fp81s21_smoothPathToL2 H hH).le_opNorm v) (norm_nonneg _) (by positivity)
    _ = ‖fp81s21_smoothPathToL2 H hH‖ * ‖v‖ := by simp

private theorem fp81s21_jointC_continuous_of_lip
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (K : ℝ) (hK : 0 ≤ K) (f : X → Y)
    (hlip : ∀ x y, ‖f x - f y‖ ≤ K * (1 + ‖x‖ + ‖y‖) * ‖x - y‖) :
    Continuous f := by
  rw [Metric.continuous_iff]
  intro x ε hε
  let A : ℝ := K * (2 * ‖x‖ + 2)
  let δ : ℝ := min 1 (ε / (2 * (A + 1)))
  refine ⟨δ, ?_, ?_⟩
  · dsimp [δ]
    positivity
  · intro y hxy
    have hd : ‖y - x‖ < δ := by simpa [dist_eq_norm] using hxy
    have hdx : ‖y - x‖ < 1 := lt_of_lt_of_le hd (min_le_left _ _)
    have hnormy : ‖y‖ ≤ ‖x‖ + 1 := by
      calc ‖y‖ = ‖x + (y - x)‖ := by congr 1 <;> abel
        _ ≤ ‖x‖ + ‖y - x‖ := norm_add_le _ _
        _ ≤ ‖x‖ + 1 := by linarith
    have hfactor : 1 + ‖x‖ + ‖y‖ ≤ 2 * ‖x‖ + 2 := by
      have hx : 0 ≤ ‖x‖ := norm_nonneg _
      linarith
    have hA : 0 ≤ A := by dsimp [A]; positivity
    have hcoef : K * (1 + ‖x‖ + ‖y‖) ≤ A := by
      dsimp [A]
      exact mul_le_mul_of_nonneg_left hfactor hK
    have hsmall : A * (ε / (2 * (A + 1))) ≤ ε / 2 := by
      have hden : 0 < 2 * (A + 1) := by positivity
      calc
        A * (ε / (2 * (A + 1))) ≤
            (A + 1) * (ε / (2 * (A + 1))) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = ε / 2 := by field_simp [ne_of_gt hden]
    have hdistout : ‖f y - f x‖ < ε := by
      calc
        ‖f y - f x‖ ≤ K * (1 + ‖x‖ + ‖y‖) * ‖y - x‖ := by
          simpa [norm_sub_rev] using hlip x y
        _ ≤ A * ‖y - x‖ :=
          mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
        _ ≤ A * δ := mul_le_mul_of_nonneg_left hd.le hA
        _ ≤ A * (ε / (2 * (A + 1))) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hA
        _ ≤ ε / 2 := hsmall
        _ < ε := by linarith
    simpa [dist_eq_norm] using hdistout

/-- Map-specific form of the packet 31-P local estimate. This statement fixes
the map to `fp81s21_jointP_map`, so later law-specific errors cannot silently
use a different existential witness. -/
theorem fp81s21_jointC_map_local_estimate {p : Parameters} (H : ℝ) (hH : 0 < H)
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (m : ℕ) (D : Fin m → fp81s21_RankKernel p.d) :
    ∃ K : ℝ, 0 ≤ K ∧
      Measurable (fp81s21_jointP_map H hH E m D) ∧
      (∀ x, ‖fp81s21_jointP_map H hH E m D x‖ ≤ K * (1 + ‖x‖ ^ 2)) ∧
      ∀ x y, ‖fp81s21_jointP_map H hH E m D x -
        fp81s21_jointP_map H hH E m D y‖ ≤
          K * (1 + ‖x‖ + ‖y‖) * ‖x - y‖ := by
  let Fmk : fp81s21_jointP_X p H → fp81s21_jointP_U H × fp81s21_jointP_U H :=
    fp81s21_jointP_map H hH E m D
  let L : fp81s21_jointP_X p H →L[ℝ] fp81s21_jointP_CH H :=
    fp81s21_jointP_linearCurveCLM p H E m
  let S : fp81s21_jointP_CH H →L[ℝ] fp81s21_jointP_U H :=
    fp81s21_smoothPathToL2 H hH
  let P : fp81s21_jointP_U H →L[ℝ] fp81s21_jointP_U H :=
    fp81s21_timeProject H m
  let Cq : ℝ := fp81s21_jointC_quadKsum m D
  let cL : ℝ := ‖S‖ * ‖L‖
  let cQ : ℝ := ‖S‖ * Cq
  let K : ℝ := max cL cQ
  have hCq : 0 ≤ Cq := fp81s21_jointC_quadKsum_nonneg m D
  have hcL : 0 ≤ cL := by dsimp [cL]; positivity
  have hcQ : 0 ≤ cQ := by dsimp [cQ]; positivity
  have hK : 0 ≤ K := le_trans hcL (le_max_left _ _)
  have hlin_growth (x : fp81s21_jointP_X p H) :
      ‖P (S (L x))‖ ≤ cL * ‖x‖ := by
    calc
      ‖P (S (L x))‖ ≤ ‖S‖ * ‖L x‖ := by
        simpa [P, S] using fp81s21_jointC_projected_curve_bound H hH m (L x)
      _ ≤ cL * ‖x‖ := by
        simpa [cL, mul_assoc] using
          (mul_le_mul_of_nonneg_left (L.le_opNorm x) (norm_nonneg S))
  have hlin_diff (x y : fp81s21_jointP_X p H) :
      ‖P (S (L x)) - P (S (L y))‖ ≤ cL * ‖x - y‖ := by
    have hmap : P (S (L x)) - P (S (L y)) = P (S (L (x - y))) := by
      dsimp [P, S, L]
      rw [← map_sub, ← map_sub, ← map_sub]
    rw [hmap]
    calc
      ‖P (S (L (x - y)))‖ ≤ ‖S‖ * ‖L (x - y)‖ := by
        simpa [P, S] using fp81s21_jointC_projected_curve_bound H hH m (L (x - y))
      _ ≤ cL * ‖x - y‖ := by
        simpa [cL, mul_assoc] using
          (mul_le_mul_of_nonneg_left (L.le_opNorm (x - y)) (norm_nonneg S))
  have hquad_growth (x : fp81s21_jointP_X p H) :
      ‖P (S (fp81s21_jointP_quadCurve H m D x))‖ ≤ cQ * ‖x‖ ^ 2 := by
    calc
      ‖P (S (fp81s21_jointP_quadCurve H m D x))‖ ≤
          ‖S‖ * ‖fp81s21_jointP_quadCurve H m D x‖ := by
        simpa [P, S] using
          fp81s21_jointC_projected_curve_bound H hH m
            (fp81s21_jointP_quadCurve H m D x)
      _ ≤ cQ * ‖x‖ ^ 2 := by
        calc
          ‖S‖ * ‖fp81s21_jointP_quadCurve H m D x‖ ≤
              ‖S‖ * (Cq * ‖x‖ ^ 2) :=
            mul_le_mul_of_nonneg_left
              (fp81s21_jointC_quadCurve_growth H m D x) (norm_nonneg S)
          _ = cQ * ‖x‖ ^ 2 := by dsimp [cQ]; ring
  have hquad_diff (x y : fp81s21_jointP_X p H) :
      ‖P (S (fp81s21_jointP_quadCurve H m D x)) -
        P (S (fp81s21_jointP_quadCurve H m D y))‖ ≤
          cQ * (‖x‖ + ‖y‖) * ‖x - y‖ := by
    have hmap : P (S (fp81s21_jointP_quadCurve H m D x)) -
        P (S (fp81s21_jointP_quadCurve H m D y)) =
        P (S (fp81s21_jointP_quadCurve H m D x -
          fp81s21_jointP_quadCurve H m D y)) := by
      dsimp [P, S]
      rw [← map_sub, ← map_sub]
    rw [hmap]
    calc
      ‖P (S (fp81s21_jointP_quadCurve H m D x -
          fp81s21_jointP_quadCurve H m D y))‖ ≤
          ‖S‖ * ‖fp81s21_jointP_quadCurve H m D x -
            fp81s21_jointP_quadCurve H m D y‖ := by
        simpa [P, S] using
          fp81s21_jointC_projected_curve_bound H hH m
            (fp81s21_jointP_quadCurve H m D x -
              fp81s21_jointP_quadCurve H m D y)
      _ ≤ cQ * (‖x‖ + ‖y‖) * ‖x - y‖ := by
        calc
          ‖S‖ * ‖fp81s21_jointP_quadCurve H m D x -
              fp81s21_jointP_quadCurve H m D y‖ ≤
              ‖S‖ * (Cq * (‖x‖ + ‖y‖) * ‖x - y‖) :=
            mul_le_mul_of_nonneg_left
              (fp81s21_jointC_quadCurve_lip H m D x y) (norm_nonneg S)
          _ = cQ * (‖x‖ + ‖y‖) * ‖x - y‖ := by dsimp [cQ]; ring
  have hgrowth (x : fp81s21_jointP_X p H) :
      ‖Fmk x‖ ≤ K * (1 + ‖x‖ ^ 2) := by
    have h1 : ‖P (S (L x))‖ ≤ K * (1 + ‖x‖ ^ 2) := by
      have hK' : cL ≤ K := le_max_left _ _
      have hx : ‖x‖ ≤ 1 + ‖x‖ ^ 2 := by nlinarith [sq_nonneg (‖x‖ - 1 / 2)]
      calc
        ‖P (S (L x))‖ ≤ cL * ‖x‖ := hlin_growth x
        _ ≤ K * (1 + ‖x‖ ^ 2) := by
          exact mul_le_mul hK' hx (norm_nonneg _) (by positivity)
    have h2 : ‖P (S (fp81s21_jointP_quadCurve H m D x))‖ ≤
        K * (1 + ‖x‖ ^ 2) := by
      have hK' : cQ ≤ K := le_max_right _ _
      calc
        ‖P (S (fp81s21_jointP_quadCurve H m D x))‖ ≤ cQ * ‖x‖ ^ 2 := hquad_growth x
        _ ≤ K * (1 + ‖x‖ ^ 2) := by
          have hsq : 0 ≤ ‖x‖ ^ 2 := sq_nonneg _
          calc
            cQ * ‖x‖ ^ 2 ≤ K * ‖x‖ ^ 2 :=
              mul_le_mul_of_nonneg_right hK' hsq
            _ ≤ K * (1 + ‖x‖ ^ 2) :=
              mul_le_mul_of_nonneg_left
                (le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)) hK
    change max ‖P (S (L x))‖
      ‖P (S (fp81s21_jointP_quadCurve H m D x))‖ ≤ _
    exact max_le h1 h2
  have hlip (x y : fp81s21_jointP_X p H) :
      ‖Fmk x - Fmk y‖ ≤ K * (1 + ‖x‖ + ‖y‖) * ‖x - y‖ := by
    have h1 : ‖P (S (L x)) - P (S (L y))‖ ≤
        K * (1 + ‖x‖ + ‖y‖) * ‖x - y‖ := by
      have hK' : cL ≤ K := le_max_left _ _
      have hfactor : 1 ≤ 1 + ‖x‖ + ‖y‖ := by
        have hx : 0 ≤ ‖x‖ := norm_nonneg _
        have hy : 0 ≤ ‖y‖ := norm_nonneg _
        linarith
      calc
        ‖P (S (L x)) - P (S (L y))‖ ≤ cL * ‖x - y‖ := hlin_diff x y
        _ ≤ K * (1 + ‖x‖ + ‖y‖) * ‖x - y‖ := by
          have hcoef : cL ≤ K * (1 + ‖x‖ + ‖y‖) := by
            calc cL ≤ K := hK'
              _ ≤ K * (1 + ‖x‖ + ‖y‖) := le_mul_of_one_le_right hK hfactor
          exact mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
    have h2 : ‖P (S (fp81s21_jointP_quadCurve H m D x)) -
        P (S (fp81s21_jointP_quadCurve H m D y))‖ ≤
          K * (1 + ‖x‖ + ‖y‖) * ‖x - y‖ := by
      have hK' : cQ ≤ K := le_max_right _ _
      have hfactor : ‖x‖ + ‖y‖ ≤ 1 + ‖x‖ + ‖y‖ := by linarith
      calc
        ‖P (S (fp81s21_jointP_quadCurve H m D x)) -
            P (S (fp81s21_jointP_quadCurve H m D y))‖ ≤
            cQ * (‖x‖ + ‖y‖) * ‖x - y‖ := hquad_diff x y
        _ ≤ K * (1 + ‖x‖ + ‖y‖) * ‖x - y‖ := by
          have hcoef : cQ * (‖x‖ + ‖y‖) ≤ K * (1 + ‖x‖ + ‖y‖) := by
            exact mul_le_mul hK' hfactor
              (add_nonneg (norm_nonneg _) (norm_nonneg _)) hK
          exact mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
    change max
      ‖P (S (L x)) - P (S (L y))‖
      ‖P (S (fp81s21_jointP_quadCurve H m D x)) -
        P (S (fp81s21_jointP_quadCurve H m D y))‖ ≤ _
    exact max_le h1 h2
  have hcont : Continuous Fmk :=
    fp81s21_jointC_continuous_of_lip K hK Fmk hlip
  refine ⟨K, hK, ?_, ?_, hlip⟩
  · simpa [Fmk] using hcont.measurable
  · simpa [Fmk] using hgrowth

#print axioms fp81s21_jointC_partialCenter_apply
#print axioms fp81s21_jointC_partialCenter_norm_le_one
#print axioms fp81s21_jointC_map_local_estimate

end HRS.Fp81.S21

end

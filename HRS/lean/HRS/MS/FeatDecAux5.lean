import HRS.MS.FeatDecAux4

/-!
# S8.5 `feature_decay`, part 5 (S85 packet): from `decayNormE` to weighted bounds of `∂_a f`

* `s85_decay_pt`: a bound `decayNormE k b g ≤ ofReal B` gives `⟨x⟩^{b+j} |∂^I g(x)| ≤ B` (`j ≤ k`);
* `s85_gradcomp_bound`: `F ∈ C^{n+1}` with `⟨x⟩^{s+1+j}|∂^I F| ≤ B` (`j ≤ n+1`) gives `∂_aF ∈ C^n` and
  `‖D^j ∂_a F(x)‖ ≤ d^{n+1} B ⟨x⟩^{-(s+2+j)}`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

namespace HRS.MS.S85

open HRS HRS.Whole HRS.MS.Ul HRS.MS.Adj

variable {d : ℕ}

theorem s85_decay_pt {k : ℕ} {b B : ℝ} {g : Euc d → ℝ} (hB : 0 ≤ B)
    (h : decayNormE k b g ≤ ENNReal.ofReal B) (j : ℕ) (hj : j ≤ k) (I : Fin j → Fin d)
    (x : Euc d) : jbracket x ^ (b + (j : ℝ)) * |partialDeriv I g x| ≤ B := by
  have h1 := (HRS.MS.AdjDecay.ad3_term_le (b := b) (g := g) hj I x).trans h
  exact (ENNReal.ofReal_le_ofReal_iff hB).1 h1

theorem s85_gradComp_eq (a : Fin d) (F : Euc d → ℝ) :
    gradComp a F = fun y => fderiv ℝ F y (EuclideanSpace.single a (1 : ℝ)) := by
  funext y
  rw [u2_fderiv_eq_sum]
  simp [gradComp]

theorem s85_gradcomp_bound (s : ℝ) (n : ℕ) {F : Euc d → ℝ} (hd1 : 1 ≤ d)
    (hF : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) F) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ j ≤ n + 1, ∀ (I : Fin j → Fin d) (x : Euc d),
      jbracket x ^ (s + 1 + (j : ℝ)) * |partialDeriv I F x| ≤ B) (a : Fin d) :
    ContDiff ℝ (n : WithTop ℕ∞) (gradComp a F) ∧ ∀ j ≤ n, ∀ x : Euc d,
      ‖iteratedFDeriv ℝ j (gradComp a F) x‖ ≤
        (d : ℝ) ^ (n + 1) * B * jbracket x ^ (-(s + 2 + (j : ℝ))) := by
  rw [s85_gradComp_eq]
  have hF' : ContDiff ℝ (n + 1) F := by exact_mod_cast hF
  refine ⟨?_, fun j hj x => ?_⟩
  · have h1 : ContDiff ℝ (n : WithTop ℕ∞) (fderiv ℝ F) :=
      hF'.fderiv_right (m := (n : WithTop ℕ∞)) (by push_cast; exact le_refl _)
    exact h1.clm_apply (contDiff_const (c := EuclideanSpace.single a (1 : ℝ)))
  · have h1 := u2_fderiv_apply_bound hF' (EuclideanSpace.single a (1 : ℝ)) j hj x
    rw [EuclideanSpace.norm_single, norm_one, one_mul] at h1
    refine h1.trans ?_
    have h2 := u2_opnorm_le_sum (iteratedFDeriv ℝ (j + 1) F x)
    have hjb : 0 < jbracket x ^ (s + 1 + ((j + 1 : ℕ) : ℝ)) :=
      Real.rpow_pos_of_pos (u2_jb_pos x) _
    have h3 : ∀ I : Fin (j + 1) → Fin d,
        |iteratedFDeriv ℝ (j + 1) F x (fun l => EuclideanSpace.single (I l) (1 : ℝ))| ≤
          B * jbracket x ^ (-(s + 2 + (j : ℝ))) := by
      intro I
      have h4 := hB (j + 1) (by omega) I x
      have e : s + 1 + ((j + 1 : ℕ) : ℝ) = s + 2 + (j : ℝ) := by push_cast; ring
      rw [e] at h4 hjb
      unfold partialDeriv at h4
      have hp : 0 < jbracket x ^ (s + 2 + (j : ℝ)) := hjb
      rw [Real.rpow_neg (u2_jb_pos x).le, ← div_eq_mul_inv, le_div_iff₀ hp]
      linarith
    have h5 : ∑ I : Fin (j + 1) → Fin d,
        |iteratedFDeriv ℝ (j + 1) F x (fun l => EuclideanSpace.single (I l) (1 : ℝ))| ≤
        (d : ℝ) ^ (j + 1) * (B * jbracket x ^ (-(s + 2 + (j : ℝ)))) := by
      refine (Finset.sum_le_sum fun I _ => h3 I).trans (le_of_eq ?_)
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
    have hd1' : (1 : ℝ) ≤ d := by exact_mod_cast hd1
    have hdj : (d : ℝ) ^ (j + 1) ≤ (d : ℝ) ^ (n + 1) := pow_le_pow_right₀ hd1' (by omega)
    have hP : 0 ≤ B * jbracket x ^ (-(s + 2 + (j : ℝ))) :=
      mul_nonneg hB0 (Real.rpow_nonneg (u2_jb_pos x).le _)
    calc ‖iteratedFDeriv ℝ (j + 1) F x‖ ≤ _ := h2
      _ ≤ _ := h5
      _ ≤ (d : ℝ) ^ (n + 1) * (B * jbracket x ^ (-(s + 2 + (j : ℝ)))) :=
          mul_le_mul_of_nonneg_right hdj hP
      _ = _ := by ring

end HRS.MS.S85

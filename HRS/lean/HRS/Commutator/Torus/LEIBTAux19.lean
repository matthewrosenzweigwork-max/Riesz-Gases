import HRS.Commutator.Torus.LEIBTAux18

/-!
# LEIB-T helpers, part 19: the bump function and norm comparison on boxes
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace
  ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- The bump function: `1` on `‖v‖ ≤ d`, supported in `‖v‖ < 2d`. -/
def leibt_bump (hd : 1 ≤ d) : ContDiffBump (0 : 𝔼) :=
  ⟨(d : ℝ), 2 * d, by exact_mod_cast hd, by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith⟩

lemma leibt_abs_apply_le_norm (v : 𝔼) (i : Fin d) : |v i| ≤ ‖v‖ := by
  have := PiLp.norm_apply_le v i
  simpa [Real.norm_eq_abs] using this

lemma leibt_norm_le_of_coord (hd : 1 ≤ d) {v : 𝔼} (hv : ∀ i, |v i| ≤ 1) : ‖v‖ ≤ d := by
  have h1 : ‖v‖ ^ 2 = ∑ i, (v i) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
    simp
  have h2 : ∑ i, (v i) ^ 2 ≤ d := by
    calc ∑ i, (v i) ^ 2 ≤ ∑ _i : Fin d, (1 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have := hv i
          have h0 : (v i) ^ 2 = |v i| ^ 2 := (sq_abs _).symm
          rw [h0]
          nlinarith [abs_nonneg (v i)]
      _ = d := by simp
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h3 : ‖v‖ ^ 2 ≤ (d : ℝ) ^ 2 := by nlinarith
  exact le_of_sq_le_sq h3 (by positivity) |> fun h => by simpa using h

lemma leibt_bump_eq_one (hd : 1 ≤ d) {v : 𝔼} (hv : ∀ i, |v i| ≤ 1) : leibt_bump hd v = 1 := by
  apply ContDiffBump.one_of_mem_closedBall
  rw [mem_closedBall_zero_iff]
  exact leibt_norm_le_of_coord hd hv

lemma leibt_bump_support (hd : 1 ≤ d) {v : 𝔼} (hv : leibt_bump hd v ≠ 0) (i : Fin d) :
    |v i| < 2 * d := by
  have h1 : ‖v‖ < 2 * d := by
    by_contra h
    push Not at h
    apply hv
    apply ContDiffBump.zero_of_le_dist
    simpa [dist_zero_right, leibt_bump] using h
  exact lt_of_le_of_lt (leibt_abs_apply_le_norm v i) h1

lemma leibt_bump_contDiff (hd : 1 ≤ d) : ContDiff ℝ ∞ (fun v : 𝔼 => leibt_bump hd v) :=
  (leibt_bump hd).contDiff

lemma leibt_bump_compact (hd : 1 ≤ d) : HasCompactSupport (fun v : 𝔼 => leibt_bump hd v) :=
  (leibt_bump hd).hasCompactSupport

lemma leibt_chi_cs (hd : 1 ≤ d) {e : ℕ} (he : 1 ≤ e) :
    HasCompactSupport (fun v : 𝔼 => (((leibt_bump hd v) ^ e : ℝ) : ℂ)) :=
  (leibt_bump_compact hd).comp_left (g := fun x : ℝ => (((x ^ e : ℝ)) : ℂ)) (by
    simp [zero_pow (by omega : e ≠ 0)])

lemma leibt_chi_cd (hd : 1 ≤ d) (e : ℕ) :
    ContDiff ℝ ∞ (fun v : 𝔼 => (((leibt_bump hd v) ^ e : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp ((contDiff_id.pow e).comp (leibt_bump_contDiff hd))

/-- The cut-off `φ^e` (`e ≥ 1`) as a complex Schwartz function. -/
def leibt_chi (hd : 1 ≤ d) {e : ℕ} (he : 1 ≤ e) : SchwartzMap 𝔼 ℂ :=
  (leibt_chi_cs hd he).toSchwartzMap (leibt_chi_cd hd e)

lemma leibt_chi_apply (hd : 1 ≤ d) {e : ℕ} (he : 1 ≤ e) (v : 𝔼) :
    leibt_chi hd he v = (((leibt_bump hd v) ^ e : ℝ) : ℂ) := rfl

lemma leibt_chi_cs' (hd : 1 ≤ d) {e : ℕ} (he : 1 ≤ e) : HasCompactSupport (⇑(leibt_chi hd he)) :=
  leibt_chi_cs hd he

end HRS.Commutator.TorusNote

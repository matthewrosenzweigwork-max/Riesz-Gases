import HRS.Sections.ScrnAux23

/-!
# Packet SCRN, part 24: the deterministic covariation density `Σ̄` is a measurable, psd, bounded matrix path

`scrnSig ts G c r` is the matrix `1_{0 ≤ r < t_a ∧ t_b} c ∫ ⟨G_a(r,x), G_b(r,x)⟩ dx` (the Haar version
of the A8P density); with `G_a(r,·) = 1_{r ∈ [0,t_a]} ∇ f_a^r` it equals `scrnSigBar` of `ScrnAux16`
(`scrnSig_eq_scrnSigBar`).  `scrnSig_isDet` gives `IsDetCovMatrix` (hypotheses of Lemma A.27).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d q : ℕ}

/-- The cut-off gradient field of the `a`-th transported test. -/
def scrnGc {p : ℕ} (ts : Fin p → ℝ) (f : Fin p → ℝ → Torus d → ℝ) (a : Fin p) (r : ℝ) (x : Torus d) :
    Euc d :=
  if r ∈ Set.Icc 0 (ts a) then Torus.grad (f a r) x else 0

/-- `Σ̄_r^{ab} = 1_{0 ≤ r < min(t_a,t_b)} c ∫ ⟨G_a(r), G_b(r)⟩`. -/
def scrnSig (ts : Fin q → ℝ) (G : Fin q → ℝ → Torus d → Euc d) (c : ℝ) (r : ℝ) :
    Matrix (Fin q) (Fin q) ℝ :=
  Matrix.of fun a b => if 0 ≤ r ∧ r < min (ts a) (ts b) then
    c * ∫ x, inner ℝ (G a r x) (G b r x) else 0

lemma scrnSig_eq_scrnSigBar (ts : Fin q → ℝ) (f : Fin q → ℝ → Torus d → ℝ) (c r : ℝ) :
    scrnSig ts (scrnGc ts f) c r = scrnSigBar ts f c r := by
  ext a b
  unfold scrnSig scrnSigBar
  simp only [Matrix.of_apply]
  by_cases h : 0 ≤ r ∧ r < min (ts a) (ts b)
  · have h1 : r ∈ Set.Icc 0 (ts a) := ⟨h.1, (lt_min_iff.1 h.2).1.le⟩
    have h2 : r ∈ Set.Icc 0 (ts b) := ⟨h.1, (lt_min_iff.1 h.2).2.le⟩
    rw [if_pos h, if_pos h]
    simp [scrnGc, h1, h2]
  · rw [if_neg h, if_neg h]

section SigBar

variable {ts : Fin q → ℝ} {G : Fin q → ℝ → Torus d → Euc d} {c : ℝ}

theorem scrnSig_entry_bound {B : ℝ} (hGb : ∀ a r x, ‖G a r x‖ ≤ B) (a b : Fin q) (r : ℝ) :
    |scrnSig ts G c r a b| ≤ |c| * (B * B) := by
  unfold scrnSig
  simp only [Matrix.of_apply]
  split_ifs with h
  · rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine (abs_integral_le_integral_abs).trans ?_
    have hbd : ∀ x, |inner ℝ (G a r x) (G b r x)| ≤ B * B := fun x =>
      (abs_real_inner_le_norm _ _).trans (mul_le_mul (hGb a r x) (hGb b r x) (norm_nonneg _)
        ((norm_nonneg _).trans (hGb a r x)))
    calc ∫ x, |inner ℝ (G a r x) (G b r x)| ≤ ∫ _x : Torus d, B * B :=
          integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _) (integrable_const _)
            (Eventually.of_forall hbd)
      _ = B * B := by simp
  · simp only [abs_zero]
    have hB : 0 ≤ B := (norm_nonneg _).trans (hGb a r (0 : Torus d))
    positivity

theorem scrnSig_entry_meas (hGm : ∀ a, Measurable fun p : ℝ × Torus d => G a p.1 p.2) (a b : Fin q) :
    Measurable fun r => scrnSig ts G c r a b := by
  have hI : Measurable fun r : ℝ => ∫ x, inner ℝ (G a r x) (G b r x) := by
    have hsm : StronglyMeasurable fun p : ℝ × Torus d => inner ℝ (G a p.1 p.2) (G b p.1 p.2) :=
      ((hGm a).inner (hGm b)).stronglyMeasurable
    exact (hsm.integral_prod_right' (ν := (volume : Measure (Torus d)))).measurable
  unfold scrnSig
  simp only [Matrix.of_apply]
  refine Measurable.ite ?_ (measurable_const.mul hI) measurable_const
  exact (measurableSet_le measurable_const measurable_id).inter (measurableSet_lt measurable_id measurable_const)

theorem scrnSig_meas (hGm : ∀ a, Measurable fun p : ℝ × Torus d => G a p.1 p.2) :
    Measurable (scrnSig ts G c) :=
  measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun b => scrnSig_entry_meas hGm a b

theorem scrnSig_psd (hGm : ∀ a, Measurable fun p : ℝ × Torus d => G a p.1 p.2) {B : ℝ}
    (hGb : ∀ a r x, ‖G a r x‖ ≤ B) (hc : 0 ≤ c) (r : ℝ) : (scrnSig ts G c r).PosSemidef := by
  by_cases hr : 0 ≤ r
  swap
  · have : scrnSig ts G c r = 0 := by
      ext a b
      simp [scrnSig, hr]
    rw [this]
    exact Matrix.PosSemidef.zero
  set g : Fin q → Torus d → Euc d := fun a x => if r < ts a then G a r x else 0 with hg
  have hent : ∀ a b, scrnSig ts G c r a b = c * ∫ x, inner ℝ (g a x) (g b x) := by
    intro a b
    unfold scrnSig
    simp only [Matrix.of_apply, hg]
    by_cases h1 : r < ts a
    · by_cases h2 : r < ts b
      · simp only [h1, h2, if_true, if_pos (show 0 ≤ r ∧ r < min (ts a) (ts b) from ⟨hr, lt_min h1 h2⟩)]
      · have : ¬ (0 ≤ r ∧ r < min (ts a) (ts b)) := fun h => h2 (lt_of_lt_of_le h.2 (min_le_right _ _))
        simp [h2, this]
    · have : ¬ (0 ≤ r ∧ r < min (ts a) (ts b)) := fun h => h1 (lt_of_lt_of_le h.2 (min_le_left _ _))
      simp [h1, this]
  have hgm : ∀ a, Measurable (g a) := by
    intro a
    by_cases h : r < ts a
    · simp only [hg, if_pos h]; exact (hGm a).comp measurable_prodMk_left
    · simp only [hg, if_neg h]; exact measurable_const
  have hgb : ∀ a x, ‖g a x‖ ≤ B := by
    intro a x
    by_cases h : r < ts a
    · simp only [hg, if_pos h]; exact hGb a r x
    · simp only [hg, if_neg h, norm_zero]
      exact (norm_nonneg _).trans (hGb a r (0 : Torus d))
  have hint : ∀ a b, Integrable (fun x => inner ℝ (g a x) (g b x)) := by
    intro a b
    refine Integrable.of_bound (C := B * B) ((hgm a).inner (hgm b)).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul (hgb a x) (hgb b x) (norm_nonneg _)
      ((norm_nonneg _).trans (hgb a x)))
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · refine Matrix.IsHermitian.ext fun a b => ?_
    have hsym : ∀ y, inner ℝ (g b y) (g a y) = inner ℝ (g a y) (g b y) := fun y => real_inner_comm _ _
    simp only [star_trivial, hent, hsym]
  · simp only [star_trivial, dotProduct, Matrix.mulVec, hent]
    have e2 : ∑ a, x a * ∑ b, c * (∫ y, inner ℝ (g a y) (g b y)) * x b =
        c * ∫ y, ∑ a, ∑ b, (x a * x b) * (inner ℝ (g a y) (g b y)) := by
      rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ fun b _ => (hint a b).const_mul _)]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [integral_finsetSum _ (fun b _ => (hint a b).const_mul _), Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [integral_const_mul]; ring
    rw [e2]
    refine mul_nonneg hc (integral_nonneg fun y => ?_)
    have : ∑ a, ∑ b, (x a * x b) * (inner ℝ (g a y) (g b y)) = ‖∑ a, x a • g a y‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, sum_inner]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [inner_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [real_inner_smul_left, real_inner_smul_right]; ring
    rw [this]
    exact sq_nonneg _

theorem scrnSig_isDet (hGm : ∀ a, Measurable fun p : ℝ × Torus d => G a p.1 p.2) {B : ℝ}
    (hGb : ∀ a r x, ‖G a r x‖ ≤ B) (hc : 0 ≤ c) (T : ℝ) :
    IsDetCovMatrix T (scrnSig ts G c) := by
  refine ⟨scrnSig_meas hGm, fun σ _ => scrnSig_psd hGm hGb hc σ, ?_⟩
  have hm : Measurable fun σ => s1Norm (scrnSig ts G c σ) :=
    measurable_traceNormMatrix (scrnSig ts G c) (fun i j => scrnSig_entry_meas hGm i j)
  refine Integrable.mono' (g := fun _ => ∑ _a : Fin q, ∑ _b : Fin q, |c| * (B * B))
    (integrable_const _) hm.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun σ _ => ?_)
  rw [Real.norm_of_nonneg (traceNormMatrix_nonneg _)]
  refine (LindebergAux.s1Norm_le_sum _).trans ?_
  exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
    scrnSig_entry_bound hGb b a σ

end SigBar

end HRS

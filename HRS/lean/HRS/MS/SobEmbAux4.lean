import HRS.MS.SobEmbAux3
import HRS.Whole.Basic

/-!
# SA1, Aux4: from the ladder to `sobolevWNorm` bounds

`sa1_glue`: if `Reach a₀ ℓ p` holds then `W^{m+ℓ,a₀} ↪ W^{m,p}`, in the form used by `sobolevWNorm`
(with the integrability of `‖D^j f‖^p`, `j ≤ m`, as part of the conclusion).
-/

noncomputable section

open MeasureTheory Filter Topology Module
open scoped ENNReal NNReal ContDiff

namespace HRS.SA1

variable {d : ℕ}

theorem sa1_lp_data {V : Type*} [NormedAddCommGroup V] {h : EuclideanSpace ℝ (Fin d) → V}
    {p : ℝ} (hp : 0 < p) (hh : MemLp h (ENNReal.ofReal p) volume) :
    Integrable (fun x => ‖h x‖ ^ p) ∧
      (∫ x, ‖h x‖ ^ p) ^ (1 / p) = (eLpNorm h (ENNReal.ofReal p) volume).toReal := by
  have hq0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.2 hp).ne'
  refine ⟨?_, ?_⟩
  · have := (integrable_norm_rpow_iff hh.aestronglyMeasurable hq0 ENNReal.ofReal_ne_top).2 hh
    rwa [ENNReal.toReal_ofReal hp.le] at this
  · rw [hh.eLpNorm_eq_integral_rpow_norm hq0 ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp.le,
      ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun x => by positivity) _),
      one_div]

theorem sa1_memLp_of_integrable {V : Type*} [NormedAddCommGroup V]
    {h : EuclideanSpace ℝ (Fin d) → V} {p : ℝ} (hp : 0 < p)
    (hc : AEStronglyMeasurable h volume) (hi : Integrable (fun x => ‖h x‖ ^ p)) :
    MemLp h (ENNReal.ofReal p) volume := by
  rw [← integrable_norm_rpow_iff hc (ENNReal.ofReal_pos.2 hp).ne' ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp.le]
  exact hi

/-- the real `L^q` norm of `D^j f` used in `sobolevWNorm` -/
def sa1_T (j : ℕ) (q : ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ) : ℝ :=
  (∫ x, ‖iteratedFDeriv ℝ j f x‖ ^ q) ^ (1 / q)

theorem sa1_T_nonneg (j : ℕ) (q : ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ) : 0 ≤ sa1_T j q f :=
  Real.rpow_nonneg (integral_nonneg fun x => by positivity) _

theorem sa1_sob_eq (m : ℕ) (q : ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ) :
    HRS.Whole.sobolevWNorm m q f = ∑ j ∈ Finset.range (m + 1), sa1_T j q f := rfl

/-- If `‖D^j f‖^q` is integrable, `sa1_nrm j q f` is finite and its real part is `sa1_T j q f`. -/
theorem sa1_nrm_of_integrable {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : ContDiff ℝ ∞ f) {q : ℝ} (hq : 0 < q)
    {j : ℕ} (hi : Integrable (fun x => ‖iteratedFDeriv ℝ j f x‖ ^ q)) :
    sa1_nrm j q f ≠ ⊤ ∧ (sa1_nrm j q f).toReal = sa1_T j q f := by
  have hmem := sa1_memLp_of_integrable hq (sa1_cont_iter hf j).aestronglyMeasurable hi
  exact ⟨hmem.eLpNorm_ne_top, ((sa1_lp_data hq hmem).2).symm⟩

theorem sa1_integrable_of_nrm {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : ContDiff ℝ ∞ f) {q : ℝ} (hq : 0 < q)
    {j : ℕ} (hn : sa1_nrm j q f ≠ ⊤) :
    Integrable (fun x => ‖iteratedFDeriv ℝ j f x‖ ^ q) ∧ (sa1_nrm j q f).toReal = sa1_T j q f := by
  have hmem : MemLp (iteratedFDeriv ℝ j f) (ENNReal.ofReal q) volume :=
    lt_top_iff_ne_top.2 (show eLpNorm (iteratedFDeriv ℝ j f) (ENNReal.ofReal q) volume ≠ ⊤ from hn)
  exact ⟨(sa1_lp_data hq hmem).1, ((sa1_lp_data hq hmem).2).symm⟩

theorem sa1_sum_shift (g : ℕ → ℝ) (hg : ∀ j, 0 ≤ g j) (i ℓ m : ℕ) (him : i ≤ m) :
    ∑ t ∈ Finset.range (ℓ + 1), g (i + t) ≤ ∑ j ∈ Finset.range (m + ℓ + 1), g j := by
  have h1 : ∑ t ∈ Finset.range (ℓ + 1), g (i + t) = ∑ j ∈ Finset.Ico i (i + (ℓ + 1)), g j := by
    rw [Finset.sum_Ico_eq_sum_range]; simp
  rw [h1]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => hg j)
  intro j hj
  simp only [Finset.mem_Ico, Finset.mem_range] at hj ⊢
  omega

theorem sa1_glue {a0 p : ℝ} (ha0 : 0 < a0) (hp : 0 < p) {ℓ : ℕ} (hR : sa1_Reach d a0 ℓ p) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ ∞ f →
      (∀ j ≤ m + ℓ, Integrable (fun x => ‖iteratedFDeriv ℝ j f x‖ ^ a0)) →
      (∀ j ≤ m, Integrable (fun x => ‖iteratedFDeriv ℝ j f x‖ ^ p)) ∧
        HRS.Whole.sobolevWNorm m p f ≤ C * HRS.Whole.sobolevWNorm (m + ℓ) a0 f := by
  choose C hC using hR
  refine ⟨∑ i ∈ Finset.range (m + 1), (C i : ℝ), Finset.sum_nonneg fun i _ => (C i).2, fun f hf hint => ?_⟩
  have hfin : ∀ j ≤ m + ℓ, sa1_nrm j a0 f ≠ ⊤ ∧ (sa1_nrm j a0 f).toReal = sa1_T j a0 f :=
    fun j hj => sa1_nrm_of_integrable hf ha0 (hint j hj)
  have hbound : ∀ i ≤ m, sa1_nrm i p f ≠ ⊤ ∧
      (sa1_nrm i p f).toReal ≤ (C i : ℝ) * ∑ t ∈ Finset.range (ℓ + 1), sa1_T (i + t) a0 f := by
    intro i him
    have hsumfin : ∑ t ∈ Finset.range (ℓ + 1), sa1_nrm (i + t) a0 f ≠ ⊤ :=
      (ENNReal.sum_lt_top.2 fun t ht => lt_top_iff_ne_top.2
        (hfin (i + t) (by have := Finset.mem_range.1 ht; omega)).1).ne
    have hle := hC i f hf
    have hne : (C i : ℝ≥0∞) * ∑ t ∈ Finset.range (ℓ + 1), sa1_nrm (i + t) a0 f ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.coe_ne_top hsumfin
    refine ⟨ne_top_of_le_ne_top hne hle, ?_⟩
    calc (sa1_nrm i p f).toReal ≤ ((C i : ℝ≥0∞) * ∑ t ∈ Finset.range (ℓ + 1), sa1_nrm (i + t) a0 f).toReal :=
          ENNReal.toReal_mono hne hle
      _ = (C i : ℝ) * ∑ t ∈ Finset.range (ℓ + 1), sa1_T (i + t) a0 f := by
          rw [ENNReal.toReal_mul, ENNReal.coe_toReal,
            ENNReal.toReal_sum (fun t ht => (hfin (i + t) (by have := Finset.mem_range.1 ht; omega)).1)]
          congr 1
          refine Finset.sum_congr rfl fun t ht => ?_
          exact (hfin (i + t) (by have := Finset.mem_range.1 ht; omega)).2
  refine ⟨fun j hj => (sa1_integrable_of_nrm hf hp (hbound j hj).1).1, ?_⟩
  rw [sa1_sob_eq, sa1_sob_eq, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have him : i ≤ m := by have := Finset.mem_range.1 hi; omega
  have h1 := (hbound i him).2
  rw [(sa1_integrable_of_nrm hf hp (hbound i him).1).2] at h1
  refine h1.trans ?_
  exact mul_le_mul_of_nonneg_left (sa1_sum_shift (fun j => sa1_T j a0 f) (fun j => sa1_T_nonneg j a0 f) i ℓ m him)
    (C i).2

end HRS.SA1

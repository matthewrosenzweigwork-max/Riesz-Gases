import HRS.Commutator.Torus.NRSTAux16

/-!
# NRS-T, part 17: box truncations of the Fourier series of a smooth mean-free function
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped BigOperators ComplexConjugate ENNReal ContDiff

namespace HRS.Commutator.TorusNote.NRST

open HRS HRS.Commutator

variable {d : ℕ}

/-- The box `{k : |k_i| ≤ n}`. -/
def boxS (d n : ℕ) : Finset (Lattice d) := Fintype.piFinset fun _ : Fin d => Finset.Icc (-(n : ℤ)) n

lemma mem_boxS {n : ℕ} {k : Lattice d} : k ∈ boxS d n ↔ ∀ i, |k i| ≤ n := by
  simp [boxS, Fintype.mem_piFinset, abs_le]

lemma boxS_mono {n m : ℕ} (h : n ≤ m) : boxS d n ⊆ boxS d m := by
  intro k hk
  rw [mem_boxS] at hk ⊢
  intro i
  exact (hk i).trans (by exact_mod_cast h)

lemma tendsto_boxS : Tendsto (fun n => boxS d n) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro t
  obtain ⟨n, hn⟩ := exists_box t
  refine ⟨n, fun m hm => ?_⟩
  intro k hk
  rw [mem_boxS]
  intro i
  exact (hn k hk i).trans (by exact_mod_cast hm)

open Classical in
/-- Box truncation of the Fourier series. -/
def truncOf (n : ℕ) (a : Torus d → ℝ) : TPA d :=
  AddMonoidAlgebra.ofCoeff (Finsupp.onFinset (boxS d n)
    (fun k => if k ∈ boxS d n then Torus.fcoef a k else 0) (fun k hk => by
      by_contra hc
      exact hk (by simp [hc])))

lemma coeff_truncOf (n : ℕ) (a : Torus d → ℝ) (k : Lattice d) :
    (truncOf n a).coeff k = if k ∈ boxS d n then Torus.fcoef a k else 0 := by
  classical
  simp [truncOf]

lemma neg_mem_boxS {n : ℕ} {k : Lattice d} : -k ∈ boxS d n ↔ k ∈ boxS d n := by
  rw [mem_boxS, mem_boxS]
  simp

lemma truncOf_symm (n : ℕ) (a : Torus d → ℝ) (k : Lattice d) :
    (truncOf n a).coeff (-k) = (starRingEnd ℂ) ((truncOf n a).coeff k) := by
  classical
  by_cases h : k ∈ boxS d n
  · have h' : -k ∈ boxS d n := neg_mem_boxS.2 h
    simp [coeff_truncOf, h, h', fcoef_neg_conj]
  · have h' : -k ∉ boxS d n := fun hh => h (neg_mem_boxS.1 hh)
    simp [coeff_truncOf, h, h']

lemma truncOf_zero (n : ℕ) {a : Torus d → ℝ} (ha : ∫ x, a x = 0) : (truncOf n a).coeff 0 = 0 := by
  classical
  rw [coeff_truncOf]
  have : (0 : Lattice d) ∈ boxS d n := by
    rw [mem_boxS]; intro i; simp
  rw [if_pos this, Torus.fcoef_zero]
  simp [Torus.mean, ha]

lemma ev_truncOf (n : ℕ) (a : Torus d → ℝ) (x : Torus d) :
    ev (truncOf n a) x = ∑ k ∈ boxS d n, Torus.fcoef a k * Torus.mode k x := by
  classical
  rw [ev_apply_sum]
  have hsub : (truncOf n a).coeff.support ⊆ boxS d n := by
    intro k hk
    by_contra hc
    rw [Finsupp.mem_support_iff] at hk
    exact hk (by rw [coeff_truncOf, if_neg hc])
  rw [Finset.sum_subset hsub (fun k _ hk => by
    have : (truncOf n a).coeff k = 0 := by simpa using hk
    simp [this])]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [coeff_truncOf, if_pos hk]

lemma smooth_summable {a : Torus d → ℝ} (ha : Torus.IsSmooth a) :
    Summable fun k : Lattice d => ‖Torus.fcoef a k‖ := by
  have ha' : ContDiff ℝ ∞ (Torus.lift a) := ha
  exact Torus.summable_fcoef_of_contDiff (fun n => ha'.of_le (by exact_mod_cast le_top))

lemma smooth_continuous {a : Torus d → ℝ} (ha : Torus.IsSmooth a) : Continuous a := by
  have ha' : ContDiff ℝ ∞ (Torus.lift a) := ha
  exact Torus.continuous_of_continuous_lift ha'.continuous

lemma truncOf_tendsto {a : Torus d → ℝ} (ha : Torus.IsSmooth a) (x : Torus d) :
    Tendsto (fun n => aOf (truncOf n a) x) atTop (𝓝 (a x)) := by
  have hc : Continuous a := smooth_continuous ha
  have hs : Summable fun k : Lattice d => ‖Torus.fcoef a k‖ := smooth_summable ha
  have h1 := Torus.hasSum_fcoef_series hc hs x
  have h2 : Tendsto (fun n => ∑ k ∈ boxS d n, Torus.fcoef a k * Torus.mode k x) atTop
      (𝓝 (a x : ℂ)) := h1.comp tendsto_boxS
  have h3 := (Complex.continuous_re.tendsto _).comp h2
  have e : (fun n => aOf (truncOf n a) x) =
      Complex.re ∘ fun n => ∑ k ∈ boxS d n, Torus.fcoef a k * Torus.mode k x := by
    funext n; simp only [aOf, Function.comp, ev_truncOf]
  rw [e]
  simpa using h3

lemma abs_aOf_truncOf_le {a : Torus d → ℝ} (ha : Torus.IsSmooth a) (n : ℕ) (x : Torus d) :
    |aOf (truncOf n a) x| ≤ ∑' k : Lattice d, ‖Torus.fcoef a k‖ := by
  have hs : Summable fun k : Lattice d => ‖Torus.fcoef a k‖ := smooth_summable ha
  unfold aOf
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [ev_truncOf]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ k ∈ boxS d n, ‖Torus.fcoef a k * Torus.mode k x‖ = ∑ k ∈ boxS d n, ‖Torus.fcoef a k‖ := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [norm_mul, Torus.norm_mode, mul_one]
    _ ≤ ∑' k : Lattice d, ‖Torus.fcoef a k‖ := hs.sum_le_tsum _ (fun _ _ => norm_nonneg _)

lemma ofReal_hom_trunc_le (t : ℝ) (n : ℕ) (a : Torus d → ℝ) :
    ENNReal.ofReal (hom t (truncOf n a)) ≤ homSqT t (fun k => Torus.fcoef a k) := by
  classical
  set g : Lattice d → ℝ≥0∞ := fun k => if k = 0 then 0 else
    ENNReal.ofReal ((2 * Real.pi * Lattice.enorm k) ^ (2 * t)) * ‖Torus.fcoef a k‖ₑ ^ 2 with hg
  unfold hom
  rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity)]
  calc ∑ k ∈ (truncOf n a).coeff.support,
        ENNReal.ofReal (lw t k ^ 2 * ‖(truncOf n a).coeff k‖ ^ 2)
      = ∑ k ∈ (truncOf n a).coeff.support, g k := by
        refine Finset.sum_congr rfl fun k hk => ?_
        have hkb : k ∈ boxS d n := by
          by_contra hc
          rw [Finsupp.mem_support_iff] at hk
          exact hk (by rw [coeff_truncOf, if_neg hc])
        rw [coeff_truncOf, if_pos hkb]
        by_cases h0 : k = 0
        · simp [hg, h0, lw_zero]
        · simp only [hg, if_neg h0]
          rw [lw_sq]
          unfold lw
          rw [if_neg h0, ENNReal.ofReal_mul (Real.rpow_nonneg (mul_nonneg (by positivity) (enorm_nonneg k)) _), ← ofReal_norm_eq_enorm,
            ENNReal.ofReal_pow (norm_nonneg _)]
    _ ≤ ∑' k, g k := ENNReal.sum_le_tsum _
    _ = homSqT t (fun k => Torus.fcoef a k) := rfl

end HRS.Commutator.TorusNote.NRST

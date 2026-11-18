import HRS.MS.MovSchAux6
import HRS.MS.QsfBridge1
import HRS.MP.SelfSimP4MolA3
import HRS.MP.RdRemainder

/-!
# S64 (S6.9), part 2: the canonical partition function is positive for every `N ≥ 1`, `0 ≤ s < d`

Namespace `HRS.MS.MovSch`, prefix `s64_`.  `s64_Zpos`: `0 < HRS.Whole.canonicalPartition (rieszKernel d s) (confinement q) N β` for `q, β > 0`,
`0 ≤ s` (also `s = 0`, the logarithmic kernel, where `s71_gwd` does not apply).  Proof: the pair weight satisfies
`exp(-(β/N) g(z)) ≤ (1+‖z‖)^{β/N}` (`g ≥ 0` for `s > 0`; `g = -log‖z‖` for `s = 0`), hence `exp(-βH_N) ≤ K₀ exp(-(βq/4) ∑‖x_k‖²)`,
which is integrable; the integrand is strictly positive.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovSch

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

lemma s64_pair_bound {s : ℝ} (hs0 : 0 ≤ s) {p : ℝ} (hp : 0 ≤ p) (z : Euc d) :
    Real.exp (-p * rieszKernel d s z) ≤ (1 + ‖z‖) ^ p := by
  have h1 : (1 : ℝ) ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
  unfold rieszKernel
  by_cases h : s = 0
  · rw [if_pos h]
    by_cases hz : ‖z‖ = 0
    · rw [hz]; simp
    · have hzpos : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      have : -p * -Real.log ‖z‖ = Real.log ‖z‖ * p := by ring
      rw [this, ← Real.rpow_def_of_pos hzpos]
      exact Real.rpow_le_rpow (norm_nonneg _) (by linarith) hp
  · rw [if_neg h]
    have hg : 0 ≤ ‖z‖ ^ (-s) := Real.rpow_nonneg (norm_nonneg _) _
    have : Real.exp (-p * ‖z‖ ^ (-s)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith
    exact this.trans (Real.one_le_rpow h1 hp)

lemma s64_one_add_pow_le {c : ℝ} (hc : 0 < c) (E : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ r : ℝ, 0 ≤ r → (1 + r) ^ E ≤ K * Real.exp (c * r ^ 2) := by
  have ha : (0 : ℝ) < 2 * c := by positivity
  refine ⟨(E.factorial : ℝ) * Real.exp (1 + (0 + 1) ^ 2 / (2 * c)), by positivity, fun r hr => ?_⟩
  have h2 := HRS.MS.Mov0.mov0_pow_exp_bound (a := 2 * c) (M := 0) ha E r hr
  have h3 : Real.exp (-(2 * c * r ^ 2 / 2) + 0 * r) * Real.exp (c * r ^ 2) = 1 := by
    rw [← Real.exp_add]
    have : -(2 * c * r ^ 2 / 2) + 0 * r + c * r ^ 2 = 0 := by ring
    rw [this, Real.exp_zero]
  have h4 : Real.exp (-(2 * c / 4) * r ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ (2 * c / 4) * r ^ 2 := by positivity
    linarith
  have hpos : 0 < Real.exp (c * r ^ 2) := Real.exp_pos _
  calc (1 + r) ^ E = (1 + r) ^ E * Real.exp (-(2 * c * r ^ 2 / 2) + 0 * r) * Real.exp (c * r ^ 2) := by
        rw [mul_assoc, h3, mul_one]
    _ ≤ ((E.factorial : ℝ) * Real.exp (1 + (0 + 1) ^ 2 / (2 * c)) * Real.exp (-(2 * c / 4) * r ^ 2)) *
          Real.exp (c * r ^ 2) := mul_le_mul_of_nonneg_right h2 hpos.le
    _ ≤ ((E.factorial : ℝ) * Real.exp (1 + (0 + 1) ^ 2 / (2 * c)) * 1) * Real.exp (c * r ^ 2) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4 (by positivity)) hpos.le
    _ = _ := by ring

lemma s64_measurable_ham {s : ℝ} {N : ℕ} (q : ℝ) :
    Measurable (HRS.Whole.canonicalHamiltonian (rieszKernel d s) (confinement q) : EucConfig d N → ℝ) := by
  refine S45.s45_measurable_ham (HRS.MP.RdRem.mrr_measurable_rieszKernel s) ?_
  unfold confinement
  exact (measurable_const.mul ((continuous_norm.pow 2).measurable)).div_const _

theorem s64_ham_integrable {s q β : ℝ} (hs0 : 0 ≤ s) (hq : 0 < q) (hβ : 0 < β) {N : ℕ} (hN : 1 ≤ N) :
    Integrable (fun X : EucConfig d N =>
      Real.exp (-β * HRS.Whole.canonicalHamiltonian (rieszKernel d s) (confinement q) X)) volume := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set p : ℝ := β / N with hp
  have hp0 : 0 ≤ p := by positivity
  set n0 : ℕ := ⌈p⌉₊ with hn0
  set E : ℕ := n0 * (N * N) with hE
  set c' : ℝ := β * q / (4 * N) with hc'
  have hc'0 : 0 < c' := by positivity
  obtain ⟨K0, hK0, hK⟩ := s64_one_add_pow_le hc'0 E
  -- the pointwise bound
  have hbound : ∀ X : EucConfig d N, Real.exp (-β * HRS.Whole.canonicalHamiltonian (rieszKernel d s) (confinement q) X) ≤
      K0 * HRS.MP.SelfSimP4Mol.p4m_E (β * q / 4) X := by
    intro X
    set S : ℝ := ∑ i, ‖X i‖ ^ 2 with hS
    set M : ℝ := 1 + ∑ i, ‖X i‖ with hM
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hr0 : 0 ≤ ∑ i, ‖X i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hM1 : 1 ≤ M := by linarith
    -- single pair bound
    have hpair : ∀ i j : Fin N, i ≠ j → 1 + ‖X i - X j‖ ≤ M := by
      intro i j hij
      have h1 : ‖X i - X j‖ ≤ ‖X i‖ + ‖X j‖ := norm_sub_le _ _
      have h2 : ‖X i‖ + ‖X j‖ ≤ ∑ k, ‖X k‖ := by
        have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun k => ‖X k‖)
          (show ({i, j} : Finset (Fin N)) ⊆ Finset.univ from Finset.subset_univ _)
          (fun _ _ _ => norm_nonneg _)
        rwa [Finset.sum_pair hij] at this
      linarith
    have hpair' : ∀ i j : Fin N, i ≠ j →
        Real.exp (-p * rieszKernel d s (X i - X j)) ≤ M ^ n0 := by
      intro i j hij
      refine (s64_pair_bound hs0 hp0 (X i - X j)).trans ?_
      have h1 : (1 + ‖X i - X j‖) ^ p ≤ (1 + ‖X i - X j‖) ^ (n0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg (X i - X j)]) (Nat.le_ceil p)
      rw [Real.rpow_natCast] at h1
      exact h1.trans (pow_le_pow_left₀ (by linarith [norm_nonneg (X i - X j)]) (hpair i j hij) n0)
    -- the pair product
    have hprod : Real.exp (-β * ((1 / (N : ℝ)) * ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j),
        rieszKernel d s (X i - X j))) ≤ M ^ E := by
      have e1 : -β * ((1 / (N : ℝ)) * ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j),
          rieszKernel d s (X i - X j)) =
          ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), (-p * rieszKernel d s (X i - X j)) := by
        have h0 : -β * ((1 / (N : ℝ)) * ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j),
            rieszKernel d s (X i - X j)) = -p * ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j),
            rieszKernel d s (X i - X j) := by
          rw [hp]; ring
        rw [h0]
        simp only [Finset.mul_sum]
      rw [e1, Real.exp_sum]
      simp_rw [Real.exp_sum]
      calc ∏ i : Fin N, ∏ j ∈ Finset.univ.filter (fun j => i < j), Real.exp (-p * rieszKernel d s (X i - X j))
          ≤ ∏ i : Fin N, ∏ j ∈ Finset.univ.filter (fun j => i < j), M ^ n0 := by
            refine Finset.prod_le_prod₀ (fun i _ => Finset.prod_nonneg fun j _ => (Real.exp_pos _).le) fun i _ => ?_
            refine Finset.prod_le_prod₀ (fun j _ => (Real.exp_pos _).le) fun j hj => ?_
            exact hpair' i j (ne_of_lt (Finset.mem_filter.1 hj).2)
        _ = M ^ (∑ i : Fin N, n0 * (Finset.univ.filter (fun j : Fin N => i < j)).card) := by
            simp only [Finset.prod_const, ← pow_mul]
            rw [Finset.prod_pow_eq_pow_sum]
        _ ≤ M ^ E := by
            refine pow_le_pow_right₀ hM1 ?_
            calc ∑ i : Fin N, n0 * (Finset.univ.filter (fun j : Fin N => i < j)).card
                ≤ ∑ _i : Fin N, n0 * N := Finset.sum_le_sum fun i _ => by
                  refine Nat.mul_le_mul_left _ ?_
                  calc _ ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_le_card (Finset.filter_subset _ _)
                    _ = N := by simp
              _ = E := by
                  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, hE]
                  ring
    -- M^E ≤ K0 exp(c' (∑‖x‖)^2) ≤ K0 exp(c' N S)
    have hME : M ^ E ≤ K0 * Real.exp (c' * N * S) := by
      refine (hK _ hr0).trans ?_
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hK0.le
      have hcs : (∑ i, ‖X i‖) ^ 2 ≤ (N : ℝ) * S := by
        have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin N))) (f := fun i => ‖X i‖)
        simpa [hS] using this
      nlinarith
    have hH : -β * HRS.Whole.canonicalHamiltonian (rieszKernel d s) (confinement q) X =
        -(β * q / 2) * S + -β * ((1 / (N : ℝ)) * ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j),
          rieszKernel d s (X i - X j)) := by
      have hA : ∑ i, q * ‖X i‖ ^ 2 / 2 = (q / 2) * S := by
        rw [hS, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      simp only [HRS.Whole.canonicalHamiltonian, confinement]
      rw [hA]
      ring
    rw [hH, Real.exp_add]
    have hE1 : Real.exp (-(β * q / 2) * S) * M ^ E ≤ Real.exp (-(β * q / 2) * S) * (K0 * Real.exp (c' * N * S)) :=
      mul_le_mul_of_nonneg_left hME (Real.exp_pos _).le
    have hcN : c' * N = β * q / 4 := by rw [hc']; field_simp
    have hcomb : Real.exp (-(β * q / 2) * S) * (K0 * Real.exp (c' * N * S)) =
        K0 * HRS.MP.SelfSimP4Mol.p4m_E (β * q / 4) X := by
      have hpE : HRS.MP.SelfSimP4Mol.p4m_E (β * q / 4) X = Real.exp (-(β * q / 4) * S) := by
        simp only [HRS.MP.SelfSimP4Mol.p4m_E, HRS.MP.SelfSimP4Mol.p4m_q, hS]
      rw [hpE, mul_left_comm, ← Real.exp_add]
      congr 2
      rw [show c' * N * S = (c' * N) * S from rfl, hcN]
      ring
    calc Real.exp (-(β * q / 2) * S) *
          Real.exp (-β * ((1 / (N : ℝ)) * ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j),
            rieszKernel d s (X i - X j)))
        ≤ Real.exp (-(β * q / 2) * S) * M ^ E :=
          mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
      _ ≤ _ := hE1.trans hcomb.le
  refine Integrable.mono' ((HRS.MP.SelfSimP4Mol.p4m_integrable_E (by positivity : 0 < β * q / 4)).const_mul K0)
    ((Real.measurable_exp.comp (measurable_const.mul (s64_measurable_ham q))).aestronglyMeasurable)
    (ae_of_all _ fun X => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact hbound X

theorem s64_Zpos {s q β : ℝ} (hs0 : 0 ≤ s) (hq : 0 < q) (hβ : 0 < β) {N : ℕ} (hN : 1 ≤ N) :
    0 < HRS.Whole.canonicalPartition (rieszKernel d s) (confinement q) N β := by
  have hint := s64_ham_integrable (d := d) hs0 hq hβ hN
  unfold HRS.Whole.canonicalPartition
  rw [integral_pos_iff_support_of_nonneg (fun X => (Real.exp_pos _).le) hint]
  have : Function.support (fun X : EucConfig d N =>
      Real.exp (-β * HRS.Whole.canonicalHamiltonian (rieszKernel d s) (confinement q) X)) = Set.univ := by
    ext X
    simp [Real.exp_ne_zero]
  rw [this]
  exact Measure.measure_univ_pos.2 (NeZero.ne _)


theorem s64_canon_prob {s q β : ℝ} (hs0 : 0 ≤ s) (hq : 0 < q) (hβ : 0 < β) {N : ℕ} (hN : 1 ≤ N) :
    IsProbabilityMeasure (HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement q) N β) := by
  have hint := s64_ham_integrable (d := d) hs0 hq hβ hN
  have hZ := s64_Zpos (d := d) hs0 hq hβ hN
  refine ⟨?_⟩
  unfold HRS.Whole.canonicalGibbs
  rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, smul_eq_mul]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun X => (Real.exp_pos _).le)]
  have : (∫ X : EucConfig d N, Real.exp (-β * HRS.Whole.canonicalHamiltonian (rieszKernel d s) (confinement q) X)) =
      HRS.Whole.canonicalPartition (rieszKernel d s) (confinement q) N β := rfl
  rw [this]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hZ).ne' ENNReal.ofReal_ne_top

end HRS.MS.MovSch

end

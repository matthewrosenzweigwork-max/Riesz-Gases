import HRS.MS.QsfStein1
import HRS.MS.FldRemAux1
import HRS.MS.WrQuadAux3

/-!
# S4.5 packet B4, part 2: bounded rows of the commutator kernel, the pair-sum algebra

`s45_Hbounds`: the row integrals `H_μ(x) = ∫ h(x,y) dμ(y)` and `H_ν(x) = ∫ h(x,y) dν(y)` of the commutator kernel of a Lipschitz
field are uniformly bounded, for the thermal `μ` and every `ν = φ_N μ` with `φ_N ≤ C_s` (`S45Static.marg`); they are measurable.
`s45_pairsum_eq`: the pair sum of a symmetric kernel in terms of `centeredPairFunctional`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace S45

open HRS.Whole
open HRS (Euc)

variable {d N : ℕ}

theorem s45_Hbounds (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β C c BU : ℝ}
    (hT : ThermalData d s a β C c BU) {Λ : ℝ≥0} {v : Euc d → Euc d} (hv : LipschitzWith Λ v)
    {φN : Euc d → ℝ} {Cs : ℝ} (hφb : ∀ x, 0 ≤ φN x ∧ φN x ≤ Cs) (hφm : Measurable φN)
    (ν : Measure (Euc d)) (hν : ν = (thermalMeasure d s a β).withDensity
      (fun x => ENNReal.ofReal (φN x))) :
    ∃ Bh : ℝ, 0 ≤ Bh ∧ ∀ x : Euc d,
      |∫ y, commutatorKernel d s v x y ∂(thermalMeasure d s a β)| ≤ Bh ∧
      |∫ y, commutatorKernel d s v x y ∂ν| ≤ Bh := by
  have hd1 : 1 ≤ d := by omega
  have hM : ∀ x, thermalDensity d s a β x ≤ C := fun x => (le_abs_self _).trans
    ((hT.h0 x).trans (by
      have : Real.exp (-c * ‖x‖ ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖x‖, hT.hc])
      nlinarith [hT.C0]))
  obtain ⟨Mρ, hMρ0, hrow⟩ := HRS.MS.S53.s53_rowConst hd1 hs0 hsd hT.prob hM
  have hCs0 : 0 ≤ Cs := (hφb 0).1.trans (hφb 0).2
  have hΛ : (0 : ℝ) ≤ Λ := NNReal.coe_nonneg Λ
  refine ⟨(1 + Cs) * ((s + 1) * (Λ : ℝ) * Mρ), by positivity, fun x => ⟨?_, ?_⟩⟩
  · have := HRS.MS.S53.s53_ker_row_norm hs0 hMρ0 hv hrow x
    rw [Real.norm_eq_abs] at this
    refine this.trans ?_
    have : 0 ≤ (s + 1) * (Λ : ℝ) * Mρ := by positivity
    nlinarith
  · obtain ⟨hi, hb⟩ := HRS.MS.S53.s53_ker_row hs0 hv hrow x
    have hc0 : 0 ≤ (s + 1) * (Λ : ℝ) * Mρ := by positivity
    have hint1 : ∫ y, |commutatorKernel d s v x y| ∂(thermalMeasure d s a β) ≤ (s + 1) * (Λ : ℝ) * Mρ := by
      show ∫ y, |commutatorKernel d s v x y| ∂(withDensityReal (thermalDensity d s a β)) ≤ _
      refine (le_of_eq (by simpa [Real.norm_eq_abs] using
        integral_norm_eq_lintegral_enorm hi.aestronglyMeasurable)).trans
        (ENNReal.toReal_le_of_le_ofReal hc0 hb)
    rw [hν, integral_withDensity_eq_integral_toReal_smul hφm.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    have hmeas : Measurable fun y => commutatorKernel d s v x y :=
      Measurable.of_uncurry_left (f := fun x y => commutatorKernel d s v x y)
        (HRS.MS.Comm.comm_meas (s := s) v hv.continuous.measurable)
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ y, |(ENNReal.ofReal (φN y)).toReal • commutatorKernel d s v x y| ∂(thermalMeasure d s a β)
        ≤ ∫ y, Cs * |commutatorKernel d s v x y| ∂(thermalMeasure d s a β) := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => abs_nonneg _)
            (hi.abs.const_mul Cs) (Filter.Eventually.of_forall fun y => ?_)
          beta_reduce
          rw [smul_eq_mul, abs_mul, ENNReal.toReal_ofReal (hφb y).1, abs_of_nonneg (hφb y).1]
          exact mul_le_mul_of_nonneg_right (hφb y).2 (abs_nonneg _)
      _ = Cs * ∫ y, |commutatorKernel d s v x y| ∂(thermalMeasure d s a β) := integral_const_mul _ _
      _ ≤ _ := by nlinarith

theorem s45_sum_erase_eq {h : Euc d → Euc d → ℝ} (hsym : ∀ x y, h x y = h y x) (X : EucConfig d N) :
    ∑ i, ∑ j ∈ Finset.univ.erase i, h (X i) (X j) =
      2 * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), h (X i) (X j) := by
  have h1 : ∀ i : Fin N, ∑ j ∈ Finset.univ.erase i, h (X i) (X j) =
      ∑ j, (if i < j then h (X i) (X j) else 0) + ∑ j, (if j < i then h (X i) (X j) else 0) := by
    intro i
    rw [← Finset.sum_add_distrib, ← Finset.filter_ne', Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    rcases lt_trichotomy i j with hij | hij | hij
    · simp [hij, hij.ne', not_lt_of_gt hij]
    · simp [hij]
    · simp [hij, hij.ne, not_lt_of_gt hij]
  have h2 : ∑ i, ∑ j, (if j < i then h (X i) (X j) else 0) =
      ∑ i, ∑ j, (if i < j then h (X i) (X j) else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs
    · exact hsym _ _
    · rfl
  simp_rw [h1, Finset.sum_add_distrib, h2, Finset.sum_filter]
  ring

/-- The a.s. algebra: the generator-side random variable `S₁` in terms of the centred statistics. -/
theorem s45_claimA (hN : 1 ≤ N) {h : Euc d → Euc d → ℝ} (hsym : ∀ x y, h x y = h y x)
    {ν : Measure (Euc d)} {Lap w Hm φ : Euc d → ℝ} {β c0 ED : ℝ} (X : EucConfig d N)
    (hstar : ∀ k, Lap (X k) - β * w (X k) - β * Hm (X k) = -β * φ (X k) + c0) :
    (∑ k, Lap (X k)) - β * (∑ k, w (X k)) -
        (β / N) * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), h (X i) (X j) =
      N * (-β * (pair (empirical X) φ - pair ν φ) +
        β * ((pair (empirical X) (fun x => Hm x - ∫ y, h x y ∂ν) -
          pair ν (fun x => Hm x - ∫ y, h x y ∂ν)) -
          (1 / 2) * (centeredPairFunctional h X ν - ED))) +
      N * (c0 - β * pair ν φ + β * pair ν (fun x => Hm x - ∫ y, h x y ∂ν) - (β / 2) * ED +
        (β / 2) * ∫ x, ∫ y, h x y ∂ν ∂ν) := by
  have hN' : 0 < N := hN
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN'.ne'
  have hsum : (∑ k, Lap (X k)) - β * (∑ k, w (X k)) - β * ∑ k, Hm (X k) =
      -β * ∑ k, φ (X k) + N * c0 := by
    have := Finset.sum_congr rfl (fun k (_ : k ∈ (Finset.univ : Finset (Fin N))) => hstar k)
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    linarith
  have hD : centeredPairFunctional h X ν = 1 / (N : ℝ) ^ 2 * (2 * ∑ i, ∑ j ∈ Finset.univ.filter
      (fun j => i < j), h (X i) (X j)) - 2 * (1 / (N : ℝ) * ∑ i, ∫ y, h (X i) y ∂ν) +
      ∫ x, ∫ y, h x y ∂ν ∂ν := by
    unfold centeredPairFunctional
    rw [s45_sum_erase_eq hsym]
  rw [hD]
  simp only [pair_empirical hN', Finset.sum_sub_distrib]
  generalize pair ν φ = pφ
  generalize pair ν (fun x => Hm x - ∫ y, h x y ∂ν) = pH
  generalize (∫ x, ∫ y, h x y ∂ν ∂ν) = IH
  generalize (∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), h (X i) (X j)) = PS
  generalize (∑ k, Lap (X k)) = T1 at *
  generalize (∑ k, w (X k)) = T2 at *
  generalize (∑ k, Hm (X k)) = TH at *
  generalize (∑ k, φ (X k)) = Tφ at *
  generalize (∑ i, ∫ y, h (X i) y ∂ν) = TN at *
  field_simp
  linear_combination 2 * (N : ℝ) * hsum

end S45

end

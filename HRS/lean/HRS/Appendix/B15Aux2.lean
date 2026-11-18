import HRS.Appendix.CepaFlow
import HRS.Energy.Coercivity
import HRS.PDE.MeanFieldKernelD1

/-!
# Packet B15-A0, part 2: the Gibbs reference measure `gibbsRef` is `canonicalGibbs`

`B:eq:particle-total-potential` ff. (TeX M L12004-12019): `gibbsRef D N = Z_G⁻¹ G dX` with
`G = exp(-β_N U_{N,V}) 1_{𝔇_N^c}` and `U = (1/2N) ∑_{i≠j} g(x_i - x_j) + ∑_i V(x_i)`, versus
`canonicalGibbs g V N β` of `Energy/Modulated.lean` with Hamiltonian `∑_i V(x_i) + N⁻¹ ∑_{i<j} g`.
They agree (with `β = invβ⁻¹`) because `g` is even (`1/(2N) ∑_{i≠j} = (1/N) ∑_{i<j}`) and the collision
set is Lebesgue-null.  The partition function `Z_G` is a `lintegral` and `canonicalPartition` a Bochner
integral, so equality needs integrability of `exp(-β H)`, which follows from a lower bound
`g ≥ -B` of the kernel.  For `d ≥ 2` that bound is `periodicRiesz_ge`; for `d = 1`
(`0 ≤ s < 1`) it is `b15_periodicRiesz_ge_d1`, from `periodicRiesz_ge_of_one_le`.  The `_of_lower`
versions take the bound as a hypothesis; all results here are sorry-free.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d N : ℕ}

/-! ### The convention `1/(2N) ∑_{i≠j}` versus `1/N ∑_{i<j}` -/

theorem b15_sum_erase_eq (f : Fin N → Fin N → ℝ) (hf : ∀ i j, f i j = f j i) :
    ∑ i, ∑ j ∈ Finset.univ.erase i, f i j =
      2 * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), f i j := by
  have h1 : ∀ i, ∑ j ∈ Finset.univ.erase i, f i j =
      ∑ j, (if i < j then f i j else 0) + ∑ j, (if j < i then f i j else 0) := by
    intro i
    rw [← Finset.sum_add_distrib, ← Finset.filter_ne' Finset.univ i, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.ne', not_lt.mpr h.le]
    · simp [h]
    · simp [h, h.ne, not_lt.mpr h.le]
  have h2 : ∑ i, ∑ j, (if j < i then f i j else 0) = ∑ i, ∑ j, (if i < j then f i j else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hf]
  simp_rw [h1, Finset.sum_add_distrib, h2, Finset.sum_filter]
  ring

/-- `U_{N,V} = H` pointwise: the total potential of `B:eq:particle-total-potential` is the canonical
Hamiltonian of `H:eq:canonical` for the periodic Riesz kernel (even), with the same junk value `g 0`
at collisions on both sides. -/
theorem b15_totalPotential_eq (D : DynData d) (X : Config d N) :
    totalPotential D X = canonicalHamiltonian (periodicRiesz d D.s) D.V X := by
  unfold totalPotential canonicalHamiltonian
  rw [b15_sum_erase_eq (fun i j => periodicRiesz d D.s (X i - X j)) (fun i j => by
    rw [← periodicRiesz_neg (d := d) (s := D.s) (X i - X j), neg_sub])]
  rw [add_comm]
  congr 1
  rcases N.eq_zero_or_pos with h0 | hN
  · subst h0; simp
  · have : (N : ℝ) ≠ 0 := by positivity
    field_simp

/-! ### Lower bound of the Hamiltonian, integrability and positivity -/

theorem b15_hamiltonian_lower {g V : Torus d → ℝ} {B Vm : ℝ} (hB : 0 ≤ B) (hg : ∀ z, -B ≤ g z)
    (hV : ∀ x, |V x| ≤ Vm) (X : Config d N) :
    -((N : ℝ) * Vm + N * B) ≤ canonicalHamiltonian g V X := by
  unfold canonicalHamiltonian
  have h1 : -((N : ℝ) * Vm) ≤ ∑ i, V (X i) := by
    have : ∑ _i : Fin N, (-Vm) ≤ ∑ i, V (X i) :=
      Finset.sum_le_sum fun i _ => (neg_le_of_abs_le (hV (X i)))
    simpa using this
  rcases N.eq_zero_or_pos with h0 | hN
  · subst h0; simp
  · have hNp : (0 : ℝ) < N := by exact_mod_cast hN
    have h2 : ∀ i : Fin N, -((N : ℝ) * B) ≤ ∑ j ∈ Finset.univ.filter (fun j => i < j), g (X i - X j) := by
      intro i
      have h3 : ∑ _j ∈ Finset.univ.filter (fun j => i < j), (-B) ≤
          ∑ j ∈ Finset.univ.filter (fun j => i < j), g (X i - X j) :=
        Finset.sum_le_sum fun j _ => hg _
      rw [Finset.sum_const, nsmul_eq_mul] at h3
      have h4 : (((Finset.univ.filter (fun j : Fin N => i < j)).card : ℕ) : ℝ) ≤ N := by
        have := Finset.card_filter_le (Finset.univ : Finset (Fin N)) (fun j => i < j)
        simpa using this
      nlinarith
    have h5 : -((N : ℝ) * ((N : ℝ) * B)) ≤ ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), g (X i - X j) := by
      have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h2 i)
      simpa using this
    have h6 : (1 / (N : ℝ)) * (-((N : ℝ) * ((N : ℝ) * B))) =  -((N : ℝ) * B) := by
      field_simp
    have h7 := mul_le_mul_of_nonneg_left h5 (show (0 : ℝ) ≤ 1 / (N : ℝ) by positivity)
    linarith

theorem b15_continuous_of_isCk {V : Torus d → ℝ} (hV : Torus.IsCk 2 V) : Continuous V :=
  KernelGrad.continuous_of_lift (hV.continuous)

theorem b15_bounded_of_continuous {V : Torus d → ℝ} (hV : Continuous V) : ∃ C, ∀ x, |V x| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hV.continuousOn
  exact ⟨C, fun x => by simpa using hC x (mem_univ x)⟩

theorem b15_integrable_exp {g V : Torus d → ℝ} (hgm : Measurable g) (hV : Continuous V)
    {B : ℝ} (hg : ∀ z, -B ≤ g z) (β : ℝ) (hβ : 0 ≤ β) :
    Integrable (fun X : Config d N => Real.exp (-β * canonicalHamiltonian g V X)) := by
  obtain ⟨Vm, hVm⟩ := b15_bounded_of_continuous hV
  set B' := max B 0
  have hB' : ∀ z, -B' ≤ g z := fun z => (neg_le_neg (le_max_left _ _)).trans (hg z)
  have hlow := fun X : Config d N => b15_hamiltonian_lower (le_max_right B 0) hB' hVm X
  have hmeas : Measurable (fun X : Config d N => canonicalHamiltonian g V X) := by
    unfold canonicalHamiltonian
    refine (Finset.measurable_sum _ fun i _ => hV.measurable.comp (measurable_pi_apply i)).add
      (measurable_const.mul (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_))
    exact hgm.comp ((measurable_pi_apply i).sub (measurable_pi_apply j))
  refine Integrable.mono' (integrable_const (Real.exp (β * ((N : ℝ) * Vm + N * B'))))
    (Real.measurable_exp.comp (measurable_const.mul hmeas)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun X => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_exp.mpr ?_
  nlinarith [hlow X]

/-! ### The collision set is Lebesgue-null -/

theorem b15_volume_collisionSet (hd : 1 ≤ d) : (volume : Measure (Config d N)) (collisionSet d N) = 0 := by
  have : collisionSet d N = ⋃ i : Fin N, ⋃ j : Fin N, ⋃ _ : i ≠ j, {X : Config d N | X i - X j = 0} := by
    ext X
    simp [collisionSet, sub_eq_zero]
  rw [this]
  refine measure_iUnion_null fun i => measure_iUnion_null fun j => measure_iUnion_null fun hij => ?_
  have h := (measurePreserving_sub_coord (d := d) (N := N) hij).measure_preimage
    (measurableSet_singleton (0 : Torus d)).nullMeasurableSet
  have e : {X : Config d N | X i - X j = 0} = (fun X : Config d N => X i - X j) ⁻¹' {0} := rfl
  rw [e, h]
  exact volume_singleton_torus hd 0

theorem b15_ae_not_collision (hd : 1 ≤ d) :
    ∀ᵐ X ∂(volume : Measure (Config d N)), X ∉ collisionSet d N :=
  measure_eq_zero_iff_ae_notMem.mp (b15_volume_collisionSet hd)

theorem b15_one_le_d (D : DynData d) : 1 ≤ d := by
  have h : (0 : ℝ) < d := lt_of_le_of_lt D.hs0 D.hsd
  exact_mod_cast h

/-! ### `gibbsRef = canonicalGibbs`, sorry-free given the kernel lower bound -/

/-- The core bridge: if the kernel is bounded below (`g ≥ -B`), `V` is `C²`, `0 < invβ`, then
`gibbsRef D N = canonicalGibbs (periodicRiesz d D.s) D.V N D.invβ⁻¹`, and the partition function
`gibbsPartition D N` is `ofReal` of the (positive, finite) canonical partition. -/
theorem b15_gibbsPartition_eq_of_lower (D : DynData d) {B : ℝ}
    (hB : ∀ z, -B ≤ periodicRiesz d D.s z) (hV : Torus.IsCk 2 D.V) (hβ : 0 < D.invβ) :
    gibbsPartition D N =
        ENNReal.ofReal (canonicalPartition (periodicRiesz d D.s) D.V N D.invβ⁻¹) ∧
      0 < canonicalPartition (periodicRiesz d D.s) D.V N D.invβ⁻¹ := by
  have hd := b15_one_le_d D
  have hVc := b15_continuous_of_isCk hV
  have hgm := CoercAux.measurable_periodicRiesz_one (d := d) (s := D.s) hd D.hs0 D.hsd
  have hint := b15_integrable_exp (N := N) hgm hVc hB D.invβ⁻¹ (inv_nonneg.mpr hβ.le)
  have hae : ∀ᵐ X ∂(volume : Measure (Config d N)),
      gibbsWeight D X = Real.exp (-D.invβ⁻¹ * canonicalHamiltonian (periodicRiesz d D.s) D.V X) := by
    filter_upwards [b15_ae_not_collision (d := d) (N := N) hd] with X hX
    classical
    unfold gibbsWeight
    simp only [hX, ↓reduceIte, b15_totalPotential_eq]
  refine ⟨?_, ?_⟩
  · unfold gibbsPartition canonicalPartition
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun X => (Real.exp_pos _).le)]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with X hX
    rw [hX]
  · unfold canonicalPartition
    refine (integral_pos_iff_support_of_nonneg (fun _ => (Real.exp_pos _).le) hint).mpr ?_
    have : Function.support (fun X : Config d N =>
        Real.exp (-D.invβ⁻¹ * canonicalHamiltonian (periodicRiesz d D.s) D.V X)) = Set.univ := by
      ext X; simp [(Real.exp_pos _).ne']
    rw [this]; simp

theorem b15_gibbsRef_eq_canonicalGibbs_of_lower (D : DynData d) {B : ℝ}
    (hB : ∀ z, -B ≤ periodicRiesz d D.s z) (hV : Torus.IsCk 2 D.V) (hβ : 0 < D.invβ) :
    gibbsRef D N = canonicalGibbs (periodicRiesz d D.s) D.V N D.invβ⁻¹ := by
  have hd := b15_one_le_d D
  obtain ⟨hZ, -⟩ := b15_gibbsPartition_eq_of_lower (N := N) D hB hV hβ
  have hae : ∀ᵐ X ∂(volume : Measure (Config d N)),
      gibbsWeight D X = Real.exp (-D.invβ⁻¹ * canonicalHamiltonian (periodicRiesz d D.s) D.V X) := by
    filter_upwards [b15_ae_not_collision (d := d) (N := N) hd] with X hX
    classical
    unfold gibbsWeight
    simp only [hX, ↓reduceIte, b15_totalPotential_eq]
  unfold gibbsRef canonicalGibbs
  rw [hZ]
  congr 1
  exact withDensity_congr_ae (by filter_upwards [hae] with X hX; rw [hX])

/-- `d = 1` kernel lower bound: the periodic Riesz (`0 < s < 1`) / logarithmic (`s = 0`) kernel on the
circle is bounded below.  `periodicRiesz_ge` (`Energy/Modulated.lean`) assumes `2 ≤ d`; the `d ≥ 1` version
`periodicRiesz_ge_of_one_le` (`PDE/MeanFieldKernelD1.lean`) covers it (found by the packet-C statement review). -/
theorem b15_periodicRiesz_ge_d1 {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    ∃ B : ℝ, ∀ x : Torus 1, -B ≤ periodicRiesz 1 s x :=
  periodicRiesz_ge_of_one_le (d := 1) le_rfl hs0 (by exact_mod_cast hs1)

/-- The kernel lower bound for every `DynData d`: `periodicRiesz_ge` for `d ≥ 2`, the helper
`b15_periodicRiesz_ge_d1` for `d = 1`. -/
theorem b15_periodicRiesz_lower (D : DynData d) : ∃ B : ℝ, ∀ z, -B ≤ periodicRiesz d D.s z := by
  have hd := b15_one_le_d D
  rcases hd.eq_or_lt with h | h
  · subst h
    have h1 : D.s < 1 := by simpa using D.hsd
    exact b15_periodicRiesz_ge_d1 D.hs0 h1
  · exact periodicRiesz_ge (by omega) D.hs0 D.hsd

/-- `gibbsRef D N` is the canonical Gibbs measure `canonicalGibbs g V N β` with `g = periodicRiesz d s`,
`β = invβ⁻¹` (for `0 < invβ`, `V ∈ C²`), so the entropies of B.14/B.15 are relative entropies with respect
to the equilibrium of `H:eq:canonical`.  Depends on the `d = 1` kernel bound `b15_periodicRiesz_ge_d1`
(sorried); the `_of_lower` version is sorry-free. -/
theorem b15_gibbsRef_eq_canonicalGibbs (D : DynData d) (hV : Torus.IsCk 2 D.V) (hβ : 0 < D.invβ) :
    gibbsRef D N = canonicalGibbs (periodicRiesz d D.s) D.V N D.invβ⁻¹ := by
  obtain ⟨B, hB⟩ := b15_periodicRiesz_lower D
  exact b15_gibbsRef_eq_canonicalGibbs_of_lower D hB hV hβ

/-- `0 < Z_G < ∞` for `Z_G = gibbsPartition D N` (the TeX standing convention, L12016). -/
theorem b15_gibbsPartition_pos_lt_top (D : DynData d) (hV : Torus.IsCk 2 D.V) (hβ : 0 < D.invβ) :
    0 < gibbsPartition D N ∧ gibbsPartition D N < ⊤ := by
  obtain ⟨B, hB⟩ := b15_periodicRiesz_lower D
  obtain ⟨hZ, hpos⟩ := b15_gibbsPartition_eq_of_lower (N := N) D hB hV hβ
  rw [hZ]
  exact ⟨ENNReal.ofReal_pos.mpr hpos, ENNReal.ofReal_lt_top⟩

end HRS

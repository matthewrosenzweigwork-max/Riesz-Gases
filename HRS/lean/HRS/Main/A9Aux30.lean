import HRS.Main.A9Aux29

/-!
# Packet A9, part 30: the finite-rank orthogonal projections `P_E` of `NegSobolev d m`

For a finite set `E` of modes: `a9TE E : H →L ℝ^{|E|}` (the coordinates), `a9QE E = id - ι_E ∘ T_E`
(the tail projection).  `‖Q_E‖ ≤ 1`, `‖Q_E x‖² = ‖x‖² - ∑_{j ∈ E} x_j²` and `‖Q_E x‖ → 0` along `E ↑`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.Main.A9

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

open HRS HRS.Main

section Gen

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] {q : ℕ}

theorem a9_proj_sq {b : Fin q → H} (hb : Orthonormal ℝ b) (x : H) :
    ‖x - embedCLM b (hmCoordCLM b x)‖ ^ 2 = ‖x‖ ^ 2 - ‖hmCoordCLM b x‖ ^ 2 := by
  have h1 := norm_embedCLM_apply hb (hmCoordCLM b x)
  have h2 : inner ℝ x (embedCLM b (hmCoordCLM b x)) = ‖hmCoordCLM b x‖ ^ 2 := by
    rw [embedCLM_apply, inner_sum]
    have : ∀ a, inner ℝ x (hmCoordCLM b x a • b a) = (hmCoordCLM b x a) ^ 2 := by
      intro a
      rw [real_inner_smul_right, hmCoordCLM_apply, real_inner_comm]
      ring
    simp_rw [this]
    rw [EuclideanSpace.norm_sq_eq]
    simp [sq_abs]
  rw [norm_sub_sq_real, h2, h1]
  ring

end Gen

section Trunc

variable {d : ℕ} {m : ℝ}

/-- the enumeration of a finite set of modes. -/
def a9kE (E : Finset (NonzeroLattice d)) : Fin E.card → NonzeroLattice d :=
  fun a => ((E.equivFin.symm a : E) : NonzeroLattice d)

theorem a9kE_inj (E : Finset (NonzeroLattice d)) : Function.Injective (a9kE E) :=
  fun _ _ h => E.equivFin.symm.injective (Subtype.ext h)

/-- the coordinates of the modes in `E`. -/
def a9TE (m : ℝ) (E : Finset (NonzeroLattice d)) : NegSobolev d m →L[ℝ] ℝ^E.card :=
  hmCoordCLM (fun a => a9unit m (a9kE E a))

/-- the tail projection `id - ι_E ∘ T_E`. -/
def a9QE (m : ℝ) (E : Finset (NonzeroLattice d)) : NegSobolev d m →L[ℝ] NegSobolev d m :=
  ContinuousLinearMap.id ℝ _ - (embedCLM (fun a => a9unit m (a9kE E a))).comp (a9TE m E)

theorem a9QE_apply (E : Finset (NonzeroLattice d)) (x : NegSobolev d m) :
    a9QE m E x = x - embedCLM (fun a => a9unit m (a9kE E a)) (a9TE m E x) := rfl

theorem a9_normT_sq (E : Finset (NonzeroLattice d)) (x : NegSobolev d m) :
    ‖a9TE m E x‖ ^ 2 = ∑ j ∈ E, NegSobolev.coord x j ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  have : ∀ a : Fin E.card, ‖a9TE m E x a‖ ^ 2 = NegSobolev.coord x (a9kE E a) ^ 2 := by
    intro a
    rw [a9TE, a9_coordCLM_apply, Real.norm_eq_abs, sq_abs]
  simp_rw [this]
  have h := Equiv.sum_comp E.equivFin.symm (fun j : E => NegSobolev.coord x j ^ 2)
  rw [Finset.sum_coe_sort E (fun j => NegSobolev.coord x j ^ 2)] at h
  exact h

theorem a9QE_norm_sq (E : Finset (NonzeroLattice d)) (x : NegSobolev d m) :
    ‖a9QE m E x‖ ^ 2 = ‖x‖ ^ 2 - ∑ j ∈ E, NegSobolev.coord x j ^ 2 := by
  rw [a9QE_apply, a9TE, a9_proj_sq (a9unit_orthonormal (a9kE_inj E)) x]
  rw [← a9TE, a9_normT_sq]

theorem a9QE_norm_le (E : Finset (NonzeroLattice d)) (x : NegSobolev d m) :
    ‖a9QE m E x‖ ≤ ‖x‖ := by
  have h : ‖a9QE m E x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [a9QE_norm_sq]
    have := Finset.sum_nonneg (s := E) (fun j _ => sq_nonneg (NegSobolev.coord x j))
    linarith
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

theorem a9QE_opNorm_le (E : Finset (NonzeroLattice d)) : ‖(a9QE m E : NegSobolev d m →L[ℝ] NegSobolev d m)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [one_mul]; exact a9QE_norm_le E x

theorem a9QE_tendsto (x : NegSobolev d m) :
    Tendsto (fun E : Finset (NonzeroLattice d) => ‖a9QE m E x‖) atTop (𝓝 0) := by
  obtain ⟨hs, hn⟩ := NegSobolev.coord_sq x
  have h1 : Tendsto (fun E : Finset (NonzeroLattice d) => ∑ j ∈ E, NegSobolev.coord x j ^ 2) atTop
      (𝓝 (∑' j, NegSobolev.coord x j ^ 2)) := hs.hasSum
  have h2 : Tendsto (fun E : Finset (NonzeroLattice d) => ‖x‖ ^ 2 - ∑ j ∈ E, NegSobolev.coord x j ^ 2)
      atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := ‖x‖ ^ 2)).sub h1
    rw [show ‖x‖ ^ 2 - ∑' j, NegSobolev.coord x j ^ 2 = 0 from sub_eq_zero.2 hn] at this
    exact this
  have h3 := (Real.continuous_sqrt.tendsto 0).comp h2
  rw [Real.sqrt_zero] at h3
  refine h3.congr fun E => ?_
  simp only [Function.comp]
  rw [← a9QE_norm_sq, Real.sqrt_sq (norm_nonneg _)]

end Trunc

end HRS.Main.A9

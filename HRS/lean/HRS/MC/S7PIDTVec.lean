import HRS.MC.S7PIDIIncr
import HRS.MC.S7PIDDefs

/-!
# Packet PI-D, sub-packet T (part 1): the finite-dimensional coordinates of the truncation `Π_F`

`truncF m F` is the orthogonal projection of `E_m` onto the finite-dimensional span of the modes of `F`.
We record: `‖Π_F a - Π_F b‖ ≤ ‖a - b‖`, and an isometric coordinate system `ℝ^r ≅ range Π_F` (`emb`, `crd`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIDT

open HRS HRS.Sec7 HRS.MC.Sec7.PID

variable {d : ℕ}

lemma S7PIDT_memℓp_trunc (m : ℝ) (F : Finset (NonzeroLattice d)) (v : NegSobolev d m) :
    Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) *
      (if k ∈ F then NegSobolev.fourierCoeff v k else 0)) 2 := by
  rw [Torus.memℓp_two_iff]
  refine summable_of_ne_finset_zero (s := F) fun j hj => ?_
  simp [hj]

lemma S7PIDT_coord_trunc (m : ℝ) (F : Finset (NonzeroLattice d)) (v : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.coord (truncF m F v) k = if k ∈ F then NegSobolev.coord v k else 0 := by
  unfold truncF
  rw [NegSobolev.coord_ofSeq_of_mem _ (S7PIDT_memℓp_trunc m F v) k]
  by_cases hk : k ∈ F
  · simp only [hk, ite_true]
    unfold NegSobolev.fourierCoeff
    rw [← mul_assoc, ← Real.rpow_add (Torus.jp_pos k.1)]
    simp
  · simp [hk]

lemma S7PIDT_coord_sub (m : ℝ) (a b : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.coord (a - b) k = NegSobolev.coord a k - NegSobolev.coord b k := rfl

/-- `Π_F` is `1`-Lipschitz -/
lemma S7PIDT_trunc_sub_le (m : ℝ) (F : Finset (NonzeroLattice d)) (a b : NegSobolev d m) :
    ‖truncF m F a - truncF m F b‖ ≤ ‖a - b‖ := by
  obtain ⟨h1, h2⟩ := NegSobolev.coord_sq (truncF m F a - truncF m F b)
  obtain ⟨h3, h4⟩ := NegSobolev.coord_sq (a - b)
  have hle : ‖truncF m F a - truncF m F b‖ ^ 2 ≤ ‖a - b‖ ^ 2 := by
    rw [h2, h4]
    refine Summable.tsum_le_tsum (fun k => ?_) h1 h3
    rw [S7PIDT_coord_sub, S7PIDT_coord_sub, S7PIDT_coord_trunc, S7PIDT_coord_trunc]
    by_cases hk : k ∈ F
    · simp [hk]
    · simp [hk]; positivity
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hle

lemma S7PIDT_coord_mode (m : ℝ) (k j : NonzeroLattice d) :
    NegSobolev.coord (modeVec m k) j = if j = k then Lattice.jp j.1 ^ (-m) else 0 := by
  unfold modeVec
  rw [NegSobolev.coord_ofSeq_of_mem _ (S7PIDI.S7PIDI_memℓp_mode m k) j]
  by_cases h : j = k <;> simp [h]

/-- `Π_F v` is a combination of the modes of `F` -/
lemma S7PIDT_trunc_eq_sum (m : ℝ) (F : Finset (NonzeroLattice d)) (v : NegSobolev d m) :
    truncF m F v = ∑ k ∈ F, NegSobolev.fourierCoeff v k • modeVec m k := by
  refine HRS.MC.Sec7.PIE.pie_ext _ _ fun j => ?_
  rw [S7PIDT_coord_trunc]
  have e : NegSobolev.coord (∑ k ∈ F, NegSobolev.fourierCoeff v k • modeVec m k) j =
      ∑ k ∈ F, NegSobolev.fourierCoeff v k * NegSobolev.coord (modeVec m k) j := by
    induction F using Finset.induction_on with
    | empty => rfl
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha]; exact congrArg₂ (· + ·) rfl ih
  rw [e]
  simp_rw [S7PIDT_coord_mode]
  by_cases hj : j ∈ F
  · rw [Finset.sum_eq_single j]
    · simp only [hj, ite_true]
      unfold NegSobolev.fourierCoeff
      rw [mul_right_comm, mul_comm _ (NegSobolev.coord v j), ← Real.rpow_add (Torus.jp_pos j.1)]
      simp
    · intro b _ hb
      simp [Ne.symm hb]
    · intro h; exact absurd hj h
  · simp only [hj, ite_false]
    refine (Finset.sum_eq_zero fun k hk => ?_).symm
    have : j ≠ k := fun h => hj (h ▸ hk)
    simp [this]

/-- the finite-dimensional range of `Π_F` -/
def S7PIDT_range (m : ℝ) (F : Finset (NonzeroLattice d)) : Submodule ℝ (NegSobolev d m) :=
  Submodule.span ℝ (modeVec m '' (F : Set (NonzeroLattice d)))

lemma S7PIDT_trunc_mem (m : ℝ) (F : Finset (NonzeroLattice d)) (v : NegSobolev d m) :
    truncF m F v ∈ S7PIDT_range m F := by
  rw [S7PIDT_trunc_eq_sum]
  exact Submodule.sum_mem _ fun k hk =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, rfl⟩)

instance S7PIDT_range_fd (m : ℝ) (F : Finset (NonzeroLattice d)) : FiniteDimensional ℝ (S7PIDT_range m F) :=
  FiniteDimensional.span_of_finite ℝ (Set.Finite.image _ F.finite_toSet)

/-- isometric coordinates of the range of `Π_F` -/
theorem S7PIDT_vec (m : ℝ) (F : Finset (NonzeroLattice d)) :
    ∃ (r : ℕ) (emb : EuclideanSpace ℝ (Fin r) →L[ℝ] NegSobolev d m)
      (crd : NegSobolev d m →L[ℝ] EuclideanSpace ℝ (Fin r)),
      (∀ y, ‖emb y‖ ≤ ‖y‖) ∧ (∀ x, ‖crd x‖ ≤ ‖x‖) ∧ ∀ x, emb (crd (truncF m F x)) = truncF m F x := by
  let S := S7PIDT_range m F
  let b := stdOrthonormalBasis ℝ S
  refine ⟨Module.finrank ℝ S,
    S.subtypeL.comp b.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap,
    b.repr.toContinuousLinearEquiv.toContinuousLinearMap.comp S.orthogonalProjectionOnto, ?_, ?_, ?_⟩
  · intro y
    exact le_of_eq (b.repr.symm.norm_map y)
  · intro x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.norm_map]
    exact Submodule.norm_orthogonalProjectionOnto_apply_le S x
  · intro x
    have hx := S7PIDT_trunc_mem m F x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.symm_apply_apply,
      Submodule.subtypeL_apply]
    have := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (K := S) ⟨truncF m F x, hx⟩
    rw [show S.orthogonalProjectionOnto (truncF m F x) = S.orthogonalProjectionOnto ((⟨truncF m F x, hx⟩ : S) : NegSobolev d m) from rfl, this]

lemma S7PIDT_trunc_zero (m : ℝ) (F : Finset (NonzeroLattice d)) : truncF m F (0 : NegSobolev d m) = 0 := by
  refine HRS.MC.Sec7.PIE.pie_ext _ _ fun k => ?_
  rw [S7PIDT_coord_trunc]
  by_cases hk : k ∈ F <;> simp [hk] <;> rfl

lemma S7PIDT_trunc_norm_le (m : ℝ) (F : Finset (NonzeroLattice d)) (a : NegSobolev d m) :
    ‖truncF m F a‖ ≤ ‖a‖ := by
  have := S7PIDT_trunc_sub_le m F a 0
  rwa [S7PIDT_trunc_zero, sub_zero, sub_zero] at this

/-- the coordinate map `G = crd ∘ Π_F` with the embedding back to `E_m` -/
theorem S7PIDT_vec' (m : ℝ) (F : Finset (NonzeroLattice d)) :
    ∃ (r : ℕ) (emb : EuclideanSpace ℝ (Fin r) →L[ℝ] NegSobolev d m) (G : NegSobolev d m → EuclideanSpace ℝ (Fin r)),
      (∀ y, ‖emb y‖ ≤ ‖y‖) ∧ (∀ a b, ‖G a - G b‖ ≤ ‖a - b‖) ∧ (∀ a, ‖G a‖ ≤ ‖a‖) ∧ Continuous G ∧
        ∀ a, emb (G a) = truncF m F a := by
  obtain ⟨r, emb, crd, h1, h2, h3⟩ := S7PIDT_vec m F
  refine ⟨r, emb, fun a => crd (truncF m F a), h1, fun a b => ?_, fun a => ?_, ?_, h3⟩
  · rw [← map_sub]
    exact (h2 _).trans (S7PIDT_trunc_sub_le m F a b)
  · exact (h2 _).trans (S7PIDT_trunc_norm_le m F a)
  · have : LipschitzWith 1 (fun a : NegSobolev d m => truncF m F a) :=
      LipschitzWith.of_dist_le_mul fun a b => by
        rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
        exact S7PIDT_trunc_sub_le m F a b
    exact crd.continuous.comp this.continuous

end HRS.MC.Sec7.S7PIDT

end

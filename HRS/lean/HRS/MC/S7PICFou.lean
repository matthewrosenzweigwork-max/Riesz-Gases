import HRS.MC.S7PICAlg
import HRS.Equilibrium.FieldSingAux

/-!
# PI-C, part 2: Fourier-coefficient functionals and the finite-box decomposition of `Π_L`

`ℓ_{t,k}(w) = F̂(w(t))(k) = ⟨w(t), e_k⟩` is the evaluation functional `l_{t,φ}` with `φ = realMode k` (smooth), and
`Π_L F = ∑_{|k|≤L} F̂(k) • E_k` is a finite sum.
-/

noncomputable section

open Filter Topology

namespace HRS.MC.Sec7.S7PIC

open HRS HRS.Sec7

variable {d : ℕ} {m T : ℝ}

/-- The frequency box `{k ≠ 0 : |k_i| ≤ L}` is finite. -/
theorem S7PIC_box_finite (d L : ℕ) :
    {k : NonzeroLattice d | ∀ i, |k.1 i| ≤ (L : ℤ)}.Finite := by
  classical
  have h : ((fun k : NonzeroLattice d => k.1) '' {k : NonzeroLattice d | ∀ i, |k.1 i| ≤ (L : ℤ)}).Finite := by
    refine (Set.finite_Icc (fun _ : Fin d => -(L : ℤ)) (fun _ => (L : ℤ))).subset ?_
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨fun i => (abs_le.1 (hk i)).1, fun i => (abs_le.1 (hk i)).2⟩
  exact Set.Finite.of_finite_image h (Subtype.val_injective.injOn)

/-- The finite frequency box as a `Finset`. -/
def S7PIC_box (d L : ℕ) : Finset (NonzeroLattice d) := (S7PIC_box_finite d L).toFinset

theorem S7PIC_mem_box {L : ℕ} {k : NonzeroLattice d} : k ∈ S7PIC_box d L ↔ ∀ i, |k.1 i| ≤ (L : ℤ) := by
  simp [S7PIC_box]

theorem S7PIC_abs_coord_le (F : NegSobolev d m) (k : NonzeroLattice d) : |NegSobolev.coord F k| ≤ ‖F‖ := by
  obtain ⟨hs, hn⟩ := NegSobolev.coord_sq F
  have h1 : NegSobolev.coord F k ^ 2 ≤ ∑' j, NegSobolev.coord F j ^ 2 :=
    hs.le_tsum k (fun j _ => sq_nonneg _)
  rw [← hn] at h1
  exact abs_le_of_sq_le_sq' (by simpa using h1) (norm_nonneg _) |> fun h => abs_le.2 h

/-- The Fourier coefficient `F ↦ F̂(k)` as a continuous linear functional on `E_m`. -/
def S7PIC_coef (m : ℝ) (k : NonzeroLattice d) : NegSobolev d m →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun F => NegSobolev.fourierCoeff F k
      map_add' := fun F G => by
        unfold NegSobolev.fourierCoeff
        rw [q17_coord_add, mul_add]
      map_smul' := fun c F => by
        unfold NegSobolev.fourierCoeff
        have h1 : NegSobolev.coord (c • F) k = c * NegSobolev.coord F k := by
          unfold NegSobolev.coord; rfl
        rw [h1]
        simp only [RingHom.id_apply, smul_eq_mul]
        ring }
    (Lattice.jp k.1 ^ m) (fun F => by
      show |Lattice.jp k.1 ^ m * NegSobolev.coord F k| ≤ _
      rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos (Torus.jp_pos k.1) m)]
      exact mul_le_mul_of_nonneg_left (S7PIC_abs_coord_le F k) (Real.rpow_pos_of_pos (Torus.jp_pos k.1) m).le)

theorem S7PIC_coef_apply (F : NegSobolev d m) (k : NonzeroLattice d) :
    S7PIC_coef m k F = NegSobolev.fourierCoeff F k := rfl

/-- Evaluation of a path at a time `t ∈ [0,T]`, as a continuous linear map. -/
def S7PIC_ev (m T : ℝ) (t : Set.Icc (0 : ℝ) T) : PathSpace d m T →L[ℝ] NegSobolev d m :=
  LinearMap.mkContinuous
    { toFun := fun w => PathSpace.at' w t
      map_add' := fun w₁ w₂ => rfl
      map_smul' := fun c w => rfl } 1 (fun w => by
      rw [one_mul]
      exact ContinuousMap.norm_coe_le_norm (show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from w) t)

theorem S7PIC_ev_apply (t : Set.Icc (0 : ℝ) T) (w : PathSpace d m T) :
    S7PIC_ev m T t w = PathSpace.at' w t := rfl

/-- The evaluation functional `ℓ_{t,k}(w) = ⟨w(t), e_k⟩` on the path space. -/
def S7PIC_lf (m T : ℝ) (t : Set.Icc (0 : ℝ) T) (k : NonzeroLattice d) : StrongDual ℝ (PathSpace d m T) :=
  (S7PIC_coef m k).comp (S7PIC_ev m T t)

theorem S7PIC_lf_apply (t : Set.Icc (0 : ℝ) T) (k : NonzeroLattice d) (w : PathSpace d m T) :
    S7PIC_lf m T t k w = NegSobolev.fourierCoeff (PathSpace.at' w t) k := rfl

theorem S7PIC_funRealCoeff_realMode (k j : NonzeroLattice d) :
    Torus.funRealCoeff (Torus.realMode k : Torus d → ℝ) j = if j = k then 1 else 0 := by
  unfold Torus.funRealCoeff
  rw [Torus.realMode_orthonormal j k]

theorem S7PIC_eval_realMode (F : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.eval F (Torus.realMode k) = NegSobolev.fourierCoeff F k := by
  unfold NegSobolev.eval
  simp_rw [S7PIC_funRealCoeff_realMode k]
  rw [tsum_eq_single k]
  · simp
  · intro j hj; simp [hj]

theorem S7PIC_lf_eq_eval (t : Set.Icc (0 : ℝ) T) (k : NonzeroLattice d) (w : PathSpace d m T) :
    S7PIC_lf m T t k w = NegSobolev.eval (pathAt w (t : ℝ)) (Torus.realMode k) := by
  rw [S7PIC_eval_realMode, S7PIC_lf_apply]
  unfold pathAt
  rw [dif_pos t.2]

/-- The basis vector `E_k ∈ E_m` with `coord E_k = jp(k)^{-m} δ_k`, i.e. `F̂(E_k) = δ_k`. -/
def S7PIC_E (m : ℝ) (k : NonzeroLattice d) : NegSobolev d m :=
  (show NegSobolev d m from lp.single (E := fun _ : NonzeroLattice d => ℝ) 2 k (Lattice.jp k.1 ^ (-m)))

theorem S7PIC_coord_E (k j : NonzeroLattice d) :
    NegSobolev.coord (S7PIC_E m k) j = if j = k then Lattice.jp k.1 ^ (-m) else 0 := by
  unfold NegSobolev.coord S7PIC_E
  rw [lp.single_apply]
  by_cases h : j = k
  · subst h; simp
  · simp [h]

theorem S7PIC_coord_sum (s : Finset (NonzeroLattice d)) (f : NonzeroLattice d → NegSobolev d m)
    (j : NonzeroLattice d) :
    NegSobolev.coord (∑ k ∈ s, f k) j = ∑ k ∈ s, NegSobolev.coord (f k) j := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, q17_coord_add, ih, Finset.sum_insert ha]

theorem S7PIC_coord_smul (c : ℝ) (F : NegSobolev d m) (j : NonzeroLattice d) :
    NegSobolev.coord (c • F) j = c * NegSobolev.coord F j := by
  unfold NegSobolev.coord; rfl

/-- `Π_L F = ∑_{|k|≤L} F̂(k) E_k`. -/
theorem S7PIC_fourierProj_eq_sum (L : ℕ) (F : NegSobolev d m) :
    fourierProj m L F = ∑ k ∈ S7PIC_box d L, NegSobolev.fourierCoeff F k • S7PIC_E m k := by
  classical
  apply q17_ext
  intro j
  rw [q17_coord_fourierProj, S7PIC_coord_sum]
  simp_rw [S7PIC_coord_smul, S7PIC_coord_E]
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq (S7PIC_box d L) j]
  by_cases h : j ∈ S7PIC_box d L
  · rw [if_pos h, q17_ind, if_pos (S7PIC_mem_box.1 h)]
    unfold NegSobolev.fourierCoeff
    have h2 : Lattice.jp j.1 ^ m * Lattice.jp j.1 ^ (-m) = 1 := by
      rw [← Real.rpow_add (Torus.jp_pos j.1), add_neg_cancel, Real.rpow_zero]
    rw [one_mul, mul_right_comm, h2, one_mul]
  · rw [if_neg h, q17_ind, if_neg (fun h' => h (S7PIC_mem_box.2 h')), zero_mul]

end HRS.MC.Sec7.S7PIC

import HRS.MS.TransOpAux8

/-!
# S611 packet P2b: the bounded operator `O_c` on `OscSpace d m`

`s611_O m hm c : OscSpace d m →L[ℝ] OscSpace d m`, `‖O_c‖ ≤ s611_K m c`, and `O_c (ofFun φ) = ofFun (φ(· + c))` for `φ ∈ Σ^m`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.TransOp

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

/-- The `L²` class with Hermite coefficients `hermiteCoeff w`. -/
def s611_F (m : ℕ) (w : OscSpace d (m : ℝ)) : Lp ℝ 2 (volume : Measure (Euc d)) :=
  (s611_basis d).repr.symm
    ⟨fun α => OscSpace.hermiteCoeff w α, OscSpace.memℓp_hermiteCoeff (Nat.cast_nonneg m) w⟩

theorem s611_inner_F (m : ℕ) (w : OscSpace d (m : ℝ)) (α : MultiIndex d) :
    inner ℝ (hermiteLpD α) (s611_F m w) = OscSpace.hermiteCoeff w α := by
  rw [← s611_basis_apply, ← HilbertBasis.repr_apply_apply]
  unfold s611_F
  simp

theorem s611_coord_add (m : ℕ) (w w' : OscSpace d (m : ℝ)) (α : MultiIndex d) :
    OscSpace.coord (w + w') α = OscSpace.coord w α + OscSpace.coord w' α := by
  show (((show lp (fun _ : MultiIndex d => ℝ) 2 from w) +
    (show lp (fun _ : MultiIndex d => ℝ) 2 from w') : lp (fun _ : MultiIndex d => ℝ) 2)) α = _
  rw [lp.coeFn_add]; rfl

theorem s611_coord_smul (m : ℕ) (a : ℝ) (w : OscSpace d (m : ℝ)) (α : MultiIndex d) :
    OscSpace.coord (a • w) α = a * OscSpace.coord w α := by
  show ((a • (show lp (fun _ : MultiIndex d => ℝ) 2 from w) : lp (fun _ : MultiIndex d => ℝ) 2)) α = _
  rw [lp.coeFn_smul]; rfl

theorem s611_hermiteCoeff_add (m : ℕ) (w w' : OscSpace d (m : ℝ)) (α : MultiIndex d) :
    OscSpace.hermiteCoeff (w + w') α = OscSpace.hermiteCoeff w α + OscSpace.hermiteCoeff w' α := by
  unfold OscSpace.hermiteCoeff
  rw [s611_coord_add]; ring

theorem s611_hermiteCoeff_smul (m : ℕ) (a : ℝ) (w : OscSpace d (m : ℝ)) (α : MultiIndex d) :
    OscSpace.hermiteCoeff (a • w) α = a * OscSpace.hermiteCoeff w α := by
  unfold OscSpace.hermiteCoeff
  rw [s611_coord_smul]; ring

theorem s611_F_add (m : ℕ) (w w' : OscSpace d (m : ℝ)) : s611_F m (w + w') = s611_F m w + s611_F m w' := by
  unfold s611_F
  rw [← map_add]
  congr 1
  refine lp.ext (funext fun α => ?_)
  show OscSpace.hermiteCoeff (w + w') α = OscSpace.hermiteCoeff w α + OscSpace.hermiteCoeff w' α
  exact s611_hermiteCoeff_add m w w' α

theorem s611_F_smul (m : ℕ) (a : ℝ) (w : OscSpace d (m : ℝ)) : s611_F m (a • w) = a • s611_F m w := by
  unfold s611_F
  rw [← map_smul]
  congr 1
  refine lp.ext (funext fun α => ?_)
  show OscSpace.hermiteCoeff (a • w) α = a * OscSpace.hermiteCoeff w α
  exact s611_hermiteCoeff_smul m a w α

theorem s611_w_hermiteCoeff_sq (m : ℕ) (w : OscSpace d (m : ℝ)) (α : MultiIndex d) :
    s611_w d m α * OscSpace.hermiteCoeff w α ^ 2 = OscSpace.coord w α ^ 2 := by
  rw [OscSpace.coord_eq_mul, mul_pow, rpow_half_sq _ _ (oscEv_pos α), Real.rpow_natCast]
  rfl

theorem s611_summable_F (m : ℕ) (w : OscSpace d (m : ℝ)) :
    Summable (fun α => s611_w d m α * (inner ℝ (hermiteLpD α) (s611_F m w)) ^ 2) := by
  simp only [s611_inner_F]
  exact (lp_two_summable (ι := MultiIndex d) w).congr fun α => (s611_w_hermiteCoeff_sq m w α).symm

/-- The weighted coordinates of `O_c w`. -/
def s611_Ocoef (m : ℕ) (c : Euc d) (w : OscSpace d (m : ℝ)) (β : MultiIndex d) : ℝ :=
  oscEigenvalue d β ^ ((m : ℝ) / 2) * inner ℝ (hermiteLpD β) (s611_U c (s611_F m w))

theorem s611_Ocoef_sq (m : ℕ) (c : Euc d) (w : OscSpace d (m : ℝ)) (β : MultiIndex d) :
    s611_Ocoef m c w β ^ 2 =
      s611_w d m β * (inner ℝ (hermiteLpD β) (s611_U c (s611_F m w))) ^ 2 := by
  unfold s611_Ocoef s611_w
  rw [mul_pow, rpow_half_sq _ _ (oscEv_pos β), Real.rpow_natCast]

theorem s611_Omem (m : ℕ) (hm : 1 ≤ m) (c : Euc d) (w : OscSpace d (m : ℝ)) :
    Memℓp (s611_Ocoef m c w) 2 := by
  rw [memℓp_two_iff]
  have := (s611_U_bound m hm c (s611_F m w) (s611_summable_F m w)).1
  exact this.congr fun β => (s611_Ocoef_sq m c w β).symm

theorem s611_Ocoef_tsum_le (m : ℕ) (hm : 1 ≤ m) (c : Euc d) (w : OscSpace d (m : ℝ)) :
    ∑' β, s611_Ocoef m c w β ^ 2 ≤ s611_K m c ^ 2 * ‖w‖ ^ 2 := by
  have h := (s611_U_bound m hm c (s611_F m w) (s611_summable_F m w)).2
  have e1 : ∑' β, s611_Ocoef m c w β ^ 2 =
      ∑' β, s611_w d m β * (inner ℝ (hermiteLpD β) (s611_U c (s611_F m w))) ^ 2 :=
    tsum_congr fun β => s611_Ocoef_sq m c w β
  have e2 : ∑' α, s611_w d m α * (inner ℝ (hermiteLpD α) (s611_F m w)) ^ 2 = ‖w‖ ^ 2 := by
    simp only [s611_inner_F]
    rw [tsum_congr fun α => s611_w_hermiteCoeff_sq m w α]
    exact (lp_two_norm_sq (ι := MultiIndex d) w).symm
  rw [e1]
  rwa [e2] at h

/-- The element `O_c w` of the sequence model. -/
def s611_Oel (m : ℕ) (hm : 1 ≤ m) (c : Euc d) (w : OscSpace d (m : ℝ)) : OscSpace d (m : ℝ) :=
  (⟨s611_Ocoef m c w, s611_Omem m hm c w⟩ : lp (fun _ : MultiIndex d => ℝ) 2)

theorem s611_Oel_coord (m : ℕ) (hm : 1 ≤ m) (c : Euc d) (w : OscSpace d (m : ℝ)) (β : MultiIndex d) :
    OscSpace.coord (s611_Oel m hm c w) β = s611_Ocoef m c w β := rfl

/-- `O_c` as a linear map. -/
def s611_Olin (m : ℕ) (hm : 1 ≤ m) (c : Euc d) :
    OscSpace d (m : ℝ) →ₗ[ℝ] OscSpace d (m : ℝ) where
  toFun := s611_Oel m hm c
  map_add' w w' := by
    refine lp.ext (funext fun β => ?_)
    have h1 : OscSpace.coord (s611_Oel m hm c (w + w')) β = s611_Ocoef m c (w + w') β := rfl
    have h2 : OscSpace.coord (s611_Oel m hm c w + s611_Oel m hm c w') β =
        s611_Ocoef m c w β + s611_Ocoef m c w' β := by
      rw [s611_coord_add]; rfl
    have h3 : s611_Ocoef m c (w + w') β = s611_Ocoef m c w β + s611_Ocoef m c w' β := by
      unfold s611_Ocoef
      rw [s611_F_add, map_add, inner_add_right, mul_add]
    exact h1.trans (h3.trans h2.symm)
  map_smul' a w := by
    refine lp.ext (funext fun β => ?_)
    have h1 : OscSpace.coord (s611_Oel m hm c (a • w)) β = s611_Ocoef m c (a • w) β := rfl
    have h2 : OscSpace.coord ((RingHom.id ℝ) a • s611_Oel m hm c w) β = a * s611_Ocoef m c w β := by
      rw [RingHom.id_apply, s611_coord_smul]; rfl
    have h3 : s611_Ocoef m c (a • w) β = a * s611_Ocoef m c w β := by
      unfold s611_Ocoef
      rw [s611_F_smul, map_smul, inner_smul_right]
      ring
    exact h1.trans (h3.trans h2.symm)

theorem s611_norm_Oel_le (m : ℕ) (hm : 1 ≤ m) (c : Euc d) (w : OscSpace d (m : ℝ)) :
    ‖s611_Oel m hm c w‖ ≤ s611_K m c * ‖w‖ := by
  rw [OscSpace.norm_eq_coord]
  have h := s611_Ocoef_tsum_le m hm c w
  calc Real.sqrt (∑' β, OscSpace.coord (s611_Oel m hm c w) β ^ 2)
      ≤ Real.sqrt (s611_K m c ^ 2 * ‖w‖ ^ 2) := Real.sqrt_le_sqrt h
    _ = s611_K m c * ‖w‖ := by
        rw [← mul_pow, Real.sqrt_sq (mul_nonneg (s611_K_pos m c).le (norm_nonneg _))]

/-- The bounded operator `O_c` on `Σ^m` (sequence model): translation `φ ↦ φ(· + c)`. -/
def s611_O (m : ℕ) (hm : 1 ≤ m) (c : Euc d) : OscSpace d (m : ℝ) →L[ℝ] OscSpace d (m : ℝ) :=
  LinearMap.mkContinuous (s611_Olin m hm c) (s611_K m c) (s611_norm_Oel_le m hm c)

theorem s611_O_apply (m : ℕ) (hm : 1 ≤ m) (c : Euc d) (w : OscSpace d (m : ℝ)) :
    s611_O m hm c w = s611_Oel m hm c w := rfl

theorem s611_norm_O_le (m : ℕ) (hm : 1 ≤ m) (c : Euc d) : ‖s611_O m hm c‖ ≤ s611_K m c :=
  LinearMap.mkContinuous_norm_le _ (s611_K_pos m c).le _

/-- Intertwining with translation of `Σ^m` functions. -/
theorem s611_O_ofFun (m : ℕ) (hm : 1 ≤ m) (c : Euc d) {φ : Euc d → ℝ} (hφ : MemOsc (m : ℝ) φ)
    (hφc : MemOsc (m : ℝ) (fun x => φ (x + c))) :
    s611_O m hm c (OscSpace.ofFun (m : ℝ) φ) = OscSpace.ofFun (m : ℝ) (fun x => φ (x + c)) := by
  refine lp.ext (funext fun β => ?_)
  have h1 : OscSpace.coord (s611_O m hm c (OscSpace.ofFun (m : ℝ) φ)) β =
      s611_Ocoef m c (OscSpace.ofFun (m : ℝ) φ) β := rfl
  show OscSpace.coord (s611_O m hm c (OscSpace.ofFun (m : ℝ) φ)) β =
    OscSpace.coord (OscSpace.ofFun (m : ℝ) (fun x => φ (x + c))) β
  rw [h1, OscSpace.coord_ofFun _ hφc]
  unfold s611_Ocoef
  congr 1
  have hF : s611_F m (OscSpace.ofFun (m : ℝ) φ) = hφ.1.toLp φ := by
    refine (s611_basis d).repr.injective (lp.ext (funext fun α => ?_))
    rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply, s611_basis_apply, s611_inner_F,
      s611_inner_toLp]
    exact OscSpace.hermiteCoeff_ofFun hφ α
  rw [hF, s611_U_toLp, s611_inner_toLp]

end HRS.MS.TransOp

end

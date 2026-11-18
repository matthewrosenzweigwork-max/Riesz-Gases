import HRS.MS.S111K2B04d

/-!
# S11.1 continuation, B04 (part 5): the orbit layer

For `v ≤ t`, `F = U(v,t)φ_α` is `C^{r+1}`, qualitatively bounded, with `‖D^jF‖ ≤ b_α e^{-c_0(t-v)}` for `1 ≤ j ≤ r+1`
(`s111k2_orbit_data`, from the S10.3/E04/E07 input).  For `η = z^v` with zero mass: `η F = η (F - F(0))`
(`s111k2_zero`), the coordinate bound `|η F| ≤ ‖η‖ c_E A` (`s111k2_coord_bound`), the `ℓ²` norm and the continuity in the
terminal time of the coordinate vector `(z^v(U(v,s)φ_α))_α`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K2

open HRS HRS.Whole HRS.MS.Go HRS.MS.CovMeas HRS.MS.R2WinErr HRS.MS.FixEq

variable {d : ℕ}

lemma s111k2_norm_iter_gradient (G : Euc d → ℝ) (j : ℕ) (x : Euc d) :
    ‖iteratedFDeriv ℝ j (fun y => gradient G y) x‖ = ‖iteratedFDeriv ℝ (j + 1) G x‖ := by
  have : (fun y => gradient G y) =
      ((InnerProductSpace.toDual ℝ (Euc d)).symm : _ ≃ₗᵢ[ℝ] _) ∘ fderiv ℝ G := rfl
  rw [this, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left, norm_iteratedFDeriv_fderiv]

lemma s111k2_orbit_data {C : WholeCoeff d} {m c0 : ℝ} {r : ℕ} {b : MultiIndex d → ℝ}
    (hW : S111k2WindowOrbitInput C m c0 r b) (α : MultiIndex d) {v t : ℝ}
    (hv : 0 ≤ v) (hvt : v ≤ t) :
    ContDiff ℝ ((r + 1 : ℕ) : WithTop ℕ∞) (propagatorW C v t (oscTestFun m α)) ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ r + 1 → ∀ x,
      ‖iteratedFDeriv ℝ j (propagatorW C v t (oscTestFun m α)) x‖ ≤ b α * Real.exp (-c0 * (t - v))) ∧
    ∃ B0 : ℝ, ∀ x, |propagatorW C v t (oscTestFun m α) x| ≤ B0 := by
  have ht0 : 0 ≤ t := hv.trans hvt
  have hex := (hW.classical α t ht0).1
  have hp : propagatorW C v t (oscTestFun m α) = hex.choose v := by
    unfold propagatorW; rw [dif_pos hex]
  have hspec := hex.choose_spec
  rw [hp]
  obtain ⟨hcd, hcb⟩ := (hW.grad α t ht0).1 hex.choose hspec v ⟨hv, hvt⟩
  have hA : 0 ≤ b α * Real.exp (-c0 * (t - v)) := mul_nonneg (hW.nonneg α) (Real.exp_pos _).le
  have hbd := s104_cbNormVecE_le hA hcb
  have hC2 : ContDiff ℝ 2 (hex.choose v) := hspec.c2 v ⟨hv, hvt⟩
  have hdiff : Differentiable ℝ (hex.choose v) := hC2.differentiable (by norm_num)
  have hfd : fderiv ℝ (hex.choose v) =
      fun x => (InnerProductSpace.toDual ℝ (Euc d)) (gradient (hex.choose v) x) := by
    funext x; simp [gradient]
  refine ⟨?_, ?_, ?_⟩
  · push_cast
    refine contDiff_succ_iff_fderiv.2 ⟨hdiff, fun h => absurd h (by simp), ?_⟩
    rw [hfd]
    exact (InnerProductSpace.toDual ℝ (Euc d)).contDiff.comp hcd
  · intro j hj1 hj2 x
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [← s111k2_norm_iter_gradient]
    exact hbd j' (by omega) x
  · obtain ⟨B, hB⟩ := hspec.bdd 0 (by norm_num)
    refine ⟨B, fun x => ?_⟩
    have := hB v ⟨hv, hvt⟩ x
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this

lemma s111k2_bounded_of_L1F {r : ℕ} {Pw H : ℝ} {z : ℝ → (Euc d → ℝ) → ℝ} (hz : IsR2L1F r Pw H z) {v : ℝ}
    (hv : v ∈ Set.Icc (0 : ℝ) H) : IsBoundedLinearOnE r Pw (z v) := by
  obtain ⟨h1, h2, ⟨M, hM⟩⟩ := hz.1 v hv
  exact ⟨fun f g hf hEf hg hEg c => ⟨h1 f g ⟨hf, hEf⟩ ⟨hg, hEg⟩, h2 c f ⟨hf, hEf⟩⟩,
    ⟨M, fun f hf hEf => hM f ⟨hf, hEf⟩⟩⟩

lemma s111k2_zero {r : ℕ} {P : ℝ} (hP : (d : ℝ) + 2 < 2 * P) {η : (Euc d → ℝ) → ℝ}
    (hη : IsBoundedLinearOnE r P η) (hone : η (fun _ => 1) = 0) {Ft : Euc d → ℝ}
    (hF : ContDiff ℝ ((r + 1 : ℕ) : WithTop ℕ∞) Ft) {A : ℝ} (hA : 0 ≤ A)
    (hL : ∀ j : ℕ, 1 ≤ j → j ≤ r + 1 → ∀ x, ‖iteratedFDeriv ℝ j Ft x‖ ≤ A) :
    η Ft = η (fun x => Ft x - Ft 0) := by
  have hP' : (d : ℝ) < 2 * P := by linarith
  obtain ⟨hgC, hgl⟩ := s111k2_g_props r hF hA hL
  have hEg : weightedSobolevE r P (fun x => Ft x - Ft 0) < ⊤ :=
    lt_of_le_of_lt (s111k2_E_le_lin hP hA hgl) ENNReal.ofReal_lt_top
  have hEone : weightedSobolevE r P (fun _ : Euc d => (1 : ℝ)) < ⊤ := by
    refine lt_of_le_of_lt (s57p_E_le_cb hP' (B := 1) zero_le_one (fun j hj x => ?_)) ENNReal.ofReal_lt_top
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp
    · rw [iteratedFDeriv_const_of_ne (by omega)]; simp
  have hk : (fun _ : Euc d => Ft 0) = (Ft 0) • (fun _ : Euc d => (1 : ℝ)) := by funext x; simp
  have hEk : weightedSobolevE r P (fun _ : Euc d => Ft 0) < ⊤ := by
    refine lt_of_le_of_lt (s57p_E_le_cb hP' (B := |Ft 0|) (abs_nonneg _) (fun j hj x => ?_)) ENNReal.ofReal_lt_top
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp
    · rw [iteratedFDeriv_const_of_ne (by omega)]; simp
  have h3 := (hη.1 (fun _ : Euc d => (1 : ℝ)) (fun _ : Euc d => (1 : ℝ)) contDiff_const hEone contDiff_const hEone (Ft 0)).2
  have hηk : η (fun _ : Euc d => Ft 0) = 0 := by rw [hk, h3, hone, mul_zero]
  have e : Ft = (fun x => Ft x - Ft 0) + (fun _ : Euc d => Ft 0) := by funext x; simp
  have h1 : η Ft = η ((fun x => Ft x - Ft 0) + (fun _ : Euc d => Ft 0)) := congrArg η e
  have h2 := (hη.1 (fun x => Ft x - Ft 0) (fun _ : Euc d => Ft 0) hgC hEg contDiff_const hEk 0).1
  rw [h1, h2, hηk, add_zero]

lemma s111k2_coord_bound {r : ℕ} {P : ℝ} (hP : (d : ℝ) + 2 < 2 * P) {η : (Euc d → ℝ) → ℝ}
    (hη : IsBoundedLinearOnE r P η) (hdual : dualNormE r P η < ⊤) (hone : η (fun _ => 1) = 0)
    {Ft : Euc d → ℝ} (hF : ContDiff ℝ ((r + 1 : ℕ) : WithTop ℕ∞) Ft) {A : ℝ} (hA : 0 ≤ A)
    (hL : ∀ j : ℕ, 1 ≤ j → j ≤ r + 1 → ∀ x, ‖iteratedFDeriv ℝ j Ft x‖ ≤ A)
    (hB : ∃ B0 : ℝ, ∀ x, |Ft x| ≤ B0) :
    |η Ft| ≤ (dualNormE r P η).toReal * (s111k2_CE d r P * A) := by
  rw [s111k2_zero hP hη hone hF hA hL]
  obtain ⟨B0, hB0⟩ := hB
  have hB00 : 0 ≤ B0 := (abs_nonneg _).trans (hB0 0)
  have hFr : ContDiff ℝ r Ft := hF.of_le (by exact_mod_cast Nat.le_succ r)
  obtain ⟨hgC, hgl⟩ := s111k2_g_props r hF hA hL
  exact s111k2_dual_lin hP hη hdual hgC (s111k2_g_qual hFr hA hB00 hB0
    (fun j h1 h2 x => hL j h1 (by omega) x)) hA hgl

end HRS.MS.S111K2

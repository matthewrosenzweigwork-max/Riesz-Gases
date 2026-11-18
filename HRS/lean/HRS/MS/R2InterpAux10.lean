import HRS.MS.R2InterpAux9
import HRS.MS.FixEqP1Aux1

/-!
# S10.2 (worker S102), part 10 (packet I3/I4 core): the transpose propagator `V^{t,u}z` of an admissible functional

For `z` an admissible functional (additive, homogeneous, norm-continuous on the tests of `E_{r,P}`) and the orbit data of `R2OrbitSummable`:
* `z(U^{u,t}φ_α)` is bounded by `M K c_α` (`c ∈ ℓ²`), so `r2Vprop C m t u z` is the genuine element of `B_m` with the coordinates `z(U^{u,t}φ_α)`
  (no junk `ofSeq`; the linearity `hlin` of the propagator on the Hermite functions is used);
* `t ↦ r2Vprop C m t u z` is Lipschitz on `[u,T]` (`‖V^{t,u}z - V^{t',u}z‖ ≤ K |t-t'|`), by `s102_orbit_diff_bound`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas HRS.MS.FixEq

variable {d : ℕ}

/-- An admissible functional on the tests of `E_{r,P}`. -/
structure S102Z (r : ℕ) (Pw : ℝ) (z : (Euc d → ℝ) → ℝ) : Prop where
  add : ∀ f g, IsR2WeightedTest r Pw f → IsR2WeightedTest r Pw g → z (f + g) = z f + z g
  smul : ∀ (c : ℝ) f, IsR2WeightedTest r Pw f → z (c • f) = c * z f
  bdd : ∃ M : ℝ, ∀ f, IsR2WeightedTest r Pw f → |z f| ≤ M * (weightedSobolevE r Pw f).toReal

theorem s102_test_of_bound {r : ℕ} {Pw : ℝ} (hP : (d : ℝ) < 2 * Pw) {f : Euc d → ℝ} (hf : ContDiff ℝ r f)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ j ≤ r, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ B) :
    IsR2WeightedTest r Pw f ∧ (weightedSobolevE r Pw f).toReal ≤ s57pC d r Pw * B := by
  have h := s57p_E_le_cb (r := r) hP hB0 hB
  refine ⟨⟨hf, lt_of_le_of_lt h ENNReal.ofReal_lt_top⟩, ?_⟩
  calc (weightedSobolevE r Pw f).toReal ≤ (ENNReal.ofReal (s57pC d r Pw * B)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    _ = s57pC d r Pw * B := ENNReal.toReal_ofReal (mul_nonneg (s57pC_nonneg d r Pw) hB0)

theorem s102_orbit_test {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ} {Pw : ℝ}
    (hP : (d : ℝ) < 2 * Pw) (hD : S101Data C m T r c) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) T) {t : ℝ}
    (ht : t ∈ Icc u T) (α : MultiIndex d) :
    IsR2WeightedTest r Pw (propagatorW C u t (oscTestFun m α)) ∧
      (weightedSobolevE r Pw (propagatorW C u t (oscTestFun m α))).toReal ≤ s57pC d r Pw * c α :=
  s102_test_of_bound hP ((hD.smoothU α u hu t ht).of_le (by exact_mod_cast Nat.le_succ r)) (hD.nonneg α)
    (fun j hj x => hD.bddU α u hu t ht j (by omega) x)

theorem s102_orbit_diff_test {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ} {Pw : ℝ}
    (hP : (d : ℝ) < 2 * Pw) (hD : S101Data C m T r c) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) T) {t' t : ℝ}
    (ht' : t' ∈ Icc u T) (ht : t ∈ Icc u T) (htt : t' ≤ t) (α : MultiIndex d) :
    IsR2WeightedTest r Pw (fun y => propagatorW C u t (oscTestFun m α) y -
        propagatorW C u t' (oscTestFun m α) y) ∧
      (weightedSobolevE r Pw (fun y => propagatorW C u t (oscTestFun m α) y -
        propagatorW C u t' (oscTestFun m α) y)).toReal ≤ s57pC d r Pw * (c α * (t - t')) := by
  have h1 : ContDiff ℝ r (propagatorW C u t (oscTestFun m α)) :=
    (hD.smoothU α u hu t ht).of_le (by exact_mod_cast Nat.le_succ r)
  have h2 : ContDiff ℝ r (propagatorW C u t' (oscTestFun m α)) :=
    (hD.smoothU α u hu t' ht').of_le (by exact_mod_cast Nat.le_succ r)
  exact s102_test_of_bound hP (h1.sub h2) (mul_nonneg (hD.nonneg α) (sub_nonneg.2 htt))
    (fun j hj x => s102_orbit_diff_bound hD hu ht' ht htt α j (by omega) x)

/-- Terminal-time Lipschitz bound of an admissible functional on the orbits. -/
theorem s102_z_orbit_diff {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ} {Pw : ℝ}
    (hP : (d : ℝ) < 2 * Pw) (hD : S101Data C m T r c) {z : (Euc d → ℝ) → ℝ} (hz : S102Z r Pw z)
    {M : ℝ} (hM : ∀ f, IsR2WeightedTest r Pw f → |z f| ≤ M * (weightedSobolevE r Pw f).toReal)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) T) {t' t : ℝ} (ht' : t' ∈ Icc u T) (ht : t ∈ Icc u T) (htt : t' ≤ t)
    (α : MultiIndex d) :
    |z (propagatorW C u t (oscTestFun m α)) - z (propagatorW C u t' (oscTestFun m α))| ≤
      |M| * (s57pC d r Pw * (c α * (t - t'))) := by
  obtain ⟨hd1, hd2⟩ := s102_orbit_diff_test hP hD hu ht' ht htt α
  obtain ⟨h2, -⟩ := s102_orbit_test hP hD hu ht' α
  have hsplit : propagatorW C u t (oscTestFun m α) =
      (fun y => propagatorW C u t (oscTestFun m α) y - propagatorW C u t' (oscTestFun m α) y) +
        propagatorW C u t' (oscTestFun m α) := by
    funext y; simp
  have : z (propagatorW C u t (oscTestFun m α)) - z (propagatorW C u t' (oscTestFun m α)) =
      z (fun y => propagatorW C u t (oscTestFun m α) y - propagatorW C u t' (oscTestFun m α) y) := by
    conv_lhs => rw [hsplit, hz.add _ _ hd1 h2]
    ring
  rw [this]
  calc _ ≤ M * (weightedSobolevE r Pw _).toReal := hM _ hd1
    _ ≤ |M| * (weightedSobolevE r Pw _).toReal := mul_le_mul_of_nonneg_right (le_abs_self M) ENNReal.toReal_nonneg
    _ ≤ |M| * (s57pC d r Pw * (c α * (t - t'))) := mul_le_mul_of_nonneg_left hd2 (abs_nonneg M)

/-- Bound of the coordinates. -/
theorem s102_z_orbit_bound {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ} {Pw : ℝ}
    (hP : (d : ℝ) < 2 * Pw) (hD : S101Data C m T r c) {z : (Euc d → ℝ) → ℝ} (hz : S102Z r Pw z)
    {M : ℝ} (hM : ∀ f, IsR2WeightedTest r Pw f → |z f| ≤ M * (weightedSobolevE r Pw f).toReal)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) T) {t : ℝ} (ht : t ∈ Icc u T) (α : MultiIndex d) :
    |z (propagatorW C u t (oscTestFun m α))| ≤ |M| * (s57pC d r Pw * c α) := by
  obtain ⟨h1, h2⟩ := s102_orbit_test hP hD hu ht α
  calc _ ≤ M * (weightedSobolevE r Pw _).toReal := hM _ h1
    _ ≤ |M| * (weightedSobolevE r Pw _).toReal := mul_le_mul_of_nonneg_right (le_abs_self M) ENNReal.toReal_nonneg
    _ ≤ |M| * (s57pC d r Pw * c α) := mul_le_mul_of_nonneg_left h2 (abs_nonneg M)

end HRS.MS.R2Interp

end

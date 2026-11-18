import HRS.Sections.Q38bAux1

/-!
# Packet Q38b, part 2: the homogeneous response inverse and equilibrium semigroup on `e_k`

For `V = 0`, `ρ_β = 1` and every nonzero real mode `e_k = realMode k`:
* `R_{β} P e_k = (1 + βĝ(k))⁻¹ e_k` (a.e.);
* `S_β(τ) e_k = exp(-λ_k τ) e_k` with `λ_k = (2π|k|)²(β⁻¹ + ĝ(k))`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS

variable {d : ℕ}

/-! ### The response inverse -/

theorem q38b_convFun_c_realMode (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (k : NonzeroLattice d) (c : ℝ) (x : Torus d) :
    convFun (periodicRiesz d s) (fun y => c * Torus.realMode k y) x =
      c * rieszCoeff d s k.1 * Torus.realMode k x := by
  have h := congrFun (q38b_convFun_realMode hd hs0 hsd k) x
  unfold convFun at h ⊢
  have e : ∀ y, periodicRiesz d s (x - y) * (c * Torus.realMode k y) =
      c * (periodicRiesz d s (x - y) * Torus.realMode k y) := fun y => by ring
  simp_rw [e]
  rw [integral_const_mul, h]
  ring

theorem q38b_int_c_realMode (k : NonzeroLattice d) (c : ℝ) :
    ∫ x : Torus d, c * Torus.realMode k x = 0 := by
  rw [integral_const_mul, Torus.integral_realMode, mul_zero]

theorem q38b_isResponse (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    (k : NonzeroLattice d) (α : ℝ) :
    IsResponse (periodicRiesz d s) (volume : Measure (Torus d)) β
      (fun x => α * Torus.realMode k x)
      (fun x => (α * (1 + β * rieszCoeff d s k.1)⁻¹) * Torus.realMode k x) := by
  have hne : (1 + β * rieszCoeff d s k.1) ≠ 0 := (q42_one_add_pos hd hs0 hsd hβ k.1).ne'
  have hv : (1 + β * rieszCoeff d s k.1) * (1 + β * rieszCoeff d s k.1)⁻¹ = 1 :=
    mul_inv_cancel₀ hne
  have hc : Continuous (fun x => Torus.realMode k x) := Torus.continuous_realMode k
  have hcand : Continuous (fun x => (α * (1 + β * rieszCoeff d s k.1)⁻¹) * Torus.realMode k x) :=
    continuous_const.mul hc
  have hmean : ∫ x : Torus d, convFun (periodicRiesz d s)
      (fun y => (α * (1 + β * rieszCoeff d s k.1)⁻¹) * Torus.realMode k y) x = 0 := by
    simp_rw [q38b_convFun_c_realMode hd hs0 hsd k]
    exact q38b_int_c_realMode k _
  have hKop : ∀ x : Torus d, Kop (periodicRiesz d s) (volume : Measure (Torus d))
      (fun x => (α * (1 + β * rieszCoeff d s k.1)⁻¹) * Torus.realMode k x) x =
      convFun (periodicRiesz d s)
        (fun y => (α * (1 + β * rieszCoeff d s k.1)⁻¹) * Torus.realMode k y) x := by
    intro x
    show convFun (periodicRiesz d s) _ x - HRS.pair (volume : Measure (Torus d))
      (convFun (periodicRiesz d s) _) = _
    unfold HRS.pair
    rw [hmean, sub_zero]
  refine ⟨hcand.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _), ?_, ?_⟩
  · unfold HRS.pair
    exact q38b_int_c_realMode k _
  · refine Filter.Eventually.of_forall fun x => ?_
    rw [hKop x, q38b_convFun_c_realMode hd hs0 hsd k]
    have hψm : HRS.pair (volume : Measure (Torus d)) (fun x => α * Torus.realMode k x) = 0 := by
      unfold HRS.pair
      exact q38b_int_c_realMode k α
    unfold projMean
    rw [hψm, sub_zero]
    dsimp only
    linear_combination (α * Torus.realMode k x) * hv

/-- The response inverse on the torus is explicit on a real mode, almost everywhere. -/
theorem q38b_responseInverse_eq (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ}
    (hβ : 0 < β) (k : NonzeroLattice d) (α : ℝ) :
    ∀ᵐ x ∂(volume : Measure (Torus d)),
      responseInverse (periodicRiesz d s) (volume : Measure (Torus d)) β
        (fun x => α * Torus.realMode k x) x =
        (α * (1 + β * rieszCoeff d s k.1)⁻¹) * Torus.realMode k x := by
  have hvol : (withDensityReal (fun _ : Torus d => (1 : ℝ))) = (volume : Measure (Torus d)) := by
    unfold withDensityReal
    simp
  have hρ : IsProbDensity (fun _ : Torus d => (1 : ℝ)) :=
    ⟨fun _ => zero_le_one, measurable_const, by simp⟩
  have hc : Continuous (fun x => Torus.realMode k x) := Torus.continuous_realMode k
  have hψL : MemLp (fun x => α * Torus.realMode k x) 2
      (withDensityReal (fun _ : Torus d => (1 : ℝ))) := by
    rw [hvol]
    exact (continuous_const.mul hc).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  obtain ⟨w, hw, huniq⟩ := exists_unique_response hd hs0 hsd (fun _ : Torus d => (1 : ℝ)) hρ 1
    (fun _ => le_rfl) β hβ.le _ hψL
  rw [hvol] at hw huniq
  have hex : ∃ h, IsResponse (periodicRiesz d s) (volume : Measure (Torus d)) β
      (fun x => α * Torus.realMode k x) h := ⟨w, hw⟩
  have hR : responseInverse (periodicRiesz d s) (volume : Measure (Torus d)) β
      (fun x => α * Torus.realMode k x) = hex.choose := by
    unfold responseInverse
    rw [dif_pos hex]
  have hch := hex.choose_spec
  have hcand := q38b_isResponse hd hs0 hsd hβ k α
  filter_upwards [huniq _ hch, huniq _ hcand] with x hx1 hx2
  rw [hR]
  exact hx1.trans hx2.symm

end HRS

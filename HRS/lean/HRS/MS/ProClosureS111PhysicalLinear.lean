import HRS.MS.ProClosureS111ClassicalLinear
import HRS.MS.ProClosureS111PhysicalOrbit
import HRS.MS.R2WinOrbAux13

/-!
Linearity of the actual thermal propagator on the frozen finite oscillator
test class. Existence is proved by finite classical superposition; accepted
thermal uniqueness then identifies each solution with `propagatorW`.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.R2WinOrb

variable {d : ℕ}

theorem physical_generator_add (hd : 2 ≤ d)
    {s a beta : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ))
    (ha : 0 < a) (hbeta : 0 < beta) {rho : Euc d → ℝ}
    (hrho : IsThermalEquilibrium d s a beta rho) (r : ℝ)
    {f g : Euc d → ℝ} (hf : MemCb 4 f) (hg : MemCb 4 g) (x : Euc d) :
    let C := (quadraticGradientDyn d s a beta).coeff (fun _ => rho)
    generatorW C r (fun y => f y + g y) x =
      generatorW C r f x + generatorW C r g x := by
  dsimp only
  rw [s103_coeff_eq s a beta rho]
  exact HRS.MS.Ul.ul6_gen_add hs0 hsd
    (s103_rho_schwartz hd hs0 hsd ha hbeta hrho).2 _ hf hg x

theorem physical_classicalCb4_basis (hd : 2 ≤ d)
    {s a beta : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ))
    (ha : 0 < a) (hbeta : 0 < beta) {rho : Euc d → ℝ}
    (hrho : IsThermalEquilibrium d s a beta rho) (alpha : MultiIndex d)
    {t : ℝ} (ht : 0 ≤ t) :
    let C := (quadraticGradientDyn d s a beta).coeff (fun _ => rho)
    let phi := oscTestFun ((24 * d + 240 : ℕ) : ℝ) alpha
    ClassicalCb4 C t phi (fun r => propagatorW C r t phi) := by
  let C := (quadraticGradientDyn d s a beta).coeff (fun _ => rho)
  let phi := oscTestFun ((24 * d + 240 : ℕ) : ℝ) alpha
  have hf : IsClassicalAdjointW C t phi (fun r => propagatorW C r t phi) :=
    HRS.MS.Fcau.propagatorW_isClassical
      (physical_classical_orbits hd hs0 hsd ha hbeta hrho alpha ht).1
  obtain ⟨B, c, hB, hc, hbound⟩ := s103_orbit_iter hd hs0 hsd ha hbeta hrho
  refine ⟨hf, fun r hr => ?_⟩
  have hb := hbound alpha t ht 0 (by norm_num) _ hf r hr
  have hA : 0 ≤ B * s103_b d alpha := mul_nonneg hB (s103_b_nonneg alpha)
  refine ⟨hb.1.of_le (by exact_mod_cast (by omega : 4 ≤ 4 * d + 42)),
    fun j hj => ⟨B * s103_b d alpha, ?_⟩⟩
  rintro _ ⟨x, rfl⟩
  exact s103_cb_of_E hA hb.2 j (by omega) x

theorem physical_classicalCb4_combo (hd : 2 ≤ d)
    {s a beta : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ))
    (ha : 0 < a) (hbeta : 0 < beta) {rho : Euc d → ℝ}
    (hrho : IsThermalEquilibrium d s a beta rho) {t : ℝ} (ht : 0 ≤ t)
    {phi : Euc d → ℝ} (hphi : IsR2DualCombo ((24 * d + 240 : ℕ) : ℝ) phi) :
    ∃ f, ClassicalCb4 ((quadraticGradientDyn d s a beta).coeff (fun _ => rho))
      t phi f := by
  let C := (quadraticGradientDyn d s a beta).coeff (fun _ => rho)
  rcases hphi with ⟨S, coeff, rfl⟩
  induction S using Finset.induction_on with
  | empty =>
      have hz := classicalCb4_const_mul
        (physical_classicalCb4_basis hd hs0 hsd ha hbeta hrho (0 : MultiIndex d) ht) 0
      refine ⟨fun _ _ => 0, ?_⟩
      simpa only [Finset.sum_empty, zero_mul] using hz
  | @insert alpha S hnot ih =>
      obtain ⟨f, hf⟩ := ih
      have hg := classicalCb4_const_mul
        (physical_classicalCb4_basis hd hs0 hsd ha hbeta hrho alpha ht) (coeff alpha)
      have hsum := classicalCb4_add hg hf (fun r hr x =>
        physical_generator_add hd hs0 hsd ha hbeta hrho r (hg.cb4 r hr) (hf.cb4 r hr) x)
      refine ⟨fun r x => coeff alpha *
        propagatorW C r t (oscTestFun ((24 * d + 240 : ℕ) : ℝ) alpha) x + f r x, ?_⟩
      simpa only [Finset.sum_insert hnot] using hsum

/-- The exact `linear` field of `S111k2WindowOrbitInput`, from physical data alone. -/
theorem physical_propagator_linear (hd : 2 ≤ d)
    {s a beta : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ))
    (ha : 0 < a) (hbeta : 0 < beta) {rho : Euc d → ℝ}
    (hrho : IsThermalEquilibrium d s a beta rho)
    (v t : ℝ) (hv : 0 ≤ v) (hvt : v ≤ t)
    (phi psi : Euc d → ℝ) (c : ℝ)
    (hphi : IsR2DualCombo ((24 * d + 240 : ℕ) : ℝ) phi)
    (hpsi : IsR2DualCombo ((24 * d + 240 : ℕ) : ℝ) psi) :
    let C := (quadraticGradientDyn d s a beta).coeff (fun _ => rho)
    propagatorW C v t (phi + c • psi) =
      propagatorW C v t phi + c • propagatorW C v t psi := by
  let C := (quadraticGradientDyn d s a beta).coeff (fun _ => rho)
  have ht : 0 ≤ t := hv.trans hvt
  obtain ⟨f, hf⟩ := physical_classicalCb4_combo hd hs0 hsd ha hbeta hrho ht hphi
  obtain ⟨g, hg⟩ := physical_classicalCb4_combo hd hs0 hsd ha hbeta hrho ht hpsi
  have hcg := classicalCb4_const_mul hg c
  have hsum := classicalCb4_add hf hcg (fun r hr x =>
    physical_generator_add hd hs0 hsd ha hbeta hrho r (hf.cb4 r hr) (hcg.cb4 r hr) x)
  have huniq := HRS.MS.TransOp.s611_uniq_of_thermal hd hs0 hsd ha hbeta hrho t
  have ef : propagatorW C v t phi = f v :=
    huniq t ⟨ht, le_rfl⟩ phi f hf.classical v ⟨hv, hvt⟩
  have eg : propagatorW C v t psi = g v :=
    huniq t ⟨ht, le_rfl⟩ psi g hg.classical v ⟨hv, hvt⟩
  have esum : propagatorW C v t (phi + c • psi) =
      fun x => f v x + c * g v x :=
    huniq t ⟨ht, le_rfl⟩ (phi + c • psi) _ hsum.classical v ⟨hv, hvt⟩
  change propagatorW C v t (phi + c • psi) = _
  rw [esum, ef, eg]
  rfl

end HRS.MS.ProClosureS111

#print axioms HRS.MS.ProClosureS111.physical_generator_add
#print axioms HRS.MS.ProClosureS111.physical_classicalCb4_combo
#print axioms HRS.MS.ProClosureS111.physical_propagator_linear

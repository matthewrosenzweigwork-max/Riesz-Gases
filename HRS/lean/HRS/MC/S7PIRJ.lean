import HRS.MC.S7PIRDrift
import HRS.MC.S7PIS3Cov1

/-!
# Packet F9 (piR): Riemann-Stieltjes sums for the `𝒥`-pairing of a cylindrical functional

Proof of `HRS.MC.Sec7.PIPlan.s7_PIF_RS_J` (statement copied verbatim).  By `s7_PIF_heat_obs_proof` (c) the second derivative of
the heat function is `(D²F)(obs y) ∘ (O, O) = ∑_{ij} ∂_{ij}F(obs y) ℓ_i ⊗ ℓ_j`; the tensor `J = jPair`'s witness is evaluated on
`ℓ_i ⊗ ℓ_j` by `IsJValue` (no uniqueness is needed: `jPair z I = (Classical.choose ..) M` for the chosen witness), and the
resulting integral over `I ∩ [0, t_i ∧ t_j]` equals the integral over `I` of the pairing with `∇obsTest_i · ∇obsTest_j`
(which vanishes beyond `t_i ∧ t_j`).  Then `s7_PIS_RS_basic_proof` (b) applies to the finite family `(i,j)`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIR

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI

variable {d : ℕ}

/-- the pairing density vanishes beyond `t_i ∧ t_j` -/
lemma S7PIR_pair_zero {m : ℝ} (R : Regime d) {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ) (i j : Fin q)
    (F : NegSobolev d m) {u : ℝ} (hu : min (t i) (t j) < u) :
    NegSobolev.eval F (fun y => inner ℝ (Torus.grad (obsTest R.D R.ρ t φ i u) y)
      (Torus.grad (obsTest R.D R.ρ t φ j u) y)) = 0 := by
  have hz : (fun y => inner ℝ (Torus.grad (obsTest R.D R.ρ t φ i u) y)
      (Torus.grad (obsTest R.D R.ρ t φ j u) y)) = fun _ => 0 := by
    funext y
    rcases min_lt_iff.1 hu with h | h
    · simp [obsTest, if_neg (not_le.2 h), HRS.MC.Sec7.S7PIS3.S7PIS3_grad_zero]
    · simp [obsTest, if_neg (not_le.2 h), HRS.MC.Sec7.S7PIS3.S7PIS3_grad_zero]
  rw [hz]
  exact HRS.A33.a33_eval_const F 0

/-- the integral over `I ∩ [0, t_i ∧ t_j]` of the propagated pairing is the integral over `I` of the `obsTest` pairing -/
lemma S7PIR_J_set {m : ℝ} (R : Regime d) (z : ℝ → NegSobolev d m) {q : ℕ} (t : Fin q → ℝ)
    (φ : Fin q → Torus d → ℝ) (i j : Fin q) (a b' : ℝ) (ha : 0 ≤ a) :
    ∫ u in Set.Ioc a b' ∩ Set.Icc (0 : ℝ) (min (t i) (t j)), NegSobolev.eval (z u)
        (fun x => inner ℝ (Torus.grad (propagator R.D R.ρ u (t i) (φ i)) x)
          (Torus.grad (propagator R.D R.ρ u (t j) (φ j)) x)) =
      ∫ u in Set.Ioc a b', NegSobolev.eval (z u)
        (fun y => inner ℝ (Torus.grad (obsTest R.D R.ρ t φ i u) y) (Torus.grad (obsTest R.D R.ρ t φ j u) y)) := by
  symm
  rw [setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioc Set.inter_subset_left]
  · refine setIntegral_congr_fun (measurableSet_Ioc.inter measurableSet_Icc) (fun u hu => ?_)
    have h1 : u ≤ t i := hu.2.2.trans (min_le_left _ _)
    have h2 : u ≤ t j := hu.2.2.trans (min_le_right _ _)
    simp only [obsTest, if_pos h1, if_pos h2]
  · intro u hu
    refine S7PIR_pair_zero R t φ i j (z u) ?_
    by_contra hcon
    exact hu.2 ⟨hu.1, (ha.trans hu.1.1.le), not_lt.1 hcon⟩

/-- **F9 (Riemann-Stieltjes `𝒥`-integral of a cylindrical functional; deterministic)**. -/
theorem s7_PIF_RS_J_proof (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T)
    (γ : ℝ → Measure (PathSpace d m T)) (hγ : ∀ u ∈ Set.Icc (0 : ℝ) T, IsFutureGaussian R.D R.ρ m T u (γ u))
    {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ) (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) T)
    (hφ : ∀ i, Torus.IsSmooth (φ i)) (G : EuclideanSpace ℝ (Fin q) → ℝ) (hG : MemCb 2 G)
    (w : PathSpace d m T) (z : ℝ → NegSobolev d m)
    (hJ : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ T → ∃ J, IsJValue R.D R.ρ m T z (Set.Ioc a b) J)
    (hzi : ∀ i j, IntegrableOn (fun r => NegSobolev.eval (z r)
        (fun y => inner ℝ (Torus.grad (obsTest R.D R.ρ t φ i r) y) (Torus.grad (obsTest R.D R.ρ t φ j r) y)))
      (Set.Icc 0 T)) :
    IsRS T (fun τ a b' => jPair R.D R.ρ m T z (Set.Ioc a b')
        (iteratedFDeriv ℝ 2 (heatFn γ (fun x => G (obsVec m T t φ x)) τ) (predicted R.D R.ρ w τ)))
      (∫ r in Set.Ioc 0 T, ∑ i, ∑ j, iteratedFDeriv ℝ 2 (gaussHeat (obsCov R.D R.ρ t φ) G r)
          (obsVec m T t φ (predicted R.D R.ρ w r)) ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] *
        (2 * R.D.invβ * NegSobolev.eval (z r)
          (fun y => inner ℝ (Torus.grad (obsTest R.D R.ρ t φ i r) y) (Torus.grad (obsTest R.D R.ρ t φ j r) y)))) := by
  classical
  have hHO := HRS.MC.Sec7.S7PIB.s7_PIF_heat_obs_proof R m T hT γ hγ t φ ht hφ G hG
  obtain ⟨O, hO⟩ := HRS.MC.Sec7.S7PIS2.s7_PIS_obs_clm_proof m T t φ ht hφ
  have hgc : ∀ ij : Fin q × Fin q, ContinuousOn (fun τ => iteratedFDeriv ℝ 2
      (gaussHeat (obsCov R.D R.ρ t φ) G τ) (obsVec m T t φ (predicted R.D R.ρ w τ))
      ![EuclideanSpace.single ij.1 1, EuclideanSpace.single ij.2 1]) (Set.Icc 0 T) := by
    intro ij
    exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => EuclideanSpace ℝ (Fin q)) ℝ
      ![EuclideanSpace.single ij.1 1, EuclideanSpace.single ij.2 1]).continuous.comp_continuousOn
      (S7PIR_heat_deriv_cont R m hm T hT γ hγ t φ ht hφ G hG w 2 le_rfl)
  have hRS := (HRS.MC.Sec7.S7PIS2.s7_PIS_RS_basic_proof T hT).2 (ι := Fin q × Fin q)
    (fun ij τ => iteratedFDeriv ℝ 2 (gaussHeat (obsCov R.D R.ρ t φ) G τ)
      (obsVec m T t φ (predicted R.D R.ρ w τ)) ![EuclideanSpace.single ij.1 1, EuclideanSpace.single ij.2 1])
    (fun ij u => 2 * R.D.invβ * NegSobolev.eval (z u)
      (fun y => inner ℝ (Torus.grad (obsTest R.D R.ρ t φ ij.1 u) y) (Torus.grad (obsTest R.D R.ρ t φ ij.2 u) y)))
    hgc (fun ij => (hzi ij.1 ij.2).const_mul _)
  have hI : (∫ r in Set.Ioc 0 T, ∑ i, ∑ j, iteratedFDeriv ℝ 2 (gaussHeat (obsCov R.D R.ρ t φ) G r)
          (obsVec m T t φ (predicted R.D R.ρ w r)) ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] *
        (2 * R.D.invβ * NegSobolev.eval (z r)
          (fun y => inner ℝ (Torus.grad (obsTest R.D R.ρ t φ i r) y) (Torus.grad (obsTest R.D R.ρ t φ j r) y)))) =
      ∫ u in Set.Ioc 0 T, ∑ ij : Fin q × Fin q, iteratedFDeriv ℝ 2 (gaussHeat (obsCov R.D R.ρ t φ) G u)
        (obsVec m T t φ (predicted R.D R.ρ w u)) ![EuclideanSpace.single ij.1 1, EuclideanSpace.single ij.2 1] *
        (2 * R.D.invβ * NegSobolev.eval (z u)
          (fun y => inner ℝ (Torus.grad (obsTest R.D R.ρ t φ ij.1 u) y)
            (Torus.grad (obsTest R.D R.ρ t φ ij.2 u) y))) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [Fintype.sum_prod_type]
  rw [hI]
  refine S7PIR_isRS_congr hRS (fun τ a b' ha haτ hτb hbT => ?_)
  have hτ : τ ∈ Set.Icc (0 : ℝ) T := ⟨ha.trans haτ, hτb.trans hbT⟩
  have hab : a ≤ b' := haτ.trans hτb
  have hex := hJ a b' ha hab hbT
  have hJv := Classical.choose_spec hex
  set Jt := Classical.choose hex with hJt
  have hjp : jPair R.D R.ρ m T z (Set.Ioc a b')
      (iteratedFDeriv ℝ 2 (heatFn γ (fun x => G (obsVec m T t φ x)) τ) (predicted R.D R.ρ w τ)) =
      Jt (iteratedFDeriv ℝ 2 (heatFn γ (fun x => G (obsVec m T t φ x)) τ) (predicted R.D R.ρ w τ)) := by
    unfold jPair
    rw [dif_pos hex]
  refine Eq.trans ?_ hjp.symm
  rw [(hHO.2.2 O hO τ hτ _).2]
  set B := iteratedFDeriv ℝ 2 (gaussHeat (obsCov R.D R.ρ t φ) G τ)
    (obsVec m T t φ (predicted R.D R.ρ w τ)) with hB
  set l : Fin q → StrongDual ℝ (PathSpace d m T) := fun i => (EuclideanSpace.proj i).comp O with hl
  have hlw : ∀ i w', l i w' = NegSobolev.eval (pathAt w' (t i)) (φ i) := by
    intro i w'
    simp only [hl, ContinuousLinearMap.comp_apply, hO]
    rfl
  have hM : B.compContinuousLinearMap (fun _ => O) = ∑ i, ∑ j, (B ![EuclideanSpace.single i 1,
      EuclideanSpace.single j 1]) • ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap
        ![l i, l j]) := by
    apply ContinuousMultilinearMap.ext
    intro v
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply, S7PIR_cmm2_expand B]
    simp only [ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.smul_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply, ContinuousMultilinearMap.mkPiAlgebra_apply,
      Fin.prod_univ_two]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    simp [hl]
    ring
  rw [hM, map_sum]
  simp only [map_sum, map_smul, smul_eq_mul]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [hJv.2 (t i) (t j) (φ i) (φ j) (l i) (l j) (hφ i) (hφ j) (ht i) (ht j) (hlw i) (hlw j),
    S7PIR_J_set R z t φ i j a b' ha, integral_const_mul]

end HRS.MC.Sec7.S7PIR

end

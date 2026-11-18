import HRS.MC.CepE1Aux4

/-!
# Packet CEPE1, auxiliary 5: the drift identity in rank coordinates
-/

open Set
open scoped NNReal RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE1

open HRS HRS.MC.CepK1

variable {N : ℕ}

/-- Derivative of the singular pair profile `u ↦ (a/N)(-log(2 sin πu))`. -/
def cepe1_h1 (a : ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  (a / N) * (-(Real.pi * (Real.cos (Real.pi * u) / Real.sin (Real.pi * u))))

/-- Derivative of the smooth pair profile `u ↦ (a/N) r(u)`. -/
def cepe1_h2 (a : ℝ) (N : ℕ) (u : ℝ) : ℝ := (a / N) * cepk1_ρ u

theorem cepe1_h1_neg (a : ℝ) (N : ℕ) (u : ℝ) : cepe1_h1 a N (-u) = -cepe1_h1 a N u := by
  unfold cepe1_h1
  have : Real.pi * -u = -(Real.pi * u) := by ring
  rw [this, Real.cos_neg, Real.sin_neg, div_neg]
  ring

theorem cepe1_h2_neg (a : ℝ) (N : ℕ) (u : ℝ) : cepe1_h2 a N (-u) = -cepe1_h2 a N u := by
  unfold cepe1_h2
  rw [cepk1_ρ_neg]
  ring

theorem cepe1_drift_core {D : DynData 1} (hs : D.s = 0) {a : ℝ}
    (hM : D.M = -(a • (1 : Matrix (Fin 1) (Fin 1) ℝ))) {π : Equiv.Perm (Fin N)} {y : Fin N → Euc 1}
    (hso : cep_StrictlyOrdered π y) (k : Fin N) :
    liftedDrift D y (π k) 0 =
      -((cepe1_pairGrad (cepe1_h1 a N) (cep_toCh π y)) k) -
        ((cepe1_pairGrad (cepe1_h2 a N) (cep_toCh π y)) k +
          (gradient (Torus.lift D.V) (cepk1_ι (y (π k) 0))) 0) := by
  rw [cepe1_drift_coord hs hM, cepe1_pairGrad_apply, cepe1_pairGrad_apply]
  have hι : cepk1_ι (y (π k) 0) = y (π k) := by
    ext j
    have : j = 0 := Subsingleton.elim _ _
    subst this
    simp [cepk1_ι]
  rw [hι]
  set z : Fin N → ℝ := fun l => y (π l) 0 with hz
  set Q : Fin N → ℝ := fun l => (-a) * (-(Real.pi * (Real.cos (Real.pi * (z k - z l)) /
        Real.sin (Real.pi * (z k - z l)))) + cepk1_ρ (z k - z l)) with hQ
  have hsum : ∑ l ∈ Finset.univ.erase k, Q l =
      ∑ j ∈ Finset.univ.erase (π k), (-a) * (periodicRieszGrad 1 0 (Torus.mk (y (π k) - y j))) 0 := by
    refine Finset.sum_equiv π (by simp) fun l hl => ?_
    rw [cepe1_force hso (Finset.ne_of_mem_erase hl).symm]
  rw [← hsum, cepe1_sum_erase_split]
  have hR : ∀ l, (1 / (N : ℝ)) * Q l = -cepe1_h1 a N (z k - z l) - cepe1_h2 a N (z k - z l) := by
    intro l
    simp only [hQ, cepe1_h1, cepe1_h2]
    ring
  have hA : (1 / (N : ℝ)) * ∑ l, (if l < k then Q l else 0) =
      -(∑ l, if l < k then cepe1_h1 a N (z k - z l) else 0) -
        ∑ l, if l < k then cepe1_h2 a N (z k - z l) else 0 := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hl : l < k
    · simp only [hl, ite_true, hR]
    · simp [hl]
  have hB : (1 / (N : ℝ)) * ∑ l, (if k < l then Q l else 0) =
      (∑ l, if k < l then cepe1_h1 a N (z l - z k) else 0) +
        ∑ l, if k < l then cepe1_h2 a N (z l - z k) else 0 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hl : k < l
    · have e : z l - z k = -(z k - z l) := by ring
      simp only [hl, ite_true, hR, e, cepe1_h1_neg, cepe1_h2_neg]
      ring
    · simp [hl]
  have hz' : ∀ l, (cep_toCh π y) l = z l := fun l => rfl
  simp only [hz']
  rw [mul_add, hA, hB]
  ring

end HRS.MC.CepE1

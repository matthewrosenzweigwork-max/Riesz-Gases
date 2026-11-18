import HRS.MC.CepE1Aux3
import HRS.Stochastic.Bridge

/-!
# Packet CEPE1, auxiliary 4: the lifted drift in rank coordinates
-/

open Set
open scoped NNReal RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE1

open HRS HRS.MC.CepK1

/-- Copy of `HRS.MC.Cepa.cep_IsC11`. -/
def cep_IsC11 {d : ℕ} (V : Torus d → ℝ) : Prop :=
  Torus.IsCk 1 V ∧ ∃ L : ℝ≥0, LipschitzWith L (gradient (Torus.lift V))

/-- Copy of `HRS.MC.Cepa.cep_rank`. -/
def cep_rank {N : ℕ} (π : Equiv.Perm (Fin N)) (y : Fin N → Euc 1) : Fin N → ℝ :=
  fun k => y (π k) 0

/-- Copy of `HRS.MC.Cepa.cep_StrictlyOrdered`. -/
def cep_StrictlyOrdered {N : ℕ} (π : Equiv.Perm (Fin N)) (y : Fin N → Euc 1) : Prop :=
  (∀ k k' : Fin N, k < k' → y (π k) 0 < y (π k') 0) ∧
    ∀ k k' : Fin N, y (π k') 0 < y (π k) 0 + 1

/-- Copy of `HRS.MC.Cepa.cep_chamberPot`. -/
def cep_chamberPot (a : ℝ) (N : ℕ) (z : Ch N) : ℝ :=
  (a / N) * ∑ k : Fin N, ∑ l : Fin N,
    if k < l then -Real.log (2 * Real.sin (Real.pi * (z l - z k))) else 0

/-- Copy of `HRS.MC.Cepa.cep_toCh`. -/
def cep_toCh {N : ℕ} (π : Equiv.Perm (Fin N)) (y : Fin N → Euc 1) : Ch N :=
  WithLp.toLp 2 (cep_rank π y)

variable {N : ℕ}

theorem cepe1_toCh_apply (π : Equiv.Perm (Fin N)) (y : Fin N → Euc 1) (k : Fin N) :
    (cep_toCh π y) k = y (π k) 0 := rfl

theorem cepe1_sub_mk (x y : Euc 1) : Torus.mk x - Torus.mk y = Torus.mk (x - y) := by
  funext i
  simp [Torus.mk]

theorem cepe1_diff {π : Equiv.Perm (Fin N)} {y : Fin N → Euc 1} (hso : cep_StrictlyOrdered π y)
    {k l : Fin N} (hkl : k < l) : 0 < y (π l) 0 - y (π k) 0 ∧ y (π l) 0 - y (π k) 0 < 1 :=
  ⟨by linarith [hso.1 k l hkl], by linarith [hso.2 k l]⟩

theorem cepe1_noint {u : ℝ} (h0 : 0 < |u|) (h1 : |u| < 1) : ∀ n : ℤ, u ≠ n := by
  intro n hn
  subst hn
  rcases lt_trichotomy n 0 with h | h | h
  · have : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt h
    rw [abs_of_neg (by exact_mod_cast h)] at h1
    linarith
  · simp [h] at h0
  · have : (1 : ℝ) ≤ n := by exact_mod_cast h
    rw [abs_of_pos (by exact_mod_cast h)] at h1
    linarith

theorem cepe1_force {π : Equiv.Perm (Fin N)} {y : Fin N → Euc 1} (hso : cep_StrictlyOrdered π y)
    {k l : Fin N} (hne : k ≠ l) :
    (periodicRieszGrad 1 0 (Torus.mk (y (π k) - y (π l)))) 0 =
      -(Real.pi * (Real.cos (Real.pi * (y (π k) 0 - y (π l) 0)) /
        Real.sin (Real.pi * (y (π k) 0 - y (π l) 0)))) +
        cepk1_ρ (y (π k) 0 - y (π l) 0) := by
  have hn : ∀ n : ℤ, (y (π k) - y (π l)) 0 ≠ n := by
    simp only [PiLp.sub_apply]
    rcases lt_or_gt_of_ne hne with h | h
    · obtain ⟨h1, h2⟩ := cepe1_diff hso h
      refine cepe1_noint ?_ ?_
      · rw [abs_pos]; linarith
      · rw [abs_of_neg (by linarith)]; linarith
    · obtain ⟨h1, h2⟩ := cepe1_diff hso h
      refine cepe1_noint ?_ ?_
      · rw [abs_pos]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
  have := cepk1_ρ_eq_off (y := y (π k) - y (π l)) hn
  simpa using this

theorem cepe1_drift_coord {D : DynData 1} (hs : D.s = 0) {a : ℝ}
    (hM : D.M = -(a • (1 : Matrix (Fin 1) (Fin 1) ℝ))) (y : Fin N → Euc 1) (i : Fin N) :
    liftedDrift D y i 0 =
      (1 / (N : ℝ)) * ∑ j ∈ Finset.univ.erase i, (-a) * (periodicRieszGrad 1 0 (Torus.mk (y i - y j))) 0 -
        (gradient (Torus.lift D.V) (y i)) 0 := by
  unfold liftedDrift particleDrift
  simp only [PiLp.sub_apply, PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply, smul_eq_mul, hs]
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [cepe1_matVec hM, cepe1_sub_mk]
  · unfold Torus.grad
    rw [cepe1_gradient_mk_eq (V := D.V) (x := y i) (x' := Torus.rep (Torus.mk (y i)))
      (Torus.mk_rep (Torus.mk (y i))).symm]

theorem cepe1_sum_erase_split (k : Fin N) (G : Fin N → ℝ) :
    ∑ l ∈ Finset.univ.erase k, G l =
      (∑ l, if l < k then G l else 0) + ∑ l, if k < l then G l else 0 := by
  rw [← Finset.sum_add_distrib]
  rw [← Finset.sum_subset (Finset.erase_subset k Finset.univ)]
  · refine Finset.sum_congr rfl fun l hl => ?_
    have hlk : l ≠ k := Finset.ne_of_mem_erase hl
    rcases lt_or_gt_of_ne hlk with h | h
    · simp [h, not_lt.2 h.le]
    · simp [h, not_lt.2 h.le]
  · intro l _ hl
    have : l = k := by simpa using hl
    subst this
    simp

end HRS.MC.CepE1

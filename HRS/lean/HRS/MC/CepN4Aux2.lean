import Mathlib
import HRS.MC.CepN4Aux1
import HRS.Stochastic.Particle

/-!
# Packet CEPN4 (aux 2): coordinate formula of the lifted drift and the explicit gap remainder

For `D.s = 0`, `D.M = -a`: `(liftedDrift D y i) 0 = (1/N) ∑_{j ≠ i} h(y_i - y_j) - gV(y_i)` with
`h(u) = a (π cot(π u) - ρ(u))` (K1: `∇g = -π cot + ρ`), and the explicit remainder `cepn4_E`
`= (b_{i1} - b_{i0}) - (2a/N)/(y_{i1} - y_{i0})`, bounded on `r`-isolated configurations with gap in `(0,1/4)`.
-/

open MeasureTheory Filter Topology Set
open scoped BigOperators

noncomputable section

namespace HRS.MC.CepN4

open HRS Real

variable {N : ℕ}

def cepn4_h (a : ℝ) (ρ : ℝ → ℝ) (u : ℝ) : ℝ := a * (π * (Real.cos (π * u) / Real.sin (π * u)) - ρ u)

def cepn4_bdrift (a : ℝ) (ρ : ℝ → ℝ) (V : Torus 1 → ℝ) (y : Fin N → Euc 1) (i : Fin N) : ℝ :=
  (1 / (N : ℝ)) * ∑ j ∈ Finset.univ.erase i, cepn4_h a ρ (y i 0 - y j 0) - cepn4_gV V (y i)

def cepn4_E (a : ℝ) (ρ : ℝ → ℝ) (V : Torus 1 → ℝ) (y : Fin N → Euc 1) (i0 i1 : Fin N) : ℝ :=
  (cepn4_bdrift a ρ V y i1 - cepn4_bdrift a ρ V y i0) - (2 * a / N) / (y i1 0 - y i0 0)

lemma cepn4_h_neg (a : ℝ) (ρ : ℝ → ℝ) (hρ : ∀ u, ρ (-u) = -ρ u) (u : ℝ) :
    cepn4_h a ρ (-u) = - cepn4_h a ρ u := by
  unfold cepn4_h
  rw [hρ, mul_neg, Real.cos_neg, Real.sin_neg, div_neg]
  ring

lemma cepn4_mk_sub (x y : Euc 1) : Torus.mk x - Torus.mk y = Torus.mk (x - y) := by
  funext i
  simp [Torus.mk]

lemma cepn4_ne_int {y : Fin N → Euc 1} (hy : y ∈ liftedFree 1 N) {i j : Fin N} (hij : i ≠ j)
    (n : ℤ) : y i 0 - y j 0 ≠ n := by
  intro h
  apply hy
  refine ⟨i, j, hij, ?_⟩
  have : y i - y j = ((n : ℝ)) • (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) := by
    ext k
    have : k = 0 := Subsingleton.elim _ _
    subst this
    simpa using h
  funext k
  have hk : k = 0 := Subsingleton.elim _ _
  subst hk
  have h2 : y i 0 = y j 0 + n := by linarith
  simp only [Torus.mk]
  rw [h2]
  simp

lemma cepn4_drift_comp {D : DynData 1} (hs : D.s = 0) {a : ℝ}
    (hM : D.M = -(a • (1 : Matrix (Fin 1) (Fin 1) ℝ))) {ρ : ℝ → ℝ}
    (hρ : ∀ y : Euc 1, (∀ n : ℤ, y 0 ≠ n) → (periodicRieszGrad 1 0 (Torus.mk y)) 0 =
      -(Real.pi * (Real.cos (Real.pi * y 0) / Real.sin (Real.pi * y 0))) + ρ (y 0))
    {y : Fin N → Euc 1} (hy : y ∈ liftedFree 1 N) (i : Fin N) :
    (liftedDrift D y i) 0 = cepn4_bdrift a ρ D.V y i := by
  unfold liftedDrift particleDrift cepn4_bdrift cepn4_gV
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  rw [hs]
  congr 1
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hji : i ≠ j := (Finset.ne_of_mem_erase hj).symm
  rw [cepn4_mk_sub]
  have hne := cepn4_ne_int hy hji
  have hK := hρ (y i - y j) (fun n => by simpa using hne n)
  have hmv : ∀ v : Euc 1, (Torus.matVec D.M v) 0 = -a * v 0 := by
    intro v
    rw [hM]
    simp [Torus.matVec, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
  rw [hmv, hK]
  simp only [PiLp.sub_apply] 
  unfold cepn4_h
  ring

end HRS.MC.CepN4

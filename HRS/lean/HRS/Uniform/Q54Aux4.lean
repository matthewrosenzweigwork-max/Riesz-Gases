import HRS.PDE.EnergyTorus
import HRS.PDE.GalerkinLimit
import HRS.Uniform.Q54Aux3

/-!
# Q54, part 4: the matrix of the forward generator on trigonometric polynomials and its decay

For a trigonometric polynomial `v` (support in a box `B`), `forwardGen D μ v k = ν (-4π²|k|²) v k + ∑_{l∈B} E k l v l` with the
entries `E = genEntry D μ`: the Fourier matrix of transport and interaction,
`E k l = ∑_j b̂_j(k-l) 2πi l_j - ∑_{i,j} M_{ji} (2πi k_i) ĝ(k) μ̂(k-l) 2πi l_j`.
Under coefficient decay of `μ̂`, `V̂`, `‖E k l‖ ≤ A ⟨k-l⟩^{-L} ⟨l⟩^{θ'}` with `θ' = max(1, s+2-d) < 2`
(TeX (P:eq:fourier-operator), L2551-2557).
-/

noncomputable section

open Finset

namespace HRS.Uniform.Q54

open HRS HRS.PDE

variable {d : ℕ}

/-- the entries of the Fourier matrix of `b·∇ - 𝒢`. -/
def genEntry (D : DynData d) (μ : Torus d → ℝ) (k l : Lattice d) : ℂ :=
  (∑ j : Fin d, driftCoeff D μ j (k - l) * (2 * Real.pi * Complex.I * (l j : ℂ))) -
    ∑ i : Fin d, ∑ j : Fin d, ((D.M j i : ℝ) : ℂ) * ((2 * Real.pi * Complex.I * (k i : ℂ)) *
      (((rieszCoeff d D.s k : ℝ) : ℂ) * (coeffOf μ (k - l) * (2 * Real.pi * Complex.I * (l j : ℂ)))))

theorem mulCoeff_trig {n : ℕ} (a v : Coeff d) (hv : IsTrigPoly n v) (k : Lattice d) :
    mulCoeff a v k = ∑ l ∈ boxFin d n, a (k - l) * v l := by
  unfold mulCoeff
  refine tsum_eq_sum fun l hl => ?_
  rw [eq_zero_of_isTrigPoly hv hl, mul_zero]

theorem forwardGen_trig_eq (D : DynData d) (μ : Torus d → ℝ) {n : ℕ} (v : Coeff d)
    (hv : IsTrigPoly n v) (k : Lattice d) :
    forwardGen D μ v k = ((D.invβ : ℝ) : ℂ) * laplaceCoeff v k +
      ∑ l ∈ boxFin d n, genEntry D μ k l * v l := by
  have hder : ∀ j : Fin d, IsTrigPoly n (derivCoeff j v) := by
    intro j l hl
    apply hv l
    intro h0
    apply hl
    simp [derivCoeff, h0]
  have hmc : ∀ (a : Coeff d) (j : Fin d) (k : Lattice d),
      mulCoeff a (derivCoeff j v) k = ∑ l ∈ boxFin d n, a (k - l) * derivCoeff j v l :=
    fun a j k => mulCoeff_trig a _ (hder j) k
  unfold forwardGen transportCoeff nonlocalCoeff gradRieszCoeff rieszMult
  simp only [hmc]
  unfold genEntry
  simp only [derivCoeff]
  rw [add_sub_assoc]
  congr 1
  simp only [Finset.sum_mul, Finset.mul_sum, sub_mul]
  rw [Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  · refine (Finset.sum_congr rfl (fun x _ => Finset.sum_comm)).trans ?_
    refine Finset.sum_comm.trans ?_
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun b _ => ?_
    ring

end HRS.Uniform.Q54

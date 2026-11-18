import HRS.Commutator.Torus.NRSTAux45

/-!
# NRS-T, part 46: evaluation of each term of the pairing
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace
  ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS HRS.Commutator.TorusNote.NRST

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- The rescaled integrand of a term. -/
def nrstr_Hs (σ N : ℝ) (k l : Lattice d) (c : Fin d) (η : 𝔼) : ℂ :=
  ((((2 * Real.pi * ‖Lattice.toEuc k + N⁻¹ • η‖) ^ (2 * σ) * (((l c : ℤ) : ℝ) - N⁻¹ * η c) : ℝ)) : ℂ) *
    (nrstr_theta0 (d := d) η) ^ 2

/-- The rescaled integral of a term. -/
def nrstr_S (σ N : ℝ) (k l : Lattice d) (c : Fin d) : ℂ := ∫ η : 𝔼, nrstr_Hs σ N k l c η

lemma nrstr_tm_shift (σ : ℝ) (h : NRST.TPA d) (V : Fin d → NRST.TPA d) {N : ℝ} (hN : 0 < N)
    (k : Lattice d) (c : Fin d) (j : Lattice d) (η : 𝔼) :
    nrstr_tm σ h V N k c j (Lattice.toEuc k + N⁻¹ • η) =
      (((N ^ d : ℝ) : ℂ) ^ 2 * h.coeff k * h.coeff (-j - k) * (V c).coeff j *
        (2 * Real.pi * Complex.I)) * nrstr_Hs σ N k (-j - k) c η := by
  have hN' : N ≠ 0 := hN.ne'
  have e1 : N • (Lattice.toEuc k + N⁻¹ • η - Lattice.toEuc k) = η := by
    rw [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hN', one_smul]
  have e2 : -(Lattice.toEuc k + N⁻¹ • η) - Lattice.toEuc j = Lattice.toEuc (-j - k) - N⁻¹ • η := by
    rw [nrstr_toEuc_neg_sub]; abel
  have e3 : N • (Lattice.toEuc (-j - k) - N⁻¹ • η - Lattice.toEuc (-j - k)) = -η := by
    rw [sub_sub_cancel_left, smul_neg, smul_smul, mul_inv_cancel₀ hN', one_smul]
  unfold nrstr_tm nrstr_a nrstr_w nrstr_Hs
  rw [e1, e2, e3, nrstr_theta0_neg]
  have e4 : ((Lattice.toEuc (-j - k) - N⁻¹ • η) c : ℝ) = (((-j - k) c : ℤ) : ℝ) - N⁻¹ * η c := by
    simp [Lattice.toEuc]
  rw [e4]
  push_cast
  ring

lemma nrstr_tm_integral (σ : ℝ) (h : NRST.TPA d) (V : Fin d → NRST.TPA d) {N : ℝ} (hN : 0 < N)
    (k : Lattice d) (c : Fin d) (j : Lattice d) :
    ∫ ξ, nrstr_tm σ h V N k c j ξ =
      ((N ^ d : ℝ) : ℂ) * (h.coeff k * (V c).coeff j * h.coeff (-j - k) * (2 * Real.pi * Complex.I)) *
        nrstr_S σ N k (-j - k) c := by
  have hN' : N ≠ 0 := hN.ne'
  set C0 : ℂ := ((N ^ d : ℝ) : ℂ) ^ 2 * h.coeff k * h.coeff (-j - k) * (V c).coeff j *
        (2 * Real.pi * Complex.I) with hC0
  have hid : ∀ ξ : 𝔼, nrstr_tm σ h V N k c j ξ =
      (fun η : 𝔼 => C0 * nrstr_Hs σ N k (-j - k) c η) (N • (ξ - Lattice.toEuc k)) := by
    intro ξ
    have := nrstr_tm_shift σ h V hN k c j (N • (ξ - Lattice.toEuc k))
    have e : Lattice.toEuc k + N⁻¹ • N • (ξ - Lattice.toEuc k) = ξ := by
      rw [smul_smul, inv_mul_cancel₀ hN', one_smul]; abel
    rw [e] at this
    exact this
  have h1 := nrstr_int_scale (fun η : 𝔼 => C0 * nrstr_Hs σ N k (-j - k) c η) hN (Lattice.toEuc k)
  simp_rw [hid]
  rw [h1, integral_const_mul]
  unfold nrstr_S
  have hNd : ((N ^ d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (N ^ d : ℝ) ≠ 0)
  rw [hC0, Complex.real_smul]
  push_cast
  field_simp

end HRS.Commutator.TorusNote

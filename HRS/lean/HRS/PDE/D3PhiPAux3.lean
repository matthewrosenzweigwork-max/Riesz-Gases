import HRS.PDE.D3PhiPAux2

/-!
# D3PHIP, helper 3: the fixed-time dictionary between the `q^r`-integrals of packet A and `P`-integrals

Definitions of the per-point exponent integrand `A = u^{p} e^{m}`, `m = ψ - log Z`, its logarithmic factors and
derivative integrand `D`, and, for every `r ∈ [0,T]`, the identity
`∫ D_r dP = -Dir(r) + (p-1) ∫ S h^p dq + p'(r) ∫ h^p log h dq` (from `d3pp_green_fixed`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS

variable {n : ℕ}

/-- `c(r) = ∫ ψt e^ψ dP / Z̃_r = E_{q^r} ψt` (the logarithmic derivative of `Z̃`). -/
def d3pp_c (κ : ℝ) (U : Torus n → ℝ) (ψ ψt : ℝ → Torus n → ℝ) (r : ℝ) : ℝ :=
  (∫ x, ψt r x * Real.exp (ψ r x) ∂(d1_gibbsMeasure κ U)) / d3phi_Z κ U ψ r

/-- `ℓ = log h`. -/
def d3pp_ell (κ : ℝ) (U : Torus n → ℝ) (ψ w : ℝ → Torus n → ℝ) (r : ℝ) (x : Torus n) : ℝ :=
  Real.log (d3phi_h κ U ψ w r x)

/-- `m = ψ - log Z̃`. -/
def d3pp_m (κ : ℝ) (U : Torus n → ℝ) (ψ : ℝ → Torus n → ℝ) (r : ℝ) (x : Torus n) : ℝ :=
  ψ r x - Real.log (d3phi_Z κ U ψ r)

/-- `∂_r ℓ = L w / w - ψt + c`. -/
def d3pp_ellr (κ : ℝ) (U : Torus n → ℝ) (ψ ψt w : ℝ → Torus n → ℝ) (r : ℝ) (x : Torus n) : ℝ :=
  d1_gen κ (d1_gradDrift U) (w r) x / w r x - ψt r x + d3pp_c κ U ψ ψt r

/-- `∂_r m = ψt - c`. -/
def d3pp_mr (κ : ℝ) (U : Torus n → ℝ) (ψ ψt : ℝ → Torus n → ℝ) (r : ℝ) (x : Torus n) : ℝ :=
  ψt r x - d3pp_c κ U ψ ψt r

/-- `A = h^p e^m = h^p e^ψ / Z̃`: the density, against `P`, of `h^p dq`. -/
def d3pp_A (κ : ℝ) (U : Torus n → ℝ) (ψ w : ℝ → Torus n → ℝ) (p : ℝ → ℝ) (r : ℝ) (x : Torus n) : ℝ :=
  d3phi_h κ U ψ w r x ^ p r * Real.exp (d3pp_m κ U ψ r x)

/-- `D = A (p' ℓ + p ∂_rℓ + ∂_r m)`: the `r`-derivative of `A` along an exponent path with derivative `pd`. -/
def d3pp_D (κ : ℝ) (U : Torus n → ℝ) (ψ ψt w : ℝ → Torus n → ℝ) (p pd : ℝ → ℝ) (r : ℝ) (x : Torus n) : ℝ :=
  d3pp_A κ U ψ w p r x *
    (pd r * d3pp_ell κ U ψ w r x + (p r * d3pp_ellr κ U ψ ψt w r x + d3pp_mr κ U ψ ψt r x))

section fixed

variable {κ : ℝ} {U : Torus n → ℝ} {T : ℝ} {w : ℝ → Torus n → ℝ} {ψ ψt : ℝ → Torus n → ℝ} {r : ℝ}
  {x : Torus n}

theorem d3pp_h_eq (κ : ℝ) (U : Torus n → ℝ) (ψ w : ℝ → Torus n → ℝ) (r : ℝ) :
    d3phi_h κ U ψ w r = d3pp_u (w r) (ψ r) (d3phi_Z κ U ψ r) := rfl

theorem d3pp_exp_m (κ : ℝ) (U : Torus n → ℝ) (ψ : ℝ → Torus n → ℝ) {r : ℝ} (hZ : 0 < d3phi_Z κ U ψ r)
    (x : Torus n) :
    Real.exp (d3pp_m κ U ψ r x) = Real.exp (ψ r x) / d3phi_Z κ U ψ r := by
  unfold d3pp_m
  rw [Real.exp_sub, Real.exp_log hZ]

/-- `A = u^{s-1} w`. -/
theorem d3pp_A_eq (hZ : 0 < d3phi_Z κ U ψ r) (hwpos : 0 < w r x) (p : ℝ → ℝ) :
    d3pp_A κ U ψ w p r x = d3phi_h κ U ψ w r x ^ (p r - 1) * w r x := by
  unfold d3pp_A
  have hu : 0 < d3phi_h κ U ψ w r x := mul_pos (mul_pos hwpos hZ) (Real.exp_pos _)
  rw [d3pp_exp_m κ U ψ hZ, Real.rpow_sub_one hu.ne']
  unfold d3phi_h
  have := hu.ne'
  have := hZ.ne'
  have := (Real.exp_pos (ψ r x)).ne'
  have h2 : Real.exp (-ψ r x) = (Real.exp (ψ r x))⁻¹ := Real.exp_neg _
  have hu' : w r x * d3phi_Z κ U ψ r * Real.exp (-ψ r x) ≠ 0 := by
    unfold d3phi_h at hu; exact hu.ne'
  rw [h2] at hu' ⊢
  field_simp

end fixed

end HRS

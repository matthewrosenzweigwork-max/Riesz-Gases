import HRS.PDE.EnergyR2Fn
import HRS.PDE.GStructure

/-!
# Regime R2: Leibniz decomposition of `⟨∂^α𝒢[F], ∂^αF⟩` and the structure of each term
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.R2Aux

variable {d : ℕ}

theorem symPart_apply (M : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) :
    Torus.symPart M i j = (M i j + M j i) / 2 := by
  simp [Torus.symPart, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply]
  ring

theorem sum_M_eq_symPart (M : Matrix (Fin d) (Fin d) ℝ) (e : Fin d → ℝ) :
    ∑ i, ∑ j, M j i * (e i * e j) = ∑ i, ∑ j, Torus.symPart M i j * (e i * e j) := by
  have h1 : ∑ i, ∑ j, M j i * (e i * e j) = ∑ i, ∑ j, M i j * (e i * e j) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have : 2 * ∑ i, ∑ j, M j i * (e i * e j) = 2 * ∑ i, ∑ j, Torus.symPart M i j * (e i * e j) := by
    calc 2 * ∑ i, ∑ j, M j i * (e i * e j)
        = ∑ i, ∑ j, M j i * (e i * e j) + ∑ i, ∑ j, M i j * (e i * e j) := by rw [← h1]; ring
      _ = ∑ i, ∑ j, (M j i + M i j) * (e i * e j) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => by
            rw [← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun j _ => by ring
      _ = _ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ => by rw [symPart_apply]; ring
  linarith

/-- The symmetric part against `e ⊗ e`, through the spectral data. -/
theorem sum_symPart_ee (M : Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ) (q : Fin d → Euc d)
    (hdiag : ∀ i j, Torus.symPart M i j = -∑ l, lam l * q l i * q l j) (e : Fin d → ℝ) :
    ∑ i, ∑ j, Torus.symPart M i j * (e i * e j) = -∑ l, lam l * (∑ i, q l i * e i) ^ 2 := by
  simp_rw [hdiag]
  have : ∀ i j, -(∑ l, lam l * q l i * q l j) * (e i * e j) =
      -∑ l, lam l * (q l i * e i) * (q l j * e j) := by
    intro i j
    rw [neg_mul, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun l _ => by ring
  simp_rw [this]
  have e1 : ∑ i, ∑ j, -∑ l, lam l * (q l i * e i) * (q l j * e j) =
      -∑ l, ∑ i, ∑ j, lam l * (q l i * e i) * (q l j * e j) := by
    simp only [Finset.sum_neg_distrib]
    congr 1
    calc ∑ i, ∑ j, ∑ l, lam l * (q l i * e i) * (q l j * e j)
        = ∑ i, ∑ l, ∑ j, lam l * (q l i * e i) * (q l j * e j) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [e1]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem sum_M_ee (M : Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ) (q : Fin d → Euc d)
    (hdiag : ∀ i j, Torus.symPart M i j = -∑ l, lam l * q l i * q l j) (e : Fin d → ℝ) :
    ∑ i, ∑ j, M j i * (e i * e j) = -∑ l, lam l * (∑ i, q l i * e i) ^ 2 := by
  rw [sum_M_eq_symPart, sum_symPart_ee M lam q hdiag e]

/-- The symbol `2πi k_i ĝ(k)` of `∂_i g *`. -/
def Ssym (d : ℕ) (s : ℝ) (i : Fin d) (k : Lattice d) : ℂ :=
  (2 * Real.pi * Complex.I * (k i : ℂ)) * ((rieszCoeff d s k : ℝ) : ℂ)

theorem gradRieszCoeff_apply (s : ℝ) (i : Fin d) (c : Coeff d) (k : Lattice d) :
    gradRieszCoeff d s i c k = Ssym d s i k * c k := by
  unfold gradRieszCoeff derivCoeff rieszMult Ssym
  ring

/-- Integration by parts in the nonlocal term: for any coefficient `a` and trigonometric
polynomial `f`,
`∑ M_{ji} ∂_i g*(a ∂_j f) = ∑_l λ_l K_l(a f) - ∑ M_{ji} ∂_i g*(f-part with ∂_j a)`. -/
theorem ct_decomp {n : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (s : ℝ) (lam : Fin d → ℝ)
    (q : Fin d → Euc d)
    (hdiag : ∀ i j, Torus.symPart M i j = -∑ l, lam l * q l i * q l j) (a f : Coeff d)
    (hf : IsTrigPoly n f) (k : Lattice d) :
    ∑ i, ∑ j, ((M j i : ℝ) : ℂ) * gradRieszCoeff d s i (mulCoeff a (derivCoeff j f)) k =
      ∑ l, ((lam l : ℝ) : ℂ) * (((symbolK d s (q l) k : ℝ) : ℂ) * mulCoeff a f k) -
      ∑ i, ∑ j, ((M j i : ℝ) : ℂ) * (Ssym d s i k * mulCoeff (derivCoeff j a) f k) := by
  set U := mulCoeff a f k with hU
  set R : Fin d → ℂ := fun j => mulCoeff (derivCoeff j a) f k with hR
  set e : Fin d → ℝ := fun i => 2 * Real.pi * (k i : ℝ) with he
  set g : ℝ := rieszCoeff d s k with hg
  have hP : ∀ j, mulCoeff a (derivCoeff j f) k = (e j : ℂ) * Complex.I * U - R j := by
    intro j
    have := derivCoeff_mulCoeff j a f hf k
    have h2 : derivCoeff j (mulCoeff a f) k = 2 * Real.pi * Complex.I * (k j : ℂ) * U := rfl
    rw [h2] at this
    simp only [hR, he]
    push_cast
    linear_combination -this
  have h1 : ∀ i j, ((M j i : ℝ) : ℂ) * gradRieszCoeff d s i (mulCoeff a (derivCoeff j f)) k =
      ((M j i : ℝ) : ℂ) * ((Ssym d s i k * ((e j : ℂ) * Complex.I * U)) -
        Ssym d s i k * R j) := by
    intro i j
    rw [gradRieszCoeff_apply, hP j]
    ring
  simp_rw [h1]
  have h2 : ∀ i j, ((M j i : ℝ) : ℂ) * ((Ssym d s i k * ((e j : ℂ) * Complex.I * U)) -
        Ssym d s i k * R j) =
      -(((M j i * (e i * e j) : ℝ) : ℂ) * ((g : ℂ) * U)) -
        ((M j i : ℝ) : ℂ) * (Ssym d s i k * R j) := by
    intro i j
    simp only [Ssym, he, hg]
    push_cast
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination (((M j i : ℝ) : ℂ) * (2 * (Real.pi : ℂ) * (k i : ℂ)) *
      (2 * (Real.pi : ℂ) * (k j : ℂ)) * (g : ℂ) * U) * hI
  simp_rw [h2]
  simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  have h3 := sum_M_ee M lam q hdiag e
  have hK : ∀ l, symbolK d s (q l) k = (∑ i, q l i * e i) ^ 2 * g := by
    intro l
    unfold symbolK
    rw [inner_toEuc_eq, Finset.mul_sum]
    congr 2
    exact Finset.sum_congr rfl fun i _ => by simp only [he]; ring
  have h5 : ∑ x, ∑ x_1, ((M x_1 x * (e x * e x_1) : ℝ) : ℂ) * ((g : ℂ) * U) =
      ((∑ x, ∑ x_1, M x_1 x * (e x * e x_1) : ℝ) : ℂ) * ((g : ℂ) * U) := by
    push_cast
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_mul]
  rw [h5, h3]
  have h6 : ∑ l, ((lam l : ℝ) : ℂ) * (((symbolK d s (q l) k : ℝ) : ℂ) * U) =
      ((∑ l, lam l * (∑ i, q l i * e i) ^ 2 : ℝ) : ℂ) * ((g : ℂ) * U) := by
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hK l]
    push_cast
    ring
  rw [h6]
  push_cast
  ring


/-- The `β`-th Leibniz term of `∂^α 𝒢[F]` (coefficients). -/
def ct (D : DynData d) (μ : Torus d → ℝ) (α : Fin d → ℕ) (F : Coeff d) (β : Fin d → ℕ)
    (k : Lattice d) : ℂ :=
  ∑ i, ∑ j, ((D.M j i : ℝ) : ℂ) * gradRieszCoeff d D.s i
    (mulCoeff (multiDerivCoeff β (coeffOf μ)) (multiDerivCoeff (α - β) (derivCoeff j F))) k

theorem multiDerivCoeff_gradRiesz (α : Fin d → ℕ) (s : ℝ) (i : Fin d) (c : Coeff d) :
    multiDerivCoeff α (gradRieszCoeff d s i c) = gradRieszCoeff d s i (multiDerivCoeff α c) := by
  funext k
  simp only [multiDerivCoeff_apply, gradRieszCoeff_apply]
  ring

theorem multiDeriv_nonlocal {n : ℕ} (D : DynData d) (μ : Torus d → ℝ) (α : Fin d → ℕ)
    (F : Coeff d) (hF : IsTrigPoly n F) (k : Lattice d) :
    multiDerivCoeff α (nonlocalCoeff D μ F) k =
      ∑ β ∈ leibnizSet α, (binomW α β : ℂ) * ct D μ α F β k := by
  unfold nonlocalCoeff ct
  rw [multiDerivCoeff_apply, Finset.mul_sum]
  simp_rw [Finset.mul_sum, Finset.sum_comm (s := leibnizSet α)]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hc : IsTrigPoly n (derivCoeff j F) := by
    rw [derivCoeff_eq_multi]; exact isTrigPoly_multiDerivCoeff hF _
  have h1 : (∏ i, (2 * Real.pi * Complex.I * (k i : ℂ)) ^ (α i)) *
      (((D.M j i : ℝ) : ℂ) * gradRieszCoeff d D.s i (mulCoeff (coeffOf μ) (derivCoeff j F)) k) =
      ((D.M j i : ℝ) : ℂ) * gradRieszCoeff d D.s i
        (multiDerivCoeff α (mulCoeff (coeffOf μ) (derivCoeff j F))) k := by
    rw [gradRieszCoeff_apply, gradRieszCoeff_apply, multiDerivCoeff_apply]
    ring
  rw [h1]
  simp only [gradRieszCoeff_apply]
  rw [multiDerivCoeff_mulCoeff α _ _ hc k]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  ring


/-- The pairing of the `β`-th Leibniz term with `w = ∂^αF` over the box. -/
def PP (D : DynData d) (μ : Torus d → ℝ) (α : Fin d → ℕ) (F : Coeff d) (n : ℕ)
    (β : Fin d → ℕ) : ℂ :=
  ∑ k ∈ boxFin d n, conj (multiDerivCoeff α F k) * ct D μ α F β k

theorem re_bilin_leibniz {n : ℕ} (D : DynData d) (μ : Torus d → ℝ) (α : Fin d → ℕ)
    (F : Coeff d) (hF : IsTrigPoly n F) :
    (bilinForm (fun k => ∏ i, (2 * Real.pi * (k i : ℝ)) ^ (2 * α i)) (nonlocalCoeff D μ F) F).re =
      ∑ β ∈ leibnizSet α, (binomW α β : ℝ) * (PP D μ α F n β).re := by
  rw [bilinForm_weight_eq α _ F hF]
  simp_rw [multiDeriv_nonlocal D μ α F hF, Finset.mul_sum]
  rw [Finset.sum_comm, Complex.re_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  unfold PP
  have : ∀ k, conj (multiDerivCoeff α F k) * ((binomW α β : ℂ) * ct D μ α F β k) =
      ((binomW α β : ℝ) : ℂ) * (conj (multiDerivCoeff α F k) * ct D μ α F β k) := by
    intro k; push_cast; ring
  simp_rw [this]
  rw [← Finset.mul_sum, Complex.re_ofReal_mul]

theorem ct_zero (D : DynData d) (μ : Torus d → ℝ) (α : Fin d → ℕ) (F : Coeff d) (k : Lattice d) :
    ct D μ α F 0 k = nonlocalCoeff D μ (multiDerivCoeff α F) k := by
  unfold ct nonlocalCoeff
  simp only [multiDerivCoeff_zero, tsub_zero, multiDerivCoeff_derivCoeff]


theorem sum_q_mul_q_sq (q : Fin d → Euc d) (hq : Orthonormal ℝ q) (l l0 : Fin d) :
    (∑ i, q l i * q l0 i) ^ 2 = if l = l0 then 1 else 0 := by
  have h := (orthonormal_iff_ite.mp hq) l l0
  have e : inner ℝ (q l) (q l0) = ∑ i, q l i * q l0 i := by
    simp only [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_comm]
  rw [e] at h
  rw [h]
  split_ifs <;> simp

theorem lam_eq (M : Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ) (q : Fin d → Euc d)
    (hdiag : ∀ i j, Torus.symPart M i j = -∑ l, lam l * q l i * q l j) (hq : Orthonormal ℝ q)
    (l0 : Fin d) : lam l0 = -∑ i, ∑ j, Torus.symPart M i j * (q l0 i * q l0 j) := by
  rw [sum_symPart_ee M lam q hdiag (fun i => q l0 i)]
  simp_rw [sum_q_mul_q_sq q hq _ l0]
  simp

theorem lam_eq_zero (M : Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ) (q : Fin d → Euc d)
    (hdiag : ∀ i j, Torus.symPart M i j = -∑ l, lam l * q l i * q l j) (hq : Orthonormal ℝ q)
    (h0 : Torus.symPart M = 0) (l0 : Fin d) : lam l0 = 0 := by
  rw [lam_eq M lam q hdiag hq l0]
  simp [h0]

theorem lam_le (hd : 1 ≤ d) (MB : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (hM : MatBound MB M)
    (lam : Fin d → ℝ) (q : Fin d → Euc d)
    (hdiag : ∀ i j, Torus.symPart M i j = -∑ l, lam l * q l i * q l j) (hq : Orthonormal ℝ q)
    (l0 : Fin d) : lam l0 ≤ d * MB := by
  rw [lam_eq M lam q hdiag hq l0]
  have hMB : 0 ≤ MB := (abs_nonneg _).trans (hM ⟨0, hd⟩ ⟨0, hd⟩)
  have hsp : ∀ i j, |Torus.symPart M i j| ≤ MB := by
    intro i j
    rw [symPart_apply, abs_div, abs_two]
    have := abs_add_le (M i j) (M j i)
    have := hM i j
    have := hM j i
    linarith
  have hn : ∑ i, q l0 i ^ 2 = 1 := by
    have h := hq.1 l0
    rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at h
    simpa using h
  have h1 : ∑ i, ∑ j, |q l0 i| * |q l0 j| = (∑ i, |q l0 i|) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
  have h2 : (∑ i, |q l0 i|) ^ 2 ≤ d := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d))) (f := fun i => |q l0 i|)
    simp only [sq_abs, Finset.card_univ, Fintype.card_fin, hn, mul_one] at this
    exact this
  calc -∑ i, ∑ j, Torus.symPart M i j * (q l0 i * q l0 j)
      ≤ |∑ i, ∑ j, Torus.symPart M i j * (q l0 i * q l0 j)| := neg_le_abs _
    _ ≤ ∑ i, ∑ j, |Torus.symPart M i j * (q l0 i * q l0 j)| :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ =>
          Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, MB * (|q l0 i| * |q l0 j|) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_right (hsp i j) (by positivity)
    _ = MB * (∑ i, |q l0 i|) ^ 2 := by
        rw [← h1, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
    _ ≤ MB * d := mul_le_mul_of_nonneg_left h2 hMB
    _ = d * MB := by ring

end HRS.PDE.R2Aux

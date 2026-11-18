import HRS.MC.S7PIDRGrad

/-!
# Packet PI-D, `s7_PID_gradprod`: Fourier support and the Sobolev bound for `∇e_k·∇e_l`

By `S7PIDRGrad`, `∇e_k·∇e_l = K_{kl} σ_k σ_l` with `K_{kl} = 8π² (k·l)` and `σ_k = -sin` / `cos` of `2π k·x`, i.e.
`σ_k = a_k e_k + b_k e_{-k}` in complex exponentials.  So the complex Fourier coefficients `∫ e_{-n} ∇e_k·∇e_l`
vanish unless `n ∈ {±k ± l}`, and every such frequency has `⟨n⟩² ≤ 2⟨k⟩²⟨l⟩²`.  With Bessel
(`Torus.hasSum_sq_coeff`) this gives `∑_n ⟨n⟩^{2r} |φ̂(n)|² ≤ 2 (2⟨k⟩⟨l⟩²)^r ∫φ²`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIDR

open HRS HRS.Sec7 HRS.MC.Sec7.PID

variable {d : ℕ}

open Classical in
/-- Coefficient of `e_k` in `σ_k`. -/
def S7PIDR_ca (k : NonzeroLattice d) : ℂ := if Lattice.IsPosHalf k.1 then Complex.I / 2 else 1 / 2

open Classical in
/-- Coefficient of `e_{-k}` in `σ_k`. -/
def S7PIDR_cb (k : NonzeroLattice d) : ℂ := if Lattice.IsPosHalf k.1 then -Complex.I / 2 else 1 / 2

/-- The real constant `8π² (k·l)` of `∇e_k·∇e_l = K σ_k σ_l`. -/
def S7PIDR_K (k l : NonzeroLattice d) : ℝ :=
  8 * Real.pi ^ 2 * inner ℝ (Lattice.toEuc k.1) (Lattice.toEuc l.1)

theorem S7PIDR_gradProd_eq' (k l : NonzeroLattice d) (x : Torus d) :
    gradProd k l x = S7PIDR_K k l * (S7PIDR_sig k x * S7PIDR_sig l x) := by
  rw [S7PIDR_gradProd_eq]
  rfl

theorem S7PIDR_sig_cplx (k : NonzeroLattice d) (x : Torus d) :
    ((S7PIDR_sig k x : ℝ) : ℂ) = S7PIDR_ca k * Torus.mode k.1 x + S7PIDR_cb k * Torus.mode (-k.1) x := by
  rw [Torus.mode_neg]
  by_cases hp : Lattice.IsPosHalf k.1
  · unfold S7PIDR_sig S7PIDR_ca S7PIDR_cb Torus.sinMode
    simp only [hp, ↓reduceIte]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  · unfold S7PIDR_sig S7PIDR_ca S7PIDR_cb Torus.cosMode
    simp only [hp, ↓reduceIte]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

theorem S7PIDR_gradProd_cplx (k l : NonzeroLattice d) (x : Torus d) :
    ((gradProd k l x : ℝ) : ℂ) = (S7PIDR_K k l : ℂ) *
      ((S7PIDR_ca k * Torus.mode k.1 x + S7PIDR_cb k * Torus.mode (-k.1) x) *
        (S7PIDR_ca l * Torus.mode l.1 x + S7PIDR_cb l * Torus.mode (-l.1) x)) := by
  rw [S7PIDR_gradProd_eq', Complex.ofReal_mul, Complex.ofReal_mul, S7PIDR_sig_cplx, S7PIDR_sig_cplx]

/-- The four frequencies `±k ± l`. -/
def S7PIDR_InS (k l n : Lattice d) : Prop :=
  n = k + l ∨ n = k + -l ∨ n = -k + l ∨ n = -k + -l

theorem S7PIDR_four_int (n q1 q2 q3 q4 : Lattice d) (c1 c2 c3 c4 : ℂ)
    (h1 : q1 ≠ n) (h2 : q2 ≠ n) (h3 : q3 ≠ n) (h4 : q4 ≠ n) :
    ∫ x : Torus d, (c1 * Torus.mode (q1 + -n) x + c2 * Torus.mode (q2 + -n) x +
      c3 * Torus.mode (q3 + -n) x + c4 * Torus.mode (q4 + -n) x) = 0 := by
  have hi : ∀ (c : ℂ) (q : Lattice d), Integrable (fun x : Torus d => c * Torus.mode (q + -n) x) :=
    fun c q => (Torus.integrable_mode _).const_mul c
  have e1 : q1 + -n ≠ 0 := fun h => h1 (add_neg_eq_zero.mp h)
  have e2 : q2 + -n ≠ 0 := fun h => h2 (add_neg_eq_zero.mp h)
  have e3 : q3 + -n ≠ 0 := fun h => h3 (add_neg_eq_zero.mp h)
  have e4 : q4 + -n ≠ 0 := fun h => h4 (add_neg_eq_zero.mp h)
  have hA : Integrable (fun x : Torus d => c1 * Torus.mode (q1 + -n) x + c2 * Torus.mode (q2 + -n) x) :=
    (hi c1 q1).add (hi c2 q2)
  have hB : Integrable (fun x : Torus d => c1 * Torus.mode (q1 + -n) x + c2 * Torus.mode (q2 + -n) x +
      c3 * Torus.mode (q3 + -n) x) := hA.add (hi c3 q3)
  rw [integral_add hB (hi c4 q4), integral_add hA (hi c3 q3), integral_add (hi c1 q1) (hi c2 q2),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    Torus.integral_mode, Torus.integral_mode, Torus.integral_mode, Torus.integral_mode,
    if_neg e1, if_neg e2, if_neg e3, if_neg e4]
  ring

theorem S7PIDR_fourier_zero (k l : NonzeroLattice d) (n : Lattice d) (hn : ¬ S7PIDR_InS k.1 l.1 n) :
    ∫ x : Torus d, Torus.mode (-n) x * ((gradProd k l x : ℝ) : ℂ) = 0 := by
  have e : (fun x : Torus d => Torus.mode (-n) x * ((gradProd k l x : ℝ) : ℂ)) =
      fun x : Torus d => ((S7PIDR_K k l : ℂ) * (S7PIDR_ca k * S7PIDR_ca l)) * Torus.mode (k.1 + l.1 + -n) x +
        ((S7PIDR_K k l : ℂ) * (S7PIDR_ca k * S7PIDR_cb l)) * Torus.mode (k.1 + -l.1 + -n) x +
        ((S7PIDR_K k l : ℂ) * (S7PIDR_cb k * S7PIDR_ca l)) * Torus.mode (-k.1 + l.1 + -n) x +
        ((S7PIDR_K k l : ℂ) * (S7PIDR_cb k * S7PIDR_cb l)) * Torus.mode (-k.1 + -l.1 + -n) x := by
    funext x
    rw [S7PIDR_gradProd_cplx]
    simp only [Torus.mode_add]
    ring
  rw [e]
  exact S7PIDR_four_int n _ _ _ _ _ _ _ _
    (fun h => hn (Or.inl h.symm)) (fun h => hn (Or.inr (Or.inl h.symm)))
    (fun h => hn (Or.inr (Or.inr (Or.inl h.symm)))) (fun h => hn (Or.inr (Or.inr (Or.inr h.symm))))

theorem S7PIDR_c2_zero (k l : NonzeroLattice d) (n : Lattice d) (hn : ¬ S7PIDR_InS k.1 l.1 n)
    (hφ : Integrable (gradProd k l)) :
    Torus.cosCoeff (gradProd k l) n ^ 2 + Torus.sinCoeff (gradProd k l) n ^ 2 = 0 := by
  rw [← Torus.norm_sq_coeff hφ n, S7PIDR_fourier_zero k l n hn, norm_zero]
  ring

theorem S7PIDR_f_sq_le (φ : Torus d → ℝ) (n : NonzeroLattice d) :
    Torus.funRealCoeff φ n ^ 2 ≤ 2 * (Torus.cosCoeff φ n.1 ^ 2 + Torus.sinCoeff φ n.1 ^ 2) := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  by_cases hp : Lattice.IsPosHalf n.1
  · rw [Torus.funRealCoeff_eq, if_pos hp, mul_pow, h2]
    nlinarith [sq_nonneg (Torus.sinCoeff φ n.1)]
  · rw [Torus.funRealCoeff_eq, if_neg hp, mul_pow, h2]
    nlinarith [sq_nonneg (Torus.cosCoeff φ n.1)]

theorem S7PIDR_mean_eq_cos (φ : Torus d → ℝ) : Torus.cosCoeff φ 0 = Torus.mean φ := by
  simp only [Torus.cosCoeff, Torus.mean, Torus.cosMode, Torus.mode_zero, Complex.one_re, one_mul]

theorem S7PIDR_rpow_sq (a : ℝ) (ha : 0 ≤ a) (r : ℝ) : a ^ (2 * r) = (a ^ 2) ^ r := by
  rw [Real.rpow_mul ha, Real.rpow_two]

theorem S7PIDR_jp_sq_le_of_InS (k l n : Lattice d) (h : S7PIDR_InS k l n) :
    Lattice.jp n ^ 2 ≤ 2 * (Lattice.jp k * Lattice.jp l) ^ 2 := by
  rcases h with rfl | rfl | rfl | rfl
  · exact S7PIDR_jp_add_sq_le k l
  · have := S7PIDR_jp_add_sq_le k (-l)
    rwa [S7PIDR_jp_neg] at this
  · have := S7PIDR_jp_add_sq_le (-k) l
    rwa [S7PIDR_jp_neg] at this
  · have := S7PIDR_jp_add_sq_le (-k) (-l)
    rwa [S7PIDR_jp_neg, S7PIDR_jp_neg] at this

end HRS.MC.Sec7.S7PIDR

end

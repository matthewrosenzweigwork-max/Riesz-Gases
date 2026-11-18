import HRS.MS.MovOpAux7

/-!
# MOV-C3a (2): the formal transpose `P^†` of `P`, the pairing identity, and the bound `Σ^r → Σ^{r-a}`

Namespace `HRS.MS.MovC1`, helper prefix `movc3a_`.  Infrastructure for S6.2/S6.3 (plan row 11); not manuscript rows.

With `ψ = √ρ`, `ℓ = ∇ log ρ`, `g = rieszKernel d s` (even) one has (`mv1_P_formula`)
`P v = -ψ (g * Δ(ψ v) + ℓ · ∇(g * (ψ v)))`, i.e. `P = -M_ψ (Δ + ℓ·∇) G M_ψ`.  The **formal transpose** is
`P^† w = -ψ (g * (Δ(ψ w) - ∑_i ∂_i(ℓ_i ψ w)))`, i.e. `P^† = -M_ψ G (Δ - div ℓ·) M_ψ`
(`g` even so the convolution `G` is symmetric, `M_ψ` symmetric, `(ℓ·∇)^† = -div ℓ·`).

* `movc3a_swap`: `∫ a (g * u) = ∫ u (g * a)` for `a, u` of Gaussian class (Fubini; majorant by a convolution of
  integrable functions; `g` even).
* `movc3a_ibp_T`: `∫ (∂_i φ) (g * u) = - ∫ φ (g * ∂_i u)` for Schwartz `φ` and `u` of Gaussian class.
* `movPadj d s ρ w`: the transpose, defined by the formula above (`Laplacian.laplacian` and `fderiv`; no junk
  value is hit for Schwartz `w`, see `movc3a_Padj_eq`).
* `mov_P_adj_pairing`: `∫ (P v) w = ∫ v (P^† w)` for Schwartz `v, w` (so `P^†` is the `L²` adjoint on Schwartz
  functions).
* `movPadj_schwartz`: `P^† w` is a Schwartz function.
* `mov_Padj_bound`: for every real `r`, `‖P^† w‖_{Σ^{r-a}} ≤ C ‖w‖_{Σ^r}` for Schwartz `w`.  Proof by duality
  (`mo_memOsc_neg_of_dual_bdd`, test functions: finite Hermite sums, which are Schwartz) from `mov_P_bound` at the
  index `a - r`; the "transposing the chain" of the plan is not repeated.

**Not delivered** (item (4) of the packet, the `_gen` form for non-Schwartz data): `P` on `Σ^r` for `v` not Schwartz.
The bounds `mov_P_bound`, `mov_Padj_bound` define, by density of Schwartz functions in `Σ^r` (Hermite partial sums
converge in `Σ^r`), unique continuous extensions `Σ^r → Σ^{r-a}`; what is missing is (i) the density statement for
`MemOsc r` in the `oscNorm r` topology and (ii) the identification of the extension with the pointwise formula
`-ψ(g*Δ(ψ v) + ℓ·∇(g*(ψ v)))` for `v ∈ C²` Gaussian-weighted (needs `L²`-continuity of `M_ψ`, `g_loc *` and the far
terms along the approximating sequence).  The pairing identity `mov_P_adj_pairing` extends to `v ∈ Σ^r`, `w ∈ Σ^{-r+a}`
by the same density argument.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovC1

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.Mov0 HRS.MS.MovForce

variable {d : ℕ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

/-! ### Symmetry of the convolution pairing -/

section Swap

variable {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)

omit hd hs0 hsd in
lemma movc3a_g_even (z : Euc d) : rieszKernel d s (-z) = rieszKernel d s z := by
  simp [rieszKernel]

include hd hs0 hsd

/-- **Symmetry of `g *`**: `∫ a (g * u) = ∫ u (g * a)` for `a, u` of Gaussian class. -/
theorem movc3a_swap {a u : Euc d → ℝ} (ha : MovcG a) (hu : MovcG u) :
    ∫ x, a x * movb2_T (rieszKernel d s) u x = ∫ y, u y * movb2_T (rieszKernel d s) a y := by
  obtain ⟨ca, Ea, hca, hEa, ha0⟩ := movc3a_G_abs ha
  obtain ⟨cu, Eu, hcu, hEu, hu0⟩ := movc3a_G_abs hu
  set c : ℝ := min ca cu with hcdef
  have hc : 0 < c := lt_min hca hcu
  obtain ⟨hgm, hB, hBint⟩ := mv1_g_data (d := d) (s := s) hd hs0 hsd (c := c / 2) (by positivity)
  set Bf : Euc d → ℝ := fun z => 2 * ‖z‖ ^ (-movtr_sp s) + ‖z‖ + 1 with hBf
  have hΦ : Integrable (fun y : Euc d => Real.exp (-(c / 2) * ‖y‖ ^ 2)) volume :=
    movc1_gauss_integrable hd (by positivity)
  have hbd : ∀ x y : Euc d, |a x| * |u y| ≤
      (Ea * Eu) * (Real.exp (-(c / 2) * ‖y‖ ^ 2) * Real.exp (-((c / 2) / 2) * ‖x - y‖ ^ 2)) := by
    intro x y
    have h1 : |a x| ≤ Ea * Real.exp (-c * ‖x‖ ^ 2) :=
      (ha0 x).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by
        nlinarith [min_le_left ca cu, sq_nonneg ‖x‖])) hEa)
    have h2 : |u y| ≤ Eu * Real.exp (-c * ‖y‖ ^ 2) :=
      (hu0 y).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by
        nlinarith [min_le_right ca cu, sq_nonneg ‖y‖])) hEu)
    have h3 : Real.exp (-c * ‖x‖ ^ 2) * Real.exp (-c * ‖y‖ ^ 2) ≤
        Real.exp (-(c / 2) * ‖y‖ ^ 2) * Real.exp (-((c / 2) / 2) * ‖x - y‖ ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have : ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
        nlinarith [pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le x y) 2, sq_nonneg (‖x‖ - ‖y‖)]
      nlinarith [mul_nonneg hc.le (sq_nonneg ‖x‖), mul_nonneg hc.le (sq_nonneg ‖y‖),
        mul_le_mul_of_nonneg_left this hc.le]
    calc |a x| * |u y| ≤ (Ea * Real.exp (-c * ‖x‖ ^ 2)) * (Eu * Real.exp (-c * ‖y‖ ^ 2)) :=
          mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ = (Ea * Eu) * (Real.exp (-c * ‖x‖ ^ 2) * Real.exp (-c * ‖y‖ ^ 2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 (mul_nonneg hEa hEu)
  -- integrability of the integrand on the product
  have hconv : Integrable (fun p : Euc d × Euc d =>
      Real.exp (-(c / 2) * ‖p.2‖ ^ 2) * (Bf (p.1 - p.2) * Real.exp (-((c / 2) / 2) * ‖p.1 - p.2‖ ^ 2)))
      (volume.prod volume) := by
    have := Integrable.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hΦ hBint
    simpa using this
  have hmaj : Integrable (fun p : Euc d × Euc d =>
      (Ea * Eu) * (Real.exp (-(c / 2) * ‖p.2‖ ^ 2) *
        (Bf (p.1 - p.2) * Real.exp (-((c / 2) / 2) * ‖p.1 - p.2‖ ^ 2)))) (volume.prod volume) :=
    hconv.const_mul _
  have hmeas : AEStronglyMeasurable (fun p : Euc d × Euc d =>
      a p.1 * (rieszKernel d s (p.1 - p.2) * u p.2)) (volume.prod volume) := by
    have h1 := AEStronglyMeasurable.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ)
      (μ := (volume : Measure (Euc d))) (ν := (volume : Measure (Euc d)))
      hu.1.continuous.aestronglyMeasurable hgm
    have h2 : AEStronglyMeasurable (fun p : Euc d × Euc d => a p.1) (volume.prod volume) :=
      ha.1.continuous.aestronglyMeasurable.comp_fst
    refine (h2.mul h1).congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [ContinuousLinearMap.mul_apply', Pi.mul_apply]
    ring
  have hint : Integrable (fun p : Euc d × Euc d => a p.1 * (rieszKernel d s (p.1 - p.2) * u p.2))
      (volume.prod volume) := by
    refine Integrable.mono' hmaj hmeas ?_
    have hae : ∀ᵐ p : Euc d × Euc d ∂(volume.prod volume), |rieszKernel d s (p.1 - p.2)| ≤ Bf (p.1 - p.2) :=
      (quasiMeasurePreserving_sub_of_right_invariant (volume : Measure (Euc d)) volume).ae hB
    filter_upwards [hae] with p hp
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
    have h4 := hbd p.1 p.2
    have h5 : |a p.1| * (|rieszKernel d s (p.1 - p.2)| * |u p.2|) ≤
        |a p.1| * (Bf (p.1 - p.2) * |u p.2|) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp (abs_nonneg _)) (abs_nonneg _)
    refine h5.trans ?_
    have hB0 : 0 ≤ Bf (p.1 - p.2) := (abs_nonneg _).trans hp
    calc |a p.1| * (Bf (p.1 - p.2) * |u p.2|) = Bf (p.1 - p.2) * (|a p.1| * |u p.2|) := by ring
      _ ≤ Bf (p.1 - p.2) * ((Ea * Eu) * (Real.exp (-(c / 2) * ‖p.2‖ ^ 2) *
            Real.exp (-((c / 2) / 2) * ‖p.1 - p.2‖ ^ 2))) :=
          mul_le_mul_of_nonneg_left h4 hB0
      _ = _ := by ring
  have e0 : ∀ (f : Euc d → ℝ) (x : Euc d), movb2_T (rieszKernel d s) f x =
      ∫ y, rieszKernel d s (x - y) * f y := fun f x => (mv1_convFun_eq _ _ x).symm
  have e1 : ∀ x, a x * movb2_T (rieszKernel d s) u x = ∫ y, a x * (rieszKernel d s (x - y) * u y) := by
    intro x
    rw [e0, ← integral_const_mul]
  have e2 : ∀ y, ∫ x, a x * (rieszKernel d s (x - y) * u y) = u y * movb2_T (rieszKernel d s) a y := by
    intro y
    rw [e0, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have : x - y = -(y - x) := by abel
    simp only
    rw [this, movc3a_g_even]
    ring
  calc ∫ x, a x * movb2_T (rieszKernel d s) u x
      = ∫ x, ∫ y, a x * (rieszKernel d s (x - y) * u y) := integral_congr_ae (Filter.Eventually.of_forall e1)
    _ = ∫ y, ∫ x, a x * (rieszKernel d s (x - y) * u y) :=
        integral_integral_swap (f := fun x y => a x * (rieszKernel d s (x - y) * u y)) hint
    _ = ∫ y, u y * movb2_T (rieszKernel d s) a y := integral_congr_ae (Filter.Eventually.of_forall e2)

end Swap

/-! ### Integration by parts against `g * u` -/

section IBP

variable {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
include hd hs0 hsd

lemma movc3a_polyG_Tg {u : Euc d → ℝ} (hu : MovcG u) : PolyG (movb2_T (rieszKernel d s) u) := by
  obtain ⟨c, E, hc, hE, h0⟩ := movc3a_G_abs hu
  obtain ⟨K, hK0, hK⟩ := movc3a_Tg_bound hd hs0 hsd (d := d) (s := s) hc
  refine ⟨K * E, 1, fun x => ?_⟩
  rw [pow_one]
  exact hK hE hu.1.continuous h0 x

/-- `∫ (∂_i φ) (g * u) = - ∫ φ (g * ∂_i u)` for a Schwartz function `φ` and `u` of Gaussian class. -/
theorem movc3a_ibp_T (φ : 𝓢R) {u : Euc d → ℝ} (hu : MovcG u) (i : Fin d) :
    ∫ x, mova3b1_Dj i (⇑φ) x * movb2_T (rieszKernel d s) u x =
      -∫ x, φ x * movb2_T (rieszKernel d s) (mova3b1_Dj i u) x := by
  have hu1 := movc1_G_Dj hu i
  have key := ibp_schwartz φ (movb2_T (rieszKernel d s) u) (fun x => movb2_T (rieszKernel d s) (mova3b1_Dj i u) x)
    (EuclideanSpace.single i (1 : ℝ) : Euc d) (fun x => movc3a_Tg_hasLineDeriv hd hs0 hsd hu i x)
    (movc3a_Tg_cont hd hs0 hsd hu) (movc3a_polyG_Tg hd hs0 hsd hu)
    (movc3a_Tg_cont hd hs0 hsd hu1) (movc3a_polyG_Tg hd hs0 hsd hu1)
  have e : ∀ x, lineDeriv ℝ (⇑φ) x (EuclideanSpace.single i (1 : ℝ) : Euc d) = mova3b1_Dj i (⇑φ) x :=
    fun x => φ.differentiableAt.lineDeriv_eq_fderiv
  simp_rw [e] at key
  exact key

/-- Integration by parts for two Gaussian-class functions. -/
theorem movc3a_ibp_G {h w : Euc d → ℝ} (hh : MovcG h) (hw : MovcG w) (i : Fin d) :
    ∫ x, mova3b1_Dj i h x * movb2_T (rieszKernel d s) w x =
      -∫ x, h x * movb2_T (rieszKernel d s) (mova3b1_Dj i w) x := by
  obtain ⟨φ, hφ⟩ := movc1_G_schwartz hh
  have := movc3a_ibp_T hd hs0 hsd φ hw i
  rwa [hφ] at this

/-- `∫ a (g * ∂_i h) = - ∫ h (g * ∂_i a)`. -/
theorem movc3a_pair_D {a h : Euc d → ℝ} (ha : MovcG a) (hh : MovcG h) (i : Fin d) :
    ∫ x, a x * movb2_T (rieszKernel d s) (mova3b1_Dj i h) x =
      -∫ x, h x * movb2_T (rieszKernel d s) (mova3b1_Dj i a) x := by
  rw [movc3a_swap hd hs0 hsd ha (movc1_G_Dj hh i)]
  exact movc3a_ibp_G hd hs0 hsd hh ha i

/-- `∫ k (g * ∂_i∂_i h) = ∫ h (g * ∂_i∂_i k)`. -/
theorem movc3a_pair_DD {k h : Euc d → ℝ} (hk : MovcG k) (hh : MovcG h) (i : Fin d) :
    ∫ x, k x * movb2_T (rieszKernel d s) (mova3b1_Dj i (mova3b1_Dj i h)) x =
      ∫ x, h x * movb2_T (rieszKernel d s) (mova3b1_Dj i (mova3b1_Dj i k)) x := by
  rw [movc3a_swap hd hs0 hsd hk (movc1_G_Dj (movc1_G_Dj hh i) i),
    movc3a_ibp_G hd hs0 hsd (movc1_G_Dj hh i) hk i,
    movc3a_ibp_G hd hs0 hsd hh (movc1_G_Dj hk i) i, neg_neg]

end IBP

/-! ### The formal transpose `P^†` -/

/-- The operator `k ↦ Δ k - ∑_i ∂_i (∂_i log ρ · k)`, the formal transpose of `Δ + ⟨∇log ρ, ∇·⟩`. -/
def movPadjOp (d : ℕ) (ρ : Euc d → ℝ) (k : Euc d → ℝ) (y : Euc d) : ℝ :=
  Laplacian.laplacian k y - ∑ i : Fin d,
    fderiv ℝ (fun z => gradient (fun u => Real.log (ρ u)) z i * k z) y (EuclideanSpace.single i 1)

/-- **The formal transpose `P^†`** of `P` (`ψ = √ρ`, `g = rieszKernel d s` even):
`P^† w = -ψ · (g * (Δ(ψ w) - ∑_i ∂_i(∂_i log ρ · ψ w)))`, for `w` Schwartz (or `C²`, Gaussian-bounded). -/
def movPadj (d : ℕ) (s : ℝ) (ρ : Euc d → ℝ) (w : Euc d → ℝ) (x : Euc d) : ℝ :=
  -(Real.sqrt (ρ x)) * HRS.Whole.convFun (rieszKernel d s)
    (movPadjOp d ρ (fun z => Real.sqrt (ρ z) * w z)) x

section Adj

variable {s : ℝ} {ρ : Euc d → ℝ} {q' : ℝ} {B : Euc d → Euc d}
variable (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
include hd hs0 hsd

lemma movc3a_int_term {f : Euc d → ℝ} (hf : MovcG f) (x : Euc d) :
    Integrable (fun z => rieszKernel d s z * f (x - z)) volume := by
  obtain ⟨c, E, hc, hE, h0⟩ := movc3a_G_abs hf
  exact movc1_conv_int hd hs0 hsd hf.1.continuous hc hE h0 x

/-- Linearity of `g *` for two finite families of Gaussian-class functions. -/
lemma movc3a_T_lin2 {f g' : Fin d → Euc d → ℝ} (hf : ∀ i, MovcG (f i)) (hg : ∀ i, MovcG (g' i)) (x : Euc d) :
    movb2_T (rieszKernel d s) (fun y => ∑ i, f i y - ∑ i, g' i y) x =
      ∑ i, movb2_T (rieszKernel d s) (f i) x - ∑ i, movb2_T (rieszKernel d s) (g' i) x := by
  unfold movb2_T
  simp_rw [mul_sub, Finset.mul_sum]
  rw [integral_sub (integrable_finset_sum _ fun i _ => movc3a_int_term hd hs0 hsd (hf i) x)
    (integrable_finset_sum _ fun i _ => movc3a_int_term hd hs0 hsd (hg i) x),
    integral_finsetSum _ fun i _ => movc3a_int_term hd hs0 hsd (hf i) x,
    integral_finsetSum _ fun i _ => movc3a_int_term hd hs0 hsd (hg i) x]

/-- The bracket of the transpose: `∑_i g * ∂_i∂_i k - ∑_i g * ∂_i(ℓ_i k)`. -/
def movc3a_brA (d : ℕ) (s : ℝ) (ρ k : Euc d → ℝ) (x : Euc d) : ℝ :=
  (∑ i : Fin d, movb2_T (rieszKernel d s) (mova3b1_Dj i (mova3b1_Dj i k)) x) -
    ∑ i : Fin d, movb2_T (rieszKernel d s)
      (mova3b1_Dj i (fun z => gradient (fun u => Real.log (ρ u)) z i * k z)) x

omit hd hs0 hsd in
lemma movc3a_lk_G (T : MovcTherm d ρ q' B) (w : 𝓢R) (i : Fin d) :
    MovcG (fun z => gradient (fun u => Real.log (ρ u)) z i * (Real.sqrt (ρ z) * w z)) := by
  have := movc1_schwartz_G_mul (T.psi_ell i) w
  have e : (fun z => gradient (fun u => Real.log (ρ u)) z i * (Real.sqrt (ρ z) * w z)) =
      fun y => (Real.sqrt (ρ y) * gradient (fun y => Real.log (ρ y)) y i) * w y := by
    funext z; ring
  rw [e]; exact this

/-- `P^† w = -(bracket) · ψ`. -/
lemma movc3a_Padj_eq (T : MovcTherm d ρ q' B) (w : 𝓢R) :
    movPadj d s ρ w = fun x => (-(movc3a_brA d s ρ (fun z => Real.sqrt (ρ z) * w z) x)) * Real.sqrt (ρ x) := by
  have hk : MovcG (fun z => Real.sqrt (ρ z) * w z) := movc1_schwartz_G_mul T.psi w
  set k : Euc d → ℝ := fun z => Real.sqrt (ρ z) * w z with hkdef
  funext x
  have hop : movPadjOp d ρ k = fun y => ∑ i : Fin d, mova3b1_Dj i (mova3b1_Dj i k) y -
      ∑ i : Fin d, mova3b1_Dj i (fun z => gradient (fun u => Real.log (ρ u)) z i * k z) y := by
    funext y
    unfold movPadjOp
    rw [mv1_laplacian_eq (hk.1.of_le (by norm_cast)) y]
    rfl
  unfold movPadj
  rw [hop, mv1_convFun_eq]
  have := movc3a_T_lin2 hd hs0 hsd (f := fun i => mova3b1_Dj i (mova3b1_Dj i k))
    (g' := fun i => mova3b1_Dj i (fun z => gradient (fun u => Real.log (ρ u)) z i * k z))
    (fun i => movc1_G_Dj (movc1_G_Dj hk i) i) (fun i => movc1_G_Dj (movc3a_lk_G T w i) i) x
  rw [show (∫ z, rieszKernel d s z * (fun y => ∑ i : Fin d, mova3b1_Dj i (mova3b1_Dj i k) y -
      ∑ i : Fin d, mova3b1_Dj i (fun z => gradient (fun u => Real.log (ρ u)) z i * k z) y) (x - z)) =
      movb2_T (rieszKernel d s) (fun y => ∑ i : Fin d, mova3b1_Dj i (mova3b1_Dj i k) y -
      ∑ i : Fin d, mova3b1_Dj i (fun z => gradient (fun u => Real.log (ρ u)) z i * k z) y) x from rfl, this]
  simp only [movc3a_brA]
  ring

end Adj

/-! ### The pairing identity `⟨P v, w⟩ = ⟨v, P^† w⟩` -/

section Pair

variable {s : ℝ} {ρ : Euc d → ℝ} {q' : ℝ} {B : Euc d → Euc d}
variable (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
include hd hs0 hsd

lemma movc3a_int_pair {k u : Euc d → ℝ} (hk : MovcG k) (hu : MovcG u) :
    Integrable (fun x => k x * movb2_T (rieszKernel d s) u x) volume := by
  obtain ⟨φ, hφ⟩ := movc1_G_schwartz hk
  rw [← hφ]
  exact int_schwartz_mul φ _ (movc3a_Tg_cont hd hs0 hsd hu) (movc3a_polyG_Tg hd hs0 hsd hu)

/-- **Pairing identity** (general thermal data): `∫ (P v) w = ∫ v (P^† w)` for Schwartz `v, w`. -/
theorem movc3a_pairing (T : MovcTherm d ρ q' B) (v w : 𝓢R) :
    ∫ x, movP d s ρ v x * w x = ∫ x, v x * movPadj d s ρ w x := by
  have hh : MovcG (fun y => Real.sqrt (ρ y) * v y) := movc1_schwartz_G_mul T.psi v
  have hk : MovcG (fun y => Real.sqrt (ρ y) * w y) := movc1_schwartz_G_mul T.psi w
  set h : Euc d → ℝ := fun y => Real.sqrt (ρ y) * v y with hhdef
  set k : Euc d → ℝ := fun y => Real.sqrt (ρ y) * w y with hkdef
  set ℓ : Fin d → Euc d → ℝ := fun i x => gradient (fun y => Real.log (ρ y)) x i with hℓ
  have hlk : ∀ i, MovcG (fun z => ℓ i z * k z) := fun i => movc3a_lk_G T w i
  have hD1 : ∀ i, MovcG (mova3b1_Dj i h) := fun i => movc1_G_Dj hh i
  have hD2 : ∀ i, MovcG (mova3b1_Dj i (mova3b1_Dj i h)) := fun i => movc1_G_Dj (hD1 i) i
  have hD2k : ∀ i, MovcG (mova3b1_Dj i (mova3b1_Dj i k)) := fun i => movc1_G_Dj (movc1_G_Dj hk i) i
  have hDlk : ∀ i, MovcG (mova3b1_Dj i (fun z => ℓ i z * k z)) := fun i => movc1_G_Dj (hlk i) i
  -- pointwise forms
  have hL : ∀ x, movP d s ρ v x * w x =
      -(∑ i : Fin d, k x * movb2_T (rieszKernel d s) (mova3b1_Dj i (mova3b1_Dj i h)) x +
        ∑ i : Fin d, (ℓ i x * k x) * movb2_T (rieszKernel d s) (mova3b1_Dj i h) x) := by
    intro x
    rw [congrFun (movc3a_P_eq hd hs0 hsd T v) x]
    simp only [movc3a_br]
    have e1 : ((∑ i : Fin d, movb2_T (rieszKernel d s) (mova3b1_Dj i (mova3b1_Dj i h)) x) +
        ∑ i : Fin d, ℓ i x * movb2_T (rieszKernel d s) (mova3b1_Dj i h) x) * k x =
        ∑ i : Fin d, k x * movb2_T (rieszKernel d s) (mova3b1_Dj i (mova3b1_Dj i h)) x +
          ∑ i : Fin d, (ℓ i x * k x) * movb2_T (rieszKernel d s) (mova3b1_Dj i h) x := by
      rw [add_mul, Finset.sum_mul, Finset.sum_mul]
      congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring
    have e2 : ((∑ i : Fin d, movb2_T (rieszKernel d s) (mova3b1_Dj i (mova3b1_Dj i h)) x) +
        ∑ i : Fin d, ℓ i x * movb2_T (rieszKernel d s) (mova3b1_Dj i h) x) * k x =
        ((∑ i : Fin d, movb2_T (rieszKernel d s) (mova3b1_Dj i (mova3b1_Dj i h)) x) +
        ∑ i : Fin d, ℓ i x * movb2_T (rieszKernel d s) (mova3b1_Dj i h) x) * (Real.sqrt (ρ x) * w x) := rfl
    rw [← e1, e2]
    ring
  have hR : ∀ x, v x * movPadj d s ρ w x =
      -(∑ i : Fin d, h x * movb2_T (rieszKernel d s) (mova3b1_Dj i (mova3b1_Dj i k)) x -
        ∑ i : Fin d, h x * movb2_T (rieszKernel d s)
          (mova3b1_Dj i (fun z => ℓ i z * k z)) x) := by
    intro x
    rw [congrFun (movc3a_Padj_eq hd hs0 hsd T w) x]
    simp only [movc3a_brA]
    have e1 : h x * ((∑ i : Fin d, movb2_T (rieszKernel d s) (mova3b1_Dj i (mova3b1_Dj i k)) x) -
        ∑ i : Fin d, movb2_T (rieszKernel d s) (mova3b1_Dj i (fun z => ℓ i z * k z)) x) =
        ∑ i : Fin d, h x * movb2_T (rieszKernel d s) (mova3b1_Dj i (mova3b1_Dj i k)) x -
        ∑ i : Fin d, h x * movb2_T (rieszKernel d s) (mova3b1_Dj i (fun z => ℓ i z * k z)) x := by
      rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
    rw [← e1]
    have e2 : h x = Real.sqrt (ρ x) * v x := rfl
    rw [e2]
    ring
  simp_rw [hL, hR]
  rw [integral_neg, integral_neg]
  congr 1
  have i1 : ∀ i : Fin d, Integrable (fun x => k x * movb2_T (rieszKernel d s)
      (mova3b1_Dj i (mova3b1_Dj i h)) x) volume := fun i => movc3a_int_pair hd hs0 hsd hk (hD2 i)
  have i2 : ∀ i : Fin d, Integrable (fun x => (ℓ i x * k x) * movb2_T (rieszKernel d s)
      (mova3b1_Dj i h) x) volume := fun i => movc3a_int_pair hd hs0 hsd (hlk i) (hD1 i)
  have i3 : ∀ i : Fin d, Integrable (fun x => h x * movb2_T (rieszKernel d s)
      (mova3b1_Dj i (mova3b1_Dj i k)) x) volume := fun i => movc3a_int_pair hd hs0 hsd hh (hD2k i)
  have i4 : ∀ i : Fin d, Integrable (fun x => h x * movb2_T (rieszKernel d s)
      (mova3b1_Dj i (fun z => ℓ i z * k z)) x) volume := fun i => movc3a_int_pair hd hs0 hsd hh (hDlk i)
  rw [integral_add (integrable_finset_sum _ fun i _ => i1 i) (integrable_finset_sum _ fun i _ => i2 i),
    integral_sub (integrable_finset_sum _ fun i _ => i3 i) (integrable_finset_sum _ fun i _ => i4 i),
    integral_finsetSum _ fun i _ => i1 i, integral_finsetSum _ fun i _ => i2 i,
    integral_finsetSum _ fun i _ => i3 i, integral_finsetSum _ fun i _ => i4 i]
  have p1 : ∀ i : Fin d, ∫ x, k x * movb2_T (rieszKernel d s) (mova3b1_Dj i (mova3b1_Dj i h)) x =
      ∫ x, h x * movb2_T (rieszKernel d s) (mova3b1_Dj i (mova3b1_Dj i k)) x :=
    fun i => movc3a_pair_DD hd hs0 hsd hk hh i
  have p2 : ∀ i : Fin d, ∫ x, (ℓ i x * k x) * movb2_T (rieszKernel d s) (mova3b1_Dj i h) x =
      -∫ x, h x * movb2_T (rieszKernel d s) (mova3b1_Dj i (fun z => ℓ i z * k z)) x :=
    fun i => movc3a_pair_D hd hs0 hsd (hlk i) hh i
  simp_rw [p1, p2, Finset.sum_neg_distrib]
  ring

end Pair

/-! ### `P^†` is Schwartz, and the bound `Σ^r → Σ^{r-a}` -/

section Bound

variable {s : ℝ} {ρ : Euc d → ℝ} {q' : ℝ} {B : Euc d → Euc d}
variable (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
include hd hs0 hsd

/-- **`P^†` of a Schwartz function is Schwartz**, general thermal data. -/
theorem movc3a_Padj_schwartz_gen (T : MovcTherm d ρ q' B) (w : 𝓢R) :
    ∃ φ : 𝓢R, ⇑φ = movPadj d s ρ w := by
  have hk : MovcG (fun y => Real.sqrt (ρ y) * w y) := movc1_schwartz_G_mul T.psi w
  have htg : Function.HasTemperateGrowth
      (movc3a_brA d s ρ (fun y => Real.sqrt (ρ y) * w y)) :=
    (Function.HasTemperateGrowth.sum
      (fun i _ => movc3a_Tg_tg hd hs0 hsd (movc1_G_Dj (movc1_G_Dj hk i) i))).sub
      (Function.HasTemperateGrowth.sum
        (fun i _ => movc3a_Tg_tg hd hs0 hsd (movc1_G_Dj (movc3a_lk_G T w i) i)))
  obtain ⟨ψS, hψS⟩ := movc1_G_schwartz T.psi
  refine ⟨SchwartzMap.smulLeftCLM ℝ (-(movc3a_brA d s ρ (fun y => Real.sqrt (ρ y) * w y))) ψS, ?_⟩
  funext x
  rw [SchwartzMap.smulLeftCLM_apply_apply htg.neg, movc3a_Padj_eq hd hs0 hsd T w, hψS]
  simp [smul_eq_mul]

/-- **Bound for the transpose**, general thermal data: `‖P^† w‖_{Σ^{r-a}} ≤ C ‖w‖_{Σ^r}`. -/
theorem movc3a_Padj_bound_gen (T : MovcTherm d ρ q' B) (r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : 𝓢R, MemOsc (r - movA d s) (movPadj d s ρ w) ∧
      oscNorm (r - movA d s) (movPadj d s ρ w) ≤ C * oscNorm r w := by
  obtain ⟨C0, hC0, hP⟩ := movc1_P_bound_gen (d := d) (s := s) hd hs0 hsd T (movA d s - r)
  refine ⟨C0, hC0, fun w => ?_⟩
  obtain ⟨φ, hφ⟩ := movc3a_Padj_schwartz_gen hd hs0 hsd T w
  have hL2 : MemLp (movPadj d s ρ w) 2 (volume : Measure (Euc d)) := by
    rw [← hφ]; exact (memOsc_schwartz 0 φ).1
  have hw0 : 0 ≤ oscNorm r w := Real.sqrt_nonneg _
  have key := mo_memOsc_neg_of_dual_bdd (movA d s - r) hL2 (M := C0 * oscNorm r w) (by
    rintro t ⟨S, a', hg, rfl⟩
    obtain ⟨γ, hγ0⟩ := mova3c_hspan_schwartz (mova3_comb_mem S a')
    have hγ : (⇑γ : Euc d → ℝ) = mo_hsum S a' := hγ0
    have hpair := movc3a_pairing hd hs0 hsd T γ w
    have e1 : ∫ x, movPadj d s ρ w x * mo_hsum S a' x = ∫ x, movP d s ρ γ x * w x := by
      rw [hpair]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      rw [← hγ]
      ring
    rw [e1]
    obtain ⟨hPm, hPn⟩ := hP γ
    have hPm' : MemOsc (-r) (movP d s ρ γ) := by
      have : movA d s - r - movA d s = -r := by ring
      rwa [this] at hPm
    have hd1 := mo_dual_le (-r) (f := w) (g := movP d s ρ γ) (by rw [neg_neg]; exact memOsc_schwartz r w) hPm'
    rw [neg_neg] at hd1
    have hPn' : oscNorm (-r) (movP d s ρ γ) ≤ C0 * oscNorm (movA d s - r) γ := by
      have : movA d s - r - movA d s = -r := by ring
      rwa [this] at hPn
    have hg' : oscNorm (movA d s - r) γ ≤ 1 := by rw [hγ]; exact hg
    calc |∫ x, movP d s ρ γ x * w x| = |∫ x, w x * movP d s ρ γ x| := by
          congr 1
          exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
      _ ≤ oscNorm r w * oscNorm (-r) (movP d s ρ γ) := hd1
      _ ≤ oscNorm r w * (C0 * oscNorm (movA d s - r) γ) := mul_le_mul_of_nonneg_left hPn' hw0
      _ ≤ oscNorm r w * (C0 * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg' hC0) hw0
      _ = C0 * oscNorm r w := by ring)
  rw [neg_sub] at key
  exact key

end Bound

/-! ### The statements for the thermal density -/

section Thermal

variable {s : ℝ}

/-- **`mov_P_adj_pairing`**: `∫ (P v) w = ∫ v (P^† w)` for Schwartz `v, w`. -/
theorem mov_P_adj_pairing (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β q : ℝ) (hβ : 0 < β) (hq : 0 < q)
    (ρ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ) (v w : SchwartzMap (Euc d) ℝ) :
    ∫ x, movP d s ρ v x * w x = ∫ x, v x * movPadj d s ρ w x := by
  obtain ⟨B, -, hR, -⟩ := mv0_gapref hd hs0 hsd hq hβ hρ
  exact movc3a_pairing (by omega) hs0 hsd ⟨mul_pos hβ hq, hR⟩ v w

/-- **`mov_Padj_schwartz`**: `P^† w` is a Schwartz function for Schwartz `w`. -/
theorem mov_Padj_schwartz (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β q : ℝ) (hβ : 0 < β) (hq : 0 < q)
    (ρ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ) (w : SchwartzMap (Euc d) ℝ) :
    ∃ φ : SchwartzMap (Euc d) ℝ, ⇑φ = movPadj d s ρ w := by
  obtain ⟨B, -, hR, -⟩ := mv0_gapref hd hs0 hsd hq hβ hρ
  exact movc3a_Padj_schwartz_gen (by omega) hs0 hsd ⟨mul_pos hβ hq, hR⟩ w

/-- **`mov_Padj_bound`** (plan row 11): for every real `r` there is `C ≥ 0` with
`P^† w ∈ Σ^{r-a}` and `‖P^† w‖_{Σ^{r-a}} ≤ C ‖w‖_{Σ^r}` for all Schwartz `w`, where `P^† = movPadj` is the formal
transpose of `P` (`a = movA d s`). -/
theorem mov_Padj_bound (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β q : ℝ) (hβ : 0 < β) (hq : 0 < q)
    (ρ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ) (r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : SchwartzMap (Euc d) ℝ, MemOsc (r - movA d s) (movPadj d s ρ w) ∧
      oscNorm (r - movA d s) (movPadj d s ρ w) ≤ C * oscNorm r w := by
  obtain ⟨B, -, hR, -⟩ := mv0_gapref hd hs0 hsd hq hβ hρ
  exact movc3a_Padj_bound_gen (by omega) hs0 hsd ⟨mul_pos hβ hq, hR⟩ r

end Thermal

end HRS.MS.MovC1

end

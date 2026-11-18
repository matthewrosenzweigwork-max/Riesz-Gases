import HRS.Uniform.Q14Aux6
import HRS.Sections.Q38bAux4

/-!
# EQ-TRACE, base: the trace norm of a bilinear form on `E_γ` is bounded by its matrix entries

`traceNormForm Q ≤ ∑_{kl} |Q(e_k,e_l)|` for the standard orthonormal basis `e_k` of `E_γ = ℓ²(ℤ^d ∖ {0})` whenever the
entries are absolutely summable (the summability lemma of `HRS/Main/T25Aux1.lean` item (4)), and a Minkowski inequality for
`ℝ≥0∞`-valued series in `L²`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MD.EQTrace

variable {d : ℕ} {γ : ℝ}

/-- The standard orthonormal basis vector of `E_γ`. -/
def eb (γ : ℝ) (k : NonzeroLattice d) : NegSobolev d γ :=
  lp.single (E := fun _ : NonzeroLattice d => ℝ) 2 k (1 : ℝ)

theorem inner_eb (x : NegSobolev d γ) (k : NonzeroLattice d) :
    inner ℝ x (eb γ k) = NegSobolev.coord x k := by
  classical
  have := lp.inner_single_right (G := fun _ : NonzeroLattice d => ℝ) (𝕜 := ℝ) k (1 : ℝ)
    (show lp (fun _ : NonzeroLattice d => ℝ) 2 from x)
  change inner ℝ (show lp (fun _ : NonzeroLattice d => ℝ) 2 from x)
    (lp.single (E := fun _ : NonzeroLattice d => ℝ) 2 k (1 : ℝ)) = _
  rw [this]
  simp [NegSobolev.coord]

theorem norm_eb (k : NonzeroLattice d) : ‖eb (d := d) γ k‖ = 1 := by
  have := lp.norm_single (E := fun _ : NonzeroLattice d => ℝ) (p := 2) (by norm_num) k (1 : ℝ)
  change ‖(lp.single (E := fun _ : NonzeroLattice d => ℝ) 2 k (1 : ℝ) :
    lp (fun _ : NonzeroLattice d => ℝ) 2)‖ = 1
  rw [this]; simp

theorem hasSum_eb (x : NegSobolev d γ) :
    HasSum (fun k => NegSobolev.coord x k • eb γ k) x := by
  have := lp.hasSum_single (E := fun _ : NonzeroLattice d => ℝ) (p := 2) (by simp)
    (show lp (fun _ : NonzeroLattice d => ℝ) 2 from x)
  have h : ∀ k, NegSobolev.coord x k • eb γ k =
      (lp.single (E := fun _ : NonzeroLattice d => ℝ) 2 k
        ((show lp (fun _ : NonzeroLattice d => ℝ) 2 from x) k) :
          lp (fun _ : NonzeroLattice d => ℝ) 2) := by
    intro k
    apply lp.ext
    funext j
    show NegSobolev.coord x k * (lp.single (E := fun _ : NonzeroLattice d => ℝ) 2 k (1 : ℝ) j) = _
    simp [lp.single_apply, Pi.single_apply]
    rfl
  simp_rw [h]
  exact this

theorem abs_coord_le (x : NegSobolev d γ) (k : NonzeroLattice d) : |NegSobolev.coord x k| ≤ ‖x‖ := by
  have := abs_real_inner_le_norm x (eb γ k)
  rw [inner_eb, norm_eb, mul_one] at this
  exact this

/-- Matrix expansion `Q(x,y) = ∑_{kl} x_k y_l Q(e_k,e_l)` for absolutely summable entries. -/
theorem eqtrace_expand (Q : NegSobolev d γ →L[ℝ] NegSobolev d γ →L[ℝ] ℝ)
    (hs : Summable fun p : NonzeroLattice d × NonzeroLattice d => |Q (eb γ p.1) (eb γ p.2)|)
    (x y : NegSobolev d γ) :
    HasSum (fun p : NonzeroLattice d × NonzeroLattice d =>
      NegSobolev.coord x p.1 * NegSobolev.coord y p.2 * Q (eb γ p.1) (eb γ p.2)) (Q x y) := by
  set f : NonzeroLattice d × NonzeroLattice d → ℝ := fun p =>
    NegSobolev.coord x p.1 * NegSobolev.coord y p.2 * Q (eb γ p.1) (eb γ p.2) with hf
  have hsum : Summable f := by
    refine Summable.of_norm_bounded (hs.mul_left (‖x‖ * ‖y‖)) fun p => ?_
    rw [hf]; simp only [Real.norm_eq_abs, abs_mul]
    have h1 := abs_coord_le x p.1
    have h2 := abs_coord_le y p.2
    have h3 := abs_nonneg (Q (eb γ p.1) (eb γ p.2))
    calc |NegSobolev.coord x p.1| * |NegSobolev.coord y p.2| * |Q (eb γ p.1) (eb γ p.2)|
        ≤ (‖x‖ * ‖y‖) * |Q (eb γ p.1) (eb γ p.2)| := by
          gcongr
      _ = _ := rfl
  have hout : HasSum (fun k => NegSobolev.coord x k * Q (eb γ k) y) (Q x y) := by
    have := (hasSum_eb x).mapL ((ContinuousLinearMap.apply ℝ ℝ y).comp Q)
    simpa using this
  have hin : ∀ k, HasSum (fun l => f (k, l)) (NegSobolev.coord x k * Q (eb γ k) y) := by
    intro k
    have := ((hasSum_eb y).mapL (Q (eb γ k))).mul_left (NegSobolev.coord x k)
    simpa [hf, mul_assoc] using this
  have h2 := hsum.hasSum.prod_fiberwise hin
  have := h2.unique hout
  rw [← this]
  exact hsum.hasSum

/-- `‖Q‖_{𝔖₁} ≤ ∑_{kl} |Q(e_k,e_l)|`. -/
theorem eqtrace_traceNorm_le (Q : NegSobolev d γ →L[ℝ] NegSobolev d γ →L[ℝ] ℝ)
    (hs : Summable fun p : NonzeroLattice d × NonzeroLattice d => |Q (eb γ p.1) (eb γ p.2)|) :
    traceNormForm Q ≤ ∑' p : NonzeroLattice d × NonzeroLattice d, |Q (eb γ p.1) (eb γ p.2)| := by
  refine Real.iSup_le (fun p => ?_) (tsum_nonneg fun _ => abs_nonneg _)
  obtain ⟨⟨n, xs, ys⟩, hxs, hys⟩ := p
  simp only
  set q : NonzeroLattice d × NonzeroLattice d → ℝ := fun p => |Q (eb γ p.1) (eb γ p.2)| with hq
  set g : Fin n → NonzeroLattice d × NonzeroLattice d → ℝ := fun i p =>
    |NegSobolev.coord (xs i) p.1| * |NegSobolev.coord (ys i) p.2| * q p with hg
  have hgs : ∀ i, Summable (g i) := by
    intro i
    refine Summable.of_nonneg_of_le (fun p => by simp only [hg]; positivity) (fun p => ?_)
      (hs.mul_left (‖xs i‖ * ‖ys i‖))
    simp only [hg]
    have h1 := abs_coord_le (xs i) p.1
    have h2 := abs_coord_le (ys i) p.2
    have h3 : 0 ≤ q p := abs_nonneg _
    calc _ ≤ (‖xs i‖ * ‖ys i‖) * q p := by gcongr
      _ = _ := rfl
  have h1 : ∀ i, |Q (xs i) (ys i)| ≤ ∑' p, g i p := by
    intro i
    have hE := eqtrace_expand Q hs (xs i) (ys i)
    rw [← hE.tsum_eq]
    have hsm : Summable fun p : NonzeroLattice d × NonzeroLattice d =>
        ‖NegSobolev.coord (xs i) p.1 * NegSobolev.coord (ys i) p.2 * Q (eb γ p.1) (eb γ p.2)‖ := by
      refine (hgs i).congr fun p => ?_
      simp only [hg, hq, Real.norm_eq_abs, abs_mul]
    rw [← Real.norm_eq_abs]
    refine (norm_tsum_le_tsum_norm hsm).trans (le_of_eq (tsum_congr fun p => ?_))
    simp only [hg, hq, Real.norm_eq_abs, abs_mul]
  have h2 : ∀ p : NonzeroLattice d × NonzeroLattice d, ∑ i, g i p ≤ q p := by
    intro p
    have hB : ∀ (zs : Fin n → NegSobolev d γ), Orthonormal ℝ zs → ∀ k,
        ∑ i, NegSobolev.coord (zs i) k ^ 2 ≤ 1 := by
      intro zs hzs k
      have := hzs.sum_inner_products_le (eb γ k) (s := Finset.univ)
      rw [norm_eb] at this
      simpa [inner_eb, Real.norm_eq_abs, sq_abs] using this
    have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i => |NegSobolev.coord (xs i) p.1|) (fun i => |NegSobolev.coord (ys i) p.2|)
    simp only [sq_abs] at hCS
    have hxB := hB xs hxs p.1
    have hyB := hB ys hys p.2
    have hS0 : 0 ≤ ∑ i, |NegSobolev.coord (xs i) p.1| * |NegSobolev.coord (ys i) p.2| :=
      Finset.sum_nonneg fun i _ => by positivity
    have hS : ∑ i, |NegSobolev.coord (xs i) p.1| * |NegSobolev.coord (ys i) p.2| ≤ 1 := by
      have hx0 : 0 ≤ ∑ i, NegSobolev.coord (xs i) p.1 ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      have hy0 : 0 ≤ ∑ i, NegSobolev.coord (ys i) p.2 ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      nlinarith [mul_le_mul hxB hyB hy0 zero_le_one]
    have hq0 : 0 ≤ q p := abs_nonneg _
    calc ∑ i, g i p = (∑ i, |NegSobolev.coord (xs i) p.1| * |NegSobolev.coord (ys i) p.2|) * q p := by
          simp only [hg]; rw [Finset.sum_mul]
      _ ≤ 1 * q p := by gcongr
      _ = q p := one_mul _
  calc ∑ i, |Q (xs i) (ys i)| ≤ ∑ i, ∑' p, g i p := Finset.sum_le_sum fun i _ => h1 i
    _ = ∑' p, ∑ i, g i p := (Summable.tsum_finsetSum fun i _ => hgs i).symm
    _ ≤ ∑' p, q p :=
        Summable.tsum_le_tsum h2 (summable_sum fun i _ => hgs i) hs

end HRS.MD.EQTrace

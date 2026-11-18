import HRS.Uniform.Q48bAux5

/-!
# Q54, part 15: weighted Fourier norms on `E_r`, the density lemma, mixed weighted bounds from duality

All operators on `E_r` considered below are described by their (level-free) Fourier matrix
`A l k = q48bMat r V l k` (`(V x)^_l = ∑_k A l k x^_k` on finite vectors).

* `fsq a x = ∑_l ⟨l⟩^{-2a} x^_l²` (finite for `r ≤ a`, `fsq r x = ‖x‖²`);
* `WB2 a b M A`: the finite-block bound `‖A ζ‖_{ℓ²_a} ≤ M ‖ζ‖_{ℓ²_b}` (mixed levels);
* `fsq_le_of_wb2` (density): the finite block bounds extend to all `x ∈ E_r` (`b ≥ r`);
* `wb2_of_duality`: a function-level bound `‖U φ‖_{H^b} ≤ M ‖φ‖_{H^a}` on finite trigonometric polynomials gives `WB2 a b M`;
* `eq_of_eval_smooth`: an element of `E_r` is determined by its pairings with smooth functions.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q54

open HRS HRS.PDE HRS.Uniform.Q48b

variable {d : ℕ}

theorem one_le_q48bW (l : NonzeroLattice d) : 1 ≤ q48bW l := Torus.jp_ge_one l.1

/-- `∑_l ⟨l⟩^{-2a} x^_l²`. -/
def fsq (a : ℝ) {r : ℝ} (x : NegSobolev d r) : ℝ :=
  ∑' l : NonzeroLattice d, q48bW l ^ (-2 * a) * NegSobolev.fourierCoeff x l ^ 2

theorem fsq_term {r : ℝ} (a : ℝ) (x : NegSobolev d r) (l : NonzeroLattice d) :
    q48bW l ^ (-2 * a) * NegSobolev.fourierCoeff x l ^ 2 =
      q48bW l ^ (2 * (r - a)) * NegSobolev.coord x l ^ 2 := by
  unfold NegSobolev.fourierCoeff
  have hw := q48bW_pos l
  have h1 : Lattice.jp l.1 = q48bW l := rfl
  rw [h1, mul_pow, q48b_rpow_sq hw, ← mul_assoc, ← Real.rpow_add hw]
  have e : -2 * a + 2 * r = 2 * (r - a) := by ring
  rw [e]

theorem summable_fsq_term {r a : ℝ} (hra : r ≤ a) (x : NegSobolev d r) :
    Summable fun l : NonzeroLattice d => q48bW l ^ (-2 * a) * NegSobolev.fourierCoeff x l ^ 2 := by
  refine Summable.of_nonneg_of_le (fun l => ?_) (fun l => ?_) (NegSobolev.coord_sq x).1
  · exact mul_nonneg (Real.rpow_nonneg (q48bW_pos l).le _) (sq_nonneg _)
  · rw [fsq_term]
    have h1 : q48bW l ^ (2 * (r - a)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (one_le_q48bW l) (by linarith)
    nlinarith [sq_nonneg (NegSobolev.coord x l)]

theorem fsq_self {r : ℝ} (x : NegSobolev d r) : fsq r x = ‖x‖ ^ 2 := by
  rw [q48b_norm_sq]
  unfold fsq
  refine tsum_congr fun l => ?_
  rw [fsq_term, sub_self, mul_zero, Real.rpow_zero, one_mul]

theorem fsq_nonneg (a : ℝ) {r : ℝ} (x : NegSobolev d r) : 0 ≤ fsq a x :=
  tsum_nonneg fun l => mul_nonneg (Real.rpow_nonneg (q48bW_pos l).le _) (sq_nonneg _)

theorem fsq_le_of_le {r a b : ℝ} (hra : r ≤ a) (hab : a ≤ b) (x : NegSobolev d r) :
    fsq b x ≤ fsq a x := by
  refine (summable_fsq_term (hra.trans hab) x).tsum_le_tsum (fun l => ?_) (summable_fsq_term hra x)
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  exact Real.rpow_le_rpow_of_exponent_le (one_le_q48bW l) (by linarith)

theorem fsq_fin (a r : ℝ) (S : Finset (NonzeroLattice d)) (ζ : NonzeroLattice d → ℝ) :
    fsq a (q48bFin r S ζ) = ∑ k ∈ S, q48bW k ^ (-2 * a) * ζ k ^ 2 := by
  classical
  unfold fsq
  rw [tsum_eq_sum (s := S)]
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [q48bFin_fourierCoeff, if_pos hk]
  · intro k hk
    rw [q48bFin_fourierCoeff, if_neg hk]
    simp

theorem continuous_coord {r : ℝ} (l : NonzeroLattice d) :
    Continuous fun F : NegSobolev d r => NegSobolev.coord F l := by
  have : LipschitzWith 1 fun F : NegSobolev d r => NegSobolev.coord F l := by
    refine LipschitzWith.of_dist_le_mul fun F G => ?_
    rw [Real.dist_eq, NNReal.coe_one, one_mul, dist_eq_norm]
    have h1 : NegSobolev.coord F l - NegSobolev.coord G l = NegSobolev.coord (F - G) l := rfl
    rw [h1]
    exact lp.norm_apply_le_norm (by norm_num) (F - G : lp (fun _ : NonzeroLattice d => ℝ) 2) l
  exact this.continuous

theorem continuous_fourierCoeff {r : ℝ} (l : NonzeroLattice d) :
    Continuous fun F : NegSobolev d r => NegSobolev.fourierCoeff F l :=
  continuous_const.mul (continuous_coord l)

/-- finite truncations converge. -/
theorem tendsto_trunc {r : ℝ} (x : NegSobolev d r) :
    Tendsto (fun S : Finset (NonzeroLattice d) => q48bFin r S (fun k => NegSobolev.fourierCoeff x k))
      atTop (𝓝 x) := by
  classical
  have hs := lp.hasSum_single (E := fun _ : NonzeroLattice d => ℝ) (p := 2) (by norm_num)
    (x : lp (fun _ : NonzeroLattice d => ℝ) 2)
  have heq : ∀ S : Finset (NonzeroLattice d), q48bFin r S (fun k => NegSobolev.fourierCoeff x k) =
      ∑ k ∈ S, lp.single 2 k (NegSobolev.coord x k) := by
    intro S
    refine lp.ext (funext fun l => ?_)
    have h1 : NegSobolev.coord (q48bFin r S (fun k => NegSobolev.fourierCoeff x k)) l =
        if l ∈ S then NegSobolev.coord x l else 0 := by
      rw [q48bFin_coord]
      split_ifs
      · show q48bW l ^ (-r) * (q48bW l ^ r * NegSobolev.coord x l) = _
        rw [← mul_assoc, q48b_rpow_neg_mul (q48bW_pos l) r, one_mul]
      · rfl
    have h2 : ((∑ k ∈ S, lp.single 2 k (NegSobolev.coord x k) :
        lp (fun _ : NonzeroLattice d => ℝ) 2) : NonzeroLattice d → ℝ) l =
        if l ∈ S then NegSobolev.coord x l else 0 := by
      rw [lp.coeFn_sum, Finset.sum_apply]
      simp [lp.single_apply, Pi.single_apply]
    exact h1.trans h2.symm
  have hs' : Tendsto (fun S : Finset (NonzeroLattice d) =>
      ∑ k ∈ S, lp.single 2 k (NegSobolev.coord x k)) atTop
      (𝓝 (x : lp (fun _ : NonzeroLattice d => ℝ) 2)) := hs
  exact hs'.congr fun S => (heq S).symm

/-- mixed weighted block bound `‖A ζ‖_{ℓ²_a} ≤ M ‖ζ‖_{ℓ²_b}`. -/
def WB2 (a b M : ℝ) (A : NonzeroLattice d → NonzeroLattice d → ℝ) : Prop :=
  ∀ (S T : Finset (NonzeroLattice d)) (ζ : NonzeroLattice d → ℝ),
    ∑ l ∈ T, q48bW l ^ (-2 * a) * (∑ k ∈ S, A l k * ζ k) ^ 2 ≤
      M ^ 2 * ∑ k ∈ S, q48bW k ^ (-2 * b) * ζ k ^ 2

theorem WB2.of_wbound {a M : ℝ} {A : NonzeroLattice d → NonzeroLattice d → ℝ}
    (h : ∀ S T : Finset (NonzeroLattice d), WBound q48bW A S T a M) : WB2 a a M A :=
  fun S T ζ => h S T ζ

/-- Density lemma: the block bounds extend from finite vectors to all of `E_r` (`b ≥ r`). -/
theorem fsq_le_of_wb2 {r : ℝ} (V : NegSobolev d r →L[ℝ] NegSobolev d r) {a b M : ℝ}
    (h : WB2 a b M (q48bMat r V)) (hb : r ≤ b) (x : NegSobolev d r) :
    Summable (fun l : NonzeroLattice d => q48bW l ^ (-2 * a) * NegSobolev.fourierCoeff (V x) l ^ 2) ∧
      fsq a (V x) ≤ M ^ 2 * fsq b x := by
  classical
  set ζ : NonzeroLattice d → ℝ := fun k => NegSobolev.fourierCoeff x k with hζ
  have hts := tendsto_trunc x
  have hcoord : ∀ l, Tendsto (fun S : Finset (NonzeroLattice d) => ∑ k ∈ S, q48bMat r V l k * ζ k)
      atTop (𝓝 (NegSobolev.fourierCoeff (V x) l)) := by
    intro l
    have h1 : Tendsto (fun S : Finset (NonzeroLattice d) => V (q48bFin r S ζ)) atTop (𝓝 (V x)) :=
      (V.continuous.tendsto x).comp hts
    have h2 : Tendsto (fun S : Finset (NonzeroLattice d) =>
        NegSobolev.fourierCoeff (V (q48bFin r S ζ)) l) atTop (𝓝 (NegSobolev.fourierCoeff (V x) l)) :=
      ((continuous_fourierCoeff (r := r) l).tendsto _).comp h1
    exact h2.congr fun S => q48bFin_V V S ζ l
  have hnn : ∀ l : NonzeroLattice d,
      0 ≤ q48bW l ^ (-2 * a) * NegSobolev.fourierCoeff (V x) l ^ 2 := fun l =>
    mul_nonneg (Real.rpow_nonneg (q48bW_pos l).le _) (sq_nonneg _)
  have hbd : ∀ T : Finset (NonzeroLattice d),
      ∑ l ∈ T, q48bW l ^ (-2 * a) * NegSobolev.fourierCoeff (V x) l ^ 2 ≤ M ^ 2 * fsq b x := by
    intro T
    have hlim : Tendsto (fun S : Finset (NonzeroLattice d) =>
        ∑ l ∈ T, q48bW l ^ (-2 * a) * (∑ k ∈ S, q48bMat r V l k * ζ k) ^ 2) atTop
        (𝓝 (∑ l ∈ T, q48bW l ^ (-2 * a) * NegSobolev.fourierCoeff (V x) l ^ 2)) :=
      tendsto_finset_sum _ fun l _ => ((hcoord l).pow 2).const_mul _
    refine le_of_tendsto' hlim fun S => (h S T ζ).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg M)
    exact (summable_fsq_term hb x).sum_le_tsum S (fun k _ =>
      mul_nonneg (Real.rpow_nonneg (q48bW_pos k).le _) (sq_nonneg _))
  exact ⟨summable_of_sum_le hnn hbd, Real.tsum_le_of_sum_le hnn hbd⟩

theorem norm_fin_le {r b M : ℝ} (V : NegSobolev d r →L[ℝ] NegSobolev d r)
    (h : WB2 r b M (q48bMat r V)) (S : Finset (NonzeroLattice d))
    (ζ : NonzeroLattice d → ℝ) :
    ‖V (q48bFin r S ζ)‖ ^ 2 ≤ M ^ 2 * ∑ k ∈ S, q48bW k ^ (-2 * b) * ζ k ^ 2 := by
  rw [q48b_norm_sq]
  refine Real.tsum_le_of_sum_le (fun l => sq_nonneg _) fun T => ?_
  have hT : ∀ l, NegSobolev.coord (V (q48bFin r S ζ)) l ^ 2 =
      q48bW l ^ (-2 * r) * (∑ k ∈ S, q48bMat r V l k * ζ k) ^ 2 := by
    intro l
    rw [q48b_coord_eq_fourier, q48bFin_V, mul_pow, q48b_rpow_sq (q48bW_pos l)]
    congr 2; ring
  simp_rw [hT]
  exact h S T ζ

theorem eval_realMode {r : ℝ} (F : NegSobolev d r) (l : NonzeroLattice d) :
    NegSobolev.eval F (q48bTest {l} (fun _ => 1)) = NegSobolev.fourierCoeff F l := by
  rw [q48b_eval_test]
  simp

theorem eq_of_eval_smooth {r : ℝ} {w w' : NegSobolev d r}
    (h : ∀ φ : Torus d → ℝ, Torus.IsSmooth φ → NegSobolev.eval w φ = NegSobolev.eval w' φ) :
    w = w' := by
  have hF : ∀ l, NegSobolev.fourierCoeff w l = NegSobolev.fourierCoeff w' l := fun l => by
    rw [← eval_realMode, ← eval_realMode]
    exact h _ (q48bTest_smooth _ _)
  show (w : lp (fun _ : NonzeroLattice d => ℝ) 2) = (w' : lp (fun _ : NonzeroLattice d => ℝ) 2)
  refine lp.ext (funext fun l => ?_)
  have h1 := hF l
  unfold NegSobolev.fourierCoeff at h1
  have hpos : 0 < Lattice.jp l.1 ^ r := Real.rpow_pos_of_pos (Torus.jp_pos _) _
  exact mul_left_cancel₀ hpos.ne' h1

/-- Mixed weighted bound from a function-level bound on finite trigonometric polynomials. -/
theorem wb2_of_duality {r a b : ℝ} (Up : (Torus d → ℝ) → Torus d → ℝ)
    (V : NegSobolev d r →L[ℝ] NegSobolev d r)
    (hdual : ∀ (z : NegSobolev d r) (φ : Torus d → ℝ), Torus.IsSmooth φ →
      NegSobolev.eval (V z) φ = NegSobolev.eval z (Up φ))
    (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ (T : Finset (NonzeroLattice d)) (c : NonzeroLattice d → ℝ),
      MemSobolev b (Up (q48bTest T c)) ∧
        sobolevNorm b (Up (q48bTest T c)) ≤ M * Real.sqrt (∑ l ∈ T, q48bW l ^ (2 * a) * c l ^ 2)) :
    WB2 a b M (q48bMat r V) := by
  intro S T ζ
  set Y : NonzeroLattice d → ℝ := fun l => ∑ k ∈ S, q48bMat r V l k * ζ k with hY
  set c : NonzeroLattice d → ℝ := fun l => q48bW l ^ (-2 * a) * Y l with hc
  set φ := q48bTest T c with hφ
  set z := q48bFin r S ζ with hz
  set X : ℝ := ∑ l ∈ T, q48bW l ^ (-2 * a) * Y l ^ 2 with hX
  set Nz : ℝ := ∑ k ∈ S, q48bW k ^ (-2 * b) * ζ k ^ 2 with hNz
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun l _ =>
    mul_nonneg (Real.rpow_nonneg (q48bW_pos l).le _) (sq_nonneg _)
  have hNz0 : 0 ≤ Nz := Finset.sum_nonneg fun l _ =>
    mul_nonneg (Real.rpow_nonneg (q48bW_pos l).le _) (sq_nonneg _)
  show X ≤ M ^ 2 * Nz
  have h1 : NegSobolev.eval (V z) φ = X := by
    rw [hφ, q48b_eval_test]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hz, q48bFin_V]
    simp only [hc, hY]
    have : (∑ k ∈ S, q48bMat r V l k * ζ k) = Y l := rfl
    rw [this]
    ring
  have hsm : Torus.IsSmooth φ := q48bTest_smooth T c
  have h2 : NegSobolev.eval (V z) φ = NegSobolev.eval z (Up φ) := hdual z φ hsm
  obtain ⟨hmem, hnorm⟩ := hb T c
  set ψ := Up φ with hψ
  have h3 : NegSobolev.eval z ψ = ∑ k ∈ S, ζ k * Torus.funRealCoeff ψ k := by
    rw [hz, q48b_eval_fin]
  have hcs : (∑ k ∈ S, ζ k * Torus.funRealCoeff ψ k) ^ 2 ≤ Nz *
      ∑ k ∈ S, q48bW k ^ (2 * b) * Torus.funRealCoeff ψ k ^ 2 := by
    have hcs0 := Finset.sum_mul_sq_le_sq_mul_sq S (fun k => q48bW k ^ (-b) * ζ k)
      (fun k => q48bW k ^ b * Torus.funRealCoeff ψ k)
    have e1 : ∀ k, (q48bW k ^ (-b) * ζ k) * (q48bW k ^ b * Torus.funRealCoeff ψ k) =
        ζ k * Torus.funRealCoeff ψ k := by
      intro k
      have := q48b_rpow_neg_mul (q48bW_pos k) b
      calc _ = (q48bW k ^ (-b) * q48bW k ^ b) * (ζ k * Torus.funRealCoeff ψ k) := by ring
        _ = _ := by rw [this, one_mul]
    have e2 : ∀ k, (q48bW k ^ (-b) * ζ k) ^ 2 = q48bW k ^ (-2 * b) * ζ k ^ 2 := by
      intro k
      rw [mul_pow, q48b_rpow_sq (q48bW_pos k)]; congr 2; ring
    have e3 : ∀ k, (q48bW k ^ b * Torus.funRealCoeff ψ k) ^ 2 =
        q48bW k ^ (2 * b) * Torus.funRealCoeff ψ k ^ 2 := by
      intro k
      rw [mul_pow, q48b_rpow_sq (q48bW_pos k)]
    simp_rw [e1, e2, e3] at hcs0
    exact hcs0
  have hsum_le : ∑ k ∈ S, q48bW k ^ (2 * b) * Torus.funRealCoeff ψ k ^ 2 ≤ sobolevNorm b ψ ^ 2 := by
    have hs := hmem.2
    have hle : ∑ k ∈ S, q48bW k ^ (2 * b) * Torus.funRealCoeff ψ k ^ 2 ≤
        ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * b) * Torus.funRealCoeff ψ k ^ 2 :=
      Summable.sum_le_tsum S (fun k _ => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _)
        (sq_nonneg _)) hs
    have hpos : 0 ≤ Torus.mean ψ ^ 2 + ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * b) *
        Torus.funRealCoeff ψ k ^ 2 := add_nonneg (sq_nonneg _) (tsum_nonneg fun k =>
          mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (sq_nonneg _))
    unfold sobolevNorm
    rw [Real.sq_sqrt hpos]
    exact hle.trans (le_add_of_nonneg_left (sq_nonneg _))
  have hTc : ∑ l ∈ T, q48bW l ^ (2 * a) * c l ^ 2 = X := by
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [hc]
    have hw := q48bW_pos l
    have h3 : q48bW l ^ (2 * a) * q48bW l ^ (-2 * a) = 1 := by
      rw [← Real.rpow_add hw]; simp
    calc q48bW l ^ (2 * a) * (q48bW l ^ (-2 * a) * Y l) ^ 2
        = (q48bW l ^ (2 * a) * q48bW l ^ (-2 * a)) * (q48bW l ^ (-2 * a) * Y l ^ 2) := by ring
      _ = _ := by rw [h3, one_mul]
  have hPn : sobolevNorm b ψ ≤ M * Real.sqrt X := by
    rw [hTc] at hnorm; exact hnorm
  have hPn0 : 0 ≤ sobolevNorm b ψ := Real.sqrt_nonneg _
  have hsq : sobolevNorm b ψ ^ 2 ≤ (M * Real.sqrt X) ^ 2 := pow_le_pow_left₀ hPn0 hPn 2
  have hE : X = ∑ k ∈ S, ζ k * Torus.funRealCoeff ψ k := by
    rw [← h1, h2, h3]
  have hfin : X ^ 2 ≤ (M ^ 2 * Nz) * X := by
    have hh2 : (∑ k ∈ S, ζ k * Torus.funRealCoeff ψ k) ^ 2 ≤ Nz * (M * Real.sqrt X) ^ 2 :=
      hcs.trans (mul_le_mul_of_nonneg_left (hsum_le.trans hsq) hNz0)
    rw [← hE, mul_pow, Real.sq_sqrt hX0] at hh2
    calc X ^ 2 ≤ Nz * (M ^ 2 * X) := hh2
      _ = (M ^ 2 * Nz) * X := by ring
  rcases eq_or_lt_of_le hX0 with h0 | hpos
  · rw [← h0]; positivity
  · have h5 : X * X ≤ (M ^ 2 * Nz) * X := by simpa [sq] using hfin
    exact le_of_mul_le_mul_right h5 hpos

end HRS.Uniform.Q54

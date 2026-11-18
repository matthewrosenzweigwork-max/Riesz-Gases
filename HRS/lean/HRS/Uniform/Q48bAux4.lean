import HRS.Uniform.Q48bAux3
import HRS.Uniform.Q48bInterp

/-!
# Q48b, part 4: the matrix of an operator on `E_m`, and the weighted bound from duality

For `V : E_m →L E_m` with matrix `A l k = ⟨V b_k, e_l⟩ ⟨k⟩^{-m}` (`b_k` the coordinate basis), the weighted bound at
level `a` (`WBound`) follows from the duality `⟨V z, φ⟩ = ⟨z, U φ⟩` and the `H^a`-boundedness of the centered `U`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q48b

open HRS HRS.PDE

variable {d : ℕ}

theorem q48b_rpow_sq {w : ℝ} (hw : 0 < w) (e : ℝ) : (w ^ e) ^ 2 = w ^ (2 * e) := by
  rw [two_mul, Real.rpow_add hw, sq]

theorem q48b_rpow_neg_mul {w : ℝ} (hw : 0 < w) (e : ℝ) : w ^ (-e) * w ^ e = 1 := by
  rw [← Real.rpow_add hw]; simp

open Classical in
/-- The coordinate basis vector `b_k` of `E_m = ℓ²`. -/
def q48bBasis (m : ℝ) (k : NonzeroLattice d) : NegSobolev d m :=
  (lp.single 2 k (1 : ℝ) : lp (fun _ : NonzeroLattice d => ℝ) 2)

/-- The matrix of `V` in the (unweighted) Fourier-coefficient normalisation. -/
def q48bMat (m : ℝ) (V : NegSobolev d m →L[ℝ] NegSobolev d m) (l k : NonzeroLattice d) : ℝ :=
  NegSobolev.fourierCoeff (V (q48bBasis m k)) l * q48bW k ^ (-m)

theorem q48b_coord_sum {m : ℝ} {ι : Type*} (s : Finset ι) (F : ι → NegSobolev d m)
    (l : NonzeroLattice d) :
    NegSobolev.coord (∑ i ∈ s, F i) l = ∑ i ∈ s, NegSobolev.coord (F i) l := by
  have h := congrFun (lp.coeFn_sum (E := fun _ : NonzeroLattice d => ℝ) (p := 2)
    (fun i => (F i : lp (fun _ : NonzeroLattice d => ℝ) 2)) s) l
  rw [Finset.sum_apply] at h
  exact h

theorem q48b_coord_smul {m : ℝ} (c : ℝ) (F : NegSobolev d m) (l : NonzeroLattice d) :
    NegSobolev.coord (c • F) l = c * NegSobolev.coord F l := by
  have h := congrFun (lp.coeFn_smul (E := fun _ : NonzeroLattice d => ℝ) (p := 2) c
    (F : lp (fun _ : NonzeroLattice d => ℝ) 2)) l
  rw [Pi.smul_apply, smul_eq_mul] at h
  exact h

theorem q48b_fourierCoeff_sum {m : ℝ} {ι : Type*} (s : Finset ι) (F : ι → NegSobolev d m)
    (l : NonzeroLattice d) :
    NegSobolev.fourierCoeff (∑ i ∈ s, F i) l = ∑ i ∈ s, NegSobolev.fourierCoeff (F i) l := by
  unfold NegSobolev.fourierCoeff
  rw [q48b_coord_sum, Finset.mul_sum]

theorem q48b_fourierCoeff_smul {m : ℝ} (c : ℝ) (F : NegSobolev d m) (l : NonzeroLattice d) :
    NegSobolev.fourierCoeff (c • F) l = c * NegSobolev.fourierCoeff F l := by
  unfold NegSobolev.fourierCoeff
  rw [q48b_coord_smul]; ring

theorem q48b_coord_basis {m : ℝ} (k l : NonzeroLattice d) :
    NegSobolev.coord (q48bBasis m k) l = if l = k then 1 else 0 := by
  classical
  unfold NegSobolev.coord q48bBasis
  show (lp.single 2 k (1 : ℝ) : NonzeroLattice d → ℝ) l = _
  rw [lp.single_apply]
  by_cases h : l = k
  · subst h; simp
  · simp [h]

/-- The finitely supported vector with Fourier coefficients `ζ` on `S`. -/
def q48bFin (m : ℝ) (S : Finset (NonzeroLattice d)) (ζ : NonzeroLattice d → ℝ) : NegSobolev d m :=
  ∑ k ∈ S, (q48bW k ^ (-m) * ζ k) • q48bBasis m k

theorem q48bFin_fourierCoeff (m : ℝ) (S : Finset (NonzeroLattice d)) (ζ : NonzeroLattice d → ℝ)
    (l : NonzeroLattice d) :
    NegSobolev.fourierCoeff (q48bFin m S ζ) l = if l ∈ S then ζ l else 0 := by
  classical
  unfold q48bFin
  rw [q48b_fourierCoeff_sum]
  simp_rw [q48b_fourierCoeff_smul]
  have hb : ∀ k, NegSobolev.fourierCoeff (q48bBasis m k) l = if l = k then q48bW l ^ m else 0 := by
    intro k
    unfold NegSobolev.fourierCoeff
    rw [q48b_coord_basis]
    split_ifs <;> simp [q48bW]
  simp_rw [hb]
  by_cases hl : l ∈ S
  · rw [if_pos hl, Finset.sum_eq_single l]
    · rw [if_pos rfl, mul_comm (q48bW l ^ (-m)) (ζ l), mul_assoc, q48b_rpow_neg_mul (q48bW_pos l) m,
        mul_one]
    · intro k _ hk; simp [Ne.symm hk]
    · intro h; exact absurd hl h
  · rw [if_neg hl]
    refine Finset.sum_eq_zero fun k hk => ?_
    have : l ≠ k := fun h => hl (h ▸ hk)
    simp [this]


theorem q48bFin_V {m : ℝ} (V : NegSobolev d m →L[ℝ] NegSobolev d m) (S : Finset (NonzeroLattice d))
    (ζ : NonzeroLattice d → ℝ) (l : NonzeroLattice d) :
    NegSobolev.fourierCoeff (V (q48bFin m S ζ)) l = ∑ k ∈ S, q48bMat m V l k * ζ k := by
  unfold q48bFin
  rw [map_sum, q48b_fourierCoeff_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, q48b_fourierCoeff_smul, q48bMat]
  ring

theorem q48b_eval_test {m : ℝ} (F : NegSobolev d m) (T : Finset (NonzeroLattice d))
    (c : NonzeroLattice d → ℝ) :
    NegSobolev.eval F (q48bTest T c) = ∑ l ∈ T, NegSobolev.fourierCoeff F l * c l := by
  classical
  unfold NegSobolev.eval
  rw [tsum_eq_sum (s := T)]
  · refine Finset.sum_congr rfl fun l hl => ?_
    rw [q48bTest_coeff, if_pos hl]
  · intro k hk
    rw [q48bTest_coeff, if_neg hk, mul_zero]

theorem q48b_eval_fin {m : ℝ} (S : Finset (NonzeroLattice d)) (ζ : NonzeroLattice d → ℝ)
    (ψ : Torus d → ℝ) :
    NegSobolev.eval (q48bFin m S ζ) ψ = ∑ k ∈ S, ζ k * Torus.funRealCoeff ψ k := by
  classical
  unfold NegSobolev.eval
  rw [tsum_eq_sum (s := S)]
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [q48bFin_fourierCoeff, if_pos hk]
  · intro k hk
    rw [q48bFin_fourierCoeff, if_neg hk, zero_mul]

/-- The weighted bound at level `a` from duality and boundedness of the centered `U`. -/
theorem q48b_wbound_of_duality {m a : ℝ} (ρβ : Torus d → ℝ) (Up : (Torus d → ℝ) → Torus d → ℝ)
    (V : NegSobolev d m →L[ℝ] NegSobolev d m)
    (hdual : ∀ (z : NegSobolev d m) (φ : Torus d → ℝ), Torus.IsSmooth φ →
      NegSobolev.eval (V z) φ = NegSobolev.eval z (Up φ))
    (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ (T : Finset (NonzeroLattice d)) (c : NonzeroLattice d → ℝ),
      sobolevNorm a (projMean (withDensityReal ρβ) (q48bTest T c)) ≤
        K * Real.sqrt (∑ l ∈ T, q48bW l ^ (2 * a) * c l ^ 2))
    (Cdec : ℝ) (hC : 0 ≤ Cdec)
    (hdec : ∀ φ : Torus d → ℝ, Continuous φ → MemSobolev a φ →
      MemSobolev a (projMean (withDensityReal ρβ) (Up φ)) ∧
        sobolevNorm a (projMean (withDensityReal ρβ) (Up φ)) ≤
          Cdec * sobolevNorm a (projMean (withDensityReal ρβ) φ)) :
    ∀ S T : Finset (NonzeroLattice d), WBound q48bW (q48bMat m V) S T a (Cdec * K) := by
  intro S T ζ
  set Y : NonzeroLattice d → ℝ := fun l => ∑ k ∈ S, q48bMat m V l k * ζ k with hY
  set c : NonzeroLattice d → ℝ := fun l => q48bW l ^ (-2 * a) * Y l with hc
  set φ := q48bTest T c with hφ
  set z := q48bFin m S ζ with hz
  set X : ℝ := ∑ l ∈ T, q48bW l ^ (-2 * a) * Y l ^ 2 with hX
  set Nz : ℝ := ∑ k ∈ S, q48bW k ^ (-2 * a) * ζ k ^ 2 with hNz
  set M : ℝ := Cdec * K with hM
  have hM0 : 0 ≤ M := mul_nonneg hC hK0
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun l _ =>
    mul_nonneg (Real.rpow_nonneg (q48bW_pos l).le _) (sq_nonneg _)
  have hNz0 : 0 ≤ Nz := Finset.sum_nonneg fun l _ =>
    mul_nonneg (Real.rpow_nonneg (q48bW_pos l).le _) (sq_nonneg _)
  show X ≤ M ^ 2 * Nz
  -- the pairing `⟨V z, φ⟩ = X`
  have h1 : NegSobolev.eval (V z) φ = X := by
    rw [hφ, q48b_eval_test]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hz, q48bFin_V]
    simp only [hc, hY]
    have : (∑ k ∈ S, q48bMat m V l k * ζ k) = Y l := rfl
    rw [this]
    ring
  -- duality
  have hsm : Torus.IsSmooth φ := q48bTest_smooth T c
  have h2 : NegSobolev.eval (V z) φ = NegSobolev.eval z (Up φ) := hdual z φ hsm
  have hdφ := hdec φ (q48bTest_continuous T c) (q48bTest_memSobolev T c a)
  obtain ⟨hmem, hnorm⟩ := hdφ
  set ψ := Up φ with hψ
  have h3 : NegSobolev.eval z ψ = ∑ k ∈ S, ζ k * Torus.funRealCoeff (projMean (withDensityReal ρβ) ψ) k := by
    rw [hz, q48b_eval_fin]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [q48b_funRealCoeff_projMean (withDensityReal ρβ) hmem.1 k]
  -- Cauchy-Schwarz
  set Pψ := projMean (withDensityReal ρβ) ψ with hPψ
  set sj : ℝ := Real.sqrt (∑ k ∈ S, q48bW k ^ (2 * a) * Torus.funRealCoeff Pψ k ^ 2) with hsj
  have hcs : (∑ k ∈ S, ζ k * Torus.funRealCoeff Pψ k) ^ 2 ≤ Nz *
      ∑ k ∈ S, q48bW k ^ (2 * a) * Torus.funRealCoeff Pψ k ^ 2 := by
    have hcs0 := Finset.sum_mul_sq_le_sq_mul_sq S (fun k => q48bW k ^ (-a) * ζ k)
      (fun k => q48bW k ^ a * Torus.funRealCoeff Pψ k)
    have e1 : ∀ k, (q48bW k ^ (-a) * ζ k) * (q48bW k ^ a * Torus.funRealCoeff Pψ k) =
        ζ k * Torus.funRealCoeff Pψ k := by
      intro k
      have := q48b_rpow_neg_mul (q48bW_pos k) a
      calc _ = (q48bW k ^ (-a) * q48bW k ^ a) * (ζ k * Torus.funRealCoeff Pψ k) := by ring
        _ = _ := by rw [this, one_mul]
    have e2 : ∀ k, (q48bW k ^ (-a) * ζ k) ^ 2 = q48bW k ^ (-2 * a) * ζ k ^ 2 := by
      intro k
      rw [mul_pow, q48b_rpow_sq (q48bW_pos k)]; congr 2; ring
    have e3 : ∀ k, (q48bW k ^ a * Torus.funRealCoeff Pψ k) ^ 2 =
        q48bW k ^ (2 * a) * Torus.funRealCoeff Pψ k ^ 2 := by
      intro k
      rw [mul_pow, q48b_rpow_sq (q48bW_pos k)]
    simp_rw [e1, e2, e3] at hcs0
    exact hcs0
  -- the Sobolev norm of `Pψ`
  have hsum_le : ∑ k ∈ S, q48bW k ^ (2 * a) * Torus.funRealCoeff Pψ k ^ 2 ≤
      sobolevNorm a Pψ ^ 2 := by
    have hs := hmem.2
    have hle : ∑ k ∈ S, q48bW k ^ (2 * a) * Torus.funRealCoeff Pψ k ^ 2 ≤
        ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * a) * Torus.funRealCoeff Pψ k ^ 2 :=
      Summable.sum_le_tsum S (fun k _ => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _)
        (sq_nonneg _)) hs
    have hpos : 0 ≤ Torus.mean Pψ ^ 2 + ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * a) *
        Torus.funRealCoeff Pψ k ^ 2 := add_nonneg (sq_nonneg _) (tsum_nonneg fun k =>
          mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (sq_nonneg _))
    unfold sobolevNorm
    rw [Real.sq_sqrt hpos]
    exact hle.trans (le_add_of_nonneg_left (sq_nonneg _))
  -- bound by `X`
  have hTc : ∑ l ∈ T, q48bW l ^ (2 * a) * c l ^ 2 = X := by
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [hc]
    have hw := q48bW_pos l
    have h2 : (q48bW l ^ (-2 * a)) ^ 2 = q48bW l ^ (-2 * a) * q48bW l ^ (-2 * a) := sq _
    have h3 : q48bW l ^ (2 * a) * q48bW l ^ (-2 * a) = 1 := by
      rw [← Real.rpow_add hw]; simp
    calc q48bW l ^ (2 * a) * (q48bW l ^ (-2 * a) * Y l) ^ 2
        = (q48bW l ^ (2 * a) * q48bW l ^ (-2 * a)) * (q48bW l ^ (-2 * a) * Y l ^ 2) := by ring
      _ = _ := by rw [h3, one_mul]
  have hKb := hK T c
  rw [hTc] at hKb
  have hPn : sobolevNorm a Pψ ≤ M * Real.sqrt X := by
    have := hnorm.trans (mul_le_mul_of_nonneg_left hKb hC)
    simpa [hM, mul_assoc] using this
  have hPn0 : 0 ≤ sobolevNorm a Pψ := Real.sqrt_nonneg _
  have hsq : sobolevNorm a Pψ ^ 2 ≤ (M * Real.sqrt X) ^ 2 := pow_le_pow_left₀ hPn0 hPn 2
  have hE : X = ∑ k ∈ S, ζ k * Torus.funRealCoeff Pψ k := by
    rw [← h1, h2, h3]
  have hfin : X ^ 2 ≤ (M ^ 2 * Nz) * X := by
    have hh2 : (∑ k ∈ S, ζ k * Torus.funRealCoeff Pψ k) ^ 2 ≤ Nz * (M * Real.sqrt X) ^ 2 :=
      hcs.trans (mul_le_mul_of_nonneg_left (hsum_le.trans hsq) hNz0)
    rw [← hE, mul_pow, Real.sq_sqrt hX0] at hh2
    calc X ^ 2 ≤ Nz * (M ^ 2 * X) := hh2
      _ = (M ^ 2 * Nz) * X := by ring
  rcases eq_or_lt_of_le hX0 with h0 | hpos
  · rw [← h0]; positivity
  · have h5 : X * X ≤ (M ^ 2 * Nz) * X := by simpa [sq] using hfin
    exact le_of_mul_le_mul_right h5 hpos

end HRS.Uniform.Q48b

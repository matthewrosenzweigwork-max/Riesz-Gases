import HRS.Uniform.Q54cAux34
import HRS.PDE.Fourier

/-!
# Packet GFB3, part 1: smoothness of `y ↦ b_{y,j} ∈ E_γ` and bounds on its iterated derivatives
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.GF

open HRS HRS.Uniform HRS.Uniform.Q54c

variable {d : ℕ}

/-- The `k`-th term of the series of `y ↦ b_{y,j}` (lifted to `ℝ^d`). -/
def gfb3_term (γ : ℝ) (j : Fin d) (k : NonzeroLattice d) (y : Euc d) : NegSobolev d γ :=
  (Lattice.jp k.1 ^ (-γ) * Dmode k j y) •
    ((lp.single 2 k (1 : ℝ) : lp (fun _ : NonzeroLattice d => ℝ) 2) : NegSobolev d γ)

lemma gfb3_Dmode_periodic (k : NonzeroLattice d) (j : Fin d) (z : Euc d) (n : Lattice d) :
    Dmode k j (z + Lattice.toEuc n) = Dmode k j z := by
  have h : Torus.freqFunctional k.1 (z + Lattice.toEuc n) =
      Torus.freqFunctional k.1 z + ((∑ i, k.1 i * n i : ℤ) : ℝ) * (2 * Real.pi) := by
    rw [map_add, Torus.freqFunctional_apply, Torus.freqFunctional_apply]
    simp only [Lattice.dot, Lattice.toEuc]
    push_cast
    ring
  unfold Dmode
  rw [h]
  split_ifs
  · rw [Real.sin_add_int_mul_two_pi]
  · rw [Real.cos_add_int_mul_two_pi]

lemma gfb3_partialDeriv_realMode_mk (k : NonzeroLattice d) (j : Fin d) (y : Euc d) :
    Torus.partialDeriv j (Torus.realMode k) (Torus.mk y) = Dmode k j y := by
  obtain ⟨n, hn⟩ := Torus.rep_mk y
  rw [← Dmode_rep, hn, gfb3_Dmode_periodic]

lemma gfb3_bVec_hasSum {γ : ℝ} (hγ : (d : ℝ) / 2 + 1 < γ) (j : Fin d) (y : Euc d) :
    HasSum (fun k => gfb3_term γ j k y) (bVec γ j (Torus.mk y)) := by
  have h := lp.hasSum_single (E := fun _ : NonzeroLattice d => ℝ) (p := 2) (by simp)
    (bVec γ j (Torus.mk y) : lp (fun _ : NonzeroLattice d => ℝ) 2)
  have hfun : (fun k => gfb3_term γ j k y) =
      fun k => lp.single 2 k (NegSobolev.coord (bVec γ j (Torus.mk y)) k) := by
    funext k
    unfold gfb3_term
    have hc : NegSobolev.coord (bVec γ j (Torus.mk y)) k = Lattice.jp k.1 ^ (-γ) * Dmode k j y := by
      rw [← gfb3_partialDeriv_realMode_mk]
      exact HRS.Uniform.Q14.q14_coord_bVec hγ j _ k
    rw [hc, ← lp.single_smul]
    simp
    rfl
  rw [hfun]
  exact h

lemma gfb3_Dmode_comp (k : NonzeroLattice d) (j : Fin d) :
    ∃ A B : ℝ, |A| + |B| ≤ Real.sqrt 2 * Lattice.jp k.1 ∧
      Dmode k j = (fun t => A * Real.cos t + B * Real.sin t) ∘ ⇑(Torus.freqFunctional k.1) := by
  have h2 : |(2 : ℝ) * Real.pi| * |(k.1 j : ℝ)| ≤ Lattice.jp k.1 := by
    rw [abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    exact HRS.Uniform.Q14.q14_two_pi_k_le k.1 j
  have hc : |2 * Real.pi * (k.1 j : ℝ) * Real.sqrt 2| ≤ Real.sqrt 2 * Lattice.jp k.1 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg 2)]
    nlinarith [Real.sqrt_nonneg 2]
  by_cases hp : Lattice.IsPosHalf k.1
  · refine ⟨0, -(2 * Real.pi * (k.1 j : ℝ) * Real.sqrt 2), by simpa using hc, ?_⟩
    funext z
    simp [Dmode, hp]
  · refine ⟨2 * Real.pi * (k.1 j : ℝ) * Real.sqrt 2, 0, by simpa using hc, ?_⟩
    funext z
    simp [Dmode, hp]

lemma gfb3_contDiff_Dmode (k : NonzeroLattice d) (j : Fin d) (n : WithTop ℕ∞) :
    ContDiff ℝ n (Dmode k j) := by
  obtain ⟨A, B, -, h⟩ := gfb3_Dmode_comp k j
  rw [h]
  exact ((contDiff_const.mul Real.contDiff_cos).add (contDiff_const.mul Real.contDiff_sin)).comp
    (Torus.freqFunctional k.1).contDiff

lemma gfb3_contDiff_term (γ : ℝ) (j : Fin d) (k : NonzeroLattice d) (n : WithTop ℕ∞) :
    ContDiff ℝ n (gfb3_term γ j k) := by
  unfold gfb3_term
  exact (contDiff_const.mul (gfb3_contDiff_Dmode k j n)).smul contDiff_const

lemma gfb3_norm_iter_term (γ : ℝ) (j : Fin d) (k : NonzeroLattice d) (i : ℕ) (y : Euc d) :
    ‖iteratedFDeriv ℝ i (gfb3_term γ j k) y‖ ≤
      Real.sqrt 2 * Lattice.jp k.1 ^ (-γ) * Lattice.jp k.1 ^ (i + 1) := by
  obtain ⟨A, B, hAB, h⟩ := gfb3_Dmode_comp k j
  set v : NegSobolev d γ := ((lp.single 2 k (1 : ℝ) : lp (fun _ : NonzeroLattice d => ℝ) 2) : NegSobolev d γ)
  have hv : ‖v‖ = 1 := by
    show ‖(lp.single 2 k (1 : ℝ) : lp (fun _ : NonzeroLattice d => ℝ) 2)‖ = 1
    rw [lp.norm_single (by norm_num)]; simp
  set w : ℝ := Lattice.jp k.1 ^ (-γ) with hw
  have hw0 : 0 ≤ w := Real.rpow_nonneg (Torus.jp_pos k.1).le _
  set g : Euc d → ℝ := fun y => w * Dmode k j y with hg
  have hterm : gfb3_term γ j k = (ContinuousLinearMap.toSpanSingleton ℝ v) ∘ g := by
    funext z; simp only [gfb3_term, hg, v, hw, Function.comp]; rfl
  have hgd : ContDiff ℝ ⊤ g := (contDiff_const.mul (gfb3_contDiff_Dmode k j ⊤))
  have hL := ContinuousLinearMap.norm_iteratedFDeriv_comp_left
    (ContinuousLinearMap.toSpanSingleton ℝ v) (hgd.contDiffAt (x := y)) (n := i) (by exact_mod_cast le_top)
  rw [hterm]
  refine hL.trans ?_
  rw [ContinuousLinearMap.norm_toSpanSingleton, hv, one_mul]
  have hg2 : g = (fun t => (w * A) * Real.cos t + (w * B) * Real.sin t) ∘ ⇑(Torus.freqFunctional k.1) := by
    funext z
    have := congrFun h z
    simp only [hg, this, Function.comp]
    ring
  have hfr : ‖(Torus.freqFunctional k.1 : Euc d →L[ℝ] ℝ)‖ ≤ Lattice.jp k.1 :=
    (Torus.norm_freqFunctional_le k.1).trans (Torus.two_pi_enorm_le_jp k.1)
  have hb := Torus.norm_iteratedFDeriv_comp_functional (d := d)
    (fun t => (w * A) * Real.cos t + (w * B) * Real.sin t)
    ((contDiff_const.mul Real.contDiff_cos).add (contDiff_const.mul Real.contDiff_sin)) (|w * A| + |w * B|)
    (fun i t => PDE.norm_iteratedFDeriv_trig_comb _ _ i t) (Torus.freqFunctional k.1) i y
  rw [hg2]
  refine hb.trans ?_
  have h1 : |w * A| + |w * B| ≤ w * (Real.sqrt 2 * Lattice.jp k.1) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hw0, ← mul_add]
    exact mul_le_mul_of_nonneg_left hAB hw0
  calc (|w * A| + |w * B|) * ‖(Torus.freqFunctional k.1 : Euc d →L[ℝ] ℝ)‖ ^ i
      ≤ (w * (Real.sqrt 2 * Lattice.jp k.1)) * Lattice.jp k.1 ^ i :=
        mul_le_mul h1 (pow_le_pow_left₀ (norm_nonneg _) hfr i) (by positivity)
          (mul_nonneg hw0 (mul_nonneg (Real.sqrt_nonneg 2) (Torus.jp_pos k.1).le))
    _ = _ := by rw [pow_succ]; ring

/-- The summable majorant of the `i`-th derivative. -/
def gfb3_majorant (d : ℕ) (γ : ℝ) (i : ℕ) (k : NonzeroLattice d) : ℝ :=
  Real.sqrt 2 * Lattice.jp k.1 ^ (-γ) * Lattice.jp k.1 ^ (i + 1)

lemma gfb3_summable_majorant {γ : ℝ} (i : ℕ) (hγ : (d : ℝ) + i + 1 < γ) :
    Summable (gfb3_majorant d γ i) := by
  have hs := summable_jp_rpow (d := d) ((γ - i - 1) / 2) (by linarith)
  refine (hs.mul_left (Real.sqrt 2)).congr fun k => ?_
  unfold gfb3_majorant
  have hj := Torus.jp_pos k.1
  rw [mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hj]
  congr 2
  push_cast
  ring

lemma gfb3_lift_eq {γ : ℝ} (hγ : (d : ℝ) / 2 + 1 < γ) (j : Fin d) :
    (fun y : Euc d => bVec γ j (Torus.mk y)) = fun y => ∑' k, gfb3_term γ j k y := by
  funext y
  exact (gfb3_bVec_hasSum hγ j y).tsum_eq.symm

lemma gfb3_bVec_contDiff (n : ℕ) {γ : ℝ} (hγ : (d : ℝ) + n + 1 < γ) (j : Fin d) :
    ContDiff ℝ n (fun y : Euc d => bVec γ j (Torus.mk y)) := by
  have hγ' : (d : ℝ) / 2 + 1 < γ := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  rw [gfb3_lift_eq hγ' j]
  refine contDiff_tsum (v := fun i => gfb3_majorant d γ i) (fun k => gfb3_contDiff_term γ j k n)
    (fun i hi => gfb3_summable_majorant i ?_) (fun i k y hi => gfb3_norm_iter_term γ j k i y)
  have : (i : ℝ) ≤ n := by exact_mod_cast hi
  linarith

lemma gfb3_bVec_iter_bound (n : ℕ) {γ : ℝ} (hγ : (d : ℝ) + n + 1 < γ) (j : Fin d)
    (i : ℕ) (hi : i ≤ n) (y : Euc d) :
    ‖iteratedFDeriv ℝ i (fun y : Euc d => bVec γ j (Torus.mk y)) y‖ ≤
      ∑' k, gfb3_majorant d γ i k := by
  have hγ' : (d : ℝ) / 2 + 1 < γ := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hsum : ∀ i : ℕ, i ≤ n → Summable (gfb3_majorant d γ i) := fun i hi =>
    gfb3_summable_majorant i (by
      have : (i : ℝ) ≤ n := by exact_mod_cast hi
      linarith)
  rw [gfb3_lift_eq hγ' j]
  rw [iteratedFDeriv_tsum_apply (v := fun i => gfb3_majorant d γ i) (N := n)
    (fun k => gfb3_contDiff_term γ j k n) (fun i hi => hsum i (by exact_mod_cast hi))
    (fun i k y hi => gfb3_norm_iter_term γ j k i y) (by exact_mod_cast hi)]
  refine (norm_tsum_le_tsum_norm ?_).trans ?_
  · exact (hsum i hi).of_nonneg_of_le (fun k => norm_nonneg _)
      (fun k => gfb3_norm_iter_term γ j k i y)
  · exact ((hsum i hi).of_nonneg_of_le (fun k => norm_nonneg _)
      (fun k => gfb3_norm_iter_term γ j k i y)).tsum_le_tsum
      (fun k => gfb3_norm_iter_term γ j k i y) (hsum i hi)

end HRS.GF

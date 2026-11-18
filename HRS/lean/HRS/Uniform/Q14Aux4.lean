import HRS.Uniform.Q14Aux3
import HRS.Uniform.Comparison

/-!
# Q14, part 4: the vectors `b_{x,j} = -∂_j δ_x` are bounded and Lipschitz in `H^{-γ}`, `γ > d/2 + 2`
-/

noncomputable section

open HRS
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q14

section TorusAnalysis

variable {d : ℕ}

lemma q14_mk_add (a b : Euc d) : Torus.mk (a + b) = Torus.mk a + Torus.mk b := by
  funext i
  simp [Torus.mk]

lemma q14_dot_add (k : Lattice d) (a b : Euc d) :
    Lattice.dot k (a + b) = Lattice.dot k a + Lattice.dot k b := by
  simp [Lattice.dot, mul_add, Finset.sum_add_distrib]

lemma q14_eq_mk (x y : Torus d) :
    x = Torus.mk (Torus.rep y + Torus.centeredRep (x - y)) := by
  rw [q14_mk_add, Torus.mk_rep]
  have : Torus.mk (Torus.centeredRep (x - y)) = x - y := KernelGrad.mk_centeredRep (x - y)
  rw [this]; abel

lemma q14_abs_dot_le (k : Lattice d) (z : Euc d) :
    |2 * Real.pi * Lattice.dot k z| ≤ 2 * Real.pi * Lattice.enorm k * ‖z‖ := by
  have := (Torus.freqFunctional k).le_opNorm z
  rw [Torus.freqFunctional_apply, Real.norm_eq_abs] at this
  exact this.trans (mul_le_mul_of_nonneg_right (Torus.norm_freqFunctional_le k) (norm_nonneg _))

lemma q14_phase_diff (k : Lattice d) (x y : Torus d) :
    |2 * Real.pi * Lattice.dot k (Torus.rep y + Torus.centeredRep (x - y)) -
        2 * Real.pi * Lattice.dot k (Torus.rep y)| ≤
      2 * Real.pi * Lattice.enorm k * Torus.tdist x y := by
  rw [q14_dot_add, mul_add, add_sub_cancel_left]
  exact q14_abs_dot_le k _

lemma q14_cos_lip (k : Lattice d) (x y : Torus d) :
    |Torus.cosMode k x - Torus.cosMode k y| ≤ 2 * Real.pi * Lattice.enorm k * Torus.tdist x y := by
  have h1 := Torus.cosMode_mk k (Torus.rep y + Torus.centeredRep (x - y))
  rw [← q14_eq_mk] at h1
  have h2 := Torus.cosMode_mk k (Torus.rep y)
  rw [Torus.mk_rep] at h2
  rw [h1, h2]
  exact (Real.abs_cos_sub_cos_le _ _).trans (q14_phase_diff k x y)

lemma q14_sin_lip (k : Lattice d) (x y : Torus d) :
    |Torus.sinMode k x - Torus.sinMode k y| ≤ 2 * Real.pi * Lattice.enorm k * Torus.tdist x y := by
  have h1 := Torus.sinMode_mk k (Torus.rep y + Torus.centeredRep (x - y))
  rw [← q14_eq_mk] at h1
  have h2 := Torus.sinMode_mk k (Torus.rep y)
  rw [Torus.mk_rep] at h2
  rw [h1, h2]
  exact (Real.abs_sin_sub_sin_le _ _).trans (q14_phase_diff k x y)

lemma q14_abs_cos_le (k : Lattice d) (x : Torus d) : |Torus.cosMode k x| ≤ 1 := by
  have h := Torus.cosMode_mk k (Torus.rep x)
  rw [Torus.mk_rep] at h
  rw [h]; exact Real.abs_cos_le_one _

lemma q14_abs_sin_le (k : Lattice d) (x : Torus d) : |Torus.sinMode k x| ≤ 1 := by
  have h := Torus.sinMode_mk k (Torus.rep x)
  rw [Torus.mk_rep] at h
  rw [h]; exact Real.abs_sin_le_one _

open Classical in
/-- The derivative of the real mode. -/
lemma q14_partialDeriv_realMode (j : Fin d) (k : NonzeroLattice d) (x : Torus d) :
    Torus.partialDeriv j (Torus.realMode k) x =
      2 * Real.pi * (k.1 j : ℝ) * Real.sqrt 2 *
        (if Lattice.IsPosHalf k.1 then -Torus.sinMode k.1 x else Torus.cosMode k.1 x) := by
  unfold Torus.partialDeriv
  have hφ : Torus.freqFunctional k.1 (EuclideanSpace.single j 1) = 2 * Real.pi * (k.1 j : ℝ) := by
    rw [Torus.freqFunctional_apply]
    simp [Lattice.dot, PiLp.single_apply]
  by_cases hp : Lattice.IsPosHalf k.1
  · have hl : Torus.lift (Torus.realMode k) =
        fun z => Real.sqrt 2 * Real.cos (Torus.freqFunctional k.1 z) := by
      funext z
      simp [Torus.lift, Torus.realMode, hp, Torus.cosMode_mk, Torus.freqFunctional_apply]
    rw [hl]
    have hd := (((Torus.freqFunctional k.1).hasFDerivAt (x := Torus.rep x)).cos).const_mul
      (Real.sqrt 2)
    rw [hd.fderiv]
    have hs : Real.sin (Torus.freqFunctional k.1 (Torus.rep x)) = Torus.sinMode k.1 x := by
      have h := Torus.sinMode_mk k.1 (Torus.rep x)
      rw [Torus.mk_rep] at h
      rw [h, Torus.freqFunctional_apply]
    simp only [hp, ite_true, ContinuousLinearMap.smul_apply, hφ, hs, smul_eq_mul]
    ring
  · have hl : Torus.lift (Torus.realMode k) =
        fun z => Real.sqrt 2 * Real.sin (Torus.freqFunctional k.1 z) := by
      funext z
      simp [Torus.lift, Torus.realMode, hp, Torus.sinMode_mk, Torus.freqFunctional_apply]
    rw [hl]
    have hd := (((Torus.freqFunctional k.1).hasFDerivAt (x := Torus.rep x)).sin).const_mul
      (Real.sqrt 2)
    rw [hd.fderiv]
    have hs : Real.cos (Torus.freqFunctional k.1 (Torus.rep x)) = Torus.cosMode k.1 x := by
      have h := Torus.cosMode_mk k.1 (Torus.rep x)
      rw [Torus.mk_rep] at h
      rw [h, Torus.freqFunctional_apply]
    simp only [hp, ite_false, ContinuousLinearMap.smul_apply, hφ, hs, smul_eq_mul]
    ring

end TorusAnalysis

section BVec

variable {d : ℕ}

lemma q14_abs_k_le (k : Lattice d) (j : Fin d) : |(k j : ℝ)| ≤ Lattice.enorm k := by
  unfold Lattice.enorm
  have := PiLp.norm_apply_le (Lattice.toEuc k) j
  simpa [Lattice.toEuc] using this

lemma q14_two_pi_k_le (k : Lattice d) (j : Fin d) : 2 * Real.pi * |(k j : ℝ)| ≤ Lattice.jp k :=
  le_trans (mul_le_mul_of_nonneg_left (q14_abs_k_le k j) (by positivity))
    (Torus.two_pi_enorm_le_jp k)

open Classical in
lemma q14_coef_bound (j : Fin d) (k : NonzeroLattice d) (x : Torus d) :
    |Torus.partialDeriv j (Torus.realMode k) x| ≤ Real.sqrt 2 * Lattice.jp k.1 := by
  rw [q14_partialDeriv_realMode, abs_mul, abs_mul, abs_mul]
  have hs : |(if Lattice.IsPosHalf k.1 then -Torus.sinMode k.1 x else Torus.cosMode k.1 x)| ≤ 1 := by
    split_ifs
    · rw [abs_neg]; exact q14_abs_sin_le _ _
    · exact q14_abs_cos_le _ _
  have h2 : |(2 : ℝ) * Real.pi| * |(k.1 j : ℝ)| ≤ Lattice.jp k.1 := by
    rw [abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]; exact q14_two_pi_k_le k.1 j
  rw [abs_of_nonneg (Real.sqrt_nonneg 2)]
  calc |(2 : ℝ) * Real.pi| * |(k.1 j : ℝ)| * Real.sqrt 2 * _ ≤
      Lattice.jp k.1 * Real.sqrt 2 * 1 := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg 2)) hs (abs_nonneg _)
          (by have := Torus.jp_ge_one k.1; positivity)
    _ = _ := by ring

open Classical in
lemma q14_coef_lip (j : Fin d) (k : NonzeroLattice d) (x y : Torus d) :
    |Torus.partialDeriv j (Torus.realMode k) x - Torus.partialDeriv j (Torus.realMode k) y| ≤
      Real.sqrt 2 * Lattice.jp k.1 ^ 2 * Torus.tdist x y := by
  rw [q14_partialDeriv_realMode, q14_partialDeriv_realMode, ← mul_sub, abs_mul]
  have hs : |(if Lattice.IsPosHalf k.1 then -Torus.sinMode k.1 x else Torus.cosMode k.1 x) -
      (if Lattice.IsPosHalf k.1 then -Torus.sinMode k.1 y else Torus.cosMode k.1 y)| ≤
      2 * Real.pi * Lattice.enorm k.1 * Torus.tdist x y := by
    split_ifs
    · have := q14_sin_lip k.1 x y
      rwa [show -Torus.sinMode k.1 x - -Torus.sinMode k.1 y =
        -(Torus.sinMode k.1 x - Torus.sinMode k.1 y) by ring, abs_neg]
    · exact q14_cos_lip k.1 x y
  have h2 : |2 * Real.pi * (k.1 j : ℝ) * Real.sqrt 2| ≤ Lattice.jp k.1 * Real.sqrt 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg 2),
      abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    exact mul_le_mul_of_nonneg_right (q14_two_pi_k_le k.1 j) (Real.sqrt_nonneg 2)
  calc _ ≤ (Lattice.jp k.1 * Real.sqrt 2) * (2 * Real.pi * Lattice.enorm k.1 * Torus.tdist x y) :=
        mul_le_mul h2 hs (abs_nonneg _) (by have := Torus.jp_ge_one k.1; positivity)
    _ ≤ (Lattice.jp k.1 * Real.sqrt 2) * (Lattice.jp k.1 * Torus.tdist x y) := by
        refine mul_le_mul_of_nonneg_left ?_ (by have := Torus.jp_ge_one k.1; positivity)
        exact mul_le_mul_of_nonneg_right (Torus.two_pi_enorm_le_jp k.1) (by
          unfold Torus.tdist; exact norm_nonneg _)
    _ = _ := by ring

lemma q14_term_bound (γ : ℝ) (e : ℕ) (k : NonzeroLattice d) {c t : ℝ}
    (hc : |c| ≤ Real.sqrt 2 * Lattice.jp k.1 ^ e * t) :
    (Lattice.jp k.1 ^ (-γ) * c) ^ 2 ≤ 2 * t ^ 2 * Lattice.jp k.1 ^ (-(2 * (γ - e))) := by
  have hj := Torus.jp_pos k.1
  have h0 : 0 ≤ Real.sqrt 2 * Lattice.jp k.1 ^ e * t := (abs_nonneg _).trans hc
  have h1 : c ^ 2 ≤ (Real.sqrt 2 * Lattice.jp k.1 ^ e * t) ^ 2 := by
    rw [← sq_abs c]; exact pow_le_pow_left₀ (abs_nonneg _) hc 2
  have h2 : (Real.sqrt 2 * Lattice.jp k.1 ^ e * t) ^ 2 =
      2 * t ^ 2 * Lattice.jp k.1 ^ (2 * e) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num), ← pow_mul]; ring_nf
  have h3 : (Lattice.jp k.1 ^ (-γ)) ^ 2 * Lattice.jp k.1 ^ (2 * e) =
      Lattice.jp k.1 ^ (-(2 * (γ - e))) := by
    rw [Torus.jp_rpow_sq, ← Real.rpow_natCast, ← Real.rpow_add hj]
    congr 1; push_cast; ring
  calc (Lattice.jp k.1 ^ (-γ) * c) ^ 2 = (Lattice.jp k.1 ^ (-γ)) ^ 2 * c ^ 2 := mul_pow _ _ _
    _ ≤ (Lattice.jp k.1 ^ (-γ)) ^ 2 * (2 * t ^ 2 * Lattice.jp k.1 ^ (2 * e)) := by
        rw [← h2]; exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    _ = 2 * t ^ 2 * ((Lattice.jp k.1 ^ (-γ)) ^ 2 * Lattice.jp k.1 ^ (2 * e)) := by ring
    _ = _ := by rw [h3]

end BVec

section BVecNorm

variable {d : ℕ}

/-- The lattice sum `∑_{k≠0} ⟨k⟩^{-2m}`. -/
def q14S (d : ℕ) (m : ℝ) : ℝ := ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m))

lemma q14S_nonneg (d : ℕ) (m : ℝ) : 0 ≤ q14S d m :=
  tsum_nonneg fun k => Real.rpow_nonneg (Torus.jp_pos k.1).le _

lemma q14_memℓp {γ : ℝ} (hγ : (d : ℝ) / 2 + 1 < γ) (j : Fin d) (x : Torus d) :
    Memℓp (fun k : NonzeroLattice d =>
      Lattice.jp k.1 ^ (-γ) * Torus.partialDeriv j (Torus.realMode k) x) 2 := by
  rw [Torus.memℓp_two_iff]
  have hs := summable_jp_rpow (d := d) (γ - 1) (by linarith)
  refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_) (hs.mul_left 2)
  have := q14_term_bound γ 1 k (c := Torus.partialDeriv j (Torus.realMode k) x) (t := 1)
    (by simpa using q14_coef_bound j k x)
  simpa using this

lemma q14_coord_bVec {γ : ℝ} (hγ : (d : ℝ) / 2 + 1 < γ) (j : Fin d) (x : Torus d)
    (k : NonzeroLattice d) :
    NegSobolev.coord (bVec γ j x) k =
      Lattice.jp k.1 ^ (-γ) * Torus.partialDeriv j (Torus.realMode k) x := by
  unfold bVec
  exact NegSobolev.coord_ofSeq_of_mem _ (q14_memℓp hγ j x) k

lemma q14_coord_sub {γ : ℝ} (a b : NegSobolev d γ) (k : NonzeroLattice d) :
    NegSobolev.coord (a - b) k = NegSobolev.coord a k - NegSobolev.coord b k := by
  unfold NegSobolev.coord
  rfl

lemma q14_norm_bVec_sq_le {γ : ℝ} (hγ : (d : ℝ) / 2 + 2 < γ) (j : Fin d) (x : Torus d) :
    ‖bVec γ j x‖ ^ 2 ≤ 2 * q14S d (γ - 1) := by
  obtain ⟨hs, hn⟩ := NegSobolev.coord_sq (bVec γ j x)
  rw [hn]
  have hs2 := summable_jp_rpow (d := d) (γ - 1) (by linarith)
  calc ∑' k, NegSobolev.coord (bVec γ j x) k ^ 2
      ≤ ∑' k : NonzeroLattice d, 2 * Lattice.jp k.1 ^ (-(2 * (γ - 1))) := by
        refine Summable.tsum_le_tsum (fun k => ?_) hs (hs2.mul_left 2)
        rw [q14_coord_bVec (by linarith) j x k]
        have := q14_term_bound γ 1 k (c := Torus.partialDeriv j (Torus.realMode k) x) (t := 1)
          (by simpa using q14_coef_bound j k x)
        simpa using this
    _ = 2 * q14S d (γ - 1) := by rw [tsum_mul_left]; rfl

lemma q14_norm_bVec_sub_sq_le {γ : ℝ} (hγ : (d : ℝ) / 2 + 2 < γ) (j : Fin d) (x y : Torus d) :
    ‖bVec γ j x - bVec γ j y‖ ^ 2 ≤ 2 * q14S d (γ - 2) * Torus.tdist x y ^ 2 := by
  obtain ⟨hs, hn⟩ := NegSobolev.coord_sq (bVec γ j x - bVec γ j y)
  rw [hn]
  have hs2 := summable_jp_rpow (d := d) (γ - 2) (by linarith)
  calc ∑' k, NegSobolev.coord (bVec γ j x - bVec γ j y) k ^ 2
      ≤ ∑' k : NonzeroLattice d,
          2 * Torus.tdist x y ^ 2 * Lattice.jp k.1 ^ (-(2 * (γ - 2))) := by
        refine Summable.tsum_le_tsum (fun k => ?_) hs (hs2.mul_left _)
        rw [q14_coord_sub, q14_coord_bVec (by linarith) j x k, q14_coord_bVec (by linarith) j y k,
          ← mul_sub]
        have := q14_term_bound γ 2 k
          (c := Torus.partialDeriv j (Torus.realMode k) x - Torus.partialDeriv j (Torus.realMode k) y)
          (t := Torus.tdist x y) (by simpa using q14_coef_lip j k x y)
        simpa using this
    _ = 2 * q14S d (γ - 2) * Torus.tdist x y ^ 2 := by
        rw [tsum_mul_left]; unfold q14S; ring

end BVecNorm

end HRS.Uniform.Q14

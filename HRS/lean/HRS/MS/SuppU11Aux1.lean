import HRS.Whole.Orbits

/-!
# U11 helper file 1: abstract Bessel inequality, the matrix operator `ℓ² → ℓ²`, continuity of the
diagonal semigroup (for the proof of `HRS.Whole.return_map_bounded`).

Everything here is independent of the analysis of the model.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

namespace HRS.Whole

/-- Bessel inequality for a symmetric positive semidefinite bilinear form and a `Q`-orthonormal
family. -/
lemma u11_bessel {V : Type*} [AddCommGroup V] [Module ℝ V] {ι : Type*} [DecidableEq ι]
    (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hsymm : ∀ x y, Q x y = Q y x) (hpos : ∀ x, 0 ≤ Q x x)
    (x : ι → V) (hx : ∀ i j, Q (x i) (x j) = if i = j then 1 else 0) (y : V) (S : Finset ι) :
    ∑ i ∈ S, Q y (x i) ^ 2 ≤ Q y y := by
  set s : V := ∑ i ∈ S, Q y (x i) • x i with hs
  have h := hpos (y - s)
  have hys : Q y s = ∑ i ∈ S, Q y (x i) ^ 2 := by
    simp only [hs, map_sum, map_smul, smul_eq_mul, sq]
  have hss : Q s s = ∑ i ∈ S, Q y (x i) ^ 2 := by
    simp only [hs, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hx]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp [mul_ite, Finset.sum_ite_eq, hi, sq]
  have h2 : Q (y - s) (y - s) = Q y y - Q y s - Q s y + Q s s := by
    simp only [map_sub, LinearMap.sub_apply]
    ring
  rw [h2, hsymm s y, hys, hss] at h
  linarith

/-- Cauchy-Schwarz for a sequence in `ℓ²` against a sequence with bounded partial square sums. -/
lemma u11_cs_tsum {a c : ℕ → ℝ} {A : ℝ} (hA : ∀ S : Finset ℕ, ∑ l ∈ S, a l ^ 2 ≤ A)
    (hC : Summable fun l => c l ^ 2) :
    Summable (fun l => a l * c l) ∧ (∑' l, a l * c l) ^ 2 ≤ A * ∑' l, c l ^ 2 := by
  have ha : Summable fun l => a l ^ 2 := summable_of_sum_le (fun l => sq_nonneg _) hA
  have hprod : Summable fun l => a l * c l := by
    refine Summable.of_norm_bounded (g := fun l => (a l ^ 2 + c l ^ 2) / 2)
      ((ha.add hC).div_const 2) (fun l => ?_)
    rw [Real.norm_eq_abs]
    exact abs_le.2 ⟨by nlinarith [sq_nonneg (a l + c l)], by nlinarith [sq_nonneg (a l - c l)]⟩
  refine ⟨hprod, ?_⟩
  have hA0 : 0 ≤ A := by simpa using hA ∅
  have hpart : ∀ S : Finset ℕ, (∑ l ∈ S, a l * c l) ^ 2 ≤ A * ∑' l, c l ^ 2 := by
    intro S
    calc (∑ l ∈ S, a l * c l) ^ 2 ≤ (∑ l ∈ S, a l ^ 2) * ∑ l ∈ S, c l ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq S a c
      _ ≤ A * ∑' l, c l ^ 2 :=
          mul_le_mul (hA S) (hC.sum_le_tsum S (fun _ _ => sq_nonneg _))
            (Finset.sum_nonneg fun _ _ => sq_nonneg _) hA0
  have ht : Tendsto (fun S : Finset ℕ => (∑ l ∈ S, a l * c l) ^ 2) atTop
      (𝓝 ((∑' l, a l * c l) ^ 2)) :=
    ((continuous_pow 2).tendsto _).comp hprod.hasSum
  exact le_of_tendsto' ht hpart

/-- The matrix bound: rows with Bessel-bounded squares and summable bounds. -/
lemma u11_matrix_bound {ι : Type*} (a : ι → ℕ → ℝ) (B : ι → ℝ) (hB : Summable B)
    (_hB0 : ∀ i, 0 ≤ B i) (hbes : ∀ i (S : Finset ℕ), ∑ l ∈ S, a i l ^ 2 ≤ B i)
    (c : ℕ → ℝ) (hc : Summable fun l => c l ^ 2) :
    (∀ i, Summable fun l => a i l * c l) ∧ Summable (fun i => (∑' l, a i l * c l) ^ 2) ∧
      ∑' i, (∑' l, a i l * c l) ^ 2 ≤ (∑' i, B i) * ∑' l, c l ^ 2 := by
  have h := fun i => u11_cs_tsum (hbes i) hc
  have hC0 : 0 ≤ ∑' l, c l ^ 2 := tsum_nonneg fun _ => sq_nonneg _
  have hs : Summable (fun i => (∑' l, a i l * c l) ^ 2) :=
    Summable.of_nonneg_of_le (fun i => sq_nonneg _) (fun i => (h i).2) (hB.mul_right _)
  refine ⟨fun i => (h i).1, hs, ?_⟩
  calc ∑' i, (∑' l, a i l * c l) ^ 2 ≤ ∑' i, B i * ∑' l, c l ^ 2 :=
        hs.tsum_le_tsum (fun i => (h i).2) (hB.mul_right _)
    _ = (∑' i, B i) * ∑' l, c l ^ 2 := tsum_mul_right

lemma u11_coord_summable (z : SeqL2) : Summable fun l => SeqL2.coord z l ^ 2 :=
  memℓp_two_iff.1 (lp.memℓp (show lp (fun _ : ℕ => ℝ) 2 from z))

lemma u11_norm_sq (z : SeqL2) : ∑' l, SeqL2.coord z l ^ 2 = ‖z‖ ^ 2 := by
  have h := lp_two_norm_eq (show lp (fun _ : ℕ => ℝ) 2 from z)
  have h2 : ‖z‖ = Real.sqrt (∑' l, SeqL2.coord z l ^ 2) := h
  rw [h2, Real.sq_sqrt (tsum_nonneg fun _ => sq_nonneg _)]

lemma u11_coord_sub (z z' : SeqL2) (l : ℕ) :
    SeqL2.coord (z - z') l = SeqL2.coord z l - SeqL2.coord z' l := rfl

lemma u11_coord_ofSeq {c : ℕ → ℝ} (hc : Memℓp c 2) (l : ℕ) :
    SeqL2.coord (SeqL2.ofSeq c) l = c l := by
  have hv : SeqL2.ofSeq c = (⟨c, hc⟩ : lp (fun _ : ℕ => ℝ) 2) := by
    unfold SeqL2.ofSeq; exact dif_pos hc
  rw [hv]
  rfl

/-- The norm of `ellVec`. -/
lemma u11_norm_ellVec_le {d : ℕ} (m : ℝ) (x : MultiIndex d → ℝ) (hx : Memℓp x 2) {K : ℝ}
    (hK : 0 ≤ K) (h : ∑' α, x α ^ 2 ≤ K ^ 2) : ‖ellVec m x‖ ≤ K := by
  have hv : ellVec m x = (⟨x, hx⟩ : lp (fun _ : MultiIndex d => ℝ) 2) := dif_pos hx
  rw [hv]
  have := lp_two_norm_eq (⟨x, hx⟩ : lp (fun _ : MultiIndex d => ℝ) 2)
  have h3 : ‖(⟨x, hx⟩ : lp (fun _ : MultiIndex d => ℝ) 2)‖ = Real.sqrt (∑' α, x α ^ 2) := this
  show ‖(⟨x, hx⟩ : lp (fun _ : MultiIndex d => ℝ) 2)‖ ≤ K
  rw [h3]
  exact Real.sqrt_le_iff.2 ⟨hK, h⟩

lemma u11_ellVec_sub {d : ℕ} (m : ℝ) {x x' : MultiIndex d → ℝ} (hx : Memℓp x 2)
    (hx' : Memℓp x' 2) :
    ellVec m x - ellVec m x' = ellVec m (fun α => x α - x' α) := by
  have h3 : Memℓp (fun α => x α - x' α) 2 := hx.sub hx'
  have hv1 : ellVec m x = (⟨x, hx⟩ : lp (fun _ : MultiIndex d => ℝ) 2) := dif_pos hx
  have hv2 : ellVec m x' = (⟨x', hx'⟩ : lp (fun _ : MultiIndex d => ℝ) 2) := dif_pos hx'
  have hv3 : ellVec m (fun α => x α - x' α) =
      (⟨fun α => x α - x' α, h3⟩ : lp (fun _ : MultiIndex d => ℝ) 2) := dif_pos h3
  rw [hv1, hv2, hv3]
  rfl

/-- The coefficient operator `c ↦ (∑_l a_{αl} c_l)_α` into `OscDual`. -/
def u11Theta {d : ℕ} (a : MultiIndex d → ℕ → ℝ) (m : ℝ) (z : SeqL2) : OscDual d m :=
  ellVec m fun α => ∑' l, a α l * SeqL2.coord z l

lemma u11_theta_norm_le {d : ℕ} (a : MultiIndex d → ℕ → ℝ) (B : MultiIndex d → ℝ)
    (hB : Summable B) (hB0 : ∀ i, 0 ≤ B i) (hbes : ∀ i (S : Finset ℕ), ∑ l ∈ S, a i l ^ 2 ≤ B i)
    (m : ℝ) (z : SeqL2) : ‖u11Theta a m z‖ ≤ Real.sqrt (∑' α, B α) * ‖z‖ := by
  obtain ⟨_, hs, hle⟩ := u11_matrix_bound a B hB hB0 hbes (SeqL2.coord z) (u11_coord_summable z)
  refine u11_norm_ellVec_le m _ (memℓp_two_iff.2 hs) (mul_nonneg (Real.sqrt_nonneg _)
    (norm_nonneg _)) ?_
  rw [mul_pow, Real.sq_sqrt (tsum_nonneg hB0)]
  rw [u11_norm_sq] at hle
  exact hle

lemma u11_theta_lip {d : ℕ} (a : MultiIndex d → ℕ → ℝ) (B : MultiIndex d → ℝ)
    (hB : Summable B) (hB0 : ∀ i, 0 ≤ B i) (hbes : ∀ i (S : Finset ℕ), ∑ l ∈ S, a i l ^ 2 ≤ B i)
    (m : ℝ) (z z' : SeqL2) :
    ‖u11Theta a m z - u11Theta a m z'‖ ≤ Real.sqrt (∑' α, B α) * ‖z - z'‖ := by
  obtain ⟨h1, hs1, _⟩ := u11_matrix_bound a B hB hB0 hbes (SeqL2.coord z) (u11_coord_summable z)
  obtain ⟨h2, hs2, _⟩ := u11_matrix_bound a B hB hB0 hbes (SeqL2.coord z') (u11_coord_summable z')
  obtain ⟨h3, hs3, hle⟩ := u11_matrix_bound a B hB hB0 hbes (SeqL2.coord (z - z'))
    (u11_coord_summable (z - z'))
  unfold u11Theta
  rw [u11_ellVec_sub m (memℓp_two_iff.2 hs1) (memℓp_two_iff.2 hs2)]
  have hfun : (fun α => (∑' l, a α l * SeqL2.coord z l) - ∑' l, a α l * SeqL2.coord z' l) =
      fun α => ∑' l, a α l * SeqL2.coord (z - z') l := by
    funext α
    rw [← (h1 α).tsum_sub (h2 α)]
    refine tsum_congr fun l => ?_
    rw [u11_coord_sub]
    ring
  rw [hfun]
  refine u11_norm_ellVec_le m _ (memℓp_two_iff.2 hs3) (mul_nonneg (Real.sqrt_nonneg _)
    (norm_nonneg _)) ?_
  rw [mul_pow, Real.sq_sqrt (tsum_nonneg hB0)]
  rw [u11_norm_sq] at hle
  exact hle

/-- The diagonal semigroup `e^{-s ω_ℓ}` on `ℓ²` (a copy of `semiDiag`). -/
def u11Diag (om : ℕ → ℝ) (s : ℝ) (z : SeqL2) : SeqL2 :=
  SeqL2.ofSeq fun l => Real.exp (-s * om l) * SeqL2.coord z l

lemma u11_diag_memℓp (om : ℕ → ℝ) (hom : ∀ l, 0 < om l) {s : ℝ} (hs : 0 ≤ s) (z : SeqL2) :
    Memℓp (fun l => Real.exp (-s * om l) * SeqL2.coord z l) 2 := by
  refine memℓp_two_iff.2 ?_
  refine Summable.of_nonneg_of_le (fun l => sq_nonneg _) (fun l => ?_) (u11_coord_summable z)
  have h1 : Real.exp (-s * om l) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [hom l]
  have h0 : 0 < Real.exp (-s * om l) := Real.exp_pos _
  rw [mul_pow]
  nlinarith [sq_nonneg (SeqL2.coord z l), mul_nonneg (sq_nonneg (SeqL2.coord z l)) h0.le,
    pow_le_one₀ (n := 2) h0.le h1]

lemma u11_diag_continuousOn (om : ℕ → ℝ) (hom : ∀ l, 0 < om l) (z : SeqL2) :
    ContinuousOn (fun s : ℝ => u11Diag om s z) (Set.Ici 0) := by
  intro s0 hs0
  have hs0' : (0 : ℝ) ≤ s0 := hs0
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have hsq : ∀ s ∈ Set.Ici (0 : ℝ), ‖u11Diag om s z - u11Diag om s0 z‖ =
      Real.sqrt (∑' l, ((Real.exp (-s * om l) - Real.exp (-s0 * om l)) *
        SeqL2.coord z l) ^ 2) := by
    intro s hs
    have hs' : (0 : ℝ) ≤ s := hs
    have h := lp_two_norm_eq (show lp (fun _ : ℕ => ℝ) 2 from (u11Diag om s z - u11Diag om s0 z))
    have h2 : ‖u11Diag om s z - u11Diag om s0 z‖ = Real.sqrt (∑' l,
        SeqL2.coord (u11Diag om s z - u11Diag om s0 z) l ^ 2) := h
    rw [h2]
    congr 1
    refine tsum_congr fun l => ?_
    rw [u11_coord_sub]
    unfold u11Diag
    rw [u11_coord_ofSeq (u11_diag_memℓp om hom hs' z), u11_coord_ofSeq (u11_diag_memℓp om hom hs0' z)]
    ring
  have hlim : Tendsto (fun s : ℝ => ∑' l, ((Real.exp (-s * om l) - Real.exp (-s0 * om l)) *
      SeqL2.coord z l) ^ 2) (𝓝[Set.Ici 0] s0) (𝓝 0) := by
    have hab : ∀ l : ℕ, Tendsto (fun s : ℝ => ((Real.exp (-s * om l) - Real.exp (-s0 * om l)) *
        SeqL2.coord z l) ^ 2) (𝓝[Set.Ici (0 : ℝ)] s0) (𝓝 0) := by
      intro l
      have hc : Continuous fun s : ℝ => ((Real.exp (-s * om l) - Real.exp (-s0 * om l)) *
          SeqL2.coord z l) ^ 2 := by fun_prop
      have := (hc.tendsto s0).mono_left (nhdsWithin_le_nhds (s := Set.Ici (0 : ℝ)))
      simpa using this
    have hbd : ∀ᶠ s in 𝓝[Set.Ici (0 : ℝ)] s0, ∀ l : ℕ,
        ‖((Real.exp (-s * om l) - Real.exp (-s0 * om l)) * SeqL2.coord z l) ^ 2‖ ≤
          SeqL2.coord z l ^ 2 := by
      filter_upwards [self_mem_nhdsWithin] with s hs l
      have hs' : (0 : ℝ) ≤ s := hs
      have e1 : Real.exp (-s * om l) ≤ 1 := by
        rw [Real.exp_le_one_iff]; nlinarith [hom l]
      have e2 : Real.exp (-s0 * om l) ≤ 1 := by
        rw [Real.exp_le_one_iff]; nlinarith [hom l]
      have e3 := Real.exp_pos (-s * om l)
      have e4 := Real.exp_pos (-s0 * om l)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow]
      have : (Real.exp (-s * om l) - Real.exp (-s0 * om l)) ^ 2 ≤ 1 := by
        nlinarith
      nlinarith [sq_nonneg (SeqL2.coord z l)]
    have := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[Set.Ici (0 : ℝ)] s0)
      (f := fun (s : ℝ) (l : ℕ) => ((Real.exp (-s * om l) - Real.exp (-s0 * om l)) *
        SeqL2.coord z l) ^ 2) (g := fun _ => (0 : ℝ))
      (bound := fun l => SeqL2.coord z l ^ 2) (u11_coord_summable z) hab hbd
    simpa using this
  have hlim2 := (Real.continuous_sqrt.tendsto 0).comp hlim
  rw [Real.sqrt_zero] at hlim2
  refine hlim2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (hsq s hs).symm

end HRS.Whole

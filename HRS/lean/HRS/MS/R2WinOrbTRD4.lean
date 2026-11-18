import HRS.MS.R2WinOrbTRD3

/-!
# S10.3 packet [C], part 4: the generator on functions with decaying derivatives, and `L_0` of a datum

Prefix `s103c_`, namespace `HRS.MS.R2WinOrbNL`.

* `s103c_gen_bd_dec`: if `e ∈ C^{N+2}` has derivatives of order `1..N+2` bounded by `G` and of order `1..N+1` decaying like `A (1+‖x‖)⁻¹`, then
  `L_τ e ∈ Bd N (K (A + (1+Ah) G))` (the last step of `s103b_gen_bd`, with the weighted decay as a hypothesis).
* `DatD.dir_syn`, `s103c_L0_sy`: for a datum `ψ ∈ DatD (N+2)`, the partial derivatives lie in `SyN 2 N` and `L_0 ψ ∈ Sy N`.
* `s103c_L0_sub`: linearity of `L_0`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.R2WinOrbNL

open HRS HRS.Whole HRS.MS.Wad HRS.MS.Ul HRS.MS.Who HRS.MS.BreakdownS67 HRS.MS.MovLin

variable {d : ℕ}

theorem s103c_gen_bd_dec {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (a β : ℝ) (ha : 0 < a)
    (N : ℕ) {L : ℝ} (hL : (d : ℝ) + N + s + 3 < L) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ρ : ℝ → Euc d → ℝ) (Ah : ℝ) (τ : ℝ), 0 ≤ Ah → U2Dec (N + 1) L Ah (ρ τ) →
      ∀ (e : Euc d → ℝ) (A G : ℝ), ContDiff ℝ ((N + 2 : ℕ) : WithTop ℕ∞) e →
        (∀ i, 1 ≤ i → i ≤ N + 1 → ∀ y, ‖iteratedFDeriv ℝ i e y‖ ≤ A * (1 + ‖y‖)⁻¹) →
        (∀ i, 1 ≤ i → i ≤ N + 2 → ∀ y, ‖iteratedFDeriv ℝ i e y‖ ≤ G) →
        Bd N (K * (A + (1 + Ah) * G)) (generatorW ((quadraticGradientDyn d s a β).coeff ρ) τ e) := by
  obtain ⟨Cq, hCq0, hCq⟩ := s103b_q_sy hd hs0 hsd N hL
  refine ⟨d * |β⁻¹| + d * (|a| * ((N + 1 : ℝ))) + Cq, by positivity, ?_⟩
  intro ρ Ah τ hAh hU e A G hec hdec hbd
  have hAφ : 0 ≤ A := by
    have := hdec 1 le_rfl (by omega) 0
    simpa using (norm_nonneg _).trans this
  have hG : 0 ≤ G := by
    have := hbd 1 le_rfl (by omega) 0
    exact (norm_nonneg _).trans this
  have hDg : ∀ i : Fin d, Sy N A (fun y => fderiv ℝ e y (EuclideanSpace.single i (1 : ℝ))) := fun i =>
    s103b_deriv_sy (hec.of_le (by exact_mod_cast (by omega : N + 1 ≤ N + 2))) (fun j hj1 hj2 x => hdec j hj1 hj2 x) i
  have hDg' : ∀ i : Fin d, Bd N ((N + 1) * A) (fun x => x i * fderiv ℝ e x (EuclideanSpace.single i (1 : ℝ))) :=
    fun i => by
      have := (hDg i).xmul i
      simpa using this
  have T1 : Bd N (|β⁻¹| * (d * G)) (fun x => β⁻¹ * Laplacian.laplacian e x) :=
    (s103b_lap_bd hec hbd).smul β⁻¹
  have T2 : Bd N (∑ i : Fin d, |(-a)| * ((N + 1) * A))
      (fun x => ∑ i : Fin d, (-a) * (x i * fderiv ℝ e x (EuclideanSpace.single i (1 : ℝ)))) :=
    Bd.sum Finset.univ _ _ (fun i _ => (hDg' i).smul (-a))
  have T3 : Bd N (Cq * Ah * G) (s103bQ d s (ρ τ) e) :=
    (hCq Ah (ρ τ) hAh hU G e hec hbd).bd
  have hsum := (T1.add T2).add T3
  have hfun : generatorW ((quadraticGradientDyn d s a β).coeff ρ) τ e = fun x =>
      (β⁻¹ * Laplacian.laplacian e x + ∑ i : Fin d, (-a) * (x i * fderiv ℝ e x
        (EuclideanSpace.single i (1 : ℝ)))) + s103bQ d s (ρ τ) e x := by
    funext x
    rw [s103b_gen_split, s103b_L0_eq]
    simp only [Finset.sum_neg_distrib, neg_mul, sub_eq_add_neg]
  rw [hfun]
  refine hsum.mono_A ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, abs_neg, abs_of_pos ha]
  have h1 : 0 ≤ Ah * G := mul_nonneg hAh hG
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hβ0 : 0 ≤ |β⁻¹| := abs_nonneg _
  have hN1 : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
  nlinarith [mul_nonneg hd0 hβ0, mul_nonneg (mul_nonneg hd0 hβ0) hG, mul_nonneg (mul_nonneg hd0 hβ0) hAφ,
    mul_nonneg (mul_nonneg hd0 hβ0) h1, mul_nonneg hCq0 hAφ, mul_nonneg hCq0 hG, mul_nonneg hCq0 h1,
    mul_nonneg (mul_nonneg hd0 (mul_nonneg ha.le hN1)) hAφ,
    mul_nonneg (mul_nonneg hd0 (mul_nonneg ha.le hN1)) hG,
    mul_nonneg (mul_nonneg hd0 (mul_nonneg ha.le hN1)) h1]

theorem s103c_L0_sub (a β : ℝ) {g1 g2 : Euc d → ℝ} (hg1 : ContDiff ℝ 2 g1) (hg2 : ContDiff ℝ 2 g2) (x : Euc d) :
    s83_L0 a β⁻¹ (fun y => g1 y - g2 y) x = s83_L0 a β⁻¹ g1 x - s83_L0 a β⁻¹ g2 x := by
  rw [s103b_L0_eq, s103b_L0_eq, s103b_L0_eq]
  have hlap : Laplacian.laplacian (fun y => g1 y - g2 y) x =
      Laplacian.laplacian g1 x - Laplacian.laplacian g2 x :=
    (hg1.contDiffAt (x := x)).laplacian_sub (hg2.contDiffAt (x := x))
  have hfd : ∀ i : Fin d, fderiv ℝ (fun y => g1 y - g2 y) x (EuclideanSpace.single i (1 : ℝ)) =
        fderiv ℝ g1 x (EuclideanSpace.single i (1 : ℝ)) - fderiv ℝ g2 x (EuclideanSpace.single i (1 : ℝ)) := by
    intro i
    rw [fderiv_fun_sub ((hg1.differentiable (by norm_num)) x) ((hg2.differentiable (by norm_num)) x)]
    rfl
  rw [hlap]
  simp only [hfd, mul_sub, Finset.sum_sub_distrib]
  ring

theorem DatD.dir_syn {N : ℕ} {A : ℝ} {ψ : Euc d → ℝ} (h : DatD (N + 1) A ψ) (i : Fin d) :
    SyN 2 N A (fun y => fderiv ℝ ψ y (EuclideanSpace.single i (1 : ℝ))) := by
  have hd1 : ContDiff ℝ (N : WithTop ℕ∞) (fderiv ℝ ψ) :=
    h.1.fderiv_right (by exact_mod_cast le_refl (N + 1))
  have hvn : ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖ = 1 := by simp
  refine ⟨hd1.clm_apply contDiff_const, fun j hj x => ?_⟩
  have h1 := norm_iteratedFDeriv_clm_apply_const (N := (N : WithTop ℕ∞)) (c := (EuclideanSpace.single i (1 : ℝ) : Euc d))
    (n := j) hd1.contDiffAt (by exact_mod_cast hj) (x := x)
  rw [norm_iteratedFDeriv_fderiv, hvn, one_mul] at h1
  have h2 := h.2.2 (j + 1) (by omega) (by omega) x
  exact (mul_le_mul_of_nonneg_right h1 (by positivity)).trans h2

theorem s103c_L0_sy {N : ℕ} {A : ℝ} {ψ : Euc d → ℝ} (a β : ℝ) (h : DatD (N + 2) A ψ) :
    Sy N ((|β⁻¹| * d + d * (|a| * ((N : ℝ) + 1))) * A) (s83_L0 a β⁻¹ ψ) := by
  have hA := h.nonneg
  have hn : ∀ i : Fin d, ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖ = 1 := fun i => by simp
  have hd1 : ContDiff ℝ ((N + 1 : ℕ) : WithTop ℕ∞) (fderiv ℝ ψ) :=
    h.1.fderiv_right (by exact_mod_cast le_refl (N + 2))
  -- the second derivatives `∂_i ∂_i ψ`
  have hDD : ∀ i : Fin d, Sy N A (fun y => fderiv ℝ (fun y => fderiv ℝ ψ y (EuclideanSpace.single i (1 : ℝ))) y
      (EuclideanSpace.single i (1 : ℝ))) := by
    intro i
    refine s103b_deriv_sy (N := N) (hd1.clm_apply contDiff_const) (fun m hm1 hm2 y => ?_) i
    have h1 := norm_iteratedFDeriv_clm_apply_const (N := ((N + 1 : ℕ) : WithTop ℕ∞))
      (c := (EuclideanSpace.single i (1 : ℝ) : Euc d)) (n := m) hd1.contDiffAt (by exact_mod_cast hm2) (x := y)
    rw [norm_iteratedFDeriv_fderiv, hn i, one_mul] at h1
    exact h1.trans (h.decay1 (m + 1) (by omega) (by omega) y)
  have hlapfun : ∀ x, Laplacian.laplacian ψ x = ∑ i : Fin d,
      fderiv ℝ (fun y => fderiv ℝ ψ y (EuclideanSpace.single i (1 : ℝ))) x (EuclideanSpace.single i (1 : ℝ)) :=
    fun x => s103n_lap_eq (h.1.of_le (by exact_mod_cast Nat.le_add_left 2 N)) x
  have T1 : Sy N (|β⁻¹| * (∑ i : Fin d, A)) (fun x => β⁻¹ * Laplacian.laplacian ψ x) := by
    simp only [hlapfun]
    exact (s103b_Sy_sum Finset.univ _ _ (fun i _ => hDD i)).smul β⁻¹
  have T2 : Sy N (∑ i : Fin d, |(-a)| * (((N : ℝ) + 1) * A))
      (fun x => ∑ i : Fin d, (-a) * (x i * fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ)))) :=
    s103b_Sy_sum Finset.univ _ _ (fun i _ =>
      ((((h.mono_N (by omega : N + 1 ≤ N + 2)).dir_syn i).xmul i).toSy).smul (-a))
  have hfun : s83_L0 a β⁻¹ ψ = fun x => β⁻¹ * Laplacian.laplacian ψ x +
      ∑ i : Fin d, (-a) * (x i * fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ))) := by
    funext x
    rw [s103b_L0_eq]
    simp only [Finset.sum_neg_distrib, neg_mul, sub_eq_add_neg]
  rw [hfun]
  refine (T1.add T2).mono_A ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, abs_neg]
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  nlinarith [mul_nonneg hd0 (abs_nonneg β⁻¹), mul_nonneg (mul_nonneg hd0 (abs_nonneg β⁻¹)) hA]

end HRS.MS.R2WinOrbNL

end

import HRS.MS.R2WinOrbTRB4

/-!
# S10.3 packet [B], part 5: the generator of the nonlocal time-dependent adjoint solution has bounded jets (the form consumed by [C])

Prefix `s103b_`, namespace `HRS.MS.R2WinOrbNL`.

`s103b_gen_bd`: under the hypotheses of `s103b_weighted_decay` (one order higher), for every slice `τ ∈ [0,t]` the function
`L_τ f_τ = β⁻¹Δf_τ - a x·∇f_τ + q_τ` has bounded jets up to order `N` (`Bd N`), with bound `K (Aφ + (1+Ah) G)`.  The only term that needs the weighted
estimate is the drift `-a x·∇f_τ` (`∂_i f_τ ∈ Sy N`, `Sy.xmul`); the terminal layer `D_h = f^{t+h}(t) - φ = ∫_t^{t+h} L_σ f^{t+h}(σ) dσ` of [C] is
therefore `O(h)` in `Bd N` as soon as the `σ`-integral may be differentiated under the jets.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.R2WinOrbNL

open HRS HRS.Whole HRS.MS.Wad HRS.MS.Ul

variable {d : ℕ}

theorem s103b_deriv_sy {N : ℕ} {A : ℝ} {g : Euc d → ℝ} (hg : ContDiff ℝ ((N + 1 : ℕ) : WithTop ℕ∞) g)
    (hb : ∀ i, 1 ≤ i → i ≤ N + 1 → ∀ x, ‖iteratedFDeriv ℝ i g x‖ ≤ A * (1 + ‖x‖)⁻¹) (i : Fin d) :
    Sy N A (fun y => fderiv ℝ g y (EuclideanSpace.single i (1 : ℝ))) := by
  have hd1 : ContDiff ℝ (N : WithTop ℕ∞) (fderiv ℝ g) :=
    hg.fderiv_right (by exact_mod_cast le_refl (N + 1))
  have hn : ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖ = 1 := by simp
  refine ⟨hd1.clm_apply contDiff_const, fun m hm y => ?_⟩
  refine (norm_iteratedFDeriv_clm_apply_const (N := (N : WithTop ℕ∞)) (c := EuclideanSpace.single i (1 : ℝ))
    (n := m) hd1.contDiffAt (by exact_mod_cast hm)).trans ?_
  rw [norm_iteratedFDeriv_fderiv, hn, one_mul]
  exact hb (m + 1) (by omega) (by omega) y

theorem s103b_lap_bd {N : ℕ} {G : ℝ} {g : Euc d → ℝ} (hg : ContDiff ℝ ((N + 2 : ℕ) : WithTop ℕ∞) g)
    (hb : ∀ i, 1 ≤ i → i ≤ N + 2 → ∀ x, ‖iteratedFDeriv ℝ i g x‖ ≤ G) :
    Bd N (d * G) (fun x => Laplacian.laplacian g x) := by
  have hn : ∀ i : Fin d, ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖ = 1 := fun i => by simp
  have hfun : (fun x => Laplacian.laplacian g x) = fun x => ∑ i : Fin d,
      fderiv ℝ (fun y => fderiv ℝ g y (EuclideanSpace.single i (1 : ℝ))) x
        (EuclideanSpace.single i (1 : ℝ)) :=
    funext fun x => s103n_lap_eq (hg.of_le (by exact_mod_cast Nat.le_add_left 2 N)) x
  rw [hfun]
  have := Bd.sum (N := N) Finset.univ (fun i x => fderiv ℝ (fun y => fderiv ℝ g y
    (EuclideanSpace.single i (1 : ℝ))) x (EuclideanSpace.single i (1 : ℝ))) (fun _ => G) (fun i _ => by
      have h1 := (s103b_deriv_bd hg hb i).deriv (EuclideanSpace.single i (1 : ℝ))
      rw [hn i, mul_one] at h1
      exact h1)
  simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using this

theorem s103b_L0_eq (a β : ℝ) (g : Euc d → ℝ) (x : Euc d) :
    HRS.MS.Wad.s83_L0 a β⁻¹ g x = β⁻¹ * Laplacian.laplacian g x -
      ∑ i : Fin d, a * (x i * fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ))) := by
  unfold HRS.MS.Wad.s83_L0
  rw [← HRS.MS.Wad.s83_lap_eq]
  have e : fderiv ℝ g x x = inner ℝ (gradient g x) x := (HRS.MS.Wad.s83_inner_gradient g x x).symm
  rw [e, HRS.MS.BreakdownS67.s67bd26_inner, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [HRS.MS.MovLin.mov2d_grad_coord]; ring

theorem s103b_gen_bd {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (a β : ℝ) (ha : 0 < a)
    (hβ : 0 < β) (N : ℕ) {L : ℝ} (hL : (d : ℝ) + ((N + 1 : ℕ) : ℝ) + s + 3 < L) (T : ℝ) (hT : 0 ≤ T) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ρ : ℝ → Euc d → ℝ) (Ah : ℝ), 0 ≤ Ah →
      (∀ τ ∈ Set.Icc (0 : ℝ) T, U2Dec (N + 1 + 1) L Ah (ρ τ)) →
      ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ (φ : Euc d → ℝ) (f : ℝ → Euc d → ℝ) (Aφ G : ℝ),
        IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff ρ) t φ f →
        ContDiff ℝ ((N + 1 : ℕ) : WithTop ℕ∞) φ →
        (∀ i, 1 ≤ i → i ≤ N + 1 → ∀ y, ‖iteratedFDeriv ℝ i φ y‖ ≤ Aφ * (1 + ‖y‖)⁻¹) →
        (∀ τ ∈ Set.Icc (0 : ℝ) t, ContDiff ℝ ((N + 1 + 2 : ℕ) : WithTop ℕ∞) (f τ) ∧
          ∀ i, 1 ≤ i → i ≤ N + 1 + 2 → ∀ y, ‖iteratedFDeriv ℝ i (f τ) y‖ ≤ G) →
        ∀ τ ∈ Set.Icc (0 : ℝ) t,
          Bd N (K * (Aφ + (1 + Ah) * G)) (generatorW ((quadraticGradientDyn d s a β).coeff ρ) τ (f τ)) := by
  obtain ⟨K1, hK10, hK1⟩ := s103b_weighted_decay hd hs0 hsd a β ha hβ (N + 1) hL T hT
  have hL' : (d : ℝ) + N + s + 3 < L := by push_cast at hL; linarith
  obtain ⟨Cq, hCq0, hCq⟩ := s103b_q_sy hd hs0 hsd N hL'
  refine ⟨d * |β⁻¹| + d * (|a| * ((N + 1 : ℝ) * K1)) + Cq, by positivity, ?_⟩
  intro ρ Ah hAh hU t ht φ f Aφ G hf hφc hφb hfb τ hτ
  have ht0 : 0 ≤ t := ht.1
  have hAφ : 0 ≤ Aφ := by
    have := hφb 1 le_rfl (by omega) 0
    simpa using (norm_nonneg _).trans this
  have hG : 0 ≤ G := by
    have := (hfb τ hτ).2 1 le_rfl (by omega) 0
    exact (norm_nonneg _).trans this
  have hτT : τ ∈ Set.Icc (0 : ℝ) T := ⟨hτ.1, hτ.2.trans ht.2⟩
  -- the weighted decay of the derivatives of `f`
  have hw := hK1 ρ Ah hAh hU t ht φ f Aφ G hf hφc hφb hfb
  -- the gradient components
  set A1 : ℝ := K1 * (Aφ + Ah * G) with hA1
  have hDg : ∀ i : Fin d, Sy N A1 (fun y => fderiv ℝ (f τ) y (EuclideanSpace.single i (1 : ℝ))) := fun i =>
    s103b_deriv_sy ((hfb τ hτ).1.of_le (by exact_mod_cast (by omega : N + 1 ≤ N + 1 + 2)))
      (fun j hj1 hj2 x => hw τ hτ j hj1 (by omega) x) i
  have hDg' : ∀ i : Fin d, Bd N ((N + 1) * A1) (fun x => x i * fderiv ℝ (f τ) x (EuclideanSpace.single i (1 : ℝ))) :=
    fun i => by
      have := (hDg i).xmul i
      simpa using this
  have T1 : Bd N (|β⁻¹| * (d * G)) (fun x => β⁻¹ * Laplacian.laplacian (f τ) x) :=
    (s103b_lap_bd ((hfb τ hτ).1.of_le (by exact_mod_cast (by omega : N + 2 ≤ N + 1 + 2)))
      (fun i h1 h2 x => (hfb τ hτ).2 i h1 (by omega) x)).smul β⁻¹
  have T2 : Bd N (∑ i : Fin d, |(-a)| * ((N + 1) * A1))
      (fun x => ∑ i : Fin d, (-a) * (x i * fderiv ℝ (f τ) x (EuclideanSpace.single i (1 : ℝ)))) :=
    Bd.sum Finset.univ _ _ (fun i _ => (hDg' i).smul (-a))
  have hU1 : U2Dec (N + 1) L Ah (ρ τ) := ult_U2Dec_mono (hU τ hτT) (by omega)
  have T3 : Bd N (Cq * Ah * G) (s103bQ d s (ρ τ) (f τ)) :=
    (hCq Ah (ρ τ) hAh hU1 G (f τ)
      ((hfb τ hτ).1.of_le (by exact_mod_cast (by omega : N + 2 ≤ N + 1 + 2)))
      (fun i h1 h2 x => (hfb τ hτ).2 i h1 (by omega) x)).bd
  have hsum := (T1.add T2).add T3
  have hfun : generatorW ((quadraticGradientDyn d s a β).coeff ρ) τ (f τ) = fun x =>
      (β⁻¹ * Laplacian.laplacian (f τ) x + ∑ i : Fin d, (-a) * (x i * fderiv ℝ (f τ) x
        (EuclideanSpace.single i (1 : ℝ)))) + s103bQ d s (ρ τ) (f τ) x := by
    funext x
    rw [s103b_gen_split, s103b_L0_eq]
    simp only [Finset.sum_neg_distrib, neg_mul, sub_eq_add_neg]
  rw [hfun]
  refine hsum.mono_A ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, abs_neg, abs_of_pos ha]
  rw [hA1]
  have h1 : 0 ≤ Ah * G := mul_nonneg hAh hG
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hβ0 : 0 ≤ |β⁻¹| := abs_nonneg _
  have hN1 : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
  nlinarith [mul_nonneg hd0 hβ0, mul_nonneg (mul_nonneg hd0 hβ0) hG, mul_nonneg (mul_nonneg hd0 hβ0) hAφ,
    mul_nonneg (mul_nonneg hd0 hβ0) h1, mul_nonneg hCq0 hAφ, mul_nonneg hCq0 hG, mul_nonneg hCq0 h1,
    mul_nonneg (mul_nonneg hd0 (mul_nonneg ha.le (mul_nonneg hN1 hK10))) hAφ,
    mul_nonneg (mul_nonneg hd0 (mul_nonneg ha.le (mul_nonneg hN1 hK10))) hG,
    mul_nonneg (mul_nonneg hd0 (mul_nonneg ha.le (mul_nonneg hN1 hK10))) h1]

end HRS.MS.R2WinOrbNL

end

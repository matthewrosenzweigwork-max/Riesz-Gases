import HRS.MS.R2WinOrbNLAux15

/-!
# S10.3 (nonlinear branch), part 16: the right time derivative `∂_t L_t φ` and its bound

Prefix `s103n_`, namespace `HRS.MS.R2WinOrbNL`.

* `s103nQ`: `Q_t φ = ∑_j ∇g*(ρ'_t ∂_jφ)_j - ∑_i (∇g*ρ'_t)_i ∂_iφ`, the derivative of the generator along the trajectory.
* `s103n_gen_hasDeriv`: `τ ↦ L_τφ(x)` has the right derivative `Q_tφ(x)` at `t ≥ 0` (`s103n_ultK_hasDeriv` for the coefficient `w = 1` and `w = ∂_jφ`); hence
  `derivWithin (fun t' => generatorW Cf t' φ x) (Set.Ici t) t = Q_tφ(x)` (`s103n_derivWithin_gen`).
* `s103n_Q_bd`: `Q_tφ ∈ Bd N (C A_d B)` if `ρ'_t ∈ U2Dec (N+1)` and `∂_iφ ∈ Bd (N+1) B`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.R2WinOrbNL

open HRS HRS.Whole HRS.MS.Ul HRS.MS.MovLin HRS.MS.MovOsc HRS.MS.Mov63 HRS.MS.Who HRS.MS.BreakdownS67
  HRS.MS.MovAdj

variable {d : ℕ}

/-- `Q_tφ(x) = ∑_j (∇g*(ρ' ∂_jφ))_j(x) - ∑_i (∇g*ρ')_i(x) ∂_iφ(x)`, the time derivative of the generator. -/
def s103nQ (d : ℕ) (s : ℝ) (ρ' : Euc d → ℝ) (φ : Euc d → ℝ) (x : Euc d) : ℝ :=
  ∑ j : Fin d, movForce d s (fun y => ρ' y * fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))) x j +
    ∑ i : Fin d, (-1 : ℝ) * (movForce d s ρ' x i * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))

theorem s103n_gen_eq {s a β : ℝ} (ρ : ℝ → Euc d → ℝ) (τ : ℝ) {φ : Euc d → ℝ} (hφ : ContDiff ℝ 2 φ)
    (x : Euc d) :
    generatorW ((quadraticGradientDyn d s a β).coeff ρ) τ φ x =
      (β⁻¹ * Laplacian.laplacian φ x + ∑ i : Fin d, (-a) * (x i * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))) +
        (∑ j : Fin d, movForce d s (fun y => ρ τ y * fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))) x j +
          ∑ i : Fin d, (-1 : ℝ) * (movForce d s (ρ τ) x i * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))) := by
  have e1 : generatorW ((quadraticGradientDyn d s a β).coeff ρ) τ φ x =
      generatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ τ)) τ φ x := by
    rw [HRS.MH.DualityRd.generatorW_coeff, HRS.MH.DualityRd.generatorW_coeff]
  rw [e1, s67_gen_eq s a β (ρ τ) τ φ x, s67bd26_inner]
  have hJ : s67J d s (ρ τ) φ x = ∑ j : Fin d, movForce d s
      (fun y => ρ τ y * fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))) x j := by
    unfold s67J
    refine Finset.sum_congr rfl fun j _ => ?_
    have hg' : (fun y => ρ τ y * gradient φ y j) =
        fun y => ρ τ y * fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ)) :=
      funext fun y => by rw [mov2d_grad_coord]
    show (movForce d s (fun y => ρ τ y * gradient φ y j) x) j = _
    rw [hg']
  rw [hJ]
  have e : ∀ i : Fin d, (-(a • x) - movForce d s (ρ τ) x) i * gradient φ x i =
      (-a) * (x i * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) +
        (-1 : ℝ) * (movForce d s (ρ τ) x i * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) := by
    intro i
    rw [mov2d_grad_coord]
    simp only [PiLp.sub_apply, PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  simp only [e, Finset.sum_add_distrib]
  ring

set_option maxHeartbeats 3200000 in
theorem s103n_gen_hasDeriv {s a β : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {L Aρ Ad Bφ : ℝ}
    (hL : (d : ℝ) < L) (hAρ : 0 ≤ Aρ) (hAd : 0 ≤ Ad)
    (ρ ρ' : ℝ → Euc d → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hρ : ∀ τ, 0 ≤ τ → U2Dec 1 L Aρ (ρ τ)) (hρ' : ∀ τ, 0 ≤ τ → U2Dec 1 L Ad (ρ' τ))
    (hder : ∀ τ, 0 ≤ τ → ∀ y, HasDerivWithinAt (fun σ => ρ σ y) (ρ' τ y) (Set.Ici τ) τ)
    (hcont : ∀ y, ContinuousOn (fun τ => ρ τ y) (Set.Ici 0))
    {φ : Euc d → ℝ} (hφ2 : ContDiff ℝ 2 φ)
    (hDg : ∀ i : Fin d, Bd 1 Bφ (fun y => fderiv ℝ φ y (EuclideanSpace.single i (1 : ℝ)))) (x : Euc d) :
    HasDerivWithinAt (fun τ => generatorW ((quadraticGradientDyn d s a β).coeff ρ) τ φ x)
      (s103nQ d s (ρ' t) φ x) (Set.Ici t) t := by
  have h1 : Bd 1 1 (fun _ : Euc d => (1 : ℝ)) := by
    refine ⟨contDiff_const, fun j hj y => ?_⟩
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp
    · rw [iteratedFDeriv_const_of_ne hj0.ne']; simp
  have hker := fun i : Fin d => ult_ker_kap hs0 hsd i
  have hconv : ∀ (i : Fin d) (τ : ℝ), 0 ≤ τ → ∀ (w : Euc d → ℝ) (Bw : ℝ), Bd 1 Bw w →
      movForce d s (fun y => ρ τ y * w y) x i = ultK (u2_kap d s i) (fun y => ρ τ y * w y) x := by
    intro i τ hτ w Bw hw
    have hB := hw.nonneg
    have := who_u2dec_mul (hρ τ hτ) hw.1 hw.2
    exact (ult_conv_comp (by omega : 1 ≤ d) hs0 hsd hL (by positivity) this x).2 i
  -- the derivatives of the two kinds of terms
  have D1 : ∀ i : Fin d, HasDerivWithinAt (fun τ => movForce d s (ρ τ) x i)
      (movForce d s (ρ' t) x i) (Set.Ici t) t := by
    intro i
    have h := s103n_ultK_hasDeriv (by omega : 1 ≤ d) (hker i) hL hAρ hAd ρ ρ' t ht hρ hρ' hder hcont
      (fun _ : Euc d => (1 : ℝ)) h1 x
    have e1 : ∀ τ, 0 ≤ τ → movForce d s (ρ τ) x i = ultK (u2_kap d s i) (fun y => ρ τ y * 1) x := by
      intro τ hτ
      have := hconv i τ hτ (fun _ => 1) 1 h1
      simpa using this
    have e2 : movForce d s (ρ' t) x i = ultK (u2_kap d s i) (fun y => ρ' t y * 1) x := by
      rw [show (fun y => ρ' t y * 1) = ρ' t from funext fun y => mul_one _]
      exact (ult_conv_comp (by omega : 1 ≤ d) hs0 hsd hL hAd (hρ' t ht) x).2 i
    rw [e2]
    exact h.congr (fun τ hτ => e1 τ (ht.trans hτ)) (e1 t ht)
  have D2 : ∀ j : Fin d, HasDerivWithinAt
      (fun τ => movForce d s (fun y => ρ τ y * fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))) x j)
      (movForce d s (fun y => ρ' t y * fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))) x j)
      (Set.Ici t) t := by
    intro j
    have h := s103n_ultK_hasDeriv (by omega : 1 ≤ d) (hker j) hL hAρ hAd ρ ρ' t ht hρ hρ' hder hcont
      (fun y => fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))) (hDg j) x
    have e2 : movForce d s (fun y => ρ' t y * fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))) x j =
        ultK (u2_kap d s j) (fun y => ρ' t y * fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))) x := by
      have := who_u2dec_mul (hρ' t ht) (hDg j).1 (hDg j).2
      exact (ult_conv_comp (by omega : 1 ≤ d) hs0 hsd hL (by have := (hDg j).nonneg; positivity) this x).2 j
    rw [e2]
    exact h.congr (fun τ hτ => hconv j τ (ht.trans hτ) _ Bφ (hDg j)) (hconv j t ht _ Bφ (hDg j))
  have D3 := HasDerivWithinAt.sum (u := Finset.univ) (fun j _ => D2 j)
  have D4 := HasDerivWithinAt.sum (u := Finset.univ) (fun i _ => ((D1 i).mul_const
    (fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))).const_mul (-1 : ℝ))
  have D5 := ((D3.add D4).const_add (β⁻¹ * Laplacian.laplacian φ x +
    ∑ i : Fin d, (-a) * (x i * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))))
  refine D5.congr (fun τ hτ => ?_) ?_
  · rw [s103n_gen_eq ρ τ hφ2 x]; simp only [Finset.sum_apply, Pi.add_apply]
  · rw [s103n_gen_eq ρ t hφ2 x]; simp only [Finset.sum_apply, Pi.add_apply]

theorem s103n_derivWithin_gen {s a β : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {L Aρ Ad Bφ : ℝ}
    (hL : (d : ℝ) < L) (hAρ : 0 ≤ Aρ) (hAd : 0 ≤ Ad)
    (ρ ρ' : ℝ → Euc d → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hρ : ∀ τ, 0 ≤ τ → U2Dec 1 L Aρ (ρ τ)) (hρ' : ∀ τ, 0 ≤ τ → U2Dec 1 L Ad (ρ' τ))
    (hder : ∀ τ, 0 ≤ τ → ∀ y, HasDerivWithinAt (fun σ => ρ σ y) (ρ' τ y) (Set.Ici τ) τ)
    (hcont : ∀ y, ContinuousOn (fun τ => ρ τ y) (Set.Ici 0))
    {φ : Euc d → ℝ} (hφ2 : ContDiff ℝ 2 φ)
    (hDg : ∀ i : Fin d, Bd 1 Bφ (fun y => fderiv ℝ φ y (EuclideanSpace.single i (1 : ℝ)))) (x : Euc d) :
    derivWithin (fun τ => generatorW ((quadraticGradientDyn d s a β).coeff ρ) τ φ x) (Set.Ici t) t =
      s103nQ d s (ρ' t) φ x :=
  (s103n_gen_hasDeriv (a := a) (β := β) hd hs0 hsd hL hAρ hAd ρ ρ' t ht hρ hρ' hder hcont hφ2 hDg x).derivWithin
    (uniqueDiffWithinAt_Ici t)

theorem s103n_Q_bd {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (N : ℕ) {L : ℝ}
    (hL : (d : ℝ) + N + s + 3 < L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Ad : ℝ) (ρ' : Euc d → ℝ), 0 ≤ Ad → U2Dec (N + 1) L Ad ρ' →
      ∀ (B : ℝ) (φ : Euc d → ℝ),
        (∀ i : Fin d, Bd (N + 1) B (fun y => fderiv ℝ φ y (EuclideanSpace.single i (1 : ℝ)))) →
        Bd N (C * Ad * B) (fun x => s103nQ d s ρ' φ x) := by
  obtain ⟨Cf, hCf0, hCf⟩ := s103n_force_sy hd hs0 hsd N hL
  refine ⟨d * (Cf * 2 ^ (N + 1)) + d * (2 ^ N * Cf), by positivity, fun Ad ρ' hAd hdec B φ hDg => ?_⟩
  have hB : 0 ≤ B := (hDg ⟨0, by omega⟩).nonneg
  have hhj : ∀ j : Fin d, U2Dec (N + 1) L (Ad * B * 2 ^ (N + 1))
      (fun y => ρ' y * fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))) := fun j =>
    who_u2dec_mul hdec (hDg j).1 (fun i hi y => (hDg j).2 i hi y)
  have T1 : Bd N (∑ j : Fin d, Cf * (Ad * B * 2 ^ (N + 1)))
      (fun x => ∑ j : Fin d, movForce d s (fun y => ρ' y * fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))) x j) :=
    Bd.sum Finset.univ _ _ (fun j _ => (hCf _ _ (by positivity) (hhj j) j).bd)
  have hFS : ∀ i : Fin d, Sy N (Cf * Ad) (fun x => movForce d s ρ' x i) := fun i => hCf Ad ρ' hAd hdec i
  have T2 : Bd N (∑ i : Fin d, |(-1 : ℝ)| * (2 ^ N * (Cf * Ad) * B))
      (fun x => ∑ i : Fin d, (-1 : ℝ) * (movForce d s ρ' x i *
        fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))) :=
    Bd.sum Finset.univ _ _ (fun i _ => ((hFS i).bd.mul ((hDg i).mono_N (Nat.le_succ N))).smul (-1))
  refine (T1.add T2).mono_A ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, abs_neg, abs_one]
  nlinarith [mul_nonneg hAd hB, mul_nonneg (mul_nonneg hAd hB) hCf0]

end HRS.MS.R2WinOrbNL

end

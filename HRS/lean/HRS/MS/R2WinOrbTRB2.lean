import HRS.MS.R2WinOrbTRB1

/-!
# S10.3 packet [B], part 2: the nonlocal part of the generator decays like `(1+‖x‖)⁻¹`

Prefix `s103b_`, namespace `HRS.MS.R2WinOrbNL`.

* `s103bQ d s h g`: the remainder of the Ornstein-Uhlenbeck splitting of the nonlinear generator,
  `q = -∑_i (∇g*h)_i ∂_i g + ∑_j (∇g*(h ∂_j g))_j` (the drift part `-∇g*h·∇g` and the nonlocal term `J_h g`).
* `s103b_gen_split`: `generatorW ((quadraticGradientDyn d s a β).coeff ρ) τ g = L_0 g + q_{ρ_τ} g` for every function `g`,
  `L_0 = β⁻¹Δ - a x·∇` (`s83_L0`).
* `s103b_q_sy`: if `h ∈ U2Dec (N+1) L Ah` (`L > d+N+s+3`) and `g ∈ C^{N+2}` has derivatives of orders `1..N+2` bounded by `G`, then
  `q_h g ∈ Sy N (C Ah G)`: the jets of `q` up to order `N` decay like `(1+‖x‖)⁻¹` (the force decay `ult_core`).  `C = C(d,s,N,L)`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.R2WinOrbNL

open HRS HRS.Whole HRS.MS.BreakdownS67 HRS.MS.MovLin HRS.MS.MovAdj HRS.MS.MovOsc HRS.MS.Ul HRS.MS.Who
  HRS.MH.DualityRd

variable {d : ℕ}

/-- `q_h g = -∑_i (∇g*h)_i ∂_i g + ∑_j (∇g*(h ∂_j g))_j`. -/
def s103bQ (d : ℕ) (s : ℝ) (h g : Euc d → ℝ) (x : Euc d) : ℝ :=
  ∑ i : Fin d, (-1 : ℝ) * (movForce d s h x i * fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ))) +
    ∑ j : Fin d, movForce d s (fun y => h y * fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ))) x j

theorem s103b_gen_split (s a β : ℝ) (ρ : ℝ → Euc d → ℝ) (τ : ℝ) (g : Euc d → ℝ) (x : Euc d) :
    generatorW ((quadraticGradientDyn d s a β).coeff ρ) τ g x =
      HRS.MS.Wad.s83_L0 a β⁻¹ g x + s103bQ d s (ρ τ) g x := by
  have h1 : generatorW ((quadraticGradientDyn d s a β).coeff ρ) τ g x =
      generatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ τ)) 0 g x := by
    simp only [generatorW_coeff]
  rw [h1, s67_gen_eq s a β (ρ τ) 0 g x]
  have hJ : s67J d s (ρ τ) g x = ∑ j : Fin d, movForce d s
      (fun y => ρ τ y * fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ))) x j := by
    unfold s67J
    refine Finset.sum_congr rfl fun j _ => ?_
    have hg' : (fun y => ρ τ y * gradient g y j) =
        fun y => ρ τ y * fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ)) :=
      funext fun y => by rw [mov2d_grad_coord]
    show (movForce d s (fun y => ρ τ y * gradient g y j) x) j = _
    rw [hg']
  have hL0 : HRS.MS.Wad.s83_L0 a β⁻¹ g x = β⁻¹ * Laplacian.laplacian g x -
      ∑ i : Fin d, a * (x i * fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ))) := by
    unfold HRS.MS.Wad.s83_L0
    rw [← HRS.MS.Wad.s83_lap_eq]
    have e : fderiv ℝ g x x = inner ℝ (gradient g x) x := (HRS.MS.Wad.s83_inner_gradient g x x).symm
    rw [e, s67bd26_inner, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mov2d_grad_coord]; ring
  have hQ : s103bQ d s (ρ τ) g x = ∑ i : Fin d, (-1 : ℝ) * (movForce d s (ρ τ) x i *
      fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ))) + ∑ j : Fin d, movForce d s
      (fun y => ρ τ y * fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ))) x j := rfl
  rw [hL0, hQ, hJ, s67bd26_inner]
  have : ∀ i : Fin d, (-(a • x) - movForce d s (ρ τ) x) i * gradient g x i =
      -(a * (x i * fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ)))) +
        (-1 : ℝ) * (movForce d s (ρ τ) x i * fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ))) := by
    intro i
    rw [mov2d_grad_coord]
    simp only [PiLp.sub_apply, PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  simp only [this, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  ring

theorem s103b_Sy_zero (N : ℕ) : Sy N 0 (fun _ : Euc d => (0 : ℝ)) := by
  refine ⟨contDiff_const, fun j _ x => ?_⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  · rw [iteratedFDeriv_const_of_ne hj.ne']; simp

theorem s103b_Sy_sum {N : ℕ} {ι : Type*} (S : Finset ι) (f : ι → Euc d → ℝ) (A : ι → ℝ)
    (h : ∀ i ∈ S, Sy N (A i) (f i)) : Sy N (∑ i ∈ S, A i) (fun x => ∑ i ∈ S, f i x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using s103b_Sy_zero (d := d) N
  | insert a S ha ih =>
    have h1 := h a (Finset.mem_insert_self _ _)
    have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have := h1.add h2
    simp only [Finset.sum_insert ha]
    exact this

theorem s103b_deriv_bd {N : ℕ} {G : ℝ} {g : Euc d → ℝ} (hg : ContDiff ℝ ((N + 2 : ℕ) : WithTop ℕ∞) g)
    (hb : ∀ i, 1 ≤ i → i ≤ N + 2 → ∀ x, ‖iteratedFDeriv ℝ i g x‖ ≤ G) (i : Fin d) :
    Bd (N + 1) G (fun y => fderiv ℝ g y (EuclideanSpace.single i (1 : ℝ))) := by
  have hd1 : ContDiff ℝ ((N + 1 : ℕ) : WithTop ℕ∞) (fderiv ℝ g) :=
    hg.fderiv_right (by exact_mod_cast le_refl (N + 2))
  have hn : ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖ = 1 := by simp
  refine ⟨hd1.clm_apply contDiff_const, fun m hm y => ?_⟩
  refine (norm_iteratedFDeriv_clm_apply_const (N := ((N + 1 : ℕ) : WithTop ℕ∞)) (c := EuclideanSpace.single i (1 : ℝ))
    (n := m) hd1.contDiffAt (by exact_mod_cast hm)).trans ?_
  rw [norm_iteratedFDeriv_fderiv, hn, one_mul]
  exact hb (m + 1) (by omega) (by omega) y

theorem s103b_q_sy {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (N : ℕ) {L : ℝ}
    (hL : (d : ℝ) + N + s + 3 < L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Ah : ℝ) (h : Euc d → ℝ), 0 ≤ Ah → U2Dec (N + 1) L Ah h →
      ∀ (G : ℝ) (g : Euc d → ℝ), ContDiff ℝ ((N + 2 : ℕ) : WithTop ℕ∞) g →
        (∀ i, 1 ≤ i → i ≤ N + 2 → ∀ x, ‖iteratedFDeriv ℝ i g x‖ ≤ G) →
        Sy N (C * Ah * G) (s103bQ d s h g) := by
  obtain ⟨Cf, hCf0, hCf⟩ := s103n_force_sy hd hs0 hsd N hL
  refine ⟨d * 2 ^ N * Cf + d * (Cf * 2 ^ (N + 1)), by positivity, fun Ah h hAh hdec G g hg hb => ?_⟩
  have hG : 0 ≤ G := by
    have := hb 1 le_rfl (by omega) 0
    exact (norm_nonneg _).trans this
  have hDg : ∀ i : Fin d, Bd (N + 1) G (fun y => fderiv ℝ g y (EuclideanSpace.single i (1 : ℝ))) :=
    fun i => s103b_deriv_bd hg hb i
  have hFS : ∀ i : Fin d, Sy N (Cf * Ah) (fun x => movForce d s h x i) := fun i => hCf Ah h hAh hdec i
  have T3 : Sy N (∑ i : Fin d, |(-1 : ℝ)| * (2 ^ N * (Cf * Ah) * G))
      (fun x => ∑ i : Fin d, (-1 : ℝ) * (movForce d s h x i *
        fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ)))) :=
    s103b_Sy_sum Finset.univ _ _ (fun i _ =>
      (((hFS i).mul_bd ((hDg i).mono_N (Nat.le_succ N)))).smul (-1))
  have hhj : ∀ j : Fin d, U2Dec (N + 1) L (Ah * G * 2 ^ (N + 1))
      (fun y => h y * fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ))) := fun j =>
    who_u2dec_mul hdec (hDg j).1 (fun i hi y => (hDg j).2 i hi y)
  have T4 : Sy N (∑ j : Fin d, Cf * (Ah * G * 2 ^ (N + 1)))
      (fun x => ∑ j : Fin d, movForce d s (fun y => h y * fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ))) x j) :=
    s103b_Sy_sum Finset.univ _ _ (fun j _ => hCf _ _ (by positivity) (hhj j) j)
  have hsum := T3.add T4
  unfold s103bQ
  refine hsum.mono_A ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, abs_neg, abs_one, one_mul]
  nlinarith [mul_nonneg hAh hG, mul_nonneg (mul_nonneg hAh hG) hCf0]

end HRS.MS.R2WinOrbNL

end

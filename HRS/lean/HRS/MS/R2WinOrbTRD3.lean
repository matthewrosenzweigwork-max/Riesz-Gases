import HRS.MS.R2WinOrbTRC2

/-!
# S10.3 packet [C], part 3: linearity of the generator, the density difference, and the generator of a function with decaying derivatives

Prefix `s103c_`, namespace `HRS.MS.R2WinOrbNL`.

* `s103c_force_sub`, `s103c_Q_sub`, `s103c_gen_sub`: `movForce`, `s103bQ` and `generatorW` are linear on the classes where they are used
  (`U2Dec 1` densities, `C²` functions with bounded first and second derivatives).
* `s103c_gen_decomp`: `L_σ g - L_t ψ = Q_{ρ_σ-ρ_t} g + L_t(g - ψ)`.
* `s103c_gen_bd_dec`: if `e ∈ C^{N+2}` has derivatives of order `1..N+2` bounded and of order `1..N+1` decaying like `(1+‖x‖)⁻¹`, then
  `L_τ e ∈ Bd N` (the standalone form of the last step of `s103b_gen_bd`).
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

theorem s103c_u2_integrable {L A : ℝ} (hL : (d : ℝ) < L) {h : Euc d → ℝ} (hh : U2Dec 0 L A h) :
    Integrable h volume := by
  refine Integrable.mono' ((u2_integrable_wt hL).const_mul A) hh.1.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  have := hh.2 0 le_rfl y
  rwa [norm_iteratedFDeriv_zero] at this

theorem s103c_force_neg {s : ℝ} (h : Euc d → ℝ) (x : Euc d) :
    movForce d s (fun y => -h y) x = - movForce d s h x := by
  unfold movForce convGradConvW
  rw [← integral_neg]
  congr 1
  funext y
  by_cases hy : ‖x - y‖ ≤ 1 / 4
  · simp only [hy, ite_true]
    rw [← neg_smul]; congr 1; ring
  · simp only [hy, ite_false]
    rw [neg_smul]

theorem s103c_force_sub {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {L A1 A2 : ℝ} (hL : (d : ℝ) < L)
    {h1 h2 : Euc d → ℝ} (h1d : U2Dec 1 L A1 h1) (h2d : U2Dec 1 L A2 h2) (x : Euc d) :
    movForce d s (fun y => h1 y - h2 y) x = movForce d s h1 x - movForce d s h2 x := by
  have c1 : ContDiff ℝ 1 h1 := by exact_mod_cast h1d.1
  have c2 : ContDiff ℝ 1 (fun y => -h2 y) := by
    have : ContDiff ℝ 1 h2 := by exact_mod_cast h2d.1
    exact this.neg
  have i1 : Integrable h1 volume := s103c_u2_integrable hL (ult_U2Dec_mono h1d (Nat.zero_le _))
  have i2 : Integrable (fun y => -h2 y) volume :=
    (s103c_u2_integrable hL (ult_U2Dec_mono h2d (Nat.zero_le _))).neg
  have := s67bd26_force_add hd hs0 hsd c1 c2 i1 i2 x
  have e : (fun y => h1 y + -h2 y) = fun y => h1 y - h2 y := by funext y; ring
  rw [e] at this
  rw [this, s103c_force_neg, sub_eq_add_neg]

theorem s103c_Q_sub {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {L A1 A2 : ℝ} (hL : (d : ℝ) < L)
    {h1 h2 : Euc d → ℝ} (h1d : U2Dec 1 L A1 h1) (h2d : U2Dec 1 L A2 h2) {g : Euc d → ℝ} {B : ℝ}
    (hg : ContDiff ℝ 2 g) (hb : ∀ i, 1 ≤ i → i ≤ 2 → ∀ y, ‖iteratedFDeriv ℝ i g y‖ ≤ B) (x : Euc d) :
    s103bQ d s (fun y => h1 y - h2 y) g x = s103bQ d s h1 g x - s103bQ d s h2 g x := by
  have hg2 : ContDiff ℝ ((0 + 2 : ℕ) : WithTop ℕ∞) g := by exact_mod_cast hg
  have hDg : ∀ j : Fin d, Bd 1 B (fun y => fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ))) :=
    fun j => by simpa using s103b_deriv_bd (N := 0) hg2 (by simpa using hb) j
  have hp1 : ∀ j : Fin d, U2Dec 1 L (A1 * B * 2 ^ 1) (fun y => h1 y * fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ))) :=
    fun j => who_u2dec_mul h1d (hDg j).1 (fun i hi y => (hDg j).2 i hi y)
  have hp2 : ∀ j : Fin d, U2Dec 1 L (A2 * B * 2 ^ 1) (fun y => h2 y * fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ))) :=
    fun j => who_u2dec_mul h2d (hDg j).1 (fun i hi y => (hDg j).2 i hi y)
  unfold s103bQ
  have hF := s103c_force_sub hd hs0 hsd hL h1d h2d x
  have e1 : ∀ j : Fin d, (fun y => (h1 y - h2 y) * fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ))) =
      fun y => h1 y * fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ)) -
        h2 y * fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ)) := fun j => by funext y; ring
  have hF2 : ∀ j : Fin d, movForce d s (fun y => (h1 y - h2 y) * fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ))) x =
      movForce d s (fun y => h1 y * fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ))) x -
      movForce d s (fun y => h2 y * fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ))) x := fun j => by
    rw [e1 j]; exact s103c_force_sub hd hs0 hsd hL (hp1 j) (hp2 j) x
  have hsum : ∑ i : Fin d, (-1 : ℝ) * (movForce d s (fun y => h1 y - h2 y) x i *
        fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ))) =
      ∑ i : Fin d, (-1 : ℝ) * (movForce d s h1 x i * fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ))) -
      ∑ i : Fin d, (-1 : ℝ) * (movForce d s h2 x i * fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ))) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hF]; simp only [PiLp.sub_apply]; ring
  have hsum2 : ∑ j : Fin d, movForce d s (fun y => (h1 y - h2 y) * fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ))) x j =
      ∑ j : Fin d, movForce d s (fun y => h1 y * fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ))) x j -
      ∑ j : Fin d, movForce d s (fun y => h2 y * fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ))) x j := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hF2 j]; simp only [PiLp.sub_apply]
  rw [hsum, hsum2]; ring

theorem s103c_Q_subg {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {L A : ℝ} (hL : (d : ℝ) < L)
    {h : Euc d → ℝ} (hh : U2Dec 1 L A h) {g1 g2 : Euc d → ℝ} {B : ℝ}
    (hg1 : ContDiff ℝ 2 g1) (hb1 : ∀ i, 1 ≤ i → i ≤ 2 → ∀ y, ‖iteratedFDeriv ℝ i g1 y‖ ≤ B)
    (hg2 : ContDiff ℝ 2 g2) (hb2 : ∀ i, 1 ≤ i → i ≤ 2 → ∀ y, ‖iteratedFDeriv ℝ i g2 y‖ ≤ B) (x : Euc d) :
    s103bQ d s h (fun y => g1 y - g2 y) x = s103bQ d s h g1 x - s103bQ d s h g2 x := by
  have hFj : ∀ (j : Fin d) (y : Euc d), fderiv ℝ (fun y => g1 y - g2 y) y (EuclideanSpace.single j (1 : ℝ)) =
      fderiv ℝ g1 y (EuclideanSpace.single j (1 : ℝ)) - fderiv ℝ g2 y (EuclideanSpace.single j (1 : ℝ)) := by
    intro j y
    rw [fderiv_fun_sub ((hg1.differentiable (by norm_num)) y) ((hg2.differentiable (by norm_num)) y)]
    rfl
  have hDg1 : ∀ j : Fin d, Bd 1 B (fun y => fderiv ℝ g1 y (EuclideanSpace.single j (1 : ℝ))) :=
    fun j => by simpa using s103b_deriv_bd (N := 0) (by exact_mod_cast hg1) (by simpa using hb1) j
  have hDg2 : ∀ j : Fin d, Bd 1 B (fun y => fderiv ℝ g2 y (EuclideanSpace.single j (1 : ℝ))) :=
    fun j => by simpa using s103b_deriv_bd (N := 0) (by exact_mod_cast hg2) (by simpa using hb2) j
  have hp1 := fun j : Fin d => who_u2dec_mul hh (hDg1 j).1 (fun i hi y => (hDg1 j).2 i hi y)
  have hp2 := fun j : Fin d => who_u2dec_mul hh (hDg2 j).1 (fun i hi y => (hDg2 j).2 i hi y)
  have hFj2 : ∀ j : Fin d, movForce d s (fun y => h y * fderiv ℝ (fun y => g1 y - g2 y) y
      (EuclideanSpace.single j (1 : ℝ))) x =
      movForce d s (fun y => h y * fderiv ℝ g1 y (EuclideanSpace.single j (1 : ℝ))) x -
      movForce d s (fun y => h y * fderiv ℝ g2 y (EuclideanSpace.single j (1 : ℝ))) x := by
    intro j
    have e : (fun y => h y * fderiv ℝ (fun y => g1 y - g2 y) y (EuclideanSpace.single j (1 : ℝ))) =
        fun y => h y * fderiv ℝ g1 y (EuclideanSpace.single j (1 : ℝ)) -
          h y * fderiv ℝ g2 y (EuclideanSpace.single j (1 : ℝ)) := by
      funext y; rw [hFj j y]; ring
    rw [e]
    exact s103c_force_sub hd hs0 hsd hL (hp1 j) (hp2 j) x
  unfold s103bQ
  have hsum1 : ∑ i : Fin d, (-1 : ℝ) * (movForce d s h x i *
        fderiv ℝ (fun y => g1 y - g2 y) x (EuclideanSpace.single i (1 : ℝ))) =
      ∑ i : Fin d, (-1 : ℝ) * (movForce d s h x i * fderiv ℝ g1 x (EuclideanSpace.single i (1 : ℝ))) -
      ∑ i : Fin d, (-1 : ℝ) * (movForce d s h x i * fderiv ℝ g2 x (EuclideanSpace.single i (1 : ℝ))) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hFj i x]; ring
  have hsum2 : ∑ j : Fin d, movForce d s (fun y => h y * fderiv ℝ (fun y => g1 y - g2 y) y
        (EuclideanSpace.single j (1 : ℝ))) x j =
      ∑ j : Fin d, movForce d s (fun y => h y * fderiv ℝ g1 y (EuclideanSpace.single j (1 : ℝ))) x j -
      ∑ j : Fin d, movForce d s (fun y => h y * fderiv ℝ g2 y (EuclideanSpace.single j (1 : ℝ))) x j := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hFj2 j]; simp only [PiLp.sub_apply]
  rw [hsum1, hsum2]; ring

theorem s103c_gen_sub {s a β : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {L A : ℝ} (hL : (d : ℝ) < L)
    (ρ : ℝ → Euc d → ℝ) (τ : ℝ) (hρ : U2Dec 1 L A (ρ τ)) {g1 g2 : Euc d → ℝ} {B : ℝ}
    (hg1 : ContDiff ℝ 2 g1) (hb1 : ∀ i, 1 ≤ i → i ≤ 2 → ∀ y, ‖iteratedFDeriv ℝ i g1 y‖ ≤ B)
    (hg2 : ContDiff ℝ 2 g2) (hb2 : ∀ i, 1 ≤ i → i ≤ 2 → ∀ y, ‖iteratedFDeriv ℝ i g2 y‖ ≤ B) (x : Euc d) :
    generatorW ((quadraticGradientDyn d s a β).coeff ρ) τ (fun y => g1 y - g2 y) x =
      generatorW ((quadraticGradientDyn d s a β).coeff ρ) τ g1 x -
      generatorW ((quadraticGradientDyn d s a β).coeff ρ) τ g2 x := by
  rw [s103b_gen_split, s103b_gen_split, s103b_gen_split, s103b_L0_eq, s103b_L0_eq, s103b_L0_eq,
    s103c_Q_subg hd hs0 hsd hL hρ hg1 hb1 hg2 hb2 x]
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

/-- `L_σ g - L_t ψ = Q_{ρ_σ-ρ_t} g + L_t (g - ψ)`. -/
theorem s103c_gen_decomp {s a β : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {L A : ℝ} (hL : (d : ℝ) < L)
    (ρ : ℝ → Euc d → ℝ) (σ t : ℝ) (hσ : U2Dec 1 L A (ρ σ)) (ht : U2Dec 1 L A (ρ t)) {g ψ : Euc d → ℝ} {B : ℝ}
    (hg : ContDiff ℝ 2 g) (hbg : ∀ i, 1 ≤ i → i ≤ 2 → ∀ y, ‖iteratedFDeriv ℝ i g y‖ ≤ B)
    (hψ : ContDiff ℝ 2 ψ) (hbψ : ∀ i, 1 ≤ i → i ≤ 2 → ∀ y, ‖iteratedFDeriv ℝ i ψ y‖ ≤ B) (x : Euc d) :
    generatorW ((quadraticGradientDyn d s a β).coeff ρ) σ g x -
        generatorW ((quadraticGradientDyn d s a β).coeff ρ) t ψ x =
      s103bQ d s (fun y => ρ σ y - ρ t y) g x +
        generatorW ((quadraticGradientDyn d s a β).coeff ρ) t (fun y => g y - ψ y) x := by
  rw [s103c_gen_sub hd hs0 hsd hL ρ t ht hg hbg hψ hbψ x, s103c_Q_sub hd hs0 hsd hL hσ ht hg hbg x,
    s103b_gen_split s a β ρ σ g x, s103b_gen_split s a β ρ t ψ x, s103b_gen_split s a β ρ t g x]
  ring

end HRS.MS.R2WinOrbNL

end

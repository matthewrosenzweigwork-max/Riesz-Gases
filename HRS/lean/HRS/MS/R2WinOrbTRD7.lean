import HRS.MS.R2WinOrbTRD6

/-!
# S10.3 packet [D], part 1: closure of `IsClassicalAdjointW` under restriction and linear combinations

Prefix `s103c_`, namespace `HRS.MS.R2WinOrbNL`.

* `s103c_gen_smul`, `s103c_gen_lin`: `generatorW` is linear on `C²` functions with bounded first and second derivatives (for `U2Dec 1` densities).
* `s103c_restrict`: a classical adjoint solution on `[0,t]` restricts to one on `[0,t']`, `t' ≤ t`, with terminal datum `f t'`.
* `s103c_lincomb`: `c₁ f₁ + c₂ f₂` is a classical adjoint solution with datum `c₁ψ₁ + c₂ψ₂`.
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

theorem s103c_force_smul {s : ℝ} (c : ℝ) (h : Euc d → ℝ) (x : Euc d) :
    movForce d s (fun y => c * h y) x = c • movForce d s h x := by
  unfold movForce convGradConvW
  rw [← integral_smul]
  congr 1
  funext y
  by_cases hy : ‖x - y‖ ≤ 1 / 4
  · simp only [hy, ite_true]
    rw [smul_smul, ← mul_sub]
  · simp only [hy, ite_false]
    rw [smul_smul]

theorem s103c_gen_smul {s a β : ℝ} (ρ : ℝ → Euc d → ℝ) (τ : ℝ) (c : ℝ) {g : Euc d → ℝ} (hg : ContDiff ℝ 2 g)
    (x : Euc d) :
    generatorW ((quadraticGradientDyn d s a β).coeff ρ) τ (fun y => c * g y) x =
      c * generatorW ((quadraticGradientDyn d s a β).coeff ρ) τ g x := by
  rw [s103b_gen_split, s103b_gen_split, s103b_L0_eq, s103b_L0_eq]
  have hfd : ∀ (y : Euc d) (i : Fin d), fderiv ℝ (fun y => c * g y) y (EuclideanSpace.single i (1 : ℝ)) =
      c * fderiv ℝ g y (EuclideanSpace.single i (1 : ℝ)) := by
    intro y i
    rw [fderiv_const_mul ((hg.differentiable (by norm_num)) y)]
    rfl
  have hlap : Laplacian.laplacian (fun y => c * g y) x = c * Laplacian.laplacian g x := by
    have e : (fun y => c * g y) = c • g := by funext y; simp
    rw [e, InnerProductSpace.laplacian_smul c (hg.contDiffAt (x := x))]
    simp
  have e : ∀ j : Fin d, (fun y => ρ τ y * fderiv ℝ (fun y => c * g y) y (EuclideanSpace.single j (1 : ℝ))) =
      fun y => c * (ρ τ y * fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ))) := fun j => by
    funext y; rw [hfd y j]; ring
  have hQ : s103bQ d s (ρ τ) (fun y => c * g y) x = c * s103bQ d s (ρ τ) g x := by
    unfold s103bQ
    have hF2 : ∀ j : Fin d, movForce d s (fun y => ρ τ y * fderiv ℝ (fun y => c * g y) y
        (EuclideanSpace.single j (1 : ℝ))) x j =
        c * movForce d s (fun y => ρ τ y * fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ))) x j := fun j => by
      rw [e j, s103c_force_smul]; simp
    simp only [hF2]
    simp only [hfd]
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  have hS : ∑ i : Fin d, a * (x i * fderiv ℝ (fun y => c * g y) x (EuclideanSpace.single i (1 : ℝ))) =
      c * ∑ i : Fin d, a * (x i * fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ))) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hfd x i]; ring
  rw [hQ, hlap, hS]
  ring

theorem s103c_gen_lin {s a β : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {L A : ℝ} (hL : (d : ℝ) < L)
    (ρ : ℝ → Euc d → ℝ) (τ : ℝ) (hρ : U2Dec 1 L A (ρ τ)) (c1 c2 : ℝ) {g1 g2 : Euc d → ℝ} {B : ℝ}
    (hg1 : ContDiff ℝ 2 g1) (hb1 : ∀ i, 1 ≤ i → i ≤ 2 → ∀ y, ‖iteratedFDeriv ℝ i g1 y‖ ≤ B)
    (hg2 : ContDiff ℝ 2 g2) (hb2 : ∀ i, 1 ≤ i → i ≤ 2 → ∀ y, ‖iteratedFDeriv ℝ i g2 y‖ ≤ B) (x : Euc d) :
    generatorW ((quadraticGradientDyn d s a β).coeff ρ) τ (fun y => c1 * g1 y + c2 * g2 y) x =
      c1 * generatorW ((quadraticGradientDyn d s a β).coeff ρ) τ g1 x +
      c2 * generatorW ((quadraticGradientDyn d s a β).coeff ρ) τ g2 x := by
  have hs1 : ContDiff ℝ 2 (fun y => c1 * g1 y) := contDiff_const.mul hg1
  have hs2 : ContDiff ℝ 2 (fun y => (-c2) * g2 y) := contDiff_const.mul hg2
  have hbs : ∀ (c : ℝ) (g : Euc d → ℝ), ContDiff ℝ 2 g → (∀ i, 1 ≤ i → i ≤ 2 → ∀ y, ‖iteratedFDeriv ℝ i g y‖ ≤ B) →
      ∀ i, 1 ≤ i → i ≤ 2 → ∀ y, ‖iteratedFDeriv ℝ i (fun y => c * g y) y‖ ≤ |c| * B := by
    intro c g hg hb i h1 h2 y
    have e : (fun y => c * g y) = c • g := by funext y; simp
    rw [e, iteratedFDeriv_const_smul_apply (hg.of_le (by exact_mod_cast h2)).contDiffAt, norm_smul,
      Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hb i h1 h2 y) (abs_nonneg _)
  have hbs1 := hbs c1 g1 hg1 hb1
  have hbs2 := hbs (-c2) g2 hg2 hb2
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hb1 1 le_rfl (by norm_num) 0)
  have hp1 : 0 ≤ |c1| * B := mul_nonneg (abs_nonneg _) hB0
  have hp2 : 0 ≤ |-c2| * B := mul_nonneg (abs_nonneg _) hB0
  have hB1 : ∀ i, 1 ≤ i → i ≤ 2 → ∀ y, ‖iteratedFDeriv ℝ i (fun y => c1 * g1 y) y‖ ≤ |c1| * B + |-c2| * B :=
    fun i h1 h2 y => (hbs1 i h1 h2 y).trans (by linarith)
  have hB2 : ∀ i, 1 ≤ i → i ≤ 2 → ∀ y, ‖iteratedFDeriv ℝ i (fun y => (-c2) * g2 y) y‖ ≤ |c1| * B + |-c2| * B :=
    fun i h1 h2 y => (hbs2 i h1 h2 y).trans (by linarith)
  have e : (fun y => c1 * g1 y + c2 * g2 y) = fun y => c1 * g1 y - (-c2) * g2 y := by funext y; ring
  rw [e, s103c_gen_sub hd hs0 hsd hL ρ τ hρ hs1 hB1 hs2 hB2 x, s103c_gen_smul ρ τ c1 hg1 x,
    s103c_gen_smul ρ τ (-c2) hg2 x]
  ring

theorem s103c_restrict {C : WholeCoeff d} {t t' : ℝ} {ψ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW C t ψ f) (ht' : t' ≤ t) : IsClassicalAdjointW C t' (f t') f := by
  have hsub : ∀ r ∈ Set.Icc (0 : ℝ) t', r ∈ Set.Icc (0 : ℝ) t := fun r hr => ⟨hr.1, hr.2.trans ht'⟩
  have hinc : Continuous (fun p : Set.Icc (0 : ℝ) t' × Euc d =>
      ((⟨p.1.1, hsub p.1.1 p.1.2⟩ : Set.Icc (0 : ℝ) t), p.2)) := by
    refine Continuous.prodMk ?_ continuous_snd
    exact Continuous.subtype_mk (continuous_subtype_val.comp continuous_fst) _
  have hbdd : ∀ j ≤ 2, ∃ B : ℝ, ∀ r ∈ Set.Icc (0 : ℝ) t', ∀ x, ‖iteratedFDeriv ℝ j (f r) x‖ ≤ B := by
    intro j hj
    obtain ⟨B, hB⟩ := hf.bdd j hj
    exact ⟨B, fun r hr x => hB r (hsub r hr) x⟩
  have hcc : ∀ j ≤ 2, Continuous fun p : Set.Icc (0 : ℝ) t' × Euc d => iteratedFDeriv ℝ j (f p.1) p.2 := by
    intro j hj
    have := (hf.cont_c2 j hj).comp hinc
    exact this
  have htd : ∀ x : Euc d, ∀ r ∈ Set.Ioo (0 : ℝ) t',
      HasDerivAt (fun r' => f r' x) (-(generatorW C r (f r) x)) r := fun x r hr =>
    hf.time_deriv x r ⟨hr.1, hr.2.trans_le ht'⟩
  have hct : Continuous fun p : Set.Icc (0 : ℝ) t' × Euc d => generatorW C p.1 (f p.1) p.2 := by
    have := hf.cont_time_deriv.comp hinc
    exact this
  have hbt : ∃ B : ℝ, ∀ r ∈ Set.Icc (0 : ℝ) t', ∀ x, |generatorW C r (f r) x| ≤ B * (1 + ‖x‖) := by
    obtain ⟨B, hB⟩ := hf.bdd_time_deriv
    exact ⟨B, fun r hr x => hB r (hsub r hr) x⟩
  exact ⟨fun r hr => hf.c2 r (hsub r hr), hbdd, hcc, rfl, htd, hct, hbt⟩

theorem s103c_lincomb {s a β : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {L A : ℝ} (hL : (d : ℝ) < L)
    (ρ : ℝ → Euc d → ℝ) {t : ℝ} (hρ : ∀ τ ∈ Set.Icc (0 : ℝ) t, U2Dec 1 L A (ρ τ)) (c1 c2 : ℝ)
    {ψ1 ψ2 : Euc d → ℝ} {f1 f2 : ℝ → Euc d → ℝ}
    (hf1 : IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff ρ) t ψ1 f1)
    (hf2 : IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff ρ) t ψ2 f2) :
    IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff ρ) t (fun y => c1 * ψ1 y + c2 * ψ2 y)
      (fun r y => c1 * f1 r y + c2 * f2 r y) := by
  set Cf := (quadraticGradientDyn d s a β).coeff ρ with hCf
  obtain ⟨B1, hB1⟩ := hf1.bdd 1 (by norm_num)
  obtain ⟨B2, hB2⟩ := hf1.bdd 2 (by norm_num)
  obtain ⟨B1', hB1'⟩ := hf2.bdd 1 (by norm_num)
  obtain ⟨B2', hB2'⟩ := hf2.bdd 2 (by norm_num)
  set Bm : ℝ := max (max B1 B2) (max B1' B2') with hBm
  have hj1 : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ i, 1 ≤ i → i ≤ 2 → ∀ y, ‖iteratedFDeriv ℝ i (f1 r) y‖ ≤ Bm := by
    intro r hr i h1 h2 y
    interval_cases i
    · exact (hB1 r hr y).trans ((le_max_left _ _).trans (le_max_left _ _))
    · exact (hB2 r hr y).trans ((le_max_right _ _).trans (le_max_left _ _))
  have hj2 : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ i, 1 ≤ i → i ≤ 2 → ∀ y, ‖iteratedFDeriv ℝ i (f2 r) y‖ ≤ Bm := by
    intro r hr i h1 h2 y
    interval_cases i
    · exact (hB1' r hr y).trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact (hB2' r hr y).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hcomb : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ y, generatorW Cf r (fun y => c1 * f1 r y + c2 * f2 r y) y =
      c1 * generatorW Cf r (f1 r) y + c2 * generatorW Cf r (f2 r) y := fun r hr y =>
    s103c_gen_lin hd hs0 hsd hL ρ r (hρ r hr) c1 c2 (hf1.c2 r hr) (hj1 r hr) (hf2.c2 r hr) (hj2 r hr) y
  have hit : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ j ≤ 2, ∀ y,
      iteratedFDeriv ℝ j (fun y => c1 * f1 r y + c2 * f2 r y) y =
        c1 • iteratedFDeriv ℝ j (f1 r) y + c2 • iteratedFDeriv ℝ j (f2 r) y := by
    intro r hr j hj y
    have e : (fun y => c1 * f1 r y + c2 * f2 r y) = (fun y => c1 • f1 r y) + (fun y => c2 • f2 r y) := by
      funext y; simp
    have hj' : (j : WithTop ℕ∞) ≤ 2 := by exact_mod_cast hj
    have hc1 : ContDiffAt ℝ j (f1 r) y := ((hf1.c2 r hr).of_le hj').contDiffAt
    have hc2 : ContDiffAt ℝ j (f2 r) y := ((hf2.c2 r hr).of_le hj').contDiffAt
    have e1 : (fun y => c1 • f1 r y) = c1 • f1 r := rfl
    have e2 : (fun y => c2 • f2 r y) = c2 • f2 r := rfl
    rw [e, iteratedFDeriv_add_apply (hc1.const_smul c1) (hc2.const_smul c2), e1, e2,
      iteratedFDeriv_const_smul_apply hc1, iteratedFDeriv_const_smul_apply hc2]
  refine ⟨fun r hr => (contDiff_const.mul (hf1.c2 r hr)).add (contDiff_const.mul (hf2.c2 r hr)),
    fun j hj => ?_, fun j hj => ?_, ?_, fun x r hr => ?_, ?_, ?_⟩
  · obtain ⟨Ba, hBa⟩ := hf1.bdd j hj
    obtain ⟨Bb, hBb⟩ := hf2.bdd j hj
    refine ⟨|c1| * Ba + |c2| * Bb, fun r hr x => ?_⟩
    rw [hit r hr j hj x]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact add_le_add (mul_le_mul_of_nonneg_left (hBa r hr x) (abs_nonneg _))
      (mul_le_mul_of_nonneg_left (hBb r hr x) (abs_nonneg _))
  · have h1 := hf1.cont_c2 j hj
    have h2 := hf2.cont_c2 j hj
    have := (h1.const_smul c1).add (h2.const_smul c2)
    refine this.congr fun p => ?_
    rw [hit p.1.1 p.1.2 j hj p.2]; rfl
  · funext y; simp [hf1.terminal, hf2.terminal]
  · have h1 := hf1.time_deriv x r hr
    have h2 := hf2.time_deriv x r hr
    have := (h1.const_mul c1).add (h2.const_mul c2)
    convert this using 1
    rw [hcomb r ⟨hr.1.le, hr.2.le⟩ x]; ring
  · have h1 := hf1.cont_time_deriv
    have h2 := hf2.cont_time_deriv
    have := (h1.const_smul c1).add (h2.const_smul c2)
    refine this.congr fun p => ?_
    rw [hcomb p.1.1 p.1.2 p.2]; simp
  · obtain ⟨Ba, hBa⟩ := hf1.bdd_time_deriv
    obtain ⟨Bb, hBb⟩ := hf2.bdd_time_deriv
    refine ⟨|c1| * Ba + |c2| * Bb, fun r hr x => ?_⟩
    rw [hcomb r hr x]
    have a1 := hBa r hr x
    have a2 := hBb r hr x
    have hw : 0 ≤ 1 + ‖x‖ := by positivity
    calc |c1 * generatorW Cf r (f1 r) x + c2 * generatorW Cf r (f2 r) x| ≤
        |c1| * |generatorW Cf r (f1 r) x| + |c2| * |generatorW Cf r (f2 r) x| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul]
      _ ≤ |c1| * (Ba * (1 + ‖x‖)) + |c2| * (Bb * (1 + ‖x‖)) :=
          add_le_add (mul_le_mul_of_nonneg_left a1 (abs_nonneg _)) (mul_le_mul_of_nonneg_left a2 (abs_nonneg _))
      _ = _ := by ring

end HRS.MS.R2WinOrbNL

end

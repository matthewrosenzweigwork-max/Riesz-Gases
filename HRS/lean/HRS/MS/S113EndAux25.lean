import HRS.MS.S113EndAux24
import HRS.MS.S113EndAux19

/-!
# S11.3 endpoint (worker S11X), part 25: the source identity, almost everywhere in time (X1a)

`S113XSourceIdentityAE`: for the members of the small class and `N ≥ 2`, for almost every `t > 0` and every collision-free `X`,
`R_N^t(X) = (movFP q_N^t - ∂_t q_N^t)/q_N^t = -βN (F_N^{h_{u^t}}(X) - E_{Q_N^t} F_N^{h_{u^t}})` (`W:r2mov:source-identity`).
`s113x_identity_ae`: proved from the class facts `S113XFacts` (Gaussian family, `∂_t ρ = div(ρ u)`), the Fokker-Planck identity (part 15),
the time derivative of `q_N^τ` (part 23, with the a.e. derivative of `log K` from S.B.1, part 21) and the algebraic identity (part 19).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S113BD

open HRS HRS.Whole

variable {d : ℕ}

/-- The source identity for almost every time. -/
def S113XSourceIdentityAE (d : ℕ) (s q β : ℝ) (ρ₀ : Euc d → ℝ) (j m : ℕ) (εstar r c₀ : ℝ) : Prop :=
  ∀ f0 : Euc d → ℝ, MovInitialClass ρ₀ j m εstar f0 →
    ∀ ρ : ℝ → Euc d → ℝ, MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ →
    ∀ N : ℕ, 2 ≤ N → ∀ᵐ t : ℝ, 0 < t → ∀ X : EucConfig d N, X ∉ eucCollisionSet d N →
      s113x_source d s q β N ρ t X =
        -β * N * (pairEnergy (commutatorKernel d s (movU d s q β (ρ t))) X (HRS.Whole.withDensityReal (ρ t)) -
          ∫ Y, pairEnergy (commutatorKernel d s (movU d s q β (ρ t))) Y (HRS.Whole.withDensityReal (ρ t))
            ∂(s113x_Q d s β ρ N t))

theorem s113x_identity_ae (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {q β : ℝ} (hβ : 0 < β)
    (hq : 0 < q) {ρ₀ : Euc d → ℝ} (hρ₀ : IsThermalEquilibrium d s q β ρ₀) {j m : ℕ}
    {εstar r c₀ c C₁ : ℝ} (hj : 1 ≤ j) (hm : (d : ℝ) / 2 + j + 6 < m) (hC₁ : 0 < C₁) (hε : 0 < εstar) (hc : 0 < c)
    (hc₀ : 0 < c₀) (hNL : MovNonlinearConclusion d s q β ρ₀ j m εstar r c₀ c C₁)
    (hF : ∀ f0 : Euc d → ℝ, MovInitialClass ρ₀ j m εstar f0 →
      ∀ ρ : ℝ → Euc d → ℝ, MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ → S113XFacts d s q β ρ) :
    S113XSourceIdentityAE d s q β ρ₀ j m εstar r c₀ := by
  intro f0 hf0 ρ hρ N hN
  have hsd : s < d := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  have hd1 : 1 ≤ d := by omega
  have hFacts := hF f0 hf0 ρ hρ
  obtain ⟨cg, Kg, M, hcg, hKg, hM, hG, hSl, hDer⟩ := hFacts
  have hprops := HRS.MS.MovEnt.s66_class_props hNL hf0 hρ hc₀.le
  have hall : ∀ n : ℕ, ∀ᵐ t : ℝ, t ∈ Set.Ioo 0 (n : ℝ) →
      HasDerivAt (fun τ => Real.log (HRS.Whole.gibbsNormalizer (rieszKernel d s) N β (HRS.Whole.withDensityReal (ρ τ))))
        (β * N * s113x_EQ d s q β ρ N t) t := fun n =>
    s113x_logK_deriv_ae hβ.ne' (Nat.cast_nonneg n)
      (s113x_SbLogK_class hd hs0 hs hβ hq hρ₀ hj hm hC₁ hε hc hc₀ hNL hf0 hρ ⟨cg, Kg, M, hcg, hKg, hM, hG, hSl, hDer⟩ hN (Nat.cast_nonneg n))
  rw [← ae_all_iff] at hall
  filter_upwards [hall] with t ht' ht0 X hX
  obtain ⟨n, hn⟩ := exists_nat_gt t
  have hκ := ht' n ⟨ht0, hn⟩
  set Dfam : ℝ → Euc d → ℝ := fun τ y => movDiv (fun y' => ρ τ y' • movU d s q β (ρ τ) y') y with hDfam
  set B' : ℝ := max Kg ((d : ℝ) * (2 * (Kg * M))) with hB'
  have hHG : S113XGauss ρ Dfam cg B' :=
    { hc := hcg
      hB := le_trans hKg (le_max_left _ _)
      rho_nn := fun τ hτ y => ((hprops τ hτ.le).2.1 y).le
      rho_cont := fun τ hτ => (hG τ hτ.le).1.continuous
      D_cont := fun τ hτ => (hSl τ hτ.le).D_cont
      rho_le := fun τ hτ y => ((hSl τ hτ.le).g0 y).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
      D_le := fun τ hτ y => ((hSl τ hτ.le).D_le y).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)
      deriv := fun τ hτ y => hDer τ hτ y }
  have hpos : ∀ τ, 0 < τ → ∀ y, 0 < ρ τ y := fun τ hτ y => (hprops τ hτ.le).2.1 y
  have hKp : ∀ τ, 0 < τ → 0 < HRS.Whole.gibbsNormalizer (rieszKernel d s) N β (HRS.Whole.withDensityReal (ρ τ)) :=
    fun τ hτ => s113x_K_pos hd hs0 hs hβ hq hρ₀ hC₁ hc₀ hNL hf0 hρ hN hτ.le
  have hQd := s113x_Q_timederiv (s := s) (β := β) (N := N) hd1 hs0 hsd hHG hpos hKp ht0 hκ X
  -- slice at time t
  have S := hSl t ht0.le
  have hQpos : 0 < movQDensity d s β N (ρ t) X := by
    unfold movQDensity
    have := hKp t ht0
    have hp : 0 < ∏ i, ρ t (X i) := Finset.prod_pos fun i _ => hpos t ht0 _
    positivity
  have hfd : ∀ x, DifferentiableAt ℝ (ρ t) x := fun x => (hG t ht0.le).1.differentiable (by norm_num) x
  have hΓ : ∀ x, HasFDerivAt (HRS.Whole.convMeasure (rieszKernel d s) (HRS.Whole.withDensityReal (ρ t)))
      (innerSL ℝ (movForce d s (ρ t) x)) x := by
    intro x
    have hfun : HRS.Whole.convMeasure (rieszKernel d s) (HRS.Whole.withDensityReal (ρ t)) =
        fun x => ∫ z, rieszKernel d s z * ρ t (x - z) := funext fun x =>
      s113x_convMeasure_eq (hG t ht0.le).1.continuous.measurable (fun y => (hpos t ht0 y).le) _ x
    rw [hfun]
    exact s113x_Gamma_hasFDerivAt hd1 hs0 hsd S x
  have hFP := s113x_movFP_eq (N := N) hβ.ne' hfd (hpos t ht0) hΓ (S.ucd.differentiable (by norm_num)) hX
  have hdw : derivWithin (fun τ => movQDensity d s β N (ρ τ) X) (Set.Ici t) t = deriv (fun τ => movQDensity d s β N (ρ τ) X) t :=
    hQd.differentiableAt.derivWithin (uniqueDiffWithinAt_Ici t)
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have halg := s113x_alg (N := N) hd1 hs0 hsd hβ.ne' S hX hN0 (β * N * s113x_EQ d s q β ρ N t) (s113x_EQ d s q β ρ N t) rfl
  unfold s113x_source
  rw [ite_cond_eq_false _ _ (eq_false hX), hdw, hQd.deriv, hFP, ← mul_sub, mul_div_cancel_left₀ _ hQpos.ne']
  exact halg

end HRS.MS.S113BD

end

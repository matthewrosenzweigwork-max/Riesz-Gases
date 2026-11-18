import HRS.MS.Fp81S21AdjointAll
import HRS.MS.Fp81S21OscDatum

/-!
# S2.1(iii): linearity of the chosen propagator on oscillator tests

Every oscillator test admits a classical adjoint along a resulting trajectory.
S10.3 superposition and S10.4 uniqueness therefore identify the chosen
propagator on all oscillator tests, not only finite Hermite combinations.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R2WinOrbNL

private theorem fp81s21_propOsc_density_u2dec
    (p : HRS.MS.R26T3.Parameters) {δ : ℝ}
    (R : HRS.MS.R26T3.Trajectory p δ) {t : ℝ} (_ht : 0 ≤ t) :
    ∃ A : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) t,
      U2Dec 1 ((p.d + 1 : ℕ) : ℝ) A (R.ρ τ) := by
  have hsd : p.s < (p.d : ℝ) := by
    have hdreal : (2 : ℝ) ≤ (p.d : ℝ) := by exact_mod_cast p.hd
    nlinarith [p.hs]
  obtain ⟨c, K, hc, hK0, hρ⟩ := HRS.MS.S104e.s104e_gauss_rho
    p.hd p.hs0 hsd p.ha p.hβ δ p.c₁ p.C₁ 1 (by omega)
    R.thermal R.resulting
  obtain ⟨P, hP0, hU⟩ := HRS.MS.S104e.s104e_u2dec_of_gauss
    (d := p.d) hc 1 (p.d + 1)
  refine ⟨P * K, fun τ hτ => ?_⟩
  have hτ' : 0 ≤ τ := hτ.1
  obtain ⟨hreg, hbnd⟩ := hρ τ hτ'
  exact hU (R.ρ τ) K hK0 hreg (fun k hk x => hbnd k hk x)

/-- The chosen propagator is linear on arbitrary oscillator tests. -/
theorem fp81s21_U_linear_of_osc_test
    (p : HRS.MS.R26T3.Parameters) {δ : ℝ}
    (R : HRS.MS.R26T3.Trajectory p δ)
    {φ ψ : Euc p.d → ℝ}
    (hφ : IsOscTest ((wholeSpaceIndex p.d : ℕ) : ℝ) φ)
    (hψ : IsOscTest ((wholeSpaceIndex p.d : ℕ) : ℝ) ψ)
    (c : ℝ) {t r : ℝ} (ht : 0 ≤ t)
    (hr : r ∈ Set.Icc (0 : ℝ) t) :
    HRS.MS.R26T3.r26t3_U R r t (fun x => φ x + c * ψ x) =
      fun x => HRS.MS.R26T3.r26t3_U R r t φ x +
        c * HRS.MS.R26T3.r26t3_U R r t ψ x := by
  obtain ⟨f, hf⟩ := fp81s21_adjoint_of_osc_test p R hφ ht
  obtain ⟨g, hg⟩ := fp81s21_adjoint_of_osc_test p R hψ ht
  have hsd : p.s < (p.d : ℝ) := by
    have hdreal : (2 : ℝ) ≤ (p.d : ℝ) := by exact_mod_cast p.hd
    nlinarith [p.hs]
  obtain ⟨A, hA⟩ := fp81s21_propOsc_density_u2dec p R ht
  have hlin0 := HRS.MS.R2WinOrbNL.s103c_lincomb p.hd p.hs0 hsd
    (show (p.d : ℝ) < ((p.d + 1 : ℕ) : ℝ) by exact_mod_cast Nat.lt_succ_self p.d)
    R.ρ hA 1 c hf hg
  have hlin : IsClassicalAdjointW ((quadraticGradientDyn p.d p.s p.a p.β).coeff R.ρ)
      t (fun x => φ x + c * ψ x) (fun q x => f q x + c * g q x) := by
    simpa only [one_mul] using hlin0
  have huF := HRS.MS.S104e.s104e_unique p.hd p.hs0 hsd p.ha p.hβ
    δ p.c₁ p.C₁ R.thermal R.admissible R.resulting t ht ⟨ht, le_rfl⟩ hf
  have huG := HRS.MS.S104e.s104e_unique p.hd p.hs0 hsd p.ha p.hβ
    δ p.c₁ p.C₁ R.thermal R.admissible R.resulting t ht ⟨ht, le_rfl⟩ hg
  have huSum := HRS.MS.S104e.s104e_unique p.hd p.hs0 hsd p.ha p.hβ
    δ p.c₁ p.C₁ R.thermal R.admissible R.resulting t ht ⟨ht, le_rfl⟩ hlin
  have ef : HRS.MS.R26T3.r26t3_U R r t φ = f r := by
    simpa [HRS.MS.R26T3.r26t3_U, HRS.MS.R26T3.r26t3_coeff] using huF r hr
  have eg : HRS.MS.R26T3.r26t3_U R r t ψ = g r := by
    simpa [HRS.MS.R26T3.r26t3_U, HRS.MS.R26T3.r26t3_coeff] using huG r hr
  have esum : HRS.MS.R26T3.r26t3_U R r t (fun x => φ x + c * ψ x) =
      (fun x => f r x + c * g r x) := by
    simpa [HRS.MS.R26T3.r26t3_U, HRS.MS.R26T3.r26t3_coeff] using huSum r hr
  rw [esum, ef, eg]

/-- The chosen propagator commutes with adding a constant to an oscillator
test; the constant datum is handled by its classical constant solution. -/
theorem fp81s21_U_constant_osc
    (p : HRS.MS.R26T3.Parameters) {δ : ℝ}
    (R : HRS.MS.R26T3.Trajectory p δ)
    {φ : Euc p.d → ℝ}
    (hφ : IsOscTest ((wholeSpaceIndex p.d : ℕ) : ℝ) φ)
    (c : ℝ) {t r : ℝ} (ht : 0 ≤ t)
    (hr : r ∈ Set.Icc (0 : ℝ) t) :
    HRS.MS.R26T3.r26t3_U R r t (fun x => φ x + c) =
      fun x => HRS.MS.R26T3.r26t3_U R r t φ x + c := by
  obtain ⟨f, hf⟩ := fp81s21_adjoint_of_osc_test p R hφ ht
  have hsd : p.s < (p.d : ℝ) := by
    have hdreal : (2 : ℝ) ≤ (p.d : ℝ) := by exact_mod_cast p.hd
    nlinarith [p.hs]
  obtain ⟨A, hA⟩ := fp81s21_propOsc_density_u2dec p R ht
  have hconst : IsClassicalAdjointW
      ((quadraticGradientDyn p.d p.s p.a p.β).coeff R.ρ) t
      (fun _ => c) (fun _ _ => c) :=
    HRS.MS.Wad.s8d_const_classical _ t c
  have hlin0 := HRS.MS.R2WinOrbNL.s103c_lincomb p.hd p.hs0 hsd
    (show (p.d : ℝ) < ((p.d + 1 : ℕ) : ℝ) by exact_mod_cast Nat.lt_succ_self p.d)
    R.ρ hA 1 1 hf hconst
  have hlin : IsClassicalAdjointW
      ((quadraticGradientDyn p.d p.s p.a p.β).coeff R.ρ) t
      (fun x => φ x + c) (fun q x => f q x + c) := by
    simpa only [one_mul] using hlin0
  have huF := HRS.MS.S104e.s104e_unique p.hd p.hs0 hsd p.ha p.hβ
    δ p.c₁ p.C₁ R.thermal R.admissible R.resulting t ht ⟨ht, le_rfl⟩ hf
  have huSum := HRS.MS.S104e.s104e_unique p.hd p.hs0 hsd p.ha p.hβ
    δ p.c₁ p.C₁ R.thermal R.admissible R.resulting t ht ⟨ht, le_rfl⟩ hlin
  have ef : HRS.MS.R26T3.r26t3_U R r t φ = f r := by
    simpa [HRS.MS.R26T3.r26t3_U, HRS.MS.R26T3.r26t3_coeff] using huF r hr
  have esum : HRS.MS.R26T3.r26t3_U R r t (fun x => φ x + c) =
      (fun x => f r x + c) := by
    simpa [HRS.MS.R26T3.r26t3_U, HRS.MS.R26T3.r26t3_coeff] using huSum r hr
  rw [esum, ef]

/-- The selected propagator trajectory itself is a classical adjoint solution.
It is the very witness selected in `propagatorW` when the oscillator datum has
an adjoint solution. -/
theorem fp81s21_U_osc_test_classical
    (p : HRS.MS.R26T3.Parameters) {δ : ℝ}
    (R : HRS.MS.R26T3.Trajectory p δ)
    {φ : Euc p.d → ℝ}
    (hφ : IsOscTest ((wholeSpaceIndex p.d : ℕ) : ℝ) φ)
    {t : ℝ} (ht : 0 ≤ t) :
    IsClassicalAdjointW (HRS.MS.R26T3.r26t3_coeff R) t φ
      (fun r => HRS.MS.R26T3.r26t3_U R r t φ) := by
  have hex : ∃ f, IsClassicalAdjointW
      ((quadraticGradientDyn p.d p.s p.a p.β).coeff R.ρ) t φ f := by
    simpa [HRS.MS.R26T3.r26t3_coeff] using
      (fp81s21_adjoint_of_osc_test p R hφ ht)
  let f : ℝ → Euc p.d → ℝ := Classical.choose hex
  have hf : IsClassicalAdjointW (HRS.MS.R26T3.r26t3_coeff R) t φ f := by
    simpa [HRS.MS.R26T3.r26t3_coeff] using (Classical.choose_spec hex)
  have hchosen : ∀ r, HRS.MS.R26T3.r26t3_U R r t φ = f r := by
    intro r
    change HRS.Whole.propagatorW
      ((quadraticGradientDyn p.d p.s p.a p.β).coeff R.ρ) r t φ =
        Classical.choose hex r
    unfold HRS.Whole.propagatorW
    rw [dif_pos hex]
  have hfun : (fun r => HRS.MS.R26T3.r26t3_U R r t φ) = f := funext hchosen
  rw [hfun]
  exact hf

end HRS.Fp81.S21

#print axioms HRS.Fp81.S21.fp81s21_U_linear_of_osc_test
#print axioms HRS.Fp81.S21.fp81s21_U_constant_osc
#print axioms HRS.Fp81.S21.fp81s21_U_osc_test_classical

end

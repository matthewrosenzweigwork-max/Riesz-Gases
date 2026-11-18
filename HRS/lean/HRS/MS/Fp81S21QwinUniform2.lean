import HRS.MS.Fp81S21QwinUniform
import HRS.MS.R2WinOrbNLAux13
import HRS.MS.R2WinOrbNLAux15
import HRS.MS.R2WinOrbNLAux16
import HRS.MS.R2WinOrbNLAux17
import HRS.MS.R2WinOrbNLAux19
import HRS.MS.R2WinOrbTRD14

/-!
# HRS S2.1(iii), SOL26 packet 27b: gradient decay for the second terminal datum

The bounded jets of `L_t^2 φ_α + ∂_t L_t φ_α` are retained from the time derivative
of the density.  The nonlinear orbit gradient estimate is applied to that datum itself.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole
open HRS.MS.R26T3
open HRS.MS.R2WinOrb
open HRS.MS.R2WinOrbNL
open HRS.MS.MovLin

private theorem fp81s21_qwin_canonical_thermal (p : Parameters) :
    IsThermalEquilibrium p.d p.s p.a p.β
      (thermalDensity p.d p.s p.a p.β) := by
  have hdp : 2 ≤ p.d := p.hd
  have hdnat : 0 < p.d := by omega
  have hdpos : (0 : ℝ) < p.d := by exact_mod_cast hdnat
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  by_cases hs0 : p.s = 0
  · obtain ⟨⟨ρ, hρ, -⟩, -, -⟩ :=
      HRS.MS.Thm.logThermalDensity_spec_proof p.hd p.a p.β p.ha p.hβ
    have hρeq := HRS.MS.Mov0.mv0_rho_eq p.hd (by norm_num) hdpos p.ha p.hβ hρ
    rw [hρeq] at hρ
    simpa [hs0] using hρ
  · have hspos : 0 < p.s := lt_of_le_of_ne p.hs0 (Ne.symm hs0)
    obtain ⟨⟨ρ, hρ, -⟩, -, -⟩ :=
      HRS.MS.Thm.thermalDensity_spec_proof p.hd hspos hsd p.a p.β p.ha p.hβ
    have hρeq := HRS.MS.Mov0.mv0_rho_eq p.hd p.hs0 hsd p.ha p.hβ hρ
    rw [hρeq] at hρ
    exact hρ

/-- A bounded smooth terminal datum has a gradient orbit estimate, with its bound
chosen uniformly before the datum and terminal time. -/
theorem fp81s21_qwin_orbitGrad_of_bd
    {d : ℕ} {s a β : ℝ} {ρβ : Euc d → ℝ} {ρ : ℝ → Euc d → ℝ}
    (H : Mov2dTh d s β a ρβ) {Cg cg Cz : ℝ}
    (hCg : 0 ≤ Cg) (hcg : 0 < cg) (hCz : 0 ≤ Cz)
    (hG : S103nGrad d s a β ρβ ρ Cg cg)
    (hZ : S103nZero d s a β ρβ ρ Cz) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (g : Euc d → ℝ) (B : ℝ), Bd (8 * d + 80) B g →
      ∀ t : ℝ, 0 ≤ t →
        R2OrbitGrad ((quadraticGradientDyn d s a β).coeff ρ) (4 * d + 42) t g (K * B) cg := by
  obtain ⟨Cψ, hCψ0, hCψ⟩ := s103n_psi_of_jets H (8 * d + 80)
  set M : ℝ := (((4 * d + 42 : ℕ) + 1 : ℝ) + 1 + Cψ)
  set K : ℝ := 2 * Cg * M
  have hM1 : ((4 * d + 42 : ℕ) + 1 : ℝ) ≤ M := by
    dsimp [M]
    nlinarith [hCψ0]
  have hM2 : 1 ≤ M := by
    dsimp [M]
    have hd0 : (0 : ℝ) ≤ (4 * d + 42 : ℕ) := Nat.cast_nonneg _
    nlinarith [hCψ0, hd0]
  have hM3 : Cψ ≤ M := by
    dsimp [M]
    have hd0 : (0 : ℝ) ≤ (4 * d + 42 : ℕ) := Nat.cast_nonneg _
    nlinarith [hd0]
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K, hK, fun g B hBd t ht => ?_⟩
  have hB := hBd.nonneg
  have hgk : ContDiff ℝ ((4 * d + 42 + 1 : ℕ) : WithTop ℕ∞) g :=
    hBd.1.of_le (by exact_mod_cast (by omega : 4 * d + 42 + 1 ≤ 8 * d + 80))
  have hcb := s103n_cb_of_jets (n := 4 * d + 42) hgk
    (fun l hl x => hBd.2 l (by omega) x)
  obtain ⟨hm1, hm2⟩ := hCψ B g hBd
  set B' : ℝ := M * B
  have hB'0 : 0 ≤ B' := by dsimp [B']; positivity
  have h1 : ((4 * d + 42 : ℕ) + 1 : ℝ) * B ≤ B' := by
    dsimp [B']
    exact mul_le_mul_of_nonneg_right hM1 hB
  have h2 : B ≤ B' := by
    dsimp [B']
    calc B = 1 * B := by ring
      _ ≤ M * B := mul_le_mul_of_nonneg_right hM2 hB
  have h3 : Cψ * B ≤ B' := by
    dsimp [B']
    exact mul_le_mul_of_nonneg_right hM3 hB
  have hcb' : cbNormVecE (4 * d + 42) (fun x => gradient g x) ≤ ENNReal.ofReal B' :=
    hcb.trans (ENNReal.ofReal_le_ofReal h1)
  have hsup : ∀ x, |g x| ≤ B' := by
    intro x
    have h := hBd.2 0 (Nat.zero_le _) x
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
    exact h.trans h2
  have hψ := s103n_orbit_of_data hCg hcg hCz hG hZ g B' hB'0 hgk hcb' hsup
    hm1 (hm2.trans h3) t ht
  have heq : 2 * Cg * B' = K * B := by
    dsimp [B', K, M]
    ring
  simpa only [heq] using hψ.1

/-- Uniform exponential gradient decay of the propagated second terminal datum
`(L_t^2 + ∂_t L_t) φ_α`, retaining the right time derivative of the generator. -/
theorem fp81s21_second_terminal_grad (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ A : ℝ, 0 ≤ A ∧ ∃ c : ℝ, 0 < c ∧
          ∀ α : MultiIndex p.d, ∀ t : ℝ, 0 ≤ t →
            R2OrbitGrad (r26t3_coeff R) (4 * p.d + 42) t
              (s103nData (r26t3_coeff R)
                (oscTestFun (wholeSpaceIndex p.d : ℝ) α) 2 t)
              (A * s103_b p.d α) c := by
  by_cases hc₁ : 0 < p.c₁
  · have hsd : p.s < (p.d : ℝ) := by
      have hdreal : (2 : ℝ) ≤ (p.d : ℝ) := by exact_mod_cast p.hd
      nlinarith [p.hs]
    obtain ⟨δc, Co, co, hδc, hδchalf, hco, hcommon⟩ := fp81s21_common_radius p
    let H : Mov2dTh p.d p.s p.β p.a (thermalDensity p.d p.s p.a p.β) :=
      ⟨p.hd, p.hs0, hsd, p.hβ, p.ha, fp81s21_qwin_canonical_thermal p⟩
    obtain ⟨Rw, hRw, hZ⟩ := s103n_zeroth H
    have hK : ((8 * p.d + 83 : ℕ) : ℝ) + (p.d : ℝ) / 2 + 4 <
        ((102 * p.d + 1020 : ℕ) : ℝ) := by
      push_cast
      linarith
    obtain ⟨εstar, r, hεstar, hr, hr1, hrRw, hCε,
        ⟨Cg, cg, hCg, hcg, hGrad⟩, hSch⟩ :=
      s103n_setup2 H Rw hRw (8 * p.d + 83) hK p.c₁ p.C₁ hc₁
    obtain ⟨Cz, hCz0, hZr⟩ :=
      hZ r p.c₁ Cg cg hr.le hrRw hr1 hc₁.le hcg (by linarith [hCg])
    let δ0 : ℝ := min δc (min εstar (1 / 2))
    have hδ0 : 0 < δ0 := by
      dsimp [δ0]
      exact lt_min hδc (lt_min hεstar (by norm_num))
    have hδhalf : δ0 ≤ 1 / 2 := by
      dsimp [δ0]
      exact (min_le_right _ _).trans (min_le_right _ _)
    refine ⟨δ0, hδ0, hδhalf, fun δ hδ hδle R => ?_⟩
    have hδε : δ ≤ εstar := by
      have hδle' : δ ≤ min δc (min εstar (1 / 2)) := by simpa [δ0] using hδle
      exact hδle'.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hC1 : 0 ≤ p.C₁ := s103c_C₁_nonneg R.resulting hδ
    have hCεδ : p.C₁ * δ ≤ r := by
      calc p.C₁ * δ ≤ p.C₁ * εstar := mul_le_mul_of_nonneg_left hδε hC1
        _ ≤ r := hCε
    have hsmall := s103n_small_class R.resulting hCεδ
    have hρeq : R.ρβ = thermalDensity p.d p.s p.a p.β := by
      rw [HRS.MS.Mov0.mv0_rho_eq p.hd p.hs0 hsd p.ha p.hβ R.thermal,
        HRS.MS.Mov0.mv0_rho_eq p.hd p.hs0 hsd p.ha p.hβ
          (fp81s21_qwin_canonical_thermal p)]
    have hsmallH : MovInSmallClass p.d p.s p.a p.β
        (thermalDensity p.d p.s p.a p.β) (102 * p.d + 1020) r p.c₁
        (fun x => R.ε * R.ψ x) R.ρ := by
      simpa [hρeq] using hsmall
    have hG : S103nGrad p.d p.s p.a p.β
        (thermalDensity p.d p.s p.a p.β) R.ρ Cg cg :=
      hGrad (fun x => R.ε * R.ψ x) R.ρ hsmallH
    have hZ' : S103nZero p.d p.s p.a p.β
        (thermalDensity p.d p.s p.a p.β) R.ρ Cz := by
      intro T φ f Bφ hT hf hφ hosc hfin hφB r' hr' x
      exact hZr (fun y => R.ε * R.ψ y) R.ρ hsmallH hG
        T φ f Bφ hT hf hφ hosc hfin hφB r' hr' x
    have hcZ : 0 ≤ Cz := hCz0
    obtain ⟨Kbd, hKbd, hbdGrad⟩ :=
      fp81s21_qwin_orbitGrad_of_bd H (by linarith) hcg hcZ hG hZ'
    set Lnat : ℕ := p.d + (8 * p.d + 80) + ⌈p.s⌉₊ + 6 with hLnat
    have hL : (p.d : ℝ) + ((8 * p.d + 80 : ℕ) : ℝ) + p.s + 5 < (Lnat : ℝ) := by
      have hsceil : p.s ≤ (⌈p.s⌉₊ : ℝ) := Nat.le_ceil p.s
      simp only [hLnat]
      push_cast
      linarith
    obtain ⟨CKL, hCKL⟩ := hSch Lnat
    obtain ⟨Aβ, hAβ0, hAβ⟩ := s103n_rho_u2dec H (8 * p.d + 83) Lnat
    obtain ⟨K5, hK50, hK5⟩ := s103n_g5_data H hL
    obtain ⟨Kφ, hKφ0, hKφ⟩ := s103n_phi_sy p.hd p.hs0 hsd
    set Ad : ℝ := 2 ^ Lnat * |CKL|
    set Aρ : ℝ := Aβ + Ad
    have hAd0 : 0 ≤ Ad := by positivity
    have hAρ0 : 0 ≤ Aρ := by positivity
    have hδε' : δ ≤ εstar := hδε
    have hAdm2 := s103c_adm_mono R.admissible hδε'
    have hRes2 := s103c_res_mono R.resulting hδ hδε'
    have hAdm2H : IsAdmissiblePerturbation (thermalDensity p.d p.s p.a p.β)
        εstar R.ε R.ψ := by simpa [hρeq] using hAdm2
    have hRes2H : IsResultingSolution p.d p.s p.a p.β
        (thermalDensity p.d p.s p.a p.β) εstar R.ε R.ψ p.c₁ p.C₁ R.ρ := by
      simpa [hρeq] using hRes2
    obtain ⟨ρ', hder, hcls⟩ := hCKL R.ε R.ψ R.ρ hAdm2H hRes2H
    have hclass : ∀ τ : ℝ, 0 ≤ τ →
        U2Dec (8 * p.d + 83) (Lnat : ℝ) Aρ (R.ρ τ) ∧
        U2Dec (8 * p.d + 83) (Lnat : ℝ) Ad (ρ' τ) := by
      intro τ hτ
      obtain ⟨h1, h2, h3⟩ := hcls τ hτ
      have hdec := hAβ |CKL| R.ρ ρ' τ hτ h1 h2
        (fun k hk x => (h3 k hk x).trans (le_abs_self _))
      simpa [Aρ, Ad] using hdec
    have hh : ∀ τ : ℝ, 0 ≤ τ → U2Dec 1 (Lnat : ℝ) Aρ (R.ρ τ) := by
      intro τ hτ
      have h := (hclass τ hτ).1
      exact ⟨h.1.of_le (by exact_mod_cast (by omega : 1 ≤ 8 * p.d + 83)),
        fun m hm => h.2 m (by omega)⟩
    have hh' : ∀ τ : ℝ, 0 ≤ τ → U2Dec 1 (Lnat : ℝ) Ad (ρ' τ) := by
      intro τ hτ
      have h := (hclass τ hτ).2
      exact ⟨h.1.of_le (by exact_mod_cast (by omega : 1 ≤ 8 * p.d + 83)),
        fun m hm => h.2 m (by omega)⟩
    have hmcls : (p.d : ℝ) / 2 + 2 < ((102 * p.d + 1020 : ℕ) : ℝ) := by
      push_cast
      linarith
    have hcont : ∀ y, ContinuousOn (fun τ => R.ρ τ y) (Set.Ici 0) :=
      fun y => s103n_cont_time H hmcls hsmallH y
    have hLd : (p.d : ℝ) < (Lnat : ℝ) := by
      have h8 : ((8 * p.d + 80 : ℕ) : ℝ) = 8 * (p.d : ℝ) + 80 := by
        push_cast
        ring
      simp only [hLnat]
      push_cast
      linarith [p.hs0]
    set Q : ℝ := K5 * (1 + Aρ) ^ 2 * (1 + Ad)
    have hQ : 0 ≤ Q := by positivity
    let A : ℝ := Kbd * Q
    have hA : 0 ≤ A := by dsimp [A]; positivity
    have hc : 0 < cg := hcg
    refine ⟨A, hA, cg, hc, fun α t ht => ?_⟩
    let φ : Euc p.d → ℝ := oscTestFun (wholeSpaceIndex p.d : ℝ) α
    have hDg : ∀ i : Fin p.d, Bd 1 (Kφ * s103_b p.d α)
        (fun y => fderiv ℝ φ y (EuclideanSpace.single i (1 : ℝ))) := fun i =>
      ((hKφ α i).bd).mono_N (by omega)
    have hφ2 : ContDiff ℝ 2 φ := by
      have hφsmooth : ContDiff ℝ ∞ φ := by
        simpa [φ, wholeSpaceIndex] using s103n_phi_smooth α
      exact hφsmooth.of_le (by norm_num)
    have hdw : ∀ x, derivWithin
        (fun t' => generatorW (r26t3_coeff R) t' φ x) (Set.Ici t) t =
          s103nQ p.d p.s (ρ' t) φ x := by
      intro x
      simpa [r26t3_coeff] using
        (s103n_derivWithin_gen (a := p.a) (β := p.β) p.hd p.hs0 hsd hLd
          hAρ0 hAd0 R.ρ ρ' t ht hh hh' hder hcont hφ2 hDg x)
    have hfun : (fun x => generatorW (r26t3_coeff R) t
          (generatorW (r26t3_coeff R) t φ) x +
          derivWithin (fun t' => generatorW (r26t3_coeff R) t' φ x) (Set.Ici t) t) =
        fun x => generatorW ((quadraticGradientDyn p.d p.s p.a p.β).coeff
            (fun _ => R.ρ t)) 0
          (fun y => generatorW ((quadraticGradientDyn p.d p.s p.a p.β).coeff
            (fun _ => R.ρ t)) 0 φ y) x + s103nQ p.d p.s (ρ' t) φ x := by
      funext x
      rw [hdw x]
      have hfreeze := s103n_gen_frozen (s := p.s) (a := p.a) (β := p.β) R.ρ t
        (generatorW (r26t3_coeff R) t φ) x
      have hfreezeInner : generatorW (r26t3_coeff R) t φ =
          generatorW ((quadraticGradientDyn p.d p.s p.a p.β).coeff
            (fun _ => R.ρ t)) 0 φ := by
        funext y
        simpa only [r26t3_coeff] using
          (s103n_gen_frozen (s := p.s) (a := p.a) (β := p.β) R.ρ t φ y)
      have hfreeze' : generatorW (r26t3_coeff R) t
          (generatorW (r26t3_coeff R) t φ) x =
          generatorW ((quadraticGradientDyn p.d p.s p.a p.β).coeff
            (fun _ => R.ρ t)) 0
            (fun y => generatorW ((quadraticGradientDyn p.d p.s p.a p.β).coeff
              (fun _ => R.ρ t)) 0 φ y) x := by
        calc
          generatorW (r26t3_coeff R) t
              (generatorW (r26t3_coeff R) t φ) x =
              generatorW ((quadraticGradientDyn p.d p.s p.a p.β).coeff
                (fun _ => R.ρ t)) 0 (generatorW (r26t3_coeff R) t φ) x := by
                  simpa only [r26t3_coeff] using hfreeze
          _ = generatorW ((quadraticGradientDyn p.d p.s p.a p.β).coeff
                (fun _ => R.ρ t)) 0
                (fun y => generatorW ((quadraticGradientDyn p.d p.s p.a p.β).coeff
                  (fun _ => R.ρ t)) 0 φ y) x := by
                  rw [hfreezeInner]
      exact congrArg (fun z : ℝ => z + s103nQ p.d p.s (ρ' t) φ x) hfreeze'
    have hsecondBd : Bd (8 * p.d + 80) (Q * s103_b p.d α)
        (s103nData (r26t3_coeff R) φ 2 t) := by
      have hg5 := hK5 Aρ Ad hAρ0 hAd0 (R.ρ t) (ρ' t) α
        (hclass t ht).1
        (by
          have h := (hclass t ht).2
          exact ⟨h.1.of_le (by exact_mod_cast (by omega : 8 * p.d + 81 ≤ 8 * p.d + 83)),
            fun m hm => h.2 m (by omega)⟩)
      have hg5base : Bd (8 * p.d + 80) (Q * s103_b p.d α)
          (fun x => generatorW ((quadraticGradientDyn p.d p.s p.a p.β).coeff
              (fun _ => R.ρ t)) 0
            (fun y => generatorW ((quadraticGradientDyn p.d p.s p.a p.β).coeff
              (fun _ => R.ρ t)) 0 φ y) x + s103nQ p.d p.s (ρ' t) φ x) := by
        simpa [Q, φ, wholeSpaceIndex] using hg5
      have hg5' : Bd (8 * p.d + 80) (Q * s103_b p.d α)
          (fun x => generatorW (r26t3_coeff R) t
            (generatorW (r26t3_coeff R) t φ) x +
            derivWithin (fun t' => generatorW (r26t3_coeff R) t' φ x) (Set.Ici t) t) :=
        hfun ▸ hg5base
      simpa [s103nData, φ] using hg5'
    have hgrad := hbdGrad (s103nData (r26t3_coeff R) φ 2 t)
      (Q * s103_b p.d α) hsecondBd t ht
    have heq : Kbd * (Q * s103_b p.d α) = A * s103_b p.d α := by
      dsimp [A]
      ring
    simpa only [heq, r26t3_coeff] using hgrad
  · refine ⟨1 / 2, by norm_num, by norm_num, fun δ hδ hδle R => ?_⟩
    exact False.elim (hc₁ R.resulting.cpos)

#print axioms fp81s21_qwin_orbitGrad_of_bd
#print axioms fp81s21_second_terminal_grad

end HRS.Fp81.S21

end

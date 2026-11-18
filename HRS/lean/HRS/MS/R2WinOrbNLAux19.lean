import HRS.MS.R2WinOrbNLAux18

/-!
# S10.3 (nonlinear branch), part 19: the five orbit claims along every small nonlinear trajectory

Prefix `s103n_`, namespace `HRS.MS.R2WinOrbNL`.  `s103n_orbits_nonlinear`: for the thermal equilibrium `ρ_β` (`Mov2dTh`) and any class constants `c₁, C₁`
(repair D2/ED14: universally quantified before `ε_*`, as in S2.1(ii); no existence statement) there are `ε_* > 0` and `C, c > 0` such that for every admissible perturbation and every `ρ` with `IsResultingSolution` and
every `α`, `t ≥ 0` the five orbit claims of `HRS.Whole.r2_window_orbits` hold for `Cf = (quadraticGradientDyn d s a β).coeff ρ` in the ED13 form (right derivative
`derivWithin (fun t' => generatorW Cf t' φ x) (Set.Ici t) t` in the fifth claim).
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.R2WinOrbNL

open HRS HRS.Whole HRS.MS.Ul HRS.MS.MovLin HRS.MS.MovOsc HRS.MS.Mov63 HRS.MS.Who HRS.MS.BreakdownS67
  HRS.MS.MovAdj HRS.MS.R2WinOrb

variable {d : ℕ}

set_option maxHeartbeats 6400000 in
theorem s103n_orbits_nonlinear {s a β : ℝ} {ρβ : Euc d → ℝ} (H : Mov2dTh d s β a ρβ) (c₁ C₁ : ℝ) :
    ∃ εstar : ℝ, 0 < εstar ∧
      ∃ C c : ℝ, 0 < c ∧ ∀ (ε : ℝ) (ψ : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ),
        IsAdmissiblePerturbation ρβ εstar ε ψ → IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ →
        ∀ (α : MultiIndex d) (t : ℝ), 0 ≤ t →
          R2OrbitSup ((quadraticGradientDyn d s a β).coeff ρ) (4 * d + 42) t
            (oscTestFun (((24 * d + 240 : ℕ)) : ℝ) α) (C * s103_b d α) ∧
          R2OrbitGrad ((quadraticGradientDyn d s a β).coeff ρ) (4 * d + 42) t
            (oscTestFun (((24 * d + 240 : ℕ)) : ℝ) α) (C * s103_b d α) c ∧
          R2OrbitSup ((quadraticGradientDyn d s a β).coeff ρ) (4 * d + 42) t
            (generatorW ((quadraticGradientDyn d s a β).coeff ρ) t (oscTestFun (((24 * d + 240 : ℕ)) : ℝ) α))
            (C * s103_b d α) ∧
          R2OrbitGrad ((quadraticGradientDyn d s a β).coeff ρ) (4 * d + 42) t
            (generatorW ((quadraticGradientDyn d s a β).coeff ρ) t (oscTestFun (((24 * d + 240 : ℕ)) : ℝ) α))
            (C * s103_b d α) c ∧
          R2OrbitSup ((quadraticGradientDyn d s a β).coeff ρ) (4 * d + 42) t
            (fun x => generatorW ((quadraticGradientDyn d s a β).coeff ρ) t
                (generatorW ((quadraticGradientDyn d s a β).coeff ρ) t
                  (oscTestFun (((24 * d + 240 : ℕ)) : ℝ) α)) x +
              derivWithin (fun t' => generatorW ((quadraticGradientDyn d s a β).coeff ρ) t'
                (oscTestFun (((24 * d + 240 : ℕ)) : ℝ) α) x) (Set.Ici t) t) (C * s103_b d α) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  by_cases hc₁ : 0 < c₁
  swap
  · exact ⟨1, one_pos, 1, 1, one_pos, fun ε ψ ρ _ hρ => absurd hρ.cpos hc₁⟩
  obtain ⟨Rw, hRw, hZ⟩ := s103n_zeroth H
  have hK : ((8 * d + 83 : ℕ) : ℝ) + d / 2 + 4 < ((102 * d + 1020 : ℕ) : ℝ) := by push_cast; linarith
  obtain ⟨εstar, r, hε, hr, hr1, hrRw, hCε, ⟨Cg, cg, hCg, hcg, hGrad⟩, hSch⟩ :=
    s103n_setup2 H Rw hRw (8 * d + 83) hK c₁ C₁ hc₁
  obtain ⟨Cz, hCz0, hZr⟩ := hZ r c₁ Cg cg hr.le hrRw hr1 hc₁.le hcg (by linarith)
  obtain ⟨C1234, hC12340, hC1234⟩ := s103n_claims1234 H (by linarith : 0 ≤ Cg) hcg hCz0
  obtain ⟨C5, hC50, hC5⟩ := s103n_orbitSup_of_bd H (by linarith : 0 ≤ Cg) hcg hCz0
  set Lnat : ℕ := d + (8 * d + 80) + ⌈s⌉₊ + 6 with hLnat
  have hL : (d : ℝ) + ((8 * d + 80 : ℕ) : ℝ) + s + 5 < (Lnat : ℝ) := by
    have : s ≤ (⌈s⌉₊ : ℝ) := Nat.le_ceil s
    simp only [hLnat]; push_cast; linarith
  obtain ⟨CKL, hCKL⟩ := hSch Lnat
  obtain ⟨Aβ, hAβ0, hAβ⟩ := s103n_rho_u2dec H (8 * d + 83) Lnat
  obtain ⟨K5, hK50, hK5⟩ := s103n_g5_data H hL
  obtain ⟨Kφ, hKφ0, hKφ⟩ := s103n_phi_sy H.hd H.hs0 H.hsd
  set Ad : ℝ := 2 ^ Lnat * |CKL| with hAd
  set Aρ : ℝ := Aβ + Ad with hAρ
  have hAd0 : 0 ≤ Ad := by positivity
  have hAρ0 : 0 ≤ Aρ := by positivity
  refine ⟨εstar, hε, max C1234 (C5 * (K5 * (1 + Aρ) ^ 2 * (1 + Ad))), cg, hcg,
    fun ε ψ ρ hψ hρ α t ht => ?_⟩
  have hb0 := s103_b_nonneg (d := d) α
  have hsm := s103n_small_class hρ hCε
  have hG : S103nGrad d s a β ρβ ρ Cg cg := hGrad _ ρ hsm
  have hZ' : S103nZero d s a β ρβ ρ Cz := fun T φ f Bφ hT hf hφ1 hosc hfin hφB r' hr' x =>
    hZr _ ρ hsm hG T φ f Bφ hT hf hφ1 hosc hfin hφB r' hr' x
  obtain ⟨c1, c2, c3, c4⟩ := hC1234 r c₁ hr.le hr1 hc₁.le _ ρ hsm hG hZ' α t ht
  have hm1 : C1234 * s103_b d α ≤ max C1234 (C5 * (K5 * (1 + Aρ) ^ 2 * (1 + Ad))) * s103_b d α :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hb0
  -- the fifth claim
  obtain ⟨ρ', hder, hcls⟩ := hCKL ε ψ ρ hψ hρ
  have hclass : ∀ τ : ℝ, 0 ≤ τ → U2Dec (8 * d + 83) (Lnat : ℝ) Aρ (ρ τ) ∧
      U2Dec (8 * d + 83) (Lnat : ℝ) Ad (ρ' τ) := by
    intro τ hτ
    obtain ⟨h1, h2, h3⟩ := hcls τ hτ
    have := hAβ |CKL| ρ ρ' τ hτ h1 h2 (fun k hk x => (h3 k hk x).trans (le_abs_self _))
    exact this
  have hh : ∀ τ : ℝ, 0 ≤ τ → U2Dec 1 (Lnat : ℝ) Aρ (ρ τ) := fun τ hτ => by
    have := (hclass τ hτ).1
    exact ⟨this.1.of_le (by exact_mod_cast (by omega : 1 ≤ 8 * d + 83)), fun m hm => this.2 m (by omega)⟩
  have hh' : ∀ τ : ℝ, 0 ≤ τ → U2Dec 1 (Lnat : ℝ) Ad (ρ' τ) := fun τ hτ => by
    have := (hclass τ hτ).2
    exact ⟨this.1.of_le (by exact_mod_cast (by omega : 1 ≤ 8 * d + 83)), fun m hm => this.2 m (by omega)⟩
  have hmcls : (d : ℝ) / 2 + 2 < ((102 * d + 1020 : ℕ) : ℝ) := by push_cast; linarith
  have hcont : ∀ y, ContinuousOn (fun τ => ρ τ y) (Set.Ici 0) := fun y => s103n_cont_time H hmcls hsm y
  have hLd : (d : ℝ) < (Lnat : ℝ) := by
    have h0 := H.hs0
    have h8 : ((8 * d + 80 : ℕ) : ℝ) = 8 * (d : ℝ) + 80 := by push_cast; ring
    linarith
  set φ : Euc d → ℝ := oscTestFun (((24 * d + 240 : ℕ)) : ℝ) α with hφ
  have hDg : ∀ i : Fin d, Bd 1 (Kφ * s103_b d α)
      (fun y => fderiv ℝ φ y (EuclideanSpace.single i (1 : ℝ))) := fun i =>
    ((hKφ α i).bd).mono_N (by omega)
  have hφ2 : ContDiff ℝ 2 φ := by
    have : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) φ := (s103n_phi_smooth α).of_le (s103_cast_le_infty 2)
    exact_mod_cast this
  have hdw : ∀ x, derivWithin (fun t' => generatorW ((quadraticGradientDyn d s a β).coeff ρ) t' φ x)
      (Set.Ici t) t = s103nQ d s (ρ' t) φ x := fun x =>
    s103n_derivWithin_gen (a := a) (β := β) H.hd H.hs0 H.hsd hLd hAρ0 hAd0 ρ ρ' t ht hh hh' hder hcont hφ2 hDg x
  have hfun : (fun x => generatorW ((quadraticGradientDyn d s a β).coeff ρ) t
        (generatorW ((quadraticGradientDyn d s a β).coeff ρ) t φ) x +
        derivWithin (fun t' => generatorW ((quadraticGradientDyn d s a β).coeff ρ) t' φ x) (Set.Ici t) t) =
      fun x => generatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ t)) 0
          (fun y => generatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ t)) 0 φ y) x +
        s103nQ d s (ρ' t) φ x := by
    funext x
    rw [hdw x, s103n_gen_frozen ρ t (generatorW ((quadraticGradientDyn d s a β).coeff ρ) t φ) x]
    congr 2
  have hg5 := hK5 Aρ Ad hAρ0 hAd0 (ρ t) (ρ' t) α (hclass t ht).1
    (by have := (hclass t ht).2
        exact ⟨this.1.of_le (by exact_mod_cast (by omega : 8 * d + 81 ≤ 8 * d + 83)),
          fun m hm => this.2 m (by omega)⟩)
  have h5 := hC5 ρ hG hZ' _ _ (hfun ▸ hg5) t ht
  have hm5 : C5 * (K5 * (1 + Aρ) ^ 2 * (1 + Ad) * s103_b d α) ≤
      max C1234 (C5 * (K5 * (1 + Aρ) ^ 2 * (1 + Ad))) * s103_b d α := by
    calc C5 * (K5 * (1 + Aρ) ^ 2 * (1 + Ad) * s103_b d α) =
        (C5 * (K5 * (1 + Aρ) ^ 2 * (1 + Ad))) * s103_b d α := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hb0
  exact ⟨s103_orbitSup_mono c1 hm1, s103_orbitGrad_mono c2 hm1, s103_orbitSup_mono c3 hm1,
    s103_orbitGrad_mono c4 hm1, s103_orbitSup_mono h5 hm5⟩

end HRS.MS.R2WinOrbNL

end

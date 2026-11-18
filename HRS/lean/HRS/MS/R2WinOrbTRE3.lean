import HRS.MS.R2WinOrbTRE2

/-!
# S10.3 packet [C], assembly part 3: `S103nTermReg` for a SMALL `ε_*`, and the tie `R2WinOrbED13`

Prefix `s103d_`, namespace `HRS.MS.R2WinOrbNL`.

* `s103dL d s`: the weight exponent `d + (9d+91) + ⌈s⌉ + 5`.
* `S103cRhoPrimeUCsmall`: the single residual hypothesis (pending decision, see HANDOFF): for the thermal equilibrium and every `c₁, C₁` there is `ε₀ > 0` such that for all
  `0 < ε_* ≤ ε₀` the right derivative `ρ'` of every trajectory of the class is continuous in time into the weighted `C^{8d+81}` norm (`S103cRhoPrimeUC`).
* `s103d_termReg_small`: for `c₁, C₁` there is `ε₁ > 0` such that for all `0 < ε_* ≤ ε₁` (and `S103cRhoPrimeUC` at `ε_*`) the orbit regularity `S103nTermReg d s a β ρβ ε_* c₁ C₁` holds.
  (The statement of `s103n_tie_of_termReg`, with `S103nTermReg` for ALL `ε_*`, is not provable: it needs the small class.)
* `s103d_tie`: `R2WinOrbED13 d s a β T` from `S103cRhoPrimeUCsmall` (the proof of `s103n_tie`, with `ε_*` replaced by `min` of the orbit-claim radius and `ε₁, ε₀`).
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.R2WinOrbNL

open HRS HRS.Whole HRS.MS.Wad HRS.MS.Ul HRS.MS.Who HRS.MS.BreakdownS67 HRS.MS.MovLin HRS.MS.R2WinOrb
  HRS.MS.MovOsc HRS.MS.Mov63 HRS.MS.MovAdj

variable {d : ℕ}

/-- The weight exponent used for the time-regularity assembly. -/
def s103dL (d : ℕ) (s : ℝ) : ℕ := d + (9 * d + 91) + ⌈s⌉₊ + 5

theorem s103dL_spec (d : ℕ) {s : ℝ} (hs0 : 0 ≤ s) :
    (d : ℝ) + ((9 * d + 91 : ℕ) : ℝ) + s + 3 < (s103dL d s : ℝ) := by
  have : s ≤ (⌈s⌉₊ : ℝ) := Nat.le_ceil s
  unfold s103dL
  push_cast
  linarith

set_option maxHeartbeats 6400000 in
theorem s103d_termReg_small {s a β : ℝ} {ρβ : Euc d → ℝ} (H : Mov2dTh d s β a ρβ) (c₁ C₁ : ℝ) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ εstar : ℝ, 0 < εstar → εstar ≤ ε₁ →
      S103cRhoPrimeUC d s a β ρβ εstar c₁ C₁ (8 * d + 80 + 1) (s103dL d s) →
      S103nTermReg d s a β ρβ εstar c₁ C₁ := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  by_cases hc₁ : 0 < c₁
  swap
  · exact ⟨1, one_pos, fun εstar _ _ _ ε ψ ρ _ hres => absurd hres.cpos hc₁⟩
  set Lnat : ℕ := s103dL d s with hLnatdef
  have hLnat := s103dL_spec d H.hs0
  obtain ⟨Rw, hRw, hZ⟩ := s103n_zeroth H
  obtain ⟨Rstar, Cg', cg', hRstar, hCg'1, hcg', hRad⟩ := s103c_radius H (8 * d + 83) (by omega)
  have hK : ((9 * d + 92 : ℕ) : ℝ) + d / 2 + 4 < ((102 * d + 1020 : ℕ) : ℝ) := by push_cast; linarith
  obtain ⟨εs, r, hεs, hr, hr1, hrRs, hCε, ⟨Cg, cg, hCg, hcg, hGrad⟩, hSch⟩ :=
    s103n_setup2 H (min Rw Rstar) (lt_min hRw hRstar) (9 * d + 92) hK c₁ C₁ hc₁
  have hrRw : r ≤ Rw := hrRs.trans (min_le_left _ _)
  have hrRstar : r ≤ Rstar := hrRs.trans (min_le_right _ _)
  obtain ⟨Cz, hCz0, hZr⟩ := hZ r c₁ Cg cg hr.le hrRw hr1 hc₁.le hcg (by linarith)
  obtain ⟨C5, hC50, hC5⟩ := s103n_orbitSup_of_bd H (by linarith : 0 ≤ Cg) hcg hCz0
  obtain ⟨CKL, hCKL⟩ := hSch Lnat
  obtain ⟨Aβ, hAβ0, hAβ⟩ := s103n_rho_u2dec H (9 * d + 92) Lnat
  set Ad : ℝ := 2 ^ Lnat * |CKL| with hAd
  set Aρ : ℝ := Aβ + Ad with hAρ
  have hAd0 : 0 ≤ Ad := by positivity
  have hAρ0 : 0 ≤ Aρ := by positivity
  refine ⟨εs, hεs, fun εstar hεpos hεle hUC ε ψ ρ hψ hres α hex T0 hT0 => ?_⟩
  have hψ' := s103c_adm_mono hψ hεle
  have hres' := s103c_res_mono hres hεpos hεle
  have hsm := s103n_small_class hres' hCε
  have hG : S103nGrad d s a β ρβ ρ Cg cg := hGrad _ ρ hsm
  have hZ' : S103nZero d s a β ρβ ρ Cz := fun T φ f Bφ hT hf hφ1 hosc hfin hφB r' hr' x =>
    hZr _ ρ hsm hG T φ f Bφ hT hf hφ1 hosc hfin hφB r' hr' x
  have hGc : S103cGrad d s a β ρβ ρ (8 * d + 83) (8 * d + 83 + d + 6) Cg' cg' :=
    hRad r c₁ hr.le hrRstar hc₁.le _ ρ hsm
  obtain ⟨ρ', hder, hcls⟩ := hCKL ε ψ ρ hψ' hres'
  have hclass : ∀ τ : ℝ, 0 ≤ τ → U2Dec (9 * d + 92) (Lnat : ℝ) Aρ (ρ τ) ∧
      U2Dec (9 * d + 92) (Lnat : ℝ) Ad (ρ' τ) := by
    intro τ hτ
    obtain ⟨h1, h2, h3⟩ := hcls τ hτ
    exact hAβ |CKL| ρ ρ' τ hτ h1 h2 (fun k hk x => (h3 k hk x).trans (le_abs_self _))
  have hmcls : (d : ℝ) / 2 + 2 < ((102 * d + 1020 : ℕ) : ℝ) := by push_cast; linarith
  have hcont : ∀ y, ContinuousOn (fun τ => ρ τ y) (Set.Ici 0) := fun y => s103n_cont_time H hmcls hsm y
  have hUC' := hUC ε ψ ρ ρ' hψ hres hder ⟨Ad, fun t ht =>
    ult_U2Dec_mono (hclass t ht).2 (by omega : 8 * d + 80 + 1 ≤ 9 * d + 92)⟩
  obtain ⟨Kφ, hKφ0, hKφ⟩ := s103c_phi_syn3 (d := d) (9 * d + 93) (by omega)
  exact s103d_core H Lnat hLnat ρ ρ' Aρ Ad hAρ0 hAd0 (fun τ hτ => (hclass τ hτ).1)
    (fun τ hτ => (hclass τ hτ).2) hder hcont hUC' (by linarith : 0 ≤ Cg') hcg' hGc hC50
    (fun g A' hg t ht => hC5 ρ hG hZ' g A' hg t ht) (hKφ α) hex T0 hT0

/-- The residual hypothesis of the final tie (pending decision): the time continuity of `ρ'` in the weighted norm, for small `ε_*`. -/
def S103cRhoPrimeUCsmall (d : ℕ) (s a β : ℝ) : Prop :=
  ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ∀ c₁ C₁ : ℝ, ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ εstar : ℝ, 0 < εstar → εstar ≤ ε₀ →
      S103cRhoPrimeUC d s a β ρβ εstar c₁ C₁ (8 * d + 80 + 1) (s103dL d s)

theorem s103d_orbits_mono {s a β : ℝ} {ρβ : Euc d → ℝ} {e1 e2 c₁ C₁ C c : ℝ} (he2 : 0 < e2) (he : e2 ≤ e1)
    (h : S103nOrbitClaims d s a β ρβ e1 c₁ C₁ C c) : S103nOrbitClaims d s a β ρβ e2 c₁ C₁ C c :=
  fun ε ψ ρ hψ hres => h ε ψ ρ (s103c_adm_mono hψ he) (s103c_res_mono hres he2 he)

theorem s103d_tie (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < d) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β)
    (T : ℝ) (hT : 0 < T) (hUCs : S103cRhoPrimeUCsmall d s a β) :
    R2WinOrbED13 d s a β T := by
  obtain ⟨Cs, cs, hcs, hsum, hstat⟩ := s103_stationary hd s hs0 hs a β ha hβ T hT
  intro c₁ C₁
  by_cases hex : ∃ ρ0 : Euc d → ℝ, IsThermalEquilibrium d s a β ρ0
  swap
  · exact ⟨1, one_pos, 1, 1, one_pos, hsum, fun ρβ hρ => absurd ⟨ρβ, hρ⟩ hex⟩
  obtain ⟨ρ0, hρ0⟩ := hex
  have H : Mov2dTh d s β a ρ0 := ⟨hd, hs0, hs, hβ, ha, hρ0⟩
  obtain ⟨εo, hεo, C, c, hc, hOrb⟩ := s103n_orbits_nonlinear' H c₁ C₁
  by_cases hc₁ : 0 < c₁
  swap
  · -- no resulting solutions: the nonlinear clauses are vacuous
    have huniq : ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ρβ = ρ0 := fun ρβ hρ => by
      rw [HRS.MS.Mov0.mv0_rho_eq hd hs0 hs ha hβ hρ, HRS.MS.Mov0.mv0_rho_eq hd hs0 hs ha hβ hρ0]
    refine ⟨εo, hεo, max (max Cs C) 0, min cs c, lt_min hcs hc, hsum, ?_⟩
    intro ρβ hρβ ρ hρ α
    obtain rfl := huniq ρβ hρβ
    intro Cf bα φ
    have hb0 : 0 ≤ bα := s103_b_nonneg (d := d) α
    have hCm : 0 ≤ max (max Cs C) 0 * bα := mul_nonneg (le_max_right _ _) hb0
    rcases hρ with rfl | ⟨ε, ψ, hψ, hres'⟩
    · obtain ⟨h1, h2⟩ := hstat ρβ hρβ α
      have hm : Cs * bα ≤ max (max Cs C) 0 * bα :=
        mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_left _ _)) hb0
      refine ⟨fun t ht => ?_, fun hex b hb n => ?_⟩
      · obtain ⟨c1, c2, c3, c4, c5⟩ := h1 t ht
        refine ⟨s103_orbitSup_mono c1 hm, s103n_orbitGrad_mono_c (s103_orbitGrad_mono c2 hm) (min_le_left _ _) hCm,
          s103_orbitSup_mono c3 hm, s103n_orbitGrad_mono_c (s103_orbitGrad_mono c4 hm) (min_le_left _ _) hCm, ?_⟩
        refine s103_orbitSup_mono ?_ hm
        have e : (fun x => generatorW Cf t (generatorW Cf t φ) x +
            derivWithin (fun t' => generatorW Cf t' φ x) (Set.Ici t) t) =
            fun x => generatorW Cf t (generatorW Cf t φ) x + deriv (fun t' => generatorW Cf t' φ x) t := by
          funext x; rw [s103n_derivWithin_stationary]
        rw [e]; exact c5
      · obtain ⟨w1, w2⟩ := h2 hex b hb n
        refine ⟨w1, w2.trans ?_⟩
        have hx : 0 ≤ (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) := by positivity
        calc Cs * (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) * bα ≤
            max (max Cs C) 0 * (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) * bα := by
              gcongr; exact (le_max_left _ _).trans (le_max_left _ _)
          _ = _ := rfl
    · exact absurd hres'.cpos hc₁
  obtain ⟨ε₁, hε₁, hTR⟩ := s103d_termReg_small H c₁ C₁
  obtain ⟨ε₀, hε₀, hUC0⟩ := hUCs ρ0 hρ0 c₁ C₁
  set εf : ℝ := min εo (min ε₁ ε₀) with hεf
  have hεf0 : 0 < εf := lt_min hεo (lt_min hε₁ hε₀)
  have hεfo : εf ≤ εo := min_le_left _ _
  have hεf1 : εf ≤ ε₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hεf2 : εf ≤ ε₀ := (min_le_right _ _).trans (min_le_right _ _)
  have hOrbf : S103nOrbitClaims d s a β ρ0 εf c₁ C₁ C c := s103d_orbits_mono hεf0 hεfo hOrb
  have hTRf : S103nTermReg d s a β ρ0 εf c₁ C₁ := hTR εf hεf0 hεf1 (hUC0 εf hεf0 hεf2)
  have hWc : S103nWindowClause d s a β T ρ0 εf c₁ C₁ := s103n_windowClause_of_termReg hT hOrbf hTRf
  obtain ⟨Cw, hCw⟩ := hWc
  have huniq : ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ρβ = ρ0 := fun ρβ hρ => by
    rw [HRS.MS.Mov0.mv0_rho_eq hd hs0 hs ha hβ hρ, HRS.MS.Mov0.mv0_rho_eq hd hs0 hs ha hβ hρ0]
  refine ⟨εf, hεf0, max (max (max Cs C) Cw) 0, min cs c, lt_min hcs hc, hsum, ?_⟩
  · intro ρβ hρβ ρ hρ α
    obtain rfl := huniq ρβ hρβ
    intro Cf bα φ
    have hb0 : 0 ≤ bα := s103_b_nonneg (d := d) α
    have hCm : 0 ≤ max (max (max Cs C) Cw) 0 * bα := mul_nonneg (le_max_right _ _) hb0
    rcases hρ with rfl | ⟨ε, ψ, hψ, hres'⟩
    · obtain ⟨h1, h2⟩ := hstat ρβ hρβ α
      have hm : Cs * bα ≤ max (max (max Cs C) Cw) 0 * bα :=
        mul_le_mul_of_nonneg_right (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _)) hb0
      refine ⟨fun t ht => ?_, fun hex b hb n => ?_⟩
      · obtain ⟨c1, c2, c3, c4, c5⟩ := h1 t ht
        refine ⟨s103_orbitSup_mono c1 hm, s103n_orbitGrad_mono_c (s103_orbitGrad_mono c2 hm) (min_le_left _ _) hCm,
          s103_orbitSup_mono c3 hm, s103n_orbitGrad_mono_c (s103_orbitGrad_mono c4 hm) (min_le_left _ _) hCm, ?_⟩
        refine s103_orbitSup_mono ?_ hm
        have e : (fun x => generatorW Cf t (generatorW Cf t φ) x +
            derivWithin (fun t' => generatorW Cf t' φ x) (Set.Ici t) t) =
            fun x => generatorW Cf t (generatorW Cf t φ) x + deriv (fun t' => generatorW Cf t' φ x) t := by
          funext x; rw [s103n_derivWithin_stationary]
        rw [e]; exact c5
      · obtain ⟨w1, w2⟩ := h2 hex b hb n
        refine ⟨w1, w2.trans ?_⟩
        have hx : 0 ≤ (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) := by positivity
        calc Cs * (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) * bα ≤
            max (max (max Cs C) Cw) 0 * (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) * bα := by
              gcongr; exact ((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _)
          _ = _ := rfl
    · have hm : C * bα ≤ max (max (max Cs C) Cw) 0 * bα :=
        mul_le_mul_of_nonneg_right (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _)) hb0
      refine ⟨fun t ht => ?_, fun hex b hb n => ?_⟩
      · obtain ⟨c1, c2, c3, c4, c5⟩ := hOrbf ε ψ _ hψ hres' α t ht
        exact ⟨s103_orbitSup_mono c1 hm, s103n_orbitGrad_mono_c (s103_orbitGrad_mono c2 hm) (min_le_right _ _) hCm,
          s103_orbitSup_mono c3 hm, s103n_orbitGrad_mono_c (s103_orbitGrad_mono c4 hm) (min_le_right _ _) hCm,
          s103_orbitSup_mono c5 hm⟩
      · obtain ⟨w1, w2⟩ := hCw ε ψ _ hψ hres' α hex b hb n
        refine ⟨w1, w2.trans ?_⟩
        have hx : 0 ≤ (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) := by positivity
        calc Cw * (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) * bα ≤
            max (max (max Cs C) Cw) 0 * (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) * bα := by
              gcongr; exact (le_max_right _ _).trans ((le_max_left _ _))
          _ = _ := rfl

end HRS.MS.R2WinOrbNL

end

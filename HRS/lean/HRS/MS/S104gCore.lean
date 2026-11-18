import HRS.MS.S104gLv2

/-!
# S10.4 packet S104G, part 7: the orbit family at a general initial time (`S104gOrbit`)

Prefix `s104g_`, namespace `HRS.MS.R2WinOrbNL`.

`S104gOrbit Cf φ T0` is the conjunction of the three clauses of `S104bTermRegGen` (existence of the classical adjoint solutions for the three data, the `C^j` difference quotients
of `U(r,t) D_a(t)` at every initial time `r ≤ t`, and the joint continuity of `∇U(r,t)L_tφ`).
`s104g_prop_eq`: a classical adjoint solution with datum in `Bd N0` is `propagatorW` (uniqueness from the stability bound).
`s104g_core`: `s103d_core` at a general initial time: for a FIXED trajectory (the hypotheses of `s103d_core`) `S104gOrbit Cf φ T0` holds.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.R2WinOrbNL

open HRS HRS.Whole HRS.MS.Wad HRS.MS.Ul HRS.MS.Who HRS.MS.BreakdownS67 HRS.MS.MovLin HRS.MS.R2WinOrb
  HRS.MS.MovOsc

variable {d : ℕ}

/-- The three clauses of `S104bTermRegGen` for a fixed coefficient, test function and horizon. -/
def S104gOrbit (Cf : WholeCoeff d) (φ : Euc d → ℝ) (T0 : ℝ) : Prop :=
  (∀ a' : Fin 3, ∀ t ∈ Set.Icc (0 : ℝ) T0, ∃ f : ℝ → Euc d → ℝ,
    IsClassicalAdjointW Cf t (s103nData Cf φ a' t) f) ∧
  (∀ a' : Fin 3, ∀ ha2 : (a' : ℕ) < 2, ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T0 → ∀ e : ℝ, 0 < e → ∃ δ : ℝ, 0 < δ ∧
    ∀ h : ℝ, h ≠ 0 → |h| < δ → r ≤ t + h → t + h ≤ T0 → ∀ j ≤ 4 * d + 42, ∀ x : Euc d,
      ‖iteratedFDeriv ℝ j (fun y => h⁻¹ * (propagatorW Cf r (t + h) (s103nData Cf φ a' (t + h)) y -
        propagatorW Cf r t (s103nData Cf φ a' t) y) -
        propagatorW Cf r t (s103nData Cf φ ⟨(a' : ℕ) + 1, by omega⟩ t) y) x‖ ≤ e) ∧
  ContinuousOn (fun q : ℝ × ℝ × Euc d => gradient (propagatorW Cf q.2.1 q.1 (generatorW Cf q.1 φ)) q.2.2)
    {q : ℝ × ℝ × Euc d | 0 ≤ q.2.1 ∧ q.2.1 ≤ q.1 ∧ q.1 ≤ T0}

theorem s104g_prop_eq {s a β : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {L A : ℝ} (hL : (d : ℝ) < L)
    {ρ : ℝ → Euc d → ℝ} {N0 : ℕ} {Cs : ℝ} (hCs : 0 ≤ Cs)
    (hStab : ∀ (g : Euc d → ℝ) (A' : ℝ), Bd N0 A' g → ∀ t : ℝ, 0 ≤ t →
      R2OrbitSup ((quadraticGradientDyn d s a β).coeff ρ) (4 * d + 42) t g (Cs * A'))
    {τ : ℝ} (hτ : 0 ≤ τ) (hρ : ∀ σ ∈ Set.Icc (0 : ℝ) τ, U2Dec 1 L A (ρ σ))
    {g : Euc d → ℝ} {A' : ℝ} (hg : Bd N0 A' g) {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff ρ) τ g f) :
    ∀ r ∈ Set.Icc (0 : ℝ) τ, propagatorW ((quadraticGradientDyn d s a β).coeff ρ) r τ g = f r := by
  intro r hr
  have hex : ∃ f, IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff ρ) τ g f := ⟨f, hf⟩
  have e : propagatorW ((quadraticGradientDyn d s a β).coeff ρ) r τ g = hex.choose r := by
    unfold propagatorW; rw [dif_pos hex]
  rw [e]
  exact s104g_unique hd hs0 hsd hL hCs hStab hτ hρ hg hex.choose_spec hf r hr

theorem s104g_dq_of {Cf : WholeCoeff d} {φ : Euc d → ℝ} {T0 : ℝ} (a' : Fin 3) (ha2 : (a' : ℕ) < 2)
    (G H : ℝ → ℝ → Euc d → ℝ)
    (hG : ∀ t : ℝ, 0 ≤ t → t ≤ T0 → ∀ r ∈ Set.Icc (0 : ℝ) t, propagatorW Cf r t (s103nData Cf φ a' t) = G t r)
    (hH : ∀ t : ℝ, 0 ≤ t → t ≤ T0 → ∀ r ∈ Set.Icc (0 : ℝ) t,
      propagatorW Cf r t (s103nData Cf φ ⟨(a' : ℕ) + 1, by omega⟩ t) = H t r)
    (hc : ∀ t : ℝ, 0 ≤ t → t ≤ T0 → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, h ≠ 0 → |h| < δ →
      0 ≤ t + h → t + h ≤ T0 → ∀ r : ℝ, 0 ≤ r → r ≤ t → r ≤ t + h → ∀ j ≤ 4 * d + 42, ∀ x : Euc d,
        ‖iteratedFDeriv ℝ j (fun y => h⁻¹ * (G (t + h) r y - G t r y) - H t r y) x‖ ≤ ε) :
    ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T0 → ∀ e : ℝ, 0 < e → ∃ δ : ℝ, 0 < δ ∧
      ∀ h : ℝ, h ≠ 0 → |h| < δ → r ≤ t + h → t + h ≤ T0 → ∀ j ≤ 4 * d + 42, ∀ x : Euc d,
        ‖iteratedFDeriv ℝ j (fun y => h⁻¹ * (propagatorW Cf r (t + h) (s103nData Cf φ a' (t + h)) y -
          propagatorW Cf r t (s103nData Cf φ a' t) y) -
          propagatorW Cf r t (s103nData Cf φ ⟨(a' : ℕ) + 1, by omega⟩ t) y) x‖ ≤ e := by
  intro r t hr hrt htT e he
  obtain ⟨δ, hδ, hh⟩ := hc t (hr.trans hrt) htT e he
  refine ⟨δ, hδ, fun h hne hhδ hrth hthT j hj x => ?_⟩
  have := hh h hne hhδ (hr.trans hrth) hthT r hr hrt hrth j hj x
  rwa [← hG (t + h) (hr.trans hrth) hthT r ⟨hr, hrth⟩, ← hG t (hr.trans hrt) htT r ⟨hr, hrt⟩,
    ← hH t (hr.trans hrt) htT r ⟨hr, hrt⟩] at this

set_option maxHeartbeats 6400000 in
theorem s104g_core {s a β : ℝ} {ρβ : Euc d → ℝ} (H : Mov2dTh d s β a ρβ) (Lnat : ℕ)
    (hLnat : (d : ℝ) + ((9 * d + 91 : ℕ) : ℝ) + s + 3 < (Lnat : ℝ))
    (ρ ρ' : ℝ → Euc d → ℝ) (Aρ Ad : ℝ) (hAρ : 0 ≤ Aρ) (hAd : 0 ≤ Ad)
    (hρU : ∀ τ : ℝ, 0 ≤ τ → U2Dec (9 * d + 92) (Lnat : ℝ) Aρ (ρ τ))
    (hρ'U : ∀ τ : ℝ, 0 ≤ τ → U2Dec (9 * d + 92) (Lnat : ℝ) Ad (ρ' τ))
    (hder : ∀ τ : ℝ, 0 ≤ τ → ∀ x, HasDerivWithinAt (fun σ => ρ σ x) (ρ' τ x) (Set.Ici τ) τ)
    (hcont : ∀ x, ContinuousOn (fun σ => ρ σ x) (Set.Ici 0))
    (hUC : ∀ t : ℝ, 0 ≤ t → ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∀ σ : ℝ, 0 ≤ σ → |σ - t| < η →
      U2Dec (8 * d + 80 + 1) (Lnat : ℝ) ε (fun y => ρ' σ y - ρ' t y))
    {Cg cg : ℝ} (hCg : 0 ≤ Cg) (hcg : 0 < cg)
    (hGrad : S103cGrad d s a β ρβ ρ (8 * d + 83) (8 * d + 83 + d + 6) Cg cg)
    {Cs : ℝ} (hCs : 0 ≤ Cs)
    (hStab : ∀ (g : Euc d → ℝ) (A' : ℝ), Bd (8 * d + 80) A' g → ∀ t : ℝ, 0 ≤ t →
      R2OrbitSup ((quadraticGradientDyn d s a β).coeff ρ) (4 * d + 42) t g (Cs * A'))
    {φ : Euc d → ℝ} {Aφ : ℝ} (hφ : SyN 3 (9 * d + 93) Aφ φ)
    (hex : ∀ t : ℝ, 0 ≤ t → ∃ f : ℝ → Euc d → ℝ,
      IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff ρ) t φ f)
    (T0 : ℝ) (hT0 : 0 ≤ T0) :
    S104gOrbit ((quadraticGradientDyn d s a β).coeff ρ) φ T0 := by
  have hd := H.hd
  have hs0 := H.hs0
  have hsd := H.hsd
  have ha := H.hq
  have hβ := H.hβ
  set Cf := (quadraticGradientDyn d s a β).coeff ρ with hCf
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hLn : ∀ n : ℕ, n ≤ 9 * d + 91 → (d : ℝ) + (n : ℝ) + s + 3 < (Lnat : ℝ) := by
    intro n hn
    have : (n : ℝ) ≤ ((9 * d + 91 : ℕ) : ℝ) := by exact_mod_cast hn
    linarith
  have hdL : (d : ℝ) < (Lnat : ℝ) := by
    have := hLn 0 (by omega)
    push_cast at this
    linarith
  have hU1 : ∀ τ : ℝ, 0 ≤ τ → U2Dec 1 (Lnat : ℝ) Aρ (ρ τ) := fun τ hτ =>
    ult_U2Dec_mono (hρU τ hτ) (by omega)
  have hD1' : ∀ τ : ℝ, 0 ≤ τ → U2Dec 1 (Lnat : ℝ) Ad (ρ' τ) := fun τ hτ =>
    ult_U2Dec_mono (hρ'U τ hτ) (by omega)
  obtain ⟨u1, hu1cl, hconv1, ⟨A1, hA1⟩, M, hM0, hMl⟩ := s104g_level1 H Lnat hLnat ρ ρ' Aρ Ad hAρ hAd hρU hρ'U hder hcont
    hCg hcg hGrad hCs hStab hφ hex (T0 + 2) (by linarith)
  obtain ⟨u2, hu2cl, hconv2, ⟨A2, hA2⟩, G3, hG30, hj3⟩ := s104g_level2 H Lnat hLnat ρ ρ' Aρ Ad hAρ hAd hρU hρ'U hder hcont
    hUC hCg hcg hGrad hCs hStab hφ (T0 + 1) (by linarith) u1 (fun l hl0 hl1 => hu1cl l hl0 (by linarith))
  have hP1 : ∀ t : ℝ, 0 ≤ t → t ≤ T0 → ∀ r ∈ Set.Icc (0 : ℝ) t,
      propagatorW Cf r t (generatorW Cf t φ) = u1 t r := fun t ht0 htT r hr =>
    s104g_prop_eq hd hs0 hsd hdL hCs hStab ht0 (fun σ hσ => hU1 σ hσ.1) (hA1 t ht0)
      (hu1cl t ht0 (by linarith)) r hr
  have hP2 : ∀ t : ℝ, 0 ≤ t → t ≤ T0 → ∀ r ∈ Set.Icc (0 : ℝ) t,
      propagatorW Cf r t (fun y => generatorW Cf t (fun x => generatorW Cf t φ x) y + s103nQ d s (ρ' t) φ y) =
        u2 t r := fun t ht0 htT r hr =>
    s104g_prop_eq hd hs0 hsd hdL hCs hStab ht0 (fun σ hσ => hU1 σ hσ.1) (hA2 t ht0)
      (hu2cl t ht0 (by linarith)) r hr

  have hn : ∀ i : Fin d, ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖ = 1 := fun i => by simp
  have hφ2 : ContDiff ℝ 2 φ := by
    have := hφ.1.of_le (show ((2 : ℕ) : WithTop ℕ∞) ≤ ((9 * d + 93 : ℕ) : WithTop ℕ∞) by
      exact_mod_cast (by omega))
    exact_mod_cast this
  have hDg : ∀ i : Fin d, Bd 1 Aφ (fun y => fderiv ℝ φ y (EuclideanSpace.single i (1 : ℝ))) := fun i => by
    have h := ((hφ.deriv (N := 9 * d + 92) (EuclideanSpace.single i (1 : ℝ))).bd).mono_N
      (show 1 ≤ 9 * d + 92 by omega)
    rw [hn i, mul_one] at h
    exact h
  have hdw : ∀ t : ℝ, 0 ≤ t → ∀ x, derivWithin (fun t' => generatorW Cf t' φ x) (Set.Ici t) t =
      s103nQ d s (ρ' t) φ x := fun t ht x =>
    s103n_derivWithin_gen (a := a) (β := β) hd hs0 hsd hdL hAρ hAd ρ ρ' t ht hU1 hD1' hder hcont hφ2 hDg x
  have hD2 : ∀ t : ℝ, 0 ≤ t → s103nData Cf φ 2 t =
      fun y => generatorW Cf t (fun x => generatorW Cf t φ x) y + s103nQ d s (ρ' t) φ y := by
    intro t ht
    funext y
    show generatorW Cf t (generatorW Cf t φ) y + derivWithin (fun t' => generatorW Cf t' φ y) (Set.Ici t) t = _
    rw [hdw t ht y]
  have hD1 : ∀ t : ℝ, s103nData Cf φ 1 t = generatorW Cf t φ := fun t => rfl
  refine ⟨?_, ?_, ?_⟩
  · intro a' t ht
    fin_cases a'
    · exact hex t ht.1
    · exact ⟨u1 t, hu1cl t ht.1 (by linarith [ht.2])⟩
    · refine ⟨u2 t, ?_⟩
      show IsClassicalAdjointW Cf t (s103nData Cf φ 2 t) (u2 t)
      rw [hD2 t ht.1]
      exact hu2cl t ht.1 (by linarith [ht.2])
  · intro a' ha2
    fin_cases a'
    · refine s104g_dq_of (Cf := Cf) (φ := φ) (T0 := T0) _ ha2 (fun t r => propagatorW Cf r t φ) u1
        (fun t ht0 htT r hr => rfl)
        (fun t ht0 htT r hr => hP1 t ht0 htT r hr)
        (fun t ht0 htT ε hε => ?_)
      obtain ⟨δ, hδ, hh⟩ := hconv1 t ht0 (by linarith) ε hε
      exact ⟨δ, hδ, fun h hne hhδ h1 h2 r hr0 hrt hrth j hj x => hh h hne hhδ h1 (by linarith) r hr0 hrt hrth j hj x⟩
    · refine s104g_dq_of (Cf := Cf) (φ := φ) (T0 := T0) _ ha2 u1 u2
        (fun t ht0 htT r hr => hP1 t ht0 htT r hr)
        (fun t ht0 htT r hr => by
          show propagatorW Cf r t (s103nData Cf φ 2 t) = u2 t r
          rw [hD2 t ht0]; exact hP2 t ht0 htT r hr)
        (fun t ht0 htT ε hε => ?_)
      obtain ⟨δ, hδ, hh⟩ := hconv2 t ht0 (by linarith) ε hε
      exact ⟨δ, hδ, fun h hne hhδ h1 h2 r hr0 hrt hrth j hj x => hh h hne hhδ h1 (by linarith) r hr0 hrt hrth j hj x⟩
    · exact absurd ha2 (by norm_num)
  · have hjc := s104g_jcont (C := Cf) (u1 := u1) (u2 := u2) (T0 := T0) (Gb := G3) (M := M) hG30 hM0
      (fun t ht => ⟨_, hu1cl t ht.1 (by linarith [ht.2])⟩)
      (fun t ht r hr => (hj3 t ht.1 (by linarith [ht.2]) r hr).1)
      (fun r t hr hrt htT e he => by
        obtain ⟨δ, hδ, hh⟩ := hconv2 t (hr.trans hrt) (by linarith) e he
        exact ⟨δ, hδ, fun h hne hhδ hrth hthT x =>
          hh h hne hhδ (hr.trans hrth) (by linarith) r hr hrt hrth 1 (by omega) x⟩)
      (fun t ht r hr x => (hj3 t ht.1 (by linarith [ht.2]) r hr).2 x)
      (fun t ht r hr x => (hMl t ht.1 (by linarith [ht.2]) r hr).2 1 (by omega) x)
    refine hjc.congr fun q hq => ?_
    obtain ⟨hq1, hq2, hq3⟩ := hq
    show gradient (propagatorW Cf q.2.1 q.1 (generatorW Cf q.1 φ)) q.2.2 = gradient (u1 q.1 q.2.1) q.2.2
    rw [hP1 q.1 (hq1.trans hq2) hq3 q.2.1 ⟨hq1, hq2⟩]

end HRS.MS.R2WinOrbNL

end

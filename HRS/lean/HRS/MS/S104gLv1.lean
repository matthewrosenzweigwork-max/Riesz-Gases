import HRS.MS.S104gJc3

/-!
# S10.4 packet S104G, part 5: level 1 of the orbit family at a general initial time

Prefix `s104g_`, namespace `HRS.MS.R2WinOrbNL`.

`s104g_level1` is the level-1 half of `s103d_core` with the initial time `r` general: for a fixed trajectory `ρ` (hypotheses of `s103d_core`) and a horizon `T1`,
there is `u1 t r` (`0 ≤ t < T1`) such that `u1 t` is a classical adjoint solution with terminal datum `L_tφ`, the difference quotients
`h⁻¹ (U(r,t+h)φ - U(r,t)φ)` converge to `u1 t r` in every `C^j` sup norm (`j ≤ 4d+42`) for every `0 ≤ r ≤ min t (t+h)`, and the data `L_tφ` lie in `Bd (8d+80) A1`, and `u1 t` is Lipschitz in `r`
towards its terminal value in the `Bd (8d+80)` norm with a constant independent of `t`.
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

set_option maxHeartbeats 6400000 in
theorem s104g_level1 {s a β : ℝ} {ρβ : Euc d → ℝ} (H : Mov2dTh d s β a ρβ) (Lnat : ℕ)
    (hLnat : (d : ℝ) + ((9 * d + 91 : ℕ) : ℝ) + s + 3 < (Lnat : ℝ))
    (ρ ρ' : ℝ → Euc d → ℝ) (Aρ Ad : ℝ) (hAρ : 0 ≤ Aρ) (hAd : 0 ≤ Ad)
    (hρU : ∀ τ : ℝ, 0 ≤ τ → U2Dec (9 * d + 92) (Lnat : ℝ) Aρ (ρ τ))
    (hρ'U : ∀ τ : ℝ, 0 ≤ τ → U2Dec (9 * d + 92) (Lnat : ℝ) Ad (ρ' τ))
    (hder : ∀ τ : ℝ, 0 ≤ τ → ∀ x, HasDerivWithinAt (fun σ => ρ σ x) (ρ' τ x) (Set.Ici τ) τ)
    (hcont : ∀ x, ContinuousOn (fun σ => ρ σ x) (Set.Ici 0))
    {Cg cg : ℝ} (hCg : 0 ≤ Cg) (hcg : 0 < cg)
    (hGrad : S103cGrad d s a β ρβ ρ (8 * d + 83) (8 * d + 83 + d + 6) Cg cg)
    {Cs : ℝ} (hCs : 0 ≤ Cs)
    (hStab : ∀ (g : Euc d → ℝ) (A' : ℝ), Bd (8 * d + 80) A' g → ∀ t : ℝ, 0 ≤ t →
      R2OrbitSup ((quadraticGradientDyn d s a β).coeff ρ) (4 * d + 42) t g (Cs * A'))
    {φ : Euc d → ℝ} {Aφ : ℝ} (hφ : SyN 3 (9 * d + 93) Aφ φ)
    (hex : ∀ t : ℝ, 0 ≤ t → ∃ f : ℝ → Euc d → ℝ,
      IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff ρ) t φ f)
    (T1 : ℝ) (hT1 : 0 ≤ T1) :
    ∃ u1 : ℝ → ℝ → Euc d → ℝ,
      (∀ t : ℝ, 0 ≤ t → t < T1 → IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff ρ) t
        (generatorW ((quadraticGradientDyn d s a β).coeff ρ) t φ) (u1 t)) ∧
      (∀ t : ℝ, 0 ≤ t → t < T1 → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, h ≠ 0 → |h| < δ →
        0 ≤ t + h → t + h ≤ T1 → ∀ r : ℝ, 0 ≤ r → r ≤ t → r ≤ t + h → ∀ j ≤ 4 * d + 42, ∀ x : Euc d,
          ‖iteratedFDeriv ℝ j (fun y => h⁻¹ * (propagatorW ((quadraticGradientDyn d s a β).coeff ρ) r (t + h) φ y -
            propagatorW ((quadraticGradientDyn d s a β).coeff ρ) r t φ y) - u1 t r y) x‖ ≤ ε) ∧
      (∃ A1 : ℝ, ∀ t : ℝ, 0 ≤ t → Bd (8 * d + 80) A1 (fun y => generatorW ((quadraticGradientDyn d s a β).coeff ρ) t φ y)) ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, 0 ≤ t → t < T1 → ∀ τ ∈ Set.Icc (0 : ℝ) t,
        Bd (8 * d + 80) (M * (t - τ)) (fun y => u1 t τ y - u1 t t y) := by
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
  obtain ⟨G0, hG00, hG0⟩ := s103c_jets_of_bd H (8 * d + 83) hCg hcg (by omega)
  obtain ⟨C2, hC20, hC2⟩ := s103d_data hd hs0 hsd a β (9 * d + 89) (L := (Lnat : ℝ))
    (by have := hLn (9 * d + 89 + 2) (by omega); exact this)
  have hAφ : 0 ≤ Aφ := hφ.bd.nonneg
  set A1 : ℝ := C2 * ((1 + Aρ) * Aφ) with hA1
  set A2 : ℝ := C2 * ((1 + Aρ) ^ 2 * (1 + Ad) * (1 + Aφ)) with hA2
  have hA10 : 0 ≤ A1 := by positivity
  have hA20 : 0 ≤ A2 := by positivity
  have hρ'U2 : ∀ τ : ℝ, 0 ≤ τ → U2Dec (9 * d + 89 + 1) (Lnat : ℝ) Ad (ρ' τ) := fun τ hτ =>
    ult_U2Dec_mono (hρ'U τ hτ) (by omega)
  have hρU2 : ∀ τ : ℝ, 0 ≤ τ → U2Dec (9 * d + 89 + 3) (Lnat : ℝ) Aρ (ρ τ) := fun τ hτ => hρU τ hτ
  have hdat : ∀ τ : ℝ, 0 ≤ τ →
      DatD (9 * d + 89 + 2) A1 (fun y => generatorW Cf τ φ y) ∧
      Sy (9 * d + 89) A2 (fun y => generatorW Cf τ (fun x => generatorW Cf τ φ x) y +
        s103nQ d s (ρ' τ) φ y) := fun τ hτ =>
    hC2 Aρ Ad Aφ hAρ hAd hAφ ρ ρ' τ φ (hρU2 τ hτ) (hρ'U2 τ hτ) hφ
  have hχ1 : ∀ τ : ℝ, 0 ≤ τ → DatD (9 * d + 91) A1 (fun y => generatorW Cf τ φ y) := fun τ hτ =>
    (hdat τ hτ).1
  have hχ2 : ∀ τ : ℝ, 0 ≤ τ → Sy (9 * d + 89) A2 (fun y => generatorW Cf τ (fun x => generatorW Cf τ φ x) y +
        s103nQ d s (ρ' τ) φ y) := fun τ hτ => (hdat τ hτ).2
  have hφD : DatD (9 * d + 93) Aφ φ := (hφ.mono_p (q := 2) (by norm_num)).toDatD
  -- classical solutions of level 0
  have hprop : ∀ l : ℝ, 0 ≤ l → IsClassicalAdjointW Cf l φ (fun r => propagatorW Cf r l φ) := by
    intro l hl
    have h := hex l hl
    have e : (fun r => propagatorW Cf r l φ) = h.choose := by
      funext r; unfold propagatorW; rw [dif_pos h]
    rw [e]; exact h.choose_spec
  set fam0 : ℝ → ℝ → Euc d → ℝ := fun l r => propagatorW Cf r l φ with hfam0def
  have hfam0 : ∀ l : ℝ, 0 ≤ l → IsClassicalAdjointW Cf l φ (fam0 l) := fun l hl => hprop l hl
  have hterm0 : ∀ e : ℝ, 0 ≤ e → ∀ y, fam0 e e y = φ y := fun e he y => congrFun (hfam0 e he).terminal y
  -- jets of the level-0 solutions
  set G1 : ℝ := G0 * Aφ with hG1
  have hG10 : 0 ≤ G1 := by positivity
  have hφBd : Bd (8 * d + 83 + d + 6) Aφ φ := hφ.bd.mono_N (by omega)
  have hj0 : ∀ l ∈ Set.Icc (0 : ℝ) T1, ∀ τ ∈ Set.Icc (0 : ℝ) l,
      ContDiff ℝ ((8 * d + 80 + 4 : ℕ) : WithTop ℕ∞) (fam0 l τ) ∧
        ∀ i, 1 ≤ i → i ≤ 8 * d + 80 + 4 → ∀ y, ‖iteratedFDeriv ℝ i (fam0 l τ) y‖ ≤ G1 := by
    intro l hl τ hτ
    obtain ⟨h1, h2⟩ := hG0 ρ hGrad l φ (fam0 l) Aφ hl.1 hφBd (hfam0 l hl.1) τ hτ
    exact ⟨h1, fun i hi1 hi2 y => h2 i hi1 (by omega) y⟩
  -- the densities
  have hU3 : ∀ τ : ℝ, 0 ≤ τ → U2Dec (8 * d + 80 + 3) (Lnat : ℝ) Aρ (ρ τ) := fun τ hτ =>
    ult_U2Dec_mono (hρU τ hτ) (by omega)
  have hU5 : ∀ τ : ℝ, 0 ≤ τ → U2Dec (8 * d + 80 + 5) (Lnat : ℝ) Aρ (ρ τ) := fun τ hτ =>
    ult_U2Dec_mono (hρU τ hτ) (by omega)
  have hD1 : ∀ τ : ℝ, 0 ≤ τ → U2Dec (8 * d + 80 + 1) (Lnat : ℝ) Ad (ρ' τ) := fun τ hτ =>
    ult_U2Dec_mono (hρ'U τ hτ) (by omega)
  have hD3 : ∀ τ : ℝ, 0 ≤ τ → U2Dec (8 * d + 80 + 3) (Lnat : ℝ) Ad (ρ' τ) := fun τ hτ =>
    ult_U2Dec_mono (hρ'U τ hτ) (by omega)
  have hU1 : ∀ τ : ℝ, 0 ≤ τ → U2Dec 1 (Lnat : ℝ) Aρ (ρ τ) := fun τ hτ =>
    ult_U2Dec_mono (hρU τ hτ) (by omega)
  have hD1' : ∀ τ : ℝ, 0 ≤ τ → U2Dec 1 (Lnat : ℝ) Ad (ρ' τ) := fun τ hτ =>
    ult_U2Dec_mono (hρ'U τ hτ) (by omega)
  -- LEVEL 1: the layer
  obtain ⟨Cl, hCl0, hCl⟩ := s103c_layer1 hd hs0 hsd a β ha hβ (8 * d + 80) Lnat
    (by have := hLn (8 * d + 80 + 2) (by omega); exact this) T1 hT1
  set M1 : ℝ := Cl * (Ad * G1 + (1 + Aρ) * (Aφ + Aρ * G1)) with hM1
  have hM10 : 0 ≤ M1 := by positivity
  have hLay1 : ∀ t ∈ Set.Icc (0 : ℝ) T1, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ e l : ℝ, 0 ≤ e → e < l →
      l ≤ T1 → e ≤ t → t ≤ l → l - e < δ →
      Bd (8 * d + 80) ε (fun y => (fam0 l e y - fam0 e e y) / (l - e) - generatorW Cf t φ y) := by
    refine s103d_hLay_of_lin (fam := fam0) (χ := fun t y => generatorW Cf t φ y) hM10 ?_
    intro t ht e l he hel hlT het htl
    have hl0 : 0 ≤ l := he.trans hel.le
    have P := hCl ρ ρ' Aρ Ad hAρ hAd hU3 hD1 hder hcont φ Aφ (hφD.mono_N (by omega)) G1 l (fam0 l)
      ⟨hl0, hlT⟩ (hfam0 l hl0) (hj0 l ⟨hl0, hlT⟩ ) e t he hel het htl
    have e1 : (fun y => (fam0 l e y - fam0 e e y) / (l - e) - generatorW Cf t φ y) =
        fun y => (fam0 l e y - φ y) / (l - e) - generatorW Cf t φ y :=
      funext fun y => by rw [hterm0 e he y]
    show Bd (8 * d + 80) (M1 * (l - e)) (fun y => (fam0 l e y - fam0 e e y) / (l - e) -
      generatorW Cf t φ y)
    rw [e1]
    exact P
  have hfam0T : ∀ l ∈ Set.Icc (0 : ℝ) T1, IsClassicalAdjointW Cf l (fam0 l l) (fam0 l) := by
    intro l hl
    have h := hfam0 l hl.1
    have e : fam0 l l = φ := funext (hterm0 l hl.1)
    rw [e]; exact h
  have hρ1T : ∀ τ ∈ Set.Icc (0 : ℝ) T1, U2Dec 1 (Lnat : ℝ) Aρ (ρ τ) := fun τ hτ => hU1 τ hτ.1
  have hχ1bd : ∀ t ∈ Set.Icc (0 : ℝ) T1, Bd (8 * d + 80) A1 (fun y => generatorW Cf t φ y) :=
    fun t ht => (hχ1 t ht.1).bd.mono_N (by omega)
  have hstep1 := s103c_step hd hs0 hsd (L := (Lnat : ℝ)) (by have := hLn 0 (by omega); simpa using this)
    hAρ ρ T1 hρ1T (8 * d + 80) Cs hCs hStab fam0 hfam0T (fun t y => generatorW Cf t φ y) A1 hχ1bd hLay1
  have hu1ex : ∀ t : ℝ, 0 ≤ t ∧ t < T1 → ∃ u : ℝ → Euc d → ℝ,
      IsClassicalAdjointW Cf t (generatorW Cf t φ) u := fun t ht => by
    obtain ⟨u, hu, -⟩ := hstep1 t ht.1 ht.2
    exact ⟨u, hu⟩
  choose! u1 hu1cl using hu1ex
  -- time regularity of level 1
  obtain ⟨Kt, hKt0, hKt⟩ := s103c_timereg hd hs0 hsd a β ha hβ (8 * d + 80) (L := (Lnat : ℝ))
    (by have := hLn (8 * d + 80 + 1) (by omega); exact this) T1 hT1
  have hU2 : ∀ τ ∈ Set.Icc (0 : ℝ) T1, U2Dec (8 * d + 80 + 1 + 1) (Lnat : ℝ) Aρ (ρ τ) := fun τ hτ =>
    ult_U2Dec_mono (hρU τ hτ.1) (by omega)
  set G2 : ℝ := G0 * A1 with hG2
  have hG20 : 0 ≤ G2 := by positivity
  have hj1 : ∀ t : ℝ, 0 ≤ t → t < T1 → ∀ τ ∈ Set.Icc (0 : ℝ) t,
      ContDiff ℝ ((8 * d + 80 + 1 + 2 : ℕ) : WithTop ℕ∞) (u1 t τ) ∧
        ∀ i, 1 ≤ i → i ≤ 8 * d + 80 + 1 + 2 → ∀ y, ‖iteratedFDeriv ℝ i (u1 t τ) y‖ ≤ G2 := by
    intro t ht0 htT τ hτ
    obtain ⟨h1, h2⟩ := hG0 ρ hGrad t (fun y => generatorW Cf t φ y) (u1 t) A1 ht0
      ((hχ1 t ht0).bd.mono_N (by omega)) (hu1cl t ⟨ht0, htT⟩) τ hτ
    exact ⟨h1.of_le (by exact_mod_cast (by omega : 8 * d + 80 + 1 + 2 ≤ 8 * d + 83 + 1)),
      fun i hi1 hi2 y => h2 i hi1 (by omega) y⟩
  have htr1 : ∀ t : ℝ, 0 ≤ t → t < T1 → S103cTimeReg (8 * d + 80) t (u1 t) := by
    intro t ht0 htT
    refine s103d_timeReg_of_lin (M := Kt * (A1 + (1 + Aρ) * G2)) (by positivity) ?_
    intro τ hτ
    exact hKt ρ Aρ hAρ hU2 t ⟨ht0, htT.le⟩ (fun y => generatorW Cf t φ y) A1 G2 (u1 t)
      (hu1cl t ⟨ht0, htT⟩) ((hχ1 t ht0).mono_N (by omega : 8 * d + 80 + 1 ≤ 9 * d + 91)).1
      (fun i h1 h2 y => (hχ1 t ht0).decay1 i h1 (by omega) y) (hj1 t ht0 htT) τ hτ
  refine ⟨u1, fun t ht0 htT => hu1cl t ⟨ht0, htT⟩, fun t ht0 htT ε hε => ?_,
    ⟨A1, fun t ht0 => (hχ1 t ht0).bd.mono_N (by omega)⟩,
    Kt * (A1 + (1 + Aρ) * G2), by positivity, fun t ht0 htT τ hτ => ?_⟩
  · exact s104g_conv hd hs0 hsd (L := (Lnat : ℝ)) (by have := hLn 0 (by omega); simpa using this)
      ρ T1 hρ1T (8 * d + 80) Cs hCs hStab fam0 hfam0T (fun t y => generatorW Cf t φ y) A1 hχ1bd hLay1
      ht0 htT (hu1cl t ⟨ht0, htT⟩) (htr1 t ht0 htT) ε hε
  · exact hKt ρ Aρ hAρ hU2 t ⟨ht0, htT.le⟩ (fun y => generatorW Cf t φ y) A1 G2 (u1 t)
      (hu1cl t ⟨ht0, htT⟩) ((hχ1 t ht0).mono_N (by omega : 8 * d + 80 + 1 ≤ 9 * d + 91)).1
      (fun i h1 h2 y => (hχ1 t ht0).decay1 i h1 (by omega) y) (hj1 t ht0 htT) τ hτ

end HRS.MS.R2WinOrbNL

end

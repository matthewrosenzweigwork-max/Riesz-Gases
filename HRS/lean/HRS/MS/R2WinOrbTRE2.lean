import HRS.MS.R2WinOrbTRE1

/-!
# S10.3 packet [C], assembly part 2: the orbit family `F` for a fixed trajectory (`S103nTermReg` core)

Prefix `s103d_`, namespace `HRS.MS.R2WinOrbNL`.

`s103d_core`: for a FIXED trajectory `ρ` (with right derivative `ρ'`, both in `U2Dec (9d+92)` uniformly in time, and `t ↦ ρ'_t` continuous into the
weighted `C^{8d+81}` norm), a test function `φ ∈ SyN 3 (9d+93)` with classical adjoint solutions for all terminal times, the gradient estimate
`S103cGrad` at jet order `8d+83` and the stability `hStab`, there are `F 0 t = U(0,t)φ`, `F 1 t = u^{(1)}_t(0)`, `F 2 t = u^{(2)}_t(0)` (values at `0` of classical
adjoint solutions for the data `φ`, `L_tφ`, `L_t²φ + ∂_tL_tφ`) with the `C^j`, `j ≤ 4d+42` convergence of the terminal-time difference quotients (both signs of `h`).

Route: level 1 (`fam0 l = U(·,l)φ`, layer `s103c_layer1`, `s103c_step`, `s103c_timereg`), level 2 (`fam1 = u^{(1)}`, layer `s103c_layer2`, step, timereg).
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
theorem s103d_core {s a β : ℝ} {ρβ : Euc d → ℝ} (H : Mov2dTh d s β a ρβ) (Lnat : ℕ)
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
    ∃ F : Fin 3 → ℝ → Euc d → ℝ,
      (∀ t ∈ Set.Icc (0 : ℝ) T0, F 0 t = propagatorW ((quadraticGradientDyn d s a β).coeff ρ) 0 t φ) ∧
      (∀ a' : Fin 3, ∀ t ∈ Set.Icc (0 : ℝ) T0, ∃ u : ℝ → Euc d → ℝ,
        IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff ρ) t
          (s103nData ((quadraticGradientDyn d s a β).coeff ρ) φ a' t) u ∧ F a' t = u 0) ∧
      (∀ a' : Fin 3, ∀ ha : (a' : ℕ) < 2, ∀ t ∈ Set.Icc (0 : ℝ) T0, ∀ e : ℝ, 0 < e → ∃ δ : ℝ, 0 < δ ∧
        ∀ h : ℝ, h ≠ 0 → |h| < δ → t + h ∈ Set.Icc (0 : ℝ) T0 → ∀ j ≤ 4 * d + 42, ∀ x : Euc d,
          ‖iteratedFDeriv ℝ j (fun y => h⁻¹ * (F a' (t + h) y - F a' t y) -
            F ⟨(a' : ℕ) + 1, by omega⟩ t y) x‖ ≤ e) := by
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
  set T1 : ℝ := T0 + 2 with hT1def
  set T2 : ℝ := T0 + 1 with hT2def
  have hT1 : 0 ≤ T1 := by rw [hT1def]; linarith
  have hT2 : 0 ≤ T2 := by rw [hT2def]; linarith
  -- the data
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
  have hρ'c : ∀ x, ContinuousOn (fun σ => ρ' σ x) (Set.Ici 0) := s103c_contOn_of_uc hUC
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
  have hstep1' : ∀ t : ℝ, 0 ≤ t ∧ t < T1 → ∃ u : ℝ → Euc d → ℝ,
      IsClassicalAdjointW Cf t (generatorW Cf t φ) u ∧
      (S103cTimeReg (8 * d + 80) t u → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, h ≠ 0 → |h| < δ →
        0 ≤ t + h → t + h ≤ T1 → ∀ j ≤ 4 * d + 42, ∀ x : Euc d,
          ‖iteratedFDeriv ℝ j (fun y => h⁻¹ * (fam0 (t + h) 0 y - fam0 t 0 y) - u 0 y) x‖ ≤ ε) :=
    fun t ht => hstep1 t ht.1 ht.2
  choose! u1 hu1cl hu1conv using hstep1'
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
  have conv1 : ∀ t : ℝ, 0 ≤ t → t < T1 → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, h ≠ 0 → |h| < δ →
      0 ≤ t + h → t + h ≤ T1 → ∀ j ≤ 4 * d + 42, ∀ x : Euc d,
        ‖iteratedFDeriv ℝ j (fun y => h⁻¹ * (fam0 (t + h) 0 y - fam0 t 0 y) - u1 t 0 y) x‖ ≤ ε :=
    fun t ht0 htT => hu1conv t ⟨ht0, htT⟩ (htr1 t ht0 htT)
  -- LEVEL 2
  have hlt1 : T2 < T1 := by linarith
  have hlt0 : T0 < T2 := by linarith
  have hfam1 : ∀ l ∈ Set.Icc (0 : ℝ) T2, IsClassicalAdjointW Cf l (generatorW Cf l φ) (u1 l) :=
    fun l hl => hu1cl l ⟨hl.1, lt_of_le_of_lt hl.2 hlt1⟩
  have hj2 : ∀ l ∈ Set.Icc (0 : ℝ) T2, ∀ τ ∈ Set.Icc (0 : ℝ) l,
      ContDiff ℝ ((8 * d + 80 + 4 : ℕ) : WithTop ℕ∞) (u1 l τ) ∧
        ∀ i, 1 ≤ i → i ≤ 8 * d + 80 + 4 → ∀ y, ‖iteratedFDeriv ℝ i (u1 l τ) y‖ ≤ G2 := by
    intro l hl τ hτ
    obtain ⟨h1, h2⟩ := hG0 ρ hGrad l (fun y => generatorW Cf l φ y) (u1 l) A1 hl.1
      ((hχ1 l hl.1).bd.mono_N (by omega)) (hfam1 l hl) τ hτ
    exact ⟨h1, fun i hi1 hi2 y => h2 i hi1 (by omega) y⟩
  have hLay2 := s103c_layer2 hd hs0 hsd a β ha hβ (8 * d + 80) Lnat
    (by have := hLn (8 * d + 80 + 4) (by omega); exact this) T2 hT2 ρ ρ' Aρ Ad hAρ hAd hU5 hD3 hder hcont hρ'c hUC
    φ Aφ hAφ (hφ.mono_N (by omega : 8 * d + 80 + 6 ≤ 9 * d + 93)) G2 hG20 u1 hfam1 hj2
  have hLay2' : ∀ t ∈ Set.Icc (0 : ℝ) T2, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ e l : ℝ, 0 ≤ e → e < l →
      l ≤ T2 → e ≤ t → t ≤ l → l - e < δ →
      Bd (8 * d + 80) ε (fun y => (u1 l e y - u1 e e y) / (l - e) -
        (generatorW Cf t (fun x => generatorW Cf t φ x) y + s103nQ d s (ρ' t) φ y)) :=
    fun t ht => hLay2 t ht.1 ht.2
  have hfam1T : ∀ l ∈ Set.Icc (0 : ℝ) T2, IsClassicalAdjointW Cf l (u1 l l) (u1 l) := by
    intro l hl
    have h := hfam1 l hl
    have e : u1 l l = generatorW Cf l φ := h.terminal
    rw [e]; exact h
  have hρ1T2 : ∀ τ ∈ Set.Icc (0 : ℝ) T2, U2Dec 1 (Lnat : ℝ) Aρ (ρ τ) := fun τ hτ => hU1 τ hτ.1
  have hχ2bd : ∀ t ∈ Set.Icc (0 : ℝ) T2, Bd (8 * d + 80) A2 (fun y => generatorW Cf t
      (fun x => generatorW Cf t φ x) y + s103nQ d s (ρ' t) φ y) :=
    fun t ht => (hχ2 t ht.1).bd.mono_N (by omega)
  have hstep2 := s103c_step hd hs0 hsd (L := (Lnat : ℝ)) (by have := hLn 0 (by omega); simpa using this)
    hAρ ρ T2 hρ1T2 (8 * d + 80) Cs hCs hStab u1 hfam1T
    (fun t y => generatorW Cf t (fun x => generatorW Cf t φ x) y + s103nQ d s (ρ' t) φ y) A2 hχ2bd hLay2'
  have hstep2' : ∀ t : ℝ, 0 ≤ t ∧ t < T2 → ∃ u : ℝ → Euc d → ℝ,
      IsClassicalAdjointW Cf t (fun y => generatorW Cf t (fun x => generatorW Cf t φ x) y +
        s103nQ d s (ρ' t) φ y) u ∧
      (S103cTimeReg (8 * d + 80) t u → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, h ≠ 0 → |h| < δ →
        0 ≤ t + h → t + h ≤ T2 → ∀ j ≤ 4 * d + 42, ∀ x : Euc d,
          ‖iteratedFDeriv ℝ j (fun y => h⁻¹ * (u1 (t + h) 0 y - u1 t 0 y) - u 0 y) x‖ ≤ ε) :=
    fun t ht => hstep2 t ht.1 ht.2
  choose! u2 hu2cl hu2conv using hstep2'
  set G3 : ℝ := G0 * A2 with hG3
  have hG30 : 0 ≤ G3 := by positivity
  have hj3 : ∀ t : ℝ, 0 ≤ t → t < T2 → ∀ τ ∈ Set.Icc (0 : ℝ) t,
      ContDiff ℝ ((8 * d + 80 + 1 + 2 : ℕ) : WithTop ℕ∞) (u2 t τ) ∧
        ∀ i, 1 ≤ i → i ≤ 8 * d + 80 + 1 + 2 → ∀ y, ‖iteratedFDeriv ℝ i (u2 t τ) y‖ ≤ G3 := by
    intro t ht0 htT τ hτ
    obtain ⟨h1, h2⟩ := hG0 ρ hGrad t _ (u2 t) A2 ht0 ((hχ2 t ht0).bd.mono_N (by omega))
      (hu2cl t ⟨ht0, htT⟩) τ hτ
    exact ⟨h1.of_le (by exact_mod_cast (by omega : 8 * d + 80 + 1 + 2 ≤ 8 * d + 83 + 1)),
      fun i hi1 hi2 y => h2 i hi1 (by omega) y⟩
  have htr2 : ∀ t : ℝ, 0 ≤ t → t < T2 → S103cTimeReg (8 * d + 80) t (u2 t) := by
    intro t ht0 htT
    refine s103d_timeReg_of_lin (M := Kt * (A2 + (1 + Aρ) * G3)) (by positivity) ?_
    intro τ hτ
    exact hKt ρ Aρ hAρ hU2 t ⟨ht0, (htT.trans hlt1).le⟩ _ A2 G3 (u2 t)
      (hu2cl t ⟨ht0, htT⟩) ((hχ2 t ht0).mono_N (by omega : 8 * d + 80 + 1 ≤ 9 * d + 89)).1
      (fun i h1 h2 y => (hχ2 t ht0).2 i (by omega) y) (hj3 t ht0 htT) τ hτ
  have conv2 : ∀ t : ℝ, 0 ≤ t → t < T2 → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, h ≠ 0 → |h| < δ →
      0 ≤ t + h → t + h ≤ T2 → ∀ j ≤ 4 * d + 42, ∀ x : Euc d,
        ‖iteratedFDeriv ℝ j (fun y => h⁻¹ * (u1 (t + h) 0 y - u1 t 0 y) - u2 t 0 y) x‖ ≤ ε :=
    fun t ht0 htT => hu2conv t ⟨ht0, htT⟩ (htr2 t ht0 htT)
  -- the derivative of the generator in time
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
  -- the family
  refine ⟨![fun t => fam0 t 0, fun t => u1 t 0, fun t => u2 t 0], ?_, ?_, ?_⟩
  · intro t ht
    rfl
  · intro a' t ht
    have ht1 : t < T1 := by linarith [ht.2]
    have ht2 : t < T2 := by linarith [ht.2]
    fin_cases a'
    · exact ⟨fam0 t, hfam0 t ht.1, rfl⟩
    · exact ⟨u1 t, hu1cl t ⟨ht.1, ht1⟩, rfl⟩
    · refine ⟨u2 t, ?_, rfl⟩
      have e : s103nData Cf φ ⟨2, by norm_num⟩ t = fun y => generatorW Cf t (fun x => generatorW Cf t φ x) y +
          s103nQ d s (ρ' t) φ y := by
        funext y
        show generatorW Cf t (generatorW Cf t φ) y + derivWithin (fun t' => generatorW Cf t' φ y) (Set.Ici t) t = _
        rw [hdw t ht.1 y]
      rw [e]
      exact hu2cl t ⟨ht.1, ht2⟩
  · intro a' ha t ht e he
    have ht1 : t < T1 := by linarith [ht.2]
    have ht2 : t < T2 := by linarith [ht.2]
    fin_cases a'
    · obtain ⟨δ, hδ, hh⟩ := conv1 t ht.1 ht1 e he
      exact ⟨δ, hδ, fun h h0 hd' ht' j hj x => hh h h0 hd' ht'.1 (ht'.2.trans (by linarith)) j hj x⟩
    · obtain ⟨δ, hδ, hh⟩ := conv2 t ht.1 ht2 e he
      exact ⟨δ, hδ, fun h h0 hd' ht' j hj x => hh h h0 hd' ht'.1 (ht'.2.trans (by linarith)) j hj x⟩
    · exact absurd ha (by norm_num)

end HRS.MS.R2WinOrbNL

end

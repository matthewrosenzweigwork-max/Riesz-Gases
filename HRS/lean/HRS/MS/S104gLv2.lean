import HRS.MS.S104gLv1

/-!
# S10.4 packet S104G, part 6: level 2 of the orbit family at a general initial time

Prefix `s104g_`, namespace `HRS.MS.R2WinOrbNL`.

`s104g_level2` is the level-2 half of `s103d_core` with the initial time `r` general: given the level-1 family `u1` (classical adjoint solutions with terminal datum `L_tφ`
on `[0,T2]`), there is `u2 t r` (`0 ≤ t < T2`) such that `u2 t` is a classical adjoint solution with terminal datum `L_t²φ + Q_{ρ'_t}φ` (`= L_t²φ + ∂_tL_tφ`), the
difference quotients `h⁻¹ (u1 (t+h) r - u1 t r)` converge to `u2 t r` in every `C^j` sup norm (`j ≤ 4d+42`) for every `0 ≤ r ≤ min t (t+h)`, and the `C^1`
jets of `u2 t τ` are bounded uniformly.
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
theorem s104g_level2 {s a β : ℝ} {ρβ : Euc d → ℝ} (H : Mov2dTh d s β a ρβ) (Lnat : ℕ)
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
    (T2 : ℝ) (hT2 : 0 ≤ T2) (u1 : ℝ → ℝ → Euc d → ℝ)
    (hu1cl : ∀ l : ℝ, 0 ≤ l → l ≤ T2 → IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff ρ) l
      (generatorW ((quadraticGradientDyn d s a β).coeff ρ) l φ) (u1 l)) :
    ∃ u2 : ℝ → ℝ → Euc d → ℝ,
      (∀ t : ℝ, 0 ≤ t → t < T2 → IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff ρ) t
        (fun y => generatorW ((quadraticGradientDyn d s a β).coeff ρ) t
          (fun x => generatorW ((quadraticGradientDyn d s a β).coeff ρ) t φ x) y + s103nQ d s (ρ' t) φ y) (u2 t)) ∧
      (∀ t : ℝ, 0 ≤ t → t < T2 → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, h ≠ 0 → |h| < δ →
        0 ≤ t + h → t + h ≤ T2 → ∀ r : ℝ, 0 ≤ r → r ≤ t → r ≤ t + h → ∀ j ≤ 4 * d + 42, ∀ x : Euc d,
          ‖iteratedFDeriv ℝ j (fun y => h⁻¹ * (u1 (t + h) r y - u1 t r y) - u2 t r y) x‖ ≤ ε) ∧
      (∃ A2 : ℝ, ∀ t : ℝ, 0 ≤ t → Bd (8 * d + 80) A2 (fun y => generatorW ((quadraticGradientDyn d s a β).coeff ρ) t
          (fun x => generatorW ((quadraticGradientDyn d s a β).coeff ρ) t φ x) y + s103nQ d s (ρ' t) φ y)) ∧
      ∃ G3 : ℝ, 0 ≤ G3 ∧ ∀ t : ℝ, 0 ≤ t → t < T2 → ∀ τ ∈ Set.Icc (0 : ℝ) t,
        ContDiff ℝ 1 (u2 t τ) ∧ ∀ y, ‖iteratedFDeriv ℝ 1 (u2 t τ) y‖ ≤ G3 := by
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
  obtain ⟨Kt, hKt0, hKt⟩ := s103c_timereg hd hs0 hsd a β ha hβ (8 * d + 80) (L := (Lnat : ℝ))
    (by have := hLn (8 * d + 80 + 1) (by omega); exact this) T2 hT2
  have hU2 : ∀ τ ∈ Set.Icc (0 : ℝ) T2, U2Dec (8 * d + 80 + 1 + 1) (Lnat : ℝ) Aρ (ρ τ) := fun τ hτ =>
    ult_U2Dec_mono (hρU τ hτ.1) (by omega)
  set G2 : ℝ := G0 * A1 with hG2
  have hG20 : 0 ≤ G2 := by positivity
  have hfam1 : ∀ l ∈ Set.Icc (0 : ℝ) T2, IsClassicalAdjointW Cf l (generatorW Cf l φ) (u1 l) :=
    fun l hl => hu1cl l hl.1 hl.2
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
  have hu2ex : ∀ t : ℝ, 0 ≤ t ∧ t < T2 → ∃ u : ℝ → Euc d → ℝ,
      IsClassicalAdjointW Cf t (fun y => generatorW Cf t (fun x => generatorW Cf t φ x) y +
        s103nQ d s (ρ' t) φ y) u := fun t ht => by
    obtain ⟨u, hu, -⟩ := hstep2 t ht.1 ht.2
    exact ⟨u, hu⟩
  choose! u2 hu2cl using hu2ex
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
    exact hKt ρ Aρ hAρ hU2 t ⟨ht0, htT.le⟩ _ A2 G3 (u2 t)
      (hu2cl t ⟨ht0, htT⟩) ((hχ2 t ht0).mono_N (by omega : 8 * d + 80 + 1 ≤ 9 * d + 89)).1
      (fun i h1 h2 y => (hχ2 t ht0).2 i (by omega) y) (hj3 t ht0 htT) τ hτ
  refine ⟨u2, fun t ht0 htT => hu2cl t ⟨ht0, htT⟩, fun t ht0 htT ε hε => ?_,
    ⟨A2, fun t ht0 => (hχ2 t ht0).bd.mono_N (by omega)⟩, G3, hG30, fun t ht0 htT τ hτ => ?_⟩
  · exact s104g_conv hd hs0 hsd (L := (Lnat : ℝ)) (by have := hLn 0 (by omega); simpa using this)
      ρ T2 hρ1T2 (8 * d + 80) Cs hCs hStab u1 hfam1T
      (fun t y => generatorW Cf t (fun x => generatorW Cf t φ x) y + s103nQ d s (ρ' t) φ y) A2 hχ2bd hLay2'
      ht0 htT (hu2cl t ⟨ht0, htT⟩) (htr2 t ht0 htT) ε hε
  · obtain ⟨h1, h2⟩ := hj3 t ht0 htT τ hτ
    exact ⟨h1.of_le (by exact_mod_cast (by omega : 1 ≤ 8 * d + 80 + 1 + 2)), fun y => h2 1 le_rfl (by omega) y⟩

end HRS.MS.R2WinOrbNL

end

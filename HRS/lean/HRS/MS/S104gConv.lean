import HRS.MS.R2WinOrbTRE3

/-!
# S10.4 packet S104G, part 1: the difference-quotient step at a general initial time `r`, and uniqueness of classical adjoint solutions

Prefix `s104g_`, namespace `HRS.MS.R2WinOrbNL`.

* `s104g_unique`: two classical adjoint solutions with the same terminal datum (in `Bd N0`) agree on `[0,τ]` (stability with `A' = 0`).
* `s104g_conv`: given the limit solution `u` of `s103c_step` (a classical adjoint solution with datum `χ_t`) and its left time continuity, the difference quotients
  `h⁻¹ (fam (t+h) r - fam t r) → u r` in every `C^j` sup norm, `j ≤ 4d+42`, for every initial time `0 ≤ r ≤ min t (t+h)` (the `δ` does not depend on `r`).
  This is the tail of `s103c_step`, stated at a general initial time.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.R2WinOrbNL

open HRS HRS.Whole HRS.MS.Wad HRS.MS.Ul HRS.MS.Who HRS.MS.BreakdownS67 HRS.MS.MovLin HRS.MS.R2WinOrb

variable {d : ℕ}

theorem s104g_unique {s a β : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {L A : ℝ} (hL : (d : ℝ) < L)
    {ρ : ℝ → Euc d → ℝ} {N0 : ℕ} {Cs : ℝ} (hCs : 0 ≤ Cs)
    (hStab : ∀ (g : Euc d → ℝ) (A' : ℝ), Bd N0 A' g → ∀ t : ℝ, 0 ≤ t →
      R2OrbitSup ((quadraticGradientDyn d s a β).coeff ρ) (4 * d + 42) t g (Cs * A'))
    {τ : ℝ} (hτ : 0 ≤ τ) (hρ : ∀ σ ∈ Set.Icc (0 : ℝ) τ, U2Dec 1 L A (ρ σ))
    {g : Euc d → ℝ} {A' : ℝ} (hg : Bd N0 A' g) {f1 f2 : ℝ → Euc d → ℝ}
    (hf1 : IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff ρ) τ g f1)
    (hf2 : IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff ρ) τ g f2) :
    ∀ r ∈ Set.Icc (0 : ℝ) τ, f1 r = f2 r := by
  intro r hr
  have h1 := s103c_stab_one hCs hStab hτ hg hf1
  have h2 := s103c_stab_one hCs hStab hτ hg hf2
  have hz : Bd N0 0 (fun y => g y - g y) := by
    have e : (fun y => g y - g y) = fun _ => (0 : ℝ) := by funext y; ring
    rw [e]; exact Bd.zero N0
  have := s103c_diff_bound hd hs0 hsd hL hCs hStab hτ hρ hz hf1 hf2 (fun r hr => (h1 r hr).1)
    (fun r hr => (h2 r hr).1) r hr 0 (Nat.zero_le _)
  funext x
  have h0 := this x
  rw [s103c_iter_sub ((h1 r hr).1.of_le (by exact_mod_cast Nat.zero_le _))
    ((h2 r hr).1.of_le (by exact_mod_cast Nat.zero_le _))] at h0
  simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, mul_zero] at h0
  have := abs_nonpos_iff.1 h0
  linarith

theorem s104g_conv {s a β : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {L A : ℝ}
    (hL : (d : ℝ) + ((0 : ℕ) : ℝ) + s + 3 < L) (ρ : ℝ → Euc d → ℝ) (T1 : ℝ)
    (hρ : ∀ τ ∈ Set.Icc (0 : ℝ) T1, U2Dec 1 L A (ρ τ)) (N0 : ℕ) (Cs : ℝ) (hCs : 0 ≤ Cs)
    (hStab : ∀ (g : Euc d → ℝ) (A' : ℝ), Bd N0 A' g → ∀ t : ℝ, 0 ≤ t →
      R2OrbitSup ((quadraticGradientDyn d s a β).coeff ρ) (4 * d + 42) t g (Cs * A'))
    (fam : ℝ → ℝ → Euc d → ℝ)
    (hfam : ∀ l ∈ Set.Icc (0 : ℝ) T1, IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff ρ) l (fam l l) (fam l))
    (χ : ℝ → Euc d → ℝ) (Aχ : ℝ) (hχ : ∀ t ∈ Set.Icc (0 : ℝ) T1, Bd N0 Aχ (χ t))
    (hLay : ∀ t ∈ Set.Icc (0 : ℝ) T1, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ e l : ℝ, 0 ≤ e → e < l → l ≤ T1 →
      e ≤ t → t ≤ l → l - e < δ → Bd N0 ε (fun y => (fam l e y - fam e e y) / (l - e) - χ t y))
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t < T1) {u : ℝ → Euc d → ℝ}
    (hucl' : IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff ρ) t (χ t) u)
    (hTR : S103cTimeReg N0 t u) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, h ≠ 0 → |h| < δ → 0 ≤ t + h → t + h ≤ T1 →
      ∀ r : ℝ, 0 ≤ r → r ≤ t → r ≤ t + h → ∀ j ≤ 4 * d + 42, ∀ x : Euc d,
        ‖iteratedFDeriv ℝ j (fun y => h⁻¹ * (fam (t + h) r y - fam t r y) - u r y) x‖ ≤ ε := by
  intro ε hε
  set Cf := (quadraticGradientDyn d s a β).coeff ρ with hCf
  have hdL : (d : ℝ) < L := by
    have : (0 : ℝ) ≤ s := hs0
    simp only [Nat.cast_zero] at hL
    linarith
  have htI : t ∈ Set.Icc (0 : ℝ) T1 := ⟨ht0, htT.le⟩
  have hρt : ∀ σ ∈ Set.Icc (0 : ℝ) t, U2Dec 1 L A (ρ σ) := fun σ hσ => hρ σ ⟨hσ.1, hσ.2.trans htT.le⟩
  have hut : u t = χ t := hucl'.terminal
  have huCk : ∀ r ∈ Set.Icc (0 : ℝ) t, ContDiff ℝ ((4 * d + 42 : ℕ) : WithTop ℕ∞) (u r) :=
    fun r hr => (s103c_stab_one hCs hStab ht0 (hχ t htI) hucl' r hr).1
  set ε₁ : ℝ := ε / (2 * (Cs + 1)) with hε₁
  have hε₁0 : 0 < ε₁ := by positivity
  obtain ⟨δa, hδa, hLa⟩ := hLay t htI ε₁ hε₁0
  obtain ⟨δb, hδb, hTb⟩ := hTR ε₁ hε₁0
  have hCsε : Cs * (ε₁ + ε₁) ≤ ε := by
    calc Cs * (ε₁ + ε₁) = (Cs / (Cs + 1)) * ε := by rw [hε₁]; field_simp; ring
      _ ≤ 1 * ε := by
          refine mul_le_mul_of_nonneg_right ?_ hε.le
          rw [div_le_one (by positivity)]; linarith
      _ = ε := one_mul _
  refine ⟨min δa δb, lt_min hδa hδb, fun h hne hh' ht1 ht2 r hr0 hrt hrth j hj x => ?_⟩
  have hhδa : |h| < δa := hh'.trans_le (min_le_left _ _)
  have hhδb : |h| < δb := hh'.trans_le (min_le_right _ _)
  set wh : ℝ → Euc d → ℝ := fun r y => h⁻¹ * fam (t + h) r y + (-h⁻¹) * fam t r y with hwh
  have htarget : (fun y => h⁻¹ * (fam (t + h) r y - fam t r y) - u r y) = fun y => wh r y - u r y := by
    funext y; simp only [hwh]; ring
  rw [htarget]
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · -- h < 0
    have hτ0 : 0 ≤ t + h := ht1
    have hτt : t + h ≤ t := by linarith
    have hρτ : ∀ σ ∈ Set.Icc (0 : ℝ) (t + h), U2Dec 1 L A (ρ σ) := fun σ hσ => hρt σ ⟨hσ.1, hσ.2.trans hτt⟩
    have hf1 : IsClassicalAdjointW Cf (t + h) (fam (t + h) (t + h)) (fam (t + h)) := hfam (t + h) ⟨hτ0, ht2⟩
    have hf2 : IsClassicalAdjointW Cf (t + h) (fam t (t + h)) (fam t) := s103c_restrict (hfam t htI) hτt
    have hwhcl := s103c_lincomb hd hs0 hsd hdL ρ hρτ h⁻¹ (-h⁻¹) hf1 hf2
    have hur := s103c_restrict hucl' hτt
    have hlay := hLa (t + h) t hτ0 (by linarith) (by linarith [htT]) (by linarith) le_rfl
      (by rw [show t - (t + h) = -h by ring]; rwa [abs_of_neg hneg] at hhδa)
    have hdat : (fun y => h⁻¹ * fam (t + h) (t + h) y + (-h⁻¹) * fam t (t + h) y - χ t y) =
        fun y => (fam t (t + h) y - fam (t + h) (t + h) y) / (t - (t + h)) - χ t y := by
      funext y; rw [show t - (t + h) = -h by ring]; field_simp; ring
    have hl2 : Bd N0 ε₁ (fun y => h⁻¹ * fam (t + h) (t + h) y + (-h⁻¹) * fam t (t + h) y - χ t y) := by
      rw [hdat]; exact hlay
    have htr := hTb (t + h) ⟨hτ0, hτt⟩ (by rw [abs_of_neg hneg] at hhδb; linarith)
    have hdiffd : Bd N0 (ε₁ + ε₁) (fun y => (h⁻¹ * fam (t + h) (t + h) y + (-h⁻¹) * fam t (t + h) y) -
        u (t + h) y) := by
      have := s103c_Bd_sub hl2 htr
      have e : (fun y => (h⁻¹ * fam (t + h) (t + h) y + (-h⁻¹) * fam t (t + h) y - χ t y) -
          (u (t + h) y - u t y)) = fun y => (h⁻¹ * fam (t + h) (t + h) y + (-h⁻¹) * fam t (t + h) y) -
          u (t + h) y := by funext y; rw [hut]; ring
      rwa [e] at this
    have hdB : Bd N0 (ε₁ + Aχ) (fun y => h⁻¹ * fam (t + h) (t + h) y + (-h⁻¹) * fam t (t + h) y) :=
      s103c_Bd_add_const (A := ε₁) (B := Aχ) hl2 (hχ t htI)
    have hck1 := (s103c_stab_one hCs hStab hτ0 hdB hwhcl)
    have hck2 : ∀ r ∈ Set.Icc (0 : ℝ) (t + h), ContDiff ℝ ((4 * d + 42 : ℕ) : WithTop ℕ∞) (u r) :=
      fun r hr => huCk r ⟨hr.1, hr.2.trans hτt⟩
    have h0m : r ∈ Set.Icc (0 : ℝ) (t + h) := ⟨hr0, hrth⟩
    have key := s103c_diff_bound hd hs0 hsd hdL hCs hStab hτ0 hρτ hdiffd hwhcl hur
      (fun r hr => (hck1 r hr).1) hck2 r h0m j hj x
    rw [s103c_iter_sub ((hck1 r h0m).1.of_le (by exact_mod_cast hj)) ((hck2 r h0m).of_le (by exact_mod_cast hj))] at key
    exact key.trans hCsε
  · -- h > 0
    have hlay := hLa t (t + h) ht0 (by linarith) ht2 le_rfl (by linarith)
      (by rw [show t + h - t = h by ring]; rwa [abs_of_pos hpos] at hhδa)
    have hdat : (fun y => h⁻¹ * fam (t + h) t y + (-h⁻¹) * fam t t y - χ t y) =
        fun y => (fam (t + h) t y - fam t t y) / (t + h - t) - χ t y := by
      funext y; rw [show t + h - t = h by ring]; field_simp; ring
    have hl2 : Bd N0 ε₁ (fun y => h⁻¹ * fam (t + h) t y + (-h⁻¹) * fam t t y - χ t y) := by
      rw [hdat]; exact hlay
    have hwhcl := s103c_lincomb hd hs0 hsd hdL ρ hρt h⁻¹ (-h⁻¹)
      (s103c_restrict (hfam (t + h) ⟨ht1, ht2⟩) (by linarith)) (hfam t htI)
    have hdiffd : Bd N0 ε₁ (fun y => (h⁻¹ * fam (t + h) t y + (-h⁻¹) * fam t t y) - u t y) := by
      have e : (fun y => (h⁻¹ * fam (t + h) t y + (-h⁻¹) * fam t t y) - u t y) =
          fun y => h⁻¹ * fam (t + h) t y + (-h⁻¹) * fam t t y - χ t y := by funext y; rw [hut]
      rwa [e]
    have hdB : Bd N0 (ε₁ + Aχ) (fun y => h⁻¹ * fam (t + h) t y + (-h⁻¹) * fam t t y) :=
      s103c_Bd_add_const (A := ε₁) (B := Aχ) hl2 (hχ t htI)
    have hck1 := (s103c_stab_one hCs hStab ht0 hdB hwhcl)
    have h0m : r ∈ Set.Icc (0 : ℝ) t := ⟨hr0, hrt⟩
    have hucl'' : IsClassicalAdjointW Cf t (u t) u := by rw [hut]; exact hucl'
    have key := s103c_diff_bound hd hs0 hsd hdL hCs hStab ht0 hρt hdiffd hwhcl hucl''
      (fun r hr => (hck1 r hr).1) huCk r h0m j hj x
    rw [s103c_iter_sub ((hck1 r h0m).1.of_le (by exact_mod_cast hj)) ((huCk r h0m).of_le (by exact_mod_cast hj))] at key
    refine key.trans ?_
    calc Cs * ε₁ ≤ Cs * (ε₁ + ε₁) := mul_le_mul_of_nonneg_left (by linarith) hCs
      _ ≤ ε := hCsε

end HRS.MS.R2WinOrbNL

end

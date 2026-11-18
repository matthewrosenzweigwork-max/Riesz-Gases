import HRS.MS.R2WinOrbTRD9

/-!
# S10.3 packet [E], part 1: the abstract difference-quotient step

Prefix `s103c_`, namespace `HRS.MS.R2WinOrbNL`.

`s103c_step` is the one-level construction used twice in `S103nTermReg`.  Data: the coefficient `C_f = coeff ρ` with `ρ_τ ∈ U2Dec 1`; the stability estimate
`hStab` (`s103n_orbitSup_of_bd`: terminal data in `Bd N0` give `C_b^{4d+42}` bounds on all classical adjoint solutions); a family `fam l` of classical adjoint
solutions on `[0,l]`, `l ∈ [0,T1]`, with terminal values `fam l l`; a bounded family `χ_t ∈ Bd N0`; and the layer hypothesis `hLay`:
`(fam l e - fam e e)/(l-e) → χ_t` in `Bd N0` as `e ≤ t ≤ l`, `l-e → 0`.  Conclusion, for every `t ∈ [0,T1)`: there is a classical adjoint solution `u` on `[0,t]`
with terminal datum `χ_t` (the `Bd N0`-Cauchy limit of the difference quotients `(fam (t+h_n) - fam t)/h_n`) such that
`h⁻¹(fam (t+h) 0 - fam t 0) → u 0` in every `C^j` sup norm, `j ≤ 4d+42`, for both signs of `h`, provided `u` is continuous in time in `Bd N0` at `t` from the left
(`S103cTimeReg`; it holds for every classical solution with a datum of the class, see the assembly).
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

/-- `u` is continuous in time at `t` from the left in `Bd N0`. -/
def S103cTimeReg (N0 : ℕ) (t : ℝ) (u : ℝ → Euc d → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ τ ∈ Set.Icc (0 : ℝ) t, t - τ < δ → Bd N0 ε (fun y => u τ y - u t y)

theorem s103c_jets_of_r2cb {f : Euc d → ℝ} {k : ℕ} {A : ℝ} (hA : 0 ≤ A) (h : r2CbNormE k f ≤ ENNReal.ofReal A) :
    ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ A := by
  intro j hj x
  have hjm : j ∈ Finset.range (k + 1) := Finset.mem_range.2 (by omega)
  have h1 : ENNReal.ofReal ‖iteratedFDeriv ℝ j f x‖ ≤ r2CbNormE k f := by
    unfold r2CbNormE
    exact (le_iSup (fun x : Euc d => ENNReal.ofReal ‖iteratedFDeriv ℝ j f x‖) x).trans
      (Finset.single_le_sum (f := fun j => ⨆ x : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ j f x‖)
        (fun _ _ => zero_le) hjm)
  exact (ENNReal.ofReal_le_ofReal_iff hA).1 (h1.trans h)

theorem s103c_Bd_sub {N : ℕ} {A B : ℝ} {f g : Euc d → ℝ} (hf : Bd N A f) (hg : Bd N B g) :
    Bd N (A + B) (fun y => f y - g y) := by
  have h := hf.add (hg.smul (-1))
  have e : (fun y => f y - g y) = fun y => f y + (-1) * g y := by funext y; ring
  rw [e]
  refine h.mono_A ?_
  simp

theorem s103c_Bd_add_const {N : ℕ} {A B : ℝ} {f g : Euc d → ℝ} (hf : Bd N A (fun y => f y - g y))
    (hg : Bd N B g) : Bd N (A + B) f := by
  have h := hf.add hg
  have e : (fun y => (f y - g y) + g y) = f := by funext y; ring
  rwa [e] at h

/-- Stability for one solution. -/
theorem s103c_stab_one {s a β : ℝ} {ρ : ℝ → Euc d → ℝ} {N0 : ℕ} {Cs : ℝ} (hCs : 0 ≤ Cs)
    (hStab : ∀ (g : Euc d → ℝ) (A' : ℝ), Bd N0 A' g → ∀ t : ℝ, 0 ≤ t →
      R2OrbitSup ((quadraticGradientDyn d s a β).coeff ρ) (4 * d + 42) t g (Cs * A'))
    {τ : ℝ} (hτ : 0 ≤ τ) {g : Euc d → ℝ} {A' : ℝ} (hg : Bd N0 A' g) {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff ρ) τ g f) :
    ∀ r ∈ Set.Icc (0 : ℝ) τ, ContDiff ℝ ((4 * d + 42 : ℕ) : WithTop ℕ∞) (f r) ∧
      ∀ j ≤ 4 * d + 42, ∀ x, ‖iteratedFDeriv ℝ j (f r) x‖ ≤ Cs * A' := by
  intro r hr
  obtain ⟨h1, h2⟩ := hStab g A' hg τ hτ f hf r hr
  exact ⟨by exact_mod_cast h1, s103c_jets_of_r2cb (mul_nonneg hCs hg.nonneg) h2⟩

/-- Stability for a difference of two solutions. -/
theorem s103c_diff_bound {s a β : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {L A : ℝ} (hL : (d : ℝ) < L)
    {ρ : ℝ → Euc d → ℝ} {N0 : ℕ} {Cs : ℝ} (hCs : 0 ≤ Cs)
    (hStab : ∀ (g : Euc d → ℝ) (A' : ℝ), Bd N0 A' g → ∀ t : ℝ, 0 ≤ t →
      R2OrbitSup ((quadraticGradientDyn d s a β).coeff ρ) (4 * d + 42) t g (Cs * A'))
    {τ : ℝ} (hτ : 0 ≤ τ) (hρ : ∀ σ ∈ Set.Icc (0 : ℝ) τ, U2Dec 1 L A (ρ σ))
    {g1 g2 : Euc d → ℝ} {A' : ℝ} (hg : Bd N0 A' (fun y => g1 y - g2 y)) {f1 f2 : ℝ → Euc d → ℝ}
    (hf1 : IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff ρ) τ g1 f1)
    (hf2 : IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff ρ) τ g2 f2)
    (hc1 : ∀ r ∈ Set.Icc (0 : ℝ) τ, ContDiff ℝ ((4 * d + 42 : ℕ) : WithTop ℕ∞) (f1 r))
    (hc2 : ∀ r ∈ Set.Icc (0 : ℝ) τ, ContDiff ℝ ((4 * d + 42 : ℕ) : WithTop ℕ∞) (f2 r)) :
    ∀ r ∈ Set.Icc (0 : ℝ) τ, ∀ j ≤ 4 * d + 42, ∀ x,
      ‖iteratedFDeriv ℝ j (f1 r) x - iteratedFDeriv ℝ j (f2 r) x‖ ≤ Cs * A' := by
  intro r hr j hj x
  have hl := s103c_lincomb hd hs0 hsd hL ρ hρ 1 (-1) hf1 hf2
  have hgd : Bd N0 A' (fun y => 1 * g1 y + (-1) * g2 y) := by
    have e : (fun y => 1 * g1 y + (-1) * g2 y) = fun y => g1 y - g2 y := by funext y; ring
    rw [e]; exact hg
  obtain ⟨-, hjet⟩ := s103c_stab_one hCs hStab hτ hgd hl r hr
  have e : (fun y => 1 * f1 r y + (-1) * f2 r y) = fun y => f1 r y - f2 r y := by funext y; ring
  have := hjet j hj x
  rw [e, ← s103c_iter_sub (hc1 r hr |>.of_le (by exact_mod_cast hj)) (hc2 r hr |>.of_le (by exact_mod_cast hj))] at this
  exact this

theorem s103c_step {s a β : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {L A : ℝ}
    (hL : (d : ℝ) + ((0 : ℕ) : ℝ) + s + 3 < L) (hA : 0 ≤ A) (ρ : ℝ → Euc d → ℝ) (T1 : ℝ)
    (hρ : ∀ τ ∈ Set.Icc (0 : ℝ) T1, U2Dec 1 L A (ρ τ)) (N0 : ℕ) (Cs : ℝ) (hCs : 0 ≤ Cs)
    (hStab : ∀ (g : Euc d → ℝ) (A' : ℝ), Bd N0 A' g → ∀ t : ℝ, 0 ≤ t →
      R2OrbitSup ((quadraticGradientDyn d s a β).coeff ρ) (4 * d + 42) t g (Cs * A'))
    (fam : ℝ → ℝ → Euc d → ℝ)
    (hfam : ∀ l ∈ Set.Icc (0 : ℝ) T1, IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff ρ) l (fam l l) (fam l))
    (χ : ℝ → Euc d → ℝ) (Aχ : ℝ) (hχ : ∀ t ∈ Set.Icc (0 : ℝ) T1, Bd N0 Aχ (χ t))
    (hLay : ∀ t ∈ Set.Icc (0 : ℝ) T1, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ e l : ℝ, 0 ≤ e → e < l → l ≤ T1 →
      e ≤ t → t ≤ l → l - e < δ → Bd N0 ε (fun y => (fam l e y - fam e e y) / (l - e) - χ t y)) :
    ∀ t : ℝ, 0 ≤ t → t < T1 → ∃ u : ℝ → Euc d → ℝ,
      IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff ρ) t (χ t) u ∧
      (S103cTimeReg N0 t u → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, h ≠ 0 → |h| < δ → 0 ≤ t + h →
        t + h ≤ T1 → ∀ j ≤ 4 * d + 42, ∀ x : Euc d,
          ‖iteratedFDeriv ℝ j (fun y => h⁻¹ * (fam (t + h) 0 y - fam t 0 y) - u 0 y) x‖ ≤ ε) := by
  intro t ht0 htT
  set Cf := (quadraticGradientDyn d s a β).coeff ρ with hCf
  have hdL : (d : ℝ) < L := by
    have : (0 : ℝ) ≤ s := hs0
    simp only [Nat.cast_zero] at hL
    linarith
  have htI : t ∈ Set.Icc (0 : ℝ) T1 := ⟨ht0, htT.le⟩
  -- the sequence of steps
  obtain ⟨δ1, hδ1, hLay1⟩ := hLay t htI 1 one_pos
  obtain ⟨n₀, hn₀⟩ := exists_nat_one_div_lt (lt_min (sub_pos.2 htT) hδ1)
  set hh : ℕ → ℝ := fun n => 1 / (((n + n₀ : ℕ) : ℝ) + 1) with hhdef
  have hhpos : ∀ n, 0 < hh n := fun n => by simp only [hhdef]; positivity
  have hhle : ∀ n, hh n < min (T1 - t) δ1 := by
    intro n
    refine lt_of_le_of_lt ?_ hn₀
    simp only [hhdef]
    apply one_div_le_one_div_of_le (by positivity)
    push_cast; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hhT : ∀ n, t + hh n ≤ T1 := fun n => by
    have := (hhle n).trans_le (min_le_left _ _); linarith
  have hhlim : ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n ≥ N, hh n < δ := by
    intro δ hδ
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
    refine ⟨N, fun n hn => lt_of_le_of_lt ?_ hN⟩
    simp only [hhdef]
    apply one_div_le_one_div_of_le (by positivity)
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    push_cast; linarith [(Nat.cast_nonneg n₀ : (0 : ℝ) ≤ n₀)]
  -- the difference quotients as classical solutions on `[0,t]`
  set θ : ℕ → Euc d → ℝ := fun n y => (hh n)⁻¹ * fam (t + hh n) t y + (-(hh n)⁻¹) * fam t t y with hθ
  set w : ℕ → ℝ → Euc d → ℝ := fun n r y => (hh n)⁻¹ * fam (t + hh n) r y + (-(hh n)⁻¹) * fam t r y with hw
  have hρt : ∀ σ ∈ Set.Icc (0 : ℝ) t, U2Dec 1 L A (ρ σ) := fun σ hσ => hρ σ ⟨hσ.1, hσ.2.trans htT.le⟩
  have hwcl : ∀ n, IsClassicalAdjointW Cf t (θ n) (w n) := fun n =>
    s103c_lincomb hd hs0 hsd hdL ρ hρt (hh n)⁻¹ (-(hh n)⁻¹)
      (s103c_restrict (hfam (t + hh n) ⟨by linarith [hhpos n], hhT n⟩) (by linarith [hhpos n])) (hfam t htI)
  have hθχ : ∀ n, Bd N0 1 (fun y => θ n y - χ t y) := by
    intro n
    have := hLay1 t (t + hh n) ht0 (by linarith [hhpos n]) (hhT n) le_rfl (by linarith [hhpos n])
      (by have := (hhle n).trans_le (min_le_right _ _); linarith)
    have e : (fun y => (fam (t + hh n) t y - fam t t y) / (t + hh n - t) - χ t y) = fun y => θ n y - χ t y := by
      funext y; simp only [hθ]; rw [show t + hh n - t = hh n by ring]; field_simp; ring
    rwa [e] at this
  have hθB : ∀ n, Bd N0 (1 + Aχ) (θ n) := fun n => s103c_Bd_add_const (hθχ n) (hχ t htI)
  have hStabk : ∀ n, ∀ r ∈ Set.Icc (0 : ℝ) t, ContDiff ℝ ((4 * d + 42 : ℕ) : WithTop ℕ∞) (w n r) ∧
      ∀ j ≤ 4 * d + 42, ∀ x, ‖iteratedFDeriv ℝ j (w n r) x‖ ≤ Cs * (1 + Aχ) := fun n r hr =>
    s103c_stab_one hCs hStab ht0 (hθB n) (hwcl n) r hr
  -- the Cauchy property
  have hθb : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, Bd N0 ε (fun y => θ n y - χ t y) := by
    intro ε hε
    obtain ⟨δ, hδ, hLayε⟩ := hLay t htI ε hε
    obtain ⟨N, hN⟩ := hhlim δ hδ
    refine ⟨N, fun n hn => ?_⟩
    have := hLayε t (t + hh n) ht0 (by linarith [hhpos n]) (hhT n) le_rfl (by linarith [hhpos n])
      (by rw [show t + hh n - t = hh n by ring]; exact hN n hn)
    have e : (fun y => (fam (t + hh n) t y - fam t t y) / (t + hh n - t) - χ t y) = fun y => θ n y - χ t y := by
      funext y; simp only [hθ]; rw [show t + hh n - t = hh n by ring]; field_simp; ring
    rwa [e] at this
  have hcau : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N, ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ j ≤ 4 * d + 42, ∀ x,
      ‖iteratedFDeriv ℝ j (w n r) x - iteratedFDeriv ℝ j (w m r) x‖ ≤ ε := by
    intro ε hε
    set ε'' : ℝ := ε / (2 * (Cs + 1)) with hε''
    have hε''0 : 0 < ε'' := by positivity
    obtain ⟨N, hN⟩ := hθb ε'' hε''0
    refine ⟨N, fun n hn m hm r hr j hj x => ?_⟩
    have hdiff : Bd N0 (ε'' + ε'') (fun y => θ n y - θ m y) := by
      have := s103c_Bd_sub (hN n hn) (hN m hm)
      have e : (fun y => (θ n y - χ t y) - (θ m y - χ t y)) = fun y => θ n y - θ m y := by funext y; ring
      rwa [e] at this
    refine (s103c_diff_bound hd hs0 hsd hdL hCs hStab ht0 hρt hdiff (hwcl n) (hwcl m)
      (fun r hr => (hStabk n r hr).1) (fun r hr => (hStabk m r hr).1) r hr j hj x).trans ?_
    calc Cs * (ε'' + ε'') = (Cs / (Cs + 1)) * ε := by rw [hε'']; field_simp; ring
      _ ≤ 1 * ε := by
          refine mul_le_mul_of_nonneg_right ?_ hε.le
          rw [div_le_one (by positivity)]; linarith
      _ = ε := one_mul _
  obtain ⟨u, hucl, huCk, huconv⟩ := s103c_limit_solution hd hs0 hsd hL hA ρ ht0 hρt (k := 4 * d + 42) (by omega) w hwcl
    (fun n r hr => (hStabk n r hr).1) (Cs * (1 + Aχ)) (fun n r hr j hj x => (hStabk n r hr).2 j hj x) hcau
  -- the terminal datum of the limit
  have hut : u t = χ t := by
    funext y
    have h1 : Tendsto (fun n => w n t y) atTop (𝓝 (u t y)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine tendsto_order.2 ⟨fun a ha => Filter.Eventually.of_forall fun n => lt_of_lt_of_le ha (norm_nonneg _), fun a ha => ?_⟩
      obtain ⟨N, hN⟩ := huconv (a / 2) (by linarith)
      refine Filter.eventually_atTop.2 ⟨N, fun n hn => ?_⟩
      have := hN n hn t ⟨ht0, le_rfl⟩ 0 (Nat.zero_le _) y
      rw [s103c_iter_sub ((hStabk n t ⟨ht0, le_rfl⟩).1.of_le (by exact_mod_cast Nat.zero_le _))
        ((huCk t ⟨ht0, le_rfl⟩).of_le (by exact_mod_cast Nat.zero_le _))] at this
      simp only [norm_iteratedFDeriv_zero] at this
      linarith
    have h2 : Tendsto (fun n => w n t y) atTop (𝓝 (χ t y)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine tendsto_order.2 ⟨fun a ha => Filter.Eventually.of_forall fun n => lt_of_lt_of_le ha (norm_nonneg _), fun a ha => ?_⟩
      obtain ⟨N, hN⟩ := hθb (a / 2) (by linarith)
      refine Filter.eventually_atTop.2 ⟨N, fun n hn => ?_⟩
      have := (hN n hn).2 0 (Nat.zero_le _) y
      simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
      have e : w n t y - χ t y = θ n y - χ t y := rfl
      rw [e, Real.norm_eq_abs]; linarith
    exact tendsto_nhds_unique h1 h2
  have hucl' : IsClassicalAdjointW Cf t (χ t) u := by
    have := hucl
    rwa [hut] at this
  refine ⟨u, hucl', fun hTR ε hε => ?_⟩
  -- the convergence of the difference quotients
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
  refine ⟨min δa δb, lt_min hδa hδb, fun h hne hh' ht1 ht2 j hj x => ?_⟩
  have hhδa : |h| < δa := hh'.trans_le (min_le_left _ _)
  have hhδb : |h| < δb := hh'.trans_le (min_le_right _ _)
  set wh : ℝ → Euc d → ℝ := fun r y => h⁻¹ * fam (t + h) r y + (-h⁻¹) * fam t r y with hwh
  have htarget : (fun y => h⁻¹ * (fam (t + h) 0 y - fam t 0 y) - u 0 y) = fun y => wh 0 y - u 0 y := by
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
    -- the datum of `wh` at `t+h` and its distance to `χ_t`
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
    have h0m : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (t + h) := ⟨le_rfl, hτ0⟩
    have key := s103c_diff_bound hd hs0 hsd hdL hCs hStab hτ0 hρτ hdiffd hwhcl hur
      (fun r hr => (hck1 r hr).1) hck2 0 h0m j hj x
    rw [s103c_iter_sub ((hck1 0 h0m).1.of_le (by exact_mod_cast hj)) ((hck2 0 h0m).of_le (by exact_mod_cast hj))] at key
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
    have h0m : (0 : ℝ) ∈ Set.Icc (0 : ℝ) t := ⟨le_rfl, ht0⟩
    have key := s103c_diff_bound hd hs0 hsd hdL hCs hStab ht0 hρt hdiffd hwhcl hucl
      (fun r hr => (hck1 r hr).1) huCk 0 h0m j hj x
    rw [s103c_iter_sub ((hck1 0 h0m).1.of_le (by exact_mod_cast hj)) ((huCk 0 h0m).of_le (by exact_mod_cast hj))] at key
    refine key.trans ?_
    calc Cs * ε₁ ≤ Cs * (ε₁ + ε₁) := mul_le_mul_of_nonneg_left (by linarith) hCs
      _ ≤ ε := hCsε

end HRS.MS.R2WinOrbNL

end

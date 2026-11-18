import HRS.MS.TransOpAux14
import HRS.MS.AdjDecayAux1

/-!
# S611 packet P4b: transport of classical adjoint solutions by a time-dependent translation

`s611_adjoint_shift`: if `f` is a classical adjoint solution (`IsClassicalAdjointW`) of `C'` with terminal datum `φ` on `[0,t]`, then
`(r, x) ↦ f r (x - c_r)` is one for `Cc` with datum `φ(· - c_t)`, whenever `Cc` is the `c`-shift of `C'`
(`drift_c = drift'(· - c_r) + c'_r`, `ρ_c = ρ'(· - c_r)`, `c' = ċ` continuous).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.TransOp

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

theorem s611_iteratedFDeriv_sub (n : ℕ) (g : Euc d → ℝ) (a x : Euc d) :
    iteratedFDeriv ℝ n (fun y => g (y - a)) x = iteratedFDeriv ℝ n g (x - a) := by
  have := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := g) n (-a) x
  simpa [sub_eq_add_neg] using this

theorem s611_fderiv_eq_curry (g : Euc d → ℝ) (x : Euc d) :
    fderiv ℝ g x = (continuousMultilinearCurryFin1 ℝ (Euc d) ℝ) (iteratedFDeriv ℝ 1 g x) := by
  ext v
  simp

/-- Continuity of `(r, y) ↦ iteratedFDeriv ℝ 1 (f r) y` at interior points, as a function on `ℝ × ℝ^d`. -/
theorem s611_continuousAt_iter1 {f : ℝ → Euc d → ℝ} {t : ℝ}
    (hf : Continuous fun p : Set.Icc (0 : ℝ) t × Euc d => iteratedFDeriv ℝ 1 (f p.1) p.2)
    {r : ℝ} (hr : r ∈ Set.Ioo 0 t) (y : Euc d) :
    ContinuousAt (fun p : ℝ × Euc d => iteratedFDeriv ℝ 1 (f p.1) p.2) (r, y) := by
  have hle : (0 : ℝ) ≤ t := hr.1.le.trans hr.2.le
  have hP : Continuous (fun p : ℝ × Euc d => ((Set.projIcc 0 t hle p.1, p.2) : Set.Icc (0 : ℝ) t × Euc d)) :=
    (continuous_projIcc.comp continuous_fst).prodMk continuous_snd
  have h1 := hf.comp hP
  have hev : ∀ᶠ p : ℝ × Euc d in 𝓝 (r, y), p.1 ∈ Set.Ioo 0 t :=
    (continuous_fst.continuousAt.eventually (isOpen_Ioo.mem_nhds hr))
  refine (h1.continuousAt (x := (r, y))).congr ?_
  filter_upwards [hev] with p hp
  simp only [Function.comp]
  rw [Set.projIcc_of_mem hle ⟨hp.1.le, hp.2.le⟩]

theorem s611_adjoint_shift {C' Cc : WholeCoeff d} (c c' : ℝ → Euc d)
    (hc : ∀ r, HasDerivAt c (c' r) r) (hc'cont : Continuous c')
    (hs : Cc.s = C'.s) (hM : Cc.M = C'.M) (hν : Cc.ν = C'.ν)
    (hdrift : ∀ r x, Cc.drift r x = C'.drift r (x - c r) + c' r)
    (hρ : ∀ r x, Cc.ρ r x = C'.ρ r (x - c r))
    {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ} (h : IsClassicalAdjointW C' t φ f) :
    IsClassicalAdjointW Cc t (fun x => φ (x - c t)) (fun r x => f r (x - c r)) := by
  have hccont : Continuous c := continuous_iff_continuousAt.2 fun r => (hc r).continuousAt
  have hgen : ∀ r x, generatorW Cc r (fun y => f r (y - c r)) x =
      generatorW C' r (f r) (x - c r) + inner ℝ (c' r) (gradient (f r) (x - c r)) := fun r x =>
    s611_generator_shift (c r) (c' r) r hs hM hν (hdrift r) (hρ r) (f r) x
  -- continuity of the gradient family
  have hgradc : Continuous fun p : Set.Icc (0 : ℝ) t × Euc d => gradient (f p.1) p.2 := by
    have h1 := h.cont_c2 1 (by norm_num)
    have : (fun p : Set.Icc (0 : ℝ) t × Euc d => gradient (f p.1) p.2) = fun p =>
        (InnerProductSpace.toDual ℝ (Euc d)).symm
          ((continuousMultilinearCurryFin1 ℝ (Euc d) ℝ) (iteratedFDeriv ℝ 1 (f p.1) p.2)) := by
      funext p
      unfold gradient
      rw [s611_fderiv_eq_curry]
    rw [this]
    exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp
      ((continuousMultilinearCurryFin1 ℝ (Euc d) ℝ).continuous.comp h1)
  have hshift : Continuous fun p : Set.Icc (0 : ℝ) t × Euc d =>
      ((p.1, p.2 - c (p.1 : ℝ)) : Set.Icc (0 : ℝ) t × Euc d) :=
    continuous_fst.prodMk
      (continuous_snd.sub (hccont.comp (continuous_subtype_val.comp continuous_fst)))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    exact (h.c2 r hr).comp (contDiff_id.sub contDiff_const)
  · intro j hj
    obtain ⟨B, hB⟩ := h.bdd j hj
    exact ⟨B, fun r hr x => by rw [s611_iteratedFDeriv_sub]; exact hB r hr _⟩
  · intro j hj
    have h1 := (h.cont_c2 j hj).comp hshift
    refine h1.congr fun p => ?_
    simp only [Function.comp]
    rw [s611_iteratedFDeriv_sub]
  · funext x
    show f t (x - c t) = φ (x - c t)
    rw [h.terminal]
  · intro x r hr
    set γ : ℝ → Euc d := fun r' => x - c r' with hγ
    have hγd : HasDerivAt γ (-(c' r)) r := (hc r).const_sub x
    have hFx : ∀ᶠ v' in 𝓝 r, ∀ y : Euc d, HasFDerivAt (f v') (fderiv ℝ (f v') y) y := by
      filter_upwards [isOpen_Ioo.mem_nhds hr] with v' hv'
      intro y
      exact (((h.c2 v' ⟨hv'.1.le, hv'.2.le⟩).differentiable (by norm_num)) y).hasFDerivAt
    have hcont : ContinuousAt (fun p : ℝ × Euc d => fderiv ℝ (f p.1) p.2) (r, γ r) := by
      have h1 := s611_continuousAt_iter1 (h.cont_c2 1 (by norm_num)) hr (γ r)
      have h2 : ContinuousAt (fun p : ℝ × Euc d =>
          (continuousMultilinearCurryFin1 ℝ (Euc d) ℝ) (iteratedFDeriv ℝ 1 (f p.1) p.2)) (r, γ r) :=
        (continuousMultilinearCurryFin1 ℝ (Euc d) ℝ).continuous.continuousAt.comp h1
      exact h2.congr (Filter.Eventually.of_forall fun p => (s611_fderiv_eq_curry (f p.1) p.2).symm)
    have hFt : HasDerivAt (fun v' => f v' (γ r)) (-(generatorW C' r (f r) (γ r))) r :=
      h.time_deriv (γ r) r hr
    have key := HRS.MS.AdjDecay.ad3_chain hFx hcont hFt hγd
    refine key.congr_deriv ?_
    rw [hgen r x]
    have e : fderiv ℝ (f r) (γ r) (-(c' r)) = -(inner ℝ (c' r) (gradient (f r) (x - c r))) := by
      rw [map_neg, ← HRS.MS.A0.a0_inner_gradient, real_inner_comm]
    rw [e]
    simp only [hγ]
    ring
  · have h1 := h.cont_time_deriv.comp hshift
    have h2 : Continuous fun p : Set.Icc (0 : ℝ) t × Euc d =>
        inner ℝ (c' (p.1 : ℝ)) (gradient (f p.1) (p.2 - c (p.1 : ℝ))) :=
      (hc'cont.comp (continuous_subtype_val.comp continuous_fst)).inner (hgradc.comp hshift)
    refine (h1.add h2).congr fun p => ?_
    simp only [Function.comp, Pi.add_apply]
    rw [hgen]
  · obtain ⟨B, hB⟩ := h.bdd_time_deriv
    obtain ⟨Bg, hBg⟩ := h.bdd 1 (by norm_num)
    obtain ⟨Bc, hBc⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (hccont.continuousOn (s := Set.Icc 0 t))
    obtain ⟨Bc', hBc'⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (hc'cont.continuousOn (s := Set.Icc 0 t))
    refine ⟨|B| * (1 + Bc) + Bc' * Bg, fun r hr x => ?_⟩
    have hBc0 : 0 ≤ Bc := (norm_nonneg _).trans (hBc r hr)
    have hBc'0 : 0 ≤ Bc' := (norm_nonneg _).trans (hBc' r hr)
    have hBg0 : 0 ≤ Bg := (norm_nonneg _).trans (hBg r hr x)
    have h1 := hB r hr (x - c r)
    have hx : ‖x - c r‖ ≤ ‖x‖ + Bc := (norm_sub_le _ _).trans (by linarith [hBc r hr])
    have hgr : ‖gradient (f r) (x - c r)‖ ≤ Bg := by
      rw [HRS.MS.A0.a0_norm_gradient, ← norm_iteratedFDeriv_one (𝕜 := ℝ)]
      exact hBg r hr _
    have hin : |inner ℝ (c' r) (gradient (f r) (x - c r))| ≤ Bc' * Bg := by
      calc |inner ℝ (c' r) (gradient (f r) (x - c r))| ≤ ‖c' r‖ * ‖gradient (f r) (x - c r)‖ :=
            abs_real_inner_le_norm _ _
        _ ≤ Bc' * Bg := mul_le_mul (hBc' r hr) hgr (norm_nonneg _) hBc'0
    show |generatorW Cc r (fun y => f r (y - c r)) x| ≤ _
    rw [hgen]
    calc |generatorW C' r (f r) (x - c r) + inner ℝ (c' r) (gradient (f r) (x - c r))|
        ≤ |generatorW C' r (f r) (x - c r)| + |inner ℝ (c' r) (gradient (f r) (x - c r))| := abs_add_le _ _
      _ ≤ |B| * (1 + ‖x‖ + Bc) + Bc' * Bg := by
          refine add_le_add ?_ hin
          calc |generatorW C' r (f r) (x - c r)| ≤ B * (1 + ‖x - c r‖) := h1
            _ ≤ |B| * (1 + ‖x - c r‖) := mul_le_mul_of_nonneg_right (le_abs_self B) (by positivity)
            _ ≤ |B| * (1 + ‖x‖ + Bc) := by
                refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg B)
                linarith
      _ ≤ (|B| * (1 + Bc) + Bc' * Bg) * (1 + ‖x‖) := by
          have h2 : 0 ≤ |B| := abs_nonneg B
          have h3 : 0 ≤ ‖x‖ := norm_nonneg x
          have h4 : 0 ≤ Bc' * Bg := mul_nonneg hBc'0 hBg0
          nlinarith [mul_nonneg h2 hBc0, mul_nonneg h2 (mul_nonneg hBc0 h3), mul_nonneg h4 h3]

end HRS.MS.TransOp

end

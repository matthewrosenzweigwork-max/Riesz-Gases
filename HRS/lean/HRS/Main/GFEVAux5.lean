import HRS.Main.GFEVAux4

/-!
# Packet GFEVG, part 5: the coefficient path `μ'`, `AdjointData` on every window, `GenHyp`

`gfevMu T ρ r = ρ (clamp r)` is the constant continuation of `ρ` after `T` (and before `0`); `GFPde` bundles the
analytic hypotheses on `(D, ρ)` and yields `AdjointData` at every level and every window, and `GenHyp`.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.GF

open HRS HRS.PDE HRS.PDE.ET HRS.Uniform HRS.Uniform.Q54

variable {d : ℕ}

def gfevClamp (T r : ℝ) : ℝ := max 0 (min r T)

theorem gfevClamp_mem {T : ℝ} (hT : 0 ≤ T) (r : ℝ) : gfevClamp T r ∈ Set.Icc 0 T :=
  ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩

theorem gfevClamp_of_mem {T r : ℝ} (hr : r ∈ Set.Icc 0 T) : gfevClamp T r = r := by
  unfold gfevClamp
  rw [min_eq_left hr.2, max_eq_right hr.1]

theorem continuous_gfevClamp (T : ℝ) : Continuous (gfevClamp T) :=
  continuous_const.max (continuous_id.min continuous_const)

/-- The constant continuation of `ρ` outside `[0,T]`. -/
def gfevMu (T : ℝ) (ρ : ℝ → Torus d → ℝ) : ℝ → Torus d → ℝ := fun r => ρ (gfevClamp T r)

theorem gfevMu_of_mem {T : ℝ} {ρ : ℝ → Torus d → ℝ} {r : ℝ} (hr : r ∈ Set.Icc 0 T) :
    gfevMu T ρ r = ρ r := by
  simp [gfevMu, gfevClamp_of_mem hr]

/-- The analytic hypotheses of the evolution construction. -/
structure GFPde (d : ℕ) (s : ℝ) (γ : ℕ) (R : Regime) (VB Λ : ℝ) (D : DynData d) (T : ℝ)
    (ρ : ℝ → Torus d → ℝ) : Prop where
  hd : 1 ≤ d
  hs0 : 0 ≤ s
  hsd : s < d
  hγ5 : 5 ≤ γ
  hm : mStar d ≤ γ
  hT : 0 < T
  hDs : D.s = s
  hDM : D.M = -1
  hV : Torus.IsCk ((γ + 2 * d + 12 : ℕ) : WithTop ℕ∞) D.V ∧ Torus.cbNorm (γ + 2 * d + 12) D.V ≤ VB
  hρ : ∀ r ∈ Set.Icc (0 : ℝ) T, IsProbDensity (ρ r) ∧
    Torus.IsCk ((γ + 2 * d + 12 : ℕ) : WithTop ℕ∞) (ρ r) ∧ Torus.cbNorm (γ + 2 * d + 12) (ρ r) ≤ Λ
  hweak : ∀ ψ : Torus d → ℝ, Continuous ψ → ContinuousOn (fun r => ∫ x, ψ x * ρ r x) (Set.Icc 0 T)
  hreg : ∀ T' : ℝ, 0 < T' → R.Holds d s D.M D.invβ 0 T' (gfevMu T ρ)

variable {s : ℝ} {γ : ℕ} {R : Regime} {VB Λ : ℝ} {D : DynData d} {T : ℝ} {ρ : ℝ → Torus d → ℝ}

theorem GFPde.matBound (h : GFPde d s γ R VB Λ D T ρ) : MatBound 1 D.M := by
  intro i j
  rw [h.hDM, Matrix.neg_apply, Matrix.one_apply]
  split_ifs <;> norm_num

theorem GFPde.adjointData (h : GFPde d s γ R VB Λ D T ρ) {m : ℕ} (hm : m + 3 ≤ γ + 2 * d + 12)
    {T' : ℝ} (hT' : 0 < T') : AdjointData s m R 1 Λ VB D 0 T' (gfevMu T ρ) := by
  have hle : m + 3 ≤ γ + 2 * d + 12 := hm
  refine ⟨h.hDs, h.matBound, ⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, hT', h.hreg T' hT'⟩
  · exact ET.isCk_mono' hle h.hV.1
  · exact (ET.cbNorm_mono' hle _).trans h.hV.2
  · intro r hr
    exact (h.hρ _ (gfevClamp_mem h.hT.le r)).1
  · intro r hr
    exact ET.isCk_mono' hle (h.hρ _ (gfevClamp_mem h.hT.le r)).2.1
  · intro r hr
    exact (ET.cbNorm_mono' hle _).trans (h.hρ _ (gfevClamp_mem h.hT.le r)).2.2
  · intro ψ hψ
    have hc : ContinuousOn ((fun r => ∫ x, ψ x * ρ r x) ∘ gfevClamp T) (Set.Icc 0 T') :=
      ContinuousOn.comp (g := fun r => ∫ x, ψ x * ρ r x) (s := Set.Icc 0 T') (h.hweak ψ hψ)
        (continuous_gfevClamp T).continuousOn (fun r _ => gfevClamp_mem h.hT.le r)
    exact hc

/-- Explicit uniform Fourier decay from a `C^n` bound. -/
theorem gfev_coeff_decay (f : Torus d → ℝ) (n : ℕ) (Λ : ℝ) (hf : Torus.IsCk (n : WithTop ℕ∞) f)
    (hb : Torus.cbNorm n f ≤ Λ) (m : Lattice d) :
    ‖coeffOf f m‖ ≤ (Λ * ((1 + 2 * Real.pi) / (2 * Real.pi)) ^ n + Λ) * Lattice.jp m ^ (-(n : ℝ)) := by
  set c0 : ℝ := Torus.cbNorm n f with hc0
  have hc00 : 0 ≤ c0 := R2Aux.cbNorm_nonneg' n f
  set c1 : ℝ := ((1 + 2 * Real.pi) / (2 * Real.pi)) ^ n with hc1
  have hc10 : 0 ≤ c1 := by positivity
  have hΛ : (c0 * c1 + c0) ≤ Λ * c1 + Λ := by nlinarith
  by_cases hm : m = 0
  · subst hm
    have h1 : ‖coeffOf f 0‖ ≤ c0 := by
      rw [coeffOf_eq_fcoef]
      exact Torus.norm_fcoef_le_of_bound (fun x => R2Aux.abs_le_cbNorm hf x) 0
    rw [jp_zero, Real.one_rpow, mul_one]
    nlinarith [mul_nonneg hc00 hc10]
  · have h1 := coeffOf_decay f hf m hm
    have hj := Torus.jp_pos m
    have e : Lattice.jp m ^ (-(n : ℝ)) = (Lattice.jp m ^ n)⁻¹ := by
      rw [Real.rpow_neg hj.le, Real.rpow_natCast]
    rw [e, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    calc ‖coeffOf f m‖ * Lattice.jp m ^ n ≤ c0 * c1 := h1
      _ ≤ (Λ * c1 + Λ) := by nlinarith

theorem gfev_jp_rpow_le {a b : ℝ} (hab : a ≤ b) (m : Lattice d) :
    Lattice.jp m ^ (-b) ≤ Lattice.jp m ^ (-a) :=
  Real.rpow_le_rpow_of_exponent_le (Torus.jp_ge_one m) (by linarith)

/-- The coefficient hypotheses `GenHyp` for the continued path, with `K = γ + 2d + 11`. -/
theorem GFPde.genHyp (h : GFPde d s γ R VB Λ D T ρ) :
    ∃ Bμ BV : ℝ, 0 ≤ Bμ ∧ 0 ≤ BV ∧ ∀ t : ℝ,
      GenHyp d s ((γ + 2 * d + 11 : ℕ) : ℝ) 1 Bμ BV D (gfevMu T ρ t) := by
  set n : ℕ := γ + 2 * d + 12 with hn
  set c1 : ℝ := ((1 + 2 * Real.pi) / (2 * Real.pi)) ^ n with hc1
  have hc10 : 0 ≤ c1 := by positivity
  have hΛ0 : 0 ≤ Λ := (R2Aux.cbNorm_nonneg' n (ρ 0)).trans
    (h.hρ 0 ⟨le_rfl, h.hT.le⟩).2.2
  have hVB0 : 0 ≤ VB := (R2Aux.cbNorm_nonneg' n D.V).trans h.hV.2
  refine ⟨Λ * c1 + Λ, VB * c1 + VB, by positivity, by positivity, fun t => ⟨h.hDs, h.matBound, ?_, ?_⟩⟩
  · intro m
    have hr := h.hρ _ (gfevClamp_mem h.hT.le t)
    have := gfev_coeff_decay (ρ (gfevClamp T t)) n Λ hr.2.1 hr.2.2 m
    refine this.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have hh := gfev_jp_rpow_le (a := ((γ + 2 * d + 11 : ℕ) : ℝ)) (b := (n : ℝ)) (by simp [hn]; norm_num) m
    exact hh
  · intro m
    have := gfev_coeff_decay D.V n VB h.hV.1 h.hV.2 m
    have e : -(((γ + 2 * d + 11 : ℕ) : ℝ) + 1) = -(n : ℝ) := by simp [hn]; ring
    rw [e]
    exact this

end HRS.GF

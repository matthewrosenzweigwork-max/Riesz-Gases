import HRS.MS.UniqC1b

/-!
# Packet C1, part 3: `IsAdvectingDrift` (minus joint continuity) for `b^σ = meanFieldDriftW D (ρ (t-σ))`

Main results (all with the explicit constant `c1Cb d s m MB Λ ΛV G₀`, depending only on
`(d, s, m, MB, Λ, ΛV, G₀)`):

* `c1_drift_single`: for every `r ∈ [0,T]`, `meanFieldDriftW D (ρ r)` satisfies `AdvBounds m Cb`
  (`C^{m+1}`, derivative bounds `1 ≤ j ≤ m+1`, growth `Cb (1+|x|)`).
* `c1_drift_family`: for `t ∈ [0,T]` and every `σ ∈ [0,t]`, the same for `b^σ = meanFieldDriftW D (ρ (t-σ))`.
* `c1_isAdvectingDrift`: the full `IsAdvectingDrift m Cb t (fun σ => meanFieldDriftW D (ρ (t-σ)))`,
  given the joint continuity of `(σ,x) ↦ b^σ(x)` on `[0,t] × ℝ^d` (packet C2).
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.UniqC1
open HRS HRS.Whole HRS.Whole.AppendixA HRS.MP.RdGen

variable {d : ℕ}

theorem AdvBounds.mono {m : ℕ} {C C' : ℝ} {f : Euc d → Euc d} (h : AdvBounds m C f) (hC : C ≤ C') :
    AdvBounds m C' f :=
  ⟨h.smooth, fun j h1 h2 x => (h.deriv_bdd j h1 h2 x).trans hC, fun x =>
    (h.growth x).trans (mul_le_mul_of_nonneg_right hC (by positivity))⟩

/-- The decay constant of the density: `d^{m+3} Λ' 2^{d+3}` (`Λ' = max Λ 0`). -/
def c1A (d m : ℕ) (Λ : ℝ) : ℝ := (d : ℝ) ^ (m + 3) * max Λ 0 * 2 ^ ((d : ℝ) + 3)

/-- The constant `Cb` of the advecting-drift bounds. -/
def c1Cb (d : ℕ) (s : ℝ) (m : ℕ) (MB Λ ΛV G₀ : ℝ) : ℝ :=
  d * (c1Kc d s (max MB 0) (c1A d m Λ) + (G₀ + ΛV))

/-- **Drift bounds at a fixed time** (`B:eq:drift-bounds-rd` minus joint continuity). -/
theorem c1_drift_single (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (MB Λ ΛV G₀ : ℝ) {D : WholeDyn d} {ρ : ℝ → Euc d → ℝ} {T : ℝ} (hDs : D.s = s)
    (hMB : HRS.PDE.MatBound MB D.M) (hV : VHypRd (m + 3) ΛV G₀ D.V)
    (hcoef : CoeffHypRd s m Λ T ρ) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) :
    AdvBounds m (c1Cb d s m MB Λ ΛV G₀) (meanFieldDriftW D (ρ r)) := by
  have hcb := hcoef.regular.1 r hr
  have hcb0 : 0 ≤ HRS.cbNorm (m + 3) (ρ r) :=
    Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _
  have hdec : RgDecay (m + 1 + 2) (fun _ => c1A d m Λ) (ρ r) :=
    rg_decay_mono (by omega) (rg_rho_decay hd (r := m + 3) (Λ := max Λ 0) hcb.1 hcb.2.1
      (by linarith [hcb.2.2, le_max_left Λ 0]))
  have hA : 0 ≤ c1A d m Λ := by unfold c1A; positivity
  have hMB' : HRS.PDE.MatBound (max MB 0) D.M := fun i j => (hMB i j).trans (le_max_left _ _)
  have hV' : VHypRd (m + 1 + 1) ΛV G₀ D.V := rg_VHyp_mono hV (by omega) le_rfl le_rfl
  have hG0 : 0 ≤ G₀ := (norm_nonneg _).trans hV.2.2
  have hΛV : 0 ≤ ΛV := (norm_nonneg _).trans (hV.2.1 2 le_rfl (by omega) 0)
  have hcomp := fun j => c1_comp hd hs0 hsd hA hDs hMB' hV' hdec j
  have hKc : 0 ≤ c1Kc d s (max MB 0) (c1A d m Λ) := by
    have h1 := rg_sigma_nonneg hs0
    have h2 := rg_near_nonneg (d := d) s
    have h3 := rg_W_nonneg (d := d)
    unfold c1Kc
    positivity
  have := c1_vec_of_comp (m := m) (C1 := c1Kc d s (max MB 0) (c1A d m Λ) + ΛV)
    (C0 := c1Kc d s (max MB 0) (c1A d m Λ) + (G₀ + ΛV)) (meanFieldDriftW D (ρ r))
    (fun j => (hcomp j).1) (fun j => (hcomp j).2.1) (fun j => (hcomp j).2.2)
  refine this.mono (max_le ?_ le_rfl)
  unfold c1Cb
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg d)
  linarith

/-- **Drift bounds along the time-reversed path** `σ ↦ b^σ = meanFieldDriftW D (ρ (t-σ))`, `σ ∈ [0,t]`,
for `t ∈ [0,T]`: everything in `IsAdvectingDrift m Cb t b` except the joint continuity (packet C2). -/
theorem c1_drift_family (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (MB Λ ΛV G₀ : ℝ) {D : WholeDyn d} {ρ : ℝ → Euc d → ℝ} {T : ℝ} (hDs : D.s = s)
    (hMB : HRS.PDE.MatBound MB D.M) (hV : VHypRd (m + 3) ΛV G₀ D.V)
    (hcoef : CoeffHypRd s m Λ T ρ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∀ σ ∈ Set.Icc (0 : ℝ) t,
      AdvBounds m (c1Cb d s m MB Λ ΛV G₀) (meanFieldDriftW D (ρ (t - σ))) := fun σ hσ =>
  c1_drift_single hd hs0 hsd m MB Λ ΛV G₀ hDs hMB hV hcoef
    ⟨by linarith [hσ.2], by linarith [hσ.1, ht.2]⟩

/-- Assembly of `IsAdvectingDrift` from the time-slice bounds and joint continuity. -/
theorem c1_isAdvectingDrift_of_advBounds {m : ℕ} {Cb t : ℝ} {b : ℝ → Euc d → Euc d}
    (hcont : ContinuousOn (fun p : ℝ × Euc d => b p.1 p.2) (Set.Icc 0 t ×ˢ Set.univ))
    (hb : ∀ σ ∈ Set.Icc (0 : ℝ) t, AdvBounds m Cb (b σ)) : IsAdvectingDrift m Cb t b :=
  ⟨hcont, fun σ hσ => (hb σ hσ).smooth, fun σ hσ j h1 h2 x => (hb σ hσ).deriv_bdd j h1 h2 x,
    fun σ hσ x => (hb σ hσ).growth x⟩

/-- **`IsAdvectingDrift` for the mean-field drift**, given the joint continuity of `(σ,x) ↦ b^σ(x)`
(to be supplied by packet C2). -/
theorem c1_isAdvectingDrift (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (MB Λ ΛV G₀ : ℝ) {D : WholeDyn d} {ρ : ℝ → Euc d → ℝ} {T : ℝ} (hDs : D.s = s)
    (hMB : HRS.PDE.MatBound MB D.M) (hV : VHypRd (m + 3) ΛV G₀ D.V)
    (hcoef : CoeffHypRd s m Λ T ρ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T)
    (hcont : ContinuousOn (fun p : ℝ × Euc d => meanFieldDriftW D (ρ (t - p.1)) p.2)
      (Set.Icc 0 t ×ˢ Set.univ)) :
    IsAdvectingDrift m (c1Cb d s m MB Λ ΛV G₀) t (fun σ => meanFieldDriftW D (ρ (t - σ))) :=
  c1_isAdvectingDrift_of_advBounds hcont (c1_drift_family hd hs0 hsd m MB Λ ΛV G₀ hDs hMB hV hcoef ht)

end HRS.MS.UniqC1

import HRS.MS.Mov63CAux14

/-!
# S6.3, uniqueness chain (N4, final): `mov_nl_unique`

Namespace `HRS.MS.Mov63`.  The uniqueness conjunct of `MovNonlinearConclusion` (`Moving.lean`): two members of
`MovInSmallClass d s q β ρ₀ m r c₀ f0 ·` (any radii, any exponents `c₀`, in particular exponent `0` as in the frozen
statement; `m : ℕ` with `d/2 + 3 < m`, implied by `d/2 + j + 6 < m`, `j ≥ 1`) agree for all `t ≥ 0`.
No smallness of the radius and no decay is used.  Packets N2b/N3a/N3b/N4 of `docs/SC63_REPORT.md` 2.4.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovForce HRS.MS.MovLin HRS.MH.DualityRd

variable {d : ℕ}

/-- **`mov_nl_unique`** (S6.3 uniqueness, packets N2b–N4). -/
theorem mov_nl_unique {s β q : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β) (hq : 0 < q)
    {ρ₀ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s q β ρ₀) {m : ℕ} (hm : (d : ℝ) / 2 + 3 < m)
    {r₁ r₂ c₁ c₂ : ℝ} {f0 : Euc d → ℝ} {P₁ P₂ : ℝ → Euc d → ℝ}
    (h₁ : MovInSmallClass d s q β ρ₀ m r₁ c₁ f0 P₁) (h₂ : MovInSmallClass d s q β ρ₀ m r₂ c₂ f0 P₂) :
    ∀ t : ℝ, 0 ≤ t → P₁ t = P₂ t := by
  have H : Mov2dTh d s β q ρ₀ := ⟨hd, hs0, hsd, hβ, hq, hρ⟩
  intro t ht
  have hpos := (mnb_rhoData H).pos
  have hw : mnc_w ρ₀ P₁ P₂ m t = 0 :=
    mnc_w_zero H hm hβ hq h₁ h₂ (T := t + 1) (by linarith) t ⟨ht, by linarith⟩
  have hu : mnc_u ρ₀ P₁ m t = mnc_u ρ₀ P₂ m t := sub_eq_zero.1 hw
  have hmem₁ := (h₁.weighted t ht).1
  have hmem₂ := (h₂.weighted t ht).1
  have h1 : OscSpace.toLp (OscSpace.ofFun (m : ℝ) (movV ρ₀ P₁ t)) =
      OscSpace.toLp (OscSpace.ofFun (m : ℝ) (movV ρ₀ P₂ t)) := by
    unfold mnc_u at hu; rw [hu]
  rw [OscSpace.toLp_ofFun _ hmem₁, OscSpace.toLp_ofFun _ hmem₂] at h1
  have h2 : movV ρ₀ P₁ t =ᵐ[(volume : Measure (Euc d))] movV ρ₀ P₂ t :=
    (MemLp.toLp_eq_toLp_iff hmem₁.1 hmem₂.1).1 h1
  have h3 : movV ρ₀ P₁ t = movV ρ₀ P₂ t :=
    mn_ae_eq_cont (mnc_movV_cont H h₁ ht) (mnc_movV_cont H h₂ ht) h2
  funext y
  have hs : 0 < Real.sqrt (ρ₀ y) := Real.sqrt_pos.2 (hpos y)
  have key : ∀ (P : ℝ → Euc d → ℝ), P t y = ρ₀ y + Real.sqrt (ρ₀ y) * movV ρ₀ P t y := by
    intro P
    simp only [movV]
    field_simp
    ring
  rw [key P₁, key P₂, h3]

/-- The uniqueness conjunct of `MovNonlinearConclusion` (exponent `0`): a member of the class with exponent `c₀`
is the unique member of the exponent-`0` class of radius `r`, for the same initial datum. -/
theorem mov_nl_unique_conjunct {s β q : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β) (hq : 0 < q)
    {ρ₀ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s q β ρ₀) {j m : ℕ} (hj : 1 ≤ j)
    (hm : (d : ℝ) / 2 + j + 6 < m) {r c₀ : ℝ} {f0 : Euc d → ℝ} {P : ℝ → Euc d → ℝ}
    (hP : MovInSmallClass d s q β ρ₀ m r c₀ f0 P) :
    ∀ P' : ℝ → Euc d → ℝ, MovInSmallClass d s q β ρ₀ m r 0 f0 P' → ∀ t : ℝ, 0 ≤ t → P' t = P t := by
  intro P' hP' t ht
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  exact mov_nl_unique hd hs0 hsd hβ hq hρ (by linarith) hP' hP t ht

end HRS.MS.Mov63

import HRS.MS.ToriCoefAAux4

/-!
# MS-TORI-COEFA: part A of `expanding_tori_coefficients` (S.A.34, coefficient part, conjuncts 1-3)

The frozen statement `HRS.Whole.AppendixALemmas.expanding_tori_coefficients` has six conjuncts; this file proves
the first three (`Z_L > 0`, the `μ_L` bounds, the `V_L` bounds), with the existential `Λ' C L₀` replaced by
`Λ' L₀` and the drift conjuncts removed.  All hypotheses and `let`s are kept verbatim (`hM`, `hγ` unused).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ToriCoefA

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

variable {d : ℕ}

/-- The constant `Λ'` of part A: `∑_{j ≤ n} (2 S_j + V_j)`. -/
def tca_Lam (d : ℕ) (Kz : ℕ → ℝ) (W M : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), (2 * tca_S d Kz W j + tca_Vb Kz M j)

theorem expanding_tori_coefficients_A_proof (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (T Λ ΛV MB G₀ V₀ : ℝ) (ζ : Euc d → ℝ) (hζ : IsCutoffRad (1 / 4) (1 / 3) ζ) :
    ∃ Λ' L₀ : ℝ, ∀ (M : Matrix (Fin d) (Fin d) ℝ) (V : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ),
      PDE.MatBound MB M → VHypRd (m + 3) ΛV G₀ V → |V 0| ≤ V₀ → CoeffHypRd s m Λ T ρ →
      ∀ γ : ℝ → Euc d → ℝ, (∀ L : ℝ, 1 ≤ L → IsPeriodicRieszKernel d s L (γ L)) →
      let μL : ℝ → ℝ → Euc d → ℝ := fun L t =>
        perL L fun x => (∫ y, ζ (L⁻¹ • y) * ρ t y)⁻¹ * (ζ (L⁻¹ • x) * ρ t x)
      let VL : ℝ → Euc d → ℝ := fun L => perL L fun x => ζ (L⁻¹ • x) * V x
      ∀ L : ℝ, max 1 L₀ ≤ L → ∀ t ∈ Set.Icc (0 : ℝ) T,
        (0 < ∫ y, ζ (L⁻¹ • y) * ρ t y) ∧
        (ContDiff ℝ ((m + 3 : ℕ) : WithTop ℕ∞) (μL L t) ∧ MemCb (m + 3) (μL L t) ∧
          cbNorm (m + 3) (μL L t) ≤ Λ' ∧
          ∀ j ≤ m + 3, ∀ x : Euc d, ‖x‖ ≤ L / 2 →
            jbracket x ^ ((d : ℝ) + 3) * ‖iteratedFDeriv ℝ j (μL L t) x‖ ≤ Λ') ∧
        (ContDiff ℝ ∞ (VL L) ∧
          ∀ j : ℕ, 2 ≤ j → j ≤ m + 3 → ∀ x : Euc d, ‖iteratedFDeriv ℝ j (VL L) x‖ ≤ Λ') := by
  choose K hK0 hK using fun i : ℕ => tca_bdd_iter ζ hζ i
  obtain ⟨N, hN⟩ := tca_tail (d := d) (1 / (2 * (|Λ| + 1))) (by positivity)
  have hBε : |Λ| * (1 / (2 * (|Λ| + 1))) ≤ 1 / 2 := by
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    nlinarith [abs_nonneg Λ]
  refine ⟨tca_Lam d K |Λ| (|V₀| + |G₀| + |ΛV|) (m + 3), 4 * (N : ℝ), ?_⟩
  intro M V ρ _hM hV hV0 hρ γ _hγ μL VL L hL t ht
  have hL1 : 1 ≤ L := le_trans (le_max_left 1 _) hL
  have hL4 : (N : ℝ) ≤ L / 4 := by
    have := le_trans (le_max_right 1 (4 * (N : ℝ))) hL
    linarith
  have hL0 : 0 < L := by linarith
  -- the density `ρ t`
  have hprob : HRS.Whole.IsProbDensity (ρ t) := hρ.prob t ht
  obtain ⟨hMC, hWfin, hWle⟩ := hρ.regular.1 t ht
  have hcb0 : 0 ≤ cbNorm (m + 3) (ρ t) :=
    Finset.sum_nonneg fun j _ => Real.iSup_nonneg fun z => norm_nonneg _
  have hWle' : (weightedSupE (m + 3) ((d : ℝ) + 3) (ρ t)).toReal ≤ |Λ| := by
    have := le_abs_self Λ
    linarith
  have hWk : ∀ k : ℕ, k ≤ m + 3 → ∀ w : Euc d,
      jbracket w ^ ((d : ℝ) + 3) * ‖iteratedFDeriv ℝ k (ρ t) w‖ ≤ (d : ℝ) ^ k * |Λ| := fun k hk w =>
    (tca_weight_le (m + 3) ((d : ℝ) + 3) (ρ t) hWfin.ne k hk w).trans
      (mul_le_mul_of_nonneg_left hWle' (pow_nonneg (Nat.cast_nonneg d) _))
  have hρB : ∀ y : Euc d, |ρ t y| ≤ |Λ| * tca_g y := by
    intro y
    exact tca_abs_le_weight (ρ t) |Λ| (fun y' => by
      have := hWk 0 (Nat.zero_le _) y'
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, pow_zero, one_mul] at this
      exact this) y
  -- the normalization `Z_L ≥ 1/2`
  have hZ : 1 / 2 ≤ ∫ y, ζ (L⁻¹ • y) * ρ t y :=
    tca_Z_ge hζ (ρ t) hprob |Λ| (abs_nonneg _) hρB L hL0 N hL4 _ hN hBε
  have hc0 : 0 < (∫ y, ζ (L⁻¹ • y) * ρ t y)⁻¹ := inv_pos.2 (by linarith)
  have hc2 : (∫ y, ζ (L⁻¹ • y) * ρ t y)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ (by linarith)]
    linarith
  have hμdef : μL L t = perL L (fun x => (∫ y, ζ (L⁻¹ • y) * ρ t y)⁻¹ * (ζ (L⁻¹ • x) * ρ t x)) := rfl
  have hVdef : VL L = perL L (fun x => ζ (L⁻¹ • x) * V x) := rfl
  obtain ⟨hcd, hglob, hloc⟩ := tca_mu_package hζ L hL1 (m + 3) (ρ t) hMC.1 K hK hK0 |Λ|
    (abs_nonneg _) hWk _ hc0 hc2
  have hS0 : ∀ j : ℕ, 0 ≤ tca_S d K |Λ| j := fun j => tca_S_nonneg d K hK0 |Λ| (abs_nonneg _) j
  have hVb0 : ∀ j : ℕ, 0 ≤ tca_Vb K (|V₀| + |G₀| + |ΛV|) j :=
    fun j => tca_Vb_nonneg K hK0 _ (by positivity) j
  have hT0 : ∀ j : ℕ, 0 ≤ 2 * tca_S d K |Λ| j + tca_Vb K (|V₀| + |G₀| + |ΛV|) j :=
    fun j => by linarith [hS0 j, hVb0 j]
  -- the single term bound for `Λ'`
  have hTle : ∀ j : ℕ, j ≤ m + 3 →
      2 * tca_S d K |Λ| j + tca_Vb K (|V₀| + |G₀| + |ΛV|) j ≤ tca_Lam d K |Λ| (|V₀| + |G₀| + |ΛV|) (m + 3) := by
    intro j hj
    unfold tca_Lam
    exact Finset.single_le_sum (fun i _ => hT0 i) (Finset.mem_range.2 (by omega))
  have hV2 : ∀ x : Euc d, ‖iteratedFDeriv ℝ 2 V x‖ ≤ ΛV := fun x => hV.2.1 2 le_rfl (by omega) x
  have hVk : ∀ k : ℕ, 2 ≤ k → k ≤ m + 3 → ∀ x : Euc d, ‖iteratedFDeriv ℝ k V x‖ ≤ ΛV :=
    fun k hk hkm x => hV.2.1 k hk hkm x
  have hV3 : ‖gradient V 0‖ ≤ G₀ := hV.2.2
  have hΛ0 : 0 ≤ ΛV := (norm_nonneg _).trans (hV2 0)
  have hG0 : 0 ≤ G₀ := (norm_nonneg _).trans hV3
  have hV0₀ : 0 ≤ V₀ := (abs_nonneg _).trans hV0
  have hMabs : V₀ + G₀ + ΛV ≤ |V₀| + |G₀| + |ΛV| := by
    linarith [le_abs_self V₀, le_abs_self G₀, le_abs_self ΛV]
  have hζL : ContDiff ℝ ∞ (fun z : Euc d => ζ (L⁻¹ • z)) := hζ.1.comp (contDiff_id.const_smul L⁻¹)
  have hvan : ∀ y : Euc d, L / 3 ≤ ‖y‖ → ζ (L⁻¹ • y) * V y = 0 := fun y hy => by
    rw [tca_zeta_far_val hζ L hL0 y hy, zero_mul]
  refine ⟨lt_of_lt_of_le (by norm_num) hZ, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [hμdef]
    exact hcd
  · rw [hμdef]
    exact ⟨hcd, fun j hj => ⟨2 * tca_S d K |Λ| j, by rintro _ ⟨x, rfl⟩; exact hglob j hj x⟩⟩
  · rw [hμdef]
    unfold HRS.cbNorm
    unfold tca_Lam
    apply Finset.sum_le_sum
    intro j hj
    rw [Finset.mem_range] at hj
    have h1 : ⨆ z : Euc d, ‖iteratedFDeriv ℝ j
        (perL L (fun x => (∫ y, ζ (L⁻¹ • y) * ρ t y)⁻¹ * (ζ (L⁻¹ • x) * ρ t x))) z‖ ≤
        2 * tca_S d K |Λ| j := ciSup_le fun z => hglob j (by omega) z
    linarith [hVb0 j]
  · intro j hj x hx
    rw [hμdef]
    exact (hloc j hj x hx).trans (by linarith [hVb0 j, hTle j hj])
  · rw [hVdef]
    exact tca_perL_contDiff ∞ L hL0 _ (hζL.mul hV.1) hvan
  · intro j hj2 hjm x
    rw [hVdef]
    refine (tca_perL_norm_le L hL0 _ hvan j _
      (fun w => tca_VL_bound hζ L hL1 (m + 3) V hV.1 ΛV G₀ V₀ hΛ0 hG0 hV0₀ hVk hV2 hV3 hV0 K hK hK0
        _ hMabs j hj2 hjm w) x).trans ?_
    linarith [hS0 j, hTle j hjm]


end HRS.MS.ToriCoefA

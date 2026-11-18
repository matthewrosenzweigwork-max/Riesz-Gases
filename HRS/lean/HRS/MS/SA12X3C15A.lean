import HRS.MS.SA12BuildC13

/-!
# S.A.12 C15 (SA12X3), part A: the integral cell Gronwall bound with an integrable (not continuous) cell rate

`cell_sup_dissipation` (C13) asks for a continuous derivative `g i`.  For a periodic solution with a drift `b` that is only
jointly continuous (the `x`-derivatives of `b` are not assumed continuous in time) the cell rate `cellRate` is the derivative of
the cell energy everywhere (C8) but its continuity in time is not available; the integrated inequality only needs
`g i` integrable.  Proof: that of C13 with `intervalIntegrable` in place of continuity.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

theorem sa12x3_ftc_int (t : ℝ) (f g : ℝ → ℝ) (hcont : ContinuousOn f (Icc (0 : ℝ) t))
    (hderiv : ∀ τ ∈ Icc (0 : ℝ) t, HasDerivWithinAt f (g τ) (Icc (0 : ℝ) t) τ)
    (hgint : IntegrableOn g (Icc (0 : ℝ) t)) (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) t) :
    ∫ σ in Icc (0 : ℝ) τ, g σ = f τ - f 0 := by
  have hsub : Icc (0 : ℝ) τ ⊆ Icc (0 : ℝ) t := Icc_subset_Icc_right hτ.2
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hτ.1]
  refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hτ.1 (hcont.mono hsub)
    (fun x hx => ?_) ((intervalIntegrable_iff_integrableOn_Icc_of_le hτ.1).2 (hgint.mono_set hsub))
  have hxt : x ∈ Ioo (0 : ℝ) t := ⟨hx.1, hx.2.trans_le hτ.2⟩
  exact ((hderiv x ⟨hx.1.le, hxt.2.le⟩).hasDerivAt (Icc_mem_nhds hxt.1 hxt.2)).hasDerivWithinAt

/-- C13: integrate the cell inequality before taking suprema. The
continuous derivative premise is supplied by the smooth approximants. -/
theorem sa12x3_cell_sup_dissipation_int {ι : Type*} (t A ν κ : ℝ) (N : ℕ) (hA : 0 ≤ A) (hκ : 0 ≤ κ) (hν : 0 ≤ ν)
    (hκN : κ * N ≤ ν / 2) (nb : ι → Finset ι) (hnb : ∀ i, (nb i).card ≤ N) (f g D : ι → ℝ → ℝ) (h : ℝ → ℝ)
    (hnn : ∀ i, ∀ τ ∈ Icc (0 : ℝ) t, 0 ≤ f i τ) (hDnn : ∀ i, ∀ τ ∈ Icc (0 : ℝ) t, 0 ≤ D i τ)
    (hbdd : ∃ B : ℝ, ∀ i, ∀ τ ∈ Icc (0 : ℝ) t, f i τ ≤ B)
    (hDint : ∀ i, IntegrableOn (D i) (Icc (0 : ℝ) t))
    (hDbdd : ∃ B : ℝ, ∀ i, ∫ σ in Icc (0 : ℝ) t, D i σ ≤ B)
    (hcont : ∀ i, ContinuousOn (f i) (Icc (0 : ℝ) t))
    (hderiv : ∀ i, ∀ τ ∈ Icc (0 : ℝ) t, HasDerivWithinAt (f i) (g i τ) (Icc (0 : ℝ) t) τ)
    (hgint : ∀ i, IntegrableOn (g i) (Icc (0 : ℝ) t))
    (hh0 : ∀ τ ∈ Icc (0 : ℝ) t, 0 ≤ h τ) (hhint : IntegrableOn h (Icc (0 : ℝ) t))
    (hineq : ∀ i, ∀ τ ∈ Icc (0 : ℝ) t, g i τ ≤ -ν * D i τ + κ * ∑ j ∈ nb i, D j τ + A * (⨆ j, f j τ) + h τ) :
    ∀ τ ∈ Icc (0 : ℝ) t, (⨆ i, f i τ) ≤ 2 * Real.exp (2 * A * τ) * ((⨆ i, f i 0) + ∫ σ in Icc (0 : ℝ) τ, h σ) := by
  intro τ₀ hτ₀
  have ht : 0 ≤ t := hτ₀.1.trans hτ₀.2
  obtain ⟨Bf, hBf⟩ := hbdd
  obtain ⟨BD, hBD⟩ := hDbdd
  have hBf0 : 0 ≤ max Bf 0 := le_max_right _ _
  set S : ℝ → ℝ := fun σ => ⨆ i, f i σ with hS
  have hbddf : ∀ σ ∈ Icc (0 : ℝ) t, BddAbove (range fun i => f i σ) := fun σ hσ =>
    ⟨max Bf 0, by rintro _ ⟨j, rfl⟩; exact (hBf j σ hσ).trans (le_max_left _ _)⟩
  have hSnn : ∀ σ ∈ Icc (0 : ℝ) t, 0 ≤ S σ := fun σ hσ => Real.iSup_nonneg fun i => hnn i σ hσ
  have hSle : ∀ σ ∈ Icc (0 : ℝ) t, S σ ≤ max Bf 0 := fun σ hσ =>
    Real.iSup_le (fun i => (hBf i σ hσ).trans (le_max_left _ _)) hBf0
  have hfS : ∀ i, ∀ σ ∈ Icc (0 : ℝ) t, f i σ ≤ S σ := fun i σ hσ => le_ciSup (hbddf σ hσ) i
  have hSmeas : AEStronglyMeasurable S (volume.restrict (Icc (0 : ℝ) t)) :=
    sa12c13_sup_aesm t ht f hcont (max Bf 0) (fun i σ hσ => (hBf i σ hσ).trans (le_max_left _ _))
  have hSint : IntegrableOn S (Icc (0 : ℝ) t) := by
    refine Integrable.of_bound (C := max Bf 0) hSmeas ?_
    refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun σ hσ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hSnn σ hσ)]
    exact hSle σ hσ
  have hsubt : ∀ τ ∈ Icc (0 : ℝ) t, Icc (0 : ℝ) τ ⊆ Icc (0 : ℝ) t := fun τ hτ =>
    Icc_subset_Icc_right hτ.2
  -- S₀ = sup of the initial values
  have h0t : (0 : ℝ) ∈ Icc (0 : ℝ) t := ⟨le_rfl, ht⟩
  set S0 : ℝ := ⨆ i, f i 0 with hS0
  have hS0nn : 0 ≤ S0 := Real.iSup_nonneg fun i => hnn i 0 h0t
  have hfS0 : ∀ i, f i 0 ≤ S0 := fun i => le_ciSup (hbddf 0 h0t) i
  -- the one-step estimate at every time
  have hstep : ∀ τ ∈ Icc (0 : ℝ) t, S τ ≤
      2 * (S0 + A * (∫ σ in Icc (0 : ℝ) τ, S σ) + ∫ σ in Icc (0 : ℝ) τ, h σ) := by
    intro τ hτ
    have hsub := hsubt τ hτ
    have hSτ : IntegrableOn S (Icc (0 : ℝ) τ) := hSint.mono_set hsub
    have hhτ : IntegrableOn h (Icc (0 : ℝ) τ) := hhint.mono_set hsub
    set I : ι → ℝ := fun j => ∫ σ in Icc (0 : ℝ) τ, D j σ with hI
    have hI0 : ∀ j, 0 ≤ I j := fun j =>
      setIntegral_nonneg measurableSet_Icc fun σ hσ => hDnn j σ (hsub hσ)
    have hIle : ∀ j, I j ≤ max BD 0 := fun j => by
      have : I j ≤ ∫ σ in Icc (0 : ℝ) t, D j σ :=
        setIntegral_mono_set (hDint j)
          ((ae_restrict_iff' measurableSet_Icc).2
            (Filter.Eventually.of_forall fun σ hσ => hDnn j σ hσ))
          (Filter.Eventually.of_forall hsub)
      exact this.trans ((hBD j).trans (le_max_left _ _))
    set Ds : ℝ := ⨆ j, I j with hDs
    have hDs0 : 0 ≤ Ds := Real.iSup_nonneg hI0
    have hIDs : ∀ j, I j ≤ Ds := fun j =>
      le_ciSup (⟨max BD 0, by rintro _ ⟨k, rfl⟩; exact hIle k⟩ : BddAbove (range I)) j
    set R : ℝ := A * (∫ σ in Icc (0 : ℝ) τ, S σ) + ∫ σ in Icc (0 : ℝ) τ, h σ with hR
    have hR0 : 0 ≤ R := by
      have h1 : 0 ≤ ∫ σ in Icc (0 : ℝ) τ, S σ :=
        setIntegral_nonneg measurableSet_Icc fun σ hσ => hSnn σ (hsub hσ)
      have h2 : 0 ≤ ∫ σ in Icc (0 : ℝ) τ, h σ :=
        setIntegral_nonneg measurableSet_Icc fun σ hσ => hh0 σ (hsub hσ)
      rw [hR]; exact add_nonneg (mul_nonneg hA h1) h2
    -- the integrated inequality for each cell
    have hkey : ∀ i, f i τ ≤ f i 0 - ν * I i + κ * ∑ j ∈ nb i, I j + R := by
      intro i
      have hftc := sa12x3_ftc_int t (f i) (g i) (hcont i) (hderiv i) (hgint i) τ hτ
      have hDi : ∀ j, IntegrableOn (D j) (Icc (0 : ℝ) τ) := fun j => (hDint j).mono_set hsub
      have hsumint : IntegrableOn (fun σ => ∑ j ∈ nb i, D j σ) (Icc (0 : ℝ) τ) :=
        integrable_finsetSum _ fun j _ => hDi j
      have hrhs : IntegrableOn (fun σ => -ν * D i σ + κ * ∑ j ∈ nb i, D j σ + A * S σ + h σ)
          (Icc (0 : ℝ) τ) :=
        ((((hDi i).const_mul (-ν)).add (hsumint.const_mul κ)).add (hSτ.const_mul A)).add hhτ
      have hgint : IntegrableOn (g i) (Icc (0 : ℝ) τ) :=
        (hgint i).mono_set hsub
      have hle : ∫ σ in Icc (0 : ℝ) τ, g i σ ≤
          ∫ σ in Icc (0 : ℝ) τ, (-ν * D i σ + κ * ∑ j ∈ nb i, D j σ + A * S σ + h σ) :=
        setIntegral_mono_on hgint hrhs measurableSet_Icc fun σ hσ => hineq i σ (hsub hσ)
      have i1 : IntegrableOn (fun σ => -ν * D i σ) (Icc (0 : ℝ) τ) := (hDi i).const_mul _
      have i2 : IntegrableOn (fun σ => κ * ∑ j ∈ nb i, D j σ) (Icc (0 : ℝ) τ) := hsumint.const_mul _
      have i3 : IntegrableOn (fun σ => A * S σ) (Icc (0 : ℝ) τ) := hSτ.const_mul _
      have i12 : IntegrableOn (fun σ => -ν * D i σ + κ * ∑ j ∈ nb i, D j σ) (Icc (0 : ℝ) τ) :=
        i1.add i2
      have i123 : IntegrableOn (fun σ => -ν * D i σ + κ * ∑ j ∈ nb i, D j σ + A * S σ)
          (Icc (0 : ℝ) τ) := i12.add i3
      have hcalc : ∫ σ in Icc (0 : ℝ) τ, (-ν * D i σ + κ * ∑ j ∈ nb i, D j σ + A * S σ + h σ) =
          -ν * I i + κ * ∑ j ∈ nb i, I j + R := by
        rw [integral_add i123 hhτ, integral_add i12 i3, integral_add i1 i2,
          integral_const_mul, integral_const_mul, integral_const_mul,
          integral_finsetSum _ (fun j _ => hDi j)]
        simp only [hI, hR]
        ring
      rw [hftc, hcalc] at hle
      linarith
    have hsumle : ∀ i, κ * ∑ j ∈ nb i, I j ≤ κ * N * Ds := by
      intro i
      have h1 : ∑ j ∈ nb i, I j ≤ (nb i).card * Ds := by
        have := Finset.sum_le_card_nsmul (nb i) I Ds (fun j _ => hIDs j)
        simpa [nsmul_eq_mul] using this
      have h2 : ((nb i).card : ℝ) * Ds ≤ N * Ds :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hnb i) hDs0
      calc κ * ∑ j ∈ nb i, I j ≤ κ * (N * Ds) :=
            mul_le_mul_of_nonneg_left (h1.trans h2) hκ
        _ = κ * N * Ds := by ring
    -- absorption of the neighbouring dissipation
    have habs : κ * N * Ds ≤ S0 + R := by
      rcases hν.eq_or_lt with hν0 | hνpos
      · have : κ * N = 0 := le_antisymm (by rw [← hν0] at hκN; simpa using hκN)
          (by positivity)
        rw [this, zero_mul]; linarith
      · have hX : ∀ i, ν * I i ≤ S0 + κ * N * Ds + R := by
          intro i
          have h1 := hkey i
          have h2 := hsumle i
          have h3 := hnn i τ hτ
          have h4 := hfS0 i
          linarith
        have hX0 : 0 ≤ (S0 + κ * N * Ds + R) / ν := by positivity
        have hDsle : Ds ≤ (S0 + κ * N * Ds + R) / ν :=
          Real.iSup_le (fun i => by rw [le_div_iff₀ hνpos, mul_comm]; exact hX i) hX0
        rw [le_div_iff₀ hνpos] at hDsle
        have h5 : κ * N * Ds ≤ ν / 2 * Ds := mul_le_mul_of_nonneg_right hκN hDs0
        nlinarith
    have hbound : ∀ i, f i τ ≤ 2 * (S0 + R) := by
      intro i
      have h1 := hkey i
      have h2 := hsumle i
      have h4 := hfS0 i
      have h5 : 0 ≤ ν * I i := mul_nonneg hν (hI0 i)
      linarith
    have : S τ ≤ 2 * (S0 + R) := Real.iSup_le hbound (by positivity)
    calc S τ ≤ 2 * (S0 + R) := this
      _ = 2 * (S0 + A * (∫ σ in Icc (0 : ℝ) τ, S σ) + ∫ σ in Icc (0 : ℝ) τ, h σ) := by
          linarith [hR]
  -- Gronwall on `[0, τ₀]`
  have hsub0 := hsubt τ₀ hτ₀
  set δ : ℝ := 2 * (S0 + ∫ σ in Icc (0 : ℝ) τ₀, h σ) with hδ
  have hh0int : 0 ≤ ∫ σ in Icc (0 : ℝ) τ₀, h σ :=
    setIntegral_nonneg measurableSet_Icc fun σ hσ => hh0 σ (hsub0 hσ)
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  have hgron := HRS.MS.UniqG1.g1_gronwall_source_paren S τ₀ (2 * A) δ (by positivity) hδ0
    (fun σ hσ => hSnn σ (hsub0 hσ)) ⟨max Bf 0, fun σ hσ => hSle σ (hsub0 hσ)⟩
    (hSmeas.mono_set hsub0) (fun σ hσ => by
      have hσt : σ ∈ Icc (0 : ℝ) t := hsub0 hσ
      have h1 := hstep σ hσt
      have hσσ : Icc (0 : ℝ) σ ⊆ Icc (0 : ℝ) τ₀ := Icc_subset_Icc_right hσ.2
      have hhle : ∫ s in Icc (0 : ℝ) σ, h s ≤ ∫ s in Icc (0 : ℝ) τ₀, h s :=
        setIntegral_mono_set (hhint.mono_set hsub0)
          ((ae_restrict_iff' measurableSet_Icc).2
            (Filter.Eventually.of_forall fun s hs => hh0 s (hsub0 hs)))
          (Filter.Eventually.of_forall hσσ)
      have hconv : ∫ s in (0 : ℝ)..σ, S s = ∫ s in Icc (0 : ℝ) σ, S s := by
        rw [intervalIntegral.integral_of_le hσ.1, integral_Icc_eq_integral_Ioc]
      have h1' : S σ ≤ 2 * (S0 + A * (∫ s in Icc (0 : ℝ) σ, S s) + ∫ s in Icc (0 : ℝ) σ, h s) := h1
      rw [hconv, hδ]
      linarith [h1', hhle])
  have := hgron τ₀ ⟨hτ₀.1, le_rfl⟩
  calc (⨆ i, f i τ₀) = S τ₀ := rfl
    _ ≤ δ * Real.exp (2 * A * τ₀) := this
    _ = 2 * Real.exp (2 * A * τ₀) * ((⨆ i, f i 0) + ∫ σ in Icc (0 : ℝ) τ₀, h σ) := by
        rw [hδ, hS0]; ring

end HRS.MH.AdjointRd.Phase2SA12Construction

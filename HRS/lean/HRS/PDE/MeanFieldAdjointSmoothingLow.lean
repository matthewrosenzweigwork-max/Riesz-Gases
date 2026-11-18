import HRS.PDE.MeanFieldAdjointSmoothing

/-!
# Frozen smoothing and `H^j` decay at the low levels `d/2 + 4 < j` (package MF-01, packet P11b-low)

`exists_frozen_hj_decay'` and `exists_frozen_smoothing'` are the statements of
`exists_frozen_hj_decay` and `exists_frozen_smoothing` in `MeanFieldAdjointSmoothing.lean` with the
level hypothesis `mStar d + 4 ≤ j` weakened to `(d : ℝ) / 2 + 4 < j` (equivalently
`mStar d + 2 ≤ j`, i.e. `j ≥ ⌊d/2⌋ + 5`); the coefficient regularity `FrozenHyp d s (j + mStar d)` is
unchanged.

Route (a): re-run the chain with the weaker level.  Where `mStar d + 4 ≤ j` was used:
* `center_chain`, `S_facts`, `P_facts`, `exists_frozen_hj_decay`, `frozen_smooth_H`: only through
  `mStar d + 2 ≤ j` (so that `S_eq`/`proj_data`/`exists_frozen_l2_decay` apply at level `j`) and
  `2 ≤ j - aExp d s` (true since `aExp < 2`, `j ≥ 5`).  These are re-proved verbatim.
* `frozen_density`: it used `mStar d + 2 ≤ j - aExp d s` to apply `S_eq` and the `L²` decay to
  `H^{j-a}` data and to the truncation differences.  At the low levels `j - a` only exceeds `mStar d`.
  We instead take the classical base level `mStar d` (`S_eq_low`, valid for `τ > 0` with
  `mStar d ≤ m`), and replace the `L²` decay of the differences by the qualitative finite-time bound
  `exists_frozenCoeff_bound` at level `mStar d` (the coordinatewise convergence at a fixed time
  `τ` does not need decay).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.MFAdjoint

variable {d : ℕ}

theorem mStar_add_two_le_of_gt {j : ℕ} (hj : (d : ℝ) / 2 + 4 < j) : mStar d + 2 ≤ j := by
  have h0 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  have h1 : ((⌊(d : ℝ) / 2⌋₊ : ℕ) : ℝ) ≤ (d : ℝ) / 2 := Nat.floor_le h0
  have h2 : ((⌊(d : ℝ) / 2⌋₊ + 4 : ℕ) : ℝ) < (j : ℝ) := by push_cast; linarith
  have h3 : ⌊(d : ℝ) / 2⌋₊ + 4 < j := by exact_mod_cast h2
  unfold mStar
  omega

section Low

/-- The chain of `⌈j/a⌉` unit-time centered smoothing steps (each of length `1/N`) from the
`L²` level to the `H^j` level over unit time, with constant `P` uniform in `β, V, ρβ, ψ`. -/
theorem center_chain' (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (j : ℕ)
    (hj : mStar d + 2 ≤ j) (νm νp c₀ Λ₀ : ℝ) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ (β : ℝ) (V ρβ : Torus d → ℝ)
      (H : FrozenHyp d s (j + mStar d) νm νp c₀ Λ₀ β V ρβ) (ψc : Coeff d), MemHs (j : ℝ) ψc →
      ∀ v₀ : ℝ, 0 ≤ v₀ →
        hsNorm (j : ℝ) (centerCoeff ρβ
            (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j ψc (v₀ + 1))) ≤
          P * hsNorm 0 (centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j ψc v₀)) := by
  have h3 := ClassicalPart.three_le_mStar d
  have hj1 : 1 ≤ j := by omega
  have ha := aExp_spec (d := d) s hsd
  have ha0 : 0 < aExp d s := by linarith [ha.1]
  have hjpos : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
  obtain ⟨N, hN1, hNa⟩ : ∃ N : ℕ, 1 ≤ N ∧ (j : ℝ) ≤ (N : ℝ) * aExp d s := by
    refine ⟨⌈(j : ℝ) / aExp d s⌉₊, Nat.ceil_pos.2 (div_pos hjpos ha0), ?_⟩
    have h := Nat.le_ceil ((j : ℝ) / aExp d s)
    rwa [div_le_iff₀ ha0] at h
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < N := by linarith
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = 1 / (N : ℝ) := ⟨_, rfl⟩
  have hδpos : 0 < δ := by rw [hδdef]; exact div_pos one_pos hNpos
  have hδ1 : δ ≤ 1 := by rw [hδdef, div_le_one hNpos]; exact hN1'
  have hNδ : (N : ℝ) * δ = 1 := by rw [hδdef]; field_simp
  have hstep : ∀ k : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ (β : ℝ) (V ρβ : Torus d → ℝ)
      (H : FrozenHyp d s (j + mStar d) νm νp c₀ Λ₀ β V ρβ) (ψc : Coeff d), MemHs (j : ℝ) ψc →
      ∀ v : ℝ, 0 ≤ v → ∀ σ ∈ Set.Ioc (0 : ℝ) 1,
        hsNorm (min (((k : ℝ) + 1) * aExp d s) (j : ℝ))
            (centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j ψc (v + σ))) ≤
          K * σ ^ (-(aExp d s / 2)) *
            hsNorm (min (((k : ℝ) + 1) * aExp d s) (j : ℝ) - aExp d s)
              (centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j ψc v)) := by
    intro k
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have ha1' : (1 : ℝ) ≤ ((k : ℝ) + 1) * aExp d s := by nlinarith [ha.1]
    have hi1 : (1 : ℝ) ≤ min (((k : ℝ) + 1) * aExp d s) (j : ℝ) :=
      le_min ha1' (by exact_mod_cast hj1)
    obtain ⟨K, hK0, hK⟩ := center_step hd s hs0 hsd j hj1 νm νp c₀ Λ₀ _ hi1 (min_le_right _ _)
    exact ⟨K, hK0, hK⟩
  choose K hK0 hKb using hstep
  refine ⟨∏ l ∈ Finset.range N, (K l * δ ^ (-(aExp d s / 2))),
    Finset.prod_nonneg fun l _ => mul_nonneg (hK0 l) (Real.rpow_nonneg hδpos.le _), ?_⟩
  intro β V ρβ H ψc hψ v₀ hv₀
  have hρc : Continuous ρβ := H.cont (by omega)
  have hmem : ∀ v : ℝ, 0 ≤ v → MemHs (j : ℝ)
      (centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j ψc v)) := fun v hv =>
    (centerCoeff_bound' H.thermal.1 hρc H.le_Lam (by positivity)
      (frozen_memHs hd s hs0 hsd j hj1 H hψ hv)).1
  have claim : ∀ k : ℕ, k ≤ N → hsNorm (min ((k : ℝ) * aExp d s) (j : ℝ))
      (centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j ψc (v₀ + (k : ℝ) * δ))) ≤
      (∏ l ∈ Finset.range k, (K l * δ ^ (-(aExp d s / 2)))) *
        hsNorm 0 (centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j ψc v₀)) := by
    intro k
    induction k with
    | zero =>
      intro _
      have e : min (((0 : ℕ) : ℝ) * aExp d s) (j : ℝ) = 0 := by
        rw [Nat.cast_zero, zero_mul]; exact min_eq_left (by positivity)
      rw [e, Nat.cast_zero, zero_mul, add_zero, Finset.prod_range_zero, one_mul]
    | succ k ih =>
      intro hk
      have ihk := ih (by omega)
      have hv : 0 ≤ v₀ + (k : ℝ) * δ := by
        have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        nlinarith
      have hs := hKb k β V ρβ H ψc hψ (v₀ + (k : ℝ) * δ) hv δ ⟨hδpos, hδ1⟩
      have hmono : hsNorm (min (((k : ℝ) + 1) * aExp d s) (j : ℝ) - aExp d s)
          (centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j ψc (v₀ + (k : ℝ) * δ))) ≤
          hsNorm (min ((k : ℝ) * aExp d s) (j : ℝ))
          (centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j ψc (v₀ + (k : ℝ) * δ))) := by
        apply MFApriori.hsNorm_mono_idx
        · apply le_min
          · linarith [min_le_left (((k : ℝ) + 1) * aExp d s) (j : ℝ)]
          · linarith [min_le_right (((k : ℝ) + 1) * aExp d s) (j : ℝ), ha.1]
        · exact (hmem _ hv).mono (min_le_right _ _)
      have e1 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      have e2 : v₀ + ((k + 1 : ℕ) : ℝ) * δ = (v₀ + (k : ℝ) * δ) + δ := by push_cast; ring
      rw [e2, e1, Finset.prod_range_succ]
      have hK := hK0 k
      have hpow : 0 ≤ K k * δ ^ (-(aExp d s / 2)) := mul_nonneg hK (Real.rpow_nonneg hδpos.le _)
      calc _ ≤ K k * δ ^ (-(aExp d s / 2)) *
            hsNorm (min (((k : ℝ) + 1) * aExp d s) (j : ℝ) - aExp d s)
              (centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j ψc (v₀ + (k : ℝ) * δ))) := hs
        _ ≤ K k * δ ^ (-(aExp d s / 2)) *
            hsNorm (min ((k : ℝ) * aExp d s) (j : ℝ))
              (centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j ψc (v₀ + (k : ℝ) * δ))) :=
          mul_le_mul_of_nonneg_left hmono hpow
        _ ≤ K k * δ ^ (-(aExp d s / 2)) * ((∏ l ∈ Finset.range k, (K l * δ ^ (-(aExp d s / 2)))) *
            hsNorm 0 (centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j ψc v₀))) :=
          mul_le_mul_of_nonneg_left ihk hpow
        _ = _ := by ring
  have hfin := claim N le_rfl
  have hmin : min ((N : ℝ) * aExp d s) (j : ℝ) = (j : ℝ) := min_eq_right hNa
  have hv1 : v₀ + (N : ℝ) * δ = v₀ + 1 := by rw [hNδ]
  rw [hmin, hv1] at hfin
  exact hfin

/-- The equilibrium semigroup at level `j` (wrapper of `S_eq` for the `H^j` frozen level). -/
theorem S_facts' (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (j : ℕ) (hj : mStar d + 2 ≤ j)
    {νm νp c₀ Λ₀ β : ℝ} {V ρβ : Torus d → ℝ} (H : FrozenHyp d s (j + mStar d) νm νp c₀ Λ₀ β V ρβ)
    {ψ : Torus d → ℝ} (hψc : Continuous ψ) (hψ : MemSobolev (j : ℝ) ψ) {t : ℝ} (ht : 0 ≤ t) :
    ∀ m' : ℝ, 0 ≤ m' → m' ≤ j →
      MemSobolev m' (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ t ψ) ∧
      sobolevNorm m' (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ t ψ) =
        hsNorm m' (centerCoeff ρβ
          (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j (coeffOf ψ) t)) := by
  have h3 := ClassicalPart.three_le_mStar d
  exact (S_eq hd j (by omega) (H.mono (by omega)) hψc hψ ht).2

/-- The centered datum `projMean ψ` at level `j` (wrapper of `proj_data`). -/
theorem P_facts' (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (j : ℕ) (hj : mStar d + 2 ≤ j)
    {νm νp c₀ Λ₀ β : ℝ} {V ρβ : Torus d → ℝ} (H : FrozenHyp d s (j + mStar d) νm νp c₀ Λ₀ β V ρβ)
    {ψ : Torus d → ℝ} (hψc : Continuous ψ) (hψ : MemSobolev (j : ℝ) ψ) :
    ∀ m' : ℝ, 0 ≤ m' → m' ≤ j →
      MemSobolev m' (projMean (withDensityReal ρβ) ψ) ∧
      sobolevNorm m' (projMean (withDensityReal ρβ) ψ) =
        hsNorm m' (centerCoeff ρβ (coeffOf ψ)) := by
  have h3 := ClassicalPart.three_le_mStar d
  exact (proj_data j (by omega) (H.mono (by omega)) hψc hψ).2


/-- P11b, `H^j` decay of the frozen equilibrium semigroup, at fixed frozen data. -/
theorem frozen_hj_decay_core (hd : 1 ≤ d) (s : ℝ) (j : ℕ) (hj : mStar d + 2 ≤ j) (νm νp c₀ Λ₀ : ℝ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (β : ℝ) (V ρβ : Torus d → ℝ) (H : FrozenHyp d s (j + mStar d) νm νp c₀ Λ₀ β V ρβ),
      ∀ ψ : Torus d → ℝ, Continuous ψ → MemSobolev j ψ → ∀ τ, 0 ≤ τ →
        MemSobolev j (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ ψ) ∧
        sobolevNorm j (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ ψ) ≤
          C * Real.exp (-c * τ) * sobolevNorm j (projMean (withDensityReal ρβ) ψ) := by
  by_cases hsc : 0 ≤ s ∧ s < d
  swap
  · exact ⟨1, 1, one_pos, one_pos, fun β V ρβ H => (hsc ⟨H.hs0, H.hsd⟩).elim⟩
  obtain ⟨hs0, hsd⟩ := hsc
  have h3 := ClassicalPart.three_le_mStar d
  obtain ⟨P, hP0, hP⟩ := center_chain' hd s hs0 hsd j hj νm νp c₀ Λ₀
  obtain ⟨L, hL, hLb⟩ := frozen_fin_bound hd s hs0 hsd j (by omega) c₀ Λ₀
  obtain ⟨CL, cL, hCL, hcL, hL2⟩ := exists_frozen_l2_decay hd s νm νp c₀ Λ₀
  have hK1 : 0 ≤ 2 * (1 + |Λ₀|) * Real.exp L := by positivity
  have hPC : 0 ≤ P * CL := mul_nonneg hP0 hCL.le
  refine ⟨(2 * (1 + |Λ₀|) * Real.exp L + P * CL + 1) * Real.exp cL, cL,
    mul_pos (by linarith) (Real.exp_pos cL), hcL, ?_⟩
  intro β V ρβ H ψ hψc hψ τ hτ
  have hjm : mStar d + 2 ≤ j := by omega
  have hprob : IsProbDensity ρβ := H.thermal.1
  have hρc : Continuous ρβ := H.cont (by omega)
  have hΛ : ∀ x, ρβ x ≤ Λ₀ := H.le_Lam
  have hΛ0 : 0 ≤ Λ₀ := (H.hc₀.le.trans (H.hlow 0)).trans (H.le_Lam 0)
  have hcdat : MemHs (j : ℝ) (coeffOf ψ) := (coeff_data j hjm hψc hψ).1
  have hcc : MemHs (j : ℝ) (centerCoeff ρβ (coeffOf ψ)) :=
    (centerCoeff_bound' hprob hρc hΛ (by positivity) hcdat).1
  have hS := S_facts' hd s hs0 hsd j hj H hψc hψ hτ
  have hPf := P_facts' hd s hs0 hsd j hj H hψc hψ
  have hR : sobolevNorm (j : ℝ) (projMean (withDensityReal ρβ) ψ) =
      hsNorm (j : ℝ) (centerCoeff ρβ (coeffOf ψ)) := (hPf j (by positivity) le_rfl).2
  have hRnn : 0 ≤ hsNorm (j : ℝ) (centerCoeff ρβ (coeffOf ψ)) := MFApriori.hsNorm_nonneg' _ _
  have hψ2 : MemSobolev ((mStar d : ℝ) + 2) ψ :=
    memSobolev_mono_idx hψ (by exact_mod_cast hjm)
  have hE0 : 0 ≤ Real.exp cL * Real.exp (-cL * τ) := by positivity
  rcases le_total τ 1 with hτ1 | hτ1
  · -- regime `τ ≤ 1`: finite-time bound on the centered datum
    have hA := adjointData_frozen' j (by omega) H 0 (τ + 1) (by linarith)
    have hcenter := center_frozen_center hd hs0 hsd (by omega) hA hprob hρc hcdat
      ⟨hτ, by linarith⟩
    have hFcc := frozen_memHs hd s hs0 hsd j (by omega) H hcc hτ
    have hBd := hLb νm νp β V ρβ H _ hcc τ hτ hτ1
    have hYc := (centerCoeff_bound' hprob hρc hΛ (by positivity) hFcc).2
    have h1 : 2 * (1 + Λ₀) ≤ 2 * (1 + |Λ₀|) := by linarith [le_abs_self Λ₀]
    have hYb : hsNorm (j : ℝ) (centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j
        (coeffOf ψ) τ)) ≤ 2 * (1 + |Λ₀|) * Real.exp L * hsNorm (j : ℝ) (centerCoeff ρβ (coeffOf ψ)) := by
      rw [hcenter]
      calc _ ≤ 2 * (1 + Λ₀) * hsNorm (j : ℝ) (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j
            (centerCoeff ρβ (coeffOf ψ)) τ) := hYc
        _ ≤ 2 * (1 + |Λ₀|) * hsNorm (j : ℝ) (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j
            (centerCoeff ρβ (coeffOf ψ)) τ) := mul_le_mul_of_nonneg_right h1 (MFApriori.hsNorm_nonneg' _ _)
        _ ≤ 2 * (1 + |Λ₀|) * (Real.exp L * hsNorm (j : ℝ) (centerCoeff ρβ (coeffOf ψ))) :=
          mul_le_mul_of_nonneg_left hBd (by positivity)
        _ = _ := by ring
    have hEe : 1 ≤ Real.exp cL * Real.exp (-cL * τ) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith [mul_nonneg hcL.le (sub_nonneg.2 hτ1)])
    have hSτ := hS (j : ℝ) (by positivity) le_rfl
    refine ⟨hSτ.1, ?_⟩
    rw [hSτ.2, hR]
    calc _ ≤ 2 * (1 + |Λ₀|) * Real.exp L * hsNorm (j : ℝ) (centerCoeff ρβ (coeffOf ψ)) := hYb
      _ ≤ (2 * (1 + |Λ₀|) * Real.exp L + P * CL + 1) * (Real.exp cL * Real.exp (-cL * τ)) *
            hsNorm (j : ℝ) (centerCoeff ρβ (coeffOf ψ)) := by
          apply mul_le_mul_of_nonneg_right _ hRnn
          have := le_mul_of_one_le_right (by linarith : 0 ≤ 2 * (1 + |Λ₀|) * Real.exp L + P * CL + 1) hEe
          linarith
      _ = _ := by ring
  · -- regime `τ ≥ 1`: one unit-time chain step from the `L²` level at time `τ - 1`
    have hτ0 : 0 ≤ τ - 1 := by linarith
    have hch := hP β V ρβ H (coeffOf ψ) hcdat (τ - 1) hτ0
    rw [sub_add_cancel] at hch
    have hS1 := S_facts' hd s hs0 hsd j hj H hψc hψ hτ0
    have hL2' : sobolevNorm 0 (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ (τ - 1) ψ) ≤
        CL * Real.exp (-cL * (τ - 1)) * sobolevNorm 2 (projMean (withDensityReal ρβ) ψ) :=
      hL2 β V ρβ (H.mono (by omega)) ψ hψc hψ2 (τ - 1) hτ0
    have hR2 : sobolevNorm 2 (projMean (withDensityReal ρβ) ψ) ≤
        hsNorm (j : ℝ) (centerCoeff ρβ (coeffOf ψ)) := by
      rw [(hPf 2 (by norm_num) (by exact_mod_cast (by omega : 2 ≤ j))).2]
      exact MFApriori.hsNorm_mono_idx (by exact_mod_cast (by omega : 2 ≤ j)) hcc
    have hSτ := hS (j : ℝ) (by positivity) le_rfl
    refine ⟨hSτ.1, ?_⟩
    rw [hSτ.2, hR]
    have hS10 := (hS1 0 le_rfl (by positivity)).2
    calc _ ≤ P * hsNorm 0 (centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j
            (coeffOf ψ) (τ - 1))) := hch
      _ = P * sobolevNorm 0 (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ (τ - 1) ψ) := by
          rw [hS10]
      _ ≤ P * (CL * Real.exp (-cL * (τ - 1)) * sobolevNorm 2 (projMean (withDensityReal ρβ) ψ)) :=
          mul_le_mul_of_nonneg_left hL2' hP0
      _ ≤ P * (CL * Real.exp (-cL * (τ - 1)) * hsNorm (j : ℝ) (centerCoeff ρβ (coeffOf ψ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hR2 (by positivity)) hP0
      _ = P * CL * (Real.exp cL * Real.exp (-cL * τ)) *
            hsNorm (j : ℝ) (centerCoeff ρβ (coeffOf ψ)) := by
          rw [show -cL * (τ - 1) = cL + (-cL * τ) by ring, Real.exp_add]; ring
      _ ≤ (2 * (1 + |Λ₀|) * Real.exp L + P * CL + 1) * (Real.exp cL * Real.exp (-cL * τ)) *
            hsNorm (j : ℝ) (centerCoeff ρβ (coeffOf ψ)) := by
          apply mul_le_mul_of_nonneg_right _ hRnn
          exact mul_le_mul_of_nonneg_right (by linarith) hE0
      _ = _ := by ring

/-- Smoothing of the equilibrium semigroup for `H^j` data (unit-time steps; constants uniform). -/
theorem frozen_smooth_H' (hd : 1 ≤ d) (s : ℝ) (j : ℕ) (hj : mStar d + 2 ≤ j) (νm νp c₀ Λ₀ : ℝ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (β : ℝ) (V ρβ : Torus d → ℝ)
      (H : FrozenHyp d s (j + mStar d) νm νp c₀ Λ₀ β V ρβ),
      ∀ ψ : Torus d → ℝ, Continuous ψ → MemSobolev j ψ → ∀ τ : ℝ, 0 < τ →
        MemSobolev j (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ ψ) ∧
        sobolevNorm j (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ ψ) ≤
          C * (1 + τ ^ (-(aExp d s / 2))) * Real.exp (-c * τ) *
            sobolevNorm ((j : ℝ) - aExp d s) (projMean (withDensityReal ρβ) ψ) := by
  by_cases hsc : 0 ≤ s ∧ s < d
  swap
  · exact ⟨1, 1, one_pos, one_pos, fun β V ρβ H => (hsc ⟨H.hs0, H.hsd⟩).elim⟩
  obtain ⟨hs0, hsd⟩ := hsc
  have h3 := ClassicalPart.three_le_mStar d
  have hjpos : 1 ≤ j := by omega
  obtain ⟨P, hP0, hP⟩ := center_chain' hd s hs0 hsd j hj νm νp c₀ Λ₀
  obtain ⟨K, hK0, hK⟩ := center_step hd s hs0 hsd j hjpos νm νp c₀ Λ₀ (j : ℝ)
    (by exact_mod_cast hjpos) le_rfl
  obtain ⟨CL, cL, hCL, hcL, hL2⟩ := exists_frozen_l2_decay hd s νm νp c₀ Λ₀
  have hPC : 0 ≤ P * CL := mul_nonneg hP0 hCL.le
  refine ⟨(K + P * CL + 1) * Real.exp cL, cL, mul_pos (by linarith) (Real.exp_pos cL), hcL, ?_⟩
  intro β V ρβ H ψ hψc hψ τ hτ
  have hjm : mStar d + 2 ≤ j := by omega
  have hprob : IsProbDensity ρβ := H.thermal.1
  have hρc : Continuous ρβ := H.cont (by omega)
  have hΛ : ∀ x, ρβ x ≤ Λ₀ := H.le_Lam
  have hΛ0 : 0 ≤ Λ₀ := (H.hc₀.le.trans (H.hlow 0)).trans (H.le_Lam 0)
  have hcdat : MemHs (j : ℝ) (coeffOf ψ) := (coeff_data j hjm hψc hψ).1
  have hcc : MemHs (j : ℝ) (centerCoeff ρβ (coeffOf ψ)) :=
    (centerCoeff_bound' hprob hρc hΛ (by positivity) hcdat).1
  have hS := S_facts' hd s hs0 hsd j hj H hψc hψ hτ.le
  have hPf := P_facts' hd s hs0 hsd j hj H hψc hψ
  have hA1 : (2 : ℝ) ≤ (j : ℝ) - aExp d s := by
    have ha := aExp_spec (d := d) s hsd
    have : (mStar d : ℝ) + 2 ≤ j := by exact_mod_cast hj
    have : (3 : ℝ) ≤ mStar d := by exact_mod_cast h3
    linarith [ha.2.1]
  have hA0 : 0 ≤ (j : ℝ) - aExp d s := by linarith
  have hAle : (j : ℝ) - aExp d s ≤ j := by linarith [(aExp_spec (d := d) s hsd).1]
  have hRj : sobolevNorm ((j : ℝ) - aExp d s) (projMean (withDensityReal ρβ) ψ) =
      hsNorm ((j : ℝ) - aExp d s) (centerCoeff ρβ (coeffOf ψ)) := (hPf _ hA0 hAle).2
  have hcJA : MemHs ((j : ℝ) - aExp d s) (centerCoeff ρβ (coeffOf ψ)) :=
    (centerCoeff_bound' hprob hρc hΛ hA0 (hcdat.mono hAle)).1
  have hR0 : 0 ≤ hsNorm ((j : ℝ) - aExp d s) (centerCoeff ρβ (coeffOf ψ)) :=
    MFApriori.hsNorm_nonneg' _ _
  have hτ0 : 0 < τ := hτ
  rcases le_total τ 1 with hτ1 | hτ1
  · -- regime `τ ≤ 1`: one centered step from time `0`
    have hstep := hK β V ρβ H (coeffOf ψ) hcdat 0 le_rfl τ ⟨hτ0, hτ1⟩
    rw [zero_add, frozenCoeff_zero hjpos hcdat] at hstep
    have hSτ := hS (j : ℝ) (by positivity) le_rfl
    refine ⟨hSτ.1, ?_⟩
    rw [hSτ.2, hRj]
    have hX : 0 ≤ τ ^ (-(aExp d s / 2)) := Real.rpow_nonneg hτ0.le _
    have hEe : 1 ≤ Real.exp cL * Real.exp (-cL * τ) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith [mul_nonneg hcL.le (sub_nonneg.2 hτ1)])
    calc _ ≤ K * τ ^ (-(aExp d s / 2)) *
          hsNorm ((j : ℝ) - aExp d s) (centerCoeff ρβ (coeffOf ψ)) := hstep
      _ ≤ (K + P * CL + 1) * (1 + τ ^ (-(aExp d s / 2))) *
            (Real.exp cL * Real.exp (-cL * τ)) *
            hsNorm ((j : ℝ) - aExp d s) (centerCoeff ρβ (coeffOf ψ)) := by
          apply mul_le_mul_of_nonneg_right _ hR0
          have h1 : K * τ ^ (-(aExp d s / 2)) ≤ (K + P * CL + 1) * (1 + τ ^ (-(aExp d s / 2))) := by
            nlinarith [mul_nonneg hPC (by linarith : (0 : ℝ) ≤ 1 + τ ^ (-(aExp d s / 2))),
              mul_nonneg hK0 hX]
          have h2 : (K + P * CL + 1) * (1 + τ ^ (-(aExp d s / 2))) ≤
              (K + P * CL + 1) * (1 + τ ^ (-(aExp d s / 2))) * (Real.exp cL * Real.exp (-cL * τ)) :=
            le_mul_of_one_le_right (mul_nonneg (by linarith) (by linarith)) hEe
          linarith
      _ = _ := by ring
  · -- regime `τ ≥ 1`: chain from the `L²` level at time `τ - 1`
    have hτ0' : 0 ≤ τ - 1 := by linarith
    have hch := hP β V ρβ H (coeffOf ψ) hcdat (τ - 1) hτ0'
    rw [sub_add_cancel] at hch
    have hS1 := (S_facts' hd s hs0 hsd j hj H hψc hψ hτ0' 0 le_rfl (by positivity)).2
    have hψ2 : MemSobolev ((mStar d : ℝ) + 2) ψ :=
      memSobolev_mono_idx hψ (by exact_mod_cast hjm)
    have hL2' : sobolevNorm 0 (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ (τ - 1) ψ) ≤
        CL * Real.exp (-cL * (τ - 1)) * sobolevNorm 2 (projMean (withDensityReal ρβ) ψ) :=
      hL2 β V ρβ (H.mono (by omega)) ψ hψc hψ2 (τ - 1) hτ0'
    have hR2 : sobolevNorm 2 (projMean (withDensityReal ρβ) ψ) ≤
        hsNorm ((j : ℝ) - aExp d s) (centerCoeff ρβ (coeffOf ψ)) := by
      rw [(hPf 2 (by norm_num) (by exact_mod_cast (by omega : 2 ≤ j))).2]
      exact MFApriori.hsNorm_mono_idx hA1 hcJA
    have hSτ := hS (j : ℝ) (by positivity) le_rfl
    have hX : 0 ≤ τ ^ (-(aExp d s / 2)) := Real.rpow_nonneg (by linarith) _
    have hE0 : 0 ≤ Real.exp cL * Real.exp (-cL * τ) := by positivity
    refine ⟨hSτ.1, ?_⟩
    rw [hSτ.2, hRj]
    calc _ ≤ P * hsNorm 0 (centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j
            (coeffOf ψ) (τ - 1))) := hch
      _ = P * sobolevNorm 0 (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ (τ - 1) ψ) := by
          rw [hS1]
      _ ≤ P * (CL * Real.exp (-cL * (τ - 1)) * sobolevNorm 2 (projMean (withDensityReal ρβ) ψ)) :=
          mul_le_mul_of_nonneg_left hL2' hP0
      _ ≤ P * (CL * Real.exp (-cL * (τ - 1)) *
            hsNorm ((j : ℝ) - aExp d s) (centerCoeff ρβ (coeffOf ψ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hR2 (by positivity)) hP0
      _ = P * CL * (Real.exp cL * Real.exp (-cL * τ)) *
            hsNorm ((j : ℝ) - aExp d s) (centerCoeff ρβ (coeffOf ψ)) := by
          rw [show -cL * (τ - 1) = cL + (-cL * τ) by ring, Real.exp_add]; ring
      _ ≤ (K + P * CL + 1) * (1 + τ ^ (-(aExp d s / 2))) * (Real.exp cL * Real.exp (-cL * τ)) *
            hsNorm ((j : ℝ) - aExp d s) (centerCoeff ρβ (coeffOf ψ)) := by
          apply mul_le_mul_of_nonneg_right _ hR0
          have h1 : P * CL ≤ (K + P * CL + 1) * (1 + τ ^ (-(aExp d s / 2))) := by
            have h1' : P * CL ≤ K + P * CL + 1 := by linarith
            have h2' : (K + P * CL + 1) ≤ (K + P * CL + 1) * (1 + τ ^ (-(aExp d s / 2))) :=
              le_mul_of_one_le_right (by linarith) (by linarith)
            exact h1'.trans h2'
          exact mul_le_mul_of_nonneg_right h1 hE0
      _ = _ := by ring

/-- `S_eq` (first part) for `τ > 0` at any level `mStar d ≤ m` (the classical `C²` threshold is
only needed at `τ = 0`). -/
theorem S_eq_low {s νm νp c₀ Λ₀ β : ℝ} {V ρβ : Torus d → ℝ} (hd : 1 ≤ d) (m : ℕ)
    (hm : mStar d ≤ m) (H : FrozenHyp d s (m + 3) νm νp c₀ Λ₀ β V ρβ) {ψ : Torus d → ℝ}
    (hψc : Continuous ψ) (hψ : MemSobolev m ψ) {τ : ℝ} (hτ : 0 < τ) :
    equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ ψ =
      toFun (centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ m (coeffOf ψ) τ)) := by
  have h3 := ClassicalPart.three_le_mStar d
  have hm1 : 1 ≤ m := by omega
  have hdm : (d : ℝ) / 2 < m := by
    have := mStar_gt d
    have h2 : (mStar d : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hcm : MemHs (m : ℝ) (coeffOf ψ) := (hsNormSq_coeffOf _ ψ hψ).1
  have hre : IsRealCoeff (coeffOf ψ) := isRealCoeff_coeffOf ψ (integrable_of_cont hψc)
  have hA := adjointData_frozen_level m H 0 (τ + 1) (by linarith)
  have hτT : τ ∈ Set.Icc (0 : ℝ) (τ + 1) := ⟨hτ.le, by linarith⟩
  have hmem := ((exists_frozenCoeff_bound (d := d) (s := s) (m := m) hd H.hs0 H.hsd hm1
    (frozenRegime d s c₀) 1 Λ₀ Λ₀).choose_spec.2 _ 0 (τ + 1) ρβ hA _ hcm τ hτT).1
  have hreal := frozenCoeff_real hd H.hs0 H.hsd hm1 hA hcm hre hτT
  have hsum := summable_norm_of_memHs _ hdm _ hmem
  have hprob := H.thermal.1
  have hρc := H.cont (by omega)
  have h2 := (projMean_toFun hprob hρc hsum hmem hreal).1
  have h1 : equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ ψ =
      projMean (withDensityReal ρβ)
        (toFun (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ m (coeffOf ψ) τ)) := by
    unfold equilibriumSemigroup
    congr 1
    rw [ClassicalPart.propagator_eq_toFun hd s H.hs0 H.hsd m hm _ 1 Λ₀ Λ₀
      (mfData d s H.hs0 H.hsd V β H.hβ) 0 τ (fun _ => ρβ)
      (adjointData_frozen_level m H 0 τ hτ) τ
      ⟨hτ, le_rfl⟩ ψ hψc hψ 0 ⟨le_rfl, hτ.le⟩]
    funext x
    simp [frozenCoeff]
  exact h1.trans h2

/-- Density: the smoothing estimate for `H^{j-a}` data, from the `H^j` case by truncation,
the `L²` decay of the differences, and Fatou on the finite partial sums of `hsNormSq`. -/
theorem frozen_density' (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (j : ℕ)
    (hj : mStar d + 2 ≤ j) (νm νp c₀ Λ₀ C c : ℝ) (hC : 0 ≤ C) {β : ℝ} {V ρβ : Torus d → ℝ}
    (H : FrozenHyp d s (j + mStar d) νm νp c₀ Λ₀ β V ρβ)
    (hsm : ∀ ψ : Torus d → ℝ, Continuous ψ → MemSobolev j ψ → ∀ τ : ℝ, 0 < τ →
        MemSobolev j (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ ψ) ∧
        sobolevNorm j (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ ψ) ≤
          C * (1 + τ ^ (-(aExp d s / 2))) * Real.exp (-c * τ) *
            sobolevNorm ((j : ℝ) - aExp d s) (projMean (withDensityReal ρβ) ψ))
    (ψ : Torus d → ℝ) (hψc : Continuous ψ) (hψa : MemSobolev ((j : ℝ) - aExp d s) ψ) {τ : ℝ}
    (hτ : 0 < τ) :
    MemSobolev j (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ ψ) ∧
    sobolevNorm j (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ ψ) ≤
      C * (1 + τ ^ (-(aExp d s / 2))) * Real.exp (-c * τ) *
        sobolevNorm ((j : ℝ) - aExp d s) (projMean (withDensityReal ρβ) ψ) := by
  have h3 := ClassicalPart.three_le_mStar d
  have ha := aExp_spec (d := d) s hsd
  have hjR : (mStar d : ℝ) + 2 ≤ (j : ℝ) := by exact_mod_cast hj
  have h3R : (3 : ℝ) ≤ mStar d := by exact_mod_cast h3
  have hmst := mStar_gt d
  have hA2 : aExp d s < 2 := ha.2.1
  have hA1 : 1 ≤ aExp d s := ha.1
  have hm0A : (mStar d : ℝ) ≤ (j : ℝ) - aExp d s := by linarith
  have hjA0 : (0 : ℝ) ≤ (j : ℝ) - aExp d s := by linarith
  have hjAle : (j : ℝ) - aExp d s ≤ j := by linarith
  have hdjA : (d : ℝ) / 2 < (j : ℝ) - aExp d s := by linarith
  have hdj : (d : ℝ) / 2 < (j : ℝ) := by linarith
  have hdm0 : (d : ℝ) / 2 < (mStar d : ℝ) := by linarith
  have hprob : IsProbDensity ρβ := H.thermal.1
  have hρc : Continuous ρβ := H.cont (by omega)
  have hΛ : ∀ x, ρβ x ≤ Λ₀ := H.le_Lam
  have hΛ0 : 0 ≤ Λ₀ := (H.hc₀.le.trans (H.hlow 0)).trans (H.le_Lam 0)
  have hρ0 : MemHs 0 (coeffOf ρβ) := MFApriori.memHs_zero_coeffOf_continuous hρc
  have hcA : MemHs ((j : ℝ) - aExp d s) (coeffOf ψ) := (hsNormSq_coeffOf _ ψ hψa).1
  have hsumA : Summable (fun k => ‖coeffOf ψ k‖) := summable_norm_of_memHs _ hdjA _ hcA
  have hreal : IsRealCoeff (coeffOf ψ) := isRealCoeff_coeffOf ψ (integrable_of_cont hψc)
  have hψeq : toFun (coeffOf ψ) = ψ := toFun_coeffOf ψ hψc hsumA
  have hm0ψ : MemSobolev ((mStar d : ℝ)) ψ := memSobolev_mono_idx hψa hm0A
  have hcm0 : MemHs ((mStar d : ℝ)) (coeffOf ψ) := hcA.mono hm0A
  have hS0 : equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ ψ =
      toFun (centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ (mStar d)
        (coeffOf ψ) τ)) :=
    S_eq_low hd (mStar d) le_rfl (H.mono (by omega)) hψc hm0ψ hτ
  -- truncations of the coefficients
  have hcn_mem : ∀ n : ℕ, MemHs (j : ℝ) (truncCoeff n (coeffOf ψ)) := fun n =>
    MFLocal.memHs_truncCoeff _ n _
  have hcn_real : ∀ n : ℕ, IsRealCoeff (truncCoeff n (coeffOf ψ)) := fun n =>
    isRealCoeff_truncCoeff' hreal n
  have hcn_sum : ∀ n : ℕ, Summable (fun k => ‖truncCoeff n (coeffOf ψ) k‖) := fun n =>
    summable_norm_of_memHs _ hdj _ (hcn_mem n)
  have hψn_cont : ∀ n : ℕ, Continuous (toFun (truncCoeff n (coeffOf ψ))) := fun n =>
    continuous_toFun _ (hcn_sum n)
  have hψn_mem : ∀ n : ℕ, MemSobolev (j : ℝ) (toFun (truncCoeff n (coeffOf ψ))) := fun n =>
    (ClassicalPart.memSobolev_toFun (hcn_sum n) (hcn_mem n) (hcn_real n)).1
  have hψn_coeff : ∀ n : ℕ, coeffOf (toFun (truncCoeff n (coeffOf ψ))) =
      truncCoeff n (coeffOf ψ) := fun n => coeffOf_toFun _ (hcn_real n) (hcn_sum n)
  have hcn0 : ∀ n : ℕ, MemHs ((mStar d : ℕ) : ℝ) (truncCoeff n (coeffOf ψ)) := fun n =>
    (hcn_mem n).mono (by linarith)
  have hcm0' : MemHs ((mStar d : ℕ) : ℝ) (coeffOf ψ) := hcm0
  -- adjoint data at the two levels
  have hA0 := adjointData_frozen' (mStar d) (by omega) H 0 (τ + 1) (by linarith)
  have hAj := adjointData_frozen' j (by omega) H 0 (τ + 1) (by linarith)
  have hτT : τ ∈ Set.Icc (0 : ℝ) (τ + 1) := ⟨hτ.le, by linarith⟩
  have hlev : ∀ n : ℕ, frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ (mStar d)
      (truncCoeff n (coeffOf ψ)) τ =
      frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j (truncCoeff n (coeffOf ψ)) τ :=
    fun n => frozenCoeff_level hd hs0 hsd (by omega) (by omega) hA0 hAj (hcn_mem n) hτT
  have hWmem : ∀ n : ℕ, MemHs 0 (centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ)
      ρβ (mStar d) (truncCoeff n (coeffOf ψ) - coeffOf ψ) τ)) := by
    intro n
    have hm := frozen_memHs' hd s hs0 hsd (mStar d) (j + mStar d) (by omega) (by omega) H
      (memHs_sub (hcn0 n) hcm0') hτ.le
    exact (centerCoeff_bound' hprob hρc hΛ (by positivity) (hm.mono (by positivity))).1
  have hdm0' : (d : ℝ) / 2 < ((mStar d : ℕ) : ℝ) := hdm0
  have hWid : ∀ n : ℕ, centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ (mStar d)
      (truncCoeff n (coeffOf ψ)) τ) - centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ)
      ρβ (mStar d) (coeffOf ψ) τ) = centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ)
      ρβ (mStar d) (truncCoeff n (coeffOf ψ) - coeffOf ψ) τ) := by
    intro n
    have hsub := frozenCoeff_sub hd s hs0 hsd (mStar d) (by omega) (frozenRegime d s c₀) 1 Λ₀ Λ₀
      (mfData d s H.hs0 H.hsd V β H.hβ) 0 (τ + 1) ρβ hA0 (truncCoeff n (coeffOf ψ)) (coeffOf ψ)
      (hcn0 n) hcm0' hτT
    have hF0t : MemHs 0 (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ (mStar d)
        (truncCoeff n (coeffOf ψ)) τ) :=
      (frozen_memHs' hd s hs0 hsd (mStar d) (j + mStar d) (by omega) (by omega) H (hcn0 n)
        hτ.le).mono (by positivity)
    have hF0c : MemHs 0 (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ (mStar d)
        (coeffOf ψ) τ) :=
      (frozen_memHs' hd s hs0 hsd (mStar d) (j + mStar d) (by omega) (by omega) H hcm0'
        hτ.le).mono (by positivity)
    rw [hsub, centerCoeff_sub' hρ0 hF0t hF0c]
  obtain ⟨Lf, -, hLf⟩ := exists_frozenCoeff_bound (d := d) (s := s) (m := mStar d) hd hs0 hsd
    (by omega) (frozenRegime d s c₀) 1 Λ₀ Λ₀
  obtain ⟨E, hE0, hWbd⟩ : ∃ E : ℝ, 0 ≤ E ∧ ∀ n : ℕ,
      hsNorm 0 (centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ
        (mStar d) (truncCoeff n (coeffOf ψ) - coeffOf ψ) τ)) ≤
      E * (2 * (1 + Λ₀) * hsNorm ((j : ℝ) - aExp d s) (coeffOf ψ - truncCoeff n (coeffOf ψ))) := by
    refine ⟨Real.exp ((frozenRegime d s c₀).lambdaM Lf 0 (thetaOrder d s) * τ),
      (Real.exp_pos _).le, fun n => ?_⟩
    obtain ⟨x, hx⟩ : ∃ x : Coeff d, x = truncCoeff n (coeffOf ψ) - coeffOf ψ := ⟨_, rfl⟩
    rw [← hx]
    have hxm0 : MemHs ((mStar d : ℕ) : ℝ) x := by
      rw [hx]; exact memHs_sub (hcn0 n) hcm0'
    have hxA : MemHs ((j : ℝ) - aExp d s) x := by
      rw [hx]; exact memHs_sub (MFLocal.memHs_truncCoeff _ n _) hcA
    have key := hLf _ 0 (τ + 1) ρβ hA0 x hxm0 τ hτT
    have hF0 : MemHs 0 (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ (mStar d) x τ) :=
      key.1.mono (by positivity)
    have hcc := (centerCoeff_bound' hprob hρc hΛ (le_refl (0 : ℝ)) hF0).2
    have hm1 : hsNorm 0 (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ (mStar d) x τ) ≤
        hsNorm ((mStar d : ℕ) : ℝ) (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ (mStar d) x τ) :=
      MFApriori.hsNorm_mono_idx (by positivity) key.1
    have hmono : hsNorm ((mStar d : ℕ) : ℝ) x ≤ hsNorm ((j : ℝ) - aExp d s) x :=
      MFApriori.hsNorm_mono_idx hm0A hxA
    have hsw : hsNorm ((j : ℝ) - aExp d s) x =
        hsNorm ((j : ℝ) - aExp d s) (coeffOf ψ - truncCoeff n (coeffOf ψ)) := by
      rw [hx]; exact MFApriori.Aux.hsNorm_sub_comm _ _ _
    have hEp := Real.exp_pos ((frozenRegime d s c₀).lambdaM Lf 0 (thetaOrder d s) * τ)
    have hΛ1 : 0 ≤ 2 * (1 + Λ₀) := by linarith
    calc _ ≤ 2 * (1 + Λ₀) * hsNorm 0 (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ (mStar d) x τ) := hcc
      _ ≤ 2 * (1 + Λ₀) * (Real.exp ((frozenRegime d s c₀).lambdaM Lf 0 (thetaOrder d s) * τ) *
            hsNorm ((mStar d : ℕ) : ℝ) x) :=
          mul_le_mul_of_nonneg_left (hm1.trans key.2) hΛ1
      _ ≤ 2 * (1 + Λ₀) * (Real.exp ((frozenRegime d s c₀).lambdaM Lf 0 (thetaOrder d s) * τ) *
            hsNorm ((j : ℝ) - aExp d s) x) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmono hEp.le) hΛ1
      _ = _ := by rw [hsw]; ring
  have hδn : Tendsto (fun n : ℕ => E * (2 * (1 + Λ₀) *
      hsNorm ((j : ℝ) - aExp d s) (coeffOf ψ - truncCoeff n (coeffOf ψ)))) atTop (𝓝 0) := by
    have h := (truncCoeff_tendsto ((j : ℝ) - aExp d s) (coeffOf ψ) hcA).2
    simpa using (h.const_mul (2 * (1 + Λ₀))).const_mul E
  have hPn : ∀ n : ℕ, sobolevNorm ((j : ℝ) - aExp d s)
      (projMean (withDensityReal ρβ) (toFun (truncCoeff n (coeffOf ψ)))) =
      hsNorm ((j : ℝ) - aExp d s) (centerCoeff ρβ (truncCoeff n (coeffOf ψ))) := by
    intro n
    have h := (P_facts' hd s hs0 hsd j hj H (hψn_cont n) (hψn_mem n) ((j : ℝ) - aExp d s) hjA0
      hjAle).2
    rw [hψn_coeff n] at h
    exact h
  have hsmooth : ∀ n : ℕ, sobolevNorm (j : ℝ)
      (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ (toFun (truncCoeff n (coeffOf ψ)))) ≤
      C * (1 + τ ^ (-(aExp d s / 2))) * Real.exp (-c * τ) *
        hsNorm ((j : ℝ) - aExp d s) (centerCoeff ρβ (truncCoeff n (coeffOf ψ))) := by
    intro n
    have h := (hsm _ (hψn_cont n) (hψn_mem n) τ hτ).2
    rw [hPn n] at h
    exact h
  obtain ⟨un, hun_def⟩ : ∃ un : ℕ → Coeff d, un = fun n =>
      centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j (truncCoeff n (coeffOf ψ)) τ) :=
    ⟨_, rfl⟩
  obtain ⟨u, hu_def⟩ : ∃ u : Coeff d, u = centerCoeff ρβ
      (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ (mStar d) (coeffOf ψ) τ) := ⟨_, rfl⟩
  have hunb : ∀ n : ℕ, hsNorm (j : ℝ) (un n) ≤ C * (1 + τ ^ (-(aExp d s / 2))) * Real.exp (-c * τ) *
      hsNorm ((j : ℝ) - aExp d s) (centerCoeff ρβ (truncCoeff n (coeffOf ψ))) := by
    intro n
    have h1 := (S_facts' hd s hs0 hsd j hj H (hψn_cont n) (hψn_mem n) hτ.le (j : ℝ)
      (by positivity) le_rfl).2
    rw [hψn_coeff n] at h1
    rw [hun_def, ← h1]
    exact hsmooth n
  have hunmem : ∀ n : ℕ, MemHs (j : ℝ) (un n) := by
    intro n
    have hm := frozen_memHs' hd s hs0 hsd j (j + mStar d) (by omega) (by omega) H (hcn_mem n) hτ.le
    rw [hun_def]
    exact (centerCoeff_bound' hprob hρc hΛ (by positivity) hm).1
  have hu_eq : ∀ n : ℕ, un n - u = centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ
      (mStar d) (truncCoeff n (coeffOf ψ) - coeffOf ψ) τ) := by
    intro n
    simp only [hun_def, hu_def]
    rw [← hlev n]
    exact hWid n
  have hcoordTend : ∀ k : Lattice d, Tendsto (fun n => un n k) atTop (𝓝 (u k)) := by
    intro k
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hδn
    have hk : un n k - u k = centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ
        (mStar d) (truncCoeff n (coeffOf ψ) - coeffOf ψ) τ) k := by
      rw [← hu_eq n]; rfl
    rw [hk]
    exact (norm_coeff_le_hsNorm0 (hWmem n) k).trans (hWbd n)
  have hsumF : ∀ F : Finset (Lattice d), Tendsto (fun n => ∑ k ∈ F, sobWeight (j : ℝ) k * ‖un n k‖ ^ 2)
      atTop (𝓝 (∑ k ∈ F, sobWeight (j : ℝ) k * ‖u k‖ ^ 2)) := by
    intro F
    apply tendsto_finset_sum
    intro k _
    exact ((hcoordTend k).norm.pow 2).const_mul (sobWeight (j : ℝ) k)
  have hRtend : Tendsto (fun n => hsNorm ((j : ℝ) - aExp d s) (centerCoeff ρβ (truncCoeff n (coeffOf ψ))))
      atTop (𝓝 (hsNorm ((j : ℝ) - aExp d s) (centerCoeff ρβ (coeffOf ψ)))) := by
    have hb2 := (truncCoeff_tendsto ((j : ℝ) - aExp d s) (coeffOf ψ) hcA).2
    have hg : Tendsto (fun n : ℕ => 2 * (1 + Λ₀) * hsNorm ((j : ℝ) - aExp d s)
        (coeffOf ψ - truncCoeff n (coeffOf ψ))) atTop (𝓝 0) := by
      simpa using hb2.const_mul (2 * (1 + Λ₀))
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hg
    rw [Real.norm_eq_abs]
    have h := abs_hsNorm_center_sub_le hprob hρc hΛ hjA0
      (MFLocal.memHs_truncCoeff ((j : ℝ) - aExp d s) n (coeffOf ψ)) hcA
    rw [MFApriori.Aux.hsNorm_sub_comm] at h
    exact h
  have hRpow : Tendsto (fun n => (C * (1 + τ ^ (-(aExp d s / 2))) * Real.exp (-c * τ) *
      hsNorm ((j : ℝ) - aExp d s) (centerCoeff ρβ (truncCoeff n (coeffOf ψ)))) ^ 2) atTop
      (𝓝 ((C * (1 + τ ^ (-(aExp d s / 2))) * Real.exp (-c * τ) *
        hsNorm ((j : ℝ) - aExp d s) (centerCoeff ρβ (coeffOf ψ))) ^ 2)) :=
    (hRtend.const_mul (C * (1 + τ ^ (-(aExp d s / 2))) * Real.exp (-c * τ))).pow 2
  have hfin : ∀ F : Finset (Lattice d), ∑ k ∈ F, sobWeight (j : ℝ) k * ‖u k‖ ^ 2 ≤
      (C * (1 + τ ^ (-(aExp d s / 2))) * Real.exp (-c * τ) *
        hsNorm ((j : ℝ) - aExp d s) (centerCoeff ρβ (coeffOf ψ))) ^ 2 := by
    intro F
    refine le_of_tendsto_of_tendsto (hsumF F) hRpow (Filter.Eventually.of_forall fun n => ?_)
    have hsn : ∑ k ∈ F, sobWeight (j : ℝ) k * ‖un n k‖ ^ 2 ≤ hsNorm (j : ℝ) (un n) ^ 2 := by
      calc _ ≤ ∑' k, sobWeight (j : ℝ) k * ‖un n k‖ ^ 2 :=
            (hunmem n).sum_le_tsum F (fun k _ => mul_nonneg (Real.rpow_nonneg (by positivity) _)
              (sq_nonneg _))
        _ = hsNorm (j : ℝ) (un n) ^ 2 := hsNormSq_eq_sq' _ _
    exact hsn.trans (pow_le_pow_left₀ (MFApriori.hsNorm_nonneg' _ _) (hunb n) 2)
  have hnn_all : (0 : Lattice d → ℝ) ≤ fun k => sobWeight (j : ℝ) k * ‖u k‖ ^ 2 :=
    fun k => mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _)
  have hsumAll : Summable (fun k => sobWeight (j : ℝ) k * ‖u k‖ ^ 2) :=
    summable_of_sum_le hnn_all hfin
  have htsum : ∑' k, sobWeight (j : ℝ) k * ‖u k‖ ^ 2 ≤
      (C * (1 + τ ^ (-(aExp d s / 2))) * Real.exp (-c * τ) *
        hsNorm ((j : ℝ) - aExp d s) (centerCoeff ρβ (coeffOf ψ))) ^ 2 :=
    Real.tsum_le_of_sum_le hnn_all hfin
  have hu_mem : MemHs (j : ℝ) u := hsumAll
  have hX0 : 0 ≤ 1 + τ ^ (-(aExp d s / 2)) := by
    have := Real.rpow_nonneg hτ.le (-(aExp d s / 2)); linarith
  have hMR0 : 0 ≤ C * (1 + τ ^ (-(aExp d s / 2))) * Real.exp (-c * τ) *
      hsNorm ((j : ℝ) - aExp d s) (centerCoeff ρβ (coeffOf ψ)) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC hX0) (Real.exp_pos _).le) (MFApriori.hsNorm_nonneg' _ _)
  have hnorm_u : hsNorm (j : ℝ) u ≤ C * (1 + τ ^ (-(aExp d s / 2))) * Real.exp (-c * τ) *
      hsNorm ((j : ℝ) - aExp d s) (centerCoeff ρβ (coeffOf ψ)) := by
    have h1 : hsNorm (j : ℝ) u = Real.sqrt (∑' k, sobWeight (j : ℝ) k * ‖u k‖ ^ 2) := rfl
    rw [h1]
    calc _ ≤ Real.sqrt ((C * (1 + τ ^ (-(aExp d s / 2))) * Real.exp (-c * τ) *
          hsNorm ((j : ℝ) - aExp d s) (centerCoeff ρβ (coeffOf ψ))) ^ 2) := Real.sqrt_le_sqrt htsum
      _ = _ := Real.sqrt_sq hMR0
  have hSu : equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ ψ = toFun u := by
    rw [hS0, hu_def]
  have hreal_u : IsRealCoeff u := by
    rw [hu_def]
    exact centerCoeff_isReal (frozenCoeff_real hd hs0 hsd (by omega) hA0 hcm0' hreal hτT)
  have hsum_u : Summable (fun k => ‖u k‖) := summable_norm_of_memHs _ hdj _ hu_mem
  have hMemTo := ClassicalPart.memSobolev_toFun hsum_u hu_mem hreal_u
  have hPR : sobolevNorm ((j : ℝ) - aExp d s) (projMean (withDensityReal ρβ) ψ) =
      hsNorm ((j : ℝ) - aExp d s) (centerCoeff ρβ (coeffOf ψ)) := by
    have hpm : projMean (withDensityReal ρβ) ψ = toFun (centerCoeff ρβ (coeffOf ψ)) := by
      conv_lhs => rw [← hψeq]
      exact (projMean_toFun hprob hρc hsumA hcA hreal).1
    rw [hpm]
    exact (projMean_toFun hprob hρc hsumA hcA hreal).2.2
  rw [hSu]
  refine ⟨hMemTo.1, ?_⟩
  rw [hMemTo.2, hPR]
  exact hnorm_u

theorem exists_frozen_hj_decay' (hd : 1 ≤ d) (s : ℝ) (j : ℕ) (hj : (d : ℝ) / 2 + 4 < j)
    (νm νp c₀ Λ₀ : ℝ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (β : ℝ) (V ρβ : Torus d → ℝ) (H : FrozenHyp d s (j + mStar d) νm νp c₀ Λ₀ β V ρβ),
      ∀ ψ : Torus d → ℝ, Continuous ψ → MemSobolev j ψ → ∀ τ, 0 ≤ τ →
        MemSobolev j (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ ψ) ∧
        sobolevNorm j (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ ψ) ≤
          C * Real.exp (-c * τ) * sobolevNorm j (projMean (withDensityReal ρβ) ψ) :=
  frozen_hj_decay_core hd s j (mStar_add_two_le_of_gt hj) νm νp c₀ Λ₀

theorem exists_frozen_smoothing' (hd : 1 ≤ d) (s : ℝ) (j : ℕ) (hj : (d : ℝ) / 2 + 4 < j)
    (νm νp c₀ Λ₀ : ℝ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (β : ℝ) (V ρβ : Torus d → ℝ) (H : FrozenHyp d s (j + mStar d) νm νp c₀ Λ₀ β V ρβ),
      ∀ ψ : Torus d → ℝ, Continuous ψ → MemSobolev ((j : ℝ) - aExp d s) ψ → ∀ τ, 0 < τ →
        MemSobolev j (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ ψ) ∧
        sobolevNorm j (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ ψ) ≤
          C * (1 + τ ^ (-(aExp d s / 2))) * Real.exp (-c * τ) * sobolevNorm ((j : ℝ) - aExp d s) (projMean (withDensityReal ρβ) ψ) := by
  have hjm := mStar_add_two_le_of_gt hj
  by_cases hsc : 0 ≤ s ∧ s < d
  swap
  · exact ⟨1, 1, one_pos, one_pos, fun β V ρβ H => (hsc ⟨H.hs0, H.hsd⟩).elim⟩
  obtain ⟨hs0, hsd⟩ := hsc
  obtain ⟨C, c, hC, hc, hsm⟩ := frozen_smooth_H' hd s j hjm νm νp c₀ Λ₀
  refine ⟨C, c, hC, hc, fun β V ρβ H ψ hψc hψa τ hτ => frozen_density' hd s hs0 hsd j hjm νm νp c₀ Λ₀
    C c hC.le H (hsm β V ρβ H) ψ hψc hψa hτ⟩

end Low

end HRS.PDE.MFAdjoint

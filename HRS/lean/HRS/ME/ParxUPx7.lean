import HRS.Equilibrium.Parametrix.PX7AuxE

/-!
# Packet P6: uniform constant for `px7_spec`

`px7_spec_unif` is `HRS.PDE.PX7.px7_spec` with the constant chosen before `β` and `ρ`.
The constant is `Cinv = 3 * (A * (M0 ^ 2 * K)) / (2 * c0)`, where

* `(M0, c0)` are the decay constants of `px7_decay` at level `m = px7_m d`, which depend only on
  `(d, s, m, νm, νp, c₀, Λ₀)`;
* `A` comes from `px7_ev_C2` and `K` from `px7_parseval`, which depend only on `d` and `m`.

The file reruns the proofs of `px7_PP_bound`, `px7_pair_C2`, `px7_inv_C2`, and `px7_oneVar`
with these constants as arguments. The qualitative lemmas (linearity, symmetry, centering, PDE,
left inverse) are reused unchanged.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.ME.ParxU

open HRS.PDE HRS.PDE.PX7 HRS.PDE.MFAdjoint

variable {d : ℕ}

/-! ### Operator bound with explicit constants -/

theorem px7_PP_bound_of {m : ℕ} {T : ℝ → Coeff d → Coeff d} {M c : ℝ} (hM : 0 < M)
    (hop : ∀ τ : ℝ, 0 ≤ τ → OpOK (m : ℝ) (T τ) (M * Real.exp (-c * τ)))
    (τ : ℝ) (hτ : 0 ≤ τ) (u : Arr d) (hu : Mem2 (m : ℝ) (m : ℝ) u) :
    Mem2 (m : ℝ) (m : ℝ) (PP T τ u) ∧
      nrm2 (m : ℝ) (m : ℝ) (PP T τ u) ≤ M ^ 2 * Real.exp (-(2 * c) * τ) * nrm2 (m : ℝ) (m : ℝ) u := by
  have hF := hop τ hτ
  obtain ⟨h1, h2⟩ := px7_colOp_mem hF hu
  obtain ⟨h3, h4⟩ := px7_rowOp_mem hF h1
  refine ⟨h3, ?_⟩
  unfold PP
  have e : M ^ 2 * Real.exp (-(2 * c) * τ) = (M * Real.exp (-c * τ)) * (M * Real.exp (-c * τ)) := by
    have : Real.exp (-(2 * c) * τ) = Real.exp (-c * τ) * Real.exp (-c * τ) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [this]; ring
  rw [e]
  calc _ ≤ (M * Real.exp (-c * τ)) * nrm2 (m : ℝ) (m : ℝ) (colOp (T τ) u) := h4
    _ ≤ (M * Real.exp (-c * τ)) * ((M * Real.exp (-c * τ)) * nrm2 (m : ℝ) (m : ℝ) u) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

section PairKernelU

variable {D : DynData d} {ρ : Torus d → ℝ} {m : ℕ} {T : ℝ → Coeff d → Coeff d} {Ah : Coeff d → Coeff d}

theorem px7_pair_C2_of (hOV : OV D ρ m T Ah) {M c A K : ℝ} (hM : 0 < M)
    (hop : ∀ τ : ℝ, 0 ≤ τ → OpOK (m : ℝ) (T τ) (M * Real.exp (-c * τ)))
    (hA : 0 ≤ A)
    (hev : ∀ u : Arr d, Mem2 (m : ℝ) (m : ℝ) u →
      IsCk2 2 (ev u) ∧ cbNorm2 2 (ev u) ≤ A * nrm2 (m : ℝ) (m : ℝ) u)
    (hdata : ∀ R : Torus d → Torus d → ℝ, IsCk2 (m + m) R →
      Mem2 (m : ℝ) (m : ℝ) (arr R) ∧ RS (arr R) ∧
        nrm2 (m : ℝ) (m : ℝ) (arr R) ≤ K * cbNorm2 (m + m) R)
    (R : Torus d → Torus d → ℝ) (hR : IsCk2 (m + m) R) (τ : ℝ) (hτ : 0 ≤ τ) :
    IsCk2 2 (pairSemigroup D ρ τ R) ∧
      cbNorm2 2 (pairSemigroup D ρ τ R) ≤
        (A * (M ^ 2 * K) * cbNorm2 (m + m) R) * Real.exp (-(2 * c) * τ) := by
  obtain ⟨h1, -, h3⟩ := hdata R hR
  obtain ⟨h4, h5⟩ := px7_PP_bound_of hM hop τ hτ _ h1
  rw [px7_pair_ev hOV hR hτ]
  obtain ⟨h6, h7⟩ := hev _ h4
  refine ⟨h6, h7.trans ?_⟩
  calc A * nrm2 (m : ℝ) (m : ℝ) (PP T τ (arr R))
      ≤ A * (M ^ 2 * Real.exp (-(2 * c) * τ) * nrm2 (m : ℝ) (m : ℝ) (arr R)) :=
        mul_le_mul_of_nonneg_left h5 hA
    _ ≤ A * (M ^ 2 * Real.exp (-(2 * c) * τ) * (K * cbNorm2 (m + m) R)) := by
        apply mul_le_mul_of_nonneg_left _ hA
        exact mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := by ring

theorem px7_inv_C2_of (hOV : OV D ρ m T Ah) {C0 c0 : ℝ} (hc0 : 0 < c0)
    (hC2 : ∀ R : Torus d → Torus d → ℝ, IsCk2 (m + m) R → ∀ τ : ℝ, 0 ≤ τ →
      IsCk2 2 (pairSemigroup D ρ τ R) ∧
        cbNorm2 2 (pairSemigroup D ρ τ R) ≤ (C0 * cbNorm2 (m + m) R) * Real.exp (-c0 * τ))
    (R : Torus d → Torus d → ℝ) (hR : IsCk2 (m + m) R) :
    IsCk2 2 (pairInverse D ρ R) ∧ cbNorm2 2 (pairInverse D ρ R) ≤ 3 * C0 / c0 * cbNorm2 (m + m) R ∧
      (∀ x y, IntegrableOn (fun t => pairSemigroup D ρ t R x y) (Set.Ici 0)) := by
  have hreg : ∀ t : ℝ, 0 ≤ t → IsCk2 2 (pairSemigroup D ρ t R) := fun t ht => (hC2 R hR t ht).1
  have hbd : ∀ t : ℝ, 0 ≤ t → cbNorm2 2 (pairSemigroup D ρ t R) ≤
      (C0 * cbNorm2 (m + m) R) * Real.exp (-c0 * t) := fun t ht => (hC2 R hR t ht).2
  have hcont : ∀ i : ℕ, i ≤ 2 → ∀ p : Euc d × Euc d,
      ContinuousOn (fun t => iteratedFDeriv ℝ i (lift2 (pairSemigroup D ρ t R)) p) (Set.Ici 0) :=
    fun i hi p => px7_pair_jets hOV hR i hi p
  obtain ⟨-, hpt, hCk, -⟩ := MFPair.integral_family_isCk2 2 (fun t => pairSemigroup D ρ t R)
    (C0 * cbNorm2 (m + m) R) c0 hc0 hreg hbd hcont
  obtain ⟨-, hb⟩ := MFPair.family_tail 2 (fun t => pairSemigroup D ρ t R) (C0 * cbNorm2 (m + m) R) c0 hc0
    hreg hbd hcont 0 le_rfl
  refine ⟨hCk, ?_, hpt⟩
  unfold cbNorm2
  calc ∑ i ∈ Finset.range (2 + 1), ⨆ p : Euc d × Euc d, ‖iteratedFDeriv ℝ i (lift2 (pairInverse D ρ R)) p‖
      ≤ ∑ i ∈ Finset.range (2 + 1), (C0 * cbNorm2 (m + m) R) * Real.exp (-c0 * 0) / c0 := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        refine ciSup_le fun p => ?_
        exact hb i hi' p
    _ = 3 * C0 / c0 * cbNorm2 (m + m) R := by
        simp only [Finset.sum_const, Finset.card_range, mul_zero, Real.exp_zero, mul_one, nsmul_eq_mul]
        push_cast; field_simp

end PairKernelU

/-! ### The one-variable operator, built from a given frozen hypothesis -/

theorem px7_oneVar_H (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (ρ : Torus d → ℝ) (N : ℕ) (hN : px7_m d + 2 + mStar d + 3 ≤ N)
    (νm νp c₀ Λ₀ : ℝ) (H : FrozenHyp d s N νm νp c₀ Λ₀ β V ρ) :
    OV (mfData d s hs0 hsd V β hβ) ρ (px7_m d) (px7_T (mfData d s hs0 hsd V β hβ) ρ (px7_m d))
      (px7_Ah (mfData d s hs0 hsd V β hβ) ρ) := by
  have h3 := ClassicalPart.three_le_mStar d
  set m := px7_m d with hmdef
  have hm : mStar d + 2 ≤ m := (px7_m_eq d).ge
  have Hm : FrozenHyp d s (m + 3) νm νp c₀ Λ₀ β V ρ := H.mono (by omega)
  have Hm1 : FrozenHyp d s (m + 1 + 3) νm νp c₀ Λ₀ β V ρ := H.mono (by omega)
  have Hm2 : FrozenHyp d s (m + 2 + 3) νm νp c₀ Λ₀ β V ρ := H.mono (by omega)
  have hj0 : (d : ℝ) / 2 + 4 < m := by
    have : (d : ℝ) / 2 < (⌊(d : ℝ) / 2⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have e : (m : ℝ) = (⌊(d : ℝ) / 2⌋₊ : ℝ) + 5 := by rw [hmdef, px7_m]; push_cast; ring
    rw [e]; linarith
  have hj2 : (d : ℝ) / 2 + 4 < ((m + 2 : ℕ) : ℝ) := by push_cast; linarith
  obtain ⟨M0, c0, hM0, hc0, hdec0⟩ := px7_decay hd s m m hm le_rfl hj0 νm νp c₀ Λ₀
  obtain ⟨M2, c2, hM2, hc2, hdec2⟩ := px7_decay hd s m (m + 2) hm (by omega) hj2 νm νp c₀ Λ₀
  have hH0 : FrozenHyp d s (m + mStar d + 3) νm νp c₀ Λ₀ β V ρ := H.mono (by omega)
  have hH2 : FrozenHyp d s (m + 2 + mStar d + 3) νm νp c₀ Λ₀ β V ρ := H.mono (by omega)
  have hmR : (m : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by push_cast; linarith
  refine ⟨hj0, H.thermal.1, H.cont (by omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro τ hτ x y hx hy; exact px7_T_add hd m hm Hm hx hy hτ
  · intro τ hτ x hx a; exact px7_T_smul hd m hm Hm hx a hτ
  · exact ⟨M0, c0, hM0, hc0, fun τ hτ x hx => hdec0 β V ρ hH0 x hx τ hτ⟩
  · exact ⟨M2, c2, hM2, hc2, fun τ hτ x hx => hdec2 β V ρ hH2 x hx τ hτ⟩
  · intro τ hτ x hx hre; exact (px7_T_real hd m hm Hm hx hre hτ).2
  · intro τ hτ x hx; exact px7_T_mean hd m hm Hm hx hτ
  · intro τ hτ z; exact px7_T_const hd m hm Hm z hτ
  · intro x hx; exact px7_T_zero hd m hm Hm hx
  · intro σ τ hσ hτ x hx; exact px7_T_semigroup hd m hm Hm hx hσ hτ
  · intro x hx τ₀ hτ₀
    refine px7_T_cont hd m hm Hm1 (M0 * 1) ?_ hx hτ₀
    intro τ hτ y hy
    have := (hdec0 β V ρ hH0 y hy τ hτ).2
    have hE : Real.exp (-c0 * τ) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    calc _ ≤ M0 * Real.exp (-c0 * τ) * HRS.PDE.hsNorm (m : ℝ) y := this
      _ ≤ M0 * 1 * HRS.PDE.hsNorm (m : ℝ) y := by
        have := hsNorm_nonneg' (m : ℝ) y
        gcongr
  · intro ψ hψc hψ τ hτ; exact px7_S_eq hd m hm Hm hψc hψ hτ
  · obtain ⟨K, hK, h⟩ := px7_Ah_bound hd m hm Hm
    exact ⟨K, hK, h⟩
  · intro x y hx hy; exact px7_Ah_add hd m hm Hm2 hx hy
  · intro a x; exact px7_Ah_smul m a x _
  · intro x hx hre; exact (px7_Ah_real hd m hm Hm hre).2.2
  · intro x hx; exact px7_T_deriv hd m hm Hm2 hx
  · obtain ⟨Kt, hKt, h⟩ := px7_T_quot_bound hd m hm Hm2
    exact ⟨Kt, hKt, h⟩
  · intro x hx τ hτ
    refine px7_comm hd m hm Hm2 M0 ?_ ?_ hx hτ
    · intro τ' hτ' y hy
      have := (hdec0 β V ρ hH0 y hy τ' hτ').2
      have hE : Real.exp (-c0 * τ') ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
      calc _ ≤ M0 * Real.exp (-c0 * τ') * HRS.PDE.hsNorm (m : ℝ) y := this
        _ ≤ M0 * 1 * HRS.PDE.hsNorm (m : ℝ) y := by
          have := hsNorm_nonneg' (m : ℝ) y
          gcongr
        _ = _ := by ring
    · intro τ' hτ' y hy; exact (hdec2 β V ρ hH2 y hy τ' hτ').1
  · intro x hr hx; exact px7_bridge hd m hm Hm2 hr hx

/-! ### The uniform statement -/

/-- `px7_spec` with the constant chosen before `β` and `ρ`. The frozen hypothesis `FrozenHyp` at a
level `N` large enough, with `(νm, νp, c₀, Λ₀)` fixed, supplies the thermal density.
The constant `Cinv` depends only on `d, s, m, νm, νp, c₀, Λ₀` (and the decay constants that come
from those parameters), not on `β` or `ρ`. -/
theorem px7_spec_unif (hd2 : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (N : ℕ) (hN : px7_m d + 2 + mStar d + 3 ≤ N)
    (νm νp c₀ Λ₀ : ℝ) (J : ℕ) (hJ : px7_m d + px7_m d + 2 ≤ J) :
    ∃ Cinv : ℝ, 0 ≤ Cinv ∧ ∀ (β : ℝ) (hβ : 0 < β) (ρ : Torus d → ℝ),
      FrozenHyp d s N νm νp c₀ Λ₀ β V ρ → Torus.IsSmooth ρ → (∀ x, 0 < ρ x) →
      (∀ R : Torus d → Torus d → ℝ, IsCk2 J R → DoublyCentered (withDensityReal ρ) R →
        IsCk2 2 (pairInverse (mfData d s hs0 hsd V β hβ) ρ R) ∧
        DoublyCentered (withDensityReal ρ) (pairInverse (mfData d s hs0 hsd V β hβ) ρ R) ∧
        cbNorm2 2 (pairInverse (mfData d s hs0 hsd V β hβ) ρ R) ≤ Cinv * cbNorm2 J R ∧
        ∀ x y, -(centeredGen (mfData d s hs0 hsd V β hβ) ρ
            (fun x' => pairInverse (mfData d s hs0 hsd V β hβ) ρ R x' y) x +
          centeredGen (mfData d s hs0 hsd V β hβ) ρ
            (fun y' => pairInverse (mfData d s hs0 hsd V β hβ) ρ R x y') y) = R x y) ∧
      (∀ (R R' : Torus d → Torus d → ℝ) (a b : ℝ), IsCk2 J R → IsCk2 J R' →
        pairInverse (mfData d s hs0 hsd V β hβ) ρ (fun x y => a * R x y + b * R' x y) =
          fun x y => a * pairInverse (mfData d s hs0 hsd V β hβ) ρ R x y +
            b * pairInverse (mfData d s hs0 hsd V β hβ) ρ R' x y) ∧
      (∀ R : Torus d → Torus d → ℝ, IsCk2 J R → (∀ x y, R x y = R y x) →
        ∀ x y, pairInverse (mfData d s hs0 hsd V β hβ) ρ R x y =
          pairInverse (mfData d s hs0 hsd V β hβ) ρ R y x) ∧
      (∀ Δ R' : Torus d → Torus d → ℝ, IsCk2 (J + 2) Δ → IsCk2 J R' →
        DoublyCentered (withDensityReal ρ) Δ → DoublyCentered (withDensityReal ρ) R' →
        (∀ x y, centeredGen (mfData d s hs0 hsd V β hβ) ρ (fun x' => Δ x' y) x +
          centeredGen (mfData d s hs0 hsd V β hβ) ρ (fun y' => Δ x y') y = R' x y) →
        pairInverse (mfData d s hs0 hsd V β hβ) ρ R' = fun x y => -Δ x y) := by
  have hd1 : 1 ≤ d := by omega
  have hm : mStar d + 2 ≤ px7_m d := (px7_m_eq d).ge
  have hj0 : (d : ℝ) / 2 + 4 < ((px7_m d : ℕ) : ℝ) := by
    have : (d : ℝ) / 2 < (⌊(d : ℝ) / 2⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have e : ((px7_m d : ℕ) : ℝ) = (⌊(d : ℝ) / 2⌋₊ : ℝ) + 5 := by
      unfold px7_m; push_cast; ring
    rw [e]; linarith
  -- constants fixed before `β` and `ρ`: decay of the one-variable operator, ev and parseval bounds
  obtain ⟨M0, c0, hM0, hc0, hdec⟩ := px7_decay hd1 s (px7_m d) (px7_m d) hm le_rfl hj0 νm νp c₀ Λ₀
  have hm2 : (d : ℝ) + 4 < 2 * ((px7_m d : ℕ) : ℝ) := by linarith
  obtain ⟨A, hA, hev⟩ := px7_ev_C2 (d := d) (m := px7_m d) hm2
  obtain ⟨K, hK, hK'⟩ := px7_parseval (d := d) (px7_m d) (px7_m d)
  have hdata : ∀ R : Torus d → Torus d → ℝ, IsCk2 (px7_m d + px7_m d) R →
      Mem2 (px7_m d : ℝ) (px7_m d : ℝ) (arr R) ∧ RS (arr R) ∧
        nrm2 (px7_m d : ℝ) (px7_m d : ℝ) (arr R) ≤ K * cbNorm2 (px7_m d + px7_m d) R := by
    intro R hR
    obtain ⟨h1, h2⟩ := hK' R hR
    have hc : Continuous (lift2 R) := by
      have : IsCk2 0 R := hR.of_le (by exact_mod_cast Nat.zero_le _)
      simpa [IsCk2] using this.continuous
    exact ⟨h1, px7_arr_RS hc, h2⟩
  have hC0 : 0 ≤ A * (M0 ^ 2 * K) := mul_nonneg hA (mul_nonneg (sq_nonneg _) hK)
  have hc2 : 0 < 2 * c0 := by linarith
  have hCpos : 0 ≤ 3 * (A * (M0 ^ 2 * K)) / (2 * c0) :=
    div_nonneg (mul_nonneg (by norm_num) hC0) hc2.le
  refine ⟨3 * (A * (M0 ^ 2 * K)) / (2 * c0), hCpos, fun β hβ ρ H hρC hpos => ?_⟩
  have hρβ : IsThermalDensity (periodicRiesz d s) V β ρ := H.thermal
  have hOV := px7_oneVar_H hd1 s hs0 hsd β hβ V ρ N hN νm νp c₀ Λ₀ H
  -- the decay of the operator at this `β`, `ρ` with the constants fixed above
  have hop : ∀ τ : ℝ, 0 ≤ τ → OpOK ((px7_m d : ℕ) : ℝ)
      (px7_T (mfData d s hs0 hsd V β hβ) ρ (px7_m d) τ) (M0 * Real.exp (-c0 * τ)) := by
    intro τ hτ
    have Hd : FrozenHyp d s (px7_m d + mStar d + 3) νm νp c₀ Λ₀ β V ρ := H.mono (by omega)
    have Hm : FrozenHyp d s (px7_m d + 3) νm νp c₀ Λ₀ β V ρ := H.mono (by omega)
    exact ⟨fun x hx => (hdec β V ρ Hd x hx τ hτ).1, fun x hx => (hdec β V ρ Hd x hx τ hτ).2,
      fun x y hx hy => px7_T_add hd1 (px7_m d) hm Hm hx hy hτ,
      fun a x hx => px7_T_smul hd1 (px7_m d) hm Hm hx a hτ⟩
  have hC2 : ∀ R : Torus d → Torus d → ℝ, IsCk2 (px7_m d + px7_m d) R → ∀ τ : ℝ, 0 ≤ τ →
      IsCk2 2 (pairSemigroup (mfData d s hs0 hsd V β hβ) ρ τ R) ∧
        cbNorm2 2 (pairSemigroup (mfData d s hs0 hsd V β hβ) ρ τ R) ≤
          (A * (M0 ^ 2 * K) * cbNorm2 (px7_m d + px7_m d) R) * Real.exp (-(2 * c0) * τ) :=
    fun R hR τ hτ => px7_pair_C2_of hOV hM0 hop hA hev hdata R hR τ hτ
  have hinv := px7_inv_C2_of (C0 := A * (M0 ^ 2 * K)) (c0 := 2 * c0) hOV hc2 hC2
  have hJm : ∀ R : Torus d → Torus d → ℝ, IsCk2 J R → IsCk2 (px7_m d + px7_m d) R :=
    fun R hR => hR.of_le (by exact_mod_cast (by omega : px7_m d + px7_m d ≤ J))
  refine ⟨fun R hR hcen => ?_, fun R R' a b hR hR' => px7_inv_lin hOV (hJm R hR) (hJm R' hR') a b,
    fun R hR hs x y => px7_inv_symm hOV (hJm R hR) hs x y,
    fun Δ R' hΔ hR' hΔc hR'c heq => ?_⟩
  · obtain ⟨h1, h2, -⟩ := hinv R (hJm R hR)
    refine ⟨h1, px7_inv_cen hOV (hJm R hR), ?_, fun x y => px7_inv_pde hd2 s hs0 hsd β hβ V hV hρβ hρC
      hpos hOV (hR.of_le (by exact_mod_cast (by omega : px7_m d + px7_m d + 2 ≤ J))) hcen x y⟩
    exact h2.trans (mul_le_mul_of_nonneg_left (px7_cbNorm2_mono (by omega) R) hCpos)
  · exact px7_left_inverse hd2 s hs0 hsd β hβ V hV hρβ hρC hpos hOV
      (hΔ.of_le (by exact_mod_cast (by omega : px7_m d + px7_m d + 2 ≤ J + 2))) (hJm R' hR') hΔc heq

end HRS.ME.ParxU

end

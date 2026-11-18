import HRS.Equilibrium.Parametrix.PX5AuxD

/-!
# Prop 4.13 parametrix, packet PX5: the nonlocal term `𝒥ψ^loc` (bound)

The kernel `K(x,y) = J_x[ψ(·,y)](x)` is conormal of order `0` (`jop_general`), hence bounded by
`C w`; `Jpair ψ = P_xK + P_yK^T`.
-/

open MeasureTheory Filter Topology
noncomputable section

namespace HRS.Parx

variable {d : ℕ} {s : ℝ} {V : Torus d → ℝ} {β : ℝ} {ρ : Torus d → ℝ}

theorem px5_ae_ne (hd : 0 < d) (ρ : Torus d → ℝ) (y : Torus d) :
    ∀ᵐ w ∂(withDensityReal ρ), w ≠ y := by
  have h0 : (withDensityReal ρ) {y} = 0 :=
    withDensity_absolutelyContinuous _ _ (volume_singleton_torus hd y)
  have := (measure_eq_zero_iff_ae_notMem (μ := withDensityReal ρ) (s := {y})).1 h0
  filter_upwards [this] with w hw using hw

/-- pointwise value bound against a generic envelope -/
theorem px5_value_bound {τ : ℝ} {b : ℕ → ℕ} {m : ℕ} {B Cw : ℝ} {F : Torus d → Torus d → ℝ}
    (hF : ConormalL τ b m B F) (hB : 0 ≤ B) (hCw0 : 0 ≤ Cw) {E : ℝ → ℝ}
    (hE : ∀ r, 0 ≤ r → 1 ≤ E r)
    (hw : ∀ r : ℝ, 0 < r → r < r0 → r ^ (-(τ + ((0 : ℕ) : ℝ))) * (1 + |Real.log r|) ^ b 0 ≤ Cw * E r)
    (x y : Torus d) (hxy : x ≠ y) :
    |F x y| ≤ B * (1 + Cw) * E (rTrunc x y) := by
  have hp : ((Torus.rep x, Torus.rep y) : Euc d × Euc d) ∈ offDiag d := by
    show Torus.mk (Torus.rep x) ≠ Torus.mk (Torus.rep y)
    rw [Torus.mk_rep, Torus.mk_rep]; exact hxy
  have hr0 : 0 ≤ rTrunc x y := le_min zero_le_one (Real.sqrt_nonneg _)
  have hT1 := hE _ hr0
  have hBC : 0 ≤ B * (1 + Cw) := by positivity
  have e : lift2 F (Torus.rep x, Torus.rep y) = F x y := by simp [lift2, Torus.mk_rep]
  have hmk : rTrunc (Torus.mk (Torus.rep x)) (Torus.mk (Torus.rep y)) = rTrunc x y := by
    rw [Torus.mk_rep, Torus.mk_rep]
  by_cases hdist : Torus.eucDist x y < r0
  · have hdist' : Torus.eucDist (Torus.mk (Torus.rep x, Torus.rep y).1)
        (Torus.mk (Torus.rep x, Torus.rep y).2) < r0 := by
      simpa [Torus.mk_rep] using hdist
    obtain ⟨X, z, n, hz, hzn, hpe⟩ := px5_near_rep hp hdist'
    have hzr : ‖z‖ < r0 := by rw [hzn]; exact hdist'
    have hrT : rTrunc x y = ‖z‖ := by
      rw [rTrunc_eq_of_lt hdist, hzn]; simp [Torus.mk_rep]
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hTz : 1 ≤ E ‖z‖ := hE _ hzpos.le
    have hnear : ‖mixedDeriv 0 0 (toChart F) X z‖ ≤ B * (1 + Cw) * E ‖z‖ := by
      refine (hF.near 0 0 (Nat.zero_le _) X z hz hzr).trans ?_
      have h1 := hw ‖z‖ hzpos hzr
      calc B * (1 + ‖z‖ ^ (-(τ + ((0 : ℕ) : ℝ))) * (1 + |Real.log ‖z‖|) ^ b 0)
          ≤ B * (1 + Cw * E ‖z‖) := mul_le_mul_of_nonneg_left (by linarith) hB
        _ ≤ B * ((1 + Cw) * E ‖z‖) := by
            refine mul_le_mul_of_nonneg_left ?_ hB
            nlinarith
        _ = _ := by ring
    have hEz : 0 ≤ B * (1 + Cw) * E ‖z‖ := by positivity
    have h := px5_near_full hF hz hzr (k := 0) (Nat.zero_le _) hEz
      (fun a c hac => by
        have ha : a = 0 := by omega
        have hc : c = 0 := by omega
        subst ha; subst hc; exact hnear)
    rw [norm_iteratedFDeriv_zero] at h
    have e2 : F x y = lift2 F (chartT d (X, z)) := by
      rw [← e, hpe]
      exact lift2_periodic_fst F _ n
    rw [e2, hrT]
    simpa using h
  · push Not at hdist
    have hfar := hF.far 0 (Nat.zero_le _) (Torus.rep x, Torus.rep y) hp (by
      simpa [Torus.mk_rep] using hdist)
    rw [norm_iteratedFDeriv_zero, e, Real.norm_eq_abs] at hfar
    calc |F x y| ≤ B := hfar
      _ ≤ B * (1 + Cw) * E (rTrunc x y) := by nlinarith


/-- the kernel `K(x,y) = J_x[ψ(·,y)](x)` (set to `0` on the diagonal) -/
def px5K (d : ℕ) (s : ℝ) (ρ : Torus d → ℝ) (ψ : Torus d → Torus d → ℝ) : Torus d → Torus d → ℝ :=
  offZero fun x y => Jop d s ρ (fun z => ψ z y) x

theorem px5K_diag (ψ : Torus d → Torus d → ℝ) (x : Torus d) : px5K d s ρ ψ x x = 0 := by
  simp [px5K, offZero]

theorem px5_K_class (H : ParxHyp d s V β ρ) (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Torus d → ℝ, Torus.IsSmooth f →
      Conormal 0 3 (J + 1) (C * posSeminorm (px5m d J + 2) f)
        (px5K d s ρ (parxPsi d s V β ρ f (parxL d J))) := by
  obtain ⟨Cp, hCp0, hCp⟩ := px5_psi_class H J
  obtain ⟨CJ, hCJ0, hCJ⟩ := jop_general H (s - 2) (px5_crit_lt H) 1 (J + 3) (by omega)
  refine ⟨CJ * Cp, mul_nonneg hCJ0 hCp0, fun f hf => ?_⟩
  have hB0 : 0 ≤ Cp * posSeminorm (px5m d J + 2) f := mul_nonneg hCp0 (posSeminorm_nonneg' _ _)
  have h := hCJ _ _ hB0 (hCp f hf)
  have e1 : s - 2 + 2 - s = 0 := by ring
  have e2 : J + 3 - 2 = J + 1 := by omega
  rw [e1, e2] at h
  have e3 : CJ * (Cp * posSeminorm (px5m d J + 2) f) = CJ * Cp * posSeminorm (px5m d J + 2) f := by ring
  rw [e3] at h
  exact h

theorem px5_wEnv_ge_one (s : ℝ) (x y : Torus d) : 1 ≤ wEnv s x y := by
  unfold wEnv
  have : 0 ≤ rTrunc x y ^ (-s) := Real.rpow_nonneg (le_min zero_le_one (Real.sqrt_nonneg _)) _
  linarith

theorem px5_wEnv_symm (s : ℝ) (x y : Torus d) : wEnv s x y = wEnv s y x := by
  unfold wEnv rTrunc
  rw [eucDist_comm x y]

/-- `|K| ≤ B (1 + Cw) w` for a conormal kernel of order `0` with log index `3` -/
theorem px5_K_pointwise (H : ParxHyp d s V β ρ) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ {B : ℝ} {F : Torus d → Torus d → ℝ}, 0 ≤ B → Conormal 0 3 0 B F →
      ∀ x y, x ≠ y → |F x y| ≤ B * (1 + Cw) * wEnv s x y := by
  have hs0 := px5_s_pos H
  obtain ⟨C0, hC0, hC⟩ := rpow_log_pow_le s hs0 3
  refine ⟨C0, hC0, fun {B F} hB hF x y hxy => ?_⟩
  refine px5_value_bound hF hB hC0 (E := fun r => 1 + r ^ (-s)) (fun r hr => ?_) (fun r hr0 hrr => ?_)
    x y hxy
  · have : 0 ≤ r ^ (-s) := Real.rpow_nonneg hr _
    linarith
  · have hr1 : r ≤ 1 := by unfold r0 at hrr; linarith
    have h1 := hC r hr0 hr1
    have e : r ^ (-s) * r ^ s = 1 := by rw [← Real.rpow_add hr0]; simp
    have e2 : (1 + |Real.log r|) ^ 3 = r ^ (-s) * (r ^ s * (1 + |Real.log r|) ^ 3) := by
      rw [← mul_assoc, e, one_mul]
    simp only [add_zero, Nat.cast_zero, neg_zero, Real.rpow_zero, one_mul]
    rw [e2]
    have h3 : 0 ≤ r ^ (-s) := Real.rpow_nonneg hr0.le _
    calc r ^ (-s) * (r ^ s * (1 + |Real.log r|) ^ 3) ≤ r ^ (-s) * C0 :=
          mul_le_mul_of_nonneg_left h1 h3
      _ ≤ C0 * (1 + r ^ (-s)) := by nlinarith

theorem px5_K_rowcol (H : ParxHyp d s V β ρ) :
    ∃ Kr : ℝ, 0 ≤ Kr ∧ ∀ {B : ℝ} {F : Torus d → Torus d → ℝ}, 0 ≤ B → Conormal 0 3 0 B F →
      (∀ x, F x x = 0) →
      (∀ x, Integrable (fun y => F x y) (withDensityReal ρ) ∧
        ∫ y, |F x y| ∂(withDensityReal ρ) ≤ Kr * B) ∧
      (∀ y, Integrable (fun x => F x y) (withDensityReal ρ) ∧
        ∫ x, |F x y| ∂(withDensityReal ρ) ≤ Kr * B) := by
  obtain ⟨Kr, hKr0, hKr⟩ := conormal_row_int H.two_le H.rho_smooth (σ := (0 : ℝ))
    (by have := H.two_le; have : (2 : ℝ) ≤ d := by exact_mod_cast H.two_le
        linarith) 3
  refine ⟨Kr, hKr0, fun {B F} hB hF hdiag => ⟨fun x => hKr B F hB hF hdiag x, fun y => ?_⟩⟩
  exact hKr B (swapK F) hB (conormalL_swap hF) (fun x => hdiag x) y

theorem px5_jpair_formula (hd : 0 < d) (ψ : Torus d → Torus d → ℝ) (hψ : IsSymmPair ψ) (x y : Torus d)
    (hxy : x ≠ y) :
    Jpair d s ρ ψ x y = (px5K d s ρ ψ x y - ∫ z, px5K d s ρ ψ z y ∂(withDensityReal ρ)) +
      (px5K d s ρ ψ y x - ∫ z, px5K d s ρ ψ z x ∂(withDensityReal ρ)) := by
  unfold Jpair projMean pair
  have e1 : ∀ y' : Torus d, ∫ z, Jop d s ρ (fun w => ψ w y') z ∂(withDensityReal ρ) =
      ∫ z, px5K d s ρ ψ z y' ∂(withDensityReal ρ) := by
    intro y'
    refine integral_congr_ae ?_
    filter_upwards [px5_ae_ne hd ρ y'] with z hz
    simp [px5K, offZero, hz]
  have e2 : (fun w => ψ x w) = fun w => ψ w x := funext fun w => hψ x w
  simp only [e2, e1]
  have h1 : Jop d s ρ (fun w => ψ w y) x = px5K d s ρ ψ x y := by simp [px5K, offZero, hxy]
  have h2 : Jop d s ρ (fun w => ψ w x) y = px5K d s ρ ψ y x := by simp [px5K, offZero, Ne.symm hxy]
  rw [h1, h2]

theorem px5_jpair_bound (H : ParxHyp d s V β ρ) (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Torus d → ℝ, Torus.IsSmooth f → ∀ x y, x ≠ y →
      |Jpair d s ρ (parxPsi d s V β ρ f (parxL d J)) x y| ≤
        C * posSeminorm (px5m d J + 2) f * wEnv s x y := by
  obtain ⟨CK, hCK0, hCK⟩ := px5_K_class H J
  obtain ⟨Cw, hCw0, hCw⟩ := px5_K_pointwise H
  obtain ⟨Kr, hKr0, hKr⟩ := px5_K_rowcol H
  refine ⟨CK * (2 * (1 + Cw) + 2 * Kr), by positivity, fun f hf x y hxy => ?_⟩
  set ψ := parxPsi d s V β ρ f (parxL d J) with hψ
  set B := CK * posSeminorm (px5m d J + 2) f with hB
  have hB0 : 0 ≤ B := mul_nonneg hCK0 (posSeminorm_nonneg' _ _)
  have hcl := hCK f hf
  have hcl0 : Conormal 0 3 0 B (px5K d s ρ ψ) :=
    ConormalL.mono hcl hB0 le_rfl (fun c => le_rfl) (Nat.zero_le _) le_rfl
  have hsym := px5_symm H J f hf
  have hd : 0 < d := by have := H.two_le; omega
  rw [px5_jpair_formula hd ψ hsym x y hxy]
  obtain ⟨hrow, hcol⟩ := hKr hB0 hcl0 (px5K_diag ψ)
  have p1 := hCw hB0 hcl0 x y hxy
  have p2 := hCw hB0 hcl0 y x (Ne.symm hxy)
  rw [px5_wEnv_symm s y x] at p2
  have m1 : |∫ z, px5K d s ρ ψ z y ∂(withDensityReal ρ)| ≤ Kr * B :=
    (abs_integral_le_integral_abs).trans (hcol y).2
  have m2 : |∫ z, px5K d s ρ ψ z x ∂(withDensityReal ρ)| ≤ Kr * B :=
    (abs_integral_le_integral_abs).trans (hcol x).2
  have hw := px5_wEnv_ge_one s x y
  calc |(px5K d s ρ ψ x y - ∫ z, px5K d s ρ ψ z y ∂(withDensityReal ρ)) +
        (px5K d s ρ ψ y x - ∫ z, px5K d s ρ ψ z x ∂(withDensityReal ρ))|
      ≤ |px5K d s ρ ψ x y| + |∫ z, px5K d s ρ ψ z y ∂(withDensityReal ρ)| +
        (|px5K d s ρ ψ y x| + |∫ z, px5K d s ρ ψ z x ∂(withDensityReal ρ)|) := by
        refine (abs_add_le _ _).trans ?_
        exact add_le_add (abs_sub _ _) (abs_sub _ _)
    _ ≤ B * (1 + Cw) * wEnv s x y + Kr * B + (B * (1 + Cw) * wEnv s x y + Kr * B) := by
        gcongr
    _ ≤ CK * (2 * (1 + Cw) + 2 * Kr) * posSeminorm (px5m d J + 2) f * wEnv s x y := by
        rw [hB]
        have hp := posSeminorm_nonneg' (px5m d J + 2) f
        have h1 : 0 ≤ CK * posSeminorm (px5m d J + 2) f * Kr := by positivity
        nlinarith

end HRS.Parx

end

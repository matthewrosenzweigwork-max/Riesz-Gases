import HRS.MC.S7S7bAux3

/-!
# Packet `s7_S7b_weighted_moments`, helper 4: `E_Q |B_{N,v}|^{2q} <= M Lam^{2q}`
(for `0 < gamma`, from the exponential pair estimate; the constants do not depend on `v`, `N`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7b

open HRS HRS.Sec7 HRS.MC.SEdge

variable {d : ℕ} {s : ℝ}

theorem s7b_add_pow_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    (a + b) ^ n ≤ 2 ^ n * (a ^ n + b ^ n) := by
  rcases le_total a b with h | h
  · calc (a + b) ^ n ≤ (2 * b) ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
      _ = 2 ^ n * b ^ n := mul_pow _ _ _
      _ ≤ 2 ^ n * (a ^ n + b ^ n) := by
          gcongr
          exact le_add_of_nonneg_left (pow_nonneg ha _)
  · calc (a + b) ^ n ≤ (2 * a) ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
      _ = 2 ^ n * a ^ n := mul_pow _ _ _
      _ ≤ 2 ^ n * (a ^ n + b ^ n) := by
          gcongr
          exact le_add_of_nonneg_right (pow_nonneg hb _)

/-- `modulatedEnergy` is linear in the kernel. -/
theorem s7b_mE_smul {N : ℕ} (a : ℝ) (k : Torus d → Torus d → ℝ) (X : Config d N)
    (μ : Measure (Torus d)) :
    modulatedEnergy (fun x y => a * k x y) X μ = a * modulatedEnergy k X μ := by
  unfold modulatedEnergy
  simp only [← Finset.mul_sum, integral_const_mul]
  ring

theorem s7b_B_moment (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {γ : ℝ} (hγ : 0 < γ)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) (q : ℕ) :
    ∃ K M : ℝ, 0 ≤ K ∧ 0 ≤ M ∧ ∀ (v : Fin d → Torus d → ℝ) (L : Fin d → ℝ),
      (∀ j, Torus.IsSmooth (v j)) → (∀ k, 0 ≤ L k) →
      (∀ k, HRS.KernelGrad.IsLipschitz (L k) (v k)) → ∀ Λ : ℝ, 0 < Λ → K * ∑ k, L k ≤ Λ →
      ∀ N : ℕ, 1 ≤ N →
        Integrable (fun X => |sed_B d s ρ γ v X| ^ (2 * q)) (sed_Q d s N γ ρ) ∧
          ∫ X, |sed_B d s ρ γ v X| ^ (2 * q) ∂(sed_Q d s N γ ρ) ≤ M * Λ ^ (2 * q) := by
  have hsd : s < (d : ℝ) := by
    have : (0 : ℝ) ≤ d := by positivity
    linarith
  obtain ⟨K, c, hK0, hc0, hw, henv⟩ := s7b_envelope hd hs0 hs
  obtain ⟨θ, M₀, hθ, hM₀, hexp⟩ := s7b_expmom hd hs0 hs hγ hρ c hw
  set A : ℕ → ℝ := fun p => (p.factorial : ℝ) * θ⁻¹ ^ p * M₀ with hA
  have hA0 : ∀ p, 0 ≤ A p := fun p => by simp only [hA]; positivity
  refine ⟨K, 2 ^ (2 * q) * (A (2 * q) + A 1 ^ (2 * q)), hK0, by
    have := hA0 (2 * q); have := hA0 1; positivity, ?_⟩
  intro v L hv hL0 hL Λ hΛ hKΛ N hN
  haveI hQ : IsProbabilityMeasure (sed_Q d s N γ ρ) :=
    HRS.MC.SEdge.B4b.b4b_isProb hd hs0 hs hγ.le hρ N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hvc : ∀ j, Continuous (v j) := fun j => HRS.StaticLimitAux.continuous_of_smooth (hv j)
  have hgc : ∀ x y, 0 ≤ periodicRiesz d s (x - y) + c := by
    intro x y
    by_cases hxy : x = y
    · subst hxy; simpa using hc0
    · have := hw (x - y) (sub_ne_zero.mpr hxy)
      linarith
  -- the normalised kernel
  set h : Torus d → Torus d → ℝ := fun x y => Λ⁻¹ * Q66.q66_hv d s v x y with hh
  have hm : Measurable (Function.uncurry h) :=
    measurable_const.mul (Q66.q66_hv_measurable hsd hvc)
  have hsym : ∀ x y, h x y = h y x := fun x y => by
    simp only [hh]; rw [Q66.q66_hv_symm hsd v x y]
  have hdom : ∀ x y, |h x y| ≤ periodicRiesz d s (x - y) + c := by
    intro x y
    simp only [hh]
    rw [abs_mul, abs_of_pos (inv_pos.2 hΛ)]
    have h1 := henv v L hL0 hL x y
    have h2 : K * (∑ k, L k) * (periodicRiesz d s (x - y) + c) ≤
        Λ * (periodicRiesz d s (x - y) + c) :=
      mul_le_mul_of_nonneg_right hKΛ (hgc x y)
    calc Λ⁻¹ * |Q66.q66_hv d s v x y| ≤ Λ⁻¹ * (Λ * (periodicRiesz d s (x - y) + c)) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (inv_pos.2 hΛ).le
      _ = _ := by field_simp
  have hexpN := hexp h hm hsym hdom N hN
  -- `Z' = N * mE h`, `Z = N * mE h_v = Λ * Z'`
  obtain ⟨hYm, -, -⟩ := HRS.MC.SEdge.B4b.b4b_L2 hd hs0 hs hρ hv N hN
  set Z : Config d N → ℝ := fun X => (N : ℝ) *
    modulatedEnergy (Q66.q66_hv d s v) X (withDensityReal ρ) with hZ
  have hZm : Measurable Z := by
    have : Z = fun X => HRS.MC.SEdge.B4b.b4b_Y d s ρ v N X -
        (1 / 2) * ∫ x, ∫ y, Q66.q66_hv d s v x y ∂(withDensityReal ρ) ∂(withDensityReal ρ) := by
      funext X; simp only [hZ, HRS.MC.SEdge.B4b.b4b_Y]; ring
    rw [this]
    exact hYm.sub_const _
  set Z' : Config d N → ℝ := fun X => (N : ℝ) * modulatedEnergy h X (withDensityReal ρ) with hZ'
  have hZZ' : ∀ X, Z X = Λ * Z' X := by
    intro X
    simp only [hZ, hZ', hh]
    rw [s7b_mE_smul]
    field_simp
  have hZ'm : Measurable Z' := by
    have : Z' = fun X => Λ⁻¹ * Z X := by
      funext X; rw [hZZ' X]; field_simp
    rw [this]
    exact measurable_const.mul hZm
  have hEZ' : ∫⁻ X, ENNReal.ofReal (Real.exp (θ * |Z' X|)) ∂(sed_Q d s N γ ρ) ≤ ENNReal.ofReal M₀ := by
    refine le_trans (le_of_eq ?_) hexpN
    refine lintegral_congr fun X => ?_
    have : θ * |Z' X| = θ * N * |modulatedEnergy h X (withDensityReal ρ)| := by
      simp only [hZ']; rw [abs_mul, abs_of_pos hNpos]; ring
    rw [this]
  have mom := fun p => s7b_moment_of_exp (sed_Q d s N γ ρ) hZ'm hθ hM₀ hEZ' p
  -- moments of `Z`
  have momZ : ∀ p : ℕ, Integrable (fun X => |Z X| ^ p) (sed_Q d s N γ ρ) ∧
      ∫ X, |Z X| ^ p ∂(sed_Q d s N γ ρ) ≤ A p * Λ ^ p := by
    intro p
    obtain ⟨hi, hb⟩ := mom p
    have e : (fun X => |Z X| ^ p) = fun X => Λ ^ p * |Z' X| ^ p := by
      funext X; rw [hZZ' X, abs_mul, abs_of_pos hΛ, mul_pow]
    rw [e]
    refine ⟨hi.const_mul _, ?_⟩
    rw [integral_const_mul]
    calc Λ ^ p * ∫ X, |Z' X| ^ p ∂(sed_Q d s N γ ρ) ≤ Λ ^ p * A p :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by ring
  set m : ℝ := ∫ X, Z X ∂(sed_Q d s N γ ρ) with hmdef
  have hm1 : |m| ≤ A 1 * Λ := by
    have h1 := (momZ 1).1
    simp only [pow_one] at h1
    have := (momZ 1).2
    simp only [pow_one] at this
    exact (abs_integral_le_integral_abs).trans this
  have hB : ∀ X, sed_B d s ρ γ v X = Z X - m := by
    intro X
    simp only [sed_B, hZ, hmdef]
    rw [integral_const_mul]
    ring
  have hBm : Measurable (fun X : Config d N => sed_B d s ρ γ v X) := by
    have : (fun X : Config d N => sed_B d s ρ γ v X) = fun X => Z X - m := funext hB
    rw [this]
    exact hZm.sub_const _
  have hpt : ∀ X, |sed_B d s ρ γ v X| ^ (2 * q) ≤
      2 ^ (2 * q) * (|Z X| ^ (2 * q) + (A 1 * Λ) ^ (2 * q)) := by
    intro X
    rw [hB X]
    calc |Z X - m| ^ (2 * q) ≤ (|Z X| + |m|) ^ (2 * q) :=
          pow_le_pow_left₀ (abs_nonneg _) (abs_sub _ _) _
      _ ≤ 2 ^ (2 * q) * (|Z X| ^ (2 * q) + |m| ^ (2 * q)) :=
          s7b_add_pow_le _ _ (abs_nonneg _) (abs_nonneg _) _
      _ ≤ _ := by
          gcongr
  have hdomI : Integrable (fun X => 2 ^ (2 * q) * (|Z X| ^ (2 * q) + (A 1 * Λ) ^ (2 * q)))
      (sed_Q d s N γ ρ) :=
    ((momZ (2 * q)).1.add (integrable_const _)).const_mul _
  refine ⟨?_, ?_⟩
  · refine Integrable.mono' hdomI (hBm.abs.pow_const _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
    exact hpt X
  · calc ∫ X, |sed_B d s ρ γ v X| ^ (2 * q) ∂(sed_Q d s N γ ρ)
        ≤ ∫ X, 2 ^ (2 * q) * (|Z X| ^ (2 * q) + (A 1 * Λ) ^ (2 * q)) ∂(sed_Q d s N γ ρ) := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun X => by positivity)
            hdomI (Filter.Eventually.of_forall hpt)
      _ = 2 ^ (2 * q) * (∫ X, |Z X| ^ (2 * q) ∂(sed_Q d s N γ ρ) + (A 1 * Λ) ^ (2 * q)) := by
          rw [integral_const_mul, integral_add (momZ (2 * q)).1 (integrable_const _)]
          simp
      _ ≤ 2 ^ (2 * q) * (A (2 * q) * Λ ^ (2 * q) + (A 1 * Λ) ^ (2 * q)) := by
          gcongr
          exact (momZ (2 * q)).2
      _ = 2 ^ (2 * q) * (A (2 * q) + A 1 ^ (2 * q)) * Λ ^ (2 * q) := by
          rw [mul_pow]; ring

end HRS.MC.Sec7.S7b

end

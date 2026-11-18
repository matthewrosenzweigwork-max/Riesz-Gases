import HRS.Energy.WeakReference
import HRS.Energy.PressureAlg
import HRS.Energy.PressureDV
import HRS.Energy.PressureSplit

/-!
# HRS.Energy.PressureProof — proof of Proposition 5.5 (perturbed partition functions)

Proposition 5.5 `N:prop:pressure` (main paper, source lines 6118-6137; proof lines 6344-6406).
The statement `perturbed_pressure` was moved here verbatim from `HRS/Energy/Pressure.lean` (the proof needs
Lemma 5.7 of `HRS/Energy/WeakReference.lean`, which imports `Pressure.lean`).

Route (`N:eq:heat-split` ... `N:eq:pair-entropy`):
1. (`PressureSplit.lean`) `g = g_L + q - c`, `g_L = ∑ a_k cos`, `q ≥ 0` even, `∫ q = c ≤ ε`, envelope
   `q ≤ E₀ (g + c_*)` uniform in `ε ≤ 1`.
2. (`pressure_upper_core`) `|h| ≤ B' q + D`; for `|θ|` small `q_θ = q - θ h + |θ| D ≥ q/2 ≥ 0` is a weak kernel
   (`q_θ ≤ A w`, row bound `< a₀`), `g - θ h = g_L + q_θ - (c + |θ| D)` off the diagonal, and the energy of
   the positive-definite finite part is `≥ -(∑ a)/(2N)` (`psd_energy_lower`); hence
   `K^{g-θh} ≤ e^{β ∑a / 2} K^{q_θ}` (`N:eq:discard-positive`); Lemma 5.7 bounds `K^{q_θ}`.
3. (`pressure_lower_core`) Jensen: `K^k ≥ exp(-β N E[F^k]) = exp((β/2) ∬ k dμ²)` and `|∬ k| ≤ O(1)`.
4. (`tilt`) `E_Q[e^{λ N F^h}] = K^{g - (λ/β) h} / K^g` (`N:eq:tilt-partition`); `e^{|x|} ≤ e^x + e^{-x}`
   and `N δ_N ≥ 1` absorb the factor `2`.
5. (`PressureDV.lean`) the entropy inequality `∫ F dν ≤ KL(ν ‖ Q) + log ∫ e^F dQ` gives `N:eq:pair-entropy`.
The proportionality constants are chosen in the order `A → (a₀, C_w) → ε → split → D → θ₀`.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HRS

variable {d : ℕ}

section Basic

theorem measurable_modulatedEnergy {N : ℕ} {μ : Measure (Torus d)} [SFinite μ]
    {k : Torus d → Torus d → ℝ} (hk : RowOK μ k) :
    Measurable (fun X : Config d N => modulatedEnergy k X μ) := by
  unfold modulatedEnergy
  refine ((measurable_const.mul (Finset.measurable_sum _ fun i _ =>
    Finset.measurable_sum _ fun j _ => ?_)).sub (measurable_const.mul (Finset.measurable_sum _ fun i _ =>
    ?_))).add measurable_const
  · exact (hk.meas.comp ((measurable_pi_apply i).prodMk (measurable_pi_apply j)) :
      Measurable fun X : Config d N => Function.uncurry k (X i, X j))
  · exact hk.measurable_rowInt.comp (measurable_pi_apply i)

theorem withDensityReal_le_smul {ρ : Torus d → ℝ} {Λ₀ : ℝ} (hρΛ : ∀ x, ρ x ≤ Λ₀) :
    withDensityReal ρ ≤ ENNReal.ofReal Λ₀ • (volume : Measure (Torus d)) := by
  unfold withDensityReal
  rw [← withDensity_const]
  exact withDensity_mono (Filter.Eventually.of_forall fun x => ENNReal.ofReal_le_ofReal (hρΛ x))

theorem withDensityReal_singleton (hd : 1 ≤ d) (ρ : Torus d → ℝ) (x : Torus d) :
    withDensityReal ρ {x} = 0 :=
  withDensity_absolutelyContinuous _ _ (volume_singleton_torus hd x)

/-- A measurable kernel dominated by `W(x - y)` (`W` integrable) has `L¹(μ)`-bounded rows. -/
theorem rowOK_of_dom {ρ : Torus d → ℝ} {Λ₀ : ℝ} (hΛ₀ : 0 ≤ Λ₀) (hρΛ : ∀ x, ρ x ≤ Λ₀)
    {W : Torus d → ℝ} (hW : Integrable W) {k : Torus d → Torus d → ℝ}
    (hk : Measurable (Function.uncurry k)) (hdom : ∀ x y, |k x y| ≤ W (x - y)) :
    RowOK (withDensityReal ρ) k ∧ ∀ x, ∫ y, |k x y| ∂(withDensityReal ρ) ≤ Λ₀ * ∫ z, W z := by
  have hμle := withDensityReal_le_smul hρΛ
  have hrow : ∀ x, Integrable (k x) (volume : Measure (Torus d)) := fun x => by
    have hWx : Integrable (fun y => W (x - y)) (volume : Measure (Torus d)) := hW.comp_sub_left x
    exact Integrable.mono' hWx (hk.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by simpa using hdom x y)
  have hbd : ∀ x, ∫ y, |k x y| ∂(withDensityReal ρ) ≤ Λ₀ * ∫ z, W z := by
    intro x
    have hWx : Integrable (fun y => W (x - y)) (volume : Measure (Torus d)) := hW.comp_sub_left x
    calc ∫ y, |k x y| ∂(withDensityReal ρ)
        ≤ ∫ y, |k x y| ∂(ENNReal.ofReal Λ₀ • (volume : Measure (Torus d))) :=
          integral_mono_measure hμle (Filter.Eventually.of_forall fun y => abs_nonneg _)
            ((hrow x).abs.smul_measure ENNReal.ofReal_ne_top)
      _ = Λ₀ * ∫ y, |k x y| := by
          rw [integral_smul_measure, ENNReal.toReal_ofReal hΛ₀, smul_eq_mul]
      _ ≤ Λ₀ * ∫ y, W (x - y) :=
          mul_le_mul_of_nonneg_left (integral_mono (hrow x).abs hWx fun y => hdom x y) hΛ₀
      _ = Λ₀ * ∫ z, W z := by rw [integral_sub_left_eq_self W volume x]
  refine ⟨⟨hk, fun x => (hrow x).smul_measure ENNReal.ofReal_ne_top |>.mono_measure hμle, ⟨_, hbd⟩⟩, hbd⟩

end Basic

section Upper

variable {N : ℕ}

/-- `N:eq:perturbed-q` and `N:eq:discard-positive`: `K^{g-θh} ≤ e^{β ∑a/2} K^{q_θ}` with
`q_θ = q - θ h + |θ| D`, for a split `g = ∑ a_k cos + q - c` and `|h| ≤ B' q + D`. -/
theorem pressure_upper_core {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    (hμ0 : ∀ x, μ {x} = 0) (Λ : Finset (Lattice d)) (a : Lattice d → ℝ) (ha : ∀ k ∈ Λ, 0 ≤ a k)
    (g q : Torus d → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hsplit : ∀ x : Torus d, x ≠ 0 → g x = ∑ k ∈ Λ, a k * Torus.cosMode k x + q x - c)
    (hgLR : RowOK μ (fun x y => ∑ k ∈ Λ, a k * Torus.cosMode k (x - y)))
    (hqR : RowOK μ (fun x y => q (x - y))) {h : Torus d → Torus d → ℝ} (hhR : RowOK μ h)
    (θ D : ℝ) (hD : 0 ≤ D) (hN : 1 ≤ N) {β : ℝ} (hβ : 0 ≤ β) :
    ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-β * N *
        modulatedEnergy (fun x y => g (x - y) - θ * h x y) X μ)) ∂(Measure.pi fun _ => μ) ≤
      ENNReal.ofReal (Real.exp (β * (∑ k ∈ Λ, a k) / 2)) *
        pairPartition (fun x y => q (x - y) - θ * h x y + |θ| * D) N β μ := by
  set qθ : Torus d → Torus d → ℝ := fun x y => q (x - y) - θ * h x y + |θ| * D with hqθ
  set c' : ℝ := c + |θ| * D with hc'
  have hc'0 : 0 ≤ c' := by positivity
  have hqθR : RowOK μ qθ := by
    have h1 := (hqR.add (hhR.smul (-θ))).add (RowOK.const (|θ| * D))
    have hfun : qθ = fun x y => (q (x - y) + (-θ) * h x y) + |θ| * D := by
      funext x y; simp only [hqθ]; ring
    rw [hfun]; exact h1
  have hk1R : RowOK μ (fun x y => (∑ k ∈ Λ, a k * Torus.cosMode k (x - y)) + qθ x y) :=
    hgLR.add hqθR
  have hpt : ∀ x y : Torus d, x ≠ y →
      g (x - y) - θ * h x y =
        ((∑ k ∈ Λ, a k * Torus.cosMode k (x - y)) + qθ x y) - c' := by
    intro x y hxy
    have := hsplit (x - y) (sub_ne_zero.2 hxy)
    simp only [hqθ, hc']
    rw [this]; ring
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hae := ae_injective_pi (N := N) hμ0
  refine le_trans (lintegral_mono_ae ?_)
    (le_of_eq (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top))
  filter_upwards [hae] with X hX
  have e0 : modulatedEnergy (fun x y => g (x - y) - θ * h x y) X μ =
      modulatedEnergy (fun x y => ((∑ k ∈ Λ, a k * Torus.cosMode k (x - y)) + qθ x y) - c') X μ :=
    modulatedEnergy_congr_offdiag hμ0 hpt X hX
  have e1 : modulatedEnergy (fun x y => ((∑ k ∈ Λ, a k * Torus.cosMode k (x - y)) + qθ x y) - c') X μ =
      modulatedEnergy (fun x y => ∑ k ∈ Λ, a k * Torus.cosMode k (x - y)) X μ +
        modulatedEnergy qθ X μ - modulatedEnergy (fun _ _ => c') X μ := by
    rw [modulatedEnergy_sub hk1R (RowOK.const c'), modulatedEnergy_add hgLR hqθR]
  have e2 : modulatedEnergy (fun _ _ => c') X μ = -c' / (2 * N) := modulatedEnergy_const c' X μ hN
  have hpsd := psd_energy_lower hN μ Λ a ha X
  have hmain : -β * N * modulatedEnergy (fun x y => g (x - y) - θ * h x y) X μ ≤
      β * (∑ k ∈ Λ, a k) / 2 + (-β * N * modulatedEnergy qθ X μ) := by
    rw [e0, e1, e2]
    have h3 : (N : ℝ) * (-c' / (2 * N)) = -c' / 2 := by field_simp
    have h4 : -β * N * (modulatedEnergy (fun x y => ∑ k ∈ Λ, a k * Torus.cosMode k (x - y)) X μ +
        modulatedEnergy qθ X μ - -c' / (2 * N)) =
        -β * ((N : ℝ) * modulatedEnergy (fun x y => ∑ k ∈ Λ, a k * Torus.cosMode k (x - y)) X μ) +
          (-β * N * modulatedEnergy qθ X μ) + β * ((N : ℝ) * (-c' / (2 * N))) * (-1) * (-1) := by ring
    rw [h4, h3]
    nlinarith [mul_nonneg hβ hc'0]
  have : ENNReal.ofReal (Real.exp (-β * N * modulatedEnergy (fun x y => g (x - y) - θ * h x y) X μ)) ≤
      ENNReal.ofReal (Real.exp (β * (∑ k ∈ Λ, a k) / 2)) *
        ENNReal.ofReal (Real.exp (-β * N * modulatedEnergy qθ X μ)) := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 hmain)
  exact this

end Upper

section Lower

variable {N : ℕ}

/-- Jensen lower bound `K^k ≥ exp(-β N E[F^k]) = exp((β/2) ∬ k dμ²) ≥ exp(-β M/2)`. -/
theorem pressure_lower_core {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    {k : Torus d → Torus d → ℝ} (hk : RowOK μ k) {M : ℝ} (hM : ∀ x, ∫ y, |k x y| ∂μ ≤ M)
    (hN : 1 ≤ N) {β : ℝ} (hβ : 0 ≤ β) :
    ENNReal.ofReal (Real.exp (-(β * M / 2))) ≤
      ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-β * N * modulatedEnergy k X μ))
        ∂(Measure.pi fun _ : Fin N => μ) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hY : Integrable (fun X : Config d N => -β * N * modulatedEnergy k X μ)
      (Measure.pi fun _ : Fin N => μ) := (integrable_modulatedEnergy_pair hk).const_mul _
  have hE := expectation_modulatedEnergy_pair (N := N) hk hN
  have hdbl : -M ≤ ∫ p : Torus d × Torus d, k p.1 p.2 ∂(μ.prod μ) := by
    have hint : Integrable (fun p : Torus d × Torus d => k p.1 p.2) (μ.prod μ) := hk.integrable_prod
    rw [integral_prod _ hint]
    have : ∫ x, -M ∂μ ≤ ∫ x, ∫ y, k x y ∂μ ∂μ :=
      integral_mono (integrable_const _) hk.integrable_rowInt fun x =>
        (abs_le.1 (hk.abs_rowInt_le hM x)).1
    simpa using this
  have hmean : -(β * M / 2) ≤ ∫ X : Config d N, -β * N * modulatedEnergy k X μ ∂(Measure.pi fun _ : Fin N => μ) := by
    rw [integral_const_mul, hE]
    have : -β * N * (-(1 / (2 * (N : ℝ))) * ∫ p : Torus d × Torus d, k p.1 p.2 ∂(μ.prod μ)) =
        β / 2 * ∫ p : Torus d × Torus d, k p.1 p.2 ∂(μ.prod μ) := by field_simp
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_left hdbl (show 0 ≤ β / 2 by positivity)]
  refine le_trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 hmean)) ?_
  exact ofReal_exp_integral_le_lintegral _ hY

end Lower

section Tilt

variable {N : ℕ}

/-- The Gibbs normaliser agrees with the `lintegral` partition function when the latter is finite. -/
theorem gibbs_facts {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {g : Torus d → ℝ}
    (hgR : RowOK μ (fun x y => g (x - y))) {β : ℝ}
    (hK0 : ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-β * N *
        modulatedEnergy (fun x y => g (x - y)) X μ)) ∂(Measure.pi fun _ : Fin N => μ) ≠ 0)
    (hKt : ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-β * N *
        modulatedEnergy (fun x y => g (x - y)) X μ)) ∂(Measure.pi fun _ : Fin N => μ) ≠ ∞) :
    ENNReal.ofReal (gibbsNormalizer g N β μ) = ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-β * N *
        modulatedEnergy (fun x y => g (x - y)) X μ)) ∂(Measure.pi fun _ : Fin N => μ) ∧
      IsProbabilityMeasure (modulatedGibbs g N β μ) := by
  have hint : Integrable (fun X : Config d N => Real.exp (-β * N *
      modulatedEnergyKernel g X μ)) (Measure.pi fun _ : Fin N => μ) := by
    refine (lintegral_ofReal_ne_top_iff_integrable ?_ ?_).1 hKt
    · exact (Real.measurable_exp.comp (measurable_const.mul (measurable_modulatedEnergy hgR))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun X => (Real.exp_pos _).le
  have hnorm : ENNReal.ofReal (gibbsNormalizer g N β μ) = ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-β * N *
        modulatedEnergy (fun x y => g (x - y)) X μ)) ∂(Measure.pi fun _ : Fin N => μ) := by
    unfold gibbsNormalizer
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun X => (Real.exp_pos _).le)]
    rfl
  refine ⟨hnorm, ?_⟩
  have hpos : 0 < gibbsNormalizer g N β μ := by
    by_contra hneg
    push Not at hneg
    have : ENNReal.ofReal (gibbsNormalizer g N β μ) = 0 := ENNReal.ofReal_eq_zero.2 hneg
    exact hK0 (hnorm ▸ this)
  exact modulatedGibbs_isProbabilityMeasure g β μ hpos hint

/-- `E_Q[e^{λ N F^h}] = K^{g - (λ/β) h} / K^g` (`N:eq:tilt-partition`), for `Q = Q_{N,β}(μ)`. -/
theorem lintegral_tilt {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {g : Torus d → ℝ}
    (hgR : RowOK μ (fun x y => g (x - y))) {h : Torus d → Torus d → ℝ} (hhR : RowOK μ h)
    {β : ℝ} (hβ : 0 < β)
    (hK0 : ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-β * N *
        modulatedEnergy (fun x y => g (x - y)) X μ)) ∂(Measure.pi fun _ : Fin N => μ) ≠ 0)
    (hKt : ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-β * N *
        modulatedEnergy (fun x y => g (x - y)) X μ)) ∂(Measure.pi fun _ : Fin N => μ) ≠ ∞)
    (lam : ℝ) :
    ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (lam * N * modulatedEnergy h X μ))
        ∂(modulatedGibbs g N β μ) =
      (∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-β * N *
        modulatedEnergy (fun x y => g (x - y)) X μ)) ∂(Measure.pi fun _ : Fin N => μ))⁻¹ *
      ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-β * N *
        modulatedEnergy (fun x y => g (x - y) - (lam / β) * h x y) X μ))
          ∂(Measure.pi fun _ : Fin N => μ) := by
  set K := ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-β * N *
        modulatedEnergy (fun x y => g (x - y)) X μ)) ∂(Measure.pi fun _ : Fin N => μ) with hK
  have hwm : Measurable (fun X : Config d N => ENNReal.ofReal (Real.exp (-β * N *
      modulatedEnergy (fun x y => g (x - y)) X μ))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul (measurable_modulatedEnergy hgR)))
  have hgm : Measurable (fun X : Config d N => ENNReal.ofReal (Real.exp (lam * N *
      modulatedEnergy h X μ))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul (measurable_modulatedEnergy hhR)))
  have hnorm : ENNReal.ofReal (gibbsNormalizer g N β μ) = K := by
    have hint : Integrable (fun X : Config d N => Real.exp (-β * N *
        modulatedEnergyKernel g X μ)) (Measure.pi fun _ : Fin N => μ) := by
      refine (lintegral_ofReal_ne_top_iff_integrable ?_ ?_).1 hKt
      · exact (Real.measurable_exp.comp (measurable_const.mul (measurable_modulatedEnergy hgR))).aestronglyMeasurable
      · exact Filter.Eventually.of_forall fun X => (Real.exp_pos _).le
    unfold gibbsNormalizer
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun X => (Real.exp_pos _).le)]
    rfl
  unfold modulatedGibbs
  rw [lintegral_smul_measure, hnorm, smul_eq_mul]
  congr 1
  refine (lintegral_withDensity_eq_lintegral_mul (Measure.pi fun _ : Fin N => μ) hwm hgm).trans ?_
  refine lintegral_congr fun X => ?_
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  have e := modulatedEnergy_sub hgR (hhR.smul (lam / β)) X
  rw [modulatedEnergy_smul (lam / β) hhR X] at e
  rw [e]
  have : β ≠ 0 := hβ.ne'
  field_simp
  ring

end Tilt

section Moments

variable {N : ℕ}

theorem exp_abs_le (x : ℝ) : Real.exp |x| ≤ Real.exp x + Real.exp (-x) := by
  rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
  · have := Real.exp_pos (-x); linarith
  · have := Real.exp_pos x; linarith

/-- The exponential-moment display `N:eq:pair-exp` and the entropy display `N:eq:pair-entropy`, from a
two-sided pressure bound for all `|θ| ≤ θ₀` (`N:eq:tilt-partition`, `e^{|x|} ≤ e^x + e^{-x}`, the
variational inequality). -/
theorem moments_of_pressure {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {g : Torus d → ℝ}
    {h : Torus d → Torus d → ℝ} (hgR : RowOK μ (fun x y => g (x - y))) (hhR : RowOK μ h)
    {δ C θ₀ βm β : ℝ} (hδ : 1 ≤ (N : ℝ) * δ) (hC : 0 ≤ C) (hθ₀ : 0 < θ₀) (hβm : 0 < βm)
    (hβ : βm ≤ β)
    (hP : ∀ θ : ℝ, |θ| ≤ θ₀ →
      ENNReal.ofReal (Real.exp (-(C * N * δ))) ≤
          ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-β * N *
            modulatedEnergy (fun x y => g (x - y) - θ * h x y) X μ)) ∂(Measure.pi fun _ : Fin N => μ) ∧
        ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-β * N *
            modulatedEnergy (fun x y => g (x - y) - θ * h x y) X μ)) ∂(Measure.pi fun _ : Fin N => μ) ≤
          ENNReal.ofReal (Real.exp (C * N * δ))) :
    ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp ((βm * θ₀) * N * |modulatedEnergy h X μ|))
        ∂(modulatedGibbs g N β μ) ≤ ENNReal.ofReal (Real.exp ((2 * C + 1) * N * δ)) ∧
      ∀ ν : Measure (Config d N), IsProbabilityMeasure ν →
        relEntropy ν (modulatedGibbs g N β μ) < ∞ →
        ∫⁻ X, ENNReal.ofReal (N * |modulatedEnergy h X μ|) ∂ν ≤
          ENNReal.ofReal ((βm * θ₀)⁻¹ * (2 * C + 1)) *
            (relEntropy ν (modulatedGibbs g N β μ) + ENNReal.ofReal (N * δ)) := by
  have hβ0 : 0 < β := lt_of_lt_of_le hβm hβ
  set θ₁ := βm * θ₀ with hθ₁
  have hθ₁0 : 0 < θ₁ := mul_pos hβm hθ₀
  have hK := hP 0 (by simp [hθ₀.le])
  simp only [zero_mul, sub_zero] at hK
  set K := ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-β * N *
        modulatedEnergy (fun x y => g (x - y)) X μ)) ∂(Measure.pi fun _ : Fin N => μ) with hKdef
  have hK0 : K ≠ 0 := by
    have : 0 < ENNReal.ofReal (Real.exp (-(C * N * δ))) := ENNReal.ofReal_pos.2 (Real.exp_pos _)
    exact (lt_of_lt_of_le this hK.1).ne'
  have hKt : K ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hK.2
  have hKinv : K⁻¹ ≤ ENNReal.ofReal (Real.exp (C * N * δ)) := by
    have h1 : K⁻¹ ≤ (ENNReal.ofReal (Real.exp (-(C * N * δ))))⁻¹ := ENNReal.inv_le_inv.2 hK.1
    refine h1.trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg, neg_neg]
  obtain ⟨-, hQprob⟩ := gibbs_facts hgR hK0 hKt
  have hdiv : ∀ lam : ℝ, |lam / β| ≤ θ₀ →
      ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (lam * N * modulatedEnergy h X μ))
        ∂(modulatedGibbs g N β μ) ≤
      ENNReal.ofReal (Real.exp (C * N * δ)) * ENNReal.ofReal (Real.exp (C * N * δ)) := by
    intro lam hlam
    rw [lintegral_tilt hgR hhR hβ0 hK0 hKt lam]
    exact mul_le_mul' hKinv (hP _ hlam).2
  have hθβ : θ₁ / β ≤ θ₀ := by
    rw [div_le_iff₀ hβ0]
    calc θ₁ = βm * θ₀ := rfl
      _ ≤ θ₀ * β := by nlinarith
  have hE : ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (θ₁ * N * |modulatedEnergy h X μ|))
      ∂(modulatedGibbs g N β μ) ≤ ENNReal.ofReal (Real.exp ((2 * C + 1) * N * δ)) := by
    have hFm : Measurable (fun X : Config d N => modulatedEnergy h X μ) := measurable_modulatedEnergy hhR
    have hpt : ∀ X : Config d N, ENNReal.ofReal (Real.exp (θ₁ * N * |modulatedEnergy h X μ|)) ≤
        ENNReal.ofReal (Real.exp (θ₁ * N * modulatedEnergy h X μ)) +
          ENNReal.ofReal (Real.exp ((-θ₁) * N * modulatedEnergy h X μ)) := by
      intro X
      rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
      refine ENNReal.ofReal_le_ofReal ?_
      have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      have : θ₁ * N * |modulatedEnergy h X μ| = |θ₁ * N * modulatedEnergy h X μ| := by
        rw [abs_mul, abs_mul, abs_of_pos hθ₁0, abs_of_nonneg hN0]
      rw [this]
      have h2 := exp_abs_le (θ₁ * N * modulatedEnergy h X μ)
      have h3 : (-θ₁) * N * modulatedEnergy h X μ = -(θ₁ * N * modulatedEnergy h X μ) := by ring
      rw [h3]; exact h2
    calc _ ≤ ∫⁻ X : Config d N, (ENNReal.ofReal (Real.exp (θ₁ * N * modulatedEnergy h X μ)) +
          ENNReal.ofReal (Real.exp ((-θ₁) * N * modulatedEnergy h X μ))) ∂(modulatedGibbs g N β μ) :=
          lintegral_mono hpt
      _ = ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (θ₁ * N * modulatedEnergy h X μ))
            ∂(modulatedGibbs g N β μ) +
          ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp ((-θ₁) * N * modulatedEnergy h X μ))
            ∂(modulatedGibbs g N β μ) :=
          lintegral_add_left (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
            (measurable_const.mul hFm))) _
      _ ≤ (ENNReal.ofReal (Real.exp (C * N * δ)) * ENNReal.ofReal (Real.exp (C * N * δ))) +
          (ENNReal.ofReal (Real.exp (C * N * δ)) * ENNReal.ofReal (Real.exp (C * N * δ))) := by
          refine add_le_add (hdiv θ₁ ?_) (hdiv (-θ₁) ?_)
          · rw [abs_of_pos (div_pos hθ₁0 hβ0)]; exact hθβ
          · rw [neg_div, abs_neg, abs_of_pos (div_pos hθ₁0 hβ0)]; exact hθβ
      _ = ENNReal.ofReal (Real.exp (C * N * δ) * Real.exp (C * N * δ) +
            Real.exp (C * N * δ) * Real.exp (C * N * δ)) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (Real.exp_pos _).le]
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          have h2 : (2 : ℝ) ≤ Real.exp ((N : ℝ) * δ) := by
            have h1 := Real.add_one_le_exp (1 : ℝ)
            have h3 : Real.exp 1 ≤ Real.exp ((N : ℝ) * δ) := Real.exp_le_exp.2 hδ
            linarith
          have h4 : Real.exp ((2 * C + 1) * N * δ) =
              Real.exp (C * N * δ) * Real.exp (C * N * δ) * Real.exp ((N : ℝ) * δ) := by
            rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
          rw [h4]
          have h5 : 0 < Real.exp (C * N * δ) * Real.exp (C * N * δ) := by positivity
          nlinarith
  refine ⟨hE, ?_⟩
  intro ν hν hKL
  haveI := hQprob
  have hFm : Measurable (fun X : Config d N => modulatedEnergy h X μ) := measurable_modulatedEnergy hhR
  have hdv := dv_lintegral (modulatedGibbs g N β μ) ν hKL.ne
    (F := fun X : Config d N => θ₁ * N * |modulatedEnergy h X μ|)
    (measurable_const.mul hFm.abs) (fun X => by positivity) (K := (2 * C + 1) * N * δ)
    (by
      have : 0 ≤ (N : ℝ) * δ := by linarith
      have h1 : (0 : ℝ) ≤ 2 * C + 1 := by linarith
      calc (0 : ℝ) ≤ (2 * C + 1) * ((N : ℝ) * δ) := mul_nonneg h1 this
        _ = (2 * C + 1) * N * δ := by ring) hE
  have hpt : ∀ X : Config d N, ENNReal.ofReal (N * |modulatedEnergy h X μ|) =
      ENNReal.ofReal θ₁⁻¹ * ENNReal.ofReal (θ₁ * N * |modulatedEnergy h X μ|) := by
    intro X
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 hθ₁0.le)]
    congr 1
    field_simp
  have h2C : (1 : ℝ) ≤ 2 * C + 1 := by linarith
  calc ∫⁻ X, ENNReal.ofReal (N * |modulatedEnergy h X μ|) ∂ν
      = ENNReal.ofReal θ₁⁻¹ * ∫⁻ X, ENNReal.ofReal (θ₁ * N * |modulatedEnergy h X μ|) ∂ν := by
        simp_rw [hpt]; exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal θ₁⁻¹ * (relEntropy ν (modulatedGibbs g N β μ) +
          ENNReal.ofReal ((2 * C + 1) * N * δ)) := mul_le_mul' le_rfl hdv
    _ ≤ ENNReal.ofReal θ₁⁻¹ * (ENNReal.ofReal (2 * C + 1) *
          (relEntropy ν (modulatedGibbs g N β μ) + ENNReal.ofReal (N * δ))) := by
        refine mul_le_mul' le_rfl ?_
        rw [mul_add]
        refine add_le_add ?_ ?_
        · exact le_mul_of_one_le_left (zero_le) (ENNReal.one_le_ofReal.2 h2C)
        · rw [← ENNReal.ofReal_mul (by linarith), mul_assoc]
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hθ₁0.le)]

end Moments

section Small

theorem one_le_mul_deltaN {s : ℝ} (hs0 : 0 ≤ s) (N : ℕ) (hN : 1 ≤ N) :
    1 ≤ (N : ℝ) * deltaN d s N := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  unfold deltaN
  split_ifs with h1 h2
  · rw [mul_inv_cancel₀ hNpos.ne']
  · rw [← mul_assoc, mul_inv_cancel₀ hNpos.ne', one_mul, Real.log_mul (Real.exp_pos _).ne' hNpos.ne',
      Real.log_exp]
    have := Real.log_nonneg hN1
    linarith
  · have hspos : 0 < s := by
      push Not at h1
      have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
      rcases lt_or_eq_of_le h1 with h | h
      · linarith
      · exact absurd h.symm h2
    have hs2 : (d : ℝ) / 2 < s := by
      push Not at h1
      exact lt_of_le_of_ne h1 (Ne.symm h2)
    have hds : (d : ℝ) / s ≤ 2 := by
      rw [div_le_iff₀ hspos]; linarith
    calc (1 : ℝ) ≤ (N : ℝ) ^ (2 - (d : ℝ) / s) := Real.one_le_rpow hN1 (by linarith)
      _ = (N : ℝ) * (N : ℝ) ^ (1 - (d : ℝ) / s) := by
          rw [show (2 - (d : ℝ) / s) = 1 + (1 - (d : ℝ) / s) by ring,
            Real.rpow_add hNpos, Real.rpow_one]

theorem exists_ne_zero_torus (hd : 1 ≤ d) : ∃ z : Torus d, z ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have h1 : (Set.univ : Set (Torus d)) ⊆ {0} := fun z _ => hcon z
  have h2 : (volume : Measure (Torus d)) Set.univ = 0 :=
    measure_mono_null h1 (volume_singleton_torus hd 0)
  have h3 : (volume : Measure (Torus d)) Set.univ = 1 := measure_univ
  rw [h2] at h3
  exact zero_ne_one h3

/-- The pair-kernel envelope with `w = g + c_*` replaced by `max B 0 · (g + c_*')`, `c_* ≤ c_*'`. -/
theorem dom_max (hd : 1 ≤ d) {g : Torus d → ℝ} {cstar cs : ℝ} (hcstar : cstar ≤ cs)
    (hw : ∀ z : Torus d, z ≠ 0 → 1 ≤ g z + cstar) {B : ℝ}
    {h : Torus d → Torus d → ℝ} (hdom : ∀ x y, |h x y| ≤ B * (g (x - y) + cstar)) :
    ∀ x y, |h x y| ≤ max B 0 * (g (x - y) + cs) := by
  have hB : 0 ≤ B := by
    obtain ⟨z, hz⟩ := exists_ne_zero_torus hd
    have h1 := hdom z 0
    rw [sub_zero] at h1
    have h2 := hw z hz
    by_contra hneg
    push Not at hneg
    have : B * (g z + cstar) < 0 := mul_neg_of_neg_of_pos hneg (by linarith)
    linarith [abs_nonneg (h z 0)]
  intro x y
  rw [max_eq_left hB]
  refine (hdom x y).trans (mul_le_mul_of_nonneg_left (by linarith) hB)

section QTheta

variable {q : Torus d → ℝ} {h : Torus d → Torus d → ℝ} {B' D θ : ℝ}

theorem qTheta_nonneg (hq0 : ∀ z, 0 ≤ q z) (henv : ∀ x y, |h x y| ≤ B' * q (x - y) + D)
    (hθB : |θ| * B' ≤ 1 / 2) (x y : Torus d) :
    0 ≤ q (x - y) - θ * h x y + |θ| * D := by
  have h1 := henv x y
  have h2 : |θ * h x y| ≤ |θ| * (B' * q (x - y) + D) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have h3 := le_abs_self (θ * h x y)
  have h4 := hq0 (x - y)
  have h5 : 0 ≤ q (x - y) * (1 - |θ| * B') := mul_nonneg h4 (by linarith)
  nlinarith [h5]

theorem qTheta_le {g : Torus d → ℝ} {cs E₀ : ℝ} (hB' : 0 ≤ B') (hD : 0 ≤ D) (hE₀ : 0 ≤ E₀)
    (hcs : ∀ z, 1 ≤ g z + cs) (hqenv : ∀ z, q z ≤ E₀ * (g z + cs))
    (hh : ∀ x y, |h x y| ≤ B' * (g (x - y) + cs)) (hθ1 : |θ| ≤ 1) (hθD : |θ| * D ≤ 1) (x y : Torus d) :
    q (x - y) - θ * h x y + |θ| * D ≤ (E₀ + B' + 1) * (g (x - y) + cs) := by
  have h1 := hh x y
  have h2 : |θ * h x y| ≤ B' * (g (x - y) + cs) := by
    rw [abs_mul]
    calc |θ| * |h x y| ≤ 1 * |h x y| := mul_le_mul_of_nonneg_right hθ1 (abs_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact h1
  have h3 := le_abs_self (-(θ * h x y))
  rw [abs_neg] at h3
  have h4 := hqenv (x - y)
  have h5 := hcs (x - y)
  nlinarith

end QTheta

end Small

section TwoSided

set_option maxHeartbeats 1600000 in
/-- The two-sided pressure bound `|log K^{g-θh}| ≤ C N δ_N` of Proposition 5.5, uniformly over the
family of backgrounds and kernels; the first display `N:eq:pressure-main`. -/
theorem pressure_two_sided (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (cstar : ℝ) (hw : ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d s z + cstar)
    (βm βp : ℝ) (hβm : 0 < βm) (c₀ : ℝ) (hc₀ : 0 < c₀) (Λ : ℕ → ℝ) (B : ℝ) :
    ∃ θ₀ C : ℝ, 0 < θ₀ ∧ 0 ≤ C ∧
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → Torus.IsSmooth ρ → (∀ x, c₀ ≤ ρ x) →
        (∀ k : ℕ, Torus.cbNorm k ρ ≤ Λ k) →
      ∀ h : Torus d → Torus d → ℝ, Measurable (Function.uncurry h) → (∀ x y, h x y = h y x) →
        (∀ x y, |h x y| ≤ B * (periodicRiesz d s (x - y) + cstar)) →
      ∀ N : ℕ, 2 ≤ N → ∀ β ∈ Set.Icc βm βp, ∀ θ : ℝ, |θ| ≤ θ₀ →
          ENNReal.ofReal (Real.exp (-(C * N * deltaN d s N))) ≤
              ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-β * N *
                modulatedEnergy (fun x y => periodicRiesz d s (x - y) - θ * h x y) X
                  (withDensityReal ρ))) ∂(Measure.pi fun _ => withDensityReal ρ) ∧
          ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-β * N *
                modulatedEnergy (fun x y => periodicRiesz d s (x - y) - θ * h x y) X
                  (withDensityReal ρ))) ∂(Measure.pi fun _ => withDensityReal ρ) ≤
            ENNReal.ofReal (Real.exp (C * N * deltaN d s N)) := by
  obtain ⟨g, hg⟩ : ∃ g : Torus d → ℝ, g = periodicRiesz d s := ⟨_, rfl⟩
  rw [← hg] at hw ⊢
  -- the shifted constant `cs ≥ c_*` with `w ≥ 1` everywhere
  obtain ⟨g0, hg0⟩ : ∃ g0 : ℝ, g0 = g 0 := ⟨_, rfl⟩
  obtain ⟨cs, hcsdef⟩ : ∃ cs : ℝ, cs = max cstar (1 - g0) := ⟨_, rfl⟩
  have hcs : ∀ z : Torus d, 1 ≤ g z + cs := by
    intro z
    by_cases hz : z = 0
    · subst hz
      have : 1 - g0 ≤ cs := by rw [hcsdef]; exact le_max_right _ _
      linarith
    · have := hw z hz; have : cstar ≤ cs := by rw [hcsdef]; exact le_max_left _ _
      linarith
  have hcstar : cstar ≤ cs := by rw [hcsdef]; exact le_max_left _ _
  obtain ⟨B', hB'def⟩ : ∃ B' : ℝ, B' = max B 0 := ⟨_, rfl⟩
  have hB' : 0 ≤ B' := by rw [hB'def]; exact le_max_right _ _
  have hgm : Measurable g := by rw [hg]; exact CoercAux.measurable_periodicRiesz_one hd hs0 hsd
  have hgi : Integrable g := by rw [hg]; exact CoercAux.integrable_periodicRiesz_one hd hs0 hsd
  have hwi : Integrable (fun z => g z + cs) := hgi.add (integrable_const cs)
  obtain ⟨Mw, hMw⟩ : ∃ Mw : ℝ, Mw = ∫ z, (g z + cs) := ⟨_, rfl⟩
  have hMw0 : 0 ≤ Mw := by
    rw [hMw]; exact integral_nonneg fun z => by show 0 ≤ g z + cs; linarith [hcs z]
  rw [hg] at hcs
  obtain ⟨E₀, hE₀, hspl⟩ := uniformSplit hd hs0 hsd cs hcs
  rw [← hg] at hcs hspl
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = E₀ + B' + 1 := ⟨_, rfl⟩
  obtain ⟨a₀, Cw, ha₀, hweak⟩ := weak_reference_pressure hd s hs0 hsd cs
    (fun z _ => by have := hcs z; rw [hg] at this; exact this) βm βp hβm c₀ hc₀ Λ A
  rw [← hg] at hweak
  obtain ⟨Λ0, hΛ0def⟩ : ∃ Λ0 : ℝ, Λ0 = max (Λ 0) 0 := ⟨_, rfl⟩
  have hΛ0 : 0 ≤ Λ0 := by rw [hΛ0def]; exact le_max_right _ _
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = min 1 (a₀ / (4 * (Λ0 + 1))) := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hεdef]; exact lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := by rw [hεdef]; exact min_le_left _ _
  have hεa : Λ0 * ε ≤ a₀ / 4 := by
    have h1 : ε ≤ a₀ / (4 * (Λ0 + 1)) := by rw [hεdef]; exact min_le_right _ _
    calc Λ0 * ε ≤ Λ0 * (a₀ / (4 * (Λ0 + 1))) := mul_le_mul_of_nonneg_left h1 hΛ0
      _ ≤ (Λ0 + 1) * (a₀ / (4 * (Λ0 + 1))) := by
          apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = a₀ / 4 := by field_simp
  obtain ⟨Λf, af, q, c, haf, hqm, hq0, hqev, hqint, hqε, hc0, hsplit, hqenv⟩ := hspl ε hε hε1
  obtain ⟨Sa, hSa⟩ : ∃ Sa : ℝ, Sa = ∑ k ∈ Λf, af k := ⟨_, rfl⟩
  have hSa0 : 0 ≤ Sa := by rw [hSa]; exact Finset.sum_nonneg haf
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = B' * (Sa + |g0| + |cs|) := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  obtain ⟨Kc, hKc⟩ : ∃ Kc : ℝ, Kc = B' * Mw + D := ⟨_, rfl⟩
  have hKc0 : 0 ≤ Kc := by rw [hKc]; positivity
  obtain ⟨θ₀, hθ₀def⟩ : ∃ θ₀ : ℝ, θ₀ = min 1 (min (1 / (2 * B' + 1))
      (min (1 / (D + 1)) (a₀ / (4 * (Λ0 + 1) * (Kc + 1))))) := ⟨_, rfl⟩
  have hθ₀pos : 0 < θ₀ := by
    rw [hθ₀def]; exact lt_min one_pos (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hθ1 : θ₀ ≤ 1 := by rw [hθ₀def]; exact min_le_left _ _
  have hθB : θ₀ * B' ≤ 1 / 2 := by
    have : θ₀ ≤ 1 / (2 * B' + 1) := by
      rw [hθ₀def]; exact (min_le_right _ _).trans (min_le_left _ _)
    calc θ₀ * B' ≤ (1 / (2 * B' + 1)) * B' := mul_le_mul_of_nonneg_right this hB'
      _ ≤ 1 / 2 := by
          rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
  have hθD : θ₀ * D ≤ 1 := by
    have : θ₀ ≤ 1 / (D + 1) := by
      rw [hθ₀def]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    calc θ₀ * D ≤ (1 / (D + 1)) * D := mul_le_mul_of_nonneg_right this hD0
      _ ≤ 1 := by
          rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
          linarith
  have hθK : Λ0 * (θ₀ * Kc) ≤ a₀ / 4 := by
    have : θ₀ ≤ a₀ / (4 * (Λ0 + 1) * (Kc + 1)) := by
      rw [hθ₀def]
      exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    calc Λ0 * (θ₀ * Kc) ≤ Λ0 * ((a₀ / (4 * (Λ0 + 1) * (Kc + 1))) * Kc) := by
          apply mul_le_mul_of_nonneg_left _ hΛ0
          exact mul_le_mul_of_nonneg_right this hKc0
      _ ≤ (Λ0 + 1) * ((a₀ / (4 * (Λ0 + 1) * (Kc + 1))) * (Kc + 1)) := by
          have h1 : 0 ≤ a₀ / (4 * (Λ0 + 1) * (Kc + 1)) := by positivity
          apply mul_le_mul (by linarith) _ (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left (by linarith) h1
      _ = a₀ / 4 := by field_simp
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = Λ0 * ∫ z, (|g z| + B' * (g z + cs)) := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    exact mul_nonneg hΛ0 (integral_nonneg fun z => by
      show 0 ≤ |g z| + B' * (g z + cs)
      have := hcs z
      have : 0 ≤ B' * (g z + cs) := mul_nonneg hB' (by linarith)
      positivity)
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = max (|βp| * Sa / 2 + |Cw|) (|βp| * M / 2) := ⟨_, rfl⟩
  have hC1 : |βp| * Sa / 2 + |Cw| ≤ C := by rw [hCdef]; exact le_max_left _ _
  have hC2 : |βp| * M / 2 ≤ C := by rw [hCdef]; exact le_max_right _ _
  have hC0 : 0 ≤ C := le_trans (by positivity) hC1
  refine ⟨θ₀, C, hθ₀pos, hC0, ?_⟩
  intro ρ hρ hsm hlow hcb h hhm hsym hdom N hN β hβ θ hθ
  have hN1 : 1 ≤ N := by omega
  have hβ0 : 0 ≤ β := (hβm.trans_le hβ.1).le
  haveI hμprob : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ
  have hρΛ : ∀ x, ρ x ≤ Λ0 := fun x =>
    ((WeakRef.le_cbNorm_zero hsm x).trans (hcb 0)).trans (hΛ0def ▸ le_max_left _ _)
  have hρm : Measurable ρ := hρ.measurable
  have hδ : 1 ≤ (N : ℝ) * deltaN d s N := one_le_mul_deltaN hs0 N hN1
  have hT : 0 ≤ (N : ℝ) * deltaN d s N := by linarith
  have hθ' : |θ| ≤ 1 := hθ.trans hθ1
  have hmeas2 : ∀ {f : Torus d → ℝ}, Measurable f → Measurable (Function.uncurry fun x y : Torus d => f (x - y)) :=
    fun hf => hf.comp (measurable_fst.sub measurable_snd)
  -- the envelope of `h` and its row bound
  have hhdom : ∀ x y, |h x y| ≤ B' * (g (x - y) + cs) := by
    rw [hB'def]; exact dom_max hd hcstar hw hdom
  have hwint : Integrable (fun z => B' * (g z + cs)) := hwi.const_mul B'
  have hhR : RowOK (withDensityReal ρ) h := (rowOK_of_dom hΛ0 hρΛ hwint hhm hhdom).1
  have hgR : RowOK (withDensityReal ρ) (fun x y => g (x - y)) :=
    (rowOK_of_dom hΛ0 hρΛ hgi.abs (hmeas2 hgm) (fun x y => le_rfl)).1
  have hqR : RowOK (withDensityReal ρ) (fun x y => q (x - y)) :=
    (rowOK_of_dom hΛ0 hρΛ hqint (hmeas2 hqm) (fun x y => by rw [abs_of_nonneg (hq0 _)])).1
  have hcosle : ∀ z : Torus d, |∑ k ∈ Λf, af k * Torus.cosMode k z| ≤ Sa := by
    intro z
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [hSa]
    refine Finset.sum_le_sum fun k hk => ?_
    rw [abs_mul, abs_of_nonneg (haf k hk)]
    exact mul_le_of_le_one_right (haf k hk) (abs_cosMode_le k z)
  have hcosm : Measurable (fun z : Torus d => ∑ k ∈ Λf, af k * Torus.cosMode k z) :=
    Finset.measurable_sum _ fun k _ => measurable_const.mul (Torus.continuous_cosMode k).measurable
  have hgLR : RowOK (withDensityReal ρ) (fun x y => ∑ k ∈ Λf, af k * Torus.cosMode k (x - y)) :=
    (rowOK_of_dom hΛ0 hρΛ (integrable_const Sa) (hmeas2 hcosm) (fun x y => hcosle _)).1
  have hsplit' : ∀ x : Torus d, x ≠ 0 → g x = ∑ k ∈ Λf, af k * Torus.cosMode k x + q x - c := hsplit
  have henv : ∀ x y, |h x y| ≤ B' * q (x - y) + D := by
    intro x y
    by_cases hxy : x = y
    · subst hxy
      have h1 := hhdom x x
      rw [sub_self] at h1
      have h2 : g 0 + cs ≤ |g0| + |cs| := by
        rw [← hg0]; exact add_le_add (le_abs_self _) (le_abs_self _)
      have h3 : B' * (g 0 + cs) ≤ B' * (|g0| + |cs|) := mul_le_mul_of_nonneg_left h2 hB'
      have h4 : 0 ≤ B' * q 0 := mul_nonneg hB' (hq0 _)
      have h5 : B' * (|g0| + |cs|) ≤ D := by
        rw [hD]; exact mul_le_mul_of_nonneg_left (by linarith [abs_nonneg g0, abs_nonneg cs]) hB'
      rw [sub_self]; linarith
    · have h1 := hhdom x y
      have h2 := hsplit' (x - y) (sub_ne_zero.2 hxy)
      have h3 := le_abs_self (∑ k ∈ Λf, af k * Torus.cosMode k (x - y))
      have h4 := hcosle (x - y)
      have h5 : g (x - y) + cs ≤ q (x - y) + (Sa + |cs|) := by
        have := le_abs_self cs
        have := (le_abs_self _ : (∑ k ∈ Λf, af k * Torus.cosMode k (x - y)) ≤ _)
        linarith
      have h6 : B' * (g (x - y) + cs) ≤ B' * (q (x - y) + (Sa + |cs|)) :=
        mul_le_mul_of_nonneg_left h5 hB'
      have h7 : B' * (Sa + |cs|) ≤ D := by
        rw [hD]; exact mul_le_mul_of_nonneg_left (by linarith [abs_nonneg g0]) hB'
      nlinarith
  -- the weak kernel `q_θ = q - θ h + |θ| D`
  have hθB' : |θ| * B' ≤ 1 / 2 := (mul_le_mul_of_nonneg_right hθ hB').trans hθB
  have hθD' : |θ| * D ≤ 1 := (mul_le_mul_of_nonneg_right hθ hD0).trans hθD
  obtain ⟨qθ, hqθdef⟩ : ∃ qθ : Torus d → Torus d → ℝ, qθ = fun x y => q (x - y) - θ * h x y + |θ| * D :=
    ⟨_, rfl⟩
  have hqθ0 : ∀ x y, 0 ≤ qθ x y := by
    intro x y; rw [hqθdef]; exact qTheta_nonneg hq0 henv hθB' x y
  have hqθsym : ∀ x y, qθ x y = qθ y x := by
    intro x y
    rw [hqθdef]
    simp only
    rw [hsym x y, ← hqev (x - y), neg_sub]
  have hqθm : Measurable (Function.uncurry qθ) := by
    rw [hqθdef]
    exact (((hmeas2 hqm).sub (measurable_const.mul hhm)).add measurable_const)
  have hqθA : ∀ x y, qθ x y ≤ A * (g (x - y) + cs) := by
    intro x y; rw [hqθdef, hA]
    exact qTheta_le hB' hD0 hE₀ hcs hqenv hhdom hθ' hθD' x y
  obtain ⟨Wθ, hWθdef⟩ : ∃ Wθ : Torus d → ℝ,
      Wθ = fun z => q z + |θ| * (B' * (g z + cs)) + |θ| * D := ⟨_, rfl⟩
  have h1w : Integrable (fun z => |θ| * (B' * (g z + cs))) := hwint.const_mul _
  have h2w : Integrable (fun z => q z + |θ| * (B' * (g z + cs))) := hqint.add h1w
  have hWθint : Integrable Wθ := by
    have h3 : Integrable (fun z => q z + |θ| * (B' * (g z + cs)) + |θ| * D) :=
      h2w.add (integrable_const (|θ| * D))
    rw [hWθdef]; exact h3
  have hdomθ : ∀ x y, |qθ x y| ≤ Wθ (x - y) := by
    intro x y
    rw [abs_of_nonneg (hqθ0 x y), hqθdef, hWθdef]
    simp only
    have h1 := hhdom x y
    have h2 : -(θ * h x y) ≤ |θ| * (B' * (g (x - y) + cs)) := by
      calc -(θ * h x y) ≤ |θ * h x y| := neg_le_abs _
        _ = |θ| * |h x y| := abs_mul _ _
        _ ≤ |θ| * (B' * (g (x - y) + cs)) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    linarith
  obtain ⟨hqθR, hrowbd⟩ := rowOK_of_dom hΛ0 hρΛ hWθint hqθm hdomθ
  have hintW : ∫ z, Wθ z = (∫ z, q z) + |θ| * Kc := by
    have e1 : ∫ z, (q z + |θ| * (B' * (g z + cs)) + |θ| * D) =
        (∫ z, (q z + |θ| * (B' * (g z + cs)))) + ∫ _z : Torus d, |θ| * D :=
      integral_add h2w (integrable_const _)
    have e2 : ∫ z, (q z + |θ| * (B' * (g z + cs))) =
        (∫ z, q z) + ∫ z, |θ| * (B' * (g z + cs)) := integral_add hqint h1w
    have e3 : ∫ z, |θ| * (B' * (g z + cs)) = |θ| * (B' * Mw) := by
      rw [integral_const_mul, integral_const_mul, hMw]
    have e4 : ∫ _z : Torus d, |θ| * D = |θ| * D := by simp
    rw [hWθdef, hKc]
    show ∫ z, (q z + |θ| * (B' * (g z + cs)) + |θ| * D) = _
    rw [e1, e2, e3, e4]; ring
  have hrowR : ∀ x, ∫ y, qθ x y ∂(withDensityReal ρ) ≤ a₀ / 2 := by
    intro x
    have h1 : ∫ y, qθ x y ∂(withDensityReal ρ) ≤ ∫ y, |qθ x y| ∂(withDensityReal ρ) :=
      integral_mono (hqθR.int x) (hqθR.int x).abs (fun y => le_abs_self _)
    have h2 := hrowbd x
    rw [hintW] at h2
    have h3 : Λ0 * ((∫ z, q z) + |θ| * Kc) ≤ a₀ / 4 + a₀ / 4 := by
      have h4 : Λ0 * (∫ z, q z) ≤ Λ0 * ε := mul_le_mul_of_nonneg_left hqε hΛ0
      have h5 : Λ0 * (|θ| * Kc) ≤ Λ0 * (θ₀ * Kc) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hθ hKc0) hΛ0
      nlinarith
    linarith
  have hrowL : ∀ x, ∫⁻ y, ENNReal.ofReal (qθ x y) ∂(withDensityReal ρ) ≤ ENNReal.ofReal (a₀ / 2) := by
    intro x
    rw [← ofReal_integral_eq_lintegral_ofReal (hqθR.int x) (Filter.Eventually.of_forall fun y => hqθ0 x y)]
    exact ENNReal.ofReal_le_ofReal (hrowR x)
  have hW := hweak ρ hρ hsm hlow hcb qθ hqθm hqθsym hqθ0 hqθA (a₀ / 2) (by positivity)
    (by linarith) hrowL N hN β hβ
  have hμ0 : ∀ x, withDensityReal ρ {x} = 0 := withDensityReal_singleton hd ρ
  have hβp : β ≤ |βp| := hβ.2.trans (le_abs_self _)
  refine ⟨?_, ?_⟩
  · -- lower bound (Jensen)
    have hkdom : ∀ x y, |g (x - y) - θ * h x y| ≤ (fun z => |g z| + B' * (g z + cs)) (x - y) := by
      intro x y
      simp only
      have h1 := hhdom x y
      calc |g (x - y) - θ * h x y| ≤ |g (x - y)| + |θ * h x y| := abs_sub _ _
        _ ≤ |g (x - y)| + B' * (g (x - y) + cs) := by
            refine add_le_add le_rfl ?_
            rw [abs_mul]
            calc |θ| * |h x y| ≤ 1 * |h x y| := mul_le_mul_of_nonneg_right hθ' (abs_nonneg _)
              _ ≤ _ := by rw [one_mul]; exact h1
    have hWint : Integrable (fun z => |g z| + B' * (g z + cs)) := hgi.abs.add hwint
    have hkm : Measurable (Function.uncurry fun x y : Torus d => g (x - y) - θ * h x y) := by
      show Measurable (fun p : Torus d × Torus d => g (p.1 - p.2) - θ * h p.1 p.2)
      exact (hgm.comp (measurable_fst.sub measurable_snd)).sub
        ((measurable_const (a := θ)).mul hhm)
    obtain ⟨hkR, hkbd⟩ := rowOK_of_dom hΛ0 hρΛ hWint hkm hkdom
    have hlow' := pressure_lower_core (N := N) hkR (M := M) (fun x => by rw [hMdef]; exact hkbd x) hN1 hβ0
    refine le_trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)) hlow'
    have h1 : β * M / 2 ≤ |βp| * M / 2 := by
      have := mul_le_mul_of_nonneg_right hβp hM0
      linarith
    have h2 : |βp| * M / 2 * 1 ≤ |βp| * M / 2 * ((N : ℝ) * deltaN d s N) :=
      mul_le_mul_of_nonneg_left hδ (by positivity)
    have h3 : C * 1 ≤ C * ((N : ℝ) * deltaN d s N) := mul_le_mul_of_nonneg_left hδ hC0
    have h4 : C * N * deltaN d s N = C * ((N : ℝ) * deltaN d s N) := by ring
    rw [h4]
    nlinarith
  · -- upper bound: discard the positive-definite part and use Lemma 5.7
    have hup := pressure_upper_core (N := N) hμ0 Λf af haf g q c hc0 hsplit' hgLR hqR hhR θ D hD0 hN1 hβ0
    rw [← hSa] at hup
    refine hup.trans ?_
    rw [← hqθdef]
    refine (mul_le_mul' le_rfl hW.2).trans ?_
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have h1 : β * Sa / 2 ≤ |βp| * Sa / 2 := by
      have := mul_le_mul_of_nonneg_right hβp hSa0
      linarith
    have h2 : (|βp| * Sa / 2 + |Cw|) * 1 ≤ (|βp| * Sa / 2 + |Cw|) * ((N : ℝ) * deltaN d s N) :=
      mul_le_mul_of_nonneg_left hδ (by positivity)
    have h3 : C * 1 ≤ C * ((N : ℝ) * deltaN d s N) := mul_le_mul_of_nonneg_left hδ hC0
    have h4 : C * N * deltaN d s N = C * ((N : ℝ) * deltaN d s N) := by ring
    have h5 : Cw * N * deltaN d s N ≤ |Cw| * ((N : ℝ) * deltaN d s N) := by
      have : Cw * N * deltaN d s N = Cw * ((N : ℝ) * deltaN d s N) := by ring
      rw [this]; exact mul_le_mul_of_nonneg_right (le_abs_self _) hT
    have h6 : β * Sa / 2 ≤ |βp| * Sa / 2 * ((N : ℝ) * deltaN d s N) := by
      have : |βp| * Sa / 2 * 1 ≤ |βp| * Sa / 2 * ((N : ℝ) * deltaN d s N) :=
        mul_le_mul_of_nonneg_left hδ (by positivity)
      linarith
    rw [h4]
    nlinarith

end TwoSided

section Final

/-- Row bounds for the kernels `g(x - y)` and `h` under a bounded density. -/
theorem rowOK_g_h (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (cstar : ℝ) (hw : ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d s z + cstar) (B : ℝ)
    {ρ : Torus d → ℝ} {Λ₀ : ℝ} (hΛ₀ : 0 ≤ Λ₀) (hρΛ : ∀ x, ρ x ≤ Λ₀)
    {h : Torus d → Torus d → ℝ} (hhm : Measurable (Function.uncurry h))
    (hdom : ∀ x y, |h x y| ≤ B * (periodicRiesz d s (x - y) + cstar)) :
    RowOK (withDensityReal ρ) (fun x y => periodicRiesz d s (x - y)) ∧ RowOK (withDensityReal ρ) h := by
  have hgm : Measurable (periodicRiesz d s) := CoercAux.measurable_periodicRiesz_one hd hs0 hsd
  have hgi : Integrable (periodicRiesz d s) := CoercAux.integrable_periodicRiesz_one hd hs0 hsd
  have hkm : Measurable (Function.uncurry fun x y : Torus d => periodicRiesz d s (x - y)) := by
    show Measurable (fun p : Torus d × Torus d => periodicRiesz d s (p.1 - p.2))
    exact hgm.comp (measurable_fst.sub measurable_snd)
  refine ⟨(rowOK_of_dom hΛ₀ hρΛ hgi.abs hkm (fun x y => le_rfl)).1, ?_⟩
  have hcs : cstar ≤ max cstar (1 - periodicRiesz d s 0) := le_max_left _ _
  have hdom' := dom_max hd hcs hw hdom
  have hwi : Integrable (fun z => periodicRiesz d s z + max cstar (1 - periodicRiesz d s 0)) :=
    hgi.add (integrable_const _)
  exact (rowOK_of_dom hΛ₀ hρΛ (hwi.const_mul (max B 0)) hhm hdom').1

/-- Proposition 5.5 `N:prop:pressure`, all three displays, uniformly over a bounded smooth positive
family of backgrounds and over a compact positive temperature interval. -/
theorem perturbed_pressure (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (cstar : ℝ) (hw : ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d s z + cstar)
    (βm βp : ℝ) (hβm : 0 < βm) (c₀ : ℝ) (hc₀ : 0 < c₀) (Λ : ℕ → ℝ) (B : ℝ) :
    ∃ θ₀ θ₁ C : ℝ, 0 < θ₀ ∧ 0 < θ₁ ∧
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → Torus.IsSmooth ρ → (∀ x, c₀ ≤ ρ x) →
        (∀ k : ℕ, Torus.cbNorm k ρ ≤ Λ k) →
      ∀ h : Torus d → Torus d → ℝ, Measurable (Function.uncurry h) → (∀ x y, h x y = h y x) →
        (∀ x y, |h x y| ≤ B * (periodicRiesz d s (x - y) + cstar)) →
      ∀ N : ℕ, 2 ≤ N → ∀ β ∈ Set.Icc βm βp,
        (∀ θ : ℝ, |θ| ≤ θ₀ →
          ENNReal.ofReal (Real.exp (-(C * N * deltaN d s N))) ≤
              ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-β * N *
                modulatedEnergy (fun x y => periodicRiesz d s (x - y) - θ * h x y) X
                  (withDensityReal ρ))) ∂(Measure.pi fun _ => withDensityReal ρ) ∧
          ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-β * N *
                modulatedEnergy (fun x y => periodicRiesz d s (x - y) - θ * h x y) X
                  (withDensityReal ρ))) ∂(Measure.pi fun _ => withDensityReal ρ) ≤
            ENNReal.ofReal (Real.exp (C * N * deltaN d s N))) ∧
        (∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (θ₁ * N *
              |modulatedEnergy h X (withDensityReal ρ)|))
            ∂(modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≤
          ENNReal.ofReal (Real.exp (C * N * deltaN d s N))) ∧
        ∀ ν : Measure (Config d N), IsProbabilityMeasure ν →
          relEntropy ν (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) < ∞ →
          ∫⁻ X, ENNReal.ofReal (N * |modulatedEnergy h X (withDensityReal ρ)|) ∂ν ≤
            ENNReal.ofReal C *
              (relEntropy ν (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) +
                ENNReal.ofReal (N * deltaN d s N)) := by
  obtain ⟨θ₀, C₁, hθ₀, hC₁, hP⟩ := pressure_two_sided hd s hs0 hsd cstar hw βm βp hβm c₀ hc₀ Λ B
  have hθ₁ : 0 < βm * θ₀ := mul_pos hβm hθ₀
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = max C₁ (max (2 * C₁ + 1) ((βm * θ₀)⁻¹ * (2 * C₁ + 1))) := ⟨_, rfl⟩
  have hCa : C₁ ≤ C := by rw [hCdef]; exact le_max_left _ _
  have hCb : 2 * C₁ + 1 ≤ C := by rw [hCdef]; exact (le_max_left _ _).trans (le_max_right _ _)
  have hCc : (βm * θ₀)⁻¹ * (2 * C₁ + 1) ≤ C := by
    rw [hCdef]; exact (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨θ₀, βm * θ₀, C, hθ₀, hθ₁, ?_⟩
  intro ρ hρ hsm hlow hcb h hhm hsym hdom N hN β hβ
  have hN1 : 1 ≤ N := by omega
  haveI hμprob : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ
  have hρΛ : ∀ x, ρ x ≤ max (Λ 0) 0 := fun x =>
    ((WeakRef.le_cbNorm_zero hsm x).trans (hcb 0)).trans (le_max_left _ _)
  obtain ⟨hgR, hhR⟩ := rowOK_g_h hd s hs0 hsd cstar hw B (le_max_right _ _) hρΛ hhm hdom
  have hδ : 1 ≤ (N : ℝ) * deltaN d s N := one_le_mul_deltaN hs0 N hN1
  have hT : 0 ≤ (N : ℝ) * deltaN d s N := by linarith
  have hP' := hP ρ hρ hsm hlow hcb h hhm hsym hdom N hN β hβ
  obtain ⟨hE, hD⟩ := moments_of_pressure (N := N) (μ := withDensityReal ρ) (g := periodicRiesz d s)
    (h := h) hgR hhR (δ := deltaN d s N) (C := C₁) (θ₀ := θ₀) (βm := βm) (β := β) hδ hC₁ hθ₀ hβm hβ.1 hP'
  have hmono : ∀ C' : ℝ, C' ≤ C → Real.exp (C' * N * deltaN d s N) ≤ Real.exp (C * N * deltaN d s N) := by
    intro C' hC'
    refine Real.exp_le_exp.2 ?_
    have : C' * N * deltaN d s N = C' * ((N : ℝ) * deltaN d s N) := by ring
    have h2 : C * N * deltaN d s N = C * ((N : ℝ) * deltaN d s N) := by ring
    rw [this, h2]; exact mul_le_mul_of_nonneg_right hC' hT
  refine ⟨fun θ hθ => ?_, ?_, ?_⟩
  · obtain ⟨hl, hu⟩ := hP' θ hθ
    refine ⟨le_trans (ENNReal.ofReal_le_ofReal ?_) hl, hu.trans (ENNReal.ofReal_le_ofReal (hmono C₁ hCa))⟩
    refine Real.exp_le_exp.2 ?_
    have h1 : C₁ * N * deltaN d s N = C₁ * ((N : ℝ) * deltaN d s N) := by ring
    have h2 : C * N * deltaN d s N = C * ((N : ℝ) * deltaN d s N) := by ring
    rw [h1, h2]
    have := mul_le_mul_of_nonneg_right hCa hT
    linarith
  · exact hE.trans (ENNReal.ofReal_le_ofReal (hmono _ hCb))
  · intro ν hν hKL
    refine (hD ν hν hKL).trans ?_
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal hCc) le_rfl

end Final

end HRS

end

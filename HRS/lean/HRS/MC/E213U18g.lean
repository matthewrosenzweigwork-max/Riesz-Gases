import HRS.MC.E213U18f

/-!
# Packet e213u18 (part g): the cross-covariance densities in terms of the canonical field, and the Wick pairing of
`B^v(f)` with two window variables
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213U18

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213U11
  HRS.MC.E213U10

variable {d : ℕ}

theorem u18_isSmooth_one : Torus.IsSmooth (fun _ : Torus d => (1 : ℝ)) := by
  unfold Torus.IsSmooth Torus.IsCk Torus.lift
  exact contDiff_const

theorem u18_eval_one {r : ℝ} (F : NegSobolev d r) : NegSobolev.eval F (fun _ => (1 : ℝ)) = 0 := by
  unfold NegSobolev.eval
  refine (tsum_congr fun k => ?_).trans tsum_zero
  have : Torus.funRealCoeff (fun _ : Torus d => (1 : ℝ)) k = 0 := by
    unfold Torus.funRealCoeff
    simpa using Torus.integral_realMode k
  rw [this, mul_zero]

section Cov

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

/-- The cross-covariance densities, expressed through the canonical field `η`. -/
structure U18Cov (H : ℝ) (t : Fin 3 → ℝ) (φ : Fin 3 → Torus d → ℝ) (χ : Fin 3 → ℝ → Torus d → ℝ) : Prop where
  hH : 0 < H
  ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) H
  hφ : ∀ i, Torus.IsSmooth (φ i)
  hχ : ∀ i r, Torus.IsSmooth (χ i r)
  cov : ∀ i, ∀ r ∈ Set.Icc (0 : ℝ) H, ∀ ψ : Torus d → ℝ, Torus.IsSmooth ψ →
    ∫ x, ψ x * χ i r x = ∫ ω, NegSobolev.eval (gd.η r ω) ψ * NegSobolev.eval (gd.η (t i) ω) (φ i) ∂gd.P₀

variable {gd}

theorem U18Cov.mean_zero {H : ℝ} {t : Fin 3 → ℝ} {φ : Fin 3 → Torus d → ℝ} {χ : Fin 3 → ℝ → Torus d → ℝ}
    (h : U18Cov gd H t φ χ) (i : Fin 3) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) H) : Torus.mean (χ i r) = 0 := by
  have := h.cov i r hr _ u18_isSmooth_one
  simp only [u18_eval_one, zero_mul, integral_zero, one_mul] at this
  exact this

theorem U18Cov.fc {H : ℝ} {t : Fin 3 → ℝ} {φ : Fin 3 → Torus d → ℝ} {χ : Fin 3 → ℝ → Torus d → ℝ}
    (h : U18Cov gd H t φ χ) (i : Fin 3) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) H) (k : NonzeroLattice d) :
    ∫ ω, NegSobolev.fourierCoeff (gd.η r ω) k * NegSobolev.eval (gd.η (t i) ω) (φ i) ∂gd.P₀ =
      Torus.funRealCoeff (χ i r) k := by
  have := h.cov i r hr _ (HRS.AdjK.adjkd_isSmooth_realMode k)
  simp only [HRS.AdjK.adjkd_eval_realMode] at this
  exact this.symm

/-- The hypotheses of `SatisfiesCubicFormula` give the covariance identities in terms of `η`. -/
theorem u18_cov_data (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) (t : Fin 3 → ℝ) (φ : Fin 3 → Torus d → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc a (a + T)) (hφ : ∀ i, Torus.IsSmooth (φ i))
    (ν : Measure (NegSobolev d m)) (hν : IsCenteredGaussianWithCov m ν (preparedCov d S.s β₀ S.μ0))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z₀ : Ω' → NegSobolev d m) (Z : ℝ → Ω' → NegSobolev d m) (hZ : IsPreparedLinear S m (a + T) ν P' Z₀ Z)
    (χ : Fin 3 → ℝ → Torus d → ℝ) (hχs : ∀ i r, Torus.IsSmooth (χ i r))
    (hχ : ∀ i, ∀ r ∈ Set.Icc (0 : ℝ) (a + T), ∀ ψ : Torus d → ℝ, Torus.IsSmooth ψ →
      ∫ x, ψ x * χ i r x = ∫ ω, NegSobolev.eval (Z r ω) ψ * NegSobolev.eval (Z (t i) ω) (φ i) ∂P') :
    U18Cov gd (a + T) t φ χ := by
  refine ⟨by linarith, fun i => ⟨ha.trans (ht i).1, (ht i).2⟩, hφ, hχs, fun i r hr ψ hψ => ?_⟩
  rw [hχ i r hr ψ hψ]
  exact u18_cov_transfer gd T hT a ha ν hν P' Z₀ Z hZ hr ⟨ha.trans (ht i).1, (ht i).2⟩ hψ (hφ i)

end Cov

section DPair

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

theorem u18_rho_bound (hE : EdgeworthHyp S β₀ m) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ v : ℝ, 0 ≤ v → withDensityReal (S.ρ v) ≤ ENNReal.ofReal Λ • (volume : Measure (Torus d)) := by
  obtain ⟨m₀, M₀, hm₀, hb⟩ := Regime.bounds (regime S β₀ hE)
  have hM0 : 0 ≤ M₀ := by
    have := hb 0 le_rfl (Classical.arbitrary _)
    linarith [this.1, this.2]
  refine ⟨M₀, hM0, fun v hv => ?_⟩
  unfold withDensityReal
  rw [← withDensity_const]
  exact withDensity_mono (Filter.Eventually.of_forall fun x =>
    ENNReal.ofReal_le_ofReal (hb v hv x).2)

theorem u18_s_lt (hE : EdgeworthHyp S β₀ m) : S.s + 1 < (d : ℝ) := by
  have h1 := hE.s_lt
  have h2 : (2 : ℝ) ≤ d := by exact_mod_cast S.hd
  linarith

theorem u18_isFinite_of_le {μ : Measure (Torus d)} {Λ : ℝ}
    (hμ : μ ≤ ENNReal.ofReal Λ • (volume : Measure (Torus d))) : IsFiniteMeasure μ :=
  ⟨lt_of_le_of_lt (hμ Set.univ) (by simp [Measure.smul_apply])⟩

variable {gd}

/-- The Wick pairing `E[B^v(f) ζ_j ζ_k] = ∬ h_{∇f} χ_j^v χ_k^v` at a fixed time `v`. -/
theorem u18_D_pair {H : ℝ} {t : Fin 3 → ℝ} {φ : Fin 3 → Torus d → ℝ} {χ : Fin 3 → ℝ → Torus d → ℝ}
    (h : U18Cov gd H t φ χ) (j k : Fin 3) {v : ℝ} (hv : v ∈ Set.Icc (0 : ℝ) H)
    (hW : IsWickQuadraticField S.s gd.P₀ (fun ω => gd.η v ω) (withDensityReal (S.ρ v)) (gd.B v))
    (hint : Integrable (fun ω => ‖gd.B v ω‖ *
      |NegSobolev.eval (gd.η (t j) ω) (φ j) * NegSobolev.eval (gd.η (t k) ω) (φ k)|) gd.P₀)
    {f : Torus d → ℝ} (hf : Torus.IsSmooth f) :
    ∫ ω, NegSobolev.eval (gd.B v ω) f *
        (NegSobolev.eval (gd.η (t j) ω) (φ j) * NegSobolev.eval (gd.η (t k) ω) (φ k)) ∂gd.P₀ =
      ∫ x, ∫ y, HRS.Main.hKernel d S.s (Torus.grad f) x y * χ j v x * χ k v y := by
  obtain ⟨Λ, hΛ0, hΛ⟩ := u18_rho_bound hE
  have hμ := hΛ v hv.1
  haveI : IsFiniteMeasure (withDensityReal (S.ρ v)) := u18_isFinite_of_le hμ
  exact u18_pair_formula S.hd S.hs0 (u18_s_lt hE) (HRS.MC.E213U13.gd_B_measurable_at gd v) hΛ0 hμ hW
    (u18_G4 gd H h.hH) (fun l => u18_fc_mem gd H h.hH hv l)
    (u18_eta_mem gd H h.hH (h.ht j) (h.hφ j)) (u18_eta_mem gd H h.hH (h.ht k) (h.hφ k))
    (h.hχ j v) (h.hχ k v) (h.mean_zero j hv) (h.mean_zero k hv) (h.fc j hv) (h.fc k hv) hf hint

end DPair

end HRS.MC.E213U18

end

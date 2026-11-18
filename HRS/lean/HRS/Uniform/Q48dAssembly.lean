import HRS.Uniform.Q48aGlue
import HRS.Uniform.Q48bDecay
import HRS.Uniform.Q48cCov
import HRS.Uniform.Evolution
import HRS.Uniform.Q48dCore

/-!
# Q48d: assembly of Lemma 3.31 `stationary_noise` from the evolution input

`stationary_noise_of_evo` is the full proof of `HRS.Uniform.stationary_noise` (statement verbatim) from one input,
`EvoInput`: the frozen dual evolution `Vev` is a plain strongly continuous evolution and satisfies the window maximal
estimate (Lemma 3.27 (3), with a.e.-strongly measurable convolutions, for probability spaces of every universe).  The
rest is: Q48a (adapted coupling on `[0,∞)` with exact `bures2` cost), Q48c (`E bures2 ≤ C (N⁻¹+δ²)`), Q48b (decay), and
the abstract core `Q48d.core` (global convolution, window bound uniform in `a`).
-/

noncomputable section

open HRS HRS.Uniform
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q48d

universe u

variable {d : ℕ}

/-- The evolution input of Lemma 3.31: for the stationary frozen coefficient `ρβ`, at every index `m ≥ m₁`, every dual
evolution `Vev` on `E_m` is a plain evolution on every `[0,T]`, and for every `T > 0` the window estimate holds with a
constant independent of `Vev` (and of the probability space). -/
def EvoInput (d : ℕ) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β) (V ρβ : Torus d → ℝ) : Prop :=
  ∃ m₁ : ℝ, ∀ m : ℝ, m₁ ≤ m →
    (∀ T : ℝ, 0 < T → ∃ C : ℝ, 0 ≤ C ∧ ∀ Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m,
      IsDualEvolution (PDE.mfData d s hs0 hsd V β hβ) (fun _ => ρβ) m Vev → WinMaxU.{u} Vev T C) ∧
    (∀ Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m,
      IsDualEvolution (PDE.mfData d s hs0 hsd V β hβ) (fun _ => ρβ) m Vev →
      ∀ T : ℝ, 0 ≤ T → IsPlainEvolution Vev T)

lemma isProb_withDensityReal {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) :
    IsProbabilityMeasure (withDensityReal ρ) := by
  have hint : Integrable ρ :=
    Integrable.of_integral_ne_zero (by rw [hρ.integral_one]; exact one_ne_zero)
  refine ⟨?_⟩
  unfold withDensityReal
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hρ.nonneg),
    hρ.integral_one]
  simp

lemma detCov_const {m : ℝ} (hm : (d : ℝ) / 2 + 2 < m) {q : ℝ} (hq : 0 ≤ q) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] (T : ℝ) :
    IsDetCovDensity T (fun _ : ℝ => covForm m q μ) := by
  refine ⟨fun x y => measurable_const, fun σ _ => (Q14.q14_covForm_trace hm hq μ).1, ?_⟩
  exact integrableOn_const (by simp) (by simp)

theorem stationary_noise_of_evo (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hVs : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hth : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρs : Torus.IsSmooth ρβ) (hpos : ∀ x, 0 < ρβ x)
    (hEvo : EvoInput.{u} d s hs0 hsd β hβ V ρβ) :
    ∃ m₀ : ℝ, ∀ m : ℝ, m₀ ≤ m → ∀ Cv : ℝ, ∀ T : ℝ, 0 < T → ∃ C : ℝ, 0 ≤ C ∧
      ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℝ mΩ) (𝒢 : InitialSigma ℱ) (N : ℕ) (_ : 1 ≤ N) (δ : ℝ) (_ : 0 ≤ δ)
        (X : ℝ → Ω → Config d N) (Q : Measure (Config d N)) [IsProbabilityMeasure Q] (_ : ∀ t : ℝ, 0 ≤ t → P.map (X t) = Q)
        (_ : ∀ f : Torus d → ℝ, Measurable f → MemLp f 2 (withDensityReal ρβ) →
          evariance (fun x : Config d N => pair (empirical x) f) Q ≤
            ENNReal.ofReal (Cv * (N : ℝ)⁻¹ * ∫ x, f x ^ 2 ∂(withDensityReal ρβ)))
        (g : Torus d → ℝ) (_ : Measurable g)
        (_ : (N : ℝ≥0∞)⁻¹ • ∑ i, Q.map (fun x : Config d N => x i) =
          (withDensityReal ρβ).withDensity fun x => ENNReal.ofReal (g x))
        (_ : ∫⁻ x, ‖g x - 1‖ₑ ^ 2 ∂(withDensityReal ρβ) ≤ ENNReal.ofReal ((Cv * δ) ^ 2))
        (Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m)
        (_ : IsDualEvolution (PDE.mfData d s hs0 hsd V β hβ) (fun _ => ρβ) m Vev)
        (M : ℝ → Ω → NegSobolev d m)
        (_ : ∀ S : ℝ, 0 ≤ S →
          IsHilbertMartingaleWithCovariation P ℱ S M
            (fun r ω => covForm m β⁻¹ (empirical (X r ω)))),
        ∃ (Ω' : Type u) (mΩ' : MeasurableSpace Ω') (P' : ProbabilityMeasure Ω') (π : Ω' → Ω)
          (ℱ' : Filtration ℝ mΩ') (Gb : ℝ → Ω' → NegSobolev d m)
          (Sd : ℝ → Ω' → (NegSobolev d m →L[ℝ] NegSobolev d m →L[ℝ] ℝ))
          (Z : ℝ → Ω' → NegSobolev d m),
          IsAdaptedGaussianCoupling P ℱ ⊤ 𝒢 M (fun r ω => covForm m β⁻¹ (empirical (X r ω)))
            (fun r => covForm m β⁻¹ (withDensityReal ρβ)) (fun _ _ => True) (fun _ _ => 0)
            P' π ℱ' Gb Sd ∧
          (∀ t : ℝ, 0 ≤ t → IsStochConv (P' : Measure Ω') Vev (ContinuousLinearMap.id ℝ (NegSobolev d m))
            (fun τ ω' => M τ (π ω') - Gb τ ω') 0 t (Z t)) ∧
          (∀ᵐ ω' ∂(P' : Measure Ω'), ContinuousOn (fun t => Z t ω') (Set.Ici 0)) ∧
          ∀ a : ℝ, 0 ≤ a →
            (∫⁻ ω', (⨆ t ∈ Set.Icc a (a + T), ‖Z t ω'‖ₑ) ^ 2 ∂(P' : Measure Ω')) ^ (1 / 2 : ℝ) ≤
              ENNReal.ofReal (C * ((N : ℝ) ^ (-(1 : ℝ) / 2) + δ))
    := by
  obtain ⟨m₁, hm₁⟩ := hEvo
  obtain ⟨mb, hmb⟩ := Q48b.stationary_decay hd s hs0 hsd β hβ V hVs ρβ hth hρs hpos
  obtain ⟨mc, hmc⟩ := Q48c.bures2_cov_estimate β hβ ρβ hρs hpos
  refine ⟨max (max m₁ mb) (max mc ((d : ℝ) + 3)), fun m hm Cv T hT => ?_⟩
  have hm1 : m₁ ≤ m := (le_max_left _ _).trans ((le_max_left _ _).trans hm)
  have hmb' : mb ≤ m := (le_max_right _ _).trans ((le_max_left _ _).trans hm)
  have hmc' : mc ≤ m := (le_max_left _ _).trans ((le_max_right _ _).trans hm)
  have hm3 : (d : ℝ) + 3 ≤ m := (le_max_right _ _).trans ((le_max_right _ _).trans hm)
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hm2 : (d : ℝ) / 2 + 2 < m := by linarith
  obtain ⟨C₀, c, hC₀, hc, hdec⟩ := hmb m hmb'
  obtain ⟨Cc, hCc0, hCc⟩ := hmc m hmc' Cv
  obtain ⟨hwin, hplain⟩ := hm₁ m hm1
  obtain ⟨C₁, hC1, h1⟩ := hwin 1 one_pos
  obtain ⟨CT, hCT0, hWT⟩ := hwin T hT
  refine ⟨coreConst C₀ c C₁ CT T * Real.sqrt Cc,
    mul_nonneg (coreConst_nonneg hC₀.le hc) (Real.sqrt_nonneg _), ?_⟩
  intro Ω mΩ P _ ℱ 𝒢 N hN δ hδ X Q _ hXQ hvar g hg hmarg hgδ Vev hdual M hM
  haveI : IsProbabilityMeasure (withDensityReal ρβ) := isProb_withDensityReal hth.1
  have hq : (0 : ℝ) ≤ β⁻¹ := (inv_pos.2 hβ).le
  have hDb : ∀ T' : ℝ, 0 ≤ T' → IsDetCovDensity T' (fun _ : ℝ => covForm m β⁻¹ (withDensityReal ρβ)) :=
    fun T' _ => detCov_const hm2 hq _ T'
  obtain ⟨Ω', mΩ', P', π, ℱ', Gb, Sd, hc'⟩ := Q48a.relative_covariance_coupling_top P ℱ 𝒢 M
    (fun r ω => covForm m β⁻¹ (empirical (X r ω))) hM
    (fun _ => covForm m β⁻¹ (withDensityReal ρβ)) hDb
  -- the cost bound
  have hK : ∀ r : ℝ, 0 ≤ r → ∫⁻ ω', ENNReal.ofReal (traceNormForm (Sd r ω')) ∂(P' : Measure Ω') ≤
      ENNReal.ofReal (Cc * ((N : ℝ)⁻¹ + δ ^ 2)) := by
    intro r hr
    have hXr : AEMeasurable (X r) P :=
      Q48c.aemeasurable_of_marginal P hN (X r) Q (hXQ r hr) ρβ g hmarg
    have hmapπ : (P' : Measure Ω').map π = P := hc'.preserving.map_eq
    have hmapX : (P' : Measure Ω').map (X r ∘ π) = Q := by
      rw [← AEMeasurable.map_map_of_aemeasurable (by rwa [hmapπ]) hc'.preserving.measurable.aemeasurable,
        hmapπ, hXQ r hr]
    have hb := hCc (P' : Measure Ω') N hN δ (X r ∘ π) Q hmapX hvar g hg hmarg hgδ
    refine le_trans (le_of_eq ?_) hb
    refine lintegral_congr_ae ?_
    filter_upwards [hc'.cost] with ω' hω'
    rw [hω' r hr le_top]
    rfl
  have hDiff : ∀ S : ℝ, 0 ≤ S → IsHilbertMartingaleWithCovariation (P' : Measure Ω') ℱ' S
      (fun τ ω' => (fun τ ω' => M τ (π ω') - Gb τ ω') (min τ S) ω')
      (fun r ω' => if r ≤ S then Sd r ω' else 0) :=
    fun S hS => hc'.difference S hS le_top
  have hW : ∀ T' : ℝ, 0 < T' → ∃ C : ℝ, 0 ≤ C ∧ WinMaxU.{u} Vev T' C := fun T' hT' => by
    obtain ⟨C, hC0, hC⟩ := hwin T' hT'
    exact ⟨C, hC0, hC Vev hdual⟩
  obtain ⟨Z, hZ1, hZ3, hZb⟩ := core (hplain Vev hdual) hC₀.le hc (fun u t hu hut => hdec Vev hdual u t hu hut)
    hW hT hC1 hCT0 (h1 Vev hdual) (hWT Vev hdual) (P' : Measure Ω') ℱ'
    (fun τ ω' => M τ (π ω') - Gb τ ω') Sd hDiff (Cc * ((N : ℝ)⁻¹ + δ ^ 2))
    (mul_nonneg hCc0 (by positivity)) hK
  refine ⟨Ω', mΩ', P', π, ℱ', Gb, Sd, Z,
    ⟨hc'.preserving, hc'.filtration, hc'.martingale, hc'.gaussian, hc'.difference, hc'.indep,
      Eventually.of_forall fun _ _ _ _ => trivial⟩, hZ1, hZ3, fun a ha => ?_⟩
  refine (hZb a ha).trans (ENNReal.ofReal_le_ofReal ?_)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsq : ((N : ℝ) ^ (-(1 : ℝ) / 2)) ^ 2 = (N : ℝ)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
    norm_num [Real.rpow_neg_one]
  have hr0 : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hNpos.le _
  have hsqrt : Real.sqrt ((N : ℝ)⁻¹ + δ ^ 2) ≤ (N : ℝ) ^ (-(1 : ℝ) / 2) + δ := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [mul_nonneg hr0 hδ]
  have hcf := coreConst_nonneg (C₁ := C₁) (CT := CT) (T := T) hC₀.le hc
  calc coreConst C₀ c C₁ CT T * Real.sqrt (Cc * ((N : ℝ)⁻¹ + δ ^ 2))
      = coreConst C₀ c C₁ CT T * Real.sqrt Cc * Real.sqrt ((N : ℝ)⁻¹ + δ ^ 2) := by
        rw [Real.sqrt_mul hCc0]; ring
    _ ≤ coreConst C₀ c C₁ CT T * Real.sqrt Cc * ((N : ℝ) ^ (-(1 : ℝ) / 2) + δ) :=
        mul_le_mul_of_nonneg_left hsqrt (mul_nonneg hcf (Real.sqrt_nonneg _))

end HRS.Uniform.Q48d

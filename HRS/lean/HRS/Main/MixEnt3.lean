import HRS.Main.MixEnt2
import HRS.Main.T25Aux5

/-!
# MIXENT 3: entropy of the mixture preparation against the moving reference `Q_N^0` (lemma M4)

TeX L6952-6962 ("for the product mixture the entropy computation gives `B_N ≤ C N δ_N`").

With `π = (μ°)^{⊗N}` and `Q = Q_N^0 = π.tilted(-β N F_N)` (`t25_ref0`, `t25_tilted`) one has the exact
identity (`MeasureTheory.integral_llr_tilted_right`)
`H(mix | Q) = H(mix | π) + β E_mix[N F_N] + log K_{N,β}`;
`H(mix | π) ≤ a₀² ‖b‖²_{L²(μ°)}` is M2, and `log K_{N,β} ≤ C N δ_N` is the pressure bound `t25_press`.
The energy term `E_mix[N F_N]` is an input here (lemma M3, `MixEnt4`).
-/

open MeasureTheory Filter Topology ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Main

variable {d : ℕ}

/-- Entropy against a tilted reference (abstract form): for probability measures `μ ≪ ν`,
`klDiv μ (ν.tilted f) = ofReal (∫ llr μ ν dμ - ∫ f dμ + log ∫ e^f dν)`. -/
theorem mx_klDiv_tilted_right {α : Type*} [MeasurableSpace α] (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (f : α → ℝ) (hμν : μ ≪ ν)
    (hint : Integrable (llr μ ν) μ) (hfμ : Integrable f μ)
    (hfν : Integrable (fun x => Real.exp (f x)) ν) :
    klDiv μ (ν.tilted f) =
      ENNReal.ofReal (∫ x, llr μ ν x ∂μ - ∫ x, f x ∂μ + Real.log (∫ x, Real.exp (f x) ∂ν)) := by
  haveI : IsProbabilityMeasure (ν.tilted f) := isProbabilityMeasure_tilted hfν
  have hac : μ ≪ ν.tilted f := hμν.trans (absolutelyContinuous_tilted hfν)
  have hint' : Integrable (llr μ (ν.tilted f)) μ := integrable_llr_tilted_right hμν hfμ hint hfν
  rw [klDiv_of_ac_of_integrable hac hint', integral_llr_tilted_right hμν hfμ hfν hint]
  simp

/-- The energy `W_N = N F_N(·; μ°)` for the Riesz kernel of the setting `S`. -/
def mxW (S : PreparedData d) (N : ℕ) (X : Config d N) : ℝ :=
  (N : ℝ) * modulatedEnergyKernel (periodicRiesz d S.s) X S.μ0

/-- **M4** (entropy of the mixture against `Q_N^0`; TeX L6952-6962).  There is `C ≥ 0`
(depending only on `S`) such that for every bounded measurable `b` with `μ°(b) = 0`, `a₀`, `N ≥ 2`
with `|a₀ b| ≤ √N/2`, every `E`, and mixture `mix = mixturePrep μ° b a₀ N` with `N F_N ∈ L¹(mix)`
and `E_mix[N F_N] ≤ E`:
`H(mix | Q_N^0) ≤ a₀² ‖b‖²_{L²(μ°)} + β E + C N δ_N`. -/
theorem mx_relEntropy_ref_le (S : PreparedData d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : Torus d → ℝ), Measurable b → ∀ M : ℝ, (∀ x, |b x| ≤ M) →
      pair S.μ0 b = 0 → ∀ (a₀ : ℝ) (N : ℕ), 2 ≤ N → (∀ x, |a₀ * b x| ≤ Real.sqrt N / 2) →
      ∀ E : ℝ, Integrable (mxW S N) (mixturePrep S.μ0 b a₀ N) →
        ∫ X, mxW S N X ∂(mixturePrep S.μ0 b a₀ N) ≤ E →
      relEntropy (mixturePrep S.μ0 b a₀ N) (S.refMeasure N 0) ≤
        ENNReal.ofReal (a₀ ^ 2 * ∫ x, b x ^ 2 ∂S.μ0 + S.β * E + C * N * deltaN d S.s N) := by
  obtain ⟨C, hC0, hCp⟩ := HRS.T25.t25_press S S.β S.β S.hβ
  refine ⟨C, hC0, fun b hb M hbM hb0 a₀ N hN hB E hWi hWE => ?_⟩
  have hN1 : 1 ≤ N := by omega
  haveI := isProb_withDensityReal S.hρ0.density
  haveI hprob : IsProbabilityMeasure S.μ0 := by unfold PreparedData.μ0; infer_instance
  set π : Measure (Config d N) := Measure.pi fun _ : Fin N => S.μ0 with hπ
  have hb0' : ∫ x, b x ∂S.μ0 = 0 := hb0
  have hbi : Integrable b S.μ0 :=
    Integrable.of_bound hb.aestronglyMeasurable M (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact hbM x)
  haveI hmixp := mx_isProb_mixturePrep S.μ0 b hb hbi hb0' a₀ N hN1 hB
  set mix := mixturePrep S.μ0 b a₀ N with hmix
  -- entropy against `π` (M2)
  have hM2 := mx_relEntropy_mixturePrep_le S.μ0 b hb M hbM hb0' a₀ N hN1 hB
  unfold relEntropy at hM2
  have hne : klDiv mix π ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hM2
  obtain ⟨hac, hllr⟩ := klDiv_ne_top_iff.1 hne
  have hHπ : ∫ x, llr mix π x ∂mix ≤ a₀ ^ 2 * ∫ x, b x ^ 2 ∂S.μ0 := by
    have h1 := toReal_klDiv_of_measure_eq hac (by simp : mix Set.univ = π Set.univ)
    rw [← h1]
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hM2
    refine this.trans ?_
    rw [ENNReal.toReal_ofReal]
    exact mul_nonneg (sq_nonneg _) (integral_nonneg fun x => sq_nonneg _)
  -- the tilted form of the reference
  set Fm : Config d N → ℝ := fun X => modulatedEnergyKernel (periodicRiesz d S.s) X S.μ0 with hFm
  have hF : Measurable Fm := measurable_modulatedEnergy (HRS.T25.t25_rowOK S)
  set f : Config d N → ℝ := fun X => -S.β * N * Fm X with hf
  have hfm : Measurable f := measurable_const.mul hF
  have hQ : S.refMeasure N 0 = π.tilted f :=
    (HRS.T25.t25_ref0 S N).trans (HRS.T25.t25_tilted S N hN S.hβ.le)
  -- pressure bounds
  have hp := hCp N hN S.β ⟨le_rfl, le_rfl⟩
  have hK := HRS.T25.t25_K_of_E π hfm (A := C * N * deltaN d S.s N)
    (by simpa [modNormalizerE, modulatedEnergyKernel, hf, hFm, hπ] using hp.1)
    (by simpa [modNormalizerE, modulatedEnergyKernel, hf, hFm, hπ] using hp.2)
  obtain ⟨hKi, hKl, hKu⟩ := hK
  have hlogK : Real.log (∫ x, Real.exp (f x) ∂π) ≤ C * N * deltaN d S.s N := by
    have hpos : 0 < ∫ x, Real.exp (f x) ∂π := lt_of_lt_of_le (Real.exp_pos _) hKl
    calc Real.log (∫ x, Real.exp (f x) ∂π) ≤ Real.log (Real.exp (C * N * deltaN d S.s N)) :=
          Real.log_le_log hpos hKu
      _ = _ := Real.log_exp _
  -- the energy under the mixture
  have hfi : Integrable f mix := by
    have := hWi.const_mul (-S.β)
    refine this.congr (ae_of_all _ fun X => ?_)
    simp only [hf, mxW, hFm]; ring
  have hfE : -∫ X, f X ∂mix ≤ S.β * E := by
    have : ∫ X, f X ∂mix = -S.β * ∫ X, mxW S N X ∂mix := by
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun X => ?_)
      simp only [hf, mxW, hFm]; ring
    rw [this]
    nlinarith [S.hβ, hWE]
  unfold relEntropy
  rw [hQ, mx_klDiv_tilted_right mix π f hac hllr hfi hKi]
  refine ENNReal.ofReal_le_ofReal ?_
  linarith

/-- **M4, entropy scale** `B_N ≤ C N δ_N` for the mixture preparation (TeX L6952-6962, "gives
`B_N ≤ C N δ_N`"), together with finiteness of `H(mix | Q_N^0)`.  Same hypotheses as
`mx_relEntropy_ref_le`; the constant is explicit in terms of `a₀² ‖b‖²_{L²(μ°)}`, `β |E|` and the
pressure constant `C`. -/
theorem mx_B_le (S : PreparedData d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : Torus d → ℝ), Measurable b → ∀ M : ℝ, (∀ x, |b x| ≤ M) →
      pair S.μ0 b = 0 → ∀ (a₀ : ℝ) (N : ℕ), 2 ≤ N → (∀ x, |a₀ * b x| ≤ Real.sqrt N / 2) →
      ∀ E : ℝ, Integrable (mxW S N) (mixturePrep S.μ0 b a₀ N) →
        ∫ X, mxW S N X ∂(mixturePrep S.μ0 b a₀ N) ≤ E →
      relEntropy (mixturePrep S.μ0 b a₀ N) (S.refMeasure N 0) < ⊤ ∧
      S.B N (mixturePrep S.μ0 b a₀ N) ≤
        (2 + a₀ ^ 2 * ∫ x, b x ^ 2 ∂S.μ0 + S.β * |E| + C) * ((N : ℝ) * deltaN d S.s N) := by
  obtain ⟨C, hC0, hC⟩ := mx_relEntropy_ref_le S
  refine ⟨C, hC0, fun b hb M hbM hb0 a₀ N hN hB E hWi hWE => ?_⟩
  have h := hC b hb M hbM hb0 a₀ N hN hB E hWi hWE
  refine ⟨lt_of_le_of_lt h ENNReal.ofReal_lt_top, ?_⟩
  have hδ : 1 ≤ (N : ℝ) * deltaN d S.s N := one_le_mul_deltaN S.hs0 N (by omega)
  have hb2 : 0 ≤ a₀ ^ 2 * ∫ x, b x ^ 2 ∂S.μ0 :=
    mul_nonneg (sq_nonneg _) (integral_nonneg fun x => sq_nonneg _)
  have hT := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  have hT2 : (relEntropy (mixturePrep S.μ0 b a₀ N) (S.refMeasure N 0)).toReal ≤
      a₀ ^ 2 * ∫ x, b x ^ 2 ∂S.μ0 + S.β * |E| + C * ((N : ℝ) * deltaN d S.s N) := by
    refine hT.trans ?_
    rw [ENNReal.toReal_ofReal']
    refine max_le ?_ ?_
    · nlinarith [S.hβ, le_abs_self E, mul_nonneg S.hβ.le (abs_nonneg E)]
    · have := mul_nonneg hC0 (by linarith : (0 : ℝ) ≤ (N : ℝ) * deltaN d S.s N)
      have := mul_nonneg S.hβ.le (abs_nonneg E)
      linarith
  unfold PreparedData.B
  have hy : 0 ≤ S.β * |E| := mul_nonneg S.hβ.le (abs_nonneg E)
  have := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + a₀ ^ 2 * ∫ x, b x ^ 2 ∂S.μ0 + S.β * |E|)
    (by linarith : (0 : ℝ) ≤ (N : ℝ) * deltaN d S.s N - 1)
  nlinarith

end Main

end HRS

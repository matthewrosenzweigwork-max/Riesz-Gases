import HRS.MS.R2WinErrAux12

/-!
# S10.4 packet E3a': the expected commutator functional along the particle process, and Lipschitz constants of orbit gradients

* `s104_forcing_expect`: `E_P |Comm_N(v; Z, ρ)| ≤ C Λ δ_N` for a random configuration `Z` whose law has relative entropy `≤ H₀ N δ_N`
  with respect to `Q_{N,β}(ρ dx)` and a `Λ`-Lipschitz field `v` (pushforward form of `s104_comm_expect`).
* `s104_vec_bound`, `s104_grad_lip`: `R2OrbitGrad` gives the Lipschitz constant `A e^{-c(t-r)}` of the vector field `∇U(r,t)ψ`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Function Set
open scoped ENNReal NNReal

namespace HRS.MS.R2WinErr

open HRS.Whole HRS.MS.Wr HRS.MS.PrepStat

variable {d : ℕ}

theorem s104_forcing_expect (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (M L β : ℝ) (hβ : 0 < β)
    (H₀ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      (s = 0 → HasLogMoment (HRS.Whole.withDensityReal ρ) L) → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (Z : Ω → EucConfig d N), Measurable Z →
      HRS.relEntropy (P.map Z) (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β
        (HRS.Whole.withDensityReal ρ)) ≤ ENNReal.ofReal (H₀ * N * deltaN d s N) →
      ∀ (v : Euc d → Euc d) (Λ : ℝ≥0), LipschitzWith Λ v →
        ∫⁻ ζ, ENNReal.ofReal |commN d s v (Z ζ) (HRS.Whole.withDensityReal ρ)| ∂P ≤
          ENNReal.ofReal (C * Λ * deltaN d s N) := by
  obtain ⟨C, hC0, hC⟩ := s104_comm_expect hd s hs0 hsd M L β hβ H₀
  refine ⟨C, hC0, fun ρ hρ hρM hlog N hN Ω _ P _ Z hZ hH v Λ hv => ?_⟩
  haveI : IsProbabilityMeasure (P.map Z) :=
    ⟨by rw [Measure.map_apply hZ MeasurableSet.univ]; simp⟩
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := Q34.isProbabilityMeasure_nu hρ
  obtain ⟨hint, hbd⟩ := hC ρ hρ hρM hlog N hN (P.map Z) inferInstance hH v Λ hv
  have hcm := HRS.MS.Comm.comm_meas (d := d) (s := s) v hv.continuous.measurable
  have hgm : Measurable (fun X : EucConfig d N => |commN d s v X (HRS.Whole.withDensityReal ρ)|) := by
    have e : (fun X : EucConfig d N => |commN d s v X (HRS.Whole.withDensityReal ρ)|) =
        fun X => |2 * pairEnergy (commutatorKernel d s v) X (HRS.Whole.withDensityReal ρ)| := by
      funext X; rw [s32_commN_eq]
    rw [e]
    exact continuous_abs.measurable.comp ((wr9_measurable_pairEnergy hcm).const_mul 2)
  rw [← lintegral_map (f := fun X : EucConfig d N =>
      ENNReal.ofReal |commN d s v X (HRS.Whole.withDensityReal ρ)|) hgm.ennreal_ofReal hZ,
    ← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun X => abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hbd

lemma s104_vec_bound (C : WholeCoeff d) {k : ℕ} {t : ℝ} {ψ : Euc d → ℝ} {A c : ℝ} (hA : 0 ≤ A)
    (h : R2OrbitGrad C k t ψ A c) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) t) :
    ContDiff ℝ k (fun x => gradient (propagatorW C r t ψ) x) ∧
    ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (fun x => gradient (propagatorW C r t ψ) x) x‖ ≤
      A * Real.exp (-c * (t - r)) := by
  have hA' : 0 ≤ A * Real.exp (-c * (t - r)) := by positivity
  by_cases hex : ∃ f, IsClassicalAdjointW C t ψ f
  · have hp : propagatorW C r t ψ = hex.choose r := by
      unfold propagatorW; rw [dif_pos hex]
    rw [hp]
    obtain ⟨hcd, hcb⟩ := h hex.choose hex.choose_spec r hr
    exact ⟨hcd, s104_cbNormVecE_le hA' hcb⟩
  · have hp : propagatorW C r t ψ = 0 := by
      unfold propagatorW; rw [dif_neg hex]
    rw [hp]
    have hz : (fun x : Euc d => gradient (0 : Euc d → ℝ) x) = fun _ => (0 : Euc d) := by
      funext x; simp [gradient]
    rw [hz]
    refine ⟨contDiff_const, fun j hj x => ?_⟩
    rcases j with _ | j
    · simp; positivity
    · rw [iteratedFDeriv_const_of_ne (by omega)]; simpa using hA'

lemma s104_grad_lip (C : WholeCoeff d) {k : ℕ} (hk : 1 ≤ k) {t : ℝ} {ψ : Euc d → ℝ} {A c : ℝ} (hA : 0 ≤ A)
    (h : R2OrbitGrad C k t ψ A c) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) t) :
    LipschitzWith (⟨A * Real.exp (-c * (t - r)), by positivity⟩ : ℝ≥0)
      (fun x => gradient (propagatorW C r t ψ) x) := by
  obtain ⟨hcd, hb⟩ := s104_vec_bound C hA h hr
  refine lipschitzWith_of_nnnorm_fderiv_le (hcd.differentiable (by exact_mod_cast (by omega : k ≠ 0))) fun x => ?_
  have h1 := hb 1 hk x
  rw [norm_iteratedFDeriv_one] at h1
  exact_mod_cast h1

end HRS.MS.R2WinErr

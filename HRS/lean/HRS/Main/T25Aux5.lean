import HRS.Main.T25Aux1
import HRS.Equilibrium.Preparation
import HRS.PDE.MovSXFinal
import HRS.PDE.MovSXAux4

/-!
# T25-IN, part 5 (PREP-SCALES): the scales of the standard preparations (`prepared_scales`)

TeX M L795-801, proof L6748-6767 (`P:eq:iid-bound`, `P:eq:initial-p-ratio`).  For the initial density `ρ°` fixed (smooth, positive):

* `t25_press`: the two-sided pressure bound `|log K_{N,γ}(μ°)| ≤ C N δ_N` for `γ ∈ [β_m, β_p] ⊂ (0,∞)`
  (`pressure_two_sided` at `θ = 0`, `h = 0`), `t25_hpress`: the upper bound for ALL `γ ∈ [0,B+1]` (Hölder/Jensen below `1`);
* `t25_scales_entropy`: `H(ℚ_{N,β₀}(μ°) | ℚ_{N,β}(μ°)) ≤ C N δ_N` (`entropy_endpoint`, Proposition 4.26);
* `t25_J_of_lintegral`: from `∫ (dν₀/dQ)^p dQ ≤ M` to `MemLp` and `log ‖h‖_p ≤ max 0 (log M/p)`;
* `t25_scales_log` (`s = 0`, any `β₀ ≥ 0`): Proposition 4.25 `log_prep_uniform`;
* `t25_scales_ratio` (`β₀ > 0`): the exact ratio identity `P:eq:initial-p-ratio` via `rnDeriv_tilted_left_self`, `tilted_tilted`,
  `integral_exp_tilted`, then the pressure bound at the three positive temperatures `β, β₀, β_* = pβ₀ - (p-1)β`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace T25

open HRS.Main

variable {d : ℕ}

/-- Hölder/Jensen on a probability space: `K_γ ≤ K_1^γ` for `0 ≤ γ ≤ 1`. -/
theorem t25_jensen {N : ℕ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ] (F : Config d N → ℝ)
    (hF : Measurable F) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    ∫⁻ X, ENNReal.ofReal (Real.exp (-γ * N * F X)) ∂(Measure.pi fun _ : Fin N => μ) ≤
      (∫⁻ X, ENNReal.ofReal (Real.exp (-1 * N * F X)) ∂(Measure.pi fun _ : Fin N => μ)) ^ γ := by
  rcases hγ0.eq_or_lt with h0 | hpos
  · subst h0
    simp
  · set π : Measure (Config d N) := Measure.pi fun _ : Fin N => μ with hπ
    set h : Config d N → ℝ≥0∞ := fun X => ENNReal.ofReal (Real.exp (-1 * N * F X)) with hh
    have hhm : Measurable h :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul hF))
    have hpow : ∀ X, h X ^ γ = ENNReal.ofReal (Real.exp (-γ * N * F X)) := fun X => by
      simp only [hh]
      rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul]
      congr 2
      ring
    have key := lintegral_rpow_mono_meas π hhm hpos hγ1
    simp only [hpow, Real.rpow_one, ENNReal.rpow_one, div_one] at key
    have hA : ∫⁻ X, ENNReal.ofReal (Real.exp (-γ * N * F X)) ∂π =
        ((∫⁻ X, ENNReal.ofReal (Real.exp (-γ * N * F X)) ∂π) ^ (1 / γ)) ^ γ := by
      rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hpos.ne', ENNReal.rpow_one]
    rw [hA]
    exact ENNReal.rpow_le_rpow key hpos.le

/-- Pressure data for the fixed initial density: `|log K_{N,γ}(μ°)| ≤ C N δ_N` for `γ ∈ [βm, βp]`, `βm > 0`. -/
theorem t25_press (S : PreparedData d) (βm βp : ℝ) (hβm : 0 < βm) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → ∀ γ ∈ Set.Icc βm βp,
      ENNReal.ofReal (Real.exp (-(C * N * deltaN d S.s N))) ≤
        modNormalizerE (periodicRiesz d S.s) N γ S.μ0 ∧
      modNormalizerE (periodicRiesz d S.s) N γ S.μ0 ≤
        ENNReal.ofReal (Real.exp (C * N * deltaN d S.s N)) := by
  have hd1 : 1 ≤ d := by have := S.hd; omega
  obtain ⟨cstar, A, hA0, hw, -, -⟩ := movsx_hdom hd1 S.hs0 S.hsd
  obtain ⟨c₀, Λ₂, hc₀, hb⟩ := movT_traj_uniform_proof S.s S.β S.V S.ρ0 S.ρ S.hs0 S.hsd S.hβ S.hV S.hρ0
    (t25_traj S).global
  obtain ⟨θ₀, C, hθ₀, hC0, hP⟩ := pressure_two_sided hd1 S.s S.hs0 S.hsd cstar hw βm βp hβm c₀ hc₀
    (fun k => Torus.cbNorm k S.ρ0) 0
  refine ⟨C, hC0, fun N hN γ hγ => ?_⟩
  have hlow : ∀ x, c₀ ≤ S.ρ0 x := by
    have := (hb 0 le_rfl).1
    rwa [S.hρ_init] at this
  have := hP S.ρ0 S.hρ0.density S.hρ0.smooth hlow (fun k => le_rfl) (fun _ _ => 0) measurable_const
    (fun _ _ => rfl) (fun x y => by simp) N hN γ hγ 0 (by simpa using hθ₀.le)
  simpa [modNormalizerE, modulatedEnergyKernel, PreparedData.μ0] using this

/-- Row bound for the Riesz kernel under the fixed initial density. -/
theorem t25_rowOK (S : PreparedData d) :
    RowOK S.μ0 (fun x y => periodicRiesz d S.s (x - y)) := by
  have hd1 : 1 ≤ d := by have := S.hd; omega
  obtain ⟨cstar, A, hA0, hw, -, -⟩ := movsx_hdom hd1 S.hs0 S.hsd
  have hcont : Continuous S.ρ0 := mova_continuous_of_isCk (mova_isCk_two_of_smooth S.hρ0.smooth)
  obtain ⟨Mρ, hMρ0, hMρ⟩ := exists_abs_bound hcont
  exact (rowOK_g_h hd1 S.s S.hs0 S.hsd cstar hw 0 hMρ0 (fun x => (le_abs_self _).trans (hMρ x))
    (h := fun _ _ => 0) measurable_const (fun x y => by simp)).1

theorem t25_hpress (S : PreparedData d) (B : ℝ) (hB : 0 ≤ B) :
    ∃ Cp : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ γ ∈ Set.Icc (0 : ℝ) (B + 1),
      modNormalizerE (periodicRiesz d S.s) N γ S.μ0 ≤
        ENNReal.ofReal (Real.exp (Cp * N * deltaN d S.s N)) := by
  obtain ⟨C, hC0, hP⟩ := t25_press S 1 (B + 1) one_pos
  refine ⟨C, fun N hN γ hγ => ?_⟩
  by_cases h1 : 1 ≤ γ
  · exact (hP N hN γ ⟨h1, hγ.2⟩).2
  · push_neg at h1
    haveI := isProb_withDensityReal S.hρ0.density
    haveI : IsProbabilityMeasure S.μ0 := by unfold PreparedData.μ0; infer_instance
    have hF : Measurable (fun X : Config d N => modulatedEnergyKernel (periodicRiesz d S.s) X S.μ0) :=
      measurable_modulatedEnergy (t25_rowOK S)
    have hJ := t25_jensen (μ := S.μ0) _ hF hγ.1 h1.le
    have hK1 := (hP N hN 1 ⟨le_rfl, by linarith [hγ.2, hB]⟩).2
    have hδ : 1 ≤ (N : ℝ) * deltaN d S.s N := one_le_mul_deltaN S.hs0 N (by omega)
    have hCN : 0 ≤ C * N * deltaN d S.s N := by
      have : C * N * deltaN d S.s N = C * ((N : ℝ) * deltaN d S.s N) := by ring
      rw [this]; positivity
    calc modNormalizerE (periodicRiesz d S.s) N γ S.μ0
        ≤ (modNormalizerE (periodicRiesz d S.s) N 1 S.μ0) ^ γ := hJ
      _ ≤ (ENNReal.ofReal (Real.exp (C * N * deltaN d S.s N))) ^ γ :=
          ENNReal.rpow_le_rpow hK1 hγ.1
      _ = ENNReal.ofReal (Real.exp (γ * (C * N * deltaN d S.s N))) := by
          rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul]
          congr 2; ring
      _ ≤ _ := ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by nlinarith [hγ.1, hCN, h1]))

/-- `H(ℚ_{N,β₀}(μ°) | ℚ_{N,β}(μ°)) ≤ C N δ_N` (Proposition 4.26 `O:eq:entropy-endpoint` with the pressure input). -/
theorem t25_scales_entropy (S : PreparedData d) (β₀ : ℝ) (hβ₀ : 0 ≤ β₀) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      relEntropy (modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0)
          (modulatedGibbs (periodicRiesz d S.s) N S.β S.μ0) ≤
        ENNReal.ofReal (C * N * deltaN d S.s N) := by
  haveI := isProb_withDensityReal S.hρ0.density
  haveI : IsProbabilityMeasure S.μ0 := by unfold PreparedData.μ0; infer_instance
  have hg : Measurable (periodicRiesz d S.s) := PoleCavityAux.measurable_periodicRiesz S.hd S.hs0 S.hsd
  have hgi : Integrable (periodicRiesz d S.s) := KernelAux.integrable_periodicRiesz S.hd S.hs0 S.hsd
  have hcont : Continuous S.ρ0 := mova_continuous_of_isCk (mova_isCk_two_of_smooth S.hρ0.smooth)
  obtain ⟨Mρ, hMρ0, hMρ⟩ := exists_abs_bound hcont
  have hI := PreparationAux.integrable_pair_withDensity hg hgi S.ρ0 Mρ
    (fun x => (le_abs_self _).trans (hMρ x)) (ν := S.μ0) rfl
  have hB : 0 ≤ max S.β β₀ := le_max_of_le_left S.hβ.le
  obtain ⟨Cp, hCp⟩ := t25_hpress S (max S.β β₀) hB
  obtain ⟨C', hC'⟩ := entropy_endpoint S.hd S.hs0 S.hsd S.μ0 (max S.β β₀) hB hI Cp hCp
  exact ⟨C', fun N hN => hC' N hN S.β ⟨S.hβ.le, le_max_left _ _⟩ β₀ ⟨hβ₀, le_max_right _ _⟩⟩

/-- From `∫ (dν/dQ)^p dQ ≤ M` to `MemLp` and the logarithm of the `L^p(Q)` norm of the density. -/
theorem t25_J_of_lintegral {α : Type*} [MeasurableSpace α] (Q ν : Measure α) {p : ℝ} (hp : 1 < p)
    {M : ℝ} (hM : 0 < M) (h : ∫⁻ x, (ν.rnDeriv Q x) ^ p ∂Q ≤ ENNReal.ofReal M) :
    MemLp (fun x => ((ν.rnDeriv Q) x).toReal) (ENNReal.ofReal p) Q ∧
      Real.log (eLpNorm (fun x => ((ν.rnDeriv Q) x).toReal) (ENNReal.ofReal p) Q).toReal ≤
        max 0 (Real.log M / p) := by
  have hp0 : 0 < p := by linarith
  set f : α → ℝ := fun x => ((ν.rnDeriv Q) x).toReal with hf
  have hfm : AEStronglyMeasurable f Q :=
    (Measure.measurable_rnDeriv ν Q).ennreal_toReal.aestronglyMeasurable
  have hnorm : eLpNorm f (ENNReal.ofReal p) Q = (∫⁻ x, ‖f x‖ₑ ^ p ∂Q) ^ (1 / p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hp0).ne' ENNReal.ofReal_ne_top hfm,
      ENNReal.toReal_ofReal hp0.le]
  have hpt : ∀ x, ‖f x‖ₑ ≤ ν.rnDeriv Q x := fun x => by
    simp only [hf]
    rw [Real.enorm_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_toReal_le
  have h1 : ∫⁻ x, ‖f x‖ₑ ^ p ∂Q ≤ ENNReal.ofReal M :=
    (lintegral_mono fun x => ENNReal.rpow_le_rpow (hpt x) hp0.le).trans h
  have h2 : eLpNorm f (ENNReal.ofReal p) Q ≤ ENNReal.ofReal (M ^ (1 / p)) := by
    rw [hnorm, ← ENNReal.ofReal_rpow_of_pos hM]
    exact ENNReal.rpow_le_rpow h1 (by positivity)
  have hlt : eLpNorm f (ENNReal.ofReal p) Q < ⊤ := lt_of_le_of_lt h2 ENNReal.ofReal_lt_top
  refine ⟨hlt, ?_⟩
  have h3 : (eLpNorm f (ENNReal.ofReal p) Q).toReal ≤ M ^ (1 / p) := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h2
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  rcases (ENNReal.toReal_nonneg (a := eLpNorm f (ENNReal.ofReal p) Q)).eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · calc Real.log (eLpNorm f (ENNReal.ofReal p) Q).toReal ≤ Real.log (M ^ (1 / p)) :=
          Real.log_le_log hpos h3
      _ = Real.log M / p := by rw [Real.log_rpow hM]; ring
      _ ≤ _ := le_max_right _ _

/-- Real normalisers from the `lintegral` ones: integrability and two-sided bounds. -/
theorem t25_K_of_E {α : Type*} [MeasurableSpace α] (π : Measure α) [IsProbabilityMeasure π]
    {φ : α → ℝ} (hφ : Measurable φ) {A : ℝ}
    (hl : ENNReal.ofReal (Real.exp (-A)) ≤ ∫⁻ x, ENNReal.ofReal (Real.exp (φ x)) ∂π)
    (hu : ∫⁻ x, ENNReal.ofReal (Real.exp (φ x)) ∂π ≤ ENNReal.ofReal (Real.exp A)) :
    Integrable (fun x => Real.exp (φ x)) π ∧ Real.exp (-A) ≤ ∫ x, Real.exp (φ x) ∂π ∧
      ∫ x, Real.exp (φ x) ∂π ≤ Real.exp A := by
  have hm : Measurable (fun x => Real.exp (φ x)) := Real.measurable_exp.comp hφ
  have hne : ∫⁻ x, ENNReal.ofReal (Real.exp (φ x)) ∂π ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hu
  have hi : Integrable (fun x => Real.exp (φ x)) π :=
    (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)).1 hne
  have heq := ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun x => (Real.exp_pos (φ x)).le)
  have hK0 : 0 ≤ ∫ x, Real.exp (φ x) ∂π := integral_nonneg fun x => (Real.exp_pos _).le
  rw [← heq] at hl hu
  exact ⟨hi, (ENNReal.ofReal_le_ofReal_iff hK0).1 hl,
    (ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le).1 hu⟩

/-- **The exact ratio identity `P:eq:initial-p-ratio` as an upper bound** (TeX M L6755-6760): for tilts
`ν_γ = π.tilted(-γ N F)`, `∫ (dν_{β₀}/dν_β)^p dν_β = K_β^{p-1} K_{β*} / K_{β₀}^p` with `β* = β + p(β₀ - β)`, so if
`e^{-A} ≤ K_γ ≤ e^{A}` at the three temperatures the moment is `≤ e^{(2p+2)A}`. -/
theorem t25_ratio_bound {α : Type*} [MeasurableSpace α] (π : Measure α) [IsProbabilityMeasure π]
    (F : α → ℝ) (hF : Measurable F) (N : ℝ) (β β₀ p A : ℝ) (hp : 1 < p) (hA : 0 ≤ A)
    (hE : ∀ γ : ℝ, (γ = β ∨ γ = β₀ ∨ γ = β + p * (β₀ - β)) →
      ENNReal.ofReal (Real.exp (-A)) ≤ ∫⁻ x, ENNReal.ofReal (Real.exp (-γ * N * F x)) ∂π ∧
      ∫⁻ x, ENNReal.ofReal (Real.exp (-γ * N * F x)) ∂π ≤ ENNReal.ofReal (Real.exp A)) :
    ∫⁻ x, ((π.tilted (fun x => -β₀ * N * F x)).rnDeriv (π.tilted (fun x => -β * N * F x)) x) ^ p
        ∂(π.tilted (fun x => -β * N * F x)) ≤ ENNReal.ofReal (Real.exp ((2 * p + 2) * A)) := by
  have hp0 : 0 < p := by linarith
  set f : ℝ → α → ℝ := fun γ x => -γ * N * F x with hf
  have hfm : ∀ γ, Measurable (f γ) := fun γ => measurable_const.mul hF
  have hK : ∀ γ : ℝ, (γ = β ∨ γ = β₀ ∨ γ = β + p * (β₀ - β)) →
      Integrable (fun x => Real.exp (f γ x)) π ∧ Real.exp (-A) ≤ ∫ x, Real.exp (f γ x) ∂π ∧
        ∫ x, Real.exp (f γ x) ∂π ≤ Real.exp A := fun γ hγ =>
    t25_K_of_E π (hfm γ) (hE γ hγ).1 (hE γ hγ).2
  obtain ⟨hiβ, hKβl, hKβu⟩ := hK β (Or.inl rfl)
  obtain ⟨hi0, hK0l, hK0u⟩ := hK β₀ (Or.inr (Or.inl rfl))
  set Kf : ℝ := ∫ x, Real.exp (f β x) ∂π with hKf
  set K0 : ℝ := ∫ x, Real.exp (f β₀ x) ∂π with hK0
  have hKfpos : 0 < Kf := lt_of_lt_of_le (Real.exp_pos _) hKβl
  have hK0pos : 0 < K0 := lt_of_lt_of_le (Real.exp_pos _) hK0l
  set ν : Measure α := π.tilted (f β) with hν
  haveI : IsProbabilityMeasure ν := isProbabilityMeasure_tilted hiβ
  set g : α → ℝ := fun x => f β₀ x - f β x with hg
  have hgm : Measurable g := (hfm β₀).sub (hfm β)
  have hν₀ : π.tilted (f β₀) = ν.tilted g := by
    rw [hν, tilted_tilted hiβ]
    congr 1
    funext x
    simp [hg]
  show ∫⁻ x, ((π.tilted (f β₀)).rnDeriv ν x) ^ p ∂ν ≤ _
  rw [hν₀]
  have hrn := rnDeriv_tilted_left_self (μ := ν) (f := g) hgm.aemeasurable
  have hZ : ∫ x, Real.exp (g x) ∂ν = K0 / Kf := by
    have := integral_exp_tilted (μ := π) (f := f β) (g := g)
    rw [← hν] at this
    rw [this]
    congr 2
    funext x
    simp [hg]
  set Z : ℝ := K0 / Kf with hZdef
  have hZpos : 0 < Z := div_pos hK0pos hKfpos
  have hZl : Real.exp (-(2 * A)) ≤ Z := by
    rw [hZdef, le_div_iff₀ hKfpos]
    calc Real.exp (-(2 * A)) * Kf ≤ Real.exp (-(2 * A)) * Real.exp A :=
          mul_le_mul_of_nonneg_left hKβu (Real.exp_pos _).le
      _ = Real.exp (-A) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ K0 := hK0l
  have hstep1 : ∫⁻ x, ((ν.tilted g).rnDeriv ν x) ^ p ∂ν =
      ∫⁻ x, ENNReal.ofReal (Real.exp (g x * p) / Z ^ p) ∂ν := by
    refine lintegral_congr_ae ?_
    filter_upwards [hrn] with x hx
    rw [hx, hZ, ENNReal.ofReal_rpow_of_nonneg (by positivity) hp0.le, Real.div_rpow
      (Real.exp_pos _).le hZpos.le, ← Real.exp_mul]
  rw [hstep1, hν, lintegral_tilted (μ := π) (f β), ← hKf]
  have hstar : ∀ x, ENNReal.ofReal (Real.exp (f β x) / Kf) *
      ENNReal.ofReal (Real.exp (g x * p) / Z ^ p) =
      ENNReal.ofReal (1 / (Kf * Z ^ p)) * ENNReal.ofReal (Real.exp (f (β + p * (β₀ - β)) x)) := by
    intro x
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have : f β x + g x * p = f (β + p * (β₀ - β)) x := by simp only [hf, hg]; ring
    rw [← this, Real.exp_add]
    field_simp
  simp_rw [hstar]
  have hmeas : Measurable (fun x => ENNReal.ofReal (Real.exp (f (β + p * (β₀ - β)) x))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hfm _))
  rw [lintegral_const_mul _ hmeas]
  have hEs := (hE (β + p * (β₀ - β)) (Or.inr (Or.inr rfl))).2
  have hc : 1 / (Kf * Z ^ p) ≤ Real.exp ((2 * p + 1) * A) := by
    have hZp : Real.exp (-(2 * p * A)) ≤ Z ^ p := by
      calc Real.exp (-(2 * p * A)) = (Real.exp (-(2 * A))) ^ p := by
            rw [← Real.exp_mul]; congr 1; ring
        _ ≤ Z ^ p := Real.rpow_le_rpow (Real.exp_pos _).le hZl hp0.le
    have hprod : Real.exp (-((2 * p + 1) * A)) ≤ Kf * Z ^ p := by
      calc Real.exp (-((2 * p + 1) * A)) = Real.exp (-A) * Real.exp (-(2 * p * A)) := by
            rw [← Real.exp_add]; congr 1; ring
        _ ≤ Kf * Z ^ p := mul_le_mul hKβl hZp (Real.exp_pos _).le hKfpos.le
    rw [div_le_iff₀ (by positivity)]
    calc (1 : ℝ) = Real.exp ((2 * p + 1) * A) * Real.exp (-((2 * p + 1) * A)) := by
          rw [← Real.exp_add]; simp
      _ ≤ Real.exp ((2 * p + 1) * A) * (Kf * Z ^ p) :=
          mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
  calc ENNReal.ofReal (1 / (Kf * Z ^ p)) *
        ∫⁻ x, ENNReal.ofReal (Real.exp (f (β + p * (β₀ - β)) x)) ∂π
      ≤ ENNReal.ofReal (Real.exp ((2 * p + 1) * A)) * ENNReal.ofReal (Real.exp A) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hc) hEs
    _ = ENNReal.ofReal (Real.exp ((2 * p + 2) * A)) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        congr 2; ring

theorem t25_ref0 (S : PreparedData d) (N : ℕ) :
    S.refMeasure N 0 = modulatedGibbs (periodicRiesz d S.s) N S.β S.μ0 := by
  unfold PreparedData.refMeasure PreparedData.μ0
  rw [S.hρ_init]

/-- `ρ°` as the density of the prepared reference: data for `movf_modGibbs_eq_tilted`. -/
theorem t25_tilted (S : PreparedData d) (N : ℕ) (hN : 2 ≤ N) {γ : ℝ} (hγ : 0 ≤ γ) :
    modulatedGibbs (periodicRiesz d S.s) N γ S.μ0 =
      (Measure.pi fun _ : Fin N => S.μ0).tilted
        (fun X => -γ * N * modulatedEnergyKernel (periodicRiesz d S.s) X S.μ0) := by
  have hd1 : 1 ≤ d := by have := S.hd; omega
  have hcont : Continuous S.ρ0 := mova_continuous_of_isCk (mova_isCk_two_of_smooth S.hρ0.smooth)
  exact movf_modGibbs_eq_tilted hd1 S.hs0 S.hsd S.hρ0.density hcont (by omega) hγ

/-- `β₀ > 0`: the `p`-moment of the density ratio, `≤ exp (A N δ_N)` (ratio identity + pressure at three temperatures). -/
theorem t25_scales_ratio (S : PreparedData d) (β₀ : ℝ) (hβ₀ : 0 < β₀) :
    ∃ p : ℝ, 1 < p ∧ ∃ A : ℝ, 0 ≤ A ∧ ∀ N : ℕ, 2 ≤ N →
      ∫⁻ X, ((modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0).rnDeriv
          (modulatedGibbs (periodicRiesz d S.s) N S.β S.μ0) X) ^ p
          ∂(modulatedGibbs (periodicRiesz d S.s) N S.β S.μ0) ≤
        ENNReal.ofReal (Real.exp (A * N * deltaN d S.s N)) := by
  haveI := isProb_withDensityReal S.hρ0.density
  haveI : IsProbabilityMeasure S.μ0 := by unfold PreparedData.μ0; infer_instance
  set δ₀ : ℝ := β₀ - S.β with hδ₀
  set ε : ℝ := min 1 (β₀ / (2 * (|δ₀| + 1))) with hε
  have hεpos : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hε2 : ε * (|δ₀| + 1) ≤ β₀ / 2 := by
    have h := min_le_right 1 (β₀ / (2 * (|δ₀| + 1)))
    have hpos : 0 < |δ₀| + 1 := by positivity
    calc ε * (|δ₀| + 1) ≤ β₀ / (2 * (|δ₀| + 1)) * (|δ₀| + 1) :=
          mul_le_mul_of_nonneg_right h hpos.le
      _ = β₀ / 2 := by field_simp
  set p : ℝ := 1 + ε with hp
  have hp1 : 1 < p := by linarith
  set βs : ℝ := S.β + p * δ₀ with hβs
  have hεδ : ε * |δ₀| ≤ β₀ / 2 := by nlinarith [abs_nonneg δ₀]
  have hβs_eq : βs = β₀ + ε * δ₀ := by simp only [hβs, hp, hδ₀]; ring
  have hβs_lo : β₀ / 2 ≤ βs := by
    have := neg_abs_le δ₀
    nlinarith
  have hβs_hi : βs ≤ 3 * β₀ / 2 := by
    have := le_abs_self δ₀
    nlinarith
  set βm : ℝ := min S.β (β₀ / 2) with hβm
  set βp : ℝ := max S.β (3 * β₀ / 2) with hβp
  have hβm0 : 0 < βm := lt_min S.hβ (by positivity)
  have hmem : ∀ γ : ℝ, (γ = S.β ∨ γ = β₀ ∨ γ = βs) → γ ∈ Set.Icc βm βp := by
    rintro γ (h | h | h)
    · subst h; exact ⟨min_le_left _ _, le_max_left _ _⟩
    · subst h
      exact ⟨(min_le_right _ _).trans (by linarith), (by linarith : γ ≤ 3 * γ / 2).trans (le_max_right _ _)⟩
    · subst h
      exact ⟨(min_le_right _ _).trans hβs_lo, hβs_hi.trans (le_max_right _ _)⟩
  obtain ⟨C, hC0, hP⟩ := t25_press S βm βp hβm0
  refine ⟨p, hp1, (2 * p + 2) * C, by positivity, fun N hN => ?_⟩
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hF : Measurable (fun X : Config d N => modulatedEnergyKernel (periodicRiesz d S.s) X S.μ0) :=
    measurable_modulatedEnergy (t25_rowOK S)
  have hδ : 1 ≤ (N : ℝ) * deltaN d S.s N := one_le_mul_deltaN S.hs0 N (by omega)
  have hA : 0 ≤ C * N * deltaN d S.s N := by
    have : C * N * deltaN d S.s N = C * ((N : ℝ) * deltaN d S.s N) := by ring
    rw [this]; positivity
  rw [t25_tilted S N hN S.hβ.le, t25_tilted S N hN hβ₀.le]
  have key := t25_ratio_bound (Measure.pi fun _ : Fin N => S.μ0)
    (fun X => modulatedEnergyKernel (periodicRiesz d S.s) X S.μ0) hF (N : ℝ) S.β β₀ p
    (C * N * deltaN d S.s N) hp1 hA (fun γ hγ => hP N hN γ (hmem γ (by
      rcases hγ with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h))))
  refine key.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (le_of_eq ?_)))
  ring

/-- `s = 0`: Proposition 4.25 `log_prep_uniform`. -/
theorem t25_scales_log (S : PreparedData d) (hs : S.s = 0) (β₀ : ℝ) (hβ₀ : 0 ≤ β₀) :
    ∃ p : ℝ, 1 < p ∧ ∃ A : ℝ, 0 ≤ A ∧ ∀ N : ℕ, 2 ≤ N →
      ∫⁻ X, ((modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0).rnDeriv
          (modulatedGibbs (periodicRiesz d S.s) N S.β S.μ0) X) ^ p
          ∂(modulatedGibbs (periodicRiesz d S.s) N S.β S.μ0) ≤
        ENNReal.ofReal (Real.exp (A * N * deltaN d S.s N)) := by
  have hcont : Continuous S.ρ0 := mova_continuous_of_isCk (mova_isCk_two_of_smooth S.hρ0.smooth)
  obtain ⟨Mρ, hMρ0, hMρ⟩ := exists_abs_bound hcont
  obtain ⟨p, hp, C, hC⟩ := log_prep_uniform S.hd S.ρ0 S.hρ0.density Mρ
    (fun x => (le_abs_self _).trans (hMρ x)) S.β β₀
  refine ⟨p, hp, Real.log (max C 1), Real.log_nonneg (le_max_right _ _), fun N hN => ?_⟩
  have h := (hC N hN S.β ⟨S.hβ.le, le_rfl⟩ β₀ ⟨hβ₀, le_rfl⟩).2
  have hδ : 1 ≤ (N : ℝ) * deltaN d S.s N := one_le_mul_deltaN S.hs0 N (by omega)
  have hA0 : 0 ≤ Real.log (max C 1) := Real.log_nonneg (le_max_right _ _)
  have hexp : max C 1 ≤ Real.exp (Real.log (max C 1) * N * deltaN d S.s N) := by
    calc max C 1 = Real.exp (Real.log (max C 1)) :=
          (Real.exp_log (lt_of_lt_of_le one_pos (le_max_right _ _))).symm
      _ ≤ _ := Real.exp_le_exp.2 (by
          have : Real.log (max C 1) * N * deltaN d S.s N =
            Real.log (max C 1) * ((N : ℝ) * deltaN d S.s N) := by ring
          rw [this]; nlinarith)
  have hexp0 : max C 1 ≤ Real.exp (Real.log (max C 1) * N * deltaN d 0 N) := by
    have := hexp
    rw [hs] at this
    exact this
  unfold PreparedData.μ0
  rw [hs]
  exact h.trans (ENNReal.ofReal_le_ofReal ((le_max_left C 1).trans hexp0))

/-- **`prepared_scales`** (Theorem 2.5, last paragraph, TeX M L795-801, proof L6748-6767), statement as in
`HRS.Main.prepared_scales`; relocated with the `type_of%` tie in `HRS/Main/T25Final.lean`. -/
theorem t25_prepared_scales (S : PreparedData d) (β₀ : ℝ) (hβ₀ : 0 ≤ β₀) :
    (∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      relEntropy (modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0) (S.refMeasure N 0) < ⊤ ∧
      S.B N (modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0) ≤ C * ((N : ℝ) * deltaN d S.s N)) ∧
    ((0 < β₀ ∨ S.s = 0) →
      ∃ p₀ : ℝ, 1 < p₀ ∧ ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
        MemLp (fun Y => (((modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0).rnDeriv
            (S.refMeasure N 0)) Y).toReal) (ENNReal.ofReal p₀) (S.refMeasure N 0) ∧
        S.J N (modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0) p₀ ≤ C * ((N : ℝ) * deltaN d S.s N)) := by
  refine ⟨?_, fun h => ?_⟩
  · obtain ⟨C', hC'⟩ := t25_scales_entropy S β₀ hβ₀
    refine ⟨2 + |C'|, fun N hN => ?_⟩
    have h1 := hC' N hN
    have hδ : 1 ≤ (N : ℝ) * deltaN d S.s N := one_le_mul_deltaN S.hs0 N (by omega)
    rw [t25_ref0]
    refine ⟨lt_of_le_of_lt h1 ENNReal.ofReal_lt_top, ?_⟩
    unfold PreparedData.B
    rw [t25_ref0]
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    rw [ENNReal.toReal_ofReal'] at h2
    have h3 : max (C' * N * deltaN d S.s N) 0 ≤ |C'| * ((N : ℝ) * deltaN d S.s N) := by
      refine max_le ?_ (by positivity)
      have : C' * N * deltaN d S.s N = C' * ((N : ℝ) * deltaN d S.s N) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
    nlinarith [abs_nonneg C']
  · obtain ⟨p, hp, A, hA, hint⟩ : ∃ p : ℝ, 1 < p ∧ ∃ A : ℝ, 0 ≤ A ∧ ∀ N : ℕ, 2 ≤ N →
        ∫⁻ X, ((modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0).rnDeriv
            (modulatedGibbs (periodicRiesz d S.s) N S.β S.μ0) X) ^ p
            ∂(modulatedGibbs (periodicRiesz d S.s) N S.β S.μ0) ≤
          ENNReal.ofReal (Real.exp (A * N * deltaN d S.s N)) := by
      rcases h with hpos | hs
      · exact t25_scales_ratio S β₀ hpos
      · exact t25_scales_log S hs β₀ hβ₀
    refine ⟨p, hp, 2 + A / p, fun N hN => ?_⟩
    have hδ : 1 ≤ (N : ℝ) * deltaN d S.s N := one_le_mul_deltaN S.hs0 N (by omega)
    have hp0 : 0 < p := by linarith
    obtain ⟨hmem, hlog⟩ := t25_J_of_lintegral (modulatedGibbs (periodicRiesz d S.s) N S.β S.μ0)
      (modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0) hp (Real.exp_pos (A * N * deltaN d S.s N))
      (hint N hN)
    rw [Real.log_exp] at hlog
    have hApN : 0 ≤ A * N * deltaN d S.s N / p := by
      have : A * N * deltaN d S.s N = A * ((N : ℝ) * deltaN d S.s N) := by ring
      rw [this]; positivity
    rw [max_eq_right hApN] at hlog
    rw [t25_ref0]
    refine ⟨hmem, ?_⟩
    unfold PreparedData.J
    rw [t25_ref0]
    have : A * N * deltaN d S.s N / p = A / p * ((N : ℝ) * deltaN d S.s N) := by
      field_simp
    rw [this] at hlog
    nlinarith

end T25

end HRS

end

/-
# HRS.Equilibrium.MarginalEntropy -- coarse entropy bound for `Q_{N,β}(μ)` (EQ-02)

`A:eq:coarse-entropy`: `KL(Q_{N,β}(μ) ‖ μ^{⊗N}) ≤ β N o_N(Λ) + β B/2 = o(N)`, from the energy lower bound
`F_N ≥ -o_N(Λ)` (`coercivity_lower`) and Jensen for the normaliser, `K_{N,β}(μ) ≥ exp(β ∬g / 2)`
(`E_{μ^N} F_N = -(2N)⁻¹ ∬ g`).  Hence `‖π_N - μ‖_TV → 0` (`tendsto_tv_firstMarginal`, via
subadditivity of entropy and Pinsker, `HRS.External.Entropy`).
-/
import HRS.Equilibrium.MarginalCavity
import HRS.External.Entropy

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS

namespace MarginalAux

variable {d : ℕ} {s : ℝ}

open HRS.External HRS.PoleCavityAux

theorem abs_mul_exp_le_of_le {x W : ℝ} (hx : x ≤ W) : |x| * Real.exp x ≤ max (|W| * Real.exp W) 1 := by
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h]
    have h1 : x * Real.exp x ≤ W * Real.exp W :=
      mul_le_mul hx (Real.exp_le_exp.2 hx) (Real.exp_pos _).le (h.trans hx)
    exact (h1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le)).trans (le_max_left _ _)
  · rw [abs_of_nonpos h]
    have h2 := Real.add_one_le_exp (-x)
    have h3 : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
    have : -x * Real.exp x ≤ 1 := by nlinarith [Real.exp_pos x]
    exact this.trans (le_max_right _ _)

/-- The modulated energy is integrable under `μ^{⊗N}`. -/
theorem integrable_energy (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Torus d → ℝ}
    (hρ : SmoothPosDensity ρ) (N : ℕ) (hN : 1 ≤ N) :
    Integrable (fun X : Config d N => modulatedEnergyKernel (periodicRiesz d s) X (withDensityReal ρ))
      (Measure.pi fun _ : Fin N => withDensityReal ρ) := by
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨B, Cc, hB0, hK⟩ := kerData_periodicRiesz hd hs0 hsd hρ
  set μ := withDensityReal ρ
  set g := periodicRiesz d s
  have hint : Integrable (fun p : Torus d × Torus d => g (p.1 - p.2)) (μ.prod μ) := hK.int2
  have hpair : ∀ i j : Fin N, i ≠ j →
      Integrable (fun X : Config d N => g (X i - X j)) (Measure.pi fun _ : Fin N => μ) :=
    fun i j hij => integrable_pair_comp μ hij (H := fun p => g (p.1 - p.2)) hint
  have hconv_int : Integrable (fun x => ∫ y, g (x - y) ∂μ) μ := hint.integral_prod_left
  have h1 : ∀ i : Fin N, Integrable (fun X : Config d N => ∫ y, g (X i - y) ∂μ)
      (Measure.pi fun _ : Fin N => μ) := fun i =>
    integrable_comp_eval (μ := fun _ : Fin N => μ) (i := i) hconv_int
  have hT1 : Integrable (fun X : Config d N => ∑ i, ∑ j ∈ Finset.univ.erase i, g (X i - X j))
      (Measure.pi fun _ : Fin N => μ) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j hj =>
      hpair i j (Finset.ne_of_mem_erase hj).symm
  have hT2 : Integrable (fun X : Config d N => ∑ i, ∫ y, g (X i - y) ∂μ)
      (Measure.pi fun _ : Fin N => μ) := integrable_finsetSum _ fun i _ => h1 i
  unfold modulatedEnergyKernel modulatedEnergy
  exact ((hT1.const_mul _).sub (hT2.const_mul _)).add (integrable_const _)

open InformationTheory in
/-- **Coarse entropy bound** `A:eq:coarse-entropy` for the full law. -/
theorem klDiv_modulatedGibbs_le (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) :
    ∃ C C' : ℝ, 0 ≤ C ∧ 0 ≤ C' ∧ ∀ N : ℕ, 2 ≤ N →
      klDiv (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ))
          (Measure.pi fun _ : Fin N => withDensityReal ρ) ≤
        ENNReal.ofReal (C * ((N : ℝ) * aN d s N) + C') := by
  have hμ := isProbabilityMeasure_mu hρ
  have hd1 : 1 ≤ d := by omega
  obtain ⟨B, Cc, hB0, hK⟩ := kerData_periodicRiesz hd hs0 hsd hρ
  obtain ⟨C₀, hC₀, hcoer⟩ := coercivity_lower hd1 hs0 hsd
  obtain ⟨Λ, hΛ0, hΛ⟩ := exists_density_bound hρ
  set Λ' : ℝ := max Λ 1 with hΛ'
  have hΛ'1 : 1 ≤ Λ' := le_max_right _ _
  have hΛ'b : ∀ x, ρ x ≤ Λ' := fun x => (hΛ x).trans (le_max_left _ _)
  obtain ⟨C₀', hC₀', hoN⟩ := oNΛ_le_aN hd1 hs0 hsd C₀ hC₀ Λ' hΛ'1
  refine ⟨β * C₀', β * (B / 2), by positivity, by positivity, fun N hN => ?_⟩
  set μ := withDensityReal ρ with hμdef
  set g := periodicRiesz d s with hgdef
  set P : Measure (Config d N) := Measure.pi fun _ : Fin N => μ with hP
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hgm : Measurable g := measurable_periodicRiesz hd hs0 hsd
  have heven : ∀ x, g (-x) = g x := fun x => periodicRiesz_neg x
  -- energy and exponent
  set F : Config d N → ℝ := fun X => modulatedEnergyKernel g X μ with hF
  set w : Config d N → ℝ := fun X => -β * N * F X with hw
  have hFi : Integrable F P := integrable_energy hd hs0 hsd hρ N (by omega)
  have hlam : 0 ≤ β / N := by positivity
  set wc : Config d N → ℝ := fun Y => -(β / N) * pairSum g Y + β * ∑ i, convMeasure g μ (Y i) with hwc
  have hwcm : Measurable wc := measurable_cavityW hgm μ N (β / N) β
  have hE : ∀ X : Config d N, w X = wc X - β * N * Calib.Kq g μ := by
    intro X
    show -β * N * modulatedEnergyKernel g X μ = _
    rw [Calib.modEnergy_q_eq (by omega : 0 < N) β X]
    unfold Calib.E0
    simp only [hwc]
    rw [RefSmall.pairSum_eq_half heven X, ← Finset.mul_sum]
    ring
  obtain ⟨W, hW⟩ := cavity_weight_le hd hs0 hsd β hρ N (β / N) hlam
  have hwb : ∀ X, w X ≤ W - β * N * Calib.Kq g μ := fun X => by rw [hE X]; linarith [hW X]
  have hwm : Measurable w := by
    have : w = fun X => wc X - β * N * Calib.Kq g μ := funext hE
    rw [this]; exact hwcm.sub measurable_const
  have hexp : Integrable (fun X => Real.exp (w X)) P :=
    Integrable.of_bound (C := Real.exp (W - β * N * Calib.Kq g μ)) (Real.measurable_exp.comp hwm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.2 (hwb X))
  have hQ : modulatedGibbs g N β μ = P.tilted w := Calib.modulatedGibbs_eq_tilted hexp
  set Q := modulatedGibbs g N β μ with hQdef
  set Z := ∫ X, Real.exp (w X) ∂P with hZ
  have hZpos : 0 < Z := integral_exp_pos hexp
  have hQprob : IsProbabilityMeasure Q := by
    rw [hQ]; exact isProbabilityMeasure_tilted hexp
  have hac : Q ≪ P := by rw [hQ]; exact tilted_absolutelyContinuous P w
  have hllr : llr Q P =ᵐ[Q] fun X => w X - Real.log Z := by
    have := log_rnDeriv_tilted_left_self hexp
    rw [← hQ] at this
    exact hac.ae_le this
  have hwQ : Integrable w Q := by
    rw [hQ, integrable_tilted_iff hexp]
    refine Integrable.of_bound (C := max (|W - β * N * Calib.Kq g μ| * Real.exp (W - β * N * Calib.Kq g μ)) 1)
      ((Real.measurable_exp.comp hwm).mul hwm).aestronglyMeasurable (Filter.Eventually.of_forall fun X => ?_)
    simp only [smul_eq_mul, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    rw [mul_comm]
    exact abs_mul_exp_le_of_le (hwb X)
  have hllrI : Integrable (llr Q P) Q := (hwQ.sub (integrable_const _)).congr hllr.symm
  rw [klDiv_of_ac_of_integrable hac hllrI]
  haveI : IsProbabilityMeasure P := by rw [hP]; infer_instance
  have h1 : P.real Set.univ = 1 := by simp [Measure.real]
  have h2 : Q.real Set.univ = 1 := by simp [Measure.real]
  rw [h1, h2, add_sub_cancel_right, integral_congr_ae hllr, integral_sub hwQ (integrable_const _), integral_const]
  simp only [h2, smul_eq_mul, one_mul]
  refine ENNReal.ofReal_le_ofReal ?_
  -- upper bound of `∫ w dQ`
  have hnc : ∀ᵐ X ∂Q, X ∉ collisionSet d N := by
    exact hac.ae_le (RefSmall.ae_not_collision hd1 hρ.density N)
  have hFlow : ∀ᵐ X ∂Q, -oNΛ d s C₀ Λ' N ≤ F X := by
    filter_upwards [hnc] with X hX
    have := hcoer Λ' hΛ'1 N hN ρ hρ.density hΛ'b X hX
    show -oNΛ d s C₀ Λ' N ≤ rieszEnergy d s X μ
    linarith
  have hwQup : ∫ X, w X ∂Q ≤ β * N * oNΛ d s C₀ Λ' N := by
    have : ∫ X, w X ∂Q ≤ ∫ _X, β * N * oNΛ d s C₀ Λ' N ∂Q := by
      refine integral_mono_ae hwQ (integrable_const _) ?_
      filter_upwards [hFlow] with X hX
      simp only [hw]
      have hb : 0 ≤ β * N := by positivity
      nlinarith
    simpa [h2] using this
  -- Jensen lower bound of `log Z`
  have hwi : Integrable w P := by
    have : w = fun X => (-β * N) * F X := rfl
    rw [this]; exact hFi.const_mul _
  have hJ : ∫ X, w X ∂P ≤ Real.log Z := by
    have := EF.ef_cgf_ge (P := P) (X := w) (b := W - β * N * Calib.Kq g μ) hwm hwb hwi
    simpa [cgf, mgf, hZ] using this
  have hEF : ∫ X, F X ∂P = -(1 / (2 * N)) * ∫ p : Torus d × Torus d, g (p.1 - p.2) ∂(μ.prod μ) :=
    expectation_modulatedEnergy_iid g μ (by omega) hK.int2 hK.int
  have hI : -B ≤ ∫ p : Torus d × Torus d, g (p.1 - p.2) ∂(μ.prod μ) := by
    have := integral_mono (integrable_const (-B)) hK.int2 (fun p => hK.lower _)
    simpa using this
  have hwP : ∫ X, w X ∂P = (β / 2) * ∫ p : Torus d × Torus d, g (p.1 - p.2) ∂(μ.prod μ) := by
    have : ∫ X, w X ∂P = (-β * N) * ∫ X, F X ∂P := integral_const_mul _ _
    rw [this, hEF]; field_simp
  have hoN' := hoN N hN
  have hb : 0 ≤ β * N := by positivity
  have : β * N * oNΛ d s C₀ Λ' N ≤ β * N * (C₀' * aN d s N) := mul_le_mul_of_nonneg_left hoN' hb
  have hI2 : (β / 2) * (-B) ≤ (β / 2) * ∫ p : Torus d × Torus d, g (p.1 - p.2) ∂(μ.prod μ) :=
    mul_le_mul_of_nonneg_left hI (by positivity)
  nlinarith


open InformationTheory in
/-- `‖π_N - μ‖_TV → 0` for the first marginal of the full law. -/
theorem tendsto_tvDist_Q (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) :
    Tendsto (fun N : ℕ => Entropy.tvDist
      ((modulatedGibbs (periodicRiesz d s) (N + 1) β (withDensityReal ρ)).map fun X : Config d (N + 1) => X 0)
      (withDensityReal ρ)) atTop (𝓝 0) := by
  have hμ := isProbabilityMeasure_mu hρ
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C, C', hC, hC', hkl⟩ := klDiv_modulatedGibbs_le hd hs0 hsd hβ hρ
  have hprob : ∀ N : ℕ, IsProbabilityMeasure (modulatedGibbs (periodicRiesz d s) (N + 1) β (withDensityReal ρ)) := by
    intro N
    rw [modulatedGibbs_eq_cavity hd hs0 hsd hβ hρ (N + 1) (Nat.succ_pos N)]
    exact cavity_isProb hd hs0 hsd β hρ (N + 1) _ (by positivity)
  have hex : ∀ N : ℕ, Entropy.IsExchangeable (modulatedGibbs (periodicRiesz d s) (N + 1) β (withDensityReal ρ)) := by
    intro N
    rw [modulatedGibbs_eq_cavity hd hs0 hsd hβ hρ (N + 1) (Nat.succ_pos N)]
    exact cavityLaw_exchangeable hd hs0 hsd β hρ (N + 1) _
  refine Entropy.tendsto_tvDist_firstMarginal (E := Torus d) (withDensityReal ρ)
    (fun N => modulatedGibbs (periodicRiesz d s) (N + 1) β (withDensityReal ρ)) hex ?_
  -- the entropy per particle
  have ha := RefSmall.tendsto_aN hd1 hs0 hsd
  have ha1 : Tendsto (fun N : ℕ => aN d s (N + 1)) atTop (𝓝 0) :=
    ha.comp (tendsto_add_atTop_nat 1)
  have hinv : Tendsto (fun N : ℕ => C' / ((N : ℝ) + 1)) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := C')).div_atTop (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
    simpa using this
  have hup : Tendsto (fun N : ℕ => ENNReal.ofReal (C * aN d s (N + 1) + C' / ((N : ℝ) + 1))) atTop (𝓝 0) := by
    have := (ha1.const_mul C).add hinv
    simp only [mul_zero, add_zero] at this
    have h2 := ENNReal.tendsto_ofReal this
    simpa using h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Filter.Eventually.of_forall fun N => bot_le) ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have h1 := hkl (N + 1) (by omega)
  have hN1 : ((N : ℝ) + 1) ≠ 0 := by positivity
  calc klDiv (modulatedGibbs (periodicRiesz d s) (N + 1) β (withDensityReal ρ))
        (Measure.pi fun _ : Fin (N + 1) => withDensityReal ρ) / ((N : ℝ≥0∞) + 1)
      ≤ ENNReal.ofReal (C * (((N + 1 : ℕ) : ℝ) * aN d s (N + 1)) + C') / ((N : ℝ≥0∞) + 1) := by
        gcongr
    _ = ENNReal.ofReal (C * aN d s (N + 1) + C' / ((N : ℝ) + 1)) := by
        have : ((N : ℝ≥0∞) + 1) = ENNReal.ofReal ((N : ℝ) + 1) := by
          rw [ENNReal.ofReal_add (by positivity) zero_le_one]; simp
        rw [this, ← ENNReal.ofReal_div_of_pos (by positivity)]
        congr 1
        push_cast
        field_simp


end MarginalAux

end HRS

import HRS.Main.A8PAux7

/-!
# Packet A8P, part 8: measurability and moments of the completed energy along the flow
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A8P

open HRS.GF HRS.Uniform

variable {d : ℕ}

section Energy

variable {S : MainData d} {R : ∀ N, Realization d N} {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ}
  {𝔈 : ℕ → ℝ}

theorem a8p_energy_meas (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ}
    (hN : 1 ≤ N) :
    Measurable fun p : ℝ × Config d N =>
      rieszEnergy d S.s p.2 (withDensityReal (S.ρ N (Q54c.clampT S.T p.1))) + oNΛ d S.s C₀ Λ N := by
  have hT : 0 ≤ S.T := S.hT.le
  have hd1 : 1 ≤ d := S.hd
  have hgm : Measurable (periodicRiesz d S.s) :=
    CoercAux.measurable_periodicRiesz_one hd1 S.hs0 S.hsd
  have hjm := a8p_rho_meas hS hN
  set ρt : ℝ → Torus d → ℝ := fun r => S.ρ N (Q54c.clampT S.T r) with hρt
  have hprob : ∀ r, IsProbDensity (ρt r) := fun r =>
    (hS.mean_field.solution N hN).density _ (Q54c.clampT_mem hT r)
  have hint : ∀ (r : ℝ) (f : Torus d → ℝ), ∫ y, f y ∂(withDensityReal (ρt r)) = ∫ y, ρt r y * f y :=
    fun r f => integral_withDensityReal_eq (ρt r) (hprob r).measurable (hprob r).nonneg f
  have hjm' : Measurable fun p : ℝ × Torus d => ρt p.1 p.2 := hjm
  unfold rieszEnergy modulatedEnergyKernel modulatedEnergy
  refine Measurable.add (Measurable.add (Measurable.sub ?_ ?_) ?_) measurable_const
  · refine measurable_const.mul (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_)
    exact hgm.comp (((measurable_pi_apply i).comp measurable_snd).sub ((measurable_pi_apply j).comp measurable_snd))
  · refine measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_)
    have e' : (fun p : ℝ × Config d N => ∫ y, (fun x y => periodicRiesz d S.s (x - y)) (p.2 i) y
        ∂(withDensityReal (ρt p.1))) = fun p => ∫ y, ρt p.1 y * periodicRiesz d S.s (p.2 i - y) :=
      funext fun p => hint p.1 _
    rw [e']
    have : StronglyMeasurable (fun q : (ℝ × Config d N) × Torus d =>
        ρt q.1.1 q.2 * periodicRiesz d S.s (q.1.2 i - q.2)) := by
      refine Measurable.stronglyMeasurable ?_
      refine Measurable.mul ?_ ?_
      · exact hjm'.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
      · exact hgm.comp (((measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)).sub measurable_snd)
    exact (this.integral_prod_right' (ν := volume)).measurable
  · have e : (fun p : ℝ × Config d N => ∫ x, ∫ y, (fun x y => periodicRiesz d S.s (x - y)) x y
        ∂(withDensityReal (ρt p.1)) ∂(withDensityReal (ρt p.1))) =
        fun p => ∫ x, ρt p.1 x * ∫ y, ρt p.1 y * periodicRiesz d S.s (x - y) := by
      funext p
      rw [hint p.1]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only
      rw [hint p.1]
    refine Measurable.const_mul ?_ _
    change Measurable (fun p : ℝ × Config d N => ∫ x, ∫ y, (fun x y => periodicRiesz d S.s (x - y)) x y
        ∂(withDensityReal (ρt p.1)) ∂(withDensityReal (ρt p.1)))
    rw [e]
    have h1 : StronglyMeasurable (fun q : (ℝ × Torus d) × Torus d =>
        ρt q.1.1 q.2 * periodicRiesz d S.s (q.1.2 - q.2)) := by
      refine Measurable.stronglyMeasurable (Measurable.mul ?_ ?_)
      · exact hjm'.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
      · exact hgm.comp ((measurable_snd.comp measurable_fst).sub measurable_snd)
    have h2 := h1.integral_prod_right' (ν := volume)
    have h3 : StronglyMeasurable (fun q : ℝ × Torus d =>
        ρt q.1 q.2 * ∫ y, ρt q.1 y * periodicRiesz d S.s (q.2 - y)) :=
      (hjm'.stronglyMeasurable).mul h2
    have h4 := h3.integral_prod_right' (ν := volume)
    exact h4.measurable.comp measurable_fst


/-- The positive part of the completed energy along the flow. -/
def a8pEn (S : MainData d) (R : ∀ N, Realization d N) (N : ℕ) (C₀ Λ : ℝ) (r : ℝ) (ω : (R N).Ω) : ℝ :=
  max (correctedEnergy (S.dyn N) C₀ Λ (S.ρ N) ((R N).X (Real.toNNReal r) ω) r) 0

theorem a8pEn_nonneg (S : MainData d) (R : ∀ N, Realization d N) (N : ℕ) (C₀ Λ r : ℝ)
    (ω : (R N).Ω) : 0 ≤ a8pEn S R N C₀ Λ r ω := le_max_right _ _

theorem a8pEn_ge (S : MainData d) (R : ∀ N, Realization d N) (N : ℕ) (C₀ Λ r : ℝ) (ω : (R N).Ω) :
    correctedEnergy (S.dyn N) C₀ Λ (S.ρ N) ((R N).X (Real.toNNReal r) ω) r ≤ a8pEn S R N C₀ Λ r ω :=
  le_max_left _ _

/-- Generic time-integral moment bound for a jointly measurable nonnegative process. -/
theorem a8p_time_moment {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 ≤ T) (G : ℝ → Ω → ℝ) (hGm : Measurable fun p : ℝ × Ω => G p.1 p.2)
    (hG0 : ∀ r ω, 0 ≤ G r ω) (E1 : ℝ) (hE1 : 0 ≤ E1)
    (hmom : ∀ r ∈ Set.Icc (0 : ℝ) T, ∫⁻ ω, ENNReal.ofReal (G r ω) ∂P ≤ ENNReal.ofReal E1) :
    (∀ᵐ ω ∂P, IntegrableOn (fun r => G r ω) (Set.Icc (0 : ℝ) T)) ∧
    ∫⁻ ω, ENNReal.ofReal (∫ r in Set.Icc (0 : ℝ) T, G r ω) ∂P ≤ ENNReal.ofReal (T * E1) ∧
    AEMeasurable (fun ω => ∫ r in Set.Icc (0 : ℝ) T, G r ω) P := by
  have hGr : ∀ r, Measurable (G r) := fun r => hGm.comp measurable_prodMk_left
  have hintG : ∀ r ∈ Set.Icc (0 : ℝ) T, Integrable (G r) P := by
    intro r hr
    refine ⟨(hGr r).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    refine lt_of_le_of_lt (le_of_eq ?_) (lt_of_le_of_lt (hmom r hr) ENNReal.ofReal_lt_top)
    refine lintegral_congr fun ω => ?_
    rw [← ofReal_norm_eq_enorm, Real.norm_of_nonneg (hG0 r ω)]
  have hE1' : ∀ r ∈ Set.Icc (0 : ℝ) T, ∫ ω, G r ω ∂P ≤ E1 := by
    intro r hr
    have h1 : ENNReal.ofReal (∫ ω, G r ω ∂P) = ∫⁻ ω, ENNReal.ofReal (G r ω) ∂P :=
      ofReal_integral_eq_lintegral_ofReal (hintG r hr) (Eventually.of_forall fun ω => hG0 r ω)
    have h2 := hmom r hr
    rw [← h1] at h2
    exact (ENNReal.ofReal_le_ofReal_iff hE1).1 h2
  exact gfb2_time_integral P hT G hGm (Eventually.of_forall fun ω r _ => hG0 r ω) hintG _ hE1'

/-- Second-moment version. -/
theorem a8p_time_moment2 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 ≤ T) (G : ℝ → Ω → ℝ) (hGm : Measurable fun p : ℝ × Ω => G p.1 p.2)
    (hG0 : ∀ r ω, 0 ≤ G r ω) (E2 : ℝ) (hE2 : 0 ≤ E2)
    (hmom : ∀ r ∈ Set.Icc (0 : ℝ) T, ∫⁻ ω, ENNReal.ofReal (G r ω) ^ 2 ∂P ≤ ENNReal.ofReal (E2 ^ 2)) :
    (∫⁻ ω, ENNReal.ofReal (∫ r in Set.Icc (0 : ℝ) T, G r ω) ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (T * E2) :=
  gfb2_time_L2 P hT G hGm (Eventually.of_forall fun ω r _ => hG0 r ω) E2 hE2 hmom


/-- The clamped version of the positive completed energy (jointly measurable). -/
def a8pEnC (S : MainData d) (R : ∀ N, Realization d N) (N : ℕ) (C₀ Λ : ℝ) (r : ℝ)
    (ω : (R N).Ω) : ℝ :=
  max (rieszEnergy d S.s ((R N).X (Real.toNNReal (Q54c.clampT S.T r)) ω)
    (withDensityReal (S.ρ N (Q54c.clampT S.T r))) + oNΛ d S.s C₀ Λ N) 0

theorem a8pEnC_nonneg (S : MainData d) (R : ∀ N, Realization d N) (N : ℕ) (C₀ Λ r : ℝ)
    (ω : (R N).Ω) : 0 ≤ a8pEnC S R N C₀ Λ r ω := le_max_right _ _

theorem a8pEnC_eq (S : MainData d) (R : ∀ N, Realization d N) (N : ℕ) (C₀ Λ : ℝ) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) S.T) (ω : (R N).Ω) :
    a8pEnC S R N C₀ Λ r ω = a8pEn S R N C₀ Λ r ω := by
  unfold a8pEnC a8pEn correctedEnergy
  rw [Q54c.clampT_of_mem hr]
  rfl

theorem a8pEnC_meas (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ}
    (hN : 1 ≤ N) {ℱ : Filtration ℝ (R N).mΩ}
    (hprog : IsProgressive ℱ (ofNNRealTime (R N).X)) :
    Measurable fun p : ℝ × (R N).Ω => a8pEnC S R N C₀ Λ p.1 p.2 := by
  have hZ := gfb2_progressive_meas ℱ (R N).X hprog S.hT.le
  have h := (a8p_energy_meas hS hN (C₀ := C₀) (Λ := Λ)).comp (measurable_fst.prodMk hZ)
  exact h.max measurable_const


theorem a8p_ofReal_max (x : ℝ) : ENNReal.ofReal (max x 0) = ENNReal.ofReal x := by
  rcases le_total x 0 with h | h
  · simp [max_eq_right h, ENNReal.ofReal_of_nonpos h]
  · simp [max_eq_left h]

theorem a8p_energy_integral (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ}
    (hN : 1 ≤ N) {ℱ : Filtration ℝ (R N).mΩ}
    (hprog : IsProgressive ℱ (ofNNRealTime (R N).X)) :
    (∀ᵐ ω ∂(R N).P, IntegrableOn (fun r => a8pEn S R N C₀ Λ r ω) (Set.Icc (0 : ℝ) S.T)) ∧
    ∫⁻ ω, ENNReal.ofReal (∫ r in Set.Icc (0 : ℝ) S.T, a8pEn S R N C₀ Λ r ω) ∂(R N).P ≤
      ENNReal.ofReal (S.T * 𝔈 N) ∧
    AEMeasurable (fun ω => ∫ r in Set.Icc (0 : ℝ) S.T, a8pEn S R N C₀ Λ r ω) (R N).P := by
  have hT : 0 ≤ S.T := S.hT.le
  have hmom : ∀ r ∈ Set.Icc (0 : ℝ) S.T,
      ∫⁻ ω, ENNReal.ofReal (a8pEnC S R N C₀ Λ r ω) ∂(R N).P ≤ ENNReal.ofReal (𝔈 N) := by
    intro r hr
    have h := hS.energy.bound N hN r hr
    refine le_trans (le_of_eq ?_) h
    refine lintegral_congr fun ω => ?_
    rw [a8pEnC_eq S R N C₀ Λ hr ω]
    unfold a8pEn
    rw [a8p_ofReal_max]
  obtain ⟨h1, h2, h3⟩ := a8p_time_moment (R N).P hT (a8pEnC S R N C₀ Λ)
    (a8pEnC_meas hS hN hprog) (a8pEnC_nonneg S R N C₀ Λ) (𝔈 N) (hS.energy.pos N hN).le hmom
  have hI : ∀ ω, ∫ r in Set.Icc (0 : ℝ) S.T, a8pEn S R N C₀ Λ r ω =
      ∫ r in Set.Icc (0 : ℝ) S.T, a8pEnC S R N C₀ Λ r ω := fun ω =>
    setIntegral_congr_fun measurableSet_Icc fun r hr => (a8pEnC_eq S R N C₀ Λ hr ω).symm
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [h1] with ω hω
    exact hω.congr_fun (fun r hr => a8pEnC_eq S R N C₀ Λ hr ω) measurableSet_Icc
  · simpa only [hI] using h2
  · simp only [hI]; exact h3


theorem a8p_energy_integral2 (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ}
    (hN : 1 ≤ N) {ℱ : Filtration ℝ (R N).mΩ}
    (hprog : IsProgressive ℱ (ofNNRealTime (R N).X)) {𝔈' : ℝ} (h𝔈' : 0 ≤ 𝔈')
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) S.T, ∫⁻ ω, ENNReal.ofReal
        ((correctedEnergy (S.dyn N) C₀ Λ (S.ρ N) ((R N).X (Real.toNNReal t) ω) t) ^ 2) ∂(R N).P ≤
      ENNReal.ofReal (𝔈' ^ 2)) :
    (∫⁻ ω, ENNReal.ofReal (∫ r in Set.Icc (0 : ℝ) S.T, a8pEn S R N C₀ Λ r ω) ^ 2 ∂(R N).P) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (S.T * 𝔈') := by
  have hT : 0 ≤ S.T := S.hT.le
  have hmom : ∀ r ∈ Set.Icc (0 : ℝ) S.T,
      ∫⁻ ω, ENNReal.ofReal (a8pEnC S R N C₀ Λ r ω) ^ 2 ∂(R N).P ≤ ENNReal.ofReal (𝔈' ^ 2) := by
    intro r hr
    refine le_trans ?_ (hb r hr)
    refine lintegral_mono fun ω => ?_
    rw [a8pEnC_eq S R N C₀ Λ hr ω, ← ENNReal.ofReal_pow (a8pEn_nonneg S R N C₀ Λ r ω)]
    refine ENNReal.ofReal_le_ofReal ?_
    unfold a8pEn
    rcases le_total (correctedEnergy (S.dyn N) C₀ Λ (S.ρ N) ((R N).X (Real.toNNReal r) ω) r) 0 with h | h
    · rw [max_eq_right h]; simp; positivity
    · rw [max_eq_left h]
  have key := a8p_time_moment2 (R N).P hT (a8pEnC S R N C₀ Λ) (a8pEnC_meas hS hN hprog)
    (a8pEnC_nonneg S R N C₀ Λ) 𝔈' h𝔈' hmom
  have hI : ∀ ω, ∫ r in Set.Icc (0 : ℝ) S.T, a8pEn S R N C₀ Λ r ω =
      ∫ r in Set.Icc (0 : ℝ) S.T, a8pEnC S R N C₀ Λ r ω := fun ω =>
    setIntegral_congr_fun measurableSet_Icc fun r hr => (a8pEnC_eq S R N C₀ Λ hr ω).symm
  simpa only [hI] using key

end Energy

end HRS.Main.A8P

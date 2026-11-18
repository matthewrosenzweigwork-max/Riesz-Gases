import HRS.Main.GFSpec3
import HRS.Uniform.Q54cAux56
import HRS.Main.GFSpec2

/-!
# Packet GFB2, part 1: joint measurability of the mean-field density and of the completed energy
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.GF

open HRS.Uniform

variable {d : ℕ}

theorem gfb2_rho_meas (S : GeneralSetup d) (M : Matrix (Fin d) (Fin d) ℝ) (hMF : S.MFHypM M) (N : ℕ) :
    Measurable fun p : ℝ × Torus d => S.ρ N (Q54c.clampT S.T p.1) p.2 := by
  obtain ⟨hMFN, hReg⟩ := hMF N
  have hT : 0 ≤ S.T := S.hT.le
  have hK : d + 1 ≤ S.γ + 2 * d + 12 := by omega
  have hK1 : 1 ≤ S.γ + 2 * d + 12 := by omega
  have hV : Torus.IsCk 1 (S.dynM M N).V := by
    have h1 : (1 : WithTop ℕ∞) ≤ ((S.γ + 2 * d + 12 : ℕ) : WithTop ℕ∞) := by
      exact_mod_cast hK1
    exact ContDiff.of_le S.V_reg h1
  have hd1 : 1 ≤ d := by have := S.hd; omega
  have hρ : ∀ r ∈ Set.Icc (0 : ℝ) S.T, IsProbDensity (S.ρ N r) ∧
      Torus.IsCk (S.γ + 2 * d + 12) (S.ρ N r) ∧ Torus.cbNorm (S.γ + 2 * d + 12) (S.ρ N r) ≤ S.Λ :=
    fun r hr => ⟨hMFN.density r hr, (hReg r hr).1, (hReg r hr).2⟩
  have hρc : ∀ r ∈ Set.Icc (0 : ℝ) S.T, Continuous (S.ρ N r) :=
    fun r hr => Q54c.isCk_continuous (hρ r hr).2.1
  have hrel : ∀ ψ : Torus d → ℝ, Torus.IsCk 2 ψ → ∀ t ∈ Set.Icc (0 : ℝ) S.T,
      (∫ x, ψ x * S.ρ N t x) - (∫ x, ψ x * S.ρ N 0 x) =
        ∫ r in Set.Icc (0 : ℝ) t, Q54c.wkG (S.dynM M N) (S.ρ N) ψ r := by
    intro ψ hψ t ht
    have := Q54c.weak_eq_wkG hMFN hψ ht
    rwa [Q54c.pair_wDR (hMFN.density t ht), Q54c.pair_wDR (hMFN.density 0 ⟨le_rfl, hT⟩)] at this
  have hbd : ∀ ψ : Torus d → ℝ, Torus.IsCk 2 ψ →
      ∃ C : ℝ, ∀ r ∈ Set.Icc (0 : ℝ) S.T, |Q54c.wkG (S.dynM M N) (S.ρ N) ψ r| ≤ C :=
    fun ψ hψ => Q54c.wkG_bound hd1 (S.dynM M N) S.T S.Λ _ hK1 hV (S.ρ N) hρ ψ hψ
  have hmeas : ∀ ψ : Torus d → ℝ, Torus.IsCk 2 ψ →
      Measurable (fun r => ∫ x, ψ x * S.ρ N (Q54c.clampT S.T r) x) := by
    intro ψ hψ
    obtain ⟨C, hC⟩ := hbd ψ hψ
    obtain ⟨f', hf', hff'⟩ := Q54c.junk_interval_measurable hT (Q54c.wkG (S.dynM M N) (S.ρ N) ψ)
      (fun t => ∫ x, ψ x * S.ρ N t x) hC (hrel ψ hψ)
    have : (fun r => ∫ x, ψ x * S.ρ N (Q54c.clampT S.T r) x) = fun r => f' (Q54c.clampT S.T r) := by
      funext r; exact (hff' _ (Q54c.clampT_mem hT r)).symm
    rw [this]; exact hf'.comp (Q54c.continuous_clampT S.T).measurable
  set ρt : ℝ → Torus d → ℝ := fun r => S.ρ N (Q54c.clampT S.T r) with hρt
  have hpt : ∀ x, Measurable fun r => ρt r x :=
    Q54c.measurable_pt_of_modes ρt (fun r => hρc _ (Q54c.clampT_mem hT r))
      (fun r => Q54c.summable_fcoef_of_ck
        (ContDiff.of_le (hρ _ (Q54c.clampT_mem hT r)).2.1 (by exact_mod_cast hK)))
      (fun r => (hMFN.density _ (Q54c.clampT_mem hT r)).integral_one)
      (fun k => hmeas _ (by exact_mod_cast Q54c.isCk_realMode k 2))
  exact Q54c.measurable_uncurry_rho ρt (fun r => hρc _ (Q54c.clampT_mem hT r)) hpt


theorem gfb2_energy_meas (S : GeneralSetup d) (M : Matrix (Fin d) (Fin d) ℝ) (hMF : S.MFHypM M) (N : ℕ) :
    Measurable fun p : ℝ × Config d N =>
      rieszEnergy d S.s p.2 (withDensityReal (S.ρ N (Q54c.clampT S.T p.1))) + oN d S.s S.C₀ N := by
  obtain ⟨hMFN, hReg⟩ := hMF N
  have hT : 0 ≤ S.T := S.hT.le
  have hd1 : 1 ≤ d := by have := S.hd; omega
  have hgm : Measurable (periodicRiesz d S.s) :=
    CoercAux.measurable_periodicRiesz_one hd1 S.hs0 S.hsd
  have hjm := gfb2_rho_meas S M hMF N
  set ρt : ℝ → Torus d → ℝ := fun r => S.ρ N (Q54c.clampT S.T r) with hρt
  have hprob : ∀ r, IsProbDensity (ρt r) := fun r => hMFN.density _ (Q54c.clampT_mem hT r)
  have hint : ∀ (r : ℝ) (f : Torus d → ℝ), ∫ y, f y ∂(withDensityReal (ρt r)) = ∫ y, ρt r y * f y :=
    fun r f => integral_withDensityReal_eq (ρt r) (hprob r).measurable (hprob r).nonneg f
  have hjm' : Measurable fun p : ℝ × Torus d => ρt p.1 p.2 := hjm
  unfold rieszEnergy modulatedEnergyKernel modulatedEnergy
  refine Measurable.add (Measurable.add (Measurable.sub ?_ ?_) ?_) measurable_const
  · refine measurable_const.mul (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_)
    exact hgm.comp (((measurable_pi_apply i).comp measurable_snd).sub ((measurable_pi_apply j).comp measurable_snd))
  · refine measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_)
    have e : (fun p : ℝ × Config d N => ∫ y, periodicRiesz d S.s (p.2 i - y) ∂(withDensityReal (ρt p.1))) =
        fun p => ∫ y, ρt p.1 y * periodicRiesz d S.s (p.2 i - y) := funext fun p => hint p.1 _
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


/-- Cauchy-Schwarz for a nonnegative extended function on `[0,T]`. -/
theorem gfb2_cs_lintegral {T : ℝ} (hT : 0 ≤ T) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ r in Set.Icc (0 : ℝ) T, f r) ^ 2 ≤ ENNReal.ofReal T * ∫⁻ r in Set.Icc (0 : ℝ) T, f r ^ 2 := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Set.Icc (0 : ℝ) T))
    Real.HolderConjugate.two_two (f := f) (g := fun _ => 1) hf.aemeasurable measurable_const.aemeasurable
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, Real.volume_Icc, sub_zero, one_mul] at h
  have h2 : (∫⁻ r in Set.Icc (0 : ℝ) T, f r) ^ 2 ≤
      ((∫⁻ r in Set.Icc (0 : ℝ) T, f r ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) * (ENNReal.ofReal T) ^ (1 / (2 : ℝ))) ^ 2 :=
    pow_le_pow_left' h 2
  refine h2.trans (le_of_eq ?_)
  rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast (ENNReal.ofReal T ^ (1 / (2 : ℝ))),
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
  simp only [Nat.cast_ofNat, ENNReal.rpow_two]
  norm_num
  rw [mul_comm]


/-- Time integral of a jointly measurable process whose one-time marginals are controlled. -/
theorem gfb2_time_integral {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 ≤ T) (F : ℝ → Ω → ℝ) (hFm : Measurable fun p : ℝ × Ω => F p.1 p.2)
    (hnn : ∀ᵐ ω ∂P, ∀ r ∈ Set.Icc (0 : ℝ) T, 0 ≤ F r ω)
    (hint : ∀ r ∈ Set.Icc (0 : ℝ) T, Integrable (F r) P) (E1 : ℝ)
    (hE1 : ∀ r ∈ Set.Icc (0 : ℝ) T, ∫ ω, F r ω ∂P ≤ E1) :
    (∀ᵐ ω ∂P, IntegrableOn (fun r => F r ω) (Set.Icc (0 : ℝ) T)) ∧
    ∫⁻ ω, ENNReal.ofReal (∫ r in Set.Icc (0 : ℝ) T, F r ω) ∂P ≤ ENNReal.ofReal (T * E1) ∧
    AEMeasurable (fun ω => ∫ r in Set.Icc (0 : ℝ) T, F r ω) P := by
  have hnn_r : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P, 0 ≤ F r ω := fun r hr => by
    filter_upwards [hnn] with ω hω using hω r hr
  have hmeasF : ∀ ω, Measurable fun r => F r ω := fun ω => hFm.comp measurable_prodMk_right
  have hjm : Measurable fun q : ℝ × Ω => ENNReal.ofReal (F q.1 q.2) := ENNReal.measurable_ofReal.comp hFm
  -- Tonelli
  have hswap : ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (F r ω)) ∂P =
      ∫⁻ r in Set.Icc (0 : ℝ) T, (∫⁻ ω, ENNReal.ofReal (F r ω) ∂P) := by
    rw [lintegral_lintegral_swap]
    exact (hjm.comp measurable_swap).aemeasurable
  have hinner : ∀ r ∈ Set.Icc (0 : ℝ) T, ∫⁻ ω, ENNReal.ofReal (F r ω) ∂P ≤ ENNReal.ofReal E1 := by
    intro r hr
    rw [← ofReal_integral_eq_lintegral_ofReal (hint r hr) (hnn_r r hr)]
    exact ENNReal.ofReal_le_ofReal (hE1 r hr)
  have hbound : ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (F r ω)) ∂P ≤ ENNReal.ofReal (T * E1) := by
    rw [hswap]
    calc ∫⁻ r in Set.Icc (0 : ℝ) T, (∫⁻ ω, ENNReal.ofReal (F r ω) ∂P)
        ≤ ∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal E1 := by
          refine setLIntegral_mono' measurableSet_Icc fun r hr => hinner r hr
      _ = ENNReal.ofReal (T * E1) := by
          rw [setLIntegral_const, Real.volume_Icc, sub_zero, ENNReal.ofReal_mul hT, mul_comm]
  have hle : ∀ᵐ ω ∂P, ENNReal.ofReal (∫ r in Set.Icc (0 : ℝ) T, F r ω) ≤
      ∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (F r ω) := by
    filter_upwards [hnn] with ω hω
    by_cases hi : IntegrableOn (fun r => F r ω) (Set.Icc (0 : ℝ) T)
    · rw [ofReal_integral_eq_lintegral_ofReal hi]
      exact (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun r hr => hω r hr)
    · rw [integral_undef hi]; simp
  have hmeasL : Measurable fun ω => ∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (F r ω) :=
    (hjm.comp measurable_swap).lintegral_prod_right'
  have hfin : ∀ᵐ ω ∂P, ∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (F r ω) < ⊤ := by
    refine ae_lt_top hmeasL (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound)
  refine ⟨?_, (lintegral_mono_ae hle).trans hbound, ?_⟩
  · filter_upwards [hfin, hnn] with ω hω hω'
    refine ⟨(hmeasF ω).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    refine lt_of_le_of_lt (le_of_eq ?_) hω
    refine setLIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    rw [← ofReal_norm_eq_enorm, Real.norm_of_nonneg (hω' r hr)]
  · have : StronglyMeasurable (fun q : Ω × ℝ => F q.2 q.1) := (hFm.comp measurable_swap).stronglyMeasurable
    exact (this.integral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) T))).measurable.aemeasurable


theorem gfb2_time_L2 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 ≤ T) (F : ℝ → Ω → ℝ) (hFm : Measurable fun p : ℝ × Ω => F p.1 p.2)
    (hnn : ∀ᵐ ω ∂P, ∀ r ∈ Set.Icc (0 : ℝ) T, 0 ≤ F r ω) (E2 : ℝ) (hE2n : 0 ≤ E2)
    (hE2 : ∀ r ∈ Set.Icc (0 : ℝ) T, ∫⁻ ω, ENNReal.ofReal (F r ω) ^ 2 ∂P ≤ ENNReal.ofReal (E2 ^ 2)) :
    (∫⁻ ω, ENNReal.ofReal (∫ r in Set.Icc (0 : ℝ) T, F r ω) ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (T * E2) := by
  have hmeasF : ∀ ω, Measurable fun r => F r ω := fun ω => hFm.comp measurable_prodMk_right
  have hjm : Measurable fun q : ℝ × Ω => ENNReal.ofReal (F q.1 q.2) := ENNReal.measurable_ofReal.comp hFm
  have hjm2 : Measurable fun q : ℝ × Ω => ENNReal.ofReal (F q.1 q.2) ^ 2 := hjm.pow_const 2
  have hle : ∀ᵐ ω ∂P, ENNReal.ofReal (∫ r in Set.Icc (0 : ℝ) T, F r ω) ^ 2 ≤
      ENNReal.ofReal T * ∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (F r ω) ^ 2 := by
    filter_upwards [hnn] with ω hω
    have h1 : ENNReal.ofReal (∫ r in Set.Icc (0 : ℝ) T, F r ω) ≤
        ∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (F r ω) := by
      by_cases hi : IntegrableOn (fun r => F r ω) (Set.Icc (0 : ℝ) T)
      · rw [ofReal_integral_eq_lintegral_ofReal hi]
        exact (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun r hr => hω r hr)
      · rw [integral_undef hi]; simp
    exact (pow_le_pow_left' h1 2).trans (gfb2_cs_lintegral hT (ENNReal.measurable_ofReal.comp (hmeasF ω)))
  have hswap : ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (F r ω) ^ 2) ∂P =
      ∫⁻ r in Set.Icc (0 : ℝ) T, (∫⁻ ω, ENNReal.ofReal (F r ω) ^ 2 ∂P) := by
    rw [lintegral_lintegral_swap]
    exact (hjm2.comp measurable_swap).aemeasurable
  have hmain : ∫⁻ ω, ENNReal.ofReal (∫ r in Set.Icc (0 : ℝ) T, F r ω) ^ 2 ∂P ≤
      ENNReal.ofReal (T * E2) ^ 2 := by
    calc ∫⁻ ω, ENNReal.ofReal (∫ r in Set.Icc (0 : ℝ) T, F r ω) ^ 2 ∂P
        ≤ ∫⁻ ω, ENNReal.ofReal T * (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (F r ω) ^ 2) ∂P :=
          lintegral_mono_ae hle
      _ = ENNReal.ofReal T * ∫⁻ r in Set.Icc (0 : ℝ) T, (∫⁻ ω, ENNReal.ofReal (F r ω) ^ 2 ∂P) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hswap]
      _ ≤ ENNReal.ofReal T * ∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (E2 ^ 2) := by
          exact mul_le_mul_right (setLIntegral_mono' measurableSet_Icc fun r hr => hE2 r hr) _
      _ = ENNReal.ofReal (T * E2) ^ 2 := by
          rw [setLIntegral_const, Real.volume_Icc, sub_zero, ← ENNReal.ofReal_pow (mul_nonneg hT hE2n),
            ← ENNReal.ofReal_mul (sq_nonneg E2), ← ENNReal.ofReal_mul hT]
          congr 1; ring
  calc (∫⁻ ω, ENNReal.ofReal (∫ r in Set.Icc (0 : ℝ) T, F r ω) ^ 2 ∂P) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal (T * E2) ^ 2) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow hmain (by norm_num)
    _ = ENNReal.ofReal (T * E2) := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num


/-- Joint measurability of a progressive configuration process, after clamping time to `[0,T]`. -/
theorem gfb2_progressive_meas {N : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℝ mΩ)
    (X : ℝ≥0 → Ω → Config d N) (hprog : IsProgressive ℱ (ofNNRealTime X)) {T : ℝ} (hT : 0 ≤ T) :
    Measurable fun p : ℝ × Ω => X (Real.toNNReal (Q54c.clampT T p.1)) p.2 := by
  have h1 := hprog T
  have hle : (Subtype.instMeasurableSpace (α := ℝ) (p := (· ∈ Set.Iic T))).prod (ℱ T) ≤
      (Subtype.instMeasurableSpace (α := ℝ) (p := (· ∈ Set.Iic T))).prod mΩ :=
    sup_le_sup le_rfl (MeasurableSpace.comap_mono (ℱ.le T))
  have h2 : Measurable fun p : Set.Iic T × Ω => ofNNRealTime X p.1 p.2 := h1.mono hle le_rfl
  have h3 : Measurable fun p : ℝ × Ω => ((⟨Q54c.clampT T p.1, (Q54c.clampT_mem hT p.1).2⟩ : Set.Iic T), p.2) :=
    (((Q54c.continuous_clampT T).measurable.comp measurable_fst).subtype_mk).prodMk measurable_snd
  exact h2.comp h3

theorem gf_energy_integral_moment_proof (S : GeneralSetup d) (M : Matrix (Fin d) (Fin d) ℝ) (hMF : S.MFHypM M) (N : ℕ)
    (hN : 2 ≤ N)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hX : IsStrongSolution P (S.dynM M N) S.T X₀ W X)
    (hF : ∃ (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X)
    (hE : S.EnergyMomentFinite P N X) :
    (∀ᵐ ω ∂P, ∀ r ∈ Set.Icc (0 : ℝ) S.T, 0 ≤ S.energyCompletion N (X (Real.toNNReal r) ω) r) ∧
    (∀ᵐ ω ∂P, IntegrableOn (fun r => S.energyCompletion N (X (Real.toNNReal r) ω) r) (Set.Icc (0 : ℝ) S.T)) ∧
    ∫⁻ ω, ENNReal.ofReal (∫ r in Set.Icc (0 : ℝ) S.T, S.energyCompletion N (X (Real.toNNReal r) ω) r) ∂P ≤
      ENNReal.ofReal (S.T * S.energyMoment P N X) ∧
    (S.EnergyMoment2Finite P N X →
      (∫⁻ ω, ENNReal.ofReal (∫ r in Set.Icc (0 : ℝ) S.T,
        S.energyCompletion N (X (Real.toNNReal r) ω) r) ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (S.T * S.energyMoment2 P N X)) ∧
    AEMeasurable (fun ω => ∫ r in Set.Icc (0 : ℝ) S.T, S.energyCompletion N (X (Real.toNNReal r) ω) r) P := by
  obtain ⟨ℱ, W', hFil⟩ := hF
  have hT : 0 ≤ S.T := S.hT.le
  have hnn : ∀ᵐ ω ∂P, ∀ r ∈ Set.Icc (0 : ℝ) S.T, 0 ≤ S.energyCompletion N (X (Real.toNNReal r) ω) r := by
    filter_upwards [hX.no_collision] with ω hω r hr
    refine S.energy_nonneg N hN r hr _ (hω (Real.toNNReal r) ?_)
    rw [Real.coe_toNNReal r hr.1]; exact hr.2
  set Gc : ℝ → Ω → ℝ := fun r ω =>
    rieszEnergy d S.s (X (Real.toNNReal (Q54c.clampT S.T r)) ω) (withDensityReal (S.ρ N (Q54c.clampT S.T r))) +
      oN d S.s S.C₀ N with hGc
  have hGm : Measurable fun p : ℝ × Ω => Gc p.1 p.2 := by
    have hZ := gfb2_progressive_meas ℱ X hFil.progressive hT
    have h := (gfb2_energy_meas S M hMF N).comp (measurable_fst.prodMk hZ)
    exact h
  have hEq : ∀ r ∈ Set.Icc (0 : ℝ) S.T, ∀ ω, S.energyCompletion N (X (Real.toNNReal r) ω) r = Gc r ω := by
    intro r hr ω
    simp only [hGc, Q54c.clampT_of_mem hr]
    rfl
  have hI : ∀ ω, ∫ r in Set.Icc (0 : ℝ) S.T, S.energyCompletion N (X (Real.toNNReal r) ω) r =
      ∫ r in Set.Icc (0 : ℝ) S.T, Gc r ω := fun ω =>
    setIntegral_congr_fun measurableSet_Icc fun r hr => hEq r hr ω
  have hfun : ∀ r ∈ Set.Icc (0 : ℝ) S.T, (fun ω => S.energyCompletion N (X (Real.toNNReal r) ω) r) = Gc r :=
    fun r hr => funext fun ω => hEq r hr ω
  have hnnG : ∀ᵐ ω ∂P, ∀ r ∈ Set.Icc (0 : ℝ) S.T, 0 ≤ Gc r ω := by
    filter_upwards [hnn] with ω hω r hr
    rw [← hEq r hr ω]; exact hω r hr
  have hintG : ∀ r ∈ Set.Icc (0 : ℝ) S.T, Integrable (Gc r) P := fun r hr => by
    rw [← hfun r hr]; exact hE.1 r hr
  have hE1 : ∀ r ∈ Set.Icc (0 : ℝ) S.T, ∫ ω, Gc r ω ∂P ≤ S.energyMoment P N X := by
    intro r hr
    have := le_ciSup hE.2 (⟨r, hr⟩ : Set.Icc (0 : ℝ) S.T)
    rw [← hfun r hr]
    exact this
  obtain ⟨hA1, hA2, hA3⟩ := gfb2_time_integral P hT Gc hGm hnnG hintG _ hE1
  refine ⟨hnn, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hA1] with ω hω
    exact hω.congr_fun (fun r hr => (hEq r hr ω).symm) measurableSet_Icc
  · simpa only [hI] using hA2
  · intro hE2
    have hE2n : 0 ≤ S.energyMoment2 P N X := Real.iSup_nonneg fun t => Real.sqrt_nonneg _
    have key := gfb2_time_L2 P hT Gc hGm hnnG _ hE2n (fun r hr => by
      have hmem : MemLp (Gc r) 2 P := by rw [← hfun r hr]; exact hE2.1 r hr
      have hnr : ∀ᵐ ω ∂P, 0 ≤ Gc r ω := by
        filter_upwards [hnnG] with ω hω using hω r hr
      have h1 : ∫⁻ ω, ENNReal.ofReal (Gc r ω) ^ 2 ∂P = ENNReal.ofReal (∫ ω, Gc r ω ^ 2 ∂P) := by
        rw [ofReal_integral_eq_lintegral_ofReal hmem.integrable_sq
          (by filter_upwards with ω using sq_nonneg _)]
        refine lintegral_congr_ae ?_
        filter_upwards [hnr] with ω hω
        rw [ENNReal.ofReal_pow hω]
      rw [h1]
      refine ENNReal.ofReal_le_ofReal ?_
      have h2 := le_ciSup hE2.2 (⟨r, hr⟩ : Set.Icc (0 : ℝ) S.T)
      have h3 : Real.sqrt (∫ ω, Gc r ω ^ 2 ∂P) ≤ S.energyMoment2 P N X := by
        have : (fun ω => (S.energyCompletion N (X (Real.toNNReal r) ω) r) ^ 2) = fun ω => Gc r ω ^ 2 := by
          funext ω; rw [hEq r hr ω]
        simp only [this] at h2
        exact h2
      exact (Real.sqrt_le_iff.1 h3).2)
    simpa only [hI] using key
  · simp only [hI]; exact hA3

example := (@gf_energy_integral_moment_proof : type_of% @HRS.GF.gf_energy_integral_moment)

end HRS.GF

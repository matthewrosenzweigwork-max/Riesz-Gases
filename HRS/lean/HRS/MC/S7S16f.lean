import HRS.MC.Sec7Vocab
import HRS.MC.SEdgeS16a
import HRS.MC.S7G0
import HRS.MC.S7S16b
import HRS.MC.S7S16c
import HRS.MC.S7S16d
import HRS.MC.S7S16e
import HRS.MC.S7S16fAux1
import HRS.MC.S7S16fAux3
import HRS.MC.S7S16fAux4
import HRS.MC.S7S16fAux5

/-!
# Packet `slow_correction` (Proposition 7.16): slow initial rates

Explicit construction (TeX L9628-9636), `eps = 1`:
* `G` the Gaussian of `G0` at `rho = 1`, `pi` the mode-pair map at a fixed nonzero frequency `k` (`S16d`);
* `f_N` = tilt of `Q_{N,beta}` by `theta_{a_N}(|pi eta_N|^2) = 1 + (1 + a_N) v(pi eta_N)`, `v(z) = exp(-|z|^2)`
  (`S16b`: probability, translation invariant, Haar first marginal; density `<= 2 + sup a`);
* `L` = tilt of `G` by `1 + v o pi`; weak convergence from the field CLT `S16a` (`G`-limits of `h`, `(v o pi) h`, `v o pi`);
* `Phi = v o pi in C_b^5`; `E_{f_N} Phi = fr(M_1(N), M_2(N), a_N)`, `L(Phi) = fr(m_1, m_2, 0)` with the ratio
  `fr` of `S16c` (slope `> 0` thanks to the full support of `pi_* G`, `S16f` Aux3) and `M_j(N) = m_j + O(N^{-1/2})` (`S16e`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S16f

open HRS HRS.Sec7 HRS.MC.SEdge HRS.MC.Sec7

variable {d : ℕ}

/-- an integral of a function with values in `[0,1]` against a probability measure lies in `[0,1]` -/
theorem s16f_int_mem_unit {γ : Type*} [MeasurableSpace γ] (Q : Measure γ) [IsProbabilityMeasure Q]
    {F : γ → ℝ} (hFm : Measurable F) (h0 : ∀ x, 0 ≤ F x) (h1 : ∀ x, F x ≤ 1) :
    0 ≤ ∫ x, F x ∂Q ∧ ∫ x, F x ∂Q ≤ 1 := by
  have hi : Integrable F Q := Integrable.of_bound hFm.aestronglyMeasurable 1
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (h0 x)]; exact h1 x)
  refine ⟨integral_nonneg h0, ?_⟩
  calc ∫ x, F x ∂Q ≤ ∫ _, (1 : ℝ) ∂Q := integral_mono hi (integrable_const _) h1
    _ = 1 := by simp

theorem slow_correction_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (β : ℝ)
    (hβ : 0 < β) (m : ℝ) (hm : (d : ℝ) / 2 < m) (a : ℕ → ℝ) (ha_pos : ∀ N, 0 < a N)
    (ha0 : Tendsto a atTop (𝓝 0)) (ha : Tendsto (fun N : ℕ => Real.sqrt N * a N) atTop atTop) :
    ∃ (f : ∀ N : ℕ, Measure (Config d N)) (L : Measure (NegSobolev d m))
      (Φ : NegSobolev d m → ℝ) (c : ℝ),
      (∀ N, IsProbabilityMeasure (f N)) ∧ IsProbabilityMeasure L ∧
      (∀ N, ∀ b : Torus d, (f N).map (fun X i => X i + b) = f N) ∧
      (∃ B : ℝ, ∀ N, f N ≪ modulatedGibbs (periodicRiesz d s) N β volume ∧
        ∀ᵐ X ∂(modulatedGibbs (periodicRiesz d s) N β volume),
          (f N).rnDeriv (modulatedGibbs (periodicRiesz d s) N β volume) X ≤ ENNReal.ofReal B) ∧
      (∀ N, 1 ≤ N → firstMarginal (f N) = volume) ∧
      (∀ G : NegSobolev d m → ℝ, Continuous G → (∃ M, ∀ x, |G x| ≤ M) →
        Tendsto (fun N : ℕ => ∫ X, G (etaE m X volume) ∂(f N)) atTop (𝓝 (∫ y, G y ∂L))) ∧
      MemCb 5 Φ ∧ 0 < c ∧
      ∃ N₀ : ℕ, ∀ N ≥ N₀, c * a N ≤ |∫ X, Φ (etaE m X volume) ∂(f N) - ∫ y, Φ y ∂L| := by
  -- the Gaussian, the frequency, the mode-pair map
  obtain ⟨G, hGp, hG⟩ := HRS.MC.Sec7.G0.s7_G0_gaussian_exists_proof hd hs0 hs m hm β hβ.le
    (fun _ : Torus d => (1 : ℝ)) HRS.MC.SEdge.S16a.s16a_smoothPos
  rw [HRS.MC.SEdge.S16a.s16a_wdr_one] at hG
  haveI := hGp
  obtain ⟨k, -⟩ : ∃ k : NonzeroLattice d, True :=
    ⟨⟨Pi.single (⟨0, by omega⟩ : Fin d) (1 : ℤ), fun h => by
      have := congrFun h ⟨0, by omega⟩; simp at this⟩, trivial⟩
  obtain ⟨π, hπ, -⟩ := HRS.MC.Sec7.S16d.s7_S16d_modePair_clm_proof d m k
  obtain ⟨hGauss, hfull⟩ := s16f_fullSupport hd hs0 hs hβ m hm G hG k π hπ
  haveI : IsProbabilityMeasure (G.map π) :=
    (Measure.isProbabilityMeasure_map_iff π.continuous.aemeasurable).2 hGp
  have hΦπ : ∀ y, s16f_Φ m k y = Real.exp (-‖π y‖ ^ 2) := fun y => by
    simp [s16f_Φ, s16f_v, hπ]
  -- the scalar data
  have hS := HRS.MC.Sec7.S16c.s7_S16c_ratio_slope_proof (G.map π) hGauss hfull 1 one_pos
  dsimp only at hS
  have hm1 : (∫ z, Real.exp (-‖z‖ ^ 2) ∂(G.map π)) = ∫ y, s16f_Φ m k y ∂G := by
    rw [integral_map (f := fun z : EuclideanSpace ℝ (Fin 2) => Real.exp (-‖z‖ ^ 2))
      π.continuous.aemeasurable (by fun_prop : Continuous fun z : EuclideanSpace ℝ (Fin 2) =>
        Real.exp (-‖z‖ ^ 2)).aestronglyMeasurable]
    simp only [hΦπ]
  have hm2 : (∫ z, Real.exp (-‖z‖ ^ 2) ^ 2 ∂(G.map π)) = ∫ y, s16f_Φ m k y ^ 2 ∂G := by
    rw [integral_map (f := fun z : EuclideanSpace ℝ (Fin 2) => Real.exp (-‖z‖ ^ 2) ^ 2)
      π.continuous.aemeasurable (by fun_prop : Continuous fun z : EuclideanSpace ℝ (Fin 2) =>
        Real.exp (-‖z‖ ^ 2) ^ 2).aestronglyMeasurable]
    simp only [hΦπ]
  rw [hm1, hm2] at hS
  obtain ⟨hvar, c, a₀, C, hc, ha₀, hC, hslope, hlip⟩ := hS
  set m₁ : ℝ := ∫ y, s16f_Φ m k y ∂G with hm₁
  set m₂ : ℝ := ∫ y, s16f_Φ m k y ^ 2 ∂G with hm₂
  have hΦc := s16f_Φ_cont m k
  have hΦm : Measurable (s16f_Φ m k) := hΦc.measurable
  have hGΦ := s16f_int_mem_unit G hΦm (fun y => (s16f_Φ_pos m k y).le) (s16f_Φ_le_one m k)
  -- the bound on `a`
  obtain ⟨A, hA⟩ : ∃ A, ∀ N, a N ≤ A := by
    obtain ⟨A, hA⟩ := ha0.bddAbove_range
    exact ⟨A, fun N => hA ⟨N, rfl⟩⟩
  -- the tilted law of the limit
  have hg1 : ∀ y, 1 ≤ 1 + s16f_Φ m k y := fun y => by linarith [s16f_Φ_pos m k y]
  have hg2 : ∀ y, 1 + s16f_Φ m k y ≤ 2 := fun y => by linarith [s16f_Φ_le_one m k y]
  have hgm : Measurable (fun y => 1 + s16f_Φ m k y) := measurable_const.add hΦm
  have hΦi : Integrable (s16f_Φ m k) G := Integrable.of_bound hΦm.aestronglyMeasurable 1
    (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_of_pos (s16f_Φ_pos m k y)]; exact s16f_Φ_le_one m k y)
  have hint_g : ∫ y, (1 + s16f_Φ m k y) ∂G = 1 + m₁ := by
    rw [integral_add (integrable_const _) hΦi]; simp [hm₁]
  have hSq : Integrable (fun y => s16f_Φ m k y ^ 2) G :=
    Integrable.of_bound (hΦm.pow_const 2).aestronglyMeasurable 1 (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [s16f_Φ_pos m k y, s16f_Φ_le_one m k y])
  have hLΦ : ∫ y, s16f_Φ m k y ∂(s16f_tilt G fun y => 1 + s16f_Φ m k y) =
      (m₁ + (1 + 0) * m₂) / (1 + (1 + 0) * m₁) := by
    rw [s16f_tilt_integral G hgm hg1 hg2 hΦi, hint_g]
    have : ∫ y, (1 + s16f_Φ m k y) * s16f_Φ m k y ∂G = m₁ + m₂ := by
      have e : ∀ y, (1 + s16f_Φ m k y) * s16f_Φ m k y = s16f_Φ m k y + s16f_Φ m k y ^ 2 :=
        fun y => by ring
      simp_rw [e]
      rw [integral_add hΦi hSq]
    rw [this]; ring_nf
  -- S16e for the two observables
  obtain ⟨C₁, hC₁⟩ := HRS.MC.Sec7.S16e.s7_S16e_edge_two_observables_proof hd hs0 hs hβ m hm G hG k
    (w := s16f_v) s16f_memCb_v
  obtain ⟨C₂, hC₂⟩ := HRS.MC.Sec7.S16e.s7_S16e_edge_two_observables_proof hd hs0 hs hβ m hm G hG k
    (w := fun z => s16f_v z ^ 2) s16f_memCb_v_sq
  refine ⟨fun N => s7_tiltedLaw d s β N m k (s16f_θ (a N)), s16f_tilt G fun y => 1 + s16f_Φ m k y,
    s16f_Φ m k, c, ?_, ?_, ?_, ?_, ?_, ?_, s16f_memCb_Φ m k, hc, ?_⟩
  · intro N
    exact (HRS.MC.Sec7.S16b.s7_S16b_tilt_invariance_proof hd hs0 hs hβ m hm k (s16f_θ (a N))
      (s16f_θ_meas _) (s16f_θ_ge (ha_pos N).le) ⟨2 + a N, s16f_θ_le (ha_pos N).le⟩ N).1
  · exact s16f_tilt_isProb G hg1 hg2
  · intro N b
    exact (HRS.MC.Sec7.S16b.s7_S16b_tilt_invariance_proof hd hs0 hs hβ m hm k (s16f_θ (a N))
      (s16f_θ_meas _) (s16f_θ_ge (ha_pos N).le) ⟨2 + a N, s16f_θ_le (ha_pos N).le⟩ N).2.1 b
  · refine ⟨2 + A, fun N => ?_⟩
    obtain ⟨h1, h2⟩ := s16f_rn hd hs0 hs hβ m hm k (ha_pos N).le N
    refine ⟨h1, ?_⟩
    filter_upwards [h2] with X hX
    exact hX.trans (ENNReal.ofReal_le_ofReal (by linarith [hA N]))
  · intro N hN
    exact (HRS.MC.Sec7.S16b.s7_S16b_tilt_invariance_proof hd hs0 hs hβ m hm k (s16f_θ (a N))
      (s16f_θ_meas _) (s16f_θ_ge (ha_pos N).le) ⟨2 + a N, s16f_θ_le (ha_pos N).le⟩ N).2.2 hN
  · -- weak convergence
    intro h hhc ⟨M, hM⟩
    have hclt := HRS.MC.SEdge.S16a.sed_S16a_field_clt_proof hd hs0 hs hβ m hm G hG
    have tA := hclt h hhc ⟨M, hM⟩
    have tB := hclt (fun y => s16f_Φ m k y * h y) (hΦc.mul hhc) ⟨M, fun y => by
      rw [abs_mul, abs_of_pos (s16f_Φ_pos m k y)]
      calc s16f_Φ m k y * |h y| ≤ 1 * M :=
            mul_le_mul (s16f_Φ_le_one m k y) (hM y) (abs_nonneg _) zero_le_one
        _ = M := one_mul M⟩
    have tD := hclt (s16f_Φ m k) hΦc ⟨1, fun y => by
      rw [abs_of_pos (s16f_Φ_pos m k y)]; exact s16f_Φ_le_one m k y⟩
    have h1a : Tendsto (fun N => 1 + a N) atTop (𝓝 (1 + 0)) := tendsto_const_nhds.add ha0
    have hden : (1 + (1 + 0) * ∫ y, s16f_Φ m k y ∂G) ≠ 0 := by
      have : 0 ≤ ∫ y, s16f_Φ m k y ∂G := hGΦ.1
      linarith
    have hlim := (tA.add (h1a.mul tB)).div (tendsto_const_nhds.add (h1a.mul tD)) hden
    -- the right-hand side
    have hhi : Integrable h G := Integrable.of_bound hhc.measurable.aestronglyMeasurable M
      (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hM y)
    have hΦhi : Integrable (fun y => s16f_Φ m k y * h y) G :=
      Integrable.of_bound (hΦm.mul hhc.measurable).aestronglyMeasurable M (ae_of_all _ fun y => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (s16f_Φ_pos m k y)]
        calc s16f_Φ m k y * |h y| ≤ 1 * M :=
              mul_le_mul (s16f_Φ_le_one m k y) (hM y) (abs_nonneg _) zero_le_one
          _ = M := one_mul M)
    have hrhs : ∫ y, h y ∂(s16f_tilt G fun y => 1 + s16f_Φ m k y) =
        ((∫ y, h y ∂G) + (1 + 0) * ∫ y, s16f_Φ m k y * h y ∂G) /
          (1 + (1 + 0) * ∫ y, s16f_Φ m k y ∂G) := by
      rw [s16f_tilt_integral G hgm hg1 hg2 hhi, hint_g]
      have e : ∀ y, (1 + s16f_Φ m k y) * h y = h y + s16f_Φ m k y * h y := fun y => by ring
      simp_rw [e]
      rw [integral_add hhi hΦhi]
      simp [hm₁]
    rw [hrhs]
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (s16f_int_f hd hs0 hs hβ m hm k (ha_pos N).le hN hhc hM).symm
  · -- the quantitative lower bound
    have hev1 : ∀ᶠ N : ℕ in atTop, a N < min a₀ 1 := ha0.eventually (gt_mem_nhds (lt_min ha₀ one_pos))
    set C' : ℝ := C * (|C₁| + |C₂|) with hC'
    have hev2 : ∀ᶠ N : ℕ in atTop, C' / c ≤ Real.sqrt N * a N := ha.eventually_ge_atTop _
    obtain ⟨N₀, hN₀⟩ := (((eventually_ge_atTop 1).and hev1).and hev2).exists_forall_of_atTop
    refine ⟨N₀, fun N hN => ?_⟩
    obtain ⟨⟨hN1, haN⟩, hsq⟩ := hN₀ N hN
    have hapos := ha_pos N
    have haa0 : a N < a₀ := lt_of_lt_of_le haN (min_le_left _ _)
    have haa1 : a N ≤ 1 := (lt_of_lt_of_le haN (min_le_right _ _)).le
    have hNpos : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN1)
    haveI := s16f_Q_prob hd hs0 hs hβ N
    set Q := modulatedGibbs (periodicRiesz d s) N β (volume : Measure (Torus d)) with hQ
    have hηm := s16f_meas_eta hd hs0 hs hβ m hm hN1
    have hΦη : Measurable (fun X : Config d N => s16f_Φ m k (etaE m X volume)) := hΦm.comp hηm
    -- the two moments
    set M₁ : ℝ := ∫ X, s16f_Φ m k (etaE m X volume) ∂Q with hM₁
    set M₂ : ℝ := ∫ X, s16f_Φ m k (etaE m X volume) ^ 2 ∂Q with hM₂
    have hM₁b := s16f_int_mem_unit Q hΦη (fun X => (s16f_Φ_pos m k _).le) (fun X => s16f_Φ_le_one m k _)
    have hM₂b := s16f_int_mem_unit Q (hΦη.pow_const 2) (fun X => sq_nonneg _) (fun X => by
      nlinarith [s16f_Φ_pos m k (etaE m X volume), s16f_Φ_le_one m k (etaE m X volume)])
    have hE : ∫ X, s16f_Φ m k (etaE m X volume) ∂(s7_tiltedLaw d s β N m k (s16f_θ (a N))) =
        (M₁ + (1 + a N) * M₂) / (1 + (1 + a N) * M₁) := by
      rw [s16f_int_f hd hs0 hs hβ m hm k hapos.le hN1 hΦc (K := 1) (fun y => by
        rw [abs_of_pos (s16f_Φ_pos m k y)]; exact s16f_Φ_le_one m k y)]
      simp only [← sq]
      rfl
    have d1 : |M₁ - m₁| ≤ C₁ / Real.sqrt N := by
      have := hC₁ N hN1
      have e : ∫ y, s16f_v (s7_modePair m k y) ∂G = m₁ := rfl
      rw [e] at this
      exact this
    have d2 : |M₂ - m₂| ≤ C₂ / Real.sqrt N := by
      have := hC₂ N hN1
      have e : ∫ y, s16f_v (s7_modePair m k y) ^ 2 ∂G = m₂ := rfl
      rw [e] at this
      exact this
    have hlip' := hlip M₁ M₂ (a N) hM₁b.1 hM₁b.2 hM₂b.1 hM₂b.2 hapos.le haa1
    have hsl := hslope (a N) hapos haa0
    rw [hE, hLΦ]
    have hsum : C * (|M₁ - m₁| + |M₂ - m₂|) ≤ C' / Real.sqrt N := by
      have : |M₁ - m₁| + |M₂ - m₂| ≤ (|C₁| + |C₂|) / Real.sqrt N := by
        rw [add_div]
        exact add_le_add (d1.trans (div_le_div_of_nonneg_right (le_abs_self _) hNpos.le))
          (d2.trans (div_le_div_of_nonneg_right (le_abs_self _) hNpos.le))
      calc C * (|M₁ - m₁| + |M₂ - m₂|) ≤ C * ((|C₁| + |C₂|) / Real.sqrt N) :=
            mul_le_mul_of_nonneg_left this hC.le
        _ = C' / Real.sqrt N := by rw [hC']; ring
    have hsq' : C' / Real.sqrt N ≤ c * a N := by
      rw [div_le_iff₀ hNpos]
      have := (div_le_iff₀ hc).1 hsq
      linarith
    refine le_trans ?_ (le_abs_self _)
    have := abs_le.1 hlip'
    linarith [this.1, this.2]

end HRS.MC.Sec7.S16f

end

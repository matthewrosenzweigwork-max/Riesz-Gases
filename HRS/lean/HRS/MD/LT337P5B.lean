import HRS.MD.LT337P5A

/-!
# Packet LT5 (chunk D), file B: measurability and bounds on `ε`-separated configurations

* `lt5_measurable_energy_clamp`: `(r, X) ↦ E_h(X, ρ_{r ∧ T})` is jointly measurable.
* `lt5_energy_bound_sep`: `|E_{g_n}(X, ρ)| ≤ B` for every `n`, every `ρ` (probability density, `|ρ| ≤ Λ`) and every
  `a`-separated `X` (uniform in `n`).
* `lt5_jfull_bound`: the pointwise drift `Jfull_{g_n}` is bounded by `B` for `n ≥ n₀`, `a`-separated `X`
  (`g336c1_comm_bound`, `g336c1_micro_bound`, `lt3_diffusion_bound_proof`, `main_alg`).
* `lt5_jfull_tendsto`: `Jfull_{g_n}(r, X) → ltDrift` for collision-free `X`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS HRS.PDE HRS.Uniform.Q54c HRS.KID HRS.MD.LT337Vocab

namespace HRS.MD.LT337P5

variable {d N : ℕ}

/-! ### Joint measurability of the energy -/

section Meas

variable {D : DynData d} {T Λ : ℝ} {ρ : ℝ → Torus d → ℝ}

theorem lt5_fK_clamp_cont (c : MFctx D T Λ ρ) {h : Torus d → ℝ} (hhc : Continuous h) (x : Torus d) :
    Continuous fun r : ℝ => fK h ρ (clampT T r) x := by
  have := c.weak_cont_clamp (ψ := psi h x) (hhc.comp (continuous_id.sub continuous_const))
  refine this.congr fun r => ?_
  unfold fK
  rw [pair_wDR (c.dens (clampT_mem c.hT r))]

theorem lt5_measurable_energy_clamp (c : MFctx D T Λ ρ) (hN : 0 < N) {h : Torus d → ℝ}
    (hsm : Torus.IsSmooth h) (hev : ∀ x, h (-x) = h x) :
    Measurable fun p : ℝ × Config d N =>
      modulatedEnergyKernel h p.2 (withDensityReal (ρ (clampT T p.1))) := by
  have hhc : Continuous h := isCk_continuous (isCk1_of_smooth hsm |>.of_le (by norm_num) : Torus.IsCk 0 h)
  have hfK : Measurable fun q : ℝ × Torus d => fK h ρ (clampT T q.1) q.2 :=
    measurable_uncurry_of_continuous_of_measurable
      (u := fun (r : ℝ) (x : Torus d) => fK h ρ (clampT T r) x)
      (fun x => lt5_fK_clamp_cont c hhc x)
      (fun r => (c.fK_cont hsm hev (clampT_mem c.hT r)).measurable)
  have hDg : Continuous fun r : ℝ => Dg h ρ (clampT T r) :=
    (c.continuousOn_Dg hsm hev).comp_continuous (continuous_clampT T) (fun r => clampT_mem c.hT r)
  have e : (fun p : ℝ × Config d N => modulatedEnergyKernel h p.2 (withDensityReal (ρ (clampT T p.1)))) =
      fun p => Fpp h p.2 - (N : ℝ)⁻¹ * ∑ i, fK h ρ (clampT T p.1) (p.2 i) +
        (1 / 2) * Dg h ρ (clampT T p.1) := by
    funext p
    rw [energy_eq hev hN, pair_empirical hN]
  rw [e]
  have m1 : Measurable fun p : ℝ × Config d N => Fpp h p.2 :=
    (measurable_Fpp hhc).comp measurable_snd
  have m2 : Measurable fun p : ℝ × Config d N => ∑ i, fK h ρ (clampT T p.1) (p.2 i) := by
    refine Finset.measurable_sum _ fun i _ => ?_
    have hxi : Measurable fun p : ℝ × Config d N => ((p.1, p.2 i) : ℝ × Torus d) :=
      measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)
    have := hfK.comp hxi
    simpa only [Function.comp_def] using this
  have m3 : Measurable fun p : ℝ × Config d N => Dg h ρ (clampT T p.1) :=
    by have h1 : Measurable fun p : ℝ × Config d N => p.1 := measurable_fst
       exact hDg.measurable.comp h1
  exact (m1.sub (m2.const_mul _)).add (m3.const_mul _)

end Meas

/-! ### Energy bound on separated configurations, uniform in `n` -/

section EnergyBound

/-- `∫ |g_M| ≤ K` uniformly in the level `M ≥ 0`. -/
theorem lt5_gReg_L1 (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ M : ℝ, 0 ≤ M → ∫ z : Torus d, |b15c_gReg d s M z| ≤ K := by
  obtain ⟨B, hB0, hB⟩ := movc_riesz_lower hd hs0 hsd
  have hgi : Integrable (periodicRiesz d s) := CoercAux.integrable_periodicRiesz_one hd hs0 hsd
  have hI0 : 0 ≤ ∫ z : Torus d, |periodicRiesz d s z| := integral_nonneg fun z => abs_nonneg _
  refine ⟨(∫ z : Torus d, |periodicRiesz d s z|) + B, by linarith, fun M hM => ?_⟩
  have hgc := movc_gReg_measurable hd hs0 hsd M
  have hgM : Integrable (b15c_gReg d s M) := hgc.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hz : (volume : Measure (Torus d)) {0} = 0 := volume_singleton_torus hd 0
  have hae : ∀ᵐ z : Torus d ∂volume, z ≠ 0 := by
    rw [ae_iff]; simpa using hz
  have : ∫ z : Torus d, |b15c_gReg d s M z| ≤ ∫ z : Torus d, (|periodicRiesz d s z| + B) := by
    refine integral_mono_ae hgM.abs (hgi.abs.add (integrable_const B)) ?_
    filter_upwards [hae] with z hz
    have h1 := b15c_gReg_le s M hz
    have h2 := b15c_gReg_ge s hB0 hM hB z
    show |b15c_gReg d s M z| ≤ |periodicRiesz d s z| + B
    rw [abs_le]
    constructor
    · linarith [abs_nonneg (periodicRiesz d s z)]
    · linarith [le_abs_self (periodicRiesz d s z)]
  rw [integral_add hgi.abs (integrable_const B)] at this
  simpa using this

theorem lt5_conv_bound (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (Λ : ℝ) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ M : ℝ, 0 ≤ M → ∀ f : Torus d → ℝ, (∀ y, |f y| ≤ Λ) → ∀ x,
      |convFun (b15c_gReg d s M) f x| ≤ Cb := by
  obtain ⟨K, hK0, hK⟩ := lt5_gReg_L1 hd hs0 hsd (d := d)
  refine ⟨|Λ| * K, by positivity, fun M hM f hf x => ?_⟩
  have hgM : Integrable (b15c_gReg d s M) := (movc_gReg_measurable hd hs0 hsd M).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hf' : ∀ y, |f y| ≤ |Λ| := fun y => (hf y).trans (le_abs_self Λ)
  refine (movc_conv_abs_le hgM hf' x).trans ?_
  exact mul_le_mul_of_nonneg_left (hK M hM) (abs_nonneg _)

theorem lt5_energy_bound_sep (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (Λ : ℝ) {a : ℝ}
    (ha : 0 < a) (hN : 0 < N) :
    ∃ B : ℝ, ∀ n : ℕ, ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ y, |ρ y| ≤ Λ) →
      ∀ X : Config d N, (∀ i j, i ≠ j → a ≤ ‖X i - X j‖) →
        |modulatedEnergyKernel (b15c_gReg d s (n : ℝ)) X (withDensityReal ρ)| ≤ B := by
  obtain ⟨Bl, hBl0, hBl⟩ := movc_riesz_lower hd hs0 hsd
  obtain ⟨U, hU⟩ := b15c_periodicRiesz_bddAbove_off_ball (s := s) hd hs0 hsd ha
  obtain ⟨Cb, hCb0, hCb⟩ := lt5_conv_bound hd hs0 hsd Λ
  set Gb : ℝ := max Bl U with hGb
  have hGb0 : 0 ≤ Gb := (le_max_left _ _).trans' hBl0
  refine ⟨Gb / 2 + Cb + Cb / 2, fun n ρ hρ hρΛ X hX => ?_⟩
  have hM : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  haveI := isProb_withDensityReal hρ
  rw [movc_energy_eq _ hρ.measurable hρ.nonneg]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  -- pair term
  have hpair : ∀ i j, i ≠ j → |b15c_gReg d s (n : ℝ) (X i - X j)| ≤ Gb := by
    intro i j hij
    have hz : X i - X j ≠ 0 := by
      intro h0
      have := hX i j hij
      rw [h0, norm_zero] at this
      linarith
    have h1 := b15c_gReg_le (d := d) s (n : ℝ) hz
    have h2 := b15c_gReg_ge s hBl0 hM hBl (X i - X j)
    have h3 : periodicRiesz d s (X i - X j) ≤ U :=
      hU _ ((hX i j hij).trans (KernelGrad.norm_le_tdist _))
    rw [abs_le]
    constructor
    · linarith [le_max_left Bl U]
    · linarith [le_max_right Bl U]
  have hP : |(1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, b15c_gReg d s (n : ℝ) (X i - X j)| ≤ Gb / 2 := by
    rw [abs_mul, abs_of_pos (by positivity)]
    have hs := g336c1_abs_sum_le (Finset.univ : Finset (Fin N))
      (fun i => ∑ j ∈ Finset.univ.erase i, b15c_gReg d s (n : ℝ) (X i - X j)) ((N : ℝ) * Gb) (fun i _ => by
        refine (g336c1_abs_sum_le _ _ Gb (fun j hj => hpair i j (Finset.mem_erase.mp hj).1.symm)).trans ?_
        refine mul_le_mul_of_nonneg_right ?_ hGb0
        have : (Finset.univ.erase i).card ≤ N := by
          simpa using Finset.card_erase_le (s := (Finset.univ : Finset (Fin N))) (a := i)
        exact_mod_cast this)
    simp only [Finset.card_univ, Fintype.card_fin] at hs
    calc 1 / (2 * (N : ℝ) ^ 2) * |∑ i, ∑ j ∈ Finset.univ.erase i, b15c_gReg d s (n : ℝ) (X i - X j)|
        ≤ 1 / (2 * (N : ℝ) ^ 2) * ((N : ℝ) * ((N : ℝ) * Gb)) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
      _ = Gb / 2 := by field_simp
  have hS : |(1 / (N : ℝ)) * ∑ i, convFun (b15c_gReg d s (n : ℝ)) ρ (X i)| ≤ Cb := by
    rw [abs_mul, abs_of_pos (by positivity)]
    have hs := g336c1_abs_sum_le (Finset.univ : Finset (Fin N))
      (fun i => convFun (b15c_gReg d s (n : ℝ)) ρ (X i)) Cb (fun i _ => hCb _ hM ρ hρΛ _)
    simp only [Finset.card_univ, Fintype.card_fin] at hs
    calc 1 / (N : ℝ) * |∑ i, convFun (b15c_gReg d s (n : ℝ)) ρ (X i)|
        ≤ 1 / (N : ℝ) * ((N : ℝ) * Cb) := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = Cb := by field_simp
  have hI : |(1 / 2 : ℝ) * ∫ x, convFun (b15c_gReg d s (n : ℝ)) ρ x ∂(withDensityReal ρ)| ≤ Cb / 2 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have := norm_integral_le_of_norm_le_const (μ := withDensityReal ρ) (C := Cb)
      (f := fun x => convFun (b15c_gReg d s (n : ℝ)) ρ x)
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hCb _ hM ρ hρΛ x)
    rw [Real.norm_eq_abs] at this
    simp at this
    linarith
  have h1 := abs_sub ((1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, b15c_gReg d s (n : ℝ) (X i - X j))
    ((1 / (N : ℝ)) * ∑ i, convFun (b15c_gReg d s (n : ℝ)) ρ (X i))
  have h2 := abs_add_le ((1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, b15c_gReg d s (n : ℝ) (X i - X j) -
    (1 / (N : ℝ)) * ∑ i, convFun (b15c_gReg d s (n : ℝ)) ρ (X i))
    ((1 / 2 : ℝ) * ∫ x, convFun (b15c_gReg d s (n : ℝ)) ρ x ∂(withDensityReal ρ))
  linarith

end EnergyBound

/-! ### The pointwise drift on separated configurations -/

section Drift

variable {D : DynData d} {T Λ : ℝ} {ρ : ℝ → Torus d → ℝ}

theorem lt5_not_collision {X : Config d N} {a : ℝ} (ha : 0 < a) (hX : ∀ i j, i ≠ j → a ≤ ‖X i - X j‖) :
    X ∉ collisionSet d N := by
  rintro ⟨i, j, hij, h⟩
  have := hX i j hij
  rw [h, sub_self, norm_zero] at this
  linarith

theorem lt5_jfull_bound (hd : 2 ≤ d) (c : MFctx D T Λ ρ) (hs : D.s = (d : ℝ) - 2)
    {L : ℝ} (hL0 : 0 ≤ L) (hLip : ∀ r ∈ Set.Icc (0 : ℝ) T, IsLipschitzVF L (meanFieldDrift D (ρ r)))
    {a : ℝ} (ha : 0 < a) (hN : 2 ≤ N) :
    ∃ (n₀ : ℕ) (B : ℝ), ∀ n : ℕ, n₀ ≤ n → ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ X : Config d N,
      (∀ i j, i ≠ j → a ≤ ‖X i - X j‖) →
      |ppDrift D (b15c_gReg d D.s (n : ℝ)) X - fDrift D (b15c_gReg d D.s (n : ℝ)) ρ r X +
          wkG D ρ (fK (b15c_gReg d D.s (n : ℝ)) ρ r) r| ≤ B := by
  have hd1 : 1 ≤ d := by omega
  have hN0 : 0 < N := by omega
  obtain ⟨C, hGk⟩ := KernelGradD1.goodKernel_periodicRieszGrad_of_one_le hd1 D.hs0 D.hsd
  obtain ⟨cM, hcM0, hcM⟩ := HRS.Duality.exists_matVec_bound D.M
  obtain ⟨n₀, B3, hB3⟩ := HRS.MD.LT337P3.lt3_diffusion_bound_proof hd Λ ha
  have hsm : ∀ n : ℕ, Torus.IsSmooth (b15c_gReg d D.s (n : ℝ)) := fun n =>
    b15c_gReg_isSmooth hd1 D.hs0 D.hsd _
  have hev : ∀ (n : ℕ) x, b15c_gReg d D.s (n : ℝ) (-x) = b15c_gReg d D.s (n : ℝ) x := fun n x =>
    b15c_gReg_neg D.s _ x
  have hGn : ∀ n : ℕ, KernelGrad.GoodKernel d D.s C (Torus.grad (b15c_gReg d D.s (n : ℝ))) := fun n =>
    g336c1_goodKernel_grad_gReg hd1 D.hs0 D.hsd hGk _
  refine ⟨n₀, (1 / 2) * g336c1_commB d D.s C L Λ a + g336c1_microB d cM D.s C Λ Λ a + |D.invβ| * B3,
    fun n hn r hr X hX => ?_⟩
  have hXc := lt5_not_collision ha hX
  rw [c.main_alg (hsm n) (hev n) hr hN0 X hXc]
  have hρΛ : ∀ x, ρ r x ≤ Λ := fun x => (le_abs_self _).trans (c.abs_le hr x)
  have hcm := g336c1_comm_bound hd1 (hGn n) hL0 (hLip r hr) (c.dens hr) hρΛ ha hN0 X hX
  have hmi := g336c1_micro_bound D hcM0 hcM (hGn n) hGk (c.cont hr).measurable
    (fun x => c.abs_le hr x) (c.lip hr) c.Λ_nonneg c.Λ_nonneg ha hN0 X hX
  have hdf : |offDiagDiffPairing (Torus.laplacian (b15c_gReg d D.s (n : ℝ))) X (withDensityReal (ρ r))| ≤ B3 := by
    rw [hs]
    exact hB3 n hn N hN0 (ρ r) (c.dens hr) (c.ck3 hr) (c.cb hr) X hX
  have h1 : |(1 / 2 : ℝ) * commQuantityWith (Torus.grad (b15c_gReg d D.s (n : ℝ))) (meanFieldDrift D (ρ r)) X
      (withDensityReal (ρ r))| ≤ (1 / 2) * g336c1_commB d D.s C L Λ a := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    exact mul_le_mul_of_nonneg_left hcm (by norm_num)
  have h3 : |D.invβ * offDiagDiffPairing (Torus.laplacian (b15c_gReg d D.s (n : ℝ))) X (withDensityReal (ρ r))|
      ≤ |D.invβ| * B3 := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hdf (abs_nonneg _)
  refine (abs_add_le _ _).trans ?_
  refine add_le_add ((abs_add_le _ _).trans (add_le_add h1 hmi)) h3

theorem lt5_jfull_tendsto (hd : 2 ≤ d) (c : MFctx D T Λ ρ) (hs : D.s = (d : ℝ) - 2)
    {L : ℝ} (hL0 : 0 ≤ L) (hLip : ∀ r ∈ Set.Icc (0 : ℝ) T, IsLipschitzVF L (meanFieldDrift D (ρ r)))
    (hN : 2 ≤ N) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) {X : Config d N} (hX : X ∉ collisionSet d N) :
    Tendsto (fun n : ℕ => ppDrift D (b15c_gReg d D.s (n : ℝ)) X -
        fDrift D (b15c_gReg d D.s (n : ℝ)) ρ r X +
        wkG D ρ (fK (b15c_gReg d D.s (n : ℝ)) ρ r) r) atTop (𝓝 (ltDrift D ρ r X)) := by
  have hd1 : 1 ≤ d := by omega
  have hN0 : 0 < N := by omega
  obtain ⟨C, hGk⟩ := KernelGradD1.goodKernel_periodicRieszGrad_of_one_le hd1 D.hs0 D.hsd
  have hsm : ∀ n : ℕ, Torus.IsSmooth (b15c_gReg d D.s (n : ℝ)) := fun n =>
    b15c_gReg_isSmooth hd1 D.hs0 D.hsd _
  have hev : ∀ (n : ℕ) x, b15c_gReg d D.s (n : ℝ) (-x) = b15c_gReg d D.s (n : ℝ) x := fun n x =>
    b15c_gReg_neg D.s _ x
  have hGn : ∀ n : ℕ, KernelGrad.GoodKernel d D.s C (Torus.grad (b15c_gReg d D.s (n : ℝ))) := fun n =>
    g336c1_goodKernel_grad_gReg hd1 D.hs0 D.hsd hGk _
  have hlim : ∀ z : Torus d, z ≠ 0 →
      Tendsto (fun n : ℕ => Torus.grad (b15c_gReg d D.s (n : ℝ)) z) atTop (𝓝 (periodicRieszGrad d D.s z)) :=
    fun z hz => g336c1_grad_gReg_tendsto hd1 D.hs0 D.hsd hz
  have hρΛ : ∀ x, ρ r x ≤ Λ := fun x => (le_abs_self _).trans (c.abs_le hr x)
  have e : ∀ n : ℕ, ppDrift D (b15c_gReg d D.s (n : ℝ)) X - fDrift D (b15c_gReg d D.s (n : ℝ)) ρ r X +
      wkG D ρ (fK (b15c_gReg d D.s (n : ℝ)) ρ r) r =
      (1 / 2) * commQuantityWith (Torus.grad (b15c_gReg d D.s (n : ℝ))) (meanFieldDrift D (ρ r)) X
        (withDensityReal (ρ r)) + microTerm D (b15c_gReg d D.s (n : ℝ)) (ρ r) X +
      D.invβ * offDiagDiffPairing (Torus.laplacian (b15c_gReg d D.s (n : ℝ))) X (withDensityReal (ρ r)) :=
    fun n => c.main_alg (hsm n) (hev n) hr hN0 X hX
  have h1 := g336c1_comm_tendsto hd1 hGn hGk hlim hL0 (hLip r hr) hρΛ X hX
  have h2 := g336c1_micro_tendsto D (hn := fun n : ℕ => b15c_gReg d D.s (n : ℝ)) hGn hGk hlim
    (c.cont hr).measurable (fun x => c.abs_le hr x) (c.lip hr) c.Λ_nonneg c.Λ_nonneg X hX
  have h3 : Tendsto (fun n : ℕ => offDiagDiffPairing (Torus.laplacian (b15c_gReg d D.s (n : ℝ))) X
      (withDensityReal (ρ r))) atTop (𝓝 (diffLimit d (ρ r) X)) := by
    rw [hs]
    exact HRS.MD.LT337P3.lt3_diffusion_limit_proof hd hN0 (c.dens hr) (c.ck3 hr |>.of_le (by norm_num)) hX
  simp only [e]
  exact ((h1.const_mul (1 / 2)).add h2).add (h3.const_mul _)

end Drift

end HRS.MD.LT337P5

import HRS.Energy.G336C1Aux4

/-!
# G336C1, helper file 5: the limit identity along the deterministic path

For the deterministic covering path `Y` (integrated ODE, `invβ = 0`), collision-free on `[0,T]`:
`F(t) - F(0) = ∫_0^t (½ Comm_g(u^r; x(r), ρ^r) + N⁻¹ ∑_i a_iᵀ M a_i) dr`
with `F = rieszEnergy` (the singular kernel), obtained from the identity at the level of the truncated kernels
`g_n = b15c_gReg d s n` by dominated convergence (`n → ∞`).
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d N : ℕ}

/-- The path in real time. -/
abbrev g336c1_x (Y : ℝ≥0 → Fin N → Euc d) (r : ℝ) : Config d N :=
  fun i => Torus.mk (Y (Real.toNNReal r) i)

/-- The zero-temperature ODE data of a covering path. -/
structure G336C1Path (D : DynData d) (T : ℝ) (Y : ℝ≥0 → Fin N → Euc d) : Prop where
  hint : ∀ t : ℝ≥0, (t : ℝ) ≤ T → ∀ i,
    IntegrableOn (fun s : ℝ => particleDrift D (fun j => Torus.mk (Y (Real.toNNReal s) j)) i)
      (Set.Icc 0 (t : ℝ))
  hy : ∀ t : ℝ≥0, (t : ℝ) ≤ T → ∀ i, Y t i = Y 0 i +
    ∫ s in Set.Icc (0 : ℝ) t, particleDrift D (fun j => Torus.mk (Y (Real.toNNReal s) j)) i
  hcont : ∀ i, Continuous fun t : ℝ≥0 => Torus.mk (Y t i)
  hcol : ∀ t : ℝ≥0, (t : ℝ) ≤ T → (fun i => Torus.mk (Y t i)) ∉ collisionSet d N

theorem g336c1_continuous_x {D : DynData d} {T : ℝ} {Y : ℝ≥0 → Fin N → Euc d}
    (hp : G336C1Path D T Y) : Continuous (g336c1_x Y) :=
  continuous_pi fun i => (hp.hcont i).comp continuous_real_toNNReal

theorem g336c1_x_not_collision {D : DynData d} {T : ℝ} {Y : ℝ≥0 → Fin N → Euc d}
    (hp : G336C1Path D T Y) {r : ℝ} (hr : r ∈ Set.Icc 0 T) : g336c1_x Y r ∉ collisionSet d N :=
  hp.hcol _ (by rw [Real.coe_toNNReal _ hr.1]; exact hr.2)

/-- A uniform lower bound for the pair separations along the path. -/
theorem g336c1_sep (hd : 1 ≤ d) {D : DynData d} {T : ℝ} {Y : ℝ≥0 → Fin N → Euc d}
    (hp : G336C1Path D T Y) :
    ∃ a : ℝ, 0 < a ∧ ∀ r ∈ Set.Icc 0 T, ∀ i j, i ≠ j → a ≤ ‖g336c1_x Y r i - g336c1_x Y r j‖ := by
  have hxc := g336c1_continuous_x hp
  have hK : IsCompact ((g336c1_x Y) '' Set.Icc 0 T) := isCompact_Icc.image hxc
  have hKd : Disjoint ((g336c1_x Y) '' Set.Icc 0 T) (collisionSet d N) := by
    rw [Set.disjoint_left]
    rintro X ⟨r, hr, rfl⟩
    exact g336c1_x_not_collision hp hr
  obtain ⟨r0, hr0, hsep⟩ := b15c_exists_sep_of_compact hK hKd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  refine ⟨2 * r0 / d, by positivity, fun r hr i j hij => ?_⟩
  have h1 := hsep _ ⟨r, hr, rfl⟩ i j hij
  have h2 : Torus.tdist (g336c1_x Y r i) (g336c1_x Y r j) ≤ d * ‖g336c1_x Y r i - g336c1_x Y r j‖ := by
    rw [← b15c_tdist_sub_zero]
    exact KernelGrad.tdist_le_mul_norm _
  rw [div_le_iff₀ hd0]
  linarith

open HRS.Uniform.Q54c in
theorem g336c1_micro_integrable (hd : 1 ≤ d) {D : DynData d} (hN : 2 ≤ N) (hV : Torus.IsCk 2 D.V)
    {T : ℝ} (hT : 0 ≤ T) {ρ : ℝ → Torus d → ℝ} {Λ : ℝ}
    (hmf : IsMeanFieldSolution D T ρ) (hreg : IsRegularMF 3 Λ T ρ)
    {Y : ℝ≥0 → Fin N → Euc d} (hp : G336C1Path D T Y) {C : ℝ}
    (hGk : KernelGrad.GoodKernel d D.s C (periodicRieszGrad d D.s))
    {h : Torus d → ℝ} (hsm : Torus.IsSmooth h) (hev : ∀ x, h (-x) = h x)
    (hGh : KernelGrad.GoodKernel d D.s C (Torus.grad h)) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    IntegrableOn (fun r : ℝ => microTerm D h (ρ r) (g336c1_x Y r)) (Set.Icc 0 t) := by
  have c : HRS.KID.MFctx D T Λ ρ := ⟨hd, hT, hV, hmf, hreg⟩
  have hN0 : 0 < N := by omega
  obtain ⟨a, ha, hsep⟩ := g336c1_sep hd hp
  obtain ⟨cM, hcM0, hcM⟩ := HRS.Duality.exists_matVec_bound D.M
  have hxc := g336c1_continuous_x hp
  have hm : Measurable fun r : ℝ => microTerm D h (ρ (clampT T r)) (g336c1_x Y r) := by
    have := (c.measurable_micro hsm hev).comp (measurable_id.prodMk hxc.measurable)
    simpa only [Function.comp_def, id_eq] using this
  have hae : (fun r : ℝ => microTerm D h (ρ (clampT T r)) (g336c1_x Y r)) =ᵐ[volume.restrict (Set.Icc 0 t)]
      fun r : ℝ => microTerm D h (ρ r) (g336c1_x Y r) := by
    refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun r hr => ?_)
    show microTerm D h (ρ (clampT T r)) (g336c1_x Y r) = microTerm D h (ρ r) (g336c1_x Y r)
    rw [clampT_of_mem ⟨hr.1, hr.2.trans ht.2⟩]
  refine Integrable.of_bound (hm.aestronglyMeasurable.congr hae)
    (g336c1_microB d cM D.s C Λ Λ a) ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun r hr => ?_)
  have hrT : r ∈ Set.Icc 0 T := ⟨hr.1, hr.2.trans ht.2⟩
  rw [Real.norm_eq_abs]
  exact g336c1_micro_bound D hcM0 hcM hGh hGk (c.cont hrT).measurable (fun x => c.abs_le hrT x)
    (c.lip hrT) c.Λ_nonneg c.Λ_nonneg ha hN0 _ (hsep r hrT)

/-- The integrand of the limit identity: `½ Comm_g(u^r; x(r), ρ^r) + N⁻¹ ∑_i a_iᵀ M a_i`. -/
def g336c1_f (D : DynData d) (ρ : ℝ → Torus d → ℝ) (Y : ℝ≥0 → Fin N → Euc d) (r : ℝ) : ℝ :=
  (1 / 2) * commQuantity d D.s (meanFieldDrift D (ρ r)) (g336c1_x Y r) (withDensityReal (ρ r)) +
    g336c1_microG D (ρ r) (g336c1_x Y r)

open HRS.Uniform.Q54c in
theorem g336c1_limit_identity (hd : 1 ≤ d) (D : DynData d) (hinvβ : D.invβ = 0) (hN : 2 ≤ N)
    (hV : Torus.IsCk 2 D.V) {T : ℝ} (hT : 0 ≤ T) {ρ : ℝ → Torus d → ℝ} {Λ : ℝ}
    (hmf : IsMeanFieldSolution D T ρ) (hreg : IsRegularMF 3 Λ T ρ)
    {L : ℝ} (hL0 : 0 ≤ L) (hLip : ∀ r ∈ Set.Icc 0 T, IsLipschitzVF L (meanFieldDrift D (ρ r)))
    {Y : ℝ≥0 → Fin N → Euc d} (hp : G336C1Path D T Y) :
    ∃ B : ℝ, AEStronglyMeasurable (g336c1_f D ρ Y) (volume.restrict (Set.Icc 0 T)) ∧
      (∀ r ∈ Set.Icc 0 T, |g336c1_f D ρ Y r| ≤ B) ∧
      ∀ t ∈ Set.Icc 0 T,
        rieszEnergy d D.s (g336c1_x Y t) (withDensityReal (ρ t)) -
          rieszEnergy d D.s (g336c1_x Y 0) (withDensityReal (ρ 0)) =
        ∫ r in Set.Icc 0 t, g336c1_f D ρ Y r := by
  obtain ⟨C, hGk⟩ := KernelGradD1.goodKernel_periodicRieszGrad_of_one_le hd D.hs0 D.hsd
  have c : HRS.KID.MFctx D T Λ ρ := ⟨hd, hT, hV, hmf, hreg⟩
  have hN0 : 0 < N := by omega
  obtain ⟨a, ha, hsep⟩ := g336c1_sep hd hp
  obtain ⟨cM, hcM0, hcM⟩ := HRS.Duality.exists_matVec_bound D.M
  set hn : ℕ → Torus d → ℝ := fun n => b15c_gReg d D.s (n : ℝ) with hhn
  have hsm : ∀ n, Torus.IsSmooth (hn n) := fun n => b15c_gReg_isSmooth hd D.hs0 D.hsd _
  have hev : ∀ n x, hn n (-x) = hn n x := fun n x => b15c_gReg_neg D.s _ x
  have hGn : ∀ n, KernelGrad.GoodKernel d D.s C (Torus.grad (hn n)) := fun n =>
    g336c1_goodKernel_grad_gReg hd D.hs0 D.hsd hGk _
  have hlim : ∀ z : Torus d, z ≠ 0 →
      Tendsto (fun n => Torus.grad (hn n) z) atTop (𝓝 (periodicRieszGrad d D.s z)) :=
    fun z hz => g336c1_grad_gReg_tendsto hd D.hs0 D.hsd hz
  set fn : ℕ → ℝ → ℝ := fun n r => (1 / 2) * commQuantityWith (Torus.grad (hn n)) (meanFieldDrift D (ρ r))
    (g336c1_x Y r) (withDensityReal (ρ r)) + microTerm D (hn n) (ρ r) (g336c1_x Y r) with hfn
  set B0 : ℝ := (1 / 2) * g336c1_commB d D.s C L Λ a + g336c1_microB d cM D.s C Λ Λ a with hB0
  have hρΛ : ∀ r ∈ Set.Icc 0 T, ∀ x, ρ r x ≤ Λ := fun r hr x => (le_abs_self _).trans (c.abs_le hr x)
  -- measurability of each `fn n` on `[0,T]`
  have hmeas : ∀ n, AEMeasurable (fn n) (volume.restrict (Set.Icc 0 T)) := fun n =>
    g336c1_integrand_measurable hd D hinvβ hN hV (hsm n) (hev n) hT hmf hreg Y hp.hint hp.hy hp.hcont hp.hcol
  -- pointwise limit
  have hlimf : ∀ r ∈ Set.Icc 0 T, Tendsto (fun n => fn n r) atTop (𝓝 (g336c1_f D ρ Y r)) := by
    intro r hr
    have hX := g336c1_x_not_collision hp hr
    have h1 := g336c1_comm_tendsto hd hGn hGk hlim hL0 (hLip r hr) (hρΛ r hr) (g336c1_x Y r) hX
    have h2 := g336c1_micro_tendsto D hGn hGk hlim (c.cont hr).measurable (fun x => c.abs_le hr x)
      (c.lip hr) c.Λ_nonneg c.Λ_nonneg (g336c1_x Y r) hX
    exact (h1.const_mul (1 / 2)).add h2
  -- uniform bound
  have hbd : ∀ n, ∀ r ∈ Set.Icc 0 T, |fn n r| ≤ B0 := by
    intro n r hr
    have hcm := g336c1_comm_bound hd (hGn n) hL0 (hLip r hr) (hmf.density r hr) (hρΛ r hr) ha hN0
      (g336c1_x Y r) (hsep r hr)
    have hmi := g336c1_micro_bound D hcM0 hcM (hGn n) hGk (c.cont hr).measurable
      (fun x => c.abs_le hr x) (c.lip hr) c.Λ_nonneg c.Λ_nonneg ha hN0 (g336c1_x Y r) (hsep r hr)
    simp only [hfn]
    calc |(1 / 2) * commQuantityWith (Torus.grad (hn n)) (meanFieldDrift D (ρ r)) (g336c1_x Y r)
          (withDensityReal (ρ r)) + microTerm D (hn n) (ρ r) (g336c1_x Y r)|
        ≤ |(1 / 2) * commQuantityWith (Torus.grad (hn n)) (meanFieldDrift D (ρ r)) (g336c1_x Y r)
          (withDensityReal (ρ r))| + |microTerm D (hn n) (ρ r) (g336c1_x Y r)| := abs_add_le _ _
      _ ≤ B0 := by
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          exact add_le_add (mul_le_mul_of_nonneg_left hcm (by norm_num)) hmi
  have hbdf : ∀ r ∈ Set.Icc 0 T, |g336c1_f D ρ Y r| ≤ B0 := by
    intro r hr
    exact le_of_tendsto_of_tendsto' (hlimf r hr).abs tendsto_const_nhds
      (fun n => hbd n r hr)
  refine ⟨B0, ?_, hbdf, ?_⟩
  · refine aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hmeas n).aestronglyMeasurable) ?_
    exact (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall hlimf)
  · intro t ht
    have e0 : g336c1_x Y 0 = fun i => Torus.mk (Y 0 i) := by
      funext i; simp [g336c1_x]
    have hid : ∀ n, modulatedEnergyKernel (hn n) (g336c1_x Y t) (withDensityReal (ρ t)) -
        modulatedEnergyKernel (hn n) (g336c1_x Y 0) (withDensityReal (ρ 0)) =
        ∫ r in Set.Icc 0 t, fn n r := by
      intro n
      have := g336c1_identity_det hd D hinvβ hN hV (hsm n) (hev n) hT hmf hreg Y hp.hint hp.hy hp.hcont
        hp.hcol ht (g336c1_micro_integrable hd hN hV hT hmf hreg hp hGk (hsm n) (hev n) (hGn n) ht)
      rw [e0]
      exact this
    have h0T : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT⟩
    have hE1 : Tendsto (fun n => modulatedEnergyKernel (hn n) (g336c1_x Y t) (withDensityReal (ρ t)))
        atTop (𝓝 (rieszEnergy d D.s (g336c1_x Y t) (withDensityReal (ρ t)))) :=
      movc_energy_tendsto hd D.hs0 D.hsd (hmf.density t ht) (c.cont ht) (M := fun n : ℕ => (n : ℝ))
        tendsto_natCast_atTop_atTop (fun n => Nat.cast_nonneg n) (g336c1_x_not_collision hp ht)
    have hE0 : Tendsto (fun n => modulatedEnergyKernel (hn n) (g336c1_x Y 0) (withDensityReal (ρ 0)))
        atTop (𝓝 (rieszEnergy d D.s (g336c1_x Y 0) (withDensityReal (ρ 0)))) :=
      movc_energy_tendsto hd D.hs0 D.hsd (hmf.density 0 h0T) (c.cont h0T) (M := fun n : ℕ => (n : ℝ))
        tendsto_natCast_atTop_atTop (fun n => Nat.cast_nonneg n) (g336c1_x_not_collision hp h0T)
    have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc 0 T := Set.Icc_subset_Icc_right ht.2
    have hR : Tendsto (fun n => ∫ r in Set.Icc 0 t, fn n r) atTop
        (𝓝 (∫ r in Set.Icc 0 t, g336c1_f D ρ Y r)) := by
      refine tendsto_integral_of_dominated_convergence (fun _ => B0)
        (fun n => (((hmeas n).mono_measure (Measure.restrict_mono hsub le_rfl))).aestronglyMeasurable)
        (integrable_const _) (fun n => ?_) ?_
      · refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun r hr => ?_)
        rw [Real.norm_eq_abs]
        exact hbd n r (hsub hr)
      · exact (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun r hr => hlimf r (hsub hr))
    exact tendsto_nhds_unique ((hE1.sub hE0).congr hid) hR

end HRS

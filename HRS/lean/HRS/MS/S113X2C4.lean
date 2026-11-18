import HRS.MS.S113X2C3
import HRS.MS.S113X2A3f

/-!
# S11.3 X2 wiring (worker S11W), C4: cutoffs and the density family of the killed laws

* `s113c_cutoff`: a smooth compactly supported cutoff equal to `1` on an open neighbourhood of a compact set.
* `s113c_btilde_contDiff`: the cut-off physical drift `θ b_E` is globally `C²` on `ℝ^{Nd}`.
* `s113c_killedLaw_compl`: the killed law at time `t` lives on `D`.
* `s113c_density_family`: a jointly measurable family `u_t` of densities of the killed laws for every `t ∈ [0,T]`
  (interior density of `s113a_killed_interior_density` for `t > 0`, Radon-Nikodym derivative at `t = 0`),
  zero off `D`, truncated at the Liouville bound `B`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S113X2C

open HRS HRS.Whole HRS.MS.S113X2 HRS.MS.S113X2B
open HRS.MC.CepP3 (Jc Jc_single fderiv2_comp_clm)

variable {d N : ℕ}

theorem s113c_cutoff {n : ℕ} {K U : Set (s113b_E n)} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (θ : s113b_E n → ℝ) (G : Set (s113b_E n)), ContDiff ℝ ∞ θ ∧ HasCompactSupport θ ∧ tsupport θ ⊆ U ∧
      (∀ z, 0 ≤ θ z ∧ θ z ≤ 1) ∧ IsOpen G ∧ K ⊆ G ∧ ∀ z ∈ G, θ z = 1 := by
  obtain ⟨L1, hL1c, hKL1, hL1U⟩ := exists_compact_between hK hU hKU
  obtain ⟨L2, hL2c, hL1L2, hL2U⟩ := exists_compact_between hL1c hU hL1U
  obtain ⟨θ, hθ, hrange, hsupp, h1⟩ := exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞))
    (isOpen_interior (s := L2)) hL1c.isClosed hL1L2
  have hts : tsupport θ ⊆ L2 := by
    unfold tsupport
    rw [hsupp]
    exact closure_minimal interior_subset hL2c.isClosed
  refine ⟨θ, interior L1, hθ, ?_, hts.trans hL2U, fun z => ⟨(hrange ⟨z, rfl⟩).1, (hrange ⟨z, rfl⟩).2⟩,
    isOpen_interior, hKL1, fun z hz => (h1 z).1 (interior_subset hz)⟩
  exact IsCompact.of_isClosed_subset hL2c (isClosed_tsupport θ) hts

theorem s113c_btilde_contDiff (s q β : ℝ) {θ : s113b_E (N * d) → ℝ} (hθ : ContDiff ℝ ∞ θ)
    (hθs : tsupport θ ⊆ {z | Jc d N z ∉ eucCollisionSet d N}) :
    ContDiff ℝ 2 (fun z => θ z • s113c_bE d s q β N z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport θ
  · have hfree : Jc d N z ∈ (eucCollisionSet d N)ᶜ := hθs hz
    have hopen : IsOpen {w : s113b_E (N * d) | Jc d N w ∈ (eucCollisionSet d N)ᶜ} := by
      exact (s113a_isOpen_free d N).preimage (Jc d N).continuous
    have hdr := s113a_drift_contDiffOn (d := d) (N := N) s q β
    have hb : ContDiffOn ℝ ∞ (s113c_bE d s q β N) {w | Jc d N w ∈ (eucCollisionSet d N)ᶜ} := by
      unfold s113c_bE
      exact (Jc d N).symm.contDiff.comp_contDiffOn (hdr.comp (Jc d N).contDiff.contDiffOn (fun w hw => hw))
    exact ((hθ.contDiffAt).smul ((hb.contDiffAt (hopen.mem_nhds hfree)))).of_le (by simp)
  · have hev : θ =ᶠ[𝓝 z] fun _ => 0 := (notMem_tsupport_iff_eventuallyEq).1 hz
    have : (fun w => θ w • s113c_bE d s q β N w) =ᶠ[𝓝 z] fun _ => (0 : s113b_E (N * d)) := by
      filter_upwards [hev] with w hw
      simp [hw]
    exact (contDiffAt_const).congr_of_eventuallyEq this

open Classical in
/-- The killed law at time `t` is carried by `D`. -/
theorem s113c_killedLaw_compl {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (D : Set (EucConfig d N)) (hD : IsOpen D) (X₀ : Ω → EucConfig d N) (X : ℝ≥0 → Ω → EucConfig d N)
    (chi : EucConfig d N → ℝ) (t : ℝ≥0) (hXt : Measurable (X t)) :
    s113a_killedLaw P D X₀ X chi t Dᶜ = 0 := by
  unfold s113a_killedLaw
  have hA : MeasurableSet Dᶜ := hD.isClosed_compl.measurableSet
  rw [Measure.map_apply hXt hA, withDensity_apply _ (hXt hA)]
  have : ∀ w ∈ X t ⁻¹' Dᶜ, (if w ∈ s113a_survives D X t then ENNReal.ofReal (chi (X₀ w)) else 0) = 0 := by
    intro w hw
    rw [if_neg]
    intro hs
    exact hw (hs t le_rfl)
  rw [setLIntegral_congr_fun (hXt hA) this]
  simp

/-- A measure dominated by a multiple of the reference measure has a density bounded by that multiple. -/
theorem s113c_ae_le_of_le {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ] {f : α → ℝ}
    (hfm : Measurable f) {B : ℝ} (hB : 0 ≤ B)
    (hν : μ.withDensity (fun x => ENNReal.ofReal (f x)) ≤ ENNReal.ofReal B • μ) : ∀ᵐ x ∂μ, f x ≤ B := by
  have h : (fun x => ENNReal.ofReal (f x)) ≤ᵐ[μ] fun _ => ENNReal.ofReal B := by
    refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite (ENNReal.measurable_ofReal.comp hfm) fun A hA _ => ?_
    have := hν A
    rw [withDensity_apply _ hA] at this
    simpa [Measure.smul_apply, mul_comm] using this.trans_eq (by simp [Measure.smul_apply, mul_comm])
  filter_upwards [h] with x hx
  exact (ENNReal.ofReal_le_ofReal_iff hB).1 hx |>.trans_eq rfl

open Classical in
/-- **The density family.**  A jointly measurable family `u_t ≥ 0` vanishing off `D`, bounded by `B`, with
`killedLaw t = u_t dx` for every `t ∈ [0,T]` (including `t = 0`), given the bound `ν_t ≤ B dx`. -/
theorem s113c_density_family {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {s q β : ℝ} (hβ : 0 < β)
    {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N}
    (hX : MovParticleSetup P d s q β N X₀ W X)
    (D : Set (EucConfig d N)) (hD : IsOpen D) (hfree : D ⊆ (eucCollisionSet d N)ᶜ)
    (chi : EucConfig d N → ℝ) (hchi : Measurable chi) (hchi0 : ∀ z, 0 ≤ chi z) (hchi1 : ∀ z, chi z ≤ 1)
    (hinit : P.map X₀ ≪ (volume : Measure (EucConfig d N)))
    {T : ℝ} (hT : 0 < T) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ t ∈ Set.Icc (0 : ℝ) T, s113a_killedLaw P D X₀ X chi t.toNNReal ≤ ENNReal.ofReal B • volume) :
    ∃ u : ℝ → EucConfig d N → ℝ, (∀ t x, 0 ≤ u t x) ∧ Measurable (Function.uncurry u) ∧
      (∀ t x, x ∉ D → u t x = 0) ∧ (∀ t x, u t x ≤ B) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T, s113a_killedLaw P D X₀ X chi t.toNNReal =
        volume.withDensity (fun x => ENNReal.ofReal (u t x)) := by
  obtain ⟨f, hfm, -, hf0, hfD, hfdens, -⟩ := s113a_killed_interior_density hβ (T := T + 1) (by linarith) hX D hD
    hfree chi hchi hchi0 hchi1
  have hXm : ∀ t, Measurable (X t) := fun t => (hX.sol 0).adapted t
  haveI : ∀ t : ℝ≥0, IsFiniteMeasure (s113a_killedLaw P D X₀ X chi t) :=
    fun t => s113a_killedLaw_finite P D X₀ X chi hchi1 t
  have hac0 := (s113a_killedLaw_zero_ac hX D chi hchi1 hinit).1
  set ν0 := s113a_killedLaw P D X₀ X chi 0 with hν0
  set g0 : EucConfig d N → ℝ := fun x => (ν0.rnDeriv volume x).toReal with hg0
  have hg0m : Measurable g0 := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hg00 : ∀ x, 0 ≤ g0 x := fun x => ENNReal.toReal_nonneg
  have hν0eq : ν0 = volume.withDensity (fun x => ENNReal.ofReal (g0 x)) := by
    rw [← Measure.withDensity_rnDeriv_eq ν0 volume hac0]
    refine withDensity_congr_ae ?_
    filter_upwards [Measure.rnDeriv_lt_top ν0 volume] with x hx
    simp [hg0, ENNReal.ofReal_toReal hx.ne]
  have hg0D : ∀ᵐ x, x ∈ Dᶜ → g0 x = 0 := by
    have h1 : ν0 Dᶜ = 0 := s113c_killedLaw_compl P D hD X₀ X chi 0 (hXm 0)
    rw [hν0eq, withDensity_apply _ hD.isClosed_compl.measurableSet] at h1
    have h2 := (lintegral_eq_zero_iff (ENNReal.measurable_ofReal.comp hg0m)).1 h1
    rw [Filter.EventuallyEq, ae_restrict_iff' hD.isClosed_compl.measurableSet] at h2
    filter_upwards [h2] with x hx hxD
    have h3 : ENNReal.ofReal (g0 x) = 0 := hx hxD
    exact le_antisymm (ENNReal.ofReal_eq_zero.1 h3) (hg00 x)
  set u : ℝ → EucConfig d N → ℝ := fun t x =>
    if t ∈ Set.Ioo 0 (T + 1) then min (f t x) B else if t = 0 then min (D.indicator g0 x) B else 0 with hu
  have hB' : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ (φ : EucConfig d N → ℝ), Measurable φ →
      s113a_killedLaw P D X₀ X chi t.toNNReal = volume.withDensity (fun x => ENNReal.ofReal (φ x)) →
      ∀ᵐ x, φ x ≤ B := by
    intro t ht φ hφ heq
    refine s113c_ae_le_of_le hφ hB0 ?_
    rw [← heq]
    exact hB t ht
  refine ⟨u, fun t x => ?_, ?_, fun t x hx => ?_, fun t x => ?_, fun t ht => ?_⟩
  · simp only [hu]
    split_ifs
    · exact le_min (hf0 t x) hB0
    · exact le_min (Set.indicator_nonneg (fun y _ => hg00 y) x) hB0
    · exact le_rfl
  · have hm1 : Measurable (fun p : ℝ × EucConfig d N => min (f p.1 p.2) B) :=
      hfm.min measurable_const
    have hm2 : Measurable (fun p : ℝ × EucConfig d N => min (D.indicator g0 p.2) B) :=
      ((hg0m.indicator hD.measurableSet).comp measurable_snd).min measurable_const
    have hs1 : MeasurableSet {p : ℝ × EucConfig d N | p.1 ∈ Set.Ioo 0 (T + 1)} :=
      measurableSet_Ioo.preimage measurable_fst
    have hs2 : MeasurableSet {p : ℝ × EucConfig d N | p.1 = 0} :=
      (measurableSet_singleton (0 : ℝ)).preimage measurable_fst
    exact Measurable.ite hs1 hm1 (Measurable.ite hs2 hm2 measurable_const)
  · simp only [hu]
    split_ifs
    · rw [hfD t x hx]; exact min_eq_left hB0
    · rw [Set.indicator_of_notMem hx]; exact min_eq_left hB0
    · rfl
  · simp only [hu]
    split_ifs
    · exact min_le_right _ _
    · exact min_le_right _ _
    · exact hB0
  · rcases ht.1.eq_or_lt with h0 | hpos
    · -- t = 0
      subst h0
      have hn0 : ¬ ((0 : ℝ) ∈ Set.Ioo 0 (T + 1)) := by simp
      have hu0 : ∀ x, u 0 x = min (D.indicator g0 x) B := fun x => by
        simp [hu, hn0]
      have hle := hB' 0 ⟨le_rfl, ht.2⟩ g0 hg0m (by simpa using hν0eq)
      rw [Real.toNNReal_zero]
      rw [show s113a_killedLaw P D X₀ X chi 0 = ν0 from rfl, hν0eq]
      refine withDensity_congr_ae ?_
      filter_upwards [hle, hg0D] with x hx hxD
      rw [hu0 x]
      by_cases hxD' : x ∈ D
      · rw [Set.indicator_of_mem hxD', min_eq_left hx]
      · rw [Set.indicator_of_notMem hxD', hxD hxD', min_eq_left hB0]
    · have htI : t ∈ Set.Ioo 0 (T + 1) := ⟨hpos, by linarith [ht.2]⟩
      have hd := hfdens t htI
      have hfmt : Measurable (f t) := hfm.comp (measurable_prodMk_left (x := t))
      have hle := hB' t ht (f t) hfmt hd
      rw [hd]
      refine withDensity_congr_ae ?_
      filter_upwards [hle] with x hx
      simp only [hu]
      rw [if_pos htI, min_eq_left hx]

end HRS.MS.S113X2C

end

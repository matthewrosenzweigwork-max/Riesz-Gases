import HRS.MS.Fp81S21ParticleWindowSup11
import HRS.MS.Fp81S21JointL
import HRS.MS.Fp81S21CenteredShort2
import HRS.MS.Fp81S21LeadingAdapter2

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open HRS HRS.Whole HRS.MS.R26T3 Set

namespace HRS.Fp81.S21

private theorem fp81s21_jointL_windowPath_restrict
    {d : ℕ} {m a H T : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ha : 0 ≤ a) (hTH : T ≤ H)
    (f : ℝ → Ω → OscDual d m)
    (hcont : ∀ᵐ ω ∂P,
      ContinuousOn (fun t : ℝ => f t ω) (Icc 0 (a + H))) :
    (fun ω => HRS.MS.ProClosureS111.physicalWindowRestriction
      (d := d) (m := m) (T := T) (H := H) (u := 0)
      (by norm_num) (by linarith [hTH])
      (HRS.Whole.windowPathOf m H a (fun t => f t ω)))
      =ᵐ[P] (fun ω => HRS.Whole.windowPathOf m T a (fun t => f t ω)) := by
  filter_upwards [hcont] with ω hω
  have hmemLong : ∀ t : Icc (0 : ℝ) H,
      a + (t : ℝ) ∈ Icc (0 : ℝ) (a + H) := by
    intro t
    constructor <;> linarith [ha, t.2.1, t.2.2]
  have hmemShort : ∀ t : Icc (0 : ℝ) T,
      a + (t : ℝ) ∈ Icc (0 : ℝ) (a + H) := by
    intro t
    constructor <;> linarith [ha, t.2.1, t.2.2, hTH]
  have hcLong : Continuous fun t : Icc (0 : ℝ) H => f (a + (t : ℝ)) ω :=
    hω.comp_continuous (by fun_prop : Continuous (fun t : Icc (0 : ℝ) H => a + (t : ℝ))) hmemLong
  have hcShort : Continuous fun t : Icc (0 : ℝ) T => f (a + (t : ℝ)) ω :=
    hω.comp_continuous (by fun_prop : Continuous (fun t : Icc (0 : ℝ) T => a + (t : ℝ))) hmemShort
  have hpathLong :
      HRS.Whole.windowPathOf m H a (fun t => f t ω) =
        (⟨fun t : Icc (0 : ℝ) H => f (a + (t : ℝ)) ω, hcLong⟩ :
          OscPath d m H) := by
    unfold HRS.Whole.windowPathOf
    exact dif_pos hcLong
  have hpathShort :
      HRS.Whole.windowPathOf m T a (fun t => f t ω) =
        (⟨fun t : Icc (0 : ℝ) T => f (a + (t : ℝ)) ω, hcShort⟩ :
          OscPath d m T) := by
    unfold HRS.Whole.windowPathOf
    exact dif_pos hcShort
  apply ContinuousMap.ext
  intro τ
  change OscPath.at'
    (HRS.MS.ProClosureS111.physicalWindowRestriction
      (d := d) (m := m) (T := T) (H := H) (u := 0)
      (by norm_num) (by linarith [hTH])
      (HRS.Whole.windowPathOf m H a (fun t => f t ω))) τ =
    OscPath.at' (HRS.Whole.windowPathOf m T a (fun t => f t ω)) τ
  rw [HRS.MS.ProClosureS111.physicalWindowRestriction_apply, hpathLong, hpathShort]
  change f (a + ((HRS.MS.ProClosureS111.physicalWindowTime
      (u := 0) (T := T) (H := H) le_rfl (by linarith [hTH]) τ : Icc (0 : ℝ) H))) ω =
    f (a + (τ : ℝ)) ω
  simp [HRS.MS.ProClosureS111.physicalWindowTime]

private theorem fp81s21_jointL_particle_raw_restriction
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) {N : ℕ}
    (hN : 2 ≤ N) (A : Particle R N)
    (H : ℝ) (hH : 0 < H) (a : ℝ) (ha : 0 ≤ a) :
    (fun ω => HRS.MS.ProClosureS111.physicalWindowRestriction
      (d := p.d) (m := ((wholeSpaceIndex p.d : ℕ) : ℝ))
      (T := H) (H := H + p.T) (u := 0)
      (by norm_num) (by linarith [p.hT])
      (flucPathW ((wholeSpaceIndex p.d : ℕ) : ℝ) (H + p.T) a
        (Real.sqrt (N : ℝ)) A.X R.ρ ω))
      =ᵐ[A.P]
    flucPathW ((wholeSpaceIndex p.d : ℕ) : ℝ) H a
      (Real.sqrt (N : ℝ)) A.X R.ρ := by
  let m : ℝ := ((wholeSpaceIndex p.d : ℕ) : ℝ)
  let Hlong : ℝ := H + p.T
  let ηfield : ℝ → A.Ω → OscDual p.d m := fun t ω =>
    HRS.Whole.etaB m (A.X (Real.toNNReal t) ω)
      (HRS.Whole.withDensityReal (R.ρ t))
  have hNpos : 0 < N := by omega
  have hd1 : 1 ≤ p.d := le_trans (by norm_num) p.hd
  have hm : (p.d : ℝ) < m := by
    dsimp [m, wholeSpaceIndex]
    push_cast
    nlinarith [show (0 : ℝ) ≤ p.d by positivity]
  have hterminal : 0 < a + Hlong := by
    dsimp [Hlong]
    linarith [ha, hH, p.hT]
  have hstrong := A.strong (a + Hlong)
  have hXm : ∀ t, Measurable (A.X t) := hstrong.adapted
  have hXc : ∀ᵐ ω ∂A.P, ∀ i, Continuous fun t : ℝ≥0 => A.X t ω i :=
    hstrong.cont
  have hprob : ∀ t ∈ Icc (0 : ℝ) (a + Hlong), HRS.Whole.IsProbDensity (R.ρ t) := by
    intro t ht
    exact (R.resulting.global (a + Hlong)).density t ht
  have hweak : ∀ ψ : Euc p.d → ℝ, Continuous ψ → (∃ B, ∀ x, |ψ x| ≤ B) →
      ContinuousOn (fun r => ∫ x, ψ x * R.ρ r x) (Icc (0 : ℝ) (a + Hlong)) := by
    intro ψ hψ hbd
    have hβprob : HRS.Whole.IsProbDensity R.ρβ := R.thermal.2.1
    have hβpos : ∀ x, 0 < R.ρβ x :=
      HRS.Whole.S78.s78_thermal_pos R.thermal.2
    exact (HRS.Whole.s21p_rho_weak_cont hβprob hβpos R.resulting ψ hψ hbd).mono
      (fun t ht => ht.1)
  have hηcont : ∀ᵐ ω ∂A.P,
      ContinuousOn (fun t : ℝ => ηfield t ω) (Icc 0 (a + Hlong)) := by
    filter_upwards [hXc] with ω hω
    exact HRS.MS.GenPath.s56_xi_cont_time hd1 hm (Real.sqrt (N : ℝ)) hNpos
      R.ρ hprob hweak (fun t => A.X (Real.toNNReal t) ω)
      (fun i => (hω i).comp continuous_real_toNNReal)
  have hsub : H ≤ Hlong := by dsimp [Hlong]; linarith [p.hT]
  have hpath := fp81s21_jointL_windowPath_restrict
    (d := p.d) (m := m) (a := a) (H := Hlong) (T := H)
    (Ω := A.Ω) (P := A.P) ha hsub ηfield
    (by
      -- Convert the global physical-time continuity to the required window interval.
      filter_upwards [hηcont] with ω hω
      exact hω)
  unfold HRS.Whole.flucPathW
  simpa [m, Hlong, ηfield, HRS.Whole.etaB, HRS.Whole.flucB] using hpath

private theorem fp81s21_jointL_gaussian_raw_restriction
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (G : GaussianRealization R) (H : ℝ) (hH : 0 < H)
    (a : ℝ) (ha : 0 ≤ a) :
    (fun ω => HRS.MS.ProClosureS111.physicalWindowRestriction
      (d := p.d) (m := ((wholeSpaceIndex p.d : ℕ) : ℝ))
      (T := H) (H := H + p.T) (u := 0)
      (by norm_num) (by linarith [p.hT])
      (processWindow ((wholeSpaceIndex p.d : ℕ) : ℝ) (H + p.T) a G.Z ω))
      =ᵐ[G.P]
    processWindow ((wholeSpaceIndex p.d : ℕ) : ℝ) H a G.Z := by
  let m : ℝ := ((wholeSpaceIndex p.d : ℕ) : ℝ)
  let Hlong : ℝ := H + p.T
  have hterminal : 0 < a + Hlong := by
    dsimp [Hlong]
    linarith [ha, hH, p.hT]
  have hZ := G.evolution (a + Hlong)
  have hcont : ∀ᵐ ω ∂G.P,
      ContinuousOn (fun t : ℝ => G.Z t ω) (Icc 0 (a + Hlong)) :=
    hZ.cont
  have hsub : H ≤ Hlong := by dsimp [Hlong]; linarith [p.hT]
  have hpath := fp81s21_jointL_windowPath_restrict
    (d := p.d) (m := m) (a := a) (H := Hlong) (T := H)
    (Ω := G.Ω) (P := G.P) ha hsub G.Z hcont
  change (fun ω => HRS.MS.ProClosureS111.physicalWindowRestriction
      (d := p.d) (m := m) (T := H) (H := Hlong) (u := 0)
      (by norm_num) (by dsimp [Hlong]; linarith [p.hT])
      (HRS.Whole.processWindow m Hlong a G.Z ω)) =ᵐ[G.P]
    (fun ω => HRS.Whole.windowPathOf m H a (fun t => G.Z t ω))
  simpa [m, Hlong, HRS.Whole.processWindow] using hpath

private theorem fp81s21_jointL_law_moment6
    {Ω B : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup B] [MeasurableSpace B] [BorelSpace B]
    (P : Measure Ω) (f : Ω → B) (M : ℝ)
    (hM : fp81s21_Moment6 P f M) :
    Integrable (fun x : B => ‖x‖ ^ 6) (law P f) ∧
      (∫ x, ‖x‖ ^ 6 ∂(law P f)) ≤ M := by
  have hmap : Integrable (fun x : B => ‖x‖ ^ 6) (P.map f) :=
    (integrable_map_measure
      (by fun_prop : AEStronglyMeasurable (fun x : B => ‖x‖ ^ 6) (P.map f))
      hM.1).mpr hM.2.1
  have hlaw : law P f = P.map f := rfl
  constructor
  · rw [hlaw]
    exact hmap
  · calc
      (∫ x, ‖x‖ ^ 6 ∂(law P f)) =
          ∫ x, ‖x‖ ^ 6 ∂(P.map f) := by rw [hlaw]
      _ = ∫ ω, ‖f ω‖ ^ 6 ∂P :=
        integral_map hM.1 hmap.aestronglyMeasurable
      _ ≤ M := hM.2.2

/-- Arbitrary-horizon raw path coupling profile. The coupled coordinates are
the actual mean-field-centered particle fluctuation window and Gaussian
process window used as raw inputs to the two-law cutoff adapter. The Gaussian
sixth-moment family is an explicit input, with its horizon quantifier before
the starts and realizations. -/
theorem fp81s21_jointL_arbitrary_horizon_raw_profile (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        (hsix :
          ∀ H : ℝ, 0 < H →
            ∃ M6 : ℝ, 0 ≤ M6 ∧
              ∀ G : GaussianRealization R, ∀ a : ℝ, 0 ≤ a →
                fp81s21_Moment6 G.P
                  (processWindow ((wholeSpaceIndex p.d : ℕ) : ℝ) H a G.Z) M6) →
        ∀ H : ℝ, 0 < H →
          ∃ d : ℕ → ℝ, fp81s21_NonnegativeVanishing d ∧
          ∃ Mpath : ℝ, 0 ≤ Mpath ∧
            ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N,
              ∀ G : GaussianRealization R, ∀ a : ℝ, 0 ≤ a →
              ∀ ε : ℝ, 0 < ε →
                ∃ π : Measure
                    (OscPath p.d ((wholeSpaceIndex p.d : ℕ) : ℝ) H ×
                     OscPath p.d ((wholeSpaceIndex p.d : ℕ) : ℝ) H),
                  IsProbabilityMeasure π ∧
                  π.map Prod.fst =
                    law A.P (flucPathW ((wholeSpaceIndex p.d : ℕ) : ℝ) H a
                      (Real.sqrt (N : ℝ)) A.X R.ρ) ∧
                  π.map Prod.snd =
                    law G.P (processWindow ((wholeSpaceIndex p.d : ℕ) : ℝ) H a G.Z) ∧
                  Integrable (fun z => ‖z.1‖ ^ 6) π ∧
                  Integrable (fun z => ‖z.2‖ ^ 6) π ∧
                  (∫ z, ‖z.1‖ ^ 6 ∂π) ≤ Mpath ∧
                  (∫ z, ‖z.2‖ ^ 6 ∂π) ≤ Mpath ∧
                  Integrable (fun z => ‖z.1 - z.2‖) π ∧
                  ((∫ z, ‖z.1 - z.2‖ ∂π) ≤ d N + ε) := by
  obtain ⟨δLead, hδLeadPos, hLeadFor⟩ := fp81s21_leadingAdapter2 p
  obtain ⟨δPart, hδPart, hδPartHalf, hPart⟩ :=
    fp81s21_particle_sixth_windows p
  let δ0 : ℝ := min δLead δPart
  have hδ0 : 0 < δ0 := lt_min hδLeadPos hδPart
  have hδ0half : δ0 ≤ 1 / 2 :=
    (min_le_right _ _).trans hδPartHalf
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R hsix H hH
  have hδLead' : δ ≤ δLead := hδle.trans (min_le_left _ _)
  have hδPart' : δ ≤ δPart := hδle.trans (min_le_right _ _)
  obtain ⟨Mpart, hMpart, hParticle6⟩ := hPart δ hδ hδPart' R H hH
  obtain ⟨M6, hM6, hGaussian6⟩ := hsix H hH
  obtain ⟨C₀, C, hC, hLead⟩ :=
    (hLeadFor δ hδ hδLead' R H hH)
  let q : ℕ → ℝ := fun n =>
    C * (Real.sqrt n * deltaN p.d p.s n +
      Real.sqrt (localizationRate p.d p.s C₀ n) +
      jN p.d p.s p.γ n)
  let d : ℕ → ℝ := fun n => (ENNReal.ofReal (q n)).toReal
  have hdnonneg : ∀ n, 0 ≤ d n := by
    intro n
    exact ENNReal.toReal_nonneg
  have hqProfile : Tendsto (fun n : ℕ =>
      ENNReal.ofReal (C * (Real.sqrt n * deltaN p.d p.s n +
        Real.sqrt (localizationRate p.d p.s C₀ n) +
        jN p.d p.s p.γ n))) atTop (𝓝 0) :=
    fp81s21_centered_recentWindow_profile p C₀ C
  have hdlim : Tendsto d atTop (𝓝 0) := by
    have h := (ENNReal.continuousAt_toReal
      (show (0 : ℝ≥0∞) ≠ ∞ by simp)).tendsto.comp hqProfile
    simpa [Function.comp_def, d, q] using h
  let Mpath : ℝ := max Mpart M6
  have hMpath : 0 ≤ Mpath := by dsimp [Mpath]; positivity
  refine ⟨d, ⟨hdnonneg, hdlim⟩, Mpath, hMpath, ?_⟩
  intro N hN A G a ha ε hε
  let m : ℝ := ((wholeSpaceIndex p.d : ℕ) : ℝ)
  let Ushort : A.Ω → OscPath p.d m H :=
    flucPathW m H a (Real.sqrt (N : ℝ)) A.X R.ρ
  let Vshort : G.Ω → OscPath p.d m H := processWindow m H a G.Z
  let Hlong : ℝ := H + p.T
  have hHlong : 0 < Hlong := by dsimp [Hlong]; linarith [hH, p.hT]
  obtain ⟨MpartLong, hMpartLong, hParticleLong⟩ :=
    hPart δ hδ hδPart' R Hlong hHlong
  have hPartShort := hParticle6 N hN A a ha
  have hGaussShort := hGaussian6 G a ha
  have hPartLong := hParticleLong N hN A a ha
  obtain ⟨M6Long, hM6Long, hGaussianLong⟩ := hsix Hlong hHlong
  have hGaussLong := hGaussianLong G a ha
  have hparticleRestriction :=
    fp81s21_jointL_particle_raw_restriction p R hN A H hH a ha
  have hgaussianRestriction :=
    fp81s21_jointL_gaussian_raw_restriction p R G H hH a ha
  have hWshort :
      wassersteinE 1 (law A.P Ushort) (law G.P Vshort) ≤
        ENNReal.ofReal (q N) := by
    let Ulong : A.Ω → OscPath p.d m Hlong :=
      flucPathW m Hlong a (Real.sqrt (N : ℝ)) A.X R.ρ
    let Vlong : G.Ω → OscPath p.d m Hlong := processWindow m Hlong a G.Z
    have hrestrict :=
      fp81s21_jointL_law_restrict_wasserstein
        (d := p.d) (m := m) (H := Hlong) (T := H) (u := 0)
        (by norm_num) (by dsimp [Hlong]; linarith [p.hT])
        Ulong Vlong hPartLong.1.1 hGaussLong.1
        Ushort Vshort
        (by simpa [Ulong, Hlong, m] using hparticleRestriction)
        (by simpa [Vlong, Hlong, m] using hgaussianRestriction)
    have hlead := hLead N hN A G a ha
    simpa [Ushort, Vshort, m] using hrestrict.trans hlead
  have hqle : q N ≤ d N := by
    by_cases hq : 0 ≤ q N
    · simp [d, ENNReal.toReal_ofReal hq]
    · have hqneg : q N < 0 := lt_of_not_ge hq
      have hzero : ENNReal.ofReal (q N) = 0 :=
        ENNReal.ofReal_eq_zero.mpr (le_of_lt hqneg)
      simp [d, hzero]
      linarith
  have hWshort' : wassersteinE 1 (law A.P Ushort) (law G.P Vshort) ≤
      ENNReal.ofReal (d N) :=
    hWshort.trans (ENNReal.ofReal_le_ofReal hqle)
  have hUlaw := fp81s21_jointL_law_moment6 A.P Ushort Mpart hPartShort.1
  have hVlaw := fp81s21_jointL_law_moment6 G.P Vshort M6 hGaussShort
  haveI hUprob : IsProbabilityMeasure (law A.P Ushort) :=
    (Measure.isProbabilityMeasure_map_iff hPartShort.1.1).2 inferInstance
  haveI hVprob : IsProbabilityMeasure (law G.P Vshort) :=
    (Measure.isProbabilityMeasure_map_iff hGaussShort.1).2 inferInstance
  obtain ⟨π, hπ, hπ₁, hπ₂, hcostInt, hcost⟩ :=
    fp81s21_exists_coupling_of_W1_le
      (law A.P Ushort) (law G.P Vshort) (hdnonneg N) hWshort' hε
  letI : IsProbabilityMeasure π := hπ
  have hUbound : (∫ x, ‖x‖ ^ 6 ∂(law A.P Ushort)) ≤ Mpath :=
    hUlaw.2.trans (by dsimp [Mpath]; exact le_max_left _ _)
  have hVbound : (∫ x, ‖x‖ ^ 6 ∂(law G.P Vshort)) ≤ Mpath :=
    hVlaw.2.trans (by dsimp [Mpath]; exact le_max_right _ _)
  obtain ⟨hfst6, hsnd6, hfstM, hsndM⟩ :=
    fp81s21_jointL_coupling_sixth_marginals
      (law A.P Ushort) (law G.P Vshort) π hπ₁ hπ₂ Mpath
      hUlaw.1 hVlaw.1 hUbound hVbound
  refine ⟨π, hπ, hπ₁, hπ₂, hfst6, hsnd6, hfstM, hsndM, hcostInt, hcost⟩

#print axioms fp81s21_jointL_arbitrary_horizon_raw_profile

end HRS.Fp81.S21

end

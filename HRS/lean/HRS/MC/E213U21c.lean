import HRS.MC.E213U21b

/-!
# Packet e213u21 (part c): the algebraic reduction of `core_bound`

For fixed `N ≥ 2`, `a ≥ 0`, `Φ` in the unit ball, and with the near/far splittings of the four Riemann--Stieltjes
expectations given as hypotheses (`hPA`, `hPJ`, `hGA`, `hGJ`; the splitting numbers `ANn, ANf, ...` are arbitrary
reals), the error `errVal` is bounded by the initial-term error plus the near-difference plus the two far terms.
Inputs used: `window_identity`, the heat identity `hheat`, `cond_removal_*`, `contract_*`, `init_identification`,
`iteratedFDeriv_three_symm` (through `u21_Kproj_apply`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213U21

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ} {S : PreparedData d} {β₀ m : ℝ}

theorem u21_err_le (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (gd : GaussData S β₀ hE)
    (fam : PrepFamily S β₀ hE)
    (hheat : ∀ (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 5 Φ),
      ∫ ω, Φ (gd.Zwin T a ω) ∂gd.P₀ = ∫ ω, Ucan hE T a ha Φ 0 (Iwin S β₀ hE T a (gd.η 0 ω)) ∂gd.P₀)
    (N : ℕ) (hN : 2 ≤ N) (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ) (hΦ : Φ ∈ CbUnitBall (PathSpace d m T) 5)
    (ANn ANf JNn JNf AGn AGf JGn JGf : ℝ)
    (hPA : ∫ ω, rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (zetaWin m (a + T) 0 (fam.P N) (fam.X N) ω)
        (fun v => quadFieldAt m (regime S β₀ hE).D.s (fun t => withDensityReal ((regime S β₀ hE).ρ t))
          (fam.P N) (fam.X N) v ω) ∂(fam.P N) = ANn + ANf)
    (hPJ : ∫ ω, rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (zetaWin m (a + T) 0 (fam.P N) (fam.X N) ω)
        (fun v => etaE m ((fam.X N) v.toNNReal ω) (withDensityReal ((regime S β₀ hE).ρ v))) ∂(fam.P N) = JNn + JNf)
    (hGA : ∫ ω, rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (gd.Zwin (a + T) 0 ω)
        (fun v => NegSobolev.embed m (gd.B v ω)) ∂gd.P₀ = AGn + AGf)
    (hGJ : ∫ ω, rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (gd.Zwin (a + T) 0 ω)
        (fun v => NegSobolev.embed m (gd.η v ω)) ∂gd.P₀ = JGn + JGf) :
    gd.errVal T N a Φ (fam.P N) (fam.X N) ≤
      |Real.sqrt N *
          (∫ X, Ucan hE T a ha Φ 0 (Iwin S β₀ hE T a
              (zetaE (rLvl d) (modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0) X))
              ∂(modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0) -
            ∫ F, Ucan hE T a ha Φ 0 (Iwin S β₀ hE T a F) ∂(gd.P₀.map (gd.η 0))) -
        (1 / 6) * ∫ F, ∫ x, iteratedFDeriv ℝ 3 (fun z => Ucan hE T a ha Φ 0 (Iwin S β₀ hE T a z)) F
            ![ellVec S β₀ x, ellVec S β₀ x, ellVec S β₀ x] ∂S.μ0 ∂(gd.P₀.map (gd.η 0))| +
      (|ANn - AGn| + 1 / 2 * |JNn - JGn|) + (|ANf| + 1 / 2 * |JNf|) + (|AGf| + 1 / 2 * |JGf|) := by
  have hN1 : 1 ≤ N := by omega
  have hH : 0 < a + T := by linarith
  have hΦ1 : MemCb 5 Φ := ⟨hΦ.1, hΦ.2.1⟩
  have hΦ3 : MemCb 3 Φ := u21_memCb_mono hΦ1
  have hreal := fam.hreal N hN1
  -- window identity
  obtain ⟨-, -, -, -, hW⟩ := HRS.MC.E213U8.window_identity_proof hE T hT a ha N hN1 (fam.P N) (fam.X₀ N) (fam.W N)
    (fam.X N) hreal Φ hΦ1
  -- laws
  have hZaem := u21_windowZeta_aem hE hN (fam.P N) (fam.X₀ N) (fam.W N) (fam.X N) hreal T a hT ha
  have hGaem := HRS.MC.E213U16.u16_Zwin_aem gd T hT a ha
  have eW : ∫ z, Φ z ∂(law (fam.P N) (HRS.Main.windowZeta m T a (fam.P N) (fam.X N))) =
      ∫ ω, Φ (HRS.Main.windowZeta m T a (fam.P N) (fam.X N) ω) ∂(fam.P N) :=
    integral_map hZaem hΦ1.1.continuous.aestronglyMeasurable
  have eZ : ∫ z, Φ z ∂(law gd.P₀ (gd.Zwin T a)) = ∫ ω, Φ (gd.Zwin T a ω) ∂gd.P₀ :=
    integral_map hGaem hΦ1.1.continuous.aestronglyMeasurable
  -- heat identity, pushed to the law of `η 0`
  have hU : MemCb 5 (Ucan hE T a ha Φ 0) :=
    (HRS.MC.E213U5.Ucan_regular_proof hE T hT a ha Φ hΦ1).1 0 ⟨le_rfl, hH.le⟩
  have hηm : AEMeasurable (gd.η 0) gd.P₀ := by
    obtain ⟨Y₀, -, hlin⟩ := gd.limit
    exact ((hlin 0).meas 0).aemeasurable
  have hΨc : Continuous fun F => Ucan hE T a ha Φ 0 (Iwin S β₀ hE T a F) :=
    hU.1.continuous.comp (Iwin S β₀ hE T a).continuous
  have eη : ∫ F, Ucan hE T a ha Φ 0 (Iwin S β₀ hE T a F) ∂(gd.P₀.map (gd.η 0)) =
      ∫ ω, Ucan hE T a ha Φ 0 (Iwin S β₀ hE T a (gd.η 0 ω)) ∂gd.P₀ :=
    integral_map hηm hΨc.aestronglyMeasurable
  have eheat : ∫ ω, Φ (gd.Zwin T a ω) ∂gd.P₀ =
      ∫ F, Ucan hE T a ha Φ 0 (Iwin S β₀ hE T a F) ∂(gd.P₀.map (gd.η 0)) := by
    rw [eη]; exact hheat T hT a ha Φ hΦ1
  -- initial term of the particle system
  have einit := u21_init_particle hE T hT a ha Φ hΦ1 hN (fam.P N) (fam.X₀ N) (fam.W N) (fam.X N) hreal
  -- Gaussian side
  have cA := HRS.MC.E213U16.cond_removal_drift_proof gd T hT a ha Φ hΦ1
  have kd := HRS.MC.E213U15.contract_drift_proof gd T hT a ha Φ hΦ3
  have cJ := HRS.MC.E213U16.cond_removal_J_proof gd T hT a ha Φ hΦ1
  have kj := HRS.MC.E213U15.contract_J_proof gd T hT a ha Φ hΦ3
  have ini := HRS.MC.E213U19.init_identification_proof gd T hT a ha Φ hΦ1
  -- the tensor `K_a` on `D³Φ(Z)`
  set uI := pushforward3 (Iwin S β₀ hE T a) (Kinit0 S β₀) with huI
  set uD := bochTensor3 gd.P₀ (gd.Dwin T a) (gd.Zwin T a) (gd.Zwin T a) with huD
  set uJ := bochTensor21 gd.P₀ (gd.Jwin T a) (gd.Zwin T a) with huJ
  have iI := u21_integrable_apply gd.P₀ (gd.Zwin T a) hGaem Φ hΦ1 uI
  have iD := u21_integrable_apply gd.P₀ (gd.Zwin T a) hGaem Φ hΦ1 uD
  have iJ := u21_integrable_apply gd.P₀ (gd.Zwin T a) hGaem Φ hΦ1 uJ
  have eK : ∫ ω, ((gd.Kproj T a : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3)
      (iteratedFDeriv ℝ 3 Φ (gd.Zwin T a ω)) ∂gd.P₀ =
      ∫ ω, uI (iteratedFDeriv ℝ 3 Φ (gd.Zwin T a ω)) ∂gd.P₀
        - 3 * ∫ ω, uD (iteratedFDeriv ℝ 3 Φ (gd.Zwin T a ω)) ∂gd.P₀
        + 3 * ∫ ω, uJ (iteratedFDeriv ℝ 3 Φ (gd.Zwin T a ω)) ∂gd.P₀ := by
    have : ∀ ω, ((gd.Kproj T a : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3)
        (iteratedFDeriv ℝ 3 Φ (gd.Zwin T a ω)) =
        uI (iteratedFDeriv ℝ 3 Φ (gd.Zwin T a ω)) - 3 * uD (iteratedFDeriv ℝ 3 Φ (gd.Zwin T a ω))
          + 3 * uJ (iteratedFDeriv ℝ 3 Φ (gd.Zwin T a ω)) := fun ω =>
      u21_Kproj_apply gd T hT a ha Φ hΦ1 (gd.Zwin T a ω)
    simp_rw [this]
    have i1 : Integrable (fun ω => uI (iteratedFDeriv ℝ 3 Φ (gd.Zwin T a ω)) -
        3 * uD (iteratedFDeriv ℝ 3 Φ (gd.Zwin T a ω))) gd.P₀ := iI.sub (iD.const_mul 3)
    rw [integral_add i1 (iJ.const_mul 3), integral_sub iI (iD.const_mul 3), integral_const_mul,
      integral_const_mul]
  -- the algebra
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < N))
  have key := u21_alg (s := Real.sqrt N)
    (x₁ := ∫ z, Φ z ∂(law (fam.P N) (HRS.Main.windowZeta m T a (fam.P N) (fam.X N))))
    (x₂ := ∫ z, Φ z ∂(law gd.P₀ (gd.Zwin T a)))
    (i₁ := ∫ x, Ucan hE T a ha Φ 0 (Iwin S β₀ hE T a
          (zetaE (rLvl d) (modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0) x))
          ∂(modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0))
    (i₂ := ∫ F, Ucan hE T a ha Φ 0 (Iwin S β₀ hE T a F) ∂(gd.P₀.map (gd.η 0)))
    (AN := ∫ ω, rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (zetaWin m (a + T) 0 (fam.P N) (fam.X N) ω)
        (fun v => quadFieldAt m (regime S β₀ hE).D.s (fun t => withDensityReal ((regime S β₀ hE).ρ t))
          (fam.P N) (fam.X N) v ω) ∂(fam.P N))
    (JN := ∫ ω, rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (zetaWin m (a + T) 0 (fam.P N) (fam.X N) ω)
        (fun v => etaE m ((fam.X N) v.toNNReal ω) (withDensityReal ((regime S β₀ hE).ρ v))) ∂(fam.P N))
    (AG := ∫ ω, rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (gd.Zwin (a + T) 0 ω)
        (fun v => NegSobolev.embed m (gd.B v ω)) ∂gd.P₀)
    (JG := ∫ ω, rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (gd.Zwin (a + T) 0 ω)
        (fun v => NegSobolev.embed m (gd.η v ω)) ∂gd.P₀)
    (T₃ := ∫ F, ∫ x, iteratedFDeriv ℝ 3 (fun z => Ucan hE T a ha Φ 0 (Iwin S β₀ hE T a z)) F
            ![ellVec S β₀ x, ellVec S β₀ x, ellVec S β₀ x] ∂S.μ0 ∂(gd.P₀.map (gd.η 0)))
    (K₁ := ∫ ω, uI (iteratedFDeriv ℝ 3 Φ (gd.Zwin T a ω)) ∂gd.P₀)
    (Kd := ∫ ω, uD (iteratedFDeriv ℝ 3 Φ (gd.Zwin T a ω)) ∂gd.P₀)
    (Kj := ∫ ω, uJ (iteratedFDeriv ℝ 3 Φ (gd.Zwin T a ω)) ∂gd.P₀)
    (EK := ∫ ω, ((gd.Kproj T a : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3)
      (iteratedFDeriv ℝ 3 Φ (gd.Zwin T a ω)) ∂gd.P₀)
    (ANn := ANn) (ANf := ANf) (JNn := JNn) (JNf := JNf) (AGn := AGn) (AGf := AGf) (JGn := JGn) (JGf := JGf)
    hsN (by rw [eW, hW, einit]) (by rw [eZ, eheat])
    (by rw [cA, kd]) (by rw [cJ, kj]) ini eK hPA hPJ hGA hGJ
  exact key

end HRS.MC.E213U21

end

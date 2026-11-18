import HRS.MS.Fp81S21TimeRep14
import HRS.MS.Fp81S21PredMap2
import HRS.MS.Fp81S21EmbedMom3

/-! Physical particle fields satisfy the weighted time-section contract. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.R2Interp
open HRS.MS.ProClosureS111

/-- Assemble the weighted-test section contract from product-a.e. compact
agreement and the physical weighted extension bound. -/
theorem fp81s21_TimeRep_of_TimeL2Rep_product
    {d r : ℕ} {Pw : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (hP : (d : ℝ) < 2 * Pw) (E : r26t6_WeightedChart d r Pw)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : ℝ → Ω → (Euc d → ℝ) → ℝ) (q : ℝ → Ω → r26t6_Coeff)
    (M a H : ℝ)
    (U : Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)))
    (hcore : fp81s21_TimeL2Rep P q M a H U)
    (hcompact_prod_ae : ∀ᵐ z ∂((volume.restrict (Set.Icc (0 : ℝ) H)).prod P),
      ∀ f, IsR2Test f → fp81s21_chartAction E (q (a + z.1) z.2) f = Q (a + z.1) z.2 f)
    (hZ_prod_ae : ∀ᵐ z ∂((volume.restrict (Set.Icc 0 H)).prod P),
      S102Z r Pw (Q (a + z.1) z.2)) :
    fp81s21_TimeRep E P Q q M a H U := by
  let dt : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) H)
  have hc := (Measure.measurePreserving_swap (μ := P) (ν := dt)).quasiMeasurePreserving.ae
    (show ∀ᵐ z ∂(dt.prod P),
      ∀ f, IsR2Test f → fp81s21_chartAction E (q (a + z.1) z.2) f = Q (a + z.1) z.2 f by
      simpa [dt] using hcompact_prod_ae)
  have hz := (Measure.measurePreserving_swap (μ := P) (ν := dt)).quasiMeasurePreserving.ae
    (show ∀ᵐ z ∂(dt.prod P), S102Z r Pw (Q (a + z.1) z.2) by
      simpa [dt] using hZ_prod_ae)
  have hc' := Measure.ae_ae_of_ae_prod hc
  have hz' := Measure.ae_ae_of_ae_prod hz
  refine ⟨hcore.1, hcore.2.1, hcore.2.2.1, ?_⟩
  filter_upwards [hcore.2.2.2, hc', hz'] with ω hω hcω hzω
  refine ⟨hω.1, ?_⟩
  filter_upwards [hω.2, hcω, hzω] with t he hc ht
  refine ⟨he, ?_⟩
  intro f hf
  rw [he]
  exact fp81s21_chartAction_eq_of_compact_agreement hP E (q (a + t) ω)
    (Q (a + t) ω) ht hc f hf

/-- Embedding for source charts whose displayed weight index is propositionally
equal to the target weight plus two. -/
theorem fp81s21_MomentRep_embedField_weight
    {d q : ℕ} {Ps Pw : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (hP : (d : ℝ) < 2 * Pw)
    (hPs : (d : ℝ) < 2 * (Pw + 2))
    (Es : r26t6_WeightedChart d q Ps)
    (hWeight : Ps = Pw + 2)
    (E : r26t6_WeightedChart d (q + 2) Pw)
    (P : Measure Ω) (Q : ℝ → Ω → (Euc d → ℝ) → ℝ)
    (qs : ℝ → Ω → r26t6_Coeff) (M : ℝ)
    (hrep : fp81s21_MomentRep Es P Q qs M) :
    fp81s21_MomentRep E P Q
      (fun u ω => fp81s21_embedField hP hPs (hWeight ▸ Es) E (qs u ω)) M := by
  subst Ps
  simpa using fp81s21_MomentRep_embedField hP hPs Es E P Q qs M hrep

/-- Build weak-chart configuration representatives from one jointly
measurable particle modification and identify them with the embedded strong
representatives on a time slab. -/
theorem fp81s21_particle_TimeRep_bridge (p : Parameters) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ R : Trajectory p δ,
        ∃ M : ℝ, 0 ≤ M ∧
          ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N,
            ∀ Es : r26t6_WeightedChart p.d (2 * p.d + 6)
                ((p.d : ℝ) + 4),
              ∀ E : r26t6_WeightedChart p.d (2 * p.d + 8)
                  ((p.d : ℝ) + 2),
                ∃ qsη qsB : ℝ → A.Ω → r26t6_Coeff,
                  fp81s21_MomentRep Es A.P
                    (fp81s21_particleEmpField R N A) qsη M ∧
                  fp81s21_MomentRep Es A.P
                    (fp81s21_particleQuadField R N A) qsB M ∧
                  ∀ a : ℝ, 0 ≤ a → ∀ H : ℝ, 0 < H →
                    ∃ qη qB : ℝ → A.Ω → r26t6_Coeff,
                      fp81s21_MomentRep E A.P
                        (fp81s21_particleEmpField R N A) qη M ∧
                      fp81s21_MomentRep E A.P
                        (fp81s21_particleQuadField R N A) qB M ∧
                      ∃ Y : ℝ × A.Ω → EucConfig p.d N,
                        Measurable Y ∧
                        (∀ᵐ ω ∂A.P, ∀ t : ℝ,
                          Y (t, ω) = A.X t.toNNReal ω) ∧
                        ∃ qη₀ qB₀ : ℝ → A.Ω → r26t6_Coeff,
                          Measurable (Function.uncurry qη₀) ∧
                          Measurable (Function.uncurry qB₀) ∧
                          (∀ᵐ z ∂((volume.restrict (Set.Icc (0 : ℝ) H)).prod A.P),
                            ∀ f, IsR2Test f →
                              fp81s21_chartAction E (qη (a + z.1) z.2) f =
                                fp81s21_particleEmpField R N A (a + z.1) z.2 f) ∧
                          (∀ᵐ z ∂((volume.restrict (Set.Icc (0 : ℝ) H)).prod A.P),
                            ∀ f, IsR2Test f →
                              fp81s21_chartAction E (qB (a + z.1) z.2) f =
                                fp81s21_particleQuadField R N A (a + z.1) z.2 f) ∧
                          (∀ᵐ z ∂((volume.restrict (Set.Icc (0 : ℝ) H)).prod A.P),
                            S102Z (2 * p.d + 8) ((p.d : ℝ) + 2)
                              (fp81s21_particleEmpField R N A (a + z.1) z.2)) ∧
                          (∀ᵐ z ∂((volume.restrict (Set.Icc (0 : ℝ) H)).prod A.P),
                            S102Z (2 * p.d + 8) ((p.d : ℝ) + 2)
                              (fp81s21_particleQuadField R N A (a + z.1) z.2)) ∧
                          ∃ Uη UB,
                            fp81s21_TimeRep E A.P
                              (fp81s21_particleEmpField R N A) qη M a H Uη ∧
                            fp81s21_TimeRep E A.P
                              (fp81s21_particleQuadField R N A) qB M a H UB := by
  obtain ⟨δs, hδs, hδshalf, hStrong⟩ :=
    fp81s21_particle_momentReps_strong p
  obtain ⟨δz, hδz, hδzhalf, hZProducer⟩ :=
    fp81s21_particle_fields_S102Z p
  obtain ⟨δu, hδu, hδuhalf, hUniform⟩ :=
    fp81s21_uniform_density_moments p
  let δ₀ : ℝ := min δs (min δz δu)
  have hδ₀ : 0 < δ₀ := lt_min hδs (lt_min hδz hδu)
  have hδ₀half : δ₀ ≤ 1 / 2 :=
    (min_le_left δs (min δz δu)).trans hδshalf
  refine ⟨δ₀, hδ₀, hδ₀half, ?_⟩
  intro δ hδ hδle R
  have hδs' : δ ≤ δs := hδle.trans (min_le_left _ _)
  have hδz' : δ ≤ δz := hδle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδu' : δ ≤ δu := hδle.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨M, hM, hMR⟩ := hStrong δ hδ hδs' R
  obtain ⟨pinf, K, C₀, c₀, Mdens, L, Mρ, Cm, hpinf, hc₀,
    hGaussian, hRound2, hReferenceMoment, hParticle⟩ :=
      hUniform δ hδ hδu' R
  have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by nlinarith [p.hd]
  have hPs : (p.d : ℝ) < 2 * (((p.d : ℝ) + 2) + 2) := by nlinarith [p.hd]
  have hExp : ((p.d : ℝ) + 2) + 2 = (p.d : ℝ) + 4 := by ring
  have hPw : 0 ≤ (p.d : ℝ) + 2 := by positivity
  have hd1 : 1 ≤ p.d := le_trans (by decide : 1 ≤ 2) p.hd
  have hrEmp : (p.d : ℝ) / 2 < (2 * p.d + 8 : ℕ) := by
    push_cast
    nlinarith [show (2 : ℝ) ≤ p.d by exact_mod_cast p.hd]
  have hrQuad : (p.d : ℝ) / 2 + 2 < (2 * p.d + 8 : ℕ) := by
    push_cast
    nlinarith [show (2 : ℝ) ≤ p.d by exact_mod_cast p.hd]
  have hNpos : ∀ N : ℕ, 2 ≤ N → 0 < N := fun N hN => by omega
  have hChartCond : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := hP
  have hδh : δ ≤ 1 / 2 := hδle.trans hδ₀half
  refine ⟨M, hM, ?_⟩
  intro N hN A Es E
  let Es' : r26t6_WeightedChart p.d (2 * p.d + 6)
      (((p.d : ℝ) + 2) + 2) := hExp.symm ▸ Es
  obtain ⟨qsη, qsB, hηsrc, hBsrc, -⟩ := hMR N hN A Es
  let qη : ℝ → A.Ω → r26t6_Coeff := fun u ω =>
    fp81s21_embedField hP hPs Es' E (qsη u ω)
  let qB : ℝ → A.Ω → r26t6_Coeff := fun u ω =>
    fp81s21_embedField hP hPs Es' E (qsB u ω)
  have hηrep : fp81s21_MomentRep E A.P
      (fp81s21_particleEmpField R N A) qη M := by
    simpa [qη, Es'] using fp81s21_MomentRep_embedField_weight hP hPs Es hExp.symm E A.P
      (fp81s21_particleEmpField R N A) qsη M hηsrc
  have hBrep : fp81s21_MomentRep E A.P
      (fp81s21_particleQuadField R N A) qB M := by
    simpa [qB, Es'] using fp81s21_MomentRep_embedField_weight hP hPs Es hExp.symm E A.P
      (fp81s21_particleQuadField R N A) qsB M hBsrc
  refine ⟨qsη, qsB, hηsrc, hBsrc, ?_⟩
  intro a ha H hH
  have hXmeas : ∀ t, Measurable (A.X t) :=
    (A.strong (1 : ℝ)).adapted
  have hXcont := (A.strong (1 : ℝ)).cont
  obtain ⟨Y, hYmeas, hYae⟩ := HRS.MS.R2S11.s11_X_joint hXmeas hXcont
  let clip : ℝ → ℝ := fun u => ((max u 0).toNNReal : ℝ)
  have hclipEq : clip = fun u => max u 0 := by
    funext u
    dsimp [clip]
    exact Real.coe_toNNReal _ (le_max_right _ _)
  have hclipMeas : Measurable clip := by
    rw [hclipEq]
    fun_prop
  have hclipNonneg : ∀ u, 0 ≤ clip u := by
    intro u
    rw [hclipEq]
    exact le_max_right _ _
  have hclipAt : ∀ u, 0 ≤ u → clip u = u := by
    intro u hu
    rw [hclipEq]
    exact max_eq_left hu
  let rhoClip : ℝ → Euc p.d → ℝ := fun u x => R.ρ (clip u) x
  have hrhoJoint : Measurable (fun q : ℝ × Euc p.d => rhoClip q.1 q.2) := by
    simpa [rhoClip, clip] using
      (fp81s21_particle_density_clip_continuous p R hδ hδh).measurable
  have hroundClip : ∀ u,
    HRS.Whole.IsRound2Density p.d p.s Mdens L (rhoClip u) := by
    intro u
    exact hRound2 (clip u) (hclipNonneg u)
  have hgaussClip : ∀ u x, rhoClip u x ≤ C₀ * Real.exp (-c₀ * ‖x‖ ^ 2) := by
    intro u x
    exact (hGaussian (clip u) (hclipNonneg u)).2 x
  have hρnonneg : ∀ u x, 0 ≤ rhoClip u x := by
    intro u x
    exact (hroundClip u).prob.nonneg x
  let μclip : ℝ → Measure (Euc p.d) := fun u =>
    HRS.Whole.withDensityReal (rhoClip u)
  have hReferenceIntegrable : ∀ u,
      Integrable (fun x : Euc p.d => jbracket x ^ ((p.d : ℝ) + 2)) (μclip u) := by
    intro u
    exact fp81s21_particle_reference_weight_integrable
      (hroundClip u).prob hc₀ hPw (hGaussian (clip u) (hclipNonneg u))
  have hm : ∀ j, Measurable (fun u =>
      HRS.Whole.pair (μclip u) (E.test j)) := by
    intro j
    have htest : Measurable (fun q : ℝ × Euc p.d => E.test j q.2) :=
      ((E.test_smooth j).1.continuous.measurable).comp measurable_snd
    have hint : Measurable (fun u =>
        ∫ x, E.test j x ∂μclip u) := by
      simpa [μclip] using
        fp81s21_moving_spatial_integral_meas hrhoJoint hρnonneg htest
    simpa [HRS.Whole.pair] using hint
  obtain ⟨zη, hzηmeas, hzηrep⟩ := fp81s21_emp_config_rep
      (d := p.d) (r := 2 * p.d + 8) (N := N) (Pw := (p.d : ℝ) + 2)
    hd1 hPw hrEmp hP E (hNpos N hN) μclip hReferenceIntegrable hm
  let Yclip : ℝ × A.Ω → EucConfig p.d N := fun z => Y (clip z.1, z.2)
  have hYclipMeas : Measurable Yclip := by
    exact hYmeas.comp ((hclipMeas.comp measurable_fst).prodMk measurable_snd)
  have hactualClip : ∀ v, HRS.Whole.HasR2ActualDensity p.s p.β pinf K
      (HRS.Whole.withDensityReal (rhoClip v))
      (A.P.map (fun ω => Yclip (v, ω))) := by
    intro v
    let t : NNReal := (clip v).toNNReal
    have hraw := (hParticle N hN A (clip v) (hclipNonneg v)).1
    change HRS.Whole.HasR2ActualDensity p.s p.β pinf K
      (HRS.Whole.withDensityReal (rhoClip v))
      (A.P.map (fun ω => A.X t ω)) at hraw
    have hYlaw : A.P.map (fun ω => Yclip (v, ω)) =
        A.P.map (fun ω => A.X t ω) := by
      apply Measure.map_congr
      filter_upwards [hYae] with ω hω
      simp [Yclip, t, hω (clip v)]
    rw [hYlaw]
    exact hraw
  obtain ⟨cQuad, hcQuad, zB, hzBmeas, hzBrep, hbound⟩ :=
    fp81s21_quad_config_rep_gen
      (d := p.d) (N := N) (s := p.s) (M := Mdens) (L := L)
      (C₀ := C₀) (c₀ := c₀) (β := p.β) (pint := pinf) (K := K)
      p.hd p.hs0 p.hs hc₀ p.hβ hpinf hrhoJoint hroundClip hgaussClip hN
      A.P Yclip hYclipMeas hactualClip hPw hChartCond hrQuad E
  let qη₀ : ℝ → A.Ω → r26t6_Coeff := fun u ω =>
    zη (clip u) (Yclip (u, ω))
  let qB₀ : ℝ → A.Ω → r26t6_Coeff := fun u ω =>
    zB (clip u) (Yclip (u, ω))
  have hqη₀meas : Measurable (Function.uncurry qη₀) := by
    change Measurable (fun z : ℝ × A.Ω => zη (clip z.1) (Yclip z))
    exact hzηmeas.comp ((hclipMeas.comp measurable_fst).prodMk hYclipMeas)
  have hqB₀meas : Measurable (Function.uncurry qB₀) := by
    change Measurable (fun z : ℝ × A.Ω => zB (clip z.1) (Yclip z))
    exact hzBmeas.comp ((hclipMeas.comp measurable_fst).prodMk hYclipMeas)
  have hη₀action (u : ℝ) (hu : 0 ≤ u) (ω : A.Ω)
      (hpath : ∀ v : ℝ, Y (v, ω) = A.X v.toNNReal ω) :
      ∀ f, IsR2Test f →
        fp81s21_chartAction E (qη₀ u ω) f =
          fp81s21_particleEmpField R N A u ω f := by
    have hclipu := hclipAt u hu
    have hqeq : qη₀ u ω = zη u (A.X u.toNNReal ω) := by
      simp [qη₀, Yclip, hclipu, hpath u]
    intro f hf
    rw [hqeq]
    simpa [fp81s21_particleEmpField, μclip, rhoClip, hclipu,
      HRS.MS.R26T3.r26t3_mu] using (hzηrep u (A.X u.toNNReal ω)).1 f hf
  have hB₀action (u : ℝ) (hu : 0 ≤ u) (ω : A.Ω)
      (hpath : ∀ v : ℝ, Y (v, ω) = A.X v.toNNReal ω) :
      ∀ f, IsR2Test f →
        fp81s21_chartAction E (qB₀ u ω) f =
          fp81s21_particleQuadField R N A u ω f := by
    have hclipu := hclipAt u hu
    let t : NNReal := u.toNNReal
    let YAt : A.Ω → EucConfig p.d N := fun ζ => Yclip (u, ζ)
    have hIntEq (f : Euc p.d → ℝ) :
        (∫ ζ, pairEnergy
          (HRS.Whole.commutatorKernel p.d p.s (fun x => gradient f x))
          (YAt ζ) (HRS.Whole.withDensityReal (R.ρ u)) ∂A.P) =
        ∫ ζ, pairEnergy
          (HRS.Whole.commutatorKernel p.d p.s (fun x => gradient f x))
          (A.X t ζ) (HRS.Whole.withDensityReal (R.ρ u)) ∂A.P := by
      apply integral_congr_ae
      filter_upwards [hYae] with ζ hζ
      simp [YAt, Yclip, hclipu, hζ u, t]
    let T : EucConfig p.d N → (Euc p.d → ℝ) → ℝ := fun X f =>
      HRS.Whole.r2CommDistr p.d p.s (HRS.Whole.withDensityReal (R.ρ u)) X f -
        ∫ ζ, HRS.Whole.r2CommDistr p.d p.s
          (HRS.Whole.withDensityReal (R.ρ u)) (YAt ζ) f ∂A.P
    have hFieldEq : T (A.X t ω) = fp81s21_particleQuadField R N A u ω := by
      funext f
      dsimp [T, fp81s21_particleQuadField, HRS.Whole.r2QuadField,
        HRS.Whole.r2CommDistr, HRS.MS.R26T3.r26t3_mu]
      rw [integral_const_mul, hIntEq f]
      ring
    have hqeq : qB₀ u ω = zB u (A.X t ω) := by
      simp [qB₀, Yclip, hclipu, hpath u, t]
    have hRep : fp81s21_TestRep E (T (A.X t ω)) (zB u (A.X t ω)) := by
      simpa [T, YAt, Yclip, hclipu, μclip, rhoClip] using hzBrep u (A.X t ω)
    intro f hf
    calc
      fp81s21_chartAction E (qB₀ u ω) f =
          fp81s21_chartAction E (zB u (A.X t ω)) f := by rw [hqeq]
      _ = T (A.X t ω) f := hRep.1 f hf
      _ = fp81s21_particleQuadField R N A u ω f := congrFun hFieldEq f
  have hηsection : ∀ u, 0 ≤ u →
      (fun ω => qη u ω) =ᵐ[A.P] (fun ω => qη₀ u ω) := by
    intro u hu
    obtain ⟨_, _, hfield⟩ := hηrep.2 u hu
    filter_upwards [hfield, hYae] with ω hω hpath
    apply fp81s21_coeff_eq_of_chartAction_eq hP E (qη u ω) (qη₀ u ω)
    intro f hf
    calc
      fp81s21_chartAction E (qη u ω) f =
          fp81s21_particleEmpField R N A u ω f := hω.1 f hf
      _ = fp81s21_chartAction E (qη₀ u ω) f :=
        (hη₀action u hu ω hpath f hf).symm
  have hBsection : ∀ u, 0 ≤ u →
      (fun ω => qB u ω) =ᵐ[A.P] (fun ω => qB₀ u ω) := by
    intro u hu
    obtain ⟨_, _, hfield⟩ := hBrep.2 u hu
    filter_upwards [hfield, hYae] with ω hω hpath
    apply fp81s21_coeff_eq_of_chartAction_eq hP E (qB u ω) (qB₀ u ω)
    intro f hf
    calc
      fp81s21_chartAction E (qB u ω) f =
          fp81s21_particleQuadField R N A u ω f := hω.1 f hf
      _ = fp81s21_chartAction E (qB₀ u ω) f :=
        (hB₀action u hu ω hpath f hf).symm
  let dt : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) H)
  let gη : ℝ × A.Ω → r26t6_Coeff := fun z => qη (a + z.1) z.2
  let gη₀ : ℝ × A.Ω → r26t6_Coeff := fun z => qη₀ (a + z.1) z.2
  let gB : ℝ × A.Ω → r26t6_Coeff := fun z => qB (a + z.1) z.2
  let gB₀ : ℝ × A.Ω → r26t6_Coeff := fun z => qB₀ (a + z.1) z.2
  have hgη : Measurable gη := by
    change Measurable (Function.uncurry qη ∘
      (fun z : ℝ × A.Ω => (a + z.1, z.2)))
    exact hηrep.1.comp ((measurable_const.add measurable_fst).prodMk measurable_snd)
  have hgη₀ : Measurable gη₀ := by
    change Measurable (Function.uncurry qη₀ ∘
      (fun z : ℝ × A.Ω => (a + z.1, z.2)))
    exact hqη₀meas.comp ((measurable_const.add measurable_fst).prodMk measurable_snd)
  have hgB : Measurable gB := by
    change Measurable (Function.uncurry qB ∘
      (fun z : ℝ × A.Ω => (a + z.1, z.2)))
    exact hBrep.1.comp ((measurable_const.add measurable_fst).prodMk measurable_snd)
  have hgB₀ : Measurable gB₀ := by
    change Measurable (Function.uncurry qB₀ ∘
      (fun z : ℝ × A.Ω => (a + z.1, z.2)))
    exact hqB₀meas.comp ((measurable_const.add measurable_fst).prodMk measurable_snd)
  have hηsecSlab : ∀ᵐ t ∂dt,
      (fun ω => gη (t, ω)) =ᵐ[A.P] (fun ω => gη₀ (t, ω)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hηsection (a + t) (by linarith [ha, ht.1])
  have hBsecSlab : ∀ᵐ t ∂dt,
      (fun ω => gB (t, ω)) =ᵐ[A.P] (fun ω => gB₀ (t, ω)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hBsection (a + t) (by linarith [ha, ht.1])
  have hηeqProd : gη =ᵐ[dt.prod A.P] gη₀ :=
    fp81s21_product_ae_of_section_ae dt A.P gη gη₀ hgη hgη₀ hηsecSlab
  have hBeqProd : gB =ᵐ[dt.prod A.P] gB₀ :=
    fp81s21_product_ae_of_section_ae dt A.P gB gB₀ hgB hgB₀ hBsecSlab
  have hYprod : ∀ᵐ z ∂(dt.prod A.P),
      ∀ t : ℝ, Y (t, z.2) = A.X t.toNNReal z.2 :=
    Measure.quasiMeasurePreserving_snd.ae hYae
  have htprod : ∀ᵐ z ∂(dt.prod A.P), z.1 ∈ Set.Icc (0 : ℝ) H :=
    Measure.quasiMeasurePreserving_fst.ae
      (ae_restrict_mem measurableSet_Icc)
  have hηcompactProd : ∀ᵐ z ∂(dt.prod A.P),
      ∀ f, IsR2Test f →
        fp81s21_chartAction E (qη (a + z.1) z.2) f =
          fp81s21_particleEmpField R N A (a + z.1) z.2 f := by
    filter_upwards [hηeqProd, hYprod, htprod] with z heq hpath ht
    intro f hf
    have heq' : qη (a + z.1) z.2 = qη₀ (a + z.1) z.2 := by
      simpa [gη, gη₀] using heq
    rw [heq']
    exact hη₀action (a + z.1) (by linarith [ha, ht.1]) z.2 hpath f hf
  have hBcompactProd : ∀ᵐ z ∂(dt.prod A.P),
      ∀ f, IsR2Test f →
        fp81s21_chartAction E (qB (a + z.1) z.2) f =
          fp81s21_particleQuadField R N A (a + z.1) z.2 f := by
    filter_upwards [hBeqProd, hYprod, htprod] with z heq hpath ht
    intro f hf
    have heq' : qB (a + z.1) z.2 = qB₀ (a + z.1) z.2 := by
      simpa [gB, gB₀] using heq
    rw [heq']
    exact hB₀action (a + z.1) (by linarith [ha, ht.1]) z.2 hpath f hf
  have hZfixed := hZProducer δ hδ hδz' R N hN A
  have hηZProd : ∀ᵐ z ∂(dt.prod A.P),
      S102Z (2 * p.d + 8) ((p.d : ℝ) + 2)
        (fp81s21_particleEmpField R N A (a + z.1) z.2) := by
    filter_upwards [htprod] with z hz
    exact (hZfixed (a + z.1) (by linarith [ha, hz.1]) z.2).1
  have hBZProd : ∀ᵐ z ∂(dt.prod A.P),
      S102Z (2 * p.d + 8) ((p.d : ℝ) + 2)
        (fp81s21_particleQuadField R N A (a + z.1) z.2) := by
    filter_upwards [htprod] with z hz
    exact (hZfixed (a + z.1) (by linarith [ha, hz.1]) z.2).2
  obtain ⟨Uη, hcoreη⟩ := fp81s21_MomentRep_time_section
    E A.P (fp81s21_particleEmpField R N A) qη M a H hηrep ha (le_of_lt hH)
  obtain ⟨UB, hcoreB⟩ := fp81s21_MomentRep_time_section
    E A.P (fp81s21_particleQuadField R N A) qB M a H hBrep ha (le_of_lt hH)
  have hTimeη := fp81s21_TimeRep_of_TimeL2Rep_product hP E A.P
    (fp81s21_particleEmpField R N A) qη M a H Uη hcoreη hηcompactProd hηZProd
  have hTimeB := fp81s21_TimeRep_of_TimeL2Rep_product hP E A.P
    (fp81s21_particleQuadField R N A) qB M a H UB hcoreB hBcompactProd hBZProd
  refine ⟨qη, qB, hηrep, hBrep, Y, hYmeas, hYae,
    qη₀, qB₀, hqη₀meas, hqB₀meas,
    hηcompactProd, hBcompactProd, hηZProd, hBZProd, ?_⟩
  exact ⟨Uη, UB, hTimeη, hTimeB⟩

#print axioms HRS.Fp81.S21.fp81s21_particle_TimeRep_bridge
#print axioms HRS.Fp81.S21.fp81s21_TimeRep_of_TimeL2Rep_product
#print axioms HRS.Fp81.S21.fp81s21_MomentRep_embedField_weight

end HRS.Fp81.S21

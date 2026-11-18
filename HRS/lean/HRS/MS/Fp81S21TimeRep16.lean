import HRS.MS.Fp81S21TimeRep15
import HRS.MS.Fp81S21EmbedTail
import HRS.MS.Fp81S21EmbedIdent

/-! The final particle export with fixed embedded representatives and
quantitative projection tails. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory
open Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.R2Interp
open HRS.MS.ProClosureS111

local instance (H : ℝ) : MeasurableSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := borel _
local instance (H : ℝ) : BorelSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := ⟨rfl⟩

universe u v w

/-- A projection out of a dependent family commutes with transport. -/
theorem fp81s21_transport_projection
    {α : Sort u} {P : α → Sort v} {Q : α → Sort w}
    (f : ∀ a, P a → Q a) {a b : α} (h : a = b) (x : P a) :
    f b (h ▸ x) = h ▸ f a x := by
  cases h
  rfl

/-- The particle-chart embedding, with the source weight normalized as
`((d + 2) + 2)`. -/
noncomputable def fp81s21_particle_embedField
    (p : Parameters)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2)) :
    r26t6_Coeff →L[ℝ] r26t6_Coeff := by
  have hd : (2 : ℝ) ≤ (p.d : ℝ) := by exact_mod_cast p.hd
  have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by nlinarith
  have hPs : (p.d : ℝ) < 2 * (((p.d : ℝ) + 2) + 2) := by nlinarith
  have hExp : ((p.d : ℝ) + 2) + 2 = (p.d : ℝ) + 4 := by ring
  exact fp81s21_embedField hP hPs (hExp.symm ▸ Es) E

/-- For fixed charts, the same strong particle representatives embed to the
weak chart before the time shift and horizon are chosen. The fixed profile
controls both time-L² projection tails. The strong-chart first moments are
retained for downstream consumers. -/
theorem fp81s21_particle_weakChart_time_tails
    (p : Parameters)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2)) :
    ∃ ε : ℕ → ℝ,
      (∀ m, 0 ≤ ε m) ∧
      Tendsto ε atTop (𝓝 0) ∧
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ R : Trajectory p δ,
          ∃ M : ℝ, 0 ≤ M ∧
            ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N,
              ∃ qsη qsB : ℝ → A.Ω → r26t6_Coeff,
                fp81s21_MomentRep Es A.P
                  (fp81s21_particleEmpField R N A) qsη M ∧
                fp81s21_MomentRep Es A.P
                  (fp81s21_particleQuadField R N A) qsB M ∧
                (∀ u : ℝ, 0 ≤ u →
                  AEMeasurable (fun ω => dualNormE (2 * p.d + 6)
                    ((p.d : ℝ) + 4)
                    (fp81s21_particleEmpField R N A u ω)) A.P ∧
                  (∫⁻ ω, dualNormE (2 * p.d + 6) ((p.d : ℝ) + 4)
                    (fp81s21_particleEmpField R N A u ω) ∂A.P) ≤
                    ENNReal.ofReal (Real.sqrt M)) ∧
                (∀ u : ℝ, 0 ≤ u →
                  AEMeasurable (fun ω => dualNormE (2 * p.d + 6)
                    ((p.d : ℝ) + 4)
                    (fp81s21_particleQuadField R N A u ω)) A.P ∧
                  (∫⁻ ω, dualNormE (2 * p.d + 6) ((p.d : ℝ) + 4)
                    (fp81s21_particleQuadField R N A u ω) ∂A.P) ≤
                    ENNReal.ofReal (Real.sqrt M)) ∧
                let qη : ℝ → A.Ω → r26t6_Coeff :=
                  fun u ω => fp81s21_particle_embedField p Es E (qsη u ω)
                let qB : ℝ → A.Ω → r26t6_Coeff :=
                  fun u ω => fp81s21_particle_embedField p Es E (qsB u ω)
                fp81s21_MomentRep E A.P
                  (fp81s21_particleEmpField R N A) qη M ∧
                fp81s21_MomentRep E A.P
                  (fp81s21_particleQuadField R N A) qB M ∧
                ∀ a : ℝ, 0 ≤ a → ∀ H : ℝ, 0 < H →
                  ∃ Uη UB : A.Ω →
                    Lp r26t6_Coeff 2
                      (volume.restrict (Set.Icc (0 : ℝ) H)),
                    fp81s21_TimeRep E A.P
                      (fp81s21_particleEmpField R N A) qη M a H Uη ∧
                    fp81s21_TimeRep E A.P
                      (fp81s21_particleQuadField R N A) qB M a H UB ∧
                    ∀ m : ℕ,
                      fp81s21_SqErr A.P Uη
                        (fun ω => fp81s21_timeProject H m (Uη ω))
                        (Real.sqrt (H * M) * ε m) ∧
                      fp81s21_SqErr A.P UB
                        (fun ω => fp81s21_timeProject H m (UB ω))
                        (Real.sqrt (H * M) * ε m) := by
  have hd : (2 : ℝ) ≤ (p.d : ℝ) := by exact_mod_cast p.hd
  have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by nlinarith
  have hPs : (p.d : ℝ) < 2 * (((p.d : ℝ) + 2) + 2) := by nlinarith
  have hExp : ((p.d : ℝ) + 2) + 2 = (p.d : ℝ) + 4 := by ring
  let Es' : r26t6_WeightedChart p.d (2 * p.d + 6)
      (((p.d : ℝ) + 2) + 2) := hExp.symm ▸ Es
  let K : r26t6_Coeff →L[ℝ] r26t6_Coeff :=
    fp81s21_embedField hP hPs Es' E
  have hKnorm : ‖K‖ ≤ 1 := by
    change ‖fp81s21_embedField hP hPs Es' E‖ ≤ 1
    calc
      ‖fp81s21_embedField hP hPs Es' E‖ =
          ‖(fp81s21_embedField_primal hP hPs E Es').adjoint‖ := rfl
      _ = ‖fp81s21_embedField_primal hP hPs E Es'‖ :=
        fp81s21_adjoint_opNorm_eq _
      _ ≤ 1 := fp81s21_embedField_primal_norm_le hP hPs E Es'
  obtain ⟨ε, hε, hεlim, hprofile⟩ :=
    fp81s21_embedField_projectionTail hP hPs Es' E
  obtain ⟨δ₀, hδ₀, hδ₀half, hbridge⟩ :=
    fp81s21_particle_TimeRep_bridge p
  refine ⟨ε, hε, hεlim, δ₀, hδ₀, hδ₀half, ?_⟩
  intro δ hδ hδle R
  obtain ⟨M, hM, hMR⟩ := hbridge δ hδ hδle R
  refine ⟨M, hM, ?_⟩
  intro N hN A
  obtain ⟨qsη, qsB, hηsrc, hBsrc, hA⟩ := hMR N hN A Es E
  let Pkgη : ℝ → Type := fun w =>
    PSigma fun Eη : r26t6_WeightedChart p.d (2 * p.d + 6) w =>
      fp81s21_MomentRep Eη A.P (fp81s21_particleEmpField R N A) qsη M
  let hPkgη : Pkgη ((p.d : ℝ) + 4) := ⟨Es, hηsrc⟩
  let hPkgη' : Pkgη (((p.d : ℝ) + 2) + 2) := hExp.symm ▸ hPkgη
  have hηsrc' : fp81s21_MomentRep Es' A.P
      (fp81s21_particleEmpField R N A) qsη M := by
    have hchart : hPkgη'.1 = Es' := by
      have hcast := fp81s21_transport_projection
        (fun w (x : Pkgη w) => x.1) hExp.symm hPkgη
      simpa [hPkgη', hPkgη, Pkgη, Es'] using hcast
    rw [← hchart]
    exact hPkgη'.2
  let PkgB : ℝ → Type := fun w =>
    PSigma fun EB : r26t6_WeightedChart p.d (2 * p.d + 6) w =>
      fp81s21_MomentRep EB A.P (fp81s21_particleQuadField R N A) qsB M
  let hPkgB : PkgB ((p.d : ℝ) + 4) := ⟨Es, hBsrc⟩
  let hPkgB' : PkgB (((p.d : ℝ) + 2) + 2) := hExp.symm ▸ hPkgB
  have hBsrc' : fp81s21_MomentRep Es' A.P
      (fp81s21_particleQuadField R N A) qsB M := by
    have hchart : hPkgB'.1 = Es' := by
      have hcast := fp81s21_transport_projection
        (fun w (x : PkgB w) => x.1) hExp.symm hPkgB
      simpa [hPkgB', hPkgB, PkgB, Es'] using hcast
    rw [← hchart]
    exact hPkgB'.2
  have hηfirst : ∀ u : ℝ, 0 ≤ u →
      AEMeasurable (fun ω => dualNormE (2 * p.d + 6)
        ((p.d : ℝ) + 4) (fp81s21_particleEmpField R N A u ω)) A.P ∧
      (∫⁻ ω, dualNormE (2 * p.d + 6) ((p.d : ℝ) + 4)
        (fp81s21_particleEmpField R N A u ω) ∂A.P) ≤
        ENNReal.ofReal (Real.sqrt M) := by
    intro u hu
    exact fp81s21_MomentRep_firstMoment Es A.P
      (fp81s21_particleEmpField R N A) qsη M hηsrc u hu
  have hBfirst : ∀ u : ℝ, 0 ≤ u →
      AEMeasurable (fun ω => dualNormE (2 * p.d + 6)
        ((p.d : ℝ) + 4) (fp81s21_particleQuadField R N A u ω)) A.P ∧
      (∫⁻ ω, dualNormE (2 * p.d + 6) ((p.d : ℝ) + 4)
        (fp81s21_particleQuadField R N A u ω) ∂A.P) ≤
        ENNReal.ofReal (Real.sqrt M) := by
    intro u hu
    exact fp81s21_MomentRep_firstMoment Es A.P
      (fp81s21_particleQuadField R N A) qsB M hBsrc u hu
  refine ⟨qsη, qsB, hηsrc, hBsrc, hηfirst, hBfirst, ?_⟩
  let qη : ℝ → A.Ω → r26t6_Coeff := fun u ω => K (qsη u ω)
  let qB : ℝ → A.Ω → r26t6_Coeff := fun u ω => K (qsB u ω)
  have hηweak : fp81s21_MomentRep E A.P
      (fp81s21_particleEmpField R N A) qη M := by
    simpa [qη, K, Es'] using
      fp81s21_MomentRep_embedField_weight hP hPs Es hExp.symm E A.P
        (fp81s21_particleEmpField R N A) qsη M hηsrc
  have hBweak : fp81s21_MomentRep E A.P
      (fp81s21_particleQuadField R N A) qB M := by
    simpa [qB, K, Es'] using
      fp81s21_MomentRep_embedField_weight hP hPs Es hExp.symm E A.P
        (fp81s21_particleQuadField R N A) qsB M hBsrc
  refine ⟨hηweak, hBweak, ?_⟩
  intro a ha H hH
  obtain ⟨qηold, qBold, hηold, hBold, hPayload⟩ := hA a ha H hH
  have hηeq := fp81s21_MomentRep_eq_ae hP E A.P
    (fp81s21_particleEmpField R N A) qη qηold M M hηweak hηold
  have hBeq := fp81s21_MomentRep_eq_ae hP E A.P
    (fp81s21_particleQuadField R N A) qB qBold M M hBweak hBold
  obtain ⟨_, _, _, _, _, _, _, hηcompactOld, hBcompactOld,
      hηZ, hBZ, _⟩ := hPayload
  let dt : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) H)
  let gη : ℝ × A.Ω → r26t6_Coeff := fun z => qη (a + z.1) z.2
  let gηold : ℝ × A.Ω → r26t6_Coeff := fun z => qηold (a + z.1) z.2
  let gB : ℝ × A.Ω → r26t6_Coeff := fun z => qB (a + z.1) z.2
  let gBold : ℝ × A.Ω → r26t6_Coeff := fun z => qBold (a + z.1) z.2
  have hgη : Measurable gη := by
    change Measurable (Function.uncurry qη ∘
      (fun z : ℝ × A.Ω => (a + z.1, z.2)))
    exact hηweak.1.comp ((measurable_const.add measurable_fst).prodMk measurable_snd)
  have hgηold : Measurable gηold := by
    change Measurable (Function.uncurry qηold ∘
      (fun z : ℝ × A.Ω => (a + z.1, z.2)))
    exact hηold.1.comp ((measurable_const.add measurable_fst).prodMk measurable_snd)
  have hgB : Measurable gB := by
    change Measurable (Function.uncurry qB ∘
      (fun z : ℝ × A.Ω => (a + z.1, z.2)))
    exact hBweak.1.comp ((measurable_const.add measurable_fst).prodMk measurable_snd)
  have hgBold : Measurable gBold := by
    change Measurable (Function.uncurry qBold ∘
      (fun z : ℝ × A.Ω => (a + z.1, z.2)))
    exact hBold.1.comp ((measurable_const.add measurable_fst).prodMk measurable_snd)
  have hηsec : ∀ᵐ t ∂dt,
      (fun ω => gη (t, ω)) =ᵐ[A.P] (fun ω => gηold (t, ω)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hat : 0 ≤ a + t := by linarith [ha, ht.1]
    simpa [gη, gηold] using hηeq (a + t) hat
  have hBsec : ∀ᵐ t ∂dt,
      (fun ω => gB (t, ω)) =ᵐ[A.P] (fun ω => gBold (t, ω)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hat : 0 ≤ a + t := by linarith [ha, ht.1]
    simpa [gB, gBold] using hBeq (a + t) hat
  have hηeqProd : gη =ᵐ[dt.prod A.P] gηold :=
    fp81s21_product_ae_of_section_ae dt A.P gη gηold hgη hgηold hηsec
  have hBeqProd : gB =ᵐ[dt.prod A.P] gBold :=
    fp81s21_product_ae_of_section_ae dt A.P gB gBold hgB hgBold hBsec
  have hηcompact : ∀ᵐ z ∂(dt.prod A.P),
      ∀ f, IsR2Test f →
        fp81s21_chartAction E (qη (a + z.1) z.2) f =
          fp81s21_particleEmpField R N A (a + z.1) z.2 f := by
    filter_upwards [hηeqProd, hηcompactOld] with z heq hact
    intro f hf
    have heq' : qη (a + z.1) z.2 = qηold (a + z.1) z.2 := by
      simpa [gη, gηold] using heq
    rw [heq']
    exact hact f hf
  have hBcompact : ∀ᵐ z ∂(dt.prod A.P),
      ∀ f, IsR2Test f →
        fp81s21_chartAction E (qB (a + z.1) z.2) f =
          fp81s21_particleQuadField R N A (a + z.1) z.2 f := by
    filter_upwards [hBeqProd, hBcompactOld] with z heq hact
    intro f hf
    have heq' : qB (a + z.1) z.2 = qBold (a + z.1) z.2 := by
      simpa [gB, gBold] using heq
    rw [heq']
    exact hact f hf
  obtain ⟨Uη, hcoreη⟩ := fp81s21_MomentRep_time_section E A.P
    (fp81s21_particleEmpField R N A) qη M a H hηweak ha (le_of_lt hH)
  obtain ⟨UB, hcoreB⟩ := fp81s21_MomentRep_time_section E A.P
    (fp81s21_particleQuadField R N A) qB M a H hBweak ha (le_of_lt hH)
  have hTimeη := fp81s21_TimeRep_of_TimeL2Rep_product hP E A.P
    (fp81s21_particleEmpField R N A) qη M a H Uη hcoreη hηcompact hηZ
  have hTimeB := fp81s21_TimeRep_of_TimeL2Rep_product hP E A.P
    (fp81s21_particleQuadField R N A) qB M a H UB hcoreB hBcompact hBZ
  have htailη : ∀ m u, 0 ≤ u →
      Integrable (fun ω => ‖qη u ω - fp81s21_projectField m (qη u ω)‖ ^ 2) A.P ∧
      (∫ ω, ‖qη u ω - fp81s21_projectField m (qη u ω)‖ ^ 2 ∂A.P) ≤
        M * (ε m) ^ 2 := by
    intro m u hu
    obtain ⟨hi, hb, _⟩ := hprofile A.P
      (fp81s21_particleEmpField R N A) qsη M hηsrc' m u hu
    exact ⟨by simpa [qη, K] using hi, by simpa [qη, K] using hb⟩
  have htailB : ∀ m u, 0 ≤ u →
      Integrable (fun ω => ‖qB u ω - fp81s21_projectField m (qB u ω)‖ ^ 2) A.P ∧
      (∫ ω, ‖qB u ω - fp81s21_projectField m (qB u ω)‖ ^ 2 ∂A.P) ≤
        M * (ε m) ^ 2 := by
    intro m u hu
    obtain ⟨hi, hb, _⟩ := hprofile A.P
      (fp81s21_particleQuadField R N A) qsB M hBsrc' m u hu
    exact ⟨by simpa [qB, K] using hi, by simpa [qB, K] using hb⟩
  have htailTimeη := fp81s21_time_projection_tails A.P qη M a H Uη
    hηweak.1 hcoreη hM ha (le_of_lt hH) ε hε htailη
  have htailTimeB := fp81s21_time_projection_tails A.P qB M a H UB
    hBweak.1 hcoreB hM ha (le_of_lt hH) ε hε htailB
  refine ⟨Uη, UB, hTimeη, hTimeB, ?_⟩
  intro m
  exact ⟨(htailTimeη m).1, (htailTimeB m).1⟩

#print axioms HRS.Fp81.S21.fp81s21_transport_projection
#print axioms HRS.Fp81.S21.fp81s21_particle_embedField
#print axioms HRS.Fp81.S21.fp81s21_particle_weakChart_time_tails

end HRS.Fp81.S21

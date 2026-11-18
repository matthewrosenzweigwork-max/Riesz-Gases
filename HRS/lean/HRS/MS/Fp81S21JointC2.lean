import HRS.MS.Fp81S21JointC
import HRS.MS.Fp81S21JointL3
import HRS.MS.Fp81S21LiftTwoLaw2

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6

namespace HRS.Fp81.S21

local instance fp81s21_jointC2_U_measSpace (H : ℝ) :
    MeasurableSpace (fp81s21_jointP_U H) := borel _
local instance fp81s21_jointC2_U_borelSpace (H : ℝ) :
    BorelSpace (fp81s21_jointP_U H) := ⟨rfl⟩
local instance fp81s21_jointC2_pair_measSpace (H : ℝ) :
    MeasurableSpace (fp81s21_jointP_U H × fp81s21_jointP_U H) := borel _
local instance fp81s21_jointC2_pair_borelSpace (H : ℝ) :
    BorelSpace (fp81s21_jointP_U H × fp81s21_jointP_U H) := ⟨rfl⟩

/-- The actual raw particle fluctuation window used by the L profile. -/
noncomputable def fp81s21_jointC_particleWindow
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) {N : ℕ}
    (A : Particle R N) (H a : ℝ) : A.Ω → fp81s21_jointP_X p H :=
  flucPathW ((wholeSpaceIndex p.d : ℕ) : ℝ) H a
    (Real.sqrt (N : ℝ)) A.X R.ρ

/-- The actual raw Gaussian process window used by the L profile. -/
noncomputable def fp81s21_jointC_gaussianWindow
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (G : GaussianRealization R) (H a : ℝ) : G.Ω → fp81s21_jointP_X p H :=
  processWindow ((wholeSpaceIndex p.d : ℕ) : ℝ) H a G.Z

/-- The fixed growth constant selected by the map-specific 31-P estimate. -/
noncomputable def fp81s21_jointC2_mapConstant {p : Parameters} (H : ℝ) (hH : 0 < H)
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (m : ℕ) (D : Fin m → fp81s21_RankKernel p.d) : ℝ :=
  Classical.choose (fp81s21_jointC_map_local_estimate H hH E m D)

private theorem fp81s21_jointC_law_coordinate_sixth
    {Ω X : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P] (U : Ω → X) (hU : Measurable U)
    (π : Measure (X × X)) (f : X × X → X) (hf : Measurable f)
    (hπ : π.map f = law P U)
    (hπ6 : Integrable (fun z : X × X => ‖f z‖ ^ 6) π) :
    Integrable (fun ω => ‖U ω‖ ^ 6) P := by
  have hmap : Integrable (fun x : X => ‖x‖ ^ 6) (π.map f) := by
    have h := (integrable_map_measure
      (by fun_prop : AEStronglyMeasurable (fun x : X => ‖x‖ ^ 6) (π.map f))
      hf.aemeasurable).mpr hπ6
    simpa only [Function.comp_def] using h
  have hlaw : law P U = P.map U := rfl
  rw [hπ, hlaw] at hmap
  exact (integrable_map_measure
    (by fun_prop : AEStronglyMeasurable (fun x : X => ‖x‖ ^ 6) (P.map U))
    hU.aemeasurable).mp hmap

private theorem fp81s21_jointC_integrable_of_growth
    {Ω X B : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B] [BorelSpace B]
    [SecondCountableTopology B]
    (P : Measure Ω) [IsFiniteMeasure P] (U : Ω → X) (hU : Measurable U)
    (hU6 : Integrable (fun ω => ‖U ω‖ ^ 6) P)
    (F : X → B) (hF : Measurable F) (K : ℝ) (hK : 0 ≤ K)
    (hgrowth : ∀ x, ‖F x‖ ≤ K * (1 + ‖x‖ ^ 2)) :
    Integrable (fun ω => F (U ω)) P := by
  have hbase : Integrable (fun ω => 1 + ‖U ω‖ ^ 6) P :=
    (integrable_const (1 : ℝ)).add hU6
  have hmajor : Integrable (fun ω => 2 * K * (1 + ‖U ω‖ ^ 6)) P := by
    convert hbase.const_mul (2 * K) using 1 <;> ext ω <;> ring
  refine hmajor.mono' (hF.comp hU).aestronglyMeasurable ?_
  filter_upwards with ω
  let x : ℝ := ‖U ω‖
  have hx : 0 ≤ x := norm_nonneg _
  have hx2 : x ^ 2 ≤ 1 + x ^ 6 := by
    by_cases hxle : x ≤ 1
    · have hxSq : x ^ 2 ≤ 1 := by
        calc
          x ^ 2 = x * x := by ring
          _ ≤ 1 * 1 := mul_le_mul hxle hxle hx (by norm_num)
          _ = 1 := by ring
      nlinarith [sq_nonneg (x ^ 3)]
    · have hxge : 1 ≤ x := le_of_not_ge hxle
      have hxSq : 1 ≤ x ^ 2 := by
        calc
          1 = 1 * 1 := by ring
          _ ≤ x * x := mul_le_mul hxge hxge (by norm_num) hx
          _ = x ^ 2 := by ring
      have hxFourth : 1 ≤ x ^ 4 := by
        calc
          1 = 1 * 1 := by ring
          _ ≤ x ^ 2 * x ^ 2 := mul_le_mul hxSq hxSq (by norm_num) (sq_nonneg x)
          _ = x ^ 4 := by ring
      have hxSixth : x ^ 2 ≤ x ^ 6 := by
        calc
          x ^ 2 = x ^ 2 * 1 := by ring
          _ ≤ x ^ 2 * x ^ 4 := mul_le_mul_of_nonneg_left hxFourth (sq_nonneg x)
          _ = x ^ 6 := by ring
      linarith
  have hx6 : 0 ≤ x ^ 6 := by positivity
  have hfac : 1 + x ^ 2 ≤ 2 * (1 + x ^ 6) := by
    calc
      1 + x ^ 2 ≤ 1 + (1 + x ^ 6) := add_le_add_right hx2 1
      _ = 2 + x ^ 6 := by ring
      _ ≤ 2 * (1 + x ^ 6) := by nlinarith [hx6]
  calc
    ‖F (U ω)‖ ≤ K * (1 + ‖U ω‖ ^ 2) := hgrowth (U ω)
    _ ≤ K * (2 * (1 + ‖U ω‖ ^ 6)) := by
      exact mul_le_mul_of_nonneg_left (by simpa [x] using hfac) hK
    _ = 2 * K * (1 + ‖U ω‖ ^ 6) := by ring

/-- Physical cutoff instantiation for the actual joint particle and Gaussian
outputs. The law-specific `SqErr` bounds remain explicit inputs until units N
and G provide them; the raw coupling comes with the positive slack supplied by
unit L, which is removed by continuity of the cutoff profile. -/
theorem fp81s21_jointC_physical_cutoff
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N) (G : GaussianRealization R)
    (H : ℝ) (hH : 0 < H)
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (m : ℕ) (D : Fin m → fp81s21_RankKernel p.d)
    (a : ℝ) (ha : 0 ≤ a)
    (actualJointN : A.Ω → fp81s21_jointP_U H × fp81s21_jointP_U H)
    (actualJointG : G.Ω → fp81s21_jointP_U H × fp81s21_jointP_U H)
    (hU₁ : Measurable (fp81s21_jointC_particleWindow p R A H a))
    (hU₂ : Measurable (fp81s21_jointC_gaussianWindow p R G H a))
    (hV₁ : Measurable actualJointN) (hV₂ : Measurable actualJointG)
    (τN τG : ℝ) (hτN : 0 ≤ τN) (hτG : 0 ≤ τG)
    (d : ℕ → ℝ) (hd : fp81s21_NonnegativeVanishing d)
    (Mpath : ℝ) (hMpath : 0 ≤ Mpath)
    (Rcut : ℝ) (hRcut : 1 ≤ Rcut)
    (hNerr : fp81s21_SqErr A.P actualJointN
      (fun ω => fp81s21_jointP_map H hH E m D
          (fp81s21_jointC_particleWindow p R A H a ω) -
        fp81s21_jointC_partialCenter H
          (∫ ω', fp81s21_jointP_map H hH E m D
            (fp81s21_jointC_particleWindow p R A H a ω') ∂A.P)) τN)
    (hGerr : fp81s21_SqErr G.P actualJointG
      (fun ω => fp81s21_jointP_map H hH E m D
          (fp81s21_jointC_gaussianWindow p R G H a ω) -
        fp81s21_jointC_partialCenter H
          (∫ ω', fp81s21_jointP_map H hH E m D
            (fp81s21_jointC_gaussianWindow p R G H a ω') ∂G.P)) τG)
    (hL : ∀ ε : ℝ, 0 < ε →
      ∃ π : Measure (fp81s21_jointP_X p H × fp81s21_jointP_X p H),
        IsProbabilityMeasure π ∧
        π.map Prod.fst = law A.P (fp81s21_jointC_particleWindow p R A H a) ∧
        π.map Prod.snd = law G.P (fp81s21_jointC_gaussianWindow p R G H a) ∧
        Integrable (fun z => ‖z.1‖ ^ 6) π ∧
        Integrable (fun z => ‖z.2‖ ^ 6) π ∧
        (∫ z, ‖z.1‖ ^ 6 ∂π) ≤ Mpath ∧
        (∫ z, ‖z.2‖ ^ 6 ∂π) ≤ Mpath ∧
        Integrable (fun z => ‖z.1 - z.2‖) π ∧
        (∫ z, ‖z.1 - z.2‖ ∂π) ≤ d N + ε) :
    wassersteinE 2 (law A.P actualJointN) (law G.P actualJointG) ≤
      ENNReal.ofReal (τN + τG + 2 * Real.sqrt
        ((fp81s21_jointC2_mapConstant H hH E m D) ^ 2 *
          ((1 + 2 * Rcut) ^ 2 * (2 * Rcut) * d N +
          64 * (1 + Mpath) / Rcut ^ 2))) := by
  let K := fp81s21_jointC2_mapConstant H hH E m D
  have hspec := Classical.choose_spec
    (fp81s21_jointC_map_local_estimate H hH E m D)
  have hK : 0 ≤ K := by simpa [K, fp81s21_jointC2_mapConstant] using hspec.1
  have hF : Measurable (fp81s21_jointP_map H hH E m D) := by
    simpa [fp81s21_jointC2_mapConstant] using hspec.2.1
  have hgrowth : ∀ x, ‖fp81s21_jointP_map H hH E m D x‖ ≤ K * (1 + ‖x‖ ^ 2) := by
    simpa [K, fp81s21_jointC2_mapConstant] using hspec.2.2.1
  have hlip : ∀ x y, ‖fp81s21_jointP_map H hH E m D x -
      fp81s21_jointP_map H hH E m D y‖ ≤
        K * (1 + ‖x‖ + ‖y‖) * ‖x - y‖ := by
    simpa [K, fp81s21_jointC2_mapConstant] using hspec.2.2.2
  let F : fp81s21_jointP_X p H → fp81s21_jointP_U H × fp81s21_jointP_U H :=
    fp81s21_jointP_map H hH E m D
  have hF' : Measurable F := by simpa [F] using hF
  have hgrowth' : ∀ x, ‖F x‖ ≤ K * (1 + ‖x‖ ^ 2) := by
    simpa [F] using hgrowth
  have hlip' : ∀ x y, ‖F x - F y‖ ≤
      K * (1 + ‖x‖ + ‖y‖) * ‖x - y‖ := by
    simpa [F] using hlip
  let U₁ := fp81s21_jointC_particleWindow p R A H a
  let U₂ := fp81s21_jointC_gaussianWindow p R G H a
  let Q := fp81s21_jointC_partialCenter H
  have hQ : ‖Q‖ ≤ 1 := by
    simpa [Q] using fp81s21_jointC_partialCenter_norm_le_one H
  let cutoff : ℝ → ℝ := fun t =>
    τN + τG + 2 * Real.sqrt
      (K ^ 2 * ((1 + 2 * Rcut) ^ 2 * (2 * Rcut) * t +
        64 * (1 + Mpath) / Rcut ^ 2))
  have hcutoff_nonneg (t : ℝ) : 0 ≤ cutoff t := by
    dsimp [cutoff]
    positivity
  have hcutoff_cont : Continuous cutoff := by
    dsimp [cutoff]
    fun_prop
  have hshift : Tendsto (fun ε : ℝ => d N + ε) (𝓝[>] (0 : ℝ)) (𝓝 (d N)) := by
    have hconst : Tendsto (fun _ : ℝ => d N) (𝓝[>] (0 : ℝ)) (𝓝 (d N)) :=
      tendsto_const_nhds
    have hid : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    simpa using hconst.add hid
  have hprofileLim :
      Tendsto (fun ε : ℝ => ENNReal.ofReal (cutoff (d N + ε)))
        (𝓝[>] (0 : ℝ)) (𝓝 (ENNReal.ofReal (cutoff (d N)))) := by
    exact (ENNReal.continuous_ofReal.comp hcutoff_cont).continuousAt.tendsto.comp hshift
  have hboundFor (ε : ℝ) (hε : 0 < ε) :
      wassersteinE 2 (law A.P actualJointN) (law G.P actualJointG) ≤
        ENNReal.ofReal (cutoff (d N + ε)) := by
    obtain ⟨π, hπ, hπ₁, hπ₂, hfst6, hsnd6, hfstM, hsndM, hcostInt, hcost⟩ :=
      hL ε hε
    letI : IsProbabilityMeasure π := hπ
    have hU₁6 : Integrable (fun ω => ‖U₁ ω‖ ^ 6) A.P :=
      fp81s21_jointC_law_coordinate_sixth A.P U₁ hU₁ π Prod.fst measurable_fst hπ₁ hfst6
    have hU₂6 : Integrable (fun ω => ‖U₂ ω‖ ^ 6) G.P :=
      fp81s21_jointC_law_coordinate_sixth G.P U₂ hU₂ π Prod.snd measurable_snd hπ₂ hsnd6
    have hF₁ : Integrable (fun ω => F (U₁ ω)) A.P :=
      fp81s21_jointC_integrable_of_growth A.P U₁ hU₁ hU₁6 F hF' K hK hgrowth'
    have hF₂ : Integrable (fun ω => F (U₂ ω)) G.P :=
      fp81s21_jointC_integrable_of_growth G.P U₂ hU₂ hU₂6 F hF' K hK hgrowth'
    have hcut := fp81s21_liftTwoLaw_cutoff
      A.P G.P U₁ U₂ actualJointN actualJointG F Q
      hU₁ hU₂ hV₁ hV₂ hF' hQ K Mpath (d N + ε) Rcut τN τG
      hK hRcut hτN hτG hgrowth' hlip' hF₁ hF₂ π hπ₁ hπ₂
      hfst6 hsnd6 hfstM hsndM hcost
      hNerr.1 hNerr.2 hGerr.1 hGerr.2
    simpa [cutoff] using hcut
  have hbound : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      wassersteinE 2 (law A.P actualJointN) (law G.P actualJointG) ≤
        ENNReal.ofReal (cutoff (d N + ε)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hboundFor ε hε
  have hWfinite :
      wassersteinE 2 (law A.P actualJointN) (law G.P actualJointG) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hboundFor 1 (by norm_num))
  have hboundReal : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      (wassersteinE 2 (law A.P actualJointN) (law G.P actualJointG)).toReal ≤
        cutoff (d N + ε) := by
    filter_upwards [hbound] with ε hε
    have hmono := ENNReal.toReal_mono ENNReal.ofReal_ne_top hε
    rw [ENNReal.toReal_ofReal (hcutoff_nonneg (d N + ε))] at hmono
    exact hmono
  have hlimitReal :
      (wassersteinE 2 (law A.P actualJointN) (law G.P actualJointG)).toReal ≤
        cutoff (d N) :=
    le_of_tendsto_of_tendsto tendsto_const_nhds
      (hcutoff_cont.continuousAt.tendsto.comp hshift) hboundReal
  apply (ENNReal.toReal_le_toReal hWfinite ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (hcutoff_nonneg (d N))]
  exact hlimitReal

#print axioms fp81s21_jointC_physical_cutoff

end HRS.Fp81.S21

end

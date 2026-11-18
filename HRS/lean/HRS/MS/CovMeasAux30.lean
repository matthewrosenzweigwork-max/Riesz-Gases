import HRS.MS.CovMeasAux29

/-!
# S10.1 (worker S101B), part 30: the proof of `r2_covariance_measure` (statement repeated verbatim; tie in `CovMeasTie.lean`)
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.CovMeas

open HRS HRS.Whole HRS.MS.Go HRS.MS.FixEq HRS.Uniform HRS.Uniform.Q45 HRS.MS.GenPath HRS.MS.U9
open Classical

variable {d : ℕ}

theorem r2_covariance_measure_proof (hd : 2 ≤ d) (C : WholeCoeff d) (m T : ℝ) (hT : 0 < T) (r : ℕ) (Pw : ℝ)
    (hP : (d : ℝ) / 2 < Pw) (horb : R2OrbitSummable C m T r)
    (hlin : ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ T → ∀ φ ψ : Euc d → ℝ, ∀ c : ℝ, IsR2DualCombo m φ → IsR2DualCombo m ψ →
      propagatorW C u t (φ + c • ψ) = propagatorW C u t φ + c • propagatorW C u t ψ) :
    ∃ (K : ℝ) (Jm : (ℝ → (Euc d → ℝ) → ℝ) → ℝ → ℝ → projTensor (OscPath d m T) 2),
      (∀ z z', IsR2L1F r Pw T z → IsR2L1F r Pw T z' → R2JIntegrandMeas C m T z → R2JIntegrandMeas C m T z' →
        ∀ a a', Jm (z + z') a a' = Jm z a a' + Jm z' a a') ∧
      (∀ (c : ℝ) z, IsR2L1F r Pw T z → R2JIntegrandMeas C m T z → ∀ a a', Jm (c • z) a a' = c • Jm z a a') ∧
      ∀ z, IsR2L1F r Pw T z → R2JIntegrandMeas C m T z →
        (∀ a b c, 0 ≤ a → a ≤ b → b ≤ c → c ≤ T → Jm z a c = Jm z a b + Jm z b c) ∧
        (∀ a, Jm z a a = 0) ∧ ContinuousOn (fun u => Jm z 0 u) (Set.Icc 0 T) ∧
        eVariationOn (fun u => Jm z 0 u) (Set.Icc 0 T) ≤
          ENNReal.ofReal K * ∫⁻ u in Set.Icc (0 : ℝ) T, dualNormE r Pw (z u) ∧
        ∀ a a', 0 ≤ a → a ≤ a' → a' ≤ T →
          IsR2JValue C m T z (Set.Ioc a a') (Jm z a a') := by
  have hd1 : 1 ≤ d := by omega
  have hT0 : 0 ≤ T := hT.le
  have hP' : (d : ℝ) < 2 * Pw := by
    have : (d : ℝ) / 2 < Pw := hP
    linarith
  obtain ⟨C0, hC0, hCm⟩ := HRS.Uniform.covariance_measure_proof T 1 hT0
  obtain ⟨J, hJ1, hJ2⟩ := hCm (KSpace d m T) (KSpace d m T) (s56_idEvol (KSpace d m T))
    (s56_idEvol_maxHyp T)
  have hJ : S101Jprops T C0 J :=
    ⟨fun D hD => (hJ1 D hD).1, fun D hD => (hJ1 D hD).2.2.1, fun D hD => (hJ1 D hD).2.2.2.1,
      fun D hD => (hJ1 D hD).2.2.2.2, hJ2⟩
  obtain ⟨K0, hK0, hK⟩ := s101_D_data hd1 hP' horb
  set n2 : ℝ := ‖(s56_reconCLM hT0 : PathSp T (KSpace d m T) →L[ℝ] OscPath d m T)‖ ^ 2 with hn2
  have hn2nn : 0 ≤ n2 := by positivity
  refine ⟨n2 * C0 * |2 * C.ν| * K0, s101Jm hT0 J C r Pw, ?_, ?_, ?_⟩
  · -- additivity in `z`
    intro z z' hz hz' hm hm' a a'
    have h1 := s101_admP_of_L1F hd1 hP' horb hT0 hz hm
    have h2 := s101_admP_of_L1F hd1 hP' horb hT0 hz' hm'
    have h3 := h1.add hd1 hP' horb hT0 h2
    have A1 := h1.adm hd1 hP' horb
    have A2 := h2.adm hd1 hP' horb
    have A3 := h3.adm hd1 hP' horb
    have TD1 := s101_Dm_isTraceDensity A1 hT0 h1.2.2
    have TD2 := s101_Dm_isTraceDensity A2 hT0 h2.2.2
    have TD3 := s101_Dm_isTraceDensity A3 hT0 h3.2.2
    apply Subtype.ext
    rw [Submodule.coe_add, s101Jm_coe h3, s101Jm_coe h1, s101Jm_coe h2]
    have hJeq : J (s101Dm C m T (z + z')) (Ioc a a') =
        J (s101Dm C m T z) (Ioc a a') + J (s101Dm C m T z') (Ioc a a') := by
      rw [s101_J_congr hJ TD3 (s101_isTraceDensity_comb TD1 TD2 1 1) (by
        filter_upwards [s101_Dm_ae_add A1 A2 hT0] with τ h
        rw [h]; simp) measurableSet_Ioc]
      have := hJ.lin (s101Dm C m T z) (s101Dm C m T z') TD1 TD2 1 1 (Ioc a a') measurableSet_Ioc
      simpa using this
    show s101Psi hT0 (J (s101Dm C m T (z + z')) (Ioc a a')) =
      s101Psi hT0 (J (s101Dm C m T z) (Ioc a a')) + s101Psi hT0 (J (s101Dm C m T z') (Ioc a a'))
    rw [hJeq, s101Psi_add]
  · -- homogeneity
    intro c z hz hm a a'
    have h1 := s101_admP_of_L1F hd1 hP' horb hT0 hz hm
    have h3 := h1.smul hd1 hP' horb hT0 c
    have A1 := h1.adm hd1 hP' horb
    have A3 := h3.adm hd1 hP' horb
    have TD1 := s101_Dm_isTraceDensity A1 hT0 h1.2.2
    have TD3 := s101_Dm_isTraceDensity A3 hT0 h3.2.2
    apply Subtype.ext
    rw [Submodule.coe_smul, s101Jm_coe h3, s101Jm_coe h1]
    have hJeq : J (s101Dm C m T (c • z)) (Ioc a a') = c • J (s101Dm C m T z) (Ioc a a') := by
      rw [s101_J_congr hJ TD3 (s101_isTraceDensity_comb TD1 TD1 c 0) (by
        filter_upwards [s101_Dm_ae_smul c A1 hT0] with τ h
        rw [h]; simp) measurableSet_Ioc]
      have := hJ.lin (s101Dm C m T z) (s101Dm C m T z) TD1 TD1 c 0 (Ioc a a') measurableSet_Ioc
      simpa using this
    show s101Psi hT0 (J (s101Dm C m T (c • z)) (Ioc a a')) = c • s101Psi hT0 (J (s101Dm C m T z) (Ioc a a'))
    rw [hJeq, s101Psi_smul]
  · intro z hz hm
    have h1 := s101_admP_of_L1F hd1 hP' horb hT0 hz hm
    have A1 := h1.adm hd1 hP' horb
    have TD1 := s101_Dm_isTraceDensity A1 hT0 h1.2.2
    have hcoe : ∀ a a', ((s101Jm hT0 J C r Pw z a a' : projTensor (OscPath d m T) 2) :
        TensorDual (OscPath d m T) 2) = s101Jx hT0 J (s101Dm C m T z) (Ioc a a') := s101Jm_coe h1
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro a b c ha hab hbc hcT
      apply Subtype.ext
      rw [Submodule.coe_add, hcoe, hcoe, hcoe]
      exact s101Jx_Ioc_add hT0 J _ hab hbc
    · intro a
      apply Subtype.ext
      rw [hcoe, Submodule.coe_zero]
      exact s101Jx_Ioc_self hT0 J _ a
    · refine Topology.IsEmbedding.subtypeVal.continuousOn_iff.2 ?_
      refine (s101_Jx_Ioc0_cont hT0 hJ TD1).congr fun u _ => ?_
      exact hcoe 0 u
    · -- total variation
      unfold eVariationOn
      refine iSup_le fun p => ?_
      obtain ⟨n, u, hu, hmem⟩ := p
      have hstep : ∀ i, edist (s101Jm hT0 J C r Pw z 0 (u (i + 1))) (s101Jm hT0 J C r Pw z 0 (u i)) =
          ‖s101Jx hT0 J (s101Dm C m T z) (Ioc (u i) (u (i + 1)))‖ₑ := by
        intro i
        rw [edist_eq_enorm_sub]
        have hui0 : 0 ≤ u i := (hmem i).1
        have hle : u i ≤ u (i + 1) := hu (Nat.le_succ i)
        have : ((s101Jm hT0 J C r Pw z 0 (u (i + 1)) - s101Jm hT0 J C r Pw z 0 (u i) :
            projTensor (OscPath d m T) 2) : TensorDual (OscPath d m T) 2) =
            s101Jx hT0 J (s101Dm C m T z) (Ioc (u i) (u (i + 1))) := by
          rw [Submodule.coe_sub, hcoe, hcoe, s101Jx_Ioc_add hT0 J _ hui0 hle]
          abel
        rw [← this]
        rfl
      simp_rw [hstep]
      refine (s101_Jx_tv hT0 (C0 := C0) (J := J) (s101Dm C m T z) n u hu hmem).trans ?_
      calc ENNReal.ofReal n2 * (J (s101Dm C m T z)).variation (Icc 0 T)
          ≤ ENNReal.ofReal n2 * (ENNReal.ofReal C0 * ∫⁻ r' in Icc (0 : ℝ) T,
              ENNReal.ofReal (HRS.traceNormForm (s101Dm C m T z r'))) :=
            mul_le_mul' le_rfl (hJ.tv _ TD1)
        _ ≤ ENNReal.ofReal n2 * (ENNReal.ofReal C0 * ∫⁻ r' in Icc (0 : ℝ) T,
              ENNReal.ofReal |2 * C.ν| * ENNReal.ofReal K0 * dualNormE r Pw (z r')) := by
            refine mul_le_mul' le_rfl (mul_le_mul' le_rfl ?_)
            exact setLIntegral_mono' measurableSet_Icc (s101_Dm_trace_bound' A1 hT0
              (fun τ hτ => (hK z hz.1 τ hτ).2.2.2))
        _ = ENNReal.ofReal (n2 * C0 * |2 * C.ν| * K0) * ∫⁻ r' in Icc (0 : ℝ) T, dualNormE r Pw (z r') := by
            rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
            rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
              ENNReal.ofReal_mul (by positivity)]
            ring
    · intro a a' ha haa' ha'T
      refine ⟨(s101Jm hT0 J C r Pw z a a').2, ?_⟩
      intro ta tb φa φb l₁ l₂ hφa hφb hta htb h₁ h₂
      obtain ⟨Sa, ca, rfl⟩ := hφa
      obtain ⟨Sb, cb, rfl⟩ := hφb
      rw [hcoe]
      exact s101_Jx_eval hlin A1 hT0 h1.2.2 hJ measurableSet_Ioc hta htb Sa Sb ca cb l₁ l₂ h₁ h₂

end HRS.MS.CovMeas

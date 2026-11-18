import HRS.MC.E213U16j
import HRS.MC.E213U5b
import HRS.MC.E213U18o

/-!
# Packet e213u19 (part a): the decomposition of the Gaussian window `Z_a = I_a η^0 + R_a Γ_0`

For a bounded continuous `G` on the path space,
`E G(Z_a) = ∫∫ G(I_a F + R_a z) dγ_0(z) d(law η^0)(F)` (`γ_0 = canonFut (a+T) 0`): `Z_a = R_a Z`, `Z = 𝖳_0 Z + Γ_0`,
`R_a 𝖳_0 Z = I_a η^0`, and `Γ_0` is independent of `η^0` with law `γ_0` (future independence, packet e213u16).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213U19

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213U16 HRS.MC.E213U10

variable {d : ℕ}

section Decomp

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

/-- `𝖳_0 w = 𝖨 (w(0))`. -/
theorem u19_predicted_zero (H : ℝ) (hH : 0 < H) {ω : gd.Ω₀}
    (hc : ContinuousOn (fun t => gd.η t ω) (Set.Icc 0 H)) :
    predicted (regime S β₀ hE).D (regime S β₀ hE).ρ (gd.Zwin H 0 ω) 0 =
      initProp (regime S β₀ hE).D (regime S β₀ hE).ρ m H (NegSobolev.embed m (gd.η 0 ω)) := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) H := ⟨le_rfl, hH.le⟩
  obtain ⟨J, k, hk, hJ, hm0, hm1, Hy⟩ := HRS.MC.Sec7.S7PIS1.S7PIS1_data (regime S β₀ hE) m hE.m_gt H hH
  have hdiag : ∀ F : NegSobolev d m, Vprop (regime S β₀ hE).D (regime S β₀ hE).ρ m 0 0 F = F := fun F =>
    HRS.MC.Sec7.S7PIS1.S7PIS1_Vdiag Hy m k hk hJ hm0 hm1 le_rfl hH.le F
  have hfacts := HRS.MC.Sec7.S7PIS1.s7_PIS_path_facts_proof (regime S β₀ hE) m hE.m_gt H hH
  refine u10_path_ext fun t ht => ?_
  rw [hfacts.1 _ 0 t h0 ht, hfacts.2.1 _ t ht]
  by_cases h : t ≤ 0
  · have : t = 0 := le_antisymm h ht.1
    subst this
    rw [u16_Z_at gd hH hc h0, hdiag]
    exact if_pos le_rfl
  · rw [u16_Z_at gd hH hc h0]
    exact if_neg h

/-- Pathwise decomposition `Z_a = I_a η^0 + R_a Γ_0` (a.s.). -/
theorem u19_Za_decomp (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) :
    ∀ᵐ ω ∂gd.P₀, gd.Zwin T a ω =
      Iwin S β₀ hE T a (gd.η 0 ω) + winRestr a ha (Gam gd (a + T) 0 ω) := by
  have hH : 0 < a + T := by linarith
  filter_upwards [u16_Zwin_restr gd T hT a ha, HRS.MC.E213U11.u11_eta_cont gd (a + T)] with ω h1 hc
  rw [h1]
  have h2 : gd.Zwin (a + T) 0 ω = predicted (regime S β₀ hE).D (regime S β₀ hE).ρ (gd.Zwin (a + T) 0 ω) 0 +
      Gam gd (a + T) 0 ω := by
    unfold Gam; abel
  rw [h2, map_add, u19_predicted_zero gd (a + T) hH hc]
  congr 1
  rw [HRS.MC.E213U18.u18_Iwin_eq T a ha,
    initWinFun_eq_winRestr_initProp (regime S β₀ hE).D (regime S β₀ hE).ρ m (rLvl d) T a ha _
      (HRS.MC.E213O.vprop_continuousOn_zero S β₀ hE m (a + T) hH.le _)]

/-- The law of `Z_a` is the image of `law η^0 ⊗ γ_0` under `(F, z) ↦ I_a F + R_a z`. -/
theorem u19_decomp (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) {G : PathSpace d m T → ℝ}
    (hG : Continuous G) (C : ℝ) (hC : ∀ w, |G w| ≤ C) :
    ∫ ω, G (gd.Zwin T a ω) ∂gd.P₀ =
      ∫ F, ∫ z, G (Iwin S β₀ hE T a F + winRestr a ha z) ∂(canonFut hE (a + T) 0)
        ∂(gd.P₀.map (gd.η 0)) := by
  have hH : 0 < a + T := by linarith
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (a + T) := ⟨le_rfl, hH.le⟩
  have hη : Measurable (gd.η 0) := u16_eta_meas gd 0
  have hγ : AEMeasurable (Gam gd (a + T) 0) gd.P₀ := u16_Gam_aemeasurable gd (a + T) hH h0
  have hv : ∃ v', Measurable[pastSig gd 0] v' ∧ gd.η 0 =ᵐ[gd.P₀] v' := by
    refine u16_neg_meas (μ := gd.P₀) (pastSig gd 0) fun ψ hψ => ?_
    exact ⟨Xs gd 0 (⟨0, le_rfl, le_rfl⟩, ⟨ψ, hψ⟩), pastSig_meas_Xs gd 0 _, Filter.Eventually.of_forall fun ω => rfl⟩
  have hindep : IndepFun (gd.η 0) (Gam gd (a + T) 0) gd.P₀ :=
    u16_indepFun_of_sig gd hH h0 hv (u16_Gam_fut gd hH h0)
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map hη.aemeasurable hγ).1 hindep
  rw [u16_Gam_law gd hH h0] at hprod
  set g : NegSobolev d (rLvl d) × PathSpace d m (a + T) → ℝ :=
    fun p => G (Iwin S β₀ hE T a p.1 + winRestr a ha p.2) with hg
  have hgc : Continuous g := hG.comp (((Iwin S β₀ hE T a).continuous.comp continuous_fst).add
    ((winRestr a ha).continuous.comp continuous_snd))
  haveI : IsProbabilityMeasure (canonFut hE (a + T) 0) := by
    rw [← u16_Gam_law gd hH h0]
    exact (Measure.isProbabilityMeasure_map_iff hγ).2 inferInstance
  calc ∫ ω, G (gd.Zwin T a ω) ∂gd.P₀
      = ∫ ω, g (gd.η 0 ω, Gam gd (a + T) 0 ω) ∂gd.P₀ :=
        integral_congr_ae ((u19_Za_decomp gd T hT a ha).mono fun ω hω => by beta_reduce; rw [hω])
    _ = ∫ p, g p ∂(gd.P₀.map fun ω => (gd.η 0 ω, Gam gd (a + T) 0 ω)) :=
        (integral_map (hη.aemeasurable.prodMk hγ) hgc.aestronglyMeasurable).symm
    _ = ∫ p, g p ∂((gd.P₀.map (gd.η 0)).prod (canonFut hE (a + T) 0)) := by rw [hprod]
    _ = _ := by
        haveI : IsProbabilityMeasure (gd.P₀.map (gd.η 0)) := (Measure.isProbabilityMeasure_map_iff hη.aemeasurable).2 inferInstance
        refine integral_prod _ (Integrable.of_bound hgc.aestronglyMeasurable C (Filter.Eventually.of_forall fun p => ?_))
        simpa using hC _

end Decomp

end HRS.MC.E213U19

end

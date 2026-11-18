import HRS.Appendix.B15Aux1
import HRS.Appendix.B15Final
import HRS.Appendix.CepaFlow
import HRS.Appendix.FDL
import HRS.Commutator.Whole.Bridge
import HRS.Duality.PairingExpansionRd
import HRS.Dynamics.Setup
import HRS.Dynamics.SetupFiltered
import HRS.Energy.Coercivity
import HRS.Energy.Commutator.Assembly
import HRS.Energy.Commutator.CommonProof
import HRS.Energy.FeatureMap
import HRS.Energy.G336C1Final
import HRS.Energy.G336Final
import HRS.Energy.KIDFinal
import HRS.Equilibrium.CavityMain
import HRS.Equilibrium.L48Aux5
import HRS.Equilibrium.L49Aux15
import HRS.Equilibrium.NormalFormProof
import HRS.Equilibrium.PairCorrection
import HRS.Equilibrium.PairMoments
import HRS.Equilibrium.PairPoissonFull
import HRS.Equilibrium.Parametrix.Assembly
import HRS.Equilibrium.Parametrix.FullAssembly
import HRS.Equilibrium.PinComparison
import HRS.Equilibrium.PinLinf
import HRS.Equilibrium.PoleCavity
import HRS.Equilibrium.ProductTransfer
import HRS.Equilibrium.QuadraticLimit.Assembly
import HRS.Equilibrium.Response
import HRS.Equilibrium.ResponseSubGaussian
import HRS.Equilibrium.StaticLimits
import HRS.Equilibrium.TRRFinal
import HRS.Equilibrium.TaylorAux8
import HRS.Equilibrium.TripleCanonical
import HRS.MC.CUB2
import HRS.MC.CepB13
import HRS.MC.CepB2
import HRS.MC.CepH5FinProof
import HRS.MC.CepP6
import HRS.MC.CrossCovP6
import HRS.MC.D1ASM
import HRS.MC.D3EAsm
import HRS.MC.D3TAsm
import HRS.MC.D47
import HRS.MC.D4R
import HRS.MC.E213Final
import HRS.MC.E214P6
import HRS.MC.E214T2
import HRS.MC.E214U
import HRS.MC.E718A
import HRS.MC.E718B7
import HRS.MC.L5566
import HRS.MC.Q714AsmFrozen
import HRS.MC.QRAsmFinal
import HRS.MC.S7Chaos
import HRS.MC.S7FCZ
import HRS.MC.S7PIZ
import HRS.MC.S7S16f
import HRS.MC.S7S7f
import HRS.MC.S7UCZ2
import HRS.MC.SEdgeB14
import HRS.MC.SEdgeU4
import HRS.MD.Cov211
import HRS.MD.LT337Final
import HRS.ME.BiasUC
import HRS.ME.CondExampleFinal
import HRS.ME.CosineTiltFinal
import HRS.ME.CritCenteredPathProved
import HRS.ME.CritNeZeroTie
import HRS.ME.FamUFinal
import HRS.ME.FamWFinal
import HRS.ME.FamXC
import HRS.ME.FamXFinal
import HRS.ME.Tie417
import HRS.ME.UIEntropyFrozen
import HRS.ME.UIFinal
import HRS.ME.UIPath
import HRS.ME.UIPathInitialP6
import HRS.ME.UIPathShiftedP6
import HRS.ME.UIPathTightP6
import HRS.ME.UnifP8A
import HRS.MH.CoercTestW7e
import HRS.MH.CommSuperCS10
import HRS.MH.CondOuFinal
import HRS.MH.ConventionHolder1
import HRS.MH.ConventionHolder2
import HRS.MH.ConventionHolder3
import HRS.MH.DualityRdFinal
import HRS.MH.EdgeSharpFinal
import HRS.MH.EdgeworthSharp
import HRS.MH.FeatureMap2
import HRS.MH.FeatureMap3
import HRS.MH.FeatureMap4
import HRS.MH.FilteredSF11
import HRS.MH.FilteredSF12
import HRS.MH.FilteredSF13
import HRS.MH.MfclA12
import HRS.MH.NoLowerBound2
import HRS.MH.PairingRdFinal
import HRS.MH.ScreenedAsmCommCell
import HRS.MH.ScreenedAsmCommLocal
import HRS.MH.ScreenedAsmLocal
import HRS.MH.ScreenedAsmPairing
import HRS.MH.ScreenedAsmPairingPos
import HRS.MH.ScreenedFarAsm
import HRS.MH.WpP6
import HRS.MP.A11Assembly
import HRS.MP.FidiAssembly
import HRS.MP.InitAssemble
import HRS.MP.KernIncr
import HRS.MP.KolmChentsov
import HRS.MP.LimitGauss
import HRS.MP.PathTightCrit
import HRS.MP.PropIncr
import HRS.MP.RdInitClose
import HRS.MP.RdInitLimitClose
import HRS.MP.RdMartingaleClose
import HRS.MP.RdPropAssemble
import HRS.MP.RdRemainder
import HRS.MP.RemainderSup
import HRS.MP.SelfSimFinal
import HRS.MS.AdjDecay
import HRS.MS.AdjSubTie
import HRS.MS.AdmThm
import HRS.MS.Asm15Aux2
import HRS.MS.Asm15Tie
import HRS.MS.BilipV
import HRS.MS.CanThm
import HRS.MS.Comm
import HRS.MS.CondDens
import HRS.MS.CovMeasAux30
import HRS.MS.CritPathTie
import HRS.MS.CritWholeMarginal
import HRS.MS.CzElemAux4
import HRS.MS.CzElemBAux2
import HRS.MS.DecStatTie
import HRS.MS.DerCorAux2
import HRS.MS.EucRegH
import HRS.MS.FeatDecTie
import HRS.MS.FinNoiseTie
import HRS.MS.FixEqTie
import HRS.MS.GapExt
import HRS.MS.GoFeatAux2
import HRS.MS.IidInitTie
import HRS.MS.IidPathTie
import HRS.MS.Ker1
import HRS.MS.LcFinal
import HRS.MS.LimFieldTie
import HRS.MS.LogBnd
import HRS.MS.LogReg
import HRS.MS.MainRdFieldTie
import HRS.MS.MainRdPathAux26
import HRS.MS.MainRdStatFourier
import HRS.MS.MainRdStatTie
import HRS.MS.MfeConfAux174
import HRS.MS.MfeConfAux190
import HRS.MS.Mov63Tie
import HRS.MS.MovAdjTie
import HRS.MS.MovEntFinal
import HRS.MS.MovForceTie
import HRS.MS.MovLinTie
import HRS.MS.MovOpAux3
import HRS.MS.MovOpAux6
import HRS.MS.MovSchTie
import HRS.MS.MovSchTie9
import HRS.MS.OrbIdTie
import HRS.MS.PathFidiTie
import HRS.MS.Poinc
import HRS.MS.PoisFinal
import HRS.MS.QprepAux13
import HRS.MS.QprepAux14
import HRS.MS.QsfAsm11
import HRS.MS.QsfAux3
import HRS.MS.QsfOsc8
import HRS.MS.R26T8AP29Final
import HRS.MS.R2ChaosTie
import HRS.MS.R2ChaosTie2
import HRS.MS.R2IidPathTie
import HRS.MS.R2IidTie
import HRS.MS.R2InterpTie
import HRS.MS.R2MtAux3
import HRS.MS.R2ObsAux3
import HRS.MS.R2ObsAux9
import HRS.MS.R2PolyTie
import HRS.MS.R2QtAux1
import HRS.MS.R2ScrAux2
import HRS.MS.R2SeAux49
import HRS.MS.R2WfmTie
import HRS.MS.S103dTie
import HRS.MS.S104eFinal
import HRS.MS.S111X1Tie
import HRS.MS.S116A01
import HRS.MS.S11Q3C3
import HRS.MS.S67NlBDTie
import HRS.MS.S81FinC
import HRS.MS.S81FinS
import HRS.MS.S81FinW2
import HRS.MS.S88BDTie
import HRS.MS.SA12DE8G
import HRS.MS.SA12X3Final
import HRS.MS.SA12X4A
import HRS.MS.SA12X4B
import HRS.MS.SA12X4E
import HRS.MS.SA12X5T
import HRS.MS.SA16Y7Asm2
import HRS.MS.SameFunction
import HRS.MS.Sf8
import HRS.MS.SharpBias
import HRS.MS.SharpBiasWrTie
import HRS.MS.SharpCritFinal
import HRS.MS.SharpCritTie
import HRS.MS.SharpIns
import HRS.MS.ShiftFldTie
import HRS.MS.ShiftPathTie
import HRS.MS.SobEmbTie
import HRS.MS.SpecAux103
import HRS.MS.StarTie
import HRS.MS.StaticInput
import HRS.MS.Ste
import HRS.MS.SuppA0
import HRS.MS.SuppU1
import HRS.MS.SuppU10a
import HRS.MS.SuppU11
import HRS.MS.SuppU2
import HRS.MS.SuppU3
import HRS.MS.SuppU4
import HRS.MS.SuppU5
import HRS.MS.SuppU5M
import HRS.MS.SuppU6
import HRS.MS.SuppU8
import HRS.MS.SuppU9
import HRS.MS.ThCorr
import HRS.MS.ThmCons
import HRS.MS.ThmLog
import HRS.MS.ThmSpec
import HRS.MS.TiltTie
import HRS.MS.ToriCoefB
import HRS.MS.ToriConv
import HRS.MS.TransOpTie
import HRS.MS.UlTie1
import HRS.MS.UlTie2
import HRS.MS.UlocCb
import HRS.MS.UlocCut
import HRS.MS.UlocModes
import HRS.MS.UlocWeighted
import HRS.MS.UniqG2
import HRS.MS.UniqQTie
import HRS.MS.WadAux188
import HRS.MS.WhoTie
import HRS.MS.WlStaticTie
import HRS.MS.WrEnt
import HRS.MS.WrPress
import HRS.MS.WrStatic
import HRS.MS.ZeroTempTie
import HRS.Main.A1014Final
import HRS.Main.A8Final
import HRS.Main.A9Final
import HRS.Main.B15Complete
import HRS.Main.Det22Final
import HRS.Main.FullBoundsFinal
import HRS.Main.FullBoundsGibbsCond
import HRS.Main.GFFinal
import HRS.Main.Headline
import HRS.Main.HeadlineEdgeworth
import HRS.Main.HeadlineEquilibrium
import HRS.Main.MeanParticlesFinal
import HRS.Main.MixtureFinal
import HRS.Main.SpecSW2
import HRS.Main.T25Final
import HRS.Main.T25PFinal
import HRS.Main.TSGFinal
import HRS.Main.ThermCond
import HRS.Main.ThermFinal
import HRS.Main.ThermLinCond
import HRS.Main.ThermTieR
import HRS.Main.TorusTheorems
import HRS.Main.WPCFinal
import HRS.PDE.ConventionHolder
import HRS.PDE.MovFinalConsumers
import HRS.Prob.GaussianIso
import HRS.Sections.AdjKGlueFinal
import HRS.Sections.AllTimeFinal
import HRS.Sections.DynCmpFinal
import HRS.Sections.DynCmpFinal2
import HRS.Sections.DynConvFinal
import HRS.Sections.DynEntFinal
import HRS.Sections.IIDFinal
import HRS.Sections.MovLogFinal
import HRS.Sections.MovLogFinal2
import HRS.Sections.Q17Aux3
import HRS.Sections.Q17Aux8
import HRS.Sections.Q40bAux12
import HRS.Sections.Q40bAux15
import HRS.Sections.QuenchFinal
import HRS.Sections.ScrnFinal
import HRS.Sections.Sec4
import HRS.Sections.Sec5
import HRS.Sections.Sec6
import HRS.Sections.Sec7Fields
import HRS.Sections.Sec7Quench
import HRS.Sections.Sec7Static
import HRS.Uniform.Comp28Final
import HRS.Uniform.Comparison
import HRS.Uniform.Evolution
import HRS.Uniform.MaximalDissipative
import HRS.Uniform.Q12Final
import HRS.Uniform.Q45Cov
import HRS.Uniform.Q45Smooth
import HRS.Uniform.Q54Aux24
import HRS.Uniform.Q54cAux59
import HRS.Uniform.RelativeCoupling
import HRS.Uniform.RelativeCov
import HRS.Uniform.Spec
import HRS.Uniform.StationaryNoise
import HRS.Uniform.TransportCoupling
import HRS.Whole.Adjoint
import HRS.Whole.AppendixA
import HRS.Whole.AppendixAAdjoint
import HRS.Whole.AppendixALemmas
import HRS.Whole.AppendixALemmas2
import HRS.Whole.AppendixBEnergy
import HRS.Whole.AppendixBField
import HRS.Whole.AppendixBKernel
import HRS.Whole.Basic
import HRS.Whole.Bias
import HRS.Whole.Critical
import HRS.Whole.CriticalNoise
import HRS.Whole.Moving
import HRS.Whole.MovingDyn
import HRS.Whole.Orbits
import HRS.Whole.Round2
import HRS.Whole.Round2Moving
import HRS.Whole.Static
import HRS.Whole.Thermal
import HRS.Whole.Window

/-! Proof terms for admitted statement labels in the frozen HRS package. -/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRSReaderEvidence
theorem cepaBranch : type_of% @HRS.cepa_entropy_confined :=
  by intros; apply @HRS.MC.CepH5Fin.cep_H5_entropy_confined_proof <;> assumption
end HRSReaderEvidence

namespace HRS
variable {d N : ℕ}
theorem hrsReaderEntropyDispatcher
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hN : 2 ≤ N) [NeZero N]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {D : DynData d} (hM : D.M = -(1 : Matrix (Fin d) (Fin d) ℝ)) (hβ : 0 < D.invβ)
    (hV : Torus.IsCk 2 D.V) {T : ℝ} (hT : 0 < T)
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hX : SelectedFlow P D T X₀ W X) (hF : IsFilteredSolution P ℱ W' W X)
    (hdens0 : HasSelectedDensity P X 0)
    (hH0 : gibbsEntropy D (selectedLaw P X 0) < ⊤) :
    (∀ t ∈ Set.Icc 0 T, HasSelectedDensity P X t ∧
      gibbsEntropy D (selectedLaw P X t)
        + ((ENNReal.ofReal D.invβ *
            ∫⁻ r in Set.Icc (0 : ℝ) t, fisherInfo D N (selectedLaw P X r) : ℝ≥0∞) : EReal)
        ≤ gibbsEntropy D (selectedLaw P X 0)) ∧
    SolvesSelectedFKE D T (selectedLaw P X) := by
  rcases hX with ⟨hX₀, hdist, hW, hind, hflow⟩
  rcases hflow with ⟨hS, hU⟩ | ⟨hd1, hs0, _, _, hCL⟩
  · exact b15_sde_entropy_law_free_proof hN hM hβ hV hT hX₀ hdist hW hind hS hU hF hdens0 hH0
  · subst hd1
    exact HRSReaderEvidence.cepaBranch hN hs0 hβ hM hV hT hX₀ hdist hW hind hCL hF hdens0 hH0

end HRS

namespace HRSReaderEvidence

theorem checked001 : type_of% @HRS.Duality.pairing_expansion_rd :=
  @HRS.MH.PairingRdP.pairing_expansion_rd_proof
#print axioms checked001

theorem checked002 : type_of% @HRS.GeneralSetup.general_fluctuation :=
  @HRS.GeneralSetup.general_fluctuation_proof
#print axioms checked002

theorem checked003 : type_of% @HRS.GeneralSetup.general_fluctuation_filtered :=
  @HRS.MH.FilteredP.general_fluctuation_filtered_proof
#print axioms checked003

theorem checked004 : type_of% @HRS.GeneralSetup.general_fluctuation_matrix :=
  @HRS.GeneralSetup.general_fluctuation_matrix_proof
#print axioms checked004

theorem checked005 : type_of% @HRS.GeneralSetup.general_fluctuation_matrix_filtered :=
  @HRS.MH.FilteredP.general_fluctuation_matrix_filtered_proof
#print axioms checked005

theorem checked006 : type_of% @HRS.GeneralSetup.general_fluctuation_matrix_transport :=
  @HRS.MH.FilteredP.general_fluctuation_matrix_transport_proof
#print axioms checked006

theorem checked007 : type_of% @HRS.GeneralSetup.general_fluctuation_transport :=
  @HRS.GeneralSetup.general_fluctuation_transport_proof
#print axioms checked007

theorem checked008 : type_of% @HRS.Main.SpecSW2.torus_sqrt_gradient_le :=
  @HRS.Main.torus_sqrt_gradient_le_proof
#print axioms checked008

theorem checked009 : type_of% @HRS.Main.SpecSW2.weak_reference_pinned_cavity :=
  @HRS.Main.SpecSW2.weak_reference_pinned_cavity_proof
#print axioms checked009

theorem checked010 : type_of% @HRS.Main.conditioned_ou :=
  @HRS.MH.CondOuFinal.conditioned_ou_proof
#print axioms checked010

theorem checked011 : type_of% @HRS.Main.covariance_obstruction :=
  @HRS.MD.Cov211.covariance_obstruction_proof
#print axioms checked011

theorem checked012 : type_of% @HRS.Main.criticalBias_ne_zero :=
  @HRS.ME.Marginal.criticalBias_ne_zero_proof
#print axioms checked012

theorem checked013 : type_of% @HRS.Main.critical_bias_constants :=
  @HRS.ME.Bias.critical_bias_constants_unif
#print axioms checked013

theorem checked014 : type_of% @HRS.Main.critical_centered_path :=
  @HRS.ME.CritFinalUnif.critical_centered_path_proved
#print axioms checked014

theorem checked015 : type_of% @HRS.Main.critical_centered_path_uniform :=
  @HRS.ME.FamU.critical_centered_path_uniform_proved
#print axioms checked015

theorem checked016 : type_of% @HRS.Main.critical_family_fixed_limsup :=
  @HRS.ME.FamX.critical_family_fixed_limsup_proved
#print axioms checked016

theorem checked017 : type_of% @HRS.Main.critical_family_path_sup :=
  @HRS.ME.FamX.critical_family_path_sup_proved
#print axioms checked017

theorem checked018 : type_of% @HRS.Main.critical_family_sharpness :=
  @HRS.ME.FamW.critical_family_sharpness_proved
#print axioms checked018

theorem checked019 : type_of% @HRS.Main.critical_marginal_expansion :=
  @HRS.ME.Unif.critical_marginal_expansion_unif_proof
#print axioms checked019

theorem checked020 : type_of% @HRS.Main.cross_cov_densities_exist :=
  @HRS.MC.CrossCov.p_assembly
#print axioms checked020

theorem checked021 : type_of% @HRS.Main.cubic_tensor_unique :=
  @HRS.MC.CUB.cubic_tensor_unique_proof
#print axioms checked021

theorem checked022 : type_of% @HRS.Main.deterministic_comparison :=
  @HRS.Main.deterministic_comparison_proof
#print axioms checked022

theorem checked023 : type_of% @HRS.Main.deterministic_comparison_matrix :=
  @HRS.Main.deterministic_comparison_matrix_proof
#print axioms checked023

theorem checked024 : type_of% @HRS.Main.edgeworth_sharpness :=
  @HRS.MH.EdgeworthSharpP.edgeworth_sharpness_proof
#print axioms checked024

theorem checked025 : type_of% @HRS.Main.edgeworth_sharpness_homogeneous :=
  @HRS.MH.EdgeSharp.edgeworth_sharpness_homogeneous_final
#print axioms checked025

theorem checked026 : type_of% @HRS.Main.edgeworth_window :=
  @HRS.MC.E213Final.edgeworth_window_proof
#print axioms checked026

theorem checked027 : type_of% @HRS.Main.fb_prepared_full_bounds_cond :=
  by intros; apply @HRS.Main.prepared_full_bounds_proof <;> assumption
#print axioms checked027

theorem checked028 : type_of% @HRS.Main.general_fluctuation_noLowerBound :=
  @HRS.MH.NoLB.general_fluctuation_noLowerBound_proof
#print axioms checked028

theorem checked029 : type_of% @HRS.Main.hybrid_correction :=
  @HRS.MC.E214P.hybrid_correction_proof
#print axioms checked029

theorem checked030 : type_of% @HRS.Main.main_torus_field :=
  @HRS.Main.main_torus_field_proof
#print axioms checked030

theorem checked031 : type_of% @HRS.Main.main_torus_field_limit :=
  @HRS.Main.main_torus_field_limit_proof
#print axioms checked031

theorem checked032 : type_of% @HRS.Main.main_torus_path :=
  @HRS.MP.A11.main_torus_path_proof
#print axioms checked032

theorem checked033 : type_of% @HRS.Main.main_torus_stat :=
  @HRS.Main.main_torus_stat_proof
#print axioms checked033

theorem checked034 : type_of% @HRS.Main.main_torus_stat_tendsto :=
  @HRS.Main.main_torus_stat_tendsto_proof
#print axioms checked034

theorem checked035 : type_of% @HRS.Main.mean_field_centering_lower_bound :=
  @HRS.MH.MfclP.mean_field_centering_lower_bound_proof
#print axioms checked035

theorem checked036 : type_of% @HRS.Main.mixture_full_bounds :=
  @HRS.Main.mixture_full_bounds_proof
#print axioms checked036

theorem checked037 : type_of% @HRS.Main.mixture_limit :=
  @HRS.Main.mixture_limit_proof
#print axioms checked037

theorem checked038 : type_of% @HRS.Main.prepared_fluctuations :=
  @HRS.Main.prepared_fluctuations_proof
#print axioms checked038

theorem checked039 : type_of% @HRS.Main.prepared_fluctuations_W2 :=
  @HRS.Main.prepared_fluctuations_W2_proof
#print axioms checked039

theorem checked040 : type_of% @HRS.Main.prepared_full_bounds :=
  @HRS.Main.prepared_full_bounds_proof
#print axioms checked040

theorem checked041 : type_of% @HRS.Main.prepared_scales :=
  @HRS.Main.prepared_scales_proof
#print axioms checked041

theorem checked042 : type_of% @HRS.Main.standard_preparation_norms :=
  @HRS.Main.standard_preparation_norms_proof
#print axioms checked042

theorem checked043 : type_of% @HRS.Main.stationary_tensor_relaxation :=
  @HRS.MC.E214U.stationary_tensor_relaxation_proof
#print axioms checked043

theorem checked044 : type_of% @HRS.Main.thermalization :=
  @HRS.Main.thermalization_proof
#print axioms checked044

theorem checked045 : type_of% @HRS.Main.thermalization_W2 :=
  @HRS.Main.thermalization_W2_proof
#print axioms checked045

theorem checked046 : type_of% @HRS.Main.thermalization_limit :=
  @HRS.Main.thermalization_limit_proof
#print axioms checked046

theorem checked047 : type_of% @HRS.Main.thermalization_recentered :=
  @HRS.Main.thermalization_recentered_proof
#print axioms checked047

theorem checked048 : type_of% @HRS.Main.torus_field_wasserstein :=
  @HRS.Main.torus_field_wasserstein_proof
#print axioms checked048

theorem checked049 : type_of% @HRS.Main.true_limit_field :=
  @HRS.Main.true_limit_field_proof
#print axioms checked049

theorem checked050 : type_of% @HRS.Main.true_limit_stat :=
  @HRS.Main.true_limit_stat_proof
#print axioms checked050

theorem checked051 : type_of% @HRS.Main.true_limit_stat_base :=
  @HRS.Main.true_limit_stat_base_proof
#print axioms checked051

theorem checked052 : type_of% @HRS.Main.two_parameter_expansion :=
  @HRS.MC.E214T.two_parameter_expansion_proof
#print axioms checked052

theorem checked053 : type_of% @HRS.Sec7.alltime_Lp :=
  @HRS.Sec7.alltime_Lp_proof'
#print axioms checked053

theorem checked054 : type_of% @HRS.Sec7.alltime_Lp_proof :=
  @HRS.Sec7.alltime_Lp_proof'
#print axioms checked054

theorem checked055 : type_of% @HRS.Sec7.critical_edgeworth :=
  @HRS.MC.Q714.Asm.critical_edgeworth_proof
#print axioms checked055

theorem checked056 : type_of% @HRS.Sec7.critical_edgeworth_equal_temperature :=
  @HRS.MC.Q714.Asm.critical_edgeworth_equal_temperature_proof
#print axioms checked056

theorem checked057 : type_of% @HRS.Sec7.field_chaos :=
  @HRS.MC.Sec7.S7FCZ.field_chaos_proof
#print axioms checked057

theorem checked058 : type_of% @HRS.Sec7.measure_projection :=
  @HRS.Sec7.measure_projection_proof
#print axioms checked058

theorem checked059 : type_of% @HRS.Sec7.path_Ito :=
  @HRS.MC.Sec7.S7PIZ.path_Ito_proof
#print axioms checked059

theorem checked060 : type_of% @HRS.Sec7.projection_strong :=
  @HRS.Sec7.projection_strong_proof
#print axioms checked060

theorem checked061 : type_of% @HRS.Sec7.quadratic_relaxation :=
  @HRS.MC.QRSpec.Asm.quadratic_relaxation_proof
#print axioms checked061

theorem checked062 : type_of% @HRS.Sec7.quench_equal_temperature :=
  @HRS.Sec7.quench_equal_temperature_proof
#print axioms checked062

theorem checked063 : type_of% @HRS.Sec7.quench_modes :=
  @HRS.Sec7.quench_modes_proof
#print axioms checked063

theorem checked064 : type_of% @HRS.Sec7.quench_window_tensors :=
  @HRS.Sec7.quench_window_tensors_proof
#print axioms checked064

theorem checked065 : type_of% @HRS.Sec7.slow_correction :=
  @HRS.MC.Sec7.S16f.slow_correction_proof
#print axioms checked065

theorem checked066 : type_of% @HRS.Sec7.static_edge :=
  @HRS.MC.SEdge.B14.static_edge_assembly_proof
#print axioms checked066

theorem checked067 : type_of% @HRS.Sec7.static_edge_char :=
  @HRS.MC.SEdge.U4.static_edge_char_assembly_proof
#print axioms checked067

theorem checked068 : type_of% @HRS.Sec7.static_field :=
  @HRS.MC.Sec7.S7f.static_field_proof
#print axioms checked068

theorem checked069 : type_of% @HRS.Sec7.uniform_chaos :=
  @HRS.MC.Sec7.S7UCZ.s7_UC_uniform_chaos_proof
#print axioms checked069

theorem checked070 : type_of% @HRS.Uniform.chart_current :=
  @HRS.Uniform.chart_current_proof
#print axioms checked070

theorem checked071 : type_of% @HRS.Uniform.coefficient_comparison :=
  @HRS.Uniform.coefficient_comparison_proof
#print axioms checked071

theorem checked072 : type_of% @HRS.Uniform.comparison_smooth :=
  @HRS.Uniform.comparison_smooth_proof
#print axioms checked072

theorem checked073 : type_of% @HRS.Uniform.comparison_wasserstein :=
  @HRS.Uniform.comparison_wasserstein_proof
#print axioms checked073

theorem checked074 : type_of% @HRS.Uniform.covariance_measure :=
  @HRS.Uniform.covariance_measure_proof
#print axioms checked074

theorem checked075 : type_of% @HRS.Uniform.energy_W2 :=
  @HRS.Uniform.Q12.energy_W2_proof
#print axioms checked075

theorem checked076 : type_of% @HRS.Uniform.evolution_estimates :=
  @HRS.Uniform.Q54.evolution_estimates_proof
#print axioms checked076

theorem checked077 : type_of% @HRS.Uniform.general_fluctuation_Wp :=
  @HRS.MH.WpP.general_fluctuation_Wp_proof
#print axioms checked077

theorem checked078 : type_of% @HRS.Uniform.maximal_estimate :=
  @HRS.Uniform.maximal_estimate_proof
#print axioms checked078

theorem checked079 : type_of% @HRS.Uniform.relative_covariance_cost :=
  @HRS.Uniform.relative_covariance_cost_proof
#print axioms checked079

theorem checked080 : type_of% @HRS.Uniform.relative_covariance_coupling :=
  @HRS.Uniform.relative_covariance_coupling_proof
#print axioms checked080

theorem checked081 : type_of% @HRS.Uniform.smooth_path_comparison :=
  @HRS.Uniform.smooth_path_comparison_proof
#print axioms checked081

theorem checked082 : type_of% @HRS.Uniform.stationary_noise :=
  @HRS.Uniform.stationary_noise_proof
#print axioms checked082

theorem checked083 : type_of% @HRS.Uniform.transport_noise_coupling :=
  @HRS.Uniform.transport_noise_coupling_proof
#print axioms checked083

theorem checked084 : type_of% @HRS.Whole.AppendixA.adjoint_lp :=
  @HRS.Whole.AppendixA.Phase2SA16R.sa16y7_adjoint_lp
#print axioms checked084

theorem checked085 : type_of% @HRS.Whole.AppendixA.adjoint_rd :=
  @HRS.MH.AdjointRd.Phase2SA12Assembly.sa12x3_adjoint_rd_from_cells
#print axioms checked085

theorem checked086 : type_of% @HRS.Whole.AppendixA.adjoint_rd_classical :=
  @HRS.MH.AdjointRd.Phase2SA12X4.sa12x4_adjoint_rd_classical_tie
#print axioms checked086

theorem checked087 : type_of% @HRS.Whole.AppendixA.adjoint_rd_planewave :=
  @HRS.MH.AdjointRd.Phase2SA12X4.sa12x4_adjoint_rd_planewave_tie
#print axioms checked087

theorem checked088 : type_of% @HRS.Whole.AppendixA.adjoint_rd_sobolev :=
  @HRS.MS.SA12DE8.sa12de8_adjoint_rd_sobolev
#print axioms checked088

theorem checked089 : type_of% @HRS.Whole.AppendixA.adjoint_rd_stability :=
  @HRS.MH.AdjointRd.Phase2SA12X5.sa12x5_adjoint_rd_stability_tie
#print axioms checked089

theorem checked090 : type_of% @HRS.Whole.AppendixA.adjoint_rd_weighted :=
  @HRS.MH.AdjointRd.Phase2SA12X4.sa12x4_adjoint_rd_weighted_tie
#print axioms checked090

theorem checked091 : type_of% @HRS.Whole.AppendixA.duality_identity_rd :=
  @HRS.MH.DualityRd.duality_identity_rd_proof
#print axioms checked091

theorem checked092 : type_of% @HRS.Whole.AppendixA.fourier_statistics_rd :=
  @HRS.MS.MainRdStat.fourier_statistics_rd_proof
#print axioms checked092

theorem checked093 : type_of% @HRS.Whole.AppendixA.iid_path_rd :=
  @HRS.MS.MainRdPath.iid_path_rd_proof
#print axioms checked093

theorem checked094 : type_of% @HRS.Whole.AppendixA.lp_Lambda_commutator_expansion :=
  @HRS.CZ.ElemA.lp_Lambda_commutator_expansion_proof
#print axioms checked094

theorem checked095 : type_of% @HRS.Whole.AppendixA.lp_Lambda_commutator_low :=
  @HRS.CZ.Asm15.lp_Lambda_commutator_low_proof
#print axioms checked095

theorem checked096 : type_of% @HRS.Whole.AppendixA.lp_positive_order_product :=
  @HRS.CZ.Asm15.asm15_lp_positive_order_product
#print axioms checked096

theorem checked097 : type_of% @HRS.Whole.AppendixA.lp_screened_negative_order :=
  @HRS.CZ.Asm15.lp_screened_negative_order_proof
#print axioms checked097

theorem checked098 : type_of% @HRS.Whole.AppendixA.lp_tensor_absorption :=
  @HRS.CZ.ElemB.lp_tensor_absorption_proof
#print axioms checked098

theorem checked099 : type_of% @HRS.Whole.AppendixA.main_rd_dec_stat :=
  @HRS.MS.DecStat.main_rd_dec_stat_proof
#print axioms checked099

theorem checked100 : type_of% @HRS.Whole.AppendixA.main_rd_field :=
  @HRS.MS.MainRdField.main_rd_field_proof
#print axioms checked100

theorem checked101 : type_of% @HRS.Whole.AppendixA.main_rd_path :=
  @HRS.MS.MainRdPath.main_rd_path_proof
#print axioms checked101

theorem checked102 : type_of% @HRS.Whole.AppendixA.main_rd_stat :=
  @HRS.MS.MainRdStat.main_rd_stat_proof
#print axioms checked102

theorem checked103 : type_of% @HRS.Whole.AppendixA.rd_field_wasserstein_one :=
  @HRS.MS.MainRdField.rd_field_wasserstein_one_proof
#print axioms checked103

theorem checked104 : type_of% @HRS.Whole.AppendixA.rd_field_wasserstein_two :=
  @HRS.MS.MainRdField.rd_field_wasserstein_two_proof
#print axioms checked104

theorem checked105 : type_of% @HRS.Whole.AppendixA.zero_temp_decaying_field :=
  @HRS.MS.ZeroTemp.zero_temp_decaying_field_proof
#print axioms checked105

theorem checked106 : type_of% @HRS.Whole.AppendixALemmas.adjoint_field_kernel :=
  @HRS.MS.SuppU3.adjoint_field_kernel_proof
#print axioms checked106

theorem checked107 : type_of% @HRS.Whole.AppendixALemmas.expanding_tori_coefficients :=
  @HRS.MS.ToriCoefB.expanding_tori_coefficients_proof
#print axioms checked107

theorem checked108 : type_of% @HRS.Whole.AppendixALemmas.expanding_tori_drift_convergence :=
  @HRS.MS.ToriConv.expanding_tori_drift_convergence_proof
#print axioms checked108

theorem checked109 : type_of% @HRS.Whole.AppendixALemmas.expanding_tori_kernel :=
  @HRS.MS.Ker1.expanding_tori_kernel_proof
#print axioms checked109

theorem checked110 : type_of% @HRS.Whole.AppendixALemmas.iid_init_path_rd :=
  @iid_init_path_rd_proof
#print axioms checked110

theorem checked111 : type_of% @HRS.Whole.AppendixALemmas.kolmogorov_modulus_tightness :=
  @HRS.MP.KC.kolmogorov_modulus_tightness_proof
#print axioms checked111

theorem checked112 : type_of% @HRS.Whole.AppendixALemmas.path_fidi_rd :=
  @HRS.MS.PathFidi.path_fidi_rd_aem_proof
#print axioms checked112

theorem checked113 : type_of% @HRS.Whole.AppendixALemmas.path_fidi_torus :=
  @HRS.MP.FidiAssembly.path_fidi_torus_proof
#print axioms checked113

theorem checked114 : type_of% @HRS.Whole.AppendixALemmas.path_initial_modulus_rd :=
  @HRS.MP.RdInitClose.path_initial_modulus_rd_proof
#print axioms checked114

theorem checked115 : type_of% @HRS.Whole.AppendixALemmas.path_initial_modulus_rd_limit :=
  @HRS.MP.RdInitLimitClose.path_initial_modulus_rd_limit_proof
#print axioms checked115

theorem checked116 : type_of% @HRS.Whole.AppendixALemmas.path_initial_modulus_torus :=
  @HRS.MP.InitAsm.path_initial_modulus_torus_proof
#print axioms checked116

theorem checked117 : type_of% @HRS.Whole.AppendixALemmas.path_kernel_increment_torus :=
  @HRS.MP.KernIncr.path_kernel_increment_torus_proof
#print axioms checked117

theorem checked118 : type_of% @HRS.Whole.AppendixALemmas.path_martingale_modulus_rd :=
  @HRS.MP.RdMartClose.path_martingale_modulus_rd_proof
#print axioms checked118

theorem checked119 : type_of% @HRS.Whole.AppendixALemmas.path_martingale_modulus_torus :=
  @HRS.MP.LimGauss.path_martingale_modulus_torus_proof
#print axioms checked119

theorem checked120 : type_of% @HRS.Whole.AppendixALemmas.path_propagator_increment_rd :=
  @HRS.MP.RdProp.path_propagator_increment_rd_proof
#print axioms checked120

theorem checked121 : type_of% @HRS.Whole.AppendixALemmas.path_propagator_increment_torus :=
  @HRS.MP.PropIncr.path_propagator_increment_torus_proof
#print axioms checked121

theorem checked122 : type_of% @HRS.Whole.AppendixALemmas.path_remainder_rd :=
  @HRS.MP.RdRem.path_remainder_rd_proof
#print axioms checked122

theorem checked123 : type_of% @HRS.Whole.AppendixALemmas.path_remainder_torus :=
  @HRS.MP.RemSup.path_remainder_torus_proof
#print axioms checked123

theorem checked124 : type_of% @HRS.Whole.AppendixALemmas.path_tightness_criterion :=
  @HRS.MP.PathTight.path_tightness_criterion_proof
#print axioms checked124

theorem checked125 : type_of% @HRS.Whole.AppendixALemmas.selected_law_selfsimilar :=
  @HRS.MP.SelfSimFinal.selected_law_selfsimilar_final
#print axioms checked125

theorem checked126 : type_of% @HRS.Whole.AppendixALemmas.uloc_bilip :=
  @HRS.MS.BilipV.uloc_bilip_proof
#print axioms checked126

theorem checked127 : type_of% @HRS.Whole.AppendixALemmas.uloc_embedding_cb :=
  @HRS.MS.UlocCb.uloc_embedding_cb_proof
#print axioms checked127

theorem checked128 : type_of% @HRS.Whole.AppendixALemmas.uloc_embedding_cutoffs :=
  @HRS.MS.UlocCut.uloc_embedding_cutoffs_proof
#print axioms checked128

theorem checked129 : type_of% @HRS.Whole.AppendixALemmas.uloc_embedding_modes :=
  @HRS.MS.UlocModes.uloc_embedding_modes_proof
#print axioms checked129

theorem checked130 : type_of% @HRS.Whole.AppendixALemmas.uloc_embedding_weighted :=
  @HRS.MS.UlocWeighted.uloc_embedding_weighted_proof
#print axioms checked130

theorem checked131 : type_of% @HRS.Whole.AppendixALemmas.uloc_uniqueness :=
  @HRS.MS.UniqG2.uloc_uniqueness_proof
#print axioms checked131

theorem checked132 : type_of% @HRS.Whole.AppendixALemmas.whole_coercivity_pair :=
  @HRS.MH.CoercTest.p_assembly
#print axioms checked132

theorem checked133 : type_of% @HRS.Whole.DecayingDensity.commutatorNorm_le :=
  @HRS.SA1.commutatorNorm_le_proof'
#print axioms checked133

theorem checked134 : type_of% @HRS.Whole.DecayingDensity.h_embeds_sobolev :=
  @HRS.SA1.h_embeds_sobolev_proof
#print axioms checked134

theorem checked135 : type_of% @HRS.Whole.DecayingDensity.sobolev_embeds_cb :=
  @HRS.SA1.sobolev_embeds_cb_proof
#print axioms checked135

theorem checked136 : type_of% @HRS.Whole.adapted_charts :=
  @adapted_charts_proof
#print axioms checked136

theorem checked137 : type_of% @HRS.Whole.adjoint_decay :=
  @HRS.MS.AdjDecay.adjoint_decay_proof
#print axioms checked137

theorem checked138 : type_of% @HRS.Whole.affine_poisson :=
  @HRS.MS.PoisFinal.affine_poisson_proof
#print axioms checked138

theorem checked139 : type_of% @HRS.Whole.affine_poisson_deriv :=
  @HRS.MS.PoisFinal.affine_poisson_deriv_proof
#print axioms checked139

theorem checked140 : type_of% @HRS.Whole.affine_poisson_higher :=
  @HRS.MS.PoisFinal.affine_poisson_higher_proof
#print axioms checked140

theorem checked141 : type_of% @HRS.Whole.commutatorKernel_isBounded :=
  @HRS.MS.Comm.commutatorKernel_isBounded_proof
#print axioms checked141

theorem checked142 : type_of% @HRS.Whole.commutatorKernel_log_isBounded :=
  @HRS.MS.Comm.commutatorKernel_log_isBounded_proof
#print axioms checked142

theorem checked143 : type_of% @HRS.Whole.conditional_density :=
  @HRS.MS.Wr.conditional_density_proof
#print axioms checked143

theorem checked144 : type_of% @HRS.Whole.critical_path_limit :=
  @HRS.Whole.S79.critical_path_limit_proof
#print axioms checked144

theorem checked145 : type_of% @HRS.Whole.critical_whole_W2 :=
  HRS.Whole.S81Fin.s81fin_W2_of_forcing HRS.MS.R26T8A.r26t8a_weighted_critical_forcing_tied
#print axioms checked145

theorem checked146 : type_of% @HRS.Whole.critical_whole_constants :=
  HRS.Whole.S81Fin.s81fin_constants_of_forcing HRS.MS.R26T8A.r26t8a_weighted_critical_forcing_tied
#print axioms checked146

theorem checked147 : type_of% @HRS.Whole.critical_whole_marginal :=
  @HRS.Whole.S81b.s81d_critical_whole_marginal
#print axioms checked147

theorem checked148 : type_of% @HRS.Whole.critical_whole_smooth :=
  HRS.Whole.S81Fin.s81fin_smooth_of_forcing HRS.MS.R26T8A.r26t8a_weighted_critical_forcing_tied
#print axioms checked148

theorem checked149 : type_of% @HRS.Whole.derivative_corrector :=
  @HRS.MS.S48.derivative_corrector_proof
#print axioms checked149

theorem checked150 : type_of% @HRS.Whole.euc_static :=
  @HRS.MS.Wr.euc_static_proof
#print axioms checked150

theorem checked151 : type_of% @HRS.Whole.euc_static_commutator :=
  @HRS.MS.Wr.euc_static_commutator_proof
#print axioms checked151

theorem checked152 : type_of% @HRS.Whole.euc_thermal_canonical :=
  @HRS.MS.Can2.euc_thermal_canonical_proof
#print axioms checked152

theorem checked153 : type_of% @HRS.Whole.euc_thermal_gaussian_bounds :=
  @HRS.MS.Poinc.euc_thermal_gaussian_bounds_proof
#print axioms checked153

theorem checked154 : type_of% @HRS.Whole.euc_thermal_moments :=
  @HRS.MS.Thm.euc_thermal_moments_proof
#print axioms checked154

theorem checked155 : type_of% @HRS.Whole.euc_thermal_regularity :=
  @HRS.MS.Thm.euc_thermal_regularity_proof
#print axioms checked155

theorem checked156 : type_of% @HRS.Whole.euclidean_pair_entropy :=
  @HRS.MS.Wr.euclidean_pair_entropy_proof
#print axioms checked156

theorem checked157 : type_of% @HRS.Whole.euclidean_pair_entropy_self :=
  @HRS.MS.Wr.euclidean_pair_entropy_self_proof
#print axioms checked157

theorem checked158 : type_of% @HRS.Whole.euclidean_pressure :=
  @HRS.MS.Wr.euclidean_pressure_proof
#print axioms checked158

theorem checked159 : type_of% @HRS.Whole.exists_gaussian_feature :=
  @S45.exists_gaussian_feature_proof
#print axioms checked159

theorem checked160 : type_of% @HRS.Whole.far_derivatives :=
  @HRS.Whole.far_derivatives_proof
#print axioms checked160

theorem checked161 : type_of% @HRS.Whole.feature_decay :=
  @HRS.MS.S85.feature_decay_proof
#print axioms checked161

theorem checked162 : type_of% @HRS.Whole.finite_noise :=
  @HRS.MS.FinNoise.finite_noise_proof
#print axioms checked162

theorem checked163 : type_of% @HRS.Whole.fixed_equation :=
  @HRS.MS.FixEq.fixed_equation_proof
#print axioms checked163

theorem checked164 : type_of% @HRS.Whole.fractional_decay :=
  @HRS.Whole.fractional_decay_proof
#print axioms checked164

theorem checked165 : type_of% @HRS.Whole.general_orbits_commutator :=
  @HRS.MS.Go.general_orbits_commutator_proof
#print axioms checked165

theorem checked166 : type_of% @HRS.Whole.general_orbits_features :=
  @HRS.MS.Star.general_orbits_features_proof
#print axioms checked166

theorem checked167 : type_of% @HRS.Whole.general_orbits_maximal :=
  @HRS.MS.Star.general_orbits_maximal_proof
#print axioms checked167

theorem checked168 : type_of% @HRS.Whole.iid_init_field_rd :=
  @iid_init_field_rd_proof
#print axioms checked168

theorem checked169 : type_of% @HRS.Whole.iid_init_field_rd_multitime :=
  @iid_init_field_rd_multitime_proof
#print axioms checked169

theorem checked170 : type_of% @HRS.Whole.isAdmissiblePerturbation_thermal :=
  @HRS.MS.Thm.isAdmissiblePerturbation_thermal_proof
#print axioms checked170

theorem checked171 : type_of% @HRS.Whole.limit_field_rd_duality :=
  by
   intros
   constructor
   · apply @HRS.MS.U10.sb7_limit_field_rd_duality_exists <;> assumption
   · exact HRS.MS.U10.sb7_limit_field_rd_duality_unique _ _ _ _ _
#print axioms checked171

theorem checked172 : type_of% @HRS.Whole.limit_field_rd_gaussian :=
  @HRS.MS.U10.limit_field_rd_gaussian_proof
#print axioms checked172

theorem checked173 : type_of% @HRS.Whole.limit_field_rd_weak_form :=
  @HRS.MS.U10.sb7_limit_field_rd_weak_form
#print axioms checked173

theorem checked174 : type_of% @HRS.Whole.local_decay :=
  @HRS.MS.Lc.local_decay_proof
#print axioms checked174

theorem checked175 : type_of% @HRS.Whole.logThermalDensity_spec :=
  @HRS.MS.Thm.logThermalDensity_spec_proof
#print axioms checked175

theorem checked176 : type_of% @HRS.Whole.logThermal_bounds :=
  @HRS.MS.Thm.logThermal_bounds_proof
#print axioms checked176

theorem checked177 : type_of% @HRS.Whole.logThermal_canonical :=
  @HRS.MS.Can2.logThermal_canonical_proof
#print axioms checked177

theorem checked178 : type_of% @HRS.Whole.logThermal_regularity :=
  @HRS.MS.LogReg.logThermal_regularity_proof
#print axioms checked178

theorem checked179 : type_of% @HRS.Whole.logThermal_stereographic :=
  @HRS.MS.Thm.logThermal_stereographic_proof
#print axioms checked179

theorem checked180 : type_of% @HRS.Whole.mfe_confined_rd_gradient_sub :=
  @HRS.MS.MfeConf.sb1_sub_tie
#print axioms checked180

theorem checked181 : type_of% @HRS.Whole.mfe_confined_rd_gradient_super :=
  @HRS.MS.MfeConf.sb1_super_tie
#print axioms checked181

theorem checked182 : type_of% @HRS.Whole.mov_entropy :=
  @HRS.MS.MovEnt.mov_entropy_proof
#print axioms checked182

theorem checked183 : type_of% @HRS.Whole.mov_global_adjoint_nonlinear :=
  @HRS.MS.BreakdownS67.mov_global_adjoint_nonlinear_proof
#print axioms checked183

theorem checked184 : type_of% @HRS.Whole.mov_global_adjoint_stationary :=
  @HRS.MS.MovAdj.mov_global_adjoint_stationary_proof
#print axioms checked184

theorem checked185 : type_of% @HRS.Whole.mov_linear :=
  @HRS.MS.MovLin.mov_linear_proof
#print axioms checked185

theorem checked186 : type_of% @HRS.Whole.mov_moving_reference :=
  @HRS.MS.MovSch.mov_moving_reference_proof
#print axioms checked186

theorem checked187 : type_of% @HRS.Whole.mov_nonlinear :=
  @HRS.MS.Mov63.mov_nonlinear_proof
#print axioms checked187

theorem checked188 : type_of% @HRS.Whole.mov_operators_B :=
  @HRS.MS.MovC2.mov_operators_B_proof
#print axioms checked188

theorem checked189 : type_of% @HRS.Whole.mov_operators_P :=
  @HRS.MS.MovC1.mov_operators_P_proof
#print axioms checked189

theorem checked190 : type_of% @HRS.Whole.mov_operators_force :=
  @HRS.MS.MovForce.mov_operators_force_proof
#print axioms checked190

theorem checked191 : type_of% @HRS.Whole.mov_schwartz :=
  @HRS.MS.MovSch.mov_schwartz_proof
#print axioms checked191

theorem checked192 : type_of% @HRS.Whole.mov_scope_infinite_dim :=
  @mov_scope_infinite_dim_proof
#print axioms checked192

theorem checked193 : type_of% @HRS.Whole.mov_translated_prepared :=
  @HRS.MS.S104e.s104e_final_mov_translated_prepared
#print axioms checked193

theorem checked194 : type_of% @HRS.Whole.mov_translated_stationary :=
  @HRS.MS.TransOp.mov_translated_stationary_proof
#print axioms checked194

theorem checked195 : type_of% @HRS.Whole.mov_translation :=
  @HRS.Whole.mov_translation_proof
#print axioms checked195

theorem checked196 : type_of% @HRS.Whole.orbit_feature_bounded :=
  @HRS.MS.UniqQ.orbit_feature_bounded_proof
#print axioms checked196

theorem checked197 : type_of% @HRS.Whole.orbit_maximal :=
  @HRS.MS.U9.orbit_maximal_proof
#print axioms checked197

theorem checked198 : type_of% @HRS.Whole.orbit_maximal_identification :=
  @HRS.MS.S52.orbit_maximal_identification_bdd
#print axioms checked198

theorem checked199 : type_of% @HRS.Whole.quadratic_preparation_static :=
  @S46.quadratic_preparation_static_proof
#print axioms checked199

theorem checked200 : type_of% @HRS.Whole.quadratic_preparation_static_osc :=
  @S46.quadratic_preparation_static_osc_proof
#print axioms checked200

theorem checked201 : type_of% @HRS.Whole.quadratic_static_field :=
  @S45.quadratic_static_field_proof
#print axioms checked201

theorem checked202 : type_of% @HRS.Whole.quadratic_static_field_osc :=
  @S45.quadratic_static_field_osc_proof
#print axioms checked202

theorem checked203 : type_of% @HRS.Whole.r2_covariance_measure :=
  @HRS.MS.CovMeas.r2_covariance_measure_proof
#print axioms checked203

theorem checked204 : type_of% @HRS.Whole.r2_cross_density_exists :=
  @HRS.MS.S111X1.r2_cross_density_exists_proof
#print axioms checked204

theorem checked205 : type_of% @HRS.Whole.r2_log_path :=
  @HRS.MS.S116.s116_log_path_proof
#print axioms checked205

theorem checked206 : type_of% @HRS.Whole.r2_log_static :=
  @HRS.MS.Wl.r2_log_static_proof
#print axioms checked206

theorem checked207 : type_of% @HRS.Whole.r2_log_static_commutator :=
  @HRS.MS.Wl.r2_log_static_commutator_proof
#print axioms checked207

theorem checked208 : type_of% @HRS.Whole.r2_moving_Lp :=
  @HRS.MS.S11Q3.s11q3_r2_moving_Lp
#print axioms checked208

theorem checked209 : type_of% @HRS.Whole.r2_moving_moment_transfer :=
  @HRS.MS.S11Q3.s11q3_r2_moving_moment_transfer
#print axioms checked209

theorem checked210 : type_of% @HRS.Whole.r2_path_interpolation :=
  @HRS.MS.R2Interp.r2_path_interpolation_proof
#print axioms checked210

theorem checked211 : type_of% @HRS.Whole.r2_screened :=
  @HRS.MS.S98.r2_screened_proof
#print axioms checked211

theorem checked212 : type_of% @HRS.Whole.r2_static_edgeworth :=
  @S99.round2_static_edgeworth_proof
#print axioms checked212

theorem checked213 : type_of% @HRS.Whole.r2_static_edgeworth_iid :=
  @HRS.MS.R2Iid.r2_static_edgeworth_iid_proof
#print axioms checked213

theorem checked214 : type_of% @HRS.Whole.r2_static_observation_family :=
  @HRS.MS.R2Obs.r2_static_observation_family_proof
#print axioms checked214

theorem checked215 : type_of% @HRS.Whole.r2_static_observation_path :=
  @HRS.MS.R2Obs.r2_static_observation_path_proof
#print axioms checked215

theorem checked216 : type_of% @HRS.Whole.r2_static_observation_path_iid :=
  @HRS.MS.R2IidPath.r2_static_observation_path_iid_proof
#print axioms checked216

theorem checked219 : type_of% @HRS.Whole.r2_window_errors :=
  @HRS.MS.S104e.s104e_final_errors
#print axioms checked219

theorem checked220 : type_of% @HRS.Whole.r2_window_general_initial :=
  @HRS.MS.S104e.s104e_final_general_initial
#print axioms checked220

theorem checked221 : type_of% @HRS.Whole.r2_window_orbits :=
  @HRS.MS.R2WinOrbNL.s103d_r2_window_orbits_proof
#print axioms checked221

theorem checked222 : type_of% @HRS.Whole.reflection_gap_poincare :=
  @HRS.MS.Gap.reflection_gap_poincare_proof
#print axioms checked222

theorem checked223 : type_of% @HRS.Whole.return_map_bounded :=
  @HRS.MS.SuppU11.return_map_bounded_proof
#print axioms checked223

theorem checked224 : type_of% @HRS.Whole.return_map_initial_decay :=
  @HRS.MS.S88Breakdown.s88_initial_decay
#print axioms checked224

theorem checked225 : type_of% @HRS.Whole.round2_approximation :=
  @HRS.Whole.U1.round2_approximation_proof
#print axioms checked225

theorem checked226 : type_of% @HRS.Whole.round2_integrated_chaos :=
  @HRS.MS.R2Chaos.round2_integrated_chaos_proof
#print axioms checked226

theorem checked227 : type_of% @HRS.Whole.round2_moment_transfer :=
  @HRS.MS.R2Mt.round2_moment_transfer_proof
#print axioms checked227

theorem checked228 : type_of% @HRS.Whole.round2_polynomial_integrated :=
  @HRS.MS.R2Chaos.round2_polynomial_integrated_proof
#print axioms checked228

theorem checked229 : type_of% @HRS.Whole.round2_polynomial_moments :=
  @HRS.MS.R2Poly.round2_polynomial_moments_proof
#print axioms checked229

theorem checked230 : type_of% @HRS.Whole.round2_quench_transfer :=
  @HRS.MS.R2Mt.round2_quench_transfer_proof
#print axioms checked230

theorem checked231 : type_of% @HRS.Whole.round2_weighted_field_moments :=
  @HRS.MS.R2Wfm.round2_weighted_field_moments_proof
#print axioms checked231

theorem checked232 : type_of% @HRS.Whole.same_function_rd :=
  @HRS.MS.SameFunction.same_function_rd_proof
#print axioms checked232

theorem checked233 : type_of% @HRS.Whole.same_function_rd_weighted :=
  @HRS.MS.Sf8.same_function_rd_weighted_proof
#print axioms checked233

theorem checked234 : type_of% @HRS.Whole.screened_comm_cell :=
  @HRS.MH.Screened.screened_comm_cell_proof
#print axioms checked234

theorem checked235 : type_of% @HRS.Whole.screened_comm_local :=
  @HRS.MH.Screened.screened_comm_local_proof
#print axioms checked235

theorem checked236 : type_of% @HRS.Whole.screened_far :=
  @HRS.MH.Screened.screened_far_proof
#print axioms checked236

theorem checked237 : type_of% @HRS.Whole.screened_local :=
  @HRS.MH.Screened.screened_local_proof
#print axioms checked237

theorem checked238 : type_of% @HRS.Whole.screened_local_global :=
  @HRS.MH.Screened.screened_local_global_proof
#print axioms checked238

theorem checked239 : type_of% @HRS.Whole.screened_pairing :=
  @HRS.MH.Screened.screened_pairing_proof
#print axioms checked239

theorem checked240 : type_of% @HRS.Whole.screened_pairing_pos :=
  @HRS.MH.Screened.screened_pairing_pos_proof
#print axioms checked240

theorem checked241 : type_of% @HRS.Whole.sharp_all_sub :=
  @HRS.MS.AdjDecay.sharp_all_sub_proof
#print axioms checked241

theorem checked242 : type_of% @HRS.Whole.sharp_bias :=
  @HRS.Whole.S71.sharp_bias_proof
#print axioms checked242

theorem checked243 : type_of% @HRS.Whole.sharp_bias_quadratic :=
  @HRS.Whole.S71.sharp_bias_quadratic_proof
#print axioms checked243

theorem checked244 : type_of% @HRS.Whole.sharp_bias_uniform_beta :=
  @HRS.Whole.S71.sharp_bias_uniform_beta_proof
#print axioms checked244

theorem checked245 : type_of% @HRS.Whole.sharp_insertion_radius :=
  @HRS.MS.S76.sharp_insertion_radius_proof
#print axioms checked245

theorem checked246 : type_of% @HRS.Whole.sharp_insertion_rate :=
  @HRS.MS.S76.sharp_insertion_rate_proof
#print axioms checked246

theorem checked247 : type_of% @HRS.Whole.sharp_tail_bound :=
  @HRS.Whole.sharp_tail_bound_proof
#print axioms checked247

theorem checked248 : type_of% @HRS.Whole.sharp_threshold_critical :=
  @HRS.Whole.S78.sharp_threshold_critical_proof
#print axioms checked248

theorem checked249 : type_of% @HRS.Whole.sharp_threshold_supercritical :=
  @HRS.Whole.S78.sharp_threshold_supercritical_proof
#print axioms checked249

theorem checked250 : type_of% @HRS.Whole.shifted_field_path :=
  @HRS.Whole.S79.shifted_field_path_proof
#print axioms checked250

theorem checked251 : type_of% @HRS.Whole.shifted_field_static :=
  @HRS.Whole.S79.shifted_field_static_proof
#print axioms checked251

theorem checked252 : type_of% @HRS.Whole.spectral_space :=
  @HRS.MS.Spec.spectral_space_proof
#print axioms checked252

theorem checked253 : type_of% @HRS.Whole.static_input :=
  @HRS.MS.Wr.static_input_proof
#print axioms checked253

theorem checked254 : type_of% @HRS.Whole.static_input_uniform_beta :=
  @HRS.MS.Wr.static_input_uniform_beta_proof
#print axioms checked254

theorem checked255 : type_of% @HRS.Whole.thermalDensity_spec :=
  @HRS.MS.Thm.thermalDensity_spec_proof
#print axioms checked255

theorem checked256 : type_of% @HRS.Whole.thermal_corrector :=
  @HRS.MS.Tc6.thermal_corrector_proof
#print axioms checked256

theorem checked257 : type_of% @HRS.Whole.thermal_corrector_sobolev :=
  @HRS.MS.Tc6.thermal_corrector_sobolev_proof
#print axioms checked257

theorem checked258 : type_of% @HRS.Whole.tilt_static :=
  @HRS.MS.Tilt.tilt_static_proof
#print axioms checked258

theorem checked259 : type_of% @HRS.Whole.tilt_static_mean_field :=
  @HRS.MS.Tilt.tilt_static_mean_field_proof
#print axioms checked259

theorem checked260 : type_of% @HRS.Whole.tilt_static_osc :=
  @HRS.MS.Tilt.tilt_static_osc_proof
#print axioms checked260

theorem checked261 : type_of% @HRS.Whole.ul_adjoint_fixed_viscosity :=
  @HRS.MS.Ul.ul_adjoint_fixed_viscosity_proof
#print axioms checked261

theorem checked262 : type_of% @HRS.Whole.ul_adjoint_orbit_bounds :=
  @HRS.MS.Ul.ul_adjoint_orbit_bounds_proof
#print axioms checked262

theorem checked263 : type_of% @HRS.Whole.weighted_adjoint_decay :=
  @HRS.MS.Wad.weighted_adjoint_decay_proof
#print axioms checked263

theorem checked264 : type_of% @HRS.Whole.weighted_critical_forcing :=
  @HRS.MS.R26T8A.r26t8a_weighted_critical_forcing_tied
#print axioms checked264

theorem checked265 : type_of% @HRS.Whole.weighted_higher_order :=
  @HRS.MS.Who.weighted_higher_order_proof
#print axioms checked265

theorem checked266 : type_of% @HRS.Whole.weighted_remainder :=
  @HRS.Whole.S77.weighted_remainder_proof
#print axioms checked266

theorem checked267 : type_of% @HRS.Whole.whole_commutator_sub_lower :=
  @HRS.Commutator.Whole.whole_commutator_sub_lower_of_subcoulomb
#print axioms checked267

theorem checked268 : type_of% @HRS.Whole.whole_commutator_sub_sharp :=
  @HRS.Commutator.Whole.whole_commutator_sub_sharp_of_subcoulomb
#print axioms checked268

theorem checked269 : type_of% @HRS.Whole.whole_commutator_super :=
  @HRS.MH.CommSuper.whole_commutator_super_of_concentration_proof
#print axioms checked269

theorem checked270 : type_of% @HRS.b15_sde_entropy_law_free :=
  @HRS.b15_sde_entropy_law_free_proof
#print axioms checked270

theorem checked271 : type_of% @HRS.b15_sde_entropy_law_of_free_proof :=
  @HRS.hrsReaderEntropyDispatcher
#print axioms checked271

theorem checked272 : type_of% @HRS.bounded_featureMap :=
  @HRS.MH.FeatureMap.bounded_featureMap_proof
#print axioms checked272

theorem checked273 : type_of% @HRS.cavity_response :=
  @HRS.cavity_response_proof
#print axioms checked273

theorem checked274 : type_of% @HRS.cepa_entropy_confined :=
  by intros; apply @HRS.MC.CepH5Fin.cep_H5_entropy_confined_proof <;> assumption
#print axioms checked274

theorem checked275 : type_of% @HRS.cepa_log_flow :=
  @HRS.MC.CepB2.cepa_log_flow_repaired_proof
#print axioms checked275

theorem checked276 : type_of% @HRS.cepa_noncollision_iff_threshold :=
  @HRS.MC.CepB13.cepa_noncollision_iff_threshold_proof
#print axioms checked276

theorem checked277 : type_of% @HRS.chaos_isonormal_basis_independent :=
  @HRS.MC.E718B.chaos_isonormal_basis_independent_proof
#print axioms checked277

theorem checked278 : type_of% @HRS.chaos_laws_not_tight :=
  @HRS.MC.E718.chaos_laws_not_tight_proof
#print axioms checked278

theorem checked279 : type_of% @HRS.chaos_no_L2_limit :=
  @HRS.MC.E718.chaos_no_L2_limit_proof
#print axioms checked279

theorem checked280 : type_of% @HRS.commutator_coercivity_common :=
  @HRS.commutator_coercivity_common_proof
#print axioms checked280

theorem checked281 : type_of% @HRS.commutator_estimate :=
  @HRS.Commutator.commutator_estimate_of_packets
#print axioms checked281

theorem checked282 : type_of% @HRS.comparison_kernel_identity :=
  @HRS.KID.comparison_kernel_identity_proof
#print axioms checked282

theorem checked283 : type_of% @HRS.conditional_singular_observation :=
  @HRS.conditional_singular_observation_proof
#print axioms checked283

theorem checked284 : type_of% @HRS.conditioned_example :=
  @HRS.ME.CondExampleFinal.conditioned_example_proof
#print axioms checked284

theorem checked285 : type_of% @HRS.continuous_featureMap :=
  @HRS.MH.FeatureMap.continuous_featureMap_proof
#print axioms checked285

theorem checked286 : type_of% @HRS.convGradConv_coeff_of_holder :=
  @HRS.MH.ConventionHolder.convGradConv_coeff_of_holder_proof
#print axioms checked286

theorem checked287 : type_of% @HRS.convGradConv_eq_convGradHolder :=
  @HRS.MH.ConventionHolder.convGradConv_eq_convGradHolder_proof
#print axioms checked287

theorem checked288 : type_of% @HRS.cosine_tilt_example :=
  @HRS.ME.CosineTiltFinal.cosine_tilt_example_proof
#print axioms checked288

theorem checked289 : type_of% @HRS.criterion_comparison :=
  @HRS.criterion_comparison_proof_aem
#print axioms checked289

theorem checked290 : type_of% @HRS.criterion_stationary :=
  @HRS.criterion_stationary_proof
#print axioms checked290

theorem checked291 : type_of% @HRS.dynamic_comparison :=
  @HRS.dynamic_comparison_proof'
#print axioms checked291

theorem checked292 : type_of% @HRS.dynamic_comparison_proof :=
  @HRS.dynamic_comparison_proof'
#print axioms checked292

theorem checked293 : type_of% @HRS.dynamic_convergence :=
  @HRS.dynamic_convergence_proof
#print axioms checked293

theorem checked294 : type_of% @HRS.dynamic_entropy :=
  @HRS.dynamic_entropy_proof'
#print axioms checked294

theorem checked295 : type_of% @HRS.dynamic_entropy_proof :=
  @HRS.dynamic_entropy_proof'
#print axioms checked295

theorem checked296 : type_of% @HRS.energy_identity_featureMap :=
  @HRS.MH.FeatureMap.energy_identity_featureMap_proof
#print axioms checked296

theorem checked297 : type_of% @HRS.energy_identity_negSpectral :=
  @HRS.MH.FeatureMap.energy_identity_negSpectral_proof
#print axioms checked297

theorem checked298 : type_of% @HRS.energy_identity_of_feature :=
  @HRS.MH.FeatureMap.energy_identity_of_feature_proof
#print axioms checked298

theorem checked300 : type_of% @HRS.fdl_compare :=
  @HRS.MC.D47.fdl_compare_proof
#print axioms checked300

theorem checked301 : type_of% @HRS.fdl_compare_reverse_false :=
  @HRS.MC.D4R.fdl_compare_reverse_false_proof
#print axioms checked301

theorem checked302 : type_of% @HRS.fdl_ito :=
  @HRS.MC.D47.fdl_ito_proof
#print axioms checked302

theorem checked303 : type_of% @HRS.fdl_kernel_euclid :=
  @HRS.MC.D3EAsm.fdl_kernel_euclid_proof
#print axioms checked303

theorem checked304 : type_of% @HRS.fdl_kernel_torus :=
  @HRS.MC.D3TAsm.fdl_kernel_torus_proof
#print axioms checked304

theorem checked305 : type_of% @HRS.fdl_rep :=
  @HRS.MC.D1ASM.fdl_rep_proof
#print axioms checked305

theorem checked306 : type_of% @HRS.fdl_scope :=
  @HRS.MC.D47.fdl_scope_proof
#print axioms checked306

theorem checked307 : type_of% @HRS.featureMap_inner :=
  @HRS.MH.FeatureMap.featureMap_inner_proof
#print axioms checked307

theorem checked308 : type_of% @HRS.featureMap_norm_sq :=
  @HRS.MH.FeatureMap.featureMap_norm_sq_proof
#print axioms checked308

theorem checked309 : type_of% @HRS.gronwall_gradient_flow :=
  @HRS.gronwall_gradient_flow_proof
#print axioms checked309

theorem checked310 : type_of% @HRS.gronwall_zero_temperature :=
  @HRS.gronwall_zero_temperature_proof
#print axioms checked310

theorem checked311 : type_of% @HRS.gronwall_zero_temperature_moment :=
  @HRS.gronwall_zero_temperature_moment_proof
#print axioms checked311

theorem checked312 : type_of% @HRS.iid_field_comparison :=
  @HRS.iid_field_comparison_proof
#print axioms checked312

theorem checked313 : type_of% @HRS.iid_field_mixture :=
  @HRS.iid_field_mixture_proof
#print axioms checked313

theorem checked314 : type_of% @HRS.insertion_coefficient :=
  @HRS.insertion_coefficient_proof
#print axioms checked314

theorem checked315 : type_of% @HRS.integrable_convGradConv_integrand_of_holder :=
  @HRS.MH.ConventionHolder.integrable_convGradConv_integrand_of_holder_proof
#print axioms checked315

theorem checked316 : type_of% @HRS.integrable_featureMap :=
  @HRS.MH.FeatureMap.integrable_featureMap_proof
#print axioms checked316

theorem checked317 : type_of% @HRS.integrated_forcing :=
  @HRS.ME.integrated_forcing_proof
#print axioms checked317

theorem checked318 : type_of% @HRS.integrated_taylor_remainder :=
  @HRS.integrated_taylor_remainder_proof
#print axioms checked318

theorem checked319 : type_of% @HRS.lowtemp_coulomb_bound :=
  @HRS.MD.LT337Final.lowtemp_coulomb_bound_proof
#print axioms checked319

theorem checked320 : type_of% @HRS.lowtemp_coulomb_threshold :=
  @HRS.MD.LT337Final.lowtemp_coulomb_threshold_proof
#print axioms checked320

theorem checked321 : type_of% @HRS.mean_particles :=
  @HRS.mean_particles_proof
#print axioms checked321

theorem checked322 : type_of% @HRS.mfe_uniform :=
  @HRS.mfe_uniform_proof'
#print axioms checked322

theorem checked323 : type_of% @HRS.moving_integrated_forcing :=
  @HRS.moving_integrated_forcing_proof
#print axioms checked323

theorem checked324 : type_of% @HRS.moving_log_moment :=
  @HRS.moving_log_moment_proof'
#print axioms checked324

theorem checked325 : type_of% @HRS.moving_log_moment_proof :=
  @HRS.moving_log_moment_proof'
#print axioms checked325

theorem checked326 : type_of% @HRS.moving_pair_moments :=
  @HRS.moving_pair_moments_proof'
#print axioms checked326

theorem checked327 : type_of% @HRS.moving_pair_moments_proof :=
  @HRS.moving_pair_moments_proof'
#print axioms checked327

theorem checked328 : type_of% @HRS.negSpectral_grad_unbounded :=
  @HRS.MC.L5566.negSpectral_grad_unbounded_proof
#print axioms checked328

theorem checked329 : type_of% @HRS.normal_form :=
  @HRS.normal_form_proof
#print axioms checked329

theorem checked330 : type_of% @HRS.pair_moments :=
  @HRS.pair_moments_proof
#print axioms checked330

theorem checked331 : type_of% @HRS.pair_poisson :=
  @HRS.pair_poisson_proof
#print axioms checked331

theorem checked332 : type_of% @HRS.pair_poisson_full :=
  @HRS.pair_poisson_full_proof
#print axioms checked332

theorem checked333 : type_of% @HRS.pin_comparison :=
  @HRS.pin_comparison_proof
#print axioms checked333

theorem checked334 : type_of% @HRS.product_moment_transfer :=
  @HRS.product_moment_transfer_proof
#print axioms checked334

theorem checked335 : type_of% @HRS.quadratic_limit :=
  @HRS.quadratic_limit_proof
#print axioms checked335

theorem checked336 : type_of% @HRS.reference_marginal_linf :=
  @HRS.reference_marginal_linf_proof
#print axioms checked336

theorem checked337 : type_of% @HRS.response_subGaussian :=
  @HRS.response_subGaussian_proof
#print axioms checked337

theorem checked338 : type_of% @HRS.screening_comparison :=
  @HRS.screening_comparison_proof
#print axioms checked338

theorem checked339 : type_of% @HRS.screening_stationary_limit :=
  @HRS.screening_stationary_limit_proof
#print axioms checked339

theorem checked340 : type_of% @HRS.sde_entropy_law :=
  @HRS.sde_entropy_law_proof
#print axioms checked340

theorem checked341 : type_of% @HRS.selected_law_smoothing :=
  by intros; apply @HRS.MC.CepP6.cep_P6_selected_law_smoothing_proof <;> assumption
#print axioms checked341

theorem checked342 : type_of% @HRS.thermal_response_rates :=
  @HRS.TRR.thermal_response_rates_proof
#print axioms checked342

theorem checked343 : type_of% @HRS.transport_bound_uniform :=
  @HRS.transport_bound_uniform_proof
#print axioms checked343

theorem checked344 : type_of% @HRS.triple_canonical :=
  @HRS.triple_canonical_proof
#print axioms checked344

theorem checked345 : type_of% @HRS.ui_comparison :=
  @HRS.ME.Ret.ui_comparison_proof
#print axioms checked345

theorem checked346 : type_of% @HRS.ui_of_entropy_bound :=
  @HRS.ME.UIEntropyFrozen.ui_of_entropy_bound_proof
#print axioms checked346

theorem checked347 : type_of% @HRS.ui_path_initial :=
  @HRS.ME.UIPathInitial.p_assembly
#print axioms checked347

theorem checked348 : type_of% @HRS.ui_path_shifted :=
  @HRS.ME.UIPathShifted.p_assembly
#print axioms checked348

theorem checked349 : type_of% @HRS.ui_path_tight :=
  @HRS.ME.UIPathTight.p6_assembly
#print axioms checked349

theorem checked350 : type_of% @HRS.ui_qualitative :=
  @HRS.ME.Ret.ui_qualitative_proof
#print axioms checked350

end HRSReaderEvidence

import HRS.Whole.AppendixALemmas2
import HRS.MP.InitModulus
import HRS.Main.A8PAux7
import HRS.Main.A9Aux7

/-!
# Packet MPDUAL: the evaluation-level three-term decomposition of `σ_N Ξ_N^t` on the torus

For smooth mean-zero `φ`, a.s. at each `t ∈ [0,T]`,
`⟨φ, σ_N Ξ_N^t⟩ = ⟨φ, 𝓘_{N,emp}^t⟩ + σ_N M_N^t[U^{·,t}φ] + σ_N ∫_0^t B_{U^{r,t}φ}(Fluc_N^r) dr`
(the fixed-time duality identity `duality_identity_final` together with the evaluation of the transported
initial field `A_N V^{t,0}(κ_N Ξ_N^0)` against `φ`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MP.DualDec

open HRS HRS.PDE HRS.Main HRS.Whole.AppendixALemmas

variable {d : ℕ}

/-- Evaluation of a transported (scaled) embedded measure difference against a smooth test. -/
theorem mdd_eval_transport (hd : 1 ≤ d) {s : ℝ} (Rg : Regime) (MB Λ VB ν₀ T : ℝ) (D : DynData d)
    (ρ : ℝ → Torus d → ℝ) (hA : AdjointData s (gammaIdx d) Rg MB Λ VB D ν₀ T ρ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) (A κ : ℝ) (μ ν : Measure (Torus d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    NegSobolev.eval (A • transportField D ρ t ((qT d : ℕ) : ℝ)
        (κ • NegSobolev.ofMeasureDiff ((qT d : ℕ) : ℝ) μ ν)) φ =
      A * κ * (pair μ (propagator D ρ 0 t φ) - pair ν (propagator D ρ 0 t φ)) := by
  obtain ⟨hg2, hq2⟩ := HRS.MP.InitMod.mim_gamma_bounds (d := d)
  have hA' : AdjointData D.s (gammaIdx d) Rg MB Λ VB D ν₀ T ρ := by rw [hA.hs]; exact hA
  rw [Main.A9.a9_eval_smul]
  rw [← HRS.MP.InitMod.mim_embed_smul_ofMeasureDiff HRS.MP.InitMod.mim_gamma_le_q hg2 hq2 κ μ ν,
    HRS.MP.InitMod.mim_tf_embed hd Rg MB Λ VB ν₀ T D ρ hA' ht,
    HRS.MP.InitMod.mim_eval_embed HRS.MP.InitMod.mim_gamma_le_q]
  obtain ⟨e⟩ := HRS.A33.a33_exists_equiv hd
  let Su : HRS.A33.A33Setup d := HRS.Main.A9.a9Setup hd Rg MB Λ VB ν₀ D T ρ hA'
  have htr := Su.eval_transport (t := t) ht e
    (κ • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ) μ ν) hφ
  have h1 : NegSobolev.eval (transportField D ρ t (gammaIdx d : ℝ)
      (κ • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ) μ ν)) φ =
      NegSobolev.eval (κ • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ) μ ν)
        (propagator D ρ 0 t φ) := htr
  rw [h1, Main.A9.a9_eval_smul]
  obtain ⟨K, -, hK⟩ := Su.U_bound
  have hmem : MemSobolev (gammaIdx d : ℝ) (propagator D ρ 0 t φ) := (hK (t := t) ht hφ).1
  have hcont : Continuous (propagator D ρ 0 t φ) := Su.U_cont (t := t) ht hφ
  rw [Main.A9.a9_eval_ofMeasureDiff Main.A9.a9_gamma_gt μ ν hmem hcont]
  ring

theorem mdd_eval_decomp {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ} {𝔈 : ℕ → ℝ} (S : Main.MainData d)
    (R : ∀ N, Main.Realization d N)
    (hS : Main.TorusStanding S R Rg ν₀ MB Λ VB (Main.gammaIdx d + 2) C₀ Cc 𝔈)
    {N : ℕ} (hN : 2 ≤ N) (ℱ : Filtration ℝ (R N).mΩ) (W' : ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ)
    (hF : IsFilteredSolution (R N).P ℱ W' (R N).W (R N).X)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T) (φ : Torus d → ℝ) (hφ : Torus.IsSmooth φ)
    (hφ0 : Torus.mean φ = 0) :
    ∀ᵐ ζ ∂(R N).P,
      NegSobolev.eval (S.sigma N • NegSobolev.ofMeasureDiff ((HRS.Whole.AppendixALemmas.qT d : ℕ) : ℝ)
          (empirical ((R N).X (Real.toNNReal t) ζ)) (withDensityReal (S.ρ N t))) φ =
        NegSobolev.eval (HRS.Whole.AppendixALemmas.transportedEmpT S R (HRS.Whole.AppendixALemmas.qT d) N t ζ) φ +
        S.sigma N * empiricalMartingale (R N).P ℱ W' (S.dyn N) t
            (fun r => propagator (S.dyn N) (S.ρ N) r t φ) (R N).X t ζ +
        S.sigma N * ∫ r in (0 : ℝ)..t,
            flucInteraction (S.dyn N) (propagator (S.dyn N) (S.ρ N) r t φ)
              ((R N).X (Real.toNNReal r) ζ) (S.ρ N r) := by
  have hd : 1 ≤ d := S.hd
  have hN1 : 1 ≤ N := by omega
  obtain ⟨Ca, Λ₁, hCa, hspec⟩ := HRS.Main.A8P.a8p_adjSpec hd S.s S.hs0 S.hsd Rg MB Λ VB ν₀
  have hmS : PDE.mStar d ≤ gammaIdx d + 2 := by unfold gammaIdx; omega
  have hSm : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈 :=
    Main.A9.a9_standing_mono hmS hS
  have hφS : MemSobolev (PDE.mStar d : ℝ) φ := MFSemigroup.memSobolev_of_isSmooth hφ _
  have hdual := HRS.Main.A8P.a8p_dual_coord hspec hCa.le hSm hN ht (HRS.MP.KernIncr.mpk_cont_of_smooth hφ)
    hφS hF
  have hA : AdjointData S.s (gammaIdx d) Rg MB Λ VB (S.dyn N) ν₀ S.T (S.ρ N) :=
    Main.A9.a9_adjointData (by unfold gammaIdx; omega) (Main.A9.a9_standing_mono (by omega) hS) hN1
  obtain ⟨-, -, hX0⟩ := HRS.Main.A8P.a8p_flow_facts hSm hN1
  haveI : IsProbabilityMeasure S.μ0 := S.hμ0
  haveI := (R N).isProb
  have hρt : ∀ r ∈ Set.Icc (0 : ℝ) S.T, IsProbabilityMeasure (withDensityReal (S.ρ N r)) := fun r hr =>
    HRS.isProb_withDensityReal ((hS.mean_field.solution N hN1).density r hr)
  haveI := hρt t ht
  obtain ⟨hg2, hq2⟩ := HRS.MP.InitMod.mim_gamma_bounds (d := d)
  filter_upwards [hdual, hX0] with ζ h1 h2
  haveI : IsProbabilityMeasure (empirical ((R N).X (Real.toNNReal t) ζ)) :=
    empirical_isProbabilityMeasure hN1 _
  haveI : IsProbabilityMeasure (empirical ((R N).X₀ ζ)) := empirical_isProbabilityMeasure hN1 _
  have hL : NegSobolev.eval (S.sigma N • NegSobolev.ofMeasureDiff ((qT d : ℕ) : ℝ)
      (empirical ((R N).X (Real.toNNReal t) ζ)) (withDensityReal (S.ρ N t))) φ =
      S.sigma N * flucPair ((R N).X (Real.toNNReal t) ζ) (S.ρ N t) φ := by
    rw [Main.A9.a9_eval_smul, NegSobolev.eval_ofMeasureDiff hq2 _ _ φ hφ]
    rfl
  have hT : NegSobolev.eval (transportedEmpT S R (qT d) N t ζ) φ =
      S.sigma N * flucPair ((R N).X 0 ζ) (S.ρ N 0) (propagator (S.dyn N) (S.ρ N) 0 t φ) := by
    unfold transportedEmpT
    rw [mdd_eval_transport hd Rg MB Λ VB ν₀ S.T (S.dyn N) (S.ρ N) hA ht (S.AN N) (S.κ N) _ _ hφ,
      HRS.Main.A8P.a8p_A_mul_kappa, h2]
    unfold flucPair
    rw [hS.mean_field.datum N hN1]
  rw [hL, hT, h1, Real.coe_toNNReal t ht.1]
  ring

end HRS.MP.DualDec

import HRS.Sections.Q40bAux12
import HRS.Sections.Q40bAux13
import HRS.Sections.Q40bAux14

/-!
# Packet Q40b, part 15: Proposition 5.14, stationary comparison (`criterion_stationary`)

Relocated proof: `criterion_stationary_proof` has the verbatim statement of `HRS.criterion_stationary`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section
namespace HRS

variable {d : ℕ}

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

set_option maxHeartbeats 4000000 in
theorem criterion_stationary_proof (hd : 2 ≤ d) {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρS : Torus.IsSmooth ρβ)
    (hρpos : ∀ x, 0 < ρβ x) (j : ℕ) (hj : Even j) (hjd : (d : ℝ) / 2 + 4 < j) (p : ℕ)
    (φ : Fin p → Torus d → ℝ) (hφ : ∀ a, Torus.IsSmooth (φ a)) (C₁ M : ℝ) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ S : ParticleSeq d,
      (∀ T : ℝ, 0 ≤ T → S.IsSolutionOn htr.dyn T) →
      (∀ n, ∃ (ℱ : MeasureTheory.Filtration ℝ (S.mΩ n))
          (W' : ℝ≥0 → S.Ω n → (Fin (n + 2) × Fin d) → ℝ),
        IsFilteredSolution (S.P n) ℱ W' (S.W n) (S.X n)) →
      (∀ n, relEntropy ((S.P n).map (S.X₀ n))
        (modulatedGibbs (periodicRiesz d s) (n + 2) β (withDensityReal (ρ 0))) ≠ ⊤) →
      (∀ n, ∀ t : ℝ, 0 ≤ t →
        relEntropy ((S.P n).map (S.X n t.toNNReal))
              (modulatedGibbs (periodicRiesz d s) (n + 2) β (withDensityReal (ρ t))) +
            relEntropy ((S.P n).map (S.X n t.toNNReal))
              (Measure.pi fun _ => withDensityReal (ρ t)) ≤
          ENNReal.ofReal (C₁ * entropyScale d s (n + 2) ((S.P n).map (S.X₀ n))
            (modulatedGibbs (periodicRiesz d s) (n + 2) β (withDensityReal (ρ 0))))) →
      Tendsto (fun n : ℕ => entropyScale d s (n + 2) ((S.P n).map (S.X₀ n))
        (modulatedGibbs (periodicRiesz d s) (n + 2) β (withDensityReal (ρ 0))) / ((n + 2 : ℕ) : ℝ))
        atTop (𝓝 0) →
      Tendsto (fun n : ℕ => criterionRemainder htr.dyn ρ ρβ j (S.P n) (S.X n)) atTop (𝓝 0) →
      (∀ n, ∫⁻ ω, ‖zetaE (j : ℝ) ((S.P n).map (S.X₀ n)) (S.X₀ n ω)‖ₑ ∂(S.P n) ≤
        ENNReal.ofReal M) →
      ∀ n : ℕ, ∀ u : ℝ, 0 ≤ u → ∀ τ : Fin p → ℝ, (∀ a, 0 ≤ τ a) →
          ENNReal.ofReal (smoothDist 2
              (law (S.P n) fun ω => (WithLp.toLp 2 fun a =>
                zetaStat (S.P n) (S.X n) (u + τ a) (φ a) ω : EuclideanSpace ℝ (Fin p)))
              (ProbabilityTheory.multivariateGaussian 0
                (PDE.stationaryLagCov d s β htr.dyn ρβ τ φ))) ≤
            ENNReal.ofReal C * (criterionRemainder htr.dyn ρ ρβ j (S.P n) (S.X n) +
              ENNReal.ofReal (Real.sqrt (entropyScale d s (n + 2) ((S.P n).map (S.X₀ n))
                (modulatedGibbs (periodicRiesz d s) (n + 2) β (withDensityReal (ρ 0))) /
                  ((n + 2 : ℕ) : ℝ))) + ENNReal.ofReal (Real.exp (-c * u))) := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hjd' : (d : ℝ) / 2 < j := by linarith
  have hK := Q40b.q40b_K_ok d j
  have H := Q40b.q40b_finiteRegHyp htr hK
  obtain ⟨ρc, hρc, hρ⟩ := Q40b.q40b_sol htr hK
  have hρβc : Continuous ρβ := PDE.MFLinear.continuous_of_isSmooth hρS
  have hβmem : β ∈ Set.Icc β β := ⟨le_rfl, le_rfl⟩
  obtain ⟨Cv, cv, hCv, hcv, hcov⟩ := Q40b.q40b_cov_uniform hd1 s β β (2 * j + 4 * d + 20) V ρ₀ H
    j hj hjd le_rfl β hβmem ρc hρc ρβ hρβ hρβc hρpos p φ hφ
  choose C₂ c₂ hC₂ hc₂ hinit using fun a =>
    PDE.MFLinear.exists_initial_part_bound hd1 s β β (2 * j + 4 * d + 20) V ρ₀ H j hj hjd le_rfl β
      hβmem ρc hρc ρβ hρβ hρβc hρpos (φ a) (hφ a)
  obtain ⟨Ca, m, hCa0, hm, hclass, hgrad⟩ :=
    Q40b.q40b_adjoint_all hd htr hρβ hρS hρpos hj hjd hφ
  set L : Fin p → ℝ := fun a => sobolevNorm (j : ℝ) (projMean (withDensityReal ρβ) (φ a)) with hL
  have hL0 : ∀ a, 0 ≤ L a := fun a => Real.sqrt_nonneg _
  have hβ : 0 < β := htr.hβ
  set K : ℝ := ∑ a, ∑ b, 2 * β⁻¹ * Ca a * Ca b / (2 * m) with hKdef
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by
    have := hCa0 a; have := hCa0 b; positivity
  set c₁ : ℝ := max C₁ 0 with hc₁
  have hc₁0 : 0 ≤ c₁ := le_max_right _ _
  set K' : ℝ := (1 / 2) * K * Real.sqrt (2 * (c₁ + 1)) with hK'
  have hK'0 : 0 ≤ K' := by positivity
  have hLs : 0 ≤ ∑ a, (L a + 1) := Finset.sum_nonneg fun a _ => by linarith [hL0 a]
  have hS0 : 0 ≤ ∑ a, 1 / c₂ a := Finset.sum_nonneg fun a _ => (one_div_pos.2 (hc₂ a)).le
  set c₀ : ℝ := 1 / (1 + ∑ a, 1 / c₂ a) with hc₀
  have hc₀pos : 0 < c₀ := one_div_pos.2 (by linarith)
  have hc₀le : ∀ a, c₀ ≤ c₂ a := by
    intro a
    have hS : 1 / c₂ a ≤ ∑ b, 1 / c₂ b :=
      Finset.single_le_sum (f := fun b => 1 / c₂ b) (fun b _ => (one_div_pos.2 (hc₂ b)).le)
        (Finset.mem_univ a)
    have h1 : 1 / (1 + ∑ b, 1 / c₂ b) ≤ 1 / (1 / c₂ a) :=
      one_div_le_one_div_of_le (one_div_pos.2 (hc₂ a)) (by linarith)
    rwa [one_div_one_div] at h1
  set c : ℝ := min cv c₀ with hcdef
  have hcpos : 0 < c := lt_min hcv hc₀pos
  have hc_cv : c ≤ cv := min_le_left _ _
  have hc_c₂ : ∀ a, c ≤ c₂ a := fun a => (min_le_right _ _).trans (hc₀le a)
  set S₂ : ℝ := ∑ a, C₂ a with hS₂
  have hS₂0 : 0 ≤ S₂ := Finset.sum_nonneg fun a _ => (hC₂ a).le
  set M₀ : ℝ := max M 0 with hM₀
  have hM₀0 : 0 ≤ M₀ := le_max_right _ _
  set Q : ℝ := S₂ * M₀ + (1 / 2) * ((p : ℝ) ^ 2 * Cv) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  refine ⟨∑ a, (L a + 1) + K' + Q + 1, c, by linarith, hcpos, ?_⟩
  intro S hsol hfilt hfin hent _ _ hzeta n u hu τ hτ
  set t : Fin p → ℝ := fun a => u + τ a with htdef
  have ht : ∀ a, 0 ≤ t a := fun a => add_nonneg hu (hτ a)
  obtain ⟨ℱ, W', hfl⟩ := hfilt n
  -- the entropy bounds
  set Bn : ℝ := entropyScale d s (n + 2) ((S.P n).map (S.X₀ n))
    (modulatedGibbs (periodicRiesz d s) (n + 2) β (withDensityReal (ρ 0))) with hBn
  have hB2 : 2 ≤ Bn := by
    have h1 : 1 ≤ ((n + 2 : ℕ) : ℝ) * deltaN d s (n + 2) :=
      one_le_mul_deltaN htr.hs0 (n + 2) (by omega)
    have h2 := ENNReal.toReal_nonneg (a := relEntropy ((S.P n).map (S.X₀ n))
      (modulatedGibbs (periodicRiesz d s) (n + 2) β (withDensityReal (ρ 0))))
    rw [hBn]; unfold entropyScale; linarith
  have hBn0 : 0 ≤ Bn := by linarith
  have hH₁ : 0 ≤ c₁ * Bn := mul_nonneg hc₁0 hBn0
  have hentB : ∀ r : ℝ, 0 ≤ r → relEntropy ((S.P n).map (S.X n r.toNNReal))
        (modulatedGibbs (periodicRiesz d s) (n + 2) β (withDensityReal (ρ r))) +
      relEntropy ((S.P n).map (S.X n r.toNNReal))
        (Measure.pi fun _ => withDensityReal (ρ r)) ≤ ENNReal.ofReal (c₁ * Bn) := by
    intro r hr
    refine (hent n r hr).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hBn0
  obtain ⟨γ, hγeq⟩ : ∃ γ : Measure (ℝ^p), γ = ProbabilityTheory.multivariateGaussian (0 : ℝ^p)
      (noiseCovMatrix htr.dyn ρ β⁻¹ t φ) := ⟨_, rfl⟩
  haveI hγ : IsProbabilityMeasure γ := by rw [hγeq]; infer_instance
  have hM := Q40b.q40b_master_gamma (P := S.P n) hd htr (by omega : 2 ≤ n + 2)
    (fun T hT => (hsol T hT n).sol) hfl hH₁ (fun r hr => le_trans le_self_add (hentB r hr))
    (fun r hr => le_trans le_add_self (hentB r hr)) t ht φ hφ Ca m hCa0 hm hclass hgrad γ hγeq
  -- measurability
  have hXm : ∀ r : ℝ≥0, Measurable (S.X n r) := fun r => (hfl.adapted r).mono (ℱ.le _) le_rfl
  have hψc : ∀ a, Continuous (propagator htr.dyn ρ 0 (t a) (φ a)) := by
    intro a
    obtain ⟨F, hFcl, hFp⟩ := hclass a (t a) (ht a)
    rw [hFp 0 ⟨le_rfl, ht a⟩]
    exact PDE.MFAux.continuous_of_isCk (PDE.ClassicalAux.isCk_of_le (by norm_num)
      (hFcl.c2 0 ⟨le_rfl, ht a⟩))
  have hζm : ∀ ψ' : Torus d → ℝ, Continuous ψ' →
      Measurable (fun ω => zetaStat (S.P n) (S.X n) 0 ψ' ω) := by
    intro ψ' hψ'
    unfold zetaStat
    refine measurable_const.mul (Measurable.sub (measurable_const.mul ?_) measurable_const)
    exact Finset.measurable_sum _ fun i _ =>
      hψ'.measurable.comp ((measurable_pi_apply i).comp (hXm _))
  set Zv : S.Ω n → ℝ^p := fun ω => WithLp.toLp 2 fun a =>
    zetaStat (S.P n) (S.X n) 0 (propagator htr.dyn ρ 0 (t a) (φ a)) ω with hZv
  have hZvm : Measurable Zv :=
    (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable.comp
      (measurable_pi_iff.2 fun a => hζm _ (hψc a))
  -- step 2: the Gaussian shift
  have hCm : (((S.P n).map Zv).prod γ).map (fun r : (ℝ^p) × (ℝ^p) => r.1 + r.2) =
      ((S.P n).prod γ).map (fun q : S.Ω n × (ℝ^p) => Zv q.1 + q.2) := by
    have hadd : Measurable (fun r : (ℝ^p) × (ℝ^p) => r.1 + r.2) :=
      measurable_fst.add measurable_snd
    have hpm : ((S.P n).map Zv).prod (γ.map id) = ((S.P n).prod γ).map (Prod.map Zv id) :=
      Measure.map_prod_map (S.P n) γ hZvm measurable_id
    rw [Measure.map_id] at hpm
    rw [hpm, Measure.map_map hadd (hZvm.prodMap measurable_id)]
    rfl
  have hsnd : ((S.P n).prod γ).map (Prod.snd : S.Ω n × (ℝ^p) → ℝ^p) = γ :=
    (measurePreserving_snd (μ := S.P n) (ν := γ)).map_eq
  have hZ2 : ENNReal.ofReal (smoothDist 2
      ((((S.P n).map Zv).prod γ).map fun r : (ℝ^p) × (ℝ^p) => r.1 + r.2) γ) ≤
      ∫⁻ ω, ‖Zv ω‖ₑ ∂(S.P n) := by
    have hpert := Q40b.q40b_smoothDist_perturb (P := (S.P n).prod γ)
      (A := fun q : S.Ω n × (ℝ^p) => Zv q.1 + q.2) (B := Prod.snd)
      ((hZvm.comp measurable_fst).add measurable_snd).aemeasurable measurable_snd.aemeasurable
    have hpert' : ENNReal.ofReal (smoothDist 2
        (((S.P n).prod γ).map (fun q : S.Ω n × (ℝ^p) => Zv q.1 + q.2))
        (((S.P n).prod γ).map (Prod.snd : S.Ω n × (ℝ^p) → ℝ^p))) ≤
        ∫⁻ q, ‖(Zv q.1 + q.2) - q.2‖ₑ ∂((S.P n).prod γ) := hpert
    rw [hsnd, ← hCm] at hpert'
    refine hpert'.trans (le_of_eq ?_)
    have e1 : ∫⁻ q : S.Ω n × (ℝ^p), ‖(Zv q.1 + q.2) - q.2‖ₑ ∂((S.P n).prod γ) =
        ∫⁻ q : S.Ω n × (ℝ^p), ‖Zv q.1‖ₑ ∂((S.P n).prod γ) := by
      refine lintegral_congr fun q => ?_
      simp
    rw [e1]
    have := lintegral_map (μ := (S.P n).prod γ) (f := fun ω => ‖Zv ω‖ₑ) (g := Prod.fst)
      hZvm.enorm measurable_fst
    rw [(measurePreserving_fst (μ := S.P n) (ν := γ)).map_eq] at this
    exact this.symm
  -- step 3: the initial part decays
  have hψmem : ∀ a, MemSobolev (j : ℝ) (fun x => propagator htr.dyn ρ 0 (t a) (φ a) x -
        pair (withDensityReal ρβ) (propagator htr.dyn ρ 0 (t a) (φ a))) ∧
      ∀ F : NegSobolev d (j : ℝ), |NegSobolev.eval F (propagator htr.dyn ρ 0 (t a) (φ a))| ≤
        C₂ a * Real.exp (-c₂ a * t a) * ‖F‖ := by
    intro a
    have h := hinit a (t a) (ht a)
    have e : propagator (PDE.MFLinear.mfD H hβmem) (PDE.mfPath ρc) 0 (t a) (φ a) =
        propagator htr.dyn ρ 0 (t a) (φ a) :=
      Q40b.q40b_propagator_congr (D := htr.dyn) (ρ := PDE.mfPath ρc) (ρ' := ρ)
        (fun r hr => hρ r hr.1) 0 (φ a)
    rw [e] at h
    exact h
  have hsumm : ∀ a, Summable fun k : Lattice d =>
      ‖Torus.fcoef (propagator htr.dyn ρ 0 (t a) (φ a)) k‖ :=
    fun a => Q40b.q40b_summable_fcoef (j := j) hjd' (hψmem a).1
  have hj2 : (d : ℝ) < 2 * (j : ℝ) := by linarith
  have hinit0 : ∀ᵐ ω ∂(S.P n), S.X n 0 ω = S.X₀ n ω := (hsol 0 le_rfl n).sol.init
  have hmapX : (S.P n).map (S.X n 0) = (S.P n).map (S.X₀ n) := Measure.map_congr hinit0
  have hZbd : ∀ a, ∫⁻ ω, ENNReal.ofReal |zetaStat (S.P n) (S.X n) 0
      (propagator htr.dyn ρ 0 (t a) (φ a)) ω| ∂(S.P n) ≤
      ENNReal.ofReal (C₂ a * Real.exp (-c₂ a * t a)) * ENNReal.ofReal M := by
    intro a
    have hpt : ∀ᵐ ω ∂(S.P n), ENNReal.ofReal |zetaStat (S.P n) (S.X n) 0
        (propagator htr.dyn ρ 0 (t a) (φ a)) ω| ≤
        ENNReal.ofReal (C₂ a * Real.exp (-c₂ a * t a)) *
          ‖zetaE (j : ℝ) ((S.P n).map (S.X₀ n)) (S.X₀ n ω)‖ₑ := by
      filter_upwards [hinit0] with ω hω
      rw [Q40b.q40b_zetaStat_eval (by omega : 1 ≤ n + 2) (S.P n) (S.X n) hj2 (hψc a) (hsumm a) ω,
        hω, hmapX, ← ofReal_norm_eq_enorm,
        ← ENNReal.ofReal_mul (by have := hC₂ a; positivity)]
      exact ENNReal.ofReal_le_ofReal ((hψmem a).2 _)
    calc _ ≤ ∫⁻ ω, ENNReal.ofReal (C₂ a * Real.exp (-c₂ a * t a)) *
          ‖zetaE (j : ℝ) ((S.P n).map (S.X₀ n)) (S.X₀ n ω)‖ₑ ∂(S.P n) := lintegral_mono_ae hpt
      _ = ENNReal.ofReal (C₂ a * Real.exp (-c₂ a * t a)) *
          ∫⁻ ω, ‖zetaE (j : ℝ) ((S.P n).map (S.X₀ n)) (S.X₀ n ω)‖ₑ ∂(S.P n) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ _ := by gcongr; exact hzeta n
  have hZ3 : ∫⁻ ω, ‖Zv ω‖ₑ ∂(S.P n) ≤
      ∑ a, ENNReal.ofReal (C₂ a * Real.exp (-c₂ a * t a)) * ENNReal.ofReal M := by
    have hpt : ∀ ω, ‖Zv ω‖ₑ ≤ ∑ a, ENNReal.ofReal |zetaStat (S.P n) (S.X n) 0
        (propagator htr.dyn ρ 0 (t a) (φ a)) ω| := by
      intro ω
      rw [← ofReal_norm_eq_enorm]
      have hn : ‖Zv ω‖ ≤ ∑ a, |zetaStat (S.P n) (S.X n) 0
          (propagator htr.dyn ρ 0 (t a) (φ a)) ω| := PDE.MFLinear.norm_euclid_le_sum _
      calc ENNReal.ofReal ‖Zv ω‖ ≤ ENNReal.ofReal (∑ a, |zetaStat (S.P n) (S.X n) 0
            (propagator htr.dyn ρ 0 (t a) (φ a)) ω|) := ENNReal.ofReal_le_ofReal hn
        _ = _ := ENNReal.ofReal_sum_of_nonneg fun a _ => abs_nonneg _
    calc ∫⁻ ω, ‖Zv ω‖ₑ ∂(S.P n) ≤ ∫⁻ ω, ∑ a, ENNReal.ofReal |zetaStat (S.P n) (S.X n) 0
          (propagator htr.dyn ρ 0 (t a) (φ a)) ω| ∂(S.P n) := lintegral_mono hpt
      _ = ∑ a, ∫⁻ ω, ENNReal.ofReal |zetaStat (S.P n) (S.X n) 0
          (propagator htr.dyn ρ 0 (t a) (φ a)) ω| ∂(S.P n) :=
        lintegral_finset_sum _ fun a _ =>
          ENNReal.measurable_ofReal.comp (hζm _ (hψc a)).abs
      _ ≤ _ := Finset.sum_le_sum fun a _ => hZbd a
  -- step 4: the Gaussian covariances
  have hSigEq : noiseCovMatrix htr.dyn ρ β⁻¹ t φ =
      PDE.MFLinear.Mcov (PDE.MFLinear.mfD H hβmem) ρc τ φ u :=
    Q40b.q40b_noiseCov_eq htr hρ t ht φ
  obtain ⟨hSig, hu'⟩ := hcov τ hτ
  obtain ⟨hMpsd, hcovu⟩ := hu' u hu
  have hZ4 : smoothDist 2 γ (ProbabilityTheory.multivariateGaussian 0
      (PDE.stationaryLagCov d s β htr.dyn ρβ τ φ)) ≤
      (1 / 2) * ((p : ℝ) ^ 2 * Cv * Real.exp (-cv * u)) := by
    rw [hγeq, hSigEq]
    refine (PDE.MFLinear.smoothDist_two_gaussian_covariance _ _ hMpsd hSig).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine (PDE.MFLinear.traceNormMatrix_le_sum _).trans ?_
    calc ∑ a, ∑ b, |(PDE.MFLinear.Mcov (PDE.MFLinear.mfD H hβmem) ρc τ φ u -
          PDE.stationaryLagCov d s β (PDE.MFLinear.mfD H hβmem) ρβ τ φ) a b|
        ≤ ∑ _a : Fin p, ∑ _b : Fin p, Cv * Real.exp (-cv * u) :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => by
            rw [Matrix.sub_apply]; exact hcovu a b
      _ = (p : ℝ) ^ 2 * Cv * Real.exp (-cv * u) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  -- assembly
  set r := criterionRemainder htr.dyn ρ ρβ j (S.P n) (S.X n) with hr
  set y := ENNReal.ofReal (Real.sqrt (Bn / ((n + 2 : ℕ) : ℝ))) with hy
  have h1 : ∑ a, ∫⁻ ω, ENNReal.ofReal |integratedRemainder htr.dyn ρ (S.P n) (S.X n) (t a) (φ a) ω|
      ∂(S.P n) ≤ ENNReal.ofReal (∑ a, (L a + 1)) * r := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun a _ => by linarith [hL0 a]), Finset.sum_mul]
    exact Finset.sum_le_sum fun a _ =>
      Q40b.q40b_R_le hd htr (S.P n) (S.X n) hρβ hρS hρpos j (hφ a) (ht a)
  have h2 : ENNReal.ofReal ((1 / 2) * K * Real.sqrt (2 * (c₁ * Bn + Real.log 2) /
      ((n + 2 : ℕ) : ℝ))) ≤ ENNReal.ofReal K' * y := by
    rw [hy, ← ENNReal.ofReal_mul hK'0]
    refine ENNReal.ofReal_le_ofReal ?_
    have hlog : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    have hN0 : 0 < ((n + 2 : ℕ) : ℝ) := by positivity
    have hin : 2 * (c₁ * Bn + Real.log 2) / ((n + 2 : ℕ) : ℝ) ≤
        (2 * (c₁ + 1)) * (Bn / ((n + 2 : ℕ) : ℝ)) := by
      rw [← mul_div_assoc]
      refine div_le_div_of_nonneg_right ?_ hN0.le
      nlinarith
    have hsq := Real.sqrt_le_sqrt hin
    rw [Real.sqrt_mul (by positivity)] at hsq
    calc (1 / 2) * K * Real.sqrt (2 * (c₁ * Bn + Real.log 2) / ((n + 2 : ℕ) : ℝ))
        ≤ (1 / 2) * K * (Real.sqrt (2 * (c₁ + 1)) * Real.sqrt (Bn / ((n + 2 : ℕ) : ℝ))) := by
          gcongr
      _ = K' * Real.sqrt (Bn / ((n + 2 : ℕ) : ℝ)) := by rw [hK']; ring
  have hE : Real.exp (-cv * u) ≤ Real.exp (-c * u) :=
    Real.exp_le_exp.2 (by nlinarith)
  have hB2' : ENNReal.ofReal (smoothDist 2 γ (ProbabilityTheory.multivariateGaussian 0
      (PDE.stationaryLagCov d s β htr.dyn ρβ τ φ))) ≤
      ENNReal.ofReal ((1 / 2) * ((p : ℝ) ^ 2 * Cv) * Real.exp (-c * u)) := by
    refine ENNReal.ofReal_le_ofReal (hZ4.trans ?_)
    have : 0 ≤ (1 / 2) * ((p : ℝ) ^ 2 * Cv) := by positivity
    calc (1 / 2) * ((p : ℝ) ^ 2 * Cv * Real.exp (-cv * u)) =
        (1 / 2) * ((p : ℝ) ^ 2 * Cv) * Real.exp (-cv * u) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hE this
  have hB3 : ∑ a, ENNReal.ofReal (C₂ a * Real.exp (-c₂ a * t a)) * ENNReal.ofReal M ≤
      ENNReal.ofReal (S₂ * M₀ * Real.exp (-c * u)) := by
    have hterm : ∀ a, ENNReal.ofReal (C₂ a * Real.exp (-c₂ a * t a)) * ENNReal.ofReal M ≤
        ENNReal.ofReal (C₂ a * M₀ * Real.exp (-c * u)) := by
      intro a
      have hc2 := (hC₂ a).le
      rw [← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hexp : Real.exp (-c₂ a * t a) ≤ Real.exp (-c * u) :=
        Real.exp_le_exp.2 (by
          have h1 := mul_le_mul_of_nonneg_right (hc_c₂ a) hu
          have h2 := mul_nonneg (hc₂ a).le (hτ a)
          simp only [htdef]
          nlinarith)
      have hM' : M ≤ M₀ := le_max_left _ _
      calc C₂ a * Real.exp (-c₂ a * t a) * M ≤ C₂ a * Real.exp (-c₂ a * t a) * M₀ :=
            mul_le_mul_of_nonneg_left hM' (by have := Real.exp_pos (-c₂ a * t a); positivity)
        _ ≤ C₂ a * Real.exp (-c * u) * M₀ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hc2) hM₀0
        _ = _ := by ring
    refine (Finset.sum_le_sum fun a _ => hterm a).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => by
      have := (hC₂ a).le; positivity)]
    congr 1
    rw [hS₂, Finset.sum_mul, Finset.sum_mul]
  have hC1 : ENNReal.ofReal (∑ a, (L a + 1)) ≤ ENNReal.ofReal (∑ a, (L a + 1) + K' + Q + 1) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  have hC2 : ENNReal.ofReal K' ≤ ENNReal.ofReal (∑ a, (L a + 1) + K' + Q + 1) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  have hC3 : ENNReal.ofReal Q ≤ ENNReal.ofReal (∑ a, (L a + 1) + K' + Q + 1) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  set Nst : Measure (ℝ^p) := ProbabilityTheory.multivariateGaussian 0
    (PDE.stationaryLagCov d s β htr.dyn ρβ τ φ) with hNst
  -- triangle inequalities
  have htri1 := smoothDist_triangle 2
    (law (S.P n) fun ω => (WithLp.toLp 2 fun a => zetaStat (S.P n) (S.X n) (t a) (φ a) ω : ℝ^p))
    ((((S.P n).map Zv).prod γ).map fun r : (ℝ^p) × (ℝ^p) => r.1 + r.2) Nst
  have htri2 := smoothDist_triangle 2
    ((((S.P n).map Zv).prod γ).map fun r : (ℝ^p) × (ℝ^p) => r.1 + r.2) γ Nst
  set d1 := smoothDist 2
    (law (S.P n) fun ω => (WithLp.toLp 2 fun a => zetaStat (S.P n) (S.X n) (t a) (φ a) ω : ℝ^p))
    ((((S.P n).map Zv).prod γ).map fun r : (ℝ^p) × (ℝ^p) => r.1 + r.2) with hd1
  set d2 := smoothDist 2 ((((S.P n).map Zv).prod γ).map fun r : (ℝ^p) × (ℝ^p) => r.1 + r.2) γ
    with hd2
  set d3 := smoothDist 2 γ Nst with hd3
  have hd1n : 0 ≤ d1 := smoothDist_nonneg _ _ _
  have hd2n : 0 ≤ d2 := smoothDist_nonneg _ _ _
  have hd3n : 0 ≤ d3 := smoothDist_nonneg _ _ _
  have hfin : ENNReal.ofReal (smoothDist 2
      (law (S.P n) fun ω => (WithLp.toLp 2 fun a => zetaStat (S.P n) (S.X n) (t a) (φ a) ω : ℝ^p))
      Nst) ≤ ENNReal.ofReal d1 + (ENNReal.ofReal d2 + ENNReal.ofReal d3) := by
    rw [← ENNReal.ofReal_add hd2n hd3n, ← ENNReal.ofReal_add hd1n (add_nonneg hd2n hd3n)]
    refine ENNReal.ofReal_le_ofReal (htri1.trans ?_)
    linarith
  refine hfin.trans ?_
  have hd1b : ENNReal.ofReal d1 ≤ ENNReal.ofReal (∑ a, (L a + 1)) * r + ENNReal.ofReal K' * y :=
    hM.trans (add_le_add h1 h2)
  have hd2b : ENNReal.ofReal d2 ≤ ENNReal.ofReal (S₂ * M₀ * Real.exp (-c * u)) :=
    hZ2.trans (hZ3.trans hB3)
  have hQe : ENNReal.ofReal (S₂ * M₀ * Real.exp (-c * u)) +
      ENNReal.ofReal ((1 / 2) * ((p : ℝ) ^ 2 * Cv) * Real.exp (-c * u)) ≤
      ENNReal.ofReal (∑ a, (L a + 1) + K' + Q + 1) * ENNReal.ofReal (Real.exp (-c * u)) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul (by linarith)]
    refine ENNReal.ofReal_le_ofReal ?_
    have he := (Real.exp_pos (-c * u)).le
    have : S₂ * M₀ * Real.exp (-c * u) + (1 / 2) * ((p : ℝ) ^ 2 * Cv) * Real.exp (-c * u) =
        Q * Real.exp (-c * u) := by rw [hQ]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (by linarith) he
  calc ENNReal.ofReal d1 + (ENNReal.ofReal d2 + ENNReal.ofReal d3)
      ≤ (ENNReal.ofReal (∑ a, (L a + 1)) * r + ENNReal.ofReal K' * y) +
        (ENNReal.ofReal (S₂ * M₀ * Real.exp (-c * u)) +
          ENNReal.ofReal ((1 / 2) * ((p : ℝ) ^ 2 * Cv) * Real.exp (-c * u))) :=
        add_le_add hd1b (add_le_add hd2b hB2')
    _ ≤ (ENNReal.ofReal (∑ a, (L a + 1) + K' + Q + 1) * r +
          ENNReal.ofReal (∑ a, (L a + 1) + K' + Q + 1) * y) +
        ENNReal.ofReal (∑ a, (L a + 1) + K' + Q + 1) * ENNReal.ofReal (Real.exp (-c * u)) :=
        add_le_add (add_le_add (by gcongr) (by gcongr)) hQe
    _ = _ := by rw [mul_add, mul_add]

/-- The relocated proof has exactly the statement of `HRS.criterion_stationary`. -/
example := (@criterion_stationary_proof : type_of% @HRS.criterion_stationary)

end HRS

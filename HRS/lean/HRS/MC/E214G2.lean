import HRS.MC.L2C6cAux2
import HRS.MC.L2C0
import HRS.MC.E214FDecay
import HRS.Equilibrium.FieldSingAux

/-!
# E214G2: Gaussianity of the coordinates of `η - ηs` and of their increments (for ANY coupled pair)

For a coupled pair (centred Gaussian independent initial fields, two linear fluctuation solutions, `IsSameNoise`)
and smooth `φ`, every real combination `c₁ (η^{t₁}(φ) - ηs^{t₁}(φ)) + c₂ (η^{t₂}(φ) - ηs^{t₂}(φ))` is a centred
real Gaussian: it is the sum of three independent centred Gaussians, `A = (c₁ Y₀(ψ₁) + c₂ Y₀(ψ₂))`,
`B = -(c₁ Ys₀(ψ₁') + c₂ Ys₀(ψ₂'))` and `C =` a linear functional of the joint noise vector of `IsSameNoise`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open HRS HRS.Sec7
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MC.E214G

variable {d : ℕ}

/-- The conclusion of `HRS.MC.E214D.exists_coupled_pair` as a predicate (copy of `E214F.IsCoupledPair`). -/
def IsCoupledPair (R : Regime d) (r : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (Y₀ Ys₀ : Ω → NegSobolev d r) (η ηs : ℝ → Ω → NegSobolev d r) : Prop :=
  IsCenteredGaussianWithCov r (P.map Y₀)
      (susceptibilityCov (periodicRiesz d R.D.s) (withDensityReal R.ρ₀) R.β₀) ∧
    IsCenteredGaussianWithCov r (P.map Ys₀)
      (susceptibilityCov (periodicRiesz d R.D.s) (withDensityReal R.ρβ) R.β) ∧
    IndepFun Y₀ Ys₀ P ∧
    (∀ T : ℝ, IsLinearFluctuationSolution P R.D R.ρ r R.D.invβ T Y₀ η) ∧
    (∀ T : ℝ, IsLinearFluctuationSolution P R.D (fun _ => R.ρβ) r R.D.invβ T Ys₀ ηs) ∧
    IsSameNoise R.D R.ρ (fun _ => R.ρβ) r P Y₀ Ys₀ η ηs

/-- A real combination of two values of `η(φ) - ηs(φ)` is a centred Gaussian. -/
theorem combo_gaussian {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : DynData d) (ρ ρ' : ℝ → Torus d → ℝ) (m : ℝ)
    (Cov Cov' : (Torus d → ℝ) → (Torus d → ℝ) → ℝ)
    (Y₀ Ys₀ : Ω → NegSobolev d m) (Y Ys : ℝ → Ω → NegSobolev d m)
    (hY : IsCenteredGaussianWithCov m (P.map Y₀) Cov)
    (hYs : IsCenteredGaussianWithCov m (P.map Ys₀) Cov')
    (hind : IndepFun Y₀ Ys₀ P)
    (hS : ∀ T : ℝ, IsLinearFluctuationSolution P D ρ m D.invβ T Y₀ Y)
    (hS' : ∀ T : ℝ, IsLinearFluctuationSolution P D ρ' m D.invβ T Ys₀ Ys)
    (hN : IsSameNoise D ρ ρ' m P Y₀ Ys₀ Y Ys)
    {t₁ t₂ : ℝ} (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ)
    (h1 : Torus.IsSmooth (propagator D ρ 0 t₁ φ)) (h2 : Torus.IsSmooth (propagator D ρ 0 t₂ φ))
    (h1' : Torus.IsSmooth (propagator D ρ' 0 t₁ φ)) (h2' : Torus.IsSmooth (propagator D ρ' 0 t₂ φ))
    (c₁ c₂ : ℝ) :
    HasGaussianLaw (fun ω => c₁ * (NegSobolev.eval (Y t₁ ω) φ - NegSobolev.eval (Ys t₁ ω) φ) +
      c₂ * (NegSobolev.eval (Y t₂ ω) φ - NegSobolev.eval (Ys t₂ ω) φ)) P ∧
    ∫ ω, (c₁ * (NegSobolev.eval (Y t₁ ω) φ - NegSobolev.eval (Ys t₁ ω) φ) +
      c₂ * (NegSobolev.eval (Y t₂ ω) φ - NegSobolev.eval (Ys t₂ ω) φ)) ∂P = 0 := by
  have hY₀ : AEMeasurable Y₀ P := by
    refine (((hS 0).meas 0).aemeasurable).congr ?_
    filter_upwards [(hS 0).init] with ω h using h
  have hYs₀ : AEMeasurable Ys₀ P := by
    refine (((hS' 0).meas 0).aemeasurable).congr ?_
    filter_upwards [(hS' 0).init] with ω h using h
  have hGY : HasGaussianLaw Y₀ P := ⟨hY₀, hY.1.1⟩
  have hGYs : HasGaussianLaw Ys₀ P := ⟨hYs₀, hYs.1.1⟩
  -- the continuous linear functionals
  obtain ⟨L1, hL1⟩ := HRS.MC.L2C6Aux.l2c6_eval_clm m h1
  obtain ⟨L2, hL2⟩ := HRS.MC.L2C6Aux.l2c6_eval_clm m h2
  obtain ⟨L1', hL1'⟩ := HRS.MC.L2C6Aux.l2c6_eval_clm m h1'
  obtain ⟨L2', hL2'⟩ := HRS.MC.L2C6Aux.l2c6_eval_clm m h2'
  set LA : StrongDual ℝ (NegSobolev d m) := c₁ • L1 + c₂ • L2 with hLA
  set LB : StrongDual ℝ (NegSobolev d m) := -(c₁ • L1' + c₂ • L2') with hLB
  set A : Ω → ℝ := fun ω => LA (Y₀ ω) with hA
  set B : Ω → ℝ := fun ω => LB (Ys₀ ω) with hB
  have hAG : HasGaussianLaw A P := hGY.map_fun LA
  have hBG : HasGaussianLaw B P := hGYs.map_fun LB
  have hAB : IndepFun A B P :=
    hind.comp LA.continuous.measurable LB.continuous.measurable
  -- the noise vector
  have hsm1 : ∀ a : Fin 2, Torus.IsSmooth (propagator D ρ 0 (![t₁, t₂] a) φ) := by
    intro a; fin_cases a <;> simpa
  have hsm2 : ∀ a : Fin 2, Torus.IsSmooth (propagator D ρ' 0 (![t₁, t₂] a) φ) := by
    intro a; fin_cases a <;> simpa
  obtain ⟨hGind, hlaw⟩ := hN 2 2 ![t₁, t₂] (fun _ => φ) ![t₁, t₂] (fun _ => φ)
    (by intro a; fin_cases a <;> simpa) (by intro a; fin_cases a <;> simpa) (fun _ => hφ) (fun _ => hφ)
  set G : Ω → EuclideanSpace ℝ (Fin 2 ⊕ Fin 2) := fun ω => WithLp.toLp 2 (Sum.elim
      (fun a : Fin 2 => noisePart D ρ Y₀ Y (![t₁, t₂] a) φ ω)
      (fun b : Fin 2 => noisePart D ρ' Ys₀ Ys (![t₁, t₂] b) φ ω)) with hG
  have hcontφ := HRS.MC.L2C6Aux.l2c6_eval_continuous m hφ
  have hGm : AEMeasurable G P := by
    refine (PiLp.continuous_toLp 2 _).measurable.comp_aemeasurable
      (aemeasurable_pi_iff.2 fun i => ?_)
    rcases i with i | i
    · exact ((hcontφ.measurable.comp ((hS 0).meas (![t₁, t₂] i))).aemeasurable).sub
        (((HRS.MC.L2C6Aux.l2c6_eval_continuous m (hsm1 i)).measurable.comp_aemeasurable hY₀))
    · exact ((hcontφ.measurable.comp ((hS' 0).meas (![t₁, t₂] i))).aemeasurable).sub
        (((HRS.MC.L2C6Aux.l2c6_eval_continuous m (hsm2 i)).measurable.comp_aemeasurable hYs₀))
  set S : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ := Matrix.of fun i j => match i, j with
      | Sum.inl a, Sum.inl b => crossNoiseCov D D.invβ ρ ρ (![t₁, t₂] a) (![t₁, t₂] b) φ φ
      | Sum.inl a, Sum.inr b => crossNoiseCov D D.invβ ρ ρ' (![t₁, t₂] a) (![t₁, t₂] b) φ φ
      | Sum.inr a, Sum.inl b => crossNoiseCov D D.invβ ρ' ρ (![t₁, t₂] a) (![t₁, t₂] b) φ φ
      | Sum.inr a, Sum.inr b => crossNoiseCov D D.invβ ρ' ρ' (![t₁, t₂] a) (![t₁, t₂] b) φ φ with hSdef
  have hlaw' : P.map G = multivariateGaussian 0 S := by
    convert hlaw using 2
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> rfl
  have hGG : HasGaussianLaw G P := ⟨hGm, by rw [hlaw']; infer_instance⟩
  set LC : StrongDual ℝ (EuclideanSpace ℝ (Fin 2 ⊕ Fin 2)) :=
    c₁ • (EuclideanSpace.proj (Sum.inl 0) - EuclideanSpace.proj (Sum.inr 0)) +
      c₂ • (EuclideanSpace.proj (Sum.inl 1) - EuclideanSpace.proj (Sum.inr 1)) with hLC
  set C : Ω → ℝ := fun ω => LC (G ω) with hC
  have hCG : HasGaussianLaw C P := hGG.map_fun LC
  have hABC : IndepFun (fun ω => A ω + B ω) C P := by
    have := hGind.comp (φ := fun z : NegSobolev d m × NegSobolev d m => LA z.1 + LB z.2) (ψ := LC)
      ((LA.continuous.comp continuous_fst).add (LB.continuous.comp continuous_snd)).measurable
      LC.continuous.measurable
    exact this
  have hABG : HasGaussianLaw (fun ω => A ω + B ω) P := iIndepFun.hasGaussianLaw_fun_add hAG hBG hAB
  have hWG := iIndepFun.hasGaussianLaw_fun_add hABG hCG hABC
  have hW : ∀ ω, c₁ * (NegSobolev.eval (Y t₁ ω) φ - NegSobolev.eval (Ys t₁ ω) φ) +
      c₂ * (NegSobolev.eval (Y t₂ ω) φ - NegSobolev.eval (Ys t₂ ω) φ) = (A ω + B ω) + C ω := by
    intro ω
    simp only [hA, hB, hC, hLA, hLB, hLC, hG, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.neg_apply, ContinuousLinearMap.sub_apply, EuclideanSpace.coe_proj, hL1, hL2, hL1', hL2',
      noisePart, smul_eq_mul]
    simp
    ring
  have hfun : (fun ω => c₁ * (NegSobolev.eval (Y t₁ ω) φ - NegSobolev.eval (Ys t₁ ω) φ) +
      c₂ * (NegSobolev.eval (Y t₂ ω) φ - NegSobolev.eval (Ys t₂ ω) φ)) = fun ω => (A ω + B ω) + C ω :=
    funext hW
  rw [hfun]
  refine ⟨hWG, ?_⟩
  -- means
  have hmA : ∫ ω, A ω ∂P = 0 := by
    have h := integral_map (μ := P) hY₀ (f := fun z => LA z) LA.continuous.aestronglyMeasurable
    rw [← h]; exact hY.1.2 LA
  have hmB : ∫ ω, B ω ∂P = 0 := by
    have h := integral_map (μ := P) hYs₀ (f := fun z => LB z) LB.continuous.aestronglyMeasurable
    rw [← h]; exact hYs.1.2 LB
  have hmC : ∫ ω, C ω ∂P = 0 := by
    have hC' : ∫ ω, C ω ∂P = ∫ v, LC v ∂(P.map G) := by
      rw [integral_map hGm LC.continuous.aestronglyMeasurable]
    rw [hC']
    rw [hlaw']
    have h := ContinuousLinearMap.integral_comp_comm LC
      (IsGaussian.integrable_id (μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2 ⊕ Fin 2)) S))
    have h' : ∫ v, LC v ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2 ⊕ Fin 2)) S) =
        LC (∫ v, v ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2 ⊕ Fin 2)) S)) := h
    rw [h', integral_id_multivariateGaussian, map_zero]
  have i1 : Integrable A P := hAG.integrable
  have i2 : Integrable B P := hBG.integrable
  have i3 : Integrable C P := hCG.integrable
  have e1 : ∫ ω, (A ω + B ω + C ω) ∂P = ∫ ω, (A ω + B ω) ∂P + ∫ ω, C ω ∂P :=
    integral_add (i1.add i2) i3
  have e2 : ∫ ω, (A ω + B ω) ∂P = ∫ ω, A ω ∂P + ∫ ω, B ω ∂P := integral_add i1 i2
  rw [e1, e2, hmA, hmB, hmC]
  norm_num

theorem coord_eq_eval {r : ℝ} (F : NegSobolev d r) (k : NonzeroLattice d) :
    NegSobolev.coord F k = Lattice.jp k.1 ^ (-r) * NegSobolev.eval F (Torus.realMode k) := by
  rw [HRS.MC.E214F.eval_realMode]
  have hj := Torus.jp_pos k.1
  unfold NegSobolev.fourierCoeff
  rw [← mul_assoc, ← Real.rpow_add hj]; simp

/-- **(G)**: for a coupled pair, the coordinates of `η^t - ηs^t` and of their increments are centred real
Gaussians. -/
theorem pair_gaussian_proof (R : Regime d) (r : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y₀ Ys₀ : Ω → NegSobolev d r) (η ηs : ℝ → Ω → NegSobolev d r)
    (h : IsCoupledPair R r P Y₀ Ys₀ η ηs) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (k : NonzeroLattice d) :
    HasGaussianLaw (fun ω => NegSobolev.coord (η t ω - ηs t ω) k) P ∧
    ∫ ω, NegSobolev.coord (η t ω - ηs t ω) k ∂P = 0 ∧
    HasGaussianLaw (fun ω => NegSobolev.coord (η t ω - ηs t ω) k - NegSobolev.coord (η s ω - ηs s ω) k) P ∧
    ∫ ω, (NegSobolev.coord (η t ω - ηs t ω) k - NegSobolev.coord (η s ω - ηs s ω) k) ∂P = 0 := by
  obtain ⟨hY, hYs, hind, hS, hS', hN⟩ := h
  have hφ : Torus.IsSmooth (Torus.realMode k) := HRS.FieldSingAux.isSmooth_realMode k
  obtain ⟨p1, p1'⟩ := HRS.MC.L2C0.l2c0_proof R (Torus.realMode k) hφ 0 t le_rfl ht
  obtain ⟨p2, p2'⟩ := HRS.MC.L2C0.l2c0_proof R (Torus.realMode k) hφ 0 s le_rfl hs
  set c := Lattice.jp k.1 ^ (-r) with hc
  have e1 : ∀ ω, NegSobolev.coord (η t ω - ηs t ω) k = c * (NegSobolev.eval (η t ω) (Torus.realMode k) -
      NegSobolev.eval (ηs t ω) (Torus.realMode k)) + 0 * (NegSobolev.eval (η s ω) (Torus.realMode k) -
      NegSobolev.eval (ηs s ω) (Torus.realMode k)) := fun ω => by
    rw [coord_eq_eval, HRS.MC.E214F.eval_realMode_sub]; ring
  have e2 : ∀ ω, NegSobolev.coord (η t ω - ηs t ω) k - NegSobolev.coord (η s ω - ηs s ω) k =
      c * (NegSobolev.eval (η t ω) (Torus.realMode k) - NegSobolev.eval (ηs t ω) (Torus.realMode k)) +
      (-c) * (NegSobolev.eval (η s ω) (Torus.realMode k) - NegSobolev.eval (ηs s ω) (Torus.realMode k)) :=
    fun ω => by
    rw [coord_eq_eval, coord_eq_eval, HRS.MC.E214F.eval_realMode_sub, HRS.MC.E214F.eval_realMode_sub]; ring
  have g1 := combo_gaussian P R.D R.ρ (fun _ => R.ρβ) r _ _ Y₀ Ys₀ η ηs hY hYs hind hS hS' hN ht hs hφ
    p1 p2 p1' p2' c 0
  have g2 := combo_gaussian P R.D R.ρ (fun _ => R.ρβ) r _ _ Y₀ Ys₀ η ηs hY hYs hind hS hS' hN ht hs hφ
    p1 p2 p1' p2' c (-c)
  simp only [funext e1, funext e2]
  exact ⟨g1.1, g1.2, g2.1, g2.2⟩

end HRS.MC.E214G

end

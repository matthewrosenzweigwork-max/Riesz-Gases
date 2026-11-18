import HRS.Main.TorusTheorems
import HRS.Main.A1014Aux1

/-!
# Packet A1014, part 2: helpers for Corollary A.14 (`true_limit_stat`, `true_limit_stat_base`,
`true_limit_field`): probability of laws, `W₁` chain, the A.34 constants uniform in `m₀`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A1014

variable {d : ℕ}

section Prob

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]

/-- If `W_p(P, Q) < ⊤` for a probability measure `Q`, then `P` is a probability measure (a coupling
exists, its second marginal is `Q`). -/
theorem a1014_prob_of_wass (P Q : Measure B) [IsProbabilityMeasure Q] (p : ℝ)
    (h : wassersteinE p P Q ≠ ⊤) : IsProbabilityMeasure P := by
  have hne : Nonempty (couplings P Q) := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    apply h
    unfold wassersteinE
    exact iInf_of_empty _
  obtain ⟨⟨π, hπ1, hπ2⟩⟩ := hne
  have h2 : π Set.univ = 1 := by
    have := congrArg (fun μ : Measure B => μ Set.univ) hπ2
    simpa [Measure.map_apply measurable_snd MeasurableSet.univ] using this
  refine ⟨?_⟩
  have := congrArg (fun μ : Measure B => μ Set.univ) hπ1
  simpa [Measure.map_apply measurable_fst MeasurableSet.univ, h2] using this.symm

end Prob

section Chain

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B] [BorelSpace B]
  [SecondCountableTopology B] [CompleteSpace B]

theorem a1014_w1_chain (P Q R : Measure B) [IsProbabilityMeasure Q] [IsProbabilityMeasure R]
    (h1 : wassersteinE 1 P Q ≠ ⊤) :
    wassersteinE 1 P R ≤ wassersteinE 1 P Q + wassersteinE 1 Q R := by
  haveI := a1014_prob_of_wass P Q 1 h1
  exact wassersteinE_triangle 1 le_rfl P Q R

end Chain

section Surr

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem a1014_surr_prob {Ω : Type*} [MeasurableSpace Ω] (D : DynData d) (ρ : ℝ → Torus d → ℝ)
    (A q : ℝ) (ts : ι → ℝ) (φ : ι → Torus d → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (η : Ω → (Torus d → ℝ) → ℝ) (hη : ∀ ψ : Torus d → ℝ, Measurable fun ω => η ω ψ) :
    IsProbabilityMeasure (surrogateStatLaw D ρ A q ts φ P η) := by
  unfold surrogateStatLaw
  have hm : Measurable fun ω => (WithLp.toLp 2 fun a => A * η ω (propagator D ρ 0 (ts a) (φ a)) :
      EuclideanSpace ℝ ι) :=
    (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 fun a => measurable_const.mul (hη _))
  haveI : IsProbabilityMeasure (law P fun ω => (WithLp.toLp 2 fun a =>
      A * η ω (propagator D ρ 0 (ts a) (φ a)) : EuclideanSpace ℝ ι)) :=
    inferInstance
  infer_instance

end Surr

section Stat

/-- the `A.34 (i)` conclusion at `m = m_*`, for a given pair of constants. -/
def A1014Q34 (d : ℕ) (s : ℝ) (Rg : PDE.Regime) (ν₀ MB Λ T VB Cin : ℝ) (m₀ : ℕ) (C ΛT : ℝ) : Prop :=
  ∀ (S : MainData d), S.s = s → S.T = T →
    ∀ (L : LimitCoeffs d), CoeffConvergence S L Rg ν₀ MB Λ VB (PDE.mStar d + 2) (PDE.mStar d) →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (η : Ω → (Torus d → ℝ) → ℝ), FunctionalMoment P η m₀ Cin →
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ φ : Torus d → ℝ, MemSobolev ((PDE.mStar d + 2 : ℕ) : ℝ) φ →
      Continuous φ → ∀ N : ℕ, 1 ≤ N →
      wassersteinE 1
        (surrogateStatLaw (S.dyn N) (S.ρ N) (S.AN N) (S.qN N) (fun _ : Fin 1 => t) (fun _ => φ) P η)
        (surrogateStatLaw (L.dyn S) L.ρ L.A L.invβstar (fun _ : Fin 1 => t) (fun _ => φ) P η) ≤
      ENNReal.ofReal (C * Real.exp (ΛT * t) * sobolevNorm ((PDE.mStar d + 2 : ℕ) : ℝ) φ *
        (S.coeffDiscrepancy L (PDE.mStar d) N + Real.sqrt (S.coeffDiscrepancy L (PDE.mStar d) N)))

theorem a1014_delta_nonneg {S : MainData d} {L : LimitCoeffs d} {Rg : PDE.Regime} {ν₀ MB Λ VB : ℝ}
    {m : ℕ} (hcoef : CoeffConvergence S L Rg ν₀ MB Λ VB (m + 2) m) {N : ℕ} (hN : 1 ≤ N) :
    0 ≤ S.coeffDiscrepancy L m N :=
  (HRS.A34.a34_delta_facts S L m N Rg ν₀ MB Λ VB (hcoef.seq_adjoint N hN) hcoef.limit_adjoint).1

theorem a1014_Q34_exists (s : ℝ) (Rg : PDE.Regime) (ν₀ MB Λ T VB Cin : ℝ) (m₀ : ℕ)
    (hm₀ : m₀ ≤ PDE.mStar d) :
    ∃ C ΛT : ℝ, 0 < C ∧ 0 < ΛT ∧ A1014Q34 d s Rg ν₀ MB Λ T VB Cin m₀ C ΛT := by
  have hm1 : 1 ≤ PDE.mStar d := by unfold PDE.mStar; omega
  exact surrogate_to_limit_stat s Rg ν₀ MB Λ T VB Cin (PDE.mStar d) m₀ hm1 hm₀ (by omega)

theorem a1014_Q34_mono {s : ℝ} {Rg : PDE.Regime} {ν₀ MB Λ T VB Cin : ℝ} {m₀ : ℕ} {C ΛT C' ΛT' : ℝ}
    (h : A1014Q34 d s Rg ν₀ MB Λ T VB Cin m₀ C ΛT) (hC : 0 < C) (hCC : C ≤ C') (hΛ : ΛT ≤ ΛT') :
    A1014Q34 d s Rg ν₀ MB Λ T VB Cin m₀ C' ΛT' := by
  intro S hs hT L hcoef Ω _ P _ η hη t ht φ hφ hφc N hN
  refine (h S hs hT L hcoef P η hη t ht φ hφ hφc N hN).trans (ENNReal.ofReal_le_ofReal ?_)
  have hΔ := a1014_delta_nonneg hcoef hN
  have hδ : 0 ≤ S.coeffDiscrepancy L (PDE.mStar d) N +
      Real.sqrt (S.coeffDiscrepancy L (PDE.mStar d) N) := by positivity
  have hY : 0 ≤ sobolevNorm ((PDE.mStar d + 2 : ℕ) : ℝ) φ := Real.sqrt_nonneg _
  have he : Real.exp (ΛT * t) ≤ Real.exp (ΛT' * t) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hΛ ht.1)
  have h1 : C * Real.exp (ΛT * t) ≤ C' * Real.exp (ΛT' * t) :=
    mul_le_mul hCC he (Real.exp_pos _).le (by linarith)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hY) hδ

theorem a1014_functionalMoment {S : MainData d} {R : ∀ N, Realization d N} {m₀ : ℕ} {Cin : ℝ}
    {ε : ℕ → ℝ} {Ψ : ℕ → Set (Torus d → ℝ)} (h : InitialFluctuation S R m₀ Cin ε Ψ) {N : ℕ}
    (hN : 1 ≤ N) : FunctionalMoment (R N).P (R N).η m₀ Cin where
  η_meas := h.η_meas N
  linear := h.linear N
  second_moment := fun ψ hψ hc => le_trans le_add_self (h.I2 N hN ψ hψ hc)

theorem a1014_arith {C1 C2 L1 L2 t X Y r δ : ℝ} (hC1 : 0 < C1) (hC2 : 0 < C2) (ht : 0 ≤ t)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hX : 0 ≤ X) (hY : 0 ≤ Y) (hr : 0 ≤ r) (hδ : 0 ≤ δ) :
    statBound C1 L1 t X r + C2 * Real.exp (L2 * t) * Y * δ ≤
      (C1 + C2) * Real.exp ((L1 + L2) * t) * (X * (1 + X) * r + Y * δ) := by
  unfold statBound
  have hA : 0 ≤ X * (1 + X) * r := by positivity
  have hB : 0 ≤ Y * δ := by positivity
  have e1 : Real.exp (L1 * t) ≤ Real.exp ((L1 + L2) * t) :=
    Real.exp_le_exp.2 (by nlinarith)
  have e2 : Real.exp (L2 * t) ≤ Real.exp ((L1 + L2) * t) :=
    Real.exp_le_exp.2 (by nlinarith)
  have p1 : 0 < Real.exp (L1 * t) := Real.exp_pos _
  have p2 : 0 < Real.exp (L2 * t) := Real.exp_pos _
  have t1 : C1 * Real.exp (L1 * t) * (X * (1 + X) * r) ≤
      (C1 + C2) * Real.exp ((L1 + L2) * t) * (X * (1 + X) * r) :=
    mul_le_mul_of_nonneg_right (mul_le_mul (by linarith) e1 p1.le (by linarith)) hA
  have t2 : C2 * Real.exp (L2 * t) * (Y * δ) ≤
      (C1 + C2) * Real.exp ((L1 + L2) * t) * (Y * δ) :=
    mul_le_mul_of_nonneg_right (mul_le_mul (by linarith) e2 p2.le (by linarith)) hB
  calc C1 * Real.exp (L1 * t) * X * (1 + X) * r + C2 * Real.exp (L2 * t) * Y * δ
      = C1 * Real.exp (L1 * t) * (X * (1 + X) * r) + C2 * Real.exp (L2 * t) * (Y * δ) := by ring
    _ ≤ (C1 + C2) * Real.exp ((L1 + L2) * t) * (X * (1 + X) * r) +
        (C1 + C2) * Real.exp ((L1 + L2) * t) * (Y * δ) := add_le_add t1 t2
    _ = _ := by ring

end Stat


section LawEq

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `surrogateStatLaw` depends on `(P, η)` only through the law of `η`. -/
theorem a1014_surr_law_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] (D : DynData d)
    (ρ : ℝ → Torus d → ℝ) (A q : ℝ) (ts : ι → ℝ) (φ : ι → Torus d → ℝ) (P : Measure Ω)
    (η : Ω → (Torus d → ℝ) → ℝ) (P' : Measure Ω') (η' : Ω' → (Torus d → ℝ) → ℝ)
    (hη : ∀ ψ : Torus d → ℝ, Measurable fun ω => η ω ψ)
    (hη' : ∀ ψ : Torus d → ℝ, Measurable fun ω => η' ω ψ) (h : law P η = law P' η') :
    surrogateStatLaw D ρ A q ts φ P η = surrogateStatLaw D ρ A q ts φ P' η' := by
  set F : ((Torus d → ℝ) → ℝ) → EuclideanSpace ℝ ι := fun g =>
    WithLp.toLp 2 fun a => A * g (propagator D ρ 0 (ts a) (φ a)) with hF
  have hFm : Measurable F :=
    (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 fun a =>
      measurable_const.mul (measurable_pi_apply _))
  have e1 : (law P fun ω => (WithLp.toLp 2 fun a => A * η ω (propagator D ρ 0 (ts a) (φ a)) :
      EuclideanSpace ℝ ι)) = (law P η).map F := by
    unfold law
    rw [Measure.map_map hFm (measurable_pi_iff.2 hη)]
    rfl
  have e2 : (law P' fun ω => (WithLp.toLp 2 fun a => A * η' ω (propagator D ρ 0 (ts a) (φ a)) :
      EuclideanSpace ℝ ι)) = (law P' η').map F := by
    unfold law
    rw [Measure.map_map hFm (measurable_pi_iff.2 hη')]
    rfl
  unfold surrogateStatLaw
  rw [e1, e2, h]

end LawEq

end HRS.Main.A1014

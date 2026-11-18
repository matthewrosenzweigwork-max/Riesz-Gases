import HRS.Main.A9Aux22
import HRS.Main.A8PAux43
import HRS.Main.Det16C2

/-!
# Example A.16, lemma L6: `det16c_rem_modes`

At zero temperature the Itô martingale of the duality identity vanishes, and for a deterministic path the
remainder is bounded, mode by mode and for *all* `t ∈ [0,T]` simultaneously, by
`σ_N (1/2) C_q c_T K_k(t) · T · G`, where `G ≥ 0` bounds the corrected energy along the path.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.Det16

open HRS HRS.Main.A8P HRS.Main.A9

variable {d : ℕ}

/-- The Itô integral of the empirical noise integrand vanishes when `invβ = 0`. -/
theorem det16c_mart_zero {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} (hW : IsBrownianFiltration P ℱ W') (D : DynData d)
    (hβ : D.invβ = 0) (t : ℝ) (f : ℝ → Torus d → ℝ) (X : ℝ≥0 → Ω → Config d N) :
    ∀ᵐ ω ∂P, ∀ t' : ℝ, empiricalMartingale P ℱ W' D t f X t' ω = 0 := by
  have e : empiricalNoiseIntegrand D t f X = fun _ _ => (0 : Fin N × Fin d → ℝ) := by
    funext s ω k
    simp [empiricalNoiseIntegrand, hβ]
  filter_upwards [itoIntegral_const hW (0 : Fin N × Fin d → ℝ)] with ω hω t'
  unfold empiricalMartingale
  rw [e, hω t']
  simp

theorem det16c_AN_eq {S : MainData d} (hβ : ∀ N, S.invβ N = 0) (N : ℕ) : S.AN N = 1 := by
  unfold MainData.AN Ascale
  simp [hβ N]

/-- From "for each `t`, a.s." to "a.s., for all `t`" when the path is a.s. a fixed deterministic one. -/
theorem det16c_ae_forall_t {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {β : Type*} {T : ℝ} (X : ℝ≥0 → Ω → β) (x : ℝ≥0 → β)
    (hx : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, (u : ℝ) ≤ T → X u ω = x u) (Q : ℝ → Ω → Prop)
    (hQ : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ ω ω' : Ω, (∀ u : ℝ≥0, (u : ℝ) ≤ T → X u ω = X u ω') →
      Q t ω → Q t ω')
    (h : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P, Q t ω) :
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, Q t ω := by
  filter_upwards [hx] with ω hω t ht
  obtain ⟨ω₁, hQ1, hx1⟩ := ((h t ht).and hx).exists
  exact hQ t ht ω₁ ω (fun u hu => (hx1 u hu).trans (hω u hu).symm) hQ1

section Rem

variable {S : MainData d} {R : ∀ N, Realization d N} {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ}
  {𝔈 : ℕ → ℝ} {Ca Λ₁ C₀' Cq Cp cT : ℝ}

theorem det16c_rem_modes
    (hP : A8Pack d S.s Rg MB Λ VB ν₀ C₀ Ca Λ₁ C₀' Cq Cp cT)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (gammaIdx d + 2) C₀ Cc 𝔈)
    (hβ : ∀ N, S.invβ N = 0) {N : ℕ} (hN : 2 ≤ N) {G : ℝ} (hG : 0 ≤ G)
    (hE : ∀ᵐ ω ∂(R N).P, ∀ t ∈ Set.Icc (0 : ℝ) S.T,
      correctedEnergy (S.dyn N) C₀ Λ (S.ρ N) ((R N).X (Real.toNNReal t) ω) t ≤ G)
    (x : ℝ≥0 → Config d N)
    (hx : ∀ᵐ ω ∂(R N).P, ∀ u : ℝ≥0, (u : ℝ) ≤ S.T → (R N).X u ω = x u)
    (k : NonzeroLattice d) :
    ∀ᵐ ω ∂(R N).P, ∀ t ∈ Set.Icc (0 : ℝ) S.T,
      |NegSobolev.coord (a9Z S R N t ω - a9I S R N t ω) k| ≤
        S.sigma N * ((1 / 2) * (Cq * (cT * a9K d Λ₁ t k))) * (S.T * G) := by
  obtain ⟨hCa, hspec, hcom, hCq, hC, hCp0, hCp, hcT0, hcT⟩ := hP
  have hN1 : 1 ≤ N := by omega
  have hSm : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈 :=
    a9_standing_mono (by unfold gammaIdx; omega) hS
  have hSg : TorusStanding S R Rg ν₀ MB Λ VB (gammaIdx d) C₀ Cc 𝔈 :=
    a9_standing_mono (by omega) hS
  obtain ⟨ℱ, W', hF⟩ := hS.filtered N hN1
  have hσ := a8p_sigma_nonneg S N
  have hT0 := S.hT.le
  have hD0 : (S.dyn N).invβ = 0 := hβ N
  haveI := (R N).isProb
  refine det16c_ae_forall_t (R N).X x hx _ ?_ ?_
  · -- Q depends on ω only through the path
    intro t ht ω ω' hω h
    have e1 : (R N).X (Real.toNNReal t) ω = (R N).X (Real.toNNReal t) ω' :=
      hω _ (by rw [Real.coe_toNNReal _ ht.1]; exact ht.2)
    have e2 : (R N).X 0 ω = (R N).X 0 ω' := hω 0 (by simpa using hT0)
    have eZ : a9Z S R N t ω = a9Z S R N t ω' := by unfold a9Z; rw [e1]
    have eI : a9I S R N t ω = a9I S R N t ω' := by unfold a9I a9F0; rw [e2]
    rw [← eZ, ← eI]; exact h
  · intro t ht
    have hdual := a8p_dual_coord hspec hCa hSm hN ht (a9phi_cont k) (a9phi_mem _ k) hF
    have hmart := det16c_mart_zero hF.brownian (S.dyn N) hD0 t
      (fun r => propagator (S.dyn N) (S.ρ N) r t (a9phi d k)) (R N).X
    have hrem := a8p_rem_norm_bound hspec hCa hSm hN hF hcom hCq hC hcT0 hcT
      (q := 1) (fun _ => t) (fun _ => ht) (fun _ => a9phi d k) (fun _ => a9phi_cont k)
      (fun _ => a9phi_mem _ k)
    filter_upwards [hdual, hmart, hrem, hE] with ω h1 h2 h3 h4
    have hint : ∫ r in Set.Icc (0 : ℝ) S.T, a8pEn S R N C₀ Λ r ω ≤ S.T * G := by
      by_cases hi : IntegrableOn (fun r => a8pEn S R N C₀ Λ r ω) (Set.Icc (0 : ℝ) S.T)
      · calc ∫ r in Set.Icc (0 : ℝ) S.T, a8pEn S R N C₀ Λ r ω
            ≤ ∫ _r in Set.Icc (0 : ℝ) S.T, G := by
              refine setIntegral_mono_on hi (integrableOn_const (by simp)) measurableSet_Icc
                fun r hr => ?_
              unfold a8pEn
              exact max_le (h4 r hr) hG
          _ = S.T * G := by simp [hT0]
      · rw [integral_undef hi]; positivity
    have hK := a9K_nonneg (d := d) Λ₁ t k
    rw [a9_coord_sub, a9_Z_coord hSm hN1 ht ω k, a9_I_coord hSg hN1 ht ω k, ← mul_sub]
    rw [h2 _, add_zero] at h1
    have e : flucPair ((R N).X (Real.toNNReal t) ω) (S.ρ N t) (a9phi d k) -
        flucPair ((R N).X 0 ω) (S.ρ N 0) (propagator (S.dyn N) (S.ρ N) 0 t (a9phi d k)) =
        ∫ r in (0 : ℝ)..t, flucInteraction (S.dyn N)
          (propagator (S.dyn N) (S.ρ N) r t (a9phi d k)) ((R N).X (Real.toNNReal r) ω) (S.ρ N r) := by
      rw [h1]; ring
    rw [e]
    have hc0 : 0 ≤ (1 / 2) * (Cq * (cT * a9K d Λ₁ t k)) := by positivity
    calc |S.sigma N * ∫ r in (0 : ℝ)..t, flucInteraction (S.dyn N)
          (propagator (S.dyn N) (S.ρ N) r t (a9phi d k)) ((R N).X (Real.toNNReal r) ω) (S.ρ N r)|
        = ‖(a8pRem S R N (fun _ : Fin 1 => t) (fun _ => a9phi d k) ω) 0‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖a8pRem S R N (fun _ : Fin 1 => t) (fun _ => a9phi d k) ω‖ := PiLp.norm_apply_le _ _
      _ ≤ _ := h3
      _ ≤ S.sigma N * ((1 / 2) * (Cq * (cT * a9K d Λ₁ t k))) * (S.T * G) := by
          simp only [Fin.sum_univ_one]
          exact mul_le_mul_of_nonneg_left hint (by positivity)

end Rem

end HRS.Main.Det16

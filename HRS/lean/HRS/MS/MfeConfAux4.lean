import HRS.MS.MfeConfAux3

/-!
# S.B.1: the two frozen statements from the dissipation inequality (DISS)

`SuperDiss d s`, `SubDiss d s a` are (DISS) (`MfeDiss`) for all data of the frozen statements
`HRS.Whole.mfe_confined_rd_gradient_super`, `HRS.Whole.mfe_confined_rd_gradient_sub` (same hypotheses, same order, the conclusion
replaced by `MfeDiss`).  `sb1_super_of_diss`, `sb1_sub_of_diss` have exactly the frozen types after the extra hypothesis.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d : ℕ}

/-- (DISS) for the data of `mfe_confined_rd_gradient_super`. -/
def SuperDiss (d : ℕ) (s : ℝ) : Prop :=
  ∀ (D : Whole.WholeDyn d), D.s = s → ContDiff ℝ 3 D.V →
    (∃ B : ℝ, ∀ x, ‖iteratedFDeriv ℝ 2 D.V x‖ ≤ B) →
    (∃ cV CV : ℝ, 0 < cV ∧ ∀ x, cV * ‖x‖ ^ 2 - CV ≤ D.V x) →
    ∀ (N : ℕ), 2 ≤ N → ∀ (T Λ : ℝ) (r : ℕ), 0 ≤ T →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (ρ : ℝ → Euc d → ℝ) (X₀ : Ω → Whole.EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
      (X : ℝ≥0 → Ω → Whole.EucConfig d N),
      Whole.WholeMFEHyp P D N T Λ r ρ X₀ W X →
    ∀ K : ℝ → ℝ, IntegrableOn K (Set.Icc 0 T) →
      (∀ t ∈ Set.Icc 0 T, Whole.HasLipBoundW (Whole.mfeTransportW D (ρ t)) (K t)) →
      MfeDiss d D N T ρ P X₀ X

/-- (DISS) for the data of `mfe_confined_rd_gradient_sub`. -/
def SubDiss (d : ℕ) (s a : ℝ) : Prop :=
  ∀ (D : Whole.WholeDyn d), D.s = s →
    ∀ (Q : Matrix (Fin d) (Fin d) ℝ) (b : Euc d) (c q : ℝ), 0 < q → Q.IsSymm →
      (Q - q • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef →
      (∀ x, D.V x = (1 / 2) * inner ℝ x (Torus.matVec Q x) + inner ℝ b x + c) →
    ∀ (N : ℕ), 2 ≤ N → ∀ (T Λ : ℝ) (r : ℕ), 0 ≤ T →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (ρ : ℝ → Euc d → ℝ) (X₀ : Ω → Whole.EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
      (X : ℝ≥0 → Ω → Whole.EucConfig d N),
      Whole.WholeMFEHyp P D N T Λ r ρ X₀ W X →
    ∀ K : ℝ → ℝ, IntegrableOn K (Set.Icc 0 T) →
      (∀ t ∈ Set.Icc 0 T, Whole.HasFracTransportBound (a / 2) (2 * d / (a - 2))
        (Whole.mfeTransport0W D (ρ t))
        (K t - ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) Q‖)) →
      MfeDiss d D N T ρ P X₀ X

/-- Alternative (i) of S.B.1 from (DISS): the exact frozen statement `mfe_confined_rd_gradient_super` (type after the
hypothesis `SuperDiss d s`). -/
theorem sb1_super_of_diss (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (hsc : (d : ℝ) - 2 ≤ s) (hDiss : SuperDiss d s) :
    ∃ C₀ C : ℝ, 0 ≤ C₀ ∧ 0 < C ∧
      ∀ (D : Whole.WholeDyn d), D.s = s → ContDiff ℝ 3 D.V →
      (∃ B : ℝ, ∀ x, ‖iteratedFDeriv ℝ 2 D.V x‖ ≤ B) →
      (∃ cV CV : ℝ, 0 < cV ∧ ∀ x, cV * ‖x‖ ^ 2 - CV ≤ D.V x) →
      ∀ (N : ℕ), 2 ≤ N → ∀ (T Λ : ℝ) (r : ℕ), 0 ≤ T →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ρ : ℝ → Euc d → ℝ) (X₀ : Ω → Whole.EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
        (X : ℝ≥0 → Ω → Whole.EucConfig d N),
        Whole.WholeMFEHyp P D N T Λ r ρ X₀ W X →
      ∀ K : ℝ → ℝ, IntegrableOn K (Set.Icc 0 T) →
        (∀ t ∈ Set.Icc 0 T, Whole.HasLipBoundW (Whole.mfeTransportW D (ρ t)) (K t)) →
      ∀ t ∈ Set.Icc 0 T,
        (P.map (X (Real.toNNReal t))).AbsolutelyContinuous volume ∧
        Whole.MFEFiniteW d s (P.map (X (Real.toNNReal t))) (Whole.withDensityReal (ρ t)) ∧
        Whole.modulatedFreeEnergyW d s D.invβ (P.map (X (Real.toNNReal t)))
            (Whole.withDensityReal (ρ t)) + oNΛ d s C₀ Λ N ≤
          Real.exp (C * ∫ r in Set.Icc 0 T, K r) *
            (Whole.modulatedFreeEnergyW d s D.invβ (P.map X₀) (Whole.withDensityReal (ρ 0)) +
              oNΛ d s C₀ Λ N) := by
  obtain ⟨A₀, A, hA₀, hA, hcomm⟩ := sb1_comm_super_free hd hs0 hsd hsc
  obtain ⟨B₀, hB₀, hnn⟩ := HRS.MH.CoercLower.completionNonnegRd_exists hd hs0 hsd
  refine ⟨max A₀ B₀, A / 2, le_max_of_le_left hA₀, by positivity, ?_⟩
  intro D hDs hV3 hB hcoer N hN T Λ k hT Ω _ P _ ρ X₀ W X h K hKi hK
  subst hDs
  have hΛ1 : 1 ≤ Λ := h.Λ_ge
  have hΛ0 : 0 ≤ Λ := by linarith
  obtain ⟨Lm, hLm⟩ := sb1_regular_density_bounds (d := d) k Λ
  have hmax : max Λ 0 = Λ := max_eq_left hΛ0
  have hK0 : ∀ r ∈ Set.Icc (0 : ℝ) T, 0 ≤ K r := fun r hr => by
    obtain ⟨L, hL, hLK⟩ := hK r hr
    exact (L.coe_nonneg).trans hLK
  have key := sb1_core hd hN hT h (C₀ := max A₀ B₀) (A := A) hA.le (hnn _ (le_max_right _ _)) hKi hK0
    (fun r hr Z hZ => by
      have hρ := h.mf.density r hr
      have hb := hLm (ρ r) hρ (h.mf_reg r hr)
      have hρΛ : ∀ x, ρ r x ≤ Λ := fun x => by
        have := hb.1 x; rwa [hmax] at this
      have h1 := (hcomm Λ hΛ1 N hN (ρ r) hρ hρΛ (fun _ => hb.2.2.1) Z hZ _ (K r) (hK r hr)).2
      refine h1.trans ?_
      have hAK : 0 ≤ A * K r := mul_nonneg hA.le (hK0 r hr)
      have := oNΛ_mono_C₀ (d := d) (s := D.s) (le_max_left A₀ B₀) hΛ0 N
      exact mul_le_mul_of_nonneg_left (by linarith) hAK)
    (hDiss D rfl hV3 hB hcoer N hN T Λ k hT P ρ X₀ W X h K hKi hK)
  exact key

/-- `∇(½xᵀQx + b·x + c) = Qx + b` for symmetric `Q`. -/
theorem sb1_gradient_V {D : Whole.WholeDyn d} {Q : Matrix (Fin d) (Fin d) ℝ} (hQ : Q.IsSymm)
    {b : Euc d} {c : ℝ}
    (hV : ∀ x, D.V x = (1 / 2) * inner ℝ x (Torus.matVec Q x) + inner ℝ b x + c) (x : Euc d) :
    gradient D.V x = Torus.matVec Q x + b := by
  have hD : D.V = fun y => Whole.quadV Q b y + c := by
    funext y
    rw [hV y]
    rfl
  rw [hD]
  unfold gradient
  rw [fderiv_add_const]
  exact HRS.MS.Adj.ad_gradient_quadV hQ b x

/-- Alternative (ii) of S.B.1 from (DISS): the exact frozen statement `mfe_confined_rd_gradient_sub`. -/
theorem sb1_sub_of_diss {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (a : ℝ)
    (ha : (d : ℝ) < a ∧ a < (d : ℝ) + 2) (hDiss : SubDiss d s a) :
    ∃ C₀ C : ℝ, 0 ≤ C₀ ∧ 0 < C ∧
      ∀ (D : Whole.WholeDyn d), D.s = s →
      ∀ (Q : Matrix (Fin d) (Fin d) ℝ) (b : Euc d) (c q : ℝ), 0 < q → Q.IsSymm →
        (Q - q • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef →
        (∀ x, D.V x = (1 / 2) * inner ℝ x (Torus.matVec Q x) + inner ℝ b x + c) →
      ∀ (N : ℕ), 2 ≤ N → ∀ (T Λ : ℝ) (r : ℕ), 0 ≤ T →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ρ : ℝ → Euc d → ℝ) (X₀ : Ω → Whole.EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
        (X : ℝ≥0 → Ω → Whole.EucConfig d N),
        Whole.WholeMFEHyp P D N T Λ r ρ X₀ W X →
      ∀ K : ℝ → ℝ, IntegrableOn K (Set.Icc 0 T) →
        (∀ t ∈ Set.Icc 0 T, Whole.HasFracTransportBound (a / 2) (2 * d / (a - 2))
          (Whole.mfeTransport0W D (ρ t))
          (K t - ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) Q‖)) →
      ∀ t ∈ Set.Icc 0 T,
        (P.map (X (Real.toNNReal t))).AbsolutelyContinuous volume ∧
        Whole.MFEFiniteW d s (P.map (X (Real.toNNReal t))) (Whole.withDensityReal (ρ t)) ∧
        Whole.modulatedFreeEnergyW d s D.invβ (P.map (X (Real.toNNReal t)))
            (Whole.withDensityReal (ρ t)) + oNΛ d s C₀ Λ N ≤
          Real.exp (C * ∫ r in Set.Icc 0 T, K r) *
            (Whole.modulatedFreeEnergyW d s D.invβ (P.map X₀) (Whole.withDensityReal (ρ 0)) +
              oNΛ d s C₀ Λ N) := by
  have hd3 : 3 ≤ d := by
    have h2 : (2 : ℝ) < d := by linarith
    have : 2 < d := by exact_mod_cast h2
    omega
  have hd : 1 ≤ d := by omega
  have hsd' : s < d := by linarith
  obtain ⟨A₀, A, hA₀, hA, hcomm⟩ := sb1_comm_sub_free hs0 hsd a ha
  obtain ⟨B₀, hB₀, hnn⟩ := HRS.MH.CoercLower.completionNonnegRd_exists hd hs0 hsd'
  refine ⟨max A₀ B₀, A / 2, le_max_of_le_left hA₀, by positivity, ?_⟩
  intro D hDs Q b c q hq hQs hQp hV N hN T Λ k hT Ω _ P _ ρ X₀ W X h K hKi hK
  subst hDs
  have hΛ1 : 1 ≤ Λ := h.Λ_ge
  have hΛ0 : 0 ≤ Λ := by linarith
  obtain ⟨Lm, hLm⟩ := sb1_regular_density_bounds (d := d) k Λ
  have hmax : max Λ 0 = Λ := max_eq_left hΛ0
  have hQn : 0 ≤ ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) Q‖ := norm_nonneg _
  have hK0 : ∀ r ∈ Set.Icc (0 : ℝ) T, 0 ≤ K r := fun r hr => by
    obtain ⟨L, F, hF, -, -, hLK⟩ := hK r hr
    have := L.coe_nonneg
    linarith
  have hα : 1 < a / 2 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd3
    linarith [ha.1]
  have hTB : ∀ r ∈ Set.Icc (0 : ℝ) T,
      Whole.HasFracTransportBound (a / 2) (2 * d / (a - 2)) (Whole.mfeTransportW D (ρ r)) (K r) := by
    intro r hr
    have h1 := sb1_transport_add_affine hd hα (hK r hr) Q b
    have e : Whole.mfeTransportW D (ρ r) =
        fun x => Whole.mfeTransport0W D (ρ r) x + (Torus.matVec Q x + b) := by
      funext x
      unfold Whole.mfeTransportW
      rw [sb1_gradient_V hQs hV x]
    rw [e]
    simpa using h1
  have key := sb1_core hd hN hT h (C₀ := max A₀ B₀) (A := A) hA.le (hnn _ (le_max_right _ _)) hKi hK0
    (fun r hr Z hZ => by
      have hρ := h.mf.density r hr
      have hb := hLm (ρ r) hρ (h.mf_reg r hr)
      have hρΛ : ∀ x, ρ r x ≤ Λ := fun x => by
        have := hb.1 x; rwa [hmax] at this
      have h1 := (hcomm Λ hΛ1 N hN (ρ r) hρ hρΛ (fun _ => hb.2.2.1) Z hZ _ (K r) (hTB r hr)).2
      refine h1.trans ?_
      have hAK : 0 ≤ A * K r := mul_nonneg hA.le (hK0 r hr)
      have := oNΛ_mono_C₀ (d := d) (s := D.s) (le_max_left A₀ B₀) hΛ0 N
      exact mul_le_mul_of_nonneg_left (by linarith) hAK)
    (hDiss D rfl Q b c q hq hQs hQp hV N hN T Λ k hT P ρ X₀ W X h K hKi hK)
  exact key

end HRS.MS.MfeConf

end

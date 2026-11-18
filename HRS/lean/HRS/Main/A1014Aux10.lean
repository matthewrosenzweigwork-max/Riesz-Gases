import HRS.Main.A1014Aux9

/-!
# Packet A1014, part 10: the remainder term `‖Z - 𝕀 - ι M‖_p` (`p = 1, 2`) and the initial term
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A1014

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

open HRS HRS.A33 HRS.PDE HRS.Main HRS.Main.A8P HRS.Main.A9 HRS.GF HRS.Uniform

variable {d : ℕ}

section Q

variable {S : MainData d} {R : ∀ N, Realization d N} {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ}
  {𝔈 : ℕ → ℝ} {Ca Λ₁ C₀' Cq Cp cT : ℝ}

/-- `p = 1`: `E‖Z - 𝕀 - ι M_T‖ ≤ ∑_j bQ_j`. -/
theorem a1014_Q1 (hP : A8Pack d S.s Rg MB Λ VB ν₀ C₀ Ca Λ₁ C₀' Cq Cp cT)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (gammaIdx d) C₀ Cc 𝔈) {N : ℕ} (hN : 2 ≤ N)
    {ℱ : MeasureTheory.Filtration ℝ (R N).mΩ} {W' : ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ}
    (hF : IsFilteredSolution (R N).P ℱ W' (R N).W (R N).X)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T)
    {q : ℕ} {k : Fin q → NonzeroLattice d} (hk : Function.Injective k) :
    (∫⁻ ω, ENNReal.ofReal (‖a9Z S R N t ω - a9I S R N t ω - embedCLM
        (fun a => a9unit (gammaIdx d : ℝ) (k a))
        (vectorItoIntegral (R N).P ℱ W'
          (fun a => killAfter (a8pPhi (S.dyn N) (S.sigma N) ((fun _ : Fin q => t) a)
            (a8pF S N (fun _ : Fin q => t) (fun a => a9phi d (k a)) a) (R N).X)
            ((fun _ : Fin q => t) a)) S.T ω)‖ ^ (1 : ℝ)) ∂(R N).P) ^ (1 / (1 : ℝ)) ≤
      ENNReal.ofReal (∑' j, a9bQ S N Ca Cq cT Λ₁ t (𝔈 N) k j) := by
  classical
  obtain ⟨hCa, hspec, hcom, hCq, hC, hCp0, hCp, hcT0, hcT⟩ := hP
  have hS' := a9_standing_mStar hS
  have hN1 : 1 ≤ N := by omega
  have hT0 : 0 ≤ S.T := S.hT.le
  have h𝔈 : 0 ≤ 𝔈 N := (hS.energy.pos N hN1).le
  set ts : Fin q → ℝ := fun _ => t with hts_def
  set φ : Fin q → Torus d → ℝ := fun a => a9phi d (k a) with hφ_def
  have hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T := fun _ => ht
  have hφc : ∀ a, Continuous (φ a) := fun a => a9phi_cont _
  have hφm : ∀ a, MemSobolev (PDE.mStar d : ℝ) (φ a) := fun a => a9phi_mem _ _
  obtain ⟨hmart, -⟩ := a8p_vector_mart hspec hCa hS' hN1 hF ts hts φ hφc hφm
  set Mv := vectorItoIntegral (R N).P ℱ W'
    (fun a => killAfter (a8pPhi (S.dyn N) (S.sigma N) (ts a) (a8pF S N ts φ a) (R N).X) (ts a))
    with hMv
  set b : Fin q → NegSobolev d (gammaIdx d : ℝ) := fun a => a9unit (gammaIdx d : ℝ) (k a) with hb
  have hZm := a9_Z_meas hS hN1 ht hF
  have hXm0 := a9_I_meas hS hN1 ht hF
  have hXm : Measurable (a9I S R N t) := hXm0.mono (ℱ.le 0) le_rfl
  have hMt : AEMeasurable (fun ω => Mv S.T ω) (R N).P :=
    (hmart.sq_int S.T ⟨hT0, le_rfl⟩).aestronglyMeasurable.aemeasurable
  have hbQ0 : ∀ j, 0 ≤ a9bQ S N Ca Cq cT Λ₁ t (𝔈 N) k j :=
    fun j => a9bQ_nonneg hCa hCq hcT0 hN1 h𝔈 k j
  have hbQs : Summable (a9bQ S N Ca Cq cT Λ₁ t (𝔈 N) k) :=
    a9bQ_summable hCa hCq hcT0 hN1 h𝔈 k
  have h1 : ∫⁻ ω, ENNReal.ofReal ‖a9Z S R N t ω - a9I S R N t ω - embedCLM b (Mv S.T ω)‖ ∂(R N).P ≤
      ENNReal.ofReal (∑' j, a9bQ S N Ca Cq cT Λ₁ t (𝔈 N) k j) := by
    refine a9_lintegral_norm_le (R N).P
      (fun ω => a9Z S R N t ω - a9I S R N t ω - embedCLM b (Mv S.T ω)) ?_
      (a9bQ S N Ca Cq cT Λ₁ t (𝔈 N) k) hbQ0 hbQs ?_
    · exact (hZm.aemeasurable.sub hXm.aemeasurable).sub
        ((embedCLM b).continuous.measurable.comp_aemeasurable hMt)
    · intro j
      by_cases hj : j ∈ Set.range k
      · obtain ⟨a, rfl⟩ := hj
        have hdec := a8p_decomp hspec hCa hS' hN hF ts hts φ hφc hφm
        have hrem := a9_rem_moment hspec hCa hS' hN hF hcom hCq hC hcT0 hcT ts hts φ hφc hφm a
        have hbQ : a9bQ S N Ca Cq cT Λ₁ t (𝔈 N) k (k a) =
            S.sigma N * ((1 / 2) * (Cq * (cT * a8pK Λ₁ (ts a) (φ a)))) * (S.T * 𝔈 N) := by
          simp only [a9bQ, if_pos (Set.mem_range_self a)]
          rfl
        rw [hbQ]
        refine le_trans (lintegral_mono_ae ?_) hrem
        filter_upwards [hdec] with ω h
        have ha := congrArg (fun v : EuclideanSpace ℝ (Fin q) => v a) h
        simp only [fluctStat, a8pIemp, PiLp.add_apply] at ha
        have hc : NegSobolev.coord (a9Z S R N t ω - a9I S R N t ω - embedCLM b (Mv S.T ω)) (k a) =
            a8pRem S R N ts φ ω a := by
          rw [a9_coord_sub_embed_mem hk, a9_coord_sub, a9_Z_coord hS' hN1 ht,
            a9_I_coord hS hN1 ht]
          have e : S.sigma N * flucPair ((R N).X (Real.toNNReal t) ω) (S.ρ N t) (a9phi d (k a)) =
              S.sigma N * (pair (empirical ((R N).X (Real.toNNReal t) ω)) (a9phi d (k a)) -
                pair (withDensityReal (S.ρ N t)) (a9phi d (k a))) := rfl
          rw [e]
          have hmv : Mv S.T ω a = (vectorItoIntegral (R N).P ℱ W'
              (fun a => killAfter (a8pPhi (S.dyn N) (S.sigma N) (ts a) (a8pF S N ts φ a) (R N).X)
                (ts a)) S.T ω) a := rfl
          rw [hmv]
          have ha' : S.sigma N * (pair (empirical ((R N).X (Real.toNNReal t) ω)) (a9phi d (k a)) -
              pair (withDensityReal (S.ρ N t)) (a9phi d (k a))) =
              S.sigma N * flucPair ((R N).X 0 ω) (S.ρ N 0)
                (propagator (S.dyn N) (S.ρ N) 0 t (a9phi d (k a))) +
              (vectorItoIntegral (R N).P ℱ W'
                (fun a => killAfter (a8pPhi (S.dyn N) (S.sigma N) (ts a) (a8pF S N ts φ a) (R N).X)
                  (ts a)) S.T ω) a + a8pRem S R N ts φ ω a := ha
          linarith
        rw [hc]
      · have hZI := a9_ZI_moment hspec hCa hS hN hF hcom hCq hC hcT0 hcT ht j
        have hbQ : a9bQ S N Ca Cq cT Λ₁ t (𝔈 N) k j =
            Real.sqrt (S.T * (2 * (S.sigma N ^ 2 * S.invβ N / N) *
              (d * (Ca * a8pK Λ₁ t (a9phi d j))) ^ 2)) +
            S.sigma N * ((1 / 2) * (Cq * (cT * a8pK Λ₁ t (a9phi d j)))) * (S.T * 𝔈 N) := by
          simp only [a9bQ, if_neg hj]
          rfl
        rw [hbQ]
        refine le_trans (lintegral_mono_ae (Eventually.of_forall fun ω => ?_)) hZI
        rw [a9_coord_sub_embed_nmem _ _ j hj, a9_coord_sub]
  simpa [Real.rpow_one] using h1


/-- `p = 2`: `(E‖Z - 𝕀 - ι M_T‖²)^{1/2} ≤ ∑_j bQ_j` with `𝔈'` in place of `𝔈`. -/
theorem a1014_Q2 (hP : A8Pack d S.s Rg MB Λ VB ν₀ C₀ Ca Λ₁ C₀' Cq Cp cT)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (gammaIdx d) C₀ Cc 𝔈) {N : ℕ} (hN : 2 ≤ N)
    {ℱ : MeasureTheory.Filtration ℝ (R N).mΩ} {W' : ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ}
    (hF : IsFilteredSolution (R N).P ℱ W' (R N).W (R N).X)
    {𝔈' : ℝ} (h𝔈' : 0 ≤ 𝔈')
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) S.T, ∫⁻ ω, ENNReal.ofReal
        ((correctedEnergy (S.dyn N) C₀ Λ (S.ρ N) ((R N).X (Real.toNNReal t) ω) t) ^ 2) ∂(R N).P ≤
      ENNReal.ofReal (𝔈' ^ 2))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T)
    {q : ℕ} {k : Fin q → NonzeroLattice d} (hk : Function.Injective k) :
    (∫⁻ ω, ENNReal.ofReal (‖a9Z S R N t ω - a9I S R N t ω - embedCLM
        (fun a => a9unit (gammaIdx d : ℝ) (k a))
        (vectorItoIntegral (R N).P ℱ W'
          (fun a => killAfter (a8pPhi (S.dyn N) (S.sigma N) ((fun _ : Fin q => t) a)
            (a8pF S N (fun _ : Fin q => t) (fun a => a9phi d (k a)) a) (R N).X)
            ((fun _ : Fin q => t) a)) S.T ω)‖ ^ (2 : ℝ)) ∂(R N).P) ^ (1 / (2 : ℝ)) ≤
      ENNReal.ofReal (∑' j, a9bQ S N Ca Cq cT Λ₁ t 𝔈' k j) := by
  classical
  obtain ⟨hCa, hspec, hcom, hCq, hC, hCp0, hCp, hcT0, hcT⟩ := hP
  have hS' := a9_standing_mStar hS
  have hN1 : 1 ≤ N := by omega
  have hT0 : 0 ≤ S.T := S.hT.le
  set ts : Fin q → ℝ := fun _ => t with hts_def
  set φ : Fin q → Torus d → ℝ := fun a => a9phi d (k a) with hφ_def
  have hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T := fun _ => ht
  have hφc : ∀ a, Continuous (φ a) := fun a => a9phi_cont _
  have hφm : ∀ a, MemSobolev (PDE.mStar d : ℝ) (φ a) := fun a => a9phi_mem _ _
  obtain ⟨hmart, -⟩ := a8p_vector_mart hspec hCa hS' hN1 hF ts hts φ hφc hφm
  set Mv := vectorItoIntegral (R N).P ℱ W'
    (fun a => killAfter (a8pPhi (S.dyn N) (S.sigma N) (ts a) (a8pF S N ts φ a) (R N).X) (ts a))
    with hMv
  set b : Fin q → NegSobolev d (gammaIdx d : ℝ) := fun a => a9unit (gammaIdx d : ℝ) (k a) with hb'
  have hZm := a9_Z_meas hS hN1 ht hF
  have hXm0 := a9_I_meas hS hN1 ht hF
  have hXm : Measurable (a9I S R N t) := hXm0.mono (ℱ.le 0) le_rfl
  have hMt : AEMeasurable (fun ω => Mv S.T ω) (R N).P :=
    (hmart.sq_int S.T ⟨hT0, le_rfl⟩).aestronglyMeasurable.aemeasurable
  have hbQ0 : ∀ j, 0 ≤ a9bQ S N Ca Cq cT Λ₁ t 𝔈' k j :=
    fun j => a9bQ_nonneg hCa hCq hcT0 hN1 h𝔈' k j
  have hbQs : Summable (a9bQ S N Ca Cq cT Λ₁ t 𝔈' k) :=
    a9bQ_summable hCa hCq hcT0 hN1 h𝔈' k
  have hQm : AEMeasurable (fun ω => a9Z S R N t ω - a9I S R N t ω - embedCLM b (Mv S.T ω))
      (R N).P :=
    (hZm.aemeasurable.sub hXm.aemeasurable).sub
      ((embedCLM b).continuous.measurable.comp_aemeasurable hMt)
  refine a1014_lintegral_sq_norm_le (R N).P
    (fun ω => a9Z S R N t ω - a9I S R N t ω - embedCLM b (Mv S.T ω)) hQm
    (a9bQ S N Ca Cq cT Λ₁ t 𝔈' k) hbQ0 hbQs ?_
  intro j
  by_cases hj : j ∈ Set.range k
  · obtain ⟨a, rfl⟩ := hj
    have hdec := a8p_decomp hspec hCa hS' hN hF ts hts φ hφc hφm
    have hrem := a1014_rem_moment2 hspec hCa hS' hN hF hcom hCq hC hcT0 hcT ts hts φ hφc hφm a
      h𝔈' hb
    have hbQ : a9bQ S N Ca Cq cT Λ₁ t 𝔈' k (k a) =
        S.sigma N * ((1 / 2) * (Cq * (cT * a8pK Λ₁ (ts a) (φ a)))) * (S.T * 𝔈') := by
      simp only [a9bQ, if_pos (Set.mem_range_self a)]
      rfl
    rw [hbQ]
    refine le_trans (lintegral_mono_ae ?_) hrem
    filter_upwards [hdec] with ω h
    have ha := congrArg (fun v : EuclideanSpace ℝ (Fin q) => v a) h
    simp only [fluctStat, a8pIemp, PiLp.add_apply] at ha
    have hc : NegSobolev.coord (a9Z S R N t ω - a9I S R N t ω - embedCLM b (Mv S.T ω)) (k a) =
        a8pRem S R N ts φ ω a := by
      rw [a9_coord_sub_embed_mem hk, a9_coord_sub, a9_Z_coord hS' hN1 ht,
        a9_I_coord hS hN1 ht]
      have e : S.sigma N * flucPair ((R N).X (Real.toNNReal t) ω) (S.ρ N t) (a9phi d (k a)) =
          S.sigma N * (pair (empirical ((R N).X (Real.toNNReal t) ω)) (a9phi d (k a)) -
            pair (withDensityReal (S.ρ N t)) (a9phi d (k a))) := rfl
      rw [e]
      have hmv : Mv S.T ω a = (vectorItoIntegral (R N).P ℱ W'
          (fun a => killAfter (a8pPhi (S.dyn N) (S.sigma N) (ts a) (a8pF S N ts φ a) (R N).X)
            (ts a)) S.T ω) a := rfl
      rw [hmv]
      have ha' : S.sigma N * (pair (empirical ((R N).X (Real.toNNReal t) ω)) (a9phi d (k a)) -
          pair (withDensityReal (S.ρ N t)) (a9phi d (k a))) =
          S.sigma N * flucPair ((R N).X 0 ω) (S.ρ N 0)
            (propagator (S.dyn N) (S.ρ N) 0 t (a9phi d (k a))) +
          (vectorItoIntegral (R N).P ℱ W'
            (fun a => killAfter (a8pPhi (S.dyn N) (S.sigma N) (ts a) (a8pF S N ts φ a) (R N).X)
              (ts a)) S.T ω) a + a8pRem S R N ts φ ω a := ha
      linarith
    show ENNReal.ofReal (NegSobolev.coord (a9Z S R N t ω - a9I S R N t ω -
      embedCLM b (Mv S.T ω)) (k a) ^ 2) ≤ ENNReal.ofReal ((a8pRem S R N ts φ ω a) ^ 2)
    rw [hc]
  · have hZI := a1014_ZI_moment2 hspec hCa hS hN hF hcom hCq hC hcT0 hcT h𝔈' hb ht j
    have hbQ : a9bQ S N Ca Cq cT Λ₁ t 𝔈' k j =
        Real.sqrt (S.T * (2 * (S.sigma N ^ 2 * S.invβ N / N) *
          (d * (Ca * a8pK Λ₁ t (a9phi d j))) ^ 2)) +
        S.sigma N * ((1 / 2) * (Cq * (cT * a8pK Λ₁ t (a9phi d j)))) * (S.T * 𝔈') := by
      simp only [a9bQ, if_neg hj]
      rfl
    rw [hbQ]
    refine le_trans (lintegral_mono_ae (Eventually.of_forall fun ω => ?_)) hZI
    show ENNReal.ofReal (NegSobolev.coord (a9Z S R N t ω - a9I S R N t ω -
      embedCLM b (Mv S.T ω)) j ^ 2) ≤ _
    rw [a9_coord_sub_embed_nmem _ _ j hj, a9_coord_sub]

end Q

section Init

variable {S : MainData d} {R : ∀ N, Realization d N} {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ}
  {𝔈 : ℕ → ℝ}

/-- `p = 1` initial term: `E‖𝕀 - Ĩ‖ ≤ Ktr ε^f` in the `rpow` form. -/
theorem a1014_I_diff1 {Ktr : ℝ} (hKtr0 : 0 ≤ Ktr)
    (hKtr : ∀ (D : DynData d) (ρ : ℝ → Torus d → ℝ),
      AdjointData S.s (gammaIdx d) Rg MB Λ VB D ν₀ S.T ρ → ∀ t ∈ Set.Icc (0 : ℝ) S.T,
      ∀ F : NegSobolev d (gammaIdx d : ℝ), ‖transportField D ρ t (gammaIdx d : ℝ) F‖ ≤ ‖F‖ * Ktr)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (gammaIdx d) C₀ Cc 𝔈) {N : ℕ} (hN : 1 ≤ N)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T) {Cin : ℝ} {εf : ℕ → ℝ}
    {ηF : ∀ N, (R N).Ω → NegSobolev d (gammaIdx d : ℝ)} {νin : Measure (NegSobolev d (gammaIdx d : ℝ))}
    (hfield : InitialFluctuationField S R (gammaIdx d) Cin εf ηF νin) :
    (∫⁻ ω, ENNReal.ofReal (‖a9I S R N t ω - a9Itil S R N t ηF ω‖ ^ (1 : ℝ)) ∂(R N).P) ^
        (1 / (1 : ℝ)) ≤ ENNReal.ofReal (Ktr * εf N) := by
  have := a9_I_diff hKtr0 hKtr hS hN ht hfield
  simpa [Real.rpow_one] using this

/-- `p = 2` initial term: `(E‖𝕀 - Ĩ‖²)^{1/2} ≤ Ktr ε^{f,(2)}`. -/
theorem a1014_I_diff2 {Ktr : ℝ} (hKtr0 : 0 ≤ Ktr)
    (hKtr : ∀ (D : DynData d) (ρ : ℝ → Torus d → ℝ),
      AdjointData S.s (gammaIdx d) Rg MB Λ VB D ν₀ S.T ρ → ∀ t ∈ Set.Icc (0 : ℝ) S.T,
      ∀ F : NegSobolev d (gammaIdx d : ℝ), ‖transportField D ρ t (gammaIdx d : ℝ) F‖ ≤ ‖F‖ * Ktr)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (gammaIdx d) C₀ Cc 𝔈) {N : ℕ} (hN : 1 ≤ N)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T)
    {ηF : ∀ N, (R N).Ω → NegSobolev d (gammaIdx d : ℝ)} {εf2 : ℝ} (hε2 : 0 ≤ εf2)
    (hL2 : ∫⁻ ω, ‖S.κ N • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ)
        (empirical ((R N).X₀ ω)) S.μ0 - ηF N ω‖ₑ ^ 2 ∂(R N).P ≤ ENNReal.ofReal (εf2 ^ 2)) :
    (∫⁻ ω, ENNReal.ofReal (‖a9I S R N t ω - a9Itil S R N t ηF ω‖ ^ (2 : ℝ)) ∂(R N).P) ^
        (1 / (2 : ℝ)) ≤ ENNReal.ofReal (Ktr * εf2) := by
  have hS' := a9_standing_mStar hS
  have hA : AdjointData S.s (gammaIdx d) Rg MB Λ VB (S.dyn N) ν₀ S.T (S.ρ N) :=
    a9_adjointData a9_mStar_le_gamma hS hN
  have hd := S.hd
  obtain ⟨-, -, h0⟩ := a8p_flow_facts hS' hN
  have hAN := a8p_A_abs_le S N
  refine a1014_lp2 _ (mul_nonneg hKtr0 hε2) ?_
  calc ∫⁻ ω, ENNReal.ofReal (‖a9I S R N t ω - a9Itil S R N t ηF ω‖ ^ (2 : ℝ)) ∂(R N).P
      ≤ ∫⁻ ω, ENNReal.ofReal Ktr ^ 2 * ‖S.κ N • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ)
          (empirical ((R N).X₀ ω)) S.μ0 - ηF N ω‖ₑ ^ 2 ∂(R N).P := by
        refine lintegral_mono_ae ?_
        filter_upwards [h0] with ω hω
        have e : a9I S R N t ω - a9Itil S R N t ηF ω =
            S.AN N • transportField (S.dyn N) (S.ρ N) t (gammaIdx d : ℝ)
              (a9F0 S R N ω - ηF N ω) := by
          unfold a9I a9Itil
          rw [← smul_sub, a9_transport_sub hd Rg MB Λ VB ν₀ S.T (S.dyn N) (S.ρ N) hA ht]
        have e2 : a9F0 S R N ω = S.κ N • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ)
            (empirical ((R N).X₀ ω)) S.μ0 := by
          unfold a9F0; rw [hω]
        have hle : ‖a9I S R N t ω - a9Itil S R N t ηF ω‖ ≤
            Ktr * ‖S.κ N • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ)
              (empirical ((R N).X₀ ω)) S.μ0 - ηF N ω‖ := by
          rw [e, norm_smul, ← e2, Real.norm_eq_abs]
          have h1 := hKtr (S.dyn N) (S.ρ N) hA t ht (a9F0 S R N ω - ηF N ω)
          calc |S.AN N| * ‖transportField (S.dyn N) (S.ρ N) t (gammaIdx d : ℝ)
                  (a9F0 S R N ω - ηF N ω)‖
              ≤ 1 * (‖a9F0 S R N ω - ηF N ω‖ * Ktr) := mul_le_mul hAN h1 (norm_nonneg _) zero_le_one
            _ = Ktr * ‖a9F0 S R N ω - ηF N ω‖ := by ring
        rw [Real.rpow_two]
        calc ENNReal.ofReal (‖a9I S R N t ω - a9Itil S R N t ηF ω‖ ^ 2)
            ≤ ENNReal.ofReal ((Ktr * ‖S.κ N • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ)
              (empirical ((R N).X₀ ω)) S.μ0 - ηF N ω‖) ^ 2) :=
              ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) hle 2)
          _ = ENNReal.ofReal Ktr ^ 2 * ‖S.κ N • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ)
              (empirical ((R N).X₀ ω)) S.μ0 - ηF N ω‖ₑ ^ 2 := by
              rw [mul_pow, ENNReal.ofReal_mul (pow_nonneg hKtr0 2), ENNReal.ofReal_pow hKtr0,
                ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
    _ = ENNReal.ofReal Ktr ^ 2 * ∫⁻ ω, ‖S.κ N • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ)
          (empirical ((R N).X₀ ω)) S.μ0 - ηF N ω‖ₑ ^ 2 ∂(R N).P :=
        lintegral_const_mul' _ _ (by simp)
    _ ≤ ENNReal.ofReal Ktr ^ 2 * ENNReal.ofReal (εf2 ^ 2) := by gcongr
    _ = ENNReal.ofReal ((Ktr * εf2) ^ 2) := by
        rw [mul_pow, ENNReal.ofReal_mul (pow_nonneg hKtr0 2), ENNReal.ofReal_pow hKtr0]

end Init

end HRS.Main.A1014

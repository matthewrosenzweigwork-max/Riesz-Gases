import HRS.Main.A1014Aux7

/-!
# Packet A1014, part 8: the `L²` moments of the modes (remainder, `Z_j - 𝕀_j`, Gaussian coordinates,
initial term) used by the `W₂` clause
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A1014

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

open HRS HRS.A33 HRS.PDE HRS.Main HRS.Main.A8P HRS.Main.A9 HRS.GF HRS.Uniform

variable {d : ℕ}

theorem a1014_sq_of_rpow {X : ℝ≥0∞} {c : ℝ≥0∞} (h : X ^ (1 / 2 : ℝ) ≤ c) : X ≤ c ^ 2 := by
  have h2 := ENNReal.rpow_le_rpow h (show (0 : ℝ) ≤ 2 by norm_num)
  have e : (X ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = X := by
    rw [← ENNReal.rpow_mul]; norm_num
  rw [e] at h2
  simpa [ENNReal.rpow_two] using h2

section Rem2

variable {S : MainData d} {R : ∀ N, Realization d N} {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ}
  {𝔈 : ℕ → ℝ} {Ca Λ₁ : ℝ}

/-- Second moment of one coordinate of the remainder vector. -/
theorem a1014_rem_moment2 (hspec : A8AdjSpec d S.s Rg MB Λ VB ν₀ Ca Λ₁) (hCa : 0 ≤ Ca)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ} (hN : 2 ≤ N)
    {ℱ : Filtration ℝ (R N).mΩ} {W' : ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ}
    (hF : IsFilteredSolution (R N).P ℱ W' (R N).W (R N).X)
    {C₀' Cq cT : ℝ} (hcom : A8CommSpec d S.s C₀' Cq) (hCq : 0 ≤ Cq) (hC : C₀' ≤ C₀) (hcT0 : 0 ≤ cT)
    (hcT : ∀ (M : Matrix (Fin d) (Fin d) ℝ), PDE.MatBound MB M → ∀ ψ : Torus d → ℝ, Torus.IsCk 2 ψ →
      MemSobolev (PDE.mStar d : ℝ) ψ →
        HasTransportBound d S.s (gfb2_v M ψ) (cT * sobolevNorm (PDE.mStar d : ℝ) ψ))
    {q : ℕ} (ts : Fin q → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T) (φ : Fin q → Torus d → ℝ)
    (hφc : ∀ a, Continuous (φ a)) (hφ : ∀ a, MemSobolev (PDE.mStar d : ℝ) (φ a)) (a : Fin q)
    {𝔈' : ℝ} (h𝔈' : 0 ≤ 𝔈')
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) S.T, ∫⁻ ω, ENNReal.ofReal
        ((correctedEnergy (S.dyn N) C₀ Λ (S.ρ N) ((R N).X (Real.toNNReal t) ω) t) ^ 2) ∂(R N).P ≤
      ENNReal.ofReal (𝔈' ^ 2)) :
    ∫⁻ ω, ENNReal.ofReal ((a8pRem S R N ts φ ω a) ^ 2) ∂(R N).P ≤
      ENNReal.ofReal ((S.sigma N * ((1 / 2) * (Cq * (cT * a8pK Λ₁ (ts a) (φ a)))) *
        (S.T * 𝔈')) ^ 2) := by
  have hN1 : 1 ≤ N := by omega
  have hσ := a8p_sigma_nonneg S N
  have hK0 := a8pK_nonneg Λ₁ (ts a) (φ a)
  set cc : ℝ := S.sigma N * ((1 / 2) * (Cq * (cT * a8pK Λ₁ (ts a) (φ a)))) with hcc
  have hcc0 : 0 ≤ cc := by
    rw [hcc]; exact mul_nonneg hσ (mul_nonneg (by norm_num) (mul_nonneg hCq (mul_nonneg hcT0 hK0)))
  have h2 := a8p_energy_integral2 hS hN1 hF.progressive h𝔈' hb (C₀ := C₀) (Λ := Λ)
  have hrem := a8p_rem_ae hspec hCa hS hN hF hcom hCq hC hcT0 hcT (hts a) (hφc a) (hφ a)
  have hbd : ∀ᵐ ω ∂(R N).P, |a8pRem S R N ts φ ω a| ≤
      cc * ∫ r in Set.Icc (0 : ℝ) S.T, a8pEn S R N C₀ Λ r ω := by
    filter_upwards [hrem] with ω h
    have e : (a8pRem S R N ts φ ω) a = S.sigma N * ∫ r in (0 : ℝ)..(ts a),
        flucInteraction (S.dyn N) (propagator (S.dyn N) (S.ρ N) r (ts a) (φ a))
          ((R N).X (Real.toNNReal r) ω) (S.ρ N r) := rfl
    rw [e, abs_mul, abs_of_nonneg hσ, hcc, mul_assoc]
    exact mul_le_mul_of_nonneg_left h hσ
  have hnn : ∀ ω, 0 ≤ ∫ r in Set.Icc (0 : ℝ) S.T, a8pEn S R N C₀ Λ r ω := fun ω =>
    setIntegral_nonneg measurableSet_Icc fun r _ => a8pEn_nonneg S R N C₀ Λ r ω
  set Y : (R N).Ω → ℝ := fun ω => ∫ r in Set.Icc (0 : ℝ) S.T, a8pEn S R N C₀ Λ r ω with hY
  have hY2 : ∫⁻ ω, ENNReal.ofReal (Y ω) ^ 2 ∂(R N).P ≤ ENNReal.ofReal (S.T * 𝔈') ^ 2 :=
    a1014_sq_of_rpow h2
  calc ∫⁻ ω, ENNReal.ofReal ((a8pRem S R N ts φ ω a) ^ 2) ∂(R N).P
      ≤ ∫⁻ ω, ENNReal.ofReal cc ^ 2 * ENNReal.ofReal (Y ω) ^ 2 ∂(R N).P := by
        refine lintegral_mono_ae ?_
        filter_upwards [hbd] with ω h
        rw [← mul_pow, ← ENNReal.ofReal_mul hcc0, ← ENNReal.ofReal_pow (mul_nonneg hcc0 (hnn ω))]
        refine ENNReal.ofReal_le_ofReal ?_
        calc (a8pRem S R N ts φ ω a) ^ 2 = |a8pRem S R N ts φ ω a| ^ 2 := (sq_abs _).symm
          _ ≤ (cc * Y ω) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = ENNReal.ofReal cc ^ 2 * ∫⁻ ω, ENNReal.ofReal (Y ω) ^ 2 ∂(R N).P :=
        lintegral_const_mul' _ _ (by simp)
    _ ≤ ENNReal.ofReal cc ^ 2 * ENNReal.ofReal (S.T * 𝔈') ^ 2 := by gcongr
    _ = ENNReal.ofReal ((cc * (S.T * 𝔈')) ^ 2) := by
        rw [← mul_pow, ← ENNReal.ofReal_mul hcc0, ← ENNReal.ofReal_pow (mul_nonneg hcc0
          (mul_nonneg S.hT.le h𝔈'))]

end Rem2

section ZI2

variable {S : MainData d} {R : ∀ N, Realization d N} {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ}
  {𝔈 : ℕ → ℝ} {Ca Λ₁ : ℝ}

/-- Second moment of `Z_k - 𝕀_k` (`= M_k + R_k`), in the `L²` form `E (·)² ≤ b²`. -/
theorem a1014_ZI_moment2 (hspec : A8AdjSpec d S.s Rg MB Λ VB ν₀ Ca Λ₁) (hCa : 0 ≤ Ca)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (gammaIdx d) C₀ Cc 𝔈) {N : ℕ} (hN : 2 ≤ N)
    {ℱ : Filtration ℝ (R N).mΩ} {W' : ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ}
    (hF : IsFilteredSolution (R N).P ℱ W' (R N).W (R N).X)
    {C₀' Cq cT : ℝ} (hcom : A8CommSpec d S.s C₀' Cq) (hCq : 0 ≤ Cq) (hC : C₀' ≤ C₀) (hcT0 : 0 ≤ cT)
    (hcT : ∀ (M : Matrix (Fin d) (Fin d) ℝ), PDE.MatBound MB M → ∀ ψ : Torus d → ℝ, Torus.IsCk 2 ψ →
      MemSobolev (PDE.mStar d : ℝ) ψ →
        HasTransportBound d S.s (gfb2_v M ψ) (cT * sobolevNorm (PDE.mStar d : ℝ) ψ))
    {𝔈' : ℝ} (h𝔈' : 0 ≤ 𝔈')
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) S.T, ∫⁻ ω, ENNReal.ofReal
        ((correctedEnergy (S.dyn N) C₀ Λ (S.ρ N) ((R N).X (Real.toNNReal t) ω) t) ^ 2) ∂(R N).P ≤
      ENNReal.ofReal (𝔈' ^ 2))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T) (k : NonzeroLattice d) :
    ∫⁻ ω, ENNReal.ofReal ((NegSobolev.coord (a9Z S R N t ω) k -
        NegSobolev.coord (a9I S R N t ω) k) ^ 2) ∂(R N).P ≤
      ENNReal.ofReal ((Real.sqrt (S.T * (2 * (S.sigma N ^ 2 * S.invβ N / N) *
          (d * (Ca * a8pK Λ₁ t (a9phi d k))) ^ 2)) +
        S.sigma N * ((1 / 2) * (Cq * (cT * a8pK Λ₁ t (a9phi d k)))) * (S.T * 𝔈')) ^ 2) := by
  have hS' := a9_standing_mStar hS
  have hN1 : 1 ≤ N := by omega
  have hdec := a9_ZI_decomp hspec hCa hS hN hF ht k
  have hmart := a9_mart_moment hspec hCa hS' hN hF (fun _ : Fin 1 => t) (fun _ => ht)
    (fun _ => a9phi d k) (fun _ => a9phi_cont k) (fun _ => a9phi_mem _ k) 0
  have hrem := a1014_rem_moment2 hspec hCa hS' hN hF hcom hCq hC hcT0 hcT (fun _ : Fin 1 => t)
    (fun _ => ht) (fun _ => a9phi d k) (fun _ => a9phi_cont k) (fun _ => a9phi_mem _ k) 0 h𝔈' hb
  set Mc : (R N).Ω → ℝ := fun ω => vectorItoIntegral (R N).P ℱ W'
    (fun a => killAfter (a8pPhi (S.dyn N) (S.sigma N) ((fun _ : Fin 1 => t) a)
      (a8pF S N (fun _ : Fin 1 => t) (fun _ => a9phi d k) a) (R N).X) ((fun _ : Fin 1 => t) a))
    S.T ω 0 with hMc
  set Rc : (R N).Ω → ℝ := fun ω => a8pRem S R N (fun _ : Fin 1 => t) (fun _ => a9phi d k) ω 0
    with hRc
  obtain ⟨hL2, hsq⟩ := hmart
  have hσ := a8p_sigma_nonneg S N
  have hK0 := a8pK_nonneg Λ₁ t (a9phi d k)
  have hT0 := S.hT.le
  have hqq : 0 ≤ S.sigma N ^ 2 * S.invβ N / N := by
    have := S.hinvβ N
    positivity
  set Bm : ℝ := S.T * (2 * (S.sigma N ^ 2 * S.invβ N / N) * (d * (Ca * a8pK Λ₁ t (a9phi d k))) ^ 2)
    with hBm
  have hBm0 : 0 ≤ Bm := by rw [hBm]; positivity
  set cR : ℝ := S.sigma N * ((1 / 2) * (Cq * (cT * a8pK Λ₁ t (a9phi d k)))) * (S.T * 𝔈') with hcR
  have hcR0 : 0 ≤ cR := by
    have : 0 ≤ Cq * (cT * a8pK Λ₁ t (a9phi d k)) := mul_nonneg hCq (mul_nonneg hcT0 hK0)
    rw [hcR]; positivity
  -- `E Mc² ≤ Bm`
  have hMsq : ∫⁻ ω, ENNReal.ofReal (Mc ω ^ 2) ∂(R N).P ≤ ENNReal.ofReal Bm := by
    have hint : Integrable (fun ω => Mc ω ^ 2) (R N).P := hL2.integrable_sq
    have e : ENNReal.ofReal (∫ ω, Mc ω ^ 2 ∂(R N).P) = ∫⁻ ω, ENNReal.ofReal (Mc ω ^ 2) ∂(R N).P :=
      ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun ω => sq_nonneg _)
    rw [← e]
    exact ENNReal.ofReal_le_ofReal hsq
  have hMlp : (∫⁻ ω, ENNReal.ofReal (Mc ω ^ 2) ∂(R N).P) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Real.sqrt Bm) :=
    a1014_lp2 _ (Real.sqrt_nonneg _) (by rwa [Real.sq_sqrt hBm0])
  have hRlp : (∫⁻ ω, ENNReal.ofReal (Rc ω ^ 2) ∂(R N).P) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal cR :=
    a1014_lp2 _ hcR0 hrem
  -- Minkowski for `|Mc| + |Rc|`
  have hdec' : ∀ᵐ ω ∂(R N).P, NegSobolev.coord (a9Z S R N t ω) k -
      NegSobolev.coord (a9I S R N t ω) k = Mc ω + Rc ω := hdec
  have hZIm : AEMeasurable (fun ω => NegSobolev.coord (a9Z S R N t ω) k -
      NegSobolev.coord (a9I S R N t ω) k) (R N).P := by
    have h1 := a9_Z_meas hS hN1 ht hF
    have h2 := (a9_I_meas hS hN1 ht hF).mono (ℱ.le 0) le_rfl
    exact (((a1014_coord_continuous _ k).measurable.comp h1).sub
      ((a1014_coord_continuous _ k).measurable.comp h2)).aemeasurable
  have hMm : AEMeasurable Mc (R N).P := hL2.aestronglyMeasurable.aemeasurable
  have hRm : AEMeasurable Rc (R N).P := by
    refine (hZIm.sub hMm).congr ?_
    filter_upwards [hdec'] with ω h
    simp only [Pi.sub_apply]
    rw [h]; ring
  have hf : AEMeasurable (fun ω => ENNReal.ofReal |Mc ω|) (R N).P := hMm.abs.ennreal_ofReal
  have hg : AEMeasurable (fun ω => ENNReal.ofReal |Rc ω|) (R N).P := hRm.abs.ennreal_ofReal
  have hmk := ENNReal.lintegral_Lp_add_le (μ := (R N).P) (p := 2) hf hg (by norm_num)
  have e2 : ∀ u : ℝ, ENNReal.ofReal |u| ^ (2 : ℝ) = ENNReal.ofReal (u ^ 2) := fun u => by
    rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (abs_nonneg u), sq_abs]
  simp only [Pi.add_apply, e2] at hmk
  have hle : ∫⁻ ω, ENNReal.ofReal ((NegSobolev.coord (a9Z S R N t ω) k -
      NegSobolev.coord (a9I S R N t ω) k) ^ 2) ∂(R N).P ≤
      ∫⁻ ω, (ENNReal.ofReal |Mc ω| + ENNReal.ofReal |Rc ω|) ^ (2 : ℝ) ∂(R N).P := by
    refine lintegral_mono_ae ?_
    filter_upwards [hdec'] with ω h
    rw [h, ENNReal.rpow_two, ← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _),
      ← ENNReal.ofReal_pow (add_nonneg (abs_nonneg _) (abs_nonneg _))]
    refine ENNReal.ofReal_le_ofReal ?_
    calc (Mc ω + Rc ω) ^ 2 = |Mc ω + Rc ω| ^ 2 := (sq_abs _).symm
      _ ≤ (|Mc ω| + |Rc ω|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (abs_add_le _ _) 2
  have hroot : (∫⁻ ω, ENNReal.ofReal ((NegSobolev.coord (a9Z S R N t ω) k -
      NegSobolev.coord (a9I S R N t ω) k) ^ 2) ∂(R N).P) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Real.sqrt Bm + cR) := by
    refine (ENNReal.rpow_le_rpow hle (by norm_num)).trans (hmk.trans ?_)
    rw [ENNReal.ofReal_add (Real.sqrt_nonneg _) hcR0]
    exact add_le_add hMlp hRlp
  have := a1014_sq_of_rpow hroot
  refine this.trans ?_
  rw [← ENNReal.ofReal_pow (add_nonneg (Real.sqrt_nonneg _) hcR0)]

end ZI2

end HRS.Main.A1014

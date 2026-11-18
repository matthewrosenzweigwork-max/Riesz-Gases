import HRS.MH.ScreenedS5a
import HRS.MH.ScreenedS5b
import HRS.MH.ScreenedL1Aux1

/-!
# Packet S5c: `mult_sobolev`, Lipschitz multipliers on `H^σ`, `0 ≤ σ < 1`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MH.Screened

open HRS HRS.Whole

variable {d : ℕ}

lemma s5c_le_of_sq_le {a b : ℝ≥0∞} (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  by_contra hab
  exact absurd h (not_le.2 (ENNReal.pow_lt_pow_left (by norm_num) (not_le.1 hab)))

lemma s5c_memSob_of_lt {σ : ℝ} {u : Euc d → ℝ} (h : sobolevNormE σ u < ⊤) :
    HRS.PDE.ToolboxRd.MemSobolev σ u := by
  by_contra hM
  unfold sobolevNormE at h
  rw [if_neg hM] at h
  exact lt_irrefl _ h

lemma s5c_norm_eq_top {σ : ℝ} {u : Euc d → ℝ} (h : ¬ HRS.PDE.ToolboxRd.MemSobolev σ u) :
    sobolevNormE σ u = ⊤ := by
  unfold sobolevNormE; rw [if_neg h]

open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux in
lemma s5c_l2_le {σ : ℝ} (h0 : 0 ≤ σ) {u : Euc d → ℝ} (hM : HRS.PDE.ToolboxRd.MemSobolev σ u) :
    eLpNorm u 2 volume ≤ sobolevNormE σ u := by
  rw [← l1_sobolev_zero_eq hM.1]
  have hM0 : HRS.PDE.ToolboxRd.MemSobolev 0 u := memSobolev_mono h0 hM
  have hsq : (sobolevNormE 0 u) ^ 2 ≤ (sobolevNormE σ u) ^ 2 := by
    rw [s5a_sobolevNormE_sq hM0, s5a_sobolevNormE_sq hM]
    refine lintegral_mono fun ξ => ?_
    gcongr
    exact one_le_wt ξ
  exact s5c_le_of_sq_le hsq

lemma s5c_mul {La B : ℝ} {ϕ u : Euc d → ℝ} (hLa : 0 ≤ La) (hL : HRS.PDE.ToolboxRd.IsLipschitz La ϕ)
    (hB : ∀ x, |ϕ x| ≤ B) (hu : MemLp u 2 volume) :
    MemLp (fun x => ϕ x * u x) 2 volume ∧
      eLpNorm (fun x => ϕ x * u x) 2 volume ≤ ENNReal.ofReal B * eLpNorm u 2 volume := by
  have hc : Continuous ϕ := by
    refine (LipschitzWith.of_dist_le_mul (K := La.toNNReal) (fun x y => ?_)).continuous
    simpa [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hLa] using hL x y
  have hmeas : AEStronglyMeasurable (fun x => ϕ x * u x) volume :=
    hc.aestronglyMeasurable.mul hu.aestronglyMeasurable
  have hae : ∀ᵐ x ∂(volume : Measure (Euc d)), ‖ϕ x * u x‖ ≤ B * ‖u x‖ :=
    Filter.Eventually.of_forall fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using hB x) (norm_nonneg _)
  exact ⟨hu.of_le_mul hmeas hae, eLpNorm_le_mul_eLpNorm_of_ae_le_mul hmeas hae 2⟩


open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux in
lemma s5c_zero_norm {σ : ℝ} : sobolevNormE σ (fun _ : Euc d => (0 : ℝ)) = 0 := by
  have h0 : MemLp (fun _ : Euc d => (0 : ℝ)) 2 volume := MemLp.zero
  have hae : fourierL2 (fun _ : Euc d => (0 : ℝ)) =ᵐ[volume] fun _ => (0 : ℂ) := by
    have := fourierL2_smul (d := d) h0 0
    simpa using this
  have hf : (fun ξ : Euc d => (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ σ *
      ‖fourierL2 (fun _ : Euc d => (0 : ℝ)) ξ‖ ^ 2) =ᵐ[volume] fun _ => (0 : ℝ) :=
    hae.mono fun ξ hξ => by simp [hξ]
  have hM : HRS.PDE.ToolboxRd.MemSobolev σ (fun _ : Euc d => (0 : ℝ)) :=
    ⟨h0, (integrable_zero _ _ _).congr (hf.symm)⟩
  unfold sobolevNormE
  rw [if_pos hM]
  have : sobolevNormSq σ (fun _ : Euc d => (0 : ℝ)) = 0 := by
    unfold sobolevNormSq
    rw [integral_congr_ae hf]; simp
  rw [this]; simp

lemma s5c_alg {c₁ c₂ p q : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hp : 0 ≤ p) (hq : 0 ≤ q) (X : ℝ≥0∞) :
    ENNReal.ofReal c₁ * (ENNReal.ofReal p * X + ENNReal.ofReal q * (X + ENNReal.ofReal c₂ * X)) =
      ENNReal.ofReal (c₁ * (p + q * (1 + c₂))) * X := by
  rw [ENNReal.ofReal_mul hc₁, ENNReal.ofReal_add hp (by positivity), ENNReal.ofReal_mul hq,
    ENNReal.ofReal_add (by norm_num) hc₂, ENNReal.ofReal_one]
  ring

lemma s5c_core (hd : 1 ≤ d) {σ : ℝ} (h0 : 0 ≤ σ) (h1 : σ < 1) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (La B : ℝ) (ϕ u : Euc d → ℝ), HRS.PDE.ToolboxRd.IsLipschitz La ϕ →
      (∀ x, |ϕ x| ≤ B) → sobolevNormE σ u < ⊤ →
      sobolevNormE σ (fun x => ϕ x * u x) ≤ ENNReal.ofReal (C * (La + B)) * sobolevNormE σ u := by
  rcases h0.eq_or_lt with h | hpos
  · subst h
    refine ⟨1, le_rfl, fun La B ϕ u hL hB hN => ?_⟩
    have hLa := s5b_La_nonneg hd hL
    have hu := (s5c_memSob_of_lt hN).1
    obtain ⟨hmem, hnorm⟩ := s5c_mul hLa hL hB hu
    rw [l1_sobolev_zero_eq hmem, l1_sobolev_zero_eq hu]
    refine hnorm.trans ?_
    gcongr
    linarith
  · obtain ⟨c₁, c₂, hc₁, hc₂, hE⟩ := gag_equiv_proof hd hpos h1
    obtain ⟨C, hC0, hP⟩ := gag_product_proof hd hpos h1
    set K : ℝ := c₁ * (1 + C * (1 + c₂)) with hK
    have hK0 : 0 < K := by positivity
    refine ⟨max 1 (Real.sqrt K), le_max_left _ _, fun La B ϕ u hL hB hN => ?_⟩
    have hLa := s5b_La_nonneg hd hL
    have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
    have hMs := s5c_memSob_of_lt hN
    have hu := hMs.1
    obtain ⟨hmem, hnorm⟩ := s5c_mul hLa hL hB hu
    set N := sobolevNormE σ u with hNdef
    have he : eLpNorm u 2 volume ≤ N := s5c_l2_le h0 hMs
    have hg : gagSq σ u ≤ ENNReal.ofReal c₂ * N ^ 2 := (hE u hu).2
    have h1' := (hE _ hmem).1
    have h2' := hP La B ϕ u hL hB hu
    have he2 : (eLpNorm (fun x => ϕ x * u x) 2 volume) ^ 2 ≤ ENNReal.ofReal (B ^ 2) * N ^ 2 := by
      calc (eLpNorm (fun x => ϕ x * u x) 2 volume) ^ 2 ≤ (ENNReal.ofReal B * N) ^ 2 := by
            gcongr; exact hnorm.trans (by gcongr)
        _ = ENNReal.ofReal (B ^ 2) * N ^ 2 := by
            rw [mul_pow, ENNReal.ofReal_pow hB0]
    have hsq : (sobolevNormE σ (fun x => ϕ x * u x)) ^ 2 ≤
        ENNReal.ofReal (K * (La + B) ^ 2) * N ^ 2 := by
      calc (sobolevNormE σ (fun x => ϕ x * u x)) ^ 2
          ≤ ENNReal.ofReal c₁ * ((eLpNorm (fun x => ϕ x * u x) 2 volume) ^ 2 +
              gagSq σ (fun x => ϕ x * u x)) := h1'
        _ ≤ ENNReal.ofReal c₁ * (ENNReal.ofReal (B ^ 2) * N ^ 2 +
              ENNReal.ofReal (C * (La + B) ^ 2) * (N ^ 2 + ENNReal.ofReal c₂ * N ^ 2)) := by
            gcongr
            refine h2'.trans ?_
            gcongr
        _ = ENNReal.ofReal (c₁ * (B ^ 2 + C * (La + B) ^ 2 * (1 + c₂))) * N ^ 2 :=
            s5c_alg hc₁.le hc₂.le (sq_nonneg B) (by positivity) _
        _ ≤ ENNReal.ofReal (K * (La + B) ^ 2) * N ^ 2 := by
            refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
            have h3 : 0 ≤ c₁ * ((La + B) ^ 2 - B ^ 2) := mul_nonneg hc₁.le (by nlinarith)
            rw [hK]
            nlinarith [h3]
    have hfin : sobolevNormE σ (fun x => ϕ x * u x) ≤
        ENNReal.ofReal (Real.sqrt K * (La + B)) * N := by
      refine s5c_le_of_sq_le ?_
      refine hsq.trans (le_of_eq ?_)
      rw [mul_pow, ← ENNReal.ofReal_pow (by positivity), mul_pow, Real.sq_sqrt hK0.le]
    refine hfin.trans ?_
    gcongr
    exact le_max_right _ _

/-- **S5c** (`mult_sobolev`). -/
theorem mult_sobolev_proof (hd : 1 ≤ d) {σ : ℝ} (h0 : 0 ≤ σ) (h1 : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (La B : ℝ) (ϕ u : Euc d → ℝ), HRS.PDE.ToolboxRd.IsLipschitz La ϕ → (∀ x, |ϕ x| ≤ B) →
      sobolevNormE σ (fun x => ϕ x * u x) ≤ ENNReal.ofReal (C * (La + B)) * sobolevNormE σ u := by
  obtain ⟨C, hC1, hC⟩ := s5c_core hd h0 h1
  refine ⟨C, by linarith, fun La B ϕ u hL hB => ?_⟩
  have hLa := s5b_La_nonneg hd hL
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  by_cases hN : sobolevNormE σ u < ⊤
  · exact hC La B ϕ u hL hB hN
  · have htop : sobolevNormE σ u = ⊤ := not_lt_top_iff.1 hN
    by_cases hz : La + B = 0
    · have hB' : B = 0 := by linarith
      have hϕ : (fun x => ϕ x * u x) = fun _ => (0 : ℝ) := by
        funext x
        have : ϕ x = 0 := abs_nonpos_iff.1 (by simpa [hB'] using hB x)
        simp [this]
      rw [hϕ, s5c_zero_norm]
      simp
    · have hpos : 0 < C * (La + B) := by
        have : 0 < La + B := lt_of_le_of_ne (by linarith) (Ne.symm hz)
        positivity
      rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.2 hpos).ne']
      exact le_top

end HRS.MH.Screened

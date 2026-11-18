import HRS.MS.SA16Y3Op1
import HRS.MS.SA16Y3Ext1

/-!
# S.A.16 (SA16Y3) Op2: the bounded operator `P^A_μ : W^{m+2,p} → W^{m,p}` (packet P7, Hilbert corner)

`sa16y3_PA_jetbound`, `sa16y3_PA_memS`, `sa16y3_PA_Jbound`, `sa16y3_LA`, `sa16y3_extendA`: the analogue of Mem1, Mem2, Ext1
for the skew operator (`sa16r_extend_cc`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Op2
variable {d : ℕ} {s p : ℝ} [Fact (2 ≤ p)]

theorem sa16y3_PA_jetbound (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hθ1 : 1 < s + 2 - d) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {A : Matrix (Fin d) (Fin d) ℝ} {AB : ℝ}, 0 ≤ AB → (∀ a b, |A a b| ≤ AB) →
      A.transpose = -A → ∀ {μ φ : Euc d → ℝ}, ContDiff ℝ ∞ μ → IsCcInfty φ → ∀ {Λ : ℝ}, 0 ≤ Λ →
      sa16z_Cb (m + 2) Λ μ →
      eLpNorm (wJet m (sa16y3_PA s A μ φ)) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (K * (AB * Λ)) * eLpNorm (wJet (m + 2) φ) (ENNReal.ofReal p) volume := by
  have hp2 : (2 : ℝ) ≤ p := Fact.out
  have hp : 1 < p := by linarith
  choose Kj hKj0 hKj using fun j : ℕ => sa16y3_pd_PA_bound (s := s) hd hs0 hsd hθ1 hp j
  set cS : ℝ := ∑ k ∈ Finset.range (m + 2 + 1), ((d : ℝ) ^ k + 1) with hcS
  set cK : ℝ := ∑ j ∈ Finset.range (m + 1), (d : ℝ) ^ j * Kj j with hcK
  have hcS0 : 0 ≤ cS := Finset.sum_nonneg fun _ _ => by positivity
  have hcK0 : 0 ≤ cK := Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (hKj0 j)
  refine ⟨cK * cS, mul_nonneg hcK0 hcS0, fun {A AB} hAB hAab hA {μ φ} hμ hφ {Λ} hΛ hCb => ?_⟩
  have hΛA : 0 ≤ AB * Λ := mul_nonneg hAB hΛ
  have hPs : ContDiff ℝ ∞ (sa16y3_PA s A μ φ) := sa16y3_PA_smooth hs0 hsd A hμ hφ
  have key : ∀ j ∈ Finset.range (m + 1), ∑ idx : Fin j → Fin d,
      eLpNorm (partialDeriv idx (sa16y3_PA s A μ φ)) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal ((d : ℝ) ^ j * (Kj j * (AB * Λ))) * sa16z_S p φ (m + 2) := by
    intro j hj
    have hjm : j ≤ m := by have := Finset.mem_range.1 hj; omega
    have h1 : ∀ idx : Fin j → Fin d, eLpNorm (partialDeriv idx (sa16y3_PA s A μ φ)) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (Kj j * (AB * Λ)) * sa16z_S p φ (m + 2) := fun idx =>
      (hKj j hAB hAab hA hμ hφ hΛ (sa16z_Cb_mono (by omega) hCb) idx).trans
        (by gcongr; exact sa16z_S_mono φ (by omega))
    refine (Finset.sum_le_sum fun idx _ => h1 idx).trans (le_of_eq ?_)
    have e : ((d ^ j : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((d : ℝ) ^ j) := by
      rw [← ENNReal.ofReal_natCast]; push_cast; rfl
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul, e,
      ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  calc eLpNorm (wJet m (sa16y3_PA s A μ φ)) (ENNReal.ofReal p) volume
      ≤ ∑ j ∈ Finset.range (m + 1), ∑ idx : Fin j → Fin d,
          eLpNorm (partialDeriv idx (sa16y3_PA s A μ φ)) (ENNReal.ofReal p) volume := sa16y3_jet_le_pd hPs m
    _ ≤ ∑ j ∈ Finset.range (m + 1), ENNReal.ofReal ((d : ℝ) ^ j * (Kj j * (AB * Λ))) * sa16z_S p φ (m + 2) :=
        Finset.sum_le_sum key
    _ = ENNReal.ofReal (cK * (AB * Λ)) * sa16z_S p φ (m + 2) := by
        rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun j _ => by
          exact mul_nonneg (by positivity) (mul_nonneg (hKj0 j) hΛA)), hcK, Finset.sum_mul]
        congr 2
        refine Finset.sum_congr rfl fun j _ => by ring
    _ ≤ ENNReal.ofReal (cK * (AB * Λ)) * (ENNReal.ofReal cS * eLpNorm (wJet (m + 2) φ) (ENNReal.ofReal p) volume) := by
        gcongr
        exact sa16y3_S_le_jet hφ.1 (m + 2)
    _ = ENNReal.ofReal (cK * cS * (AB * Λ)) * eLpNorm (wJet (m + 2) φ) (ENNReal.ofReal p) volume := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (mul_nonneg hcK0 hΛA)]
        congr 2; ring

lemma sa16y3_memLp_pdA (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hθ1 : 1 < s + 2 - d) (j : ℕ)
    {A : Matrix (Fin d) (Fin d) ℝ} {AB : ℝ} (hAB : 0 ≤ AB) (hAab : ∀ a b, |A a b| ≤ AB) (hA : A.transpose = -A)
    {μ φ : Euc d → ℝ} (hμ : ContDiff ℝ ∞ μ) (hφ : IsCcInfty φ) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hCb : sa16z_Cb (j + 2) Λ μ) (idx : Fin j → Fin d) :
    MemLp (partialDeriv idx (sa16y3_PA s A μ φ)) (ENNReal.ofReal p) volume := by
  have hp2 : (2 : ℝ) ≤ p := Fact.out
  obtain ⟨K, hK0, hK⟩ := sa16y3_pd_PA_bound (s := s) hd hs0 hsd hθ1 (show 1 < p by linarith) j
  exact lt_of_le_of_lt (hK hAB hAab hA hμ hφ hΛ hCb idx)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (sa16y3_S_lt_top hφ _))

lemma sa16y3_S_memLpA (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hθ1 : 1 < s + 2 - d) (m : ℕ)
    {A : Matrix (Fin d) (Fin d) ℝ} {AB : ℝ} (hAB : 0 ≤ AB) (hAab : ∀ a b, |A a b| ≤ AB) (hA : A.transpose = -A)
    {μ φ : Euc d → ℝ} (hμ : ContDiff ℝ ∞ μ) (hφ : IsCcInfty φ) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hCb : sa16z_Cb (m + 2) Λ μ) :
    MemLp (sa16j_S d m (sa16y3_PA s A μ φ)) (ENNReal.ofReal p) volume := by
  have hPs : ContDiff ℝ ∞ (sa16y3_PA s A μ φ) := sa16y3_PA_smooth hs0 hsd A hμ hφ
  have hg : MemLp (fun x => ∑ j ∈ Finset.range (m + 1), ∑ idx : Fin j → Fin d,
      ‖partialDeriv idx (sa16y3_PA s A μ φ) x‖) (ENNReal.ofReal p) volume := by
    refine memLp_finsetSum _ fun j hj => memLp_finsetSum _ fun idx _ => ?_
    exact (sa16y3_memLp_pdA hd hs0 hsd hθ1 j hAB hAab hA hμ hφ hΛ
      (sa16z_Cb_mono (by have := Finset.mem_range.1 hj; omega) hCb) idx).norm
  refine hg.mono' (sa16j_S_cont hPs m).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sa16j_S_nonneg d m _ x)]
  simpa [Real.norm_eq_abs] using sa16j_S_le m (sa16y3_PA s A μ φ) x

theorem sa16y3_PA_memS (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hθ1 : 1 < s + 2 - d) (m : ℕ)
    {A : Matrix (Fin d) (Fin d) ℝ} {AB : ℝ} (hAB : 0 ≤ AB) (hAab : ∀ a b, |A a b| ≤ AB) (hA : A.transpose = -A)
    {μ φ : Euc d → ℝ} (hμ : ContDiff ℝ ∞ μ) (hφ : IsCcInfty φ) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hCb : sa16z_Cb (m + 2) Λ μ) : sa16y3_PA s A μ φ ∈ sa16r_S d m p :=
  sa16r_mem_S m (sa16y3_PA_smooth hs0 hsd A hμ hφ) (sa16y3_S_memLpA hd hs0 hsd hθ1 m hAB hAab hA hμ hφ hΛ hCb)

theorem sa16y3_PA_Jbound (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hθ1 : 1 < s + 2 - d) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {A : Matrix (Fin d) (Fin d) ℝ} {AB : ℝ}, 0 ≤ AB → (∀ a b, |A a b| ≤ AB) →
      A.transpose = -A → ∀ {μ : Euc d → ℝ}, ContDiff ℝ ∞ μ → ∀ {Λ : ℝ}, 0 ≤ Λ → sa16z_Cb (m + 2) Λ μ →
      ∀ (φ : ccSub d) (f : sa16r_S d m p), f.1 = sa16y3_PA s A μ φ.1 →
        ‖sa16r_J d m p f‖ ≤ K * (AB * Λ) * ‖sa16r_Jcc d (m + 2) p φ‖ := by
  obtain ⟨K, hK0, hK⟩ := sa16y3_PA_jetbound (s := s) (p := p) hd hs0 hsd hθ1 m
  refine ⟨K, hK0, fun {A AB} hAB hAab hA {μ} hμ {Λ} hΛ hCb φ f hf => ?_⟩
  have hS : MemLp (sa16j_S d m f.1) (ENNReal.ofReal p) volume := by
    rw [hf]; exact sa16y3_S_memLpA hd hs0 hsd hθ1 m hAB hAab hA hμ φ.2 hΛ hCb
  rw [sa16r_J_norm m hS, sa16r_Jcc_norm, hf]
  have hfin : eLpNorm (wJet (m + 2) φ.1) (ENNReal.ofReal p) volume ≠ ⊤ :=
    (sa16r_jet_memLp_cc (p := p) φ.2 (m + 2)).eLpNorm_lt_top.ne
  have h1 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) (hK hAB hAab hA hμ φ.2 hΛ hCb)
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg hK0 (mul_nonneg hAB hΛ))] at h1

/-- `φ ↦ P^A_μ φ` as a linear map `C_c^∞ → sa16r_S d m p` -/
def sa16y3_LA (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hθ1 : 1 < s + 2 - d) (m : ℕ)
    {A : Matrix (Fin d) (Fin d) ℝ} {AB : ℝ} (hAB : 0 ≤ AB) (hAab : ∀ a b, |A a b| ≤ AB) (hA : A.transpose = -A)
    {μ : Euc d → ℝ} (hμ : ContDiff ℝ ∞ μ) {Λ : ℝ} (hΛ : 0 ≤ Λ) (hCb : sa16z_Cb (m + 2) Λ μ) :
    ccSub d →ₗ[ℝ] sa16r_S d m p where
  toFun φ := ⟨sa16y3_PA s A μ φ.1, sa16y3_PA_memS hd hs0 hsd hθ1 m hAB hAab hA hμ φ.2 hΛ hCb⟩
  map_add' φ ψ := Subtype.ext (sa16y3_PA_add hs0 hsd A hμ φ.2 ψ.2)
  map_smul' c φ := Subtype.ext (sa16y3_PA_smul hs0 hsd A hμ φ.2 c)

theorem sa16y3_extendA (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hθ1 : 1 < s + 2 - d) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {A : Matrix (Fin d) (Fin d) ℝ} {AB : ℝ}, 0 ≤ AB → (∀ a b, |A a b| ≤ AB) →
      A.transpose = -A → ∀ {μ : Euc d → ℝ}, ContDiff ℝ ∞ μ → ∀ {Λ : ℝ}, 0 ≤ Λ → sa16z_Cb (m + 2) Λ μ →
      ∃ T : WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d m p, ‖T‖ ≤ K * (AB * Λ) ∧
        ∀ φ : ccSub d, (((T (sa16r_Jcc d (m + 1 + 1) p φ) : WmpSpace d m p) : WLp d m p) :
          Euc d → (WIndex d m → ℝ)) =ᵐ[volume] wJet m (sa16y3_PA s A μ φ.1) := by
  obtain ⟨K, hK0, hK⟩ := sa16y3_PA_Jbound (s := s) (p := p) hd hs0 hsd hθ1 m
  refine ⟨K, hK0, fun {A AB} hAB hAab hA {μ} hμ {Λ} hΛ hCb => ?_⟩
  obtain ⟨T, hT, hTJ, -⟩ := sa16r_extend_cc d (m + 1 + 1) m p (sa16y3_LA hd hs0 hsd hθ1 m hAB hAab hA hμ hΛ hCb)
    (mul_nonneg hK0 (mul_nonneg hAB hΛ)) (fun φ => hK hAB hAab hA hμ hΛ hCb φ _ rfl)
  refine ⟨T, hT, fun φ => ?_⟩
  have hS : MemLp (sa16j_S d m (sa16y3_PA s A μ φ.1)) (ENNReal.ofReal p) volume :=
    sa16y3_S_memLpA hd hs0 hsd hθ1 m hAB hAab hA hμ φ.2 hΛ hCb
  rw [hTJ φ]
  exact sa16r_J_coe m (f := sa16y3_LA hd hs0 hsd hθ1 m hAB hAab hA hμ hΛ hCb φ) hS

end Op2

end HRS.Whole.AppendixA.Phase2SA16R

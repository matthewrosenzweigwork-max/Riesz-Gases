import HRS.MC.IID1
import HRS.MC.IID2
import HRS.MC.IID3
import HRS.MC.IID4
import HRS.MC.S7ChaosIIDVocab

/-!
# Packet iid3, step A: the bridge from independent to correlated Gaussians (`chaos_iid_representation`)

`chaos_iid_representation_proof` is the statement of `HRS.chaos_iid_representation` (the printed independent form of
`Q_ε`): the field `G_i = lim ∑_{k<n} S_ik g_k` of `iid_field` is Gaussian with the susceptibility covariance, and
every `L²`-limit `Q` of the iid sections of `SᵀHS` is the correlated chaos limit `s7_IsChaosLimit`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.IID

open HRS HRS.MC.Sec7

section Aux

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- `L²` convergence from convergence of the seminorms. -/
theorem tendstoL2_of_tendsto_eLpNorm {Qn : ℕ → Ω → ℝ} {Q : Ω → ℝ} (hQ : AEStronglyMeasurable Q P)
    (hm : ∀ n, AEStronglyMeasurable (Qn n) P)
    (h : Tendsto (fun n => eLpNorm (Qn n - Q) 2 P) atTop (𝓝 0)) : TendstoL2 P Qn Q := by
  refine ⟨hQ, ?_⟩
  have e : ∀ n, ∫⁻ ω, ‖Qn n ω - Q ω‖ₑ ^ 2 ∂P = eLpNorm (Qn n - Q) 2 P ^ 2 :=
    fun n => lintegral_enorm_sq_eq ((hm n).sub hQ)
  simp_rw [e]
  have := (ENNReal.continuous_pow 2).tendsto 0 |>.comp h
  simpa [Function.comp_def] using this

/-- `L²` limits are compatible with differences. -/
theorem tendstoL2_sub {an bn : ℕ → Ω → ℝ} {a b : Ω → ℝ} (ham : ∀ n, AEStronglyMeasurable (an n) P)
    (hbm : ∀ n, AEStronglyMeasurable (bn n) P) (ha : TendstoL2 P an a) (hb : TendstoL2 P bn b) :
    TendstoL2 P (fun n ω => an n ω - bn n ω) (fun ω => a ω - b ω) := by
  have h1 := ha.tendsto_eLpNorm ham
  have h2 := hb.tendsto_eLpNorm hbm
  have h3 := Filter.Tendsto.add h1 h2
  rw [add_zero] at h3
  refine tendstoL2_of_tendsto_eLpNorm (ha.1.sub hb.1) (fun n => (ham n).sub (hbm n)) ?_
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3 (fun _ => bot_le) fun n => ?_
  have e : (fun ω => an n ω - bn n ω) - (fun ω => a ω - b ω) = (an n - a) - (bn n - b) := by
    funext ω; simp only [Pi.sub_apply]; ring
  rw [e]
  exact eLpNorm_sub_le (by norm_num)

/-- Sections are linear in the coefficient matrix. -/
theorem chaosSection_sub (A A' : ℕ → ℕ → ℝ) (g : ℕ → Ω → ℝ) (n : ℕ) :
    chaosSection (fun k l => A k l - A' k l) g n =
      fun ω => chaosSection A g n ω - chaosSection A' g n ω := by
  funext ω
  unfold chaosSection
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- Second moment of a centred `L²` function as a variance. -/
theorem lintegral_sq_eq_variance {f : Ω → ℝ} (hf : MemLp f 2 P) (h0 : ∫ ω, f ω ∂P = 0) :
    ∫⁻ ω, ‖f ω‖ₑ ^ 2 ∂P = ENNReal.ofReal (variance f P) := by
  rw [variance_eq_integral hf.aemeasurable, h0]
  have hi : Integrable (fun ω => (f ω) ^ 2) P := hf.integrable_sq
  simp only [sub_zero]
  rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun ω => sq_nonneg _)]
  refine lintegral_congr fun ω => ?_
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]

end Aux

section Main

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ}

/-- The chaos limit statement for a general contraction factor. -/
theorem chaosLimit_of_tendstoL2 (hg : IsStdGaussianSeq P g) {S Cm : ℕ → ℕ → ℝ} (hbound : ContrBound S)
    (hS : ∀ i j, HasSum (fun k => S i k * S j k) (Cm i j)) {G : ℕ → Ω → ℝ}
    (hG : ∀ i, TendstoL2 P (fun n ω => ∑ k ∈ range n, S i k * g k ω) (G i))
    {B : ℕ → ℕ → ℝ} (hB : IsSymmetricHS B) {Q : Ω → ℝ}
    (hQ : TendstoL2 P (chaosSection (s7_conjCoeff S B) g) Q) :
    Tendsto (fun L : ℕ => ∫⁻ ω, ‖Q ω - (1 / 2) * ∑ i ∈ range L, ∑ j ∈ range L,
      B i j * (G i ω * G j ω - Cm i j)‖ₑ ^ 2 ∂P) atTop (𝓝 0) := by
  have hAs : IsSymmetricHS (s7_conjCoeff S B) := (conj_isSymmetricHS hbound hB).1
  have hmeasS : ∀ (A : ℕ → ℕ → ℝ) n, AEStronglyMeasurable (chaosSection A g n) P := fun A n =>
    ((memLp_quadSum hg A n).const_mul (1 / 2)).aestronglyMeasurable
  have hmemS : ∀ (A : ℕ → ℕ → ℝ) n, MemLp (chaosSection A g n) 2 P := fun A n =>
    (memLp_quadSum hg A n).const_mul (1 / 2)
  -- `Q` is the iid chaos of `SᵀBS`
  have hQc : Q =ᵐ[P] chaos P (s7_conjCoeff S B) g :=
    TendstoL2.ae_unique (hmeasS _) hQ (chaos_tendsto P _ hAs g hg)
  have hL : ∀ L : ℕ, ∫⁻ ω, ‖Q ω - (1 / 2) * ∑ i ∈ range L, ∑ j ∈ range L,
      B i j * (G i ω * G j ω - Cm i j)‖ₑ ^ 2 ∂P =
      ENNReal.ofReal ((1 / 2) * hsNorm (fun k l => s7_conjCoeff S B k l -
        s7_conjCoeff S (trunc L B) k l) ^ 2) := by
    intro L
    have hAL : IsSymmetricHS (s7_conjCoeff S (trunc L B)) :=
      (conj_isSymmetricHS hbound (isSymmetricHS_trunc L hB)).1
    have hD : IsSymmetricHS (fun k l => s7_conjCoeff S B k l - s7_conjCoeff S (trunc L B) k l) := by
      have hsub := conj_sub hbound hB (isSymmetricHS_trunc L hB)
      have : (fun k l => s7_conjCoeff S B k l - s7_conjCoeff S (trunc L B) k l) =
          s7_conjCoeff S (B - trunc L B) := hsub.symm
      rw [this]
      exact (conj_isSymmetricHS hbound (isSymmetricHS_sub hB (isSymmetricHS_trunc L hB))).1
    -- the correlated section is the iid chaos of the truncation
    have hXL := section_ae_eq hg hbound hS hG hB L
    -- linearity of the chaos
    have hlin : chaos P (fun k l => s7_conjCoeff S B k l - s7_conjCoeff S (trunc L B) k l) g =ᵐ[P]
        fun ω => chaos P (s7_conjCoeff S B) g ω - chaos P (s7_conjCoeff S (trunc L B)) g ω := by
      refine TendstoL2.ae_unique (hmeasS _) (chaos_tendsto P _ hD g hg) ?_
      have e := funext (chaosSection_sub (s7_conjCoeff S B) (s7_conjCoeff S (trunc L B)) g)
      rw [e]
      exact tendstoL2_sub (hmeasS _) (hmeasS _) (chaos_tendsto P _ hAs g hg)
        (chaos_tendsto P _ hAL g hg)
    have hmD : MemLp (chaos P (fun k l => s7_conjCoeff S B k l - s7_conjCoeff S (trunc L B) k l) g) 2 P :=
      memLp_of_tendstoL2 (hmemS _) (chaos_tendsto P _ hD g hg)
    obtain ⟨hmean, hvar, -⟩ := chaos_moments P _ hD g hg
    have hq := lintegral_sq_eq_variance hmD hmean
    rw [hvar] at hq
    rw [← hq]
    refine lintegral_congr_ae ?_
    filter_upwards [hQc, hXL, hlin] with ω h1 h2 h3
    have h2' : (1 / 2) * ∑ i ∈ range L, ∑ j ∈ range L, B i j * (G i ω * G j ω - Cm i j) =
        chaos P (s7_conjCoeff S (trunc L B)) g ω := h2
    rw [h1, h2', h3]
  simp_rw [hL]
  have h0 := hsNorm_conj_tail_tendsto hbound hB
  have h1 : Tendsto (fun L => (1 / 2 : ℝ) * hsNorm (fun k l => s7_conjCoeff S B k l -
      s7_conjCoeff S (trunc L B) k l) ^ 2) atTop (𝓝 ((1 / 2) * 0 ^ 2)) :=
    (h0.pow 2).const_mul _
  have h2 := ENNReal.tendsto_ofReal h1
  simpa using h2

end Main

section Bridge

variable {d : ℕ}

/-- Bridge from independent to correlated Gaussians (the mathematics behind `E:eq:Qepsilon`): the proof of
`HRS.chaos_iid_representation`. -/
theorem chaos_iid_representation_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (e : ℕ → Torus d → ℝ)
    (he : IsONBL2Zero (withDensityReal ρ) e) (S : ℕ → ℕ → ℝ) (hS : s7_IsCovFactor d s β ρ e S)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (g : ℕ → Ω → ℝ)
    (hg : IsStdGaussianSeq P g) :
    ∃ G : ℕ → Ω → ℝ,
      s7_GaussData d s β ρ e P G ∧
      (∀ i, TendstoL2 P (fun n ω => ∑ k ∈ Finset.range n, S i k * g k ω) (G i)) ∧
      ∀ h : Torus d → Torus d → ℝ, IsSymmetricHS (s7_kernelCoeff ρ e h) →
        IsSymmetricHS (s7_conjCoeff S (s7_kernelCoeff ρ e h)) ∧
        ∀ Q : Ω → ℝ, TendstoL2 P (chaosSection (s7_conjCoeff S (s7_kernelCoeff ρ e h)) g) Q →
          s7_IsChaosLimit d s β ρ e P G h Q := by
  have hbound : ContrBound S := covFactor_bound hd hs0 hsd hβ ρ hρ e he S hS
  obtain ⟨G, hGm, hGL, hGlaw⟩ := iid_field P g hg S _ hS
  refine ⟨G, ⟨hGm, hGlaw⟩, hGL, fun h hh => ⟨(conj_isSymmetricHS hbound hh).1, fun Q hQ => ?_⟩⟩
  exact chaosLimit_of_tendstoL2 hg hbound hS hGL hh hQ

end Bridge

end HRS.MC.IID

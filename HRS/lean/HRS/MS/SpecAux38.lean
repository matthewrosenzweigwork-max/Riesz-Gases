import HRS.MS.SpecAux37
import HRS.MS.QsfAux2

/-!
# S8P: `L²(μ)` facts for the eigenfunction `e = A f` and its response (S8.7, packets b3, b7)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  For a Schwartz `φ` with `∫ √ρ φ = 0`, `f = φ/√ρ`, `e = s8p_E φ`:
`f, U, e ∈ L²(μ)`, `∫ f dμ = ∫ e dμ = 0`, `h = ν f` is a response of `e` (`IsResponse`, `(I + βK) ν f = e`) and
`responseInverse (rieszKernel) μ β e = ν f` `μ`-a.e. (uniqueness from the abstract `s45_response_iff`).
-/

noncomputable section

open MeasureTheory
open scoped ENNReal RealInnerProductSpace ContDiff

namespace HRS.MS.Spec

open HRS HRS.Whole HRS.MS.MovDec

variable {d : ℕ} {s : ℝ} {ρ : Euc d → ℝ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

theorem s8p_f_memLp (hρ : Mov2eRho d ρ) (φ : 𝓢R) :
    MemLp (fun x => φ x / Real.sqrt (ρ x)) 2 (HRS.Whole.withDensityReal ρ) :=
  (mov2e_f_data hρ φ).2.1

theorem s8p_f_mean (hρ : Mov2eRho d ρ) (φ : 𝓢R) (hφc : ∫ x, Real.sqrt (ρ x) * φ x = 0) :
    ∫ x, φ x / Real.sqrt (ρ x) ∂(HRS.Whole.withDensityReal ρ) = 0 := by
  rw [mov2e_integral_mu hρ]
  rw [← hφc]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact mov2e_rho_div hρ φ x

theorem s8p_U_memLp (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : Mov2eRho d ρ) (hE : Mov2eEll d ρ)
    (β : ℝ) (φ : 𝓢R) : MemLp (s8p_U d s ρ φ) 2 (HRS.Whole.withDensityReal ρ) := by
  haveI := mov2e_isProb hρ
  have hUc : Continuous (s8p_U d s ρ φ) := (s8p_U_smooth hd hs0 hsd hρ hE φ).continuous
  refine (memLp_two_iff_integrable_sq hUc.aestronglyMeasurable).2 ?_
  rw [mov2e_integrable_mu hρ]
  have hW := mov2e_W_memLp hd hs0 hsd hρ hE β φ
  have hphi : MemLp (⇑φ) 2 volume := φ.memLp 2
  have e : (fun x => Real.sqrt (ρ x) * s8p_U d s ρ φ x) =
      fun x => mov2eW d s β ρ φ x - β⁻¹ * φ x := by
    funext x; simp only [s8p_U, mov2eW, mov2eH]; ring
  have h1 : MemLp (fun x => Real.sqrt (ρ x) * s8p_U d s ρ φ x) 2 volume := by
    rw [e]; exact hW.sub (hphi.const_mul β⁻¹)
  have h2 := (memLp_two_iff_integrable_sq h1.aestronglyMeasurable).1 h1
  refine h2.congr (Filter.Eventually.of_forall fun x => ?_)
  have := hρ.psi_sq x
  show (Real.sqrt (ρ x) * s8p_U d s ρ φ x) ^ 2 = ρ x * s8p_U d s ρ φ x ^ 2
  rw [mul_pow, sq, this]

theorem s8p_U_mean (hρ : Mov2eRho d ρ) (φ : Euc d → ℝ) :
    ∫ x, s8p_U d s ρ φ x ∂(HRS.Whole.withDensityReal ρ) = s8p_Cc d s ρ φ := by
  rw [mov2e_integral_mu hρ]; rfl

theorem s8p_E_memLp (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : Mov2eRho d ρ) (hE : Mov2eEll d ρ)
    (β : ℝ) (φ : 𝓢R) : MemLp (s8p_E d s β ρ φ) 2 (HRS.Whole.withDensityReal ρ) := by
  haveI := mov2e_isProb hρ
  have h1 := ((s8p_f_memLp hρ φ).const_mul β⁻¹).add (s8p_U_memLp hd hs0 hsd hρ hE β φ)
  have h2 := h1.sub (memLp_const (s8p_Cc d s ρ φ))
  have e2 : s8p_E d s β ρ φ = ((fun x => β⁻¹ * (φ x / Real.sqrt (ρ x))) + s8p_U d s ρ φ) -
      fun _ => s8p_Cc d s ρ φ := by
    funext x; simp [s8p_E]
  rw [e2]; exact h2

theorem s8p_E_mean (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : Mov2eRho d ρ) (hE : Mov2eEll d ρ)
    (β : ℝ) (φ : 𝓢R) (hφc : ∫ x, Real.sqrt (ρ x) * φ x = 0) :
    ∫ x, s8p_E d s β ρ φ x ∂(HRS.Whole.withDensityReal ρ) = 0 := by
  haveI := mov2e_isProb hρ
  have hf := (s8p_f_memLp hρ φ).integrable one_le_two
  have hU := (s8p_U_memLp hd hs0 hsd hρ hE β φ).integrable one_le_two
  have e : (fun x => s8p_E d s β ρ φ x) = fun x =>
      (β⁻¹ * (φ x / Real.sqrt (ρ x)) + s8p_U d s ρ φ x) - s8p_Cc d s ρ φ := by
    funext x; simp [s8p_E]
  have I1 : Integrable (fun x => β⁻¹ * (φ x / Real.sqrt (ρ x)) + s8p_U d s ρ φ x)
      (HRS.Whole.withDensityReal ρ) := (hf.const_mul β⁻¹).add hU
  rw [e, integral_sub I1 (integrable_const _), integral_add (hf.const_mul β⁻¹) hU,
    integral_const_mul, s8p_f_mean hρ φ hφc, s8p_U_mean hρ, integral_const]
  simp

theorem s8p_Kop_f (hρ : Mov2eRho d ρ) (a : ℝ) (φ : 𝓢R) (x : Euc d) :
    HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ) (fun y => a * (φ y / Real.sqrt (ρ y))) x =
      a * s8p_U d s ρ φ x - a * s8p_Cc d s ρ φ := by
  haveI := mov2e_isProb hρ
  have hK : ∀ x, ∫ y, rieszKernel d s (x - y) * (a * (φ y / Real.sqrt (ρ y)))
      ∂(HRS.Whole.withDensityReal ρ) = a * s8p_U d s ρ φ x := by
    intro x
    have e1 : ∀ y, rieszKernel d s (x - y) * (a * (φ y / Real.sqrt (ρ y))) =
        a * (rieszKernel d s (x - y) * (φ y / Real.sqrt (ρ y))) := fun y => by ring
    simp_rw [e1]
    rw [integral_const_mul]
    congr 1
    have h2 := mov2eKt_eq hρ s (fun y => φ y / Real.sqrt (ρ y)) x
    unfold mov2eKt at h2
    rw [h2]
    unfold s8p_U HRS.Whole.convFun
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [mov2eH]
    rw [mov2e_rho_div hρ φ y]
  unfold HRS.Whole.Kop HRS.Whole.projMean HRS.Whole.pair
  simp only [hK]
  rw [integral_const_mul, s8p_U_mean hρ]

theorem s8p_response (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : Mov2eRho d ρ) (hE : Mov2eEll d ρ)
    {β : ℝ} (hβ : 0 < β) (φ : 𝓢R) (hφc : ∫ x, Real.sqrt (ρ x) * φ x = 0) :
    HRS.Whole.IsResponse (rieszKernel d s) (HRS.Whole.withDensityReal ρ) β (s8p_E d s β ρ φ)
      (fun y => β⁻¹ * (φ y / Real.sqrt (ρ y))) := by
  haveI := mov2e_isProb hρ
  refine ⟨⟨(s8p_f_memLp hρ φ).const_mul β⁻¹, ?_⟩, Filter.Eventually.of_forall fun x => ?_⟩
  · rw [integral_const_mul, s8p_f_mean hρ φ hφc, mul_zero]
  · rw [s8p_Kop_f hρ β⁻¹ φ x]
    unfold HRS.Whole.projMean HRS.Whole.pair
    rw [s8p_E_mean hd hs0 hsd hρ hE β φ hφc]
    unfold s8p_E
    field_simp
    ring

theorem s8p_responseInverse_eq {ν : MeasureTheory.Measure (Euc d)} [IsProbabilityMeasure ν] {g : Euc d → ℝ}
    {K : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν} (hK : S45.IsKData ν g K) {β : ℝ} (hβ : 0 < β) {ψ h : Euc d → ℝ}
    (hψ : MemLp ψ 2 ν) (hh : HRS.Whole.IsResponse g ν β ψ h) :
    HRS.Whole.responseInverse g ν β ψ =ᵐ[ν] h :=
  (S45.s45_responseInverse_ae hK hβ hψ).trans ((S45.s45_response_iff hK hβ hψ h).1 hh).symm

theorem s8p_responseInverse_E (hd : 1 ≤ d) (hs0 : 0 < s) (hsd : s < d) (hρ : Mov2eRho d ρ)
    (hE : Mov2eEll d ρ) {M : ℝ} (hM : ∀ x, ρ x ≤ M) {β : ℝ} (hβ : 0 < β) (φ : 𝓢R)
    (hφc : ∫ x, Real.sqrt (ρ x) * φ x = 0) :
    HRS.Whole.responseInverse (rieszKernel d s) (HRS.Whole.withDensityReal ρ) β (s8p_E d s β ρ φ)
      =ᵐ[HRS.Whole.withDensityReal ρ] fun y => β⁻¹ * (φ y / Real.sqrt (ρ y)) := by
  haveI := mov2e_isProb hρ
  obtain ⟨K, hK⟩ := S45.s45_kdata hd hs0.le hsd hρ.prob hM (L := 0) (fun h => absurd h hs0.ne')
  exact s8p_responseInverse_eq hK hβ (s8p_E_memLp hd hs0.le hsd hρ hE β φ)
    (s8p_response hd hs0.le hsd hρ hE hβ φ hφc)

end HRS.MS.Spec

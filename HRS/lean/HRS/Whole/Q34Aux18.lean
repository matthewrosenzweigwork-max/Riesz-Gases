import HRS.Whole.Q34Aux17

/-!
# Packet Q34, helper file 18: assembly of the susceptibility statement (S7.3, last part)
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric InnerProductSpace
open scoped ENNReal NNReal

namespace HRS.Whole.Q34

variable {d : ℕ} {s : ℝ} {ρ : Euc d → ℝ} {M : ℝ}

section Assembly

variable {ν : Measure (Euc d)}

theorem l2Inner_eq {u v : Euc d → ℝ} {U V : Lp ℝ 2 ν} (hu : u =ᵐ[ν] (U : Euc d → ℝ))
    (hv : v =ᵐ[ν] (V : Euc d → ℝ)) : l2Inner ν u v = inner ℝ U V := by
  rw [lp_inner]
  refine integral_congr_ae ?_
  filter_upwards [hu, hv] with x h1 h2
  rw [h1, h2]

theorem integral_sq_eq {u : Euc d → ℝ} {U : Lp ℝ 2 ν} (hu : u =ᵐ[ν] (U : Euc d → ℝ)) :
    ∫ x, u x ^ 2 ∂ν = ‖U‖ ^ 2 := by
  rw [lp_norm_sq]
  refine integral_congr_ae ?_
  filter_upwards [hu] with x h1
  rw [h1]

theorem l2Norm_eq {u : Euc d → ℝ} {U : Lp ℝ 2 ν} (hu : u =ᵐ[ν] (U : Euc d → ℝ)) :
    l2Norm ν u = ‖U‖ := by
  unfold l2Norm
  rw [integral_sq_eq hu, Real.sqrt_sq (norm_nonneg _)]

theorem kop_congr_ae (hs0 : s ≠ 0) {u u' : Euc d → ℝ} (h : u =ᵐ[ν] u') :
    Kop (rieszKernel d s) ν u = Kop (rieszKernel d s) ν u' := by
  rw [kop_eq hs0, kop_eq hs0, tk_congr_ae h]



theorem exists_class [IsProbabilityMeasure ν] {f : Euc d → ℝ} (hf : MemL2Zero ν f) :
    ∃ F : Lp ℝ 2 ν, f =ᵐ[ν] (F : Euc d → ℝ) ∧ Pc ν F = F := by
  refine ⟨hf.1.toLp f, (MemLp.coeFn_toLp hf.1).symm, ?_⟩
  have h0 : inner ℝ (one2 ν) (hf.1.toLp f) = 0 := by
    rw [inner_one2]
    exact (integral_congr_ae (MemLp.coeFn_toLp hf.1)).trans hf.2
  rw [Pc_apply, h0]; simp

end Assembly

section Main

variable [IsProbabilityMeasure (withDensityReal ρ)]

theorem kop_class (h : Q34Hyp d s ρ M) {f : Euc d → ℝ} {F : Lp ℝ 2 (withDensityReal ρ)}
    (hF : f =ᵐ[withDensityReal ρ] (F : Euc d → ℝ)) (hP : Pc (withDensityReal ρ) F = F) :
    Kop (rieszKernel d s) (withDensityReal ρ) f =ᵐ[withDensityReal ρ] (Kc h F : Euc d → ℝ) := by
  rw [kop_congr_ae h.hs0.ne' hF]
  exact (kc_ae h F hP).symm

theorem partA (h : Q34Hyp d s ρ M) {f : Euc d → ℝ} (hf : MemL2Zero (withDensityReal ρ) f) :
    MemL2Zero (withDensityReal ρ) (Kop (rieszKernel d s) (withDensityReal ρ) f) ∧
      l2Norm (withDensityReal ρ) (Kop (rieszKernel d s) (withDensityReal ρ) f) ≤
        Mg d s M * l2Norm (withDensityReal ρ) f := by
  obtain ⟨F, hF, hP⟩ := exists_class hf
  have hK := kop_class h hF hP
  refine ⟨⟨(Lp.memLp (Kc h F)).ae_eq hK.symm, ?_⟩, ?_⟩
  · rw [integral_congr_ae hK, ← inner_one2]
    exact inner_one2_Kc h F
  · rw [l2Norm_eq hK, l2Norm_eq hF]
    exact Kc_norm_le h F

theorem partB (h : Q34Hyp d s ρ M) {f g : Euc d → ℝ} (hf : MemL2Zero (withDensityReal ρ) f)
    (hg : MemL2Zero (withDensityReal ρ) g) :
    l2Inner (withDensityReal ρ) (Kop (rieszKernel d s) (withDensityReal ρ) f) g =
      l2Inner (withDensityReal ρ) f (Kop (rieszKernel d s) (withDensityReal ρ) g) := by
  obtain ⟨F, hF, hPF⟩ := exists_class hf
  obtain ⟨G, hG, hPG⟩ := exists_class hg
  rw [l2Inner_eq (kop_class h hF hPF) hG, l2Inner_eq hF (kop_class h hG hPG)]
  exact Kc_symm h F G

theorem partC (h : Q34Hyp d s ρ M) {f : Euc d → ℝ} (hf : MemL2Zero (withDensityReal ρ) f) :
    0 ≤ l2Inner (withDensityReal ρ) (Kop (rieszKernel d s) (withDensityReal ρ) f) f := by
  obtain ⟨F, hF, hPF⟩ := exists_class hf
  rw [l2Inner_eq (kop_class h hF hPF) hF]
  exact Kc_pos h F



theorem partD (h : Q34Hyp d s ρ M) {β : ℝ} (hβ : 0 < β) {f : Euc d → ℝ}
    (hf : MemL2Zero (withDensityReal ρ) f) :
    (∃ h', IsResponse (rieszKernel d s) (withDensityReal ρ) β f h') ∧
    (∀ h1 h2, IsResponse (rieszKernel d s) (withDensityReal ρ) β f h1 →
      IsResponse (rieszKernel d s) (withDensityReal ρ) β f h2 →
        h1 =ᵐ[withDensityReal ρ] h2) ∧
    (∫ x, f x ^ 2 ∂(withDensityReal ρ)) / (1 + β * Mg d s M) ≤
      l2Inner (withDensityReal ρ) f
        (responseInverse (rieszKernel d s) (withDensityReal ρ) β f) ∧
    l2Inner (withDensityReal ρ) f
        (responseInverse (rieszKernel d s) (withDensityReal ρ) β f) ≤
      ∫ x, f x ^ 2 ∂(withDensityReal ρ) ∧
    l2Norm (withDensityReal ρ) (responseInverse (rieszKernel d s) (withDensityReal ρ) β f) ≤
      l2Norm (withDensityReal ρ) f := by
  have hM0 : 0 ≤ M := (h.hρ.nonneg 0).trans (h.hM 0)
  have hMg0 := Mg_nonneg h.hd h.hsd hM0
  set ν := withDensityReal ρ with hν
  obtain ⟨F, hF, hPF⟩ := exists_class hf
  obtain ⟨Hh, hsol, huniq, hlow, hup, hnorm⟩ :=
    resolvent_exists (Kc h) (Kc_symm h) (Kc_pos h) hMg0 (Kc_norm_le h) hβ F
  have hPHh : Pc ν Hh = Hh := by
    have h1 := congrArg (Pc ν) hsol
    rw [map_add, map_smul, Pc_Kc, hPF] at h1
    have h2 : Pc ν Hh + β • Kc h Hh = Hh + β • Kc h Hh := h1.trans hsol.symm
    exact add_right_cancel h2
  have hpm : ∀ x, projMean ν f x = f x := by
    intro x
    simp only [projMean, pair, hf.2, sub_zero]
  have hresp : IsResponse (rieszKernel d s) ν β f (Hh : Euc d → ℝ) := by
    refine ⟨⟨Lp.memLp Hh, ?_⟩, ?_⟩
    · rw [← inner_one2]
      calc inner ℝ (one2 ν) Hh = inner ℝ (one2 ν) (Pc ν Hh) := by rw [hPHh]
        _ = 0 := inner_one2_Pc Hh
    · have hsol' : ((Hh + β • Kc h Hh : Lp ℝ 2 ν) : Euc d → ℝ) = (F : Euc d → ℝ) := by
        rw [hsol]
      filter_upwards [Lp.coeFn_add Hh (β • Kc h Hh), Lp.coeFn_smul β (Kc h Hh),
        kc_ae h Hh hPHh, hF] with x h1 h2 h3 h4
      have e1 := congrFun hsol' x
      rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, smul_eq_mul] at e1
      rw [hpm, h4, ← e1]
  have huniq' : ∀ h', IsResponse (rieszKernel d s) ν β f h' → h' =ᵐ[ν] (Hh : Euc d → ℝ) := by
    intro h' hh'
    set U' : Lp ℝ 2 ν := hh'.1.1.toLp h' with hU'
    have hU'ae : h' =ᵐ[ν] (U' : Euc d → ℝ) := (MemLp.coeFn_toLp hh'.1.1).symm
    have hPU' : Pc ν U' = U' := by
      have h0 : inner ℝ (one2 ν) U' = 0 := by
        rw [inner_one2]
        exact (integral_congr_ae hU'ae.symm).trans hh'.1.2
      rw [Pc_apply, h0]; simp
    have hKU' := kop_class h hU'ae hPU'
    have heq : U' + β • Kc h U' = F := by
      refine Lp.ext ?_
      filter_upwards [Lp.coeFn_add U' (β • Kc h U'), Lp.coeFn_smul β (Kc h U'), hU'ae, hKU',
        hh'.2, hF] with x h1 h2 h3 h4 h5 h6
      rw [h1, Pi.add_apply, h2, Pi.smul_apply, ← h3, ← h4, smul_eq_mul, h5, hpm, h6]
    have := huniq U' heq
    filter_upwards [hU'ae] with x hx
    rw [hx, this]
  have hex : ∃ h', IsResponse (rieszKernel d s) ν β f h' := ⟨_, hresp⟩
  have hR : responseInverse (rieszKernel d s) ν β f =ᵐ[ν] (Hh : Euc d → ℝ) := by
    unfold responseInverse
    rw [dif_pos hex]
    exact huniq' _ hex.choose_spec
  refine ⟨hex, fun h1 h2 hh1 hh2 => (huniq' h1 hh1).trans (huniq' h2 hh2).symm, ?_, ?_, ?_⟩
  · rw [l2Inner_eq hF hR, integral_sq_eq hF]
    exact hlow
  · rw [l2Inner_eq hF hR, integral_sq_eq hF]
    exact hup
  · rw [l2Norm_eq hR, l2Norm_eq hF]
    exact hnorm

end Main

end HRS.Whole.Q34

import HRS.MC.CepH3M1
import HRS.MC.CepH3H2

/-!
# Packet CEPH3, part PF: proof of `cep_H3_limit_semicontinuity`

Assembly of parts (a) (`h3h_entropy_liminf`), (b) (`h3m_fisher_liminf`) and (c) (`h3h_initial_limsup`).
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH3

open HRS HRS.MC.Cepa

section Final

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

lemma h3p_selectedLaw (σ₀ : Equiv.Perm (Fin N)) (Zl : ℝ → Ω → Ch N) {r : ℝ} (hr : 0 ≤ r) :
    selectedLaw P (fun s ω => fun i => Torus.mk (cep_unrank σ₀ (Zl (s : ℝ) ω) i)) r =
      P.map fun ω => h3d_Q σ₀ (Zl r ω) := by
  unfold selectedLaw
  show Measure.map (fun ω => fun i => Torus.mk (cep_unrank σ₀ (Zl ((Real.toNNReal r : ℝ≥0) : ℝ) ω) i)) P = _
  rw [Real.coe_toNNReal r hr]
  rfl

theorem cep_H3_limit_semicontinuity_proof [IsProbabilityMeasure P] [NeZero N] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {D : DynData 1} (hs : D.s = 0) (hβ : 0 < D.invβ) (hM : D.M = -(1 : Matrix (Fin 1) (Fin 1) ℝ))
    (hV : cep_IsC11 D.V) (σ₀ : Equiv.Perm (Fin N))
    {J : ℝ → Ch N → Ch N} (hJ : cep_Yosida 1 N J) {Φn : ℝ → Ch N → ℝ}
    (hΦ : ∀ n z, 0 < n → HasGradientAt (Φn n) (n • (z - J n z)) z)
    (hΦle : ∀ n z, 0 < n → z ∈ cep_Alcove N → Φn n z ≤ cep_chamberPot 1 N z)
    (hΦlim : ∀ z, z ∈ cep_Alcove N → Filter.Tendsto (fun n : ℕ => Φn n z) Filter.atTop (𝓝 (cep_chamberPot 1 N z)))
    {Ψ : Ch N → ℝ} {L : ℝ≥0} (hΨ : ContDiff ℝ 1 Ψ) (hΨL : LipschitzWith L (gradient Ψ))
    (hΨtot : ∀ (π : Equiv.Perm (Fin N)) (y : Fin N → Euc 1), cep_StrictlyOrdered π y →
      totalPotential D (fun i => Torus.mk (y i)) = cep_chamberPot 1 N (cep_toCh π y) + Ψ (cep_toCh π y))
    {z₀ : Ω → Ch N} (hz₀ : Measurable[ℱ 0] z₀) (hz₀A : ∀ ω, z₀ ω ∈ cep_Alcove N)
    {Z : ℕ → ℝ → Ω → Ch N}
    (hZ : ∀ n : ℕ, 1 ≤ n → cep_IsChamberSolution P ℱ W' (fun _ => σ₀) (Real.sqrt (2 * D.invβ))
      (fun z => -(gradient (fun w => Φn n w + Ψ w) z)) z₀ (Z n))
    {Zl : ℝ → Ω → Ch N}
    (hZl : ∀ T : ℝ, ∀ ε : ℝ, 0 < ε → Filter.Tendsto (fun n : ℕ =>
        P {ω | ε < ⨆ t : Set.Icc (0 : ℝ) T, ‖Z n t ω - Zl t ω‖}) Filter.atTop (𝓝 0))
    (hZlc : ∀ ω, Continuous fun t => Zl t ω)
    (hZlA : ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → Zl t ω ∈ closure (cep_Alcove N))
    (hZlnull : ∀ᵐ ω ∂P, ∀ T : ℝ, volume {s : ℝ | s ∈ Set.Icc 0 T ∧ Zl s ω ∉ cep_Alcove N} = 0) :
    ∀ t : ℝ, 0 ≤ t →
      gibbsEntropy D (selectedLaw P (fun s ω => fun i => Torus.mk (cep_unrank σ₀ (Zl (s : ℝ) ω) i)) t)
        ≤ Filter.liminf (fun n : ℕ => cep_cylEntropy D.invβ (fun w => Φn n w + Ψ w)
            (P.map fun ω => cep_reduce (Z n t ω))) Filter.atTop ∧
      (∫⁻ r in Set.Icc (0 : ℝ) t, fisherInfo D N
          (selectedLaw P (fun s ω => fun i => Torus.mk (cep_unrank σ₀ (Zl (s : ℝ) ω) i)) r))
        ≤ Filter.liminf (fun n : ℕ => ∫⁻ r in Set.Icc (0 : ℝ) t, cep_cylFisher D.invβ (fun w => Φn n w + Ψ w)
            (P.map fun ω => cep_reduce (Z n r ω))) Filter.atTop ∧
      Filter.limsup (fun n : ℕ => cep_cylEntropy D.invβ (fun w => Φn n w + Ψ w)
            (P.map fun ω => cep_reduce (z₀ ω))) Filter.atTop
        ≤ gibbsEntropy D (selectedLaw P (fun s ω => fun i => Torus.mk (cep_unrank σ₀ (Zl (s : ℝ) ω) i)) 0) := by
  intro t ht
  have hH : H3 N D.invβ J Φn Ψ L := ⟨hJ, hΦ, hΦle, hΦlim, hΨ, hΨL, hβ⟩
  have hZc : ∀ n, 1 ≤ n → ∀ ω, Continuous fun s => Z n s ω := fun n hn => (hZ n hn).1
  have hZm : ∀ n, 1 ≤ n → ∀ s, 0 ≤ s → Measurable (Z n s) := fun n hn s hs =>
    ((hZ n hn).2.1 s hs).mono (ℱ.le s) le_rfl
  have hconv : ∀ s, 0 ≤ s → ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => P {ω | ε ≤ ‖Z n s ω - Zl s ω‖}) atTop (𝓝 0) :=
    fun s hs => h3f_conv_prob hs hZc hZlc hZl
  have hZlm : ∀ s, 0 ≤ s → AEMeasurable (Zl s) P := fun s hs =>
    h3f_aemeasurable (fun n hn => hZm n hn s hs) (hconv s hs)
  have hZ0 : ∀ n, 1 ≤ n → ∀ᵐ ω ∂P, Z n 0 ω = z₀ ω := by
    intro n hn
    filter_upwards [(hZ n hn).2.2] with ω hω
    have := hω 0 le_rfl
    rw [this]
    have hn0 : cep_noise (fun _ : Ω => σ₀) W' 0 ω = 0 := by
      ext k
      simp [cep_noise, hW'.zero]
    simp [hn0]
  have hZl0 : ∀ᵐ ω ∂P, Zl 0 ω = z₀ ω := h3f_Zl_zero hZ0 (hconv 0 le_rfl)
  have hz₀m : Measurable z₀ := hz₀.mono (ℱ.le 0) le_rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [h3p_selectedLaw σ₀ Zl ht]
    exact h3h_entropy_liminf hH hΨtot σ₀ (Zn := fun n => Z n t) (fun n hn => hZm n hn t ht) (hZlm t ht)
      (hconv t ht)
  · calc (∫⁻ r in Set.Icc (0 : ℝ) t, fisherInfo D N
          (selectedLaw P (fun s ω => fun i => Torus.mk (cep_unrank σ₀ (Zl (s : ℝ) ω) i)) r))
        = ∫⁻ r in Set.Icc (0 : ℝ) t, fisherInfo D N (P.map fun ω => h3d_Q σ₀ (Zl r ω)) :=
          setLIntegral_congr_fun measurableSet_Icc fun r hr => by rw [h3p_selectedLaw σ₀ Zl hr.1]
      _ ≤ _ := h3m_fisher_liminf hH hΨtot σ₀ hZc hZm hZlc hZlA hconv ht
  · rw [h3p_selectedLaw σ₀ Zl le_rfl]
    exact h3h_initial_limsup hH hΨtot σ₀ hz₀m hz₀A hZl0

end Final

end HRS.MC.CepH3

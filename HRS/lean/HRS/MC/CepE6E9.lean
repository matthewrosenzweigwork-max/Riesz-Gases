import HRS.MC.CepE6E8

/-!
# Packet CEPE6E, file 9: deterministic glue

* `cepe6e_hA`: the antiderivatives `∫_0^t b_i` of the force converge uniformly on `[0,T]` to
  `A(t) = z0 + ∫_0^t F(Zl) + σ' N_t - Zl_t` (from the integral equations of the approximants).
* `cepe6e_normint_le`: `ofReal ∫_0^T ‖b‖ ≤ ∫⁻_{[0,T]} ofReal ∑_k |b_k|`.
* `cepe6e_glue`: a sequence of Itô identities with small martingale bounds along subsequences forces `A(T) = ∫_0^T ∇Φ(Zl)`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE6E

open HRS HRS.MC.Cepa HRS.MC.CepE6D

variable {N : ℕ}

theorem cepe6e_tuo_subseq {X : Type*} [PseudoMetricSpace X] {F : ℕ → ℝ → X} {f : ℝ → X} {S : Set ℝ}
    (h : TendstoUniformlyOn F f atTop S) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    TendstoUniformlyOn (fun j => F (φ j)) f atTop S := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  exact hφ.tendsto_atTop.eventually (h ε hε)

theorem cepe6e_hA {a : ℝ} {J : ℝ → Ch N → Ch N} {T : ℝ} (hT : 0 ≤ T) {nn : ℕ → ℝ} {Zs : ℕ → ℝ → Ch N}
    {Zl : ℝ → Ch N} (hZs : ∀ i, Continuous (Zs i)) (hZl : Continuous Zl) (hJ : cep_Yosida a N J)
    (hnn : ∀ i, 0 < nn i) {F : Ch N → Ch N} {L : ℝ≥0} (hF : LipschitzWith L F) {z0 : Ch N}
    {nz : ℝ → Ch N} {σ' : ℝ}
    (hsol : ∀ i, ∀ t : ℝ, 0 ≤ t → Zs i t = z0 + (∫ s in (0 : ℝ)..t, (-(bF J nn Zs i s) + F (Zs i s))) +
      σ' • nz t)
    (hunif : TendstoUniformlyOn Zs Zl atTop (Icc 0 T)) :
    TendstoUniformlyOn (fun i t => ∫ s in (0 : ℝ)..t, bF J nn Zs i s)
      (fun t => z0 + (∫ s in (0 : ℝ)..t, F (Zl s)) + σ' • nz t - Zl t) atTop (Icc 0 T) := by
  have hbc : ∀ i, Continuous (bF J nn Zs i) := fun i => (hJ.lip (nn i) (hnn i)).continuous.comp (hZs i)
  have hFc : Continuous F := hF.continuous
  have hid : ∀ i, ∀ t, 0 ≤ t → ∫ s in (0 : ℝ)..t, bF J nn Zs i s =
      (∫ s in (0 : ℝ)..t, F (Zs i s)) + z0 + σ' • nz t - Zs i t := by
    intro i t ht
    have h1 := hsol i t ht
    rw [intervalIntegral.integral_add (f := fun s => -(bF J nn Zs i s)) (g := fun s => F (Zs i s))
      ((hbc i).neg.intervalIntegrable 0 t) ((hFc.comp (hZs i)).intervalIntegrable 0 t),
      intervalIntegral.integral_neg] at h1
    rw [h1]; abel
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hLT : 0 ≤ (L : ℝ) * T := mul_nonneg L.2 hT
  have hδ : 0 < ε / ((L : ℝ) * T + 2) := by positivity
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hunif _ hδ] with i hi t ht
  set δ := ε / ((L : ℝ) * T + 2) with hδdef
  have h2 : ∀ s ∈ Icc (0 : ℝ) T, ‖F (Zl s) - F (Zs i s)‖ ≤ (L : ℝ) * δ := by
    intro s hs
    rw [← dist_eq_norm]
    exact (hF.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left (hi s hs).le L.2)
  have h3 : ‖∫ s in (0 : ℝ)..t, (F (Zl s) - F (Zs i s))‖ ≤ (L : ℝ) * δ * T := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
      (f := fun s => F (Zl s) - F (Zs i s)) (C := (L : ℝ) * δ) (fun s hs => by
        rw [uIoc_of_le ht.1] at hs
        exact h2 s ⟨hs.1.le, hs.2.trans ht.2⟩)
    refine this.trans ?_
    rw [sub_zero, abs_of_nonneg ht.1]
    exact mul_le_mul_of_nonneg_left ht.2 (by positivity)
  rw [dist_eq_norm, hid i t ht.1]
  have e : z0 + (∫ s in (0 : ℝ)..t, F (Zl s)) + σ' • nz t - Zl t -
      ((∫ s in (0 : ℝ)..t, F (Zs i s)) + z0 + σ' • nz t - Zs i t) =
      (∫ s in (0 : ℝ)..t, (F (Zl s) - F (Zs i s))) - (Zl t - Zs i t) := by
    rw [intervalIntegral.integral_sub (f := fun s => F (Zl s)) (g := fun s => F (Zs i s))
      ((hFc.comp hZl).intervalIntegrable 0 t) ((hFc.comp (hZs i)).intervalIntegrable 0 t)]
    abel
  rw [e]
  have h4 : ‖Zl t - Zs i t‖ < δ := by rw [← dist_eq_norm]; exact hi t ht
  calc ‖(∫ s in (0 : ℝ)..t, (F (Zl s) - F (Zs i s))) - (Zl t - Zs i t)‖
      ≤ ‖∫ s in (0 : ℝ)..t, (F (Zl s) - F (Zs i s))‖ + ‖Zl t - Zs i t‖ := norm_sub_le _ _
    _ < (L : ℝ) * δ * T + δ := by linarith
    _ ≤ ε := by
      have : (L : ℝ) * δ * T + δ = δ * ((L : ℝ) * T + 1) := by ring
      rw [this, hδdef, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith

theorem cepe6e_normint_le {b : ℝ → Ch N} (hb : Continuous b) {T : ℝ} (hT : 0 ≤ T) :
    ENNReal.ofReal (∫ s in (0 : ℝ)..T, ‖b s‖) ≤
      ∫⁻ s in Icc (0 : ℝ) T, ENNReal.ofReal (∑ k : Fin N, |b s k|) := by
  rw [intervalIntegral.integral_of_le hT, ← integral_Icc_eq_integral_Ioc,
    ofReal_integral_eq_lintegral_ofReal]
  · exact lintegral_mono fun s => ENNReal.ofReal_le_ofReal (HRS.MC.CepE6A.e6a_norm_le_sum _)
  · exact hb.norm.continuousOn.integrableOn_Icc
  · exact Eventually.of_forall fun s => norm_nonneg _

theorem cepe6e_glue {a : ℝ} {J : ℝ → Ch N → Ch N} {T : ℝ} {nn : ℕ → ℝ} {Zs : ℕ → ℝ → Ch N}
    {Zl : ℝ → Ch N} (D : Det a J T nn Zs Zl) (hN : 1 ≤ N) {A : ℝ → Ch N}
    (hA : TendstoUniformlyOn (fun i t => ∫ s in (0 : ℝ)..t, bF J nn Zs i s) A atTop (Icc 0 T))
    {σ' : ℝ} {z0 : Ch N} (hz0 : z0 ∈ cep_Alcove N) {F : Ch N → Ch N} (hF : Continuous F)
    (hinv : IntegrableOn (fun s => ∑ k : Fin N, ∑ l : Fin N,
      (if k < l then 1 / min (Zl s l - Zl s k) (1 - (Zl s l - Zl s k)) else 0)) (Icc 0 T))
    {ε : ℕ → ℝ} (hε0 : ∀ k, 0 < ε k) (hε1 : ∀ k, ε k ≤ 1 / 8) (hεlim : Tendsto ε atTop (𝓝 0))
    {M : ℕ → ℕ → ℝ}
    (hIto : ∀ k i, ∫ s in (0 : ℝ)..T, ⟪vv (ε k) (Zs i s), bF J nn Zs i s⟫ =
      gg (ε k) z0 - gg (ε k) (Zs i T) + (∫ s in (0 : ℝ)..T, ⟪vv (ε k) (Zs i s), F (Zs i s)⟫) +
        σ' ^ 2 * (∫ s in (0 : ℝ)..T, lap2 (ε k) (Zs i s)) + M k i)
    {K B : ℕ → ℝ} (hB : Tendsto B atTop (𝓝 0))
    (hsel : ∀ᶠ k in atTop, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ j, (∫ s in (0 : ℝ)..T, ‖bF J nn Zs (φ j) s‖ ≤ K k) ∧ |M k (φ j)| ≤ B k) :
    A T = ∫ s in (0 : ℝ)..T, gradient (cep_chamberPot a N) (Zl s) := by
  set Dt : ℕ → ℝ := fun l => (N : ℝ) ^ 2 * ε l + |∫ s in (0 : ℝ)..T, ⟪vv (ε l) (Zl s), F (Zl s)⟫| +
        σ' ^ 2 * |∫ s in (0 : ℝ)..T, lap2 (ε l) (Zl s)| +
        ∫ s in (0 : ℝ)..T, |⟪vv (ε l) (Zl s), gradient (cep_chamberPot a N) (Zl s)⟫| with hDt
  have hDtlim : Tendsto Dt atTop (𝓝 0) :=
    cepe6e_Dterms_tendsto D.hT D.hZl hF σ' D.hnull D.hint hinv hε0 hε1 hεlim
  have hlim : Tendsto (fun k => Dt k + B k) atTop (𝓝 0) := by simpa using hDtlim.add hB
  have hbd : ∀ᶠ k in atTop, (1 / 2) * ‖A T - ∫ s in (0 : ℝ)..T, gradient (cep_chamberPot a N) (Zl s)‖ ≤
      Dt k + B k := by
    filter_upwards [hsel] with k hk
    obtain ⟨φ, hφ, hφk⟩ := hk
    have Dφ : Det a J T (fun j => nn (φ j)) (fun j => Zs (φ j)) Zl :=
      ⟨D.ha, D.hJ, D.hT, fun j => D.hnn _, D.hnn_top.comp hφ.tendsto_atTop, fun j => D.hZs _, D.hZl,
        D.hcl, D.hnull, D.hint,
        cepe6e_tuo_subseq D.hunif hφ⟩
    have hAφ : TendstoUniformlyOn
        (fun j t => ∫ s in (0 : ℝ)..t, bF J (fun j => nn (φ j)) (fun j => Zs (φ j)) j s) A atTop
        (Icc 0 T) :=
      cepe6e_tuo_subseq hA hφ
    have := cepe6e_det_final Dφ hN hAφ (K := K k) (Eventually.of_forall fun j => (hφk j).1)
      (hε0 k) (hε1 k) hz0 hF (M := fun j => M k (φ j)) (B := B k)
      (Eventually.of_forall fun j => (hφk j).2) (fun j => hIto k (φ j))
    simp only [hDt]
    linarith
  have h0 : (1 / 2) * ‖A T - ∫ s in (0 : ℝ)..T, gradient (cep_chamberPot a N) (Zl s)‖ ≤ 0 :=
    ge_of_tendsto hlim hbd
  have : ‖A T - ∫ s in (0 : ℝ)..T, gradient (cep_chamberPot a N) (Zl s)‖ = 0 :=
    le_antisymm (by linarith) (norm_nonneg _)
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

end HRS.MC.CepE6E

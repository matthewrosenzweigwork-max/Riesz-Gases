import HRS.Sections.ScrnAux43

/-!
# Packet SCRN, part 44: the uniform bound for `ℓ ≤ 1`

`scrn_instance`: for fixed tests and fixed commutator constants `(C₀, C_q)` there is a constant `C` such that
for every `ℓ ∈ (0,1]`, every flow, and all times `t_a ≥ 0`,
`smoothDist 3 (law Z) N(0, mesoCov) ≤ C [N^{-1/2}ℓ^{-d/2} + √N o_N ℓ^{-d/2-max(q,2)} + ... + ℓ + |b_N - b|]`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS

open HRS.Main.A8P PDE

variable {d : ℕ}

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

lemma scrn_comb3 {a KL KH T3 T4 : ℝ} (ha : 0 ≤ a) (hL : 0 ≤ KL) (hH : 0 ≤ KH) (h3 : 0 ≤ T3)
    (h4 : 0 ≤ T4) : (1 / 2) * (a * (KL * T3 + KH * T4)) ≤ (1 / 2) * (a * (KL + KH)) * (T3 + T4) := by
  have h : 0 ≤ KL * T4 + KH * T3 := by positivity
  have e : (KL + KH) * (T3 + T4) = KL * T3 + KH * T4 + (KL * T4 + KH * T3) := by ring
  have : a * (KL * T3 + KH * T4) ≤ a * ((KL + KH) * (T3 + T4)) :=
    mul_le_mul_of_nonneg_left (by rw [e]; linarith) ha
  nlinarith

lemma scrn_comb_final {C1 C2 C3 C4 T1 T2 T3 T4 l T5 : ℝ} (h1 : 0 ≤ C1) (h2 : 0 ≤ C2) (h3 : 0 ≤ C3)
    (h4 : 0 ≤ C4) (t1 : 0 ≤ T1) (t2 : 0 ≤ T2) (t3 : 0 ≤ T3) (t4 : 0 ≤ T4) (hl : 0 ≤ l)
    (t5 : 0 ≤ T5) :
    C2 * T2 + C1 * T1 + C3 * (T3 + T4) + C4 * (l + T5) ≤
      (C1 + C2 + C3 + C4) * (T1 + T2 + T3 + T4 + l + T5) := by
  nlinarith [mul_nonneg h1 t2, mul_nonneg h1 t3, mul_nonneg h1 t4, mul_nonneg h1 hl,
    mul_nonneg h1 t5, mul_nonneg h2 t1, mul_nonneg h2 t3, mul_nonneg h2 t4, mul_nonneg h2 hl,
    mul_nonneg h2 t5, mul_nonneg h3 t1, mul_nonneg h3 t2, mul_nonneg h3 hl, mul_nonneg h3 t5,
    mul_nonneg h4 t1, mul_nonneg h4 t2, mul_nonneg h4 t3, mul_nonneg h4 t4]

set_option maxHeartbeats 1600000 in
theorem scrn_instance (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {p : ℕ} (φ : Fin p → Euc d → ℝ)
    (hφ : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (φ a) ∧ HasCompactSupport (φ a)) (x₀ : Euc d) {bm bp : ℝ}
    (hbm : 0 < bm) (hbmp : bm ≤ bp) {C₀ Cq : ℝ} (hC₀ : 0 ≤ C₀) (hcom : A8CommSpec d s C₀ Cq)
    (hCq : 0 ≤ Cq) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N : ℕ}, 2 ≤ N → ∀ {β : ℝ} (hβ : 0 < β) {ℓ b : ℝ}, 0 < ℓ → ℓ ≤ 1 →
      β * ℓ ^ ((d : ℝ) - s) ∈ Set.Icc bm bp → b ∈ Set.Icc bm bp →
      ∀ {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
        {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N},
        ScrnFlow d hs0 hsd β hβ N P X₀ W X → ∀ t : Fin p → ℝ, (∀ a, 0 ≤ t a) →
        smoothDist 3
            (law P fun ω => (WithLp.toLp 2 fun a =>
              linCoord (volume : Measure (Torus d)) (mesoTest d ℓ x₀ (φ a))
                (X (ℓ ^ (2 - ((d : ℝ) - s)) * t a).toNNReal ω) : EuclideanSpace ℝ (Fin p)))
            (ProbabilityTheory.multivariateGaussian 0 (mesoCovMatrix d s b t φ)) ≤
          C * ((N : ℝ) ^ (-(1 : ℝ) / 2) * ℓ ^ (-(d : ℝ) / 2) +
            Real.sqrt N * oN d s C₀ N * ℓ ^ (-(d : ℝ) / 2 - max ((d : ℝ) - s) 2) +
            (N : ℝ) ^ (-(1 : ℝ) / d) * ℓ ^ (-(d : ℝ) - 3 + min ((d : ℝ) - s) 2) +
            Real.sqrt (oN d s C₀ N) *
              ℓ ^ (-((d : ℝ) + ((d : ℝ) - s)) / 2 - 2 + min ((d : ℝ) - s) 2) +
            ℓ + |β * ℓ ^ ((d : ℝ) - s) - b|) := by
  have hex : ∀ a, ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ 1 → ∀ (g : Torus d → ℝ) (θ : ℝ),
      ScrnDecay (mesoTest d ℓ x₀ (φ a)) g θ → ScrnGB d s ℓ θ g C :=
    fun a => scrn_exists_GB hd hs0 hsd x₀ (hφ a).1 (hφ a).2
  choose Ca hCa0 hCa using hex
  set CG : ℝ := ∑ a, Ca a with hCG
  have hCG0 : 0 ≤ CG := Finset.sum_nonneg fun a _ => hCa0 a
  have hCaCG : ∀ a, Ca a ≤ CG := fun a =>
    Finset.single_le_sum (f := Ca) (fun b _ => hCa0 b) (Finset.mem_univ a)
  obtain ⟨Cg, hCg0, hCg⟩ := scrn_Q_gauss hd hs0 hsd φ hφ x₀ hbm
  have hbp : 0 < bp := hbm.trans_le hbmp
  have hc1 : 0 < min (rieszConst d s) bp⁻¹ :=
    lt_min (rieszConst_pos hd hs0 hsd) (inv_pos.2 hbp)
  set c1 : ℝ := min (rieszConst d s) bp⁻¹ with hc1def
  set KH : ℝ := 2 * d * 2 ^ (3 * (((d : ℝ) - s) / 2) / 2) * CG ^ 2 with hKH
  set Clin : ℝ := (1 + Real.sqrt 3) / 6 * (2 * (p : ℝ) ^ 2 * CG ^ 3) with hClin
  set Crem : ℝ := p * (Cq * CG / (2 * c1)) with hCrem
  set Ccov : ℝ := (1 / 2) * ((p : ℝ) ^ 2 * (2 * Cq / (bm * c1)) * (2 * d * CG ^ 2 + KH)) with hCcov
  have hdR : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hKH0 : 0 ≤ KH := by positivity
  have hClin0 : 0 ≤ Clin := by positivity
  have hCrem0 : 0 ≤ Crem := by positivity
  have hCcov0 : 0 ≤ Ccov := by positivity
  refine ⟨Clin + Crem + Ccov + Cg, by positivity, ?_⟩
  intro N hN β hβ ℓ b hℓ hℓ1 hβb hb Ω mΩ P _ X₀ W X hfl t ht
  set ts : Fin p → ℝ := fun a => ℓ ^ (2 - ((d : ℝ) - s)) * t a with hts
  have hts0 : ∀ a, 0 ≤ ts a := fun a => mul_nonneg (Real.rpow_nonneg hℓ.le _) (ht a)
  -- the transported tests
  have hfex : ∀ a, ∃ f : ℝ → Torus d → ℝ,
      ((ts a = 0 ∧ f = fun _ => mesoTest d ℓ x₀ (φ a)) ∨
        (0 < ts a ∧ IsClassicalAdjointSolution (mfData d s hs0 hsd (fun _ => 0) β hβ)
          (fun _ _ => (1 : ℝ)) (ts a) (mesoTest d ℓ x₀ (φ a)) f)) ∧
      ∀ r ∈ Set.Icc 0 (ts a), ∀ k : Lattice d,
        coeffOf (f r) k = ((Real.exp (-(ts a - r) * scrnLam d s β⁻¹ k) : ℝ) : ℂ) *
          coeffOf (mesoTest d ℓ x₀ (φ a)) k :=
    fun a => scrn_f_exists hd hs0 hsd hβ hℓ x₀ (hφ a).1 (hφ a).2 (hts0 a)
  choose f hfcases hfcoeff using hfex
  have htr : ScrnTr d hs0 hsd hβ ℓ (scrnLamS d s bp ℓ) CG ts
      (fun a => mesoTest d ℓ x₀ (φ a)) f := by
    refine ⟨hts0, fun a => isCk_mesoTest hℓ x₀ (hφ a).1 (hφ a).2 2 (by
      have h : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 le_top
      exact h), hfcases, hfcoeff, fun a r hr => ?_⟩
    have hdec := scrn_f_decay hd hs0 hsd hβ hℓ hbp hβb.2 x₀ (hφ a).1 (hφ a).2 (hts0 a) (hfcases a)
      (hfcoeff a) r hr
    exact (hCa a ℓ hℓ hℓ1 (f a r) _ hdec).mono hℓ (Real.exp_pos _).le (hCaCG a)
  have hprob := scrn_prob_bound hd hs0 hsd β hβ hN hfl hC₀ hcom hCq hbm hbp hℓ hCG0 hβb.1 htr
  have hTm0 : 0 < ∑ a, ts a + 1 := by
    have : 0 ≤ ∑ a, ts a := Finset.sum_nonneg fun a _ => hts0 a
    linarith
  have hTmge : ∀ a, ts a ≤ ∑ a, ts a + 1 := fun a => by
    have : ts a ≤ ∑ b, ts b := Finset.single_le_sum (fun b _ => hts0 b) (Finset.mem_univ a)
    linarith
  have hgauss := hCg hβ hℓ hℓ1 hβb.1 hb.1 t ht (T := ∑ a, ts a + 1) hTmge f htr.coeff htr.f2
    htr.fcont htr.c12
  refine (smoothDist_triangle 3 _ (multivariateGaussian 0
    (scrnQ f ts (∑ a, ts a + 1) β⁻¹)) _).trans ?_
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hsq : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  have hN12 : (N : ℝ) ^ (-(1 : ℝ) / 2) = (Real.sqrt N)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hNpos.le]; congr 1; ring
  have hexp2 : ℓ ^ (-((d : ℝ) / 2) - 2 - max ((d : ℝ) - s - 2) 0) =
      ℓ ^ (-(d : ℝ) / 2 - max ((d : ℝ) - s) 2) := by
    congr 1
    have := scrn_max_q ((d : ℝ) - s)
    rw [neg_div]; linarith
  have hexp1 : ℓ ^ (-((d : ℝ) / 2)) = ℓ ^ (-(d : ℝ) / 2) := by rw [neg_div]
  have hoN : 0 ≤ oN d s C₀ N := scrn_oN_nonneg hC₀ (show 1 ≤ N by omega)
  set T1 : ℝ := (N : ℝ) ^ (-(1 : ℝ) / 2) * ℓ ^ (-(d : ℝ) / 2) with hT1
  set T2 : ℝ := Real.sqrt N * oN d s C₀ N * ℓ ^ (-(d : ℝ) / 2 - max ((d : ℝ) - s) 2) with hT2
  set T3 : ℝ := (N : ℝ) ^ (-(1 : ℝ) / d) * ℓ ^ (-(d : ℝ) - 3 + min ((d : ℝ) - s) 2) with hT3
  set T4 : ℝ := Real.sqrt (oN d s C₀ N) *
    ℓ ^ (-((d : ℝ) + ((d : ℝ) - s)) / 2 - 2 + min ((d : ℝ) - s) 2) with hT4
  set T5 : ℝ := |β * ℓ ^ ((d : ℝ) - s) - b| with hT5
  have hT10 : 0 ≤ T1 := by positivity
  have hT20 : 0 ≤ T2 := by positivity
  have hT30 : 0 ≤ T3 := by positivity
  have hT40 : 0 ≤ T4 := by positivity
  have hT50 : 0 ≤ T5 := abs_nonneg _
  have e1 : p * (Cq * CG / (2 * c1)) *
      (Real.sqrt N * oN d s C₀ N * ℓ ^ (-((d : ℝ) / 2) - 2 - max ((d : ℝ) - s - 2) 0)) = Crem * T2 := by
    rw [hexp2, hCrem, hT2]
  have e2 : (1 + Real.sqrt 3) / (6 * Real.sqrt N) *
      (2 * p * (CG * ℓ ^ (-((d : ℝ) / 2))) * (p * CG ^ 2)) = Clin * T1 := by
    rw [hexp1, hT1, hN12, hClin]
    field_simp
  have e3 : (1 / 2) * ((p : ℝ) ^ 2 * (2 * Cq / (bm * c1)) *
      ((2 * d * CG ^ 2) * T3 + KH * T4)) ≤ Ccov * (T3 + T4) := by
    have := scrn_comb3 (a := (p : ℝ) ^ 2 * (2 * Cq / (bm * c1))) (KL := 2 * d * CG ^ 2) (KH := KH)
      (T3 := T3) (T4 := T4) (by positivity) (by positivity) hKH0 hT30 hT40
    rw [hCcov]
    linarith
  rw [e1, e2] at hprob
  have hprob' : smoothDist 3 (law P (scrnZ (fun a => mesoTest d ℓ x₀ (φ a)) ts X))
      (multivariateGaussian 0 (scrnQ f ts (∑ a, ts a + 1) β⁻¹)) ≤
      Crem * T2 + Clin * T1 + Ccov * (T3 + T4) := hprob.trans (by linarith)
  have hgauss' : smoothDist 3 (multivariateGaussian 0 (scrnQ f ts (∑ a, ts a + 1) β⁻¹))
      (multivariateGaussian 0 (mesoCovMatrix d s b t φ)) ≤ Cg * (ℓ + T5) := hgauss
  have hfin := scrn_comb_final hClin0 hCrem0 hCcov0 hCg0 hT10 hT20 hT30 hT40 hℓ.le hT50
  exact (add_le_add hprob' hgauss').trans hfin

end HRS

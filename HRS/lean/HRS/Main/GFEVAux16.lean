import HRS.Main.GFEVAux15

/-!
# Packet GFEVG, part 16: the Duhamel formula `⟨z, U^{u,t}φ - U^{u',t}φ⟩ = ∫_u^{u'} ⟨z, 𝓛_s U^{s,t}φ⟩ ds`
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.GF

open HRS HRS.PDE HRS.PDE.ET HRS.Uniform HRS.Uniform.Q54 HRS.Uniform.Q48b

variable {d : ℕ} {s : ℝ} {γ : ℕ} {R : Regime} {VB Λ : ℝ} {D : DynData d} {T : ℝ} {ρ : ℝ → Torus d → ℝ}

open Classical in
/-- `funRealCoeff` as a real-linear functional of the complex coefficient. -/
def gfevRc (k : NonzeroLattice d) : ℂ →L[ℝ] ℝ :=
  if Lattice.IsPosHalf k.1 then Real.sqrt 2 • Complex.reCLM else (-Real.sqrt 2) • Complex.imCLM

theorem gfev_funRealCoeff_eq_rc (φ : Torus d → ℝ) (hφ : Integrable φ) (k : NonzeroLattice d) :
    Torus.funRealCoeff φ k = gfevRc k (coeffOf φ k.1) := by
  have h := Torus.integral_mode_mul_real hφ k.1
  rw [← ClassicalAux.coeffOf_apply] at h
  have e1 : (coeffOf φ k.1).re = Torus.cosCoeff φ k.1 := by rw [h]; simp
  have e2 : (coeffOf φ k.1).im = -Torus.sinCoeff φ k.1 := by rw [h]; simp
  rw [Torus.funRealCoeff_eq]
  unfold gfevRc
  split_ifs
  · simp [e1]
  · simp [e2]

theorem GFPde.duhamel (h : GFPde d s γ R VB Λ D T ρ) (l : ℝ)
    (hq : QuasiAt (γ + 2) (UpF D (gfevMu T ρ)) (γ : ℝ) l) {φ : Torus d → ℝ} (hφ : Dom (γ + 2) φ)
    {t u u' : ℝ} (hu : 0 ≤ u) (huu' : u ≤ u') (hu't : u' ≤ t) (z : NegSobolev d ((γ : ℝ) - 2)) :
    NegSobolev.eval z (UpF D (gfevMu T ρ) u t φ) - NegSobolev.eval z (UpF D (gfevMu T ρ) u' t φ) =
      ∫ r in u..u', NegSobolev.eval z (gfevL D (gfevMu T ρ r) (UpF D (gfevMu T ρ) r t φ)) := by
  have hcore := h.core
  have hγ2 : (2 : ℝ) ≤ γ := by have := h.hγ5; exact_mod_cast (by omega : 2 ≤ γ)
  by_cases hE : u = u'
  · subst hE; simp
  have hlt : u < u' := lt_of_le_of_ne huu' hE
  have ht : 0 < t := by linarith
  obtain ⟨F, hsol, hlink⟩ := h.forward_link hφ ht
  obtain ⟨Bμ, BV, hBμ, hBV, hG⟩ := h.genHyp
  have hK : (d : ℝ) + |(γ : ℝ) - 2| + 4 ≤ ((γ + 2 * d + 11 : ℕ) : ℝ) := by
    rw [abs_of_nonneg (by linarith)]; push_cast; linarith
  obtain ⟨C, hC, hfacts⟩ := h.gen_facts (K := ((γ + 2 * d + 11 : ℕ) : ℝ)) (MB := 1) (Bμ := Bμ) (BV := BV)
    zero_le_one hBμ hBV hK
  set μ' := gfevMu T ρ with hμ'
  have hψD : ∀ r, 0 ≤ r → r ≤ t → Dom (γ + 2) (UpF D μ' r t φ) := fun r hr hrt =>
    hcore.dom r t hr hrt φ hφ
  have hgc : ∀ r, 0 ≤ r → r ≤ t → coeffOf (gfevL D (μ' r) (UpF D μ' r t φ)) =
      forwardGen D (μ' r) (F (t - r)) := by
    intro r hr hrt
    have h1 := (hfacts _ (h.contMu r) (hG r) _ (hψD r hr hrt)).1
    have h2 := hlink (t - r) ⟨by linarith, by linarith⟩
    rw [show t - (t - r) = r by ring] at h2
    rw [h1, h2]
  -- integrability of the coefficient integrands
  have hI : ∀ k : Lattice d, IntervalIntegrable (fun σ => forwardGen D (μ' (t - σ)) (F σ) k) volume 0 t := by
    intro k
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht.le]
    exact hsol.integrable k
  have hIc : ∀ (k : Lattice d) (a b : ℝ), 0 ≤ a → a ≤ b → b ≤ t →
      IntervalIntegrable (fun σ => forwardGen D (μ' (t - σ)) (F σ) k) volume a b := by
    intro k a b ha hab hb
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact (hsol.integrable k).mono_set (Set.Icc_subset_Icc ha hb)
  have hII : ∀ (L : ℂ →L[ℝ] ℝ) (k : Lattice d) (a b : ℝ), 0 ≤ a → a ≤ b → b ≤ t →
      IntervalIntegrable (fun σ => L (forwardGen D (μ' (t - σ)) (F σ) k)) volume a b := by
    intro L k a b ha hab hb
    have := hIc k a b ha hab hb
    rw [intervalIntegrable_iff] at this ⊢
    exact L.integrable_comp this
  -- the coefficient identity
  have hcont : ∀ r, 0 ≤ r → r ≤ t → Integrable (UpF D μ' r t φ) := fun r hr hrt =>
    ClassicalAux.integrable_of_continuous (hψD r hr hrt).1
  have hlinkc : ∀ r, 0 ≤ r → r ≤ t → coeffOf (UpF D μ' r t φ) = F (t - r) := by
    intro r hr hrt
    have := hlink (t - r) ⟨by linarith, by linarith⟩
    rwa [show t - (t - r) = r by ring] at this
  have hgrc : ∀ (k : NonzeroLattice d) r, 0 ≤ r → r ≤ t →
      Torus.funRealCoeff (gfevL D (μ' r) (UpF D μ' r t φ)) k =
        gfevRc k (forwardGen D (μ' (t - (t - r))) (F (t - r)) k.1) := by
    intro k r hr hrt
    have hgi : Integrable (gfevL D (μ' r) (UpF D μ' r t φ)) :=
      ClassicalAux.integrable_of_continuous (hfacts _ (h.contMu r) (hG r) _ (hψD r hr hrt)).2.1
    rw [gfev_funRealCoeff_eq_rc _ hgi, hgc r hr hrt, show t - (t - r) = r by ring]
  have hcoef : ∀ (k : NonzeroLattice d) {a b : ℝ}, 0 ≤ a → a ≤ b → b ≤ t →
      Torus.funRealCoeff (UpF D μ' a t φ) k - Torus.funRealCoeff (UpF D μ' b t φ) k =
        ∫ r in a..b, Torus.funRealCoeff (gfevL D (μ' r) (UpF D μ' r t φ)) k := by
    intro k a b ha hab hb
    rw [gfev_funRealCoeff_eq_rc _ (hcont a ha (hab.trans hb)), gfev_funRealCoeff_eq_rc _ (hcont b (ha.trans hab) hb),
      hlinkc a ha (hab.trans hb), hlinkc b (ha.trans hab) hb, ← map_sub,
      gfev_forward_increment hsol k.1 (by linarith) (by linarith) (by linarith),
      ← (gfevRc k).intervalIntegral_comp_comm (hIc k.1 (t - b) (t - a) (by linarith) (by linarith) (by linarith)),
      ← intervalIntegral.integral_comp_sub_left (fun σ => gfevRc k (forwardGen D (μ' (t - σ)) (F σ) k.1)) t]
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [Set.uIcc_of_le hab] at hr
    exact (hgrc k r (by linarith [hr.1]) (by linarith [hr.2])).symm
  -- the bound
  have hν0 : 0 ≤ 2 * D.invβ ^ 2 + C := by positivity
  set B : ℝ := Real.sqrt (2 * D.invβ ^ 2 + C) * (Real.exp (|l| * t) * sobolevNorm (γ : ℝ) φ) with hB
  have hg : ∀ r ∈ Set.Icc u u', MemSobolev ((γ : ℝ) - 2) (gfevL D (μ' r) (UpF D μ' r t φ)) ∧
      sobolevNorm ((γ : ℝ) - 2) (gfevL D (μ' r) (UpF D μ' r t φ)) ≤ B := by
    intro r hr
    have hr0 : 0 ≤ r := hu.trans hr.1
    have hrt : r ≤ t := hr.2.trans hu't
    obtain ⟨-, -, hm, hn⟩ := hfacts _ (h.contMu r) (hG r) _ (hψD r hr0 hrt)
    refine ⟨hm, ?_⟩
    obtain ⟨-, hqn⟩ := hq r t hr0 hrt φ hφ
    have h1 : sobolevNorm (γ : ℝ) (UpF D μ' r t φ) ≤ Real.exp (|l| * t) * sobolevNorm (γ : ℝ) φ :=
      hqn.trans (mul_le_mul_of_nonneg_right (gfev_exp_le l (by linarith) (by linarith)) (Real.sqrt_nonneg _))
    have hB0 : 0 ≤ B := mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _))
    refine le_of_sq_le_sq ?_ hB0
    calc sobolevNorm ((γ : ℝ) - 2) (gfevL D (μ' r) (UpF D μ' r t φ)) ^ 2
        ≤ (2 * D.invβ ^ 2 + C) * sobolevNorm (γ : ℝ) (UpF D μ' r t φ) ^ 2 := hn
      _ ≤ (2 * D.invβ ^ 2 + C) * (Real.exp (|l| * t) * sobolevNorm (γ : ℝ) φ) ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ hν0
          exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
      _ = B ^ 2 := by
          rw [hB, mul_pow (Real.sqrt (2 * D.invβ ^ 2 + C)), Real.sq_sqrt hν0]
  have hint : ∀ k : NonzeroLattice d, IntervalIntegrable
      (fun r => Torus.funRealCoeff (gfevL D (μ' r) (UpF D μ' r t φ)) k) volume u u' := by
    intro k
    have h0 : IntervalIntegrable (fun r => gfevRc k (forwardGen D (μ' (t - (t - r))) (F (t - r)) k.1))
        volume u u' := by
      have := (hII (gfevRc k) k.1 (t - u') (t - u) (by linarith) (by linarith) (by linarith)).comp_sub_left t
      simpa using this.symm
    refine h0.congr fun r hr => ?_
    rw [Set.uIoc_of_le huu'] at hr
    exact (hgrc k r (by linarith [hr.1]) (by linarith [hr.2])).symm
  have hmem : ∀ r, 0 ≤ r → r ≤ t → MemSobolev ((γ : ℝ) - 2) (UpF D μ' r t φ) := fun r hr hrt =>
    memSobolev_of_dom (by push_cast; linarith) (hψD r hr hrt)
  exact gfev_eval_duhamel_abs (f := fun r => UpF D μ' r t φ)
    (g := fun r => gfevL D (μ' r) (UpF D μ' r t φ)) huu' (hmem u hu (by linarith)) (hmem u' (hu.trans huu') hu't) hg hint
    (fun k => hcoef k hu huu' hu't) z

end HRS.GF

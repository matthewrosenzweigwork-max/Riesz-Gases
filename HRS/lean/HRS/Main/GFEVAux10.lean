import HRS.Main.GFEVAux9

/-!
# Packet GFEVG, part 10: the generator at the function level, its `H^γ → H^{γ-2}` bound, the dual operator `A_s`
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.GF

open HRS HRS.PDE HRS.PDE.ET HRS.Uniform HRS.Uniform.Q54

variable {d : ℕ} {s : ℝ} {γ : ℕ} {R : Regime} {VB Λ : ℝ} {D : DynData d} {T : ℝ} {ρ : ℝ → Torus d → ℝ}

/-- The backward generator at the function level: `𝓛_ρ' ψ = toFun (forwardGen D ρ' (ψ̂))`. -/
def gfevL (D : DynData d) (ρ' : Torus d → ℝ) (ψ : Torus d → ℝ) : Torus d → ℝ :=
  toFun (forwardGen D ρ' (coeffOf ψ))

theorem GFPde.dgt (h : GFPde d s γ R VB Λ D T ρ) : (d : ℝ) / 2 + 2 < γ := by
  have h1 := mStar_gt d
  have h2 : (mStar d : ℝ) ≤ γ := by exact_mod_cast h.hm
  linarith

theorem GFPde.realV (h : GFPde d s γ R VB Λ D T ρ) : IsRealCoeff (coeffOf D.V) :=
  isRealCoeff_coeffOf _ (ClassicalAux.integrable_of_continuous
    (Torus.continuous_of_continuous_lift (h.hV.1.continuous)))

theorem GFPde.contMu (h : GFPde d s γ R VB Λ D T ρ) (t : ℝ) : Continuous (gfevMu T ρ t) := by
  have := (h.hρ _ (gfevClamp_mem h.hT.le t)).2.1
  exact Torus.continuous_of_continuous_lift (this.continuous)

theorem GFPde.realMu (h : GFPde d s γ R VB Λ D T ρ) (t : ℝ) : IsRealCoeff (coeffOf (gfevMu T ρ t)) :=
  isRealCoeff_coeffOf _ (ClassicalAux.integrable_of_continuous (h.contMu t))

theorem gfev_forwardGen_isReal (D : DynData d) (ρ : Torus d → ℝ) (hρ : IsRealCoeff (coeffOf ρ))
    (hV : IsRealCoeff (coeffOf D.V)) {F : Coeff d} (hF : IsRealCoeff F) :
    IsRealCoeff (forwardGen D ρ F) := by
  rw [isRealCoeff_iff_reflConj] at hF ⊢
  rw [← forwardGen_reflConj D ρ hρ hV F, hF]

/-- Facts on `𝓛 ψ` for `ψ ∈ Dom (γ+2)`, uniformly in the frozen density. -/
theorem GFPde.gen_facts (h : GFPde d s γ R VB Λ D T ρ) {K MB Bμ BV : ℝ} (hMB : 0 ≤ MB) (hBμ : 0 ≤ Bμ)
    (hBV : 0 ≤ BV) (hK : (d : ℝ) + |(γ : ℝ) - 2| + 4 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ' : Torus d → ℝ), Continuous ρ' → GenHyp d s K MB Bμ BV D ρ' →
      ∀ ψ : Torus d → ℝ, Dom (γ + 2) ψ →
        coeffOf (gfevL D ρ' ψ) = forwardGen D ρ' (coeffOf ψ) ∧ Continuous (gfevL D ρ' ψ) ∧
        MemSobolev ((γ : ℝ) - 2) (gfevL D ρ' ψ) ∧
        sobolevNorm ((γ : ℝ) - 2) (gfevL D ρ' ψ) ^ 2 ≤ (2 * D.invβ ^ 2 + C) * sobolevNorm (γ : ℝ) ψ ^ 2 := by
  obtain ⟨C, hC, hgen⟩ := gen_hs_bound s h.hsd K MB Bμ BV hMB hBμ hBV ((γ : ℝ) - 2) hK
  refine ⟨C, hC, fun ρ' hρc hG ψ hψ => ?_⟩
  have hγ1 : (1 : ℝ) ≤ γ := by have := h.hγ5; exact_mod_cast (by omega : 1 ≤ γ)
  have hψγ : MemSobolev (γ : ℝ) ψ := memSobolev_of_dom (by push_cast; linarith) hψ
  obtain ⟨hc1, hc2⟩ := hsNormSq_coeffOf (γ : ℝ) ψ hψγ
  have hc1' : MemHs 1 (coeffOf ψ) := hc1.mono hγ1
  have e2 : ((γ : ℝ) - 2) + 2 = γ := by ring
  have hc1'' : MemHs (((γ : ℝ) - 2) + 2) (coeffOf ψ) := by rw [e2]; exact hc1
  obtain ⟨hm, hn⟩ := hgen D ρ' hG (coeffOf ψ) hc1'' hc1'
  have hrealρ : IsRealCoeff (coeffOf ρ') := isRealCoeff_coeffOf _ (ClassicalAux.integrable_of_continuous hρc)
  have hrealψ : IsRealCoeff (coeffOf ψ) := isRealCoeff_coeffOf _ (ClassicalAux.integrable_of_continuous hψ.1)
  have hreal := gfev_forwardGen_isReal D ρ' hrealρ h.realV hrealψ
  have hsum : Summable fun k => ‖forwardGen D ρ' (coeffOf ψ) k‖ :=
    summable_norm_of_memHs ((γ : ℝ) - 2) (by linarith [h.dgt]) _ hm
  have hcoef : coeffOf (gfevL D ρ' ψ) = forwardGen D ρ' (coeffOf ψ) := coeffOf_toFun _ hreal hsum
  have hcont : Continuous (gfevL D ρ' ψ) := MFPair.continuous_toFun' _ hsum
  have hMS : MemSobolev ((γ : ℝ) - 2) (gfevL D ρ' ψ) :=
    memSobolev_of_memHs _ _ (ClassicalAux.memLp_two_of_continuous hcont) (by rw [hcoef]; exact hm)
  refine ⟨hcoef, hcont, hMS, ?_⟩
  have e1 := (hsNormSq_coeffOf ((γ : ℝ) - 2) _ hMS).2
  rw [hcoef] at e1
  rw [← e1, ← hc2]
  rw [e2] at hn
  exact hn

theorem gfev_forwardGen_lin (D : DynData d) (ρ' : Torus d → ℝ) (h0 : MemHs 0 (coeffOf ρ'))
    (hb : ∀ j, MemHs 0 (driftCoeff D ρ' j)) {u v : Coeff d} (hu : MemHs 1 u) (hv : MemHs 1 v) (α β : ℂ) :
    forwardGen D ρ' (fun k => α * u k + β * v k) = fun k => α * forwardGen D ρ' u k + β * forwardGen D ρ' v k := by
  have hαu : MemHs 1 (fun k => α * u k) := by
    refine Summable.congr (hu.mul_left (‖α‖ ^ 2)) fun k => ?_
    simp [norm_mul, mul_pow]; ring
  have hβv : MemHs 1 (fun k => β * v k) := by
    refine Summable.congr (hv.mul_left (‖β‖ ^ 2)) fun k => ?_
    simp [norm_mul, mul_pow]; ring
  have e : (fun k => α * u k + β * v k) = (fun k => α * u k) + (fun k => β * v k) := rfl
  rw [e, forwardGen_add_H1 D ρ' h0 hb hαu hβv, MFPair.forwardGen_smul_aux, MFPair.forwardGen_smul_aux]
  rfl

theorem gfev_forwardGen_delta (D : DynData d) (ρ' : Torus d → ℝ) (c : ℝ) :
    forwardGen D ρ' (coeffOf (fun _ : Torus d => c)) = 0 := by
  have e : coeffOf (fun _ : Torus d => c) = fun k => (c : ℂ) * deltaCoeff 0 k := funext (coeffOf_const c)
  rw [e, MFPair.forwardGen_smul_aux]
  have hd : ∀ j, derivCoeff j (deltaCoeff (0 : Lattice d)) = 0 := by
    intro j; funext k
    by_cases hk : k = 0
    · subst hk
      have : (((0 : Lattice d) j : ℤ) : ℂ) = 0 := by simp
      show (2 * Real.pi * Complex.I * (((0 : Lattice d) j : ℤ) : ℂ)) * deltaCoeff 0 0 = (0 : Coeff d) 0
      rw [this]; simp
    · simp [derivCoeff, deltaCoeff, hk]
  have hl : laplaceCoeff (deltaCoeff (0 : Lattice d)) = 0 := by
    funext k
    by_cases hk : k = 0
    · subst hk
      have h0 : Lattice.toEuc (0 : Lattice d) = 0 := by ext i; simp [Lattice.toEuc]
      simp [laplaceCoeff, Lattice.enorm, h0]
    · simp [laplaceCoeff, deltaCoeff, hk]
  have h0 : forwardGen D ρ' (deltaCoeff 0) = 0 := by
    funext k
    simp only [forwardGen, transportCoeff, nonlocalCoeff, hl, hd, ClassicalPart.mulCoeff_zero_right,
      gradRieszCoeff, rieszMult, derivCoeff, Pi.zero_apply]
    simp [mul_zero]
  rw [h0]; funext k; simp

theorem gfev_toFun_zero : toFun (0 : Coeff d) = fun _ => 0 := by
  funext x; simp [toFun, series]

theorem GFPde.generator (h : GFPde d s γ R VB Λ D T ρ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ,
      GfDualHyp (Dom (γ + 2)) (γ : ℝ) ((γ : ℝ) - 2) (gfevL D (gfevMu T ρ t)) M := by
  obtain ⟨Bμ, BV, hBμ, hBV, hG⟩ := h.genHyp
  have hγ2 : (2 : ℝ) ≤ γ := by have := h.hγ5; exact_mod_cast (by omega : 2 ≤ γ)
  have hK : (d : ℝ) + |(γ : ℝ) - 2| + 4 ≤ ((γ + 2 * d + 11 : ℕ) : ℝ) := by
    rw [abs_of_nonneg (by linarith)]; push_cast; linarith
  obtain ⟨C, hC, hfacts⟩ := h.gen_facts (K := ((γ + 2 * d + 11 : ℕ) : ℝ)) (MB := 1) (Bμ := Bμ) (BV := BV)
    zero_le_one hBμ hBV hK
  have hν0 : 0 ≤ 2 * D.invβ ^ 2 + C := by positivity
  refine ⟨Real.sqrt (2 * D.invβ ^ 2 + C), Real.sqrt_nonneg _, fun t => ?_⟩
  have hγ1 : (1 : ℝ) ≤ γ := by linarith
  refine ⟨Real.sqrt_nonneg _, fun φ hφ => dom_smooth hφ,
    fun φ hφ => memSobolev_of_dom (by push_cast; linarith) hφ,
    fun φ ψ hφ hψ α β => dom_closed hφ hψ α β, ?_, ?_, ?_⟩
  · -- linearity
    intro φ ψ hφ hψ α β
    have hφ' := hfacts _ (h.contMu t) (hG t) φ hφ
    have hψ' := hfacts _ (h.contMu t) (hG t) ψ hψ
    have hcl := dom_closed hφ hψ α β
    have hχ := hfacts _ (h.contMu t) (hG t) _ hcl
    have hmemφ : MemSobolev (γ : ℝ) φ := memSobolev_of_dom (by push_cast; linarith) hφ
    have hmemψ : MemSobolev (γ : ℝ) ψ := memSobolev_of_dom (by push_cast; linarith) hψ
    have hc1 := (hsNormSq_coeffOf (γ : ℝ) φ hmemφ).1.mono hγ1
    have hc2 := (hsNormSq_coeffOf (γ : ℝ) ψ hmemψ).1.mono hγ1
    obtain ⟨h0, hdr⟩ := genHyp_memHs0 h.hsd (hG t) (by linarith [abs_nonneg ((γ : ℝ) - 2), Nat.cast_nonneg (α := ℝ) d]) zero_le_one hBμ hBV
    refine MFAux.eq_of_funFourierCoeff_eq hχ.2.1 ((continuous_const.mul hφ'.2.1).add (continuous_const.mul hψ'.2.1)) fun k => ?_
    have e1 := congrFun hχ.1 k
    have e2 := Q54.coeffOf_lin hφ'.2.1 hψ'.2.1 α β
    have e3 := Q54.coeffOf_lin hφ.1 hψ.1 α β
    have e4 := congrFun (gfev_forwardGen_lin D (gfevMu T ρ t) h0 hdr hc1 hc2 (α : ℂ) (β : ℂ)) k
    change coeffOf (gfevL D (gfevMu T ρ t) (fun x => α * φ x + β * ψ x)) k = coeffOf _ k
    rw [e1, e3, e4, e2]
    simp only [hφ'.1, hψ'.1]
  · intro c
    unfold gfevL
    rw [gfev_forwardGen_delta, gfev_toFun_zero]
  · intro φ hφ
    obtain ⟨-, -, hm, hn⟩ := hfacts _ (h.contMu t) (hG t) φ hφ
    refine ⟨hm, ?_⟩
    have h0 : 0 ≤ sobolevNorm ((γ : ℝ) - 2) (gfevL D (gfevMu T ρ t) φ) := Real.sqrt_nonneg _
    have h1 : 0 ≤ Real.sqrt (2 * D.invβ ^ 2 + C) * sobolevNorm (γ : ℝ) φ :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    refine le_of_sq_le_sq ?_ h1
    rw [mul_pow, Real.sq_sqrt hν0]
    exact hn

end HRS.GF

import HRS.MS.WadAux157

/-!
# S8.3, packet S8G-9: the frozen clause (4b)

`s8g_clause4b`: for every `U` with `IsWeightedSemigroup`, `S8eC4b a β ρβ M U` holds: for every `j` there are `C_j, c > 0` with, for
`t ≥ 1` and every doubly centered `R ∈ C_M^{pair}` (order `0`), `U_t^xU_t^yR ∈ C_M^{pair,j}` and
`‖U_t^xU_t^yR‖_{M,j} ≤ C_j e^{-ct}‖R‖_{M,0}`.  (Route: Banach space `C_0`, `ℓ(x) = (q ↦ U_tP(⟨·⟩^M q)(x))` is a `C^j` map
into the dual by `S8eC2b` at order `j+1`; the tensor is the bilinear pairing `(ℓ(x)+m)(ψ_s ℓ(y))`.)
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8g_clause4b (hd : 2 ≤ d) {a β M : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) (hMpos : 0 < M) {U : ℝ → (Euc d → ℝ) → Euc d → ℝ}
    (hU : IsWeightedSemigroup (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) M U) :
    S8eC4b a β ρβ M U := by
  intro j
  have hP : HRS.Whole.IsProbDensity ρβ := hρ.1.1
  have hg : s84_GaussReg ρβ := s84_thermal_gaussReg hd ha hβ hρ
  have hint : Integrable (fun y : Euc d => jbracket y ^ M) (HRS.Whole.withDensityReal ρβ) :=
    s85_jb_integrable hP hg hMpos.le
  obtain ⟨Cj, c, hc, h⟩ := s8f_clause2b hd ha hβ hρ hMpos hU (j + 1)
  set a0 : ℝ := max Cj 0 with ha0
  set cc : ℝ := ((d : ℝ) + 1) ^ (j + 1) with hcc
  set mm : ℝ := ∫ x, jbracket x ^ M ∂(HRS.Whole.withDensityReal ρβ) with hmm
  have ha00 : 0 ≤ a0 := le_max_right _ _
  have hcc0 : 0 ≤ cc := by positivity
  have hmm0 : 0 ≤ mm := integral_nonneg fun x => Real.rpow_nonneg (s83_jb_pos x).le _
  refine ⟨2 ^ j * ((cc * a0 + mm) * (cc * a0)), c, hc, fun t ht R hR hdc => ?_⟩
  have hT := s8g_op_of_2b hd ha hβ hρ hMpos hU (J := j + 1) (fun t ht f hf => h t ht f hf) ht
  obtain ⟨N0', hN00', hN0'⟩ := s8e_Qa_bdd hR
  have hfin : pairNormE M 0 R ≠ ⊤ := by
    rw [s8e_pairNorm_zero]
    refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top (iSup_le fun z => ENNReal.ofReal_le_ofReal (hN0' z))
  set N0 : ℝ := (pairNormE M 0 R).toReal with hN0def
  have hN0 : ∀ z, |s8e_Qa M R z| ≤ N0 := fun z => by
    have : ENNReal.ofReal |s8e_Qa M R z| ≤ pairNormE M 0 R := by
      rw [s8e_pairNorm_zero]; exact le_iSup (fun z => ENNReal.ofReal |s8e_Qa M R z|) z
    exact (ENNReal.ofReal_le_iff_le_toReal hfin).1 this
  have hNn : 0 ≤ N0 := ENNReal.toReal_nonneg
  have hs := s8g_qsec_sec M hR hN0
  set m := s8g_meanF hint with hm
  have hmn : ‖m‖ ≤ mm := s8g_meanF_norm hint
  have hF : Function.uncurry (tensorU U t R) = s8g_Phi hT hs m := by
    funext z
    obtain ⟨x, y⟩ := z
    exact s8g_tensor_eq hd ha hβ hρ hMpos hU hR hdc ht hT hN0 hint x y
  have hexp1 : Real.exp (-c * t) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith [mul_pos hc (show (0 : ℝ) < t by linarith)])
  have hE0 : 0 ≤ Real.exp (-c * t) := (Real.exp_pos _).le
  refine ⟨⟨?_, fun i hi => ?_⟩, ?_⟩
  · rw [hF]; exact s8g_Phi_contDiff hT hs m
  · rw [hF]; exact (s8g_Phi_decay hMpos hT hs m).2 i hi
  · unfold pairNormE
    refine iSup_le fun i => iSup_le fun z => ?_
    rw [hF]
    have hb := s8g_Phi_bound hMpos.le hT hs m (k := (i : ℕ)) (by have := i.2; omega) z
    have hx1 : jbracket z.1 ^ (-M) * jbracket z.1 ^ M = 1 := by
      rw [← Real.rpow_add (s83_jb_pos z.1)]; simp
    have hy1 : jbracket z.2 ^ (-M) * jbracket z.2 ^ M = 1 := by
      rw [← Real.rpow_add (s83_jb_pos z.2)]; simp
    set A : ℝ := a0 * Real.exp (-c * t) with hA
    have hAcc : cc * A = (cc * a0) * Real.exp (-c * t) := by rw [hA]; ring
    have hw0 : 0 ≤ jbracket z.1 ^ (-M) * jbracket z.2 ^ (-M) :=
      mul_nonneg (Real.rpow_nonneg (s83_jb_pos z.1).le _) (Real.rpow_nonneg (s83_jb_pos z.2).le _)
    have hreal : jbracket z.1 ^ (-M) * jbracket z.2 ^ (-M) *
        ‖iteratedFDeriv ℝ (i : ℕ) (s8g_Phi hT hs m) z‖ ≤
        2 ^ j * ((cc * a0 + mm) * (cc * a0)) * Real.exp (-c * t) * N0 := by
      calc _ ≤ jbracket z.1 ^ (-M) * jbracket z.2 ^ (-M) *
            (2 ^ (i : ℕ) * ((cc * A + ‖m‖) * N0 * (cc * A)) * (jbracket z.1 ^ M * jbracket z.2 ^ M)) :=
            mul_le_mul_of_nonneg_left hb hw0
        _ = 2 ^ (i : ℕ) * ((cc * A + ‖m‖) * N0 * (cc * A)) *
            ((jbracket z.1 ^ (-M) * jbracket z.1 ^ M) * (jbracket z.2 ^ (-M) * jbracket z.2 ^ M)) := by ring
        _ = 2 ^ (i : ℕ) * ((cc * A + ‖m‖) * N0 * (cc * A)) := by rw [hx1, hy1]; ring
        _ ≤ 2 ^ j * ((cc * a0 * Real.exp (-c * t) + mm) * N0 * (cc * a0 * Real.exp (-c * t))) := by
            rw [hAcc]
            have h2 : (2 : ℝ) ^ (i : ℕ) ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) (by have := i.2; omega)
            have hq : 0 ≤ (cc * a0 * Real.exp (-c * t) + ‖m‖) * N0 * (cc * a0 * Real.exp (-c * t)) := by
              have := norm_nonneg m
              positivity
            calc 2 ^ (i : ℕ) * ((cc * a0 * Real.exp (-c * t) + ‖m‖) * N0 * (cc * a0 * Real.exp (-c * t)))
                ≤ 2 ^ j * ((cc * a0 * Real.exp (-c * t) + ‖m‖) * N0 * (cc * a0 * Real.exp (-c * t))) :=
                  mul_le_mul_of_nonneg_right h2 hq
              _ ≤ _ := by
                  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                  have hca : 0 ≤ cc * a0 * Real.exp (-c * t) := by positivity
                  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hNn) hca
                  linarith
        _ ≤ 2 ^ j * ((cc * a0 + mm) * (cc * a0)) * Real.exp (-c * t) * N0 := by
            have := s8e_const_ineq (A := cc * a0) (m := mm) (E := Real.exp (-c * t)) (N := N0)
              (by positivity) hmm0 hE0 hexp1 hNn
            calc 2 ^ j * ((cc * a0 * Real.exp (-c * t) + mm) * N0 * (cc * a0 * Real.exp (-c * t)))
                = 2 ^ j * (cc * a0 * Real.exp (-c * t) * (cc * a0 * Real.exp (-c * t) + mm) * N0) := by ring
              _ ≤ 2 ^ j * (cc * a0 * (cc * a0 + mm) * Real.exp (-c * t) * N0) :=
                  mul_le_mul_of_nonneg_left this (by positivity)
              _ = _ := by ring
    calc ENNReal.ofReal (jbracket z.1 ^ (-M) * jbracket z.2 ^ (-M) *
          ‖iteratedFDeriv ℝ (i : ℕ) (s8g_Phi hT hs m) z‖)
        ≤ ENNReal.ofReal (2 ^ j * ((cc * a0 + mm) * (cc * a0)) * Real.exp (-c * t) * N0) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal (2 ^ j * ((cc * a0 + mm) * (cc * a0)) * Real.exp (-c * t)) * pairNormE M 0 R := by
          rw [ENNReal.ofReal_mul (by positivity), hN0def, ENNReal.ofReal_toReal hfin]

end HRS.MS.Wad

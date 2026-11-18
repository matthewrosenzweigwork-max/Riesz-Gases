import HRS.MS.WadAux95

/-!
# S8.3, packet S8E-5, part 7: the frozen clause (4a)

`s8e_pairNorm_zero`: `pairNormE M 0 F = sup_z ofReal |⟨x⟩^{-M}⟨y⟩^{-M} F(x,y)|`.
`s8e_clause4a`: for every `U` with `IsWeightedSemigroup` there are `C_d, c > 0` with, for `t ≥ 1` and every doubly centered
`R ∈ C_M^{pair}`, `‖U_t^xU_t^yR‖_{M,0} ≤ C_d e^{-ct} ‖R‖_{M,0}` (fifth conjunct of the frozen statement).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8e_pairNorm_zero (M : ℝ) (F : Euc d → Euc d → ℝ) :
    pairNormE M 0 F = ⨆ z : Euc d × Euc d, ENNReal.ofReal |s8e_Qa M F z| := by
  have key : ∀ (i : Fin (0 + 1)) (z : Euc d × Euc d),
      ENNReal.ofReal (jbracket z.1 ^ (-M) * jbracket z.2 ^ (-M) *
        ‖iteratedFDeriv ℝ (i : ℕ) (Function.uncurry F) z‖) = ENNReal.ofReal |s8e_Qa M F z| := by
    intro i z
    have hi : (i : ℕ) = 0 := by have := i.2; omega
    rw [hi, norm_iteratedFDeriv_zero]
    unfold s8e_Qa
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (s83_jb_pos _).le _),
      abs_of_nonneg (Real.rpow_nonneg (s83_jb_pos _).le _)]
    rfl
  unfold pairNormE
  refine le_antisymm (iSup_le fun i => iSup_le fun z => ?_) (iSup_le fun z => ?_)
  · rw [key]; exact le_iSup (fun z => ENNReal.ofReal |s8e_Qa M F z|) z
  · refine le_iSup_of_le ⟨0, by norm_num⟩ (le_iSup_of_le z ?_)
    rw [key]

theorem s8e_tensorU_eq (hd : 2 ≤ d) {a β M : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) (hMpos : 0 < M) {Cd c : ℝ} (hCd : 0 ≤ Cd)
    (h2a : S8e2a a β M ρβ Cd c) {U : ℝ → (Euc d → ℝ) → Euc d → ℝ}
    (hU : IsWeightedSemigroup (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) M U)
    {R : Euc d → Euc d → ℝ} (hR : MemCMpair M 0 R) (hdc : IsDoublyCentered (HRS.Whole.withDensityReal ρβ) R)
    {t : ℝ} (ht : 1 ≤ t) (x y : Euc d) :
    tensorU U t R x y = s85_Ulim a β ρβ M t (fun x' => s85_Ulim a β ρβ M t (R x') y) x := by
  unfold tensorU
  have h1 : (fun x' => U t (R x') y) = fun x' => s85_Ulim a β ρβ M t (R x') y := by
    funext x'
    rw [s85_semigroup_unique hd ha hβ hρ hMpos hU (by linarith) (s8e_R_cm hR x')]
  rw [h1]
  exact congrFun (s85_semigroup_unique hd ha hβ hρ hMpos hU (by linarith)
    (s8e_G_cm hd ha hβ hρ hMpos hCd h2a hR hdc ht y)) x

theorem s8e_const_ineq {A m E N : ℝ} (hA : 0 ≤ A) (hm : 0 ≤ m) (hE0 : 0 ≤ E) (hE1 : E ≤ 1) (hN : 0 ≤ N) :
    A * E * (A * E + m) * N ≤ A * (A + m) * E * N := by
  have h1 : A * E ≤ A := by nlinarith
  have h2 : A * E * (A * E + m) ≤ A * (A + m) * E := by
    calc A * E * (A * E + m) = A * E * (A * E) + A * E * m := by ring
      _ ≤ A * E * A + A * E * m := by
          have := mul_le_mul_of_nonneg_left h1 (mul_nonneg hA hE0)
          linarith
      _ = A * (A + m) * E := by ring
  exact mul_le_mul_of_nonneg_right h2 hN

theorem s8e_clause4a (hd : 2 ≤ d) {a β M : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) (hMpos : 0 < M) {U : ℝ → (Euc d → ℝ) → Euc d → ℝ}
    (hU : IsWeightedSemigroup (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) M U) :
    ∃ Cd c : ℝ, 0 < c ∧ ∀ t : ℝ, 1 ≤ t → ∀ R : Euc d → Euc d → ℝ, MemCMpair M 0 R →
      IsDoublyCentered (HRS.Whole.withDensityReal ρβ) R →
      pairNormE M 0 (tensorU U t R) ≤ ENNReal.ofReal (Cd * Real.exp (-c * t)) * pairNormE M 0 R := by
  have hM := hMpos.le
  have hP : HRS.Whole.IsProbDensity ρβ := hρ.1.1
  have hg : s84_GaussReg ρβ := s84_thermal_gaussReg hd ha hβ hρ
  obtain ⟨Cd0, c, hCd0, hc, h2a⟩ := s8e_2a_pt hd ha hβ hρ hMpos
  have h2a' : S8e2a a β M ρβ Cd0 c := h2a
  set m : ℝ := ∫ z, jbracket z ^ M ∂(HRS.Whole.withDensityReal ρβ) with hm
  have hm0 : 0 ≤ m := integral_nonneg fun z => Real.rpow_nonneg (s83_jb_pos z).le _
  refine ⟨Cd0 * (Cd0 + m), c, hc, fun t ht R hR hdc => ?_⟩
  obtain ⟨N0, hN00, hN0⟩ := s8e_Qa_bdd hR
  have hfin : pairNormE M 0 R ≠ ⊤ := by
    rw [s8e_pairNorm_zero]
    refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top (iSup_le fun z => ENNReal.ofReal_le_ofReal (hN0 z))
  set N : ℝ := (pairNormE M 0 R).toReal with hN
  have hN0' : ∀ z, |s8e_Qa M R z| ≤ N := fun z => by
    have : ENNReal.ofReal |s8e_Qa M R z| ≤ pairNormE M 0 R := by
      rw [s8e_pairNorm_zero]; exact le_iSup (fun z => ENNReal.ofReal |s8e_Qa M R z|) z
    exact (ENNReal.ofReal_le_iff_le_toReal hfin).1 this
  have hNn : 0 ≤ N := ENNReal.toReal_nonneg
  have hexp : Real.exp (-c * t) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [mul_pos hc (show (0:ℝ) < t by linarith)])
  have hE0 : 0 ≤ Real.exp (-c * t) := (Real.exp_pos _).le
  rw [s8e_pairNorm_zero]
  refine iSup_le fun z => ?_
  obtain ⟨x, y⟩ := z
  have hpt := s8e_tensor_pt hd ha hβ hρ hMpos hCd0 h2a' hR hdc hN0' ht x y
  rw [← s8e_tensorU_eq hd ha hβ hρ hMpos hCd0 h2a' hU hR hdc ht x y] at hpt
  have hjx := Real.rpow_pos_of_pos (s83_jb_pos x) M
  have hjy := Real.rpow_pos_of_pos (s83_jb_pos y) M
  have hQ : |s8e_Qa M (tensorU U t R) (x, y)| ≤ Cd0 * (Cd0 + m) * Real.exp (-c * t) * N := by
    have e : |s8e_Qa M (tensorU U t R) (x, y)| =
        jbracket x ^ (-M) * jbracket y ^ (-M) * |tensorU U t R x y| := by
      unfold s8e_Qa
      rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (s83_jb_pos _).le _),
        abs_of_nonneg (Real.rpow_nonneg (s83_jb_pos _).le _)]
    rw [e]
    have hx1 : jbracket x ^ (-M) * jbracket x ^ M = 1 := by
      rw [← Real.rpow_add (s83_jb_pos x)]; simp
    have hy1 : jbracket y ^ (-M) * jbracket y ^ M = 1 := by
      rw [← Real.rpow_add (s83_jb_pos y)]; simp
    have hxn := Real.rpow_nonneg (s83_jb_pos x).le (-M)
    have hyn := Real.rpow_nonneg (s83_jb_pos y).le (-M)
    calc jbracket x ^ (-M) * jbracket y ^ (-M) * |tensorU U t R x y|
        ≤ jbracket x ^ (-M) * jbracket y ^ (-M) * (Cd0 * Real.exp (-c * t) * (Cd0 * Real.exp (-c * t) + m) * N *
            jbracket x ^ M * jbracket y ^ M) := mul_le_mul_of_nonneg_left hpt (mul_nonneg hxn hyn)
      _ = Cd0 * Real.exp (-c * t) * (Cd0 * Real.exp (-c * t) + m) * N *
            ((jbracket x ^ (-M) * jbracket x ^ M) * (jbracket y ^ (-M) * jbracket y ^ M)) := by ring
      _ = Cd0 * Real.exp (-c * t) * (Cd0 * Real.exp (-c * t) + m) * N := by rw [hx1, hy1]; ring
      _ ≤ Cd0 * (Cd0 + m) * Real.exp (-c * t) * N := s8e_const_ineq hCd0 hm0 hE0 hexp hNn
  calc ENNReal.ofReal |s8e_Qa M (tensorU U t R) (x, y)|
      ≤ ENNReal.ofReal (Cd0 * (Cd0 + m) * Real.exp (-c * t) * N) := ENNReal.ofReal_le_ofReal hQ
    _ = ENNReal.ofReal (Cd0 * (Cd0 + m) * Real.exp (-c * t)) * pairNormE M 0 R := by
        rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hCd0 (add_nonneg hCd0 hm0)) hE0), hN,
          ENNReal.ofReal_toReal hfin]

end HRS.MS.Wad

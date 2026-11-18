import HRS.MS.WadAux106
import HRS.MS.WadAux32

/-!
# S8.3, packet S8F-7: smoothness of classical solutions with `C_c^∞` data; terminal values of the iterated differences

`s8f_cl_smooth`: for `φ ∈ C_c^∞` the time-zero slice of the classical solution is `C^j` for every `j` (from the all-order uniformly local
adjoint input `s85_witness5`; `propagatorW = f_0` by uniqueness).
`s8f_hdat`: if `φ ∈ C^N` has weighted derivative bounds `‖D^iφ(y)‖ ≤ Nφ ⟨y⟩^M` (`i ≤ N`), then the terminal values of the iterated
differences satisfy `Wt M (Nφ (3^M)^N ∏‖ξ_i‖) (Δ_J f_t)` for every small `J` (iterated mean value inequality).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole HRS.MS.Ul HRS.MS.S85 HRS.MS.S52B

variable {d : ℕ}

theorem s8f_cl_smooth (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) {T : ℝ} (hT : 0 ≤ T)
    (g : SchwartzMap (Euc d) ℝ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (j : ℕ) :
    ContDiff ℝ j (propagatorW (critCoeff d a β ρβ) 0 t (⇑g)) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  have hsd : (d : ℝ) / 2 < (d : ℝ) := by linarith
  have hν : 0 < β⁻¹ := inv_pos.2 hβ
  have hρS : IsSchwartzDensity ρβ := by
    rw [HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρ]
    exact HRS.MS.S21.s21_schwartz_thermal hd hs0 hsd ha hβ
  have hQ : (a • (1 : Matrix (Fin d) (Fin d) ℝ)).IsSymm := by
    simp [Matrix.IsSymm]
  have hcoeff : critCoeff d a β ρβ =
      (⟨(d : ℝ) / 2, -1, quadV (a • (1 : Matrix (Fin d) (Fin d) ℝ)) 0, β⁻¹⟩ : WholeDyn d).coeff
        (fun _ => ρβ) := by
    unfold critCoeff
    rw [HRS.MS.S21.s21_dyn_eq]
  obtain ⟨θ, hθ⟩ := s52b_exists_ulCutoff d
  obtain ⟨K, hK⟩ := s85_witness5 hd ((d : ℝ) / 2) hs0 hsd θ hθ (max j 5) (le_max_right _ _) T β⁻¹
    (a • 1) (-1) 0 ρβ hT hν hQ hρS
  set k : ℕ := max j 5 + 1 + ⌈(d : ℝ) / 2⌉₊ with hk
  obtain ⟨Cu, hCu0, hCu⟩ := ul6_ul_of_S (d := d) hθ k
  obtain ⟨C1, hC10, hC1⟩ := s52b_schwartz_S (d := d) ((d : ℝ) / 2) k
  have hφ : ContDiff ℝ (k : WithTop ℕ∞) (⇑g) := s85_cdiff_nat (g.smooth _) _
  have hul : ulNormE k θ (⇑g) < ⊤ := by
    have := hCu (-((d : ℝ) / 2 + 1)) (C1 * oscNorm ((s52bIdx d ((d : ℝ) / 2) k : ℕ) : ℝ) g) g
      (by linarith) (g.smooth _) (hC1 g)
    exact lt_of_le_of_lt this ENNReal.ofReal_lt_top
  rw [hcoeff]
  have := (hK 0 t le_rfl ht.1 ht.2 _ hφ hul).2.1
  exact this.1.of_le (by exact_mod_cast le_max_left j 5)

theorem s8f_cl_smooth_cc (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) {T : ℝ} (hT : 0 ≤ T) {φ : Euc d → ℝ}
    (hφ : S85Cc φ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (j : ℕ) {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW (critCoeff d a β ρβ) t φ f) : ContDiff ℝ j (f 0) := by
  have h := s8f_cl_smooth hd ha hβ hρ hT (hφ.2.toSchwartzMap hφ.1) ht j
  have e : propagatorW (critCoeff d a β ρβ) 0 t φ = f 0 :=
    s85_propagator_eq hd ha hβ hρ ht.1 hf ⟨le_rfl, ht.1⟩
  rw [← e]
  exact h

theorem s8f_map_zs_le (a s : ℝ) (ha : 0 ≤ a) (hs : 0 ≤ s) (J : List (Euc d)) :
    ((J.map (fun ξ => s8e_zs a ξ s)).map (fun e => ‖e‖)).sum ≤ (J.map (fun e => ‖e‖)).sum ∧
    ((J.map (fun ξ => s8e_zs a ξ s)).map (fun e => ‖e‖)).prod ≤ (J.map (fun e => ‖e‖)).prod := by
  induction J with
  | nil => simp
  | cons ξ J ih =>
    simp only [List.map_cons, List.sum_cons, List.prod_cons]
    have h1 := s8e_zs_norm ha hs ξ
    refine ⟨add_le_add h1 ih.1, ?_⟩
    have hp : 0 ≤ ((J.map (fun ξ => s8e_zs a ξ s)).map (fun e => ‖e‖)).prod :=
      s8f_prod_nonneg (J.map (fun ξ => s8e_zs a ξ s))
    exact mul_le_mul h1 ih.2 hp (norm_nonneg _)

theorem s8f_hdat {M : ℝ} (hM : 0 ≤ M) {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) (N : ℕ) {φ : Euc d → ℝ}
    {f : ℝ → Euc d → ℝ} (hft : f t = φ) (hφN : ContDiff ℝ N φ) {Nφ : ℝ}
    (hb : ∀ i ≤ N, ∀ y, ‖iteratedFDeriv ℝ i φ y‖ ≤ Nφ * jbracket y ^ M) :
    ∀ J : List (Euc d), s8f_small N J →
      Wt M (Nφ * (3 ^ M) ^ N * (J.map (fun e => ‖e‖)).prod) (s8f_Dif a J f t) := by
  intro J hJ y
  have hNφ : 0 ≤ Nφ := by
    have h0 := hb 0 (Nat.zero_le _) y
    rw [norm_iteratedFDeriv_zero] at h0
    have hj : 0 < jbracket y ^ M := Real.rpow_pos_of_pos (s83_jb_pos y) _
    by_contra hneg
    push Not at hneg
    nlinarith [norm_nonneg (φ y)]
  rw [s8f_Dif_eq_dp, hft]
  have hlen : (J.map (fun ξ => s8e_zs a ξ t)).length = J.length := by simp
  have hb' := s8f_dp_bound hM J.length φ (hφN.of_le (by exact_mod_cast hJ.1))
    (fun i hi y => hb i (hi.trans hJ.1) y) (J.map (fun ξ => s8e_zs a ξ t)) hlen
    ((s8f_map_zs_le a t ha ht J).1.trans hJ.2) y
  refine hb'.trans ?_
  have h3 : 1 ≤ (3 : ℝ) ^ M := Real.one_le_rpow (by norm_num) hM
  have hj : 0 ≤ jbracket y ^ M := Real.rpow_nonneg (s83_jb_pos y).le _
  have hpow : ((3 : ℝ) ^ M) ^ J.length ≤ ((3 : ℝ) ^ M) ^ N := pow_le_pow_right₀ h3 hJ.1
  have hP := (s8f_map_zs_le a t ha ht J).2
  have hP0 : 0 ≤ (J.map (fun e => ‖e‖)).prod := s8f_prod_nonneg J
  have hP1 : 0 ≤ ((J.map (fun ξ => s8e_zs a ξ t)).map (fun e => ‖e‖)).prod :=
    s8f_prod_nonneg (J.map (fun ξ => s8e_zs a ξ t))
  rw [Real.norm_eq_abs] at *
  calc Nφ * ((3 : ℝ) ^ M) ^ J.length * ((J.map (fun ξ => s8e_zs a ξ t)).map (fun e => ‖e‖)).prod *
        jbracket y ^ M
      ≤ Nφ * ((3 : ℝ) ^ M) ^ N * (J.map (fun e => ‖e‖)).prod * jbracket y ^ M := by
        gcongr
    _ = _ := rfl

end HRS.MS.Wad

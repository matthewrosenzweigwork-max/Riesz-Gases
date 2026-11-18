import HRS.MS.S82P2Local
import HRS.MS.WadAux188

/-!
# S8.2 local Newton layer, packet T8A.P24: uniform short-time tensor operator norm
The merged `s8h2_P1` has a datum dependent constant `N0`.  `r26t8a_p24_jets` redoes its approximation argument with the
incoming weighted jet size `nu` as the scale of the separable approximants (error `nu/(n+1)`), giving the bound `3 C0 nu w`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

section Jets

variable {d : ℕ} {a β : ℝ} {ρβ : Euc d → ℝ} {M : ℝ} {U : ℝ → (Euc d → ℝ) → Euc d → ℝ}

theorem r26t8a_p24_jets
    (hU : IsWeightedSemigroup (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) M U)
    (h3 : S8eC3 M U) (hM : 0 ≤ M) (j : ℕ) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ {F : Euc d × Euc d → ℝ}, S8hPair M j F → ∀ {ν : ℝ}, 0 < ν →
      (∀ i ≤ j, ∀ z, ‖iteratedFDeriv ℝ i F z‖ ≤ ν * s8h_w M z) → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ContDiff ℝ j (s8h2_S U t F) ∧
      ∀ i ≤ j, ∀ z, ‖iteratedFDeriv ℝ i (s8h2_S U t F) z‖ ≤ 3 * C0 * ν * s8h_w M z := by
  obtain ⟨K0, hK00, hsec⟩ := s8h2_sec0 hU hM (T := 1) zero_le_one
  obtain ⟨C0, hC00, hsep⟩ := s8h2_sepZ_jets hU h3 hM j (T := 1) zero_le_one
  refine ⟨C0, hC00, fun {F} hF {ν} hν hNR t ht => ?_⟩
  set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hε
  have hε0 : ∀ n, 0 ≤ ε n := fun n => by simp only [hε]; positivity
  have hε1 : ∀ n, ε n ≤ 1 := fun n => by
    simp only [hε]
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hεa : Antitone ε := fun n m hnm => by
    simp only [hε]
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)
  have hεt : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hex : ∀ n : ℕ, ∃ G : Euc d × Euc d → ℝ, S8hSepZ G ∧ ∀ i ≤ j, ∀ z,
      ‖iteratedFDeriv ℝ i (fun z => F z - G z) z‖ ≤ (ν * ε n) * s8h_w M z := fun n =>
    s8h_density hM hF.1 hF.2 (mul_pos hν (by simp only [hε]; positivity))
  choose G hGs hGe using hex
  have hGpair : ∀ n, S8hPair M j (G n) := fun n => s8h2_sepZ_pair M (hGs n) j
  have hFG : ∀ n, S8hPair M j (fun z => F z - G n z) := fun n => s8h2_pair_sub hF (hGpair n)
  have hF0 : S8hPair M 0 F := s8h2_pair_mono (Nat.zero_le j) hF
  have hGjet : ∀ n, ∀ i ≤ j, ∀ z, ‖iteratedFDeriv ℝ i (G n) z‖ ≤ (2 * ν) * s8h_w M z := by
    intro n i hi z
    have hFi : ContDiff ℝ i F := hF.1.of_le (by exact_mod_cast hi)
    have hGi : ContDiff ℝ i (G n) := s8h2_sepZ_contDiff (hGs n) i
    have e : iteratedFDeriv ℝ i (G n) z =
        iteratedFDeriv ℝ i F z - iteratedFDeriv ℝ i (fun z => F z - G n z) z := by
      rw [s8h2_iter_sub hFi hGi]; abel
    rw [e]
    have hw := s8h_w_pos M z
    calc _ ≤ ‖iteratedFDeriv ℝ i F z‖ + ‖iteratedFDeriv ℝ i (fun z => F z - G n z) z‖ := norm_sub_le _ _
      _ ≤ ν * s8h_w M z + (ν * ε n) * s8h_w M z := add_le_add (hNR i hi z) (hGe n i hi z)
      _ ≤ (2 * ν) * s8h_w M z := by nlinarith [hε1 n, mul_pos hν hw, mul_le_mul_of_nonneg_left (hε1 n) hν.le]
  have hSG : ∀ n, ContDiff ℝ j (s8h2_S U t (G n)) ∧ ∀ i ≤ j, ∀ z,
      ‖iteratedFDeriv ℝ i (s8h2_S U t (G n)) z‖ ≤ C0 * (2 * ν) * s8h_w M z :=
    fun n => hsep t ht (hGs n) (by positivity) (hGjet n)
  have hpt : ∀ z, Tendsto (fun n => s8h2_S U t (G n) z) atTop (𝓝 (s8h2_S U t F z)) := by
    intro z
    have hb : ∀ n, |s8h2_S U t F z - s8h2_S U t (G n) z| ≤ K0 ^ 2 * (ν * ε n) * s8h_w M z := by
      intro n
      have hP0 : S8hPair M 0 (fun z => F z - G n z) := s8h2_pair_mono (Nat.zero_le j) (hFG n)
      obtain ⟨hc, hd, -⟩ := s8h2_pair_good hP0
      have h0 := (hsec (F := fun x y => F (x, y) - G n (x, y)) (N := ν * ε n) hc hd (fun z' => by
        have := hGe n 0 (Nat.zero_le j) z'
        rw [norm_iteratedFDeriv_zero] at this
        exact this) t ht).2.2 z.1 z.2
      have hsub := congrFun (s8h2_S_sub hU hM zero_le_one ht hF0
        (s8h2_pair_mono (Nat.zero_le j) (hGpair n))) z
      have h1 : s8h2_S U t F z - s8h2_S U t (G n) z =
          tensorU U t (fun x y => F (x, y) - G n (x, y)) z.1 z.2 := hsub.symm
      rw [h1]
      refine h0.trans (le_of_eq ?_)
      unfold s8h_w
      ring
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      (g := fun n => K0 ^ 2 * (ν * ε n) * s8h_w M z) ?_)
    · rw [Real.norm_eq_abs, abs_sub_comm]; exact hb n
    · have := ((hεt.const_mul ν).const_mul (K0 ^ 2)).mul_const (s8h_w M z)
      simpa using this
  have hcau : ∀ n m, ∀ i ≤ j, ∀ z, ‖iteratedFDeriv ℝ i (s8h2_S U t (G n)) z -
      iteratedFDeriv ℝ i (s8h2_S U t (G m)) z‖ ≤ (ε n + ε m) * (C0 * ν) * s8h_w M z := by
    intro n m i hi z
    have hH : S8hSepZ (fun z => G n z - G m z) := s8h_sep_sub (hGs n) (hGs m)
    have hHjet : ∀ i ≤ j, ∀ z, ‖iteratedFDeriv ℝ i (fun z => G n z - G m z) z‖ ≤
        (ν * (ε n + ε m)) * s8h_w M z := by
      intro i hi z
      have e : (fun z => G n z - G m z) = fun z => (F z - G m z) - (F z - G n z) := by
        funext z; ring
      rw [e, s8h2_iter_sub ((hFG m).1.of_le (by exact_mod_cast hi)) ((hFG n).1.of_le (by exact_mod_cast hi))]
      calc _ ≤ ‖iteratedFDeriv ℝ i (fun z => F z - G m z) z‖ + ‖iteratedFDeriv ℝ i (fun z => F z - G n z) z‖ :=
            norm_sub_le _ _
        _ ≤ (ν * ε m) * s8h_w M z + (ν * ε n) * s8h_w M z := add_le_add (hGe m i hi z) (hGe n i hi z)
        _ = (ν * (ε n + ε m)) * s8h_w M z := by ring
    obtain ⟨-, hHb⟩ := hsep t ht hH (mul_nonneg hν.le (add_nonneg (hε0 n) (hε0 m))) hHjet
    have e2 : s8h2_S U t (fun z => G n z - G m z) = fun z => s8h2_S U t (G n) z - s8h2_S U t (G m) z :=
      s8h2_S_sub hU hM zero_le_one ht (s8h2_pair_mono (Nat.zero_le j) (hGpair n))
        (s8h2_pair_mono (Nat.zero_le j) (hGpair m))
    rw [← s8h2_iter_sub ((hSG n).1.of_le (by exact_mod_cast hi)) ((hSG m).1.of_le (by exact_mod_cast hi)),
      ← e2]
    calc _ ≤ C0 * (ν * (ε n + ε m)) * s8h_w M z := hHb i hi z
      _ = (ε n + ε m) * (C0 * ν) * s8h_w M z := by ring
  obtain ⟨hUd, hUb, -⟩ := s8h_closure (E := Euc d × Euc d) (s8h_w_cont M) (fun z => (s8h_w_pos M z).le)
    (mul_nonneg hC00 hν.le) hε0 hεa hεt j (u := fun n => s8h2_S U t (G n)) (U := s8h2_S U t F)
    (fun n => (hSG n).1) hpt hcau
  refine ⟨hUd, fun i hi z => ?_⟩
  have h0 := hUb 0 i hi z
  have hε00 : ε 0 = 1 := by simp [hε]
  rw [hε00] at h0
  have h1 := (hSG 0).2 i hi z
  calc ‖iteratedFDeriv ℝ i (s8h2_S U t F) z‖
      ≤ ‖iteratedFDeriv ℝ i (s8h2_S U t (G 0)) z‖ +
        ‖iteratedFDeriv ℝ i (s8h2_S U t F) z - iteratedFDeriv ℝ i (s8h2_S U t (G 0)) z‖ := by
        have := norm_add_le (iteratedFDeriv ℝ i (s8h2_S U t (G 0)) z)
          (iteratedFDeriv ℝ i (s8h2_S U t F) z - iteratedFDeriv ℝ i (s8h2_S U t (G 0)) z)
        simpa using this
    _ ≤ C0 * (2 * ν) * s8h_w M z + 1 * (C0 * ν) * s8h_w M z := add_le_add h1 h0
    _ = 3 * C0 * ν * s8h_w M z := by ring

end Jets

theorem r26t8a_p24_term {d : ℕ} (M : ℝ) (z : Euc d × Euc d) (x : ℝ) :
    jbracket z.1 ^ (-M) * jbracket z.2 ^ (-M) * x = x / s8h_w M z := by
  unfold s8h_w
  rw [Real.rpow_neg (s83_jb_pos _).le, Real.rpow_neg (s83_jb_pos _).le]
  field_simp

theorem r26t8a_p24_norm_le {d : ℕ} {M : ℝ} {j : ℕ} {R : Euc d → Euc d → ℝ} {B : ℝ}
    (h : ∀ i ≤ j, ∀ z : Euc d × Euc d, ‖iteratedFDeriv ℝ i (Function.uncurry R) z‖ ≤ B * s8h_w M z) :
    pairNormE M j R ≤ ENNReal.ofReal B := by
  refine iSup₂_le fun i z => ENNReal.ofReal_le_ofReal ?_
  rw [r26t8a_p24_term, div_le_iff₀ (s8h_w_pos M z)]
  exact h i (Nat.lt_succ_iff.1 i.2) z

theorem r26t8a_p24_jet_of_norm {d : ℕ} {M : ℝ} {j : ℕ} {G : Euc d → Euc d → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (h : pairNormE M j G ≤ ENNReal.ofReal B) :
    ∀ i ≤ j, ∀ z : Euc d × Euc d, ‖iteratedFDeriv ℝ i (Function.uncurry G) z‖ ≤ B * s8h_w M z := by
  intro i hi z
  have h0 : ENNReal.ofReal (jbracket z.1 ^ (-M) * jbracket z.2 ^ (-M) *
      ‖iteratedFDeriv ℝ i (Function.uncurry G) z‖) ≤ pairNormE M j G :=
    le_iSup₂_of_le (⟨i, Nat.lt_succ_of_le hi⟩ : Fin (j + 1)) z le_rfl
  have h1 := h0.trans h
  rw [ENNReal.ofReal_le_ofReal_iff hB] at h1
  rw [r26t8a_p24_term, div_le_iff₀ (s8h_w_pos M z)] at h1
  exact h1

theorem r26t8a_p24_of_pair {d : ℕ} {M : ℝ} {j : ℕ} {R : Euc d → Euc d → ℝ}
    (hRp : S8hPair M j (Function.uncurry R)) :
    pairNormE M j R ≠ ⊤ ∧ ∀ i ≤ j, ∀ z : Euc d × Euc d,
      ‖iteratedFDeriv ℝ i (Function.uncurry R) z‖ ≤ (pairNormE M j R).toReal * s8h_w M z := by
  obtain ⟨N, hN0, hN⟩ := s8h_bound_of_pair hRp
  have hPle : pairNormE M j R ≤ ENNReal.ofReal N :=
    r26t8a_p24_norm_le (fun i hi z => hN i hi z)
  have hPtop : pairNormE M j R ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hPle
  exact ⟨hPtop, r26t8a_p24_jet_of_norm ENNReal.toReal_nonneg (ENNReal.ofReal_toReal hPtop).symm.le⟩

theorem r26t8a_tensor_short_bound (d : ℕ) (hd : 2 ≤ d) (a beta M : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (hM : 0 < M) (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (U : ℝ → (Euc d → ℝ) → Euc d → ℝ)
    (hU : IsWeightedSemigroup (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) M U) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : Euc d → Euc d → ℝ, MemCMpair M j R →
      ∀ t∈Set.Icc (0:ℝ) 1, pairNormE M j (tensorU U t R) ≤ ENNReal.ofReal C*pairNormE M j R := by
  have hrho' : IsThermalEquilibrium d ((d : ℝ) / 2) a beta rho := hrho
  have h3 := s8f_clause3 hd ha hbeta hrho' hM hU
  obtain ⟨C0, hC0, hjet⟩ := r26t8a_p24_jets hU h3 hM.le j
  refine ⟨3 * C0, by positivity, fun R hR t ht => ?_⟩
  have hRp : S8hPair M j (Function.uncurry R) := s8h_pair_iff.1 hR
  obtain ⟨hPtop, hν⟩ := r26t8a_p24_of_pair hRp
  set ν0 : ℝ := (pairNormE M j R).toReal with hν0
  have hν0n : 0 ≤ ν0 := ENNReal.toReal_nonneg
  have hPeq : pairNormE M j R = ENNReal.ofReal ν0 := (ENNReal.ofReal_toReal hPtop).symm
  have hδ : ∀ δ : ℝ, 0 < δ → pairNormE M j (tensorU U t R) ≤ ENNReal.ofReal (3 * C0 * (ν0 + δ)) := by
    intro δ hδ
    obtain ⟨-, hb⟩ := hjet hRp (ν := ν0 + δ) (by linarith) (fun i hi z =>
      (hν i hi z).trans (mul_le_mul_of_nonneg_right (by linarith) (s8h_w_pos M z).le)) t ht
    exact r26t8a_p24_norm_le (fun i hi z => by
      have := hb i hi z
      rw [show 3 * C0 * (ν0 + δ) * s8h_w M z = 3 * C0 * (ν0 + δ) * s8h_w M z from rfl]
      exact this)
  rw [hPeq, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hεr : (0 : ℝ) < ε := by exact_mod_cast hε
  have hq : (0 : ℝ) < ε / (3 * C0 + 1) := by positivity
  refine (hδ _ hq).trans ?_
  have e : 3 * C0 * (ν0 + ε / (3 * C0 + 1)) = 3 * C0 * ν0 + 3 * C0 * (ε / (3 * C0 + 1)) := by ring
  rw [e]
  refine (ENNReal.ofReal_add_le).trans (add_le_add le_rfl ?_)
  have : 3 * C0 * (ε / (3 * C0 + 1)) ≤ ε := by
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith
  calc ENNReal.ofReal (3 * C0 * (ε / (3 * C0 + 1))) ≤ ENNReal.ofReal (ε : ℝ) := ENNReal.ofReal_le_ofReal this
    _ = (ε : ℝ≥0∞) := by simp

end HRS.MS.R26T8A

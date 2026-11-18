import HRS.MS.R26T8AP25

/-!
# S8.2 local Newton layer, packet T8A.P26: tensor semigroup keeps canonical rows and symmetry
Route: error lemma `|tensorU R - tensorU G| <= K eps w` from `s8h2_sec0` for a separated `G` with `|R-G| <= eps w`; the two
scalar actions commute on separated kernels (`s8h2_tensor_sep`), hence on `R`; row integrability from the weighted bound; centering by
mean preservation (P25) on the separated pieces and the weighted bound on `U_t` of the centering defect.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

section P26

variable {d : ℕ} {a β : ℝ} {ρβ : Euc d → ℝ} {M : ℝ} {U : ℝ → (Euc d → ℝ) → Euc d → ℝ}

theorem r26t8a_p26_swap {F : Euc d × Euc d → ℝ} (hF : S8hPair M 0 F) :
    S8hPair M 0 (fun z => F z.swap) := by
  obtain ⟨hc, hdec, -⟩ := s8h2_pair_good hF
  refine ⟨contDiff_zero.2 (hc.comp continuous_swap), fun i hi => ?_⟩
  obtain rfl : i = 0 := Nat.le_zero.1 hi
  simp only [norm_iteratedFDeriv_zero]
  have h := hdec.comp ((Homeomorph.prodComm (Euc d) (Euc d)).map_cocompact.le)
  refine h.congr fun z => ?_
  have hw : s8h_w M z.swap = s8h_w M z := by unfold s8h_w; simp [mul_comm]
  show ‖F z.swap‖ / s8h_w M z.swap = ‖F z.swap‖ / s8h_w M z
  rw [hw]

theorem r26t8a_p26_integrable {μ : Measure (Euc d)} (hjint : Integrable (fun y : Euc d => jbracket y ^ M) μ)
    {g : Euc d → ℝ} (hg : MemCM M g) : Integrable g μ := by
  have hw := HRS.MS.Wad.s83_wt_of_memCM hg
  exact Integrable.mono' (hjint.const_mul _) hg.1.aestronglyMeasurable
    (Eventually.of_forall fun x => by simpa using hw x)

/-- Error lemma: `tensorU R - tensorU G` is `K eps w` small when `|R - G| <= eps w`. -/
theorem r26t8a_p26_err
    (hU : IsWeightedSemigroup (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) M U)
    (hM : 0 ≤ M) {t : ℝ} (ht : 0 ≤ t) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {R : Euc d → Euc d → ℝ} {G : Euc d × Euc d → ℝ} {ε : ℝ},
      S8hPair M 0 (Function.uncurry R) → S8hPair M 0 G →
      (∀ z, ‖Function.uncurry R z - G z‖ ≤ ε * s8h_w M z) → ∀ x y,
      |tensorU U t R x y - tensorU U t (fun x y => G (x, y)) x y| ≤ K * ε * (jbracket x ^ M * jbracket y ^ M) := by
  obtain ⟨K0, hK00, hsec⟩ := s8h2_sec0 hU hM ht
  refine ⟨K0 ^ 2, by positivity, fun {R G ε} hR hG hb x y => ?_⟩
  have hP : S8hPair M 0 (fun z => Function.uncurry R z - G z) := s8h2_pair_sub hR hG
  obtain ⟨hc, hd, -⟩ := s8h2_pair_good hP
  have h0 := (hsec (F := fun x y => Function.uncurry R (x, y) - G (x, y)) (N := ε) hc hd hb t
    ⟨ht, le_rfl⟩).2.2 x y
  have hsub := congrFun (s8h2_S_sub hU hM ht ⟨ht, le_rfl⟩ hR hG) (x, y)
  have h1 : tensorU U t R x y - tensorU U t (fun x y => G (x, y)) x y =
      tensorU U t (fun x y => Function.uncurry R (x, y) - G (x, y)) x y := hsub.symm
  rw [h1]
  exact h0

theorem r26t8a_p26_approx {R : Euc d → Euc d → ℝ} (hR : S8hPair M 0 (Function.uncurry R)) (hM : 0 ≤ M)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ G : Euc d × Euc d → ℝ, S8hSepZ G ∧ (∀ z, ‖Function.uncurry R z - G z‖ ≤ ε * s8h_w M z) := by
  obtain ⟨G, hGs, hGe⟩ := s8h_density hM hR.1 hR.2 hε
  exact ⟨G, hGs, fun z => by simpa using hGe 0 le_rfl z⟩

/-- The two scalar actions commute. -/
theorem r26t8a_p26_comm
    (hU : IsWeightedSemigroup (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) M U)
    (hM : 0 ≤ M) {t : ℝ} (ht : 0 ≤ t) {R : Euc d → Euc d → ℝ}
    (hR : S8hPair M 0 (Function.uncurry R)) (x y : Euc d) :
    tensorU U t R x y = tensorU U t (fun x y => R y x) y x := by
  obtain ⟨K, hK0, hK⟩ := r26t8a_p26_err hU hM ht
  have hRs : S8hPair M 0 (Function.uncurry (fun x y => R y x)) := r26t8a_p26_swap hR
  have hn : ∀ n : ℕ, |tensorU U t R x y - tensorU U t (fun x y => R y x) y x| ≤
      (2 * K * (jbracket x ^ M * jbracket y ^ M)) * (1 / ((n : ℝ) + 1)) := by
    intro n
    obtain ⟨G, hGs, hGe⟩ := r26t8a_p26_approx hR hM (show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity)
    have hGp := s8h2_sepZ_pair M hGs 0
    have hGq : S8hPair M 0 (fun z : Euc d × Euc d => G (z.2, z.1)) := r26t8a_p26_swap hGp
    have h1 := hK hR hGp hGe x y
    have h2 := hK (R := fun x y => R y x) (G := fun z : Euc d × Euc d => G (z.2, z.1)) (ε := 1 / ((n : ℝ) + 1)) hRs hGq (fun z => by
      have := hGe (z.2, z.1)
      simpa [Function.uncurry, s8h_w, mul_comm] using this) y x
    have hEq : tensorU U t (fun x y => G (x, y)) x y = tensorU U t (fun x y => G (y, x)) y x := by
      obtain ⟨ι, _, a', b', hab, rfl⟩ := hGs
      have e1 := s8h2_tensor_sep hU ht (a' := a') (b' := b') (fun l => (hab l).1) (fun l => (hab l).2) x y
      have e2 := s8h2_tensor_sep hU ht (a' := b') (b' := a') (fun l => (hab l).2) (fun l => (hab l).1) y x
      have e0 : (fun x' y' => ∑ l, a' l y' * b' l x') = fun x' y' => ∑ l, b' l x' * a' l y' := by
        funext x' y'; exact Finset.sum_congr rfl fun l _ => mul_comm _ _
      simp only at *
      rw [e1, e0, e2]
      exact Finset.sum_congr rfl fun l _ => mul_comm _ _
    have h2' : |tensorU U t (fun x y => R y x) y x - tensorU U t (fun x y => G (y, x)) y x| ≤
        K * (1 / ((n : ℝ) + 1)) * (jbracket y ^ M * jbracket x ^ M) := h2
    have hsw : jbracket y ^ M * jbracket x ^ M = jbracket x ^ M * jbracket y ^ M := mul_comm _ _
    rw [hsw] at h2'
    have := abs_sub_le (tensorU U t R x y) (tensorU U t (fun x y => G (x, y)) x y)
      (tensorU U t (fun x y => R y x) y x)
    rw [hEq] at h1 this
    have h3 := abs_sub_comm (tensorU U t (fun x y => G (y, x)) y x) (tensorU U t (fun x y => R y x) y x)
    nlinarith [abs_sub_comm (tensorU U t (fun x y => G (y, x)) y x) (tensorU U t (fun x y => R y x) y x)]
  have hlim : Tendsto (fun n : ℕ => (2 * K * (jbracket x ^ M * jbracket y ^ M)) * (1 / ((n : ℝ) + 1)))
      atTop (𝓝 ((2 * K * (jbracket x ^ M * jbracket y ^ M)) * 0)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.const_mul _
  have := ge_of_tendsto' hlim hn
  rw [mul_zero] at this
  exact sub_eq_zero.1 (abs_nonpos_iff.1 this)

theorem r26t8a_p26_rowint
    (hU : IsWeightedSemigroup (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) M U)
    (hM : 0 ≤ M) {t : ℝ} (ht : 0 ≤ t)
    (hjint : Integrable (fun y : Euc d => jbracket y ^ M) (HRS.Whole.withDensityReal ρβ))
    {R : Euc d → Euc d → ℝ} (hR : S8hPair M 0 (Function.uncurry R)) (y : Euc d) :
    Integrable (fun x => tensorU U t R x y) (HRS.Whole.withDensityReal ρβ) := by
  obtain ⟨K0, -, hsec⟩ := s8h2_sec0 hU hM ht
  obtain ⟨hc, hdec, N, -, hN⟩ := s8h2_pair_good hR
  have hmem := (hsec (F := R) (N := N) hc hdec hN t ⟨ht, le_rfl⟩).1 y
  exact r26t8a_p26_integrable hjint (hU.maps t ht _ hmem)

theorem r26t8a_p26_center
    (hU : IsWeightedSemigroup (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) M U)
    (hM : 0 ≤ M) {t : ℝ} (ht : 0 ≤ t)
    (hjint : Integrable (fun y : Euc d => jbracket y ^ M) (HRS.Whole.withDensityReal ρβ))
    (hmean : ∀ f : Euc d → ℝ, MemCM M f → ∫ x, U t f x ∂(HRS.Whole.withDensityReal ρβ) =
      ∫ x, f x ∂(HRS.Whole.withDensityReal ρβ))
    {R : Euc d → Euc d → ℝ} (hR : S8hPair M 0 (Function.uncurry R))
    (hrow : ∀ y, Integrable (fun x => R x y) (HRS.Whole.withDensityReal ρβ))
    (hc0 : ∀ y, ∫ x, R x y ∂(HRS.Whole.withDensityReal ρβ) = 0) (y : Euc d) :
    ∫ x, tensorU U t R x y ∂(HRS.Whole.withDensityReal ρβ) = 0 := by
  set μ := HRS.Whole.withDensityReal ρβ with hμ
  set m : ℝ := ∫ z, jbracket z ^ M ∂μ with hm
  have hm0 : 0 ≤ m := integral_nonneg fun z => Real.rpow_nonneg (s83_jb_pos z).le _
  obtain ⟨K, hK0, hK⟩ := r26t8a_p26_err hU hM ht
  obtain ⟨K1, hK10, hU0⟩ := s8h_U0 hU (T := t) ht
  have hjp : ∀ z : Euc d, 0 ≤ jbracket z ^ M := fun z => Real.rpow_nonneg (s83_jb_pos z).le _
  have key : ∀ ε : ℝ, 0 < ε →
      |∫ x, tensorU U t R x y ∂μ| ≤ ε * ((K + K1) * m * jbracket y ^ M) := by
    intro ε hε
    obtain ⟨G, hGs, hGe⟩ := r26t8a_p26_approx hR hM hε
    have hGp : S8hPair M 0 G := s8h2_sepZ_pair M hGs 0
    have hGp' : S8hPair M 0 (Function.uncurry (fun x y => G (x, y))) := hGp
    have hI1 := r26t8a_p26_rowint hU hM ht hjint hR y
    have hI2 := r26t8a_p26_rowint hU hM ht hjint hGp' y
    have h1 : |∫ x, tensorU U t R x y ∂μ - ∫ x, tensorU U t (fun x y => G (x, y)) x y ∂μ| ≤
        ε * (K * m * jbracket y ^ M) := by
      rw [← integral_sub hI1 hI2, ← Real.norm_eq_abs]
      have : ‖∫ x, (tensorU U t R x y - tensorU U t (fun x y => G (x, y)) x y) ∂μ‖ ≤
          ∫ x, K * ε * jbracket y ^ M * jbracket x ^ M ∂μ :=
        norm_integral_le_of_norm_le (hjint.const_mul (K * ε * jbracket y ^ M))
        (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs]
          refine (hK hR hGp hGe x y).trans (le_of_eq ?_)
          ring)
      refine this.trans (le_of_eq ?_)
      rw [integral_const_mul]
      ring
    obtain ⟨ι, _, a', b', hab, hGeq⟩ := hGs
    have hfun : (fun x y => G (x, y)) = fun x y => ∑ l, a' l x * b' l y :=
      funext fun x => funext fun y => by rw [hGeq]
    have hai : ∀ l, Integrable (a' l) μ := fun l =>
      r26t8a_p26_integrable hjint (s8h2_cc_memCM M (hab l).1)
    have hUai : ∀ l, Integrable (U t (a' l)) μ := fun l =>
      r26t8a_p26_integrable hjint (hU.maps t ht _ (s8h2_cc_memCM M (hab l).1))
    have h2 : ∫ x, tensorU U t (fun x y => G (x, y)) x y ∂μ =
        ∑ l, (∫ x, a' l x ∂μ) * U t (b' l) y := by
      have e : (fun x => tensorU U t (fun x y => G (x, y)) x y) =
          fun x => ∑ l, U t (a' l) x * U t (b' l) y := by
        funext x
        rw [hfun]
        exact s8h2_tensor_sep hU ht (fun l => (hab l).1) (fun l => (hab l).2) x y
      rw [e, integral_finset_sum _ (fun l _ => (hUai l).mul_const _)]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [integral_mul_const, hmean _ (s8h2_cc_memCM M (hab l).1)]
    set H : Euc d → ℝ := fun y' => ∑ l, (∫ x, a' l x ∂μ) * b' l y' with hH
    have hHcc : S85Cc H := s8h2_cc_lincomb Finset.univ _ (fun l => (hab l).2)
    have h3 : ∑ l, (∫ x, a' l x ∂μ) * U t (b' l) y = U t H y :=
      (congrFun (s8h2_U_sum hU ht (fun l => ∫ x, a' l x ∂μ)
        (fun l => s8h2_cc_memCM M (hab l).2) Finset.univ) y).symm
    have hHw : ∀ y', ‖H y'‖ ≤ (ε * m) * jbracket y' ^ M := by
      intro y'
      have hGint : Integrable (fun x' => G (x', y')) μ := by
        have : (fun x' => G (x', y')) = fun x' => ∑ l, a' l x' * b' l y' :=
          funext fun x' => by rw [hGeq]
        rw [this]
        exact integrable_finset_sum _ fun l _ => (hai l).mul_const _
      have e1 : H y' = ∫ x', G (x', y') ∂μ := by
        have : (fun x' => G (x', y')) = fun x' => ∑ l, a' l x' * b' l y' :=
          funext fun x' => by rw [hGeq]
        rw [this, integral_finset_sum _ (fun l _ => (hai l).mul_const _)]
        exact Finset.sum_congr rfl fun l _ => by rw [integral_mul_const]
      have e2 : H y' = ∫ x', (G (x', y') - R x' y') ∂μ := by
        rw [integral_sub hGint (hrow y'), hc0 y', sub_zero, ← e1]
      rw [e2]
      have : ‖∫ x', (G (x', y') - R x' y') ∂μ‖ ≤ ∫ x', ε * jbracket y' ^ M * jbracket x' ^ M ∂μ :=
        norm_integral_le_of_norm_le (hjint.const_mul (ε * jbracket y' ^ M))
        (Eventually.of_forall fun x' => by
          rw [norm_sub_rev]
          refine (hGe (x', y')).trans (le_of_eq ?_)
          simp only [s8h_w]
          ring)
      refine this.trans (le_of_eq ?_)
      rw [integral_const_mul]
      ring
    have hUH := hU0 t ⟨ht, le_rfl⟩ H (s8h2_cc_memCM M hHcc) (C := ε * m) (by positivity) hHw y
    rw [Real.norm_eq_abs] at hUH
    have hB : ∫ x, tensorU U t (fun x y => G (x, y)) x y ∂μ = U t H y := h2.trans h3
    have h4 : |∫ x, tensorU U t (fun x y => G (x, y)) x y ∂μ| ≤ ε * (K1 * m * jbracket y ^ M) := by
      rw [hB]
      refine hUH.trans (le_of_eq ?_)
      ring
    have h5 := abs_sub_abs_le_abs_sub (∫ x, tensorU U t R x y ∂μ)
      (∫ x, tensorU U t (fun x y => G (x, y)) x y ∂μ)
    have h6 : ε * ((K + K1) * m * jbracket y ^ M) =
        ε * (K * m * jbracket y ^ M) + ε * (K1 * m * jbracket y ^ M) := by ring
    linarith
  by_contra hne
  have hpos : 0 < |∫ x, tensorU U t R x y ∂μ| := abs_pos.2 hne
  set c : ℝ := (K + K1) * m * jbracket y ^ M with hc
  have hc0' : 0 ≤ c := mul_nonneg (mul_nonneg (add_nonneg hK0 hK10) hm0) (hjp y)
  have h7 := key (|∫ x, tensorU U t R x y ∂μ| / (c + 1)) (by positivity)
  have h8 : |∫ x, tensorU U t R x y ∂μ| / (c + 1) * c < |∫ x, tensorU U t R x y ∂μ| := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

end P26

theorem r26t8a_tensor_canonical (d : ℕ) (hd : 2 ≤ d) (a beta M : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (hM : 0 < M) (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (U : ℝ → (Euc d → ℝ) → Euc d → ℝ)
    (hU : IsWeightedSemigroup (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) M U) :
    ∀ R : Euc d → Euc d → ℝ, MemCMpair M 0 R → CanonicalPair (HRS.Whole.withDensityReal rho) R →
      ∀ t : ℝ, 0 ≤ t → CanonicalPair (HRS.Whole.withDensityReal rho) (tensorU U t R) ∧
        ((∀ x y, R x y=R y x) → ∀ x y, tensorU U t R x y=tensorU U t R y x) := by
  intro R hR hcan t ht
  have hrho' : IsThermalEquilibrium d ((d : ℝ) / 2) a beta rho := hrho
  have hjint := HRS.MS.Wad.s85_jb_integrable hrho'.1.1
    (HRS.MS.Wad.s84_thermal_gaussReg hd ha hbeta hrho') hM.le
  have hmean : ∀ f : Euc d → ℝ, MemCM M f → ∫ x, U t f x ∂(HRS.Whole.withDensityReal rho) =
      ∫ x, f x ∂(HRS.Whole.withDensityReal rho) := fun f hf =>
    (r26t8a_weighted_mean d hd a beta M ha hbeta hM rho hrho U hU f hf t ht).2
  obtain ⟨h1, h2, hc1, hc2⟩ := hcan
  have hRp : S8hPair M 0 (Function.uncurry R) := s8h_pair_iff.1 hR
  have hRs : S8hPair M 0 (Function.uncurry (fun x y => R y x)) := r26t8a_p26_swap hRp
  have hcomm := r26t8a_p26_comm hU hM.le ht hRp
  refine ⟨⟨fun y => r26t8a_p26_rowint hU hM.le ht hjint hRp y, fun x => ?_,
    fun y => r26t8a_p26_center hU hM.le ht hjint hmean hRp h1 hc1 y, fun x => ?_⟩, fun hsym x y => ?_⟩
  · have e : tensorU U t R x = fun y => tensorU U t (fun x y => R y x) y x := funext fun y => hcomm x y
    rw [e]
    exact r26t8a_p26_rowint hU hM.le ht hjint hRs x
  · have e : (fun y => tensorU U t R x y) = fun y => tensorU U t (fun x y => R y x) y x :=
      funext fun y => hcomm x y
    rw [e]
    exact r26t8a_p26_center hU hM.le ht hjint hmean hRs h2 hc2 x
  · have e : (fun x y => R y x) = R := funext fun x => funext fun y => (hsym x y).symm
    have := hcomm x y
    rw [e] at this
    exact this


end HRS.MS.R26T8A

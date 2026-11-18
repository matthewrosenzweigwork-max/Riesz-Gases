import HRS.MS.WadAux177

/-!
# S8.3, packet S8H2-4: propagation of pair jets by `tensorU` on bounded time intervals (P1)

`s8h2_P1`: for `t ∈ [0,T]` and a pair kernel `R` with `S8hPair M j (uncurry R)`, `tensorU U t R` is `C^j` with pair jets bounded by
`C N₀ w`, and it is the limit, with all jets and uniformly in `t`, of `tensorU U t G_n` for a fixed sequence of separated kernels `G_n`
(`‖D^i S_tR - D^i S_tG_n‖ ≤ C w/(n+1)`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff Convolution

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

/-- The pair kernel `(x,y) ↦ tensorU U t G x y`. -/
def s8h2_S (U : ℝ → (Euc d → ℝ) → Euc d → ℝ) (t : ℝ) (G : Euc d × Euc d → ℝ) : Euc d × Euc d → ℝ :=
  Function.uncurry (tensorU U t (fun x y => G (x, y)))

theorem s8h2_iter_sub {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {F G : V → ℝ} {i : ℕ}
    (hF : ContDiff ℝ i F) (hG : ContDiff ℝ i G) (z : V) :
    iteratedFDeriv ℝ i (fun z => F z - G z) z = iteratedFDeriv ℝ i F z - iteratedFDeriv ℝ i G z :=
  iteratedFDeriv_sub_apply hF.contDiffAt hG.contDiffAt

theorem s8h2_pair_mono {M : ℝ} {j j' : ℕ} (h : j' ≤ j) {F : Euc d × Euc d → ℝ} (hF : S8hPair M j F) :
    S8hPair M j' F :=
  ⟨hF.1.of_le (by exact_mod_cast h), fun i hi => hF.2 i (hi.trans h)⟩

theorem s8h2_pair_sub {M : ℝ} {j : ℕ} {F G : Euc d × Euc d → ℝ} (hF : S8hPair M j F) (hG : S8hPair M j G) :
    S8hPair M j (fun z => F z - G z) := by
  refine ⟨hF.1.sub hG.1, fun i hi => ?_⟩
  have hFi : ContDiff ℝ i F := hF.1.of_le (by exact_mod_cast hi)
  have hGi : ContDiff ℝ i G := hG.1.of_le (by exact_mod_cast hi)
  have h := (hF.2 i hi).add (hG.2 i hi)
  rw [add_zero] at h
  refine squeeze_zero (fun z => by have := s8h_w_pos M z; positivity) (fun z => ?_) h
  rw [s8h2_iter_sub hFi hGi, ← add_div]
  exact div_le_div_of_nonneg_right (norm_sub_le _ _) (s8h_w_pos M z).le

theorem s8h2_sepZ_contDiff {G : Euc d × Euc d → ℝ} (hG : S8hSepZ G) (n : ℕ) : ContDiff ℝ n G := by
  obtain ⟨ι, _, a, b, hab, rfl⟩ := hG
  exact s8h2_G_contDiff (fun l => (hab l).1.1.of_le (by exact_mod_cast le_top))
    (fun l => (hab l).2.1.of_le (by exact_mod_cast le_top))

theorem s8h2_sepZ_cs {G : Euc d × Euc d → ℝ} (hG : S8hSepZ G) : HasCompactSupport G := by
  classical
  obtain ⟨ι, _, a, b, hab, rfl⟩ := hG
  have key : ∀ s : Finset ι, HasCompactSupport (fun z : Euc d × Euc d => ∑ l ∈ s, a l z.1 * b l z.2) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact HasCompactSupport.zero
    | insert l s hl ih =>
      simp only [Finset.sum_insert hl]
      have h1 : HasCompactSupport (fun z : Euc d × Euc d => a l z.1 * b l z.2) := by
        refine HasCompactSupport.intro (((hab l).1.2.isCompact).prod ((hab l).2.2.isCompact)) ?_
        intro z hz
        rw [Set.mem_prod, not_and_or] at hz
        rcases hz with hz | hz
        · rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]
        · rw [image_eq_zero_of_notMem_tsupport hz, mul_zero]
      exact h1.add ih
  exact key Finset.univ

theorem s8h2_sepZ_pair (M : ℝ) {G : Euc d × Euc d → ℝ} (hG : S8hSepZ G) (j : ℕ) : S8hPair M j G := by
  refine ⟨s8h2_sepZ_contDiff hG j, fun i hi => ?_⟩
  have hev : ∀ᶠ z in cocompact (Euc d × Euc d), ‖iteratedFDeriv ℝ i G z‖ / s8h_w M z = 0 := by
    filter_upwards [((s8h2_sepZ_cs hG).iteratedFDeriv (𝕜 := ℝ) i).compl_mem_cocompact] with z hz
    rw [image_eq_zero_of_notMem_tsupport hz]
    simp
  exact tendsto_const_nhds.congr' (hev.mono fun z hz => hz.symm)

theorem s8h2_pair_good {M : ℝ} {F : Euc d × Euc d → ℝ} (hF : S8hPair M 0 F) :
    Continuous F ∧ Tendsto (fun z => ‖F z‖ / s8h_w M z) (cocompact (Euc d × Euc d)) (𝓝 0) ∧
      ∃ N : ℝ, 0 ≤ N ∧ ∀ z, ‖F z‖ ≤ N * s8h_w M z := by
  refine ⟨hF.1.continuous, ?_, ?_⟩
  · have := hF.2 0 le_rfl
    simpa [norm_iteratedFDeriv_zero] using this
  · obtain ⟨N, hN, h⟩ := s8h_bound_of_pair hF
    exact ⟨N, hN, fun z => by simpa [norm_iteratedFDeriv_zero] using h 0 le_rfl z⟩

section Interface

variable {a β : ℝ} {ρβ : Euc d → ℝ} {M : ℝ} {U : ℝ → (Euc d → ℝ) → Euc d → ℝ}

theorem s8h2_S_sub (hU : IsWeightedSemigroup (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) M U)
    (hM : 0 ≤ M) {T : ℝ} (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Set.Icc 0 T) {F G : Euc d × Euc d → ℝ}
    (hF : S8hPair M 0 F) (hG : S8hPair M 0 G) :
    s8h2_S U t (fun z => F z - G z) = fun z => s8h2_S U t F z - s8h2_S U t G z := by
  obtain ⟨K0, -, hsec⟩ := s8h2_sec0 hU hM hT
  obtain ⟨hFc, hFd, NF, hNF0, hNF⟩ := s8h2_pair_good hF
  obtain ⟨hGc, hGd, NG, hNG0, hNG⟩ := s8h2_pair_good hG
  have h1 := (hsec (F := fun x y => F (x, y)) (N := NF) hFc hFd hNF t ht).1
  have h2 := (hsec (F := fun x y => G (x, y)) (N := NG) hGc hGd hNG t ht).1
  funext z
  exact s8h2_tensor_sub hU ht.1 (F := fun x y => F (x, y)) (G := fun x y => G (x, y))
    (fun x' => s8h2_slice_memCM hFc hFd x') (fun x' => s8h2_slice_memCM hGc hGd x') h1 h2 z.1 z.2

theorem s8h2_P1 (hU : IsWeightedSemigroup (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) M U)
    (h3 : S8eC3 M U) (hM : 0 ≤ M) (j : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {F : Euc d × Euc d → ℝ}, S8hPair M j F → ∃ N0 : ℝ, 0 ≤ N0 ∧
      ∃ G : ℕ → Euc d × Euc d → ℝ, (∀ n, S8hSepZ (G n)) ∧
        (∀ n : ℕ, ∀ z, ‖F z - G n z‖ ≤ (1 / ((n : ℝ) + 1)) * s8h_w M z) ∧ ∀ t ∈ Set.Icc 0 T,
        ContDiff ℝ j (s8h2_S U t F) ∧
        (∀ i ≤ j, ∀ z, ‖iteratedFDeriv ℝ i (s8h2_S U t F) z‖ ≤ C * N0 * s8h_w M z) ∧
        ∀ n : ℕ, ∀ i ≤ j, ∀ z, ‖iteratedFDeriv ℝ i (s8h2_S U t F) z -
          iteratedFDeriv ℝ i (s8h2_S U t (G n)) z‖ ≤ (1 / ((n : ℝ) + 1)) * C * s8h_w M z := by
  obtain ⟨K0, hK00, hsec⟩ := s8h2_sec0 hU hM hT
  obtain ⟨C0, hC00, hsep⟩ := s8h2_sepZ_jets hU h3 hM j hT
  refine ⟨C0, hC00, fun {F} hF => ?_⟩
  obtain ⟨NR, hNR0, hNR⟩ := s8h_bound_of_pair hF
  have hex : ∀ n : ℕ, ∃ G : Euc d × Euc d → ℝ, S8hSepZ G ∧ ∀ i ≤ j, ∀ z,
      ‖iteratedFDeriv ℝ i (fun z => F z - G z) z‖ ≤ (1 / ((n : ℝ) + 1)) * s8h_w M z :=
    fun n => s8h_density hM hF.1 hF.2 (by positivity)
  choose G hGs hGe using hex
  refine ⟨NR + 2, by positivity, G, hGs, fun n z => ?_, fun t ht => ?_⟩
  · have := hGe n 0 (Nat.zero_le j) z
    rwa [norm_iteratedFDeriv_zero] at this
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
  have hGpair : ∀ n, S8hPair M j (G n) := fun n => s8h2_sepZ_pair M (hGs n) j
  have hFG : ∀ n, S8hPair M j (fun z => F z - G n z) := fun n => s8h2_pair_sub hF (hGpair n)
  have hF0 : S8hPair M 0 F := s8h2_pair_mono (Nat.zero_le j) hF
  have hGjet : ∀ n, ∀ i ≤ j, ∀ z, ‖iteratedFDeriv ℝ i (G n) z‖ ≤ (NR + 1) * s8h_w M z := by
    intro n i hi z
    have hFi : ContDiff ℝ i F := hF.1.of_le (by exact_mod_cast hi)
    have hGi : ContDiff ℝ i (G n) := s8h2_sepZ_contDiff (hGs n) i
    have e : iteratedFDeriv ℝ i (G n) z =
        iteratedFDeriv ℝ i F z - iteratedFDeriv ℝ i (fun z => F z - G n z) z := by
      rw [s8h2_iter_sub hFi hGi]; abel
    rw [e]
    calc _ ≤ ‖iteratedFDeriv ℝ i F z‖ + ‖iteratedFDeriv ℝ i (fun z => F z - G n z) z‖ := norm_sub_le _ _
      _ ≤ NR * s8h_w M z + ε n * s8h_w M z := add_le_add (hNR i hi z) (hGe n i hi z)
      _ ≤ (NR + 1) * s8h_w M z := by nlinarith [hε1 n, s8h_w_pos M z]
  have hSG : ∀ n, ContDiff ℝ j (s8h2_S U t (G n)) ∧ ∀ i ≤ j, ∀ z,
      ‖iteratedFDeriv ℝ i (s8h2_S U t (G n)) z‖ ≤ C0 * (NR + 1) * s8h_w M z :=
    fun n => hsep t ht (hGs n) (by positivity) (hGjet n)
  have hpt : ∀ z, Tendsto (fun n => s8h2_S U t (G n) z) atTop (𝓝 (s8h2_S U t F z)) := by
    intro z
    have hb : ∀ n, |s8h2_S U t F z - s8h2_S U t (G n) z| ≤ K0 ^ 2 * ε n * s8h_w M z := by
      intro n
      have hP0 : S8hPair M 0 (fun z => F z - G n z) := s8h2_pair_mono (Nat.zero_le j) (hFG n)
      obtain ⟨hc, hd, -⟩ := s8h2_pair_good hP0
      have h0 := (hsec (F := fun x y => F (x, y) - G n (x, y)) (N := ε n) hc hd (fun z' => by
        have := hGe n 0 (Nat.zero_le j) z'
        rw [norm_iteratedFDeriv_zero] at this
        exact this) t ht).2.2 z.1 z.2
      have hsub := congrFun (s8h2_S_sub hU hM hT ht hF0 (s8h2_pair_mono (Nat.zero_le j) (hGpair n))) z
      have h1 : s8h2_S U t F z - s8h2_S U t (G n) z = tensorU U t (fun x y => F (x, y) - G n (x, y)) z.1 z.2 :=
        hsub.symm
      rw [h1]
      refine h0.trans (le_of_eq ?_)
      unfold s8h_w
      ring
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      (g := fun n => K0 ^ 2 * ε n * s8h_w M z) ?_)
    · rw [Real.norm_eq_abs, abs_sub_comm]; exact hb n
    · have := (hεt.const_mul (K0 ^ 2)).mul_const (s8h_w M z)
      simpa using this
  have hcau : ∀ n m, ∀ i ≤ j, ∀ z, ‖iteratedFDeriv ℝ i (s8h2_S U t (G n)) z -
      iteratedFDeriv ℝ i (s8h2_S U t (G m)) z‖ ≤ (ε n + ε m) * C0 * s8h_w M z := by
    intro n m i hi z
    have hH : S8hSepZ (fun z => G n z - G m z) := s8h_sep_sub (hGs n) (hGs m)
    have hHjet : ∀ i ≤ j, ∀ z, ‖iteratedFDeriv ℝ i (fun z => G n z - G m z) z‖ ≤
        (ε n + ε m) * s8h_w M z := by
      intro i hi z
      have e : (fun z => G n z - G m z) = fun z => (F z - G m z) - (F z - G n z) := by
        funext z; ring
      rw [e, s8h2_iter_sub ((hFG m).1.of_le (by exact_mod_cast hi)) ((hFG n).1.of_le (by exact_mod_cast hi))]
      calc _ ≤ ‖iteratedFDeriv ℝ i (fun z => F z - G m z) z‖ + ‖iteratedFDeriv ℝ i (fun z => F z - G n z) z‖ :=
            norm_sub_le _ _
        _ ≤ ε m * s8h_w M z + ε n * s8h_w M z := add_le_add (hGe m i hi z) (hGe n i hi z)
        _ = (ε n + ε m) * s8h_w M z := by ring
    obtain ⟨-, hHb⟩ := hsep t ht hH (add_nonneg (hε0 n) (hε0 m)) hHjet
    have hHb' : ∀ i ≤ j, ∀ z, ‖iteratedFDeriv ℝ i (s8h2_S U t (fun z => G n z - G m z)) z‖ ≤
        C0 * (ε n + ε m) * s8h_w M z := hHb
    have e2 : s8h2_S U t (fun z => G n z - G m z) = fun z => s8h2_S U t (G n) z - s8h2_S U t (G m) z :=
      s8h2_S_sub hU hM hT ht (s8h2_pair_mono (Nat.zero_le j) (hGpair n))
        (s8h2_pair_mono (Nat.zero_le j) (hGpair m))
    rw [← s8h2_iter_sub ((hSG n).1.of_le (by exact_mod_cast hi)) ((hSG m).1.of_le (by exact_mod_cast hi)),
      ← e2]
    calc _ ≤ C0 * (ε n + ε m) * s8h_w M z := hHb' i hi z
      _ = (ε n + ε m) * C0 * s8h_w M z := by ring
  obtain ⟨hUd, hUb, -⟩ := s8h_closure (E := Euc d × Euc d) (s8h_w_cont M) (fun z => (s8h_w_pos M z).le)
    hC00 hε0 hεa hεt j (u := fun n => s8h2_S U t (G n)) (U := s8h2_S U t F) (fun n => (hSG n).1) hpt hcau
  refine ⟨hUd, fun i hi z => ?_, fun n i hi z => hUb n i hi z⟩
  have h0 := hUb 0 i hi z
  have hε00 : ε 0 = 1 := by simp [hε]
  rw [hε00] at h0
  have h1 := (hSG 0).2 i hi z
  have hw := (s8h_w_pos M z).le
  calc ‖iteratedFDeriv ℝ i (s8h2_S U t F) z‖
      ≤ ‖iteratedFDeriv ℝ i (s8h2_S U t (G 0)) z‖ +
        ‖iteratedFDeriv ℝ i (s8h2_S U t F) z - iteratedFDeriv ℝ i (s8h2_S U t (G 0)) z‖ := by
        have := norm_add_le (iteratedFDeriv ℝ i (s8h2_S U t (G 0)) z)
          (iteratedFDeriv ℝ i (s8h2_S U t F) z - iteratedFDeriv ℝ i (s8h2_S U t (G 0)) z)
        simpa using this
    _ ≤ C0 * (NR + 1) * s8h_w M z + 1 * C0 * s8h_w M z := add_le_add h1 h0
    _ = C0 * (NR + 2) * s8h_w M z := by ring

end Interface

end HRS.MS.Wad

import HRS.MS.WadAux171

/-!
# S8.3, packet S8H-3: density of separated `C_c^∞` tensors in the pair jet norm

`S8hSepZ G`: `G(x,y) = ∑_l a_l(x) b_l(y)` (finite sum, `a_l, b_l ∈ C_c^∞`).  `s8h_density_cc`: every `F ∈ C^j_c(ℝ^d × ℝ^d)` is the limit of such
sums in `C^j` (product mollifier `κ(u,v) = ψ(u)ψ(v)` and a partition-of-unity discretization of the convolution).  `s8h_density`: weighted version
for `F ∈ C^j` with weighted decay of all jets of order `≤ j` (product weight `⟨x⟩^M⟨y⟩^M`), using a cutoff on `ℝ^d × ℝ^d`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff Convolution

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

/-- Finite sums of tensor products of `C_c^∞` functions. -/
def S8hSepZ (G : Euc d × Euc d → ℝ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (a b : ι → Euc d → ℝ), (∀ l, S85Cc (a l) ∧ S85Cc (b l)) ∧
    G = fun z => ∑ l, a l z.1 * b l z.2

theorem s8h_sep_neg {G : Euc d × Euc d → ℝ} (hG : S8hSepZ G) : S8hSepZ (fun z => - G z) := by
  obtain ⟨ι, _, a, b, hab, rfl⟩ := hG
  refine ⟨ι, inferInstance, fun l x => - a l x, b, fun l => ⟨⟨(hab l).1.1.neg, (hab l).1.2.neg⟩, (hab l).2⟩, ?_⟩
  funext z
  simp [Finset.sum_neg_distrib]

theorem s8h_sep_add {G₁ G₂ : Euc d × Euc d → ℝ} (h₁ : S8hSepZ G₁) (h₂ : S8hSepZ G₂) :
    S8hSepZ (fun z => G₁ z + G₂ z) := by
  obtain ⟨ι₁, _, a₁, b₁, hab₁, rfl⟩ := h₁
  obtain ⟨ι₂, _, a₂, b₂, hab₂, rfl⟩ := h₂
  refine ⟨ι₁ ⊕ ι₂, inferInstance, Sum.elim a₁ a₂, Sum.elim b₁ b₂, fun l => ?_, ?_⟩
  · rcases l with l | l
    · exact hab₁ l
    · exact hab₂ l
  · funext z
    simp [Fintype.sum_sum_type]

theorem s8h_sep_sub {G₁ G₂ : Euc d × Euc d → ℝ} (h₁ : S8hSepZ G₁) (h₂ : S8hSepZ G₂) :
    S8hSepZ (fun z => G₁ z - G₂ z) := by
  have := s8h_sep_add h₁ (s8h_sep_neg h₂)
  simpa [sub_eq_add_neg] using this

theorem s8h_density_cc {j : ℕ} {F : Euc d × Euc d → ℝ} (hF : ContDiff ℝ j F) (hFc : HasCompactSupport F)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ G, S8hSepZ G ∧ ∀ i ≤ j, ∀ z, ‖iteratedFDeriv ℝ i (fun z => F z - G z) z‖ ≤ ε := by
  classical
  -- the modulus of continuity of the jets of `F`
  have hunif : ∀ i : Fin (j + 1), ∃ δ > 0, ∀ x y : Euc d × Euc d, dist x y < δ →
      ‖iteratedFDeriv ℝ i F x - iteratedFDeriv ℝ i F y‖ ≤ ε / 2 := by
    intro i
    have hcont : Continuous (iteratedFDeriv ℝ i F) :=
      hF.continuous_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_iff.1 i.2)
    have hcs : HasCompactSupport (iteratedFDeriv ℝ i F) := hFc.iteratedFDeriv i
    obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuous_iff.1 (hcs.uniformContinuous_of_continuous hcont)
      (ε / 2) (half_pos hε)
    exact ⟨δ, hδ, fun x y hxy => by rw [← dist_eq_norm]; exact (h hxy).le⟩
  choose δ hδ hδ' using hunif
  have hne : (Finset.univ : Finset (Fin (j + 1))).Nonempty := Finset.univ_nonempty
  set r : ℝ := Finset.univ.inf' hne δ with hr
  have hr0 : 0 < r := by
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' hne δ
    rw [hr, hi]
    exact hδ i
  have hrδ : ∀ i : Fin (j + 1), r ≤ δ i := fun i => Finset.inf'_le _ (Finset.mem_univ i)
  set ψ : ContDiffBump (0 : Euc d) := ⟨r / 2, r, half_pos hr0, half_lt_self hr0⟩ with hψ
  have hψr : ψ.rOut = r := rfl
  set ψn : Euc d → ℝ := ψ.normed volume with hψn
  have hψc : Continuous ψn := ψ.continuous_normed
  have hψd : ContDiff ℝ ∞ ψn := ψ.contDiff_normed
  have hψcs : HasCompactSupport ψn := ψ.hasCompactSupport_normed
  have hψ0 : ∀ x, 0 ≤ ψn x := fun x => ψ.nonneg_normed x
  -- the product kernel
  set κ : Euc d × Euc d → ℝ := fun u => ψn u.1 * ψn u.2 with hκ
  have hκc : Continuous κ := (hψc.comp continuous_fst).mul (hψc.comp continuous_snd)
  have hκd : ContDiff ℝ ∞ κ := (hψd.comp contDiff_fst).mul (hψd.comp contDiff_snd)
  have hκcs : HasCompactSupport κ := by
    refine HasCompactSupport.intro (hψcs.isCompact.prod hψcs.isCompact) fun u hu => ?_
    simp only [Set.mem_prod, not_and_or] at hu
    rcases hu with hu | hu
    · simp [hκ, image_eq_zero_of_notMem_tsupport hu]
    · simp [hκ, image_eq_zero_of_notMem_tsupport hu]
  have hκ0 : ∀ u, 0 ≤ κ u := fun u => mul_nonneg (hψ0 _) (hψ0 _)
  have hκ1 : ∫ u, κ u = 1 := by
    rw [Measure.volume_eq_prod, integral_prod_mul]
    simp only [hψn, ψ.integral_normed, mul_one]
  have hκs : ∀ u, κ u ≠ 0 → ‖u‖ < r := by
    intro u hu
    have h1 : ψn u.1 ≠ 0 := left_ne_zero_of_mul hu
    have h2 : ψn u.2 ≠ 0 := right_ne_zero_of_mul hu
    have e1 : u.1 ∈ Function.support ψn := h1
    have e2 : u.2 ∈ Function.support ψn := h2
    rw [hψn, ψ.support_normed_eq, mem_ball_zero_iff] at e1 e2
    rw [Prod.norm_def]
    exact max_lt e1 e2
  -- the mollification
  set Φ : Euc d × Euc d → ℝ := s8h_Conv κ F with hΦ
  have hFloc : LocallyIntegrable F volume := hF.continuous.locallyIntegrable
  have hΦd : ContDiff ℝ ∞ Φ := by
    rw [hΦ, s8h_Conv_eq]
    exact hκcs.contDiff_convolution_left _ hκd hFloc
  have hstepA : ∀ i ≤ j, ∀ y, ‖iteratedFDeriv ℝ i Φ y - iteratedFDeriv ℝ i F y‖ ≤ ε / 2 := by
    intro i hi y
    exact s8h_Conv_err hκc hκcs hκ0 hκ1 hκs i F hFc (hF.of_le (by exact_mod_cast hi)) (ε := ε / 2)
      (fun x x' hxx => hδ' ⟨i, by omega⟩ x x' (lt_of_lt_of_le hxx (hψr ▸ hrδ ⟨i, by omega⟩))) y
  -- the discretization
  set A : ℝ := ∫ u, ‖F u‖ with hA
  have hA0 : 0 ≤ A := integral_nonneg fun u => norm_nonneg _
  have hunif2 : ∀ i : Fin (j + 1), ∃ δ2 > 0, ∀ a b : Euc d × Euc d, dist a b < δ2 →
      ‖iteratedFDeriv ℝ i κ a - iteratedFDeriv ℝ i κ b‖ ≤ ε / 2 / (1 + A) := by
    intro i
    have hcont : Continuous (iteratedFDeriv ℝ i κ) :=
      hκd.continuous_iteratedFDeriv (by exact_mod_cast le_top)
    have hcs : HasCompactSupport (iteratedFDeriv ℝ i κ) := hκcs.iteratedFDeriv i
    obtain ⟨δ2, hδ2, h⟩ := Metric.uniformContinuous_iff.1 (hcs.uniformContinuous_of_continuous hcont)
      (ε / 2 / (1 + A)) (by positivity)
    exact ⟨δ2, hδ2, fun x y hxy => by rw [← dist_eq_norm]; exact (h hxy).le⟩
  choose δ2 hδ2 hδ2' using hunif2
  set h : ℝ := Finset.univ.inf' hne δ2 with hh
  have hh0 : 0 < h := by
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' hne δ2
    rw [hh, hi]
    exact hδ2 i
  have hhδ : ∀ i : Fin (j + 1), h ≤ δ2 i := fun i => Finset.inf'_le _ (Finset.mem_univ i)
  obtain ⟨ι, _, θ, zs, hp⟩ := s8h_part_exists hFc hh0
  set c : ι → ℝ := fun l => ∫ u, θ l u * F u with hc
  set G : Euc d × Euc d → ℝ := s8h_Disc c zs κ with hG
  have hΦcomm : Φ = s8h_Conv F κ := funext fun z => s8h_Conv_comm κ F z
  have hstepB : ∀ i ≤ j, ∀ z, ‖iteratedFDeriv ℝ i (fun z => G z - Φ z) z‖ ≤ ε / 2 := by
    intro i hi z
    have := s8h_disc_err hF.continuous hFc hp i κ hκcs (hκd.of_le (by exact_mod_cast le_top))
      (ε := ε / 2 / (1 + A)) (by positivity) (fun a b hab => hδ2' ⟨i, by omega⟩ a b
        (by rw [dist_eq_norm]; exact lt_of_lt_of_le hab (hhδ ⟨i, by omega⟩))) z
    rw [hΦcomm]
    refine this.trans ?_
    rw [← hA]
    calc ε / 2 / (1 + A) * A ≤ ε / 2 / (1 + A) * (1 + A) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = ε / 2 := by field_simp
  -- `G` is separated
  have hGsep : S8hSepZ G := by
    refine ⟨ι, inferInstance, fun l x => c l * ψn (x - (zs l).1), fun l y => ψn (y - (zs l).2), fun l => ?_, ?_⟩
    · refine ⟨⟨contDiff_const.mul (hψd.comp (contDiff_id.sub contDiff_const)), ?_⟩,
        ⟨hψd.comp (contDiff_id.sub contDiff_const), ?_⟩⟩
      · exact (hψcs.comp_homeomorph (Homeomorph.subRight (zs l).1)).mul_left
      · exact hψcs.comp_homeomorph (Homeomorph.subRight (zs l).2)
    · funext z
      simp only [hG, s8h_Disc, hκ, smul_eq_mul, Prod.fst_sub, Prod.snd_sub]
      refine Finset.sum_congr rfl fun l _ => by ring
  have hGd : ContDiff ℝ ∞ G := by
    show ContDiff ℝ ∞ (fun z => ∑ l, c l • κ (z - zs l))
    exact ContDiff.sum fun l _ => (hκd.comp (contDiff_id.sub contDiff_const)).const_smul (c l)
  refine ⟨G, hGsep, fun i hi z => ?_⟩
  have hFi : ContDiff ℝ i F := hF.of_le (by exact_mod_cast hi)
  have hGi : ContDiff ℝ i G := hGd.of_le (by exact_mod_cast le_top)
  have hΦi : ContDiff ℝ i Φ := hΦd.of_le (by exact_mod_cast le_top)
  have e1 : iteratedFDeriv ℝ i (fun z => F z - G z) z = iteratedFDeriv ℝ i F z - iteratedFDeriv ℝ i G z := by
    have := iteratedFDeriv_sub_apply (𝕜 := ℝ) (x := z) (i := i) hFi.contDiffAt hGi.contDiffAt
    simpa [Pi.sub_def] using this
  have e2 : iteratedFDeriv ℝ i (fun z => G z - Φ z) z = iteratedFDeriv ℝ i G z - iteratedFDeriv ℝ i Φ z := by
    have := iteratedFDeriv_sub_apply (𝕜 := ℝ) (x := z) (i := i) hGi.contDiffAt hΦi.contDiffAt
    simpa [Pi.sub_def] using this
  have hA' := hstepA i hi z
  have hB' := hstepB i hi z
  rw [e2] at hB'
  rw [e1]
  have e3 : iteratedFDeriv ℝ i F z - iteratedFDeriv ℝ i G z =
      -(iteratedFDeriv ℝ i Φ z - iteratedFDeriv ℝ i F z) - (iteratedFDeriv ℝ i G z - iteratedFDeriv ℝ i Φ z) := by
    abel
  rw [e3]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_neg]
  linarith

/-- The weight `⟨x⟩^M⟨y⟩^M` on the pair space. -/
def s8h_w (M : ℝ) (z : Euc d × Euc d) : ℝ := jbracket z.1 ^ M * jbracket z.2 ^ M

theorem s8h_w_pos (M : ℝ) (z : Euc d × Euc d) : 0 < s8h_w M z :=
  mul_pos (Real.rpow_pos_of_pos (s83_jb_pos _) _) (Real.rpow_pos_of_pos (s83_jb_pos _) _)

theorem s8h_w_cont (M : ℝ) : Continuous (s8h_w (d := d) M) :=
  ((s83_jb_rpow_cont M).comp continuous_fst).mul ((s83_jb_rpow_cont M).comp continuous_snd)

theorem s8h_one_le_w {M : ℝ} (hM : 0 ≤ M) (z : Euc d × Euc d) : 1 ≤ s8h_w M z := by
  unfold s8h_w
  have h1 : 1 ≤ jbracket z.1 ^ M := Real.one_le_rpow (s83_one_le_jb _) hM
  have h2 : 1 ≤ jbracket z.2 ^ M := Real.one_le_rpow (s83_one_le_jb _) hM
  nlinarith

theorem s8h_density {M : ℝ} (hM : 0 ≤ M) {j : ℕ} {F : Euc d × Euc d → ℝ} (hF : ContDiff ℝ j F)
    (hdec : ∀ i ≤ j, Tendsto (fun z => ‖iteratedFDeriv ℝ i F z‖ / s8h_w M z) (cocompact (Euc d × Euc d)) (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ G, S8hSepZ G ∧ ∀ i ≤ j, ∀ z, ‖iteratedFDeriv ℝ i (fun z => F z - G z) z‖ ≤ ε * s8h_w M z := by
  obtain ⟨χ, hχd, hχc, hχe⟩ := s8h_cutoff_error (w := s8h_w (d := d) M) (s8h_w_pos M) hF hdec (half_pos hε)
  set g : Euc d × Euc d → ℝ := fun y => χ y * F y with hg
  have hgk : ContDiff ℝ j g := (hχd.of_le (by exact_mod_cast le_top)).mul hF
  have hgc : HasCompactSupport g := hχc.mul_right
  obtain ⟨G, hGs, hG⟩ := s8h_density_cc hgk hgc (half_pos hε)
  refine ⟨G, hGs, fun i hi z => ?_⟩
  have hFi : ContDiff ℝ i F := hF.of_le (by exact_mod_cast hi)
  have hgi : ContDiff ℝ i g := hgk.of_le (by exact_mod_cast hi)
  have hGi : ContDiff ℝ i G := by
    obtain ⟨ι, _, a, b, hab, rfl⟩ := hGs
    refine ContDiff.sum fun l _ => ((hab l).1.1.comp contDiff_fst).mul ((hab l).2.1.comp contDiff_snd) |>.of_le
      (by exact_mod_cast le_top)
  have e1 : iteratedFDeriv ℝ i (fun z => F z - G z) z = iteratedFDeriv ℝ i F z - iteratedFDeriv ℝ i G z := by
    have := iteratedFDeriv_sub_apply (𝕜 := ℝ) (x := z) (i := i) hFi.contDiffAt hGi.contDiffAt
    simpa [Pi.sub_def] using this
  have e2 : iteratedFDeriv ℝ i (fun z => g z - F z) z = iteratedFDeriv ℝ i g z - iteratedFDeriv ℝ i F z := by
    have := iteratedFDeriv_sub_apply (𝕜 := ℝ) (x := z) (i := i) hgi.contDiffAt hFi.contDiffAt
    simpa [Pi.sub_def] using this
  have e3 : iteratedFDeriv ℝ i (fun z => g z - G z) z = iteratedFDeriv ℝ i g z - iteratedFDeriv ℝ i G z := by
    have := iteratedFDeriv_sub_apply (𝕜 := ℝ) (x := z) (i := i) hgi.contDiffAt hGi.contDiffAt
    simpa [Pi.sub_def] using this
  have h1 := hχe i hi z
  have h2 := hG i hi z
  rw [e2] at h1
  rw [e3] at h2
  rw [e1]
  have e4 : iteratedFDeriv ℝ i F z - iteratedFDeriv ℝ i G z =
      -(iteratedFDeriv ℝ i g z - iteratedFDeriv ℝ i F z) + (iteratedFDeriv ℝ i g z - iteratedFDeriv ℝ i G z) := by
    abel
  rw [e4]
  refine (norm_add_le _ _).trans ?_
  rw [norm_neg]
  have hw1 := s8h_one_le_w hM z
  nlinarith

end HRS.MS.Wad

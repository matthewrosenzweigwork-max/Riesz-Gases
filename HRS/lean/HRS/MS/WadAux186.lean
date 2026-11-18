import HRS.MS.WadAux185

/-!
# S8.3, packet S8H2-12: the equation for separated data on a finite horizon

`s8h2_one`: for `φ ∈ C_c^∞` and `T > 0`, `s ↦ U_sφ` on `[0,T]` is `C²` with bounded jets continuous in `(s,x)`, `∂_s U_sφ(x) = 𝒜(U_sφ)(x)` and `s ↦ 𝒜(U_sφ)(x)` is continuous
(`U_sφ = f(T-s)` for the classical solution `f`).  `s8h2_sep_eq`: for separated `G` and `Φ_T = ∫_{(0,T]} S_tG dt`,
`𝒜_xΦ_T(·,y)(x) + 𝒜_yΦ_T(x,·)(y) = S_TG(x,y) - G(x,y)` (`s8h2_comm` and the fundamental theorem of calculus).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

section Interface

variable {a β : ℝ} {ρβ : Euc d → ℝ} {M : ℝ} {U : ℝ → (Euc d → ℝ) → Euc d → ℝ}

theorem s8h2_one (hd : 2 ≤ d) (ha : 0 < a) (hβ : 0 < β)
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ)
    (hU : IsWeightedSemigroup (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) M U)
    {T : ℝ} (hT : 0 < T) {φ : Euc d → ℝ} (hφ : S85Cc φ) :
    ∃ B : ℝ, (∀ s ∈ Set.Icc 0 T, ContDiff ℝ 2 (U s φ)) ∧
      (∀ s ∈ Set.Icc 0 T, ∀ x, ∀ i ≤ 2, ‖iteratedFDeriv ℝ i (U s φ) x‖ ≤ B) ∧
      (∀ i ≤ 2, ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ i (U p.1 φ) p.2)
        (Set.Icc 0 T ×ˢ Set.univ)) ∧
      (∀ x, ContinuousOn (fun s => projGeneratorW (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) 0
        (U s φ) x) (Set.Icc 0 T)) ∧
      (∀ x, ∀ s ∈ Set.Ioo 0 T, HasDerivAt (fun s' => U s' φ x)
        (projGeneratorW (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) 0 (U s φ) x) s) := by
  obtain ⟨f, hf, -⟩ := hU.classical T hT.le φ hφ.1 hφ.2
  have hUf : ∀ s ∈ Set.Icc (0 : ℝ) T, U s φ = f (T - s) := fun s hs =>
    s8h2_U_eq_sol hd ha hβ hρ hU hs.1 hs.2 hφ hf
  have hmem : ∀ s ∈ Set.Icc (0 : ℝ) T, T - s ∈ Set.Icc (0 : ℝ) T := fun s hs =>
    ⟨by linarith [hs.2], by linarith [hs.1]⟩
  obtain ⟨B0, hB0⟩ := hf.bdd 0 (by norm_num)
  obtain ⟨B1, hB1⟩ := hf.bdd 1 (by norm_num)
  obtain ⟨B2, hB2⟩ := hf.bdd 2 (by norm_num)
  refine ⟨|B0| + |B1| + |B2|, fun s hs => ?_, fun s hs x i hi => ?_, fun i hi => ?_, fun x => ?_, fun x s hs => ?_⟩
  · rw [hUf s hs]; exact hf.c2 _ (hmem s hs)
  · rw [hUf s hs]
    have h0 := hB0 _ (hmem s hs) x
    have h1 := hB1 _ (hmem s hs) x
    have h2 := hB2 _ (hmem s hs) x
    have := abs_nonneg B0; have := abs_nonneg B1; have := abs_nonneg B2
    interval_cases i
    · linarith [le_abs_self B0]
    · linarith [le_abs_self B1]
    · linarith [le_abs_self B2]
  · have hF : ContinuousOn (fun q : ℝ × Euc d => iteratedFDeriv ℝ i (f q.1) q.2) (Set.Icc 0 T ×ˢ Set.univ) :=
      s84_contOn_of_subtype (hf.cont_c2 i hi)
    have hc : ContinuousOn (fun p : ℝ × Euc d => (T - p.1, p.2)) (Set.Icc 0 T ×ˢ Set.univ) :=
      (continuousOn_const.sub continuous_fst.continuousOn).prodMk continuous_snd.continuousOn
    have := hF.comp hc (fun p hp => ⟨hmem p.1 hp.1, Set.mem_univ _⟩)
    refine this.congr (fun p hp => ?_)
    simp only [Function.comp]
    rw [hUf p.1 hp.1]
  · obtain ⟨-, -, -, -, -, -, -, -, -, hGc⟩ := s85_G_facts hf
    have h1 := s85_slice_cont hGc x
    have h2 : ContinuousOn (fun s => projGeneratorW (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) 0
        (f (T - s)) x) (Set.Icc 0 T) :=
      h1.comp (continuousOn_const.sub continuousOn_id) (fun s hs => hmem s hs)
    exact h2.congr (fun s hs => by rw [hUf s hs])
  · have hs' : T - s ∈ Set.Ioo (0 : ℝ) T := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have h1 := hf.time_deriv x (T - s) hs'
    have h2 := h1.comp s ((hasDerivAt_id s).const_sub T)
    have h3 : (fun s' => f (T - s') x) =ᶠ[𝓝 s] (fun s' => U s' φ x) :=
      Filter.eventuallyEq_of_mem (Ioo_mem_nhds hs.1 hs.2) (fun s' hs'' => by
        rw [hUf s' ⟨hs''.1.le, hs''.2.le⟩])
    have h4 := h2.congr_of_eventuallyEq h3.symm
    rw [hUf s ⟨hs.1.le, hs.2.le⟩]
    exact h4.congr_deriv (by rw [s8h2_gen_time a β ρβ (T - s) 0]; ring)

theorem s8h2_part (hd : 2 ≤ d) (ha : 0 < a) (hβ : 0 < β)
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ)
    (hU : IsWeightedSemigroup (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) M U)
    {T : ℝ} (hT : 0 < T) {ι : Type} [Fintype ι] {a' b' : ι → Euc d → ℝ} (hab : ∀ l, S85Cc (a' l))
    (hbb : ∀ l, S85Cc (b' l)) (x y : Euc d) :
    projGeneratorW (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) 0
        (fun x' => ∫ t in Set.Ioc 0 T, ∑ l, U t (b' l) y * U t (a' l) x') x =
      ∑ l, ∫ t in Set.Ioc 0 T, U t (b' l) y *
        projGeneratorW (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) 0 (U t (a' l)) x := by
  have hlam : ∀ l, ContinuousOn (fun t => U t (b' l) y) (Set.Icc 0 T) := fun l =>
    (s8h2_U_cont hd ha hβ hρ hU (hbb l) y).mono Set.Icc_subset_Ici_self
  have hga : ∀ l x', ContinuousOn (fun t => U t (a' l) x') (Set.Icc 0 T) := fun l x' =>
    (s8h2_U_cont hd ha hβ hρ hU (hab l) x').mono Set.Icc_subset_Ici_self
  have hcomm : ∀ l, ∃ V W : ℝ, 0 ≤ V ∧ 0 ≤ W ∧
      S8hCls 1 V W (fun x' => ∫ t in Set.Ioc 0 T, U t (b' l) y * U t (a' l) x') ∧
      projGeneratorW (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) 0
        (fun x' => ∫ t in Set.Ioc 0 T, U t (b' l) y * U t (a' l) x') x =
      ∫ t in Set.Ioc 0 T, U t (b' l) y *
        projGeneratorW (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) 0 (U t (a' l)) x := by
    intro l
    obtain ⟨B, hc2, hB, hcont, hA, -⟩ := s8h2_one hd ha hβ hρ hU hT (hab l)
    obtain ⟨-, ⟨V, W, hV, hW, hcls⟩, hAc⟩ := s8h2_comm hd ha hβ hρ hT (g := fun s => U s (a' l))
      (lam := fun t => U t (b' l) y) hc2 hB hcont (hlam l) hA
    exact ⟨V, W, hV, hW, hcls, hAc x⟩
  choose V W hV hW hcls hAeq using hcomm
  have hint : ∀ l x', IntegrableOn (fun t => U t (b' l) y * U t (a' l) x') (Set.Ioc 0 T) := fun l x' =>
    (((hlam l).mul (hga l x')).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have e : (fun x' => ∫ t in Set.Ioc 0 T, ∑ l, U t (b' l) y * U t (a' l) x') =
      fun x' => ∑ l, (fun _ => (1 : ℝ)) l * (fun l x' => ∫ t in Set.Ioc 0 T, U t (b' l) y * U t (a' l) x') l x' := by
    funext x'
    rw [integral_finset_sum _ (fun l _ => hint l x')]
    simp
  rw [e, s8h2_proj_sum hd ha hβ hρ zero_le_one (fun _ => (1 : ℝ))
    (fun l x' => ∫ t in Set.Ioc 0 T, U t (b' l) y * U t (a' l) x') V W x Finset.univ
    (fun l _ => hV l) (fun l _ => hW l) (fun l _ => hcls l)]
  exact Finset.sum_congr rfl fun l _ => by rw [one_mul, hAeq l]

theorem s8h2_sep_eq (hd : 2 ≤ d) (ha : 0 < a) (hβ : 0 < β)
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ)
    (hU : IsWeightedSemigroup (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) M U)
    {T : ℝ} (hT : 0 < T) {G : Euc d × Euc d → ℝ} (hG : S8hSepZ G) (x y : Euc d) :
    projGeneratorW (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) 0
        (fun x' => ∫ t in Set.Ioc 0 T, s8h2_S U t G (x', y)) x +
      projGeneratorW (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) 0
        (fun y' => ∫ t in Set.Ioc 0 T, s8h2_S U t G (x, y')) y =
      s8h2_S U T G (x, y) - G (x, y) := by
  obtain ⟨ι, _, a', b', hab, rfl⟩ := hG
  have hS : ∀ t, 0 ≤ t → ∀ x' y', s8h2_S U t (fun z => ∑ l, a' l z.1 * b' l z.2) (x', y') =
      ∑ l, U t (b' l) y' * U t (a' l) x' := by
    intro t ht x' y'
    have := s8h2_tensor_sep hU ht (fun l => (hab l).1) (fun l => (hab l).2) x' y'
    unfold s8h2_S
    refine this.trans (Finset.sum_congr rfl fun l _ => mul_comm _ _)
  have hS' : ∀ t, 0 ≤ t → ∀ x' y', s8h2_S U t (fun z => ∑ l, a' l z.1 * b' l z.2) (x', y') =
      ∑ l, U t (a' l) x' * U t (b' l) y' := fun t ht x' y' => by
    rw [hS t ht]; exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  have hx : (fun x' => ∫ t in Set.Ioc 0 T, s8h2_S U t (fun z => ∑ l, a' l z.1 * b' l z.2) (x', y)) =
      fun x' => ∫ t in Set.Ioc 0 T, ∑ l, U t (b' l) y * U t (a' l) x' := by
    funext x'
    exact setIntegral_congr_fun measurableSet_Ioc (fun t ht => hS t ht.1.le x' y)
  have hy : (fun y' => ∫ t in Set.Ioc 0 T, s8h2_S U t (fun z => ∑ l, a' l z.1 * b' l z.2) (x, y')) =
      fun y' => ∫ t in Set.Ioc 0 T, ∑ l, U t (a' l) x * U t (b' l) y' := by
    funext y'
    exact setIntegral_congr_fun measurableSet_Ioc (fun t ht => hS' t ht.1.le x y')
  rw [hx, hy, s8h2_part hd ha hβ hρ hU hT (a' := a') (b' := b') (fun l => (hab l).1) (fun l => (hab l).2) x y,
    s8h2_part hd ha hβ hρ hU hT (a' := b') (b' := a') (fun l => (hab l).2) (fun l => (hab l).1) y x,
    ← Finset.sum_add_distrib]
  have key : ∀ l : ι, (∫ t in Set.Ioc 0 T, U t (b' l) y *
        projGeneratorW (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) 0 (U t (a' l)) x) +
      (∫ t in Set.Ioc 0 T, U t (a' l) x *
        projGeneratorW (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) 0 (U t (b' l)) y) =
      U T (b' l) y * U T (a' l) x - b' l y * a' l x := by
    intro l
    obtain ⟨Ba, hc2a, hBa, hconta, hAa, hdera⟩ := s8h2_one hd ha hβ hρ hU hT (hab l).1
    obtain ⟨Bb, hc2b, hBb, hcontb, hAb, hderb⟩ := s8h2_one hd ha hβ hρ hU hT (hab l).2
    have hUa : ∀ x', ContinuousOn (fun t => U t (a' l) x') (Set.Icc 0 T) := fun x' =>
      (s8h2_U_cont hd ha hβ hρ hU (hab l).1 x').mono Set.Icc_subset_Ici_self
    have hUb : ∀ y', ContinuousOn (fun t => U t (b' l) y') (Set.Icc 0 T) := fun y' =>
      (s8h2_U_cont hd ha hβ hρ hU (hab l).2 y').mono Set.Icc_subset_Ici_self
    have hc1 : ContinuousOn (fun t => U t (b' l) y *
        projGeneratorW (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) 0 (U t (a' l)) x) (Set.Icc 0 T) :=
      (hUb y).mul (hAa x)
    have hc2 : ContinuousOn (fun t => U t (a' l) x *
        projGeneratorW (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) 0 (U t (b' l)) y) (Set.Icc 0 T) :=
      (hUa x).mul (hAb y)
    have hcp : ContinuousOn (fun t => U t (b' l) y * U t (a' l) x) (Set.Icc 0 T) := (hUb y).mul (hUa x)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT.le hcp
      (f' := fun t => U t (b' l) y *
          projGeneratorW (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) 0 (U t (a' l)) x +
        U t (a' l) x *
          projGeneratorW (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) 0 (U t (b' l)) y)
      (fun t ht => ((hderb y t ht).mul (hdera x t ht)).congr_deriv (by ring))
      (by
        rw [← Set.uIcc_of_le hT.le] at hc1 hc2
        exact (hc1.add hc2).intervalIntegrable)
    have hi1 : IntegrableOn (fun t => U t (b' l) y *
        projGeneratorW (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) 0 (U t (a' l)) x) (Set.Ioc 0 T) :=
      hc1.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
    have hi2 : IntegrableOn (fun t => U t (a' l) x *
        projGeneratorW (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) 0 (U t (b' l)) y) (Set.Ioc 0 T) :=
      hc2.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
    rw [← integral_add hi1 hi2, ← intervalIntegral.integral_of_le hT.le]
    try simp only at hftc
    rw [hftc, hU.zero (a' l) (s8h2_cc_memCM M (hab l).1), hU.zero (b' l) (s8h2_cc_memCM M (hab l).2)]
  rw [Finset.sum_congr rfl fun l _ => key l, Finset.sum_sub_distrib, ← hS T hT.le x y]
  congr 1
  refine Finset.sum_congr rfl fun l _ => mul_comm _ _

end Interface

end HRS.MS.Wad

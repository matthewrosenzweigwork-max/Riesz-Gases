import HRS.MS.FixEqP3Aux6

/-!
# S5.7 `fixed_equation` (worker S57P), part 19: terminal-time Duhamel formula

`s57p_td_core`: `D^i (U^{r,T'}φ - φ) = ∫_r^{T'} D^i U^{r,u}(𝓛_u φ) du` (apply `s57p_duhamel` to `h(r) = U^{r,T'}φ - φ`, source `g(u) = 𝓛_uφ`).
`s57p_td_int`: for `r ≤ s ≤ t ≤ T`: `D^i (U^{r,t}φ - U^{r,s}φ) = ∫_s^t D^i U^{r,u}(𝓛_uφ) du`.
`s57p_td_bound`: the bound `|K| C_u B_g (t-s)`.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.FixEq

open HRS HRS.Whole HRS.MP.RdGen HRS.MS.Go HRS.MS.Fcau

variable {d : ℕ}

/-- the constant of `s57p_orb` -/
def s57pCu (θ : Euc d → ℝ) (hθ : IsUlCutoff θ) (j : ℕ) : ℝ := Classical.choose (s57p_orb hθ j)

theorem s57pCu_spec {θ : Euc d → ℝ} (hθ : IsUlCutoff θ) (j : ℕ) :
    0 ≤ s57pCu θ hθ j ∧ ∀ {C : WholeCoeff d} {T K : ℝ}, UlAdjointInput θ C T j K → ∀ {ψ : Euc d → ℝ} {B : ℝ}, 0 ≤ B →
      ContDiff ℝ ((j + 1 + ⌈(d : ℝ) / 2⌉₊ : ℕ) : WithTop ℕ∞) ψ →
      (∀ l ≤ j + 1 + ⌈(d : ℝ) / 2⌉₊, ∀ x, ‖iteratedFDeriv ℝ l ψ x‖ ≤ B) → ∀ t ∈ Set.Icc (0 : ℝ) T,
      IsClassicalAdjointW C t ψ (fun r => propagatorW C r t ψ) ∧
      ∀ r ∈ Set.Icc (0 : ℝ) t, ContDiff ℝ j (propagatorW C r t ψ) ∧
        ∀ i ≤ j, ∀ x, ‖iteratedFDeriv ℝ i (propagatorW C r t ψ) x‖ ≤ |K| * (s57pCu θ hθ j * B) :=
  Classical.choose_spec (s57p_orb hθ j)

theorem s57p_orbfam {C : WholeCoeff d} {θ : Euc d → ℝ} {T : ℝ} {n : ℕ} {K : ℝ} (hθ : IsUlCutoff θ)
    (Fm : S57pFam C θ T (n + 1) K) (hn4 : 4 ≤ n) {φ : Euc d → ℝ} {Bφ Bg : ℝ} (hBφ : 0 ≤ Bφ) (hBg : 0 ≤ Bg)
    (hφ : ContDiff ℝ ((n + 1 + 1 + ⌈(d : ℝ) / 2⌉₊ : ℕ) : WithTop ℕ∞) φ)
    (hφb : ∀ l ≤ n + 1 + 1 + ⌈(d : ℝ) / 2⌉₊, ∀ x, ‖iteratedFDeriv ℝ l φ x‖ ≤ Bφ)
    (hg : ∀ u ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ ((n + 1 + 1 + ⌈(d : ℝ) / 2⌉₊ : ℕ) : WithTop ℕ∞) (generatorW C u φ) ∧
      ∀ l ≤ n + 1 + 1 + ⌈(d : ℝ) / 2⌉₊, ∀ x, ‖iteratedFDeriv ℝ l (generatorW C u φ) x‖ ≤ Bg) :
    (Continuous fun p : Set.Icc (0 : ℝ) T × Euc d => generatorW C p.1 φ p.2) ∧
    S57pOrbFam C T n (|K| * (s57pCu θ hθ (n + 1) * Bg)) (fun u => generatorW C u φ) := by
  obtain ⟨hCu0, hCu⟩ := s57pCu_spec hθ (n + 1)
  have hφ4 : ContDiff ℝ 4 φ := hφ.of_le (by exact_mod_cast (by omega : 4 ≤ n + 1 + 1 + ⌈(d : ℝ) / 2⌉₊))
  obtain ⟨K1, hK1, hgen⟩ := Fm.gen.bound
  have hjc : Continuous fun p : Set.Icc (0 : ℝ) T × Euc d => generatorW C p.1 φ p.2 :=
    s57p_cont_gen Fm.gen (B := Bφ) (K := K1) (L := 0) hBφ hK1
      (fun τ hτ u hu hub => hgen τ hτ Bφ u hBφ hu hub) (g := fun _ => φ)
      (fun _ => ⟨hφ4, fun j hj x => hφb j (by omega) x⟩) (fun r r' x => by simp)
  refine ⟨hjc, fun y => s57p_contOn_of_cont hjc y, fun u hu => ?_, fun u hu r' hr' => ?_⟩
  · exact (hCu Fm.adj hBg (hg u hu).1 (hg u hu).2 u hu).1
  · exact ((hCu Fm.adj hBg (hg u hu).1 (hg u hu).2 u hu).2 r' hr').imp_right fun h => h

theorem s57p_td_core {C : WholeCoeff d} {θ : Euc d → ℝ} {T : ℝ} {n : ℕ} {K : ℝ} (hθ : IsUlCutoff θ)
    (Fm : S57pFam C θ T (n + 1) K) (hn4 : 4 ≤ n) {φ : Euc d → ℝ} {Bφ Bg : ℝ} (hBφ : 0 ≤ Bφ) (hBg : 0 ≤ Bg)
    (hφ : ContDiff ℝ ((n + 1 + 1 + ⌈(d : ℝ) / 2⌉₊ : ℕ) : WithTop ℕ∞) φ)
    (hφb : ∀ l ≤ n + 1 + 1 + ⌈(d : ℝ) / 2⌉₊, ∀ x, ‖iteratedFDeriv ℝ l φ x‖ ≤ Bφ)
    (hg : ∀ u ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ ((n + 1 + 1 + ⌈(d : ℝ) / 2⌉₊ : ℕ) : WithTop ℕ∞) (generatorW C u φ) ∧
      ∀ l ≤ n + 1 + 1 + ⌈(d : ℝ) / 2⌉₊, ∀ x, ‖iteratedFDeriv ℝ l (generatorW C u φ) x‖ ≤ Bg)
    {T' : ℝ} (hT' : T' ∈ Set.Icc (0 : ℝ) T) :
    ∀ r ∈ Set.Icc (0 : ℝ) T', ∀ i ≤ n, ∀ x,
      iteratedFDeriv ℝ i (fun y => propagatorW C r T' φ y - φ y) x =
        ∫ u in r..T', iteratedFDeriv ℝ i (propagatorW C r u (generatorW C u φ)) x := by
  obtain ⟨hCu0, hCu⟩ := s57pCu_spec hθ (n + 1)
  set Cu := s57pCu θ hθ (n + 1) with hCudef
  have F' := Fm.mono hT'.2
  have hT0 : 0 ≤ T' := hT'.1
  have hT'T : ∀ τ ∈ Set.Icc (0 : ℝ) T', τ ∈ Set.Icc (0 : ℝ) T := fun τ hτ => ⟨hτ.1, hτ.2.trans hT'.2⟩
  have hφ4 : ContDiff ℝ 4 φ := hφ.of_le (by exact_mod_cast (by omega : 4 ≤ n + 1 + 1 + ⌈(d : ℝ) / 2⌉₊))
  have hφ3 : ContDiff ℝ 3 φ := hφ.of_le (by exact_mod_cast (by omega : 3 ≤ n + 1 + 1 + ⌈(d : ℝ) / 2⌉₊))
  obtain ⟨hclφ, hOφ⟩ := hCu F'.adj hBφ hφ hφb T' ⟨hT0, le_rfl⟩
  set BF : ℝ := |K| * (Cu * Bφ) with hBF
  set BO : ℝ := |K| * (Cu * Bg) with hBO
  have hBO0 : 0 ≤ BO := by positivity
  obtain ⟨K1, hK1, hgen⟩ := F'.gen.bound
  obtain ⟨hjc, hOrb⟩ := s57p_orbfam hθ F' hn4 hBφ hBg hφ hφb (fun u hu => hg u (hT'T u hu))
  -- the difference `h`
  set h : ℝ → Euc d → ℝ := fun r x => propagatorW C r T' φ x - φ x with hh
  have hsub : ∀ r ∈ Set.Icc (0 : ℝ) T', ∀ x, generatorW C r (h r) x =
      generatorW C r (propagatorW C r T' φ) x - generatorW C r φ x := by
    intro r hr x
    exact F'.lin.sub r hr (max BF Bφ) _ _ ((hOφ r hr).1.of_le (by exact_mod_cast (by omega : 3 ≤ n + 1)))
      hφ3 (fun i hi y => ((hOφ r hr).2 i (by omega) y).trans (le_max_left _ _))
      (fun i hi y => (hφb i (by omega) y).trans (le_max_right _ _)) x
  have hc3 : ∀ r ∈ Set.Icc (0 : ℝ) T', ContDiff ℝ 3 (h r) ∧ ∀ i ≤ 3, ∀ x, ‖iteratedFDeriv ℝ i (h r) x‖ ≤ BF + Bφ := by
    intro r hr
    have c1 : ContDiff ℝ 3 (propagatorW C r T' φ) := (hOφ r hr).1.of_le (by exact_mod_cast (by omega : 3 ≤ n + 1))
    refine ⟨c1.sub hφ3, fun i hi x => ?_⟩
    have e : iteratedFDeriv ℝ i (h r) x = iteratedFDeriv ℝ i (propagatorW C r T' φ) x - iteratedFDeriv ℝ i φ x :=
      iteratedFDeriv_sub_apply (c1.of_le (by exact_mod_cast hi)).contDiffAt (hφ3.of_le (by exact_mod_cast hi)).contDiffAt
    rw [e]
    exact (norm_sub_le _ _).trans (add_le_add ((hOφ r hr).2 i (by omega) x) (hφb i (by omega) x))
  have hcont : ∀ i ≤ 2, Continuous fun p : Set.Icc (0 : ℝ) T' × Euc d => iteratedFDeriv ℝ i (h p.1) p.2 := by
    intro i hi
    have h1 := hclφ.cont_c2 i hi
    have h2 : Continuous fun p : Set.Icc (0 : ℝ) T' × Euc d => iteratedFDeriv ℝ i φ p.2 :=
      ((hφ3.continuous_iteratedFDeriv (by exact_mod_cast (by omega : i ≤ 3))).comp continuous_snd)
    refine (h1.sub h2).congr fun p => ?_
    have c1 : ContDiff ℝ 3 (propagatorW C p.1 T' φ) := (hOφ p.1 p.1.2).1.of_le (by exact_mod_cast (by omega : 3 ≤ n + 1))
    have e : iteratedFDeriv ℝ i (h p.1) p.2 = iteratedFDeriv ℝ i (propagatorW C p.1 T' φ) p.2 - iteratedFDeriv ℝ i φ p.2 :=
      iteratedFDeriv_sub_apply (c1.of_le (by exact_mod_cast (by omega : i ≤ 3))).contDiffAt
        (hφ3.of_le (by exact_mod_cast (by omega : i ≤ 3))).contDiffAt
    simp only [Pi.sub_apply]
    rw [e]
  have hterm : h T' = 0 := by
    funext x
    have := congrFun hclφ.terminal x
    simp only [hh, Pi.zero_apply]
    rw [this]; ring
  have hode : ∀ x, ∀ r ∈ Set.Ioo 0 T', HasDerivAt (fun r' => h r' x)
      (-(generatorW C r (h r) x) - generatorW C r φ x) r := by
    intro x r hr
    have hr' : r ∈ Set.Icc (0 : ℝ) T' := ⟨hr.1.le, hr.2.le⟩
    have := (hclφ.time_deriv x r hr).sub_const (φ x)
    convert this using 1
    rw [hsub r hr' x]; ring
  have hgc : Continuous fun p : Set.Icc (0 : ℝ) T' × Euc d => generatorW C p.1 (h p.1) p.2 := by
    refine (hclφ.cont_time_deriv.sub hjc).congr fun p => ?_
    simp only [Pi.sub_apply]
    rw [hsub p.1 p.1.2 p.2]
  have hgb : ∃ Bg' : ℝ, ∀ r ∈ Set.Icc (0 : ℝ) T', ∀ x, |generatorW C r (h r) x| ≤ Bg' * (1 + ‖x‖) := by
    obtain ⟨Bt, hBt⟩ := hclφ.bdd_time_deriv
    refine ⟨Bt + Bφ * K1, fun r hr x => ?_⟩
    rw [hsub r hr x]
    have h1 := hBt r hr x
    have h2 := (hgen r hr Bφ φ hBφ hφ4 (fun n' hn' x => hφb n' (by omega) x)).2 0 (by norm_num) x
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h2
    calc |generatorW C r (propagatorW C r T' φ) x - generatorW C r φ x|
        ≤ |generatorW C r (propagatorW C r T' φ) x| + |generatorW C r φ x| := abs_sub _ _
      _ ≤ Bt * (1 + ‖x‖) + Bφ * K1 * (1 + ‖x‖) := add_le_add h1 h2
      _ = (Bt + Bφ * K1) * (1 + ‖x‖) := by ring
  exact s57p_duhamel F'.gen F'.lin F'.uniq hn4 hBO0 hOrb hT0 hc3 hcont hterm hode hgc hgb

theorem s57p_td_int {C : WholeCoeff d} {θ : Euc d → ℝ} {T : ℝ} {n : ℕ} {K : ℝ} (hθ : IsUlCutoff θ)
    (Fm : S57pFam C θ T (n + 1) K) (hn4 : 4 ≤ n) {φ : Euc d → ℝ} {Bφ Bg : ℝ} (hBφ : 0 ≤ Bφ) (hBg : 0 ≤ Bg)
    (hφ : ContDiff ℝ ((n + 1 + 1 + ⌈(d : ℝ) / 2⌉₊ : ℕ) : WithTop ℕ∞) φ)
    (hφb : ∀ l ≤ n + 1 + 1 + ⌈(d : ℝ) / 2⌉₊, ∀ x, ‖iteratedFDeriv ℝ l φ x‖ ≤ Bφ)
    (hg : ∀ u ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ ((n + 1 + 1 + ⌈(d : ℝ) / 2⌉₊ : ℕ) : WithTop ℕ∞) (generatorW C u φ) ∧
      ∀ l ≤ n + 1 + 1 + ⌈(d : ℝ) / 2⌉₊, ∀ x, ‖iteratedFDeriv ℝ l (generatorW C u φ) x‖ ≤ Bg)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
    ∀ r ∈ Set.Icc (0 : ℝ) s, ∀ i ≤ n, ∀ x,
      iteratedFDeriv ℝ i (fun y => propagatorW C r t φ y - propagatorW C r s φ y) x =
        ∫ u in s..t, iteratedFDeriv ℝ i (propagatorW C r u (generatorW C u φ)) x := by
  obtain ⟨hCu0, hCu⟩ := s57pCu_spec hθ (n + 1)
  set Cu := s57pCu θ hθ (n + 1) with hCudef
  intro r hr i hi x
  have hsT : s ∈ Set.Icc (0 : ℝ) T := ⟨hs, hst.trans ht⟩
  have htT : t ∈ Set.Icc (0 : ℝ) T := ⟨hs.trans hst, ht⟩
  have c1 := s57p_td_core hθ Fm hn4 hBφ hBg hφ hφb hg htT r ⟨hr.1, hr.2.trans hst⟩ i hi x
  have c2 := s57p_td_core hθ Fm hn4 hBφ hBg hφ hφb hg hsT r hr i hi x
  have hφ0 : ContDiff ℝ ((n + 1 + 1 + ⌈(d : ℝ) / 2⌉₊ : ℕ) : WithTop ℕ∞) φ := hφ
  have hr0 : 0 ≤ r := hr.1
  have hrt : r ≤ t := hr.2.trans hst
  have hφ1 : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (propagatorW C r t φ) :=
    ((hCu Fm.adj hBφ hφ hφb t htT).2 r ⟨hr0, hrt⟩).1
  have hφ2 : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (propagatorW C r s φ) :=
    ((hCu Fm.adj hBφ hφ hφb s hsT).2 r hr).1
  have e : iteratedFDeriv ℝ i (fun y => propagatorW C r t φ y - propagatorW C r s φ y) x =
      iteratedFDeriv ℝ i (fun y => propagatorW C r t φ y - φ y) x -
        iteratedFDeriv ℝ i (fun y => propagatorW C r s φ y - φ y) x := by
    have h1 : ContDiff ℝ (i : WithTop ℕ∞) (propagatorW C r t φ) := hφ1.of_le (by exact_mod_cast (by omega : i ≤ n + 1))
    have h2 : ContDiff ℝ (i : WithTop ℕ∞) (propagatorW C r s φ) := hφ2.of_le (by exact_mod_cast (by omega : i ≤ n + 1))
    have h3 : ContDiff ℝ (i : WithTop ℕ∞) φ :=
      hφ0.of_le (by exact_mod_cast (by omega : i ≤ n + 1 + 1 + ⌈(d : ℝ) / 2⌉₊))
    have e1 : iteratedFDeriv ℝ i (fun y => propagatorW C r t φ y - propagatorW C r s φ y) x =
        iteratedFDeriv ℝ i (propagatorW C r t φ) x - iteratedFDeriv ℝ i (propagatorW C r s φ) x :=
      iteratedFDeriv_sub_apply h1.contDiffAt h2.contDiffAt
    have e2 : iteratedFDeriv ℝ i (fun y => propagatorW C r t φ y - φ y) x =
        iteratedFDeriv ℝ i (propagatorW C r t φ) x - iteratedFDeriv ℝ i φ x :=
      iteratedFDeriv_sub_apply h1.contDiffAt h3.contDiffAt
    have e3 : iteratedFDeriv ℝ i (fun y => propagatorW C r s φ y - φ y) x =
        iteratedFDeriv ℝ i (propagatorW C r s φ) x - iteratedFDeriv ℝ i φ x :=
      iteratedFDeriv_sub_apply h2.contDiffAt h3.contDiffAt
    rw [e1, e2, e3]
    abel
  rw [e, c1, c2]
  obtain ⟨-, hOrb⟩ := s57p_orbfam hθ Fm hn4 hBφ hBg hφ hφb hg
  have hBO0 : 0 ≤ |K| * (Cu * Bg) := by positivity
  have hcc := s57p_jet_continuousOn Fm.gen Fm.uniq hn4 hBO0 (fun u => generatorW C u φ) hOrb.cont hOrb.classical
    hOrb.bound hr0 hi x
  have hBO : ∀ u ∈ Set.Ioc r T, ‖iteratedFDeriv ℝ i (propagatorW C r u (generatorW C u φ)) x‖ ≤ |K| * (Cu * Bg) := by
    intro u hu
    exact (hOrb.bound u ⟨hr0.trans hu.1.le, hu.2⟩ r ⟨hr0, hu.1.le⟩).2 i (by omega) x
  have hI : ∀ b, r ≤ b → b ≤ t →
      IntervalIntegrable (fun u => iteratedFDeriv ℝ i (propagatorW C r u (generatorW C u φ)) x) volume r b := by
    intro b hrb hbt
    exact s57p_ii_of_bound hrb (hcc.mono (Set.Ioc_subset_Ioc_right (hbt.trans ht)))
      (fun u hu => hBO u ⟨hu.1, hu.2.trans (hbt.trans ht)⟩)
  exact intervalIntegral.integral_interval_sub_left (hI t hrt le_rfl) (hI s hr.2 hst)

end HRS.MS.FixEq

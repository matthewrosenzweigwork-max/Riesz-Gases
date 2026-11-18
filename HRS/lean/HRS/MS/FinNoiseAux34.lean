import HRS.Torus.Basic

/-!
# S8.6 `finite_noise`: periodisation of a function with compact support in the open cube (S86b)

`s86_periodize`: if `g : ℝ^d → E` is `C^r` with compact support inside `(-1/2,1/2)^d`, then `G(y) = ∑_{n∈ℤ^d} g(y+n)` (a
locally finite sum) is `ℤ^d`-periodic and `C^r`, equals `g` on the closed cube `[-1/2,1/2]^d`, and its derivatives are
bounded by any common bound of the derivatives of `g` (at most one term is non-zero at each point).  Used for the
zero-collar periodic extension of the localised features (Pro FR05).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped BigOperators

namespace HRS.MS.FinNoise

open HRS HRS.Torus

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem s86_toEuc_add (m n : Lattice d) :
    Lattice.toEuc (m + n) = Lattice.toEuc m + Lattice.toEuc n := by
  ext i; simp [Lattice.toEuc]

theorem s86_finite_lattice_ball (ρ : ℝ) : {n : Lattice d | ‖Lattice.toEuc n‖ ≤ ρ}.Finite := by
  have hsub : {n : Lattice d | ‖Lattice.toEuc n‖ ≤ ρ} ⊆
      Set.pi Set.univ (fun _ : Fin d => Set.Icc (-⌈ρ⌉) ⌈ρ⌉) := by
    intro n hn i _
    have h := PiLp.norm_apply_le (Lattice.toEuc n) i
    have h2 : |(n i : ℝ)| ≤ ρ := by
      have : ‖(Lattice.toEuc n) i‖ = |(n i : ℝ)| := by simp [Lattice.toEuc]
      rw [← this]; exact h.trans hn
    have h3 := abs_le.mp h2
    constructor
    · have : (-(⌈ρ⌉ : ℤ) : ℝ) ≤ n i := by
        have := Int.le_ceil ρ
        linarith [h3.1]
      exact_mod_cast this
    · have : (n i : ℝ) ≤ (⌈ρ⌉ : ℤ) := h3.2.trans (Int.le_ceil ρ)
      exact_mod_cast this
  exact (Set.Finite.pi (fun _ => Set.finite_Icc _ _)).subset hsub

/-- The periodisation `y ↦ ∑ᶠ_n g(y + n)`. -/
def s86_per (g : Euc d → E) (y : Euc d) : E := ∑ᶠ n : Lattice d, g (y + Lattice.toEuc n)

theorem s86_per_local (g : Euc d → E) (hc : HasCompactSupport g) (y₀ : Euc d) :
    ∃ F : Finset (Lattice d), ∀ᶠ y in 𝓝 y₀, s86_per g y = ∑ n ∈ F, g (y + Lattice.toEuc n) ∧
      ∀ n ∉ F, y + Lattice.toEuc n ∉ tsupport g := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : Euc d)
  set ρ : ℝ := ‖y₀‖ + 1 + R with hρ
  have hfin := s86_finite_lattice_ball (d := d) ρ
  refine ⟨hfin.toFinset, ?_⟩
  filter_upwards [Metric.ball_mem_nhds y₀ one_pos] with y hy
  have hy' : ‖y‖ < ‖y₀‖ + 1 := by
    have := norm_le_norm_add_norm_sub' y y₀
    rw [mem_ball_iff_norm] at hy
    have h2 : ‖y‖ ≤ ‖y₀‖ + ‖y - y₀‖ := norm_le_insert' y y₀
    linarith
  have hnot : ∀ n ∉ hfin.toFinset, y + Lattice.toEuc n ∉ tsupport g := by
    intro n hn hmem
    have h1 := hR hmem
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    have h2 : ρ < ‖Lattice.toEuc n‖ := by
      by_contra hcon
      exact hn (by simpa using not_lt.mp hcon)
    have h3 : ‖Lattice.toEuc n‖ ≤ ‖y + Lattice.toEuc n‖ + ‖y‖ := by
      have := norm_le_add_norm_add (Lattice.toEuc n) y
      rwa [add_comm (Lattice.toEuc n) y] at this
    linarith
  refine ⟨?_, hnot⟩
  unfold s86_per
  refine finsum_eq_sum_of_support_subset _ ?_
  intro n hn
  by_contra hn'
  exact hnot n hn' (subset_tsupport _ hn)

theorem s86_per_contDiff (g : Euc d → E) (hc : HasCompactSupport g) {r : ℕ}
    (hg : ContDiff ℝ r g) : ContDiff ℝ r (s86_per g) := by
  rw [contDiff_iff_contDiffAt]
  intro y₀
  obtain ⟨F, hF⟩ := s86_per_local g hc y₀
  have : ContDiff ℝ r (fun y => ∑ n ∈ F, g (y + Lattice.toEuc n)) :=
    ContDiff.sum fun n _ => hg.comp (contDiff_id.add contDiff_const)
  exact this.contDiffAt.congr_of_eventuallyEq (hF.mono fun y hy => hy.1)

theorem s86_per_periodic (g : Euc d → E) (y : Euc d) (m : Lattice d) :
    s86_per g (y + Lattice.toEuc m) = s86_per g y := by
  unfold s86_per
  have := finsum_comp_equiv (Equiv.addLeft m) (f := fun n : Lattice d => g (y + Lattice.toEuc n))
  rw [← this]
  refine finsum_congr fun n => ?_
  simp only [Equiv.coe_addLeft, s86_toEuc_add]
  congr 1
  abel

theorem s86_cube_unique {y : Euc d} {n n' : Lattice d}
    (h : y + Lattice.toEuc n ∈ {u : Euc d | ∀ i, |u i| < 1 / 2})
    (h' : y + Lattice.toEuc n' ∈ {u : Euc d | ∀ i, |u i| < 1 / 2}) : n = n' := by
  funext i
  have h1 := h i
  have h2 := h' i
  simp only [PiLp.add_apply, Lattice.toEuc] at h1 h2
  have h3 : |((n i : ℤ) : ℝ) - (n' i : ℝ)| < 1 := by
    have := abs_sub (y i + (n i : ℝ)) (y i + (n' i : ℝ))
    calc |((n i : ℤ) : ℝ) - (n' i : ℝ)| = |(y i + (n i : ℝ)) - (y i + (n' i : ℝ))| := by ring_nf
      _ ≤ |y i + (n i : ℝ)| + |y i + (n' i : ℝ)| := this
      _ < 1 := by linarith
  have h4 : |(n i) - (n' i)| < 1 := by exact_mod_cast h3
  have : n i - n' i = 0 := by
    have := abs_lt.mp h4
    omega
  omega

theorem s86_periodize (g : Euc d → E) (r : ℕ) (hg : ContDiff ℝ r g) (hc : HasCompactSupport g)
    (hsupp : tsupport g ⊆ {u | ∀ i, |u i| < 1 / 2}) :
    ∃ G : Euc d → E, (∀ (y : Euc d) (n : Lattice d), G (y + Lattice.toEuc n) = G y) ∧
      ContDiff ℝ r G ∧ (∀ u : Euc d, (∀ i, |u i| ≤ 1 / 2) → G u = g u) ∧
      ∀ l ≤ r, ∀ C : ℝ, 0 ≤ C → (∀ x, ‖iteratedFDeriv ℝ l g x‖ ≤ C) →
        ∀ y, ‖iteratedFDeriv ℝ l G y‖ ≤ C := by
  classical
  refine ⟨s86_per g, s86_per_periodic g, s86_per_contDiff g hc hg, ?_, ?_⟩
  · intro u hu
    unfold s86_per
    rw [finsum_eq_single _ 0]
    · have h0 : Lattice.toEuc (0 : Lattice d) = 0 := by ext i; simp [Lattice.toEuc]
      rw [h0, add_zero]
    · intro n hn
      by_contra hne
      have hmem : u + Lattice.toEuc n ∈ tsupport g := subset_tsupport _ (by simpa using hne)
      have h1 := hsupp hmem
      apply hn
      funext i
      have h2 := h1 i
      have h3 := hu i
      simp only [PiLp.add_apply, Lattice.toEuc] at h2
      have h4 : |(n i : ℝ)| < 1 := by
        calc |(n i : ℝ)| = |(u i + (n i : ℝ)) - u i| := by ring_nf
          _ ≤ |u i + (n i : ℝ)| + |u i| := abs_sub _ _
          _ < 1 := by linarith
      have h5 : |n i| < 1 := by exact_mod_cast h4
      have := abs_lt.mp h5
      simp only [Pi.zero_apply]
      omega
  · intro l hl C hC0 hC y
    obtain ⟨F, hF⟩ := s86_per_local g hc y
    have hev : s86_per g =ᶠ[𝓝 y] fun z => ∑ n ∈ F, g (z + Lattice.toEuc n) :=
      hF.mono fun z hz => hz.1
    have hshift : ∀ n, ContDiff ℝ r (fun z => g (z + Lattice.toEuc n)) := fun n =>
      hg.comp (contDiff_id.add contDiff_const)
    have h1 : iteratedFDeriv ℝ l (s86_per g) y =
        iteratedFDeriv ℝ l (fun z => ∑ n ∈ F, g (z + Lattice.toEuc n)) y := by
      have := Filter.EventuallyEq.iteratedFDerivWithin_eq (𝕜 := ℝ)
        (hev.filter_mono (nhdsWithin_le_nhds (s := Set.univ)))
        (by simpa using hev.eq_of_nhds) l
      simpa [iteratedFDerivWithin_univ] using this
    rw [h1, iteratedFDeriv_fun_sum_apply (fun n _ => (hshift n).contDiffAt.of_le (by exact_mod_cast hl))]
    simp_rw [iteratedFDeriv_comp_add_right]
    by_cases hex : ∃ n₀ ∈ F, y + Lattice.toEuc n₀ ∈ tsupport g
    · obtain ⟨n₀, hn₀, hmem⟩ := hex
      rw [Finset.sum_eq_single_of_mem n₀ hn₀]
      · exact hC _
      · intro n _ hne
        by_cases hm : y + Lattice.toEuc n ∈ tsupport g
        · exact absurd (s86_cube_unique (hsupp hm) (hsupp hmem)) hne
        · have : y + Lattice.toEuc n ∉ Function.support (iteratedFDeriv ℝ l g) := fun h =>
            hm (support_iteratedFDeriv_subset l h)
          simpa using this
    · push Not at hex
      have : ∀ n ∈ F, iteratedFDeriv ℝ l g (y + Lattice.toEuc n) = 0 := by
        intro n hn
        have : y + Lattice.toEuc n ∉ Function.support (iteratedFDeriv ℝ l g) := fun h =>
          hex n hn (support_iteratedFDeriv_subset l h)
        simpa using this
      rw [Finset.sum_eq_zero this]
      simpa using hC0

end HRS.MS.FinNoise

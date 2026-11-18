import HRS.MS.FixEqP2Aux4

/-!
# S5.7 `fixed_equation` (worker S57P), part 8: inhomogeneous Duhamel formula for classical adjoint solutions

For a source `g : [0,T] → functions` whose orbits `F(r,u) = U^{r,u} g(u)` are classical and bounded in `C^{n+1}` uniformly
(`S57pOrbFam`), every `h` with `-∂_r h = 𝓛_r h + g_r`, `h_T = 0` (classical regularity, `C^3`) satisfies
`D^i h(r) = ∫_r^T D^i F(r,u) du`, `i ≤ n`.  Proof: `Z(r) = ∫_r^T F(r,u) du` is a classical solution of the same equation
(`D^iZ = ∫ D^iF` by `s57p_param_jets`; the right derivative from the difference quotients of `F` in `r`, dominated
convergence, and the commutation `S57pLin.comm`), and `h - Z` is a classical solution with zero datum, hence `0` by the
uniqueness hypothesis `S52bUniq`.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.FixEq

open HRS HRS.Whole HRS.MP.RdGen HRS.MS.Go HRS.MS.Fcau

variable {d : ℕ}

/-- hypotheses on the orbit family `F(r,u) = U^{r,u} g(u)` of a source `g` -/
structure S57pOrbFam (C : WholeCoeff d) (T : ℝ) (n : ℕ) (B : ℝ) (g : ℝ → Euc d → ℝ) : Prop where
  cont : ∀ y, ContinuousOn (fun u => g u y) (Set.Icc (0 : ℝ) T)
  classical : ∀ u ∈ Set.Icc (0 : ℝ) T, IsClassicalAdjointW C u (g u) (fun r => propagatorW C r u (g u))
  bound : ∀ u ∈ Set.Icc (0 : ℝ) T, ∀ r' ∈ Set.Icc (0 : ℝ) u, ContDiff ℝ (n + 1 : ℕ) (propagatorW C r' u (g u)) ∧
    ∀ j ≤ n + 1, ∀ y, ‖iteratedFDeriv ℝ j (propagatorW C r' u (g u)) y‖ ≤ B

section Duhamel

variable {C : WholeCoeff d} {T : ℝ} {n : ℕ} {B : ℝ} {g : ℝ → Euc d → ℝ}

/-- the integral `Z(r) = ∫_r^T U^{r,u} g(u) du` -/
def s57pZ (C : WholeCoeff d) (g : ℝ → Euc d → ℝ) (T r : ℝ) : Euc d → ℝ :=
  fun x => ∫ u in r..T, propagatorW C r u (g u) x

theorem s57p_Z_jets (G : S57pGen C T) (huniq : HRS.MS.S52B.S52bUniq C T) (hn4 : 4 ≤ n) (hB0 : 0 ≤ B)
    (O : S57pOrbFam C T n B g) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) :
    ContDiff ℝ n (s57pZ C g T r) ∧ ∀ j ≤ n, ∀ y, iteratedFDeriv ℝ j (s57pZ C g T r) y =
      ∫ u in r..T, iteratedFDeriv ℝ j (propagatorW C r u (g u)) y := by
  refine s57p_param_jets n hr.2 (B := B) (F := fun u => propagatorW C r u (g u)) ?_ ?_
  · intro u hu
    exact O.bound u ⟨hr.1.trans hu.1.le, hu.2⟩ r ⟨hr.1, hu.1.le⟩
  · intro j hj y
    exact s57p_jet_continuousOn G huniq hn4 hB0 g O.cont O.classical O.bound hr.1 hj y

/-- uniform bounds of the generator along the orbits and Lipschitz continuity of the orbits in `r` -/
theorem s57p_F_lip (G : S57pGen C T) (hn4 : 4 ≤ n) (hB0 : 0 ≤ B) (O : S57pOrbFam C T n B g) :
    ∃ BL : ℝ, 0 ≤ BL ∧ ∀ u ∈ Set.Icc (0 : ℝ) T,
      (∀ τ ∈ Set.Icc (0 : ℝ) u, ∀ x, |generatorW C τ (propagatorW C τ u (g u)) x| ≤ BL * (1 + ‖x‖)) ∧
      ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ u → ∀ x,
        |propagatorW C a u (g u) x - propagatorW C b u (g u) x| ≤ BL * (1 + ‖x‖) * (b - a) := by
  obtain ⟨K, hK0, hgen⟩ := G.bound
  refine ⟨B * K, mul_nonneg hB0 hK0, fun u hu => ?_⟩
  have hgl : ∀ τ ∈ Set.Icc (0 : ℝ) u, ∀ x, |generatorW C τ (propagatorW C τ u (g u)) x| ≤ B * K * (1 + ‖x‖) := by
    intro τ hτ x
    have hτT : τ ∈ Set.Icc (0 : ℝ) T := ⟨hτ.1, hτ.2.trans hu.2⟩
    obtain ⟨h1, h2⟩ := O.bound u hu τ hτ
    have := (hgen τ hτT B (propagatorW C τ u (g u)) hB0 (h1.of_le (by exact_mod_cast (by omega : 4 ≤ n + 1)))
      (fun j hj => h2 j (by omega))).2 0 (by norm_num) x
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  refine ⟨hgl, fun a b ha hab hbu x => ?_⟩
  exact s55m_lip_r (O.classical u hu) (BL := B * K) hgl ha hab hbu x

/-- the jets of the orbit are continuous in `(r,x)` (clamped in `r`) -/
theorem s57p_orb_jet_continuous (O : S57pOrbFam C T n B g) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) T) {j : ℕ}
    (hj : j ≤ 2) :
    Continuous fun q : ℝ × Euc d => iteratedFDeriv ℝ j (propagatorW C (max 0 (min q.1 u)) u (g u)) q.2 := by
  have h := (O.classical u hu).cont_c2 j hj
  have hcl : Continuous fun q : ℝ × Euc d => ((⟨max 0 (min q.1 u), le_max_left _ _,
      max_le hu.1 (min_le_right _ _)⟩ : Set.Icc (0 : ℝ) u), q.2) :=
    (((continuous_const.max ((continuous_fst).min continuous_const)).subtype_mk _).prodMk continuous_snd)
  exact h.comp hcl

/-- jets of `Z` are jointly continuous in `(r,x)` -/
theorem s57p_Z_jet_cont (G : S57pGen C T) (huniq : HRS.MS.S52B.S52bUniq C T) (hn4 : 4 ≤ n) (hB0 : 0 ≤ B)
    (O : S57pOrbFam C T n B g) {j : ℕ} (hj : j ≤ 2) :
    Continuous fun p : Set.Icc (0 : ℝ) T × Euc d => iteratedFDeriv ℝ j (s57pZ C g T p.1) p.2 := by
  refine continuous_iff_seqContinuous.2 fun pm p₀ hp => ?_
  set μ : Measure ℝ := volume.restrict (Set.Ioc 0 T) with hμ
  haveI : IsFiniteMeasure μ := ⟨by simp [hμ]⟩
  have hae : ∀ᵐ u ∂μ, u ∈ Set.Ioc 0 T := by rw [hμ]; exact ae_restrict_mem measurableSet_Ioc
  have hne : ∀ᵐ u ∂μ, u ≠ (p₀.1 : ℝ) := by
    rw [hμ]
    exact ae_restrict_of_ae ((Set.countable_singleton (p₀.1 : ℝ)).ae_notMem volume)
  set J : ℝ → Euc d → ℝ → (Euc d [×j]→L[ℝ] ℝ) := fun r x u => (Set.Ioi r).indicator
    (fun u => iteratedFDeriv ℝ j (propagatorW C r u (g u)) x) u with hJ
  have hrepr : ∀ p : Set.Icc (0 : ℝ) T × Euc d, iteratedFDeriv ℝ j (s57pZ C g T p.1) p.2 =
      ∫ u, J p.1 p.2 u ∂μ := by
    intro p
    rw [(s57p_Z_jets G huniq hn4 hB0 O p.1.2).2 j (by omega) p.2, intervalIntegral.integral_of_le p.1.2.2]
    rw [hμ, hJ]
    rw [setIntegral_indicator measurableSet_Ioi]
    have hset : Set.Ioc (p.1 : ℝ) T = Set.Ioc 0 T ∩ Set.Ioi (p.1 : ℝ) := by
      ext u; simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ioi]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨⟨p.1.2.1.trans_lt h1, h2⟩, h1⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h3, h2⟩
    rw [hset]
  simp only [hrepr]
  have hr : Tendsto (fun i => ((pm i).1 : ℝ)) atTop (𝓝 (p₀.1 : ℝ)) :=
    ((continuous_subtype_val.comp continuous_fst).tendsto _).comp hp
  have hx : Tendsto (fun i => (pm i).2) atTop (𝓝 p₀.2) := (continuous_snd.tendsto _).comp hp
  have huT : ∀ u ∈ Set.Ioc (0 : ℝ) T, u ∈ Set.Icc (0 : ℝ) T := fun u hu => ⟨hu.1.le, hu.2⟩
  refine tendsto_integral_of_dominated_convergence (fun _ => B) ?_ (integrable_const _) ?_ ?_
  · intro i
    set r := ((pm i).1 : ℝ) with hri
    have hrt : r ∈ Set.Icc (0 : ℝ) T := (pm i).1.2
    have hc : ContinuousOn (fun u => iteratedFDeriv ℝ j (propagatorW C r u (g u)) (pm i).2) (Set.Ioc r T) :=
      s57p_jet_continuousOn G huniq hn4 hB0 g O.cont O.classical O.bound hrt.1 (by omega) _
    have e : J r (pm i).2 =ᵐ[μ] (Set.Ioc r T).indicator (fun u => iteratedFDeriv ℝ j (propagatorW C r u (g u)) (pm i).2) := by
      filter_upwards [hae] with u hu
      simp only [hJ, Set.indicator_apply, Set.mem_Ioi, Set.mem_Ioc]
      by_cases h : r < u
      · simp [h, hu.2]
      · simp [h]
    refine AEStronglyMeasurable.congr ?_ e.symm
    rw [aestronglyMeasurable_indicator_iff measurableSet_Ioc, hμ, Measure.restrict_restrict measurableSet_Ioc,
      Set.inter_eq_left.2 (Set.Ioc_subset_Ioc_left hrt.1)]
    exact hc.aestronglyMeasurable measurableSet_Ioc
  · intro i
    filter_upwards [hae] with u hu
    simp only [hJ, Set.indicator_apply, Set.mem_Ioi]
    split_ifs with h
    · have hrt : ((pm i).1 : ℝ) ∈ Set.Icc (0 : ℝ) u := ⟨(pm i).1.2.1, h.le⟩
      obtain ⟨h1, h2⟩ := O.bound u (huT u hu) _ hrt
      exact h2 j (by omega) _
    · simpa using hB0
  · filter_upwards [hae, hne] with u hu hne'
    have hcont := s57p_orb_jet_continuous O (huT u hu) hj
    simp only [hJ, Set.indicator_apply, Set.mem_Ioi]
    rcases lt_or_gt_of_ne hne' with hlt | hgt
    · have hev : ∀ᶠ i in atTop, u < ((pm i).1 : ℝ) := hr.eventually (Ioi_mem_nhds hlt)
      have : ¬ (p₀.1 : ℝ) < u := not_lt.2 hlt.le
      simp only [this, if_false]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with i hi
      simp [not_lt.2 hi.le]
    · have hev : ∀ᶠ i in atTop, ((pm i).1 : ℝ) < u := hr.eventually (Iio_mem_nhds hgt)
      simp only [hgt, if_true]
      have hq : Tendsto (fun i => iteratedFDeriv ℝ j (propagatorW C (max 0 (min ((pm i).1 : ℝ) u)) u (g u)) (pm i).2)
          atTop (𝓝 (iteratedFDeriv ℝ j (propagatorW C (max 0 (min (p₀.1 : ℝ) u)) u (g u)) p₀.2)) :=
        (hcont.tendsto ((p₀.1 : ℝ), p₀.2)).comp (hr.prodMk_nhds hx)
      have e0 : max 0 (min (p₀.1 : ℝ) u) = (p₀.1 : ℝ) := by
        rw [min_eq_left hgt.le, max_eq_right p₀.1.2.1]
      rw [e0] at hq
      refine hq.congr' ?_
      filter_upwards [hev] with i hi
      have : max 0 (min ((pm i).1 : ℝ) u) = ((pm i).1 : ℝ) := by
        rw [min_eq_left hi.le, max_eq_right (pm i).1.2.1]
      simp [this, hi]

/-- the value of the orbit is continuous in the terminal time `u ∈ [r,T]`, including the endpoint `u = r` -/
theorem s57p_phi_contOn (G : S57pGen C T) (huniq : HRS.MS.S52B.S52bUniq C T) (hn4 : 4 ≤ n) (hB0 : 0 ≤ B)
    (O : S57pOrbFam C T n B g) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) (x : Euc d) :
    ContinuousOn (fun u => propagatorW C r u (g u) x) (Set.Icc r T) := by
  obtain ⟨BL, hBL0, hBL⟩ := s57p_F_lip G hn4 hB0 O
  have hIoc : ContinuousOn (fun u => propagatorW C r u (g u) x) (Set.Ioc r T) := by
    have h := s57p_jet_continuousOn G huniq hn4 hB0 g O.cont O.classical O.bound hr.1 (j := 0) (by omega) x
    have e : (fun u => propagatorW C r u (g u) x) = fun u =>
        (continuousMultilinearCurryFin0 ℝ (Euc d) ℝ) (iteratedFDeriv ℝ 0 (propagatorW C r u (g u)) x) := by
      funext u; simp [iteratedFDeriv_zero_eq_comp]
    rw [e]
    exact (continuousMultilinearCurryFin0 ℝ (Euc d) ℝ).continuous.comp_continuousOn h
  intro u hu
  rcases eq_or_lt_of_le hu.1 with h | h
  · have h' : u = r := h.symm
    subst h'
    have hval : propagatorW C u u (g u) x = g u x := congrFun (O.classical u hr).terminal x
    have hg : Tendsto (fun v => g v x) (𝓝[Set.Icc u T] u) (𝓝 (g u x)) :=
      ((O.cont x u hr).mono (Set.Icc_subset_Icc hr.1 le_rfl)).tendsto
    have hlin : Tendsto (fun v : ℝ => BL * (1 + ‖x‖) * (v - u)) (𝓝[Set.Icc u T] u) (𝓝 0) := by
      have : Tendsto (fun v : ℝ => BL * (1 + ‖x‖) * (v - u)) (𝓝 u) (𝓝 (BL * (1 + ‖x‖) * (u - u))) :=
        ((continuous_const.mul (continuous_id.sub continuous_const)).tendsto u)
      simp only [sub_self, mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hgd : Tendsto (fun v => dist (g v x) (g u x)) (𝓝[Set.Icc u T] u) (𝓝 0) :=
      tendsto_iff_dist_tendsto_zero.1 hg
    rw [ContinuousWithinAt, hval]
    refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero' (Eventually.of_forall fun v => dist_nonneg) ?_
      (by simpa using hlin.add hgd))
    filter_upwards [self_mem_nhdsWithin] with v hv
    have hvT : v ∈ Set.Icc (0 : ℝ) T := ⟨hr.1.trans hv.1, hv.2⟩
    have h1 := (hBL v hvT).2 u v hr.1 hv.1 le_rfl x
    have h2 : propagatorW C v v (g v) x = g v x := congrFun (O.classical v hvT).terminal x
    rw [h2] at h1
    calc dist (propagatorW C u v (g v) x) (g u x)
        ≤ dist (propagatorW C u v (g v) x) (g v x) + dist (g v x) (g u x) := dist_triangle _ _ _
      _ ≤ BL * (1 + ‖x‖) * (v - u) + dist (g v x) (g u x) := by
          rw [Real.dist_eq]; exact add_le_add h1 le_rfl
  · exact (hIoc u ⟨h, hu.2⟩).mono_of_mem_nhdsWithin (mem_nhdsWithin.2 ⟨Set.Ioi r, isOpen_Ioi, h, fun v hv => ⟨hv.1, hv.2.2⟩⟩)

/-- the generator of `Z(r)` is the integral of the generators of the orbits -/
theorem s57p_gen_Z (G : S57pGen C T) (Lin : S57pLin C T) (huniq : HRS.MS.S52B.S52bUniq C T) (hn4 : 4 ≤ n)
    (hB0 : 0 ≤ B) (O : S57pOrbFam C T n B g) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) (x : Euc d) :
    generatorW C r (s57pZ C g T r) x = ∫ u in r..T, generatorW C r (propagatorW C r u (g u)) x := by
  have hrT := hr
  refine Lin.comm r hrT r T B hB0 hr.2 (fun u => propagatorW C r u (g u)) ?_ ?_ x
  · intro u hu
    obtain ⟨h1, h2⟩ := O.bound u ⟨hr.1.trans hu.1.le, hu.2⟩ r ⟨hr.1, hu.1.le⟩
    exact ⟨h1.of_le (by exact_mod_cast (by omega : 4 ≤ n + 1)), fun i hi y => h2 i (by omega) y⟩
  · intro i hi
    refine s57p_jets_jointCont i (S := Set.Ioc r T) (B := B) (F := fun u => propagatorW C r u (g u)) ?_ ?_
    · intro u hu
      obtain ⟨h1, h2⟩ := O.bound u ⟨hr.1.trans hu.1.le, hu.2⟩ r ⟨hr.1, hu.1.le⟩
      exact ⟨h1.of_le (by exact_mod_cast (by omega : i + 1 ≤ n + 1)), fun y => h2 (i + 1) (by omega) y⟩
    · intro y
      exact s57p_jet_continuousOn G huniq hn4 hB0 g O.cont O.classical O.bound hr.1 (by omega) y

/-- the right derivative of the difference part -/
theorem s57p_I2_deriv (G : S57pGen C T) (Lin : S57pLin C T) (huniq : HRS.MS.S52B.S52bUniq C T) (hn4 : 4 ≤ n)
    (hB0 : 0 ≤ B) (O : S57pOrbFam C T n B g) {r : ℝ} (hr : r ∈ Set.Ioo 0 T) (x : Euc d) :
    HasDerivWithinAt (fun s => ∫ u in s..T, (propagatorW C r u (g u) x - propagatorW C s u (g u) x))
      (generatorW C r (s57pZ C g T r) x) (Set.Ici r) r := by
  obtain ⟨BL, hBL0, hBL⟩ := s57p_F_lip G hn4 hB0 O
  have hrI : r ∈ Set.Icc (0 : ℝ) T := ⟨hr.1.le, hr.2.le⟩
  set μ : Measure ℝ := volume.restrict (Set.Ioc r T) with hμ
  haveI : IsFiniteMeasure μ := ⟨by simp [hμ]⟩
  have hae : ∀ᵐ u ∂μ, u ∈ Set.Ioc r T := by rw [hμ]; exact ae_restrict_mem measurableSet_Ioc
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hset : Set.Ici r \ {r} = Set.Ioi r := by ext v; simp [lt_iff_le_and_ne, eq_comm]
  rw [hset]
  set q : ℝ → ℝ → ℝ := fun s u => (s - r)⁻¹ * (Set.Ioi s).indicator
    (fun u => propagatorW C r u (g u) x - propagatorW C s u (g u) x) u with hq
  have hslope : ∀ s ∈ Set.Ioo r T, slope (fun s => ∫ u in s..T,
      (propagatorW C r u (g u) x - propagatorW C s u (g u) x)) r s = ∫ u, q s u ∂μ := by
    intro s hs
    rw [slope_def_field, hq]
    simp only []
    rw [integral_const_mul]
    congr 1
    have h0 : (∫ u in r..T, (propagatorW C r u (g u) x - propagatorW C r u (g u) x)) = 0 := by simp
    rw [h0, sub_zero, intervalIntegral.integral_of_le hs.2.le, hμ, setIntegral_indicator measurableSet_Ioi]
    have hI : Set.Ioc r T ∩ Set.Ioi s = Set.Ioc s T := by
      ext u; simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ioi]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨hs.1.trans h1, h2⟩, h1⟩
    rw [hI, div_eq_inv_mul]
  have hlim : Tendsto (fun s => ∫ u, q s u ∂μ) (𝓝[Set.Ioi r] r)
      (𝓝 (generatorW C r (s57pZ C g T r) x)) := by
    rw [s57p_gen_Z G Lin huniq hn4 hB0 O hrI x, intervalIntegral.integral_of_le hr.2.le]
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => BL * (1 + ‖x‖)) ?_ ?_
      (integrable_const _) ?_
    · filter_upwards [Ioo_mem_nhdsGT hr.2] with s hs
      have hsI : s ∈ Set.Icc (0 : ℝ) T := ⟨hr.1.le.trans hs.1.le, hs.2.le⟩
      have hc1 : ContinuousOn (fun u => propagatorW C r u (g u) x - propagatorW C s u (g u) x) (Set.Ioc s T) :=
        ((s57p_phi_contOn G huniq hn4 hB0 O hrI x).mono (fun u hu => ⟨hs.1.le.trans hu.1.le, hu.2⟩)).sub
          ((s57p_phi_contOn G huniq hn4 hB0 O hsI x).mono Set.Ioc_subset_Icc_self)
      refine aestronglyMeasurable_const.mul ?_
      rw [aestronglyMeasurable_indicator_iff measurableSet_Ioi, hμ, Measure.restrict_restrict measurableSet_Ioi]
      have hI : Set.Ioi s ∩ Set.Ioc r T = Set.Ioc s T := by
        ext u; simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ioi]
        constructor
        · rintro ⟨h3, _, h2⟩; exact ⟨h3, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨h1, hs.1.trans h1, h2⟩
      rw [hI]
      exact hc1.aestronglyMeasurable measurableSet_Ioc
    · filter_upwards [Ioo_mem_nhdsGT hr.2] with s hs
      filter_upwards [hae] with u hu
      have huT : u ∈ Set.Icc (0 : ℝ) T := ⟨hr.1.le.trans hu.1.le, hu.2⟩
      simp only [hq, Set.indicator_apply, Set.mem_Ioi, Real.norm_eq_abs]
      split_ifs with h
      · have h1 := ((hBL u huT).2 r s hr.1.le hs.1.le h.le x)
        rw [abs_mul, abs_of_pos (inv_pos.2 (sub_pos.2 hs.1))]
        calc (s - r)⁻¹ * |propagatorW C r u (g u) x - propagatorW C s u (g u) x|
            ≤ (s - r)⁻¹ * (BL * (1 + ‖x‖) * (s - r)) :=
              mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 (sub_pos.2 hs.1).le)
          _ = BL * (1 + ‖x‖) := by field_simp [(sub_pos.2 hs.1).ne']
      · simp only [mul_zero, abs_zero]; positivity
    · filter_upwards [hae] with u hu
      have huT : u ∈ Set.Icc (0 : ℝ) T := ⟨hr.1.le.trans hu.1.le, hu.2⟩
      have hd := (O.classical u huT).time_deriv x r ⟨hr.1, hu.1⟩
      have hsl := (hasDerivAt_iff_tendsto_slope.1 hd).mono_left (nhdsWithin_mono r (fun v hv => ne_of_gt hv))
      have hneg := hsl.neg
      rw [neg_neg] at hneg
      refine hneg.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT hu.1] with s hs
      simp only [hq, Set.indicator_apply, Set.mem_Ioi, hs.2, if_true, slope_def_field, Pi.neg_apply]
      rw [div_eq_inv_mul]
      ring
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hr.2] with s hs
  exact (hslope s hs).symm

/-- the right derivative of `Z(·)(x)` -/
theorem s57p_Z_rderiv (G : S57pGen C T) (Lin : S57pLin C T) (huniq : HRS.MS.S52B.S52bUniq C T) (hn4 : 4 ≤ n)
    (hB0 : 0 ≤ B) (O : S57pOrbFam C T n B g) {r : ℝ} (hr : r ∈ Set.Ioo 0 T) (x : Euc d) :
    HasDerivWithinAt (fun s => s57pZ C g T s x) (-(g r x) - generatorW C r (s57pZ C g T r) x) (Set.Ici r) r := by
  have hrI : r ∈ Set.Icc (0 : ℝ) T := ⟨hr.1.le, hr.2.le⟩
  have hφ := s57p_phi_contOn G huniq hn4 hB0 O hrI x
  have hval : propagatorW C r r (g r) x = g r x := congrFun (O.classical r hrI).terminal x
  have hΦ : HasDerivWithinAt (fun s => ∫ u in r..s, propagatorW C r u (g u) x) (g r x) (Set.Ici r) r := by
    have := intervalIntegral.integral_hasDerivWithinAt_right (a := r) (b := r) (s := Set.Ici r) (t := Set.Ioi r)
      (f := fun u => propagatorW C r u (g u) x) IntervalIntegrable.refl ?_ ?_
    · rwa [hval] at this
    · rw [← nhdsWithin_Ioc_eq_nhdsGT hr.2]
      exact (hφ.mono Set.Ioc_subset_Icc_self).stronglyMeasurableAtFilter_nhdsWithin measurableSet_Ioc r
    · exact (hφ r ⟨le_rfl, hr.2.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGT hr.2)
  have hI2 := s57p_I2_deriv G Lin huniq hn4 hB0 O hr x
  have h1 := (hΦ.add hI2).const_sub (s57pZ C g T r x)
  refine (h1.congr_deriv (by ring)).congr_of_eventuallyEq ?_ ?_
  · filter_upwards [Icc_mem_nhdsGE hr.2] with s hs
    have hsI : s ∈ Set.Icc (0 : ℝ) T := ⟨hr.1.le.trans hs.1, hs.2⟩
    have hint1 : IntervalIntegrable (fun u => propagatorW C r u (g u) x) volume r T :=
      (hφ.mono le_rfl).intervalIntegrable_of_Icc hr.2.le
    have hint2 : IntervalIntegrable (fun u => propagatorW C s u (g u) x) volume s T :=
      ((s57p_phi_contOn G huniq hn4 hB0 O hsI x)).intervalIntegrable_of_Icc hs.2
    have hint1a : IntervalIntegrable (fun u => propagatorW C r u (g u) x) volume r s :=
      (hφ.mono (Set.Icc_subset_Icc le_rfl hs.2)).intervalIntegrable_of_Icc hs.1
    have hint1b : IntervalIntegrable (fun u => propagatorW C r u (g u) x) volume s T :=
      (hφ.mono (Set.Icc_subset_Icc hs.1 le_rfl)).intervalIntegrable_of_Icc hs.2
    simp only [s57pZ, Pi.add_apply]
    rw [intervalIntegral.integral_sub hint1b hint2, ← intervalIntegral.integral_add_adjacent_intervals hint1a hint1b]
    ring
  · simp [s57pZ]

/-- `Z` is Lipschitz in `r` with the weight `1 + ‖x‖` -/
theorem s57p_Z_lip (G : S57pGen C T) (huniq : HRS.MS.S52B.S52bUniq C T) (hn4 : 4 ≤ n)
    (hB0 : 0 ≤ B) (O : S57pOrbFam C T n B g) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ r r' : ℝ, r ∈ Set.Icc (0 : ℝ) T → r' ∈ Set.Icc (0 : ℝ) T → r ≤ r' → ∀ x,
      |s57pZ C g T r x - s57pZ C g T r' x| ≤ L * (1 + ‖x‖) * (r' - r) := by
  obtain ⟨BL, hBL0, hBL⟩ := s57p_F_lip G hn4 hB0 O
  refine ⟨B + |T| * BL, by positivity, fun r r' hr hr' hrr' x => ?_⟩
  have hφ := s57p_phi_contOn G huniq hn4 hB0 O hr x
  have hφ' := s57p_phi_contOn G huniq hn4 hB0 O hr' x
  have hi1 : IntervalIntegrable (fun u => propagatorW C r u (g u) x) volume r r' :=
    (hφ.mono (Set.Icc_subset_Icc le_rfl hr'.2)).intervalIntegrable_of_Icc hrr'
  have hi2 : IntervalIntegrable (fun u => propagatorW C r u (g u) x) volume r' T :=
    (hφ.mono (Set.Icc_subset_Icc hrr' le_rfl)).intervalIntegrable_of_Icc hr'.2
  have hi3 : IntervalIntegrable (fun u => propagatorW C r' u (g u) x) volume r' T :=
    hφ'.intervalIntegrable_of_Icc hr'.2
  have e : s57pZ C g T r x - s57pZ C g T r' x = (∫ u in r..r', propagatorW C r u (g u) x) +
      ∫ u in r'..T, (propagatorW C r u (g u) x - propagatorW C r' u (g u) x) := by
    simp only [s57pZ]
    rw [intervalIntegral.integral_sub hi2 hi3, ← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
    ring
  have b1 : ‖∫ u in r..r', propagatorW C r u (g u) x‖ ≤ B * |r' - r| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const (fun u hu => ?_)
    rw [Set.uIoc_of_le hrr'] at hu
    have huT : u ∈ Set.Icc (0 : ℝ) T := ⟨hr.1.trans hu.1.le, hu.2.trans hr'.2⟩
    obtain ⟨-, h2⟩ := O.bound u huT r ⟨hr.1, hu.1.le⟩
    have := h2 0 (by omega) x
    rw [norm_iteratedFDeriv_zero] at this
    exact this
  have b2 : ‖∫ u in r'..T, (propagatorW C r u (g u) x - propagatorW C r' u (g u) x)‖ ≤
      BL * (1 + ‖x‖) * (r' - r) * |T - r'| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const (fun u hu => ?_)
    rw [Set.uIoc_of_le hr'.2] at hu
    have huT : u ∈ Set.Icc (0 : ℝ) T := ⟨hr'.1.trans hu.1.le, hu.2⟩
    rw [Real.norm_eq_abs]
    exact ((hBL u huT).2 r r' hr.1 hrr' hu.1.le x)
  have hT0 : 0 ≤ T := le_trans hr.1 hr.2
  have hTr : |T - r'| ≤ T := by rw [abs_of_nonneg (sub_nonneg.2 hr'.2)]; linarith [hr'.1]
  rw [abs_of_nonneg (sub_nonneg.2 hrr')] at b1
  calc |s57pZ C g T r x - s57pZ C g T r' x| ≤ ‖∫ u in r..r', propagatorW C r u (g u) x‖ +
        ‖∫ u in r'..T, (propagatorW C r u (g u) x - propagatorW C r' u (g u) x)‖ := by
        rw [e, ← Real.norm_eq_abs]; exact norm_add_le _ _
    _ ≤ B * (r' - r) + BL * (1 + ‖x‖) * (r' - r) * |T| := by
        refine add_le_add b1 (b2.trans ?_)
        exact mul_le_mul_of_nonneg_left (hTr.trans (le_abs_self T)) (by positivity)
    _ ≤ (B + |T| * BL) * (1 + ‖x‖) * (r' - r) := by
        have h1 : 0 ≤ r' - r := sub_nonneg.2 hrr'
        have h2 : 0 ≤ ‖x‖ := norm_nonneg x
        nlinarith [mul_nonneg hB0 h2, mul_nonneg (mul_nonneg (abs_nonneg T) hBL0) h1, mul_nonneg hB0 h1,
          mul_nonneg (mul_nonneg hB0 h2) h1]

/-- bounds of the jets of `Z` -/
theorem s57p_Z_bound (G : S57pGen C T) (huniq : HRS.MS.S52B.S52bUniq C T) (hn4 : 4 ≤ n) (hB0 : 0 ≤ B)
    (O : S57pOrbFam C T n B g) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) {j : ℕ} (hj : j ≤ n) (y : Euc d) :
    ‖iteratedFDeriv ℝ j (s57pZ C g T r) y‖ ≤ B * T := by
  rw [(s57p_Z_jets G huniq hn4 hB0 O hr).2 j hj y]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := B) (fun u hu => ?_)).trans ?_
  · rw [Set.uIoc_of_le hr.2] at hu
    exact (O.bound u ⟨hr.1.trans hu.1.le, hu.2⟩ r ⟨hr.1, hu.1.le⟩).2 j (by omega) y
  · have : |T - r| ≤ T := by rw [abs_of_nonneg (sub_nonneg.2 hr.2)]; linarith [hr.1]
    exact mul_le_mul_of_nonneg_left this hB0

/-- the generator of `Z` is continuous in `(r,x)` -/
theorem s57p_Z_gen_cont (G : S57pGen C T) (huniq : HRS.MS.S52B.S52bUniq C T) (hn4 : 4 ≤ n) (hB0 : 0 ≤ B)
    (O : S57pOrbFam C T n B g) (hT : 0 ≤ T) :
    Continuous fun p : Set.Icc (0 : ℝ) T × Euc d => generatorW C p.1 (s57pZ C g T p.1) p.2 := by
  obtain ⟨K, hK0, hgen⟩ := G.bound
  obtain ⟨L, hL0, hLip⟩ := s57p_Z_lip G huniq hn4 hB0 O
  set Zc : ℝ → Euc d → ℝ := fun r => s57pZ C g T (max 0 (min r T)) with hZc
  have hcl : ∀ r, max 0 (min r T) ∈ Set.Icc (0 : ℝ) T := fun r => ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩
  have hBz : 0 ≤ B * T := mul_nonneg hB0 hT
  have hG : ∀ r', ContDiff ℝ 4 (Zc r') ∧ ∀ j ≤ 4, ∀ x, ‖iteratedFDeriv ℝ j (Zc r') x‖ ≤ B * T := by
    intro r'
    refine ⟨((s57p_Z_jets G huniq hn4 hB0 O (hcl r')).1).of_le (by exact_mod_cast hn4), fun j hj x => ?_⟩
    exact s57p_Z_bound G huniq hn4 hB0 O (hcl r') (by omega) x
  have hgr : ∀ r r' x, |Zc r x - Zc r' x| ≤ L * (1 + ‖x‖) * |r - r'| := by
    intro r r' x
    have hc := s55m_clip_abs T r r'
    rcases le_total (max 0 (min r T)) (max 0 (min r' T)) with h | h
    · have := hLip _ _ (hcl r) (hcl r') h x
      refine this.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      rw [abs_of_nonpos (sub_nonpos.2 h)] at hc
      linarith
    · have := hLip _ _ (hcl r') (hcl r) h x
      rw [abs_sub_comm]
      refine this.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      rw [abs_of_nonneg (sub_nonneg.2 h)] at hc
      linarith
  have key := s57p_cont_gen G hBz hK0 (fun τ hτ u hu hub => hgen τ hτ (B * T) u hBz hu hub) hG hgr
  refine key.congr fun p => ?_
  have : max 0 (min (p.1 : ℝ) T) = p.1 := by rw [min_eq_left p.1.2.2, max_eq_right p.1.2.1]
  simp [hZc, this]

end Duhamel

end HRS.MS.FixEq

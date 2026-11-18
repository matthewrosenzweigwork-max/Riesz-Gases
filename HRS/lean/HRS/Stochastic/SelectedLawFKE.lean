import HRS.Stochastic.EmpiricalIto

/-!
# Proposition B.3: the selected law solves the forward Kolmogorov equation (row 5)

Package PART-01, row 5 (`M:B:prop:selected-law-fke`).  Spec: `HRS/Stochastic/PART01_REST_SPEC.md` §6.
The definitions `IsFKETest`, `configLift`, `fkeGenerator`, `fkeInteraction` are those of
`HRS/Stochastic/SelectedFlow.lean`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d N : ℕ}

/-! ### Periodicity on the covering space -/

theorem fderiv_periodic_add {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {g : E → F} {v : E}
    (hg : ∀ x, g (x + v) = g x) (x : E) :
    fderiv ℝ g (x + v) = fderiv ℝ g x := by
  rw [← fderiv_comp_add_right]
  congr 1
  funext z
  exact hg z

/-- Coordinatewise lattice vectors of `Fin N → Euc d`. -/
def IsLatticeVec (v : Fin N → Euc d) : Prop := ∀ i, ∃ n : Lattice d, v i = Lattice.toEuc n

theorem configLift_add_lattice (Φ : ℝ → Config d N → ℝ) (r : ℝ) {v : Fin N → Euc d}
    (hv : IsLatticeVec v) (Y : Fin N → Euc d) :
    configLift Φ r (Y + v) = configLift Φ r Y := by
  unfold configLift
  congr 1
  funext i
  obtain ⟨n, hn⟩ := hv i
  have h := Torus.lift_periodic (fun t : Torus d => t) (Y i) n
  simp only [Pi.add_apply, hn]
  exact h

theorem fderiv_configLift_add_lattice (Φ : ℝ → Config d N → ℝ) (r : ℝ) {v : Fin N → Euc d}
    (hv : IsLatticeVec v) (Y : Fin N → Euc d) :
    fderiv ℝ (configLift Φ r) (Y + v) = fderiv ℝ (configLift Φ r) Y :=
  fderiv_periodic_add (fun x => configLift_add_lattice Φ r hv x) Y

theorem fderiv2_configLift_add_lattice (Φ : ℝ → Config d N → ℝ) (r : ℝ) {v : Fin N → Euc d}
    (hv : IsLatticeVec v) (Y : Fin N → Euc d) :
    fderiv ℝ (fderiv ℝ (configLift Φ r)) (Y + v) = fderiv ℝ (fderiv ℝ (configLift Φ r)) Y :=
  fderiv_periodic_add (fun x => fderiv_configLift_add_lattice Φ r hv x) Y

/-- The canonical representatives of the coordinates of a configuration, on the covering space. -/
def repC (x : Config d N) : Fin N → Euc d := fun i => Torus.rep (x i)

theorem mk_repC (x : Config d N) : (fun i => Torus.mk (repC x i)) = x := by
  funext i
  exact Torus.mk_rep (x i)

theorem exists_lattice_shift {Y Y' : Fin N → Euc d}
    (h : ∀ i, Torus.mk (Y i) = Torus.mk (Y' i)) :
    ∃ v : Fin N → Euc d, IsLatticeVec v ∧ Y' = Y + v := by
  choose n hn using fun i => exists_lattice_of_mk_eq (h i).symm
  refine ⟨fun i => Lattice.toEuc (n i), fun i => ⟨n i, rfl⟩, ?_⟩
  funext i
  rw [Pi.add_apply]
  exact hn i

/-! ### Algebra of the drift -/

/-- The pair force `M ∇g(x_i - x_j)` of the particle drift. -/
def pairForce (D : DynData d) (x : Config d N) (i j : Fin N) : Euc d :=
  Torus.matVec D.M (periodicRieszGrad d D.s (x i - x j))

theorem pairForce_swap (D : DynData d) (hsd : D.s < d) (x : Config d N) (i j : Fin N) :
    pairForce D x j i = -pairForce D x i j := by
  unfold pairForce
  rw [← neg_sub (x i) (x j), PDE.periodicRieszGrad_neg hsd]
  unfold Torus.matVec
  rw [map_neg]

theorem sum_offdiag_split {N : ℕ} (A B : Fin N → Fin N → ℝ) (hAB : ∀ i j, A j i = -B i j) :
    ∑ i, ∑ j ∈ Finset.univ.erase i, A i j
      = ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), (A i j - B i j) := by
  have hsplit : ∀ i, ∑ j ∈ Finset.univ.erase i, A i j
      = ∑ j ∈ Finset.univ.filter (fun j => i < j), A i j
        + ∑ j ∈ Finset.univ.filter (fun j => j < i), A i j := by
    intro i
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ.erase i) (fun j => i < j)]
    congr 1
    · refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext j
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
      constructor
      · exact fun h => h.2
      · intro h; exact ⟨ne_of_gt h, h⟩
    · refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext j
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
      constructor
      · rintro ⟨hne, hlt⟩
        exact lt_of_le_of_ne (not_lt.1 hlt) hne
      · intro h
        exact ⟨ne_of_lt h, not_lt.2 h.le⟩
  have hswap : ∑ i, ∑ j ∈ Finset.univ.filter (fun j => j < i), A i j
      = -∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), B i j := by
    rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun j => Finset.univ.filter (fun i => j < i))
      (by intro x y; simp)]
    simp only [hAB, Finset.sum_neg_distrib]
  simp only [hsplit, Finset.sum_add_distrib, Finset.sum_sub_distrib, hswap]
  ring

/-! ### The drift of Itô's formula and the generator of Proposition B.3 -/

/-- The drift part of Itô's formula for `configLift Φ` at a covering point `Y`, with additive
noise `liftedNoise D` and drift `driftVec D` (the value of `itoDrift` at `(s, Y)`). -/
def fkeIto (D : DynData d) (T : ℝ) (Φ : ℝ → Config d N → ℝ) (s : ℝ) (Y : Fin N → Euc d) : ℝ :=
  derivWithin (fun r => configLift Φ r Y) (Set.Icc 0 T) s
    + fderiv ℝ (configLift Φ s) Y (driftVec D (fun j => Torus.mk (Y j)))
    + (1 / 2 : ℝ) * ∑ k : Fin N × Fin d,
        fderiv ℝ (fderiv ℝ (configLift Φ s)) Y (liftedNoise D k) (liftedNoise D k)

/-- The coordinate functional `u ↦ L (Pi.single i u)`. -/
def coordFun (L : (Fin N → Euc d) →L[ℝ] ℝ) (i : Fin N) : Euc d →ₗ[ℝ] ℝ :=
  L.toLinearMap.comp (LinearMap.single ℝ (fun _ : Fin N => Euc d) i)

theorem coordFun_apply (L : (Fin N → Euc d) →L[ℝ] ℝ) (i : Fin N) (u : Euc d) :
    coordFun L i u = L (Pi.single i u) := rfl

/-- Linear decomposition of a continuous linear functional along the coordinates. -/
theorem clm_eq_sum_single (L : (Fin N → Euc d) →L[ℝ] ℝ) (v : Fin N → Euc d) :
    L v = ∑ i, coordFun L i (v i) := by
  have hsum : v = ∑ i, Pi.single i (v i) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  have h := congrArg L hsum
  rw [h, map_sum]
  rfl

theorem clm_driftVec (D : DynData d) (L : (Fin N → Euc d) →L[ℝ] ℝ) (x : Config d N) :
    L (driftVec D x) = (1 / (N : ℝ)) * ∑ i, ∑ j ∈ Finset.univ.erase i,
        L (Pi.single i (pairForce D x i j))
      - ∑ i, L (Pi.single i (Torus.grad D.V (x i))) := by
  rw [clm_eq_sum_single L (driftVec D x)]
  have hi : ∀ i, coordFun L i (driftVec D x i)
      = (1 / (N : ℝ)) * ∑ j ∈ Finset.univ.erase i, coordFun L i (pairForce D x i j)
        - coordFun L i (Torus.grad D.V (x i)) := by
    intro i
    simp only [driftVec, particleDrift, pairForce, map_sub, map_smul, map_sum, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun i _ => hi i), Finset.sum_sub_distrib, Finset.mul_sum]
  simp only [coordFun_apply]

theorem clm_driftVec_filter (D : DynData d) (hsd : D.s < d) (L : (Fin N → Euc d) →L[ℝ] ℝ)
    (x : Config d N) :
    L (driftVec D x) = (1 / (N : ℝ)) * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
        (L (Pi.single i (pairForce D x i j)) - L (Pi.single j (pairForce D x i j)))
      - ∑ i, L (Pi.single i (Torus.grad D.V (x i))) := by
  have hs : ∑ i, ∑ j ∈ Finset.univ.erase i, L (Pi.single i (pairForce D x i j))
      = ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
          (L (Pi.single i (pairForce D x i j)) - L (Pi.single j (pairForce D x i j))) := by
    refine sum_offdiag_split (fun i j => L (Pi.single i (pairForce D x i j)))
      (fun i j => L (Pi.single j (pairForce D x i j))) ?_
    intro i j
    rw [pairForce_swap D hsd, Pi.single_neg, map_neg]
  rw [clm_driftVec D L x, hs]

/-- Itô's drift identity: the drift of `configLift Φ` along a lift `Y` equals the generator and
interaction of Proposition B.3 at the projected configuration (pointwise, for every `s`). -/
theorem fkeIto_eq (D : DynData d) (hsd : D.s < d) (T : ℝ) (Φ : ℝ → Config d N → ℝ) (s : ℝ)
    (Y : Fin N → Euc d) :
    fkeIto D T Φ s Y = fkeGenerator D T Φ s (fun i => Torus.mk (Y i))
      + fkeInteraction D Φ s (fun i => Torus.mk (Y i)) := by
  obtain ⟨v, hv, hYr⟩ := exists_lattice_shift (Y := Y)
    (Y' := repC (fun i => Torus.mk (Y i))) (fun i => (Torus.mk_rep _).symm)
  have hr : (fun i => Torus.rep (Torus.mk (Y i))) = Y + v := hYr
  have e1 : derivWithin (fun r => configLift Φ r (fun i => Torus.rep (Torus.mk (Y i))))
      (Set.Icc 0 T) s = derivWithin (fun r => configLift Φ r Y) (Set.Icc 0 T) s := by
    congr 1
    funext r
    rw [hr]
    exact configLift_add_lattice Φ r hv Y
  have e2 : fderiv ℝ (configLift Φ s) (fun i => Torus.rep (Torus.mk (Y i)))
      = fderiv ℝ (configLift Φ s) Y := by
    rw [hr]
    exact fderiv_configLift_add_lattice Φ s hv Y
  have e3 : fderiv ℝ (fderiv ℝ (configLift Φ s)) (fun i => Torus.rep (Torus.mk (Y i)))
      = fderiv ℝ (fderiv ℝ (configLift Φ s)) Y := by
    rw [hr]
    exact fderiv2_configLift_add_lattice Φ s hv Y
  have hσ : ∀ k : Fin N × Fin d,
      fderiv ℝ (fderiv ℝ (configLift Φ s)) Y (liftedNoise D k) (liftedNoise D k)
        = (2 * D.invβ) * fderiv ℝ (fderiv ℝ (configLift Φ s)) Y (configBasis d N k)
            (configBasis d N k) := by
    intro k
    have hc : liftedNoise D k = Real.sqrt (2 * D.invβ) • configBasis d N k := rfl
    have h2 : Real.sqrt (2 * D.invβ) ^ 2 = 2 * D.invβ := Real.sq_sqrt (by linarith [D.hβ])
    rw [hc]
    simp only [map_smul, smul_apply, smul_eq_mul]
    linear_combination (fderiv ℝ (fderiv ℝ (configLift Φ s)) Y (configBasis d N k)
      (configBasis d N k)) * h2
  unfold fkeIto
  simp only [fkeGenerator, fkeInteraction]
  rw [e1, e2, e3, clm_driftVec_filter D hsd, Finset.sum_congr rfl (fun k _ => hσ k),
    ← Finset.mul_sum]
  simp only [pairForce]
  ring

/-! ### Bounds -/

theorem smoothOffZero_of_dim (D : DynData d) :
    Torus.IsSmoothOffZero (periodicRieszGrad d D.s) := by
  rcases Nat.lt_or_ge d 2 with hd | hd
  · have hpos : (0 : ℝ) < d := lt_of_le_of_lt D.hs0 D.hsd
    have hd1 : d = 1 := by
      have : 0 < d := by exact_mod_cast hpos
      omega
    subst hd1
    exact (kernelLocal_d1 D.hs0 (by simpa using D.hsd)).smoothOffZero
  · exact (kernelLocal_of_two_le hd D.hs0 D.hsd).smoothOffZero

theorem exists_pos_lower_bound {α : Type*} [TopologicalSpace α] {K : Set α} (hK : IsCompact K)
    {f : α → ℝ} (hf : Continuous f) (hpos : ∀ x ∈ K, 0 < f x) :
    ∃ ε > 0, ∀ x ∈ K, ε ≤ f x := by
  rcases K.eq_empty_or_nonempty with h | h
  · exact ⟨1, one_pos, by simp [h]⟩
  · obtain ⟨x0, hx0, hmin⟩ := hK.exists_isMinOn h hf.continuousOn
    exact ⟨f x0, hpos x0 hx0, fun x hx => (isMinOn_iff.1 hmin) x hx⟩

/-- A compact set of configurations without collisions is uniformly separated. -/
theorem sep_lower_bound (hN : 0 < N) {K : Set (Config d N)} (hK : IsCompact K)
    (hdisj : Disjoint K (collisionSet d N)) :
    ∃ ε > 0, ∀ x ∈ K, ∀ i j : Fin N, i ≠ j → ε ≤ Torus.tdist (x i) (x j) := by
  have hp : ∀ p : Fin N × Fin N, ∃ ε > 0, ∀ x ∈ K, p.1 ≠ p.2 →
      ε ≤ Torus.tdist (x p.1) (x p.2) := by
    rintro ⟨i, j⟩
    by_cases hij : i = j
    · exact ⟨1, one_pos, fun x _ h => absurd hij h⟩
    · obtain ⟨ε, hε, h⟩ := exists_pos_lower_bound hK
        (f := fun x : Config d N => Torus.tdist (x i) (x j))
        (Torus.continuous_tdist_comp (continuous_apply i) (continuous_apply j))
        (fun x hx => by
          have hne : x i ≠ x j := fun heq =>
            Set.disjoint_left.1 hdisj hx ⟨i, j, hij, heq⟩
          refine lt_of_le_of_ne (by unfold Torus.tdist; exact norm_nonneg _) fun h0 => hne ?_
          exact (Torus.tdist_eq_zero_iff _ _).1 h0.symm)
      exact ⟨ε, hε, fun x hx _ => h x hx⟩
  choose ε hεpos hε using hp
  haveI : Nonempty (Fin N × Fin N) := ⟨(⟨0, hN⟩, ⟨0, hN⟩)⟩
  obtain ⟨p0, hp0⟩ := Finite.exists_min ε
  exact ⟨ε p0, hεpos p0, fun x hx i j hij => (hp0 (i, j)).trans (hε (i, j) x hx hij)⟩

/-- The drift is bounded on a compact collision-free set of configurations. -/
theorem driftVec_bound_on_K (D : DynData d) (hN : 0 < N) (hV : Torus.IsCk 2 D.V)
    {K : Set (Config d N)} (hK : IsCompact K) (hdisj : Disjoint K (collisionSet d N)) :
    ∃ B : ℝ, ∀ x ∈ K, ‖driftVec D x‖ ≤ B := by
  obtain ⟨ε, hε, hsep⟩ := sep_lower_bound hN hK hdisj
  obtain ⟨B, hB⟩ := liftedDrift_bounded_of_sep D (smoothOffZero_of_dim D) hV hε
  refine ⟨B, fun x hx => ?_⟩
  have h1 := hB (fun i => Torus.rep (x i)) (fun i j hij => by
    simpa only [Torus.mk_rep] using hsep x hx i j hij)
  have e : liftedDrift D (fun i => Torus.rep (x i)) = driftVec D x := by
    unfold liftedDrift driftVec
    congr 1
    funext i
    simp only [Torus.mk_rep]
  rw [← e]
  exact h1

/-- Periodic bound: a continuous, lattice-periodic function is bounded on `[0,T] × (Euc)^N`. -/
theorem bounded_of_periodic {α : Type*} [NormedAddCommGroup α] {T : ℝ} (H : ℝ → (Fin N → Euc d) → α)
    (hH : ContinuousOn (fun p : ℝ × (Fin N → Euc d) => H p.1 p.2) (Icc 0 T ×ˢ univ))
    (hper : ∀ (s : ℝ) (Y : Fin N → Euc d) (v : Fin N → Euc d), IsLatticeVec v → H s (Y + v) = H s Y) :
    ∃ C : ℝ, ∀ s ∈ Icc 0 T, ∀ Y, ‖H s Y‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod
      (isCompact_closedBall (0 : Fin N → Euc d) (Real.sqrt d))).exists_bound_of_continuousOn
    (hH.mono (prod_mono subset_rfl (subset_univ _)))
  refine ⟨C, fun s hs Y => ?_⟩
  have hmem : (fun i => Torus.rep (Torus.mk (Y i))) ∈ Metric.closedBall (0 : Fin N → Euc d) (Real.sqrt d) := by
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro i
    exact rep_norm_le _
  have hb := hC (s, fun i => Torus.rep (Torus.mk (Y i))) ⟨hs, hmem⟩
  obtain ⟨v, hv, hYr⟩ := exists_lattice_shift (Y := Y) (Y' := fun i => Torus.rep (Torus.mk (Y i)))
    (fun i => (Torus.mk_rep _).symm)
  have e : H s (fun i => Torus.rep (Torus.mk (Y i))) = H s Y := by
    rw [hYr]
    exact hper s Y v hv
  rw [← e]
  exact hb

theorem fderiv_configLift_eq_zero {K : Set (Config d N)} (hK : IsCompact K)
    (Φ : ℝ → Config d N → ℝ) (hsupp : ∀ r (X : Config d N), X ∉ K → Φ r X = 0)
    (s : ℝ) (Y : Fin N → Euc d) (hY : (fun i => Torus.mk (Y i)) ∉ K) :
    fderiv ℝ (configLift Φ s) Y = 0 := by
  have hcont : Continuous (fun Z : Fin N → Euc d => fun i => Torus.mk (Z i)) :=
    continuous_pi fun i => Torus.continuous_mk.comp (continuous_apply i)
  have hopen : IsOpen ((fun Z : Fin N → Euc d => fun i => Torus.mk (Z i)) ⁻¹' Kᶜ) :=
    (hK.isClosed.isOpen_compl).preimage hcont
  have hev : configLift Φ s =ᶠ[nhds Y] (fun _ => (0 : ℝ)) := by
    filter_upwards [hopen.mem_nhds hY] with Z hZ
    exact hsupp s _ hZ
  rw [hev.fderiv_eq]
  simp

/-- The Itô drift of `configLift Φ` is bounded, uniformly in `s ∈ [0,T]` and in the lift. -/
theorem fkeIto_bound {T : ℝ} (hT : 0 ≤ T) (D : DynData d) (hN : 0 < N) (hV : Torus.IsCk 2 D.V)
    (Φ : ℝ → Config d N → ℝ) (hΦ : IsC12On T Set.univ (configLift Φ))
    {K : Set (Config d N)} (hK : IsCompact K) (hdisj : Disjoint K (collisionSet d N))
    (hsupp : ∀ r (X : Config d N), X ∉ K → Φ r X = 0) :
    ∃ C : ℝ, ∀ s ∈ Icc 0 T, ∀ Y, ‖fkeIto D T Φ s Y‖ ≤ C := by
  obtain ⟨C0, hC0⟩ := bounded_of_periodic (T := T)
    (fun s Y => derivWithin (fun r => configLift Φ r Y) (Icc 0 T) s)
    (by simpa [Function.uncurry] using hΦ.cont_deriv)
    (fun s Y v hv => by simp only [configLift_add_lattice Φ _ hv])
  obtain ⟨C1, hC1⟩ := bounded_of_periodic (T := T)
    (fun s Y => fderiv ℝ (configLift Φ s) Y)
    (by simpa [Function.uncurry] using hΦ.cont_fderiv)
    (fun s Y v hv => fderiv_configLift_add_lattice Φ s hv Y)
  obtain ⟨C2, hC2⟩ := bounded_of_periodic (T := T)
    (fun s Y => fderiv ℝ (fderiv ℝ (configLift Φ s)) Y)
    (by simpa [Function.uncurry] using hΦ.cont_fderiv₂)
    (fun s Y v hv => fderiv2_configLift_add_lattice Φ s hv Y)
  obtain ⟨B, hB⟩ := driftVec_bound_on_K D hN hV hK hdisj
  set C1' := max C1 0
  set C2' := max C2 0
  set B' := max B 0
  set C0' := max C0 0
  have hσ : ∑ k : Fin N × Fin d, ‖liftedNoise D k‖ * ‖liftedNoise D k‖ ≥ 0 :=
    Finset.sum_nonneg fun k _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  refine ⟨C0' + C1' * B' + (1 / 2) * (C2' * ∑ k : Fin N × Fin d,
      ‖liftedNoise D k‖ * ‖liftedNoise D k‖), fun s hs Y => ?_⟩
  have hd : ‖fderiv ℝ (configLift Φ s) Y (driftVec D (fun j => Torus.mk (Y j)))‖ ≤ C1' * B' := by
    have hL : ‖fderiv ℝ (configLift Φ s) Y‖ ≤ C1' := (hC1 s hs Y).trans (le_max_left _ _)
    by_cases hmem : (fun j => Torus.mk (Y j)) ∈ K
    · calc ‖fderiv ℝ (configLift Φ s) Y (driftVec D (fun j => Torus.mk (Y j)))‖
          ≤ ‖fderiv ℝ (configLift Φ s) Y‖ * ‖driftVec D (fun j => Torus.mk (Y j))‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ C1' * B' := mul_le_mul hL ((hB _ hmem).trans (le_max_left _ _))
            (norm_nonneg _) ((norm_nonneg _).trans hL)
    · rw [fderiv_configLift_eq_zero hK Φ hsupp s Y hmem]
      simp only [ContinuousLinearMap.zero_apply, norm_zero]
      exact mul_nonneg (le_max_right _ _) (le_max_right _ _)
  have hsec : ‖(1 / 2 : ℝ) * ∑ k : Fin N × Fin d,
      fderiv ℝ (fderiv ℝ (configLift Φ s)) Y (liftedNoise D k) (liftedNoise D k)‖
        ≤ (1 / 2) * (C2' * ∑ k : Fin N × Fin d, ‖liftedNoise D k‖ * ‖liftedNoise D k‖) := by
    have hC2s : ‖fderiv ℝ (fderiv ℝ (configLift Φ s)) Y‖ ≤ C2' :=
      (hC2 s hs Y).trans (le_max_left _ _)
    have hterm : ∀ k : Fin N × Fin d,
        ‖fderiv ℝ (fderiv ℝ (configLift Φ s)) Y (liftedNoise D k) (liftedNoise D k)‖
          ≤ C2' * (‖liftedNoise D k‖ * ‖liftedNoise D k‖) := fun k =>
      calc ‖fderiv ℝ (fderiv ℝ (configLift Φ s)) Y (liftedNoise D k) (liftedNoise D k)‖
          ≤ ‖fderiv ℝ (fderiv ℝ (configLift Φ s)) Y‖ * ‖liftedNoise D k‖ * ‖liftedNoise D k‖ :=
            ContinuousLinearMap.le_opNorm₂ _ _ _
        _ ≤ C2' * ‖liftedNoise D k‖ * ‖liftedNoise D k‖ := by gcongr
        _ = C2' * (‖liftedNoise D k‖ * ‖liftedNoise D k‖) := by ring
    calc ‖(1 / 2 : ℝ) * ∑ k : Fin N × Fin d,
          fderiv ℝ (fderiv ℝ (configLift Φ s)) Y (liftedNoise D k) (liftedNoise D k)‖
        = (1 / 2) * ‖∑ k : Fin N × Fin d,
          fderiv ℝ (fderiv ℝ (configLift Φ s)) Y (liftedNoise D k) (liftedNoise D k)‖ := by
          rw [norm_mul]; norm_num
      _ ≤ (1 / 2) * ∑ k : Fin N × Fin d,
          ‖fderiv ℝ (fderiv ℝ (configLift Φ s)) Y (liftedNoise D k) (liftedNoise D k)‖ := by
          gcongr; exact norm_sum_le _ _
      _ ≤ (1 / 2) * ∑ k : Fin N × Fin d, C2' * (‖liftedNoise D k‖ * ‖liftedNoise D k‖) := by
          gcongr with k
          exact hterm k
      _ = (1 / 2) * (C2' * ∑ k : Fin N × Fin d, ‖liftedNoise D k‖ * ‖liftedNoise D k‖) := by
          simp only [Finset.mul_sum]
  unfold fkeIto
  have h0 : ‖derivWithin (fun r => configLift Φ r Y) (Icc 0 T) s‖ ≤ C0' :=
    (hC0 s hs Y).trans (le_max_left _ _)
  calc _ ≤ ‖derivWithin (fun r => configLift Φ r Y) (Icc 0 T) s‖
        + ‖fderiv ℝ (configLift Φ s) Y (driftVec D (fun j => Torus.mk (Y j)))‖
        + ‖(1 / 2 : ℝ) * ∑ k : Fin N × Fin d,
          fderiv ℝ (fderiv ℝ (configLift Φ s)) Y (liftedNoise D k) (liftedNoise D k)‖ :=
          norm_add₃_le
    _ ≤ C0' + C1' * B' + (1 / 2) * (C2' * ∑ k : Fin N × Fin d,
          ‖liftedNoise D k‖ * ‖liftedNoise D k‖) := by linarith

/-! ### Narrow continuity of the selected law -/

theorem selectedFlow_toContact {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {D : DynData d} {T : ℝ} {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X : ℝ≥0 → Ω → Config d N} (hX : SelectedFlow P D T X₀ W X) :
    IsContactStrongSolution P D T X₀ W X := by
  rcases hX.flow with h | h
  · exact h.1.toContact
  · exact h.2.2.2.2.toContact

/-- Narrow continuity of `t ↦ P_N^t` on `[0,T]` (bounded continuous tests). -/
theorem selectedLaw_narrow_continuous {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {D : DynData d} {T : ℝ} {X₀ : Ω → Config d N}
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hX : SelectedFlow P D T X₀ W X) :
    ∀ ψ : BoundedContinuousFunction (Fin N → Torus d) ℝ,
      ContinuousOn (fun t : ℝ => ∫ x, ψ x ∂(selectedLaw P X t)) (Set.Icc 0 T) := by
  intro ψ
  have hC := selectedFlow_toContact hX
  have hmeas : ∀ t : ℝ, Measurable (X (Real.toNNReal t)) := fun t => hC.adapted _
  have heq : ∀ t : ℝ, ∫ x, ψ x ∂(selectedLaw P X t) = ∫ ω, ψ (X (Real.toNNReal t) ω) ∂P :=
    fun t => integral_map (hmeas t).aemeasurable ψ.continuous.aestronglyMeasurable
  simp only [heq]
  intro t0 _
  unfold ContinuousWithinAt
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => ‖ψ‖) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun t =>
      (ψ.continuous.measurable.comp (hmeas t)).aestronglyMeasurable
  · exact Eventually.of_forall fun t => Eventually.of_forall fun ω => ψ.norm_coe_le_norm _
  · exact integrable_const _
  · filter_upwards [hC.cont] with ω hω
    have hc : Continuous fun t : ℝ => X (Real.toNNReal t) ω :=
      continuous_pi fun i => (hω i).comp continuous_real_toNNReal
    exact ((ψ.continuous.comp hc).tendsto t0).mono_left nhdsWithin_le_nhds

/-! ### Lattice invariance and measurability -/

theorem measurable_repC : Measurable (repC : Config d N → (Fin N → Euc d)) :=
  measurable_pi_iff.2 fun i => (measurable_torusRep d).comp (measurable_pi_apply i)

theorem mk_add_lattice_vec {v : Fin N → Euc d} (hv : IsLatticeVec v) (Y : Fin N → Euc d) :
    (fun j => Torus.mk ((Y + v) j)) = fun j => Torus.mk (Y j) := by
  funext j
  obtain ⟨n, hn⟩ := hv j
  have h := Torus.lift_periodic (fun t : Torus d => t) (Y j) n
  simp only [Pi.add_apply, hn]
  exact h

theorem fkeIto_add_lattice (D : DynData d) (T : ℝ) (Φ : ℝ → Config d N → ℝ) (s : ℝ)
    {v : Fin N → Euc d} (hv : IsLatticeVec v) (Y : Fin N → Euc d) :
    fkeIto D T Φ s (Y + v) = fkeIto D T Φ s Y := by
  have hc : ∀ r Y', configLift Φ r (Y' + v) = configLift Φ r Y' :=
    fun r Y' => configLift_add_lattice Φ r hv Y'
  unfold fkeIto
  rw [mk_add_lattice_vec hv Y]
  simp only [hc, fderiv_configLift_add_lattice Φ s hv, fderiv2_configLift_add_lattice Φ s hv]

theorem fderiv_configLift_eq_of_mk (Φ : ℝ → Config d N → ℝ) (r : ℝ) {Y Y' : Fin N → Euc d}
    (h : ∀ i, Torus.mk (Y i) = Torus.mk (Y' i)) :
    fderiv ℝ (configLift Φ r) Y = fderiv ℝ (configLift Φ r) Y' := by
  obtain ⟨v, hv, rfl⟩ := exists_lattice_shift h
  exact (fderiv_configLift_add_lattice Φ r hv Y).symm

theorem configLift_eq_of_mk (Φ : ℝ → Config d N → ℝ) (r : ℝ) {Y Y' : Fin N → Euc d}
    (h : ∀ i, Torus.mk (Y i) = Torus.mk (Y' i)) :
    configLift Φ r Y = configLift Φ r Y' := by
  obtain ⟨v, hv, rfl⟩ := exists_lattice_shift h
  exact (configLift_add_lattice Φ r hv Y).symm

theorem fkeIto_eq_of_mk (D : DynData d) (T : ℝ) (Φ : ℝ → Config d N → ℝ) (s : ℝ)
    {Y Y' : Fin N → Euc d} (h : ∀ i, Torus.mk (Y i) = Torus.mk (Y' i)) :
    fkeIto D T Φ s Y = fkeIto D T Φ s Y' := by
  obtain ⟨v, hv, rfl⟩ := exists_lattice_shift h
  exact (fkeIto_add_lattice D T Φ s hv Y).symm

/-- The generator and interaction of Proposition B.3 as the Itô drift at a lift of the configuration. -/
theorem fkeGI_eq_fkeIto (D : DynData d) (hsd : D.s < d) (T : ℝ) (Φ : ℝ → Config d N → ℝ)
    (s : ℝ) (x : Config d N) :
    fkeGenerator D T Φ s x + fkeInteraction D Φ s x = fkeIto D T Φ s (repC x) := by
  rw [fkeIto_eq D hsd T Φ s (repC x), mk_repC]

/-- The Itô drift of the lifted process, at a point where the lift projects to `X`. -/
theorem itoDrift_eq_fkeIto {Ω : Type*} [mΩ : MeasurableSpace Ω] (D : DynData d) (T : ℝ)
    (Φ : ℝ → Config d N → ℝ) (Zl : ℝ≥0 → Ω → (Fin N → Euc d)) (Xc : ℝ≥0 → Ω → Config d N)
    (ω : Ω) (s : ℝ)
    (hx : Xc (Real.toNNReal s) ω = fun j => Torus.mk (Zl (Real.toNNReal s) ω j)) :
    itoDrift T (configLift Φ) (ofNNRealTime Zl) (ofNNRealTime (driftProc D Xc))
      (fun _ _ => liftedNoise D) s ω = fkeIto D T Φ s (Zl (Real.toNNReal s) ω) := by
  unfold itoDrift fkeIto
  simp only [ofNNRealTime_apply, driftProc, hx]

theorem measurable_fkeIto_lift {T : ℝ} (hT : 0 ≤ T) (D : DynData d) (hV : Torus.IsCk 2 D.V)
    (Φ : ℝ → Config d N → ℝ) (hΦ : IsC12On T Set.univ (configLift Φ)) :
    Measurable (fun p : ℝ × (Fin N → Euc d) => fkeIto D T Φ (clampTI T p.1) p.2) := by
  have hq : Continuous (fun q : ℝ × (Fin N → Euc d) => (clampTI T q.1, q.2)) :=
    ((continuous_clampTI T).comp continuous_fst).prodMk continuous_snd
  have hmem : ∀ q : ℝ × (Fin N → Euc d),
      (clampTI T q.1, q.2) ∈ Icc 0 T ×ˢ (univ : Set (Fin N → Euc d)) :=
    fun q => ⟨clampTI_mem hT q.1, mem_univ _⟩
  have hdt : Continuous (fun q : ℝ × (Fin N → Euc d) =>
      derivWithin (fun r => configLift Φ r q.2) (Icc 0 T) (clampTI T q.1)) :=
    ContinuousOn.comp_continuous hΦ.cont_deriv hq hmem
  have hfd : Continuous (fun q : ℝ × (Fin N → Euc d) =>
      fderiv ℝ (configLift Φ (clampTI T q.1)) q.2) :=
    ContinuousOn.comp_continuous hΦ.cont_fderiv hq hmem
  have hfd2 : Continuous (fun q : ℝ × (Fin N → Euc d) =>
      fderiv ℝ (fderiv ℝ (configLift Φ (clampTI T q.1))) q.2) :=
    ContinuousOn.comp_continuous hΦ.cont_fderiv₂ hq hmem
  have hmk : Measurable (fun Y : Fin N → Euc d => fun j => Torus.mk (Y j)) :=
    measurable_pi_iff.2 fun j => Torus.continuous_mk.measurable.comp (measurable_pi_apply j)
  have hdrift : Measurable (fun p : ℝ × (Fin N → Euc d) =>
      driftVec D (fun j => Torus.mk (p.2 j))) :=
    (measurable_driftVec hV).comp (hmk.comp measurable_snd)
  have h4 : Measurable (fun p : ℝ × (Fin N → Euc d) =>
      fderiv ℝ (configLift Φ (clampTI T p.1)) p.2 (driftVec D (fun j => Torus.mk (p.2 j)))) :=
    (continuous_fst.clm_apply continuous_snd).measurable.comp (hfd.measurable.prodMk hdrift)
  have h5 : Measurable (fun p : ℝ × (Fin N → Euc d) => (1 / 2 : ℝ) * ∑ k : Fin N × Fin d,
      fderiv ℝ (fderiv ℝ (configLift Φ (clampTI T p.1))) p.2 (liftedNoise D k) (liftedNoise D k)) := by
    refine measurable_const.mul (Finset.measurable_sum _ fun k _ => ?_)
    have ha : Measurable (fun p : ℝ × (Fin N → Euc d) =>
        fderiv ℝ (fderiv ℝ (configLift Φ (clampTI T p.1))) p.2 (liftedNoise D k)) :=
      hfd2.measurable.apply_continuousLinearMap (liftedNoise D k)
    exact ha.apply_continuousLinearMap (liftedNoise D k)
  exact ((hdt.measurable.add h4).add h5)

theorem measurable_fkeIto_clamp_config {T : ℝ} (hT : 0 ≤ T) (D : DynData d) (hV : Torus.IsCk 2 D.V)
    (Φ : ℝ → Config d N → ℝ) (hΦ : IsC12On T Set.univ (configLift Φ)) :
    Measurable (fun p : ℝ × Config d N => fkeIto D T Φ (clampTI T p.1) (repC p.2)) :=
  (measurable_fkeIto_lift hT D hV Φ hΦ).comp (measurable_fst.prodMk (measurable_repC.comp measurable_snd))

/-- Joint measurability of the clamped test function along the progressive process. -/
theorem measurable_fkeIto_sample {Ω : Type*} [mΩ : MeasurableSpace Ω] {ℱ : Filtration ℝ mΩ}
    {X : ℝ≥0 → Ω → Config d N} (hF : IsProgressive ℱ (ofNNRealTime X)) {T : ℝ} (hT : 0 ≤ T)
    (D : DynData d) (hV : Torus.IsCk 2 D.V) (Φ : ℝ → Config d N → ℝ)
    (hΦ : IsC12On T Set.univ (configLift Φ)) :
    Measurable (fun p : ℝ × Ω => fkeIto D T Φ (clampTI T p.1) (repC (X (Real.toNNReal p.1) p.2))) := by
  have hrep : IsProgressive ℱ (fun s ω => repC (ofNNRealTime X s ω)) :=
    isProgressive_comp_measurable' (ofNNRealTime X) hF (fun _ x => repC x)
      (measurable_repC.comp measurable_snd)
  have hR : Measurable (fun p : ℝ × Ω => repC (ofNNRealTime X p.1 p.2)) :=
    measurable_of_progressive hrep
  exact (measurable_fkeIto_lift hT D hV Φ hΦ).comp (measurable_fst.prodMk hR)

/-! ### Sampled drift, reference martingale integrand, and the Fubini step -/

/-- The sampled drift `s ↦ fkeIto (clamp s) (repC X_s)` along the configuration process. -/
def fkeSample {Ω : Type*} (D : DynData d) (T : ℝ) (Φ : ℝ → Config d N → ℝ)
    (X : ℝ≥0 → Ω → Config d N) (s : ℝ) (ω : Ω) : ℝ :=
  fkeIto D T Φ (clampTI T s) (repC (X (Real.toNNReal s) ω))

/-- The progressive reference version of the martingale integrand `fderiv (configLift Φ s) X_s (σ_k)`
(zero off `[0,T]`). -/
def fkeRef {Ω : Type*} (D : DynData d) (T : ℝ) (Φ : ℝ → Config d N → ℝ)
    (X : ℝ≥0 → Ω → Config d N) (s : ℝ) (ω : Ω) (k : Fin N × Fin d) : ℝ :=
  if s ∈ Set.Icc 0 T then
    fderiv ℝ (configLift Φ (clampTI T s)) (repC (X (Real.toNNReal s) ω)) (liftedNoise D k)
  else 0

theorem continuous_fderiv_clamp {T : ℝ} (hT : 0 ≤ T) (Φ : ℝ → Config d N → ℝ)
    (hΦ : IsC12On T Set.univ (configLift Φ)) :
    Continuous (fun q : ℝ × (Fin N → Euc d) => fderiv ℝ (configLift Φ (clampTI T q.1)) q.2) := by
  have hq : Continuous (fun q : ℝ × (Fin N → Euc d) => (clampTI T q.1, q.2)) :=
    ((continuous_clampTI T).comp continuous_fst).prodMk continuous_snd
  exact ContinuousOn.comp_continuous hΦ.cont_fderiv hq
    (fun q => ⟨clampTI_mem hT q.1, mem_univ _⟩)

theorem isProgressive_fkeRef {Ω : Type*} [mΩ : MeasurableSpace Ω] {ℱ : Filtration ℝ mΩ}
    {X : ℝ≥0 → Ω → Config d N} (hF : IsProgressive ℱ (ofNNRealTime X)) {T : ℝ} (hT : 0 ≤ T)
    (D : DynData d) (Φ : ℝ → Config d N → ℝ) (hΦ : IsC12On T Set.univ (configLift Φ)) :
    IsProgressive ℱ (fun s ω k => fkeRef D T Φ X s ω k) := by
  have hrep : IsProgressive ℱ (fun s ω => repC (ofNNRealTime X s ω)) :=
    isProgressive_comp_measurable' (ofNNRealTime X) hF (fun _ x => repC x)
      (measurable_repC.comp measurable_snd)
  have hk : ∀ k : Fin N × Fin d, IsProgressive ℱ (fun s ω => fkeRef D T Φ X s ω k) := by
    intro k
    have hc := (continuous_fderiv_clamp hT Φ hΦ).clm_apply
      (continuous_const (y := liftedNoise D k))
    have hm : Measurable (Function.uncurry (fun (s : ℝ) (y : Fin N → Euc d) =>
        if s ∈ Set.Icc 0 T then fderiv ℝ (configLift Φ (clampTI T s)) y (liftedNoise D k) else 0)) :=
      Measurable.ite (measurableSet_Icc.preimage measurable_fst) hc.measurable measurable_const
    exact isProgressive_comp_measurable' (fun s ω => repC (ofNNRealTime X s ω)) hrep
      (fun (s : ℝ) (y : Fin N → Euc d) =>
        if s ∈ Set.Icc 0 T then fderiv ℝ (configLift Φ (clampTI T s)) y (liftedNoise D k) else 0) hm
  exact isProgressive_pi hk

theorem fkeRef_bound {Ω : Type*} {X : ℝ≥0 → Ω → Config d N} {T : ℝ} (hT : 0 ≤ T)
    (D : DynData d) (Φ : ℝ → Config d N → ℝ) {C1 : ℝ} (hC1 : ∀ s ∈ Set.Icc 0 T, ∀ Y, ‖fderiv ℝ (configLift Φ s) Y‖ ≤ C1)
    (s : ℝ) (ω : Ω) (k : Fin N × Fin d) :
    |fkeRef D T Φ X s ω k| ≤ max C1 0 * ∑ j : Fin N × Fin d, ‖liftedNoise D j‖ := by
  unfold fkeRef
  split_ifs with hs
  · rw [← Real.norm_eq_abs]
    have hb : ‖fderiv ℝ (configLift Φ (clampTI T s)) (repC (X (Real.toNNReal s) ω))‖ ≤ max C1 0 :=
      (hC1 _ (clampTI_mem hT s) _).trans (le_max_left _ _)
    calc ‖fderiv ℝ (configLift Φ (clampTI T s)) (repC (X (Real.toNNReal s) ω)) (liftedNoise D k)‖
        ≤ ‖fderiv ℝ (configLift Φ (clampTI T s)) (repC (X (Real.toNNReal s) ω))‖ * ‖liftedNoise D k‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ max C1 0 * ‖liftedNoise D k‖ :=
          mul_le_mul hb le_rfl (norm_nonneg _) ((norm_nonneg _).trans hb)
      _ ≤ max C1 0 * ∑ j : Fin N × Fin d, ‖liftedNoise D j‖ :=
          mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun j _ => norm_nonneg _)
            (Finset.mem_univ k)) (le_max_right _ _)
  · simp only [abs_zero]
    exact mul_nonneg (le_max_right _ _) (Finset.sum_nonneg fun j _ => norm_nonneg _)

/-- The Itô integrand of the lifted process agrees with the reference integrand on the event
where the lift projects to the configuration. -/
theorem itoIntegrand_eq_fkeRef {Ω : Type*} [mΩ : MeasurableSpace Ω] {T : ℝ}
    (D : DynData d) (Φ : ℝ → Config d N → ℝ)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (X : ℝ≥0 → Ω → Config d N) (ω : Ω)
    (hω : ∀ τ : ℝ≥0, (τ : ℝ) ≤ T → X τ ω = fun i => Torus.mk (liftProcM D W' X τ ω i))
    (s : ℝ) (k : Fin N × Fin d) :
    itoIntegrand T Set.univ (configLift Φ) (ofNNRealTime (liftProcM D W' X))
      (fun _ _ => liftedNoise D) s ω k = fkeRef D T Φ X s ω k := by
  unfold itoIntegrand fkeRef
  by_cases hs : s ∈ Set.Icc 0 T
  · have hτ : ((Real.toNNReal s : ℝ≥0) : ℝ) ≤ T := by
      rw [Real.coe_toNNReal _ hs.1]
      exact hs.2
    have hmk : ∀ i, Torus.mk (liftProcM D W' X (Real.toNNReal s) ω i)
        = Torus.mk (repC (X (Real.toNNReal s) ω) i) := by
      intro i
      show _ = Torus.mk (Torus.rep (X (Real.toNNReal s) ω i))
      rw [Torus.mk_rep]
      exact (congrFun (hω _ hτ) i).symm
    have hfd := fderiv_configLift_eq_of_mk Φ s hmk
    simp only [if_pos hs, Set.indicator_of_mem hs, Set.mem_setOf_eq, Set.mem_univ,
      Set.setOf_true, Set.indicator_univ, ofNNRealTime_apply, clampTI_of_mem hs]
    rw [hfd]
  · simp [hs]


/-- The selected law at a deterministic time, integrated against a measurable test function. -/
theorem integral_selectedLaw_eq {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {D : DynData d} {T : ℝ} {X₀ : Ω → Config d N}
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hC : IsContactStrongSolution P D T X₀ W X) (t : ℝ) {g : Config d N → ℝ} (hg : Measurable g) :
    ∫ x, g x ∂(selectedLaw P X t) = ∫ ω, g (X (Real.toNNReal t) ω) ∂P :=
  integral_map (hC.adapted _).aemeasurable hg.aestronglyMeasurable

/-- The distributional forward Kolmogorov identity (Proposition B.3, FKE part). -/
theorem selected_law_fke_FKE {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {D : DynData d} (hN : 2 ≤ N) (hV : Torus.IsCk 2 D.V) {T : ℝ} (hT : 0 < T)
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hX : SelectedFlow P D T X₀ W X) (hF : IsFilteredSolution P ℱ W' W X)
    (Φ : ℝ → Config d N → ℝ) (hΦ : IsFKETest T Φ) :
    - ∫ x, Φ 0 x ∂(selectedLaw P X 0)
      = ∫ r in (0:ℝ)..T, ∫ x, (fkeGenerator D T Φ r x + fkeInteraction D Φ r x) ∂(selectedLaw P X r) := by
  have hT0 : 0 ≤ T := hT.le
  have hN0 : 0 < N := by omega
  have hsd : D.s < d := D.hsd
  have hC := selectedFlow_toContact hX
  obtain ⟨Tp, hTp, hzero⟩ := hΦ.time_support
  obtain ⟨K, hK, hdisj, hsupp⟩ := hΦ.space_support
  have hΦc := hΦ.c12
  obtain ⟨C0, hC0⟩ := bounded_of_periodic (T := T) (fun s Y => configLift Φ s Y) hΦc.cont
    (fun s Y v hv => configLift_add_lattice Φ s hv Y)
  obtain ⟨C1, hC1⟩ := bounded_of_periodic (T := T) (fun s Y => fderiv ℝ (configLift Φ s) Y)
    hΦc.cont_fderiv (fun s Y v hv => fderiv_configLift_add_lattice Φ s hv Y)
  obtain ⟨Cf, hCf⟩ := fkeIto_bound hT0 D hN0 hV Φ hΦc hK hdisj hsupp
  -- almost sure lift facts
  have hlift := hC.ae_lift_eq hF
  have hI0 : ∀ᵐ ω ∂P, IntegrableOn (fun s : ℝ => driftProc D X (Real.toNNReal s) ω) (Set.Icc 0 T) :=
    hC.ae_integrableOn_drift hT0 le_rfl
  have hint : ∀ᵐ ω ∂P, ∀ τ : ℝ≥0, (τ : ℝ) ≤ T →
      intPart D X τ ω = ∫ s in Set.Icc (0 : ℝ) (τ : ℝ), driftProc D X (Real.toNNReal s) ω := by
    filter_upwards [hI0] with ω hω τ hτ
    exact intPart_eq_integral ω τ (hω.mono_set (Set.Icc_subset_Icc le_rfl hτ))
  have hlift' : ∀ᵐ ω ∂P, ∀ τ : ℝ≥0, (τ : ℝ) ≤ T →
      X τ ω = fun i => Torus.mk (liftProcM D W' X τ ω i) := by
    filter_upwards [hlift, hint] with ω h1 h2 τ hτ
    rw [h1 τ hτ]
    funext i
    simp only [liftProcM, liftProc, h2 τ hτ]
  have hZint : ∀ᵐ ω ∂P, ∀ τ : ℝ≥0, (τ : ℝ) ≤ T →
      liftProcM D W' X τ ω = liftProcM D W' X 0 ω
        + (∫ s in Set.Icc (0 : ℝ) τ, driftProc D X (Real.toNNReal s) ω)
        + ∑ k, (W' τ ω k - W' 0 ω k) • liftedNoise D k := by
    filter_upwards [hint] with ω hω τ hτ
    rw [liftProcM_zero ω]
    simp only [liftProcM]
    rw [hω τ hτ]
  have hX₀ : ∀ s : ℝ, Measurable[ℱ s] (liftProcM D W' X 0) := by
    intro s
    have e : liftProcM D W' X 0 = fun ω => fun i => Torus.rep (X 0 ω i) :=
      funext fun ω => liftProcM_zero ω
    rw [e]
    have hg : Measurable (fun x : Config d N => fun i => Torus.rep (x i)) :=
      measurable_pi_iff.2 fun i => (measurable_torusRep d).comp (measurable_pi_apply i)
    exact hg.comp (hF.measurable_init s)
  -- Itô's formula for `configLift Φ` along the lift
  have hito := ito_formula_additive (P := P) (ℱ := ℱ) hF.brownian (T := T) hT0 (configLift Φ) hΦc
    (liftedNoise D) (liftProcM D W' X) (measurable_liftProcM hV hF) hX₀ (driftProc D X)
    (isProgressive_driftProc hV hF) hI0 hZint
  have hτ : ((Real.toNNReal T : ℝ≥0) : ℝ) = T := Real.coe_toNNReal T hT0
  have hcore : ∀ᵐ ω ∂P, Φ 0 (X 0 ω) + (∫ s in Set.Icc (0:ℝ) T, fkeSample D T Φ X s ω)
      + localItoIntegral P ℱ W' (itoIntegrand T Set.univ (configLift Φ)
          (ofNNRealTime (liftProcM D W' X)) (fun _ _ => liftedNoise D)) T ω = 0 := by
    filter_upwards [hito, hlift'] with ω hωito hω
    have h := hωito.2 (Real.toNNReal T) (le_of_eq hτ)
    rw [hτ] at h
    have hL : configLift Φ T (liftProcM D W' X (Real.toNNReal T) ω) = 0 := by
      show Φ T (fun i => Torus.mk (liftProcM D W' X (Real.toNNReal T) ω i)) = 0
      rw [← hω (Real.toNNReal T) (le_of_eq hτ)]
      exact hzero T hTp.le _
    have hcol0 : configLift Φ 0 (liftProcM D W' X 0 ω) = Φ 0 (X 0 ω) := by
      have h0 := hω 0 (by simpa using hT0)
      show Φ 0 (fun i => Torus.mk (liftProcM D W' X 0 ω i)) = Φ 0 (X 0 ω)
      rw [h0]
    have hint2 : ∫ s in Set.Icc (0:ℝ) T, itoDrift T (configLift Φ)
        (ofNNRealTime (liftProcM D W' X)) (ofNNRealTime (driftProc D X))
        (fun _ _ => liftedNoise D) s ω = ∫ s in Set.Icc (0:ℝ) T, fkeSample D T Φ X s ω := by
      refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
      have hsτ : ((Real.toNNReal s : ℝ≥0) : ℝ) ≤ T := by
        rw [Real.coe_toNNReal _ hs.1]
        exact hs.2
      have hx := hω _ hsτ
      rw [itoDrift_eq_fkeIto D T Φ (liftProcM D W' X) X ω s hx]
      unfold fkeSample
      rw [clampTI_of_mem hs]
      have hmk : ∀ i, Torus.mk (repC (X (Real.toNNReal s) ω) i)
          = Torus.mk (liftProcM D W' X (Real.toNNReal s) ω i) := by
        intro i
        show Torus.mk (Torus.rep (X (Real.toNNReal s) ω i)) = _
        rw [Torus.mk_rep]
        exact congrFun hx i
      exact (fkeIto_eq_of_mk D T Φ s hmk).symm
    rw [hL, hcol0, hint2] at h
    linarith
  -- the reference integrand and the martingale term
  have hΨprog := isProgressive_fkeRef hF.progressive hT0 D Φ hΦc
  have hΨL2 : IsProgressiveL2 P ℱ (fun s ω k => fkeRef D T Φ X s ω k) :=
    IsProgressiveL2.of_bounded P hΨprog (max C1 0 * ∑ j : Fin N × Fin d, ‖liftedNoise D j‖)
      (fun s ω k => fkeRef_bound hT0 D Φ hC1 s ω k)
  obtain ⟨N0, hN0m, hN0P, hN0⟩ := exists_null_of_ae (P := P)
    (p := fun ω => ∀ τ : ℝ≥0, (τ : ℝ) ≤ T → X τ ω = fun i => Torus.mk (liftProcM D W' X τ ω i)) hlift'
  have hMart : ∀ᵐ ω ∂P, localItoIntegral P ℱ W' (itoIntegrand T Set.univ (configLift Φ)
          (ofNNRealTime (liftProcM D W' X)) (fun _ _ => liftedNoise D)) T ω
        = itoIntegral P ℱ W' (fun s ω k => fkeRef D T Φ X s ω k) T ω := by
    have hcongr := localItoIntegral_congr_null hF.brownian hΨL2.locL2 hN0m hN0P
      (Ψ := itoIntegrand T Set.univ (configLift Φ) (ofNNRealTime (liftProcM D W' X))
        (fun _ _ => liftedNoise D))
      (fun s ω hω => by
        funext k
        exact itoIntegrand_eq_fkeRef D Φ W' X ω (hN0 ω hω) s k)
      (fun s hs ω => by
        have hn : s ∉ Set.Icc (0:ℝ) T := fun h => absurd h.1 (not_le.2 hs)
        funext k
        simp [itoIntegrand, hn])
      (fun s hs ω => by
        have hn : s ∉ Set.Icc (0:ℝ) T := fun h => absurd h.1 (not_le.2 hs)
        funext k
        simp [fkeRef, hn])
    have hloc := localItoIntegral_eq_itoIntegral hF.brownian hΨL2
    filter_upwards [hcongr, hloc] with ω h1 h2
    rw [h1 T, h2 T]
  have hMLp : MemLp (itoIntegral P ℱ W' (fun s ω k => fkeRef D T Φ X s ω k) T) 2 P :=
    memLp_two_itoIntegral hF.brownian hΨL2 T
  have hMint : ∫ ω, itoIntegral P ℱ W' (fun s ω k => fkeRef D T Φ X s ω k) T ω ∂P = 0 :=
    integral_itoIntegral hF.brownian hΨL2 T
  have hsum : ∀ᵐ ω ∂P, Φ 0 (X 0 ω) + (∫ s in Set.Icc (0:ℝ) T, fkeSample D T Φ X s ω)
      + itoIntegral P ℱ W' (fun s ω k => fkeRef D T Φ X s ω k) T ω = 0 := by
    filter_upwards [hcore, hMart] with ω h1 h2
    rw [h2] at h1
    exact h1
  -- integrability
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc (0:ℝ) T)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
  have hprodm : Measurable (fun p : ℝ × Ω => fkeSample D T Φ X p.1 p.2) :=
    measurable_fkeIto_sample hF.progressive hT0 D hV Φ hΦc
  have hprodint : Integrable (fun p : ℝ × Ω => fkeSample D T Φ X p.1 p.2)
      ((volume.restrict (Set.Icc (0:ℝ) T)).prod P) :=
    Integrable.of_bound hprodm.aestronglyMeasurable Cf
      (ae_of_all _ fun p => hCf _ (clampTI_mem hT0 p.1) (repC (X (Real.toNNReal p.1) p.2)))
  have hIint : Integrable (fun ω => ∫ s in Set.Icc (0:ℝ) T, fkeSample D T Φ X s ω) P :=
    hprodint.integral_prod_right
  have hm0 : Measurable (fun x : Config d N => Φ 0 x) := by
    have e : (fun x : Config d N => Φ 0 x) = fun x => configLift Φ 0 (repC x) := by
      funext x
      show Φ 0 x = Φ 0 (fun i => Torus.mk (repC x i))
      rw [mk_repC]
    have hcont0 : Continuous (configLift Φ 0) :=
      hΦc.cont.comp_continuous (continuous_const.prodMk continuous_id)
        (fun Y => ⟨⟨le_refl (0:ℝ), hT0⟩, Set.mem_univ Y⟩)
    rw [e]
    exact hcont0.measurable.comp measurable_repC
  have hΦ0int : Integrable (fun ω => Φ 0 (X 0 ω)) P := by
    have hb : ∀ x : Config d N, ‖Φ 0 x‖ ≤ C0 := fun x => by
      have e : Φ 0 x = configLift Φ 0 (repC x) := by
        show Φ 0 x = Φ 0 (fun i => Torus.mk (repC x i))
        rw [mk_repC]
      rw [e]
      exact (hC0 0 ⟨le_refl (0:ℝ), hT0⟩ (repC x)).trans' (le_refl _)
    exact Integrable.of_bound ((hm0.comp (hC.adapted 0)).aestronglyMeasurable) C0
      (ae_of_all _ fun ω => hb _)
  have hMi : Integrable (fun ω => itoIntegral P ℱ W' (fun s ω k => fkeRef D T Φ X s ω k) T ω) P :=
    hMLp.integrable one_le_two
  -- Fubini and the identification with the selected law
  have hIeq : ∫ ω, (∫ s in Set.Icc (0:ℝ) T, fkeSample D T Φ X s ω) ∂P
      = ∫ r in Set.Icc (0:ℝ) T, ∫ x, (fkeGenerator D T Φ r x + fkeInteraction D Φ r x)
          ∂(selectedLaw P X r) := by
    have hswap := integral_integral_swap (μ := volume.restrict (Set.Icc (0:ℝ) T)) (ν := P)
      (f := fun s ω => fkeSample D T Φ X s ω) hprodint
    rw [← hswap]
    refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    have hg : Measurable (fun x : Config d N => fkeIto D T Φ (clampTI T r) (repC x)) :=
      (measurable_fkeIto_lift hT0 D hV Φ hΦc).comp (measurable_const.prodMk measurable_repC)
    have e : ∀ x : Config d N, fkeGenerator D T Φ r x + fkeInteraction D Φ r x
        = fkeIto D T Φ (clampTI T r) (repC x) := by
      intro x
      rw [clampTI_of_mem hr]
      exact fkeGI_eq_fkeIto D hsd T Φ r x
    simp only [e]
    exact (integral_selectedLaw_eq hC r hg).symm
  have hLHS : ∫ x, Φ 0 x ∂(selectedLaw P X 0) = ∫ ω, Φ 0 (X 0 ω) ∂P := by
    have hm0' : Measurable (fun x : Config d N => Φ 0 x) := hm0
    rw [integral_selectedLaw_eq hC 0 hm0', Real.toNNReal_zero]
  have hzeroint : ∫ ω, (Φ 0 (X 0 ω) + (∫ s in Set.Icc (0:ℝ) T, fkeSample D T Φ X s ω)
      + itoIntegral P ℱ W' (fun s ω k => fkeRef D T Φ X s ω k) T ω) ∂P = 0 := by
    rw [integral_congr_ae hsum]
    simp
  have hA : Integrable (fun ω => Φ 0 (X 0 ω) + ∫ s in Set.Icc (0:ℝ) T, fkeSample D T Φ X s ω) P :=
    hΦ0int.add hIint
  rw [integral_add hA hMi, integral_add hΦ0int hIint, hMint, add_zero] at hzeroint
  rw [intervalIntegral.integral_of_le hT0, ← integral_Icc_eq_integral_Ioc, ← hIeq, hLHS]
  linarith

/-- Proposition B.3 (row 5, `M:B:prop:selected-law-fke`): under Assumption A.1 the selected law is
narrowly continuous on `[0,T]` and is a distributional solution of the forward Kolmogorov equation
on `(0,T) × Ω_N` for the compactly supported tests `IsFKETest`. -/
theorem selected_law_fke
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d N : ℕ} (hN : 2 ≤ N) [NeZero N]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {D : DynData d} (hV : Torus.IsCk 2 D.V) {T : ℝ} (hT : 0 < T) {X₀ : Ω → Config d N}
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hX : SelectedFlow P D T X₀ W X) (hF : IsFilteredSolution P ℱ W' W X) :
    -- narrow continuity of t ↦ P_N^t on [0,T]
    (∀ ψ : BoundedContinuousFunction (Fin N → Torus d) ℝ,
        ContinuousOn (fun t : ℝ => ∫ x, ψ x ∂(selectedLaw P X t)) (Set.Icc 0 T)) ∧
    -- distributional FKE on (0,T) × Ω_N
    ∀ Φ, IsFKETest T Φ →
      - ∫ x, Φ 0 x ∂(selectedLaw P X 0)
        = ∫ r in (0:ℝ)..T, ∫ x, (fkeGenerator D T Φ r x + fkeInteraction D Φ r x) ∂(selectedLaw P X r) :=
  ⟨selectedLaw_narrow_continuous hX, fun Φ hΦ => selected_law_fke_FKE hN hV hT hX hF Φ hΦ⟩

/-! ### The empirical corollary `cepa_empirical_fke`: uniform bounds and the kernel -/

theorem matVec_bound {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v : Euc d, ‖Torus.matVec M v‖ ≤ K * ‖v‖ := by
  refine ⟨‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)‖, norm_nonneg _, fun v => ?_⟩
  have h := (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)).le_opNorm v
  simpa [Torus.matVec] using h

theorem norm_fderiv_gradient_le {F : Euc d → ℝ} (hF : ContDiff ℝ 2 F) (z : Euc d) :
    ‖fderiv ℝ (gradient F) z‖ ≤ ‖fderiv ℝ (fderiv ℝ F) z‖ := by
  have hfd : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) z) z :=
    ((hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) z).hasFDerivAt
  have he' := ((InnerProductSpace.toDual ℝ (Euc d)).symm.toContinuousLinearMap.hasFDerivAt).comp z hfd
  have hgrad : gradient F = (InnerProductSpace.toDual ℝ (Euc d)).symm.toContinuousLinearMap ∘
      (fderiv ℝ F) := rfl
  have hg : fderiv ℝ (gradient F) z = ((InnerProductSpace.toDual ℝ (Euc d)).symm.toContinuousLinearMap).comp
      (fderiv ℝ (fderiv ℝ F) z) := by
    rw [hgrad, he'.fderiv]
  rw [hg]
  have hn : ‖(InnerProductSpace.toDual ℝ (Euc d)).symm.toContinuousLinearMap‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => by simp)
  calc ‖((InnerProductSpace.toDual ℝ (Euc d)).symm.toContinuousLinearMap).comp
        (fderiv ℝ (fderiv ℝ F) z)‖
      ≤ ‖(InnerProductSpace.toDual ℝ (Euc d)).symm.toContinuousLinearMap‖ *
          ‖fderiv ℝ (fderiv ℝ F) z‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖fderiv ℝ (fderiv ℝ F) z‖ :=
          mul_le_mul_of_nonneg_right hn (norm_nonneg (fderiv ℝ (fderiv ℝ F) z))
    _ = ‖fderiv ℝ (fderiv ℝ F) z‖ := one_mul _

theorem euc_decomp {d : ℕ} (v : Euc d) :
    v = ∑ j : Fin d, v j • (EuclideanSpace.single j 1 : Euc d) := by
  ext i
  simp [Finset.sum_apply, Pi.single_apply]

theorem abs_coord_le_norm {d : ℕ} (v : Euc d) (j : Fin d) : |v j| ≤ ‖v‖ := by
  have := PiLp.norm_apply_le v j
  rwa [Real.norm_eq_abs] at this

theorem norm_clm1_le_sum {d : ℕ} (L : Euc d →L[ℝ] ℝ) :
    ‖L‖ ≤ ∑ j : Fin d, |L (EuclideanSpace.single j 1)| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun j _ => abs_nonneg _) fun v => ?_
  have hLv : L v = ∑ j : Fin d, v j * L (EuclideanSpace.single j 1) := by
    conv_lhs => rw [euc_decomp v]
    simp [map_sum, map_smul, smul_eq_mul]
  rw [Real.norm_eq_abs, hLv]
  calc |∑ j : Fin d, v j * L (EuclideanSpace.single j 1)|
      ≤ ∑ j : Fin d, |v j * L (EuclideanSpace.single j 1)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j : Fin d, |v j| * |L (EuclideanSpace.single j 1)| :=
        Finset.sum_congr rfl fun j _ => abs_mul _ _
    _ ≤ ∑ j : Fin d, ‖v‖ * |L (EuclideanSpace.single j 1)| :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (abs_coord_le_norm v j) (abs_nonneg _)
    _ = ‖v‖ * ∑ j : Fin d, |L (EuclideanSpace.single j 1)| := by rw [Finset.mul_sum]
    _ = (∑ j : Fin d, |L (EuclideanSpace.single j 1)|) * ‖v‖ := mul_comm _ _

theorem norm_clm2_le_sum {d : ℕ} (B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) :
    ‖B‖ ≤ ∑ j : Fin d, ∑ k : Fin d, |B (EuclideanSpace.single j 1) (EuclideanSpace.single k 1)| := by
  have hS0 : 0 ≤ ∑ j : Fin d, ∑ k : Fin d,
      |B (EuclideanSpace.single j 1) (EuclideanSpace.single k 1)| :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => abs_nonneg _
  refine ContinuousLinearMap.opNorm_le_bound _ hS0 fun v => ?_
  refine (norm_clm1_le_sum (B v)).trans ?_
  have hterm : ∀ k : Fin d, |B v (EuclideanSpace.single k 1)| ≤
      ‖v‖ * ∑ j : Fin d, |B (EuclideanSpace.single j 1) (EuclideanSpace.single k 1)| := by
    intro k
    have hBv : B v (EuclideanSpace.single k 1)
        = ∑ j : Fin d, v j * B (EuclideanSpace.single j 1) (EuclideanSpace.single k 1) := by
      conv_lhs => rw [euc_decomp v]
      simp [map_sum, map_smul, smul_eq_mul]
    rw [hBv, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (abs_coord_le_norm v j) (abs_nonneg _)
  calc ∑ k : Fin d, |B v (EuclideanSpace.single k 1)|
      ≤ ∑ k : Fin d, ‖v‖ * ∑ j : Fin d, |B (EuclideanSpace.single j 1) (EuclideanSpace.single k 1)| :=
        Finset.sum_le_sum fun k _ => hterm k
    _ = ‖v‖ * ∑ k : Fin d, ∑ j : Fin d, |B (EuclideanSpace.single j 1) (EuclideanSpace.single k 1)| := by
        rw [← Finset.mul_sum]
    _ = ‖v‖ * ∑ j : Fin d, ∑ k : Fin d, |B (EuclideanSpace.single j 1) (EuclideanSpace.single k 1)| := by
        rw [Finset.sum_comm]
    _ = (∑ j : Fin d, ∑ k : Fin d, |B (EuclideanSpace.single j 1) (EuclideanSpace.single k 1)|) * ‖v‖ :=
        mul_comm _ _

/-- Uniform bounds on the first and second covering derivatives of `lift (f r)` for `r ∈ [0,t]`
on a ball (through the real-valued basis evaluations, which are continuous). -/
theorem exists_bound_deriv_ball {t : ℝ} {f ft : ℝ → Torus d → ℝ} (hf : IsC12Test t f ft) (R : ℝ) :
    ∃ C1 C2 : ℝ, ∀ r ∈ Set.Icc 0 t, ∀ y ∈ Metric.closedBall (0 : Euc d) R,
      ‖fderiv ℝ (Torus.lift (f r)) y‖ ≤ C1 ∧
        ‖fderiv ℝ (fderiv ℝ (Torus.lift (f r))) y‖ ≤ C2 := by
  have h1 : ContinuousOn (fun p : ℝ × Euc d => fderiv ℝ (Torus.lift (f p.1)) p.2)
      (Set.Icc 0 t ×ˢ Set.univ) := by
    have h := (continuousMultilinearCurryFin1 ℝ (Euc d) ℝ).continuous.comp_continuousOn
      (hf.contOn_iter (j := 1) (by norm_num))
    exact h.congr fun p _ => by simp [fderiv_eq_curry]
  have h2 : ContinuousOn (fun p : ℝ × Euc d => fderiv ℝ (fderiv ℝ (Torus.lift (f p.1))) p.2)
      (Set.Icc 0 t ×ˢ Set.univ) := by
    have h := (continuous_curry2 d).comp_continuousOn (hf.contOn_iter (j := 2) (by norm_num))
    exact h.congr fun p _ => by simp [fderiv_fderiv_eq_curry2]
  have hK : IsCompact (Set.Icc (0:ℝ) t ×ˢ Metric.closedBall (0 : Euc d) R) :=
    isCompact_Icc.prod (isCompact_closedBall (0 : Euc d) R)
  have hG1 : ContinuousOn (fun p : ℝ × Euc d =>
      ∑ j : Fin d, |fderiv ℝ (Torus.lift (f p.1)) p.2 (EuclideanSpace.single j 1)|)
      (Set.Icc 0 t ×ˢ Set.univ) :=
    continuousOn_finset_sum _ fun j _ => (h1.clm_apply continuousOn_const).norm
  have hG2 : ContinuousOn (fun p : ℝ × Euc d =>
      ∑ j : Fin d, ∑ k : Fin d,
        |fderiv ℝ (fderiv ℝ (Torus.lift (f p.1))) p.2 (EuclideanSpace.single j 1)
          (EuclideanSpace.single k 1)|)
      (Set.Icc 0 t ×ˢ Set.univ) :=
    continuousOn_finset_sum _ fun j _ => continuousOn_finset_sum _ fun k _ =>
      ((h2.clm_apply continuousOn_const).clm_apply continuousOn_const).norm
  obtain ⟨C1, hC1⟩ := hK.exists_bound_of_continuousOn
    (hG1.mono (Set.prod_mono subset_rfl (Set.subset_univ _)))
  obtain ⟨C2, hC2⟩ := hK.exists_bound_of_continuousOn
    (hG2.mono (Set.prod_mono subset_rfl (Set.subset_univ _)))
  refine ⟨C1, C2, fun r hr y hy => ⟨?_, ?_⟩⟩
  · refine (norm_clm1_le_sum _).trans ?_
    have h := hC1 (r, y) ⟨hr, hy⟩
    have hn : (0:ℝ) ≤ ∑ j : Fin d, |fderiv ℝ (Torus.lift (f r)) y (EuclideanSpace.single j 1)| :=
      Finset.sum_nonneg fun j _ => abs_nonneg _
    simp only [Real.norm_eq_abs, abs_of_nonneg hn] at h
    exact h
  · refine (norm_clm2_le_sum _).trans ?_
    have h := hC2 (r, y) ⟨hr, hy⟩
    have hn : (0:ℝ) ≤ ∑ j : Fin d, ∑ k : Fin d,
        |fderiv ℝ (fderiv ℝ (Torus.lift (f r))) y (EuclideanSpace.single j 1)
          (EuclideanSpace.single k 1)| :=
      Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => abs_nonneg _
    simp only [Real.norm_eq_abs, abs_of_nonneg hn] at h
    exact h

/-- The gradient of a `C²` function on the torus is Lipschitz for the torus distance, with the
constant given by a bound on its second covering derivative on a ball of radius `√d + d`. -/
theorem grad_lipschitz_ball {f : Torus d → ℝ} (hf : Torus.IsCk 2 f) {C2 : ℝ}
    (hC2 : ∀ z ∈ Metric.closedBall (0 : Euc d) (Real.sqrt d + d),
      ‖fderiv ℝ (fderiv ℝ (Torus.lift f)) z‖ ≤ C2) (x y : Torus d) :
    ‖Torus.grad f x - Torus.grad f y‖ ≤ C2 * Torus.tdist x y := by
  have hF : ContDiff ℝ 2 (Torus.lift f) := hf
  have hg1 : Differentiable ℝ (gradient (Torus.lift f)) := by
    have hc : ContDiff ℝ 1 (gradient (Torus.lift f)) := by
      have e : gradient (Torus.lift f) = fun w =>
          (InnerProductSpace.toDual ℝ (Euc d)).symm.toContinuousLinearMap (fderiv ℝ (Torus.lift f) w) :=
        rfl
      rw [e]
      exact (InnerProductSpace.toDual ℝ (Euc d)).symm.toContinuousLinearMap.contDiff.comp
        (hF.fderiv_right (by norm_num))
    exact hc.differentiable (by norm_num)
  set c : Euc d := Torus.centeredRep (x - y) with hc_def
  have hc_mk : Torus.mk c = x - y := KernelGrad.mk_centeredRep (x - y)
  have hcn : ‖c‖ = Torus.tdist x y := rfl
  have hc_le : ‖c‖ ≤ d := by
    have h := KernelGrad.tdist_le_card (x - y)
    unfold KernelGrad.tdist at h
    rw [sub_zero] at h
    exact h
  set a : Euc d := Torus.rep x with ha_def
  set b : Euc d := a - c with hb_def
  have hmk_b : Torus.mk b = y := by
    rw [hb_def, mk_sub', hc_mk, ha_def, Torus.mk_rep]
    abel
  have ha_mem : a ∈ Metric.closedBall (0 : Euc d) (Real.sqrt d + d) := by
    rw [mem_closedBall_zero_iff]
    have h1 : ‖a‖ ≤ Real.sqrt d := rep_norm_le x
    have h2 : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
    linarith [norm_nonneg c]
  have hb_mem : b ∈ Metric.closedBall (0 : Euc d) (Real.sqrt d + d) := by
    rw [mem_closedBall_zero_iff]
    have h1 : ‖a‖ ≤ Real.sqrt d := rep_norm_le x
    have h2 : ‖b‖ ≤ ‖a‖ + ‖c‖ := by
      rw [hb_def]
      exact norm_sub_le _ _
    linarith
  have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le
    (f := gradient (Torus.lift f)) (C := C2) (s := Metric.closedBall (0 : Euc d) (Real.sqrt d + d))
    (fun w _ => hg1 w) (fun w hw => (norm_fderiv_gradient_le hF w).trans (hC2 w hw))
    (convex_closedBall _ _) ha_mem hb_mem
  have hba : ‖b - a‖ = Torus.tdist x y := by
    have e : b - a = -c := by rw [hb_def]; abel
    rw [e, norm_neg, hcn]
  have ea : Torus.grad f x = gradient (Torus.lift f) a := rfl
  have eb : Torus.grad f y = gradient (Torus.lift f) b := by
    rw [← hmk_b]
    exact grad_mk f b
  rw [ea, eb, norm_sub_rev]
  calc ‖gradient (Torus.lift f) b - gradient (Torus.lift f) a‖
      ≤ C2 * ‖b - a‖ := hmv
    _ = C2 * Torus.tdist x y := by rw [hba]

theorem norm_gradient_eq (F : Euc d → ℝ) (y : Euc d) :
    ‖gradient F y‖ = ‖fderiv ℝ F y‖ :=
  (InnerProductSpace.toDual ℝ (Euc d)).symm.norm_map _

theorem abs_avg_le {N : ℕ} (hN : 0 < N) (k : Fin N → Fin N → ℝ) {B : ℝ}
    (hB : ∀ i j, |k i j| ≤ B) :
    |(N : ℝ)⁻¹ * ∑ i, (N : ℝ)⁻¹ * ∑ j, k i j| ≤ B := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : ∀ i, |(N : ℝ)⁻¹ * ∑ j, k i j| ≤ (N : ℝ)⁻¹ * (N * B) := fun i => by
    rw [abs_mul, abs_of_pos (inv_pos.2 hN')]
    refine mul_le_mul_of_nonneg_left ?_ (inv_pos.2 hN').le
    calc |∑ j, k i j| ≤ ∑ j, |k i j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin N, B := Finset.sum_le_sum fun j _ => hB i j
      _ = N * B := by simp
  have h2 : |∑ i, (N : ℝ)⁻¹ * ∑ j, k i j| ≤ N * ((N : ℝ)⁻¹ * (N * B)) := by
    calc |∑ i, (N : ℝ)⁻¹ * ∑ j, k i j| ≤ ∑ i, |(N : ℝ)⁻¹ * ∑ j, k i j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin N, (N : ℝ)⁻¹ * (N * B) := Finset.sum_le_sum fun i _ => h1 i
      _ = N * ((N : ℝ)⁻¹ * (N * B)) := by simp
  rw [abs_mul, abs_of_pos (inv_pos.2 hN')]
  calc (N : ℝ)⁻¹ * |∑ i, (N : ℝ)⁻¹ * ∑ j, k i j| ≤ (N : ℝ)⁻¹ * (N * ((N : ℝ)⁻¹ * (N * B))) :=
        mul_le_mul_of_nonneg_left h2 (inv_pos.2 hN').le
    _ = B := by field_simp

/-- The `d = 1`, `s = 0` kernel is bounded by the Lipschitz constant of the gradient times a
constant depending only on `D` (the force `∇g` has the singularity `|z|^{-1}`, and the factor
`tdist` cancels it). -/
theorem kernel_bound_d1 (D : DynData 1) (hs : D.s = 0) :
    ∃ K0 : ℝ, 0 ≤ K0 ∧ ∀ (L : ℝ) (ψ : Torus 1 → ℝ), 0 ≤ L →
      (∀ x y : Torus 1, ‖Torus.grad ψ x - Torus.grad ψ y‖ ≤ L * Torus.tdist x y) →
      ∀ x y : Torus 1, |interKernel D ψ x y| ≤ L * K0 := by
  obtain ⟨Kd, hKd0, hKd⟩ := matVec_bound D.M
  obtain ⟨Cg, hCg⟩ := periodicRieszGrad_bound_d1 (s := D.s) D.hs0 (by simpa using D.hsd)
  have hM0 : 0 ≤ max Cg 0 := le_max_right _ _
  refine ⟨Kd * max Cg 0 * 2, by positivity, fun L ψ hL0 hL x y => ?_⟩
  unfold interKernel
  split_ifs with hxy
  · simp only [abs_zero]
    have : 0 ≤ L * (Kd * max Cg 0 * 2) := by positivity
    exact this
  · set c : Euc 1 := Torus.centeredRep (x - y) with hc_def
    have hc_mk : Torus.mk c = x - y := KernelGrad.mk_centeredRep (x - y)
    have hz : x - y ≠ 0 := sub_ne_zero.2 hxy
    have hc_ne : c ≠ 0 := by
      intro h
      apply hz
      rw [← hc_mk, h]
      rfl
    have ht : 0 < Torus.tdist x y := norm_pos_iff.2 hc_ne
    have ht1 : Torus.tdist x y ≤ 1 := by
      have h := KernelGrad.tdist_le_card (x - y)
      unfold KernelGrad.tdist at h
      rw [sub_zero] at h
      exact_mod_cast h
    have hcoord : ∀ i, |c i| ≤ 1 / 2 := by
      intro i
      have h := Torus.abs_centeredRep_apply (x - y) i
      have h2 : ‖(x - y) i‖ ≤ 1 / 2 := by
        have := AddCircle.norm_le_half_period (p := (1 : ℝ)) (x := (x - y) i) one_ne_zero
        rw [abs_one] at this
        exact this
      calc |c i| = ‖(x - y) i‖ := h
        _ ≤ 1 / 2 := h2
    have hg := hCg c hc_ne hcoord
    have hpow : ‖c‖ ^ (-D.s - 1) = ‖c‖⁻¹ := by
      rw [hs, show (-(0:ℝ) - 1) = -1 by norm_num, Real.rpow_neg_one]
    rw [hc_mk, hpow] at hg
    have hg' : ‖periodicRieszGrad 1 D.s (x - y)‖ ≤ max Cg 0 * ((Torus.tdist x y)⁻¹ + 1) := by
      have h1 : Cg * ((Torus.tdist x y)⁻¹ + 1) ≤ max Cg 0 * ((Torus.tdist x y)⁻¹ + 1) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      exact hg.trans h1
    have hw : ‖Torus.matVec D.M (periodicRieszGrad 1 D.s (x - y))‖
        ≤ Kd * (max Cg 0 * ((Torus.tdist x y)⁻¹ + 1)) := by
      exact (hKd _).trans (mul_le_mul_of_nonneg_left hg' hKd0)
    have hu : ‖Torus.grad ψ x - Torus.grad ψ y‖ ≤ L * Torus.tdist x y := hL x y
    have hLt : 0 ≤ L * Torus.tdist x y := mul_nonneg hL0 ht.le
    have hprod := mul_le_mul hu hw (norm_nonneg _) hLt
    have hkey : L * Torus.tdist x y * (Kd * (max Cg 0 * ((Torus.tdist x y)⁻¹ + 1)))
        = L * (Kd * max Cg 0) * (1 + Torus.tdist x y) := by
      field_simp
    have hfin : L * (Kd * max Cg 0) * (1 + Torus.tdist x y) ≤ L * (Kd * max Cg 0 * 2) := by
      have hpos : 0 ≤ L * (Kd * max Cg 0) := by positivity
      nlinarith
    calc |inner ℝ (Torus.grad ψ x - Torus.grad ψ y) (Torus.matVec D.M (periodicRieszGrad 1 D.s (x - y)))|
        ≤ ‖Torus.grad ψ x - Torus.grad ψ y‖ *
            ‖Torus.matVec D.M (periodicRieszGrad 1 D.s (x - y))‖ := abs_real_inner_le_norm _ _
      _ ≤ L * Torus.tdist x y * (Kd * (max Cg 0 * ((Torus.tdist x y)⁻¹ + 1))) := hprod
      _ = L * (Kd * max Cg 0) * (1 + Torus.tdist x y) := hkey
      _ ≤ L * (Kd * max Cg 0 * 2) := hfin

/-- The test-function part `ft + β⁻¹Δf - ∇V·∇f` of the empirical identity is bounded, uniformly in
`r ∈ [0,t]` and in the configuration. -/
theorem lpsi_bound {d : ℕ} {t : ℝ} {f ft : ℝ → Torus d → ℝ} (ht : 0 ≤ t) (hf : IsC12Test t f ft)
    (D : DynData d) (hV : Torus.IsCk 2 D.V) :
    ∃ KL : ℝ, ∀ r ∈ Set.Icc 0 t, ∀ x : Torus d,
      |ft r x + D.invβ * Torus.laplacian (f r) x - inner ℝ (Torus.grad D.V x) (Torus.grad (f r) x)|
        ≤ KL := by
  set R : ℝ := Real.sqrt d + d with hR
  obtain ⟨C1, C2, hC⟩ := exists_bound_deriv_ball hf R
  have hcont3 : ContinuousOn (fun p : ℝ × Euc d => ft p.1 (Torus.mk p.2))
      (Set.Icc 0 t ×ˢ Set.univ) :=
    hf.contOn_timeDeriv
  obtain ⟨C3, hC3⟩ := (isCompact_Icc.prod (isCompact_closedBall (0 : Euc d) R)).exists_bound_of_continuousOn
    (hcont3.mono (Set.prod_mono subset_rfl (Set.subset_univ _)))
  have hVd : ContDiff ℝ 2 (Torus.lift D.V) := hV
  have hVc : Continuous (gradient (Torus.lift D.V)) := by
    have e : gradient (Torus.lift D.V) = fun w =>
        (InnerProductSpace.toDual ℝ (Euc d)).symm.toContinuousLinearMap (fderiv ℝ (Torus.lift D.V) w) :=
      rfl
    rw [e]
    exact ((InnerProductSpace.toDual ℝ (Euc d)).symm.toContinuousLinearMap.continuous).comp
      (hVd.continuous_fderiv (by norm_num))
  obtain ⟨C4, hC4⟩ := (isCompact_closedBall (0 : Euc d) R).exists_bound_of_continuousOn
    hVc.continuousOn
  refine ⟨max C3 0 + |D.invβ| * (d * max C2 0) + max C4 0 * max C1 0, fun r hr x => ?_⟩
  have hball : Torus.rep x ∈ Metric.closedBall (0 : Euc d) R := by
    rw [mem_closedBall_zero_iff]
    have h1 := rep_norm_le x
    have h2 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  -- the time-derivative term
  have h1 : |ft r x| ≤ max C3 0 := by
    have e : ft r x = ft r (Torus.mk (Torus.rep x)) := by rw [Torus.mk_rep]
    have h := hC3 (r, Torus.rep x) ⟨hr, hball⟩
    simp only [Real.norm_eq_abs] at h
    rw [e]
    exact h.trans (le_max_left _ _)
  -- the Laplacian term
  have hlap : |Torus.laplacian (f r) x| ≤ d * max C2 0 := by
    show |Laplacian.laplacian (Torus.lift (f r)) (Torus.rep x)| ≤ _
    rw [laplacian_eq_sum_fderiv]
    have hD := (hC r hr (Torus.rep x) hball).2
    calc |∑ j, (fderiv ℝ (fderiv ℝ (Torus.lift (f r))) (Torus.rep x))
            (EuclideanSpace.single j 1) (EuclideanSpace.single j 1)|
        ≤ ∑ j : Fin d, |(fderiv ℝ (fderiv ℝ (Torus.lift (f r))) (Torus.rep x))
            (EuclideanSpace.single j 1) (EuclideanSpace.single j 1)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin d, max C2 0 := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [← Real.norm_eq_abs]
          calc ‖(fderiv ℝ (fderiv ℝ (Torus.lift (f r))) (Torus.rep x))
                (EuclideanSpace.single j 1) (EuclideanSpace.single j 1)‖
              ≤ ‖fderiv ℝ (fderiv ℝ (Torus.lift (f r))) (Torus.rep x)‖ *
                  ‖(EuclideanSpace.single j 1 : Euc d)‖ * ‖(EuclideanSpace.single j 1 : Euc d)‖ :=
                ContinuousLinearMap.le_opNorm₂ _ _ _
            _ = ‖fderiv ℝ (fderiv ℝ (Torus.lift (f r))) (Torus.rep x)‖ := by
                rw [EuclideanSpace.norm_single, norm_one]; ring
            _ ≤ max C2 0 := hD.trans (le_max_left _ _)
      _ = d * max C2 0 := by simp
  have h2 : |D.invβ * Torus.laplacian (f r) x| ≤ |D.invβ| * (d * max C2 0) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hlap (abs_nonneg _)
  -- the drift term
  have h3 : |inner ℝ (Torus.grad D.V x) (Torus.grad (f r) x)| ≤ max C4 0 * max C1 0 := by
    have hu : ‖Torus.grad D.V x‖ ≤ max C4 0 := (hC4 (Torus.rep x) hball).trans (le_max_left _ _)
    have hv : ‖Torus.grad (f r) x‖ ≤ max C1 0 := by
      have e : Torus.grad (f r) x = gradient (Torus.lift (f r)) (Torus.rep x) := rfl
      rw [e, norm_gradient_eq]
      exact (hC r hr (Torus.rep x) hball).1.trans (le_max_left _ _)
    refine (abs_real_inner_le_norm _ _).trans ?_
    exact mul_le_mul hu hv (norm_nonneg _) ((norm_nonneg _).trans hu)
  have hsum1 := abs_add_le (ft r x) (D.invβ * Torus.laplacian (f r) x)
  have hsum2 := abs_sub (ft r x + D.invβ * Torus.laplacian (f r) x)
    (inner ℝ (Torus.grad D.V x) (Torus.grad (f r) x))
  have hnn : 0 ≤ max C4 0 * max C1 0 := mul_nonneg (le_max_right _ _) (le_max_right _ _)
  linarith

/-! ### The empirical integrand: measurability and bounds -/

theorem interKernel_eq_inner {d : ℕ} (D : DynData d) (ψ : Torus d → ℝ) (x y : Torus d) :
    interKernel D ψ x y = inner ℝ (Torus.grad ψ x - Torus.grad ψ y)
      (Torus.matVec D.M (periodicRieszGrad d D.s (x - y))) := by
  unfold interKernel
  split_ifs with h
  · subst h
    simp
  · rfl

theorem abs_single_avg_le {N : ℕ} (hN : 0 < N) (k : Fin N → ℝ) {B : ℝ} (hB : ∀ i, |k i| ≤ B) :
    |(N : ℝ)⁻¹ * ∑ i, k i| ≤ B := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [abs_mul, abs_of_pos (inv_pos.2 hN')]
  have h : |∑ i, k i| ≤ N * B := by
    calc |∑ i, k i| ≤ ∑ i, |k i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin N, B := Finset.sum_le_sum fun i _ => hB i
      _ = N * B := by simp
  calc (N : ℝ)⁻¹ * |∑ i, k i| ≤ (N : ℝ)⁻¹ * (N * B) :=
        mul_le_mul_of_nonneg_left h (inv_pos.2 hN').le
    _ = B := by field_simp

theorem continuous_lap_clamp {d : ℕ} {t : ℝ} (ht : 0 ≤ t) {f ft : ℝ → Torus d → ℝ}
    (hf : IsC12Test t f ft) :
    Continuous (fun p : ℝ × Euc d => Laplacian.laplacian (Torus.lift (f (clampTI t p.1))) p.2) := by
  have hq : Continuous (fun q : ℝ × Euc d => (clampTI t q.1, q.2)) :=
    ((continuous_clampTI t).comp continuous_fst).prodMk continuous_snd
  have hmem : ∀ q : ℝ × Euc d, (clampTI t q.1, q.2) ∈ Set.Icc 0 t ×ˢ (Set.univ : Set (Euc d)) :=
    fun q => ⟨clampTI_mem ht q.1, Set.mem_univ _⟩
  have h2on : ContinuousOn (fun p : ℝ × Euc d => fderiv ℝ (fderiv ℝ (Torus.lift (f p.1))) p.2)
      (Set.Icc 0 t ×ˢ Set.univ) := by
    have h := (continuous_curry2 d).comp_continuousOn (hf.contOn_iter (j := 2) (by norm_num))
    exact h.congr fun p _ => by simp [fderiv_fderiv_eq_curry2]
  have h2 : Continuous (fun q : ℝ × Euc d =>
      fderiv ℝ (fderiv ℝ (Torus.lift (f (clampTI t q.1)))) q.2) :=
    ContinuousOn.comp_continuous h2on hq hmem
  have hsum : Continuous (fun p : ℝ × Euc d => ∑ j : Fin d,
      (fderiv ℝ (fderiv ℝ (Torus.lift (f (clampTI t p.1)))) p.2)
        (EuclideanSpace.single j 1) (EuclideanSpace.single j 1)) :=
    continuous_finsetSum _ fun j _ => (h2.clm_apply continuous_const).clm_apply continuous_const
  refine hsum.congr fun p => ?_
  exact (laplacian_eq_sum_fderiv p.2).symm

theorem measurable_lpsi_clamp {d : ℕ} {t : ℝ} (ht : 0 ≤ t) {f ft : ℝ → Torus d → ℝ}
    (hf : IsC12Test t f ft) (D : DynData d) (hV : Torus.IsCk 2 D.V) :
    Measurable (fun p : ℝ × Torus d => ft (clampTI t p.1) p.2
      + D.invβ * Torus.laplacian (f (clampTI t p.1)) p.2
      - inner ℝ (Torus.grad D.V p.2) (Torus.grad (f (clampTI t p.1)) p.2)) := by
  have hq : Continuous (fun q : ℝ × Euc d => (clampTI t q.1, q.2)) :=
    ((continuous_clampTI t).comp continuous_fst).prodMk continuous_snd
  have hmem : ∀ q : ℝ × Euc d, (clampTI t q.1, q.2) ∈ Set.Icc 0 t ×ˢ (Set.univ : Set (Euc d)) :=
    fun q => ⟨clampTI_mem ht q.1, Set.mem_univ _⟩
  have hft : Continuous (fun q : ℝ × Euc d => ft (clampTI t q.1) (Torus.mk q.2)) :=
    ContinuousOn.comp_continuous hf.contOn_timeDeriv hq hmem
  have hft' : Measurable (fun p : ℝ × Torus d => ft (clampTI t p.1) p.2) := by
    have h := hft.measurable.comp (measurable_fst.prodMk ((measurable_torusRep d).comp measurable_snd))
    simpa [Function.comp_def, Torus.mk_rep] using h
  have hlap : Measurable (fun p : ℝ × Torus d => Torus.laplacian (f (clampTI t p.1)) p.2) := by
    have hL : Measurable (fun q : ℝ × Euc d => Laplacian.laplacian (Torus.lift (f (clampTI t q.1))) q.2) :=
      (continuous_lap_clamp ht hf).measurable
    have hR : Measurable (fun p : ℝ × Torus d => ((p.1, Torus.rep p.2) : ℝ × Euc d)) :=
      measurable_fst.prodMk ((measurable_torusRep d).comp measurable_snd)
    have h := hL.comp hR
    exact h
  have hgf : Measurable (fun p : ℝ × Torus d => Torus.grad (f (clampTI t p.1)) p.2) :=
    measurable_grad_clamp ht hf
  have hgV : Measurable (fun p : ℝ × Torus d => Torus.grad D.V p.2) :=
    (measurable_torusGrad hV).comp measurable_snd
  have hsum1 : Measurable (fun p : ℝ × Torus d => ft (clampTI t p.1) p.2
      + D.invβ * Torus.laplacian (f (clampTI t p.1)) p.2) :=
    Measurable.add hft' (Measurable.const_mul hlap D.invβ)
  exact Measurable.sub hsum1 (Measurable.inner hgV hgf)

theorem measurable_interKernel_clamp {d : ℕ} {t : ℝ} (ht : 0 ≤ t) {f ft : ℝ → Torus d → ℝ}
    (hf : IsC12Test t f ft) (D : DynData d) (hsd : D.s < d) :
    Measurable (fun q : ℝ × (Torus d × Torus d) => interKernel D (f (clampTI t q.1)) q.2.1 q.2.2) := by
  have hgr1 : Measurable (fun q : ℝ × (Torus d × Torus d) => Torus.grad (f (clampTI t q.1)) q.2.1) :=
    (measurable_grad_clamp ht hf).comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hgr2 : Measurable (fun q : ℝ × (Torus d × Torus d) => Torus.grad (f (clampTI t q.1)) q.2.2) :=
    (measurable_grad_clamp ht hf).comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have hsub : Measurable (fun q : ℝ × (Torus d × Torus d) => q.2.1 - q.2.2) :=
    (continuous_sub).measurable.comp (measurable_snd)
  have hk : Measurable (fun q : ℝ × (Torus d × Torus d) => periodicRieszGrad d D.s (q.2.1 - q.2.2)) :=
    (KernelGrad.measurable_periodicRieszGrad hsd).comp hsub
  have hm : Measurable (fun q : ℝ × (Torus d × Torus d) => Torus.matVec D.M (periodicRieszGrad d D.s (q.2.1 - q.2.2))) :=
    (LinearMap.continuous_of_finiteDimensional (Matrix.toEuclideanLin D.M)).measurable.comp hk
  have e : (fun q : ℝ × (Torus d × Torus d) => interKernel D (f (clampTI t q.1)) q.2.1 q.2.2)
      = fun q => inner ℝ (Torus.grad (f (clampTI t q.1)) q.2.1 - Torus.grad (f (clampTI t q.1)) q.2.2)
          (Torus.matVec D.M (periodicRieszGrad d D.s (q.2.1 - q.2.2))) := by
    funext q
    exact interKernel_eq_inner D _ _ _
  rw [e]
  exact (hgr1.sub hgr2).inner hm

/-- The empirical integrand of Lemma 3.6 at the clamped time, written with the empirical sums. -/
def cepaG {d N : ℕ} (D : DynData d) (ft f : ℝ → Torus d → ℝ) (r : ℝ) (x : Config d N) : ℝ :=
  pair (empirical x) (fun y => ft r y + D.invβ * Torus.laplacian (f r) y
      - inner ℝ (Torus.grad D.V y) (Torus.grad (f r) y))
    + interactionPairing D (f r) (empirical x) (empirical x)

theorem cepaG_eq {d N : ℕ} (hN : 0 < N) (D : DynData d) (ft f : ℝ → Torus d → ℝ) (r : ℝ)
    (x : Config d N) :
    cepaG D ft f r x = (N : ℝ)⁻¹ * ∑ i, (ft r (x i) + D.invβ * Torus.laplacian (f r) (x i)
        - inner ℝ (Torus.grad D.V (x i)) (Torus.grad (f r) (x i)))
      + (1 / 2 : ℝ) * ((N : ℝ)⁻¹ * ∑ i, (N : ℝ)⁻¹ * ∑ j, interKernel D (f r) (x i) (x j)) := by
  unfold cepaG
  rw [pair_empirical hN, interactionPairing_empirical hN]

theorem measurable_cepaG {t : ℝ} (ht : 0 ≤ t) {f ft : ℝ → Torus 1 → ℝ} (hf : IsC12Test t f ft)
    (D : DynData 1) (hV : Torus.IsCk 2 D.V) (hsd : D.s < ((1 : ℕ) : ℝ)) {N : ℕ} (hN : 0 < N) :
    Measurable (fun p : ℝ × Config 1 N => cepaG D ft f (clampTI t p.1) p.2) := by
  have hphi := measurable_lpsi_clamp ht hf D hV
  have hK := measurable_interKernel_clamp ht hf D hsd
  have e : (fun p : ℝ × Config 1 N => cepaG D ft f (clampTI t p.1) p.2)
      = fun p => (N : ℝ)⁻¹ * ∑ i, (ft (clampTI t p.1) (p.2 i)
          + D.invβ * Torus.laplacian (f (clampTI t p.1)) (p.2 i)
          - inner ℝ (Torus.grad D.V (p.2 i)) (Torus.grad (f (clampTI t p.1)) (p.2 i)))
        + (1 / 2 : ℝ) * ((N : ℝ)⁻¹ * ∑ i, (N : ℝ)⁻¹ * ∑ j,
            interKernel D (f (clampTI t p.1)) (p.2 i) (p.2 j)) := by
    funext p
    exact cepaG_eq hN D ft f (clampTI t p.1) p.2
  rw [e]
  refine Measurable.add (measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_))
    (measurable_const.mul (measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_)))
  · exact hphi.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  · refine measurable_const.mul (Finset.measurable_sum _ fun j _ => ?_)
    have hij : Measurable (fun p : ℝ × Config 1 N => (p.2 i, p.2 j)) :=
      ((measurable_pi_apply i).comp measurable_snd).prodMk ((measurable_pi_apply j).comp measurable_snd)
    have hpair : Measurable (fun p : ℝ × Config 1 N => (p.1, (p.2 i, p.2 j))) :=
      measurable_fst.prodMk hij
    exact hK.comp hpair

theorem abs_cepaG_le {d N : ℕ} {t : ℝ} (ht : 0 ≤ t) {f ft : ℝ → Torus d → ℝ}
    (D : DynData d) (hN : 0 < N) {KL L K0 : ℝ} (hL : 0 ≤ L) (hK0 : 0 ≤ K0)
    (hKL : ∀ r ∈ Set.Icc 0 t, ∀ x : Torus d,
      |ft r x + D.invβ * Torus.laplacian (f r) x - inner ℝ (Torus.grad D.V x) (Torus.grad (f r) x)| ≤ KL)
    (hkern : ∀ r ∈ Set.Icc 0 t, ∀ x y : Torus d, |interKernel D (f r) x y| ≤ L * K0)
    (s : ℝ) (x : Config d N) :
    |cepaG D ft f (clampTI t s) x| ≤ KL + L * K0 := by
  rw [cepaG_eq hN]
  have ha := abs_single_avg_le hN (fun i => ft (clampTI t s) (x i)
      + D.invβ * Torus.laplacian (f (clampTI t s)) (x i)
      - inner ℝ (Torus.grad D.V (x i)) (Torus.grad (f (clampTI t s)) (x i)))
    (B := KL) (fun i => hKL _ (clampTI_mem ht s) (x i))
  have hb := abs_avg_le hN (fun i j => interKernel D (f (clampTI t s)) (x i) (x j))
    (B := L * K0) (fun i j => hkern _ (clampTI_mem ht s) _ _)
  have hLK : 0 ≤ L * K0 := mul_nonneg hL hK0
  have h2 : |(1 / 2 : ℝ) * ((N : ℝ)⁻¹ * ∑ i, (N : ℝ)⁻¹ * ∑ j,
      interKernel D (f (clampTI t s)) (x i) (x j))| ≤ L * K0 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith [hb]
  have h1 : |(N : ℝ)⁻¹ * ∑ i, (ft (clampTI t s) (x i) + D.invβ * Torus.laplacian (f (clampTI t s)) (x i)
      - inner ℝ (Torus.grad D.V (x i)) (Torus.grad (f (clampTI t s)) (x i)))| ≤ KL := ha
  exact (abs_add_le _ _).trans (by linarith [h1, h2])


/-! ### The expectation identity `cepa_empirical_fke` (Lemma 3.6 in expectation) -/

theorem measurable_pair_empirical {d N : ℕ} (hN : 0 < N) {g : Torus d → ℝ} (hg : Measurable g) :
    Measurable (fun x : Config d N => pair (empirical x) g) := by
  have e : (fun x : Config d N => pair (empirical x) g) = fun x => (N : ℝ)⁻¹ * ∑ i, g (x i) := by
    funext x
    rw [pair_empirical hN]
  rw [e]
  exact measurable_const.mul (Finset.measurable_sum _ fun i _ => hg.comp (measurable_pi_apply i))

theorem abs_pair_empirical_le {d N : ℕ} (hN : 0 < N) {g : Torus d → ℝ} {B : ℝ}
    (hB : ∀ y, |g y| ≤ B) (x : Config d N) : |pair (empirical x) g| ≤ B := by
  rw [pair_empirical hN]
  exact abs_single_avg_le hN (fun i => g (x i)) (fun i => hB _)

theorem measurable_torus_of_lift {d : ℕ} {φ : Torus d → ℝ} (hφ : Torus.IsCk 2 φ) :
    Measurable φ := by
  have hc : Continuous (Torus.lift φ) := (show ContDiff ℝ 2 (Torus.lift φ) from hφ).continuous
  have e : φ = fun y => Torus.lift φ (Torus.rep y) := by
    funext y
    show φ y = φ (Torus.mk (Torus.rep y))
    rw [Torus.mk_rep]
  rw [e]
  exact hc.measurable.comp (measurable_torusRep d)

theorem abs_torus_le_of_lift {d : ℕ} {φ : Torus d → ℝ} (hφ : Torus.IsCk 2 φ) :
    ∃ B : ℝ, ∀ y, |φ y| ≤ B := by
  have hc : Continuous (Torus.lift φ) := (show ContDiff ℝ 2 (Torus.lift φ) from hφ).continuous
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : Euc d) (Real.sqrt d)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max B 0, fun y => ?_⟩
  have hmem : Torus.rep y ∈ Metric.closedBall (0 : Euc d) (Real.sqrt d) := by
    rw [mem_closedBall_zero_iff]
    exact rep_norm_le y
  have h := hB (Torus.rep y) hmem
  have e : φ y = Torus.lift φ (Torus.rep y) := by
    show φ y = φ (Torus.mk (Torus.rep y))
    rw [Torus.mk_rep]
  rw [e]
  rw [Real.norm_eq_abs] at h
  exact h.trans (le_max_left _ _)

theorem cepa_empirical_fke
    {N : ℕ} (hN : 2 ≤ N) [NeZero N] {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ}
    {D : DynData 1} (hs : D.s = 0) (hβ : 0 < D.invβ) {a : ℝ} (ha : 0 < a)
    (hM : D.M = -(a • (1 : Matrix (Fin 1) (Fin 1) ℝ))) (hV : Torus.IsCk 2 D.V)
    {T : ℝ} {X₀ : Ω → Config 1 N} {W : ℝ≥0 → Ω → (Fin N → Euc 1)} {X : ℝ≥0 → Ω → Config 1 N}
    (hX : IsCepaLepingleFlow P D T X₀ W X) (hF : IsFilteredSolution P ℱ W' W X)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) {f ft : ℝ → Torus 1 → ℝ} (hf : IsC12Test t f ft) :
    ∫ ω, pair (empirical (X (Real.toNNReal t) ω)) (f t) ∂P
      = ∫ ω, pair (empirical (X 0 ω)) (f 0) ∂P
        + ∫ r in (0:ℝ)..t, ∫ ω, (pair (empirical (X (Real.toNNReal r) ω))
            (fun x => ft r x + D.invβ * Torus.laplacian (f r) x
              - inner ℝ (Torus.grad D.V x) (Torus.grad (f r) x))
          + interactionPairing D (f r) (empirical (X (Real.toNNReal r) ω))
              (empirical (X (Real.toNNReal r) ω))) ∂P := by
  have ht0 : 0 ≤ t := ht.1
  have hN0 : 0 < N := by omega
  have hsd : D.s < ((1 : ℕ) : ℝ) := D.hsd
  obtain ⟨hprog, hae⟩ := cepa_empirical_ito hN hs hβ ha hM hV hX hF ht hf
  have hXm : ∀ s : ℝ≥0, Measurable (X s) := hX.toContact.adapted
  -- uniform constants on [0,t]
  obtain ⟨C1, C2, hC⟩ := exists_bound_deriv_ball hf (Real.sqrt ((1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ))
  have hL0 : 0 ≤ max C2 0 := le_max_right _ _
  have hLip : ∀ r ∈ Set.Icc 0 t, ∀ x y : Torus 1,
      ‖Torus.grad (f r) x - Torus.grad (f r) y‖ ≤ max C2 0 * Torus.tdist x y := fun r hr x y =>
    (grad_lipschitz_ball (hf.c2 r hr) (fun z hz => (hC r hr z hz).2) x y).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (by unfold Torus.tdist; exact norm_nonneg _))
  obtain ⟨K0, hK0, hkern0⟩ := kernel_bound_d1 D hs
  have hkern : ∀ r ∈ Set.Icc 0 t, ∀ x y : Torus 1, |interKernel D (f r) x y| ≤ max C2 0 * K0 :=
    fun r hr x y => hkern0 (max C2 0) (f r) hL0 (hLip r hr) x y
  obtain ⟨KL, hKL⟩ := lpsi_bound ht0 hf D hV
  -- joint measurability of the integrand
  have hcg := measurable_cepaG ht0 hf D hV hsd hN0
  have hprogG : IsProgressive ℱ (fun s ω => cepaG D ft f (clampTI t s) (ofNNRealTime X s ω)) :=
    isProgressive_comp_measurable' (ofNNRealTime X) hF.progressive
      (fun s x => cepaG D ft f (clampTI t s) x) hcg
  have hjoint : Measurable (fun p : ℝ × Ω =>
      cepaG D ft f (clampTI t p.1) (ofNNRealTime X p.1 p.2)) :=
    measurable_of_progressive hprogG
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) t)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  have hBnd : ∀ s (x : Config 1 N), |cepaG D ft f (clampTI t s) x| ≤ KL + max C2 0 * K0 :=
    fun s x => abs_cepaG_le ht0 D hN0 hL0 hK0 hKL hkern s x
  have hprodint : Integrable (fun p : ℝ × Ω => cepaG D ft f (clampTI t p.1) (ofNNRealTime X p.1 p.2))
      ((volume.restrict (Set.Ioc (0 : ℝ) t)).prod P) :=
    Integrable.of_bound hjoint.aestronglyMeasurable (KL + max C2 0 * K0)
      (ae_of_all _ fun p => by rw [Real.norm_eq_abs]; exact hBnd _ _)
  -- the martingale term
  have hMlp : MemLp (itoIntegral P ℱ W' (empiricalNoiseIntegrand D t f X) t) 2 P :=
    memLp_two_itoIntegral hF.brownian hprog t
  have hMint : ∫ ω, itoIntegral P ℱ W' (empiricalNoiseIntegrand D t f X) t ω ∂P = 0 :=
    integral_itoIntegral hF.brownian hprog t
  have hMi : Integrable (fun ω => itoIntegral P ℱ W' (empiricalNoiseIntegrand D t f X) t ω) P :=
    hMlp.integrable one_le_two
  have hMeq : ∀ ω, empiricalMartingale P ℱ W' D t f X (Real.toNNReal t) ω
      = itoIntegral P ℱ W' (empiricalNoiseIntegrand D t f X) t ω := by
    intro ω
    unfold empiricalMartingale
    rw [Real.coe_toNNReal t ht0]
  -- the endpoint terms
  obtain ⟨Bt, hBt⟩ := abs_torus_le_of_lift (hf.c2 t ⟨ht0, le_rfl⟩)
  obtain ⟨B0, hB0⟩ := abs_torus_le_of_lift (hf.c2 0 ⟨le_rfl, ht0⟩)
  have hmt : Measurable (f t) := measurable_torus_of_lift (hf.c2 t ⟨ht0, le_rfl⟩)
  have hm0 : Measurable (f 0) := measurable_torus_of_lift (hf.c2 0 ⟨le_rfl, ht0⟩)
  have hPt : Integrable (fun ω => pair (empirical (X (Real.toNNReal t) ω)) (f t)) P :=
    Integrable.of_bound ((measurable_pair_empirical hN0 hmt).comp (hXm _)).aestronglyMeasurable Bt
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact abs_pair_empirical_le hN0 hBt _)
  have hP0 : Integrable (fun ω => pair (empirical (X 0 ω)) (f 0)) P :=
    Integrable.of_bound ((measurable_pair_empirical hN0 hm0).comp (hXm _)).aestronglyMeasurable B0
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact abs_pair_empirical_le hN0 hB0 _)
  -- the a.s. identity of Lemma 3.6 at the time `t`
  have hpt : ∀ᵐ ω ∂P, pair (empirical (X (Real.toNNReal t) ω)) (f t)
      = pair (empirical (X 0 ω)) (f 0)
        + (∫ r in (0:ℝ)..t, cepaG D ft f r (X (Real.toNNReal r) ω))
        + itoIntegral P ℱ W' (empiricalNoiseIntegrand D t f X) t ω := by
    filter_upwards [hae] with ω hω
    obtain ⟨-, heq⟩ := hω t ⟨ht0, le_rfl⟩
    rw [heq, hMeq ω]
    rfl
  -- Fubini on `(0,t] × Ω`
  have hGe : ∀ ω, (∫ r in (0:ℝ)..t, cepaG D ft f r (X (Real.toNNReal r) ω))
      = ∫ r in Set.Ioc (0 : ℝ) t, cepaG D ft f (clampTI t r) (X (Real.toNNReal r) ω) := by
    intro ω
    rw [intervalIntegral.integral_of_le ht0]
    refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
    rw [clampTI_of_mem ⟨hr.1.le, hr.2⟩]
  have hI : Integrable (fun ω => ∫ r in (0:ℝ)..t, cepaG D ft f r (X (Real.toNNReal r) ω)) P := by
    have e : (fun ω => ∫ r in (0:ℝ)..t, cepaG D ft f r (X (Real.toNNReal r) ω))
        = fun ω => ∫ r in Set.Ioc (0 : ℝ) t, cepaG D ft f (clampTI t r) (X (Real.toNNReal r) ω) :=
      funext hGe
    rw [e]
    exact hprodint.integral_prod_right
  have hFub : ∫ ω, (∫ r in (0:ℝ)..t, cepaG D ft f r (X (Real.toNNReal r) ω)) ∂P
      = ∫ r in (0:ℝ)..t, ∫ ω, cepaG D ft f r (X (Real.toNNReal r) ω) ∂P := by
    have hswap := integral_integral_swap (μ := volume.restrict (Set.Ioc (0 : ℝ) t)) (ν := P)
      (f := fun s ω => cepaG D ft f (clampTI t s) (X (Real.toNNReal s) ω)) hprodint
    have h1 : ∫ ω, (∫ r in (0:ℝ)..t, cepaG D ft f r (X (Real.toNNReal r) ω)) ∂P
        = ∫ ω, (∫ r in Set.Ioc (0 : ℝ) t, cepaG D ft f (clampTI t r) (X (Real.toNNReal r) ω)) ∂P :=
      integral_congr_ae (ae_of_all _ hGe)
    rw [h1, ← hswap, intervalIntegral.integral_of_le ht0]
    refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
    rw [clampTI_of_mem ⟨hr.1.le, hr.2⟩]
  -- conclusion
  have hA : Integrable (fun ω => pair (empirical (X 0 ω)) (f 0)
      + ∫ r in (0:ℝ)..t, cepaG D ft f r (X (Real.toNNReal r) ω)) P := hP0.add hI
  have hsplit : ∫ ω, pair (empirical (X (Real.toNNReal t) ω)) (f t) ∂P
      = ∫ ω, (pair (empirical (X 0 ω)) (f 0)
        + (∫ r in (0:ℝ)..t, cepaG D ft f r (X (Real.toNNReal r) ω))
        + itoIntegral P ℱ W' (empiricalNoiseIntegrand D t f X) t ω) ∂P :=
    integral_congr_ae hpt
  rw [hsplit, integral_add hA hMi, integral_add hP0 hI, hMint, add_zero, hFub]
  rfl

end HRS

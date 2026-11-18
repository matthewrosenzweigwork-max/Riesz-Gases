import HRS.MC.CepP3Aux1

/-!
# Packet P3, Aux2: periodization of compactly supported smooth functions on `ℝ × (Fin N → Euc d)`
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MC.CepP3

open HRS

variable {d N : ℕ}

/-- The spatial lattice translation of `ℝ × (Fin N → Euc d)`. -/
def tau (w : Fin N → Lattice d) (p : ℝ × (Fin N → Euc d)) : ℝ × (Fin N → Euc d) := (p.1, p.2 + lat w)

theorem tau_eq (w : Fin N → Lattice d) (p : ℝ × (Fin N → Euc d)) : tau w p = p + (0, lat w) := by
  ext <;> simp [tau]

theorem tau_add (w u : Fin N → Lattice d) (p : ℝ × (Fin N → Euc d)) :
    tau w (tau u p) = tau (u + w) p := by
  simp only [tau, lat_add]
  ext
  · rfl
  · simp [add_assoc, add_comm (lat w)]

theorem continuous_tau (w : Fin N → Lattice d) : Continuous (tau (d := d) w) :=
  continuous_fst.prodMk (continuous_snd.add continuous_const)

theorem contDiff_tau (w : Fin N → Lattice d) {n : WithTop ℕ∞} : ContDiff ℝ n (tau (d := d) w) :=
  contDiff_fst.prodMk (contDiff_snd.add contDiff_const)

/-- Finitely many lattice vectors in a ball. -/
theorem finite_lat_ball (R : ℝ) : {w : Fin N → Lattice d | ‖lat w‖ ≤ R}.Finite := by
  have hsub : {w : Fin N → Lattice d | ‖lat w‖ ≤ R} ⊆
      Set.pi univ (fun _ : Fin N => Set.pi univ (fun _ : Fin d => Icc (-⌈R⌉) ⌈R⌉)) := by
    intro w hw i _ j _
    have h1 : ‖lat w i‖ ≤ R := (norm_le_pi_norm (lat w) i).trans hw
    have h2 : |(w i j : ℝ)| ≤ R := by
      have := PiLp.norm_apply_le (lat w i) j
      simpa [lat, Lattice.toEuc] using this.trans h1
    have h3 : |w i j| ≤ ⌈R⌉ := by
      have : ((|w i j| : ℤ) : ℝ) ≤ (⌈R⌉ : ℝ) := by
        push_cast; exact h2.trans (Int.le_ceil R)
      exact_mod_cast this
    exact abs_le.1 h3
  refine Set.Finite.subset ?_ hsub
  exact Set.Finite.pi fun _ => Set.Finite.pi fun _ => Set.finite_Icc _ _

theorem exists_finset_tau (R : ℝ) (p0 : ℝ × (Fin N → Euc d)) :
    ∃ S : Finset (Fin N → Lattice d), ∀ q, dist q p0 < 1 → ∀ w ∉ S, R < ‖tau w q‖ := by
  refine ⟨(finite_lat_ball (d := d) (N := N) (R + ‖p0‖ + 1)).toFinset, fun q hq w hw => ?_⟩
  have hw' : R + ‖p0‖ + 1 < ‖lat w‖ := by
    by_contra h
    exact hw ((Set.Finite.mem_toFinset _).2 (not_lt.1 h))
  have hq' : ‖q‖ < ‖p0‖ + 1 := by
    have := norm_le_norm_add_norm_sub' q p0
    rw [dist_eq_norm] at hq
    linarith
  have h2 : ‖lat w‖ ≤ ‖q.2 + lat w‖ + ‖q.2‖ := by
    have := norm_le_norm_add_norm_sub' (lat w) (-q.2)
    have e : lat w - -q.2 = q.2 + lat w := by abel
    rw [e, norm_neg] at this
    linarith [norm_add_le q.2 (lat w), this]
  have h3 : ‖q.2 + lat w‖ ≤ ‖tau w q‖ := by
    show ‖q.2 + lat w‖ ≤ ‖(q.1, q.2 + lat w)‖
    exact le_max_right _ _
  have h4 : ‖q.2‖ ≤ ‖q‖ := le_max_right _ _
  linarith

/-- The support condition: `G` vanishes outside the ball of radius `R`. -/
def Supp {M : Type*} [Zero M] (R : ℝ) (G : ℝ × (Fin N → Euc d) → M) : Prop :=
  ∀ q, R < ‖q‖ → G q = 0

/-- The periodization. -/
def per {M : Type*} [AddCommMonoid M] (G : ℝ × (Fin N → Euc d) → M) (p : ℝ × (Fin N → Euc d)) : M :=
  ∑ᶠ w : Fin N → Lattice d, G (tau w p)

theorem per_eq_sum {M : Type*} [AddCommMonoid M] {G : ℝ × (Fin N → Euc d) → M} {R : ℝ}
    (hG : Supp R G) {p : ℝ × (Fin N → Euc d)} {S : Finset (Fin N → Lattice d)}
    (hS : ∀ w ∉ S, R < ‖tau w p‖) : per G p = ∑ w ∈ S, G (tau w p) := by
  unfold per
  refine finsum_eq_sum_of_support_subset _ ?_
  intro w hw
  by_contra hwS
  exact hw (hG _ (hS w hwS))

theorem per_tau {M : Type*} [AddCommMonoid M] (G : ℝ × (Fin N → Euc d) → M) (u : Fin N → Lattice d)
    (p : ℝ × (Fin N → Euc d)) : per G (tau u p) = per G p := by
  unfold per
  calc ∑ᶠ w, G (tau w (tau u p)) = ∑ᶠ w, G (tau (u + w) p) := by simp_rw [tau_add]
    _ = ∑ᶠ w, G (tau w p) := finsum_comp_equiv (Equiv.addLeft u) (f := fun w => G (tau w p))

theorem supp_fderiv {F : ℝ × (Fin N → Euc d) → ℝ} {R : ℝ} (hF : Supp R F) :
    Supp R (fderiv ℝ F) := by
  intro q hq
  have hopen : IsOpen {q : ℝ × (Fin N → Euc d) | R < ‖q‖} := isOpen_lt continuous_const continuous_norm
  have : F =ᶠ[𝓝 q] fun _ => (0 : ℝ) := by
    filter_upwards [hopen.mem_nhds hq] with x hx using hF x hx
  rw [this.fderiv_eq]
  simp

theorem supp_fderiv_clm {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    {F : ℝ × (Fin N → Euc d) → M} {R : ℝ} (hF : Supp R F) : Supp R (fderiv ℝ F) := by
  intro q hq
  have hopen : IsOpen {q : ℝ × (Fin N → Euc d) | R < ‖q‖} := isOpen_lt continuous_const continuous_norm
  have : F =ᶠ[𝓝 q] fun _ => (0 : M) := by
    filter_upwards [hopen.mem_nhds hq] with x hx using hF x hx
  rw [this.fderiv_eq]
  simp

/-- Local finite-sum representation of the periodization. -/
theorem per_eventuallyEq {M : Type*} [AddCommMonoid M] {G : ℝ × (Fin N → Euc d) → M} {R : ℝ}
    (hG : Supp R G) (p : ℝ × (Fin N → Euc d)) :
    ∃ S : Finset (Fin N → Lattice d),
      (∀ q, dist q p < 1 → ∀ w ∉ S, R < ‖tau w q‖) ∧
      per G =ᶠ[𝓝 p] fun q => ∑ w ∈ S, G (tau w q) := by
  obtain ⟨S, hS⟩ := exists_finset_tau R p
  refine ⟨S, hS, ?_⟩
  filter_upwards [Metric.ball_mem_nhds p one_pos] with q hq
  exact per_eq_sum hG (fun w hw => hS q hq w hw)

theorem contDiff_per {F : ℝ × (Fin N → Euc d) → ℝ} {R : ℝ} {n : WithTop ℕ∞}
    (hF : ContDiff ℝ n F) (hS : Supp R F) : ContDiff ℝ n (per F) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  obtain ⟨S, _, hev⟩ := per_eventuallyEq hS p
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  exact (ContDiff.sum fun w _ => hF.comp (contDiff_tau w)).contDiffAt

theorem fderiv_tau_sum {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    {G : ℝ × (Fin N → Euc d) → M} (hG : Differentiable ℝ G) (S : Finset (Fin N → Lattice d))
    (q : ℝ × (Fin N → Euc d)) :
    fderiv ℝ (fun q => ∑ w ∈ S, G (tau w q)) q = ∑ w ∈ S, fderiv ℝ G (tau w q) := by
  have h1 : (fun q => ∑ w ∈ S, G (tau w q)) = ∑ w ∈ S, fun q => G (q + (0, lat w)) := by
    funext q; simp [tau_eq]
  rw [h1, fderiv_sum (A := fun w q => G (q + (0, lat w)))
    (fun w _ => (hG _).comp q ((differentiableAt_id).add_const _))]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [fderiv_comp_add_right, tau_eq]

/-- The first derivative of the periodization is the periodization of the first derivative. -/
theorem fderiv_per_eq_sum {F : ℝ × (Fin N → Euc d) → ℝ} {R : ℝ} (hF : ContDiff ℝ ∞ F)
    (hS : Supp R F) (p : ℝ × (Fin N → Euc d)) {S : Finset (Fin N → Lattice d)}
    (hSp : ∀ q, dist q p < 1 → ∀ w ∉ S, R < ‖tau w q‖) :
    fderiv ℝ (per F) p = ∑ w ∈ S, fderiv ℝ F (tau w p) := by
  have hev : per F =ᶠ[𝓝 p] fun q => ∑ w ∈ S, F (tau w q) := by
    filter_upwards [Metric.ball_mem_nhds p one_pos] with q hq
    exact per_eq_sum hS (fun w hw => hSp q hq w hw)
  rw [hev.fderiv_eq]
  exact fderiv_tau_sum (hF.differentiable (by simp)) S p

theorem fderiv_per_eq {F : ℝ × (Fin N → Euc d) → ℝ} {R : ℝ} (hF : ContDiff ℝ ∞ F)
    (hS : Supp R F) (p : ℝ × (Fin N → Euc d)) :
    fderiv ℝ (per F) p = per (fderiv ℝ F) p := by
  obtain ⟨S, hSp, _⟩ := per_eventuallyEq hS p
  rw [fderiv_per_eq_sum hF hS p hSp, per_eq_sum (supp_fderiv hS) (fun w hw => hSp p (by simp) w hw)]

theorem fderiv2_per_eq_sum {F : ℝ × (Fin N → Euc d) → ℝ} {R : ℝ} (hF : ContDiff ℝ ∞ F)
    (hS : Supp R F) (p : ℝ × (Fin N → Euc d)) {S : Finset (Fin N → Lattice d)}
    (hSp : ∀ q, dist q p < 1 → ∀ w ∉ S, R < ‖tau w q‖) :
    fderiv ℝ (fderiv ℝ (per F)) p = ∑ w ∈ S, fderiv ℝ (fderiv ℝ F) (tau w p) := by
  have hev : fderiv ℝ (per F) =ᶠ[𝓝 p] fun q => ∑ w ∈ S, fderiv ℝ F (tau w q) := by
    filter_upwards [Metric.ball_mem_nhds p one_pos] with q hq
    have hq' : ∀ w ∉ S, R < ‖tau w q‖ := fun w hw => hSp q hq w hw
    rw [fderiv_per_eq hF hS q, per_eq_sum (supp_fderiv hS) hq']
  rw [hev.fderiv_eq]
  exact fderiv_tau_sum ((hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) S p

end HRS.MC.CepP3

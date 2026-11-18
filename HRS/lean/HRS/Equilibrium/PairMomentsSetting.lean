/-
# HRS.Equilibrium.PairMomentsSetting -- the reference setting for Proposition 4.12 (`pair_moments`, EQ-01b)

Extracts, for the thermal density `ρ`, the weak split `g = g_L + q - c` with small row bound, the
calibrated reference `R_N = pinnedLaw V_N (β/N) N ∅`, the domination `P_{N,β} ≤ K R_N`, and the
pointwise pinned-marginal comparison of Lemma 4.10.
-/
import HRS.Equilibrium.PairMomentsBase
import HRS.Equilibrium.PairMomentsLinf

open MeasureTheory ProbabilityTheory Filter Topology Function
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.PairMom

open HRS HRS.External HRS.Quad HRS.External.HeatSplit HRS.External.RefMarg HRS.External.PoleVar

variable {d : ℕ} {s : ℝ}

/-- The split parameters with a prescribed smallness `Λ c ≤ γ₀`. -/
theorem exists_split_params' (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {γ₀ : ℝ} (hγ₀ : 0 < γ₀) :
    ∃ (τ : ℝ) (L : ℕ) (Λ : ℝ) (M : ℕ) (Ψ : Torus d → EuclideanSpace ℝ (Fin M)),
      0 < τ ∧ τ ≤ 1 ∧ 1 ≤ Λ ∧ (∀ y, ρ y ≤ Λ) ∧
      (∀ x y, (weakSplit d s τ L).gL (x - y) = inner ℝ (Ψ x) (Ψ y)) ∧
      Calib.KappaSmall β (Λ * (weakSplit d s τ L).c) ∧ Λ * (weakSplit d s τ L).c ≤ γ₀ := by
  obtain ⟨Λ0, hΛ0, hΛ0b⟩ := PoleCavityAux.exists_density_bound hρ
  set Λ := max Λ0 1 with hΛ
  have hΛpos : 0 < Λ := lt_max_of_lt_right one_pos
  have hΛ1 : 1 ≤ Λ := le_max_right _ _
  have hΛb : ∀ y, ρ y ≤ Λ := fun y => (hΛ0b y).trans (le_max_left _ _)
  set u : ℝ := 1 / (16 * Real.exp 3) with hu
  have hu0 : 0 < u := by positivity
  obtain ⟨τ, hτ, hτ1, L₀, hL₀⟩ := weakSplit_small hd hs0 hsd (ε := min (u / (β * Λ)) (γ₀ / Λ))
    (lt_min (by positivity) (by positivity))
  obtain ⟨M, Ψ, -, hΨ, -⟩ := RefSmall.exists_continuous_features_weakSplit hd hs0 hsd hτ L₀
  refine ⟨τ, L₀, Λ, M, Ψ, hτ, hτ1, hΛ1, hΛb, hΨ, ?_, ?_⟩
  · obtain ⟨-, -, -, -, -, -, -, -, -, hc0, -⟩ := weakSplit_spec hd hs0 hsd hτ hτ1 L₀
    have hc := (hL₀ L₀ le_rfl).trans (min_le_left _ _)
    refine kappaSmall_of_le hβ (mul_nonneg hΛpos.le hc0) ?_
    calc β * (Λ * (weakSplit d s τ L₀).c) ≤ β * (Λ * (u / (β * Λ))) := by gcongr
      _ = u := by field_simp
  · have hc := (hL₀ L₀ le_rfl).trans (min_le_right _ _)
    calc Λ * (weakSplit d s τ L₀).c ≤ Λ * (γ₀ / Λ) := by gcongr
      _ = γ₀ := by field_simp

/-- Finite cosine sums are smooth. -/
theorem isSmooth_cosSum (Λ : Finset (Lattice d)) (a : Lattice d → ℝ) :
    Torus.IsSmooth (fun x : Torus d => ∑ k ∈ Λ, a k * Torus.cosMode k x) := by
  unfold Torus.IsSmooth Torus.IsCk
  have hdot : ∀ k : Lattice d, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : Euc d => Lattice.dot k y) := by
    intro k
    unfold Lattice.dot
    refine ContDiff.sum fun i _ => contDiff_const.mul ?_
    exact (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).contDiff
  have : Torus.lift (fun x : Torus d => ∑ k ∈ Λ, a k * Torus.cosMode k x) =
      fun y : Euc d => ∑ k ∈ Λ, a k * Real.cos (2 * Real.pi * Lattice.dot k y) := by
    funext y
    simp only [Torus.lift, Function.comp, Torus.cosMode_mk]
  rw [this]
  refine ContDiff.sum fun k _ => contDiff_const.mul ?_
  exact Real.contDiff_cos.comp (contDiff_const.mul (hdot k))

/-- The hypotheses of Lemma 4.10 for the pair kernel `q` of the weak split. -/
theorem weakSplit_pin_hyp (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hs : s ≠ 0) {τ : ℝ} (hτ : 0 < τ)
    (hτ1 : τ ≤ 1) (L : ℕ) :
    Measurable (weakSplit d s τ L).q ∧ (∀ z, 0 ≤ (weakSplit d s τ L).q z) ∧
      (∀ z, (weakSplit d s τ L).q (-z) = (weakSplit d s τ L).q z) ∧
      (∃ k : Torus d → ℝ, Torus.IsSmooth k ∧ ∃ c : ℝ, ∀ z, z ≠ 0 →
        periodicRiesz d s z = (weakSplit d s τ L).q z + k z + c) ∧
      (∃ Cq : ℝ, ∀ z, z ≠ 0 → (weakSplit d s τ L).q z ≤ Cq * (1 + Torus.eucDist z 0 ^ (-s))) := by
  obtain ⟨-, -, h3, -, h5, h6, -, -, -, hc0, -, h12, -, -, h15, -, -⟩ := weakSplit_spec hd hs0 hsd hτ hτ1 L
  refine ⟨h5, h6, fun z => Calib.hQ_even hd hs0 hsd τ L z, ?_, ?_⟩
  · obtain ⟨Λ, a, -, -, hΛ⟩ := h12
    refine ⟨(weakSplit d s τ L).gL, ?_, -(weakSplit d s τ L).c, fun z hz => ?_⟩
    · have : (weakSplit d s τ L).gL = fun x => ∑ k ∈ Λ, a k * Torus.cosMode k x := funext hΛ
      rw [this]; exact isSmooth_cosSum Λ a
    · rw [h3 z hz]; ring
  · obtain ⟨B, hB0, hB⟩ := h15
    refine ⟨B, fun z hz => ?_⟩
    have := hB z hz
    unfold singEnvelope at this
    simpa [hs] using this

section Bridge

variable {M : ℕ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {q gL : Torus d → ℝ}
  {Ψ : Torus d → EuclideanSpace ℝ (Fin M)} {γ : ℝ}

/-- The calibrated reference is the unpinned weak ensemble of `weakPotK`. -/
theorem RN_eq_pinnedLaw (h : Calib.RefHyp μ q gL Ψ γ) {β : ℝ} (hβ : 0 ≤ β) {N : ℕ} {K : ℝ}
    (ht : ∀ x, |inner ℝ (Calib.tN q μ Ψ β N) (Calib.Xi μ Ψ x)| ≤ K) :
    Calib.RN q μ Ψ β N = pinnedLaw (weakPotK h hβ (Calib.tN q μ Ψ β N) ht) (β / (N : ℝ)) N
      (fun e : Empty => e.elim) := by
  rw [RN_eq_fieldLawK h hβ ht, pinnedLaw_empty]

/-- The first marginal of the calibrated reference is `weakRefMarginal` for the field `t_N·Ξ`. -/
theorem weakRefMarginal_eq (h : Calib.RefHyp μ q gL Ψ γ) {β : ℝ} (hβ : 0 ≤ β) {N : ℕ} {K : ℝ}
    (ht : ∀ x, |inner ℝ (Calib.tN q μ Ψ β N) (Calib.Xi μ Ψ x)| ≤ K) :
    weakRefMarginal q (fun x => inner ℝ (Calib.tN q μ Ψ β N) (Calib.Xi μ Ψ x)) μ β N
      = firstMarginal (Calib.RN q μ Ψ β N) := by
  have hlam : 0 ≤ β / (N : ℝ) := div_nonneg hβ (Nat.cast_nonneg N)
  have e1 := pinnedReference_eq_pinnedLaw μ (weakPotK h hβ (Calib.tN q μ Ψ β N) ht) q
    (fun x => β * convMeasure q μ x + inner ℝ (Calib.tN q μ Ψ β N) (Calib.Xi μ Ψ x))
    (fun x y => rfl) rfl N hlam (Fin.elim0 : Fin 0 → Torus d)
  unfold weakRefMarginal
  rw [e1, PinAux.pinnedLaw_isEmpty, ← PinAux.pinnedLaw_isEmpty (a := (fun e : Empty => e.elim)), ← RN_eq_pinnedLaw h hβ ht]

end Bridge

/-! ### The pinned-marginal comparison data (Lemma 4.10) -/

section RefDensSec

variable {μ : Measure (Torus d)}

/-- The density data of Lemma 4.10 for the unpinned reference `R = pinnedLaw V (β/(n+1)) (n+1) ∅` and
its one-pin conditional laws: `π ≪ μ`, `|dπ/dμ - 1| ≤ δ`, and the conditional one-coordinate laws
`π^x_k ≪ μ` with `|dπ^x_k/dμ - dπ/dμ| ≤ C₁ min{1, (1 + q(z,x))/N}`. -/
structure RefDens (V : WeakPotential μ) (β : ℝ) (n : ℕ) (δ C1 : ℝ) : Prop where
  ac0 : (pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)).map
    (fun Y => Y 0) ≪ μ
  linf : ∀ᵐ y ∂μ, |(((pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)).map
    (fun Y => Y 0)).rnDeriv μ y).toReal - 1| ≤ δ
  ac1 : ∀ (x : Torus d) (k : Fin n), (pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) n
    (pinsWith (fun e : Empty => e.elim) x)).map (fun Y => Y k) ≪ μ
  cmp1 : ∀ (x : Torus d) (k : Fin n), ∀ᵐ z ∂μ,
    |(((pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) n (pinsWith (fun e : Empty => e.elim) x)).map
        (fun Y => Y k)).rnDeriv μ z).toReal -
      (((pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)).map
        (fun Y => Y 0)).rnDeriv μ z).toReal| ≤
      C1 * min 1 ((1 / ((n + 1 : ℕ) : ℝ)) * (1 + V.q z x))

/-- The two-pin density data of Lemma 4.10 (for `N = m + 2`): the `m` free coordinates of the
two-pinned ensemble have one-coordinate densities within `C₂ min{1, (1 + q(z,x) + q(z,y))/N}` of
`dπ_N/dμ`. -/
structure RefDens2 (V : WeakPotential μ) (β : ℝ) (m : ℕ) (C2 : ℝ) : Prop where
  ac2 : ∀ (x y : Torus d) (k : Fin m), (pinnedLaw V (β / ((m + 1 + 1 : ℕ) : ℝ)) m
    (pinsWith (pinsWith (fun e : Empty => e.elim) x) y)).map (fun Y => Y k) ≪ μ
  cmp2 : ∀ (x y : Torus d) (k : Fin m), ∀ᵐ z ∂μ,
    |(((pinnedLaw V (β / ((m + 1 + 1 : ℕ) : ℝ)) m (pinsWith (pinsWith (fun e : Empty => e.elim) x) y)).map
        (fun Y => Y k)).rnDeriv μ z).toReal -
      (((pinnedLaw V (β / ((m + 1 + 1 : ℕ) : ℝ)) (m + 1 + 1) (fun e : Empty => e.elim)).map
        (fun Y => Y 0)).rnDeriv μ z).toReal| ≤
      C2 * min 1 ((1 / ((m + 1 + 1 : ℕ) : ℝ)) * (1 + V.q z x + V.q z y))

end RefDensSec


section PinIdent

variable {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {B B' : Type*} [Fintype B] [Fintype B']

/-- The pinned law only depends on the pinned field. -/
theorem pinnedLaw_congr (V : WeakPotential μ) (lam : ℝ) (n : ℕ) (a : B → Torus d) (a' : B' → Torus d)
    (h : pinField V lam a = pinField V lam a') : pinnedLaw V lam n a = pinnedLaw V lam n a' := by
  unfold pinnedLaw; rw [h]

/-- One external pin: `pinnedReference` with `Fin 1` pins is the `pinsWith` pinned law. -/
theorem pinnedReference_one_pin (V : WeakPotential μ) (q field : Torus d → ℝ)
    (hVq : ∀ x y, V.q x y = q (x - y)) (hfield : V.φ = field) (n : ℕ) {lam : ℝ} (hlam : 0 ≤ lam)
    (x : Torus d) :
    pinnedReference q field μ n lam (fun _ : Fin 1 => x) =
      pinnedLaw V lam n (pinsWith (fun e : Empty => e.elim) x) := by
  rw [pinnedReference_eq_pinnedLaw μ V q field hVq hfield n hlam (fun _ : Fin 1 => x)]
  refine pinnedLaw_congr V lam n _ _ ?_
  funext z
  rw [pinField_pinsWith, HRS.External.RefMarg.pinField_empty]
  unfold pinField
  simp

/-- Two external pins: `pinnedReference` with `Fin 2` pins is the nested `pinsWith` pinned law. -/
theorem pinnedReference_two_pins (V : WeakPotential μ) (q field : Torus d → ℝ)
    (hVq : ∀ x y, V.q x y = q (x - y)) (hfield : V.φ = field) (n : ℕ) {lam : ℝ} (hlam : 0 ≤ lam)
    (x y : Torus d) :
    pinnedReference q field μ n lam (![x, y] : Fin 2 → Torus d) =
      pinnedLaw V lam n (pinsWith (pinsWith (fun e : Empty => e.elim) x) y) := by
  rw [pinnedReference_eq_pinnedLaw μ V q field hVq hfield n hlam (![x, y] : Fin 2 → Torus d)]
  refine pinnedLaw_congr V lam n _ _ ?_
  funext z
  rw [pinField_pinsWith, pinField_pinsWith, HRS.External.RefMarg.pinField_empty]
  unfold pinField
  simp [Fin.sum_univ_two]
  ring

end PinIdent

section Calib

variable {M : ℕ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {q gL : Torus d → ℝ}
  {Ψ : Torus d → EuclideanSpace ℝ (Fin M)} {γ : ℝ}

/-- The calibration identity in the form used by `reference_marginal_linf`: for the field
`h_N = t_N·Ξ`, `h_N = -β g_L * (π_N - 1) + c_N`, `π_N = dweakRefMarginal/dμ`. -/
theorem calib_form (h : Calib.RefHyp μ q gL Ψ γ) {β : ℝ} (hβ : 0 < β) {n : ℕ} {K : ℝ}
    (ht : ∀ x, |inner ℝ (Calib.tN q μ Ψ β (n + 1)) (Calib.Xi μ Ψ x)| ≤ K) :
    ∃ cN : ℝ, ∀ x, inner ℝ (Calib.tN q μ Ψ β (n + 1)) (Calib.Xi μ Ψ x) =
      -β * ∫ y, gL (x - y) * (((weakRefMarginal q
        (fun x => inner ℝ (Calib.tN q μ Ψ β (n + 1)) (Calib.Xi μ Ψ x)) μ β (n + 1)).rnDeriv μ y).toReal - 1)
        ∂μ + cN := by
  obtain ⟨c₀, hc₀⟩ := hh_eq h hβ ht (n := n)
  refine ⟨c₀, fun x => ?_⟩
  rw [hc₀ x]
  congr 2
  unfold ResponseAux.Kt
  rw [weakRefMarginal_eq h hβ.le ht, firstMarginal_RN_eq h hβ ht]
  have hθm := measurable_theta (weakPotK h hβ.le (Calib.tN q μ Ψ β (n + 1)) ht)
    (div_nonneg hβ.le (Nat.cast_nonneg ((n + 1 : ℕ) : ℕ)) : 0 ≤ β / ((n + 1 : ℕ) : ℝ)) n
  have hae := Measure.rnDeriv_withDensity μ (f := fun x => ENNReal.ofReal (theta
    (weakPotK h hβ.le (Calib.tN q μ Ψ β (n + 1)) ht) (β / ((n + 1 : ℕ) : ℝ)) n x))
    (ENNReal.measurable_ofReal.comp hθm)
  refine integral_congr_ae ?_
  filter_upwards [hae] with y hy
  rw [hy, ENNReal.toReal_ofReal (theta_pos _ (div_nonneg hβ.le (Nat.cast_nonneg _)) n y).le]

end Calib

/-! ### The setting -/

section Setting

open HRS.External.Glue in
/-- **The reference setting**: for the thermal density `ρ`, a calibrated weak reference
`R_n = pinnedLaw (Vf n) (β/(n+1)) (n+1) ∅` with the uniform bounds, the domination
`Q_{n+1} ≤ K R_n` (non-uniform for small `n`, uniform for `n+1 ≥ N₁`) and, for `n+1 ≥ N₁`, the
density data of Lemma 4.10. -/
theorem exists_setting (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (ρ : Torus d → ℝ) (hρs : SmoothPosDensity ρ) :
    ∃ (c Cq Mmax M'max γmax : ℝ) (N₁ : ℕ) (KQ δC C1 Cu C2 : ℝ)
      (Vf : ℕ → WeakPotential (withDensityReal ρ)),
      (∀ z, 0 ≤ periodicRiesz d s z + c) ∧ 0 ≤ Cq ∧ 2 ≤ N₁ ∧ 0 < KQ ∧ 0 ≤ δC ∧ 0 ≤ C1 ∧ 0 ≤ Cu ∧ 0 ≤ C2 ∧
      (∀ n (x y : Torus d), x ≠ y → (Vf n).q x y ≤ Cu * wEnv s x y) ∧
      (∀ n, PotBound (d := d) s c Mmax M'max γmax Cq (Vf n)) ∧
      (∀ n, IsProbabilityMeasure (modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ))) ∧
      (∀ n, ∃ K' : ℝ, 0 < K' ∧
        modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ) ≤ ENNReal.ofReal K' •
          pinnedLaw (Vf n) (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) ∧
      (∀ n, N₁ ≤ n + 1 →
        modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ) ≤ ENNReal.ofReal KQ •
          pinnedLaw (Vf n) (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim) ∧
        weakKappa (Vf n) β ≤ 1 / 2 ∧
        RefDens (Vf n) β n (δC * deltaN d s (n + 1)) C1) ∧
      (∀ m : ℕ, N₁ ≤ m + 2 → RefDens2 (Vf (m + 1)) β m C2) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 ≤ s := by rw [hcrit]; linarith
  have hsd : s < d := by rw [hcrit]; linarith
  have hs : s ≠ 0 := by rw [hcrit]; linarith
  have hρ := hρs.density
  haveI hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ
  obtain ⟨γ₁, hγ₁, hpin⟩ := pin_comparison_proof hd hcrit β hβ ρ hρs
  obtain ⟨γ₂, hγ₂, hlinf⟩ := reference_marginal_linf_ev hd hcrit β hβ ρ hρs
  obtain ⟨τ, L, Λ, M, Ψ, hτ, hτ1, hΛ1, hΛ, hΨ, hκ, hΛc⟩ :=
    exists_split_params' hd hs0 hsd hβ hρs (γ₀ := min γ₁ γ₂) (lt_min hγ₁ hγ₂)
  have hRH := Calib.refHyp_weakSplit hd hs0 hsd hτ hτ1 L hρ hΛ Ψ hΨ
  obtain ⟨hqm, hq0, hqe, hdec, Cq0, hqenv⟩ := weakSplit_pin_hyp hd hs0 hsd hs hτ hτ1 L
  set q := (weakSplit d s τ L).q with hqdef
  set gL := (weakSplit d s τ L).gL with hgLdef
  set c0 := (weakSplit d s τ L).c with hc0def
  have hrow : ∀ x, ∫⁻ y, ENNReal.ofReal (q (x - y)) ∂(withDensityReal ρ) ≤ ENNReal.ofReal (min γ₁ γ₂) := by
    intro x
    have h1 := hRH.q_row x
    rw [← ofReal_integral_eq_lintegral_ofReal (hRH.q_int x) (Filter.Eventually.of_forall fun y => hq0 _)]
    exact ENNReal.ofReal_le_ofReal (h1.trans hΛc)
  obtain ⟨-, -, hsplit, -, -, -, -, -, -, hc0nn, -, -, hgLc, -, -, -, -⟩ := weakSplit_spec hd hs0 hsd hτ hτ1 L
  have hgLabs : ∀ z, |gL z| ≤ gL 0 := fun z => abs_gL_le hRH z
  have hgL0 : 0 ≤ gL 0 := hRH.gL_zero_nonneg
  set c : ℝ := gL 0 + c0 + |periodicRiesz d s 0| with hcdef
  have hc : ∀ z, 0 ≤ periodicRiesz d s z + c := by
    intro z
    by_cases hz : z = 0
    · subst hz
      have := neg_abs_le (periodicRiesz d s 0)
      have := abs_nonneg (periodicRiesz d s 0)
      linarith
    · rw [hsplit z hz]
      have h1 := hgLabs z
      have h2 := neg_abs_le (gL z)
      have h3 := hq0 z
      have h4 := abs_nonneg (periodicRiesz d s 0)
      linarith
  set Cq : ℝ := max 0 (gL 0 + c) with hCqdef
  have hCq0 : 0 ≤ Cq := le_max_left _ _
  have hqlow : ∀ z : Torus d, z ≠ 0 → gPlus d s c z - Cq ≤ q z := by
    intro z hz
    unfold gPlus
    rw [hsplit z hz]
    have h1 := le_abs_self (gL z)
    have h2 := hgLabs z
    have h3 : gL 0 + c ≤ Cq := le_max_right _ _
    linarith
  set γ : ℝ := Λ * c0 with hγdef
  have hγ0 : 0 ≤ γ := hRH.gamma_nonneg
  set K0 : ℝ := max 1 (4 * β * gL 0) with hK0def
  have hK01 : 1 ≤ K0 := le_max_left _ _
  have ht0 : ∀ N : ℕ, 0 < N → ∀ x, |inner ℝ (Calib.tN q (withDensityReal ρ) Ψ β N)
      (Calib.Xi (withDensityReal ρ) Ψ x)| ≤ K0 :=
    fun N hN x => (abs_tN_inner_le hRH hβ hN x).trans (le_max_right _ _)
  obtain ⟨N₀, hN₀⟩ := Glue.eventually_hsmall hd hs0 hsd hτ hτ1 L hρ hΛ Ψ hΨ hβ
  have ht1 : ∀ N : ℕ, N₀ ≤ N → ∀ x, |inner ℝ (Calib.tN q (withDensityReal ρ) Ψ β N)
      (Calib.Xi (withDensityReal ρ) Ψ x)| ≤ 1 := fun N hN x => by
    have := hN₀ N hN x
    rwa [← Calib.inner_eq_sum] at this
  obtain ⟨N₂, hN₂⟩ := Glue.riesz_Q_le_smul_RN_eventually hd hs0 hsd hτ hτ1 L hρ hΛ Ψ hΨ hβ hκ
  classical
  let Vf : ℕ → WeakPotential (withDensityReal ρ) := fun n =>
    if h : N₀ ≤ n + 1 then weakPotK hRH hβ.le (Calib.tN q (withDensityReal ρ) Ψ β (n + 1)) (ht1 (n + 1) h)
    else weakPotK hRH hβ.le (Calib.tN q (withDensityReal ρ) Ψ β (n + 1)) (ht0 (n + 1) (Nat.succ_pos n))
  have hVq : ∀ n x y, (Vf n).q x y = q (x - y) := by
    intro n x y; simp only [Vf]; split_ifs <;> rfl
  have hVφ : ∀ n, (Vf n).φ = fun x => β * convMeasure q (withDensityReal ρ) x +
      inner ℝ (Calib.tN q (withDensityReal ρ) Ψ β (n + 1)) (Calib.Xi (withDensityReal ρ) Ψ x) := by
    intro n; simp only [Vf]; split_ifs <;> rfl
  have hVRN : ∀ n, Calib.RN q (withDensityReal ρ) Ψ β (n + 1) =
      pinnedLaw (Vf n) (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim) := by
    intro n; simp only [Vf]; split_ifs
    · exact RN_eq_pinnedLaw hRH hβ.le _
    · exact RN_eq_pinnedLaw hRH hβ.le _
  have hVbound : ∀ n, PotBound (d := d) s c (β * γ + K0) 0 γ Cq (Vf n) := by
    intro n
    refine ⟨?_, ?_, ?_, fun x y hxy => ?_⟩
    · simp only [Vf]; split_ifs <;> simp [weakPotK] <;> linarith
    · simp only [Vf]; split_ifs <;> simp [weakPotK]
    · simp only [Vf]; split_ifs <;> simp [weakPotK, hγdef]
    · rw [hVq]; exact hqlow (x - y) (sub_ne_zero.2 hxy)
  have hQprob : ∀ n, IsProbabilityMeasure (modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ)) :=
    fun n => riesz_Q_isProb hd hs0 hsd hτ hτ1 L hρ hΛ Ψ hΨ hβ (Nat.succ_pos n)
  have hcrude : ∀ n, ∃ K' : ℝ, 0 < K' ∧
      modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ) ≤ ENNReal.ofReal K' •
        pinnedLaw (Vf n) (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim) := by
    intro n
    obtain ⟨K', hK', hQK⟩ := riesz_Q_le_smul_RN_crude hd hs0 hsd hτ hτ1 L hρ hΛ Ψ hΨ hβ (Nat.succ_pos n)
    exact ⟨K', hK', by rw [← hVRN n]; exact hQK⟩
  -- Lemma 4.10 constants
  have hrow1 : ∀ x, ∫⁻ y, ENNReal.ofReal (q (x - y)) ∂(withDensityReal ρ) ≤ ENNReal.ofReal γ₁ :=
    fun x => (hrow x).trans (ENNReal.ofReal_le_ofReal (min_le_left _ _))
  have hrow2 : ∀ x, ∫⁻ y, ENNReal.ofReal (q (x - y)) ∂(withDensityReal ρ) ≤ ENNReal.ofReal γ₂ :=
    fun x => (hrow x).trans (ENNReal.ofReal_le_ofReal (min_le_right _ _))
  obtain ⟨Cpin, hCpin⟩ := hpin q Cq0 hqm hq0 hqe hdec hqenv hrow1 1 1
  obtain ⟨Cac, hCac⟩ := hpin q Cq0 hqm hq0 hqe hdec hqenv hrow1 0 0
  obtain ⟨Cpin2, hCpin2⟩ := hpin q Cq0 hqm hq0 hqe hdec hqenv hrow1 2 2
  obtain ⟨CR, N₃, hR2⟩ := reference_marginal_density_L2 hd hs0 hsd hτ hτ1 L hΛ1 hβ hκ Ψ hΨ
  have hunif := reference_marginal_density_uniform hd hs0 hsd hτ hτ1 L hΛ1 hβ hκ Ψ hΨ
  have hgLm : Measurable gL := hgLc.measurable
  have hfieldm : ∀ N : ℕ, Measurable (fun x => inner ℝ (Calib.tN q (withDensityReal ρ) Ψ β N)
      (Calib.Xi (withDensityReal ρ) Ψ x)) := fun N => measurable_const.inner hRH.measurable_Xi
  have hWRM : ∀ N : ℕ, 0 < N → weakRefMarginal q (fun x => inner ℝ (Calib.tN q (withDensityReal ρ) Ψ β N)
      (Calib.Xi (withDensityReal ρ) Ψ x)) (withDensityReal ρ) β N =
      firstMarginal (Calib.RN q (withDensityReal ρ) Ψ β N) :=
    fun N hN => weakRefMarginal_eq hRH hβ.le (ht0 N hN)
  set Ns : ℕ := max (max N₀ N₃) 3 with hNs
  have hNs3 : 3 ≤ Ns := le_max_right _ _
  obtain ⟨Clinf, hClinf⟩ := hlinf q Cq0 hqm hq0 hqe hdec hqenv hrow2 gL (gL 0) hgLm hgLabs Ns (by omega)
    (fun N x => inner ℝ (Calib.tN q (withDensityReal ρ) Ψ β N) (Calib.Xi (withDensityReal ρ) Ψ x))
    (fun N hN => ⟨hfieldm N, ht1 N (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN)⟩)
    (fun N hN => by
      have := hCac N (by omega) _ (hfieldm N)
        (ht1 N (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN)) (Fin.elim0 : Fin 0 → Torus d)
        ⟨0, by omega⟩
      exact this.2.1)
    (fun N hN => by
      obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
      exact calib_form hRH hβ (ht1 (n + 1) (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN)))
    ⟨CR, fun N hN => by
      have hN3 : N₃ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
      rw [hWRM N (by omega)]
      exact (hR2 ρ hρ hΛ N hN3).2⟩
    (fun ε hε => by
      obtain ⟨N₄, hN4⟩ := hunif ε hε
      refine ⟨max N₄ 1, fun N hN => ?_⟩
      rw [hWRM N (by omega)]
      exact (hN4 ρ hρ hΛ N (le_trans (le_max_left _ _) hN)).2)
  set N₁ : ℕ := max (max Ns N₂) 4 with hN₁
  have hN₁Ns : Ns ≤ N₁ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hN₁N₂ : N₂ ≤ N₁ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hN₁3 : 4 ≤ N₁ := le_max_right _ _
  have hN₀Ns : N₀ ≤ Ns := le_trans (le_max_left _ _) (le_max_left _ _)
  have hqup : ∀ x y : Torus d, x ≠ y → q (x - y) ≤ |Cq0| * wEnv s x y := by
    intro x y hxy
    have h1 := hqenv (x - y) (sub_ne_zero.2 hxy)
    have hr := PairCorrAux.rTrunc_pos hxy
    have hd0 : Torus.eucDist (x - y) 0 = Torus.eucDist x y := (eucDist_sub x y).symm
    rw [hd0] at h1
    have h2 : Torus.eucDist x y ^ (-s) ≤ rTrunc x y ^ (-s) :=
      Real.rpow_le_rpow_of_nonpos hr (PairCorrAux.rTrunc_le_dist x y) (by linarith)
    have h3 : 0 ≤ 1 + Torus.eucDist x y ^ (-s) :=
      add_nonneg zero_le_one (Real.rpow_nonneg (PairCorrAux.eucDist_nonneg' x y) _)
    unfold wEnv
    calc q (x - y) ≤ Cq0 * (1 + Torus.eucDist x y ^ (-s)) := h1
      _ ≤ |Cq0| * (1 + Torus.eucDist x y ^ (-s)) := mul_le_mul_of_nonneg_right (le_abs_self _) h3
      _ ≤ |Cq0| * (1 + rTrunc x y ^ (-s)) := by gcongr
  have hπall : ∀ n : ℕ, (pinnedLaw (Vf n) (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)).map
      (fun Y => Y 0) = weakRefMarginal q (fun x => inner ℝ (Calib.tN q (withDensityReal ρ) Ψ β (n + 1))
        (Calib.Xi (withDensityReal ρ) Ψ x)) (withDensityReal ρ) β (n + 1) := by
    intro n
    rw [hWRM (n + 1) (Nat.succ_pos n), ← hVRN n]
    unfold firstMarginal
    rw [dif_pos (Nat.succ_pos n)]
    rfl
  refine ⟨c, Cq, β * γ + K0, 0, γ, N₁, Real.exp (4 * β * gL 0), max Clinf 0, max Cpin 0, |Cq0|,
    max Cpin2 0, Vf, hc, hCq0,
    by omega, Real.exp_pos _, le_max_right _ _, le_max_right _ _, abs_nonneg _, le_max_right _ _,
    fun n x y hxy => by rw [hVq]; exact hqup x y hxy, hVbound, hQprob, hcrude, ?_, ?_⟩
  swap
  · intro m hm
    have hn : N₁ ≤ m + 1 + 1 := hm
    have hNs : Ns ≤ m + 1 + 1 := le_trans hN₁Ns hn
    have hN0 : N₀ ≤ m + 1 + 1 := le_trans hN₀Ns hNs
    have hlam : 0 ≤ β / ((m + 1 + 1 : ℕ) : ℝ) := div_nonneg hβ.le (Nat.cast_nonneg _)
    have hπ := hπall (m + 1)
    refine ⟨?_, ?_⟩
    · intro x y k
      have := (hCpin2 (m + 2) (by omega) _ (hfieldm (m + 2)) (ht1 (m + 2) hN0) (![x, y] : Fin 2 → Torus d) k).1
      rw [← pinnedReference_two_pins (Vf (m + 1)) q _ (hVq (m + 1)) (hVφ (m + 1)) m hlam x y]
      exact this
    · intro x y k
      have h1 := (hCpin2 (m + 2) (by omega) _ (hfieldm (m + 2)) (ht1 (m + 2) hN0) (![x, y] : Fin 2 → Torus d) k).2.2
      rw [← pinnedReference_two_pins (Vf (m + 1)) q _ (hVq (m + 1)) (hVφ (m + 1)) m hlam x y, hπ]
      filter_upwards [h1] with z hz
      refine hz.trans ?_
      have e : ∑ k : Fin 2, q (z - (![x, y] : Fin 2 → Torus d) k) = (Vf (m + 1)).q z x + (Vf (m + 1)).q z y := by
        rw [hVq, hVq]; simp [Fin.sum_univ_two]
      rw [e]
      have hq1 := (Vf (m + 1)).q_nonneg z x
      have hq2 := (Vf (m + 1)).q_nonneg z y
      have : (1 : ℝ) + ((Vf (m + 1)).q z x + (Vf (m + 1)).q z y) = 1 + (Vf (m + 1)).q z x + (Vf (m + 1)).q z y := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (le_min zero_le_one (by positivity))
  intro n hn
  have hNs : Ns ≤ n + 1 := le_trans hN₁Ns hn
  have hN0 : N₀ ≤ n + 1 := le_trans hN₀Ns hNs
  have hdif : Vf n = weakPotK hRH hβ.le (Calib.tN q (withDensityReal ρ) Ψ β (n + 1)) (ht1 (n + 1) hN0) := by
    simp only [Vf]; rw [dif_pos hN0]
  refine ⟨?_, ?_, ?_⟩
  · rw [← hVRN n]; exact hN₂ (n + 1) (le_trans hN₁N₂ hn)
  · rw [hdif]; exact weakKappa_weakPotK_le hRH hβ.le (ht1 (n + 1) hN0) hκ
  · have hlam : 0 ≤ β / ((n + 1 : ℕ) : ℝ) := div_nonneg hβ.le (Nat.cast_nonneg _)
    have hπ := hπall n
    have hδ : 0 ≤ deltaN d s (n + 1) := PinAux.deltaN_nonneg hcrit (by omega)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hπ]
      exact (hCac (n + 1) (by omega) _ (hfieldm (n + 1)) (ht1 (n + 1) hN0) (Fin.elim0 : Fin 0 → Torus d)
        ⟨0, by omega⟩).2.1
    · rw [hπ]
      filter_upwards [hClinf (n + 1) hNs] with y hy
      refine hy.trans ?_
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hδ
    · intro x k
      have := (hCpin (n + 1) (by omega) _ (hfieldm (n + 1)) (ht1 (n + 1) hN0) (fun _ : Fin 1 => x) k).1
      rw [← pinnedReference_one_pin (Vf n) q _ (hVq n) (hVφ n) n hlam x]
      exact this
    · intro x k
      have h1 := (hCpin (n + 1) (by omega) _ (hfieldm (n + 1)) (ht1 (n + 1) hN0) (fun _ : Fin 1 => x) k).2.2
      rw [← pinnedReference_one_pin (Vf n) q _ (hVq n) (hVφ n) n hlam x, hπ]
      filter_upwards [h1] with z hz
      refine hz.trans ?_
      have e : ∑ k : Fin 1, q (z - (fun _ : Fin 1 => x) k) = (Vf n).q z x := by
        rw [hVq]; simp
      rw [e]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _)
        (le_min zero_le_one (by have := (Vf n).q_nonneg z x; positivity))

end Setting

end HRS.PairMom

end

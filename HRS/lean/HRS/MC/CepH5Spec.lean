import HRS.MC.CepaSpec
import HRS.Appendix.B15Aux2

/-!
# Packet CEPH5SPEC: decomposition of B.14 (`cep_H5_entropy_confined`) into lemmas

SPECIFICATION FILE.  The lemmas `h5Comp_*`, `h5_class_constancy`, `h5_flow_of_ac`, `h5_cond_*`, `h5_selectedLaw_mixture`,
`h5_fisher_measurable` below are `sorry` (their docstrings give the mathematical proofs); the EReal/ENNReal bookkeeping lemmas
(`h5_gibbsEntropy_ne_bot`, `h5_components_lt_top`, `h5_recombine`) are proved; the final
theorem `cep_H5_assembly` has the statement of `HRS.MC.Cepa.cep_H5_entropy_confined` and is proved from
`cep_H1_fke`, `cep_H4_single_component`, `cep_H0_component_additivity`, `cep_H4a_density_of_entropy` and the `h5*` lemmas.

Components: `ι := {σ : Equiv.Perm (Fin N) // σ 0 = 0}`; `h5Comp σ` is the set of configurations with a strictly
ordered lift along `σ` (one cyclic order class).  `X₀ ∈ h5Comp σ` is an event `A_σ`; the conditional measure
`cond P A_σ = (P A_σ)⁻¹ • P.restrict A_σ` carries the same flow (L3), with the single anchor `σ` (H4).
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH5

open HRS HRS.MC.Cepa

/-! ### Components -/

/-- The index set: one representative `σ` (with `σ 0 = 0`) of each cyclic order class of labels. -/
abbrev h5Idx (N : ℕ) [NeZero N] := {σ : Equiv.Perm (Fin N) // σ 0 = 0}

/-- The component `C σ`: configurations having a lift strictly ordered along `σ`. -/
def h5Comp {N : ℕ} (σ : Equiv.Perm (Fin N)) : Set (Config 1 N) :=
  {x | ∃ y : Fin N → Euc 1, (fun i => Torus.mk (y i)) = x ∧ cep_StrictlyOrdered σ y}

section Components

variable {N : ℕ} [NeZero N]

/-- **L1a**: `h5Comp σ` is open.  It is the image under the open covering map `y ↦ (mk (y i))ᵢ` of the open set
`{y | y(σ 0) 0 < ... < y(σ (N-1)) 0 < y(σ 0) 0 + 1}` (finitely many strict inequalities of continuous functions). -/
theorem h5Comp_isOpen (σ : Equiv.Perm (Fin N)) : IsOpen (h5Comp σ) := by
  sorry

/-- **L1b**: distinct representatives give disjoint components.  If `x` has strictly ordered lifts `y` along `σ` and
`y'` along `σ'`, then both list the particles of `x` in the cyclic order of the circle starting from the particle
`σ 0 = 0 = σ' 0`: by induction on `k`, `σ k = σ' k` (the successor of a particle in the cyclic order is unique since
`x` is collision-free and `y`, `y'` have spread `< 1`). -/
theorem h5Comp_disjoint : Pairwise fun σ σ' : h5Idx N => Disjoint (h5Comp σ.1) (h5Comp σ'.1) := by
  sorry

/-- **L1c** (E0 plus rotation): the components cover exactly the collision-free configurations.  `⊆`: a strictly
ordered lift has pairwise distinct classes mod `1`.  `⊇`: sort the representatives `rep (x i) ∈ [0,1)` (strictly
increasing since `x` is collision-free) to get `π` with a strictly ordered lift, then rotate the ranks by
`m = π.symm 0` (`σ k = π (k + m)`, adding `1` to the coordinates that wrap around) so that `σ 0 = 0`. -/
theorem h5Comp_iUnion : (⋃ σ : h5Idx N, h5Comp σ.1) = (collisionSet 1 N)ᶜ := by
  sorry

/-- **L1d**: every component is nonempty (take `y (σ k) 0 = k / N`).  Used only to choose a harmless probability
measure `dirac x_σ` supported on `C σ` for the classes of `P`-measure `0`. -/
theorem h5Comp_nonempty (σ : h5Idx N) : (h5Comp σ.1).Nonempty := by
  sorry

end Components

section Flow

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ} [NeZero N]

/-- **L2 (class constancy)**.  A.s. in `ω`: if `X₀ ω ∈ C σ` and `X t ω` is collision-free for some `t ∈ [0,T]`, then
`X t ω ∈ C σ`.  Proof: `hX.ordered` gives a continuous lift `Y` weakly cyclically ordered along `π ω` for all `t ≤ T`
(and `X 0 = X₀`, `X t = mk ∘ Y t` a.s.).  A weakly cyclically ordered lift of a collision-free configuration is strictly
ordered (equality of two coordinates mod `1` would be a collision).  At `t = 0` this makes `Y 0` a strictly ordered lift
along `π ω` of `X₀ ω ∈ C σ`; by uniqueness of the cyclic class (proof of L1b) `σ = π ω ∘ rot_m` for a rotation
`m = m ω`, `σ 0 = 0`.  At the collision-free time `t`, `Y t` is strictly ordered along `π ω`, and re-reading it along
`σ` (rotating the ranks by `m`, adding `1` to the wrapped coordinates) gives a strictly ordered lift along `σ`. -/
theorem h5_class_constancy {D : DynData 1} {T : ℝ} {X₀ : Ω → Config 1 N}
    {W : ℝ≥0 → Ω → (Fin N → Euc 1)} {X : ℝ≥0 → Ω → Config 1 N}
    (hX : IsCepaLepingleFlow P D T X₀ W X) :
    ∀ᵐ ω ∂P, ∀ σ : h5Idx N, X₀ ω ∈ h5Comp σ.1 → ∀ t : ℝ≥0, (t : ℝ) ≤ T →
      X t ω ∉ collisionSet 1 N → X t ω ∈ h5Comp σ.1 := by
  sorry

/-- **L3a** (the flow property transfers to any absolutely continuous measure, in particular to the conditional
measure): every field of `IsCepaLepingleFlow` (`lift`, `init`, `cont`, `ordered`, `occupation`) is an a.s. statement
(with the same measurable `π`) or a measurability statement, and `Q ≪ P` transfers a.s. statements. -/
theorem h5_flow_of_ac {Q : Measure Ω} (hQP : Q ≪ P) {D : DynData 1} {T : ℝ} {X₀ : Ω → Config 1 N}
    {W : ℝ≥0 → Ω → (Fin N → Euc 1)} {X : ℝ≥0 → Ω → Config 1 N}
    (hX : IsCepaLepingleFlow P D T X₀ W X) : IsCepaLepingleFlow Q D T X₀ W X := by
  sorry

/-- **L3b** (Brownian motion survives conditioning on an `X₀`-event).  For `B` measurable with `P (X₀⁻¹ B) ≠ 0`,
`W` is a vector Brownian motion under `P[·| X₀ ∈ B]`: by `hind`, `P(A ∩ {W ∈ E}) = P(A) P(W ∈ E)` for `A = X₀⁻¹ B`,
so the law of `W` (hence of every coordinate path, and the joint independence of the coordinates) is unchanged. -/
theorem h5_cond_brownian [IsProbabilityMeasure P] {X₀ : Ω → Config 1 N} (hX₀ : Measurable X₀)
    {W : ℝ≥0 → Ω → (Fin N → Euc 1)} (hW : IsVectorBrownian P W)
    (hind : IndepFun X₀ (fun ω => fun t => W t ω) P)
    {B : Set (Config 1 N)} (hB : MeasurableSet B) (hPB : P (X₀ ⁻¹' B) ≠ 0) :
    IsVectorBrownian (ProbabilityTheory.cond P (X₀ ⁻¹' B)) W := by
  sorry

/-- **L3c** (independence survives conditioning on an `X₀`-event): for `A = X₀⁻¹ B`,
`P(A ∩ {X₀ ∈ B'} ∩ {W ∈ E}) = P(A ∩ {X₀ ∈ B'}) P(W ∈ E)` by `hind` applied to `B ∩ B'`; divide by `P(A)`. -/
theorem h5_cond_indep [IsProbabilityMeasure P] {X₀ : Ω → Config 1 N} (hX₀ : Measurable X₀)
    {W : ℝ≥0 → Ω → (Fin N → Euc 1)} (hind : IndepFun X₀ (fun ω => fun t => W t ω) P)
    {B : Set (Config 1 N)} (hB : MeasurableSet B) (hPB : P (X₀ ⁻¹' B) ≠ 0) :
    IndepFun X₀ (fun ω => fun t => W t ω) (ProbabilityTheory.cond P (X₀ ⁻¹' B)) := by
  sorry

/-- **L3d** (filtered solution under conditioning).  Let `A = X₀⁻¹ B`.  Since `X 0 = X₀` a.s. and `X 0` is
`ℱ 0`-measurable, completeness of `ℱ` (a field of `hF.brownian`) puts `A` in `ℱ 0`.  Under `Q = P[·|A]` the
filtration `ℱ` is no longer complete (new `Q`-null sets `Aᶜ ∩ s` appear), so take `ℱ' t := ℱ t ⊔ σ(measurable
`Q`-null sets)`: this is again a filtration, `Q`-complete, `W t` and `X t` stay adapted, `X` stays progressive.
Independence of the increments `W t - W s` from `ℱ' s` and their Gaussian law hold under `Q` because `A ∈ ℱ 0 ⊆ ℱ s`
and increments are independent of `ℱ s` under `P`. -/
theorem h5_cond_filtered [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ}
    {X₀ : Ω → Config 1 N} (hX₀ : Measurable X₀) {W : ℝ≥0 → Ω → (Fin N → Euc 1)}
    {X : ℝ≥0 → Ω → Config 1 N} (hinit : ∀ᵐ ω ∂P, X 0 ω = X₀ ω)
    (hF : IsFilteredSolution P ℱ W' W X) {B : Set (Config 1 N)} (hB : MeasurableSet B)
    (hPB : P (X₀ ⁻¹' B) ≠ 0) :
    ∃ ℱ' : Filtration ℝ mΩ, IsFilteredSolution (ProbabilityTheory.cond P (X₀ ⁻¹' B)) ℱ' W' W X := by
  sorry

/-- **L3e** (the selected law is the mixture of the conditional selected laws).  The sets `A_σ = X₀⁻¹ (C σ)`
are measurable, pairwise disjoint and cover `Ω` up to a `P`-null set (L1b, L1c, `hdist`).  Hence for measurable
`S`, `P (X t ∈ S) = ∑_σ P (A_σ ∩ {X t ∈ S}) = ∑_σ P(A_σ) P[X t ∈ S | A_σ]` (`cond_apply'`; when `P A_σ = 0`
both sides of the `σ`-term vanish). -/
theorem h5_selectedLaw_mixture [IsProbabilityMeasure P] {X₀ : Ω → Config 1 N} (hX₀ : Measurable X₀)
    (hdist : ∀ᵐ ω ∂P, X₀ ω ∉ collisionSet 1 N) {X : ℝ≥0 → Ω → Config 1 N} (t : ℝ)
    (hXt : Measurable (X (Real.toNNReal t))) :
    selectedLaw P X t = ∑ σ : h5Idx N, ENNReal.ofReal ((P (X₀ ⁻¹' h5Comp σ.1)).toReal) •
      selectedLaw (ProbabilityTheory.cond P (X₀ ⁻¹' h5Comp σ.1)) X t := by
  sorry

/-- **L3f** (measurability of the Fisher information along the flow; needed to integrate a finite sum termwise).
REPAIR (2026-10-18, proof worker): the hypothesis `hV : Torus.IsCk 1 D.V` was missing; `fisherInfo` contains `fderiv` of the total potential,
which is junk (not continuous, not even measurable) for rough `V`.
For a probability measure `Q` and an a.s. continuous adapted process `X`, `r ↦ selectedLaw Q X r` is weakly continuous
(dominated convergence: the paths are continuous and `Real.toNNReal` is continuous), while `fisherInfo D N` is weakly
lower semicontinuous: it is the supremum over test fields `ζ ∈ C_c^∞(Ω_N)` of `μ ↦ ofReal ∫ F_ζ dμ` with
`F_ζ = -2 Div ζ + 2 β DU[ζ] - |ζ|²` bounded and continuous on `Config 1 N` (compact support in the open collision-free set, periodicity of
`ζ ∘ mk` makes `F_ζ` independent of the chosen lift).  A lower semicontinuous function of a continuous map is
lower semicontinuous, hence Borel measurable. -/
theorem h5_fisher_measurable {Q : Measure Ω} [IsProbabilityMeasure Q] (D : DynData 1)
    (hV : Torus.IsCk 1 D.V)
    {X : ℝ≥0 → Ω → Config 1 N} (hmeas : ∀ t, Measurable (X t))
    (hcont : ∀ᵐ ω ∂Q, ∀ i, Continuous fun t => X t ω i) :
    Measurable fun r : ℝ => fisherInfo D N (selectedLaw Q X r) := by
  sorry

end Flow

/-! ### Bookkeeping in `EReal` / `ℝ≥0∞` (finite mixtures) -/

section Bookkeeping

/-- A finite sum of real coercions is the coercion of the real sum (glue; proved). -/
theorem h5_coe_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ∑ i ∈ s, ((f i : ℝ) : EReal) = ((∑ i ∈ s, f i : ℝ) : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, EReal.coe_add]


/-- A finite sum of terms `≠ ⊥` is `≠ ⊥` (glue; proved). -/
theorem h5_sum_ne_bot {ι : Type*} (s : Finset ι) (f : ι → EReal) (h : ∀ i, f i ≠ ⊥) : ∑ i ∈ s, f i ≠ ⊥ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact fun hh => (EReal.add_eq_bot_iff.1 hh).elim (h a) ih

/-- `gibbsEntropy` is never `⊥` (proved): it is `↑(relEntropy) - ↑(log Z)` with `relEntropy ∈ [0,∞]` and `log Z` real. -/
theorem h5_gibbsEntropy_ne_bot {N : ℕ} (D : DynData 1) (μ : Measure (Config 1 N)) :
    gibbsEntropy D μ ≠ ⊥ := by
  unfold gibbsEntropy
  generalize relEntropy μ (gibbsRef D N) = x
  generalize Real.log (gibbsPartition D N).toReal = r
  rcases eq_or_ne x ⊤ with rfl | hx
  · simp
  · have : ((x : ℝ≥0∞) : EReal) = ((x.toReal : ℝ) : EReal) := by
      rw [← EReal.coe_ennreal_toReal hx]
    rw [this, ← EReal.coe_sub]
    exact EReal.coe_ne_bot _


/-- **B1** (finiteness of the components).  In a mixture `∑ p_i a_i + c` of `EReal` numbers `a_i ≠ ⊥` with weights
`p_i ≥ 0` and a real `c`, finiteness of the total forces `a_i < ⊤` for every `i` with `p_i ≠ 0` (a term `p_i * ⊤ = ⊤`
absorbs the finitely many other terms, none of which is `⊥`). -/
theorem h5_components_lt_top {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (a : ι → EReal)
    (ha : ∀ i, a i ≠ ⊥) (c : EReal) (hc1 : c ≠ ⊥) (hc2 : c ≠ ⊤)
    (h : ∑ i, ((p i : ℝ) : EReal) * a i + c < ⊤) : ∀ i, p i ≠ 0 → a i < ⊤ := by
  classical
  intro i0 hi0
  by_contra hcon
  have hat : a i0 = ⊤ := by
    rcases (not_lt.1 hcon).eq_or_lt with h' | h'
    · exact (top_le_iff.1 (not_lt.1 hcon))
    · exact absurd h' (not_lt.2 le_top)
  have hpos : 0 < p i0 := lt_of_le_of_ne (hp i0) (Ne.symm hi0)
  have hterm : ((p i0 : ℝ) : EReal) * a i0 = ⊤ := by
    rw [hat]; exact EReal.coe_mul_top_of_pos hpos
  have hne : ∀ i, ((p i : ℝ) : EReal) * a i ≠ ⊥ := by
    intro i
    by_cases hz : p i = 0
    · simp [hz]
    · exact (EReal.mul_ne_bot _ _).2 ⟨Or.inl (EReal.coe_ne_bot _), Or.inr (ha i),
        Or.inl (EReal.coe_ne_top _), Or.inl (EReal.coe_nonneg.2 (hp i))⟩
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i0), hterm,
    EReal.top_add_of_ne_bot (h5_sum_ne_bot _ _ hne), EReal.top_add_of_ne_bot hc1] at h
  exact lt_irrefl _ h


/-- **B2** (recombination of the entropy inequalities).  If for the weights `p_i ≥ 0` and each `i` with `p_i ≠ 0`
`Ht_i + F_i ≤ H0_i < ⊤` with `Ht_i, H0_i ≠ ⊥`, then for any real `c`
`∑ p_i Ht_i + c + ↑(∑ ofReal p_i * F_i) ≤ ∑ p_i H0_i + c`.  Proof: for `p_i ≠ 0` the three numbers `Ht_i, F_i, H0_i`
are finite (`Ht_i ≠ ⊥`, `Ht_i + F_i ≤ H0_i < ⊤`), so everything is real arithmetic; terms with `p_i = 0` vanish. -/
theorem h5_recombine {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (Ht H0 : ι → EReal)
    (F : ι → ℝ≥0∞) (hHt : ∀ i, Ht i ≠ ⊥) (hH0 : ∀ i, H0 i ≠ ⊥)
    (h : ∀ i, p i ≠ 0 → H0 i < ⊤ ∧ Ht i + (F i : EReal) ≤ H0 i) (c : EReal) (hc1 : c ≠ ⊥) (hc2 : c ≠ ⊤) :
    ∑ i, ((p i : ℝ) : EReal) * Ht i + c + ((∑ i, ENNReal.ofReal (p i) * F i : ℝ≥0∞) : EReal)
      ≤ ∑ i, ((p i : ℝ) : EReal) * H0 i + c := by
  classical
  obtain ⟨c', rfl⟩ : ∃ c' : ℝ, c = (c' : EReal) := ⟨c.toReal, (EReal.coe_toReal hc2 hc1).symm⟩
  -- real shadows
  have key : ∀ i, ((p i : ℝ) : EReal) * Ht i = (((p i * (Ht i).toReal : ℝ)) : EReal) := by
    intro i
    by_cases hz : p i = 0
    · simp [hz]
    · obtain ⟨h1, h2⟩ := h i hz
      have hHtt : Ht i ≠ ⊤ := by
        intro ht
        rw [ht] at h2
        have : (⊤ : EReal) + (F i : EReal) = ⊤ := EReal.top_add_of_ne_bot (by simp)
        rw [this] at h2
        exact absurd (lt_of_le_of_lt h2 h1) (lt_irrefl _)
      rw [EReal.coe_mul, EReal.coe_toReal hHtt (hHt i)]
  have key0 : ∀ i, ((p i : ℝ) : EReal) * H0 i = (((p i * (H0 i).toReal : ℝ)) : EReal) := by
    intro i
    by_cases hz : p i = 0
    · simp [hz]
    · obtain ⟨h1, h2⟩ := h i hz
      rw [EReal.coe_mul, EReal.coe_toReal h1.ne (hH0 i)]
  have keyF : ∀ i, ENNReal.ofReal (p i) * F i = ENNReal.ofReal (p i * (F i).toReal) := by
    intro i
    by_cases hz : p i = 0
    · simp [hz]
    · obtain ⟨h1, h2⟩ := h i hz
      have hFt : F i ≠ ⊤ := by
        intro ft
        have hh : Ht i + (F i : EReal) = ⊤ := by
          rw [ft]; simp; exact EReal.add_top_of_ne_bot (hHt i)
        rw [hh] at h2
        exact absurd (lt_of_le_of_lt h2 h1) (lt_irrefl _)
      rw [ENNReal.ofReal_mul (hp i), ENNReal.ofReal_toReal hFt]
  have hineq : ∑ i, p i * (Ht i).toReal + c' + ∑ i, p i * (F i).toReal ≤ ∑ i, p i * (H0 i).toReal + c' := by
    have : ∑ i, p i * (Ht i).toReal + ∑ i, p i * (F i).toReal ≤ ∑ i, p i * (H0 i).toReal := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      by_cases hz : p i = 0
      · simp [hz]
      · obtain ⟨h1, h2⟩ := h i hz
        have hHtt : Ht i ≠ ⊤ := by
          intro ht
          rw [ht] at h2
          have : (⊤ : EReal) + (F i : EReal) = ⊤ := EReal.top_add_of_ne_bot (by simp)
          rw [this] at h2
          exact absurd (lt_of_le_of_lt h2 h1) (lt_irrefl _)
        have hFt : F i ≠ ⊤ := by
          intro ft
          have hh : Ht i + (F i : EReal) = ⊤ := by
            rw [ft]; simp; exact EReal.add_top_of_ne_bot (hHt i)
          rw [hh] at h2
          exact absurd (lt_of_le_of_lt h2 h1) (lt_irrefl _)
        rw [← mul_add]
        refine mul_le_mul_of_nonneg_left ?_ (hp i)
        have e1 : (Ht i) = ((Ht i).toReal : EReal) := (EReal.coe_toReal hHtt (hHt i)).symm
        have e2 : (F i : EReal) = (((F i).toReal : ℝ) : EReal) := by
          rw [← EReal.coe_ennreal_toReal hFt]
        have e0 : (H0 i) = ((H0 i).toReal : EReal) := (EReal.coe_toReal h1.ne (hH0 i)).symm
        rw [e1, e2, e0, ← EReal.coe_add] at h2
        exact EReal.coe_le_coe_iff.1 h2
    linarith
  simp only [key, key0, keyF]
  rw [h5_coe_sum, h5_coe_sum, ← ENNReal.ofReal_sum_of_nonneg
    (fun i _ => mul_nonneg (hp i) ENNReal.toReal_nonneg), EReal.coe_ennreal_ofReal,
    ← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_add]
  refine EReal.coe_le_coe_iff.2 ?_
  have := le_max_left (∑ i, p i * (F i).toReal) 0
  rw [max_eq_left (Finset.sum_nonneg fun i _ => mul_nonneg (hp i) ENNReal.toReal_nonneg)]
  exact hineq


end Bookkeeping


/-! ### Assembly -/

section Assembly

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

open Classical in
/-- The conditional selected law of the class `σ` at time `t` (with a harmless probability measure supported on
`C σ` for classes of `P`-measure `0`, whose weight is `0` in every mixture). -/
def h5Nu [NeZero N] (P : Measure Ω) (X₀ : Ω → Config 1 N) (X : ℝ≥0 → Ω → Config 1 N) (t : ℝ)
    (σ : h5Idx N) : Measure (Config 1 N) :=
  if P (X₀ ⁻¹' h5Comp σ.1) = 0 then Measure.dirac (Classical.choose (h5Comp_nonempty σ))
  else selectedLaw (ProbabilityTheory.cond P (X₀ ⁻¹' h5Comp σ.1)) X t

/-- **H5, assembly** (the statement of `cep_H5_entropy_confined`, copied verbatim; proved from `cep_H1_fke`,
`cep_H4_single_component`, `cep_H0_component_additivity`, `cep_H4a_density_of_entropy` and the `h5*` lemmas). -/
theorem cep_H5_assembly [IsProbabilityMeasure P]
    (hN : 2 ≤ N) [NeZero N]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ}
    {D : DynData 1} (hs : D.s = 0) (hβ : 0 < D.invβ)
    (hM : D.M = -(1 : Matrix (Fin 1) (Fin 1) ℝ)) (hV : Torus.IsCk 2 D.V)
    {T : ℝ} (hT : 0 < T)
    {X₀ : Ω → Config 1 N} (hX₀ : Measurable X₀) (hdist : ∀ᵐ ω ∂P, X₀ ω ∉ collisionSet 1 N)
    {W : ℝ≥0 → Ω → (Fin N → Euc 1)} (hW : IsVectorBrownian P W)
    (hind : IndepFun X₀ (fun ω => fun t => W t ω) P)
    {X : ℝ≥0 → Ω → Config 1 N}
    (hX : IsCepaLepingleFlow P D T X₀ W X) (hF : IsFilteredSolution P ℱ W' W X)
    (hdens0 : HasSelectedDensity P X 0)
    (hH0 : gibbsEntropy D (selectedLaw P X 0) < ⊤) :
    cep_EntropyConcl P D T X ∧ SolvesSelectedFKE D T (selectedLaw P X) := by
  refine ⟨?_, cep_H1_fke hN hs hβ hM hV hT hX₀ hdist hW hind hX hF⟩
  classical
  have hXm : ∀ t : ℝ≥0, Measurable (X t) := hX.toContact.adapted
  have hCm : ∀ σ : h5Idx N, MeasurableSet (h5Comp σ.1) := fun σ => (h5Comp_isOpen σ.1).measurableSet
  have hcollm : MeasurableSet (collisionSet 1 N) := (isClosed_collisionSet 1 N).measurableSet
  set A : h5Idx N → Set Ω := fun σ => X₀ ⁻¹' h5Comp σ.1 with hA
  have hAm : ∀ σ, MeasurableSet (A σ) := fun σ => hX₀ (hCm σ)
  have hPne : ∀ σ, P (A σ) ≠ ⊤ := fun σ => measure_ne_top P _
  set p : h5Idx N → ℝ := fun σ => (P (A σ)).toReal with hp
  have hp0 : ∀ σ, 0 ≤ p σ := fun σ => ENNReal.toReal_nonneg
  have hpne : ∀ σ, p σ ≠ 0 ↔ P (A σ) ≠ 0 := by
    intro σ
    simp only [hp, ne_eq, ENNReal.toReal_eq_zero_iff, hPne σ, or_false]
  have hsum1 : ∑ σ, p σ = 1 := by
    have hdisj : Pairwise (Function.onFun Disjoint A) := by
      intro σ σ' h
      exact (h5Comp_disjoint h).preimage X₀
    have hcov : (⋃ σ, A σ) = X₀ ⁻¹' (collisionSet 1 N)ᶜ := by
      rw [← h5Comp_iUnion]; simp only [hA, Set.preimage_iUnion]
    have hP1 : P (⋃ σ, A σ) = 1 := by
      rw [hcov, Set.preimage_compl]
      refine (prob_compl_eq_one_iff (hX₀ hcollm)).2 ?_
      exact measure_eq_zero_iff_ae_notMem.mpr hdist
    have h2 : (∑ σ, P (A σ)) = 1 := by
      have h4 := measure_biUnion_finset (μ := P) (s := Finset.univ) (f := A)
        (fun i _ j _ h => hdisj h) (fun i _ => hAm i)
      simp only [Finset.mem_univ, Set.iUnion_true] at h4
      rw [← h4, hP1]
    have h3 := congrArg ENNReal.toReal h2
    rw [ENNReal.toReal_sum (fun σ _ => hPne σ)] at h3
    simpa using h3
  -- laws are probability measures
  have hsl : ∀ (Q : Measure Ω) [IsProbabilityMeasure Q] (t : ℝ), IsProbabilityMeasure (selectedLaw Q X t) :=
    fun Q _ t => (Measure.isProbabilityMeasure_map_iff (hXm _).aemeasurable).2 inferInstance
  have hQprob : ∀ σ, P (A σ) ≠ 0 → IsProbabilityMeasure (ProbabilityTheory.cond P (A σ)) :=
    fun σ hσ => cond_isProbabilityMeasure_of_finite hσ (hPne σ)
  have hνprob : ∀ (t : ℝ) (σ : h5Idx N), IsProbabilityMeasure (h5Nu P X₀ X t σ) := by
    intro t σ
    by_cases h : P (A σ) = 0
    · simp only [h5Nu, hA] at h ⊢
      rw [if_pos h]; infer_instance
    · simp only [h5Nu, hA] at h ⊢
      rw [if_neg h]
      haveI := hQprob σ h
      exact hsl _ t
  -- the mixture decomposition
  have hmix : ∀ t : ℝ, selectedLaw P X t = ∑ σ, ENNReal.ofReal (p σ) • h5Nu P X₀ X t σ := by
    intro t
    rw [h5_selectedLaw_mixture hX₀ hdist t (hXm _)]
    refine Finset.sum_congr rfl fun σ _ => ?_
    by_cases h : P (A σ) = 0
    · have : p σ = 0 := by simp [hp, h]
      have h0 : (P (X₀ ⁻¹' h5Comp σ.1)).toReal = 0 := by
        rw [show P (X₀ ⁻¹' h5Comp σ.1) = 0 from h]; simp
      simp only [this, h0, ENNReal.ofReal_zero, zero_smul]
    · simp only [h5Nu, hA] at h ⊢
      rw [if_neg h]
  -- Fisher information and entropy of the mixture (H0)
  have hH0t : ∀ t : ℝ, (∀ σ, h5Nu P X₀ X t σ (h5Comp σ.1)ᶜ = 0) →
      fisherInfo D N (selectedLaw P X t) = ∑ σ, ENNReal.ofReal (p σ) * fisherInfo D N (h5Nu P X₀ X t σ) ∧
      gibbsEntropy D (selectedLaw P X t) = ∑ σ, ((p σ : ℝ) : EReal) * gibbsEntropy D (h5Nu P X₀ X t σ)
        + ∑ σ, (((p σ * Real.log (p σ)) : ℝ) : EReal) := by
    intro t hsupp
    haveI : ∀ σ, IsProbabilityMeasure (h5Nu P X₀ X t σ) := hνprob t
    rw [hmix t]
    exact cep_H0_component_additivity (fun σ : h5Idx N => h5Comp σ.1) (fun σ => h5Comp_isOpen σ.1)
      h5Comp_disjoint h5Comp_iUnion (fun σ => h5Nu P X₀ X t σ) hsupp p hp0 hsum1
  have hc : ∑ σ, (((p σ * Real.log (p σ)) : ℝ) : EReal) = ((∑ σ, p σ * Real.log (p σ) : ℝ) : EReal) :=
    h5_coe_sum _ _
  -- support at time 0
  have hinit : ∀ᵐ ω ∂P, X 0 ω = X₀ ω := hX.toContact.init
  have hsupp0 : ∀ σ, h5Nu P X₀ X 0 σ (h5Comp σ.1)ᶜ = 0 := by
    intro σ
    by_cases h : P (A σ) = 0
    · simp only [h5Nu, hA] at h ⊢
      rw [if_pos h, Measure.dirac_apply' _ (hCm σ).compl]
      have := Classical.choose_spec (h5Comp_nonempty σ)
      simp [Set.indicator, this]
    · simp only [h5Nu, hA] at h ⊢
      rw [if_neg h, selectedLaw, Measure.map_apply (hXm _) (hCm σ).compl]
      have hac : ProbabilityTheory.cond P (X₀ ⁻¹' h5Comp σ.1) ≪ P := cond_absolutelyContinuous
      have h1 := hac.ae_le hinit
      have h2 := ae_cond_mem (μ := P) (hAm σ)
      refine ae_iff.mp ?_
      filter_upwards [h1, h2] with ω h1 h2
      show X (Real.toNNReal 0) ω ∈ h5Comp σ.1
      rw [Real.toNNReal_zero, h1]; exact h2
  -- finite conditional entropies at time 0
  have hfin0 : ∀ σ, P (A σ) ≠ 0 →
      gibbsEntropy D (selectedLaw (ProbabilityTheory.cond P (A σ)) X 0) < ⊤ := by
    intro σ hσ
    have h := (hH0t 0 hsupp0).2
    rw [h, hc] at hH0
    have := h5_components_lt_top p hp0 (fun σ => gibbsEntropy D (h5Nu P X₀ X 0 σ))
      (fun σ => h5_gibbsEntropy_ne_bot D _) _ (EReal.coe_ne_bot _) (EReal.coe_ne_top _) hH0 σ ((hpne σ).2 hσ)
    simp only [h5Nu] at this
    rwa [if_neg (show ¬ P (X₀ ⁻¹' h5Comp σ.1) = 0 from hσ)] at this
  -- entropy inequality on each (good) component, by H4 under the conditional measure
  have hH4 : ∀ σ : h5Idx N, P (A σ) ≠ 0 →
      cep_EntropyConcl (ProbabilityTheory.cond P (A σ)) D T X := by
    intro σ hσ
    haveI := hQprob σ hσ
    have hac : ProbabilityTheory.cond P (A σ) ≪ P := cond_absolutelyContinuous
    have hdist' : ∀ᵐ ω ∂(ProbabilityTheory.cond P (A σ)), X₀ ω ∉ collisionSet 1 N := hac.ae_le hdist
    have hcomp : ∀ᵐ ω ∂(ProbabilityTheory.cond P (A σ)),
        ∃ y : Fin N → Euc 1, (fun i => Torus.mk (y i)) = X₀ ω ∧ cep_StrictlyOrdered σ.1 y := by
      filter_upwards [ae_cond_mem (μ := P) (hAm σ)] with ω hω
      exact hω
    obtain ⟨ℱ', hF'⟩ := h5_cond_filtered hX₀ hinit hF (hCm σ) hσ
    haveI := hsl (ProbabilityTheory.cond P (A σ)) 0
    have hdens0' : HasSelectedDensity (ProbabilityTheory.cond P (A σ)) X 0 :=
      cep_H4a_density_of_entropy hβ _ (hfin0 σ hσ)
    exact cep_H4_single_component hN hs hβ hM hV hT hX₀ hdist' σ.1 hcomp
      (h5_cond_brownian hX₀ hW hind (hCm σ) hσ) (h5_cond_indep hX₀ hind (hCm σ) hσ)
      (h5_flow_of_ac hac hX) hF' hdens0' (hfin0 σ hσ)
  -- support of the conditional laws on `[0,T]`
  have hsuppT : ∀ σ : h5Idx N, ∀ t ∈ Set.Icc (0 : ℝ) T,
      h5Nu P X₀ X t σ (h5Comp σ.1)ᶜ = 0 := by
    intro σ t ht
    by_cases h : P (A σ) = 0
    · simp only [h5Nu, hA] at h ⊢
      rw [if_pos h, Measure.dirac_apply' _ (hCm σ).compl]
      have := Classical.choose_spec (h5Comp_nonempty σ)
      simp [Set.indicator, this]
    · have hdens := (hH4 σ h t ht).1
      simp only [h5Nu, hA] at h ⊢
      rw [if_neg h]
      have hac : ProbabilityTheory.cond P (X₀ ⁻¹' h5Comp σ.1) ≪ P := cond_absolutelyContinuous
      have hnull : selectedLaw (ProbabilityTheory.cond P (X₀ ⁻¹' h5Comp σ.1)) X t (collisionSet 1 N) = 0 :=
        hdens (b15_volume_collisionSet (d := 1) (N := N) le_rfl)
      rw [selectedLaw, Measure.map_apply (hXm _) hcollm] at hnull
      have hae1 := measure_eq_zero_iff_ae_notMem.mp hnull
      have hae2 : ∀ᵐ ω ∂(ProbabilityTheory.cond P (X₀ ⁻¹' h5Comp σ.1)),
          X (Real.toNNReal t) ω ∈ h5Comp σ.1 := by
        have h1 := hac.ae_le (h5_class_constancy hX)
        filter_upwards [h1, ae_cond_mem (μ := P) (hAm σ), hae1] with ω h1 h2 h3
        refine h1 σ h2 (Real.toNNReal t) ?_ h3
        rw [Real.coe_toNNReal t ht.1]; exact ht.2
      rw [selectedLaw, Measure.map_apply (hXm _) (hCm σ).compl]
      exact ae_iff.mp hae2
  -- measurability of the component Fisher informations in time
  have hfm : ∀ σ : h5Idx N, Measurable fun r : ℝ => fisherInfo D N (h5Nu P X₀ X r σ) := by
    intro σ
    by_cases h : P (A σ) = 0
    · have : (fun r : ℝ => fisherInfo D N (h5Nu P X₀ X r σ)) =
          fun _ => fisherInfo D N (Measure.dirac (Classical.choose (h5Comp_nonempty σ))) := by
        funext r; simp only [h5Nu, hA] at h ⊢; rw [if_pos h]
      rw [this]; exact measurable_const
    · haveI := hQprob σ h
      have hac : ProbabilityTheory.cond P (A σ) ≪ P := cond_absolutelyContinuous
      have := h5_fisher_measurable (Q := ProbabilityTheory.cond P (A σ)) D (ContDiff.of_le hV (by norm_num)) hXm
        (hac.ae_le hX.toContact.cont)
      simp only [h5Nu, hA] at h ⊢
      simpa [if_neg h] using this
  intro t ht
  have hsupp_all : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ σ, h5Nu P X₀ X r σ (h5Comp σ.1)ᶜ = 0 :=
    fun r hr σ => hsuppT σ r hr
  -- density
  have hdens : HasSelectedDensity P X t := by
    unfold HasSelectedDensity
    rw [hmix t]
    intro S hS
    rw [Measure.coe_finset_sum, Finset.sum_apply]
    refine Finset.sum_eq_zero fun σ _ => ?_
    by_cases h : P (A σ) = 0
    · have h0 : ENNReal.ofReal (p σ) = 0 := by simp [hp, h]
      rw [h0]; simp
    · have h1 := (hH4 σ h t ht).1
      have : h5Nu P X₀ X t σ = selectedLaw (ProbabilityTheory.cond P (A σ)) X t := by
        simp only [h5Nu, hA] at h ⊢; rw [if_neg h]
      rw [this]
      simp [h1 hS]
  refine ⟨hdens, ?_⟩
  -- the inequality
  have hIcc : ∀ r ∈ Set.Icc (0 : ℝ) t, r ∈ Set.Icc (0 : ℝ) T := fun r hr => ⟨hr.1, hr.2.trans ht.2⟩
  have hfisher : (∫⁻ r in Set.Icc (0 : ℝ) t, fisherInfo D N (selectedLaw P X r)) =
      ∑ σ, ENNReal.ofReal (p σ) * ∫⁻ r in Set.Icc (0 : ℝ) t, fisherInfo D N (h5Nu P X₀ X r σ) := by
    rw [setLIntegral_congr_fun measurableSet_Icc
      (g := fun r => ∑ σ, ENNReal.ofReal (p σ) * fisherInfo D N (h5Nu P X₀ X r σ))
      (fun r hr => (hH0t r (hsupp_all r (hIcc r hr))).1)]
    rw [lintegral_finset_sum']
    · exact Finset.sum_congr rfl fun σ _ =>
        lintegral_const_mul'' _ (hfm σ).aemeasurable
    · intro σ _
      exact ((hfm σ).const_mul _).aemeasurable
  have hF' : ENNReal.ofReal D.invβ * ∫⁻ r in Set.Icc (0 : ℝ) t, fisherInfo D N (selectedLaw P X r) =
      ∑ σ, ENNReal.ofReal (p σ) *
        (ENNReal.ofReal D.invβ * ∫⁻ r in Set.Icc (0 : ℝ) t, fisherInfo D N (h5Nu P X₀ X r σ)) := by
    rw [hfisher, Finset.mul_sum]
    exact Finset.sum_congr rfl fun σ _ => mul_left_comm _ _ _
  rw [hF', (hH0t t (hsupp_all t ht)).2, (hH0t 0 hsupp0).2, hc]
  refine h5_recombine p hp0 (fun σ => gibbsEntropy D (h5Nu P X₀ X t σ))
    (fun σ => gibbsEntropy D (h5Nu P X₀ X 0 σ))
    (fun σ => ENNReal.ofReal D.invβ * ∫⁻ r in Set.Icc (0 : ℝ) t, fisherInfo D N (h5Nu P X₀ X r σ))
    (fun σ => h5_gibbsEntropy_ne_bot D _) (fun σ => h5_gibbsEntropy_ne_bot D _) ?_ _
    (EReal.coe_ne_bot _) (EReal.coe_ne_top _)
  intro σ hσ
  have hg : P (A σ) ≠ 0 := (hpne σ).1 hσ
  have hFin := (hH4 σ hg t ht).2
  have hnu : ∀ r : ℝ, h5Nu P X₀ X r σ = selectedLaw (ProbabilityTheory.cond P (A σ)) X r := by
    intro r
    simp only [h5Nu, hA] at hg ⊢
    rw [if_neg hg]
  simp only [hnu]
  exact ⟨hfin0 σ hg, hFin⟩

/-- The assembled statement is literally the one of `cep_H5_entropy_confined`. -/
example := (@cep_H5_assembly : type_of% @HRS.MC.Cepa.cep_H5_entropy_confined)

end Assembly

end HRS.MC.CepH5

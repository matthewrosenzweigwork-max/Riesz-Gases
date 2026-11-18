import HRS.MS.MovLinAux4
import HRS.MS.MovLinAux6

/-!
# MOV-2d, part 1: function-level operators as bounded operators on the scale `OscSpace d r`

Namespace `HRS.MS.MovLin`, helpers `mov2d_`.  Infrastructure for S6.2 (`W:lem:r2mov-linear`); not a manuscript row.

The scale `X r = OscSpace d r` (`ℓ²` with the weights `λ_α^{r/2}`; every real `r`, also negative, where the elements are
distributions, not functions).  A *function-level* operator `A : (ℝ^d → ℝ) → (ℝ^d → ℝ)` that is coefficientwise linear
and bounded `Σ^ρ → Σ^σ` on the finite Hermite sums `mov2d_hs c` (`c : MultiIndex d →₀ ℝ`) extends uniquely to a
bounded operator `mov2d_op ρ σ A : OscSpace d ρ →L OscSpace d σ` (`LinearMap.extendOfNorm` along the dense
embedding of the finitely supported coefficient vectors).  This is the transport lemma between the function-level
objects (`mov_expS0`, `movP`, multiplication by `V_1`) and bundled continuous linear maps.

## Contents

* `mov2d_hs`, `Mov2dData`, `mov2d_op`: the construction (`mov2d_op_hs`: action on finite Hermite sums;
  `mov2d_op_norm_le`: operator norm; `mov2d_op_ext`: two bounded operators agreeing on all `ofFun (hs c)` coincide).
* `mov2d_op_apply_of_bdd`: if `A` is coefficientwise linear and bounded on all of `MemOsc ρ`, then
  `mov2d_op ρ σ A (ofFun ρ f) = ofFun σ (A f)` for every `f ∈ Σ^ρ` (not only finite sums).
* The embedding `j`, the semigroup `e^{-tS_0}` as bounded operators on the scale (`mov2d_Sm`), with strong
  continuity, semigroup law, zero, the smoothing bound for all `t ∈ (0, T0]`, and compatibility with `j`.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovLin

open HRS HRS.Whole HRS.MS.MovOsc

variable {d : ℕ}

/-! ## A. Finite Hermite sums -/

/-- `c ↦ ∑_α c_α h_α` for finitely supported `c`. -/
def mov2d_hs (d : ℕ) : (MultiIndex d →₀ ℝ) →ₗ[ℝ] (Euc d → ℝ) :=
  Finsupp.linearCombination ℝ (fun α : MultiIndex d => hermiteFunD α)

lemma mov2d_hs_eq (c : MultiIndex d →₀ ℝ) : mov2d_hs d c = mo_hsum c.support (⇑c) := by
  funext z
  simp [mov2d_hs, Finsupp.linearCombination_apply, Finsupp.sum, mo_hsum]

lemma mov2d_hs_coeff (c : MultiIndex d →₀ ℝ) (β : MultiIndex d) :
    hermiteCoeff (mov2d_hs d c) β = c β := by
  rw [mov2d_hs_eq, mova2_coeff_hsum]
  by_cases h : β ∈ c.support
  · simp [h]
  · simp only [h, ite_false]
    exact (Finsupp.notMem_support_iff.1 h).symm

lemma mov2d_hs_memOsc (r : ℝ) (c : MultiIndex d →₀ ℝ) : MemOsc r (mov2d_hs d c) := by
  rw [mov2d_hs_eq]; exact mo_hsum_memOsc r _ _

lemma mov2d_hs_add (c c' : MultiIndex d →₀ ℝ) :
    mov2d_hs d (c + c') = fun z => mov2d_hs d c z + mov2d_hs d c' z := by
  funext z; simp

lemma mov2d_hs_smul (a : ℝ) (c : MultiIndex d →₀ ℝ) :
    mov2d_hs d (a • c) = fun z => a * mov2d_hs d c z := by
  funext z; simp

lemma mov2d_hs_sum (S : Finset (MultiIndex d)) (a : MultiIndex d → ℝ) :
    mov2d_hs d (∑ α ∈ S, Finsupp.single α (a α)) = mo_hsum S a := by
  funext z
  simp [mov2d_hs, mo_hsum, map_sum, Finsupp.linearCombination_single]

/-! ## B. `ofFun` calculus -/

lemma mov2d_coord_add {m : ℝ} (x y : OscSpace d m) (α : MultiIndex d) :
    OscSpace.coord (x + y) α = OscSpace.coord x α + OscSpace.coord y α := rfl

lemma mov2d_coord_smul {m : ℝ} (a : ℝ) (x : OscSpace d m) (α : MultiIndex d) :
    OscSpace.coord (a • x) α = a * OscSpace.coord x α := rfl

lemma mov2d_coord_sub {m : ℝ} (x y : OscSpace d m) (α : MultiIndex d) :
    OscSpace.coord (x - y) α = OscSpace.coord x α - OscSpace.coord y α := rfl

lemma mov2d_ofFun_ext {m : ℝ} {f g : Euc d → ℝ} (hf : MemOsc m f) (hg : MemOsc m g)
    (h : ∀ α, hermiteCoeff f α = hermiteCoeff g α) : OscSpace.ofFun m f = OscSpace.ofFun m g := by
  rw [OscSpace.ofFun_eq hf, OscSpace.ofFun_eq hg]
  apply lp.ext
  funext α
  change oscEigenvalue d α ^ (m / 2) * hermiteCoeff f α = oscEigenvalue d α ^ (m / 2) * hermiteCoeff g α
  rw [h α]

lemma mov2d_ofFun_ae {m : ℝ} {f g : Euc d → ℝ} (hf : MemOsc m f) (h : f =ᵐ[volume] g) :
    OscSpace.ofFun m f = OscSpace.ofFun m g :=
  mov2d_ofFun_ext hf (mov2b_memOsc_congr h m hf) (mov2b_hermiteCoeff_congr h)

lemma mov2d_ofFun_add {m : ℝ} {f g : Euc d → ℝ} (hf : MemOsc m f) (hg : MemOsc m g) :
    OscSpace.ofFun m (fun z => f z + g z) = OscSpace.ofFun m f + OscSpace.ofFun m g := by
  have hfg := (HRS.MS.MovC1.movc1_osc_add m hf hg).1
  rw [OscSpace.ofFun_eq hfg, OscSpace.ofFun_eq hf, OscSpace.ofFun_eq hg]
  apply lp.ext
  funext α
  change oscEigenvalue d α ^ (m / 2) * hermiteCoeff (fun x => f x + g x) α =
    oscEigenvalue d α ^ (m / 2) * hermiteCoeff f α + oscEigenvalue d α ^ (m / 2) * hermiteCoeff g α
  rw [HRS.MS.MovC1.movc1_coeff_add hf.1 hg.1]; ring

lemma mov2d_ofFun_smul {m : ℝ} (a : ℝ) {f : Euc d → ℝ} (hf : MemOsc m f) :
    OscSpace.ofFun m (fun z => a * f z) = a • OscSpace.ofFun m f := by
  have hfa := (HRS.MS.MovC1.movc1_osc_smul m a hf).1
  rw [OscSpace.ofFun_eq hfa, OscSpace.ofFun_eq hf]
  apply lp.ext
  funext α
  change oscEigenvalue d α ^ (m / 2) * hermiteCoeff (fun x => a * f x) α =
    a * (oscEigenvalue d α ^ (m / 2) * hermiteCoeff f α)
  rw [HRS.MS.MovC1.movc1_coeff_smul]; ring

lemma mov2d_ofFun_sub {m : ℝ} {f g : Euc d → ℝ} (hf : MemOsc m f) (hg : MemOsc m g) :
    OscSpace.ofFun m (fun z => f z - g z) = OscSpace.ofFun m f - OscSpace.ofFun m g := by
  have h1 := (HRS.MS.MovC1.movc1_osc_smul m (-1) hg)
  have h2 := mov2d_ofFun_add hf h1.1
  have h3 : (fun z => f z - g z) = fun z => f z + (-1 : ℝ) * g z := by funext z; ring
  rw [h3, h2, mov2d_ofFun_smul (-1) hg]
  simp [sub_eq_add_neg]

lemma mov2d_memOsc_sub {m : ℝ} {f g : Euc d → ℝ} (hf : MemOsc m f) (hg : MemOsc m g) :
    MemOsc m (fun z => f z - g z) := by
  have h1 := (HRS.MS.MovC1.movc1_osc_smul m (-1) hg).1
  have h3 : (fun z => f z - g z) = fun z => f z + (-1 : ℝ) * g z := by funext z; ring
  rw [h3]; exact (HRS.MS.MovC1.movc1_osc_add m hf h1).1

/-! ## C. The construction of bounded operators from function-level data -/

/-- Coefficientwise linear function-level operator, bounded `Σ^ρ → Σ^σ` with constant `C` on finite Hermite sums. -/
def Mov2dData (ρ σ : ℝ) (A : (Euc d → ℝ) → Euc d → ℝ) (C : ℝ) : Prop :=
  (∀ c : MultiIndex d →₀ ℝ, MemOsc σ (A (mov2d_hs d c)) ∧
      oscNorm σ (A (mov2d_hs d c)) ≤ C * oscNorm ρ (mov2d_hs d c)) ∧
    (∀ c c' : MultiIndex d →₀ ℝ, ∀ α, hermiteCoeff (A (fun z => mov2d_hs d c z + mov2d_hs d c' z)) α =
      hermiteCoeff (A (mov2d_hs d c)) α + hermiteCoeff (A (mov2d_hs d c')) α) ∧
    (∀ (a : ℝ) (c : MultiIndex d →₀ ℝ), ∀ α, hermiteCoeff (A (fun z => a * mov2d_hs d c z)) α =
      a * hermiteCoeff (A (mov2d_hs d c)) α)

/-- The linear map `c ↦ ofFun σ (A (hs c))`. -/
def mov2d_lin {ρ σ : ℝ} {A : (Euc d → ℝ) → Euc d → ℝ} {C : ℝ} (h : Mov2dData ρ σ A C) :
    (MultiIndex d →₀ ℝ) →ₗ[ℝ] OscSpace d σ where
  toFun c := OscSpace.ofFun σ (A (mov2d_hs d c))
  map_add' c c' := by
    have e : OscSpace.ofFun σ (A (mov2d_hs d (c + c'))) =
        OscSpace.ofFun σ (fun z => A (mov2d_hs d c) z + A (mov2d_hs d c') z) := by
      refine mov2d_ofFun_ext (h.1 (c + c')).1 (HRS.MS.MovC1.movc1_osc_add σ (h.1 c).1 (h.1 c').1).1 ?_
      intro α
      rw [mov2d_hs_add, h.2.1 c c' α, HRS.MS.MovC1.movc1_coeff_add (h.1 c).1.1 (h.1 c').1.1]
    rw [e, mov2d_ofFun_add (h.1 c).1 (h.1 c').1]
  map_smul' a c := by
    have e : OscSpace.ofFun σ (A (mov2d_hs d (a • c))) =
        OscSpace.ofFun σ (fun z => a * A (mov2d_hs d c) z) := by
      refine mov2d_ofFun_ext (h.1 (a • c)).1 (HRS.MS.MovC1.movc1_osc_smul σ a (h.1 c).1).1 ?_
      intro α
      rw [mov2d_hs_smul, h.2.2 a c α, HRS.MS.MovC1.movc1_coeff_smul]
    rw [e, mov2d_ofFun_smul a (h.1 c).1]
    rfl

lemma mov2d_lin_apply {ρ σ : ℝ} {A : (Euc d → ℝ) → Euc d → ℝ} {C : ℝ} (h : Mov2dData ρ σ A C)
    (c : MultiIndex d →₀ ℝ) : mov2d_lin h c = OscSpace.ofFun σ (A (mov2d_hs d c)) := rfl

lemma mov2d_id_data (ρ : ℝ) : Mov2dData (d := d) ρ ρ (fun f => f) 1 := by
  refine ⟨fun c => ⟨mov2d_hs_memOsc ρ c, by rw [one_mul]⟩, fun c c' α => ?_, fun a c α => ?_⟩
  · exact HRS.MS.MovC1.movc1_coeff_add (mov2d_hs_memOsc ρ c).1 (mov2d_hs_memOsc ρ c').1 α
  · exact HRS.MS.MovC1.movc1_coeff_smul a _ α

/-- The dense embedding of the finitely supported coefficient vectors into `OscSpace d ρ`
(`c ↦ ofFun ρ (∑ c_α h_α)`). -/
def mov2d_e (d : ℕ) (ρ : ℝ) : (MultiIndex d →₀ ℝ) →ₗ[ℝ] OscSpace d ρ :=
  mov2d_lin (mov2d_id_data (d := d) ρ)

lemma mov2d_e_apply (ρ : ℝ) (c : MultiIndex d →₀ ℝ) :
    mov2d_e d ρ c = OscSpace.ofFun ρ (mov2d_hs d c) := rfl

lemma mov2d_e_norm (ρ : ℝ) (c : MultiIndex d →₀ ℝ) : ‖mov2d_e d ρ c‖ = oscNorm ρ (mov2d_hs d c) := by
  rw [mov2d_e_apply, OscSpace.norm_ofFun _ (mov2d_hs_memOsc ρ c)]

lemma mov2d_coord_e (ρ : ℝ) (c : MultiIndex d →₀ ℝ) (α : MultiIndex d) :
    OscSpace.coord (mov2d_e d ρ c) α = oscEigenvalue d α ^ (ρ / 2) * c α := by
  rw [mov2d_e_apply, OscSpace.coord_ofFun _ (mov2d_hs_memOsc ρ c), mov2d_hs_coeff]

/-- Density of the finitely supported vectors. -/
lemma mov2d_e_dense (ρ : ℝ) : DenseRange (mov2d_e d ρ) := by
  intro x
  set xl : lp (fun _ : MultiIndex d => ℝ) 2 := x with hxl
  have hS : HasSum (fun i : MultiIndex d => lp.single 2 i (xl i)) xl :=
    lp.hasSum_single (E := fun _ : MultiIndex d => ℝ) (p := 2) (by simp) xl
  have hT : Tendsto (fun F : Finset (MultiIndex d) => ∑ i ∈ F, lp.single 2 i (xl i)) atTop (𝓝 xl) := hS
  refine mem_closure_of_tendsto (b := atTop)
    (f := fun F : Finset (MultiIndex d) => (∑ i ∈ F, lp.single 2 i (xl i) : OscSpace d ρ)) hT
    (Eventually.of_forall fun F => ?_)
  refine ⟨∑ α ∈ F, Finsupp.single α (oscEigenvalue d α ^ (-(ρ / 2)) * xl α), ?_⟩
  show mov2d_e d ρ _ = (∑ i ∈ F, lp.single 2 i (xl i) : lp (fun _ : MultiIndex d => ℝ) 2)
  apply lp.ext
  funext β
  change OscSpace.coord (mov2d_e d ρ _) β = _
  rw [mov2d_coord_e, lp.coeFn_sum]
  simp only [Finset.sum_apply, lp.coeFn_single, Finsupp.coe_finsetSum, Finsupp.single_apply,
    Finset.sum_pi_single, Finset.sum_ite_eq']
  by_cases hβ : β ∈ F
  · simp only [hβ, ite_true]
    have h := oscEv_pos (d := d) β
    rw [← mul_assoc, ← Real.rpow_add h]
    simp
  · simp [hβ]

lemma mov2d_data_of_ae {ρ σ : ℝ} {A : (Euc d → ℝ) → Euc d → ℝ} {C : ℝ}
    (hb : ∀ c : MultiIndex d →₀ ℝ, MemOsc σ (A (mov2d_hs d c)) ∧
      oscNorm σ (A (mov2d_hs d c)) ≤ C * oscNorm ρ (mov2d_hs d c))
    (hadd : ∀ c c' : MultiIndex d →₀ ℝ, A (fun z => mov2d_hs d c z + mov2d_hs d c' z) =ᵐ[volume]
      fun z => A (mov2d_hs d c) z + A (mov2d_hs d c') z)
    (hsm : ∀ (a : ℝ) (c : MultiIndex d →₀ ℝ), A (fun z => a * mov2d_hs d c z) =ᵐ[volume]
      fun z => a * A (mov2d_hs d c) z) : Mov2dData ρ σ A C := by
  refine ⟨hb, fun c c' α => ?_, fun a c α => ?_⟩
  · rw [mov2b_hermiteCoeff_congr (hadd c c') α,
      HRS.MS.MovC1.movc1_coeff_add (hb c).1.1 (hb c').1.1]
  · rw [mov2b_hermiteCoeff_congr (hsm a c) α, HRS.MS.MovC1.movc1_coeff_smul]

open Classical in
/-- The bounded operator `OscSpace d ρ →L OscSpace d σ` generated by the function-level operator `A`
(`0` if `A` does not satisfy `Mov2dData` for any constant). -/
def mov2d_op (ρ σ : ℝ) (A : (Euc d → ℝ) → Euc d → ℝ) : OscSpace d ρ →L[ℝ] OscSpace d σ :=
  if h : ∃ C, Mov2dData ρ σ A C then (mov2d_lin h.choose_spec).extendOfNorm (mov2d_e d ρ) else 0

lemma mov2d_lin_bound {ρ σ : ℝ} {A : (Euc d → ℝ) → Euc d → ℝ} {C : ℝ} (h : Mov2dData ρ σ A C)
    (c : MultiIndex d →₀ ℝ) : ‖mov2d_lin h c‖ ≤ C * ‖mov2d_e d ρ c‖ := by
  rw [mov2d_lin_apply, OscSpace.norm_ofFun _ (h.1 c).1, mov2d_e_norm]
  exact (h.1 c).2

lemma mov2d_op_eq {ρ σ : ℝ} {A : (Euc d → ℝ) → Euc d → ℝ} {C : ℝ} (h : Mov2dData ρ σ A C) :
    mov2d_op ρ σ A = (mov2d_lin h).extendOfNorm (mov2d_e d ρ) := by
  have hex : ∃ C, Mov2dData ρ σ A C := ⟨C, h⟩
  unfold mov2d_op
  rw [dif_pos hex]
  have : mov2d_lin hex.choose_spec = mov2d_lin h := LinearMap.ext fun c => rfl
  rw [this]

/-- The action on finite Hermite sums. -/
lemma mov2d_op_hs {ρ σ : ℝ} {A : (Euc d → ℝ) → Euc d → ℝ} {C : ℝ} (h : Mov2dData ρ σ A C)
    (c : MultiIndex d →₀ ℝ) :
    mov2d_op ρ σ A (OscSpace.ofFun ρ (mov2d_hs d c)) = OscSpace.ofFun σ (A (mov2d_hs d c)) := by
  rw [mov2d_op_eq h]
  have := LinearMap.extendOfNorm_eq (f := mov2d_lin h) (e := mov2d_e d ρ) (mov2d_e_dense ρ)
    ⟨C, mov2d_lin_bound h⟩ c
  rw [mov2d_e_apply] at this
  rw [this]; rfl

lemma mov2d_op_norm_apply_le {ρ σ : ℝ} {A : (Euc d → ℝ) → Euc d → ℝ} {C : ℝ} (h : Mov2dData ρ σ A C)
    (x : OscSpace d ρ) : ‖mov2d_op ρ σ A x‖ ≤ C * ‖x‖ := by
  rw [mov2d_op_eq h]
  exact LinearMap.norm_extendOfNorm_apply_le (mov2d_e_dense ρ) C (mov2d_lin_bound h) x

lemma mov2d_op_norm_le {ρ σ : ℝ} {A : (Euc d → ℝ) → Euc d → ℝ} {C : ℝ} (h : Mov2dData ρ σ A C)
    (hC : 0 ≤ C) : ‖mov2d_op ρ σ A‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC (mov2d_op_norm_apply_le h)

/-- Two bounded operators on `OscSpace d ρ` that agree on all finite Hermite sums coincide. -/
lemma mov2d_ext {ρ : ℝ} {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {E₁ E₂ : OscSpace d ρ →L[ℝ] Z}
    (h : ∀ c : MultiIndex d →₀ ℝ, E₁ (OscSpace.ofFun ρ (mov2d_hs d c)) = E₂ (OscSpace.ofFun ρ (mov2d_hs d c))) :
    E₁ = E₂ := by
  have := (mov2d_e_dense ρ).equalizer E₁.continuous E₂.continuous (funext fun c => h c)
  exact DFunLike.coe_injective this

/-- If `A` is coefficientwise linear and bounded on all of `Σ^ρ`, the operator acts as `A` on every `f ∈ Σ^ρ`. -/
lemma mov2d_op_apply_of_bdd {ρ σ : ℝ} {A : (Euc d → ℝ) → Euc d → ℝ} {C : ℝ} (h : Mov2dData ρ σ A C)
    {K : ℝ} (hb : ∀ f : Euc d → ℝ, MemOsc ρ f → MemOsc σ (A f) ∧ oscNorm σ (A f) ≤ K * oscNorm ρ f)
    (hl : ∀ f g : Euc d → ℝ, MemLp f 2 (volume : Measure (Euc d)) → MemLp g 2 (volume : Measure (Euc d)) →
      ∀ α, hermiteCoeff (A (fun z => f z - g z)) α = hermiteCoeff (A f) α - hermiteCoeff (A g) α)
    {f : Euc d → ℝ} (hf : MemOsc ρ f) :
    mov2d_op ρ σ A (OscSpace.ofFun ρ f) = OscSpace.ofFun σ (A f) := by
  have hgc : ∀ n, mo_pSum f n =
      mov2d_hs d (∑ α ∈ mova2_S d n, Finsupp.single α (hermiteCoeff f α)) := fun n => by
    rw [mov2d_hs_sum]; rfl
  have hgm : ∀ n, MemOsc ρ (mo_pSum f n) := fun n => mo_hsum_memOsc ρ _ _
  have h1 : Tendsto (fun n => OscSpace.ofFun ρ (mo_pSum f n)) atTop (𝓝 (OscSpace.ofFun ρ f)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have e : ∀ n, ‖OscSpace.ofFun ρ (mo_pSum f n) - OscSpace.ofFun ρ f‖ =
        oscNorm ρ (fun x => f x - mo_pSum f n x) := by
      intro n
      rw [norm_sub_rev, ← mov2d_ofFun_sub hf (hgm n),
        OscSpace.norm_ofFun _ (mov2d_memOsc_sub hf (hgm n))]
    simp_rw [e]
    exact mo_hsum_tail ρ hf
  have h2 : Tendsto (fun n => mov2d_op ρ σ A (OscSpace.ofFun ρ (mo_pSum f n))) atTop
      (𝓝 (mov2d_op ρ σ A (OscSpace.ofFun ρ f))) := ((mov2d_op ρ σ A).continuous.tendsto _).comp h1
  have h3 : Tendsto (fun n => mov2d_op ρ σ A (OscSpace.ofFun ρ (mo_pSum f n))) atTop
      (𝓝 (OscSpace.ofFun σ (A f))) := by
    have e : ∀ n, mov2d_op ρ σ A (OscSpace.ofFun ρ (mo_pSum f n)) =
        OscSpace.ofFun σ (A (mo_pSum f n)) := fun n => by
      rw [hgc n]; exact mov2d_op_hs h _
    simp_rw [e]
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hAg : ∀ n, MemOsc σ (A (mo_pSum f n)) := fun n => by rw [hgc n]; exact (h.1 _).1
    have hAf : MemOsc σ (A f) := (hb f hf).1
    have e2 : ∀ n, ‖OscSpace.ofFun σ (A (mo_pSum f n)) - OscSpace.ofFun σ (A f)‖ ≤
        K * oscNorm ρ (fun x => f x - mo_pSum f n x) := by
      intro n
      rw [norm_sub_rev, ← mov2d_ofFun_sub hAf (hAg n)]
      have hbn := hb _ (mov2d_memOsc_sub hf (hgm n))
      have : OscSpace.ofFun σ (fun z => A f z - A (mo_pSum f n) z) =
          OscSpace.ofFun σ (A (fun z => f z - mo_pSum f n z)) :=
        mov2d_ofFun_ext (mov2d_memOsc_sub hAf (hAg n)) hbn.1 (fun α => by
          rw [mova2_coeff_sub hAf.1 (hAg n).1, hl f (mo_pSum f n) hf.1 (hgm n).1 α])
      rw [this, OscSpace.norm_ofFun _ hbn.1]
      exact hbn.2
    refine squeeze_zero (fun n => norm_nonneg _) e2 ?_
    simpa using (mo_hsum_tail ρ hf).const_mul K
  exact tendsto_nhds_unique h2 h3

/-! ## D. The embedding `j` -/

/-- The embedding `Σ^r → Σ^{r'}` (`r' ≤ r`) as a bounded operator on the scale. -/
def mov2d_j {r r' : ℝ} (_ : r' ≤ r) : OscSpace d r →L[ℝ] OscSpace d r' :=
  mov2d_op r r' (fun f => f)

lemma mov2d_j_data {r r' : ℝ} (h : r' ≤ r) : Mov2dData (d := d) r r' (fun f => f) 1 := by
  refine mov2d_data_of_ae (fun c => ?_) (fun c c' => Filter.EventuallyEq.rfl) (fun a c => Filter.EventuallyEq.rfl)
  obtain ⟨h1, h2⟩ := mo_mono h (mov2d_hs_memOsc r c)
  exact ⟨h1, by rw [one_mul]; exact h2⟩

lemma mov2d_j_ofFun {r r' : ℝ} (h : r' ≤ r) {f : Euc d → ℝ} (hf : MemOsc r f) :
    mov2d_j h (OscSpace.ofFun r f) = OscSpace.ofFun r' f := by
  unfold mov2d_j
  exact mov2d_op_apply_of_bdd (mov2d_j_data h) (K := 1)
    (fun f hf => by obtain ⟨h1, h2⟩ := mo_mono h hf; exact ⟨h1, by rw [one_mul]; exact h2⟩)
    (fun f g hf hg α => mova2_coeff_sub hf hg α) hf

lemma mov2d_j_norm_le {r r' : ℝ} (h : r' ≤ r) : ‖mov2d_j (d := d) h‖ ≤ 1 :=
  mov2d_op_norm_le (mov2d_j_data h) zero_le_one

/-! ## E. The semigroup `e^{-tS_0}` on the scale -/

section ExpS0

variable {β q : ℝ}

lemma mov2d_dcoeff_add (hβ : 0 < β) (hq : 0 < q) {f g : Euc d → ℝ}
    (hf : MemLp f 2 (volume : Measure (Euc d))) (hg : MemLp g 2 (volume : Measure (Euc d)))
    (α : MultiIndex d) :
    mov2b_dcoeff (mov_dil β q) (fun z => f z + g z) α =
      mov2b_dcoeff (mov_dil β q) f α + mov2b_dcoeff (mov_dil β q) g α := by
  have hl := mov_dil_pos hβ hq
  rw [mov2b_dcoeff_eq hl, mov2b_dcoeff_eq hl, mov2b_dcoeff_eq hl]
  have := HRS.MS.MovC1.movc1_coeff_add (mov2b_memLp_inv hl hf) (mov2b_memLp_inv hl hg) α
  rw [this]; ring

lemma mov2d_dcoeff_smul (hβ : 0 < β) (hq : 0 < q) (a : ℝ) (f : Euc d → ℝ) (α : MultiIndex d) :
    mov2b_dcoeff (mov_dil β q) (fun z => a * f z) α = a * mov2b_dcoeff (mov_dil β q) f α := by
  have hl := mov_dil_pos hβ hq
  rw [mov2b_dcoeff_eq hl, mov2b_dcoeff_eq hl]
  have := HRS.MS.MovC1.movc1_coeff_smul a (fun y => f ((mov_dil β q)⁻¹ • y)) α
  rw [this]; ring

/-- Linearity of `e^{-tS_0}` (a.e.): `A(a f + b g) = a A f + b A g`. -/
lemma mov2d_expS0_lin (hβ : 0 < β) (hq : 0 < q) {t : ℝ} (ht : 0 ≤ t) (a b : ℝ) {f g : Euc d → ℝ}
    (hf : MemLp f 2 (volume : Measure (Euc d))) (hg : MemLp g 2 (volume : Measure (Euc d))) :
    mov_expS0 β q t (fun z => a * f z + b * g z) =ᵐ[volume]
      fun z => a * mov_expS0 β q t f z + b * mov_expS0 β q t g z := by
  have haf : MemLp (fun z => a * f z) 2 (volume : Measure (Euc d)) := hf.const_mul a
  have hbg : MemLp (fun z => b * g z) 2 (volume : Measure (Euc d)) := hg.const_mul b
  have hfg : MemLp (fun z => a * f z + b * g z) 2 (volume : Measure (Euc d)) := haf.add hbg
  have hAf := mov_expS0_memLp hβ hq t f
  have hAg := mov_expS0_memLp hβ hq t g
  have hu : MemLp (fun z => a * mov_expS0 β q t f z + b * mov_expS0 β q t g z) 2
      (volume : Measure (Euc d)) := (hAf.const_mul a).add (hAg.const_mul b)
  have := mov_expS0_unique hβ hq ht hfg hu (fun α => by
    rw [mov2d_dcoeff_add hβ hq (hAf.const_mul a) (hAg.const_mul b), mov2d_dcoeff_smul hβ hq,
      mov2d_dcoeff_smul hβ hq, mov_expS0_dcoeff hβ hq ht hf, mov_expS0_dcoeff hβ hq ht hg,
      mov2d_dcoeff_add hβ hq haf hbg, mov2d_dcoeff_smul hβ hq, mov2d_dcoeff_smul hβ hq]
    ring)
  exact this.symm

lemma mov2d_expS0_coeff_sub (hβ : 0 < β) (hq : 0 < q) {t : ℝ} (ht : 0 ≤ t) {f g : Euc d → ℝ}
    (hf : MemLp f 2 (volume : Measure (Euc d))) (hg : MemLp g 2 (volume : Measure (Euc d)))
    (α : MultiIndex d) :
    hermiteCoeff (mov_expS0 β q t (fun z => f z - g z)) α =
      hermiteCoeff (mov_expS0 β q t f) α - hermiteCoeff (mov_expS0 β q t g) α := by
  have h := mov2d_expS0_lin hβ hq ht 1 (-1) hf hg
  have e1 : (fun z => (1 : ℝ) * f z + (-1 : ℝ) * g z) = fun z => f z - g z := by funext z; ring
  rw [e1] at h
  rw [mov2b_hermiteCoeff_congr h α]
  have hAf := mov_expS0_memLp hβ hq t f
  have hAg := mov_expS0_memLp hβ hq t g
  have e2 : (fun z => (1 : ℝ) * mov_expS0 β q t f z + (-1 : ℝ) * mov_expS0 β q t g z) =
      fun z => mov_expS0 β q t f z - mov_expS0 β q t g z := by funext z; ring
  rw [e2, mova2_coeff_sub hAf hAg]

/-- The bound for `e^{-tS_0} : Σ^ρ → Σ^σ`, uniform for `t ∈ (0, T0]`. -/
lemma mov2d_expS0_bdd_T0 (hβ : 0 < β) (hq : 0 < q) {ρ σ : ℝ} (hρσ : ρ ≤ σ) {T0 : ℝ} (hT0 : 0 < T0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → t ≤ T0 → ∀ f : Euc d → ℝ, MemOsc ρ f →
      MemOsc σ (mov_expS0 β q t f) ∧
        oscNorm σ (mov_expS0 β q t f) ≤ C * t ^ (-((σ - ρ) / 2)) * oscNorm ρ f := by
  obtain ⟨C0, hC0, h0⟩ := mov_expS0_bound (d := d) hβ hq ρ (σ - ρ) (sub_nonneg.2 hρσ)
  obtain ⟨Cs, hCs, hs⟩ := mov_expS0_bounded (d := d) hβ hq σ
  have e : ρ + (σ - ρ) = σ := by ring
  have hb1 : ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ f : Euc d → ℝ, MemOsc ρ f →
      MemOsc σ (mov_expS0 β q t f) ∧
        oscNorm σ (mov_expS0 β q t f) ≤ C0 * t ^ (-((σ - ρ) / 2)) * oscNorm ρ f := by
    intro t ht ht1 f hf
    have := h0 t ht ht1 f hf
    rw [e] at this
    exact this
  refine ⟨C0 + Cs * C0 * T0 ^ ((σ - ρ) / 2), by positivity, fun t ht htT f hf => ?_⟩
  by_cases ht1 : t ≤ 1
  · obtain ⟨m1, m2⟩ := hb1 t ht ht1 f hf
    refine ⟨m1, m2.trans ?_⟩
    have hp : 0 ≤ t ^ (-((σ - ρ) / 2)) := Real.rpow_nonneg ht.le _
    have hn : 0 ≤ oscNorm ρ f := Real.sqrt_nonneg _
    have : 0 ≤ Cs * C0 * T0 ^ ((σ - ρ) / 2) := by positivity
    nlinarith [mul_nonneg (mul_nonneg this hp) hn]
  · push_neg at ht1
    obtain ⟨n1, n2⟩ := hb1 1 one_pos le_rfl f hf
    have hadd := mov_expS0_add hβ hq (s := t - 1) (t := 1) (by linarith) zero_le_one hf.1
    rw [sub_add_cancel] at hadd
    obtain ⟨m1, m2⟩ := hs (t - 1) (by linarith) _ n1
    rw [hadd] at m1 m2
    refine ⟨m1, m2.trans ?_⟩
    rw [Real.one_rpow, mul_one] at n2
    have hb : 0 ≤ σ - ρ := sub_nonneg.2 hρσ
    have hT : 1 ≤ T0 ^ ((σ - ρ) / 2) * t ^ (-((σ - ρ) / 2)) := by
      have h1 : T0 ^ (-((σ - ρ) / 2)) ≤ t ^ (-((σ - ρ) / 2)) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) htT (by linarith)
      have h2 : T0 ^ ((σ - ρ) / 2) * T0 ^ (-((σ - ρ) / 2)) = 1 := by
        rw [← Real.rpow_add hT0]; simp
      calc (1 : ℝ) = T0 ^ ((σ - ρ) / 2) * T0 ^ (-((σ - ρ) / 2)) := h2.symm
        _ ≤ T0 ^ ((σ - ρ) / 2) * t ^ (-((σ - ρ) / 2)) :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hT0.le _)
    have hn : 0 ≤ oscNorm ρ f := Real.sqrt_nonneg _
    have hCC : 0 ≤ Cs * C0 := mul_nonneg hCs hC0
    calc Cs * oscNorm σ (mov_expS0 β q 1 f) ≤ Cs * (C0 * oscNorm ρ f) :=
          mul_le_mul_of_nonneg_left n2 hCs
      _ = (Cs * C0) * oscNorm ρ f := by ring
      _ ≤ (Cs * C0) * (T0 ^ ((σ - ρ) / 2) * t ^ (-((σ - ρ) / 2))) * oscNorm ρ f := by
          apply mul_le_mul_of_nonneg_right _ hn
          nlinarith [mul_le_mul_of_nonneg_left hT hCC]
      _ ≤ _ := by
          have hp : 0 ≤ t ^ (-((σ - ρ) / 2)) := Real.rpow_nonneg ht.le _
          have : 0 ≤ C0 * t ^ (-((σ - ρ) / 2)) * oscNorm ρ f := by positivity
          nlinarith [this]

/-- A bound for `e^{-tS_0} : Σ^ρ → Σ^σ` at a single time (`t > 0`, or `ρ = σ` and `t ≥ 0`). -/
lemma mov2d_expS0_bdd (hβ : 0 < β) (hq : 0 < q) {ρ σ : ℝ} (hρσ : ρ ≤ σ) {t : ℝ} (ht : 0 ≤ t)
    (hc : 0 < t ∨ ρ = σ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ f : Euc d → ℝ, MemOsc ρ f →
      MemOsc σ (mov_expS0 β q t f) ∧ oscNorm σ (mov_expS0 β q t f) ≤ K * oscNorm ρ f := by
  rcases hc with hpos | hρ
  · obtain ⟨C, hC, h⟩ := mov2d_expS0_bdd_T0 (d := d) hβ hq hρσ (T0 := max t 1) (lt_of_lt_of_le one_pos (le_max_right _ _))
    refine ⟨C * t ^ (-((σ - ρ) / 2)), by positivity, fun f hf => ?_⟩
    exact h t hpos (le_max_left _ _) f hf
  · subst hρ
    obtain ⟨C, hC, h⟩ := mov_expS0_bounded (d := d) hβ hq ρ
    exact ⟨C, hC, fun f hf => h t ht f hf⟩

lemma mov2d_expS0_data (hβ : 0 < β) (hq : 0 < q) {ρ σ K t : ℝ} (ht : 0 ≤ t)
    (hK : ∀ f : Euc d → ℝ, MemOsc ρ f → MemOsc σ (mov_expS0 β q t f) ∧
      oscNorm σ (mov_expS0 β q t f) ≤ K * oscNorm ρ f) :
    Mov2dData (d := d) ρ σ (mov_expS0 β q t) K := by
  refine mov2d_data_of_ae (fun c => hK _ (mov2d_hs_memOsc ρ c)) (fun c c' => ?_) (fun a c => ?_)
  · have h := mov2d_expS0_lin hβ hq ht 1 1 (mov2d_hs_memOsc ρ c).1 (mov2d_hs_memOsc ρ c').1
    simpa using h
  · have h := mov2d_expS0_lin hβ hq ht a 0 (mov2d_hs_memOsc ρ c).1 (mov2d_hs_memOsc ρ c).1
    simpa using h

/-- `e^{-tS_0}` as a bounded operator `Σ^ρ → Σ^σ` on the scale (`t ≤ 0` is read as `t = 0`). -/
def mov2d_Sm (β q : ℝ) {ρ σ : ℝ} (_ : ρ ≤ σ) (t : ℝ) : OscSpace d ρ →L[ℝ] OscSpace d σ :=
  mov2d_op ρ σ (mov_expS0 β q (max t 0))

lemma mov2d_Sm_ofFun (hβ : 0 < β) (hq : 0 < q) {ρ σ : ℝ} (h : ρ ≤ σ) {t : ℝ} (hc : 0 < t ∨ ρ = σ)
    {f : Euc d → ℝ} (hf : MemOsc ρ f) :
    mov2d_Sm β q h t (OscSpace.ofFun ρ f) = OscSpace.ofFun σ (mov_expS0 β q (max t 0) f) := by
  have ht : 0 ≤ max t 0 := le_max_right _ _
  have hc' : 0 < max t 0 ∨ ρ = σ := hc.imp_left fun h => lt_of_lt_of_le h (le_max_left _ _)
  obtain ⟨K, hK0, hK⟩ := mov2d_expS0_bdd (d := d) hβ hq h ht hc'
  exact mov2d_op_apply_of_bdd (mov2d_expS0_data hβ hq ht hK) hK
    (fun f g hf hg α => mov2d_expS0_coeff_sub hβ hq ht hf hg α) hf

lemma mov2d_Sm_zero (hβ : 0 < β) (hq : 0 < q) (r : ℝ) :
    mov2d_Sm β q (le_refl r) 0 = ContinuousLinearMap.id ℝ (OscSpace d r) := by
  refine mov2d_ext fun c => ?_
  rw [mov2d_Sm_ofFun hβ hq (le_refl r) (Or.inr rfl) (mov2d_hs_memOsc r c)]
  simp only [max_self, ContinuousLinearMap.id_apply]
  exact (mov2d_ofFun_ae (mov2d_hs_memOsc r c) (mov_expS0_zero hβ hq (mov2d_hs_memOsc r c).1).symm).symm

lemma mov2d_Sm_refl_norm_le (hβ : 0 < β) (hq : 0 < q) (r : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, 0 ≤ t → ‖(mov2d_Sm (d := d) β q (le_refl r) t : OscSpace d r →L[ℝ] OscSpace d r)‖ ≤ M := by
  obtain ⟨C, hC, h⟩ := mov_expS0_bounded (d := d) hβ hq r
  refine ⟨C, hC, fun t ht => ?_⟩
  unfold mov2d_Sm
  exact mov2d_op_norm_le (mov2d_expS0_data hβ hq (le_max_right _ _)
    (fun f hf => h (max t 0) (le_max_right _ _) f hf)) hC

/-- Strong continuity on a dense set and a uniform bound give strong continuity. -/
lemma mov2d_cont_of_dense {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {U : ℝ → E →L[ℝ] F} {S : Set ℝ} {M : ℝ}
    (hM : ∀ t ∈ S, ‖U t‖ ≤ M) {D : Set E} (hD : Dense D)
    (hc : ∀ x ∈ D, ContinuousOn (fun t => U t x) S) (x : E) : ContinuousOn (fun t => U t x) S := by
  have hne : (𝓝[D] x).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (hD x)
  refine TendstoUniformlyOn.continuousOn (F := fun (y : E) (t : ℝ) => U t y) (p := 𝓝[D] x) ?_ ?_
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hδ : 0 < ε / (|M| + 1) := by positivity
    have hmem : Metric.ball x (ε / (|M| + 1)) ∈ 𝓝[D] x :=
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x hδ)
    filter_upwards [hmem] with y hy t ht
    rw [dist_eq_norm, ← map_sub]
    have h1 : ‖U t (x - y)‖ ≤ |M| * ‖x - y‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right ((hM t ht).trans (le_abs_self M)) (norm_nonneg _))
    have h2 : ‖x - y‖ < ε / (|M| + 1) := by
      have := hy; rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev] at this; exact this
    calc ‖U t (x - y)‖ ≤ |M| * ‖x - y‖ := h1
      _ ≤ |M| * (ε / (|M| + 1)) := mul_le_mul_of_nonneg_left h2.le (abs_nonneg _)
      _ < ε := by
        have hM1 : 0 < |M| + 1 := by positivity
        rw [mul_div_assoc', div_lt_iff₀ hM1]
        nlinarith [abs_nonneg M]
  · exact (eventually_nhdsWithin_of_forall fun y hy => hc y hy).frequently

lemma mov2d_Sm_cont (hβ : 0 < β) (hq : 0 < q) (r : ℝ) (x : OscSpace d r) :
    ContinuousOn (fun t => mov2d_Sm β q (le_refl r) t x) (Set.Ici 0) := by
  obtain ⟨M, hM0, hM⟩ := mov2d_Sm_refl_norm_le (d := d) hβ hq r
  refine mov2d_cont_of_dense (D := Set.range (mov2d_e d r)) (fun t ht => hM t ht) (mov2d_e_dense r) ?_ x
  rintro _ ⟨c, rfl⟩ t0 ht0
  have hf := mov2d_hs_memOsc r c
  have hc := mov_expS0_continuous hβ hq hf ht0
  obtain ⟨C, hC, hbd⟩ := mov_expS0_bounded (d := d) hβ hq r
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  refine hc.2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : (0 : ℝ) ≤ t := ht
  have ht0' : (0 : ℝ) ≤ t0 := ht0
  have h1 := mov2d_Sm_ofFun (d := d) hβ hq (le_refl r) (t := t) (Or.inr rfl) hf
  have h2 := mov2d_Sm_ofFun (d := d) hβ hq (le_refl r) (t := t0) (Or.inr rfl) hf
  rw [max_eq_left ht'] at h1
  rw [max_eq_left ht0'] at h2
  show oscNorm r _ = ‖mov2d_Sm β q (le_refl r) t (OscSpace.ofFun r (mov2d_hs d c)) -
    mov2d_Sm β q (le_refl r) t0 (OscSpace.ofFun r (mov2d_hs d c))‖
  rw [h1, h2, ← mov2d_ofFun_sub (hbd t ht' _ hf).1 (hbd t0 ht0' _ hf).1,
    OscSpace.norm_ofFun _ (hc.1 t ht')]

/-- Semigroup law `e^{-sS_0} e^{-τ S_0} = e^{-(s+τ) S_0}` as operators `Σ^ρ → Σ^σ` (`s ≥ 0`, `τ > 0`). -/
lemma mov2d_Sm_semi (hβ : 0 < β) (hq : 0 < q) {ρ σ : ℝ} (h : ρ ≤ σ) {s τ : ℝ} (hs : 0 ≤ s) (hτ : 0 < τ)
    (y : OscSpace d ρ) :
    mov2d_Sm β q (le_refl σ) s (mov2d_Sm β q h τ y) = mov2d_Sm β q h (s + τ) y := by
  have key : (mov2d_Sm β q (le_refl σ) s).comp (mov2d_Sm β q h τ) = mov2d_Sm (d := d) β q h (s + τ) := by
    refine mov2d_ext fun c => ?_
    have hf := mov2d_hs_memOsc ρ c
    have hτ' : 0 ≤ max τ 0 := le_max_right _ _
    obtain ⟨K, hK0, hK⟩ := mov2d_expS0_bdd (d := d) hβ hq h hτ' (Or.inl (lt_of_lt_of_le hτ (le_max_left _ _)))
    have hAf := (hK _ hf).1
    rw [ContinuousLinearMap.comp_apply, mov2d_Sm_ofFun hβ hq h (Or.inl hτ) hf,
      mov2d_Sm_ofFun hβ hq (le_refl σ) (Or.inr rfl) hAf,
      mov2d_Sm_ofFun hβ hq h (Or.inl (by linarith)) hf]
    rw [max_eq_left hτ.le, max_eq_left hs, max_eq_left (by linarith : (0 : ℝ) ≤ s + τ),
      mov_expS0_add hβ hq hs hτ.le hf.1]
  exact congrArg (fun E => E y) key

/-- Smoothing bound for the operators `e^{-tS_0} : Σ^ρ → Σ^σ`, `0 < t ≤ T0`. -/
lemma mov2d_Sm_bound (hβ : 0 < β) (hq : 0 < q) {ρ σ : ℝ} (h : ρ ≤ σ) {T0 : ℝ} (hT0 : 0 < T0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ioc (0 : ℝ) T0,
      ‖(mov2d_Sm (d := d) β q h t : OscSpace d ρ →L[ℝ] OscSpace d σ)‖ ≤ C * t ^ (-((σ - ρ) / 2)) := by
  obtain ⟨C, hC, hb⟩ := mov2d_expS0_bdd_T0 (d := d) hβ hq h hT0
  refine ⟨C, hC, fun t ht => ?_⟩
  have hK0 : 0 ≤ C * t ^ (-((σ - ρ) / 2)) := mul_nonneg hC (Real.rpow_nonneg ht.1.le _)
  unfold mov2d_Sm
  rw [max_eq_left ht.1.le]
  exact mov2d_op_norm_le (mov2d_expS0_data hβ hq ht.1.le (fun f hf => hb t ht.1 ht.2 f hf)) hK0

/-- Compatibility of `e^{-tS_0}` with the embeddings `j`. -/
lemma mov2d_Sm_compS (hβ : 0 < β) (hq : 0 < q) {ρ σ ρ' σ' : ℝ} (h : ρ ≤ σ) (h' : ρ' ≤ σ') (hρ : ρ' ≤ ρ)
    (hσ : σ' ≤ σ) {t : ℝ} (ht : 0 < t) (x : OscSpace d ρ) :
    mov2d_j hσ (mov2d_Sm β q h t x) = mov2d_Sm β q h' t (mov2d_j hρ x) := by
  have key : (mov2d_j hσ).comp (mov2d_Sm β q h t) = (mov2d_Sm β q h' t).comp (mov2d_j (d := d) hρ) := by
    refine mov2d_ext fun c => ?_
    have hf := mov2d_hs_memOsc ρ c
    have hf' : MemOsc ρ' (mov2d_hs d c) := (mo_mono hρ hf).1
    obtain ⟨K, hK0, hK⟩ := mov2d_expS0_bdd (d := d) hβ hq h ht.le (Or.inl ht)
    have hAf := (hK _ hf).1
    have hm : max t 0 = t := max_eq_left ht.le
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      mov2d_Sm_ofFun hβ hq h (Or.inl ht) hf, hm, mov2d_j_ofFun hσ hAf, mov2d_j_ofFun hρ hf,
      mov2d_Sm_ofFun hβ hq h' (Or.inl ht) hf', hm]
  exact congrArg (fun E => E x) key

end ExpS0

lemma mov2d_j_refl (r : ℝ) : mov2d_j (le_refl r) = ContinuousLinearMap.id ℝ (OscSpace d r) := by
  refine mov2d_ext fun c => ?_
  rw [mov2d_j_ofFun (le_refl r) (mov2d_hs_memOsc r c)]
  rfl



end HRS.MS.MovLin

end

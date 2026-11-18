import HRS.Sections.AdjKAFinal

/-!
# ADJKA part 6: the embedding `E_j ↪ E_m` as a continuous linear map, finite energy lifts, dual evolutions
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.AdjK

open HRS HRS.Uniform HRS.Uniform.Q54 HRS.Uniform.Q48b

variable {d : ℕ}

theorem adjka_fourierCoeff_embed {r a : ℝ} (hra : r ≤ a) (x : NegSobolev d r) (k : NonzeroLattice d) :
    NegSobolev.fourierCoeff (NegSobolev.embed a x) k = NegSobolev.fourierCoeff x k := by
  have hw := q48bW_pos k
  have h : q48bW k ^ a * q48bW k ^ (-a) = 1 := by rw [mul_comm]; exact q48b_rpow_neg_mul hw a
  have hc := adjka_embed_coord hra x k
  have e : NegSobolev.fourierCoeff (NegSobolev.embed a x) k =
      q48bW k ^ a * NegSobolev.coord (NegSobolev.embed a x) k := rfl
  rw [e, hc, ← mul_assoc, h, one_mul]

theorem adjka_eval_embed {r a : ℝ} (hra : r ≤ a) (x : NegSobolev d r) (φ : Torus d → ℝ) :
    NegSobolev.eval (NegSobolev.embed a x) φ = NegSobolev.eval x φ := by
  unfold NegSobolev.eval
  exact tsum_congr fun k => by rw [adjka_fourierCoeff_embed hra]

theorem adjka_embed_add {r a : ℝ} (hra : r ≤ a) (x y : NegSobolev d r) :
    NegSobolev.embed a (x + y) = NegSobolev.embed a x + NegSobolev.embed a y := by
  refine lp.ext (funext fun k => ?_)
  show NegSobolev.coord (NegSobolev.embed a (x + y)) k =
    NegSobolev.coord (NegSobolev.embed a x) k + NegSobolev.coord (NegSobolev.embed a y) k
  rw [adjka_embed_coord hra, adjka_embed_coord hra, adjka_embed_coord hra]
  have : NegSobolev.fourierCoeff (x + y) k = NegSobolev.fourierCoeff x k + NegSobolev.fourierCoeff y k := by
    unfold NegSobolev.fourierCoeff
    have h2 : NegSobolev.coord (x + y) k = NegSobolev.coord x k + NegSobolev.coord y k := rfl
    rw [h2]; ring
  rw [this]; ring

theorem adjka_embed_smul {r a : ℝ} (hra : r ≤ a) (c : ℝ) (x : NegSobolev d r) :
    NegSobolev.embed a (c • x) = c • NegSobolev.embed a x := by
  refine lp.ext (funext fun k => ?_)
  show NegSobolev.coord (NegSobolev.embed a (c • x)) k = c * NegSobolev.coord (NegSobolev.embed a x) k
  rw [adjka_embed_coord hra, adjka_embed_coord hra]
  have : NegSobolev.fourierCoeff (c • x) k = c * NegSobolev.fourierCoeff x k := q48b_fourierCoeff_smul c x k
  rw [this]; ring

/-- The embedding `E_j ↪ E_m` (`j ≤ m`) as a contraction. -/
def adjkEmb (d : ℕ) {j m : ℝ} (h : j ≤ m) : NegSobolev d j →L[ℝ] NegSobolev d m :=
  LinearMap.mkContinuous
    { toFun := NegSobolev.embed m
      map_add' := adjka_embed_add h
      map_smul' := fun c x => adjka_embed_smul h c x } 1
    (fun x => by simpa using NegSobolev.norm_embed_le m h x)

theorem adjkEmb_apply {j m : ℝ} (h : j ≤ m) (x : NegSobolev d j) :
    adjkEmb d h x = NegSobolev.embed m x := rfl

theorem adjkEmb_norm_le {j m : ℝ} (h : j ≤ m) (x : NegSobolev d j) : ‖adjkEmb d h x‖ ≤ ‖x‖ :=
  NegSobolev.norm_embed_le m h x


theorem adjka_energy_term {j m : ℝ} (w c : ℝ) (hw : 0 < w) :
    w ^ (2 * (m - j)) * (w ^ (-m) * (w ^ j * c)) ^ 2 = c ^ 2 := by
  have e1 : (w ^ (-m) * (w ^ j * c)) ^ 2 = w ^ (2 * (-m)) * w ^ (2 * j) * c ^ 2 := by
    rw [mul_pow, mul_pow, q48b_rpow_sq hw, q48b_rpow_sq hw]; ring
  rw [e1]
  have e2 : w ^ (2 * (m - j)) * w ^ (2 * (-m)) * w ^ (2 * j) = 1 := by
    rw [← Real.rpow_add hw, ← Real.rpow_add hw]
    have : 2 * (m - j) + 2 * (-m) + 2 * j = 0 := by ring
    rw [this, Real.rpow_zero]
  calc w ^ (2 * (m - j)) * (w ^ (2 * (-m)) * w ^ (2 * j) * c ^ 2)
      = (w ^ (2 * (m - j)) * w ^ (2 * (-m)) * w ^ (2 * j)) * c ^ 2 := by ring
    _ = c ^ 2 := by rw [e2, one_mul]

theorem adjka_energy_embed {j m : ℝ} (hjm : j ≤ m) (z : NegSobolev d j) :
    adjkEnergy j m (NegSobolev.embed m z) = ENNReal.ofReal (‖z‖ ^ 2) := by
  obtain ⟨hs, hn⟩ := NegSobolev.coord_sq z
  rw [hn, ENNReal.ofReal_tsum_of_nonneg (fun k => sq_nonneg _) hs]
  unfold adjkEnergy
  refine tsum_congr fun k => ?_
  congr 1
  rw [adjka_embed_coord hjm z k]
  have hz : NegSobolev.fourierCoeff z k = q48bW k ^ j * NegSobolev.coord z k := rfl
  rw [hz]
  exact adjka_energy_term (j := j) (m := m) _ _ (q48bW_pos k)

theorem adjka_lift {j m : ℝ} (hjm : j ≤ m) (F : NegSobolev d m) (h : adjkEnergy j m F ≠ ⊤) :
    ∃ z : NegSobolev d j, NegSobolev.embed m z = F := by
  have hs := ENNReal.summable_toReal h
  set c : NonzeroLattice d → ℝ := fun k => q48bW k ^ (m - j) * NegSobolev.coord F k with hc
  have hsq : ∀ k, c k ^ 2 = Lattice.jp k.1 ^ (2 * (m - j)) * NegSobolev.coord F k ^ 2 := by
    intro k
    rw [hc]; dsimp only
    rw [mul_pow, q48b_rpow_sq (q48bW_pos k)]; rfl
  have hmem : Memℓp c 2 := by
    rw [Torus.memℓp_two_iff]
    refine hs.congr fun k => ?_
    rw [hsq k, ENNReal.toReal_ofReal (mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (sq_nonneg _))]
  let z : NegSobolev d j := (⟨c, hmem⟩ : lp (fun _ : NonzeroLattice d => ℝ) 2)
  refine ⟨z, ?_⟩
  refine lp.ext (funext fun k => ?_)
  show NegSobolev.coord (NegSobolev.embed m z) k = NegSobolev.coord F k
  rw [adjka_embed_coord hjm]
  have hz : NegSobolev.fourierCoeff z k = q48bW k ^ j * c k := rfl
  rw [hz, hc]
  dsimp only
  have hw := q48bW_pos k
  calc q48bW k ^ (-m) * (q48bW k ^ j * (q48bW k ^ (m - j) * NegSobolev.coord F k))
      = (q48bW k ^ (-m) * q48bW k ^ j * q48bW k ^ (m - j)) * NegSobolev.coord F k := by ring
    _ = NegSobolev.coord F k := by
        rw [← Real.rpow_add hw, ← Real.rpow_add hw]
        have : -m + j + (m - j) = 0 := by ring
        rw [this, Real.rpow_zero, one_mul]

/-- Dual evolutions are determined by the duality. -/
theorem adjka_dual_unique {D : DynData d} {ρ : ℝ → Torus d → ℝ} {r : ℝ}
    {V₁ V₂ : ℝ → ℝ → NegSobolev d r →L[ℝ] NegSobolev d r}
    (h₁ : IsDualEvolution D ρ r V₁) (h₂ : IsDualEvolution D ρ r V₂) {u t : ℝ} (hu : 0 ≤ u)
    (hut : u ≤ t) : V₁ t u = V₂ t u := by
  refine ContinuousLinearMap.ext fun z => ?_
  refine Q54.eq_of_eval_smooth fun φ hφ => ?_
  rw [h₁ u t hu hut z φ hφ, h₂ u t hu hut z φ hφ]

/-- Compatibility of dual evolutions on two levels with the embedding. -/
theorem adjka_dual_embed {D : DynData d} {ρ : ℝ → Torus d → ℝ} {j m : ℝ} (hjm : j ≤ m)
    {Vj : ℝ → ℝ → NegSobolev d j →L[ℝ] NegSobolev d j}
    {Vm : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m}
    (hj : IsDualEvolution D ρ j Vj) (hm : IsDualEvolution D ρ m Vm) {u t : ℝ} (hu : 0 ≤ u)
    (hut : u ≤ t) (z : NegSobolev d j) :
    Vm t u (NegSobolev.embed m z) = NegSobolev.embed m (Vj t u z) := by
  refine Q54.eq_of_eval_smooth fun φ hφ => ?_
  rw [hm u t hu hut _ φ hφ, adjka_eval_embed hjm, adjka_eval_embed hjm, hj u t hu hut z φ hφ]

end HRS.AdjK

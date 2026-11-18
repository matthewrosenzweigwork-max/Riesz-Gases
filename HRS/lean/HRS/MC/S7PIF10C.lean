import HRS.MC.S7PIF10B

/-!
# Packet piF10, part C: integrability of the densities `cylA`, `cylJ` and measurability / integrability of `A`

* pathwise: `cylA ω`, `cylJ ω` are integrable on `(0,T]` (continuous tag coefficient times an integrable density);
* `S7PIF10_A_aesm`: `ω ↦ ∫_{(0,T]} cylA ω r dr` is a.e. strongly measurable: `cylA` agrees a.s. with a jointly Borel function built from the
  progressive Itô process `Z` (`F5`) and the progressive drift `b` (`F5`), and the tag coefficient is jointly continuous (`H3`);
* `S7PIF10_A_int`: `A` is integrable, by `|cylA ω r| ≤ C ‖ℬ_N^r(ω)‖` and `M1`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIF10

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI HRS.MC.Sec7.S7PIS3 HRS.MC.Sec7.S7PIF5

variable {d : ℕ}

/-- `MemCb` is monotone in the order -/
theorem S7PIF10_memCb_mono {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {G : E → ℝ} {k l : ℕ}
    (hG : MemCb k G) (hlk : l ≤ k) : MemCb l G :=
  ⟨hG.1.of_le (by exact_mod_cast hlk), fun j hj => hG.2 j (hj.trans hlk)⟩

section Det

variable (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T)
  (γ : ℝ → Measure (PathSpace d m T)) (hγ : ∀ u ∈ Set.Icc (0 : ℝ) T, IsFutureGaussian R.D R.ρ m T u (γ u))
  {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ) (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) T)
  (hφ : ∀ i, Torus.IsSmooth (φ i)) (G : EuclideanSpace ℝ (Fin q) → ℝ) (hG : MemCb 2 G)
  (w : PathSpace d m T)

include hm hT hγ ht hφ hG

/-- the tag coefficient of the drift density is continuous on `[0,T]` -/
theorem S7PIF10_D_cont (i : Fin q) :
    ContinuousOn (fun τ => fderiv ℝ (gaussHeat (obsCov R.D R.ρ t φ) G τ)
      (obsVec m T t φ (predicted R.D R.ρ w τ)) (EuclideanSpace.single i 1)) (Set.Icc 0 T) := by
  have h1 := HRS.MC.Sec7.S7PIR.S7PIR_heat_deriv_cont R m hm T hT γ hγ t φ ht hφ G hG w 1 (by norm_num)
  have h2 := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => EuclideanSpace ℝ (Fin q)) ℝ
    (fun _ => EuclideanSpace.single i 1)).continuous.comp_continuousOn h1
  refine h2.congr (fun τ _ => ?_)
  simp [iteratedFDeriv_one_apply]

/-- the tag coefficient of the covariance density is continuous on `[0,T]` -/
theorem S7PIF10_H_cont (i j : Fin q) :
    ContinuousOn (fun τ => iteratedFDeriv ℝ 2 (gaussHeat (obsCov R.D R.ρ t φ) G τ)
      (obsVec m T t φ (predicted R.D R.ρ w τ)) ![EuclideanSpace.single i 1, EuclideanSpace.single j 1])
      (Set.Icc 0 T) :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => EuclideanSpace ℝ (Fin q)) ℝ
      ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]).continuous.comp_continuousOn
    (HRS.MC.Sec7.S7PIR.S7PIR_heat_deriv_cont R m hm T hT γ hγ t φ ht hφ G hG w 2 le_rfl)

variable {N : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → Config d N)

/-- the drift density is integrable on `(0,T]` -/
theorem S7PIF10_cylA_int (ω : Ω)
    (hb : MemLp (fun u => quadFieldAt m R.D.s (fun t => withDensityReal (R.ρ t)) P X u ω) 1
      (volume.restrict (Set.Icc (0 : ℝ) T))) :
    IntegrableOn (fun r => cylA R m T P X t φ G ω r) (Set.Ioc 0 T) := by
  refine IntegrableOn.mono_set (t := Set.Icc 0 T) ?_ Set.Ioc_subset_Icc_self
  unfold cylA
  refine integrable_finsetSum _ (fun i _ => ?_)
  exact (HRS.MC.Sec7.S7PIR.S7PIR_hInt R m hm T hT hb t φ ht hφ i).continuousOn_mul
    (S7PIF10_D_cont R m hm T hT γ hγ t φ ht hφ G hG (zetaWin m T 0 P X ω) i) isCompact_Icc

/-- the covariance density is integrable on `(0,T]` as soon as the pairings of `η_N` are -/
theorem S7PIF10_cylJ_int (ω : Ω)
    (hzi : ∀ i j, IntegrableOn (fun r => NegSobolev.eval (etaE m (X r.toNNReal ω) (withDensityReal (R.ρ r)))
        (fun y => inner ℝ (Torus.grad (obsTest R.D R.ρ t φ i r) y) (Torus.grad (obsTest R.D R.ρ t φ j r) y)))
      (Set.Icc 0 T)) :
    IntegrableOn (fun r => cylJ R m T P X t φ G ω r) (Set.Ioc 0 T) := by
  refine IntegrableOn.mono_set (t := Set.Icc 0 T) ?_ Set.Ioc_subset_Icc_self
  unfold cylJ
  refine integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => ?_))
  have h := (hzi i j).const_mul (2 * R.D.invβ)
  exact IntegrableOn.continuousOn_mul
    (S7PIF10_H_cont R m hm T hT γ hγ t φ ht hφ G hG (zetaWin m T 0 P X ω) i j) h isCompact_Icc

end Det

end HRS.MC.Sec7.S7PIF10

end

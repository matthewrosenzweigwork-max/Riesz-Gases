import HRS.Whole.Hermite
import HRS.Whole.Oscillator
import HRS.Whole.Basic
import HRS.Whole.Static
import HRS.Whole.Thermal
import HRS.Whole.Dynamics
import HRS.Whole.Adjoint
import HRS.Whole.Orbits
import HRS.Whole.Headline
import HRS.Whole.Moving
import HRS.Whole.MovingDyn
import HRS.Whole.Bias
import HRS.Whole.Critical
import HRS.Whole.CriticalNoise
import HRS.Whole.SobolevDual
import HRS.Whole.AppendixBEnergy
import HRS.Whole.AppendixBField
import HRS.Whole.AppendixBKernel
import HRS.Whole.Round2
import HRS.Whole.Window
import HRS.Whole.Round2Moving
import HRS.Whole.AppendixA
import HRS.Whole.AppendixAAdjoint
import HRS.Whole.AppendixALemmas
import HRS.Whole.AppendixALemmas2

/-!
# HRS whole-space supplement: foundations (package SFOUND-01)

* `HRS.Whole.Hermite`: Hermite functions on `ℝ` and `ℝ^d`, eigenvalues of `𝓗 = 1 - Δ + |x|²`.
* `HRS.Whole.Oscillator`: oscillator spaces `Σ^m`, duals `B_m = (Σ^m)'`, zero mass where
  defined, path spaces `C([0,T]; B_m)`.
* `HRS.Whole.Basic`: whole-space kernel, modulated energy and Gibbs laws, canonical ensemble
  with quadratic confinement, thermal equilibrium, rates, smallness class, Definition S.A.1.
* `HRS.Whole.Static` (S-STAT-01, Section S3) and `HRS.Whole.Thermal` (S-STAT-01, Section S4):
  statements of the static whole-space results (proofs pending).
-/

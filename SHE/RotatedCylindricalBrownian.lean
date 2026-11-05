module
public import SHE.RotatedItoAlgebra
public import SHE.RotatedCylindricalCoordinates
public import SHE.StandardTerminalLevy
public import SHE.CylindricalDriverLaw
public import SHE.BoundedStoppedVersion
public import SHE.BoundedVectorIntegral
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.RotatedCylindricalBrownian
open MeasureTheory PredictableL2 StoppedItoInputs PredictableItoRotation
open scoped NNReal ENNReal
variable{Ω A C ι:Type*}[MeasurableSpace Ω]
variable[NormedAddCommGroup A][InnerProductSpace ℝ A][MeasurableSpace A][BorelSpace A]
variable[NormedAddCommGroup C][InnerProductSpace ℝ C][MeasurableSpace C][BorelSpace C]
variable[SecondCountableTopology C]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable(Φ:(ℝ≥0×Ω)→A→ₗᵢ[ℝ]C)
variable(hΦ:@Measurable ((ℝ≥0×Ω)×A) C
  (𝓕.predictable.prod ‹MeasurableSpace A›) ‹MeasurableSpace C› (fun p=>Φ p.1 p.2))

open RotatedCylindricalCoordinates
variable [Countable ι][DecidableEq ι](e:ι→A) (he:Orthonormal ℝ e)
variable (J:StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H)

include he in
/-- Actual countable rotated original-J coordinates have all finite
Brownian laws, including repeated spatial coordinates and unrelated
observation times. The ONLY recognition premise is accepted block5. -/
theorem finite_laws (hH:(H:ℝ)≤1) (hH0:0<H)
    (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ) (B:ℝ≥0) (hBDG:StandardTerminalBDG16 J B)
    (hLevy:StandardTerminalLevy J) (n:ℕ) (a:Fin n→ι):
    FiniteBrownianLawOn 𝓕 μ H
      (fun i=>coordinate 𝓕 μ H Φ hΦ e J (a i)) (fun i j=>if a i=a j then 1 else 0):=by
  apply hLevy n (fun i=>row 𝓕 μ H Φ hΦ (e (a i)))
  · intro i
    exact predictable_coordinate 𝓕 μ H Φ hΦ e he J hH hH0 hnull B hBDG (a i)
  · intro i ω
    exact continuous_coordinate 𝓕 μ H Φ hΦ e he J hH0 (a i) ω
  · intro t ht
    filter_upwards [coordinate_ae 𝓕 μ H Φ hΦ e he J hH hH0 B hBDG t] with ω hω i
    simpa only [min_eq_left ht,min_eq_left (show (t:ℝ)≤(H:ℝ) from by exact_mod_cast ht)] using hω (a i)
  · filter_upwards [all_gram 𝓕 μ H Φ hΦ e he] with p hp i j
    exact hp (a i) (a j)

include he in
/-- The actual continuous rotated driver has a common Gaussian law for
EVERY finite family of coordinate/time evaluations, on the original
probability space and without choosing new coordinate versions. -/
theorem evaluation_law (hH:(H:ℝ)≤1) (hH0:0<H)
    (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ) (B:ℝ≥0) (hBDG:StandardTerminalBDG16 J B)
    (hLevy:StandardTerminalLevy J) (n:ℕ) (a:Fin n→ι) (t:Fin n→ℝ≥0) (ht:∀i,t i≤H):
    ProbabilityTheory.HasLaw
      (fun ω=>WithLp.toLp 2 (fun i=>coordinate 𝓕 μ H Φ hΦ e J (a i) (t i) ω))
      (ProbabilityTheory.multivariateGaussian (0:WordRecursion.State n)
        (fun i j=>(min (t i) (t j):ℝ≥0)*(if a i=a j then 1 else 0:ℝ))) μ:=
  (finite_laws 𝓕 μ H Φ hΦ e he J hH hH0 hnull B hBDG hLevy n a).1 t ht
include he in
/-- Concrete all-finite-laws interface consumed by the proved
cross-probability-space cylindrical driver law theorem. -/
theorem driver_law (hH:(H:ℝ)≤1) (hH0:0<H)
    (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ) (B:ℝ≥0) (hBDG:StandardTerminalBDG16 J B)
    (hLevy:StandardTerminalLevy J):
    CylindricalDriverLaw.Law μ H (coordinate 𝓕 μ H Φ hΦ e J):=by
  intro n a t ht
  exact evaluation_law 𝓕 μ H Φ hΦ e he J hH hH0 hnull B hBDG hLevy n a t ht

include he in
theorem coordinate_measurable (hH:(H:ℝ)≤1) (hH0:0<H)
    (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ) (B:ℝ≥0) (hBDG:StandardTerminalBDG16 J B)
    (i:ι) (t:ℝ≥0):Measurable (coordinate 𝓕 μ H Φ hΦ e J i t):=by
  have hp:=predictable_coordinate 𝓕 μ H Φ hΦ e he J hH hH0 hnull B hBDG i
  exact ((show IsStronglyPredictable 𝓕 (coordinate 𝓕 μ H Φ hΦ e J i) from hp).stronglyAdapted t).measurable.mono (𝓕.le t) le_rfl
end SHE.RotatedCylindricalBrownian

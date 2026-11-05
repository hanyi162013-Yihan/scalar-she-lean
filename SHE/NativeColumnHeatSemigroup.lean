module

public import SHE.NativeHeatObservation
public import SHE.HilbertColumnMap

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SHE.NativeColumnHeatSemigroup
open Set MeasureTheory FiniteHaar DyadicApproximation NativeHeatObservation
open scoped ENNReal
local instance nativeColumnHeatSemigroup_unitPositive : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩
local instance nativeColumnHeatSemigroup_nativePositive : Fact (0<2*Real.pi) := ⟨by positivity⟩

/-- The native-clock real Hilbert column has its exact unit-circle
Fourier heat realization, retaining the factor (2*pi)^2. -/
theorem realEmbed_kernel_column {ell M a : ℝ} (hell : 0<ell) (ha : 0<a)
    (f : EllipticField ell M) (i : HaarNode) :
    realEmbed (kernel ell M hell (a,f) i)=
      CircleHeat.heat (a/timeScale) (globalHaarColumn i f.1) := by
  change realEmbed (realPart (HaarHeatIntegrand.kernel ell M hell (a/timeScale,f) i))=_
  rw [realEmbed_realPart_of_real _ (RealHaarIntegrand.kernel_column_real hell _ i),
    HaarHeatIntegrand.kernel_apply,ite_eq_left (div_pos ha timeScale_pos)]

/-- Exact native heat propagation of the ENTIRE countable real Haar
column input. This is an equality in its true square-summable space. -/
theorem map_kernel {ell M t a : ℝ} (hell : 0<ell) (ht : 0≤t) (ha : 0<a)
    (f : EllipticField ell M) :
    HilbertColumns.mapCLM (NativeHeatObservation.heat t) (kernel ell M hell (a,f))=
      kernel ell M hell (t+a,f) := by
  apply lp.ext
  funext i
  change NativeHeatObservation.heat t (kernel ell M hell (a,f) i)=kernel ell M hell (t+a,f) i
  apply realCircleIdentification.injective
  apply Subtype.ext
  change realEmbed (NativeHeatObservation.heat t (kernel ell M hell (a,f) i))=
    realEmbed (kernel ell M hell (t+a,f) i)
  rw [NativeHeatObservation.heat,RealHeat.realEmbed_realHeat,
    realEmbed_kernel_column hell ha,realEmbed_kernel_column hell (add_pos_of_nonneg_of_pos ht ha)]
  rw [add_div,CircleHeat.heat_semigroup (div_nonneg ht timeScale_pos.le) (div_nonneg ha.le timeScale_pos.le)]
  rfl

end SHE.NativeColumnHeatSemigroup

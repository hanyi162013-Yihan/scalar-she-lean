module
public import SHE.RotatedCylindricalBrownian
public import SHE.StoppedInputAlgebra
public import SHE.FiniteCoordinateLaw
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1400000
namespace SHE.RawCylindricalCoordinates
open MeasureTheory ProbabilityTheory PredictableL2 StoppedItoInputs Set
open scoped NNReal ENNReal
variable {Ω C ι:Type*}[MeasurableSpace Ω]
variable [NormedAddCommGroup C][InnerProductSpace ℝ C][MeasurableSpace C][BorelSpace C][SecondCountableTopology C]
variable[Countable ι][DecidableEq ι]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable(e:ι→C)(he:Orthonormal ℝ e)
variable(J:StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H)

def row(i:ι):Process (E:=C) 𝓕 μ H:=RotatedCylindricalCoordinates.constant 𝓕 μ H (e i)
def value(i:ι)(t:ℝ≥0)(ω:Ω):ℝ:=J.integral (stop 𝓕 μ H t (row 𝓕 μ H e i)) ω

theorem value_measurable(i:ι)(t:ℝ≥0):Measurable (value 𝓕 μ H e J i t):=(Lp.stronglyMeasurable _).measurable

include he in
theorem row_norm(i:ι):∀ᵐp∂energyMeasure μ H,‖row 𝓕 μ H e i p‖^2≤1:=by
  filter_upwards [RotatedCylindricalCoordinates.constant_ae 𝓕 μ H (e i)] with p hp
  change ‖RotatedCylindricalCoordinates.constant 𝓕 μ H (e i) p‖^2≤1
  rw [hp,he.norm_eq_one i]
  norm_num

theorem stop_min(t:ℝ≥0)(u:Process (E:=C) 𝓕 μ H):
    stop 𝓕 μ H (min t H) u=stop 𝓕 μ H t u:=by
  apply PastItoAlgebra.eq_of_ambient_ae
  have ht:∀ᵐp∂energyMeasure μ H,p.1<H:=Measure.quasiMeasurePreserving_fst.ae
    ((timeMeasure_ae_mem H).and ((timeMeasure H).ae_ne H) |>.mono (fun s hs=>lt_of_le_of_ne hs.1.2 hs.2))
  filter_upwards [stop_ae 𝓕 μ H (min t H) u,stop_ae 𝓕 μ H t u,ht] with p hl hr hp
  rw [hl,hr]
  simp only [Set.indicator_apply,before,Set.mem_setOf_eq,NNReal.coe_min,lt_min_iff]
  have hp':(p.1:ℝ)<(H:ℝ):=by exact_mod_cast hp
  simp only [hp',and_true]

theorem value_clip(i:ι)(t:ℝ≥0):value 𝓕 μ H e J i t=value 𝓕 μ H e J i (min t H):=by
  unfold value
  simp only [NNReal.coe_min,stop_min]

variable(B:ℝ≥0)(hBDG:StandardTerminalBDG16 J B)(hH:(H:ℝ)≤1)(hpos:0<H)
variable(hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)

def continuous(i:ι):ℝ≥0→Ω→ℝ:=BoundedStoppedVersion.version 𝓕 μ H J (row 𝓕 μ H e i)

include he hBDG hH hpos in
theorem continuous_ae(i:ι)(t:ℝ≥0):continuous 𝓕 μ H e J i t=ᵐ[μ] value 𝓕 μ H e J i t:=by
  have hh:=BoundedStoppedVersion.version_ae 𝓕 μ H J (row 𝓕 μ H e i) hH hpos B hBDG
    (by norm_num:0≤(1:ℝ)) (row_norm 𝓕 μ H e he i) t
  rw [stop_min] at hh
  exact hh

include he hBDG hH hpos hnull in
theorem finite_laws(hLevy:StandardTerminalLevy J)(n:ℕ)(a:Fin n→ι):
    FiniteBrownianLawOn 𝓕 μ H (fun i=>continuous 𝓕 μ H e J (a i))
      (fun i j=>if a i=a j then 1 else 0):=by
  apply hLevy n (fun i=>row 𝓕 μ H e (a i))
  · intro i
    exact BoundedStoppedVersion.predictable_version 𝓕 μ H J (row 𝓕 μ H e (a i)) hH hpos hnull B hBDG
      (by norm_num:0≤(1:ℝ)) (row_norm 𝓕 μ H e he (a i))
  · intro i ω
    exact BoundedStoppedVersion.continuous_version 𝓕 μ H J (row 𝓕 μ H e (a i)) hpos ω
  · intro t ht
    filter_upwards [ae_all_iff.mpr (fun i:Fin n=>continuous_ae 𝓕 μ H e he J B hBDG hH hpos (a i) t)] with ω hω i
    exact hω i
  · filter_upwards [ae_all_iff.mpr (fun i:Fin n=>RotatedCylindricalCoordinates.constant_ae 𝓕 μ H (e (a i)))] with p hp i j
    change inner ℝ (RotatedCylindricalCoordinates.constant 𝓕 μ H (e (a i)) p)
      (RotatedCylindricalCoordinates.constant 𝓕 μ H (e (a j)) p)=_
    rw [hp i,hp j]
    exact orthonormal_iff_ite.mp he (a i) (a j)

include he hBDG hH hpos hnull in
/-- The literal original stopped deterministic rows have the full
finite Brownian laws, derived from the accepted ordinary Levy package. -/
theorem law(hLevy:StandardTerminalLevy J):CylindricalDriverLaw.Law μ H (value 𝓕 μ H e J):=by
  intro n a t ht
  apply ((finite_laws 𝓕 μ H e he J B hBDG hH hpos hnull hLevy n a).1 t ht).congr
  filter_upwards [ae_all_iff.mpr (fun i:Fin n=>continuous_ae 𝓕 μ H e he J B hBDG hH hpos (a i) (t i))] with ω hω
  apply PiLp.ext
  intro i
  exact (hω i).symm

variable {Ω':Type*}[MeasurableSpace Ω']

/-- Full raw cylindrical laws follow from the ordinary finite Brownian
laws on [0,H]; later coordinates are the SAME stopped input classes. -/
theorem map_eq(𝓖:Filtration ℝ≥0 ‹MeasurableSpace Ω'›)(ν:Measure Ω')[IsProbabilityMeasure ν]
    (K:StandardTerminalIto (C:=C) (E:=ℝ) 𝓖 ν H)
    (hμ:CylindricalDriverLaw.Law μ H (value 𝓕 μ H e J))
    (hν:CylindricalDriverLaw.Law ν H (value 𝓖 ν H e K)):
    μ.map (fun ω=>fun p:ι×ℝ≥0=>value 𝓕 μ H e J p.1 p.2 ω)=
      ν.map (fun ω=>fun p:ι×ℝ≥0=>value 𝓖 ν H e K p.1 p.2 ω):=by
  apply FiniteCoordinateLaw.map_eq μ ν
    (fun p:ι×ℝ≥0=>value 𝓕 μ H e J p.1 p.2)
    (fun p:ι×ℝ≥0=>value 𝓖 ν H e K p.1 p.2)
    (fun p=>value_measurable 𝓕 μ H e J p.1 p.2)
    (fun p=>value_measurable 𝓖 ν H e K p.1 p.2)
  intro n a
  let ind:Fin n→ι:=fun i=>(a i).1
  let t:Fin n→ℝ≥0:=fun i=>min (a i).2 H
  have ht:∀i,t i≤H:=fun i=>min_le_right _ _
  have hx:=hμ n ind t ht
  have hy:=hν n ind t ht
  have hxm:Measurable (fun ω=>WithLp.toLp 2 (fun i=>value 𝓕 μ H e J (ind i) (t i) ω)):=
    (WithLp.measurable_toLp 2 (Fin n→ℝ)).comp (measurable_pi_iff.mpr (fun i=>value_measurable 𝓕 μ H e J _ _))
  have hym:Measurable (fun ω=>WithLp.toLp 2 (fun i=>value 𝓖 ν H e K (ind i) (t i) ω)):=
    (WithLp.measurable_toLp 2 (Fin n→ℝ)).comp (measurable_pi_iff.mpr (fun i=>value_measurable 𝓖 ν H e K _ _))
  have hh:=congrArg (fun P:Measure (WordRecursion.State n)=>P.map WithLp.ofLp) (hx.map_eq.trans hy.map_eq.symm)
  rw [Measure.map_map (WithLp.measurable_ofLp 2 (Fin n→ℝ)) hxm,
    Measure.map_map (WithLp.measurable_ofLp 2 (Fin n→ℝ)) hym] at hh
  have h1:(fun ω=>fun i:Fin n=>value 𝓕 μ H e J (a i).1 (a i).2 ω)=
      (fun ω=>fun i:Fin n=>value 𝓕 μ H e J (ind i) (t i) ω):=by
    funext ω i
    exact congrFun (value_clip 𝓕 μ H e J (a i).1 (a i).2) ω
  have h2:(fun ω=>fun i:Fin n=>value 𝓖 ν H e K (a i).1 (a i).2 ω)=
      (fun ω=>fun i:Fin n=>value 𝓖 ν H e K (ind i) (t i) ω):=by
    funext ω i
    exact congrFun (value_clip 𝓖 ν H e K (a i).1 (a i).2) ω
  rw [h1,h2]
  simpa only [Function.comp_def,WithLp.ofLp_toLp] using hh
end SHE.RawCylindricalCoordinates

module
public import SHE.SelectedGirsanovSmoothModel
public import SHE.InverseNativeSmoothCommonLaw
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2400000
namespace SHE.SelectedSmoothCommonLaw
open MeasureTheory PredictableL2 LowBands OrthogonalItoChannels PredictableTimeDilation
open scoped NNReal ENNReal
local instance : SecondCountableTopology CircleHeat.CircleL2:=(_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology StateL2:=FiniteHaar.realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace StateL2:=borel _
local instance : BorelSpace StateL2:=⟨rfl⟩
local instance : MeasurableSpace RealHaarIntegrand.Columns:=borel _
local instance : BorelSpace RealHaarIntegrand.Columns:=⟨rfl⟩
local instance : MeasurableSpace FiniteHaar.RealHaarInput:=borel _
local instance : BorelSpace FiniteHaar.RealHaarInput:=⟨rfl⟩
local instance : MeasurableSpace (Both FiniteHaar.RealHaarInput):=borel _
local instance : BorelSpace (Both FiniteHaar.RealHaarInput):=⟨rfl⟩
variable{Ω Ω':Type}[MeasurableSpace Ω][MeasurableSpace Ω']
variable(Q:Measure Ω)[IsProbabilityMeasure Q]

theorem facts_cast
    {F G:Filtration ℝ≥0 ‹MeasurableSpace Ω›}{T S:ℝ≥0}(hF:F=G)(hT:T=S)
    (K:StandardTerminalIto (C:=Both FiniteHaar.RealHaarInput) (E:=ℝ) F Q T)
    (K':StandardTerminalIto (C:=Both FiniteHaar.RealHaarInput) (E:=ℝ) G Q S)(hK:HEq K K')
    (A0 A1:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2) F Q T)
    (A0' A1':StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2) G Q S)
    (h0:HEq A0 A0')(h1:HEq A1 A1')
    (hr:CylindricalDriverLaw.Law Q T (RawCylindricalCoordinates.value F Q T NativeTwoChannelNoiseBasis.both K))
    (hl:StandardTerminalPastLocality K)(hn:NullCompleteFiltration.ContainsNullSets F Q)
    (hn0:NativeObservationNaturality.StandardScalarNaturality A0 (leftIntegral F Q T K))
    (hn1:NativeObservationNaturality.StandardScalarNaturality A1 (rightIntegral F Q T K))
    (B:Bool→ℝ≥0)(hb:∀b,StandardTerminalBDG16 (if b then A0 else A1) (B b)):
    CylindricalDriverLaw.Law Q S (RawCylindricalCoordinates.value G Q S NativeTwoChannelNoiseBasis.both K') ∧
      StandardTerminalPastLocality K' ∧ NullCompleteFiltration.ContainsNullSets G Q ∧
      NativeObservationNaturality.StandardScalarNaturality A0' (leftIntegral G Q S K') ∧
      NativeObservationNaturality.StandardScalarNaturality A1' (rightIntegral G Q S K') ∧
      ∀b,StandardTerminalBDG16 (if b then A0' else A1') (B b):=by
  subst G
  subst S
  cases eq_of_heq hK
  cases eq_of_heq h0
  cases eq_of_heq h1
  exact ⟨hr,hl,hn,hn0,hn1,hb⟩

variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(H:ℝ≥0)(hH:(H:ℝ)≤1)
variable(κ:ℝ)(hκ:0<κ){a:ℝ→ℝ}(ha:Measurable a)
variable{ell M L β:ℝ}(hell:0<ell)(hb:∀z,ell≤a z∧a z≤M)(hβ:0<β)(hL:0≤L)
variable(hholder:∀z w,|a z-a w|≤L*|z-w|^β)
variable(K:StandardTerminalIto (C:=Both FiniteHaar.RealHaarInput) (E:=ℝ) 𝓕 Q H)
variable(A0 A1:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2) 𝓕 Q H)
variable(u₀:StateL2)

/-- The actual selected changed-measure smooth solutions have identical
native continuous path laws. Selection and unit-clock compatibility are
retained, and no equal-BDG-constant premise is imposed across spaces. -/
theorem paths{Lip:ℝ≥0}(hLip:LipschitzWith Lip (fun z=>(a z:ℂ)))(hpos:0<H)
    (D:SelectedGirsanovSmoothModel.Data 𝓕 Q H hH κ hκ ha hell hb hβ hL hholder K A0 A1 u₀)
    (𝓖:Filtration ℝ≥0 ‹MeasurableSpace Ω'›)(ν:Measure Ω')[IsProbabilityMeasure ν]
    (K':StandardTerminalIto (C:=Both FiniteHaar.RealHaarInput) (E:=ℝ) 𝓖 ν H)
    (A0' A1':StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2) 𝓖 ν H)
    (D':SelectedGirsanovSmoothModel.Data 𝓖 ν H hH κ hκ ha hell hb hβ hL hholder K' A0' A1' u₀)
    :
    let W:=SelectedGirsanovSmoothModel.Data.solution 𝓕 Q H hH κ hκ ha hell hb hβ hL hholder K A0 A1 u₀ D
    let W':=SelectedGirsanovSmoothModel.Data.solution 𝓖 ν H hH κ hκ ha hell hb hβ hL hholder K' A0' A1' u₀ D'
    NativePathLawComparison.law H Q W.value W.continuous=
      NativePathLawComparison.law H ν W'.value W'.continuous:=by
  dsimp only
  obtain ⟨hr,hl,hn,hn0,hn1,hB⟩:=facts_cast Q
    (NativeInverseClock.filtration_eq 𝓕).symm (NativeInverseClock.span_eq H).symm
    K (NativeInverseClock.native 𝓕 Q H K) (NativeInverseClock.native_heq 𝓕 Q H K).symm
    A0 A1 (NativeInverseClock.native 𝓕 Q H A0) (NativeInverseClock.native 𝓕 Q H A1)
    (NativeInverseClock.native_heq 𝓕 Q H A0).symm (NativeInverseClock.native_heq 𝓕 Q H A1).symm
    D.rawLaw D.locality D.nullComplete D.naturality0 D.naturality1 D.B D.bdg
  obtain ⟨hr',hl',hn',hn0',hn1',hB'⟩:=facts_cast ν
    (NativeInverseClock.filtration_eq 𝓖).symm (NativeInverseClock.span_eq H).symm
    K' (NativeInverseClock.native 𝓖 ν H K') (NativeInverseClock.native_heq 𝓖 ν H K').symm
    A0' A1' (NativeInverseClock.native 𝓖 ν H A0') (NativeInverseClock.native 𝓖 ν H A1')
    (NativeInverseClock.native_heq 𝓖 ν H A0').symm (NativeInverseClock.native_heq 𝓖 ν H A1').symm
    D'.rawLaw D'.locality D'.nullComplete D'.naturality0 D'.naturality1 D'.B D'.bdg
  have hN:∀b,NativeObservationNaturality.StandardScalarNaturality
      (NativeInverseClock.native 𝓕 Q H (if b then A0 else A1))
      (TwoChannelRawDriver.channels _ Q _ (NativeInverseClock.native 𝓕 Q H K) b):=by
    intro b
    cases b
    · exact hn1
    · exact hn0
  have hN':∀b,NativeObservationNaturality.StandardScalarNaturality
      (NativeInverseClock.native 𝓖 ν H (if b then A0' else A1'))
      (TwoChannelRawDriver.channels _ ν _ (NativeInverseClock.native 𝓖 ν H K') b):=by
    intro b
    cases b
    · exact hn1'
    · exact hn0'
  have hBs(b:Bool):StandardTerminalBDG16
      (NativeInverseClock.native 𝓕 Q H (if b then A0 else A1)) (D.B b):=by
    cases b
    · exact hB false
    · exact hB true
  have hBs'(b:Bool):StandardTerminalBDG16
      (NativeInverseClock.native 𝓖 ν H (if b then A0' else A1')) (D'.B b):=by
    cases b
    · exact hB' false
    · exact hB' true
  have he:=InverseNativeSmoothCommonLaw.paths (NativeInverseClock.base 𝓕) Q (NativeClock.time H)
    (NativeInverseClock.time_le_one H hH) κ hκ ha hell hb hβ hL hholder
    (fun b=>NativeInverseClock.native 𝓕 Q H (if b then A0 else A1))
    (NativeInverseClock.native 𝓕 Q H K) D.B hBs (NativeInverseClock.time_pos H hpos)
    hn hN hl hLip u₀ D.model (NativeInverseClock.base 𝓖) ν
    (fun b=>NativeInverseClock.native 𝓖 ν H (if b then A0' else A1'))
    (NativeInverseClock.native 𝓖 ν H K') D'.B hBs' hn' hN' hl' D'.model (ContinuousLinearMap.id ℝ StateL2) hr hr'
  rw [NativeInverseClock.span_eq H] at he
  simpa only [SelectedGirsanovSmoothModel.Data.solution,NativeInverseClock.solution_value,
    NativeInverseClock.span_eq,ContinuousLinearMap.id_apply] using he
end SHE.SelectedSmoothCommonLaw

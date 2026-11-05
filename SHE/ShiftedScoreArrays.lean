module

public import SHE.ShiftedIntervalCovariance
public import SHE.ShiftedWordCalculus
public import SHE.PhysicalFullResidualScore
public import SHE.ActualBaselineAssignments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SHE.ShiftedScoreArrays
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
  ShiftedWordGeometry ShiftedPhysicalArrays PhysicalChainArrays PhysicalScoreChain
  StoppedGaussianFeatures ObservationTimeShift GaussianConvolution
open scoped BigOperators
local instance shiftedScoreArrays_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable {X : Type} [MeasurableSpace X] {R Q : ReferenceData} {n N : ℕ}
variable (L : Level R X n) (K : Level Q X n) (v : ℝ)
variable (hb : Q.base=R.base+v) (hT : ∀ x,K.terminal x=L.terminal x+v)
variable (hZ : ∀ x,K.observations.observations x=observations v (L.observations.observations x))

theorem lower_ge_base (k : ℕ) (p : History X k) (j : Fin k) : R.base≤lower L k p j := by
  induction k with
  | zero=>exact Fin.elim0 j
  | succ k ih=>
    refine Fin.cases ?_ (fun i=>ih p.1 i) j
    exact ((carrier L k).nodeTime_mem p).1

include hb hT in
theorem lower_shift (k : ℕ) (p : History X k) :
    lower K k (shift v k p)=fun j=>lower L k p j+v := by
  induction k with
  | zero=>exact funext (fun j=>Fin.elim0 j)
  | succ k ih=>
    funext j
    refine Fin.cases ?_ (fun i=>congrFun (ih p.1) i) j
    exact nodeTime_shift L K v hb hT k p

include hb hT in
theorem upper_shift (k : ℕ) (p : History X k) :
    upper K k (shift v k p)=fun j=>upper L k p j+v := by
  induction k with
  | zero=>exact funext (fun j=>Fin.elim0 j)
  | succ k ih=>
    funext j
    refine Fin.cases ?_ (fun i=>congrFun (ih p.1) i) j
    exact terminal_shift L K v hb hT k p.1

theorem space_shift (k : ℕ) (p : History X k) : space k (shift v k p)=space k p := by
  induction k with
  | zero=>exact funext (fun j=>Fin.elim0 j)
  | succ k ih=>
    funext j
    refine Fin.cases rfl (fun i=>congrFun (ih p.1) i) j

include hb hT hZ in
theorem direction_shift (Z : Fin N→Observation) (k : ℕ) (p : History X (k+1)) :
    direction K (observations v Z) k (shift v (k+1) p)=direction L Z k p := by
  classical
  have hi:=interior_shift L K v hb hT k p
  by_cases hp : Interior L k p
  · have hp':=hi.mpr hp
    simp only [direction,if_pos hp,if_pos hp']
    rw [nodeTime_shift L K v hb hT k p]
    exact stoppedRow_translation v _ _ _ ((carrier L k).nodeTime p,p.2.2)
  · have hp':=mt hi.mp hp
    simp only [direction,if_neg hp,if_neg hp']

include hb hT hZ in
theorem directions_shift (Z : Fin N→Observation) (k : ℕ) (p : History X k) :
    directions K (observations v Z) k (shift v k p)=directions L Z k p := by
  induction k with
  | zero=>exact funext (fun j=>Fin.elim0 j)
  | succ k ih=>
    funext j
    refine Fin.cases ?_ (fun i=>congrFun (ih p.1) i) j
    exact direction_shift L K v hb hT hZ Z k p

include hb hT in
theorem covariances_shift (hR : 0≤R.base) (hv : 0≤v) (Z : Fin N→Observation)
    (c : Domain→ℝ) (k : ℕ) (p : History X k) :
    covariances K (observations v Z) (profile v c) k (shift v k p)=covariances L Z c k p := by
  funext j
  unfold covariances
  rw [lower_shift L K v hb hT k p,upper_shift L K v hb hT k p]
  have hlo : 0≤lower L k p j:=hR.trans (lower_ge_base L k p j)
  exact ShiftedIntervalCovariance.intervalCovariance_translation v Z c _ _ hlo (add_nonneg hlo hv)

include hb hT hZ in
theorem actual_covariances_shift (hR : 0≤R.base) (hv : 0≤v)
    (c : Domain→ℝ) (k : ℕ) (p : History X k) :
    covariances K ((carrier K k).observations.observations (shift v k p)) (profile v c) k (shift v k p)=
      covariances L ((carrier L k).observations.observations p) c k p := by
  rw [observations_shift L K v hb hT hZ k p]
  exact covariances_shift L K v hb hT hR hv _ c k p

variable (hc : Q.reference=profile v R.reference)
variable (hV : Q.totalVariance=R.totalVariance) (hF : ∀ x,K.test x=L.test x)

include hF in
theorem initial_shift (k : ℕ) (p : History X k) (g : Fin (n+k)→Fin N) :
    initial K k (shift v k p) g=initial L k p g := by
  unfold initial
  rw [rootParameter_shift v k p,hF]

include hb hT hc in
theorem baseline_shift (k : ℕ) (p : History X k) : baseline K k (shift v k p)=baseline L k p := by
  funext j
  unfold baseline
  rw [lower_shift L K v hb hT k p,space_shift v k p,hc]
  change R.reference ((lower L k p j+v)-v,space k p j)=R.reference (lower L k p j,space k p j)
  rw [add_sub_cancel_right]

include hb hT hc hV hF in
theorem word_shift (k : ℕ) (p : History X k) (g : Fin (n+k)→Fin N) :
    word K k (shift v k p) g=word L k p g := by
  funext z
  unfold word leaves
  rw [initial_shift L K v hF k p g,baseline_shift L K v hb hT hc k p,hV]

include hb hT hZ hc hV hF in
theorem oldAverage_shift (hR : 0≤R.base) (hv : 0≤v) (c : Domain→ℝ) (k : ℕ) (p : History X k) :
    oldAverage K (profile v c) k (shift v k p)=oldAverage L c k p := by
  unfold oldAverage
  rw [actual_covariances_shift L K v hb hT hZ hR hv c k p,
    observations_shift L K v hb hT hZ k p,directions_shift L K v hb hT hZ _ k p,
    word_shift L K v hb hT hc hV hF k p (fun i=>i)]

include hb hT hZ hc in
theorem fullResidualCovariance_shift (hR : 0≤R.base) (hv : 0≤v)
    (c : Domain→ℝ) (k : ℕ) (p : History X k) (q : ℝ) :
    fullResidualCovariance K (profile v c) k (shift v k p) (q+v)=fullResidualCovariance L c k p q := by
  unfold fullResidualCovariance
  rw [ShiftedWordCalculus.covariance_shift L K v hb hT hZ hc k p q]
  have he : (fun r=>Q.reference r-profile v c r)=profile v (fun r=>R.reference r-c r) := by
    rw [hc]
    rfl
  rw [he,actual_covariances_shift L K v hb hT hZ hR hv _ k p]

include hb hT hc hV hF in
theorem centered_test_shift (k : ℕ) (p : History X k) (s : Finset (Fin k)) :
    FiniteCenteredProduct.test s (initial K k (shift v k p) (fun i=>i))
      (fun j z=>Q.totalVariance (z (leafIndex k (fun i=>i) j))) (baseline K k (shift v k p))=
    FiniteCenteredProduct.test s (initial L k p (fun i=>i))
      (fun j z=>R.totalVariance (z (leafIndex k (fun i=>i) j))) (baseline L k p) := by
  rw [initial_shift L K v hF k p,baseline_shift L K v hb hT hc k p,hV]

include hb hT hZ hc hV hF in
theorem omittedAverage_shift (hR : 0≤R.base) (hv : 0≤v) (c : Domain→ℝ)
    (k : ℕ) (p : History X k) (q : ℝ) (j : Fin k) (m : WordRecursion.State (n+k)) :
    omittedAverage K (profile v c) k (shift v k p) (q+v) j m=omittedAverage L c k p q j m := by
  unfold omittedAverage
  rw [fullResidualCovariance_shift L K v hb hT hZ hc hR hv c k p q,
    actual_covariances_shift L K v hb hT hZ hR hv c k p,
    observations_shift L K v hb hT hZ k p,directions_shift L K v hb hT hZ _ k p,
    centered_test_shift L K v hb hT hc hV hF k p]

end SHE.ShiftedScoreArrays

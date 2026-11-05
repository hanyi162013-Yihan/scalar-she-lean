module

public import SHEStochastic.VectorHeat
public import SHE.HaarPacketL2

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.VectorHeatPackets
open MeasureTheory SHE SHE.DyadicApproximation SHE.FiniteHaar
open scoped ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local notation "μ" => AddCircle.haarAddCircle (T := (1 : ℝ))
variable {d : Type*} [Fintype d] [DecidableEq d]

theorem coordinate_integral (u : VectorHeat.Physical (d := d)) (i : d) :
    (∫ x, VectorHeat.coordinates u i x ∂μ) = (∫ x, u x ∂μ) i := by
  let L := L2EuclideanCoordinates.projection i
  have hi : Integrable (fun x => u x) μ := (Lp.memLp _).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have ha := L2EuclideanCoordinates.coordinates_ae μ u
  calc
    _ = ∫ x, L (u x) ∂μ := integral_congr_ae (by
      filter_upwards [ha] with x hx
      exact hx i)
    _ = L (∫ x, u x ∂μ) := L.integral_comp_comm hi
    _ = _ := rfl

theorem real_mean_zero (u : RealL2) (hz : (∫ x, u x ∂μ) = 0) :
    inner ℂ circleOne (realEmbed u) = 0 := by
  rw [L2.inner_def]
  have hi : Integrable (fun x => u x) μ := (Lp.memLp _).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have he : (∫ x, inner ℂ (circleOne x) (realEmbed u x) ∂μ) =
      ∫ x, Complex.ofRealCLM (u x) ∂μ := by
    apply integral_congr_ae
    filter_upwards [circleOne_ae, realEmbed_ae u] with x hx hy
    simp [hx, hy, RCLike.inner_apply]
  rw [he, Complex.ofRealCLM.integral_comp_comm hi, hz, map_zero]

theorem real_packet {t : ℝ} (ht : 0 < t) (p : List Bool) (u : RealL2)
    (hu : ∀ᵐ x ∂μ, x ∉ nodeCell p → u x = 0)
    (hz : (∫ x, u x ∂μ) = 0) :
    ‖RealHeat.realHeat t u‖ ^ 2 ≤
      nodeLength p ^ 3 * heatGradientTrace t * ‖u‖ ^ 2 := by
  have hs : ∀ᵐ x ∂μ, x ∉ nodeCell p → realEmbed u x = 0 := by
    filter_upwards [hu, realEmbed_ae u] with x hx hy
    intro hn
    rw [hy, hx hn, Complex.ofReal_zero]
  have hh := supported_mean_zero_heat_trace ht p (realEmbed u) hs (real_mean_zero u hz)
  rw [← RealHeat.realEmbed_realHeat, realEmbed_norm_eq, realEmbed_norm_eq] at hh
  exact hh

/-- Vector packets reuse the scalar Fourier cancellation theorem with
the exact Hilbert sum of coordinate energies; no dimension loss is needed. -/
theorem packet {t : ℝ} (ht : 0 < t) (p : List Bool) (u : VectorHeat.Physical (d := d))
    (hu : ∀ᵐ x ∂μ, x ∉ nodeCell p → u x = 0)
    (hz : (∫ x, u x ∂μ) = 0) :
    ‖VectorHeat.heat t u‖ ^ 2 ≤
      nodeLength p ^ 3 * heatGradientTrace t * ‖u‖ ^ 2 := by
  rw [← VectorHeat.coordinates.norm_map (VectorHeat.heat t u),
    ← VectorHeat.coordinates.norm_map u, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  rw [VectorHeat.coordinate_heat]
  apply real_packet ht p
  · filter_upwards [hu, L2EuclideanCoordinates.coordinates_ae μ u] with x hx hy
    intro hn
    change L2EuclideanCoordinates.coordinates μ u i x = 0
    rw [hy i, hx hn]
    rfl
  · rw [coordinate_integral, hz]
    rfl

theorem packet_time_bound {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (p : List Bool) (u : VectorHeat.Physical (d := d))
    (hu : ∀ᵐ x ∂μ, x ∉ nodeCell p → u x = 0)
    (hz : (∫ x, u x ∂μ) = 0) :
    ‖VectorHeat.heat t u‖ ^ 2 ≤
      nodeLength p ^ 3 * (packetHeatConstant * t ^ (-(3 / 2 : ℝ))) * ‖u‖ ^ 2 :=
  (packet ht p u hu hz).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (heatGradientTrace_bound ht ht1) (pow_nonneg (nodeLength_pos p).le 3))
      (sq_nonneg _))

theorem real_packet_min {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (p : List Bool) (u : RealL2)
    (hu : ∀ᵐ x ∂μ, x ∉ nodeCell p → u x = 0)
    (hz : (∫ x, u x ∂μ) = 0) :
    ‖RealHeat.realHeat t u‖ ^ 2 ≤
      packetHeatConstant * min 1 (nodeLength p ^ 2 / t) * ‖u‖ ^ 2 := by
  have hs : ∀ᵐ x ∂μ, x ∉ nodeCell p → realEmbed u x = 0 := by
    filter_upwards [hu, realEmbed_ae u] with x hx hy
    intro hn
    rw [hy, hx hn, Complex.ofReal_zero]
  have hh := supported_mean_zero_heat ht ht1 p (realEmbed u) hs (real_mean_zero u hz)
  rw [← RealHeat.realEmbed_realHeat, realEmbed_norm_eq, realEmbed_norm_eq] at hh
  exact hh

theorem packet_min {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (p : List Bool) (u : VectorHeat.Physical (d := d))
    (hu : ∀ᵐ x ∂μ, x ∉ nodeCell p → u x = 0)
    (hz : (∫ x, u x ∂μ) = 0) :
    ‖VectorHeat.heat t u‖ ^ 2 ≤
      packetHeatConstant * min 1 (nodeLength p ^ 2 / t) * ‖u‖ ^ 2 := by
  rw [← VectorHeat.coordinates.norm_map (VectorHeat.heat t u),
    ← VectorHeat.coordinates.norm_map u, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  rw [VectorHeat.coordinate_heat]
  apply real_packet_min ht ht1 p
  · filter_upwards [hu, L2EuclideanCoordinates.coordinates_ae μ u] with x hx hy
    intro hn
    change L2EuclideanCoordinates.coordinates μ u i x = 0
    rw [hy i, hx hn]
    rfl
  · rw [coordinate_integral, hz]
    rfl

end SHEStochastic.VectorHeatPackets

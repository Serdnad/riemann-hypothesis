module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueRealLinearOfEventuallyAddModDiscrete
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Separation.CompletelyRegular
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

namespace PureTypeVector

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField in
open scoped CategoryTheory.Obj in
theorem _root_.GlobalTheory.PureTypeVector.hermForm_smul_smul {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : ℂ) (u v : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (z • u) (w • v) = z * starRingEnd ℂ w * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm u v := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm
  rw [star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct]
  simp only [smul_eq_mul, Complex.star_def]
  ring

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField in
open scoped CategoryTheory.Obj in
theorem _root_.GlobalTheory.PureTypeVector.hermForm_self_im {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (v : Fin g → ℂ) :
    (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm v v).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm
  have key : ∀ u : Fin g → ℂ, star (star u ⬝ᵥ Hm.mulVec u) = star u ⬝ᵥ Hm.mulVec u := by
    intro u
    rw [← Matrix.star_dotProduct (Hm.mulVec u) u, Matrix.star_mulVec, hH.eq, ← Matrix.dotProduct_mulVec]
  have := key (star v)
  rw [star_star] at this
  exact this

end PureTypeVector


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField in
open scoped CategoryTheory.Obj in
theorem _root_.GlobalTheory.pureType_vector_spans_quadratic_lattice :
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Pe : D.La →+ (Fin g → ℂ))
    (Hm : Matrix (Fin g) (Fin g) ℂ), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod D ty Pe → Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z z).re) →
  (∀ x y, (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (Pe x) (Pe y)).im = D.EF x y) →
  ∀ (ρ : ℂ) (a : D.La), ρ ^ 2 = -(H.d : ℂ) → (∀ i, ty i (H.rt : E) ≠ ρ → Pe a i = 0) →
  (∀ m n : ℤ, ((m : ℂ) + n * ((1 + Complex.I * Real.sqrt H.d) / 2)) • Pe a ∈ Pe.range) ∧
  ∀ z w : ℂ, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (z • Pe a) (w • Pe a) = ((D.EF (H.w0 • a) a).natAbs : ℂ) * (2 * z * starRingEnd ℂ w / Real.sqrt H.d) := by
  intro E _ _ _ H D g ty Pe Hm hP hH hpos hE ρ a hρ hsupp
  have hw0 : ∀ i, Pe (H.w0 • a) i = (1 + ρ) / 2 * Pe a i := by
    intro i
    rw [hP.1 H.w0 a i]
    by_cases hi : ty i (H.rt : E) = ρ
    · have h2 : (2 : ℂ) * ty i (H.w0 : E) = 1 + ty i (H.rt : E) := by
        have := congrArg (fun x : 𝓞 E => ty i (x : E)) H.two_weight_eq_one_add_root
        simp only [map_mul, map_add (f := _), map_one, RingOfIntegers.coe_eq_algebraMap, map_ofNat] at this
        linear_combination this
      rw [hi] at h2
      have h3 : ty i (H.w0 : E) = (1 + ρ) / 2 := by linear_combination h2 / 2
      rw [h3]
    · rw [hsupp i hi]
      simp
  have hw0' : Pe (H.w0 • a) = ((1 + ρ) / 2) • Pe a := funext fun i => by simp [hw0 i]
  have hsqd : ((Real.sqrt H.d : ℝ) : ℂ) ^ 2 = H.d := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp
  have hsq : ρ = Complex.I * Real.sqrt H.d ∨ ρ = -(Complex.I * Real.sqrt H.d) := by
    have hprod : (ρ - Complex.I * Real.sqrt H.d) * (ρ + Complex.I * Real.sqrt H.d) = 0 := by
      linear_combination hρ + hsqd - ((Real.sqrt H.d : ℝ) : ℂ) ^ 2 * Complex.I_sq
    rcases mul_eq_zero.1 hprod with h | h
    · left
      linear_combination h
    · right
      linear_combination h
  constructor
  · intro m n
    rcases hsq with h | h
    · refine ⟨m • a + n • (H.w0 • a), ?_⟩
      rw [map_add (f := _), map_zsmul, map_zsmul]
      ext i
      simp only [Pi.add_apply, Pi.smul_apply]
      simp only [smul_eq_mul, zsmul_eq_mul, hw0 i, h]
      ring
    · refine ⟨(m + n) • a - n • (H.w0 • a), ?_⟩
      rw [map_sub, map_zsmul, map_zsmul]
      ext i
      simp only [Pi.sub_apply, Pi.smul_apply]
      simp only [smul_eq_mul, zsmul_eq_mul, hw0 i, h]
      push_cast
      ring
  · intro z w
    rw [_root_.GlobalTheory.PureTypeVector.hermForm_smul_smul]
    have him : (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (Pe a) (Pe a)).im = 0 := _root_.GlobalTheory.PureTypeVector.hermForm_self_im hH _
    have hre : 0 ≤ (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (Pe a) (Pe a)).re := by
      by_cases h0 : Pe a = 0
      · simp [h0, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm]
      · exact (hpos _ h0).le
    have hc : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (((1 + ρ) / 2) • Pe a) (Pe a) = (1 + ρ) / 2 * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (Pe a) (Pe a) := by
      simpa using _root_.GlobalTheory.PureTypeVector.hermForm_smul_smul Hm ((1 + ρ) / 2) 1 (Pe a) (Pe a)
    have hEF := hE (H.w0 • a) a
    rw [hw0', hc] at hEF
    have hh : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (Pe a) (Pe a) = ((_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (Pe a) (Pe a)).re : ℂ) :=
      Complex.ext rfl (by simp [him])
    have hs : 0 < Real.sqrt H.d := Real.sqrt_pos.2 (Nat.cast_pos.2 H.d_prime.pos)
    have habs : |((D.EF (H.w0 • a) a : ℤ) : ℝ)| = (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (Pe a) (Pe a)).re * Real.sqrt H.d / 2 := by
      rw [hh] at hEF
      have hnn : 0 ≤ (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (Pe a) (Pe a)).re * Real.sqrt H.d / 2 :=
        div_nonneg (mul_nonneg hre hs.le) zero_le_two
      rcases hsq with h | h
      · rw [h] at hEF
        simp [Complex.mul_im, Complex.div_re, Complex.div_im] at hEF
        have he : ((D.EF (H.w0 • a) a : ℤ) : ℝ) = (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (Pe a) (Pe a)).re * Real.sqrt H.d / 2 := by
          linarith
        rw [he, abs_of_nonneg hnn]
      · rw [h] at hEF
        simp [Complex.mul_im, Complex.div_re, Complex.div_im] at hEF
        have he : ((D.EF (H.w0 • a) a : ℤ) : ℝ) = -((_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (Pe a) (Pe a)).re * Real.sqrt H.d / 2) := by
          linarith
        rw [he, abs_neg, abs_of_nonneg hnn]
    have hcast : (((D.EF (H.w0 • a) a).natAbs : ℕ) : ℂ) = ((|((D.EF (H.w0 • a) a : ℤ) : ℝ)| : ℝ) : ℂ) := by
      rw [Nat.cast_natAbs, ← Int.cast_abs, Complex.ofReal_intCast]
    have hs' : ((Real.sqrt H.d : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs.ne'
    rw [hcast, habs]
    conv_lhs => rw [hh]
    push_cast
    field_simp

end GlobalTheory
end

section

open Filter Topology Set Metric

namespace GlobalTheory

section Analytic

variable {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W] {A : Type*} [AddCommGroup A]
  {ι : Type*} {Y : Type*} [TopologicalSpace Y] [T2Space Y]

theorem tendsto_map_nhds_of_separating [CompleteSpace V] [ProperSpace W] {ex : W →+ A}
    (hex : Function.Surjective ex) {G : V →+ A} {S : Set A} (h0 : (0 : A) ∈ S) {f : ι → A → Y}
    (hsep : ∀ a ∈ S, ∀ b ∈ S, (∀ i, f i a = f i b) → a = b)
    (hSe : IsOpen (ex ⁻¹' S)) (hSG : IsOpen (G ⁻¹' S))
    (hfe : ∀ i, ContinuousOn (fun w ↦ f i (ex w)) (ex ⁻¹' S))
    (hfG : ∀ i, ContinuousOn (fun z ↦ f i (G z)) (G ⁻¹' S)) :
    ∀ N ∈ 𝓝 (0 : W), ∀ᶠ z in 𝓝 (0 : V), G z ∈ ex '' N := by
  intro N hN
  have hN' : N ∩ ex ⁻¹' S ∈ 𝓝 (0 : W) := inter_mem hN (hSe.mem_nhds (by simpa using h0))
  obtain ⟨R, hR, hRN⟩ := nhds_basis_closedBall.mem_iff.1 hN'
  set r := R / 4 with hr
  have hr0 : 0 < r := by positivity
  let T : Set V := {z | ∃ w ∈ closedBall (0 : W) (2 * r), ex w = G z}
  have hKS : closedBall (0 : W) (2 * r) ⊆ ex ⁻¹' S := fun w hw ↦
    (hRN (closedBall_subset_closedBall (by linarith) hw)).2
  have hTS : T ⊆ G ⁻¹' S := by
    rintro z ⟨w, hw, h⟩
    rw [mem_preimage, ← h]
    exact hKS hw
  have hcl : closure T ∩ G ⁻¹' S ⊆ T := by
    rintro z ⟨hz, hzS⟩
    obtain ⟨x, hx, hxz⟩ := mem_closure_iff_seq_limit.1 hz
    choose w hw hwx using hx
    obtain ⟨w₀, hw₀, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : W) (2 * r)).tendsto_subseq hw
    refine ⟨w₀, hw₀, hsep _ (hKS hw₀) _ hzS fun i ↦ ?_⟩
    have h1 := (((hfe i).continuousAt (hSe.mem_nhds (hKS hw₀))).tendsto).comp hlim
    have h2 := (((hfG i).continuousAt (hSG.mem_nhds hzS)).tendsto).comp
      (hxz.comp hφ.tendsto_atTop)
    refine tendsto_nhds_unique h1 (h2.congr fun n ↦ ?_)
    simp [hwx]
  obtain ⟨c, hc⟩ := TopologicalSpace.exists_dense_seq W
  let B : ℕ → Set V := fun j ↦ {z | ∃ w ∈ ball (c j) r, ex w = G z}
  have hB : ⋃ j, closure (B j) = univ := by
    refine eq_univ_of_forall fun z ↦ ?_
    obtain ⟨w, hw⟩ := hex (G z)
    obtain ⟨j, hj⟩ := hc.exists_dist_lt w hr0
    exact mem_iUnion.2 ⟨j, subset_closure ⟨w, hj, hw⟩⟩
  obtain ⟨j, y, hy⟩ := nonempty_interior_of_iUnion_of_closed (fun _ ↦ isClosed_closure) hB
  obtain ⟨z₀, hz₀i, w₀, hw₀, hz₀⟩ :=
    mem_closure_iff.1 (interior_subset hy) _ isOpen_interior hy
  have hBT : ∀ z ∈ B j, z - z₀ ∈ T := by
    rintro z ⟨w, hw, h⟩
    refine ⟨w - w₀, ?_, by simp [h, hz₀]⟩
    rw [mem_closedBall, dist_zero_right, ← dist_eq_norm]
    have := dist_triangle_right w w₀ (c j)
    rw [mem_ball] at hw hw₀
    linarith
  have h1 : ∀ᶠ z in 𝓝 (0 : V), z + z₀ ∈ closure (B j) := by
    have : Tendsto (fun z : V ↦ z + z₀) (𝓝 0) (𝓝 z₀) := by
      simpa using (continuous_add_const z₀).tendsto 0
    exact this (mem_interior_iff_mem_nhds.1 hz₀i)
  filter_upwards [h1, hSG.mem_nhds (show (0 : V) ∈ G ⁻¹' S by simpa using h0)] with z hz hzS
  have hzT : z ∈ closure T := by
    simpa using map_mem_closure (continuous_sub_right z₀) hz hBT
  obtain ⟨w, hw, h⟩ := hcl ⟨hzT, hzS⟩
  exact ⟨w, (hRN (closedBall_subset_closedBall (by linarith) hw)).1, h⟩

theorem existsUnique_linear_lift_of_separating [NormedSpace ℂ V] [NormedSpace ℂ W]
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] {ex : W →+ A}
    (hex : Function.Surjective ex) (hker : IsDiscrete (ex.ker : Set W))
    {G : V →+ A} {S : Set A} (h0 : (0 : A) ∈ S) {f : ι → A → ℂ}
    (hsep : ∀ a ∈ S, ∀ b ∈ S, (∀ i, f i a = f i b) → a = b)
    (hSe : IsOpen (ex ⁻¹' S)) (hSG : IsOpen (G ⁻¹' S))
    (hfe : ∀ i, DifferentiableOn ℂ (fun w ↦ f i (ex w)) (ex ⁻¹' S))
    (hfG : ∀ i, DifferentiableOn ℂ (fun z ↦ f i (G z)) (G ⁻¹' S))
    (hD : ∀ w, (∀ i, fderiv ℂ (fun w ↦ f i (ex w)) 0 w = 0) → w = 0) :
    ∃! F : V →ₗ[ℂ] W, ∀ z, ex (F z) = G z := by
  have : CompleteSpace V := FiniteDimensional.complete ℂ V
  have : ProperSpace W := FiniteDimensional.proper ℂ W
  have ht := tendsto_map_nhds_of_separating hex h0 hsep hSe hSG
    (fun i ↦ (hfe i).continuousOn) (fun i ↦ (hfG i).continuousOn)
  have ht' : Tendsto G (𝓝 0) (map ex (𝓝 0)) := fun s hs ↦
    (ht _ hs).mono fun z hz ↦ image_preimage_subset _ _ hz
  obtain ⟨U, hU, hU0⟩ := isDiscrete_iff_forall_mem_exists_isOpen.1 hker 0 ex.ker.zero_mem
  obtain ⟨N, hN, hNU⟩ := exists_nhds_half_neg (hU.mem_nhds (hU0.ge rfl).1)
  have hinj : InjOn ex N := fun x hx y hy hxy ↦
    sub_eq_zero.1 (hU0.le ⟨hNU x hx y hy, by simp [AddMonoidHom.mem_ker, hxy]⟩)
  have hs : ∀ᶠ z in 𝓝 0, Function.invFunOn ex N (ex z) = z := by
    filter_upwards [hN] with z hz using hinj.leftInvOn_invFunOn hz
  have hs0 : Function.invFunOn ex N 0 = 0 := by simpa using hs.self_of_nhds
  have hc : ContinuousAt (fun z ↦ Function.invFunOn ex N (G z)) 0 := by
    rw [ContinuousAt, map_zero, hs0]
    have h1 : Tendsto (Function.invFunOn ex N) (map ex (𝓝 0)) (𝓝 0) :=
      tendsto_map'_iff.2 (tendsto_id.congr' (hs.mono fun z hz ↦ hz.symm))
    exact h1.comp ht'
  obtain ⟨L, hL, hu⟩ := existsUnique_realLinear_lift_of_germ (ex := G) hker hc
    ((ht N hN).mono fun z hz ↦ Function.invFunOn_eq hz)
  have hI : ∀ (c : ℂ) z, L (c • z) = c • L z := by
    intro c z
    refine sub_eq_zero.1 (hD _ fun i ↦ ?_)
    have h1 : DifferentiableAt ℂ (fun w ↦ f i (ex w)) 0 :=
      (hfe i).differentiableAt (hSe.mem_nhds (by simpa using h0))
    have h2 : DifferentiableAt ℂ (fun z ↦ f i (G z)) 0 :=
      (hfG i).differentiableAt (hSG.mem_nhds (by simpa using h0))
    have h3 := (h1.hasFDerivAt.restrictScalars ℝ)
    rw [← map_zero L] at h3
    have h4 := h3.comp 0 L.hasFDerivAt
    have h5 : ((fun w ↦ f i (ex w)) ∘ L) = fun z ↦ f i (G z) := by
      funext z
      simp [hL]
    rw [h5, map_zero] at h4
    have h6 := h4.unique (h2.hasFDerivAt.restrictScalars ℝ)
    have h7 : ∀ z, fderiv ℂ (fun w ↦ f i (ex w)) 0 (L z) = fderiv ℂ (fun z ↦ f i (G z)) 0 z :=
      fun z ↦ DFunLike.congr_fun h6 z
    rw [map_sub, h7, map_smul, map_smul, h7, sub_self]
  refine ⟨⟨⟨L, L.map_add⟩, hI⟩, hL, fun F hF ↦ ?_⟩
  have := realLinear_eq_of_sub_mem_discrete hker (L := F.restrictScalars ℝ) (L' := L.toLinearMap)
    fun x ↦ by simp [AddMonoidHom.mem_ker, hF, hL]
  ext z
  exact DFunLike.congr_fun this z

end Analytic

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor


open TangentOrigin in
theorem existsUnique_linear_lift_of_isHolTo :
    ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (g m : ℕ)
      (u : HolUnif A L g), (∀ v, IsTangent v → ∃! w, u.IsDiff w v) →
      (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) →
      ∀ G : (Fin m → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A), (∀ z w, G (z + w) = G z * G w) →
      IsHolTo (Set.univ : Set (Fin m → ℂ)) (fun z => (G z).left) →
      ∃! F : (Fin m → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, u.ex (F z) = G z := by
  intro A _ _ L g m u h₁ h₂ G hG hhol
  letI : CommGroup (𝟙_ (Over (Sp ℂ)) ⟶ A) :=
    { (inferInstance : Group (𝟙_ (Over (Sp ℂ)) ⟶ A)) with
      mul_comm := fun a b ↦ by
        obtain ⟨z, rfl⟩ := u.ex_onto a
        obtain ⟨w, rfl⟩ := u.ex_onto b
        exact (u.ex_add z w).symm.trans ((congrArg u.ex (add_comm z w)).trans (u.ex_add w z)) }
  let ex : (Fin g → ℂ) →+ Additive (𝟙_ (Over (Sp ℂ)) ⟶ A) :=
    AddMonoidHom.mk' (fun z ↦ Additive.ofMul (u.ex z)) u.ex_add
  let G' : (Fin m → ℂ) →+ Additive (𝟙_ (Over (Sp ℂ)) ⟶ A) :=
    AddMonoidHom.mk' (fun z ↦ Additive.ofMul (G z)) hG
  let pt : (𝟙_ (Over (Sp ℂ))).left := (default : PrimeSpectrum ℂ)
  have hsub : ∀ q : (𝟙_ (Over (Sp ℂ))).left, q = pt := fun q ↦
    Subsingleton.elim (α := PrimeSpectrum ℂ) q pt
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (x := (u.ex 0).left pt) (U := ⊤)
    (Set.mem_univ _)
  have h0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U := by
    intro q _
    rw [hsub q]
    exact hpU
  have hker : (ex.ker : Set (Fin g → ℂ)) = u.Λ := Set.ext fun z ↦ u.ker z
  refine existsUnique_linear_lift_of_separating (ex := ex) (G := G') u.ex_onto
    (hker ▸ isDiscrete_iff_discreteTopology.2 u.discrete)
    (S := {a | ⊤ ≤ (Additive.toMul a).left ⁻¹ᵁ U})
    (f := fun (s : Γ(A.left, U)) a ↦ valAt' (Additive.toMul a).left U s)
    ?_ ?_ (u.hol U 0).1 ?_ (fun s ↦ (u.hol U s).2) ?_ ?_
  · rw [← map_zero ex]
    exact h0
  · intro a ha b hb h
    refine Over.OverMorphism.ext (f := Additive.toMul a) (g := Additive.toMul b)
      (ext_evalPt (R := ℂ) hU ha hb (RingHom.ext fun s ↦ ?_))
    exact (valAt'_eq_evalPt _ U ha s).symm.trans ((h s).trans (valAt'_eq_evalPt _ U hb s))
  · have := (hhol U 0).1
    simp only [Set.mem_univ, true_and] at this
    exact this
  · intro s
    have := (hhol U s).2
    simp only [Set.mem_univ, true_and] at this
    exact this
  · intro w hw
    obtain ⟨v, ⟨hv, hd⟩, -⟩ := h₂ w
    have hvU := (tangent_mem_iff (u := u) hv U).2 h0
    refine (h₁ v hv).unique hd ((isDiff_iff hv hU hvU h0 0).2 ?_)
    rw [(isDiff_iff hv hU hvU h0 w).1 hd]
    refine RingHom.ext fun s ↦ TrivSqZeroExt.ext rfl ?_
    rw [jet_snd, jet_snd, map_zero]
    exact hw s

end GlobalTheory
end

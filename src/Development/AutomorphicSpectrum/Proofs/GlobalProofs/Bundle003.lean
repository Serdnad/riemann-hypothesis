module

public import GroundTheory.ProfiniteCohomology.Bundle001
public import Mathlib.GroupTheory.Index
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle002
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SkewOperatorBoundedByPolynomialRoots
public import Mathlib.Analysis.Complex.Norm
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle024
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Function.L2Space
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
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle001
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle001
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.ConjugateSelfDual.Bundle001
public import Mathlib.Topology.Algebra.OpenSubgroup
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace GlobalTheory.CompanionTheory.Cocycles

section Algebra

variable {k G V : Type} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
  {ρ : Representation k G V} {f : G → V}

theorem cocycle_map_one (hf : ∀ g h : G, f (g * h) = f g + ρ g (f h)) : f 1 = 0 := by
  simpa using hf 1 1

theorem cocycle_map_inv (hf : ∀ g h : G, f (g * h) = f g + ρ g (f h)) (a : G) :
    f a⁻¹ = -ρ a⁻¹ (f a) := by
  have h := hf a⁻¹ a
  rw [inv_mul_cancel, cocycle_map_one hf] at h
  exact eq_neg_of_add_eq_zero_left h.symm

def cocycleKer (ρ : Representation k G V) (f : G → V)
    (hf : ∀ g h : G, f (g * h) = f g + ρ g (f h)) : Subgroup G where
  carrier := {g | ρ g = 1 ∧ f g = 0}
  one_mem' := ⟨map_one ρ, cocycle_map_one hf⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨by rw [map_mul, ha, hb, one_mul], ?_⟩
    rw [hf, ha', hb', map_zero, add_zero]
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    have h1 : ρ a⁻¹ = 1 := by
      have h2 : ρ a⁻¹ * ρ a = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
      rwa [ha, mul_one] at h2
    refine ⟨h1, ?_⟩
    rw [cocycle_map_inv hf, ha', map_zero, neg_zero]

theorem mem_cocycleKer (hf : ∀ g h : G, f (g * h) = f g + ρ g (f h)) (g : G) :
    g ∈ cocycleKer ρ f hf ↔ ρ g = 1 ∧ f g = 0 := by
  exact Iff.rfl

theorem cocycle_mul_mem (hf : ∀ g h : G, f (g * h) = f g + ρ g (f h)) (g : G) {c : G}
    (hc : c ∈ cocycleKer ρ f hf) : f (g * c) = f g := by
  have hc' := ((mem_cocycleKer hf c).1 hc).2
  rw [hf, hc', map_zero, add_zero]

theorem inv_mul_mem_cocycleKer (hf : ∀ g h : G, f (g * h) = f g + ρ g (f h)) {a b : G}
    (h1 : f a = f b) (h2 : ρ a = ρ b) : a⁻¹ * b ∈ cocycleKer ρ f hf := by
  refine (mem_cocycleKer hf _).2 ⟨?_, ?_⟩
  · rw [map_mul, ← h2, ← map_mul, inv_mul_cancel, map_one]
  · rw [hf, cocycle_map_inv hf, h1, neg_add_cancel]

theorem injective_out_cocycleKer (hf : ∀ g h : G, f (g * h) = f g + ρ g (f h)) :
    Function.Injective fun q : G ⧸ cocycleKer ρ f hf =>
      ((f q.out, ⇑(ρ q.out)) : V × (V → V)) := by
  intro q₁ q₂ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have h2' : ρ q₁.out = ρ q₂.out := LinearMap.coe_injective h2
  rw [← QuotientGroup.out_eq' q₁, ← QuotientGroup.out_eq' q₂, QuotientGroup.eq]
  exact inv_mul_mem_cocycleKer hf h1 h2'

theorem index_cocycleKer [Finite V] (hf : ∀ g h : G, f (g * h) = f g + ρ g (f h)) :
    (cocycleKer ρ f hf).index ≠ 0 ∧
      (cocycleKer ρ f hf).index ≤ Nat.card (V × (V → V)) := by
  have hinj := injective_out_cocycleKer hf
  haveI : Finite (G ⧸ cocycleKer ρ f hf) := Finite.of_injective _ hinj
  exact ⟨Subgroup.index_ne_zero_of_finite, Nat.card_le_card_of_injective _ hinj⟩

theorem finite_right_invariant [Finite V] (H : Subgroup G) (hH : H.index ≠ 0) :
    {f : G → V | ∀ g, ∀ c ∈ H, f (g * c) = f g}.Finite := by
  haveI : Finite (G ⧸ H) := Nat.finite_of_card_ne_zero hH
  refine (Set.finite_range (fun φ : G ⧸ H → V => φ ∘ (QuotientGroup.mk : G → G ⧸ H))).subset ?_
  intro f₀ hf₀
  simp only [Set.mem_ofPred_eq] at hf₀
  refine ⟨fun q => f₀ q.out, ?_⟩
  funext g
  obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul H g
  simp only [Function.comp_apply]
  rw [hc]
  exact hf₀ g c c.2

end Algebra

theorem isOpen_cocycleKer {k G : Type} [CommRing k] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (A : Rep.{0} k G) [IsDiscreteRep A] [Finite A.V] {f : G → A.V}
    (hlc : IsLocallyConstant f) (hf : ∀ g h : G, f (g * h) = f g + A.ρ g (f h)) :
    IsOpen (cocycleKer A.ρ f hf : Set G) := by
  have hU : IsOpen ((⋂ v : A.V, (stabilizer A.ρ v : Set G)) ∩ {g | f g = 0}) :=
    (isOpen_iInter_of_finite fun v => IsDiscreteRep.isOpen_stabilizer v).inter (hlc.isOpen_fiber 0)
  apply Subgroup.isOpen_of_mem_nhds (g := 1)
  refine Filter.mem_of_superset (hU.mem_nhds ⟨Set.mem_iInter.2 fun v => ?_, cocycle_map_one hf⟩) ?_
  · rw [SetLike.mem_coe, mem_stabilizer, map_one]
    rfl
  · rintro g ⟨hg1, hg2⟩
    refine ⟨LinearMap.ext fun v => ?_, hg2⟩
    exact (mem_stabilizer A.ρ v g).1 (Set.mem_iInter.1 hg1 v)

theorem finite_cocycles : ∀ (k G : Type) [CommRing k] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (A : Rep.{0} k G) [IsDiscreteRep A], Finite A.V →
    (∀ N : ℕ, {H : Subgroup G | IsOpen (H : Set G) ∧ H.index ≠ 0 ∧ H.index ≤ N}.Finite) →
    {f : G → A.V | IsLocallyConstant f ∧ ∀ g h : G, f (g * h) = f g + A.ρ g (f h)}.Finite := by
  intro k G _ _ _ _ A _ hV hN
  refine ((hN (Nat.card (A.V × (A.V → A.V)))).biUnion (fun H hH => finite_right_invariant H hH.2.1)).subset ?_
  rintro f ⟨hlc, hf⟩
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  exact ⟨cocycleKer A.ρ f hf, ⟨isOpen_cocycleKer A hlc hf, index_cocycleKer hf⟩,
    fun g c hc => cocycle_mul_mem hf g hc⟩

end GlobalTheory.CompanionTheory.Cocycles
end

section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Charts

theorem smooth_affine_chart {k : Type} [Field k] {X : Scheme.{0}} (g : X ⟶ Sp k)
    (Z : X.IdealSheafData) (U : X.affineOpens) (hg : Smooth g) (hZ : Smooth (Z.subschemeι ≫ g)) :
    ∃ φ : k →+* Γ(X, U.1), φ.Smooth ∧ ((Ideal.Quotient.mk (Z.ideal U)).comp φ).Smooth := by
  let φ₀ : CommRingCat.of k ⟶ Γ(X, U.1) := Spec.preimage (U.2.fromSpec ≫ g)
  have h1 : Spec.map φ₀ = U.2.fromSpec ≫ g := Spec.map_preimage _
  refine ⟨φ₀.hom, ?_, ?_⟩
  · have : Smooth (Spec.map φ₀) := by
      rw [h1]
      exact @HasRingHomProperty.comp_of_isOpenImmersion @Smooth _ _ _ _ _ _ _
        (IsAffineOpen.isOpenImmersion_fromSpec (hU := U.2)) hg
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mp this
  · have hc : Z.subschemeCover.f U ≫ (Z.subschemeι ≫ g) =
        Spec.map (φ₀ ≫ CommRingCat.ofHom (Ideal.Quotient.mk (Z.ideal U))) := by
      rw [Spec.map_comp, h1, ← Category.assoc, Z.subschemeCover_map_subschemeι,
        Z.glueDataObjι_ι]
      exact Category.assoc _ _ _
    have : Smooth (Spec.map (φ₀ ≫ CommRingCat.ofHom (Ideal.Quotient.mk (Z.ideal U)))) := by
      rw [← hc]
      exact @HasRingHomProperty.comp_of_isOpenImmersion @Smooth _ _ _ _ _ _ _
        (Z.subschemeCover.map_prop U) hZ
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mp this

end GlobalTheory.CompanionTheory.Hypotheses₂.Charts
end

section

noncomputable section

open MeasureTheory Complex Matrix GlobalTheory.RealWeil Filter Topology
open scoped Real SchwartzMap ComplexConjugate

namespace GlobalTheory.CompanionTheory.Hypotheses₂.GaussCurve

theorem lp_two_norm_sq {E : Type*} [MeasurableSpace E] {μ : Measure E} (f : Lp ℂ 2 μ) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [@norm_sq_eq_re_inner ℂ, MeasureTheory.L2.inner_def,
    ← integral_re (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) f f)]
  simp_rw [inner_self_eq_norm_sq]

theorem hasDerivAt_Lp_of_dominated {E : Type*} [MeasurableSpace E] {μ : Measure E}
    (F : ℝ → Lp ℂ 2 μ) (G : Lp ℂ 2 μ) (f f' : ℝ → E → ℂ) (b : E → ℝ) (t₀ δ : ℝ) (hδ : 0 < δ)
    (hF : ∀ t, F t =ᵐ[μ] f t) (hG : G =ᵐ[μ] f' t₀) (hb : MemLp b 2 μ)
    (hd : ∀ x, ∀ t ∈ Metric.ball t₀ δ, HasDerivAt (fun s => f s x) (f' t x) t)
    (hbd : ∀ x, ∀ t ∈ Metric.ball t₀ δ, ‖f' t x‖ ≤ b x) :
    HasDerivAt F G t₀ := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  set d : ℝ → E → ℂ := fun s x => (s⁻¹ : ℝ) • (f (t₀ + s) x - f t₀ x) - f' t₀ x with hd_def
  have hD : ∀ s : ℝ, ((s⁻¹ • (F (t₀ + s) - F t₀) - G : Lp ℂ 2 μ) : E → ℂ) =ᵐ[μ] d s := by
    intro s
    filter_upwards [Lp.coeFn_sub (s⁻¹ • (F (t₀ + s) - F t₀)) G,
      Lp.coeFn_smul s⁻¹ (F (t₀ + s) - F t₀), Lp.coeFn_sub (F (t₀ + s)) (F t₀),
      hF (t₀ + s), hF t₀, hG] with x h1 h2 h3 h4 h5 h6
    simp only [hd_def, h1, Pi.sub_apply, h2, Pi.smul_apply, h3, h4, h5, h6]
  have hsq : ∀ s : ℝ, ‖s⁻¹ • (F (t₀ + s) - F t₀) - G‖ ^ 2 = ∫ x, ‖d s x‖ ^ 2 ∂μ := by
    intro s
    rw [lp_two_norm_sq]
    exact integral_congr_ae ((hD s).mono fun x hx => by simp only [hx])
  have hlim : Tendsto (fun s : ℝ => ∫ x, ‖d s x‖ ^ 2 ∂μ) (𝓝[≠] 0) (𝓝 (∫ _x, (0 : ℝ) ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => (2 * b x) ^ 2) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun s =>
        (((Lp.aestronglyMeasurable _).congr (hD s)).norm.pow 2)
    · have hs : ∀ᶠ s : ℝ in 𝓝[≠] 0, s ≠ 0 ∧ |s| < δ := by
        have h1 : ∀ᶠ s : ℝ in 𝓝[≠] 0, s ≠ 0 := eventually_mem_nhdsWithin
        have h2 : ∀ᶠ s : ℝ in 𝓝[≠] 0, |s| < δ := by
          refine nhdsWithin_le_nhds ?_
          have : ∀ᶠ s : ℝ in 𝓝 0, s ∈ Metric.ball (0 : ℝ) δ := Metric.ball_mem_nhds _ hδ
          exact this.mono fun s hs => by simpa using hs
        exact h1.and h2
      refine hs.mono fun s hs => Eventually.of_forall fun x => ?_
      obtain ⟨hs0, hsδ⟩ := hs
      have hmem : t₀ + s ∈ Metric.ball t₀ δ := by simpa [Metric.mem_ball, dist_eq_norm] using hsδ
      have h0 : t₀ ∈ Metric.ball t₀ δ := Metric.mem_ball_self hδ
      have hmv : ‖f (t₀ + s) x - f t₀ x‖ ≤ b x * ‖(t₀ + s) - t₀‖ :=
        (convex_ball t₀ δ).norm_image_sub_le_of_norm_hasDerivWithin_le
          (f := fun r => f r x) (f' := fun r => f' r x)
          (fun r hr => (hd x r hr).hasDerivWithinAt) (fun r hr => hbd x r hr) h0 hmem
      have hb0 : 0 ≤ b x := (norm_nonneg _).trans (hbd x t₀ h0)
      have hq : ‖(s⁻¹ : ℝ) • (f (t₀ + s) x - f t₀ x)‖ ≤ b x := by
        rw [norm_smul, norm_inv]
        have hn : 0 < ‖s‖ := norm_pos_iff.2 hs0
        rw [add_sub_cancel_left] at hmv
        rw [inv_mul_le_iff₀ hn]
        linarith [mul_comm (b x) ‖s‖]
      have hdn : ‖d s x‖ ≤ 2 * b x := by
        calc ‖d s x‖ ≤ ‖(s⁻¹ : ℝ) • (f (t₀ + s) x - f t₀ x)‖ + ‖f' t₀ x‖ := norm_sub_le _ _
          _ ≤ 2 * b x := by linarith [hbd x t₀ h0]
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) hdn 2
    · simpa [mul_pow] using hb.integrable_sq.const_mul (2 ^ 2)
    · refine Eventually.of_forall fun x => ?_
      have h1 := hasDerivAt_iff_tendsto_slope_zero.1 (hd x t₀ (Metric.mem_ball_self hδ))
      have h2 : Tendsto (fun s : ℝ => d s x) (𝓝[≠] 0) (𝓝 (f' t₀ x - f' t₀ x)) :=
        h1.sub tendsto_const_nhds
      have h3 := (h2.norm).pow 2
      simpa using h3
  have hlim0 : Tendsto (fun s : ℝ => ‖s⁻¹ • (F (t₀ + s) - F t₀) - G‖ ^ 2) (𝓝[≠] 0) (𝓝 0) := by
    simp only [hsq]
    simpa using hlim
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h4 := (Real.continuous_sqrt.tendsto 0).comp hlim0
  simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using h4

variable {l : Type} [Fintype l]

end GlobalTheory.CompanionTheory.Hypotheses₂.GaussCurve

end
end

section

open Matrix

namespace GlobalTheory.CompanionTheory.IsometricMatrix

theorem exp_mulVec_of_mulVec_eq_zero {m : ℕ} (N : Matrix (Fin m) (Fin m) ℂ) (x : Fin m → ℂ)
    (hx : N *ᵥ x = 0) : NormedSpace.exp N *ᵥ x = x := by
  have hC : N * Matrix.replicateCol (Fin 1) x = Matrix.replicateCol (Fin 1) x * (0 : Matrix (Fin 1) (Fin 1) ℂ) := by
    ext i j
    have hi := congrFun hx i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hi
    simpa [Matrix.mul_apply, Matrix.replicateCol] using hi
  have hE := matrix_exp_mul_eq_mul_exp_of_intertwine N _ 0 hC
  simp only [NormedSpace.exp_zero, Matrix.mul_one] at hE
  ext i
  have hi := congrFun (congrFun hE i) 0
  simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.replicateCol] using hi

theorem main {n n' : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (H' : Matrix (Fin n') (Fin n') ℂ)
    (J : Matrix (Fin n) (Fin n') ℂ)
    (hH : Hᴴ = H) (hH' : H'ᴴ = H') (hd : IsUnit H.det) (hd' : IsUnit H'.det)
    (hJ : Jᴴ * H * J = H') :
    ((H'⁻¹ * Jᴴ * H) * J = 1 ∧
      (∀ Z : Matrix (Fin n') (Fin n') ℂ, -(H⁻¹ * (J * Z * (H'⁻¹ * Jᴴ * H))ᴴ * H) = J * (-(H'⁻¹ * Zᴴ * H')) * (H'⁻¹ * Jᴴ * H)) ∧
      (∀ A : Matrix (Fin n') (Fin n') ℂ, Aᴴ * H' + H' * A = 0 →
        (J * A * (H'⁻¹ * Jᴴ * H))ᴴ * H + H * (J * A * (H'⁻¹ * Jᴴ * H)) = 0) ∧
      (∀ (A : Matrix (Fin n') (Fin n') ℂ) (t : ℝ), NormedSpace.exp (t • (J * A * (H'⁻¹ * Jᴴ * H))) * J = J * NormedSpace.exp (t • A)) ∧
      (∀ (A : Matrix (Fin n') (Fin n') ℂ) (t : ℝ) (x : Fin n → ℂ), (Jᴴ * H) *ᵥ x = 0 →
        NormedSpace.exp (t • (J * A * (H'⁻¹ * Jᴴ * H))) *ᵥ x = x)) := by
  have hJ' : Jᴴ * (H * J) = H' := by rw [← Matrix.mul_assoc]; exact hJ
  have hPJ : H'⁻¹ * Jᴴ * H * J = 1 := by
    simp only [Matrix.mul_assoc]
    rw [hJ', Matrix.nonsing_inv_mul _ hd']
  have hPs : (H'⁻¹ * Jᴴ * H)ᴴ = H * J * H'⁻¹ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_nonsing_inv, hH, hH', Matrix.mul_assoc]
  refine ⟨hPJ, fun Z => ?_, fun A hA => ?_, fun A t => ?_, fun A t x hx => ?_⟩
  · rw [Matrix.conjTranspose_mul (J * Z) (H'⁻¹ * Jᴴ * H), hPs, Matrix.conjTranspose_mul J Z]
    simp only [Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg,
      Matrix.nonsing_inv_mul_cancel_left _ _ hd, Matrix.mul_nonsing_inv_cancel_left _ _ hd']
  · have key : H * J * H'⁻¹ * (Aᴴ * H' + H' * A) * (H'⁻¹ * Jᴴ * H) =
        (J * A * (H'⁻¹ * Jᴴ * H))ᴴ * H + H * (J * A * (H'⁻¹ * Jᴴ * H)) := by
      rw [Matrix.conjTranspose_mul (J * A) (H'⁻¹ * Jᴴ * H), hPs, Matrix.conjTranspose_mul J A,
        Matrix.mul_add, Matrix.add_mul]
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hd',
        Matrix.mul_nonsing_inv_cancel_left _ _ hd']
    rw [← key, hA, Matrix.mul_zero, Matrix.zero_mul]
  · have hBJ : J * A * (H'⁻¹ * Jᴴ * H) * J = J * A := by
      rw [Matrix.mul_assoc, hPJ, Matrix.mul_one]
    exact matrix_exp_smul_mul_eq_mul_exp_smul_of_intertwine n n' _ J A hBJ t
  · have hB : (J * A * (H'⁻¹ * Jᴴ * H)) *ᵥ x = 0 := by
      have hfac : J * A * (H'⁻¹ * Jᴴ * H) = (J * A * H'⁻¹) * (Jᴴ * H) := by
        simp only [Matrix.mul_assoc]
      rw [hfac, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
    apply exp_mulVec_of_mulVec_eq_zero
    rw [Matrix.smul_mulVec, hB, smul_zero]

end GlobalTheory.CompanionTheory.IsometricMatrix
end

section

open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.skew_operator_bounded_by_polynomial_roots :
    ∀ (M H : Type) [AddCommGroup M] [Module ℂ M] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (ι : M →ₗ[ℂ] H), Function.Injective ι → ∀ T : Module.End ℂ M,
      (∀ x y, ⟪ι (T x), ι y⟫_ℂ = -⟪ι x, ι (T y)⟫_ℂ) →
      ∀ m : Polynomial ℂ, m ≠ 0 → ∀ κ : ℝ, 0 ≤ κ → (∀ r ∈ m.roots, ‖r‖ ≤ κ) →
      ∀ x, Polynomial.aeval T m x = 0 → ‖ι (T x)‖ ≤ κ * ‖ι x‖ :=
  GlobalTheory.CompanionTheory.SkewSpec.norm_le_of_aeval_eq_zero
end

section

open Filter Topology

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test

theorem eq_one_of_pow_near (z : ℂ) (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 :=
  _root_.UpperTheory.Reformulated.B.EqOneOfPowNear.eq_one_of_pow_near z h

theorem char_eq_one_of_near {G : Type} [AddCommGroup G] (H : AddSubgroup G) (χ : G → ℂ) (h0 : χ 0 = 1)
    (hχ : ∀ x y, χ (x + y) = χ x * χ y) (hs : ∀ x ∈ H, ‖χ x - 1‖ < 1 / 2) {x : G} (hx : x ∈ H) :
    χ x = 1 := by
  have hn : ∀ n : ℕ, χ (n • x) = χ x ^ n := by
    intro n
    induction n with
    | zero => simp [h0]
    | succ n ih => rw [succ_nsmul, hχ, ih, pow_succ]
  refine eq_one_of_pow_near _ fun n => ?_
  rw [← hn]
  exact hs _ (H.nsmul_mem hx n)

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
end

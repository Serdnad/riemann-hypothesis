module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import Mathlib.Tactic.ENatToNat
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle012
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.NormalSchemeHeightOneStalkDvr
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle004
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle017
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RiemannFormHermitianLattice
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FirstOrderPointsCommute
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.Henselian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinitePartLePreimageOfClosedFibreSubset
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle018
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Trace.Defs
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TraceIntegralSubringExtension
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT.TorIso

variable {R : Type} [CommRing R] [IsDomain R] {T₁ T₂ : Type} [CommGroup T₁] [CommGroup T₂]
  {Γ₁ : BT.QFGroup R T₁} {Γ₂ : BT.QFGroup R T₂} {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : Sp R ⟶ S} {N : ℕ}
  {i₁ : Γ₁.G.left ⟶ G.left} {i₂ : Γ₂.G.left ⟶ G.left}

theorem exists_hom (h₁ : Γ₁.IsTorsionAlong G x N i₁) (h₂ : Γ₂.IsTorsionAlong G x N i₂) :
    ∃ ψ : Γ₁.G ⟶ Γ₂.G, ψ.left ≫ i₂ = i₁ := by
  let g : Over.mk (Γ₁.G.hom ≫ x) ⟶ G := Over.homMk i₁ h₁.isOver
  have hg : g ^ N = 1 := (h₁.kernel Γ₁.G g).2 ⟨𝟙 _, by simp [g]⟩
  obtain ⟨y, hy⟩ := (h₂.kernel Γ₁.G g).1 hg
  exact ⟨y, hy⟩

theorem hom_mul (h₁ : Γ₁.IsTorsionAlong G x N i₁) (h₂ : Γ₂.IsTorsionAlong G x N i₂) (ψ : Γ₁.G ⟶ Γ₂.G)
    (hψ : ψ.left ≫ i₂ = i₁) {Y : Over (Spec (CommRingCat.of R))} (y z : Y ⟶ Γ₁.G) :
    (y * z) ≫ ψ = (y ≫ ψ) * (z ≫ ψ) := by
  have w : ∀ u : Y ⟶ Γ₁.G, (u.left ≫ i₁) ≫ G.hom = (Over.mk (Y.hom ≫ x)).hom := fun u => by
    have := Over.w u
    simp only [Category.assoc, h₁.isOver, Over.mk_hom]
    rw [← Category.assoc, this]
  let y₀ : Over.mk (Y.hom ≫ x) ⟶ G := Over.homMk (y.left ≫ i₁) (w y)
  let z₀ : Over.mk (Y.hom ≫ x) ⟶ G := Over.homMk (z.left ≫ i₁) (w z)
  have e₁ := h₁.mul Y y z y₀ z₀ rfl rfl
  have e₂ := h₂.mul Y (y ≫ ψ) (z ≫ ψ) y₀ z₀ (by simp [y₀, hψ]) (by simp [z₀, hψ])
  apply h₂.inj
  rw [Over.comp_left, Category.assoc, hψ, ← e₁, e₂]

theorem exists_pt (ψ : Γ₁.G ⟶ Γ₂.G) (t : T₁) : ∃ t', Γ₁.pt t ≫ ψ = Γ₂.pt t' := by
  obtain ⟨t', ht⟩ := BT.QFGroup.exists_eq_comp_pt R T₂ Γ₂ (FractionRing R) (RingHom.id _)
    ((Γ₁.pt t).left ≫ ψ.left) (by
      rw [Category.assoc, Over.w ψ, Over.w (Γ₁.pt t), RingHom.id_comp]
      rfl)
  refine ⟨t', Over.OverMorphism.ext ?_⟩
  rw [Over.comp_left, ht]
  have : CommRingCat.ofHom (RingHom.id (FractionRing R)) = 𝟙 _ := rfl
  rw [this, Spec.map_id, Category.id_comp]

theorem pt_injective (Γ : BT.QFGroup R T₁) : Function.Injective Γ.pt := fun a b h => by
  let o : Spec (CommRingCat.of (FractionRing R)) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing R))
  exact Γ.pt_inj a b o o (by rw [h])

theorem valAt_comp {B : Type} [CommRing B] {X Y : Scheme.{0}} (y : Spec (CommRingCat.of B) ⟶ Y) (g : Y ⟶ X)
    (s : Γ(X, ⊤)) : BT.valAt (y ≫ g) ⊤ le_top s = BT.valAt y ⊤ le_top (g.appTop s) := by
  unfold BT.valAt
  congr 1

theorem exists_mulEquiv_isHT : ∀ (R : Type) [CommRing R] [IsDomain R] (T₁ T₂ : Type) [CommGroup T₁] [CommGroup T₂] (Γ₁ : BT.QFGroup R T₁) (Γ₂ : BT.QFGroup R T₂) (S : Scheme.{0}) (G : Over S) [GrpObj G] (x : Sp R ⟶ S) (N : ℕ) (i₁ : Γ₁.G.left ⟶ G.left) (i₂ : Γ₂.G.left ⟶ G.left), Γ₁.IsTorsionAlong G x N i₁ → Γ₂.IsTorsionAlong G x N i₂ → ∃ b : T₁ ≃* T₂, ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (χ : T₁ →* Rˣ) (w : Module.Dual R L), Γ₁.IsHT i₁ M N χ w → Γ₂.IsHT i₂ M N (χ.comp b.symm.toMonoidHom) w := by
  intro R _ _ T₁ T₂ _ _ Γ₁ Γ₂ S G _ x N i₁ i₂ h₁ h₂
  obtain ⟨ψ, hψ⟩ := exists_hom h₁ h₂
  obtain ⟨ψ', hψ'⟩ := exists_hom h₂ h₁
  have c₁ : ψ ≫ ψ' = 𝟙 _ := h₁.inj _ _ _ (by simp [hψ, hψ'])
  have c₂ : ψ' ≫ ψ = 𝟙 _ := h₂.inj _ _ _ (by simp [hψ, hψ'])
  choose f hf using exists_pt (Γ₁ := Γ₁) (Γ₂ := Γ₂) ψ
  choose f' hf' using exists_pt (Γ₁ := Γ₂) (Γ₂ := Γ₁) ψ'
  have fmul : ∀ a c, f (a * c) = f a * f c := fun a c => pt_injective Γ₂ (by
    rw [← hf, map_mul, map_mul, hom_mul h₁ h₂ ψ hψ, hf, hf])
  let b : T₁ ≃* T₂ :=
    { toFun := f
      invFun := f'
      left_inv := fun t => pt_injective Γ₁ (by rw [← hf', ← hf, Category.assoc, c₁, Category.comp_id])
      right_inv := fun t => pt_injective Γ₂ (by rw [← hf, ← hf', Category.assoc, c₂, Category.comp_id])
      map_mul' := fmul }
  refine ⟨b, ?_⟩
  rintro L _ _ M χ w ⟨s, hs, hv⟩
  refine ⟨ψ'.left.appTop s, fun t => ?_, fun e => ?_⟩
  · have e₁ : (Γ₂.pt t).left ≫ ψ'.left = (Γ₁.pt (f' t)).left := congrArg (fun z => z.left) (hf' t)
    refine (valAt_comp _ _ s).symm.trans ?_
    rw [e₁]
    exact hs (f' t)
  · obtain ⟨v, v₁, v₂, v₃⟩ := hv e
    have e₁ : ψ.left ≫ ψ'.left = 𝟙 _ := congrArg (fun z => z.left) c₁
    refine ⟨v ≫ ψ.left, ?_, ?_, ?_⟩
    · rw [Category.assoc, Over.w ψ, v₁]
    · rw [Category.assoc, hψ, v₂]
    · refine (valAt_comp _ _ s).symm.trans ?_
      rw [Category.assoc, e₁, Category.comp_id]
      exact v₃

end GlobalTheory.CompanionTheory.Ar.BT.TorIso
end
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem isFinite_open_le_of_closedFibre_le : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (U U' : X.Opens), IsFinite (U.ι ≫ f) → (∀ x : X, f x = IsLocalRing.closedPoint R → x ∈ U') → U ≤ U' :=
  @PositivityTheory.HtPt.Unc.finite_le

end GlobalTheory.CompanionTheory.Ar.BT
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem exists_isFinite_open_of_henselian : ∀ (R : Type) [CommRing R] [HenselianLocalRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) [LocallyQuasiFinite f] [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f], ∃ U : X.Opens, IsFinite (U.ι ≫ f) ∧ ∀ x : X, f x = IsLocalRing.closedPoint R → x ∈ U := by
  intro R _ _ X f _ _ _ _
  refine ⟨GlobalTheory.finitePart f, GlobalTheory.isFinite_finitePart f, fun x hx => ?_⟩
  exact GlobalTheory.mem_finitePart_of_eq_closedPoint f x hx

end GlobalTheory.CompanionTheory.Ar.BT
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar


theorem _root_.GlobalTheory.T.smooth_group_tangent_lift : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [Smooth G.hom] (R : Type) [CommRing R] (x : Sp R ⟶ S) (p : Ideal R) [p.IsPrime],
  ∃ f : R, f ∉ p ∧ ∃ (U : G.left.Opens) (V : S.Opens) (hU : IsAffineOpen U) (_ : IsAffineOpen V) (hUV : U ≤ G.hom ⁻¹ᵁ V),
    RingHom.Smooth (G.hom.appLE V U hUV).hom ∧
    ∃ u : Γ(G.left, U) →+* Localization.Away f,
      (1 : Over.mk (spMap (algebraMap R (Localization.Away f)) ≫ x) ⟶ G).left = spMap u ≫ hU.fromSpec := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Chart.exists_chart_at_point | exact GlobalTheory.CompanionTheory.Ar.Chart.exists_chart_at_point | (intros; apply GlobalTheory.CompanionTheory.Ar.Chart.exists_chart_at_point <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem stalk_isDiscreteValuationRing_of_dim_one : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X], IsNormalScheme X → ∀ p : X, ringKrullDim (X.presheaf.stalk p) = 1 → ∃ _ : IsDomain (X.presheaf.stalk p), IsDiscreteValuationRing (X.presheaf.stalk p) :=
  @PositivityTheory.UnitarySelfGeneration.normal_scheme_height_one_stalk_dvr

end GlobalTheory.CompanionTheory.Ar
end

section

open AlgebraicGeometry CategoryTheory

theorem _root_.GlobalTheory.T.generic_vanishing_stalk_vanishing : ∀ (X : Scheme.{0}) [IsReduced X] (Ω O : Type) [Field Ω] [CommRing O] (ξ : Spec (CommRingCat.of Ω) ⟶ X), (∀ q : X, ξ (IsLocalRing.closedPoint Ω) ⤳ q) → ∀ (s₀ : X ⟶ Spec (CommRingCat.of O)) (gm : O →+* Ω), ξ ≫ s₀ = Spec.map (CommRingCat.ofHom gm) → ∀ (x : X) (a : O), gm a = 0 → (Spec.preimage (X.fromSpecStalk x ≫ s₀)).hom a = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.germ_vanish_of_generic_dominated | exact GlobalTheory.CompanionTheory.Ggeo.germ_vanish_of_generic_dominated | (intros; apply GlobalTheory.CompanionTheory.Ggeo.germ_vanish_of_generic_dominated <;> assumption)
end

section

open Filter Topology Metric

theorem _root_.GlobalTheory.T.implicit_function_holomorphic : ∀ (n : ℕ) (I J : Type) [Fintype I] [Fintype J] (Ω : Set ((Fin n → ℂ) × (I → ℂ))) (Φ : (Fin n → ℂ) × (I → ℂ) → (J → ℂ)) (b₀ : Fin n → ℂ) (x₀ : I → ℂ) (L : (I → ℂ) ≃L[ℂ] (J → ℂ)), IsOpen Ω → (b₀, x₀) ∈ Ω → DifferentiableOn ℂ Φ Ω → HasFDerivAt (fun x => Φ (b₀, x)) (L : (I → ℂ) →L[ℂ] (J → ℂ)) x₀ →
  ∃ (ε δ : ℝ) (X : (Fin n → ℂ) × (J → ℂ) → (I → ℂ)), 0 < ε ∧ 0 < δ ∧ X (b₀, Φ (b₀, x₀)) = x₀ ∧
    DifferentiableOn ℂ X (ball b₀ ε ×ˢ ball (Φ (b₀, x₀)) ε) ∧
    (∀ p ∈ ball b₀ ε ×ˢ ball (Φ (b₀, x₀)) ε, (p.1, X p) ∈ Ω ∧ Φ (p.1, X p) = p.2 ∧
      ∀ v, fderiv ℂ (fun x => Φ (p.1, x)) (X p) v = 0 → v = 0) ∧
    ∀ b ∈ ball b₀ δ, ∀ x ∈ ball x₀ δ, (b, x) ∈ Ω ∧ Φ (b, x) ∈ ball (Φ (b₀, x₀)) ε ∧ X (b, Φ (b, x)) = x := by
  first | exact @GlobalTheory.CompanionTheory.HoloChart.holomorphic_inverse_with_parameters | exact GlobalTheory.CompanionTheory.HoloChart.holomorphic_inverse_with_parameters | (intros; apply GlobalTheory.CompanionTheory.HoloChart.holomorphic_inverse_with_parameters <;> assumption)
end

section

open Filter Topology Matrix

theorem _root_.GlobalTheory.T.siegel_limit_imag_bound : ∀ (g : ℕ) (Bs : Matrix (Fin g) (Fin g) ℤ) (σ : Matrix (Fin g) (Fin g) ℂ) (σs τs : ℕ → Matrix (Fin g) (Fin g) ℂ) (t : ℕ → ℂ) (c : ℝ) (us vs : ℕ → Fin g → ℤ) (y : Fin g → ℂ), 0 < c → Tendsto σs atTop (𝓝 σ) → Tendsto (fun m => (t m).im) atTop atTop → (∀ m, τs m = σs m + t m • Bs.map (fun x : ℤ => (x : ℂ))) → (∀ m, ((τs m).map Complex.im - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef) → (∀ v : Fin g → ℝ, Bs.map (fun x : ℤ => (x : ℝ)) *ᵥ v = 0 → c * (v ⬝ᵥ v) ≤ v ⬝ᵥ ((σ.map Complex.im) *ᵥ v)) → Tendsto (fun m => (fun k => (us m k : ℂ)) + τs m *ᵥ (fun k => (vs m k : ℂ))) atTop (𝓝 y) → ∃ u v : Fin g → ℤ, Bs *ᵥ v = 0 ∧ y = (fun k => (u k : ℂ)) + σ *ᵥ (fun k => (v k : ℂ)) ∧ ∀ᶠ m in atTop, us m = u ∧ vs m = v := by
  first | exact @GlobalTheory.CompanionTheory.PeriodLimitSeq.limit_seq | exact GlobalTheory.CompanionTheory.PeriodLimitSeq.limit_seq | (intros; apply GlobalTheory.CompanionTheory.PeriodLimitSeq.limit_seq <;> assumption)
end

section

open Filter Topology Matrix

theorem _root_.GlobalTheory.T.riemann_form_hermitian_lattice : ∀ (g : ℕ) (Bs : Matrix (Fin g) (Fin g) ℤ) (τ G : Matrix (Fin g) (Fin g) ℂ) (c : ℝ), 0 < c → (Bs.map (fun x : ℤ => (x : ℝ))).PosSemidef → τᵀ = τ → (∀ v : Fin g → ℝ, Bs.map (fun x : ℤ => (x : ℝ)) *ᵥ v = 0 → c * (v ⬝ᵥ v) ≤ v ⬝ᵥ ((τ.map Complex.im) *ᵥ v)) → G.IsHermitian → (∀ u u' v v' : Fin g → ℤ, Bs *ᵥ v = 0 → Bs *ᵥ v' = 0 → (((fun k => (u k : ℂ)) + τ *ᵥ (fun k => (v k : ℂ))) ⬝ᵥ G *ᵥ star ((fun k => (u' k : ℂ)) + τ *ᵥ (fun k => (v' k : ℂ)))).im = ((v ⬝ᵥ u' - u ⬝ᵥ v' : ℤ) : ℝ)) → (∀ u : Fin g → ℤ, (∀ v : Fin g → ℤ, Bs *ᵥ v = 0 → u ⬝ᵥ v = 0) → G *ᵥ (fun k => (u k : ℂ)) = 0) → ∀ y : Fin g → ℂ, 0 ≤ (y ⬝ᵥ G *ᵥ star y).re ∧ (y ⬝ᵥ G *ᵥ star y).re ≤ c⁻¹ * ∑ i, ‖y i‖ ^ 2 ∧ ((y ⬝ᵥ G *ᵥ star y).re = 0 → y ∈ Submodule.span ℂ {p : Fin g → ℂ | ∃ u : Fin g → ℤ, (∀ v : Fin g → ℤ, Bs *ᵥ v = 0 → u ⬝ᵥ v = 0) ∧ p = fun k => (u k : ℂ)}) := by
  first | exact @GlobalTheory.CompanionTheory.RiemannForm.form_bounds | exact GlobalTheory.CompanionTheory.RiemannForm.form_bounds | (intros; apply GlobalTheory.CompanionTheory.RiemannForm.form_bounds <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.first_order_points_commute : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (B : Type) [CommRing B] [IsLocalRing B] (b : Sp B ⟶ S) (A : Type) [CommRing A] (g : B →+* A) (J : Ideal A), J ^ 2 = ⊥ → ∀ x y : Over.mk (spMap g ≫ b) ⟶ G, spMap (Ideal.Quotient.mk J) ≫ x.left = spMap (Ideal.Quotient.mk J) ≫ (1 : Over.mk (spMap g ≫ b) ⟶ G).left → spMap (Ideal.Quotient.mk J) ≫ y.left = spMap (Ideal.Quotient.mk J) ≫ (1 : Over.mk (spMap g ≫ b) ⟶ G).left → ∀ (V : G.left.Opens) (hx : ⊤ ≤ x.left ⁻¹ᵁ V) (hy : ⊤ ≤ y.left ⁻¹ᵁ V) (hxy : ⊤ ≤ (x * y).left ⁻¹ᵁ V) (h1 : ⊤ ≤ (1 : Over.mk (spMap g ≫ b) ⟶ G).left ⁻¹ᵁ V) (f : Γ(G.left, V)), ((x * y).left.appLE V ⊤ hxy).hom f + ((1 : Over.mk (spMap g ≫ b) ⟶ G).left.appLE V ⊤ h1).hom f = (x.left.appLE V ⊤ hx).hom f + (y.left.appLE V ⊤ hy).hom f := by
  first | exact @GlobalTheory.CompanionTheory.Ar.sqzero_add | exact GlobalTheory.CompanionTheory.Ar.sqzero_add | (intros; apply GlobalTheory.CompanionTheory.Ar.sqzero_add <;> assumption)
end

section

namespace GlobalTheory.CompanionTheory.FieldDeg

open ReciprocityTheory.ChartRestriction.G.T0.VariableBasisExtension

theorem finrank_fraction_over_adjoin_X_eq (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [Algebra Ω₀ Ω]
    [FiniteDimensional Ω₀ Ω] (I : Type)
    [Algebra Ω₀ (FractionRing (MvPolynomial I Ω))]
    (hF : algebraMap Ω₀ (FractionRing (MvPolynomial I Ω)) =
      (algebraMap Ω (FractionRing (MvPolynomial I Ω))).comp (algebraMap Ω₀ Ω)) :
    Module.finrank (IntermediateField.adjoin Ω₀ (Set.range fun q : I =>
        algebraMap (MvPolynomial I Ω) (FractionRing (MvPolynomial I Ω)) (MvPolynomial.X q)))
      (FractionRing (MvPolynomial I Ω)) = Module.finrank Ω₀ Ω := by
  classical
  let φ : FractionRing (MvPolynomial I Ω₀) →+* FractionRing (MvPolynomial I Ω) :=
    liftY (L := Ω₀) (E := Ω) (σ := I)
  let : Algebra (FractionRing (MvPolynomial I Ω₀)) (FractionRing (MvPolynomial I Ω)) :=
    φ.toAlgebra
  have hφ : ∀ a : MvPolynomial I Ω₀, φ (algebraMap _ _ a) =
      algebraMap (MvPolynomial I Ω) (FractionRing (MvPolynomial I Ω))
        (MvPolynomial.map (algebraMap Ω₀ Ω) a) := fun a => by
    simp only [φ, liftY, IsFractionRing.lift_algebraMap, RingHom.comp_apply]
  have h1 : Module.finrank (FractionRing (MvPolynomial I Ω₀)) (FractionRing (MvPolynomial I Ω)) =
      Module.finrank Ω₀ Ω := by
    let : Algebra (MvPolynomial I Ω₀) (MvPolynomial I Ω) := MvPolynomial.algebraMvPolynomial
    let b := Module.finBasis Ω₀ Ω
    let j := algebraMap (MvPolynomial I Ω) (FractionRing (MvPolynomial I Ω))
    let v := fun i => j (MvPolynomial.C (b i))
    let S := Submodule.span (FractionRing (MvPolynomial I Ω₀)) (Set.range v)
    have hsmul (q : MvPolynomial I Ω₀) (p : MvPolynomial I Ω) :
        j (q • p) =
          (algebraMap (MvPolynomial I Ω₀) (FractionRing (MvPolynomial I Ω₀)) q) • j p := by
      rw [Algebra.smul_def, Algebra.smul_def]
      change j (_ * p) = φ (algebraMap _ _ q) * j p
      rw [map_mul, hφ]
      rfl
    have hj (p : MvPolynomial I Ω) : j p ∈ S := by
      rw [ReciprocityTheory.ChartRestriction.G.T0.PolynomialCoordinateBasis.eq_sum_crd b p, map_sum]
      simp only [hsmul]
      exact Submodule.sum_mem S fun i _ => S.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
    have hli : LinearIndependent (FractionRing (MvPolynomial I Ω₀)) v := by
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples
        (nonZeroDivisors (MvPolynomial I Ω₀)) Finset.univ g
      choose q hq using fun k => ha k (Finset.mem_univ k)
      have hsum : ∑ k, q k • (MvPolynomial.C (b k) : MvPolynomial I Ω) = 0 := by
        apply IsFractionRing.injective (MvPolynomial I Ω) (FractionRing (MvPolynomial I Ω))
        change j (∑ k, q k • MvPolynomial.C (b k)) = j 0
        rw [map_sum, map_zero]
        simp only [hsmul]
        change ∑ k, (algebraMap (MvPolynomial I Ω₀) (FractionRing (MvPolynomial I Ω₀)) (q k)) •
          v k = 0
        simp_rw [hq, Algebra.smul_def (a : MvPolynomial I Ω₀), mul_smul, ← Finset.smul_sum,
          hg, smul_zero]
      have hqi := (Fintype.linearIndependent_iff.mp
        (ReciprocityTheory.ChartRestriction.G.T0.PolynomialCoordinateBasis.linearIndependent_C
          (σ := I) b)) q hsum i
      have hzero : (a : MvPolynomial I Ω₀) • g i = 0 := by
        rw [← hq i, hqi, map_zero]
      rw [Algebra.smul_def] at hzero
      exact (mul_eq_zero.mp hzero).resolve_left
        (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors a.2)
    have hmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S := by
      intro x hx y hy
      have hxy := Submodule.mul_mem_mul hx hy
      change x * y ∈ Submodule.span _ (Set.range v) * Submodule.span _ (Set.range v) at hxy
      rw [Submodule.span_mul_span] at hxy
      refine (Submodule.span_le.mpr ?_) hxy
      rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨k, rfl⟩, rfl⟩
      change j _ * j _ ∈ S
      rw [← map_mul]
      exact hj _
    have hone : 1 ∈ S := by simpa using hj 1
    let A := S.toSubalgebra hone fun x y hx hy => hmul x hx y hy
    have hfg : A.toSubmodule.FG := by
      rw [Submodule.toSubalgebra_toSubmodule]
      exact Submodule.fg_span (Set.finite_range v)
    have htop : ⊤ ≤ S := by
      intro x _
      obtain ⟨p, q, -, rfl⟩ := IsFractionRing.div_surjective (MvPolynomial I Ω) x
      have hint := IsIntegral.of_mem_of_fg _ hfg (j q) (hj q)
      have hinv := A.inv_mem_of_algebraic (x := ⟨j q, hj q⟩) hint.isAlgebraic
      rw [div_eq_mul_inv]
      exact hmul _ (hj p) _ hinv
    rw [Module.finrank_eq_card_basis (Module.Basis.mk hli htop)]
    simp
  let K := IntermediateField.adjoin Ω₀ (Set.range fun q : I =>
    algebraMap (MvPolynomial I Ω) (FractionRing (MvPolynomial I Ω)) (MvPolynomial.X q))
  have hpoly : ∀ a : MvPolynomial I Ω₀, algebraMap (MvPolynomial I Ω)
      (FractionRing (MvPolynomial I Ω)) (MvPolynomial.map (algebraMap Ω₀ Ω) a) ∈ K := fun a => by
    induction a using MvPolynomial.induction_on with
    | C r =>
      have := K.algebraMap_mem r
      rw [hF] at this
      simpa [MvPolynomial.algebraMap_eq, IsScalarTower.algebraMap_apply Ω (MvPolynomial I Ω) (FractionRing (MvPolynomial I Ω))] using this
    | add p q hp hq => simpa using K.add_mem hp hq
    | mul_X p i hp =>
      have hX : algebraMap (MvPolynomial I Ω) (FractionRing (MvPolynomial I Ω)) (MvPolynomial.X i) ∈ K :=
        IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩
      simpa using K.mul_mem hp hX
  have hmem : ∀ x, φ x ∈ K := fun x => by
    obtain ⟨a, c, -, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial I Ω₀) x
    rw [map_div₀, hφ, hφ]
    exact K.div_mem (hpoly a) (hpoly c)
  have hle : K ≤ Subfield.toIntermediateField φ.fieldRange (fun r => by
      refine ⟨algebraMap (MvPolynomial I Ω₀) _ (MvPolynomial.C r), ?_⟩
      rw [hφ, hF]
      simp [MvPolynomial.map_C, MvPolynomial.algebraMap_eq, IsScalarTower.algebraMap_apply Ω (MvPolynomial I Ω) (FractionRing (MvPolynomial I Ω))]) := by
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨q, rfl⟩
    refine ⟨algebraMap (MvPolynomial I Ω₀) _ (MvPolynomial.X q), ?_⟩
    rw [hφ]; simp
  let ψ : FractionRing (MvPolynomial I Ω₀) →+* K := φ.codRestrict K hmem
  have hψ : Function.Bijective ψ := by
    refine ⟨fun x y h => φ.injective (congrArg Subtype.val h), fun y => ?_⟩
    obtain ⟨x, hx⟩ := hle y.2
    exact ⟨x, Subtype.ext hx⟩
  rw [← h1]
  exact (Algebra.finrank_eq_of_equiv_equiv (RingEquiv.ofBijective ψ hψ) (RingEquiv.refl _)
    (by ext x; rfl)).symm

theorem finrank_adjoin_vars :
    ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (fn : Ω₀ →+* Ω) (I : Type) (d : ℕ),
      0 < d →
      (letI : Algebra Ω₀ Ω := fn.toAlgebra;
       Module.finrank Ω₀ Ω = d) →
      letI : Algebra Ω₀ (FractionRing (MvPolynomial I Ω)) :=
        ((algebraMap Ω (FractionRing (MvPolynomial I Ω))).comp fn).toAlgebra;
      Module.finrank (IntermediateField.adjoin Ω₀ (Set.range fun q : I =>
        algebraMap (MvPolynomial I Ω) (FractionRing (MvPolynomial I Ω)) (MvPolynomial.X q)))
        (FractionRing (MvPolynomial I Ω)) = d := by
  intro Ω₀ Ω _ _ fn I d hd hfin
  let : Algebra Ω₀ Ω := fn.toAlgebra
  have : FiniteDimensional Ω₀ Ω := Module.finite_of_finrank_pos (hfin ▸ hd)
  let : Algebra Ω₀ (FractionRing (MvPolynomial I Ω)) :=
    ((algebraMap Ω (FractionRing (MvPolynomial I Ω))).comp fn).toAlgebra
  exact (finrank_fraction_over_adjoin_X_eq Ω₀ Ω I rfl).trans hfin

end GlobalTheory.CompanionTheory.FieldDeg
end

section


theorem _root_.GlobalTheory.T.trace_integral_subring_extension : ∀ (K L : Type) [Field K] [Field L] [CharZero K] (φ : K →+* L) (B₀ : Finset L) (x : L), (letI := φ.toAlgebra; FiniteDimensional K L) → ∃ B' : Finset K, ∀ A' : Subring K, (↑B' : Set K) ⊆ A' → ∃ (A : Subring L) (hA : ∀ a : A', φ a ∈ A) (_ : (↑B₀ : Set L) ⊆ A) (hx : x ∈ A) (ht : (letI := φ.toAlgebra; Algebra.trace K L x) ∈ A'), ∀ (C : Type) [Field C] [IsAlgClosed C] (ev : A' →+* C), (∀ a, IsAlgebraic ℤ (ev a)) → ∃ (n : ℕ) (ev' : Fin n → (A →+* C)), (∀ j (a : A'), ev' j ⟨φ a, hA a⟩ = ev a) ∧ (∀ j a, IsAlgebraic ℤ (ev' j a)) ∧ ev ⟨_, ht⟩ = ∑ j, ev' j ⟨x, hx⟩ := by
  first | exact @GlobalTheory.CompanionTheory.TraceSpec.trace_specialisation | exact GlobalTheory.CompanionTheory.TraceSpec.trace_specialisation | (intros; apply GlobalTheory.CompanionTheory.TraceSpec.trace_specialisation <;> assumption)
end

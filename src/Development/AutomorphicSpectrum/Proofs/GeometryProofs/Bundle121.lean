module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusAff
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeFlagVectorBundle
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle007
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle107
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle108
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle110
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointExistsUniqueEmbedding
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle021
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle111
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Connected
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle086
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle087
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv

@[expose] public section

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt

theorem lifts_eq_frobenius_powers : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∃ (σ' : MulChar F RC) (ee : Sg → ℕ), GlobalTheory.CompanionTheory.Ar.GR.IsFund p σ' ∧ (∀ τ a, χ τ a = ((σ' ^ p ^ ee τ) a : RC)) ∧ ∀ τ, σ' ^ p ^ ee (φ' τ) = σ' ^ p ^ (ee τ + 1) :=
  @PositivityTheory.Xgn.test_character_exists

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

namespace GlobalTheory.CompanionTheory.Ar.RootHt.ArchB

private theorem smoothOfRelativeDimension_restrict_of_le {A S : Scheme.{0}} (f : A ⟶ S) {n : ℕ} {V W : A.Opens} (h : V ≤ W)
    (hW : SmoothOfRelativeDimension n (W.ι ≫ f)) : SmoothOfRelativeDimension n (V.ι ≫ f) := by
  have := smoothOfRelativeDimension_comp 0 n (A.homOfLE h) (W.ι ≫ f)
  rw [zero_add, ← Category.assoc, Scheme.homOfLE_ι] at this
  exact this

private theorem relDim_eq_of_mem_of_mem {A S : Scheme.{0}} (f : A ⟶ S) {n m : ℕ} {V W : A.Opens}
    (hV : SmoothOfRelativeDimension n (V.ι ≫ f)) (hW : SmoothOfRelativeDimension m (W.ι ≫ f))
    {x : A} (hxV : x ∈ V) (hxW : x ∈ W) : n = m :=
  ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ (smoothOfRelativeDimension_restrict_of_le f inf_le_left hV) (smoothOfRelativeDimension_restrict_of_le f inf_le_right hW)
    ⟨x, hxV, hxW⟩

theorem reldim_eq_of_two_pullbacks {P A S : Scheme.{0}} {f : A ⟶ S} {b : A ⟶ S} {p : P ⟶ A} {a₁ a₂ : P ⟶ A}
    (h₁ : IsPullback a₁ p f b) (h₂ : IsPullback a₂ p f b) {n₁ n₂ : ℕ} {W₁ W₂ : A.Opens}
    (d₁ : SmoothOfRelativeDimension n₁ (W₁.ι ≫ f)) (d₂ : SmoothOfRelativeDimension n₂ (W₂.ι ≫ f))
    (z : P) (hz₁ : a₁ z ∈ W₁) (hz₂ : a₂ z ∈ W₂) : n₁ = n₂ := by
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange n₁
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange n₂
  have e₁ : SmoothOfRelativeDimension n₁ ((a₁ ⁻¹ᵁ W₁).ι ≫ p) :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension n₁)
      ((isPullback_morphismRestrict a₁ W₁).paste_vert h₁) d₁
  have e₂ : SmoothOfRelativeDimension n₂ ((a₂ ⁻¹ᵁ W₂).ι ≫ p) :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension n₂)
      ((isPullback_morphismRestrict a₂ W₂).paste_vert h₂) d₂
  exact relDim_eq_of_mem_of_mem p e₁ e₂ hz₁ hz₂

theorem isPullback_fst_snd {X : Scheme.{0}} (G : Over X) :
    IsPullback (fst G G) (snd G G) (toUnit G) (toUnit G) := by
  exact IsPullback.of_is_product (tensorProductIsBinaryProduct G G) isTerminalTensorUnit

theorem isPullback_mul_snd {X : Scheme.{0}} (G : Over X) [GrpObj G] :
    IsPullback (fst G G * snd G G) (snd G G) (toUnit G) (toUnit G) := by
  refine IsPullback.of_is_product (c := BinaryFan.mk (fst G G * snd G G) (snd G G)) ?_ isTerminalTensorUnit
  refine BinaryFan.IsLimit.mk _ (fun u v => lift (u * v⁻¹) v) ?_ ?_ ?_
  · intro T u v
    simp [comp_mul]
  · intro T u v
    simp
  · intro T u v m h₁ h₂
    simp only [BinaryFan.mk_fst, BinaryFan.mk_snd] at h₁ h₂
    have h₃ : m ≫ fst G G * v = u := by
      rw [← h₂]
      exact (comp_mul m (fst G G) (snd G G)).symm.trans h₁
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · simpa using eq_mul_inv_of_mul_eq h₃
    · simpa using h₂

theorem toUnit_left {X : Scheme.{0}} (G : Over X) : (toUnit G).left = G.hom := by
  simpa using Over.w (toUnit G)

theorem reldim_eq_unit {X : Scheme.{0}} (G : Over X) [GrpObj G] {n m : ℕ} {W V : G.left.Opens}
    (dW : SmoothOfRelativeDimension n (W.ι ≫ G.hom)) (dV : SmoothOfRelativeDimension m (V.ι ≫ G.hom))
    (g : G.left) (hg : g ∈ W) (hV : eSec G (G.hom g) ∈ V) : n = m := by
  have h₁ := (isPullback_fst_snd G).map (Over.forget X)
  have h₂ := (isPullback_mul_snd G).map (Over.forget X)
  simp only [Over.forget_map, toUnit_left] at h₁ h₂
  have p₁ : (fst G G).left ((lift (𝟙 G) (𝟙 G)⁻¹).left g) = g := by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_fst]
    simp
  have p₂ : (fst G G * snd G G).left ((lift (𝟙 G) (𝟙 G)⁻¹).left g) = (η[G]).left (G.hom g) := by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, comp_mul, lift_fst, lift_snd, mul_inv_cancel,
      Hom.one_def, Over.comp_left, Scheme.Hom.comp_apply, toUnit_left]
  refine reldim_eq_of_two_pullbacks h₁ h₂ dW dV ((lift (𝟙 G) (𝟙 G)⁻¹).left g) ?_ ?_
  · show (fst G G).left ((lift (𝟙 G) (𝟙 G)⁻¹).left g) ∈ W
    rw [p₁]
    exact hg
  · show (fst G G * snd G G).left ((lift (𝟙 G) (𝟙 G)⁻¹).left g) ∈ V
    rw [p₂]
    unfold eSec at hV
    exact hV

private theorem smoothOfRelativeDimension_of_local {A S : Scheme.{0}} (f : A ⟶ S) (n : ℕ)
    (h : ∀ x : A, ∃ W : A.Opens, x ∈ W ∧ SmoothOfRelativeDimension n (W.ι ≫ f)) :
    SmoothOfRelativeDimension n f := by
  rw [smoothOfRelativeDimension_iff]
  intro x
  obtain ⟨W, hxW, hW⟩ := h x
  obtain ⟨U, hU, V, hV, hxV, e, hstd⟩ := (smoothOfRelativeDimension_iff n (W.ι ≫ f)).1 hW ⟨x, hxW⟩
  have e₁ : W.ι ''ᵁ V ≤ f ⁻¹ᵁ U := by
    rintro _ ⟨v, hv, rfl⟩
    exact e hv
  have e₂ : V ≤ W.ι ⁻¹ᵁ (W.ι ''ᵁ V) := fun v hv => ⟨v, hv, rfl⟩
  have hcomp := Scheme.Hom.appLE_comp_appLE W.ι f U (W.ι ''ᵁ V) V e₁ e₂
  have hiso : W.ι.appLE (W.ι ''ᵁ V) V e₂ = (W.ι.appIso V).hom := (Scheme.Hom.appIso_hom' W.ι V).symm
  have key : f.appLE U (W.ι ''ᵁ V) e₁ = (W.ι ≫ f).appLE U V e ≫ (W.ι.appIso V).inv := by
    rw [← hcomp, hiso, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine ⟨U, hU, W.ι ''ᵁ V, hV.image_of_isOpenImmersion W.ι, ⟨⟨x, hxW⟩, hxV, rfl⟩, e₁, ?_⟩
  rw [key, CommRingCat.hom_comp]
  have h0 : RingHom.IsStandardSmoothOfRelativeDimension 0 (W.ι.appIso V).inv.hom :=
    RingHom.IsStandardSmoothOfRelativeDimension.equiv (W.ι.appIso V).symm.commRingCatIsoToRingEquiv
  have h1 := h0.comp hstd
  rwa [zero_add] at h1

theorem smoothGrp_relDim : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] [Smooth G.hom],
    (∀ q : X, genPt ξ ⤳ q) → ∃ g : ℕ, SmoothOfRelativeDimension g G.hom := by
  intro X Ω _ ξ G _ _ hgen
  obtain ⟨n₀, W₀, hW₀, d₀⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_dim G.hom (eSec G (genPt ξ))
  refine ⟨n₀, smoothOfRelativeDimension_of_local G.hom n₀ fun g => ?_⟩
  obtain ⟨n, W, hgW, dW⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_dim G.hom g
  obtain ⟨m, V, hV, dV⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_dim G.hom (eSec G (G.hom g))
  have h₁ : n = m := reldim_eq_unit G dW dV g hgW hV
  have hsp : eSec G (genPt ξ) ⤳ eSec G (G.hom g) := (hgen (G.hom g)).map (eSec G).base.hom.continuous
  have h₂ : m = n₀ := relDim_eq_of_mem_of_mem G.hom dV d₀ (hsp.mem_open V.isOpen hV) hW₀
  rw [h₁, h₂] at dW
  exact ⟨W, hgW, dW⟩

end GlobalTheory.CompanionTheory.Ar.RootHt.ArchB
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric


theorem _root_.GlobalTheory.T.holomorphic_chart_near_point : ∀ (K : Type) [Field K] (σ : K →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp K) (d : ℕ), SmoothOfRelativeDimension d s → ∀ (x : Sp ℂ ⟶ X) (W₀ : X.Opens), x ≫ s = spMap σ → ⊤ ≤ x ⁻¹ᵁ W₀ → IsDomain (X.presheaf.stalk (centre x)) → ∃ (V : X.Opens) (hV : IsAffineOpen V) (ψ : (Fin d → ℂ) → (Γ(X, V) →+* ℂ)), V ≤ W₀ ∧ IsHolPts (ball 0 1) ψ ∧ spMap (ψ 0) ≫ hV.fromSpec = x ∧ (∀ z ∈ ball (0 : Fin d → ℂ) 1, (spMap (ψ z) ≫ hV.fromSpec) ≫ s = spMap σ) ∧ ∀ g : Γ(X, V), (∀ z ∈ ball (0 : Fin d → ℂ) 1, ψ z g = 0) → g = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.SmoothChart.exists_polydisc_chart | exact GlobalTheory.CompanionTheory.Ar.Flat.SmoothChart.exists_polydisc_chart | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.SmoothChart.exists_polydisc_chart <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj


theorem _root_.GlobalTheory.T.coords_finite_type_over_integers : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X), (∀ q : X, genPt ξ ⤳ q) →
    CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → LocallyOfFiniteType (toZ X) ∧ QuasiCompact (toZ X) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TorusUnif.closure_finiteType_over_int | exact GlobalTheory.CompanionTheory.Ar.TorusUnif.closure_finiteType_over_int | (intros; apply GlobalTheory.CompanionTheory.Ar.TorusUnif.closure_finiteType_over_int <;> assumption)
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.complex_point_existsUnique_embedding : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω), OverInt y φ → ∀ z ∈ mcPts (mCoordIdeal y), ∃! σ : F →+* ℂ, PtOver y φ σ z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.existsUnique_ptOver | exact GlobalTheory.CompanionTheory.Ar.Flat.existsUnique_ptOver | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.existsUnique_ptOver <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

theorem _root_.GlobalTheory.T.lattice_flag_vector_bundle : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (T : Set (Cpt ξ)) (g r : ℕ) (W : Submodule Ω E) (b₀ : Fin r → E), LinearIndependent Ω b₀ → (∀ k, b₀ k ∈ W) → L.IsVBOn T g W → (∀ n : ℕ, ∃ s W', (L.map (flagStep Ω b₀ n).mkQ).IsVBOn T s W') → (L.inter (Submodule.span Ω (Set.range b₀))).IsFlagVBOn T b₀ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.isFlagVBOn_inter_of_steps | exact GlobalTheory.CompanionTheory.Ar.isFlagVBOn_inter_of_steps | (intros; apply GlobalTheory.CompanionTheory.Ar.isFlagVBOn_inter_of_steps <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.hodge_component_twist_frame_compat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F)
    (Y : Model Xo c β) (Y' : Model Xo c β') (g : HostAut H) (Φ : Xo.X ≅ Xo.X)
    (n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K]
    (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y) (A' : HodgeCpt Y' S y)
    (e : A'.X ≅ A.X) (x x' : Sp Ω ⟶ Xo.XF c),
    Mono (spMap β) → Mono (spMap β') → Φ.hom ≫ Xo.s = Xo.s → A'.ξ ≫ e.hom = A.ξ → A.ξ ≫ A.f = x ≫ Y.j → A'.ξ ≫ A'.f = x' ≫ Y'.j →
    x' ≫ pullback.fst _ _ = x ≫ pullback.fst _ _ ≫ Φ.hom → x' ≫ pullback.snd _ _ = x ≫ pullback.snd _ _ →
    A.cst = A'.cst → x ≫ pullback.snd _ _ = spMap A.cst → (∀ p ∈ S, A'.R p = A.R p) →
    ∀ z : Sp ℂ ⟶ A'.X, A'.Interior z ↔ A.Interior (z ≫ e.hom) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TwistInterior.interior_iff | exact GlobalTheory.CompanionTheory.Ar.TwistInterior.interior_iff | (intros; apply GlobalTheory.CompanionTheory.Ar.TwistInterior.interior_iff <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.twist_inverse_iso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : HostAut H) (a : TwIso D g), ∃ a' : TwIso D g.symm, ∀ (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), (∀ (h : TwOK o g a) (h' : TwOK (twistObj o g a h) g.symm a'), Nonempty (ObjMap (twistObj (twistObj o g a h) g.symm a' h') o (𝟙 S))) ∧ ∀ (h : TwOK o g.symm a') (h' : TwOK (twistObj o g.symm a' h) g a), Nonempty (ObjMap (twistObj (twistObj o g.symm a' h) g a h') o (𝟙 S)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.twBack | exact GlobalTheory.CompanionTheory.Ar.twBack | (intros; apply GlobalTheory.CompanionTheory.Ar.twBack <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem propZ_numerical : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s] (ϖ : O), Irreducible ϖ → Function.Injective (algebraMap O Ω) → ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → IsCptGen ξ → NormalCpt ξ → _root_.IsConnected (zeroSet ξ (algebraMap O Ω ϖ)) → ∀ (L : Lat ξ Ω) (σ : Ω), L.IsVB 1 ⊤ → NumTrivMod L (algebraMap O Ω ϖ) → (∀ p ∈ genFibre O ξ, L.IsGenAt p σ) → ∃ (M : ℕ) (a : ℤ), 0 < M ∧ ∀ p : Cpt ξ, OrderAt L σ (algebraMap O Ω ϖ) M a p :=
  @PositivityTheory.Xgn.normal_proper_line_order

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

theorem _root_.GlobalTheory.T.holomorphic_disc_in_affine_open : ∀ (X : Scheme.{0}) (W : X.Opens) (hW : IsAffineOpen W) (n : ℕ) (p : (Fin n → ℂ) → (Sp ℂ ⟶ X)), IsHolTo (Metric.ball 0 1) p → ⊤ ≤ p 0 ⁻¹ᵁ W → ∃ (ρ : ℝ) (ψ : (Fin n → ℂ) → (Γ(X, W) →+* ℂ)), 0 < ρ ∧ ρ ≤ 1 ∧ Flat.IsHolPts (Metric.ball 0 1) ψ ∧ ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, spMap (ψ z) ≫ hW.fromSpec = p ((ρ : ℂ) • z) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HolFac.exists_ringMaps_of_hol | exact GlobalTheory.CompanionTheory.Ar.HolFac.exists_ringMaps_of_hol | (intros; apply GlobalTheory.CompanionTheory.Ar.HolFac.exists_ringMaps_of_hol <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric


theorem _root_.GlobalTheory.T.exists_action_complex_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (y : Sp ℂ ⟶ Xo.XF c), ∃ (EC : Type) (_ : AddCommGroup EC) (_ : Module ℂ EC) (N : LieModel Y.t.G (y ≫ Y.j) EC) (ρ : 𝓞 E →+* Module.End ℂ EC), N.IsActOf Y.t.act.act ρ ∧ ∀ (ch : 𝓞 E →+* ℂ) (n : ℕ) (v : Vecs y n) (w : Fin n → EC), LieMult Xo.univ.t.act (under y) ch n → (∀ i, SameVec Y y (v i) (N.pt (w i))) → LinearIndependent ℂ w → (∀ i, w i ∈ eigSp ρ ch) → IsEigFrame Xo.univ.t.act (under y) ch v := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_lieModel_tied_isEigFrame | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_lieModel_tied_isEigFrame | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_lieModel_tied_isEigFrame <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.exists_clopen_irreducible_cpt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (u : Xo.XF c), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → ∃ (U : Set (Xo.XF c)) (_ : CptOver Y U), u ∈ U ∧ IsClopen U ∧ IsIrreducible U := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_cptOver_mem_isClopen_isIrreducible | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_cptOver_mem_isClopen_isIrreducible | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_cptOver_mem_isClopen_isIrreducible <;> assumption)
end

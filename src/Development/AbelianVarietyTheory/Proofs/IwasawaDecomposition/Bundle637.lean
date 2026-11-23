module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle232
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ContinuousOnThetaFrameValueHolomorphicFamily
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle064
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle046
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle029
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GradedLineBundleExists
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionField
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle627
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Basify
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
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle625
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle231
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle013
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle624
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivLift

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open GlobalTheory.LineNorm GlobalTheory.TrueGeo.SmallSec

namespace GlobalTheory.LineNorm.Glue

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

variable {Δ : Y.Dv} {t : Y.X → Y.Fnˣ} {φ : PtFn Y}

theorem below_mem (N : TrueGeo.Model Y) {v : HeightOneSpectrum (𝓞 F)} {e : Ext v} {y : AlgPt Y}
    {yt : Sp e.O ⟶ N.X} (h : spMap e.O.subtype ≫ yt = y.1 ≫ N.j) {W : N.X.Opens} (hW : ⊤ ≤ yt ⁻¹ᵁ W) :
    N.j (below y.1) ∈ W := by
  change (y.1 ≫ N.j) _ ∈ W
  rw [← h]
  exact hW (x := spMap e.O.subtype _) trivial

theorem w_le_one (N : TrueGeo.Model Y) {v : HeightOneSpectrum (𝓞 F)} {e : Ext v} {y : AlgPt Y}
    {yt : Sp e.O ⟶ N.X} (h : spMap e.O.subtype ≫ yt = y.1 ≫ N.j) {W : N.X.Opens} (hW : ⊤ ≤ yt ⁻¹ᵁ W)
    (g : Γ(N.X, W)) (hg : genericPoint Y.X ∈ N.j ⁻¹ᵁ W) :
    e.w (valAt y.1 (fnOf (N.j ⁻¹ᵁ W) hg (N.j.app W g))) ≤ 1 := by
  have hb : below y.1 ∈ N.j ⁻¹ᵁ W := below_mem N h hW
  have ht : ⊤ ≤ y.1 ⁻¹ᵁ (N.j ⁻¹ᵁ W) := fun p _ => by
    change (y.1 ≫ N.j) p ∈ W
    rw [← h]
    exact hW (x := spMap e.O.subtype p) trivial
  have hev := OfModel.eval_pull e.O.subtype N.j y.1 yt h (U := W) (W := N.j ⁻¹ᵁ W) le_rfl ht hW g
  rw [OfModel.valAt_fnOf _ hb ht, Scheme.Hom.app_eq_appLE, hev, ← e.mem_O]
  exact Subtype.prop _

end GlobalTheory.LineNorm.Glue
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct

namespace GlobalTheory.ThetaScalar

open GlobalTheory.HolGen Formalism.L2.PjFree GlobalTheory.Frames

theorem continuousAt_scalar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)) (r : ℕ) (M : _root_.GlobalTheory.FrameUnif.ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k) (A : Type) [CommRing A] [Algebra c.F A] (yA : FrPt Xo c A) (m : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → (A →ₐ[c.F] CAt σ)) (y : (Fin m → ℂ) → FrPt Xo c (CAt σ)) (P : (Fin m → ℂ) → ((F.Di k).La →+ (Fin g → ℂ))) (x : (Fin m → ℂ) → (Fin T.m → ℂ)) (a : (Fin m → ℂ) → ℂ), IsOpen B → (∀ a, DifferentiableOn ℂ (fun b => Formalism.L2.PjFree.toC (φ b a)) B) → (∀ b ∈ B, FrMap (φ b) yA (y b)) → IsHolPeriods (F.Di k) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) B P → (∀ b ∈ B, x b ∈ T.co ⁻¹' (M.X k).dom ∧ T.Pf (T.co (x b)) = P b ∧ IsThetaPt T (x b) (a b) (y b)) → ∀ b₀ ∈ B, ContinuousAt x b₀ → ContinuousAt a b₀ := by
  intro E _ _ _ H Dw l Xo c σ g e F r M k T A _ _ yA m B ψ y P x a hB hψ hb hP hx b₀ hb₀ hx₀
  have hT : Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  have hxu : ∀ b ∈ B, (y b).x = F.u k (P b) := fun b h => by
    rw [← (hx b h).2.1]
    exact (hx b h).2.2.1
  let φ : (Fin m → ℂ) → (A →+* ℂ) := fun b => (ψ b).toRingHom
  have hux : ∀ b ∈ B, F.u k (P b) = (y b).x := fun b h => (hxu b h).symm
  obtain ⟨pm₀, p₁, p₂, p₃⟩ := (hb b₀ hb₀).2.2
  obtain ⟨e₀, j, hne⟩ := exists_val_ne hT (φ b₀) yA.x (y b₀).x _ (hux b₀ hb₀) yA.s (y b₀).s pm₀ p₁ p₂ p₃ (y b₀).gen
  obtain ⟨w₀, rfl⟩ := F.ex_onto k _ (hP.1 b₀ hb₀) e₀
  have hq₁ : ∀ b ∈ B, ∃ q : Sp ℂ ⟶ Gx yA.x, q ≫ Formalism.L2.PjFree.gxFst yA.x = (F.ex k (P b) w₀).left ∧
      q ≫ Formalism.L2.PjFree.gxSnd yA.x = spMap (φ b) := fun b h =>
    exists_pt _ _ _ (((hb b h).1.symm.trans (hux b h).symm).trans (Over.w (F.ex k (P b) w₀)).symm)
  have hq₂ : ∀ b, ∃ q : Sp ℂ ⟶ Gx yA.x, b ∈ B → q ≫ Formalism.L2.PjFree.gxFst yA.x = (F.ex k (P b) w₀).left ∧
      q ≫ Formalism.L2.PjFree.gxSnd yA.x = spMap (φ b) := fun b => by
    by_cases h : b ∈ B
    · exact (hq₁ b h).imp fun _ h' _ => h'
    · exact ⟨(hq₁ b₀ hb₀).choose, fun h' => absurd h' h⟩
  choose q hq using hq₂
  have hι : Differentiable ℂ (fun b : Fin m → ℂ => ((b, w₀) : (Fin m → ℂ) × (Fin g → ℂ))) := by fun_prop
  have hol : IsHolTo B q := by
    refine HolPullback.isHolTo_of_components _ B _ _ _ _ (Formalism.L2.PjFree.gxSnd yA.x) (Formalism.L2.PjFree.gxFst yA.x) yA.x Xo.univ.t.G.hom q
      (IsPullback.of_hasPullback yA.x Xo.univ.t.G.hom) hB ?_ ?_
    · exact LocLift.isHolTo_congr (ThetaValueCont.isHolTo_spMap hB φ hψ) fun b h => (hq b h).2
    · exact LocLift.isHolTo_congr (LocLift.isHolTo_comp (F.hol k _ B _ hB hP).2 hB hι.differentiableOn
        fun b h => ⟨h, trivial⟩) fun b h => (hq b h).1
  have hW := (hol ((Gx yA.x).basicOpen (yA.s.f (fun _ => j))) 0).1
  set W := {b ∈ B | ⊤ ≤ q b ⁻¹ᵁ (Gx yA.x).basicOpen (yA.s.f (fun _ => j))} with hWd
  have hb₀W : b₀ ∈ W := ⟨hb₀, (top_le_preimage_basicOpen_iff _ _ _).2 (hne _ (hq b₀ hb₀).1 (hq b₀ hb₀).2)⟩
  have vnz : ∀ b ∈ W, valAt' (q b) ((PPx yA.x).U (fun _ => j)) (yA.s.f (fun _ => j)) ≠ 0 := fun b h =>
    (top_le_preimage_basicOpen_iff _ _ _).1 h.2
  have m₁ : ∀ b ∈ W, ⊤ ≤ q b ⁻¹ᵁ (PPx yA.x).U (fun _ => j) := fun b h =>
    top_le_preimage_of_valAt'_ne_zero _ (vnz b h)
  have m₂ : ∀ b ∈ W, ⊤ ≤ (F.ex k (P b) w₀).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun b h => by
    rw [← (hq b h.1).1]
    exact (chart_iff _ _ _).1 (m₁ b h)
  have m₃ : ∀ b ∈ W, ⊤ ≤ (F.ex k (T.Pf (T.co (x b))) w₀).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun b h => by
    rw [(hx b h.1).2.1]
    exact m₂ b h
  have hO : IsOpen (T.co ⁻¹' (M.X k).dom) := (FourierCoefficientDomain.isOpen_dom (M.X k)).preimage T.co.continuous
  have hθ := (ThetaHalf.thetaChar_holomorphic_ne_zero g T.c₁ T.c₂ T.half₁ T.half₂).2 T.m _ T.h T.ta hO
    (fun b h => ⟨(T.norm b h).2.1, (T.norm b h).2.2.1⟩) T.hol
  have hκ : ContinuousWithinAt (fun b : Fin m → ℂ => ((x b, w₀) : (Fin T.m → ℂ) × (Fin g → ℂ))) W b₀ :=
    (hx₀.prodMk continuousAt_const).continuousWithinAt
  have d₁ : ContinuousWithinAt (fun b => thetaChar (T.ta (x b)) T.c₁ T.c₂ (T.h (x b) *ᵥ w₀)) W b₀ :=
    ContinuousWithinAt.comp (f := fun b : Fin m → ℂ => ((x b, w₀) : (Fin T.m → ℂ) × (Fin g → ℂ)))
      (g := fun bz : (Fin T.m → ℂ) × (Fin g → ℂ) => thetaChar (T.ta bz.1) T.c₁ T.c₂ (T.h bz.1 *ᵥ bz.2))
      (hθ.continuousOn _ ⟨(hx b₀ hb₀).1, trivial⟩) hκ fun b h => ⟨(hx b h.1).1, trivial⟩
  have d₂ : ContinuousWithinAt (fun b => T.fr j (x b, w₀)) W b₀ :=
    ContinuousWithinAt.comp (f := fun b : Fin m → ℂ => ((x b, w₀) : (Fin T.m → ℂ) × (Fin g → ℂ))) (g := T.fr j)
      ((T.fr_hol j).continuousOn _ ⟨(hx b₀ hb₀).1, m₃ b₀ hb₀W⟩) hκ fun b h => ⟨(hx b h.1).1, m₃ b h⟩
  have d₃ : DifferentiableOn ℂ (fun b => valAt' (q b) ((PPx yA.x).U (fun _ => j)) (yA.s.f (fun _ => j))) W :=
    (hol _ _).2.mono fun b h => ⟨h.1, m₁ b h⟩
  have key : ∀ b ∈ W, valAt' (q b) ((PPx yA.x).U (fun _ => j)) (yA.s.f (fun _ => j)) =
      a b * (thetaChar (T.ta (x b)) T.c₁ T.c₂ (T.h (x b) *ᵥ w₀) * T.fr j (x b, w₀)) := fun b h => by
    obtain ⟨-, -, pm, p₁, p₂, p₃⟩ := hb b h.1
    obtain ⟨pt, e₁, e₂⟩ := exists_pt (R := ℂ) (y b).x (𝟙 _) (F.ex k (P b) w₀).left
      (((Category.id_comp _).trans (hxu b h.1)).trans (Over.w (F.ex k (P b) w₀)).symm)
    have e₁' : pt ≫ Formalism.L2.PjFree.gxFst (y b).x = (F.ex k (T.Pf (T.co (x b))) w₀).left := by
      rw [(hx b h.1).2.1]
      exact e₁
    rw [← mul_assoc]
    refine Eq.trans ?_ ((hx b h.1).2.2.2.2 j w₀ pt e₁' e₂ (m₃ b h))
    refine (val_pull (φ b) yA.x (y b).x yA.s (y b).s pm p₁ p₂ p₃ _ pt (q b)
      ((hq b h.1).1.trans e₁.symm) e₂ (hq b h.1).2 ((chart_iff _ _ _).2 ?_)).symm
    rw [e₁]
    exact m₂ b h
  have nz : ∀ b ∈ W, thetaChar (T.ta (x b)) T.c₁ T.c₂ (T.h (x b) *ᵥ w₀) * T.fr j (x b, w₀) ≠ 0 := fun b h =>
    right_ne_zero_of_mul (key b h ▸ vnz b h)
  have d : ContinuousWithinAt a W b₀ :=
    ((d₃.continuousOn b₀ hb₀W).mul ((d₁.mul d₂).inv₀ (nz b₀ hb₀W))).congr
      (fun b h => ((mul_inv_eq_iff_eq_mul₀ (nz b h)).2 (key b h)).symm)
      ((mul_inv_eq_iff_eq_mul₀ (nz b₀ hb₀W)).2 (key b₀ hb₀W)).symm
  exact d.continuousAt (hW.mem_nhds hb₀W)

end GlobalTheory.ThetaScalar
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory.LieMet GlobalTheory.LocM
open GlobalTheory.GradedPieces GlobalTheory.Points

namespace GlobalTheory.TotalFrame

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_basis_sigma {O S M J : Type} [CommRing O] [CommRing S] [AddCommGroup M] [Module S M] [Fintype J]
    {χ : J → O →+* S} (h : EigenSplit.IsSplitting χ) (ρ : O →+* Module.End S M) {m : J → ℕ}
    (u : ∀ σ, Fin (m σ) → M) (li : ∀ σ, LinearIndependent S (u σ))
    (hs : ∀ σ, Submodule.span S (Set.range (u σ)) = EigenSplit.eigenSub ρ (χ σ)) :
    ∃ b : Module.Basis (Σ σ, Fin (m σ)) S M, ∀ σ a, b ⟨σ, a⟩ = u σ a := by
  classical
  have hi := EigenSplit.isInternal_eigenSub h ρ
  simp only [← hs] at hi
  exact ⟨hi.collectedBasis fun σ => Module.Basis.span (li σ), fun σ a => by
    rw [DirectSum.IsInternal.collectedBasis_coe]
    exact congrArg Subtype.val (Module.Basis.span_apply (li σ) a)⟩

section Tangent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ X} {m : ℕ}

theorem exists_basis {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} (hv : ∀ i, IsTanAtG t x (v i))
    (hb : ∀ w, IsTanAtG t x w → ∃! cf, IsCombAtG t x v cf w) :
    ∃ b : Module.Basis (Fin m) S (TanM x t.G), ∀ i, b i = tanOf (hv i) := by
  refine ⟨Module.Basis.mk (v := fun i => tanOf (hv i)) (Fintype.linearIndependent_iffₛ.2 fun c c' h => congrFun
    ((hb _ (isTan_tv (∑ i, c i • tanOf (hv i)))).unique ((isComb_iff (fun i => tanOf (hv i)) c _).2 rfl)
      ((isComb_iff (fun i => tanOf (hv i)) c' _).2 h))) fun w _ => ?_, fun i => Module.Basis.mk_apply _ _ i⟩
  obtain ⟨a, ha, -⟩ := hb _ (isTan_tv w)
  rw [(isComb_iff (fun i => tanOf (hv i)) a w).1 ha]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem exists_basis_map {J : Type} [Fintype J] (b : Module.Basis J S (TanM x t.G)) (φ : S →+* T) {x' : Sp T ⟶ X}
    (hx : spMap φ ≫ x = x') :
    ∃ b' : Module.Basis J T (TanM x' t.G), ∀ i, (tv (b' i)).left = spMap (dualMap φ) ≫ (tv (b i)).left := by
  let e := Fintype.equivFin J
  have hb : ∀ w, IsTanAtG t x w → ∃! cf, IsCombAtG t x (fun i => (tv (b.reindex e i)).left) cf w := fun w hw =>
    ⟨(b.reindex e).repr (tanOf hw), (isComb_iff _ _ (tanOf hw)).2 ((b.reindex e).sum_repr _).symm, fun a ha => by
      rw [(isComb_iff _ _ (tanOf hw)).1 ha, Module.Basis.repr_sum_self]⟩
  obtain ⟨b', hb'⟩ := exists_basis (fun i => isTan_map φ hx (isTan_tv (b.reindex e i)))
    (basis_map φ hx (fun i => isTan_tv _) hb)
  refine ⟨b'.reindex e.symm, fun i => ?_⟩
  rw [Module.Basis.reindex_apply, hb', left_tanOf, Module.Basis.reindex_apply, Equiv.symm_symm, Equiv.symm_apply_apply]

theorem dualMap_epsMul (φ : S →+* T) (a : S) {Y : Scheme.{0}} (v : Sp (DualNumber S) ⟶ Y) :
    spMap (dualMap φ) ≫ spMap (epsMul a) ≫ v = spMap (epsMul (φ a)) ≫ spMap (dualMap φ) ≫ v := by
  rw [← Category.assoc, ← Category.assoc, spMap_comp_spMap, spMap_comp_spMap]
  congr 2
  refine RingHom.ext fun z => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap, epsMul, mul_comm]

variable {Dw : Datum H} {l : Level H} {c : Coeff l} {w : Vecs Dw t S} {χ : (E →+* ℂ) → 𝓞 E →+* S}


variable (c x w χ) in
def FramesSeparate : Prop :=
  ∀ r s : S, (∀ (k : Type) [Field k] (φ : S →+* k) (f : c.F →+* k), IsFrame t f (spMap φ ≫ x) (w.bc φ) →
    (∀ σ a, f (embK c σ a) = φ (χ σ a)) → φ r = φ s) → r = s

theorem span_eq_eigenSub (hw : FramesSeparate x c w χ) (σ : E →+* ℂ) (ht : ∀ i, IsTanAtG t x (w σ i))
    {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} (e : Fin (Dw.mult σ) ↪ Fin m) (he : ∀ i, v (e i) = w σ i)
    (hv : ∀ i, IsTanAtG t x (v i)) (hb : ∀ u, IsTanAtG t x u → ∃! cf, IsCombAtG t x v cf u) :
    Submodule.span S (Set.range fun i => tanOf (ht i)) = EigenSplit.eigenSub (actR t.act) (χ σ) := by
  classical
  refine le_antisymm (Submodule.span_le.2 ?_) fun u hu => ?_
  · rintro _ ⟨i, rfl⟩
    refine EigenSplit.mem_eigenSub.2 fun a => ?_
    obtain ⟨g, hc, -⟩ := hb _ (isTan_tv (actR t.act a (tanOf (ht i))))
    obtain ⟨g', hc', -⟩ := hb _ (isTan_tv (χ σ a • tanOf (ht i)))
    have hcc : g = g' := funext fun l => hw _ _ fun k _ φ f hf hfj => by
      have h1 := comb_map φ rfl hc
      have h2 := comb_map φ rfl hc'
      have h3 : spMap (dualMap φ) ≫ (tv (actR t.act a (tanOf (ht i)))).left =
          spMap (dualMap φ) ≫ (tv (χ σ a • tanOf (ht i))).left := by
        refine (Category.assoc _ _ _).symm.trans (((hf.1 σ i).2 a).trans ?_)
        rw [hfj]
        exact (dualMap_epsMul φ _ _).symm
      rw [h3] at h1
      exact congrFun ((basis_map φ rfl hv hb _ (isTan_map φ rfl (isTan_tv _))).unique h1 h2) l
    subst hcc
    exact ((isComb_iff (fun i => tanOf (hv i)) g _).1 hc).trans ((isComb_iff (fun i => tanOf (hv i)) g _).1 hc').symm
  · obtain ⟨g, hc, -⟩ := hb _ (isTan_tv u)
    rw [(isComb_iff (fun i => tanOf (hv i)) g _).1 hc]
    refine Submodule.sum_mem _ fun l _ => ?_
    by_cases hl : ∃ i, e i = l
    · obtain ⟨i, rfl⟩ := hl
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, tan_ext (he i).symm⟩)
    have h0 : g l = 0 := hw _ _ fun k _ φ f hf hfj => by
      have hvk := fun i => isTan_map φ rfl (hv i)
      have huk := isTan_map φ rfl (isTan_tv u)
      obtain ⟨d, hd, -⟩ := hf.2 σ _ huk fun a => by
        rw [hfj, ← dualMap_epsMul, Category.assoc]
        exact congrArg (fun q => spMap (dualMap φ) ≫ (tv q).left) (EigenSplit.mem_eigenSub.1 hu a)
      have h1 := (comb_iff hvk _ huk).1 (comb_map φ rfl hc)
      have h2 := (comb_iff (fun i => (hf.1 σ i).1) _ huk).1 hd
      have h3 : ∑ i, d i • tanOf (hf.1 σ i).1 = ∑ l, Function.extend e d 0 l • tanOf (hvk l) :=
        Fintype.sum_of_injective e e.injective _ _
          (fun l hl => by rw [Function.extend_apply' _ _ _ hl, Pi.zero_apply, zero_smul])
          (fun i => by
            rw [e.injective.extend_apply]
            exact congrArg (d i • ·) (tan_ext (congrArg (spMap (dualMap φ) ≫ ·) (he i).symm)))
      rw [map_zero, Fintype.linearIndependent_iffₛ.1 (linInd_of_basis hvk (basis_map φ rfl hv hb)) _ _
        (h1.symm.trans (h2.trans h3)) l, Function.extend_apply' _ _ _ hl, Pi.zero_apply]
    rw [h0, zero_smul]
    exact Submodule.zero_mem _

theorem exists_basis_total (hw : FramesSeparate x c w χ) (hχ : EigenSplit.IsSplitting χ)
    (h : ∀ σ, ∃ (n : ℕ) (v : Fin n → (Sp (DualNumber S) ⟶ t.G.left)) (e : Fin (Dw.mult σ) ↪ Fin n),
      (∀ i, v (e i) = w σ i) ∧ (∀ i, IsTanAtG t x (v i)) ∧ ∀ u, IsTanAtG t x u → ∃! cf, IsCombAtG t x v cf u)
    (φ : S →+* T) {x' : Sp T ⟶ X} (hx : spMap φ ≫ x = x') :
    ∃ b : Module.Basis (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) T (TanM x' t.G), ∀ σ a, (tv (b ⟨σ, a⟩)).left = w.bc φ σ a := by
  choose n v e he hv hb using h
  have ht : ∀ σ i, IsTanAtG t x (w σ i) := fun σ i => he σ i ▸ hv σ (e σ i)
  have li : ∀ σ, LinearIndependent S fun i => tanOf (ht σ i) := fun σ => by
    obtain ⟨b, hb'⟩ := exists_basis (hv σ) (hb σ)
    convert b.linearIndependent.comp (e σ) (e σ).injective using 1
    exact funext fun i => Eq.trans (tan_ext (w := tanOf (hv σ (e σ i))) (he σ i).symm) (hb' (e σ i)).symm
  obtain ⟨b, hb'⟩ := exists_basis_sigma hχ _ (fun σ i => tanOf (ht σ i)) li
    fun σ => span_eq_eigenSub hw σ (ht σ) (e σ) (he σ) (hv σ) (hb σ)
  obtain ⟨b', hb''⟩ := exists_basis_map b φ hx
  exact ⟨b', fun σ a => by rw [hb'', hb']; rfl⟩

end Tangent

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

def embV {l : Level H} (c : Coeff l) (W : ValuationSubring ℂ) (σ : E →+* ℂ) : 𝓞 E →+* c.V W :=
  (embK c σ).codRestrict (c.V W) fun a =>
    GlobalTheory.CoeffRings.mem_of_isIntegral _ (map_isIntegral_int (embK c σ) (RingOfIntegers.isIntegral a))

theorem isSplitting_embV {l : Level H} (c : Coeff l) (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits)
    (hd : ¬ p ∣ (discr E).natAbs) {S : Type} [CommRing S] (j : c.V W →+* S) :
    EigenSplit.IsSplitting fun σ : E →+* ℂ => j.comp (embV c W σ) := by
  refine EigenSplit.isSplitting_of_isDomain (fun σ τ h => ?_) (NumberField.Embeddings.card E ℂ) j ?_
  · exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
      (RingHom.ext fun a => congrArg (fun f : 𝓞 E →+* c.V W => (((f a : c.V W) : c.F) : ℂ)) h)
  · have hu := (((GlobalTheory.CoeffRings.coeff_isDedFrac E H l c).2.2.2 p W hp hW).2.1 _
      (hp.coprime_iff_not_dvd.2 hd).symm).map j
    rw [map_natCast] at hu
    rcases Int.natAbs_eq (discr E) with h | h <;> rw [h]
    · rwa [Int.cast_natCast]
    · rw [Int.cast_neg, Int.cast_natCast]
      exact hu.neg

variable {Z : Mdl Y i₀} {U : Z.X.Opens} {hU : IsAffineOpen U} {w : Vecs Dw (Y Z.i).t Γ(Z.X, U)}


variable (hU) in
theorem fn_ext_affine {f g : Γ(Z.X, U)} (h : ∀ (k : Type) [Field k] (φ : Γ(Z.X, U) →+* k),
    Set.range (spMap φ ≫ hU.fromSpec) ⊆ Z.opn → φ f = φ g) : f = g :=
  fn_ext Z fun k _ x hx ho => by
    rw [valR_eq x U hx, valR_eq x U hx]
    exact h k (valMap x U hx).hom (by
      rw [show spMap (valMap x U hx).hom ≫ hU.fromSpec = x from specMap_valMap_fromSpec hU x hx]
      exact ho)

theorem frame_at (hw : IntFrame Z hU w) {j : Z.i.c.V W →+* Γ(Z.X, U)} (hj : spMap j = hU.fromSpec ≫ Z.s)
    {k : Type} [Field k] (φ : Γ(Z.X, U) →+* k) (ho : Set.range (spMap φ ≫ hU.fromSpec) ⊆ Z.opn) :
    ∃ f : Z.i.c.F →+* k, IsFrame (Y Z.i).t f (spMap φ ≫ hU.fromSpec ≫ Z.π) (w.bc φ) ∧
      ∀ σ a, f (embK Z.i.c σ a) = φ (j (embV Z.i.c W σ a)) := by
  obtain ⟨a, ψ, hx, hf, -⟩ := hw.2 k φ ho
  rw [Category.assoc] at hf
  refine ⟨_, hf, fun σ r => ?_⟩
  have e : spMap (ψ.comp ((Z.alg a).comp (Z.i.c.V W).subtype)) = spMap (φ.comp j) := by
    rw [← spMap_comp_spMap _ ψ, ← spMap_comp_spMap _ φ, hj, ← Z.alg_s a, ← Category.assoc, hx, Category.assoc]
  exact congrArg (fun q => q.hom (embV Z.i.c W σ r)) (Spec.map_injective e)

end Model

theorem exists_basis_of_intFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ)
    (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ¬ p ∣ (discr E).natAbs →
    ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : Mdl Y i₀) (U : Z.X.Opens) (hU : IsAffineOpen U)
      (w : Vecs Dw (Y Z.i).t Γ(Z.X, U)), IntFrame Z hU w → ∀ (R : Type) [CommRing R] (φ : Γ(Z.X, U) →+* R)
      (x : Sp R ⟶ Z.X), spMap φ ≫ hU.fromSpec = x →
      ∃ b : Module.Basis (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) R (TanM (x ≫ Z.π) (Y Z.i).t.G),
        ∀ σ a, (tv (b ⟨σ, a⟩)).left = w.bc φ σ a := by
  intro E _ _ _ H Dw Xo p W hp hW hd Y i₀ Z U hU w hw R _ φ x hx
  let j : Z.i.c.V W →+* Γ(Z.X, U) := (Spec.preimage (hU.fromSpec ≫ Z.s)).hom
  have hj : spMap j = hU.fromSpec ≫ Z.s := Spec.map_preimage _
  refine exists_basis_total (c := Z.i.c) (fun r s h => fn_ext_affine hU fun k _ ψ ho => ?_)
    (isSplitting_embV Z.i.c hp hW hd j) hw.1 φ (hx ▸ (Category.assoc _ _ _).symm)
  obtain ⟨f, hf, hfj⟩ := frame_at hw hj ψ ho
  exact h k ψ f hf hfj

end GlobalTheory.TotalFrame
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle

namespace GlobalTheory.ShFam.GradedDiv

section Diag

variable {ι : Type} {m : ι → ℕ} {K : Type} [Field K] {O O' : Subring K} {g h : Mat m K}

theorem diag_mul (hg : Par m O g) (hh : Par m O' h) (τ : ι) (i : Fin (m τ)) :
    (g * h) τ i i = g τ i i * h τ i i := by
  rw [Pi.mul_apply, Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun l _ hl => ?_) (by simp)
  rcases lt_or_gt_of_ne hl with h' | h'
  · rw [(hh τ).2.2.2 l i l.2 h', mul_zero]
  · rw [(hg τ).2.2.2 i l i.2 h', zero_mul]

theorem diag_ne_zero (hg : Par m O g) (τ : ι) (i : Fin (m τ)) : g τ i i ≠ 0 := by
  have := diag_mul hg hg.inv τ i
  rw [Mat.mul_inv hg.det_ne] at this
  exact left_ne_zero_of_mul_eq_one (this.symm.trans (Matrix.one_apply_eq i))

end Diag

theorem exists_div {F : Type} [Field F] {Y : GlobalTheory.ProjVar.Var F} {ι : Type} {m : ι → ℕ} (S : Fr (ratOf Y) m m)
    {A₀ : Mat m Y.Fn} (h₀ : A₀ ∈ S.S (genericPoint Y.X)) :
    ∃ gr : ∀ τ, Fin (m τ) → Y.Dv, ∀ y : Y.X, ∃ A ∈ S.S y, ∃ t : ∀ τ, Fin (m τ) → Y.Fnˣ,
      (∀ τ i, (A₀ * A⁻¹) τ i i = t τ i) ∧ (∀ τ i k, i < k → (A₀ * A⁻¹) τ i k = 0) ∧
        ∀ τ i, (gr τ i).IsEqn y (t τ i) := by
  have hP : ∀ {y : Y.X} {A : Mat m Y.Fn}, A ∈ S.S y →
      Par m ((ratOf Y).O (genericPoint Y.X)).toSubring (A₀ * A⁻¹) := fun hA =>
    (Fr.mem_iff (Fr.mem_genericPoint hA)).1 h₀
  let t : ∀ {y : Y.X} {A : Mat m Y.Fn}, A ∈ S.S y → ∀ τ, Fin (m τ) → Y.Fnˣ := fun hA τ i =>
    Units.mk0 _ (diag_ne_zero (hP hA) τ i)
  have hreg : ∀ {y : Y.X} {A A' : Mat m Y.Fn} (hA : A ∈ S.S y) (hA' : A' ∈ S.S y) τ i,
      RegAt y ((t hA' τ i : Y.Fn) / t hA τ i) := fun {y A A'} hA hA' τ i => by
    have hg := (Fr.mem_iff hA').1 hA
    have e := diag_mul (hP hA) hg τ i
    rw [← mul_assoc, mul_assoc A₀, Mat.inv_mul (Fr.det_ne hA), mul_one] at e
    have e' : (t hA' τ i : Y.Fn) / t hA τ i = (A * A'⁻¹) τ i i := by
      rw [div_eq_iff (t hA τ i).ne_zero, mul_comm]
      exact e
    rw [e']
    exact mem_O_ratOf.1 ((hg τ).1 i i)
  have hgerm : ∀ {y : Y.X} {A A' : Mat m Y.Fn} (hA : A ∈ S.S y) (hA' : A' ∈ S.S y) τ i,
      germOf y (t hA τ i) = germOf y (t hA' τ i) := fun {y A A'} hA hA' τ i => by
    rw [germOf_eq_iff, unitAt_iff (div_ne_zero (t hA' τ i).ne_zero (t hA τ i).ne_zero), inv_div]
    exact ⟨hreg hA hA' τ i, hreg hA' hA τ i⟩
  choose A hA using fun y : Y.X => S.nonempty y
  refine ⟨fun τ i => show cartierGroup Y.X from ⟨fun y => germOf y (t (hA y) τ i), fun y => ?_⟩,
    fun y => ⟨A y, hA y, t (hA y), fun _ _ => rfl, fun τ i k hik => (hP (hA y) τ).2.2.2 i k i.2 hik,
      fun _ _ => rfl⟩⟩
  obtain ⟨U, B, hy, hB, hU⟩ := S.loc y
  have hBm : ∀ z ∈ U, B ∈ S.S z := fun z hz => (hU z hz B).2 (by rw [Mat.mul_inv hB]; exact Par.one)
  exact ⟨U, hy, t (hBm y hy) τ i, fun z hz => hgerm (hA z) (hBm z hz) τ i⟩

theorem exists_gr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (Y : GlobalTheory.ProjVar.Var F) (π : Y.X ⟶ gen Z) (f₀ : EigFrame Z (constF e Y) (genericPt Y ≫ π ≫ genι Z)) (S : Fr (ratOf Y) Dw.mult Dw.mult) (A₀ : Mat Dw.mult Y.Fn), Tied e Y π f₀ S A₀ → ∃ gr : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Dv, ∀ y : Y.X, ∃ (φ : c.F →+* Y.X.presheaf.stalk y) (f : EigFrame Z φ (stalkPt Y y ≫ π ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Fnˣ), f.Tri (algebraMap (Y.X.presheaf.stalk y) Y.X.functionField) f₀ t ∧ ∀ τ i, (gr τ i).IsEqn y (t τ i) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e Y π f₀ S A₀ hT
  obtain ⟨gr, hgr⟩ := exists_div S hT.1
  refine ⟨gr, fun y => ?_⟩
  obtain ⟨A, hA, t, h1, h2, h3⟩ := hgr y
  obtain ⟨φ, f, hf⟩ := hT.2 y A hA
  exact ⟨φ, f, t, (f.tri_iff _ f₀ t).2 ⟨_, hf, h1, h2⟩, h3⟩

end GlobalTheory.ShFam.GradedDiv
end
end

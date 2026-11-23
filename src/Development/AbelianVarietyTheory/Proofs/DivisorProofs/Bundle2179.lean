module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle035
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNormalFormArcDatumFramedPointRootOfUnity
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle006
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2144
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle072
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle276
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2143
public import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfFiniteOrderOfTrivialModSqTateModule
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2146
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle014

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem isIntegral_isLocallyNoetherian_compactSpace :
    ∀ (K : Type) [Field K] (A : AbVar K),
      IsIntegral A.X.left ∧ IsLocallyNoetherian A.X.left ∧ CompactSpace A.X.left := by
  intro K _ A
  have hA : IsAbelianScheme A.X := A.ab
  have : Smooth A.X.hom := hA.smooth
  have : IsProper A.X.hom := hA.proper
  have : GeometricallyConnected A.X.hom := hA.geomConnected
  refine ⟨isIntegral_of_smooth_of_geometricallyConnected A.X.hom,
    LocallyOfFiniteType.isLocallyNoetherian A.X.hom, ?_⟩
  exact (quasiCompact_iff_compactSpace A.X.hom).mp inferInstance

end GlobalTheory.AV.AbVar
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.FinKer

theorem finite_of_isClosed_of_finite_closedPoints {T : Type*} [TopologicalSpace T]
    [JacobsonSpace T] {S : Set T} (hS : IsClosed S) (h : (S ∩ closedPoints T).Finite) :
    S.Finite := by
  have hc : IsClosed (S ∩ closedPoints T) := by
    rw [← Set.biUnion_of_singleton (S ∩ closedPoints T)]
    exact h.isClosed_biUnion fun x hx ↦ hx.2
  rw [← JacobsonSpace.closure_inter_closedPoints hS, hc.closure_eq]
  exact h

theorem locallyQuasiFinite_of_finite_closedFibres {Y X : Scheme.{0}} (f : Y ⟶ X)
    [LocallyOfFiniteType f] [JacobsonSpace Y]
    (h : ∀ y : Y, IsClosed ({y} : Set Y) → (f ⁻¹' {f y}).Finite) : LocallyQuasiFinite f := by
  rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff, eq_top_iff]
  refine subset_of_isOpen_of_closedPoints isOpen_univ f.quasiFiniteLocus.isOpen fun y hy _ ↦ ?_
  have : Finite (f.fiber (f y)) := (f.fiberHomeo (f y)).finite_iff.mpr (h y hy)
  exact Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr (isOpen_discrete _)

theorem exists_lift_of_isClosed {Ω : Type} [Field Ω] [IsAlgClosed Ω] {X Y : Scheme.{0}} (g : X ⟶ Y)
    [LocallyOfFiniteType g] (u : Sp Ω ⟶ Y) (z : X) (hz : IsClosed ({z} : Set X))
    (h : u (IsLocalRing.closedPoint Ω) = g z) :
    ∃ w : Sp Ω ⟶ X, w ≫ g = u ∧ w (IsLocalRing.closedPoint Ω) = z := by
  obtain ⟨p, -, hp2⟩ := Scheme.Pullback.exists_preimage_pullback (f := u) (g := g) _ z h
  have : JacobsonSpace ↥(pullback u g) := LocallyOfFiniteType.jacobsonSpace (pullback.fst u g)
  have hcl : IsClosed (closure ({p} : Set ↥(pullback u g))) := isClosed_closure
  have hne : (closure ({p} : Set ↥(pullback u g)) ∩ closedPoints _).Nonempty := by
    by_contra hc
    rw [Set.not_nonempty_iff_eq_empty] at hc
    have := JacobsonSpace.closure_inter_closedPoints hcl
    rw [hc, closure_empty] at this
    exact (this.symm ▸ subset_closure (Set.mem_singleton p) : p ∈ (∅ : Set _))
  obtain ⟨q, hqp, hq₀⟩ := hne
  have hq : IsClosed ({q} : Set ↥(pullback u g)) := mem_closedPoints_iff.mp hq₀
  refine ⟨pointOfClosedPoint (pullback.fst u g) q hq ≫ pullback.snd u g, ?_, ?_⟩
  · rw [Category.assoc, ← pullback.condition, pointOfClosedPoint_comp_assoc]
  · change (pullback.snd u g) (pointOfClosedPoint (pullback.fst u g) q hq _) = z
    erw [pointOfClosedPoint_apply]
    have hs : p ⤳ q := specializes_iff_mem_closure.mpr hqp
    have := (hs.map (pullback.snd u g).continuous).mem_closed hz (by rw [hp2]; rfl)
    exact this

end GlobalTheory.AV.FinKer

namespace GlobalTheory.AV.AbVar


open GlobalTheory.AV.FinKer in
theorem isFinite_iff_finite_ker : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B),
    IsFinite f.hom.left ↔ Finite (ptMap f).ker := by
  intro K _ A B f
  have : IsProper A.X.hom := A.ab.proper
  have : IsProper B.X.hom := B.ab.proper
  have hw : f.hom.left ≫ B.X.hom = A.X.hom := Over.w f.hom
  have : LocallyOfFiniteType (f.hom.left ≫ B.X.hom) := by rw [hw]; infer_instance
  have : LocallyOfFiniteType f.hom.left := locallyOfFiniteType_of_comp _ B.X.hom
  let pt : Sp (AlgebraicClosure K) := IsLocalRing.closedPoint (AlgebraicClosure K)
  constructor
  · intro hf
    let u : Sp (AlgebraicClosure K) ⟶ B.X.left := (1 : B.Pt).left
    have : IsFinite (pullback.fst u f.hom.left) := inferInstance
    have hfin := ((pullback.fst u f.hom.left).finite_preimage_singleton pt).to_subtype
    have hmem : ∀ x : (ptMap f).ker, 𝟙 _ ≫ u = x.1.left ≫ f.hom.left := fun x ↦ by
      rw [Category.id_comp, ← Over.comp_left]
      exact congrArg CommaMorphism.left (MonoidHom.mem_ker.mp x.2).symm
    refine Finite.of_injective (β := (pullback.fst u f.hom.left) ⁻¹' {pt})
      (fun x ↦ ⟨pullback.lift (𝟙 _) x.1.left (hmem x) pt, Subsingleton.elim _ _⟩) fun x y hxy ↦ ?_
    have e := ext_of_apply_closedPoint_eq (pullback.fst u f.hom.left) (pullback.lift_fst _ _ _)
      (pullback.lift_fst _ _ _) (congrArg Subtype.val hxy)
    have e2 := congrArg (· ≫ pullback.snd u f.hom.left) e
    simp only [pullback.lift_snd] at e2
    exact Subtype.ext (Over.OverMorphism.ext e2)
  · intro hker
    have : IsProper (f.hom.left ≫ B.X.hom) := by rw [hw]; infer_instance
    have : IsProper f.hom.left := IsProper.of_comp _ B.X.hom
    have : JacobsonSpace A.X.left := LocallyOfFiniteType.jacobsonSpace A.X.hom
    have : LocallyQuasiFinite f.hom.left := by
      refine locallyQuasiFinite_of_finite_closedFibres f.hom.left fun y hy ↦ ?_
      obtain ⟨a, ha, hay⟩ := exists_lift_of_isClosed A.X.hom (spMap (algebraMap K (AlgebraicClosure K)))
        y hy (Subsingleton.elim _ _)
      let x : A.Pt := Over.homMk a ha
      have hcl : IsClosed (f.hom.left ⁻¹' {f.hom.left y}) := by
        have := f.hom.left.isClosedMap _ hy
        rw [Set.image_singleton] at this
        exact this.preimage f.hom.left.continuous
      refine finite_of_isClosed_of_finite_closedPoints hcl ?_
      refine (Set.finite_range (fun k : (ptMap f).ker ↦ (x * k.1).left pt)).subset ?_
      rintro z ⟨hzS, hz⟩
      have hzS' : f.hom.left z = f.hom.left y := hzS
      obtain ⟨w, hw1, hw2⟩ := exists_lift_of_isClosed f.hom.left (a ≫ f.hom.left) z hz
        (by change f.hom.left (a pt) = _; rw [hay, hzS'])
      let w' : A.Pt := Over.homMk w (by
        change w ≫ A.X.hom = _
        rw [← hw, ← Category.assoc, hw1, Category.assoc, hw]; exact ha)
      have hk : x⁻¹ * w' ∈ (ptMap f).ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
        exact Over.OverMorphism.ext hw1.symm
      refine ⟨⟨_, hk⟩, ?_⟩
      change (x * (x⁻¹ * w')).left pt = z
      rw [mul_inv_cancel_left]
      exact hw2
    exact IsFinite.of_isProper_of_locallyQuasiFinite _

end GlobalTheory.AV.AbVar
end

section

set_option autoImplicit false


noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Frames GlobalTheory.AllWt
open Formalism.L2.Pj
open scoped Classical

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FlagTan

open GlobalTheory.DeRham GlobalTheory.Cris GlobalTheory.Published

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def IsKSR (Φ : Finset (E →+* ℂ)) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    (x' : Sp (DualNumber S) ⟶ Xo.X) (M : HIx Dw Φ → S) : Prop :=
  ∃ (A : Over (Sp S)) (_ : GrpObj A) (A' : Over (Sp (DualNumber S))) (_ : GrpObj A')
    (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left)
    (h : IsGrpPullback A A' (_root_.GlobalTheory.DeRham.epsRed S) i) (ψ : LinearMap.BilinForm S (HdR A))
    (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR S ⟶ A)) (hb : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) → HdR A),
    IsGrpPullback A Xo.univ.t.G y.x π ∧ IsGrpPullback A' Xo.univ.t.G x' π' ∧ i ≫ π' = π ∧
    IsPolForm (dp0 S) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ ∧
    (∀ σ k, (ub σ k).left ≫ π = y.u σ k) ∧ (∀ σ k, DeRham.IsLieImage (hb ⟨σ, k⟩) (ub σ k)) ∧
    ∀ (τ : Φ) (a : Fin (Dw.mult (conjEmb τ.1))), ∃ w, IsLieComb (fun b => M ⟨τ, a, b⟩) (ub τ.1) w ∧
      IsKSRow h ψ hb ⟨conjEmb τ.1, a⟩ w

theorem isKSR_iff_isKS {Φ : Finset (E →+* ℂ)} {K : Type} [Field K] [Algebra c.F K] {y : FrPt Xo c K}
    {x' : Sp (DualNumber K) ⟶ Xo.X} {M : HIx Dw Φ → K} : IsKSR Φ y x' M ↔ IsKS Φ y x' M := Iff.rfl

theorem IsKSR.baseChange (P : AbelianDeRham) {Φ : Finset (E →+* ℂ)} {S S' : Type} [CommRing S] [Algebra c.F S]
    [CommRing S'] [Algebra c.F S'] {ψ : S →ₐ[c.F] S'} {y : FrPt Xo c S} {y' : FrPt Xo c S'} (h : FrMap ψ y y')
    {x : Sp (DualNumber S) ⟶ Xo.X} {M : HIx Dw Φ → S}
    (hM : IsKSR Φ y x M) : IsKSR Φ y' (spMap (dualMap ψ.toRingHom) ≫ x) (ψ ∘ M) := by
  obtain ⟨A, _, A', _, π, π', i, hi, b, ub, hb, hπ, hπ', e, hpol, hu, hl, hM⟩ := hM
  let : Algebra S S' := ψ.toRingHom.toAlgebra
  obtain ⟨B, _, φ, hφ⟩ := exists_isGrpPullback A (spMap (algebraMap S S'))
  obtain ⟨B', _, φ', hφ'⟩ := exists_isGrpPullback A' (spMap (dualMap (algebraMap S S')))
  have e₀ : spMap (algebraMap S S') ≫ _root_.GlobalTheory.DeRham.epsRed S = _root_.GlobalTheory.DeRham.epsRed S' ≫ spMap (dualMap (algebraMap S S')) := by
    rw [← Cris.spMap_comp, ← Cris.spMap_comp]
    congr 1
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have w : (φ ≫ i) ≫ A'.hom = (B.hom ≫ _root_.GlobalTheory.DeRham.epsRed S') ≫ spMap (dualMap (algebraMap S S')) := by
    rw [(hφ.comp hi).1.w, e₀, Category.assoc]
  have sq : hφ'.1.lift _ _ w ≫ φ' = φ ≫ i := hφ'.1.lift_fst _ _ _
  have hj : IsGrpPullback B B' (_root_.GlobalTheory.DeRham.epsRed S') (hφ'.1.lift _ _ w) :=
    hφ'.cancel ((hφ.comp hi).congr e₀ sq.symm) (hφ'.1.lift_snd _ _ _)
  have hU := ObjDim.isAbelianScheme Xo.univ
  have hg := ObjDim.smoothOfRelativeDimension Xo.univ
  have hA := PolPull.isAbelianScheme_of_isGrpPullback hU hπ
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1 hg
  have hA' := PolPull.isAbelianScheme_of_isGrpPullback hU hπ'
  have gA' := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ'.1 hg
  obtain ⟨bc, hF⟩ := P.2.2.1 S A _ hA gA S' B φ hφ
  have hL := (P.2.1 S' B _ (PolPull.isAbelianScheme_of_isGrpPullback hA hφ)
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hφ.1 gA)).1
  obtain ⟨b', hpol', eb⟩ := hpol.pull_comp (AbelianDeRham.bcMor hφ) (UnivPol.pol Xo).isLB
  choose tv htv using ArcQ.NormalForm.exists_baseChange hφ
  choose th hth using bc.exists
  refine ⟨B, _, B', _, φ ≫ π, φ' ≫ π', _, hj, b', fun σ k => tv (ub σ k), fun k => th (hb k),
    (hφ.comp hπ).congr h.1.symm rfl, hφ'.comp hπ', by rw [← Category.assoc, sq, Category.assoc, e], hpol',
    fun σ k => ?_, fun σ k => (hl σ k).baseChange (hφ := hφ) hF hL (hth _) (htv _), fun τ a => ?_⟩
  · rw [← Category.assoc, htv, Category.assoc, hu, h.2.1] <;> rfl
  · obtain ⟨w, hw, f, hf, hd, hv⟩ := hM τ a
    refine ⟨tv w, ArcQ.NormalForm.isLieComb_baseChange hφ (fun _ => htv _) (htv w) hw, th f,
      mem_Fil_of_corr (hφ := hφ) hF (hth f) hf, fun k => ?_,
      hv.baseChange (hφ := hφ) P hA' gA' hj hφ' sq (hth f) (htv w)⟩
    rw [eb _ _ _ _ (hth f) (hth _), hd]
    split_ifs <;> simp

end GlobalTheory.FlagTan
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

theorem _root_.GlobalTheory.T.kodaira_spencer_tangent_vectors_lift : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {K : Type} [Field K] [Algebra c.F K] {y : FrPt Xo c K} (hy : KSIso (psiSet H) y)
    {ι : Type} [Fintype ι] {x : ι → (Sp (DualNumber K) ⟶ Xo.X)} (hx : ∀ a, GlobalTheory.FlagTan.IsTanX y (x a))
    {Mx : ι → HIx Dw (psiSet H) → K} (hM : ∀ a, GlobalTheory.FlagTan.IsKS (psiSet H) y (x a) (Mx a))
    {x' : Sp (DualNumber K) ⟶ Xo.X} (hx' : GlobalTheory.FlagTan.IsTanX y x') (m : ι → K)
    (h : ∀ (O : Xo.X.Opens) (f : Γ(Xo.X, O)) (h' : ⊤ ≤ x' ⁻¹ᵁ O) (hc : ∀ a, ⊤ ≤ x a ⁻¹ᵁ O),
      (evalPt x' O h' f).snd = ∑ a, m a * (evalPt (x a) O (hc a) f).snd), GlobalTheory.FlagTan.IsKS (psiSet H) y x' (∑ a, m a • Mx a) := by
  first | exact @GlobalTheory.FlagTan.IsKS.sum_of_der | exact GlobalTheory.FlagTan.IsKS.sum_of_der | (intros; apply GlobalTheory.FlagTan.IsKS.sum_of_der <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.kodairaSpencerRow_dual_eigenvector_mem_span_ring : ∀ {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] [IsCommMonObj A] {A' : Over (Sp (DualNumber R))} [GrpObj A'] {i : A.left ⟶ A'.left} (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed R) i) {O : Type} [CommRing O] (a : OAct O A) (cO : O → O) (ψ : LinearMap.BilinForm R (HdR A)), (∀ f ∈ Fil A, ∀ g ∈ Fil A, ψ f g = 0) → (∀ f, (∀ g ∈ Fil A, ψ f g = 0) → f ∈ Fil A) → LinearMap.IsPerfPair ψ → IsAdjointFor a cO ψ → KSRegular h → (∀ (z : O) (f : HdR A) (w : epsR R ⟶ A), IsKSValue h f w → IsKSValue h (act (dp0 R) (𝟙 _) a z f) (w ≫ a.act z)) → ∀ {ι : Type} {m : ι → ℕ} (χ : ι → O →+* R) (ub : ∀ σ, Fin (m σ) → (epsR R ⟶ A)) (hb : (Σ σ, Fin (m σ)) → HdR A), Submodule.span R (Set.range hb) ⊔ Fil A = ⊤ → LinearIndependent R (fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)) → (∀ k (z : O), act (dp0 R) (𝟙 _) a z (hb k) - χ k.1 z • hb k ∈ Fil A) → (∀ σ (w : epsR R ⟶ A), IsTangent w → (∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (χ σ z) ≫ w) → ∃ cf, IsLieComb cf (ub σ) w) → ∀ (τ τb : ι), (∀ z, χ τb (cO z) = χ τ z) → ∀ (j : Fin (m τb)), ∃ cf : Fin (m τ) → R, ∃ w, IsLieComb cf (ub τ) w ∧ GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨τb, j⟩ w := by
  first | exact @GlobalTheory.KSRing.ksRow_exists_lieComb_ring | exact GlobalTheory.KSRing.ksRow_exists_lieComb_ring | (intros; apply GlobalTheory.KSRing.ksRow_exists_lieComb_ring <;> assumption)
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open GlobalTheory.FunObj.SqNum GlobalTheory.NormSum

noncomputable section

namespace GlobalTheory.StdLoc

theorem idx_alg (q : ℝ) (hq : q ≠ 0) (c a a' : ℕ) :
    q ^ (c * (a + a') ^ 2) * glVol q (a + a') /
      (q ^ (c * a ^ 2) * glVol q a * (q ^ (c * a' ^ 2) * glVol q a') * (q ^ c) ^ (a * a')) = blockIdx q c a a' := by
  rw [blockIdx]
  have e : c * (a + a') ^ 2 = c * a ^ 2 + c * a' ^ 2 + c * a * a' + c * a * a' := by ring
  have e2 : (q ^ c) ^ (a * a') = q ^ (c * a * a') := by rw [← pow_mul, mul_assoc]
  rw [e, pow_add, pow_add, pow_add, e2]
  have h1 : q ^ (c * a ^ 2) ≠ 0 := pow_ne_zero _ hq
  have h2 : q ^ (c * a' ^ 2) ≠ 0 := pow_ne_zero _ hq
  have h3 : q ^ (c * a * a') ≠ 0 := pow_ne_zero _ hq
  by_cases ha : glVol q a = 0
  · simp [ha]
  by_cases hb : glVol q a' = 0
  · simp [hb]
  field_simp

end GlobalTheory.StdLoc

namespace GlobalTheory.StdLoc

theorem glVol_add (q : ℝ) (a' a : ℕ) :
    glVol q (a' + a) = glVol q a' * ∏ i ∈ Finset.Icc 1 a, (1 - (q ^ (a' + i))⁻¹) := by
  induction a with
  | zero => simp
  | succ n ih =>
    rw [← add_assoc, glVol, Finset.prod_Icc_succ_top (by omega), ← glVol, ih, Finset.prod_Icc_succ_top (by omega), mul_assoc, add_assoc]

theorem glVol_pos {q : ℝ} (hq : 1 < q) (n : ℕ) : 0 < glVol q n :=
  Finset.prod_pos fun i hi => sub_pos.2 (inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq (by simp at hi; omega)))

theorem stdLoc_product {q : ℝ} (hq : 1 < q) (c a a' : ℕ) :
    (∏ i ∈ Finset.Icc 1 a, (1 - (q ^ (a' + i))⁻¹))⁻¹ * blockIdx q c a a' * ((q ^ (c * a * a'))⁻¹ * glVol q a) = 1 := by
  have h1 := glVol_pos hq a
  have h2 := glVol_pos hq a'
  have h3 : (0 : ℝ) < q ^ (c * a * a') := pow_pos (by linarith) _
  have h4 : 0 < ∏ i ∈ Finset.Icc 1 a, (1 - (q ^ (a' + i))⁻¹) := by
    have := glVol_add q a' a
    have h5 := glVol_pos hq (a' + a)
    rw [this] at h5
    exact pos_of_mul_pos_right h5 h2.le
  rw [blockIdx, add_comm a a', glVol_add]
  generalize ∏ i ∈ Finset.Icc 1 a, (1 - (q ^ (a' + i))⁻¹) = P at h4 ⊢
  field_simp

end GlobalTheory.StdLoc

namespace GlobalTheory.StdLoc

open UniqueFactorizationMonoid

theorem absNorm_eq_prod {E : Type} [Field E] [NumberField E] {𝔪 : Ideal (𝓞 E)} (h𝔪 : 𝔪 ≠ ⊥) :
    (Ideal.absNorm 𝔪 : ℝ) = ∏ w ∈ (normalizedFactors 𝔪).toFinset, (Ideal.absNorm w : ℝ) ^ (normalizedFactors 𝔪).count w := by
  have h1 : (normalizedFactors 𝔪).prod = 𝔪 := by
    have := prod_normalizedFactors h𝔪
    exact associated_iff_eq.1 this
  conv_lhs => rw [← h1]
  rw [map_multiset_prod, Nat.cast_multiset_prod, Multiset.map_map, Finset.prod_multiset_map_count]
  simp

theorem relIndex_blockLevel {D : D7} {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) (𝔪 : Ideal (𝓞 D.host.E)) (a : ℕ)
    (h𝔪 : 𝔪 ≠ ⊥) (hcop : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤) (ha : a ≤ P.d) (hJ : IsBlockLevel P 𝔪 a) :
    ((P.J.relIndex (intG D P.d) : ℕ) : ℝ) = ∏ w ∈ (normalizedFactors 𝔪).toFinset,
      blockIdx (Ideal.absNorm w : ℝ) ((normalizedFactors 𝔪).count w) a (P.d - a) := by
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.exists_reduction_maxLevel_unitary_mod_ideal D 𝔪 h𝔪 P.d
  have hsurj : Function.Surjective ρ := by
    intro g'
    choose g hg using fun i j => Ideal.Quotient.mk_surjective (I := 𝔪) (((g' : GL (Fin P.d) (𝓞 D.host.E ⧸ 𝔪)) : Matrix (Fin P.d) (Fin P.d) (𝓞 D.host.E ⧸ 𝔪)) i j)
    have hgm : (Matrix.of g).map (Ideal.Quotient.mk 𝔪) = ((g' : GL (Fin P.d) (𝓞 D.host.E ⧸ 𝔪)) : Matrix (Fin P.d) (Fin P.d) (𝓞 D.host.E ⧸ 𝔪)) := by
      ext i j; simp [hg]
    have h2 := GlobalTheory.T.exists_maxLevel_unitary_congr_mod_ideal D 𝔪 h𝔪 hcop P.d (Matrix.of g) (by rw [hgm]; exact Matrix.isUnits_det_units g')
    obtain ⟨k, hk, hk'⟩ := h2
    simp only [Matrix.of_apply] at hk'
    refine ⟨⟨k, hk⟩, ?_⟩
    apply Units.ext
    ext i j
    exact ((hρ ⟨k, hk⟩ i j (g i j)).2 (hk' i j)).trans (hg i j)
  have hsub : P.J.subgroupOf (intG D P.d) = (blockPar (𝓞 D.host.E ⧸ 𝔪) a P.d).comap ρ := by
    have h0 : ∀ x : AE D, x - inc D ((0 : 𝓞 D.host.E) : D.host.E) = x := fun x => by simp
    refine Subgroup.ext fun k => ⟨fun h => ?_, fun h => ?_⟩
    · have h' : (k : GA D P.d) ∈ P.J := h
      show ρ k ∈ blockPar (𝓞 D.host.E ⧸ 𝔪) a P.d
      refine (mem_blockPar _).2 fun i j hj hi => ?_
      have h1 := ((hJ _).1 h').2 i j hj hi
      rw [← h0 ((((k : GA D P.d) : GL (Fin P.d) (AE D)) : Matrix (Fin P.d) (Fin P.d) (AE D)) i j)] at h1
      exact ((hρ k i j 0).2 h1).trans (map_zero _)
    · have h' : ρ k ∈ blockPar (𝓞 D.host.E ⧸ 𝔪) a P.d := h
      show (k : GA D P.d) ∈ P.J
      refine (hJ _).2 ⟨k.2, fun i j hj hi => ?_⟩
      have h1 := (hρ k i j 0).1 (((mem_blockPar _).1 h' i j hj hi).trans (map_zero _).symm)
      rwa [h0] at h1
  have hR : Nat.card (𝓞 D.host.E ⧸ 𝔪) = Ideal.absNorm 𝔪 := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 D.host.E ⧸ 𝔪) :=
    Nat.finite_of_card_ne_zero (by rw [hR]; simpa [Ideal.absNorm_eq_zero_iff] using h𝔪)
  have hidx : P.J.relIndex (intG D P.d) = (blockPar (𝓞 D.host.E ⧸ 𝔪) a P.d).index := by
    show (P.J.subgroupOf (intG D P.d)).index = _
    rw [hsub, Subgroup.index_comap_of_surjective _ hsurj]
  have hcm := (blockPar (𝓞 D.host.E ⧸ 𝔪) a P.d).card_mul_index
  have hP0 : (Nat.card (blockPar (𝓞 D.host.E ⧸ 𝔪) a P.d) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  have hI : ((blockPar (𝓞 D.host.E ⧸ 𝔪) a P.d).index : ℝ) =
      (Nat.card (GL (Fin P.d) (𝓞 D.host.E ⧸ 𝔪)) : ℝ) / (Nat.card (blockPar (𝓞 D.host.E ⧸ 𝔪) a P.d) : ℝ) := by
    rw [eq_div_iff hP0, mul_comm]; exact_mod_cast hcm
  rw [hidx, hI, GlobalTheory.T.card_blockParabolicSubgroupGL _ a P.d ha, hR]
  push_cast
  rw [GlobalTheory.T.card_GL_ringOfIntegers_quotient_prod_factors _ 𝔪 h𝔪, GlobalTheory.T.card_GL_ringOfIntegers_quotient_prod_factors _ 𝔪 h𝔪, GlobalTheory.T.card_GL_ringOfIntegers_quotient_prod_factors _ 𝔪 h𝔪, absNorm_eq_prod h𝔪, ← Finset.prod_pow, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun w hw => ?_
  have hq : (Ideal.absNorm w : ℝ) ≠ 0 := by
    have hw0 : w ≠ ⊥ := fun h => by
      rw [h] at hw; exact zero_notMem_normalizedFactors _ (Multiset.mem_toFinset.1 hw)
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 hw0)
  obtain ⟨a', ha'⟩ := Nat.exists_eq_add_of_le ha
  rw [ha', Nat.add_sub_cancel_left]
  exact idx_alg _ hq _ _ _

end GlobalTheory.StdLoc
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.tateModule_level_surjective_of_divisible : ∀ (l : ℕ) [Fact l.Prime] (M : Type) [CommGroup M], (∀ x : M, ∃ y, y ^ l = x) → ∀ (n : ℕ) (x : M), x ^ l ^ n = 1 → ∃ t : Tate l M, t.lev n = x := by
  first | exact @GlobalTheory.Published.tate_lev_surj | exact GlobalTheory.Published.tate_lev_surj | (intros; apply GlobalTheory.Published.tate_lev_surj <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.eq_one_of_finite_order_of_trivial_mod_sq_tateModule : ∀ (l : ℕ) [Fact l.Prime] (M : Type) [CommGroup M] (u : Module.End ℤ_[l] (Tate l M)) (E : ℕ), 0 < E → u ^ E = 1 → (∀ t, (u t).lev 2 = t.lev 2) → u = 1 := by
  first | exact @GlobalTheory.HTLat.Tate.eq_one_of_pow_eq_one_of_lev_two | exact GlobalTheory.HTLat.Tate.eq_one_of_pow_eq_one_of_lev_two | (intros; apply GlobalTheory.HTLat.Tate.eq_one_of_pow_eq_one_of_lev_two <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

theorem _root_.GlobalTheory.T.twistingSection_preserves_hermitianLattices_ranks : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (D : D7) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (Z : Comp Xo c) (G₀ : WTZ E) (_s : TwSec U x Z G₀) (G : WTZ E), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → Even G.2 → GoodOn U x V dict Z G → GoodOn U x V dict Z (G + G₀) ∧ rankOn U Z (G + G₀) = rankOn U Z G := by
  first | exact @GlobalTheory.FlatTw.Good.twist_goodOn | exact GlobalTheory.FlatTw.Good.twist_goodOn | (intros; apply GlobalTheory.FlatTw.Good.twist_goodOn <;> assumption)
end

module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitMkOfFormallyUnramified
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2146
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1560
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeDegreeGrowthChowFormIntegrality
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1365
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2147
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1792
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedSectionReadingEqMovedFrameReading
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.IndefiniteTreeX
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1910
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMixModelB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle337
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle386
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FinEtSubgroup

variable {K : Type} [Field K]

theorem discreteTopology_of_isFinite (X : Over (Sp K)) [IsFinite X.hom] : DiscreteTopology X.left := by
  have : IsLocallyArtinian (Sp K) := inferInstanceAs (IsLocallyArtinian (Spec (CommRingCat.of K)))
  have : IsLocallyArtinian X.left := IsLocallyArtinian.of_locallyQuasiFinite X.hom
  infer_instance

theorem exists_pt_of_finiteEtale (X : Over (Sp K)) [IsFinite X.hom] [Etale X.hom] (x : X.left) :
    ∃ y : ptOver K (AlgebraicClosure K) ⟶ X, x ∈ Set.range y.left := by
  let Ω := AlgebraicClosure K
  let t : Sp Ω ⟶ Sp K := spMap (algebraMap K Ω)
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := X.hom) (g := t) x
    (IsLocalRing.closedPoint Ω) (Subsingleton.elim (α := PrimeSpectrum K) _ _)
  obtain ⟨s, hs, -, hx⟩ := (FinEt.isSplitOfRank_iff _ _).mp
    (FinEt.isSplitOfRank_of_isSepClosed (pullback.snd X.hom t) (pullback.snd X.hom t z))
  obtain ⟨i, w, hw⟩ := (hx z).exists
  refine ⟨Over.homMk (s i ≫ pullback.fst X.hom t) ?_, w, ?_⟩
  · change (s i ≫ pullback.fst X.hom t) ≫ X.hom = t
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp]
  · change (s i ≫ pullback.fst X.hom t) w = x
    rw [Scheme.Hom.comp_apply, hw, hz]

theorem exists_gal_of_apply_eq (X : Over (Sp K)) (a b : ptOver K (AlgebraicClosure K) ⟶ X)
    (p : Sp (AlgebraicClosure K)) (h : a.left p = b.left p) :
    ∃ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, a = specAut σ ≫ b := by
  let Ω := AlgebraicClosure K
  obtain ⟨⟨q, φ⟩, ha⟩ := (Scheme.SpecToEquivOfField Ω X.left).symm.surjective a.left
  obtain ⟨⟨q', ψ⟩, hb⟩ := (Scheme.SpecToEquivOfField Ω X.left).symm.surjective b.left
  simp only [Scheme.SpecToEquivOfField_symm_apply] at ha hb
  have hq : q = q' := by
    have h1 : (Spec.map φ ≫ X.left.fromSpecResidueField q) p =
        (Spec.map ψ ≫ X.left.fromSpecResidueField q') p := by rw [ha, hb]; exact h
    simpa only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] using h1
  subst hq
  let c : CommRingCat.of K ⟶ X.left.residueField q := Spec.preimage (X.left.fromSpecResidueField q ≫ X.hom)
  have hc : Spec.map c = X.left.fromSpecResidueField q ≫ X.hom := Spec.map_preimage _
  have key : ∀ (χ : X.left.residueField q ⟶ CommRingCat.of Ω)
      (u : ptOver K Ω ⟶ X), Spec.map χ ≫ X.left.fromSpecResidueField q = u.left →
      c ≫ χ = CommRingCat.ofHom (algebraMap K Ω) := by
    intro χ u hu
    apply Spec.map_injective
    rw [Spec.map_comp, hc, ← Category.assoc, hu]
    exact Over.w u
  have hφ := key φ a ha
  have hψ := key ψ b hb
  letI : Algebra K (X.left.residueField q) := c.hom.toAlgebra
  letI : Algebra (X.left.residueField q) Ω := ψ.hom.toAlgebra
  haveI : IsScalarTower K (X.left.residueField q) Ω := IsScalarTower.of_algebraMap_eq fun x =>
    (congrArg (fun f => f.hom x) hψ).symm
  let φ' : X.left.residueField q →ₐ[K] Ω :=
    { φ.hom with commutes' := fun x => congrArg (fun f => f.hom x) hφ }
  let σ₀ : Ω →ₐ[K] Ω := φ'.liftNormal Ω
  have hσ₀ : ∀ x, σ₀ (ψ.hom x) = φ.hom x := fun x => φ'.liftNormal_commutes Ω x
  let σ : Ω ≃ₐ[K] Ω := AlgEquiv.ofBijective σ₀ (Algebra.IsAlgebraic.algHom_bijective σ₀)
  refine ⟨σ, Over.OverMorphism.ext ?_⟩
  change a.left = spMap (σ : Ω →+* Ω) ≫ b.left
  rw [← ha, ← hb, ← Category.assoc]
  congr 1
  rw [spMap, ← Spec.map_comp]
  congr 1
  ext x
  exact (hσ₀ x).symm

theorem exists_finiteEtale_subgroup_of_points : ∀ (K : Type) [Field K] (A : AbVar K) (G : Subgroup A.Pt), Finite G → ((Nat.card G : ℕ) : K) ≠ 0 → (∀ (σ : Gal K) (x : A.Pt), x ∈ G → galPts A.X σ x ∈ G) → ∃ (H : Over (Sp K)) (_ : GrpObj H) (i : H ⟶ A.X), IsMonHom i ∧ Mono i ∧ IsFinite H.hom ∧ Etale H.hom ∧ ∀ x : A.Pt, x ∈ G ↔ ∃ y, y ≫ i = x := by
  intro K _ A G _ hn hgal
  classical
  let Ω := AlgebraicClosure K
  let n := Nat.card G
  have hu : IsUnit (n : Γ(Sp K, ⊤)) := by
    simpa using (isUnit_iff_ne_zero.2 hn).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  obtain ⟨-, hTf, hTe⟩ := GrpTangent.finiteEtale_mulN_torsion A.X (hG := A.ab) hu
  let T := torsion A.X n
  let ι₀ : T ⟶ A.X := torsion.ι A.X n
  have hι₀ : ι₀ ^ n = 1 := by
    rw [← GrpTangent.comp_mulN]
    refine pullback.condition.trans ?_
    rw [Hom.one_def]
    congr 1
    exact toUnit_unique _ _
  haveI : IsSplitMono η[A.X] := IsSplitMono.mk' ⟨toUnit _, toUnit_unique _ _⟩
  haveI : Mono ι₀ := inferInstanceAs (Mono (pullback.fst _ _))
  have hpow : ∀ x ∈ G, x ^ n = 1 := fun x hx =>
    congrArg Subtype.val (pow_card_eq_one' (G := G) (x := ⟨x, hx⟩))
  let lt : ∀ {S : Over (Sp K)} (x : S ⟶ A.X), x ^ n = 1 → (S ⟶ T) := fun x hx =>
    pullback.lift x (toUnit _) (by rw [GrpTangent.comp_mulN, hx, Hom.one_def])
  have hlt : ∀ {S : Over (Sp K)} (x : S ⟶ A.X) (hx : x ^ n = 1), lt x hx ≫ ι₀ = x :=
    fun x hx => pullback.lift_fst _ _ _
  let U : Set T.left := {t | ∃ (x : A.Pt) (hx : x ∈ G) (p : Sp Ω), (lt x (hpow x hx)).left p = t}
  haveI := discreteTopology_of_isFinite T
  let V : T.left.Opens := ⟨U, isOpen_discrete U⟩
  let H : Over (Sp K) := Over.mk (V.ι ≫ T.hom)
  let j : H ⟶ T := Over.homMk V.ι rfl
  obtain ⟨ν, hνj⟩ : ∃ ν : H ⟶ A.X, ν = j ≫ ι₀ := ⟨_, rfl⟩
  haveI : IsClosedImmersion V.ι := .of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι]; exact isClosed_discrete _)
  haveI hHf : IsFinite H.hom := by change IsFinite (V.ι ≫ T.hom); infer_instance
  haveI hHe : Etale H.hom := by change Etale (V.ι ≫ T.hom); infer_instance
  haveI : Mono j := (Over.forget _).mono_of_mono_map (by change Mono V.ι; infer_instance)
  haveI : Mono ν := hνj ▸ mono_comp _ _
  have hν : ν ^ n = 1 := by
    rw [hνj, ← MonObj.comp_pow, hι₀, MonObj.comp_one]
  have lift : ∀ {S : Over (Sp K)} (f : S ⟶ A.X) (hf : f ^ n = 1),
      (∀ s : S.left, ∃ y : ptOver K Ω ⟶ S, s ∈ Set.range y.left) →
      (∀ y : ptOver K Ω ⟶ S, y ≫ f ∈ G) → ∃ g : S ⟶ H, g ≫ ν = f := by
    intro S f hf hS hG
    have hr : Set.range (lt f hf).left ⊆ Set.range V.ι := by
      rintro _ ⟨s, rfl⟩
      obtain ⟨y, p, rfl⟩ := hS s
      rw [Scheme.Opens.range_ι]
      have e : y ≫ lt f hf = lt (y ≫ f) (hpow _ (hG y)) := by
        rw [← cancel_mono ι₀, hlt (y ≫ f) (hpow _ (hG y)), Category.assoc, hlt f hf]
      refine ⟨y ≫ f, hG y, p, ?_⟩
      rw [← e]
      rfl
    let g : S ⟶ H := Over.homMk (IsOpenImmersion.lift V.ι (lt f hf).left hr) (by
      change IsOpenImmersion.lift V.ι (lt f hf).left hr ≫ V.ι ≫ T.hom = S.hom
      rw [← Category.assoc, IsOpenImmersion.lift_fac]
      exact Over.w _)
    have hg : g ≫ j = lt f hf := Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)
    exact ⟨g, by rw [hνj, ← Category.assoc, hg, hlt f hf]⟩
  have hP : ∀ y : ptOver K Ω ⟶ H, y ≫ ν ∈ G := by
    intro y
    obtain ⟨p⟩ : Nonempty (Sp Ω) := inferInstance
    have hmem : (y ≫ j).left p ∈ U := by
      have h1 : V.ι (y.left p) ∈ Set.range V.ι := ⟨_, rfl⟩
      rw [Scheme.Opens.range_ι] at h1
      exact h1
    obtain ⟨x, hx, p', hp'⟩ := hmem
    rw [Subsingleton.elim p' p] at hp'
    obtain ⟨σ, hσ⟩ := exists_gal_of_apply_eq T (y ≫ j) (lt x (hpow x hx)) p hp'.symm
    have e : y ≫ ν = galPts A.X σ x := by
      show y ≫ ν = specAut σ ≫ x
      rw [hνj, ← Category.assoc, hσ, Category.assoc, hlt x (hpow x hx)]
    rw [e]
    exact hgal σ x hx

  have hone : η[A.X] = 1 := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  obtain ⟨e, he⟩ := lift η[A.X] (by rw [hone, one_pow])
    (fun s => ⟨toUnit _, by
      obtain ⟨p⟩ : Nonempty (Sp Ω) := inferInstance
      exact ⟨p, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩)
    (fun y => by
      have : y ≫ η[A.X] = 1 := by rw [Hom.one_def, toUnit_unique (toUnit _) y]
      rw [this]; exact one_mem G)
  have hmul : (ν ⊗ₘ ν) ≫ μ[A.X] = (fst H H ≫ ν) * (snd H H ≫ ν) := by
    rw [Hom.mul_def, ← lift_map, lift_fst_snd, Category.id_comp]
  haveI : IsFinite (H ⊗ H).hom := by rw [Over.tensorObj_hom]; infer_instance
  haveI : Etale (H ⊗ H).hom := by rw [Over.tensorObj_hom]; infer_instance
  have hν' : ∀ {S : Over (Sp K)} (g : S ⟶ H), (g ≫ ν) ^ n = 1 := fun g => by
    rw [← MonObj.comp_pow ν n g, hν, MonObj.comp_one]
  obtain ⟨m, hm⟩ := lift ((ν ⊗ₘ ν) ≫ μ[A.X])
    (by rw [hmul, mul_pow, hν' (fst H H), hν' (snd H H), _root_.one_mul])
    (exists_pt_of_finiteEtale _)
    (fun y => by
      rw [hmul, MonObj.comp_mul, ← Category.assoc, ← Category.assoc]
      exact mul_mem (hP (y ≫ fst H H)) (hP (y ≫ snd H H)))
  obtain ⟨i, hi⟩ := lift (ν ≫ ι[A.X]) (by rw [← Hom.inv_def, inv_pow, hν, inv_one])
    (exists_pt_of_finiteEtale _)
    (fun y => by
      rw [← Hom.inv_def, GrpObj.comp_inv]
      exact inv_mem (hP y))
  obtain ⟨gH, hνH⟩ := ReducedSubgroup.exists_grpObj_of_mono ν e m i he hm hi
  refine ⟨H, gH, ν, hνH, inferInstance, hHf, hHe, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · obtain ⟨g, hg⟩ := lift x (hpow x hx) (fun s => ⟨𝟙 _, s, rfl⟩) (fun y => by
      obtain ⟨p⟩ : Nonempty (Sp Ω) := inferInstance
      obtain ⟨σ, hσ⟩ := exists_gal_of_apply_eq (ptOver K Ω) y (𝟙 _) p
        (Subsingleton.elim (α := PrimeSpectrum Ω) _ _)
      rw [hσ, Category.comp_id]
      exact hgal σ x hx)
    exact ⟨g, hg⟩
  · rintro ⟨y, rfl⟩
    exact hP y

end GlobalTheory.FinEtSubgroup
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag psiSet TIx IsTanFrame)
open scoped Classical

theorem _root_.GlobalTheory.T.eq_zero_tangent_of_jacobian_derivs_vanish : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {D : ℕ} [SmoothOfRelativeDimension D p] (K : GlobalTheory.CanonLB p D) (i : K.bundle.ι) {F : Type} [Field F] (z : Sp F ⟶ Y) (hz : ⊤ ≤ z ⁻¹ᵁ K.bundle.U i) (g : Fin D → Γ(Y, K.bundle.U i)), evalPt z _ hz (K.jacobian i le_rfl g) ≠ 0 → ∀ (w : Sp (DualNumber F) ⟶ Y) (hw : ⊤ ≤ w ⁻¹ᵁ K.bundle.U i), spMap (TrivSqZeroExt.fstHom F F F).toRingHom ≫ w = z → w ≫ p = spMap (TrivSqZeroExt.inlHom F F) ≫ z ≫ p → (∀ a, (evalPt w _ hw (g a)).snd = 0) → w = spMap (TrivSqZeroExt.inlHom F F) ≫ z := by
  first | exact @GlobalTheory.CanonLB.eq_zero_tangent_of_jacobian | exact GlobalTheory.CanonLB.eq_zero_tangent_of_jacobian | (intros; apply GlobalTheory.CanonLB.eq_zero_tangent_of_jacobian <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag psiSet TIx IsTanFrame)
open scoped Classical

theorem _root_.GlobalTheory.T.exists_jacobian_evalRingPoint_ne_zero : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {D : ℕ} [SmoothOfRelativeDimension D p] (K : GlobalTheory.CanonLB p D) (i : K.bundle.ι) {F : Type} [Field F] (z : Sp F ⟶ Y) (hz : ⊤ ≤ z ⁻¹ᵁ K.bundle.U i), ∃ g : Fin D → Γ(Y, K.bundle.U i), evalPt z _ hz (K.jacobian i le_rfl g) ≠ 0 := by
  first | exact @GlobalTheory.CanonLB.exists_jacobian_evalPt_ne_zero | exact GlobalTheory.CanonLB.exists_jacobian_evalPt_ne_zero | (intros; apply GlobalTheory.CanonLB.exists_jacobian_evalPt_ne_zero <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.ChiGrid Formalism.L2.DIV

namespace GlobalTheory.FunObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace VecEx

section Frames

variable {K : Type} [Field K] [NumberField K] {n : ℕ}


omit [NumberField K] in
theorem mem_colLat_iff (B : GL (Fin n) K) (x : Fin n → K) :
    x ∈ colLat B ↔ ∃ c : Fin n → 𝓞 K, (B : Matrix (Fin n) (Fin n) K) *ᵥ (fun j => (c j : K)) = x := by
  unfold colLat
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine exists_congr fun c => ?_
  have key : (∑ j, c j • fun a : Fin n => (B : Matrix (Fin n) (Fin n) K) a j) =
      (B : Matrix (Fin n) (Fin n) K) *ᵥ fun j => (c j : K) := by
    funext a
    simp only [Finset.sum_apply, Pi.smul_apply, Matrix.mulVec, dotProduct, Algebra.smul_def]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [key]

theorem isLattice_colLat (B : GL (Fin n) K) : Submodule.IsLattice K (colLat B) := by
  exact Submodule.IsLattice.of_fg K (Submodule.fg_span (Set.finite_range _))


omit [NumberField K] in
theorem form_frame [StarRing K] (G B : Matrix (Fin n) (Fin n) K) (hB : Bᴴ * G * B = 1) (c d : Fin n → K) :
    ∑ i, ∑ j, star ((B *ᵥ c) i) * G i j * (B *ᵥ d) j = ∑ i, star (c i) * d i := by
  have h1 : ∑ i, ∑ j, star ((B *ᵥ c) i) * G i j * (B *ᵥ d) j = star (B *ᵥ c) ⬝ᵥ (G *ᵥ (B *ᵥ d)) := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, mul_assoc]
  rw [h1, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hB,
    Matrix.one_mulVec]
  rfl

end Frames

variable {D : D7}

theorem isSelfDualC_colLat (V : HSp D) (B : GL (Fin V.rank) D.host.E)
    (hB : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B.1 * V.gram * B.1 = 1) : IsSelfDualC V (colLat B) := by
  classical
  have hB' : B.1ᴴ * V.gram * B.1 = 1 := hB
  refine ⟨isLattice_colLat B, fun y => ⟨fun hy x hx => ?_, fun h => ?_⟩⟩
  · obtain ⟨c, rfl⟩ := (mem_colLat_iff B x).1 hx
    obtain ⟨d, rfl⟩ := (mem_colLat_iff B y).1 hy
    rw [form_frame _ _ hB']
    have : ∑ i, star (c i : D.host.E) * (d i : D.host.E) ∈ Formalism.UG.intOE D.host.E :=
      sum_mem fun i _ => mul_mem (GlobalTheory.PlaceDatum.star_mem_intOE ⟨c i, rfl⟩) ⟨d i, rfl⟩
    exact this
  · have hy : B.1 *ᵥ ((B⁻¹).1 *ᵥ y) = y := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    have : ∀ j, ∃ b : 𝓞 D.host.E, (b : D.host.E) = ((B⁻¹).1 *ᵥ y) j := fun j => by
      obtain ⟨b, hb⟩ := h _ ((mem_colLat_iff B _).2 ⟨Pi.single j 1, rfl⟩)
      refine ⟨b, ?_⟩
      rw [hb, ← hy, form_frame _ _ hB', hy, Finset.sum_eq_single j]
      · simp
      · intro i _ hij
        simp [Pi.single_eq_of_ne hij]
      · simp
    choose b hb using this
    exact (mem_colLat_iff B y).2 ⟨b, by rw [show (fun j => (b j : D.host.E)) = _ from funext hb, hy]⟩

variable {S T : HSp D} {ΛS ΛS' : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {ΛT ΛT' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem exists_nsmul_latO (hS : ΛS.FG) (hT : ΛT.FG) (hS' : Submodule.IsFullLattice D.host.E ΛS')
    (hT' : Submodule.IsFullLattice D.host.E ΛT') : ∃ c : ℕ, 0 < c ∧ ∀ u : WO S T, u.map (infPart D) = 0 →
      u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) →
      c • u ∈ latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
  obtain ⟨K, hK, h⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO hS' hT'
  obtain ⟨N, hN, h'⟩ := GlobalTheory.PlaceDatum.exists_den_latO hS hT
  refine ⟨N * K, Nat.mul_pos hN hK, fun t ht hu => ?_⟩
  rw [mul_nsmul]
  refine h _ (Matrix.ext fun i j => ?_) fun i j => ?_
  · change infPart D (N • t i j) = 0
    rw [nsmul_eq_mul, RingHom.map_mul, show infPart D (t i j) = 0 from congrFun (congrFun ht i) j, mul_zero]
  · change toEAf D (N • t i j) ∈ _
    rw [nsmul_eq_mul, RingHom.map_mul, map_natCast]
    exact h' t hu i j

theorem isSBHalf_of_lattices (hS : Submodule.IsFullLattice D.host.E ΛS) (hT : Submodule.IsFullLattice D.host.E ΛT)
    (hS' : Submodule.IsFullLattice D.host.E ΛS') (hT' : Submodule.IsFullLattice D.host.E ΛT') {e : AE D}
    (he : infPart D e = 0) {Φ : WO S T → ℂ} (hΦ : IsSBHalf e (latO S T ΛS ΛT fun _ => True) Φ) :
    IsSBHalf e (latO S T ΛS' ΛT' fun _ => True) Φ := by
  obtain ⟨c, hc, h⟩ := exists_nsmul_latO hS.toIsLattice.fg hT.toIsLattice.fg hS' hT'
  obtain ⟨c', hc', h'⟩ := exists_nsmul_latO hS'.toIsLattice.fg hT'.toIsLattice.fg hS hT
  obtain ⟨h1, k, hk, h2, h3⟩ := hΦ
  have hh : ∀ (m : ℕ) (u : WO S T), IsHalf e u → IsHalf e (m • u) := fun m u hu =>
    (GlobalTheory.PlaceModel.isHalf_iff S T).2 (nsmul_mem ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hu) m)
  refine ⟨h1, c' * (c * k), by positivity, fun u hu hu' t => ?_, fun t ht => ?_⟩
  · rw [mul_nsmul, mul_nsmul]
    exact h2 _ (nsmul_mem (h' u (GlobalTheory.PlaceDatum.infPart_of_half he hu') hu) c) (hh _ _ (hh _ _ hu')) t
  · rw [mul_nsmul', mul_nsmul']
    exact nsmul_mem (h _ (GlobalTheory.PlaceDatum.infPart_of_half he (hh _ _ (h1 t ht))) (h3 t ht)) c'

theorem exists_isThetaAt_of_vac {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {sS sT}
    (hS : Submodule.IsFullLattice D.host.E ΛS) (hT : Submodule.IsFullLattice D.host.E ΛT) (hS' : IsSelfDualC S ΛS')
    (hT' : IsSelfDualC T ΛT') {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) {f₀ Φ : WO S T → ℂ}
    (hf : IsVacO ψ θ S T sS sT ΛS' ΛT' f₀) (hΦ : IsSBHalf e (latO S T ΛS ΛT fun _ => True) Φ) :
    ∃ f, IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS' ΛT' fun _ => True) 1 f₀ Φ f :=
  GlobalTheory.PlaceDatum.exists_isThetaAt hf.1 hS' hT' (GlobalTheory.PlaceDatum.idemSum_mul_self he) (GlobalTheory.PlaceDatum.infPart_idemSum he)
    (GlobalTheory.PlaceModelSum.placeModelExistsSum D ψ hf.1 S T ΛS' ΛT' hS' hT' _ e he f₀ hf.2.theta hf.2.lat).1
    (isSBHalf_of_lattices hS hT
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull S ΛS' hS')
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull T ΛT' hT')
      (GlobalTheory.PlaceDatum.infPart_idemSum he) hΦ)

end VecEx

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem DefNode.selfDual (G : ChiGrid.GridData L sc) {μ0 : T} (hL : L.Is μ0) {X : Node} (h : DefNode D.R.m X) :
    IsSelfDualC (G.V X) (G.Λ X) := by
  rcases X with ⟨_ | i, j⟩ | i | j
  · exact (colY_isV D T L μ0 hL j h.2.le).sd
  · exact (G.isV (X := .grid (i + 1) j) ⟨h.1, h.2.le⟩ (by simp)).sd
  · exact h.elim
  · exact (G.isV (X := .top j) h (by simp)).sd

theorem Std.selfDual {G : ChiGrid.GridData L sc} {U : Set T} (N : Std G U) {X : Node} (h : DefNode D.R.m X) :
    IsSelfDualC (G.V X) (colLat (N.fr X)) :=
  VecEx.isSelfDualC_colLat _ _ (N.fr_on X h)

theorem Normal.hasVec_of_defPair {G : ChiGrid.GridData L sc} {W : G.Weil} {μ0 : T} (hL : L.Is μ0) {U : Set T} {N : Std G U}
    (Z : Normal W N) {t : T} {p : Pair T} (hp : DefPair D.R.m p) (d : FinDatum G t p) : Z.HasVec d := by
  obtain ⟨h1, h2⟩ := hp.nodes
  have hv := Z.vac_is p hp
  letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ (h1.selfDual G hL)
  letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ (h2.selfDual G hL)
  rcases p with ⟨i, j⟩ | ⟨t', i, j⟩ | i | ⟨t', j⟩
  · exact VecEx.exists_isThetaAt_of_vac (S := G.pS (.chi i j)) (T := G.pT (.chi i j)) inferInstance inferInstance (isSelfDualC_neg (N.selfDual h2))
      (N.selfDual h1) d.e_is hv d.sb
  · exact hp.elim
  · exact hp.elim
  · exact VecEx.exists_isThetaAt_of_vac inferInstance inferInstance (N.selfDual h1)
      (N.selfDual h2) d.e_is hv d.sb

theorem hasVec {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : ChiGrid.GridData L sc) (W : G.Weil) :
    ∀ μ0, L.Is μ0 → ∀ (U : Set T) (N : Std G U) (Z : Normal W N) (t : T), t ∈ U → ∀ p : Pair T, DefPair D.R.m p →
      ∀ d : FinDatum G t p, Z.HasVec d :=
  fun _ hL _ _ Z _ _ _ hp d => Z.hasVec_of_defPair hL hp d

end GlobalTheory.FunObj

end
end

section

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Indef.Tree
open scoped ENNReal

theorem _root_.GlobalTheory.T.cone_degree_growth_chowForm_integrality : (∀ (K V Ω : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Field Ω] [Algebra K Ω] (ev : V →ₗ[K] Ω) (D a : ℕ), 1 ≤ a → ∀ δ : ℕ, IsImageDeg ev D δ → growth D (fun k => hilb ev (a * k)) = (a : ℝ≥0∞) ^ D * δ) ∧ (∀ (K V Ω : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Field Ω] [Algebra K Ω] (ev : V →ₗ[K] Ω) (D a : ℕ), 1 ≤ a → growth D (fun k => hilb ev (a * k)) ≠ 0 → growth D (fun k => hilb ev (a * k)) ≠ ⊤ → ∃ δ : ℕ, IsImageDeg ev D δ) ∧ (∀ (K V Ω : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Field Ω] [Algebra K Ω] (ev : V →ₗ[K] Ω) (D a : ℕ), 1 ≤ a → ∀ S : ℕ → Submodule K Ω, (∀ k, ∀ t ∈ S k, IsIntDeg ev (a * k) t ∧ IsRatio ev (a * k) t) → growth D (fun k => Cardinal.toENat (Module.rank K (S k))) ≤ growth D (fun k => hilb ev (a * k))) ∧ (∀ (K A : Type) [Field K] [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A] (σ : K →+* ℂ) (n k : ℕ) (w : Fin n → A) (s : A) (C : ℝ), (∀ φ : A →+* ℂ, φ.comp (algebraMap K A) = σ → ‖φ s‖ ≤ C * (1 + ∑ i, ‖φ (w i)‖) ^ k) → IsIntegral (Algebra.adjoin K (Set.range w)) s) := by
  first | exact @GlobalTheory.ConeDeg.degree_growth_integral | exact GlobalTheory.ConeDeg.degree_growth_integral | (intros; apply GlobalTheory.ConeDeg.degree_growth_integral <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip


theorem _root_.GlobalTheory.T.zetaIntegral_standardPair_first_eq_second : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν β : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ), IsUnif ϖ →
      bigP (haarVol (KO k (Fin a))) ϖ finSumFinEquiv ν β (GlobalTheory.StdPairCone.stdA ν ϖ c a a') =
        smallP (haarVol (KO k (Fin a'))) finSumFinEquiv ν (ν * β) (GlobalTheory.StdPairCone.stdB ν ϖ c a a') := by
  first | exact @GlobalTheory.StdZetaAgree.bigZetaIntegral_stdA_eq_smallZetaIntegral_stdB | exact GlobalTheory.StdZetaAgree.bigZetaIntegral_stdA_eq_smallZetaIntegral_stdB | (intros; apply GlobalTheory.StdZetaAgree.bigZetaIntegral_stdA_eq_smallZetaIntegral_stdB <;> assumption)
end

section

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GeoLevel GlobalTheory.LevelCusp GlobalTheory.FrameUnif
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

theorem _root_.GlobalTheory.T.movedSection_reading_eq_movedFrame_reading : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (k : U.Comp) (φD : Dw.La →ₗ[𝓞 E] (Fin r → E)), Function.Injective φD → Submodule.span E (Set.range φD) = ⊤ → (∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (φD x) (φD y))) → (∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → (τ (U.X k).ξ0).im < 0) → ∀ (δ : GL (Fin r) E) (h : IsMatch (U.X k) (U.X k) δ), ((δ : Matrix (Fin r) (Fin r) E).det = 1 ∨ ((∃ m : ℕ, 0 < m ∧ (δ : Matrix (Fin r) (Fin r) E).det ^ m = 1) ∧ 4 ∣ Module.finrank ℚ E)) → ∀ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ), ρ ≫ Xo.s = Xo.s → MoveMatch U U k k h ρ ν → ∀ w n, Dom w n → ∀ f ∈ sec Xo c w n, ∀ f' ∈ sec Xo c w n, (∀ y y' : FrPt Xo c (CAt σ), FrMove ρ ν y y' → evR Xo c f' y = evR Xo c f y') → ∀ x ∈ (U.X k).dom, Formalism.L2.PjFree.rdU U f' k x = Formalism.L2.PjFree.rdU U f k (lact δ (castFr h.psi x)) := by
  first | exact @GlobalTheory.GeoLevel.rdU_move_eq | exact GlobalTheory.GeoLevel.rdU_move_eq | (intros; apply GlobalTheory.GeoLevel.rdU_move_eq <;> assumption)
end

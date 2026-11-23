module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HdimEqZeroOfSubsingleton
public import Mathlib.RingTheory.Length
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle160
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle271
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle033
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle008
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsEventuallyNormRiemannThetaTermLe
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsEqTransposeMulDiagonalMul
public import Mathlib.LinearAlgebra.SymplecticGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle272
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle012
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Mathlib.Topology.Sheaves.Presheaf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle273
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Mathlib.RingTheory.Valuation.LocalSubring
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation

@[expose] public section

section

open ValuativeRel Matrix

namespace GlobalTheory.RankCoinv

theorem exists_KO_row_zero_of_rank_lt (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
    (X : Matrix A D k) (hX : X.rank < Fintype.card A) :
    ∃ g ∈ GlobalTheory.SplitWeil.KO k A, ∃ i₀ : A, ∀ j, (g.val * X) i₀ j = 0 := by

  have hdep : ¬ LinearIndependent k X.row := by
    intro h
    rw [linearIndependent_iff_card_eq_finrank_span] at h
    rw [rank_eq_finrank_span_row] at hX
    exact (lt_irrefl _) (h ▸ hX)
  obtain ⟨c, hc, i₁, hi₁⟩ := Fintype.not_linearIndependent_iff.1 hdep
  have hcj : ∀ j, ∑ i, c i * X i j = 0 := by
    intro j
    have := congrFun hc j
    simpa [Finset.sum_apply, Matrix.row] using this

  obtain ⟨i₀, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun i => valuation k (c i))
    ⟨i₁, Finset.mem_univ _⟩
  have hc0 : c i₀ ≠ 0 := by
    intro h0
    have := hmax i₁ (Finset.mem_univ _)
    rw [h0, map_zero, le_zero_iff, Valuation.zero_iff] at this
    exact hi₁ this
  set c' : A → k := fun i => c i / c i₀ with hc'
  have hc'int : ∀ i, c' i ∈ 𝒪[k] := by
    intro i
    rw [Valuation.mem_integer_iff, hc', map_div₀]
    have hpos : 0 < valuation k (c i₀) := by
      rw [zero_lt_iff]; exact (Valuation.ne_zero_iff _).2 hc0
    exact (div_le_one₀ hpos).2 (hmax i (Finset.mem_univ _))
  have hc'0 : c' i₀ = 1 := div_self hc0

  let E : Matrix A A k := Matrix.of fun i j => if i = i₀ ∧ j ≠ i₀ then c' j else 0
  have hEE : E * E = 0 := by
    ext i j
    simp only [Matrix.mul_apply, E, Matrix.of_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : l = i₀
    · simp [hl]
    · simp [hl]
  have hEint : ∀ i j, E i j ∈ 𝒪[k] := by
    intro i j
    simp only [E, Matrix.of_apply]
    split_ifs
    · exact hc'int j
    · exact zero_mem _
  have h1int : ∀ i j, (1 : Matrix A A k) i j ∈ 𝒪[k] := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  let g : GL A k := ⟨1 + E, 1 - E, by rw [add_mul, one_mul, mul_sub, mul_one, hEE]; abel,
    by rw [sub_mul, one_mul, mul_add, mul_one, hEE]; abel⟩
  refine ⟨g, ?_, i₀, fun j => ?_⟩
  · rw [GlobalTheory.SplitFlip.mem_KO_iff]
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · show (1 + E) i j ∈ 𝒪[k]
      exact add_mem (h1int i j) (hEint i j)
    · show (1 - E) i j ∈ 𝒪[k]
      exact sub_mem (h1int i j) (hEint i j)
  · show (((1 : Matrix A A k) + E) * X) i₀ j = 0
    have hrow : ∀ l, (1 + E) i₀ l = c' l := by
      intro l
      by_cases hl : l = i₀
      · subst hl; simp [E, hc'0]
      · simp [E, hl, Matrix.one_apply, Ne.symm hl]
    rw [Matrix.mul_apply]
    simp_rw [hrow, hc', div_mul_eq_mul_div, ← Finset.sum_div, hcj j, zero_div]

end GlobalTheory.RankCoinv
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.QCoh

noncomputable section

namespace GlobalTheory

theorem restrictGlobal_appTop_eq_appLE {X Y : Scheme.{0}} (f : Y ⟶ X) (V : X.Opens)
    (a : Γ(X, ⊤)) :
    restrictGlobal Y (f ⁻¹ᵁ V) (f.appTop a) = f.appLE V (f ⁻¹ᵁ V) le_rfl (restrictGlobal X V a) := by
  have h : f.app V (restrictGlobal X V a) = restrictGlobal Y (f ⁻¹ᵁ V) (f.appTop a) :=
    ConcreteCategory.congr_hom (f.naturality (homOfLE le_top : V ⟶ ⊤).op) _
  rw [← h, Scheme.Hom.app_eq_appLE]

theorem length_sectionsOn_pullback_of_free (O : Type) [CommRing O] {X Y : Scheme.{0}}
    [Algebra O Γ(X, ⊤)] [Algebra O Γ(Y, ⊤)] (f : Y ⟶ X)
    (hO : ∀ r : O, f.appTop (algebraMap O Γ(X, ⊤) r) = algebraMap O Γ(Y, ⊤) r)
    (V : X.Opens) (n : ℕ) (hV : IsAffineOpen V) (hU : IsAffineOpen (f ⁻¹ᵁ V))
    (hfree : letI := (f.app V).hom.toAlgebra; Module.Free Γ(X, V) Γ(Y, f ⁻¹ᵁ V) ∧
      Module.Finite Γ(X, V) Γ(Y, f ⁻¹ᵁ V) ∧ Module.finrank Γ(X, V) Γ(Y, f ⁻¹ᵁ V) = n)
    (G : X.Modules) [G.IsQuasicoherent] :
    Module.length O (sectionsOn ((Scheme.Modules.pullback f).obj G) (f ⁻¹ᵁ V)) =
      n * Module.length O (sectionsOn G V) := by
  rw [Scheme.Hom.app_eq_appLE] at hfree
  letI := appLEAlgebra f (le_refl (f ⁻¹ᵁ V))
  letI := appLEModule f ((Scheme.Modules.pullback f).obj G) (le_refl (f ⁻¹ᵁ V))
  haveI := appLE_isScalarTower f ((Scheme.Modules.pullback f).obj G) (le_refl (f ⁻¹ᵁ V))
  obtain ⟨hF, hFin, hr⟩ := hfree
  have hbc := isBaseChange_pullbackSections f G hU hV (le_refl (f ⁻¹ᵁ V))
  let b := Module.Free.chooseBasis Γ(X, V) Γ(Y, f ⁻¹ᵁ V)
  let ι := Module.Free.ChooseBasisIndex Γ(X, V) Γ(Y, f ⁻¹ᵁ V)
  let E : Γ((Scheme.Modules.pullback f).obj G, f ⁻¹ᵁ V) ≃ₗ[Γ(X, V)] (ι → Γ(G, V)) :=
    (hbc.equiv.restrictScalars Γ(X, V)).symm ≪≫ₗ
      TensorProduct.congr b.equivFun (LinearEquiv.refl Γ(X, V) Γ(G, V)) ≪≫ₗ
      TensorProduct.comm _ _ _ ≪≫ₗ TensorProduct.piScalarRight _ _ _ _
  let A : sectionsOn ((Scheme.Modules.pullback f).obj G) (f ⁻¹ᵁ V) ≃+ (ι → sectionsOn G V) :=
    (sectionsOn.toΓ _ _).trans (E.toAddEquiv.trans
      (AddEquiv.piCongrRight fun _ ↦ (sectionsOn.toΓ G V).symm))
  let Φ : sectionsOn ((Scheme.Modules.pullback f).obj G) (f ⁻¹ᵁ V) ≃ₗ[O]
      (ι → sectionsOn G V) :=
    A.toLinearEquiv fun r x ↦ by
      funext i
      apply (sectionsOn.toΓ G V).injective
      change sectionsOn.toΓ G V ((sectionsOn.toΓ G V).symm
          (E (sectionsOn.toΓ _ _ (r • x)) i)) =
        sectionsOn.toΓ G V (r • (sectionsOn.toΓ G V).symm (E (sectionsOn.toΓ _ _ x) i))
      rw [AddEquiv.apply_symm_apply, sectionsOn.toΓ_smul, sectionsOn.toΓ_smul,
        AddEquiv.apply_symm_apply, ← hO, restrictGlobal_appTop_eq_appLE]
      rw [← appLEModule_smul, E.map_smul]
      rfl
  rw [Φ.length_eq, Module.length_pi_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rcases subsingleton_or_nontrivial Γ(X, V) with hA | hA
  · haveI : Subsingleton Γ(G, V) := Module.subsingleton Γ(X, V) Γ(G, V)
    haveI : Subsingleton (sectionsOn G V) := (sectionsOn.toΓ G V).toEquiv.subsingleton_congr.2 this
    rw [Module.length_eq_zero_iff.2 this, mul_zero, mul_zero]
  · rw [← hr, Module.finrank_eq_card_chooseBasisIndex]

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits

theorem _root_.GlobalTheory.T.isField_stalk_imageOfGenericPoint : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsIntegral Y] [GlobalTheory.IsNormalScheme Z], IsOpen (Set.range π) →
    IsField (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)) := by
  first | exact @GlobalTheory.NormSheafDescent.isField_stalk_genPt | exact GlobalTheory.NormSheafDescent.isField_stalk_genPt | (intros; apply GlobalTheory.NormSheafDescent.isField_stalk_genPt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.isNormalScheme_pullback_spMap_of_isNormalScheme : (∀ (F K A : Type) [Field F] [CharZero F] [Field K] [Algebra F K] [CommRing A] [Algebra F A], (∀ (P : Ideal A) [P.IsPrime], IsDomain (Localization.AtPrime P) ∧ IsIntegrallyClosed (Localization.AtPrime P)) → ∀ (Q : Ideal (TensorProduct F A K)) [Q.IsPrime], IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q)) → ∀ (F K : Type) [Field F] [CharZero F] [Field K] (c : F →+* K) (Y : Scheme.{0}) (g : Y ⟶ Sp F), GlobalTheory.IsNormalScheme Y → GlobalTheory.IsNormalScheme (pullback g (spMap c)) := by
  first | exact @GlobalTheory.isNormalScheme_pullback_spMap_of_algebra | exact GlobalTheory.isNormalScheme_pullback_spMap_of_algebra | (intros; apply GlobalTheory.isNormalScheme_pullback_spMap_of_algebra <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FieldPointGraph

theorem epi_spMap {K K' : Type} [Field K] [Field K'] (ι : K →+* K') : Epi (spMap ι) := by
  have : Flat (spMap ι) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    letI := ι.toAlgebra
    exact (inferInstance : Module.Flat K K')
  have : Surjective (spMap ι) := ⟨fun y => ⟨IsLocalRing.closedPoint K', Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

noncomputable def pt (K : Type) [Field K] : Sp K := IsLocalRing.closedPoint K

theorem eq_pt {K : Type} [Field K] (t : Sp K) : t = pt K := Subsingleton.elim _ _

theorem exists_eq_spMap_comp {X : Scheme.{0}} {K : Type} [Field K] (c : Sp K ⟶ X) {x : X}
    (hx : c (pt K) = x) :
    ∃ ι : X.residueField x →+* K, c = spMap ι ≫ X.fromSpecResidueField x := by
  subst hx
  exact ⟨_, (Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X c).symm⟩

theorem exists_valuationRing_factor {R K : Type} [CommRing R] [IsLocalRing R] [Field K]
    (f : R →+* K) :
    ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : ValuationRing A) (φ : R →+* A)
      (ι : FractionRing A →+* K), IsLocalHom φ ∧
        ι.comp ((algebraMap A (FractionRing A)).comp φ) = f := by
  obtain ⟨A, hA, hl⟩ := IsLocalRing.exists_factor_valuationRing f
  refine ⟨A, inferInstance, inferInstance, inferInstance, f.codRestrict A.toSubring hA,
    IsFractionRing.lift (A := A) (g := A.subtype) Subtype.val_injective, hl, ?_⟩
  ext a
  exact IsFractionRing.lift_algebraMap (A := A) (g := A.subtype) Subtype.val_injective _

theorem exists_valuationRing_of_specializes {X : Scheme.{0}} {x y : X} (h : x ⤳ y) :
    ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : ValuationRing A) (u : Sp A ⟶ X)
      (ι : FractionRing A →+* X.residueField x),
      spMap ι ≫ spMap (algebraMap A (FractionRing A)) ≫ u = X.fromSpecResidueField x ∧
        (spMap (IsLocalRing.residue A) ≫ u) (pt _) = y := by
  obtain ⟨A, _, _, _, φ, ι, hl, hf⟩ := exists_valuationRing_factor
    (X.presheaf.stalkSpecializes h ≫ X.residue x).hom
  refine ⟨A, inferInstance, inferInstance, inferInstance, spMap φ ≫ X.fromSpecStalk y, ι, ?_, ?_⟩
  · have e : spMap ι ≫ spMap (algebraMap A (FractionRing A)) ≫ spMap φ =
        Spec.map (X.presheaf.stalkSpecializes h ≫ X.residue x) := by
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hf]
      rfl
    refine Eq.trans ?_ ((congrArg (· ≫ X.fromSpecStalk y) e).trans ?_)
    · simp only [Category.assoc]
    · rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
      rfl
  · have e1 : (spMap (IsLocalRing.residue A)) (pt _) = IsLocalRing.closedPoint A :=
      IsLocalRing.comap_closedPoint (IsLocalRing.residue A)
    have e2 : (spMap φ) (IsLocalRing.closedPoint A) = IsLocalRing.closedPoint _ :=
      IsLocalRing.comap_closedPoint φ
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, e1]
    exact (congrArg (X.fromSpecStalk y) e2).trans Scheme.fromSpecStalk_closedPoint

theorem exists_section {W Q : Scheme.{0}} (r : W ⟶ Q) [IsProper r] [IsNoetherian Q]
    [GlobalTheory.IsNormalScheme Q] (G : ∀ (K : Type) [Field K], (Sp K ⟶ W) → Prop)
    (hU : ∀ (K : Type) [Field K] (z : Sp K ⟶ Q), ∃! c, G K c ∧ c ≫ r = z)
    (hB : ∀ (K K' : Type) [Field K] [Field K'] (ι : K →+* K') (c : Sp K ⟶ W),
      G K c → G K' (spMap ι ≫ c))
    (hV : ∀ (A : Type) [CommRing A] [IsDomain A] [ValuationRing A] (u : Sp A ⟶ W),
      G (FractionRing A) (spMap (algebraMap A (FractionRing A)) ≫ u) →
      G (IsLocalRing.ResidueField A) (spMap (IsLocalRing.residue A) ≫ u)) :
    ∃ s : Q ⟶ W, s ≫ r = 𝟙 Q ∧ ∀ (K : Type) [Field K] (z : Sp K ⟶ Q), G K (z ≫ s) := by

  have hD : ∀ (K K' : Type) [Field K] [Field K'] (ι : K →+* K') (c : Sp K ⟶ W),
      G K' (spMap ι ≫ c) → G K c := by
    intro K K' _ _ ι c hc
    obtain ⟨d, ⟨hd, hdr⟩, -⟩ := hU K (c ≫ r)
    have e : spMap ι ≫ c = spMap ι ≫ d :=
      (hU K' (spMap ι ≫ c ≫ r)).unique ⟨hc, Category.assoc _ _ _⟩
        ⟨hB _ _ ι d hd, by rw [Category.assoc, hdr]⟩
    have := epi_spMap ι
    rwa [(cancel_epi _).mp e]
  let T : Set W := {x | G (W.residueField x) (W.fromSpecResidueField x)}
  have hT : ∀ (K : Type) [Field K] (c : Sp K ⟶ W),
      G K c ↔ c (pt K) ∈ T := by
    intro K _ c
    obtain ⟨ι, hι⟩ := exists_eq_spMap_comp c rfl
    exact ⟨fun h => hD _ _ ι _ (hι ▸ h), fun h => by rw [hι]; exact hB _ _ ι _ h⟩
  have hspec : ∀ x y : W, x ⤳ y → x ∈ T → y ∈ T := by
    intro x y h hx
    obtain ⟨A, _, _, _, u, ι, hu, hy⟩ := exists_valuationRing_of_specializes h
    have h1 := hV A u (hD _ _ ι _ (hu ▸ hx))
    rwa [hT, hy] at h1
  choose g hg hg' using fun y : Q => hU (Q.residueField y) (Q.fromSpecResidueField y)
  let γ : Q → W := fun y => g y (pt _)
  have hγT : ∀ y, γ y ∈ T := fun y => (hT _ _).mp (hg y).1
  have hγr : ∀ y, r (γ y) = y := fun y => by
    refine (Scheme.Hom.comp_apply (g y) r _).symm.trans ?_
    rw [(hg y).2]
    exact Scheme.fromSpecResidueField_apply _ _
  have hTγ : ∀ x ∈ T, x = γ (r x) := by
    intro x hx
    have hpt : (W.fromSpecResidueField x ≫ r) (pt (W.residueField x)) =
        r x := by
      rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
    obtain ⟨ι, hι⟩ := exists_eq_spMap_comp (K := W.residueField x) _ hpt
    have e : W.fromSpecResidueField x = spMap ι ≫ g (r x) :=
      (hU (W.residueField x) (W.fromSpecResidueField x ≫ r)).unique ⟨hx, rfl⟩
        ⟨hB _ _ ι _ (hg _).1, by rw [Category.assoc, (hg _).2, hι]⟩
    have e1 := Scheme.fromSpecResidueField_apply x (pt (W.residueField x))
    refine e1.symm.trans ?_
    rw [e, Scheme.Hom.comp_apply]
    exact congrArg (g (r x)) (eq_pt _)
  have hfin : (γ '' genericPoints Q).Finite :=
    (genericPoints.finite NoetherianSpace.finite_irreducibleComponents).image γ
  have hsub : closure (γ '' genericPoints Q) ⊆ T := by
    intro x hx
    rw [← Set.biUnion_of_singleton (γ '' genericPoints Q), hfin.closure_biUnion] at hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨_, ⟨y, -, rfl⟩, hx⟩ := hx
    exact hspec _ _ (specializes_iff_mem_closure.mpr hx) (hγT y)
  have hcl : IsClosed T := by
    have hsurj : r '' closure (γ '' genericPoints Q) = Set.univ := by
      refine Set.eq_univ_of_univ_subset ?_
      rw [← genericPoints.closure (α := Q)]
      refine closure_minimal (fun y hy => ⟨γ y, subset_closure ⟨y, hy, rfl⟩, hγr y⟩)
        (r.isClosedMap _ isClosed_closure)
    have : T = closure (γ '' genericPoints Q) := by
      refine Set.Subset.antisymm (fun x hx => ?_) hsub
      obtain ⟨x', hx', e⟩ : r x ∈ r '' closure (γ '' genericPoints Q) := hsurj ▸ Set.mem_univ _
      rwa [hTγ x hx, ← e, ← hTγ x' (hsub hx')]
    rw [this]
    exact isClosed_closure
  let I := Scheme.IdealSheafData.vanishingIdeal (⟨T, hcl⟩ : Closeds W)
  have hI : Set.range I.subschemeι = T := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    rfl
  have hGI : ∀ (K : Type) [Field K] (c : Sp K ⟶ I.subscheme), G K (c ≫ I.subschemeι) := by
    intro K _ c
    rw [hT, ← hI, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  have : IsIso (I.subschemeι ≫ r) := by
    refine GlobalTheory.isIso_of_isProper_of_existsUnique_field_point _ _ _ inferInstance
      (ReducedSubgroup.isReduced_subscheme_vanishingIdeal _) (GlobalTheory.IsNormalScheme.pred _)
      inferInstance fun K _ z => ?_
    obtain ⟨c, ⟨hc, hcr⟩, hu⟩ := hU K z
    have hker : I.subschemeι.ker ≤ c.ker := by
      rw [Scheme.IdealSheafData.ker_subschemeι]
      apply ReducedSubgroup.vanishingIdeal_le_ker c ⟨T, hcl⟩
      rintro _ ⟨t, rfl⟩
      rw [eq_pt t]
      exact (hT K c).mp hc
    have hl := IsClosedImmersion.lift_fac I.subschemeι c hker
    refine ⟨IsClosedImmersion.lift I.subschemeι c hker, ?_, fun d hd => ?_⟩
    · show _ ≫ _ ≫ _ = _
      rw [← Category.assoc, hl, hcr]
    · rw [← cancel_mono I.subschemeι, hl]
      exact hu _ ⟨hGI K d, (Category.assoc _ _ _).trans hd⟩
  refine ⟨inv (I.subschemeι ≫ r) ≫ I.subschemeι, ?_, fun K _ z => ?_⟩
  · rw [Category.assoc, IsIso.inv_hom_id]
  · rw [← Category.assoc]
    exact hGI K _

theorem exists_hom_of_rel : ∀ (Q P S : Scheme.{0}) (q : Q ⟶ S) (p : P ⟶ S) [IsProper p] [IsNoetherian Q] [GlobalTheory.IsNormalScheme Q] (R : ∀ (K : Type) [Field K], (Sp K ⟶ Q) → (Sp K ⟶ P) → Prop), (∀ (K : Type) [Field K] (z : Sp K ⟶ Q) (w : Sp K ⟶ P), R K z w → z ≫ q = w ≫ p) → (∀ (K : Type) [Field K] (z : Sp K ⟶ Q), ∃! w, R K z w) → (∀ (K K' : Type) [Field K] [Field K'] (ι : K →+* K') (z : Sp K ⟶ Q) (w : Sp K ⟶ P), R K z w → R K' (spMap ι ≫ z) (spMap ι ≫ w)) → (∀ (A : Type) [CommRing A] [IsDomain A] [ValuationRing A] (u : Sp A ⟶ Q) (v : Sp A ⟶ P), u ≫ q = v ≫ p → R (FractionRing A) (spMap (algebraMap A (FractionRing A)) ≫ u) (spMap (algebraMap A (FractionRing A)) ≫ v) → R (IsLocalRing.ResidueField A) (spMap (IsLocalRing.residue A) ≫ u) (spMap (IsLocalRing.residue A) ≫ v)) → ∃ h : Q ⟶ P, h ≫ p = q ∧ ∀ (K : Type) [Field K] (z : Sp K ⟶ Q), R K z (z ≫ h) := by
  intro Q P S q p _ _ _ R hC hU hB hV
  obtain ⟨s, hs, hG⟩ := exists_section (pullback.fst q p)
    (fun K _ c => R K (c ≫ pullback.fst q p) (c ≫ pullback.snd q p))
    (fun K _ z => by
      obtain ⟨w, hw, hu⟩ := hU K z
      refine ⟨pullback.lift z w (hC K z w hw), ⟨?_, pullback.lift_fst _ _ _⟩, fun c hc => ?_⟩
      · rwa [pullback.lift_fst, pullback.lift_snd]
      · refine pullback.hom_ext (by rw [pullback.lift_fst, hc.2]) ?_
        rw [pullback.lift_snd]
        exact hu _ (hc.2 ▸ hc.1))
    (fun K K' _ _ ι c hc => by
      rw [Category.assoc, Category.assoc]
      exact hB K K' ι _ _ hc)
    (fun A _ _ _ u hu => by
      rw [Category.assoc, Category.assoc] at hu ⊢
      exact hV A _ _ (by simp [pullback.condition]) hu)
  refine ⟨s ≫ pullback.snd q p, ?_, fun K _ z => ?_⟩
  · rw [Category.assoc, ← pullback.condition, ← Category.assoc, hs, Category.id_comp]
  · have := hG K z
    rwa [Category.assoc, Category.assoc, hs, Category.comp_id] at this

end GlobalTheory.FieldPointGraph
end

section

open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

namespace GlobalTheory

theorem siegelGauss_pair_standard (l : Type) [Fintype l] [DecidableEq l] (τ : Matrix l l ℂ) (c : ℂ) (hτ : GlobalTheory.IsSiegel τ) :
    (∫ x : l → ℝ, c * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ τ *ᵥ fun i => (x i : ℂ))) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)))) ^ 2 * (1 - I • τ).det = c ^ 2 := by
  set σ : Matrix l l ℂ := τ + I • (1 : Matrix l l ℂ) with hσdef
  have hσ : GlobalTheory.IsSiegel σ := by
    refine ⟨?_, ?_⟩
    · exact hτ.1.add (by simp [Matrix.IsSymm, Matrix.transpose_smul])
    · have : σ.map Complex.im = τ.map Complex.im + 1 := by
        ext i j
        by_cases hij : i = j
        · subst hij; simp [σ, Matrix.one_apply]
        · simp [σ, Matrix.one_apply, hij]
      rw [this]
      exact hτ.2.add_posSemidef Matrix.PosSemidef.one
  have hint : ∀ x : l → ℝ, c * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ τ *ᵥ fun i => (x i : ℂ))) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)))
      = c * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ (σ *ᵥ fun i => (x i : ℂ)))) := by
    intro x
    rw [← Complex.exp_conj, mul_assoc, ← Complex.exp_add]
    congr 2
    have e : ((x ⬝ᵥ x : ℝ) : ℂ) = (fun i => (x i : ℂ)) ⬝ᵥ (fun i => (x i : ℂ)) := by
      simp [dotProduct]
    rw [e, hσdef, Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul]
    simp only [map_mul, map_neg, conj_ofReal, smul_eq_mul]
    have : conj ((fun i => (x i : ℂ)) ⬝ᵥ (fun i => (x i : ℂ))) = (fun i => (x i : ℂ)) ⬝ᵥ (fun i => (x i : ℂ)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp [dotProduct, map_sum]
    rw [this]
    ring_nf
    simp [I_sq]
    ring
  have hdet : (1 - I • τ) = -I • σ := by
    rw [hσdef, smul_add, smul_smul]
    simp [neg_smul, sub_eq_add_neg, add_comm]
  simp_rw [hint]
  rw [integral_const_mul, hdet, mul_pow, mul_assoc]
  have := hσ.siegelGaussIntegral_sq_mul_det
  rw [siegelGaussIntegral] at this
  rw [this, mul_one]

end GlobalTheory
end

section

open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

theorem _root_.GlobalTheory.T.isSiegelUpperHalfSpace_neg_mul_inv_symplectic : ∀ (l : Type) [Fintype l] [DecidableEq l] (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) (P Q : Matrix l l ℂ), (∀ a b, P a b = (s (.inl a) (.inl b) : ℂ) - I * (s (.inl a) (.inr b) : ℂ)) → (∀ a b, Q a b = (s (.inr a) (.inl b) : ℂ) - I * (s (.inr a) (.inr b) : ℂ)) → s ∈ Matrix.symplecticGroup l ℝ → P.det ≠ 0 → (-(Q * P⁻¹)).IsSymm → GlobalTheory.IsSiegel (-(Q * P⁻¹)) := by
  first | exact @GlobalTheory.IsSiegel.neg_mul_inv_of_symplectic | exact GlobalTheory.IsSiegel.neg_mul_inv_of_symplectic | (intros; apply GlobalTheory.IsSiegel.neg_mul_inv_of_symplectic <;> assumption)
end

section

open IsLocalRing GlobalTheory.Henselisation

theorem _root_.GlobalTheory.T.exists_le_isRoot_of_simpleRoot_pointedEtaleNbhd : ∀ (R : Type) [CommRing R] [IsLocalRing R] (i : EtNbhd R) (h : Polynomial i.A) (a₀ : i.A), h.Monic → i.pt (h.eval a₀) = 0 → i.pt (h.derivative.eval a₀) ≠ 0 → ∃ (j : EtNbhd R) (hij : i ≤ j) (c : j.B), (h.map ((EtNbhd.trans hij).comp (algebraMap i.A i.B))).IsRoot c ∧ c - EtNbhd.trans hij (algebraMap i.A i.B a₀) ∈ maximalIdeal j.B := by
  first | exact @GlobalTheory.Henselisation.exists_le_isRoot_of_simple_root | exact GlobalTheory.Henselisation.exists_le_isRoot_of_simple_root | (intros; apply GlobalTheory.Henselisation.exists_le_isRoot_of_simple_root <;> assumption)
end

section

open IsLocalRing GlobalTheory.Henselisation

theorem _root_.GlobalTheory.T.pointedEtaleNbhd_transitionMap_directedSystem : ∀ (R : Type) [CommRing R] [IsLocalRing R], (∀ (i : EtNbhd R) (x : i.B), EtNbhd.trans (le_refl i) x = x) ∧ ∀ (i j k : EtNbhd R) (hij : i ≤ j) (hjk : j ≤ k) (x : i.B), EtNbhd.trans hjk (EtNbhd.trans hij x) = EtNbhd.trans (hij.trans hjk) x := by
  first | exact @GlobalTheory.Henselisation.trans_system | exact GlobalTheory.Henselisation.trans_system | (intros; apply GlobalTheory.Henselisation.trans_system <;> assumption)
end

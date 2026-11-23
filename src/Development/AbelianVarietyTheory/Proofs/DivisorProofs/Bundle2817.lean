module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2720
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2719
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle388
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2409
public import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2722
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle090
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2765
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2764
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2721
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2723
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2724
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2325
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle031
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.QuotSetup

theorem geometricallyConnected_of_surjective {X Y Z : Scheme.{0}} (p : X ⟶ Y) (f : Y ⟶ Z)
    [Surjective p] [GeometricallyConnected (p ≫ f)] : GeometricallyConnected f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x => ?_⟩
  have : ConnectedSpace ↥(pullback (p ≫ f) x) :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback _ _)
  let q := (pullbackRightPullbackFstIso f x p).inv ≫ pullback.snd p (pullback.fst f x)
  have : Surjective q := inferInstance
  exact q.surjective.connectedSpace q.continuous

theorem genericPoint_mem {X : Scheme.{0}} [IsIntegral X] (U : X.Opens) (hU : (U : Set X).Nonempty) :
    genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 (by simpa using hU)

theorem map_genericPoint {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsDominant f] :
    f (genericPoint X) = genericPoint Y := by
  have := (genericPoint_spec X).image f.continuous
  rw [Set.image_univ, f.denseRange.closure_range] at this
  exact this.eq (genericPoint_spec Y)

theorem surjective_of_isProjOver {F : Type} [Field F] {Y Z : Scheme.{0}} [IsIntegral Z] (p : Y ⟶ Sp F)
    (pZ : Z ⟶ Sp F) (f : Y ⟶ Z) (hf : f ≫ pZ = p) (hp : IsProjOver p) (hZ : IsProjOver pZ) (y : Y)
    (hy : f y = genericPoint Z) : Surjective f := by
  have h₁ : IsProper (f ≫ pZ) := hf ▸ ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp).1
  have : IsProper pZ := ((isProjOver_iff_isProper_and_exists_isAmpleLB pZ).1 hZ).1
  have : IsProper f := IsProper.of_comp f pZ
  have hc : closure {genericPoint Z} ⊆ Set.range f :=
    f.isClosedMap.isClosed_range.closure_subset_iff.2 (by rintro _ rfl; exact ⟨y, hy⟩)
  exact ⟨fun z => hc (by rw [(genericPoint_spec Z).def]; trivial)⟩

end GlobalTheory.QuotSetup

namespace GlobalTheory.QuotSetup

theorem exists_resolved_modification : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] [CharZero F] (X X' W V : Scheme.{0}) [IsIntegral X] [IsIntegral X'] [IsIntegral W] (sX : X ⟶ Sp F) (n : ℕ) [SmoothOfRelativeDimension n sX] (φ : X' ⟶ X) (q : X' ⟶ W) (sW : W ⟶ Sp F) (i : V ⟶ X) (ℓ : V ⟶ X'), IsProjOver sX → GeometricallyConnected sX → IsProjOver (φ ≫ sX) → IsProjOver sW → IsFinite q → Surjective q → q ≫ sW = φ ≫ sX → IsOpenImmersion i → IsOpenImmersion ℓ → ℓ ≫ φ = i → ∀ (δ : LB X) (hδ : δ.IsLB) (N : LB W) (hN : N.IsLB), CechPic.pull q (cls N hN) = CechPic.pull φ (cls δ hδ) → ∀ (J : Type) (v : J → (Sp ℂ ⟶ V)), (∀ j j', v j ≫ ℓ ≫ q = v j' ≫ ℓ ≫ q) → (∃ j, ∀ s, (v j ≫ i) s = genericPoint X) → ∃ (W' : Scheme.{0}) (_ : IsIntegral W') (pW : W' ⟶ Sp F) (U : X.Opens) (M : Modif sX U n) (f : M.X ⟶ W') (NW : LB W') (hNW : NW.IsLB), IsIntegral M.X ∧ SmoothOfRelativeDimension n pW ∧ IsProjOver pW ∧ GeometricallyConnected pW ∧ f ≫ pW = M.str ∧ Surjective f ∧ (U : Set X).Nonempty ∧ CechPic.pull f (cls NW hNW) = CechPic.pull M.σ (cls δ hδ) ∧ ∃ z : J → (Sp ℂ ⟶ M.X), (∀ j, ⊤ ≤ z j ⁻¹ᵁ M.opn) ∧ (∀ j, z j ≫ M.σ = v j ≫ i) ∧ (∀ j j', z j ≫ f = z j' ≫ f) ∧ (∀ j s, (z j ≫ f) s = genericPoint W') := by
  intro hP F _ _ X X' W V _ _ _ sX n _ φ q sW i ℓ hsX hgc hφ hsW hqf hqs hw hi hℓ hℓi δ hδ N hN hNδ J v hv hgen
  obtain ⟨j₀, hj₀⟩ := hgen
  obtain ⟨o₀⟩ : Nonempty (Sp ℂ) := inferInstance
  haveI : Nonempty V := ⟨v j₀ o₀⟩
  haveI : IsIntegral V := isIntegral_of_isOpenImmersion i
  haveI : Nonempty X := ⟨i (v j₀ o₀)⟩
  have hpX : IsProper sX := ((isProjOver_iff_isProper_and_exists_isAmpleLB sX).1 hsX).1
  have hpX' : IsProper (φ ≫ sX) := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hφ).1
  have hpW : IsProper sW := ((isProjOver_iff_isProper_and_exists_isAmpleLB sW).1 hsW).1

  have hWgen : ∀ j o, (v j ≫ ℓ ≫ q) o = genericPoint W := fun j o => by
    rw [hv j j₀]
    have h₁ : v j₀ o = genericPoint V :=
      i.isOpenEmbedding.injective ((hj₀ o).trans (genericPoint_eq_of_isOpenImmersion i).symm)
    simp only [Scheme.Hom.comp_apply]
    rw [h₁, genericPoint_eq_of_isOpenImmersion ℓ, map_genericPoint q]

  have hdW : topologicalKrullDim W = n := by
    have hdX : topologicalKrullDim X = n := GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth sX n inferInstance
    have hdV := GlobalTheory.T.topologicalKrullDim_eq_of_openImmersion_integral_scheme F X V sX i
    have hdV' := GlobalTheory.T.topologicalKrullDim_eq_of_openImmersion_integral_scheme F X' V (φ ≫ sX) ℓ
    have h₁ := PosBaseChange.dim_le_of_isClosedMap q.isClosedMap q.surjective
    have h₂ := PosBaseChange.dim_le_of_isDiscrete q.continuous q.isDiscrete_preimage_singleton
    rw [← hdX, ← hdV, hdV']
    exact le_antisymm h₁ h₂

  obtain ⟨W', s, UW, hW', hsm, hpj, hUW, hiso⟩ := GlobalTheory.T.weak_resolution_of_principalisation hP F W sW n hsW hdW
  haveI := hW'
  haveI := hiso
  have hηUW : genericPoint W ∈ UW := genericPoint_mem UW hUW

  let O : V.Opens := (ℓ ≫ q) ⁻¹ᵁ UW
  have hvO : ∀ j o, v j o ∈ O := fun j o => by
    show (ℓ ≫ q) (v j o) ∈ UW
    rw [← Scheme.Hom.comp_apply, hWgen j o]
    exact hηUW
  let U : X.Opens := i ''ᵁ O
  have hUi : Set.range U.ι ⊆ Set.range i := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, -, rfl⟩
    exact ⟨y, rfl⟩
  let e : U.toScheme ⟶ V := IsOpenImmersion.lift i U.ι hUi
  have he : e ≫ i = U.ι := IsOpenImmersion.lift_fac _ _ _
  have hc : Set.range (e ≫ ℓ ≫ q) ⊆ Set.range UW.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    have hx : i (e x) ∈ U := by rw [← Scheme.Hom.comp_apply, he]; exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    rw [i.isOpenEmbedding.injective hyx] at hy
    exact hy
  let c : U.toScheme ⟶ UW.toScheme := IsOpenImmersion.lift UW.ι (e ≫ ℓ ≫ q) hc
  have hcf : c ≫ UW.ι = e ≫ ℓ ≫ q := IsOpenImmersion.lift_fac _ _ _
  let b : UW.toScheme ⟶ W' := inv (s ∣_ UW) ≫ (s ⁻¹ᵁ UW).ι
  have hb : b ≫ s = UW.ι := by simp [b, ← morphismRestrict_ι]
  let r₀ : U.toScheme ⟶ pullback q s :=
    pullback.lift (e ≫ ℓ) (c ≫ b) (by rw [Category.assoc, Category.assoc, hb, hcf])
  have hUne : (U : Set X).Nonempty := ⟨i (v j₀ o₀), v j₀ o₀, hvO j₀ o₀, rfl⟩
  have ht : IsProjOver (pullback.snd q s ≫ s ≫ sW) := isProjOver_comp_of_isFinite _ hpj
  have hr₀ : r₀ ≫ pullback.snd q s ≫ s ≫ sW = U.ι ≫ sX := by
    simp only [r₀, pullback.lift_snd_assoc, Category.assoc]
    rw [reassoc_of% hb, reassoc_of% hcf, hw, reassoc_of% hℓi, reassoc_of% he]
  obtain ⟨M, r, hMi, hrt, hrM⟩ :=
    GlobalTheory.T.exists_modification_extending_map_from_open hP F X (pullback q s) sX n (pullback.snd q s ≫ s ≫ sW) U r₀ inferInstance hsX ht hUne hr₀
  haveI := hMi
  have hsep : IsSeparated sX := inferInstance
  haveI : IsDominant M.opn.ι := ⟨show Dense (Set.range M.opn.ι) by rw [Scheme.Opens.range_ι]; exact M.dense⟩
  have hσ : r ≫ pullback.fst q s ≫ φ = M.σ := by
    refine ext_of_isDominant_of_isSeparated sX ?_ M.opn.ι ?_
    · simp only [Category.assoc]
      rw [← hw, pullback.condition_assoc]
      exact hrt
    · rw [reassoc_of% hrM]
      simp only [r₀, pullback.lift_fst_assoc, Category.assoc]
      rw [hℓi, he, morphismRestrict_ι]
  let f : M.X ⟶ W' := r ≫ pullback.snd q s
  have hfs : f ≫ s = (r ≫ pullback.fst q s) ≫ q := by
    simp only [f, Category.assoc, pullback.condition]
  have hfp : f ≫ s ≫ sW = M.str := by
    simp only [f, Category.assoc]; exact hrt

  have hvU : ∀ j, ⊤ ≤ (v j ≫ i) ⁻¹ᵁ U := fun j o _ => by
    show (v j ≫ i) o ∈ U
    rw [Scheme.Hom.comp_apply]
    exact ⟨v j o, hvO j o, rfl⟩
  choose z hz using fun j => (M.existsUnique_lift (v j ≫ i) (hvU j)).exists
  have hzU : ∀ j, ⊤ ≤ z j ⁻¹ᵁ M.opn := fun j => by
    show ⊤ ≤ z j ⁻¹ᵁ (M.σ ⁻¹ᵁ U)
    rw [← Scheme.Hom.comp_preimage, hz j]
    exact hvU j
  have key : ∀ j, ∃ d : Sp ℂ ⟶ UW.toScheme, d ≫ UW.ι = v j ≫ ℓ ≫ q ∧ z j ≫ f = d ≫ b := fun j => by
    have hr : Set.range (z j) ⊆ Set.range M.opn.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨o, rfl⟩
      exact hzU j (Set.mem_univ o)
    let w := IsOpenImmersion.lift M.opn.ι (z j) hr
    have hw' : w ≫ M.opn.ι = z j := IsOpenImmersion.lift_fac _ _ _
    have hwe : w ≫ (M.σ ∣_ U) ≫ e = v j := by
      rw [← cancel_mono i, Category.assoc, Category.assoc, he, morphismRestrict_ι, reassoc_of% hw', hz j]
    refine ⟨w ≫ (M.σ ∣_ U) ≫ c, ?_, ?_⟩
    · rw [Category.assoc, Category.assoc, hcf, ← reassoc_of% hwe]
    · simp only [f, ← hw', Category.assoc]
      rw [reassoc_of% hrM]
      simp only [r₀, pullback.lift_snd, Category.assoc]
  choose d hd hzd using key
  haveI : Nonempty UW.toScheme := ⟨⟨_, hηUW⟩⟩
  haveI : IsIntegral UW.toScheme := isIntegral_of_isOpenImmersion UW.ι
  have hgen' : ∀ j o, (z j ≫ f) o = genericPoint W' := fun j o => by
    have h₁ : d j o = genericPoint UW.toScheme := by
      apply UW.ι.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hd j, hWgen j o, genericPoint_eq_of_isOpenImmersion UW.ι]
    rw [hzd j, Scheme.Hom.comp_apply, h₁]
    exact genericPoint_eq_of_isOpenImmersion b
  have hfsurj : Surjective f :=
    surjective_of_isProjOver M.str (s ≫ sW) f hfp M.proj hpj (z j₀ o₀) (by rw [← Scheme.Hom.comp_apply]; exact hgen' j₀ o₀)
  have hgcM : GeometricallyConnected M.str := GlobalTheory.T.geometricallyConnected_smoothProjModification_offOpen F X sX n U M hUne
  have hgcW : GeometricallyConnected (s ≫ sW) := by
    rw [← hfp] at hgcM
    exact geometricallyConnected_of_surjective f (s ≫ sW)
  refine ⟨W', hW', s ≫ sW, U, M, f, N.pull s, LB.isLB_pull hN s, hMi, hsm, hpj, hgcW, hfp, hfsurj, hUne, ?_,
    z, hzU, hz, fun j j' => ?_, hgen'⟩
  · rw [cls_pull hN s, ← pull_comp, hfs, pull_comp, hNδ, ← pull_comp, Category.assoc, hσ]
  · rw [hzd j, hzd j']
    congr 1
    rw [← cancel_mono UW.ι, hd j, hd j', hv j j']

end GlobalTheory.QuotSetup
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_unitPartOfPeriodTau_monomial : ∀ {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) {m : ℕ} (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Q.X), IsMonomial Q t gam → (∀ i y z, gam i y z = gam i z y) → (∀ i, t i ≠ 0) → ∀ y z, ∃ τ₀, IsUnitTau Q t gam y z τ₀ := by
  first | exact @GlobalTheory.UnitTau.exists_isUnitTau | exact GlobalTheory.UnitTau.exists_isUnitTau | (intros; apply GlobalTheory.UnitTau.exists_isUnitTau <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_unitPartPeriodTau_zero_value_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X) (mu : P.D.toPre.X), ∃ τ₀, IsUnitTau P.D.toPre (bdParam k m d) gam mu 0 τ₀ ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp (ChartRing k m d)) (z : Z) (J : (Z ⟶ P.D.toPre.P.A.left) → P.D.toPre.P.L.ι), Good P.D.toPre.P.L z J → val τ₀ r z J = 1 := by
  intro E _ _ _ H k _ _ m d t P gam mu
  exact GlobalTheory.UnitTauZero.exists_isUnitTau_zero_val_one E H k m d t P gam mu
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc GlobalTheory.SiegJoin

namespace GlobalTheory.SiegDescent

theorem exists_chart {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {F : SFam g n ζ} {S : Scheme.{0}} {s : S ⟶ Sp o}
    {j : F.X ⟶ S} [IsOpenImmersion j] {φ : InvFun ℤ} {BD : EffCartierData S} {d : ℕ} {x : S}
    (h : GlobalTheory.PolDeg.PreChart F s j φ BD d x) :
    ∃ C : Chart j F.univ.A x, ∀ p : Sp C.R, p ∈ abLocus C.G ↔ C.ξ p ∈ Set.range j := by
  obtain ⟨R, _, _, _, b, ξ, m, t, Q, δ, a, G₁, _, y, α₁, ⟨hc, h0, -, hx, het, hun⟩, ⟨-, -, hr⟩, ⟨hs, hab, hy, hgen⟩, -⟩ := h
  exact ⟨{ R := R, complete := hc, charZero := h0, ξ := ξ, centre := hx, etc := het, unr := hun, G := G₁, semi := hs,
           y := y, hy := hy, α := α₁, gen := hgen }, fun p => (hab p).trans (hr p).symm⟩

end GlobalTheory.SiegDescent
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.GenericDec


open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison in
theorem gen_pull_div_of_gen_div {X Y : Scheme.{0}} (M N : LB X) (a : Y ⟶ X)
    (h : ∃ t : LB.Gen (LB.div (M.pull a) (N.pull a)), t.IsGen) :
    ∃ t : LB.Gen ((LB.div M N).pull a), t.IsGen := by
  refine exists_gen_transfer (L := LB.div (M.pull a) (N.pull a)) (L' := (LB.div M N).pull a)
    (fun p => ((fun _ => (p PUnit.unit).1), (fun _ => (p PUnit.unit).2))) (fun j y hy => ?_)
    (fun i j y hy => ?_) h
  · exact ⟨Set.mem_iInter.2 fun _ => (Set.mem_iInter.1 hy PUnit.unit).1,
      Set.mem_iInter.2 fun _ => (Set.mem_iInter.1 hy PUnit.unit).2⟩
  · have hM : a.base y ∈ M.U (i PUnit.unit).1 ⊓ M.U (j PUnit.unit).1 :=
      ⟨(Set.mem_iInter.1 hy.1 PUnit.unit).1, (Set.mem_iInter.1 hy.2 PUnit.unit).1⟩
    have hN : a.base y ∈ N.U (i PUnit.unit).2 ⊓ N.U (j PUnit.unit).2 :=
      ⟨(Set.mem_iInter.1 hy.1 PUnit.unit).2, (Set.mem_iInter.1 hy.2 PUnit.unit).2⟩
    refine (germ_pull (LB.div M N) a i j y hy ⟨⟨hM.1, hN.1⟩, ⟨hM.2, hN.2⟩⟩).trans ?_
    refine (gU_pullU a _ y _ _).trans ?_
    refine (congrArg _ (germ_div M N _ _ (a.base y) _)).trans ?_
    rw [map_mul, map_inv]
    refine Eq.trans ?_ (germ_div _ _ _ _ y _).symm
    exact congrArg₂ (· * ·) ((germ_pull M a (fun _ => (i PUnit.unit).1) (fun _ => (j PUnit.unit).1) y _ hM).trans (gU_pullU a _ y _ _)).symm
      (congrArg (·⁻¹) ((germ_pull N a (fun _ => (i PUnit.unit).2) (fun _ => (j PUnit.unit).2) y _ hN).trans (gU_pullU a _ y _ _)).symm)

theorem lbIso_of_generic {R' : Type} [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] [IsIntegrallyClosed R']
    [IsLocalRing R'] (G : Over (Sp R')) [GrpObj G] (hG : IsSemiAbelian G) {P Q : LB G.left} (hP : P.IsLB)
    (hQ : Q.IsLB) (h : LBIso (P.pull (pullback.fst G.hom (jK R'))) (Q.pull (pullback.fst G.hom (jK R')))) :
    LBIso P Q :=
  PicGenericInj.exists_gen_of_generic R' G hG (LB.div Q P) (LB.isLB_div hQ hP)
    (gen_pull_div_of_gen_div Q P _ h)

theorem sqDec_of_generic : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] [IsIntegrallyClosed R']
    [IsLocalRing R'] (G : Over (Sp R')) [GrpObj G], IsSemiAbelian G → ∀ (L M : LB G.left), L.IsLB → M.IsLB →
    SqDec ((Over.pullback (jK R')).obj G) (L.pull (pullback.fst G.hom (jK R')))
      (M.pull (pullback.fst G.hom (jK R'))) → SqDec G L M := by
  intro R' _ _ _ _ _ G _ hG L M hL hM hD
  obtain ⟨N, a₀, r, a, β, hN, ha₀, hβ, H⟩ := hD
  have ext : ∀ i, ∃ B : G ⟶ G, IsMonHom B ∧ (Over.pullback (jK R')).map B = β i := fun i =>
    (semiAbelian_hom_extend_generic R' G G hG hG (β i) (hβ i)).exists
  choose B hBm hBe using ext
  refine ⟨N, a₀, r, a, B, hN, ha₀, hBm, ?_⟩
  set f := pullback.fst G.hom (jK R') with hf
  have hc : ∀ o : Option (Fin r), (o.elim (𝟙 _) fun i => (β i).left) ≫ f =
      f ≫ (o.elim (𝟙 G.left) fun i => (B i).left) := by
    intro o
    cases o with
    | none => simp
    | some i =>
      simp only [Option.elim_some]
      rw [← hBe i]
      simp only [hf, Over.pullback_map_left, pullback.lift_fst]
  have i1 := (lbIso_lbPow_pull hL f N).symm
  have i5 := GlobalTheory.SymExtend.lbIso_linComb_pull hM f (fun o : Option (Fin r) => o.elim (𝟙 _) fun i => (β i).left)
    (fun o : Option (Fin r) => o.elim (𝟙 G.left) fun i => (B i).left) (fun o => o.elim (a₀ : ℤ) fun i => (a i : ℤ)) f hc
  have j1 := i1.trans (pull_isLB (isLB_lbPow hL N) f) (isLB_lbPow (pull_isLB hL f) N)
    (LB.isLB_linComb (pull_isLB hM f) _ _) H
  have j2 := j1.trans (pull_isLB (isLB_lbPow hL N) f) (LB.isLB_linComb (pull_isLB hM f) _ _)
    (pull_isLB (LB.isLB_linComb hM _ _) f) i5
  exact lbIso_of_generic G hG (isLB_lbPow hL N) (LB.isLB_linComb hM _ _) j2

end GlobalTheory.GenericDec
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.mem_cartierMultiple_chart_iff_regular_codimOne : ∀ (σ : Setup) (x : Sp σ.R) (k : ℕ) (v : (σ.C x).G.left.functionField), v ∈ Sec (σ.D₁ x) k ↔ (∀ z : (σ.V x).toScheme, (k • σ.D₁ x).RegularAt ((σ.V x).ι z) v) ∧ ∀ z, Vert (σ.C x).G.hom (σ.ρ x σ.f) z → RegAt z v := by
  first | exact @GlobalTheory.Desc.ChartHartogs.mem_sec_iff | exact GlobalTheory.Desc.ChartHartogs.mem_sec_iff | (intros; apply GlobalTheory.Desc.ChartHartogs.mem_sec_iff <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.chart_grpLaw_agrees_with_abelian_scheme_law : ∀ (σ : Setup) (E : Emb σ) (x : Sp σ.R), MulAgree (σ.C x).G σ.A (E.emb x) E.ιA := by
  first | exact @GlobalTheory.Desc.ChartLaw.chart_mulAgree | exact GlobalTheory.Desc.ChartLaw.chart_mulAgree | (intros; apply GlobalTheory.Desc.ChartLaw.chart_mulAgree <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.exists_pow_mul_mem_codimOne_regular_chart' : ∀ (σ : Setup) (x : Sp σ.R) (u : σ.A.left.functionField), ∃ m : ℕ, σ.c₀ σ.f ^ m * u ∈ σ.W x := by
  first | exact @GlobalTheory.Desc.exists_pow_mul_mem_codimOne_regular_chart | exact GlobalTheory.Desc.exists_pow_mul_mem_codimOne_regular_chart | (intros; apply GlobalTheory.Desc.exists_pow_mul_mem_codimOne_regular_chart <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.rationalFunction_app_of_preservesGenericPoint : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (m : Y ⟶ X) (φ : X.functionField →+* Y.functionField), PFF (𝟙 _) m φ → ∀ (V : X.Opens) (hV : genericPoint X ∈ V) (hV' : genericPoint Y ∈ m ⁻¹ᵁ V) (a : Γ(X, V)), fnOf (m ⁻¹ᵁ V) hV' ((m.app V).hom a) = φ (fnOf V hV a) := by
  first | exact @GlobalTheory.Desc.fnOf_app_of_pff | exact GlobalTheory.Desc.fnOf_app_of_pff | (intros; apply GlobalTheory.Desc.fnOf_app_of_pff <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
open TensorProduct

theorem _root_.GlobalTheory.T.span_iInter_submodules_of_flat_baseChange : ∀ (R R₁ K L : Type) [CommRing R] [CommRing R₁] [CommRing K] [CommRing L] [Algebra R R₁] [Algebra R K] [Module.Flat R R₁] (θ : K →+* L) (c : R₁ →+* L), (∀ a : R, θ (algebraMap R K a) = c (algebraMap R R₁ a)) → (∀ (n : ℕ) (u : Fin n → K) (r : Fin n → R₁), ∑ j, c (r j) * θ (u j) = 0 → ∑ j, u j ⊗ₜ[R] r j = 0) → ∀ (J : Type) [Finite J] [Nonempty J] (N : J → Submodule R K), spanBy c (θ '' ⋂ j, (N j : Set K)) = ⋂ j, spanBy c (θ '' (N j : Set K)) := by
  first | exact @GlobalTheory.Desc.spanBy_iInter_of_flat | exact GlobalTheory.Desc.spanBy_iInter_of_flat | (intros; apply GlobalTheory.Desc.spanBy_iInter_of_flat <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.exists_cartierSectionLocus_of_ample_span : ∀ (R₁ F : Type) [CommRing R₁] [Field F] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp R₁) (θ : F →+* Y.functionField) (N : ℕ → Set F) (D₁ : CartierDiv Y), AmpleDiv D₁ → (∀ k, Sec D₁ k = spanBy (GlobalTheory.Desc.cst q) (θ '' N k)) → ∀ y : Y, ∃ k, 1 ≤ k ∧ ∃ b ∈ N k, y ∈ locus D₁ k (θ b) := by
  first | exact @GlobalTheory.Desc.exists_locus_of_span | exact GlobalTheory.Desc.exists_locus_of_span | (intros; apply GlobalTheory.Desc.exists_locus_of_span <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.exists_hom_to_affineOpen_of_functionField_map_regular : ∀ (Y P : Scheme.{0}) [IsIntegral Y] [IsIntegral P] (U : Y.Opens), genericPoint Y ∈ U → ∀ (V : P.Opens), IsAffineOpen V → ∀ (hVη : genericPoint P ∈ V) (φ : P.functionField →+* Y.functionField), (∀ s : Γ(P, V), ∀ y ∈ U, RegAt y (φ (fnOf V hVη s))) → ∃ f : U.toScheme ⟶ P, (∀ y : U.toScheme, f y ∈ V) ∧ ∀ l : Sp Y.functionField ⟶ U.toScheme, l ≫ U.ι = gp Y → l ≫ f = spMap φ ≫ gp P := by
  first | exact @GlobalTheory.Desc.exists_hom_of_regAt_fnOf | exact GlobalTheory.Desc.exists_hom_of_regAt_fnOf | (intros; apply GlobalTheory.Desc.exists_hom_of_regAt_fnOf <;> assumption)
end

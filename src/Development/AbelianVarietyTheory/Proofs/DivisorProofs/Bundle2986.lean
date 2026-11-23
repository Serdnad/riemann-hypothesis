module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2860
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2870
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2867
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleNeighbourhoodFinitePieceIsolatedPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2789
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle243
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2868
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2869
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

noncomputable section

namespace GlobalTheory.Poinc.Sep.Spz

theorem link_of_normal : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), (U₀ : Set M.Z).Nonempty → ∀ (O : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O] [Algebra O Ω] [IsFractionRing O Ω] (x : Sp O ⟶ M.Z) (u : S.R →+* O), spMap (algebraMap O Ω) ≫ x = M.pt → (algebraMap O Ω).comp u = S.R.val.toRingHom → ∃ gm : ((Over.pullback (spMap u)).obj ρ.P.A).left ⟶ FinalForm.G.left, Link FinalForm x (spMap u) ((Over.pullback (spMap u)).obj ρ.P.A) (pullback.fst ρ.P.A.hom (spMap u)) gm := by
  intro o Ω _ _ _ _ S ρ M U₀ EE FinalForm hU O _ _ _ _ _ _ x u hx hu

  have hr : Set.range M.pt ⊆ Set.range U₀.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact M.top_le_preimage_pt hU (x := w) trivial
  let x₀ : Sp Ω ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι M.pt hr
  have hx₀ : x₀ ≫ U₀.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  have hxu : x₀ ≫ FinalForm.u₀ = spMap S.R.val.toRingHom := FinalForm.u₀_gen x₀ hx₀
  let j : Sp Ω ⟶ Sp O := spMap (algebraMap O Ω)
  have hju : j ≫ spMap u = spMap S.R.val.toRingHom := (spMap_comp u (algebraMap O Ω)).symm.trans (congrArg spMap hu)

  let Q := (Over.pullback FinalForm.u₀).obj ρ.P.A
  let A₀ := (Over.pullback M.pt).obj FinalForm.G
  let ν : pullback FinalForm.G.hom M.pt ⟶ pullback ρ.P.A.hom FinalForm.u₀ :=
    FinalForm.cart.1.lift (pullback.fst FinalForm.G.hom M.pt) (pullback.snd FinalForm.G.hom M.pt ≫ x₀)
             (by rw [pullback.condition, Category.assoc, hx₀])
  have hν₁ : ν ≫ FinalForm.φ = pullback.fst FinalForm.G.hom M.pt := FinalForm.cart.1.lift_fst _ _ _
  have hν₂ : ν ≫ Q.hom = pullback.snd FinalForm.G.hom M.pt ≫ x₀ := FinalForm.cart.1.lift_snd _ _ _
  have gη : IsGrpPullback A₀ FinalForm.G (x₀ ≫ U₀.ι) (ν ≫ FinalForm.φ) :=
    (isGrpPullback_pullback FinalForm.G M.pt).congr hx₀.symm hν₁.symm
  have gν : IsGrpPullback A₀ Q x₀ ν := FinalForm.cart.cancel gη hν₂
  have gψ : IsGrpPullback A₀ ρ.P.A (j ≫ spMap u) (ν ≫ pullback.fst ρ.P.A.hom FinalForm.u₀) :=
    (gν.comp (isGrpPullback_pullback ρ.P.A FinalForm.u₀)).congr (by rw [hju, hxu]) rfl

  let A := (Over.pullback (spMap u)).obj ρ.P.A
  have hA := isGrpPullback_pullback ρ.P.A (spMap u)
  have wA : (ν ≫ pullback.fst ρ.P.A.hom FinalForm.u₀) ≫ ρ.P.A.hom = (A₀.hom ≫ j) ≫ spMap u := by
    rw [gψ.1.w, Category.assoc]
  let φ₂ : A₀.left ⟶ A.left := hA.1.lift _ _ wA
  have eφ₂ : φ₂ ≫ pullback.fst ρ.P.A.hom (spMap u) = ν ≫ pullback.fst ρ.P.A.hom FinalForm.u₀ := hA.1.lift_fst _ _ _
  have sφ₂ : φ₂ ≫ A.hom = A₀.hom ≫ j := hA.1.lift_snd _ _ _
  have hφ₂ : IsGrpPullback A₀ A j φ₂ := hA.cancel (gψ.congr rfl eφ₂.symm) sφ₂

  let GO := (Over.pullback x).obj FinalForm.G
  have hGO := isGrpPullback_pullback FinalForm.G x
  have gη' : IsGrpPullback A₀ FinalForm.G (j ≫ x) (pullback.fst FinalForm.G.hom M.pt) :=
    (isGrpPullback_pullback FinalForm.G M.pt).congr hx.symm rfl
  have wG : pullback.fst FinalForm.G.hom M.pt ≫ FinalForm.G.hom = (A₀.hom ≫ j) ≫ x := by rw [gη'.1.w, Category.assoc]
  let φ₁ : A₀.left ⟶ GO.left := hGO.1.lift _ _ wG
  have eφ₁ : φ₁ ≫ pullback.fst FinalForm.G.hom x = pullback.fst FinalForm.G.hom M.pt := hGO.1.lift_fst _ _ _
  have hφ₁ : IsGrpPullback A₀ GO j φ₁ := hGO.cancel (gη'.congr rfl eφ₁.symm) (hGO.1.lift_snd _ _ _)
  have sA : IsSemiAbelian A := IsSemiAbelian.pullback _ _ (GlobalTheory.isSemiAbelian_of_isAbelianScheme _ ρ.P.isAb)
  have sG : IsSemiAbelian GO := IsSemiAbelian.pullback _ _ FinalForm.semi
  obtain ⟨E, ⟨hE, hEφ⟩, -⟩ := GlobalTheory.semiAbelianHomExtension_holds.generic_existsUnique_iso_of_extensions
    (GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec O) (GlobalTheory.IsGenericPointHom.fractionField O Ω) sA sG hφ₂ hφ₁
  haveI := hE
  let gm : A.left ⟶ FinalForm.G.left := E.hom.left ≫ pullback.fst FinalForm.G.hom x
  have hgm : IsGrpPullback A FinalForm.G x gm := ((isGrpPullback_of_iso E).comp hGO).congr (Category.id_comp _) rfl
  have key : φ₂ ≫ gm = ν ≫ FinalForm.φ := by
    show φ₂ ≫ E.hom.left ≫ pullback.fst FinalForm.G.hom x = _
    rw [← Category.assoc, hEφ, eφ₁, hν₁]
  have hgmw : gm ≫ FinalForm.G.hom = A.hom ≫ x := hgm.1.w
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian _ sA
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian _ FinalForm.semi
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.spec_fractionRing O Ω
  haveI : IsSchemeTheoreticallyDominant φ₂ := .of_isPullback hφ₂.1.flip
  refine ⟨gm, hgm, ?_, ?_⟩
  · intro f Fm hf T' p p' h₁ h₂
    let fO := (Over.pullback (spMap u)).map f
    let fQ := (Over.pullback FinalForm.u₀).map f
    have hfO₁ : fO.left ≫ pullback.fst ρ.P.A.hom (spMap u) = pullback.fst ρ.P.A.hom (spMap u) ≫ f.left :=
      pullback.lift_fst _ _ _
    have hfQ₁ : fQ.left ≫ pullback.fst ρ.P.A.hom FinalForm.u₀ = pullback.fst ρ.P.A.hom FinalForm.u₀ ≫ f.left :=
      pullback.lift_fst _ _ _
    have hfO₂ : fO.left ≫ A.hom = A.hom := Over.w fO
    have hp' : p' = p ≫ fO.left := by
      apply pullback.hom_ext
      · rw [h₂, Category.assoc, hfO₁]
      · show p' ≫ A.hom = (p ≫ fO.left) ≫ A.hom
        rw [Category.assoc, hfO₂, h₁]
    have wk : (ν ≫ fQ.left) ≫ Q.hom = A₀.hom ≫ x₀ := by
      rw [Category.assoc, Over.w fQ, gν.1.w]
    let k : A₀.left ⟶ A₀.left := gν.1.lift _ _ wk
    have hk₁ : k ≫ ν = ν ≫ fQ.left := gν.1.lift_fst _ _ _
    have hk₂ : k ≫ A₀.hom = A₀.hom := gν.1.lift_snd _ _ _
    have hφk : φ₂ ≫ fO.left = k ≫ φ₂ := by
      apply pullback.hom_ext
      · simp only [Category.assoc, hfO₁, eφ₂, reassoc_of% eφ₂, reassoc_of% hk₁, hfQ₁]
      · show (φ₂ ≫ fO.left) ≫ A.hom = (k ≫ φ₂) ≫ A.hom
        rw [Category.assoc, hfO₂, Category.assoc, sφ₂, ← Category.assoc, hk₂]
    have main : fO.left ≫ gm = gm ≫ Fm.left := by
      refine GlobalTheory.ExtUnique.hom_ext_of_dominant FinalForm.G.hom ?_ φ₂ ?_
      · rw [Category.assoc, hgmw, ← Category.assoc, hfO₂, Category.assoc, Over.w Fm, hgmw]
      · calc φ₂ ≫ fO.left ≫ gm = k ≫ φ₂ ≫ gm := by rw [← Category.assoc, hφk, Category.assoc]
          _ = (k ≫ ν) ≫ FinalForm.φ := by rw [key, Category.assoc]
          _ = ν ≫ FinalForm.φ ≫ Fm.left := by rw [hk₁, Category.assoc, hf]
          _ = φ₂ ≫ gm ≫ Fm.left := by rw [← Category.assoc, ← key, Category.assoc]
    rw [hp', Category.assoc, main]
  · intro a Wo h hs T' p x' h₁ h₂
    have hpa : (ρ.pt a).left ≫ ρ.P.A.hom = 𝟙 _ := by simpa [baseOver] using Over.w (ρ.pt a)
    let σ : Sp O ⟶ A.left := pullback.lift (spMap u ≫ (ρ.pt a).left) (𝟙 (Sp O))
      (by rw [Category.assoc, hpa]; simp)
    have hσ₁ : σ ≫ pullback.fst ρ.P.A.hom (spMap u) = spMap u ≫ (ρ.pt a).left := pullback.lift_fst _ _ _
    have hσ₂ : σ ≫ A.hom = 𝟙 _ := pullback.lift_snd _ _ _
    have hp : p = (p ≫ A.hom) ≫ σ := by
      apply pullback.hom_ext
      · rw [Category.assoc, hσ₁, h₂, Category.assoc]
      · show p ≫ A.hom = ((p ≫ A.hom) ≫ σ) ≫ A.hom
        rw [Category.assoc, hσ₂, Category.comp_id]
    let O' := x ⁻¹ᵁ Wo
    have hpb := isPullback_morphismRestrict x Wo
    let q : T' ⟶ O'.toScheme := hpb.lift x' (p ≫ A.hom) (by rw [h₁, Category.assoc])
    have hq₁ : q ≫ (x ∣_ Wo) = x' := hpb.lift_fst _ _ _
    have hq₂ : q ≫ O'.ι = p ≫ A.hom := hpb.lift_snd _ _ _
    have hmain : O'.ι ≫ σ ≫ gm = (x ∣_ Wo) ≫ h := by
      by_cases hO : (O' : Set (Sp O)).Nonempty
      · have hr' : Set.range j ⊆ Set.range O'.ι := by
          rw [Scheme.Opens.range_ι, (GlobalTheory.IsGenericPointHom.fractionField O Ω).range_eq, Set.singleton_subset_iff]
          exact ((genericPoint_spec (Sp O)).mem_open_set_iff O'.isOpen).2 (by simpa using hO)
        let jO : Sp Ω ⟶ O'.toScheme := IsOpenImmersion.lift O'.ι j hr'
        have hjO : jO ≫ O'.ι = j := IsOpenImmersion.lift_fac _ _ _
        haveI : IsDominant (jO ≫ O'.ι) := by rw [hjO]; infer_instance
        haveI : IsDominant jO := IsDominant.of_comp_of_isOpenImmersion jO O'.ι
        refine ext_of_isDominant_of_isSeparated FinalForm.G.hom ?_ jO ?_
        · simp only [Category.assoc]
          rw [hgmw, ← Category.assoc σ, hσ₂, Category.id_comp, hs.1, morphismRestrict_ι]
        · let x'' : Sp Ω ⟶ pullback ρ.P.A.hom FinalForm.u₀ := pullback.lift (spMap S.R.val.toRingHom ≫ (ρ.pt a).left) x₀
            (by rw [Category.assoc, hpa, hxu]; simp)
          have hx''₁ : x'' ≫ pullback.fst ρ.P.A.hom FinalForm.u₀ = spMap S.R.val.toRingHom ≫ (ρ.pt a).left :=
            pullback.lift_fst _ _ _
          have hx''₂ : x'' ≫ pullback.snd ρ.P.A.hom FinalForm.u₀ = x₀ := pullback.lift_snd _ _ _
          have hsec := hs.2 (jO ≫ (x ∣_ Wo)) x''
            (by rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hjO, hx])
            (by rw [FinalForm.cart.1.w, ← Category.assoc]; erw [hx''₂]; exact hx₀) hx''₁
          let e : Sp Ω ⟶ A₀.left := hφ₂.1.lift (j ≫ σ) (𝟙 _) (by rw [Category.assoc, hσ₂, Category.comp_id, Category.id_comp])
          have he₁ : e ≫ φ₂ = j ≫ σ := hφ₂.1.lift_fst _ _ _
          have he₂ : e ≫ A₀.hom = 𝟙 _ := hφ₂.1.lift_snd _ _ _
          have heν : e ≫ ν = x'' := by
            apply pullback.hom_ext
            · rw [hx''₁, Category.assoc, ← eφ₂, ← Category.assoc, he₁, Category.assoc, hσ₁, ← Category.assoc, hju]
            · rw [hx''₂, Category.assoc]
              erw [hν₂]
              rw [← Category.assoc]
              erw [he₂]
              rw [Category.id_comp]
          calc jO ≫ O'.ι ≫ σ ≫ gm = (e ≫ φ₂) ≫ gm := by rw [← Category.assoc, hjO, he₁, Category.assoc]
            _ = (e ≫ ν) ≫ FinalForm.φ := by rw [Category.assoc, key, Category.assoc]
            _ = jO ≫ (x ∣_ Wo) ≫ h := by rw [heν, ← Category.assoc, hsec]
      · haveI : IsEmpty O'.toScheme := ⟨fun y => hO ⟨y.1, y.2⟩⟩
        exact isInitialOfIsEmpty.hom_ext _ _
    rw [hp, ← hq₂, ← hq₁, Category.assoc, Category.assoc, hmain, Category.assoc]

end GlobalTheory.Poinc.Sep.Spz
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_open_etale_restrict_of_universallyClosed' : ∀ (X P' T : Scheme.{0}) (a : X ⟶ P') (W1 : P'.Opens) (c : (a ⁻¹ᵁ W1).toScheme ⟶ T) (x : P'), UniversallyClosed a → x ∈ W1 → (∀ z : (a ⁻¹ᵁ W1).toScheme, ((a ⁻¹ᵁ W1).ι ≫ a) z = x → ∃ U : (a ⁻¹ᵁ W1).toScheme.Opens, z ∈ U ∧ Etale (U.ι ≫ c)) → ∃ W : P'.Opens, W ≤ W1 ∧ x ∈ W ∧ ∀ hle : a ⁻¹ᵁ W ≤ a ⁻¹ᵁ W1, Etale (X.homOfLE hle ≫ c) := by
  first | exact @GlobalTheory.exists_open_etale_restrict_of_universallyClosed | exact GlobalTheory.exists_open_etale_restrict_of_universallyClosed | (intros; apply GlobalTheory.exists_open_etale_restrict_of_universallyClosed <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.fibre_etale_restrict_open_alt : ∀ (T X Z T' X' Z' S : Scheme.{0}) (p : X ⟶ T) (q : Z ⟶ T) (h : X ⟶ Z) (hh : h ≫ q = p) (p' : X' ⟶ T') (q' : Z' ⟶ T') (h' : X' ⟶ Z') (hh' : h' ≫ q' = p') (iT : T' ⟶ T) (iX : X' ⟶ X) (iZ : Z' ⟶ Z) [IsOpenImmersion iT] [IsOpenImmersion iX] [IsOpenImmersion iZ] (sZ : iZ ≫ q = q' ≫ iT) (sh : iX ≫ h = h' ≫ iZ) (x : S ⟶ T) (x' : S ⟶ T') (sx : x' ≫ iT = x) (W : (pullback p x).Opens) (w : ↥(pullback p x)) (hw : w ∈ W) (hz : pullback.fst p x w ∈ Set.range iX), Etale (W.ι ≫ pullback.map p x q x h (𝟙 _) (𝟙 _) (by simp [hh]) (by simp)) → ∃ (W' : (pullback p' x').Opens) (w' : ↥(pullback p' x')), w' ∈ W' ∧ iX (pullback.fst p' x' w') = pullback.fst p x w ∧ Etale (W'.ι ≫ pullback.map p' x' q' x' h' (𝟙 _) (𝟙 _) (by simp [hh']) (by simp)) := by
  first | exact @GlobalTheory.fibre_etale_restrict_open | exact GlobalTheory.fibre_etale_restrict_open | (intros; apply GlobalTheory.fibre_etale_restrict_open <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.exists_etale_neighbourhood_finite_piece_isolated_point : ∀ (U Y : Scheme.{0}) (τ : U ⟶ Y), IsLocallyNoetherian Y → LocallyOfFiniteType τ → IsSeparated τ → ∀ x : U, (∃ O : U.Opens, x ∈ O ∧ ∀ u ∈ O, τ u = τ x → u = x) → ∃ (T : Scheme.{0}) (h : T ⟶ Y) (W : (pullback τ h).Opens) (p : ↥(pullback τ h)), Etale h ∧ PreconnectedSpace T ∧ p ∈ W ∧ pullback.fst τ h p = x ∧ IsFinite (W.ι ≫ pullback.snd τ h) ∧ (∀ w ∈ W, pullback.snd τ h w = pullback.snd τ h p → w = p) ∧ ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ T), Set.range t = {pullback.snd τ h p} → ∃! w : Sp Ω ⟶ W.toScheme, w ≫ W.ι ≫ pullback.snd τ h = t := by
  first | exact @GlobalTheory.EtaleFinitePiece.main | exact GlobalTheory.EtaleFinitePiece.main | (intros; apply GlobalTheory.EtaleFinitePiece.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_finite_openImmersion_nbhd_isolatedFibrePoints : ∀ (H X : Scheme.{0}) (φ : H ⟶ X), IsNoetherian X → IsSeparated φ → LocallyOfFiniteType φ → QuasiCompact φ → ∀ Z : Set H, (∀ z ∈ Z, ∃ O : H.Opens, z ∈ O ∧ ∀ w ∈ O, φ w = φ z → w = z) → ∃ (H' : H.Opens) (X' : Scheme.{0}) (ν : X' ⟶ X) (i : H'.toScheme ⟶ X'), Z ⊆ H' ∧ IsFinite ν ∧ IsOpenImmersion i ∧ i ≫ ν = H'.ι ≫ φ ∧ IsDominant i ∧ ∀ V : X'.Opens, Function.Injective (i.app V).hom := by
  first | exact @GlobalTheory.ZmtNbhd.exists_finite_openImmersion_nbhd | exact GlobalTheory.ZmtNbhd.exists_finite_openImmersion_nbhd | (intros; apply GlobalTheory.ZmtNbhd.exists_finite_openImmersion_nbhd <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section

namespace GlobalTheory.SecCompact

theorem exists_openImmersion_genericFibre (F : Type) [Field F] (o : Type) [CommRing o] [Algebra o F]
    [IsFractionRing o F] [Algebra.FiniteType ℤ o] (m : ℕ) (X : Scheme.{0}) (sX : X ⟶ Sp F) [IsReduced X]
    [IsSeparated sX] [LocallyOfFiniteType sX] [QuasiCompact sX] (f : X ⟶ PSpace o m) [QuasiCompact f]
    [QuasiSeparated f] (hf : f ≫ PSpace.str o m = sX ≫ spMap (algebraMap o F))
    (hfib : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ X),
      Set.Finite {y : Sp K ⟶ X | y ≫ sX = x ≫ sX ∧ y ≫ f = x ≫ f}) :
    IsFinite f.fromNormalization ∧
      ∃ iF : X ⟶ pullback (f.fromNormalization ≫ PSpace.str o m) (spMap (algebraMap o F)),
        IsOpenImmersion iF ∧ Dense (Set.range iF) ∧ iF ≫ pullback.snd _ _ = sX ∧
          iF ≫ pullback.fst _ _ = f.toNormalization := by
  haveI := isProper_str o m
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI := IsPreimmersion.of_isLocalization (R := o) (S := F) (nonZeroDivisors o)
  haveI : Algebra.FiniteType ℤ (CommRingCat.of o) := ‹Algebra.FiniteType ℤ o›
  refine ⟨GlobalTheory.NormBlowupInt.isFinite_fromNormalization_int_of_isReduced (o := CommRingCat.of o) f
    (PSpace.str o m) fun x _ => ?_, ?_⟩
  · have h1 : ((f ≫ PSpace.str o m).stalkMap x).hom.EssFiniteType := by
      rw [hf, Scheme.Hom.stalkMap_comp]
      exact .comp (RingHom.FiniteType.of_surjective _
        (Scheme.Hom.stalkMap_surjective _ _)).essFiniteType (LocallyOfFiniteType.stalkMap sX x)
    rw [Scheme.Hom.stalkMap_comp] at h1
    have h2 : (f.stalkMap x).hom.EssFiniteType := .of_comp _ h1
    exact h2.residueFieldMap
  have hb := IsPullback.of_hasPullback (PSpace.str o m) (spMap (algebraMap o F))
  let f' : X ⟶ pullback (PSpace.str o m) (spMap (algebraMap o F)) := pullback.lift f sX hf
  have e₁ : f' ≫ pullback.fst _ _ = f := pullback.lift_fst _ _ _
  have e₂ : f' ≫ pullback.snd _ _ = sX := pullback.lift_snd _ _ _
  haveI : LocallyOfFiniteType (f' ≫ pullback.snd _ _) := by rw [e₂]; infer_instance
  haveI : LocallyOfFiniteType f' := locallyOfFiniteType_of_comp f' (pullback.snd _ _)
  haveI : QuasiCompact (f' ≫ pullback.snd _ _) := by rw [e₂]; infer_instance
  haveI : QuasiCompact f' := QuasiCompact.of_comp f' (pullback.snd _ _)
  haveI : IsSeparated (f' ≫ pullback.snd _ _) := by rw [e₂]; infer_instance
  haveI : IsSeparated f' := IsSeparated.of_comp f' (pullback.snd _ _)
  haveI : LocallyQuasiFinite f' := by
    refine GlobalTheory.GeomFibre.locallyQuasiFinite_of_finite_geometric_fibres X _ f' inferInstance fun K _ _ x => ?_
    refine (hfib K x).subset fun y (hy : y ≫ f' = x ≫ f') => ⟨?_, ?_⟩
    · rw [← e₂, ← Category.assoc, hy, Category.assoc]
    · rw [← e₁, ← Category.assoc, hy, Category.assoc]
  obtain ⟨hoi, -, hdom⟩ :=
    GlobalTheory.isOpenImmersion_lift_toNormalization_of_isLocalization (M := nonZeroDivisors o) hb f' f e₁.symm
  refine ⟨pullback.lift f.toNormalization f' (by simp [e₁]) ≫
    (pullbackRightPullbackFstIso (PSpace.str o m) (spMap (algebraMap o F)) f.fromNormalization).hom,
    inferInstance, (Scheme.Hom.denseRange _), ?_, ?_⟩
  · rw [Category.assoc, pullbackRightPullbackFstIso_hom_snd, pullback.lift_snd_assoc, e₂]
  · rw [Category.assoc, pullbackRightPullbackFstIso_hom_fst, pullback.lift_fst]

end GlobalTheory.SecCompact
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.finite_stalk_germ_quotient_integral_unit_denominator : ∀ (X Y : Scheme.{0}) (p : Y ⟶ X), IsFinite p → ∀ (y : Y) (a : Y.presheaf.stalk y), ∃ b s : Y.presheaf.stalk y, IsUnit s ∧ a * s = b ∧ (∃ P : Polynomial (X.presheaf.stalk (p y)), P.Monic ∧ P.eval₂ (p.stalkMap y).hom b = 0) ∧ ∃ Q : Polynomial (X.presheaf.stalk (p y)), Q.Monic ∧ Q.eval₂ (p.stalkMap y).hom s = 0 := by
  first | exact @GlobalTheory.Poinc.finite_stalk_quot_integral | exact GlobalTheory.Poinc.finite_stalk_quot_integral | (intros; apply GlobalTheory.Poinc.finite_stalk_quot_integral <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_fieldPoint_lift_finite_surjective_morphism : ∀ (U X : Scheme.{0}) (c : U ⟶ X) [IsFinite c] [Surjective c] (K : Type) [Field K] (y : Sp K ⟶ X), ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K') (y' : Sp K' ⟶ U), y' ≫ c = spMap (algebraMap K K') ≫ y := by
  first | exact @GlobalTheory.FinLift.lift_fieldPoint | exact GlobalTheory.FinLift.lift_fieldPoint | (intros; apply GlobalTheory.FinLift.lift_fieldPoint <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_lift_fieldPoint_finite_surjective_after_extension : ∀ (K : Type) [Field K] (X Y : Scheme.{0}) (y : Sp K ⟶ X) (q : Y ⟶ X), IsFinite q → Surjective q → ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L) (y' : Sp L ⟶ Y), y' ≫ q = spMap (algebraMap K L) ≫ y := by
  first | exact @GlobalTheory.FinLift.lift_point_finite_surjective | exact GlobalTheory.FinLift.lift_point_finite_surjective | (intros; apply GlobalTheory.FinLift.lift_point_finite_surjective <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.normal_scheme_extension_through_finite_cover : ∀ (o : Type) [CommRing o] (N : ℕ) (S' X Z : Scheme.{0}) (U : S'.Opens) (c : U.toScheme ⟶ X) (i : X ⟶ Z) (p : Z ⟶ PSpace o N) (h : S' ⟶ PSpace o N), IsIntegral S' → Geo.Tor.IsNormalScheme S' → IsIntegral Z → Dense (U : Set S') → IsDominant c → IsFinite p → IsOpenImmersion i → Dense (Set.range i) → U.ι ≫ h = c ≫ i ≫ p → ∃ π : S' ⟶ Z, U.ι ≫ π = c ≫ i ∧ π ≫ p = h := by
  first | exact @GlobalTheory.NormalFiniteLift.exists_lift_of_finite | exact GlobalTheory.NormalFiniteLift.exists_lift_of_finite | (intros; apply GlobalTheory.NormalFiniteLift.exists_lift_of_finite <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.isFinite_fromSpecResidueField_comp_of_closed : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Over (Sp R)), LocallyOfFiniteType X.hom → ∀ x : X.left, X.hom x = closedPoint R → IsClosed ({x} : Set X.left) → IsFinite (X.left.fromSpecResidueField x ≫ X.hom) := by
  first | exact @GlobalTheory.isFinite_fromSpecResidueField_comp_of_isClosed_of_closedPoint | exact GlobalTheory.isFinite_fromSpecResidueField_comp_of_isClosed_of_closedPoint | (intros; apply GlobalTheory.isFinite_fromSpecResidueField_comp_of_isClosed_of_closedPoint <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.mem_range_app_of_flat_baseChange_equalised : ∀ (R : Type) [CommRing R] (S Y Z : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), IsProper π → Flat y → IsPullback p q y π → ∀ r : pullback p p ⟶ pullback π π, r ≫ pullback.fst π π = pullback.fst p p ≫ q → r ≫ pullback.snd π π = pullback.snd p p ≫ q → IsPullback r (pullback.fst p p ≫ p) (pullback.fst π π ≫ π) y → (∀ x : Γ(S, ⊤), (pullback.fst π π).appTop.hom x = (pullback.snd π π).appTop.hom x → x ∈ Set.range π.appTop.hom) → ∀ V : Y.Opens, IsAffineOpen V → ∀ f : Γ(Z, p ⁻¹ᵁ V), (∀ h : pullback.snd p p ⁻¹ᵁ (p ⁻¹ᵁ V) = pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V), ((pullback.fst p p).app _).hom f = ((pullback.snd p p).appLE _ _ h.ge).hom f) → f ∈ Set.range (p.app V).hom := by
  first | exact @GlobalTheory.Mum.AffDesc.mem_range_app_of_flat | exact GlobalTheory.Mum.AffDesc.mem_range_app_of_flat | (intros; apply GlobalTheory.Mum.AffDesc.mem_range_app_of_flat <;> assumption)
end

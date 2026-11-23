module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.OreLocalization.Ring
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle001
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle097
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DivMemOfForallPowSuccDivPowMem
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.DivSheafA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaGlue

theorem hom_ext_of_geometric {Z P S : Scheme.{0}} [IsReduced Z] (q : P ⟶ S) [IsSeparated q] (a b : Z ⟶ P)
    (hq : a ≫ q = b ≫ q)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ Z), y ≫ a = y ≫ b) : a = b := by
  let T : Z → Scheme.{0} := fun z => Sp (AlgebraicClosure (Z.residueField z))
  let pt : ∀ z, T z ⟶ Z := fun z =>
    spMap (algebraMap (Z.residueField z) (AlgebraicClosure (Z.residueField z))) ≫ Z.fromSpecResidueField z
  let m : (∐ T) ⟶ Z := Sigma.desc pt
  have hs : Function.Surjective m.base := by
    intro z
    refine ⟨(Sigma.ι T z).base default, ?_⟩
    rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]
    simp only [pt, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply _ _
  have : IsDominant m := ⟨hs.denseRange⟩
  refine ext_of_isDominant_of_isSeparated q hq m ?_
  refine Sigma.hom_ext _ _ fun z => ?_
  simp only [m, Sigma.ι_desc_assoc]
  exact h _ (pt z)

theorem glue_geom : ∀ (o : Type) [CommRing o] (n : ℕ) (X : Scheme.{0}) [IsReduced X] (s : X ⟶ Sp o) (I : Type)
    (W : I → X.Opens) (f : ∀ i, (W i).toScheme ⟶ PSpace o n), (⨆ i, W i) = ⊤ →
    (∀ i, f i ≫ PSpace.str o n = (W i).ι ≫ s) →
    (∀ i j (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ (W i).toScheme) (y' : Sp K ⟶ (W j).toScheme),
      y ≫ (W i).ι = y' ≫ (W j).ι → y ≫ f i = y' ≫ f j) →
    ∃ g : X ⟶ PSpace o n, g ≫ PSpace.str o n = s ∧ ∀ i, (W i).ι ≫ g = f i := by
  intro o _ n X _ s I W f hW hf hg
  have : IsSeparated (PSpace.str o n) := by
    have := isProper_str o n
    infer_instance
  let 𝒰 := X.openCoverOfIsOpenCover W hW
  have hc : ∀ a b, pullback.fst (W a).ι (W b).ι ≫ f a = pullback.snd (W a).ι (W b).ι ≫ f b := by
    intro a b
    have : IsReduced (pullback (W a).ι (W b).ι) :=
      isReduced_of_isOpenImmersion (pullback.fst _ _ ≫ (W a).ι)
    refine hom_ext_of_geometric (PSpace.str o n) _ _ ?_ fun K _ _ y => ?_
    · rw [Category.assoc, Category.assoc, hf, hf, pullback.condition_assoc]
    · rw [← Category.assoc, ← Category.assoc]
      exact hg a b K _ _ (by rw [Category.assoc, Category.assoc, pullback.condition])
  have he : ∀ a, (W a).ι ≫ 𝒰.glueMorphisms f hc = f a := fun a => 𝒰.ι_glueMorphisms f hc a
  refine ⟨𝒰.glueMorphisms f hc, 𝒰.hom_ext _ _ fun (a : I) => ?_, he⟩
  change (W a).ι ≫ _ = (W a).ι ≫ _
  rw [← Category.assoc, he, hf]

end GlobalTheory.ThetaGlue
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem glue_field_points (R : Type) [CommRing R]
    (P : (K : Type) → [Field K] → (R →+* K) → K → Prop)
    (huniq : ∀ (K : Type) [Field K] (i : R →+* K) (u v : K), P K i u → P K i v → u = v)
    (hloc : ∀ p : Ideal R, p.IsPrime → ∃ f ∉ p, ∃ c : Localization.Away f,
      ∀ (K : Type) [Field K] (j : Localization.Away f →+* K),
        P K (j.comp (algebraMap R (Localization.Away f))) (j c)) :
    ∃ c : R, ∀ (K : Type) [Field K] (i : R →+* K), P K i (i c) := by
  classical
  have hloc' : ∀ k : {p : Ideal R // p.IsPrime}, ∃ f ∉ k.1, ∃ c : Localization.Away f,
      ∀ (K : Type) [Field K] (j : Localization.Away f →+* K),
        P K (j.comp (algebraMap R (Localization.Away f))) (j c) := fun k => hloc k.1 k.2
  choose f hf c hc using hloc'
  have hsurj : ∀ k : {p : Ideal R // p.IsPrime}, ∃ (a : R) (n : ℕ),
      c k * algebraMap R _ (f k ^ n) = algebraMap R _ a := by
    intro k
    obtain ⟨n, a, h⟩ := IsLocalization.Away.surj (f k) (c k)
    exact ⟨a, n, by rw [map_pow]; exact h⟩
  choose a n ha using hsurj

  have key : ∀ (K : Type) [Field K] (i : R →+* K) (k : {p : Ideal R // p.IsPrime}),
      i (f k) ≠ 0 → ∃ v, P K i v ∧ v * i (f k) ^ n k = i (a k) := by
    intro K _ i k hk
    let j : Localization.Away (f k) →+* K :=
      IsLocalization.Away.lift (f k) (isUnit_iff_ne_zero.mpr hk)
    have hj : j.comp (algebraMap R _) = i := by first | exact IsLocalization.Away.lift_comp _ | exact IsLocalization.lift_comp _
    refine ⟨j (c k), ?_, ?_⟩
    · have := hc k K j
      rwa [hj] at this
    · have h2 := congrArg j (ha k)
      rw [map_mul, ← RingHom.comp_apply, ← RingHom.comp_apply, hj, map_pow] at h2
      exact h2

  have hnil : ∀ k l : {p : Ideal R // p.IsPrime},
      IsNilpotent (f k * f l * (a k * f l ^ n l - a l * f k ^ n k)) := by
    intro k l
    rw [← mem_nilradical, nilradical_eq_sInf, Ideal.mem_sInf]
    intro q hq
    haveI : q.IsPrime := hq
    by_cases hk : f k ∈ q
    · exact q.mul_mem_right _ (q.mul_mem_right _ hk)
    by_cases hl : f l ∈ q
    · exact q.mul_mem_right _ (q.mul_mem_left _ hl)
    apply q.mul_mem_left
    have hker : RingHom.ker (algebraMap R q.ResidueField) = q := Ideal.ker_algebraMap_residueField q
    have hik : algebraMap R q.ResidueField (f k) ≠ 0 := fun h => hk (hker ▸ RingHom.mem_ker.mpr h)
    have hil : algebraMap R q.ResidueField (f l) ≠ 0 := fun h => hl (hker ▸ RingHom.mem_ker.mpr h)
    obtain ⟨v, hv, hv'⟩ := key _ (algebraMap R q.ResidueField) k hik
    obtain ⟨w, hw, hw'⟩ := key _ (algebraMap R q.ResidueField) l hil
    have hvw := huniq _ _ v w hv hw
    subst hvw
    rw [← hker, RingHom.mem_ker, map_sub, map_mul, map_mul, map_pow, map_pow, ← hv', ← hw']
    ring

  let g : {p : Ideal R // p.IsPrime} → R := fun k => f k ^ (n k + 1)
  let α : {p : Ideal R // p.IsPrime} → R := fun k => f k * a k
  have hspan : Ideal.span (Set.range g) = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    let k : {p : Ideal R // p.IsPrime} := ⟨m, hm.isPrime⟩
    exact hf k (hm.isPrime.mem_of_pow_mem _ (hle (Ideal.subset_span ⟨k, rfl⟩)))
  have h1 : (1 : R) ∈ Submodule.span R (Set.range g) := by
    rw [← Ideal.span, hspan]; exact Submodule.mem_top
  obtain ⟨b, hb⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp h1
  let π := Ideal.Quotient.mk (nilradical R)
  have hrel : ∀ k l, π (g l) * π (α k) = π (g k) * π (α l) := by
    intro k l
    rw [← map_mul, ← map_mul, Ideal.Quotient.eq, mem_nilradical]
    have e : g l * α k - g k * α l = f k * f l * (a k * f l ^ n l - a l * f k ^ n k) := by
      simp only [g, α]; ring
    rw [e]; exact hnil k l
  obtain ⟨c0, hc0⟩ := Ideal.Quotient.mk_surjective (I := nilradical R)
    (b.sum fun k r => π r * π (α k))
  have hb' : (b.sum fun k r => π r * π (g k)) = 1 := by
    have := congrArg π hb

    simpa [Finsupp.sum, map_sum, smul_eq_mul] using this
  have hglue : ∀ l, IsNilpotent (g l * c0 - α l) := by
    intro l
    rw [← mem_nilradical, ← Ideal.Quotient.eq]
    calc π (g l * c0) = b.sum (fun k r => π r * π (g k) * π (α l)) := by
          rw [map_mul]
          change π (g l) * Ideal.Quotient.mk (nilradical R) c0 = _
          rw [hc0, Finsupp.mul_sum]
          refine Finsupp.sum_congr fun k _ => ?_
          linear_combination π (b k) * hrel k l
      _ = π (α l) := by rw [← Finsupp.sum_mul, hb', _root_.one_mul]
  refine ⟨c0, fun K _ i => ?_⟩
  let k : {p : Ideal R // p.IsPrime} := ⟨RingHom.ker i, RingHom.ker_isPrime i⟩
  have hik : i (f k) ≠ 0 := fun h => hf k (RingHom.mem_ker.mpr h)
  obtain ⟨v, hv, hv'⟩ := key K i k hik
  have h0 : i (g k * c0 - α k) = 0 := ((hglue k).map i).eq_zero
  have hcv : i c0 = v := by
    have hp : i (f k) ^ (n k + 1) ≠ 0 := pow_ne_zero _ hik
    apply mul_left_cancel₀ hp
    simp only [g, α, map_sub, map_mul, map_pow, sub_eq_zero] at h0
    rw [h0, ← hv']; ring
  rw [hcv]; exact hv

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Poinc

namespace GlobalTheory.SpreadIdeal

theorem exists_open_nhds_mem_stalkId (P : Scheme.{0}) (I : P.IdealSheafData) (s : Γ(P, ⊤)) (v : P)
    (hv : (P.presheaf.germ ⊤ v trivial).hom s ∈ FinalTheorems.stalkId I v) :
    ∃ O : P.Opens, v ∈ O ∧ ∀ y ∈ O, (P.presheaf.germ ⊤ y trivial).hom s ∈ FinalTheorems.stalkId I y := by
  obtain ⟨U, hU, hvU, -⟩ := exists_isAffineOpen_mem_and_subset (x := v) (U := ⊤) trivial
  letI : Algebra Γ(P, U) (P.presheaf.stalk v) := P.presheaf.algebra_section_stalk ⟨v, hvU⟩
  haveI hlocv := hU.isLocalization_stalk ⟨v, hvU⟩
  set t : Γ(P, U) := P.presheaf.map (homOfLE le_top).op s with ht
  have hgerm : ∀ (y : P) (hy : y ∈ U), (P.presheaf.germ ⊤ y trivial).hom s =
      (P.presheaf.germ U y hy).hom t := fun y hy => by
    rw [ht, ← CommRingCat.comp_apply, P.presheaf.germ_res]
  rw [hgerm v hvU, ds_stalkId_eq_map I ⟨U, hU⟩ v hvU] at hv
  change algebraMap Γ(P, U) (P.presheaf.stalk v) t ∈
    Ideal.map (algebraMap Γ(P, U) (P.presheaf.stalk v)) (I.ideal ⟨U, hU⟩) at hv
  obtain ⟨⟨a, w⟩, e⟩ := (IsLocalization.mem_map_algebraMap_iff
    (hU.primeIdealOf ⟨v, hvU⟩).asIdeal.primeCompl _).mp hv
  rw [← map_mul] at e
  obtain ⟨c, hc⟩ := IsLocalization.exists_of_eq (M := (hU.primeIdealOf ⟨v, hvU⟩).asIdeal.primeCompl) e
  set σ : Γ(P, U) := (c : Γ(P, U)) * w with hσ
  have hσt : σ * t ∈ I.ideal ⟨U, hU⟩ := by
    rw [hσ, show (c : Γ(P, U)) * w * t = c * (t * w) by ring, hc]
    exact Ideal.mul_mem_left _ _ a.2
  have hσunit : IsUnit (algebraMap Γ(P, U) (P.presheaf.stalk v) σ) :=
    IsLocalization.map_units (M := (hU.primeIdealOf ⟨v, hvU⟩).asIdeal.primeCompl) _
      (c * w : (hU.primeIdealOf ⟨v, hvU⟩).asIdeal.primeCompl)
  refine ⟨P.basicOpen σ, ?_, fun y hy => ?_⟩
  · exact (P.mem_basicOpen σ v hvU).mpr hσunit
  · have hyU : y ∈ U := P.basicOpen_le σ hy
    have hyu : IsUnit ((P.presheaf.germ U y hyU).hom σ) := (P.mem_basicOpen σ y hyU).mp hy
    rw [hgerm y hyU, ← Ideal.unit_mul_mem_iff_mem _ hyu, ← map_mul,
      ds_stalkId_eq_map I ⟨U, hU⟩ y hyU]
    exact Ideal.mem_map_of_mem _ hσt

end GlobalTheory.SpreadIdeal

namespace GlobalTheory.SpreadIdeal

theorem mem_stalkId_of_closedFibre : ∀ (P : Scheme.{0}) (R : Type) [CommRing R] [IsLocalRing R] (p : P ⟶ Sp R) [UniversallyClosed p] (I : P.IdealSheafData) (s : Γ(P, ⊤)), (∀ v : P, p v = closedPoint R → (P.presheaf.germ ⊤ v trivial).hom s ∈ FinalTheorems.stalkId I v) → ∀ v : P, (P.presheaf.germ ⊤ v trivial).hom s ∈ FinalTheorems.stalkId I v := by
  intro P R _ _ p _ I s hs v
  by_contra hv
  set Z : Set P := {y | (P.presheaf.germ ⊤ y trivial).hom s ∉ FinalTheorems.stalkId I y} with hZ
  have hZc : IsClosed Z := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro y hy
    have hy' : (P.presheaf.germ ⊤ y trivial).hom s ∈ FinalTheorems.stalkId I y := by
      simpa [hZ] using hy
    obtain ⟨O, hyO, hO⟩ := exists_open_nhds_mem_stalkId P I s y hy'
    exact ⟨O, fun z hz => by simpa [hZ] using hO z hz, O.2, hyO⟩
  have himg : IsClosed (p.base '' Z) := p.isClosedMap _ hZc
  have hmem : closedPoint R ∈ p.base '' Z :=
    (IsLocalRing.specializes_closedPoint (p.base v)).mem_closed himg ⟨v, hv, rfl⟩
  obtain ⟨w, hwZ, hw⟩ := hmem
  exact hwZ (hs w hw)

end GlobalTheory.SpreadIdeal
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc

def SameAt {R₁ R₂ B M Γ : Type} [CommRing R₁] [CommRing R₂] [CommRing B] (P₁ : PolAV (Sp R₁)) (P₂ : PolAV (Sp R₂))
    (f₁ : R₁ →+* B) (f₂ : R₂ →+* B) (e₁ : M → (P₁.A ⟶ P₁.A)) (e₂ : M → (P₂.A ⟶ P₂.A))
    (t₁ : Γ → (baseOver (Sp R₁) ⟶ P₁.A)) (t₂ : Γ → (baseOver (Sp R₂) ⟶ P₂.A)) : Prop :=
  ∃ (P : PolAV (Sp B)) (a₁ : P.A.left ⟶ P₁.A.left) (a₂ : P.A.left ⟶ P₂.A.left),
    IsGrpPullback P.A P₁.A (spMap f₁) a₁ ∧ IsGrpPullback P.A P₂.A (spMap f₂) a₂ ∧
    LBIso P.L (P₁.L.pull a₁) ∧ LBIso P.L (P₂.L.pull a₂) ∧
    (∀ E, ∃ e : P.A ⟶ P.A, e.left ≫ a₁ = a₁ ≫ (e₁ E).left ∧ e.left ≫ a₂ = a₂ ≫ (e₂ E).left) ∧
    ∀ x, ∃ w : Sp B ⟶ P.A.left, w ≫ a₁ = spMap f₁ ≫ (t₁ x).left ∧ w ≫ a₂ = spMap f₂ ≫ (t₂ x).left

end GlobalTheory.Poinc
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Special

theorem spc {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem lbIso_pull' {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {a : Y ⟶ X} (h : LBIso M (L.pull a)) (j : Z ⟶ Y)
    {a' : Z ⟶ X} (e : a' = j ≫ a) : LBIso (M.pull j) (L.pull a') :=
  LBIso.chartPull (Geo.Tor.chartPullPull M j j rfl) (Geo.Tor.chartPullSame L _ (fun _ => a) _ j fun _ => e) h

theorem main : ∀ (R₁ R₂ O K F₁ F₂ M Γ : Type) [CommRing R₁] [CommRing R₂] [CommRing O] [Field K] [Field F₁] [Field F₂] [Algebra F₁ K] [Algebra F₂ K] (P₁ : PolAV (Sp R₁)) (P₂ : PolAV (Sp R₂)) (f₁ : R₁ →+* O) (f₂ : R₂ →+* O) (e₁ : M → (P₁.A ⟶ P₁.A)) (e₂ : M → (P₂.A ⟶ P₂.A)) (t₁ : Γ → (baseOver (Sp R₁) ⟶ P₁.A)) (t₂ : Γ → (baseOver (Sp R₂) ⟶ P₂.A)), (∃ (P : PolAV (Sp O)) (b₁ : P.A.left ⟶ P₁.A.left) (b₂ : P.A.left ⟶ P₂.A.left), IsGrpPullback P.A P₁.A (spMap f₁) b₁ ∧ IsGrpPullback P.A P₂.A (spMap f₂) b₂ ∧ LBIso P.L (P₁.L.pull b₁) ∧ LBIso P.L (P₂.L.pull b₂) ∧ (∀ E, ∃ e : P.A ⟶ P.A, e.left ≫ b₁ = b₁ ≫ (e₁ E).left ∧ e.left ≫ b₂ = b₂ ≫ (e₂ E).left) ∧ ∀ x, ∃ w : Sp O ⟶ P.A.left, w ≫ P.A.hom = 𝟙 _ ∧ w ≫ b₁ = spMap f₁ ≫ (t₁ x).left ∧ w ≫ b₂ = spMap f₂ ≫ (t₂ x).left) → ∀ (v : O →+* K) (k₁ : R₁ →+* F₁) (k₂ : R₂ →+* F₂), (algebraMap F₁ K).comp k₁ = v.comp f₁ → (algebraMap F₂ K).comp k₂ = v.comp f₂ → ∀ (A₁ : PolAV (Sp F₁)) (A₂ : PolAV (Sp F₂)) (φ₁ : A₁.A.left ⟶ P₁.A.left) (φ₂ : A₂.A.left ⟶ P₂.A.left), IsGrpPullback A₁.A P₁.A (spMap k₁) φ₁ → IsGrpPullback A₂.A P₂.A (spMap k₂) φ₂ → LBIso A₁.L (P₁.L.pull φ₁) → LBIso A₂.L (P₂.L.pull φ₂) → ∃ (P₀ : PolAV (Sp K)) (a₁ : P₀.A.left ⟶ A₁.A.left) (a₂ : P₀.A.left ⟶ A₂.A.left), IsGrpPullback P₀.A A₁.A (spMap (algebraMap F₁ K)) a₁ ∧ IsGrpPullback P₀.A A₂.A (spMap (algebraMap F₂ K)) a₂ ∧ LBIso P₀.L (A₁.L.pull a₁) ∧ LBIso P₀.L (A₂.L.pull a₂) ∧ (∀ x, ∃ w : Sp K ⟶ P₀.A.left, w ≫ P₀.A.hom = 𝟙 _ ∧ w ≫ a₁ ≫ φ₁ = spMap (v.comp f₁) ≫ (t₁ x).left ∧ w ≫ a₂ ≫ φ₂ = spMap (v.comp f₂) ≫ (t₂ x).left) ∧ ∀ (E : M) (w w₂ : Sp K ⟶ P₀.A.left), w ≫ P₀.A.hom = 𝟙 _ → w₂ ≫ P₀.A.hom = 𝟙 _ → w₂ ≫ a₁ ≫ φ₁ = w ≫ a₁ ≫ φ₁ ≫ (e₁ E).left → w₂ ≫ a₂ ≫ φ₂ = w ≫ a₂ ≫ φ₂ ≫ (e₂ E).left := by
  intro R₁ R₂ O K F₁ F₂ M Γ _ _ _ _ _ _ _ _ P₁ P₂ f₁ f₂ e₁ e₂ t₁ t₂ hS v k₁ k₂ hk₁ hk₂ A₁ A₂ φ₁ φ₂ hA₁ hA₂ hL₁ hL₂
  obtain ⟨P, b₁, b₂, hb₁, hb₂, hPL₁, hPL₂, he, ht⟩ := hS
  let P₀ : PolAV (Sp K) := GlobalTheory.StrictPull.polPull P (spMap v)
  let β : P₀.A.left ⟶ P.A.left := pullback.fst P.A.hom (spMap v)
  have hβ : IsGrpPullback P₀.A P.A (spMap v) β := isGrpPullback_pullback P.A (spMap v)
  have eq₁ : spMap (algebraMap F₁ K) ≫ spMap k₁ = spMap v ≫ spMap f₁ := by rw [spc, spc, hk₁]
  have eq₂ : spMap (algebraMap F₂ K) ≫ spMap k₂ = spMap v ≫ spMap f₂ := by rw [spc, spc, hk₂]
  have c₁ := hβ.comp hb₁
  have c₂ := hβ.comp hb₂
  have w₁ : (β ≫ b₁) ≫ P₁.A.hom = (P₀.A.hom ≫ spMap (algebraMap F₁ K)) ≫ spMap k₁ := by
    rw [c₁.1.w, Category.assoc, eq₁]
  have w₂ : (β ≫ b₂) ≫ P₂.A.hom = (P₀.A.hom ≫ spMap (algebraMap F₂ K)) ≫ spMap k₂ := by
    rw [c₂.1.w, Category.assoc, eq₂]
  let a₁ : P₀.A.left ⟶ A₁.A.left := hA₁.1.lift _ _ w₁
  let a₂ : P₀.A.left ⟶ A₂.A.left := hA₂.1.lift _ _ w₂
  have ha₁ : a₁ ≫ φ₁ = β ≫ b₁ := hA₁.1.lift_fst _ _ w₁
  have ha₂ : a₂ ≫ φ₂ = β ≫ b₂ := hA₂.1.lift_fst _ _ w₂
  have ga₁ : IsGrpPullback P₀.A A₁.A (spMap (algebraMap F₁ K)) a₁ :=
    IsGrpPullback.cancel hA₁ (c₁.congr eq₁.symm ha₁.symm) (hA₁.1.lift_snd _ _ w₁)
  have ga₂ : IsGrpPullback P₀.A A₂.A (spMap (algebraMap F₂ K)) a₂ :=
    IsGrpPullback.cancel hA₂ (c₂.congr eq₂.symm ha₂.symm) (hA₂.1.lift_snd _ _ w₂)
  have hP₀L : P₀.L = P.L.pull β := rfl
  refine ⟨P₀, a₁, a₂, ga₁, ga₂, ?_, ?_, fun x => ?_, fun E w w₂' hw hw₂ h => ?_⟩
  · rw [hP₀L]
    exact LBIso.trans (pull_isLB P.isLB _) (pull_isLB P₁.isLB _) (pull_isLB A₁.isLB _)
      (lbIso_pull' hPL₁ β rfl) (lbIso_pull' hL₁ a₁ ha₁.symm).symm
  · rw [hP₀L]
    exact LBIso.trans (pull_isLB P.isLB _) (pull_isLB P₂.isLB _) (pull_isLB A₂.isLB _)
      (lbIso_pull' hPL₂ β rfl) (lbIso_pull' hL₂ a₂ ha₂.symm).symm
  · obtain ⟨wO, hs, h₁, h₂⟩ := ht x
    have sq : (spMap v ≫ wO) ≫ P.A.hom = 𝟙 _ ≫ spMap v := by
      rw [Category.assoc, hs, Category.comp_id, Category.id_comp]
    have hl : pullback.lift (spMap v ≫ wO) (𝟙 _) sq ≫ β = spMap v ≫ wO := pullback.lift_fst _ _ _
    refine ⟨pullback.lift (spMap v ≫ wO) (𝟙 _) sq, pullback.lift_snd _ _ _, ?_, ?_⟩
    · calc pullback.lift (spMap v ≫ wO) (𝟙 _) sq ≫ a₁ ≫ φ₁ = pullback.lift (spMap v ≫ wO) (𝟙 _) sq ≫ β ≫ b₁ := congrArg (fun z => pullback.lift (spMap v ≫ wO) (𝟙 _) sq ≫ z) ha₁
        _ = (pullback.lift (spMap v ≫ wO) (𝟙 _) sq ≫ β) ≫ b₁ := (Category.assoc _ _ _).symm
        _ = _ := by rw [hl, Category.assoc, h₁, ← Category.assoc, spc]
    · calc pullback.lift (spMap v ≫ wO) (𝟙 _) sq ≫ a₂ ≫ φ₂ = pullback.lift (spMap v ≫ wO) (𝟙 _) sq ≫ β ≫ b₂ := congrArg (fun z => pullback.lift (spMap v ≫ wO) (𝟙 _) sq ≫ z) ha₂
        _ = (pullback.lift (spMap v ≫ wO) (𝟙 _) sq ≫ β) ≫ b₂ := (Category.assoc _ _ _).symm
        _ = _ := by rw [hl, Category.assoc, h₂, ← Category.assoc, spc]
  · obtain ⟨e, he₁, he₂⟩ := he E
    have sqe : (β ≫ e.left) ≫ P.A.hom = P₀.A.hom ≫ spMap v := by
      rw [Category.assoc, Over.w e]; exact pullback.condition
    let e₀ : P₀.A.left ⟶ P₀.A.left := pullback.lift (β ≫ e.left) P₀.A.hom sqe
    have he₀ : e₀ ≫ β = β ≫ e.left := pullback.lift_fst _ _ _
    have he₀' : e₀ ≫ P₀.A.hom = P₀.A.hom := pullback.lift_snd _ _ _
    have key : w₂' = w ≫ e₀ := by
      apply c₁.1.hom_ext
      · calc w₂' ≫ β ≫ b₁ = w₂' ≫ a₁ ≫ φ₁ := by rw [ha₁]
          _ = w ≫ a₁ ≫ φ₁ ≫ (e₁ E).left := h
          _ = w ≫ (a₁ ≫ φ₁) ≫ (e₁ E).left := by simp only [Category.assoc]
          _ = w ≫ β ≫ (b₁ ≫ (e₁ E).left) := by rw [ha₁, Category.assoc]
          _ = w ≫ (β ≫ e.left) ≫ b₁ := by rw [← he₁, Category.assoc]
          _ = (w ≫ e₀) ≫ β ≫ b₁ := by rw [← he₀]; simp only [Category.assoc]
      · rw [hw₂, Category.assoc, he₀', hw]
    calc w₂' ≫ a₂ ≫ φ₂ = (w ≫ e₀) ≫ β ≫ b₂ := by rw [key, ha₂]
      _ = w ≫ (e₀ ≫ β) ≫ b₂ := by simp only [Category.assoc]
      _ = w ≫ β ≫ (e.left ≫ b₂) := by rw [he₀, Category.assoc]
      _ = w ≫ (β ≫ b₂) ≫ (e₂ E).left := by rw [he₂]; simp only [Category.assoc]
      _ = w ≫ a₂ ≫ φ₂ ≫ (e₂ E).left := by rw [← ha₂]; simp only [Category.assoc]

end GlobalTheory.Poinc.Special
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtTrans

theorem ptTrans : ∀ {V V' : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] (K : Type) [Field K] [Algebra (FractionRing V) K] [Algebra (FractionRing V') K] (A : PolAV (Sp (FractionRing V))) (A' : PolAV (Sp (FractionRing V'))) (P₀ : PolAV (Sp K)) (a : P₀.A.left ⟶ A.A.left) (a' : P₀.A.left ⟶ A'.A.left), IsGrpPullback P₀.A A.A (spMap (algebraMap (FractionRing V) K)) a → IsGrpPullback P₀.A A'.A (spMap (algebraMap (FractionRing V') K)) a' → ∀ (m : ℕ) (x : TFK (R := V) K ⟶ A.A), x ^ m = 1 → ∃ (w : Sp K ⟶ P₀.A.left) (x' : TFK (R := V') K ⟶ A'.A), w ≫ P₀.A.hom = 𝟙 _ ∧ w ≫ a = x.left ∧ w ≫ a' = x'.left ∧ x' ^ m = 1 := by
  intro V V' _ _ _ _ K _ _ _ A A' P₀ a a' h h' m x hx
  let T : Over (Sp K) := Over.mk (𝟙 (Sp K))
  let e : TFK (R := V) K ⟶ Over.mk (T.hom ≫ spMap (algebraMap (FractionRing V) K)) :=
    Over.homMk (𝟙 _) (by simp [T])
  let e' : TFK (R := V') K ⟶ Over.mk (T.hom ≫ spMap (algebraMap (FractionRing V') K)) :=
    Over.homMk (𝟙 _) (by simp [T])
  let Φ : (T ⟶ P₀.A) →* (TFK (R := V) K ⟶ A.A) := (preHom e).comp (pushHom h T)
  let Φ' : (T ⟶ P₀.A) →* (TFK (R := V') K ⟶ A'.A) := (preHom e').comp (pushHom h' T)
  have hΦ : ∀ u : T ⟶ P₀.A, (Φ u).left = u.left ≫ a := fun u => by
    simp [Φ, e, preHom, pushHom, pushPt]
  have hΦ' : ∀ u : T ⟶ P₀.A, (Φ' u).left = u.left ≫ a' := fun u => by
    simp [Φ', e', preHom, pushHom, pushPt]
  have inj : Function.Injective Φ := fun u v huv => by
    apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · rw [← hΦ, ← hΦ, huv]
    · rw [Over.w u, Over.w v]
  have hsq : x.left ≫ A.A.hom = 𝟙 (Sp K) ≫ spMap (algebraMap (FractionRing V) K) := by
    rw [Over.w x, Category.id_comp]; rfl
  let w : T ⟶ P₀.A := Over.homMk (h.1.lift x.left (𝟙 _) hsq) (by simp [T])
  have hw : Φ w = x := by
    apply Over.OverMorphism.ext
    rw [hΦ]
    simp [w]
  have hwm : w ^ m = 1 := by
    apply inj
    rw [map_pow, hw, hx, map_one]
  refine ⟨w.left, Φ' w, ?_, ?_, ?_, ?_⟩
  · simpa [T] using Over.w w
  · rw [← hΦ, hw]
  · rw [hΦ']
  · rw [← map_pow, hwm, map_one]

end GlobalTheory.PtTrans
end

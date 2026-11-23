module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle583
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle007
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1384
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle137
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothGrpSchemeDescendsToFgSubring
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle030
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.AdelicGL2ExtOfLocalComponents
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle031
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelTor

open TopologicalSpace

namespace GlobalTheory.CompPart

theorem isIrreducible_generizations {Z : Scheme.{0}} (hd : ∀ x : Z, IsDomain (Z.presheaf.stalk x)) (x : Z) :
    IsIrreducible {y : Z | y ⤳ x} := by
  haveI := hd x
  rw [← Scheme.range_fromSpecStalk, ← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ (Spec (Z.presheaf.stalk x))).image _
    (Z.fromSpecStalk x).continuous.continuousOn

theorem eq_closure_generizations {Z : Scheme.{0}} (hd : ∀ x : Z, IsDomain (Z.presheaf.stalk x))
    {C : Set Z} (hC : C ∈ irreducibleComponents Z) {x : Z} (hx : x ∈ C) :
    C = closure {y : Z | y ⤳ x} := by
  have hcl : IsClosed C := isClosed_of_mem_irreducibleComponents C hC
  obtain ⟨η, hη⟩ := QuasiSober.sober hC.1 hcl
  have hηx : η ⤳ x := by
    rw [specializes_iff_mem_closure, hη.def]; exact hx
  have hsub : C ⊆ closure {y : Z | y ⤳ x} := by
    rw [← hη.def]
    exact closure_mono (Set.singleton_subset_iff.2 hηx)
  exact hsub.antisymm (hC.2 (isIrreducible_generizations hd x).closure hsub)

theorem existsUnique_mem {Z : Scheme.{0}} (hd : ∀ x : Z, IsDomain (Z.presheaf.stalk x)) (x : Z) :
    ∃! C : irreducibleComponents Z, x ∈ (C : Set Z) :=
  ⟨⟨_, irreducibleComponent_mem_irreducibleComponents x⟩, mem_irreducibleComponent, fun C hC =>
    Subtype.ext ((eq_closure_generizations hd C.2 hC).trans
      (eq_closure_generizations hd (irreducibleComponent_mem_irreducibleComponents x)
        mem_irreducibleComponent).symm)⟩

theorem isOpen_of_mem {Z : Scheme.{0}} [NoetherianSpace Z] (hd : ∀ x : Z, IsDomain (Z.presheaf.stalk x))
    {C : Set Z} (hC : C ∈ irreducibleComponents Z) : IsOpen C := by
  have hfin : (irreducibleComponents Z).Finite := NoetherianSpace.finite_irreducibleComponents
  have hcompl : Cᶜ = ⋃ D ∈ {D ∈ irreducibleComponents Z | D ≠ C}, D := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · intro hy
      exact ⟨irreducibleComponent y, ⟨irreducibleComponent_mem_irreducibleComponents y,
        fun h => hy (h ▸ mem_irreducibleComponent)⟩, mem_irreducibleComponent⟩
    · rintro ⟨D, ⟨hD, hne⟩, hyD⟩ hyC
      exact hne (congrArg Subtype.val ((existsUnique_mem hd y).unique (y₁ := ⟨D, hD⟩) (y₂ := ⟨C, hC⟩) hyD hyC))
  rw [← isClosed_compl_iff, hcompl]
  exact (hfin.subset (by exact fun D hD => hD.1)).isClosed_biUnion fun D hD =>
    isClosed_of_mem_irreducibleComponents D hD.1

end GlobalTheory.CompPart

theorem GlobalTheory.irreducibleComponents_clopen_partition : ∀ (n : ℕ) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)),
    IsProjOver z → GlobalTheory.IsNormalScheme Z → ∃ (ι : Type) (_ : Fintype ι) (W : ι → Set Z),
      (∀ c, IsClopen (W c)) ∧ (∀ c, IsIrreducible (W c)) ∧ ∀ x, ∃! c, x ∈ W c := by
  intro n Z z hz hN
  haveI : IsNoetherianRing (cycAway n) :=
    is_noetherian_subring_closure _ (Set.toFinite _)
  haveI : AlgebraicGeometry.IsNoetherian Z := GlobalTheory.isNoetherian_of_isProjOver hz
  have hd : ∀ x : Z, IsDomain (Z.presheaf.stalk x) := fun x => hN.isDomain_stalk x
  have hfin : (irreducibleComponents Z).Finite := NoetherianSpace.finite_irreducibleComponents
  exact ⟨irreducibleComponents Z, hfin.fintype, fun C => (C : Set Z),
    fun C => ⟨isClosed_of_mem_irreducibleComponents _ C.2, GlobalTheory.CompPart.isOpen_of_mem hd C.2⟩,
    fun C => C.2.1, GlobalTheory.CompPart.existsUnique_mem hd⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.LevSurjOpen

theorem lev_nsmul {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : Type} [AddCommGroup L]
    (lev : L → (𝟙_ (Over S) ⟶ G)) (hadd : ∀ a b, lev (a + b) = lev a * lev b) (a : L) :
    ∀ n : ℕ, lev (n • a) = lev a ^ n
  | 0 => by
    have h := hadd 0 0
    rw [add_zero] at h
    rw [zero_smul, pow_zero]
    exact mul_eq_left.mp h.symm
  | n + 1 => by rw [succ_nsmul, hadd, lev_nsmul lev hadd a n, pow_succ]

theorem range_subset_iff_pt {k : Type} [Field k] {X : Scheme.{0}} (y : Sp k ⟶ X) (O : Set X) :
    Set.range y.base ⊆ O ↔ y.base (⊥ : PrimeSpectrum k) ∈ O := by
  haveI : Subsingleton (Sp k) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  rw [Set.range_subset_iff]
  refine ⟨fun H => H _, fun H p => ?_⟩
  have : p = (⊥ : PrimeSpectrum k) := Subsingleton.elim (α := Sp k) p (⊥ : PrimeSpectrum k)
  rw [this]
  exact H

theorem torsion_hom_ext {S : Scheme.{0}} {G : Over S} [GrpObj G] {M : ℕ} {X : Over S} (u v : X ⟶ torsion G M)
    (h : u ≫ torsion.ι G M = v ≫ torsion.ι G M) : u = v :=
  pullback.hom_ext h (toUnit_unique _ _)

theorem exists_open_levSurj : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (M : ℕ) (t : S ⟶ Sp (cycAway M)) (G : Over S) [GrpObj G] [IsCommMonObj G] (h : ℕ) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ G)), IsAbelianScheme G → 3 ≤ M → (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ M = 1) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x₀ : Sp k ⟶ S), (∀ g : Over.mk x₀ ⟶ G, g ^ M = 1 → ∃ a, toUnit _ ≫ lev a = g) → ∃ W : S.Opens, Set.range x₀.base ⊆ W ∧ ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (x : Sp k' ⟶ S), Set.range x.base ⊆ W → ∀ g : Over.mk x ⟶ G, g ^ M = 1 → ∃ a, toUnit _ ≫ lev a = g := by
  intro S _ M t G _ _ h lev hab hM hadd htors k _ _ x₀ hx₀
  haveI := hab
  have hM0 : M ≠ 0 := by omega
  have hu : IsUnit (M : Γ(S, ⊤)) := by
    simpa using (GlobalTheory.SiegelTor.isUnit_natCast hM0).map
      ((Scheme.ΓSpecIso (CommRingCat.of (cycAway M))).inv ≫ t.appTop).hom
  obtain ⟨-, hfin, het⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion G hu
  haveI := hfin
  haveI := het
  let ℓ : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ torsion G M) := fun a =>
    GlobalTheory.TorsionFamily.torsionLift G (lev a) M (htors a)
  have hℓ : ∀ a, ℓ a ≫ torsion.ι G M = lev a := fun a => GlobalTheory.TorsionFamily.torsionLift_ι _ _ _ _

  have hcl : ∀ a, GlobalTheory.LevCover.ClopenCond (torsion G M)
      fun _ y => y ≫ 𝟙 (torsion G M) = y ≫ (toUnit (torsion G M) ≫ ℓ a) :=
    fun a => GlobalTheory.LevCover.clopenCond_eq _ _
  choose U hUc hU using hcl
  obtain ⟨κ, _, q, hq⟩ := GlobalTheory.LevCover.exists_finite_mod (Fin h ⊕ Fin h → ℤ) (n := M) (by omega)
  let rep : Set.range q → (Fin h ⊕ Fin h → ℤ) := fun c => c.2.choose
  have hrep : ∀ a, lev (rep ⟨q a, a, rfl⟩) = lev a := by
    intro a
    obtain ⟨c, hc⟩ := hq _ _ ((⟨q a, a, rfl⟩ : Set.range q).2.choose_spec)
    have e := congrArg lev hc
    rw [hadd, lev_nsmul lev hadd, htors, _root_.mul_one] at e
    exact e.symm

  let Zs : Set (torsion G M).left := ⋃ c : Set.range q, (U (rep c) : Set (torsion G M).left)
  have hZo : IsOpen Zs := isOpen_iUnion fun c => (U _).isOpen
  have hZc : IsClosed Zs := isClosed_iUnion_of_finite fun c => hUc _
  let C : (torsion G M).left.Opens := ⟨Zsᶜ, hZc.isOpen_compl⟩
  obtain ⟨V, i, hVf, hVe, -, hV⟩ := GlobalTheory.LevCover.exists_sub C hZo.isClosed_compl
  haveI := hVf
  haveI := hVe
  haveI : IsFinite (𝟙_ (Over S)).hom := by show IsFinite (𝟙 S); infer_instance
  haveI : Etale (𝟙_ (Over S)).hom := by show Etale (𝟙 S); infer_instance

  obtain ⟨U₀, hU₀c, hU₀⟩ := GlobalTheory.LevCover.exists_image (toUnit V)
  let U₁ : Set S := (U₀ : Set (𝟙_ (Over S)).left)
  have hU₁c : IsClosed U₁ := hU₀c
  have key : ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (x : Sp k' ⟶ S),
      Set.range x.base ⊆ U₁ ↔ Nonempty (Over.mk x ⟶ V) := by
    intro k' _ _ x
    have H := hU₀ k' x (toUnit _)
    have hz : (toUnit (Over.mk x) : Over.mk x ⟶ 𝟙_ (Over S)).left = x := by
      simpa using Over.w (toUnit (Over.mk x))
    rw [hz] at H
    exact H.trans ⟨fun ⟨w, _⟩ => ⟨w⟩, fun ⟨w⟩ => ⟨w, toUnit_unique _ _⟩⟩
  refine ⟨⟨U₁ᶜ, hU₁c.isOpen_compl⟩, ?_, ?_⟩
  · intro _ ⟨p, hp⟩ hpU
    subst hp
    have hr : Set.range x₀.base ⊆ U₁ := by
      rw [range_subset_iff_pt]
      have : p = (⊥ : PrimeSpectrum k) :=
        @Subsingleton.elim (Sp k) (inferInstanceAs (Subsingleton (PrimeSpectrum k))) p (⊥ : PrimeSpectrum k)
      rw [← this]
      exact hpU
    obtain ⟨w⟩ := (key k x₀).1 hr
    let y := w ≫ i
    have hy : Set.range y.left.base ⊆ (C : Set (torsion G M).left) := (hV _ y).2 ⟨w, rfl⟩
    have hg : (y ≫ torsion.ι G M) ^ M = 1 := by
      rw [← MonObj.comp_pow, GlobalTheory.TorsionFamily.torsion_ι_pow, MonObj.comp_one]
    obtain ⟨a, ha⟩ := hx₀ _ hg
    have e1 : (toUnit (Over.mk x₀) ≫ ℓ (rep ⟨q a, a, rfl⟩)) ≫ torsion.ι G M = toUnit _ ≫ lev a := by
      rw [Category.assoc, hℓ, hrep]
    have e2 : y ≫ torsion.ι G M = toUnit _ ≫ lev a := ha.symm
    have hy' : y = toUnit _ ≫ ℓ (rep ⟨q a, a, rfl⟩) := torsion_hom_ext _ _ (e2.trans e1.symm)
    have hin : Set.range y.left.base ⊆ (U (rep ⟨q a, a, rfl⟩) : Set (torsion G M).left) := by
      refine (hU _ _ y).1 ?_
      show y ≫ 𝟙 _ = y ≫ toUnit _ ≫ ℓ _
      rw [Category.comp_id, ← Category.assoc, toUnit_unique (y ≫ toUnit _) (toUnit _), ← hy']
    have h1 := (range_subset_iff_pt _ _).1 hy
    have h2 := (range_subset_iff_pt _ _).1 hin
    exact h1 (Set.mem_iUnion.2 ⟨⟨q a, a, rfl⟩, h2⟩)
  · intro k' _ _ x hx g hg
    let y := GlobalTheory.TorsionFamily.torsionLift G g M hg
    have hnC : ¬ Set.range y.left.base ⊆ (C : Set (torsion G M).left) := by
      intro H
      obtain ⟨w, -⟩ := (hV _ y).1 H
      have hr := (key k' x).2 ⟨w⟩
      have h1 := (range_subset_iff_pt _ _).1 hr
      have h2 := (range_subset_iff_pt _ _).1 hx
      exact h2 h1
    rw [range_subset_iff_pt] at hnC
    have hZ : y.left.base (⊥ : PrimeSpectrum k') ∈ Zs := not_not.1 hnC
    obtain ⟨c, hc⟩ := Set.mem_iUnion.1 hZ
    have hin : Set.range y.left.base ⊆ (U (rep c) : Set (torsion G M).left) :=
      (range_subset_iff_pt _ _).2 hc
    have e : y ≫ 𝟙 _ = y ≫ toUnit _ ≫ ℓ (rep c) := (hU _ _ y).2 hin
    rw [Category.comp_id, ← Category.assoc, toUnit_unique (y ≫ toUnit _) (toUnit _)] at e
    refine ⟨rep c, ?_⟩
    rw [← hℓ, ← Category.assoc, ← e]
    exact GlobalTheory.TorsionFamily.torsionLift_ι _ _ _ _

end GlobalTheory.LevSurjOpen
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

namespace GlobalTheory.SiegFg

theorem spMap_subtype_inclusion' {R : Type} [CommRing R] {S₀ R₁ : Subring R} (h : S₀ ≤ R₁) :
    spMap R₁.subtype ≫ spMap (Subring.inclusion h) = spMap S₀.subtype := by
  rw [← Spec.map_comp]
  rfl

theorem smooth_pull {S S' : Scheme.{0}} (f : S' ⟶ S) (B : Over S) (g : ℕ) (hB : SmoothOfRelativeDimension g B.hom) :
    SmoothOfRelativeDimension g ((Over.pullback f).obj B).hom :=
  (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback B.hom f) hB

theorem range_le {n : ℕ} {R : Type} [CommRing R] (β : cycAway n →+* R) (S₀ : Subring R)
    (h₁ : β (zetaAway n) ∈ S₀) (h₂ : ∀ hm : ((n : ℂ))⁻¹ ∈ cycAway n, β ⟨((n : ℂ))⁻¹, hm⟩ ∈ S₀) (x : cycAway n) :
    β x ∈ S₀ := by
  obtain ⟨x, hx⟩ := x
  induction hx using Subring.closure_induction with
  | mem y hy =>
    rcases hy with rfl | hy
    · exact h₁
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact h₂ _
  | zero => exact (congrArg (· ∈ S₀) (map_zero β)).mpr S₀.zero_mem
  | one => exact (congrArg (· ∈ S₀) (map_one β)).mpr S₀.one_mem
  | add y z hy hz ihy ihz =>
    have e : β ⟨y + z, Subring.add_mem _ hy hz⟩ = β ⟨y, hy⟩ + β ⟨z, hz⟩ := by rw [← map_add (f := _)]; rfl
    rw [e]; exact S₀.add_mem ihy ihz
  | neg y hy ihy =>
    have e : β ⟨-y, Subring.neg_mem _ hy⟩ = -β ⟨y, hy⟩ := by rw [← map_neg]; rfl
    rw [e]; exact S₀.neg_mem ihy
  | mul y z hy hz ihy ihz =>
    have e : β ⟨y * z, Subring.mul_mem _ hy hz⟩ = β ⟨y, hy⟩ * β ⟨z, hz⟩ := by rw [← map_mul]; rfl
    rw [e]; exact S₀.mul_mem ihy ihz

end GlobalTheory.SiegFg

namespace GlobalTheory.SiegFg

theorem siegPre_data_descends_fg : ∀ (g n : ℕ), 3 ≤ n → ∀ (R : Type) [CommRing R] (β : cycAway n →+* R) (c : SiegPre g n (zetaAway n) (spMap β)), ∃ (R₁ : Subring R) (β₁ : cycAway n →+* R₁) (A₁ : Over (Sp R₁)) (_ : GrpObj A₁) (P₁ : LB (A₁ ⊗ A₁).left) (lv₁ : Std g n → (𝟙_ (Over (Sp R₁)) ⟶ A₁)), Algebra.FiniteType ℤ R₁ ∧ R₁.subtype.comp β₁ = β ∧ IsAbelianScheme A₁ ∧ SmoothOfRelativeDimension g A₁.hom ∧ P₁.IsLB ∧ IsPullbackTriple c.A c.P (lvOf c) A₁ P₁ lv₁ (spMap R₁.subtype) := by
  intro g n hn R _ β c
  classical
  have h0 : n ≠ 0 := by omega
  haveI : NeZero n := ⟨h0⟩
  have hdim : SmoothOfRelativeDimension g c.A.hom :=
    relDim (ζ := (cycBase h0).ζ) (by omega) (isUnit_natCast h0) c
  have hm : ((n : ℂ))⁻¹ ∈ cycAway n := Subring.subset_closure (by simp)
  obtain ⟨S₀, B, _, φ, hF, hS₀, hB, hBd, hφ⟩ := GlobalTheory.AbelianLimit.abelianScheme_descends_to_fg_subring R g c.A
    {β (zetaAway n), β ⟨((n : ℂ))⁻¹, hm⟩} c.ab hdim
  have hβ : ∀ x, β x ∈ S₀ := range_le β S₀ (hF (by simp)) (fun _ => hF (by simp))
  have : IsCommMonObj B := hB.comm
  have : IsProper B.hom := hB.proper
  have : Smooth B.hom := hB.smooth
  have : QuasiCompact (B ⊗ B).hom := by
    change QuasiCompact (pullback.fst B.hom B.hom ≫ B.hom); infer_instance
  have : QuasiSeparated (B ⊗ B).hom := by
    change QuasiSeparated (pullback.fst B.hom B.hom ≫ B.hom); infer_instance

  obtain ⟨φ₂, hsq⟩ := GlobalTheory.SiegDesc.exists_isSquare hφ.1.w
  obtain ⟨SP, hSP⟩ := GlobalTheory.LBLimit.lb_descends_to_fg_subring R S₀ (c.A ⊗ c.A).left (B ⊗ B).left (c.A ⊗ c.A).hom
    (B ⊗ B).hom φ₂ c.P (GlobalTheory.SiegDesc.isPullback_of_isSquare hφ.1 hsq) c.isLB

  have hw : ∀ a : Std g n, ((lvOf c a).left ≫ φ) ≫ B.hom = spMap S₀.subtype ≫ 𝟙 _ := fun a => by
    have e : (lvOf c a).left ≫ c.A.hom = 𝟙 _ := Over.w (lvOf c a)
    rw [Category.assoc, hφ.1.w, reassoc_of% e, Category.comp_id]
  choose SL hSL using fun a : Std g n => GlobalTheory.morphism_descends_to_subring R S₀ (Sp R) (Sp S₀) B.left (𝟙 _) (𝟙 _)
    B.hom (spMap S₀.subtype) ((lvOf c a).left ≫ φ) IsPullback.of_id_snd (hw a)

  let T : Finset R := SP ∪ Finset.univ.biUnion SL
  let R₁ : Subring R := (Algebra.adjoin S₀ (T : Set R)).toSubring
  have hFT : Algebra.FiniteType ℤ R₁ :=
    GlobalTheory.SpreadGroup.finiteType_of_fg hS₀ (Subalgebra.fg_adjoin_finset T)
  have h : S₀ ≤ R₁ := fun x hx => Subalgebra.algebraMap_mem (Algebra.adjoin S₀ (T : Set R)) (⟨x, hx⟩ : S₀)
  have hT : (T : Set R) ⊆ R₁ := Algebra.subset_adjoin
  have hSPs : (SP : Set R) ⊆ R₁ := fun x hx => hT (by simp [T, Finset.mem_coe.1 hx])
  have hSLs : ∀ a, (SL a : Set R) ⊆ R₁ := fun a x hx => hT (by
    simp only [T, Finset.coe_union, Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true]
    exact Or.inr (Set.mem_iUnion.2 ⟨a, hx⟩))
  have hj : spMap R₁.subtype ≫ spMap (Subring.inclusion h) = spMap S₀.subtype := spMap_subtype_inclusion' h

  let A₁ : Over (Sp R₁) := (Over.pullback (spMap (Subring.inclusion h))).obj B
  have hA₁ : IsAbelianScheme A₁ :=
    { comm := by infer_instance
      smooth := by show Smooth (pullback.snd _ _); infer_instance
      proper := by show IsProper (pullback.snd _ _); infer_instance
      geomConnected := by
        have := hB.geomConnected
        show GeometricallyConnected (pullback.snd _ _); infer_instance }
  have hA₁d : SmoothOfRelativeDimension g A₁.hom := smooth_pull _ B g hBd
  have hpb := Pdiv.PullbackComparison.isGrpPullback (spMap (Subring.inclusion h)) B
  let ψ : c.A.left ⟶ A₁.left := pullback.lift φ (c.A.hom ≫ spMap R₁.subtype)
    (by rw [hφ.1.w, Category.assoc, hj])
  have hψ₁ : ψ ≫ Pdiv.PullbackComparison.pφ (spMap (Subring.inclusion h)) B = φ := pullback.lift_fst _ _ _
  have hψ₂ : ψ ≫ A₁.hom = c.A.hom ≫ spMap R₁.subtype := pullback.lift_snd _ _ _
  have hgp : IsGrpPullback c.A A₁ (spMap R₁.subtype) ψ :=
    IsGrpPullback.cancel hpb (by rw [hψ₁, hj]; exact hφ) hψ₂

  obtain ⟨ψ₂, hsqψ⟩ := GlobalTheory.SiegDesc.exists_isSquare hψ₂
  obtain ⟨P₁, hP₁, hiso⟩ := hSP R₁ h hSPs (A₁ ⊗ A₁).left (A₁ ⊗ A₁).hom
    (Pdiv.PullbackComparison.pφ₂ (spMap (Subring.inclusion h)) B) ψ₂
    (GlobalTheory.SiegDesc.isPullback_of_isSquare hpb.1 (Pdiv.PullbackComparison.isSquare _ B))
    (GlobalTheory.SiegDesc.isSquare_comp hψ₁ hsqψ (Pdiv.PullbackComparison.isSquare _ B) hsq) (GlobalTheory.SiegDesc.isSquare_w hψ₂ hsqψ)

  choose ψa hψa using fun a : Std g n => hSL a R₁ h (hSLs a) (Sp R₁) (𝟙 _) (spMap (Subring.inclusion h))
    (spMap R₁.subtype) IsPullback.of_id_snd hj (by simp)
  let l : Std g n → (Sp R₁ ⟶ A₁.left) := fun a => pullback.lift (ψa a) (𝟙 _)
    (by rw [(hψa a).2, Category.comp_id, Category.id_comp])
  have hl₁ : ∀ a, l a ≫ pullback.fst _ _ = ψa a := fun a => pullback.lift_fst _ _ _
  have hl₂ : ∀ a, l a ≫ A₁.hom = 𝟙 _ := fun a => pullback.lift_snd _ _ _
  let lv₁ : Std g n → (𝟙_ (Over (Sp R₁)) ⟶ A₁) := fun a => Over.homMk (l a) (hl₂ a)
  refine ⟨R₁, β.codRestrict R₁ (fun x => h (hβ x)), A₁, inferInstance, P₁, lv₁, hFT, by ext; rfl, hA₁, hA₁d, hP₁,
    ψ, ψ₂, hgp, hsqψ.1, hsqψ.2, hiso, fun a => ?_⟩
  have e : (lvOf c a).left ≫ c.A.hom = 𝟙 _ := Over.w (lvOf c a)
  apply pullback.hom_ext
  · change (lvOf c a).left ≫ ψ ≫ pullback.fst _ _ = spMap R₁.subtype ≫ l a ≫ pullback.fst _ _
    rw [hl₁]
    exact (congrArg ((lvOf c a).left ≫ ·) hψ₁).trans (hψa a).1.symm
  · change (lvOf c a).left ≫ ψ ≫ A₁.hom = spMap R₁.subtype ≫ l a ≫ A₁.hom
    rw [hψ₂, hl₂, reassoc_of% e, Category.comp_id]

end GlobalTheory.SiegFg
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LogKSUp

theorem spMap_comp'' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (α : A →+* B) (β : B →+* C) :
    spMap β ≫ spMap α = spMap (β.comp α) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dualMap_comp'' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (α : A →+* B) (β : B →+* C) :
    (dualMap β).comp (dualMap α) = dualMap (β.comp α) := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [dualMap]

theorem chart_res' {X : Scheme.{0}} (U W : X.affineOpens) (h : W.1 ≤ U.1) :
    spMap (X.presheaf.map (homOfLE h).op).hom ≫ GlobalTheory.LogKS.chart U = GlobalTheory.LogKS.chart W :=
  U.2.map_fromSpec W.2 (homOfLE h).op

theorem exists_factor {X : Scheme.{0}} (U W : X.affineOpens) (h : W.1 ≤ U.1) {S : Type} [CommRing S]
    (φ : Γ(X, U.1) →+* S) (hr : ∀ z, (spMap φ ≫ GlobalTheory.LogKS.chart U) z ∈ W.1) :
    ∃ φ' : Γ(X, W.1) →+* S, φ = φ'.comp (X.presheaf.map (homOfLE h).op).hom := by
  have hr' : Set.range (spMap φ ≫ GlobalTheory.LogKS.chart U) ⊆ Set.range (GlobalTheory.LogKS.chart W) := by
    show _ ⊆ Set.range (IsAffineOpen.fromSpec W.2)
    rw [W.2.range_fromSpec]
    rintro _ ⟨z, rfl⟩
    exact hr z
  have : IsOpenImmersion (GlobalTheory.LogKS.chart W) := W.2.isOpenImmersion_fromSpec
  have : IsOpenImmersion (GlobalTheory.LogKS.chart U) := U.2.isOpenImmersion_fromSpec
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Sp S ⟶ Sp Γ(X, W.1), ψ ≫ GlobalTheory.LogKS.chart W = spMap φ ≫ GlobalTheory.LogKS.chart U :=
    ⟨IsOpenImmersion.lift (GlobalTheory.LogKS.chart W) _ hr', IsOpenImmersion.lift_fac _ _ _⟩
  refine ⟨(Spec.preimage ψ).hom, ?_⟩
  have hfac : spMap (Spec.preimage ψ).hom ≫ GlobalTheory.LogKS.chart W = spMap φ ≫ GlobalTheory.LogKS.chart U := by
    simp only [spMap, CommRingCat.ofHom_hom, Spec.map_preimage]
    exact hψ
  rw [← chart_res' U W h, ← Category.assoc, spMap_comp''] at hfac
  have h2 := Spec.map_inj.1 ((cancel_mono (GlobalTheory.LogKS.chart U)).1 hfac)
  simpa using (congrArg CommRingCat.Hom.hom h2).symm

end GlobalTheory.LogKSUp

namespace GlobalTheory.LogKSUp

theorem isKS_of_inf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (V : X.Opens) (U W : X.affineOpens) (hW : W.1 = U.1 ⊓ V) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (D : Γ(X, U.1) → Γ(X, U.1)) (DW : Γ(X, W.1) → Γ(X, W.1)) (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1)), (∀ r, DW ((X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom r) = (X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom (D r)) → IsKS t V W (fun i => spMap (dualMap (X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom) ≫ v i) DW ((X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom.mapMatrix Θ) → IsKS t V U v D Θ := by
  intro E _ _ _ H X t V U W hW n v D DW Θ hD ⟨J, Wc, j, d, hsup, hj, hfld, hcomp, htest⟩
  have hWU : W.1 ≤ U.1 := hW.le.trans inf_le_left
  have hWW : ∀ i, Wc i ≤ t.G.hom ⁻¹ᵁ W.1 := fun i =>
    (le_iSup Wc i).trans (hsup.le.trans (t.G.hom.preimage_mono inf_le_left))
  refine ⟨J, Wc, j, d, ?_, hj, hfld, fun i h r => ?_, fun i i' O hO f S _ φ g₀ w hg₀ hO' hw => ?_⟩
  · rw [hsup, hW, inf_assoc, inf_idem]
  · have e : ∀ r : Γ(X, U.1), (t.G.hom.appLE U.1 (Wc i) h).hom r =
        (t.G.hom.appLE W.1 (Wc i) (hWW i)).hom ((X.presheaf.map (homOfLE hWU).op).hom r) := by
      intro r
      exact (congrArg (fun k => k.hom r) (t.G.hom.map_appLE (hWW i) (homOfLE hWU).op)).symm
    rw [e, e, hcomp i (hWW i), hD]
  · have hr : ∀ z, (spMap φ ≫ GlobalTheory.LogKS.chart U) z ∈ W.1 := by
      intro z
      rw [← hg₀]
      have hz : g₀ z ∈ O := hO' (show z ∈ (⊤ : (Sp S).Opens) from trivial)
      exact hWW i (inf_le_left (a := Wc i) (b := Wc i') (hO hz))
    obtain ⟨φ', hfac⟩ := exists_factor U W hWU φ hr
    have hg₀' : g₀ ≫ t.G.hom = spMap φ' ≫ GlobalTheory.LogKS.chart W := by
      rw [hg₀, hfac, ← spMap_comp'', Category.assoc, chart_res']
    have := htest i i' O hO f S φ' g₀ w hg₀' hO' fun a => by
      obtain ⟨g', v', h₁, h₂, h₃⟩ := hw a
      refine ⟨g', v', h₁, ?_, h₃⟩
      rw [h₂, ← Category.assoc, spMap_comp'', dualMap_comp'', ← hfac]
    rw [this]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hfac]
    rfl

end GlobalTheory.LogKSUp
end
end

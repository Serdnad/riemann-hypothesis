module

public import Development.EtaleCohomology.EtaleTrace.Bundle006
public import Development.EtaleCohomology.EtaleTrace.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Lemma
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

@[expose] public section

section

namespace LateralTheory.EtaleTrace.GenEtaleRing

theorem ring_gen_etale (A B : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B] [Module.Finite A B]
    [Algebra.IsEtaleAt A (⊥ : Ideal B)] :
    ∃ a : A, a ≠ 0 ∧ ∀ (A' B' : Type) [CommRing A'] [CommRing B'] [Algebra A A'] [Algebra B B']
      [Algebra A' B'] [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B'],
      IsLocalization.Away a A' → IsLocalization.Away (algebraMap A B a) B' → Algebra.Etale A' B' := by
  haveI : Algebra.FinitePresentation A B := Algebra.FinitePresentation.of_finiteType.1 inferInstance
  obtain ⟨f, hf, hEt⟩ := Algebra.exists_etale_of_isEtaleAt (R := A) (⊥ : Ideal B)
  have hf0 : f ≠ 0 := by simpa using hf
  obtain ⟨a, ha, g, hg⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := A) f).exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero hf0)
  refine ⟨a, ha, fun A' B' _ _ _ _ _ _ _ _ hA hB => ?_⟩
  have hloc : Algebra.Etale A (Localization.Away (algebraMap A B a)) := by
    rw [← Algebra.basicOpen_subset_etaleLocus_iff_etale] at hEt ⊢
    refine subset_trans ?_ hEt
    rw [hg]
    exact PrimeSpectrum.basicOpen_mul_le_left _ _
  haveI : Algebra.Etale A B' := Algebra.Etale.of_equiv
    ((IsLocalization.algEquiv (Submonoid.powers (algebraMap A B a))
      (Localization.Away (algebraMap A B a)) B').restrictScalars A)
  haveI : IsLocalization (Algebra.algebraMapSubmonoid B (Submonoid.powers a)) B' := by
    rw [Algebra.algebraMapSubmonoid_powers]; exact hB
  haveI : Algebra.FormallyEtale A' B' := Algebra.FormallyEtale.localization_base (Submonoid.powers a)
  haveI : Algebra.FiniteType A A' := IsLocalization.finiteType_of_monoid_fg (Submonoid.powers a) A'
  haveI : Algebra.FinitePresentation A' B' :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation A A' B'
  exact ⟨inferInstance, inferInstance⟩

end LateralTheory.EtaleTrace.GenEtaleRing

open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.EtaleTrace.Cov

def GenAffineSetup : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X P : Scheme.{0}} [IsIntegral X] [IsIntegral P]
  (p : X ⟶ S k) (r : P ⟶ S k) (π : X ⟶ P), π ≫ r = p → LocallyOfFiniteType r → IsFinite π → Surjective π →
  (π.stalkMap (genericPoint X)).hom.FormallyUnramified →
  ∃ U : P.Opens, IsAffineOpen U ∧ (U : Set P).Nonempty ∧ IsAffineOpen (π ⁻¹ᵁ U) ∧ IsNoetherianRing Γ(P, U) ∧
    (π.app U).hom.Finite ∧ Function.Injective (π.app U).hom ∧
    ∃ _ : (⊥ : Ideal Γ(X, π ⁻¹ᵁ U)).IsPrime, (letI := (π.app U).hom.toAlgebra; Algebra.IsEtaleAt Γ(P, U) (⊥ : Ideal Γ(X, π ⁻¹ᵁ U)))

def EtaleOverBasic : Prop := ∀ {X P : Scheme.{0}} (π : X ⟶ P) (U : P.Opens), IsAffineOpen U → IsAffineOpen (π ⁻¹ᵁ U) →
  ∀ a : Γ(P, U), (letI := (π.app U).hom.toAlgebra;
    ∀ (A' B' : Type) [CommRing A'] [CommRing B'] [Algebra Γ(P, U) A'] [Algebra Γ(X, π ⁻¹ᵁ U) B']
      [Algebra A' B'] [Algebra Γ(P, U) B'] [IsScalarTower Γ(P, U) A' B'] [IsScalarTower Γ(P, U) Γ(X, π ⁻¹ᵁ U) B'],
      IsLocalization.Away a A' → IsLocalization.Away (algebraMap Γ(P, U) Γ(X, π ⁻¹ᵁ U) a) B' → Algebra.Etale A' B') →
  Etale (π ∣_ P.basicOpen a)

theorem GenEtale_of (h1 : GenAffineSetup) (h2 : EtaleOverBasic) : GenEtale := by
  intro k _ _ X P _ _ p r π hπ hr hfin hsurj hun
  obtain ⟨U, hU, hne, hU', hnoeth, hfinU, hinj, _, het⟩ := h1 k p r π hπ hr hfin hsurj hun
  haveI : Nonempty U := ⟨⟨hne.some, hne.some_mem⟩⟩
  haveI : Nonempty (π ⁻¹ᵁ U) := by
    obtain ⟨x, hx⟩ := hsurj.surj hne.some
    exact ⟨⟨x, show π x ∈ U by rw [hx]; exact hne.some_mem⟩⟩
  letI := (π.app U).hom.toAlgebra
  haveI : Module.Finite Γ(P, U) Γ(X, π ⁻¹ᵁ U) := hfinU
  haveI : FaithfulSMul Γ(P, U) Γ(X, π ⁻¹ᵁ U) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  obtain ⟨a, ha, H⟩ := LateralTheory.EtaleTrace.GenEtaleRing.ring_gen_etale Γ(P, U) Γ(X, π ⁻¹ᵁ U)
  refine ⟨P.basicOpen a, ?_, h2 π U hU hU' a H⟩
  by_contra hc
  rw [Set.not_nonempty_iff_eq_empty] at hc
  have : P.basicOpen a = ⊥ := by ext1; simpa using hc
  exact ha ((basicOpen_eq_bot_iff a).1 this)

end LateralTheory.EtaleTrace.Cov
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

def LocOpen : Prop := ∀ (X : Scheme.{0}) [IsIntegral X] (z : X.functionField), IsOpen {y : X | z ∈ loc X y}

def ChartMap : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ)
  (w : Fin (N + 1) → X.functionField) (i : Fin (N + 1)), w i ≠ 0 → ∀ (U : X.Opens),
  (∀ y ∈ U, ∀ j, w j / w i ∈ loc X y) →
  ∃ πU : U.toScheme ⟶ PN k N, πU ≫ PNto k N = U.ι ≫ p ∧ GenOn p w U πU

theorem GenOutChart_of_cut (h1 : LocOpen) (h2 : ChartMap) : GenOutChart := by
  intro k _ X _ p N w hw x
  obtain ⟨i, hi, hx⟩ := hw x
  have hop : IsOpen {y : X | ∀ j, w j / w i ∈ loc X y} := by
    have : {y : X | ∀ j, w j / w i ∈ loc X y} = ⋂ j, {y : X | w j / w i ∈ loc X y} := by
      ext y; simp
    rw [this]
    exact isOpen_iInter_of_finite fun j => h1 X (w j / w i)
  obtain ⟨πU, h1U, h2U⟩ := h2 k p N w i hi ⟨_, hop⟩ (fun y hy => hy)
  exact ⟨⟨_, hop⟩, πU, hx, h1U, h2U⟩

theorem LocOpen_pf (X : Scheme.{0}) [IsIntegral X] (z : X.functionField) : IsOpen {y : X | z ∈ loc X y} := by
  rw [isOpen_iff_forall_mem_open]
  rintro y ⟨a, rfl⟩
  obtain ⟨V, hyV, s, rfl⟩ := X.presheaf.exists_germ_eq (x := y) a
  have : Nonempty V := ⟨⟨y, hyV⟩⟩
  refine ⟨V, fun y' hy' => ?_, V.isOpen, hyV⟩
  refine ⟨X.presheaf.germ V y' hy' s, ?_⟩
  simp only [Scheme.algebraMap_germ_eq_germToFunctionField]

def ChartRing : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ)
  (w : Fin (N + 1) → X.functionField) (i : Fin (N + 1)), w i ≠ 0 → ∀ (U : X.Opens),
  (∀ y ∈ U, ∀ j, w j / w i ∈ loc X y) →
  ∀ (hx : (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ∈ homogeneousSubmodule (Fin (N + 1)) k 1),
  ∃ φ : HomogeneousLocalization.Away (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) →+* Γ(X, U),
    ∀ (y : X) (hy : y ∈ U) (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k)
      (hg : g ∈ homogeneousSubmodule (Fin (N + 1)) k (m • 1)),
      algebraMap (X.presheaf.stalk y) X.functionField
        (X.presheaf.germ U y hy (φ (HomogeneousLocalization.Away.mk _ hx m g hg))) = eval₂ (kHom p) w g / w i ^ m

def ChartGen : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ)
  (w : Fin (N + 1) → X.functionField) (i : Fin (N + 1)), w i ≠ 0 → ∀ (U : X.Opens)
  (hx : (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ∈ homogeneousSubmodule (Fin (N + 1)) k 1)
  (φ : HomogeneousLocalization.Away (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) →+* Γ(X, U)),
  (∀ (y : X) (hy : y ∈ U) (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k)
      (hg : g ∈ homogeneousSubmodule (Fin (N + 1)) k (m • 1)),
      algebraMap (X.presheaf.stalk y) X.functionField
        (X.presheaf.germ U y hy (φ (HomogeneousLocalization.Away.mk _ hx m g hg))) = eval₂ (kHom p) w g / w i ^ m) →
  ∃ πU : U.toScheme ⟶ PN k N, πU ≫ PNto k N = U.ι ≫ p ∧ GenOn p w U πU

theorem ChartMap_pf (h1 : ChartRing) (h2 : ChartGen) : ChartMap := by
  intro k _ X _ p N w i hi U hU
  have hx : (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ∈ homogeneousSubmodule (Fin (N + 1)) k 1 :=
    (mem_homogeneousSubmodule _ _).2 (isHomogeneous_X k i)
  obtain ⟨φ, hφ⟩ := h1 k p N w i hi U hU hx
  exact h2 k p N w i hi U hx φ hφ

theorem GenOutChart_of (h1 : ChartRing) (h2 : ChartGen) : GenOutChart :=
  GenOutChart_of_cut (fun X _ z => LocOpen_pf X z) (ChartMap_pf h1 h2)

end LateralTheory.EtaleTrace.Cov
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC Opposite

namespace LateralTheory.EtaleTrace

def PrimSplit : Prop := ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] (ζ ξ : Prim q A), ∃ e : Fin q → A,
  (∀ i, IsIdempotentElem (e i)) ∧ ∑ i, e i = 1 ∧ (∀ i, e i * ξ.1 = e i * ζ.1 ^ (i : ℕ)) ∧ (∀ i : Fin q, ¬ Nat.Coprime (i : ℕ) q → e i = 0)

def SplitLoc : Prop := ∀ (U : Scheme.{0}) (n : ℕ) (e : Fin n → Γ(U, ⊤)), (∀ i, IsIdempotentElem (e i)) → ∑ i, e i = 1 →
  Loc U fun V g => ∃ i, g.appTop.hom (e i) = 1

theorem primLoc_of (hS : PrimSplit) (hL : SplitLoc) : PrimLoc := by
  intro q _ U ζ ξ
  obtain ⟨e, he, hs, hx, hc⟩ := hS q Γ(U, ⊤) ζ ξ
  obtain ⟨S, hSc, hP⟩ := hL U q e he hs
  refine ⟨S, hSc, fun V g hg => ?_⟩
  obtain ⟨i, hi⟩ := hP V g hg
  have key : g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (i : ℕ) := by
    have := congrArg g.appTop.hom (hx i)
    simpa [map_mul, map_pow, hi] using this
  by_cases hcop : Nat.Coprime (i : ℕ) q
  · refine ⟨ZMod.unitOfCoprime i hcop, ?_⟩
    change g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ _
    rw [key, ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt i.2]
  · have h0 := hc i hcop
    rw [h0, map_zero] at hi
    have : Subsingleton Γ(V, ⊤) := subsingleton_of_zero_eq_one hi
    exact ⟨1, Subsingleton.elim _ _⟩

theorem TwZero_of (hTw : LateralTheory.EtaleFoundations.CongruenceLocalDecomposition.TwLoc) (hS : PrimSplit) (hL : SplitLoc) : TwZero :=
  TwZero_of_primLoc hTw (primLoc_of hS hL)

end LateralTheory.EtaleTrace
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

theorem loc_generic_top (X : Scheme.{0}) [IsIntegral X] (z : X.functionField) : z ∈ loc X (genericPoint X) := by
  refine ⟨z, ?_⟩
  simp [RingHom.algebraMap_toAlgebra, TopCat.Presheaf.stalkSpecializes_refl]

theorem FSDense_pf : FSDense := by
  intro k _ X _ p d π w cw hind

  have hz : ∀ (n : ℕ) (g : MvPolynomial (Fin (d + 1)) k), g.IsHomogeneous n →
      g ∈ (π (genericPoint X)).asHomogeneousIdeal → g = 0 := by
    intro n g hg hmem
    have hgX : (g * MvPolynomial.X 0).IsHomogeneous (n + 1) := hg.mul (isHomogeneous_X k (0 : Fin (d + 1)))
    have h1 := (cw.opens (n + 1) (Nat.succ_pos n) (g * MvPolynomial.X 0) hgX (genericPoint X))
    have hnot : genericPoint X ∉ π ⁻¹ᵁ Proj.basicOpen _ (g * MvPolynomial.X 0) := by
      intro h
      have h' : π (genericPoint X) ∈ Proj.basicOpen _ (g * MvPolynomial.X 0) := h
      rw [Proj.mem_basicOpen] at h'
      exact h' (Ideal.mul_mem_right _ _ hmem)
    have he : eval₂ (kHom p) w (g * MvPolynomial.X 0) = 0 := by
      by_contra hne
      exact hnot (h1.2 ⟨hne, fun _ _ => loc_generic_top X _⟩)
    have := hind (n + 1) _ hgX he
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h (X_ne_zero 0)
  have hbot : ∀ a ∈ (π (genericPoint X)).asHomogeneousIdeal, a = 0 := by
    intro a ha
    classical
    rw [← DirectSum.sum_support_decompose (homogeneousSubmodule (Fin (d + 1)) k) a]
    refine Finset.sum_eq_zero fun i _ => ?_
    refine hz i _ ?_ ((π (genericPoint X)).asHomogeneousIdeal.isHomogeneous i ha)
    exact (mem_homogeneousSubmodule i _).mp (SetLike.coe_mem _)
  constructor
  intro y
  have hle : (show ProjectiveSpectrum (homogeneousSubmodule (Fin (d + 1)) k) from π (genericPoint X)) ≤
      (show ProjectiveSpectrum (homogeneousSubmodule (Fin (d + 1)) k) from y) := by
    rw [← ProjectiveSpectrum.as_ideal_le_as_ideal]
    intro a ha
    rw [hbot a ha]
    exact zero_mem _
  have hc := (ProjectiveSpectrum.le_iff_mem_closure _ _ _).mp hle
  exact closure_mono (Set.singleton_subset_iff.mpr (Set.mem_range_self _)) hc
end Cov
end EtaleTrace
end LateralTheory
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.EtaleTrace.Cov

lemma isPullback_equalizer {k : Type} [Field k] {X P : Scheme.{0}} (p : X ⟶ S k) (r : P ⟶ S k) (π : X ⟶ P)
    (hπ : π ≫ r = p) (t : Pt r) :
    IsPullback (equalizer.ι π (p ≫ t.1)) (equalizer.ι π (p ≫ t.1) ≫ p) π t.1 := by
  have key : ∀ {T : Scheme.{0}} (a : T ⟶ X) (b : T ⟶ S k), a ≫ π = b ≫ t.1 → a ≫ p = b := by
    intro T a b h
    rw [← hπ, ← Category.assoc, h, Category.assoc, t.2, Category.comp_id]
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk ?_ ?_ ?_ ?_ ?_)
  · rw [Category.assoc]; exact equalizer.condition _ _
  · intro s
    exact equalizer.lift s.fst (by rw [s.condition, ← Category.assoc, key s.fst s.snd s.condition])
  · intro s; exact equalizer.lift_ι _ _
  · intro s
    rw [← Category.assoc, equalizer.lift_ι]; exact key s.fst s.snd s.condition
  · intro s m h1 _
    apply equalizer.hom_ext
    exact h1.trans (equalizer.lift_ι _ _).symm

theorem FibreOfEtale_of : FibreOfEtale := by
  intro k _ X P p r π hπ V hE t ht
  have hr : Set.range t.1.base ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]; rintro _ ⟨x, rfl⟩; exact ht x
  set t' := IsOpenImmersion.lift V.ι t.1 hr
  have ht' : t' ≫ V.ι = t.1 := IsOpenImmersion.lift_fac _ _ _
  have s := (congrArg (IsPullback (equalizer.ι π (p ≫ t.1)) (equalizer.ι π (p ≫ t.1) ≫ p) π) ht').mpr
    (isPullback_equalizer p r π hπ t)
  have h := IsPullback.of_right' s (isPullback_morphismRestrict π V).flip
  exact MorphismProperty.of_isPullback h hE

end LateralTheory.EtaleTrace.Cov
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

def GenOnAgree : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ)
  (w : Fin (N + 1) → X.functionField) (U U' : X.Opens) (πU : U.toScheme ⟶ PN k N) (πU' : U'.toScheme ⟶ PN k N),
  GenOn p w U πU → GenOn p w U' πU' → pullback.fst U.ι U'.ι ≫ πU = pullback.snd U.ι U'.ι ≫ πU'

def GenOnGen : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ)
  (w : Fin (N + 1) → X.functionField) (π : X ⟶ PN k N) (U : X.Opens),
  genericPoint X ∈ U → GenOn p w U (U.ι ≫ π) → Gen p π w

theorem GenOutGlue_of (h1 : GenOnAgree) (h2 : GenOnGen) : GenOutGlue := by
  intro k _ X _ p N w hloc
  choose U πU hxU hover hgen using hloc
  have hcov : TopologicalSpace.IsOpenCover U := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro x _
    exact (TopologicalSpace.Opens.mem_iSup).2 ⟨x, hxU x⟩
  let 𝒰 := X.openCoverOfIsOpenCover U hcov
  have hf : ∀ x y, pullback.fst (𝒰.f x) (𝒰.f y) ≫ πU x = pullback.snd (𝒰.f x) (𝒰.f y) ≫ πU y :=
    fun x y => h1 k p N w (U x) (U y) (πU x) (πU y) (hgen x) (hgen y)
  refine ⟨𝒰.glueMorphisms πU hf, ?_, ?_⟩
  · refine 𝒰.hom_ext _ _ fun x => ?_
    have e : 𝒰.f x ≫ 𝒰.glueMorphisms πU hf = πU x := 𝒰.ι_glueMorphisms πU hf x
    rw [← Category.assoc, e]
    exact hover x
  · have hη := 𝒰.ι_glueMorphisms πU hf (genericPoint X)
    refine h2 k p N w _ (U (genericPoint X)) (hxU _) ?_
    have : (U (genericPoint X)).ι ≫ 𝒰.glueMorphisms πU hf = πU (genericPoint X) := hη
    rw [this]
    exact hgen _

theorem genOnGen : GenOnGen := by
  intro k _ X _ p N w π U hη hG n hn f hf
  obtain ⟨h1, h2⟩ := hG hη n hn f hf
  refine ⟨?_, ?_⟩
  · rw [← h1]; exact Iff.rfl
  · intro m g hg h
    have h' := h2 m g hg h
    have hinj : Function.Injective (U.ι.stalkMap ⟨genericPoint X, hη⟩).hom :=
      haveI : IsIso (U.ι.stalkMap ⟨genericPoint X, hη⟩) :=
        (IsOpenImmersion.iff_isIso_stalkMap.1 inferInstance).2 _
      ((asIso (U.ι.stalkMap ⟨genericPoint X, hη⟩)).commRingCatIsoToRingEquiv).injective
    apply hinj
    refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) ?_ (map_pow _ _ _)).trans h')
    rw [Scheme.Hom.comp_app]
    exact (Scheme.Hom.germ_stalkMap_apply U.ι (π ⁻¹ᵁ Proj.basicOpen _ f) ⟨genericPoint X, hη⟩ h
      (π.app _ (Proj.awayToSection _ f (HomogeneousLocalization.Away.mk _ hf m g hg))))

theorem GenOutGlue_of_agree (h1 : GenOnAgree) : GenOutGlue :=
  GenOutGlue_of h1 genOnGen

end LateralTheory.EtaleTrace.Cov
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.EtaleTrace

theorem exists_ratPt_of_etale (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} (p : X ⟶ S k)
    (hp : IsProper p) {U : Scheme.{0}} (f : U ⟶ X) [Etale f] (x : U) :
    ∃ w : S k ⟶ U, w ≫ f ≫ p = 𝟙 _ := by
  have := hp
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  have hopen : IsOpen (Set.range f) := f.isOpenMap.isOpen_range
  obtain ⟨y, ⟨x', rfl⟩, hy⟩ := nonempty_inter_closedPoints (show (Set.range f).Nonempty from ⟨f x, x, rfl⟩) hopen.isLocallyClosed
  let s : S k ⟶ X := pointOfClosedPoint p (f x') hy
  obtain ⟨l, hl, -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed f s x' (pointOfClosedPoint_apply p (f x') hy _).symm
  exact ⟨l, by rw [reassoc_of% hl]; exact pointOfClosedPoint_comp p (f x') hy⟩

theorem PtCov_of : PtCov := by
  intro k _ _ X p hp Sv hSv
  obtain ⟨𝒰, h𝒰⟩ := Scheme.mem_grothendieckTopology_iff.1 hSv
  let T : Sieve X :=
    { arrows := fun V g => ∃ (U : Scheme.{0}) (g' : U ⟶ X) (h : V ⟶ U),
        Sv.arrows g' ∧ h ≫ g' = g ∧ ∃ w : S k ⟶ U, w ≫ g' ≫ p = 𝟙 _
      downward_closed := by
        rintro V W g ⟨U, g', h, hg', rfl, w, hw⟩ a
        exact ⟨U, g', a ≫ h, hg', by simp, w, hw⟩ }
  refine ⟨T, ?_, fun V g hg => hg⟩
  have hG : Sieve.generate (Presieve.ofArrows 𝒰.X 𝒰.f) ∈ Scheme.etaleTopology X :=
    Scheme.mem_grothendieckTopology_iff.2 ⟨𝒰, Sieve.le_generate _⟩
  refine (Scheme.etaleTopology).transitive hG T ?_
  rintro Z _ ⟨W, a, b, hb, rfl⟩
  rw [Sieve.pullback_comp]
  refine (Scheme.etaleTopology).pullback_stable a ?_
  obtain ⟨i⟩ := hb
  by_cases hne : Nonempty (𝒰.X i)
  · obtain ⟨x⟩ := hne
    obtain ⟨w, hw⟩ := exists_ratPt_of_etale k p hp (𝒰.f i) x
    have : T.arrows (𝒰.f i) := ⟨𝒰.X i, 𝒰.f i, 𝟙 _, h𝒰 _ _ (Presieve.ofArrows.mk i), by simp, w, hw⟩
    rw [Sieve.pullback_eq_top_of_mem T this]
    exact (Scheme.etaleTopology).top_mem _
  · have : IsEmpty (𝒰.X i) := not_nonempty_iff.1 hne
    exact (Scheme.etaleTopology).superset_covering bot_le (Scheme.bot_mem_grothendieckTopology _)

end LateralTheory.EtaleTrace
end
end

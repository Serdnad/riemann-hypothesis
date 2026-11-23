module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle016
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.IntReg

theorem mem_regAt_of_isIntegral_of_stalk :
    ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (p : Cpt ξ), IsCptGen ξ →
      IsIntegrallyClosed (X.presheaf.stalk p.1) → ∀ a : Ω, IsIntegral ℤ a → a ∈ regAt ξ p := by
  intro X Ω _ ξ p hξ hcl a ha
  have hinj : Function.Injective (genMap ξ p) := hξ.inj p
  let _ : Algebra (X.presheaf.stalk p.1) Ω := (genMap ξ p).toAlgebra
  have hmap : ∀ x, algebraMap (X.presheaf.stalk p.1) Ω x = genMap ξ p x := fun _ => rfl
  have : IsDomain (X.presheaf.stalk p.1) := hinj.isDomain _
  have : FaithfulSMul (X.presheaf.stalk p.1) Ω :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have : IsFractionRing (X.presheaf.stalk p.1) Ω := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨b, c, hc, e⟩ := exists_frac_genMap ξ hξ p z
    exact ⟨b, c, by rw [hmap, hmap, ← e, mul_div_cancel_right₀ _ hc]⟩
  have hb : _root_.IsIntegral (X.presheaf.stalk p.1) a := ha.tower_top
  obtain ⟨w, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hb
  exact ⟨w, rfl⟩

end GlobalTheory.CompanionTheory.Ar.IntReg
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.torsion_along_base_change : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : BT.QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] (x : Sp R ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (R' : Type) [CommRing R'] [IsDomain R'] (φ : R →+* R') (Γ' : BT.QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ φ F → Γ'.IsTorsionAlong G (Spec.map (CommRingCat.ofHom φ) ≫ x) N (F ≫ i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TorBC.isTorsionAlong_baseChange | exact GlobalTheory.CompanionTheory.Ar.TorBC.isTorsionAlong_baseChange | (intros; apply GlobalTheory.CompanionTheory.Ar.TorBC.isTorsionAlong_baseChange <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]

theorem regAt_isLocalRing (q : Cpt ξ) : IsLocalRing (regAt ξ q) :=
  IsLocalRing.of_surjective' (genMap ξ q).rangeRestrict (genMap ξ q).rangeRestrict_surjective

theorem not_inFibre_of_isUnit {q : Cpt ξ} {p : ℕ} (h : IsUnit (p : regAt ξ q)) : ¬ InFibre ξ p q := by
  obtain ⟨v, hv⟩ := h.exists_right_inv
  have e : (p : Ω) * (v : Ω) = 1 := by
    have := congrArg (Subtype.val) hv
    simpa using this
  have hp : (p : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one e
  have hreg : (p : Ω) ∈ regAt ξ q := natCast_mem (regAt ξ q) p
  have hinv : (p : Ω)⁻¹ ∈ regAt ξ q := by
    rw [eq_comm.1 (eq_inv_of_mul_eq_one_right e)]
    exact v.2
  exact not_not.2 ⟨hp, hreg, hinv⟩

theorem inFibre_unique {q : Cpt ξ} {p p' : ℕ} (hp : p.Prime) (hp' : p'.Prime) (h : InFibre ξ p q)
    (h' : InFibre ξ p' q) : p' = p := by
  by_contra hne
  haveI := regAt_isLocalRing (ξ := ξ) q
  have hc : IsCoprime (p : ℤ) (p' : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hp').2 (Ne.symm hne))
  obtain ⟨a, b, hab⟩ := hc.map (Int.castRingHom (regAt ξ q))
  simp only [eq_intCast, Int.cast_natCast] at hab
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hab with hu | hu
  · exact not_inFibre_of_isUnit (isUnit_of_mul_isUnit_right hu) h
  · exact not_inFibre_of_isUnit (isUnit_of_mul_isUnit_right hu) h'

end GlobalTheory.CompanionTheory.Ar
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ValHom

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

def stalkEquiv {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (hξ : IsCptGen ξ) (p : Cpt ξ) : X.presheaf.stalk p.1 ≃+* regAt ξ p :=
  RingEquiv.ofBijective (genMap ξ p).rangeRestrict
    ⟨fun a b hab => hξ.inj p (congrArg Subtype.val hab), (genMap ξ p).rangeRestrict_surjective⟩

theorem stalkEquiv_coe {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (hξ : IsCptGen ξ) (p : Cpt ξ) (s : X.presheaf.stalk p.1) :
    ((stalkEquiv ξ hξ p s : regAt ξ p) : Ω) = genMap ξ p s := rfl

theorem isUnit_iff_unitAt {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (hξ : IsCptGen ξ) (p : Cpt ξ) (s : X.presheaf.stalk p.1) :
    IsUnit s ↔ unitAt ξ p (genMap ξ p s) := by
  constructor
  · intro hs
    obtain ⟨u, rfl⟩ := hs
    refine ⟨((u.isUnit).map (genMap ξ p)).ne_zero, ⟨_, rfl⟩, ⟨((u⁻¹ : _ˣ) : X.presheaf.stalk p.1), ?_⟩⟩
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul, Units.inv_mul, map_one]
  · rintro ⟨h0, -, ⟨t, ht⟩⟩
    refine IsUnit.of_mul_eq_one t (hξ.inj p ?_)
    rw [map_mul, map_one, ht, mul_inv_cancel₀ h0]

theorem exists_valAt_hom (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (R : Type) [CommRing R] [IsLocalRing R] (z : Spec (CommRingCat.of R) ⟶ X)
    (h : genPt ξ ⤳ centre z) (hξ : IsCptGen ξ) :
    ∃ φ : regAt ξ ⟨centre z, h⟩ →+* R,
      (∀ (a : Ω) (r : R), ValAt ξ z a r ↔ ∃ ha : a ∈ regAt ξ ⟨centre z, h⟩, φ ⟨a, ha⟩ = r) ∧
      ∀ a : regAt ξ ⟨centre z, h⟩, IsUnit (φ a) ↔ unitAt ξ ⟨centre z, h⟩ (a : Ω) := by
  let p : Cpt ξ := ⟨centre z, h⟩
  let e := stalkEquiv ξ hξ p
  let v : X.presheaf.stalk (centre z) →+* R := (Scheme.stalkClosedPointTo z).hom
  have hv : IsLocalHom v := inferInstanceAs (IsLocalHom (Scheme.stalkClosedPointTo z).hom)
  have key : ∀ s, e.symm (e s) = s := e.symm_apply_apply
  refine ⟨v.comp (e.symm : regAt ξ p →+* X.presheaf.stalk p.1), ?_, ?_⟩
  · intro a r
    constructor
    · rintro ⟨h', s, hs, hr⟩
      have hs' : genMap ξ p s = a := hs
      refine ⟨⟨s, hs'⟩, ?_⟩
      have : (⟨a, ⟨s, hs'⟩⟩ : regAt ξ p) = e s := Subtype.ext hs'.symm
      simp only [RingHom.comp_apply, RingHom.coe_coe]
      rw [this, key]
      exact hr
    · rintro ⟨ha, hr⟩
      refine ⟨h, e.symm ⟨a, ha⟩, ?_, hr⟩
      have := stalkEquiv_coe ξ hξ p (e.symm ⟨a, ha⟩)
      rw [RingEquiv.apply_symm_apply] at this
      exact this.symm
  · intro a
    obtain ⟨s, rfl⟩ := e.surjective a
    simp only [RingHom.comp_apply, RingHom.coe_coe]
    rw [key]
    have : IsUnit (v s) ↔ IsUnit s := isUnit_map_iff v s
    exact this.trans (isUnit_iff_unitAt ξ hξ p s)

end GlobalTheory.CompanionTheory.Ar.ValHom
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.CoordNoeth

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

def secVal (ξ : Spec (CommRingCat.of Ω) ⟶ X) (U : X.Opens) (h : genPt ξ ∈ U) : Γ(X, U) →+* Ω :=
  (X.presheaf.germ U (genPt ξ) h ≫ Scheme.stalkClosedPointTo ξ).hom

lemma genMap_germ (ξ : Spec (CommRingCat.of Ω) ⟶ X) (q : Cpt ξ) (U : X.Opens) (hq : q.1 ∈ U)
    (h : genPt ξ ∈ U) (s : Γ(X, U)) :
    genMap ξ q (X.presheaf.germ U q.1 hq s) = secVal ξ U h s := by
  have e : X.presheaf.germ U q.1 hq ≫ X.presheaf.stalkSpecializes q.2 = X.presheaf.germ U (genPt ξ) h :=
    TopCat.Presheaf.germ_stalkSpecializes _ _ _
  simp only [genMap, secVal, ← e]
  rfl

lemma secVal_res (ξ : Spec (CommRingCat.of Ω) ⟶ X) {U V : X.Opens} (i : V ⟶ U) (h : genPt ξ ∈ V)
    (s : Γ(X, U)) : secVal ξ V h (X.presheaf.map i.op s) = secVal ξ U (leOfHom i h) s := by
  exact congrArg (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ_res_apply i (genPt ξ) h s)

lemma secVal_injective {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hg : IsCptGen ξ) (U : X.Opens)
    (h : genPt ξ ∈ U) (hU : ∀ q : X, q ∈ U → genPt ξ ⤳ q) : Function.Injective (secVal ξ U h) := by
  intro s t e
  refine TopCat.Presheaf.section_ext X.sheaf U s t fun q hq => ?_
  apply hg.inj ⟨q, hU q hq⟩
  exact (genMap_germ ξ ⟨q, hU q hq⟩ U hq h s).trans (e.trans (genMap_germ ξ ⟨q, hU q hq⟩ U hq h t).symm)

lemma exists_secVal_eq {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hg : IsCptGen ξ) (U : X.Opens)
    (h : genPt ξ ∈ U) (hU : ∀ q : X, q ∈ U → genPt ξ ⤳ q) (a : Ω)
    (ha : ∀ q : Cpt ξ, q.1 ∈ U → a ∈ regAt ξ q) : ∃ s, secVal ξ U h s = a := by
  have key : ∀ q : U, ∃ (W : X.Opens) (_ : q.1 ∈ W) (_ : W ⟶ U) (hW : genPt ξ ∈ W) (s : Γ(X, W)),
      secVal ξ W hW s = a := by
    intro q
    obtain ⟨t, ht⟩ := ha ⟨q.1, hU _ q.2⟩ q.2
    obtain ⟨V, hqV, s, rfl⟩ := X.presheaf.germ_exist t
    have hqW : q.1 ∈ V ⊓ U := ⟨hqV, q.2⟩
    have hW : genPt ξ ∈ V ⊓ U := (hU _ q.2).mem_open (V ⊓ U).isOpen hqW
    refine ⟨V ⊓ U, hqW, homOfLE inf_le_right, hW, X.presheaf.map (homOfLE inf_le_left).op s, ?_⟩
    rw [secVal_res, ← genMap_germ ξ ⟨q.1, hU _ q.2⟩ V hqV]
    exact ht
  choose W hq i hW s hs using key
  have comp : TopCat.Presheaf.IsCompatible X.sheaf.1 W s := by
    intro p q
    apply secVal_injective hg (W p ⊓ W q) ⟨hW p, hW q⟩ (fun r hr => hU r (leOfHom (i p) hr.1))
    refine (secVal_res ξ _ _ _).trans (Eq.trans ?_ (secVal_res ξ _ _ _).symm)
    rw [hs, hs]
  obtain ⟨t, ht, -⟩ := X.sheaf.existsUnique_gluing' W U i
    (fun r hr => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨r, hr⟩, hq _⟩) s comp
  refine ⟨t, ?_⟩
  rw [← hs ⟨_, h⟩, ← ht ⟨_, h⟩]
  exact (secVal_res ξ _ _ _).symm

lemma mem_regAt_self {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hg : IsCptGen ξ) (a : Ω) :
    a ∈ regAt ξ ⟨genPt ξ, specializes_rfl⟩ := by
  obtain ⟨t, ht⟩ := hg.bij.2 a
  refine ⟨t, ?_⟩
  simp only [genMap, TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]
  exact ht

lemma isNoetherianRing_chart {ξ : Spec (CommRingCat.of Ω) ⟶ X} {o : Type} [CommRing o]
    [IsNoetherianRing o] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω} (tie : CoordTie o ξ x)
    (c : κ) (hc : x c ≠ 0) (U : X.Opens) (hU : ∀ q : X, q ∈ U ↔ ∃ h : genPt ξ ⤳ q, InChart ξ x c ⟨q, h⟩)
    (h : genPt ξ ∈ U) : IsNoetherianRing Γ(X, U) := by
  have hsp : ∀ q : X, q ∈ U → genPt ξ ⤳ q := fun q hq => ((hU q).1 hq).elim fun h _ => h
  have hA : IsNoetherianRing (Algebra.adjoin o (Set.range fun j => x j / x c)) := by
    have : Algebra.FiniteType o (Algebra.adjoin o (Set.range fun j => x j / x c)) :=
      (Subalgebra.fg_iff_finiteType _).1 ⟨(Set.finite_range fun j => x j / x c).toFinset, by simp⟩
    exact Algebra.FiniteType.isNoetherianRing o _
  have mem : ∀ a, a ∈ Algebra.adjoin o (Set.range fun j => x j / x c) ↔ ∃ s, secVal ξ U h s = a := by
    intro a
    rw [tie.ring c hc a]
    constructor
    · intro H
      refine exists_secVal_eq tie.gen U h hsp a fun q hq => ?_
      obtain ⟨_, hc'⟩ := (hU q.1).1 hq
      exact H q hc'
    · rintro ⟨s, rfl⟩ p hp
      have hpU : p.1 ∈ U := (hU p.1).2 ⟨p.2, hp⟩
      exact ⟨_, genMap_germ ξ p U hpU h s⟩
  let g : Γ(X, U) →+* Algebra.adjoin o (Set.range fun j => x j / x c) :=
    (secVal ξ U h).codRestrict _ fun s => (mem _).2 ⟨s, rfl⟩
  have hb : Function.Bijective g := by
    constructor
    · intro s t e
      exact secVal_injective tie.gen U h hsp (congrArg Subtype.val e)
    · rintro ⟨a, ha⟩
      obtain ⟨s, rfl⟩ := (mem a).1 ha
      exact ⟨s, rfl⟩
  exact isNoetherianRing_of_ringEquiv _ (RingEquiv.ofBijective g hb).symm

theorem noetherian_of_coordTie (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (o : Type) [CommRing o] [IsNoetherianRing o] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω)
    (tie : CoordTie o ξ x) :
    (∀ p : Cpt ξ, IsNoetherianRing (regAt ξ p)) ∧ ((∀ q : X, genPt ξ ⤳ q) → IsNoetherian X ∧ IsIntegral X) := by
  refine ⟨fun p => ?_, fun hall => ?_⟩
  · obtain ⟨c, hcp⟩ := tie.cover p
    obtain ⟨U, hUa, hU⟩ := tie.affine c hcp.1
    have hp : p.1 ∈ U := (hU p.1).2 ⟨p.2, hcp⟩
    have h : genPt ξ ∈ U := p.2.mem_open U.isOpen hp
    haveI := isNoetherianRing_chart tie c hcp.1 U hU h
    letI := X.presheaf.algebra_section_stalk (⟨p.1, hp⟩ : U)
    haveI := hUa.isLocalization_stalk ⟨p.1, hp⟩
    haveI : IsNoetherianRing (X.presheaf.stalk p.1) :=
      IsLocalization.isNoetherianRing (hUa.primeIdealOf ⟨p.1, hp⟩).asIdeal.primeCompl _ ‹_›
    exact isNoetherianRing_of_surjective _ _ (genMap ξ p).rangeRestrict
      (genMap ξ p).rangeRestrict_surjective
  · have ex : ∀ c : {c // x c ≠ 0}, ∃ U : X.affineOpens,
        ∀ q : X, q ∈ (U : X.Opens) ↔ ∃ h : genPt ξ ⤳ q, InChart ξ x c.1 ⟨q, h⟩ := fun c => by
      obtain ⟨U, hUa, hU⟩ := tie.affine c.1 c.2
      exact ⟨⟨U, hUa⟩, hU⟩
    choose S hS using ex
    have hcov : (⨆ c, (S c : X.Opens)) = ⊤ := by
      refine eq_top_iff.2 fun q _ => ?_
      obtain ⟨c, hc⟩ := tie.cover ⟨q, hall q⟩
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨c, hc.1⟩, (hS _ q).2 ⟨hall q, hc⟩⟩
    have hgen : ∀ c, genPt ξ ∈ (S c : X.Opens) := fun c =>
      (hS c _).2 ⟨specializes_rfl, c.2, fun _ => mem_regAt_self tie.gen _⟩
    haveI : IsLocallyNoetherian X := isLocallyNoetherian_of_affine_cover hcov fun c =>
      isNoetherianRing_chart tie c.1 c.2 _ (hS c) (hgen c)
    haveI : CompactSpace X := by
      refine ⟨?_⟩
      have e : (Set.univ : Set X) = ⋃ c, ((S c : X.Opens) : Set X) := by
        have := congrArg (fun V : X.Opens => (V : Set X)) hcov
        simpa using this.symm
      rw [e]
      exact isCompact_iUnion fun c => (S c).2.isCompact
    have hcl : closure {genPt ξ} = (Set.univ : Set X) :=
      Set.eq_univ_of_forall fun q => specializes_iff_mem_closure.1 (hall q)
    have hirr : IsIrreducible (Set.univ : Set X) := hcl ▸ isIrreducible_singleton.closure
    haveI : IrreducibleSpace X := (irreducibleSpace_def X).2 hirr
    haveI : ∀ q : X, _root_.IsReduced (X.presheaf.stalk q) := fun q =>
      isReduced_of_injective (genMap ξ ⟨q, hall q⟩) (tie.gen.inj _)
    haveI : AlgebraicGeometry.IsReduced X := isReduced_of_isReduced_stalk X
    exact ⟨{}, isIntegral_of_irreducibleSpace_of_isReduced X⟩

end GlobalTheory.CompanionTheory.Ar.CoordNoeth

end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagFib

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem isUnit_natCast_stalk (X : Scheme.{0}) (L : Type) [Field L] [CharZero L] (z : Sp L ⟶ X) (n : ℕ) (hn : n ≠ 0) :
    IsUnit ((n : X.presheaf.stalk (centre z))) := by
  set x := IsLocalRing.closedPoint L
  have hL : IsUnit (n : L) := (Nat.cast_ne_zero.mpr hn).isUnit
  let φ : L →+* (Sp L).presheaf.stalk x :=
    ((Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ (Sp L).presheaf.germ ⊤ x trivial).hom
  have h2 : IsUnit (n : (Sp L).presheaf.stalk x) := by
    simpa using hL.map φ
  have h3 : IsUnit ((z.stalkMap x).hom (n : X.presheaf.stalk (z x))) := by
    simpa using h2
  haveI : IsLocalHom (z.stalkMap x).hom := z.prop x
  exact (isUnit_map_iff (z.stalkMap x).hom _).mp h3

end GlobalTheory.CompanionTheory.Ar.FlagFib
end
end

section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.EigMap

open GlobalTheory.CompanionTheory.Ar

section Indep

variable {k V O : Type} [Field k] [AddCommGroup V] [Module k V] [CommRing O]

theorem mem_eigSp_iff' (ρ : O →+* Module.End k V) (σ : O →+* k) (x : V) :
    x ∈ eigSp ρ σ ↔ ∀ a, ρ a x = σ a • x := by
  simp [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

theorem eigSp_sum_eq_zero (ρ : O →+* Module.End k V) (s : Finset (O →+* k)) :
    ∀ f : (O →+* k) → V, (∀ t ∈ s, f t ∈ eigSp ρ t) → ∑ t ∈ s, f t = 0 → ∀ t ∈ s, f t = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert t₀ s ht₀ ih =>
    intro f hf hsum
    have hf' : ∀ t ∈ s, f t ∈ eigSp ρ t := fun t ht => hf t (Finset.mem_insert_of_mem ht)
    have hf₀ := (mem_eigSp_iff' ρ t₀ _).1 (hf t₀ (Finset.mem_insert_self _ _))
    rw [Finset.sum_insert ht₀] at hsum
    have hs : ∀ t ∈ s, f t = 0 := by
      intro t ht
      have hne : t ≠ t₀ := fun e => ht₀ (e ▸ ht)
      obtain ⟨a, ha⟩ : ∃ a, t a ≠ t₀ a := by
        by_contra hcon
        push Not at hcon
        exact hne (RingHom.ext hcon)
      have hz : ∑ u ∈ s, (u a - t₀ a) • f u = 0 := by
        have h1 : ρ a (f t₀ + ∑ u ∈ s, f u) - t₀ a • (f t₀ + ∑ u ∈ s, f u) = 0 := by
          rw [hsum]; simp
        have h2 : ρ a (∑ u ∈ s, f u) = ∑ u ∈ s, u a • f u := by

          rw [map_sum]
          exact Finset.sum_congr rfl fun u hu => (mem_eigSp_iff' ρ u _).1 (hf' u hu) a
        rw [map_add (f := _), hf₀ a, h2, smul_add, Finset.smul_sum] at h1
        simp only [sub_smul, Finset.sum_sub_distrib]
        rw [← h1]
        abel
      have := ih (fun u => (u a - t₀ a) • f u)
        (fun u hu => Submodule.smul_mem _ _ (hf' u hu)) hz t ht
      exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 ha)
    have h₀ : f t₀ = 0 := by
      rw [Finset.sum_eq_zero hs, add_zero] at hsum
      exact hsum
    intro t ht
    rcases Finset.mem_insert.1 ht with rfl | ht
    · exact h₀
    · exact hs t ht

theorem iSupIndep_eigSp (ρ : O →+* Module.End k V) : iSupIndep (fun σ : O →+* k => eigSp ρ σ) :=
  (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).2 fun s v hv h0 i hi =>
    eigSp_sum_eq_zero ρ s v hv h0 i hi

theorem eq_zero_of_mem_eigSp_of_mem_iSup (ρ : O →+* Module.End k V) (σ : O →+* k) {y : V}
    (h₁ : y ∈ eigSp ρ σ) (h₂ : y ∈ ⨆ σ' ∈ {σ' : O →+* k | σ' ≠ σ}, eigSp ρ σ') : y = 0 :=
  Submodule.disjoint_def.1 (iSupIndep_eigSp ρ σ) y h₁ (by simpa using h₂)

end Indep

theorem eigComp_map {k k' V V' O : Type} [Field k] [Field k'] [AddCommGroup V] [Module k V] [AddCommGroup V']
    [Module k' V'] [CommRing O] (κ : k →+* k') (j : V →+ V') (hj : ∀ (c : k) x, j (c • x) = κ c • j x)
    (ρ : O →+* Module.End k V) (ρ' : O →+* Module.End k' V') (hρ : ∀ a x, ρ' a (j x) = j (ρ a x))
    (σ : O →+* k) (x : V) (hx : eigComp ρ σ x ≠ 0) :
    eigComp ρ' (κ.comp σ) (j x) = j (eigComp ρ σ x) := by
  have hmap : ∀ (s : O →+* k) (y : V), y ∈ eigSp ρ s → j y ∈ eigSp ρ' (κ.comp s) := by
    intro s y hy
    refine (mem_eigSp_iff' ρ' _ _).2 fun a => ?_
    rw [hρ, (mem_eigSp_iff' ρ s y).1 hy a, hj]
    rfl
  have hsup : ∀ y ∈ ⨆ σ' ∈ {σ' : O →+* k | σ' ≠ σ}, eigSp ρ σ',
      j y ∈ ⨆ τ' ∈ {τ' : O →+* k' | τ' ≠ κ.comp σ}, eigSp ρ' τ' := by
    intro y hy
    refine Submodule.iSup_induction _ (motive := fun y =>
      j y ∈ ⨆ τ' ∈ {τ' : O →+* k' | τ' ≠ κ.comp σ}, eigSp ρ' τ') hy ?_ (by simp) ?_
    · intro s y hy
      refine Submodule.iSup_induction _ (motive := fun y =>
        j y ∈ ⨆ τ' ∈ {τ' : O →+* k' | τ' ≠ κ.comp σ}, eigSp ρ' τ') hy ?_ (by simp) ?_
      · intro hs y hy
        have hne : κ.comp s ≠ κ.comp σ := fun e => hs (RingHom.ext fun a =>
          κ.injective (RingHom.congr_fun e a))
        exact Submodule.mem_iSup_of_mem (κ.comp s) (Submodule.mem_iSup_of_mem hne (hmap s y hy))
      · intro a b ha hb
        rw [map_add (f := _)]
        exact Submodule.add_mem _ ha hb
    · intro a b ha hb
      rw [map_add (f := _)]
      exact Submodule.add_mem _ ha hb
  have h : ∃ p ∈ eigSp ρ σ, x - p ∈ ⨆ σ' ∈ {σ' : O →+* k | σ' ≠ σ}, eigSp ρ σ' := by
    by_contra hcon
    exact hx (by rw [eigComp, dite_eq_right hcon])
  have hp : eigComp ρ σ x = h.choose := by rw [eigComp, dite_eq_left h]
  obtain ⟨hp₁, hp₂⟩ := h.choose_spec
  rw [← hp] at hp₁ hp₂
  have hp₃ := hsup _ hp₂
  rw [map_sub] at hp₃
  have h' : ∃ q ∈ eigSp ρ' (κ.comp σ), j x - q ∈ ⨆ τ' ∈ {τ' : O →+* k' | τ' ≠ κ.comp σ}, eigSp ρ' τ' :=
    ⟨_, hmap σ _ hp₁, hp₃⟩
  have hq : eigComp ρ' (κ.comp σ) (j x) = h'.choose := by rw [eigComp, dite_eq_left h']
  obtain ⟨hq₁, hq₂⟩ := h'.choose_spec
  rw [← hq] at hq₁ hq₂
  refine sub_eq_zero.1 (eq_zero_of_mem_eigSp_of_mem_iSup ρ' (κ.comp σ)
    (Submodule.sub_mem _ hq₁ (hmap σ _ hp₁)) ?_)
  have : eigComp ρ' (κ.comp σ) (j x) - j (eigComp ρ σ x) =
      (j x - j (eigComp ρ σ x)) - (j x - eigComp ρ' (κ.comp σ) (j x)) := by abel
  rw [this]
  exact Submodule.sub_mem _ hp₃ hq₂

end GlobalTheory.CompanionTheory.Ar.Cusp.EigMap
end

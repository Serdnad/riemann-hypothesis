module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle027
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueGlueSectionsPrincipalCover
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyPadicIntRingHomOfIsAdicComplete
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle006
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle003
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsChartFiniteType
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem _root_.GlobalTheory.T.frameChange_comm_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y y' : FrPt Xo c S) (z z' : FrPt Xo c T) (g : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S)) (a : S), FrChg g a y y' → FrMap φ y z → (FrMap φ y' z' ↔ FrChg (fun τ => (g τ).map φ) (φ a) z z') := by
  first | exact @GlobalTheory.Frames.ChgBC.frChg_baseChange | exact GlobalTheory.Frames.ChgBC.frChg_baseChange | (intros; apply GlobalTheory.Frames.ChgBC.frChg_baseChange <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem _root_.GlobalTheory.T.lieBasis_iff_tangentBasis_pullback_universal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (G' : Over (Sp S)) [GrpObj G'] (φ : G'.left ⟶ Xo.univ.t.G.left), IsGrpPullback G' Xo.univ.t.G x φ → (∀ w : (Sp (DualNumber S) ⟶ Xo.univ.t.G.left), IsTanAt x w → ∃ v : epsR S ⟶ G', v.left ≫ φ = w) ∧ ∀ (n : ℕ) (v : Fin n → (epsR S ⟶ G')), IsLieBasis v ↔ TanBasis x (fun i => (v i).left ≫ φ) := by
  first | exact @GlobalTheory.Frames.lieBasis_iff_tanBasis | exact GlobalTheory.Frames.lieBasis_iff_tanBasis | (intros; apply GlobalTheory.Frames.lieBasis_iff_tanBasis <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

theorem _root_.GlobalTheory.T.universalFrameRing_subalgebra_eq_top : ∀ (K : Type) [Field K] (J : Type) (m : J → ℕ) (R A : Type) [CommRing R] [Algebra K R] [CommRing A] [Algebra K A] (π : R →ₐ[K] A) (X : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) A) (s : Aˣ), FrameRing m π X s → ∀ A' : Subalgebra K A, (∀ t, π t ∈ A') → (∀ τ i j, X τ i j ∈ A') → (s : A) ∈ A' → ((s⁻¹ : Aˣ) : A) ∈ A' → (∀ τ, ∃ d ∈ A', d * (X τ).det = 1) → A' = ⊤ := by
  first | exact @GlobalTheory.frameRing_subalgebra_eq_top | exact GlobalTheory.frameRing_subalgebra_eq_top | (intros; apply GlobalTheory.frameRing_subalgebra_eq_top <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem _root_.GlobalTheory.T.existsUnique_glue_sections_principal_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (n : ℕ) (h : Fin n → S), Ideal.span (Set.range h) = ⊤ → ∀ s : ∀ i, LB.Sec (PPx (spMap (algebraMap S (Localization.Away (h i))) ≫ x)), (∀ i j (α : Localization.Away (h i) →+* Localization.Away (h i * h j)) (β : Localization.Away (h j) →+* Localization.Away (h i * h j)), α.comp (algebraMap S (Localization.Away (h i))) = (algebraMap S (Localization.Away (h i * h j))) → β.comp (algebraMap S (Localization.Away (h j))) = (algebraMap S (Localization.Away (h i * h j))) → ∀ t : LB.Sec (PPx (spMap (algebraMap S (Localization.Away (h i * h j))) ≫ x)), SecBC α 1 _ _ (s i) t → SecBC β 1 _ _ (s j) t) → ∃! s₀ : LB.Sec (PPx x), ∀ i, SecBC (algebraMap S (Localization.Away (h i))) 1 x _ s₀ (s i) := by
  first | exact @GlobalTheory.SecGlue.existsUnique_glue | exact GlobalTheory.SecGlue.existsUnique_glue | (intros; apply GlobalTheory.SecGlue.existsUnique_glue <;> assumption)
end

section

open IsLocalRing

namespace GlobalTheory

namespace CompleteJoin

variable {C : Type} [NormedField C] [IsUltrametricDist C]


omit [IsUltrametricDist C] in
theorem not_isUnit_of_norm_lt_one {R : Type*} [CommRing R] (f : R →+* C) (hf : ∀ a, ‖f a‖ ≤ 1)
    {a : R} (ha : ‖f a‖ < 1) : ¬ IsUnit a := by
  rintro ⟨u, rfl⟩
  have h1 : ‖f u‖ * ‖f (↑u⁻¹ : R)‖ = 1 := by
    rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
  have := mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) ha (hf (↑u⁻¹ : R))
  exact this.ne h1

theorem padicInt_ringHom_ext {p : ℕ} [Fact p.Prime] (hp : ‖(p : C)‖ < 1) (a b : ℤ_[p] →+* C)
    (ha : ∀ x, ‖a x‖ ≤ 1) (hb : ∀ x, ‖b x‖ ≤ 1) : a = b := by
  refine RingHom.ext fun x => ?_
  have key : ∀ k : ℕ, ‖a x - b x‖ ≤ ‖(p : C)‖ ^ k := fun k => by
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec k x)
    have hx : x = y * (p : ℤ_[p]) ^ k + (x.appr k : ℤ_[p]) := by rw [hy]; ring
    have : a x - b x = (a y - b y) * (p : C) ^ k := by
      conv_lhs => rw [hx]
      simp only [map_add (f := _), map_mul, map_pow, map_natCast]
      ring
    rw [this, norm_mul, norm_pow]
    refine mul_le_of_le_one_left (by positivity) ?_
    rw [sub_eq_add_neg]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha y) (by simpa using hb y))
  have := ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hp) key
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

theorem subring_of_finite {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] (S : Subring C) (φ : R →+* S) (hφ : φ.Finite)
    (h1 : ∀ a, ‖(φ a : C)‖ ≤ 1) (h2 : ∀ a ∈ maximalIdeal R, ‖(φ a : C)‖ < 1) :
    ∃ _ : IsLocalRing S, IsNoetherianRing S ∧ IsAdicComplete (maximalIdeal S) S ∧
      (∀ z : S, ‖(z : C)‖ ≤ 1) ∧ ∀ z : S, z ∈ maximalIdeal S ↔ ‖(z : C)‖ < 1 := by
  letI := φ.toAlgebra
  haveI : Module.Finite R S := hφ
  haveI : IsLocalRing S := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := R) S
  have hle : ∀ z : S, ‖(z : C)‖ ≤ 1 := fun z => by
    let v := NormedField.valuation (K := C)
    let ψ : R →+* v.integer := (S.subtype.comp φ).codRestrict _ fun a => h1 a
    have hz : IsIntegral R z := Algebra.IsIntegral.isIntegral z
    have hz' : IsIntegral v.integer (z : C) := hz.map_of_comp_eq ψ S.subtype rfl
    exact (Valuation.integer.integers v).isIntegral_iff_v_le_one.mp hz'
  refine ⟨inferInstance, IsNoetherianRing.of_finite R S,
    CompleteFiniteExtension.isAdicComplete_of_finite_local R S, hle, fun z => ⟨fun hz => ?_,
      fun hz => not_isUnit_of_norm_lt_one S.subtype hle hz⟩⟩
  let P : Ideal S :=
    { carrier := {z | ‖(z : C)‖ < 1}
      add_mem' := fun {a b} ha hb =>
        (IsUltrametricDist.norm_add_le_max (a : C) b).trans_lt (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        change ‖(c : C) * x‖ < 1
        rw [norm_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_right (hle c) (norm_nonneg _) hx }
  have hP : ∀ z : S, z ∈ P ↔ ‖(z : C)‖ < 1 := fun _ => Iff.rfl
  have hP1 : P ≠ ⊤ := by
    rw [Ideal.ne_top_iff_one, hP]
    simp
  haveI : P.IsPrime := ⟨hP1, fun {x y} hxy => by
    by_contra h
    rw [not_or, hP, hP, not_lt, not_lt] at h
    rw [hP, Subring.coe_mul, norm_mul] at hxy
    exact hxy.not_ge (one_le_mul_of_one_le_of_one_le h.1 h.2)⟩
  have hc : maximalIdeal R = P.comap (algebraMap R S) :=
    (maximalIdeal.isMaximal R).eq_of_le (Ideal.comap_ne_top _ hP1) fun a ha => h2 a ha
  have hm : P.IsMaximal := by
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R) P
    change (P.comap (algebraMap R S)).IsMaximal
    rw [← hc]
    exact maximalIdeal.isMaximal R
  rw [← eq_maximalIdeal hm] at hz
  exact hz


omit [IsUltrametricDist C] in
theorem exists_subring_finite {R V : Type} [CommRing R] [CommRing V] {p : ℕ} [Fact p.Prime]
    [Algebra ℤ_[p] V] [Module.Finite ℤ_[p] V] (f : R →+* C) (g : V →+* C) (φ : ℤ_[p] →+* R)
    (h : f.comp φ = g.comp (algebraMap ℤ_[p] V)) :
    ∃ (S : Subring C) (ψ : R →+* S), ψ.Finite ∧ (∀ a, (ψ a : C) = f a) ∧ ∀ a, g a ∈ S := by
  letI := f.toAlgebra
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ_[p]) (M := V)
  have hint : ∀ x : V, IsIntegral R (g x) := fun x =>
    (Algebra.IsIntegral.isIntegral (R := ℤ_[p]) x).map_of_comp_eq φ g h
  have hfin : Module.Finite R (Algebra.adjoin R (g '' s)) :=
    Algebra.finite_adjoin_of_finite_of_isIntegral (s.finite_toSet.image g)
      (by rintro _ ⟨x, -, rfl⟩; exact hint x)
  refine ⟨(Algebra.adjoin R (g '' s)).toSubring, algebraMap R (Algebra.adjoin R (g '' s)),
    (RingHom.finite_algebraMap (B := Algebra.adjoin R (g '' s))).2 hfin, fun _ => rfl, fun a => ?_⟩
  have ha : a ∈ Submodule.span ℤ_[p] (s : Set V) := hs ▸ Submodule.mem_top
  change g a ∈ Algebra.adjoin R (g '' s)
  induction ha using Submodule.span_induction with
  | mem x hx => exact Algebra.subset_adjoin ⟨x, hx, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx =>
    rw [Algebra.smul_def, map_mul]
    refine mul_mem ?_ hx
    have : g (algebraMap ℤ_[p] V c) = algebraMap R C (φ c) := (RingHom.congr_fun h c).symm
    rw [this]
    exact Subalgebra.algebraMap_mem _ _


omit [IsUltrametricDist C] in
theorem exists_normal_subring (S : Subring C)
    (h : Module.Finite S (integralClosure S (FractionRing S))) :
    ∃ (S' : Subring C) (ψ : S →+* S'), ψ.Finite ∧ (∀ a, (ψ a : C) = a) ∧ IsIntegrallyClosed S' := by
  let j : FractionRing S →ₐ[S] C :=
    IsFractionRing.liftAlgHom (g := Algebra.ofId S C) Subtype.val_injective
  let e := (integralClosure S (FractionRing S)).equivMapOfInjective j j.injective
  haveI : IsFractionRing (integralClosure S (FractionRing S)) (FractionRing S) :=
    integralClosure.isFractionRing_of_finite_extension (FractionRing S) (FractionRing S)
  haveI : IsIntegrallyClosed (integralClosure S (FractionRing S)) :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn (FractionRing S)).2 inferInstance
  exact ⟨((integralClosure S (FractionRing S)).map j).toSubring,
    algebraMap S ((integralClosure S (FractionRing S)).map j),
    (RingHom.finite_algebraMap (B := (integralClosure S (FractionRing S)).map j)).2
      (Module.Finite.equiv e.toLinearEquiv), fun _ => rfl,
    IsIntegrallyClosed.of_equiv e.toRingEquiv⟩

end CompleteJoin


open CompleteJoin in
theorem exists_complete_normal_subring_join : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (T : Formalism.L2.Pj.CDVR) (C : Type) [NormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] (f : R →+* C) (g : T.V →+* C) (p : ℕ), p.Prime → ‖(p : C)‖ < 1 → T.FinRes → IsNoetherianRing R → IsAdicComplete (maximalIdeal R) R → (∀ a, ‖f a‖ ≤ 1) → (∀ a ∈ maximalIdeal R, ‖f a‖ < 1) → (∀ a, ‖g a‖ ≤ 1) → (∀ a ∈ maximalIdeal T.V, ‖g a‖ < 1) → ∃ (S : Subring C) (_ : IsLocalRing S), IsNoetherianRing S ∧ IsIntegrallyClosed S ∧ IsAdicComplete (maximalIdeal S) S ∧ (∀ a, f a ∈ S) ∧ (∀ a, g a ∈ S) ∧ (∀ z : S, ‖(z : C)‖ ≤ 1) ∧ ∀ z : S, z ∈ maximalIdeal S ↔ ‖(z : C)‖ < 1 := by
  intro R _ _ _ _ T C _ _ _ _ f g _ _ _ hT hN hR hf1 hf2 hg1 hg2
  haveI : Finite (ResidueField T.V) := hT
  obtain ⟨q, hq, _, hfin⟩ := exists_padicInt_algebra_finite T.V
  have hqV : (q : T.V) ∈ maximalIdeal T.V := by
    have := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.map_maximalIdeal_le_maximal (R := ℤ_[q]) T.V _ (maximalIdeal.isMaximal _)
      (Ideal.mem_map_of_mem _ (show (q : ℤ_[q]) ∈ maximalIdeal _ from
        PadicInt.irreducible_p.not_isUnit))
    rwa [map_natCast] at this
  have hqC : ‖(q : C)‖ < 1 := by simpa using hg2 _ hqV
  have hqR : (q : R) ∈ maximalIdeal R := not_isUnit_of_norm_lt_one f hf1 (by simpa using hqC)
  obtain ⟨φ⟩ := nonempty_padicInt_ringHom_of_isAdicComplete (maximalIdeal R) q hqR
  obtain ⟨S₀, ψ₀, hψ₀, h₀, hg₀⟩ := exists_subring_finite f g φ
    (padicInt_ringHom_ext hqC _ _ (fun x => hf1 _) fun x => hg1 _)
  obtain ⟨_, hN₀, hc₀, -, hm₀⟩ := subring_of_finite S₀ ψ₀ hψ₀ (fun a => h₀ a ▸ hf1 a)
    fun a ha => h₀ a ▸ hf2 a ha
  obtain ⟨S, ψ, hψ, h, hS⟩ := exists_normal_subring S₀
    (GlobalTheory.T.integralClosure_finite_local_complete_mixedChar S₀ q hq.out ((hm₀ _).2 (by simpa using hqC)) hN₀ hc₀).1
  have h' : ∀ a, ((ψ.comp ψ₀ a : S) : C) = f a := fun a => (h _).trans (h₀ a)
  obtain ⟨_, hN₁, hc₁, hle, hm₁⟩ := subring_of_finite S (ψ.comp ψ₀) (hψ.comp hψ₀)
    (fun a => h' a ▸ hf1 a) fun a ha => h' a ▸ hf2 a ha
  exact ⟨S, inferInstance, hN₁, hS, hc₁, fun a => h' a ▸ (ψ.comp ψ₀ a).2,
    fun a => (show ((ψ ⟨g a, hg₀ a⟩ : S) : C) = g a from h _) ▸ (ψ ⟨g a, hg₀ a⟩).2, hle, hm₁⟩

end GlobalTheory
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenusLatCompare

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice
open scoped Pointwise

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

def toGen (Λ : Lat E n) : GenLat E n := ⟨Λ.L⟩

def IsLat (Λ : GenLat E n) : Prop := Λ.La.FG ∧ Submodule.span E (Λ.La : Set (Fin n → E)) = ⊤

def latEquiv : Lat E n ≃ {Λ : GenLat E n // IsLat Λ} where
  toFun Λ := ⟨toGen Λ, Λ.fg, Λ.span_top⟩
  invFun Λ := ⟨Λ.1.La, Λ.2.1, Λ.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [NumberField E] in
theorem span_smul_le_iff (k : ℕ) (A B : Submodule (𝓞 E) (Fin n → E)) :
    Ideal.span {(k : 𝓞 E)} • A ≤ B ↔ ∀ x ∈ A, k • x ∈ B := by
  rw [Submodule.smul_le]
  constructor
  · intro h x hx
    have := h k (Ideal.mem_span_singleton_self _) x hx
    rwa [Nat.cast_smul_eq_nsmul] at this
  · intro h r hr x hx
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    rw [mul_smul, Nat.cast_smul_eq_nsmul]
    exact B.smul_mem _ (h x hx)


theorem fg_of_smul_mem {A : Submodule (𝓞 E) (Fin n → E)} {o : 𝓞 E} (ho : o ≠ 0)
    (h : ∀ x ∈ A, o • x ∈ stdMod E n) : A.FG := by
  have hinj : Function.Injective (LinearMap.lsmul (𝓞 E) (Fin n → E) o) := by
    intro x y hxy
    funext j
    have := congrFun hxy j
    simp only [LinearMap.lsmul_apply, Pi.smul_apply, Algebra.smul_def] at this
    exact mul_left_cancel₀ (by simpa using ho) this
  refine Submodule.fg_of_fg_map_injective _ hinj ?_
  haveI : IsNoetherian (𝓞 E) (stdMod E n) := isNoetherian_of_fg_of_noetherian _ (Lat.std E n).fg
  refine Submodule.FG.of_le_of_isNoetherian (T := stdMod E n) ?_
  rintro _ ⟨x, hx, rfl⟩
  exact h x hx

variable [IsCMField E]

theorem eq_zero_of_sum_conj (v : Fin n → E) (h : ∑ j, IsCMField.complexConj E (v j) * v j = 0) : v = 0 := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h1 := congrArg φ h

  simp only [map_sum, map_mul, IsCMField.complexEmbedding_complexConj, map_zero,
  Complex.conj_mul'] at h1
  have h2 : ∑ j, ‖φ (v j)‖ ^ 2 = 0 := by exact_mod_cast h1
  rw [Finset.sum_eq_zero_iff_of_nonneg fun _ _ => by positivity] at h2
  funext j
  simpa using h2 j (Finset.mem_univ j)


omit [IsCMField E] in
private theorem exists_mul_mem_of_mem_span (A : Submodule (𝓞 E) (Fin n → E)) {x : Fin n → E}
    (hx : x ∈ Submodule.span E (A : Set (Fin n → E))) : ∃ o : 𝓞 E, o ≠ 0 ∧ o • x ∈ A := by
  first
  | exact @_root_.GlobalTheory.NonzeroSmulMemSpan.exists_ne_zero_smul_mem_of_mem_span
  | exact _root_.GlobalTheory.NonzeroSmulMemSpan.exists_ne_zero_smul_mem_of_mem_span
  | (apply _root_.GlobalTheory.NonzeroSmulMemSpan.exists_ne_zero_smul_mem_of_mem_span <;> assumption)
  | (intros; apply _root_.GlobalTheory.NonzeroSmulMemSpan.exists_ne_zero_smul_mem_of_mem_span <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NonzeroSmulMemSpan.exists_ne_zero_smul_mem_of_mem_span <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NonzeroSmulMemSpan.exists_ne_zero_smul_mem_of_mem_span ..)

private theorem span_eq_top_of_unimod (Λ : GenLat E n) (h : Λ.Unimod) :
    Submodule.span E (Λ.La : Set (Fin n → E)) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  let v : Fin n → E := fun j => IsCMField.complexConj E (f (Pi.single j 1))
  have hpair : ∀ w : Fin n → E, ∑ j, IsCMField.complexConj E (v j) * w j = f w := by
    intro w

    conv_rhs => rw [pi_eq_sum_univ' w, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
    simp only [v, IsCMField.complexConj_apply_apply]
  have hkill : ∀ w ∈ Λ.La, f w = 0 := fun w hw => hf (Submodule.subset_span hw)
  have hv : v ∈ Λ.La := (h v).2 fun w hw => by
    rw [hpair, hkill w hw]
    exact zero_mem _
  have hv0 : v = 0 := eq_zero_of_sum_conj v (by rw [hpair, hkill v hv])
  refine hf0 (LinearMap.ext fun w => ?_)
  rw [← hpair, hv0]
  simp

theorem isLat_of_unimod (Λ : GenLat E n) (h : Λ.Unimod) : IsLat Λ := by
  classical
  have hspan := span_eq_top_of_unimod Λ h
  refine ⟨?_, hspan⟩
  choose o ho0 ho using fun j : Fin n =>
    exists_mul_mem_of_mem_span Λ.La (x := Pi.single j 1) (hspan ▸ Submodule.mem_top)
  have hd : ∀ j, (∏ i, o i) • (Pi.single j 1 : Fin n → E) ∈ Λ.La := fun j => by
    rw [← Finset.prod_erase_mul _ o (Finset.mem_univ j), mul_smul]
    exact Λ.La.smul_mem _ (ho j)
  have hd0 : ∏ i, o i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => ho0 i
  refine fg_of_smul_mem (o := IsCMField.ringOfIntegersComplexConj E (∏ i, o i))
    ((map_ne_zero_iff _ (IsCMField.ringOfIntegersComplexConj E).injective).2 hd0) fun x hx => ?_
  refine mem_stdMod.2 fun j => ?_
  obtain ⟨a, ha⟩ := (h _).1 (hd j) x hx
  refine ⟨a, Eq.trans ha ?_⟩
  rw [Finset.sum_eq_single j (fun i _ hi => by simp [Pi.single_eq_of_ne hi]) (by simp)]
  rw [Pi.smul_apply, Pi.smul_apply, Pi.single_eq_same, Algebra.smul_def, Algebra.smul_def, mul_one]
  congr 1

section Poly

variable {H : Host E} (Dw : Datum H) {l : Level H} (c : Coeff l)

end Poly

end GlobalTheory.GenusLatCompare
end
end

section

noncomputable section

namespace GlobalTheory.ValuativeExtension

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem valuation_extension :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (oV : O →+* V) (fK : c.F →+* K) (y : Sp K ⟶ Xo.XF c), (algebraMap V K).comp oV = fK.comp β → y ≫ pullback.snd _ _ = spMap fK → (∃! yt : Sp V ⟶ Y.X, yt ≫ Y.s = spMap oV ∧ spMap (algebraMap V K) ≫ yt = y ≫ Y.j) ∧ ∀ yt : Sp V ⟶ Y.X, ∃ G : SAB H (Sp V), Nonempty (SABMap G Y.t yt) := by
  intro E _ _ _ H D l Xo c O _ β Y V K _ _ _ _ _ _ oV fK y ho hy
  obtain ⟨h1, h2, -⟩ := GlobalTheory.ModelPoints.model_points_charts E H D l Xo c O β Y
  exact ⟨h1 V K oV fK y ho hy, fun yt => h2 _ yt⟩

end GlobalTheory.ValuativeExtension
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem sab_group_iso_of_generic
    (hx : ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K]
      [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' →
      ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G',
      IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f)
    (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (T K : Type) [CommRing T] [IsDomain T]
    [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (t t' : SAB H (Sp T)) (tK : SAB H (Sp K))
    (m : SABMap tK t (spMap (algebraMap T K))) (m' : SABMap tK t' (spMap (algebraMap T K))) :
    ∃ ψ : t.G ≅ t'.G, IsMonHom ψ.hom ∧ m.φ ≫ ψ.hom.left = m'.φ ∧
      ∀ a, t.act.act a ≫ ψ.hom = ψ.hom ≫ t'.act.act a := by
  have inj : ∀ (s s' : SAB H (Sp T)) (F F' : s.G ⟶ s'.G), IsMonHom F → IsMonHom F' →
      (Over.pullback (spMap (algebraMap T K))).map F = (Over.pullback (spMap (algebraMap T K))).map F' → F = F' := by
    intro s s' F F' hF hF' h
    exact (hx T K s.G s'.G s.semi s'.semi _ inferInstance).unique ⟨hF, rfl⟩ ⟨hF', h.symm⟩
  have A : ∀ {X Y : Over (Sp T)} (a : X ⟶ Y),
      ((Over.pullback (spMap (algebraMap T K))).map a).left ≫ pullback.fst Y.hom _ =
        pullback.fst X.hom _ ≫ a.left := fun a => pullback.lift_fst _ _ _
  obtain ⟨e, he, hφ⟩ := grpPullback_iso m.cart (isGrpPullback_pullback t.G _)
  obtain ⟨e', he', hφ'⟩ := grpPullback_iso m'.cart (isGrpPullback_pullback t'.G _)
  obtain ⟨F, ⟨hF, hFf⟩, -⟩ := hx T K t.G t'.G t.semi t'.semi (e.inv ≫ e'.hom) inferInstance
  obtain ⟨F', ⟨hF', hFf'⟩, -⟩ := hx T K t'.G t.G t'.semi t.semi (e'.inv ≫ e.hom) inferInstance
  have key : m.cm.F ≫ F.left = m'.cm.F := by
    rw [← hφ, Category.assoc, ← A, hFf, ← Category.assoc, ← Over.comp_left, e.hom_inv_id_assoc, hφ']
  refine ⟨⟨F, F', inj _ _ _ _ inferInstance inferInstance ?_, inj _ _ _ _ inferInstance inferInstance ?_⟩, hF, key,
    fun a => ?_⟩
  · rw [Functor.map_comp, hFf, hFf']; simp
  · rw [Functor.map_comp, hFf, hFf']; simp
  · show t.act.act a ≫ F = F ≫ t'.act.act a
    have := t.act.hom a
    have := t'.act.hom a
    refine inj _ _ _ _ inferInstance inferInstance ?_
    rw [← cancel_epi e.hom]
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp only [Over.comp_left, Category.assoc, A]
      rw [reassoc_of% hφ, reassoc_of% hφ, ← reassoc_of% m.act a, reassoc_of% key, key, m'.act]
    · exact (Over.w _).trans (Over.w _).symm

end GlobalTheory
end

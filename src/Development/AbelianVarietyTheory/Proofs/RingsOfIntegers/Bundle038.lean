module

public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle015
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle026
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
import Mathlib.Algebra.AffineMonoid.Basic
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle025
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle045
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle004
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle002

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory

namespace IsotropicPrimary

theorem exists_primary_complement (Z : Type) [CommGroup Z] [Finite Z] (ℓ : ℕ) (hℓ : ℓ.Prime) :
    ∃ P Q : Subgroup Z, (∀ u, u ∈ P ↔ ∃ j : ℕ, u ^ (ℓ ^ j) = 1) ∧ Nat.Coprime (Nat.card Q) ℓ ∧
      (Function.Bijective fun y : P × Q => (y.1 : Z) * (y.2 : Z)) ∧
      Nat.card P = ℓ ^ (Nat.card Z).factorization ℓ := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨S⟩ : Nonempty (Sylow ℓ Z) := inferInstance
  haveI : (S : Subgroup Z).Normal := Subgroup.normal_of_isMulCommutative _
  obtain ⟨Q, hQ⟩ := Subgroup.exists_right_complement'_of_coprime (N := (S : Subgroup Z)) S.card_coprime_index
  refine ⟨S, Q, fun u => ⟨fun hu => ?_, fun hu => ?_⟩, ?_, hQ, S.card_eq_multiplicity⟩
  · obtain ⟨k, hk⟩ := S.isPGroup' ⟨u, hu⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  · obtain ⟨j, hj⟩ := hu
    have hp : IsPGroup ℓ (Subgroup.zpowers u) :=
      IsPGroup.of_card_dvd_pow (n := j) (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hj)
    obtain ⟨T, hT⟩ := hp.exists_le_sylow
    letI := Sylow.unique_of_normal S ‹_›
    have hTS : T = S := Subsingleton.elim _ _
    subst hTS
    exact hT (Subgroup.mem_zpowers u)
  · rw [← hQ.symm.index_eq_card]
    exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hℓ).2 S.not_dvd_index)

theorem epi_spMap_of_fields {K k : Type} [Field K] [Field k] (β : K →+* k) : Epi (spMap β) := by
  letI : Algebra K k := β.toAlgebra
  have hff : (CommRingCat.ofHom β).hom.FaithfullyFlat := by
    change Module.FaithfullyFlat K k
    infer_instance
  obtain ⟨h1, h2⟩ := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom β)).2 hff
  exact Flat.epi_of_flat_of_surjective _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

def zhSubgroup (Xo : Moduli Dw l) {n : ℕ} (Λ : GenLat E n) (N : ℕ) (hN : 0 < N) (T : Over Xo.X) :
    Subgroup (Fin n → (T ⟶ Xo.univ.t.G)) :=
  have hone : InZh Xo Λ N (1 : Fin n → (T ⟶ Xo.univ.t.G)) := by
    refine ⟨fun b => one_pow _, fun mu _ cm _ i => List.prod_eq_one fun x hx => ?_⟩
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
    have := Xo.univ.t.act.hom (cm i j)
    exact MonObj.one_comp _
  have hpow : ∀ (a : Fin n → (T ⟶ Xo.univ.t.G)), InZh Xo Λ N a → ∀ k : ℕ, InZh Xo Λ N (a ^ k) := by
    intro a ha k
    induction k with
    | zero => rw [pow_zero]; exact hone
    | succ k ih => rw [pow_succ]; exact ZhStable.inZh_mul Xo Λ N _ _ ih ha
  { carrier := {a | InZh Xo Λ N a}
    one_mem' := hone
    mul_mem' := fun {a a'} ha ha' => ZhStable.inZh_mul Xo Λ N a a' ha ha'
    inv_mem' := fun {a} ha => by
      have h1 : a ^ (N ^ 2) = 1 := funext ha.1
      have h2 : a⁻¹ = a ^ (N ^ 2 - 1) := by
        refine inv_eq_of_mul_eq_one_left ?_
        rw [← pow_succ, Nat.sub_add_cancel (pow_pos hN 2), h1]
      change InZh Xo Λ N a⁻¹
      rw [h2]
      exact hpow a ha _ }

theorem enumeration_bijective (Xo : Moduli Dw l) {K : Type} [Field K] (x : Sp K ⟶ Xo.X)
    {n : ℕ} (Λ : GenLat E n) {N : ℕ} (hΛ : Λ.Unimod) (hN : 0 < N)
    (hle : Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La)
    (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo x ⟶ Xo.univ.t.G)) (hz : ∀ i, InZh Xo Λ N (z i))
    (hinj : GeoInj Xo x z) : Function.Injective z ∧ ∀ a, InZh Xo Λ N a → ∃ i, z i = a := by
  refine ⟨fun i j hij => ?_, fun a ha => ?_⟩
  · let g : ptO Xo (spMap (RingHom.id K) ≫ x) ⟶ ptO Xo x := Over.homMk (spMap (RingHom.id K)) rfl
    refine hinj K (RingHom.id K) g rfl ?_
    show (fun b => g ≫ z i b) = fun b => g ≫ z j b
    rw [hij]
  · let ψ : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
    let g : ptO Xo (spMap ψ ≫ x) ⟶ ptO Xo x := Over.homMk (spMap ψ) rfl
    have hw : ∀ i, InZh Xo Λ N (fun b => g ≫ z i b) := fun i => ZhStable.inZh_comp Xo Λ N g (z i) (hz i)
    obtain ⟨i, hi⟩ := IsotropicEnum.exists_eq_of_isAlgClosed Xo (spMap ψ ≫ x) Λ hΛ hN hle
      (fun i b => g ≫ z i b) hw (hinj (AlgebraicClosure K) ψ g rfl) (fun b => g ≫ a b)
      (ZhStable.inZh_comp Xo Λ N g a ha)
    refine ⟨i, funext fun b => ?_⟩
    haveI := epi_spMap_of_fields ψ
    have hb := congrArg CommaMorphism.left (congrFun hi b)
    simp only [Over.comp_left] at hb
    exact Over.OverMorphism.ext ((cancel_epi (spMap ψ)).1 hb)

end IsotropicPrimary


open IsotropicPrimary in
theorem isotropic_primary_decomposition :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K : Type) [Field K] (x : Sp K ⟶ Xo.X) (n : ℕ) (Λ : GenLat E n) (N M ℓ : ℕ), Λ.Unimod → Λ.LevOK N M → ℓ.Prime → ∀ z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo x ⟶ Xo.univ.t.G), (∀ i, InZh Xo Λ N (z i)) → GeoInj Xo x z → ∃ (J J' : Type) (_ : Fintype J) (_ : Fintype J') (a : J → Fin n → (ptO Xo x ⟶ Xo.univ.t.G)) (a' : J' → Fin n → (ptO Xo x ⟶ Xo.univ.t.G)) (σ : J × J' ≃ Fin (Λ.zCard N (Dw.p + Dw.q))), Function.Injective a ∧ (∀ u, (∃ i, a i = u) ↔ (InZh Xo Λ N u ∧ ∀ b, ∃ j : ℕ, u b ^ (ℓ ^ j) = 1)) ∧ (∃ m : ℕ, Nat.Coprime m ℓ ∧ ∀ i b, a' i b ^ m = 1 ∧ a' i b ^ (N ^ 2) = 1) ∧ (∀ i i' b, z (σ (i, i')) b = a i b * a' i' b) ∧ Fintype.card J = ℓ ^ (Λ.zCard N (Dw.p + Dw.q)).factorization ℓ := by
  intro E _ _ _ H Dw l Xo K _ x n Λ N M ℓ hΛ hlev hℓ z hz hinj
  have hN : 0 < N := hlev.1.pos
  have hle : Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La := hlev.2.2.trans inf_le_left
  obtain ⟨hzinj, hzon⟩ := enumeration_bijective Xo x Λ hΛ hN hle z hz hinj
  let e : Fin (Λ.zCard N (Dw.p + Dw.q)) → zhSubgroup Xo Λ N hN (ptO Xo x) := fun i => ⟨z i, hz i⟩
  have he : Function.Bijective e :=
    ⟨fun i j h => hzinj (congrArg Subtype.val h), fun u => by
      obtain ⟨i, hi⟩ := hzon u.1 u.2
      exact ⟨i, Subtype.ext hi⟩⟩
  haveI : Finite (zhSubgroup Xo Λ N hN (ptO Xo x)) := Finite.of_surjective e he.2
  obtain ⟨P, Q, hP, hQ, hPQ, hcard⟩ := exists_primary_complement (zhSubgroup Xo Λ N hN (ptO Xo x)) ℓ hℓ
  refine ⟨P, Q, Fintype.ofFinite _, Fintype.ofFinite _, fun p => ((p : zhSubgroup Xo Λ N hN (ptO Xo x)) : Fin n → _),
    fun q => ((q : zhSubgroup Xo Λ N hN (ptO Xo x)) : Fin n → _),
    (Equiv.ofBijective _ hPQ).trans (Equiv.ofBijective e he).symm, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun p p' h => Subtype.ext (Subtype.ext h)
  · intro u
    constructor
    · rintro ⟨p, rfl⟩
      refine ⟨(p : zhSubgroup Xo Λ N hN (ptO Xo x)).2, fun b => ?_⟩
      obtain ⟨j, hj⟩ := (hP _).1 p.2
      refine ⟨j, ?_⟩
      have := congrArg (fun w : zhSubgroup Xo Λ N hN (ptO Xo x) => w.1 b) hj
      simpa using this
    · rintro ⟨hu, hpow⟩
      choose j hj using hpow
      refine ⟨⟨⟨u, hu⟩, (hP _).2 ⟨∑ b, j b, Subtype.ext (funext fun b => ?_)⟩⟩, rfl⟩
      obtain ⟨c, hc⟩ : ℓ ^ j b ∣ ℓ ^ (∑ b, j b) :=
        pow_dvd_pow ℓ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ b))
      simp only [Subgroup.coe_pow, Pi.pow_apply, Subgroup.coe_one, Pi.one_apply]
      rw [hc, pow_mul, hj b, one_pow]
  · refine ⟨Nat.card Q, hQ, fun i b => ⟨?_, ((i : zhSubgroup Xo Λ N hN (ptO Xo x)).2 : InZh Xo Λ N _).1 b⟩⟩
    have := congrArg (fun w : Q => (w : zhSubgroup Xo Λ N hN (ptO Xo x)).1 b) (pow_card_eq_one' (G := Q) (x := i))
    simp only [Subgroup.coe_pow, Pi.pow_apply, Subgroup.coe_one, Pi.one_apply] at this
    exact this
  · intro i i' b
    have h1 : e ((Equiv.ofBijective e he).symm ((i : zhSubgroup Xo Λ N hN (ptO Xo x)) * (i' : zhSubgroup Xo Λ N hN (ptO Xo x)))) =
        (i : zhSubgroup Xo Λ N hN (ptO Xo x)) * (i' : zhSubgroup Xo Λ N hN (ptO Xo x)) :=
      Equiv.ofBijective_apply_symm_apply e he _
    simp only [Equiv.trans_apply, Equiv.ofBijective_apply]
    exact congrFun (congrArg Subtype.val h1) b
  · rw [@Fintype.card_eq_nat_card P (Fintype.ofFinite P), hcard, ← Nat.card_eq_of_bijective e he, Nat.card_fin]

end GlobalTheory
end
end

section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.TorsFac

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem act_nat {S : Scheme.{0}} (t : SAB H S) {T : Over S} (x : T ⟶ t.G) (n : ℕ) :
    x ≫ t.act.act (n : 𝓞 E) = x ^ n := by
  have h0 : t.act.act 0 = 1 := by
    have h := t.act.add 0 0
    rw [add_zero] at h
    have h2 := congrArg (fun f => (t.act.act 0)⁻¹ * f) h
    simp only [inv_mul_cancel, inv_mul_cancel_left] at h2
    exact h2.symm
  induction n with
  | zero => rw [Nat.cast_zero, pow_zero, h0, MonObj.comp_one]
  | succ n ih => rw [Nat.cast_succ, t.act.add, MonObj.comp_mul, ih, t.act.one, Category.comp_id, pow_succ]

theorem act_pow {S : Scheme.{0}} (t : SAB H S) {T : Over S} (x : T ⟶ t.G) (b : 𝓞 E) (n : ℕ) :
    (x ≫ t.act.act b) ^ n = x ≫ t.act.act (b * n) := by
  rw [t.act.mul, ← Category.assoc, act_nat]

theorem bar_bar (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply RingOfIntegers.ext
  rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]

theorem M_mem (l : Level H) : (l.M : 𝓞 E) ∈ l.Mb := by
  have h : (l.M : 𝓞 E) ∈ Ideal.span {(l.M : 𝓞 E)} := Ideal.mem_span_singleton_self _
  rw [← l.prod] at h
  exact (Ideal.mul_le_left : l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb) h

theorem kill {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) {T : Over Xo.X} (t : T ⟶ Xo.univ.t.G) (N : ℕ)
    (h : KilledBy Xo l.Mb (t ^ N)) (a : 𝓞 E) (ha : a ∈ l.Mb) : t ≫ Xo.univ.t.act.act (N * a) = 1 := by
  rw [Xo.univ.t.act.mul, ← Category.assoc, act_nat]
  exact h a ha

omit [IsCMField E] in
theorem dvd_of_cast_dvd {p m : ℕ} (hp : p.Prime) (h : (p : 𝓞 E) ∣ (m : 𝓞 E)) : p ∣ m := by
  have h2 := map_dvd (Algebra.norm ℤ) h
  have e1 : (p : 𝓞 E) = algebraMap ℤ (𝓞 E) (p : ℤ) := by simp
  have e2 : (m : 𝓞 E) = algebraMap ℤ (𝓞 E) (m : ℤ) := by simp
  rw [e1, e2, Algebra.norm_algebraMap, Algebra.norm_algebraMap] at h2
  have hr : Module.finrank ℤ (𝓞 E) ≠ 0 := Module.finrank_pos.ne'
  rw [IsIntegrallyClosed.pow_dvd_pow_iff hr] at h2
  exact Int.natCast_dvd_natCast.mp h2

theorem split_once {M ℓ e n' : ℕ} (hp : ℓ.Prime) (h1 : ℓ ∣ M) (h2 : ¬ ℓ ^ 2 ∣ M) (h : M ∣ ℓ ^ e * n') :
    ∃ m k, M = ℓ * m ∧ n' = m * k := by
  obtain ⟨m, rfl⟩ := h1
  have hm : ¬ ℓ ∣ m := fun ⟨c, hc⟩ => h2 ⟨c, by rw [hc]; ring⟩
  have hcop : Nat.Coprime m (ℓ ^ e) :=
    Nat.Coprime.pow_right e ((Nat.Prime.coprime_iff_not_dvd hp).2 hm).symm
  obtain ⟨k, hk⟩ := hcop.dvd_of_dvd_mul_left ((Dvd.intro_left ℓ rfl).trans h)
  exact ⟨m, k, rfl, hk⟩

private theorem sq_lemma' {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) {T : Over Xo.X} (t : T ⟶ Xo.univ.t.G)
    {N : ℕ} (hMN : l.M ∣ N) (hk : KilledBy Xo l.Mb (t ^ N)) : t ^ (N ^ 2) = 1 := by
  have hN : (N : 𝓞 E) ∈ l.Mb := by
    obtain ⟨q, rfl⟩ := hMN
    push_cast
    exact Ideal.mul_mem_right _ _ (M_mem l)
  rw [sq, pow_mul, ← act_nat Xo.univ.t (t ^ N) N]
  exact hk _ hN

private theorem natCast_mem_level_of_dvd {l : Level H} {k : ℕ} (h : l.M ∣ k) : (k : 𝓞 E) ∈ l.Mb := by
  obtain ⟨q, rfl⟩ := h
  push_cast
  exact Ideal.mul_mem_right _ _ (M_mem l)

private theorem dvd_lemma_3 {M ℓ e n' : ℕ} (hp : ℓ.Prime) (h2 : ¬ ℓ ^ 2 ∣ M) (h : M ∣ ℓ ^ e * n') :
    M ∣ ℓ * n' := by
  by_cases h1 : ℓ ∣ M
  · obtain ⟨m, k, rfl, rfl⟩ := split_once hp h1 h2 h
    exact ⟨k, by ring⟩
  · have hc : Nat.Coprime M (ℓ ^ e) :=
      Nat.Coprime.pow_right e ((Nat.Prime.coprime_iff_not_dvd hp).2 h1).symm
    exact Dvd.dvd.mul_left (hc.dvd_of_dvd_mul_left h) ℓ

theorem factorisation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (N ℓ : ℕ), Odd N → l.M ∣ N → ℓ.Prime → (¬ ℓ ∣ l.M → ∃ (n' j : ℕ), Nat.Coprime n' ℓ ∧ N = ℓ ^ j * n' ∧ ∀ (T : Over Xo.X) (t : T ⟶ Xo.univ.t.G), KilledBy Xo l.Mb (t ^ N) → (∃ i : ℕ, KilledBy Xo (l.Mb ^ i) t) → t ^ (N ^ 2) = 1 ∧ (t ≫ Xo.univ.t.act.act ((ℓ : 𝓞 E) ^ j)) ^ (n' ^ 2 * 1) = 1 ∧ ∃ i : ℕ, t ^ (l.M ^ i) = 1) ∧ ∀ (α : 𝓞 E) (A : ℕ), α * H.bar α = (A : 𝓞 E) → ¬ ℓ ^ 2 ∣ l.M → ((A = ℓ ∧ l.Mb ≤ Ideal.span {H.bar α}) ∨ (α = (ℓ : 𝓞 E) ∧ ℓ ∣ l.M)) → ∃ (n' Bn j : ℕ) (β : 𝓞 E), Nat.Coprime n' ℓ ∧ (N : 𝓞 E) = β * α * n' ∧ β * H.bar β = (Bn : 𝓞 E) ∧ A * Bn = ℓ ^ j ∧ ∀ (T : Over Xo.X) (t : T ⟶ Xo.univ.t.G), KilledBy Xo l.Mb (t ^ N) → (∃ i : ℕ, KilledBy Xo (l.Mb ^ i) t) → t ^ (N ^ 2) = 1 ∧ (t ≫ Xo.univ.t.act.act β) ^ (n' ^ 2 * A) = 1 := by
  intro E _ _ _ H Dw l Xo N ℓ hN hMN hp
  have hN0 : N ≠ 0 := hN.pos.ne'
  refine ⟨fun hℓM => ?_, fun α A hA h2 hc => ?_⟩
  · obtain ⟨j, n', hn', hNe⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN0 ℓ hp.one_lt.ne'
    have hcop : Nat.Coprime n' ℓ := ((Nat.Prime.coprime_iff_not_dvd hp).2 hn').symm
    have hMn : l.M ∣ n' := by
      have hc : Nat.Coprime l.M (ℓ ^ j) :=
        Nat.Coprime.pow_right j ((Nat.Prime.coprime_iff_not_dvd hp).2 hℓM).symm
      exact hc.dvd_of_dvd_mul_left (hNe ▸ hMN)
    refine ⟨n', j, hcop, hNe, fun T t hk hi => ⟨sq_lemma' Xo t hMN hk, ?_, ?_⟩⟩
    · rw [act_pow]
      have he : (ℓ : 𝓞 E) ^ j * ((n' ^ 2 * 1 : ℕ) : 𝓞 E) = (N : 𝓞 E) * (n' : 𝓞 E) := by
        rw [hNe]; push_cast; ring
      rw [he]
      exact kill Xo t N hk _ (natCast_mem_level_of_dvd hMn)
    · obtain ⟨i, hi⟩ := hi
      refine ⟨i, ?_⟩
      rw [← act_nat Xo.univ.t t, Nat.cast_pow]
      exact hi _ (Ideal.pow_mem_pow (M_mem l) i)
  · have hℓN : ℓ ∣ N := by
      rcases hc with ⟨hA', hle⟩ | ⟨_, hℓM⟩
      · have hbM : H.bar α ∣ (l.M : 𝓞 E) := Ideal.mem_span_singleton.mp (hle (M_mem l))
        have haM : α ∣ (l.M : 𝓞 E) := by
          have h3 := map_dvd H.bar hbM
          rwa [bar_bar, map_natCast] at h3
        have hl : (ℓ : 𝓞 E) = α * H.bar α := by rw [hA, hA']
        have h4 : (ℓ : 𝓞 E) ∣ ((N ^ 2 : ℕ) : 𝓞 E) := by
          obtain ⟨q, rfl⟩ := hMN
          rw [hl]
          exact (mul_dvd_mul haM hbM).trans ⟨(q : 𝓞 E) ^ 2, by push_cast; ring⟩
        exact hp.dvd_of_dvd_pow (dvd_of_cast_dvd hp h4)
      · exact hℓM.trans hMN
    obtain ⟨N', hN'⟩ := hℓN
    have hN'0 : N' ≠ 0 := right_ne_zero_of_mul (hN' ▸ hN0)
    obtain ⟨e, n', hn', hN'e⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN'0 ℓ hp.one_lt.ne'
    have hNe : N = ℓ ^ (e + 1) * n' := by rw [hN', hN'e]; ring
    have hcop : Nat.Coprime n' ℓ := ((Nat.Prime.coprime_iff_not_dvd hp).2 hn').symm
    have hMl : l.M ∣ ℓ * n' := dvd_lemma_3 hp h2 (by rw [← hNe]; exact hMN)
    have hmem : ((ℓ * n' : ℕ) : 𝓞 E) ∈ l.Mb := natCast_mem_level_of_dvd hMl
    rcases hc with ⟨hA', hle⟩ | ⟨hα, _⟩
    · have hl : (ℓ : 𝓞 E) = α * H.bar α := by rw [hA, hA']
      refine ⟨n', ℓ ^ (2 * e + 1), 2 * e + 2, (ℓ : 𝓞 E) ^ e * H.bar α, hcop, ?_, ?_, ?_,
        fun T t hk _ => ⟨sq_lemma' Xo t hMN hk, ?_⟩⟩
      · rw [hNe]; push_cast; rw [hl]; ring
      · rw [map_mul, map_pow, map_natCast, bar_bar]; push_cast; rw [hl]; ring
      · rw [hA']; ring
      · have htop : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
          rw [l.coprime]; exact Submodule.mem_top
        obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp htop
        have hy' : y ∈ Ideal.span {α} := by
          have h5 := Ideal.map_mono (f := (H.bar : 𝓞 E →+* 𝓞 E)) hle hy
          simpa [Ideal.map_span, bar_bar] using h5
        obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp hy'
        have hb : (n' : 𝓞 E) * H.bar α ∈ l.Mb := by
          have h6 : (n' : 𝓞 E) * H.bar α = x * ((n' : 𝓞 E) * H.bar α) + z * ((ℓ * n' : ℕ) : 𝓞 E) := by
            push_cast
            linear_combination (-((n' : 𝓞 E) * H.bar α)) * hxy + (-((n' : 𝓞 E) * H.bar α)) * hz +
              (-(z * (n' : 𝓞 E))) * hl
          rw [h6]
          exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hx) (Ideal.mul_mem_left _ z hmem)
        rw [act_pow]
        have he : (ℓ : 𝓞 E) ^ e * H.bar α * ((n' ^ 2 * A : ℕ) : 𝓞 E) =
            (N : 𝓞 E) * ((n' : 𝓞 E) * H.bar α) := by
          rw [hNe, hA']; push_cast; ring
        rw [he]
        exact kill Xo t N hk _ hb
    · have hA2 : A = ℓ ^ 2 := by
        have h7 : ((A : ℕ) : 𝓞 E) = ((ℓ ^ 2 : ℕ) : 𝓞 E) := by
          rw [← hA, hα, map_natCast]; push_cast; ring
        exact Nat.cast_injective h7
      refine ⟨n', ℓ ^ (2 * e), 2 * e + 2, (ℓ : 𝓞 E) ^ e, hcop, ?_, ?_, ?_,
        fun T t hk _ => ⟨sq_lemma' Xo t hMN hk, ?_⟩⟩
      · rw [hNe, hα]; push_cast; ring
      · rw [map_pow, map_natCast]; push_cast; ring
      · rw [hA2]; ring
      · rw [act_pow, hA2]
        have he : (ℓ : 𝓞 E) ^ e * ((n' ^ 2 * ℓ ^ 2 : ℕ) : 𝓞 E) = (N : 𝓞 E) * ((ℓ * n' : ℕ) : 𝓞 E) := by
          rw [hNe]; push_cast; ring
        rw [he]
        exact kill Xo t N hk _ hmem

end GlobalTheory.TorsFac
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open Formalism.BasicNotions Formalism.MainNotions IsDedekindDomain
open scoped Pointwise

namespace GlobalTheory.PlaceInt

theorem host_bar_eq_smul (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (x : 𝓞 D.host.E) :
    H.bar x = D.host.conj • x := by
  apply RingOfIntegers.ext
  let φ : D.host.E →+* ℂ := Classical.choice inferInstance
  apply φ.injective
  rw [H.bar_eq, IsCMField.complexEmbedding_complexConj]
  exact (D.host.conjE_apply φ x).symm

theorem host_galois_discr_moves : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E), IsGalois ℚ D.host.E ∧ Module.finrank ℚ D.host.E = 4 * D.R.ord ∧ (∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr D.host.E → p ∣ D.host.condN) ∧ ∀ p ∈ D.host.condN.primeFactors, p.Prime ∧ ∀ 𝔭 : Ideal (𝓞 D.host.E), 𝔭.IsPrime → (p : 𝓞 D.host.E) ∈ 𝔭 → ∃ x ∈ 𝔭, H.bar x ∉ 𝔭 := by
  intro D H
  refine ⟨D.host.galois, D.host.der.finrank_E, D.host.der.discr_primes.1, ?_⟩
  · intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    refine ⟨hpp, fun P hP hmem => ?_⟩
    by_contra hall
    push Not at hall
    have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hpp).irreducible
    have hlo : P.LiesOver (Ideal.span {(p : ℤ)}) := by
      refine ⟨hmax.eq_of_le (Ideal.IsPrime.under ℤ P).ne_top ?_⟩
      rw [Ideal.span_le, Set.singleton_subset_iff]
      show algebraMap ℤ (𝓞 D.host.E) (p : ℤ) ∈ P
      rw [map_natCast]
      exact hmem
    have hbb : ∀ x : 𝓞 D.host.E, H.bar (H.bar x) = x := fun x => by
      apply RingOfIntegers.ext
      rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]
    refine D.host.der.decompConj p hpp (Nat.dvd_of_mem_primeFactors hp) P ?_
    rw [MulAction.mem_stabilizer_iff]
    ext x
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    have hinv : (D.host.conj)⁻¹ • x = H.bar x := by
      rw [inv_smul_eq_iff, ← host_bar_eq_smul D H, hbb]
    rw [hinv]
    refine ⟨fun h => ?_, hall x⟩
    have := hall _ h
    rwa [hbb] at this

end GlobalTheory.PlaceInt
end

section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

theorem GlobalTheory.PlaceInt.card_fun_levQ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (n : ℕ), Nat.card (Fin n → LevQ Dw l) = l.M ^ (Module.finrank ℚ E / 2 * (Dw.p + Dw.q) * n) := by
  intro E _ _ _ H Dw l n
  rw [Nat.card_fun, (GlobalTheory.card_levQ E H Dw l).2, Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_mul]
  rfl
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

theorem _root_.GlobalTheory.T.exists_finite_basis_powerSeries_subst_finite_colength : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (σ : Type) [Fintype σ] (φ : σ → MvPowerSeries σ V), (∀ j, MvPowerSeries.constantCoeff (φ j) = 0) → (∃ M : ℕ, Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ (ResidueField V))) ^ M ≤ Ideal.span (Set.range fun j => MvPowerSeries.map (residue V) (φ j))) → ∃ (r : ℕ) (b : Fin r → MvPowerSeries σ V), Module.finrank V (MvPowerSeries σ V ⧸ Ideal.span (Set.range φ)) = r ∧ ∀ f, ∃! cf : Fin r → MvPowerSeries σ V, f = ∑ i, MvPowerSeries.subst φ (cf i) * b i := by
  first | exact @GlobalTheory.FiniteColength.exists_basis_subst_finrank_quotient | exact GlobalTheory.FiniteColength.exists_basis_subst_finrank_quotient | (intros; apply GlobalTheory.FiniteColength.exists_basis_subst_finrank_quotient <;> assumption)
end

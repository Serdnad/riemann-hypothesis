module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumLatticePairsIndexRpowLe
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle136
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle139
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.Flat.Localization

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct

namespace GlobalTheory

theorem eq_of_pow_pred_eq_of_sub_one_mem {R : Type*} [CommRing R] [IsDomain R] (I : Ideal R)
    (hI : I ≠ ⊤) (l : ℕ) (hl : 0 < l) (hlI : (l : R) ∈ I) (a b : R)
    (hab : a ^ (l - 1) = b ^ (l - 1)) (ha : a - 1 ∈ I) (hb : b - 1 ∈ I) : a = b := by
  by_contra hne
  have h := geom_sum₂_mul a b (l - 1)
  rw [hab, sub_self] at h
  have hs := (mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hne)
  have ha' : Ideal.Quotient.mk I a = 1 := by
    rw [← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]; exact ha
  have hb' : Ideal.Quotient.mk I b = 1 := by
    rw [← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]; exact hb
  have hl' : (l : R ⧸ I) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]; exact hlI
  have h2 := congrArg (Ideal.Quotient.mk I) hs

  simp only [map_sum, map_mul, map_pow, ha', hb', one_pow, mul_one, Finset.sum_const,
  Finset.card_range, nsmul_eq_mul, map_zero] at h2
  rw [Nat.cast_sub hl, hl', Nat.cast_one, zero_sub, neg_eq_zero] at h2
  apply hI
  rw [Ideal.eq_top_iff_one, ← Ideal.Quotient.eq_zero_iff_mem, map_one]
  exact h2

def posValIdeal {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l) : Ideal ↥(OL LL) where
  carrier := {x | 0 < P.v LL (algebraMap ↥(OL LL) ↥LL.1 x)}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, (algebraMap ↥(OL LL) ↥LL.1).map_add] at ha hb ⊢
    exact (P.v LL).map_lt_add ha hb
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_ofPred_eq, smul_eq_mul, (algebraMap ↥(OL LL) ↥LL.1).map_mul,
      AddValuation.map_mul] at hx ⊢
    have hc : 0 ≤ P.v LL (algebraMap ↥(OL LL) ↥LL.1 c) := (P.v_O LL _).2 c.2
    exact lt_of_lt_of_le hx (le_add_of_nonneg_left hc)

theorem oneUnit_eq_of_pow_pred_eq_of_pos {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l)
    (a b : ↥(OL LL)) (hab : a ^ (l - 1) = b ^ (l - 1))
    (ha : 0 < P.v LL (algebraMap ↥(OL LL) ↥LL.1 a - 1))
    (hb : 0 < P.v LL (algebraMap ↥(OL LL) ↥LL.1 b - 1)) : a = b := by
  refine eq_of_pow_pred_eq_of_sub_one_mem (posValIdeal P LL) ?_ l (Fact.out : l.Prime).pos ?_ a b
    hab ?_ ?_
  · rw [Ne, Ideal.eq_top_iff_one]
    change ¬ 0 < P.v LL (algebraMap ↥(OL LL) ↥LL.1 1)
    simp
  · change 0 < P.v LL (algebraMap ↥(OL LL) ↥LL.1 (l : ↥(OL LL)))
    rw [map_natCast, P.v_l]
    exact zero_lt_one
  · change 0 < P.v LL (algebraMap ↥(OL LL) ↥LL.1 (a - 1))
    rwa [map_sub, map_one]
  · change 0 < P.v LL (algebraMap ↥(OL LL) ↥LL.1 (b - 1))
    rwa [map_sub, map_one]

theorem units_eq_of_pow_pred_eq_of_pos {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l)
    (u w : (↥(OL LL))ˣ) (h : u ^ (l - 1) = w ^ (l - 1))
    (hu : 0 < P.v LL (algebraMap ↥(OL LL) ↥LL.1 (u : ↥(OL LL)) - 1))
    (hw : 0 < P.v LL (algebraMap ↥(OL LL) ↥LL.1 (w : ↥(OL LL)) - 1)) : u = w := by
  apply Units.ext
  refine oneUnit_eq_of_pow_pred_eq_of_pos P LL _ _ ?_ hu hw
  rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, h]

theorem units_eq_of_pow_pred_eq_of_val_one : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l)
    (LL : FinExt l) (u w : (↥(OL LL))ˣ), u ^ (l - 1) = w ^ (l - 1) →
    P.v LL (algebraMap ↥(OL LL) ↥LL.1 ((u : ↥(OL LL)) - 1)) = 1 →
    P.v LL (algebraMap ↥(OL LL) ↥LL.1 (w : ↥(OL LL)) - 1) = 1 → u = w := by
  intro l _ P LL u w h hu hw
  rw [map_sub, map_one] at hu
  refine units_eq_of_pow_pred_eq_of_pos P LL u w h ?_ ?_
  · rw [hu]; exact zero_lt_one
  · rw [hw]; exact zero_lt_one

end GlobalTheory
end

section

namespace GlobalTheory.UltrametricUnitNorm

section
variable {K : Type*} [NormedField K] [IsUltrametricDist K]

theorem norm_add_lt_one {x y : K} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) : ‖x + y‖ < 1 :=
  (IsUltrametricDist.norm_add_le_max x y).trans_lt (max_lt hx hy)

theorem norm_pow_sub_one_lt {u : K} (hu : ‖u‖ = 1) (h : ‖u - 1‖ < 1) (i : ℕ) : ‖u ^ i - 1‖ < 1 := by
  induction i with
  | zero => simp
  | succ i ih =>
    have e : u ^ (i + 1) - 1 = u * (u ^ i - 1) + (u - 1) := by ring
    rw [e]
    refine norm_add_lt_one ?_ h
    rwa [norm_mul, hu, one_mul]

theorem norm_geom_sub_lt {u : K} (hu : ‖u‖ = 1) (h : ‖u - 1‖ < 1) (n : ℕ) :
    ‖(∑ i ∈ Finset.range n, u ^ i) - (n : K)‖ < 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : (∑ i ∈ Finset.range (n + 1), u ^ i) - ((n + 1 : ℕ) : K)
        = ((∑ i ∈ Finset.range n, u ^ i) - (n : K)) + (u ^ n - 1) := by
      rw [Finset.sum_range_succ]; push_cast; ring
    rw [e]
    exact norm_add_lt_one ih (norm_pow_sub_one_lt hu h n)

omit [IsUltrametricDist K] in
theorem norm_eq_one_of_pow {x : K} {m : ℕ} (hm : 0 < m) (hx : x ^ m = 1) : ‖x‖ = 1 := by
  have h : ‖x‖ ^ m = 1 := by rw [← norm_pow, hx, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg x) hm.ne').1 h

theorem eq_of_norm_sub_lt {m : ℕ} (hm : 0 < m) (hn : ‖(m : K)‖ = 1) {ζ η : K} (hζ : ζ ^ m = 1)
    (hη : η ^ m = 1) (h : ‖η - ζ‖ < 1) : η = ζ := by
  have nζ := norm_eq_one_of_pow hm hζ
  have nη := norm_eq_one_of_pow hm hη
  have z0 : ζ ≠ 0 := by
    rintro rfl
    simp at nζ
  by_contra hne
  have hu : ‖η / ζ‖ = 1 := by rw [norm_div, nζ, nη, div_one]
  have hu1 : η / ζ - 1 = (η - ζ) / ζ := by field_simp
  have hlt : ‖η / ζ - 1‖ < 1 := by rwa [hu1, norm_div, nζ, div_one]
  have hne' : η / ζ - 1 ≠ 0 := by
    rw [hu1]
    exact div_ne_zero (sub_ne_zero.2 hne) z0
  have hs : (∑ i ∈ Finset.range m, (η / ζ) ^ i) = 0 := by
    have := geom_sum_mul (η / ζ) m
    rw [div_pow η ζ m, hη, hζ, div_one, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_right hne'
  have := norm_geom_sub_lt hu hlt m
  rw [hs, zero_sub, norm_neg, hn] at this
  exact lt_irrefl _ this

end

theorem norm_natCast_eq_one {l : ℕ} [hl : Fact (Nat.Prime l)] {m : ℕ} (hlm : ¬l ∣ m) :
    ‖(m : PadicAlgCl l)‖ = 1 := by
  have e : (m : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (m : ℚ_[l]) := (map_natCast _ m).symm
  rw [e, norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd hl.out).2 hlm

theorem root_eq_of_norm_sub_lt_one {l : ℕ} [hl : Fact (Nat.Prime l)] {m : ℕ} (hm : 0 < m) (hlm : ¬l ∣ m)
    {ζ η : Formalism.BasicNotions.Loc.Om l} (hζ : ζ ^ m = 1) (hη : η ^ m = 1) (h : ‖η - ζ‖ < 1) : η = ζ :=
  eq_of_norm_sub_lt hm (norm_natCast_eq_one hlm) hζ hη h

end GlobalTheory.UltrametricUnitNorm
end

section

namespace GlobalTheory.QuotientLatticeTorsion

theorem exists_ne_zero_smul_mem_of_span_eq_top
    {O K V : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    (N : Submodule O V) (hN : Submodule.span K (N : Set V) = ⊤) (v : V) :
    ∃ b : O, b ≠ 0 ∧ b • v ∈ N := by
  have hv : v ∈ Submodule.span K (N : Set V) := hN ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine N.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact N.smul_mem b hax
    · rw [mul_smul]
      exact N.smul_mem a hby
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (nonZeroDivisors O) c
    refine ⟨s.1 * a, mul_ne_zero (nonZeroDivisors.ne_zero s.2) ha, ?_⟩
    have key : (s.1 * a) • c • x = r • a • x := by
      rw [← algebraMap_smul K (s.1 * a), ← algebraMap_smul K r, ← algebraMap_smul K a x,
        smul_smul, smul_smul, ← hrs, map_mul]
      congr 1
      ring
    rw [key]
    exact N.smul_mem r hax

theorem quotient_lattice_torsion
    {G : Type} [Group G] [TopologicalSpace G] {Qp : Type} [Field Qp] {LL : Type} [Field LL]
    [Algebra Qp LL] [TopologicalSpace LL] {O : Type} [CommRing O] [Algebra O LL] [IsDomain O]
    [IsFractionRing O LL] (T : Formalism.BasicNotions.LocLat G Qp LL O)
    (w : Formalism.BasicNotions.LocLat.V T ⧸ Formalism.WeaklyAdmissibleFiltrations.Lattice.T (Formalism.BasicNotions.LocLat.L T)) :
    ∃ (b : O), b ≠ (0 : O) ∧
      b • w = (0 : Formalism.BasicNotions.LocLat.V T ⧸ Formalism.WeaklyAdmissibleFiltrations.Lattice.T (Formalism.BasicNotions.LocLat.L T)) := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  obtain ⟨b, hb, hbv⟩ :=
    exists_ne_zero_smul_mem_of_span_eq_top (K := LL) T.L.T T.L.span v
  refine ⟨b, hb, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact hbv

end GlobalTheory.QuotientLatticeTorsion
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

namespace GlobalTheory

theorem absoluteGalois_fixes_unramified_in_crystalline {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (g : ↥(GK K))
    (a : ↥(K0 K)) : P.actQ (g : GQ l) (algebraMap ↥(K0 K) P.R.B a) = algebraMap ↥(K0 K) P.R.B a := by
  have hfix : (g : GQ l) ((a : Om l)) = (a : Om l) :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 (a : Om l) a.2.1
  exact P.actQ_Kur (g : GQ l) (IntermediateField.inclusion (inf_le_right : K0 K ≤ MaximalUnramifiedExtension l) a)
    (IntermediateField.inclusion (inf_le_right : K0 K ≤ MaximalUnramifiedExtension l) a) hfix

theorem ltChar_hom : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (x : P.R.B), IsUnit x → (∀ g : ↥(GK K), ∃ a : ↥(K0 K), P.actQ (g : GQ l) x = algebraMap ↥(K0 K) P.R.B a * x) → ∃ c : ↥(GK K) →* (↥(K0 K))ˣ, ∀ g : ↥(GK K), P.actQ (g : GQ l) x = algebraMap ↥(K0 K) P.R.B ((c g : (↥(K0 K))ˣ) : ↥(K0 K)) * x := by
  intro l _ P K x hx h
  rcases subsingleton_or_nontrivial P.R.B with hB | hB
  · exact ⟨1, fun g => Subsingleton.elim _ _⟩
  · have hinj : Function.Injective (algebraMap ↥(K0 K) P.R.B) := (algebraMap ↥(K0 K) P.R.B).injective
    have hcan : ∀ a b : ↥(K0 K), algebraMap ↥(K0 K) P.R.B a * x = algebraMap ↥(K0 K) P.R.B b * x → a = b :=
      fun a b e => hinj (hx.mul_left_injective e)
    let f : ↥(GK K) → ↥(K0 K) := fun g : ↥(GK K) => Classical.choose (h g)
    have hf : ∀ g : ↥(GK K), P.actQ (g : GQ l) x = algebraMap ↥(K0 K) P.R.B (f g) * x :=
      fun g => Classical.choose_spec (h g)
    let F : ↥(GK K) →* ↥(K0 K) :=
      { toFun := f
        map_one' := by
          apply hcan
          rw [← hf, map_one, one_mul, OneMemClass.coe_one, map_one, AlgEquiv.one_apply]
        map_mul' := by
          intro g g'
          apply hcan
          rw [← hf]
          have e1 : P.actQ ((g * g' : ↥(GK K)) : GQ l) x = P.actQ (g : GQ l) (P.actQ (g' : GQ l) x) := by
            rw [Subgroup.coe_mul, map_mul, AlgEquiv.mul_apply]
          rw [e1, hf g', map_mul, absoluteGalois_fixes_unramified_in_crystalline, hf g, map_mul]
          ring }
    refine ⟨F.toHomUnits, fun g => ?_⟩
    rw [MonoidHom.coe_toHomUnits]
    exact hf g

end GlobalTheory
end

section

open Formalism.BasicNotions

namespace GlobalTheory
namespace FlatCompl

section Level

variable {A R E : Type} [CommRing A] [CommRing R] [CommRing E] [Algebra A R] [Algebra A E]
  [Algebra R E] [IsScalarTower A R E]

theorem mem_pow_smul_top_iff (p : ℕ) (n : ℕ) (e : E) :
    e ∈ ((Ideal.span {(p : R)}) ^ n • ⊤ : Submodule R E) ↔ e ∈ Ideal.span {(p : E) ^ n} := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨y, -, rfl⟩
    exact ⟨y, by simp [Algebra.smul_def, mul_comm]⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b, Submodule.mem_top, by simp [Algebra.smul_def, mul_comm]⟩

variable (s : A) [IsLocalization.Away s R] (p : ℕ)

theorem level_surj
    (hd : ∀ (x : E) (k : ℕ), ∃ (a : A) (m : ℕ),
      x * algebraMap A E (s ^ m) - algebraMap A E a ∈ Ideal.span {(p : E) ^ k})
    (n : ℕ) (e : E) : ∃ r : R, algebraMap R E r - e ∈ Ideal.span {(p : E) ^ n} := by
  obtain ⟨a, m, h⟩ := hd e n
  obtain ⟨u, hu⟩ := (IsLocalization.Away.algebraMap_isUnit (S := R) s).pow m
  refine ⟨algebraMap A R a * ↑u⁻¹, ?_⟩
  have hE : algebraMap R E ↑u * algebraMap R E ↑u⁻¹ = 1 := by
    rw [← map_mul, u.mul_inv, map_one]
  have key : algebraMap R E (algebraMap A R a * ↑u⁻¹) - e =
      -((e * algebraMap A E (s ^ m) - algebraMap A E a) * algebraMap R E ↑u⁻¹) := by
    rw [map_mul, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A R E (s ^ m),
      map_pow, ← hu]
    linear_combination e * hE
  rw [key]
  exact (Ideal.neg_mem_iff _).mpr (Ideal.mul_mem_right _ _ h)

include s in
theorem level_inj
    (hsat : ∀ (a : A) (k : ℕ), algebraMap A E a ∈ Ideal.span {(p : E) ^ k} →
      ∃ b : A, a = (p : A) ^ k * b)
    (n : ℕ) (r : R) (h : algebraMap R E r ∈ Ideal.span {(p : E) ^ n}) :
    r ∈ Ideal.span {(p : R) ^ n} := by
  obtain ⟨⟨a, ⟨_, m, rfl⟩⟩, hr⟩ := IsLocalization.surj (Submonoid.powers s) r
  simp only at hr
  have hE : algebraMap A E a ∈ Ideal.span {(p : E) ^ n} := by
    rw [IsScalarTower.algebraMap_apply A R E, ← hr, map_mul]
    exact Ideal.mul_mem_right _ _ h
  obtain ⟨b, rfl⟩ := hsat a n hE
  obtain ⟨u, hu⟩ := (IsLocalization.Away.algebraMap_isUnit (S := R) s).pow m
  rw [Ideal.mem_span_singleton']
  refine ⟨algebraMap A R b * ↑u⁻¹, ?_⟩
  have h1 : r = r * (↑u * ↑u⁻¹) := by simp
  rw [h1, ← mul_assoc, hu, ← map_pow, hr]
  simp only [map_mul, map_pow, map_natCast]
  ring

end Level

end FlatCompl
end GlobalTheory

namespace GlobalTheory
namespace FlatCompl

open AdicCompletion

theorem flat_of_dense_sat {A E : Type} [CommRing A] [IsNoetherianRing A] [CommRing E] [Algebra A E]
    (s : A) (p : ℕ) (hs : IsUnit (algebraMap A E s))
    (hc : IsAdicComplete (Ideal.span {(p : E)}) E)
    (hd : ∀ (x : E) (k : ℕ), ∃ (a : A) (m : ℕ),
      x * algebraMap A E (s ^ m) - algebraMap A E a ∈ Ideal.span {(p : E) ^ k})
    (hsat : ∀ (a : A) (k : ℕ), algebraMap A E a ∈ Ideal.span {(p : E) ^ k} →
      ∃ b : A, a = (p : A) ^ k * b) :
    Module.Flat A E := by
  let R := Localization.Away s
  letI : Algebra R E := (IsLocalization.Away.lift s hs).toAlgebra
  haveI : IsScalarTower A R E :=
    IsScalarTower.of_algebraMap_eq (fun a => (IsLocalization.lift_eq _ a).symm)
  let I : Ideal R := Ideal.span {(p : R)}
  have hmap : I.map (algebraMap R E) = Ideal.span {(p : E)} := by
    simp [I, Ideal.map_span]
  haveI : IsAdicComplete I E := by
    have h1 : IsHausdorff I E :=
      IsHausdorff.map_algebraMap_iff.mp (by rw [hmap]; exact hc.toIsHausdorff)
    have h2 : IsPrecomplete I E :=
      IsPrecomplete.map_algebraMap_iff.mp (by rw [hmap]; exact hc.toIsPrecomplete)
    exact { toIsHausdorff := h1, toIsPrecomplete := h2 }
  let f : R →ₗ[R] E := Algebra.linearMap R E
  have hinj : ∀ n, Function.Injective (f.reduceModIdeal (I ^ n)) := by
    intro n
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | H r =>
      rw [LinearMap.reduceModIdeal_apply, Submodule.Quotient.mk_eq_zero] at hx
      rw [Submodule.Quotient.mk_eq_zero, mem_pow_smul_top_iff (E := R)]
      exact level_inj s p hsat n r ((mem_pow_smul_top_iff p n _).mp hx)
  have hsurj : ∀ n, Function.Surjective (f.reduceModIdeal (I ^ n)) := by
    intro n y
    induction y using Submodule.Quotient.induction_on with
    | H e =>
      obtain ⟨r, hr⟩ := level_surj (R := R) s p hd n e
      refine ⟨Submodule.Quotient.mk r, ?_⟩
      rw [LinearMap.reduceModIdeal_apply, Submodule.Quotient.eq, mem_pow_smul_top_iff]
      exact hr
  have hbij : Function.Bijective (AdicCompletion.map I f) := by
    constructor
    · intro x y hxy
      ext n
      apply hinj n
      have := congrArg (fun z => z.val n) hxy
      simpa only [AdicCompletion.map_val_apply] using this
    · intro y
      let g := fun n => Function.surjInv (hsurj n)
      refine ⟨⟨fun n => g n (y.val n), fun {m n} hmn => ?_⟩, ?_⟩
      · apply hinj m
        have h1 := LinearMap.congr_fun
          (AdicCompletion.transitionMap_comp_reduceModIdeal I f hmn) (g n (y.val n))
        simp only [LinearMap.coe_comp, Function.comp_apply] at h1
        rw [show (f.reduceModIdeal (I ^ m)) (transitionMap I R hmn (g n (y.val n))) =
          transitionMap I E hmn (f.reduceModIdeal (I ^ n) (g n (y.val n))) from h1.symm]
        rw [Function.surjInv_eq (hsurj n), Function.surjInv_eq (hsurj m)]
        exact y.property hmn
      · ext n
        exact Function.surjInv_eq (hsurj n) _
  let Φ : AdicCompletion I R ≃ₗ[R] E :=
    (LinearEquiv.ofBijective ((AdicCompletion.map I f).restrictScalars R) hbij).trans
      (AdicCompletion.ofLinearEquiv I E).symm
  haveI : Module.Flat R E := Module.Flat.of_linearEquiv Φ.symm
  haveI : Module.Flat A R := IsLocalization.flat R (Submonoid.powers s)
  exact Module.Flat.trans A R E

end FlatCompl
end GlobalTheory

namespace GlobalTheory

theorem flat_letA_of_dense_sat : ∀ (O : Type) [CommRing O] [IsNoetherianRing O] (n : ℕ) [NeZero n] (p : ℕ) (E : Type) [CommRing E] [Algebra (LetA O n) E], IsUnit (algebraMap (LetA O n) E letπ) → IsAdicComplete (Ideal.span {(p : E)}) E → (∀ (x : E) (k : ℕ), ∃ (a : LetA O n) (m : ℕ), x * algebraMap (LetA O n) E (letπ ^ m) - algebraMap (LetA O n) E a ∈ Ideal.span {(p : E) ^ k}) → (∀ (a : LetA O n) (k : ℕ), algebraMap (LetA O n) E a ∈ Ideal.span {(p : E) ^ k} → ∃ b : LetA O n, a = (p : LetA O n) ^ k * b) → Module.Flat (LetA O n) E :=
  fun _ _ _ _ _ p _ _ _ hs hc hd hsat => FlatCompl.flat_of_dense_sat letπ p hs hc hd hsat

end GlobalTheory
end

section

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

theorem _root_.GlobalTheory.T.sum_lattice_pairs_index_rpow_le : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ) (σ : ℝ), (r : ℝ) - 1 < σ → ∀ C : Finset (GL (Fin r) K), (∀ g ∈ C, ∀ g' ∈ C, (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map (((g : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O) = (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map (((g' : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O) → g = g') → ∑ g ∈ C, (((((Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map (((g : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O)).toAddSubgroup.relIndex (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).toAddSubgroup : ℕ) : ℝ) * (((Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).toAddSubgroup.relIndex ((Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map (((g : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O)).toAddSubgroup : ℕ) : ℝ)) ^ (-σ) ≤ (∏ i ∈ Finset.range r, (1 - (Nat.card (IsLocalRing.ResidueField O) : ℝ) ^ ((i : ℝ) - σ))⁻¹) ^ 2 := by
  first | exact @GlobalTheory.LatticePairSum.sum_index_pairs_le | exact GlobalTheory.LatticePairSum.sum_index_pairs_le | (intros; apply GlobalTheory.LatticePairSum.sum_index_pairs_le <;> assumption)
end

section

open scoped BigOperators

theorem _root_.GlobalTheory.T.brauer_nesbitt_semisimple_matrix_representations : ∀ {k G : Type} [Field k] [Group G] (n : ℕ) (ρ σ : G →* Matrix (Fin n) (Fin n) k), (∀ W : Submodule k (Fin n → k), (∀ g, ∀ v ∈ W, (ρ g).mulVec v ∈ W) → ∃ W', IsCompl W W' ∧ ∀ g, ∀ v ∈ W', (ρ g).mulVec v ∈ W') → (∀ W : Submodule k (Fin n → k), (∀ g, ∀ v ∈ W, (σ g).mulVec v ∈ W) → ∃ W', IsCompl W W' ∧ ∀ g, ∀ v ∈ W', (σ g).mulVec v ∈ W') → (∀ g, (ρ g).charpoly = (σ g).charpoly) → ∃ P : GL (Fin n) k, ∀ g, (P : Matrix (Fin n) (Fin n) k) * ρ g = σ g * P := by
  first | exact @GlobalTheory.BrauerNesbittMatrix.main | exact GlobalTheory.BrauerNesbittMatrix.main | (intros; apply GlobalTheory.BrauerNesbittMatrix.main <;> assumption)
end

section

open Matrix Finset
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.galois_matrix_gaussSum_eq_char_pow_mul : ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (ψ : AddChar k ℂ) (ξ : kˣ →* ℂˣ) (r : ℕ), ψ.IsPrimitive → ξ ≠ 1 → ∀ S : ℂ, S = (∑ x : GL (Fin r) k, (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ) * ψ (Matrix.trace (x : Matrix (Fin r) (Fin r) k))) → ‖S‖ ^ 2 = (Fintype.card k : ℝ) ^ (r ^ 2) ∧ IsIntegral ℤ S ∧ IsIntegral ℤ ((Fintype.card k : ℂ) ^ (r ^ 2) * S⁻¹) ∧ ∀ (τ : ℂ ≃+* ℂ) (ξ' : kˣ →* ℂˣ), (∀ x, ((ξ' x : ℂˣ) : ℂ) = τ ((ξ x : ℂˣ) : ℂ)) → ∃ a : kˣ, (∀ x, τ (ψ x) = ψ ((a : k) * x)) ∧ τ S = ((ξ' a : ℂˣ) : ℂ) ^ r * ∑ x : GL (Fin r) k, (((ξ' (Matrix.GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ) * ψ (Matrix.trace (x : Matrix (Fin r) (Fin r) k)) := by
  first | exact @GlobalTheory.complexMatrixGaussSum_norm_integral_galois | exact GlobalTheory.complexMatrixGaussSum_norm_integral_galois | (intros; apply GlobalTheory.complexMatrixGaussSum_norm_integral_galois <;> assumption)
end

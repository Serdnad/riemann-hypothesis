module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1060
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle014
public import Mathlib.NumberTheory.NumberField.CMField
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle595
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle828
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle561
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1065
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle103
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle613
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle403
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle969
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle863
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle864
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1067
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_mono_classifying_of_injective_family : ∀ (S : Scheme.{0}) (A B S' U : Over S) [GrpObj A] (b : B ⟶ S') (P : LB (A ⊗ B).left) (M : LB (A ⊗ U).left), Rep A b P → Fam A M → Inj A M → ∃ φ : U ⊗ S' ⟶ B, φ ≫ b = snd U S' ∧ Same A M P (fst U S') φ ∧ Mono φ.left := by
  first | exact @GlobalTheory.DualCon.classify_mono | exact GlobalTheory.DualCon.classify_mono | (intros; apply GlobalTheory.DualCon.classify_mono <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.openImmersion_classifying_family_chart : ∀ (S : Scheme.{0}) (A B S' U : Over S) [GrpObj A] (b : B ⟶ S') (P : LB (A ⊗ B).left) (M : LB (A ⊗ U).left), Rep A b P → Fam A M → ∀ φ : U ⊗ S' ⟶ B, φ ≫ b = snd U S' → Same A M P (fst U S') φ → IsOpenImmersion φ.left → ∀ (T : Over S) (_ : T ⟶ S') (N : LB (A ⊗ T).left), Fam A N → ChartAt A M N := by
  first | exact @GlobalTheory.RepChart.repChart | exact GlobalTheory.RepChart.repChart | (intros; apply GlobalTheory.RepChart.repChart <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.RedCoef

variable {S R T : Type} [CommRing S] [CommRing R] [CommRing T]

def semiId (I : Cx S) : SemiMap I I where
  app _ _ := AddMonoidHom.id _
  nat _ _ _ := rfl
  comm _ _ _ _ := rfl

def semiComp {I : Cx S} {J : Cx R} {K : Cx T} (ρ : SemiMap I J) (σ : SemiMap J K) : SemiMap I K where
  app U s := (σ.app U s).comp (ρ.app U s)
  nat g s a := by
    change Sec.res g (σ.app _ s (ρ.app _ s a)) = σ.app _ s (ρ.app _ s (Sec.res g a))
    rw [σ.nat, ρ.nat]
  comm U s t a := by
    change Sec.map (K.d s t) (σ.app U s (ρ.app U s a)) = σ.app U t (ρ.app U t (Sec.map (I.d s t) a))
    rw [σ.comm, ρ.comm]

theorem semiId_op (I : Cx S) (E : Spc) (n : ℤ) (x : CohomologyClass ((chains S).obj E) I n) :
    (semiId I).op.app E n x = x := by
  obtain ⟨α, rfl⟩ := x.mk_surjective
  exact (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S S (semiId I)).2 E n α α (fun _ _ _ _ _ => rfl)

theorem semiComp_op {I : Cx S} {J : Cx R} {K : Cx T} (ρ : SemiMap I J) (σ : SemiMap J K) (E : Spc) (n : ℤ)
    (x : CohomologyClass ((chains S).obj E) I n) : (semiComp ρ σ).op.app E n x = σ.op.app E n (ρ.op.app E n x) := by
  obtain ⟨α, rfl⟩ := x.mk_surjective
  obtain ⟨β, hβ⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ).1 E n α
  obtain ⟨γ, hγ⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap R T σ).1 E n β
  rw [(GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ).2 E n α β hβ, (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap R T σ).2 E n β γ hγ]
  exact (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S T (semiComp ρ σ)).2 E n α γ (fun p s h U y => by
    rw [hγ p s h U y, hβ p s h U y]; rfl)

theorem neZero_of_dvd {q Q : ℕ} [NeZero Q] (h : q ∣ Q) : NeZero q :=
  ⟨by rintro rfl; exact NeZero.ne Q (zero_dvd_iff.mp h)⟩

theorem div_mul_div {Q q r : ℕ} [NeZero Q] (hq : q ∣ Q) (hr : r ∣ q) : Q / q * (q / r) = Q / r := by
  obtain ⟨k, rfl⟩ := hq
  obtain ⟨l, rfl⟩ := hr
  have hQ := NeZero.ne (r * l * k)
  have hr0 : r ≠ 0 := by rintro rfl; simp at hQ
  have hl0 : l ≠ 0 := by rintro rfl; simp at hQ
  rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (Nat.mul_ne_zero hr0 hl0)),
    Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hr0), mul_assoc, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hr0),
    mul_comm]

end GlobalTheory.EtC.RedCoef

namespace GlobalTheory.EtC.RedCoef

theorem a11 : GlobalTheory.EtC.A11 := by
  intro Q q _ hqQ E
  haveI : NeZero q := neZero_of_dvd hqQ
  refine ⟨fun a b => GlobalTheory.T.tateTwistCoefficientReduction_cup Q q hqQ E a b, fun hE => ⟨GlobalTheory.T.tateTwistCoefficientReduction_unitClass Q q hqQ E hE, fun L => GlobalTheory.T.red_c1_eq_c1_of_dvd Q q hqQ E hE L⟩,
    fun n i a => ?_, fun r hr n i a => ?_⟩
  · have hgen : ∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)),
        (redMap Q Q i).app U 0 (resGen i ζ) = (semiId (res _ (tw Q i))).app U 0 (resGen i ζ) := by
      intro U ζ
      refine GlobalTheory.T.tateTwistReductionResolutionMap_generator Q Q dvd_rfl i U ζ ζ ?_
      rw [Nat.div_self (Nat.pos_of_ne_zero (NeZero.ne Q)), pow_one]
    exact (GlobalTheory.T.tateTwistReduction_cohomology_map_unique Q Q dvd_rfl i _ _ hgen E n a).trans (semiId_op _ E n a)
  · haveI : NeZero r := neZero_of_dvd hr
    have hrQ : r ∣ Q := hr.trans hqQ
    have hgen : ∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)),
        (semiComp (redMap Q q i) (redMap q r i)).app U 0 (resGen i ζ) = (redMap Q r i).app U 0 (resGen i ζ) := by
      intro U ζ
      obtain ⟨η, hη⟩ := (GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties Q Γ(U, ⊤)).2.2.2.2.2 q hqQ ζ
      obtain ⟨ξ, hξ⟩ := (GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties q Γ(U, ⊤)).2.2.2.2.2 r hr η
      change (redMap q r i).app U 0 ((redMap Q q i).app U 0 (resGen i ζ)) = _
      rw [GlobalTheory.T.tateTwistReductionResolutionMap_generator Q q hqQ i U ζ η hη, GlobalTheory.T.tateTwistReductionResolutionMap_generator q r hr i U η ξ hξ,
        GlobalTheory.T.tateTwistReductionResolutionMap_generator Q r hrQ i U ζ ξ (by rw [hξ, hη, ← pow_mul, div_mul_div hqQ hr])]
    exact (semiComp_op _ _ E n a).symm.trans (GlobalTheory.T.tateTwistReduction_cohomology_map_unique Q r hrQ i _ _ hgen E n a)

end GlobalTheory.EtC.RedCoef
end
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.LatEnt UniqueFactorizationMonoid

namespace GlobalTheory.CMVal.IdealIdele

variable {E : Type} [Field E] [NumberField E]


open Classical in
def primeIdele (p : Ideal (𝓞 E)) : (Af E)ˣ :=
  if h : p.IsPrime ∧ p ≠ ⊥ then unifAt ⟨p, h.1, h.2⟩ else 1

def idl (I : Ideal (𝓞 E)) : (Af E)ˣ := ((normalizedFactors I).map primeIdele).prod

theorem idl_top : idl (⊤ : Ideal (𝓞 E)) = 1 := by
  rw [idl, ← Ideal.one_eq_top, normalizedFactors_one]; simp

theorem idl_mul {I J : Ideal (𝓞 E)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) : idl (I * J) = idl I * idl J := by
  rw [idl, normalizedFactors_mul hI hJ, Multiset.map_add (f := _), Multiset.prod_add]; rfl

theorem nf_prime (v : HeightOneSpectrum (𝓞 E)) : normalizedFactors v.asIdeal = {v.asIdeal} := by
  rw [normalizedFactors_irreducible v.irreducible, normalize_eq]

theorem idl_prime (v : HeightOneSpectrum (𝓞 E)) : idl v.asIdeal = unifAt v := by
  rw [idl, nf_prime, Multiset.map_singleton, Multiset.prod_singleton, primeIdele,
    dite_eq_left ⟨v.isPrime, v.ne_bot⟩]

theorem ind {P : Ideal (𝓞 E) → Prop} (h1 : P ⊤)
    (h2 : ∀ (v : HeightOneSpectrum (𝓞 E)) (I : Ideal (𝓞 E)), I ≠ ⊥ → P I → P (v.asIdeal * I)) :
    ∀ I, I ≠ ⊥ → P I := fun I => by
  refine induction_on_prime (P := fun I => I ≠ ⊥ → P I) I (fun h => absurd rfl h) ?_ ?_
  · intro x hx _
    rw [Ideal.isUnit_iff.1 hx]; exact h1
  · intro a p ha hp h _
    exact h2 ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩ a ha (h ha)

theorem mul_apply' (a b : (Af E)ˣ) (w : HeightOneSpectrum (𝓞 E)) :
    ((a * b : (Af E)ˣ) : Af E) w = (a : Af E) w * (b : Af E) w := rfl

theorem one_apply' (w : HeightOneSpectrum (𝓞 E)) : ((1 : (Af E)ˣ) : Af E) w = 1 := rfl

theorem modF_idl : ∀ I : Ideal (𝓞 E), I ≠ ⊥ → modF (idl I) = ((Ideal.absNorm I : ℕ) : ℝ)⁻¹ := by
  refine ind ?_ ?_
  · rw [idl_top, modF_eq_one fun w => by rw [one_apply', map_one]]
    simp
  · intro v I hI h
    rw [idl_mul v.ne_bot hI, ObjModel.modF_mul, h, idl_prime, modF_unifAt, map_mul]
    push_cast
    rw [mul_inv]

open Classical in
theorem val_idl (w : HeightOneSpectrum (𝓞 E)) : ∀ I : Ideal (𝓞 E), I ≠ ⊥ →
    Valued.v ((idl I : Af E) w) = WithZero.exp (-((normalizedFactors I).count w.asIdeal : ℤ)) := by
  refine ind ?_ ?_
  · rw [idl_top, one_apply', map_one, ← Ideal.one_eq_top, normalizedFactors_one]; simp
  · intro v I hI h
    rw [idl_mul v.ne_bot hI, mul_apply', map_mul, h, idl_prime, normalizedFactors_mul v.ne_bot hI, nf_prime,
      Multiset.count_add]
    by_cases hw : w = v
    · subst hw
      rw [(unifAt_spec w).2, ← WithZero.exp_add, Multiset.count_singleton_self]
      congr 1; push_cast; ring
    · have : w.asIdeal ≠ v.asIdeal := fun h => hw (HeightOneSpectrum.ext h)
      rw [(unifAt_spec v).1 w hw, map_one, one_mul, Multiset.count_singleton, if_neg this, zero_add]

theorem idl_eq_one (w : HeightOneSpectrum (𝓞 E)) : ∀ I : Ideal (𝓞 E), I ≠ ⊥ →
    ¬ w.asIdeal ∣ I → (idl I : Af E) w = 1 := by
  refine ind ?_ ?_
  · intro _; rw [idl_top, one_apply']
  · intro v I hI h hd
    have hw : w ≠ v := by
      rintro rfl
      exact hd (dvd_mul_right _ _)
    rw [idl_mul v.ne_bot hI, mul_apply', h fun h => hd (h.mul_left _), idl_prime, (unifAt_spec v).1 w hw, one_mul]

theorem mem_nf {w : HeightOneSpectrum (𝓞 E)} {I : Ideal (𝓞 E)} (hI : I ≠ ⊥) (h : w.asIdeal ∣ I) :
    w.asIdeal ∈ normalizedFactors I :=
  (mem_normalizedFactors_iff hI).2 ⟨w.prime, h⟩

open Classical in
theorem exists_count (n : HeightOneSpectrum (𝓞 E) → ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) :
    ∃ I : Ideal (𝓞 E), I ≠ ⊥ ∧ ∀ w : HeightOneSpectrum (𝓞 E),
      (normalizedFactors I).count w.asIdeal = if w ∈ S then n w else 0 := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, fun w => by rw [normalizedFactors_one]; simp⟩
  | insert v S hv ih =>
    obtain ⟨I, hI, h⟩ := ih
    have h0 : v.asIdeal ^ n v ≠ 0 := pow_ne_zero _ v.ne_bot
    refine ⟨v.asIdeal ^ n v * I, mul_ne_zero h0 hI, fun w => ?_⟩
    rw [normalizedFactors_mul h0 hI, normalizedFactors_pow, nf_prime, Multiset.count_add, h, Multiset.count_nsmul,
      Multiset.count_singleton]
    by_cases hw : w = v
    · subst hw; simp [hv]
    · have : w.asIdeal ≠ v.asIdeal := fun h => hw (HeightOneSpectrum.ext h)
      simp [this, hw]

theorem finite_val_ne_one (z : (Af E)ˣ) : {w : HeightOneSpectrum (𝓞 E) | Valued.v ((z : Af E) w) ≠ 1}.Finite :=
  GlobalTheory.Mem.TupHecke.finite_nonunit z

theorem main : ∀ (E : Type) [Field E] [NumberField E], ∃ t : Ideal (𝓞 E) → (Af E)ˣ, t ⊤ = 1 ∧
    (∀ I J, I ≠ ⊥ → J ≠ ⊥ → t (I * J) = t I * t J) ∧ (∀ v : HeightOneSpectrum (𝓞 E), t v.asIdeal = unifAt v) ∧
    (∀ I, I ≠ ⊥ → modF (t I) = ((Ideal.absNorm I : ℕ) : ℝ)⁻¹) ∧
    (∀ I, I ≠ ⊥ → ∀ w : HeightOneSpectrum (𝓞 E), Valued.v ((t I : Af E) w) ≤ 1 ∧
      (w.asIdeal ∣ I → Valued.v ((t I : Af E) w) < 1) ∧ (¬ w.asIdeal ∣ I → (t I : Af E) w = 1)) ∧
    (∀ I J, I ≠ ⊥ → J ≠ ⊥ → (∀ w, Valued.v ((t I : Af E) w) = Valued.v ((t J : Af E) w)) → I = J) ∧
    ∀ z : (Af E)ˣ, (∀ w, Valued.v ((z : Af E) w) ≤ 1) →
      ∃ I, I ≠ ⊥ ∧ ∀ w, Valued.v ((t I : Af E) w) = Valued.v ((z : Af E) w) := by
  intro E _ _
  classical
  refine ⟨idl, idl_top, fun _ _ => idl_mul, idl_prime, modF_idl, fun I hI w => ⟨?_, fun hd => ?_, idl_eq_one w I hI⟩,
    fun I J hI hJ h => ?_, fun z hz => ?_⟩
  · rw [val_idl w I hI, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega
  · have := Multiset.count_pos.2 (mem_nf hI hd)
    rw [val_idl w I hI, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  · have e : normalizedFactors I = normalizedFactors J := by
      ext p
      by_cases hp : Prime p
      · have := h ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩
        rw [val_idl _ I hI, val_idl _ J hJ, WithZero.exp_inj] at this
        simpa using this
      · rw [Multiset.count_eq_zero.2 fun h => hp (prime_of_normalized_factor _ h),
          Multiset.count_eq_zero.2 fun h => hp (prime_of_normalized_factor _ h)]
    rw [← Ideal.prod_normalizedFactors_eq_self hI, e, Ideal.prod_normalizedFactors_eq_self hJ]
  · obtain ⟨I, hI, h⟩ := exists_count (fun w => (-(Valued.v ((z : Af E) w)).log).toNat)
      (finite_val_ne_one z).toFinset
    refine ⟨I, hI, fun w => ?_⟩
    rw [val_idl w I hI, h]
    split_ifs with hw
    · have h0 := ObjModel.coord_ne z w
      have h1 : (Valued.v ((z : Af E) w)).log ≤ 0 := by
        rw [← WithZero.exp_le_exp, WithZero.exp_log h0]; exact hz w
      rw [Int.toNat_of_nonneg (by omega), neg_neg, WithZero.exp_log h0]
    · have : Valued.v ((z : Af E) w) = 1 := by simpa using hw
      rw [this]; simp

end GlobalTheory.CMVal.IdealIdele
end
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler

namespace GlobalTheory.CMVal.Euler

theorem exists_finset_cover_units : ∀ (E : Type) [Field E] [NumberField E] (c : Ideal (OF E)), c ≠ ⊥ →
    ∃ R : Finset (Af E)ˣ, ∀ y : (Af E)ˣ, (∀ w, Valued.v ((y : Af E) w) = 1) → ∃ r ∈ R, r⁻¹ * y ∈ hatOUnits c := by
  classical
  intro E _ _ c hc
  let U : Subgroup (Af E)ˣ := (PicFin.intR E).toSubmonoid.units
  have h1 : ((hatOUnits c).subgroupOf U).FiniteIndex := PicFin.finiteIndex_units hc
  have h2 : Finite (U ⧸ (hatOUnits c).subgroupOf U) := Subgroup.finite_quotient_of_finiteIndex
  have := Fintype.ofFinite (U ⧸ (hatOUnits c).subgroupOf U)
  refine ⟨Finset.univ.image fun q : U ⧸ (hatOUnits c).subgroupOf U => (q.out : U).1, fun y hy => ?_⟩
  have hyU : y ∈ U := (Submonoid.mem_units_iff _ _).2
    ⟨fun v => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hy v).le,
     fun v => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2
      (by rw [inv_coord, map_inv₀, hy v, inv_one])⟩
  refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ (QuotientGroup.mk ⟨y, hyU⟩)), ?_⟩
  have h3 := (QuotientGroup.eq (s := (hatOUnits c).subgroupOf U)).1
    (QuotientGroup.out_eq' (QuotientGroup.mk ⟨y, hyU⟩ : U ⧸ (hatOUnits c).subgroupOf U))
  exact Subgroup.mem_subgroupOf.1 h3

end GlobalTheory.CMVal.Euler
end
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal

theorem _root_.GlobalTheory.T.finite_ringClassGroup_of_conductor_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → Finite (PicO c) := by
  first | exact @GlobalTheory.CMVal.PicFin.finite_picO | exact GlobalTheory.CMVal.PicFin.finite_picO | (intros; apply GlobalTheory.CMVal.PicFin.finite_picO <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.exists_lift_adapted_basis_quasi_logarithms_frame : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ Θ : F.Q →+* C, (∀ b, Θ (algebraMap F.B F.Q b) = algebraMap O C (F.θ b)) → ∀ (k : ℕ) (e0 : Fin d ⊕ Fin k → MvPowerSeries (Fin d) C), IsBasis c.μ e0 → IsAdapted (RingHom.id O) c.μ e0 → ∃ e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q, (∀ l, map Θ (e l) = e0 l) ∧ IsBasis μ' e ∧ IsAdapted F.θ μ' e := by
  first | exact @GlobalTheory.QLog.LiftBasis.exists_lift_isAdapted | exact GlobalTheory.QLog.LiftBasis.exists_lift_isAdapted | (intros; apply GlobalTheory.QLog.LiftBasis.exists_lift_isAdapted <;> assumption)
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog

theorem exists_int_cob_dvd_of_defect_ev :
    ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (f : MvPowerSeries (Fin d) E) (s : MvPowerSeries (Fin d) O) (y : G.A 1), QL c.μ ⊤ f → map (algebraMap O E) s = defect c.μ p f → c.ev 1 s = (p : O) • y → ∃ t : MvPowerSeries (Fin d) O, constantCoeff t = 0 ∧ In (Ideal.span {(p : O)}) (cob1 (up E c.μ) (f - map (algebraMap O E) t)) := by
  intro p _ O E _ _ _ hF G d c f s y hQL hs hy
  obtain ⟨hf0, -, hcob⟩ := hQL
  choose bκ _ hbκ using hcob
  set κ : MvPowerSeries (Fin d ⊕ Fin d) O := fun α => bκ α with hκdef
  have hκ : map (algebraMap O E) κ = cob1 (up E c.μ) f := by
    ext α
    rw [coeff_map, hbκ α]
    rfl
  obtain ⟨hcoc, hκ0, hdef⟩ := GlobalTheory.T.integral_coboundary_representative_cocycle_rules O E d c.μ c.isLaw hF.inj f κ hκ
  have hrel := (hdef p s hs).1
  have hμ0 := c.isLaw.const
  have hneg : cob1 c.μ (-s) = -cob1 c.μ s := by
    rw [← neg_one_smul O s, formalCoboundary_smul hμ0, neg_one_smul]
  obtain ⟨t, ht0, htd⟩ := GlobalTheory.T.formalGroupCocycle_coboundary_mod_prime p O G d c κ (-s) (-y) (hκ0 hf0) hcoc
    (fun α => by
      rw [hneg, hrel, show -((p : O) • κ - pull2 (nmul c.μ p) κ) - pull2 (nmul c.μ p) κ
        = -((p : O) • κ) by ring, map_neg, coeff_smul]
      exact (Dvd.intro _ rfl).neg_right)
    (by rw [map_neg, hy, smul_neg])
  refine ⟨t, ht0, fun α => ⟨coeff α (κ - cob1 c.μ t), Ideal.mem_span_singleton.2 (htd α), ?_⟩⟩
  have hup0 : ∀ i, constantCoeff (up E c.μ i) = 0 := fun i => by
    rw [up, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      hμ0, map_zero]
  have hadd := formalCoboundary_add hup0 (f - map (algebraMap O E) t) (map (algebraMap O E) t)
  rw [sub_add_cancel] at hadd
  have hmap := (GlobalTheory.T.map_coboundary_swap_pullback_commute O d c.μ hμ0 E (algebraMap O E)).1 t
  have hsub : cob1 (up E c.μ) (f - map (algebraMap O E) t) =
      map (algebraMap O E) (κ - cob1 c.μ t) := by
    rw [map_sub, hmap, hκ]
    exact eq_sub_of_add_eq hadd.symm
  rw [hsub, coeff_map]

end GlobalTheory.QLog
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.additive_mod_prime_eq_quasiLogarithm_defect : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (b : G.A 1) (z : G.A 1 ⊗[O] G.A 1), cobOne O (G.A 1) b = (p : O) • z → ∃ (f : MvPowerSeries (Fin d) E) (s : MvPowerSeries (Fin d) O) (y : G.A 1), QL c.μ ⊤ f ∧ map (algebraMap O E) s = defect c.μ p f ∧ c.ev 1 s = b + (p : O) • y := by
  first | exact @GlobalTheory.QLog.additive_mod_p_is_defect | exact GlobalTheory.QLog.additive_mod_p_is_defect | (intros; apply GlobalTheory.QLog.additive_mod_p_is_defect <;> assumption)
end

section

open GlobalTheory.EtC

theorem _root_.GlobalTheory.T.henselian_directed_union_subalgebras : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) → ∀ (O : Type) [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O] [IsSepClosed (IsLocalRing.ResidueField O)], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E) (P : Ideal E) (_ : P.IsPrime), Nonempty (Localization.AtPrime P ≃ₐ[(Polynomial T)] Si i)) → ∀ (A : Type) [CommRing A] [Algebra (Polynomial T) A] [Algebra T A] [IsScalarTower T (Polynomial T) A] (π : O →ₐ[Polynomial T] A), Function.Surjective π → ∀ u : (TensorProduct T (FractionRing T) A)ˣ, ∃ v : (TensorProduct T (FractionRing T) A)ˣ, v ^ q = u := by
  first | (exact @GlobalTheory.QUnits.tensorFractionRing_units_pow_surj) | (exact GlobalTheory.QUnits.tensorFractionRing_units_pow_surj) | (intros; apply GlobalTheory.QUnits.tensorFractionRing_units_pow_surj  <;> assumption)
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.WpFam

theorem _root_.GlobalTheory.T.galois_conj_qExpansion_family_diag_one_unit : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) [NeZero N] (L : Lat F), 1 ≤ s → HasLevel N L → ∀ (z : ClassGroup (𝓞 F) → ℚ), ZetaVals (2 * s) z → ∀ (g : ℂ ≃+* ℂ) (a : (ZMod N)ˣ) (κ κ' : Emb F → ℕ) (y : Fin 2 → ZMod N), ZetaAct g N a → (∀ i j : Emb F, (∀ x : F, g ((i x : ℝ) : ℂ) = ((j x : ℝ) : ℂ)) → κ' j = κ i) → y ≠ 0 → ∀ α : GL (Fin 2) (ZMod N), QConj g N (hfun (2 * s) (twist N L ((α : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) κ (wB N (vmul y (α)))) (hfun (2 * s) (twist N L ((α * dg a : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) κ' (wB N (vmul y (α * dg a)))) := by
  first | exact @GlobalTheory.HilbFam.GalFamily.qConj_family | exact GlobalTheory.HilbFam.GalFamily.qConj_family | (intros; apply GlobalTheory.HilbFam.GalFamily.qConj_family <;> assumption)
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.WpFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.norm_hilbertEisensteinValue_le_of_integral_j : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) [NeZero N] (L : Lat F), 1 ≤ s → HasLevel N L → ∀ [IsGalois ℚ F] (z : ClassGroup (𝓞 F) → ℚ), ZetaVals (2 * s) z → ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (κ : Emb F → ℕ) (y : Fin 2 → ZMod N) (M M' b : ℕ) (e ρ₀ ρ : ℝ), 0 ≤ e → (∀ C, -(padicValRat l (z C / 2 ^ Module.finrank ℚ F) : ℝ) ≤ e) → ¬ l ∣ M → (∀ x ∈ stdLat F, ((M * l ^ b : ℕ) : 𝓞 F) • x ∈ L) → (∀ v ∈ L, ∀ (j : Fin 2) (i : Emb F), Sz l lam ρ₀ ((i (v j) : ℝ) : ℂ)) → Sz l lam ρ₀ (N : ℂ) → b + (padicValInt l (discr F) : ℝ) / Module.finrank ℚ F + ρ₀ ≤ ρ → 0 ≤ ρ → ¬ l ∣ M' → M' • y = 0 → y ≠ 0 →  ∀ (τ : ℍ) (ω : ℂ), Sz l lam 0 (jT τ) → ω ^ 12 = DD τ → Sz l lam (e + s * (padicValInt l (discr F) : ℝ) + 2 * s * b * Module.finrank ℚ F + (∑ i, κ i : ℕ) * ρ) (hfun (2 * s) L κ (wB N y) τ / ω ^ wt (2 * s) κ) := by
  first | exact @GlobalTheory.HilbFam.size_values_hfun | exact GlobalTheory.HilbFam.size_values_hfun | (intros; apply GlobalTheory.HilbFam.size_values_hfun <;> assumption)
end

module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle009
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
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
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Localization.Submodule
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def FormalFibresRegularPolynomial.Statement : Prop :=
  ∀ (k : Type) [Field k] (n : ℕ) (M : Ideal (MvPolynomial (Fin n) k)), M.IsMaximal →
    ∀ (P : Ideal (AdicCompletion M (MvPolynomial (Fin n) k))) [P.IsPrime],
      IsRegularLocalRing (primeFibreLocalRing (MvPolynomial (Fin n) k) P)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing RingTheory.Sequence

def SerreRAt (B : Type*) [CommRing B] (k : ℕ) : Prop :=
  ringKrullDim B ≤ (k : WithBot ℕ∞) → IsRegularLocalRing B

def SerreSAt (B : Type*) [CommRing B] [IsLocalRing B] (k : ℕ) : Prop :=
  ∃ rs : List B, (∀ r ∈ rs, r ∈ maximalIdeal B) ∧ IsWeaklyRegular B rs ∧
    min (k : WithBot ℕ∞) (ringKrullDim B) ≤ (rs.length : WithBot ℕ∞)

def SerreR (A : Type*) [CommRing A] (k : ℕ) : Prop :=
  ∀ (P : Ideal A) [P.IsPrime], SerreRAt (Localization.AtPrime P) k

def SerreS (A : Type*) [CommRing A] (k : ℕ) : Prop :=
  ∀ (P : Ideal A) [P.IsPrime], SerreSAt (Localization.AtPrime P) k

def NormalRing (A : Type*) [CommRing A] : Prop :=
  ∀ (P : Ideal A) [P.IsPrime], IsDomain (Localization.AtPrime P) ∧ IsIntegrallyClosed (Localization.AtPrime P)

theorem primeFibreLocalRing_ideal_ne_top (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Ideal S) [P.IsPrime] :
    Ideal.map (algebraMap S (Localization.AtPrime P))
      (Ideal.map (algebraMap R S) (Ideal.comap (algebraMap R S) P)) ≠ ⊤ := by
  intro h
  have hle : Ideal.map (algebraMap S (Localization.AtPrime P))
      (Ideal.map (algebraMap R S) (Ideal.comap (algebraMap R S) P)) ≤ maximalIdeal (Localization.AtPrime P) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.map_mono Ideal.map_comap_le
  exact (maximalIdeal.isMaximal _).ne_top (top_le_iff.mp (h ▸ hle))

instance primeFibreLocalRing.isLocalRing (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Ideal S) [P.IsPrime] : IsLocalRing (primeFibreLocalRing R P) := by
  have : Nontrivial (primeFibreLocalRing R P) :=
    Ideal.Quotient.nontrivial_iff.mpr (primeFibreLocalRing_ideal_ne_top R P)
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u

noncomputable section

theorem length_self_eq_of_ringEquiv {A C : Type*} [CommRing A] [CommRing C] (e : A ≃+* C) :
    Module.length A A = Module.length C C := by
  have : RingHomSurjective (e : A →+* C) := ⟨e.surjective⟩
  let f : A →ₛₗ[(e : A →+* C)] C :=
    { toFun := e, map_add' := e.map_add, map_smul' := fun a b => by simp }
  rw [Module.length, Module.length, WithBot.unbot_inj,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f e.bijective)]

theorem LocalizeQuotientStages.proof : LocalizeQuotientStages.Statement.{u} := by
  intro R _ m W I _ _ hWm hIW P _ hP
  let Q := R ⧸ I
  let B := Localization.AtPrime m ⧸ I.map (algebraMap R (Localization.AtPrime m))
  let T := Localization.AtPrime W ⧸ I.map (algebraMap R (Localization.AtPrime W))

  have hdisj : Disjoint (m.primeCompl : Set R) (W : Set R) :=
    Set.disjoint_left.2 fun a ha hW => ha (hWm hW)
  have hPR : P.comap (algebraMap R B) = W := by
    rw [IsScalarTower.algebraMap_eq R (Localization.AtPrime m) B, ← Ideal.comap_comap,
      Ideal.Quotient.algebraMap_eq, ← hP,
      ← Ideal.map_map, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.2 (Ideal.map_mono hIW)]
    exact IsLocalization.under_map_of_isPrime_disjoint m.primeCompl _ ‹W.IsPrime› hdisj

  have hsub : (P.comap (algebraMap Q B)).primeCompl =
      Algebra.algebraMapSubmonoid Q W.primeCompl := by
    ext q
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
    have h1 : Ideal.Quotient.mk I r ∈ (P.comap (algebraMap Q B)).primeCompl ↔ r ∉ W := by
      rw [← hPR]; exact Iff.rfl
    rw [h1]
    constructor
    · intro hr; exact ⟨r, hr, rfl⟩
    · rintro ⟨r', hr', he⟩ hr
      apply hr'
      have : r' - r ∈ I := Ideal.Quotient.eq.1 he
      simpa using W.add_mem (hIW this) hr
  have hBP : IsLocalization (Algebra.algebraMapSubmonoid Q W.primeCompl)
      (Localization.AtPrime P) := by
    have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Algebra.algebraMapSubmonoid Q m.primeCompl) (Localization.AtPrime P) P
    rw [IsLocalization.AtPrime, hsub] at this
    exact this
  let e := IsLocalization.algEquiv (Algebra.algebraMapSubmonoid Q W.primeCompl)
    (Localization.AtPrime P) T
  exact (length_self_eq_of_ringEquiv (A := Localization.AtPrime P) (C := T) e.toRingEquiv).trans
    (Module.length_eq_of_surjective (R := T) (S := Localization.AtPrime W) (M := T)
      Ideal.Quotient.mk_surjective).symm

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u v

open IsLocalRing

theorem LengthCutLocalizedModule.proof (hG : LengthCutGlobal.Statement.{u, max u v})
    (hL : LengthLocalizedLocalized.Statement.{u, v}) : LengthCutLocalizedModule.Statement.{u, v} := by
  intro B _ _ P _ y Q₀ _ M _ _ _ hnil hy hQ htf
  have hPQ : P ≤ Q₀ := hQ ▸ le_sup_left
  have hdisj : Disjoint (Q₀.primeCompl : Set B) P := Set.disjoint_left.mpr fun _ hx hxP => hx (hPQ hxP)
  have hP' : (P.map (algebraMap B (Localization.AtPrime Q₀))).IsPrime :=
    LengthLocalizedLocalized.map_isPrime B P Q₀ hPQ
  have : IsNoetherianRing (Localization.AtPrime Q₀) :=
    IsLocalization.isNoetherianRing Q₀.primeCompl _ inferInstance
  have hunder : (P.map (algebraMap B (Localization.AtPrime Q₀))).comap (algebraMap B (Localization.AtPrime Q₀)) =
      P := IsLocalization.under_map_of_isPrime_disjoint Q₀.primeCompl _ ‹P.IsPrime› hdisj

  have hy' : algebraMap B (Localization.AtPrime Q₀) y ∉ P.map (algebraMap B (Localization.AtPrime Q₀)) := by
    intro h
    apply hy
    rw [← hunder]
    exact h

  have hsup : P.map (algebraMap B (Localization.AtPrime Q₀)) ⊔
      Ideal.span {algebraMap B (Localization.AtPrime Q₀) y} = maximalIdeal (Localization.AtPrime Q₀) := by
    have hmap : Ideal.map (algebraMap B (Localization.AtPrime Q₀)) Q₀ =
        Ideal.map (algebraMap B (Localization.AtPrime Q₀)) (P ⊔ Ideal.span {y}) := congrArg _ hQ
    rw [← Localization.AtPrime.map_eq_maximalIdeal, hmap, Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  have hmax : (P.map (algebraMap B (Localization.AtPrime Q₀)) ⊔
      Ideal.span {algebraMap B (Localization.AtPrime Q₀) y}).IsMaximal := by
    rw [hsup]
    exact maximalIdeal.isMaximal _

  have hnil' : IsNilpotent (P.map (algebraMap B (Localization.AtPrime Q₀))) := by
    obtain ⟨n, hn⟩ := hnil
    refine ⟨n, ?_⟩
    rw [← Ideal.map_pow, hn]
    simp

  have hpir : IsPrincipalIdealRing
      (Localization.AtPrime Q₀ ⧸ P.map (algebraMap B (Localization.AtPrime Q₀))) := by
    set I := P.map (algebraMap B (Localization.AtPrime Q₀)) with hI
    have : IsLocalRing (Localization.AtPrime Q₀ ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    have hm : maximalIdeal (Localization.AtPrime Q₀ ⧸ I) =
        Ideal.span {Ideal.Quotient.mk I (algebraMap B (Localization.AtPrime Q₀) y)} := by
      have hc : (maximalIdeal (Localization.AtPrime Q₀ ⧸ I)).comap (Ideal.Quotient.mk I) =
          maximalIdeal (Localization.AtPrime Q₀) :=
        eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
      rw [← Ideal.map_comap_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective (maximalIdeal _), hc, ← hsup,
        Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_span, Set.image_singleton]
    have hprin : (maximalIdeal (Localization.AtPrime Q₀ ⧸ I)).IsPrincipal := ⟨⟨_, hm⟩⟩
    exact ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (Localization.AtPrime Q₀ ⧸ I)).out 1 5).mpr hprin

  have htf' : ∀ s ∉ P.map (algebraMap B (Localization.AtPrime Q₀)), ∀ m : LocalizedModule Q₀.primeCompl M,
      s • m = 0 → m = 0 := by
    intro s hs m hsm
    induction s using Localization.induction_on with
    | H x =>
    obtain ⟨a, t⟩ := x
    dsimp only at hs hsm
    have ha : a ∉ P := by
      intro ha
      apply hs
      rw [Localization.mk_eq_mk', IsLocalization.mk'_eq_mul_mk'_one]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha)
    induction m using LocalizedModule.induction_on with
    | h m u =>
      rw [LocalizedModule.mk_smul_mk, ← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at hsm
      obtain ⟨v, hv⟩ := hsm
      simp only [smul_zero, one_smul, Submonoid.smul_def, smul_smul] at hv
      have hva : (v : B) * a ∉ P := fun h =>
        (‹P.IsPrime›.mem_or_mem h).elim (fun h1 => v.2 (hPQ h1)) ha
      rw [htf _ hva m hv, LocalizedModule.zero_mk]

  have hloc : (Ideal.span {y} • ⊤ : Submodule B M).localized' (Localization.AtPrime Q₀) Q₀.primeCompl
      (LocalizedModule.mkLinearMap Q₀.primeCompl M) =
      (Ideal.span {algebraMap B (Localization.AtPrime Q₀) y} • ⊤ :
        Submodule (Localization.AtPrime Q₀) (LocalizedModule Q₀.primeCompl M)) := by
    rw [Submodule.localized'_smul, Submodule.localized'_top, Ideal.localized'_eq_map, Ideal.map_span,
      Set.image_singleton]
  let e := (IsLocalizedModule.linearEquiv Q₀.primeCompl
    ((Ideal.span {y} • ⊤ : Submodule B M).toLocalizedQuotient' (Localization.AtPrime Q₀) Q₀.primeCompl
      (LocalizedModule.mkLinearMap Q₀.primeCompl M))
    (LocalizedModule.mkLinearMap Q₀.primeCompl (M ⧸ (Ideal.span {y} • ⊤ : Submodule B M)))).extendScalarsOfIsLocalization
      Q₀.primeCompl (Localization.AtPrime Q₀)
  rw [← e.length_eq, (Submodule.quotEquivOfEq _ _ hloc).length_eq,
    hG (Localization.AtPrime Q₀) (P.map (algebraMap B (Localization.AtPrime Q₀)))
      (algebraMap B (Localization.AtPrime Q₀) y) (LocalizedModule Q₀.primeCompl M) hnil' hpir hy' hmax htf',
    hL B P Q₀ M hPQ]

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u

noncomputable section

theorem LocalizationAtPrimeQuotient.proof : LocalizationAtPrimeQuotient.Statement.{u} := by
  intro A _ I T P _ W _ hP
  let Q := A ⧸ I
  let B := Localization.AtPrime W ⧸ I.map (algebraMap A (Localization.AtPrime W))

  have hsub : (P.comap (algebraMap Q (Localization T))).primeCompl =
      Algebra.algebraMapSubmonoid Q W.primeCompl := by
    have hmem : ∀ r : A, Ideal.Quotient.mk I r ∈ P.comap (algebraMap Q (Localization T)) ↔ r ∈ W := by
      intro r; rw [← hP]; exact Iff.rfl
    have hIW : I ≤ W := fun r hr => by
      rw [← hmem, Ideal.Quotient.eq_zero_iff_mem.2 hr]; exact Ideal.zero_mem _
    ext q
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
    have h1 : Ideal.Quotient.mk I r ∈ (P.comap (algebraMap Q (Localization T))).primeCompl ↔ r ∉ W :=
      not_congr (hmem r)
    rw [h1]
    constructor
    · intro hr; exact ⟨r, hr, rfl⟩
    · rintro ⟨r', hr', he⟩ hr
      apply hr'
      have : r' - r ∈ I := Ideal.Quotient.eq.1 he
      simpa using W.add_mem (hIW this) hr
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid Q W.primeCompl) (Localization.AtPrime P) := by
    have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization T
      (Localization.AtPrime P) P
    rw [IsLocalization.AtPrime, hsub] at this
    exact this
  let e := IsLocalization.algEquiv (Algebra.algebraMapSubmonoid Q W.primeCompl)
    (Localization.AtPrime P) B
  refine ⟨e.toRingEquiv, fun a => ?_⟩
  have h2 : algebraMap (Localization T) (Localization.AtPrime P)
      (algebraMap Q (Localization T) (Ideal.Quotient.mk I a)) =
      algebraMap Q (Localization.AtPrime P) (Ideal.Quotient.mk I a) :=
    (IsScalarTower.algebraMap_apply Q (Localization T) (Localization.AtPrime P) _).symm
  rw [h2]
  exact e.commutes (Ideal.Quotient.mk I a)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing RingTheory.Sequence Pointwise

universe u

theorem RegularSequenceLengthLeDim.proof : RegularSequenceLengthLeDim.Statement.{u} := by
  suffices key : ∀ (n : ℕ) (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (rs : List R),
      rs.length = n → (∀ r ∈ rs, r ∈ maximalIdeal R) → IsWeaklyRegular R rs →
        (rs.length : WithBot ℕ∞) ≤ ringKrullDim R from
    fun R _ _ _ rs hmem hreg => key _ R rs rfl hmem hreg
  intro n
  induction n with
  | zero =>
    intro R _ _ _ rs hlen _ _
    rw [hlen, Nat.cast_zero]
    exact ringKrullDim_nonneg_of_nontrivial
  | succ n ih =>
    intro R _ _ _ rs hlen hmem hreg
    obtain _ | ⟨r, rs⟩ := rs
    · simp at hlen
    rw [List.length_cons, Nat.succ_inj] at hlen
    rw [isWeaklyRegular_cons_iff] at hreg
    obtain ⟨hr, htail⟩ := hreg
    have hrm : r ∈ maximalIdeal R := hmem r (List.mem_cons_self ..)
    set S := R ⧸ Ideal.span {r}
    have hne : Ideal.span {r} ≠ ⊤ := by
      rw [Ne, Ideal.span_singleton_eq_top]
      exact (mem_maximalIdeal _).mp hrm
    have : Nontrivial S := Ideal.Quotient.nontrivial_iff.mpr hne
    have : IsLocalRing S := IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    have : IsLocalHom (Ideal.Quotient.mk (Ideal.span {r})) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    have hdim : ringKrullDim S + 1 = ringKrullDim R :=
      ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hr hrm
    have heq : (r • ⊤ : Submodule R R) = Ideal.span {r} := by
      rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top]
    have hS : IsWeaklyRegular S rs :=
      (Submodule.quotEquivOfEq _ _ heq).isWeaklyRegular_congr rs |>.mp htail
    have hS' : IsWeaklyRegular S (rs.map (algebraMap R S)) :=
      (isWeaklyRegular_map_algebraMap_iff S S rs).mpr hS
    have hmem' : ∀ s ∈ rs.map (algebraMap R S), s ∈ maximalIdeal S := by
      intro s hs
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
      refine (mem_maximalIdeal _).mpr fun hu => (mem_maximalIdeal _).mp (hmem t (List.mem_cons_of_mem _ ht)) ?_
      exact isUnit_of_map_unit (Ideal.Quotient.mk (Ideal.span {r})) t hu
    have h := ih S _ (by rw [List.length_map, hlen]) hmem' hS'
    rw [List.length_map] at h
    rw [← hdim, List.length_cons, Nat.cast_succ]
    exact add_le_add h le_rfl

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing RingTheory.Sequence Pointwise

def quotSMulTopQuotIdealSMulTopEquiv {B M : Type} [CommRing B] [AddCommGroup M] [Module B M]
    (I : Ideal B) (y : B) :
    QuotSMulTop y (M ⧸ (I • ⊤ : Submodule B M)) ≃ₗ[B]
      (QuotSMulTop y M ⧸ (I • ⊤ : Submodule B (QuotSMulTop y M))) :=
  (Submodule.quotEquivOfEq ((y • (⊤ : Submodule B M)).map (I • (⊤ : Submodule B M)).mkQ) (y • ⊤)
      (by rw [Submodule.map_pointwise_smul, Submodule.map_top, Submodule.range_mkQ])).symm ≪≫ₗ
    Submodule.quotientQuotientEquivQuotientSup (I • ⊤) (y • ⊤) ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (sup_comm _ _) ≪≫ₗ
    (Submodule.quotientQuotientEquivQuotientSup (y • ⊤) (I • ⊤)).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (by rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ])

theorem FlatLocalRegularElement.iterate (h : FlatLocalRegularElement.Statement)
    {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [Algebra A B]
    (hA : IsNoetherianRing A) (hB : IsNoetherianRing B) (hl : IsLocalHom (algebraMap A B))
    (ys : List B) (hys : ∀ y ∈ ys, y ∈ maximalIdeal B)
    (M : Type) [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    (hfin : Module.Finite B M) (hflat : Module.Flat A M)
    (hreg : IsWeaklyRegular (M ⧸ ((maximalIdeal A).map (algebraMap A B) • (⊤ : Submodule B M))) ys) :
    IsWeaklyRegular M ys ∧ Module.Flat A (M ⧸ (Ideal.ofList ys • (⊤ : Submodule B M))) := by
  induction ys generalizing M with
  | nil =>
    refine ⟨IsWeaklyRegular.nil B M, ?_⟩
    have e : (M ⧸ (Ideal.ofList ([] : List B) • (⊤ : Submodule B M))) ≃ₗ[B] M :=
      Submodule.quotEquivOfEqBot _ (by rw [Ideal.ofList_nil, Submodule.bot_smul])
    exact Module.Flat.of_linearEquiv (e.restrictScalars A)
  | cons y ys ih =>
    rw [isWeaklyRegular_cons_iff] at hreg
    obtain ⟨hyM, hflat'⟩ := h A B hA hB hl M hfin hflat y (hys y List.mem_cons_self) hreg.1
    have hfin' : Module.Finite B (QuotSMulTop y M) := inferInstance
    obtain ⟨h1, h2⟩ := ih (fun z hz => hys z (List.mem_cons_of_mem _ hz)) (QuotSMulTop y M) hfin' hflat'
      (((quotSMulTopQuotIdealSMulTopEquiv _ y).isWeaklyRegular_congr ys).mp hreg.2)
    refine ⟨(isWeaklyRegular_cons_iff M y ys).mpr ⟨hyM, h1⟩, ?_⟩
    have : Module.Flat A (QuotSMulTop y M ⧸ (Ideal.ofList ys • (⊤ : Submodule B (QuotSMulTop y M)))) := h2
    exact Module.Flat.of_linearEquiv
      ((Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M y ys).restrictScalars A)

theorem FlatLocalRegularSequence.proof (h : FlatLocalRegularElement.Statement) :
    FlatLocalRegularSequence.Statement := by
  intro A B _ _ _ _ _ hA hB hl hflat rs ys hrs hreg hys hfib
  set I := (maximalIdeal A).map (algebraMap A B) with hI
  have hfib' : IsWeaklyRegular (B ⧸ (I • ⊤ : Submodule B B)) ys := by
    have e : (B ⧸ I) ≃ₗ[B] (B ⧸ (I • ⊤ : Submodule B B)) :=
      Submodule.quotEquivOfEq _ _ (by rw [Ideal.smul_eq_mul, Ideal.mul_top])
    rw [← Ideal.Quotient.algebraMap_eq, isWeaklyRegular_map_algebraMap_iff] at hfib
    exact (e.isWeaklyRegular_congr ys).mp hfib
  obtain ⟨hysB, hflatQ⟩ :=
    FlatLocalRegularElement.iterate h hA hB hl ys hys B inferInstance hflat hfib'
  have hrsN : IsWeaklyRegular (B ⧸ (Ideal.ofList ys • (⊤ : Submodule B B))) rs :=
    ((TensorProduct.lid A _).isWeaklyRegular_congr rs).mp (hreg.isWeaklyRegular_rTensor)
  have happ : IsWeaklyRegular B (ys ++ rs.map (algebraMap A B)) :=
    (isWeaklyRegular_append_iff B ys _).mpr
      ⟨hysB, (isWeaklyRegular_map_algebraMap_iff B _ rs).mpr hrsN⟩
  have : IsNoetherian B B := hB
  refine IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal happ List.perm_append_comm ?_
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact hys r hr
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact fun hu => (IsLocalRing.mem_maximalIdeal a).mp (hrs a ha) (isUnit_of_map_unit _ _ hu)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def CurveProperClosedFinite.Statement : Prop :=
  ∀ (n : ℕ) (W K : Ideal (MvPolynomial (Fin n) ℂ)), W.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = 1 → ¬ K ≤ W →
      (zeroSet W ∩ zeroSet K).Finite

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

def FiniteProjHomInjective.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → (projHom J A).toRingHom.Finite →
      Function.Injective (projHom J A)

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle030
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LiftFormNotMemBlowUpOf
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle055
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpLocalChart
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle044
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle040
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle043
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle033
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle034
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle031
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle026
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle049
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle053
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpValuationCentre
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
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
public import Mathlib.RingTheory.Valuation.LocalSubring
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem prime_eq_or_eq_of_le_mem_minimalPrimes_sup_span {A : Type*} [CommRing A] [IsNoetherianRing A]
    {P W Q : Ideal A} (hP : P.IsPrime) (hQ : Q.IsPrime) {x : A}
    (hW : W ∈ (P ⊔ Ideal.span {x}).minimalPrimes) (hPQ : P ≤ Q) (hQW : Q ≤ W) : Q = P ∨ Q = W := by
  by_contra h
  rw [not_or] at h
  obtain ⟨hQP, hQW'⟩ := h
  have hWp : W.IsPrime := hW.1.1
  let f := Ideal.Quotient.mk P
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker f ≤ Q := by rw [Ideal.mk_ker]; exact hPQ
  have hkerW : RingHom.ker f ≤ W := hker.trans hQW
  have : (Q.map f).IsPrime := Ideal.map_isPrime_of_surjective hf hker
  have : (W.map f).IsPrime := Ideal.map_isPrime_of_surjective hf hkerW
  have : (⊥ : Ideal (A ⧸ P)).IsPrime := Ideal.isPrime_bot
  have h1 : (⊥ : Ideal (A ⧸ P)) < Q.map f := by
    refine bot_lt_iff_ne_bot.mpr fun h0 => hQP (le_antisymm (fun q hq => ?_) hPQ)
    have hq' : f q ∈ Q.map f := Ideal.mem_map_of_mem f hq
    rw [h0, Ideal.mem_bot] at hq'
    exact Ideal.Quotient.eq_zero_iff_mem.mp hq'
  have h2 : Q.map f < W.map f := by
    refine lt_of_le_of_ne (Ideal.map_mono hQW) fun e => hQW' ?_
    have e' := congrArg (Ideal.comap f) e
    rwa [Ideal.comap_map_of_surjective' f hf, Ideal.comap_map_of_surjective' f hf,
      sup_eq_left.mpr hker, sup_eq_left.mpr hkerW] at e'
  have e1 := Ideal.height_add_one_le_of_lt_of_isPrime h1
  have e2 := Ideal.height_add_one_le_of_lt_of_isPrime h2
  have e3 := Ideal.map_height_le_one_of_mem_minimalPrimes hW
  rw [Ideal.height_bot] at e1
  have e4 : (0 : ℕ∞) + 1 + 1 ≤ 1 := ((add_le_add e1 le_rfl).trans e2).trans e3
  norm_num at e4

theorem eq_blowUpOf_of_comap_liftForm_le {K : Type} [DecidableEq K] {ι : K → Type} {J : Type} {R : Type*}
    [CommRing R] {P : Ideal (MRing ι R)} {u : J → MRing ι R} {Q : Ideal (MRing (extIdx ι J) R)}
    (hQp : Q.IsPrime) (hQh : IsMultiHomogIdeal Q) (hle : blowUpOf P u ≤ Q) {j : J}
    (hj : (newVar j : MRing (extIdx ι J) R) ∉ Q)
    (hc : Q.comap (liftForm (ι := ι) (J := J) (R := R)) ≤ P) : Q = blowUpOf P u := by
  classical
  refine le_antisymm (fun F hF => ?_) hle
  have hcomp : ∀ b, weightedHomogeneousComponent (blockWeight (extIdx ι J)) b F ∈ blowUpOf P u := by
    intro b
    set G := weightedHomogeneousComponent (blockWeight (extIdx ι J)) b F
    have hG : IsMultiHomog G b := weightedHomogeneousComponent_isWeightedHomogeneous _ _
    have hGQ : G ∈ Q := hQh F hF b
    obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective (blowUpEval P u G)
    have hrel : liftForm (u j) ^ (b none) * G - newVar j ^ (b none) * liftForm f ∈ blowUpOf P u := by
      rw [blowUpOf, RingHom.mem_ker, map_sub, map_mul, map_mul, map_pow, map_pow,
        aeval_blowUpSubst_of_isMultiHomog P u hG, aeval_blowUpSubst_liftForm, aeval_blowUpSubst_liftForm,
        aeval_blowUpSubst_newVar, ← hf]
      ring
    have h1 : newVar j ^ (b none) * liftForm f ∈ Q := by
      have h := Q.sub_mem (Q.mul_mem_left (liftForm (u j) ^ (b none)) hGQ) (hle hrel)
      rwa [sub_sub_cancel] at h
    have h2 : liftForm f ∈ Q :=
      (hQp.mem_or_mem h1).resolve_left fun h => hj (hQp.mem_of_pow_mem _ h)
    have h3 : f ∈ P := hc h2
    rw [blowUpOf, RingHom.mem_ker, aeval_blowUpSubst_of_isMultiHomog P u hG, ← hf,
      Ideal.Quotient.eq_zero_iff_mem.mpr h3, map_zero, zero_mul]
  rw [← sum_weightedHomogeneousComponent (blockWeight (extIdx ι J)) F]
  exact finsum_induction (· ∈ blowUpOf P u) (Submodule.zero_mem _) (fun _ _ => Submodule.add_mem _) hcomp

theorem BlowUpOverLocFamilyFinite.proof (h₁ : BlowUpOverLocFibreFinite.Statement.{u}) :
    BlowUpOverLocFamilyFinite.Statement.{u} := by
  intro O _ _ _ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hWmin hWrel
  have hPp : P.IsPrime := hP.multiProj.isPrime
  refine ((Set.finite_singleton (blowUpOf P u)).union
    (h₁ O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel)).subset ?_
  rintro Q ⟨hQp, hQh, hQr, hQle, hQW⟩
  obtain ⟨hcp, hPc, -, j, hj⟩ := comap_liftForm_facts hQp hQle hQr
  rcases prime_eq_or_eq_of_le_mem_minimalPrimes_sup_span hPp hcp hWmin hPc hQW with h | h
  · exact Or.inl (eq_blowUpOf_of_comap_liftForm_le hQp hQh hQle hj h.le)
  · exact Or.inr ⟨hQp, hQh, hQr, hQle, h⟩

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx ptCoord)

namespace ChernClassOnFlagPair

theorem fieldNum_spec (F : Type) [Field F] {K : Type} [Fintype K] (κ : K → Type) [∀ k, Fintype (κ k)] :
    IsFieldIntersection (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum F κ) := by
  classical
  exact Classical.epsilon_spec (p := fun I : IFamily F κ => IsFieldIntersection I)
    ⟨_, IntNumIsFieldIntersection.full F K κ⟩

theorem append_pullDeg {K K' : Type} {a b : ℕ} (u : Fin a → K → ℤ) (v : Fin b → K → ℤ) :
    Fin.append (fun i => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := K') (u i))
        (fun j => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := K') (v j)) =
      fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := K') (Fin.append u v l) := by
  funext l
  induction l using Fin.addCases with
  | left i => simp
  | right j => simp

theorem isVertDiv_one {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {K : Type}
    [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι O)} (hP : P.IsPrime)
    (b : K → ℤ) (hb : b = 0) : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O P b 1 1 := by
  subst hb
  have h1 : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (1 : MRing ι O) 0 := by
    simpa using IndefiniteRowSideFullHecke.NumbersDVR.Bundles.isMultiHomog_C O (ι := ι) (1 : O)
  refine ⟨⟨0, 0, h1, h1, by simp⟩, ?_, ?_, fun Q hQ _ _ => ⟨1, 1, ⟨0, h1⟩, ⟨0, h1⟩, ?_, ?_, by simp⟩⟩
  · exact fun h => hP.ne_top ((Ideal.eq_top_iff_one P).mpr h)
  · exact fun h => hP.ne_top ((Ideal.eq_top_iff_one P).mpr h)
  · exact fun h => hQ.1.ne_top ((Ideal.eq_top_iff_one Q).mpr h)
  · exact fun h => hQ.1.ne_top ((Ideal.eq_top_iff_one Q).mpr h)

theorem length_classList {K σ : Type*} (cls : σ → K → ℤ) (μ : σ →₀ ℕ) :
    (classList cls μ).length = μ.degree := by
  simp [classList, Finsupp.card_toMultiset, Finsupp.sum]
  rfl

theorem isFlagPair_self {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    {Ω : Type} [Field Ω] [Algebra O Ω] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    {y : (Σ k, ι k) → Ω} [(pointIdeal O y).IsPrime] {N : ℕ} {E : Type} [AddCommGroup E] [Module Ω E]
    {B : ChartBundle O (segreVec y) N E} {w : Module.Basis (Fin N) Ω E} {x : Fin N → K → ℤ}
    (h : IsFlagFrame y B w x) :
    IsFlagPair ϖ y B B w w x x (fun _ => 1) (fun _ => 1) := by
  refine ⟨h, h, ?_, ?_, ?_⟩
  · intro i j hij
    rw [Module.Basis.repr_self, Finsupp.single_apply, ite_eq_right hij.ne]
  · intro i
    rw [sub_self]
    exact isVerticalDivisor_one ϖ _
  · intro i
    simp [Module.Basis.repr_self]

end ChernClassOnFlagPair


open ChernClassOnFlagPair in
theorem ChernClassOnFlagPair.proof (h1 : JoinPointFlagModel.Statement)
    (h2 : JoinPointNumbers.Statement) (h3 : FlagModelValueIndependence.Statement)
    (h4 : FlagModelRootIndependence.Statement) (h5 : plainPolynomialPairNumber.Statement)
    (h6 : RootPolynomialNumber.Statement) (h7 : PairNumberExpansionIndependence.Statement)
    (h8 : dividedDifferenceExpansion.Statement) : ChernClassOnFlagPair.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hK hW N E _ _ B B' hBB' w w' x x' f g hfp
  have hW2 : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O y) d :=
    (BundleExamples.isModelOver_iff O _ d).mpr ⟨hK, hW⟩
  have hprime : (pointIdeal O y).IsPrime := hW2.2.1.1
  refine ⟨fun k hk1 hk2 Gs hGs q L Q hQ => ?_, fun c G hsym hG hc q L Q hQ a ha => ?_⟩
  · obtain ⟨EB, E'B, φ, hm, hb, hp, hp', hd, hd', hf, hg⟩ :=
      h1 O ϖ hϖ Ω K ι y d hW N E B B' hBB' w w' x x' f g hfp
    let F₀ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagModel O y d N B B' :=
      { K' := Unit, ι' := ptIdx, z := ptCoord, model := hm, birat := hb, EB := EB, E'B := E'B,
        pull := hp, pull' := hp', flag := φ }
    have hne : Nonempty (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagModel O y d N B B') := ⟨F₀⟩
    have hv : F₀.value O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum (IsLocalRing.ResidueField O) (Sum.elim ι ptIdx))
        (psum (Fin N) ℤ k) L L (fun _ => 1) (fun _ => 1) Q =
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum (IsLocalRing.ResidueField O) (Sum.elim ι ptIdx))
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord y (ptCoord (Ω := Ω)))) d
          (Fin.append (fun i => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (x i))
            fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (L l))
          (Fin.append (fun i => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (x' i))
            fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (L l))
          (Fin.append (fun i => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) (f i))
            fun _ => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) 1)
          (Fin.append (fun i => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) (g i))
            fun _ => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) 1)
          (rename (Fin.castAdd q) (psum (Fin N) ℤ k) * rename (Fin.natAdd N) Q) := by
      show IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O _ _ d (Fin.append φ.deg _) (Fin.append φ.deg' _)
        (Fin.append φ.f _) (Fin.append φ.g _) _ = _
      rw [hd, hd', hf, hg]
    have hW' : ∀ H : MvPolynomial (Fin (N + q)) ℤ, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum (IsLocalRing.ResidueField O) (Sum.elim ι ptIdx))
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord y (ptCoord (Ω := Ω)))) d
          (Fin.append (fun i => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (x i))
            fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (L l))
          (Fin.append (fun i => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (x' i))
            fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (L l))
          (Fin.append (fun i => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) (f i))
            fun _ => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) 1)
          (Fin.append (fun i => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) (g i))
            fun _ => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) 1) H =
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O (fun V _ bs => intNum (IsLocalRing.ResidueField O) V bs)
          (pointIdeal O y) d (Fin.append x L) (Fin.append x' L) (Fin.append f fun _ => 1)
          (Fin.append g fun _ => 1) H := by
      intro H
      unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum
      simp only [append_pullDeg]
      refine Finset.sum_congr rfl fun l _ => ?_
      induction l using Fin.addCases with
      | left i =>
        simp only [Fin.append_left]
        exact (h2 O ϖ hϖ Ω K ι y d hW _ _ _).1 _ _ _ (hfp.vertical i)
      | right j =>
        simp only [Fin.append_right, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc, sub_self,
          IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval, Finsupp.sum_zero_index]
    unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ck
    rw [dite_eq_left hne]
    let _ := (Classical.choice hne).finK
    let _ := (Classical.choice hne).finι
    refine (h3 O Ω K ι y d N E B B' hW2 ((BundleExamples.sameGeneric_iff hϖ y B B').mpr hBB')
      (Classical.choice hne) F₀ _ _ (fieldNum_spec _ _) (fieldNum_spec _ _) (psum (Fin N) ℤ k)
      (psum_isSymmetric _ _ k) q L L (fun _ => 1) (fun _ => 1)
      (fun l => isVertDiv_one hprime _ (sub_self _)) k Q hk2 (isHomogeneous_psum N k) hQ).trans ?_
    refine hv.trans ((hW' _).trans ((h5 O K ι (pointIdeal O y) d N x x' f g k (psum (Fin N) ℤ k)
      (isHomogeneous_psum N k) hk2 q L Q hQ).trans ?_))
    refine Finset.sum_congr rfl fun μ hμ => ?_
    have hlen : (classList L μ).length + k = d + 1 := by
      have h := hQ (mem_support_iff.mp hμ)
      rw [length_classList, Finsupp.degree_eq_weight_one]
      have : Finsupp.weight (fun _ => 1) μ = Finsupp.weight 1 μ := rfl
      omega
    rw [h7 O ϖ hϖ K ι (pointIdeal O y) d hW N x x' f g hfp.vertical k (psum (Fin N) ℤ k)
      (isHomogeneous_psum N k) _ Gs (h8 N k _ (isHomogeneous_psum N k)) hGs (classList L μ) hlen]
  · have hsame : SameGenericFibre ϖ B B := fun c _ =>
      ⟨fun v hv => ⟨0, by simpa using hv⟩, fun v hv => ⟨0, by simpa using hv⟩⟩
    obtain ⟨EB, E'B, φ, hm, hb, hp, hp', hd, -, -, -⟩ :=
      h1 O ϖ hϖ Ω K ι y d hW N E B B hsame w w x x _ _ (isFlagPair_self hfp.flag)
    let F₀ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagModel O y d N B B :=
      { K' := Unit, ι' := ptIdx, z := ptCoord, model := hm, birat := hb, EB := EB, E'B := E'B,
        pull := hp, pull' := hp', flag := φ }
    have hne : Nonempty (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagModel O y d N B B) := ⟨F₀⟩
    have hv : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O (fun W => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum (IsLocalRing.ResidueField O) (Sum.elim ι F₀.ι')) W d
          (Fin.append F₀.flag.deg fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := F₀.K') (L l))
          (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q))
        (Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero (ReciprocityTheory.ChartRestriction.G.Geo.divCycle
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord y F₀.z)) (C a))) =
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O (fun W => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum (IsLocalRing.ResidueField O) (Sum.elim ι ptIdx)) W d
          (fun j => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (Fin.append x L j))
          (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q))
        (Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero (ReciprocityTheory.ChartRestriction.G.Geo.divCycle
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord y (ptCoord (Ω := Ω))))
          (C a))) := by
      show IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O (fun W => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum _ W d
          (Fin.append φ.deg _) _) _ = _
      rw [hd, append_pullDeg]
    unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.rootNum
    rw [dite_eq_left hne]
    let _ := (Classical.choice hne).finK
    let _ := (Classical.choice hne).finι
    refine (h4 O Ω K ι y d N E B B hW2 ((BundleExamples.sameGeneric_iff hϖ y B B).mpr hsame)
      (Classical.choice hne) F₀ _ _ (fieldNum_spec _ _) (fieldNum_spec _ _) c G hsym hG hc q L Q hQ a
      ha).trans ?_
    refine hv.trans (((h2 O ϖ hϖ Ω K ι y d hW _ _ _).2 a ha).trans ?_)
    exact h6 O K ι (pointIdeal O y) d N x c G hG hc q L Q hQ a

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)

namespace FlagModelValueIndependence

theorem fieldNum_isFieldIntersection (F : Type) [Field F] {K : Type} [Fintype K] (κ : K → Type)
    [∀ k, Fintype (κ k)] : IsFieldIntersection (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum F κ) := by
  classical
  exact Classical.epsilon_spec (p := fun I : IFamily F κ => IsFieldIntersection I)
    ⟨_, IntNumIsFieldIntersection.full F K κ⟩

theorem pullDeg_sub {K K' : Type} (a b : K → ℤ) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := K') (a - b) =
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := K') a - IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := K') b := by
  funext k
  cases k <;> simp [IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg]

theorem proof (hOne : FlagPairValueIndependence.Statement) (hCommon : FlagModelCommonModel.Statement) :
    FlagModelValueIndependence.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x d N V _ _ E E' hW hE F₁ F₂ I₁ I₂ hI₁ hI₂ G hG r y y' f g hv c Q hc hGc hQ
  obtain ⟨K'', _, ι'', _, z, EB, E'B, φ₁, φ₂, hZ, -, -, -, hS, hpull, hval⟩ :=
    hCommon O Ω K ι x d N V E E' hW hE F₁ F₂
  have hI := fieldNum_isFieldIntersection (IsLocalRing.ResidueField O) (Sum.elim ι ι'')
  obtain ⟨h₁, h₂⟩ := hval _ I₁ I₂ hI hI₁ hI₂ G r y y' f g hv c Q hc hGc hQ
  rw [h₁, h₂]
  refine hOne O Ω (K ⊕ K'') (Sum.elim ι ι'') (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord x z) d N V EB E'B hZ hS
    φ₁ φ₂ _ hI G hG r (fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (y l))
    (fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (y' l))
    (fun l => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ι'') (f l))
    (fun l => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ι'') (g l)) (fun l => ?_) c Q hc hGc hQ
  rw [← pullDeg_sub]
  exact hpull _ _ _ (hv l)

end FlagModelValueIndependence

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (joinCoord midDeg midVar assocDeg assocVar midSwapBlocks midSwapVars
  midSwapVars_fst joinCoord_comp_midSwapVars)

namespace PairNumberJoinRight

variable {K K' K₂ : Type} {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type}

theorem assocDeg_comp_midSwapBlocks (a : K ⊕ K' → ℤ) :
    assocDeg (K₂ := K₂) a ∘ midSwapBlocks = midDeg (K₂ := K₂) a := by
  funext k
  rcases k with k | k | k <;> rfl

theorem midSwapVars_comp_midVar :
    ⇑(midSwapVars ι ι' ι₂) ∘ midVar (ι := ι) (ι' := ι') ι₂ = assocVar ι₂ := by
  funext p
  obtain ⟨k | k, i⟩ := p <;> rfl

theorem midDeg_sub (a b : K ⊕ K' → ℤ) :
    midDeg (K₂ := K₂) a - midDeg (K₂ := K₂) b = midDeg (K₂ := K₂) (a - b) := by
  funext k
  rcases k with k | k | k <;> simp [midDeg]

end PairNumberJoinRight


open PairNumberJoinRight in
theorem PairNumberJoinRight.proof (hLeft : PairNumberJoinLeft.Statement)
    (hVert : JoinVerticalDivisorRight.Statement) (hRel : PairNumberRelabelAlt.Statement) :
    PairNumberJoinRight.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x K' _ ι' _ z K₂ _ ι₂ _ w d hF hZ hfn I I₁ hI hI₁ n a a' f g hv H hH
  classical
  have hy := joinCoord_comp_midSwapVars x z w
  obtain ⟨hZL, hfnL, -, hnum⟩ := hRel O Ω (K ⊕ (K₂ ⊕ K')) (Sum.elim ι (Sum.elim ι₂ ι'))
    (K ⊕ (K' ⊕ K₂)) (Sum.elim ι (Sum.elim ι' ι₂)) midSwapBlocks (midSwapVars ι ι' ι₂) midSwapVars_fst
    (joinCoord x (joinCoord z w)) d (by rw [hy]; exact hZ)
  have hIL : IsFieldIntersection (F := IsLocalRing.ResidueField O) (ι := Sum.elim ι (Sum.elim ι' ι₂))
      (fun V _ L => intNum (IsLocalRing.ResidueField O) V L) :=
    IntNumIsFieldIntersection.full _ _ _
  rw [hLeft O Ω K ι x K' ι' z K₂ ι₂ w d hF hZL (hfnL.trans (by rw [hy]; exact hfn)) _ I₁ hIL hI₁ n a a'
    f g hv H hH]
  have key := hnum I _ hI hIL n (fun i => assocDeg (K₂ := K₂) (a i)) (fun i => assocDeg (K₂ := K₂) (a' i))
    (fun i => rename (midVar ι₂) (f i)) (fun i => rename (midVar ι₂) (g i)) (fun i => by
      rw [hy, assocDeg_comp_midSwapBlocks, assocDeg_comp_midSwapBlocks, midDeg_sub]
      exact hVert O Ω K ι x K' ι' z K₂ ι₂ w _ _ _ (hv i)) H hH
  simp only [hy, assocDeg_comp_midSwapBlocks, rename_rename, midSwapVars_comp_midVar] at key
  exact key.symm

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem BlowUpOverLocCentreDom.proof : BlowUpOverLocCentreDom.Statement.{u} := by
  intro O _ _ _ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hWmin hWrel
  have := hP.multiProj.isPrime
  intro 𝔫 h𝔫
  have hW : W.IsPrime := hWmin.1.1
  have hPW : P ≤ W := le_sup_left.trans hWmin.1.2
  obtain ⟨V, hBV, hnV⟩ := Ideal.image_subset_nonunits_valuationSubring 𝔫 h𝔫.ne_top
  obtain ⟨W', hp, hh, hr, hb, hc, hloc⟩ := exists_blowUp_centre (J := J) P W hP.multiProj.multiHomog hW hPW
    hWrel N u hu hu' V ((homLocRing_le_blowUpOverLoc P W u).trans hBV)
  have h : blowUpOverLoc P W u ≤ blowUpLocRing P u W' := iInf₂_le W' ⟨hp, hh, hr, hb, hc⟩
  refine ⟨W', hp, hh, hr, hb, hc, h, fun y hy hunit => ?_⟩
  obtain ⟨w, hw⟩ := hunit
  obtain ⟨hyV, hymax⟩ := (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal (A := V)).1
    (hnV ⟨y, hy, rfl⟩)
  have hinv : ((w⁻¹ : (blowUpLocRing P u W')ˣ) : FractionRing (MRing ι O ⧸ P)) ∈ V := hloc ((w⁻¹ : (blowUpLocRing P u W')ˣ) : blowUpLocRing P u W').2
  have hmul : (y : FractionRing (MRing ι O ⧸ P)) * ((w⁻¹ : (blowUpLocRing P u W')ˣ) : _) = 1 := by
    have h1 := congrArg Subtype.val w.mul_inv
    rw [hw] at h1
    exact h1
  exact (IsLocalRing.mem_maximalIdeal _).1 hymax (IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext hmul))

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

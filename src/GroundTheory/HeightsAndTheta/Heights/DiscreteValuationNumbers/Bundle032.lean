module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.CutIdentityRightSideCongrOfSubMem
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleMul
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Statements
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

section

variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]

theorem divCycle_nonneg (P : Ideal (MRing ι R)) (x : MRing ι R) (W : Ideal (MRing ι R)) :
    0 ≤ divCycle P x W := by
  unfold divCycle
  split_ifs <;> simp

theorem divCycle_eq_zero_of_form_not_mem (P : Ideal (MRing ι R)) {x : MRing ι R} {W : Ideal (MRing ι R)}
    (hx : x ∉ W) : divCycle P x W = 0 := by
  unfold divCycle
  rw [dite_eq_right]
  exact fun h => hx (h.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x)))

end

theorem ExcessPositive.proof : ExcessPositive.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD s hsP ⟨G, hϖG, hsG, hDG⟩
  have hPp : P.IsPrime := hP.multiProj.isPrime
  have hGdef : G ∈ (P ⊔ Ideal.span {s}).minimalPrimes ∧ IsRelevant G := by
    by_contra h
    exact hsG (by unfold divCycle; rw [dite_eq_right h])
  have hGp : G.IsPrime := hGdef.1.1.1
  have hPG : P ≤ G := le_sup_left.trans hGdef.1.1.2
  obtain ⟨u, v, huG, huv⟩ := hD.2 G hGp hPG hGdef.2
  have huP : u ∉ P := fun h => huG (hPG h)
  have hfP := hD.1.num_not_mem
  have hgP := hD.1.den_not_mem
  have hvP : v ∉ P := by
    intro hv
    have h1 : u * f ∈ P := by
      have h2 := P.add_mem huv (P.mul_mem_right g hv)
      rwa [sub_add_cancel] at h2
    exact (hPp.mem_or_mem h1).elim huP hfP
  have hcyc : divCycle P (u * f) G = divCycle P (v * g) G :=
    congrFun (divCycle_congr_of_sub_mem huv) G
  have huf := congrFun (DivCycleMul.proof O K ι P u f hPp huP hfP) G
  have hvg := congrFun (DivCycleMul.proof O K ι P v g hPp hvP hgP) G
  simp only [Pi.add_apply] at huf hvg
  have hu0 := divCycle_eq_zero_of_form_not_mem P huG
  have hv0 := divCycle_nonneg P v G
  have hs0 := divCycle_nonneg P s G
  have hDpos : 0 < ratDiv P f g G := by
    unfold ratDiv at hDG ⊢
    omega
  have hprod : 0 < (divCycle P s G * ratDiv P f g G).toNat := by
    have : 0 < divCycle P s G * ratDiv P f g G := mul_pos (lt_of_le_of_ne hs0 (Ne.symm hsG)) hDpos
    omega

  have hfin := DivCycleFiniteSupport.proof.{u} O K ι P s
  have hbdd : BddAbove (Set.range fun G' : {G' : Ideal (MRing ι O) // (C ϖ : MRing ι O) ∈ G'} =>
      (divCycle P s G'.1 * ratDiv P f g G'.1).toNat) := by
    apply Set.Finite.bddAbove
    apply ((hfin.image fun G' => (divCycle P s G' * ratDiv P f g G').toNat).insert 0).subset
    rintro _ ⟨G', rfl⟩
    by_cases h : divCycle P s G'.1 = 0
    · left
      simp [h]
    · right
      exact ⟨G'.1, h, rfl⟩
  exact lt_of_lt_of_le hprod (le_ciSup hbdd ⟨G, hϖG⟩)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem BlowUpReduction.proof (hpieces : BlowUpDecomposition.Statement.{u})
    (hinv : BlowUpInvariance.Statement.{u}) (hcf : CommonFactorRemoval.Statement.{u})
    (hadd : AdditivityInDivisor.Statement.{u}) (hrhs : RightSideMultiplicativeInForm.Statement.{u})
    (hlhs : LeftSideAdditiveInDegree.Statement.{u}) (htaut : TautologicalCase.Statement.{u}) :
    BlowUpReduction.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH L hId₁ hId₀
  obtain ⟨hmodel, hsl, hslP, hY₀P, hD₁, hE, hH₁, -⟩ :=
    hpieces O ϖ hϖ K ι P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH
  obtain ⟨hinvl, hinvr⟩ := hinv O ϖ hϖ K ι P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH L
  set Q := blowUpOf P (blowUpGens s g f m e)
  set Y₀ : MRing (extIdx ι (BlowUpIdx ι)) O := newVar none
  set Y₁ : MRing (extIdx ι (BlowUpIdx ι)) O := newVar (some none)
  have hQ : Q.IsPrime := hmodel.multiProj.isPrime
  have hfmQ := hE.1.num_not_mem
  have hgYQ := hE.1.den_not_mem
  rw [map_mul] at hfmQ
  have hfQ : liftForm f ∉ Q := fun h => hfmQ (Q.mul_mem_right _ h)
  have hgQ : liftForm g ∉ Q := fun h => hgYQ (Q.mul_mem_right _ h)
  have hqQ : liftForm m * Y₁ ∉ Q := fun h =>
    (hQ.mem_or_mem h).elim hD₁.1.den_not_mem hD₁.1.num_not_mem

  have hcfq := hcf O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) Q d hmodel (liftDeg b) (liftForm f)
    (liftForm g) (liftForm m * Y₁) (liftForm s) hfQ hgQ hqQ hslP (fun H hH hϖH => by
      obtain ⟨h₁, h₂⟩ := hH₁ H hH hϖH
      have hHp := isPrime_of_divCycle_ne_zero hH
      refine ⟨fun h => h₂.num_not_mem ?_, fun h => h₂.den_not_mem (H.mul_mem_right _ h),
        fun h => (hHp.mem_or_mem h).elim h₁.den_not_mem h₁.num_not_mem⟩
      rw [map_mul]; exact H.mul_mem_right _ h) (liftMDeg c) (liftDegs L)
  obtain ⟨haddl, haddr⟩ := hadd O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) Q d hmodel _ _ _ _ _ _
    hD₁.1 hE.1 (liftMDeg c) (liftForm s) hsl hslP hH₁ (liftDegs L)
  have hnum : Y₁ * liftForm (f * m) = liftForm f * (liftForm m * Y₁) := by rw [map_mul]; ring
  have hden : liftForm m * (liftForm g * Y₁) = liftForm g * (liftForm m * Y₁) := by ring
  have hdeg : residualDeg e + exceptionalDeg b e = liftDeg b := by
    funext o; cases o <;> simp [residualDeg, exceptionalDeg, liftDeg]
  rw [hnum, hden, hcfq.1] at haddl
  rw [hnum, hden, hdeg, hcfq.2] at haddr

  obtain ⟨bf, bg, hbf, hbg, hb⟩ := hE.1.degrees
  have ht := htaut O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) Q d hmodel _ _ _ hE.1 bf bg hbf hbg hb
    (liftDegs L)
  have hdegs : liftMDeg c + bg = bf + Pi.single none 1 := by
    funext o
    have h := congrFun hb o
    cases o with
    | none => simp [exceptionalDeg, liftDeg, liftMDeg] at h ⊢; omega
    | some k => simp [exceptionalDeg, liftDeg, liftMDeg] at h ⊢; have := he k; omega
  have hl₁ := hlhs O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) Q d hmodel _ _ _ hE.1 (liftMDeg c) bg
    (liftDegs L)
  have hl₂ := hlhs O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) Q d hmodel _ _ _ hE.1 bf
    (Pi.single none 1) (liftDegs L)
  rw [hdegs] at hl₁
  have hrel := cutIdentityRightSide_congr_of_sub_mem ϖ Q (exceptionalDeg b e) (liftForm (f * m))
    (liftForm g * Y₁) (blowUp_relation P s g f m e) (liftDegs L)
  have hsg : liftForm (s * g) * Y₁ = liftForm s * (liftForm g * Y₁) := by rw [map_mul]; ring
  rw [hsg, hrhs O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) Q d hmodel _ _ _ _ _ hslP hE.1.den_not_mem,
    hrhs O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) Q d hmodel _ _ _ _ _ hE.1.num_not_mem hY₀P] at hrel
  rw [cutIdentity_iff] at hId₁ hId₀ ⊢
  rw [← hinvl, ← hinvr]
  linarith

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

private theorem lt_natCast_of_add_one_le' {x : WithBot ℕ∞} {n : ℕ} (h : x + 1 ≤ (n : WithBot ℕ∞)) :
    x < (n : WithBot ℕ∞) := by
  induction x with
  | bot => exact WithBot.bot_lt_coe _
  | coe e =>
    have h' : e + 1 ≤ (n : ℕ∞) := by exact_mod_cast h
    have h'' : e < (n : ℕ∞) := (ENat.add_one_le_iff' (ENat.natCast_ne_top n)).mp h'
    exact_mod_cast h''

theorem TautologicalCase.proof (h3 : IntNumAddFirst.Statement.{u}) (h5 : MinimalPrimeMultiHomog.Statement.{u})
    (h6 : SupSpanMultiHomog.Statement.{u}) (h7 : SpecialQuotDim.Statement.{u})
    (h8 : SpecialIdealCorresp.Statement.{u}) (h9 : SpecialIdealMultiHomog.Statement.{u})
    (h10 : DimStrictDrop.Statement.{u}) : TautologicalCase.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD cf cg hf hg hb L

  have hfin : ∀ x : MRing ι O, (Function.support (divCycle P x)).Finite := fun x =>
    (Ideal.finite_minimalPrimes_of_isNoetherianRing _ (P ⊔ Ideal.span {x})).subset fun W hW => by
      by_contra hmin
      exact hW (by unfold divCycle; rw [dite_eq_right]; exact fun h => hmin h.1)
  have hZfin : (Function.support (ratDiv P f g)).Finite :=
    ((hfin f).union (hfin g)).subset fun W hW => by
      by_contra h
      simp only [Set.mem_union, Function.mem_support, not_or, not_not] at h
      exact hW (by simp [ratDiv, h.1, h.2])
  have hPmh : IsMultiHomogIdeal P := hP.multiProj.multiHomog
  have : P.IsPrime := hP.multiProj.isPrime
  have hϖP : (C ϖ : MRing ι O) ∉ P := by
    intro h
    have h' : ϖ ∈ P.comap (C : O →+* MRing ι O) := h
    rw [hP.noTorsion, Ideal.mem_bot] at h'
    exact hϖ.ne_zero h'

  have hmh : ∀ (x : MRing ι O) (e : K → ℕ), IsMultiHomog x e → ∀ W, divCycle P x W ≠ 0 →
      IsMultiHomogIdeal W ∧ W.IsPrime ∧ P ≤ W := by
    intro x e he W hW
    unfold divCycle at hW
    split_ifs at hW with hW'
    · exact ⟨h5 O K ι _ W (h6 O K ι P x e hPmh he) hW'.1, hW'.1.1.1, le_sup_left.trans hW'.1.1.2⟩
    · exact absurd rfl hW

  have hadd : ∀ W, ratDiv P f g W ≠ 0 → vNum W (Matrix.vecCons b L) =
      vNum W (Matrix.vecCons (fun k => (cf k : ℤ)) L) - vNum W (Matrix.vecCons (fun k => (cg k : ℤ)) L) := by
    intro W hW
    have hϖW : (C ϖ : MRing ι O) ∈ W := hD.vertical W hW
    obtain ⟨hWm, hWp, hPW⟩ : IsMultiHomogIdeal W ∧ W.IsPrime ∧ P ≤ W := by
      by_cases hWf : divCycle P f W = 0
      · exact hmh g cg hg W fun hWg => hW (by simp [ratDiv, hWf, hWg])
      · exact hmh f cf hf W hWf
    have hdrop := h10 (MRing ι O) P W (lt_of_le_of_ne hPW fun e => hϖP (e ▸ hϖW))
    rw [hP.dim, show d + 1 + 1 + Fintype.card K = d + 2 + Fintype.card K by omega] at hdrop
    have hdim : ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal W) <
        ((d + 2 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
      rw [h7 O ϖ hϖ K ι W hϖW]
      exact lt_natCast_of_add_one_le' hdrop
    have key := h3 (IsLocalRing.ResidueField O) K ι d (specialIdeal W)
      (h8 O ϖ hϖ K ι P W hWp hϖW).1 (h9 O K ι W hWm) hdim b (fun k => (cg k : ℤ)) L
    rw [show b + (fun k => (cg k : ℤ)) = fun k => (cf k : ℤ) by rw [← hb]; funext k; simp] at key
    unfold vNum
    rw [key]; ring
  unfold cutIdentityLeftSide cutIdentityRightSide cycEval
  rw [← finsum_sub_distrib (hZfin.subset (Function.support_mul_subset_left _ _))
      (hZfin.subset (Function.support_mul_subset_left _ _)),
    ← finsum_sub_distrib ((hfin f).subset (Function.support_mul_subset_left _ _))
      ((hfin g).subset (Function.support_mul_subset_left _ _))]
  refine finsum_congr fun W => ?_
  rw [← mul_sub, ← sub_mul]
  change ratDiv P f g W * _ = ratDiv P f g W * _
  by_cases hW : ratDiv P f g W = 0
  · simp [hW]
  · beta_reduce
    rw [if_pos (hD.vertical W hW), hadd W hW]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 TensorProduct

section Restrict

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def genPt (F : Type*) [Field F] (Q : Ideal (MRingOver F ι)) :
    (Σ k, ι k) → FractionRing (MRingOver F ι ⧸ Q) :=
  fun p => algebraMap (MRingOver F ι ⧸ Q) _ (Ideal.Quotient.mk Q (X p))

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {Ω : Type*} [Field Ω] [Algebra O Ω]

def IsLocFrac (Q : Ideal (MRingOver (kap O) ι)) (F G : MRingOver O ι) : Prop :=
  ∃ α : K → ℕ, IsMultiHomog F α ∧ IsMultiHomog G α ∧ MvPolynomial.map (IsLocalRing.residue O) G ∉ Q

def stalk (x : (Σ k, ι k) → Ω) (Q : Ideal (MRingOver (kap O) ι)) {N : ℕ} {V : Type*} [AddCommGroup V]
    [Module Ω V] (B : ChartBundle O (mseg x) N V) : AddSubgroup V :=
  AddSubgroup.closure {v | ∃ F G : MRingOver O ι, IsLocFrac O Q F G ∧ ∃ s, mseg (genPt (kap O) Q) s ≠ 0 ∧
    ∃ e ∈ B.lat s, v = (aeval x F / aeval x G) • e}

def resRel (x : (Σ k, ι k) → Ω) (Q : Ideal (MRingOver (kap O) ι)) [Q.IsPrime] {N : ℕ} {V : Type*} [AddCommGroup V]
    [Module Ω V] (B : ChartBundle O (mseg x) N V) :
    Set (FractionRing (MRingOver (kap O) ι ⧸ Q) ⊗[ℤ] stalk O x Q B) :=
  {t | ∃ F G : MRingOver O ι, IsLocFrac O Q F G ∧ ∃ m m' : stalk O x Q B,
    (m' : V) = (aeval x F / aeval x G) • (m : V) ∧
    t = (aeval (genPt (kap O) Q) (MvPolynomial.map (IsLocalRing.residue O) F) /
        aeval (genPt (kap O) Q) (MvPolynomial.map (IsLocalRing.residue O) G)) ⊗ₜ m - 1 ⊗ₜ m'}

abbrev resFibre (x : (Σ k, ι k) → Ω) (Q : Ideal (MRingOver (kap O) ι)) [Q.IsPrime] {N : ℕ} {V : Type*} [AddCommGroup V]
    [Module Ω V] (B : ChartBundle O (mseg x) N V) :=
  (FractionRing (MRingOver (kap O) ι ⧸ Q) ⊗[ℤ] stalk O x Q B) ⧸
    Submodule.span (FractionRing (MRingOver (kap O) ι ⧸ Q)) (resRel O x Q B)

def resMap (x : (Σ k, ι k) → Ω) (Q : Ideal (MRingOver (kap O) ι)) [Q.IsPrime] {N : ℕ} {V : Type*} [AddCommGroup V]
    [Module Ω V] (B : ChartBundle O (mseg x) N V) : stalk O x Q B →+ resFibre O x Q B :=
  (Submodule.mkQ _).toAddMonoidHom.comp
    (TensorProduct.mk ℤ (FractionRing (MRingOver (kap O) ι ⧸ Q)) (stalk O x Q B) 1).toAddMonoidHom

def resLat (x : (Σ k, ι k) → Ω) (Q : Ideal (MRingOver (kap O) ι)) [Q.IsPrime] {N : ℕ} {V : Type*} [AddCommGroup V]
    [Module Ω V] (B : ChartBundle O (mseg x) N V) (s : ∀ k, ι k) : AddSubgroup (resFibre O x Q B) :=
  ((B.lat s).addSubgroupOf (stalk O x Q B)).map (resMap O x Q B)

def resSub (x : (Σ k, ι k) → Ω) (Q : Ideal (MRingOver (kap O) ι)) [Q.IsPrime] {N : ℕ} {V : Type*} [AddCommGroup V]
    [Module Ω V] (B : ChartBundle O (mseg x) N V) (W : Submodule Ω V) :
    Submodule (FractionRing (MRingOver (kap O) ι ⧸ Q)) (resFibre O x Q B) :=
  Submodule.span _ (resMap O x Q B '' {m | (m : V) ∈ W})

end Restrict

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle MRingOver)

def FullFlagRestriction.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω]
    (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d N : ℕ)
    (V : Type) [AddCommGroup V] [Module Ω V] (B : ChartBundle O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg x) N V),
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d →
    ∀ (Q : Ideal (MRingOver (IsLocalRing.ResidueField O) ι)) [Q.IsPrime], ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime Q →
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) ≤ Q →
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal (IsLocalRing.ResidueField O)
                                (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.genPt (IsLocalRing.ResidueField O) Q) = Q ∧
      ∃ B' : ChartBundle (IsLocalRing.ResidueField O)
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.genPt (IsLocalRing.ResidueField O) Q)) N
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.resFibre O x Q B),
        B'.lat = IndefiniteRowSideFullHecke.NumbersDVR.Bundles.resLat O x Q B ∧
        ∀ fl : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FullFlag O x B,
          ∃ fl' : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FullFlag (IsLocalRing.ResidueField O)
              (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.genPt (IsLocalRing.ResidueField O) Q) B',
            fl'.deg = fl.deg ∧ ∀ i, fl'.Vs i = IndefiniteRowSideFullHecke.NumbersDVR.Bundles.resSub O x Q B (fl.Vs i)

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing div_mem_chartRing exists_pow_mul_mem_chartRing)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg joinCoord restrictChart IsPull SameGeneric)

namespace JoinPullbackAlt

section Charts

variable {Ω : Type*} [Field Ω] {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}

def zChart (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) : ∀ k, ι' k :=
  fun k => s (.inr k)

def combChart (t : ∀ k, ι k) (u : ∀ k, ι' k) : ∀ k : K ⊕ K', Sum.elim ι ι' k
  | .inl k => t k
  | .inr k => u k

theorem restrictChart_combChart (t : ∀ k, ι k) (u : ∀ k, ι' k) :
    restrictChart (combChart t u) = t :=
  rfl

theorem zChart_combChart (t : ∀ k, ι k) (u : ∀ k, ι' k) : zChart (combChart t u) = u :=
  rfl

theorem mseg_joinCoord (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) :
    mseg (joinCoord x z) s = mseg x (restrictChart s) * mseg z (zChart s) := by
  simp only [mseg, Fintype.prod_sum_type]
  rfl

variable (O : Type*) [CommRing O] [Algebra O Ω]

theorem chartRing_le_join (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (s : ∀ k : K ⊕ K', Sum.elim ι ι' k)
    (hs : mseg (joinCoord x z) s ≠ 0) :
    chartRing O (mseg x) (restrictChart s) ≤ chartRing O (mseg (joinCoord x z)) s := by
  have hz : mseg z (zChart s) ≠ 0 := by
    rw [mseg_joinCoord] at hs
    exact right_ne_zero_of_mul hs
  unfold chartRing
  apply Algebra.adjoin_le
  rintro _ ⟨t', rfl⟩
  have h : mseg x t' / mseg x (restrictChart s) =
      mseg (joinCoord x z) (combChart t' (zChart s)) / mseg (joinCoord x z) s := by
    rw [mseg_joinCoord x z (combChart t' (zChart s)), mseg_joinCoord x z s, restrictChart_combChart,
      zChart_combChart, mul_div_mul_right _ _ hz]
  simp only
  rw [h]
  exact div_mem_chartRing (o := O) _ _ _

end Charts

section Pull

variable (O : Type*) [CommRing O] {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
  [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
variable {N : ℕ} {V : Type*} [AddCommGroup V] [Module Ω V]

end Pull

end JoinPullbackAlt


end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver)
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsProjVarF)

def VerticalDivisorSupportFibre.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K]
    (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRingOver O ι)) (d : ℕ),
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O P d →
    ∀ (b : K → ℤ) (f g : MRingOver O ι), IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O P b f g →
    ∀ W : Ideal (MRingOver O ι), IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O P f g W ≠ 0 →
      IsProjVarF (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O W) d

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg joinCoord IsPull SameGeneric)

def JoinPullbackAlt.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (z : (Σ k, ι' k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V]
    (E E' : ChartBundle O (mseg x) N V), SameGeneric O x E E' →
    ∃ EB E'B : ChartBundle O (mseg (joinCoord x z)) N V,
      IsPull O x z E EB ∧ IsPull O x z E' E'B ∧ SameGeneric O (joinCoord x z) EB E'B

end GroundTheory.Heights₂.Heights.NumbersDVR
end

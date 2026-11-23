module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Statements
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle003
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
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem ratDiv_support_finite (h4 : DivCycleFiniteSupport.Statement.{u}) {O : Type u} [CommRing O]
    [IsNoetherianRing O] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι O)) (f g : MRing ι O) : (Function.support (ratDiv P f g)).Finite := by
  refine ((h4 O K ι P f).union (h4 O K ι P g)).subset ?_
  intro W hW
  by_contra h
  simp only [Set.mem_union, Function.mem_support, not_or, not_not] at h
  exact hW (by simp [ratDiv, h.1, h.2])

theorem lt_natCast_of_add_one_le {x : WithBot ℕ∞} {n : ℕ} (h : x + 1 ≤ (n : WithBot ℕ∞)) :
    x < (n : WithBot ℕ∞) := by
  induction x with
  | bot => exact WithBot.bot_lt_coe _
  | coe e =>
    have h' : e + 1 ≤ (n : ℕ∞) := by exact_mod_cast h
    have h'' : e < (n : ℕ∞) := (ENat.add_one_le_iff' (ENat.natCast_ne_top n)).mp h'
    exact_mod_cast h''

theorem VerticalDivisorsCommute.proof (h1 : CutByEffectiveDivisor.Statement.{u})
    (h2 : Representative.Statement.{u}) (h3 : IntNumAddFirst.Statement.{u})
    (h4 : DivCycleFiniteSupport.Statement.{u}) (h5 : MinimalPrimeMultiHomog.Statement.{u})
    (h6 : SupSpanMultiHomog.Statement.{u}) (h7 : SpecialQuotDim.Statement.{u})
    (h8 : SpecialIdealCorresp.Statement.{u}) (h9 : SpecialIdealMultiHomog.Statement.{u})
    (h10 : DimStrictDrop.Statement.{u}) : VerticalDivisorsCommute.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b b' f g f' g' hD hD' L
  obtain ⟨c', c'', hc', hc'', hb'⟩ := hD'.degrees
  obtain ⟨bf, bg, hbf, hbg, -⟩ := hD.degrees
  have hPmh : IsMultiHomogIdeal P := hP.multiProj.multiHomog
  have : P.IsPrime := hP.multiProj.isPrime

  have hmh : ∀ (h : MRing ι O) (e : K → ℕ), IsMultiHomog h e → ∀ W, divCycle P h W ≠ 0 →
      IsMultiHomogIdeal W ∧ W ∈ (P ⊔ Ideal.span {h}).minimalPrimes ∧ IsRelevant W := by
    intro h e he W hW
    unfold divCycle at hW
    split_ifs at hW with hW'
    · exact ⟨h5 O K ι _ W (h6 O K ι P h e hPmh he) hW'.1, hW'.1, hW'.2⟩
    · exact absurd rfl hW
  have hϖP : (C ϖ : MRing ι O) ∉ P := by
    intro h
    have h' : ϖ ∈ P.comap (C : O →+* MRing ι O) := h
    rw [hP.noTorsion, Ideal.mem_bot] at h'
    exact hϖ.ne_zero h'

  have hTfin : {H : Ideal (MRing ι O) | (divCycle P f' H ≠ 0 ∨ divCycle P g' H ≠ 0) ∧
      (C ϖ : MRing ι O) ∉ H}.Finite :=
    ((h4 O K ι P f').union (h4 O K ι P g')).subset fun H hH => hH.1
  obtain ⟨f₁, g₁, hV₁, hrat, hT₁⟩ := h2 O ϖ hϖ K ι P b f g hP.multiProj hD hTfin.toFinset (by
    intro H hH
    rw [Set.Finite.mem_toFinset] at hH
    obtain ⟨hne, hϖH⟩ := hH
    rcases hne with hne | hne
    · obtain ⟨hm, hmin, hrel⟩ := hmh f' c' hc' H hne
      exact ⟨⟨hmin.1.1, hm, hrel⟩, le_sup_left.trans hmin.1.2, hϖH, f', hD'.num_not_mem, hmin⟩
    · obtain ⟨hm, hmin, hrel⟩ := hmh g' c'' hc'' H hne
      exact ⟨⟨hmin.1.1, hm, hrel⟩, le_sup_left.trans hmin.1.2, hϖH, g', hD'.den_not_mem, hmin⟩)
  have e1 := h1 O ϖ hϖ K ι P d hP b f₁ g₁ hV₁ c' f' hc' hD'.num_not_mem
    (fun H hH hϖH => hT₁ H (by rw [Set.Finite.mem_toFinset]; exact ⟨Or.inl hH, hϖH⟩)) L
  have e2 := h1 O ϖ hϖ K ι P d hP b f₁ g₁ hV₁ c'' g' hc'' hD'.den_not_mem
    (fun H hH hϖH => hT₁ H (by rw [Set.Finite.mem_toFinset]; exact ⟨Or.inr hH, hϖH⟩)) L
  rw [hrat] at e1 e2

  have hadd : ∀ W, ratDiv P f g W ≠ 0 →
      vNum W (Matrix.vecCons b' L) = vNum W (Matrix.vecCons (fun k => (c' k : ℤ)) L) -
        vNum W (Matrix.vecCons (fun k => (c'' k : ℤ)) L) := by
    intro W hW
    have hϖW : (C ϖ : MRing ι O) ∈ W := hD.vertical W hW
    have hWdata : IsMultiHomogIdeal W ∧ W.IsPrime ∧ P ≤ W := by
      by_cases hWf : divCycle P f W = 0
      · have hWg : divCycle P g W ≠ 0 := by
          intro hWg; apply hW; simp [ratDiv, hWf, hWg]
        obtain ⟨hm, hmin, -⟩ := hmh g bg hbg W hWg
        exact ⟨hm, hmin.1.1, le_sup_left.trans hmin.1.2⟩
      · obtain ⟨hm, hmin, -⟩ := hmh f bf hbf W hWf
        exact ⟨hm, hmin.1.1, le_sup_left.trans hmin.1.2⟩
    obtain ⟨hWm, hWp, hPW⟩ := hWdata
    have := hWp
    have hlt : P < W := lt_of_le_of_ne hPW (fun e => hϖP (e ▸ hϖW))
    have hdrop := h10 (MRing ι O) P W hlt
    rw [hP.dim] at hdrop
    have hdim : ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal W) <
        ((d + 2 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
      rw [h7 O ϖ hϖ K ι W hϖW]
      have e : d + 1 + 1 + Fintype.card K = d + 2 + Fintype.card K := by omega
      rw [e] at hdrop
      exact lt_natCast_of_add_one_le hdrop
    have key := h3 (IsLocalRing.ResidueField O) K ι d (specialIdeal W)
      (h8 O ϖ hϖ K ι P W hWp hϖW).1 (h9 O K ι W hWm) hdim b' (fun k => (c'' k : ℤ)) L
    have hsum : b' + (fun k => (c'' k : ℤ)) = fun k => (c' k : ℤ) := by
      rw [← hb']; funext k; simp
    rw [hsum] at key
    unfold vNum
    rw [key]; ring
  have hZfin := ratDiv_support_finite h4 P f g
  calc cycEval (fun G => vNum G (Matrix.vecCons b' L)) (ratDiv P f g)
      = cycEval (fun G => vNum G (Matrix.vecCons (fun k => (c' k : ℤ)) L)) (ratDiv P f g) -
          cycEval (fun G => vNum G (Matrix.vecCons (fun k => (c'' k : ℤ)) L)) (ratDiv P f g) := by
        unfold cycEval
        rw [← finsum_sub_distrib (hZfin.subset (Function.support_mul_subset_left _ _))
          (hZfin.subset (Function.support_mul_subset_left _ _))]
        refine finsum_congr fun W => ?_
        by_cases hW : ratDiv P f g W = 0
        · simp [hW]
        · beta_reduce
          rw [hadd W hW, mul_sub]
    _ = _ := by rw [e1, e2]
    _ = cycEval (fun G => vNum G (Matrix.vecCons b L)) (ratDiv P f' g') := by
        unfold cycEval
        rw [← finsum_sub_distrib ((h4 O K ι P f').subset (Function.support_mul_subset_left _ _))
          ((h4 O K ι P g').subset (Function.support_mul_subset_left _ _))]
        refine finsum_congr fun W => ?_
        rw [← sub_mul]
        change ratDiv P f' g' W * _ = ratDiv P f' g' W * _
        by_cases hW : ratDiv P f' g' W = 0
        · simp [hW]
        · beta_reduce
          rw [if_pos (hD'.vertical W hW)]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

namespace HilbDegBound

section Lemmas

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem isHomogeneous_of_isMultiHomogIdeal {I : Ideal (MRing ι F)} (hI : IsMultiHomogIdeal I) :
    I.IsHomogeneous (weightedHomogeneousSubmodule F (blockWeight ι)) := by
  classical
  have e : I = Ideal.span
      {g | ∃ f ∈ I, ∃ b, g = weightedHomogeneousComponent (blockWeight ι) b f} := by
    apply le_antisymm
    · intro f hf
      rw [← sum_weightedHomogeneousComponent (blockWeight ι) f,
        finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
      exact Ideal.sum_mem _ fun b _ => Ideal.subset_span ⟨f, hf, b, rfl⟩
    · rw [Ideal.span_le]
      rintro g ⟨f, hf, b, rfl⟩
      exact hI f hf b
  rw [e]
  refine Ideal.homogeneous_span _ _ fun x hx => ?_
  obtain ⟨f, -, b, rfl⟩ := hx
  exact ⟨b, weightedHomogeneousComponent_isWeightedHomogeneous b f⟩

theorem isMultiHomogIdeal_sup_span {I : Ideal (MRing ι F)} (hI : IsMultiHomogIdeal I)
    {s : MRing ι F} {c : K → ℕ} (hs : IsMultiHomog s c) :
    IsMultiHomogIdeal (I ⊔ Ideal.span {s}) := by
  classical
  have h2 : (Ideal.span {s}).IsHomogeneous (weightedHomogeneousSubmodule F (blockWeight ι)) :=
    Ideal.homogeneous_span _ _ fun x hx => ⟨c, (Set.mem_singleton_iff.mp hx) ▸ hs⟩
  intro f hf b
  exact weightedHomogeneousComponent_mem_of_mem
    (h := (isHomogeneous_of_isMultiHomogIdeal hI).sup h2) (hp := hf) (m := b)

theorem lt_of_add_one_le_natCast {x : WithBot ℕ∞} {N : ℕ} (h : x + 1 ≤ N) : x < N := by
  induction x using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      have e : ((⊤ : ℕ∞) : WithBot ℕ∞) + 1 = ((⊤ : ℕ∞) : WithBot ℕ∞) := by
        rw [← WithBot.coe_one, ← WithBot.coe_add, top_add]
      rw [e, ← WithBot.coe_natCast, WithBot.coe_le_coe] at h
      exact absurd h (not_le.mpr (ENat.natCast_lt_top N))
    | coe a =>
      have : a + 1 ≤ N := by exact_mod_cast h
      exact_mod_cast (show a < N by omega)

theorem le_natCast_of_lt_natCast_succ {x : WithBot ℕ∞} {N : ℕ}
    (h : x < ((N + 1 : ℕ) : WithBot ℕ∞)) : x ≤ N := by
  induction x using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      rw [← WithBot.coe_natCast, WithBot.coe_lt_coe] at h
      exact absurd h (not_lt.mpr le_top)
    | coe a =>
      have : a < N + 1 := by exact_mod_cast h
      exact_mod_cast (show a ≤ N by omega)


omit [Fintype K] [DecidableEq K] in
theorem degLT_listSum (h6 : DegLTClosure.Statement) {α : Type*} (n : ℕ)
    (g : α → (K → ℤ) → ℤ) (l : List α) (hl : ∀ a ∈ l, DegLT (g a) n) :
    DegLT (fun m => (l.map fun a => g a m).sum) n := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    exact degLT_zero n
  | cons a l ih =>
    have e : (fun m => ((a :: l).map fun a => g a m).sum) =
        g a + fun m => (l.map fun a => g a m).sum := by
      funext m
      simp
    rw [e]
    exact (h6 K n _ _ 0 0).1 (hl a (by simp)) (ih fun b hb => hl b (by simp [hb]))

end Lemmas

end HilbDegBound


open HilbDegBound in
theorem HilbDegBound.proof (h1 : HilbFnVanishBlock.Statement.{u}) (h2 : HilbFnCut.Statement.{u})
    (h3 : PrimeFiltration.Statement.{u}) (h4 : DimStrictDrop.Statement.{u})
    (h5 : RelevantDimGe.Statement.{u}) (h6 : DegLTClosure.Statement)
    (h7 : DegLTOfUnitSteps.Statement) : HilbDegBound.Statement.{u} := by
  intro F _ K _ _ ι _ n

  have irr : ∀ (n : ℕ) (Q : Ideal (MRing ι F)), ¬ IsRelevant Q → DegLT (hilbFn Q) n := by
    intro n Q hrel
    unfold IsRelevant at hrel
    push Not at hrel
    obtain ⟨k, hk⟩ := hrel
    have hev : (0 : (K → ℤ) → ℤ) =ᶠ[Filter.atTop] hilbFn Q := by
      filter_upwards [Filter.eventually_ge_atTop (1 : K → ℤ)] with m hm
      exact (h1 F K ι Q k hk m (hm k)).symm
    exact (h6 K n 0 _ 0 0).2.2.2.2 hev (degLT_zero n)
  induction n with
  | zero =>
    intro Q hQ hQh hdim
    by_cases hrel : IsRelevant Q
    · exfalso
      have hge := h5 F K ι Q ⟨hQ, hQh, hrel⟩
      rw [Nat.zero_add] at hdim
      exact absurd hge (not_le.mpr hdim)
    · exact irr 0 Q hrel
  | succ n ih =>
    intro Q hQ hQh hdim
    by_cases hrel : IsRelevant Q
    swap
    · exact irr _ Q hrel
    have hdimle : ringKrullDim (MRing ι F ⧸ Q) ≤ ((n + Fintype.card K : ℕ) : WithBot ℕ∞) := by
      have e : n + 1 + Fintype.card K = n + Fintype.card K + 1 := by omega
      rw [e] at hdim
      exact le_natCast_of_lt_natCast_succ hdim
    apply h7 K n
    intro k
    obtain ⟨i, hi⟩ := hrel k
    have hx : IsMultiHomog (X ⟨k, i⟩ : MRing ι F) (Pi.single k 1) := isWeightedHomogeneous_X _ _ _
    have hnzd : ∀ y, (X ⟨k, i⟩ : MRing ι F) * y ∈ Q → y ∈ Q :=
      fun y hy => (hQ.mem_or_mem hy).resolve_left hi
    have hcut := h2 F K ι Q (X ⟨k, i⟩) (Pi.single k 1) hQh hx hnzd
    have hJ : IsMultiHomogIdeal (Q ⊔ Ideal.span {(X ⟨k, i⟩ : MRing ι F)}) :=
      isMultiHomogIdeal_sup_span hQh hx
    have hs : (fun j => ((Pi.single k 1 : K → ℕ) j : ℤ)) = (Pi.single k 1 : K → ℤ) := by
      funext j
      by_cases h : j = k <;> simp [h]
    have heq : diffStep (Pi.single k 1) (hilbFn Q) =
        hilbFn (Q ⊔ Ideal.span {(X ⟨k, i⟩ : MRing ι F)}) := by
      funext m
      rw [hcut m, hs]
      rfl
    rw [heq]
    obtain ⟨l, hl1, hl2, -⟩ := h3 F K ι _ hJ
    obtain ⟨G, hG⟩ : ∃ G : Ideal (MRing ι F) × (K → ℕ) → (K → ℤ) → ℤ,
        G = fun p => shiftFn (fun j => (p.2 j : ℤ)) (hilbFn p.1) := ⟨_, rfl⟩
    have hfun : hilbFn (Q ⊔ Ideal.span {(X ⟨k, i⟩ : MRing ι F)}) = fun m =>
        (l.map fun p => G p m).sum := by
      funext m
      rw [hl2 m, hG]
      rfl
    rw [hfun]
    apply degLT_listSum h6 n G l
    intro p hp
    obtain ⟨hp1, hp2, hp3⟩ := hl1 p hp
    rw [hG]
    refine (h6 K n (hilbFn p.1) 0 0 _).2.2.1 ?_
    refine ih p.1 hp1 hp2 ?_
    have hlt : Q < p.1 := by
      refine lt_of_le_of_ne (le_sup_left.trans hp3) fun h => hi ?_
      rw [h]
      exact hp3 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have := hQ
    have := hp1
    have hd := h4 (MRing ι F) Q p.1 hlt
    exact lt_of_add_one_le_natCast (hd.trans hdimle)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem withBotENat_lt_of_add_one_le {a : WithBot ℕ∞} {n : ℕ} (h : a + 1 ≤ (n : WithBot ℕ∞)) :
    a < (n : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : ((⊤ : ℕ∞) + 1 : ℕ∞) ≤ (n : ℕ∞) := by exact_mod_cast h
      simp at h'
    | coe m =>
      have h' : ((m + 1 : ℕ) : ℕ∞) ≤ (n : ℕ∞) := by exact_mod_cast h
      have h'' : m + 1 ≤ n := by exact_mod_cast h'
      exact_mod_cast (show m < n by omega)

theorem SpecialDimBound.proof : SpecialDimBound.Statement := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP
  have := hP.multiProj.isPrime
  set φ : MRing ι O →+* MRing ι (IsLocalRing.ResidueField O) :=
    MvPolynomial.map (IsLocalRing.residue O) with hφdef
  have hφ : Function.Surjective φ := MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective
  have hker : RingHom.ker φ = Ideal.span {(C ϖ : MRing ι O)} := by
    rw [hφdef, MvPolynomial.ker_map, IsLocalRing.ker_residue, hϖ.maximalIdeal_eq, Ideal.map_span,
      Set.image_singleton]

  set g : MRing ι O →+* MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal P :=
    (Ideal.Quotient.mk (specialIdeal P)).comp φ with hgdef
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp hφ
  have hkg : RingHom.ker g = P ⊔ Ideal.span {(C ϖ : MRing ι O)} := by
    rw [hgdef, ← RingHom.comap_ker, Ideal.mk_ker, specialIdeal, ← hφdef,
      Ideal.comap_map_of_surjective _ hφ, ← RingHom.ker_eq_comap_bot, hker]
  have e1 : MRing ι O ⧸ (P ⊔ Ideal.span {(C ϖ : MRing ι O)}) ≃+*
      MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal P :=
    (Ideal.quotEquivOfEq hkg.symm).trans (RingHom.quotientKerEquivOfSurjective hg)

  set r : MRing ι O ⧸ P := Ideal.Quotient.mk P (C ϖ) with hrdef
  have hspan : (Ideal.span {(C ϖ : MRing ι O)}).map (Ideal.Quotient.mk P) = Ideal.span {r} := by
    rw [Ideal.map_span, Set.image_singleton]
  have e2 : (MRing ι O ⧸ P) ⧸ Ideal.span {r} ≃+* MRing ι O ⧸ (P ⊔ Ideal.span {(C ϖ : MRing ι O)}) :=
    (Ideal.quotEquivOfEq hspan.symm).trans (DoubleQuot.quotQuotEquivQuotSup P _)

  have hr0 : r ≠ 0 := by
    intro h0
    rw [hrdef, Ideal.Quotient.eq_zero_iff_mem] at h0
    have hmem : ϖ ∈ P.comap (C : O →+* MRing ι O) := h0
    rw [hP.noTorsion, Ideal.mem_bot] at hmem
    exact hϖ.ne_zero hmem
  have hr : r ∈ nonZeroDivisors (MRing ι O ⧸ P) := mem_nonZeroDivisors_of_ne_zero hr0
  have hle := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr
  rw [hP.dim, ringKrullDim_eq_of_ringEquiv e2, ringKrullDim_eq_of_ringEquiv e1] at hle
  exact withBotENat_lt_of_add_one_le hle

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem exists_block_var_of_weight_pos {K : Type} [DecidableEq K] {ι : K → Type}
    (d : (Σ k, ι k) →₀ ℕ) (k : K) (h : 1 ≤ Finsupp.weight (blockWeight ι) d k) :
    ∃ v : Σ k, ι k, v.1 = k ∧ d v ≠ 0 := by
  by_contra hne
  push Not at hne
  have h0 : Finsupp.weight (blockWeight ι) d k = 0 := by
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
    refine Finset.sum_eq_zero fun v hv => ?_
    have hv1 : v.1 ≠ k := fun e => (Finsupp.mem_support_iff.mp hv) (hne v e)
    simp [blockWeight, hv1]
  omega

theorem mem_of_block_vars_mem {F : Type u} [Field F] {K : Type} [DecidableEq K] {ι : K → Type}
    (Q : Ideal (MRing ι F)) (k : K) (hX : ∀ i, (X ⟨k, i⟩ : MRing ι F) ∈ Q) (m : K → ℕ)
    (hm : 1 ≤ m k) (f : MRing ι F) (hf : f ∈ weightedHomogeneousSubmodule F (blockWeight ι) m) :
    f ∈ Q := by
  have hspan : Ideal.span ((X : (Σ k, ι k) → MRing ι F) '' {v | v.1 = k}) ≤ Q := by
    rw [Ideal.span_le]
    rintro _ ⟨⟨k', i⟩, hv, rfl⟩
    simp only [Set.mem_ofPred_eq] at hv
    subst hv
    exact hX i
  apply hspan
  rw [mem_ideal_span_X_image]
  intro d hd
  rw [mem_weightedHomogeneousSubmodule] at hf
  have hw : Finsupp.weight (blockWeight ι) d = m := hf (Finsupp.mem_support_iff.mp hd)
  obtain ⟨v, hv, hdv⟩ := exists_block_var_of_weight_pos d k (by rw [hw]; exact hm)
  exact ⟨v, hv, hdv⟩

theorem HilbFnVanishBlock.proof : HilbFnVanishBlock.Statement.{u} := by
  intro F _ K _ _ ι _ Q k hX m hm
  unfold hilbFn
  split_ifs with h
  · have hbot : gradedPiece Q (fun k => (m k).toNat) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hx
      have hfQ : f ∈ Q := mem_of_block_vars_mem Q k hX _ (by omega) f hf
      simpa using (Ideal.Quotient.eq_zero_iff_mem).mpr hfQ
    rw [hbot, finrank_bot]
    rfl
  · rfl

end GroundTheory.Heights₂.Heights.NumbersDVR
end

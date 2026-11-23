module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1639
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle637
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEntireLatticeSumOfHeckeLContinuation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1160
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1376
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsHeckeLOfHasInf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle867
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle876
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1641
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormsAddOfFactorProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1582
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle137
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1635
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle886
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle479
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDisjointUnipotentCellsCoverCompactMiraboli
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle917
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1642
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036

@[expose] public section

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.FinClsLoc
open IsDedekindDomain

theorem ratAdicInt_eventually (q : ℚ) :
    ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite,
      algebraMap ℚ (v.adicCompletion ℚ) q ∈ v.adicCompletionIntegers ℚ := by
  have h := (algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q).2
  filter_upwards [h] with v hv
  exact hv

theorem intC_inC_eventually : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (c : G.C), ∀ᶠ w : AwayP p in Filter.cofinite,
    IntC G w (inC G (w.1.adicCompletion ℚ) c) := by
  intro p _ G c
  have hall : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ i : Fin (Module.finrank ℚ G.C),
      algebraMap ℚ (v.adicCompletion ℚ) ((Module.finBasis ℚ G.C).repr c i) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun i => ratAdicInt_eventually _
  have ht : Filter.Tendsto (Subtype.val : AwayP p → HeightOneSpectrum ℤ) Filter.cofinite Filter.cofinite :=
    Subtype.val_injective.tendsto_cofinite
  filter_upwards [ht.eventually hall] with w hw
  intro i
  have : coordL G w (inC G (w.1.adicCompletion ℚ) c) i =
      algebraMap ℚ (w.1.adicCompletion ℚ) ((Module.finBasis ℚ G.C).repr c i) := by
    have e : inC G (w.1.adicCompletion ℚ) c = (1 : w.1.adicCompletion ℚ) ⊗ₜ[ℚ] c := rfl
    rw [coordL, e, Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply]
  rw [this]; exact hw i

end GlobalTheory.FinClsLoc
end
end

section

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical
open IsDedekindDomain

namespace GlobalTheory.FinClsLoc

theorem ratInt_eventually (x : ℚ) :
    ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite,
      algebraMap ℚ (v.adicCompletion ℚ) x ∈ v.adicCompletionIntegers ℚ := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := ℤ) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hI : Ideal.span {b} ≠ (0 : Ideal ℤ) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hb0
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors hI).subset fun w hw => ?_)
  simp only [Set.mem_setOf_eq] at hw ⊢
  by_contra hd
  apply hw
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  refine (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _).trans_le ?_
  have h1 : w.valuation ℚ (algebraMap ℤ ℚ b) = 1 :=
    le_antisymm (w.valuation_le_one b) (not_lt.1 fun h => hd ((w.valuation_lt_one_iff_dvd b).1 h))
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  rw [map_div₀, h1, div_one]
  exact w.valuation_le_one a

theorem ratInt_eventually_away {p : ℕ} (x : ℚ) :
    ∀ᶠ w : AwayP p in Filter.cofinite,
      algebraMap ℚ (w.1.adicCompletion ℚ) x ∈ w.1.adicCompletionIntegers ℚ :=
  (Subtype.val_injective.tendsto_cofinite).eventually (ratInt_eventually x)

section

variable {C : Type} [Ring C] [Algebra ℚ C] {κ : Type} [Fintype κ] (b : Module.Basis κ ℚ C)
  (v : HeightOneSpectrum ℤ)

theorem repr_tmul_apply' (a : v.adicCompletion ℚ) (x : C) (k : κ) :
    (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).repr (a ⊗ₜ[ℚ] x) k =
      a * algebraMap ℚ (v.adicCompletion ℚ) (b.repr x k) := by
  rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]

theorem eq_sum_tmul' (y : v.adicCompletion ℚ ⊗[ℚ] C) :
    y = ∑ i, (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).repr y i ⊗ₜ[ℚ] b i := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).sum_repr y]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end

theorem intC_stab : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ), ∀ᶠ w : AwayP p in Filter.cofinite,
    (∀ a b : (w.1.adicCompletion ℚ ⊗[ℚ] G.C), IntC G w a → IntC G w b → IntC G w (a * b)) ∧
    (∀ a : (w.1.adicCompletion ℚ ⊗[ℚ] G.C), IntC G w a → IntC G w (starT G.star (w.1.adicCompletion ℚ) a).unop) ∧
    IntC G w (inC G (w.1.adicCompletion ℚ) (β : G.C)) ∧ IntC G w (inC G (w.1.adicCompletion ℚ) ((β⁻¹ : G.Cˣ) : G.C)) := by
  intro p _ G β
  set bb := Module.finBasis ℚ G.C
  have hc : ∀ᶠ w : AwayP p in Filter.cofinite, ∀ t : Fin (Module.finrank ℚ G.C) × Fin (Module.finrank ℚ G.C) ×
      Fin (Module.finrank ℚ G.C),
      algebraMap ℚ (w.1.adicCompletion ℚ) (bb.repr (bb t.1 * bb t.2.1) t.2.2) ∈ w.1.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => ratInt_eventually_away _
  have hs : ∀ᶠ w : AwayP p in Filter.cofinite, ∀ t : Fin (Module.finrank ℚ G.C) × Fin (Module.finrank ℚ G.C),
      algebraMap ℚ (w.1.adicCompletion ℚ) (bb.repr (G.star (bb t.1)).unop t.2) ∈ w.1.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => ratInt_eventually_away _
  have hb : ∀ x : G.C, ∀ᶠ w : AwayP p in Filter.cofinite, ∀ k : Fin (Module.finrank ℚ G.C),
      algebraMap ℚ (w.1.adicCompletion ℚ) (bb.repr x k) ∈ w.1.adicCompletionIntegers ℚ :=
    fun x => Filter.eventually_all.2 fun k => ratInt_eventually_away _
  have hin : ∀ (w : AwayP p) (x : G.C), (∀ k, algebraMap ℚ (w.1.adicCompletion ℚ) (bb.repr x k) ∈
      w.1.adicCompletionIntegers ℚ) → IntC G w (inC G (w.1.adicCompletion ℚ) x) := by
    intro w x hx k
    change (Algebra.TensorProduct.basis (w.1.adicCompletion ℚ) bb).repr ((1 : w.1.adicCompletion ℚ) ⊗ₜ[ℚ] x) k ∈ _
    rw [repr_tmul_apply', one_mul]
    exact hx k
  filter_upwards [hc, hs, hb (β : G.C), hb ((β⁻¹ : G.Cˣ) : G.C)] with w hcv hsv hbv hbv'
  refine ⟨fun y z hy hz k => ?_, fun y hy k => ?_, hin w _ hbv, hin w _ hbv'⟩
  · change (Algebra.TensorProduct.basis (w.1.adicCompletion ℚ) bb).repr (y * z) k ∈ _

    rw [eq_sum_tmul' bb w.1 y, eq_sum_tmul' bb w.1 z, Finset.sum_mul_sum, map_sum, Finsupp.finsetSum_apply]
    refine sum_mem fun i _ => ?_

    rw [map_sum, Finsupp.finsetSum_apply]
    refine sum_mem fun j _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, repr_tmul_apply']
    exact mul_mem (mul_mem (hy i) (hz j)) (hcv (i, j, k))
  · have hu : ∀ (f : Fin (Module.finrank ℚ G.C) → (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ᵐᵒᵖ),
        (∑ i, f i).unop = ∑ i, (f i).unop :=
      fun f => map_sum (MulOpposite.opAddEquiv : w.1.adicCompletion ℚ ⊗[ℚ] G.C ≃+ _).symm f Finset.univ
    change (Algebra.TensorProduct.basis (w.1.adicCompletion ℚ) bb).repr _ k ∈ _

    rw [eq_sum_tmul' bb w.1 y, map_sum, hu, map_sum, Finsupp.finsetSum_apply]
    refine sum_mem fun i _ => ?_
    rw [starT_tmul, repr_tmul_apply']
    exact mul_mem (hy i) (hsv (i, k))

end GlobalTheory.FinClsLoc
end
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.HeckeGal
open GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols (IsTwistedSum IsSymbol conjChar classOf ToricRatioConjugates)
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (IsConjWt IsConjChar lamF upIdele)

namespace GlobalTheory.ToricTransport

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

theorem exists_toricSum_ne_zero [IsCMField E] {φ : I → E →+* ℂ} {s : ℕ} {κ : I → ℕ} {𝔣 : Ideal (OF E)} {χ : HChar E}
    (hU : UnramFin E) (hφ : IsCMType φ) (hs : 1 ≤ s) (hb : IsBaseCond 𝔣) (hχ : IsValChar φ s κ 𝔣 ∅ χ) :
    ∃ T₀ : ℂ, IsToricSum φ s κ (condQ 𝔣 ∅) χ T₀ ∧ T₀ ≠ 0 := by
  obtain ⟨i₀, -⟩ := hφ (Classical.arbitrary _)
  obtain ⟨Λ, hΛ⟩ := GlobalTheory.ToricDistribution.exists_isHeckeL_of_hasInf E I φ _ χ hφ hχ.1 hχ.2.2.1 ⟨i₀, by omega⟩
  obtain ⟨P₀⟩ : Nonempty (HeightOneSpectrum (𝓞 E)) := by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 E)
    exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField _)⟩⟩
  have t1 := GlobalTheory.ToricSumValue.toricSum_eq GlobalTheory.ToricDistribution.exists_isHeckeL_of_hasInf E I φ hφ s κ 𝔣 ∅ χ (fun _ => P₀) Λ hU hs hb
    (fun _ h => absurd h (Finset.notMem_empty _)) hχ (fun _ h => absurd h (Finset.notMem_empty _)) hΛ
  rw [Finset.filter_empty, Finset.prod_empty, mul_one] at t1
  exact ⟨Λ s, t1, hΛ.ne_zero_nat hχ.1 hs⟩

theorem condQ_ne_bot {𝔣 : Ideal (OF E)} (hb : IsBaseCond 𝔣) (Q : Finset (HeightOneSpectrum (OF E))) : condQ 𝔣 Q ≠ ⊥ :=
  mul_ne_zero hb.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)

theorem exists_twistedSum [IsCMField E] {φ : I → E →+* ℂ} {s : ℕ} {κ : I → ℕ} {𝔣 : Ideal (OF E)} {χ : HChar E}
    (hU : UnramFin E) (hφ : IsCMType φ) (hs : 1 ≤ s) (hb : IsBaseCond 𝔣) (hχ : IsValChar φ s κ 𝔣 ∅ χ)
    (Q : Finset (HeightOneSpectrum (OF E))) (ψ : PicO (condQ 𝔣 Q) →* ℂˣ) : ∃ T, IsTwistedSum φ s κ (condQ 𝔣 Q) χ ψ T := by
  have h0 := OrderUnits.finPart_eq_one E I φ hφ s κ 𝔣 ∅ χ hU hb (fun _ h => absurd h (Finset.notMem_empty _)) hχ
  have hle : condQ 𝔣 Q ≤ condQ 𝔣 ∅ := by
    rw [show condQ 𝔣 ∅ = 𝔣 by simp [condQ]]
    exact Ideal.dvd_iff_le.1 (dvd_mul_right 𝔣 _)
  choose S hS using fun q : PicO (condQ 𝔣 Q) =>
    LatEnt.exists_isLatSum GlobalTheory.ToricDistribution.exists_isHeckeL_of_hasInf E I φ hφ s κ 𝔣 _ χ hU hs hb (dvd_mul_right _ _)
      (condQ_ne_bot hb Q) hχ.1 hχ.2.2.1 (fun y hy => h0 y (hatOUnits_mono hle hy)) q.out
  exact ⟨_, PicFin.finite_picO E _ (condQ_ne_bot hb Q), S, hS, rfl⟩

theorem isTwistedSum_one {φ : I → E →+* ℂ} {s : ℕ} {κ : I → ℕ} {c : Ideal (OF E)} {χ : HChar E} (T : ℂ) :
    IsTwistedSum φ s κ c χ 1 T ↔ IsToricSum φ s κ c χ T := by
  simp [IsTwistedSum, IsToricSum, GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.lamF]

theorem conjChar_one {c : Ideal (OF E)} (g : ℂ ≃+* ℂ) : conjChar g (1 : PicO c →* ℂˣ) = 1 :=
  MonoidHom.ext fun _ => Units.ext (map_one g)

theorem toricRatioConjugates_of_transport (hT : TwistedTransport) : ToricRatioConjugates := by
  intro E _ _ _ K _ _ _ d δ ι I _ φ s κ 𝔣 Q χ hU hK hd hδ hφ hι hs hκ hb hQ hχ
  obtain ⟨Ω₀, hΩ₀, halg, hconj⟩ := hT K d δ ι hK hd hδ
  obtain ⟨T₀, hT₀, h0⟩ := exists_toricSum_ne_zero hU hφ hs hb hχ
  choose T hTw using exists_twistedSum hU hφ hs hb hχ Q
  have hD : IsDatum ι φ s κ 𝔣 Q χ := ⟨hU, hφ, hι, hs, hκ, hb, hQ, hχ⟩
  have hD₀ : IsDatum ι φ s κ 𝔣 ∅ χ := ⟨hU, hφ, hι, hs, hκ, hb, fun _ h => absurd h (Finset.notMem_empty _), hχ⟩
  have hT₀' := (isTwistedSum_one T₀).2 hT₀
  have e : condQ 𝔣 ∅ = 𝔣 := by simp [condQ]
  refine ⟨T₀, T, e ▸ hT₀, h0, hTw, fun ψ => ?_, fun Ω _ _ _ j art hj ha g σ t hgE hgl hσ ht ψ => ⟨?_, ?_⟩⟩
  · rw [← coordIn_div E hd hs κ hΩ₀, div_eq_mul_inv]
    exact (halg E I φ s κ 𝔣 Q χ hD ψ _ (hTw ψ)).mul (halg E I φ s κ 𝔣 ∅ χ hD₀ 1 _ hT₀').inv
  · obtain ⟨Ω₁, hΩ₁, h⟩ := hconj Ω j art hj ha g σ t hσ ht
    have hw : IsConjWt φ g κ κ := fun i i' hi => by
      have : φ i = φ i' := RingHom.ext fun x => (hgE i x).symm.trans (hi x)
      rw [(hφ (φ i)).unique (Or.inl rfl) (Or.inl this)]
    have hc : IsConjChar φ s κ g χ χ := ⟨fun y => (hgl y).symm, hχ.2.2.1⟩
    have h1 := h E I φ s κ 𝔣 Q χ hD κ χ hw hc ψ _ _ (hTw ψ) (hTw _)
    have h2 := h E I φ s κ 𝔣 ∅ χ hD₀ κ χ hw hc 1 T₀ T₀ hT₀' (by rw [conjChar_one]; exact hT₀')
    have hl := GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.lamF_ne_zero s χ (upIdele K E t)
    have hm : ((modF t : ℝ) : ℂ) ≠ 0 := by
      have := GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.lamF_ne_zero 1 (1 : HChar K) t
      rw [lamF, pow_one] at this
      exact right_ne_zero_of_mul this
    rw [← coordIn_div E hd hs κ hΩ₀, map_div₀, h1, h2, coordIn_div E hd hs κ hΩ₁, conjChar_one]
    simp only [MonoidHom.one_apply, Units.val_one, mul_one]
    have := (conjChar g ψ (classOf K (condQ 𝔣 Q) t)).ne_zero
    field_simp
  · have := PicFin.finite_picO E _ (condQ_ne_bot hb Q)
    exact (conjChar g ψ).isOfFinOrder (isOfFinOrder_of_finite _)

end GlobalTheory.ToricTransport
end
end

section

open NumberField MeasureTheory GlobalTheory.CuspRep

theorem _root_.GlobalTheory.T.constant_term_slice_levi_moderate_growth : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) (hr : r ≤ a) [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ φ : Sm E a, IsAutForm φ → ∀ (m₁ : GA E r) (t : GL (Fin a) (Af E)) (κ : Kinf E a) (g : GA E (a - r)), ∃ (C : ℝ) (M : ℕ), ∀ y, ‖GlobalTheory.SliceTwo.slice E μ 𝓕 hr φ.1 m₁ t κ (g * infGL E (a - r) y)‖ ≤ C * height y ^ M := by
  first | exact @GlobalTheory.SliceTwo.Growth.norm_slice_le | exact GlobalTheory.SliceTwo.Growth.norm_slice_le | (intros; apply GlobalTheory.SliceTwo.Growth.norm_slice_le <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix

theorem _root_.GlobalTheory.T.mumfordBundle_pullback_trivial_of_im_form_int : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), M.IsLB → GlobalTheory.TorusRM.IsFactorAH u Hm χ → ∀ w : Fin g → ℂ, (∀ l ∈ u.Λ, ∃ n : ℤ, (w ⬝ᵥ Hm.mulVec (star l)).im = n) → ∃ t : ((abelian₂ A M).pull (lift (fst A (𝟙_ (Over (Sp ℂ)))) (snd A (𝟙_ (Over (Sp ℂ))) ≫ u.ex w)).left).Gen, t.IsGen := by
  first | exact @GlobalTheory.TorusRM.hasGen_lam_pull_of_im_int | exact GlobalTheory.TorusRM.hasGen_lam_pull_of_im_int | (intros; apply GlobalTheory.TorusRM.hasGen_lam_pull_of_im_int <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory


open GlobalTheory.TorusRM.LamAdd GlobalTheory.ProdUnifSq in
theorem GlobalTheory.TorusRM.lbIso_lam_of_same_form : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → IsProjOver A.hom →
    ∀ (M M' : LB A.left) (u : HolUnif A M g) (u' : HolUnif A M' g) (Hm : Matrix (Fin g) (Fin g) ℂ)
      (χ : u.Λ → ℂ) (χ' : u'.Λ → ℂ), M.IsLB → M'.IsLB → u'.ex = u.ex →
    GlobalTheory.TorusRM.IsFactorAH u Hm χ → GlobalTheory.TorusRM.IsFactorAH u' Hm χ' → LBIso (abelian₂ A M) (abelian₂ A M') := by
  intro g A _ hA hP M M' u u' Hm χ χ' h1 h2 he f1 f2
  haveI : IsCommMonObj A := hA.comm
  have hl1 : (abelian₂ A M).IsLB := LB.isLB_linComb h1 _ _
  have hl2 : (abelian₂ A M').IsLB := LB.isLB_linComb h2 _ _
  have hPP : IsProjOver (A ⊗ A).hom := GlobalTheory.ProjSpace.isProjOver_pullback hP hP
  refine GlobalTheory.HolUnifSec.hasGen_of_periodic (A ⊗ A) (AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA) hPP _
    (LB.isLB_div hl2 hl1) (g + g)
    (GlobalTheory.SameFactor.divUnif (lamUnif u u rfl) (lamUnif u u' he) rfl)
    (fun _ => 1) (differentiable_const _) (fun _ => one_ne_zero) ?_
  intro l hl p z hz
  obtain ⟨hz2, hz1⟩ := (GlobalTheory.top_le_preimage_inf _ _ _).1 hz
  have hexl : (sqUnif A u).ex (z + l) = (sqUnif A u).ex z := by
    rw [(sqUnif A u).ex_add, ((sqUnif A u).ker l).2 hl, _root_.mul_one]
  have e1 := lam_shift u u rfl h1 f1 p.2 z l hl hz1
  have e2 := lam_shift u u' he h2 f2 p.1 z l hl hz2
  have n1 := (lamUnif u u rfl).fr_ne p.2 (z + l) (by rw [lamUnif_ex, hexl]; exact hz1)
  have n2 := (lamUnif u u' he).fr_ne p.1 (z + l) (by rw [lamUnif_ex, hexl]; exact hz2)
  show 1 * ((lamUnif u u' he).fr p.1 (z + l) * ((lamUnif u u rfl).fr p.2 (z + l))⁻¹) =
    1 * ((lamUnif u u' he).fr p.1 z * ((lamUnif u u rfl).fr p.2 z)⁻¹)
  rw [e1, e2]
  have q1 := Complex.exp_ne_zero (Q Hm z l)
  field_simp
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.hermitian_forms_add_of_factor_product : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → IsProjOver A.hom →
    ∀ (M₁ M₂ M₃ : LB A.left) (u₁ : HolUnif A M₁ g) (u₂ : HolUnif A M₂ g) (u₃ : HolUnif A M₃ g)
      (H₁ H₂ H₃ : Matrix (Fin g) (Fin g) ℂ) (χ₁ : u₁.Λ → ℂ) (χ₂ : u₂.Λ → ℂ) (χ₃ : u₃.Λ → ℂ),
    M₁.IsLB → M₂.IsLB → M₃.IsLB → u₂.ex = u₁.ex → u₃.ex = u₁.ex →
    IsFactorAH u₁ H₁ χ₁ → IsFactorAH u₂ H₂ χ₂ → IsFactorAH u₃ H₃ χ₃ → H₃ = H₁ + H₂ →
    LBIso (abelian₂ A M₂) (LB.div (abelian₂ A M₃) (abelian₂ A M₁)) := by
  first | exact @GlobalTheory.TorusRM.lbIso_lam_of_add | exact GlobalTheory.TorusRM.lbIso_lam_of_add | (intros; apply GlobalTheory.TorusRM.lbIso_lam_of_add <;> assumption)
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.cubeLineBundle_iso_of_appellHumbert_adjoint : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (N : LB A.left), N.IsLB → Out.RelAmple A N → ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), M.IsLB → GlobalTheory.TorusRM.IsFactorAH u Hm χ → ∀ (f f' : A ⟶ A) (F F' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), IsMonHom f → IsMonHom f' → (∀ z, u.ex (F z) = u.ex z ≫ f) → (∀ z, u.ex (F' z) = u.ex z ≫ f') → (∀ z w, hermForm Hm (F z) w = hermForm Hm z (F' w)) → LBIso (cubeLB A ![fst A A ≫ f, snd A A] M) (cubeLB A ![fst A A, snd A A ≫ f'] M) := by
  first | (exact @GlobalTheory.AdjPullFrame.lbIso_cubeLB_of_adjoint) | (exact GlobalTheory.AdjPullFrame.lbIso_cubeLB_of_adjoint) | (intros; apply GlobalTheory.AdjPullFrame.lbIso_cubeLB_of_adjoint  <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

theorem _root_.GlobalTheory.T.exists_disjoint_unipotentCells_cover_compact_mirabolic : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (C : Set (GA E (m + 1))), IsCompact C → ∀ V : GA E (m + 1) → Subgroup (GL (Fin (m + 1)) (Af E)), (∀ q, IsOpen (V q : Set (GL (Fin (m + 1)) (Af E)))) → ∃ (K : Subgroup (GL (Fin (m + 1)) (Af E))) (R : Finset (GA E (m + 1))) (j : GA E (m + 1) → GA E (m + 1)), IsOpen (K : Set (GL (Fin (m + 1)) (Af E))) ∧ IsCompact (K : Set (GL (Fin (m + 1)) (Af E))) ∧ (∀ x ∈ R, j x ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m) ∧ GeneralLinearGroup.map (pInf E) (j x) = 1 ∧ K ≤ V (j x) ∧ GlobalTheory.JSW.MirPatch.cell K x ⊆ GlobalTheory.JSW.MirPatch.cell (V (j x)) (j x)) ∧ (∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), (∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * p ∈ C) → ∃ x ∈ R, p ∈ GlobalTheory.JSW.MirPatch.cell K x) ∧ (∀ x ∈ R, ∀ x' ∈ R, ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), p ∈ GlobalTheory.JSW.MirPatch.cell K x → p ∈ GlobalTheory.JSW.MirPatch.cell K x' → x = x') := by
  first | exact @GlobalTheory.JSW.MirPatch.Cover.exists_cover | exact GlobalTheory.JSW.MirPatch.Cover.exists_cover | (intros; apply GlobalTheory.JSW.MirPatch.Cover.exists_cover <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

theorem _root_.GlobalTheory.T.mirabolic_cell_finite_union_local_double_cosets : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (K : Subgroup (GL (Fin (m + 1)) (Af E))), IsOpen (K : Set (GL (Fin (m + 1)) (Af E))) → IsCompact (K : Set (GL (Fin (m + 1)) (Af E))) → ∀ q : GA E (m + 1), ∃ (U : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin (m + 1)) (w.adicCompletion E))) (N : ℕ) (z : Fin N → ∀ w : HeightOneSpectrum (𝓞 E), GL (Fin (m + 1)) (w.adicCompletion E)), (∀ w ∈ S, IsCompact (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E))) ∧ IsOpen (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E))) ∧ ∀ u ∈ U w, locGL E (m + 1) w u ∈ K) ∧ (∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), ∀ i j : Fin N, (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p ∈ GlobalTheory.JSW.Cut.cell (z i w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p ∈ GlobalTheory.JSW.Cut.cell (z j w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) → i = j) ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), (p ∈ GlobalTheory.JSW.MirPatch.cell K q ↔ ∃ i : Fin N, ∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p ∈ GlobalTheory.JSW.Cut.cell (z i w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) := by
  first | (exact @GlobalTheory.JSW.MirPatch.cell_decomp) | (exact GlobalTheory.JSW.MirPatch.cell_decomp) | (intros; apply GlobalTheory.JSW.MirPatch.cell_decomp  <;> assumption)
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

theorem _root_.GlobalTheory.T.kernelOperator_GLn_smoothAffineTranslation_section : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (σ₀ : Fin n → Fin n → Cinf E) (L : Z →L[ℝ] (Fin n → Fin n → Cinf E)) (χ : Z → ℂ) (α : (Fin n → Fin n → Cinf E) → ℂ), ContDiff ℝ ∞ χ → HasCompactSupport χ → (∀ z ∈ tsupport χ, IsUnit (Matrix.of (σ₀ + L z))) → ContDiff ℝ ∞ α → HasCompactSupport α → tsupport α ⊆ {x | IsUnit (Matrix.of x)} → ∀ T : (GL (Fin n) (Cinf E) → ℂ) → Z → GL (Fin n) (Cinf E) → ℂ, IsKerOpInf T → IsKerOpInf (fun W z g => χ z * T (smoothMatInf α W) z (g * (toGLInf (Matrix.of (σ₀ + L z)))⁻¹)) := by
  first | exact @GlobalTheory.JSW.MirCinf.kerOpInf_section | exact GlobalTheory.JSW.MirCinf.kerOpInf_section | (intros; apply GlobalTheory.JSW.MirCinf.kerOpInf_section <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV

namespace GlobalTheory.BrPairF

variable {K ι : Type} [Field K] [Fintype ι] {n N : ℕ}

def brPairF (σ : ι → DomWeight n) (hN : N = n + 1) (Λ : ι → DomWeight N) :
    VV K Λ →ₗ[K] (VV K fun τ => (σ τ).dual) →ₗ[K] K :=
  (pairBK σ).compl₁₂ (Formalism.L2.Col.Br.brStd hN Λ σ) (GlobalTheory.FunObj.funEquiv σ).symm.toLinearMap

theorem brPairF_apply (σ : ι → DomWeight n) (hN : N = n + 1) (Λ : ι → DomWeight N) (u : VV K Λ)
    (v : VV K fun τ => (σ τ).dual) :
    brPairF σ hN Λ u v = pairBK σ (Formalism.L2.Col.Br.brStd hN Λ σ u) ((GlobalTheory.FunObj.funEquiv σ).symm v) := rfl

end GlobalTheory.BrPairF

end
end

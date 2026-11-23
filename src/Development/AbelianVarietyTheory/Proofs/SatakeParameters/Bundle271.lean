module

public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import ReciprocityTheory.Automorphisms.SplitCoeAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle051
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle004
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.PadicSubsetSums.StableGradedCounts.CardLtAddCardGtAddCardEq
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle068
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.IsBichar
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.Automorphisms.PlaceA
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle009

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TypeBlockPf

theorem splitAt : ∀ (D : D7) (w : PlE D.host), IsSplitPl D.host w → ∃ s : SplitPlace D.host.E, s.w = w := by
  intro D w hw
  have hc : ∀ x : 𝓞 D.host.E, ((GlobalTheory.SumWCompare.cj D.host.E x : 𝓞 D.host.E) : D.host.E) = D.host.conj (x : D.host.E) := by
    intro x; rw [GlobalTheory.SumWCompare.cj_coe, GlobalTheory.DimPartsCompare.star_conj]
  have hcc : ∀ z : D.host.E, D.host.conj (D.host.conj z) = z := by
    intro z; rw [← GlobalTheory.DimPartsCompare.star_conj, ← GlobalTheory.DimPartsCompare.star_conj, star_star]
  obtain ⟨x, hx, hy⟩ := hw
  have hsp : IsSplitPl D.host (GlobalTheory.DimPartsCompare.cPl w) := by
    refine ⟨GlobalTheory.SumWCompare.cj D.host.E x, ?_, fun y e hy' => ?_⟩
    · rw [GlobalTheory.DimPartsCompare.mem_cPl, GlobalTheory.SumWCompare.cj_cj]; exact hx
    · rw [GlobalTheory.DimPartsCompare.mem_cPl] at hy'
      refine hy _ ?_ hy'
      rw [hc, show y = x from RingOfIntegers.ext (by rw [e, hc, hcc])]
  obtain ⟨s, -, hs, -⟩ := GlobalTheory.SplitConjPlace.splitEx_all D _ hsp
  refine ⟨s, HeightOneSpectrum.ext (Ideal.ext fun y => ?_)⟩
  have := hs (GlobalTheory.SumWCompare.cj D.host.E y) y (by rw [hc, hcc])
  rw [GlobalTheory.DimPartsCompare.mem_cPl, GlobalTheory.SumWCompare.cj_cj] at this
  exact this.symm

end GlobalTheory.TypeBlockPf
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.GalClose

open GlobalTheory.CuspRep

theorem isSSRep_rankOne {Γ k : Type} [Group Γ] [Field k] (ρ : Γ →* GL (Fin 1) k) : IsSSRep ρ := by
  intro W _
  by_cases h : W = ⊥
  · refine ⟨⊤, fun g v _ => Submodule.mem_top, ?_⟩
    rw [h]; exact isCompl_bot_top
  · have hW : W = ⊤ := by
      obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
      have h0 : v 0 ≠ 0 := fun e => hv0 (funext fun j => by rw [Subsingleton.elim j 0, e]; rfl)
      refine eq_top_iff.2 fun u _ => ?_
      have : u = (u 0 / v 0) • v := funext fun j => by
        rw [Subsingleton.elim j 0, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ h0]
      rw [this]; exact W.smul_mem _ hv
    refine ⟨⊥, fun g v hv => ?_, ?_⟩
    · rw [Submodule.mem_bot] at hv ⊢; rw [hv]; exact Matrix.mulVec_zero _
    · rw [hW]; exact isCompl_top_bot

end GlobalTheory.GalClose
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.GoodCuspPoint

theorem param_parts_pos_rank (D : D7) (i : D.nd.Loc) (x : D.nd.X i) (Sig : List (Formalism.BasicNotions.Part D.naut.CG))
    (hx : HasParamX D.nd D.naut i x Sig) :
    (∀ p ∈ Sig, 1 ≤ p.a ∧ 1 ≤ p.d) ∧ rankIso D.nd D.naut Sig = D.R.r := by
  apply _root_.Formalism.MainNotions.AdmissibleThreePrime.parts_of <;> assumption

theorem cuspidal_of_good_labels (D : D7) (hT : Formalism.MainNotions.SumRepresentations.tieLab D) (i : D.nd.Loc) (x : D.nd.X i)
    (Sig : List (Formalism.BasicNotions.Part D.naut.CG)) (hx : HasParamX D.nd D.naut i x Sig)
    (hg : goodSig D.nd D.naut Sig) : IsCuspIso D.nd D.naut Sig := by
  obtain ⟨hpos, hrank⟩ := param_parts_pos_rank D i x Sig hx
  let k : Fin 2 := 0
  have : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨h1, h2, -, -, h5, -⟩ := (hg k).1
  have : Nonempty (D.nd.PlG k) := by
    rw [← Fintype.card_pos_iff, D.nd.card_PlG k]
    show 0 < 2 * D.R.ord
    have := D.R.ord_pos
    omega
  have hr : 1 ≤ D.R.r := by
    have := D.R.two_le_m
    show 1 ≤ D.R.k + D.R.m - 1
    omega
  have hf : ∀ v, D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v)) =
      ∏ j : Fin Sig.length,
        D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG (Sig.get j).π (D.naut.plGw k v)) ^ (Sig.get j).d := by
    intro v
    rw [Formalism.MainNotions.SumRepresentations.inertiaCharpoly_eq_of_iso D.nd D.naut hT k v Sig,
      Formalism.MainNotions.SumRepresentations.list_prod_fin Sig (fun p => D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG p.π (D.naut.plGw k v)) ^ p.d)]
  have hrk : ∑ j : Fin Sig.length, (Sig.get j).a * (Sig.get j).d = D.R.r := by
    rw [← hrank, rankIso, Formalism.MainNotions.SumRepresentations.list_sum_fin Sig (fun p => p.a * p.d)]
  have hd : ∀ j : Fin Sig.length, 1 ≤ (Sig.get j).a ∧ 1 ≤ (Sig.get j).d :=
    fun j => hpos _ (List.get_mem Sig j)
  have hdeg : ∀ v (j : Fin Sig.length),
      (D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG (Sig.get j).π (D.naut.plGw k v))).natDegree =
        (Sig.get j).a := by
    intro v
    have hne : ∀ j ∈ (Finset.univ : Finset (Fin Sig.length)),
        D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG (Sig.get j).π (D.naut.plGw k v)) ^ (Sig.get j).d ≠ 0 := by
      rw [← Finset.prod_ne_zero_iff, ← hf v]
      exact (h1 v).1.ne_zero
    have hsum : ∑ j : Fin Sig.length,
        (D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG (Sig.get j).π (D.naut.plGw k v))).natDegree *
          (Sig.get j).d =
        ∑ j : Fin Sig.length, (Sig.get j).a * (Sig.get j).d := by
      have h1' : (D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v))).natDegree = D.R.r :=
        (h1 v).2.1
      rw [hrk, ← h1', hf v, natDegree_prod _ _ hne]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [natDegree_pow, mul_comm]
    have hle : ∀ j ∈ (Finset.univ : Finset (Fin Sig.length)),
        (D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG (Sig.get j).π (D.naut.plGw k v))).natDegree *
          (Sig.get j).d ≤ (Sig.get j).a * (Sig.get j).d := by
      intro j _
      refine Nat.mul_le_mul_right _ ?_
      have := hT.2 k v (D.naut.locG (Sig.get j).π (D.naut.plGw k v))
      rwa [D.naut.locG_dim] at this
    intro j
    have := (Finset.sum_eq_sum_iff_of_le hle).1 hsum j (Finset.mem_univ j)
    exact Nat.eq_of_mul_eq_mul_right (hd j).2 this
  obtain ⟨hc, hall⟩ := Formalism.IrreducibleCountingLemmas.Z.good_cuspidal_multiplicity_one (ZMod (D.host.g k)) (D.nd.PlG k) D.R.r
    (fun v => D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v)))
    (Fin Sig.length) (fun j => (Sig.get j).a) (fun j => (Sig.get j).d)
    (fun v j => D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG (Sig.get j).π (D.naut.plGw k v))) hr
    (fun v => (h1 v).2.1) h2 hf hdeg (fun j => (hd j).1) (fun j => (hd j).2)
    (by
      rintro ⟨a, ha1, ha2, ha⟩
      obtain ⟨v, hv⟩ := h5 a ha1 ha2
      exact hv (ha v))
  rw [Fintype.card_fin] at hc
  obtain ⟨p, rfl⟩ := List.length_eq_one_iff.1 hc
  obtain ⟨hd1, ha1⟩ := hall ⟨0, by simp⟩
  obtain ⟨a, π, d⟩ := p
  simp only [List.get_eq_getElem, List.getElem_cons_zero] at hd1 ha1
  subst hd1 ha1
  exact ⟨π, rfl⟩

theorem main : ∀ D : D7, Formalism.MainNotions.SumRepresentations.tieLab D → GlobalTheory.LocalInv.GoodCuspidal D.nd D.naut :=
  fun D hT i x Sig hx hg => cuspidal_of_good_labels D hT i x Sig hx hg

end GlobalTheory.GoodCuspPoint
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DesignBC

open Formalism.FrobeniusOrbits

variable (D : D7)

theorem conj_sqrtMinusD : D.host.conj D.host.sqrtMinusD = -D.host.sqrtMinusD := by
  apply D.host.φ₀.injective
  have h2 := D.host.conjE_apply D.host.φ₀ D.host.sqrtMinusD
  have h3 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  rw [h2, map_neg, h3]
  simp

theorem sqrtMinusD_mul_self : D.host.sqrtMinusD * D.host.sqrtMinusD = -((D.host.d : ℕ) : D.host.E) := by
  rw [← sq]
  exact D.host.sqd_sq

theorem conj_conj (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  apply D.host.φ₀.injective
  rw [D.host.conjE_apply, D.host.conjE_apply, Complex.conj_conj]

theorem mem_F_iff (x : D.host.E) : x ∈ D.host.F ↔ D.host.conj x = x :=
  D.host.conjE_mem_hostF_iff x

theorem d_ne_zero : ((D.host.d : ℕ) : D.host.E) ≠ 0 :=
  Nat.cast_ne_zero.mpr D.host.hyp.2.1.ne_zero

theorem sqrtMinusD_ne_zero : D.host.sqrtMinusD ≠ 0 := by
  intro h
  have := sqrtMinusD_mul_self D
  rw [h, zero_mul, eq_comm, neg_eq_zero] at this
  exact d_ne_zero D this

end GlobalTheory.DesignBC

namespace GlobalTheory.DesignBC

open Formalism.FrobeniusOrbits

variable (D : D7)

theorem hypEFK : Formalism.MainNotions.SphericalInertData.HypEFK D := by
  rw [Formalism.MainNotions.SphericalInertData.HypEFK, eq_top_iff]
  intro x _
  set c := D.host.conj
  set s := D.host.sqrtMinusD
  have hs : s ≠ 0 := sqrtMinusD_ne_zero D
  have hcs : c s = -s := conj_sqrtMinusD D
  have hcc : c (c x) = x := conj_conj D x
  have hu : (x + c x) / 2 ∈ D.host.F := by
    rw [mem_F_iff]
    show c ((x + c x) / 2) = _
    rw [map_div₀, map_add (f := _), hcc, map_ofNat, add_comm]
  have hv : (x - c x) / (2 * s) ∈ D.host.F := by
    rw [mem_F_iff]
    show c ((x - c x) / (2 * s)) = _
    rw [map_div₀, map_sub, map_mul, hcc, map_ofNat, hcs]
    field_simp
    ring
  have hK : s ∈ D.host.K := IntermediateField.mem_adjoin_simple_self ℚ _
  have hx : x = (x + c x) / 2 + (x - c x) / (2 * s) * s := by
    field_simp
    ring
  rw [hx]
  refine add_mem (Subfield.subset_closure (Or.inl hu))
    (mul_mem (Subfield.subset_closure (Or.inl hv)) (Subfield.subset_closure (Or.inr hK)))

theorem two_le_finrank : 2 ≤ Module.finrank ℚ D.host.F := by
  have h := D.host.finrank_hostF
  show 2 ≤ Module.finrank ℚ (D.host.F)
  rw [h]
  have := D.R.ord_pos
  omega

end GlobalTheory.DesignBC

namespace GlobalTheory.DesignBC

open Formalism.FrobeniusOrbits Polynomial

variable (D : D7)

theorem d_eq : ∃ m : ℕ, D.host.d + 1 = 8 * m := ⟨(D.host.d + 1) / 8, by
  have := D.host.hyp.2.2.2.1; omega⟩

theorem isIntegral_half (y : D.host.E) (hy : y * y = -((D.host.d : ℕ) : D.host.E)) :
    IsIntegral ℤ ((1 + y) / 2) := by
  obtain ⟨m, hm⟩ := d_eq D
  refine ⟨X ^ 2 - X + C (2 * (m : ℤ)), ?_, ?_⟩
  · have : (X ^ 2 - X + C (2 * (m : ℤ)) : ℤ[X]) = X ^ 2 + (C (2 * (m : ℤ)) - X) := by ring
    rw [this]
    refine (monic_X_pow 2).add_of_left ?_
    refine lt_of_le_of_lt (degree_sub_le _ _) ?_
    rw [degree_X_pow, degree_X]
    refine max_lt (lt_of_le_of_lt degree_C_le (by norm_num)) (by norm_num)
  · have hd : ((D.host.d : ℕ) : D.host.E) = 8 * (m : D.host.E) - 1 := by
      have : ((D.host.d + 1 : ℕ) : D.host.E) = ((8 * m : ℕ) : D.host.E) := by rw [hm]
      push_cast at this
      linear_combination this
    simp only [eval₂_add, eval₂_sub, eval₂_X_pow, eval₂_X, eval₂_C]
    simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, algebraMap_int_eq, eq_intCast]
    push_cast
    rw [hd] at hy
    linear_combination (1/4 : D.host.E) * hy

end GlobalTheory.DesignBC

namespace GlobalTheory.DesignBC

open Formalism.FrobeniusOrbits

variable (D : D7)

theorem isSplitPl_of_two_mem (w : PlE D.host) (h2 : ((2 : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) :
    IsSplitPl D.host w := by
  set s := D.host.sqrtMinusD
  have hss : s * s = -((D.host.d : ℕ) : D.host.E) := sqrtMinusD_mul_self D
  have hss' : (-s) * (-s) = -((D.host.d : ℕ) : D.host.E) := by rw [neg_mul_neg]; exact hss
  have hcs : D.host.conj s = -s := conj_sqrtMinusD D
  obtain ⟨m, hm⟩ := d_eq D
  let α : 𝓞 D.host.E := ⟨(1 + s) / 2, isIntegral_half D s hss⟩
  let β : 𝓞 D.host.E := ⟨(1 + -s) / 2, isIntegral_half D (-s) hss'⟩
  have hα : ((α : 𝓞 D.host.E) : D.host.E) = (1 + s) / 2 := rfl
  have hβ : ((β : 𝓞 D.host.E) : D.host.E) = (1 + -s) / 2 := rfl
  have hsum : α + β = 1 := by
    apply RingOfIntegers.ext
    show (1 + s) / 2 + (1 + -s) / 2 = ((1 : 𝓞 D.host.E) : D.host.E)
    push_cast
    ring
  have hprod : α * β = ((2 : ℕ) : 𝓞 D.host.E) * (m : 𝓞 D.host.E) := by
    apply RingOfIntegers.ext
    have key : ((((2 : ℕ) : 𝓞 D.host.E) * (m : 𝓞 D.host.E) : 𝓞 D.host.E) : D.host.E) = 2 * (m : D.host.E) := by
      exact (map_mul (algebraMap (𝓞 D.host.E) D.host.E) _ _).trans (by rw [map_natCast, map_natCast]; norm_num)
    show (1 + s) / 2 * ((1 + -s) / 2) = ((((2 : ℕ) : 𝓞 D.host.E) * (m : 𝓞 D.host.E) : 𝓞 D.host.E) : D.host.E)
    rw [key]
    have hd : ((D.host.d : ℕ) : D.host.E) = 8 * (m : D.host.E) - 1 := by
      have : ((D.host.d + 1 : ℕ) : D.host.E) = ((8 * m : ℕ) : D.host.E) := by rw [hm]
      push_cast at this
      linear_combination this
    rw [hd] at hss
    linear_combination (-1/4 : D.host.E) * hss
  have hcα : D.host.conj ((α : 𝓞 D.host.E) : D.host.E) = ((β : 𝓞 D.host.E) : D.host.E) := by
    rw [hα, hβ, map_div₀, map_add (f := _), map_one, hcs, map_ofNat]
  have hcβ : D.host.conj ((β : 𝓞 D.host.E) : D.host.E) = ((α : 𝓞 D.host.E) : D.host.E) := by
    rw [← hcα, conj_conj]
  have hne : ∀ x y : 𝓞 D.host.E, x + y = 1 → x ∈ w.asIdeal → y ∉ w.asIdeal := by
    intro x y hxy hx hy
    exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hxy ▸ add_mem hx hy))
  have hmem : α * β ∈ w.asIdeal := by
    rw [hprod]; exact Ideal.mul_mem_right _ _ h2
  rcases w.isPrime.mem_or_mem hmem with ha | hb
  · refine ⟨α, ha, fun y hy => ?_⟩
    have : y = β := RingOfIntegers.coe_injective (hy.trans hcα)
    rw [this]; exact hne α β hsum ha
  · refine ⟨β, hb, fun y hy => ?_⟩
    have : y = α := RingOfIntegers.coe_injective (hy.trans hcβ)
    rw [this]; exact hne β α (by rw [add_comm]; exact hsum) hb

end GlobalTheory.DesignBC

namespace GlobalTheory.DesignBC

theorem jointCond_of_definite : ∀ D : D7, (∀ j, 1 ≤ j → j ≤ D.R.m → (letI := D.host.cmStar; (D.sp.V j).IsDefinite)) →
    GlobalDatumCompatibility D := by
  intro D hdef
  refine ⟨hypEFK D, ⟨two_le_finrank D, fun w hw h2 => hw (isSplitPl_of_two_mem D w h2)⟩, hdef⟩

end GlobalTheory.DesignBC
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.TwistParamAbove

theorem isFrobSS_wdRep {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] :
    IsFrobSS (wdRho P ι Bw h hj ρ) (wdN P ι ρ) (wdRep P ι Bw h hj ρ) := by
  obtain ⟨u, hN, hu, -, hc, hρ⟩ := wdRep_spec P ι Bw h hj ρ
  have := isFrobSS_of_unipotent u hu hc hρ
  rwa [hN] at this

theorem isModel_twist {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] {Bw : LocBridge l E Ω Gw O} {a : ℕ} {L : FinExt l} {r : ↥Gw →* GL (Fin a) (Om l)} {c : ↥Gw →* GL (Fin 1) (Om l)} {s : ↥Gw →* GL (Fin a) ↥L.1} {m : ↥Gw →* GL (Fin 1) ↥L.1} (h₁ : IsModel Bw r L s) (h₂ : IsModel Bw c L m) :
    IsModel Bw (Formalism.MainNotions.SumRepresentations.At.twGL r (Matrix.GeneralLinearGroup.det.comp c)) L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m)) := by
  refine ⟨h₁.1, ?_⟩
  rw [← h₁.2, ← h₂.2]
  ext g i j
  simp [mapRep, Formalism.MainNotions.SumRepresentations.At.twGL, Matrix.det_unique, Matrix.algebraMap_eq_diagonal, Matrix.diagonal_mul]
  rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_mul]
  simp [Matrix.map_apply]

end GlobalTheory.TwistParamAbove
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TwistGal

theorem twGL_coe {Γ k : Type} [Group Γ] [CommRing k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (χ : Γ →* kˣ) (g : Γ) :
    ((Formalism.MainNotions.SumRepresentations.At.twGL ρ χ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) =
      ((χ g : kˣ) : k) • (ρ g : Matrix (Fin a) (Fin a) k) := by
  rw [Algebra.smul_def]
  rfl

theorem cont_twGL {Γ k : Type} [Group Γ] [TopologicalSpace Γ] [CommRing k] [TopologicalSpace k] [IsTopologicalRing k] {a : ℕ}
    (ρ : Γ →* GL (Fin a) k) (χ : Γ →* GL (Fin 1) k)
    (hρ : Continuous fun g => ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k))
    (hχ : Continuous fun g => ((χ g : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k)) :
    Continuous fun g => ((Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ) g : GL (Fin a) k) :
      Matrix (Fin a) (Fin a) k) := by
  simp only [twGL_coe]
  refine Continuous.smul (M := k) ?_ hρ
  exact hχ.matrix_det

theorem comp_twGL {Γ Γ' k : Type} [Group Γ] [Group Γ'] [CommRing k] {a : ℕ} (ρ : Γ →* GL (Fin a) k)
    (χ : Γ →* GL (Fin 1) k) (f : Γ' →* Γ) :
    (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)).comp f =
      Formalism.MainNotions.SumRepresentations.At.twGL (ρ.comp f) (Matrix.GeneralLinearGroup.det.comp (χ.comp f)) :=
  MonoidHom.ext fun _ => rfl

end GlobalTheory.TwistGal

end
end

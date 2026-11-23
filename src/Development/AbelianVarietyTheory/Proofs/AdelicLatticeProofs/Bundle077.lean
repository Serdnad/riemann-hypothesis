module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle002
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle070
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle077
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle078
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle079
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle042
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle076
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix
open GlobalTheory.Member

namespace GlobalTheory.UnRep.Space

theorem finrank_two (D : D7) : Module.finrank D.host.F D.host.E = 2 :=
  Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield D.host.E) D.host.E

theorem isUnA_finHom {D : D7} (V : HSp D) (g : GA D V) : GlobalTheory.UnRep.IsUnA (cF D) V.gramᵀ (finHom V g).1 := by
  intro x y
  rw [GlobalTheory.UnitarySplit.hermA_eq, GlobalTheory.UnitarySplit.hermA_eq]
  exact (GlobalTheory.Member.RatElt.mem_UJ_iff _ _ _).1 (GlobalTheory.UnitarySplit.finHom_mem V g) y x

theorem herm_neg_eq {D : D7} (V : HSp D) (u v : Fin V.rank → D.host.E) :
    herm (-V.gramᵀ) u v = -GlobalTheory.UnRep.hermE (cF D) V.gramᵀ u v := by
  unfold herm GlobalTheory.UnRep.hermE
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  change u a * (-V.gram b a) * cc (v b) = -(u a * V.gram b a * cc (v b))
  ring



theorem exists_rep_suppSplit : ∀ (D : D7) (V : HSp D) (N : ℕ), 0 < N → ∀ g : GA D V, ∃ γ ∈ GQ V, ∃ a ∈ GinfC V, ∃ h ∈ GfC V, ∃ k ∈ GfC V, g = γ * a * h * k ∧ FinCong V N k ∧ GlobalTheory.UnRep.SuppSplit (cF D) N (finHom V h).1 := by
  intro D V N hN g
  obtain ⟨e1, -, hfg, hsp, c2, -, c1, gh, gd, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  obtain ⟨γ', h', k', u1, u2, u3, hg, hs, hk, -⟩ := GlobalTheory.T.exists_unitary_adelic_decomposition_split_support D.host.F D.host.E (cF D) V.rank V.gramᵀ
    ⟨c2, c1, gh, gd⟩ (finrank_two D) (latC V) hfg hsp (finHom V g) N (isUnA_finHom V g) hN
  obtain ⟨-, -, -, lift, -⟩ := GlobalTheory.UnitarySplit.real_finite_split D V
  obtain ⟨r1, -, r3, -⟩ := GlobalTheory.Member.RatElt.rational_elements D V
  obtain ⟨h, hh, eh⟩ := lift h' u2
  obtain ⟨k, hk', ek⟩ := lift k' u3
  obtain ⟨γ, hγ⟩ := r3 γ' fun u v => by rw [herm_neg_eq, herm_neg_eq, u1]
  have eγ : (finHom V γ).1 = GlobalTheory.UnRep.fm D.host.F γ'.1 := GlobalTheory.Member.RatElt.fin_eq hγ
  have e : finHom V g = finHom V γ * finHom V h * finHom V k := by
    apply Units.ext
    rw [hg, Units.val_mul, Units.val_mul, eγ, eh, ek]
  refine ⟨γ, (r1 γ).2 ⟨γ', hγ⟩, γ⁻¹ * g * k⁻¹ * h⁻¹, ?_, h, hh, k, hk', by group, ?_, ?_⟩
  · change finHom V _ = 1
    simp only [map_mul, map_inv, e]
    group
  · unfold FinCong
    rw [e1, ek]
    exact hk
  · rw [eh]
    exact hs

end GlobalTheory.UnRep.Space
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem np_of_finrank_one (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
    (h : Module.finrank F E = 1) : NP F E := by
  intro x _ _
  refine ⟨algebraMap F E x, ?_⟩
  rw [Algebra.norm_algebraMap, h, pow_one]

theorem np_of_finrank_prime (p : ℕ) (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] [IsGalois F E] (hp : p.Prime) (h : Module.finrank F E = p) :
    NP F E := by
  by_cases h2 : p = 2
  · exact GlobalTheory.T.np_of_finrank_two' F E (h2 ▸ h)
  · exact GlobalTheory.T.np_of_odd_prime_degree' p F E hp h2 h

theorem hasseNormPrinciple_cyclic_of_finrank (n : ℕ) : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E], Module.finrank F E = n → IsGalois F E → IsCyclic (E ≃ₐ[F] E) → NP F E := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro F E _ _ _ _ _ hn hG hC
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  by_cases h1 : n = 1
  · exact np_of_finrank_one F E (hn.trans h1)
  obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd h1
  have : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card (E ≃ₐ[F] E) = n := (IsGalois.card_aut_eq_finrank F E).trans hn
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := E ≃ₐ[F] E) p (hcard ▸ hpn)
  set H : Subgroup (E ≃ₐ[F] E) := Subgroup.zpowers g with hH
  have hHc : Nat.card H = p := by rw [hH, Nat.card_zpowers, hg]
  have : H.Normal := by
    constructor
    intro a ha b
    have hc : b * a = a * b := by
      obtain ⟨s, hs⟩ := IsCyclic.exists_generator (α := E ≃ₐ[F] E)
      obtain ⟨i, rfl⟩ := hs a
      obtain ⟨j, rfl⟩ := hs b
      exact (Commute.zpow_zpow_self s j i).eq
    rw [hc, mul_inv_cancel_right]
    exact ha
  let M : IntermediateField F E := IntermediateField.fixedField H
  have : NumberField M := NumberField.of_module_finite F M
  have hME : Module.finrank M E = p :=
    (IntermediateField.finrank_fixedField_eq_card H).trans hHc
  have : IsGalois M E := IsGalois.tower_top_of_isGalois F M E
  have hFM : IsGalois F M := IsGalois.of_fixedField_normal_subgroup H
  have hCM : IsCyclic (M ≃ₐ[F] M) :=
    isCyclic_of_surjective (AlgEquiv.restrictNormalHom (F := F) (K₁ := E) M)
      (AlgEquiv.restrictNormalHom_surjective E)
  have hmul : Module.finrank F M * Module.finrank M E = n :=
    (Module.finrank_mul_finrank F M E).trans hn
  have hpos : 0 < Module.finrank F M := Module.finrank_pos
  have hlt : Module.finrank F M < n := by
    rw [← hmul, hME]
    exact lt_mul_of_one_lt_right hpos hp.one_lt
  exact GlobalTheory.T.hasseNormPrinciple_of_cyclic_tower F M E hC (np_of_finrank_prime p M E hp hME) (ih _ hlt F M rfl hFM hCM)

theorem np_cyclic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E], IsGalois F E → IsCyclic (E ≃ₐ[F] E) → NP F E :=
  fun F E _ _ _ _ _ hG hC => hasseNormPrinciple_cyclic_of_finrank _ F E rfl hG hC

end GlobalTheory.CNorm
end

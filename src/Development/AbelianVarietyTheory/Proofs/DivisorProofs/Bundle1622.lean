module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
import Aesop.Main
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1574
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.HaarSum
open MeasureTheory

theorem vol_mul_relIndex {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (H H' : Subgroup G) (hle : H' ≤ H)
    (hc : IsCompact (H : Set G)) (ho : IsOpen (H' : Set G)) :
    μ.real H' * (H'.relIndex H : ℝ) = μ.real H ∧ H'.relIndex H ≠ 0 := by
  haveI : CompactSpace H := isCompact_iff_compactSpace.1 hc
  have hHo : IsOpen (H : Set G) := Subgroup.isOpen_mono hle ho
  have ho' : IsOpen ((H'.subgroupOf H : Subgroup H) : Set H) := ho.preimage continuous_subtype_val
  haveI : Finite (H ⧸ H'.subgroupOf H) := (H'.subgroupOf H).quotient_finite_of_isOpen ho'
  haveI : (H'.subgroupOf H).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hemb : MeasurableEmbedding (H.subtype : H → G) := MeasurableEmbedding.subtype_coe hHo.measurableSet
  have : (μ.comap (H.subtype : H → G)).IsMulLeftInvariant := Measure.IsMulLeftInvariant.comap μ hemb
  have key := (H'.subgroupOf H).index_mul_measure ho'.measurableSet (μ.comap (H.subtype : H → G))
  rw [hemb.comap_apply, hemb.comap_apply] at key
  have e1 : (H.subtype : H → G) '' Set.univ = (H : Set G) := by ext x; simp
  have e2 : (H.subtype : H → G) '' ((H'.subgroupOf H : Subgroup H) : Set H) = (H' : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hle hx⟩, hx, rfl⟩
  rw [e1, e2] at key
  refine ⟨?_, Subgroup.FiniteIndex.index_ne_zero⟩
  rw [Subgroup.relIndex, Measure.real, Measure.real, ← key, ENNReal.toReal_mul, mul_comm]
  simp

theorem integral_eq_sum_cosets {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (S : Subgroup G) (hS : IsOpen (S : Set G))
    (hfin : μ (S : Set G) ≠ ⊤) (u : G → ℂ) (hu : ∀ x, ∀ s ∈ S, u (x * s) = u x) (F : Finset (G ⧸ S))
    (hF : ∀ q : G ⧸ S, q ∉ F → u q.out = 0) :
    ∫ x, u x ∂μ = (μ.real (S : Set G) : ℂ) * ∑ q ∈ F, u q.out := by
  have key : ∀ x : G, u ((x : G ⧸ S).out) = u x := fun x => by
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul S x
    rw [hh]
    exact hu x h h.2
  have hset : ∀ q : G ⧸ S, {x : G | (x : G ⧸ S) = q} = (fun x => q.out⁻¹ * x) ⁻¹' (S : Set G) := by
    intro q
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe]
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rw [eq_comm]
    exact QuotientGroup.eq
  have hmeas : ∀ q : G ⧸ S, MeasurableSet {x : G | (x : G ⧸ S) = q} := fun q => by
    rw [hset]
    exact (hS.preimage (continuous_const_mul _)).measurableSet
  have hμ : ∀ q : G ⧸ S, μ {x : G | (x : G ⧸ S) = q} = μ (S : Set G) := fun q => by
    rw [hset]
    exact measure_preimage_mul μ _ _
  have hfun : u = fun x => ∑ q ∈ F, ({x : G | (x : G ⧸ S) = q}.indicator (fun _ => u q.out) x) := by
    funext x
    rw [Finset.sum_eq_single (x : G ⧸ S)]
    · simp [Set.indicator, key]
    · intro q _ hq
      simp [Set.indicator, Ne.symm hq]
    · intro hx
      have h0 := hF _ hx
      rw [key] at h0
      simp [Set.indicator, key, h0]
  conv_lhs => rw [hfun]
  rw [integral_finsetSum]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [integral_indicator_const _ (hmeas q), Measure.real, hμ q, Complex.real_smul, Measure.real]
  · intro q _
    exact (integrableOn_const (hμ q ▸ hfin)).integrable_indicator (hmeas q)

theorem finite_cosets {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (S : Subgroup G)
    (hS : IsOpen (S : Set G)) {C : Set G} (hC : IsCompact C) : ((fun x : G => (x : G ⧸ S)) '' C).Finite := by
  haveI : DiscreteTopology (G ⧸ S) := QuotientGroup.discreteTopology hS
  exact (hC.image (continuous_coinduced_rng : Continuous fun x : G => (x : G ⧸ S))).finite_of_discrete

theorem hint_eq_integral : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    (μ : @MeasureTheory.Measure V (borel V)), @MeasureTheory.Measure.IsAddHaarMeasure V _ _ (borel V) μ →
    ∀ (Λ : AddSubgroup V), IsOpen (Λ : Set V) → IsCompact (Λ : Set V) → ∀ u : V → ℂ,
    (∃ U : AddSubgroup V, IsOpen (U : Set V) ∧ ∀ x, ∀ y ∈ U, u (x + y) = u x) → HasCompactSupport u →
    GlobalTheory.BCT.hint (AddSubgroup.toSubgroup Λ) (fun X : Multiplicative V => u (Multiplicative.toAdd X)) =
      ((μ (Λ : Set V)).toReal : ℂ)⁻¹ * ∫ x, u x ∂μ := by
  intro V _ _ _ μ hμ Λ hΛo hΛc u ⟨U, hUo, hU⟩ hsupp
  letI : MeasurableSpace V := borel V
  haveI : BorelSpace V := ⟨rfl⟩
  haveI := hμ
  let G := Multiplicative V
  letI : MeasurableSpace G := borel V
  haveI : BorelSpace G := ⟨rfl⟩
  let ν : Measure G := μ
  haveI : ν.IsMulLeftInvariant := ⟨fun g => Measure.IsAddLeftInvariant.map_add_left_eq_self (μ := μ) (Multiplicative.toAdd g)⟩
  let u' : G → ℂ := fun X => u (Multiplicative.toAdd X)
  let K : Subgroup G := AddSubgroup.toSubgroup Λ
  let S : Subgroup G := rStab u' ⊓ K
  have hSK : S ≤ K := inf_le_right
  have hSo : IsOpen (S : Set G) := by
    refine Subgroup.isOpen_mono (H₁ := AddSubgroup.toSubgroup (U ⊓ Λ)) ?_ ?_
    · intro x hx
      refine ⟨fun y => hU _ _ hx.1, hx.2⟩
    · exact hUo.inter hΛo
  have hKc : IsCompact (K : Set G) := hΛc
  obtain ⟨hvol, hidx⟩ := vol_mul_relIndex ν K S hSK hKc hSo
  have hKpos : 0 < μ (Λ : Set V) := hΛo.measure_pos μ ⟨0, Λ.zero_mem⟩
  have hKfin : μ (Λ : Set V) < ⊤ := hΛc.measure_lt_top
  have hSfin : ν (S : Set G) ≠ ⊤ := ne_top_of_le_ne_top hKfin.ne (measure_mono hSK)
  have hfinC := finite_cosets S hSo (C := tsupport u') hsupp
  have hF : ∀ q : G ⧸ S, q ∉ hfinC.toFinset → u' q.out = 0 := by
    intro q hq
    by_contra h
    apply hq
    rw [Set.Finite.mem_toFinset]
    exact ⟨q.out, subset_tsupport _ h, QuotientGroup.out_eq' q⟩
  have hint_eq := integral_eq_sum_cosets ν S hSo hSfin u' (fun x s hs => hs.1 x) hfinC.toFinset hF
  have hsum : ∑ᶠ q : G ⧸ S, u' q.out = ∑ q ∈ hfinC.toFinset, u' q.out := by
    refine finsum_eq_sum_of_support_subset _ fun q hq => ?_
    by_contra h
    exact hq (hF q h)
  have hKr : (μ (Λ : Set V)).toReal = ν.real (S : Set G) * (S.relIndex K : ℝ) := hvol.symm
  have hKne : (μ (Λ : Set V)).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hKpos.ne', hKfin.ne⟩
  have hSne : ν.real (S : Set G) ≠ 0 := by
    intro h0
    rw [hKr, h0, zero_mul] at hKne
    exact hKne rfl
  change (((S.relIndex K : ℕ) : ℂ))⁻¹ * ∑ᶠ q : G ⧸ S, u' q.out = _ * ∫ x : G, u' x ∂ν
  rw [hint_eq, hsum, hKr]
  have hidx' : ((S.relIndex K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hidx
  have hSne' : ((ν.real (S : Set G) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hSne
  push_cast
  field_simp

end GlobalTheory.HaarSum
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT

theorem levOp_id_mem_inf_fixed {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (K K' : Subgroup G) (F : G → ℂ) (hF : ∀ k ∈ K', ∀ x, F (k * x) = F x ∧ F (x * k) = F x)
    (M : Submodule ℂ V) (hM : ∀ g, ∀ v ∈ M, ρ g v ∈ M) (v : V) (hv : v ∈ M ⊓ fixed ρ K') :
    levOp ρ K K' F LinearMap.id v ∈ M ⊓ fixed ρ K' := by
  obtain ⟨hvM, hvK⟩ := Submodule.mem_inf.1 hv
  have hfix : ∀ k ∈ K', ρ k v = v := fun k hk => by simpa using hvK ⟨k, hk⟩
  set φ : G ⧸ K' → V →ₗ[ℂ] V := fun q => F q.out • (ρ q.out ∘ₗ LinearMap.id) with hφ
  unfold levOp
  rw [LinearMap.smul_apply]
  refine Submodule.smul_mem _ _ ?_
  by_cases hs : (Function.support φ).Finite
  · have hs' : (Function.support fun q => φ q v).Finite :=
      hs.subset (fun q hq h => hq (by simp [h]))
    have happ : (∑ᶠ q, φ q) v = ∑ᶠ q, φ q v := map_finsum (LinearMap.applyₗ v) hs
    rw [happ]
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · rw [finsum_eq_sum _ hs']
      exact Submodule.sum_mem _ fun q _ => M.smul_mem _ (hM _ _ hvM)
    · intro k
      simp only [MonoidHom.one_apply, Units.val_one, one_smul]
      rw [map_finsum (ρ (k : G)) hs']
      have key : ∀ q : G ⧸ K', ρ (k : G) (φ q v) = φ ((k : G) • q) v := by
        intro q
        have hq : ((((k : G) • q).out : G) : G ⧸ K') = ((k : G) * q.out : G) := by
          rw [QuotientGroup.out_eq']
          conv_lhs => rw [← QuotientGroup.out_eq' q]
          rfl
        have hk2 : ((k : G) * q.out)⁻¹ * ((k : G) • q).out ∈ K' := QuotientGroup.eq.1 hq.symm
        obtain ⟨c, hc, hg'⟩ : ∃ c ∈ K', ((k : G) • q).out = (k : G) * q.out * c := ⟨_, hk2, by group⟩
        simp only [hφ, LinearMap.smul_apply, LinearMap.comp_id, map_smul]
        rw [hg', (hF _ hc _).2, (hF _ k.2 _).1, map_mul, Module.End.mul_apply, hfix _ hc, map_mul,
          Module.End.mul_apply]
      rw [finsum_congr key]
      exact finsum_comp_equiv (MulAction.toPerm (k : G)) (f := fun q => φ q v)
  · rw [finsum_of_infinite_support hs]
    simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem toSub_mul_left_eq {w : Pl E} {U : Subgroup (UL n w)} (g : UL n w → ℂ) (hg : ∀ k ∈ U, ∀ x, g (k * x) = g x)
    (a : UL n w) (ha : a ∈ U) (y : GLw n w) : g (toSub (UL n w) (a.1 * y)) = g (toSub (UL n w) y) := by
  unfold toSub
  by_cases hy : y ∈ UL n w
  · rw [dite_eq_left (mul_mem a.2 hy), dite_eq_left hy, ← hg a ha ⟨y, hy⟩]
    rfl
  · have : a.1 * y ∉ UL n w := fun h => hy (by simpa using mul_mem (inv_mem a.2) h)
    rw [dite_eq_right this, dite_eq_right hy]

theorem toSub_mul_right_eq {w : Pl E} {U : Subgroup (UL n w)} (g : UL n w → ℂ) (hg : ∀ k ∈ U, ∀ x, g (x * k) = g x)
    (a : UL n w) (ha : a ∈ U) (y : GLw n w) : g (toSub (UL n w) (y * a.1)) = g (toSub (UL n w) y) := by
  unfold toSub
  by_cases hy : y ∈ UL n w
  · rw [dite_eq_left (mul_mem hy a.2), dite_eq_left hy, ← hg a ha ⟨y, hy⟩]
    rfl
  · have : y * a.1 ∉ UL n w := fun h => hy (by simpa using mul_mem h (inv_mem a.2))
    rw [dite_eq_right this, dite_eq_right hy]

theorem mem_globLev_iff (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (k : finU (E := E) (n := n)) :
    k ∈ globLev S K' ↔ ∀ w ∈ S, ∃ a ∈ K' w, (a : GLw n w) = cLoc w k.1 := by
  simp [globLev, Subgroup.mem_iInf]

theorem globFn_inv (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ)
    (hf : ∀ w, ∀ k ∈ K' w, ∀ x, f w (k * x) = f w x ∧ f w (x * k) = f w x) :
    ∀ k ∈ globLev S K', ∀ x, globFn S f (k * x) = globFn S f x ∧ globFn S f (x * k) = globFn S f x := by
  intro k hk x
  rw [mem_globLev_iff] at hk
  constructor
  · unfold globFn
    refine finprod_mem_congr rfl fun w hw => ?_
    obtain ⟨a, ha, hae⟩ := hk w hw
    rw [Subgroup.coe_mul, map_mul, ← hae]
    exact toSub_mul_left_eq (f w) (fun k hk x => (hf w k hk x).1) a ha _
  · unfold globFn
    refine finprod_mem_congr rfl fun w hw => ?_
    obtain ⟨a, ha, hae⟩ := hk w hw
    rw [Subgroup.coe_mul, map_mul, ← hae]
    exact toSub_mul_right_eq (f w) (fun k hk x => (hf w k hk x).2) a ha _

end GlobalTheory.BCT


open GlobalTheory.BCT in
theorem GlobalTheory.BCT.hop_mem_inf_fixed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ v ∈ π ⊓ fixed (RF E n) (globLev S K'), hop S K' f v ∈ π ⊓ fixed (RF E n) (globLev S K') := by
  intro E _ _ _ n S _ K' _ f hf π hπ v hv
  exact levOp_id_mem_inf_fixed (RF E n) _ _ _ (globFn_inv S K' f fun w => (hf.1 w).2) π
    (fun g v hv => hπ.stable _ v hv) v hv
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.HintLevel

theorem finsum_prod_fst {A T : Type} [Finite T] [Nonempty T] (f : A → ℂ) :
    ∑ᶠ x : A × T, f x.1 = (Nat.card T : ℂ) * ∑ᶠ a : A, f a := by
  by_cases hf : (Function.support f).Finite
  · have hg : (Function.support fun x : A × T => f x.1).Finite := by
      refine (hf.prod (Set.finite_univ (α := T))).subset ?_
      intro x hx
      exact ⟨hx, Set.mem_univ _⟩
    rw [finsum_curry _ hg, mul_finsum]
    refine finsum_congr fun a => ?_
    haveI := Fintype.ofFinite T
    rw [finsum_eq_sum_of_fintype]
    show ∑ _i : T, f a = _
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  · have hg : ¬ (Function.support fun x : A × T => f x.1).Finite := by
      intro hg
      apply hf
      refine (hg.image Prod.fst).subset ?_
      intro a ha
      exact ⟨(a, Classical.arbitrary T), ha, rfl⟩
    rw [finsum_of_infinite_support hg, finsum_of_infinite_support hf, mul_zero]

theorem sum_level (H : Type) [Group H] (S L : Subgroup H) (u : H → ℂ) (hLS : L ≤ S) (hS : S ≤ rStab u)
    (hfin : L.relIndex S ≠ 0) :
    ∑ᶠ q : H ⧸ L, u q.out = ((L.relIndex S : ℕ) : ℂ) * ∑ᶠ p : H ⧸ S, u p.out := by
  have hinv : ∀ g : H, u ((QuotientGroup.mk g : H ⧸ S).out) = u g := by
    intro g
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul S g
    rw [hk]
    exact hS k.2 g
  have hfst : ∀ q : H ⧸ L, u q.out = u ((Subgroup.quotientEquivProdOfLE hLS q).1.out) := by
    intro q
    have : (Subgroup.quotientEquivProdOfLE hLS q).1 = (QuotientGroup.mk q.out : H ⧸ S) := by
      simp only [Subgroup.quotientEquivProdOfLE, Subgroup.quotientEquivProdOfLE']
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    rw [this, hinv]
  haveI : Finite (S ⧸ L.subgroupOf S) := Subgroup.index_ne_zero_iff_finite.1 hfin
  rw [finsum_congr hfst, finsum_comp_equiv (Subgroup.quotientEquivProdOfLE hLS)
    (f := fun x : (H ⧸ S) × (S ⧸ L.subgroupOf S) => u x.1.out)]
  exact finsum_prod_fst (fun p : H ⧸ S => u p.out)

theorem hint_level : ∀ (H : Type) [Group H] (K L : Subgroup H) (u : H → ℂ), L ≤ K → L ≤ rStab u →
    L.relIndex K ≠ 0 → hint K u = ((L.relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ q : H ⧸ L, u q.out := by
  intro H _ K L u hLK hLu hne
  have hLS : L ≤ rStab u ⊓ K := le_inf hLu hLK
  have hmul := Subgroup.relIndex_mul_relIndex L (rStab u ⊓ K) K hLS inf_le_right
  have h1 : L.relIndex (rStab u ⊓ K) ≠ 0 := by
    intro h0; apply hne; rw [← hmul, h0, zero_mul]
  have h2 : (rStab u ⊓ K).relIndex K ≠ 0 := by
    intro h0; apply hne; rw [← hmul, h0, mul_zero]
  rw [sum_level H (rStab u ⊓ K) L u hLS inf_le_left h1, hint, ← hmul]
  push_cast
  have h1' : ((L.relIndex (rStab u ⊓ K) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 h1
  field_simp

end GlobalTheory.BCT.HintLevel
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.FinPtLoc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def fstA (E : Type) [Field E] [NumberField E] : Ad E →+* InfiniteAdeleRing E := RingHom.fst _ _

theorem fst_entry (γ : GL (Fin n) E) (i j : Fin n) :
    fstA E ((finGL E n (ratF E n γ)).val i j) = (1 : Matrix (Fin n) (Fin n) (InfiniteAdeleRing E)) i j := by
  change ((1 : Matrix (Fin n) (Fin n) (InfiniteAdeleRing E × Af E)) i j -
      ((0 : InfiniteAdeleRing E), (1 : Matrix (Fin n) (Fin n) (Af E)) i j) +
      ((0 : InfiniteAdeleRing E), algebraMap E (Af E) (γ.val i j))).1 = _
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem snd_entry (γ : GL (Fin n) E) (i j : Fin n) :
    pFin E ((finGL E n (ratF E n γ)).val i j) = algebraMap E (Af E) (γ.val i j) := by
  change ((1 : Matrix (Fin n) (Fin n) (InfiniteAdeleRing E × Af E)) i j -
      ((0 : InfiniteAdeleRing E), (1 : Matrix (Fin n) (Fin n) (Af E)) i j) +
      ((0 : InfiniteAdeleRing E), algebraMap E (Af E) (γ.val i j))).2 = _
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem map_cT {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (σ : A →+* A) (τ : B →+* B)
    (h : ∀ x, f (σ x) = τ (f x)) (M : Matrix (Fin n) (Fin n) A) : (cT σ M).map f = cT τ (M.map f) := by
  ext i j; simp [cT, h]

theorem ext_ad (M N : Matrix (Fin n) (Fin n) (Ad E)) (h1 : M.map (fstA E) = N.map (fstA E))
    (h2 : M.map (pFin E) = N.map (pFin E)) : M = N := by
  ext i j
  exact Prod.ext (congrFun (congrFun h1 i) j) (congrFun (congrFun h2 i) j)

theorem mem_UA (γ : UE E n) : finGL E n (ratF E n γ.1) ∈ UA E n := by
  have hγ : cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ.1.val * 1 * γ.1.val = 1 := γ.2
  show cT (conjAd E) (finGL E n (ratF E n γ.1)).val * 1 * (finGL E n (ratF E n γ.1)).val = 1
  have hf : (finGL E n (ratF E n γ.1)).val.map (fstA E) = 1 := by
    ext i j; rw [Matrix.map_apply, fst_entry]
  have hs : (finGL E n (ratF E n γ.1)).val.map (pFin E) = γ.1.val.map (algebraMap E (Af E)) := by
    ext i j; rw [Matrix.map_apply, snd_entry]; rfl
  apply ext_ad
  · rw [Matrix.map_mul, Matrix.map_mul, map_cT (fstA E) (conjAd E) ((infEq E).toRingHom.comp ((starRingEnd (Cinf E)).comp (infEq E).symm.toRingHom)) (fun x => rfl), hf, Matrix.map_one _ (map_zero _) (map_one _)]
    ext i j; simp [cT, Matrix.one_apply]
  · rw [Matrix.map_mul, Matrix.map_mul, map_cT (pFin E) (conjAd E) (conjFin (IsCMField.complexConj E).toRingEquiv) (fun x => rfl), hs,
      Matrix.map_one _ (map_zero _) (map_one _)]
    have : cT (conjFin (IsCMField.complexConj E).toRingEquiv) (γ.1.val.map (algebraMap E (Af E))) =
        (cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ.1.val).map (algebraMap E (Af E)) := by
      ext i j; simp [cT, conjFin_algebraMap]
    rw [this, ← Matrix.map_one (algebraMap E (Af E)) (map_zero _) (map_one _), ← Matrix.map_mul, ← Matrix.map_mul, hγ]

theorem toSub_of_mem {G : Type} [Group G] (H : Subgroup G) (g : G) (h : g ∈ H) : toSub H g = ⟨g, h⟩ :=
  dif_pos h

theorem mem_finU (γ : UE E n) : (⟨_, mem_UA γ⟩ : UA E n) ∈ finU (E := E) (n := n) := by
  show cInf (⟨_, mem_UA γ⟩ : UA E n) = 1
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  change (infEq E).symm (fstA E ((finGL E n (ratF E n γ.1)).val i j)) = (1 : Matrix (Fin n) (Fin n) (Cinf E)) i j
  rw [fst_entry]
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem finPt_eq (γ : UE E n) : ((finPt γ : finU (E := E) (n := n)) : UA E n) = ⟨_, mem_UA γ⟩ := by
  have h1 : toSub (UA E n) (finGL E n (ratF E n γ.1)) = ⟨_, mem_UA γ⟩ := toSub_of_mem _ _ (mem_UA γ)
  unfold finPt
  rw [h1, toSub_of_mem _ _ (mem_finU γ)]

end GlobalTheory.BCT.FinPtLoc

theorem GlobalTheory.BCT.locPt_finPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ (γ : UE E n) (w : Pl E),
    toSub (UL n w) (cLoc w ((finPt γ : finU (E := E) (n := n)) : UA E n)) = locPt w γ := by
  intro E _ _ _ _ n γ w
  rw [FinPtLoc.finPt_eq]
  unfold locPt
  congr 1
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  change pLoc E w (pFin E ((finGL E n (ratF E n γ.1)).val i j)) = algebraMap E _ (γ.1.val i j)
  rw [FinPtLoc.snd_entry]
  rfl
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.SuppFin

theorem factor_ne_zero_of_globFn_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ), IsTest (KL n) K' f → ∀ y : finU (E := E) (n := n), (∀ᶠ w in cofinite, cLoc w y.1 ∈ GlobalTheory.LFun.KGL w (n := n)) → globFn S f y ≠ 0 → ∀ w ∈ S, f w (toSub _ (cLoc w y.1)) ≠ 0 := by
  intro E _ _ _ n S K' f hT y hy hne w hw h0
  set F : Pl E → ℂ := fun w => f w (toSub _ (cLoc w y.1)) with hF
  have hev : ∀ᶠ v in cofinite, F v = 1 := by
    filter_upwards [hT.2, hy] with v hv hyv
    simp only [hF, hv]
    have hmem : toSub (UL n v) (cLoc v y.1) ∈ KL n v := by
      unfold toSub
      split_ifs with h
      · exact (Subgroup.mem_subgroupOf).2 hyv
      · exact Subgroup.one_mem _
    exact Set.indicator_of_mem (show toSub (UL n v) (cLoc v y.1) ∈ ((KL n v : Subgroup (UL n v)) : Set (UL n v)) from hmem) _
  have hfin : (Function.mulSupport F).Finite := by
    have := Filter.eventually_cofinite.1 hev
    exact this
  have hfin' : (S ∩ Function.mulSupport F).Finite := hfin.subset Set.inter_subset_right
  apply hne
  show ∏ᶠ v ∈ S, F v = 0
  rw [← finprod_mem_inter_mulSupport, finprod_mem_eq_finite_toFinset_prod F hfin']
  apply Finset.prod_eq_zero (i := w)
  · rw [Set.Finite.mem_toFinset]
    refine ⟨hw, ?_⟩
    rw [Function.mem_mulSupport]
    change f w (toSub _ (cLoc w y.1)) ≠ 1
    rw [h0]; exact zero_ne_one
  · exact h0

end GlobalTheory.BCT.SuppFin
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

theorem _root_.GlobalTheory.T.exists_open_covering_charts_generically_finite_field : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ), IsProjOver p → IsProjOver q → SmoothOfRelativeDimension D p → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∃ U : X.Opens, genericPoint X ∈ U ∧ (∀ y ∈ ptsIn p σ U, (PtsOver.map π hπ (spMap σ) ⁻¹' {y}).encard = (π.residueDegree (genericPoint Y) : ℕ∞)) ∧ (∀ y ∈ ptsIn p σ U, ∃ c : AlgChart p σ D, y ∈ c.e.source) ∧ (∀ z : CxPts q σ, PtsOver.map π hπ (spMap σ) z ∈ ptsIn p σ U → ∀ c : AlgChart p σ D, PtsOver.map π hπ (spMap σ) z ∈ c.e.source → ∃ c' : AlgChart q σ D, z ∈ c'.e.source ∧ ∀ w ∈ c'.e.source, PtsOver.map π hπ (spMap σ) w ∈ c.e.source ∧ c'.e w = c.e (PtsOver.map π hπ (spMap σ) w)) := by
  first | exact @GlobalTheory.CoverDegField.exists_open_covering_charts | exact GlobalTheory.CoverDegField.exists_open_covering_charts | (intros; apply GlobalTheory.CoverDegField.exists_open_covering_charts <;> assumption)
end

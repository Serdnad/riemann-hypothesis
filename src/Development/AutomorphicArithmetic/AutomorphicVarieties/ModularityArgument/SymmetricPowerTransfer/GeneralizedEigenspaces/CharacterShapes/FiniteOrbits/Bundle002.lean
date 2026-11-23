module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So

section SlopeTestRemainingChoices

variable {G : Type} [Group G] {S U : Subgroup G}

private theorem dc_up {x g : S} (h : g ∈ DC (U.subgroupOf S) x) : (g : G) ∈ DC U (x : G) := by
  obtain ⟨u, hu, u', hu', rfl⟩ := h
  exact ⟨u, Subgroup.mem_subgroupOf.mp hu, u', Subgroup.mem_subgroupOf.mp hu', by simp⟩

private theorem dc_left {b w z : G} (hw : w ∈ U) (hz : z ∈ DC U b) : w * z ∈ DC U b := by
  obtain ⟨u, hu, u', hu', rfl⟩ := hz
  exact ⟨w * u, U.mul_mem hw hu, u', hu', by simp only [mul_assoc]⟩

private theorem dc_right {b w z : G} (hw : w ∈ U) (hz : z ∈ DC U b) : z * w ∈ DC U b := by
  obtain ⟨u, hu, u', hu', rfl⟩ := hz
  exact ⟨u, hu, u' * w, U.mul_mem hu' hw, by simp only [mul_assoc]⟩

private theorem dc_rep {x : S} (hx : ∀ u ∈ U, ∃ c ∈ U, c * (x : G) = x * c ∧ u * c⁻¹ ∈ S)
    {y : G} (hy : y ∈ DC U (x : G)) :
    ∃ t : S, t ∈ U.subgroupOf S ∧ ((t * x : S) : G)⁻¹ * y ∈ U := by
  obtain ⟨u, hu, u', hu', rfl⟩ := hy
  obtain ⟨c, hc, hcx, hcS⟩ := hx u hu
  refine ⟨⟨u * c⁻¹, hcS⟩, Subgroup.mem_subgroupOf.mpr (U.mul_mem hu (U.inv_mem hc)), ?_⟩
  have e : ((⟨u * c⁻¹, hcS⟩ * x : S) : G)⁻¹ * (u * (x : G) * u') = c * u' := by
    simp only [Subgroup.coe_mul, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left]
    rw [← mul_assoc c, hcx]
    group
  rw [e]
  exact U.mul_mem hc hu'

private theorem dc_down {x g : S} (hx : ∀ u ∈ U, ∃ c ∈ U, c * (x : G) = x * c ∧ u * c⁻¹ ∈ S)
    (hg : (g : G) ∈ DC U (x : G)) : g ∈ DC (U.subgroupOf S) x := by
  obtain ⟨t, ht, hw⟩ := dc_rep hx hg
  refine ⟨t, ht, (t * x)⁻¹ * g, Subgroup.mem_subgroupOf.2 (by simpa using hw), ?_⟩
  group

private theorem mk_eq_of {r r' : S} (h : (r : G)⁻¹ * r' ∈ U) :
    (r : S ⧸ U.subgroupOf S) = r' := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simpa using h

private theorem finOrb_sub {a : S} (h : AlgebraTools.FinOrb U U (a : G)) :
    AlgebraTools.FinOrb (U.subgroupOf S) (U.subgroupOf S) a := by
  have inj : Function.Injective
      (fun q : S ⧸ U.subgroupOf S => (((Quotient.out q : S) : G) : G ⧸ U)) := by
    intro q1 q2 e
    dsimp only at e
    have e' := QuotientGroup.eq.mp e
    calc q1 = ((Quotient.out q1 : S) : S ⧸ U.subgroupOf S) := (QuotientGroup.out_eq' q1).symm
      _ = ((Quotient.out q2 : S) : S ⧸ U.subgroupOf S) := mk_eq_of e'
      _ = q2 := QuotientGroup.out_eq' q2
  apply Set.Finite.of_finite_image _ inj.injOn
  apply h.subset
  rintro _ ⟨q, ⟨k, rfl⟩, rfl⟩
  obtain ⟨t, ht⟩ := QuotientGroup.mk_out_eq_mul (U.subgroupOf S) (k.1 * a)
  refine ⟨⟨((k.1 : S) : G), k.2⟩, ?_⟩
  have hq : (k • (a : S ⧸ U.subgroupOf S)) = ((k.1 * a : S) : S ⧸ U.subgroupOf S) := rfl
  dsimp only
  rw [hq, ht]
  show ((((k.1 : S) : G) * (a : G) : G) : G ⧸ U) = _
  rw [QuotientGroup.eq]
  convert Subgroup.mem_subgroupOf.mp t.2 using 1
  simp only [Subgroup.coe_mul]
  group

private theorem uf_sub {a b : S}
    (hab : ∀ u ∈ U, ∃ c ∈ U, c * (a : G) = a * c ∧ c * (b : G) = b * c ∧ u * c⁻¹ ∈ S ∧ c⁻¹ * u ∈ S)
    (hUF : UF U (a : G) (b : G)) : UF (U.subgroupOf S) a b := by
  have ha : ∀ u ∈ U, ∃ c ∈ U, c * (a : G) = a * c ∧ u * c⁻¹ ∈ S := fun u hu => by
    obtain ⟨c, hc, h1, -, h3, -⟩ := hab u hu
    exact ⟨c, hc, h1, h3⟩
  have hb : ∀ u ∈ U, ∃ c ∈ U, c * (b : G) = b * c ∧ u * c⁻¹ ∈ S := fun u hu => by
    obtain ⟨c, hc, -, h2, h3, -⟩ := hab u hu
    exact ⟨c, hc, h2, h3⟩
  have hab' : ∀ u ∈ U, ∃ c ∈ U, c * ((a * b : S) : G) = ((a * b : S) : G) * c ∧ u * c⁻¹ ∈ S :=
    fun u hu => by
      obtain ⟨c, hc, h1, h2, h3, -⟩ := hab u hu
      refine ⟨c, hc, ?_, h3⟩
      simp only [Subgroup.coe_mul]
      rw [← mul_assoc, h1, mul_assoc, h2, mul_assoc]
  intro g
  refine ⟨fun hg => ?_, fun y hy hyg => ?_⟩
  · have hg' : (g : G) ∈ DC U ((a : G) * b) := by
      rw [← Subgroup.coe_mul]
      exact dc_up hg
    obtain ⟨Y, ⟨hY1, hY2⟩, hYu⟩ := (hUF g).1 hg'
    obtain ⟨t, ht, htY⟩ := dc_rep ha hY1
    have hrg : (t * a)⁻¹ * g ∈ DC (U.subgroupOf S) b := by
      apply dc_down hb
      have e : (((t * a)⁻¹ * g : S) : G)
          = (((t * a : S) : G)⁻¹ * Quotient.out Y) * ((Quotient.out Y)⁻¹ * g) := by
        push_cast
        group
      rw [e]
      exact dc_left htY hY2
    have hrY : ((((t * a : S) : G)) : G ⧸ U) = Y := by
      rw [← QuotientGroup.out_eq' Y]
      exact QuotientGroup.eq.mpr htY
    have key : ∀ s : G, s ∈ DC U a → s⁻¹ * g ∈ DC U b → (s : G ⧸ U) = Y := by
      intro s hs1 hs2
      obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul U s
      refine hYu _ ⟨?_, ?_⟩
      · rw [hk]
        exact dc_right k.2 hs1
      · rw [hk, mul_inv_rev, mul_assoc]
        exact dc_left (inv_mem k.2) hs2
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (U.subgroupOf S) (t * a)
    refine ⟨((t * a : S) : S ⧸ U.subgroupOf S), ⟨?_, ?_⟩, ?_⟩
    · rw [hk]
      exact dc_right k.2 ⟨t, ht, 1, one_mem _, (mul_one _).symm⟩
    · rw [hk, mul_inv_rev, mul_assoc]
      exact dc_left (inv_mem k.2) hrg
    · rintro z ⟨hz1, hz2⟩
      have hz : (((Quotient.out z : S) : G) : G ⧸ U) = Y :=
        key _ (dc_up hz1) (by simpa using dc_up hz2)
      calc z = ((Quotient.out z : S) : S ⧸ U.subgroupOf S) := (QuotientGroup.out_eq' z).symm
        _ = _ := mk_eq_of (QuotientGroup.eq.mp (hz.trans hrY.symm))
  · have h1 := (hUF g).2 y (dc_up hy) (by simpa using dc_up hyg)
    apply dc_down hab'
    rw [Subgroup.coe_mul]
    exact h1

private theorem reps_sub {a : S} (ha : ∀ u ∈ U, ∃ c ∈ U, c * (a : G) = a * c ∧ u * c⁻¹ ∈ S)
    (hfin : AlgebraTools.FinOrb (U.subgroupOf S) (U.subgroupOf S) a) :
    ∃ R : Finset S, (∀ y ∈ R, y ∈ DC (U.subgroupOf S) a) ∧
      (∀ y ∈ DC (U.subgroupOf S) a, ∃! r, r ∈ R ∧ r⁻¹ * y ∈ U.subgroupOf S) ∧
      ∀ y ∈ DC U (a : G), ∃! r : S, r ∈ R ∧ (r : G)⁻¹ * y ∈ U := by
  classical
  have orb : ∀ k : S, k ∈ U.subgroupOf S →
      ((k * a : S) : S ⧸ U.subgroupOf S) ∈
        MulAction.orbit (U.subgroupOf S) (a : S ⧸ U.subgroupOf S) :=
    fun k hk => ⟨⟨k, hk⟩, rfl⟩
  refine ⟨hfin.toFinset.image (fun q => Quotient.out q), ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨k, rfl⟩ := hfin.mem_toFinset.mp hq
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (U.subgroupOf S) ((k : S) * a)
    have hq' : k • (a : S ⧸ U.subgroupOf S) = (((k : S) * a : S) : S ⧸ U.subgroupOf S) := rfl
    dsimp only
    rw [hq', hh]
    exact dc_right h.2 ⟨k, k.2, 1, one_mem _, (mul_one _).symm⟩
  · intro y hy
    obtain ⟨u, hu, u', hu', rfl⟩ := hy
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (U.subgroupOf S) (u * a)
    refine ⟨Quotient.out ((u * a : S) : S ⧸ U.subgroupOf S), ⟨?_, ?_⟩, ?_⟩
    · exact Finset.mem_image.mpr ⟨_, hfin.mem_toFinset.mpr (orb u hu), rfl⟩
    · rw [hh]
      have e : (u * a * (h : S))⁻¹ * (u * a * u') = (h : S)⁻¹ * u' := by group
      rw [e]
      exact mul_mem (inv_mem h.2) hu'
    · rintro r ⟨hr, hry⟩
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hr
      have e : q = ((u * a : S) : S ⧸ U.subgroupOf S) :=
        calc q = ((Quotient.out q : S) : S ⧸ U.subgroupOf S) := (QuotientGroup.out_eq' q).symm
          _ = ((u * a * u' : S) : S ⧸ U.subgroupOf S) := QuotientGroup.eq.mpr hry
          _ = _ := QuotientGroup.eq.mpr (by
            rw [show (u * a * u')⁻¹ * (u * a) = u'⁻¹ by group]
            exact inv_mem hu')
      rw [e]
  · intro y hy
    obtain ⟨t, ht, hty⟩ := dc_rep ha hy
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (U.subgroupOf S) (t * a)
    refine ⟨Quotient.out ((t * a : S) : S ⧸ U.subgroupOf S), ⟨?_, ?_⟩, ?_⟩
    · exact Finset.mem_image.mpr ⟨_, hfin.mem_toFinset.mpr (orb t ht), rfl⟩
    · rw [hh]
      have e : ((t * a * (h : S) : S) : G)⁻¹ * y
          = ((h : S) : G)⁻¹ * (((t * a : S) : G)⁻¹ * y) := by
        push_cast
        group
      rw [e]
      exact mul_mem (inv_mem (Subgroup.mem_subgroupOf.mp h.2)) hty
    · rintro r ⟨hr, hry⟩
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hr
      have e : q = ((t * a : S) : S ⧸ U.subgroupOf S) :=
        calc q = ((Quotient.out q : S) : S ⧸ U.subgroupOf S) := (QuotientGroup.out_eq' q).symm
          _ = _ := mk_eq_of (by
            have m := U.mul_mem hry (U.inv_mem hty)
            convert m using 1
            group)
      rw [e]

end SlopeTestRemainingChoices

end UpperTheory.V.Z.Sym.So

theorem UpperTheory.V.Z.Sym.So.dcSub :
    UpperTheory.V.Z.Sym.So.DcSub := by
  intro G V _ _ _ S U a hfin ha _
  have ha' : ∀ u ∈ U, ∃ c ∈ U, c * (a : G) = a * c ∧ u * c⁻¹ ∈ S := fun u hu => by
    obtain ⟨c, hc, h1, h2, _⟩ := ha u hu
    exact ⟨c, hc, h1, h2⟩
  have hfin' := finOrb_sub hfin
  exact ⟨hfin', fun g => ⟨dc_up, dc_down ha'⟩, fun b hb hUF => uf_sub hb hUF, reps_sub ha' hfin'⟩

end
end

section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem out_mul {G : Type} [Group G] (U : Subgroup G) (g : G) :
    ∃ i ∈ U, ((g : G ⧸ U)).out = g * i := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul U g
  exact ⟨h, h.2, hh⟩

private theorem orb_iff {G : Type} [Group G] (U : Subgroup G) (a : G) (p : G ⧸ U) :
    p ∈ MulAction.orbit U (a : G ⧸ U) ↔ p.out ∈ DC U a := by
  have key : ∀ u : U, u • (a : G ⧸ U) = (((u : G) * a : G) : G ⧸ U) := fun u => rfl
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨i, hi, h⟩ := out_mul U ((u : G) * a)
    refine ⟨u, u.2, i, hi, ?_⟩
    dsimp only
    rw [key, h]
  · rintro ⟨u, hu, u', hu', h⟩
    refine ⟨⟨u, hu⟩, ?_⟩
    dsimp only
    rw [key, ← QuotientGroup.out_eq' p, h]
    refine QuotientGroup.eq.mpr ?_
    rw [inv_mul_cancel_left]
    exact hu'

private theorem dcF_sum {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (U : Subgroup G) (a : G)
    [Fintype (MulAction.orbit U (a : G ⧸ U))] (φ : G → V) (g : G) :
    dcF U a φ g = ∑ q : MulAction.orbit U (a : G ⧸ U), φ (g * (q : G ⧸ U).out) := by
  simp only [dcF, dc, finsum_eq_sum_of_fintype, LinearMap.sum_apply, Finset.sum_apply]
  rfl

private theorem mul_mem_dc_of_mem_subgroup {G : Type} [Group G] (U : Subgroup G) (c x i : G) (hx : x ∈ DC U c) (hi : i ∈ U) :
    x * i ∈ DC U c := by
  obtain ⟨u, hu, u', hu', rfl⟩ := hx
  exact ⟨u, hu, u' * i, U.mul_mem hu' hi, mul_assoc _ _ _⟩

private theorem quotient_out_mem_dc_iff {G : Type} [Group G] (U : Subgroup G) (c x : G) :
    ((x : G ⧸ U)).out ∈ DC U c ↔ x ∈ DC U c := by
  obtain ⟨i, hi, h⟩ := out_mul U x
  rw [h]
  constructor
  · intro hx
    simpa using mul_mem_dc_of_mem_subgroup U c _ i⁻¹ hx (U.inv_mem hi)
  · intro hx
    exact mul_mem_dc_of_mem_subgroup U c x i hx hi

theorem UpperTheory.V.Z.Sym.So.uFMul :
    UpperTheory.V.Z.Sym.So.UFMul := by
  intro G V _ _ _ U a b ha hb hab huf φ hφ
  haveI : Fintype (MulAction.orbit U (a : G ⧸ U)) := Set.Finite.fintype ha
  haveI : Fintype (MulAction.orbit U (b : G ⧸ U)) := Set.Finite.fintype hb
  haveI : Fintype (MulAction.orbit U ((a * b : G) : G ⧸ U)) := Set.Finite.fintype hab
  funext g
  rw [dcF_sum U a _ g, dcF_sum U (a * b) φ g]
  simp only [dcF_sum U b φ]
  rw [← Fintype.sum_prod_type']
  have hmem : ∀ x : MulAction.orbit U (a : G ⧸ U) × MulAction.orbit U (b : G ⧸ U),
      (((x.1 : G ⧸ U).out * (x.2 : G ⧸ U).out : G) : G ⧸ U) ∈ MulAction.orbit U ((a * b : G) : G ⧸ U) := by
    intro x
    refine (orb_iff U (a * b) _).mpr ((quotient_out_mem_dc_iff U _ _).mpr ((huf _).2 _ ((orb_iff U a _).mp x.1.2) ?_))
    rw [inv_mul_cancel_left]
    exact (orb_iff U b _).mp x.2.2
  refine Fintype.sum_bijective (fun x => ⟨_, hmem x⟩) ⟨?_, ?_⟩ _ _ ?_
  · rintro ⟨q, r⟩ ⟨q', r'⟩ hx
    have hx' : (((q : G ⧸ U).out * (r : G ⧸ U).out : G) : G ⧸ U) =
        (((q' : G ⧸ U).out * (r' : G ⧸ U).out : G) : G ⧸ U) := congrArg Subtype.val hx
    obtain ⟨i, hi, hs⟩ := out_mul U ((q : G ⧸ U).out * (r : G ⧸ U).out)
    obtain ⟨i', hi', hs'⟩ := out_mul U ((q' : G ⧸ U).out * (r' : G ⧸ U).out)
    have hsab : (q : G ⧸ U).out * (r : G ⧸ U).out * i ∈ DC U (a * b) := by
      have := (orb_iff U (a * b) _).mp (hmem (q, r))
      rwa [hs] at this
    rw [hx'] at hs
    have he : (q : G ⧸ U).out * (r : G ⧸ U).out * i = (q' : G ⧸ U).out * (r' : G ⧸ U).out * i' :=
      hs.symm.trans hs'
    obtain ⟨y, -, huniq⟩ := (huf _).1 hsab
    have h1 : (q : G ⧸ U) = y := huniq _ ⟨(orb_iff U a _).mp q.2, by
      simp only [mul_assoc, inv_mul_cancel_left]
      exact mul_mem_dc_of_mem_subgroup U b _ i ((orb_iff U b _).mp r.2) hi⟩
    have h2 : (q' : G ⧸ U) = y := huniq _ ⟨(orb_iff U a _).mp q'.2, by
      rw [he]
      simp only [mul_assoc, inv_mul_cancel_left]
      exact mul_mem_dc_of_mem_subgroup U b _ i' ((orb_iff U b _).mp r'.2) hi'⟩
    have hq : q = q' := Subtype.ext (h1.trans h2.symm)
    subst hq
    have hr : (r : G ⧸ U).out * i = (r' : G ⧸ U).out * i' := by
      rw [mul_assoc, mul_assoc] at he
      exact mul_left_cancel he
    have hr' : (r : G ⧸ U) = r' := by
      rw [← QuotientGroup.out_eq' (r : G ⧸ U), ← QuotientGroup.out_eq' (r' : G ⧸ U),
        ← QuotientGroup.mk_mul_of_mem (r : G ⧸ U).out hi, hr, QuotientGroup.mk_mul_of_mem _ hi']
    exact Prod.ext rfl (Subtype.ext hr')
  · rintro ⟨s, hs⟩
    have hsd : (s : G ⧸ U).out ∈ DC U (a * b) := (orb_iff U (a * b) s).mp hs
    obtain ⟨y, ⟨hy1, hy2⟩, -⟩ := (huf _).1 hsd
    refine ⟨(⟨y, (orb_iff U a y).mpr hy1⟩,
      ⟨((y.out⁻¹ * s.out : G) : G ⧸ U), (orb_iff U b _).mpr ((quotient_out_mem_dc_iff U _ _).mpr hy2)⟩), ?_⟩
    apply Subtype.ext
    obtain ⟨i, hi, h⟩ := out_mul U (y.out⁻¹ * s.out)
    dsimp only
    rw [h, ← mul_assoc, mul_inv_cancel_left, QuotientGroup.mk_mul_of_mem _ hi, QuotientGroup.out_eq']
  · rintro ⟨q, r⟩
    obtain ⟨i, hi, h⟩ := out_mul U ((q : G ⧸ U).out * (r : G ⧸ U).out)
    dsimp only
    rw [h, ← mul_assoc, ← mul_assoc, hφ i hi]

end
end

section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem finsum_end_apply {α M : Type} [AddCommGroup M] [Module ℂ M] [Finite α]
    (f : α → Module.End ℂ M) (x : M) : (∑ᶠ a, f a) x = ∑ᶠ a, f a x := by
  cases nonempty_fintype α
  simp only [finsum_eq_sum_of_fintype, LinearMap.sum_apply]

theorem UpperTheory.V.Z.Sym.So.dcLocal :
    UpperTheory.V.Z.Sym.So.DcLocal := by
  intro H G V _ _ _ _ j p J U hpj hU hJ d hd

  have hin : ∀ h : H, (h : H ⧸ J) ∈ MulAction.orbit J (d : H ⧸ J) →
      ((j h : G) : G ⧸ U) ∈ MulAction.orbit U ((j d : G) : G ⧸ U) := by
    rintro h ⟨a, ha⟩
    have h1 : (((a : H) * d : H) : H ⧸ J) = (h : H ⧸ J) := ha
    have h2 : ((a : H) * d)⁻¹ * h ∈ J := QuotientGroup.eq.1 h1
    have h3 : (j ((a : H) * d))⁻¹ * j h ∈ U := by
      have := hJ _ h2
      simpa [map_mul] using this
    refine ⟨⟨j a, hJ _ a.2⟩, ?_⟩
    change ((j a * j d : G) : G ⧸ U) = ((j h : G) : G ⧸ U)
    refine QuotientGroup.eq.2 ?_
    simpa [map_mul] using h3

  have hsurj : ∀ y ∈ MulAction.orbit U ((j d : G) : G ⧸ U),
      ∃ h : H, (h : H ⧸ J) ∈ MulAction.orbit J (d : H ⧸ J) ∧ ((j h : G) : G ⧸ U) = y := by
    rintro y ⟨u, rfl⟩
    obtain ⟨hpu, hc⟩ := hU u u.2
    set c : G := (u : G) * (j (p u))⁻¹ with hcdef
    have hcU : c ∈ U := U.mul_mem u.2 (U.inv_mem (hJ _ hpu))
    refine ⟨p u * d, ⟨⟨p u, hpu⟩, rfl⟩, ?_⟩
    change ((j (p u * d) : G) : G ⧸ U) = (((u : G) * j d : G) : G ⧸ U)
    have hfac : (u : G) * j d = j (p u * d) * c := by
      have h1 : (u : G) = c * j (p u) := by simp [hcdef]
      calc (u : G) * j d = c * j (p u * d) := by rw [map_mul, ← mul_assoc, ← h1]
        _ = j (p u * d) * c := hc _
    rw [hfac]
    exact (QuotientGroup.mk_mul_of_mem _ hcU).symm
  have hfin : AlgebraTools.FinOrb U U (j d) := by
    refine (hd.image fun q : H ⧸ J => ((j q.out : G) : G ⧸ U)).subset ?_
    intro y hy
    obtain ⟨h, hh, rfl⟩ := hsurj y hy
    refine ⟨(h : H ⧸ J), hh, ?_⟩
    change ((j (h : H ⧸ J).out : G) : G ⧸ U) = ((j h : G) : G ⧸ U)
    refine QuotientGroup.eq.2 ?_
    have h1 : ((h : H ⧸ J).out)⁻¹ * h ∈ J := QuotientGroup.eq.1 (by simp)
    have := hJ _ h1
    simpa [map_mul] using this
  refine ⟨hfin, fun φ hφ => ?_⟩
  haveI : Finite (MulAction.orbit J (d : H ⧸ J)) := Set.Finite.to_subtype hd
  haveI : Finite (MulAction.orbit U ((j d : G) : G ⧸ U)) := Set.Finite.to_subtype hfin

  let e : MulAction.orbit J (d : H ⧸ J) → MulAction.orbit U ((j d : G) : G ⧸ U) := fun q =>
    ⟨((j (q : H ⧸ J).out : G) : G ⧸ U), hin _ (by simpa using q.2)⟩
  have he : Function.Bijective e := by
    constructor
    · intro q q' hqq
      have h1 : ((j (q : H ⧸ J).out : G) : G ⧸ U) = ((j (q' : H ⧸ J).out : G) : G ⧸ U) :=
        congrArg Subtype.val hqq
      have h2 : (j (q : H ⧸ J).out)⁻¹ * j (q' : H ⧸ J).out ∈ U := QuotientGroup.eq.1 h1
      have h3 := (hU _ h2).1
      have h4 : ((q : H ⧸ J).out)⁻¹ * (q' : H ⧸ J).out ∈ J := by
        simpa [map_mul, map_inv, hpj] using h3
      have h5 : (((q : H ⧸ J).out : H) : H ⧸ J) = (((q' : H ⧸ J).out : H) : H ⧸ J) :=
        QuotientGroup.eq.2 h4
      apply Subtype.ext
      simpa using h5
    · rintro ⟨y, hy⟩
      obtain ⟨h, hh, rfl⟩ := hsurj y hy
      refine ⟨⟨(h : H ⧸ J), hh⟩, Subtype.ext ?_⟩
      change ((j (h : H ⧸ J).out : G) : G ⧸ U) = ((j h : G) : G ⧸ U)
      refine QuotientGroup.eq.2 ?_
      have h1 : ((h : H ⧸ J).out)⁻¹ * h ∈ J := QuotientGroup.eq.1 (by simp)
      have := hJ _ h1
      simpa [map_mul] using this
  unfold dcF dc
  rw [finsum_end_apply, finsum_end_apply, ← finsum_comp e he]
  refine finsum_congr fun q => ?_
  funext g
  have h1 : (((e q : G ⧸ U)).out)⁻¹ * j (q : H ⧸ J).out ∈ U := QuotientGroup.eq.1 (by simp [e])
  have h2 := hφ _ h1 (g * ((e q : G ⧸ U)).out)
  change φ (g * ((e q : G ⧸ U)).out) = φ (g * j (q : H ⧸ J).out)
  rw [← h2]
  congr 1
  group

end
end

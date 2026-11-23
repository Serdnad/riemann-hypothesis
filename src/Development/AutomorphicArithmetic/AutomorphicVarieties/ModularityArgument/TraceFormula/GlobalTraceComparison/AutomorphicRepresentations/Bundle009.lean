module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.SlotBasic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1235
import GroundTheory.LocalFields.PadicLogSeries
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
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
import Mathlib.Tactic.Lemma
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

open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.zSimple_pf :
    GenLoc → LocComm → SphOp → YLoc → ZSimple := by
  intro hG hC hS hY E _ _ _ n S Z N hSec hZ hN π y W hW hst
  have key : ∀ U : Submodule ℂ (Sm E n), U ≤ y.Y →
      (∀ i, Sl S i → ∀ f, IsHecke (N i.1) f → ∀ x ∈ U, Lw N i.1 i.2 f x ∈ U) →
      U = ⊥ ∨ U = y.Y := by
    intro U hU hUs
    have hgen := hG E n S Z N hSec hZ hN U (hU.trans y.fix) hUs
    have hs := y.simple (U.comap y.Y.subtype) (by
      intro h hh x hx
      have hmem : ((y.r h x : y.Y) : Sm E n) ∈ U := by
        rw [y.act h hh x]
        exact hgen h hh _ hx
      exact hmem)
    rcases hs with hs | hs
    · left
      rw [eq_bot_iff]
      intro x hx
      have hx' : (⟨x, hU hx⟩ : y.Y) ∈ U.comap y.Y.subtype := hx
      rw [hs] at hx'
      have h0 := (Submodule.mem_bot ℂ).1 hx'
      exact (Submodule.mem_bot ℂ).2 (congrArg Subtype.val h0)
    · right
      refine le_antisymm hU fun x hx => ?_
      have hx' : (⟨x, hx⟩ : y.Y) ∈ U.comap y.Y.subtype := by
        rw [hs]
        exact Submodule.mem_top
      exact hx'
  have scal : ∀ i, Sl S i → i.1 ∉ Z → ∀ f, IsHecke (N i.1) f →
      ∃ c : ℂ, ∀ x ∈ y.Y, Lw N i.1 i.2 f x = c • x := by
    intro i hi hiZ f hf
    haveI := y.fd
    haveI : Nontrivial y.Y := Submodule.nontrivial_iff_ne_bot.2 y.ne
    have hNw : N i.1 = KGL i.1 (n := n) := (hN i.1).2.2.2 hiZ
    let T : Module.End ℂ y.Y := (Lw N i.1 i.2 f).restrict
      (fun x hx => hY E n S Z N hSec hZ hN π y i hi f hf x hx)
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T
    obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
    refine ⟨c, ?_⟩
    let U : Submodule ℂ (Sm E n) := y.Y ⊓ LinearMap.ker (Lw N i.1 i.2 f - c • LinearMap.id)
    have memU : ∀ x, x ∈ U ↔ x ∈ y.Y ∧ Lw N i.1 i.2 f x = c • x := by
      intro x
      simp [U, Submodule.mem_inf, LinearMap.mem_ker, sub_eq_zero]
    have hcomm : ∀ k, Sl S k → ∀ g, IsHecke (N k.1) g → ∀ x ∈ y.Y,
        Lw N i.1 i.2 f (Lw N k.1 k.2 g x) = Lw N k.1 k.2 g (Lw N i.1 i.2 f x) := by
      intro k hk g hg x hx
      by_cases hik : i = k
      · subst hik
        have hxf : x ∈ fixed (rw' n i.1 i.2) (N i.1) := ((hC E n S Z N hSec hZ hN i hi f hf).1 x (y.fix hx)).1
        rw [hNw] at hf hg hxf
        simp only [Lw]
        rw [hNw]
        exact hS E n i.1 (Sm E n) (rw' n i.1 i.2) f g hf hg x hxf
      · exact LinearMap.congr_fun ((hC E n S Z N hSec hZ hN i hi f hf).2 k hk hik g hg).eq x
    have hUs : ∀ k, Sl S k → ∀ g, IsHecke (N k.1) g → ∀ x ∈ U, Lw N k.1 k.2 g x ∈ U := by
      intro k hk g hg x hx
      obtain ⟨hxY, hxe⟩ := (memU x).1 hx
      refine (memU _).2 ⟨hY E n S Z N hSec hZ hN π y k hk g hg x hxY, ?_⟩
      rw [hcomm k hk g hg x hxY, hxe, map_smul]
    have hvU : (v : Sm E n) ∈ U := by
      refine (memU _).2 ⟨v.2, ?_⟩
      have h1 : T v = c • v := hv.apply_eq_smul
      exact congrArg Subtype.val h1
    rcases key U inf_le_left hUs with h0 | h1
    · exfalso
      rw [h0] at hvU
      exact hv.2 (Subtype.ext ((Submodule.mem_bot ℂ).1 hvU))
    · intro x hx
      rw [← h1] at hx
      exact ((memU x).1 hx).2
  refine key W hW fun i hi f hf x hx => ?_
  by_cases hiZ : i.1 ∈ Z
  · exact hst i.1 hiZ i.2 f hf x hx
  · obtain ⟨c, hc⟩ := scal i hi hiZ f hf
    rw [hc x (hW hx)]
    exact W.smul_mem c hx
end

section

open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc

private lemma lv_eq_sum {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (K : Subgroup G) (u : G → ℂ) (S : Finset (G ⧸ K)) (hS : ∀ c : G ⧸ K, u c.out ≠ 0 → c ∈ S) :
    Lv ρ K u = ∑ c ∈ S, u c.out • ρ c.out := by
  have hs : Function.support (fun c : G ⧸ K => u c.out • (ρ c.out ∘ₗ LinearMap.id)) ⊆ (S : Set (G ⧸ K)) := by
    intro c hc
    refine Finset.mem_coe.2 (hS c fun h0 => hc ?_)
    simp [h0]
  simp only [Lv, GlobalTheory.BCT.levOp, Subgroup.relIndex_self, Nat.cast_one, inv_one, one_smul]
  rw [finsum_eq_sum_of_support_subset _ hs]
  rfl

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.absStep_pf :
    AbsStep := by
  intro G A V _ _ _ _ ρ K N j q f h h₁ hqj hcomm hjN hqK hh hh₁N hK hfN hfs hh₁s y hy
  classical
  have hyk : ∀ k ∈ K, ρ k y = y := fun k hk => by
    have := hy ⟨k, hk⟩
    simpa using this

  have hx0 : ∀ g, q ((j (q g))⁻¹ * g) = 1 := fun g => by simp [hqj]
  have hright : ∀ g k, k ∈ K → h (g * k) = h g := by
    intro g k hk
    rw [hh (g * k), hh g]
    have e1 : f (q (g * k)) = f (q g) := by
      rw [map_mul]
      exact hfN _ (hqK k hk) _
    have c : Commute (j (q k)) ((j (q g))⁻¹ * g) := hcomm (q k) _ (hx0 g)
    have e2 : (j (q (g * k)))⁻¹ * (g * k) = ((j (q g))⁻¹ * g) * ((j (q k))⁻¹ * k) := by
      have c' : (j (q k))⁻¹ * ((j (q g))⁻¹ * g) = ((j (q g))⁻¹ * g) * (j (q k))⁻¹ := c.inv_left.eq
      rw [map_mul, map_mul, mul_inv_rev, ← mul_assoc ((j (q g))⁻¹ * g), ← c']
      simp only [mul_assoc]
    rw [e1, e2, (hK _ (K.mul_mem (K.inv_mem (hjN _ (hqK k hk))) hk) _).2]
  set S₁ : Finset (A ⧸ N) := hfs.toFinset with hS₁
  set S₂ : Finset (G ⧸ K) := hh₁s.toFinset with hS₂
  have m₁ : ∀ s, s ∈ S₁ ↔ f s.out ≠ 0 := fun s => by simp [hS₁]
  have m₂ : ∀ t, t ∈ S₂ ↔ h₁ t.out ≠ 0 := fun t => by simp [hS₂]
  let φ : (A ⧸ N) × (G ⧸ K) → G ⧸ K := fun p => ((j p.1.out * p.2.out : G) : G ⧸ K)
  have hterm : ∀ (s : A ⧸ N) (t : G ⧸ K), t ∈ S₂ → h (j s.out * t.out) = f s.out * h₁ t.out := by
    intro s t ht
    have hn : q t.out ∈ N := hh₁N _ ((m₂ t).1 ht)
    have e0 : q (j s.out * t.out) = s.out * q t.out := by rw [map_mul, hqj]
    have e1 : (j (q (j s.out * t.out)))⁻¹ * (j s.out * t.out) = (j (q t.out))⁻¹ * t.out := by
      rw [e0, map_mul, mul_inv_rev]
      group
    rw [hh, e1, e0, hfN _ hn, (hK _ (K.inv_mem (hjN _ hn)) _).1]
  have hinj : Set.InjOn φ (S₁ ×ˢ S₂ : Finset _) := by
    rintro ⟨s, t⟩ hp ⟨s', t'⟩ hp' e
    have ht : t ∈ S₂ := (Finset.mem_product.1 (Finset.mem_coe.1 hp)).2
    have ht' : t' ∈ S₂ := (Finset.mem_product.1 (Finset.mem_coe.1 hp')).2
    have hn : q t.out ∈ N := hh₁N _ ((m₂ t).1 ht)
    have hn' : q t'.out ∈ N := hh₁N _ ((m₂ t').1 ht')
    have hk : (j s.out * t.out)⁻¹ * (j s'.out * t'.out) ∈ K := QuotientGroup.eq.1 e
    have hq : (q t.out)⁻¹ * (s.out⁻¹ * s'.out) * q t'.out ∈ N := by
      have := hqK _ hk
      simpa [hqj, mul_assoc] using this
    have hs : s.out⁻¹ * s'.out ∈ N := by
      have := N.mul_mem (N.mul_mem hn hq) (N.inv_mem hn')
      simpa [mul_assoc] using this
    have es : s = s' := by
      rw [← QuotientGroup.out_eq' s, ← QuotientGroup.out_eq' s']
      exact QuotientGroup.eq.2 hs
    subst es
    have ht2 : t.out⁻¹ * t'.out ∈ K := by
      simpa [mul_assoc] using hk
    have et : t = t' := by
      rw [← QuotientGroup.out_eq' t, ← QuotientGroup.out_eq' t']
      exact QuotientGroup.eq.2 ht2
    rw [et]
  have hsupp : ∀ c : G ⧸ K, h c.out ≠ 0 → c ∈ (S₁ ×ˢ S₂).image φ := by
    intro c hc
    set g := c.out with hg
    set a := q g with ha
    set x := (j a)⁻¹ * g with hx
    rw [hh g] at hc
    have hfa : f a ≠ 0 := left_ne_zero_of_mul hc
    have hhx : h₁ x ≠ 0 := right_ne_zero_of_mul hc
    obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul N a
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K x
    refine Finset.mem_image.2 ⟨((a : A ⧸ N), (x : G ⧸ K)), Finset.mem_product.2 ⟨?_, ?_⟩, ?_⟩
    · show ((a : A ⧸ N)) ∈ S₁
      rw [m₁, hn, hfN _ n.2]
      exact hfa
    · show ((x : G ⧸ K)) ∈ S₂
      rw [m₂, hk, (hK _ k.2 _).2]
      exact hhx
    · show ((j (a : A ⧸ N).out * (x : G ⧸ K).out : G) : G ⧸ K) = c
      have c1 : Commute (j (n : A)) x := hcomm _ _ (hx0 g)
      have e : j (a : A ⧸ N).out * (x : G ⧸ K).out = g * (j (n : A) * (k : G)) := by
        have hgx : j a * x = g := by rw [hx]; group
        rw [hn, hk, map_mul, mul_assoc (j a), ← mul_assoc (j (n : A)), c1.eq, mul_assoc x, ← mul_assoc (j a), hgx]
      rw [e, QuotientGroup.mk_mul_of_mem _ (K.mul_mem (hjN _ n.2) k.2), hg, QuotientGroup.out_eq']
  have hout : ∀ p ∈ S₁ ×ˢ S₂, h (φ p).out • ρ (φ p).out y = (f p.1.out * h₁ p.2.out) • ρ (j p.1.out * p.2.out) y := by
    rintro ⟨s, t⟩ hp
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (j s.out * t.out)
    have ht : t ∈ S₂ := (Finset.mem_product.1 hp).2
    show h (((j s.out * t.out : G) : G ⧸ K)).out • ρ (((j s.out * t.out : G) : G ⧸ K)).out y = _
    rw [hk, hright _ _ k.2, hterm s t ht, map_mul ρ (j s.out * t.out), Module.End.mul_apply, hyk _ k.2]
  rw [lv_eq_sum ρ K h _ hsupp, lv_eq_sum (ρ.comp j) N f S₁ (fun s hs => (m₁ s).2 hs),
    lv_eq_sum ρ K h₁ S₂ (fun t ht => (m₂ t).2 ht)]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  rw [Finset.sum_image hinj, Finset.sum_congr rfl hout, Finset.sum_product]
  refine Finset.sum_congr rfl fun s _ => ?_

  simp only [MonoidHom.comp_apply, map_sum, map_smul, Finset.smul_sum, smul_smul, map_mul, Module.End.mul_apply]
end

section

noncomputable section

open GlobalTheory.BCT GlobalTheory.PRep

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

section SlopeTestRemainingChoices

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

private theorem mem_fixed_iff (ρ : Representation ℂ G V) (K : Subgroup G) (y : V) :
    y ∈ fixed ρ K ↔ ∀ k ∈ K, ρ k y = y := by
  constructor
  · intro hy k hk
    have := hy ⟨k, hk⟩
    simpa using this
  · intro hy k
    simpa using hy k k.2

private theorem lv_apply (ρ : Representation ℂ G V) (K : Subgroup G) (f : G → ℂ) (y : V)
    (hf : (Function.support fun q : G ⧸ K => f q.out).Finite) :
    Lv ρ K f y = ∑ᶠ q : G ⧸ K, f q.out • ρ q.out y := by
  have hs : (Function.support fun q : G ⧸ K =>
      f q.out • (ρ q.out ∘ₗ (LinearMap.id : V →ₗ[ℂ] V))).Finite := hf.subset (by
    intro q hq hz
    apply hq
    simp [hz])
  simp only [Lv, levOp, Subgroup.relIndex_self, Nat.cast_one, inv_one, one_smul]
  have := map_finsum (LinearMap.applyₗ y : (V →ₗ[ℂ] V) →ₗ[ℂ] V) hs
  simpa using this

private theorem reindex (K : Subgroup G) (σ : G ⧸ K ≃ G ⧸ K) (a : G → G)
    (hσ : ∀ g : G, σ (g : G ⧸ K) = (a g : G ⧸ K)) (ψ₁ ψ₂ : G → V)
    (hi : ∀ g, ∀ k ∈ K, ψ₁ (g * k) = ψ₁ g) (ha : ∀ g, ψ₁ (a g) = ψ₂ g) :
    ∑ᶠ q : G ⧸ K, ψ₁ q.out = ∑ᶠ q : G ⧸ K, ψ₂ q.out := by
  refine (finsum_comp_equiv σ (f := fun q : G ⧸ K => ψ₁ q.out)).symm.trans (finsum_congr fun q => ?_)
  have e : ((a q.out : G) : G ⧸ K) = ((σ q).out : G) := by
    rw [← hσ, QuotientGroup.out_eq', QuotientGroup.out_eq']
  have hk : (a q.out)⁻¹ * (σ q).out ∈ K := QuotientGroup.eq.1 e
  show ψ₁ (σ q).out = ψ₂ q.out
  rw [← ha, ← hi (a q.out) _ hk, mul_inv_cancel_left]

private def rEquiv (K : Subgroup G) (u : G) (h₁ : ∀ x ∈ K, u * x * u⁻¹ ∈ K)
    (h₂ : ∀ x ∈ K, u⁻¹ * x * u ∈ K) : G ⧸ K ≃ G ⧸ K where
  toFun := Quotient.map' (· * u) (by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    have := h₂ _ hab
    convert this using 1
    group)
  invFun := Quotient.map' (· * u⁻¹) (by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    have := h₁ _ hab
    convert this using 1
    group)
  left_inv := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      show ((g * u * u⁻¹ : G) : G ⧸ K) = g
      rw [mul_inv_cancel_right]
  right_inv := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      show ((g * u⁻¹ * u : G) : G ⧸ K) = g
      rw [inv_mul_cancel_right]

private theorem fin_supp [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G)
    (hK : IsOpen (K : Set G)) (f : G → ℂ) (hf : HasCompactSupport f) :
    (Function.support fun q : G ⧸ K => f q.out).Finite := by
  obtain ⟨t, ht⟩ := hf.isCompact.elim_finite_subcover
    (fun x : G => (fun y => x⁻¹ * y) ⁻¹' (K : Set G))
    (fun x => hK.preimage (continuous_const.mul continuous_id))
    (fun x _ => Set.mem_iUnion.2 ⟨x, by simp [K.one_mem]⟩)
  refine (t.finite_toSet.image (fun x : G => (x : G ⧸ K))).subset ?_
  intro q hq
  have hm : q.out ∈ tsupport f := subset_tsupport _ hq
  obtain ⟨x, hx, hxq⟩ := Set.mem_iUnion₂.1 (ht hm)
  exact ⟨x, hx, (QuotientGroup.eq.2 hxq).trans (QuotientGroup.out_eq' q)⟩

end SlopeTestRemainingChoices

theorem lvShift_pf : LvShift := by
  intro G V _ _ _ _ _ ρ K hKo hKc u hu h hh
  have hc : ∀ x ∈ K, u * x * u⁻¹ ∈ K := fun x hx => (hu x).1 hx
  have hc' : ∀ x ∈ K, u⁻¹ * x * u ∈ K := fun x hx => (hu _).2 (by
    have e : u * (u⁻¹ * x * u) * u⁻¹ = x := by group
    rwa [e])
  have H1 : IsHecke K (fun g => h (g * u⁻¹)) := by
    refine ⟨hh.1.comp_homeomorph (Homeomorph.mulRight u⁻¹), fun k hk x => ⟨?_, ?_⟩⟩
    · show h (k * x * u⁻¹) = h (x * u⁻¹)
      rw [mul_assoc]
      exact (hh.2 k hk _).1
    · show h (x * k * u⁻¹) = h (x * u⁻¹)
      have e : x * k * u⁻¹ = x * u⁻¹ * (u * k * u⁻¹) := by group
      rw [e]
      exact (hh.2 _ (hc k hk) _).2
  have H2 : IsHecke K (fun g => h (u⁻¹ * g)) := by
    refine ⟨hh.1.comp_homeomorph (Homeomorph.mulLeft u⁻¹), fun k hk x => ⟨?_, ?_⟩⟩
    · show h (u⁻¹ * (k * x)) = h (u⁻¹ * x)
      have e : u⁻¹ * (k * x) = u⁻¹ * k * u * (u⁻¹ * x) := by group
      rw [e]
      exact (hh.2 _ (hc' k hk) _).1
    · show h (u⁻¹ * (x * k)) = h (u⁻¹ * x)
      rw [← mul_assoc]
      exact (hh.2 k hk _).2
  have H3 : IsHecke K ((K : Set G).indicator 1) := by
    refine ⟨?_, fun k hk x => ⟨?_, ?_⟩⟩
    · have e : Function.support ((K : Set G).indicator (1 : G → ℂ)) = (K : Set G) := by
        ext x
        by_cases hx : x ∈ (K : Set G) <;> simp [hx]
      show IsCompact (closure (Function.support ((K : Set G).indicator (1 : G → ℂ))))
      rw [e, (K.isClosed_of_isOpen hKo).closure_eq]
      exact hKc
    · have : k * x ∈ (K : Set G) ↔ x ∈ (K : Set G) := K.mul_mem_cancel_left hk
      by_cases hx : x ∈ (K : Set G)
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (this.2 hx)]
        rfl
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun c => hx (this.1 c))]
    · have : x * k ∈ (K : Set G) ↔ x ∈ (K : Set G) := K.mul_mem_cancel_right hk
      by_cases hx : x ∈ (K : Set G)
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (this.2 hx)]
        rfl
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun c => hx (this.1 c))]
  refine ⟨H1, H2, H3, fun y hy => ?_⟩
  have hy' := (mem_fixed_iff ρ K y).1 hy
  have hm : ∀ (a b : G) (v : V), ρ (a * b) v = ρ a (ρ b v) := fun a b v => by
    rw [map_mul]
    rfl
  have hinv : ∀ (f : G → ℂ), (∀ k ∈ K, ∀ x, f (x * k) = f x) → ∀ g, ∀ k ∈ K,
      f (g * k) • ρ (g * k) y = f g • ρ g y := fun f hf g k hk => by
    rw [hf k hk, hm, hy' k hk]
  refine ⟨(mem_fixed_iff ρ K _).2 fun k hk => ?_, ?_, ?_, ?_⟩
  · have e : k * u = u * (u⁻¹ * k * u) := by group
    rw [← hm, e, hm, hy' _ (hc' k hk)]
  · rw [lv_apply ρ K _ y (fin_supp K hKo _ H1.1), lv_apply ρ K h _ (fin_supp K hKo _ hh.1)]
    refine reindex K (rEquiv K u hc hc') (· * u) (fun g => rfl)
      (fun g => h (g * u⁻¹) • ρ g y) (fun g => h g • ρ g (ρ u y))
      (hinv (fun g => h (g * u⁻¹)) fun k hk x => (H1.2 k hk x).2) fun g => ?_
    show h (g * u * u⁻¹) • ρ (g * u) y = h g • ρ g (ρ u y)
    rw [mul_inv_cancel_right, hm]
  · have hs : (Function.support fun q : G ⧸ K => h q.out • ρ q.out y).Finite :=
      (fin_supp K hKo _ hh.1).subset (by
        intro q hq hz
        apply hq
        simp [hz])
    rw [lv_apply ρ K _ y (fin_supp K hKo _ H2.1), lv_apply ρ K h y (fin_supp K hKo _ hh.1),
      map_finsum (ρ u) hs]
    simp only [map_smul]
    refine reindex K (MulAction.toPerm u) (u * ·) (fun g => rfl)
      (fun g => h (u⁻¹ * g) • ρ g y) (fun g => h g • ρ u (ρ g y))
      (hinv (fun g => h (u⁻¹ * g)) fun k hk x => (H2.2 k hk x).2) fun g => ?_
    show h (u⁻¹ * (u * g)) • ρ (u * g) y = h g • ρ u (ρ g y)
    rw [inv_mul_cancel_left, hm]
  · rw [lv_apply ρ K _ y (fin_supp K hKo _ H3.1)]
    have h1 : ((1 : G) : G ⧸ K).out ∈ (K : Set G) := by
      have : ((((1 : G) : G ⧸ K).out : G) : G ⧸ K) = ((1 : G) : G ⧸ K) := QuotientGroup.out_eq' _
      have := QuotientGroup.eq.1 this
      simpa using this
    rw [finsum_eq_single _ ((1 : G) : G ⧸ K)]
    · rw [Set.indicator_of_mem h1, hy' _ h1]
      simp
    · intro q hq
      have : q.out ∉ (K : Set G) := fun c => hq (by
        rw [← QuotientGroup.out_eq' q]
        exact QuotientGroup.eq.2 (by simpa using K.inv_mem c))
      rw [Set.indicator_of_notMem this, zero_smul]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
end

section

open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc
open GlobalTheory.BCT GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.L2.Host Formalism.UG Formalism.BasicNotions

private theorem lv_commute {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ G V) (H : Subgroup G) (hH : IsOpen (H : Set G)) (f : G → ℂ)
    (hf : HasCompactSupport f) (T : Module.End ℂ V) (hT : ∀ a, Commute T (ρ a)) : Commute T (Lv ρ H f) := by
  have hs := GlobalTheory.TwTrLevel.finite_supp H hH f hf
  have hsupp : (Function.support fun q : G ⧸ H =>
      f q.out • (ρ q.out ∘ₗ (LinearMap.id : V →ₗ[ℂ] V))).Finite :=
    hs.subset fun q hq h0 => hq (by simp [h0])
  unfold UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.Lv levOp
  rw [finsum_eq_sum_of_support_subset _ (s := hsupp.toFinset) (by simp)]
  refine Commute.smul_right (Commute.sum_right _ _ _ fun q _ => Commute.smul_right ?_ _) _
  rw [LinearMap.comp_id]
  exact hT _

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.locComm_pf :
    SlotBasic → LevTop → LocComm := by
  intro hSF _ E _ _ _ n S Z N hSec _ hG i hi f hf
  obtain ⟨-, -, hloc, hind, -⟩ := hSF E n S hSec
  have hmem : ∀ c, c ∈ Lev S N ↔ ∀ k, Sl S k → qw n k.1 k.2 c ∈ N k.1 := by
    intro c
    simp only [Lev, Subgroup.mem_iInf, Subgroup.mem_comap, Subtype.forall]
  have hjw : ∀ a ∈ N i.1, jw n i.1 i.2 a ∈ Lev S N := by
    intro a ha
    refine (hmem _).2 fun k hk => ?_
    by_cases h : i = k
    · subst h
      rw [(hloc i.1 i.2).2.2.1]
      exact ha
    · rw [hind i k hi hk h a]
      exact one_mem _
  have hopen := (hG i.1).1
  refine ⟨fun y hy => ?_, fun k hk hik g hg => ?_⟩
  · have hy' := (GlobalTheory.TwTrLevel.mem_fixed_iff _ _ y).1 hy
    have h1 : y ∈ fixed (rw' n i.1 i.2) (N i.1) :=
      (GlobalTheory.TwTrLevel.mem_fixed_iff _ _ y).2 fun a ha => hy' _ (hjw a ha)
    refine ⟨h1, (GlobalTheory.TwTrLevel.mem_fixed_iff _ _ _).2 fun c hc => ?_⟩
    have ha : qw n i.1 i.2 c ∈ N i.1 := (hmem c).1 hc i hi
    obtain ⟨c', hcc⟩ : ∃ c', c' = (jw n i.1 i.2 (qw n i.1 i.2 c))⁻¹ * c := ⟨_, rfl⟩
    have hc' : c' ∈ Lev S N := hcc ▸ mul_mem (inv_mem (hjw _ ha)) hc
    have hq : qw n i.1 i.2 c' = 1 := by
      rw [hcc, map_mul, map_inv, (hloc i.1 i.2).2.2.1, inv_mul_cancel]
    have hc2 : c = jw n i.1 i.2 (qw n i.1 i.2 c) * c' := by
      rw [hcc, mul_inv_cancel_left]
    have hL : Commute (finRep E n c') (Lw N i.1 i.2 f) :=
      lv_commute (rw' n i.1 i.2) (N i.1) hopen f hf.1 _ fun a =>
        (((hloc i.1 i.2).2.2.2 a c' hq).map (finRep E n)).symm
    have hfix : Lw N i.1 i.2 f y ∈ fixed (rw' n i.1 i.2) (N i.1) :=
      GlobalTheory.TwTrLevel.levOp_mem_fixed (rw' n i.1 i.2) (MonoidHom.id _) (fun _ => rfl) LinearMap.id
        (fun _ => rfl) (N i.1) (N i.1) hopen (fun _ h => h) f hf y h1
    have e : finRep E n c' (Lw N i.1 i.2 f y) = Lw N i.1 i.2 f y := by
      have h2 := LinearMap.congr_fun hL.eq y
      rw [Module.End.mul_apply, Module.End.mul_apply, hy' c' hc'] at h2
      exact h2
    have h3 := (GlobalTheory.TwTrLevel.mem_fixed_iff _ _ _).1 hfix _ ha
    rw [hc2, map_mul, Module.End.mul_apply, e]
    exact h3
  · have hrr : ∀ a b, Commute (rw' n i.1 i.2 a) (rw' n k.1 k.2 b) := fun a b =>
      (((hloc k.1 k.2).2.2.2 b (jw n i.1 i.2 a) (hind i k hi hk hik a)).map (finRep E n)).symm
    exact lv_commute (rw' n k.1 k.2) (N k.1) (hG k.1).1 g hg.1 _ fun b =>
      (lv_commute (rw' n i.1 i.2) (N i.1) hopen f hf.1 _ fun a => (hrr a b).symm).symm
end

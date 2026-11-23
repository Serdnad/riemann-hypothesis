module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.Bundle001
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

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.So.extF :
    UpperTheory.V.Z.Sym.So.ExtF := by
  intro Γ G V _ _ _ _ ι W S U hSn hcomm hΓ ψ hψΓ hψU
  classical
  have wd : ∀ (γ γ' : Γ) (s s' : S) (u u' : G), u ∈ U → u' ∈ U →
      ι γ * s * u = ι γ' * s' * u' → W γ (ψ s) = W γ' (ψ s') := by
    intro γ γ' s s' u u' hu hu' h
    have hv : u * u'⁻¹ ∈ U := U.mul_mem hu (U.inv_mem hu')
    have h1 : ι (γ'⁻¹ * γ) * s * (u * u'⁻¹) = s' := by
      rw [map_mul, map_inv]
      rw [show (ι γ')⁻¹ * ι γ * ↑s * (u * u'⁻¹) = (ι γ')⁻¹ * (ι γ * ↑s * u) * u'⁻¹ by group, h]
      group
    have hδ : ι (γ'⁻¹ * γ) ∈ S := by
      apply hΓ (γ'⁻¹ * γ) (u * u'⁻¹) hv
      have e : ι (γ'⁻¹ * γ) * (u * u'⁻¹) =
          ↑s' * ((u * u'⁻¹)⁻¹ * (↑s)⁻¹ * (u * u'⁻¹)) := by
        rw [← h1]
        group
      rw [e]
      apply S.mul_mem s'.2
      have hc := hSn.conj_mem _ (S.inv_mem s.2) (u * u'⁻¹)⁻¹
      rw [inv_inv] at hc
      exact hc
    have hvS : u * u'⁻¹ ∈ S := by
      have e : u * u'⁻¹ = (ι (γ'⁻¹ * γ) * ↑s)⁻¹ * ↑s' := by
        rw [← h1]
        group
      rw [e]
      exact S.mul_mem (S.inv_mem (S.mul_mem hδ s.2)) s'.2
    have e1 : s' = ⟨ι (γ'⁻¹ * γ) * s, S.mul_mem hδ s.2⟩ * ⟨u * u'⁻¹, hvS⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_mk]
      exact h1.symm
    rw [e1, hψU ⟨u * u'⁻¹, hvS⟩ hv,
      hψΓ (γ'⁻¹ * γ) s ⟨ι (γ'⁻¹ * γ) * s, S.mul_mem hδ s.2⟩ rfl, ← Module.End.mul_apply, ← map_mul,
      mul_inv_cancel_left]
  obtain ⟨P, hP⟩ : ∃ P : G → Prop, ∀ g, P g ↔ ∃ γ : Γ, ∃ s : S, ∃ u ∈ U, g = ι γ * s * u :=
    ⟨_, fun _ => Iff.rfl⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : G → V, ∀ g, Φ g = if h : P g then
      W ((hP g).1 h).choose (ψ ((hP g).1 h).choose_spec.choose) else 0 := ⟨_, fun _ => rfl⟩
  have Φ_spec : ∀ (γ : Γ) (s : S) (u : G), u ∈ U → Φ (ι γ * s * u) = W γ (ψ s) := by
    intro γ s u hu
    have h : P (ι γ * s * u) := (hP _).2 ⟨γ, s, u, hu, rfl⟩
    rw [hΦ, dite_eq_left h]
    obtain ⟨u0, hu0, e⟩ := ((hP _).1 h).choose_spec.choose_spec
    exact wd _ _ _ _ _ _ hu0 hu e.symm
  have Φ_neg : ∀ g, ¬ P g → Φ g = 0 := fun g h => by rw [hΦ, dite_eq_right h]
  have hUinv : ∀ u ∈ U, ∀ g : G, Φ (g * u) = Φ g := by
    intro u hu g
    by_cases hg : P g
    · obtain ⟨γ, s, u0, hu0, rfl⟩ := (hP g).1 hg
      rw [show ι γ * ↑s * u0 * u = ι γ * ↑s * (u0 * u) by group, Φ_spec _ _ _ (U.mul_mem hu0 hu),
        Φ_spec _ _ _ hu0]
    · rw [Φ_neg _ hg, Φ_neg]
      intro h'
      apply hg
      obtain ⟨γ, s, u1, hu1, e⟩ := (hP _).1 h'
      refine (hP g).2 ⟨γ, s, u1 * u⁻¹, U.mul_mem hu1 (U.inv_mem hu), ?_⟩
      rw [← mul_assoc, ← e]
      group
  refine ⟨Φ, ?_, ?_, hUinv, ?_⟩
  · intro g
    have h := Φ_spec 1 g 1 U.one_mem
    simpa using h
  · intro γ g
    by_cases hg : P g
    · obtain ⟨δ, s, u, hu, rfl⟩ := (hP g).1 hg
      rw [show ι γ * (ι δ * ↑s * u) = ι (γ * δ) * ↑s * u by rw [map_mul]; group,
        Φ_spec _ _ _ hu, Φ_spec _ _ _ hu, map_mul, Module.End.mul_apply]
    · rw [Φ_neg _ hg, map_zero, Φ_neg]
      intro h'
      apply hg
      obtain ⟨δ, s, u, hu, e⟩ := (hP _).1 h'
      refine (hP g).2 ⟨γ⁻¹ * δ, s, u, hu, ?_⟩
      have e2 : g = (ι γ)⁻¹ * (ι γ * g) := by group
      rw [e2, e, map_mul, map_inv]
      group
  · intro a c hfin hz heig
    obtain ⟨hfinS, hmem, -, R, hR1, hR2, hR3⟩ := dcSub G V S U a hfin hz hSn
    have hψU' : ∀ u ∈ U.subgroupOf S, ∀ g : S, ψ (g * u) = ψ g :=
      fun u hu g => hψU u (Subgroup.mem_subgroupOf.1 hu) g
    have hval : ∀ x ∈ U, ∀ g : G, dcF U (↑a) Φ g = ∑ r ∈ R, Φ (g * (x⁻¹ * ↑r * x)) := by
      intro x hx g
      let e : S ↪ G := ⟨fun r => x⁻¹ * ↑r * x, fun r1 r2 h => Subtype.ext (by simpa using h)⟩
      have h1 : ∀ y ∈ R.map e, y ∈ DC U (↑a) := by
        intro y hy
        obtain ⟨r, hr, rfl⟩ := Finset.mem_map.1 hy
        obtain ⟨v, hv, w, hw, h⟩ := (hmem r).1 (hR1 r hr)
        refine ⟨x⁻¹ * v, U.mul_mem (U.inv_mem hx) hv, w * x, U.mul_mem hw hx, ?_⟩
        show x⁻¹ * ↑r * x = _
        rw [h]
        group
      have h2 : ∀ y ∈ DC U (↑a), ∃! r, r ∈ R.map e ∧ r⁻¹ * y ∈ U := by
        intro y hy
        have hxy : x * y ∈ DC U (↑a) := by
          obtain ⟨v, hv, w, hw, rfl⟩ := hy
          exact ⟨x * v, U.mul_mem hx hv, w, hw, by group⟩
        obtain ⟨r, ⟨hr, hry⟩, huniq⟩ := hR3 _ hxy
        refine ⟨x⁻¹ * ↑r * x, ⟨Finset.mem_map_of_mem e hr, ?_⟩, ?_⟩
        · have e3 : (x⁻¹ * ↑r * x)⁻¹ * y = x⁻¹ * ((↑r)⁻¹ * (x * y)) := by group
          rw [e3]
          exact U.mul_mem (U.inv_mem hx) hry
        · rintro y' ⟨hy', hy'y⟩
          obtain ⟨r1, hr1, rfl⟩ := Finset.mem_map.1 hy'
          have hr1y : (↑r1 : G)⁻¹ * (x * y) ∈ U := by
            have e4 : (↑r1 : G)⁻¹ * (x * y) = x * ((x⁻¹ * ↑r1 * x)⁻¹ * y) := by group
            rw [e4]
            exact U.mul_mem hx hy'y
          rw [huniq r1 ⟨hr1, hr1y⟩]
          rfl
      rw [(dcBasic G V U a hfin Φ hUinv).2.2.2.2 (R.map e) h1 h2 g, Finset.sum_map]
      rfl
    funext g
    rw [Pi.smul_apply]
    by_cases hg : P g
    · obtain ⟨γ, s, u, hu, rfl⟩ := (hP g).1 hg
      rw [hval u hu, Φ_spec γ s u hu]
      have e5 : ∀ r : S, Φ (ι γ * ↑s * u * (u⁻¹ * ↑r * u)) = W γ (ψ (s * r)) := by
        intro r
        rw [show ι γ * ↑s * u * (u⁻¹ * ↑r * u) = ι γ * ↑(s * r) * u by
          simp only [Subgroup.coe_mul]; group, Φ_spec _ _ _ hu]

      rw [Finset.sum_congr rfl (fun r _ => e5 r), ← map_sum (W γ),
      ← (dcBasic S V (U.subgroupOf S) a hfinS ψ hψU').2.2.2.2 R hR1 hR2 s, heig, Pi.smul_apply,
      map_smul]
    · rw [hval 1 U.one_mem, Φ_neg _ hg, smul_zero]
      apply Finset.sum_eq_zero
      intro r _
      apply Φ_neg
      intro h'
      apply hg
      obtain ⟨γ, s, u, hu, e⟩ := (hP _).1 h'
      refine (hP g).2 ⟨γ, s * ⟨u * (↑r)⁻¹ * u⁻¹, hSn.conj_mem _ (S.inv_mem r.2) u⟩, u, hu, ?_⟩
      have e6 : g = g * (1⁻¹ * ↑r * 1) * (↑r)⁻¹ := by group
      rw [e6, e]
      simp only [Subgroup.coe_mul, Subgroup.coe_mk]
      group

end
end

section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem core {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    (Fi In Rt U : Subgroup G) [hN : Fi.Normal] (c : G →* H) (R : Representation ℂ H V)
    (hdec : ∀ x : G, ∃ f ∈ Fi, ∃ k ∈ In, x = f * k)
    (hcomm : ∀ f ∈ Fi, ∀ k ∈ In, Commute f k)
    (hint : ∀ x ∈ Fi, x ∈ In → x = 1)
    (hc : ∀ x ∈ Fi, c x = 1)
    (hU : U ≤ Fi)
    (Φ : Fi → V)
    (hL : ∀ (f : Fi), ∀ k ∈ In, (f : G) * k ∈ Rt → ∀ g, Φ (f * g) = R (c k) (Φ g))
    (hV : ∀ u : Fi, (u : G) ∈ U → ∀ g, Φ (g * u) = Φ g) :
    ∃ φ : G → V, (∀ γ ∈ Rt, ∀ g, φ (γ * g) = φ g) ∧ (∀ x ∈ In, ∀ g, φ (g * x) = R (c x⁻¹) (φ g)) ∧
      (∀ u ∈ U, ∀ g, φ (g * u) = φ g) ∧ (∀ g : Fi, φ g = Φ g) ∧
      ∀ (x : Fi) (cc : ℂ), UpperTheory.V.AlgebraTools.FinOrb U U (x : G) →
        dcF (U.subgroupOf Fi) x Φ = cc • Φ → dcF U (x : G) φ = cc • φ := by
  classical
  have hex : ∀ x : G, ∃ f : Fi, (f : G)⁻¹ * x ∈ In := by
    intro x
    obtain ⟨f, hf, k, hk, rfl⟩ := hdec x
    exact ⟨⟨f, hf⟩, by simpa using hk⟩
  choose p hp using hex
  have hpu : ∀ (f : Fi) (k : G), k ∈ In → p ((f : G) * k) = f := by
    intro f k hk
    have h2 : ((p ((f : G) * k) : G)⁻¹ * f) ∈ In := by
      have := In.mul_mem (hp ((f : G) * k)) (In.inv_mem hk)
      simpa [mul_assoc] using this
    have h3 : ((p ((f : G) * k) : G)⁻¹ * f) ∈ Fi := Fi.mul_mem (Fi.inv_mem (p _).2) f.2
    exact Subtype.ext (inv_mul_eq_one.mp (hint _ h3 h2))
  have hfac : ∀ g : G, ∃ k ∈ In, g = (p g : G) * k := fun g => ⟨_, hp g, by simp⟩
  have hmulR : ∀ (g : G) (f : Fi), p (g * f) = p g * f := by
    intro g f
    obtain ⟨k, hk, hg⟩ := hfac g
    have : g * f = ((p g * f : Fi) : G) * k := by
      have h := (hcomm f f.2 k hk).eq
      calc g * f = (p g : G) * (k * f) := by rw [← mul_assoc, ← hg]
        _ = _ := by rw [← h]; simp [mul_assoc]
    rw [this, hpu _ _ hk]
  have hmulL : ∀ (f : Fi) (g : G), p ((f : G) * g) = f * p g := by
    intro f g
    obtain ⟨k, hk, hg⟩ := hfac g
    have : (f : G) * g = ((f * p g : Fi) : G) * k := by
      calc (f : G) * g = (f : G) * ((p g : G) * k) := by rw [← hg]
        _ = _ := by simp [mul_assoc]
    rw [this, hpu _ _ hk]
  have hmulIn : ∀ (g k : G), k ∈ In → p (g * k) = p g := by
    intro g k hk
    obtain ⟨k', hk', hg⟩ := hfac g
    have : g * k = (p g : G) * (k' * k) := by
      calc g * k = (p g : G) * k' * k := by rw [← hg]
        _ = _ := by rw [mul_assoc]
    rw [this, hpu _ _ (In.mul_mem hk' hk)]
  have hinL : ∀ (k g : G), k ∈ In → p (k * g) = p g := by
    intro k g hk
    obtain ⟨k', hk', hg⟩ := hfac g
    have : k * g = (p g : G) * (k * k') := by
      have h := (hcomm (p g) (p g).2 k hk).eq
      calc k * g = k * ((p g : G) * k') := by rw [← hg]
        _ = _ := by rw [← mul_assoc, ← h, mul_assoc]
    rw [this, hpu _ _ (In.mul_mem hk hk')]
  refine ⟨fun x => R (c x)⁻¹ (Φ (p x)), ?_, ?_, ?_, ?_, ?_⟩
  · intro γ hγ g
    have hk := hp γ
    have hγ' : (p γ : G) * ((p γ : G)⁻¹ * γ) = γ := by simp
    have hcγ : c ((p γ : G)⁻¹ * γ) = c γ := by
      rw [map_mul, map_inv, hc _ (p γ).2]; simp
    have hpp : p (γ * g) = p γ * p g := by
      have : γ * g = (p γ : G) * (((p γ : G)⁻¹ * γ) * g) := by simp [mul_assoc]
      rw [this, hmulL, hinL _ _ hk]
    have h := hL (p γ) _ hk (by rw [hγ']; exact hγ) (p g)
    simp only [hpp, h, hcγ, map_mul, mul_inv_rev, Module.End.mul_apply]
    rw [← Module.End.mul_apply (R (c γ)⁻¹), ← map_mul]
    simp
  · intro x hx g
    simp only [hmulIn g x hx, map_mul, mul_inv_rev, map_inv, Module.End.mul_apply]
  · intro u hu g
    have h := hmulR g ⟨u, hU hu⟩
    simp only at h
    simp only [h, map_mul, hc u (hU hu), mul_one]
    rw [hV ⟨u, hU hu⟩ hu]
  · intro g
    have h := hpu g 1 In.one_mem
    rw [mul_one] at h
    simp [h, hc _ g.2]
  · intro x cc hfo heig
    obtain ⟨hfo', hDC, -, Rr, hR1, hR2, hR3⟩ := dcSub G V Fi U x hfo
      (fun u hu => ⟨1, U.one_mem, by simp, by simpa using hU hu, by simpa using hU hu⟩) hN
    have hΦ : ∀ u ∈ U.subgroupOf Fi, ∀ g, Φ (g * u) = Φ g := fun u hu g => hV u hu g
    have hsum := (dcBasic Fi V (U.subgroupOf Fi) x hfo' Φ hΦ).2.2.2.2 Rr hR1 hR2
    have hφ : ∀ u ∈ U, ∀ g, (fun x => R (c x)⁻¹ (Φ (p x))) (g * u) = (fun x => R (c x)⁻¹ (Φ (p x))) g := by
      intro u hu g
      have h := hmulR g ⟨u, hU hu⟩
      simp only at h
      simp only [h, map_mul, hc u (hU hu), mul_one]
      rw [hV ⟨u, hU hu⟩ hu]
    have hsum' := (dcBasic G V U x hfo (fun x => R (c x)⁻¹ (Φ (p x))) hφ).2.2.2.2 (Rr.map (Function.Embedding.subtype _))
      (by
        intro y hy
        obtain ⟨r, hr, rfl⟩ := Finset.mem_map.mp hy
        exact (hDC r).1 (hR1 r hr))
      (by
        intro y hy
        obtain ⟨r, ⟨hr, hry⟩, hu⟩ := hR3 y hy
        refine ⟨r, ⟨Finset.mem_map.mpr ⟨r, hr, rfl⟩, hry⟩, ?_⟩
        rintro r' ⟨hr', hry'⟩
        obtain ⟨r'', hr'', rfl⟩ := Finset.mem_map.mp hr'
        simpa using congrArg Subtype.val (hu r'' ⟨hr'', hry'⟩))
    funext g
    rw [hsum' g, Finset.sum_map]
    have hE := congrFun heig (p g)
    rw [hsum (p g)] at hE
    simp only [Function.Embedding.subtype_apply, Pi.smul_apply]
    have : ∀ r : Fi, R (c (g * r))⁻¹ (Φ (p (g * r))) = R (c g)⁻¹ (Φ (p g * r)) := by
      intro r
      rw [hmulR, map_mul, hc _ r.2, mul_one]
    simp only [this]

    rw [← map_sum, hE, Pi.smul_apply, map_smul]

theorem UpperTheory.V.Z.Sym.So.finToAF :
    UpperTheory.V.Z.Sym.So.FinToAF := by
  intro L _ _ _ n V _ _ R U hU Φ hL hV
  obtain ⟨-, -, hdec, hcomm, hext, hmem, -, -⟩ := uaFacts L n
  have hN : (finU (E := L) (n := n)).Normal := ⟨fun x hx g => (hmem _).1.2 fun τ => by
    simp [((hmem x).1.1 hx) τ]⟩
  obtain ⟨φ, h1, h2, h3, h4, h5⟩ := core (finU (E := L) (n := n)) (infU L n) (ratU L n) U (infC L n) R hdec hcomm
    (fun x hx hx' => hext x 1 (fun w => by simpa using (hmem x).2.1 hx' w)
      (fun τ => by simpa using (hmem x).1.1 hx τ))
    (fun x hx => by
      funext v
      exact (hmem x).1.1 hx v.embedding)
    hU Φ hL hV
  exact ⟨φ, ⟨h1, h2, h3⟩, h4, h5⟩

end
end

section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So

section SlopeTestRemainingChoices

variable {G : Type} [Group G]

private theorem dc_left (U : Subgroup G) (a : G) {u : G} (hu : u ∈ U) (y : G) :
    u * y ∈ DC U a ↔ y ∈ DC U a := by
  constructor
  · rintro ⟨v, hv, w, hw, h⟩
    refine ⟨u⁻¹ * v, U.mul_mem (U.inv_mem hu) hv, w, hw, ?_⟩
    rw [mul_assoc u⁻¹ v a, mul_assoc u⁻¹, ← h]
    group
  · rintro ⟨v, hv, w, hw, rfl⟩
    exact ⟨u * v, U.mul_mem hu hv, w, hw, by group⟩

private theorem dc_right (U : Subgroup G) (a : G) {u : G} (hu : u ∈ U) (y : G) :
    y * u ∈ DC U a ↔ y ∈ DC U a := by
  constructor
  · rintro ⟨b, hb, c, hc, h⟩
    exact ⟨b, hb, c * u⁻¹, U.mul_mem hc (U.inv_mem hu), by
      rw [← mul_assoc, ← h]; group⟩
  · rintro ⟨b, hb, c, hc, rfl⟩
    exact ⟨b, hb, c * u, U.mul_mem hc hu, by group⟩

private theorem out_orbit (U : Subgroup G) (a : G) (x : G ⧸ U) (h : x.out ∈ DC U a) :
    x ∈ MulAction.orbit U (a : G ⧸ U) := by
  obtain ⟨v, hv, w, hw, h⟩ := h
  refine ⟨⟨v, hv⟩, ?_⟩
  rw [← QuotientGroup.out_eq' x, h]
  show (v : G) • ((a : G ⧸ U)) = QuotientGroup.mk (v * a * w)
  rw [QuotientGroup.mk_mul_of_mem _ hw]
  rfl

private theorem one_neg {p : Prop} (h : ¬p) : one p = 0 := by
  classical
  simp [one, h]

end SlopeTestRemainingChoices

end UpperTheory.V.Z.Sym.So

theorem UpperTheory.V.Z.Sym.So.opDc :
    UpperTheory.V.Z.Sym.So.OpDc := by
  intro Γ G V _ _ _ _ B hω g hfin
  have hω1 : ∀ u : B.U, (B.ω u : ℂ) = 1 := by
    intro u
    rw [hω]
    rfl
  have htest : (Base.Tw.one B).IsTest fun y ↦ one (y ∈ DC B.U g) := by
    refine ⟨?_, ?_, ?_⟩
    · intro u y
      simp only [hω, MonoidHom.one_apply, inv_one, Units.val_one, one_mul]
      show one (↑u * y ∈ DC B.U g) = one (y ∈ DC B.U g)
      rw [dc_left B.U g u.2 y]
    · intro u y
      simp only [hω, MonoidHom.one_apply, inv_one, Units.val_one, one_mul]
      show one (y * ↑u ∈ DC B.U g) = one (y ∈ DC B.U g)
      rw [dc_right B.U g u.2 y]
    · refine Set.Finite.subset hfin ?_
      intro x hx
      apply out_orbit B.U g x
      by_contra h
      exact hx (one_neg h)
  refine ⟨htest, ?_⟩
  intro φ
  rw [Tf.rSpec Γ G V B _ _ htest φ]
  funext y
  have hinv : ∀ u ∈ B.U, ∀ z : G, (φ : G → V) (z * u) = (φ : G → V) z := by
    intro u hu z
    rw [φ.2.2 z ⟨u, hu⟩, hω1, one_smul]
  rw [(dcBasic G V B.U g hfin φ hinv).2.1 y]
  show ∑ᶠ x : G ⧸ B.U, one (x.out ∈ DC B.U g) • (φ : G → V) (y * x.out) = _
  refine finsum_congr ?_
  intro x
  by_cases h : x.out ∈ DC B.U g
  · simp [one, h]
  · simp [one, h]

end
end

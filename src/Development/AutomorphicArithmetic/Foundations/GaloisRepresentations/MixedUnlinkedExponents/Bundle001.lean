module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.ValsExtOf
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.EmbedsLevelZeroDepthZero
import Formalism.DoubleCosetMeasures.Statement
import GroundTheory.GlobalFields.KummerTheory.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CycCOfCyclic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
open UpperTheory.Gal.GamX

private theorem map_eq_of_injOn {α β : Type*} (S : Set α) (g : α → β) (hg : Set.InjOn g S)
    (A B : Multiset α) (hA : ∀ x ∈ A, x ∈ S) (hB : ∀ x ∈ B, x ∈ S)
    (h : A.map g = B.map g) : A = B := by
  have key : ∀ C : Multiset α, (∀ x ∈ C, x ∈ S) → ∀ ξ ∈ S, C.count ξ = (C.map g).count (g ξ) := by
    intro C hC ξ hξ
    rw [Multiset.count_map, Multiset.count_eq_card_filter_eq]
    congr 1
    apply Multiset.filter_congr
    intro x hx
    exact ⟨fun e => congrArg g e, fun e => hg hξ (hC x hx) e⟩
  ext ξ
  by_cases hξ : ξ ∈ S
  · rw [key A hA ξ hξ, key B hB ξ hξ, h]
  · rw [Multiset.count_eq_zero_of_notMem (fun m => hξ (hA _ m)),
      Multiset.count_eq_zero_of_notMem (fun m => hξ (hB _ m))]

theorem UpperTheory.Gal.GamX.valsExtOf :
    UpperTheory.Gal.GamX.ValsExtOf := by
  unfold ValsExtOf ValsExt
  intro hP k _ _ _ _ c c' θ h
  have hinj : Set.InjOn (fun ξ : kˣ →* ℂˣ => (ξ * θ) (unif k)) {ξ | IsUnram (ξ * θ)} := by
    intro ξ hξ ξ' hξ' e
    have hu : IsUnram ((ξ * θ) * (ξ' * θ)⁻¹) := isUnram_mul hξ (isUnram_inv hξ')
    exact mul_right_cancel ((hP k).2.1 _ _ hu e)
  exact map_eq_of_injOn _ _ hinj _ _ (fun x hx => (Multiset.mem_filter.1 hx).2)
    (fun x hx => (Multiset.mem_filter.1 hx).2) h
end

section

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
open UpperTheory.Gal.GamX

private theorem lp_zero' : UpperTheory.Gal.GamX.lp (0 : Multiset ℂˣ) = 1 := by
  simp [UpperTheory.Gal.GamX.lp]

private theorem lp_cons' (a : ℂˣ) (A : Multiset ℂˣ) :
    UpperTheory.Gal.GamX.lp (a ::ₘ A) = (1 - Polynomial.C (a : ℂ) * Polynomial.X) * UpperTheory.Gal.GamX.lp A := by
  simp [UpperTheory.Gal.GamX.lp]

private theorem lp_eval_zero (A : Multiset ℂˣ) : (UpperTheory.Gal.GamX.lp A).eval 0 = 1 := by
  induction A using Multiset.induction_on with
  | empty => simp [lp_zero']
  | cons a A ih => rw [lp_cons', Polynomial.eval_mul, ih]; simp

private theorem lp_ne_zero (A : Multiset ℂˣ) : UpperTheory.Gal.GamX.lp A ≠ 0 := by
  intro h
  have h1 := lp_eval_zero A
  rw [h] at h1
  simp at h1

private theorem lin_eq (a : ℂˣ) :
    (1 - Polynomial.C (a : ℂ) * Polynomial.X : ℂ[X]) =
      Polynomial.C (-(a : ℂ)) * (Polynomial.X - Polynomial.C ((a⁻¹ : ℂˣ) : ℂ)) := by
  have ha : (a : ℂ) ≠ 0 := a.ne_zero
  rw [Units.val_inv_eq_inv_val, mul_sub, ← Polynomial.C_mul, neg_mul, mul_inv_cancel₀ ha,
    Polynomial.C_neg, Polynomial.C_neg, Polynomial.C_1]
  ring

private theorem lin_roots (a : ℂˣ) :
    (1 - Polynomial.C (a : ℂ) * Polynomial.X : ℂ[X]).roots = {((a⁻¹ : ℂˣ) : ℂ)} := by
  rw [lin_eq, Polynomial.roots_C_mul _ (by simp), Polynomial.roots_X_sub_C]

private theorem lp_roots (A : Multiset ℂˣ) :
    (UpperTheory.Gal.GamX.lp A).roots = A.map (fun a => ((a⁻¹ : ℂˣ) : ℂ)) := by
  induction A using Multiset.induction_on with
  | empty => simp [lp_zero']
  | cons a A ih =>
    rw [lp_cons', Polynomial.roots_mul (by rw [← lp_cons']; exact lp_ne_zero _), lin_roots, ih,
      Multiset.map_cons, Multiset.singleton_add]

theorem UpperTheory.Gal.GamX.lpInj :
    UpperTheory.Gal.GamX.LpInj := by
  intro A B h
  have h1 := congrArg Polynomial.roots h
  rw [lp_roots, lp_roots] at h1
  exact Multiset.map_injective (fun a b hab => inv_injective (Units.ext hab)) h1
end

section

noncomputable section

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.Gal.GamX

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem opt_ofChar (ξ : kˣ →* ℂˣ) (hξ) :
    (if h : ∃ ξ' : kˣ →* ℂˣ, ∃ hξ', (IrrGL.ofChar ξ hξ : IrrGL (k := k)) = IrrGL.ofChar ξ' hξ' then some h.choose else none)
      = some ξ := by
  have h : ∃ ξ' : kˣ →* ℂˣ, ∃ hξ', (IrrGL.ofChar ξ hξ : IrrGL (k := k)) = IrrGL.ofChar ξ' hξ' := ⟨ξ, hξ, rfl⟩
  rw [dite_eq_left h]
  obtain ⟨_, h2⟩ := h.choose_spec
  exact congrArg some (IrrGL.ofChar_inj.1 h2).symm

private theorem chs_cons_ofChar (ξ : kˣ →* ℂˣ) (hξ) (s : Multiset (IrrGL (k := k))) :
    chs (IrrGL.ofChar ξ hξ ::ₘ s) = ξ ::ₘ chs s :=
  Multiset.filterMap_cons_some _ _ _ (opt_ofChar ξ hξ)

private theorem chs_cons_none {y : IrrGL (k := k)} (hy : ¬ ∃ ξ : kˣ →* ℂˣ, ∃ hξ, y = IrrGL.ofChar ξ hξ)
    (s : Multiset (IrrGL (k := k))) : chs (y ::ₘ s) = chs s :=
  Multiset.filterMap_cons_none _ _ (dif_neg hy)

private theorem mem_chs_iff (s : Multiset (IrrGL (k := k))) (ξ : kˣ →* ℂˣ) :
    ξ ∈ chs s ↔ ∃ hξ, IrrGL.ofChar ξ hξ ∈ s := by
  unfold chs
  rw [Multiset.mem_filterMap]
  constructor
  · rintro ⟨y, hy, e⟩
    by_cases h : ∃ ξ : kˣ →* ℂˣ, ∃ hξ, y = IrrGL.ofChar ξ hξ
    · obtain ⟨ξ', hξ', rfl⟩ := h
      rw [opt_ofChar] at e
      obtain rfl := Option.some.inj e
      exact ⟨hξ', hy⟩
    · rw [dif_neg h] at e
      cases e
  · rintro ⟨hξ, h⟩
    exact ⟨_, h, opt_ofChar ξ hξ⟩

private theorem pol_cons (y : IrrGL (k := k)) (s : Multiset (IrrGL (k := k))) (θ : kˣ →* ℂˣ) :
    pol (y ::ₘ s) θ = (if h : ∃ ξ : kˣ →* ℂˣ, (∃ hξ, y = IrrGL.ofChar ξ hξ) ∧ IsUnram (ξ * θ) then
      1 - C (((h.choose * θ) (unif k) : ℂˣ) : ℂ) * X else 1) * pol s θ := by
  unfold pol
  rw [Multiset.map_cons, Multiset.prod_cons]

private theorem lp_cons (a : ℂˣ) (A : Multiset ℂˣ) : lp (a ::ₘ A) = (1 - C ((a : ℂˣ) : ℂ) * X) * lp A := by
  unfold lp
  rw [Multiset.map_cons, Multiset.prod_cons]

private theorem pol_eq_lp (s : Multiset (IrrGL (k := k))) (θ : kˣ →* ℂˣ) : pol s θ = lp (vals (chs s) θ) := by
  induction s using Multiset.induction with
  | empty => simp [pol, lp, vals, chs_zero]
  | cons y s ih =>
    rw [pol_cons, ih]
    by_cases hy : ∃ ξ : kˣ →* ℂˣ, ∃ hξ, y = IrrGL.ofChar ξ hξ
    · obtain ⟨ξ, hξ, rfl⟩ := hy
      rw [chs_cons_ofChar]
      by_cases hu : IsUnram (ξ * θ)
      · have h : ∃ ξ' : kˣ →* ℂˣ, (∃ hξ', (IrrGL.ofChar ξ hξ : IrrGL (k := k)) = IrrGL.ofChar ξ' hξ') ∧ IsUnram (ξ' * θ) :=
          ⟨ξ, ⟨hξ, rfl⟩, hu⟩
        rw [dite_eq_left h]
        obtain ⟨⟨_, h2⟩, _⟩ := h.choose_spec
        have e : h.choose = ξ := (IrrGL.ofChar_inj.1 h2).symm
        rw [e]
        unfold vals
        rw [Multiset.filter_cons_of_pos (p := fun ξ => IsUnram (ξ * θ)) _ hu, Multiset.map_cons, lp_cons]
      · have h : ¬ ∃ ξ' : kˣ →* ℂˣ, (∃ hξ', (IrrGL.ofChar ξ hξ : IrrGL (k := k)) = IrrGL.ofChar ξ' hξ') ∧ IsUnram (ξ' * θ) := by
          rintro ⟨ξ', ⟨_, h2⟩, h3⟩
          obtain rfl := IrrGL.ofChar_inj.1 h2
          exact hu h3
        rw [dif_neg h, one_mul]
        unfold vals
        rw [Multiset.filter_cons_of_neg (p := fun ξ => IsUnram (ξ * θ)) _ hu]
    · have h : ¬ ∃ ξ : kˣ →* ℂˣ, (∃ hξ, y = IrrGL.ofChar ξ hξ) ∧ IsUnram (ξ * θ) := by
        rintro ⟨ξ, h2, _⟩
        exact hy ⟨ξ, h2⟩
      rw [dif_neg h, one_mul, chs_cons_none hy]

end Loc

theorem chsFacts : ChsFacts := by
  unfold ChsFacts
  intro k _ _ _ _ s
  refine ⟨fun ξ => ?_, fun ξ hξ => ?_, fun θ => pol_eq_lp s θ⟩
  · rw [mem_chs_iff]
    rfl
  · obtain ⟨h, _⟩ := (mem_chs_iff s ξ).1 hξ
    exact h

end UpperTheory.Gal.GamX
end
end

section

noncomputable section

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.Gal.GamX

theorem gamOneOf : GamOneOf := by
  unfold GamOneOf GamOne
  intro hC hV hS K L _ _ _ _ _ _ _ _ hp n hn π P hW v w hw s s' hs hs'
  have hsub : Subsingleton (PlacesOver L v) := ⟨fun a b => (hw a).trans (hw b).symm⟩
  have key : ∀ (u : PlacesOver L v) (h : w = u), SuppAt P u.1 (h ▸ s') := by
    rintro u rfl
    exact hs'
  have hval : ∀ θ : (v.adicCompletion K)ˣ →* ℂˣ, IsSmoothChar θ →
      vals (chs s') (θ.comp (nm w)) = vals (up w s) (θ.comp (nm w)) := by
    intro θ hθ
    have h := hS K L hp n hn π P hW v s (fun u => (hw u).symm ▸ s') hs
      (fun u => key u (hw u).symm) θ hθ
    rw [Fintype.sum_subsingleton _ w, Fintype.sum_subsingleton _ w] at h
    exact h
  refine Multiset.ext.2 fun ζ => ?_
  by_cases hT : Thru w ζ
  · obtain ⟨χ, hχ, hu⟩ := id hT
    have hf := hV (w.1.adicCompletion L) (chs s') (up w s) (χ.comp (nm w)) (hval χ hχ)
    have hc := congrArg (Multiset.count ζ) hf
    rw [Multiset.count_filter_of_pos (p := fun ξ => IsUnram (ξ * χ.comp (nm w))) hu,
      Multiset.count_filter_of_pos (p := fun ξ => IsUnram (ξ * χ.comp (nm w))) hu] at hc
    rw [Multiset.count_filter_of_pos hT]
    exact hc
  · rw [Multiset.count_filter_of_neg hT, eq_comm, Multiset.count_eq_zero]
    intro hm
    obtain ⟨ξ, hξ, rfl⟩ := Multiset.mem_map.1 hm
    exact hT ⟨ξ⁻¹, ((hC _ s).2.1 ξ hξ).inv, fun x _ => by simp⟩

end UpperTheory.Gal.GamX
end
end

section

noncomputable section

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.Gal.GamX

private theorem lp_zero : lp 0 = 1 := by simp [lp]

private theorem lp_add (A B : Multiset ℂˣ) : lp (A + B) = lp A * lp B := by simp [lp]

private theorem lp_sum {ι : Type} (t : Finset ι) (A : ι → Multiset ℂˣ) :
    lp (∑ i ∈ t, A i) = ∏ i ∈ t, lp (A i) := by
  induction t using Finset.induction_on with
  | empty => simp [lp_zero]
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, lp_add, ih]

private theorem loc_pow_apply {E : Type} [Field E] [NumberField E] (χ : HChar E) (a : ℕ) (v x) :
    (χ ^ a).loc v x = χ.loc v x ^ a := by
  change (χ ^ a).1 _ = _
  rw [SubgroupClass.coe_pow, MonoidHom.pow_apply]
  rfl

theorem gamSumOf : GamSumOf := by
  unfold GamSumOf GamSum
  intro hM hN hV hP hC hF hT K L _ _ _ _ _ _ _ _ hp n hn π P hW v s s' hs hs' θ hθ
  obtain ⟨η, h1, h2⟩ := hN K L hp
  obtain ⟨⟨w₀⟩, hf⟩ := hF K L v
  have hfw : ∀ w : PlacesOver L v, fdeg w = fdeg w₀ := fun w => hf w w₀
  have hf0 : 0 < fdeg w₀ := (hV K L v w₀ 1).2.2.1
  have he : ∀ (j : ℕ) (w : PlacesOver L v), ((η ^ j).loc v).comp (nm w) = 1 := by
    intro j w
    refine MonoidHom.ext fun x => ?_
    have hx := DFunLike.congr_fun (h2 v w).1 x
    simp only [MonoidHom.comp_apply, MonoidHom.one_apply] at hx ⊢
    rw [loc_pow_apply, hx, one_pow]
  have hm := hM K L hp n hn π P hW η h1 v s s' hs hs' θ hθ
  have hlp : lp (∑ j ∈ Finset.range (Module.finrank K L), vals (chs s) (θ * (η ^ j).loc v)) =
      (lp (∑ w, vals (chs (s' w)) (θ.comp (nm w)))).comp (X ^ fdeg w₀) := by
    rw [lp_sum, lp_sum, Polynomial.prod_comp]
    simp only [← (hC _ _).2.2]
    rw [hm]
    exact Finset.prod_congr rfl fun w _ => by rw [hfw w]
  have h3 := hP (fdeg w₀) hf0 _ _ hlp
  have h4 := hT K L v (Module.finrank K L) (fdeg w₀) (fun j => (η ^ j).loc v) hfw ⟨w₀⟩ he
    (fun w w' μ h => (h2 v w).2.1 w' μ h) (fun w μ hμ h => ((h2 v w).2.2 μ hμ).2.2 h)
    (chs s) (hC _ s).2.1 θ hθ
  have h5 := h3.symm.trans h4
  refine Multiset.ext.2 fun a => ?_
  have h6 := congrArg (Multiset.count a) h5
  rw [Multiset.count_nsmul, Multiset.count_nsmul] at h6
  exact Nat.eq_of_mul_eq_mul_left hf0 h6

end UpperTheory.Gal.GamX
end
end

section

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
open UpperTheory.Gal.GamX


theorem UpperTheory.Gal.GamX.twValsOf :
    UpperTheory.Gal.GamX.TwValsOf := by
  intro hNV K L _ _ _ _ _ v d f e hf hne he hA hB c hc θ hθ
  unfold UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.NormVal at hNV
  have hv1 : ∀ {k : Type} [Field k] [ValuativeRel k] (a t : kˣ →* ℂˣ),
      vals {a} t = if IsUnram (a * t) then {(a * t) (unif k)} else 0 := by
    intro k _ _ a t
    unfold vals
    rw [Multiset.filter_singleton]
    split_ifs <;> simp
  have hadd : ∀ {k : Type} [Field k] [ValuativeRel k] (c1 c2 : Multiset (kˣ →* ℂˣ)) (t : kˣ →* ℂˣ),
      vals (c1 + c2) t = vals c1 t + vals c2 t := by
    intro k _ _ c1 c2 t
    simp only [vals, Multiset.filter_add, Multiset.map_add (f := _)]
  induction c using Multiset.induction_on with
  | empty => simp [vals]
  | cons a c ih =>
    have hca : IsSmoothChar a := hc a (Multiset.mem_cons_self a c)
    have ih' := ih (fun ξ h => hc ξ (Multiset.mem_cons_of_mem h))
    have hone : Multiset.map (fun x => x ^ f) (∑ j ∈ Finset.range d, vals {a} (θ * e j)) =
        f • ∑ w : PlacesOver L v, vals (Multiset.map (fun ξ => ξ.comp (nm w)) {a}) (θ.comp (nm w)) := by
      simp only [Multiset.map_singleton, hv1, ← mul_assoc, ← MonoidHom.mul_comp]
      set μ := a * θ with hμ
      have hμs : IsSmoothChar μ := by
        unfold IsSmoothChar at hca hθ ⊢
        have hle : a.ker ⊓ θ.ker ≤ μ.ker := by
          intro x hx
          rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at hx
          rw [MonoidHom.mem_ker, hμ, MonoidHom.mul_apply, hx.1, hx.2, mul_one]
        exact Subgroup.isOpen_mono hle (by rw [Subgroup.coe_inf]; exact hca.inter hθ)
      have hcomp : ∀ j (w : PlacesOver L v), (μ * e j).comp (nm w) = μ.comp (nm w) := by
        intro j w
        rw [MonoidHom.mul_comp, he j w, mul_one]
      by_cases hex : ∃ w : PlacesOver L v, IsUnram (μ.comp (nm w))
      · obtain ⟨w1, hw1⟩ := hex
        have hall : ∀ w : PlacesOver L v, IsUnram (μ.comp (nm w)) := fun w => hA w1 w μ hw1
        have hcard := hB w1 μ hμs hw1
        have hsumf : ∑ w' : PlacesOver L v, fdeg w' = Fintype.card (PlacesOver L v) * f := by
          simp only [hf, Finset.sum_const, Finset.card_univ, smul_eq_mul]
        have hfpos : 0 < f := by
          have := (hNV K L v w1 μ).2.2.1
          rwa [hf w1] at this
        have hval : ∀ j, IsUnram (μ * e j) → ∀ w : PlacesOver L v,
            μ ((nm w) (unif (HeightOneSpectrum.adicCompletion L (w : HeightOneSpectrum (𝓞 L))))) =
              (μ * e j) (unif (HeightOneSpectrum.adicCompletion K v)) ^ f := by
          intro j hj w
          have h1 := ((hNV K L v w (μ * e j)).1 hj).2
          have h2 : (e j) ((nm w) (unif (HeightOneSpectrum.adicCompletion L
              (w : HeightOneSpectrum (𝓞 L))))) = 1 := by
            have := congrArg (fun φ => φ (unif (HeightOneSpectrum.adicCompletion L
              (w : HeightOneSpectrum (𝓞 L))))) (he j w)
            simpa using this
          rw [MonoidHom.mul_apply, h2, mul_one, hf w] at h1
          exact h1
        have hpos : 0 < (Finset.filter (fun j => IsUnram (μ * e j)) (Finset.range d)).card := by
          rw [hcard, hsumf]
          exact Nat.mul_pos (Fintype.card_pos_iff.mpr hne) hfpos
        obtain ⟨j0, hj0⟩ := Finset.card_pos.mp hpos
        rw [Finset.mem_filter] at hj0
        refine Eq.trans ((Multiset.eq_replicate (n := Fintype.card (PlacesOver L v) * f)
          (a := (μ * e j0) (unif (HeightOneSpectrum.adicCompletion K v)) ^ f)).mpr ⟨?_, ?_⟩)
          ((Multiset.eq_replicate).mpr ⟨?_, ?_⟩).symm
        · rw [Multiset.card_map, Multiset.card_sum, ← hsumf, ← hcard, Finset.card_filter]
          refine Finset.sum_congr rfl fun j _ => ?_
          split_ifs <;> simp
        · intro b hb
          rw [Multiset.mem_map] at hb
          obtain ⟨x, hx, rfl⟩ := hb
          rw [Multiset.mem_sum] at hx
          obtain ⟨j, -, hxj⟩ := hx
          split_ifs at hxj with hj
          · rw [Multiset.mem_singleton] at hxj
            subst hxj
            rw [← hval j hj w1, hval j0 hj0.2 w1]
          · simp at hxj
        · simp only [hall, ↓reduceIte]
          rw [Multiset.card_nsmul, Multiset.card_sum]
          simp [mul_comm]
        · intro b hb
          simp only [hall, ↓reduceIte] at hb
          have hb' := Multiset.mem_of_mem_nsmul hb
          rw [Multiset.mem_sum] at hb'
          obtain ⟨w, -, hbw⟩ := hb'
          rw [Multiset.mem_singleton] at hbw
          rw [hbw, MonoidHom.comp_apply]
          exact hval j0 hj0.2 w
      · push_neg at hex
        have hno : ∀ j, ¬ IsUnram (μ * e j) := by
          intro j hj
          obtain ⟨w0⟩ := hne
          have := ((hNV K L v w0 (μ * e j)).1 hj).1
          rw [hcomp] at this
          exact hex w0 this
        simp [hno, hex]
    rw [← Multiset.singleton_add]
    simp only [hadd, Multiset.map_add (f := _), Finset.sum_add_distrib, smul_add]
    rw [hone, ih']
end

section

noncomputable section

open NumberField IsDedekindDomain
open GroundTheory.Global.SemiLocal UpperTheory.V.Z.Gam

namespace UpperTheory.Gal.GamX

theorem fdegEq : FdegEq := by
  intro K L _ _ _ _ _ _ v
  refine ⟨GroundTheory.Global.nonempty_placesOver L v, fun w w' => ?_⟩
  have hw := w.2
  have hw' := w'.2
  unfold fdeg
  rw [Ideal.inertiaDeg'_eq_inertiaDeg v.asIdeal w.1.asIdeal,
    Ideal.inertiaDeg'_eq_inertiaDeg v.asIdeal w'.1.asIdeal]
  exact Ideal.inertiaDeg_eq_of_isGaloisGroup v.asIdeal w.1.asIdeal w'.1.asIdeal Gal(L/K)

end UpperTheory.Gal.GamX
end
end

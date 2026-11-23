module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.Bundle004
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle020
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle041
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle035
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.PrimitiveClassFunctionExpansionRootSums
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle019
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
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchCut

@[expose] public section

section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open GlobalTheory.CuspGL GlobalTheory.BI
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem pow_mod_modEq (q m : ℕ) (hq : 0 < q) (hm : 0 < m) (e : ℕ) :
    q ^ e ≡ q ^ (e % m) [MOD q ^ m - 1] := by
  have h1 : q ^ m ≡ 1 [MOD q ^ m - 1] := Nat.modEq_sub (Nat.one_le_pow _ _ hq)
  conv_lhs => rw [← Nat.div_add_mod e m, pow_add, pow_mul]
  calc (q ^ m) ^ (e / m) * q ^ (e % m) ≡ 1 ^ (e / m) * q ^ (e % m) [MOD q ^ m - 1] :=
        (h1.pow _).mul_right _
    _ = q ^ (e % m) := by rw [one_pow, one_mul]

private theorem count_le (q m c c' i k : ℕ) (hq : 0 < q) (hm : 0 < m)
    (h : c' ≡ c * q ^ i [MOD q ^ m - 1]) :
    ((Finset.range m).filter fun j => c' * q ^ j ≡ k [MOD q ^ m - 1]).card ≤
      ((Finset.range m).filter fun j => c * q ^ j ≡ k [MOD q ^ m - 1]).card := by
  apply Finset.card_le_card_of_injOn (fun j => (j + i) % m)
  · intro j hj
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hj ⊢
    refine ⟨Nat.mod_lt _ hm, ?_⟩
    calc c * q ^ ((j + i) % m) ≡ c * q ^ (j + i) [MOD q ^ m - 1] :=
          ((pow_mod_modEq q m hq hm (j + i)).symm).mul_left _
      _ = c * q ^ i * q ^ j := by ring
      _ ≡ c' * q ^ j [MOD q ^ m - 1] := h.symm.mul_right _
      _ ≡ k [MOD q ^ m - 1] := hj.2
  · intro a ha b hb hab
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at ha hb
    have h' : a ≡ b [MOD m] := Nat.ModEq.add_right_cancel' i hab
    unfold Nat.ModEq at h'
    rwa [Nat.mod_eq_of_lt ha.1, Nat.mod_eq_of_lt hb.1] at h'

private theorem count_eq (q m c c' i k : ℕ) (hq : 0 < q) (hm : 0 < m)
    (h : c' ≡ c * q ^ i [MOD q ^ m - 1]) :
    ((Finset.range m).filter fun j => c' * q ^ j ≡ k [MOD q ^ m - 1]).card =
      ((Finset.range m).filter fun j => c * q ^ j ≡ k [MOD q ^ m - 1]).card := by
  apply le_antisymm (count_le q m c c' i k hq hm h)
  apply count_le q m c' c (m - i % m) k hq hm
  have hr : i % m < m := Nat.mod_lt _ hm
  have hd : m * (i / m) + i % m = i := Nat.div_add_mod i m
  have hs : i + (m - i % m) = m * (i / m + 1) := by
    rw [mul_add, mul_one]
    omega
  calc c = c * q ^ ((i + (m - i % m)) % m) := by rw [hs, Nat.mul_mod_right, pow_zero, mul_one]
    _ ≡ c * q ^ (i + (m - i % m)) [MOD q ^ m - 1] :=
        ((pow_mod_modEq q m hq hm _).symm).mul_left _
    _ = c * q ^ i * q ^ (m - i % m) := by ring
    _ ≡ c' * q ^ (m - i % m) [MOD q ^ m - 1] := h.symm.mul_right _

private theorem psi_eq (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y)
    (hn : 0 < Module.finrank F V) (c c' i : ℕ)
    (h : c' ≡ c * Nat.card F ^ i [MOD Nat.card F ^ Module.finrank F V - 1])
    (g : Module.End F V) (hg : IsUnit g) :
    psi (rootSum θ c') V g = psi (rootSum θ c) V g := by
  have hcl : ∀ s : F[X] → ℂ, IsAdditive s →
      IsClassFn (psi s V) ∧ GlobalTheory.CuspGL.IsPrimitive (psi s V) := fun s hs =>
    ⟨fun e x => GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_linearEquiv_conj F s V V e x, GlobalTheory.T.isPrimitiveEndClassFunction_invariantSubspaceMobiusInverse F V s hs⟩
  have hc := hcl _ (GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow F θ c).1
  have hc' := hcl _ (GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow F θ c').1
  have e1 := GlobalTheory.T.primitiveClassFunction_expansion_rootSums F V θ hθ _ hc'.1 hc'.2 hn g hg
  have e2 := GlobalTheory.T.primitiveClassFunction_expansion_rootSums F V θ hθ _ hc.1 hc.2 hn g hg
  have hsum : (∑ k ∈ Finset.range (Nat.card F ^ Module.finrank F V - 1),
      (ipGL (psi (rootSum θ c') V) fun x ↦ rootSum θ k (LinearMap.charpoly x)) *
        psi (rootSum θ k) V g) =
      ∑ k ∈ Finset.range (Nat.card F ^ Module.finrank F V - 1),
      (ipGL (psi (rootSum θ c) V) fun x ↦ rootSum θ k (LinearMap.charpoly x)) *
        psi (rootSum θ k) V g := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [GlobalTheory.T.invertibleEndInnerProduct_rootPowerSum_mobius F V θ hθ hn, GlobalTheory.T.invertibleEndInnerProduct_rootPowerSum_mobius F V θ hθ hn,
      count_eq (Nat.card F) (Module.finrank F V) c c' i k Nat.card_pos hn h]
  have hne : glCard F (Module.finrank F V) * (Module.finrank F V : ℂ) ≠ 0 := by
    refine mul_ne_zero ?_ (Nat.cast_ne_zero.mpr hn.ne')
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  exact mul_left_cancel₀ hne (e1.trans (hsum.trans e2.symm))

theorem UpperTheory.Gal.InertialTypesAlt.cuspFrob :
    CuspFrob := by
  intro F _ _ θ hθ m c c' i hm h
  funext x
  simp only [GlobalTheory.Shin.cusp, GlobalTheory.Shin.psiG]
  congr 1
  have hr : Module.finrank F (Fin m → F) = m := Module.finrank_fin_fun F
  refine psi_eq F (Fin m → F) θ hθ (by rw [hr]; exact hm) c c' i (by rw [hr]; exact h) _ ?_
  exact x.isUnit.map
    (Matrix.toLinAlgEquiv' : Matrix (Fin m) (Fin m) F ≃ₐ[F] Module.End F (Fin m → F))
end

section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem inj_comp {F R : Type} [Field F] [Field R] (Θ : R →* ℂ) (hΘ : Inj Θ) (e : F →+* R) :
    Inj (Θ.comp e.toMonoidHom) := by
  intro x y hx hy hxy
  have hx' : e x ≠ 0 := by simpa using hx
  have hy' : e y ≠ 0 := by simpa using hy
  exact e.injective (hΘ _ _ hx' hy' hxy)

private theorem cast_eq_of_pow {k : Type} [Field k] [Finite k] (θ : AlgebraicClosure k →* ℂ) (hθ : Inj θ)
    (c c' : ℕ) (h : ∀ u : kˣ, θ (algebraMap k _ (u : k)) ^ c = θ (algebraMap k _ (u : k)) ^ c') :
    ((c : ℕ) : ZMod (Nat.card k - 1)) = ((c' : ℕ) : ZMod (Nat.card k - 1)) := by
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := kˣ)
  have hord : orderOf ζ = Nat.card k - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hζ, Nat.card_units]
  have hz : algebraMap k (AlgebraicClosure k) (ζ : k) ≠ 0 := by simp
  have h1 : θ (algebraMap k (AlgebraicClosure k) (ζ : k) ^ c) = θ (algebraMap k (AlgebraicClosure k) (ζ : k) ^ c') := by
    rw [map_pow θ, map_pow θ]; exact h ζ
  have h2 := hθ _ _ (pow_ne_zero _ hz) (pow_ne_zero _ hz) h1
  have h3 : ζ ^ c = ζ ^ c' := by
    apply Units.ext
    apply (algebraMap k (AlgebraicClosure k)).injective
    simpa using h2
  rw [pow_eq_pow_iff_modEq, hord] at h3
  exact (ZMod.natCast_eq_natCast_iff _ _ _).2 h3

theorem UpperTheory.Gal.InertialTypesAlt.mixType :
    (LblOn fun _ => True) → LblMixed → SepOf → LeTop → PolTop → TypeOfLbl → ResEmbEx → BaseQ → CardRes → MixType := by
  intro hOn hMix hSep hTop hPol hType hEmb hBase hCard E Ω _ _ _ _ _ _ n hn π Y hY A v w h h' g _ i hi hI τ τ' hτ hτ' hM f hf hs
  obtain ⟨⟨e, he⟩, Θ, hΘ⟩ := hEmb E Ω A v h
  obtain ⟨⟨e', he'⟩, -⟩ := hEmb Y.K Ω A w h'
  obtain ⟨a, s, ha, hApart, hS, hL⟩ := hMix E Ω A v h g i hi (Θ.comp e.toMonoidHom) (inj_comp Θ hΘ e) n τ hM
  obtain ⟨b, hab, hb⟩ := hOn E Ω n hn (Pt.base Ω π) Y hY A Θ hΘ hI v w h h' e e' he he' τ τ' hτ hτ' a trivial ha
  have hag : a.q = g := ha.2.1.trans (hBase E v g i hi).2.1
  have hbQ : b.q = g ^ f := by rw [hb.2.1, hCard, hf]
  have hb2 : 2 ≤ b.q := hb.1.1
  have hf0 : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [hbQ, h0] at hb2; simp at hb2
    · exact h0
  have hsp : a.Splits b.q := ⟨f, hf0, by rw [hbQ, hag], fun p hp => by
    obtain ⟨y, hy, hyp⟩ := hL p hp
    rw [← hyp]; exact hs s hS y hy⟩
  obtain ⟨-, -, hL1, hbl⟩ := hTop a b ha.1 hab hsp
  have hsep : b.Sep b.q := by
    have := hSep a b.q ha.1 hApart hsp
    unfold Lbl.Sep at this ⊢
    rwa [hbl]
  obtain ⟨c, d, k, hd, ω, hlist, hω, hT⟩ := hType _ (Θ.comp e'.toMonoidHom) n _ τ'.ρ b hb hL1
  have hbl2 := (hPol b 1 hb2 hL1 (one_pow _)).1
  have hinj : Function.Injective fun x : Fin c => ((k x : ℕ) : ZMod (b.q - 1)) := by
    unfold Lbl.Sep at hsep
    rw [hbl2, hlist.symm] at hsep
    rw [Multiset.map_coe, Multiset.coe_nodup] at hsep
    simp only [List.map_ofFn] at hsep
    exact List.nodup_ofFn.1 hsep
  have : Finite 𝓀[w.adicCompletion Y.K] := Nat.finite_of_card_ne_zero (by rw [← hb.2.1]; omega)
  refine ⟨c, d, hd, ω, ?_, ?_, hT⟩
  · intro x
    have hmem : (d x, k x) ∈ b.D ++ b.L := by
      rw [← hlist]; exact (List.mem_ofFn' _ _).2 ⟨x, rfl⟩
    rcases List.mem_append.1 hmem with hm | hm
    · exact hb.1.2.1 _ hm
    · exact (hb.1.2.2 _ hm).1
  · intro x x' hxx
    apply hinj
    have := cast_eq_of_pow (Θ.comp e'.toMonoidHom) (inj_comp Θ hΘ e') (k x) (k x') (fun u => by
      rw [← hω x u, ← hω x' u, hxx])
    rw [← hb.2.1] at this
    exact this
end

section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.avgMap :
    AvgMap := by
  intro G _ _ H U Z W X _ _ _ _ _ _ _ _ ρ κ η Φ ev ψ hΦ hev hinj hψ hne
  haveI := Fintype.ofFinite G
  refine ⟨∑ g : G, (ρ g⁻¹).comp (Φ.comp (ψ.comp (η g))), ?_, ?_⟩
  · obtain ⟨x, hx⟩ : ∃ x, ψ x ≠ 0 := by
      by_contra h
      push_neg at h
      exact hne (LinearMap.ext h)
    intro h0
    have h1 := congrArg (fun L => ev (L x)) h0

    simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum,
    LinearMap.zero_apply, map_zero] at h1
    have key : ∀ g : G, ev (ρ g⁻¹ (Φ (ψ (η g x)))) = if g ∈ H then ev (Φ (ψ x)) else 0 := by
      intro g
      split_ifs with hg
      · have e1 := hψ ⟨g, hg⟩ x
        have e2 := hΦ ⟨g, hg⟩ (ψ x)
        simp only at e1 e2
        rw [e1, e2, Representation.inv_self_apply]
      · exact hev g⁻¹ (by simpa using hg) _
    rw [Finset.sum_congr rfl (fun g _ => key g), Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const] at h1
    have hc : (Finset.univ.filter (· ∈ H)).card ≠ 0 := by
      rw [← Nat.pos_iff_ne_zero, Finset.card_pos]
      exact ⟨1, by simp [H.one_mem]⟩
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero] at h1
    rcases h1 with h1 | h1
    · exact hc (by exact_mod_cast h1)
    · exact hx (hinj _ h1)
  · intro k x

    simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum]
    refine Fintype.sum_equiv (Equiv.mulRight k) _ _ (fun g => ?_)
    simp only [Equiv.coe_mulRight, map_mul, Module.End.mul_apply, mul_inv_rev,
      Representation.self_inv_apply]
end

section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem count_expand_map (c : ℕ → ℕ) (m k : ℕ) (K : List ℕ) (hK : K.Nodup) :
    (expand (K.map fun j => (c j, j))).count (m, k) = if m = 1 ∧ k ∈ K then c k else 0 := by
  induction K with
  | nil => simp [UpperTheory.Gal.InertialTypesAlt.expand]
  | cons a K ih =>
    rw [List.nodup_cons] at hK
    have ih' := ih hK.2
    simp only [UpperTheory.Gal.InertialTypesAlt.expand, List.map_cons, List.flatMap_cons, List.count_append] at ih' ⊢
    rw [ih', List.count_replicate]
    by_cases hm : m = 1 <;> by_cases hk : k = a <;> simp_all <;> intros <;> subst_vars <;> simp_all

theorem UpperTheory.Gal.InertialTypesAlt.group1 :
    Group1 := by
  intro L₀ hpos
  have hmemK : ∀ k, k ∈ ((L₀.filter fun p => p.1 = 1).map Prod.snd).dedup ↔ (1, k) ∈ L₀ := by
    intro k
    simp only [List.mem_dedup, List.mem_map, List.mem_filter]
    constructor
    · rintro ⟨q, ⟨hq, hq1⟩, rfl⟩
      have hq' : q = (1, q.2) := Prod.ext (by simpa using hq1) rfl
      rw [← hq']
      exact hq
    · intro h
      exact ⟨(1, k), ⟨h, by simp⟩, rfl⟩
  refine ⟨(((L₀.filter fun p => p.1 = 1).map Prod.snd).dedup).map fun j => (L₀.count (1, j), j),
    ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hp
    have h1 : (1, j) ∈ L₀ := (hmemK j).1 hj
    exact ⟨List.count_pos_iff.2 h1, h1⟩
  · rw [List.map_map]
    simpa [Function.comp_def] using List.nodup_dedup ((L₀.filter fun p => p.1 = 1).map Prod.snd)
  · rw [List.perm_iff_count]
    rintro ⟨m, k⟩
    rw [List.count_append, count_expand_map _ m k _ (List.nodup_dedup _)]
    rcases Nat.lt_or_ge m 2 with hm | hm
    · have hf : (m, k) ∉ L₀.filter (fun p => decide (2 ≤ p.1)) := by
        simp only [List.mem_filter, decide_eq_true_eq, not_and]
        intro _ h2
        omega
      rw [List.count_eq_zero_of_not_mem hf]
      interval_cases m
      · have h0 : (0, k) ∉ L₀ := fun h => absurd (hpos _ h) (lt_irrefl 0)
        simp [List.count_eq_zero_of_not_mem h0]
      · by_cases h : (1, k) ∈ L₀
        · simp [(hmemK k).2 h]
        · have h' : k ∉ ((L₀.filter fun p => p.1 = 1).map Prod.snd).dedup :=
            fun hk => h ((hmemK k).1 hk)
          simp [h', List.count_eq_zero_of_not_mem h]
    · rw [List.count_filter (by simpa using hm)]
      have hm1 : m ≠ 1 := by omega
      simp [hm1]
end

section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem toG_one' {F : Type} [Field F] (m : ℕ) :
    toG (1 : Matrix (Fin m) (Fin m) F) = 1 := by
  unfold toG
  rw [dite_eq_left isUnit_one]
  exact Units.ext (IsUnit.unit_spec _)

private theorem ent_one' {F : Type} [Field F] {n : ℕ} (i j : ℕ) (hi : i < n) (hj : j < n) :
    ent (1 : Matrix (Fin n) (Fin n) F) i j = if i = j then 1 else 0 := by
  unfold ent
  rw [dite_eq_left ⟨hi, hj⟩, Matrix.one_apply]
  simp only [Fin.mk.injEq]

private theorem tlG_one' {F : Type} [Field F] (a b : ℕ) :
    tlG a (1 : GL (Fin (a + b)) F) = 1 := by
  have h : tl a ((1 : GL (Fin (a + b)) F) : Matrix (Fin (a + b)) (Fin (a + b)) F) = 1 := by
    ext i j
    rw [Matrix.one_apply]
    show ent _ (i : ℕ) (j : ℕ) = _
    rw [Units.val_one, ent_one' _ _ (lt_of_lt_of_le i.isLt (Nat.le_add_right a b))
      (lt_of_lt_of_le j.isLt (Nat.le_add_right a b))]
    simp only [Fin.val_inj]
  unfold tlG
  rw [h, toG_one']

private theorem brG_one' {F : Type} [Field F] (a b : ℕ) :
    brG a b (1 : GL (Fin (a + b)) F) = 1 := by
  have h : br a b ((1 : GL (Fin (a + b)) F) : Matrix (Fin (a + b)) (Fin (a + b)) F) = 1 := by
    ext i j
    rw [Matrix.one_apply]
    show ent _ (a + (i : ℕ)) (a + (j : ℕ)) = _
    rw [Units.val_one, ent_one' _ _ (Nat.add_lt_add_left i.isLt a)
      (Nat.add_lt_add_left j.isLt a)]
    simp only [Nat.add_left_cancel_iff, Fin.val_inj]
  unfold brG
  rw [h, toG_one']

private theorem inPar_one' {F : Type} [Field F] (a n : ℕ) : InPar a (1 : GL (Fin n) F) := by
  intro i j hj hi
  rw [Units.val_one, Matrix.one_apply_ne]
  intro h
  rw [h] at hi
  omega

private theorem gal_id' {F : Type} [Field F] (n : ℕ) (y : GL (Fin n) F) :
    gal (RingHom.id F) n y = y := by
  ext i j
  rfl

theorem UpperTheory.Gal.InertialTypesAlt.hcOne :
    HcOne := by
  intro F _ _ a b n hn α β hα hβ
  subst hn
  unfold hc hcTw
  simp only [gal_id', mul_one, inv_mul_cancel, inPar_one', ite_true, tlG_one', brG_one']
  haveI : Nonempty { p : GL (Fin (a + b)) F // InPar a p } := ⟨⟨1, inPar_one' a _⟩⟩
  haveI : Fintype (GL (Fin (a + b)) F) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, Finset.sum_const, nsmul_eq_mul]
  exact mul_ne_zero (inv_ne_zero (Nat.cast_ne_zero.mpr Nat.card_pos.ne'))
    (mul_ne_zero (Nat.cast_ne_zero.mpr Finset.univ_nonempty.card_pos.ne') (mul_ne_zero hα hβ))
end

section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.InertialTypesAlt

theorem tensInc : TensInc := by
  intro k _ _ _ _ s d V _ _ σ
  refine ⟨PiTensorProduct.map fun a => (fixed (σ a) (KOne k (Fin (d a)))).subtype, ?_, ?_⟩
  · intro u w h
    have hl : ∀ a, ∃ g : V a →ₗ[ℂ] fixed (σ a) (KOne k (Fin (d a))),
        g ∘ₗ (fixed (σ a) (KOne k (Fin (d a)))).subtype = LinearMap.id := fun a =>
      LinearMap.exists_leftInverse_of_injective _ (Submodule.ker_subtype _)
    choose g hg using hl
    have e : PiTensorProduct.map g ∘ₗ
        (PiTensorProduct.map fun a => (fixed (σ a) (KOne k (Fin (d a)))).subtype) = LinearMap.id := by
      rw [← PiTensorProduct.map_comp]
      simp only [hg]
      exact PiTensorProduct.map_id
    have h1 := LinearMap.congr_fun e u
    have h2 := LinearMap.congr_fun e w
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1 h2
    rw [← h1, ← h2, h]
  · intro x z
    have key : ∀ a, (fixed (σ a) (KOne k (Fin (d a)))).subtype ∘ₗ
        levelZero (σ a) (redLevi k (fun a => Fin (d a)) x a) =
          σ a ((x : (a : Fin s) → GL (Fin (d a)) k) a) ∘ₗ (fixed (σ a) (KOne k (Fin (d a)))).subtype :=
      fun a => LinearMap.ext fun v => levelZero_apply (σ a) ⟨_, x.2 a (Set.mem_univ a)⟩ v
    change (PiTensorProduct.map (fun a => (fixed (σ a) (KOne k (Fin (d a)))).subtype) ∘ₗ
        PiTensorProduct.map (fun a => levelZero (σ a) (redLevi k (fun a => Fin (d a)) x a))) z =
      (PiTensorProduct.map (fun a => σ a ((x : (a : Fin s) → GL (Fin (d a)) k) a)) ∘ₗ
        PiTensorProduct.map (fun a => (fixed (σ a) (KOne k (Fin (d a)))).subtype)) z
    rw [← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp]
    simp only [key]

end UpperTheory.Gal.InertialTypesAlt
end
end

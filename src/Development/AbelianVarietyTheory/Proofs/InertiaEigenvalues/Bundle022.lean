module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RepresentationTheory.Character
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
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
public import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

section

namespace GlobalTheory.IsoSep

open Representation

theorem main : ∀ (H V W : Type) [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ H V) (σ : Representation ℂ H W), σ.IsIrreducible → (⨆ f : σ.IntertwiningMap ρ, LinearMap.range f.toLinearMap) = ⊤ → (∀ (W' : Type) [AddCommGroup W'] [Module ℂ W'] (σ' : Representation ℂ H W'), σ'.IsIrreducible → ∀ f' : σ'.IntertwiningMap ρ, f' ≠ 0 → Nonempty (σ.Equiv σ')) → ∀ v : V, v ≠ 0 → ∃ p : ρ.IntertwiningMap σ, p v ≠ 0 := by
  intro H V W _ _ _ _ _ ρ σ hσ hsum hiso v hv
  haveI := hσ
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)

  have hatom : ∀ f : σ.IntertwiningMap ρ, f ≠ 0 → IsAtom f.range := by
    intro f hf
    refine ⟨?_, ?_⟩
    · intro h
      apply hf
      ext w
      have hw : f w ∈ f.range := ⟨w, rfl⟩
      rw [h] at hw
      exact hw
    · intro U hU
      let U' : Subrepresentation σ := ⟨U.toSubmodule.comap f.toLinearMap, fun g w hw => by
        show f (σ g w) ∈ U.toSubmodule
        rw [f.isIntertwining]
        exact U.apply_mem_toSubmodule g hw⟩
      rcases eq_bot_or_eq_top U' with h | h
      · refine le_antisymm (fun x hx => ?_) bot_le
        obtain ⟨w, rfl⟩ := hU.le hx
        have hw : w ∈ U'.toSubmodule := hx
        rw [h] at hw
        have hw0 : w = 0 := (Submodule.mem_bot ℂ).1 hw
        show f w ∈ (⊥ : Submodule ℂ V)
        rw [hw0, map_zero]
        exact zero_mem _
      · exfalso
        refine hU.ne (le_antisymm hU.le ?_)
        rintro _ ⟨w, rfl⟩
        have hw : w ∈ U'.toSubmodule := by rw [h]; trivial
        exact hw

  have hss : IsSemisimpleModule (MonoidAlgebra ℂ H) ρ.asModule := by
    apply IsSemisimpleModule.of_sSup_simples_eq_top
    refine eq_top_iff.2 fun x _ => ?_
    have hx : ρ.asModuleEquiv x ∈ (⨆ f : σ.IntertwiningMap ρ, LinearMap.range f.toLinearMap) := by
      rw [hsum]; trivial
    have key := Submodule.iSup_induction _ (motive := fun y : V => ρ.asModuleEquiv.symm y ∈
      sSup {m : Submodule (MonoidAlgebra ℂ H) ρ.asModule | IsSimpleModule (MonoidAlgebra ℂ H) m}) hx
      (fun f y hy => by
        by_cases hf : f = 0
        · subst hf
          obtain ⟨w, rfl⟩ := hy
          simp
        · refine le_sSup (a := e f.range) ?_ ?_
          · exact isSimpleModule_iff_isAtom.2 ((e.isAtom_iff _).2 (hatom f hf))
          · exact hy)
      (by simp) (fun a b ha hb => by simpa only [map_add] using add_mem ha hb)
    simpa using key

  let K : Submodule (MonoidAlgebra ℂ H) ρ.asModule := Submodule.span _ {ρ.asModuleEquiv.symm v}
  have hK : K ≠ ⊥ := by
    intro h
    apply hv
    have hm : ρ.asModuleEquiv.symm v ∈ K := Submodule.subset_span rfl
    rw [h, Submodule.mem_bot] at hm
    simpa using hm
  obtain ⟨N, hN, hNK⟩ := (eq_bot_or_exists_atom_le K).resolve_left hK
  obtain ⟨C, hC⟩ := exists_isCompl N
  let N' := e.symm N
  let C' := e.symm C
  have hC' : IsCompl N' C' := (e.isCompl_iff).2 (by
    simp only [N', C', OrderIso.apply_symm_apply]; exact hC)
  have hN' : IsAtom N' := (e.isAtom_iff N').1 (by simp only [N', OrderIso.apply_symm_apply]; exact hN)
  have hc : IsCompl N'.toSubmodule C'.toSubmodule := by
    constructor
    · rw [disjoint_iff]; exact congrArg Subrepresentation.toSubmodule hC'.inf_eq_bot
    · rw [codisjoint_iff]; exact congrArg Subrepresentation.toSubmodule hC'.sup_eq_top
  let P := Submodule.projectionOnto N'.toSubmodule C'.toSubmodule hc
  let τ := N'.toRepresentation
  let p : ρ.IntertwiningMap τ := ⟨P, fun g => LinearMap.ext fun x => by
    have hx : x ∈ N'.toSubmodule ⊔ C'.toSubmodule := by rw [hc.sup_eq_top]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    have h1 : P (ρ g y) = ⟨ρ g y, N'.apply_mem_toSubmodule g hy⟩ :=
      Submodule.projectionOnto_apply_left hc ⟨ρ g y, N'.apply_mem_toSubmodule g hy⟩
    have h2 : P (ρ g z) = 0 :=
      Submodule.projectionOnto_apply_right hc ⟨ρ g z, C'.apply_mem_toSubmodule g hz⟩
    have h3 : P y = ⟨y, hy⟩ := Submodule.projectionOnto_apply_left hc ⟨y, hy⟩
    have h4 : P z = 0 := Submodule.projectionOnto_apply_right hc ⟨z, hz⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, map_add (f := _), h1, h2, h3, h4, add_zero, map_zero]
    rfl⟩
  have hpv : p v ≠ 0 := by
    intro h0
    have hvC : v ∈ C'.toSubmodule := (Submodule.projectionOnto_apply_eq_zero_iff hc).1 h0
    have hKC : K ≤ C := by
      refine Submodule.span_le.2 ?_
      rintro _ rfl
      exact hvC
    have hNC : N ≤ N ⊓ C := le_inf le_rfl (hNK.trans hKC)
    rw [hC.inf_eq_bot] at hNC
    exact hN.1 (le_bot_iff.1 hNC)

  have hN'0 : N'.toSubmodule ≠ ⊥ := fun h => hN'.1 (Subrepresentation.toSubmodule_injective h)
  obtain ⟨x0, hx0, hx00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN'0
  have hτ : τ.IsIrreducible := by
    refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun U => ?_ }
    · have hm : (⟨x0, hx0⟩ : N'.toSubmodule) ∈ (⊤ : Subrepresentation τ).toSubmodule := trivial
      rw [← h] at hm
      have : (⟨x0, hx0⟩ : N'.toSubmodule) = 0 := (Submodule.mem_bot ℂ).1 hm
      exact hx00 (congrArg Subtype.val this)
    · let U'' : Subrepresentation ρ := ⟨U.toSubmodule.map N'.toSubmodule.subtype, fun g x hx => by
        obtain ⟨y, hy, rfl⟩ := hx
        exact ⟨τ g y, U.apply_mem_toSubmodule g hy, rfl⟩⟩
      have hle : U'' ≤ N' := by
        rintro _ ⟨y, -, rfl⟩
        exact y.2
      rcases hN'.le_iff.1 hle with h | h
      · left
        refine Subrepresentation.toSubmodule_injective (eq_bot_iff.2 fun y hy => ?_)
        have hm : (y : V) ∈ U''.toSubmodule := ⟨y, hy, rfl⟩
        rw [h] at hm
        have h0 : (y : V) = 0 := (Submodule.mem_bot ℂ).1 hm
        exact (Submodule.mem_bot ℂ).2 (Subtype.ext h0)
      · right
        refine Subrepresentation.toSubmodule_injective (eq_top_iff.2 fun y _ => ?_)
        have hm : (y : V) ∈ U''.toSubmodule := by rw [h]; exact y.2
        obtain ⟨z, hz, hzy⟩ := hm
        have : z = y := Subtype.ext hzy
        rw [← this]
        exact hz
  let f' : τ.IntertwiningMap ρ := ⟨N'.toSubmodule.subtype, fun g => LinearMap.ext fun x => rfl⟩
  have hf' : f' ≠ 0 := by
    intro h
    have := congrArg (fun q : τ.IntertwiningMap ρ => q ⟨x0, hx0⟩) h
    exact hx00 this
  obtain ⟨eqv⟩ := hiso _ τ hτ f' hf'
  refine ⟨eqv.symm.toIntertwiningMap.comp p, fun h => hpv ?_⟩
  have := congrArg eqv h
  simpa using this

end GlobalTheory.IsoSep
end

section

namespace GlobalTheory.InvariantSupremum

theorem eq_bot_or_eq_top_of_invariant {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ G W) (hσ : Representation.IsIrreducible σ) (P : Submodule ℂ W)
    (hP : ∀ g : G, ∀ w ∈ P, σ g w ∈ P) : P = ⊥ ∨ P = ⊤ := by
  let Q : Subrepresentation σ :=
    { toSubmodule := P
      apply_mem_toSubmodule := by
        intro g v hv
        exact hP g v hv }
  rcases @IsSimpleOrder.eq_bot_or_eq_top _ _ _ hσ Q with h | h
  · exact Or.inl (congrArg Subrepresentation.toSubmodule h)
  · exact Or.inr (congrArg Subrepresentation.toSubmodule h)

theorem fixed_mem_of_mem_iSup_range {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {ι : Type} (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) (hσ : Representation.IsIrreducible σ) (f : ι → W →ₗ[ℂ] V)
    (hf : ∀ (i : ι) (g : G) (u : W), f i (σ g u) = ρ g (f i u)) (K : Set G)
    (Z : Submodule ℂ V) (hZ : ∀ (i : ι) (v : W), (∀ k ∈ K, σ k v = v) → f i v ∈ Z)
    (_hfix : ∀ z ∈ Z, ∀ k ∈ K, ρ k z = z) (φ : V) (hφ : ∀ k ∈ K, ρ k φ = φ)
    (hmem : φ ∈ ⨆ i : ι, LinearMap.range (f i)) : φ ∈ Z := by
  classical
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.mp hmem
  clear hmem

  have inv : ∀ (t : Finset ι) (g : G), ∀ z ∈ ⨆ i ∈ t, LinearMap.range (f i),
      ρ g z ∈ ⨆ i ∈ t, LinearMap.range (f i) := by
    intro t g z hz
    have hle : (⨆ i ∈ t, LinearMap.range (f i)) ≤
        (⨆ i ∈ t, LinearMap.range (f i)).comap (ρ g) := by
      refine iSup₂_le fun i hi => ?_
      rintro _ ⟨w, rfl⟩
      rw [Submodule.mem_comap, ← hf i g w]
      exact (le_iSup₂ (f := fun i (_ : i ∈ t) => LinearMap.range (f i)) i hi)
        (LinearMap.mem_range_self _ _)
    exact hle hz
  induction s using Finset.induction_on generalizing φ with
  | empty =>
    simp only [Finset.notMem_empty, iSup_false, iSup_bot, Submodule.mem_bot] at hs
    rw [hs]
    exact Z.zero_mem
  | @insert j s hj ih =>
    rw [Finset.iSup_insert, Submodule.mem_sup] at hs
    obtain ⟨y, ⟨u, rfl⟩, z, hz, rfl⟩ := hs

    rcases eq_bot_or_eq_top_of_invariant σ hσ ((⨆ i ∈ s, LinearMap.range (f i)).comap (f j)) (by
        intro g w hw
        rw [Submodule.mem_comap] at hw ⊢
        rw [hf]
        exact inv s g _ hw) with hN | hN
    ·
      have hu : ∀ k ∈ K, σ k u = u := by
        intro k hk
        have e : ρ k (f j u) - f j u = z - ρ k z := by
          rw [sub_eq_sub_iff_add_eq_add, ← map_add (f := _), hφ k hk, add_comm]
        have h1 : σ k u - u ∈ (⨆ i ∈ s, LinearMap.range (f i)).comap (f j) := by
          rw [Submodule.mem_comap, map_sub, hf, e]
          exact Submodule.sub_mem _ hz (inv s k z hz)
        rw [hN, Submodule.mem_bot, sub_eq_zero] at h1
        exact h1
      have hzfix : ∀ k ∈ K, ρ k z = z := by
        intro k hk
        have h2 := hφ k hk
        rw [map_add (f := _), ← hf, hu k hk] at h2
        exact add_left_cancel h2
      exact Z.add_mem (hZ j u hu) (ih z hzfix hz)
    ·
      have hu : f j u ∈ ⨆ i ∈ s, LinearMap.range (f i) := by
        have h3 : u ∈ (⨆ i ∈ s, LinearMap.range (f i)).comap (f j) := by
          rw [hN]
          trivial
        exact h3
      exact ih _ hφ (Submodule.add_mem _ hu hz)

end GlobalTheory.InvariantSupremum
end

section

namespace GlobalTheory.CharacterDetermines

open Representation Module

variable {G V W V' W' : Type} [Group G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']

noncomputable def prodEquivOfIsCompl {ρ : Representation ℂ G V} (p q : Subrepresentation ρ)
    (h : IsCompl p.toSubmodule q.toSubmodule) :
    (p.toRepresentation.prod q.toRepresentation).Equiv ρ :=
  Representation.Equiv.mk (Submodule.prodEquivOfIsCompl _ _ h) fun g => by
    refine LinearMap.ext fun x => ?_
    obtain ⟨a, b⟩ := x
    simp [Representation.prod, Subrepresentation.toRepresentation]

noncomputable def prodCongr {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    {ρ' : Representation ℂ G V'} {σ' : Representation ℂ G W'}
    (e : ρ.Equiv σ) (e' : ρ'.Equiv σ') : (ρ.prod ρ').Equiv (σ.prod σ') :=
  Representation.Equiv.mk (e.toLinearEquiv.prodCongr e'.toLinearEquiv) fun g => by
    refine LinearMap.ext fun x => ?_
    obtain ⟨a, b⟩ := x
    refine Prod.ext ?_ ?_
    · exact e.toIntertwiningMap.isIntertwining _ _ g a
    · exact e'.toIntertwiningMap.isIntertwining _ _ g b

theorem character_prod [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    (ρ.prod σ).character = ρ.character + σ.character := by
  funext g
  change LinearMap.trace ℂ (V × W) ((ρ g).prodMap (σ g)) = LinearMap.trace ℂ V (ρ g) + LinearMap.trace ℂ W (σ g)
  rw [LinearMap.trace_prodMap']

theorem exists_isCompl [Finite G] {ρ : Representation ℂ G V} (p : Subrepresentation ρ) :
    ∃ q : Subrepresentation ρ, IsCompl p.toSubmodule q.toSubmodule := by
  have : NeZero (Nat.card G : ℂ) := ⟨by exact_mod_cast Nat.card_pos.ne'⟩
  obtain ⟨c, hc⟩ := MonoidAlgebra.Submodule.exists_isCompl (Subrepresentation.asSubmodule p)
  refine ⟨Subrepresentation.ofSubmodule' c, ?_⟩
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    exact (Submodule.disjoint_def.mp hc.disjoint) x hx hx'
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro x
    have hx : (show ρ.asModule from x) ∈ (Subrepresentation.asSubmodule p ⊔ c) := by
      rw [hc.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hx
    exact Submodule.mem_sup.mpr ⟨y, hy, z, hz, hyz⟩

theorem nonempty_equiv_range {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (f : IntertwiningMap ρ σ) (q : Subrepresentation ρ)
    (h : IsCompl f.ker.toSubmodule q.toSubmodule) :
    Nonempty (q.toRepresentation.Equiv f.range.toRepresentation) := by
  let φ : q.toSubmodule →ₗ[ℂ] f.range.toSubmodule :=
    (f.toLinearMap.comp q.toSubmodule.subtype).codRestrict f.range.toSubmodule
      (fun v => LinearMap.mem_range_self _ _)
  have hinj : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have ha' : f.toLinearMap (a : V) = 0 := congrArg Subtype.val ha
    have hk : (a : V) ∈ f.ker.toSubmodule := ha'
    exact Subtype.ext ((Submodule.disjoint_def.mp h.disjoint) _ hk a.2)
  have hsurj : Function.Surjective φ := by
    rintro ⟨w, v, rfl⟩
    have hv : v ∈ f.ker.toSubmodule ⊔ q.toSubmodule := by
      rw [h.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨k, hk, u, hu, hku⟩ := Submodule.mem_sup.mp hv
    refine ⟨⟨u, hu⟩, Subtype.ext ?_⟩
    have hk' : f.toLinearMap k = 0 := hk
    change f.toLinearMap u = f.toLinearMap v
    rw [← hku, map_add (f := _), hk', zero_add]
  let ψ : IntertwiningMap q.toRepresentation f.range.toRepresentation :=
    φ.intertwiningMap_of_isIntertwiningMap _ _ (by
      intro g v
      apply Subtype.ext
      change f.toLinearMap (ρ g (v : V)) = σ g (f.toLinearMap v)
      exact IntertwiningMap.isIntertwining _ _ f g v)
  exact ⟨ψ.ofBijective ⟨hinj, hsurj⟩⟩

theorem exists_ne_zero [Finite G] [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] [Nontrivial V]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (h : ρ.character = σ.character) :
    ∃ f : IntertwiningMap ρ σ, f ≠ 0 := by
  have := Fintype.ofFinite G
  have : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
  have h1 := card_inv_mul_sum_char_mul_char_eq_finrank ρ σ
  have h2 := card_inv_mul_sum_char_mul_char_eq_finrank ρ ρ
  rw [← h, h2] at h1
  have hid : IntertwiningMap.id ρ ≠ 0 := by
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    intro h0
    exact hv (by simpa using DFunLike.congr_fun h0 v)
  have hpos : 0 < finrank ℂ (IntertwiningMap ρ ρ) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_, hid⟩
  have heq : finrank ℂ (IntertwiningMap ρ ρ) = finrank ℂ (IntertwiningMap ρ σ) := by
    exact_mod_cast h1
  rw [heq] at hpos
  exact Module.finrank_pos_iff_exists_ne_zero.mp hpos

theorem aux [Finite G] (n : ℕ) : ∀ (V W : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W), finrank ℂ V = n →
    ρ.character = σ.character → Nonempty (ρ.Equiv σ) := by
  refine Nat.strong_induction_on n ?_
  intro n ih V W _ _ _ _ _ _ ρ σ hn h
  rcases subsingleton_or_nontrivial V with hV | hV
  · have hW : finrank ℂ V = finrank ℂ W := by
      have h1 := congrFun h 1
      rw [char_one, char_one] at h1
      exact_mod_cast h1
    refine ⟨Representation.Equiv.mk (LinearEquiv.ofFinrankEq V W hW) fun g => ?_⟩
    ext v
    rw [Subsingleton.elim v 0]
    simp
  · obtain ⟨f, hf⟩ := exists_ne_zero ρ σ h
    obtain ⟨q, hq⟩ := exists_isCompl f.ker
    obtain ⟨r, hr⟩ := exists_isCompl f.range
    obtain ⟨e⟩ := nonempty_equiv_range f q hq
    have h1 := char_iso (prodEquivOfIsCompl q f.ker hq.symm)
    have h2 := char_iso (prodEquivOfIsCompl f.range r hr)
    rw [character_prod] at h1 h2
    have h3 := char_iso e
    have hsum : q.toRepresentation.character + f.ker.toRepresentation.character =
        f.range.toRepresentation.character + r.toRepresentation.character := by
      rw [h1, h2, h]
    rw [h3] at hsum
    have hK := add_left_cancel hsum
    have hlt : finrank ℂ f.ker.toSubmodule < n := by
      rw [← hn]
      apply Submodule.finrank_lt
      intro htop
      apply hf
      ext v
      have hv : v ∈ f.ker.toSubmodule := htop ▸ Submodule.mem_top
      have hv' : f.toLinearMap v = 0 := hv
      simpa using hv'
    obtain ⟨eK⟩ := ih _ hlt f.ker.toSubmodule r.toSubmodule f.ker.toRepresentation
      r.toRepresentation rfl hK
    exact ⟨((prodEquivOfIsCompl q f.ker hq.symm).symm.trans (prodCongr e eK)).trans
      (prodEquivOfIsCompl f.range r hr)⟩

theorem nonempty_equiv_of_character_eq : ∀ (G V W : Type) [Group G] [Finite G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ G W), ρ.character = σ.character → Nonempty (ρ.Equiv σ) := by
  intro G V W _ _ _ _ _ _ _ _ ρ σ h
  exact aux (finrank ℂ V) V W ρ σ rfl h

end GlobalTheory.CharacterDetermines
end

section

namespace GlobalTheory

theorem exists_rootsOfUnity_character_hom : ∀ {Γ F O LL : Type} [Group Γ] [Field F] [CommRing O] [Field LL] (n : ℕ), 0 < n → ∀ (f : F → Γ → ℂ), (∀ x, x ≠ 0 → f x 1 = 1) → (∀ x, x ≠ 0 → ∀ σ σ', f x (σ * σ') = f x σ * f x σ') → (∀ x y, x ≠ 0 → y ≠ 0 → ∀ σ, f (x * y) σ = f x σ * f y σ) → ∀ (ι : O →+* ℂ), Function.Injective ι → ∀ (ζ : O), IsPrimitiveRoot ζ n → ∀ (t : O →+* LL), ∃ Ψ : ↥(rootsOfUnity n F) →* (Γ →* LLˣ), ∀ (u : ↥(rootsOfUnity n F)) (σ : Γ), ∃ o : O, ι o = f (((u : Fˣ)) : F) σ ∧ ((Ψ u σ : LLˣ) : LL) = t o := by
  intro Γ F O LL _ _ _ _ n hn f hone hmul hx ι hι ζ hζ t
  haveI : NeZero n := ⟨hn.ne'⟩
  have h1 : ∀ σ, f 1 σ = 1 := by
    intro σ
    have hne : f 1 σ ≠ 0 := by
      intro h
      have := hmul 1 one_ne_zero σ σ⁻¹
      rw [mul_inv_cancel, hone 1 one_ne_zero, h, zero_mul] at this
      exact one_ne_zero this
    have := hx 1 1 one_ne_zero one_ne_zero σ
    rw [mul_one] at this
    exact (mul_left_cancel₀ hne (by rw [mul_one]; exact this)).symm
  have hpow : ∀ x, x ≠ 0 → ∀ σ (k : ℕ), f (x ^ k) σ = f x σ ^ k := by
    intro x hx0 σ k
    induction k with
    | zero => simp [h1]
    | succ k ih => rw [pow_succ, hx _ _ (pow_ne_zero k hx0) hx0, ih, pow_succ]
  have hex : ∀ (u : rootsOfUnity n F) (σ : Γ), ∃ o : O, ι o = f ((u : Fˣ) : F) σ := by
    intro u σ
    have hu : (((u : Fˣ) : F)) ^ n = 1 := by
      have := u.2
      rw [mem_rootsOfUnity'] at this
      exact this
    have h2 : f ((u : Fˣ) : F) σ ^ n = 1 := by
      rw [← hpow _ (Units.ne_zero _), hu, h1]
    obtain ⟨j, -, hj⟩ := (hζ.map_of_injective hι).eq_pow_of_pow_eq_one h2
    exact ⟨ζ ^ j, by rw [map_pow, hj]⟩
  choose o ho using hex
  let g : rootsOfUnity n F → (Γ →* LL) := fun u =>
    { toFun := fun σ => t (o u σ)
      map_one' := by
        have : o u 1 = 1 := hι (by rw [ho, map_one, hone _ (Units.ne_zero _)])
        rw [this, map_one]
      map_mul' := by
        intro a b
        have : o u (a * b) = o u a * o u b :=
          hι (by rw [map_mul, ho, ho, ho, hmul _ (Units.ne_zero _)])
        rw [this, map_mul] }
  refine ⟨MonoidHom.mk' (fun u => (g u).toHomUnits) ?_, fun u σ => ⟨o u σ, ho u σ, rfl⟩⟩
  intro u v
  ext σ
  have : o (u * v) σ = o u σ * o v σ :=
    hι (by
      rw [map_mul, ho, ho, ho, Subgroup.coe_mul, Units.val_mul,
        hx _ _ (Units.ne_zero _) (Units.ne_zero _)])
  show t (o (u * v) σ) = t (o u σ) * t (o v σ)
  rw [this, map_mul]

end GlobalTheory
end

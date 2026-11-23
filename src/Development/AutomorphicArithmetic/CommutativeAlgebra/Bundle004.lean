module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle001
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.LocallyConstant.Basic
public import Development.AutomorphicArithmetic.RepresentationRank.RepOfRank
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section
open IsLocalRing UpperTheory.Et

private theorem one_add_mul_idem_pow {S : Type} [CommRing S] {e : S} (he : IsIdempotentElem e)
    (c : S) (n : ℕ) : (1 + c * e) ^ n = 1 + ((1 + c) ^ n - 1) * e := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h2 : e * e = e := he
    rw [pow_succ, ih, pow_succ]
    linear_combination (((1 + c) ^ n - 1) * c) * h2

theorem UpperTheory.roots_of_unity_eq_locallyConstant_powers_spectrum :
    ∀ (S : Type) [CommRing S] (q : ℕ) [NeZero q] (ζ : S), GoodRoot q ζ →
      (∀ g : LocallyConstant (PrimeSpectrum S) (ZMod q), ∃ w : S, w ^ q = 1 ∧ ∀ p : PrimeSpectrum S, w - ζ ^ (g p).val ∈ p.asIdeal) ∧
      (∀ w : S, w ^ q = 1 → ∃ g : LocallyConstant (PrimeSpectrum S) (ZMod q), ∀ p : PrimeSpectrum S, w - ζ ^ (g p).val ∈ p.asIdeal) ∧
      ∀ (a b : ZMod q) (p : PrimeSpectrum S), ζ ^ a.val - ζ ^ b.val ∈ p.asIdeal → a = b := by
  intro S _ q _ ζ hζ
  obtain ⟨hq1, hunit, hsplit⟩ := hζ
  have notmem : ∀ (a b : ZMod q) (p : PrimeSpectrum S), a ≠ b →
      ζ ^ a.val - ζ ^ b.val ∉ p.asIdeal := by
    intro a b p hab hmem
    exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem (hunit a b hab))
  refine ⟨fun g => ?_, fun w hw => ?_, fun a b p h => ?_⟩
  · have hfib : ∀ a : ZMod q, ∃ e : S, IsIdempotentElem e ∧
        ∀ p : PrimeSpectrum S, (g p = a ↔ e ∉ p.asIdeal) := by
      intro a
      obtain ⟨e, he, hs⟩ := PrimeSpectrum.isClopen_iff.1 (g.isLocallyConstant.isClopen_fiber a)
      refine ⟨e, he, fun p => ?_⟩
      have := congrArg (p ∈ ·) hs
      simpa [PrimeSpectrum.mem_basicOpen] using this
    choose e he hge using hfib
    refine ⟨∏ a : ZMod q, (1 + (ζ ^ a.val - 1) * e a), ?_, fun p => ?_⟩
    · rw [← Finset.prod_pow]
      refine Finset.prod_eq_one fun a _ => ?_
      rw [one_add_mul_idem_pow (he a)]
      have hz : (1 + (ζ ^ a.val - 1)) ^ q = 1 := by
        rw [add_sub_cancel, ← pow_mul, mul_comm, pow_mul, hq1, one_pow]
      rw [hz, sub_self, zero_mul, add_zero]
    · have h0 : ∀ b, b ≠ g p → Ideal.Quotient.mk p.asIdeal (e b) = 0 := by
        intro b hb
        rw [Ideal.Quotient.eq_zero_iff_mem]
        by_contra h
        exact hb ((hge b p).2 h).symm
      have h1 : Ideal.Quotient.mk p.asIdeal (e (g p)) = 1 := by
        have hn : e (g p) ∉ p.asIdeal := (hge (g p) p).1 rfl
        have hm : e (g p) * (1 - e (g p)) ∈ p.asIdeal := by
          rw [mul_sub, mul_one, (he (g p)).eq, sub_self]
          exact p.asIdeal.zero_mem
        have h1m : 1 - e (g p) ∈ p.asIdeal := (p.isPrime.mem_or_mem hm).resolve_left hn
        rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk p.asIdeal), ← map_sub,
          Ideal.Quotient.eq_zero_iff_mem]
        have := p.asIdeal.neg_mem h1m
        simpa using this
      rw [← Ideal.Quotient.eq, map_prod, Finset.prod_eq_single (g p)]
      · simp [h1]
      · intro b _ hb
        simp [h0 b hb]
      · intro h
        exact absurd (Finset.mem_univ _) h
  · have hprod : ∏ a ∈ Finset.range q, (w - ζ ^ a) = 0 := by
      have := hsplit S (RingHom.id S) w
      simp only [RingHom.id_apply, hw, sub_self] at this
      exact this.symm
    have hex : ∀ p : PrimeSpectrum S, ∃ a : ZMod q, w - ζ ^ a.val ∈ p.asIdeal := by
      intro p
      have h0 : ∏ a ∈ Finset.range q, (w - ζ ^ a) ∈ p.asIdeal := by
        rw [hprod]
        exact p.asIdeal.zero_mem
      obtain ⟨a, ha, hmem⟩ := (Ideal.IsPrime.prod_mem_iff (hp := p.isPrime)).1 h0
      refine ⟨(a : ZMod q), ?_⟩
      rwa [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.1 ha)]
    choose g0 hg0 using hex
    have hiff : ∀ (p : PrimeSpectrum S) (a : ZMod q),
        g0 p = a ↔ ∀ b, b ≠ a → w - ζ ^ b.val ∉ p.asIdeal := by
      intro p a
      constructor
      · rintro rfl b hb hmem
        apply notmem b (g0 p) p hb
        have e1 : ζ ^ b.val - ζ ^ (g0 p).val = (w - ζ ^ (g0 p).val) - (w - ζ ^ b.val) := by ring
        rw [e1]
        exact p.asIdeal.sub_mem (hg0 p) hmem
      · intro h
        by_contra hne
        exact h (g0 p) hne (hg0 p)
    refine ⟨⟨g0, ?_⟩, hg0⟩
    rw [IsLocallyConstant.iff_isOpen_fiber]
    intro a
    have hset : g0 ⁻¹' {a} = ⋂ b : ZMod q, ⋂ (_ : b ≠ a),
        (PrimeSpectrum.basicOpen (w - ζ ^ b.val) : Set (PrimeSpectrum S)) := by
      ext p
      simp [hiff, PrimeSpectrum.mem_basicOpen]
    rw [hset]
    exact isOpen_iInter_of_finite fun b => isOpen_iInter_of_finite fun _ =>
      (PrimeSpectrum.basicOpen _).isOpen
  · by_contra hab
    exact notmem a b p hab h

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace UpperTheory.ClopSum

variable {S : Scheme.{0}}

private theorem isPullback_wl (T : Over S) {A B : Over S} (i : A ⟶ B) :
    IsPullback (T ◁ i).left (snd T A).left (snd T B).left i.left := by
  have eq1 : (T ◁ i).left ≫ (fst T B).left = (fst T A).left := Over.whiskerLeft_left_fst i
  have eq2 : i.left ≫ B.hom = A.hom := Over.w i
  have s : IsPullback ((T ◁ i).left ≫ (fst T B).left) (snd T A).left T.hom (i.left ≫ B.hom) := by
    rw [eq1, eq2]
    exact IsPullback.of_hasPullback T.hom A.hom
  exact IsPullback.of_right s (Over.whiskerLeft_left_snd i) (IsPullback.of_hasPullback T.hom B.hom)

private theorem range_wl (T : Over S) {A B : Over S} (i : A ⟶ B) :
    Set.range (T ◁ i).left = (snd T B).left ⁻¹' Set.range i.left := by
  have h := isPullback_wl T i
  rw [← Scheme.Pullback.range_fst, ← h.isoPullback_hom_fst]
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨h.isoPullback.hom a, rfl⟩
  · rintro ⟨b, rfl⟩
    refine ⟨h.isoPullback.inv b, ?_⟩
    show (h.isoPullback.inv ≫ h.isoPullback.hom ≫ pullback.fst _ _) b = _
    rw [Iso.inv_hom_id_assoc]

private theorem opens_ext {C A₁ A₂ : Scheme.{0}} (j₁ : A₁ ⟶ C) (j₂ : A₂ ⟶ C)
    (hr : Set.range j₁ = (Set.range j₂)ᶜ) {V V' : C.Opens}
    (h₁ : j₁ ⁻¹ᵁ V = j₁ ⁻¹ᵁ V') (h₂ : j₂ ⁻¹ᵁ V = j₂ ⁻¹ᵁ V') : V = V' := by
  ext x
  by_cases hx : x ∈ Set.range j₁
  · obtain ⟨a, rfl⟩ := hx
    have := SetLike.ext_iff.mp h₁ a
    simpa using this
  · have hx2 : x ∈ Set.range j₂ := by
      rw [hr] at hx
      simpa using hx
    obtain ⟨b, rfl⟩ := hx2
    have := SetLike.ext_iff.mp h₂ b
    simpa using this

private theorem glue {C A₁ A₂ : Scheme.{0}} (j₁ : A₁ ⟶ C) (j₂ : A₂ ⟶ C)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] (hr : Set.range j₁ = (Set.range j₂)ᶜ)
    (V₁ : A₁.Opens) (V₂ : A₂.Opens) (h₁ : IsClosed (V₁ : Set A₁)) (h₂ : IsClosed (V₂ : Set A₂)) :
    ∃ V : C.Opens, IsClosed (V : Set C) ∧ j₁ ⁻¹ᵁ V = V₁ ∧ j₂ ⁻¹ᵁ V = V₂ := by
  have hc1 : IsClosed (Set.range j₁) := by
    rw [hr]
    exact j₂.isOpenEmbedding.isOpen_range.isClosed_compl
  have hc2 : IsClosed (Set.range j₂) := by
    have e : Set.range j₂ = (Set.range j₁)ᶜ := by rw [hr, compl_compl]
    rw [e]
    exact j₁.isOpenEmbedding.isOpen_range.isClosed_compl
  have e1 : Topology.IsClosedEmbedding j₁ := ⟨j₁.isOpenEmbedding.isEmbedding, hc1⟩
  have e2 : Topology.IsClosedEmbedding j₂ := ⟨j₂.isOpenEmbedding.isEmbedding, hc2⟩
  have hopen : IsOpen (j₁ '' (V₁ : Set A₁) ∪ j₂ '' (V₂ : Set A₂)) :=
    (j₁.isOpenEmbedding.isOpenMap _ V₁.isOpen).union (j₂.isOpenEmbedding.isOpenMap _ V₂.isOpen)
  refine ⟨⟨_, hopen⟩, (e1.isClosedMap _ h₁).union (e2.isClosedMap _ h₂), ?_, ?_⟩
  · ext a
    show j₁ a ∈ j₁ '' (V₁ : Set A₁) ∪ j₂ '' (V₂ : Set A₂) ↔ a ∈ V₁
    constructor
    · rintro (⟨a', ha', he⟩ | ⟨b, hb, he⟩)
      · rw [← j₁.isOpenEmbedding.injective he]
        exact ha'
      · exfalso
        have hm : j₁ a ∈ Set.range j₁ := ⟨a, rfl⟩
        rw [hr] at hm
        exact hm ⟨b, he⟩
    · intro ha
      exact Or.inl ⟨a, ha, rfl⟩
  · ext b
    show j₂ b ∈ j₁ '' (V₁ : Set A₁) ∪ j₂ '' (V₂ : Set A₂) ↔ b ∈ V₂
    constructor
    · rintro (⟨a, ha, he⟩ | ⟨b', hb', he⟩)
      · exfalso
        have hm : j₂ b ∈ Set.range j₁ := ⟨a, he⟩
        rw [hr] at hm
        exact hm ⟨b, rfl⟩
      · rw [← j₂.isOpenEmbedding.injective he]
        exact hb'
    · intro hb
      exact Or.inr ⟨b, hb, rfl⟩

end UpperTheory.ClopSum

private theorem UpperTheory.preimage_comp_scheme_opens {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (W : Z.Opens) :
    (f ≫ g) ⁻¹ᵁ W = f ⁻¹ᵁ (g ⁻¹ᵁ W) := by
  simp

private theorem UpperTheory.preimage_whisker_left_right_comm {S : Scheme.{0}} {T Y G' G : Over S} (y : T ⟶ Y) (i : G' ⟶ G)
    (W : (Y ⊗ G).left.Opens) :
    (T ◁ i).left ⁻¹ᵁ ((y ▷ G).left ⁻¹ᵁ W) = (y ▷ G').left ⁻¹ᵁ ((Y ◁ i).left ⁻¹ᵁ W) := by
  rw [← UpperTheory.preimage_comp_scheme_opens, ← UpperTheory.preimage_comp_scheme_opens, ← Over.comp_left, ← Over.comp_left,
    whisker_exchange]

private theorem UpperTheory.preimage_whiskerRight_whiskerRight_comp {S : Scheme.{0}} {T Y Z G : Over S} (y : T ⟶ Y) (f : Y ⟶ Z)
    (W : (Z ⊗ G).left.Opens) :
    (y ▷ G).left ⁻¹ᵁ ((f ▷ G).left ⁻¹ᵁ W) = ((y ≫ f) ▷ G).left ⁻¹ᵁ W := by
  rw [← UpperTheory.preimage_comp_scheme_opens, ← Over.comp_left, comp_whiskerRight]

open UpperTheory.ClopSum in
theorem UpperTheory.exists_clopRep_of_disjoint_open_cover :
    ∀ {S : Scheme.{0}} (G G₁ G₂ Y₁ Y₂ : Over S) (i₁ : G₁ ⟶ G) (i₂ : G₂ ⟶ G) (U₁ : (Y₁ ⊗ G₁).left.Opens) (U₂ : (Y₂ ⊗ G₂).left.Opens), IsOpenImmersion i₁.left → IsOpenImmersion i₂.left → Set.range i₁.left = (Set.range i₂.left)ᶜ → UpperTheory.RepresentationRank.Rep G₁ Y₁ U₁ → UpperTheory.RepresentationRank.Rep G₂ Y₂ U₂ → ∃ U : ((Y₁ ⊗ Y₂) ⊗ G).left.Opens, UpperTheory.RepresentationRank.Rep G (Y₁ ⊗ Y₂) U := by
  intro S G G₁ G₂ Y₁ Y₂ i₁ i₂ U₁ U₂ ho₁ ho₂ hr hU₁ hU₂
  have o1 : ∀ T : Over S, IsOpenImmersion (T ◁ i₁).left := fun T =>
    MorphismProperty.of_isPullback (UpperTheory.ClopSum.isPullback_wl T i₁).flip ho₁
  have o2 : ∀ T : Over S, IsOpenImmersion (T ◁ i₂).left := fun T =>
    MorphismProperty.of_isPullback (UpperTheory.ClopSum.isPullback_wl T i₂).flip ho₂
  have rr : ∀ T : Over S, Set.range (T ◁ i₁).left = (Set.range (T ◁ i₂).left)ᶜ := by
    intro T
    rw [UpperTheory.ClopSum.range_wl, UpperTheory.ClopSum.range_wl, hr]
    rfl
  haveI := o1 (Y₁ ⊗ Y₂)
  haveI := o2 (Y₁ ⊗ Y₂)
  obtain ⟨U, hUc, hU1, hU2⟩ := UpperTheory.ClopSum.glue ((Y₁ ⊗ Y₂) ◁ i₁).left ((Y₁ ⊗ Y₂) ◁ i₂).left
    (rr _) ((fst Y₁ Y₂ ▷ G₁).left ⁻¹ᵁ U₁) ((snd Y₁ Y₂ ▷ G₂).left ⁻¹ᵁ U₂)
    (hU₁.1.preimage (Scheme.Hom.continuous _)) (hU₂.1.preimage (Scheme.Hom.continuous _))
  refine ⟨U, hUc, ?_⟩
  intro T V hV
  have c1 : ∀ y : T ⟶ Y₁ ⊗ Y₂,
      (T ◁ i₁).left ⁻¹ᵁ ((y ▷ G).left ⁻¹ᵁ U) = ((y ≫ fst Y₁ Y₂) ▷ G₁).left ⁻¹ᵁ U₁ := by
    intro y
    rw [UpperTheory.preimage_whisker_left_right_comm, hU1, UpperTheory.preimage_whiskerRight_whiskerRight_comp]
  have c2 : ∀ y : T ⟶ Y₁ ⊗ Y₂,
      (T ◁ i₂).left ⁻¹ᵁ ((y ▷ G).left ⁻¹ᵁ U) = ((y ≫ snd Y₁ Y₂) ▷ G₂).left ⁻¹ᵁ U₂ := by
    intro y
    rw [UpperTheory.preimage_whisker_left_right_comm, hU2, UpperTheory.preimage_whiskerRight_whiskerRight_comp]
  obtain ⟨y₁, hy₁, hu₁⟩ := hU₁.2 T ((T ◁ i₁).left ⁻¹ᵁ V) (hV.preimage (Scheme.Hom.continuous _))
  obtain ⟨y₂, hy₂, hu₂⟩ := hU₂.2 T ((T ◁ i₂).left ⁻¹ᵁ V) (hV.preimage (Scheme.Hom.continuous _))
  refine ⟨lift y₁ y₂, ?_, ?_⟩
  · show ((lift y₁ y₂) ▷ G).left ⁻¹ᵁ U = V
    apply UpperTheory.ClopSum.opens_ext (T ◁ i₁).left (T ◁ i₂).left (rr T)
    · rw [c1, lift_fst]
      exact hy₁
    · rw [c2, lift_snd]
      exact hy₂
  · intro y hy
    have hy' : (y ▷ G).left ⁻¹ᵁ U = V := hy
    apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst]
      exact hu₁ _ (by
        show ((y ≫ fst Y₁ Y₂) ▷ G₁).left ⁻¹ᵁ U₁ = _
        rw [← c1, hy'])
    · rw [lift_snd]
      exact hu₂ _ (by
        show ((y ≫ snd Y₁ Y₂) ▷ G₂).left ⁻¹ᵁ U₂ = _
        rw [← c2, hy'])
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

private theorem UpperTheory.preimage_whiskerRight_comp_over {S : Scheme.{0}} {A B C G : Over S} (f : A ⟶ B) (g : B ⟶ C)
    (W : (C ⊗ G).left.Opens) :
    ((f ≫ g) ▷ G).left ⁻¹ᵁ W = (f ▷ G).left ⁻¹ᵁ ((g ▷ G).left ⁻¹ᵁ W) := by
  simp

theorem UpperTheory.clopRep_unique :
    ∀ {S : Scheme.{0}} (G Y Y' : Over S) (U : (Y ⊗ G).left.Opens) (U' : (Y' ⊗ G).left.Opens), UpperTheory.RepresentationRank.Rep G Y U → UpperTheory.RepresentationRank.Rep G Y' U' → Nonempty (Y ≅ Y') := by
  intro S G Y Y' U U' hU hU'
  obtain ⟨φ, hφ, -⟩ := hU'.2 Y U hU.1
  obtain ⟨ψ, hψ, -⟩ := hU.2 Y' U' hU'.1
  have hid : ∀ {Z : Over S} (W : (Z ⊗ G).left.Opens), ((𝟙 Z) ▷ G).left ⁻¹ᵁ W = W := by
    intro Z W
    simp
  have e1 : φ ≫ ψ = 𝟙 Y := by
    obtain ⟨y, -, huniq⟩ := hU.2 Y U hU.1
    have a := huniq (φ ≫ ψ) (by
      show ((φ ≫ ψ) ▷ G).left ⁻¹ᵁ U = U
      rw [UpperTheory.preimage_whiskerRight_comp_over, hψ, hφ])
    have b := huniq (𝟙 Y) (hid U)
    rw [a, b]
  have e2 : ψ ≫ φ = 𝟙 Y' := by
    obtain ⟨y, -, huniq⟩ := hU'.2 Y' U' hU'.1
    have a := huniq (ψ ≫ φ) (by
      show ((ψ ≫ φ) ▷ G).left ⁻¹ᵁ U' = U'
      rw [UpperTheory.preimage_whiskerRight_comp_over, hφ, hψ])
    have b := huniq (𝟙 Y') (hid U')
    rw [a, b]
  exact ⟨⟨φ, ψ, e1, e2⟩⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace UpperTheory.ClopPullback

variable {S S' : Scheme.{0}} (t : S' ⟶ S) (G Y : Over S)

private noncomputable def fwd (T' : Over S') :
    (T' ⊗ (Over.pullback t).obj G).left ⟶ ((Over.map t).obj T' ⊗ G).left :=
  pullback.lift (pullback.fst T'.hom (pullback.snd G.hom t))
    (pullback.snd T'.hom (pullback.snd G.hom t) ≫ pullback.fst G.hom t) (by
      have h := pullback.condition (f := T'.hom) (g := pullback.snd G.hom t)
      have h2 := pullback.condition (f := G.hom) (g := t)
      simp only [Over.map_obj_hom, Category.assoc, h2]
      rw [reassoc_of% h])

private noncomputable def bwd (T' : Over S') :
    ((Over.map t).obj T' ⊗ G).left ⟶ (T' ⊗ (Over.pullback t).obj G).left :=
  pullback.lift (pullback.fst (T'.hom ≫ t) G.hom)
    (pullback.lift (pullback.snd (T'.hom ≫ t) G.hom) (pullback.fst (T'.hom ≫ t) G.hom ≫ T'.hom)
      (by simpa using (pullback.condition (f := T'.hom ≫ t) (g := G.hom)).symm))
    (pullback.lift_snd _ _ _).symm

private theorem fwd_fst (T' : Over S') :
    fwd t G T' ≫ pullback.fst (T'.hom ≫ t) G.hom = pullback.fst T'.hom (pullback.snd G.hom t) :=
  pullback.lift_fst _ _ _

private theorem fwd_snd (T' : Over S') :
    fwd t G T' ≫ pullback.snd (T'.hom ≫ t) G.hom =
      pullback.snd T'.hom (pullback.snd G.hom t) ≫ pullback.fst G.hom t :=
  pullback.lift_snd _ _ _

private theorem bwd_fst (T' : Over S') :
    bwd t G T' ≫ pullback.fst T'.hom (pullback.snd G.hom t) = pullback.fst (T'.hom ≫ t) G.hom :=
  pullback.lift_fst _ _ _

private theorem bwd_snd_fst (T' : Over S') :
    bwd t G T' ≫ pullback.snd T'.hom (pullback.snd G.hom t) ≫ pullback.fst G.hom t =
      pullback.snd (T'.hom ≫ t) G.hom := by
  unfold bwd
  erw [pullback.lift_snd_assoc, pullback.lift_fst]

private theorem fwd_bwd (T' : Over S') : fwd t G T' ≫ bwd t G T' = 𝟙 _ := by
  apply pullback.hom_ext
  · show fwd t G T' ≫ bwd t G T' ≫ pullback.fst T'.hom (pullback.snd G.hom t) =
      𝟙 _ ≫ pullback.fst T'.hom (pullback.snd G.hom t)
    rw [bwd_fst, fwd_fst, Category.id_comp]
  · show fwd t G T' ≫ bwd t G T' ≫ pullback.snd T'.hom (pullback.snd G.hom t) =
      𝟙 _ ≫ pullback.snd T'.hom (pullback.snd G.hom t)
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, Category.assoc, bwd_snd_fst, fwd_snd]
      exact (Category.id_comp _).symm
    · have hb : bwd t G T' ≫ pullback.snd T'.hom (pullback.snd G.hom t) ≫ pullback.snd G.hom t =
          pullback.fst (T'.hom ≫ t) G.hom ≫ T'.hom := by
        unfold bwd
        erw [pullback.lift_snd_assoc, pullback.lift_snd]
      rw [Category.assoc, Category.assoc, hb, ← Category.assoc, fwd_fst, pullback.condition]
      exact (Category.id_comp _).symm

private theorem bwd_fwd (T' : Over S') : bwd t G T' ≫ fwd t G T' = 𝟙 _ := by
  apply pullback.hom_ext
  · show bwd t G T' ≫ fwd t G T' ≫ pullback.fst (T'.hom ≫ t) G.hom =
      𝟙 _ ≫ pullback.fst (T'.hom ≫ t) G.hom
    rw [fwd_fst, bwd_fst, Category.id_comp]
  · show bwd t G T' ≫ fwd t G T' ≫ pullback.snd (T'.hom ≫ t) G.hom =
      𝟙 _ ≫ pullback.snd (T'.hom ≫ t) G.hom
    rw [fwd_snd, bwd_snd_fst, Category.id_comp]

private noncomputable def cmp :
    ((Over.pullback t).obj Y ⊗ (Over.pullback t).obj G).left ⟶ (Y ⊗ G).left :=
  pullback.map _ _ _ _ (pullback.fst Y.hom t) (pullback.fst G.hom t) t
    (by simp [pullback.condition]) (by simp [pullback.condition])

private theorem key {T' : Over S'} (y' : T' ⟶ (Over.pullback t).obj Y) :
    (y' ▷ (Over.pullback t).obj G).left ≫ cmp t G Y =
      fwd t G T' ≫ (((Over.mapPullbackAdj t).homEquiv _ _).symm y' ▷ G).left := by
  set x := ((Over.mapPullbackAdj t).homEquiv _ _).symm y' with hx
  have a1 : (y' ▷ (Over.pullback t).obj G).left ≫
      pullback.fst ((Over.pullback t).obj Y).hom ((Over.pullback t).obj G).hom =
      pullback.fst T'.hom ((Over.pullback t).obj G).hom ≫ y'.left :=
    Over.whiskerRight_left_fst _
  have a2 : (y' ▷ (Over.pullback t).obj G).left ≫
      pullback.snd ((Over.pullback t).obj Y).hom ((Over.pullback t).obj G).hom =
      pullback.snd T'.hom ((Over.pullback t).obj G).hom :=
    Over.whiskerRight_left_snd _
  have b1 : (x ▷ G).left ≫ pullback.fst Y.hom G.hom =
      pullback.fst ((Over.map t).obj T').hom G.hom ≫ x.left :=
    Over.whiskerRight_left_fst _
  have b2 : (x ▷ G).left ≫ pullback.snd Y.hom G.hom =
      pullback.snd ((Over.map t).obj T').hom G.hom :=
    Over.whiskerRight_left_snd _
  have c1 : cmp t G Y ≫ pullback.fst Y.hom G.hom =
      pullback.fst ((Over.pullback t).obj Y).hom ((Over.pullback t).obj G).hom ≫
        pullback.fst Y.hom t :=
    pullback.lift_fst _ _ _
  have c2 : cmp t G Y ≫ pullback.snd Y.hom G.hom =
      pullback.snd ((Over.pullback t).obj Y).hom ((Over.pullback t).obj G).hom ≫
        pullback.fst G.hom t :=
    pullback.lift_snd _ _ _
  have hxl : x.left = y'.left ≫ pullback.fst Y.hom t := by
    simp [hx, Over.mapPullbackAdj]
  apply pullback.hom_ext
  · rw [Category.assoc, c1, ← Category.assoc, a1, Category.assoc, Category.assoc, b1,
      ← Category.assoc, hxl]
    exact congrArg (· ≫ y'.left ≫ pullback.fst Y.hom t) (fwd_fst t G T').symm
  · rw [Category.assoc, c2, ← Category.assoc, a2, Category.assoc, b2]
    exact (fwd_snd t G T').symm

end UpperTheory.ClopPullback

open UpperTheory.ClopPullback

private theorem UpperTheory.preimage_comp_scheme_opens_of_pullback {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (W : Z.Opens) :
    (f ≫ g) ⁻¹ᵁ W = f ⁻¹ᵁ (g ⁻¹ᵁ W) := by
  simp

private theorem UpperTheory.isClosed_preimage_opens_of_isClosed {X Y : Scheme.{0}} (f : X ⟶ Y) {W : Y.Opens}
    (hW : IsClosed (W : Set Y)) : IsClosed ((f ⁻¹ᵁ W : X.Opens) : Set X) :=
  hW.preimage f.continuous

private theorem UpperTheory.preimage_preimage_eq_of_section {X Y : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ X) (h : f ≫ g = 𝟙 X)
    (W : X.Opens) : f ⁻¹ᵁ (g ⁻¹ᵁ W) = W := by
  rw [← UpperTheory.preimage_comp_scheme_opens_of_pullback, h]
  simp

theorem UpperTheory.exists_clopRep_pullback :
    ∀ {S S' : Scheme.{0}} (t : S' ⟶ S) (G Y : Over S) (U : (Y ⊗ G).left.Opens), UpperTheory.RepresentationRank.Rep G Y U → ∃ U' : ((Over.pullback t).obj Y ⊗ (Over.pullback t).obj G).left.Opens, UpperTheory.RepresentationRank.Rep ((Over.pullback t).obj G) ((Over.pullback t).obj Y) U' := by
  intro S S' t G Y U hU
  refine ⟨cmp t G Y ⁻¹ᵁ U, UpperTheory.isClosed_preimage_opens_of_isClosed _ hU.1, ?_⟩
  intro T' V' hV'
  obtain ⟨y, hy, huniq⟩ := hU.2 ((Over.map t).obj T') (bwd t G T' ⁻¹ᵁ V')
    (UpperTheory.isClosed_preimage_opens_of_isClosed _ hV')
  have hpre : ∀ y' : T' ⟶ (Over.pullback t).obj Y,
      (y' ▷ (Over.pullback t).obj G).left ⁻¹ᵁ (cmp t G Y ⁻¹ᵁ U) =
        fwd t G T' ⁻¹ᵁ ((((Over.mapPullbackAdj t).homEquiv _ _).symm y' ▷ G).left ⁻¹ᵁ U) := by
    intro y'
    rw [← UpperTheory.preimage_comp_scheme_opens_of_pullback, key, UpperTheory.preimage_comp_scheme_opens_of_pullback]
  refine ⟨(Over.mapPullbackAdj t).homEquiv _ _ y, ?_, ?_⟩
  · show (((Over.mapPullbackAdj t).homEquiv _ _ y) ▷ (Over.pullback t).obj G).left ⁻¹ᵁ
        (cmp t G Y ⁻¹ᵁ U) = V'
    rw [hpre, Equiv.symm_apply_apply, hy]
    exact UpperTheory.preimage_preimage_eq_of_section _ _ (fwd_bwd t G T') V'
  · intro y'' hy''
    have hy2 : (y'' ▷ (Over.pullback t).obj G).left ⁻¹ᵁ (cmp t G Y ⁻¹ᵁ U) = V' := hy''
    have h1 : ((((Over.mapPullbackAdj t).homEquiv _ _).symm y'' ▷ G).left ⁻¹ᵁ U) =
        bwd t G T' ⁻¹ᵁ V' := by
      rw [← hy2, hpre, UpperTheory.preimage_preimage_eq_of_section _ _ (bwd_fwd t G T')]
    have h2 := huniq _ h1
    rw [← h2, Equiv.apply_symm_apply]
end

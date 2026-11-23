module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle022
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2699
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2700
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2701
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2702
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.ClosedFibreInj

theorem spMap_epi {K L : Type} [Field K] [Field L] (f : K →+* L) : Epi (spMap f) := by
  letI := f.toAlgebra
  haveI : Flat (spMap f) := by
    rw [spMap, HasRingHomProperty.Spec_iff (P := @Flat)]
    exact (show Module.Flat K L from inferInstance)
  haveI : Surjective (spMap f) := ⟨fun z => ⟨⟨⊥, Ideal.isPrime_bot⟩, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem point_lift (Ω : Type) [Field Ω] (X Y : Scheme.{0}) (g : Y ⟶ X) (hg : Surjective g) (x : Sp Ω ⟶ X) :
    ∃ (Ω' : Type) (_ : Field Ω') (io : Ω →+* Ω') (y : Sp Ω' ⟶ Y), y ≫ g = spMap io ≫ x := by
  haveI := hg
  obtain ⟨w⟩ : Nonempty ↥(Sp Ω) := inferInstance
  obtain ⟨z, -⟩ := (pullback.fst x g).surjective w
  refine ⟨(pullback x g).residueField z, inferInstance,
    (Spec.preimage ((pullback x g).fromSpecResidueField z ≫ pullback.fst x g)).hom,
    (pullback x g).fromSpecResidueField z ≫ pullback.snd x g, ?_⟩
  rw [Category.assoc, ← pullback.condition, ← Category.assoc]
  exact congrArg (· ≫ x) (Spec.map_preimage _).symm

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

theorem closedFibre_inj : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G' : Over M.S) [GrpObj G'] (E : Emb M.π G') (N : Near M.π G') (fU : N.U.left ⟶ PSpace R E.N) (l : pullback N.U.hom M.π ⟶ E.H.toScheme), l ≫ E.H.ι = N.u → l ≫ E.f = pullback.fst _ _ ≫ fU → Surjective M.π → ∀ (Ω : Type) [Field Ω] (κ : ResidueField R →+* Ω) (a a' : Sp Ω ⟶ N.U.left), a ≫ N.U.hom = spMap (κ.comp (residue R)) → a' ≫ N.U.hom = spMap (κ.comp (residue R)) → a ≫ fU = a' ≫ fU → a = a' := by
  intro R _ _ _ M G' _ E N fU l hl hlf hπ Ω _ κ a a' ha ha' hf
  haveI := N.isOpen
  haveI := E.imm
  obtain ⟨Ω', _, io, s, hs⟩ := point_lift Ω (Sp R) M.S M.π hπ (spMap (κ.comp (residue R)))
  have hs' : s ≫ M.π = spMap ((io.comp κ).comp (residue R)) := by
    rw [hs, ← spMap_comp, RingHom.comp_assoc]
  obtain ⟨Ω'', _, io', e, l', -, hl'1, hl'2⟩ := E.fib Ω' s (io.comp κ) hs'

  have pt : ∀ (b : Sp Ω ⟶ N.U.left) (hb : b ≫ N.U.hom = spMap (κ.comp (residue R))),
      ∃ x : Sp Ω'' ⟶ pullback G'.hom (spMap io' ≫ s),
        x ≫ pullback.fst _ _ = spMap io' ≫ pullback.lift (spMap io ≫ b) s (by rw [Category.assoc, hb, hs]) ≫ N.u ∧
        x ≫ pullback.snd _ _ = 𝟙 _ ∧
        x ≫ e.hom.left ≫ pullback.fst _ _ ≫ E.j = spMap io' ≫ spMap io ≫ b ≫ fU := by
    intro b hb
    have hc : (spMap io ≫ b) ≫ N.U.hom = s ≫ M.π := by rw [Category.assoc, hb, hs]
    set p := pullback.lift (spMap io ≫ b) s hc with hp
    refine ⟨pullback.lift (spMap io' ≫ p ≫ N.u) (𝟙 _) (by
      rw [Category.id_comp, Category.assoc, Category.assoc, N.u_over, hp, pullback.lift_snd]), pullback.lift_fst _ _ _,
      pullback.lift_snd _ _ _, ?_⟩
    have h1 : pullback.lift (spMap io' ≫ p ≫ N.u) (𝟙 _) (by
        rw [Category.id_comp, Category.assoc, Category.assoc, N.u_over, hp, pullback.lift_snd]) ≫ l' =
        spMap io' ≫ p ≫ l := by
      rw [← cancel_mono E.H.ι, Category.assoc, hl'1, pullback.lift_fst, Category.assoc, Category.assoc, hl]
    rw [← hl'2, ← Category.assoc, h1, Category.assoc, Category.assoc, hlf, ← Category.assoc p, hp,
      pullback.lift_fst, Category.assoc]
  obtain ⟨x, hx1, hx2, hx3⟩ := pt a ha
  obtain ⟨x', hx1', hx2', hx3'⟩ := pt a' ha'
  have hj : x ≫ e.hom.left ≫ pullback.fst _ _ = x' ≫ e.hom.left ≫ pullback.fst _ _ := by
    rw [← cancel_mono E.j, Category.assoc, Category.assoc, Category.assoc, Category.assoc, hx3, hx3', hf]
  have hsec : ∀ y : Sp Ω'' ⟶ pullback G'.hom (spMap io' ≫ s), y ≫ pullback.snd _ _ = 𝟙 _ →
      y ≫ e.hom.left ≫ pullback.snd _ _ = 𝟙 _ := by
    intro y hy
    have hw := Over.w e.hom
    simp only [Over.pullback_obj_hom] at hw
    rw [hw, hy]
  have he : x ≫ e.hom.left = x' ≫ e.hom.left :=
    pullback.hom_ext (by simpa using hj) (by rw [Category.assoc, Category.assoc, hsec x hx2, hsec x' hx2'])
  have hxx : x = x' := by
    have := congrArg (· ≫ e.inv.left) he
    simpa [← Over.comp_left] using this
  subst hxx
  rw [hx1'] at hx1
  simp only [← Category.assoc, cancel_mono] at hx1
  have h2 := congrArg (· ≫ pullback.fst N.U.hom M.π) hx1
  simp only [Category.assoc, pullback.lift_fst] at h2
  haveI := spMap_epi io'
  haveI := spMap_epi io
  rw [cancel_epi, cancel_epi] at h2
  exact h2.symm

end GlobalTheory.Mum.ClosedFibreInj
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.LawDesc

section

variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S} (N : Near π G)

theorem pt_unique {T : Scheme.{0}} {s : T ⟶ S} {a : T ⟶ N.U.left} {x x' : T ⟶ G.left}
    (h : N.Pt s a x) (h' : N.Pt s a x') : x = x' := by
  obtain ⟨x₀, h₁, h₂, rfl⟩ := h
  obtain ⟨x₁, h₃, h₄, rfl⟩ := h'
  rw [pullback.hom_ext (h₁.trans h₃.symm) (h₂.trans h₄.symm)]

theorem pt_unique_left {T : Scheme.{0}} {s s' : T ⟶ S} {a a' : T ⟶ N.U.left} {x : T ⟶ G.left}
    (h : N.Pt s a x) (h' : N.Pt s' a' x) : a = a' := by
  obtain ⟨x₀, rfl, -, h₂⟩ := h
  obtain ⟨x₁, rfl, -, h₄⟩ := h'
  have := N.isOpen
  rw [(cancel_mono N.u).1 (h₂.trans h₄.symm)]

theorem pt_comp {T T' : Scheme.{0}} (k : T' ⟶ T) {s : T ⟶ S} {a : T ⟶ N.U.left} {x : T ⟶ G.left}
    (h : N.Pt s a x) : N.Pt (k ≫ s) (k ≫ a) (k ≫ x) := by
  obtain ⟨x₀, rfl, rfl, rfl⟩ := h
  exact ⟨k ≫ x₀, Category.assoc _ _ _, Category.assoc _ _ _, Category.assoc _ _ _⟩

theorem pt_over {T : Scheme.{0}} {s : T ⟶ S} {a : T ⟶ N.U.left} {x : T ⟶ G.left}
    (h : N.Pt s a x) : s ≫ π = a ≫ N.U.hom := by
  obtain ⟨x₀, rfl, rfl, -⟩ := h
  rw [Category.assoc, Category.assoc, pullback.condition]

theorem pt_exists {T : Scheme.{0}} {s : T ⟶ S} {a : T ⟶ N.U.left} (h : s ≫ π = a ≫ N.U.hom) :
    ∃ x : Over.mk s ⟶ G, N.Pt s a x.left :=
  ⟨Over.homMk (pullback.lift a s h.symm ≫ N.u) (by
      change (pullback.lift a s h.symm ≫ N.u) ≫ G.hom = s
      rw [Category.assoc, N.u_over, pullback.lift_snd]),
    pullback.lift a s h.symm, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, rfl⟩

variable [GrpObj G]

def Prod {T : Scheme.{0}} (s : T ⟶ S) (v : T ⟶ (N.U ⊗ N.U).left) (z : T ⟶ G.left) : Prop :=
  ∃ x y : Over.mk s ⟶ G, N.Pt s (v ≫ (fst N.U N.U).left) x.left ∧ N.Pt s (v ≫ (snd N.U N.U).left) y.left ∧
    (x * y).left = z

theorem prod_exists {T : Scheme.{0}} {s : T ⟶ S} {v : T ⟶ (N.U ⊗ N.U).left} (h : s ≫ π = v ≫ (N.U ⊗ N.U).hom) :
    ∃ z, Prod N s v z := by
  obtain ⟨x, hx⟩ := pt_exists N (s := s) (a := v ≫ (fst N.U N.U).left)
    (by rw [h, Category.assoc]; exact congrArg (v ≫ ·) (Over.w (fst N.U N.U)).symm)
  obtain ⟨y, hy⟩ := pt_exists N (s := s) (a := v ≫ (snd N.U N.U).left)
    (by rw [h, Category.assoc]; exact congrArg (v ≫ ·) (Over.w (snd N.U N.U)).symm)
  exact ⟨_, x, y, hx, hy, rfl⟩

theorem prod_unique {T : Scheme.{0}} {s : T ⟶ S} {v : T ⟶ (N.U ⊗ N.U).left} {z z' : T ⟶ G.left}
    (h : Prod N s v z) (h' : Prod N s v z') : z = z' := by
  obtain ⟨x, y, hx, hy, rfl⟩ := h
  obtain ⟨x', y', hx', hy', rfl⟩ := h'
  obtain rfl : x = x' := Over.OverMorphism.ext (pt_unique N hx hx')
  obtain rfl : y = y' := Over.OverMorphism.ext (pt_unique N hy hy')
  rfl

theorem prod_over {T : Scheme.{0}} {s : T ⟶ S} {v : T ⟶ (N.U ⊗ N.U).left} {z : T ⟶ G.left}
    (h : Prod N s v z) : z ≫ G.hom = s := by
  obtain ⟨x, y, -, -, rfl⟩ := h
  exact Over.w (x * y)

theorem prod_comp {T T' : Scheme.{0}} (k : T' ⟶ T) {s : T ⟶ S} {v : T ⟶ (N.U ⊗ N.U).left} {z : T ⟶ G.left}
    (h : Prod N s v z) : Prod N (k ≫ s) (k ≫ v) (k ≫ z) := by
  obtain ⟨x, y, hx, hy, rfl⟩ := h
  let k' : Over.mk (k ≫ s) ⟶ Over.mk s := Over.homMk k rfl
  refine ⟨k' ≫ x, k' ≫ y, ?_, ?_, ?_⟩
  · rw [Category.assoc]; exact pt_comp N k hx
  · rw [Category.assoc]; exact pt_comp N k hy
  · rw [← comp_mul]; rfl

theorem prod_act {c : S ⟶ S} {φ : G.left ⟶ G.left} (hφ : IsGrpPullback G G c φ)
    (hN : ∀ (T : Scheme.{0}) (s : T ⟶ S) (u : T ⟶ N.U.left) (x : T ⟶ G.left),
      N.Pt s u x → N.Pt (s ≫ c) u (x ≫ φ))
    {T : Scheme.{0}} {s : T ⟶ S} {v : T ⟶ (N.U ⊗ N.U).left} {z : T ⟶ G.left}
    (h : Prod N s v z) : Prod N (s ≫ c) v (z ≫ φ) := by
  obtain ⟨x, y, hx, hy, rfl⟩ := h
  have hx' := hN _ _ _ _ hx
  have hy' := hN _ _ _ _ hy
  obtain ⟨x₀, hx₀⟩ := pt_exists N (pt_over N hx')
  obtain ⟨y₀, hy₀⟩ := pt_exists N (pt_over N hy')
  exact ⟨x₀, y₀, hx₀, hy₀, hφ.2 (Over.mk s) x y x₀ y₀ (pt_unique N hx₀ hx') (pt_unique N hy₀ hy')⟩

theorem law_of_isAffineQuotient {Γ : Type} [Group Γ] [Finite Γ] {α : Γ →* Aut S} (hq : IsAffineQuotient α π)
    (φ : Γ → (G.left ⟶ G.left)) (hφ : ∀ g, IsGrpPullback G G (α g).asIso.hom (φ g))
    (hN : ∀ g (T : Scheme.{0}) (s : T ⟶ S) (u : T ⟶ N.U.left) (x : T ⟶ G.left),
      N.Pt s u x → N.Pt (s ≫ (α g).asIso.hom) u (x ≫ φ g)) : N.Law := by
  have := N.smooth
  have := N.isOpen
  have hy : Flat (N.U ⊗ N.U).hom := by
    change Flat (pullback.fst N.U.hom N.U.hom ≫ N.U.hom)
    infer_instance
  have quot : ∀ {Y : Scheme.{0}} (y : Y ⟶ Sp R) [Flat y],
      IsAffineQuotient (pullbackAction α π hq.comp_eq y) (pullback.snd π y) := fun y _ =>
    hq.of_isPullback (IsPullback.of_hasPullback π y) (pullbackAction_fst α π hq.comp_eq y)
      (pullbackAction_snd α π hq.comp_eq y)
  have equiv : ∀ {Y : Scheme.{0}} (y : Y ⟶ Sp R) (j : Y ⟶ (N.U ⊗ N.U).left) (z : pullback π y ⟶ G.left),
      Prod N (pullback.fst π y) (pullback.snd π y ≫ j) z →
      ∀ g, (pullbackAction α π hq.comp_eq y g).asIso.hom ≫ z = z ≫ φ g := fun y j z hz g => by
    have h₁ := prod_comp N (pullbackAction α π hq.comp_eq y g).asIso.hom hz
    rw [pullbackAction_fst, pullbackAction_snd_assoc] at h₁
    exact prod_unique N h₁ (prod_act N (hφ g) (hN g) hz)
  obtain ⟨z₀, hz₁⟩ := prod_exists N (pullback.condition (f := π) (g := (N.U ⊗ N.U).hom))
  have hrange : ∀ g, pullback.map N.U.hom π N.U.hom π (𝟙 _) (α g).asIso.hom (𝟙 _) (by simp) (by simp [hq.comp_eq]) ≫ N.u
      = N.u ≫ φ g := fun g => by
    refine pt_unique N (s := pullback.snd N.U.hom π ≫ (α g).asIso.hom) (a := pullback.fst N.U.hom π)
      ⟨_, ?_, pullback.lift_snd _ _ _, rfl⟩
      (hN g _ _ _ _ ⟨𝟙 _, Category.id_comp _, Category.id_comp _, Category.id_comp _⟩)
    exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  obtain ⟨V, hV⟩ := (quot (N.U ⊗ N.U).hom).exists_preimage_eq (U := z₀ ⁻¹ᵁ N.u.opensRange) fun g w hw => by
    obtain ⟨w', hw'⟩ := hw
    change ((pullbackAction α π hq.comp_eq (N.U ⊗ N.U).hom g).asIso.hom ≫ z₀) w ∈ Set.range N.u
    rw [equiv _ (𝟙 _) z₀ (by rw [Category.comp_id]; exact hz₁) g, Scheme.Hom.comp_apply, ← hw',
      ← Scheme.Hom.comp_apply, ← hrange g, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  let y : V.toScheme ⟶ Sp R := V.ι ≫ (N.U ⊗ N.U).hom
  let k : pullback π y ⟶ pullback π (N.U ⊗ N.U).hom :=
    pullback.lift (pullback.fst π y) (pullback.snd π y ≫ V.ι) (by rw [pullback.condition, Category.assoc])
  have hk : k ≫ pullback.snd _ _ = pullback.snd π y ≫ V.ι := pullback.lift_snd _ _ _
  have hz : Prod N (pullback.fst π y) (pullback.snd π y ≫ V.ι) (k ≫ z₀) := by
    have := prod_comp N k hz₁
    rwa [hk, pullback.lift_fst] at this
  have hsub : Set.range (k ≫ z₀) ⊆ Set.range N.u := by
    rintro _ ⟨w, rfl⟩
    have : k w ∈ pullback.snd π (N.U ⊗ N.U).hom ⁻¹ᵁ V := by
      change (k ≫ pullback.snd π (N.U ⊗ N.U).hom) w ∈ V
      rw [hk, Scheme.Hom.comp_apply]
      exact (pullback.snd π y w).2
    rw [hV] at this
    exact this
  let l := IsOpenImmersion.lift N.u (k ≫ z₀) hsub
  have hl : l ≫ N.u = k ≫ z₀ := IsOpenImmersion.lift_fac _ _ _
  have hf : N.Pt (pullback.fst π y) (l ≫ pullback.fst _ _) (k ≫ z₀) :=
    ⟨l, rfl, by rw [← N.u_over, ← Category.assoc, hl, prod_over N hz], hl⟩
  obtain ⟨m, hm⟩ := (quot y).exists_comp_eq (l ≫ pullback.fst _ _) fun g => by
    have h₁ := pt_comp N (pullbackAction α π hq.comp_eq y g).asIso.hom hf
    rw [equiv y V.ι _ hz g] at h₁
    exact pt_unique_left N h₁ (hN g _ _ _ _ hf)
  refine ⟨V, m, fun z hz₀ => ?_, (quot y).hom_ext ?_, fun T v s a b ha hb => ?_⟩
  · obtain ⟨w, rfl⟩ := (quot (N.U ⊗ N.U).hom).surjective.surj z
    change w ∈ pullback.snd π (N.U ⊗ N.U).hom ⁻¹ᵁ V
    rw [hV]
    refine N.all (z₀ w) ?_
    rw [← hz₀, ← Scheme.Hom.comp_apply z₀, prod_over N hz₁, ← Scheme.Hom.comp_apply, pullback.condition,
      Scheme.Hom.comp_apply]
  · rw [← Category.assoc, hm, ← pt_over N hf, pullback.condition]
  · have hs : s ≫ π = v ≫ y := by
      rw [pt_over N ha, Category.assoc, Category.assoc]
      exact congrArg (fun t => v ≫ V.ι ≫ t) (Over.w (fst N.U N.U))
    have h₁ := pt_comp N (pullback.lift s v hs) hf
    have h₂ := prod_comp N (pullback.lift s v hs) hz
    rw [pullback.lift_fst, pullback.lift_snd_assoc] at h₂
    have h₃ : Prod N s (v ≫ V.ι) (a * b).left :=
      ⟨a, b, by rw [Category.assoc]; exact ha, by rw [Category.assoc]; exact hb, rfl⟩
    rw [← hm, pullback.lift_fst, pullback.lift_snd_assoc, prod_unique N h₂ h₃] at h₁
    exact h₁

end

end GlobalTheory.Mum.LawDesc

namespace GlobalTheory.Mum

theorem law_of_galAct_invariant : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U'), ∀ N : Near (spMap ρ) G', (∀ σ (T : Scheme.{0}) (s : T ⟶ Sp R') (u : T ⟶ N.U.left) (x : T ⟶ G'.left), N.Pt s u x → N.Pt (s ≫ spMap (Gal.hom σ)) u (x ≫ a.act σ)) → N.Law := by
  intro R _ _ _ _ R' _ _ _ ρ hρ hG D D' hD A' G' _ _ _ U' a N hN
  have := hG.1
  let _ : Algebra R R' := ρ.toAlgebra
  let _ : MulSemiringAction (R' ≃+* R') R' := RingAut.applyMulSemiringAction
  let _ : MulSemiringAction (Gal ρ) R' := Subgroup.mulSemiringAction _
  have : SMulCommClass (Gal ρ) R R' := ⟨fun σ r x => by
    change σ.1 (ρ r * x) = ρ r * σ.1 x
    rw [map_mul, σ.2 r]⟩
  have : FaithfulSMul R R' := (faithfulSMul_iff_algebraMap_injective _ _).2 hρ.2.1
  have : Algebra.IsInvariant R R' (Gal ρ) := ⟨fun x hx => hG.2 x fun σ hσ => hx ⟨σ, hσ⟩⟩
  have hq : IsAffineQuotient (specAction (Gal ρ) R') (spMap ρ) := isAffineQuotient_spec R R'
  have e : ∀ σ : Gal ρ, (specAction (Gal ρ) R' σ).asIso.hom = spMap (Gal.hom σ⁻¹) := fun σ => by
    rw [specAction_hom]; rfl
  refine LawDesc.law_of_isAffineQuotient N hq (fun σ => a.act σ⁻¹) (fun σ => ?_) fun σ => ?_
  · rw [e]; exact a.cart σ⁻¹
  · rw [e]; exact hN σ⁻¹

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

theorem _root_.GlobalTheory.T.generates_of_close_localEquation_classicalPoint :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω]
      (M₁ M : RatModel o Ω) (π : M.Z ⟶ M₁.Z),
      M₁.IsHom M (AlgHom.id o Ω) π →
      ∀ (U : M.Z.Opens) (D : EffCartierData M.Z),
        (∀ x ∈ (GlobalTheory.EffCartierData.idealSheaf D).support, x ∉ U) →
        ∀ (x : M.Z) (p : ℕ) [Fact p.Prime] (y₀ : Sp (OO p) ⟶ M.Z),
          M.Cen U x y₀ → ∀ f, EqAt M D x f →
          ∃ k : ℕ, ∀ (G b : M₁.O (π x)),
            ‖RatModel.val M (gPt p ≫ y₀) ((G : Ω) + b)‖ = ‖RatModel.val M (gPt p ≫ y₀) f‖ →
            b ∈ Ideal.span {c : M₁.O (π x) | ¬ IsUnit c} ^ k →
            (G : Ω) / f ∈ M.O x → (G : Ω) ≠ 0 ∧ f / G ∈ M.O x := by
  intro o Ω _ _ _ _ M₁ M π hπ U D hD x p _ y₀ hy f hf
  obtain ⟨i, hxi, rfl⟩ := hf
  set F : Ω := valF M.pt (D.U i) (D.f i)
  set y : Sp (PadicAlgCl p) ⟶ M.Z := gPt p ≫ y₀ with hydef

  have hFO : F ∈ M.O x := RatModel.valF_mem_O hxi _
  have hwx : y (IsLocalRing.closedPoint (PadicAlgCl p)) ⤳ x := RatModel.gPt_specializes hy.1 _
  have hwU : y (IsLocalRing.closedPoint (PadicAlgCl p)) ∈ U := hy.2 ⟨_, rfl⟩
  have hwi : y (IsLocalRing.closedPoint (PadicAlgCl p)) ∈ D.U i := hwx.mem_open (D.U i).isOpen hxi
  have hwb : y (IsLocalRing.closedPoint (PadicAlgCl p)) ∈ M.Z.basicOpen (D.f i) := by
    by_contra h
    exact hD _ ((D.mem_support_iff i hwi).2 h) hwU
  have hF0 : RatModel.val M y F ≠ 0 :=
    (RatModel.val_ne_zero_iff (RatModel.range_eq_singleton y (IsLocalRing.closedPoint (PadicAlgCl p)))
      ⟨_, RatModel.valF_mem_O hwi _⟩).2 ((RatModel.isUnit_valF_iff hwi (D.f i)).2 hwb)
  have hFpos : 0 < ‖RatModel.val M y F‖₊ := nnNorm_pos.2 hF0

  have hle : M₁.O (π x) ≤ M.O x := fun c hc => hπ.map_mem_O hc
  let v : M₁.O (π x) →+* PadicAlgCl p :=
    (RatModel.valHomOf y x (RatModel.gPt_specializes hy.1)).comp (Subalgebra.inclusion hle).toRingHom
  have hv_apply : ∀ c : M₁.O (π x), v c = RatModel.val M y c := fun c => rfl
  have hv1 : ∀ c, ‖v c‖₊ ≤ 1 := fun c => by
    rw [← NNReal.coe_le_coe, coe_nnNorm, NNReal.coe_one, hv_apply]
    exact RatModel.norm_val_le_one hy.1 (hle c.2)
  have hvlt : ∀ c : M₁.O (π x), ¬ IsUnit c → ‖v c‖₊ < 1 := by
    intro c hc
    have hc' : (c : Ω) ∈ M₁.O (π (y (IsLocalRing.closedPoint (PadicAlgCl p)))) :=
      RatModel.O_le_of_specializes (hwx.map π.continuous) c.2
    have e := hπ.val_comp y (IsLocalRing.closedPoint (PadicAlgCl p)) hc'
    have hc0 : (y₀ ≫ π) (cPt p) = π x := by rw [Scheme.Hom.comp_apply, hy.1]
    have h1 := (RatModel.norm_val_lt_one_iff hc0 c.2).2 hc
    rw [← Category.assoc, ← hydef, e] at h1
    rw [← NNReal.coe_lt_coe, coe_nnNorm, NNReal.coe_one, hv_apply]
    exact h1

  have : IsDedekindDomain o := ArithBase.ded (Ω := Ω)
  have := M₁.lft
  have : IsLocallyNoetherian M₁.Z := LocallyOfFiniteType.isLocallyNoetherian M₁.s
  have : IsNoetherianRing (M₁.O (π x)) := isNoetherianRing_of_ringEquiv _ (M₁.stalkEquiv (π x))
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian (maximalIdeal (M₁.O (π x)))
  set ρ : NNReal := s.sup fun c => ‖v c‖₊
  have hρ : ρ < 1 := by
    refine (Finset.sup_lt_iff (by simp)).2 fun c hc => hvlt c ?_
    have : c ∈ maximalIdeal (M₁.O (π x)) := hs ▸ Submodule.subset_span hc
    exact (mem_maximalIdeal c).1 this
  have hm : ∀ c ∈ maximalIdeal (M₁.O (π x)), ‖v c‖₊ ≤ ρ := by
    rw [← hs]
    exact nnnorm_le_of_mem_span v hv1 fun c hc => Finset.le_sup (f := fun c => ‖v c‖₊) hc
  have hspan : Ideal.span {c : M₁.O (π x) | ¬ IsUnit c} = maximalIdeal (M₁.O (π x)) := by
    have : {c : M₁.O (π x) | ¬ IsUnit c} = (maximalIdeal (M₁.O (π x)) : Set (M₁.O (π x))) :=
      Set.ext fun c => (mem_maximalIdeal c).symm
    rw [this, Ideal.span_eq]
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hFpos hρ
  refine ⟨k, fun G b hGb hb hGf => ?_⟩

  rw [hspan] at hb
  have hbk : ‖RatModel.val M y b‖₊ < ‖RatModel.val M y F‖₊ :=
    lt_of_le_of_lt (nnnorm_le_pow_of_mem_pow v hv1 hm k b hb) hk
  have hadd : RatModel.val M y ((G : Ω) + b) = RatModel.val M y G + RatModel.val M y b :=
    RatModel.val_add (RatModel.gPt_specializes hy.1) (hle G.2) (hle b.2)
  have hGb' : ‖RatModel.val M y G + RatModel.val M y b‖₊ = ‖RatModel.val M y F‖₊ := by
    rw [← hadd]
    exact NNReal.eq hGb
  have hG : ‖RatModel.val M y G‖₊ = ‖RatModel.val M y F‖₊ := by
    refine le_antisymm ?_ ?_
    · have e : RatModel.val M y G = (RatModel.val M y G + RatModel.val M y b) + -RatModel.val M y b := by ring
      rw [e]
      refine (IsUltrametricDist.nnNorm_add_le_max _ _).trans (max_le hGb'.le ?_)
      rw [nnNorm_neg]
      exact hbk.le
    · rw [← hGb']
      refine (IsUltrametricDist.nnNorm_add_le_max _ _).trans (max_le le_rfl ?_)
      by_contra h
      push Not at h
      have := (IsUltrametricDist.nnNorm_add_le_max (RatModel.val M y G) (RatModel.val M y b)).trans
        (max_le h.le le_rfl)
      rw [hGb'] at this
      exact absurd hbk (not_lt.2 this)
  have hG0 : (G : Ω) ≠ 0 := by
    intro h
    rw [h, RatModel.val_zero, nnNorm_zero] at hG
    exact hFpos.ne hG
  have hFne : F ≠ 0 := by
    intro h
    rw [h, RatModel.val_zero] at hF0
    exact hF0 rfl
  refine ⟨hG0, ?_⟩
  have hmul : RatModel.val M y ((G : Ω) / F * F) = RatModel.val M y ((G : Ω) / F) * RatModel.val M y F :=
    RatModel.val_mul (RatModel.gPt_specializes hy.1) hGf hFO
  rw [div_mul_cancel₀ _ hFne] at hmul
  have hq : ‖RatModel.val M y ((G : Ω) / F)‖₊ = 1 := by
    have h2 : ‖RatModel.val M y ((G : Ω) / F)‖₊ * ‖RatModel.val M y F‖₊ = 1 * ‖RatModel.val M y F‖₊ := by
      rw [one_mul, ← nnNorm_mul, ← hmul, hG]
    exact mul_right_cancel₀ hFpos.ne' h2
  have hq' : ‖RatModel.val M (gPt p ≫ y₀) ((G : Ω) / F)‖ = 1 := by
    rw [← coe_nnNorm]
    exact congrArg NNReal.toReal hq
  have hu := (RatModel.isUnit_O_iff _).1 ((RatModel.norm_val_eq_one_iff hy.1 hGf).1 hq')
  simpa [inv_div] using hu.2
end

section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

namespace GlobalTheory.ScalarCuspTwist

theorem exists_scalar_cusp_indefinite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → 1 ≤ Dw.p → 1 ≤ Dw.q → ¬ (∃ m : ℕ, 1 ≤ m ∧ m ^ 4 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.f E ∧ (ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) ^ 2 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ∧ 16 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ∧ (Dw.p ≤ m ∨ Dw.q ≤ m)) → ∀ (σ : c.F →+* ℂ), GoodEmb c σ → ∀ (Z : Comp Xo c), ∃ n₀ : ℕ, 0 < n₀ ∧ Even n₀ ∧ ∃ f₀ ∈ cusp Xo c U 0 n₀, ∃ z ∈ framesOn (U σ) Z, rdU (U σ) f₀ z.1 z.2 ≠ 0 := by
  intro E _ _ _ H Dw l Xo c r U x hL hp hq _ σ hσ Z
  exact exists_scalar_of_models (GlobalTheory.T.exists_nonzero_cuspSection_large_evenScalarWeight E r) hL hp hq hσ Z

end GlobalTheory.ScalarCuspTwist
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.isAnalyticSNC_of_algebraicSNC_section : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (D : ℕ), IsProjOver p → SmoothOfRelativeDimension D p → ∀ (A : FinHolAtlas D (CxPts p σ)), IsAlgAtlas A → ∀ (M : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (r : ℕ) (z : Fin r → X), Function.Injective z → (∀ a, Order.coheight (z a) = 1) → ((nonzeroLocus s : Set X)ᶜ = ⋃ a, closure {z a}) → (∀ x : X, FinalTheorems.LSncAt X (fun a => (Closeds.closure {z a})) x) → IsSNC A M.φ.locPot (M.φ.locSec (secVal p σ s)) (fun a => ((divOfSec M.φ.isLB s hs).mult (z a)).toNat) (fun a => Set.range (ptMap (closι (z a)) rfl σ)) := by
  first | exact @GlobalTheory.SecSnc.isSNC_locSec | exact GlobalTheory.SecSnc.isSNC_locSec | (intros; apply GlobalTheory.SecSnc.isSNC_locSec <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.exists_adaptedLieBasis_torusExtensionModel : AllVC fun {V} _ _ _ {D} {A} {G} _ _ U {C} _ _ {N} ν => ∃ (vB : Fin D.toPre.P.g → (epsR V ⟶ D.toPre.P.A)) (r : ℕ) (bX : Module.Basis (Fin r) ℤ N.X) (σ : Fin A.g ≃ Fin D.toPre.P.g ⊕ Fin r) (y : Fin A.g → (epsR V ⟶ G)) (gm₀ : Fin A.g → GtPt D.toPre (epsR V)) (gm : Fin A.g → GtPt D.toPre (TE V C)), IsLieBasis y ∧ Adapted ν vB bX σ gm ∧ ∀ j, TanRel U.toUnifPre (y j) (gm₀ j) ∧ GtTan (gm₀ j) ∧ GtPt.IsPull (spMap (dualMap (toF V C))) (gm₀ j) (gm j) := by
  first | exact @GlobalTheory.MBLow.Adapt.main | exact GlobalTheory.MBLow.Adapt.main | (intros; apply GlobalTheory.MBLow.Adapt.main <;> assumption)
end

module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle399
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle402
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.standardOpenCoordinateRing_isFractionRing_isNoetherianRing : ∀ (k : Type) [Field k] (F : Type) [Field F] [Algebra k F] (d : ℕ) (x : Fin (d + 1) → F), IsPd k x → ∀ I : Finset (Fin (d + 1)), I.Nonempty → IsFractionRing (rA k x I) F ∧ IsNoetherianRing (rA k x I) := by
  first | (exact @GlobalTheory.PD.rA_isFractionRing_isNoetherianRing) | (exact GlobalTheory.PD.rA_isFractionRing_isNoetherianRing) | (intros; apply GlobalTheory.PD.rA_isFractionRing_isNoetherianRing  <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct

namespace GlobalTheory.HTPair.QuotIsog

variable {p : ℕ} {O : Type} [CommRing O] {G H : PDivGroup p O} (τ : QuotTower G)

theorem j_injective (m : ℕ) : Function.Injective (τ.j m) := fun a b h => by
  rw [← τ.ρ_j m a, ← τ.ρ_j m b, h]

theorem pDivSubgroupQuotientTower_r_s_eq_s_res (m : ℕ) (a : G.A (m + 1)) : τ.r m (τ.s (m + 1) a) = τ.s m (G.res m a) := by
  apply j_injective τ m
  rw [τ.j_r, τ.j_s, τ.j_s, G.res_mulP, G.mulP_res]

theorem s_res_j (m : ℕ) (b : τ.B m) : τ.s m (G.res m (τ.j m b)) = mulBy O _ p b := by
  apply j_injective τ m
  rw [τ.j_s, G.mulP_res, map_mulBy]

theorem ker_le (m : ℕ) : torsionIdeal (R := O) (A := τ.B m) (p ^ m) ≤
    RingHom.ker (((G.res m).comp (τ.j m) : τ.B m →ₐc[O] G.A m) : τ.B m →ₐ[O] G.A m) := by
  refine (kerIdeal_le_ker_iff _ _).2 fun c => ?_
  change ((G.res m).comp (τ.j m)) (mulBy O _ (p ^ m) c) = _
  rw [map_mulBy, G.mulBy_pow_self, CoalgHomClass.counit_comp_apply]

variable [Fact p.Prime]

def toQuot (q : ∀ m, τ.B m →ₐc[O] H.A m) (hs : ∀ m, Function.Surjective (q m))
    (hk : ∀ m, RingHom.ker (q m) = torsionIdeal (R := O) (A := τ.B m) (p ^ m))
    (hc : ∀ m b, H.res m (q (m + 1) b) = q m (τ.r m b)) : G ⟶ H where
  app m := liftSurj (q m) (hs m) ((G.res m).comp (τ.j m)) ((hk m).le.trans (ker_le τ m))
  comm n := BialgHom.ext fun c => by
    obtain ⟨b, rfl⟩ := hs (n + 1) c
    rw [BialgHom.comp_apply, BialgHom.comp_apply, hc, liftSurj_apply, liftSurj_apply,
      BialgHom.comp_apply, BialgHom.comp_apply, ← τ.j_r]

theorem toQuot_app_q (q : ∀ m, τ.B m →ₐc[O] H.A m) (hs : ∀ m, Function.Surjective (q m))
    (hk : ∀ m, RingHom.ker (q m) = torsionIdeal (R := O) (A := τ.B m) (p ^ m))
    (hc : ∀ m b, H.res m (q (m + 1) b) = q m (τ.r m b)) (m : ℕ) (b : τ.B m) :
    (toQuot τ q hs hk hc).app m (q m b) = G.res m (τ.j m b) :=
  liftSurj_apply ..

def fromQuot (q : ∀ m, τ.B m →ₐc[O] H.A m)
    (hc : ∀ m b, H.res m (q (m + 1) b) = q m (τ.r m b)) : H ⟶ G where
  app m := (q m).comp (τ.s m)
  comm n := BialgHom.ext fun a => by
    change H.res n (q (n + 1) (τ.s (n + 1) a)) = q n (τ.s n (G.res n a))
    rw [hc, pDivSubgroupQuotientTower_r_s_eq_s_res]

end GlobalTheory.HTPair.QuotIsog
end
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.CechDR

variable {X X' : Scheme.{0}}

theorem Pair.exists_basicOpen (φ : X' ⟶ X) (W : X'.affineOpens) {x : X'} (hx : x ∈ W.1) :
    ∃ (p : Pair φ) (f : Γ(X', W.1)), p.1.1.1 = X'.basicOpen f ∧ x ∈ p.1.1.1 := by
  obtain ⟨U, hU, hxU, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (show φ.base x ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨f, hf, hxf⟩ := W.2.exists_basicOpen_le (V := W.1 ⊓ φ ⁻¹ᵁ U) ⟨x, hx, hxU⟩ hx
  exact ⟨⟨(⟨X'.basicOpen f, W.2.basicOpen f⟩, ⟨U, hU⟩), hf.trans inf_le_right⟩, f, rfl, hxf⟩

theorem Pair.exists_le_le (φ : X' ⟶ X) (p q : Pair φ) {x : X'} (hx : x ∈ p.1.1.1 ⊓ q.1.1.1) :
    ∃ r : Pair φ, r ≤ p ∧ r ≤ q ∧ x ∈ r.1.1.1 := by
  have hy : φ.base x ∈ p.1.2.1 ⊓ q.1.2.1 := ⟨p.2 hx.1, q.2 hx.2⟩
  obtain ⟨U, hU, hxU, hUle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hy
  obtain ⟨U', hU', hxU', hU'le⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X'.isBasis_affineOpens
    (show x ∈ p.1.1.1 ⊓ q.1.1.1 ⊓ φ ⁻¹ᵁ U from ⟨hx, hxU⟩)
  refine ⟨⟨(⟨U', hU'⟩, ⟨U, hU⟩), hU'le.trans inf_le_right⟩, ?_, ?_, hxU'⟩
  · exact ⟨hU'le.trans (inf_le_left.trans inf_le_left), hUle.trans inf_le_left⟩
  · exact ⟨hU'le.trans (inf_le_left.trans inf_le_right), hUle.trans inf_le_right⟩

end GlobalTheory.CechDR

namespace GlobalTheory.CechDR
open Opposite
variable {R' : Type} [CommRing R'] {X X' : Scheme.{0}}

theorem Pair.exists_le (φ : X' ⟶ X) (W : X'.affineOpens) {x : X'} (hx : x ∈ W.1) :
    ∃ (p : Pair φ) (hp : p.1.1 ≤ W), x ∈ p.1.1.1 := by
  obtain ⟨p, f, e, hxp⟩ := Pair.exists_basicOpen φ W hx
  exact ⟨p, show p.1.1.1 ≤ W.1 from e ▸ X'.basicOpen_le f, hxp⟩

theorem sec_eq_of_pair (φ : X' ⟶ X) (s' : X' ⟶ Sp R') (W : X'.affineOpens)
    (a b : (OAff s').obj (op W))
    (h : ∀ (p : Pair φ) (hp : p.1.1 ≤ W), mp (OAff s') (homOfLE hp).op a = mp (OAff s') (homOfLE hp).op b) :
    a = b := by
  refine TopCat.Presheaf.section_ext X'.sheaf W.1 a b fun x hx ↦ ?_
  obtain ⟨p, hp, hxp⟩ := Pair.exists_le φ W hx
  have e : (X'.presheaf.germ p.1.1.1 x hxp).hom ((X'.presheaf.map (homOfLE (show p.1.1.1 ≤ W.1 from hp)).op).hom a) =
      (X'.presheaf.germ p.1.1.1 x hxp).hom ((X'.presheaf.map (homOfLE (show p.1.1.1 ≤ W.1 from hp)).op).hom b) :=
    congrArg _ (h p hp)
  have k := X'.presheaf.germ_res (homOfLE (show p.1.1.1 ≤ W.1 from hp)) x hxp
  exact (congrArg (fun t ↦ t.hom a) k).symm.trans (e.trans (congrArg (fun t ↦ t.hom b) k))

end GlobalTheory.CechDR
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CechDR

theorem exists_pair_below_two : ∀ {R' : Type} [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X) (s' : X' ⟶ Sp R'), (∀ (t₁ t₂ : (Pair φ)ᵒᵖ) (S : AffOp X'), ((pairFst φ).obj t₁ ⟶ S) → ((pairFst φ).obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → (OAff s').obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : AffOp X') (u : S ⟶ S'), IsUnit (mp (OAff s') u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty ((pairFst φ).obj t₃ ⟶ S')) := by
  intro R' _ X X' φ s' t₁ t₂ S h₁ h₂
  have hS₁ : S.unop.1 ≤ t₁.unop.1.1.1 := leOfHom h₁.unop
  have hS₂ : S.unop.1 ≤ t₂.unop.1.1.1 := leOfHom h₂.unop
  let B : Set Γ(X', S.unop.1) := {g | ∃ W : X.affineOpens, W.1 ≤ t₁.unop.1.2.1 ∧
    W.1 ≤ t₂.unop.1.2.1 ∧ X'.basicOpen g ≤ φ ⁻¹ᵁ W.1}
  have hB : Ideal.span B = ⊤ := by
    refine (S.unop.2.self_le_iSup_basicOpen_iff).1 fun x hx ↦ ?_
    have hx₁ : φ.base x ∈ t₁.unop.1.2.1 := t₁.unop.2 (hS₁ hx)
    have hx₂ : φ.base x ∈ t₂.unop.1.2.1 := t₂.unop.2 (hS₂ hx)
    obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset (x := φ.base x)
      (U := t₁.unop.1.2.1 ⊓ t₂.unop.1.2.1) ⟨hx₁, hx₂⟩
    obtain ⟨f, hf, hxf⟩ := S.unop.2.exists_basicOpen_le (V := S.unop.1 ⊓ φ ⁻¹ᵁ W)
      ⟨x, hx, hxW⟩ hx
    have hfB : f ∈ B := ⟨⟨W, hW⟩, fun y hy ↦ (hWV hy).1, fun y hy ↦ (hWV hy).2,
      hf.trans inf_le_right⟩
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, hfB⟩, hxf⟩
  obtain ⟨s0, hs0, hspan⟩ := (Ideal.span_eq_top_iff_finite B).1 hB
  refine ⟨s0.card, fun i ↦ (s0.equivFin.symm i).1, ?_, fun i S' u hu ↦ ?_⟩
  · have hsp : Ideal.span (Set.range fun i ↦ ((s0.equivFin.symm i).1 : Γ(X', S.unop.1))) = ⊤ := by
      rw [eq_top_iff, ← hspan]
      exact Ideal.span_mono fun x hx ↦ ⟨s0.equivFin ⟨x, hx⟩, by simp⟩
    exact hsp
  · have hbB : (s0.equivFin.symm i).1 ∈ B := hs0 (s0.equivFin.symm i).2
    obtain ⟨W, hW₁, hW₂, hW⟩ := hbB
    set g : Γ(X', S.unop.1) := (s0.equivFin.symm i).1 with hg
    change IsUnit (X'.presheaf.map (homOfLE (show S'.unop.1 ≤ S.unop.1 from leOfHom u.unop)).op g) at hu
    have hS' : S'.unop.1 ≤ X'.basicOpen g := by
      have := Scheme.basicOpen_of_isUnit X' hu
      rw [Scheme.basicOpen_res] at this
      rw [← this]; exact inf_le_right
    let t₃ : Pair φ := ⟨(⟨X'.basicOpen g, S.unop.2.basicOpen g⟩, W), hW⟩
    refine ⟨Opposite.op t₃, ⟨(homOfLE ?_).op⟩, ⟨(homOfLE ?_).op⟩, ⟨(homOfLE ?_).op⟩⟩
    · exact ⟨(X'.basicOpen_le g).trans hS₁, hW₁⟩
    · exact ⟨(X'.basicOpen_le g).trans hS₂, hW₂⟩
    · exact hS'

end GlobalTheory.CechDR
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CechDR

theorem pair_cover_affine {R' : Type} [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X)
    (s' : X' ⟶ Sp R') : ∀ T : AffOp X', ∃ (n : ℕ) (b : Fin n → (OAff s').obj T),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X') (u : T ⟶ S),
        IsUnit (mp (OAff s') u (b i)) →
          ∃ (t : (Pair φ)ᵒᵖ) (v : T ⟶ (pairFst φ).obj t) (w : (pairFst φ).obj t ⟶ S), v ≫ w = u := by
  intro T
  have hT : IsAffineOpen T.unop.1 := T.unop.2
  let G : Set Γ(X', T.unop.1) :=
    {f | ∃ V : X.affineOpens, X'.basicOpen f ≤ φ ⁻¹ᵁ V.1}
  have hG : Ideal.span G = ⊤ := by
    rw [← hT.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (φ x)) isOpen_univ
    obtain ⟨f, hf, hxf⟩ := hT.exists_basicOpen_le (V := φ ⁻¹ᵁ V) ⟨x, hxV⟩ hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, ⟨⟨V, hV⟩, hf⟩⟩, hxf⟩
  obtain ⟨F, hFG, hF⟩ := (Ideal.span_eq_top_iff_finite G).1 hG
  refine ⟨F.card, fun i ↦ (F.equivFin.symm i).1, ?_, ?_⟩
  · have hR : Set.range (fun i : Fin F.card ↦ (F.equivFin.symm i).1) = (F : Set Γ(X', T.unop.1)) := by
      ext f
      constructor
      · rintro ⟨i, rfl⟩; exact (F.equivFin.symm i).2
      · intro hf; exact ⟨F.equivFin ⟨f, hf⟩, by simp⟩
    exact hR ▸ hF
  · intro i S u hu
    obtain ⟨V, hV⟩ := hFG (F.equivFin.symm i).2
    set f : Γ(X', T.unop.1) := (F.equivFin.symm i).1
    have hW : IsAffineOpen (X'.basicOpen f) := hT.basicOpen f
    have hWT : X'.basicOpen f ≤ T.unop.1 := X'.basicOpen_le f
    let t : Pair φ := ⟨(⟨_, hW⟩, V), hV⟩
    have hSW : S.unop.1 ≤ X'.basicOpen f := by
      have h1 : X'.basicOpen (X'.presheaf.map (homOfLE (leOfHom u.unop)).op f) = S.unop.1 :=
        X'.basicOpen_of_isUnit hu
      rw [Scheme.basicOpen_res] at h1
      rw [← h1]; exact inf_le_right
    refine ⟨Opposite.op t, (homOfLE (show (⟨_, hW⟩ : X'.affineOpens) ≤ T.unop from hWT)).op,
      (homOfLE (show S.unop ≤ (⟨_, hW⟩ : X'.affineOpens) from hSW)).op, ?_⟩
    exact Quiver.Hom.unop_inj (Subsingleton.elim _ _)

end GlobalTheory.CechDR
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CechDR

namespace GlobalTheory.CechDR

private theorem spc {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B)
    (g : B →+* C) : spMap (g.comp f) = spMap g ≫ spMap f :=
  Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)

private theorem spi {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B}
    (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem secPull_surjective_and_ker (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R)
    (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ X : Scheme.{0})
    (s₀ : X₀ ⟶ Sp R₀) (s : X ⟶ Sp R) (i : X₀ ⟶ X) (hpb : IsPullback i s₀ s (spMap π))
    (p : Pair i) (hp : i ⁻¹ᵁ p.1.2.1 = p.1.1.1) :
    Function.Surjective (secPull s s₀ p) ∧
      ∀ b, secPull s s₀ p b = 0 ↔ b ∈ I.map (algebraMap R (Sec s p.1.2.1)) := by
  set J : Ideal (Sec s p.1.2.1) := I.map (algebraMap R (Sec s p.1.2.1)) with hJ
  let q := Ideal.Quotient.mk J
  have hφ : ∀ r, secPull s s₀ p (algebraMap R _ r) = algebraMap R₀ _ (π r) :=
    (semiHom_secPull hpb.w p).map_algebraMap
  have hJker : ∀ a ∈ J, secPull s s₀ p a = 0 := by
    have : J ≤ RingHom.ker (secPull s s₀ p) := by
      rw [hJ, Ideal.map_le_iff_le_comap]
      intro r hr
      rw [← hk, RingHom.mem_ker] at hr
      rw [Ideal.mem_comap, RingHom.mem_ker, hφ, hr, map_zero]
    exact fun a ha ↦ this ha
  let τ : R₀ →+* (Sec s p.1.2.1 ⧸ J) := π.liftOfSurjective hπ
    ⟨q.comp (algebraMap R _), fun r hr ↦ by
      rw [hk] at hr
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hr)⟩
  have hτ : τ.comp π = q.comp (algebraMap R _) := RingHom.liftOfSurjective_comp _ _ _
  have hz : (spMap q ≫ affPt s p.1.2) ≫ s = spMap τ ≫ spMap π := by
    rw [Category.assoc, affPt_w, ← spc, ← spc, hτ]
  let w := hpb.lift _ _ hz
  have hw : w ≫ i = spMap q ≫ affPt s p.1.2 := hpb.lift_fst _ _ _
  haveI : IsOpenImmersion (affPt s₀ p.1.1) := p.1.1.2.isOpenImmersion_fromSpec
  haveI : IsOpenImmersion (affPt s p.1.2) := p.1.2.2.isOpenImmersion_fromSpec
  have hr : Set.range w ⊆ Set.range (affPt s₀ p.1.1) := by
    rintro _ ⟨x, rfl⟩
    have e : Set.range (affPt s₀ p.1.1) = p.1.1.1 := p.1.1.2.range_fromSpec
    have e' : Set.range (affPt s p.1.2) = p.1.2.1 := p.1.2.2.range_fromSpec
    rw [e, ← hp]
    change i (w x) ∈ (p.1.2.1 : Set X)
    rw [← e', ← Scheme.Hom.comp_apply, hw, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  let w' := IsOpenImmersion.lift (affPt s₀ p.1.1) w hr
  have hw' : w' ≫ affPt s₀ p.1.1 = w := IsOpenImmersion.lift_fac _ _ _
  let ψ : Sec s₀ p.1.1.1 →+* (Sec s p.1.2.1 ⧸ J) := (Spec.preimage w').hom
  have hψ : spMap ψ = w' := Spec.map_preimage w'
  have h1 : ψ.comp (secPull s s₀ p) = q := by
    apply spi
    rw [← cancel_mono (affPt s p.1.2), spc, Category.assoc, secPull_affPt, hψ, ← Category.assoc,
      hw', hw]
  let ψ' := Ideal.Quotient.lift J (secPull s s₀ p) hJker
  have h2 : ψ'.comp q = secPull s s₀ p := Ideal.Quotient.lift_comp_mk _ _ _
  haveI : IsClosedImmersion (spMap π) := IsClosedImmersion.spec_of_surjective _ hπ
  haveI : IsClosedImmersion i := MorphismProperty.of_isPullback hpb.flip this
  haveI : Mono (spMap (secPull s s₀ p) ≫ affPt s p.1.2) := by
    rw [secPull_affPt]; infer_instance
  haveI : Mono (spMap (secPull s s₀ p)) := mono_of_mono _ (affPt s p.1.2)
  have h3 : ψ'.comp ψ = RingHom.id _ := by
    apply spi
    rw [← cancel_mono (spMap (secPull s s₀ p)), ← spc, ← spc, RingHom.comp_assoc, h1, h2,
      RingHom.id_comp]
  refine ⟨fun b ↦ ?_, fun b ↦ ⟨fun hb ↦ ?_, hJker b⟩⟩
  · obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (ψ b)
    refine ⟨a, ?_⟩
    rw [← h2, RingHom.comp_apply, show q a = ψ b from ha]
    exact congrArg (fun f ↦ f b) h3
  · rw [← Ideal.Quotient.eq_zero_iff_mem]
    change q b = 0
    rw [← h1, RingHom.comp_apply, hb, map_zero]

end GlobalTheory.CechDR
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR

namespace GlobalTheory.CechDR.AffLoc

variable {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R}

abbrev TT (s : X ⟶ Sp R) : Type 1 := (IsTriv s).FullSubcategory

theorem π_bij (T : TT s) : Function.Bijective T.obj.π := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun b hb ↦ ?_, T.obj.surj⟩
  have h := (T.obj.ker b).1 hb
  rw [T.property] at h
  exact Ideal.mem_bot.1 h

def πe (T : TT s) : T.obj.B ≃+* T.obj.B₀ := RingEquiv.ofBijective T.obj.π (π_bij T)

def pt (T : TT s) : Sp T.obj.B ⟶ X := spMap ((πe T).symm : T.obj.B₀ →+* T.obj.B) ≫ T.obj.x

theorem pt_w (T : TT s) : pt T ≫ s = algStr R T.obj.B := by
  rw [pt, Category.assoc, T.obj.w, ← spMap_comp]
  congr 1
  ext r
  exact (πe T).symm_apply_apply (algebraMap R T.obj.B r)

abbrev affF (s : X ⟶ Sp R) : AffOp X ⥤ TT s where
  obj U := ⟨Thick.triv (Sec s U.unop.1) (affPt s U.unop) (affPt_w s U.unop), rfl⟩
  map {U V} a := ⟨Thick.trivHom (hx := affPt_w s U.unop)
    (T := Thick.triv (Sec s V.unop.1) (affPt s V.unop) (affPt_w s V.unop))
    (Sec.res s (leOfHom a.unop)) (affPt_res s (leOfHom a.unop))⟩
  map_id U := by
    apply ObjectProperty.hom_ext (IsTriv s)
    apply Thick.Hom.ext'
    ext b
    exact congrArg (fun q ↦ q.hom b) (X.presheaf.map_id (op U.unop.1))
  map_comp a b := by
    apply ObjectProperty.hom_ext (IsTriv s)
    apply Thick.Hom.ext'
    ext c
    exact Sec.res_res s (leOfHom a.unop) (leOfHom b.unop) c

abbrev thk (T : TT s) (p : Pair (pt T)) : TT s :=
  ⟨Thick.triv (Sec (algStr R T.obj.B) p.1.1.1) (affPt _ p.1.1 ≫ pt T)
    (by rw [Category.assoc, pt_w]; exact affPt_w _ p.1.1), rfl⟩

def secPullA (T : TT s) (p : Pair (pt T)) : Sec s p.1.2.1 →ₐ[R] Sec (algStr R T.obj.B) p.1.1.1 :=
  { secPull s (algStr R T.obj.B) p with
    commutes' := (semiHom_secPull (σ := RingHom.id R)
      (by rw [spMap_id, Category.comp_id, pt_w]) p).map_algebraMap }

def aM (T : TT s) (p : Pair (pt T)) : (affF s).obj (op p.1.2) ⟶ thk T p :=
  ⟨Thick.trivHom (hx := affPt_w s p.1.2) (T := (thk T p).obj) (secPullA T p) (secPull_affPt s _ p)⟩

theorem bM_pt (T : TT s) (p : Pair (pt T)) :
    spMap ((toSec R T.obj.B p.1.1).toRingHom.comp ((πe T).symm : T.obj.B₀ →+* T.obj.B)) =
      affPt (algStr R T.obj.B) p.1.1 ≫ spMap ((πe T).symm : T.obj.B₀ →+* T.obj.B) := by
  rw [spMap_comp, affPt_eq]
  rfl

abbrev fv (f : Z1 ((IsTriv s).ι ⋙ O (dp0 R) s)) {T T' : TT s} (a : T ⟶ T') : T'.obj.B := f.1 T T' a

def bM (T : TT s) (p : Pair (pt T)) : T ⟶ thk T p :=
  ⟨{ φ := toSec R T.obj.B p.1.1
     φ₀ := (toSec R T.obj.B p.1.1).toRingHom.comp ((πe T).symm : T.obj.B₀ →+* T.obj.B)
     comm := fun b ↦ congrArg (toSec R T.obj.B p.1.1) ((πe T).symm_apply_apply b)
     dp := isDPMorphism_of_eq_bot _ T.property _ _
     pt := (congrArg (· ≫ T.obj.x) (bM_pt T p)).trans (Category.assoc _ _ _) }⟩

def hSec (f : Z1 ((IsTriv s).ι ⋙ O (dp0 R) s)) (g : C0 (OAff s)) (T : TT s) (p : Pair (pt T)) :
    Sec (algStr R T.obj.B) p.1.1.1 :=
  secPullA T p (g (op p.1.2)) + fv f (aM T p) - fv f (bM T p)

end GlobalTheory.CechDR.AffLoc
end
end

section

open MeasureTheory ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.OriginBox
open GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx

variable {k : Type*} [Field k]

def auxiliaryVectorUniformizerExponent (a a' : ℤ) (c : ℕ) {n : Type*} : n ⊕ Fin c → ℤ
  | .inl _ => 0
  | .inr p => a * ((c : ℤ) - p) - a' * ((p : ℤ) + 1)

def vtxExp (a a' : ℤ) (c t x : ℕ) : ℤ :=
  if t ≤ x then a * ((c : ℤ) - ((x - t : ℕ) : ℤ)) - a' * (((x - t : ℕ) : ℤ) + 1) else 0

variable (G : Grid k)

def colDiag (ϖ : kˣ) (a a' : ℤ) (j : ℕ) : GL (Fin (G.rank (G.m, j))) k :=
  diagGL fun x => ϖ ^ vtxExp a a' (G.m - 1 - j) (topRank G j) x

def boxExp (a a' : ℤ) (j : Fin (G.m - 1))
    (v : StepVar (Fin (topRank G ((j : ℕ) + 1))) (G.m - 2 - j) (Fin (topRank G j))) : ℤ :=
  a - auxiliaryVectorUniformizerExponent a a' (G.m - 2 - j + 1) v.1.2 + auxiliaryVectorUniformizerExponent a a' (G.m - 2 - j) v.1.1

variable [ValuativeRel k]

def box (ϖ : kˣ) (a a' : ℤ) : Set (Vars G) :=
  Set.univ.pi fun j => Set.univ.pi fun v => {x : k | valuation k x ≤ valuation k ((ϖ ^ boxExp G a a' j v : kˣ) : k)}

variable {G}


omit [ValuativeRel k] in
theorem vtxExp_frame (a a' : ℤ) {t c b : ℕ} (h : t + c = b) (y : Fin t ⊕ Fin c) :
    vtxExp a a' c t (frame h y) = auxiliaryVectorUniformizerExponent a a' c y := by
  rcases y with x | p
  · simp [vtxExp, auxiliaryVectorUniformizerExponent, frame, finSumFinEquiv_apply_left, x.2]
  · simp [vtxExp, auxiliaryVectorUniformizerExponent, frame, finSumFinEquiv_apply_right]

end GlobalTheory.OriginBox
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_section_of_etale_surjective_of_SH : ∀ (A : Type) [CommRing A], SH A → ∀ (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of A)), Etale f → Surjective f → ∃ s : Spec (CommRingCat.of A) ⟶ Y, s ≫ f = 𝟙 _ := by
  first | exact @GlobalTheory.EtC.etale_surjective_section_of_SH | exact GlobalTheory.EtC.etale_surjective_section_of_SH | (intros; apply GlobalTheory.EtC.etale_surjective_section_of_SH <;> assumption)
end

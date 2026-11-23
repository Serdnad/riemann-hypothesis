module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle014
public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle031
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle002
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle027
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle073
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle023
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle024
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle026
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.exists_orthogonal_local_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (p q : ℕ) (ℓ : Nat.Primes) (x' : Fin p → D.La), p + q = D.p + D.q → (gramE D x').det ≠ 0 → (∀ j : E →+* ℂ_[ℓ], Real.log ‖j (gramE D x').det‖ = -(p : ℝ) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) → ∃ x : Fin p ⊕ Fin q → D.La, x ∘ Sum.inl = x' ∧ IsLocBasis (𝓞 E) ℓ x ∧ ∀ a b, sesq D (x (.inl a)) (x (.inr b)) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Relay.exists_orthogonal_local_basis | exact GlobalTheory.CompanionTheory.Relay.exists_orthogonal_local_basis | (intros; apply GlobalTheory.CompanionTheory.Relay.exists_orthogonal_local_basis <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.exists_local_basis' : ∀ (E : Type) [Field E] [NumberField E] (M : Type) [AddCommGroup M] [Module (𝓞 E) M] [Module.Finite (𝓞 E) M] [Module.IsTorsionFree (𝓞 E) M] (I : Type) [Fintype I] (ℓ : ℕ), ℓ.Prime → Fintype.card I = Module.finrank (𝓞 E) M → ∃ x : I → M, IsLocBasis (𝓞 E) ℓ x := by
  first | exact @GlobalTheory.CompanionTheory.Relay.exists_local_basis' | exact GlobalTheory.CompanionTheory.Relay.exists_local_basis' | (intros; apply GlobalTheory.CompanionTheory.Relay.exists_local_basis' <;> assumption)
end

section

set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal


theorem _root_.GlobalTheory.T.integral_fubini_study_sum_cone : ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
  (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (u : Fin n → ℂ),
  IsProjPrime W → IsChowForm W (e + 1) f → IsMultiHomog δ f → linForm u ∉ W →
    Integrable (fsSum h u (coneSet h W)) (gaussM (e + 1) n) ∧
      ∫ π, fsSum h u (coneSet h W) π ∂(gaussM (e + 1) n) =
        (gaussM (e + 1) n Set.univ).toReal * coneIntegral h W e (fsLog h u) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Short.Crofton.fsSum_crofton | exact GlobalTheory.CompanionTheory.Ar.Short.Crofton.fsSum_crofton | (intros; apply GlobalTheory.CompanionTheory.Ar.Short.Crofton.fsSum_crofton <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot

noncomputable section
namespace GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd

variable {S : Scheme.{0}} (G X : Over S) [GrpObj G] [ModObj G X]

theorem mem_orbit_iff {x y : X.left} : y ∈ orbit G X x ↔
    ∃ z, (snd G X).left z = x ∧ (γ[G, X] : G ⊗ X ⟶ X).left z = y := by
  constructor
  · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩

theorem orbit_symm {x y : X.left} (h : y ∈ orbit G X x) : x ∈ orbit G X y := by
  obtain ⟨σ, -, h1, h2⟩ := GlobalTheory.T.shear_iso_action_projection G X
  obtain ⟨z, rfl, rfl⟩ := (mem_orbit_iff G X).1 h
  refine (mem_orbit_iff G X).2 ⟨σ.left z, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, h1]
  · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, h2]

theorem orbit_hom {x y : X.left} (h : y ∈ orbit G X x) : X.hom y = X.hom x := by
  obtain ⟨z, rfl, rfl⟩ := (mem_orbit_iff G X).1 h
  have e : (γ[G, X] : G ⊗ X ⟶ X).left ≫ X.hom = (snd G X).left ≫ X.hom := (Over.w _).trans (Over.w _).symm
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, e]

theorem stable_of_forall (V : X.left.Opens) (h : ∀ y ∈ V, orbit G X y ⊆ V) :
    (γ[G, X] : G ⊗ X ⟶ X).left ⁻¹ᵁ V = (snd G X).left ⁻¹ᵁ V := by
  ext z
  constructor
  · intro hz
    exact h _ hz (orbit_symm G X ((mem_orbit_iff G X).2 ⟨z, rfl, rfl⟩))
  · intro hz
    exact h _ hz ((mem_orbit_iff G X).2 ⟨z, rfl, rfl⟩)

variable {G X} in
theorem isFinite_snd (hG : IsFiniteLocallyFree G.hom) : IsFinite (snd G X).left := by
  have := hG.1
  have h : IsFinite (pullback.snd G.hom X.hom) := inferInstance
  exact h

variable {G X} in
theorem orbit_finite (hG : IsFiniteLocallyFree G.hom) (x : X.left) : (orbit G X x).Finite := by
  have := isFinite_snd (X := X) hG
  exact ((snd G X).left.finite_preimage_singleton x).image _

variable {G X} in
theorem isOpen_saturated (hG : IsFiniteLocallyFree G.hom) (O : X.left.Opens) :
    IsOpen {y : X.left | orbit G X y ⊆ O} := by
  have := isFinite_snd (X := X) hG
  have hc : IsClosed ((snd G X).left '' ((γ[G, X] : G ⊗ X ⟶ X).left ⁻¹' (O : Set X.left)ᶜ)) :=
    (snd G X).left.isClosedMap _ (O.isOpen.isClosed_compl.preimage (γ[G, X] : G ⊗ X ⟶ X).left.continuous)
  convert hc.isOpen_compl using 1
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_image, Set.mem_preimage, not_exists, not_and]
  constructor
  · intro h z hz hy
    exact hz (h ((mem_orbit_iff G X).2 ⟨z, hy, rfl⟩))
  · intro h w hw
    obtain ⟨z, hz, rfl⟩ := (mem_orbit_iff G X).1 hw
    by_contra hn
    exact h z hn hz

theorem mem_basicOpen_appLE' {P Y : Scheme.{0}} (c : P ⟶ Y) (U : Y.Opens) (hc : ⊤ ≤ c ⁻¹ᵁ U) (f : Γ(Y, U)) (z : P) :
    z ∈ P.basicOpen ((c.appLE U ⊤ hc).hom f) ↔ c z ∈ Y.basicOpen f := by
  have key : P.basicOpen ((c.appLE U ⊤ hc).hom f) = c ⁻¹ᵁ Y.basicOpen f := by
    rw [Scheme.preimage_basicOpen, Scheme.Hom.appLE, CommRingCat.comp_apply, Scheme.basicOpen_res, top_inf_eq]
  rw [key]
  rfl

theorem exists_norm {P D : Scheme.{0}} [IsAffine P] [IsAffine D] (v : P ⟶ D)
    (hv : FiniteFreeHom v.appTop.hom) (e : Γ(P, ⊤)) :
    ∃ N : Γ(D, ⊤), ∀ y : D, y ∈ D.basicOpen N ↔ ∀ z : P, v z = y → z ∈ P.basicOpen e := by
  letI := v.appTop.hom.toAlgebra
  have h1 : Module.Free Γ(D, ⊤) Γ(P, ⊤) := hv.1
  have h2 : Module.Finite Γ(D, ⊤) Γ(P, ⊤) := hv.2
  refine ⟨Algebra.norm Γ(D, ⊤) e, GlobalTheory.T.basic_open_norm_fibre_iff v _ e fun p => ?_⟩
  rw [GlobalTheory.T.norm_not_mem_prime_iff e p.asIdeal p.isPrime]
  constructor
  · intro h q hq
    exact h q.asIdeal q.isPrime hq
  · intro h q hq hq'
    exact h ⟨q, hq⟩ hq'

theorem exists_stable_affine_nbhd : ∀ {S : Scheme.{0}} (G X : Over S) [GrpObj G] [ModObj G X], IsFiniteLocallyFree G.hom → ∀ (x : X.left) (U : X.left.Opens), IsAffineOpen U → orbit G X x ⊆ U → ∃ (V : X.left.Opens) (W : S.Opens), x ∈ V ∧ IsAffineOpen V ∧ IsAffineOpen W ∧ V ≤ X.hom ⁻¹ᵁ W ∧ (γ[G, X] : G ⊗ X ⟶ X).left ⁻¹ᵁ V = (snd G X).left ⁻¹ᵁ V := by
  intro S G X _ _ hG x U hU hxU
  have hfl := hG.1
  have hfl2 := hG.2.1
  have hfl3 := hG.2.2
  obtain ⟨W, hsW, hW, hfree⟩ := GlobalTheory.T.finite_flat_locally_free_affine G.hom (X.hom x)
  have htrans : ∀ {y w : X.left}, y ∈ orbit G X x → w ∈ orbit G X y → w ∈ orbit G X x :=
    fun {y w} => GlobalTheory.T.mem_orbit_trans G X x y w
  let O : X.left.Opens := U ⊓ X.hom ⁻¹ᵁ W
  have hxO : orbit G X x ⊆ O := fun y hy => ⟨hxU hy, by
    show X.hom y ∈ W
    rw [orbit_hom G X hy]; exact hsW⟩
  let V₀ : X.left.Opens := ⟨{y | orbit G X y ⊆ O}, isOpen_saturated hG O⟩
  have hV₀O : V₀ ≤ O := fun y hy => hy (GlobalTheory.T.mem_orbit_self' G X y)
  have hV₀U : V₀ ≤ U := hV₀O.trans inf_le_left
  have hxV₀ : orbit G X x ⊆ V₀ := fun y hy w hw => hxO (htrans hy hw)
  obtain ⟨f, hKf, hfV⟩ := GlobalTheory.T.finite_set_basic_open_affine U V₀ hU hV₀U _ (orbit_finite hG x) hxV₀
  let D : X.left.Opens := X.left.basicOpen f
  have hD : IsAffineOpen D := hU.basicOpen f
  have hDW : D ≤ X.hom ⁻¹ᵁ W := (hfV.trans hV₀O).trans inf_le_right
  have hsq : IsPullback (fst G X).left (snd G X).left G.hom X.hom :=
    IsPullback.of_hasPullback G.hom X.hom
  obtain ⟨h, u, hpb⟩ := GlobalTheory.T.pullback_restrict_open hsq W D hDW
  have := isFinite_snd (X := X) hG
  haveI : IsAffine D.toScheme := hD
  haveI : IsAffine W.toScheme := hW
  haveI : IsAffine (G.hom ⁻¹ᵁ W).toScheme := hW.preimage G.hom
  haveI : IsAffine ((snd G X).left ⁻¹ᵁ D).toScheme := hD.preimage (snd G X).left
  have hfree' := GlobalTheory.T.finite_free_pullback_affine hpb hfree
  let P' : (G ⊗ X).left.Opens := (snd G X).left ⁻¹ᵁ D
  let c : P'.toScheme ⟶ X.left := P'.ι ≫ (γ[G, X] : G ⊗ X ⟶ X).left
  have hc : ⊤ ≤ c ⁻¹ᵁ U := by
    rintro z -
    have hz : (snd G X).left z.1 ∈ D := z.2
    have h1 : (γ[G, X] : G ⊗ X ⟶ X).left z.1 ∈ orbit G X ((snd G X).left z.1) :=
      (mem_orbit_iff G X).2 ⟨z.1, rfl, rfl⟩
    exact (hfV hz h1).1
  obtain ⟨N, hN⟩ := exists_norm ((snd G X).left ∣_ D) hfree' ((c.appLE U ⊤ hc).hom f)
  let V : X.left.Opens := D.ι ''ᵁ (D.toScheme.basicOpen N)
  have hVmem : ∀ y, y ∈ V ↔ y ∈ D ∧ orbit G X y ⊆ D := by
    intro y
    show y ∈ D.ι '' (D.toScheme.basicOpen N : Set D.toScheme) ↔ _
    constructor
    · rintro ⟨y', hy', rfl⟩
      refine ⟨y'.2, fun w hw => ?_⟩
      obtain ⟨z, hz, rfl⟩ := (mem_orbit_iff G X).1 hw
      have hzP : z ∈ P' := by
        show (snd G X).left z ∈ D
        rw [hz]; exact y'.2
      have h1 := (hN y').1 hy' ⟨z, hzP⟩ (Subtype.ext ((morphismRestrict_base_coe _ _ _).trans hz))
      exact (mem_basicOpen_appLE' c U hc f _).1 h1
    · rintro ⟨hyD, ho⟩
      refine ⟨⟨y, hyD⟩, (hN ⟨y, hyD⟩).2 fun z hz => ?_, rfl⟩
      refine (mem_basicOpen_appLE' c U hc f _).2 ?_
      have h2 : (snd G X).left z.1 = y :=
        (morphismRestrict_base_coe _ _ z).symm.trans (congrArg Subtype.val hz)
      exact ho ((mem_orbit_iff G X).2 ⟨z.1, h2, rfl⟩)
  refine ⟨V, W, (hVmem x).2 ⟨hKf (GlobalTheory.T.mem_orbit_self' G X x), fun y hy => hKf hy⟩, ?_, hW, ?_, ?_⟩
  · exact ((isAffineOpen_top D.toScheme).basicOpen N).image_of_isOpenImmersion D.ι
  · exact fun y hy => hDW ((hVmem y).1 hy).1
  · refine stable_of_forall G X V fun y hy w hw => (hVmem w).2 ⟨((hVmem y).1 hy).2 hw, fun t ht => ?_⟩
    exact ((hVmem y).1 hy).2 (GlobalTheory.T.mem_orbit_trans G X y w t hw ht)

end GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.norm_map_restriction_compatible : ∀ {X Y : Scheme.{0}} (q : X ⟶ Y), IsFinite q → Flat q → LocallyOfFinitePresentation q → ∃ N : ∀ V : Y.Opens, Γ(X, q ⁻¹ᵁ V) →* Γ(Y, V), (∀ (V W : Y.Opens) (h : W ≤ V) (a : Γ(X, q ⁻¹ᵁ V)), (Y.presheaf.map (homOfLE h).op).hom (N V a) = N W ((X.presheaf.map (homOfLE (show q ⁻¹ᵁ W ≤ q ⁻¹ᵁ V from fun _ hx => h hx)).op).hom a)) ∧ ∀ (V : Y.Opens) (a : Γ(X, q ⁻¹ᵁ V)) (y : Y), y ∈ V → (y ∈ Y.basicOpen (N V a) ↔ ∀ x : X, q x = y → x ∈ X.basicOpen a) := by
  first | exact @GlobalTheory.CompanionTheory.FinFlatNorm.exists_norm_sheaf | exact GlobalTheory.CompanionTheory.FinFlatNorm.exists_norm_sheaf | (intros; apply GlobalTheory.CompanionTheory.FinFlatNorm.exists_norm_sheaf <;> assumption)
end

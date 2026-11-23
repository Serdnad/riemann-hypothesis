module

public import Development.WeilBound.CoreStatements.VolumeEquality.Bundle008
public import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle105
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle115
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle194
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GagaLineGeneratorEmbedding
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle120
public import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifGood
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle052
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle061
public import Development.WeilBound.CoreStatements.VolumeEquality.OnePieceA
public import Development.WeilBound.CoreStatements.VolumeEquality.OnePieceB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle004

@[expose] public section

section

noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory Limits NumberField MeasureTheory Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H} {Xo : Moduli D l}
  {c : Coeff l}

theorem spMap_injective {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem baseUnif_of_kUnif (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (sm : CMType H → CMType H ⊕ CMType H) (j j' n g : ℕ)
    (q : CMType H × Fin j × Fin j' ≃ Fin n) (U : ∀ κ, KUnif Y sm j j' n g q κ) :
    ∃ B : BaseUnif Y sm j j' n, B.Locc := by
  classical
  letI : Fintype (CMType H) := Subtype.fintype (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0)
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  haveI : ∀ κ, Finite (U κ).ι := fun κ => (U κ).fin
  let C : Type := Σ κ : c.F →+* ℂ, (U κ).ι
  obtain ⟨np, ⟨e⟩⟩ := Finite.exists_equiv_fin C
  let a : Fin np → C := e.symm
  have hκ : ∀ κ κ' : c.F →+* ℂ, κ.comp (algebraMap (𝓞 c.F) c.F) = κ'.comp (algebraMap (𝓞 c.F) c.F) → κ = κ' :=
    fun κ κ' h => IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) h
  have hq : ∀ b : C, ((U b.1).F b.2).q = q := fun b => (U b.1).q_eq b.2
  have hdisj : ∀ b b' : C, ∀ t ∈ ballDom q, ∀ t' ∈ ballDom q, (U b.1).pt b.2 t = (U b'.1).pt b'.2 t' → b = b' := by
    rintro ⟨κ, k⟩ ⟨κ', k'⟩ t ht t' ht' h
    have h₁ := (U κ).comp_s_eq_spMap_of_isOver k t ht
    have h₂ := (U κ').comp_s_eq_spMap_of_isOver k' t' ht'
    dsimp only at h
    rw [h, h₂] at h₁
    obtain rfl := hκ _ _ (spMap_injective h₁)
    rw [(U κ').disj k k' t ht t' ht' h]
  have hemb : ∀ p : Sp ℂ ⟶ Y.X, ∃ κ : c.F →+* ℂ, p ≫ Y.s = spMap (κ.comp (algebraMap (𝓞 c.F) c.F)) := fun p => by
    obtain ⟨κ, hκρ⟩ := FamEx.exists_ringHom_extend (Spec.preimage (p ≫ Y.s)).hom
    refine ⟨κ, ?_⟩
    rw [hκρ]
    unfold spMap
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  refine ⟨{
    np := np
    g := g
    Di := fun k => (U (a k).1).Di (a k).2
    sig := fun k => (U _).sig _
    κ := fun k => (a k).1
    F := fun k => (U (a k).1).F (a k).2
    q_eq := fun k k' => (hq _).trans (hq _).symm
    form_eq := fun k => (U _).form_eq _
    σ_eq := fun k => (U _).σ_eq _
    Γ := fun k => (U (a k).1).Γ (a k).2
    mem_Γ := fun k => (U _).mem_Γ _
    arith := fun k => (U _).arith _
    pt := fun k => (U (a k).1).pt (a k).2
    hol := fun k => by rw [hq]; exact (U _).hol _
    comp_s_eq_spMap_of_isOver := fun k => by rw [hq]; exact (U _).comp_s_eq_spMap_of_isOver _
    interior := fun k => by rw [hq]; exact (U _).interior _
    disj := fun k k' => by
      rw [hq, hq]
      exact fun t ht t' ht' h => e.symm.injective (hdisj _ _ t ht t' ht' h)
    fibre := fun k => by rw [hq]; exact (U _).fibre _
    onto := fun p hp => ?_
    lat := fun k => by rw [hq]; exact (U _).lat _
    vec := fun S Ω _ K _ J _ y 𝔐 k V z hV hs => (U _).vec S Ω K J y 𝔐 _ V z hV (by rw [← hq (a k)]; exact hs) }, ?_⟩
  · obtain ⟨κ, hκ⟩ := hemb p
    obtain ⟨k, t, ht, h⟩ := (U κ).onto p hp hκ
    obtain ⟨i, hi⟩ := e.symm.surjective ⟨κ, k⟩
    refine ⟨i, t, by rw [hq]; exact ht, ?_⟩
    show (U (e.symm i).1).pt (e.symm i).2 t = p
    rw [hi]
    exact h
  · intro m T y hT hTc hy hyi b hb b' hb' k k' t ht t' ht' h h'
    choose κ hκy using fun b => hemb (y b)
    have hd : ∀ r : 𝓞 c.F, DifferentiableOn ℂ (fun b => κ b (r : c.F)) T := fun r => by
      have h3 := (PullbackSections.isHolTo_comp hy Y.s ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 c.F))).inv r)).2
      have hset : T ⊆ {b ∈ T | ⊤ ≤ (y b ≫ Y.s) ⁻¹ᵁ ⊤} := fun b hb => ⟨hb, le_top⟩
      refine (h3.mono hset).congr fun b _ => ?_
      show κ b (r : c.F) = valAt' (y b ≫ Y.s) ⊤ _
      rw [hκy b]
      exact (PullbackSections.valAt'_spMap ((κ b).comp (algebraMap (𝓞 c.F) c.F)) r).symm
    have hc : ∀ b₁ ∈ T, y b₁ ≫ Y.s = spMap ((κ b).comp (algebraMap (𝓞 c.F) c.F)) := fun b₁ hb₁ => by
      rw [hκy, FamEx.embedding_const_preconnected hTc κ hd hb₁ hb]
    have key : ∀ d d' : C, y b = (U d.1).pt d.2 t → y b' = (U d'.1).pt d'.2 t' → t ∈ ballDom q → t' ∈ ballDom q → d = d' := by
      rintro ⟨κ₁, k₁⟩ ⟨κ₂, k₂⟩ h₁ h₂ ht ht'
      dsimp only at h₁ h₂
      have e₁ := (U κ₁).comp_s_eq_spMap_of_isOver k₁ t ht
      have e₂ := (U κ₂).comp_s_eq_spMap_of_isOver k₂ t' ht'
      rw [← h₁, hc b hb] at e₁
      rw [← h₂, hc b' hb'] at e₂
      obtain rfl := hκ _ _ (spMap_injective e₁)
      obtain rfl := hκ _ _ (spMap_injective e₂)
      rw [(U (κ b)).locc m T y hT hTc hy hyi hc b hb b' hb' k₁ k₂ t ht t' ht' h₁ h₂]
    exact e.symm.injective (key (a k) (a k') h h' (by rw [← hq (a k)]; exact ht) (by rw [← hq (a k')]; exact ht'))

theorem baseUnifEx2_of (hV : VecOfPeriods) (hC : KUnifConj) : BaseUnifEx2 := by
  intro hG E _ _ _ H D l Xo c Y sm j j' n h1 hs hn
  letI : Fintype (CMType H) := Subtype.fintype (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0)
  have hN : N1c := hG.1.2.2.1
  obtain ⟨g, ty, hty⟩ := GlobalTheory.AllClasses.exists_isTypeFn H D.p D.q
  have q : CMType H × Fin j × Fin j' ≃ Fin n := Fintype.equivFinOfCardEq (by simp [hn, mul_assoc])
  let ρ : c.F := (IntermediateField.inclusion c.le).toRingHom (baseKA l).ρ
  have hρ : (ρ : ℂ) = H.rt0 := rfl
  have good : ∀ κ : c.F →+* ℂ, κ ρ = H.rt0 → Nonempty (KUnif Y sm j j' n g q κ) := fun κ hκ => by
    obtain ⟨FU⟩ := hN E H D l Xo (κ.comp (IntermediateField.inclusion c.le).toRingHom) g ty h1 hκ hty
    exact kUnif_good hV Y sm j j' n g q κ ty hty hs ρ hρ hκ FU
  have all : ∀ κ : c.F →+* ℂ, Nonempty (KUnif Y sm j j' n g q κ) := fun κ => by
    have e : ρ ^ 2 = -(H.d : c.F) := Subtype.ext (by show (ρ : ℂ) ^ 2 = -(H.d : ℂ); exact H.sqrt_neg_disc_sq)
    have e2 : (κ ρ) ^ 2 = H.rt0 ^ 2 := by
      rw [← map_pow, e, H.sqrt_neg_disc_sq]
      simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 e2 with h | h
    · exact good κ h
    · have h' := hC E H D l Xo c Y sm j j' n g q _ (good ((starRingEnd ℂ).comp κ) (by
        show starRingEnd ℂ (κ ρ) = _
        rw [h, map_neg, FamEx.rt0_conj_neg_ne_zero, neg_neg]))
      have e3 : (starRingEnd ℂ).comp ((starRingEnd ℂ).comp κ) = κ := RingHom.ext fun x => by simp
      rwa [e3] at h'
  exact baseUnif_of_kUnif Y sm j j' n g q fun κ => (all κ).some

end SheetDecomposition
end
end

section

noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory Limits NumberField Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace One

theorem spMap_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map (CommRingCat.ofHom (g.comp f)) = _
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

theorem spMap_inj {R S : Type} [CommRing R] [CommRing S] {f g : R →+* S} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem spec_map_factorisation {X : Scheme.{0}} {A A' B B' : CommRingCat.{0}} (u : A ⟶ B) [IsIso u] (r : A ⟶ A') (v : A' ⟶ B')
    (a : Spec A ⟶ X) (a' : Spec A' ⟶ X) (x : Spec B ⟶ X) (x' : Spec B' ⟶ X) (e : Spec.map u ≫ a = x)
    (e' : Spec.map v ≫ a' = x') (e₂ : Spec.map r ≫ a = a') : Spec.map (inv u ≫ r ≫ v) ≫ x = x' := by
  subst e e' e₂
  rw [← Category.assoc (Spec.map _), ← Spec.map_comp, IsIso.hom_inv_id_assoc, Spec.map_comp, Category.assoc]

theorem exists_factor {X : Scheme.{0}} {Ω₀ Ω₁ : Type} [Field Ω₀] [Field Ω₁] {ξ₀ : Sp Ω₀ ⟶ X} (ξ₁ : Sp Ω₁ ⟶ X)
    (h₀ : IsCptGen ξ₀) (h : genPt ξ₁ ⤳ genPt ξ₀) : ∃ i : Ω₀ →+* Ω₁, spMap i ≫ ξ₀ = ξ₁ := by
  haveI : IsIso (Scheme.stalkClosedPointTo ξ₀) := (ConcreteCategory.isIso_iff_bijective _).2 h₀.bij
  refine ⟨(inv (Scheme.stalkClosedPointTo ξ₀) ≫ X.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo ξ₁).hom, ?_⟩
  exact spec_map_factorisation (Scheme.stalkClosedPointTo ξ₀) (X.presheaf.stalkSpecializes h) (Scheme.stalkClosedPointTo ξ₁) _ _ ξ₀ ξ₁
    (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ₀) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ₁)
    (Scheme.SpecMap_stalkSpecializes_fromSpecStalk (X := X) h)

theorem ext_int {F Ω : Type} [Field F] [NumberField F] [Field Ω] {f g : F →+* Ω}
    (h : f.comp (algebraMap (𝓞 F) F) = g.comp (algebraMap (𝓞 F) F)) : f = g :=
  IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F)) h

theorem constClosed_of {F Ω₀ Ω₁ Ω₂ : Type} [Field F] [NumberField F] [Field Ω₀] [Field Ω₁] [Field Ω₂] [Algebra F Ω₀]
    (i : Ω₀ →+* Ω₁) (g : Ω₁ →+* Ω₂) (cst : F →+* Ω₂) (h : (g.comp i).comp (algebraMap F Ω₀) = cst)
    (halg : ∀ a : Ω₁, IsAlgebraic ℤ a → g a ∈ cst.range) : ConstClosed F Ω₀ := by
  intro a ha
  haveI : Algebra.IsAlgebraic ℤ F := (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ)).2 inferInstance
  have h1 : IsAlgebraic ℤ a := ha.restrictScalars ℤ
  obtain ⟨x, hx⟩ := halg (i a) (h1.algHom i.toIntAlgHom)
  refine ⟨x, 1, one_ne_zero, ?_⟩
  rw [map_one, mul_one]
  refine (g.comp i).injective ?_
  rw [← h] at hx
  exact hx.symm

theorem int_frac (F : Type) [Field F] [NumberField F] : Function.Injective (algebraMap (𝓞 F) F) ∧ IsNoetherianRing (𝓞 F) ∧
    ∀ x : F, ∃ a b : 𝓞 F, algebraMap (𝓞 F) F b ≠ 0 ∧ x * algebraMap (𝓞 F) F b = algebraMap (𝓞 F) F a := by
  refine ⟨IsFractionRing.injective _ _, inferInstance, fun x => ?_⟩
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) x
  have : algebraMap (𝓞 F) F b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  exact ⟨a, b, this, div_mul_cancel₀ _ this⟩

end One

open SheetDecomposition.One

theorem onePiece : OnePiece := by
  intro hgiven E _ _ _ H D l Xo c Y sm j j' n B Ω₀ _ ξ₀ Ω₁ Ω₂ _ _ ξ₁ g cst U hloc hξ₀ hpt hover halg hU hUc κ
  classical
  letI : Fintype (CMType H) := Subtype.fintype (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0)
  obtain ⟨-, -, -, -, hRes, -⟩ := hgiven
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := {}
  obtain ⟨i, hi⟩ := exists_factor ξ₁ hξ₀ (hpt ▸ specializes_rfl)
  haveI : CharZero Ω₂ := (RingHom.charZero_iff cst.injective).1 inferInstance
  haveI : CharZero Ω₀ := (g.comp i).charZero
  obtain ⟨b, ξF, hF1, hF2, hFg⟩ := GlobalTheory.T.generic_point_generic_fibre c.F Y.X Y.s Ω₀ ξ₀ hξ₀
  letI : Algebra c.F Ω₀ := b.toAlgebra
  have hb : (g.comp i).comp b = cst := by
    refine ext_int (spMap_inj ?_)
    rw [← hover, ← hi, ← hF1, spMap_comp', spMap_comp', spMap_comp', ← hF2]
    simp only [Category.assoc, pullback.condition]
  have hcl : ConstClosed c.F Ω₀ := constClosed_of i g cst hb halg
  have hβ := int_frac c.F
  obtain ⟨hnoeth, X', f, d, W', jW, hiso, hjW, -, -, hsm, -⟩ := GlobalTheory.T.exists_resolution_generic_fibre hRes E H D l Xo c _ _ Y hβ
  haveI := Y.jQ_open
  haveI hpre : IsPreimmersion (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) := by
    have h : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
      IsPreimmersion.of_isLocalization (R := 𝓞 c.F) (S := c.F) (nonZeroDivisors (𝓞 c.F))
    infer_instance
  have hsurj := GlobalTheory.T.stalk_surjective_open_immersion _ _ _ _ _ f W' jW Y.jQ hpre inferInstance hiso hjW
  haveI hopen : IsOpenImmersion (W'.ι ≫ f) := by rw [← hjW]; infer_instance
  have hrange : Set.range (W'.ι ≫ f) = Set.range Y.jQ := by
    rw [← hjW, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.2 (show Function.Surjective jW from jW.homeomorph.surjective), Set.image_univ]
  have hlift : ∀ (R : Type) [Field R] (z : Sp R ⟶ pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F))),
      centre z ∈ Set.range Y.jQ → ∃ z' : Sp R ⟶ W'.toScheme, z' ≫ W'.ι ≫ f = z := by
    intro R _ z hz
    refine ⟨IsOpenImmersion.lift (W'.ι ≫ f) z ?_, IsOpenImmersion.lift_fac _ _ _⟩
    rintro _ ⟨q, rfl⟩
    have : q = IsLocalRing.closedPoint R := Subsingleton.elim (α := PrimeSpectrum R) _ _
    rw [hrange, this]
    exact hz
  obtain ⟨π, hπ⟩ : ∃ π, π = f ≫ pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F)) := ⟨_, rfl⟩
  obtain ⟨s', hs'⟩ : ∃ s', s' = f ≫ pullback.snd Y.s (spMap (algebraMap (𝓞 c.F) c.F)) := ⟨_, rfl⟩
  haveI hemb : IsPreimmersion (W'.ι ≫ π) := by
    rw [hπ, ← Category.assoc]
    infer_instance
  rw [← hπ] at hsurj
  rw [← hs'] at hsm
  have hsm' : Smooth s' := SmoothOfRelativeDimension.smooth d s'
  have hπs : π ≫ Y.s = s' ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    rw [hπ, hs', Category.assoc, Category.assoc, pullback.condition]
  obtain ⟨ξW, hξW⟩ := hlift Ω₀ ξF
    (genPt_mem_dense Y.jQ.opensRange hFg (by simpa using Y.jQ_dense))
  have h2 : (ξW ≫ W'.ι) ≫ π = ξ₀ := by
    rw [hπ, ← hF1, ← hξW]
    simp only [Category.assoc]
  have h3 : (ξW ≫ W'.ι) ≫ s' = spMap (algebraMap c.F Ω₀) := by
    refine Eq.trans ?_ hF2
    rw [hs', ← hξW]
    simp only [Category.assoc]
  have hgW : genPt (ξW ≫ W'.ι) ∈ W' := (genPt ξW).2
  have hξg : IsCptGen (ξW ≫ W'.ι) := GlobalTheory.T.generic_of_smooth_surjective c.F _ _ _ _ _ π s' hsm' h2 hξ₀ (hsurj _ hgW)
  have hab : ∀ x : Sp ℂ ⟶ X', ⊤ ≤ x ⁻¹ᵁ W' → centre (x ≫ π) ∈ abLocus Y.t.G := by
    intro x hx
    have h1 : f (centre x) ∈ Set.range Y.jQ := by
      rw [← hrange]
      exact ⟨⟨centre x, GagaRat.centre_mem hx⟩, rfl⟩
    rw [← Y.ab_gen] at h1
    rw [hπ]
    exact h1
  have hexF : ∀ x : Sp ℂ ⟶ X', ∃ r : ℂ, r ≠ 0 ∧ ∀ k, ∀ t ∈ Cusp.ballDom (B.F k).q, x ≫ π = B.pt k t →
      r = (((k : ℕ) + 1 : ℕ) : ℂ) := by
    intro x
    by_cases h : ∃ k, ∃ t ∈ Cusp.ballDom (B.F k).q, x ≫ π = B.pt k t
    · obtain ⟨k, t, ht, e⟩ := h
      refine ⟨(((k : ℕ) + 1 : ℕ) : ℂ), Nat.cast_ne_zero.2 (Nat.succ_ne_zero _), fun k' t' ht' e' => ?_⟩
      rw [B.disj k k' t ht t' ht' (e.symm.trans e')]
    · exact ⟨1, one_ne_zero, fun k t ht e => absurd ⟨k, t, ht, e⟩ h⟩
  choose F _ hF using hexF
  have hconst := const_of_hol κ s' (ξW ≫ W'.ι) W' F d hsm h3 hξg hcl (by
    intro m T y hT hc hy hW b₁ hb₁ b₂ hb₂
    obtain ⟨k₁, t₁, ht₁, e₁⟩ := B.onto _ (hab _ (hW b₁ hb₁))
    obtain ⟨k₂, t₂, ht₂, e₂⟩ := B.onto _ (hab _ (hW b₂ hb₂))
    rw [hF _ k₁ t₁ ht₁ e₁.symm, hF _ k₂ t₂ ht₂ e₂.symm,
      hloc m T (fun b => y b ≫ π) hT hc (GagaRat.isHolTo_comp π hy) (fun b hb => hab _ (hW b hb)) b₁ hb₁ b₂ hb₂ k₁ k₂
        t₁ ht₁ t₂ ht₂ e₁.symm e₂.symm])
  have hup : ∀ k, B.κ k = κ → ∀ t ∈ Cusp.ballDom (B.F k).q, ⊤ ≤ B.pt k t ⁻¹ᵁ U → ∃ x : Sp ℂ ⟶ X',
      x ≫ π = B.pt k t ∧ x ≫ s' = spMap κ ∧ ⊤ ≤ x ⁻¹ᵁ W' ∧ genPt (ξW ≫ W'.ι) ⤳ centre x := by
    intro k hk t ht hu
    let z : Sp ℂ ⟶ pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F)) :=
      pullback.lift (B.pt k t) (spMap κ) (by rw [B.comp_s_eq_spMap_of_isOver k t ht, hk, spMap_comp'])
    have z1 : z ≫ pullback.fst _ _ = B.pt k t := pullback.lift_fst _ _ _
    have z2 : z ≫ pullback.snd _ _ = spMap κ := pullback.lift_snd _ _ _
    obtain ⟨z', hz'⟩ := hlift ℂ z (by
      rw [← Y.ab_gen]
      have := B.interior k t ht
      rw [← z1] at this
      exact this)
    have a1 : (z' ≫ W'.ι) ≫ π = B.pt k t := by
      rw [hπ, ← z1, ← hz']
      simp only [Category.assoc]
    refine ⟨z' ≫ W'.ι, a1, ?_, GagaRat.top_le_of_centre_mem (centre z').2, ?_⟩
    · rw [hs', ← z2, ← hz']
      simp only [Category.assoc]
    · have a2 := hUc _ hu
      rw [← a1, ← h2, Category.assoc, Category.assoc] at a2
      have a3 : genPt ξW ⤳ centre z' := (W'.ι ≫ π).isEmbedding.isInducing.specializes_iff.1 a2
      exact a3.map W'.ι.continuous
  have hgU : genPt (ξW ≫ W'.ι) ∈ W' ⊓ π ⁻¹ᵁ U := by
    refine ⟨hgW, ?_⟩
    rw [← h2] at hU
    exact hU
  obtain ⟨x, hx, hxU⟩ := exists_point κ s' _ hgU
  obtain ⟨k, t, ht, e⟩ := B.onto _ (hab x fun q hq => (hxU hq).1)
  have hk : B.κ k = κ := by
    refine ext_int (spMap_inj ?_)
    rw [← B.comp_s_eq_spMap_of_isOver k t ht, e, Category.assoc, hπs, ← Category.assoc, hx, spMap_comp']
  have hu : ⊤ ≤ B.pt k t ⁻¹ᵁ U := by
    rw [e]
    exact fun q hq => (hxU hq).2
  refine ⟨k, ⟨hk, t, ht, hu⟩, ?_⟩
  rintro k' ⟨hk', t', ht', hu'⟩
  obtain ⟨x₁, a₁, b₁, c₁, d₁⟩ := hup k hk t ht hu
  obtain ⟨x₂, a₂, b₂, c₂, d₂⟩ := hup k' hk' t' ht' hu'
  have := hconst x₂ x₁ b₂ b₁ c₂ c₁ d₂ d₁
  rw [hF _ k t ht a₁, hF _ k' t' ht' a₂] at this
  exact Fin.ext (Nat.succ_injective (Nat.cast_injective this))

end SheetDecomposition
end
end

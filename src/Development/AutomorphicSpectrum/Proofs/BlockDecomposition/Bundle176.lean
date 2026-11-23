module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle026
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.TopologicalKrullDimLeOfIrreducibleCloseds
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle155
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle154
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle089
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle102
public import Formalism.ConjugateSelfDual.Bundle001
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle053
public import ReciprocityTheory.Hypotheses.GalCoh
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle165
public import ReciprocityTheory.Hypotheses.GalCohDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SelmerGroupDualExact
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle153
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GelfandSpectralNormalisation.NormalisedInvariants.PoitouTateExactSecond
import Mathlib.RepresentationTheory.Basic
import ReciprocityTheory.GaloisValuations.GlobalA
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle038
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PairSums.SumPair

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.Hodge.Nerve

theorem nerveCx_shortExact {R : Type} [CommRing R] {C : Type} [Category.{0} C]
    (S : ShortComplex (C ⥤ ModuleCat.{0} R))
    (hS : ∀ a : C, (S.map ((evaluation _ _).obj a)).ShortExact) : (S.map nerveCx).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun p ↦ ?_
  refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
  · change Function.Exact ((nerveCx.map S.f).f p).hom ((nerveCx.map S.g).f p).hom
    have h := fun a : C ↦ (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 (hS a).exact
    intro y
    constructor
    · intro hy
      choose x hx using fun c : Fin (p + 1) ⥤ C ↦ (h _ (y c)).1 (congrFun hy c)
      exact ⟨x, funext hx⟩
    · rintro ⟨x, rfl⟩
      exact funext fun c ↦ (h _ _).2 ⟨x c, rfl⟩
  · change Function.Injective ((nerveCx.map S.f).f p).hom
    exact fun x y hxy ↦ funext fun c ↦ (hS _).moduleCat_injective_f (congrFun hxy c)
  · change Function.Surjective ((nerveCx.map S.g).f p).hom
    intro y
    choose x hx using fun c : Fin (p + 1) ⥤ C ↦ (hS _).moduleCat_surjective_g (y c)
    exact ⟨x, funext hx⟩

theorem cechOf_shortExact {R : Type} [CommRing R] {P : Type} [SemilatticeInf P] {κ : Type} [LinearOrder κ] (e : κ → P)
    (S : ShortComplex (Pᵒᵖ ⥤ ModuleCat.{0} R))
    (hS : ∀ a : Pᵒᵖ, (S.map ((evaluation _ _).obj a)).ShortExact) : (S.map (cechOf e)).ShortExact := by
  refine (cechFunctor_shortExact (S.map (cubeOfFunctor e)) fun s hs ↦ ?_ : ((S.map (cubeOfFunctor e)).map (cechFunctor κ R)).ShortExact)
  have hs' : ∀ (hs : PLift s.Nonempty), _ := fun hs : PLift s.Nonempty ↦ hS (op (s.inf' hs.down e))
  refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
  · intro y
    have h := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 (hs' ⟨hs⟩).exact
    constructor
    · intro hy
      obtain ⟨x, hx⟩ := (h (y ⟨hs⟩)).1 (congrFun hy ⟨hs⟩)
      exact ⟨fun _ ↦ x, funext fun _ ↦ hx⟩
    · rintro ⟨x, rfl⟩
      exact funext fun t ↦ (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 (hs' t).exact _ |>.2 ⟨x t, rfl⟩
  · exact fun x y hxy ↦ funext fun t ↦ (hs' t).moduleCat_injective_f (congrFun hxy t)
  · intro y
    choose x hx using fun t : PLift s.Nonempty ↦ (hs' t).moduleCat_surjective_g (y t)
    exact ⟨x, funext hx⟩

theorem exists_toCoind_shortExact {R : Type} [CommRing R] {P : Type} [SemilatticeInf P]
    (G : Pᵒᵖ ⥤ ModuleCat.{0} R) :
    ∃ (Q : Pᵒᵖ ⥤ ModuleCat.{0} R) (p : (coind fun b ↦ G.obj (op b)) ⟶ Q) (w : toCoind G ≫ p = 0),
      ∀ a : Pᵒᵖ, ((ShortComplex.mk _ _ w).map ((evaluation _ _).obj a)).ShortExact := by
  have : Mono (toCoind G) := by
    refine (NatTrans.mono_iff_mono_app _).2 fun a ↦ (ModuleCat.mono_iff_injective _).2 fun x y h ↦ ?_
    have h1 := congrFun h ⟨a.unop, le_rfl⟩
    have e : ∀ z : G.obj a, (G.map (homOfLE (le_refl a.unop)).op).hom z = z := fun z ↦ by
      have : (homOfLE (le_refl a.unop)).op = 𝟙 a := rfl
      rw [this, G.map_id]
      rfl
    exact (e x).symm.trans (h1.trans (e y))
  have hS : (ShortComplex.mk _ _ (cokernel.condition (toCoind G))).ShortExact :=
    { exact := ShortComplex.exact_cokernel _ }
  exact ⟨_, _, _, fun a ↦ hS.map_of_exact _⟩

theorem nonempty_iso {R : Type} [CommRing R] {P : Type} [SemilatticeInf P] {κ : Type} [LinearOrder κ] (e : κ → P)
    (he : Function.Bijective e) (n : ℕ) (G : Pᵒᵖ ⥤ ModuleCat.{0} R) :
    Nonempty ((nerveCx.obj G).homology n ≅ ((cechOf e).obj G).homology n) := by
  obtain ⟨ε, h1, h2⟩ := GlobalTheory.T.nerve_cech_degree_zero_compatible (R := R) e he
  refine GlobalTheory.T.natural_degree_zero_homology_iso nerveCx (cechOf e) ε h1 h2 (fun G ↦ ?_) n G
  obtain ⟨Q, p, w, h⟩ := exists_toCoind_shortExact G
  exact ⟨_, Q, toCoind G, p, w, nerveCx_shortExact _ h, cechOf_shortExact e _ h,
    fun n ↦ ⟨GlobalTheory.T.coinduced_nerve_acyclic _ n, GlobalTheory.T.coinduced_cech_acyclic e he.2 _ n⟩⟩


theorem cmpSt_of_cxSt : CxSt → CmpSt := by
  intro _ R _ X s _ P _ _ S
  letI := GlobalTheory.algebraΓOfHom s
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin P
  let e' : Fin m → P := e.symm
  have he' : Function.Bijective e' := e.symm.bijective
  have hc : ⨆ i, (S.u (e' i)).1 = ⊤ := by
    rw [← S.cover]
    exact e.symm.iSup_comp (g := fun a ↦ (S.u a).1)
  have hinf : ∀ (t : Finset (Fin m)) (ht : t.Nonempty), (⨅ i ∈ t, (S.u (e' i)).1) = (S.u (t.inf' ht e')).1 := by
    intro t ht
    induction ht using Finset.Nonempty.cons_induction with
    | singleton i => simp
    | cons i t hi ht ih =>
      rw [Finset.inf'_cons ht, S.map_inf, Finset.cons_eq_insert, Finset.iInf_insert, ih]
  have hD : ∀ t : Finset (Fin m), t.Nonempty → IsAffineOpen (⨅ i ∈ t, (S.u (e' i)).1) := fun t ht ↦ by
    rw [hinf t ht]
    exact (S.u _).2
  have key : ∀ n, Nonempty ((nerveCx.obj (toMod (OSys s S))).homology n ≃ₗ[R] GlobalTheory.coh (GlobalTheory.structureModule X) n) := by
    intro n
    obtain ⟨i⟩ := nonempty_iso e' he' n (toMod (OSys s S))
    obtain ⟨f⟩ := GlobalTheory.T.cech_structure_sheaf_comparison R X s P S e' n
    letI : (GlobalTheory.structureModule X).IsQuasicoherent := GlobalTheory.QCoh.IsFiniteQC.isQuasicoherent
    exact ⟨i.toLinearEquiv ≪≫ₗ f ≪≫ₗ GlobalTheory.cechHEquivCoh R hc hD (GlobalTheory.structureModule X) n⟩
  obtain ⟨⟨a⟩, b⟩ := GlobalTheory.T.cochain_cohomology_nerve_homology_equiv (OSys s S)
  obtain ⟨k⟩ := key 0
  refine ⟨⟨a ≪≫ₗ k⟩, fun n ↦ ?_⟩
  obtain ⟨b'⟩ := b n
  obtain ⟨k'⟩ := key (n + 1)
  exact ⟨b' ≪≫ₗ k'⟩

end GlobalTheory.CompanionTheory.Hodge.Nerve
end
end

section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso

namespace GlobalTheory.CompanionTheory.PTIso.Places

variable {R S : Type} [CommRing R] [CommRing S]

theorem mem_iff_apply_mem_map (f : R ≃+* S) (I : Ideal R) (x : R) :
    x ∈ I ↔ f x ∈ I.map f := by
  rw [Ideal.mem_map_of_equiv]
  constructor
  · exact fun h => ⟨x, h, rfl⟩
  · rintro ⟨y, hy, e⟩
    rwa [← f.injective e]

variable [IsDedekindDomain R] [IsDedekindDomain S]

noncomputable def placeMap (f : R ≃+* S) (v : HeightOneSpectrum R) : HeightOneSpectrum S where
  asIdeal := v.asIdeal.map f
  isPrime := by
    haveI := v.isPrime
    exact Ideal.map_isPrime_of_equiv f
  ne_bot := by
    intro h
    apply v.ne_bot
    exact (Ideal.map_eq_bot_iff_of_injective f.injective).1 h

theorem placeMap_asIdeal (f : R ≃+* S) (v : HeightOneSpectrum R) :
    (placeMap f v).asIdeal = v.asIdeal.map f := rfl

theorem placeMap_symm_placeMap (f : R ≃+* S) (v : HeightOneSpectrum R) :
    placeMap f.symm (placeMap f v) = v := by
  apply HeightOneSpectrum.ext
  rw [placeMap_asIdeal, placeMap_asIdeal, Ideal.map_symm]
  ext x
  rw [Ideal.mem_comap]
  exact (mem_iff_apply_mem_map f _ x).symm

noncomputable def placeEquiv (f : R ≃+* S) : HeightOneSpectrum R ≃ HeightOneSpectrum S where
  toFun := placeMap f
  invFun := placeMap f.symm
  left_inv := placeMap_symm_placeMap f
  right_inv := placeMap_symm_placeMap f.symm

theorem exists_places_of_ringEquiv : ∀ (F F' : Type) [Field F] [NumberField F] [Field F'] [NumberField F'] (e : F ≃+* F'), ∃ (eO : 𝓞 F ≃+* 𝓞 F') (eV : HeightOneSpectrum (𝓞 F) ≃ HeightOneSpectrum (𝓞 F')), (∀ x : 𝓞 F, ((eO x : 𝓞 F') : F') = e (x : F)) ∧ (∀ (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F), x ∈ v.asIdeal ↔ eO x ∈ (eV v).asIdeal) ∧ (∀ (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F), x ∈ v.asIdeal ^ 2 ↔ eO x ∈ (eV v).asIdeal ^ 2) ∧ ∀ v : HeightOneSpectrum (𝓞 F), normV (eV v) = normV v := by
  intro F F' _ _ _ _ e
  refine ⟨RingOfIntegers.mapRingEquiv e, placeEquiv (RingOfIntegers.mapRingEquiv e), ?_, ?_, ?_, ?_⟩
  · intro x
    rw [RingOfIntegers.mapRingEquiv_apply]
  · intro v x
    exact mem_iff_apply_mem_map _ _ x
  · intro v x
    change x ∈ v.asIdeal ^ 2 ↔ _ ∈ (v.asIdeal.map (RingOfIntegers.mapRingEquiv e)) ^ 2
    rw [← Ideal.map_pow]
    exact mem_iff_apply_mem_map _ _ x
  · intro v
    exact (Nat.card_congr (Ideal.quotientEquiv v.asIdeal _ (RingOfIntegers.mapRingEquiv e) rfl).toEquiv).symm

end GlobalTheory.CompanionTheory.PTIso.Places
end

section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso

namespace GlobalTheory.CompanionTheory.PTIso

private theorem valuation_lt_one_iff_mem_and_inv_not_mem {K : Type*} [Field K] (A : ValuationSubring K) (y : K) :
    A.valuation y < 1 ↔ y = 0 ∨ y⁻¹ ∉ A := by
  by_cases hy : y = 0
  · subst hy
    simp
  · have hp : 0 < A.valuation y := (Valuation.pos_iff _).2 hy
    rw [← A.valuation_le_one_iff, Valuation.map_inv, inv_le_one₀ hp, not_le]
    simp [hy]

theorem isPlaceOver_transfer_fieldIso :
    ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∀ (eO : 𝓞 F ≃+* 𝓞 F') (eV : HeightOneSpectrum (𝓞 F) ≃ HeightOneSpectrum (𝓞 F')), (∀ x : 𝓞 F, ((eO x : 𝓞 F') : F') = e (x : F)) → (∀ (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F), x ∈ v.asIdeal ↔ eO x ∈ (eV v).asIdeal) → ∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → ∀ v : HeightOneSpectrum (𝓞 F), IsPlaceOver A v ↔ IsPlaceOver A' (eV v) := by
  intro F Ω F' Ω' _ _ _ _ _ _ _ _ _ _ e E hE eO eV hO hv A A' hA v
  have hlt : ∀ y : Ω, A'.valuation (E y) < 1 ↔ A.valuation y < 1 := by
    intro y
    rw [valuation_lt_one_iff_mem_and_inv_not_mem, valuation_lt_one_iff_mem_and_inv_not_mem, ← map_inv₀, hA, map_eq_zero_iff E E.injective]
  have hx : ∀ x : 𝓞 F, (A'.valuation (algebraMap F' Ω' ((eO x : 𝓞 F') : F')) < 1 ↔ eO x ∈ (eV v).asIdeal) ↔
      (A.valuation (algebraMap F Ω (x : F)) < 1 ↔ x ∈ v.asIdeal) := by
    intro x
    rw [hO x, ← hE, hlt, ← hv]
  unfold Formalism.ConjugateSelfDual.IsPlaceOver
  constructor
  · intro h x'
    obtain ⟨x, rfl⟩ := eO.surjective x'
    exact (hx x).2 (h x)
  · intro h x
    exact (hx x).1 (h (eO x))

end GlobalTheory.CompanionTheory.PTIso
end

section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso

namespace GlobalTheory.CompanionTheory.PTIso

section GalConj

variable {F Ω F' Ω' : Type} [Field F] [Field Ω] [Algebra F Ω]
  [Field F'] [Field Ω'] [Algebra F' Ω']

def galConjFun (e : F ≃+* F') (E : Ω ≃+* Ω')
    (hE : ∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) (σ : Ω ≃ₐ[F] Ω) :
    Ω' ≃ₐ[F'] Ω' :=
  AlgEquiv.ofRingEquiv (f := E.symm.trans ((σ : Ω ≃+* Ω).trans E)) (fun y => by
    obtain ⟨x, rfl⟩ := e.surjective y
    have h1 : E.symm (algebraMap F' Ω' (e x)) = algebraMap F Ω x := by
      rw [← hE, RingEquiv.symm_apply_apply]
    simp [h1, hE])

theorem galConjFun_apply (e : F ≃+* F') (E : Ω ≃+* Ω')
    (hE : ∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) (σ : Ω ≃ₐ[F] Ω) (x : Ω) :
    galConjFun e E hE σ (E x) = E (σ x) := by
  simp [galConjFun]

def galConjHom (e : F ≃+* F') (E : Ω ≃+* Ω')
    (hE : ∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) :
    (Ω ≃ₐ[F] Ω) →* (Ω' ≃ₐ[F'] Ω') where
  toFun := galConjFun e E hE
  map_one' := by
    ext y
    obtain ⟨x, rfl⟩ := E.surjective y
    rw [galConjFun_apply]; rfl
  map_mul' σ τ := by
    ext y
    obtain ⟨x, rfl⟩ := E.surjective y
    show galConjFun e E hE (σ * τ) (E x) = galConjFun e E hE σ (galConjFun e E hE τ (E x))
    rw [galConjFun_apply e E hE τ, galConjFun_apply e E hE σ, galConjFun_apply e E hE (σ * τ),
      AlgEquiv.mul_apply]

theorem galConjHom_apply (e : F ≃+* F') (E : Ω ≃+* Ω')
    (hE : ∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) (σ : Ω ≃ₐ[F] Ω) (x : Ω) :
    galConjHom e E hE σ (E x) = E (σ x) :=
  galConjFun_apply e E hE σ x

theorem continuous_galConjHom [Algebra.IsAlgebraic F Ω]
    (e : F ≃+* F') (E : Ω ≃+* Ω')
    (hE : ∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) :
    Continuous (galConjHom e E hE) := by
  refine continuous_of_continuousAt_one _ ?_
  intro s hs
  rw [map_one, krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨K', hK', hKs⟩ := hs
  let b := Module.finBasis F' K'
  let T : Set Ω := Set.range fun i => E.symm (b i : Ω')
  let L : IntermediateField F Ω := IntermediateField.adjoin F T
  have hL : FiniteDimensional F L :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  rw [Filter.mem_map, krullTopology_mem_nhds_one_iff]
  refine ⟨L, hL, fun σ hσ => hKs ?_⟩
  have hfix : ∀ i, galConjHom e E hE σ (b i : Ω') = (b i : Ω') := by
    intro i
    have hmem : E.symm (b i : Ω') ∈ L :=
      IntermediateField.subset_adjoin F T ⟨i, rfl⟩
    have h1 : σ (E.symm (b i : Ω')) = E.symm (b i : Ω') :=
      (IntermediateField.mem_fixingSubgroup_iff L σ).1 hσ _ hmem
    have h2 := galConjHom_apply e E hE σ (E.symm (b i : Ω'))
    rwa [h1, RingEquiv.apply_symm_apply] at h2
  have hlin : ((galConjHom e E hE σ).toAlgHom.comp K'.val).toLinearMap = K'.val.toLinearMap :=
    b.ext fun i => hfix i
  refine (IntermediateField.mem_fixingSubgroup_iff K' _).2 fun x hx => ?_
  exact congrArg (fun f : K' →ₗ[F'] Ω' => f ⟨x, hx⟩) hlin

end GalConj

theorem exists_galContinuousMulEquiv : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω']
    [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'),
    (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) →
    ∃ Φ : G F Ω ≃ₜ* G F' Ω', ∀ (σ : G F Ω) (x : Ω), Φ σ (E x) = E (σ x) := by
  intro F Ω F' Ω' _ _ _ _ _ _ _ _ _ _ e E hE
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsAlgebraic F' Ω' := IsAlgClosure.isAlgebraic
  have hE' : ∀ x : F', E.symm (algebraMap F' Ω' x) = algebraMap F Ω (e.symm x) := by
    intro x
    rw [RingEquiv.symm_apply_eq, hE, RingEquiv.apply_symm_apply]
  refine ⟨{ toFun := galConjHom e E hE
            invFun := galConjHom e.symm E.symm hE'
            left_inv := ?_
            right_inv := ?_
            map_mul' := map_mul _
            continuous_toFun := continuous_galConjHom e E hE
            continuous_invFun := continuous_galConjHom e.symm E.symm hE' },
    fun σ x => galConjHom_apply e E hE σ x⟩
  · intro σ
    ext x
    have h := galConjHom_apply e.symm E.symm hE' (galConjHom e E hE σ) (E x)
    rw [galConjHom_apply e E hE σ x, RingEquiv.symm_apply_apply,
      RingEquiv.symm_apply_apply] at h
    exact h
  · intro τ
    ext y
    have h := galConjHom_apply e E hE (galConjHom e.symm E.symm hE' τ) (E.symm y)
    rw [galConjHom_apply e.symm E.symm hE' τ y, RingEquiv.apply_symm_apply,
      RingEquiv.apply_symm_apply] at h
    exact h

end GlobalTheory.CompanionTheory.PTIso
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.ChartDenom

theorem exists_nat_mul_mem_chartRingZ {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type}
    [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) {x : Ω} (hx : x ∈ chartRingQ y c) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : Ω) * x ∈ chartRingZ y c := by
  unfold chartRingQ at hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    refine ⟨1, one_ne_zero, ?_⟩
    rw [Nat.cast_one, one_mul]
    exact Algebra.subset_adjoin hx
  | algebraMap r =>
    refine ⟨r.den, r.den_ne_zero, ?_⟩
    have h : ((r.den : ℕ) : Ω) * algebraMap ℚ Ω r = ((r.num : ℤ) : Ω) := by
      have hd : ((r.den : ℕ) : Ω) ≠ 0 := Nat.cast_ne_zero.2 r.den_ne_zero
      rw [eq_ratCast, Rat.cast_def]
      field_simp
    rw [h]
    exact intCast_mem _ _
  | add u v _ _ hu hv =>
    obtain ⟨m, hm, hmu⟩ := hu
    obtain ⟨n, hn, hnv⟩ := hv
    refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
    have e : ((m * n : ℕ) : Ω) * (u + v) = (n : Ω) * ((m : Ω) * u) + (m : Ω) * ((n : Ω) * v) := by
      push_cast; ring
    rw [e]
    exact add_mem (mul_mem (natCast_mem _ _) hmu) (mul_mem (natCast_mem _ _) hnv)
  | mul u v _ _ hu hv =>
    obtain ⟨m, hm, hmu⟩ := hu
    obtain ⟨n, hn, hnv⟩ := hv
    refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
    have e : ((m * n : ℕ) : Ω) * (u * v) = ((m : Ω) * u) * ((n : Ω) * v) := by
      push_cast; ring
    rw [e]
    exact mul_mem hmu hnv

theorem chartLatQ_le_span_chartLatNm :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
      (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ),
      chartLatQ y a τ ≤ Submodule.span ℚ (chartLatNm y a τ : Set Ω) := by
  intro K _ ι _ Ω _ _ y a τ s hs
  classical
  have hex : ∀ c : ∀ k, ι k, ∃ n : ℕ, n ≠ 0 ∧ ((∀ k, y ⟨k, c k⟩ ≠ 0) →
      (n : Ω) * (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k))) ∈ chartRingZ y c) := by
    intro c
    by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
    · obtain ⟨n, hn, h⟩ := exists_nat_mul_mem_chartRingZ y c (hs c hc)
      exact ⟨n, hn, fun _ => h⟩
    · exact ⟨1, one_ne_zero, fun h => absurd h hc⟩
  choose n hn0 hn using hex
  have hN : (∏ c, n c) ≠ 0 := Finset.prod_ne_zero_iff.2 fun c _ => hn0 c
  have hNΩ : (((∏ c, n c : ℕ)) : Ω) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hmem : (((∏ c, n c : ℕ)) : Ω) * s ∈ chartLatNm y a τ := by
    intro c hc
    have e : ((((∏ c, n c : ℕ)) : Ω) * s) * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)) =
        (((∏ c' ∈ Finset.univ.erase c, n c' : ℕ)) : Ω) *
          ((n c : Ω) * (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)))) := by
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ c)]
      push_cast; ring
    rw [e]
    have h : (((∏ c' ∈ Finset.univ.erase c, n c' : ℕ)) : Ω) *
        ((n c : Ω) * (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)))) ∈ chartRingZ y c :=
      mul_mem (natCast_mem _ _) (hn c hc)
    exact Subalgebra.algebraMap_mem (integralClosure (chartRingZ y c) Ω) (⟨_, h⟩ : chartRingZ y c)
  have h1 : (((∏ c, n c : ℕ)) : Ω) * s ∈ Submodule.span ℚ (chartLatNm y a τ : Set Ω) :=
    Submodule.subset_span hmem
  have h2 := Submodule.smul_mem _ (((∏ c, n c : ℕ) : ℚ)⁻¹) h1
  have e : (((∏ c, n c : ℕ) : ℚ)⁻¹) • ((((∏ c, n c : ℕ)) : Ω) * s) = s := by
    rw [Rat.smul_def, Rat.cast_inv, Rat.cast_natCast, ← mul_assoc, inv_mul_cancel₀ hNΩ, one_mul]
  rwa [e] at h2

end GlobalTheory.CompanionTheory.Ar.ChartDenom
end

section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt

theorem _root_.GlobalTheory.T.finite_local_cohomology_at_places_of_localFiniteness : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (Av : S → ValuationSubring Ω) (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ) (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) (hρ : ContAction ρ), LocalFiniteness → 0 < r → (∀ v : S, IsPlaceOver (Av v) v.1) → ∀ v : S, Finite (H0 (ρ.comp (locFam S Av v))) ∧ Finite (H1 (ρ.comp (locFam S Av v))) ∧ Finite (H2 (ρ.comp (locFam S Av v))) := by
  first | exact @GlobalTheory.CompanionTheory.Galois.PlacesOfS.localFinite_at_places | exact GlobalTheory.CompanionTheory.Galois.PlacesOfS.localFinite_at_places | (intros; apply GlobalTheory.CompanionTheory.Galois.PlacesOfS.localFinite_at_places <;> assumption)
end

section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt

theorem _root_.GlobalTheory.T.selmer_group_dual_exact : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (Av : S → ValuationSubring Ω) (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ) (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) (hρ : ContAction ρ), μ.comp (toGS Ω _) = cycMod F Ω l r → ContAction (twDual μ ρ) := by
  first | exact @GlobalTheory.CompanionTheory.GalDual.contAction_twDual | exact GlobalTheory.CompanionTheory.GalDual.contAction_twDual | (intros; apply GlobalTheory.CompanionTheory.GalDual.contAction_twDual <;> assumption)
end

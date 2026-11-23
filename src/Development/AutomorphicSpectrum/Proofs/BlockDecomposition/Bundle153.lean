module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle512
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle003
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Mathlib.Algebra.Algebra.ZMod
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle133
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle026
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PairSums.SumPair
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GelfandSpectralNormalisation.NormalisedInvariants.PoitouTateExactSecond
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.smooth_sections_affine_flat : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), Smooth s →
    ∀ U : X.affineOpens, Module.Flat R (Sec s U.1) := by
  first | exact @GlobalTheory.CompanionTheory.Axis.flat_sec_of_smooth | exact GlobalTheory.CompanionTheory.Axis.flat_sec_of_smooth | (intros; apply GlobalTheory.CompanionTheory.Axis.flat_sec_of_smooth <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.DegenSeries

theorem isAdmissible_degenerate : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ →
    IsAdmissible (parInd (two (stdSum (rfl : a + b = a + b)))
      ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)) := by
  intro k _ _ _ _ a b χ₁ χ₂ _ _
  exact GlobalTheory.SmGL.ParIndAdm.isAdmissible_parInd _ _

end GlobalTheory.CompanionTheory.DegenSeries
end

section

noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt

namespace GlobalTheory.CompanionTheory.GreenbergWiles

theorem exists_primitiveRoot_of_isAlgClosure (F Ω : Type) [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] [IsAlgClosure F Ω] (n : ℕ) (hn : 0 < n) : ∃ ζ : Ω, IsPrimitiveRoot ζ n := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : NeZero (n : Ω) := ⟨Nat.cast_ne_zero.2 hn.ne'⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot Ω n

theorem poitouTate_instance : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (Av : S → ValuationSubring Ω) (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ) (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) (hρ : ContAction ρ), ∀ hμ : μ.comp (toGS Ω _) = cycMod F Ω l r, PoitouTateNormalised → l ≠ 2 → 0 < r → ContainsAbove S l → (∀ v : S, IsPlaceOver (Av v) v.1) → ∃ inv : InvFam F Ω l r, (∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → Function.Bijective (inv A)) ∧ NineTermExact S Av μ (invAt S Av μ hμ inv) ρ hρ ∧ ShaDual S Av μ ρ := by
  intro F Ω _ _ _ _ _ l _ r M _ _ _ _ _ S Av μ ρ hρ hμ hPT hl hr hS hAv
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_isAlgClosure F Ω (l ^ r)
    (pow_pos (Fact.out : l.Prime).pos r)
  obtain ⟨inv, h1, h2⟩ := hPT F Ω l r (Or.inl hl) hr ζ hζ
  obtain ⟨hN, hD, -⟩ := h2 S hS Av hAv μ hμ M ρ hρ
  exact ⟨inv, fun A v h => (h1 A v h).1, hN, hD⟩

end GlobalTheory.CompanionTheory.GreenbergWiles

end
end

section

noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion

namespace GlobalTheory.CompanionTheory.PTIso

section Gen

variable {R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {I : Type} [Fintype I] {D : I → Type} [∀ i, Group (D i)] [∀ i, TopologicalSpace (D i)]
  (φ : ∀ i, D i →* Γ) (hφ : ∀ i, Continuous (φ i))
  (χ : Γ →* Rˣ)
  (j : ∀ i, H2 ((charRep χ).comp (φ i)) →ₗ[R] R)
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
  (ρ : Representation R Γ M)

def gloc0 : H0 ρ →ₗ[R] ∀ i, H0 (ρ.comp (φ i)) :=
  LinearMap.pi fun i => resH0 ρ (φ i)

def gloc1 : H1 ρ →ₗ[R] ∀ i, H1 (ρ.comp (φ i)) :=
  LinearMap.pi fun i => resH1 ρ (φ i) (hφ i)

def gloc2 : H2 ρ →ₗ[R] ∀ i, H2 (ρ.comp (φ i)) :=
  LinearMap.pi fun i => resH2 ρ (φ i) (hφ i)

def gtr0 : (∀ i, H0 (ρ.comp (φ i))) →ₗ[R] Module.Dual R (H2 (twDual χ ρ)) :=
  ∑ i, (((cupH0H2TwistedDual χ ρ (φ i)).compr₂ (j i)).compl₁₂ (LinearMap.proj i)
    (resH2 (twDual χ ρ) (φ i) (hφ i)))

def gtr1 (hρ : ContAction ρ) : (∀ i, H1 (ρ.comp (φ i))) →ₗ[R] Module.Dual R (H1 (twDual χ ρ)) :=
  ∑ i, (((cupH1H1TwistedDual χ ρ (φ i) (hρ.comp' (hφ i))).flip.compr₂ (j i)).compl₁₂ (LinearMap.proj i)
    (resH1 (twDual χ ρ) (φ i) (hφ i)))

def gtr2 : (∀ i, H2 (ρ.comp (φ i))) →ₗ[R] Module.Dual R (H0 (twDual χ ρ)) :=
  ∑ i, (((cup20 χ ρ (φ i)).compr₂ (j i)).compl₁₂ (LinearMap.proj i)
    (resH0 (twDual χ ρ) (φ i)))

def NineG (hρ : ContAction ρ) : Prop :=
  ∃ (δ₁ : Module.Dual R (H2 (twDual χ ρ)) →ₗ[R] H1 ρ)
    (δ₂ : Module.Dual R (H1 (twDual χ ρ)) →ₗ[R] H2 ρ),
    Function.Injective (gloc0 φ ρ) ∧
    Function.Exact (gloc0 φ ρ) (gtr0 φ hφ χ j ρ) ∧
    Function.Exact (gtr0 φ hφ χ j ρ) δ₁ ∧
    Function.Exact δ₁ (gloc1 φ hφ ρ) ∧
    Function.Exact (gloc1 φ hφ ρ) (gtr1 φ hφ χ j ρ hρ) ∧
    Function.Exact (gtr1 φ hφ χ j ρ hρ) δ₂ ∧
    Function.Exact δ₂ (gloc2 φ hφ ρ) ∧
    Function.Exact (gloc2 φ hφ ρ) (gtr2 φ χ j ρ) ∧
    Function.Surjective (gtr2 φ χ j ρ)

def ShaG : Prop :=
  (Finite (Sha1 (twDual χ ρ) φ hφ) ∧ Finite (Sha2 ρ φ hφ) ∧
    Nonempty (Sha2 ρ φ hφ ≃ₗ[R] Module.Dual R (Sha1 (twDual χ ρ) φ hφ)) ∧
    Nat.card (Sha1 (twDual χ ρ) φ hφ) = Nat.card (Sha2 ρ φ hφ)) ∧
  (Finite (Sha1 ρ φ hφ) ∧ Finite (Sha2 (twDual χ ρ) φ hφ) ∧
    Nonempty (Sha2 (twDual χ ρ) φ hφ ≃ₗ[R] Module.Dual R (Sha1 ρ φ hφ)) ∧
    Nat.card (Sha1 ρ φ hφ) = Nat.card (Sha2 (twDual χ ρ) φ hφ))

end Gen

section Concrete

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] {r : ℕ} (S : Finset (HeightOneSpectrum (𝓞 F)))
  (Av : S → ValuationSubring Ω)
  (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ)
  (j : ∀ v : S, H2 ((charRep μ).comp (locFam S Av v)) →ₗ[ZMod (l ^ r)] ZMod (l ^ r))
  {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [TopologicalSpace M] [DiscreteTopology M]
  (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)

theorem nineTermExact_iff (hρ : ContAction ρ) :
    NineTermExact S Av μ j ρ hρ ↔
      NineG (locFam S Av) (continuous_locFam S Av) μ j ρ hρ := Iff.rfl

theorem shaDual_iff :
    ShaDual S Av μ ρ ↔ ShaG (locFam S Av) (continuous_locFam S Av) μ ρ := Iff.rfl

end Concrete

def subgroupIso {A B : Type} [Group A] [TopologicalSpace A] [Group B] [TopologicalSpace B]
    (Φ : A ≃ₜ* B) (H : Subgroup A) (K : Subgroup B) (h : ∀ a, a ∈ H ↔ Φ a ∈ K) : H ≃ₜ* K where
  toFun a := ⟨Φ a.1, (h a.1).1 a.2⟩
  invFun b := ⟨Φ.symm b.1, (h _).2 (by simpa using b.2)⟩
  left_inv a := Subtype.ext (by simp)
  right_inv b := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  continuous_toFun := (Φ.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (Φ.symm.continuous.comp continuous_subtype_val).subtype_mk _

end GlobalTheory.CompanionTheory.PTIso
end
end

section

noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.S2pt

namespace GlobalTheory.CompanionTheory.LocalPerfect

section General

variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {Γ : Type*} [Group Γ] {M : Type*} [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [DiscreteTopology M]
  {D : Type*} [Group D] [TopologicalSpace D]
  (χ : Γ →* Rˣ) (ρ : Representation R Γ M) (φ : D →* Γ) (χ' : D →* Rˣ)

theorem twDual_comp_apply (h : χ.comp φ = χ') (g : D) (y : TDual R M) :
    ((twDual χ ρ).comp φ) g y = ((twDual χ' (ρ.comp φ)).comp (MonoidHom.id D)) g y := by
  subst h
  apply LinearMap.ext
  intro m
  change ((χ (φ g) : Rˣ) : R) * y (ρ (φ g)⁻¹ m) =
    ((χ (φ g) : Rˣ) : R) * y (ρ (φ g⁻¹) m)
  rw [map_inv φ]

def dualMap (h : χ.comp φ = χ') :
    H1 ((twDual χ ρ).comp φ) →ₗ[R] H1 ((twDual χ' (ρ.comp φ)).comp (MonoidHom.id D)) :=
  mapH1 _ _ LinearMap.id continuous_id (twDual_comp_apply χ ρ φ χ' h)

def coefMap : H1 (ρ.comp φ) →ₗ[R] H1 ((ρ.comp φ).comp (MonoidHom.id D)) :=
  mapH1 _ _ LinearMap.id continuous_id (fun _ _ => rfl)

theorem dualMap_bijective (h : χ.comp φ = χ') : Function.Bijective (dualMap χ ρ φ χ' h) := by
  refine Function.bijective_iff_has_inverse.2 ⟨mapH1 _ _ LinearMap.id continuous_id
    (fun g y => (twDual_comp_apply χ ρ φ χ' h g y).symm), fun x => ?_, fun x => ?_⟩
  · induction x using Submodule.Quotient.induction_on with
    | H z => rfl
  · induction x using Submodule.Quotient.induction_on with
    | H z => rfl

theorem coefMap_bijective : Function.Bijective (coefMap ρ φ) := by
  refine Function.bijective_iff_has_inverse.2 ⟨mapH1 ((ρ.comp φ).comp (MonoidHom.id D)) (ρ.comp φ)
    LinearMap.id continuous_id (fun _ _ => rfl), fun x => ?_, fun x => ?_⟩
  · induction x using Submodule.Quotient.induction_on with
    | H z => rfl
  · induction x using Submodule.Quotient.induction_on with
    | H z => rfl

theorem mapH2_cup_product_naturality (h : χ.comp φ = χ') (hc : ContAction (ρ.comp φ))
    (hc' : ContAction ((ρ.comp φ).comp (MonoidHom.id D)))
    (hq : ∀ (g : D) (m : R), ((charRep χ).comp φ) g m = charRep χ' g m)
    (y : H1 ((twDual χ ρ).comp φ)) (x : H1 (ρ.comp φ)) :
    mapH2 ((charRep χ).comp φ) (charRep χ') LinearMap.id continuous_id hq
        (cupH1H1TwistedDual χ ρ φ hc y x) =
      cupH1H1TwistedDual χ' (ρ.comp φ) (MonoidHom.id D) hc' (dualMap χ ρ φ χ' h y) (coefMap ρ φ x) := by
  induction y using Submodule.Quotient.induction_on with
  | H y =>
    induction x using Submodule.Quotient.induction_on with
    | H x => rfl

theorem injective_compr₂ (h : χ.comp φ = χ') (hc : ContAction (ρ.comp φ))
    (hc' : ContAction ((ρ.comp φ).comp (MonoidHom.id D)))
    (hq : ∀ (g : D) (m : R), ((charRep χ).comp φ) g m = charRep χ' g m)
    {P : H2 (charRep χ') →ₗ[R] R} (hP : Function.Injective P)
    (hL : Function.Injective (cupH1H1TwistedDual χ' (ρ.comp φ) (MonoidHom.id D) hc'))
    (hF : Function.Injective (cupH1H1TwistedDual χ' (ρ.comp φ) (MonoidHom.id D) hc').flip) :
    Function.Injective ((cupH1H1TwistedDual χ ρ φ hc).compr₂
        (P.comp (mapH2 ((charRep χ).comp φ) (charRep χ') LinearMap.id continuous_id hq))) ∧
      Function.Injective ((cupH1H1TwistedDual χ ρ φ hc).compr₂
        (P.comp (mapH2 ((charRep χ).comp φ) (charRep χ') LinearMap.id continuous_id hq))).flip := by
  have key : ∀ y x y' x', P (mapH2 ((charRep χ).comp φ) (charRep χ') LinearMap.id continuous_id hq
        (cupH1H1TwistedDual χ ρ φ hc y x)) =
      P (mapH2 ((charRep χ).comp φ) (charRep χ') LinearMap.id continuous_id hq
        (cupH1H1TwistedDual χ ρ φ hc y' x')) →
      cupH1H1TwistedDual χ' (ρ.comp φ) (MonoidHom.id D) hc' (dualMap χ ρ φ χ' h y) (coefMap ρ φ x) =
      cupH1H1TwistedDual χ' (ρ.comp φ) (MonoidHom.id D) hc' (dualMap χ ρ φ χ' h y') (coefMap ρ φ x') := by
    intro y x y' x' e
    have := hP e
    rwa [mapH2_cup_product_naturality χ ρ φ χ' h hc hc' hq, mapH2_cup_product_naturality χ ρ φ χ' h hc hc' hq] at this
  refine ⟨fun y y' e => (dualMap_bijective χ ρ φ χ' h).1 (hL (LinearMap.ext fun x => ?_)),
    fun x x' e => (coefMap_bijective ρ φ).1 (hF (LinearMap.ext fun y => ?_))⟩
  · obtain ⟨x, rfl⟩ := (coefMap_bijective ρ φ).2 x
    exact key y x y' x (LinearMap.congr_fun e x)
  · obtain ⟨y, rfl⟩ := (dualMap_bijective χ ρ φ χ' h).2 y
    exact key y x y x' (LinearMap.congr_fun e y)

end General

theorem locPerfect (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M]
    [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (Av : S → ValuationSubring Ω)
    (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ)
    (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
    (hρ : ContAction ρ) (hμ : μ.comp (toGS Ω _) = cycMod F Ω l r) (hT : LocalTateDuality)
    (hr : 0 < r) (inv : InvFam F Ω l r)
    (hinv : ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v →
      Function.Bijective (inv A))
    (hA : ∀ v : S, IsPlaceOver (Av v) v.1) (v : S) :
    Function.Injective ((cupH1H1TwistedDual μ ρ (locFam S Av v)
        (hρ.comp' (continuous_locFam S Av v))).compr₂ (invAt S Av μ hμ inv v)) ∧
      Function.Injective ((cupH1H1TwistedDual μ ρ (locFam S Av v)
        (hρ.comp' (continuous_locFam S Av v))).compr₂ (invAt S Av μ hμ inv v)).flip := by
  have hc := hρ.comp' (continuous_locFam S Av v)
  have hχ : μ.comp (locFam S Av v) = (cycMod F Ω l r).comp (Dec (F := F) (Av v)).subtype :=
    MonoidHom.ext fun g => DFunLike.congr_fun hμ (g : G F Ω)
  obtain ⟨-, -, h1, h2, -⟩ := hT F Ω l r M (Av v) (ρ.comp (locFam S Av v)) v.1 hr (hA v) hc
  exact injective_compr₂ μ ρ (locFam S Av v) _ hχ _ (hc.comp' continuous_id)
    (locFam_apply_eq S Av μ hμ v) (hinv _ _ (hA v)).1 h1.1 h2.1

end GlobalTheory.CompanionTheory.LocalPerfect

end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

theorem _root_.GlobalTheory.T.cell_functor_scalar_diagonal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ) (B : SizeMatrix (Two (Fin a) (Fin b)) (Two (Fin a) (Fin b))) (f : ∀ i, (Σ j, Fin (B.1 i j)) ≃ Two (Fin a) (Fin b) i) (g : ∀ j, (Σ i, Fin (B.1 i j)) ≃ Two (Fin a) (Fin b) j), B.1 false true = 0 → (∀ φ ψ : (cellFunctor f g ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)).IntertwiningMap (((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)), φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap) := by
  first | exact @GlobalTheory.CompanionTheory.CellDiag.diag_cell_at_most_one_map | exact GlobalTheory.CompanionTheory.CellDiag.diag_cell_at_most_one_map | (intros; apply GlobalTheory.CompanionTheory.CellDiag.diag_cell_at_most_one_map <;> assumption)
end

section

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.ChartBij
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

variable {n d : ℕ}

def coord (k : Fin d) (g : Gam n d) : E n d → ℤ
  | Sum.inl l => g (Sum.inl l)
  | Sum.inr j => if j = k then tdeg g else g (Sum.inr j)

theorem coord_add (k : Fin d) (g g' : Gam n d) : coord k (g + g') = coord k g + coord k g' := by
  funext e
  rcases e with l | j
  · rfl
  · by_cases h : j = k
    · simp [coord, h, tdeg_add]
    · simp [coord, h]

theorem coord_zero (k : Fin d) : coord k (0 : Gam n d) = 0 := by
  funext e
  rcases e with l | j
  · rfl
  · by_cases h : j = k
    · simp [coord, h, tdeg]
    · simp [coord, h]

theorem tdeg_ratE (k j : Fin d) : tdeg (ratE k j : Gam n d) = 0 := by
  have h1 := tdeg_add (ratE k j : Gam n d) (oneE (Sum.inr k))
  have h2 : (ratE k j : Gam n d) + oneE (Sum.inr k) = oneE (Sum.inr j) := by simp [ratE]
  rw [h2, tdeg_oneE_inr, tdeg_oneE_inr] at h1
  linarith

theorem coord_wv (k : Fin d) (e e' : E n d) : coord k (wv k e) e' = if e' = e then 1 else 0 := by
  rcases e with l | j <;> rcases e' with l' | j'
  · simp [coord, wv, oneE, Pi.single_apply]
  · by_cases h : j' = k
    · simp [coord, wv, oneE, h, tdeg, Pi.single_apply]
    · simp [coord, wv, oneE, h, Pi.single_apply]
  · by_cases h : j = k
    · simp [coord, wv, oneE, h, Pi.single_apply]
    · simp [coord, wv, ratE, oneE, h, Pi.single_apply]
  · by_cases h : j = k
    · subst h
      by_cases h' : j' = j
      · simp [coord, wv, h', tdeg_oneE_inr]
      · simp [coord, wv, oneE, h', Pi.single_apply]
    · by_cases h' : j' = k
      · subst h'
        have hne : ¬ j' = j := fun e => h e.symm
        simp [coord, wv, h, hne, tdeg_ratE]
      · by_cases h'' : j' = j
        · subst h''
          simp [coord, wv, ratE, oneE, h, h', Pi.single_apply]
        · simp [coord, wv, ratE, oneE, h, h', h'', Pi.single_apply]

theorem coord_inj (k : Fin d) {g g' : Gam n d} (h : coord k g = coord k g') : g = g' := by
  have hj : ∀ j, j ≠ k → g (Sum.inr j) = g' (Sum.inr j) := fun j hj => by
    have := congrFun h (Sum.inr j)
    simpa [coord, hj] using this
  have ht : tdeg g = tdeg g' := by
    have := congrFun h (Sum.inr k)
    simpa [coord] using this
  funext e
  rcases e with l | j
  · exact congrFun h (Sum.inl l)
  · by_cases hjk : j = k
    · subst hjk
      unfold tdeg at ht
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), ← Finset.add_sum_erase _ _ (Finset.mem_univ j)] at ht
      have : ∑ x ∈ Finset.univ.erase j, g (Sum.inr x) = ∑ x ∈ Finset.univ.erase j, g' (Sum.inr x) :=
        Finset.sum_congr rfl fun x hx => hj x (Finset.ne_of_mem_erase hx)
      linarith
    · exact hj j hjk

def toCone (k : Fin d) : (E n d →₀ ℕ) →+ (cone {k} : AddSubmonoid (Gam n d)) :=
  Finsupp.liftAddHom fun e => multiplesHom _ ⟨wv k e, wv_mem (Finset.mem_singleton_self k) e⟩

theorem toCone_single (k : Fin d) (e : E n d) :
    toCone k (Finsupp.single e 1) = ⟨wv k e, wv_mem (Finset.mem_singleton_self k) e⟩ := by
  simp [toCone]

theorem coord_toCone (k : Fin d) (f : E n d →₀ ℕ) (e : E n d) :
    coord k (toCone k f : Gam n d) e = f e := by
  induction f using Finsupp.induction_linear with
  | zero => simp [coord_zero]
  | add f g hf hg =>
    rw [map_add (f := _), AddSubmonoid.coe_add, coord_add, Pi.add_apply, hf, hg]
    simp
  | single a b =>
    induction b with
    | zero => simp [coord_zero]
    | succ b ih =>
      rw [show Finsupp.single a (b + 1) = Finsupp.single a b + Finsupp.single a 1 by simp,
        map_add, AddSubmonoid.coe_add, coord_add, Pi.add_apply, ih, toCone_single]
      simp only [coord_wv, Finsupp.add_apply, Finsupp.single_apply]
      by_cases h : e = a
      · simp [h]
      · have : ¬ a = e := fun x => h x.symm
        simp [h, this]

theorem toCone_injective (k : Fin d) : Function.Injective (toCone k : (E n d →₀ ℕ) → _) := by
  intro f f' h
  ext e
  have h1 := coord_toCone k f e
  rw [h, coord_toCone] at h1
  exact_mod_cast h1.symm

theorem coord_nonneg (k : Fin d) {g : Gam n d} (hg : g ∈ (cone {k} : AddSubmonoid (Gam n d))) (e : E n d) :
    0 ≤ coord k g e := by
  rcases e with l | j
  · exact hg.1 l
  · by_cases h : j = k
    · simpa [coord, h] using hg.2.2
    · simpa [coord, h] using hg.2.1 j (by simpa using h)

theorem toCone_surjective (k : Fin d) : Function.Surjective (toCone k : (E n d →₀ ℕ) → _) := by
  rintro ⟨g, hg⟩
  refine ⟨Finsupp.equivFunOnFinite.symm fun e => (coord k g e).toNat, Subtype.ext (coord_inj k ?_)⟩
  funext e
  rw [coord_toCone]
  simpa using coord_nonneg k hg e

def coneEquiv (k : Fin d) : (E n d →₀ ℕ) ≃+ (cone {k} : AddSubmonoid (Gam n d)) :=
  AddEquiv.ofBijective (toCone k) ⟨toCone_injective k, toCone_surjective k⟩

theorem chart_bijective {K : Type} [Field K] {n d : ℕ} (k : Fin d) :
    Function.Bijective (MvPolynomial.aeval (R := K)
      (fun e : E n d => mon K (wv k e) (wv_mem (Finset.mem_singleton_self k) e)) : Bp K n d →ₐ[K] R0 K n d {k}) := by
  let Φ : Bp K n d ≃ₐ[K] R0 K n d {k} := AddMonoidAlgebra.domCongr K K (coneEquiv k)
  have h : (MvPolynomial.aeval (R := K)
      (fun e : E n d => mon K (wv k e) (wv_mem (Finset.mem_singleton_self k) e)) : Bp K n d →ₐ[K] R0 K n d {k}) = Φ.toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro e
    rw [MvPolynomial.aeval_X]
    change _ = AddMonoidAlgebra.domCongr K K (coneEquiv k) (AddMonoidAlgebra.single (Finsupp.single e 1) 1)
    simp only [mon, coneEquiv]
    simp
    exact congrArg (fun m => AddMonoidAlgebra.single m (1 : K)) (toCone_single k e).symm
  rw [h]
  exact Φ.bijective

end GlobalTheory.CompanionTheory.SurjectionOntoH4.ChartBij
end
end

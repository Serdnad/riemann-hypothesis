module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.BaseCase
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
import GroundTheory.LocalFields.LocalFourierHaar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle997
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportKeepsProductsCosocles
import GroundTheory.GlobalFields.CompletionAtPlace.Galois
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchCut

@[expose] public section

section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private def selfPl {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) : PlacesOver K v :=
  ⟨v, ⟨Ideal.ext fun _ => Iff.rfl⟩⟩

private theorem cm_id {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (x : v.adicCompletion K) : completionMap v (selfPl v).1 x = x := by
  refine congrFun ((HeightOneSpectrum.denseRange_algebraMap K v).equalizer
    (continuous_completionMap v (selfPl v).1) continuous_id (funext fun y => ?_)) x
  simp only [Function.comp_apply, id]
  rw [completionMap_algebraMap]
  rfl

private theorem map_refl {R : Type} [CommRing R] {n : ℕ} (g : GL (Fin n) R) :
    Matrix.GeneralLinearGroup.map (RingEquiv.refl R).toRingHom g = g := by
  ext i j
  simp

theorem UpperTheory.Gal.InertialTypesAlt.baseCase :
    ResEmbCompat → LblIso → BaseCase := by
  intro hC hI K Ω _ _ _ _ _ n π A Θ v e e' he he' τ τ' hτ hτ' a ha
  have H : ∃ (r : 𝓀[v.adicCompletion K] →+* 𝓀[v.adicCompletion K])
      (j : AlgebraicClosure 𝓀[v.adicCompletion K] ≃+* AlgebraicClosure 𝓀[v.adicCompletion K]),
      (∀ (x y : 𝒪[v.adicCompletion K]), (y : v.adicCompletion K) = x →
        IsLocalRing.residue _ y = r (IsLocalRing.residue _ x)) ∧
      (∀ x, j (algebraMap _ _ x) = algebraMap _ _ (r x)) ∧ ∀ x, e' (j x) = e x := by
    obtain ⟨r, j, h1, h2, h3⟩ := hC K K Ω A v (selfPl v) e e' he he'
    exact ⟨r, j, fun x y h => h1 x y (h.trans (cm_id v _).symm), h2, h3⟩
  obtain ⟨r, j, h1, h2, h3⟩ := H
  obtain ⟨E⟩ := GlobalTheory.CuspRep.LocUniq.isLocComp_unique π v τ τ' hτ hτ'
  have hθ : (Θ.comp e'.toMonoidHom).comp j.toMonoidHom = Θ.comp e.toMonoidHom := by
    ext x
    simp [h3]
  refine hI (v.adicCompletion K) (v.adicCompletion K) (RingEquiv.refl _) (fun _ => Iff.rfl) j ?_
    (Θ.comp e'.toMonoidHom) n τ.V τ'.V τ.ρ τ'.ρ E.toLinearEquiv ?_ a (by rw [hθ]; exact ha)
  · intro x y hxy
    rw [h2, h1 x y hxy]
  · intro g x
    rw [map_refl]
    exact LinearMap.congr_fun (E.isIntertwining' g) x
end

section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped Pointwise in
private theorem ine_restrict {K M Ω : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Field Ω] [Algebra K M] [Algebra K Ω]
    [Algebra M Ω] [IsScalarTower K M Ω] (A : ValuationSubring Ω) (t : G M Ω) (ht : t ∈ Ine (F := M) A) :
    (AlgEquiv.restrictScalars K t : G K Ω) ∈ Ine (F := K) A := by
  obtain ⟨h1, h2⟩ := ht
  refine ⟨?_, fun x hx => h2 x hx⟩
  have h1' : t • A = A := h1
  show (AlgEquiv.restrictScalars K t : G K Ω) • A = A
  have : (AlgEquiv.restrictScalars K t : G K Ω) • A = t • A := by
    ext x
    simp only [ValuationSubring.mem_smul_pointwise_iff_exists]
    rfl
  rw [this, h1']

private theorem place_unique {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (A : ValuationSubring Ω)
    (v w : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A v) (h' : IsPlaceOver A w) : v = w := by
  apply HeightOneSpectrum.ext
  ext x
  rw [← h x, ← h' x]

private theorem le_closed (P₀ : Lbl → Prop) (hl : ∀ a l, P₀ a → P₀ (a.lift l)) {a b : Lbl} (h : a.Le b) (ha : P₀ a) : P₀ b := by
  induction h with
  | refl => exact ha
  | tail _ hbc ih =>
    obtain ⟨l, _, rfl⟩ := hbc
    exact hl _ _ ih

theorem UpperTheory.Gal.InertialTypesAlt.lblOn :
    BaseCase → LiftsFix → PlaceEx → ResEmbEx → UnrOfIne → ∀ P₀ : Lbl → Prop, (∀ a l, P₀ a → P₀ (a.lift l)) → StepAt P₀ id → StepAt P₀ Not → LblOn P₀ := by
  intro hB hF hP hR hU P₀ hl hS hN E Ω _ _ _ n hn X Y hXY A Θ hΘ
  induction hXY using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro _ v w hv hw e e' he he' τ τ' hτ hτ' a _ hL
    obtain rfl := place_unique A v w hv hw
    exact ⟨a, Relation.ReflTransGen.refl, hB Y.K Ω n Y.π A Θ v e e' he he' τ τ' hτ hτ' a hL⟩
  | @head X Z hXZ hZY ih =>
    intro hI v w hv hw e e' he he' τ τ' hτ hτ' a ha hL
    obtain ⟨i1, i2, hGal, hpr, hW⟩ := hXZ
    obtain ⟨u, hu, τ₁, hτ₁⟩ := hP X.K Z.K Ω A v hv n Z.π
    obtain ⟨⟨e₁, he₁⟩, _⟩ := hR Z.K Ω A u hu
    have hIZ : ∀ t ∈ Ine (F := X.K) A, UpperTheory.Gal.UnramifiedFromSplittingCriterion.Fixes Z.K t := by
      intro t ht x
      obtain ⟨y, hy⟩ := hF E Ω n Z Y hZY x
      rw [← hy]
      exact hI t ht y
    obtain ⟨hund, hUnr, _⟩ := hU X.K Z.K Ω A v u hv hu hIZ
    let u' : PlacesOver Z.K v := ⟨u, ⟨by rw [← hund]; rfl⟩⟩
    have hb : ∃ b₁, a.Le b₁ ∧ HasLbl (Θ.comp e₁.toMonoidHom) τ₁.ρ b₁ := by
      by_cases hs : UpperTheory.ConvolutionTheory.GM.Split Z.K v
      · exact hS X.K Z.K Ω hpr n hn X.π Z.π hW A Θ hΘ v u' hs hUnr e e₁ he he₁ τ τ₁ hτ hτ₁ a ha hL
      · exact hN X.K Z.K Ω hpr n hn X.π Z.π hW A Θ hΘ v u' hs hUnr e e₁ he he₁ τ τ₁ hτ hτ₁ a ha hL
    obtain ⟨b₁, hab, hb₁⟩ := hb
    have hIZ' : ∀ t ∈ Ine (F := Z.K) A, UpperTheory.Gal.UnramifiedFromSplittingCriterion.Fixes Y.K t := by
      intro t ht y
      exact hI _ (ine_restrict (K := X.K) A t ht) y
    obtain ⟨b, hbb, hbL⟩ := ih hIZ' u w hu hw e₁ e' he₁ he' τ₁ τ' hτ₁ hτ' b₁ (le_closed P₀ hl hab ha) hb₁
    exact ⟨b, hab.trans hbb, hbL⟩
end

section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem detc_isChar {F : Type} [Field F] (θ : AlgebraicClosure F →* ℂ) (t k : ℕ) :
    GlobalTheory.BI.IsChar ℂ ℂ (detc θ t k) := by
  let χ : GL (Fin t) F →* ℂ := (powMonoidHom k).comp (θ.comp
    ((algebraMap F (AlgebraicClosure F)).toMonoidHom.comp
      ((Units.coeHom F).comp Matrix.GeneralLinearGroup.det)))
  refine ⟨1, (algebraMap ℂ (Module.End ℂ (Fin 1 → ℂ))).toMonoidHom.comp χ, fun g => ?_⟩
  simp [Representation.character, χ, detc, Module.algebraMap_end_eq_smul_id, LinearMap.trace_id]

private theorem jd_isChar (hH : HcChar) {F : Type} [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ)
    (L : List (ℕ × ℕ)) (hL : GlobalTheory.BI.IsChar ℂ ℂ (J θ L (deg L))) (D : List (ℕ × ℕ)) :
    GlobalTheory.BI.IsChar ℂ ℂ (JD θ D L (deg D + deg L)) := by
  induction D with
  | nil =>
    have e : deg ([] : List (ℕ × ℕ)) + deg L = deg L := by simp [GlobalTheory.Shin.deg]
    rw [e, JD_nil]
    exact hL
  | cons p D ih =>
    rw [JD_cons]
    refine hH F p.1 (deg D + deg L) _ ?_ _ _ (detc_isChar θ p.1 p.2) ih
    simp [GlobalTheory.Shin.deg, add_assoc]

theorem UpperTheory.Gal.InertialTypesAlt.jdChar :
    HcChar → JDChar := by
  intro hH F _ _ θ hθ
  refine ⟨detc_isChar θ, fun a hok hq => ?_⟩
  obtain ⟨-, -, hL⟩ := hok
  have hJ := GlobalTheory.T.isCharacter_harishChandraProductCuspidalGL_of_regular F θ hθ a.L (fun p hp => by rw [← hq]; exact hL p hp) _ rfl
  exact jd_isChar hH θ a.L hJ a.D
end

section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

section SlopeTestRemainingChoices

open GlobalTheory.Parabolic (mem_fixed)

variable {k K : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

private def intEquiv (i : k ≃+* K) (hi : ∀ x : k, valuation K (i x) ≤ 1 ↔ valuation k x ≤ 1) : 𝒪[k] ≃+* 𝒪[K] where
  toFun x := ⟨i x, (hi x).2 x.2⟩
  invFun y := ⟨i.symm y, (hi _).1 (by rw [i.apply_symm_apply]; exact y.2)⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

private def resEquiv (i₀ : 𝒪[k] ≃+* 𝒪[K]) : 𝓀[k] ≃+* 𝓀[K] := IsLocalRing.ResidueField.mapEquiv i₀

private def glEquiv {F F' : Type} [Field F] [Field F'] (r : F ≃+* F') (n : ℕ) : GL (Fin n) F ≃ GL (Fin n) F' where
  toFun := Matrix.GeneralLinearGroup.map r.toRingHom
  invFun := Matrix.GeneralLinearGroup.map r.symm.toRingHom
  left_inv g := by ext a b; simp
  right_inv g := by ext a b; simp

variable (i : k ≃+* K) (hi : ∀ x : k, valuation K (i x) ≤ 1 ↔ valuation k x ≤ 1) {n : ℕ}

include hi

private theorem map_alg (u : GL (Fin n) 𝒪[k]) :
    Matrix.GeneralLinearGroup.map i.toRingHom (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) u) =
      Matrix.GeneralLinearGroup.map (algebraMap 𝒪[K] K)
        (Matrix.GeneralLinearGroup.map (intEquiv i hi).toRingHom u) := by
  ext a b; rfl

private theorem map_mem_KO {g : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) :
    Matrix.GeneralLinearGroup.map i.toRingHom g ∈ KO K (Fin n) := by
  obtain ⟨u, rfl⟩ := hg
  exact ⟨_, (map_alg i hi u).symm⟩

private theorem exists_KO {y : GL (Fin n) K} (hy : y ∈ KO K (Fin n)) :
    ∃ g ∈ KO k (Fin n), Matrix.GeneralLinearGroup.map i.toRingHom g = y := by
  obtain ⟨u, rfl⟩ := hy
  refine ⟨_, ⟨Matrix.GeneralLinearGroup.map (intEquiv i hi).symm.toRingHom u, rfl⟩, ?_⟩
  rw [map_alg i hi]
  congr 1
  ext a b
  simp

private theorem red_map (g : KO k (Fin n)) :
    redK K (Fin n) ⟨Matrix.GeneralLinearGroup.map i.toRingHom g, map_mem_KO i hi g.2⟩ =
      Matrix.GeneralLinearGroup.map (resEquiv (intEquiv i hi)).toRingHom (redK k (Fin n) g) := by
  ext a b
  rw [redK_apply]
  show _ = resEquiv (intEquiv i hi) ((redK k (Fin n) g : Matrix (Fin n) (Fin n) 𝓀[k]) a b)
  rw [redK_apply]
  rfl

private theorem map_mem_KOne_iff {g : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) :
    Matrix.GeneralLinearGroup.map i.toRingHom g ∈ KOne K (Fin n) ↔ g ∈ KOne k (Fin n) := by
  rw [← redK_eq_one_iff ⟨g, hg⟩, ← redK_eq_one_iff ⟨_, map_mem_KO i hi hg⟩, red_map i hi ⟨g, hg⟩]
  constructor
  · intro h
    have := congrArg (glEquiv (resEquiv (intEquiv i hi)) n).symm h
    rw [show Matrix.GeneralLinearGroup.map (resEquiv (intEquiv i hi)).toRingHom (redK k (Fin n) ⟨g, hg⟩) =
      glEquiv (resEquiv (intEquiv i hi)) n (redK k (Fin n) ⟨g, hg⟩) from rfl, Equiv.symm_apply_apply] at this
    rw [this]
    exact map_one (Matrix.GeneralLinearGroup.map (resEquiv (intEquiv i hi)).symm.toRingHom)
  · intro h
    rw [h, map_one]

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (GL (Fin n) k) V) (P : Representation ℂ (GL (Fin n) K) W) (e : V ≃ₗ[ℂ] W)
  (he : ∀ g x, e (π g x) = P (Matrix.GeneralLinearGroup.map i.toRingHom g) (e x))

include he in
private theorem map_fixed :
    (fixed π (KOne k (Fin n))).map (e : V →ₗ[ℂ] W) = fixed P (KOne K (Fin n)) := by
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine mem_fixed.2 fun y hy => ?_
    obtain ⟨g, hg, rfl⟩ := exists_KO i hi (GlobalTheory.StepData.KOne_le_KO hy)
    show P _ (e x) = e x
    rw [← he, mem_fixed.1 hx g ((map_mem_KOne_iff i hi hg).1 hy)]
  · intro hw
    refine ⟨e.symm w, mem_fixed.2 fun g hg => ?_, by simp⟩
    apply e.injective
    rw [he, e.apply_symm_apply,
      mem_fixed.1 hw _ ((map_mem_KOne_iff i hi (GlobalTheory.StepData.KOne_le_KO hg)).2 hg)]

private def fixEquiv : fixed π (KOne k (Fin n)) ≃ₗ[ℂ] fixed P (KOne K (Fin n)) :=
  e.ofSubmodules _ _ (map_fixed i hi π P e he)

private theorem fixEquiv_level (γ : GL (Fin n) 𝓀[k]) (x : fixed π (KOne k (Fin n))) :
    fixEquiv i hi π P e he (levelZero π γ x) =
      levelZero P (Matrix.GeneralLinearGroup.map (resEquiv (intEquiv i hi)).toRingHom γ)
        (fixEquiv i hi π P e he x) := by
  obtain ⟨g, rfl⟩ := redK_surjective γ
  rw [← red_map i hi g]
  apply Subtype.ext
  rw [levelZero_apply]
  show e (levelZero π (redK k (Fin n) g) x : V) = P _ (e x)
  rw [levelZero_apply, he]

include he in
private theorem trace_level (γ : GL (Fin n) 𝓀[k]) :
    LinearMap.trace ℂ _ (levelZero P (Matrix.GeneralLinearGroup.map (resEquiv (intEquiv i hi)).toRingHom γ)) =
      LinearMap.trace ℂ _ (levelZero π γ) := by
  have h : levelZero P (Matrix.GeneralLinearGroup.map (resEquiv (intEquiv i hi)).toRingHom γ) =
      (fixEquiv i hi π P e he).conj (levelZero π γ) := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨y, rfl⟩ := (fixEquiv i hi π P e he).surjective x
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply, fixEquiv_level]
  rw [h, LinearMap.trace_conj']

end SlopeTestRemainingChoices

theorem UpperTheory.Gal.InertialTypesAlt.lblIso :
    JDIso → LblIso := by
  intro hJ k _ _ _ _ K _ _ _ _ i hi j hj θ N V W _ _ _ _ π P e he a ha
  obtain ⟨hok, hq, hn, hm⟩ := ha
  have hjr : ∀ x, j (algebraMap _ _ x) = algebraMap _ _ (resEquiv (intEquiv i hi) x) := by
    intro x
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
    exact hj y (intEquiv i hi y) rfl
  refine ⟨hok, hq.trans (Nat.card_congr (resEquiv (intEquiv i hi)).toEquiv), hn, ?_⟩
  unfold Meets at hm ⊢
  rw [← finsum_comp_equiv (glEquiv (resEquiv (intEquiv i hi)) N)]
  have key : ∀ γ : GL (Fin N) 𝓀[k],
      star (JD θ a.D a.L N (glEquiv (resEquiv (intEquiv i hi)) N γ)) *
          LinearMap.trace ℂ _ (levelZero P (glEquiv (resEquiv (intEquiv i hi)) N γ)) =
        star (JD (θ.comp j.toMonoidHom) a.D a.L N γ) * LinearMap.trace ℂ _ (levelZero π γ) := by
    intro γ
    rw [← hJ _ _ (resEquiv (intEquiv i hi)) j hjr θ a.D a.L N γ, ← trace_level i hi π P e he γ]
    rfl
  rw [finsum_congr key]
  exact hm
end
end

section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.resDeg :
    CardRes → ResDeg := by
  intro hcard K M _ _ _ _ _ _ hn v w hns hunr _
  classical
  have hw : (w : HeightOneSpectrum (𝓞 M)).asIdeal.LiesOver v.asIdeal := w.2
  set f := (w : HeightOneSpectrum (𝓞 M)).asIdeal.inertiaDeg (𝓞 K) with hf
  have hfconst : ∀ u : PlacesOver M v,
      (u : HeightOneSpectrum (𝓞 M)).asIdeal.inertiaDeg (𝓞 K) = f := by
    intro u
    haveI := u.2
    exact Ideal.inertiaDeg_eq_of_isGaloisGroup v.asIdeal _ _ Gal(M/K)
  have heone : ∀ u : PlacesOver M v,
      (u : HeightOneSpectrum (𝓞 M)).asIdeal.ramificationIdx (𝓞 K) = 1 := by
    intro u
    haveI := hunr u
    exact Ideal.ramificationIdx_eq_one _ _
  have hsum := GroundTheory.Global.SemiLocal.sum_ramificationIdx_mul_inertiaDeg M v
  have hdvd : f ∣ Module.finrank K M := by
    rw [← hsum]
    apply Finset.dvd_sum
    intro u _
    rw [heone u, hfconst u, one_mul]
  have hf1 : f ≠ 1 := by
    intro h1
    apply hns
    intro u
    haveI := u.2
    have hrk := GroundTheory.Global.SemiLocal.finrank_eq_ramificationIdx_mul_inertiaDeg M v
      (u : HeightOneSpectrum (𝓞 M))
    rw [heone u, hfconst u, h1, one_mul] at hrk
    have htop := Subalgebra.bot_eq_top_of_finrank_eq_one hrk
    intro y
    have hy : y ∈ (⊥ : Subalgebra (HeightOneSpectrum.adicCompletion K v)
        (HeightOneSpectrum.adicCompletion M (u : HeightOneSpectrum (𝓞 M)))) := by
      rw [htop]
      trivial
    obtain ⟨x, hx⟩ := Algebra.mem_bot.mp hy
    exact ⟨x, hx⟩
  have hfn : f = Module.finrank K M := (hn.eq_one_or_self_of_dvd f hdvd).resolve_left hf1
  have hnormK : normV v = v.asIdeal.absNorm := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  have hnormM : normV (w : HeightOneSpectrum (𝓞 M)) =
      (w : HeightOneSpectrum (𝓞 M)).asIdeal.absNorm := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  have hpow : v.asIdeal.absNorm ^ f = (w : HeightOneSpectrum (𝓞 M)).asIdeal.absNorm :=
    Ideal.absNorm_pow_inertiaDeg v.asIdeal _
  have hK := hcard K v
  have hM := hcard M (w : HeightOneSpectrum (𝓞 M))
  have hge : 2 ≤ v.asIdeal.absNorm := by
    have h0 : v.asIdeal.absNorm ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact v.ne_bot
    have h1 : v.asIdeal.absNorm ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]
      exact v.isPrime.ne_top
    omega
  have hcardM : Nat.card 𝓀[HeightOneSpectrum.adicCompletion M (w : HeightOneSpectrum (𝓞 M))] =
      Nat.card 𝓀[HeightOneSpectrum.adicCompletion K v] ^ Module.finrank K M := by
    rw [hM, hK, hnormM, hnormK, ← hpow, hfn]
  haveI : Finite 𝓀[HeightOneSpectrum.adicCompletion K v] :=
    Nat.finite_of_card_ne_zero (by rw [hK, hnormK]; omega)
  haveI : Finite 𝓀[HeightOneSpectrum.adicCompletion M (w : HeightOneSpectrum (𝓞 M))] :=
    Nat.finite_of_card_ne_zero (by rw [hcardM, hK, hnormK]; positivity)
  letI := Fintype.ofFinite 𝓀[HeightOneSpectrum.adicCompletion K v]
  haveI : Module.Finite 𝓀[HeightOneSpectrum.adicCompletion K v]
      𝓀[HeightOneSpectrum.adicCompletion M (w : HeightOneSpectrum (𝓞 M))] :=
    Module.Finite.of_finite
  refine ⟨?_, ?_⟩
  · have hc := Module.natCard_eq_pow_finrank (K := 𝓀[HeightOneSpectrum.adicCompletion K v])
      (V := 𝓀[HeightOneSpectrum.adicCompletion M (w : HeightOneSpectrum (𝓞 M))])
    rw [hcardM] at hc
    have h2 : 2 ≤ Nat.card 𝓀[HeightOneSpectrum.adicCompletion K v] := by
      rw [hK, hnormK]
      exact hge
    exact (Nat.pow_right_injective h2 hc).symm
  · refine ⟨FiniteField.frobeniusAlgEquivOfAlgebraic _ _, fun z => ?_⟩
    rw [FiniteField.frobeniusAlgEquivOfAlgebraic_apply, Nat.card_eq_fintype_card]
end

section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.finSec :
    FinSec := by
  intro H U V _ _ _ _ _ _ ρ σ f hf hsurj
  haveI := Fintype.ofFinite H
  obtain ⟨s₀, hs₀⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hsurj)
  have hs₀' : ∀ y, f (s₀ y) = y := fun y => LinearMap.congr_fun hs₀ y
  have hc : (Fintype.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hρ : ∀ (a b : H) (x : U), ρ (a * b) x = ρ a (ρ b x) := fun a b x => by
    rw [map_mul]; rfl
  have hσ : ∀ (a b : H) (x : V), σ (a * b) x = σ a (σ b x) := fun a b x => by
    rw [map_mul]; rfl
  have hσ1 : ∀ x : V, σ 1 x = x := fun x => by
    rw [map_one]; rfl
  refine ⟨(Fintype.card H : ℂ)⁻¹ • ∑ g : H, (ρ g) ∘ₗ s₀ ∘ₗ (σ g⁻¹), ?_, ?_⟩
  · intro h x

    simp only [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply, map_smul, map_sum]
    congr 1
    refine Fintype.sum_equiv (Equiv.mulLeft h⁻¹) _ _ fun g => ?_
    simp only [Equiv.coe_mulLeft, mul_inv_rev, inv_inv]
    rw [← hρ, mul_inv_cancel_left, hσ]
  · intro x

    simp only [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply, map_smul, map_sum]
    have : ∀ g : H, f (ρ g (s₀ (σ g⁻¹ x))) = x := fun g => by
      rw [hf, hs₀', ← hσ, mul_inv_cancel, hσ1]
    simp only [this, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]
end

section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.liftsFix :
    LiftsFix := by
  intro E Ω _ _ _ n X Y h x
  induction h with
  | refl => exact ⟨x, rfl⟩
  | @tail B C _ hs ih =>
    obtain ⟨y, hy⟩ := ih
    obtain ⟨i₁, i₂, -⟩ := hs
    refine ⟨algebraMap B.K C.K y, ?_⟩
    rw [← hy]
    exact (IsScalarTower.algebraMap_apply B.K C.K Ω y).symm
end

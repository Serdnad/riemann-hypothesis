module

import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle015
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.LocTower
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.Bundle003
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle581
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle119
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.IsAdmissibleIntegralBasisChangeOne
import GroundTheory.PAdicHodge.Bundle004
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle058
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.IntegOfMem
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.IsGrRefl
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
open GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh
universe u

private theorem sp_sub (Ω : Type) [Field Ω] : Subsingleton (UpperTheory.Gal.G3.sp Ω) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem isAdmissible_flagPair_of_unitriangular_left_automorphism {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {m j : X.ι} {k h : G}
    (hk : k ∈ X.K j) (hh : X.admitted m j h) : X.admitted m j (k * h) := by
  refine ⟨X.Δ.mul_mem (X.K_le j k hk) hh.1, fun u hu => ?_⟩
  have h3 := (X.K j).mul_mem ((X.K j).mul_mem hk (hh.2 u hu)) ((X.K j).inv_mem hk)
  have e : k * h * u * (k * h)⁻¹ = k * (h * u * h⁻¹) * k⁻¹ := by group
  rw [e]
  exact h3

private theorem pl_left {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {F : Type} [Field F] (T : Th.{u} B F)
    {m j : X.ι} {k h : G} (hk : k ∈ X.K j) (hh : X.admitted m j h) : X.pl T m j (k * h) = X.pl T m j h := by
  have a := isAdmissible_flagPair_of_unitriangular_left_automorphism X hk hh
  have e : X.tr m j (k * h) a.1 a.2 = X.tr m j h hh.1 hh.2 := by
    rw [← X.tr_mul m j j h k hh.1 hh.2 (X.K_le j k hk)
      (fun u hu => (X.K j).mul_mem ((X.K j).mul_mem hk hu) ((X.K j).inv_mem hk)) a.1 a.2,
      X.tr_self j k _ _ hk, Category.comp_id]
  unfold Tower.pl
  rw [dite_eq_left a, dite_eq_left hh]
  simp only [e]
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open UpperTheory.Gal.Int.Geo

namespace UpperTheory.Gal.G3

theorem jGenIso : GenIso := by
  intro O O' k K _ _ _ _ _ _ φ τ h X p
  have hg : gen O' K ≫ Spec.map (CommRingCat.ofHom φ) =
      Spec.map (CommRingCat.ofHom τ) ≫ gen O k := by
    simp only [gen, ← Spec.map_comp]
    congr 1
    ext x
    simpa using h x
  refine ⟨pullbackLeftPullbackSndIso p (Spec.map (CommRingCat.ofHom φ)) (gen O' K) ≪≫
    pullback.congrHom rfl hg ≪≫
    (pullbackLeftPullbackSndIso p (gen O k) (Spec.map (CommRingCat.ofHom τ))).symm, ?_, ?_⟩
  · simp only [Iso.trans_hom, Iso.symm_hom, pullback.congrHom_hom, Category.assoc,
      pullbackLeftPullbackSndIso_inv_snd_snd]
    rw [pullback.lift_snd, Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]
  · simp only [Iso.trans_hom, Iso.symm_hom, pullback.congrHom_hom, Category.assoc,
      pullbackLeftPullbackSndIso_inv_fst]
    rw [pullback.lift_fst, Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]

end UpperTheory.Gal.G3

end
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo PositivityTheory.AutomorphicGaloisHodgeTate.G8
open Formalism.ConjugateSelfDual (Qbar)
universe u v

private theorem intertwine_of_restrict {K V₁ V₀ G : Type*} [Field K] [AddCommGroup V₁] [Module K V₁]
    [AddCommGroup V₀] [Module K V₀] (f : V₁ →ₗ[K] V₀) (hf : Function.Injective f) {d₁ d₀ : ℕ}
    (W₁ : Submodule K V₁) (W₀ : Submodule K V₀) (b₁ : Module.Basis (Fin d₁) K W₁)
    (b₀ : Module.Basis (Fin d₀) K W₀) (hW : ∀ x ∈ W₁, f x ∈ W₀)
    (g₁ : G → V₁ →ₗ[K] V₁) (g₀ : G → V₀ →ₗ[K] V₀) (hc : ∀ σ x, g₀ σ (f x) = f (g₁ σ x))
    (ρ₁ : G → Matrix (Fin d₁) (Fin d₁) K) (ρ₀ : G → Matrix (Fin d₀) (Fin d₀) K)
    (h₁ : ∀ σ j, g₁ σ (b₁ j).1 = ∑ i, ρ₁ σ i j • (b₁ i).1)
    (h₀ : ∀ σ j, g₀ σ (b₀ j).1 = ∑ i, ρ₀ σ i j • (b₀ i).1) :
    ∃ A : Matrix (Fin d₀) (Fin d₁) K, Function.Injective A.mulVec ∧ ∀ σ, ρ₀ σ * A = A * ρ₁ σ := by
  let f' : W₁ →ₗ[K] W₀ := f.restrict hW
  have hf' : Function.Injective f' := fun x y h =>
    Subtype.ext (hf (congrArg Subtype.val h))
  let A := LinearMap.toMatrix b₁ b₀ f'
  have hA : ∀ j, f (b₁ j).1 = ∑ i, A i j • (b₀ i).1 := by
    intro j
    have e2 := congrArg W₀.subtype (b₀.sum_repr (f' (b₁ j)))

    rw [map_sum] at e2
    simp only [map_smul, Submodule.subtype_apply] at e2
    simp only [A, LinearMap.toMatrix_apply]
    exact e2.symm
  refine ⟨A, ?_, fun σ => ?_⟩
  · intro v w h
    have key : ∀ u : Fin d₁ → K, A.mulVec u = b₀.repr (f' (b₁.equivFun.symm u)) := by
      intro u
      have hu : ⇑(b₁.repr (b₁.equivFun.symm u)) = u := by
        rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
      have := LinearMap.toMatrix_mulVec_repr b₁ b₀ f' (b₁.equivFun.symm u)
      rw [hu] at this
      exact this
    rw [key, key] at h
    exact b₁.equivFun.symm.injective (hf' (b₀.repr.injective (Finsupp.ext fun i => congrFun h i)))
  · have hli : LinearIndependent K (fun i => (b₀ i).1) :=
      b₀.linearIndependent.map' W₀.subtype (Submodule.ker_subtype _)
    ext i j
    have e₁ : g₀ σ (f (b₁ j).1) = ∑ i, (ρ₀ σ * A) i j • (b₀ i).1 := by

      rw [hA, map_sum]
      simp only [map_smul, h₀, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]
    have e₂ : f (g₁ σ (b₁ j).1) = ∑ i, (A * ρ₁ σ) i j • (b₀ i).1 := by

      rw [h₁, map_sum]
      simp only [map_smul, hA, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]
    have e₃ : ∑ i, ((ρ₀ σ * A) i j - (A * ρ₁ σ) i j) • (b₀ i).1 = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [← e₁, ← e₂, hc, sub_self]
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.1 hli _ e₃ i)

private theorem galMap_bcMap {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {X Y : Scheme.{0}}
    {p : X ⟶ sp k} {q : Y ⟶ sp k} (f : Y ⟶ X) (h : f ≫ p = q) (σ : Ω ≃ₐ[k] Ω) :
    galMap Ω q σ ≫ bcMap (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) f h =
      bcMap (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) f h ≫ galMap Ω p σ := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, bcMap_fst, galMap_fst, bcMap_fst, galMap_fst_assoc]
  · rw [Category.assoc, Category.assoc, bcMap_snd, galMap_snd, galMap_snd, reassoc_of% bcMap_snd]

theorem UpperTheory.Gal.G3.jLowPiece :
    HopLies → PieceLe → PositivityTheory.AutomorphicGaloisHodgeTate.G8.LowPiece := by
  intro hL hP E Ω _ _ _ _ _ l _ H θ O _ _ C D hN hO d₁ d₀ ρ₁ ρ₀ ⟨b₁, h₁⟩ ⟨b₀, h₀⟩
  have hl : (l : E) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  obtain ⟨hinj, -⟩ := hP l hl C hO Ω
  have hop' := fun g => hL l hl C D hN Ω g
  let P : Htot l (sch.obj ((low D).geomZ Ω)) →ₗ[ℚ_[l]] Htot l (sch.obj (H.geomZ Ω)) :=
    (etG l E Ω).pull (piK C) (piK_snd C)
  have hop'' : ∀ g, hop l H Ω g ∘ₗ P = (D.m g : ℚ_[l]) • (P ∘ₗ hop l (low D) Ω g) := hop'
  have hinj' : Function.Injective (P.baseChange (Qbar l)) := hinj
  have hW : ∀ x ∈ piece l (low D) Ω (Qbar l) (fun g => θ g / D.m g),
      P.baseChange (Qbar l) x ∈ piece l H Ω (Qbar l) θ := by
    intro x hx
    simp only [piece, Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at hx ⊢
    intro g
    have hm : ((D.m g : ℕ) : Qbar l) ≠ 0 := Nat.cast_ne_zero.mpr (D.lies g).1.ne'
    have e : (hop l H Ω g).baseChange (Qbar l) (P.baseChange (Qbar l) x) =
        ((hop l H Ω g ∘ₗ P).baseChange (Qbar l)) x := by
      rw [LinearMap.baseChange_comp]; rfl
    rw [e, hop'', LinearMap.baseChange_smul, LinearMap.smul_apply, LinearMap.baseChange_comp,
      LinearMap.comp_apply, hx g, map_smul, ← algebraMap_smul (Qbar l) (D.m g : ℚ_[l]), map_natCast,
      smul_smul, mul_div_cancel₀ _ hm]
  have hc : ∀ (σ : Ω ≃ₐ[E] Ω) x, galV l H Ω (Qbar l) σ (P.baseChange (Qbar l) x) =
      P.baseChange (Qbar l) (galV l (low D) Ω (Qbar l) σ x) := by
    intro σ x
    have e : galTot l Ω H.q σ ∘ₗ P = P ∘ₗ galTot l Ω (low D).q σ := by
      have e' := congrArg (fun u => pullTot l (sch.map u))
        (galMap_bcMap (Ω := Ω) (piK C) (piK_snd C) σ)
      simp only [Functor.map_comp, pullTot_comp] at e'
      exact e'
    have e2 := congrArg (fun u => LinearMap.baseChange (Qbar l) u x) e
    simp only [LinearMap.baseChange_comp] at e2
    exact e2
  exact intertwine_of_restrict _ hinj' _ _ b₁ b₀ hW (galV l (low D) Ω (Qbar l)) (galV l H Ω (Qbar l)) hc
    (fun σ => (ρ₁ σ).val) (fun σ => (ρ₀ σ).val) h₁ h₀
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
universe u v

theorem UpperTheory.Gal.G3.jModBc :
    UpperTheory.Gal.Seam.GoodOf → ModBc := by
  intro hG l _ K O _ _ φ Y W p d hs hp c _ _
  haveI : SmoothOfRelativeDimension d p := hs
  haveI : SmoothOfRelativeDimension 0 c := (Etale.iff_smoothOfRelativeDimension_zero c).1 inferInstance
  have hcs : SmoothOfRelativeDimension d (c ≫ p) := by
    have h : SmoothOfRelativeDimension (0 + d) (c ≫ p) := inferInstance
    rwa [Nat.zero_add] at h
  have hqs : SmoothOfRelativeDimension d (pullback.snd (c ≫ p) (Spec.map (CommRingCat.ofHom φ))) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hcs
  have hcq : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver (c ≫ p) :=
    GlobalTheory.isQProjOver_comp_of_isFinite_general c (GlobalTheory.SchemeWords.isQProjOver_of_isProjOver hp)
  haveI : IsProper p := GlobalTheory.SchemeWords.isProper_of_isProjOver hp
  have hcp : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver (c ≫ p) :=
    GlobalTheory.UPel.isProjOver_of_isQProjOver_of_isProper O W (c ≫ p) hcq inferInstance
  have hqp : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver (pullback.snd (c ≫ p) (Spec.map (CommRingCat.ofHom φ))) :=
    GlobalTheory.ProjSpace.isProjOver_pullback_snd φ hcp
  haveI : FiniteDimensional ℚ_[l] K.1 := K.2
  have hsm : Smooth (pullback.snd (c ≫ p) (Spec.map (CommRingCat.ofHom φ))) :=
    SmoothOfRelativeDimension.smooth d _
  exact ⟨⟨hG l K.1 ⟨_, _⟩ hsm hqp, hsm⟩, hqs⟩
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
open NumberField IsDedekindDomain UpperTheory.Gal.Int.Geo PositivityTheory.AutomorphicGaloisHodgeTate.G8
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal
universe u v

private theorem ext2 {X B k K T : Scheme.{0}} {p : X ⟶ B} {g₁ : k ⟶ B} {g₂ : K ⟶ k}
    (a b : T ⟶ pullback (pullback.snd p g₁) g₂)
    (h1 : a ≫ pullback.snd _ _ = b ≫ pullback.snd _ _)
    (h2 : a ≫ pullback.fst _ _ ≫ pullback.fst _ _ = b ≫ pullback.fst _ _ ≫ pullback.fst _ _) : a = b := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simpa only [Category.assoc] using h2
    · simp only [Category.assoc, pullback.condition]
      rw [reassoc_of% h1]
  · exact h1

private theorem bcComp {B B' X Y Z : Scheme.{0}} (g : B ⟶ B') {p : X ⟶ B'} {q : Y ⟶ B'} {r : Z ⟶ B'}
    (f₁ : Z ⟶ Y) (f₂ : Y ⟶ X) (h₁ : f₁ ≫ q = r) (h₂ : f₂ ≫ p = q) (h : (f₁ ≫ f₂) ≫ p = r) :
    bcMap g (f₁ ≫ f₂) h = bcMap g f₁ h₁ ≫ bcMap g f₂ h₂ := by
  apply pullback.hom_ext
  · simp only [Category.assoc, bcMap_fst]
    rw [← Category.assoc (bcMap g f₁ h₁), bcMap_fst, Category.assoc]
  · simp only [Category.assoc, bcMap_snd]

private theorem bcCongr {B B' X Y : Scheme.{0}} (g : B ⟶ B') {p : X ⟶ B'} {q : Y ⟶ B'} {f f' : Y ⟶ X}
    (e : f = f') (h : f ≫ p = q) (h' : f' ≫ p = q) : bcMap g f h = bcMap g f' h' := by
  subst e; rfl

private theorem square {B B' k K X Y : Scheme.{0}} (gφ : B' ⟶ B) (g₁ : k ⟶ B) (g₂ : K ⟶ k) (gO : K ⟶ B')
    {p : X ⟶ B} {q : Y ⟶ B} (u : Y ⟶ X) (h : u ≫ p = q)
    (eX : pullback (pullback.snd p gφ) gO ⟶ pullback (pullback.snd p g₁) g₂)
    (eY : pullback (pullback.snd q gφ) gO ⟶ pullback (pullback.snd q g₁) g₂)
    (hX1 : eX ≫ pullback.snd _ _ = pullback.snd _ _)
    (hX2 : eX ≫ pullback.fst _ _ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _)
    (hY1 : eY ≫ pullback.snd _ _ = pullback.snd _ _)
    (hY2 : eY ≫ pullback.fst _ _ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _) :
    bcMap gO (bcMap gφ u h) (bcMap_snd _ _ _) ≫ eX = eY ≫ bcMap g₂ (bcMap g₁ u h) (bcMap_snd _ _ _) := by
  apply ext2
  · simp only [Category.assoc, hX1, hY1, bcMap_snd]
  · simp only [Category.assoc, hX2, reassoc_of% hY2, bcMap_fst, reassoc_of% bcMap_fst]

private theorem modP (hM : ModBc) (l : ℕ) [Fact l.Prime] (K : FinExt l) {O : Type} [CommRing O] [IsNoetherianRing O]
    (φ : O →+* ↥(CrystallineSemistableComparison.OK l K.1)) {Y : Scheme.{0}} (p : Y ⟶ sp O) (d : ℕ)
    (hs : SmoothOfRelativeDimension d p) (hp : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver p) :
    (⟨_, pullback.snd p (Spec.map (CommRingCat.ofHom φ))⟩ : CrystallineSemistableComparison.Model l K.1).Sm ∧
      SmoothOfRelativeDimension d (pullback.snd p (Spec.map (CommRingCat.ofHom φ))) := by
  have h : (⟨_, pullback.snd (𝟙 Y ≫ p) (Spec.map (CommRingCat.ofHom φ))⟩ : CrystallineSemistableComparison.Model l K.1).Sm ∧
      SmoothOfRelativeDimension d (pullback.snd (𝟙 Y ≫ p) (Spec.map (CommRingCat.ofHom φ))) :=
    hM l K φ p d hs hp (𝟙 Y)
  rw [Category.id_comp] at h
  exact h

private theorem galPart (hSp : BcSplits) (hGal : BcGal) {B k K Y T W₀ : Scheme.{0}} (p : Y ⟶ B) (g₁ : k ⟶ B) (g₂ : K ⟶ k)
    (s : T ⟶ Y) [IsFinite s] [Etale s] (c₀ : W₀ ⟶ Y) (G : Type) [Group G] [Finite G] (a₀ : G → (W₀ ⟶ W₀)) (n : ℕ)
    (σ₀ : Fin n → (W₀ ⟶ T)) (hG : IsGalois c₀ G a₀) (hS : Splits s c₀ σ₀) :
    ∃ (ha : ∀ x, a₀ x ≫ c₀ ≫ p = c₀ ≫ p) (hσ : ∀ j, σ₀ j ≫ s ≫ p = c₀ ≫ p)
      (hσ₁ : ∀ j, bcMap g₁ (σ₀ j) (hσ j) ≫ bcMap g₁ s rfl ≫ pullback.snd p g₁ = pullback.snd (c₀ ≫ p) g₁),
      IsGalois (bcMap g₂ (bcMap g₁ c₀ rfl) (bcMap_snd _ _ _)) G
        (fun x => bcMap g₂ (bcMap g₁ (a₀ x) (ha x)) (bcMap_snd _ _ _)) ∧
      Splits (bcMap g₂ (bcMap g₁ s rfl) rfl) (bcMap g₂ (bcMap g₁ c₀ rfl) (bcMap_snd _ _ _))
        (fun j => bcMap g₂ (bcMap g₁ (σ₀ j) (hσ j)) (hσ₁ j)) := by
  have hac := hG.2.2.2.2.2.1
  have hsc := hS.1
  have ha : ∀ x, a₀ x ≫ c₀ ≫ p = c₀ ≫ p := fun x => by rw [← Category.assoc, hac x]
  have hσ : ∀ j, σ₀ j ≫ s ≫ p = c₀ ≫ p := fun j => by rw [← Category.assoc, hsc j]
  have hσ₁ : ∀ j, bcMap g₁ (σ₀ j) (hσ j) ≫ bcMap g₁ s rfl ≫ pullback.snd p g₁ =
      pullback.snd (c₀ ≫ p) g₁ := fun j => by simp only [bcMap_snd]
  refine ⟨ha, hσ, hσ₁, ?_, ?_⟩
  · have hG1 := hGal g₁ p (c₀ ≫ p) c₀ rfl G a₀ ha hG
    exact hGal g₂ (pullback.snd p g₁) (pullback.snd (c₀ ≫ p) g₁) (bcMap g₁ c₀ rfl) (bcMap_snd _ _ _) G _
      (fun x => bcMap_snd _ _ _) hG1
  · obtain ⟨hF, hE, hsp⟩ := hSp g₁ p (s ≫ p) (c₀ ≫ p) s rfl c₀ rfl (Fin n) σ₀ hσ
    haveI := hF
    haveI := hE
    exact (hSp g₂ (pullback.snd p g₁) _ (pullback.snd (c₀ ≫ p) g₁) (bcMap g₁ s rfl) rfl (bcMap g₁ c₀ rfl)
      (bcMap_snd _ _ _) (Fin n) _ hσ₁).2.2 (hsp hS)

private theorem compPart {B k K Y T W₀ : Scheme.{0}} (p : Y ⟶ B) (g₁ : k ⟶ B) (g₂ : K ⟶ k) (s t : T ⟶ Y)
    (ht : t ≫ p = s ≫ p) (c₀ : W₀ ⟶ Y) (σ : W₀ ⟶ T) (hσ : σ ≫ s ≫ p = c₀ ≫ p) (hu : (σ ≫ t) ≫ p = c₀ ≫ p)
    (hσ₁ : bcMap g₁ σ hσ ≫ bcMap g₁ s rfl ≫ pullback.snd p g₁ = pullback.snd (c₀ ≫ p) g₁)
    (ht' : bcMap g₁ t ht ≫ pullback.snd p g₁ = bcMap g₁ s rfl ≫ pullback.snd p g₁) :
    bcMap g₂ (bcMap g₁ (σ ≫ t) hu) (bcMap_snd _ _ _) = bcMap g₂ (bcMap g₁ σ hσ) hσ₁ ≫ bcMap g₂ (bcMap g₁ t ht) ht' := by
  have h' : (bcMap g₁ σ hσ ≫ bcMap g₁ t ht) ≫ pullback.snd p g₁ = pullback.snd (c₀ ≫ p) g₁ := by
    simp only [Category.assoc, ht', hσ₁]
  exact (bcCongr g₂ (bcComp g₁ σ t hσ ht hu) _ h').trans (bcComp g₂ _ _ hσ₁ ht' h')


theorem UpperTheory.Gal.G3.jLowCov :
    GalClosD → BcSplits → BcGal → GenIso → ModBc → LowCov := by
  intro hGC hSp hGal hGI hM E _ _ l _ H θ w C D K τK hτ
  let φ : Ow w →+* CrystallineSemistableComparison.OK l K.1 :=
    RingHom.codRestrict (τK.comp (HeightOneSpectrum.valuation E w).valuationSubring.subtype) _
      (fun x => GroundTheory.PAdicHodge.mem_normInteger.mpr (hτ x))
  have hφ : ∀ x : Ow w, algebraMap (CrystallineSemistableComparison.OK l K.1) K.1 (φ x) = τK (algebraMap (Ow w) E x) := fun x => rfl
  obtain ⟨d₀, hd₀⟩ := C.dim
  obtain ⟨eZ, hZ1, hZ2⟩ := hGI φ τK hφ C.p
  have hMZ := modP hM l K φ C.p d₀ hd₀ C.proj
  refine ⟨⟨_, pullback.snd C.p (Spec.map (CommRingCat.ofHom φ))⟩, eZ,
    ⟨hMZ.1, ⟨d₀, hMZ.2⟩, eZ, hZ1⟩, hZ1, fun g => ?_⟩
  have hfet := D.fet g
  haveI := hfet.1
  haveI := hfet.2.1
  obtain ⟨W₀, c₀, G, _, _, a₀, σ₀, hG, hS⟩ := hGC (D.s g) (D.d g) (D.fet g)
  obtain ⟨ha, hσ, hσ₁, hGal', hSpl⟩ := galPart hSp hGal C.p (gen (Ow w) E)
    (Spec.map (CommRingCat.ofHom τK)) (D.s g) c₀ G a₀ (D.d g) σ₀ hG hS
  haveI := hG.1
  haveI := hG.2.1
  have hMW := hM l K φ C.p d₀ hd₀ C.proj c₀
  obtain ⟨eW, hW1, hW2⟩ := hGI φ τK hφ (c₀ ≫ C.p)
  have hu : ∀ i, (σ₀ i ≫ D.t g) ≫ C.p = c₀ ≫ C.p := fun i => by
    rw [Category.assoc, D.comm g, ← Category.assoc, hS.1 i]
  have ht' : bcMap (gen (Ow w) E) (D.t g) (D.comm g) ≫ pullback.snd C.p (gen (Ow w) E) =
      bcMap (gen (Ow w) E) (D.s g) rfl ≫ pullback.snd C.p (gen (Ow w) E) := by
    simp only [bcMap_snd]
  refine ⟨_, bcMap (Spec.map (CommRingCat.ofHom τK)) (bcMap (gen (Ow w) E) c₀ rfl) (bcMap_snd _ _ _),
    G, inferInstance, inferInstance, _, Fin (D.d g), inferInstance,
    fun i => bcMap (Spec.map (CommRingCat.ofHom τK)) (bcMap (gen (Ow w) E) (σ₀ i) (hσ i)) (hσ₁ i), hGal', ?_,
    ⟨_, pullback.snd (c₀ ≫ C.p) (Spec.map (CommRingCat.ofHom φ))⟩, eW,
    ⟨hMW.1, ⟨d₀, hMW.2⟩, eW, ?_⟩,
    ⟨bcMap (Spec.map (CommRingCat.ofHom φ)) c₀ rfl, bcMap_snd _ _ _, ?_⟩,
    fun i => ⟨bcMap (Spec.map (CommRingCat.ofHom φ)) (σ₀ i ≫ D.t g) (hu i), bcMap_snd _ _ _, ?_⟩⟩
  · exact hSpl
  · exact (congrArg (eW.hom ≫ ·) (bcMap_snd _ _ _)).trans hW1
  · exact square (Spec.map (CommRingCat.ofHom φ)) (gen (Ow w) E) (Spec.map (CommRingCat.ofHom τK))
      (gen (CrystallineSemistableComparison.OK l K.1) K.1) c₀ rfl eZ.hom eW.hom hZ1 hZ2 hW1 hW2
  · have hcp := compPart C.p (gen (Ow w) E) (Spec.map (CommRingCat.ofHom τK)) (D.s g) (D.t g) (D.comm g)
      c₀ (σ₀ i) (hσ i) (hu i) (hσ₁ i) ht'
    have hsq := square (Spec.map (CommRingCat.ofHom φ)) (gen (Ow w) E) (Spec.map (CommRingCat.ofHom τK))
      (gen (CrystallineSemistableComparison.OK l K.1) K.1) (σ₀ i ≫ D.t g) (hu i) eZ.hom eW.hom hZ1 hZ2 hW1 hW2
    exact hsq.trans (congrArg (eW.hom ≫ ·) hcp)
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV GlobalTheory.HodgeCoh UpperTheory.Gal.G3 UpperTheory.Gal.Int.Geo
universe u v

private theorem hodgeTrace_pull_congr {F : Type} [Field F] {Y Z : Scheme.{0}} (s t : Y ⟶ Z) [IsFinite s] [Etale s]
    (p : Z ⟶ sp F) {q q' : Y ⟶ sp F} (e : q = q') (h₁ : s ≫ p = q) (h₂ : t ≫ p = q) (h₁' : s ≫ p = q') (h₂' : t ≫ p = q')
    (a b : ℕ) (x : hodgeH p a b) :
    hodgeTrace h₁ a b (hodgePull h₂ a b x) = hodgeTrace h₁' a b (hodgePull h₂' a b x) := by
  subst e; rfl

theorem UpperTheory.Gal.G3.jHodgeOpBc :
    BcSplits → HodgeTr → TrBc.{0} → HodgeOpBc := by
  intro hBc hTr hTrBc k F _ _ φ H g _ _ a b
  letI : Algebra k F := φ.toAlgebra
  obtain ⟨hF, hE, -⟩ := hBc (Spec.map (CommRingCat.ofHom φ)) H.q (H.s g ≫ H.q) (H.s g ≫ H.q) (H.s g) rfl
    (H.s g) rfl PEmpty (fun e => e.elim) (fun e => e.elim)
  refine ⟨hF, hE, hodgeTrace (bcMap_snd _ (H.s g) rfl) a b, ?_, ?_⟩
  · exact hTrBc (hodge F a b) _ H.q (H.s g ≫ H.q) (H.s g) rfl _ (hTr F a b _ _ _ (bcMap_snd _ _ _))
  · intro hF' hE' x
    exact @hodgeTrace_pull_congr _ _ _ _ _ _ hF' hE' _ _ _
      (bcMap_snd (Spec.map (CommRingCat.ofHom φ)) (H.s g) rfl) _ _ _ _ a b x
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo PositivityTheory.AutomorphicGaloisHodgeTate.G8
universe u v

namespace UpperTheory.Gal.G3.HopfLiesOver

private theorem isTr_congr {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) {Z Y : Scheme.{0}} (p : Z ⟶ B)
    {q q' : Y ⟶ B} (e : q = q') (s : Y ⟶ Z) (tr : T.H q →ₗ[R] T.H p) (h : T.IsTr p q s tr) :
    ∃ tr' : T.H q' →ₗ[R] T.H p, T.IsTr p q' s tr' ∧
      ∀ {X : Scheme.{0}} (r : X ⟶ B) (t : Y ⟶ X) (a : t ≫ r = q) (a' : t ≫ r = q') (y : T.H r),
        tr' (T.pull t a' y) = tr (T.pull t a y) := by
  subst e
  exact ⟨tr, h, fun _ _ _ _ _ => rfl⟩

private theorem unit_l (l : ℕ) {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (hl : (l : k) ≠ 0) :
    IsUnit (l : Γ(sp Ω, ⊤)) := by
  have h1 : (l : Ω) ≠ 0 := by
    intro h0
    apply hl
    apply (algebraMap k Ω).injective
    simpa using h0
  have h2 := (h1.isUnit).map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom
  simpa using h2

private theorem low_fet (hF : FEtBasic) {k L O : Type} [Field k] [Field L] [CommRing O] [Algebra O k] {H : HTower k}
    {θ : H.Γ → L} {C : Cover H θ O} (D : LowData C) (g : H.Γ) : FEt ((low D).s g) (D.d g) := by
  have hp : IsPullback (pullback.fst (D.s g ≫ C.p) (gen O k)) ((low D).s g) (D.s g)
      (pullback.fst C.p (gen O k)) := by
    refine (IsPullback.of_right ?_ ?_ (IsPullback.of_hasPullback C.p (gen O k)).flip).flip
    · change IsPullback (bcMap (gen O k) (D.s g) rfl ≫ pullback.snd C.p (gen O k)) _ _ _
      rw [bcMap_snd]
      exact (IsPullback.of_hasPullback _ _).flip
    · exact bcMap_fst (gen O k) (D.s g) rfl
  exact hF.1 _ _ _ _ _ hp (D.fet g)

end UpperTheory.Gal.G3.HopfLiesOver

open UpperTheory.Gal.G3.HopfLiesOver in
theorem UpperTheory.Gal.G3.jHopLies :
    EtGood → BcGood.{1} → FEtBasic → HopSpec → LiesOp.{1} → HopLies := by
  intro hEt hBc hF hHop hLies l _ k L O _ _ _ _ hl H θ C D hN Ω _ _ g
  have hT : (etG l k Ω).Good := hBc _ _ (hEt l (sp Ω) (unit_l l hl))
  obtain ⟨d, hd⟩ := hN.2.2 g
  haveI : IsFinite (H.s g) := hd.1
  haveI : Etale (H.s g) := hd.2.1
  obtain ⟨trg, htrg⟩ := hT.tr H.q (H.s g ≫ H.q) (H.s g) rfl
  have hfet := low_fet hF D g
  obtain ⟨tr, htr⟩ := @Th.Good.tr _ _ _ _ hT _ _ (pullback.snd C.p (gen O k))
    (pullback.snd (D.s g ≫ C.p) (gen O k)) ((low D).s g) hfet.1 hfet.2.1
    (bcMap_snd (gen O k) (D.s g) rfl)
  have hq : pullback.snd (D.s g ≫ C.p) (gen O k) = (low D).s g ≫ (low D).q :=
    (bcMap_snd (gen O k) (D.s g) rfl).symm
  obtain ⟨tr', htr', hrel⟩ := isTr_congr (etG l k Ω) _ hq _ tr htr
  rw [(hHop l hl H Ω g d hd).2 trg htrg, (hHop l hl (low D) Ω g (D.d g) hfet).2 tr' htr']
  apply LinearMap.ext
  intro x
  have e := hLies C g (D.s g) (D.t g) (D.comm g) (D.m g) (D.d g) (D.lies g) hfet (etG l k Ω) hT tr trg
    htr htrg x
  have e2 := hrel _ _ (bcMap_snd (gen O k) (D.t g) (D.comm g))
    ((bcMap_snd (gen O k) (D.t g) (D.comm g)).trans hq) x
  exact e.trans (congrArg (fun y => (D.m g : ℚ_[l]) • (etG l k Ω).pull (piK C) (piK_snd C) y) e2.symm)
end

module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle014
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle015
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
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
import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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

@[expose] public section

section

noncomputable section

open TensorProduct Module

namespace UpperTheory.Gal.crystallineComparison

section Comm
variable {L M N : Type} [Field L] [AddCommGroup M] [Module L M] [AddCommGroup N] [Module L N]

private theorem pow_comm (φ : M →ₗ[L] N) (A : End L M) (A' : End L N) (h : ∀ y, φ (A y) = A' (φ y)) (n : ℕ) (y : M) :
    φ ((A ^ n) y) = (A' ^ n) (φ y) := by
  induction n generalizing y with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]

private theorem aeval_comm (φ : M →ₗ[L] N) (A : End L M) (A' : End L N) (h : ∀ y, φ (A y) = A' (φ y)) (Q : Polynomial L) (y : M) :
    φ (Polynomial.aeval A Q y) = Polynomial.aeval A' Q (φ y) :=
  _root_.UpperTheory.Reformulated.B.Qk66.aeval_comm φ A A' h Q y

end Comm

section
variable {F G B : Type} [Field F] [Group G] [AddCommGroup B] [Module F B] (σ : G → End F B) (ψ : End F B)
  {L : Type} [Field L] [Algebra F L] {V W : Type} [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V]
  [AddCommGroup W] [Module L W] [Module F W] [IsScalarTower F L W]

private def ext1 (B : Type) [AddCommGroup B] [Module F B] (f : V →ₗ[L] W) : V ⊗[F] B →ₗ[L] W ⊗[F] B :=
  AlgebraTensorModule.map f (LinearMap.id : B →ₗ[F] B)

private theorem scalar_extension_tmul (f : V →ₗ[L] W) (v : V) (b : B) : ext1 (F := F) B f (v ⊗ₜ b) = f v ⊗ₜ b := by
  simp [ext1]

private theorem typeCharacterExtension_mem_range_coefficientRing {ρ : Representation L G V} {ρ' : Representation L G W} {f : V →ₗ[L] W} (h : Inter ρ ρ' f)
    {x : V ⊗[F] B} (hx : x ∈ Dinv σ ρ) : ext1 B f x ∈ Dinv σ ρ' := by
  rw [mem_Dinv] at hx ⊢
  intro g
  have key : ∀ y : V ⊗[F] B, AlgebraTensorModule.map (ρ' g) (σ g) (ext1 B f y) =
      ext1 B f (AlgebraTensorModule.map (ρ g) (σ g) y) := by
    intro y
    induction y with
    | tmul v b => simp [scalar_extension_tmul, h g v]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  rw [key, hx]

private theorem scalar_extension_period_action (f : V →ₗ[L] W) (y : V ⊗[F] B) :
    ext1 B f (onPer ψ L V y) = onPer ψ L W (ext1 B f y) := by
  induction y with
  | tmul v b => simp [scalar_extension_tmul, onPer]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

private theorem scalar_extension_basis_coord {κ : Type} [DecidableEq κ] (b : Basis κ F B) (f : V →ₗ[L] W) (y : V ⊗[F] B) (k : κ) :
    TensorProduct.equivFinsuppOfBasisRight b (ext1 B f y) k = f (TensorProduct.equivFinsuppOfBasisRight b y k) := by
  induction y with
  | tmul v c =>
    rw [scalar_extension_tmul, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply,
      TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply, LinearMap.map_smul_of_tower]
  | add a c ha hc => simp only [map_add (f := _), Finsupp.add_apply, ha, hc]

end

theorem nilEmb_of : NilEmb := by
  intro F G B _ _ _ _ σ ψ L _ _ V _ _ _ _ ρ I _ W _ _ _ _ ρ' f hI hinj Q hQ
  classical
  cases nonempty_fintype I
  choose N hN using hQ
  refine ⟨∑ i, N i, fun x hx => ?_⟩
  set A := Polynomial.aeval (onPer ψ L V) Q with hA
  have hzero : ∀ i, ext1 B (f i) ((A ^ ∑ i, N i) x) = 0 := by
    intro i
    have hle : N i ≤ ∑ i, N i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [pow_comm (ext1 B (f i)) A (Polynomial.aeval (onPer ψ L (W i)) Q)
      (aeval_comm _ _ _ (scalar_extension_period_action ψ (f i)) Q), ← Nat.sub_add_cancel hle, pow_add, Module.End.mul_apply,
      hN i _ (typeCharacterExtension_mem_range_coefficientRing σ (hI i) hx), map_zero]
  apply (TensorProduct.equivFinsuppOfBasisRight (Basis.ofVectorSpace F B)).injective
  ext k
  rw [map_zero, Finsupp.zero_apply]
  refine hinj _ fun i => ?_
  rw [← scalar_extension_basis_coord, hzero i, map_zero, Finsupp.zero_apply]

end UpperTheory.Gal.crystallineComparison
end
end

section

open TensorProduct Module
open UpperTheory.Gal.crystallineComparison

private theorem pow_inter {L M N : Type} [Field L] [AddCommGroup M] [Module L M] [AddCommGroup N] [Module L N]
    (c : M →ₗ[L] N) (f : End L M) (g : End L N) (h : ∀ x, c (f x) = g (c x)) (n : ℕ) (x : M) :
    c ((f ^ n) x) = (g ^ n) (c x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]

private theorem aeval_inter {L M N : Type} [Field L] [AddCommGroup M] [Module L M] [AddCommGroup N] [Module L N]
    (c : M →ₗ[L] N) (f : End L M) (g : End L N) (h : ∀ x, c (f x) = g (c x)) (Q : Polynomial L) (x : M) :
    c (Polynomial.aeval f Q x) = Polynomial.aeval g Q (c x) :=
  _root_.UpperTheory.Reformulated.B.Qi58.aeval_inter c f g h Q x

theorem UpperTheory.Gal.crystallineComparison.nilSubq_of :
    AdmExact → NilEmb → NilSubq := by
  intro hA hE F G B _ _ _ _ σ ψ L _ _ e hB V W _ _ _ _ _ _ _ _ _ ρ ρ' hS hAdm
  obtain ⟨U, _, _, ρU, i, p, hi, hinj, hp, hsurj⟩ := hS
  letI : Module F U := Module.compHom U (algebraMap F L)
  haveI : IsScalarTower F L U := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : Module.Finite L U := Module.Finite.of_injective i hinj
  haveI : Module.Finite L W := Module.Finite.of_surjective p hsurj
  have hU : admitted σ e ρU := (hA F G B σ L e hB U V ρU ρ i hi).1 hinj hAdm
  obtain ⟨hW, hmap⟩ := (hA F G B σ L e hB U W ρU ρ' p hp).2 hsurj hU
  refine ⟨hW, fun Q hQ => ?_⟩
  obtain ⟨N, hN⟩ : NilD σ ψ ρU Q :=
    hE F G B σ ψ L U ρU Unit (fun _ => V) (fun _ => ρ) (fun _ => i) (fun _ => hi)
      (fun v h => hinj (by simpa using h ())) Q (fun _ => hQ)
  refine ⟨N, fun y hy => ?_⟩
  rw [← hmap] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  have h1 : ∀ z : U ⊗[F] B, AlgebraTensorModule.map p (LinearMap.id : B →ₗ[F] B) (onPer ψ L U z) =
      onPer ψ L W (AlgebraTensorModule.map p (LinearMap.id : B →ₗ[F] B) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul u b => simp [onPer]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  rw [← pow_inter _ _ _ (fun z => aeval_inter _ _ _ h1 Q z) N x, hN x hx, map_zero]
end

section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

private theorem ring_step {R S R' S' : Type} [CommRing R] [CommRing S] [CommRing R'] [CommRing S'] [Algebra R S]
    (a : R) (f : R →+* R') (g : S →+* S') (h : R' →+* S') (hc : h.comp f = g.comp (algebraMap R S))
    (hf : letI := f.toAlgebra; IsLocalization.Away a R')
    (hg : letI := g.toAlgebra; IsLocalization.Away (algebraMap R S a) S') (het : h.Etale) :
    Algebra.Etale (Localization.Away a) (Localization.Away a ⊗[R] S) := by
  classical
  letI : Algebra R R' := f.toAlgebra
  letI : Algebra S S' := g.toAlgebra
  letI : Algebra S (Localization.Away a ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  have hM : Algebra.algebraMapSubmonoid S (Submonoid.powers a) =
      Submonoid.powers (algebraMap R S a) := by
    simp [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
  haveI : IsLocalization (Algebra.algebraMapSubmonoid S (Submonoid.powers a)) S' := by
    rw [hM]; exact hg
  haveI : IsLocalization (Algebra.algebraMapSubmonoid S (Submonoid.powers a))
      (Localization.Away a ⊗[R] S) := IsLocalization.tensorRight _ (Submonoid.powers a)
  let e1 := IsLocalization.algEquiv (Submonoid.powers a) (Localization.Away a) R'
  let e2 := IsLocalization.algEquiv (Algebra.algebraMapSubmonoid S (Submonoid.powers a))
    (Localization.Away a ⊗[R] S) S'
  have key : algebraMap (Localization.Away a) (Localization.Away a ⊗[R] S) =
      e2.symm.toRingEquiv.toRingHom.comp (h.comp e1.toRingEquiv.toRingHom) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers a)
    ext r
    have h1 : e1 (algebraMap R (Localization.Away a) r) = f r := by
      rw [AlgEquiv.commutes]; rfl
    have h2 : h (f r) = g (algebraMap R S r) := by
      rw [← RingHom.comp_apply, hc, RingHom.comp_apply]
    have h3 : e2.symm (g (algebraMap R S r)) =
        algebraMap S (Localization.Away a ⊗[R] S) (algebraMap R S r) := by
      rw [← AlgEquiv.commutes e2.symm]; rfl
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      AlgEquiv.coe_ringEquiv]
    rw [h1, h2, h3]
    simp [Algebra.TensorProduct.algebraMap_apply, RingHom.algebraMap_toAlgebra,
      Algebra.TensorProduct.tmul_one_eq_one_tmul]
  rw [← RingHom.etale_algebraMap, key]
  exact RingHom.Etale.respectsIso.1 _ _ (RingHom.Etale.respectsIso.2 _ _ het)

private theorem appLE_step {Y Z : Scheme.{0}} (p : Z ⟶ Y) (D U' : Y.Opens) [Etale (p ∣_ D)] (hUD : U' ≤ D)
    (hU' : IsAffineOpen U') (W' : Z.Opens) (hW' : IsAffineOpen W') (e : W' ≤ p ⁻¹ᵁ U') :
    (p.appLE U' W' e).hom.Etale := by
  have hV : IsAffineOpen (D.ι ⁻¹ᵁ U') :=
    hU'.preimage_of_isOpenImmersion D.ι (by rw [Scheme.Opens.opensRange_ι]; exact hUD)
  have hW : IsAffineOpen ((p ⁻¹ᵁ D).ι ⁻¹ᵁ W') :=
    hW'.preimage_of_isOpenImmersion _
      (by rw [Scheme.Opens.opensRange_ι]; exact e.trans (fun x hx => hUD hx))
  have e' : (p ⁻¹ᵁ D).ι ⁻¹ᵁ W' ≤ (p ∣_ D) ⁻¹ᵁ (D.ι ⁻¹ᵁ U') := by
    intro x hx
    have h1 := e hx
    have h2 : D.ι ((p ∣_ D) x) = p ((p ⁻¹ᵁ D).ι x) := by
      rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
    change D.ι ((p ∣_ D) x) ∈ U'
    rw [h2]
    exact h1
  have H := HasRingHomProperty.appLE @Etale (p ∣_ D) ‹_›
    ⟨D.ι ⁻¹ᵁ U', hV⟩ ⟨(p ⁻¹ᵁ D).ι ⁻¹ᵁ W', hW⟩ e'
  rw [morphismRestrict_appLE] at H
  refine (Scheme.Hom.appLE_congr _ _ ?_ ?_ (fun f => f.hom.Etale)).mp H
  · rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hUD]
  · rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr (e.trans (fun x hx => hUD hx))]

theorem UpperTheory.Gal.crystallineComparison.etChart_of :
    EtChart := by
  unfold EtChart
  intro l Y T U hU
  letI := T.alg U
  haveI := T.fin
  haveI := T.et
  have hZU : IsAffineOpen (T.p ⁻¹ᵁ U) := hU.preimage T.p
  have e0 : T.Z.basicOpen ((T.p.app U).hom (l : Γ(Y, U))) ≤
      T.p ⁻¹ᵁ Y.basicOpen (l : Γ(Y, U)) := (Scheme.preimage_basicOpen T.p _).ge
  have hUD : Y.basicOpen (l : Γ(Y, U)) ≤ Y.basicOpen (l : Γ(Y, ⊤)) := by
    have hres : (Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom (l : Γ(Y, ⊤)) =
        (l : Γ(Y, U)) := map_natCast _ l
    rw [← hres, Scheme.basicOpen_res]
    exact inf_le_right
  have het := appLE_step T.p (Y.basicOpen (l : Γ(Y, ⊤))) (Y.basicOpen (l : Γ(Y, U))) hUD
    (hU.basicOpen _) _ (hZU.basicOpen _) e0
  refine ring_step (l : Γ(Y, U))
    (Y.presheaf.map (homOfLE (Y.basicOpen_le (l : Γ(Y, U)))).op).hom
    (T.Z.presheaf.map (homOfLE (T.Z.basicOpen_le ((T.p.app U).hom (l : Γ(Y, U))))).op).hom
    (T.p.appLE _ _ e0).hom ?_ (hU.isLocalization_basicOpen _) (hZU.isLocalization_basicOpen _) het
  rw [← CommRingCat.hom_comp]
  change _ = CommRingCat.Hom.hom (T.p.app U ≫ _)
  congr 1
  simp only [Scheme.Hom.map_appLE, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
end

section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.genChart_of :
    GenChart := by
  intro Y π U hU V _ _ f hmin
  set πU := Y.presheaf.map (homOfLE le_top).op π with hπU
  let P : PrimeSpectrum Γ(Y, U) := ⟨Ideal.comap f (IsLocalRing.maximalIdeal V), inferInstance⟩
  have hx : ptOf hU V f (IsLocalRing.closedPoint V) = hU.fromSpec P := rfl
  have hinU : ∀ q : PrimeSpectrum Γ(Y, U), hU.fromSpec q ∈ U := by
    intro q
    have : hU.fromSpec q ∈ Set.range hU.fromSpec := ⟨q, rfl⟩
    rw [hU.range_fromSpec] at this
    exact this
  have hmem : ∀ q : PrimeSpectrum Γ(Y, U), hU.fromSpec q ∈ Y.basicOpen π ↔ πU ∉ q.asIdeal := by
    intro q
    have h1 : q ∈ PrimeSpectrum.basicOpen πU ↔ hU.fromSpec q ∈ Y.basicOpen πU := by
      rw [← hU.fromSpec_preimage_basicOpen]
      rfl
    rw [← PrimeSpectrum.mem_basicOpen, h1, hπU, Scheme.basicOpen_res]
    exact ⟨fun h => ⟨hinU q, h⟩, fun h => h.2⟩
  rw [hx]
  refine ⟨?_, ?_⟩
  · rw [hmem, not_not]
    exact hmin.1.2 (Ideal.subset_span (Set.mem_singleton _))
  · intro x' hx' hsp
    have hx'U : x' ∈ U := hsp.mem_open U.isOpen (hinU P)
    obtain ⟨q, rfl⟩ : x' ∈ Set.range hU.fromSpec := by
      rw [hU.range_fromSpec]
      exact hx'U
    have hqp : q ⤳ P := hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff.mp hsp
    have hqp' : q.asIdeal ≤ P.asIdeal := (PrimeSpectrum.le_iff_specializes (R := Γ(Y, U)) q P).mpr hqp
    have hπq : πU ∈ q.asIdeal := by
      by_contra h
      exact hx' ((hmem q).mpr h)
    have hPq : P.asIdeal ≤ q.asIdeal :=
      hmin.2 ⟨q.2, Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hπq)⟩ hqp'
    congr 1
    exact PrimeSpectrum.ext (le_antisymm hqp' hPq)
end

section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.normInt_of :
    NormEx → SplitsBC → InjSplit → CoeffInt → LiftP → NormInt := by
  intro hNE hBC hIS hCI hLP l d R S _ _ _ h hcl ι _ s
  haveI hfin : Module.Finite R S := h.fin
  haveI het := h.et
  haveI : Module.Finite (Localization.Away (l : R)) (Localization.Away (l : R) ⊗[R] S) := inferInstance
  haveI : Algebra.FinitePresentation (Localization.Away (l : R)) (Localization.Away (l : R) ⊗[R] S) := inferInstance
  haveI : Module.FinitePresentation (Localization.Away (l : R)) (Localization.Away (l : R) ⊗[R] S) :=
    Module.FinitePresentation.of_finite_of_finitePresentation _ _
  haveI : Module.Flat (Localization.Away (l : R)) (Localization.Away (l : R) ⊗[R] S) := inferInstance
  haveI : Module.Projective (Localization.Away (l : R)) (Localization.Away (l : R) ⊗[R] S) :=
    Module.Flat.projective_of_finitePresentation
  obtain ⟨N', hN'⟩ := hNE (Localization.Away (l : R)) (Localization.Away (l : R) ⊗[R] S) ι (fun k => 1 ⊗ₜ s k)
  obtain ⟨T, _, _, m, z, hinj, hz⟩ := hIS l d R S h
  haveI : FaithfulSMul (Localization.Away (l : R)) T :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  letI : Algebra R T := ((algebraMap (Localization.Away (l : R)) T).comp (algebraMap R (Localization.Away (l : R)))).toAlgebra
  haveI : IsScalarTower R (Localization.Away (l : R)) T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hNz := hN' T (Fin m) z hz
  have hint : ∀ i k, IsIntegral R (z i (1 ⊗ₜ s k)) := by
    intro i k
    have hs : IsIntegral R (s k) := Algebra.IsIntegral.isIntegral (R := R) (s k)
    have := hs.map (((z i).restrictScalars R).comp
      (Algebra.TensorProduct.includeRight : S →ₐ[R] (Localization.Away (l : R) ⊗[R] S)))
    simpa using this
  have hco : ∀ (a : ℕ) (mm : ι →₀ ℕ), ∃ r, algebraMap R (Localization.Away (l : R)) r = AddMonoidAlgebra.coeff (N'.coeff a) mm := by
    intro a mm
    apply hcl
    have h1 := hCI R T ι (Fin m) (fun i k => z i (1 ⊗ₜ s k)) hint a mm
    rw [← hNz, Polynomial.coeff_map, MvPolynomial.coeff_map] at h1
    exact (isIntegral_algebraMap_iff ).1 h1
  obtain ⟨N, hN⟩ := hLP R (Localization.Away (l : R)) ι (algebraMap R (Localization.Away (l : R))) N' hco
  refine ⟨N, ?_⟩
  intro B _ _ hl I _ zB hzB
  letI : Algebra (Localization.Away (l : R)) B :=
    (IsLocalization.Away.lift (S := Localization.Away (l : R)) (l : R) (g := algebraMap R B) (by simpa using hl)).toAlgebra
  haveI : IsScalarTower R (Localization.Away (l : R)) B := IsScalarTower.of_algebraMap_eq fun r =>
    (IsLocalization.Away.lift_eq (S := Localization.Away (l : R)) (l : R) (g := algebraMap R B) (by simpa using hl) r).symm
  obtain ⟨z', hz', hzz⟩ := hBC R (Localization.Away (l : R)) S B I zB hzB
  have h2 := hN' B I z' hz'
  simp only [hzz] at h2
  rw [← h2, ← hN]
  have hc : (MvPolynomial.map (algebraMap (Localization.Away (l : R)) B)).comp
      (MvPolynomial.map (σ := ι) (algebraMap R (Localization.Away (l : R)))) = MvPolynomial.map (algebraMap R B) := by
    ext x
    · simp [← IsScalarTower.algebraMap_apply]
    · simp
  simp only [mapP, Polynomial.map_map, hc]
end

section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

private theorem exists_forall_algHom_pi_eq_apply_of_finite {K P : Type} [Field K] [Finite P] (ψ : (P → K) →ₐ[K] K) :
    ∃ p, ∀ x, ψ x = x p := by
  classical
  have hex : ∃ p, ψ (Pi.single p 1) ≠ 0 := by
    by_contra h
    push_neg at h
    have := Fintype.ofFinite P
    have h1 : (1 : P → K) = ∑ p, Pi.single p 1 := by
      simpa using (Finset.univ_sum_single (1 : P → K)).symm
    have h2 : ψ 1 = 0 := by

      rw [h1, map_sum]
      simp [h]
    simp at h2
  obtain ⟨p, hp⟩ := hex
  refine ⟨p, fun x => ?_⟩
  have hid : ψ (Pi.single p 1) = 1 := by
    have h2 : ψ (Pi.single p 1) * ψ (Pi.single p 1) = ψ (Pi.single p 1) := by
      rw [← map_mul]
      congr 1
      ext i
      by_cases h : i = p <;> simp [Pi.single_apply, h]
    exact (mul_left_inj' hp).1 (h2.trans (one_mul _).symm)
  have hx : x * Pi.single p 1 = algebraMap K (P → K) (x p) * Pi.single p 1 := by
    ext i
    by_cases h : i = p <;> simp [Pi.single_apply, h]
  have h3 := congrArg ψ hx
  rw [map_mul, map_mul, AlgHom.commutes, hid] at h3
  simpa using h3

theorem UpperTheory.Gal.crystallineComparison.splitsField_of :
    SplitsField := by
  intro R S K _ _ _ _ _ _ hE
  classical
  have hfin : Module.Finite K (K ⊗[R] S) := Algebra.FormallyUnramified.finite_of_free K (K ⊗[R] S)
  haveI : IsArtinianRing (K ⊗[R] S) := isArtinian_of_tower K inferInstance
  haveI : Finite (PrimeSpectrum (K ⊗[R] S)) := inferInstance
  let e := Algebra.FormallyEtale.equivPiOfIsSepClosed K (K ⊗[R] S)
  let F := splitMap (R := R) (S := S) (B := K) (I := S →ₐ[R] K) (fun z => z)
  let L : (S →ₐ[R] K) → ((K ⊗[R] S) →ₐ[K] K) := fun ψ => (Pi.evalAlgHom K (fun _ => K) ψ).comp F
  have hL : ∀ ψ x, L ψ x = F x ψ := fun _ _ => rfl
  have hLs : ∀ ψ (s : S), L ψ (1 ⊗ₜ s) = ψ s := by
    intro ψ s
    simp [L, F, splitMap]
  choose q hq using fun ψ => exists_forall_algHom_pi_eq_apply_of_finite ((L ψ).comp e.symm.toAlgHom)
  have hLe : ∀ ψ x, L ψ x = e x (q ψ) := by
    intro ψ x
    simpa using hq ψ (e x)
  have qinj : Function.Injective q := by
    intro ψ1 ψ2 h
    ext s
    rw [← hLs, ← hLs, hLe, hLe, h]
  have hsec : ∀ p, ∃ ψ, q ψ = p := by
    intro p
    let g : (K ⊗[R] S) →ₐ[K] K := (Pi.evalAlgHom K (fun _ => K) p).comp e.toAlgHom
    let ψ : S →ₐ[R] K := (g.restrictScalars R).comp Algebra.TensorProduct.includeRight
    have hg : L ψ = g := by
      apply Algebra.TensorProduct.ext
      · exact Subsingleton.elim _ _
      · ext s
        simp [hLs, ψ]
    refine ⟨ψ, ?_⟩
    have h1 := hLe ψ (e.symm (Pi.single p 1))
    rw [hg] at h1
    simp only [g, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgHom.coe_coe,
      AlgEquiv.apply_symm_apply, Pi.evalAlgHom_apply] at h1
    by_contra hne
    simp [Pi.single_apply, hne] at h1
  refine ⟨Finite.of_injective q qinj, ?_⟩
  show Function.Bijective F
  constructor
  · intro x y h
    apply e.injective
    funext p
    obtain ⟨ψ, rfl⟩ := hsec p
    rw [← hLe, ← hLe, hL, hL, h]
  · intro v
    refine ⟨e.symm (Function.extend q v 0), ?_⟩
    funext ψ
    rw [← hL, hLe, e.apply_symm_apply, qinj.extend_apply]
end

section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.etUnit_of :
    EtOfUnit := by
  intro l R S B _ _ _ _ _ h hl
  have hl' : IsUnit (algebraMap R B (l : R)) := by simpa using hl
  letI : Algebra (Localization.Away (l : R)) B :=
    (IsLocalization.Away.lift (S := Localization.Away (l : R)) (l : R) hl').toAlgebra
  haveI : IsScalarTower R (Localization.Away (l : R)) B :=
    IsScalarTower.of_algebraMap_eq fun r =>
      (IsLocalization.Away.lift_eq (S := Localization.Away (l : R)) (l : R) hl' r).symm
  exact Algebra.Etale.of_equiv
    (Algebra.TensorProduct.cancelBaseChange R (Localization.Away (l : R)) B B S)
end

module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.PicardGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle140
public import Mathlib.RingTheory.Henselian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle046
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle230
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle229
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle231
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
import Mathlib.RingTheory.Etale.Pi
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Localization.Free
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.Smooth.NoetherianDescent

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.PicLoc

theorem exists_away_mapAlgebra_eq_one : ∀ (A : Type) [CommRing A] (c : CommRing.Pic A) (p : Ideal A) [p.IsPrime], ∃ f ∉ p, CommRing.Pic.mapAlgebra A (Localization.Away f) c = 1 := by
  intro A _ c p _
  letI := @Module.addCommMonoidToAddCommGroup A
  haveI : Module.FinitePresentation A c := Module.finitePresentation_of_projective A c
  haveI : Module.Free (Localization.AtPrime p) (LocalizedModule p.primeCompl c) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨f, hf, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl c) (Localization.AtPrime p)
  refine ⟨f, hf, ?_⟩
  rw [CommRing.Pic.mapAlgebra_apply, CommRing.Pic.mk_eq_one_iff_free]
  exact Module.Free.of_equiv (LocalizedModule.equivTensorProduct (Submonoid.powers f) c)

theorem exists_etale_faithfullyFlat_mapAlgebra_eq_one : ∀ (A : Type) [CommRing A] (c : CommRing.Pic A), ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B) (_ : Algebra.Etale A B) (_ : Module.FaithfullyFlat A B), CommRing.Pic.mapAlgebra A B c = 1 := by
  intro A _ c
  classical
  let T : Set A := {f | CommRing.Pic.mapAlgebra A (Localization.Away f) c = 1}
  have hT : Ideal.span T = ⊤ := by
    by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨f, hf, hf1⟩ := exists_away_mapAlgebra_eq_one A c m
    exact hf (hle (Ideal.subset_span hf1))
  obtain ⟨s, hsT, hs⟩ := (Ideal.span_eq_top_iff_finite T).mp hT
  let R : s → Type := fun i => Localization.Away (i : A)
  haveI : ∀ i, Algebra.Etale A (R i) := fun i => Algebra.Etale.of_isLocalizationAway (i : A)
  have halg : ∀ i, (Pi.evalRingHom R i).comp (algebraMap A ((i : s) → R i)) = algebraMap A (R i) :=
    fun i => RingHom.ext fun _ => rfl
  refine ⟨(i : s) → R i, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · refine Module.FaithfullyFlat.of_comap_surjective fun p => ?_
    obtain ⟨i, hi⟩ : ∃ i : s, (i : A) ∉ p.asIdeal := by
      by_contra h
      push Not at h
      apply p.isPrime.ne_top
      rw [eq_top_iff, ← hs, Ideal.span_le]
      intro x hx
      exact h ⟨x, hx⟩
    have hp : p ∈ Set.range (PrimeSpectrum.comap (algebraMap A (R i))) := by
      rw [PrimeSpectrum.localization_away_comap_range (R i) (i : A)]
      exact hi
    obtain ⟨q, rfl⟩ := hp
    refine ⟨PrimeSpectrum.comap (Pi.evalRingHom R i) q, ?_⟩
    rw [← PrimeSpectrum.comap_comp_apply, halg]
  · apply GlobalTheory.PicPi.eq_one_of_forall
    intro i
    rw [← CommRing.Pic.mapRingHom_algebraMap, CommRing.Pic.mapRingHom_mapRingHom, halg,
      CommRing.Pic.mapRingHom_algebraMap]
    exact hsT i.2

end GlobalTheory.PicLoc
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtaleLiftQuot

open IsLocalRing TensorProduct

theorem ker_le_jacobson_of_factor {S T F : Type} [CommRing S] [CommRing T] [FunLike F S T]
    [RingHomClass F S T] (g : F)
    (h : ∀ n : Ideal S, n.IsMaximal → ∃ τ : T →+* S ⧸ n, ∀ x, τ (g x) = Ideal.Quotient.mk n x) :
    RingHom.ker g ≤ (⊥ : Ideal S).jacobson := by
  intro x hx
  refine GlobalTheory.mem_jacobson_bot_of_forall_isMaximal fun n hn ↦ ?_
  obtain ⟨τ, hτ⟩ := h n hn
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← hτ, RingHom.mem_ker.1 hx, map_zero]

def residueToQuot (R : Type) [CommRing R] [IsLocalRing R] {S : Type} [CommRing S] [Algebra R S]
    [Module.Finite R S] (n : Ideal S) [n.IsMaximal] : ResidueField R →ₐ[R] S ⧸ n :=
  Ideal.Quotient.liftₐ (maximalIdeal R) (Algebra.ofId R _) fun a ha ↦ by
    rw [← GlobalTheory.comap_eq_maximalIdeal_of_finite n] at ha
    exact Ideal.Quotient.eq_zero_iff_mem.2 ha

variable {R : Type} [CommRing R] [HenselianLocalRing R] (I : Ideal R)

abbrev algQuotResidue (hI : I ≤ maximalIdeal R) : Algebra (R ⧸ I) (ResidueField R) :=
  (Ideal.Quotient.factor hI : R ⧸ I →+* R ⧸ maximalIdeal R).toAlgebra

theorem exists_lift (hI : I ≤ maximalIdeal R) (E : Type) [CommRing E] [Algebra (R ⧸ I) E] [Module.Finite (R ⧸ I) E]
    [Algebra.Etale (R ⧸ I) E] :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B), Module.Finite R B ∧ Algebra.Etale R B ∧
      Nonempty ((B ⧸ I.map (algebraMap R B)) ≃ₐ[R ⧸ I] E) := by
  letI := algQuotResidue I hI
  have : IsScalarTower R (R ⧸ I) (ResidueField R) := .of_algebraMap_eq fun _ ↦ rfl
  have hsurj : Function.Surjective (algebraMap R (R ⧸ I)) := Ideal.Quotient.mk_surjective
  have hk : Function.Surjective (algebraMap (R ⧸ I) (ResidueField R)) := fun y ↦ by
    obtain ⟨x, rfl⟩ := residue_surjective y
    exact ⟨Ideal.Quotient.mk I x, rfl⟩
  letI : Algebra R E := ((algebraMap (R ⧸ I) E).comp (algebraMap R (R ⧸ I))).toAlgebra
  have : IsScalarTower R (R ⧸ I) E := .of_algebraMap_eq fun _ ↦ rfl
  have : Module.Finite R E := .trans (R ⧸ I) E
  obtain ⟨B, _, _, hBfin, hBet, ⟨e⟩⟩ :=
    GlobalTheory.exists_etale_lift_of_etale.{0, 0} R (ResidueField R ⊗[R ⧸ I] E)
  refine ⟨B, inferInstance, inferInstance, hBfin, hBet, ?_⟩
  have : IsScalarTower R (R ⧸ I) (ResidueField R ⊗[R ⧸ I] E) := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower R (R ⧸ I) (ResidueField R ⊗[R] B) := .of_algebraMap_eq fun _ ↦ rfl

  let πE : E →ₐ[R ⧸ I] ResidueField R ⊗[R ⧸ I] E := Algebra.TensorProduct.includeRight
  have hπE : Function.Surjective πE := Algebra.TensorProduct.includeRight_surjective _ hk
  have hkerE : RingHom.ker πE ≤ (⊥ : Ideal E).jacobson := by
    refine ker_le_jacobson_of_factor πE fun n hn ↦ ?_
    let σ := (residueToQuot R n).extendScalarsOfSurjective hsurj
    let τ := Algebra.TensorProduct.lift σ (Ideal.Quotient.mkₐ (R ⧸ I) n) fun _ _ ↦ .all _ _
    exact ⟨τ.toRingHom, fun x ↦ by simp [τ, πE]⟩

  let J := I.map (algebraMap R B)
  have hJ : ∀ (T : Type) [CommRing T] [Algebra R T] (g : B →ₐ[R] T),
      (∀ r ∈ I, algebraMap R T r = 0) → ∀ a ∈ J, g a = 0 := fun T _ _ g hT a ha ↦ by
    have : J ≤ RingHom.ker g := by
      rw [Ideal.map_le_iff_le_comap]
      intro r hr
      rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes]
      exact hT r hr
    exact this ha
  have hres : ∀ r ∈ I, algebraMap R (ResidueField R ⊗[R] B) r = 0 := fun r hr ↦ by
    have h0 : algebraMap R (ResidueField R) r = 0 := (residue_eq_zero_iff r).2 (hI hr)
    rw [IsScalarTower.algebraMap_apply R (ResidueField R), h0, map_zero]
  let πB₀ : B ⧸ J →ₐ[R] ResidueField R ⊗[R] B :=
    Ideal.Quotient.liftₐ J Algebra.TensorProduct.includeRight (hJ _ _ hres)
  let πB : B ⧸ J →ₐ[R ⧸ I] ResidueField R ⊗[R] B := πB₀.extendScalarsOfSurjective hsurj
  have hπB_mk : ∀ b : B, πB (Ideal.Quotient.mk J b) = 1 ⊗ₜ b := fun b ↦ rfl
  have hπB : Function.Surjective πB := fun y ↦ by
    obtain ⟨b, rfl⟩ := Algebra.TensorProduct.includeRight_surjective B residue_surjective y
    exact ⟨Ideal.Quotient.mk J b, rfl⟩
  have hkerB : RingHom.ker πB ≤ (⊥ : Ideal (B ⧸ J)).jacobson := by
    refine ker_le_jacobson_of_factor πB fun n hn ↦ ?_
    let τ := Algebra.TensorProduct.lift (residueToQuot R n)
      ((Ideal.Quotient.mkₐ R n).comp (Ideal.Quotient.mkₐ R J)) fun _ _ ↦ .all _ _
    refine ⟨τ.toRingHom, fun x ↦ ?_⟩
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hπB_mk]
    simp [τ]

  obtain ⟨φ, hφ⟩ := (GlobalTheory.bijective_algHom_comp_of_etale_of_henselian R (k := R) (A := B)
    (πE.restrictScalars R) hπE hkerE).2
    ((e.toAlgHom.restrictScalars R).comp Algebra.TensorProduct.includeRight)
  have hφb : ∀ b, πE (φ b) = e (1 ⊗ₜ b) := fun b ↦ congr($hφ b)

  obtain ⟨ψ, hψ⟩ := (GlobalTheory.bijective_algHom_comp_of_etale_of_henselian R (k := R ⧸ I) (A := E)
    πB hπB hkerB).2 ((e.symm.toAlgHom.restrictScalars (R ⧸ I)).comp πE)
  have hψx : ∀ x, πB (ψ x) = e.symm (πE x) := fun x ↦ congr($hψ x)
  have hEI : ∀ r ∈ I, algebraMap R E r = 0 := fun r hr ↦ by
    rw [IsScalarTower.algebraMap_apply R (R ⧸ I), Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.2 hr, map_zero]
  let φ' : B ⧸ J →ₐ[R ⧸ I] E := (Ideal.Quotient.liftₐ J φ (hJ _ _ hEI)).extendScalarsOfSurjective hsurj
  have hφ'_mk : ∀ b, φ' (Ideal.Quotient.mk J b) = φ b := fun b ↦ rfl
  have key : ∀ y, πE (φ' y) = e (πB y) := fun y ↦ by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [hφ'_mk, hφb, hπB_mk]
  have h1 : φ'.comp ψ = AlgHom.id (R ⧸ I) E := by
    refine (GlobalTheory.bijective_algHom_comp_of_etale_of_henselian R (k := R ⧸ I) (A := E)
      πE hπE hkerE).1 (AlgHom.ext fun x ↦ ?_)
    simp only [AlgHom.comp_apply, AlgHom.id_apply, key, hψx, AlgEquiv.apply_symm_apply]
  have h2 : ψ.comp φ' = AlgHom.id (R ⧸ I) (B ⧸ J) := by
    have H := (GlobalTheory.bijective_algHom_comp_of_etale_of_henselian R (k := R) (A := B)
      (πB.restrictScalars R) hπB hkerB).1
      (a₁ := (ψ.restrictScalars R).comp φ) (a₂ := Ideal.Quotient.mkₐ R J) (AlgHom.ext fun b ↦ by
        simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, Ideal.Quotient.mkₐ_eq_mk]
        rw [hψx, hφb, AlgEquiv.symm_apply_apply, hπB_mk])
    refine AlgHom.ext fun y ↦ ?_
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [AlgHom.comp_apply, AlgHom.id_apply, hφ'_mk]
    simpa using congr($H b)
  exact ⟨AlgEquiv.ofAlgHom φ' ψ h1 h2⟩

end GlobalTheory.EtaleLiftQuot

namespace GlobalTheory.EtaleLiftQuot

open IsLocalRing TensorProduct

theorem exists_finite_free_etale_lift : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R],
    IsAdicComplete (maximalIdeal R) R → ∀ f ∈ maximalIdeal R, ∀ (E : Type) [CommRing E]
    [Algebra (R ⧸ Ideal.span {f}) E] [Module.Finite (R ⧸ Ideal.span {f}) E]
    [Algebra.Etale (R ⧸ Ideal.span {f}) E], ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B),
      Module.Finite R B ∧ Module.Free R B ∧ Algebra.Etale R B ∧
        Nonempty ((B ⧸ (Ideal.span {f}).map (algebraMap R B)) ≃ₐ[R ⧸ Ideal.span {f}] E) := by
  intro R _ _ _ hc f hf E _ _ _ _
  have : HenselianRing R (maximalIdeal R) := @IsAdicComplete.henselianRing R _ _ hc
  have : HenselianLocalRing R := GlobalTheory.henselianLocalRing_of_henselianRing R
  obtain ⟨B, _, _, h₁, h₂, h₃⟩ :=
    exists_lift (Ideal.span {f}) ((Ideal.span_singleton_le_iff_mem _).2 hf) E
  exact ⟨B, inferInstance, inferInstance, h₁, Module.free_of_flat_of_isLocalRing, h₂, h₃⟩

end GlobalTheory.EtaleLiftQuot
end
end

section

open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory

theorem tensor_localization_atPrime_isDomain_of_isLocalRing_etale :
    ∀ (P R E : Type) [CommRing P] [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Algebra P R]
      [CommRing E] [Algebra P E] [Algebra.Etale P E] (Q : Ideal E) [Q.IsPrime],
      IsLocalRing (TensorProduct P R (Localization.AtPrime Q)) →
        IsDomain (TensorProduct P R (Localization.AtPrime Q)) := by
  intro P R E _ _ _ _ _ _ _ _ Q _ hloc
  letI : Algebra (R ⊗[P] E) (R ⊗[P] Localization.AtPrime Q) :=
    (Algebra.TensorProduct.map (AlgHom.id P R)
      (IsScalarTower.toAlgHom P E (Localization.AtPrime Q))).toAlgebra
  haveI : IsScalarTower R (R ⊗[P] E) (R ⊗[P] Localization.AtPrime Q) :=
    .of_algebraMap_eq <| by intro; simp [RingHom.algebraMap_toAlgebra]
  haveI hl := IsLocalization.tensorProduct_tensorProduct_right P R Q.primeCompl
    (Localization.AtPrime Q) (by ext; simp [RingHom.algebraMap_toAlgebra])
  let 𝔭 : Ideal (R ⊗[P] E) :=
    (maximalIdeal (R ⊗[P] Localization.AtPrime Q)).comap
      (algebraMap (R ⊗[P] E) (R ⊗[P] Localization.AtPrime Q))
  haveI : 𝔭.IsPrime := Ideal.comap_isPrime _ _
  have hle : Q.primeCompl.map (Algebra.TensorProduct.includeRight (R := P) (A := R)) ≤
      𝔭.primeCompl := by
    intro x hx
    have hu := IsLocalization.map_units (R ⊗[P] Localization.AtPrime Q)
      (⟨x, hx⟩ : Q.primeCompl.map (Algebra.TensorProduct.includeRight (R := P) (A := R)))
    intro h
    exact ((mem_maximalIdeal _).mp (Ideal.mem_comap.mp h)) hu
  haveI : IsLocalization 𝔭.primeCompl (R ⊗[P] Localization.AtPrime Q) :=
    IsLocalization.of_le _ _ hle (fun r hr => by
      by_contra hu
      exact hr (Ideal.mem_comap.mpr ((mem_maximalIdeal _).mpr hu)))
  obtain ⟨hd, -⟩ := etale_localization_atPrime_isDomain_isIntegrallyClosed R (R ⊗[P] E) 𝔭
  let e : Localization.AtPrime 𝔭 ≃ₐ[R ⊗[P] E] (R ⊗[P] Localization.AtPrime Q) :=
    IsLocalization.algEquiv 𝔭.primeCompl _ _
  exact e.symm.injective.isDomain _

end GlobalTheory
end

section

open IsLocalRing

namespace GlobalTheory

namespace IndEtaleNormal

open Polynomial

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
  {ι : Type} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]

lemma exists_mem_of_finset (Si : ι → Subalgebra R S) (hmono : Monotone Si)
    (hcov : ∀ s : S, ∃ i, s ∈ Si i) (T : Finset S) : ∃ i, ∀ t ∈ T, t ∈ Si i := by
  classical
  choose idx hidx using hcov
  obtain ⟨M, hM⟩ := Finset.exists_le (T.image idx)
  exact ⟨M, fun t ht => hmono (hM _ (Finset.mem_image_of_mem idx ht)) (hidx t)⟩

lemma isDomain [Nontrivial S] (Si : ι → Subalgebra R S) (hmono : Monotone Si)
    (hcov : ∀ s : S, ∃ i, s ∈ Si i) (hdom : ∀ i, IsDomain (Si i)) : IsDomain S := by
  classical
  have : NoZeroDivisors S := by
    refine ⟨fun {x y} hxy => ?_⟩
    obtain ⟨i, hi⟩ := exists_mem_of_finset Si hmono hcov {x, y}
    have hx : x ∈ Si i := hi x (by simp)
    have hy : y ∈ Si i := hi y (by simp)
    haveI := hdom i
    have h0 : (⟨x, hx⟩ : Si i) * ⟨y, hy⟩ = 0 := Subtype.ext (by simpa using hxy)
    rcases mul_eq_zero.mp h0 with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  exact NoZeroDivisors.to_isDomain S

lemma isIntegrallyClosed [IsDomain S] (Si : ι → Subalgebra R S) (hmono : Monotone Si)
    (hcov : ∀ s : S, ∃ i, s ∈ Si i)
    (hic : ∀ i, IsDomain (Si i) ∧ IsIntegrallyClosed (Si i)) : IsIntegrallyClosed S := by
  classical
  rw [isIntegrallyClosed_iff (FractionRing S)]
  intro x hx
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := S) x
  obtain ⟨p, hpm, hp⟩ := hx
  obtain ⟨i, hi⟩ := exists_mem_of_finset Si hmono hcov (insert a (insert b p.coeffs))
  haveI := (hic i).1
  haveI := (hic i).2
  have ha : a ∈ Si i := hi a (by simp)
  have hb' : b ∈ Si i := hi b (by simp)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  set g : Si i →+* FractionRing S := (algebraMap S (FractionRing S)).comp (algebraMap (Si i) S)
    with hg_def
  have hg : Function.Injective g :=
    (IsFractionRing.injective S (FractionRing S)).comp Subtype.val_injective
  let φ : FractionRing (Si i) →+* FractionRing S := IsFractionRing.lift hg
  have hφ : ∀ c : Si i, φ (algebraMap (Si i) (FractionRing (Si i)) c) = g c := fun c =>
    IsFractionRing.lift_algebraMap hg c
  have hlift : p ∈ Polynomial.lifts (algebraMap (Si i) S) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    by_cases hn : p.coeff n = 0
    · exact ⟨0, by simp [hn]⟩
    · exact ⟨⟨p.coeff n, hi _ (by simp [Polynomial.coeff_mem_coeffs hn])⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hpm
  set y : FractionRing (Si i) := algebraMap (Si i) (FractionRing (Si i)) ⟨a, ha⟩ /
    algebraMap (Si i) (FractionRing (Si i)) ⟨b, hb'⟩ with hy_def
  have hφy : φ y = algebraMap S (FractionRing S) a / algebraMap S (FractionRing S) b := by
    rw [hy_def, map_div₀, hφ, hφ]
    rfl
  have hyint : IsIntegral (Si i) y := by
    refine ⟨q, hqm, φ.injective ?_⟩
    rw [Polynomial.hom_eval₂, map_zero, hφy]
    have : φ.comp (algebraMap (Si i) (FractionRing (Si i))) = g :=
      RingHom.ext hφ
    rw [this, hg_def, ← Polynomial.eval₂_map, hq]
    exact hp
  obtain ⟨c, hc⟩ := (isIntegrallyClosed_iff (FractionRing (Si i))).mp (hic i).2 hyint
  refine ⟨(c : S), ?_⟩
  rw [← hφy, ← hc, hφ]
  rfl

end IndEtaleNormal

theorem indEtale_isDomain_isIntegrallyClosed :
    ∀ (R S : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing S] [Algebra R S]
      [Nontrivial S], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι)
        (Si : ι → Subalgebra R S), Monotone Si ∧ (∀ s : S, ∃ i, s ∈ Si i) ∧
        ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A)
          (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i)) →
      IsDomain S ∧ IsIntegrallyClosed S := by
  intro R S _ _ _ _ _ _ h
  obtain ⟨ι, _, _, _, Si, hmono, hcov, hloc⟩ := h
  have hic : ∀ i, IsDomain (Si i) ∧ IsIntegrallyClosed (Si i) := by
    intro i
    obtain ⟨A, _, _, _, q, _, ⟨e⟩⟩ := hloc i
    obtain ⟨h1, h2⟩ := etale_localization_atPrime_isDomain_isIntegrallyClosed R A q
    exact ⟨MulEquiv.isDomain (Localization.AtPrime q) e.symm.toMulEquiv,
      IsIntegrallyClosed.of_equiv e.toRingEquiv⟩
  haveI := IndEtaleNormal.isDomain Si hmono hcov (fun i => (hic i).1)
  exact ⟨inferInstance, IndEtaleNormal.isIntegrallyClosed Si hmono hcov hic⟩

end GlobalTheory
end

section

open IsLocalRing TensorProduct

namespace GlobalTheory.EtaleOverDirectedUnion

theorem localRing_of_etale_over_essEtale : ∀ (R S' E : Type) [CommRing R] [CommRing S'] [CommRing E] [Algebra R S'] [Algebra S' E] [Algebra R E] [IsScalarTower R S' E] [Algebra.Etale S' E], (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] S')) → ∀ (P : Ideal E) (_ : P.IsPrime), (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Localization.AtPrime P)) := by
  intro R S' E _ _ _ _ _ _ _ _ ⟨A, _, _, _, q, _, ⟨ψ⟩⟩ P hP
  letI : Algebra (Localization.AtPrime q) S' := ψ.toRingHom.toAlgebra
  letI : Algebra (Localization.AtPrime q) E := ((algebraMap S' E).comp ψ.toRingHom).toAlgebra
  haveI : IsScalarTower (Localization.AtPrime q) S' E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.Etale (Localization.AtPrime q) S' :=
    Algebra.Etale.of_equiv (R := Localization.AtPrime q)
      ({ ψ.toRingEquiv with commutes' := fun _ => rfl } : Localization.AtPrime q ≃ₐ[Localization.AtPrime q] S')
  haveI : Algebra.Etale (Localization.AtPrime q) E := Algebra.Etale.comp (Localization.AtPrime q) S' E
  haveI : IsScalarTower R (Localization.AtPrime q) E := IsScalarTower.of_algebraMap_eq (fun r => by
    show algebraMap R E r = algebraMap S' E (ψ (algebraMap R _ r))
    rw [ψ.commutes, ← IsScalarTower.algebraMap_apply])
  exact GlobalTheory.T.etale_local_ring_of_localization R A E q P

theorem span_one_tmul_eq_top (S B : Type) [CommRing S] [CommRing B] [Algebra S B] (A₀ B₀ : Type)
    [CommRing A₀] [CommRing B₀] [Algebra A₀ S] [Algebra A₀ B₀] (e : B ≃ₐ[S] S ⊗[A₀] B₀) :
    Submodule.span S (Set.range (fun b : B₀ => e.symm (1 ⊗ₜ b))) = ⊤ := by
  rw [eq_top_iff]
  intro y _
  rw [← e.symm_apply_apply y]
  induction e y using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | tmul s b =>
    have : s ⊗ₜ[A₀] b = s • ((1 : S) ⊗ₜ[A₀] b) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
  | add x z hx hz => rw [map_add]; exact add_mem hx hz

theorem fg_le_member {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {ι : Type} [Preorder ι]
    [IsDirected ι (· ≤ ·)] [Nonempty ι] (Si : ι → Subalgebra R S) (hmono : Monotone Si)
    (hcov : ∀ s : S, ∃ i, s ∈ Si i) (A₀ : Subalgebra R S) (h : A₀.FG) :
    ∃ i, A₀ ≤ Si i := by
  classical
  obtain ⟨t, rfl⟩ := h
  choose f hf using hcov
  obtain ⟨M, hM⟩ := Finset.exists_le (t.image f)
  exact ⟨M, Algebra.adjoin_le fun s hs => hmono (hM _ (Finset.mem_image_of_mem f hs)) (hf s)⟩

theorem construct : ∀ (R S B : Type) [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra S B] [Algebra R B] [IsScalarTower R S B] [Algebra.Etale S B], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra R S), Monotone Si ∧ (∀ s : S, ∃ i, s ∈ Si i) ∧ ∀ i, (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i))) → ∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (C : ι → Subalgebra R B), Monotone C ∧ (∀ b : B, ∃ i, b ∈ C i) ∧ ∀ i (P : Ideal (C i)) (_ : P.IsPrime), (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Localization.AtPrime P)) := by
  intro R S B _ _ _ _ _ _ _ _ ⟨ι, _, _, _, Si, hmono, hcov, hloc⟩
  obtain ⟨A₀, B₀, _, _, hfg, hét, ⟨e⟩⟩ := Algebra.Etale.exists_subalgebra_fg R S B
  obtain ⟨i₀, hi₀⟩ := fg_le_member Si hmono hcov A₀ hfg
  let g : B₀ → B := fun b => e.symm (1 ⊗ₜ b)
  let C : {j // i₀ ≤ j} → Subalgebra R B := fun j =>
    Algebra.adjoin R ((algebraMap S B) '' (Si j.1 : Set S) ∪ Set.range g)
  have hdir : IsDirected {j // i₀ ≤ j} (· ≤ ·) := ⟨fun a b => by
    obtain ⟨k, hak, hbk⟩ := directed_of (· ≤ ·) a.1 b.1
    exact ⟨⟨k, a.2.trans hak⟩, hak, hbk⟩⟩
  have hCmono : Monotone C := fun a b hab =>
    Algebra.adjoin_mono (Set.union_subset_union_left _ (Set.image_mono (hmono hab)))
  refine ⟨{j // i₀ ≤ j}, inferInstance, hdir, ⟨⟨i₀, le_rfl⟩⟩, C, hCmono, ?_, ?_⟩
  · intro b
    have hb : b ∈ Submodule.span S (Set.range g) := by
      rw [span_one_tmul_eq_top S B A₀ B₀ e]; trivial
    induction hb using Submodule.span_induction with
    | mem x hx => exact ⟨⟨i₀, le_rfl⟩, Algebra.subset_adjoin (Or.inr hx)⟩
    | zero => exact ⟨⟨i₀, le_rfl⟩, zero_mem _⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      obtain ⟨k, hak, hbk⟩ := directed_of (· ≤ ·) a b
      exact ⟨k, add_mem (hCmono hak ha) (hCmono hbk hb)⟩
    | smul s x _ hx =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨j, hj⟩ := hcov s
      obtain ⟨k, hak, hjk⟩ := directed_of (· ≤ ·) a.1 j
      refine ⟨⟨k, a.2.trans hak⟩, ?_⟩
      rw [Algebra.smul_def]
      exact mul_mem (Algebra.subset_adjoin (Or.inl ⟨s, hmono hjk hj, rfl⟩)) (hCmono hak ha)
  · intro j P hP
    obtain ⟨_, _, _⟩ := GlobalTheory.T.etale_adjoin_baseChange_image' R S B A₀ B₀ e (Si j.1) (hi₀.trans (hmono j.2))
    exact localRing_of_etale_over_essEtale R (Si j.1) (C j) (hloc j.1) P hP

end GlobalTheory.EtaleOverDirectedUnion
end

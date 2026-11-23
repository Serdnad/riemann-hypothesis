module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Combinatorics.Quiver.ReflQuiver
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle001
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.GenericMulOfProd
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.InstAddCommGroup
import GroundTheory.PAdicHodge.LogPowSeries
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison UpperTheory.Gal.crystallineComparison

theorem UpperTheory.exists_finite_sections_determining_ringHom_of_smooth :
    ∀ {O : Type} [CommRing O] {Y : Scheme.{0}} (q : Y ⟶ Spec (CommRingCat.of O)), Smooth q →
        ∀ {V : Y.Opens} (hV : IsAffineOpen V),
        ∃ (k : ℕ) (x : Fin k → Γ(Y, V)), ∀ (R : Type) [CommRing R] (f₁ f₂ : Γ(Y, V) →+* R),
          ptOf hV R f₁ ≫ q = ptOf hV R f₂ ≫ q → (∀ i, f₁ (x i) = f₂ (x i)) → f₁ = f₂ := by
  intro O _ Y q hq V hV
  have hlft : LocallyOfFiniteType q := inferInstance
  have htop : IsAffineOpen (⊤ : (Spec (CommRingCat.of O)).Opens) := isAffineOpen_top _
  have hle : V ≤ q ⁻¹ᵁ ⊤ := le_top
  have hψ : (q.appLE ⊤ V hle).hom.FiniteType :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) q hlft ⟨⊤, htop⟩ ⟨V, hV⟩ hle
  let ι : O →+* Γ(Spec (CommRingCat.of O), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom
  have hι : Function.Surjective ι :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of O)).inv).2
  let φ : O →+* Γ(Y, V) := (q.appLE ⊤ V hle).hom.comp ι
  have hφ : φ.FiniteType := hψ.comp (RingHom.FiniteType.of_surjective ι hι)
  letI : Algebra O Γ(Y, V) := φ.toAlgebra
  have hft : Algebra.FiniteType O Γ(Y, V) := hφ
  obtain ⟨s, hs⟩ := hft.out
  refine ⟨s.card, fun i => (s.equivFin.symm i : Γ(Y, V)), ?_⟩
  intro R _ f₁ f₂ hpt hgen
  have hcomp : f₁.comp (q.appLE ⊤ V hle).hom = f₂.comp (q.appLE ⊤ V hle).hom := by
    have e : ∀ f : Γ(Y, V) →+* R, ptOf hV R f ≫ q =
        Spec.map (CommRingCat.ofHom (f.comp (q.appLE ⊤ V hle).hom)) ≫ htop.fromSpec := by
      intro f
      unfold ptOf
      rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec q htop hV hle, ← Category.assoc,
        ← Spec.map_comp]
      rfl
    rw [e, e] at hpt
    have h1 := Spec.map_injective ((cancel_mono htop.fromSpec).1 hpt)
    exact congrArg CommRingCat.Hom.hom h1
  have hO : ∀ a : O, f₁ (algebraMap O Γ(Y, V) a) = f₂ (algebraMap O Γ(Y, V) a) := fun a =>
    congrArg (fun g : Γ(Spec (CommRingCat.of O), ⊤) →+* R => g (ι a)) hcomp
  have hx : ∀ a ∈ s, f₁ a = f₂ a := fun a ha => by
    have := hgen (s.equivFin ⟨a, ha⟩)
    simpa using this
  ext a
  have ha : a ∈ Algebra.adjoin O (s : Set Γ(Y, V)) := by rw [hs]; trivial
  induction ha using Algebra.adjoin_induction with
  | mem b hb => exact hx b hb
  | algebraMap r => exact hO r
  | add b c _ _ hb hc => rw [map_add (f := _), map_add (f := _), hb, hc]
  | mul b c _ _ hb hc => rw [map_mul, map_mul, hb, hc]
end

section


set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison TensorProduct UpperTheory.Gal.crystallineComparison UpperTheory.Ru.crystallineComparison

theorem UpperTheory.linear_combination_transfer_of_projector_relations :
    ∀ {A : Type} [CommRing A] {H H' : Type 1} [AddCommGroup H] [Module A H] [AddCommGroup H'] [Module A H']
        {J ι : Type} [Fintype J] [Fintype ι] {I : J → Type} [∀ i, Fintype (I i)] (G : H →ₗ[A] H') (P : ∀ i, I i → (H →ₗ[A] H'))
        (Ev : ι → H) (Wc : J → ι → H) (β γ L R : A) (σ : J → ℤ) (ρ : J → A) (cc : J → ι → A) (Z : J → H)
        (_ : ∀ i k, β • G (Wc i k) = γ • ∑ a, P i a (Ev k))
        (_ : ∀ i, (L * ρ i) • ∑ k, cc i k • Ev k = R • Z i)
        (_ : ∑ x : Σ i, I i, σ x.1 • P x.1 x.2 (Z x.1) = 0),
        (L * β) • G (∑ q : J × ι, ((σ q.1 : A) * ρ q.1 * cc q.1 q.2) • Wc q.1 q.2) = 0 := by
  intro A _ H H' _ _ _ _ J ι _ _ I _ G P Ev Wc β γ L R σ ρ cc Z h1 h2 h3
  have hi : ∀ i, ∑ k, (L * ρ i * cc i k) • (β • G (Wc i k)) = (γ * R) • ∑ a, P i a (Z i) := by
    intro i
    have e1 : ∀ a, ∑ k, (L * ρ i * cc i k) • P i a (Ev k) = R • P i a (Z i) := by
      intro a
      have := congrArg (P i a) (h2 i)

      simp only [map_smul, map_sum, Finset.smul_sum, smul_smul] at this
      simpa only [mul_assoc] using this
    calc ∑ k, (L * ρ i * cc i k) • (β • G (Wc i k))
        = ∑ k, (L * ρ i * cc i k) • (γ • ∑ a, P i a (Ev k)) := by simp only [h1]
      _ = γ • ∑ a, ∑ k, (L * ρ i * cc i k) • P i a (Ev k) := by
          rw [Finset.sum_comm]
          simp only [Finset.smul_sum, smul_comm γ]
      _ = (γ * R) • ∑ a, P i a (Z i) := by
          rw [Finset.sum_congr rfl fun a _ => e1 a, mul_smul, ← Finset.smul_sum]
  have h3' : ∑ i, (σ i : A) • ∑ a, P i a (Z i) = 0 := by
    rw [Fintype.sum_sigma] at h3
    simpa only [Finset.smul_sum, Int.cast_smul_eq_zsmul] using h3
  calc (L * β) • G (∑ q : J × ι, ((σ q.1 : A) * ρ q.1 * cc q.1 q.2) • Wc q.1 q.2)
      = ∑ i, (σ i : A) • ∑ k, (L * ρ i * cc i k) • (β • G (Wc i k)) := by
        rw [Fintype.sum_prod_type]

        simp only [map_sum, map_smul, Finset.smul_sum, smul_smul]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
        congr 1
        ring
    _ = (γ * R) • ∑ i, (σ i : A) • ∑ a, P i a (Z i) := by
        simp only [hi, Finset.smul_sum (s := Finset.univ) (r := γ * R), smul_comm (γ * R)]
    _ = 0 := by rw [h3', smul_zero]
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison UpperTheory.Gal.crystallineComparison

private lemma key {R : Type} [CommRing R]
    (hsec : ∀ (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)), Etale f → Surjective f →
      ∃ s, s ≫ f = 𝟙 _)
    {I : Type} [Finite I] (f : I → R) (hcov : ∀ p : PrimeSpectrum R, ∃ k, f k ∉ p.asIdeal) :
    ∃ r : (Π k, Localization.Away (f k)) →+* R,
      r.comp (algebraMap R (Π k, Localization.Away (f k))) = RingHom.id R := by
  let A : I → CommRingCat.{0} := fun k => CommRingCat.of (Localization.Away (f k))
  let m : ∀ k, Spec (A k) ⟶ Spec (CommRingCat.of R) :=
    fun k => Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (f k))))
  let g : ∐ (fun k => Spec (A k)) ⟶ Spec (CommRingCat.of R) := Sigma.desc m
  have hEt : Etale g := by
    refine (IsZariskiLocalAtSource.sigmaDesc (P := @Etale) ?_)
    intro k
    infer_instance
  have hSu : Surjective g := by
    refine ⟨fun p => ?_⟩
    obtain ⟨k, hk⟩ := hcov p
    have hp : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away (f k)))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away (f k)) (f k)]
      exact hk
    obtain ⟨q, rfl⟩ := hp
    refine ⟨(Sigma.ι (fun k => Spec (A k)) k) q, ?_⟩
    have : Sigma.ι (fun k => Spec (A k)) k ≫ g = m k := Sigma.ι_desc _ _
    rw [← Scheme.Hom.comp_apply, this]
    rfl
  obtain ⟨s, hs⟩ := hsec _ g hEt hSu
  have hg : g = sigmaSpec A ≫ Spec.map (CommRingCat.ofHom (algebraMap R (Π k, Localization.Away (f k)))) := by
    refine Sigma.hom_ext _ _ fun k => ?_
    rw [Sigma.ι_desc, ι_sigmaSpec_assoc, ← Spec.map_comp]
    rfl
  let r' := Spec.preimage (s ≫ sigmaSpec A)
  have hr' : Spec.map r' = s ≫ sigmaSpec A := Spec.map_preimage _
  have hc : CommRingCat.ofHom (algebraMap R (Π k, Localization.Away (f k))) ≫ r' = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hr', Category.assoc, ← hg, hs, Spec.map_id]
  exact ⟨r'.hom, congrArg CommRingCat.Hom.hom hc⟩

theorem UpperTheory.exists_orthogonalIdempotents_subordinate_of_etale_sections :
    ∀ (R : Type) [CommRing R],
        (∀ (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)), Etale f → Surjective f → ∃ s, s ≫ f = 𝟙 _) →
        ∀ (ι : Type) (W : ι → Set (PrimeSpectrum R)), (∀ i, IsOpen (W i)) → (∀ p, ∃ i, p ∈ W i) →
        ∃ (I : Type) (_ : Fintype I) (e : I → R) (a : I → ι), CompleteOrthogonalIdempotents e ∧
          ∀ i (p : PrimeSpectrum R), e i ∉ p.asIdeal → p ∈ W (a i) := by
  intro R _ hsec ι W hWo hWc
  classical
  let J : Type := {x : ι × R // (PrimeSpectrum.basicOpen x.2 : Set (PrimeSpectrum R)) ⊆ W x.1}
  have hcov : (Set.univ : Set (PrimeSpectrum R)) ⊆
      ⋃ j : J, (PrimeSpectrum.basicOpen j.1.2 : Set (PrimeSpectrum R)) := by
    intro p _
    obtain ⟨i, hi⟩ := hWc p
    obtain ⟨_, ⟨f, rfl⟩, hpf, hsub⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hi (hWo i)
    exact Set.mem_iUnion.2 ⟨⟨(i, f), hsub⟩, hpf⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover _
    (fun j : J => (PrimeSpectrum.basicOpen j.1.2).isOpen) hcov
  let f : t → R := fun k => k.1.1.2
  have hcovI : ∀ p : PrimeSpectrum R, ∃ k, f k ∉ p.asIdeal := by
    intro p
    obtain ⟨j, hj, hp⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ p))
    exact ⟨⟨j, hj⟩, hp⟩
  obtain ⟨r, hr⟩ := key hsec f hcovI
  have hrf : ∀ x, r (algebraMap R _ x) = x := fun x => congrArg (fun h => h x) hr
  refine ⟨t, inferInstance, fun k => r (Pi.single k 1), fun k => k.1.1.1, ?_, ?_⟩
  · exact (CompleteOrthogonalIdempotents.single (fun k => Localization.Away (f k))).map r
  · intro k p hp
    refine k.1.2 ?_
    show f k ∉ p.asIdeal
    intro hf
    apply hp
    have hu : Pi.single k 1 = algebraMap R (Π k, Localization.Away (f k)) (f k) *
        Pi.single k (IsLocalization.Away.invSelf (f k)) := by
      ext l
      by_cases h : l = k
      · subst h
        simp [IsLocalization.Away.mul_invSelf]
      · simp [Pi.single_eq_of_ne h]
    show r (Pi.single k 1) ∈ p.asIdeal
    rw [hu, map_mul, hrf]
    exact p.asIdeal.mul_mem_right _ hf
end

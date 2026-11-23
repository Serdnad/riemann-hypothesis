module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.LinearAlgebra.Span.Defs
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import ReciprocityTheory.Hypotheses.GalCoh
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
public import Mathlib.RingTheory.Localization.FractionRing
public import ReciprocityTheory.Hypotheses.GalCohDefs
import Mathlib.Algebra.AffineMonoid.Basic
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
public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.RamificationInertia.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.LinearAlgebra.Basis.VectorSpace
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle013
import Formalism.ConjugateSelfDual.Bundle001
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct

namespace GlobalTheory

private lemma span_range_eval_embeddings_eq_whole (F D : Type) [Field F] [Fintype D] (σ : D → (F →+* F))
    (hσ : Function.Injective σ) :
    Submodule.span F (Set.range (fun c : F => fun d : D => σ d c)) = ⊤ := by

  classical
  by_contra hne
  obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  have hli : LinearIndependent F (fun d : D => ((σ d : F →* F) : F → F)) := by
    refine (linearIndependent_monoidHom F F).comp (fun d => (σ d : F →* F)) ?_
    intro a b h
    apply hσ
    ext x
    exact congrArg (fun g : F →* F => g x) h
  rw [Fintype.linearIndependent_iff] at hli
  have hzero : ∑ d, f (Pi.single d 1) • ((σ d : F →* F) : F → F) = 0 := by
    funext c
    have hc : (fun d : D => σ d c) ∈ LinearMap.ker f := hle (Submodule.subset_span ⟨c, rfl⟩)
    rw [LinearMap.mem_ker] at hc
    have hdecomp : (fun d : D => σ d c) = ∑ d, σ d c • Pi.single d (1 : F) := by
      ext e
      simp [Finset.sum_apply, Pi.single_apply]

    rw [hdecomp, map_sum] at hc
    simp only [map_smul, smul_eq_mul] at hc
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← hc]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp [mul_comm]
  have hall := hli _ hzero
  apply hf0
  ext d
  simpa using hall d

theorem stable_le_span_invariants_of_semilinear_family :
    ∀ (F M D : Type) [Field F] [AddCommGroup M] [Module F M] [Fintype D] (σ : D → (F →+* F)) (t : D → (M →+ M)) (V : Submodule F M), Function.Injective σ → (∀ d (c : F), ∀ y ∈ V, t d (c • y) = σ d c • t d y) → (∀ d, ∀ y ∈ V, t d y ∈ V) → (∀ d, ∀ y ∈ V, t d (∑ d', t d' y) = ∑ d', t d' y) → (∃ d, ∀ y ∈ V, t d y = y) → V ≤ Submodule.span F {y | y ∈ V ∧ ∀ d, t d y = y} := by
  classical
  rintro F M D _ _ _ _ σ t V hσ hsemi hV hinv ⟨d₀, hd₀⟩ y hy
  let W := Submodule.span F {y | y ∈ V ∧ ∀ d, t d y = y}
  let Φ : (D → F) →ₗ[F] M :=
    { toFun := fun w => ∑ d, w d • t d y
      map_add' := by
        intro a b
        simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro c a
        simp [Finset.smul_sum, smul_smul] }
  have hmem : ∀ c : F, (∑ d, σ d c • t d y) ∈ W := by
    intro c
    apply Submodule.subset_span
    have hcy : c • y ∈ V := V.smul_mem c hy
    have heq : ∑ d, σ d c • t d y = ∑ d, t d (c • y) :=
      Finset.sum_congr rfl fun d _ => (hsemi d c y hy).symm
    rw [heq]
    exact ⟨V.sum_mem fun d _ => hV d _ hcy, fun d => hinv d _ hcy⟩
  have hle : Submodule.span F (Set.range (fun c : F => fun d : D => σ d c)) ≤ W.comap Φ := by
    rw [Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    exact hmem c
  rw [span_range_eval_embeddings_eq_whole F D σ hσ] at hle
  have h1 : Φ (Pi.single d₀ 1) ∈ W := hle Submodule.mem_top
  have h2 : Φ (Pi.single d₀ 1) = y := by
    show ∑ d, (Pi.single d₀ (1 : F) : D → F) d • t d y = y
    rw [Finset.sum_eq_single d₀]
    · simp [hd₀ y hy]
    · intro b _ hb
      simp [Pi.single_apply, hb]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [h2] at h1
  exact h1

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw
open scoped TensorProduct

namespace GlobalTheory.JointDiag

theorem aeval_restrict_coe {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (W : Submodule K V) (hW : ∀ x ∈ W, T x ∈ W) (q : K[X]) (y : W) :
    ((aeval (T.restrict hW) q y : W) : V) = aeval T q (y : V) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n c =>
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, Module.End.pow_restrict,
      LinearMap.restrict_apply, Submodule.coe_smul]
    rw [Module.End.pow_restrict n hW]
    rfl

theorem ker_prod {K M : Type} [Field K] [AddCommGroup M] [Module K M]
    (f : Module.End K M) (s : Finset K) :
    LinearMap.ker (aeval f (∏ r ∈ s, (X - C r))) = ⨆ r ∈ s, f.eigenspace r := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
    exact LinearMap.ker_id
  · intro a s ha ih
    rw [Finset.prod_insert ha, ← sup_ker_aeval_eq_ker_aeval_mul_of_coprime, ih, Finset.iSup_insert]
    · congr 1
      rw [Module.End.eigenspace_def, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]
    · exact IsCoprime.prod_right fun i hi =>
        (pairwise_coprime_X_sub_C (K := K) (s := id) Function.injective_id) (fun h => ha (h ▸ hi))

theorem iSup_eigenspace_eq_top_of_aeval {K M : Type} [Field K] [AddCommGroup M] [Module K M]
    (f : Module.End K M) (p : K[X]) (hs : p.Separable) (hp : p.Splits) (h0 : aeval f p = 0) :
    ⨆ μ, f.eigenspace μ = ⊤ := by
  classical
  have hne : p ≠ 0 := hs.ne_zero
  let s : Finset K := ⟨p.roots, nodup_roots hs⟩
  have hprod : ∏ r ∈ s, (X - C r) = (p.roots.map (X - C ·)).prod := rfl
  have hc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hne
  have hker : LinearMap.ker (aeval f (∏ r ∈ s, (X - C r))) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have h1 := LinearMap.congr_fun h0 x
    rw [hp.eq_prod_roots, ← hprod, map_mul, aeval_C, Module.End.mul_apply,
      Module.algebraMap_end_apply, LinearMap.zero_apply, smul_eq_zero] at h1
    exact h1.resolve_left hc
  rw [ker_prod] at hker
  rw [eq_top_iff, ← hker]
  exact iSup₂_le fun r _ => le_iSup (fun μ => f.eigenspace μ) r

theorem le_iSup_jointEigenspace_inf : ∀ (K V ι : Type) [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (T : ι → Module.End K V) (W : Submodule K V), (∀ a c, Commute (T a) (T c)) → (∀ a, ∀ x ∈ W, T a x ∈ W) → (∀ a, ∃ p : K[X], p.Separable ∧ p.Splits ∧ ∀ x ∈ W, Polynomial.aeval (T a) p x = 0) → W ≤ ⨆ ev : ι → K, ((⨅ a, LinearMap.ker (T a - ev a • LinearMap.id)) ⊓ W) := by
  intro K V ι _ _ _ _ T W hc hW hp
  let S : ι → Module.End K W := fun a => (T a).restrict (hW a)
  have hS0 : ∀ a, ∃ p : K[X], p.Separable ∧ p.Splits ∧ aeval (S a) p = 0 := by
    intro a
    obtain ⟨p, hs, hsp, hx⟩ := hp a
    refine ⟨p, hs, hsp, LinearMap.ext fun y => Subtype.ext ?_⟩
    rw [aeval_restrict_coe]
    simpa using hx y y.2
  have hmax : ∀ a μ, (S a).maxGenEigenspace μ = (S a).eigenspace μ := by
    intro a μ
    obtain ⟨p, hs, _, h0⟩ := hS0 a
    exact (Module.End.isSemisimple_of_squarefree_aeval_eq_zero hs.squarefree h0).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ
  have hdiag : ∀ a, ⨆ μ, (S a).maxGenEigenspace μ = ⊤ := by
    intro a
    obtain ⟨p, hs, hsp, h0⟩ := hS0 a
    simp_rw [hmax]
    exact iSup_eigenspace_eq_top_of_aeval (S a) p hs hsp h0
  have hcomm : Pairwise fun i j => Commute (S i) (S j) := fun i j _ =>
    LinearMap.restrict_commute (hc i j) (hW i) (hW j)
  have htop := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute S hcomm hdiag
  simp_rw [hmax] at htop
  have hle : Submodule.map W.subtype (⨆ χ : ι → K, ⨅ a, (S a).eigenspace (χ a)) ≤
      ⨆ ev : ι → K, ((⨅ a, LinearMap.ker (T a - ev a • LinearMap.id)) ⊓ W) := by
    rw [Submodule.map_iSup]
    refine iSup_mono fun χ => ?_
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨?_, y.2⟩
    rw [SetLike.mem_coe] at hy ⊢
    rw [Submodule.mem_iInf]
    intro a
    have h := Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hy a)
    have h' := congrArg Subtype.val h
    simp only [S, LinearMap.restrict_apply, Submodule.coe_smul] at h'
    rw [LinearMap.mem_ker, Submodule.subtype_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, h', sub_self]
  intro x hx
  have hmem : (⟨x, hx⟩ : W) ∈ ⨆ χ : ι → K, ⨅ a, (S a).eigenspace (χ a) := by
    rw [htop]; trivial
  exact hle ⟨⟨x, hx⟩, hmem, rfl⟩

end GlobalTheory.JointDiag
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published

namespace GlobalTheory.EulerScalars

noncomputable def subquotEquiv {R R' X : Type*} [CommRing R] [CommRing R'] [AddCommGroup X]
    [Module R X] [Module R' X] (Z B : Submodule R X) (Z' B' : Submodule R' X)
    (hZ : ∀ x, x ∈ Z ↔ x ∈ Z') (hB : ∀ x, x ∈ B ↔ x ∈ B') :
    (Z ⧸ B.comap Z.subtype) ≃ (Z' ⧸ B'.comap Z'.subtype) :=
  Quotient.congr (Equiv.subtypeEquivRight hZ) fun a b => by
    rw [Submodule.quotientRel_def, Submodule.quotientRel_def]
    exact hB _

theorem global_euler_char : GlobalFiniteness → GlobalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (Λ M : Type) [CommRing Λ] [AddCommGroup M] [Module Λ M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (ρ : Representation Λ (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M), (∀ m : M, l • m = 0) → ContainsAbove S l → ContAction ρ → Finite (H1 ρ) ∧ Finite (H2 ρ) ∧ Nat.card (H1 ρ) = Nat.card (H0 ρ) * Nat.card (H2 ρ) * Nat.card M ^ InfinitePlace.nrComplexPlaces F := by
  intro hF hE F Ω _ _ _ _ _ _ l _ Λ M _ _ _ _ _ _ S ρ hl hS hc

  obtain ⟨_⟩ : Nonempty (Module (ZMod (l ^ 1)) M) :=
    ⟨AddCommGroup.zmodModule (n := l ^ 1) (by simpa using hl)⟩
  obtain ⟨ρ', hρ'⟩ : ∃ ρ' : Representation (ZMod (l ^ 1)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M,
      ∀ g m, ρ' g m = ρ g m := ⟨zmodRep (l ^ 1) ρ, fun _ _ => rfl⟩

  have hc' : ContAction ρ' := by
    unfold ReciprocityTheory.Gal.ContAction at hc ⊢
    simpa only [hρ'] using hc
  have hd : ∀ c : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) → M,
      ReciprocityTheory.Gal.d1 ρ c = ReciprocityTheory.Gal.d1 ρ' c := by
    intro c
    funext p
    rcases p with ⟨g, h⟩
    simp only [ReciprocityTheory.Gal.d1_apply, hρ']
  have e0 : {m : M // m ∈ ReciprocityTheory.Gal.H0 ρ} ≃ {m : M // m ∈ ReciprocityTheory.Gal.H0 ρ'} := by
    refine Equiv.subtypeEquivRight fun m => ?_
    rw [ReciprocityTheory.Gal.mem_riemannRochSpace_iff_regularAt_everywhere, ReciprocityTheory.Gal.mem_riemannRochSpace_iff_regularAt_everywhere]
    simp only [hρ']
  have c0 : Nat.card (ReciprocityTheory.Gal.H0 ρ) = Nat.card (ReciprocityTheory.Gal.H0 ρ') := Nat.card_congr e0
  have e1 : ReciprocityTheory.Gal.H1 ρ ≃ ReciprocityTheory.Gal.H1 ρ' :=
    subquotEquiv _ _ _ _
      (fun f => by rw [ReciprocityTheory.Gal.mem_Z1_iff_cocycle, ReciprocityTheory.Gal.mem_Z1_iff_cocycle]; simp only [hρ'])
      (fun f => by rw [ReciprocityTheory.Gal.mem_coboundaries1, ReciprocityTheory.Gal.mem_coboundaries1]; simp only [hρ'])
  have e2 : ReciprocityTheory.Gal.H2 ρ ≃ ReciprocityTheory.Gal.H2 ρ' :=
    subquotEquiv _ _ _ _
      (fun f => by rw [ReciprocityTheory.Gal.mem_cocycles2, ReciprocityTheory.Gal.mem_cocycles2]; simp only [hρ'])
      (fun f => by rw [ReciprocityTheory.Gal.separated_dvr_second_cohomology_mem, ReciprocityTheory.Gal.separated_dvr_second_cohomology_mem]; simp only [hd])

  obtain ⟨-, f1, f2, -⟩ := hF F Ω l 1 M S ρ' one_pos hS hc'
  have hreal : ∀ w : InfinitePlace F, ¬ w.IsReal := fun w =>
    InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w)
  have heq := hE F Ω l 1 M S ρ' one_pos hS hc' (fun _ => 1) (fun w hw => absurd hw (hreal w))

  have harch : archH0Card S ρ' (fun _ => 1) = Nat.card M ^ InfinitePlace.nrComplexPlaces F := by
    classical
    unfold archH0Card
    rw [Finset.prod_eq_one, one_mul]
    intro w hw
    exact absurd (Finset.mem_filter.mp hw).2 (hreal w)
  rw [harch, IsTotallyComplex.finrank] at heq
  refine ⟨Finite.of_equiv _ e1.symm, Finite.of_equiv _ e2.symm, ?_⟩
  rw [Nat.card_congr e1, c0, Nat.card_congr e2]
  have hpos : 0 < Nat.card M ^ InfinitePlace.nrComplexPlaces F := pow_pos Nat.card_pos _
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [← heq, two_mul, pow_add]
  ring

end GlobalTheory.EulerScalars
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published

namespace GlobalTheory.LocEulerScalars

theorem nonempty_subquot_equiv {R R' X : Type*} [Ring R] [Ring R'] [AddCommGroup X] [Module R X]
    [Module R' X] (Z B : Submodule R X) (Z' B' : Submodule R' X)
    (hZ : ∀ x, x ∈ Z ↔ x ∈ Z') (hB : ∀ x, x ∈ B ↔ x ∈ B') :
    Nonempty ((Z ⧸ B.comap Z.subtype) ≃ (Z' ⧸ B'.comap Z'.subtype)) := by
  refine ⟨Quotient.congr (Equiv.subtypeEquivRight hZ) fun a b => ?_⟩
  change (B.comap Z.subtype).quotientRel a b ↔
    (B'.comap Z'.subtype).quotientRel (Equiv.subtypeEquivRight hZ a) (Equiv.subtypeEquivRight hZ b)
  rw [Submodule.quotientRel_def, Submodule.quotientRel_def, Submodule.mem_comap,
    Submodule.mem_comap]
  exact hB _

theorem localEulerChar_above : LocalFiniteness → LocalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (Λ M : Type) [CommRing Λ] [AddCommGroup M] [Module Λ M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (ρ : Representation Λ (Dec (F := F) A) M), (∀ m : M, l • m = 0) → IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → ContAction ρ → Finite (H1 ρ) ∧ Finite (H2 ρ) ∧ Nat.card (H1 ρ) = Nat.card (H0 ρ) * Nat.card (H2 ρ) * Nat.card M ^ ReciprocityTheory.Gal.locDeg v := by
  intro hF hE F Ω _ _ _ _ _ _ l _ Λ M _ _ _ _ _ _ A v ρ hl hA hv hc

  let _ : Module (ZMod (l ^ 1)) M := AddCommGroup.zmodModule fun m => by rw [pow_one]; exact hl m
  let ρ' : Representation (ZMod (l ^ 1)) (Dec (F := F) A) M := zmodRep (l ^ 1) ρ
  have hc' : ContAction ρ' := hc

  have hd : ∀ c : Dec (F := F) A → M, d1 ρ c = d1 ρ' c := fun c => by
    funext p
    obtain ⟨g, h⟩ := p
    rw [d1_apply, d1_apply]
    rfl
  have hZ1 : ∀ f, f ∈ Z1 ρ ↔ f ∈ Z1 ρ' := fun f => by
    rw [mem_Z1_iff_cocycle, mem_Z1_iff_cocycle]
    exact Iff.rfl
  have hB1 : ∀ f, f ∈ B1 ρ ↔ f ∈ B1 ρ' := fun f => by
    rw [mem_coboundaries1, mem_coboundaries1]
    exact Iff.rfl
  have hZ2 : ∀ f, f ∈ Z2 ρ ↔ f ∈ Z2 ρ' := fun f => by
    rw [mem_cocycles2, mem_cocycles2]
    exact Iff.rfl
  have hB2 : ∀ f, f ∈ B2 ρ ↔ f ∈ B2 ρ' := fun f => by
    rw [separated_dvr_second_cohomology_mem, separated_dvr_second_cohomology_mem]
    simp only [hd]
  obtain ⟨e1⟩ := nonempty_subquot_equiv (Z1 ρ) (B1 ρ) (Z1 ρ') (B1 ρ') hZ1 hB1
  obtain ⟨e2⟩ := nonempty_subquot_equiv (Z2 ρ) (B2 ρ) (Z2 ρ') (B2 ρ') hZ2 hB2
  have c1 : Nat.card (H1 ρ) = Nat.card (H1 ρ') := Nat.card_congr e1
  have c2 : Nat.card (H2 ρ) = Nat.card (H2 ρ') := Nat.card_congr e2

  obtain ⟨-, h1, h2, -⟩ := hF F Ω l 1 M A ρ' v Nat.one_pos hA hc'
  have hχ := (hE F Ω l 1 M A ρ' v Nat.one_pos hA hc').1 hv
  refine ⟨Finite.of_equiv _ e1.symm, Finite.of_equiv _ e2.symm, ?_⟩
  rw [c1, c2]
  convert hχ using 3

  exact Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)

end GlobalTheory.LocEulerScalars
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms
open scoped TensorProduct

namespace GlobalTheory.IntRestBall

open GlobalTheory.TwAll

theorem span_inf_of_span_top {O V : Type} [CommRing O] [IsDomain O] [AddCommGroup V] [Module O V]
    [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V] (B : Submodule O V)
    (hB : Submodule.span (FractionRing O) (B : Set V) = ⊤) (W : Submodule (FractionRing O) V)
    (M : Submodule O V) (hM : ∀ f, f ∈ M ↔ f ∈ B ∧ f ∈ W) :
    Submodule.span (FractionRing O) (M : Set V) = W := by
  apply le_antisymm
  · rw [Submodule.span_le]
    exact fun f hf => ((hM f).1 hf).2
  · intro f hf
    have h1 : f ∈ Submodule.span (FractionRing O) (B : Set V) := hB ▸ Submodule.mem_top
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors O) (FractionRing O) (B : Set V) f h1
    rw [Submodule.span_eq] at ht
    have e : t • f = (algebraMap O (FractionRing O) t) • f := by
      rw [algebraMap_smul]; rfl
    have hne : algebraMap O (FractionRing O) t ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors t.2
    have h2 : t • f ∈ M := (hM _).2 ⟨ht, e ▸ W.smul_mem _ hf⟩
    have h3 := (Submodule.span (FractionRing O) (M : Set V)).smul_mem
      (algebraMap O (FractionRing O) t)⁻¹ (Submodule.subset_span h2)
    rwa [e, smul_smul, inv_mul_cancel₀ hne, one_smul] at h3

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  {Y : NExp D.R D.host D.what₂ D.LL0 N X} (T : NTh D.R D.host D.what₂ D.LL0 N X Y)

end GlobalTheory.IntRestBall
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published

namespace GlobalTheory.Proof.LocalDegreeSum

theorem sum_locDeg : ∀ (F : Type) [Field F] [NumberField F] (l : ℕ) [Fact l.Prime] [Fintype {v : HeightOneSpectrum (𝓞 F) // ((l : ℕ) : 𝓞 F) ∈ v.asIdeal}], ∑ v : {v : HeightOneSpectrum (𝓞 F) // ((l : ℕ) : 𝓞 F) ∈ v.asIdeal}, ReciprocityTheory.Gal.locDeg v.1 = Module.finrank ℚ F := by
  intro F _ _ l hl _
  classical

  set p : Ideal ℤ := Ideal.span {(l : ℤ)} with hp
  have hpmax : p.IsMaximal := Int.ideal_span_isMaximal_of_prime l
  have : p.IsPrime := hpmax.isPrime
  have hp0 : p ≠ 0 := by
    rw [hp, Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl.out.ne_zero

  have key : ∀ v : HeightOneSpectrum (𝓞 F),
      ((l : ℕ) : 𝓞 F) ∈ v.asIdeal ↔ v.asIdeal ∣ Ideal.map (algebraMap ℤ (𝓞 F)) p := by
    intro v
    rw [Ideal.dvd_iff_le, hp, Ideal.map_span, Set.image_singleton,
      Ideal.span_singleton_le_iff_mem]
    simp

  let e := (Equiv.subtypeEquivRight key).trans (HeightOneSpectrum.equivPrimesOver (𝓞 F) hp0)
  rw [← NumberField.RingOfIntegers.rank, ← Ideal.sum_ramification_inertia_eq_finrank p (𝓞 F)]
  exact Fintype.sum_equiv e _ _ (fun v => by rfl)

end GlobalTheory.Proof.LocalDegreeSum
end

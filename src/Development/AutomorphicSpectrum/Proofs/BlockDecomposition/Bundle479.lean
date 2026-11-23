module

public import Mathlib.FieldTheory.Separable
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeakApproximationIntegral
import GroundTheory.GlobalFields.LocalFieldAtPlace
import GroundTheory.GlobalFields.TateThesis.AdelicCharDual
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
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Artinian.Instances
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulEqOfRangeLe
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.WedgeSub
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.QuotVanish
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.InvTransposeGLInvTransposeGL
public import Mathlib.Algebra.Algebra.Spectrum.Basic

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.TorusCh.CyclicVector

theorem exists_ne_zero_aeval_mulVec_eq_zero {K : Type} [Field K] {n : ℕ}
    (γ : Matrix (Fin n) (Fin n) K) (p : K[X]) (hp : Irreducible p) (hd : p ∣ γ.charpoly) :
    ∃ w : Fin n → K, w ≠ 0 ∧ aeval γ p *ᵥ w = 0 := by
  classical
  apply Matrix.exists_mulVec_eq_zero_iff.2
  have : Fact (Irreducible p) := ⟨hp⟩
  let L := AdjoinRoot p
  let f := (Algebra.ofId K L).mapMatrix (m := Fin n)
  let M' : Matrix (Fin n) (Fin n) L := γ.map (algebraMap K L)
  have hf : f (aeval γ p) = aeval M' p := (Polynomial.aeval_algHom_apply f γ p).symm
  have hroot : M'.charpoly.IsRoot (AdjoinRoot.root p) := by
    rw [Matrix.charpoly_map, IsRoot.def, eval_map, ← aeval_def,
      AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero]
    exact hd
  have hs : AdjoinRoot.root p ∈ spectrum L M' := Matrix.mem_spectrum_iff_isRoot_charpoly.2 hroot
  have h2 := spectrum.subset_polynomial_aeval M' (p.map (algebraMap K L)) ⟨_, hs, rfl⟩
  rw [aeval_map_algebraMap] at h2
  have h0 : eval (AdjoinRoot.root p) (p.map (algebraMap K L)) = 0 := by
    rw [eval_map, ← aeval_def, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  beta_reduce at h2
  rw [h0, spectrum.zero_mem_iff] at h2
  have h3 : (aeval M' p).det = 0 := by
    by_contra hne
    exact h2 ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hne))
  have h4 : (algebraMap K L) (aeval γ p).det = 0 := by
    rw [RingHom.map_det, ← h3, ← hf]
    rfl
  exact (map_eq_zero_iff _ (algebraMap K L).injective).1 h4

theorem exists_vector_annihilator_dvd {K : Type} [Field K] {n : ℕ}
    (γ : Matrix (Fin n) (Fin n) K) (hs : γ.charpoly.Separable) :
    ∃ v : Fin n → K, ∀ h : K[X], aeval γ h *ᵥ v = 0 → γ.charpoly ∣ h := by
  classical
  set χ := γ.charpoly with hχ
  have hχ0 : χ ≠ 0 := (Matrix.charpoly_monic γ).ne_zero
  have hsq : Squarefree χ := hs.squarefree
  let S : Finset K[X] := (UniqueFactorizationMonoid.normalizedFactors χ).toFinset
  have hSirr : ∀ p ∈ S, Irreducible p := fun p hp =>
    UniqueFactorizationMonoid.irreducible_of_normalized_factor p (Multiset.mem_toFinset.1 hp)
  have hSdvd : ∀ p ∈ S, p ∣ χ := fun p hp =>
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.1 hp)
  have hw : ∀ p : K[X], ∃ w : Fin n → K, p ∈ S → w ≠ 0 ∧ aeval γ p *ᵥ w = 0 := by
    intro p
    by_cases hp : p ∈ S
    · obtain ⟨w, h1, h2⟩ := exists_ne_zero_aeval_mulVec_eq_zero γ p (hSirr p hp) (hSdvd p hp)
      exact ⟨w, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose w hw using hw
  refine ⟨∑ p ∈ S, w p, fun h hh => ?_⟩

  have key : ∀ p ∈ S, p ∣ h := by
    intro p hp
    obtain ⟨q, hq⟩ := hSdvd p hp
    have hpi := hSirr p hp
    have hpq : ¬ p ∣ q := by
      rintro ⟨r, rfl⟩
      exact hpi.not_isUnit (hsq p ⟨r, by rw [hq]; ring⟩)
    have hother : ∀ p' ∈ S, p' ≠ p → aeval γ q *ᵥ w p' = 0 := by
      intro p' hp' hne
      have hd : p' ∣ q := by
        have h1 : p' ∣ p * q := hq ▸ hSdvd p' hp'
        rcases (hSirr p' hp').prime.dvd_or_dvd h1 with h2 | h2
        · exfalso
          apply hne
          have hass : Associated p' p := (hSirr p' hp').associated_of_dvd hpi h2
          have e1 := UniqueFactorizationMonoid.normalize_normalized_factor p' (Multiset.mem_toFinset.1 hp')
          have e2 := UniqueFactorizationMonoid.normalize_normalized_factor p (Multiset.mem_toFinset.1 hp)
          rw [← e1, ← e2]
          exact normalize_eq_normalize_iff.2 ⟨hass.dvd, hass.symm.dvd⟩
        · exact h2
      obtain ⟨r, rfl⟩ := hd
      rw [mul_comm p' r, map_mul, ← Matrix.mulVec_mulVec, (hw p' hp').2, Matrix.mulVec_zero]
    have hqv : aeval γ q *ᵥ (∑ p' ∈ S, w p') = aeval γ q *ᵥ w p := by
      rw [Matrix.mulVec_sum, Finset.sum_eq_single_of_mem p hp]
      intro p' hp' hne
      exact hother p' hp' hne
    have hker : aeval γ (h * q) *ᵥ w p = 0 := by
      rw [map_mul, ← Matrix.mulVec_mulVec, ← hqv, Matrix.mulVec_mulVec, ← map_mul, mul_comm h q,
        map_mul, ← Matrix.mulVec_mulVec, hh, Matrix.mulVec_zero]
    by_contra hph
    have hcop : IsCoprime p (h * q) :=
      (hpi.coprime_iff_not_dvd.2 hph).mul_right (hpi.coprime_iff_not_dvd.2 hpq)
    obtain ⟨a, b, hab⟩ := hcop
    apply (hw p hp).1
    have hval := congrArg (fun t => aeval γ t *ᵥ w p) hab
    simp only [map_add (f := _), map_mul, map_one, Matrix.one_mulVec, Matrix.add_mulVec] at hval
    rw [← hval, ← Matrix.mulVec_mulVec, (hw p hp).2, ← Matrix.mulVec_mulVec (M := aeval γ b),
      ← map_mul, hker]
    simp
  by_cases hh0 : h = 0
  · simp [hh0]
  have hnd := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hχ0).1 hsq
  refine (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hχ0 hh0).2
    ((Multiset.le_iff_subset hnd).2 fun p hp => ?_)
  have hpS : p ∈ S := Multiset.mem_toFinset.2 hp
  have hnorm := UniqueFactorizationMonoid.normalize_normalized_factor p hp
  exact (UniqueFactorizationMonoid.mem_normalizedFactors_iff' hh0).2 ⟨hSirr p hpS, hnorm, key p hpS⟩

theorem exists_cyclic_vector : ∀ (K : Type) [Field K] (n : ℕ) (γ : Matrix (Fin n) (Fin n) K),
    γ.charpoly.Separable → ∃ v : Fin n → K, ∀ y : Fin n → K, ∃ h : K[X], y = aeval γ h *ᵥ v := by
  intro K _ n γ hs
  obtain ⟨v, hv⟩ := exists_vector_annihilator_dvd γ hs
  refine ⟨v, ?_⟩
  let T : K[X] →ₗ[K] (Fin n → K) :=
    { toFun := fun h => aeval γ h *ᵥ v
      map_add' := fun a b => by simp [Matrix.add_mulVec]
      map_smul' := fun c a => by simp [Matrix.smul_mulVec] }
  let F : (Fin n → K) →ₗ[K] (Fin n → K) :=
    T ∘ₗ (degreeLT K n).subtype ∘ₗ (degreeLTEquiv K n).symm.toLinearMap
  have hinj : Function.Injective F := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro c hc
    have hd : γ.charpoly ∣ (((degreeLTEquiv K n).symm c : degreeLT K n) : K[X]) := hv _ hc
    have hdeg : (((degreeLTEquiv K n).symm c : degreeLT K n) : K[X]).degree < γ.charpoly.degree := by
      rw [Matrix.charpoly_degree_eq_dim, Fintype.card_fin]
      exact Polynomial.mem_degreeLT.1 ((degreeLTEquiv K n).symm c).2
    have h0 := Polynomial.eq_zero_of_dvd_of_degree_lt hd hdeg
    have h1 : (degreeLTEquiv K n).symm c = 0 := Subtype.ext h0
    simpa using h1
  have hsurj : Function.Surjective F := LinearMap.injective_iff_surjective.1 hinj
  intro y
  obtain ⟨c, hc⟩ := hsurj y
  exact ⟨_, hc.symm⟩

end GlobalTheory.CompanionTheory.TorusCh.CyclicVector
end

section

open scoped Pointwise Topology
open IsDedekindDomain NumberField

namespace GlobalTheory.CompanionTheory.AddSA

variable {F : Type} [Field F] [NumberField F]

theorem exists_approx_finite (w : InfinitePlace F) (x : InfiniteAdeleRing F)
    (y : FiniteAdeleRing (𝓞 F) F) (O : ∀ v : InfinitePlace F, Set v.Completion)
    (hO : ∀ v, O v ∈ 𝓝 (x v)) {U : Set (FiniteAdeleRing (𝓞 F) F)} (hU : U ∈ 𝓝 y) :
    ∃ t : F, (∀ v, v ≠ w → algebraMap F v.Completion t ∈ O v) ∧
      algebraMap F (FiniteAdeleRing (𝓞 F) F) t ∈ U := by
  classical
  have hW : (fun z => y + z) ⁻¹' U ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F) :=
    (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using hU)
  obtain ⟨d, hd0, hd⟩ := GroundTheory.Global.exists_forall_mul_mem_of_mem_nhds hW
  have hdF : (d : F) ≠ 0 := by simpa using hd0
  set e : FiniteAdeleRing (𝓞 F) F := algebraMap F _ (d : F)⁻¹ with he
  have hfin : {v : HeightOneSpectrum (𝓞 F) |
      ¬ (e v ∈ v.adicCompletionIntegers F ∧ (e * y) v ∈ v.adicCompletionIntegers F)}.Finite := by
    have h1 := e.2
    have h2 := (e * y).2
    have := h1.and h2
    exact this
  let T₂ : Finset (HeightOneSpectrum (𝓞 F)) := hfin.toFinset
  have hOF : ∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen {z : v.adicCompletion F | e v * (z - y v) ∈ v.adicCompletionIntegers F} ∧
        y v ∈ {z : v.adicCompletion F | e v * (z - y v) ∈ v.adicCompletionIntegers F} := by
    intro v
    refine ⟨(Valued.isOpen_valuationSubring _).preimage
      (continuous_const.mul (continuous_id.sub continuous_const)), ?_⟩
    show e v * (y v - y v) ∈ v.adicCompletionIntegers F
    simp
  obtain ⟨t, ht₁, ht₂, ht₃⟩ := GlobalTheory.CompanionTheory.PlaneSA.Additive.exists_approx_core (F := F) (Sum.inl w)
    (Finset.univ.erase w) T₂ (fun v hv h => (Finset.mem_erase.1 hv).1 (Sum.inl_injective h))
    (fun v _ h => by cases h) x O (fun v _ => hO v) (fun v => y v)
    (fun v => {z | e v * (z - y v) ∈ v.adicCompletionIntegers F}) (fun v _ => hOF v)
  refine ⟨t, fun v hv => ht₁ v (Finset.mem_erase.2 ⟨hv, Finset.mem_univ v⟩), ?_⟩
  have hmem : e * (algebraMap F (FiniteAdeleRing (𝓞 F) F) t - y) ∈
      GroundTheory.Global.integralFiniteAdeles (𝓞 F) F := by
    refine GroundTheory.Global.mem_integralFiniteAdeles.2 fun v => ?_
    by_cases hv : v ∈ T₂
    · exact ht₂ v hv
    · have hv' : e v ∈ v.adicCompletionIntegers F ∧ (e * y) v ∈ v.adicCompletionIntegers F := by
        simpa [T₂] using hv
      have h3 := ht₃ v hv (by simp)
      have : (e * (algebraMap F (FiniteAdeleRing (𝓞 F) F) t - y)) v =
          e v * algebraMap F (v.adicCompletion F) t - (e * y) v := by
        show e v * (algebraMap F (v.adicCompletion F) t - y v) = e v * _ - e v * y v
        ring
      rw [this]
      exact sub_mem (mul_mem hv'.1 h3) hv'.2
  have h := hd _ hmem
  have hde : algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * e = 1 := by
    rw [he, ← map_mul, mul_inv_cancel₀ hdF, map_one]
  have h4 : y + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) *
      (e * (algebraMap F (FiniteAdeleRing (𝓞 F) F) t - y)) =
      algebraMap F (FiniteAdeleRing (𝓞 F) F) t := by
    rw [← mul_assoc, hde]; ring
  simpa only [Set.mem_preimage, h4] using h

theorem dense_add_place : ∀ (F : Type) [Field F] [NumberField F] (w : NumberField.InfinitePlace F), Dense ((Set.range (algebraMap F (NumberField.AdeleRing (NumberField.RingOfIntegers F) F))) + {a : NumberField.AdeleRing (NumberField.RingOfIntegers F) F | a.2 = 0 ∧ ∀ w', w' ≠ w → a.1 w' = 0}) := by
  intro F _ _ w
  classical
  rw [dense_iff_inter_open]
  rintro U hU ⟨a, ha⟩
  obtain ⟨U₁, hU₁, U₂, hU₂, hsub⟩ := mem_nhds_prod_iff.1
    (show U ∈ 𝓝 ((a.1, a.2) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) from hU.mem_nhds ha)
  have hU₁' : U₁ ∈ Filter.pi (fun v : InfinitePlace F => 𝓝 (a.1 v)) := by
    have h : 𝓝 a.1 = Filter.pi (fun v : InfinitePlace F => 𝓝 (a.1 v)) := nhds_pi
    rwa [← h]
  obtain ⟨I, -, O, hO, hIO⟩ := Filter.mem_pi.1 hU₁'
  obtain ⟨t, ht₁, ht₂⟩ := exists_approx_finite w a.1 a.2 O hO hU₂
  let b : NumberField.AdeleRing (𝓞 F) F :=
    ((Function.update (0 : ∀ v : InfinitePlace F, v.Completion) w
      (a.1 w - algebraMap F w.Completion t) : InfiniteAdeleRing F), (0 : FiniteAdeleRing (𝓞 F) F))
  refine ⟨algebraMap F _ t + b, ?_, Set.add_mem_add ⟨t, rfl⟩ ⟨rfl, fun v hv => ?_⟩⟩
  · apply hsub
    refine ⟨hIO fun v _ => ?_, ?_⟩
    · by_cases hv : v = w
      · subst hv
        have : (algebraMap F (NumberField.AdeleRing (𝓞 F) F) t + b).1 v = a.1 v := by
          show algebraMap F v.Completion t + Function.update (0 : ∀ v : InfinitePlace F, v.Completion) v
            (a.1 v - algebraMap F v.Completion t) v = a.1 v
          simp
        show (algebraMap F (NumberField.AdeleRing (𝓞 F) F) t + b).1 v ∈ O v
        rw [this]
        exact mem_of_mem_nhds (hO v)
      · have : (algebraMap F (NumberField.AdeleRing (𝓞 F) F) t + b).1 v = algebraMap F v.Completion t := by
          show algebraMap F v.Completion t + Function.update (0 : ∀ v : InfinitePlace F, v.Completion) w
            (a.1 w - algebraMap F w.Completion t) v = _
          simp [Function.update_of_ne hv]
        show (algebraMap F (NumberField.AdeleRing (𝓞 F) F) t + b).1 v ∈ O v
        rw [this]
        exact ht₁ v hv
    · show algebraMap F (FiniteAdeleRing (𝓞 F) F) t + 0 ∈ U₂
      simpa using ht₂
  · show Function.update (0 : ∀ v : InfinitePlace F, v.Completion) w
      (a.1 w - algebraMap F w.Completion t) v = 0
    simp [Function.update_of_ne hv]

end GlobalTheory.CompanionTheory.AddSA
end

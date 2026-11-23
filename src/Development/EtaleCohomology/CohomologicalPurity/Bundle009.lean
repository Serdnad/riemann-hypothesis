module

public import Development.EtaleCohomology.CohomologicalPurity.Bundle005
public import Development.EtaleCohomology.CohomologicalPurity.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.CategoryTheory.Presentable.Type
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

def nbhdRet {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A) (hb : Function.Bijective
    (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map)) : B →+* A ⧸ I :=
  ((RingEquiv.ofBijective _ hb).symm : (B ⧸ I.map φ) →+* A ⧸ I).comp (Ideal.Quotient.mk (I.map φ))

theorem nbhdRet_comp {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A) (hb : Function.Bijective
    (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map)) (a : A) :
    nbhdRet φ I hb (φ a) = Ideal.Quotient.mk I a := by
  unfold nbhdRet
  simp only [RingHom.coe_comp, Function.comp_apply]
  rw [RingEquiv.coe_toRingHom, RingEquiv.symm_apply_eq]
  simp [Ideal.quotientMap_mk]

theorem nbhd_isPushout {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A) (hb : Function.Bijective
    (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map)) :
    IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom (Ideal.Quotient.mk I))
      (CommRingCat.ofHom (nbhdRet φ I hb)) (𝟙 (CommRingCat.of (A ⧸ I))) := by
  have w : CommRingCat.ofHom φ ≫ CommRingCat.ofHom (nbhdRet φ I hb) =
      CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ 𝟙 (CommRingCat.of (A ⧸ I)) := by
    ext a; simp [nbhdRet_comp]
  refine IsPushout.of_isColimit' ⟨w⟩ (PushoutCocone.IsColimit.mk _ (fun s => s.inr) ?_ ?_ ?_)
  · intro s
    ext b
    obtain ⟨x, hx⟩ := hb.2 (Ideal.Quotient.mk (I.map φ) b)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq] at hx
    have hker : ∀ y ∈ I.map φ, s.inl y = 0 := by
      intro y hy
      have hle : I.map φ ≤ RingHom.ker s.inl.hom := by
        rw [Ideal.map_le_iff_le_comap]
        intro i hi
        have := congrArg (fun g => g.hom i) s.condition
        simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
        simp only [Ideal.mem_comap, RingHom.mem_ker, this, Ideal.Quotient.eq_zero_iff_mem.2 hi, map_zero]
      exact hle hy
    have h1 : s.inl b = s.inl (φ a) := by
      have := hker _ hx
      rw [map_sub, sub_eq_zero] at this
      exact this.symm
    have h2 := congrArg (fun g => g.hom a) s.condition
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
    have h3 : nbhdRet φ I hb b = Ideal.Quotient.mk I a := by
      unfold nbhdRet
      simp only [RingHom.coe_comp, Function.comp_apply]
      rw [RingEquiv.coe_toRingHom, RingEquiv.symm_apply_eq, RingEquiv.ofBijective_apply, Ideal.quotientMap_mk]
      exact (Ideal.Quotient.eq.2 hx).symm
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
    rw [h3, h1, h2]
  · intro s; simp
  · intro s m h1 h2
    simpa using h2

theorem nbhd_isPullback {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A) (hb : Function.Bijective
    (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map)) :
    IsPullback (Spec.map (CommRingCat.ofHom (nbhdRet φ I hb))) (𝟙 _) (Spec.map (CommRingCat.ofHom φ))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) := by
  have := isPullback_SpecMap_of_isPushout _ _ _ _ (nbhd_isPushout φ I hb)
  simpa using this

theorem range_spec_quot {A : Type} [CommRing A] (I : Ideal A) :
    (off A I : Set (Spec (CommRingCat.of A))) = (Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))ᶜ := by
  ext x
  change x ∈ (PrimeSpectrum.zeroLocus (I : Set A))ᶜ ↔ x ∈ (Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)))ᶜ
  rw [range_comap_of_surjective _ _ (Ideal.Quotient.mk_surjective (I := I)), Ideal.mk_ker]

theorem leafNbhdExc_of (hE : LeafExc) : LeafNbhdExc := by
  intro a1 q A B _ _ φ I hN hq h
  obtain ⟨het, hb⟩ := hN
  have : Etale (Spec.map (CommRingCat.ofHom φ)) := HasRingHomProperty.Spec_iff.2 het
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  exact hE a1 q (Spec.map (CommRingCat.ofHom φ)) (Spec.map (CommRingCat.ofHom (nbhdRet φ I hb)))
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) (nbhd_isPullback φ I hb) _ _ (range_spec_quot I)
    (off_map φ I)

end LateralTheory.CohomologicalPurity
end
end

section

noncomputable section
open TensorProduct

namespace LateralTheory.CohomologicalPurity.LeafSpanPf

theorem span_of_subsingleton {R P B ι : Type} [CommRing R] [CommRing P] [CommRing B] [Algebra R P]
    [Algebra R B] [Algebra P B] [IsScalarTower R P B] [Subsingleton Ω[B⁄P]] (z : ι → P)
    (hz : Submodule.span P (Set.range fun i => KaehlerDifferential.D R P (z i)) = ⊤) :
    Submodule.span B (Set.range fun i => KaehlerDifferential.D R B (algebraMap P B (z i))) = ⊤ := by
  set T := Submodule.span B (Set.range fun i => KaehlerDifferential.D R B (algebraMap P B (z i)))
  have hmap : ∀ m : Ω[P⁄R], KaehlerDifferential.map R R P B m ∈ T := by
    intro m
    have hm : m ∈ Submodule.span P (Set.range fun i => KaehlerDifferential.D R P (z i)) := by
      rw [hz]; trivial
    induction hm using Submodule.span_induction with
    | mem m hm =>
      obtain ⟨i, rfl⟩ := hm
      rw [KaehlerDifferential.map_D]
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp
    | add a b _ _ ha hb => rw [map_add (f := _)]; exact T.add_mem ha hb
    | smul c m _ hm =>
      rw [LinearMap.map_smul, ← algebraMap_smul B c]
      exact T.smul_mem _ hm
  rw [eq_top_iff]
  intro ω _
  have hk : ω ∈ LinearMap.ker (KaehlerDifferential.map R P B B) := by
    rw [LinearMap.mem_ker]; exact Subsingleton.elim _ _
  have hbc : ∀ t, KaehlerDifferential.mapBaseChange R P B t ∈ T := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul b m =>
      rw [KaehlerDifferential.mapBaseChange_tmul]
      exact T.smul_mem _ (hmap m)
    | add a b ha hb => rw [map_add (f := _)]; exact T.add_mem ha hb
  obtain ⟨t, rfl⟩ := (KaehlerDifferential.exact_mapBaseChange_map R P B (ω)).mp hk
  exact hbc t

theorem annih {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    (S : Submodule A M) (p : Ideal A) (hp : p.IsPrime) (f : A) (hf : f ∉ p)
    (h : ∀ ω : M, f • ω ∈ S ⊔ p • ⊤) : ∃ g : A, g ∉ p ∧ ∀ ω : M, g • ω ∈ S := by
  let φ : Module.End A (M ⧸ S) := algebraMap A (Module.End A (M ⧸ S)) f
  have hφ : LinearMap.range φ ≤ p • ⊤ := by
    rintro _ ⟨n, rfl⟩
    obtain ⟨ω, rfl⟩ := S.mkQ_surjective n
    obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.mp (h ω)
    have e1 : φ (S.mkQ ω) = S.mkQ t := by
      simp only [φ, Module.algebraMap_end_apply, Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, ← hst,
        Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero S).mpr hs, zero_add]
    rw [e1]
    exact (Submodule.smul_mono (le_refl p) (le_top : Submodule.map S.mkQ ⊤ ≤ ⊤)) (by rw [← Submodule.map_smul'']; exact Submodule.mem_map_of_mem ht)
  obtain ⟨q, hmon, -, hcoef, hq⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero _ φ p hφ
  refine ⟨Polynomial.aeval f q, ?_, ?_⟩
  · intro hmem
    apply hf
    apply hp.mem_of_pow_mem q.natDegree
    have hsum : Polynomial.aeval f q = f ^ q.natDegree + ∑ k ∈ Finset.range q.natDegree, q.coeff k * f ^ k := by
      rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, hmon.coeff_natDegree]
      simp [add_comm, smul_eq_mul]
    have hlow : ∑ k ∈ Finset.range q.natDegree, q.coeff k * f ^ k ∈ p :=
      Ideal.sum_mem _ fun k hk => Ideal.mul_mem_right _ _
        (Ideal.pow_le_self (by have := Finset.mem_range.mp hk; omega) (hcoef k))
    have := p.sub_mem hmem hlow
    rwa [hsum, add_sub_cancel_right] at this
  · intro ω
    have e2 : Polynomial.aeval φ q = algebraMap A (Module.End A (M ⧸ S)) (Polynomial.aeval f q) :=
      Polynomial.aeval_algebraMap_apply _ _ _
    have := LinearMap.congr_fun hq (S.mkQ ω)
    rw [e2, Module.algebraMap_end_apply, LinearMap.zero_apply, Submodule.mkQ_apply,
      ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this
    exact this


open KaehlerDifferential in
theorem key {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (I : Ideal A) {e d : ℕ}
    (x : Fin d → A) (y : Fin e → A) (f : A) (hx : ∀ j, x j ∈ I)
    (hfI : ∀ a ∈ I, f * a ∈ Ideal.span (Set.range x))
    (hspan : Submodule.span (A ⧸ I) (Set.range fun k => D R (A ⧸ I) (Ideal.Quotient.mk I (y k))) = ⊤)
    (ω : Ω[A⁄R]) :
    f • ω ∈ Submodule.span A (Set.range fun k => D R A (Sum.elim x y k)) ⊔ I • ⊤ := by
  set S := Submodule.span A (Set.range fun k => D R A (Sum.elim x y k))
  have hSx : ∀ j, D R A (x j) ∈ S := fun j => Submodule.subset_span ⟨Sum.inl j, rfl⟩
  have hSy : ∀ k, D R A (y k) ∈ S := fun k => Submodule.subset_span ⟨Sum.inr k, rfl⟩
  have hI : ∀ a ∈ I, ∀ m : Ω[A⁄R], a • m ∈ S ⊔ I • ⊤ := fun a ha m =>
    Submodule.mem_sup_right (Submodule.smul_mem_smul ha trivial)
  have hDa : ∀ a ∈ I, f • D R A a ∈ S ⊔ I • ⊤ := by
    intro a ha
    obtain ⟨b, hb⟩ := Ideal.mem_span_range_iff_exists_fun.mp (hfI a ha)
    have e1 : D R A (f * a) = f • D R A a + a • D R A f := Derivation.leibniz _ _ _
    have e2 : D R A (f * a) = ∑ j, (b j • D R A (x j) + x j • D R A (b j)) := by

      rw [← hb, map_sum]; simp only [Derivation.leibniz]
    have e3 : f • D R A a = ∑ j, (b j • D R A (x j) + x j • D R A (b j)) - a • D R A f := by
      rw [← e2, e1]; abel
    rw [e3]
    refine Submodule.sub_mem _ (Submodule.sum_mem _ fun j _ => Submodule.add_mem _ ?_ ?_) (hI a ha _)
    · exact Submodule.mem_sup_left (S.smul_mem _ (hSx j))
    · exact hI _ (hx j) _
  have hω : map R R A (A ⧸ I) ω ∈
      Submodule.span (A ⧸ I) (Set.range fun k => D R (A ⧸ I) (Ideal.Quotient.mk I (y k))) := by
    rw [hspan]; trivial
  obtain ⟨c, hc⟩ := Submodule.mem_span_range_iff_exists_fun _ |>.mp hω
  choose c' hc' using fun k => Ideal.Quotient.mk_surjective (c k)
  set ω' := ω - ∑ k, c' k • D R A (y k) with hω'
  have hck : ∀ k, c' k • D R (A ⧸ I) (algebraMap A (A ⧸ I) (y k)) =
      c k • D R (A ⧸ I) (Ideal.Quotient.mk I (y k)) := by
    intro k
    rw [← algebraMap_smul (A ⧸ I) (c' k), Ideal.Quotient.algebraMap_eq, hc']
  have h0 : mapBaseChange R A (A ⧸ I) (1 ⊗ₜ ω') = 0 := by

    rw [mapBaseChange_tmul, one_smul, hω', map_sub, map_sum]
    simp only [LinearMap.map_smul_of_tower, map_D, hck, hc, sub_self]
  obtain ⟨t, ht⟩ := (exact_kerCotangentToTensor_mapBaseChange R A (A ⧸ I)
    Ideal.Quotient.mk_surjective (1 ⊗ₜ ω')).mp h0
  obtain ⟨a, rfl⟩ := Ideal.toCotangent_surjective _ t
  rw [kerCotangentToTensor_toCotangent] at ht
  have haI : (a : A) ∈ I := by
    exact Ideal.Quotient.eq_zero_iff_mem.mp a.2
  have hdiff : ω' - D R A a ∈ I • (⊤ : Submodule A Ω[A⁄R]) := by
    have h1 : (1 : A ⧸ I) ⊗ₜ[A] (ω' - D R A a) = 0 := by rw [tmul_sub, ← ht, sub_self]
    have := congrArg (TensorProduct.quotTensorEquivQuotSMul Ω[A⁄R] I) h1
    rwa [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, map_zero, Submodule.Quotient.mk_eq_zero] at this
  have e4 : f • ω = f • (ω' - D R A a) + f • ∑ k, c' k • D R A (y k) + f • D R A a := by
    rw [← smul_add, ← smul_add, hω']; congr 1; abel
  rw [e4]
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) (hDa a haI)
  · exact Submodule.mem_sup_right (Submodule.smul_mem _ f hdiff)
  · exact Submodule.mem_sup_left (S.smul_mem _ (Submodule.sum_mem _ fun k _ => S.smul_mem _ (hSy k)))

theorem LeafSpan_of : LateralTheory.CohomologicalPurity.ChartCut.LeafSpan := by
  intro e d R A _ _ _ _ I p hp hIp hB x f hx hf hfI
  obtain ⟨g, hg⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial (n := e) R (A ⧸ I)
  choose y hy using fun k : Fin e => Ideal.Quotient.mk_surjective (g (MvPolynomial.X k))
  have hspan : Submodule.span (A ⧸ I)
      (Set.range fun k => KaehlerDifferential.D R (A ⧸ I) (Ideal.Quotient.mk I (y k))) = ⊤ := by
    let _ : Algebra (MvPolynomial (Fin e) R) (A ⧸ I) := g.toRingHom.toAlgebra
    have : Algebra.Etale (MvPolynomial (Fin e) R) (A ⧸ I) := hg
    have : IsScalarTower R (MvPolynomial (Fin e) R) (A ⧸ I) :=
      IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
    have h := span_of_subsingleton (R := R) (P := MvPolynomial (Fin e) R) (B := A ⧸ I)
      MvPolynomial.X (by
        rw [← (KaehlerDifferential.mvPolynomialBasis R (Fin e)).span_eq]
        congr 2; funext i; simp [KaehlerDifferential.mvPolynomialBasis_apply])
    have e5 : (fun k => KaehlerDifferential.D R (A ⧸ I) (Ideal.Quotient.mk I (y k))) =
        fun k => KaehlerDifferential.D R (A ⧸ I)
          (algebraMap (MvPolynomial (Fin e) R) (A ⧸ I) (MvPolynomial.X k)) := by
      funext k; rw [hy]; rfl
    rw [e5]; exact h
  obtain ⟨g', hg'p, hg'⟩ := annih
    (Submodule.span A (Set.range fun k => KaehlerDifferential.D R A (Sum.elim x y k))) p hp f hf
    (fun ω => (show _ ⊔ I • (⊤ : Submodule A Ω[A⁄R]) ≤ _ ⊔ p • ⊤ from
      sup_le_sup_left (Submodule.smul_mono_left hIp) _) (key I x y f hx hfI hspan ω))
  exact ⟨y, g', hg'p, hg'⟩

end LateralTheory.CohomologicalPurity.LeafSpanPf
end
end

section

noncomputable section
open TensorProduct KaehlerDifferential

namespace LateralTheory.CohomologicalPurity.LeafEtPf

theorem etale_main (n : ℕ) (R A ι : Type) [CommRing R] [CommRing A] [Algebra R A] [Fintype ι] (z : ι → A)
    (hn : Fintype.card ι = n) (hA : Algebra.IsStandardSmoothOfRelativeDimension n R A)
    (hspan : Submodule.span A (Set.range fun k => KaehlerDifferential.D R A (z k)) = ⊤) :
    (MvPolynomial.eval₂Hom (algebraMap R A) z).Etale := by
  rcases subsingleton_or_nontrivial A with hA0 | hA0
  · exact ChartCut.etale_of_subsingleton _
  letI : Algebra (MvPolynomial ι R) A := (MvPolynomial.aeval z).toRingHom.toAlgebra
  have : IsScalarTower R (MvPolynomial ι R) A :=
    IsScalarTower.of_algebraMap_eq fun r => (MvPolynomial.aeval_C z r).symm
  have := hA
  have : Algebra.IsStandardSmooth R A := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  have hD : ∀ k, mapBaseChange R (MvPolynomial ι R) A
      ((1 : A) ⊗ₜ D R (MvPolynomial ι R) (MvPolynomial.X k)) = D R A (z k) := by
    intro k
    rw [mapBaseChange_tmul, one_smul, map_D]
    congr 1
    exact MvPolynomial.aeval_X z k
  have hsurj : Function.Surjective (mapBaseChange R (MvPolynomial ι R) A) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact ⟨_, hD k⟩
  haveI hΩ : Subsingleton Ω[A⁄MvPolynomial ι R] := by
    refine subsingleton_of_forall_eq 0 fun ω => ?_
    obtain ⟨w, rfl⟩ := map_surjective R (MvPolynomial ι R) A ω
    obtain ⟨u, rfl⟩ := hsurj w
    exact (exact_mapBaseChange_map R (MvPolynomial ι R) A).apply_apply_eq_zero u
  have hfin : Module.finrank A Ω[A⁄R] = n :=
    Module.finrank_eq_of_rank_eq (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n)
  let b := Algebra.TensorProduct.basis A (mvPolynomialBasis R ι)
  have hli : LinearIndependent A (mapBaseChange R (MvPolynomial ι R) A ∘ b) := by
    have : (mapBaseChange R (MvPolynomial ι R) A ∘ b) = fun k => D R A (z k) := by
      funext k
      simp only [Function.comp_apply, b, Algebra.TensorProduct.basis_apply, mvPolynomialBasis_apply, hD]
    rw [this]
    exact linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge (hn.trans hfin.symm)
  have hinj : Function.Injective (mapBaseChange R (MvPolynomial ι R) A) :=
    LinearMap.injective_of_linearIndependent b.span_eq hli
  haveI hH1 : Subsingleton (Algebra.H1Cotangent (MvPolynomial ι R) A) := by
    refine subsingleton_of_forall_eq 0 fun h => ?_
    have h1 : Algebra.H1Cotangent.δ R (MvPolynomial ι R) A h = 0 := by
      apply hinj
      rw [map_zero]
      exact (Algebra.H1Cotangent.exact_δ_mapBaseChange R (MvPolynomial ι R) A).apply_apply_eq_zero h
    obtain ⟨g, rfl⟩ := ((Algebra.H1Cotangent.exact_map_δ R (MvPolynomial ι R) A) h).mp h1
    rw [Subsingleton.elim g 0, map_zero]
  have : Algebra.FinitePresentation (MvPolynomial ι R) A :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R (MvPolynomial ι R) A
  have : Algebra.IsStandardSmooth (MvPolynomial ι R) A :=
    Algebra.IsStandardSmooth.of_basis_kaehlerDifferential (I := Empty) (Module.Basis.empty _) (by rintro _ ⟨i, _⟩; exact i.elim)
  have : Algebra.FormallyUnramified (MvPolynomial ι R) A := ⟨hΩ⟩
  have : Algebra.Etale (MvPolynomial ι R) A :=
    Algebra.Etale.iff_formallyUnramified_and_smooth.mpr ⟨inferInstance, inferInstance⟩
  exact RingHom.etale_algebraMap.mpr this

theorem LeafEt_of : ChartCut.LeafEt := by
  intro n R A ι _ _ _ _ z hn hA hspan
  exact etale_main n R A ι z hn hA hspan

end LateralTheory.CohomologicalPurity.LeafEtPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Bd.PushPf

variable (R : Type) [CommRing R]

instance pres_ulift : PreservesColimitsOfShape WalkingSpan uliftFunctor.{1, 0} := inferInstance

instance pres_freeMod : PreservesColimitsOfShape WalkingSpan (ModuleCat.free.{1} (ULift.{1} R)) :=
  (ModuleCat.adj (ULift.{1} R)).leftAdjoint_preservesColimits.preservesColimitsOfShape

instance pres_freeP : PreservesColimitsOfShape WalkingSpan (freeP R) := by
  unfold freeP; infer_instance

instance pres_sheafify : PreservesColimitsOfShape WalkingSpan
    (presheafToSheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))) := inferInstance

instance pres_free : PreservesColimitsOfShape WalkingSpan (free R) := by
  unfold free; infer_instance

instance pres_eval (k : ℕ) : PreservesColimitsOfShape WalkingSpan
    ((evaluation SimplexCategoryᵒᵖ PSh).obj (op (SimplexCategory.mk k))) := inferInstance

def isoN (k : ℕ) : chainsN R ⋙ HomologicalComplex.eval _ _ k ≅
    (evaluation SimplexCategoryᵒᵖ PSh).obj (op (SimplexCategory.mk k)) ⋙ free R :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

instance pres_N (k : ℕ) : PreservesColimitsOfShape WalkingSpan (chainsN R ⋙ HomologicalComplex.eval _ _ k) :=
  preservesColimitsOfShape_of_natIso (isoN R k).symm

theorem hk (k : ℕ) : ComplexShape.embeddingDownNat.f k = -(k : ℤ) := by simp

def isoC (k : ℕ) : chains R ⋙ HomologicalComplex.eval _ _ (-(k : ℤ)) ≅ chainsN R ⋙ HomologicalComplex.eval _ _ k :=
  NatIso.ofComponents (fun X => HomologicalComplex.extendXIso _ _ (hk k))
    (by
      intro X Y f
      change (HomologicalComplex.extendMap ((chainsN R).map f) ComplexShape.embeddingDownNat).f (-(k : ℤ)) ≫ _ =
        _ ≫ ((chainsN R).map f).f k
      rw [HomologicalComplex.extendMap_f _ _ (hk k)]
      simp)

theorem pres (p : ℤ) : PreservesColimitsOfShape WalkingSpan (chains R ⋙ HomologicalComplex.eval _ _ p) := by
  by_cases hp : ∃ k : ℕ, ComplexShape.embeddingDownNat.f k = p
  · obtain ⟨k, rfl⟩ := hp
    have := pres_N R k
    exact preservesColimitsOfShape_of_natIso (isoC R k).symm
  · push Not at hp
    apply Functor.preservesColimitsOfShape_of_isZero
    rw [Functor.isZero_iff]
    intro X
    exact HomologicalComplex.isZero_extend_X _ _ _ hp

end LateralTheory.CohomologicalPurity.Bd.PushPf

open LateralTheory.CohomologicalPurity.Bd.PushPf in
theorem LateralTheory.CohomologicalPurity.Bd.LeafPush_of : LateralTheory.CohomologicalPurity.Bd.LeafPush := by
  intro R _ U E E' D f g l r h p
  have := pres R p
  exact (chains R ⋙ HomologicalComplex.eval _ _ p).map_isPushout h
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Bd

theorem sec_map_comp {R : Type} [CommRing R] {F G H : Shv R} (a : F ⟶ G) (b : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (a ≫ b) x = Sec.map b (Sec.map a x) := rfl

theorem sec_map_add {R : Type} [CommRing R] {F G : Shv R} (a b : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (a + b) x = Sec.map a x + Sec.map b x := rfl

theorem sec_map_res {R : Type} [CommRing R] {F G : Shv R} (a : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map a x) = Sec.map a (Sec.res g x) := by
  simp only [Sec.res, Sec.map]
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← a.hom.naturality]

theorem LeafImgHom_of (hG : LeafGen) : LeafImgHom := by
  intro S R _ _ I J ρ
  have ex : ∀ (P : PSh) (s : ℤ) (φ : (free S).obj P ⟶ I.X s), ∃ ψ : (free R).obj P ⟶ J.X s,
      ∀ (U : Scheme.{0}) (x : P.obj (op U)), Sec.map ψ (freeGen R P U x) = ρ.app U s (Sec.map φ (freeGen S P U x)) := by
    intro P s φ
    refine (hG R P).2.2.2 (J.X s) (fun U x => ρ.app U s (Sec.map φ (freeGen S P U x))) ?_
    intro V U g x
    rw [ρ.nat, sec_map_res, (hG S P).1]
  choose T hT using ex
  have ext : ∀ (P : PSh) (s : ℤ) (ψ ψ' : (free R).obj P ⟶ J.X s),
      (∀ (U : Scheme.{0}) (x : P.obj (op U)), Sec.map ψ (freeGen R P U x) = Sec.map ψ' (freeGen R P U x)) → ψ = ψ' :=
    fun P s ψ ψ' h => (hG R P).2.2.1 _ ψ ψ' h
  refine ⟨fun P s => { toFun := T P s, map_zero' := ?_, map_add' := ?_ }, ?_, ?_, ?_⟩
  · apply ext; intro U x
    rw [hT]; show ρ.app U s 0 = 0; exact map_zero _
  · intro φ ψ; apply ext; intro U x
    rw [sec_map_add, hT, hT, hT, sec_map_add, map_add (f := _)]
  · intro P s φ U x; exact hT P s φ U x
  · intro P s t φ; apply ext; intro U x
    show Sec.map (T P t (φ ≫ I.d s t)) _ = Sec.map (T P s φ ≫ J.d s t) _
    rw [hT, sec_map_comp, sec_map_comp, hT, ρ.comm]
  · intro P P' f s φ; apply ext; intro U x
    show Sec.map (T P s ((free S).map f ≫ φ)) _ = Sec.map ((free R).map f ≫ T P' s φ) _
    rw [hT, sec_map_comp, sec_map_comp, (hG S P).2.1, (hG R P).2.1, hT]

end LateralTheory.CohomologicalPurity.Bd
end
end

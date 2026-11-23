module

public import Development.AutomorphicArithmetic.RepresentationRank.RepOfRank
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle004
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineHomOfFlatQuotientOfAffineKernel
public import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.RingTheory.Extension.Presentation.Submersive
public import Mathlib.RingTheory.Henselian
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Connected
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
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Ideal.IdempotentFG
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
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
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.RingTheory.Ideal.BigOperators
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

private lemma tensor_fe {S : Scheme.{0}} (Y₁ Y₂ : Over S) (h1 : IsFinite Y₁.hom) (e1 : Etale Y₁.hom)
    (h2 : IsFinite Y₂.hom) (e2 : Etale Y₂.hom) :
    IsFinite (Y₁ ⊗ Y₂).hom ∧ Etale (Y₁ ⊗ Y₂).hom := by
  have hY : (Y₁ ⊗ Y₂).hom = pullback.fst Y₁.hom Y₂.hom ≫ Y₁.hom := rfl
  rw [hY]
  exact ⟨inferInstance, inferInstance⟩

private lemma rep_empty {S : Scheme.{0}} (G : Over S) (hG : IsEmpty G.left) :
    UpperTheory.RepresentationRank.Rep G (Over.mk (𝟙 S)) (⊥ : ((Over.mk (𝟙 S)) ⊗ G).left.Opens) := by
  refine ⟨by simp, fun T V _ => ?_⟩
  have hE : IsEmpty (T ⊗ G).left := ⟨fun x => hG.false ((CartesianMonoidalCategory.snd T G).left x)⟩
  have hV : V = ⊥ := by
    ext x
    exact hE.elim x
  subst hV
  refine ⟨Over.homMk T.hom (by simp), ?_, ?_⟩
  · ext x
    exact hE.elim x
  · intro y _
    ext
    simpa using Over.w y

theorem UpperTheory.exists_clopRep_of_isSplitOfRank :
    ∀ {S : Scheme.{0}} (G : Over S) (n : ℕ), GlobalTheory.FinEt.IsSplitOfRank G.hom n → ∃ (Y : Over S) (U : (Y ⊗ G).left.Opens), UpperTheory.RepresentationRank.Rep G Y U ∧ IsFinite Y.hom ∧ Etale Y.hom := by
  intro S G n
  induction n generalizing G with
  | zero =>
    intro h
    have hG : IsEmpty G.left := (GlobalTheory.FinEt.isSplitOfRank_zero_iff G.hom).1 h
    refine ⟨Over.mk (𝟙 S), ⊥, rep_empty G hG, ?_, ?_⟩
    · show IsFinite (𝟙 S)
      infer_instance
    · show Etale (𝟙 S)
      infer_instance
  | succ n ih =>
    intro h
    obtain ⟨σ, hσ, V, hσp, hrange, hV⟩ := h.exists_of_succ
    obtain ⟨Y₁, U₁, hR₁, hf₁, he₁⟩ := UpperTheory.exists_clopRep_trivial S
    obtain ⟨Y₂, U₂, hR₂, hf₂, he₂⟩ := ih (Over.mk (V.ι ≫ G.hom)) hV
    obtain ⟨U, hU⟩ := UpperTheory.exists_clopRep_of_disjoint_open_cover G (Over.mk (𝟙 S)) (Over.mk (V.ι ≫ G.hom)) Y₁ Y₂
      (Over.homMk σ hσp) (Over.homMk V.ι rfl) U₁ U₂ hσ (show IsOpenImmersion V.ι from inferInstance)
      (show Set.range σ = (Set.range V.ι)ᶜ by rw [hrange, compl_compl]) hR₁ hR₂
    exact ⟨Y₁ ⊗ Y₂, U, hU, tensor_fe Y₁ Y₂ hf₁ he₁ hf₂ he₂⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

private lemma UpperTheory.isPullback_whisker_fst {S : Scheme.{0}} {T T' G : Over S} (y : T' ⟶ T) :
    IsPullback (y ▷ G).left (fst T' G).left (fst T G).left y.left := by
  have h : IsPullback (y ▷ G) (fst T' G) (fst T G) y := by
    refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => lift s.snd (s.fst ≫ snd _ _)) ?_ ?_ ?_⟩⟩
    · intro s
      apply CartesianMonoidalCategory.hom_ext
      · simp [s.condition]
      · simp
    · intro s
      simp
    · intro s m h1 h2
      apply CartesianMonoidalCategory.hom_ext
      · simpa using h2
      · simp only [lift_snd]
        rw [← h1, Category.assoc, whiskerRight_snd]
  exact h.map (Over.forget S)

theorem UpperTheory.clopProj_finrank_pullback :
    ∀ {S : Scheme.{0}} {T T' G : Over S} (y : T' ⟶ T) (V : (T ⊗ G).left.Opens), IsFinite G.hom → Etale G.hom → IsClosed (V : Set (T ⊗ G).left) → ∀ t : T'.left, (UpperTheory.RepresentationRank.proj ((y ▷ G).left ⁻¹ᵁ V)).finrank t = (UpperTheory.RepresentationRank.proj V).finrank (y.left t) := by
  intro S T T' G y V hfin het hcl t
  obtain ⟨hF, hE⟩ := UpperTheory.clopProj_finite_etale_of_isClosed V hfin het hcl
  have hsq := (isPullback_morphismRestrict (y ▷ G).left V).paste_vert (UpperTheory.isPullback_whisker_fst y)
  exact Scheme.Hom.finrank_of_isPullback _ _ _ _ hsq t
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

theorem UpperTheory.isFinite_of_isPullback_fpqc :
    ∀ {X Y X' Y' : Scheme.{0}} (a : X' ⟶ X) (q : X' ⟶ Y') (p : X ⟶ Y) (t : Y' ⟶ Y), IsPullback a q p t → Surjective t → Flat t → QuasiCompact t → IsFinite q → IsFinite p := by
  intro X Y X' Y' a q p t h h₁ h₂ h₃ hq
  have := GlobalTheory.isAffineHom_descendsAlong_fpqc.{0}
  have ht : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) t :=
    ⟨⟨h₁, h₂⟩, h₃⟩
  have hA : IsAffineHom p :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @IsAffineHom) h.flip ht inferInstance
  have hU : UniversallyClosed p :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @UniversallyClosed) h.flip ht inferInstance
  have hL : LocallyOfFiniteType p :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @LocallyOfFiniteType) h.flip ht inferInstance
  exact (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).2
    ⟨IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨hU, hA⟩, hL⟩
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

private theorem conn_of_idem (R : Type) [CommRing R] [Nontrivial R]
    (h : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1) : ConnectedSpace (PrimeSpectrum R) := by
  rw [connectedSpace_iff_clopen]
  refine ⟨inferInstance, fun s hs => ?_⟩
  obtain ⟨e, he, rfl⟩ := PrimeSpectrum.isClopen_iff.mp hs
  rcases h e he with rfl | rfl
  · left
    simp
  · right
    simp

private theorem idem_local (O : Type) [CommRing O] [IsLocalRing O] (e : O)
    (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with h | h
  · right
    have h1 : e * e = e * 1 := by rw [he.eq, mul_one]
    exact h.mul_left_cancel h1
  · left
    have h1 : (1 - e) * e = (1 - e) * 0 := by rw [mul_zero, sub_mul, one_mul, he.eq, sub_self]
    exact h.mul_left_cancel h1

private theorem idem_zero (O : Type) [CommRing O] [IsLocalRing O] (e : LaurentPolynomial O)
    (he : IsIdempotentElem e) (hm : ∀ n, e.coeff n ∈ IsLocalRing.maximalIdeal O) : e = 0 := by
  classical
  set I : Ideal O := Ideal.span ((e.coeff.support.image e.coeff : Finset O) : Set O) with hI
  have hfg : I.FG := ⟨_, rfl⟩
  have hmem : ∀ n, e.coeff n ∈ I := by
    intro n
    by_cases hn : n ∈ e.coeff.support
    · exact Ideal.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hn))
    · rw [Finsupp.notMem_support_iff.1 hn]
      exact zero_mem _
  have hsq : I ≤ I * I := by
    rw [hI, Ideal.span_le]
    intro x hx
    obtain ⟨n, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
    have h2 : e.coeff n = (e * e).coeff n := by rw [he.eq]
    rw [← hI, h2, AddMonoidAlgebra.coeff_mul]
    simp only [Finsupp.sum]
    refine Ideal.sum_mem _ fun i _ => Ideal.sum_mem _ fun j _ => ?_
    split_ifs
    · exact Ideal.mul_mem_mul (hmem i) (hmem j)
    · exact zero_mem _
  have hidem : IsIdempotentElem I := le_antisymm Ideal.mul_le_right hsq
  obtain ⟨f, hf, hIf⟩ := (Ideal.isIdempotentElem_iff_of_fg I hfg).mp hidem
  have hfI : f ∈ I := hIf ▸ Submodule.mem_span_singleton_self f
  have hIm : I ≤ IsLocalRing.maximalIdeal O := by
    rw [hI, Ideal.span_le]
    intro x hx
    obtain ⟨n, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
    exact hm n
  have hf0 : f = 0 := by
    rcases idem_local O f hf with h | h
    · exact h
    · exfalso
      have := hIm hfI
      rw [h] at this
      exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 this)
  apply AddMonoidAlgebra.ext
  ext n
  have hn := hmem n
  rw [hIf, hf0] at hn
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hn
  rw [← ha, smul_zero]
  rfl

private theorem idem_laurent (O : Type) [CommRing O] [IsLocalRing O] (e : LaurentPolynomial O)
    (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  set φ := AddMonoidAlgebra.mapRingHom ℤ (IsLocalRing.residue O) with hφ
  have key : ∀ x : LaurentPolynomial O, φ x = 0 → ∀ n, x.coeff n ∈ IsLocalRing.maximalIdeal O := by
    intro x hx n
    have := congrArg (fun y => AddMonoidAlgebra.coeff y n) hx
    simp only [hφ, AddMonoidAlgebra.coeff_mapRingHom] at this
    rw [← IsLocalRing.residue_eq_zero_iff]
    simpa using this
  rcases IsIdempotentElem.iff_eq_zero_or_one.1 (he.map φ) with h | h
  · left
    exact idem_zero O e he (key e h)
  · right
    have h1 : 1 - e = 0 := idem_zero O (1 - e) he.one_sub (key _ (by rw [map_sub, map_one, h, sub_self]))
    exact (sub_eq_zero.1 h1).symm

theorem UpperTheory.connectedSpace_spec_local_and_laurent :
    ∀ (O : Type) [CommRing O] [IsLocalRing O], ConnectedSpace (Spec (CommRingCat.of O)) ∧ ConnectedSpace (Spec (CommRingCat.of (LaurentPolynomial O))) := by
  intro O _ _
  exact ⟨conn_of_idem O (idem_local O), conn_of_idem _ (idem_laurent O)⟩
end

section

noncomputable section
open IsLocalRing UpperTheory.Et

private theorem etale_away_jacobian (A : Type) [CommRing A] (n : ℕ)
    (F : Fin n → MvPolynomial (Fin n) A) :
    Algebra.Etale A (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F))
      (Matrix.of fun s t : Fin n => MvPolynomial.pderiv s (F t)).det)) := by
  classical
  let I := Ideal.span (Set.range F)
  let d := Ideal.Quotient.mk I (Matrix.of fun s t : Fin n => MvPolynomial.pderiv s (F t)).det
  let P1 := Algebra.PreSubmersivePresentation.naive (v := F) (id : Fin n → Fin n)
    Function.injective_id
  let P2 := Algebra.PreSubmersivePresentation.localizationAway (Localization.Away d) d
  have hJ : P1.jacobian = d := by
    rw [P1.jacobian_eq_jacobiMatrix_det]
    have hM : P1.jacobiMatrix = Matrix.of fun s t : Fin n => MvPolynomial.pderiv s (F t) := by
      ext i j
      simp [P1]
    rw [hM, Algebra.Generators.algebraMap_apply]
    have hE : MvPolynomial.aeval P1.val = Ideal.Quotient.mkₐ A I :=
      MvPolynomial.algHom_ext fun i => by simp [P1, I, Algebra.Generators.naive]
    exact congrFun (congrArg DFunLike.coe hE) _
  let P : Algebra.SubmersivePresentation A (Localization.Away d) (Unit ⊕ Fin n) (Unit ⊕ Fin n) :=
    { P2.comp P1 with
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
          Algebra.smul_def, Algebra.PreSubmersivePresentation.localizationAway_jacobian, hJ]
        exact (IsLocalization.Away.algebraMap_isUnit d).mul
          (IsLocalization.Away.algebraMap_isUnit d) }
  have : Algebra.IsStandardSmoothOfRelativeDimension 0 A (Localization.Away d) :=
    P.isStandardSmoothOfRelativeDimension (by simp [Algebra.Presentation.dimension])
  infer_instance

theorem UpperTheory.exists_common_zero_of_jacobian_isUnit_henselian :
    ∀ (A : Type) [CommRing A] [HenselianLocalRing A] (n : ℕ) (F : Fin n → MvPolynomial (Fin n) A),
      (∀ i, MvPolynomial.eval 0 (F i) ∈ maximalIdeal A) → IsUnit (Matrix.det (Matrix.of fun i j => MvPolynomial.eval 0 (MvPolynomial.pderiv j (F i)))) →
      ∃ x : Fin n → A, (∀ i, MvPolynomial.eval x (F i) = 0) ∧ ∀ j, x j ∈ maximalIdeal A := by
  intro A _ _ n F hF hU
  classical
  let I := Ideal.span (Set.range F)
  let d := Ideal.Quotient.mk I (Matrix.of fun s t : Fin n => MvPolynomial.pderiv s (F t)).det
  haveI := etale_away_jacobian A n F
  let ψ : MvPolynomial (Fin n) A →ₐ[A] ResidueField A :=
    (Algebra.ofId A (ResidueField A)).comp (MvPolynomial.aeval (0 : Fin n → A))
  have hψ : ∀ p, ψ p = residue A (MvPolynomial.eval 0 p) := fun p => by
    simp [ψ, MvPolynomial.coe_aeval_eq_eval, IsLocalRing.ResidueField.algebraMap_eq]
  have hI : ∀ a ∈ I, ψ a = 0 := by
    intro a ha
    have hle : I ≤ RingHom.ker ψ := by
      refine Ideal.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, hψ, residue_eq_zero_iff]
      exact hF i
    exact hle ha
  let π0 : (MvPolynomial (Fin n) A ⧸ I) →ₐ[A] ResidueField A := Ideal.Quotient.liftₐ I ψ hI
  have hπ0 : ∀ p, π0 (Ideal.Quotient.mk I p) = residue A (MvPolynomial.eval 0 p) := fun p => by
    rw [← hψ]
    rfl
  have hd : IsUnit (π0 d) := by
    rw [hπ0]
    have hdet : MvPolynomial.eval 0 (Matrix.of fun s t : Fin n => MvPolynomial.pderiv s (F t)).det =
        (Matrix.of fun i j => MvPolynomial.eval 0 (MvPolynomial.pderiv j (F i))).det := by
      rw [RingHom.map_det, ← Matrix.det_transpose]
      congr 1
    rw [hdet]
    exact hU.map (residue A)
  let π : Localization.Away d →ₐ[A] ResidueField A :=
    IsLocalization.liftAlgHom (M := Submonoid.powers d) (f := π0) (by
      rintro ⟨y, k, rfl⟩
      simpa using hd.pow k)
  obtain ⟨σ, hσ⟩ := UpperTheory.exists_section_lift_of_etale_of_henselian A (Localization.Away d) π
  let φ : MvPolynomial (Fin n) A →ₐ[A] A :=
    (σ.comp (IsScalarTower.toAlgHom A _ (Localization.Away d))).comp (Ideal.Quotient.mkₐ A I)
  have hφ : ∀ p, φ p = MvPolynomial.eval (fun j => φ (MvPolynomial.X j)) p := by
    intro p
    rw [← MvPolynomial.coe_aeval_eq_eval]
    exact congrFun (congrArg DFunLike.coe
      (MvPolynomial.algHom_ext (fun j => by simp) : φ = MvPolynomial.aeval _)) p
  refine ⟨fun j => φ (MvPolynomial.X j), fun i => ?_, fun j => ?_⟩
  · rw [← hφ]
    have h0 : Ideal.Quotient.mk I (F i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨i, rfl⟩)
    simp [φ, h0]
  · rw [← residue_eq_zero_iff]
    show residue A (σ (algebraMap _ (Localization.Away d)
      (Ideal.Quotient.mk I (MvPolynomial.X j)))) = 0
    rw [hσ]
    simp [π, hπ0]

end
end

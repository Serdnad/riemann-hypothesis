module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateSandwichOfPrismaticDieudonne
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
public import Formalism.DirichletDensity.DirichletDensityProofs.Bundle001
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.EqOfLeOfAbsNormEq
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle006
public import Mathlib.CategoryTheory.MorphismProperty.Descent
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineHomOfFlatQuotientOfAffineKernel
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantSubspaceMobiusInverseCharpolyPrimaryEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle491
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle492
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle251
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle494
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle493
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.AlgebraicGeometry.Morphisms.Descent
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
import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm

@[expose] public section

section

noncomputable section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.BlockSum

def blk {R : Type} [Zero R] {m n : ℕ} (A : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin (m + n)) (Fin (m + n)) R :=
  (fromBlocks A 0 0 B).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

theorem blk_mulVec {R : Type} [CommRing R] {m n : ℕ} (A : Matrix (Fin m) (Fin m) R)
    (B : Matrix (Fin n) (Fin n) R) (x : Fin m → R) (y : Fin n → R) :
    blk A B *ᵥ Fin.append x y = Fin.append (A *ᵥ x) (B *ᵥ y) := by
  unfold blk
  rw [submatrix_mulVec_equiv, fromBlocks_mulVec]
  ext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · have : Fin.append x y ∘ finSumFinEquiv = Sum.elim x y := by
      ext (a | b) <;> simp
    simp [this]
  · have : Fin.append x y ∘ finSumFinEquiv = Sum.elim x y := by
      ext (a | b) <;> simp
    simp [this]

theorem blk_mul {R : Type} [CommRing R] {m n : ℕ} (A A' : Matrix (Fin m) (Fin m) R)
    (B B' : Matrix (Fin n) (Fin n) R) : blk A B * blk A' B' = blk (A * A') (B * B') := by
  unfold blk
  rw [submatrix_mul_equiv, fromBlocks_multiply]
  simp

theorem blk_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin n) (Fin n) R) :
    (blk A B).map f = blk (A.map f) (B.map f) := by
  unfold blk
  rw [← submatrix_map, fromBlocks_map]
  simp

theorem blk_smul_one {R : Type} [CommRing R] {m n : ℕ} (c : R) :
    blk (c • (1 : Matrix (Fin m) (Fin m) R)) (c • (1 : Matrix (Fin n) (Fin n) R)) =
      c • (1 : Matrix (Fin (m + n)) (Fin (m + n)) R) := by
  unfold blk
  have : fromBlocks (c • (1 : Matrix (Fin m) (Fin m) R)) 0 0 (c • (1 : Matrix (Fin n) (Fin n) R))
      = c • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) R) := by
    rw [← fromBlocks_one, fromBlocks_smul, smul_zero, smul_zero]
  rw [this, ← submatrix_one_equiv finSumFinEquiv.symm]
  rfl

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

def sum {ε : PreTilt O p} {h₁ h₂ : ℕ} (D₁ : Datum ε h₁ ℤ_[p]) (D₂ : Datum ε h₂ ℤ_[p]) :
    Datum ε (h₁ + h₂) ℤ_[p] where
  F := blk D₁.F D₂.F
  G := blk D₁.G D₂.G
  Ψ := blk D₁.Ψ D₂.Ψ
  Ψ' := blk D₁.Ψ' D₂.Ψ'
  ρT := Algebra.ofId _ _
  ρM := (RingHom.mapMatrix (ofPadic p O)).comp (algebraMap _ _)
  G_mul_F := by rw [blk_mul, D₁.G_mul_F, D₂.G_mul_F, blk_smul_one]
  F_eq := by rw [blk_map, blk_mul, ← D₁.F_eq, ← D₂.F_eq]
  Ψ_mul := by rw [blk_mul, D₁.Ψ_mul, D₂.Ψ_mul, blk_smul_one]
  F_act := by
    intro a
    have : ((algebraMap ℤ_[p] (Matrix (Fin (h₁ + h₂)) (Fin (h₁ + h₂)) ℤ_[p]) a).map (ofPadic p O))
        = ofPadic p O a • (1 : Matrix (Fin (h₁ + h₂)) (Fin (h₁ + h₂)) (Ainf p O)) := by
      ext1 i j
      by_cases h : i = j <;> simp [Matrix.algebraMap_matrix_apply, h]
    simp only [Algebra.ofId_apply, RingHom.comp_apply, RingHom.mapMatrix_apply, this,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]

theorem sum_al {ε : PreTilt O p} {h₁ h₂ : ℕ} (D₁ : Datum ε h₁ ℤ_[p]) (D₂ : Datum ε h₂ ℤ_[p])
    (x : Fin h₁ → O) (y : Fin h₂ → O) :
    (sum D₁ D₂).al (Fin.append x y) = Fin.append (D₁.al x) (D₂.al y) := by
  change Matrix.toLin' ((blk D₁.F D₂.F).map _) _ = _
  rw [blk_map, toLin'_apply, blk_mulVec]
  rfl

theorem sum_bb {ε : PreTilt O p} {h₁ h₂ : ℕ} (D₁ : Datum ε h₁ ℤ_[p]) (D₂ : Datum ε h₂ ℤ_[p])
    (x : Fin h₁ → O) (y : Fin h₂ → O) :
    (sum D₁ D₂).bb (Fin.append x y) = Fin.append (D₁.bb x) (D₂.bb y) := by
  change Matrix.toLin' ((blk D₁.G D₂.G).map _) _ = _
  rw [blk_map, toLin'_apply, blk_mulVec]
  rfl

theorem exists_sum_datum : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ (h₁ h₂ : ℕ) (D₁ : Datum ε h₁ ℤ_[p]) (D₂ : Datum ε h₂ ℤ_[p]), ∃ D : Datum ε (h₁ + h₂) ℤ_[p], (∀ x y, D.al (Fin.append x y) = Fin.append (D₁.al x) (D₂.al y)) ∧ ∀ x y, D.bb (Fin.append x y) = Fin.append (D₁.bb x) (D₂.bb y) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ ε hε h₁ h₂ D₁ D₂
  exact ⟨sum D₁ D₂, sum_al D₁ D₂, sum_bb D₁ D₂⟩

end GlobalTheory.BlockSum
end
end

section

open GlobalTheory.Sandwich

theorem _root_.GlobalTheory.T.hodgeTateSandwich_of_prismaticDieudonne : GlobalTheory.Published.PrismaticDieudonneHodge → ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ [IsDomain O] (ε : PreTilt O p) (hε : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε), GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.HodgeTateSandwichAt hε := by
  first | exact @GlobalTheory.DieudonneSandwich.hodgeTateSandwich_of_prismaticDieudonne₂ | exact GlobalTheory.DieudonneSandwich.hodgeTateSandwich_of_prismaticDieudonne₂ | (intros; apply GlobalTheory.DieudonneSandwich.hodgeTateSandwich_of_prismaticDieudonne₂ <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke Polynomial

namespace GlobalTheory

theorem finrank_eq_two_of_adjoin_sqrt_eq_top (K : Type) [Field K] [NumberField K] (a : ℤ) (x : K)
    (hx : x ^ 2 = (a : K)) (hadj : IntermediateField.adjoin ℚ {x} = ⊤) (hsf : Squarefree a) (h1 : a ≠ 1) :
    Module.finrank ℚ K = 2 := by
  have hirr : Irreducible (X ^ 2 - C (a : ℚ)) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two (Formalism.HF.P.quad_not_sq_rat a hsf h1)
  have hmon : (X ^ 2 - C (a : ℚ)).Monic := monic_X_pow_sub_C _ two_ne_zero
  have hev : aeval x (X ^ 2 - C (a : ℚ)) = 0 := by simp [hx]
  have hmin : minpoly ℚ x = X ^ 2 - C (a : ℚ) :=
    (minpoly.eq_of_irreducible_of_monic hirr hev hmon).symm
  have := IntermediateField.adjoin.finrank (K := ℚ) (x := x) (.of_finite ℚ x)
  rw [hmin, natDegree_X_pow_sub_C _, hadj, IntermediateField.finrank_top'] at this
  exact this

theorem adjoin_gen_eq_top_rat {E : Type} [Field E] [NumberField E] (y : E) :
    IntermediateField.adjoin ℚ {IntermediateField.AdjoinSimple.gen ℚ y} = ⊤ := by
  apply IntermediateField.lift_injective
  exact (IntermediateField.lift_adjoin_simple ℚ _ (IntermediateField.AdjoinSimple.gen ℚ y)).trans
    (IntermediateField.lift_top ℚ (IntermediateField.adjoin ℚ {y})).symm

theorem rootDiscr_and_different_quadField :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E),
      rootDiscr (AdelicDegreeTameRamification.quadField H) = √(H.d : ℝ) ∧
      (differentIdeal ℤ (𝓞 (AdelicDegreeTameRamification.quadField H))).map (algebraMap (𝓞 (AdelicDegreeTameRamification.quadField H)) (𝓞 E)) =
        Ideal.span {H.rt} := by
  intro E _ _ _ H
  have hd16 := H.d_mod
  have hb2 : ((H.rt : 𝓞 E) : E) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  obtain ⟨x, hxdef, hadj⟩ : ∃ x : AdelicDegreeTameRamification.quadField H, (x : E) = (H.rt : E) ∧
      IntermediateField.adjoin ℚ {x} = ⊤ :=
    ⟨IntermediateField.AdjoinSimple.gen ℚ _, rfl, adjoin_gen_eq_top_rat _⟩
  have hx : x ^ 2 = ((-(H.d : ℤ) : ℤ) : AdelicDegreeTameRamification.quadField H) := by
    apply Subtype.ext
    push_cast
    rw [hxdef, hb2]
  have hint : IsIntegral ℤ x := by
    apply IsIntegral.of_pow (n := 2) (by norm_num)
    rw [hx, ← eq_intCast (algebraMap ℤ (AdelicDegreeTameRamification.quadField H))]
    exact isIntegral_algebraMap
  have hsf : Squarefree (-(H.d : ℤ)) := by
    rw [← Int.squarefree_natAbs, Int.natAbs_neg, Int.natAbs_natCast]
    exact H.d_prime.squarefree
  obtain ⟨x', hx'⟩ : ∃ x' : 𝓞 (AdelicDegreeTameRamification.quadField H), (x' : AdelicDegreeTameRamification.quadField H) = x := ⟨⟨x, hint⟩, rfl⟩
  have hdiff := Formalism.MainNotions.UnusedSlot33.HK.different_quad (AdelicDegreeTameRamification.quadField H) (-(H.d : ℤ)) x hx hadj hsf
    (by omega) (by omega) x' hx'
  have h2 := finrank_eq_two_of_adjoin_sqrt_eq_top (AdelicDegreeTameRamification.quadField H) (-(H.d : ℤ)) x hx hadj hsf (by omega)
  have hD := Formalism.HF.P.quadDiscr_ne_one (AdelicDegreeTameRamification.quadField H) (-(H.d : ℤ)) x hx hadj hsf (by omega) (by omega)
  refine ⟨?_, ?_⟩
  · rw [rootDiscr_def, h2, hD, Real.sqrt_eq_rpow]
    simp
  · rw [hdiff, Ideal.map_span, Set.image_singleton]
    congr 2
    apply RingOfIntegers.coe_injective
    show ((x' : AdelicDegreeTameRamification.quadField H) : E) = _
    rw [hx', hxdef]

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps (torus lieMap lieAdd LieCongr IsLieLinear lieCoord)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ClosedImmFieldDescent

set_option backward.isDefEq.respectTransparency.types false

theorem isClosedImmersion_descendsAlong_fpqc :
    MorphismProperty.DescendsAlong (@IsClosedImmersion : MorphismProperty Scheme.{0})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  have := GlobalTheory.isAffineHom_descendsAlong_fpqc.{0}
  have hP : HasAffineProperty @IsClosedImmersion (affineAnd fun f ↦ Function.Surjective f) :=
    IsClosedImmersion.hasAffineProperty
  have H₂ : ∀ {R S : CommRingCat.{0}} {f : R ⟶ S}, (@Surjective ⊓ @Flat) (Spec.map f) →
      RingHom.FaithfullyFlat f.hom := by
    intro R S f ⟨hf₁, hf₂⟩
    rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
    refine ⟨?_, (Spec.map f).surjective⟩
    rwa [HasRingHomProperty.Spec_iff (P := @Flat)] at hf₂
  refine IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact _ _ ?_ ?_
  · rw [inf_comm]
    exact inf_le_inf le_rfl (IsLocalIso.le_of_isZariskiLocalAtSource _)
  intro R S Y φ g h hf
  have : IsAffine Y := by
    have : IsAffineHom g := MorphismProperty.of_pullback_fst_of_descendsAlong
      (P := @IsAffineHom) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) ⟨h, inferInstance⟩
      (HasAffineProperty.affineAnd_le_isAffineHom @IsClosedImmersion hP _ hf)
    exact isAffine_of_isAffineHom g
  wlog hY : ∃ S, Y = Spec S generalizing Y
  · rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion) Y.isoSpec.inv]
    have heq : pullback.fst (Spec.map φ) (Y.isoSpec.inv ≫ g) =
        pullback.map _ _ _ _ (𝟙 _) (Y.isoSpec.inv) (𝟙 _) (by simp) (by simp) ≫
          pullback.fst (Spec.map φ) g := (pullback.lift_fst _ _ _).symm
    refine this _ ?_ inferInstance ⟨_, rfl⟩
    rwa [heq, MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)]
  obtain ⟨Y, rfl⟩ := hY
  apply of_pullback_fst_Spec_of_codescendsAlong _ _ RingHom.FaithfullyFlat.codescendsAlong_surjective H₂ _ h hf
  intro R' S' f'
  exact HasAffineProperty.SpecMap_iff_of_affineAnd hP RingHom.surjective_respectsIso f'

theorem isPullback_baseChange_step {R k Ω : Type} [CommRing R] [Field k] [Field Ω] [Algebra R k]
    [Algebra k Ω] [Algebra R Ω] [IsScalarTower R k Ω] {C : Scheme.{0}} (c : C ⟶ Spec (CommRingCat.of R)) :
    IsPullback (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap R Ω))))
      (pullback.map c (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) c (Spec.map (CommRingCat.ofHom (algebraMap R k)))
        (𝟙 C) (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) (𝟙 _) (by simp)
        (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]))
      (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))
      (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap R k)))) := by
  have e : Spec.map (CommRingCat.ofHom (algebraMap k Ω)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R k)) =
      Spec.map (CommRingCat.ofHom (algebraMap R Ω)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  refine IsPullback.of_bot ?_ (pullback.lift_snd _ _ _).symm (IsPullback.of_hasPullback c _).flip
  have h0 := (IsPullback.of_hasPullback c (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).flip
  rw [pullback.lift_fst, Category.comp_id, e]
  exact h0

theorem fpqc_specMap_field (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] :
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) := by
  refine ⟨⟨⟨fun x ↦ ?_⟩, ?_⟩, inferInstance⟩
  · obtain ⟨y⟩ : Nonempty (Spec (CommRingCat.of Ω)) := inferInstanceAs (Nonempty (PrimeSpectrum Ω))
    exact ⟨y, Subsingleton.elim (α := PrimeSpectrum k) _ _⟩
  · rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance

theorem isClosedImmersion_of_baseChange_extension :
    ∀ (R k Ω : Type) [CommRing R] [Field k] [Field Ω] [Algebra R k] [Algebra k Ω] [Algebra R Ω] [IsScalarTower R k Ω] (V W : Over (Spec (CommRingCat.of R))) (f : V ⟶ W), IsClosedImmersion ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R Ω).map f).left → IsClosedImmersion ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R k).map f).left := by
  intro R k Ω _ _ _ _ _ _ _ V W f hΩ
  have hd := isClosedImmersion_descendsAlong_fpqc
  have e : (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R k))) = (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  let vX := pullback.map V.hom (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) V.hom (Spec.map (CommRingCat.ofHom (algebraMap R k))) (𝟙 _) (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) (𝟙 _) (by simp) (by rw [Category.comp_id, e])
  let vY := pullback.map W.hom (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) W.hom (Spec.map (CommRingCat.ofHom (algebraMap R k))) (𝟙 _) (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) (𝟙 _) (by simp) (by rw [Category.comp_id, e])
  have sX : IsPullback (pullback.snd V.hom (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))) vX (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) (pullback.snd V.hom (Spec.map (CommRingCat.ofHom (algebraMap R k)))) :=
    isPullback_baseChange_step (k := k) (Ω := Ω) V.hom
  have sY : IsPullback (pullback.snd W.hom (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))) vY (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) (pullback.snd W.hom (Spec.map (CommRingCat.ofHom (algebraMap R k)))) :=
    isPullback_baseChange_step (k := k) (Ω := Ω) W.hom
  let φk := ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R k).map f).left
  let φΩ := ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R Ω).map f).left
  have hk2 : φk ≫ pullback.snd W.hom (Spec.map (CommRingCat.ofHom (algebraMap R k))) = pullback.snd V.hom (Spec.map (CommRingCat.ofHom (algebraMap R k))) := by simp only [φk, Over.pullback_map_left, pullback.lift_fst, pullback.lift_snd, Category.comp_id, Category.assoc]
  have hk1 : φk ≫ pullback.fst W.hom (Spec.map (CommRingCat.ofHom (algebraMap R k))) = pullback.fst V.hom (Spec.map (CommRingCat.ofHom (algebraMap R k))) ≫ f.left := by simp only [φk, Over.pullback_map_left, pullback.lift_fst, pullback.lift_snd, Category.comp_id, Category.assoc]
  have hΩ2 : φΩ ≫ pullback.snd W.hom (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) = pullback.snd V.hom (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) := by simp only [φΩ, Over.pullback_map_left, pullback.lift_fst, pullback.lift_snd, Category.comp_id, Category.assoc]
  have hΩ1 : φΩ ≫ pullback.fst W.hom (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) = pullback.fst V.hom (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ≫ f.left := by simp only [φΩ, Over.pullback_map_left, pullback.lift_fst, pullback.lift_snd, Category.comp_id, Category.assoc]
  have comm : φΩ ≫ vY = vX ≫ φk := by
    apply pullback.hom_ext
    · simp only [vX, vY, Category.assoc, hk1, pullback.lift_fst, pullback.lift_fst_assoc, Category.comp_id]
      exact hΩ1
    · simp only [vX, vY, Category.assoc, hk2, pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]
      rw [← Category.assoc, hΩ2]
  have sq : IsPullback φΩ vX vY φk := by
    refine IsPullback.of_right ?_ comm sY
    rw [hΩ2, hk2]
    exact sX
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := @IsClosedImmersion)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) sq
    (MorphismProperty.of_isPullback (P := @Surjective ⊓ @Flat ⊓ @QuasiCompact) sY (fpqc_specMap_field k Ω)) hΩ

end GlobalTheory.ClosedImmFieldDescent
end
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

theorem _root_.GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_primary_eq : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (s : F[X] → ℂ), IsAdditive s → ∀ (g : Module.End F V) (f : F[X]) (m t : ℕ), f.Monic → Irreducible f → 0 < m → LinearMap.charpoly g = f ^ m → Module.finrank F (LinearMap.ker (aeval g f)) = f.natDegree * t → psi s V g = s f * ∏ i ∈ Finset.Ico 1 t, (1 - (Nat.card F : ℂ) ^ (f.natDegree * i)) := by
  first | exact @GlobalTheory.CuspGL.psi_primary | exact GlobalTheory.CuspGL.psi_primary | (intros; apply GlobalTheory.CuspGL.psi_primary <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.levelOne_modularForm_value_galois_transport : ∀ (g : ℂ ≃+* ℂ) (w N : ℕ) (F F' : ℍ → ℂ) (τ₀ τ₁ : ℍ) (ω₀ ω₁ : ℂ), 0 < N → (∀ γ : SL(2, ℤ), F ∣[(w : ℤ)] γ = F) → QConj g N F F' → g (E₄ τ₀ / ω₀ ^ 4) = E₄ τ₁ / ω₁ ^ 4 → g (E₆ τ₀ / ω₀ ^ 6) = E₆ τ₁ / ω₁ ^ 6 → g (F τ₀ / ω₀ ^ w) = F' τ₁ / ω₁ ^ w := by
  first | exact @GlobalTheory.QFam.levelOne_value_transport | exact GlobalTheory.QFam.levelOne_value_transport | (intros; apply GlobalTheory.QFam.levelOne_value_transport <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.esymm_pow_twelve_div_discriminant_mem_subring : ∀ (ι : Type) [Fintype ι] (act : ι → SL(2, ℤ) → ι) (w N : ℕ) (f : ι → ℍ → ℂ) (R : Subring ℂ) (τ₀ : ℍ), 0 < N → ActBij act → IsFam act w f → (∀ i, QAll (· ∈ R) N (f i)) → jT τ₀ ∈ R → ∀ k : ℕ, (∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, f i τ₀ ^ 12 / DD τ₀ ^ w) ∈ R := by
  first | exact @GlobalTheory.QFam.esymm_pow_twelve_div_mem | exact GlobalTheory.QFam.esymm_pow_twelve_div_mem | (intros; apply GlobalTheory.QFam.esymm_pow_twelve_div_mem <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

open Polynomial SemidirectProduct in
open scoped Classical in
private lemma isCl_apply_eq_of_isConj {G : Type} [Group G] {f : G → ℂ}
    (hf : _root_.GlobalTheory.Shin.IsCl f) {a b : G} (h : IsConj a b) : f a = f b := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp h
  have := hf a c⁻¹
  rw [inv_inv] at this
  exact this.symm


open Polynomial SemidirectProduct in
open scoped Classical in
theorem _root_.GlobalTheory.Shin.shLift_isNorm_and_twisted_inv : ∀ (F F' : Type) [Field F] [Field F']
    [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) →
    ∀ (n : ℕ) (f : GL (Fin n) F → ℂ), _root_.GlobalTheory.Shin.IsCl f →
    (∀ δ γ, _root_.GlobalTheory.Shin.IsNorm s δ γ → _root_.GlobalTheory.Shin.shLift s f δ = f γ) ∧
    ∀ δ y : GL (Fin n) F', _root_.GlobalTheory.Shin.shLift s f
      (y⁻¹ * δ * _root_.GlobalTheory.Shin.galAct F F' n s y) = _root_.GlobalTheory.Shin.shLift s f δ := by
  intro F F' _ _ _ _ s hs n f hf
  have hconj := (_root_.GlobalTheory.Shin.NrmBasic.main F F' s hs n).2.2.1
  refine ⟨fun δ γ hδ => ?_, fun δ y => ?_⟩
  · unfold _root_.GlobalTheory.Shin.IsNorm at hδ
    unfold _root_.GlobalTheory.Shin.shLift
    have hex : ∃ γ, _root_.GlobalTheory.Shin.IsNorm s δ γ := ⟨γ, hδ⟩
    rw [dite_eq_left hex]
    have hspec : IsConj (_root_.GlobalTheory.Shin.incl F F' n hex.choose) (_root_.GlobalTheory.Shin.nrm s δ) :=
      hex.choose_spec
    exact isCl_apply_eq_of_isConj hf
      (_root_.GlobalTheory.Shin.isConj_of_isConj_incl F F' n _ _ (hspec.trans hδ.symm))
  · have hN : IsConj (_root_.GlobalTheory.Shin.nrm s δ)
        (_root_.GlobalTheory.Shin.nrm s (y⁻¹ * δ * _root_.GlobalTheory.Shin.galAct F F' n s y)) := by
      rw [hconj δ y, isConj_iff]
      exact ⟨y⁻¹, by rw [inv_inv]⟩
    unfold _root_.GlobalTheory.Shin.shLift
    by_cases hex : ∃ γ, _root_.GlobalTheory.Shin.IsNorm s δ γ
    · have hspec : IsConj (_root_.GlobalTheory.Shin.incl F F' n hex.choose) (_root_.GlobalTheory.Shin.nrm s δ) :=
        hex.choose_spec
      have hex' : ∃ γ, _root_.GlobalTheory.Shin.IsNorm s (y⁻¹ * δ * _root_.GlobalTheory.Shin.galAct F F' n s y) γ :=
        ⟨hex.choose, hspec.trans hN⟩
      have hspec' : IsConj (_root_.GlobalTheory.Shin.incl F F' n hex'.choose)
          (_root_.GlobalTheory.Shin.nrm s (y⁻¹ * δ * _root_.GlobalTheory.Shin.galAct F F' n s y)) :=
        hex'.choose_spec
      rw [dite_eq_left hex, dite_eq_left hex']
      exact isCl_apply_eq_of_isConj hf
        (_root_.GlobalTheory.Shin.isConj_of_isConj_incl F F' n _ _
          (hspec'.trans (hspec.trans hN).symm))
    · have hex' : ¬ ∃ γ, _root_.GlobalTheory.Shin.IsNorm s (y⁻¹ * δ * _root_.GlobalTheory.Shin.galAct F F' n s y) γ :=
        fun ⟨γ, hγ⟩ => hex ⟨γ, (show IsConj (_root_.GlobalTheory.Shin.incl F F' n γ) _ from hγ).trans hN.symm⟩
      rw [dite_eq_right hex, dite_eq_right hex']

end GlobalTheory.Shin
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

theorem _root_.GlobalTheory.T.eq_of_weierstrassP_derivWeierstrassP_torsion_eq : ∀ (N : ℕ) [NeZero N] (τ : ℍ) (x y : Fin 2 → ZMod N), x ≠ 0 → y ≠ 0 → wp N x τ = wp N y τ → wpd N x τ = wpd N y τ → x = y := by
  first | exact @GlobalTheory.WpFam.wp_wpd_separate | exact GlobalTheory.WpFam.wp_wpd_separate | (intros; apply GlobalTheory.WpFam.wp_wpd_separate <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.harishChandraProductCuspidalGL_list_properties : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ L n, IsCl (J θ L n)) ∧ (∀ (L L' : List (ℕ × ℕ)) (n : ℕ), n = deg L + deg L' → J θ (L ++ L') n = hc (deg L) (deg L') (J θ L (deg L)) (J θ L' (deg L')) n) ∧ ∀ (L L' : List (ℕ × ℕ)) (n : ℕ), n = deg L → L.Perm L' → J θ L n = J θ L' n := by
  first | (exact @GlobalTheory.Shin.J_list_props) | (exact GlobalTheory.Shin.J_list_props) | (intros; apply GlobalTheory.Shin.J_list_props <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.isConj_of_isConj_glFieldExtensionInclusion : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (n : ℕ) (γ γ' : GL (Fin n) F), IsConj (incl F F' n γ) (incl F F' n γ') → IsConj γ γ' := by
  first | (exact @GlobalTheory.Shin.isConj_of_isConj_incl) | (exact GlobalTheory.Shin.isConj_of_isConj_incl) | (intros; apply GlobalTheory.Shin.isConj_of_isConj_incl <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.pairing_cuspidalCharacterGL_rootPowerSumCharacter : ∀ (F : Type) [Field F] [Finite F], ∀ (θ : AlgebraicClosure F →* ℂ) (m : ℕ) (e : ℕ → ℕ) (ε : ℤ), (∀ i, ∑ᶠ x, cusp θ m (e i) x = 0) → ∀ N : ℕ, (∀ i j, i < N → j < N → ∑ᶠ x, cusp θ m (e i) x * star (chG (rootSum θ (e j)) m x) = if i = j then (ε : ℂ) * (Nat.card (GL (Fin m) F) : ℂ) else 0) → ∀ (L : List ℕ) (T : Finset ℕ), L.Nodup → (∀ i ∈ L, i < N) → (∀ j ∈ T, j < N) → T.card ≤ L.length → ∀ n, n = m * L.length → ∑ᶠ x, J θ (L.map fun i => (m, e i)) n x * star (chG (fun P => ∏ j ∈ T, rootSum θ (e j) P) n x) = if T = L.toFinset then (ε : ℂ) ^ L.length * (Nat.card (GL (Fin n) F) : ℂ) else 0 := by
  first | (exact @GlobalTheory.Shin.pair_J_prod_rootSum) | (exact GlobalTheory.Shin.pair_J_prod_rootSum) | (intros; apply GlobalTheory.Shin.pair_J_prod_rootSum <;> assumption)
end

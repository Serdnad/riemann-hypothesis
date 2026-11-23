module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle018
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Free
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle023
public import Mathlib.RingTheory.Localization.Away.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle161
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle159
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle164
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle039
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle163
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle147
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Polynomial.IsIntegral
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace GlobalTheory.NormSheaf.IntegralCoeff

open MvPolynomial
open scoped TensorProduct

theorem leftMulMatrix_sum_tmul (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] {m : ℕ}
    (x : Fin m → L) :
    Algebra.leftMulMatrix (Algebra.TensorProduct.basis (MvPolynomial (Fin m) K) (Module.finBasis K L))
      (∑ i, (X i : MvPolynomial (Fin m) K) ⊗ₜ[K] x i) =
    ∑ i, (X i : MvPolynomial (Fin m) K) •
      (Algebra.leftMulMatrix (Module.finBasis K L) (x i)).map (C : K →+* MvPolynomial (Fin m) K) := by

  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ext a c
  simp [Algebra.leftMulMatrix_eq_repr_mul, Algebra.TensorProduct.basis_repr_tmul,
    Algebra.TensorProduct.basis_apply]

theorem isIntegral_det_of_aeval {R' F : Type} [CommRing R'] [Field F] [Algebra R' F] {n : Type} [Fintype n]
    [DecidableEq n] (M : Matrix n n F) (g : Polynomial R') (hg : g.Monic)
    (h : Polynomial.aeval M (g.map (algebraMap R' F)) = 0) : IsIntegral R' M.det := by
  have hd := GlobalTheory.CharpolyDvd.matrix_charpoly_dvd_pow M _ h
  rw [← Polynomial.map_pow] at hd
  have hc := Polynomial.isIntegral_coeff_of_dvd (g ^ Fintype.card n) M.charpoly (hg.pow _) M.charpoly_monic hd 0
  rw [Matrix.det_eq_sign_charpoly_coeff]
  exact (isIntegral_one.neg.pow _).mul hc

end GlobalTheory.NormSheaf.IntegralCoeff

namespace GlobalTheory.NormSheaf.IntegralCoeff

open MvPolynomial
open scoped TensorProduct

theorem isIntegral_normForm (A K L : Type) [CommRing A] [Field K] [Field L] [Algebra A K]
    [Algebra K L] [FiniteDimensional K L] [Algebra A L] [IsScalarTower A K L] {m : ℕ}
    (x : Fin m → L) (hx : ∀ i, IsIntegral A (x i)) :
    @IsIntegral (MvPolynomial (Fin m) A) (MvPolynomial (Fin m) K) _ _
      MvPolynomial.algebraMvPolynomial (GlobalTheory.NormSheaf.normForm K L x) := by
  classical
  letI : Algebra (MvPolynomial (Fin m) A) (MvPolynomial (Fin m) K) := MvPolynomial.algebraMvPolynomial
  set R := MvPolynomial (Fin m) K
  set R' := MvPolynomial (Fin m) A
  let F := FractionRing R
  haveI : IsScalarTower R' R F := inferInstance
  let S := R ⊗[K] L
  letI : Algebra R' S := ((algebraMap R S).comp (algebraMap R' R)).toAlgebra
  let y : S := ∑ i, (X i : R) ⊗ₜ[K] x i
  have hy : IsIntegral R' y := by
    refine IsIntegral.sum _ fun i _ => ?_
    have e : (X i : R) ⊗ₜ[K] x i = algebraMap R' S (X i) * (1 ⊗ₜ[K] x i) := by
      have hX : algebraMap R' R (X i) = X i := MvPolynomial.map_X _ _
      change _ = algebraMap R S (algebraMap R' R (X i)) * _
      rw [hX]
      change _ = ((X i : R) ⊗ₜ[K] (1 : L)) * (1 ⊗ₜ[K] x i)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e]
    refine isIntegral_algebraMap.mul ?_
    refine IsIntegral.map_of_comp_eq (algebraMap A R')
      (Algebra.TensorProduct.includeRight : L →ₐ[K] S).toRingHom ?_ (hx i)
    refine RingHom.ext fun a => ?_
    change (algebraMap R' R (algebraMap A R' a)) ⊗ₜ[K] (1 : L) = (1 : R) ⊗ₜ[K] algebraMap A L a
    have h1 : algebraMap R' R (algebraMap A R' a) = algebraMap K R (algebraMap A K a) := by
      change MvPolynomial.map (algebraMap A K) (C a) = C (algebraMap A K a)
      exact MvPolynomial.map_C _ _
    rw [h1, IsScalarTower.algebraMap_apply A K L, Algebra.algebraMap_eq_smul_one (A := R) (algebraMap A K a),
      Algebra.algebraMap_eq_smul_one (A := L) (algebraMap A K a), TensorProduct.smul_tmul]
  obtain ⟨g, hgm, hgy⟩ := hy
  let bS := Algebra.TensorProduct.basis R (Module.finBasis K L)
  let φ : S →ₐ[R] Matrix (Fin (Module.finrank K L)) (Fin (Module.finrank K L)) F :=
    (AlgHom.mapMatrix (Algebra.ofId R F)).comp (Algebra.leftMulMatrix bS)
  have hM : φ y = (algebraMap R F).mapMatrix
      (∑ i, (X i : R) • (Algebra.leftMulMatrix (Module.finBasis K L) (x i)).map (C : K →+* R)) := by
    rw [← leftMulMatrix_sum_tmul K L x]
    rfl
  have h0 : Polynomial.aeval (φ y) (g.map (algebraMap R' F)) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    have hh : (algebraMap F (Matrix (Fin (Module.finrank K L)) (Fin (Module.finrank K L)) F)).comp (algebraMap R' F)
        = φ.toRingHom.comp (algebraMap R' S) := by
      refine RingHom.ext fun r => ?_
      change algebraMap F _ (algebraMap R' F r) = φ (algebraMap R S (algebraMap R' R r))
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R' R F]
      exact (IsScalarTower.algebraMap_apply R F _ _).symm
    rw [hh]
    have h2 := Polynomial.hom_eval₂ g (algebraMap R' S) φ.toRingHom y
    rw [hgy, map_zero] at h2
    exact h2.symm
  have hdet := isIntegral_det_of_aeval _ g hgm h0
  rw [hM, ← RingHom.map_det] at hdet
  exact (isIntegral_algebraMap_iff ).mp hdet

end GlobalTheory.NormSheaf.IntegralCoeff

namespace GlobalTheory.NormSheaf.IntegralCoeff

theorem coeff_normForm_mem_range : ∀ (A K L : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [FiniteDimensional K L] [Algebra A L] [IsScalarTower A K L] {m : ℕ}
    (x : Fin m → L), (∀ i, IsIntegral A (x i)) →
    ∀ s, (GlobalTheory.NormSheaf.normForm K L x).coeff s ∈ (algebraMap A K).range := by
  intro A K L _ _ _ _ _ _ _ _ _ _ _ m x hx s
  letI : Algebra (MvPolynomial (Fin m) A) (MvPolynomial (Fin m) K) := MvPolynomial.algebraMvPolynomial
  have key := isIntegral_normForm A K L x hx
  have hc := MvPolynomial.isIntegral_iff_isIntegral_coeff.mp key s
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hc
  exact ⟨a, ha⟩

end GlobalTheory.NormSheaf.IntegralCoeff
end
end

section

open AlgebraicGeometry CategoryTheory Limits

theorem _root_.GlobalTheory.T.normFormCoefficientIdeal_map_localizationAway : ∀ (A K L B A' B' : Type) [CommRing A] [CommRing B] [CommRing A'] [CommRing B'] [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [Algebra A K] [Algebra B L] [Algebra A' K] [Algebra B' L]
    [Algebra A A'] [Algebra B B'] [Algebra A B] (f : A) [IsLocalization.Away f A']
    [IsLocalization.Away (algebraMap A B f) B'],
    (algebraMap A' K).comp (algebraMap A A') = algebraMap A K →
    (algebraMap B' L).comp (algebraMap B B') = algebraMap B L →
    (algebraMap K L).comp (algebraMap A K) = (algebraMap B L).comp (algebraMap A B) →
    Function.Injective (algebraMap A' K) →
    (∀ {m : ℕ} (g : Fin m → B) s,
      (GlobalTheory.NormSheaf.normForm K L (fun i => algebraMap B L (g i))).coeff s ∈ (algebraMap A K).range) →
    ∀ J : Ideal B, (GlobalTheory.NormSheaf.normIdeal A K L B J).map (algebraMap A A') =
      GlobalTheory.NormSheaf.normIdeal A' K L B' (J.map (algebraMap B B')) := by
  first | exact @GlobalTheory.NormSheaf.normIdeal_map_away | exact GlobalTheory.NormSheaf.normIdeal_map_away | (intros; apply GlobalTheory.NormSheaf.normIdeal_map_away <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem _root_.GlobalTheory.T.ferrandPush_res_surjective_and_isNilpotent_ker : ∀ {Y₀ Y₁ : Scheme.{0}} (i : Y₀ ⟶ Y₁) [IsClosedImmersion i] [Surjective i], (∀ U : Y₁.Opens, IsAffineOpen U → IsNilpotent (RingHom.ker (i.app U).hom)) → ∀ U : Y₀.Opens, IsAffineOpen (GlobalTheory.FerrandPush.upOpen i U) → Function.Surjective (GlobalTheory.FerrandPush.res i U).hom ∧ IsNilpotent (RingHom.ker (GlobalTheory.FerrandPush.res i U).hom) := by
  first | exact @GlobalTheory.FerrandPush.res_surjective_nilpotent_ker | exact GlobalTheory.FerrandPush.res_surjective_nilpotent_ker | (intros; apply GlobalTheory.FerrandPush.res_surjective_nilpotent_ker <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem _root_.GlobalTheory.T.isLocalization_away_ferrandPush_fib : ∀ {Y₀ Y₁ Y₂ : Scheme.{0}} (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂) [IsClosedImmersion i₁] [Surjective i₁] [IsClosedImmersion i₂] [Surjective i₂], ∀ U ∈ GlobalTheory.FerrandPush.good i₁ i₂, ∀ a : (GlobalTheory.FerrandPush.fib i₁ i₂).obj (op U), letI := ((GlobalTheory.FerrandPush.fib i₁ i₂).map (homOfLE (Y₀.basicOpen_le (((GlobalTheory.FerrandPush.fibπ i₁ i₂).app (op U)).hom a))).op).hom.toAlgebra; IsLocalization.Away a ((GlobalTheory.FerrandPush.fib i₁ i₂).obj (op (Y₀.basicOpen (((GlobalTheory.FerrandPush.fibπ i₁ i₂).app (op U)).hom a)))) := by
  first | exact @GlobalTheory.FerrandPush.isLocalization_away_fib | exact GlobalTheory.FerrandPush.isLocalization_away_fib | (intros; apply GlobalTheory.FerrandPush.isLocalization_away_fib; all_goals assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem _root_.GlobalTheory.T.ferrand_pushout_good_basic_open : ∀ {Y₀ Y₁ Y₂ : Scheme.{0}} (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂) [IsClosedImmersion i₁] [Surjective i₁] [IsClosedImmersion i₂] [Surjective i₂], ∀ U ∈ GlobalTheory.FerrandPush.good i₁ i₂, ∀ a : (GlobalTheory.FerrandPush.fib i₁ i₂).obj (op U), Y₀.basicOpen (((GlobalTheory.FerrandPush.fibπ i₁ i₂).app (op U)).hom a) ∈ GlobalTheory.FerrandPush.good i₁ i₂ := by
  first | exact @GlobalTheory.FerrandPush.basicOpen_fibπ_mem_good | exact GlobalTheory.FerrandPush.basicOpen_fibπ_mem_good | (intros; apply GlobalTheory.FerrandPush.basicOpen_fibπ_mem_good; all_goals assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch GlobalTheory.HilbGlue

theorem _root_.GlobalTheory.T.hilbertFunctor_local_representing_data_of_restrict : ∀ {S Z : Scheme.{0}} (z : Z ⟶ S) (r : ℕ) (W : S.Opens), GlobalTheory.HilbertSch.IsHilbRep (z ∣_ W) r → ∃ (T : Scheme.{0}) (y : GlobalTheory.HilbGlue.HPt z r T) (π : T ⟶ W.toScheme), IsProper π ∧ y.1 = π ≫ W.ι ∧ ∀ (Y : Scheme.{0}) (x : GlobalTheory.HilbGlue.HPt z r Y) (b : Y ⟶ W.toScheme), x.1 = b ≫ W.ι → ∃! c : Y ⟶ T, GlobalTheory.HilbGlue.HPt.map c y = x := by
  first | exact @GlobalTheory.HilbGlue.isHilbRep_restrict_local | exact GlobalTheory.HilbGlue.isHilbRep_restrict_local | (intros; apply GlobalTheory.HilbGlue.isHilbRep_restrict_local <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch

theorem _root_.GlobalTheory.T.isHilbertSchemeRepresentable_of_iso : ∀ {S Z S' Z' : Scheme.{0}} (z : Z ⟶ S) (z' : Z' ⟶ S') (eS : S' ≅ S) (eZ : Z' ≅ Z), eZ.hom ≫ z = z' ≫ eS.hom → ∀ r : ℕ, IsHilbRep z' r → IsHilbRep z r := by
  first | exact @GlobalTheory.HilbertSch.isHilbRep_transfer | exact GlobalTheory.HilbertSch.isHilbRep_transfer | (intros; apply GlobalTheory.HilbertSch.isHilbRep_transfer <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.AlgConn

theorem _root_.GlobalTheory.T.exists_hom_specProdSelf_preimage_eq_clopen : ∀ (O : Type) [CommRing O] (T : Scheme.{0}) (p : T ⟶ Spec (.of O)) (U : Set T), IsClopen U → ∃ h : T ⟶ Spec (.of (O × O)), h ≫ twoπ O = p ∧ ((h ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) : T.Opens) : Set T) = U := by
  first | exact @GlobalTheory.exists_hom_spec_prod_self_preimage_eq_clopen | exact GlobalTheory.exists_hom_spec_prod_self_preimage_eq_clopen | (intros; apply GlobalTheory.exists_hom_spec_prod_self_preimage_eq_clopen <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.AlgConn

theorem _root_.GlobalTheory.T.hom_ext_specProdSelf_of_basicOpen_preimage_eq : ∀ (O : Type) [CommRing O] (T : Scheme.{0}) (h h' : T ⟶ Spec (.of (O × O))), h ≫ twoπ O = h' ≫ twoπ O → h ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) = h' ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) → h = h' := by
  first | exact @GlobalTheory.AlgConn.hom_ext_of_twoπ_of_basicOpen | exact GlobalTheory.AlgConn.hom_ext_of_twoπ_of_basicOpen | (intros; apply GlobalTheory.AlgConn.hom_ext_of_twoπ_of_basicOpen <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry

theorem _root_.GlobalTheory.T.pullback_square_sections_glue_of_basis : ∀ {X X' Z Z' : Scheme.{0}} (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z) (B : Set X.Opens), (∀ (W : X.Opens) (x : X), x ∈ W → ∃ W' ∈ B, x ∈ W' ∧ W' ≤ W) → (∀ W ∈ B, ∀ (a : Γ(X', p ⁻¹ᵁ W)) (b : Γ(Z, i ⁻¹ᵁ W)), (i'.appLE (p ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_left).hom a = (p'.appLE (i ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_right).hom b → ∃! s : Γ(X, W), (p.app W).hom s = a ∧ (i.app W).hom s = b) → GlobalTheory.PinchLift.Glues p i i' p' := by
  first | exact @GlobalTheory.PinchLift.glues_of_basis | exact GlobalTheory.PinchLift.glues_of_basis | (intros; apply GlobalTheory.PinchLift.glues_of_basis <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub

theorem _root_.GlobalTheory.T.mem_adjoin_restricted_sections_of_local : ∀ (X : Scheme.{0}) (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F), ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered → ∀ (V W : X.Opens) (T : Set (F.obj (op V))) (b : F.obj (op W)), (∀ x ∈ W ⊓ V, ∃ D : X.Opens, IsAffineOpen D ∧ x ∈ D ∧ ∃ (hW : D ≤ W) (hV : D ≤ V), (F.map (homOfLE hW).op).hom b ∈ gen F α hV T) → ∀ W' : X.Opens, IsAffineOpen W' → ∀ (hW : W' ≤ W) (hV : W' ≤ V), (F.map (homOfLE hW).op).hom b ∈ gen F α hV T := by
  first | exact @GlobalTheory.QcSub.Local.mem_gen_of_local | exact GlobalTheory.QcSub.Local.mem_gen_of_local | (intros; apply GlobalTheory.QcSub.Local.mem_gen_of_local <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub

theorem _root_.GlobalTheory.T.coequifibered_generated_subalgebra_quasiCoherent : ∀ (X : Scheme.{0}) (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F), ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered → ∀ {ι : Type} (V : ι → X.Opens) (T : ∀ j, Set (F.obj (op (V j)))), (∀ W : X.Opens, IsAffineOpen W → ∀ (f : Γ(X, W)) (a : F.obj (op W)), (F.map (homOfLE (X.basicOpen_le f)).op).hom a ∈ sub F α V T (X.basicOpen f) → ∃ m : ℕ, (α.app (op W)).hom f ^ m * a ∈ sub F α V T W) → (subNat F α V T).Coequifibered := by
  first | exact @GlobalTheory.QcSub.coequifibered_subNat | exact GlobalTheory.QcSub.coequifibered_subNat | (intros; apply GlobalTheory.QcSub.coequifibered_subNat <;> assumption)
end

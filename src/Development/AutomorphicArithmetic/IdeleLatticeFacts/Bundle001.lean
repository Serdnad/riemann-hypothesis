module

public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle002
public import Mathlib.LinearAlgebra.Determinant
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntAFSmulMemLatOF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle008
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutEtaA
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.GoodLat
import Formalism.LocalToGlobal.IndefiniteReal.DatumF
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
open PositivityTheory.ThKW PositivityTheory.ThKW.AutEtaA
open UpperTheory.TP.W

theorem UpperTheory.eq_zero_of_splitIdempotent_eval_place_eq_zero :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
        IsCMExt F E σ → ∀ e, IsSplitIdemF σ e → ∀ P : HeightOneSpectrum (𝓞 E), (∀ Q, Q ≠ P → ev F E Q e = 0) →
        ∀ a : AEF F E, e * a = a → ev F E P a = 0 → a = 0 := by
  intro F E _ _ _ _ _ σ hσ e he P hP a hea haP
  obtain ⟨hee, hec, v, ε, hε, hsum⟩ := he
  obtain ⟨α, rfl, -, -⟩ := hε
  have h1 : e * algebraMap (AF F) (AEF F E) (pairA F 0 α) = e := by
    rw [← hsum, mul_add, hee, hec, add_zero]
  have h2 : a = algebraMap (AF F) (AEF F E) (pairA F 0 α) * a := by
    calc a = e * a := hea.symm
      _ = (e * algebraMap (AF F) (AEF F E) (pairA F 0 α)) * a := by rw [h1]
      _ = _ := by rw [mul_comm e, mul_assoc, hea]
  have h3 : ∀ Q, ev F E Q a = 0 := by
    intro Q
    by_cases hQ : Q = P
    · subst hQ
      exact haP
    · rw [← hea, map_mul, hP Q hQ, zero_mul]
  have h4 : finPartF F E a = 0 := by
    apply (finAdEquiv F E).injective
    rw [map_zero]
    apply RestrictedProduct.ext
    intro Q
    exact h3 Q
  let g : Af F →ₗ[F] AF F := (LinearMap.inr F (Ainf F) (Af F) : Af F →ₗ[F] AF F) ∘ₗ LinearMap.mulLeft F α
  have h5 : ∀ b : AEF F E, algebraMap (AF F) (AEF F E) (pairA F 0 α) * b =
      TensorProduct.map g LinearMap.id (finPartF F E b) := by
    intro b
    induction b using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      show _ = TensorProduct.map g LinearMap.id ((sndA F x) ⊗ₜ[F] y)
      rw [TensorProduct.map_tmul]
      congr 1
      exact Prod.ext (zero_mul x.1) rfl
    | add x y hx hy => rw [mul_add, hx, hy, map_add (f := _), map_add (f := _)]
  rw [h2, h5, h4, map_zero]
end

section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
open PositivityTheory.ThKW PositivityTheory.ThKW.AutEtaA
open UpperTheory.TP.W

private theorem relIndex_map_of_injOn {G G' : Type} [AddGroup G] [AddGroup G'] (f : G →+ G') (R H K : AddSubgroup G)
    (hH : H ≤ R) (hK : K ≤ R) (hf : ∀ x ∈ R, f x = 0 → x = 0) :
    (H.map f).relIndex (K.map f) = H.relIndex K := by
  have hinj : Function.Injective (f.comp R.subtype) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    exact Subtype.ext (hf x x.2 hx)
  have h1 := AddSubgroup.relIndex_map_map_of_injective (H.addSubgroupOf R) (K.addSubgroupOf R) hinj
  have h2 := AddSubgroup.relIndex_map_map_of_injective (H.addSubgroupOf R) (K.addSubgroupOf R) R.subtype_injective
  rw [AddSubgroup.map_addSubgroupOf_eq_of_le hH, AddSubgroup.map_addSubgroupOf_eq_of_le hK] at h2
  rw [← AddSubgroup.map_map, ← AddSubgroup.map_map, AddSubgroup.map_addSubgroupOf_eq_of_le hH,
    AddSubgroup.map_addSubgroupOf_eq_of_le hK] at h1
  exact h1.trans h2.symm

theorem UpperTheory.lattice_determinant_comparison_at_split_place :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {nS nT : ℕ}
        (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (e : AEF F E), e * e = e →
        ∀ (P : HeightOneSpectrum (𝓞 E)), ev F E P e = 1 → (∀ a : AEF F E, e * a = a → ev F E P a = 0 → a = 0) →
        ∀ (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E))
          (L : Submodule (P.adicCompletionIntegers E) (Matrix (Fin nT) (Fin nS) (P.adicCompletion E))),
          (∀ v, v ∈ L ↔ ∃ x ∈ latF F E nS nT Λ, (x : WOF F E nS nT).map (ev F E P) = v) →
        ∀ (g : GAF σ JS) (h : GAF σ JT)
          (T : Matrix (Fin nT) (Fin nS) (P.adicCompletion E) →ₗ[P.adicCompletion E] Matrix (Fin nT) (Fin nS) (P.adicCompletion E)),
          (∀ u, T u = (mtF σ JT h).map (ev F E P) * u * (mtF σ JS g⁻¹).map (ev F E P)) →
          idx ((latF F E nS nT Λ).map (mulFF e)) (((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))).map (mulFF e)) =
            idx L (L.map (T.restrictScalars (P.adicCompletionIntegers E))) ∧
          idx (((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))).map (mulFF e)) ((latF F E nS nT Λ).map (mulFF e)) =
            idx (L.map (T.restrictScalars (P.adicCompletionIntegers E))) L := by
  intro F E _ _ _ _ _ σ nS nT JS JT e he P hev hinj Λ L hL g h T hT
  let φ : XFF F E nS nT →+ Matrix (Fin nT) (Fin nS) (P.adicCompletion E) :=
    AddMonoidHom.mk' (fun x => (x : WOF F E nS nT).map (ev F E P)) (fun x y => by
      rw [XFF.coe_add]
      ext i j
      simp [Matrix.map_apply, map_add (f := _)])
  have hφ : ∀ x, φ x = (x : WOF F E nS nT).map (ev F E P) := fun _ => rfl
  have hφe : ∀ x, φ (mulFF e x) = φ x := by
    intro x
    rw [hφ, hφ, coe_mulFF]
    ext i j
    simp [Matrix.map_apply, Matrix.smul_apply, map_mul, hev]
  have hφr : ∀ x, φ (rhoFF σ JS JT (g, h) x) = T (φ x) := by
    intro x
    rw [hT, hφ, hφ, coe_rhoFF]
    show ((mtF σ JT h * (x : WOF F E nS nT)) * mtF σ JS g⁻¹).map (ev F E P) = _
    rw [Matrix.map_mul, Matrix.map_mul]
  let R : AddSubgroup (XFF F E nS nT) :=
    (LinearMap.range (mulFF e : XFF F E nS nT →ₗ[𝓞 E] XFF F E nS nT)).toAddSubgroup
  have hR : ∀ x ∈ R, φ x = 0 → x = 0 := by
    rintro _ ⟨y, rfl⟩ h0
    apply XFF.ext
    rw [XFF.coe_zero]
    ext i j
    apply hinj
    · rw [coe_mulFF]
      simp [Matrix.smul_apply, ← mul_assoc, he]
    · exact congrFun (congrFun h0 i) j
  have hmapA : ((latF F E nS nT Λ).map (mulFF e)).toAddSubgroup.map φ = L.toAddSubgroup := by
    ext v
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, Submodule.mem_map]
    rw [hL]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, (hφe x).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, ⟨x, hx, rfl⟩, hφe x⟩
  have hmapB : (((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))).map (mulFF e)).toAddSubgroup.map φ =
      (L.map (T.restrictScalars (P.adicCompletionIntegers E))).toAddSubgroup := by
    ext v
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, Submodule.mem_map]
    constructor
    · rintro ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
      refine ⟨φ x, (hL _).2 ⟨x, hx, rfl⟩, ?_⟩
      show T (φ x) = _
      rw [hφe, hφr]
    · rintro ⟨_, hu, rfl⟩
      obtain ⟨x, hx, rfl⟩ := (hL _).1 hu
      refine ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, ?_⟩
      exact (hφe _).trans (hφr x)
  have hleA : ((latF F E nS nT Λ).map (mulFF e)).toAddSubgroup ≤ R := by
    rintro _ ⟨x, _, rfl⟩
    exact ⟨x, rfl⟩
  have hleB : (((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))).map (mulFF e)).toAddSubgroup ≤ R := by
    rintro _ ⟨x, _, rfl⟩
    exact ⟨x, rfl⟩
  constructor
  · unfold idx
    rw [← hmapA, ← hmapB]
    exact (relIndex_map_of_injOn φ R _ _ hleA hleB hR).symm
  · unfold idx
    rw [← hmapA, ← hmapB]
    exact (relIndex_map_of_injOn φ R _ _ hleB hleA hR).symm
end

section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
open PositivityTheory.ThKW PositivityTheory.ThKW.AutEtaA
open UpperTheory.TP.W

theorem UpperTheory.exists_linearMap_det_mul_mul_eq_pow :
    ∀ {K : Type} [Field K] {m n : ℕ} (H : Matrix (Fin m) (Fin m) K) (G : Matrix (Fin n) (Fin n) K),
        ∃ T : Matrix (Fin m) (Fin n) K →ₗ[K] Matrix (Fin m) (Fin n) K, (∀ u, T u = H * u * G) ∧
          LinearMap.det T = H.det ^ n * G.det ^ m := by
  intro K _ m n H G
  let T : Matrix (Fin m) (Fin n) K →ₗ[K] Matrix (Fin m) (Fin n) K :=
    { toFun := fun u => H * u * G
      map_add' := by
        intro u v
        simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := by
        intro c u
        simp [Matrix.mul_smul, Matrix.smul_mul] }
  refine ⟨T, fun u => rfl, ?_⟩
  have hrepr : ∀ (M : Matrix (Fin m) (Fin n) K) (i : Fin m) (j : Fin n),
      (Matrix.stdBasis K (Fin m) (Fin n)).repr M (i, j) = M i j := by
    intro M i j
    simp [Matrix.stdBasis]
  have hmat : LinearMap.toMatrix (Matrix.stdBasis K (Fin m) (Fin n)) (Matrix.stdBasis K (Fin m) (Fin n)) T
      = H ⊗ₖ Gᵀ := by
    ext ⟨i, j⟩ ⟨k, l⟩
    rw [LinearMap.toMatrix_apply, Matrix.stdBasis_eq_single, hrepr]
    simp [T, Matrix.kroneckerMap_apply, Matrix.mul_apply, Matrix.single_apply, ite_and,
      Finset.sum_ite_eq', Finset.sum_ite_eq, ite_mul]
  rw [← LinearMap.det_toMatrix (Matrix.stdBasis K (Fin m) (Fin n)), hmat, Matrix.det_kronecker,
    Matrix.det_transpose, Fintype.card_fin, Fintype.card_fin]
end

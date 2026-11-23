module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
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
public import Mathlib.RingTheory.Smooth.IntegralClosure
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

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.congrRad_of :
    CongrRad := by
  intro R _ 𝔞 h𝔞 ι N N' H B' _ g hg
  have key : ∀ (a : ℕ) (m : ι →₀ ℕ),
      AddMonoidAlgebra.coeff (N.coeff a) m - AddMonoidAlgebra.coeff (N'.coeff a) m ∈ 𝔞 := by
    intro a m
    rw [← h𝔞.radical, ← Ideal.sInf_minimalPrimes, Ideal.mem_sInf]
    intro 𝔭 h𝔭
    obtain ⟨κ, _, f, hker, hf⟩ := H 𝔭 h𝔭
    rw [← hker, RingHom.mem_ker, map_sub, sub_eq_zero]
    have := congrArg (fun p => AddMonoidAlgebra.coeff (p.coeff a) m) hf
    simpa [mapP, Polynomial.coeff_map, MvPolynomial.coeff_map] using this
  refine Polynomial.ext fun a => MvPolynomial.ext _ _ fun m => ?_
  simp only [mapP, Polynomial.coeff_map, MvPolynomial.coeff_map]
  rw [← sub_eq_zero, ← map_sub]
  exact hg _ (key a m)
end

section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.detSplit_of :
    DetSplit := by
  intro A _ m I _ _ P Q hPQ d
  have h1 : 1 - Q * P + Q * Matrix.diagonal d * P = 1 + Q * ((Matrix.diagonal d - 1) * P) := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, ← Matrix.mul_assoc]
    abel
  rw [h1, Matrix.det_one_add_mul_comm, Matrix.mul_assoc, hPQ, Matrix.mul_one, add_sub_cancel,
    Matrix.det_diagonal]
end

section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.liftingProperty :
    LiftP := by
  intro R T ι _ _ f N' h
  have hl : N' ∈ Polynomial.lifts (MvPolynomial.map (σ := ι) f) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro a
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro c hc
    obtain ⟨m, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hc
    exact h a m
  rw [Polynomial.lifts_iff_set_range] at hl
  obtain ⟨N, hN⟩ := hl
  exact ⟨N, hN⟩
end

section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.splitsEquiv_of :
    SplitsOfEquiv := by
  intro R S B _ _ _ _ _ I e
  let z : I → (S →ₐ[R] B) := fun i =>
    (((Pi.evalAlgHom B (fun _ => B) i).comp e.toAlgHom).restrictScalars R).comp
      Algebra.TensorProduct.includeRight
  refine ⟨z, ?_⟩
  have h : ∀ x, splitMap z x = e x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [hx, hy]
    | tmul b s =>
      funext i
      have hb : b ⊗ₜ[R] s = b • ((1 : B) ⊗ₜ[R] s) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [splitMap_tmul, hb, map_smul, Pi.smul_apply, smul_eq_mul]
      rfl
  have hf : (splitMap z : B ⊗[R] S → (I → B)) = e := funext h
  unfold Splits
  rw [hf]
  exact e.bijective
end

section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.valPts_of :
    ValPts := by
  intro R S V _ _ _ _ _ _ _ _
  have hinj : Function.Injective (IsScalarTower.toAlgHom R V (FractionRing V)) :=
    IsFractionRing.injective V (FractionRing V)
  constructor
  · intro z z' h
    ext s
    apply hinj
    simpa only [AlgHom.comp_apply] using AlgHom.congr_fun h s
  · intro φ
    have hmem : ∀ s, φ s ∈ (IsScalarTower.toAlgHom R V (FractionRing V)).range := by
      intro s
      have h1 : IsIntegral R (φ s) := (Algebra.IsIntegral.isIntegral s).map φ
      have h2 : IsIntegral V (φ s) := h1.tower_top
      obtain ⟨v, hv⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
      exact (AlgHom.mem_range _).2 ⟨v, hv⟩
    let e := AlgEquiv.ofInjective (IsScalarTower.toAlgHom R V (FractionRing V)) hinj
    refine ⟨e.symm.toAlgHom.comp (φ.codRestrict _ hmem), ?_⟩
    ext s
    have h := e.apply_symm_apply ⟨φ s, hmem s⟩
    exact congrArg Subtype.val h
end

section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.coeffInt_of :
    CoeffInt := by
  intro R T _ _ _ ι I _ _ c hc a m
  let c' : I → ι → integralClosure R T := fun i k => ⟨c i k, hc i k⟩
  let f : MvPolynomial ι (integralClosure R T) →+* MvPolynomial ι T :=
    MvPolynomial.map (algebraMap (integralClosure R T) T)
  have hform : ∀ i, form (c i) = (form (c' i)).map f := by
    intro i
    simp [form, f, Polynomial.map_sub, MvPolynomial.map_C, c']

    rw [Polynomial.map_sum]
    simp [Polynomial.map_mul, Polynomial.map_C, MvPolynomial.map_C, MvPolynomial.map_X]
  have hP : (∏ i, form (c i)) = (∏ i, form (c' i)).map f := by
    rw [Polynomial.map_prod]
    exact Finset.prod_congr rfl fun i _ => hform i
  rw [hP, Polynomial.coeff_map]
  simp only [f, MvPolynomial.coeff_map]
  exact (((∏ i, form (c' i)).coeff a).coeff m).2
end

section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.ptsProd_of :
    PtsProd := by
  intro B B' _ _ ρ ι J _ _ I _ a v
  have hf : ∀ c : ι → B, Polynomial.map (MvPolynomial.map ρ) (form c) = form (fun k => ρ (c k)) := by
    intro c

    simp [form, Polynomial.map_sub, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C]
  have key : ∀ (m : J → Multiset (ι → B')) (s : Finset J),
      (Multiset.map form (∑ j ∈ s, a j • m j)).prod = ∏ j ∈ s, (Multiset.map form (m j)).prod ^ a j := by
    intro m s
    classical
    refine Finset.induction_on s (by simp) ?_
    intro j s hj ih
    rw [Finset.sum_insert hj, Finset.prod_insert hj, Multiset.map_add (f := _), Multiset.prod_add, ih,
      Multiset.map_nsmul, Multiset.prod_nsmul]
  simp only [pts, mapP]
  rw [key, Polynomial.map_prod]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [Polynomial.map_pow, Polynomial.map_prod, Multiset.map_map]
  congr 1
  rw [Finset.prod_eq_multiset_prod]
  simp [Function.comp_def, hf]
end

section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

private theorem away_closed (O : Type) [CommRing O] [IsDomain O] [IsIntegrallyClosed O] (a : O) (ha : a ≠ 0)
    (x : Localization.Away a) (hx : IsIntegral O x) : ∃ o : O, algebraMap O _ o = x := by
  classical
  have hunit : ∀ y : Submonoid.powers a, IsUnit (Algebra.ofId O (FractionRing O) y) := by
    rintro ⟨_, n, rfl⟩
    rw [map_pow]
    refine IsUnit.pow n (IsUnit.mk0 _ ?_)
    rw [Algebra.ofId_apply]
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero ha)
  let f : Localization.Away a →ₐ[O] FractionRing O :=
    IsLocalization.liftAlgHom (M := Submonoid.powers a) hunit
  have hinj : Function.Injective f := by
    have h := (IsLocalization.lift_injective_iff (M := Submonoid.powers a)
      (S := Localization.Away a) (g := algebraMap O (FractionRing O)) hunit).mpr ?_
    · exact h
    · intro x y
      rw [(IsLocalization.injective (Localization.Away a)
          (powers_le_nonZeroDivisors_of_noZeroDivisors ha)).eq_iff,
        (IsFractionRing.injective O (FractionRing O)).eq_iff]
  have hcl : IsIntegrallyClosedIn O (Localization.Away a) :=
    f.isIntegrallyClosedIn hinj inferInstance
  exact IsIntegrallyClosedIn.algebraMap_eq_of_integral hx

theorem UpperTheory.Gal.crystallineComparison.smoothClosed_of :
    SmoothClosed := by
  intro l O R _ _ _ _ _ _ hl c hc
  classical
  have hM : Algebra.algebraMapSubmonoid R (Submonoid.powers (l : O)) = Submonoid.powers (l : R) := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers, map_natCast]
  haveI : IsLocalization (Submonoid.powers (l : R)) (R ⊗[O] Localization.Away (l : O)) := by
    rw [← hM]
    infer_instance
  let e : (R ⊗[O] Localization.Away (l : O)) ≃ₐ[R] Localization.Away (l : R) :=
    IsLocalization.algEquiv (Submonoid.powers (l : R)) _ _
  have hc' : IsIntegral R (e.symm c) := hc.map e.symm
  obtain ⟨s, hs⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth (R := O) (S := R)
    (B := Localization.Away (l : O))).2 ⟨e.symm c, hc'⟩
  have key : ∀ s : R ⊗[O] integralClosure O (Localization.Away (l : O)), ∃ r : R,
      algebraMap R (R ⊗[O] Localization.Away (l : O)) r =
        (TensorProduct.toIntegralClosure O R (Localization.Away (l : O)) s :
          R ⊗[O] Localization.Away (l : O)) := by
    intro s
    induction s with
    | tmul r y =>
      obtain ⟨o, ho⟩ := away_closed O (l : O) hl y.1 y.2
      refine ⟨algebraMap O R o * r, ?_⟩
      show _ = r ⊗ₜ[O] y.1
      rw [← ho, Algebra.algebraMap_eq_smul_one (A := Localization.Away (l : O)), ← TensorProduct.smul_tmul,
        Algebra.smul_def]
      rfl
    | add x y hx hy =>
      obtain ⟨r1, h1⟩ := hx
      obtain ⟨r2, h2⟩ := hy
      exact ⟨r1 + r2, by simp only [map_add (f := _), h1, h2]; rfl⟩
  obtain ⟨r, hr⟩ := key s
  refine ⟨r, ?_⟩
  rw [← e.commutes r, hr, hs]
  simp
end

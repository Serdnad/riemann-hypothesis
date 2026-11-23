module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Extension.Presentation.Core
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.RingTheory.Smooth.StandardSmooth
public import Mathlib.RingTheory.Extension.Presentation.Basic

@[expose] public section

section

namespace GlobalTheory

theorem exists_regular_exponent_of_sum_sq_eq :
    ∀ (q d : ℕ) (a : ℕ → ℤ), 2 ≤ q → 0 < d →
      (∀ k l i : ℕ, k * q ^ i ≡ l [MOD q ^ d - 1] → a k = a l) →
      ∑ k ∈ Finset.range (q ^ d - 1), a k ^ 2 = d →
      (∀ s e l : ℕ, s * e = d → l * q ^ e ≡ l [MOD q ^ d - 1] → (s : ℤ) ∣ a l) →
      ∃ k : ℕ, a k ≠ 0 ∧ ∀ i : ℕ, 0 < i → i < d → ¬ k * q ^ i ≡ k [MOD q ^ d - 1] := by
  classical
  intro q d a hq hd hinv hsum hdiv
  have h1 : 1 < q ^ d := Nat.one_lt_pow hd.ne' (by omega)
  have hN : 0 < q ^ d - 1 := by omega
  have hqd : q ^ d ≡ 1 [MOD q ^ d - 1] :=
    ((Nat.modEq_iff_dvd' h1.le).2 dvd_rfl).symm
  generalize q ^ d - 1 = N at *
  obtain ⟨k, hk⟩ : ∃ k, a k ≠ 0 := by
    by_contra h
    push_neg at h
    simp [h] at hsum
    omega
  refine ⟨k, hk, fun i hi hid hki => ?_⟩
  have hex : ∃ e, 0 < e ∧ k * q ^ e ≡ k [MOD N] := ⟨i, hi, hki⟩
  have hspec := Nat.find_spec hex
  have hle : Nat.find hex ≤ i := Nat.find_min' hex ⟨hi, hki⟩
  have hmin : ∀ m, 0 < m → m < Nat.find hex → ¬ k * q ^ m ≡ k [MOD N] :=
    fun m hm hlt h => Nat.find_min hex hlt ⟨hm, h⟩
  generalize Nat.find hex = e at hspec hle hmin
  obtain ⟨he, hke⟩ := hspec
  have hmul : ∀ m, k * q ^ (e * m) ≡ k [MOD N] := by
    intro m
    induction m with
    | zero => simp [Nat.ModEq]
    | succ m ih =>
      have : k * q ^ (e * (m + 1)) = k * q ^ (e * m) * q ^ e := by ring
      rw [this]
      exact (ih.mul_right _).trans hke
  have hmod : d % e = 0 := by
    by_contra h
    apply hmin (d % e) (Nat.pos_of_ne_zero h) (Nat.mod_lt _ he)
    have h2 : k * q ^ d = k * q ^ (e * (d / e)) * q ^ (d % e) := by
      rw [mul_assoc, ← pow_add, Nat.div_add_mod]
    have h3 : k * q ^ d ≡ k [MOD N] := by simpa using hqd.mul_left k
    rw [h2] at h3
    exact ((hmul (d / e)).mul_right _).symm.trans h3
  obtain ⟨s, hs⟩ := Nat.dvd_of_mod_eq_zero hmod
  have hs2 : 2 ≤ s := by
    by_contra h
    have : s ≤ 1 := by omega
    have : e * s ≤ e * 1 := Nat.mul_le_mul_left _ this
    omega
  have hdv : (s : ℤ) ∣ a k := hdiv s e k (by rw [hs, mul_comm]) hke
  have hsq : (s : ℤ) ^ 2 ≤ a k ^ 2 :=
    Int.le_of_dvd (by positivity) (pow_dvd_pow_of_dvd hdv 2)
  have key : ∀ i j, i < j → j < e → ¬ k * q ^ i ≡ k * q ^ j [MOD N] := by
    intro i j hij hj h
    apply hmin (i + (e - j)) (by omega) (by omega)
    have h2 := h.mul_right (q ^ (e - j))
    rw [mul_assoc, mul_assoc, ← pow_add, ← pow_add, Nat.add_sub_cancel' hj.le] at h2
    exact h2.trans hke
  have hinj : Set.InjOn (fun i => k * q ^ i % N) (Finset.range e : Set ℕ) := by
    intro i hi j hj h
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    rcases lt_trichotomy i j with h' | h' | h'
    · exact absurd h (key i j h' hj)
    · exact h'
    · exact absurd (Eq.symm h) (key j i h' hi)
  have hsub : (Finset.range e).image (fun i => k * q ^ i % N) ⊆ Finset.range N := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
    exact Finset.mem_range.2 (Nat.mod_lt _ hN)
  have hle2 := Finset.sum_le_sum_of_subset_of_nonneg (f := fun k => a k ^ 2) hsub
    (fun _ _ _ => by positivity)
  rw [Finset.sum_image hinj, hsum] at hle2
  have heq : ∑ i ∈ Finset.range e, a (k * q ^ i % N) ^ 2 = (e : ℤ) * a k ^ 2 := by
    rw [Finset.sum_congr rfl (fun i _ => by rw [← hinv k _ i (Nat.mod_modEq _ _).symm])]
    simp
  rw [heq, hs] at hle2
  push_cast at hle2
  have he' : (0 : ℤ) < e := by exact_mod_cast he
  have hs' : (2 : ℤ) ≤ s := by exact_mod_cast hs2
  have := le_of_mul_le_mul_left hle2 he'
  nlinarith

end GlobalTheory
end

section

open CategoryTheory Limits

namespace GlobalTheory

theorem exists_torsion_eq_prime_smul_of_noPTorsion {M : Type*} [AddCommGroup M] (p : ℕ)
    [hp : Fact p.Prime] (hM : ∀ x : M, (p : ℤ) • x = 0 → x = 0) (t : M)
    (ht : t ∈ Submodule.torsion ℤ M) :
    ∃ s ∈ Submodule.torsion ℤ M, t = (p : ℤ) • s := by
  obtain ⟨⟨a, ha⟩, hat⟩ := (Submodule.mem_torsion_iff t).1 ht
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  change a • t = 0 at hat
  set n := a.natAbs with hn
  have hn0 : n ≠ 0 := Int.natAbs_ne_zero.2 ha0
  have hnt : (n : ℤ) • t = 0 := by
    rcases Int.natAbs_eq a with h | h
    · rw [← h]; exact hat
    · have : a = -(n : ℤ) := h
      rw [this, neg_smul, neg_eq_zero] at hat; exact hat
  have hpow : ∀ k : ℕ, ∀ y : M, ((p : ℤ) ^ k) • y = 0 → y = 0 := by
    intro k
    induction k with
    | zero => intro y hy; simpa using hy
    | succ k ih =>
      intro y hy
      rw [pow_succ, mul_smul] at hy
      exact hM y (ih _ hy)
  set k := n.factorization p
  set m := n / p ^ k
  have hnm : p ^ k * m = n := Nat.ordProj_mul_ordCompl_eq_self n p
  have hmt : (m : ℤ) • t = 0 := by
    apply hpow k
    rw [← mul_smul]
    have : ((p : ℤ) ^ k * (m : ℤ)) = (n : ℤ) := by exact_mod_cast hnm
    rw [this, hnt]
  have hndvd : ¬ p ∣ m := Nat.not_dvd_ordCompl hp.out hn0
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp.out).2 hndvd
  have hic : IsCoprime (p : ℤ) (m : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd_natCast_natCast] using hcop
  obtain ⟨u, v, huv⟩ := hic
  refine ⟨u • t, Submodule.smul_mem _ _ ht, ?_⟩
  calc t = ((u * p + v * m : ℤ)) • t := by rw [huv, one_smul]
    _ = (p : ℤ) • (u • t) := by
      rw [add_smul, mul_smul, mul_smul, hmt, smul_zero, add_zero, smul_comm]

theorem subsingleton_zmod_tensor_torsion {M : Type*} [AddCommGroup M] (p : ℕ) [Fact p.Prime]
    (hM : ∀ x : M, (p : ℤ) • x = 0 → x = 0) :
    Subsingleton (TensorProduct ℤ (ZMod p) (Submodule.torsion ℤ M)) := by
  refine subsingleton_of_forall_eq 0 fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => rfl
  | tmul c t =>
    obtain ⟨s, hs, hts⟩ := exists_torsion_eq_prime_smul_of_noPTorsion p hM t.1 t.2
    have : t = (p : ℤ) • (⟨s, hs⟩ : Submodule.torsion ℤ M) := Subtype.ext hts
    rw [this, ← TensorProduct.smul_tmul]
    have hc : (p : ℤ) • c = 0 := by
      rw [zsmul_eq_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul]
    rw [hc, TensorProduct.zero_tmul]
  | add x y hx hy => rw [hx, hy, add_zero]

theorem finrank_zmod_tensor_eq_finrank_of_noPTorsion (M : Type*) [AddCommGroup M] [inst : Module ℤ M]
    [Module.Finite ℤ M] (p : ℕ) [Fact p.Prime] (hM : ∀ x : M, (p : ℤ) • x = 0 → x = 0) :
    Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) M) = Module.finrank ℤ M := by
  obtain rfl : inst = AddCommGroup.toIntModule M := Subsingleton.elim _ _
  set T := Submodule.torsion ℤ M
  haveI : Module.Free ℤ (M ⧸ T) := Module.free_of_finite_type_torsion_free'
  haveI := subsingleton_zmod_tensor_torsion p hM
  let g := LinearMap.baseChange (ZMod p) T.mkQ
  have hg : ⇑g = ⇑(LinearMap.lTensor (ZMod p) T.mkQ) := LinearMap.baseChange_eq_ltensor _
  have hex := lTensor_exact (ZMod p) (LinearMap.exact_subtype_mkQ T) (Submodule.mkQ_surjective T)
  have hinj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have hy' : LinearMap.lTensor (ZMod p) T.mkQ y = 0 := by rw [← hg]; exact hy
    obtain ⟨z, rfl⟩ := (hex y).1 hy'
    rw [Subsingleton.elim z 0, map_zero]
  have hsurj : Function.Surjective g := by
    rw [hg]; exact LinearMap.lTensor_surjective _ (Submodule.mkQ_surjective T)
  rw [(LinearEquiv.ofBijective g ⟨hinj, hsurj⟩).finrank_eq, Module.finrank_baseChange,
    finrank_quotient_eq_of_le_torsion le_rfl]

theorem finrank_zmod_tensor_homology_zero :
    ∀ (C : CochainComplex (ModuleCat.{0} ℤ) ℕ) (p : ℕ) [Fact p.Prime],
      (∀ (x : C.X 0), (p : ℤ) • x = 0 → x = 0) → Module.Finite ℤ (C.homology 0) →
      Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (C.homology 0)) =
        Module.finrank ℤ (C.homology 0) := by
  intro C p _ hC _
  let f : C.homology 0 ⟶ C.X 0 := C.isoHomologyπ₀.inv ≫ C.iCycles 0
  have hinj : Function.Injective (ConcreteCategory.hom f) :=
    (ModuleCat.mono_iff_injective f).1 inferInstance
  apply finrank_zmod_tensor_eq_finrank_of_noPTorsion
  intro x hx
  apply hinj
  rw [map_zero]
  apply hC
  rw [← map_zsmul, hx, map_zero]

end GlobalTheory
end

section

open IsLocalRing CategoryTheory Limits

namespace GlobalTheory.EtaleDescent

open TensorProduct

theorem exists_etale_model_of_isColimit :
    ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ (A : Type) [CommRing A] [Algebra c.pt A] [Algebra.Etale c.pt A], ∃ (j : J), (letI : Algebra (D.obj j) c.pt := (c.ι.app j).hom.toAlgebra; ∃ (Aj : Type) (_ : CommRing Aj) (_ : Algebra (D.obj j) Aj), Algebra.Etale (D.obj j) Aj ∧ Nonempty (TensorProduct (D.obj j) c.pt Aj ≃ₐ[c.pt] A)) := by
  intro J _ _ D c hc A _ _ _
  classical
  have hc' := isColimitOfPreserves (forget _) hc
  obtain ⟨ι, σ, _, _, P, hP⟩ :=
    (Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero (R := c.pt) (S := A)).mp
      inferInstance |>.out

  obtain ⟨j, hj⟩ : ∃ j, P.coeffs ⊆ Set.range (c.ι.app j).hom := by
    have hfin := P.finite_coeffs
    choose jx x hx using fun y : c.pt ↦ Types.jointly_surjective_of_isColimit hc' y
    obtain ⟨j, hj⟩ := IsFiltered.sup_objs_exists (hfin.toFinset.image jx)
    refine ⟨j, fun y hy ↦ ?_⟩
    obtain ⟨f⟩ := hj (Finset.mem_image_of_mem jx (hfin.mem_toFinset.mpr hy))
    refine ⟨D.map f (x y), ?_⟩
    have h1 := hx y
    have h2 := congr(($(c.w f)).hom (x y))
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h2
    rw [h2]
    exact h1
  letI : Algebra (D.obj j) c.pt := (c.ι.app j).hom.toAlgebra
  letI : Algebra (D.obj j) A := ((algebraMap c.pt A).comp (c.ι.app j).hom).toAlgebra
  haveI : IsScalarTower (D.obj j) c.pt A := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  haveI : P.HasCoeffs (D.obj j) := ⟨by rw [RingHom.coe_range]; exact hj⟩
  letI : Fintype σ := Fintype.ofFinite σ
  let P₀ := P.toPreSubmersivePresentation.ofHasCoeffs (D.obj j)
  have hP₀ : P₀.jacobian = Ideal.Quotient.mk _ (P.jacobianOfHasCoeffs (D.obj j)) := by
    simp only [P₀]
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    simp [Algebra.SubmersivePresentation.jacobianOfHasCoeffs]
    rw [← Algebra.Generators.algebraMap_apply]
    rfl

  set E : MvPolynomial ι (D.obj j) :=
    ∑ i, P.jacobianRelationsOfHasCoeffs (D.obj j) i * P.relationOfHasCoeffs (D.obj j) i -
      (P.jacobianOfHasCoeffs (D.obj j) * P.invJacobianOfHasCoeffs (D.obj j) - 1) with hEdef
  have hE : E.map (algebraMap (D.obj j) c.pt) = 0 := by
    simp [E, P.map_relationOfHasCoeffs, P.jacobianRelations_spec]

  have hdie : ∀ m : E.support, ∃ (k : J) (f : j ⟶ k), D.map f (E.coeff m) = 0 := by
    intro m
    have h0 : (c.ι.app j).hom (E.coeff m) = (c.ι.app j).hom 0 := by
      rw [map_zero]
      have := congr(($hE).coeff (m : ι →₀ ℕ))
      simp only [MvPolynomial.coeff_map, MvPolynomial.coeff_zero] at this
      exact this
    obtain ⟨k, f, e⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc' (E.coeff m) 0).1 (by exact h0)
    exact ⟨k, f, by simpa using e⟩
  choose k f hf using hdie
  obtain ⟨c'⟩ := IsFiltered.cocone_nonempty (WidePushoutShape.wideSpan j k f)
  set K := c'.pt
  set g : j ⟶ K := c'.ι.app none
  have hEK : E.map (D.map g).hom = 0 := by
    ext m
    rw [MvPolynomial.coeff_map]
    change (D.map g).hom (E.coeff m) = 0
    by_cases hm : m ∈ E.support
    · have hw := c'.w (WidePushoutShape.Hom.init ⟨m, hm⟩)
      have h3 : (D.map g).hom (E.coeff m) = (D.map ((WidePushoutShape.wideSpan j k f).map
          (WidePushoutShape.Hom.init ⟨m, hm⟩) ≫ c'.ι.app (some ⟨m, hm⟩))).hom (E.coeff m) := by
        rw [hw]
      rw [h3, Functor.map_comp, CommRingCat.hom_comp, RingHom.comp_apply]
      erw [hf ⟨m, hm⟩]
      exact map_zero _
    · rw [MvPolynomial.notMem_support_iff.mp hm, map_zero]

  letI : Algebra (D.obj j) (D.obj K) := (D.map g).hom.toAlgebra
  letI : Algebra (D.obj K) c.pt := (c.ι.app K).hom.toAlgebra
  haveI : IsScalarTower (D.obj j) (D.obj K) c.pt := IsScalarTower.of_algebraMap_eq (fun x ↦ by
    change (c.ι.app j).hom x = (c.ι.app K).hom ((D.map g).hom x)
    rw [← c.w g]
    rfl)
  let M := P.ModelOfHasCoeffs (D.obj j)
  let Q := P₀.baseChange (D.obj K)
  let φ : MvPolynomial ι (D.obj j) →ₐ[D.obj j] D.obj K ⊗[D.obj j] M :=
    (Algebra.TensorProduct.includeRight).comp (Ideal.Quotient.mkₐ _ _)
  have hφrel : ∀ i, φ (P.relationOfHasCoeffs (D.obj j) i) = 0 := by
    intro i
    change Algebra.TensorProduct.includeRight (Ideal.Quotient.mk _ (P.relationOfHasCoeffs (D.obj j) i)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i)), map_zero]
  have hφE : φ E = 0 := by
    rw [MvPolynomial.aeval_unique φ, MvPolynomial.aeval_def,
      IsScalarTower.algebraMap_eq (D.obj j) (D.obj K) (D.obj K ⊗[D.obj j] M),
      ← MvPolynomial.eval₂_map]
    change MvPolynomial.eval₂ _ _ (E.map (D.map g).hom) = 0
    rw [hEK, MvPolynomial.eval₂_zero]
  have hQ : IsUnit Q.jacobian := by
    rw [Algebra.PreSubmersivePresentation.baseChange_jacobian, hP₀]
    refine IsUnit.of_mul_eq_one (φ (P.invJacobianOfHasCoeffs (D.obj j))) ?_
    have h1 : P.jacobianOfHasCoeffs (D.obj j) * P.invJacobianOfHasCoeffs (D.obj j) =
        ∑ i, P.jacobianRelationsOfHasCoeffs (D.obj j) i * P.relationOfHasCoeffs (D.obj j) i
          - E + 1 := by
      rw [hEdef]; ring
    have h2 := congr(φ $h1)

    simp only [map_mul, map_add (f := _), map_sub, map_sum, map_one, hφrel, mul_zero,
    Finset.sum_const_zero, hφE, sub_zero, zero_add] at h2
    exact h2
  let Q' : Algebra.SubmersivePresentation (D.obj K) (D.obj K ⊗[D.obj j] M) ι σ :=
    { toPreSubmersivePresentation := Q, jacobian_isUnit := hQ }
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 0 (D.obj K) (D.obj K ⊗[D.obj j] M) :=
    Q'.isStandardSmoothOfRelativeDimension (by rw [← hP]; rfl)
  refine ⟨K, D.obj K ⊗[D.obj j] M, inferInstance, inferInstance, inferInstance, ⟨?_⟩⟩
  exact (Algebra.TensorProduct.cancelBaseChange (D.obj j) (D.obj K) c.pt c.pt M).trans
    (P.tensorModelOfHasCoeffsEquiv (D.obj j))

end GlobalTheory.EtaleDescent
end

section

open CategoryTheory Limits TensorProduct

namespace GlobalTheory.FpDescent

theorem exists_finitePresentation_model_of_isColimit :
    ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (D : Type) [CommRing D] [Algebra c.pt D], Algebra.FinitePresentation c.pt D →
    ∃ (j : J) (A : Type) (_ : CommRing A) (_ : Algebra (F.obj j) A)
      (_ : Algebra.FinitePresentation (F.obj j) A),
      letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
      Nonempty (c.pt ⊗[F.obj j] A ≃ₐ[c.pt] D) := by
  intro J _ _ F c hc D _ _ hD
  classical
  have hc' := isColimitOfPreserves (forget _) hc
  let P := Algebra.Presentation.ofFinitePresentation c.pt D
  obtain ⟨j, hj⟩ : ∃ j, P.coeffs ⊆ Set.range (c.ι.app j).hom := by
    have hfin := P.finite_coeffs
    choose jx x hx using fun y : c.pt ↦ Types.jointly_surjective_of_isColimit hc' y
    obtain ⟨j, hj⟩ := IsFiltered.sup_objs_exists (hfin.toFinset.image jx)
    refine ⟨j, fun y hy ↦ ?_⟩
    obtain ⟨f⟩ := hj (Finset.mem_image_of_mem jx (hfin.mem_toFinset.mpr hy))
    refine ⟨F.map f (x y), ?_⟩
    have h1 := hx y
    have h2 := congr(($(c.w f)).hom (x y))
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h2
    rw [h2]
    exact h1
  letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
  letI : Algebra (F.obj j) D := ((algebraMap c.pt D).comp (c.ι.app j).hom).toAlgebra
  haveI : IsScalarTower (F.obj j) c.pt D := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  haveI : P.HasCoeffs (F.obj j) := ⟨hj⟩
  exact ⟨j, P.ModelOfHasCoeffs (F.obj j), inferInstance, inferInstance, inferInstance,
    ⟨P.tensorModelOfHasCoeffsEquiv (F.obj j)⟩⟩

end GlobalTheory.FpDescent
end

section

open CategoryTheory Limits TensorProduct

theorem _root_.GlobalTheory.T.exists_finitePresentation_descent_of_isColimit : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (D : Type) [CommRing D] [Algebra c.pt D], Algebra.FinitePresentation c.pt D →
    ∃ (j : J) (A : Type) (_ : CommRing A) (_ : Algebra (F.obj j) A)
      (_ : Algebra.FinitePresentation (F.obj j) A),
      letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
      Nonempty (c.pt ⊗[F.obj j] A ≃ₐ[c.pt] D) := by
  intro J _ _ F c hc D _ _ hD
  classical
  have hc' := isColimitOfPreserves (forget _) hc
  let P := Algebra.Presentation.ofFinitePresentation c.pt D
  obtain ⟨j, hj⟩ : ∃ j, P.coeffs ⊆ Set.range (c.ι.app j).hom := by
    have hfin := P.finite_coeffs
    choose jx x hx using fun y : c.pt ↦ Types.jointly_surjective_of_isColimit hc' y
    obtain ⟨j, hj⟩ := IsFiltered.sup_objs_exists (hfin.toFinset.image jx)
    refine ⟨j, fun y hy ↦ ?_⟩
    obtain ⟨f⟩ := hj (Finset.mem_image_of_mem jx (hfin.mem_toFinset.mpr hy))
    refine ⟨F.map f (x y), ?_⟩
    have hw := congr(($(c.w f)).hom (x y))
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at hw
    rw [hw]
    exact hx y
  let : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
  let : Algebra (F.obj j) D := ((algebraMap c.pt D).comp (c.ι.app j).hom).toAlgebra
  have : IsScalarTower (F.obj j) c.pt D := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  have : P.HasCoeffs (F.obj j) := ⟨hj⟩
  exact ⟨j, P.ModelOfHasCoeffs (F.obj j), inferInstance, inferInstance, inferInstance,
    ⟨P.tensorModelOfHasCoeffsEquiv (F.obj j)⟩⟩
end

section

universe u_1 u_2

namespace GlobalTheory.BandLemmaFirst

theorem main :
    (let d1 : {k : Type u_1} → [Field k] → {ι : Type u_2} → (ι → ℕ) → ℕ → Matrix ι ι k → Prop :=
      @(fun {k : Type u_1} [Field k] {ι : Type u_2} (ℓ : ι → ℕ) (j : ℕ) (X : Matrix ι ι k) ↦
        ∀ (r s : ι), ℓ s < ℓ r + j → X r s = (0 : k));
    ∀ {k : Type u_1} [inst : Field k] {ι : Type u_2} [Fintype ι] [DecidableEq ι] {ℓ : ι → ℕ} {j : ℕ}
      {X Y : Matrix ι ι k}, d1 ℓ j X → d1 ℓ j Y → d1 ℓ j (X + Y)) := by
  intro d1 k _ ι _ _ ℓ j X Y hX hY r s h
  show (X + Y) r s = 0
  rw [Matrix.add_apply, hX r s h, hY r s h, add_zero]

end GlobalTheory.BandLemmaFirst
end

section

universe u_1 u_2

namespace GlobalTheory.BandLemmaSecond

theorem main : (let d1 : {k : Type u_1} → [Field k] → {ι : Type u_2} → (ι → ℕ) → ℕ → Matrix ι ι k → Prop := @(fun {k : Type u_1} [Field k] {ι : Type u_2} (ℓ : ι → ℕ) (j : ℕ) (X : Matrix ι ι k) ↦ ∀ (r s : ι), ℓ s < ℓ r + j → X r s = (0 : k)); ∀ {k : Type u_1} [inst : Field k] {ι : Type u_2} [Fintype ι] [DecidableEq ι] {ℓ : ι → ℕ} {j : ℕ} {X : Matrix ι ι k}, d1 ℓ j X → d1 ℓ j (-X)) := by
  intro d1 k _ ι _ _ ℓ j X h r s hrs
  simp only [Matrix.neg_apply, h r s hrs, neg_zero]

end GlobalTheory.BandLemmaSecond
end

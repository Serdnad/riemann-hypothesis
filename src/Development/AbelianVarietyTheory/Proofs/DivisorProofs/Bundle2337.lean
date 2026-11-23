module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2317
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle451
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2314
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle613
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1591
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle627
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle595
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1909
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle068
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2315
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetAbelianLocusOfGoodReduction
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle058
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1512
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishesToPullChartIffOfFlat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings

@[expose] public section

section

set_option autoImplicit false

namespace GlobalTheory.ShFam.Cell

open Matrix

variable {R : Type} [CommRing R]

theorem exists_lowInv_mul_upperUni_of_leadingMinors :
    ∀ (n : ℕ) (N : Matrix (Fin n) (Fin n) R),
      (∀ (k : ℕ) (hk : k ≤ n), IsUnit (N.submatrix (Fin.castLE hk) (Fin.castLE hk)).det) →
      ∃ L U : Matrix (Fin n) (Fin n) R, IsLowInv L ∧ (∀ i j, j < i → U i j = 0) ∧ (∀ i, U i i = 1) ∧ N = L * U := by
  intro n
  induction n with
  | zero =>
    intro N _
    exact ⟨1, 1, ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
      by ext i; exact Fin.elim0 i⟩
  | succ n ih =>
    intro N hN
    set P : Matrix (Fin n) (Fin n) R := N.submatrix Fin.castSucc Fin.castSucc with hP
    have hPm : ∀ (k : ℕ) (hk : k ≤ n), IsUnit (P.submatrix (Fin.castLE hk) (Fin.castLE hk)).det := by
      intro k hk
      have e : P.submatrix (Fin.castLE hk) (Fin.castLE hk)
          = N.submatrix (Fin.castLE (hk.trans (Nat.le_succ n))) (Fin.castLE (hk.trans (Nat.le_succ n))) := by
        ext i j; rfl
      rw [e]; exact hN k _
    obtain ⟨L₀, U₀, ⟨hL₀z, hL₀d⟩, hU₀z, hU₀d, hPLU⟩ := ih P hPm
    have hdL₀ : IsUnit L₀.det := by
      rw [Matrix.det_of_isLowerTriangular L₀ (fun i j h => hL₀z i j h)]
      exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one (fun i _ => hL₀d i)
    have hdU₀ : IsUnit U₀.det := by
      rw [Matrix.det_of_isUpperTriangular (M := U₀) (fun i j h => hU₀z i j h)]
      simp [hU₀d]
    set q : Fin n → R := fun i => N (Fin.castSucc i) (Fin.last n)
    set r : Fin n → R := fun j => N (Fin.last n) (Fin.castSucc j)
    set u : Fin n → R := L₀⁻¹ *ᵥ q with hu
    set l : Fin n → R := r ᵥ* U₀⁻¹ with hl
    set d : R := N (Fin.last n) (Fin.last n) - l ⬝ᵥ u with hd
    have hq : L₀ *ᵥ u = q := by rw [hu, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdL₀, Matrix.one_mulVec]
    have hr : l ᵥ* U₀ = r := by rw [hl, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hdU₀, Matrix.vecMul_one]
    let L : Matrix (Fin (n+1)) (Fin (n+1)) R := Matrix.of fun i j =>
      Fin.lastCases (Fin.lastCases d l j) (fun i' => Fin.lastCases 0 (fun j' => L₀ i' j') j) i
    let U : Matrix (Fin (n+1)) (Fin (n+1)) R := Matrix.of fun i j =>
      Fin.lastCases (Fin.lastCases 1 (fun _ => 0) j) (fun i' => Fin.lastCases (u i') (fun j' => U₀ i' j') j) i
    have hLz : ∀ i j, i < j → L i j = 0 := by
      intro i j hij
      induction i using Fin.lastCases with
      | last => exact absurd hij (not_lt.2 (Fin.le_last j))
      | cast i' =>
        induction j using Fin.lastCases with
        | last => simp [L]
        | cast j' => simpa [L] using hL₀z i' j' (Fin.castSucc_lt_castSucc_iff.1 hij)
    have hLdiag : ∀ i, L i i = Fin.lastCases d (fun i' => L₀ i' i') i := by
      intro i
      induction i using Fin.lastCases with
      | last => simp [L]
      | cast i' => simp [L]
    have hUz : ∀ i j, j < i → U i j = 0 := by
      intro i j hij
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact absurd hij (lt_irrefl _)
        | cast j' => simp [U]
      | cast i' =>
        induction j using Fin.lastCases with
        | last => exact absurd hij (not_lt.2 (Fin.le_last _))
        | cast j' => simpa [U] using hU₀z i' j' (Fin.castSucc_lt_castSucc_iff.1 hij)
    have hUd : ∀ i, U i i = 1 := by
      intro i
      induction i using Fin.lastCases with
      | last => simp [U]
      | cast i' => simpa [U] using hU₀d i'
    have hNLU : N = L * U := by
      ext i j
      rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last =>
          simp only [L, U, Matrix.of_apply, Fin.lastCases_last, Fin.lastCases_castSucc, mul_one]
          rw [hd]; simp [dotProduct]
        | cast j' =>
          simp only [L, U, Matrix.of_apply, Fin.lastCases_last, Fin.lastCases_castSucc, mul_zero, add_zero]
          have := congrFun hr j'
          simpa [vecMul, dotProduct, r] using this.symm
      | cast i' =>
        induction j using Fin.lastCases with
        | last =>
          simp only [L, U, Matrix.of_apply, Fin.lastCases_last, Fin.lastCases_castSucc, mul_one, add_zero]
          have := congrFun hq i'
          simpa [mulVec, dotProduct, q] using this.symm
        | cast j' =>
          simp only [L, U, Matrix.of_apply, Fin.lastCases_last, Fin.lastCases_castSucc, zero_mul, add_zero]
          have := congrFun (congrFun hPLU i') j'
          simpa [hP, Matrix.mul_apply] using this
    have hdet : IsUnit L.det := by
      have h1 : N.det = L.det * U.det := by rw [hNLU, Matrix.det_mul]
      have h2 : U.det = 1 := by
        rw [Matrix.det_of_isUpperTriangular (M := U) (fun i j h => hUz i j h)]; simp [hUd]
      have h3 : N = N.submatrix (Fin.castLE (le_refl (n+1))) (Fin.castLE (le_refl (n+1))) := by
        ext i j; rfl
      have := hN (n+1) le_rfl
      rw [← h3, h1, h2, mul_one] at this
      exact this
    have hdu : IsUnit d := by
      rw [Matrix.det_of_isLowerTriangular L (fun i j h => hLz i j h), Fin.prod_univ_castSucc] at hdet
      have := isUnit_of_mul_isUnit_right hdet
      simpa [hLdiag] using this
    refine ⟨L, U, ⟨hLz, fun i => ?_⟩, hUz, hUd, hNLU⟩
    rw [hLdiag i]
    induction i using Fin.lastCases with
    | last => simpa using hdu
    | cast i' => simpa using hL₀d i'

end GlobalTheory.ShFam.Cell
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

open GlobalTheory.InvForm

namespace GlobalTheory.InvFormRetract

theorem dVal_smul {R B D : Type} [CommRing R] [CommRing B] [Algebra R B] [CommRing D] [Algebra R D] (φ : B →ₐ[R] DualNumber D) (b : B) (x : Ω[B⁄R]) : dVal φ (b • x) = redHom φ b * dVal φ x := by
  letI : Algebra B D := (redHom φ).toAlgebra
  haveI : IsScalarTower R B D := IsScalarTower.of_algebraMap_eq fun r ↦ (redHom_algebraMap φ r).symm
  unfold dVal
  simp only [LinearMap.restrictScalars_apply, LinearMap.map_smul]
  rfl

theorem injective_baseChange {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] (hab : IsAbelianScheme A) (U : AffOp A.left) :
    Function.Injective (LinearMap.liftBaseChange (Sec A.hom U.unop.1) (evForm A.hom U ∘ₗ (InvForm A).subtype)) := by
  haveI : Smooth A.hom := hab.smooth
  haveI : IsProper A.hom := hab.proper
  haveI : CompactSpace A.left := ⟨by simpa using QuasiCompact.isCompact_preimage (f := A.hom) Set.univ isOpen_univ isCompact_univ⟩
  haveI : Algebra.Smooth R (Sec A.hom U.unop.1) := smooth_sec_affine A.hom U.unop
  haveI : Module.Flat R (Sec A.hom U.unop.1) := Algebra.Smooth.flat R _
  obtain ⟨n, V, hV⟩ := GlobalTheory.T.exists_finite_affineCover_globalForm_eq_zero_of_restrictions R A.left A.hom inferInstance
  let f : ∀ k, InvForm A →ₗ[R] Ω[Sec A.hom (V k).unop.1⁄R] := fun k => evForm A.hom (V k) ∘ₗ (InvForm A).subtype
  let F : InvForm A →ₗ[R] ((k : Fin n) → Ω[Sec A.hom (V k).unop.1⁄R]) := LinearMap.pi f
  have hF : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    exact Subtype.ext (hV w.1 fun k => congrFun hw k)
  have hFB : Function.Injective (LinearMap.lTensor (Sec A.hom U.unop.1) F) :=
    Module.Flat.lTensor_preserves_injective_linearMap F hF
  have hk : ∀ (k : Fin n) (z : Sec A.hom U.unop.1 ⊗[R] InvForm A), TensorProduct.piRight R R (Sec A.hom U.unop.1) (fun k : Fin n => Ω[Sec A.hom (V k).unop.1⁄R])
      (LinearMap.lTensor (Sec A.hom U.unop.1) F z) k = LinearMap.lTensor (Sec A.hom U.unop.1) (f k) z := by
    intro k z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b w => simp [F]
    | add x y hx hy => simp only [map_add (f := _), Pi.add_apply, hx, hy]
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  apply hFB
  rw [map_zero]
  apply (TensorProduct.piRight R R (Sec A.hom U.unop.1) (fun k : Fin n => Ω[Sec A.hom (V k).unop.1⁄R])).injective
  rw [map_zero]
  funext k
  rw [hk, Pi.zero_apply]
  haveI : Algebra.Smooth R (Sec A.hom (V k).unop.1) := smooth_sec_affine A.hom (V k).unop
  refine GlobalTheory.T.eq_zero_of_liftBaseChange_derivations_eq_zero R (Sec A.hom U.unop.1) _ inferInstance _ (fun θ hθ => ?_)
  obtain ⟨ψ, hfst, hψ⟩ := GlobalTheory.T.exists_groupLawTranslate_derivation_invariantForms R A U (V k) θ hθ
  have key : ∀ y, LinearMap.liftBaseChange (Sec A.hom U.unop.1) θ (LinearMap.lTensor (Sec A.hom U.unop.1) (f k) y) =
      dVal ψ (LinearMap.liftBaseChange (Sec A.hom U.unop.1) (evForm A.hom U ∘ₗ (InvForm A).subtype) y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul b w =>
      rw [LinearMap.lTensor_tmul, LinearMap.liftBaseChange_tmul, LinearMap.liftBaseChange_tmul, dVal_smul]
      have h1 : redHom ψ b = b ⊗ₜ 1 := hfst b
      rw [h1, Algebra.smul_def]
      simp only [f, LinearMap.comp_apply, Submodule.subtype_apply, hψ]
      rfl
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  rw [key, hz, map_zero]

theorem retract : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ U : AffOp A.left, ∃ r : Ω[Sec A.hom U.unop.1⁄R] →ₗ[Sec A.hom U.unop.1] (Sec A.hom U.unop.1 ⊗[R] GlobalTheory.InvForm.InvForm A), ∀ w : GlobalTheory.InvForm.InvForm A, r (evForm A.hom U w.1) = 1 ⊗ₜ w := by
  intro R _ A _ g hab hdim U
  have hsurj : Function.Surjective (LinearMap.liftBaseChange (Sec A.hom U.unop.1) (evForm A.hom U ∘ₗ (InvForm A).subtype)) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← GlobalTheory.T.span_invariantOneForms_affineOpen_abelianScheme_eq_top R A g hab hdim U, Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    exact ⟨1 ⊗ₜ w, by simp⟩
  let e := LinearEquiv.ofBijective _ ⟨injective_baseChange A hab U, hsurj⟩
  refine ⟨e.symm.toLinearMap, fun w => ?_⟩
  apply e.injective
  rw [LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply]
  change _ = LinearMap.liftBaseChange _ _ (1 ⊗ₜ w)
  rw [LinearMap.liftBaseChange_tmul, one_smul]
  rfl

end GlobalTheory.InvFormRetract
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HeckeFibre

theorem transl_triv {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    (M : LB A.left) (hM : M.IsLB) (hR : Out.Rigidified A M) (K : Type) [Field K] [IsAlgClosed K]
    (y : Sp K ⟶ S) (n : ℕ) (hn : (n : K) ≠ 0) (x : Over.mk y ⟶ A) (hx : x ^ n = 1)
    (h : ∀ z : Over.mk y ⟶ A, z ^ n = 1 → Out.WeilIs A M (n : ℤ) x z 1) :
    ∃ t : (Out.translDiff A M x).Gen, t.IsGen := by
  obtain ⟨L, hL, ⟨c⟩⟩ := GlobalTheory.Moduli.cubicalStr_of_triv_theta GlobalTheory.abelianSchemeLaws_all.1 _ A hA M hM hR
    (GlobalTheory.WeilIntegral.triv_theta GlobalTheory.CubeTop.cubeTheorem hA hM)
  subst hL
  exact GlobalTheory.OrthKer.mem_kernel_of_cubWeil_orthogonal K S y A hA L c n hn x hx
    (fun z hz => (GlobalTheory.UU.cubWeil_iff_weilIs GlobalTheory.globalFns_holds hA hx hz 1).2 (h z hz))

theorem pic_field_eq_zero (K : Type) [Field K] (c : GlobalTheory.CechPic.Pic (Sp K)) : c = 0 := by
  obtain ⟨V, hV, hc⟩ := GlobalTheory.AbDual.exists_pull_eq_zero c (IsLocalRing.closedPoint K)
  have h := GlobalTheory.AbDual.pull_eq_zero_of_mem V (𝟙 _) (fun z => by
    have : z = IsLocalRing.closedPoint K := Subsingleton.elim (α := PrimeSpectrum K) _ _
    rw [this]; exact hV) hc
  rwa [GlobalTheory.CechPic.pull_id] at h

theorem rigidified_diag {S : Scheme.{0}} (A : Over S) [GrpObj A] (P : LB (A ⊗ A).left) (hP : P.IsLB)
    (rig₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) :
    Out.Rigidified A (P.pull (lift (𝟙 A) (𝟙 A)).left) := by
  have h0 := (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hP _)).2 rig₁
  refine (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB (pull_isLB hP _) _)).1 ?_
  rw [GlobalTheory.CechPic.cls_pull (pull_isLB hP _), GlobalTheory.CechPic.cls_pull hP, ← GlobalTheory.CechPic.pull_comp]
  have e : eSec A ≫ (lift (𝟙 A) (𝟙 A)).left = eSec A ≫ (lift (1 : A ⟶ A) (𝟙 A)).left := by
    have h1 : η[A] ≫ (1 : A ⟶ A) = η[A] := by
      rw [MonObj.comp_one, CategoryTheory.Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    simp only [eSec, ← Over.comp_left, comp_lift, Category.comp_id, h1]
  rw [e, GlobalTheory.CechPic.pull_comp, ← GlobalTheory.CechPic.cls_pull hP _ (pull_isLB hP _), h0, map_zero]

end GlobalTheory.HeckeFibre

namespace GlobalTheory.HeckeFibre

theorem fibre_triv : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ h ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, ∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ S), ∃ t : (((GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).pull (lift (toUnit o.A ≫ h) (𝟙 o.A)).left).pull (pullback.fst o.A.hom y)).Gen, t.IsGen := by
  intro p _ D R _ b g c k N hc hk hN3 hNp hEF hsurj hdvd S s o h hh K _ _ y
  obtain ⟨x, rfl⟩ := hh
  obtain ⟨β, hβ⟩ : ∃ β : R →+* K, y ≫ s = spMap β :=
    ⟨(Spec.preimage (y ≫ s)).hom, by simp [spMap]⟩
  obtain ⟨I, hI⟩ := o.geom K y β hβ
  obtain ⟨n, h', hn0, hnp, hsq, hpow, hW⟩ :=
    GlobalTheory.T.exists_sqrt_heckePoint_weilPairing_orthogonal D K _ _ _ I g c k N hc hk (by omega) hNp hEF hsurj hdvd x
  have hnK : (n : K) ≠ 0 := by
    have := (b.unit n hnp).map β
    rw [map_natCast] at this
    exact this.ne_zero
  have htr := transl_triv o.A o.ab _ (pull_isLB o.isLB _) (rigidified_diag o.A o.P o.isLB o.rig₁) K y n hnK
    (h' ^ (k ^ 2 / c)) hpow (fun z hz => by
      have w := hW z hz
      have e1 : unitOn (1 : Kˣ) = 1 := map_one _
      rw [e1] at w
      exact w)
  exact GlobalTheory.T.biextension_trivial_of_translate_difference_trivial o.A o.ab o.P o.isLB o.rig₁ o.rig₂ o.symm (Over.mk y) (pic_field_eq_zero K)
    (o.eta (N • g x)) h' (k ^ 2 / c) (by rw [hsq, hI]) htr

end GlobalTheory.HeckeFibre
end
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.thetaTransform_hasLevel_cmExtension : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ φ ∈ schA F κ,
          ∃ U : AddSubgroup (Formalism.IndefR.DatumF.WOF F E nS nT), IsOpen (U : Set (Formalism.IndefR.DatumF.WOF F E nS nT)) ∧
            ∀ u ∈ U, u.map (Formalism.IndefR.DatumF.infPartF F E) = 0 →
              Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ u (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ) =
                GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ := by
  first | exact @GlobalTheory.ThetaLevelCM.thetaTr_level | exact GlobalTheory.ThetaLevelCM.thetaTr_level | (intros; apply GlobalTheory.ThetaLevelCM.thetaTr_level <;> assumption)
end

section

open IsLocalRing GlobalTheory.TorRef

namespace GlobalTheory.DivVal

theorem exists_valuation_centre (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (hV : IsCN V) :
    ∃ ν : Valuation (FractionRing V) (WithZero (Multiplicative ℤ)),
      (∀ v : V, ν (algebraMap V (FractionRing V) v) ≤ 1) ∧
        ∀ v ∈ maximalIdeal V, ν (algebraMap V (FractionRing V) v) < 1 := by
  classical
  haveI : IsNoetherianRing V := hV.1
  by_cases hm : maximalIdeal V = ⊥
  · refine ⟨1, fun v => ?_, fun v hv => ?_⟩
    · by_cases h : algebraMap V (FractionRing V) v = 0
      · simp [h]
      · simp [Valuation.one_apply_of_ne_zero h]
    · rw [hm, Ideal.mem_bot] at hv
      simp [hv]
  · obtain ⟨T, hT, g, hg, hc⟩ := GlobalTheory.GoodVal.exists_dvr_centre (R := V) (K := FractionRing V)
      (L := FractionRing V) (maximalIdeal V) hm
    have hg' : ∀ v : V, algebraMap T (FractionRing V) (g v) = algebraMap V (FractionRing V) v := fun v => by
      simpa using congrArg (fun f => f v) hg
    have hne : maximalIdeal T ≠ ⊥ := IsDiscreteValuationRing.not_a_field T
    let P : IsDedekindDomain.HeightOneSpectrum T := ⟨maximalIdeal T, inferInstance, hne⟩
    refine ⟨P.valuation (FractionRing V), fun v => ?_, fun v hv => ?_⟩
    · rw [← hg']
      exact P.valuation_le_one (g v)
    · rw [← hg']
      refine (P.valuation_lt_one_iff_mem (g v)).2 ?_
      show g v ∈ maximalIdeal T
      rw [← Ideal.mem_comap, hc]
      exact hv

end GlobalTheory.DivVal
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

open GlobalTheory.LB GlobalTheory.Vanishing.H0 GlobalTheory.TangentOrigin
open GlobalTheory.Adelic (cutIdeal)

namespace GlobalTheory.CompHS

def Cartier.pullOfInt {Y T : Scheme.{0}} [IsIntegral T] {I : Y.IdealSheafData} (Δ : Cartier I) (r : T ⟶ Y) {z₀ : T}
    (hz : r z₀ ∉ I.support) : Cartier (I.comap r) :=
  { Cartier.ofSec (LB.isLB_pull Δ.isLB r) (secPull Δ.t r) (y₀ := z₀)
      (by rw [nonzeroLocus_secPull]; exact (Δ.mem_nonzeroLocus _).2 hz) with
    cut := (GlobalTheory.Vanishing.eq_comap_of_stalk
      (fun z => GlobalTheory.Vanishing.stalkId_cutIdeal_secPull Δ.isLB (fun _ : Unit => Δ.t) z)).trans (by rw [Δ.cut]) }

theorem ne_bot_of_notMem {Y : Scheme.{0}} {I : Y.IdealSheafData} {y : Y} (h : y ∉ I.support) : I ≠ ⊥ := fun e => by
  rw [e, Scheme.IdealSheafData.support_bot] at h
  exact h trivial

theorem nonempty_resol (hPr : GlobalTheory.Published.Principalisation) {F : Type} [Field F] [NumberField F] {Y : Scheme.{0}}
    {p : Y ⟶ Sp F} {D : ℕ} (hs : SmoothOfRelativeDimension D p) (hp : IsProjOver p) (hc : GeometricallyConnected p)
    {U : Y.Opens} (hU : (U : Set Y).Nonempty) {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) {a₁ a₂ : Λ}
    {W₁ : Submodule F (H0 p (B a₁) ⊤)} {W₂ : Submodule F (H0 p (B a₂) ⊤)}
    (h₁ : NoBase (C.isLB a₁) W₁ U) (h₂ : NoBase (C.isLB a₂) W₂ U) : Nonempty (Resol C U D W₁ W₂) := by
  have : Smooth p := SmoothOfRelativeDimension.smooth D p
  have : GeometricallyIntegral p := geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres p
  have hY : IsIntegral Y := GeometricallyIntegral.geometrically_isIntegral (f := p) (K := F) (𝟙 _) (𝟙 Y) p IsPullback.of_id_fst
  obtain ⟨u, hu⟩ := hU
  obtain ⟨Y₁, s₁, hi₁, hs₁, hp₁, hb₁, -, hc₁, -⟩ :=
    hPr F D Y p hY hs hp (baseIdeal (C.isLB a₁) W₁) (ne_bot_of_notMem (h₁ u hu))
  have iso₁ : IsIso (s₁ ∣_ U) := hb₁.isIso_restrict U h₁
  obtain ⟨z₁, hz₁⟩ : ∃ z : Y₁, z ∈ s₁ ⁻¹ᵁ U :=
    let z := inv (s₁ ∣_ U) ⟨u, hu⟩
    ⟨z.1, z.2⟩
  let M₁ : Modif p U D := ⟨Y₁, s₁, hs₁, hp₁, iso₁, (s₁ ⁻¹ᵁ U).isOpen.dense ⟨z₁, hz₁⟩⟩
  have off₂ : ∀ y ∈ s₁ ⁻¹ᵁ U, y ∉ ((baseIdeal (C.isLB a₂) W₂).comap s₁).support := fun y hy h => by
    rw [Scheme.IdealSheafData.support_comap] at h
    exact h₂ _ hy h
  obtain ⟨Y₂, s₂, hi₂, hs₂, hp₂, hb₂, -, hc₂, -⟩ :=
    hPr F D Y₁ (s₁ ≫ p) hi₁ hs₁ hp₁ _ (ne_bot_of_notMem (off₂ z₁ hz₁))
  have iso₂ : IsIso (s₂ ∣_ (s₁ ⁻¹ᵁ U)) := hb₂.isIso_restrict _ off₂
  obtain ⟨z₂, hz₂⟩ : ∃ z : Y₂, z ∈ s₂ ⁻¹ᵁ (s₁ ⁻¹ᵁ U) :=
    let z := inv (s₂ ∣_ (s₁ ⁻¹ᵁ U)) ⟨z₁, hz₁⟩
    ⟨z.1, z.2⟩
  let M₂ : Modif M₁.str M₁.opn D := ⟨Y₂, s₂, hs₂, hp₂, iso₂, (s₂ ⁻¹ᵁ (s₁ ⁻¹ᵁ U)).isOpen.dense ⟨z₂, hz₂⟩⟩
  have Δ₂ : Cartier ((baseIdeal (C.isLB a₂) W₂).comap (s₂ ≫ s₁)) := by
    rw [Scheme.IdealSheafData.comap_comp]; exact (GlobalTheory.T.nonempty_cartier_of_locally_principal' _ _ hc₂).some
  have Δ₁ : Cartier ((baseIdeal (C.isLB a₁) W₁).comap (s₂ ≫ s₁)) := by
    rw [Scheme.IdealSheafData.comap_comp]
    exact (GlobalTheory.T.nonempty_cartier_of_locally_principal' _ _ hc₁).some.pullOfInt s₂ (z₀ := z₂) (by
      rw [Scheme.IdealSheafData.support_comap]; exact h₁ _ hz₂)
  exact ⟨{ toModif := M₁.trans M₂, Δ₁ := Δ₁, Δ₂ := Δ₂ }⟩

end GlobalTheory.CompHS


open GlobalTheory.CompHS in
theorem GlobalTheory.CompHS.nonempty_choice : GlobalTheory.Published.Principalisation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : WtPar Dw), IsVariety₀ TF.X Z → FreeOnOpen TF.X Z U P.u₁ → FreeOnOpen TF.X Z U P.u₂ → Nonempty (Choice TF.X Z U P) := by
  intro hPr E _ _ _ H Dw l Xo c TF Z r U P hv h₁ h₂
  obtain ⟨hs, hp, hc⟩ := hv
  have : ConnectedSpace (Y₀ TF.X Z) := GeometricallyConnected.connectedSpace_of_subsingleton (str₀ TF.X Z)
  exact nonempty_resol hPr hs hp hc (dense_U₀ TF.X Z).nonempty (common₀ TF.X Z) h₁ h₂
end

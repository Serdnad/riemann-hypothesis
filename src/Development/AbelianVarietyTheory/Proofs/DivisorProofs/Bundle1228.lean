module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulSecNonzeroOnSpecialFibre
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle019
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1137
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1171
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsEffAddNsmulDiv
import Development.AbelianVarietyTheory.Definitions.Divisors.ToNatLengthEqRangeAddRange

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.GenSecInt

open GlobalTheory.PrimSec GlobalTheory.AbLaw

variable {X XK : Scheme.{0}} [IsIntegral X] {f : X ⟶ Sp ℤ} {j : XK ⟶ X} {fK : XK ⟶ Sp ℚ}
  (H : IsPullback j fK f (spMap (algebraMap ℤ ℚ)))
include H

theorem app_injective_of_affine (hc : CharZero Γ(X, ⊤)) {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Injective (j.app U).hom := by
  by_cases hne : Nonempty U
  · letI := (j.app U).hom.toAlgebra
    haveI := isLocalization_app H hU
    haveI : CharZero Γ(X, U) :=
      ((resG X (le_top : U ≤ ⊤)).charZero_iff (map_injective_of_isIntegral X _)).1 hc
    refine IsLocalization.injective (M := (nonZeroDivisors ℤ).map (AbLaw.cst f U)) Γ(XK, j ⁻¹ᵁ U) ?_
    rintro _ ⟨π, hπ, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero ?_
    have e : AbLaw.cst f U π = (π : Γ(X, U)) := map_intCast _ π
    rw [e, Ne, Int.cast_eq_zero]
    exact nonZeroDivisors.ne_zero hπ
  · haveI : Subsingleton Γ(X, U) := by
      have : U = ⊥ := by
        rw [eq_bot_iff]
        exact fun x hx => (hne ⟨⟨x, hx⟩⟩).elim
      subst this
      infer_instance
    exact fun a b _ => Subsingleton.elim a b

theorem app_injective (hc : CharZero Γ(X, ⊤)) (U : X.Opens) : Function.Injective (j.app U).hom := by
  intro a b h
  refine X.sheaf.eq_of_locally_eq' (fun V : {V : X.affineOpens // V.1 ≤ U} => V.1.1) U
    (fun V => homOfLE V.2) ?_ a b fun V => ?_
  · intro x hx
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨W, hW⟩, hWU⟩, hxW⟩
  · apply app_injective_of_affine H hc V.1.2
    exact (app_rs j V.2 a).trans ((congrArg _ h).trans (app_rs j V.2 b).symm)

theorem exists_extension (hc : CharZero Γ(X, ⊤)) {U : X.Opens} (t : Γ(XK, j ⁻¹ᵁ U))
    (h : ∀ x ∈ U, ∃ (V : X.Opens) (hV : V ≤ U) (b : Γ(X, V)), x ∈ V ∧
      (j.app V).hom b = rs XK (pre_le j hV) t) :
    ∃ b : Γ(X, U), (j.app U).hom b = t := by
  choose V hV b hx hb using h
  have hcov : U ≤ ⨆ x : U, V x.1 x.2 := fun x hxU =>
    TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hxU⟩, hx x hxU⟩
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' (fun x : U => V x.1 x.2) U
    (fun x => homOfLE (hV x.1 x.2)) hcov (fun x => b x.1 x.2) (fun x y => by
      apply app_injective H hc
      refine (app_rs j inf_le_left _).trans (Eq.trans ?_ (app_rs j inf_le_right _).symm)
      rw [hb, hb]
      exact (rs_rs _ _ _).trans (rs_rs _ _ _).symm)
  refine ⟨s, XK.sheaf.eq_of_locally_eq' (fun x : U => j ⁻¹ᵁ V x.1 x.2) (j ⁻¹ᵁ U)
    (fun x => homOfLE fun _ hy => hV x.1 x.2 hy) ?_ _ _ fun x => ?_⟩
  · intro y hy
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨j y, hy⟩, hx _ hy⟩
  · exact (app_rs j (hV x.1 x.2) s).symm.trans ((congrArg _ (hs x)).trans (hb x.1 x.2))

theorem exists_sec [CompactSpace X] (hc0 : CharZero Γ(X, ⊤)) (B : LB X) (hB : B.IsLB)
    (t : (B.pull j).Sec) : ∃ s : B.Sec, ∀ y : XK,
      j y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s ↔ y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus t := by
  have hx : ∀ x : X, ∃ (i : B.ι) (W : X.Opens), IsAffineOpen W ∧ x ∈ W ∧ W ≤ B.U i := by
    intro x
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show x ∈ ⨆ i, B.U i from hB.cover ▸ trivial)
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hi (B.U i).isOpen
    exact ⟨i, W, hW, hxW, hWU⟩
  choose ci Wx hWa hxW hWle using hx
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover (fun x => (Wx x : Set X)) (fun x => (Wx x).isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxW x⟩)
  choose π b hπ hb using fun x => exists_numerator H (hWa x) (loc t (ci x) (hWle x))
  classical
  let c : ℤ := ∏ x ∈ S, π x
  have hc : algebraMap ℤ ℚ c ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
    exact Finset.prod_ne_zero_iff.2 fun x _ => hπ x
  have hb' : ∀ x ∈ S, ∃ b' : Γ(X, Wx x), (j.app (Wx x)).hom b' =
      AbLaw.cst fK (j ⁻¹ᵁ Wx x) (algebraMap ℤ ℚ c) * loc t (ci x) (hWle x) := by
    intro x hxS
    refine ⟨AbLaw.cst f (Wx x) (∏ y ∈ S.erase x, π y) * b x, ?_⟩
    rw [map_mul, app_cst H.w, hb, ← mul_assoc, ← map_mul, ← map_mul, Finset.prod_erase_mul _ _ hxS]
  choose! b' hb' using hb'
  have key : ∀ i, ∃ s : Γ(X, B.U i), (j.app (B.U i)).hom s =
      AbLaw.cst fK (j ⁻¹ᵁ B.U i) (algebraMap ℤ ℚ c) * loc t i le_rfl := by
    intro i
    refine exists_extension H hc0 _ fun x hx => ?_
    obtain ⟨z, hzS, hxz⟩ := Set.mem_iUnion₂.1 (hS (Set.mem_univ x))
    have hV : B.U i ⊓ Wx z ≤ B.U i := inf_le_left
    have hk : B.U i ⊓ Wx z ≤ B.U (ci z) := inf_le_right.trans (hWle z)
    refine ⟨B.U i ⊓ Wx z, hV, rs X (le_inf hV hk) (B.g i (ci z)).val * rs X inf_le_right (b' z), ⟨hx, hxz⟩, ?_⟩
    rw [map_mul, app_rs j (inf_le_right : B.U i ⊓ Wx z ≤ Wx z) (b' z), hb' z hzS, map_mul, rs_cst,
      rs_loc t (ci z) (hWle z) (inf_le_right : B.U i ⊓ Wx z ≤ Wx z), map_mul, rs_cst,
      rs_loc t i le_rfl hV,
      loc_trans t i (ci z) (le_rfl.trans hV) hk]
    ring
  choose s hs using key
  have hunit : ∀ W : XK.Opens, IsUnit (AbLaw.cst fK W (algebraMap ℤ ℚ c)) := fun W =>
    (IsUnit.mk0 _ hc).map _
  refine ⟨⟨s, fun i k => ?_⟩, fun y => ?_⟩
  · apply app_injective H hc0
    change (j.app _).hom (rs X inf_le_left (s i)) = (j.app _).hom (_ * rs X inf_le_right (s k))
    rw [map_mul, app_rs, app_rs, hs, hs, map_mul, map_mul, rs_cst, rs_cst,
      rs_loc t _ _ inf_le_left, rs_loc t _ _ inf_le_right, loc_trans t i k _ inf_le_right, rs_self]
    ring
  · have hmem : ∀ i, y ∈ j ⁻¹ᵁ B.U i →
        (j y ∈ X.basicOpen (s i) ↔ y ∈ XK.basicOpen (t.f (fun _ => i))) := by
      intro i hy
      change y ∈ j ⁻¹ᵁ X.basicOpen (s i) ↔ _
      rw [Scheme.preimage_basicOpen]
      change y ∈ XK.basicOpen ((j.app (B.U i)).hom (s i)) ↔ _
      rw [hs, Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ (hunit _)]
      exact ⟨fun h => (mem_basicOpen_rs _ _ hy).1 h.2, fun h => ⟨hy, (mem_basicOpen_rs _ _ hy).2 h⟩⟩
    constructor
    · intro h
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h
      have hy : y ∈ j ⁻¹ᵁ B.U i := X.basicOpen_le (s i) hi
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, (hmem i hy).1 hi⟩
    · intro h
      obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 h
      have hy : y ∈ j ⁻¹ᵁ B.U (k PUnit.unit) := Set.mem_iInter.1 (XK.basicOpen_le (t.f k) hk) PUnit.unit
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨k PUnit.unit, (hmem (k PUnit.unit) hy).2 hk⟩

end GlobalTheory.GenSecInt

theorem GlobalTheory.GenSecInt.main : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (B : LB X), B.IsLB → ∀ t : (B.pull (Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)))).Sec, ∃ s : B.Sec, ∀ y : ↥(Limits.pullback (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ))), (Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ))) y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s ↔ y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus t := by
  intro k _ X _ p D h B hB t
  haveI := h.isNoetherian
  have H : IsPullback (Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)))
      (Limits.pullback.snd (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)))
      (p ≫ spMap (Int.castRingHom k)) (spMap (algebraMap ℤ ℚ)) := IsPullback.of_hasPullback _ _
  exact GlobalTheory.GenSecInt.exists_sec H h.charZero B hB t
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

namespace GlobalTheory

theorem unitary_diag_one_mem_dbl : ∀ (R E : Type) [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) (β : Type)
    [Fintype β] [DecidableEq β] (J : Matrix β β E) (g : UG c J), ∃ gd : UG c (dbl J),
    ((gd : GL (β ⊕ β) E) : Matrix (β ⊕ β) (β ⊕ β) E) = Matrix.fromBlocks ((g : GL β E) : Matrix β β E) 0 0 1 := by
  intro R E _ _ _ c β _ _ J g
  have hg : ((g : GL β E) : Matrix β β E)ᵀ * J * ((g : GL β E) : Matrix β β E).map c = J := g.2
  have h1 : ((g : GL β E) : Matrix β β E) * (((g : GL β E)⁻¹ : GL β E) : Matrix β β E) = 1 := Units.mul_inv _
  have h2 : (((g : GL β E)⁻¹ : GL β E) : Matrix β β E) * ((g : GL β E) : Matrix β β E) = 1 := Units.inv_mul _
  have hm1 : (1 : Matrix β β E).map c = 1 := Matrix.map_one _ (map_zero c) (map_one c)
  have hm0 : (0 : Matrix β β E).map c = 0 := Matrix.map_zero _ (map_zero c)
  refine ⟨⟨⟨Matrix.fromBlocks ((g : GL β E) : Matrix β β E) 0 0 1,
    Matrix.fromBlocks (((g : GL β E)⁻¹ : GL β E) : Matrix β β E) 0 0 1, ?_, ?_⟩, ?_⟩, rfl⟩
  · rw [Matrix.fromBlocks_multiply]; simp [h1, Matrix.fromBlocks_one]
  · rw [Matrix.fromBlocks_multiply]; simp [h2, Matrix.fromBlocks_one]
  · show (Matrix.fromBlocks ((g : GL β E) : Matrix β β E) 0 0 1)ᵀ * dbl J *
        (Matrix.fromBlocks ((g : GL β E) : Matrix β β E) 0 0 1).map c = dbl J
    rw [dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, hm0, hm1, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply]
    simp [hg]

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.ConjSch

open scoped Classical

noncomputable def conjSch {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : SchwartzMap V ℂ) : SchwartzMap V ℂ where
  toFun x := star (f x)
  smooth' := (Complex.conjLIE.toContinuousLinearEquiv.contDiff).comp f.smooth'
  decay' := by
    intro k n
    obtain ⟨C, hC⟩ := f.decay' k n
    refine ⟨C, fun x => ?_⟩
    have e : (fun x => star (f x)) = Complex.conjLIE ∘ f := rfl
    rw [e, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
    exact hC x

theorem conjSch_apply {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : SchwartzMap V ℂ) (x : V) :
    conjSch f x = star (f x) := rfl

theorem star_mem_schA {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    ∀ Φ ∈ schA F κ, (fun x => star (Φ x)) ∈ schA F κ := by
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    refine Submodule.subset_span ⟨conjSch f, fun y => star (g y),
      ⟨hg.1.comp _, hg.2.comp_left (g := star) (star_zero _)⟩, ?_⟩
    funext y
    simp only [pureA, conjSch_apply, star_mul', mul_comm]
  | zero =>
    simp only [Pi.zero_apply, star_zero]
    exact (schA F κ).zero_mem
  | add x y _ _ hx hy =>
    have := (schA F κ).add_mem hx hy
    convert this using 1
    funext z; simp
  | smul c x _ hx =>
    have := (schA F κ).smul_mem (star c) hx
    convert this using 1
    funext z; simp [star_mul', mul_comm]

end GlobalTheory.ConjSch

theorem GlobalTheory.star_mem_schA_main : ∀ {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ], ∀ Φ ∈ schA F κ, (fun x => star (Φ x)) ∈ schA F κ :=
  fun κ _ => GlobalTheory.ConjSch.star_mem_schA κ
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

namespace GlobalTheory.ThetaBox

theorem thetaSum_boxFun : ∀ (F : Type) [Field F] [NumberField F] (κ κ' : Type) [Fintype κ] [Fintype κ'], ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ', thetaSum F (boxFun φ₁ φ₂) = thetaSum F φ₁ * thetaSum F φ₂ := by
  intro F _ _ κ κ' _ _ φ₁ h₁ φ₂ h₂
  have s₁ := (thetaSum_summable_linear F κ).2.1 φ₁ h₁
  have s₂ := (thetaSum_summable_linear F κ').2.1 φ₂ h₂
  unfold thetaSum
  rw [tsum_mul_tsum_of_summable_norm s₁ s₂]
  rw [← (Equiv.sumArrowEquivProdArrow κ κ' F).symm.tsum_eq]
  rfl

end GlobalTheory.ThetaBox
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun MeasureTheory Topology
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem schwartzBruhat_matrix_lintegral_sq_ne_zero_ne_top : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {a d : ℕ}
    (Φ : Matrix (Fin a) (Fin d) k → ℂ), Φ ∈ SB (Matrix (Fin a) (Fin d) k) → Φ ≠ 0 →
    ∀ ν : @Measure (Matrix (Fin a) (Fin d) k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
      ∫⁻ Y, ‖Φ Y‖ₑ ^ 2 ∂ν ≠ 0 ∧ ∫⁻ Y, ‖Φ Y‖ₑ ^ 2 ∂ν ≠ ⊤ := by
  intro k _ _ _ _ a d Φ hΦ h0 ν hν
  letI : MeasurableSpace (Matrix (Fin a) (Fin d) k) := borel _
  haveI : BorelSpace (Matrix (Fin a) (Fin d) k) := ⟨rfl⟩
  obtain ⟨hlc, hcs⟩ : IsLocallyConstant Φ ∧ HasCompactSupport Φ := hΦ
  have hc : Continuous Φ := hlc.continuous
  have hcont : Continuous fun Y => ‖Φ Y‖ₑ ^ 2 :=
    (ENNReal.continuous_pow 2).comp hc.enorm
  constructor
  · intro h
    rw [lintegral_eq_zero_iff hcont.measurable] at h
    have h' := (Continuous.ae_eq_iff_eq ν hcont continuous_zero).1 h
    apply h0
    funext Y
    have := congrFun h' Y
    simpa using this
  · obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hcs
    have hle : ∫⁻ Y, ‖Φ Y‖ₑ ^ 2 ∂ν ≤
        ∫⁻ Y, (tsupport Φ).indicator (fun _ => ENNReal.ofReal C ^ 2) Y ∂ν := by
      refine lintegral_mono fun Y => ?_
      by_cases hY : Y ∈ tsupport Φ
      · rw [Set.indicator_of_mem hY]
        gcongr
        rw [← ofReal_norm_eq_enorm]
        exact ENNReal.ofReal_le_ofReal (hC Y)
      · simp [image_eq_zero_of_notMem_tsupport hY]
    refine ne_top_of_le_ne_top ?_ hle
    rw [lintegral_indicator_const (isClosed_tsupport Φ).measurableSet]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      (IsCompact.measure_lt_top hcs).ne

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

noncomputable section

namespace GlobalTheory.SchANonzero

theorem exists_schwartz_one (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    ∃ Φ : SchwartzMap V ℂ, Φ 0 = 1 := by
  let b : ContDiffBump (0 : V) := ⟨1, 2, one_pos, one_lt_two⟩
  have h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  refine ⟨h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff), ?_⟩
  change ((b 0 : ℝ) : ℂ) = 1
  rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]
  simp

def intPts (F : Type) [Field F] [NumberField F] (κ : Type) : Set (κ → FiniteAdeleRing (𝓞 F) F) :=
  Set.pi Set.univ fun _ => {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ v.adicCompletionIntegers F}

theorem isOpen_intPts (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] : IsOpen (intPts F κ) :=
  isOpen_set_pi Set.finite_univ fun _ _ =>
    RestrictedProduct.isOpen_forall_mem
      (A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      (fun v => Valued.isOpen_valuationSubring _)

theorem isCompact_intPts (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] : IsCompact (intPts F κ) :=
  isCompact_univ_pi fun _ => GlobalTheory.AdeleCocompact.isCompact_integral F

theorem isClosed_intPts (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] : IsClosed (intPts F κ) := by
  haveI : T2Space (FiniteAdeleRing (𝓞 F) F) :=
    inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite))
  exact (isCompact_intPts F κ).isClosed

theorem indicator_intPts_mem_SB (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    (intPts F κ).indicator (1 : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  refine ⟨?_, HasCompactSupport.intro' (isCompact_intPts F κ) (isClosed_intPts F κ)
    fun x hx => Set.indicator_of_notMem hx _⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  by_cases hx : x ∈ intPts F κ
  · exact ⟨intPts F κ, isOpen_intPts F κ, hx, fun y hy => by
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]; rfl⟩
  · exact ⟨(intPts F κ)ᶜ, (isClosed_intPts F κ).isOpen_compl, hx, fun y hy => by
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩

theorem exists_mem_schA_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    ∃ φ ∈ schA F κ, φ 0 ≠ 0 := by
  intro F _ _ κ _
  classical
  obtain ⟨f, hf⟩ := exists_schwartz_one (κ → mixedEmbedding.mixedSpace F)
  refine ⟨pureA F f ((intPts F κ).indicator 1), Submodule.subset_span ⟨f, _, indicator_intPts_mem_SB F κ, rfl⟩, ?_⟩
  have h0 : (fun i : κ => ((0 : κ → AdeleRing (𝓞 F) F) i).2) ∈ intPts F κ := fun i _ v => by
    show (0 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F
    exact zero_mem (v.adicCompletionIntegers F)
  simp only [pureA]
  rw [Set.indicator_of_mem h0]
  have hz : (fun i : κ => InfiniteAdeleRing.ringEquiv_mixedSpace F ((0 : κ → AdeleRing (𝓞 F) F) i).1) = 0 := by
    funext i
    show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
    exact map_zero _
  rw [hz, hf]
  simp

end GlobalTheory.SchANonzero
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Vert GlobalTheory.Vert.Model GlobalTheory.VB
open GlobalTheory.Twist (resM resM_resM resM_self app_resM)
open GlobalTheory.QCoh (appLinear appLinear_apply)

namespace GlobalTheory.SubPull

theorem app_injective_of_frames {X : Scheme.{0}} {F E : X.Modules} (φ : F ⟶ E) {U V : X.Opens}
    {ι κ : Type} [Fintype ι] [Fintype κ] {e : ι → Γ(F, U)} {b : ι ⊕ κ → Γ(E, U)}
    (he : IsFrame e) (hb : IsFrame b) (hφ : ∀ j, φ.app U (e j) = b (.inl j)) (h : V ≤ U) :
    Function.Injective (φ.app V) := by
  have li : LinearIndependent Γ(X, V) (appLinear φ V ∘ he.basis h) := by
    have := (hb.basis h).linearIndependent.comp Sum.inl Sum.inl_injective
    convert this using 1
    funext j
    simp only [Function.comp_apply, IsFrame.basis_apply, appLinear_apply, app_resM, hφ]
  have : Function.Injective (appLinear φ V) := by
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    have h0 := Fintype.linearIndependent_iff.1 li ((he.basis h).repr x) (by
      rw [← hx]
      conv_rhs => rw [← (he.basis h).sum_repr x]

      simp only [map_sum, map_smul, Function.comp_apply])
    exact (he.basis h).ext_elem fun j => by simp [h0 j]
  exact this

theorem isSubbundle_pullback : ∀ (X Y : Scheme.{0}) (f : Y ⟶ X) (F E : X.Modules) (i : F ⟶ E) (r : ℕ), IsVB F r → IsSubbundle i → IsSubbundle ((Scheme.Modules.pullback f).map i) := by
  intro X Y f F E i r hF ⟨hm, s, hs⟩
  have hS : (ShortComplex.mk i (cokernel.π i) (cokernel.condition i)).ShortExact :=
    { exact := ShortComplex.exact_cokernel i }
  refine ⟨QCoh.mono_of_locally_app_injective _ fun W y hy => ?_, s,
    (hs.pullback f).of_iso (PreservesCokernel.iso (Scheme.Modules.pullback f) i)⟩
  have h₁ : SheafOfModules.IsQuasicoherent
      (ShortComplex.mk i (cokernel.π i) (cokernel.condition i)).X₁ := hF.isQuasicoherent
  have h₂ : SheafOfModules.IsQuasicoherent
      (ShortComplex.mk i (cokernel.π i) (cokernel.condition i)).X₂ :=
    (VBExt.isVB_and_cls_det_of_shortExact X _ r s hS hF hs).1.isQuasicoherent
  obtain ⟨c, hc⟩ := VBExt.exists_adaptedChart hS hF hs (f y)
  refine ⟨W ⊓ f ⁻¹ᵁ c.U, ⟨hy, hc⟩, inf_le_left, ?_⟩
  exact app_injective_of_frames _ (c.he.pullback f)
    ((VBExt.isFrame_sumElim hS c.he c.ht).pullback f)
    (fun j => QCoh.pullback_map_app_pullbackSections f i _ _) inf_le_right

end GlobalTheory.SubPull
end
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem _root_.GlobalTheory.T.intersectionNumber_nonneg_of_nef_ample_add_nef : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → (∀ A N : LB X, IsAmpleLB A → IsNef k N → IsAmpleLB (tens A N)) → ∀ (d : ℕ) (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d : ℕ) → ∀ P : Fin d → LB X, (∀ i, IsNef k (P i)) → 0 ≤ interNum k F P := by
  first | exact @GlobalTheory.interNum_nonneg_of_isNef_of_ample_tens_nef | exact GlobalTheory.interNum_nonneg_of_isNef_of_ample_tens_nef | (intros; apply GlobalTheory.interNum_nonneg_of_isNef_of_ample_tens_nef <;> assumption)
end

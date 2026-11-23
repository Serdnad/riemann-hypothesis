module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle086
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle176
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HermitianPeriodLinearAlgebra
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle030
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle252
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle156
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle172
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PeriodHermitianTypeCompatibility
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle009
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjEmbRtOfNe
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle207
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle215
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle253
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LawsProved
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GeoRead

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.hol_unif_period_matrix_middle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (g n : ℕ) (M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : Flat.FamExp t.G M B ψ) (b : Fin n → ℂ) (P : AbPart t (spMap (ψ b))) (A : Over (Sp ℂ)) (_ : GrpObj A) (φ : A.left ⟶ P.tB.G.left) (g' : ℕ) (u : HolUnif A (P.tB.PP.L.pull φ) g') (Hm : Matrix (Fin g') (Fin g') ℂ) (χ : u.Λ → ℂ) (ℓ : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)), b ∈ B → IsGrpPullback A P.tB.G (𝟙 _) φ → u.IsAH Hm χ → IsPrincipal P.tB → GlobalTheory.CompanionTheory.Ar.QuotLoc.IsAbLift e b P φ u ℓ → ∀ (N : ℕ) (ζ : ℂˣ) (y y' : Fin g → ℂ), 0 < N → y ∈ e.per b → y' ∈ e.per b → GlobalTheory.UU.CubWeil t.cub N (e.ex b ((N : ℂ)⁻¹ • y)) (e.ex b ((N : ℂ)⁻¹ • y')) (unitOn ζ) → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (((ℓ y ⬝ᵥ Hm *ᵥ star (ℓ y')).im : ℝ) : ℂ) / N) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.QuotLoc.Pair.cubWeil_eq_exp_riemann | exact GlobalTheory.CompanionTheory.Ar.QuotLoc.Pair.cubWeil_eq_exp_riemann | (intros; apply GlobalTheory.CompanionTheory.Ar.QuotLoc.Pair.cubWeil_eq_exp_riemann <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

theorem abPart_exists (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S)
    (L : Type) [Field L] [NumberField L] (z : Sp L ⟶ S) :
    ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (e : L →+* L'), Nonempty (AbPart t (spMap e ≫ z)) := by
  obtain ⟨L', _, _, hfin, ⟨τ⟩⟩ := GlobalTheory.T.exists_torus_extension_finite S t.G t.semi L z
  have : CharZero L' := charZero_of_injective_algebraMap (algebraMap L L').injective
  have : NumberField L' := NumberField.of_module_finite L L'
  obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull Out.proved_CubePullSt (spMap (algebraMap L L') ≫ z) t
  obtain ⟨tB, e, he, ha, hp⟩ := GlobalTheory.T.torus_extension_abelian_quotient E H L'
    ⟨(Over.pullback (spMap (algebraMap L L') ≫ z)).obj t.G, IsSemiAbelian.pullback _ t.G t.semi,
      OAct.pullback _ t.G t.act, PP', cub, sym, adj, prim⟩ τ
  exact ⟨L', _, inferInstance, algebraMap L L', ⟨⟨_, m, τ, tB, e, he, ha, hp⟩⟩⟩

end GlobalTheory.CompanionTheory.Ar
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.TrivialModel

theorem exists_model_of_rank_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (t : SAB H (Sp L)), IsPrincipal t → (∀ (σ : L →+* ℂ) (τ : 𝓞 E →+* ℂ), LieMult t.act (spMap σ) τ 0) → ∃ t' : SAB H (Sp (𝓞 L)), Nonempty (SABMap t t' (spMap (algebraMap (𝓞 L) L))) :=
  @PositivityTheory.Xgn.trivial_type_good_reduction

end GlobalTheory.CompanionTheory.Ar.TrivialModel
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.SabModel

theorem datum_tate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] (t : SAB H (Sp L)), IsPrincipal t → ∀ (σ : L →+* ℂ) (p q : ℕ), (∀ τ : 𝓞 E →+* ℂ, (τ H.rt = H.rt0 → LieMult t.act (spMap σ) τ p) ∧ (τ H.rt ≠ H.rt0 → LieMult t.act (spMap σ) τ q)) → ∃ D : Datum H, D.p = p ∧ D.q = q ∧ Nonempty (TateIso D ℂ (Over.mk (spMap σ) ⟶ t.G) (fun a g => g ≫ t.act.act a) (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c))) :=
  @PositivityTheory.Xgn.shimura_datum_tate_isomorphism

end GlobalTheory.CompanionTheory.Ar.SabModel
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.SabModel

theorem obj_of_sections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (F : IntermediateField ℚ ℂ) (hK : KA l ≤ F) (t : SAB H (Sp F)), IsPrincipal t → l.A = 1 → (∀ (k : Type) [Field k] [IsAlgClosed k] (g : F →+* k) (τ : 𝓞 E →+* k), (τ H.rt = g (IntermediateField.inclusion hK (baseKA l).ρ) → LieMult t.act (spMap g) τ D.p) ∧ (τ H.rt ≠ g (IntermediateField.inclusion hK (baseKA l).ρ) → LieMult t.act (spMap g) τ D.q)) → ∀ I : TateIso D ℂ (Over.mk (spMap (algebraMap F ℂ)) ⟶ t.G) (fun a g => g ≫ t.act.act a) (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)), (∀ a : D.La, ∃ s : 𝟙_ (Over (Sp F)) ⟶ t.G, toUnit _ ≫ s = I.ev l.M a) → ∃ o : Obj D l (baseKA l) (spMap (IntermediateField.inclusion hK).toRingHom), o.t = t :=
  @PositivityTheory.Xgn.model_object_sections

end GlobalTheory.CompanionTheory.Ar.SabModel
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

open Matrix GlobalTheory.CompanionTheory.Ar.LinFlat
open scoped ComplexOrder

theorem det_rows_mul_det_rows {p q : ℕ} (A C : Matrix (Fin p) (Fin q ⊕ Fin p) ℂ)
    (F : Matrix (Fin q) (Fin q ⊕ Fin p) ℂ) (hAF : A * Fᵀ = 0) (hAC : A * Cᵀ = 1) :
    (fromRows (Fᵀ)ᴴ A).det * (fromRows F C).det = ((Fᵀ)ᴴ * Fᵀ).det := by
  have h : fromRows (Fᵀ)ᴴ A * (fromRows F C)ᵀ = fromBlocks ((Fᵀ)ᴴ * Fᵀ) ((Fᵀ)ᴴ * Cᵀ) 0 1 := by
    rw [transpose_fromRows, fromRows_mul_fromCols, hAF, hAC]
  rw [← det_transpose (fromRows F C), ← det_mul, h, det_fromBlocks_zero₂₁]
  simp

theorem norm_core {p q g : ℕ} (V : Fin p → Fin g → ℂ) (W : Fin q → Fin g → ℂ)
    (U U' : Fin p ⊕ Fin q → Fin g → ℂ) (S : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) (hS : S.det ≠ 0)
    (hV : LinearIndependent ℂ V) (hW : LinearIndependent ℂ W)
    (hU : ∀ n, U n ∈ Submodule.span ℂ (Set.range V))
    (C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ) (Fm B : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ)
    (hB : ∀ n, U' n = ∑ j, B j n • W j) (hFm : ∀ j n, ∑ m, Fm j m * S m n = B j n)
    (hC : ∀ a, ∑ m, C a m • U m = V a)
    (hR : ∀ m n, hermForm Hm (U m) (U n) - star (hermForm Hm (U' m) (U' n)) = 2 * Complex.I * S m n)
    (Γ : Matrix (Fin p) (Fin p) ℂ) (Δ : Matrix (Fin q) (Fin q) ℂ)
    (hΓ : ∀ a b, Γ a b = Real.pi * hermForm Hm (V a) (V b))
    (hΔ : ∀ a b, Δ a b = Real.pi * hermForm Hm (W a) (W b)) :
    ‖Γ.det‖ = ‖(fromRows C Fm).det‖ ^ 2 *
      ((2 * Real.pi) ^ p * (2 * Real.pi)⁻¹ ^ q * ‖S.det‖) * ‖Δ.det‖ := by
  choose a ha using fun n => (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hU n)
  let A : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ := Matrix.of fun i n => a n i
  have hA : ∀ n, ∑ i, A i n • V i = U n := ha
  clear_value A
  set H₁ : Matrix (Fin p) (Fin p) ℂ := Matrix.of fun i j => hermForm Hm (V i) (V j) with hH₁
  set H₂ : Matrix (Fin q) (Fin q) ℂ := Matrix.of fun i j => hermForm Hm (W i) (W j) with hH₂
  have pd₁ : H₁.PosDef := gram_posDef Hm hH hpos V hV
  have pd₂ : H₂.PosDef := gram_posDef Hm hH hpos W hW
  have hrel : Aᵀ * H₁ * A.map star - (Bᵀ * H₂ * B.map star)ᵀ = (2 * Complex.I) • S := by
    ext m n
    rw [Matrix.sub_apply, Matrix.transpose_apply, gram_expand, gram_expand, hA, hA, ← hB, ← hB,
      ← star_hermForm hH (U' m) (U' n), hR m n]
    simp
  let e : Fin q ⊕ Fin p ≃ Fin p ⊕ Fin q := Equiv.sumComm _ _
  have hrel' : (A.submatrix id e)ᵀ * H₁ * (A.submatrix id e).map star -
      ((B.submatrix id e)ᵀ * H₂ * (B.submatrix id e).map star)ᵀ =
      (2 * Complex.I) • S.submatrix e e := by
    ext m n
    have := congrFun (congrFun hrel (e m)) (e n)
    simpa [Matrix.mul_apply] using this
  have hdet : (S.submatrix e e).det ≠ 0 := by rwa [Matrix.det_submatrix_equiv_self]
  obtain ⟨t₁, -, -, t₄⟩ := GlobalTheory.T.riemann_form_period_determinant p q (A.submatrix id e) (B.submatrix id e)
    (S.submatrix e e) H₁ H₂ pd₁ pd₂ hdet hrel'
  have hFS : Fm * S = B := by
    ext j n
    rw [Matrix.mul_apply, hFm]
  have hN : ((S.submatrix e e)ᵀ)⁻¹ * (B.submatrix id e)ᵀ = (Fm.submatrix id e)ᵀ := by
    have h1 : B.submatrix id e = Fm.submatrix id e * S.submatrix e e := by
      rw [Matrix.submatrix_mul_equiv, hFS]
    have hu : IsUnit ((S.submatrix e e)ᵀ).det := by
      rw [Matrix.det_transpose]; exact isUnit_iff_ne_zero.mpr hdet
    rw [h1, Matrix.transpose_mul, Matrix.nonsing_inv_mul_cancel_left _ _ hu]
  rw [hN] at t₁ t₄
  have hCA : C * Aᵀ = 1 := by
    ext i k
    have hexp : ∑ m, C i m • U m = ∑ k, (C * Aᵀ) i k • V k := by
      simp_rw [← hA, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.mul_apply, Finset.sum_smul]
      rfl
    have := coef_unique hV (fun k => (C * Aᵀ) i k) (fun k => (1 : Matrix _ _ ℂ) i k)
      (by rw [← hexp, hC i]; simp [Matrix.one_apply])
    exact congrFun this k
  have hAC : A.submatrix id e * (C.submatrix id e)ᵀ = 1 := by
    have h1 : C.submatrix id e * (A.submatrix id e)ᵀ = 1 := by
      rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, hCA]
      simp
    have := congrArg Matrix.transpose h1
    simpa [Matrix.transpose_mul] using this
  have hG : (fromRows (Fm.submatrix id e) (C.submatrix id e)).det = (fromRows C Fm).det := by
    have : fromRows (Fm.submatrix id e) (C.submatrix id e) = (fromRows C Fm).submatrix e e := by
      ext (i | i) n <;> simp [e]
    rw [this, Matrix.det_submatrix_equiv_self]
  have hmul := det_rows_mul_det_rows _ _ _ t₁ hAC
  rw [hG] at hmul
  set d := (fromRows C Fm).det with hd
  set X := (((Fm.submatrix id e)ᵀ)ᴴ * (Fm.submatrix id e)ᵀ).det with hX
  set M := (fromRows ((Fm.submatrix id e)ᵀ)ᴴ (A.submatrix id e)).det with hM
  have hSd : ‖(S.submatrix e e).det‖ = ‖S.det‖ := by rw [Matrix.det_submatrix_equiv_self]
  rw [hSd] at t₄
  have p₁ : 0 < H₁.det := pd₁.det_pos
  have p₂ : 0 < H₂.det := pd₂.det_pos
  have r₁ : 0 < H₁.det.re := (Complex.pos_iff.mp p₁).1
  have r₂ : 0 < H₂.det.re := (Complex.pos_iff.mp p₂).1
  have n₁ : ‖H₁.det‖ = H₁.det.re := by
    rw [← Complex.abs_re_eq_norm.mpr (Complex.pos_iff.mp p₁).2.symm, abs_of_pos r₁]
  have n₂ : ‖H₂.det‖ = H₂.det.re := by
    rw [← Complex.abs_re_eq_norm.mpr (Complex.pos_iff.mp p₂).2.symm, abs_of_pos r₂]
  have hSp : 0 < ‖S.det‖ := norm_pos_iff.mpr hS
  have hc : 0 < (2 : ℝ) ^ p * (2 : ℝ)⁻¹ ^ q * ‖S.det‖ * H₂.det.re := by positivity
  have hXne : X ≠ 0 := by
    intro h0
    rw [h0, div_zero, norm_zero] at t₄
    have h00 : (2 : ℝ) ^ p * (2 : ℝ)⁻¹ ^ q * ‖S.det‖ * H₂.det.re = 0 := by rw [← t₄]; simp
    exact hc.ne' h00
  have hdne : d ≠ 0 := fun h0 => hXne (by rw [← hmul, h0, mul_zero])
  have hq : M / X = d⁻¹ := by
    have hMne : M ≠ 0 := fun h0 => hXne (by rw [← hmul, h0, zero_mul])
    rw [← hmul]
    field_simp
  have hΓ' : Γ = (Real.pi : ℂ) • H₁ := by ext a b; simp [hΓ, hH₁]
  have hΔ' : Δ = (Real.pi : ℂ) • H₂ := by ext a b; simp [hΔ, hH₂]
  have hpi : ‖(Real.pi : ℂ)‖ = Real.pi := by simp [abs_of_pos Real.pi_pos]
  rw [hΓ', hΔ', Matrix.det_smul, Matrix.det_smul, norm_mul, norm_mul, norm_pow, norm_pow, hpi, n₁, n₂]
  simp only [Fintype.card_fin]
  rw [hq, norm_inv] at t₄
  have hdn : 0 < ‖d‖ := norm_pos_iff.mpr hdne
  have t₅ : H₁.det.re = ‖d‖ ^ 2 * (2 ^ p * (2 : ℝ)⁻¹ ^ q * ‖S.det‖ * H₂.det.re) := by
    rw [← t₄]; field_simp
  rw [t₅, mul_pow, inv_pow, inv_pow, mul_pow]
  have := Real.pi_pos
  field_simp

theorem hodgeNorm_flat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (τ τ' : E →+* ℂ) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), IsTypeFn H D.p D.q ty → τ' (H.rt : E) = H.rt0 → (∀ a : 𝓞 E, σ (tauIn c τ a) = τ' (a : E)) → ∀ (i : Fin FU.n) (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La), LinearIndependent (𝓞 E) e → ∃ t : ℝ, 0 < t ∧ ∀ (ρ : ℂ) (Φ : CFn Xo c), IsFlatAn Set.univ τ τ' σ Φ FU i e ρ → ∀ (P : (FU.Di i).La →+ (Fin g → ℂ)) (y : Sp ℂ ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q) (Γ : Matrix (Fin D.p) (Fin D.p) ℂ) (Δ : Matrix (Fin D.q) (Fin D.q) ℂ), IsPeriod (FU.Di i) ty P → under y = FU.u i P → IsFramed Set.univ τ σ y v w → IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L (under y) v Γ → IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L (under y) w Δ → ‖Φ y v w‖ ^ 2 * ‖Γ.det‖ = ‖ρ‖ ^ 2 * t * ‖Δ.det‖ := by
  intro E _ _ _ H D l Xo c τ τ' σ g ty FU hty hrt hτ i e he
  let S : Matrix (Fin D.p ⊕ Fin D.q) (Fin D.p ⊕ Fin D.q) ℂ :=
    Matrix.of fun m n => τ' (sesq (FU.Di i) (e m) (e n))
  have hSne : ∀ P : (FU.Di i).La →+ (Fin g → ℂ), IsPeriod (FU.Di i) ty P → S.det ≠ 0 := by
    intro P hP
    obtain ⟨Hm, hHh, -, hHi⟩ := id hP.2.2.2.2
    obtain ⟨-, -, hd⟩ := GlobalTheory.CompanionTheory.Ar.Flat.riemann_tau_component E H (FU.Di i) g ty P Hm hP hHh hHi
    have hcard : Fintype.card (Fin D.p ⊕ Fin D.q) = (FU.Di i).p + (FU.Di i).q := by
      rw [(FU.sig i).1, (FU.sig i).2]; simp
    have := hd 0 _ e hcard he
    have h2 : S = (Matrix.of fun m n => sesq (FU.Di i) (e m) (e n)).map τ' := rfl
    rw [h2, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero τ').2 this
  by_cases hS0 : S.det = 0
  · refine ⟨1, one_pos, ?_⟩
    intro ρ Φ _ P y v w Γ Δ hP
    exact absurd hS0 (hSne P hP)
  refine ⟨(2 * Real.pi) ^ D.p * (2 * Real.pi)⁻¹ ^ D.q * ‖S.det‖, ?_, ?_⟩
  · have := norm_pos_iff.mpr hS0
    have := Real.pi_pos
    positivity
  intro ρ Φ hΦ P y v w Γ Δ hP hy hfr hΓ hΔ
  obtain ⟨⟨V₀, W₀, Fm, B, d⟩, ⟨k1, k2, k3, k4, -, ⟨C, k6⟩, k7⟩, -⟩ :=
    GlobalTheory.T.uniformised_eigen_frame_one E H D l Xo c τ τ' σ g ty FU hty hrt hτ i e P y v w he hP hy hfr
  simp only at k1 k2 k3 k4 k6 k7
  have hflat : Φ y v w * (Matrix.fromRows C Fm).det = ρ :=
    hΦ P y v w V₀ W₀ C Fm B hP hy hfr k1 k2 k6 k3 k4
  obtain ⟨-, -, hv, hw⟩ := id hfr
  have hc : ∀ a : 𝓞 E, (σ.comp (tauIn c (ComplexEmbedding.conjugate τ))) a = ComplexEmbedding.conjugate τ' (a : E) := by
    intro a
    have h1 : tauIn c (ComplexEmbedding.conjugate τ) a = tauIn c τ (H.bar a) := by
      apply Subtype.ext
      show ComplexEmbedding.conjugate τ (a : E) = τ ((H.bar a : 𝓞 E) : E)
      rw [H.bar_eq, IsCMField.complexEmbedding_complexConj]
      rfl
    show σ (tauIn c (ComplexEmbedding.conjugate τ) a) = _
    rw [h1, hτ, H.bar_eq, IsCMField.complexEmbedding_complexConj]
    rfl
  obtain ⟨V, hVd, hVl, hVs⟩ := GlobalTheory.T.period_eigen_frame E H D l Xo _ g ty FU i P (under y) (σ.comp (tauIn c τ)) τ' D.p v hP hy hτ hv
  obtain ⟨W, hWd, hWl, -⟩ := GlobalTheory.T.period_eigen_frame E H D l Xo _ g ty FU i P (under y) _ (ComplexEmbedding.conjugate τ') D.q w hP hy hc hw
  have eV : V₀ = V := funext fun a => (hVd a _).1 (k1 a)
  have eW : W₀ = W := funext fun a => (hWd a _).1 (k2 a)
  subst eV eW
  obtain ⟨Hm, hHh, hHp, hHi⟩ := id hP.2.2.2.2
  obtain ⟨-, hs, -⟩ := GlobalTheory.CompanionTheory.Ar.Flat.riemann_tau_component E H (FU.Di i) g ty P Hm hP hHh hHi
  have hΓ' := (GlobalTheory.CompanionTheory.Ar.Flat.hodgeGram_iff_period E H D l Xo _ g ty FU i P Hm hP hHh hHi (under y) hy D.p v V₀ Γ k1).1 hΓ
  have hΔ' := (GlobalTheory.CompanionTheory.Ar.Flat.hodgeGram_iff_period E H D l Xo _ g ty FU i P Hm hP hHh hHi (under y) hy D.q w W₀ Δ k2).1 hΔ
  have hlin : IsLinearMap ℂ (tyPart ty τ') := by
    constructor
    · intro a b; funext k; simp only [tyPart, Pi.add_apply]; split_ifs <;> simp
    · intro a b; funext k; simp only [tyPart, Pi.smul_apply]; split_ifs <;> simp
  have hC : ∀ a, ∑ m, C a m • tyPart ty τ' (P (e m)) = V₀ a := by
    intro a
    rw [← k6 a]
    have := map_sum (hlin.mk' _) (fun m => C a m • P (e m)) Finset.univ
    simpa [hlin.map_smul] using this.symm
  have key := norm_core V₀ W₀ (fun n => tyPart ty τ' (P (e n)))
    (fun n => tyPart ty (ComplexEmbedding.conjugate τ') (P (e n))) S Hm hHh hHp hS0 hVl hWl
    (fun n => hVs _) C Fm B k3 k4 hC (fun m n => hs τ' _ _) Γ Δ hΓ' hΔ'
  rw [key, ← hflat, norm_mul]
  ring

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

theorem _root_.GlobalTheory.T.hodge_tate_free_flag_lattice_lower : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (hpq : 0 < D.p + D.q) (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)), ∃ (Dc : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, HTChart (chartRing o (mseg y) s.1) Ω (cmConj E) p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li)), IsHTFamily 𝔐 p o Dc ∧ ∀ (s : {s : ∀ k, J k // mseg y s ≠ 0}) (κ : chartRing o (mseg y) s.1), PointHT → IsCp p (κ : Ω) → (Dc s).HasTestPoints κ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.hodgeTate_family_exists | exact GlobalTheory.CompanionTheory.Ar.HT.hodgeTate_family_exists | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.hodgeTate_family_exists <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

theorem hodgeLattices_isVBOn_overPrime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime], p ∈ S → ¬ (p : ℤ) ∣ NumberField.discr E → (∀ (t : CMType H ⊕ CMType H) (q : Cpt 𝔐.ξ), (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q) → 𝔐.HT p t q = 𝔐.dR t q) → ∀ t : CMType H ⊕ CMType H, (𝔐.dR t).IsVBOn (overPrime 𝔐.ξ p) (labelRk D t) (𝔐.Vgen t) ∧ (𝔐.HT p t).IsVBOn (overPrime 𝔐.ξ p) (labelRk D t) (𝔐.Vgen t) :=
  PositivityTheory.Xgn.vector_bundle_lattice_labels

end GlobalTheory.CompanionTheory.Ar.Num.FamEx
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.RigScale

open GlobalTheory GlobalTheory.ArchMetricCompare

theorem eSec_comp_of_cart {S : Scheme.{0}} {G : Over S} [GrpObj G] {z : Sp ℂ ⟶ S} {A : Over (Sp ℂ)} [GrpObj A]
    {φ : A.left ⟶ G.left} (h : IsGrpPullback A G z φ) : eSec A ≫ φ = z ≫ eSec G := by
  have e := congrArg (fun q => q.left) (map_one (pushHom h (𝟙_ (Over (Sp ℂ)))))
  have e₁ : (1 : 𝟙_ (Over (Sp ℂ)) ⟶ A) = η[A] := by rw [Hom.one_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  show (toUnit _ ≫ η[G]).left = _
  simp [eSec]

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

def scale (u : HolUnif A L g) (c : ℂ) (hc : c ≠ 0) : HolUnif A L g :=
  { u with
    fr := fun j w => c * u.fr j w
    fr_hol := fun i => (u.fr_hol i).const_mul c
    fr_ne := fun i z h => mul_ne_zero hc (u.fr_ne i z h)
    fr_compat := fun i j z h => by
      rw [u.fr_compat i j z h]
      ring }

theorem scale_isAH {u : HolUnif A L g} {c : ℂ} (hc : c ≠ 0) {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    (h : u.IsAH Hm χ) : (scale u c hc).IsAH Hm χ := by
  refine ⟨h.1, h.2.1, h.2.2.1, fun l i z hz => ?_⟩
  show c * u.fr i z = _ * (c * u.fr i (z + (l : Fin g → ℂ)))
  rw [h.2.2.2 l i z hz]
  ring

end GlobalTheory.CompanionTheory.Ar.Sl.RigScale

namespace GlobalTheory.CompanionTheory.Ar.Sl

open GlobalTheory GlobalTheory.ArchMetricCompare RigScale

theorem exists_archFrame_of_isAH : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : RigLB G) (z : Sp ℂ ⟶ S) (A : Over (Sp ℂ)) [GrpObj A] (φ : A.left ⟶ G.left) (g : ℕ) (u : HolUnif A (P.L.pull φ) g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), IsGrpPullback A G z φ → u.IsAH Hm χ → Nonempty (ArchFrame P z g) := by
  intro S G _ _ P z A _ φ g u Hm χ cart ah
  have he : (u.ex 0).left ≫ φ = z ≫ eSec G := by
    have := eSec_comp_of_cart cart
    rw [show (u.ex 0).left = eSec A from GlobalTheory.CompanionTheory.Ar.Flat.PerGram.ex_zero_left u]
    exact this
  obtain ⟨i₀, h₀⟩ : ∃ i, ⊤ ≤ ((u.ex 0).left ≫ φ) ⁻¹ᵁ P.L.U i :=
    (exists_chart P.isLB (((u.ex 0).left ≫ φ) (default : PrimeSpectrum ℂ))).imp
      fun _ h => (top_le_preimage_iff_mem _ _).2 h

  have hfr : ∀ i, ⊤ ≤ ((u.ex 0).left ≫ φ) ⁻¹ᵁ P.L.U i → ⊤ ≤ (u.ex 0).left ⁻¹ᵁ (P.L.pull φ).U (fun _ => i) :=
    fun i h => (le_pull_iff P.L φ _ _).2 h
  have hz : ∀ i, ⊤ ≤ ((u.ex 0).left ≫ φ) ⁻¹ᵁ P.L.U i →
      ⊤ ≤ z ⁻¹ᵁ (P.L.pull (eSec G)).U (fun _ => i) := fun i h =>
    (le_pull_iff P.L (eSec G) z _).2 (he ▸ h)
  have hrel : ∀ i, ⊤ ≤ ((u.ex 0).left ≫ φ) ⁻¹ᵁ P.L.U i →
      valF (X := (𝟙_ (Over S)).left) z _ (P.rig.s fun _ => i).val =
        valAt' ((u.ex 0).left ≫ φ) (P.L.U i ⊓ P.L.U i₀) (P.L.g i i₀).val *
          valF (X := (𝟙_ (Over S)).left) z _ (P.rig.s fun _ => i₀).val := by
    intro i hi
    have hm : ⊤ ≤ z ⁻¹ᵁ ((P.L.pull (eSec G)).U (fun _ => i) ⊓ (P.L.pull (eSec G)).U (fun _ => i₀)) :=
      (top_le_preimage_inf _ _ _).2 ⟨hz i hi, hz i₀ h₀⟩
    have e := congrArg (fun a => valAt' z _ (Units.val a)) (P.rigGen (fun _ => i) (fun _ => i₀))
    have e2 := (valAt'_res z inf_le_left _ hm).symm.trans (e.trans ((valAt'_mul _ _ _ _).trans
      (congrArg₂ (· * ·) rfl (valAt'_res z inf_le_right _ hm))))
    rw [he]
    rw [← val_pull_g P.L (eSec G) z (fun _ => i) (fun _ => i₀) hm]
    exact e2
  have hn : valF (X := (𝟙_ (Over S)).left) z _ (P.rig.s fun _ => i₀).val ≠ 0 :=
    valAt'_unit_ne_zero z (hz i₀ h₀) _
  have hd := u.fr_ne (fun _ => i₀) 0 (hfr i₀ h₀)
  have hc : valF (X := (𝟙_ (Over S)).left) z _ (P.rig.s fun _ => i₀).val / u.fr (fun _ => i₀) 0 ≠ 0 :=
    div_ne_zero hn hd
  refine ⟨{ A := A, φ := φ, cart := cart, u := scale u _ hc, Hm := Hm, χ := χ, ah := scale_isAH hc ah, rig := ?_ }⟩
  intro i hi
  have hi' : ⊤ ≤ ((u.ex 0).left ≫ φ) ⁻¹ᵁ P.L.U i := hi
  show _ / u.fr (fun _ => i₀) 0 * u.fr (fun _ => i) 0 = _
  have hm : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ ((P.L.pull φ).U (fun _ => i) ⊓ (P.L.pull φ).U (fun _ => i₀)) :=
    (top_le_preimage_inf _ _ _).2 ⟨hfr i hi', hfr i₀ h₀⟩
  rw [u.fr_compat (fun _ => i) (fun _ => i₀) 0 hm, val_pull_g P.L φ _ (fun _ => i) (fun _ => i₀) hm, hrel i hi']
  field_simp

end GlobalTheory.CompanionTheory.Ar.Sl
end
end

section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
open AlgebraicGeometry CategoryTheory Limits
open scoped Matrix

theorem _root_.GlobalTheory.CompanionTheory.Relay.root_origin_constant_algebra_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx), letI := Small.cstAlg Or; ∀ (y₂ y' : FrPt Xo c RM.Ω), Small.ptY Y y₂ = Or.𝔐.ξ ≫ Or.𝔐.f → y'.x = y₂.x → ∀ (s : CMType H ⊕ CMType H) (w : Fin (labelRk Dw s) → Or.𝔐.Li), (∀ k, (Or.𝔐.M.pt (w k)).left ≫ Or.𝔐.m.φ = Small.tanY Y y₂ (Small.labelC s) (Small.labelFin Dw s k)) → ∀ (cf : Fin (Dw.mult (Small.labelC s)) → RM.Ω) (k : Fin (labelRk Dw s)), IsCombAt y₂.x (y₂.u (Small.labelC s)) cf (y'.u (Small.labelC s) (Small.labelFin Dw s k)) → (Or.𝔐.M.pt (∑ m, cf (Small.labelFin Dw s m) • w m)).left ≫ Or.𝔐.m.φ = Small.tanY Y y' (Small.labelC s) (Small.labelFin Dw s k) := by
  intro E _ _ _ H Dw l Xo c Y SS RM Sys Fx Or y₂ y' h₁ hx s w hw cf k hc
  letI : Algebra (↥c.F) RM.Ω := Small.cstAlg Or
  have h : labelRk Dw s = Dw.mult (Small.labelC s) := (Small.mult_labelC Dw s).symm
  have hh : Small.labelFin Dw s = Fin.cast h := by
    funext i
    exact Fin.ext (Small.labelFin_val Dw s i)
  obtain ⟨hw', hres⟩ := GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.comb_val E H Dw l Xo c _ _ Y Or.𝔐.X Or.𝔐.t
    Or.𝔐.f Or.𝔐.m RM.Ω Or.𝔐.ξ Or.𝔐.Li Or.𝔐.M y₂ h₁ (Dw.mult (Small.labelC s))
    (y₂.u (Small.labelC s)) (fun j => y₂.tan _ j) (fun j => w (Fin.cast h.symm j))
    (fun j => by rw [hw (Fin.cast h.symm j)]; rfl) cf
    (y'.u (Small.labelC s) (Small.labelFin Dw s k)) hc
  have hsum : ∑ m, cf (Small.labelFin Dw s m) • w m = ∑ j, cf j • w (Fin.cast h.symm j) := by
    rw [hh]
    exact Fintype.sum_equiv (finCongr h) _ _ (fun m => rfl)
  rw [hsum, hres]
  have hpt : Small.ptF y' = Small.ptF y₂ := by
    simp only [Small.ptF, hx]
  simp only [Small.tanY, Small.tanF, GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.tanW, hpt]
  simp only [Small.ptF, GlobalTheory.AllWt.ptF]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.hol_unif_period_matrix_left : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (g n : ℕ) (M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : Flat.FamExp t.G M B ψ) (b : Fin n → ℂ) (P : AbPart t (spMap (ψ b))) (A : Over (Sp ℂ)) (_ : GrpObj A) (φ : A.left ⟶ P.tB.G.left) (g' : ℕ) (u : HolUnif A (P.tB.PP.L.pull φ) g') (Hm : Matrix (Fin g') (Fin g') ℂ) (χ : u.Λ → ℂ), b ∈ B → IsGrpPullback A P.tB.G (𝟙 _) φ → u.IsAH Hm χ → IsPrincipal P.tB → ∃ ℓ : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ), GlobalTheory.CompanionTheory.Ar.QuotLoc.IsAbLift e b P φ u ℓ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.QuotLoc.exists_isAbLift | exact GlobalTheory.CompanionTheory.Ar.QuotLoc.exists_isAbLift | (intros; apply GlobalTheory.CompanionTheory.Ar.QuotLoc.exists_isAbLift <;> assumption)
end

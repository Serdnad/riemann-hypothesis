module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1212
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1213
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1214
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1216
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.semiPos_add_log_normSq_section_add_pos : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (N : MLine p σ), N.φ.SemiPosReg D → ∀ (t : N.B.Sec) (δ : ℝ), 0 < δ → (∀ y, CInfAt (fun y => Real.log (N.φ.nsq (secVal p σ t) y + δ)) y) ∧ (N.φ.addFn fun y => Real.log (N.φ.nsq (secVal p σ t) y + δ)).SemiPosReg D := by
  first | exact @GlobalTheory.Mix.semiPosReg_addFn_log_nsq | exact GlobalTheory.Mix.semiPosReg_addFn_log_nsq | (intros; apply GlobalTheory.Mix.semiPosReg_addFn_log_nsq <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.mixedChernFormSignedPartMeasure_eq_of_isometric_projOver : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ), IsProjOver p → ∀ (D : ℕ) (L M : Fin D → MLine p σ), (∀ i, (L i).Isom (M i)) → ∀ ε : ℤˣ, part L ε = part M ε := by
  first | exact @GlobalTheory.Mix.part_eq_of_isom | exact GlobalTheory.Mix.part_eq_of_isom | (intros; apply GlobalTheory.Mix.part_eq_of_isom <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.mixedChernFormSignedPartMeasure_neg_eq_zero_semiPositive : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [SecondCountableTopology (CxPts p σ)] (D : ℕ) (L : Fin D → MLine p σ), (∀ i, (L i).φ.SemiPosReg D) → part L (-1) = 0 := by
  first | exact @GlobalTheory.Mix.part_neg_eq_zero_of_semiPosReg | exact GlobalTheory.Mix.part_neg_eq_zero_of_semiPosReg | (intros; apply GlobalTheory.Mix.part_neg_eq_zero_of_semiPosReg <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.mixedChernFormDensity_change_of_chart : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (L : Fin D → MLine p σ) (c c' : AlgChart p σ D) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source → dens L c y = ‖transDet c.e c'.e y‖ ^ 2 * dens L c' y := by
  first | exact @GlobalTheory.Mix.ChartChange.dens_change_chart | exact GlobalTheory.Mix.ChartChange.dens_change_chart | (intros; apply GlobalTheory.Mix.ChartChange.dens_change_chart <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.existsUnique_genericFibreDualNumberPoint_of_model : AllV fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (y : epsR V ⟶ G), (∃! yA, VecAt U.toUnifPre F y yA) ∧ (∃! v : epsR (FractionRing V) ⟶ A.A, IsVecOver (algebraMap V (FractionRing V)) (U.gen.inv.left ≫ pullback.fst G.hom (jK V)) y v) ∧ ∀ (v : epsR (FractionRing V) ⟶ A.A) yA, IsVecOver (algebraMap V (FractionRing V)) (U.gen.inv.left ≫ pullback.fst G.hom (jK V)) y v → VecAt U.toUnifPre F y yA → yA ≫ (snd (TFK (R := V) F) A.A).left = spMap (dualMap (algebraMap (FractionRing V) F)) ≫ v.left := by
  first | exact @GlobalTheory.MBLow.vecAt_genFibre | exact GlobalTheory.MBLow.vecAt_genFibre | (intros; apply GlobalTheory.MBLow.vecAt_genFibre <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

namespace GlobalTheory.MBLow.Cl.TwistExp

variable {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X}

theorem full_mulVec (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r) (S : Matrix (Fin r) (Fin r) ℂ) (x : Fin g → ℂ) :
    d.full σ S *ᵥ x = d.full σ 0 *ᵥ x + fun i => Sum.elim (0 : Fin g' → ℂ) (S *ᵥ tP σ x) (σ i) := by
  ext i
  simp only [CD.full, Matrix.submatrix_mulVec_equiv, Function.comp_apply, Pi.add_apply, Matrix.fromBlocks_mulVec]
  rcases h : σ i with j | j
  · simp [tP]
  · simp [tP, Matrix.add_mulVec, add_assoc]
    rfl

theorem leftComponent_fullMatrix_mulVec (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r) (S : Matrix (Fin r) (Fin r) ℂ) (x : Fin g → ℂ) :
    zP σ (d.full σ S *ᵥ x) = zP σ (d.full σ 0 *ᵥ x) := by
  rw [full_mulVec]; ext i; simp [zP]

theorem secondBlock_full_mulVec (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r) (S : Matrix (Fin r) (Fin r) ℂ) (x : Fin g → ℂ) :
    tP σ (d.full σ S *ᵥ x) = tP σ (d.full σ 0 *ᵥ x) + S *ᵥ tP σ x := by
  rw [full_mulVec]; ext i; simp [tP]

theorem dot_full (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r) (S : Matrix (Fin r) (Fin r) ℂ) (x : Fin g → ℂ) :
    x ⬝ᵥ d.full σ S *ᵥ x = x ⬝ᵥ d.full σ 0 *ᵥ x + tP σ x ⬝ᵥ S *ᵥ tP σ x := by
  rw [full_mulVec, dotProduct_add]
  congr 1
  simp only [dotProduct]
  rw [← σ.symm.sum_comp, Fintype.sum_sum_type]
  simp [tP]

theorem co_form {k : ℕ} (β : N.Form k) (x y : N.X) :
    co bX x ⬝ᵥ bmat bX β *ᵥ co bX y = (β.be x y : ℂ) := by
  conv_rhs => rw [← bX.sum_repr x, ← bX.sum_repr y]

  simp only [map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply, smul_eq_mul, dotProduct, mulVec, co, bmat,
  Matrix.of_apply, Int.cast_sum, Int.cast_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
  ring

theorem co_sum (σ : Fin g ≃ Fin g' ⊕ Fin r) (Nn : Fin g → ℤ) :
    co bX (∑ l, tP σ Nn l • bX l) = tP σ (cv Nn) := by
  ext l; simp [co, tP, cv, Finsupp.single_apply]

end GlobalTheory.MBLow.Cl.TwistExp

namespace GlobalTheory.MBLow.Cl.TwistExp
open GlobalTheory.MBLow.Cl.TwistExp

theorem main_eq {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X} (d : CD N g' r bX)
    (σ : Fin g ≃ Fin g' ⊕ Fin r) (k m : ℕ) (β : N.Form k) (hm : 1 ≤ m) (hk : m ^ 2 ∣ k) (w : ℂ) (M Nn : Fin g → ℤ)
    (χ : N.X) (Z : Fin g → ℂ) :
    d.term σ (w • bmat bX β) m M Nn χ Z = d.term σ 0 m M Nn χ Z * Complex.exp ((2 * Real.pi * Complex.I : ℂ) * w) ^
      (β.be ((∑ l, tP σ Nn l • bX l) + m • χ) ((∑ l, tP σ Nn l • bX l) + m • χ) / (2 * m ^ 2)).toNat := by
  set S := w • bmat bX β with hS
  have hz : ∀ S' : Matrix (Fin r) (Fin r) ℂ, zP σ ((m:ℂ) • Z + (m:ℂ)⁻¹ • perV (d.full σ S') M Nn) =
      zP σ ((m:ℂ) • Z + (m:ℂ)⁻¹ • perV (d.full σ 0) M Nn) := fun S' => by
    ext i
    have := congrFun (leftComponent_fullMatrix_mulVec d σ S' (cv Nn)) i
    simp only [zP, perV, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [this]
  have ht : tP σ ((m:ℂ) • Z + (m:ℂ)⁻¹ • perV (d.full σ S) M Nn) =
      tP σ ((m:ℂ) • Z + (m:ℂ)⁻¹ • perV (d.full σ 0) M Nn) + (m:ℂ)⁻¹ • (S *ᵥ tP σ (cv Nn)) := by
    ext i
    have := congrFun (secondBlock_full_mulVec d σ S (cv Nn)) i
    simp only [tP, perV, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [this]; ring
  unfold CD.term trFac CD.fj
  rw [hz S, ht, dot_full d σ S (cv Nn)]

  set y : N.X := ∑ l, tP σ Nn l • bX l with hy
  have hn : tP σ (cv Nn) = co bX y := (co_sum σ Nn).symm
  have hSv : ∀ u v : Fin r → ℂ, ∀ x x' : N.X, u = co bX x → v = co bX x' → u ⬝ᵥ S *ᵥ v = w * (β.be x x' : ℂ) := by
    intro u v x x' hu hv
    rw [hS, Matrix.smul_mulVec, dotProduct_smul, hu, hv, co_form, smul_eq_mul]
  have h1 := hSv _ _ y y hn hn
  have h2 := hSv _ _ χ χ rfl rfl
  have h3 := hSv _ _ χ y rfl hn
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hsymm : β.be y χ = β.be χ y := β.symm y χ
  have hα : β.be (y + m • χ) (y + m • χ) = β.be y y + 2 * m * β.be χ y + m ^ 2 * β.be χ χ := by
    simp only [map_add (f := _), map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul, hsymm]; ring
  have hdvd : (2 * m ^ 2 : ℤ) ∣ β.be (y + m • χ) (y + m • χ) :=
    (mul_dvd_mul_left 2 (by exact_mod_cast hk)).trans (β.dvd _ _)
  have hnn : 0 ≤ β.be (y + m • χ) (y + m • χ) := by
    by_cases h0 : y + m • χ = 0
    · rw [h0]; simp
    · exact (β.pos _ h0).le
  have hK : (((β.be (y + m • χ) (y + m • χ) / (2 * m ^ 2)).toNat : ℕ) : ℂ) =
      ((β.be y y : ℂ) + 2 * m * β.be χ y + m ^ 2 * β.be χ χ) / (2 * m ^ 2) := by
    obtain ⟨q, hq⟩ := hdvd
    have hm2 : (2 * m ^ 2 : ℤ) ≠ 0 := by positivity
    have hq0 : 0 ≤ q := by
      rw [hq] at hnn
      have hp : (0:ℤ) < 2 * m ^ 2 := by positivity
      by_contra hc; push_neg at hc
      have := mul_neg_of_pos_of_neg hp hc; linarith
    rw [hq, Int.mul_ediv_cancel_left _ hm2]
    have : ((q.toNat : ℕ) : ℂ) = (q : ℂ) := by exact_mod_cast Int.toNat_of_nonneg hq0
    rw [this, eq_div_iff (by simpa using hm0)]
    have hc : ((β.be (y + m • χ) (y + m • χ) : ℤ) : ℂ) = ((2 * m ^ 2 * q : ℤ) : ℂ) := by rw [hq]
    rw [hα] at hc; push_cast at hc; linear_combination -hc
  have key : ∀ a b a' b' f t : ℂ, a + b = a' + b' + f →
      Complex.exp a * (Complex.exp b * t) = Complex.exp a' * (Complex.exp b' * t) * Complex.exp f := by
    intro a b a' b' f t h
    have : Complex.exp a * Complex.exp b = Complex.exp a' * Complex.exp b' * Complex.exp f := by
      rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, h]
    linear_combination t * this
  rw [← Complex.exp_nat_mul]
  refine key _ _ _ _ _ _ ?_
  simp only [Matrix.add_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul, add_zero, Matrix.zero_mulVec,
    dotProduct_zero, h1, h2, h3, hK]
  field_simp
  ring

end GlobalTheory.MBLow.Cl.TwistExp

namespace GlobalTheory.MBLow.Cl.TwistExp

theorem term_differentiable {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X} (d : CD N g' r bX)
    (σ : Fin g ≃ Fin g' ⊕ Fin r) (S : Matrix (Fin r) (Fin r) ℂ) (m : ℕ) (M Nn : Fin g → ℤ) (χ : N.X) :
    Differentiable ℂ (d.term σ S m M Nn χ) := by
  have hθ := (thetaChar_entire_ne_zero_automorphy g' d.τ d.a d.b d.symm d.pos d.ha d.hb).1
  have hzP : Differentiable ℂ (fun Z : Fin g → ℂ => zP σ Z) := differentiable_pi.2 fun i => differentiable_apply _
  have htP : Differentiable ℂ (fun Z : Fin g → ℂ => tP σ Z) := differentiable_pi.2 fun i => differentiable_apply _
  have hdot : ∀ {n : Type} [Fintype n] (v : n → ℂ), Differentiable ℂ (fun Z : n → ℂ => v ⬝ᵥ Z) := by
    intro n _ v
    simp only [dotProduct]
    fun_prop
  have haff : Differentiable ℂ (fun Z : Fin g → ℂ => (m : ℂ) • Z + (m : ℂ)⁻¹ • perV (d.full σ S) M Nn) := by fun_prop
  unfold CD.term trFac CD.fj
  have e1 : Differentiable ℂ (fun Z : Fin g → ℂ => thetaChar d.τ d.a d.b
      (zP σ ((m : ℂ) • Z + (m : ℂ)⁻¹ • perV (d.full σ S) M Nn) + d.t12 *ᵥ co bX χ)) :=
    hθ.comp ((hzP.comp haff).add_const _)
  have e2 : Differentiable ℂ (fun Z : Fin g → ℂ => co bX χ ⬝ᵥ (tP σ ((m : ℂ) • Z + (m : ℂ)⁻¹ • perV (d.full σ S) M Nn) + d.b2)) :=
    by have := (hdot (co bX χ)).comp ((htP.comp haff).add_const d.b2); exact this
  have e3 : Differentiable ℂ (fun Z : Fin g → ℂ => cv Nn ⬝ᵥ Z) := hdot _
  refine Differentiable.mul ?_ (Differentiable.mul ?_ e1)
  · fun_prop
  · fun_prop
end GlobalTheory.MBLow.Cl.TwistExp

namespace GlobalTheory.MBLow.Cl

theorem term_smul_bmat : AllCD fun {N} {g'} {r} {g} {bX} d σ => (∀ S m M Nn χ, Differentiable ℂ (d.term σ S m M Nn χ)) ∧ ∀ (k m : ℕ) (β : N.Form k), 1 ≤ m → m ^ 2 ∣ k → ∀ (w : ℂ) (M Nn : Fin g → ℤ) (χ : N.X) (Z : Fin g → ℂ), d.term σ (w • bmat bX β) m M Nn χ Z = d.term σ 0 m M Nn χ Z * Complex.exp ((2 * Real.pi * Complex.I : ℂ) * w) ^ (β.be ((∑ l, tP σ Nn l • bX l) + m • χ) ((∑ l, tP σ Nn l • bX l) + m • χ) / (2 * m ^ 2)).toNat := by
  intro N g' r g bX d σ
  exact ⟨fun S m M Nn χ => TwistExp.term_differentiable d σ S m M Nn χ,
    fun k m β hm hk w M Nn χ Z => TwistExp.main_eq d σ k m β hm hk w M Nn χ Z⟩

end GlobalTheory.MBLow.Cl
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

theorem _root_.GlobalTheory.T.thetaChar_differentiable_ne_zero_automorphy : ∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ), τ.IsSymm → (τ.map Complex.im).PosDef → Half a → Half b → Differentiable ℂ (thetaChar τ a b) ∧ (∃ z, thetaChar τ a b z ≠ 0) ∧ ∀ M N z, thetaChar τ a b (z + perV τ M N) = autV τ a b M N z * thetaChar τ a b z := by
  first | exact @GlobalTheory.MBLow.Cl.thetaChar_entire_ne_zero_automorphy | exact GlobalTheory.MBLow.Cl.thetaChar_entire_ne_zero_automorphy | (intros; apply GlobalTheory.MBLow.Cl.thetaChar_entire_ne_zero_automorphy <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

theorem _root_.GlobalTheory.T.thetaSection_inverseImage_baseProduct_function : ∀ (g : ℕ) (x : KeyIn ℂ) (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (c : ℂ) (W : Fin g → Fin g → ℂ), NF x hg u τ a b c W → (∃ th, IsPolAVSectionInverseImage x.P (baseOver (Sp ℂ)) x.th th) ∧ (∀ th, IsPolAVSectionInverseImage x.P (baseOver (Sp ℂ)) x.th th → FnT u 1 th fun z => c * thetaChar τ a b z) ∧ ∀ (k : ℕ) (t t' : LB.Sec (LPow x.P.A x.P.L (k : ℤ) (baseOver (Sp ℂ)))) f, FnT u k t f → FnT u k t' f → ∀ j, t.f j = t'.f j := by
  first | exact @GlobalTheory.MBLow.Cl.thetaSection_fnT_thetaChar_and_unique | exact GlobalTheory.MBLow.Cl.thetaSection_fnT_thetaChar_and_unique | (intros; apply GlobalTheory.MBLow.Cl.thetaSection_fnT_thetaChar_and_unique <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.translatedDualPoint_of_integralTorusExtPoint : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (C : Type) [Field C] [Algebra (FractionRing V) C] (gm₀ : GtPt D (epsR V)) (gm : GtPt D (TE V C)), GtPt.IsPull (spMap (dualMap (toF V C))) gm₀ gm → ∀ mu : D.X, ((lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE V C ⟶ TF (R := V) C) gm.b).left ≫ (DegPre.trF D C mu).left) ≫ (DegPre.prB D C).left = spMap (dualMap (toF V C)) ≫ (padd D.P.A gm₀.b (toUnit _ ≫ D.c mu)).left ∧ (padd D.P.A gm₀.b (toUnit _ ≫ D.c mu)).left ≫ D.P.A.hom = spMap (algebraMap V (DualNumber V)) ∧ ((lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE V C ⟶ TF (R := V) C) gm.b).left ≫ (DegPre.trF D C mu).left) ≫ (fst (TF (R := V) C) D.P.A).left = spMap (algebraMap C (DualNumber C)) := by
  first | exact @GlobalTheory.MBLow.trF_dualPoint_of_isPull | exact GlobalTheory.MBLow.trF_dualPoint_of_isPull | (intros; apply GlobalTheory.MBLow.trF_dualPoint_of_isPull <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.degenerationValues_norms_eq_uniformizer_zpow : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN → ‖ν.rg‖ = 1 ∧ ∀ χ, ∃ n : ℤ, ‖(N.ψ χ : C)‖ = ‖toF V C ϖ‖ ^ n := by
  first | exact @GlobalTheory.MBLow.DiscNorm.main | exact GlobalTheory.MBLow.DiscNorm.main | (intros; apply GlobalTheory.MBLow.DiscNorm.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

theorem _root_.GlobalTheory.T.holomorphic_uniformization_complex_base_change : ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (D : DegPre R) (N : NumD ℂ)
    (ν : NumOf D ℂ N) (g : ℕ) (d : AB N.toNumB g) (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L g) (φ : x.P.A.left ⟶ D.P.A.left),
    IsGrpPullback x.P.A D.P.A (spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) φ → (∀ z, (ν.eA (d.ex z)).left = (u.ex z).left ≫ φ) →
    ∀ (b' : epsR ℂ ⟶ x.P.A) (b : TE R ℂ ⟶ D.P.A), IsTangent b' → b'.left ≫ φ = b.left →
      ∀ W' : Fin g → ℂ, (IsD ν d W' b ↔ u.IsDiff W' b') := by
  first | exact @GlobalTheory.UnifTan.isD_iff_isDiff | exact GlobalTheory.UnifTan.isD_iff_isDiff | (intros; apply GlobalTheory.UnifTan.isD_iff_isDiff <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.pulledBackSection_integralValue_dualPoint : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (IsLocalRing.maximalIdeal V)) (C : Type) [NontriviallyNormedField C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN → ∀ (k : ℕ) (β : D.toPre.X) (σ : D.toPre.SecB k β) (σF : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre C β) (DegPre.famε k))), GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre C β) (DegPre.famε k) σF (D.toPre.famφB β) (DegPre.famε k) σ (DegPre.prB D.toPre C).left 1 → ∀ (Q : Sp (DualNumber V) ⟶ D.toPre.P.A.left), Q ≫ D.toPre.P.A.hom = spMap (algebraMap V (DualNumber V)) → ∀ (r : Sp (DualNumber C) ⟶ (DegPre.BF D.toPre C).left), r ≫ (DegPre.prB D.toPre C).left = spMap (dualMap (toF V C)) ≫ Q → ‖(sE σF r ν.J).fst‖ ≤ 1 ∧ ‖(sE σF r ν.J).snd‖ ≤ 1 := by
  intro V _ _ _ D C _ _ hC N ν hI k β σ σF hS Q hQ r hr
  exact GlobalTheory.IntGaugePull.sE_norm_le_one_of_pull V D C hC N ν hI k β σ σF hS Q hQ r hr
end

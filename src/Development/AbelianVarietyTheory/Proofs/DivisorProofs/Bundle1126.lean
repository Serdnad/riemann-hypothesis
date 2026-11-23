module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinSubstLinSubst
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1093
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle009
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BiadditiveOfTrivAxes
public import Mathlib.NumberTheory.NumberField.CMField
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1094
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1095
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle999
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1027
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
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable
import ReciprocityTheory.SemistableReduction.Bundle005
import ReciprocityTheory.SemistableReduction.Bundle006
import ReciprocityTheory.SemistableReduction.RestBlockSubstIsMultiHomogeneous
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle007
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open MvPolynomial NumberField Module GlobalTheory.ChowHt GlobalTheory.CompHt MeasureTheory

namespace GlobalTheory.SphereMeanFrame

set_option autoImplicit false in
open MvPolynomial NumberField Module MeasureTheory in
theorem _root_.GlobalTheory.SphereMeanFrame.eval_linSubst {B N n : ℕ} (M : Matrix (Fin N) (Fin n) ℂ)
    (f : MvPolynomial (Fin B × Fin N) ℂ) (u : Fin B × Fin n → ℂ) :
    eval u (_root_.GlobalTheory.ChowHt.linSubst M f) =
      eval (fun p : Fin B × Fin N => ∑ k, M p.2 k * u (p.1, k)) f := by
  unfold _root_.GlobalTheory.ChowHt.linSubst
  rw [_root_.ReciprocityTheory.MultiplicativeHeights.eval_aeval_alt]
  simp


set_option autoImplicit false in
open MvPolynomial NumberField Module MeasureTheory in
theorem _root_.GlobalTheory.SphereMeanFrame.blockSphereMean_linSubst {B N : ℕ} (Q : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (hQ : ∀ x : EuclideanSpace ℂ (Fin (N + 1)), ‖Matrix.toEuclideanLin Q x‖ = ‖x‖)
    (f : MvPolynomial (Fin B × Fin (N + 1)) ℂ) :
    _root_.ReciprocityTheory.MultiplicativeHeights.blockSphereMean B (N + 1) (_root_.GlobalTheory.ChowHt.linSubst Q f) = _root_.ReciprocityTheory.MultiplicativeHeights.blockSphereMean B (N + 1) f := by
  let T : EuclideanSpace ℂ (Fin (N + 1)) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (N + 1)) :=
    { toLinearMap := Matrix.toEuclideanLin Q, norm_map' := hQ }
  let U := T.toLinearIsometryEquiv rfl
  let V : EuclideanSpace ℂ (Fin (N + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin (N + 1)) :=
    { toLinearEquiv := U.toLinearEquiv.restrictScalars ℝ, norm_map' := U.norm_map }
  set μ : Measure (Fin B → _root_.ReciprocityTheory.MultiplicativeHeights.UnitSphereC (N + 1)) := Measure.pi fun _ => _root_.ReciprocityTheory.MultiplicativeHeights.sphereProb (N + 1) with hμ
  set Φ : (Fin B → _root_.ReciprocityTheory.MultiplicativeHeights.UnitSphereC (N + 1)) → (Fin B → _root_.ReciprocityTheory.MultiplicativeHeights.UnitSphereC (N + 1)) :=
    fun z b => _root_.ReciprocityTheory.MultiplicativeHeights.sphereMap V (z b) with hΦdef
  have hΦ : MeasurePreserving Φ μ μ := measurePreserving_pi _ _ (fun _ => _root_.ReciprocityTheory.MultiplicativeHeights.measurePreserving_sphereMap V)
  set g : (Fin B → _root_.ReciprocityTheory.MultiplicativeHeights.UnitSphereC (N + 1)) → ℝ := fun z => Real.log ‖eval (_root_.ReciprocityTheory.MultiplicativeHeights.blockPoint z) f‖ with hg
  have hcont : Continuous (fun z : Fin B → _root_.ReciprocityTheory.MultiplicativeHeights.UnitSphereC (N + 1) => _root_.ReciprocityTheory.MultiplicativeHeights.blockPoint z) := by
    unfold _root_.ReciprocityTheory.MultiplicativeHeights.blockPoint
    exact continuous_pi fun p => (continuous_apply p.2).comp
      ((_root_.ReciprocityTheory.MultiplicativeHeights.continuous_spherePoint (N + 1)).comp (continuous_apply p.1))
  have hgm : Measurable g :=
    Real.measurable_log.comp (((MvPolynomial.continuous_eval f).comp hcont).norm.measurable)
  have hpt : ∀ z, eval (_root_.ReciprocityTheory.MultiplicativeHeights.blockPoint z) (_root_.GlobalTheory.ChowHt.linSubst Q f) = eval (_root_.ReciprocityTheory.MultiplicativeHeights.blockPoint (Φ z)) f := by
    intro z
    rw [_root_.GlobalTheory.SphereMeanFrame.eval_linSubst]
    congr 1
  change ∫ z, Real.log ‖eval (_root_.ReciprocityTheory.MultiplicativeHeights.blockPoint z) (_root_.GlobalTheory.ChowHt.linSubst Q f)‖ ∂μ = ∫ z, g z ∂μ
  simp_rw [hpt]
  change ∫ z, g (Φ z) ∂μ = ∫ z, g z ∂μ
  rw [← integral_map hΦ.measurable.aemeasurable hgm.aestronglyMeasurable, hΦ.map_eq]


set_option autoImplicit false in
open MvPolynomial NumberField Module MeasureTheory in
theorem _root_.GlobalTheory.SphereMeanFrame.blockSphereMean_eq_of_frameNorm_eq : ∀ (B N : ℕ) (A A' : Matrix (Fin N) (Fin N) ℂ),
    A.det ≠ 0 → A'.det ≠ 0 → (∀ z, _root_.GlobalTheory.ChowHt.frameNorm A z = _root_.GlobalTheory.ChowHt.frameNorm A' z) →
    ∀ f : MvPolynomial (Fin B × Fin N) ℂ,
      _root_.ReciprocityTheory.MultiplicativeHeights.blockSphereMean B N (_root_.GlobalTheory.ChowHt.linSubst A f) = _root_.ReciprocityTheory.MultiplicativeHeights.blockSphereMean B N (_root_.GlobalTheory.ChowHt.linSubst A' f) := by
  intro B N A A' hA hA' hn f
  cases N with
  | zero =>
    have hAA : A = A' := Subsingleton.elim _ _
    rw [hAA]
  | succ N =>
    have hAu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
    have hA'u : IsUnit A'.det := isUnit_iff_ne_zero.mpr hA'
    have hAQ : A * (A⁻¹ * A') = A' := by
      rw [← mul_assoc, Matrix.mul_nonsing_inv _ hAu, one_mul]
    have key : _root_.GlobalTheory.ChowHt.linSubst A' f =
        _root_.GlobalTheory.ChowHt.linSubst (A⁻¹ * A') (_root_.GlobalTheory.ChowHt.linSubst A f) := by
      rw [_root_.GlobalTheory.HeightUnique.linSubst_linSubst, hAQ]
    rw [key, _root_.GlobalTheory.SphereMeanFrame.blockSphereMean_linSubst (A⁻¹ * A')]
    intro x
    have h1 := hn (A'.mulVec x.ofLp)
    simp only [_root_.GlobalTheory.ChowHt.frameNorm, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA'u,
      Matrix.one_mulVec] at h1
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    convert h1 using 4 with i
    rfl

end GlobalTheory.SphereMeanFrame
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.continuity_baseChange_affine_cofiltered_limit : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (S : Scheme.{0}) (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Over S) (c : Cone G), IsLimit c → (∀ i, IsAffineHom (G.obj i).hom) → ∀ (W : Scheme.{0}) (r : W ⟶ S), IsAffine W → ContCone R F ((bc (sch.map r)).mapCone c) := by
  first
  | exact @GlobalTheory.EtC.contCone_bc_affine
  | exact GlobalTheory.EtC.contCone_bc_affine
  | (intros; apply GlobalTheory.EtC.contCone_bc_affine <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.continuity_cofiltered_limit_represented_affine : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (I : Type) [SmallCategory I] [IsCofiltered I] (D : I ⥤ PSh) (c : Cone D), IsLimit c → (∀ i, ∃ Z : Scheme.{0}, IsAffine Z ∧ Nonempty (yoneda.obj Z ≅ D.obj i)) → (∃ Z : Scheme.{0}, Nonempty (yoneda.obj Z ≅ c.pt)) → ContCone R F (disc.mapCone c) := by
  first
  | exact @GlobalTheory.contCone_of_represented
  | exact GlobalTheory.contCone_of_represented
  | (intros; apply GlobalTheory.contCone_of_represented <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.cohomology_cech_level_eq_zero_of_pos : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (k : ℕ) (m : ℕ), 0 < m → ∀ y : H R (disc.obj ((cech (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj (op (SimplexCategory.mk (k))))) F m, y = 0 := by
  first
  | exact @GlobalTheory.EtC.cech_level_acyclic
  | exact GlobalTheory.EtC.cech_level_acyclic
  | (intros; apply GlobalTheory.EtC.cech_level_acyclic <;> assumption)
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.exists_connectedPDivGroupChart_of_isConn : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G : PDivGroup p K), G.IsConn → ∃ d, Nonempty (Chart G d) := by
  first | exact @GlobalTheory.Katz.exists_chart_of_isConn | exact GlobalTheory.Katz.exists_chart_of_isConn | (intros; apply GlobalTheory.Katz.exists_chart_of_isConn <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.CasimirPull

open GlobalTheory.CechPic

theorem main : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), IsAbelianScheme A → Q.IsLB → (∃ t : (Q.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (Q.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso Q (Q.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (Q.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (O : Type) [Ring O] (bar : O → O) (r : ℕ) (e : Fin r → O) (W : Matrix (Fin r) (Fin r) ℤ) (d : ℕ), (∀ a b, bar (a + b) = bar a + bar b) → Submodule.span ℤ (Set.range e) = ⊤ → ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → 0 < d → ∑ i, ∑ j, W i j • (e j * bar (e i)) = (d : O) → ∀ (act : O → (A ⟶ A)), IsRAct A act → Adj A Q bar act → ∀ (G : Over S) [GrpObj G] (pr : Fin r → (G ⟶ A)), (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin r → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) → ∀ Φ : A ⟶ G, (∀ u, Φ ≫ pr u = act (e u)) → LBIso ((LB.LinComb Q (K := Fin r × Fin r) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)).pull Φ.left) (LB.LinComb Q (K := Fin 1) (fun _ => (lift (𝟙 A) (𝟙 A)).left) (fun _ => (d : ℤ))) := by
  intro S A _ _ Q hA hQ h₁ h₂ _ hamp O _ bar r e W d _ _ _ _ hsum act hact hadj G _ pr _ _ Φ hΦ
  have hbi := GlobalTheory.Biadditive.biadditive_of_triv_axes GlobalTheory.globalFns_holds S A
    (Q.pull (lift (𝟙 A) (𝟙 A)).left) hA (pull_isLB hQ _) hamp Q hQ h₁ h₂

  have add2 : ∀ (T : Over S) (y x x' : T ⟶ A), pull (lift y (x * x')).left (cls Q hQ) =
      pull (lift y x).left (cls Q hQ) + pull (lift y x').left (cls Q hQ) := by
    intro T y x x'
    have z := (cls_eq_zero_iff (LB.isLB_linComb hQ _ _)).2 (hbi T x x' y).2
    rw [cls_linComb hQ, Fin.sum_univ_three] at z
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul] at z
    rw [← sub_eq_zero, ← z]
    abel

  have adjB : ∀ (T : Over S) (x y : T ⟶ A) (a : O), pull (lift (x ≫ act a) y).left (cls Q hQ) =
      pull (lift x (y ≫ act (bar a))).left (cls Q hQ) := by
    intro T x y a
    have h := (cls_eq_iff (pull_isLB hQ _) (pull_isLB hQ _)).2 (hadj a)
    rw [cls_pull hQ, cls_pull hQ] at h
    have k₁ : (lift x y).left ≫ (lift (fst A A ≫ act a) (snd A A)).left = (lift (x ≫ act a) y).left := by
      rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd]
    have k₂ : (lift x y).left ≫ (lift (fst A A) (snd A A ≫ act (bar a))).left = (lift x (y ≫ act (bar a))).left := by
      rw [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc]
    rw [← k₁, ← k₂, pull_comp, pull_comp, h]
  let f : O →+ Pic A.left := AddMonoidHom.mk' (fun a => pull (lift (𝟙 A) (act a)).left (cls Q hQ))
    (fun a b => by simp only [hact.2.2.2 a b]; exact add2 A (𝟙 A) _ _)
  have term : ∀ i j : Fin r, pull Φ.left (pull (lift (pr i) (pr j)).left (cls Q hQ)) =
      f (e j * bar (e i)) := by
    intro i j
    rw [← pull_comp, ← Over.comp_left, comp_lift, hΦ, hΦ]
    have := adjB A (𝟙 A) (act (e j)) (e i)
    rw [Category.id_comp] at this
    rw [this, ← hact.2.2.1]
    rfl
  refine (cls_eq_iff (pull_isLB (LB.isLB_linComb hQ _ _) _) (LB.isLB_linComb hQ _ _)).1 ?_

  rw [cls_pull (LB.isLB_linComb hQ _ _), cls_linComb hQ, cls_linComb hQ, map_sum, Fin.sum_univ_one]
  simp only [map_zsmul, term]
  rw [Fintype.sum_prod_type]

  simp only [← map_zsmul, ← map_sum, hsum]
  rw [← nsmul_one, map_nsmul, natCast_zsmul]
  rw [map_nsmul]
  show d • pull (lift (𝟙 A) (act 1)).left (cls Q hQ) = _
  rw [hact.2.1]

end GlobalTheory.CasimirPull
end
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.norm_galois_conj_heckeCharacter_finitePart_eq_one : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (hφ : IsCMType φ) (s : ℕ) (κ : I → ℕ) (c : Ideal (OF E)) (hc : c ≠ ⊥) (χ : HChar E) (hχ : HasInf χ φ (fun i => (κ i : ℤ) + s)) (hu : ∀ u ∈ hatOUnits c, finPart χ u = 1) (σ : ℂ ≃+* ℂ) (y : (Af E)ˣ), ‖σ (finPart χ y : ℂ)‖ = 1 := by
  first | exact @GlobalTheory.CMVal.norm_conj_finPart | exact GlobalTheory.CMVal.norm_conj_finPart | (intros; apply GlobalTheory.CMVal.norm_conj_finPart <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.harrisTaylorObjectPullback_comp : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S₁ S₂ S₃ : Scheme.{0}) (s₁ : S₁ ⟶ Sp R) (s₂ : S₂ ⟶ Sp R) (s₃ : S₃ ⟶ Sp R) (o₁ : Obj b N s₁) (o₂ : Obj b N s₂) (o₃ : Obj b N s₃) (f : S₁ ⟶ S₂) (g : S₂ ⟶ S₃), ObjMap o₁ o₂ f → ObjMap o₂ o₃ g → Nonempty (ObjMap o₁ o₃ (f ≫ g)) := by
  first | exact @GlobalTheory.UPel.HT.objMap_comp | exact GlobalTheory.UPel.HT.objMap_comp | (intros; apply GlobalTheory.UPel.HT.objMap_comp <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.lieMult_iff_finrank_common_eigenspace_coords : ∀ (W : Type) [CommRing W] (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G] (O : Type) [CommRing O] (act : OAct O G) (n : ℕ) (k : Type) [Field k] (β : W →+* k) (T : (Fin n → k) → (epsPtR (spMap β) ⟶ G)) (A : O → Matrix (Fin n) (Fin n) k), Function.Injective T → (∀ v : epsPtR (spMap β) ⟶ G, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk (spMap β) ⟶ G).left ↔ v ∈ Set.range T) → (∀ c c', T (c + c') = T c * T c') → (∀ (s : k) c, (T (s • c)).left = spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScaleR s) ≫ (T c).left) → (∀ a c, T c ≫ act.act a = T ((A a).mulVec c)) → ∀ (τ : O →+* k) (N : ℕ), LieMult act (spMap β) τ N ↔ Module.finrank k (⨅ a, LinearMap.ker (Matrix.mulVecLin (A a) - τ a • LinearMap.id) : Submodule k (Fin n → k)) = N := by
  first | (exact @GlobalTheory.LieCoordMult.lieMult_iff_finrank_eig) | (exact GlobalTheory.LieCoordMult.lieMult_iff_finrank_eig) | (intros; apply GlobalTheory.LieCoordMult.lieMult_iff_finrank_eig  <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.exists_embedding_lie_multiplicity_zero_char_zero : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s), 2 * D.a < Module.finrank ℚ D.F → ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S) (β : R →+* k), x ≫ s = spMap β → ∃ σ : 𝓞 D.F →+* k, LieMult (o.act.toF D) x σ 0 := by
  first | exact @GlobalTheory.HTLie.exists_lieMult_zero | exact GlobalTheory.HTLie.exists_lieMult_zero | (intros; apply GlobalTheory.HTLie.exists_lieMult_zero <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.exists_tangent_coords_base_change_smooth_comm_group : ∀ (W : Type) [CommRing W] [IsLocalRing W] (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∃ (n : ℕ) (M : (G ⟶ G) → Matrix (Fin n) (Fin n) W), ∀ (R' : Type) [CommRing R'] (β : W →+* R'), ∃ T : (Fin n → R') → (epsPtR (spMap β) ⟶ G), Function.Injective T ∧ (∀ v : epsPtR (spMap β) ⟶ G, spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ v.left = (1 : Over.mk (spMap β) ⟶ G).left ↔ v ∈ Set.range T) ∧ (∀ c c', T (c + c') = T c * T c') ∧ (∀ (s : R') c, (T (s • c)).left = spMap (epsScaleR s) ≫ (T c).left) ∧ ∀ u : G ⟶ G, IsMonHom u → ∀ c, T c ≫ u = T (((M u).map β).mulVec c) := by
  first | (exact @GlobalTheory.LieCoordR.exists_coords_baseChange) | (exact GlobalTheory.LieCoordR.exists_coords_baseChange) | (intros; apply GlobalTheory.LieCoordR.exists_coords_baseChange  <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory



theorem GlobalTheory.LBObs.exists_lift_of_isObL_zero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (S : Sys I π s₀) (X : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X) (P : S.Presents s i) (L₀ : LB X₀), IsPullback i s₀ s (spMap π) → L₀.IsLB → IsObL S α L₀ 0 → ∃ L : LB X, L.IsLB ∧ LBIso (L.pull i) L₀ := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α X₀ s₀ S X s i P L₀ hpb hL₀ hob
  obtain ⟨C', _, _, G, hbas, u, hfr, hobu⟩ := hob
  rw [map_zero] at hobu
  obtain ⟨v, hvp, hvc⟩ := GlobalTheory.T.unitCocycle_lift_of_obstruction_eq_zero R R₀ I hI π hπ hk R₁ α C' (G ⋙ OAff s₀) ((ofSys S).restrict G) u hobu
  obtain ⟨V, hV, hi, e, hpre, he, hred⟩ := GlobalTheory.T.exists_charts_squareZero_presented_scheme R R₀ I hI π hπ hk X₀ s₀ S X s i P hpb
  let V' : C' → X.Opens := fun T => V (G.obj T)
  have hV' : ∀ ⦃T T' : C'⦄, (T ⟶ T') → V' T' ≤ V' T := fun T T' a => hV (G.map a)
  let u' : ∀ (T T' : C') (_ : T ⟶ T'), Γ(X, V' T')ˣ := fun T T' a => Units.map (e (G.obj T')).toMonoidHom (v T T' a)
  have hcoc : IsCoc V' hV' u' := by
    intro T T' T'' a b
    ext
    have h1 := hvc T T' T'' a b
    change e (G.obj T'') (v T T'' (a ≫ b)).val = _
    rw [h1]
    refine ((e (G.obj T'')).map_mul _ _).trans ?_
    exact congrArg (· * e (G.obj T'') (v T' T'' b).val) (he (G.obj T') (G.obj T'') (G.map b) (v T T' a).val)
  haveI : IsClosedImmersion i := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hpb.flip
    (IsClosedImmersion.spec_of_surjective _ hπ)
  haveI : Surjective i := surjective_of_isPullback_sqZero hI hπ hk hpb
  have hbas' : IsBas V' := GlobalTheory.LBObs.isBas_of_preimage_eq X X₀ i C' V' (opOf G) (fun T => hpre _) hbas
  obtain ⟨L, hL, hfrL⟩ := GlobalTheory.T.exists_lineBundle_of_thinBasis_cocycle X C' V' hV' u' hbas' hcoc
  have hH : ∀ T, opOf G T ≤ i ⁻¹ᵁ V' ((𝟭 C').obj T) := fun T => (hpre _).ge
  have hfr2 := GlobalTheory.LBObs.isFrame_pull X C' V' hV' L u' X₀ i C' (opOf G) (opOf_le G) (𝟭 C') hH hfrL
  have hueq : (fun T T' (a : T ⟶ T') => res (hH T') (pullU i _ (u' _ _ ((𝟭 C').map a)))) = u := by
    funext T T' a
    ext
    have h2 := hred (G.obj T') (v T T' a).val
    have h3 := hvp T T' a
    refine Eq.trans ?_ (h2.trans h3)
    rfl
  rw [hueq] at hfr2
  exact ⟨L, hL, GlobalTheory.LBObs.lbIso_of_isFrame X₀ C' (opOf G) (opOf_le G) (L.pull i) L₀ u hbas (LB.isLB_pull hL i) hL₀ hfr2 hfr⟩
end

module

public import Development.EtaleCohomology.EtaleTrace.Bundle003
public import Development.EtaleCohomology.TateTwists.Bundle004
public import Development.EtaleCohomology.TateTwists.Bundle013
public import Mathlib.Order.CompletePartialOrder
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleTrace

def PtCov : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} (p : X ⟶ S k), IsProper p →
  ∀ Sv : Sieve X, Sv ∈ Scheme.etaleTopology X → ∃ T : Sieve X, T ∈ Scheme.etaleTopology X ∧
    ∀ (V : Scheme.{0}) (g : V ⟶ X), T.arrows g → ∃ (U : Scheme.{0}) (g' : U ⟶ X) (h : V ⟶ U),
      Sv.arrows g' ∧ h ≫ g' = g ∧ ∃ w : S k ⟶ U, w ≫ g' ≫ p = 𝟙 _

def EtaleTateTwistSectionConstantOnPointsOfConnectedProper : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], (l : k) ≠ 0 → ∀ j : ℕ,
  ∀ {X : Scheme.{0}} (p : X ⟶ S k), IsProper p → ∀ s : Sec (tw (l ^ j) 0) X,
    (ConnectedSpace X → ∀ y y' : Pt p, Sec.res y.1 s = Sec.res y'.1 s)

theorem q_nsmul {q : ℕ} {U : Scheme.{0}} (x : Sec (tw q 0) U) : q • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  have : ((q : ℕ) : ULift.{1} (ZMod q)) = 0 := ULift.ext (by simp)
  rw [this, zero_smul]

theorem res_comp {q : ℕ} {W V U : Scheme.{0}} (a : W ⟶ V) (b : V ⟶ U) (x : Sec (tw q 0) U) :
    Sec.res (a ≫ b) x = Sec.res a (Sec.res b x) := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem res_nsmul {q : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (c : ℕ) (x : Sec (tw q 0) U) :
    Sec.res g (c • x) = c • Sec.res g x := map_nsmul _ _ _

theorem res_zero' {q : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) : Sec.res g (0 : Sec (tw q 0) U) = 0 := map_zero _

theorem primK (k : Type) [Field k] [IsAlgClosed k] (q : ℕ) (hq : (q : k) ≠ 0) : Nonempty (Prim q k) := by
  have hq0 : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; simp at hq)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic q k)
    (ne_of_gt (Polynomial.degree_cyclotomic_pos q k hq0))
  refine ⟨⟨z, isUnit_iff_ne_zero.2 hq, ?_⟩⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact hz

theorem etale_tate_twist_zero_section_eq_zero_of_vanishing_at_points (hT : LateralTheory.EtaleFoundations.CongruenceLocalDecomposition.TwLoc) (hC : PtCov) (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k]
    (hl : (l : k) ≠ 0) (j : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) (hp : IsProper p) (s : Sec (tw (l ^ j) 0) X)
    (h : ∀ y : Pt p, Sec.res y.1 s = 0) : s = 0 := by
  haveI : NeZero (l ^ j) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hq : ((l ^ j : ℕ) : k) ≠ 0 := by push_cast; exact pow_ne_zero _ hl
  obtain ⟨ζ0⟩ := primK k (l ^ j) hq
  let φ : k →+* Γ(X, ⊤) := (p.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  obtain ⟨Sv, hSv, hSs⟩ := (hT (l ^ j) 0).1 X (ζ0.map φ) s
  obtain ⟨T, hTm, hTs⟩ := hC k p hp Sv hSv
  refine (EtaleFoundations.etale_sheaf_sections_glue_of_forget_isSheaf (ZMod (l ^ j)) (tw (l ^ j) 0) X).1 s 0 ⟨T, hTm, fun V g hg => ?_⟩
  obtain ⟨U, g', hh, hg', rfl, w, hw⟩ := hTs V g hg
  obtain ⟨c, hc⟩ := hSs U g' hg'
  have h0 : Sec.res g' s = 0 := by
    have e1 : Sec.res w (Sec.res g' s) = 0 := by
      rw [← res_comp]
      exact h ⟨w ≫ g', by rw [Category.assoc]; exact hw⟩
    rw [hc] at e1 ⊢
    rw [res_nsmul, (hT (l ^ j) 0).2.2] at e1
    obtain ⟨m, rfl⟩ := (hT (l ^ j) 0).2.1 (S k) _ c e1
    rw [mul_comm]
    first
      | (rw [mul_nsmul, q_nsmul, nsmul_zero])
      | (rw [mul_nsmul', q_nsmul, nsmul_zero])
      | (rw [mul_nsmul', q_nsmul, smul_zero])
      | (rw [mul_nsmul, q_nsmul, smul_zero])
  rw [res_comp, h0, res_zero', res_zero']

theorem tateTwistSections_determinedByPoints_of_constant (hT : LateralTheory.EtaleFoundations.CongruenceLocalDecomposition.TwLoc) (hC : PtCov) (hK : EtaleTateTwistSectionConstantOnPointsOfConnectedProper) : EtaleTateTwistSectionsDeterminedByPointsOfProper := by
  intro l _ k _ _ hl j X p hp s
  exact ⟨etale_tate_twist_zero_section_eq_zero_of_vanishing_at_points hT hC l k hl j p hp s, hK l k hl j p hp s⟩

end LateralTheory.EtaleTrace
end
end

section

open MvPolynomial

namespace LateralTheory.EtaleTrace.LSmoothPf

noncomputable def polyPres (k : Type) [CommRing k] (N : ℕ) :
    Algebra.SubmersivePresentation k (MvPolynomial (Fin N) k) (Fin N) PEmpty.{1} :=
  let P : Algebra.PreSubmersivePresentation k (MvPolynomial (Fin N) k) (Fin N) PEmpty.{1} :=
    { toGenerators := Algebra.Generators.mvPolynomial k (Fin N)
      relation := PEmpty.elim
      span_range_relation_eq_ker := by
        simp only [Set.range_eq_empty, Ideal.span_empty]
        symm
        rw [Algebra.Generators.ker_eq_ker_aeval_val, ← RingHom.injective_iff_ker_eq_bot]
        first
          | intro a b h; simpa only [MvPolynomial.aeval_X_left_apply] using h
          | intro a b h; simpa [Algebra.Generators.mvPolynomial] using h
          | change Function.Injective (MvPolynomial.aeval (R := k) (MvPolynomial.X : Fin N → MvPolynomial (Fin N) k))
            intro a b h; simpa only [MvPolynomial.aeval_X_left_apply] using h
      map := PEmpty.elim
      map_inj a := by cases a }
  { P with
    jacobian_isUnit := by
      rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
      rw [Matrix.det_isEmpty, map_one]
      exact isUnit_one }

theorem poly_ssmooth (k : Type) [CommRing k] (N : ℕ) :
    Algebra.IsStandardSmoothOfRelativeDimension N k (MvPolynomial (Fin N) k) :=
  (polyPres k N).isStandardSmoothOfRelativeDimension (by simp [Algebra.Presentation.dimension])

open CategoryTheory AlgebraicGeometry LateralTheory.EtaleTrace.LPdCut
attribute [local instance] MvPolynomial.gradedAlgebra

theorem spec_C_smooth (k : Type) [Field k] (N : ℕ) :
    SmoothOfRelativeDimension N (Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial (Fin N) k))) := by
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension N)]
  refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := N) (R := k) (S := MvPolynomial (Fin N) k)).mpr
    (poly_ssmooth k N)

theorem Dp_cover (k : Type) [Field k] (N : ℕ) : ⨆ i, Dp k N i = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top'
  · intro i; exact ⟨1, MvPolynomial.isHomogeneous_X k i⟩
  · rw [eq_top_iff]
    intro p _hp
    clear _hp
    induction p using MvPolynomial.induction_on with
    | C a =>
      have ha : MvPolynomial.C a ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0 :=
        MvPolynomial.isHomogeneous_C _ a
      have : MvPolynomial.C a = algebraMap (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0) (MvPolynomial (Fin (N + 1)) k) ⟨_, ha⟩ := rfl
      rw [this]; exact Subalgebra.algebraMap_mem _ _
    | add p q hp hq => exact Subalgebra.add_mem _ hp hq
    | mul_X p i hp => exact Subalgebra.mul_mem _ hp (Algebra.subset_adjoin ⟨i, rfl⟩)

theorem LSmooth_of (hC : LChart) : LSmooth := by
  intro k _ N
  choose j hj hc hr using fun i => hC k N i
  let 𝒰 : (PN k N).OpenCover := Scheme.Cover.mkOfCovers (Fin (N + 1)) _ j (fun x => by
    have hx : x ∈ (⊤ : (PN k N).Opens) := trivial
    rw [← Dp_cover k N] at hx
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    have : x ∈ Set.range (j i) := by rw [hr i]; exact hi
    obtain ⟨y, hy⟩ := this
    exact ⟨i, y, hy⟩) hj
  have hA : ∀ i, IsAffine (𝒰.X i) := fun i => by
    change IsAffine (Spec (CommRingCat.of (MvPolynomial (Fin N) k))); infer_instance
  refine HasRingHomProperty.of_source_openCover (P := @SmoothOfRelativeDimension.{0} N) 𝒰 (fun i => ?_)
  have h : SmoothOfRelativeDimension N (𝒰.f i ≫ PNto k N) := by
    change SmoothOfRelativeDimension N (j i ≫ PNto k N)
    rw [hc i]
    exact spec_C_smooth k N
  exact (HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension.{0} N)).mp h

end LateralTheory.EtaleTrace.LSmoothPf
end

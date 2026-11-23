module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle715
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle714
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1908
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle842
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle716
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Jp.SplitK

open Formalism.UG (GLint)

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {m : ℕ} {J : Matrix (Fin m) (Fin m) E} {v : HeightOneSpectrum (𝓞 F)}

theorem mem_stabLoc_std_iff (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) {g : GLoc σ J v} :
    g ∈ stabLoc σ J (stdLattice E m) v ↔
      splitHom σ J τ g ∈ GLint (Fin m) (v.adicCompletionIntegers F).toSubring ∧
        splitHom σ J (τ.comp σ) g ∈ GLint (Fin m) (v.adicCompletionIntegers F).toSubring := by
  have key : ∀ y : Fin m → Fv F v ⊗[F] E, y ∈ latLoc F (stdLattice E m) v ↔
      (∀ i, splitVec τ y i ∈ v.adicCompletionIntegers F) ∧
        ∀ i, splitVec (τ.comp σ) y i ∈ v.adicCompletionIntegers F := fun y => by
    rw [mem_latLoc_iff_split τ h, mem_splitLat_stdLattice h, mem_splitLat_stdLattice h]
  rw [mem_stabLoc]
  simp only [key, splitVec_matHom_mulVec, mem_GLint_iff_mulVec]
  constructor
  · intro H
    refine ⟨fun u => ?_, fun u => ?_⟩
    · simpa using H (splitIncl h τ u)
    · simpa using H (splitIncl h (τ.comp σ) u)
  · rintro ⟨H1, H2⟩ y
    exact and_congr (H1 _) (H2 _)


omit [NumberField E] in
theorem transpose_splitHom_comp (τ : E →ₐ[F] Fv F v) (hJ : J.map τ * J.map τ = -1) (g : GLoc σ J v) :
    (splitHom σ J (τ.comp σ) g).1ᵀ = -(J.map τ * (splitHom σ J τ g⁻¹).1 * J.map τ) := by
  have e := splitHom_unitary τ g
  have i1 : (splitHom σ J τ g).1 * (splitHom σ J τ g⁻¹).1 = 1 := by
    rw [map_inv, Units.mul_inv]
  calc (splitHom σ J (τ.comp σ) g).1ᵀ
      = -((splitHom σ J (τ.comp σ) g).1ᵀ * (J.map τ * J.map τ)) := by rw [hJ]; simp
    _ = -(((splitHom σ J (τ.comp σ) g).1ᵀ * J.map τ * (splitHom σ J τ g).1) *
          (splitHom σ J τ g⁻¹).1 * J.map τ) := by
        congr 1
        rw [Matrix.mul_assoc _ (splitHom σ J τ g).1, i1]
        simp [Matrix.mul_assoc]
    _ = _ := by rw [e]

theorem mul_entry_mem {ι : Type} [Fintype ι] {X Y : Matrix ι ι (Fv F v)}
    (hX : ∀ i j, X i j ∈ v.adicCompletionIntegers F) (hY : ∀ i j, Y i j ∈ v.adicCompletionIntegers F) (i j : ι) :
    (X * Y) i j ∈ v.adicCompletionIntegers F := by
  rw [Matrix.mul_apply]
  exact sum_mem fun l _ => mul_mem (hX i l) (hY l j)


omit [NumberField E] in
theorem comp_mem_GLint (τ : E →ₐ[F] Fv F v) (hJ : J.map τ * J.map τ = -1)
    (hint : ∀ i j, J.map τ i j ∈ v.adicCompletionIntegers F) {g : GLoc σ J v}
    (hg : splitHom σ J τ g ∈ GLint (Fin m) (v.adicCompletionIntegers F).toSubring) :
    splitHom σ J (τ.comp σ) g ∈ GLint (Fin m) (v.adicCompletionIntegers F).toSubring := by
  rw [mem_GLint_iff] at hg ⊢
  obtain ⟨h1, h2⟩ := hg
  have h2' : ∀ i j, (splitHom σ J τ g⁻¹).1 i j ∈ v.adicCompletionIntegers F := by
    rw [map_inv]; exact h2
  have h1' : ∀ i j, (splitHom σ J τ g⁻¹⁻¹).1 i j ∈ v.adicCompletionIntegers F := by
    rw [inv_inv]; exact h1
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · have e := congrFun₂ (transpose_splitHom_comp τ hJ g) j i
    rw [Matrix.transpose_apply] at e
    rw [e, Matrix.neg_apply]
    exact neg_mem (mul_entry_mem (mul_entry_mem hint h2') hint j i)
  · have e := congrFun₂ (transpose_splitHom_comp τ hJ g⁻¹) j i
    rw [Matrix.transpose_apply, map_inv] at e
    rw [e, Matrix.neg_apply]
    exact neg_mem (mul_entry_mem (mul_entry_mem hint h1') hint j i)

theorem mem_stabLoc_std_iff_GLint (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (hJ : J.map τ * J.map τ = -1)
    (hint : ∀ i j, J.map τ i j ∈ v.adicCompletionIntegers F) {g : GLoc σ J v} :
    g ∈ stabLoc σ J (stdLattice E m) v ↔
      splitHom σ J τ g ∈ GLint (Fin m) (v.adicCompletionIntegers F).toSubring :=
  (mem_stabLoc_std_iff h τ).trans ⟨fun H => H.1, fun H => ⟨H, comp_mem_GLint τ hJ hint H⟩⟩

end Gen

section Blocks

variable {D : D7} {n : ℕ} {v : Pl D}

theorem blkGL_val {R : Type} [CommRing R] (x : GL (Fin (n + n)) R) (i j : Ix n) :
    (blkGL n x).1 i j = x.1 (finSumFinEquiv i) (finSumFinEquiv j) := rfl

theorem mem_GLint_iff_blkGL {x : GL (Fin (n + n)) (Lv D v)} :
    x ∈ GLint (Fin (n + n)) (v.adicCompletionIntegers D.host.F).toSubring ↔
      blkGL n x ∈ GLint (Ix n) (v.adicCompletionIntegers D.host.F).toSubring := by
  rw [mem_GLint_iff, mem_GLint_iff, ← map_inv]
  simp only [blkGL_val]
  constructor
  · exact fun H => ⟨fun i j => H.1 _ _, fun i j => H.2 _ _⟩
  · refine fun H => ⟨fun i j => ?_, fun i j => ?_⟩
    · simpa using H.1 (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)
    · simpa using H.2 (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)

theorem Jst_map_sq (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) :
    (Jst D n).map τ * (Jst D n).map τ = -1 := by
  have e : (Jst D n).map τ = blk4 0 1 (-1) 0 := by
    ext i j
    simp only [Matrix.map_apply, Jst, blk4, Matrix.submatrix_apply]
    rcases finSumFinEquiv.symm i with a | a <;> rcases finSumFinEquiv.symm j with b | b <;>
      simp [Matrix.one_apply]
  have e2 : (Matrix.fromBlocks (-1) 0 0 (-1) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (Fv D.host.F v)) = -1 := by
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
    simp
  rw [e, blk4, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.mul_one, zero_add, add_zero, Matrix.mul_neg, neg_zero]
  rw [e2]
  ext i j
  simp [Matrix.one_apply]

theorem Jst_map_int (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (i j : Fin (n + n)) :
    (Jst D n).map τ i j ∈ v.adicCompletionIntegers D.host.F := by
  simp only [Matrix.map_apply, Jst, blk4, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with a | a <;> rcases finSumFinEquiv.symm j with b | b <;>
    simp [Matrix.one_apply] <;> split_ifs <;> simp

end Blocks

theorem mem_KUpFin_iff (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (g : GLoc D.sp.cm.sig (Jst D n) v) :
    g ∈ GlobalTheory.LocIntw.KUpFin D.sp.cm.sig (Jst D n) v ↔
      thU D n v τ g ∈ (inL (O := Ov D v) (L := Lv D v) (n := n)).range :=
  (mem_stabLoc_std_iff_GLint (isCMExt_host D) τ (Jst_map_sq τ) (Jst_map_int τ)).trans
    mem_GLint_iff_blkGL

end GlobalTheory.CompanionTheory.Jp.SplitK

end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Jp

section Skew

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {m : ℕ} {J : Matrix (Fin m) (Fin m) E} {v : HeightOneSpectrum (𝓞 F)}

def skewGram (hd : J.det ≠ 0) (τ : E →ₐ[F] Fv F v) : GL (Fin m) (Fv F v) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (J.map τ) (by
    rw [← AlgHom.mapMatrix_apply, ← AlgHom.map_det]; exact (map_ne_zero τ).2 hd)

theorem map_comp_conj_skew (hs : ∀ i j, σ (J j i) = -J i j) (τ : E →ₐ[F] Fv F v) :
    J.map (τ.comp σ) = -(J.map τ)ᵀ :=
  Matrix.ext fun i j => by
    simp only [Matrix.map_apply, AlgHom.comp_apply, Matrix.neg_apply, Matrix.transpose_apply]
    rw [hs j i, map_neg]

theorem splitPairMat_unitary_skew (h : IsCMExt F E σ) (hs : ∀ i j, σ (J j i) = -J i j) (τ : E →ₐ[F] Fv F v)
    {a b : Matrix (Fin m) (Fin m) (Fv F v)} (e : bᵀ * J.map τ * a = J.map τ) :
    Formalism.UG.cT (sigR _ σ) (splitPairMat h τ a b) * JR (Fv F v) J * splitPairMat h τ a b = JR (Fv F v) J := by
  refine splitMat_ext h τ ?_ ?_
  · rw [map_unitary, splitPairMat_map, splitPairMat_map_comp, JR_map_splitProj, e]
  · rw [map_unitary, comp_conj_conj h, splitPairMat_map, splitPairMat_map_comp, JR_map_splitProj,
      map_comp_conj_skew hs, Matrix.mul_neg, Matrix.neg_mul, neg_inj,
      ← Matrix.transpose_inj, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_transpose, ← Matrix.mul_assoc, e]

theorem splitHom_injective_skew (h : IsCMExt F E σ) (hd : J.det ≠ 0) (τ : E →ₐ[F] Fv F v) :
    Function.Injective (splitHom σ J τ) := fun g g' e => by
  have c : ∀ x : GLoc σ J v, splitHom σ J (τ.comp σ) x = dualConj (skewGram hd τ) (splitHom σ J τ x) :=
    fun x => eq_dualConj_iff.2 (splitHom_unitary τ x)
  exact matHom_injective _ σ J (Units.ext (splitMat_ext h τ (congrArg Units.val e) (by
    rw [← splitHom_val, ← splitHom_val, c, c, e])))

theorem splitHom_surjective_skew (h : IsCMExt F E σ) (hs : ∀ i j, σ (J j i) = -J i j) (hd : J.det ≠ 0)
    (τ : E →ₐ[F] Fv F v) : Function.Surjective (splitHom σ J τ) := fun x =>
  ⟨(⟨splitPairGL h τ x (dualConj (skewGram hd τ) x),
    splitPairMat_unitary_skew h hs τ ((eq_dualConj_iff (A := skewGram hd τ)).1 rfl)⟩ : HR (Fv F v) σ J),
    Units.ext (splitPairMat_map h τ _ _)⟩

end Skew

theorem blkGL_bijective {R : Type} [CommRing R] (n : ℕ) : Function.Bijective (blkGL (R := R) n) :=
  (Units.mapEquiv (Matrix.reindexAlgEquiv R R (finSumFinEquiv (m := n) (n := n)).symm).toMulEquiv).bijective

theorem Jst_mul_self (D : D7) (n : ℕ) : Jst D n * Jst D n = -1 := by
  have e : (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) D.host.E) *
      Matrix.fromBlocks 0 1 (-1) 0 = -1 := by
    rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
    simp
  have e2 := Matrix.submatrix_mul_equiv
    (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) D.host.E)
    (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) D.host.E)
    (finSumFinEquiv (m := n) (n := n)).symm (finSumFinEquiv (m := n) (n := n)).symm
    (finSumFinEquiv (m := n) (n := n)).symm
  rw [e] at e2
  refine e2.trans (Matrix.ext fun i j => ?_)
  simp [Matrix.one_apply]

theorem Jst_det_ne_zero (D : D7) (n : ℕ) : (Jst D n).det ≠ 0 := by
  have : IsUnit (Jst D n).det :=
    Matrix.isUnit_det_of_left_inverse (B := -Jst D n) (by rw [Matrix.neg_mul, Jst_mul_self, neg_neg])
  exact this.ne_zero

theorem Jst_skew (D : D7) (n : ℕ) (i j : Fin (n + n)) :
    D.sp.cm.sig (Jst D n j i) = -Jst D n i j := by
  have key : ∀ a b : Fin n ⊕ Fin n,
      D.sp.cm.sig ((Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) D.host.E) b a) =
        -(Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) D.host.E) a b := by
    rintro (a | a) (b | b) <;>
      simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
        Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply, Matrix.one_apply, map_zero, neg_zero, map_neg]
    · by_cases hab : a = b
      · subst hab; simp
      · simp [hab, Ne.symm hab]
    · by_cases hab : a = b
      · subst hab; simp
      · simp [hab, Ne.symm hab]
  exact key _ _

theorem thU_bijective : ∀ (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v),
    Function.Bijective (thU D n v τ) := fun D n _ τ =>
  (blkGL_bijective n).comp
    ⟨splitHom_injective_skew (isCMExt_host D) (Jst_det_ne_zero D n) τ,
      splitHom_surjective_skew (isCMExt_host D) (Jst_skew D n) (Jst_det_ne_zero D n) τ⟩

end GlobalTheory.CompanionTheory.Jp

end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Jp.SplitPair

section gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem evInf_trace [FiniteDimensional F E] (w : InfinitePlace F) (z : AF F ⊗[F] E) :
    evInf F w (Algebra.trace (AF F) (AF F ⊗[F] E) z) =
      Algebra.trace w.Completion (w.Completion ⊗[F] E) (compInf F E w z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]
  | tmul a x =>
    have e : compInf F E w (a ⊗ₜ[F] x) = evInf F w a ⊗ₜ[F] x := rfl
    rw [e, GlobalTheory.OppLinChar.trace_tmul', GlobalTheory.OppLinChar.trace_tmul', map_mul, AlgHom.commutes]

theorem eq_single (v : HeightOneSpectrum (𝓞 F)) (y : AF F)
    (hi : ∀ w, evInf F w y = 0) (hf : ∀ v' ≠ v, evFin F v' y = 0) :
    y = pairA F 0 (singleV F v (evFin F v y)) := by
  classical
  refine Prod.ext (funext fun w => hi w) (GlobalTheory.AdelicU.af_ext fun u => ?_)
  by_cases h : u = v
  · subst h
    change _ = singleV F u _ u
    exact (RestrictedProduct.single_eq_same _ u _).symm
  · change _ = singleV F v _ u
    exact (hf u h).trans (RestrictedProduct.single_eq_of_ne _ _ h).symm

theorem cA_eq_sigR (σ : E →ₐ[F] E) (y : AF F ⊗[F] E) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ y = sigR (AF F) σ y := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  | tmul a x => rfl

theorem psi_half_trace {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (v : HeightOneSpectrum (𝓞 F))
    (τ : E →ₐ[F] Fv F v) (ψ : AddChar (AF F) ℂ) {n : ℕ}
    (x : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) (b : Matrix (Fin n) (Fin n) E)
    (hx : ∀ i j, sigR (AF F) σ (x j i) = x i j) (hb : ∀ i j, σ (b j i) = b i j)
    (hinf : ∀ w i j, compInf F E w (x i j) = 0) (hfin : ∀ v' ≠ v, ∀ i j, compFin F E v' (x i j) = 0) :
    ψ (algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
        (∑ i, ∑ j, x i j * inclR (AF F) (b j i))) =
      psiV F ψ v (∑ i, ∑ j, splitProj τ (compFin F E v (x i j)) * τ (b j i)) := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hcm.2.2.1
  set z : AF F ⊗[F] E := ∑ i, ∑ j, x i j * inclR (AF F) (b j i) with hz
  set a : Fv F v := ∑ i, ∑ j, splitProj τ (compFin F E v (x i j)) * τ (b j i) with ha
  have hzi : ∀ w, compInf F E w z = 0 := fun w => by

    simp only [hz, map_sum, map_mul, hinf, zero_mul, Finset.sum_const_zero]
  have hzf : ∀ v' ≠ v, compFin F E v' z = 0 := fun v' h => by

    simp only [hz, map_sum, map_mul, hfin v' h, zero_mul, Finset.sum_const_zero]
  have hpi : ∀ t : E →ₐ[F] Fv F v, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW t z =
      ∑ i, ∑ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW t (x i j) * t (b j i) := fun t => by

    simp only [hz, map_sum, map_mul, GlobalTheory.OppLinChar.piW_inclR]
  have h1 : splitProj τ (compFin F E v z) = a := hpi τ
  have h2 : splitProj (τ.comp σ) (compFin F E v z) = a := by
    refine (hpi (τ.comp σ)).trans ?_
    rw [ha, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    have e : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ) (x i j) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ (x j i) := by
      rw [← hx i j, ← cA_eq_sigR]
      exact GlobalTheory.OppLinChar.piW_cA hcm τ (x j i)
    rw [e, AlgHom.comp_apply, hb i j]
    rfl
  set y : AF F := algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E) z with hy
  have hv : evFin F v y = a := by
    rw [hy, map_mul, AlgHom.commutes, GlobalTheory.OppLinChar.evFin_trace, GlobalTheory.OppLinChar.trace_split hcm τ, h1, h2,
      ← two_mul, ← mul_assoc, ← map_ofNat (algebraMap F (Fv F v)) 2, ← map_mul]
    norm_num
  have hs := eq_single v y
    (fun w => by rw [hy, map_mul, evInf_trace, hzi, map_zero, mul_zero])
    (fun v' h => by rw [hy, map_mul, GlobalTheory.OppLinChar.evFin_trace, hzf v' h, map_zero, mul_zero])
  rw [hv] at hs
  rw [hs]
  rfl

end gen

theorem pch_rat_split : ∀ (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (ψ : AddChar (AF D.host.F) ℂ) (x : hermA D n),
    (∀ w i j, compInf D.host.F D.host.E w (x.1 i j) = 0) → (∀ v' ≠ v, ∀ i j, cv D v' (x.1 i j) = 0) →
    ∀ β : HermE D n, pch ψ x.1 (rat β.1) =
      psiV D.host.F ψ v (Matrix.trace (tauC τ x.1 * β.1.map τ)) := by
  intro D n v τ ψ x hinf hfin β
  have hx : ∀ i j, sigR (AF D.host.F) D.sp.cm.sig (x.1 j i) = x.1 i j := fun i j =>
    congrFun (congrFun x.2 i) j
  have hb : ∀ i j, D.sp.cm.sig (β.1 j i) = β.1 i j := fun i j => congrFun (congrFun β.2 i) j
  exact psi_half_trace (isCMExt_host D) v τ ψ x.1 β.1 hx hb hinf hfin

end GlobalTheory.CompanionTheory.Jp.SplitPair
end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Jp

theorem nvOK_nvL : ∀ (D : D7) (v : Pl D) (ϖ : Ov D v), Irreducible ϖ → ∀ w : (Lv D v)ˣ,
    (w : Lv D v) = algebraMap (Ov D v) (Lv D v) ϖ → NvOK (O := Ov D v) (nvL D v) w := by
  intro D v ϖ hϖ w hw
  have hu1 : Formalism.UG.IsUnifV D.host.F v (algebraMap (Ov D v) (Lv D v) ϖ) := by
    unfold Formalism.UG.IsUnifV
    rw [GlobalTheory.SplitDetValue.valued_irreducible v hϖ] <;> rfl
  have hn : ‖algebraMap (Ov D v) (Lv D v) ϖ‖₊ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0)⁻¹ :=
    GlobalTheory.norm_uniformiser_eq_inv_absNorm D.host.F v _ hu1
  have hc : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0)⁻¹ ≠ 0 := by
    rw [Ne, inv_eq_zero, Nat.cast_eq_zero, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  unfold NvOK
  refine ⟨fun u => ?_, ?_⟩
  · show ‖algebraMap (Ov D v) (Lv D v) (u : Ov D v)‖₊ = 1
    have hu2 : Formalism.UG.IsUnifV D.host.F v (algebraMap (Ov D v) (Lv D v) ((u : Ov D v) * ϖ)) := by
      unfold Formalism.UG.IsUnifV
      rw [map_mul, map_mul, GlobalTheory.SplitDetValue.valued_unit v u, GlobalTheory.SplitDetValue.valued_irreducible v hϖ,
        one_mul] <;> rfl
    have h2 := GlobalTheory.norm_uniformiser_eq_inv_absNorm D.host.F v _ hu2
    rw [map_mul, nnnorm_mul, hn] at h2
    exact (mul_eq_right₀ hc).mp h2
  · show ‖(w : Lv D v)‖₊ = _
    rw [hw, hn, Fintype.card_eq_nat_card, GlobalTheory.SplitDetValue.card_residue_eq]

end GlobalTheory.CompanionTheory.Jp
end

section

open GlobalTheory.CompanionTheory.ThTot

theorem _root_.GlobalTheory.T.step_total_of_products : ProdTh → ProdMeas → StepTotal := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.stepTotal | exact GlobalTheory.CompanionTheory.ThTot.stepTotal | (intros; apply GlobalTheory.CompanionTheory.ThTot.stepTotal <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.eisenstein_theta_invariance : PositivityTheory.GramSchwartzFunctions.EC.ThetaInv := by
  first | exact @GlobalTheory.CompanionTheory.EisCellsTheta.thetaInv | exact GlobalTheory.CompanionTheory.EisCellsTheta.thetaInv | (intros; apply GlobalTheory.CompanionTheory.EisCellsTheta.thetaInv <;> assumption)
end

section

open PositivityTheory.Rg.Rsw

theorem _root_.GlobalTheory.T.partial_constant_fourier_coefficient : MapsExist → PositivityTheory.PfSWUS.FourierZero → PcFc := by
  first | exact @GlobalTheory.CompanionTheory.PcFc.target | exact GlobalTheory.CompanionTheory.PcFc.target | (intros; apply GlobalTheory.CompanionTheory.PcFc.target <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.centre_coefficient_equivariance : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (F : G D n → ℂ), LeftInv (GF D n) F → ∀ (c : hermA D ρ) (h : G D n), zc M m ψ b₀ F (M.nzx c 0 * h) = chz ψ b₀ c * zc M m ψ b₀ F h := by
  first | exact @GlobalTheory.CompanionTheory.ZcShift.zc_shift | exact GlobalTheory.CompanionTheory.ZcShift.zc_shift | (intros; apply GlobalTheory.CompanionTheory.ZcShift.zc_shift <;> assumption)
end

module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LGenKE
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle005
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LGenKD
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle007
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)




namespace PositivityTheory.Rg.Rsw.L.LGenK

open Matrix

section Blocks

variable {R : Type} [CommRing R] {n : ℕ}

theorem blocks_one : bA (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) = 1 ∧ bB (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) = 0 ∧
    bC (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) = 0 ∧ bD (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) = 1 := by
  have h : (1 : Matrix (Fin (n + n)) (Fin (n + n)) R).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks 1 0 0 1 := by
    rw [Matrix.submatrix_one_equiv, Matrix.fromBlocks_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · show ((1 : Matrix (Fin (n + n)) (Fin (n + n)) R).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁ = 1
    rw [h, Matrix.toBlocks_fromBlocks₁₁]
  · show ((1 : Matrix (Fin (n + n)) (Fin (n + n)) R).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂ = 0
    rw [h, Matrix.toBlocks_fromBlocks₁₂]
  · show ((1 : Matrix (Fin (n + n)) (Fin (n + n)) R).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0
    rw [h, Matrix.toBlocks_fromBlocks₂₁]
  · show ((1 : Matrix (Fin (n + n)) (Fin (n + n)) R).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂ = 1
    rw [h, Matrix.toBlocks_fromBlocks₂₂]

theorem bC_map {S : Type} [CommRing S] (f : R →+* S) (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : bC (M.map f) = (bC M).map f := rfl
theorem bD_map {S : Type} [CommRing S] (f : R →+* S) (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : bD (M.map f) = (bD M).map f := rfl

theorem weyl_block_matrix_map {S : Type} [CommRing S] (f : R →+* S) :
    (blk4 (0 : Matrix (Fin n) (Fin n) R) 1 (-1) 0).map f = blk4 0 1 (-1) 0 := by
  rw [block_matrix_map]
  have h0 : (0 : Matrix (Fin n) (Fin n) R).map f = 0 := Matrix.map_zero _ (map_zero f)
  have h1 : (1 : Matrix (Fin n) (Fin n) R).map f = 1 := Matrix.map_one _ (map_zero f) (map_one f)
  have hn : (-1 : Matrix (Fin n) (Fin n) R).map f = -1 := by
    rw [Matrix.map_neg _ (fun a => map_neg f a), h1]
  rw [h0, h1, hn]

end Blocks

variable {D : D7} {n : ℕ}

theorem sig_invol (x : D.host.E) : D.sp.cm.sig (D.sp.cm.sig x) = x := by
  exact star_star x

theorem sig_ne : D.sp.cm.sig ≠ AlgHom.id D.host.F D.host.E := by
  intro h
  have h1 : ∀ a : D.host.E, star a = a := fun a => by
    have := DFunLike.congr_fun h a
    exact this
  have htop : (⊥ : Subalgebra D.host.F D.host.E) = ⊤ := by
    refine eq_top_iff.mpr fun a _ => ?_
    rw [Algebra.mem_bot]
    obtain ⟨r, hr⟩ := (D.sp.cm.fixed a).mp (h1 a)
    exact ⟨r, hr⟩
  have h2 := Subalgebra.bot_eq_top_iff_finrank_eq_one.mp htop
  rw [D.sp.cm.deg2] at h2
  exact absurd h2 (by norm_num)

private theorem cv_cA_lemma (v : Pl D) (x : AE D) :
    cv D v (cA D x) = sigR (Fv D.host.F v) D.sp.cm.sig (cv D v x) := by
  have key : ((Algebra.TensorProduct.map (GlobalTheory.AdelicU.evFin D.host.F v) (AlgHom.id D.host.F D.host.E)).comp
      (Algebra.TensorProduct.map (AlgHom.id D.host.F (AF D.host.F)) D.sp.cm.sig)) =
      (Algebra.TensorProduct.map (AlgHom.id D.host.F (Fv D.host.F v)) D.sp.cm.sig).comp
        (Algebra.TensorProduct.map (GlobalTheory.AdelicU.evFin D.host.F v) (AlgHom.id D.host.F D.host.E)) := by
    rw [← Algebra.TensorProduct.map_comp, ← Algebra.TensorProduct.map_comp]
    simp only [AlgHom.id_comp, AlgHom.comp_id]
  exact DFunLike.congr_fun key x

theorem unit_loc (v : Pl D) (g : G D n) :
    cj (sigR (Fv D.host.F v) D.sp.cm.sig) (fromBlocks (bA ((mat g).map (cv D v))) (bB ((mat g).map (cv D v)))
        (bC ((mat g).map (cv D v))) (bD ((mat g).map (cv D v)))) * fromBlocks 0 1 (-1) 0 *
      fromBlocks (bA ((mat g).map (cv D v))) (bB ((mat g).map (cv D v))) (bC ((mat g).map (cv D v)))
        (bD ((mat g).map (cv D v))) = fromBlocks 0 1 (-1) 0 := by
  have hcj : (cj (cA D) (mat g)).map (cv D v) =
      cj (sigR (Fv D.host.F v) D.sp.cm.sig) ((mat g).map (cv D v)) := by
    ext i j
    exact cv_cA_lemma v (mat g j i)
  have hJ : (Jm D n).map (cv D v) = blk4 0 1 (-1) 0 := weyl_block_matrix_map (cv D v)
  have h2 := congrArg (fun N => N.map (cv D v)) (mat_unit g)
  simp only [Matrix.map_mul] at h2
  rw [hcj, hJ] at h2
  apply unit_fromBlocks
  rw [block_matrix_of_blocks]
  exact h2

theorem det_map_u {T : Type} [CommRing T] (f : AE D →+* T) (M : Mx D (n + n) (n + n)) (X : Mx D n n) :
    f (bD M + bC M * X).det = (bD (M.map f) + bC (M.map f) * X.map f).det := by
  rw [RingHom.map_det, RingHom.map_add (f := _), RingHom.map_mul, bD_map, bC_map]
  rfl

theorem exists_X {S : Finset (Pl D)} (hS2 : ∀ v ∉ S, (2 : 𝓞 D.host.F) ∉ v.asIdeal) {k : G D n} (hk : k ∈ KOff D n S) :
    ∃ X : Mx D n n, cj (cA D) X = X ∧ X.map (infPart D) = 0 ∧ (∀ v ∈ S, X.map (cv D v) = 0) ∧
      (∀ v ∉ S, ∀ i j, cv D v (X i j) ∈ intLoc D.host.F D.host.E v) ∧
      (∀ v, ∃ z ∈ intLoc D.host.F D.host.E v, cv D v (bD (mat k) + bC (mat k) * X).det * z = 1) ∧
      IsUnit (bD (mat k) + bC (mat k) * X).det := by
  classical
  obtain ⟨hinf, hSv, hint⟩ := KOff_props hk
  have hloc : ∀ v, v ∉ S → ∃ x : Matrix (Fin n) (Fin n) (Fv D.host.F v ⊗[D.host.F] D.host.E),
      (∀ i j, x i j ∈ intLoc D.host.F D.host.E v) ∧ cj (sigR (Fv D.host.F v) D.sp.cm.sig) x = x ∧
      ∃ z ∈ intLoc D.host.F D.host.E v,
        (bD ((mat k).map (cv D v)) + bC ((mat k).map (cv D v)) * x).det * z = 1 := fun v hv =>
    local_choice v D.sp.cm.sig sig_invol sig_ne D.sp.cm.deg2 (hS2 v hv) _ _ _ _
      (fun i j => hint v hv _ _) (fun i j => hint v hv _ _) (fun i j => hint v hv _ _) (fun i j => hint v hv _ _)
      (unit_loc v k)
  choose x hx using hloc
  let b : ∀ v : Pl D, Matrix (Fin n) (Fin n) (Fv D.host.F v ⊗[D.host.F] D.host.E) :=
    fun v => if hv : v ∈ S then 0 else x v hv
  have hb : ∀ v i j, b v i j ∈ intLoc D.host.F D.host.E v := by
    intro v i j
    by_cases hv : v ∈ S
    · simp only [b, dif_pos hv]; exact zero_mem _
    · simp only [b, dif_neg hv]; exact (hx v hv).1 i j
  obtain ⟨X, hXc, hXi⟩ := glue_mat D b hb
  have hXv : ∀ v (hv : v ∉ S), X.map (cv D v) = x v hv := by
    intro v hv; ext i j; rw [Matrix.map_apply, hXc]; simp only [b, dif_neg hv]
  have hXinf : X.map (infPart D) = 0 := by ext i j; exact hXi i j
  have hz : ∀ v, ∃ z ∈ intLoc D.host.F D.host.E v, cv D v (bD (mat k) + bC (mat k) * X).det * z = 1 := by
    intro v
    rw [det_map_u]
    by_cases hv : v ∈ S
    · refine ⟨1, one_mem _, ?_⟩
      rw [hSv v hv, blocks_one.2.2.1, blocks_one.2.2.2]; simp
    · rw [hXv v hv]; exact (hx v hv).2.2
  refine ⟨X, ?_, hXinf, fun v hv => ?_, fun v hv i j => ?_, hz, ?_⟩
  · ext i j
    apply ext_comp
    · intro v
      rw [cj_apply, cv_cA, hXc, hXc]
      by_cases hv : v ∈ S
      · simp only [b, dif_pos hv, Matrix.zero_apply, map_zero]
      · simp only [b, dif_neg hv]
        have := congrFun (congrFun (hx v hv).2.1 i) j
        rw [cj_apply] at this
        exact this
    · rw [cj_apply, infPart_cA, hXi, hXi, map_zero]
  · ext i j; rw [Matrix.map_apply, hXc]; simp only [b, dif_pos hv, Matrix.zero_apply]
  · rw [hXc]; exact hb v i j
  · refine isUnit_of_comp D _ hz ?_
    rw [det_map_u, hinf, hXinf, blocks_one.2.2.1, blocks_one.2.2.2]; simp

end PositivityTheory.Rg.Rsw.L.LGenK
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LFixTh

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

open PositivityTheory.Rg.Rsw.L

variable {D : D7} {ρ p n : ℕ}

theorem one_cc {R : Type} [Ring R] (i j : Fin n) :
    (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) (Fin.castAdd n i) (Fin.castAdd n j) = (1 : Matrix (Fin n) (Fin n) R) i j := by
  by_cases h : i = j
  · subst h
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
  · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne]
    exact fun h' => h (Fin.castAdd_injective _ _ h')

theorem map_one_apply {R : Type} [Ring R] (f : AE D →+* R) (i j : Fin n) :
    f ((1 : Mx D n n) i j) = (1 : Matrix (Fin n) (Fin n) R) i j := by
  by_cases h : i = j
  · subst h
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
  · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h, map_zero]

theorem mat_inv_levi {g : G D p} {a : GL (Fin p) (AE D)} (ha : mat g = blk4 a.1 0 0 (adj (a⁻¹).1)) :
    mat g⁻¹ = blk4 (a⁻¹).1 0 0 (adj a.1) := by
  have h1 : (a⁻¹).1 * a.1 = 1 := a.inv_mul
  have h2 : adj a.1 * adj (a⁻¹).1 = 1 := by
    delta GlobalTheory.MixModel.adj
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.transpose_one]
  have hprod : blk4 (a⁻¹).1 0 0 (adj a.1) * blk4 a.1 0 0 (adj (a⁻¹).1) = 1 := by
    delta GlobalTheory.StdUnn.blk4
    rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, h1, h2, Matrix.fromBlocks_one]
    exact Matrix.submatrix_one_equiv _
  delta GlobalTheory.StdUnn.mat at ha ⊢
  rw [map_inv]
  exact Units.inv_eq_of_mul_eq_one_left (by rw [ha]; exact hprod)

private theorem matHom_proj_fst_eq_mat_map_cv (g : G D p) (v : Pl D) :
    (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig (GlobalTheory.StdUnn.Jst D p)
      (GlobalTheory.AdelicU.proj D.sp.cm.sig (GlobalTheory.StdUnn.Jst D p) v g)).1 = (mat g).map (cv D v) := by
  delta GlobalTheory.AdelicU.proj GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.mapH
  rfl

private theorem exists_mat_apply_eq_one_at_S_and_int_off_S {S : Finset (Pl D)} {h : G D p} (hh : h ∈ KOff D p S) :
    (∀ (w : NumberField.InfinitePlace D.host.F) (i j : Fin (p + p)),
      compInf D.host.F D.host.E w (mat h i j) = (1 : Matrix (Fin (p + p)) (Fin (p + p)) _) i j) ∧
    (∀ v ∈ S, ∀ i j : Fin (p + p), cv D v (mat h i j) = (1 : Matrix (Fin (p + p)) (Fin (p + p)) _) i j) ∧
    (∀ v ∉ S, ∀ i j : Fin (p + p), cv D v (mat h i j) ∈ intLoc D.host.F D.host.E v) := by
  delta PositivityTheory.Rg.Rsw.L.KOff GlobalTheory.AdelicU.levelOff GlobalTheory.AdelicU.finAwayPts at hh
  obtain ⟨hfa, hoff⟩ := Subgroup.mem_inf.mp hh
  obtain ⟨hfin, haway⟩ := Subgroup.mem_inf.mp hfa
  refine ⟨fun w i j => ?_, fun v hv i j => ?_, fun v hv i j => ?_⟩
  · delta GlobalTheory.AdelicU.finPts at hfin
    have h1 := congrArg (fun u : GL (Fin (p + p)) _ => u.1 i j) (MonoidHom.mem_ker.mp hfin)
    have h2 : (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA _) (AlgHom.id (↥D.host.F) D.host.E)) (mat h i j) =
        (1 : Matrix (Fin (p + p)) (Fin (p + p)) _) i j := h1
    have e := Algebra.TensorProduct.map_comp (GlobalTheory.AutFunCompare.evW w) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA (↥D.host.F))
      (AlgHom.id (↥D.host.F) D.host.E) (AlgHom.id (↥D.host.F) D.host.E)
    rw [AlgHom.id_comp] at e
    have hc : compInf D.host.F D.host.E w (mat h i j) =
        (Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id (↥D.host.F) D.host.E))
          ((Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA _) (AlgHom.id (↥D.host.F) D.host.E)) (mat h i j)) :=
      DFunLike.congr_fun e (mat h i j)
    rw [hc, h2]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
    · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, map_zero]
  · delta GlobalTheory.AdelicU.awayPts at haway
    have hker := MonoidHom.mem_ker.mp (Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp haway v) hv)
    have h3 := matHom_proj_fst_eq_mat_map_cv h v
    rw [hker, map_one] at h3
    have h4 := congrArg (fun M : Matrix (Fin (p + p)) (Fin (p + p)) _ => M i j) h3
    exact h4.symm
  · have hs := (GlobalTheory.AdelicU.mem_stabLoc_stdLattice_iff.mp
      (Subgroup.mem_comap.mp (Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hoff v) hv))).1 i j
    rw [matHom_proj_fst_eq_mat_map_cv] at hs
    exact hs

theorem levi_blocks {S : Finset (Pl D)} {g : G D p} (hg : g ∈ KOff D p S) {a : GL (Fin p) (AE D)}
    (ha : mat g = blk4 a.1 0 0 (adj (a⁻¹).1)) :
    (∀ i j, (∀ w, compInf D.host.F D.host.E w (a.1 i j) = (1 : Matrix (Fin p) (Fin p) _) i j ∧
      compInf D.host.F D.host.E w ((a⁻¹).1 i j) = (1 : Matrix (Fin p) (Fin p) _) i j) ∧
      (∀ v ∈ S, cv D v (a.1 i j) = (1 : Matrix (Fin p) (Fin p) _) i j ∧
        cv D v ((a⁻¹).1 i j) = (1 : Matrix (Fin p) (Fin p) _) i j) ∧
      (∀ v ∉ S, cv D v (a.1 i j) ∈ intLoc D.host.F D.host.E v ∧ cv D v ((a⁻¹).1 i j) ∈ intLoc D.host.F D.host.E v)) := by
  have hgi : g⁻¹ ∈ KOff D p S := inv_mem hg
  obtain ⟨hI, hS, hO⟩ := exists_mat_apply_eq_one_at_S_and_int_off_S hg
  obtain ⟨hI', hS', hO'⟩ := exists_mat_apply_eq_one_at_S_and_int_off_S hgi
  have hA : ∀ i j, mat g (Fin.castAdd p i) (Fin.castAdd p j) = a.1 i j := by
    intro i j
    rw [ha]
    delta GlobalTheory.StdUnn.blk4
    rw [Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_castAdd,
      Matrix.fromBlocks_apply₁₁]
  have hAi : ∀ i j, mat g⁻¹ (Fin.castAdd p i) (Fin.castAdd p j) = (a⁻¹).1 i j := by
    intro i j
    rw [mat_inv_levi ha]
    delta GlobalTheory.StdUnn.blk4
    rw [Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_castAdd,
      Matrix.fromBlocks_apply₁₁]
  intro i j
  refine ⟨fun w => ⟨?_, ?_⟩, fun v hv => ⟨?_, ?_⟩, fun v hv => ⟨?_, ?_⟩⟩
  · rw [← hA, hI, one_cc]
  · rw [← hAi, hI', one_cc]
  · rw [← hA, hS v hv, one_cc]
  · rw [← hAi, hS' v hv, one_cc]
  · rw [← hA]
    exact hO v hv _ _
  · rw [← hAi]
    exact hO' v hv _ _

theorem levi_good {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e) {g : G D p} (hg : g ∈ KOff D p S)
    {a : GL (Fin p) (AE D)} (ha : mat g = blk4 a.1 0 0 (adj (a⁻¹).1)) (f : Mx D ρ p → ℂ) (hf : Good S e f)
    (y : Mx D ρ p) : f (y * a.1) = f y := by
  have hb := levi_blocks hg ha
  have he1 : ∀ k j, e * a.1 k j = e * (1 : Mx D p p) k j := by
    intro k j
    apply PositivityTheory.Rg.Rsw.L.LIdemEx.ae_ext
    · intro w
      rw [map_mul, map_mul, ((hb k j).1 w).1, map_one_apply]
    · intro v
      rw [map_mul, map_mul, map_one_apply]
      by_cases hv : v ∈ S
      · rw [((hb k j).2.1 v hv).1]
      · rw [he.2 v, if_neg hv, zero_mul, zero_mul]
  have hsmul : e • (y * a.1) = e • y := by
    ext i j
    rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
    calc e * (y * a.1) i j = ∑ k, y i k * (e * a.1 k j) := by
          rw [Matrix.mul_apply, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = ∑ k, y i k * (e * (1 : Mx D p p) k j) := Finset.sum_congr rfl fun k _ => by rw [he1]
      _ = e * ∑ k, y i k * (1 : Mx D p p) k j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = e * y i j := by rw [← Matrix.mul_apply, Matrix.mul_one]
  have hint : ∀ (x : Mx D ρ p) (b : Mx D p p), IntOff S x →
      (∀ v ∉ S, ∀ k j, cv D v (b k j) ∈ intLoc D.host.F D.host.E v) → IntOff S (x * b) := by
    intro x b hx hb' v hv i j
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.mul_apply, map_sum]
    exact Subring.sum_mem _ fun k _ => by
      rw [map_mul]
      exact Subring.mul_mem _ (hx v hv i k) (hb' v hv k j)
  have hyI : IntOff S (y * a.1) ↔ IntOff S y := by
    constructor
    · intro h
      have h' := hint _ (a⁻¹).1 h fun v hv k j => ((hb k j).2.2 v hv).2
      rwa [Matrix.mul_assoc, a.mul_inv, Matrix.mul_one] at h'
    · intro h
      exact hint _ a.1 h fun v hv k j => ((hb k j).2.2 v hv).1
  rw [hf (y * a.1), hf y, hsmul]
  by_cases h : IntOff S y
  · rw [if_pos (hyI.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (hyI.mp h')), if_neg h]

end PositivityTheory.Rg.Rsw.L.LFixTh

end
end

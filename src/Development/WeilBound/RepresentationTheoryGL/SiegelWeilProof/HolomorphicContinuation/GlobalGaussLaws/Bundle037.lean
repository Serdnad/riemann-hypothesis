module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle238
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle033
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle001
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle015
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle036
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.PlaceFacts
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle034
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle242
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle010
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.DA

variable {D : D7} {n : ℕ}

theorem mat_mul (g h : G D n) : mat (g * h) = mat g * mat h := by
  simp only [mat, map_mul, Units.val_mul]

theorem mat_one : mat (1 : G D n) = 1 := by
  simp only [mat, map_one, Units.val_one]

theorem mat_inj {g h : G D n} (e : mat g = mat h) : g = h := by
  apply GlobalTheory.AdelicU.matHom_injective
  exact Units.ext e

theorem compAt_mul (θ : InfFam D) (τ : D.what₂.Tau) {k : ℕ} (A B : Mx D k k) :
    compAt θ τ (A * B) = compAt θ τ A * compAt θ τ B :=
  Matrix.map_mul (f := (θ τ).comp (infPart D))

theorem compAt_one (θ : InfFam D) (τ : D.what₂.Tau) {k : ℕ} : compAt θ τ (1 : Mx D k k) = 1 := by
  unfold compAt
  exact Matrix.map_one _ (by simp) (by simp)

theorem finMap_mul {k : ℕ} (A B : Mx D k k) : (A * B).map (finPart D) = A.map (finPart D) * B.map (finPart D) :=
  Matrix.map_mul (f := finPart D)

theorem compAt_conjT (θ : InfFam D) (hθ : IsInfFam θ) (τ : D.what₂.Tau) {k : ℕ} (A : Mx D k k) :
    compAt θ τ (Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) A) = (compAt θ τ A)ᴴ := by
  ext i j
  simp only [compAt, Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply]
  exact (GlobalTheory.StdUnn.RealComp.real_components D θ hθ).2.1 _ _

theorem compAt_Jst (θ : InfFam D) (hθ : IsInfFam θ) (τ : D.what₂.Tau) :
    compAt θ τ ((Jst D n).map (incA D)) = reidx (JJ n) := by
  ext i j
  simp only [compAt, Matrix.map_apply]
  rw [(GlobalTheory.StdUnn.RealComp.real_components D θ hθ).2.2.1]
  simp only [Jst, blk4, reidx, JJ, Matrix.submatrix_apply]
  rcases h1 : finSumFinEquiv.symm i with a | a <;> rcases h2 : finSumFinEquiv.symm j with b | b <;>
    simp [Matrix.one_apply, apply_ite]

end PositivityTheory.Rg.Sw.Glob.DA
end
end

section

noncomputable section

open scoped Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.AdelicU GlobalTheory.StdUnn IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar




namespace PositivityTheory.Rg.Sw.Glob.GenGlueH

variable {D : D7} {n : ℕ}

theorem compAt_sigR (v : GlobalTheory.FinPl.Pl D) (z : AE D) :
    GlobalTheory.FinPl.compAt D v (sigR (AF D.host.F) D.sp.cm.sig z) =
      sigR (Fv D.host.F v) D.sp.cm.sig (GlobalTheory.FinPl.compAt D v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a e => rfl

theorem glueFull (f : D.what₂.Tau → ℂ) (z : ∀ v : GlobalTheory.FinPl.Pl D, Ev D v)
    (hz : ∀ v, z v ∈ intLoc D.host.F D.host.E v) :
    ∃ x : AE D, (∀ τ, Formalism.IndefR.Eqv.psiT D τ x = f τ) ∧ ∀ v, GlobalTheory.FinPl.compAt D v x = z v := by
  obtain ⟨s, -, hs⟩ := GenUnitH.glueEntry z hz
  refine ⟨Formalism.IndefR.Eqv.glueA D (Formalism.IndefR.Eqv.splitInv D f) (finPart D s),
    fun τ => Formalism.IndefR.Eqv.psiT_glueA D τ f _, fun v => ?_⟩
  show GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v (finPart D _) = _
  rw [Formalism.IndefR.Eqv.finPart_glueA]
  exact hs v

theorem map_inv_of {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (M : Matrix (Fin n) (Fin n) R)
    (h : IsUnit M.det) : (M⁻¹).map f = (M.map f)⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv M h, Matrix.map_one _ (map_zero f) (map_one f)]

theorem adj_map {S : Type} [CommRing S] (f : AE D →+* S) (σS : S →+* S)
    (hf : ∀ z, f (sigR (AF D.host.F) D.sp.cm.sig z) = σS (f z)) (x : Matrix (Fin n) (Fin n) (AE D)) :
    (GlobalTheory.MixModel.adj x).map f = ((x.map f).map σS)ᵀ := by
  ext i j
  simp only [GlobalTheory.MixModel.adj, Matrix.map_apply, Matrix.transpose_apply]
  exact hf _

theorem isUnit_of_intUnit {v : GlobalTheory.FinPl.Pl D} {z : Ev D v} (h : IsIntUnit z) : IsUnit z := by
  obtain ⟨-, z', -, hz⟩ := h
  exact ⟨⟨z, z', hz, by rw [mul_comm]; exact hz⟩, rfl⟩

end PositivityTheory.Rg.Sw.Glob.GenGlueH

namespace PositivityTheory.Rg.Sw.Glob

open GenGlueH

theorem glueLevi : GlueLevi := by
  intro D n a hint hdet
  have hE : ∀ i j, ∃ x : AE D, (∀ τ, Formalism.IndefR.Eqv.psiT D τ x = (1 : Matrix (Fin n) (Fin n) ℂ) i j) ∧
      ∀ v, GlobalTheory.FinPl.compAt D v x = a v i j := fun i j => glueFull _ (fun v => a v i j) (fun v => hint v i j)
  choose A hAτ hAv using hE
  let A' : Matrix (Fin n) (Fin n) (AE D) := Matrix.of A
  have hτ : ∀ τ, A'.map (Formalism.IndefR.Eqv.psiT D τ) = 1 := fun τ => by ext i j; exact hAτ i j τ
  have hv : ∀ v, A'.map (GlobalTheory.FinPl.compAt D v) = a v := fun v => by ext i j; exact hAv i j v
  have hdetA : IsUnit A'.det := by
    apply unitAE D
    · intro τ
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hτ τ, Matrix.det_one]
      exact one_ne_zero
    · intro v
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hv v]
      exact hdet v
  let u : GL (Fin n) (AE D) := ((Matrix.isUnit_iff_isUnit_det A').2 hdetA).unit
  have hu : (u : Matrix (Fin n) (Fin n) (AE D)) = A' := IsUnit.unit_spec _
  have hui : ((u⁻¹ : GL (Fin n) (AE D)) : Matrix (Fin n) (Fin n) (AE D)) = A'⁻¹ := by
    rw [Matrix.coe_units_inv, hu]
  obtain ⟨m, hm⟩ := GlobalTheory.StdUnn.Model.exists_levi u
  refine ⟨m, Or.inr (Or.inl ⟨_, _, hm⟩), fun v => ?_, fun τ => ?_⟩
  · rw [show cTv (a v) = ((a v).map (sigR (Fv D.host.F v) D.sp.cm.sig))ᵀ from rfl,
      hm, PlaceFactsH.block_matrix_map, hu, hv v, hui,
      adj_map (GlobalTheory.FinPl.compAt D v) (sigR (Fv D.host.F v) D.sp.cm.sig) (compAt_sigR v),
      map_inv_of (GlobalTheory.FinPl.compAt D v) A' hdetA, hv v,
      map_inv_of (sigR (Fv D.host.F v) D.sp.cm.sig) (a v) (isUnit_of_intUnit (hdet v)),
      Matrix.transpose_nonsing_inv, Matrix.map_zero _ (map_zero _)]
  · rw [hm, PlaceFactsH.block_matrix_map, hu, hτ τ, hui,
      adj_map (Formalism.IndefR.Eqv.psiT D τ) (starRingEnd ℂ) (fun z => Formalism.IndefR.Eqv.psiT_sigR D τ z),
      map_inv_of (Formalism.IndefR.Eqv.psiT D τ) A' hdetA, hτ τ, inv_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one,
      Matrix.map_zero _ (map_zero _), PlaceFactsH.block_matrix_one]

theorem glueW : GlueW := by
  intro D n I
  have hE : ∀ i, ∃ x : AE D, (∀ τ, Formalism.IndefR.Eqv.psiT D τ x = 0) ∧
      ∀ v, GlobalTheory.FinPl.compAt D v x = if i ∈ I v then 1 else 0 := fun i =>
    glueFull _ _ (fun v => by split_ifs; exacts [one_mem _, zero_mem _])
  choose e heτ hev using hE
  have hσe : ∀ i, sigR (AF D.host.F) D.sp.cm.sig (e i) = e i := fun i => by
    apply Formalism.IndefR.Eqv.ae_ext' D
    · intro τ
      rw [Formalism.IndefR.Eqv.psiT_sigR, heτ, map_zero]
    · apply GenUnitH.finExt
      intro v
      show GlobalTheory.FinPl.compAt D v (sigR (AF D.host.F) D.sp.cm.sig (e i)) = GlobalTheory.FinPl.compAt D v (e i)
      rw [compAt_sigR, hev]
      split_ifs <;> simp
  let B : Matrix (Fin n) (Fin n) (AE D) := Matrix.diagonal e
  have hB : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) B = B := by
    ext i j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, B, Matrix.diagonal_apply]
    by_cases h : j = i
    · subst h; simp [hσe]
    · simp [h, Ne.symm h]
  have hB' : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (-B) = -B := by rw [GenInfH.cT_neg', hB]
  have h1 : GenInfH.nEl B hB ∈ genSet D n := Or.inl ⟨B, GenInfH.mat_nEl B hB⟩
  have h2 : GenInfH.nBarEl (-B) hB' ∈ genSet D n := Or.inr (Or.inr ⟨-B, GenInfH.mat_nBarEl _ _⟩)
  refine ⟨GenInfH.nEl B hB * GenInfH.nBarEl (-B) hB' * GenInfH.nEl B hB,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure h1) (Subgroup.subset_closure h2))
      (Subgroup.subset_closure h1), fun v => ?_, fun τ => ?_⟩
  · have hBv : B.map (GlobalTheory.FinPl.compAt D v) = eI (I v) := by
      ext i j
      simp only [Matrix.map_apply, B, Matrix.diagonal_apply, eI]
      by_cases h : i = j
      · subst h; simp [hev]
      · simp [h]
    show (blk4 1 B 0 1 * blk4 1 0 (-B) 1 * blk4 1 B 0 1).map (GlobalTheory.FinPl.compAt D v) = wIm (I v)
    rw [Matrix.map_mul, Matrix.map_mul, PlaceFactsH.block_matrix_map, PlaceFactsH.block_matrix_map, hBv,
      Matrix.map_neg _ (map_neg _), hBv, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _),
      GenInfH.weyl_idem _ (GenInfH.eI_mul_self _)]
    rfl
  · have hBτ : B.map (Formalism.IndefR.Eqv.psiT D τ) = 0 := by
      ext i j
      simp only [Matrix.map_apply, B, Matrix.diagonal_apply, Matrix.zero_apply]
      split_ifs <;> simp [heτ]
    show (blk4 1 B 0 1 * blk4 1 0 (-B) 1 * blk4 1 B 0 1).map (Formalism.IndefR.Eqv.psiT D τ) = 1
    rw [Matrix.map_mul, Matrix.map_mul, PlaceFactsH.block_matrix_map, PlaceFactsH.block_matrix_map, hBτ,
      Matrix.map_neg _ (map_neg _), hBτ, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _),
      neg_zero, PlaceFactsH.block_matrix_one, Matrix.one_mul, Matrix.one_mul]

end PositivityTheory.Rg.Sw.Glob
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.LocLawH

variable {D : D7} {n : ℕ}

theorem cnt_add {m : ℕ} (ε : Fin m → Bool) : cnt ε true + cnt ε false = m := by
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m))) (fun a => ε a = true)
  simp only [Finset.card_univ, Fintype.card_fin, Bool.not_eq_true] at this
  exact this

theorem pqOf_add {m : ℕ} (ε : Fin m → Bool) (l : D.what₂.Tau → ℝ) (τ : D.what₂.Tau) :
    (pqOf ε l τ).1 + (pqOf ε l τ).2 = m := by
  unfold pqOf
  split_ifs
  · exact cnt_add ε
  · rw [add_comm]; exact cnt_add ε

theorem npow_sq (z : ℂ) (m : ℕ) : npow (‖z‖₊ ^ 2) ((m : ℂ) / 2) = ((‖z‖ : ℝ) : ℂ) ^ (m : ℤ) := by
  simp only [npow, NNReal.coe_pow, coe_nnnorm]
  rw [show ((m : ℂ) / 2) = (((m : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (sq_nonneg _), ← Real.rpow_natCast ‖z‖ 2, ← Real.rpow_mul (norm_nonneg _),
    show ((2 : ℕ) : ℝ) * ((m : ℝ) / 2) = (m : ℝ) by push_cast; ring, Real.rpow_natCast, zpow_natCast,
    Complex.ofReal_pow]


theorem scal {χ : (AE D)ˣ →* Circle} {θ : InfFam D} (hθ : IsInfFam θ) {σ : (D.what₂.Tau → ℂ) →+ AE D}
    (hσ : GlobalTheory.FockCompare.Chart θ σ) {τ : D.what₂.Tau} {m : ℕ} (k j : ℤ)
    (hk : ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → (∀ τ', τ' ≠ τ → θ τ' (infPart D (x : AE D)) = 1) →
      ((χ x : Circle) : ℂ) = (θ τ (infPart D (x : AE D)) / (‖θ τ (infPart D (x : AE D))‖ : ℂ)) ^ k)
    (hj : k - m = j + j) (p q : ℕ) (hpq : p + q = m) (y : PositivityTheory.Rg.Sw.GR n) (hy : (mR y).toBlocks₂₁ = 0) :
    (χ (Matrix.GeneralLinearGroup.det (unitAt hσ τ (aOf y hy))) : ℂ) *
      npow (absA D (Matrix.GeneralLinearGroup.det (unitAt hσ τ (aOf y hy)))) ((m : ℂ) / 2) = F0 p q (k - j) y := by
  have hv : (unitAt hσ τ (aOf y hy)).1 = baseColumnsAt σ τ (mR y).toBlocks₁₁ := by rw [unitAt_val, aOf_val]
  have hxv : ((Matrix.GeneralLinearGroup.det (unitAt hσ τ (aOf y hy)) : (AE D)ˣ) : AE D) =
      (baseColumnsAt σ τ (mR y).toBlocks₁₁).det := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hv]
  have hf : finPart D (((Matrix.GeneralLinearGroup.det (unitAt hσ τ (aOf y hy))) : (AE D)ˣ) : AE D) = 1 := by
    rw [hxv, RingHom.map_det, RingHom.mapMatrix_apply, finite_part_adelic_point_matrix hσ, Matrix.det_one]
  have hcomp : ∀ τ', θ τ' (infPart D (((Matrix.GeneralLinearGroup.det (unitAt hσ τ (aOf y hy))) : (AE D)ˣ) : AE D)) = (compAt θ τ' (baseColumnsAt σ τ (mR y).toBlocks₁₁)).det := by
    intro τ'
    rw [hxv]
    show cf θ τ' (baseColumnsAt σ τ (mR y).toBlocks₁₁).det = _
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
    rfl
  have hτ : θ τ (infPart D (((Matrix.GeneralLinearGroup.det (unitAt hσ τ (aOf y hy))) : (AE D)ˣ) : AE D)) = ((mR y).toBlocks₁₁).det := by rw [hcomp, component_adelic_point_matrix hσ]
  have hne : ∀ τ', τ' ≠ τ → θ τ' (infPart D (((Matrix.GeneralLinearGroup.det (unitAt hσ τ (aOf y hy))) : (AE D)ˣ) : AE D)) = 1 := fun τ' h => by
    rw [hcomp, component_adelic_point_ne hσ h, Matrix.det_one]
  have habs : absA D (Matrix.GeneralLinearGroup.det (unitAt hσ τ (aOf y hy))) = ‖((mR y).toBlocks₁₁).det‖₊ ^ 2 := by
    rw [show absA D (Matrix.GeneralLinearGroup.det (unitAt hσ τ (aOf y hy))) = ‖θ τ (infPart D (((Matrix.GeneralLinearGroup.det (unitAt hσ τ (aOf y hy))) : (AE D)ˣ) : AE D))‖₊ ^ 2 from GlobalTheory.StabAtPlace.absE_single hθ (Matrix.GeneralLinearGroup.det (unitAt hσ τ (aOf y hy))) τ hf hne, hτ]
  rw [hk _ hf hne, hτ, habs, npow_sq]
  have hZ := det_ne y hy
  have hu1 : u1 (mR y) = (mR y).toBlocks₂₂ := by simp only [u1, hy, smul_zero, zero_add]
  have hu2 : u2 (mR y) = (mR y).toBlocks₂₂ := by simp only [u2, hy, smul_zero, neg_zero, zero_add]
  have hdy : (mR y).det = ((mR y).toBlocks₁₁).det * ((mR y).toBlocks₂₂).det := by
    conv_lhs => rw [fromBlocks_of y hy]
    rw [Matrix.det_fromBlocks_zero₂₁]
  have hR : ((‖((mR y).toBlocks₁₁).det‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 hZ)
  have hd : ((mR y).toBlocks₂₂).det = ((mR y).toBlocks₁₁).det / ((‖((mR y).toBlocks₁₁).det‖ : ℝ) : ℂ) ^ 2 := by
    have h1 : ((mR y).toBlocks₂₂).det = (star ((mR y).toBlocks₁₁).det)⁻¹ := eq_inv_of_mul_eq_one_right (det_rel y hy)
    have h2 : ((mR y).toBlocks₁₁).det * star ((mR y).toBlocks₁₁).det = ((‖((mR y).toBlocks₁₁).det‖ : ℝ) : ℂ) ^ 2 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
    have h3 : star ((mR y).toBlocks₁₁).det ≠ 0 := star_ne_zero.2 hZ
    rw [h1, eq_div_iff (pow_ne_zero 2 hR), ← h2]
    field_simp
  simp only [F0, f0, hu1, hu2, hdy, hd]
  exact alg_id _ _ hZ hR k j p q m hpq hj

end PositivityTheory.Rg.Sw.Glob.LocLawH

namespace PositivityTheory.Rg.Sw.Glob

theorem lIlaw : LIlaw := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hC.hθ
  obtain ⟨k, ⟨j, hj⟩, hk⟩ := LocLawH.chi_exp hC.hθ hC.hχ hC.hη τ
  exact ⟨k - j, fun P y g hy => by
    rw [LocLawH.glob_law hC hL hσ P y g hy, LocLawH.scal hC.hθ hσ k j hk hj _ _ (LocLawH.pqOf_add ε l τ) y hy]⟩

end PositivityTheory.Rg.Sw.Glob
end
end

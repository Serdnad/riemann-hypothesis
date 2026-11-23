module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle081
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle004
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle007
public import GroundTheory.HeightsAndTheta.Theta.AdelicFourier
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.CharSum
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LGenKE
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LGenKD
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LThBddB
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

namespace PositivityTheory.Rg.Rsw.L.LApproxId

open GlobalTheory.CompanionTheory.SiegelND.Coef.TestN

theorem memHA (D : D7) (t : ℕ) (X : Mx D t t) : X ∈ hermA D t ↔ X ∈ HermR (AF D.host.F) D.sp.cm.sig t := by
  constructor
  · intro h a c
    have h' : GlobalTheory.MixModel.adj X = X := h
    have := congrFun (congrFun h' a) c
    simpa [GlobalTheory.MixModel.adj, Matrix.transpose_apply, Matrix.map_apply] using this
  · intro h
    change GlobalTheory.MixModel.adj X = X
    ext a c
    simpa [GlobalTheory.MixModel.adj, Matrix.transpose_apply, Matrix.map_apply] using h a c

theorem smul_memA (D : D7) (t : ℕ) (e : AE D) (he : cA D e = e) (X : Mx D t t) (h : X ∈ hermA D t) :
    e • X ∈ hermA D t := by
  have h' : GlobalTheory.MixModel.adj X = X := h
  change GlobalTheory.MixModel.adj (e • X) = e • X
  ext a c
  have := congrFun (congrFun h' a) c
  simp only [GlobalTheory.MixModel.adj, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
    map_mul, he] at this ⊢
  rw [this]

theorem pch_eq (D : D7) (t : ℕ) (ψ : AddChar (AF D.host.F) ℂ) (X T : Mx D t t) (hX : X ∈ hermA D t)
    (hT : T ∈ hermA D t) :
    pch ψ X T = ψ (pairHerm (AF D.host.F) D.sp.cm.sig t ⟨X, (memHA D t X).1 hX⟩ ⟨T, (memHA D t T).1 hT⟩) := by
  simp only [pch, halfTr, trA, pairHerm, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]

theorem coord_fix (D : D7) (t : ℕ) (e : AE D) (ε : AF D.host.F) (heS : e = algebraMap (AF D.host.F) (AE D) ε)
    {d : ℕ} (b : Module.Basis (Fin d) D.host.F D.host.E)
    (X : HermR (AF D.host.F) D.sp.cm.sig t) (hX : e • X.1 = X.1) (i : Idx t d) :
    ε * hCo (AF D.host.F) D.sp.cm.sig b X i = hCo (AF D.host.F) D.sp.cm.sig b X i :=
  (hCo_smul _ b ε X X (by rw [← heS, hX]) i).symm

theorem mem_of_coord (D : D7) (t : ℕ) (e : AE D) (ε : AF D.host.F) (heS : e = algebraMap (AF D.host.F) (AE D) ε)
    (hcA : cA D e = e) {d : ℕ} (b : Module.Basis (Fin d) D.host.F D.host.E)
    (eA : HermR (AF D.host.F) D.sp.cm.sig t ≃ₜ+ (Idx t d → AF D.host.F))
    (heA : ∀ X, eA X = hCo (AF D.host.F) D.sp.cm.sig b X) (y : HermR (AF D.host.F) D.sp.cm.sig t)
    (hw : ∀ i, ε * eA y i = eA y i) : e • y.1 = y.1 := by
  have hyA : y.1 ∈ hermA D t := (memHA D t y.1).2 y.2
  have hY := (memHA D t _).1 (smul_memA D t e hcA y.1 hyA)
  have h1 : eA ⟨e • y.1, hY⟩ = eA y := by
    funext i
    rw [heA, hCo_smul _ b ε y ⟨e • y.1, hY⟩ (by rw [← heS]) i, ← heA, hw]
  exact congrArg Subtype.val (eA.injective h1)



theorem exTheta' (D : D7) (t : ℕ) (e : AE D) (ε : AF D.host.F) (heS : e = algebraMap (AF D.host.F) (AE D) ε)
    (hcA : cA D e = e) {d : ℕ} (b : Module.Basis (Fin d) D.host.F D.host.E)
    (eA : HermR (AF D.host.F) D.sp.cm.sig t ≃ₜ+ (Idx t d → AF D.host.F))
    (heA : ∀ X, eA X = hCo (AF D.host.F) D.sp.cm.sig b X) :
    ∃ Θ : hermS D t e ≃ₜ+ (Idx t d → fixE ε),
      ∀ x i, ((Θ x i) : AF D.host.F) = eA ⟨x.1.1, (memHA D t x.1.1).1 x.1.2⟩ i := by
  have hfix : ∀ (x : hermS D t e) i, ε * eA ⟨x.1.1, (memHA D t x.1.1).1 x.1.2⟩ i =
      eA ⟨x.1.1, (memHA D t x.1.1).1 x.1.2⟩ i := fun x i => by
    rw [heA]; exact coord_fix D t e ε heS b ⟨x.1.1, (memHA D t x.1.1).1 x.1.2⟩ x.2 i
  have hinv : ∀ v : Idx t d → fixE ε, e • (eA.symm (fun i => (v i).1)).1 = (eA.symm (fun i => (v i).1)).1 :=
    fun v => mem_of_coord D t e ε heS hcA b eA heA _ (fun i => by rw [eA.apply_symm_apply]; exact (v i).2)
  refine ⟨{ toFun := fun x i => ⟨eA ⟨x.1.1, (memHA D t x.1.1).1 x.1.2⟩ i, hfix x i⟩
            invFun := fun v => ⟨⟨(eA.symm (fun i => (v i).1)).1, (memHA D t _).2 (eA.symm _).2⟩, hinv v⟩
            left_inv := fun x => by
              apply Subtype.ext; apply Subtype.ext
              simp
            right_inv := fun v => by
              funext i
              apply Subtype.ext
              simp
            map_add' := fun x y => by
              funext i
              apply Subtype.ext
              change eA _ i = eA _ i + eA _ i
              exact congrFun (map_add eA ⟨x.1.1, (memHA D t x.1.1).1 x.1.2⟩ ⟨y.1.1, (memHA D t y.1.1).1 y.1.2⟩) i
            continuous_toFun := continuous_pi fun i => Continuous.subtype_mk ((continuous_apply i).comp
              (eA.continuous.comp ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _))) _
            continuous_invFun := ((continuous_subtype_val.comp (eA.symm.continuous.comp
              (continuous_pi fun i => continuous_subtype_val.comp (continuous_apply i)))).subtype_mk _).subtype_mk _ },
    fun x i => rfl⟩

theorem e_eq (D : D7) (S : Finset (Pl D)) (e : AE D) (he : IsIdem S e) :
    e = algebraMap (AF D.host.F) (AE D) ((1, LIdemEx.indS S) : AF D.host.F) := by
  have h : e = LIdemEx.eS S := LIdemEx.ae_ext _ _ (fun w => by rw [he.1 w, (LIdemEx.isIdem_eS S).1 w])
    (fun v => by rw [he.2 v, (LIdemEx.isIdem_eS S).2 v])
  exact h.trans rfl

end PositivityTheory.Rg.Rsw.L.LApproxId

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

namespace PositivityTheory.Rg.Rsw.L.LMajor

variable {D : D7} {a b : ℕ}

abbrev cA (θ : InfFam D) (x : Mx D a b) : D.what₂.Tau → Fin a → Fin b → ℂ := fun τ i j => compAt θ τ x i j

abbrev row (i : Fin a) (x : Mx D a b) : Mx D 1 b := x.submatrix (fun _ => i) id

theorem cA_idem (θ : InfFam D) {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e) (x : Mx D a b) :
    cA θ (e • x) = cA θ x := by
  funext τ i j
  rw [cA, compAt_smul, infPart_idem he, map_one, one_smul]

theorem cv_sF (v : Pl D) (z : AE D) : cv D v (sF D * z) = cv D v z :=
  cv_congr v (by rw [map_mul, finPart_sF, one_mul])

theorem good_mul (θ : InfFam D) {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e) {Φ : Mx D a b → ℂ}
    (hG : Good S e Φ) (q : (D.what₂.Tau → Fin a → Fin b → ℂ) → ℂ) : Good S e (fun x => q (cA θ x) * Φ x) := by
  intro x
  have h := hG x
  split_ifs at h ⊢ with hx
  · show q (cA θ x) * Φ x = q (cA θ (e • x)) * Φ (e • x)
    rw [h, cA_idem θ he]
  · show q (cA θ x) * Φ x = 0
    rw [h, mul_zero]

theorem re_im_mul {z w : ℂ} (hz : 0 ≤ z.re ∧ z.im = 0) (hw : 0 ≤ w.re ∧ w.im = 0) :
    0 ≤ (z * w).re ∧ (z * w).im = 0 := by
  rw [Complex.mul_re, Complex.mul_im, hz.2, hw.2]
  exact ⟨by simpa using mul_nonneg hz.1 hw.1, by simp⟩

theorem re_im_prod {ι : Type} (s : Finset ι) (u : ι → ℂ) (h : ∀ i, 0 ≤ (u i).re ∧ (u i).im = 0) :
    0 ≤ (∏ i ∈ s, u i).re ∧ (∏ i ∈ s, u i).im = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi]; exact re_im_mul (h i) ih

end PositivityTheory.Rg.Rsw.L.LMajor

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




namespace PositivityTheory.Rg.Rsw.L.LGenK

open Matrix

variable {D : D7} {n : ℕ}

theorem map_one' {T : Type} [CommRing T] (f : AE D →+* T) : (1 : Mx D n n).map f = 1 :=
  Matrix.map_one _ (map_zero f) (map_one f)

theorem map_zero' {T : Type} [CommRing T] (f : AE D →+* T) {m p : ℕ} : (0 : Mx D m p).map f = 0 :=
  Matrix.map_zero _ (map_zero f)

theorem unit_n (Y : Mx D n n) (hY : cj (cA D) Y = Y) :
    cj (cA D) (blk4 1 Y 0 1) * Jm D n * blk4 1 Y 0 1 = Jm D n := by
  rw [conj_block_matrix, cj_one, cj_zero, hY, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp

def nOf (Y : Mx D n n) (hY : cj (cA D) Y = Y) : G D n := (exists_G _ (unit_n Y hY)).choose

theorem mat_nOf (Y : Mx D n n) (hY : cj (cA D) Y = Y) : mat (nOf Y hY) = blk4 1 Y 0 1 :=
  (exists_G _ (unit_n Y hY)).choose_spec

theorem isN_nOf (Y : Mx D n n) (hY : cj (cA D) Y = Y) : IsN (nOf Y hY) := ⟨Y, mat_nOf Y hY⟩

theorem cj_Jm : cj (cA D) (Jm D n) = blk4 0 (-1) 1 0 := by
  rw [conj_block_matrix, cj_one, cj_zero, cj_neg, cj_one]

theorem unit_w : cj (cA D) (Jm D n) * Jm D n * Jm D n = Jm D n := by
  rw [cj_Jm, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]; simp

def wE (D : D7) (n : ℕ) : G D n := (exists_G _ (unit_w (D := D) (n := n))).choose

theorem mat_wE : mat (wE D n) = Jm D n := (exists_G _ (unit_w (D := D) (n := n))).choose_spec

theorem isW_wE : IsW (wE D n) := mat_wE

theorem mat_wE_inv : mat (wE D n)⁻¹ = blk4 0 (-1) 1 0 :=
  mat_inv_eq (by rw [mat_wE, submatrix_fromBlocks_mul]; simp [block_matrix_one])

theorem mat_conj (Y : Mx D n n) (hY : cj (cA D) Y = Y) :
    mat (wE D n * nOf Y hY * (wE D n)⁻¹) = blk4 1 0 (-Y) 1 := by
  rw [mat_mul, mat_mul, mat_wE, mat_nOf, mat_wE_inv, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]; simp

theorem nOf_mem {S : Finset (Pl D)} (Y : Mx D n n) (hY : cj (cA D) Y = Y) (hinf : Y.map (infPart D) = 0)
    (hS : ∀ v ∈ S, Y.map (cv D v) = 0) (hint : ∀ v ∉ S, IntM v Y) : nOf Y hY ∈ KOff D n S := by
  have hinv : mat (nOf Y hY)⁻¹ = blk4 1 (-Y) 0 1 := mat_inv_eq (by rw [mat_nOf, submatrix_fromBlocks_mul]; simp [block_matrix_one])
  apply mem_KOff
  · rw [mat_nOf, block_matrix_map, hinf, map_one', map_zero', block_matrix_one]
  · intro v hv; rw [mat_nOf, block_matrix_map, hS v hv, map_one', map_zero', block_matrix_one]
  · intro v hv i j
    rw [hinv, mat_nOf]
    exact ⟨integral_block_matrix_iff.2 ⟨IntM.one, hint v hv, IntM.zero, IntM.one⟩ i j,
      integral_block_matrix_iff.2 ⟨IntM.one, (hint v hv).neg, IntM.zero, IntM.one⟩ i j⟩

theorem conj_mem {S : Finset (Pl D)} (Y : Mx D n n) (hY : cj (cA D) Y = Y) (hinf : Y.map (infPart D) = 0)
    (hS : ∀ v ∈ S, Y.map (cv D v) = 0) (hint : ∀ v ∉ S, IntM v Y) :
    wE D n * nOf Y hY * (wE D n)⁻¹ ∈ KOff D n S := by
  have hinv : mat (wE D n * nOf Y hY * (wE D n)⁻¹)⁻¹ = blk4 1 0 Y 1 :=
    mat_inv_eq (by rw [mat_conj, submatrix_fromBlocks_mul]; simp [block_matrix_one])
  have hneg : ∀ {T : Type} [CommRing T] (f : AE D →+* T), (-Y).map f = -(Y.map f) := fun f => Matrix.map_neg _ (map_neg f) _
  apply mem_KOff
  · rw [mat_conj, block_matrix_map, hneg, hinf, neg_zero, map_one', map_zero', block_matrix_one]
  · intro v hv; rw [mat_conj, block_matrix_map, hneg, hS v hv, neg_zero, map_one', map_zero', block_matrix_one]
  · intro v hv i j
    rw [hinv, mat_conj]
    exact ⟨integral_block_matrix_iff.2 ⟨IntM.one, IntM.zero, (hint v hv).neg, IntM.one⟩ i j,
      integral_block_matrix_iff.2 ⟨IntM.one, IntM.zero, hint v hv, IntM.one⟩ i j⟩

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

namespace PositivityTheory.Rg.Rsw.L.LThBdd

variable {D : D7} {n : ℕ} {W : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
  {μ : Measure (Mx D W.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ W.rank n)}

theorem eval_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → schwartzA θ W.rank n) (X : Mx D W.rank n) :
    (∑ i ∈ s, c i • f i).1 X = ∑ i ∈ s, c i * (f i).1 X := by
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem omega_nb (hω : IsWeilSch ψ χ θ W μ ω) {nb : hermA D n → G D n} (hnb : IsNMap nb) (x : hermA D n)
    (Φ : schwartzA θ W.rank n) (X : Mx D W.rank n) : (ω (nb x) Φ).1 X = pch ψ x.1 (ip W X X) * Φ.1 X := by
  exact hω.unip (nb x) x.1 (hnb x) Φ X

theorem omega_cut (hω : IsWeilSch ψ χ θ W μ ω) {nb : hermA D n → G D n} (hnb : IsNMap nb) {v : Pl D}
    (C : Cut D n v) (Ψ Ψ' : schwartzA θ W.rank n) (hΨ' : Ψ' = ∑ x ∈ C.s, C.co x • ω (nb x) Ψ) {g : G D n}
    (hg : GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g = 1) (X : Mx D W.rank n) :
    (ω g Ψ').1 X = cutF ψ C (ip W X X) * (ω g Ψ).1 X := by
  subst hΨ'

  simp only [map_sum, map_smul]
  rw [eval_sum, show cutF ψ C (ip W X X) = ∑ x ∈ C.s, C.co x * pch ψ x.1 (ip W X X) from rfl,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hcomm : nb x * g = g * nb x :=
    PositivityTheory.Rg.Rsw.L.LThBdd.commute_of_atPts
      (PositivityTheory.Rg.Rsw.L.LThBdd.nb_mem_atPts hnb x (C.inf x hx) (C.off x hx)) hg
  rw [← Module.End.mul_apply, ← map_mul, ← hcomm, map_mul, Module.End.mul_apply,
    omega_nb hω hnb x, mul_assoc]

theorem pch_eq_one (hω : IsWeilSch ψ χ θ W μ ω) {nb : hermA D n → G D n} (hnb : IsNMap nb) {v : Pl D}
    (Ψ : schwartzA θ W.rank n) (hΨ : ∀ k ∈ KAt D n v, ω k Ψ = Ψ) {g : G D n}
    (hg : GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g = 1) (X : Mx D W.rank n) (hX : (ω g Ψ).1 X ≠ 0)
    (o : hermA D n) (ho : IntAt v o) : pch ψ o.1 (ip W X X) = 1 := by
  have hk := PositivityTheory.Rg.Rsw.L.LThBdd.nb_mem_KAt hnb o ho
  have hfix : ω (nb o) (ω g Ψ) = ω g Ψ := by
    rw [← Module.End.mul_apply, ← map_mul,
      PositivityTheory.Rg.Rsw.L.LThBdd.commute_of_atPts (Subgroup.mem_inf.mp hk).2 hg, map_mul,
      Module.End.mul_apply, hΨ _ hk]
  have h := omega_nb hω hnb o (ω g Ψ) X
  rw [hfix] at h
  exact mul_right_cancel₀ hX (h.symm.trans (one_mul _).symm)

theorem inner_rat' (ξ : Matrix (Fin W.rank) (Fin n) D.host.E) :
    GlobalTheory.StdUnn.inner W (rat ξ : Mx D W.rank n) (rat ξ) = rat (gramQ W ξ) := by
  rw [show GlobalTheory.StdUnn.inner W (rat ξ : Mx D W.rank n) (rat ξ) =
      GlobalTheory.MixModel.adj (rat ξ) * (GlobalTheory.MixModel.rat (Formalism.BasicNotions.HSpace.gram W) * rat ξ) from rfl,
    ← GlobalTheory.MixModel.rat_conjTranspose, ← GlobalTheory.MixModel.rat_mul, ← GlobalTheory.MixModel.rat_mul,
    ← GlobalTheory.MixModel.cT_sig]
  rfl

theorem ip_mt_rat (h : GA D W) (ξ : Matrix (Fin W.rank) (Fin n) D.host.E) :
    ip W (mm (mt W h⁻¹) (rat ξ)) (mm (mt W h⁻¹) (rat ξ)) = rat (gramQ W ξ) := by
  calc ip W (mm (mt W h⁻¹) (rat ξ)) (mm (mt W h⁻¹) (rat ξ))
      = GlobalTheory.MixModel.adj (mt W h⁻¹ * rat ξ) * (GlobalTheory.MixModel.gA W * (mt W h⁻¹ * rat ξ)) := rfl
    _ = GlobalTheory.MixModel.adj (rat ξ : Mx D W.rank n) *
          ((GlobalTheory.MixModel.adj (mt W h⁻¹) * (GlobalTheory.MixModel.gA W * mt W h⁻¹)) * rat ξ) := by
        rw [GlobalTheory.MixModel.adj_mul]
        simp only [Matrix.mul_assoc]
    _ = GlobalTheory.StdUnn.inner W (rat ξ : Mx D W.rank n) (rat ξ) := by
        rw [GlobalTheory.MixModel.mt_unitary]
        rfl
    _ = rat (gramQ W ξ) := inner_rat' ξ

theorem rank_gramQ_le (ξ : Matrix (Fin W.rank) (Fin n) D.host.E) : (gramQ W ξ).rank ≤ ξ.rank := by
  exact (Matrix.rank_mul_le_right _ _).trans (Matrix.rank_mul_le_right _ _)

theorem term_zero (hω : IsWeilSch ψ χ θ W μ ω) {nb : hermA D n → G D n} (hnb : IsNMap nb) {v : Pl D}
    (C : Cut D n v) (hC : C.Kills ψ W.rank) (Ψ Ψ' : schwartzA θ W.rank n) (hΨ : ∀ k ∈ KAt D n v, ω k Ψ = Ψ)
    (hΨ' : Ψ' = ∑ x ∈ C.s, C.co x • ω (nb x) Ψ) {g : G D n} (hg : GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g = 1)
    (h : GA D W) (ξ : Matrix (Fin W.rank) (Fin n) D.host.E) (hξ : ξ.rank ≠ W.rank) :
    (ω g Ψ').1 (mm (mt W h⁻¹) (rat ξ)) = 0 := by
  rw [omega_cut hω hnb C Ψ Ψ' hΨ' hg, ip_mt_rat]
  by_cases h0 : (ω g Ψ).1 (mm (mt W h⁻¹) (rat ξ)) = 0
  · rw [h0, mul_zero]
  · have hq : gramQ W ξ = ξᴴ * (Formalism.BasicNotions.HSpace.gram W * ξ) := by
      rw [← GlobalTheory.MixModel.cT_sig]
      rfl
    have hherm : ((gramQ W ξ).map ⇑(D.sp.cm.sig)).transpose = gramQ W ξ := by
      change Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (gramQ W ξ) = gramQ W ξ
      rw [GlobalTheory.MixModel.cT_sig, hq, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, GlobalTheory.MixModel.gram_conjTranspose, Matrix.mul_assoc]
    have hlt : (gramQ W ξ).rank < W.rank :=
      (rank_gramQ_le ξ).trans_lt (lt_of_le_of_ne (Matrix.rank_le_height ξ) hξ)
    have hcut := hC (⟨gramQ W ξ, hherm⟩ : PositivityTheory.GramSchwartzFunctions.HermE D n) hlt (fun o ho => by
      have := pch_eq_one hω hnb Ψ hΨ hg _ h0 o ho
      rwa [ip_mt_rat] at this)
    rw [show cutF ψ C (rat (gramQ W ξ)) = 0 from hcut, zero_mul]

theorem theta_nb (hω : IsWeilSch ψ χ θ W μ ω) {nb : hermA D n → G D n} (hnb : IsNMap nb) {v : Pl D}
    (C : Cut D n v) (hC : C.Kills ψ W.rank) (Ψ Ψ' : schwartzA θ W.rank n) (hΨ : ∀ k ∈ KAt D n v, ω k Ψ = Ψ)
    (hΨ' : Ψ' = ∑ x ∈ C.s, C.co x • ω (nb x) Ψ) (x : hermA D n) {g : G D n}
    (hg : GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g = 1) (h : GA D W) :
    theta ω Ψ' (nb x * g) h =
      ∑' y : {y : Matrix (Fin W.rank) (Fin n) D.host.E // y.rank = W.rank},
        pch ψ x.1 (ip W (mm (mt W h⁻¹) (rat y.1)) (mm (mt W h⁻¹) (rat y.1))) * (ω g Ψ').1 (mm (mt W h⁻¹) (rat y.1)) := by
  have hfun : ∀ ξ : Matrix (Fin W.rank) (Fin n) D.host.E,
      ((ω (nb x * g)) Ψ').1 (mm (mt W h⁻¹) (rat ξ)) =
        pch ψ x.1 (ip W (mm (mt W h⁻¹) (rat ξ)) (mm (mt W h⁻¹) (rat ξ))) *
          (ω g Ψ').1 (mm (mt W h⁻¹) (rat ξ)) := by
    intro ξ
    rw [map_mul, Module.End.mul_apply]
    exact omega_nb hω hnb x _ _
  have hsub : Function.support (fun ξ : Matrix (Fin W.rank) (Fin n) D.host.E =>
      pch ψ x.1 (ip W (mm (mt W h⁻¹) (rat ξ)) (mm (mt W h⁻¹) (rat ξ))) *
        (ω g Ψ').1 (mm (mt W h⁻¹) (rat ξ))) ⊆ {y | y.rank = W.rank} := by
    intro ξ hξ
    by_contra hne
    apply hξ
    show _ * _ = 0
    rw [term_zero hω hnb C hC Ψ Ψ' hΨ hΨ' hg h ξ hne, mul_zero]
  calc theta ω Ψ' (nb x * g) h
      = ∑' ξ : Matrix (Fin W.rank) (Fin n) D.host.E, ((ω (nb x * g)) Ψ').1 (mm (mt W h⁻¹) (rat ξ)) := rfl
    _ = ∑' ξ : Matrix (Fin W.rank) (Fin n) D.host.E,
          pch ψ x.1 (ip W (mm (mt W h⁻¹) (rat ξ)) (mm (mt W h⁻¹) (rat ξ))) *
            (ω g Ψ').1 (mm (mt W h⁻¹) (rat ξ)) := tsum_congr hfun
    _ = _ := (tsum_subtype_eq_of_support_subset hsub).symm

theorem fix_open {nb : hermA D n → G D n} (hnb : IsNMap nb) {v : Pl D} (C : Cut D n v) (Ψ Ψ' : schwartzA θ W.rank n)
    (hΨ : ∀ k ∈ KAt D n v, ω k Ψ = Ψ) (hΨ' : Ψ' = ∑ x ∈ C.s, C.co x • ω (nb x) Ψ) {k : G D n}
    (hk : k ∈ Ucut nb v C.s) (hkv : k ∈ atPts D.sp.cm.sig (Jst D n) {v}) : ω k Ψ' = Ψ' := by
  subst hΨ'

  simp only [map_sum, map_smul]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hc := PositivityTheory.Rg.Rsw.L.LThBdd.conj_mem_KAt hnb C hk hkv hx
  congr 1
  calc ω k (ω (nb x) Ψ) = ω (nb x * ((nb x)⁻¹ * k * nb x)) Ψ := by
        rw [show nb x * ((nb x)⁻¹ * k * nb x) = k * nb x by group, map_mul, Module.End.mul_apply]
    _ = ω (nb x) (ω ((nb x)⁻¹ * k * nb x) Ψ) := by rw [map_mul, Module.End.mul_apply]
    _ = ω (nb x) Ψ := by rw [hΨ _ hc]

end PositivityTheory.Rg.Rsw.L.LThBdd

end
end

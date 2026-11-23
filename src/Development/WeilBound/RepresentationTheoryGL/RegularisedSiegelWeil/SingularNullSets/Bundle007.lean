module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
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

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace PositivityTheory.Rg.Rsw.L.LGenK

variable {D : D7}

def IntM {D : D7} {m p : ℕ} (v : Pl D) (M : Mx D m p) : Prop := ∀ i j, cv D v (M i j) ∈ intLoc D.host.F D.host.E v

namespace IntM

variable {v : Pl D} {m p q : ℕ}

theorem add {M N : Mx D m p} (hM : IntM v M) (hN : IntM v N) : IntM v (M + N) := fun i j => by
  rw [Matrix.add_apply, map_add (f := _)]; exact add_mem (hM i j) (hN i j)

theorem neg {M : Mx D m p} (hM : IntM v M) : IntM v (-M) := fun i j => by
  rw [Matrix.neg_apply, map_neg]; exact neg_mem (hM i j)

theorem zero : IntM v (0 : Mx D m p) := fun i j => by
  rw [Matrix.zero_apply, map_zero]; exact zero_mem _

theorem one : IntM v (1 : Mx D m m) := fun i j => by
  rw [Matrix.one_apply]
  split_ifs
  · rw [map_one]; exact one_mem _
  · rw [map_zero]; exact zero_mem _

theorem mul {M : Mx D m p} {N : Mx D p q} (hM : IntM v M) (hN : IntM v N) : IntM v (M * N) := fun i j => by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.mul_apply, map_sum]
  exact sum_mem fun k _ => by rw [map_mul]; exact mul_mem (hM i k) (hN k j)

theorem inv {M : Mx D m m} (hM : IntM v M) (hu : IsUnit M.det)
    (hdet : ∃ z ∈ intLoc D.host.F D.host.E v, cv D v M.det * z = 1) : IntM v M⁻¹ := by
  obtain ⟨z, hz, hdz⟩ := hdet
  obtain ⟨u, hu'⟩ := hu
  have hinv : cv D v (Ring.inverse M.det) = z := by
    rw [← hu', Ring.inverse_unit]
    have h1 : cv D v ((u⁻¹ : (AE D)ˣ) : AE D) * cv D v (u : AE D) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    rw [hu'] at h1
    calc cv D v ((u⁻¹ : (AE D)ˣ) : AE D) = cv D v ((u⁻¹ : (AE D)ˣ) : AE D) * (cv D v M.det * z) := by
          rw [hdz, mul_one]
      _ = z := by rw [← mul_assoc, h1, one_mul]

  let N : Matrix (Fin m) (Fin m) (intLoc D.host.F D.host.E v) := fun i j => ⟨cv D v (M i j), hM i j⟩
  have hN : N.map (intLoc D.host.F D.host.E v).subtype = M.map (cv D v) := rfl
  have hadj : ∀ i j, cv D v (M.adjugate i j) ∈ intLoc D.host.F D.host.E v := by
    intro i j
    have e1 : cv D v (M.adjugate i j) = (M.map (cv D v)).adjugate i j :=
      congrFun (congrFun (RingHom.map_adjugate (cv D v) M) i) j
    have e2 : (intLoc D.host.F D.host.E v).subtype (N.adjugate i j) =
        (N.map (intLoc D.host.F D.host.E v).subtype).adjugate i j :=
      congrFun (congrFun (RingHom.map_adjugate (intLoc D.host.F D.host.E v).subtype N) i) j
    rw [e1, ← hN, ← e2]
    exact (N.adjugate i j).2
  intro i j
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, map_mul, hinv]
  exact mul_mem hz (hadj i j)

end IntM

theorem integral_block_matrix_iff {v : Pl D} {n : ℕ} {a b c d : Mx D n n} :
    IntM v (blk4 a b c d) ↔ IntM v a ∧ IntM v b ∧ IntM v c ∧ IntM v d := by
  have key : ∀ x y, blk4 a b c d (finSumFinEquiv x) (finSumFinEquiv y) = Matrix.fromBlocks a b c d x y := by
    intro x y; simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  constructor
  · intro h
    refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
    · have := h (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j))
      rwa [key, Matrix.fromBlocks_apply₁₁] at this
    · have := h (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j))
      rwa [key, Matrix.fromBlocks_apply₁₂] at this
    · have := h (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j))
      rwa [key, Matrix.fromBlocks_apply₂₁] at this
    · have := h (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr j))
      rwa [key, Matrix.fromBlocks_apply₂₂] at this
  · rintro ⟨ha, hb, hc, hd⟩ i j
    obtain ⟨i', rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j', rfl⟩ := finSumFinEquiv.surjective j
    show cv D v (blk4 a b c d _ _) ∈ _
    rw [key]
    rcases i' with i' | i' <;> rcases j' with j' | j'
    · rw [Matrix.fromBlocks_apply₁₁]; exact ha i' j'
    · rw [Matrix.fromBlocks_apply₁₂]; exact hb i' j'
    · rw [Matrix.fromBlocks_apply₂₁]; exact hc i' j'
    · rw [Matrix.fromBlocks_apply₂₂]; exact hd i' j'

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

namespace PositivityTheory.Rg.Rsw.L.LMajor

variable {D : D7}

theorem repr_map {F E R R' ι : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] [CommRing R']
    [Algebra F R'] (φ : R →ₐ[F] R') (b : Module.Basis ι F E) (z : R ⊗[F] E) (k : ι) :
    (Algebra.TensorProduct.basis R' b).repr (Algebra.TensorProduct.map φ (AlgHom.id F E) z) k =
      φ ((Algebra.TensorProduct.basis R b).repr z k) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]
  | tmul a e => simp [Algebra.TensorProduct.basis_repr_tmul]



theorem infPart_eq_of {e e' : AE D}
    (h : ∀ w, compInf D.host.F D.host.E w e = compInf D.host.F D.host.E w e') : infPart D e = infPart D e' := by
  let b := Module.Basis.ofVectorSpace D.host.F D.host.E
  show Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) e =
    Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) e'
  apply (Algebra.TensorProduct.basis (Ainf D.host.F) b).repr.injective
  refine Finsupp.ext fun k => ?_
  rw [repr_map, repr_map]
  funext w
  have h1 := repr_map (evInf D.host.F w) b e k
  have h2 := repr_map (evInf D.host.F w) b e' k
  have hw : Algebra.TensorProduct.map (evInf D.host.F w) (AlgHom.id D.host.F D.host.E) e =
      Algebra.TensorProduct.map (evInf D.host.F w) (AlgHom.id D.host.F D.host.E) e' := h w
  rw [hw, h2] at h1
  exact h1.symm

theorem infPart_idem {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e) : infPart D e = 1 :=
  (infPart_eq_of (e' := 1) fun w => (he.1 w).trans (map_one _).symm).trans (map_one _)



theorem cv_eq (v : Pl D) (a : AE D) :
    cv D v a = Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v) (AlgHom.id D.host.F D.host.E)
      (finPart D a) := by
  induction a using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, map_zero]
  | add x y hx hy => rw [RingHom.map_add (f := _), hx, hy, RingHom.map_add (f := _), map_add (f := _)]
  | tmul x y =>
    show Algebra.TensorProduct.map (evFin D.host.F v) (AlgHom.id D.host.F D.host.E) (x ⊗ₜ[D.host.F] y) =
      Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v) (AlgHom.id D.host.F D.host.E)
        (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) (x ⊗ₜ[D.host.F] y))
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
    rfl

theorem cv_congr (v : Pl D) {a a' : AE D} (h : finPart D a = finPart D a') : cv D v a = cv D v a' := by
  rw [cv_eq, cv_eq, h]

def afF (D : D7) : AF D.host.F := (0, 1)

theorem fstA_afF : fstA D.host.F (afF D) = 0 := rfl

theorem sndA_afF : sndA D.host.F (afF D) = 1 := rfl

def sF (D : D7) : AE D := afF D ⊗ₜ[D.host.F] (1 : D.host.E)



theorem infPart_sF : infPart D (sF D) = 0 := by
  show Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)
    (afF D ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
  rw [Algebra.TensorProduct.map_tmul, fstA_afF, TensorProduct.zero_tmul]



theorem finPart_sF : finPart D (sF D) = 1 := by
  show Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)
    (afF D ⊗ₜ[D.host.F] (1 : D.host.E)) = 1
  rw [Algebra.TensorProduct.map_tmul, sndA_afF]
  rfl

theorem compAt_smul (θ : InfFam D) (τ : D.what₂.Tau) {m n : ℕ} (c : AE D) (x : Mx D m n) :
    compAt θ τ (c • x) = θ τ (infPart D c) • compAt θ τ x := by
  ext i j
  simp [compAt, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

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

namespace PositivityTheory.Rg.Rsw.L.LIdemEx

variable {D : D7}

theorem repr_map' {F E R R' ι : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] [CommRing R']
    [Algebra F R'] (φ : R →ₐ[F] R') (b : Module.Basis ι F E) (z : R ⊗[F] E) (k : ι) :
    (Algebra.TensorProduct.basis R' b).repr (Algebra.TensorProduct.map φ (AlgHom.id F E) z) k =
      φ ((Algebra.TensorProduct.basis R b).repr z k) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]
  | tmul a e => simp [Algebra.TensorProduct.basis_repr_tmul]

theorem ae_ext (z z' : AE D) (hi : ∀ w, compInf D.host.F D.host.E w z = compInf D.host.F D.host.E w z')
    (hf : ∀ v, cv D v z = cv D v z') : z = z' := by
  let b := Module.Basis.ofVectorSpace D.host.F D.host.E
  apply (Algebra.TensorProduct.basis (AF D.host.F) b).repr.injective
  refine Finsupp.ext fun k => Prod.ext ?_ ?_
  · funext w
    have h1 := repr_map' (evInf D.host.F w) b z k
    have h2 := repr_map' (evInf D.host.F w) b z' k
    have h : Algebra.TensorProduct.map (evInf D.host.F w) (AlgHom.id D.host.F D.host.E) z =
        Algebra.TensorProduct.map (evInf D.host.F w) (AlgHom.id D.host.F D.host.E) z' := hi w
    rw [h, h2] at h1
    exact h1.symm
  · refine FiniteAdeleRing.ext _ fun v => ?_
    have h1 := repr_map' (evFin D.host.F v) b z k
    have h2 := repr_map' (evFin D.host.F v) b z' k
    have h : Algebra.TensorProduct.map (evFin D.host.F v) (AlgHom.id D.host.F D.host.E) z =
        Algebra.TensorProduct.map (evFin D.host.F v) (AlgHom.id D.host.F D.host.E) z' := hf v
    rw [h, h2] at h1
    exact h1.symm


open Classical in
def indS (S : Finset (Pl D)) : Af D.host.F :=
  ⟨fun v => if v ∈ S then 1 else 0, Filter.Eventually.of_forall fun v => by
    by_cases h : v ∈ S
    · simp only [if_pos h]; exact one_mem (v.adicCompletionIntegers D.host.F)
    · simp only [if_neg h]; exact zero_mem (v.adicCompletionIntegers D.host.F)⟩

def eS (S : Finset (Pl D)) : AE D := ((1, indS S) : AF D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)

theorem isIdem_eS (S : Finset (Pl D)) : IsIdem S (eS S) := by
  classical
  refine ⟨fun w => ?_, fun v => ?_⟩
  · change (evInf D.host.F w (1, indS S)) ⊗ₜ[D.host.F] (1 : D.host.E) = 1
    rw [show evInf D.host.F w (1, indS S) = 1 from rfl]
    rfl
  · change (evFin D.host.F v (1, indS S)) ⊗ₜ[D.host.F] (1 : D.host.E) = _
    rw [show evFin D.host.F v (1, indS S) = if v ∈ S then 1 else 0 from rfl]
    split_ifs
    · rfl
    · exact TensorProduct.zero_tmul _ _

theorem compInf_cA (w : InfinitePlace D.host.F) (z : AE D) :
    compInf D.host.F D.host.E w (cA D z) =
      (Algebra.TensorProduct.map (AlgHom.id D.host.F w.Completion) D.sp.cm.sig).toRingHom (compInf D.host.F D.host.E w z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, RingHom.map_zero]
  | add x y hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), hx, hy, RingHom.map_add (f := _)]
  | tmul a x => rfl

theorem cv_cA (v : Pl D) (z : AE D) :
    cv D v (cA D z) =
      (Algebra.TensorProduct.map (AlgHom.id D.host.F (Fv D.host.F v)) D.sp.cm.sig).toRingHom (cv D v z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, RingHom.map_zero]
  | add x y hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), hx, hy, RingHom.map_add (f := _)]
  | tmul a x => rfl

theorem idem_props (S : Finset (Pl D)) (e : AE D) (he : IsIdem S e) : e * e = e ∧ cA D e = e := by
  classical
  refine ⟨ae_ext _ _ (fun w => ?_) (fun v => ?_), ae_ext _ _ (fun w => ?_) (fun v => ?_)⟩
  · rw [map_mul, he.1 w, one_mul]
  · rw [map_mul, he.2 v]
    split_ifs <;> simp
  · rw [compInf_cA, he.1 w, RingHom.map_one]
  · rw [cv_cA, he.2 v]
    split_ifs <;> simp

end PositivityTheory.Rg.Rsw.L.LIdemEx

namespace PositivityTheory.Rg.Rsw.L

theorem idemEx : IdemEx := fun _ S =>
  ⟨⟨_, LIdemEx.isIdem_eS S⟩, fun e he => LIdemEx.idem_props S e he⟩

end PositivityTheory.Rg.Rsw.L

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

variable {D : D7} {n : ℕ}

theorem mat_proj (v : Pl D) (g : G D n) :
    ((matHom (Fv D.host.F v) D.sp.cm.sig (Jst D n) (GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g) : GL (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) :
      Matrix (Fin (n + n)) (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) = (mat g).map (cv D v) := rfl

theorem mulVec_int (v : Pl D) {m : ℕ} (A : Matrix (Fin m) (Fin m) (Fv D.host.F v ⊗[D.host.F] D.host.E))
    (x : Fin m → Fv D.host.F v ⊗[D.host.F] D.host.E) (hA : ∀ i j, A i j ∈ intLoc D.host.F D.host.E v)
    (hx : ∀ j, x j ∈ intLoc D.host.F D.host.E v) (i : Fin m) : (A *ᵥ x) i ∈ intLoc D.host.F D.host.E v := by
  simp only [Matrix.mulVec, dotProduct]
  exact sum_mem fun j _ => mul_mem (hA i j) (hx j)

theorem single_int (v : Pl D) {m : ℕ} (j : Fin m) (i : Fin m) :
    (Pi.single j (1 : Fv D.host.F v ⊗[D.host.F] D.host.E) : Fin m → _) i ∈ intLoc D.host.F D.host.E v := by
  rw [Pi.single_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem KOff_props {D : D7} {n : ℕ} {S : Finset (Pl D)} {k : G D n} (hk : k ∈ KOff D n S) :
    (mat k).map (infPart D) = 1 ∧ (∀ v ∈ S, (mat k).map (cv D v) = 1) ∧
    ∀ v ∉ S, ∀ i j, cv D v (mat k i j) ∈ intLoc D.host.F D.host.E v := by
  obtain ⟨⟨hfin, haway⟩, hoff⟩ := Subgroup.mem_inf.1 hk
  refine ⟨congrArg Units.val (MonoidHom.mem_ker.1 hfin), fun v hv => ?_, fun v hv i j => ?_⟩
  · have h1 := MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 haway v) hv)
    rw [← mat_proj, h1, map_one, Units.val_one]
  · have h1 := Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hoff v) hv)
    have h2 := Subgroup.mem_comap.1 h1
    have hs : (Pi.single j 1 : Fin (n + n) → Fv D.host.F v ⊗[D.host.F] D.host.E) ∈
        latLoc D.host.F (stdLattice D.host.E (n + n)) v :=
      mem_latLoc_stdLattice.2 (single_int v j)
    have h3 := mem_latLoc_stdLattice.1 ((h2 _).1 hs) i
    rw [mat_proj] at h3
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h3

theorem mem_KOff {D : D7} {n : ℕ} {S : Finset (Pl D)} (g : G D n) (hinf : (mat g).map (infPart D) = 1)
    (hS : ∀ v ∈ S, (mat g).map (cv D v) = 1)
    (hint : ∀ v ∉ S, ∀ i j, cv D v (mat g i j) ∈ intLoc D.host.F D.host.E v ∧
      cv D v (mat g⁻¹ i j) ∈ intLoc D.host.F D.host.E v) :
    g ∈ KOff D n S := by
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨MonoidHom.mem_ker.2 (Units.ext hinf), ?_⟩, ?_⟩
  · refine Subgroup.mem_iInf.2 fun v => Subgroup.mem_iInf.2 fun hv => MonoidHom.mem_ker.2 ?_
    refine matHom_injective _ _ _ (Units.ext ?_)
    rw [mat_proj, hS v hv, map_one, Units.val_one]
  · refine Subgroup.mem_iInf.2 fun v => Subgroup.mem_iInf.2 fun hv => ?_
    refine Subgroup.mem_comap.2 (Subgroup.mem_comap.2 ?_)
    have hM : ∀ i j, ((matHom (Fv D.host.F v) D.sp.cm.sig (Jst D n)
        (GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g) : GL (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) : Matrix (Fin (n + n)) (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) i j ∈ intLoc D.host.F D.host.E v := by
      intro i j; rw [mat_proj]; exact (hint v hv i j).1
    have hM' : ∀ i j, ((matHom (Fv D.host.F v) D.sp.cm.sig (Jst D n)
        (GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g⁻¹) : GL (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) : Matrix (Fin (n + n)) (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) i j ∈ intLoc D.host.F D.host.E v := by
      intro i j; rw [mat_proj]; exact (hint v hv i j).2
    have hinv : ((matHom (Fv D.host.F v) D.sp.cm.sig (Jst D n)
        (GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g⁻¹) : GL (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) : Matrix (Fin (n + n)) (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) *
        ((matHom (Fv D.host.F v) D.sp.cm.sig (Jst D n)
        (GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g) : GL (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) : Matrix (Fin (n + n)) (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) = 1 := by
      rw [← Units.val_mul, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one, Units.val_one]
    intro x
    rw [mem_latLoc_stdLattice, mem_latLoc_stdLattice]
    constructor
    · intro hx i
      exact mulVec_int v _ x hM hx i
    · intro hx i
      have e : x = ((matHom (Fv D.host.F v) D.sp.cm.sig (Jst D n)
          (GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g⁻¹) : GL (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) : Matrix (Fin (n + n)) (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) *ᵥ
          (((matHom (Fv D.host.F v) D.sp.cm.sig (Jst D n)
          (GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g) : GL (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) : Matrix (Fin (n + n)) (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) *ᵥ x) := by
        rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
      rw [e]
      exact mulVec_int v _ _ hM' hx i

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

namespace PositivityTheory.Rg.Rsw.L.LGenK

theorem dyadic_fin (D : D7) : ∃ S₀ : Finset (Pl D), ∀ v : Pl D, (2 : 𝓞 D.host.F) ∈ v.asIdeal → v ∈ S₀ := by
  have h2 : Ideal.span {(2 : 𝓞 D.host.F)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact two_ne_zero
  obtain hfin := Ideal.finite_factors h2
  refine ⟨hfin.toFinset, fun v hv => ?_⟩
  rw [Set.Finite.mem_toFinset]
  exact Ideal.dvd_span_singleton.mpr hv

end PositivityTheory.Rg.Rsw.L.LGenK
end
end

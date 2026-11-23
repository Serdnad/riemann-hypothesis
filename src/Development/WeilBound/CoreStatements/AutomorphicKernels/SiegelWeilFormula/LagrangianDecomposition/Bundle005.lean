module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle003
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle004
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle002
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.UnitaryConjIff
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle021
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest

@[expose] public section

section

namespace PositivityTheory.SiegelWeilFormula.Ald

theorem partCharInv : PartCharInv := PCI.partCharInv_of PCI.finPart

end PositivityTheory.SiegelWeilFormula.Ald
end

section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

set_option linter.unusedSectionVars false

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem trace_mul_single' {m k : ℕ} (A : Matrix (Fin k) (Fin m) (AE F E)) (a : Fin m) (c : Fin k) (z : AE F E) :
    (A * Matrix.single a c z).trace = A c a * z := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and]

theorem map_single' {m k : ℕ} (a : Fin m) (c : Fin k) (z : AE F E) :
    (Matrix.single a c z).map (cA σ) = Matrix.single a c (cA σ z) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.single_apply]
  split_ifs <;> simp

theorem Bf_Ek {m k : ℕ} (bs : Module.Basis (Fin 2) F E) (J : Matrix (Fin m) (Fin m) E) (X : Mx F E m k)
    (q : Fin m × Fin k × Fin 2) : Bf σ J X (Ek bs q) =
      Algebra.trace (AF F) (AE F E) ((∑ p, X p q.2.1 * incM F J p q.1) * cA σ ((1 : AF F) ⊗ₜ[F] bs q.2.2)) := by
  unfold Bf Ek
  rw [map_single', trace_mul_single']
  simp [Matrix.mul_apply, Matrix.transpose_apply]

theorem Bf_col {m k k' : ℕ} (bs : Module.Basis (Fin 2) F E) (J : Matrix (Fin m) (Fin m) E) (X : Mx F E m k)
    (X' : Mx F E m k') (a : Fin m) (c : Fin k) (c' : Fin k') (t : Fin 2) (hX : ∀ p, X p c = X' p c') :
    Bf σ J X (Ek bs (a, c, t)) = Bf σ J X' (Ek bs (a, c', t)) := by
  simp only [Bf_Ek, hX]

theorem Bf_zero_col {m k : ℕ} (bs : Module.Basis (Fin 2) F E) (J : Matrix (Fin m) (Fin m) E) (X : Mx F E m k)
    (a : Fin m) (c : Fin k) (t : Fin 2) (hX : ∀ p, X p c = 0) : Bf σ J X (Ek bs (a, c, t)) = 0 := by
  rw [Bf_Ek]
  simp [hX]

theorem crdB_col {m k k' : ℕ} (bs : Module.Basis (Fin 2) F E) (X : Mx F E m k) (X' : Mx F E m k') (a : Fin m)
    (c : Fin k) (c' : Fin k') (t : Fin 2) (hX : X a c = X' a c') : crdB bs X (a, c, t) = crdB bs X' (a, c', t) := by
  simp only [crdB, hX]

theorem crdB_zero_col {m k : ℕ} (bs : Module.Basis (Fin 2) F E) (X : Mx F E m k) (a : Fin m) (c : Fin k) (t : Fin 2)
    (hX : X a c = 0) : crdB bs X (a, c, t) = 0 := by
  simp [crdB, hX]

theorem extend_zero_embedded_column {m n N : ℕ} (h : n + 1 = N) (X : Mx F E m n) (p : Fin m) (j : Fin n) : ext0 h X p (em0 h j) = X p j := by
  simp [ext0, em0]

theorem extend_zero_last_column {m n N : ℕ} (h : n + 1 = N) (X : Mx F E m n) (p : Fin m) : ext0 h X p (i0 h) = 0 := by
  simp [ext0, i0]

end PositivityTheory.SiegelWeilFormula.Ald

end
end

section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

def SiegelSmall : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (n : ℕ) (h : n + 1 = d.n) (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E)
  (j : G2 σ Y →* d.G) (ε : ℤˣ), 1 ≤ n → SignOK d Y → IsFrame2 σ Y b →
  d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = jeps d.n ε → b.1ᵀ * dbl Y.J * b.1.map σ = jeps n ε → IsJ d h b j →
  ∀ (dd0 : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) d.A.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) d.Y.J))) (Fin d.m × Fin d.n × Fin 2))
    (dd' : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) d.A.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) Y.J))) (Fin d.m × Fin n × Fin 2)),
    IsAdapted d.bs d.A d.Y d.b dd0 → IsAdapted d.bs d.A Y b dd' →
  ∀ (om1 : d.G →* Module.End ℂ ((K1 d.m n → AF F) → ℂ)),
    IsSplitting (adeleClass F) d.B.ψ (GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm) (actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ)) om1 →
    SiegelRule (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) d.B.ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) d.A.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) d.Y.J))
      (GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm) d.χ (diagCols (Fin d.n)) om1 →
  ∀ φ₀ ∈ schA F (Fin d.m × Fin 2), φ₀ 0 = 1 →
  ∀ (om' : G2 σ Y →* Module.End ℂ ((Fin d.m × Fin n × Fin 2 → AF F) → ℂ)),
    (∀ g, ∀ φ' ∈ schA F (Fin d.m × Fin n × Fin 2), om1 (j g) (boxFun φ' φ₀) = boxFun (om' g φ') φ₀) →
    SiegelRule (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) d.B.ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) d.A.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) Y.J)) dd' d.χ (diagCols (Fin n)) om'

def SmallS : Prop := TAll → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (n : ℕ) (h : n + 1 = d.n) (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E)
  (j : G2 σ Y →* d.G) (ε : ℤˣ), 1 ≤ n → SignOK d Y → IsFrame2 σ Y b →
  d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = jeps d.n ε → b.1ᵀ * dbl Y.J * b.1.map σ = jeps n ε → IsJ d h b j →
  ∀ (dd0 : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) d.A.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) d.Y.J))) (Fin d.m × Fin d.n × Fin 2))
    (dd' : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) d.A.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) Y.J))) (Fin d.m × Fin n × Fin 2)),
    IsAdapted d.bs d.A d.Y d.b dd0 → IsAdapted d.bs d.A Y b dd' →
  ∀ (S1 : ((d.κ → AF F) → ℂ) →ₗ[ℂ] ((K1 d.m n → AF F) → ℂ)) (S1' : ((K1 d.m n → AF F) → ℂ) →ₗ[ℂ] ((d.κ → AF F) → ℂ))
    (C : ℂ), C ≠ 0 →
    GlobalTheory.TowU.IsOp d.B.ψ (fun w => (GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm).e (d.dd.e.symm w)) S1 S1' →
    (∀ Φ ∈ d.sch, ∀ X, d.T Φ X = C * S1 Φ (crdB d.bs X ∘ eK d.m h)) →
  ∃ S' : UA σ d.A.J →* Module.End ℂ ((Fin d.m × Fin n × Fin 2 → AF F) → ℂ),
    IsUSplitting (adeleClass F) d.B.ψ dd' (fun (g : UA σ d.A.J) x => mat g * x) S' ∧
    ∀ g, ∀ Φ ∈ schA F (Fin d.m × Fin n × Fin 2), ev0 _ (S' g Φ) = ev0 _ Φ

end PositivityTheory.SiegelWeilFormula.Ald

end
end

section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def cmbE (bs : Module.Basis (Fin 2) F E) (c : Fin 2 → AF F) : AE F E := ∑ t, c t • ((1 : AF F) ⊗ₜ[F] bs t)

theorem cmbE_eq (bs : Module.Basis (Fin 2) F E) (c : Fin 2 → AF F) :
    cmbE bs c = ∑ t, c t • (Algebra.TensorProduct.basis (AF F) bs) t := by
  simp [cmbE, Algebra.TensorProduct.basis_apply]

theorem repr_cmbE_apply (bs : Module.Basis (Fin 2) F E) (c : Fin 2 → AF F) (t : Fin 2) :
    (Algebra.TensorProduct.basis (AF F) bs).repr (cmbE bs c) t = c t := by
  rw [cmbE_eq, Module.Basis.repr_sum_self]

theorem cmbE_repr (bs : Module.Basis (Fin 2) F E) (z : AE F E) :
    cmbE bs (fun t => (Algebra.TensorProduct.basis (AF F) bs).repr z t) = z := by
  rw [cmbE_eq]
  exact (Algebra.TensorProduct.basis (AF F) bs).sum_repr z

def cmbB {m n : ℕ} (bs : Module.Basis (Fin 2) F E) (y : Fin m × Fin n × Fin 2 → AF F) : Mx F E m n :=
  fun a i => cmbE bs fun t => y (a, i, t)

theorem crdB_cmbB {m n : ℕ} (bs : Module.Basis (Fin 2) F E) (y : Fin m × Fin n × Fin 2 → AF F) :
    crdB bs (cmbB bs y) = y := by
  funext k
  simp only [crdB, cmbB, repr_cmbE_apply]

theorem cmbB_crdB {m n : ℕ} (bs : Module.Basis (Fin 2) F E) (X : Mx F E m n) : cmbB bs (crdB bs X) = X := by
  funext a i
  simp only [cmbB, crdB, cmbE_repr]

def Lk {m n : ℕ} (bs : Module.Basis (Fin 2) F E) (M : Matrix (Fin m) (Fin m) (AE F E)) (y : Fin m × Fin n × Fin 2 → AF F) :
    Fin m × Fin n × Fin 2 → AF F := crdB bs (M * cmbB bs y)

theorem Lk_crdB {m n : ℕ} (bs : Module.Basis (Fin 2) F E) (M : Matrix (Fin m) (Fin m) (AE F E)) (X : Mx F E m n) :
    Lk bs M (crdB bs X) = crdB bs (M * X) := by rw [Lk, cmbB_crdB]

theorem Lk_one {m n : ℕ} (bs : Module.Basis (Fin 2) F E) (y : Fin m × Fin n × Fin 2 → AF F) : Lk bs 1 y = y := by
  rw [Lk, Matrix.one_mul, crdB_cmbB]

theorem Lk_mul {m n : ℕ} (bs : Module.Basis (Fin 2) F E) (M M' : Matrix (Fin m) (Fin m) (AE F E))
    (y : Fin m × Fin n × Fin 2 → AF F) : Lk bs (M * M') y = Lk bs M (Lk bs M' y) := by
  rw [Lk, Lk, Lk, cmbB_crdB, Matrix.mul_assoc]

theorem Lk_zero {m n : ℕ} (bs : Module.Basis (Fin 2) F E) (M : Matrix (Fin m) (Fin m) (AE F E)) :
    Lk (n := n) bs M 0 = 0 := by
  have : cmbB (m := m) (n := n) bs 0 = 0 := by
    funext a i; simp [cmbB, cmbE]
  funext k
  simp [Lk, this, crdB]

def Lc {m : ℕ} (bs : Module.Basis (Fin 2) F E) (M : Matrix (Fin m) (Fin m) (AE F E)) (v : Fin m × Fin 2 → AF F) :
    Fin m × Fin 2 → AF F :=
  fun p => (Algebra.TensorProduct.basis (AF F) bs).repr ((M *ᵥ fun a => cmbE bs fun t => v (a, t)) p.1) p.2

theorem Lc_zero {m : ℕ} (bs : Module.Basis (Fin 2) F E) (M : Matrix (Fin m) (Fin m) (AE F E)) : Lc bs M 0 = 0 := by
  funext p
  have hz : (fun _ : Fin m => (0 : AE F E)) = 0 := rfl
  simp [Lc, cmbE, hz, Matrix.mulVec_zero]

theorem triple_index_symm_embedded {m n N : ℕ} (h : n + 1 = N) (a : Fin m) (j : Fin n) (t : Fin 2) :
    (eK m h).symm (a, em0 h j, t) = Sum.inl (a, j, t) := by
  rw [Equiv.symm_apply_eq]; rfl

theorem triple_index_symm_last {m n N : ℕ} (h : n + 1 = N) (a : Fin m) (t : Fin 2) :
    (eK m h).symm (a, i0 h, t) = Sum.inr (a, t) := by
  rw [Equiv.symm_apply_eq]; rfl

theorem Lk_eK {m n N : ℕ} (h : n + 1 = N) (bs : Module.Basis (Fin 2) F E) (M : Matrix (Fin m) (Fin m) (AE F E))
    (x : K1 m n → AF F) :
    Lk bs M (x ∘ (eK m h).symm) ∘ eK m h = Sum.elim (Lk bs M (x ∘ Sum.inl)) (Lc bs M (x ∘ Sum.inr)) := by
  funext k
  rcases k with ⟨a, j, t⟩ | ⟨a, t⟩
  · have hk : eK m h (Sum.inl (a, j, t)) = (a, em0 h j, t) := rfl
    simp only [Function.comp_apply, hk, Sum.elim_inl, Lk, crdB, cmbB, Matrix.mul_apply, triple_index_symm_embedded]
  · have hk : eK m h (Sum.inr (a, t)) = (a, i0 h, t) := rfl
    simp only [Function.comp_apply, hk, Sum.elim_inr, Lk, Lc, crdB, cmbB, Matrix.mul_apply, Matrix.mulVec,
      dotProduct, triple_index_symm_last]

end PositivityTheory.SiegelWeilFormula.Ald

end
end

section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

set_option linter.unusedSectionVars false

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem frQ_mul_frame {m k : ℕ} (c : GL (Fin k ⊕ Fin k) E) (w : Matrix (Fin m) (Fin k ⊕ Fin k) (AE F E)) :
    frQ c w * (incM F c.1)ᵀ = w := by
  change (w * (incM F (c⁻¹).1)ᵀ) * (incM F c.1)ᵀ = w
  rw [Matrix.mul_assoc, ← Matrix.transpose_mul, incM_mul_inv, Matrix.transpose_one, Matrix.mul_one]

theorem frQ_of {m k : ℕ} (c : GL (Fin k ⊕ Fin k) E) (Q : Matrix (Fin m) (Fin k ⊕ Fin k) (AE F E)) :
    frQ c (Q * (incM F c.1)ᵀ) = Q := by
  change (Q * (incM F c.1)ᵀ) * (incM F (c⁻¹).1)ᵀ = Q
  rw [Matrix.mul_assoc, ← Matrix.transpose_mul, incM_inv_mul, Matrix.transpose_one, Matrix.mul_one]

theorem frQ_injective {m k : ℕ} (c : GL (Fin k ⊕ Fin k) E) {w w' : Matrix (Fin m) (Fin k ⊕ Fin k) (AE F E)}
    (e : frQ c w = frQ c w') : w = w' := by
  rw [← frQ_mul_frame c w, ← frQ_mul_frame c w', e]

theorem split_frame {m k : ℕ} (c : GL (Fin k ⊕ Fin k) E) (Q : Matrix (Fin m) (Fin k ⊕ Fin k) (AE F E)) :
    Q * (incM F c.1)ᵀ = Q.toCols₁ * (incM F c.1.toCols₁)ᵀ + Q.toCols₂ * (incM F c.1.toCols₂)ᵀ := by
  have e1 : incM F c.1 = Matrix.fromCols (incM F c.1.toCols₁) (incM F c.1.toCols₂) := by
    ext i j
    rcases j with j | j <;> rfl
  conv_lhs => rw [← Matrix.fromCols_toCols Q, e1, Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows]

theorem adapted_e {m k : ℕ} {bs : Module.Basis (Fin 2) F E} {A : Spc F E m} {Y : Spc F E k} {c : GL (Fin k ⊕ Fin k) E}
    {dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J))) (Fin m × Fin k × Fin 2)}
    (hd : IsAdapted bs A Y c dd) (w : Matrix (Fin m) (Fin k ⊕ Fin k) (AE F E)) :
    dd.e w = (crdB bs (frQ c w).toCols₂, fun k => Bf σ A.J (frQ c w).toCols₁ (Ek bs k)) := by
  conv_lhs => rw [← frQ_mul_frame c w, split_frame]
  exact hd _ _

def embQ {R : Type*} [Zero R] {m n N : ℕ} (h : n + 1 = N) (Q : Matrix (Fin m) (Fin n ⊕ Fin n) R) :
    Matrix (Fin m) (Fin N ⊕ Fin N) R :=
  (Matrix.fromCols Q (0 : Matrix (Fin m) (Fin 1 ⊕ Fin 1) R)).submatrix id (eB h)

theorem embQ_toCols₁ {m n N : ℕ} (h : n + 1 = N) (Q : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)) :
    (embQ h Q).toCols₁ = ext0 h Q.toCols₁ := by
  ext a i
  rcases idx_cases h (Sum.inl i) with ⟨u, hu⟩ | hu | hu
  · rcases u with u | u
    · simp only [Sum.map_inl, Sum.inl.injEq] at hu
      subst hu
      simp only [Matrix.toCols₁, Matrix.of_apply, embQ, Matrix.submatrix_apply, id_eq]
      rw [show (Sum.inl (em0 h u) : Fin N ⊕ Fin N) = Sum.map (em0 h) (em0 h) (Sum.inl u) from rfl, eB_map]
      simp [ext0, em0]
    · simp at hu
  · simp only [Sum.inl.injEq] at hu
    subst hu
    simp only [Matrix.toCols₁, Matrix.of_apply, embQ, Matrix.submatrix_apply, id_eq, block_index_inl_last]
    simp [ext0, i0]
  · simp at hu

theorem embQ_toCols₂ {m n N : ℕ} (h : n + 1 = N) (Q : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)) :
    (embQ h Q).toCols₂ = ext0 h Q.toCols₂ := by
  ext a i
  rcases idx_cases h (Sum.inr i) with ⟨u, hu⟩ | hu | hu
  · rcases u with u | u
    · simp at hu
    · simp only [Sum.map_inr, Sum.inr.injEq] at hu
      subst hu
      simp only [Matrix.toCols₂, Matrix.of_apply, embQ, Matrix.submatrix_apply, id_eq]
      rw [show (Sum.inr (em0 h u) : Fin N ⊕ Fin N) = Sum.map (em0 h) (em0 h) (Sum.inr u) from rfl, eB_map]
      simp [ext0, em0]
  · simp at hu
  · simp only [Sum.inr.injEq] at hu
    subst hu
    simp only [Matrix.toCols₂, Matrix.of_apply, embQ, Matrix.submatrix_apply, id_eq, block_index_inr_last]
    simp [ext0, i0]

theorem emb_eq {m n N : ℕ} (h : n + 1 = N) (b : GL (Fin n ⊕ Fin n) E) (bd : GL (Fin N ⊕ Fin N) E)
    (w : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)) : emb h b bd w = embQ h (frQ b w) * (incM F bd.1)ᵀ := by
  rw [split_frame, embQ_toCols₁, embQ_toCols₂, emb]
  rfl

theorem frQ_emb {m n N : ℕ} (h : n + 1 = N) (b : GL (Fin n ⊕ Fin n) E) (bd : GL (Fin N ⊕ Fin N) E)
    (w : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)) : frQ bd (emb h b bd w) = embQ h (frQ b w) := by
  rw [emb_eq, frQ_of]

theorem embQ_mul_blk {m n N : ℕ} (h : n + 1 = N) (Q : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E))
    (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) : embQ h Q * (blk h M 1)ᵀ = embQ h (Q * Mᵀ) := by
  rw [blk_transpose]
  simp only [embQ, blk]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromBlocks]
  simp

theorem frQ_mul_mat {m k : ℕ} {Y : Spc F E k} (c : GL (Fin k ⊕ Fin k) E) (x : G2 σ Y)
    (w : Matrix (Fin m) (Fin k ⊕ Fin k) (AE F E)) : frQ c (w * (x.1.1)ᵀ) = frQ c w * (inFrame c x)ᵀ := by
  have e : x.1.1 = incM F c.1 * inFrame c x * incM F (c⁻¹).1 := by
    rw [inFrame_eq, ← Matrix.mul_assoc, ← Matrix.mul_assoc, incM_mul_inv, Matrix.one_mul, Matrix.mul_assoc,
      incM_mul_inv, Matrix.mul_one]
  rw [frQ, frQ, e]
  simp only [Matrix.transpose_mul, ← Matrix.mul_assoc]
  change w * (incM F (c⁻¹).1)ᵀ * (inFrame c x)ᵀ * (incM F c.1)ᵀ * (incM F (c⁻¹).1)ᵀ =
    w * (incM F (c⁻¹).1)ᵀ * (inFrame c x)ᵀ
  rw [Matrix.mul_assoc _ (incM F c.1)ᵀ, ← Matrix.transpose_mul, incM_inv_mul, Matrix.transpose_one, Matrix.mul_one]

end PositivityTheory.SiegelWeilFormula.Ald

end
end

section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

set_option linter.unusedSectionVars false

namespace PositivityTheory.SiegelWeilFormula.Ald

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem incM_mul {ι κ ν : Type} [Fintype κ] (M : Matrix ι κ E) (N : Matrix κ ν E) :
    incM F (M * N) = incM F M * incM F N := by
  simp only [incM]
  exact Matrix.map_mul (f := (inclR (F := F) (E := E) (AF F)))

theorem incM_diagCols (n : ℕ) :
    incM F (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) E) = (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) := by
  ext u k
  rcases u with u | u <;> simp [incM, diagCols, Matrix.one_apply, apply_ite] <;> split_ifs <;> simp_all

theorem mul_fromRows_one_zero {R : Type*} [CommRing R] {n : ℕ} (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) :
    M * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) R) (0 : Matrix (Fin n) (Fin n) R) = M.toCols₁ := by
  ext u k
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Matrix.toCols₁]

theorem frame_fromRows {n : ℕ} {Y : Spc F E n} {b : GL (Fin n ⊕ Fin n) E} (hb : IsFrame2 σ Y b) :
    ∃ tb : GL (Fin n) E, incM F b.1 * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (0 : Matrix (Fin n) (Fin n) (AE F E)) =
      (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * incM F tb.1 := by
  obtain ⟨-, tb, htb0⟩ := hb
  have htb : b.1.toCols₁ = (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) E) * tb.1 := htb0
  refine ⟨tb, ?_⟩
  have e : (incM F b.1).toCols₁ = incM F b.1.toCols₁ := rfl
  rw [mul_fromRows_one_zero, e, htb, incM_mul]
  congr 1
  ext u k
  rcases u with u | u <;> simp [incM, diagCols, Matrix.one_apply, apply_ite] <;> split_ifs <;> simp_all

theorem frame_decomp {m n : ℕ} (b : GL (Fin n ⊕ Fin n) E) (w : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)) :
    w = (frQ b w).toCols₁ * (incM F b.1.toCols₁)ᵀ + (frQ b w).toCols₂ * (incM F b.1.toCols₂)ᵀ := by
  have e1 : frQ b w * (incM F b.1)ᵀ = w := by
    change (w * (incM F (b⁻¹).1)ᵀ) * (incM F b.1)ᵀ = w
    rw [Matrix.mul_assoc, ← Matrix.transpose_mul, incM_mul_inv, Matrix.transpose_one, Matrix.mul_one]
  have e2 : incM F b.1 = Matrix.fromCols (incM F b.1.toCols₁) (incM F b.1.toCols₂) := by
    ext u v
    rcases v with v | v <;> rfl
  conv_lhs => rw [← e1, e2, Matrix.transpose_fromCols, ← Matrix.fromCols_toCols (frQ b w), Matrix.fromCols_mul_fromRows]

end PositivityTheory.SiegelWeilFormula.Ald

end
end

section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald.YFA

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem sig_sig' (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  exact τ.injective (by rw [h.2.2.2, h.2.2.2, star_star])


variable (F) in
def spcOf {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Spc F E n := ⟨J, ⊤, fun _ => 1, fun _ => 1⟩

theorem toCols₁_wit {n : ℕ} (T : GL (Fin n) E) (a : E) :
    ∃ t : GL (Fin n) E, (GlobalTheory.ThK.Dbl.Frame.two 1 * GlobalTheory.ThK.Dbl.Frame.wit a T).1.toCols₁ = diagCols (Fin n) * t.1 := by
  have hd := GlobalTheory.ThK.Dbl.Frame.frame_diag (1 : GL (Fin n) E) T a
  refine ⟨1, ?_⟩
  ext i j
  have := congrFun (congrFun hd i) j
  rw [Matrix.mul_apply, Fintype.sum_sum_type] at this
  simp only [Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.zero_apply, mul_zero,
    Finset.sum_const_zero, add_zero, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true] at this
  simpa [Matrix.toCols₁] using this

omit [NumberField F] [NumberField E] in
theorem dbl_sym {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {e₀ : E} (hJ : ∀ i j, σ (J j i) = e₀ * J i j) :
    ((dbl J).map (σ : E →+* E))ᵀ = e₀ • dbl J := by
  ext (i | i) (j | j) <;> simp [dbl, Matrix.fromBlocks, hJ]

theorem eps_eq {n : ℕ} (hn : 1 ≤ n) (hc : ∀ z : E, σ (σ z) = z) {J : Matrix (Fin n) (Fin n) E} {e₀ : E}
    (hJ : ∀ i j, σ (J j i) = e₀ * J i j) {b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E} {e : E}
    (hb : bᵀ * dbl J * b.map σ = Matrix.fromBlocks 0 1 (e • 1) 0) (he : σ e = e) : e = e₀ := by
  have h := GlobalTheory.ThK.Dbl.Frame.gram_sym (σ : E →+* E) hc (dbl_sym hJ) b
  have hb' : bᵀ * dbl J * b.map (σ : E →+* E) = Matrix.fromBlocks 0 1 (e • 1) 0 := hb
  rw [hb'] at h
  have := congrFun (congrFun h (Sum.inl ⟨0, hn⟩)) (Sum.inr ⟨0, hn⟩)
  simpa [Matrix.fromBlocks, he] using this

end PositivityTheory.SiegelWeilFormula.Ald.YFA

end
end

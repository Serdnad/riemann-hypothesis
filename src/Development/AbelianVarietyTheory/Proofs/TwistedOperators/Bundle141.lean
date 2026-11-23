module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle015
public import Mathlib.Data.Matrix.ColumnRowPartitioned
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle137
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistDual

variable {D : D7}

theorem adj_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) : adj D A = Aᴴ := by
  funext i j
  rfl

theorem hT_coord (V : HSp D) (x y : V.V) :
    V.hT x y = ∑ i, ∑ j, star (V.frame.repr x i) * V.gram i j * V.frame.repr y j := by
  conv_lhs => rw [← V.frame.sum_repr x, ← V.frame.sum_repr y]

  simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, HSpace.gram]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [RingHom.id_apply, starRingEnd_apply, mul_comm]

theorem gram_det_ne (V : HSp D) : V.gram.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hv
  have : V.frame.equivFun.symm v = 0 := by
    apply V.nondeg.2
    intro x
    rw [hT_coord]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h1 : ∑ j, V.gram i j * v j = 0 := congr_fun h0 i
    have h2 : ∀ j, V.frame.repr (V.frame.equivFun.symm v) j = v j := fun j =>
      congr_fun (V.frame.equivFun.apply_symm_apply v) j
    simp only [h2, mul_assoc, ← Finset.mul_sum, h1, mul_zero]
  exact V.frame.equivFun.symm.map_eq_zero_iff.1 this

theorem gram_ct (V : HSp D) : V.gramᴴ = V.gram := by
  funext i j
  exact V.herm.eq (V.frame j) (V.frame i)

theorem exists_isotropic_dual : ∀ (D : D7) (V V' : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B →
    ∃ C' : Matrix (Fin V.rank) (Fin r) D.host.E,
      adj D C * V.gram * C' = 1 ∧ adj D C' * V.gram * C' = 0 ∧ adj D C' * V.gram * B = 0 := by
  intro D V V' r C B hs
  simp only [adj_eq]
  have hCC : Cᴴ * V.gram * C = 0 := by rw [← adj_eq]; exact hs.frame.2.2
  have hBB : (Bᴴ * V.gram * B).det ≠ 0 := by rw [← adj_eq, hs.isom]; exact gram_det_ne V'
  have hCB : Cᴴ * V.gram * B = 0 := by rw [← adj_eq]; exact hs.orth
  exact exists_dual (gram_ct V) (gram_det_ne V) hs.frame.2.1 hCC hBB hCB

end GlobalTheory.TwistDual
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LeviScale

section Alg

variable {E : Type} [Field E] [CharZero E] (σ : E →+* E)

theorem cT_fromCols {ι α β : Type} (X : Matrix ι α E) (Y : Matrix ι β E) :
    Formalism.UG.cT σ (fromCols X Y) = fromRows (Formalism.UG.cT σ X) (Formalism.UG.cT σ Y) := by
  ext (i | i) j <;> rfl

theorem cT_diagonal {ι : Type} [DecidableEq ι] (d : ι → E) (hd : ∀ i, σ (d i) = d i) :
    Formalism.UG.cT σ (diagonal d) = diagonal d := by
  ext i j
  by_cases h : i = j
  · subst h; simp [Formalism.UG.cT, hd]
  · simp [Formalism.UG.cT, diagonal_apply_ne _ h, diagonal_apply_ne _ (Ne.symm h)]

theorem levi_alg (hσ : ∀ x, σ (σ x) = x) {n m r : ℕ} (hn : n = m + 2 * r)
    (G : Matrix (Fin n) (Fin n) E) (G' Gi : Matrix (Fin m) (Fin m) E) (hGi : Gi * G' = 1)
    (hG : Formalism.UG.cT σ G = G)
    (C C' : Matrix (Fin n) (Fin r) E) (B : Matrix (Fin n) (Fin m) E)
    (h11 : Formalism.UG.cT σ C * G * C = 0) (h12 : Formalism.UG.cT σ C * G * B = 0)
    (h22 : Formalism.UG.cT σ B * G * B = G')
    (h13 : Formalism.UG.cT σ C * G * C' = 1) (h33 : Formalism.UG.cT σ C' * G * C' = 0)
    (h32 : Formalism.UG.cT σ C' * G * B = 0) :
    ∃ A A' : Matrix (Fin n) (Fin n) E, A * A' = 1 ∧ A' * A = 1 ∧ Formalism.UG.cT σ A * G * A = G ∧
      A * C = (2 : E) • C ∧ A * B = B ∧ (2 : E) • (A * C') = C' := by
  have hcc : ∀ {a : ℕ} (X : Matrix (Fin n) (Fin a) E), Formalism.UG.cT σ (Formalism.UG.cT σ X) = X := by
    intro a X; ext i j; simp [Formalism.UG.cT, hσ]
  have swap : ∀ {a b : ℕ} (X : Matrix (Fin n) (Fin a) E) (Y : Matrix (Fin n) (Fin b) E),
      Formalism.UG.cT σ (Formalism.UG.cT σ X * G * Y) = Formalism.UG.cT σ Y * G * X := by
    intro a b X Y
    rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul, hG, hcc, Matrix.mul_assoc]
  have cT0 : ∀ {a b : ℕ}, Formalism.UG.cT σ (0 : Matrix (Fin a) (Fin b) E) = 0 := by
    intro a b; ext i j; simp [Formalism.UG.cT]
  have h21 : Formalism.UG.cT σ B * G * C = 0 := by rw [← swap C B, h12, cT0]
  have h23 : Formalism.UG.cT σ B * G * C' = 0 := by rw [← swap C' B, h32, cT0]
  have h31 : Formalism.UG.cT σ C' * G * C = 1 := by rw [← swap C C', h13, Formalism.UG.cT_one]
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin n) (Fin r ⊕ (Fin m ⊕ Fin r)) E, P = fromCols C (fromCols B C') := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin r ⊕ (Fin m ⊕ Fin r)) (Fin n) E,
      Q = fromRows (Formalism.UG.cT σ C' * G) (fromRows (Gi * Formalism.UG.cT σ B * G) (Formalism.UG.cT σ C * G)) := ⟨_, rfl⟩
  have as3 : ∀ {a : ℕ} (X : Matrix (Fin n) (Fin a) E), Gi * Formalism.UG.cT σ B * G * X = Gi * (Formalism.UG.cT σ B * G * X) := by
    intro a X; simp only [Matrix.mul_assoc]
  have hQC : Q * C = fromRows 1 (fromRows 0 0) := by
    rw [hQ, fromRows_mul, fromRows_mul, h31, h11, as3, h21, Matrix.mul_zero]
  have hQB : Q * B = fromRows 0 (fromRows 1 0) := by
    rw [hQ, fromRows_mul, fromRows_mul, h32, h12, as3, h22, hGi]
  have hQC' : Q * C' = fromRows 0 (fromRows 0 1) := by
    rw [hQ, fromRows_mul, fromRows_mul, h33, h13, as3, h23, Matrix.mul_zero]
  have hQP : Q * P = 1 := by
    rw [hP, mul_fromCols, mul_fromCols, hQC, hQB, hQC']
    ext (i | i | i) (j | j | j) <;> simp [Matrix.one_apply]
  have hPQ : P * Q = 1 := by
    have e : (Fin r ⊕ (Fin m ⊕ Fin r)) ≃ Fin n := Fintype.equivOfCardEq (by simp; omega)
    exact (Matrix.mul_eq_one_comm_of_equiv e).1 hQP
  obtain ⟨d, hd⟩ : ∃ d : Fin r ⊕ (Fin m ⊕ Fin r) → E,
      d = Sum.elim (fun _ => 2) (Sum.elim (fun _ => 1) (fun _ => 2⁻¹)) := ⟨_, rfl⟩
  obtain ⟨d', hd'⟩ : ∃ d' : Fin r ⊕ (Fin m ⊕ Fin r) → E,
      d' = Sum.elim (fun _ => 2⁻¹) (Sum.elim (fun _ => 1) (fun _ => 2)) := ⟨_, rfl⟩
  have h2 : (2 : E) ≠ 0 := two_ne_zero
  have hdd : (fun i => d i * d' i) = fun _ => 1 := by
    funext i; rcases i with i | i | i <;> simp [hd, hd', h2]
  have hdd' : (fun i => d' i * d i) = fun _ => 1 := by
    funext i; rcases i with i | i | i <;> simp [hd, hd', h2]
  have hσd : ∀ i, σ (d i) = d i := by
    intro i; rcases i with i | i | i <;> simp [hd, map_inv₀, map_ofNat]
  have hK : Formalism.UG.cT σ P * G * P = fromCols (fromRows 0 (fromRows 0 1))
      (fromCols (fromRows 0 (fromRows G' 0)) (fromRows 1 (fromRows 0 0))) := by
    rw [hP, cT_fromCols, cT_fromCols]
    simp only [fromRows_mul, mul_fromCols]
    rw [h11, h12, h13, h21, h22, h23, h31, h32, h33]
  have hDKD : diagonal d * (Formalism.UG.cT σ P * G * P) * diagonal d = Formalism.UG.cT σ P * G * P := by
    rw [hK]
    ext (i | i | i) (j | j | j) <;> simp [diagonal_mul, mul_diagonal, hd] <;> ring
  refine ⟨P * diagonal d * Q, P * diagonal d' * Q, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc P * diagonal d * Q * (P * diagonal d' * Q) = P * (diagonal d * (Q * P) * diagonal d') * Q := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hQP, Matrix.mul_one, diagonal_mul_diagonal, hdd, diagonal_one, Matrix.mul_one, hPQ]
  · calc P * diagonal d' * Q * (P * diagonal d * Q) = P * (diagonal d' * (Q * P) * diagonal d) * Q := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hQP, Matrix.mul_one, diagonal_mul_diagonal, hdd', diagonal_one, Matrix.mul_one, hPQ]
  · have hA : Formalism.UG.cT σ (P * diagonal d * Q) = Formalism.UG.cT σ Q * diagonal d * Formalism.UG.cT σ P := by
      rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul, cT_diagonal σ d hσd, Matrix.mul_assoc]
    calc Formalism.UG.cT σ (P * diagonal d * Q) * G * (P * diagonal d * Q)
        = Formalism.UG.cT σ Q * (diagonal d * (Formalism.UG.cT σ P * G * P) * diagonal d) * Q := by
          rw [hA]; simp only [Matrix.mul_assoc]
      _ = Formalism.UG.cT σ (P * Q) * G * (P * Q) := by
          rw [hDKD, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = G := by rw [hPQ, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
  · have h : diagonal d * (Q * C) = (2 : E) • (Q * C) := by
      rw [hQC]; ext (i | i | i) j <;> simp [diagonal_mul, hd]
    calc P * diagonal d * Q * C = P * (diagonal d * (Q * C)) := by simp only [Matrix.mul_assoc]
      _ = (2 : E) • (P * Q * C) := by rw [h, Matrix.mul_smul, Matrix.mul_assoc]
      _ = (2 : E) • C := by rw [hPQ, Matrix.one_mul]
  · have h : diagonal d * (Q * B) = Q * B := by
      rw [hQB]; ext (i | i | i) j <;> simp [diagonal_mul, hd]
    calc P * diagonal d * Q * B = P * (diagonal d * (Q * B)) := by simp only [Matrix.mul_assoc]
      _ = P * Q * B := by rw [h, Matrix.mul_assoc]
      _ = B := by rw [hPQ, Matrix.one_mul]
  · have h : diagonal d * (Q * C') = (2 : E)⁻¹ • (Q * C') := by
      rw [hQC']; ext (i | i | i) j <;> simp [diagonal_mul, hd]
    calc (2 : E) • (P * diagonal d * Q * C') = (2 : E) • (P * (diagonal d * (Q * C'))) := by
          simp only [Matrix.mul_assoc]
      _ = ((2 : E) * (2 : E)⁻¹) • (P * Q * C') := by rw [h, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
      _ = C' := by rw [hPQ, Matrix.one_mul, mul_inv_cancel₀ h2, one_smul]

end Alg

theorem exists_levi_scale : ∀ (D : D7) (V V' : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∃ a : GA D V, a ∈ GQ V ∧ HMul.hMul (matHom V a).1 (C.map (incA D)) = (2 : AE D) • C.map (incA D) ∧ HMul.hMul (matHom V a).1 (B.map (incA D)) = B.map (incA D) ∧ (2 : AE D) • HMul.hMul (matHom V a).1 (C'.map (incA D)) = C'.map (incA D) := by
  intro D V V' r C C' B hs h1 h2 h3
  obtain ⟨A, A', hAA', hA'A, hU, hC, hB, hC'⟩ :=
    levi_alg (D.sp.cm.sig : D.host.E →+* D.host.E) (fun x => star_star x) hs.rank V.gram V'.gram V'.gram⁻¹
      (Matrix.nonsing_inv_mul _ (GlobalTheory.AutFunCounterexample.gram_det_ne V').isUnit) (GlobalTheory.AutFunCounterexample.gram_herm V)
      C C' B hs.frame.2.2 hs.orth hs.isom h1 h2 h3
  let g : GL (Fin V.rank) D.host.E := ⟨A, A', hAA', hA'A⟩
  have hg : g ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram := hU
  have hmem : Formalism.UG.bc (incA D) g ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
    show Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (A.map (incA D)) * V.gram.map (incA D) * A.map (incA D) =
      V.gram.map (incA D)
    rw [GlobalTheory.AutFunCounterexample.cT_map_gen, ← Matrix.map_mul, ← Matrix.map_mul, hU]
  have hsm : ∀ {k : ℕ} (X : Matrix (Fin V.rank) (Fin k) D.host.E),
      ((2 : D.host.E) • X).map (incA D) = (2 : AE D) • X.map (incA D) := by
    intro k X; ext i j; simp [Matrix.map_apply, Matrix.smul_apply, map_ofNat]
  refine ⟨⟨Formalism.UG.bc (incA D) g, hmem⟩, ?_, ?_, ?_, ?_⟩
  · show (⟨Formalism.UG.bc (incA D) g, hmem⟩ : HR (AF D.host.F) D.sp.cm.sig V.gram) ∈
      (HFin (AF D.host.F) D.sp.cm.sig V.gram).subgroupOf (HR (AF D.host.F) D.sp.cm.sig V.gram)
    rw [Subgroup.mem_subgroupOf]
    exact ⟨g, hg, rfl⟩
  · change HMul.hMul (A.map (incA D)) (C.map (incA D)) = _
    rw [← Matrix.map_mul, hC, hsm]
  · change HMul.hMul (A.map (incA D)) (B.map (incA D)) = _
    rw [← Matrix.map_mul, hB]
  · change (2 : AE D) • HMul.hMul (A.map (incA D)) (C'.map (incA D)) = _
    rw [← Matrix.map_mul, ← hsm, hC']

end GlobalTheory.LeviScale
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatticeLocal

section
variable (F : Type) [Field F] [NumberField F]

theorem ev_self (v : HeightOneSpectrum (𝓞 F)) : evalV F v (singleV F v 1) = 1 := by
  classical
  show (singleV F v 1 : Af F) v = 1
  unfold singleV
  exact RestrictedProduct.single_eq_same _ v 1

theorem ev_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) : evalV F w (singleV F v 1) = 0 := by
  classical
  show (singleV F v 1 : Af F) w = 0
  unfold singleV
  exact RestrictedProduct.single_eq_of_ne _ 1 h

theorem af_ext {α β : Af F} (h : ∀ w, evalV F w α = evalV F w β) : α = β := by
  apply RestrictedProduct.ext
  intro w
  exact h w

end

variable {D : D7}

theorem idem_inl_mul (v : FinPl D) (α : Af D.host.F) (m : D.host.E) :
    idem D (.inl v) * (pairA D.host.F 0 α ⊗ₜ[D.host.F] m) =
      pairA D.host.F 0 (singleV D.host.F v 1 * α) ⊗ₜ[D.host.F] m := by
  have key : pairA D.host.F 0 (singleV D.host.F v 1) * pairA D.host.F 0 α =
      pairA D.host.F 0 (singleV D.host.F v 1 * α) := Prod.ext (mul_zero _) rfl
  simp only [idem, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, key]

theorem idem_inr_mul (τ : D.what₂.Tau) (α : Af D.host.F) (m : D.host.E) :
    idem D (.inr τ) * (pairA D.host.F 0 α ⊗ₜ[D.host.F] m) = 0 := by
  have key : pairA D.host.F (GlobalTheory.AutFunCompare.sgW (plTau D τ) 1) 0 * pairA D.host.F 0 α = 0 :=
    Prod.ext (mul_zero _) (zero_mul _)
  simp only [idem, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    Algebra.TensorProduct.tmul_mul_tmul, key, TensorProduct.zero_tmul]

theorem wAt_add {m n : ℕ} (p : Place D) (x y : Mx D m n) : wAt p (x + y) = wAt p x + wAt p y := by
  ext i j
  simp [wAt, mul_add]

theorem wAt_neg {m n : ℕ} (p : Place D) (x : Mx D m n) : wAt p (-x) = -wAt p x := by
  ext i j
  simp [wAt]

theorem wAt_zero {m n : ℕ} (p : Place D) : wAt p (0 : Mx D m n) = 0 := by
  ext i j
  simp [wAt]

theorem wAt_mem_latO : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (P : FinPl D → Prop) (u : WO S T), u ∈ latO S T ΛS ΛT P → ∀ p : Place D, wAt p u ∈ (latO S T ΛS ΛT fun v => P v ∧ Sum.inl v = p) ∧ u - wAt p u ∈ (latO S T ΛS ΛT fun v => P v ∧ Sum.inl v ≠ p) ∧ ((∀ v, P v → Sum.inl v ≠ p) → wAt p u = 0) := by
  intro D S T ΛS ΛT P u hu p
  unfold latO at hu
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, hv, a, ha, s, hs, t, ht, hw⟩ := hw

    obtain ⟨X, hX⟩ : ∃ X : Fin T.rank → Fin S.rank → D.host.E,
        X = fun i j => a * t i * ∑ k, star (s k) * S.gram k j := ⟨_, rfl⟩

    have gen : ∀ (Q : FinPl D → Prop) (β : Af D.host.F), β ∈ intAf D.host.F →
        (∀ v, ¬ Q v → evalV D.host.F v β = 0) →
        (Matrix.of fun i j => pairA D.host.F 0 β ⊗ₜ[D.host.F] X i j) ∈ latO S T ΛS ΛT Q := by
      intro Q β hβ hQ
      unfold latO
      refine AddSubgroup.subset_closure ?_
      simp only [Set.mem_setOf_eq]
      exact ⟨β, hβ, hQ, a, ha, s, hs, t, ht, by subst hX; rfl⟩
    have hw' : w = Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] X i j := by
      subst hX
      exact hw
    subst hw'
    rcases p with v | τ
    ·
      have hs1 : ∀ v', evalV D.host.F v' (singleV D.host.F v 1) ∈ v'.adicCompletionIntegers D.host.F := by
        intro v'
        by_cases h : v' = v
        · rw [h, ev_self]
          exact one_mem _
        · rw [ev_ne _ h]
          exact zero_mem _
      have e1 : wAt (.inl v) (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] X i j) =
          Matrix.of fun i j => pairA D.host.F 0 (singleV D.host.F v 1 * α) ⊗ₜ[D.host.F] X i j := by
        ext i j
        simp only [wAt, Matrix.of_apply, idem_inl_mul]
      have e2 : (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] X i j) -
            wAt (.inl v) (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] X i j) =
          Matrix.of fun i j => pairA D.host.F 0 (α - singleV D.host.F v 1 * α) ⊗ₜ[D.host.F] X i j := by
        rw [e1]
        ext i j
        simp only [Matrix.sub_apply, Matrix.of_apply, ← TensorProduct.sub_tmul]
        congr 1
        exact Prod.ext (sub_self _) rfl
      refine ⟨?_, ?_, fun hp => ?_⟩
      · rw [e1]
        refine gen _ _ (fun v' => ?_) (fun v' hv' => ?_)
        · rw [map_mul]
          exact mul_mem (hs1 v') (hα v')
        · by_cases h : v' = v
          · rw [h] at hv' ⊢
            have hPv : ¬ P v := fun hP => hv' ⟨hP, rfl⟩
            rw [map_mul, hv v hPv, mul_zero]
          · rw [map_mul, ev_ne _ h, zero_mul]
      · rw [e2]
        refine gen _ _ (fun v' => ?_) (fun v' hv' => ?_)
        · rw [map_sub, map_mul]
          exact sub_mem (hα v') (mul_mem (hs1 v') (hα v'))
        · by_cases h : v' = v
          · rw [h, map_sub, map_mul, ev_self, one_mul, sub_self]
          · have hPv : ¬ P v' := fun hP => hv' ⟨hP, fun e => h (Sum.inl_injective e)⟩
            rw [map_sub, map_mul, hv v' hPv, mul_zero, sub_zero]
      · have hPv : ¬ P v := fun hP => hp v hP rfl
        have h0 : singleV D.host.F v 1 * α = 0 := by
          apply af_ext
          intro v'
          by_cases h : v' = v
          · rw [h, map_mul, hv v hPv, mul_zero, map_zero]
          · rw [map_mul, ev_ne _ h, zero_mul, map_zero]
        rw [e1, h0]
        ext i j
        simp only [Matrix.of_apply, Matrix.zero_apply]
        rw [show pairA D.host.F 0 0 = 0 from Prod.ext rfl rfl, TensorProduct.zero_tmul]
    ·
      have e0 : wAt (.inr τ) (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] X i j) = 0 := by
        ext i j
        simp only [wAt, Matrix.of_apply, Matrix.zero_apply, idem_inr_mul]
      refine ⟨?_, ?_, fun _ => e0⟩
      · rw [e0]
        exact zero_mem _
      · rw [e0, sub_zero]
        exact gen _ _ hα (fun v' hv' => hv v' (fun hP => hv' ⟨hP, Sum.inl_ne_inr⟩))
  | zero =>
    rw [wAt_zero, sub_zero]
    exact ⟨zero_mem _, zero_mem _, fun _ => rfl⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨hx1, hx2, hx3⟩ := ihx
    obtain ⟨hy1, hy2, hy3⟩ := ihy
    rw [wAt_add]
    refine ⟨add_mem hx1 hy1, ?_, fun hp => by rw [hx3 hp, hy3 hp, add_zero]⟩
    rw [add_sub_add_comm]
    exact add_mem hx2 hy2
  | neg x _ ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [wAt_neg]
    refine ⟨neg_mem h1, ?_, fun hp => by rw [h3 hp, neg_zero]⟩
    rw [neg_sub_neg, ← neg_sub]
    exact neg_mem h2

end GlobalTheory.LatticeLocal
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder

namespace GlobalTheory.StepVec

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}


open Classical in
def gLoc {a b : ℕ} (L : Formalism.L2.DIV.LevDat D.host.E ℂ a) (PP : Formalism.L2.DIV.Pl D.host.E)
    (H : Subgroup (GL (Fin L.r) (Formalism.L2.DIV.kP PP))) (c : H →* ℂˣ) (χ : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (y : Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP)) : ℂ :=
  if h : LowZero a y ∧ ∃ g : GL (Fin a) (Formalism.L2.DIV.kP PP),
      ((g : GL (Fin a) _) : Matrix (Fin a) (Fin a) _) = topL a y ∧
      g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf L.r L.t) ∧ Formalism.L2.DIV.upperLeftBlock L.hr g ∈ H then
    ((c ⟨Formalism.L2.DIV.upperLeftBlock L.hr h.2.choose, h.2.choose_spec.2.2⟩ : ℂˣ) : ℂ) *
      (∏ i ∈ Finset.range L.s,
        ((L.cg (i + 1) PP (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf L.r L.t) (i + 1) h.2.choose) : ℂˣ) : ℂ)) *
      (((χ (Matrix.GeneralLinearGroup.det h.2.choose)) : ℂˣ) : ℂ)⁻¹
  else 0


open Classical in
def qLoc {a b : ℕ} (r : ℕ) (PP : Formalism.L2.DIV.Pl D.host.E) (ξ : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (y : Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP)) : ℂ :=
  if h : LowZero r y ∧ IsUnit (topL r y).det then ((ξ h.2.unit : ℂˣ) : ℂ) else 0

def IsRedMap {v : FinPl D} (φ : SplitProj D v) (PP : Formalism.L2.DIV.Pl D.host.E)
    (r : v.adicCompletionIntegers D.host.F →+* Formalism.L2.DIV.kP PP) : Prop :=
  Function.Surjective r ∧ (∀ a : v.adicCompletionIntegers D.host.F, r a = 0 ↔ Valued.v (a : Fv D.host.F v) < 1) ∧
    (∀ (a : Fv D.host.F v) (b : Formalism.L2.DIV.kP PP), RedRel φ PP a b ↔ ∃ h : a ∈ v.adicCompletionIntegers D.host.F, r ⟨a, h⟩ = b) ∧
    ∀ (N : EAf D) (hN : N ∈ Formalism.L2.Herm.intAf D.host.F D.host.E),
      ∃ h : rdE φ N ∈ v.adicCompletionIntegers D.host.F, r ⟨rdE φ N, h⟩ = Formalism.L2.DIV.resS D.host.F PP ⟨N, hN⟩


open Classical in
def viaRed {v : FinPl D} {k : Type} [CommRing k] {a b : ℕ} (r : v.adicCompletionIntegers D.host.F →+* k)
    (ω : Matrix (Fin b) (Fin a) k → ℂ) (Y : Matrix (Fin b) (Fin a) (Fv D.host.F v)) : ℂ :=
  if h : ∀ i j, Y i j ∈ v.adicCompletionIntegers D.host.F then ω (Matrix.of fun i j => r ⟨Y i j, h i j⟩) else 0


open Classical in
def locFn (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D)
    (PP : Formalism.L2.DIV.Pl D.host.E) (ω : Matrix (Fin T.rank) (Fin S.rank) (Formalism.L2.DIV.kP PP) → ℂ) : WO S T → ℂ :=
  fun x => if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then ω (redM PP (frMapO S T βS βT x)) else 0

end GlobalTheory.StepVec

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isSmoothAutomorphic_rightTranslate_finite : ∀ {D : D7} (θ : InfFam D) (V : HSp D) (κ : GA D V), κ ∈ GfC V → ∀ φ : GA D V → ℂ, IsAutFunSm θ V φ → IsAutFunSm θ V (rTr V κ φ) := by
  first | exact @GlobalTheory.FinTranslate.isAutFunSm_rTr | exact GlobalTheory.FinTranslate.isAutFunSm_rTr | (intros; apply GlobalTheory.FinTranslate.isAutFunSm_rTr <;> assumption)
end

module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle016
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle070
public import Development.WeilBound.ThetaLifts.LatticeBasics.FrameConj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicIntertwine
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle031
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle033
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.Bundle001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle068
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle025
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.CompFinFinOne
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.ChiWPf
import Development.WeilBound.ThetaLifts.TowerModels.LeviAd
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle034
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle012
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle006
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle005
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAHEqOfMemRatPts

@[expose] public section

section



section
noncomputable section
namespace GlobalTheory.ThK.Dbl.Frame
open scoped Matrix TensorProduct
open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Doubling
open Formalism.UG (bc)
section Generic
variable {S R β : Type} [CommRing S] [CommRing R] [Fintype β] [DecidableEq β]
end Generic
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
end GlobalTheory.ThK.Dbl.Frame
namespace GlobalTheory.ThK.Dbl
open scoped Matrix TensorProduct
open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Doubling GlobalTheory.ThK.Dbl.Frame
open Formalism.UG (bc)
theorem frameConj_k : _root_.GlobalTheory.ThK.Dbl.FrameConj_k := by
  intro F E _ _ _ _ _ σ B n Y r s hB hY K hK
  have hc := hB.cm
  have hσ := cm_conj_conj hc
  have hL : Y.L.IsLattice E := hY.elim (·.lat.toIsLattice) (·.lat.toIsLattice)
  have hJ := Frame.det_ne hY
  obtain ⟨ε, hε, c, c1, c2⟩ : ∃ ε : ℤˣ, (Y.J.map σ)ᵀ = ((ε : ℤ) : E) • Y.J ∧ ∃ c : ℂ, star c * c = 1 ∧
      ∀ w, (c • Y.J.map (B.emb w).1)ᴴ = c • Y.J.map (B.emb w).1 ∧ IsCartan (c • Y.J.map (B.emb w).1) (Y.θ w) := by
    rcases hY with h | h
    · refine ⟨1, Matrix.ext fun i j => by simpa using h.herm i j, 1, by simp, fun w => ?_⟩
      rw [one_smul]
      exact ⟨Matrix.ext fun i j => (hc.2.2.2 _ _).symm.trans (congrArg _ (h.herm i j)), h.cartan w⟩
    · refine ⟨-1, Matrix.ext fun i j => by simpa using h.skew i j, Complex.I, by simp, fun w => ⟨Matrix.ext fun i j => ?_, h.cartan w⟩⟩
      change star (Complex.I * (B.emb w).1 (Y.J j i)) = Complex.I * (B.emb w).1 (Y.J i j)
      rw [star_mul', ← hc.2.2.2, h.skew]; simp
  have ee : ∀ (S : Type) [CommRing S], ((ε : ℤ) : S) * (ε : ℤ) = 1 := fun S _ => by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp
  choose gw hw using fun w => Frame.exists_arch c1 (c2 w).1 (Frame.isUnit_of_cartan (c2 w).2) (c2 w).2
  obtain ⟨a, g, ha, hg, hg'⟩ := _root_.GlobalTheory.ThK.Dbl.Frame.exists_ad_k hB hY hJ gw
  obtain ⟨t, ht⟩ := _root_.GlobalTheory.exists_int_add_conj_eq_one_of_base_good_k B hB
  let ι := inclR (F := F) (E := E) (AF F)
  let cc : AE F E →+* AE F E := cA σ
  have hι : ∀ z, ι (σ z) = cc (ι z) := fun z => rfl
  have hcc : ∀ z, cc (cc z) = z := fun z => by
    change cA σ (cA σ z) = z
    rw [cA_eq]; exact sigR_invol hσ z
  have hf : ∀ v z, compFin F E v (cc z) = sigR _ σ (compFin F E v z) := fun v z => by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a x => rfl
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hi : ∀ w z, piInf (B.emb w) (cc z) = star (piInf (B.emb w) z) := fun w z => by
    refine Eq.trans (congrArg (infEmb (B.emb w)) ?_) (infEmb_sigR hc (B.emb w) (compInf F E w z)).symm
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a x => rfl
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have jf : ∀ v, (incM F Y.J).map (compFin F E v) = Y.J.map (inclR (F := F) (Fv F v)) := fun v =>
    Matrix.ext fun i j => congrArg (· ⊗ₜ[F] Y.J i j) (map_one (evFin F v))
  have ii : ∀ w z, piInf (B.emb w) (ι z) = (B.emb w).1 z := fun w z => by
    change InfinitePlace.Completion.extensionEmbedding w 1 * (B.emb w).1 z = _
    rw [map_one, one_mul]
  have ji : ∀ w, (incM F Y.J).map (piInf (B.emb w)) = Y.J.map (B.emb w).1 := fun w => Matrix.ext fun i j => ii w _
  have h2 : (2⁻¹ : E) + σ 2⁻¹ = 1 := by rw [map_inv₀, map_ofNat]; norm_num
  let α : AE F E := ι 2⁻¹ + eF F • ι (t - 2⁻¹)
  have α0 : α + cc α = 1 := by
    have : cc α = ι (σ 2⁻¹) + eF F • ι (σ (t - 2⁻¹)) := by
      rw [hι, hι, map_add (f := _)]; exact congrArg _ (map_smul (cA σ) _ _)
    rw [this, add_add_add_comm, ← smul_add, ← map_add (f := _), ← map_add (f := _), h2, map_sub σ, sub_add_sub_comm, ht, h2, sub_self]
    simp
  have α1 : ∀ v, compFin F E v α ∈ intLoc F E v := fun v => by
    rw [map_add (f := _), comp_eF, ← map_add (f := _), ← map_add (f := _), add_sub_cancel]
    exact tmul_mem_intLoc (a := evFin F v 1) (by rw [map_one]; exact one_mem _) t
  have α2 : ∀ w, piInf (B.emb w) α = 2⁻¹ := fun w => by
    have : piInf (B.emb w) (algebraMap (AF F) (AE F E) (eF F)) = 0 := by
      change InfinitePlace.Completion.extensionEmbedding w 0 * (B.emb w).1 1 = _
      rw [map_zero, zero_mul]
    rw [map_add (f := _), Algebra.smul_def, map_mul, this, zero_mul, add_zero, ii, map_inv₀, map_ofNat]
  have uJ : IsUnit Y.J := (Matrix.isUnit_iff_isUnit_det _).2 hJ.isUnit
  obtain ⟨T₀, hT₀⟩ := exists_dual (σ : E →+* E) hσ uJ 1
  obtain ⟨T, hT⟩ := exists_dual cc hcc (J := incM F Y.J) (uJ.map ι.mapMatrix) g
  have g0 := frame_gram (σ : E →+* E) hσ (ee E) h2 hε 1 T₀ hT₀
  have g1 := frame_gram cc hcc (ee _) α0 (J := incM F Y.J) (Matrix.ext fun i j => by
    have := congrArg ι (congrFun (congrFun hε i) j)
    rw [Matrix.smul_apply, smul_eq_mul, map_mul, map_intCast] at this
    exact this) g T hT
  have d0 := frame_diag 1 T₀ (2⁻¹ : E)
  set b := two 1 * wit (2⁻¹ : E) T₀
  have d1 := frame_diag g T α
  set b' := two g * wit α T with hb'
  have g2 : (bc ι b).1ᵀ * dbl (incM F Y.J) * (bc ι b).1.map cc = b'.1ᵀ * dbl (incM F Y.J) * b'.1.map cc := by
    have := (map_gram ι hι b.1 (dbl Y.J)).symm.trans (congrArg (·.map ι) g0)
    rw [map_dbl] at this
    rw [g1]
    refine this.trans ?_
    ext (i | i) (j | j) <;> simp [Matrix.one_apply, apply_ite ι]
  let p : G2 σ Y := ⟨b' * (bc ι b)⁻¹, by
    change (b'.1 * ((bc ι b)⁻¹).1)ᵀ * _ * (b'.1 * ((bc ι b)⁻¹).1).map cc = _
    calc _ = ((bc ι b)⁻¹).1ᵀ * (b'.1ᵀ * dbl (incM F Y.J) * b'.1.map cc) * ((bc ι b)⁻¹).1.map cc := by
          simp only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
      _ = ((bc ι b).1 * ((bc ι b)⁻¹).1)ᵀ * dbl (incM F Y.J) * ((bc ι b).1 * ((bc ι b)⁻¹).1).map cc := by
          simp only [← g2, Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
      _ = _ := by rw [Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]⟩
  have fr : ∀ k : G2 σ Y, inFrame b k = (b'⁻¹ * (p * k * p⁻¹).1 * b').1 := fun k => by
    rw [show b'⁻¹ * (p * k * p⁻¹).1 * b' = bc ι b⁻¹ * k.1 * bc ι b by
      change b'⁻¹ * (b' * (bc ι b)⁻¹ * k.1 * (b' * (bc ι b)⁻¹)⁻¹) * b' = _
      rw [map_inv]; group]
    rfl
  have fin : ∀ k : G2 σ Y, Keeps (p * k * p⁻¹) ↔ ∀ i j, eF F • inFrame b k i j ∈ intHat F E := fun k => by
    simp only [keeps_iff hL.fg ha, mem_intHat, fr]
    refine (forall_congr' fun v => ?_).trans (forall_comm.trans (forall_congr' fun i => forall_comm))
    obtain ⟨⟨l, hl⟩, u1, G', u2, u3⟩ := hg v
    obtain ⟨q1, q2⟩ := int_dual (T := bc (compFin F E v) T) (sigR_invol hσ) (fun z => sigR_mem_intLoc σ) u1 u2 u3 (by
      have := congrArg (·.map (compFin F E v)) hT
      simp only [Matrix.map_mul (M := T.1.map cc), map_gram _ (hf v), jf, Matrix.map_one _ (map_zero _) (map_one _)] at this
      rw [← this]
      congr 1
      exact Matrix.ext fun i j => (hf v _).symm)
    obtain ⟨q3, q4⟩ := int_wit (α1 v) q1 q2
    have := int_conj hl q3 q4 (bc (compFin F E v) (p * k * p⁻¹).1)
    simp only [← bc_wit, ← bc_two, ← map_mul (bc (compFin F E v)), ← map_inv (bc (compFin F E v))] at this
    exact this
  refine ⟨b, K.comap (MulAut.conj p).toMonoidHom, p, g, ⟨⟨ε, g0⟩, 1, ?_⟩, fun k => ?_, ?_, fun k => ?_⟩
  · rw [← d0, ← Matrix.fromCols_toCols b.1, Matrix.fromCols_mul_fromRows]; simp
  · refine (hK (p * k * p⁻¹)).trans (and_congr (forall_congr' fun w => ?_) ?_)
    · have := hw w (bc (piInf (B.emb w)) T) (by
        have := congrArg (·.map (piInf (B.emb w))) hT
        simp only [Matrix.map_mul (M := T.1.map cc), map_gram _ (hi w), ji, Matrix.map_one _ (map_zero _) (map_one _)] at this
        rw [← this, ← hg']
        congr 1
        exact Matrix.ext fun i j => (hi w _).symm) (bc (piInf (B.emb w)) (p * k * p⁻¹).1) (by
        have := (map_gram _ (hi w) _ _).symm.trans (congrArg (·.map (piInf (B.emb w))) (show _ = _ from (p * k * p⁻¹).2))
        simp only [map_dbl, ji] at this
        exact this)
      rw [← hg', ← α2 w, ← bc_wit, ← bc_two, ← map_mul, ← map_inv, ← map_mul, ← map_mul] at this
      rw [fr]
      exact this.symm
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, forall_and]
      refine Iff.trans ?_ (and_congr (fin k) (fin k⁻¹))
      rw [show p * k⁻¹ * p⁻¹ = (p * k * p⁻¹)⁻¹ by group]
      simp only [Keeps, forall_and]
      exact and_and_and_comm
  · exact par_of ι (d0.trans (Matrix.mul_one _)) d1
  · change _ ↔ p * (p⁻¹ * k * p) * p⁻¹ ∈ K
    rw [show p * (p⁻¹ * k * p) * p⁻¹ = k by group]
end GlobalTheory.ThK.Dbl
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace KC
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
def sec_k : (InfinitePlace F → ℂ) → AE F E := (Place.exists_sec d.cm d.B.emb).choose
theorem sec_spec_k : Continuous (_root_.PositivityTheory.SiegelWeilFormula.KC.sec_k d) ∧ (∀ x w, piInf (d.B.emb w) (_root_.PositivityTheory.SiegelWeilFormula.KC.sec_k d x) = x w) ∧ (∀ x, finOne F • _root_.PositivityTheory.SiegelWeilFormula.KC.sec_k d x = 0) ∧
    (∀ x y, _root_.PositivityTheory.SiegelWeilFormula.KC.sec_k d (x + y) = _root_.PositivityTheory.SiegelWeilFormula.KC.sec_k d x + _root_.PositivityTheory.SiegelWeilFormula.KC.sec_k d y) ∧ (∀ x y, _root_.PositivityTheory.SiegelWeilFormula.KC.sec_k d (x * y) = _root_.PositivityTheory.SiegelWeilFormula.KC.sec_k d x * _root_.PositivityTheory.SiegelWeilFormula.KC.sec_k d y) :=
  (Place.exists_sec d.cm d.B.emb).choose_spec
theorem uW_eq_k (w : InfinitePlace F) (z : ℂ) :
    d.uW w z = _root_.PositivityTheory.SiegelWeilFormula.KC.sec_k d (Function.update (fun _ => 1) w z) + finOne F • (1 : AE F E) := rfl
theorem sec_mul_e_k (x : InfinitePlace F → ℂ) : _root_.PositivityTheory.SiegelWeilFormula.KC.sec_k d x * (finOne F • (1 : AE F E)) = 0 := by
  rw [mul_smul_comm, mul_one, (_root_.PositivityTheory.SiegelWeilFormula.KC.sec_spec_k d).2.2.1]
theorem e_mul_sec_k (x : InfinitePlace F → ℂ) : (finOne F • (1 : AE F E)) * _root_.PositivityTheory.SiegelWeilFormula.KC.sec_k d x = 0 := by
  rw [smul_mul_assoc, one_mul, (_root_.PositivityTheory.SiegelWeilFormula.KC.sec_spec_k d).2.2.1]
theorem uW_mul_k (w : InfinitePlace F) (z z' : ℂ) : d.uW w (z * z') = d.uW w z * d.uW w z' := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.KC.uW_eq_k, _root_.PositivityTheory.SiegelWeilFormula.KC.uW_eq_k, _root_.PositivityTheory.SiegelWeilFormula.KC.uW_eq_k, update_mul, (_root_.PositivityTheory.SiegelWeilFormula.KC.sec_spec_k d).2.2.2.2, add_mul, mul_add, mul_add, _root_.PositivityTheory.SiegelWeilFormula.KC.sec_mul_e_k, _root_.PositivityTheory.SiegelWeilFormula.KC.e_mul_sec_k, e_mul_e]
  abel
theorem uW_one_k (w : InfinitePlace F) : d.uW w 1 = 1 := by
  apply d.ae_ext
  · intro w'
    rw [_root_.PositivityTheory.SiegelWeilFormula.KC.uW_eq_k, map_add (f := _), (_root_.PositivityTheory.SiegelWeilFormula.KC.sec_spec_k d).2.1, Place.piInf_finOne, map_one]
    simp [Function.update_apply]
  · rw [_root_.PositivityTheory.SiegelWeilFormula.KC.uW_eq_k, smul_add, (_root_.PositivityTheory.SiegelWeilFormula.KC.sec_spec_k d).2.2.1, smul_smul, finOne_mul_self, zero_add]
theorem uW_isUnit_k (w : InfinitePlace F) {z : ℂ} (hz : z ≠ 0) : IsUnit (d.uW w z) := by
  have h : d.uW w z * d.uW w z⁻¹ = 1 := by rw [← _root_.PositivityTheory.SiegelWeilFormula.KC.uW_mul_k, mul_inv_cancel₀ hz, _root_.PositivityTheory.SiegelWeilFormula.KC.uW_one_k]
  exact ⟨⟨d.uW w z, d.uW w z⁻¹, h, by rw [mul_comm]; exact h⟩, rfl⟩
theorem uW_cont_k (w : InfinitePlace F) : Continuous (d.uW w) := by
  have h : Continuous fun z : ℂ => Function.update (fun _ : InfinitePlace F => (1 : ℂ)) w z :=
    continuous_const.update w continuous_id
  exact ((_root_.PositivityTheory.SiegelWeilFormula.KC.sec_spec_k d).1.comp h).add continuous_const
end KC
namespace SD
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem _root_.PositivityTheory.SiegelWeilFormula.SD_k.chiW_mul_pf (w : InfinitePlace F) : ∀ z z' : ℂ, z ≠ 0 → z' ≠ 0 →
    d.chiW w (z * z') = d.chiW w z * d.chiW w z' := by
  intro z z' hz hz'
  have h1 := _root_.PositivityTheory.SiegelWeilFormula.KC.uW_isUnit_k d w hz
  have h2 := _root_.PositivityTheory.SiegelWeilFormula.KC.uW_isUnit_k d w hz'
  have h3 := _root_.PositivityTheory.SiegelWeilFormula.KC.uW_isUnit_k d w (mul_ne_zero hz hz')
  unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.chiW
  rw [dite_eq_left h3, dite_eq_left h1, dite_eq_left h2]
  have : h3.unit = h1.unit * h2.unit := Units.ext (by simp [_root_.PositivityTheory.SiegelWeilFormula.KC.uW_mul_k])
  rw [this, map_mul, Circle.coe_mul]
theorem _root_.PositivityTheory.SiegelWeilFormula.SD_k.chiW_cont_pf (w : InfinitePlace F) : ContinuousOn (d.chiW w) {z : ℂ | z ≠ 0} := by
  rw [continuousOn_iff_continuous_domRestrict]
  let U : {z : ℂ // z ≠ 0} → (AE F E)ˣ := fun z => (_root_.PositivityTheory.SiegelWeilFormula.KC.uW_isUnit_k d w z.2).unit
  have hU : Continuous U := by
    rw [Units.continuous_iff]
    constructor
    · exact (_root_.PositivityTheory.SiegelWeilFormula.KC.uW_cont_k d w).comp continuous_subtype_val
    · have e : ∀ z : {z : ℂ // z ≠ 0}, ((U z)⁻¹ : (AE F E)ˣ).1 = d.uW w (z.1)⁻¹ := fun z =>
        Units.inv_eq_of_mul_eq_one_right (by
          show d.uW w z.1 * d.uW w (z.1)⁻¹ = 1
          rw [← _root_.PositivityTheory.SiegelWeilFormula.KC.uW_mul_k, mul_inv_cancel₀ z.2, _root_.PositivityTheory.SiegelWeilFormula.KC.uW_one_k])
      simp only [e]
      exact (_root_.PositivityTheory.SiegelWeilFormula.KC.uW_cont_k d w).comp (continuous_subtype_val.inv₀ fun z => z.2)
  have e : Set.domRestrict {z : ℂ | z ≠ 0} (d.chiW w) = fun z => ((d.χ (U z) : Circle) : ℂ) := by
    funext z
    rw [Set.domRestrict_apply]
    unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.chiW
    rw [dite_eq_left (_root_.PositivityTheory.SiegelWeilFormula.KC.uW_isUnit_k d w z.2)]
  rw [e]
  exact continuous_subtype_val.comp (d.ok.hecke.1.comp hU)
theorem _root_.PositivityTheory.SiegelWeilFormula.SD_k.chiW_pos_pf (w : InfinitePlace F) : ∀ r : ℝ, 0 < r → d.chiW w (r : ℂ) = 1 := by
  intro r hr
  set t := Real.sqrt r with ht
  have ht0 : (t : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact (Real.sqrt_pos.mpr hr).ne'
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hc : cA σ (d.uW w t) = d.uW w t := by
    apply d.ae_ext
    · intro w'
      rw [Place.piInf_cA d.cm, _root_.PositivityTheory.SiegelWeilFormula.KC.uW_eq_k, map_add (f := _), (_root_.PositivityTheory.SiegelWeilFormula.KC.sec_spec_k d).2.1, Place.piInf_finOne, add_zero]
      by_cases h : w' = w
      · subst h; simp
      · simp [Function.update_apply, h]
    · rw [← map_smul, _root_.PositivityTheory.SiegelWeilFormula.KC.uW_eq_k, smul_add, (_root_.PositivityTheory.SiegelWeilFormula.KC.sec_spec_k d).2.2.1, zero_add, smul_smul, KC.finOne_mul_self, map_smul,
        map_one]
  have huw : d.uW w (r : ℂ) = d.uW w t * cA σ (d.uW w t) := by
    rw [hc, ← _root_.PositivityTheory.SiegelWeilFormula.KC.uW_mul_k, ← Complex.ofReal_mul, ht, Real.mul_self_sqrt hr.le]
  obtain ⟨ξ, hξ⟩ := GlobalTheory.SplitIdele.exists_isQuad d.cm
  have hn := hξ.algebraMap_norm (d.uW w t)
  let u := (_root_.PositivityTheory.SiegelWeilFormula.KC.uW_isUnit_k d w ht0).unit
  let a : (AF F)ˣ := Units.map (Algebra.norm (AF F) : AE F E →* AF F) u
  have ha : Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E) a = (_root_.PositivityTheory.SiegelWeilFormula.KC.uW_isUnit_k d w hr0).unit :=
    Units.ext (by
      show algebraMap (AF F) (AE F E) (Algebra.norm (AF F) (d.uW w t)) = d.uW w (r : ℂ)
      rw [hn, huw])
  have hres := d.ok.res a
  rw [if_pos (Subgroup.mem_sup_right (MonoidHom.mem_range.mpr ⟨u, rfl⟩))] at hres
  unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.chiW
  rw [dite_eq_left (_root_.PositivityTheory.SiegelWeilFormula.KC.uW_isUnit_k d w hr0), ← ha]
  exact hres
end SD
end PositivityTheory.SiegelWeilFormula
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F)
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.compFin_det (t : GL (Fin d.n) (AE F E)) (hf : finOne F • t.1 = finOne F • 1) (v : Pl F) :
    compFin F E v (t.1.det) = 1 := by
  have hm : t.1.map (compFin F E v) = 1 := by
    ext i j
    rw [Matrix.map_apply, ← Place.compFin_finOne v (t.1 i j)]
    change compFin F E v ((finOne F • t.1) i j) = _
    rw [hf, Matrix.smul_apply, Place.compFin_finOne, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [RingHom.map_det, RingHom.mapMatrix_apply, hm, Matrix.det_one]
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.piInf_det (t : GL (Fin d.n) (AE F E)) (a : Matrix (Fin d.n) (Fin d.n) ℂ) (ht : d.cw w t.1 = a)
    (ho : ∀ w', w' ≠ w → d.cw w' t.1 = 1) (w' : InfinitePlace F) :
    piInf (d.B.emb w') (t.1.det) = Function.update (fun _ => (1 : ℂ)) w a.det w' := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply]
  by_cases h : w' = w
  · subst h
    rw [Function.update_self]
    exact congrArg Matrix.det ht
  · rw [Function.update_of_ne h]
    have := congrArg Matrix.det (ho w' h)
    rw [Matrix.det_one] at this
    exact this
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.det_uW (t : GL (Fin d.n) (AE F E)) (a : Matrix (Fin d.n) (Fin d.n) ℂ) (ht : d.cw w t.1 = a)
    (ho : ∀ w', w' ≠ w → d.cw w' t.1 = 1) (hf : finOne F • t.1 = finOne F • 1) :
    t.1.det = d.uW w a.det := by
  obtain ⟨-, hs2, hs3, -, -⟩ := (Place.exists_sec d.cm d.B.emb).choose_spec
  apply PositivityTheory.ThKG.Tow.Levi.ad_ext d.cm d.B.emb
  · intro w'
    rw [_root_.PositivityTheory.SiegelWeilFormula.RD_k.piInf_det (d := d) w t a ht ho w', _root_.PositivityTheory.SiegelWeilFormula.SD_k.uW, map_add (f := _), hs2, Place.piInf_finOne, add_zero]
  · intro v
    rw [_root_.PositivityTheory.SiegelWeilFormula.RD_k.compFin_det (d := d) t hf v, _root_.PositivityTheory.SiegelWeilFormula.SD_k.uW, map_add (f := _), ← Place.compFin_finOne v, hs3, map_zero, zero_add,
      Place.compFin_finOne, map_one]
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.chi_det (t : GL (Fin d.n) (AE F E)) (a : Matrix (Fin d.n) (Fin d.n) ℂ) (ht : d.cw w t.1 = a)
    (ho : ∀ w', w' ≠ w → d.cw w' t.1 = 1) (hf : finOne F • t.1 = finOne F • 1) :
    (d.χ (Matrix.GeneralLinearGroup.det t) : ℂ) = d.chiW w a.det := by
  have e := _root_.PositivityTheory.SiegelWeilFormula.RD_k.det_uW (d := d) w t a ht ho hf
  have hu : IsUnit (d.uW w a.det) := by
    rw [← e]
    exact (Matrix.GeneralLinearGroup.det t).isUnit.map (RingHom.id _) |>.map (RingHom.id _) |> fun h => by
      simpa [Matrix.GeneralLinearGroup.val_det_apply] using h
  rw [_root_.PositivityTheory.SiegelWeilFormula.SD_k.chiW, dite_eq_left hu]
  have : hu.unit = Matrix.GeneralLinearGroup.det t :=
    Units.ext (by rw [IsUnit.unit_spec, Matrix.GeneralLinearGroup.val_det_apply, e])
  rw [this]
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.absE_det (t : GL (Fin d.n) (AE F E)) (a : Matrix (Fin d.n) (Fin d.n) ℂ) (ht : d.cw w t.1 = a)
    (ho : ∀ w', w' ≠ w → d.cw w' t.1 = 1) (hf : finOne F • t.1 = finOne F • 1) :
    (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) = ‖a.det‖ ^ 2 := by
  rw [GlobalTheory.Doubling.absE_apply]
  have hinf : ∀ w', GlobalTheory.Doubling.absEw F E w' (GlobalTheory.Doubling.unitInf F E w' (Matrix.GeneralLinearGroup.det t)) =
      ‖Function.update (fun _ => (1 : ℂ)) w a.det w'‖₊ ^ 2 := by
    intro w'
    rw [GlobalTheory.Doubling.absEw_eq_sq d.cm (d.B.emb w'), ← _root_.PositivityTheory.SiegelWeilFormula.RD_k.piInf_det (d := d) w t a ht ho w',
      ← Matrix.GeneralLinearGroup.val_det_apply]
    rfl
  have hfin : ∀ v, GlobalTheory.Doubling.absEv F E v (GlobalTheory.Doubling.unitFin F E v (Matrix.GeneralLinearGroup.det t)) = 1 := by
    intro v
    have : GlobalTheory.Doubling.unitFin F E v (Matrix.GeneralLinearGroup.det t) = 1 := by
      apply Units.ext
      show compFin F E v ((Matrix.GeneralLinearGroup.det t : (AE F E)ˣ) : AE F E) = 1
      rw [Matrix.GeneralLinearGroup.val_det_apply, _root_.PositivityTheory.SiegelWeilFormula.RD_k.compFin_det (d := d) t hf v]
    rw [this, map_one]
  simp only [hinf, hfin, finprod_one, mul_one]
  rw [Finset.prod_eq_single w (fun w' _ h => by rw [Function.update_of_ne h]; simp) (fun h => absurd (Finset.mem_univ w) h),
    Function.update_self]
  push_cast
  rfl
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.stepM_val_pf (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) : ∀ (y : GR d.n) (a : Matrix (Fin d.n) (Fin d.n) ℂ), IsUnit a.det → mR y = mLoc a →
    R.StepOK w (R.ι w y) (fun f u => (d.chiW w a.det * (‖a.det‖ : ℂ) ^ d.m) * f (Matrix.of u * a)) id := by
  intro y a ha hy
  obtain ⟨t, ht, ho, hf, hS⟩ := R.stepM_gen w hT y a ha hy
  have hc : (d.χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
      (((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) ^ ((d.m : ℝ) / 2) : ℝ) : ℂ) =
      d.chiW w a.det * (‖a.det‖ : ℂ) ^ d.m := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.RD_k.chi_det (d := d) w t a ht ho hf, _root_.PositivityTheory.SiegelWeilFormula.RD_k.absE_det (d := d) w t a ht ho hf, ← Real.rpow_natCast ‖a.det‖ 2,
      ← Real.rpow_mul (norm_nonneg _), show ((2 : ℕ) : ℝ) * ((d.m : ℝ) / 2) = (d.m : ℝ) by push_cast; ring,
      Real.rpow_natCast]
    push_cast
    rfl
  simp only [hc] at hS
  exact hS
end RD
end PositivityTheory.SiegelWeilFormula
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
open PositivityTheory.SiegelWeilFormula.Ald.YFA
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem yFrame_k : _root_.PositivityTheory.SiegelWeilFormula.Ald.YFrame_k := by
  intro F E _ _ _ _ _ σ d n hN hn
  have hc : ∀ z : E, σ (σ z) = z := sig_sig' d.ok.good.cm
  obtain ⟨ε, hε⟩ := d.ok.frame.1
  have hεσ : σ (((ε : ℤ) : E)) = ((ε : ℤ) : E) := map_intCast σ _
  rcases d.ok.sign with ⟨hA, hY⟩ | ⟨hA, hY⟩
  · obtain ⟨ξ, hξ, hσξ⟩ := _root_.GlobalTheory.T.exists_trace_zero_element F E σ d.B d.ok.good
    have hξ' : -ξ ≠ 0 := neg_ne_zero.2 hξ
    let J : Matrix (Fin n) (Fin n) E := ξ • 1
    have hJ : ∀ i j, σ (J j i) = (-1) * J i j := fun i j => by
      by_cases h : i = j
      · subst h; simp [J, hσξ]
      · simp [J, Matrix.one_apply, h, Ne.symm h]
    let T : GL (Fin n) E := ⟨(-ξ)⁻¹ • 1, (-ξ) • 1,
      by rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, inv_mul_cancel₀ hξ', one_smul],
      by rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hξ', one_smul]⟩
    have hm : T.1.map σ = ξ⁻¹ • 1 := by
      ext i j
      by_cases h : i = j
      · subst h; simp [T, map_inv₀, hσξ]
      · simp [T, Matrix.one_apply, h]
    have hT : J * T.1.map σ = 1 := by
      rw [hm, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hξ, one_smul]
    obtain ⟨b, hb, hd⟩ := frame_of hc (by norm_num) hJ T hT
    have hεv : ((ε : ℤ) : E) = -1 :=
      eps_eq (by omega) hc (fun i j => by rw [hY]; ring) hε hεσ
    refine ⟨spcOf F J, b, ε, Or.inl ⟨hA, fun i j => (by simpa using hJ i j : σ (J j i) = -J i j)⟩, ⟨⟨ε, ?_⟩, hd⟩, hε, ?_⟩ <;>
      · change b.1ᵀ * dbl J * b.1.map σ = _
        try simp only [jeps]
        rw [hεv]; exact hb
  · let J : Matrix (Fin n) (Fin n) E := 1
    have hJ : ∀ i j, σ (J j i) = 1 * J i j := fun i j => by
      by_cases h : i = j
      · subst h; simp [J]
      · simp [J, Matrix.one_apply, h, Ne.symm h]
    have hT : J * (1 : GL (Fin n) E).1.map σ = 1 := by
      simp [J, Matrix.map_one _ (map_zero σ) (map_one σ)]
    obtain ⟨b, hb, hd⟩ := frame_of hc (by norm_num) hJ 1 hT
    have hεv : ((ε : ℤ) : E) = 1 :=
      eps_eq (by omega) hc (fun i j => by rw [hY]; ring) hε hεσ
    refine ⟨spcOf F J, b, ε, Or.inr ⟨hA, fun i j => (by simpa using hJ i j : σ (J j i) = J i j)⟩, ⟨⟨ε, ?_⟩, hd⟩, hε, ?_⟩ <;>
      · change b.1ᵀ * dbl J * b.1.map σ = _
        try simp only [jeps]
        rw [hεv]; exact hb
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end

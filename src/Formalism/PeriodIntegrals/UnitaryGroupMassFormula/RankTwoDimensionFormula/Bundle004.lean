module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IsSplitFrame
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.Bundle003
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle044
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.MemMLOfInAt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IsUnitDetLeviM
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.UnitriangularReductionOfMemLevel
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

namespace PI.UnitaryDimensionFormula

open Matrix

section Core

variable {F : Type} [Field F] {k : ℕ}

theorem uniA_mul_diag (A B : Matrix (Fin k) (Fin k) F) (hA : A.BlockTriangular id)
    (hB : B.BlockTriangular id) (i : Fin k) : (A * B) i i = A i i * B i i := by
  first | exact UpperTheory.Reformulated.B.Qh23.uniA_mul_diag .. | (apply UpperTheory.Reformulated.B.Qh23.uniA_mul_diag <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qh23.uniA_mul_diag <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag F ‹_› k A B hA hB i | exact @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag F ‹_› k A B hA hB | exact @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag F ‹_› k A B hA | exact @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag F ‹_› k A B | exact @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag F ‹_› k A | exact @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag F ‹_› k | exact @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag F ‹_› | exact @UpperTheory.Reformulated.B.Qh23.uniA_mul_diag F

theorem uniA_tri (x : GL (Fin k) F) (hx : ∀ i j : Fin k, j < i → (x : Matrix (Fin k) (Fin k) F) i j = 0) :
    (x : Matrix (Fin k) (Fin k) F).BlockTriangular id := fun i j h => hx i j h

theorem uniA_mul (x y : GL (Fin k) F) (hx : Formalism.L2.SG.GGMirabolic.IsUni k x)
    (hy : Formalism.L2.SG.GGMirabolic.IsUni k y) : Formalism.L2.SG.GGMirabolic.IsUni k (x * y) := by
  have tx := uniA_tri x hx.2
  have ty := uniA_tri y hy.2
  have txy : ((x : Matrix (Fin k) (Fin k) F) * (y : Matrix (Fin k) (Fin k) F)).BlockTriangular id :=
    tx.mul ty
  refine ⟨fun i => ?_, fun i j h => ?_⟩
  · rw [Units.val_mul, uniA_mul_diag _ _ tx ty, hx.1 i, hy.1 i, one_mul]
  · rw [Units.val_mul]; exact txy h

theorem uniA_inv (x : GL (Fin k) F) (hx : Formalism.L2.SG.GGMirabolic.IsUni k x) :
    Formalism.L2.SG.GGMirabolic.IsUni k x⁻¹ := by
  have tx := uniA_tri x hx.2
  have : Invertible (x : Matrix (Fin k) (Fin k) F) := Units.invertible x
  have tinv : ((x : Matrix (Fin k) (Fin k) F)⁻¹).BlockTriangular id :=
    Matrix.blockTriangular_inv_of_blockTriangular tx
  have hc : ((x⁻¹ : GL (Fin k) F) : Matrix (Fin k) (Fin k) F) = (x : Matrix (Fin k) (Fin k) F)⁻¹ :=
    Matrix.coe_units_inv x
  refine ⟨fun i => ?_, fun i j h => ?_⟩
  · have h1 : ((x : Matrix (Fin k) (Fin k) F)⁻¹ * (x : Matrix (Fin k) (Fin k) F)) i i = 1 := by
      rw [Matrix.inv_mul_of_invertible, Matrix.one_apply_eq]
    rw [uniA_mul_diag _ _ tinv tx, hx.1 i, mul_one] at h1
    rw [hc]; exact h1
  · rw [hc]; exact tinv h

end Core

theorem uniSub : UniSub := by
  intro F _ k x y hx hy
  exact ⟨uniA_mul x y hx hy, uniA_inv x hx⟩

end PI.UnitaryDimensionFormula
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.Full Formalism.MainNotions.S.Cnt

namespace PI.UnitaryDimensionFormula

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cj_good {D : D7} {X : HidaSetting D} (u : D.what₂.Word) (s : Hfin X u) (hs : cj X u s ∈ X.B.I.Kset) :
    NormCutK.Good X (cj X u s) := by
  have hk1 : (((1 : Hfin X u) : X.B.I.Gf) * X.xu u)⁻¹ * ((s : X.B.I.Gf) * X.xu u) ∈ X.B.I.Kset := by
    simpa [cj, mul_assoc] using hs
  have hk2 : ((s : X.B.I.Gf) * X.xu u)⁻¹ * (((1 : Hfin X u) : X.B.I.Gf) * X.xu u) ∈ X.B.I.Kset := by
    have hi := PI.UnitaryDimensionFormula.kset_inv hs
    simpa [cj, mul_assoc, mul_inv_rev] using hi
  have hg := NormCutK.colGood X u 1 s hk1 hk2
  simpa [cj, mul_assoc] using hg

theorem idxHom : IdxHom := by
  intro D X Y u _
  refine ⟨NormCutK.levi_one (TR := Y.TR), fun s t hs ht => ?_, fun s hs hKu v => ?_⟩
  · have hst : cj X u (s * t) = cj X u s * cj X u t := by
      simp [cj, mul_assoc]
    rw [hst, NormCutK.levi_mul (TR := Y.TR) (cj_good u s hs) (cj_good u t ht)]
  · exact NormCutK.unitriangular_reduction_of_mem_level (TR := Y.TR) (cj_good u s hs) hKu v

end PI.UnitaryDimensionFormula
end
end

section

noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.Full Formalism.MainNotions.S.Cnt

namespace PI.UnitaryDimensionFormula

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Alg

variable {A : Type} [CommRing A] (σ : A →+* A) {n k : ℕ} (J : Matrix (Fin n) (Fin n) A)

theorem hrow_dot (x y : Fin n → A) : hrow σ J x ⬝ᵥ y = Formalism.UG.hform σ J x y := by
  simp only [hrow, Formalism.UG.hform, dotProduct, Finset.sum_mul]
  exact Finset.sum_comm

theorem sMat_mulVec (b bs : Fin k → Fin n → A) (C D : Matrix (Fin k) (Fin k) A) (y : Fin n → A) :
    sMat σ J b bs C D *ᵥ y = y + ∑ i, ∑ j, (((C - 1) i j * Formalism.UG.hform σ J (bs j) y) • b i +
      ((D - 1) i j * Formalism.UG.hform σ J (b j) y) • bs i) := by
  have key : ∀ (a c : Fin n → A) (t : A), (t • Matrix.vecMulVec a c) *ᵥ y = (t * (c ⬝ᵥ y)) • a := by
    intro a c t
    funext q
    simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun r _ => by ring
  have hsum : ∀ (s : Finset (Fin k)) (f : Fin k → Matrix (Fin n) (Fin n) A),
      (∑ i ∈ s, f i) *ᵥ y = ∑ i ∈ s, f i *ᵥ y := by
    intro s f
    classical
    refine Finset.induction_on s (by simp) ?_
    intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.add_mulVec, ih]
  unfold sMat
  rw [Matrix.add_mulVec, Matrix.one_mulVec, hsum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hsum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.add_mulVec, key, key, hrow_dot, hrow_dot]

end Alg

variable {D : D7} {X : HidaSetting D}

theorem sMat_Lf (hI : IdxDInt) (b bs : Fin D.R.k → VA X.B.I) (hb : ∀ i, b i ∈ X.B.I.Lf ∧ bs i ∈ X.B.I.Lf)
    (C D' : Matrix (Fin D.R.k) (Fin D.R.k) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F))
    (hC : ∀ i j, (C - 1) i j ∈ IntAf X.B.I.F X.B.I.E ∧ (D' - 1) i j ∈ IntAf X.B.I.F X.B.I.E)
    (y : VA X.B.I) (hy : y ∈ X.B.I.Lf) :
    sMat (sigA X.B.I) (JA X.B.I) b bs C D' *ᵥ y ∈ X.B.I.Lf := by
  rw [sMat_mulVec]
  refine X.B.I.Lf.add_mem hy (Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_)
  have h1 : Formalism.UG.hform (sigA X.B.I) (JA X.B.I) (bs j) y ∈ IntAf X.B.I.F X.B.I.E :=
    (hI X.B.I).1 _ (hb j).2 _ hy
  have h2 : Formalism.UG.hform (sigA X.B.I) (JA X.B.I) (b j) y ∈ IntAf X.B.I.F X.B.I.E :=
    (hI X.B.I).1 _ (hb j).1 _ hy
  refine X.B.I.Lf.add_mem ?_ ?_
  · exact X.B.I.Lf.smul_mem ⟨_, (IntAf X.B.I.F X.B.I.E).mul_mem (hC i j).1 h1⟩ (hb i).1
  · exact X.B.I.Lf.smul_mem ⟨_, (IntAf X.B.I.F X.B.I.E).mul_mem (hC i j).2 h2⟩ (hb i).2

theorem one_sub_int (i j : Fin D.R.k) (C : Matrix (Fin D.R.k) (Fin D.R.k) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F))
    (hC : C i j ∈ IntAf X.B.I.F X.B.I.E) : (C - 1) i j ∈ IntAf X.B.I.F X.B.I.E := by
  rw [Matrix.sub_apply, Matrix.one_apply]
  split_ifs
  · exact sub_mem hC (one_mem _)
  · simpa using hC

theorem fmat_inv_fix (x : X.B.I.Gf) (w : VA X.B.I) (h : X.B.I.fmat x *ᵥ w = w) : X.B.I.fmat x⁻¹ *ᵥ w = w := by
  have h1 : X.B.I.fmat x⁻¹ * X.B.I.fmat x = 1 := by
    first
    | simp [Formalism.MainNotions.S.AutInst.fmat]
    | (simp only [Formalism.MainNotions.S.AutInst.fmat]
       rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one])
  calc X.B.I.fmat x⁻¹ *ᵥ w = X.B.I.fmat x⁻¹ *ᵥ (X.B.I.fmat x *ᵥ w) := by rw [h]
    _ = (X.B.I.fmat x⁻¹ * X.B.I.fmat x) *ᵥ w := by rw [Matrix.mulVec_mulVec]
    _ = w := by rw [h1, Matrix.one_mulVec]

theorem fixV_of (u : D.what₂.Word) (y : Fin X.B.I.n → X.B.I.E) (hy : y ∈ fixSet X u) :
    X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I y ∈ fixV X u := by
  rcases hy with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hz
  · rw [show X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.eR a) = incl X.B.I (X.eR a) from
      fmat_inv_fix _ _ (X.xu_fix u a).1]
    exact Or.inl (Or.inl ⟨a, rfl⟩)
  · rw [show X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.fR a) = incl X.B.I (X.fR a) from
      fmat_inv_fix _ _ (X.xu_fix u a).2]
    exact Or.inl (Or.inr ⟨a, rfl⟩)
  · rw [Set.mem_singleton_iff] at hz
    subst hz
    exact Or.inr rfl

theorem idxSurj_of (hAlg : IdxDAlg) (hAd : IdxDAd) (hI : IdxDInt) (hSig : IdxDSig) (hFr : IdxDFrame)
    (hMat : IdxDMat) (hLev : IdxDLevi) : IdxSurj := by
  intro D X Y u _ A
  obtain ⟨e, he⟩ := hAd X.B.I.F X.B.g
  obtain ⟨b, bs, hfr, hL, hperp, hcong⟩ := hFr D X u e he
  obtain ⟨C, C', hCC, hint, hres⟩ := hMat D X Y.TR e he A
  obtain ⟨hinv, hherm⟩ := hSig X.B.I
  obtain ⟨hfix, hcomp, hone, hunit⟩ :=
    hAlg _ (sigA X.B.I) X.B.I.n D.R.k (JA X.B.I) (epsX X e) b bs hinv hherm hfr
  have hCC' : C * C' = 1 := mul_eq_one_comm.mp hCC
  set σ := sigA X.B.I with hσ
  set s := sMat σ (JA X.B.I) b bs C (C'.map σ)ᵀ with hs
  set sI := sMat σ (JA X.B.I) b bs C' (C.map σ)ᵀ with hsI
  have hmapT : ∀ M N : Matrix (Fin D.R.k) (Fin D.R.k) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F), M * N = 1 →
      (N.map σ)ᵀ * (M.map σ)ᵀ = 1 := by
    intro M N hMN
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, hMN, Matrix.map_one _ (map_zero σ) (map_one σ),
      Matrix.transpose_one]
  have h1 : s * sI = 1 := by
    rw [hs, hsI, hcomp, hCC', hmapT C C' hCC']
    exact hone 1 1 (by simp) (by simp)
  have h2 : sI * s = 1 := by
    rw [hs, hsI, hcomp, hCC, hmapT C' C hCC]
    exact hone 1 1 (by simp) (by simp)
  let u0 : GL (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := ⟨s, sI, h1, h2⟩
  have hmem : u0 ∈ Formalism.UG.UPts X.B.I.cm.sig X.B.I.J (Af X.B.I.F) := hunit C C' hCC
  let s' : X.B.I.Gf := ⟨u0, hmem⟩
  have hfs : X.B.I.fmat s' = s := rfl
  have hintS : ∀ i j, (C - 1) i j ∈ IntAf X.B.I.F X.B.I.E ∧ ((C'.map σ)ᵀ - 1) i j ∈ IntAf X.B.I.F X.B.I.E :=
    fun i j => ⟨one_sub_int i j C (hint i j).1, one_sub_int i j _ ((hI X.B.I).2 _ (hint j i).2)⟩
  have hintI : ∀ i j, (C' - 1) i j ∈ IntAf X.B.I.F X.B.I.E ∧ ((C.map σ)ᵀ - 1) i j ∈ IntAf X.B.I.F X.B.I.E :=
    fun i j => ⟨one_sub_int i j C' (hint i j).2, one_sub_int i j _ ((hI X.B.I).2 _ (hint j i).1)⟩
  have hK : s' ∈ X.B.I.Kset := by
    show ∀ x, x ∈ X.B.I.Lf ↔ s *ᵥ x ∈ X.B.I.Lf
    intro x
    constructor
    · exact sMat_Lf hI b bs hL C _ hintS x
    · intro hx
      have := sMat_Lf hI b bs hL C' _ hintI _ hx
      rwa [← hsI, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec] at this
  have hfixs : ∀ w ∈ fixV X u, s *ᵥ w = w := by
    intro w hw
    exact hfix C _ w fun j => hperp j w hw
  let sF : Hfin X u := ⟨X.xu u * s' * (X.xu u)⁻¹, by
    intro y hy
    have e1 : X.B.I.fmat (X.xu u * s' * (X.xu u)⁻¹) =
        X.B.I.fmat (X.xu u) * X.B.I.fmat s' * X.B.I.fmat (X.xu u)⁻¹ := rfl
    have e2 : X.B.I.fmat (X.xu u) * X.B.I.fmat (X.xu u)⁻¹ = 1 := by
      have : X.B.I.fmat (X.xu u) * X.B.I.fmat (X.xu u)⁻¹ = X.B.I.fmat (X.xu u * (X.xu u)⁻¹) := rfl
      rw [this, mul_inv_cancel]; rfl
    rw [e1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hfs, hfixs _ (fixV_of u y hy),
      Matrix.mulVec_mulVec, e2, Matrix.one_mulVec]⟩
  have hcj : cj X u sF = s' := by
    show (X.xu u)⁻¹ * (X.xu u * s' * (X.xu u)⁻¹) * X.xu u = s'
    group
  refine ⟨sF, ?_, ?_⟩
  · rw [hcj]; exact hK
  · rw [hcj]
    funext v
    have hM : leviM Y.TR s' v = ((A v : GL (Fin D.R.k) (Y.TR.Fq v)) : Matrix (Fin D.R.k) (Fin D.R.k) (Y.TR.Fq v)) := by
      ext i j
      rw [← hres v i j]
      exact hLev D X Y.TR e he b bs hfr hL hcong C C' hCC hint v i j
    unfold levi
    split_ifs with hdet
    · ext i j
      show leviM Y.TR s' v i j = _
      rw [hM]
    · exact absurd (by rw [hM]; exact (A v).isUnit.map Matrix.detMonoidHom) hdet

end PI.UnitaryDimensionFormula
end
end

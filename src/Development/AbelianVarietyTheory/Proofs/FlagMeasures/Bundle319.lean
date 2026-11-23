module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle014
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle011
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SCompact
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.TupOfOneMemLabT
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle170
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle017
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle304
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle315
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle314
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle026
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle002
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017

@[expose] public section

section

open scoped Classical ENNReal Pointwise NNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.CovGrp
open Formalism.QuantumDeterminants Formalism.L2.SG.PoincareInHH.PoincareSetting

section Gen
variable {n k r : ℕ}

theorem coord_span_zero (Q : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ) (Qi : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ)
    (hQ1 : Qi * Q = 1) (lam : ℂ) (e : Fin r → Fin n → ℂ)
    (he : ∀ a : Fin r, Q *ᵥ Pi.single (eI k r a) 1 = lam ^ (r - (a : ℕ)) • e a)
    (c : ℕ) (y : Fin n → ℂ) (hy : y ∈ Formalism.L2.SG.HidaSetting.spanLt e c) (i : Fin (2 * r + k + 1)) (hi : c ≤ i.val) :
    (Qi *ᵥ y) i = 0 := by
  let f : (Fin n → ℂ) →ₗ[ℂ] ℂ := (LinearMap.proj i).comp (Matrix.mulVecLin Qi)
  have hle : Formalism.L2.SG.HidaSetting.spanLt e c ≤ LinearMap.ker f := by
    unfold Formalism.L2.SG.HidaSetting.spanLt
    rw [Submodule.span_le]
    rintro _ ⟨b, hb, rfl⟩
    simp only [Set.mem_setOf_eq] at hb
    have hne : lam ^ (r - (b : ℕ)) ≠ 0 := by
      intro h0
      have h1 := congrArg (fun w => Qi *ᵥ w) (he b)
      simp only [Matrix.mulVec_mulVec, hQ1, Matrix.one_mulVec, h0, zero_smul, Matrix.mulVec_zero] at h1
      have h2 := congrFun h1 (eI k r b)
      simp at h2
    have h1 := congrArg (fun w => Qi *ᵥ w) (he b)
    simp only [Matrix.mulVec_mulVec, hQ1, Matrix.one_mulVec, Matrix.mulVec_smul] at h1
    have h3 : Qi *ᵥ e b = (lam ^ (r - (b : ℕ)))⁻¹ • Pi.single (eI k r b) 1 := by
      rw [h1, smul_smul, inv_mul_cancel₀ hne, one_smul]
    show f (e b) = 0
    simp only [f, LinearMap.coe_comp, Function.comp_apply, Matrix.mulVecLin_apply, LinearMap.coe_proj,
      Function.eval, h3, Pi.smul_apply, smul_eq_mul]
    have : i ≠ eI k r b := by
      intro h; rw [h] at hi; simp [eI] at hi; omega
    simp [Pi.single_apply, this]
  exact hle hy

theorem mem_nset (J : Matrix (Fin n) (Fin n) ℂ) (Q : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ)
    (Qi : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ) (hQ1 : Qi * Q = 1) (hQ2 : Q * Qi = 1)
    (hH : Qᴴ * J * Q = Hpk k r) (lam : ℂ) (e : Fin r → Fin n → ℂ)
    (he : ∀ a : Fin r, Q *ᵥ Pi.single (eI k r a) 1 = lam ^ (r - (a : ℕ)) • e a)
    (M : Matrix (Fin n) (Fin n) ℂ) (hM : Mᴴ * J * M = J)
    (hS : ∀ a : Fin r, (M - 1) *ᵥ e a ∈ Formalism.L2.SG.HidaSetting.spanLt e a.1)
    (hX : ∀ y, (∀ a, star (e a) ⬝ᵥ (J *ᵥ y) = 0) → (M - 1) *ᵥ y ∈ Formalism.L2.SG.HidaSetting.spanLt e r) :
    Qi * M * Q ∈ Nset k r := by
  have hcol : ∀ (j i : Fin (2 * r + k + 1)), (Qi * M * Q) i j = (Qi *ᵥ (M *ᵥ (Q *ᵥ Pi.single j 1))) i := by
    intro j i
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
    rfl
  have hsplit : ∀ w : Fin n → ℂ, Qi *ᵥ (M *ᵥ w) = Qi *ᵥ w + Qi *ᵥ ((M - 1) *ᵥ w) := by
    intro w
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub]
    abel
  refine ⟨?_, ?_, ?_⟩
  · show (Qi * M * Q)ᴴ * Hpk k r * (Qi * M * Q) = Hpk k r
    have hQ2' : Qiᴴ * Qᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hQ2, Matrix.conjTranspose_one]
    rw [← hH]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    calc Qᴴ * (Mᴴ * (Qiᴴ * (Qᴴ * (J * (Q * (Qi * (M * Q)))))))
        = Qᴴ * (Mᴴ * ((Qiᴴ * Qᴴ) * (J * ((Q * Qi) * (M * Q))))) := by simp only [Matrix.mul_assoc]
      _ = Qᴴ * ((Mᴴ * J * M) * Q) := by rw [hQ2', hQ2]; simp only [Matrix.one_mul, Matrix.mul_assoc]
      _ = Qᴴ * (J * Q) := by rw [hM]
  · intro a i hai
    have hne : lam ^ (r - (a : ℕ)) ≠ 0 := by
      intro h0
      have h1 := congrArg (fun w => Qi *ᵥ w) (he a)
      simp only [Matrix.mulVec_mulVec, hQ1, Matrix.one_mulVec, h0, zero_smul, Matrix.mulVec_zero] at h1
      have h2 := congrFun h1 (eI k r a)
      simp at h2
    have h1 := congrArg (fun w => Qi *ᵥ w) (he a)
    simp only [Matrix.mulVec_mulVec, hQ1, Matrix.one_mulVec, Matrix.mulVec_smul] at h1
    have hv : Qi *ᵥ (M *ᵥ (Q *ᵥ Pi.single (eI k r a) 1)) =
        Pi.single (eI k r a) 1 + lam ^ (r - (a : ℕ)) • (Qi *ᵥ ((M - 1) *ᵥ e a)) := by
      rw [he a, Matrix.mulVec_smul, Matrix.mulVec_smul, hsplit, smul_add, ← h1]
    rw [hcol, hv, Pi.add_apply, Pi.smul_apply,
      coord_span_zero Q Qi hQ1 lam e he a.1 _ (hS a) i (by simpa [eI] using hai), smul_zero, add_zero,
      Pi.single_apply]
  · intro i j hj1 hj2 hi
    have horth : ∀ a, star (e a) ⬝ᵥ (J *ᵥ (Q *ᵥ Pi.single j 1)) = 0 := by
      intro a
      have hne : lam ^ (r - (a : ℕ)) ≠ 0 := by
        intro h0
        have h1 := congrArg (fun w => Qi *ᵥ w) (he a)
        simp only [Matrix.mulVec_mulVec, hQ1, Matrix.one_mulVec, h0, zero_smul, Matrix.mulVec_zero] at h1
        have h2 := congrFun h1 (eI k r a)
        simp at h2
      have key : star (Q *ᵥ Pi.single (eI k r a) 1) ⬝ᵥ (J *ᵥ (Q *ᵥ Pi.single j 1)) = 0 := by
        rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hH]
        have hz : Hpk k r (eI k r a) j = 0 := by
          have ha := a.isLt
          unfold Hpk
          simp only [eI, Fin.ext_iff]
          split_ifs <;> first | rfl | (exfalso; omega)
        simp [Matrix.mulVec, dotProduct, Pi.single_apply, hz]
      rw [he a, star_smul, smul_dotProduct] at key
      exact (smul_eq_zero.1 key).resolve_left (by simpa using hne)
    rw [hcol, hsplit, Pi.add_apply, coord_span_zero Q Qi hQ1 lam e he r _ (hX _ horth) i hi, add_zero,
      Matrix.mulVec_mulVec, hQ1, Matrix.one_mulVec]
    simp [Pi.single_apply]

end Gen

section Main
open GlobalTheory.TypeAsm

theorem trI_one {D : D7} {X : HidaSetting D} (C : Choice X 1) : trI C 1 = fun _ => Matrix.of.symm 1 := by
  funext τ
  show Matrix.of.symm (C.Qi τ * Formalism.MainNotions.S.uMat ((1 : X.B.I.Ginf) (vOf X τ)) * C.Q τ) = Matrix.of.symm 1
  have hu : Formalism.MainNotions.S.uMat ((1 : X.B.I.Ginf) (vOf X τ)) = 1 := rfl
  rw [hu, Matrix.mul_one, (C.isT τ).1]

theorem trI_mul {D : D7} {X : HidaSetting D} (C : Choice X 1) (s t : X.B.I.Ginf) :
    trI C (s * t) = GlobalTheory.DegVol.mulP (trI C s) (trI C t) := by
  funext τ
  have h2 := (C.isT τ).2.1
  have e : C.Qi τ * Formalism.MainNotions.S.uMat ((s * t) (vOf X τ)) * C.Q τ =
      (C.Qi τ * Formalism.MainNotions.S.uMat (s (vOf X τ)) * C.Q τ) * (C.Qi τ * Formalism.MainNotions.S.uMat (t (vOf X τ)) * C.Q τ) := by
    have : Formalism.MainNotions.S.uMat ((s * t) (vOf X τ)) = Formalism.MainNotions.S.uMat (s (vOf X τ)) * Formalism.MainNotions.S.uMat (t (vOf X τ)) := by
      simp [Formalism.MainNotions.S.uMat]
    rw [this]
    calc C.Qi τ * (Formalism.MainNotions.S.uMat (s (vOf X τ)) * Formalism.MainNotions.S.uMat (t (vOf X τ))) * C.Q τ
        = C.Qi τ * Formalism.MainNotions.S.uMat (s (vOf X τ)) * (C.Q τ * C.Qi τ) * Formalism.MainNotions.S.uMat (t (vOf X τ)) * C.Q τ := by
          rw [h2]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  simp only [trI, GlobalTheory.DegVol.mulP, Formalism.QuantumDeterminants.lmulM, Formalism.L2.SG.RealObj.trG, Equiv.apply_symm_apply]
  rw [e]
  rfl

theorem trI_inv {D : D7} {X : HidaSetting D} (C : Choice X 1) (s : X.B.I.Ginf) :
    (fun τ => Matrix.of.symm (Matrix.of (trI C s τ))⁻¹) = trI C s⁻¹ := by
  funext τ
  have h1 := (C.isT τ).1
  have h2 := (C.isT τ).2.1
  simp only [trI, Equiv.apply_symm_apply, Formalism.L2.SG.RealObj.trG]
  congr 1
  apply Matrix.inv_eq_right_inv
  have hu : Formalism.MainNotions.S.uMat (s (vOf X τ)) * Formalism.MainNotions.S.uMat (s⁻¹ (vOf X τ)) = 1 := by
    simp [Formalism.MainNotions.S.uMat]
  calc C.Qi τ * Formalism.MainNotions.S.uMat (s (vOf X τ)) * C.Q τ * (C.Qi τ * Formalism.MainNotions.S.uMat (s⁻¹ (vOf X τ)) * C.Q τ)
      = C.Qi τ * Formalism.MainNotions.S.uMat (s (vOf X τ)) * (C.Q τ * C.Qi τ) * Formalism.MainNotions.S.uMat (s⁻¹ (vOf X τ)) * C.Q τ := by
        simp only [Matrix.mul_assoc]
    _ = C.Qi τ * C.Q τ := by
        rw [h2, Matrix.mul_one, Matrix.mul_assoc (C.Qi τ), hu, Matrix.mul_one]
    _ = 1 := h1

theorem cov_grp : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (C : Choice X 1),
    (trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u).Countable ∧
    (fun _ => Matrix.of.symm 1) ∈ trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u ∧
    (∀ m ∈ trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u, ∀ m' ∈ trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u,
      GlobalTheory.DegVol.mulP m m' ∈ trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u) ∧
    (∀ m ∈ trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u,
      (fun τ => Matrix.of.symm (Matrix.of (m τ))⁻¹) ∈ trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u) ∧
    ∀ m ∈ trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u, ∀ τ, Matrix.of (m τ) ∈ Formalism.QuantumDeterminants.Nset D.R.k D.R.rS := by
  intro D X Y u C
  have hS := Formalism.L2.SG.Pf.NOsub_coe X u Y.hK
  have mem : ∀ s, s ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u ↔ s ∈ Formalism.L2.SG.Pf.NOsub X u Y.hK := by
    intro s; rw [← hS]; rfl
  refine ⟨(Formalism.L2.SG.Pf.noCount_holds X u).image _, ⟨1, (mem 1).2 (Subgroup.one_mem _), trI_one C⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    exact ⟨s * t, (mem _).2 (Subgroup.mul_mem _ ((mem _).1 hs) ((mem _).1 ht)), trI_mul C s t⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact ⟨s⁻¹, (mem _).2 (Subgroup.inv_mem _ ((mem _).1 hs)), (trI_inv C s).symm⟩
  · rintro _ ⟨s, hs, rfl⟩ τ
    obtain ⟨γ, -, hγ1, hγN, -⟩ := hs
    have hN : s ∈ X.NinfU u := hγ1 ▸ hγN
    have hNv := hN (vOf X τ)
    obtain ⟨hQ1, hQ2, hH, he⟩ := C.isT τ
    simp only [trI, Equiv.apply_symm_apply, Formalism.L2.SG.RealObj.trG]
    exact mem_nset (Formalism.REAL.Jm (X.B.I.ε (vOf X τ))) (C.Q τ) (C.Qi τ) hQ1 hQ2 hH (frS D) _
      (fun a => (he a a rfl).1) _ (s (vOf X τ)).2 hNv.1.1 hNv.2

end Main

end GlobalTheory.CovGrp
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

namespace GlobalTheory.LabIdem

theorem ES_single_coeff_central : ∀ (D : D7) (t : Tup2 D), (∀ k v, IsLabel D k (t k v)) →
    (∀ γ, (ES {t}).coeff γ = serCoef t γ) ∧ ∀ b, ES {t} * b = b * ES {t} := by
  intro D t _
  have e : (ES {t} : MonoidAlgebra ℂ (G0g D.nd)) = GlobalTheory.RowLev.zTup D t := GlobalTheory.RowLev.ES_singleton (D := D) t
  refine ⟨fun γ => ?_, fun b => ?_⟩
  · rw [e]; rfl
  · rw [e]; exact GlobalTheory.RowLev.zTup_comm t b

end GlobalTheory.LabIdem
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

noncomputable section

namespace GlobalTheory.LabFix

section Gen

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem rt_mul (a b : GAf L n) (f : GAf L n → ℂ) :
    Formalism.L2.NG.rt L n (a * b) f = Formalism.L2.NG.rt L n a (Formalism.L2.NG.rt L n b f) := by
  funext g
  show f (g * (a * b)) = f (g * a * b)
  rw [mul_assoc]

theorem rt_one (f : GAf L n → ℂ) : Formalism.L2.NG.rt L n 1 f = f := by
  funext g
  show f (g * 1) = f g
  rw [mul_one]

theorem exists_lifts (n : ℕ) (s : SplitPlace L) (g : ℕ) (hg : g.Prime) :
    ∃ ℓ : GL (Fin n) (ZMod g) → GAf L n, ∀ γ, IsLift s (ℓ γ) γ := by
  classical
  haveI : Fact g.Prime := ⟨hg⟩
  have key : ∀ γ : GL (Fin n) (ZMod g), ∃ x : GAf L n, IsLift s x γ := by
    intro γ
    let A : Matrix (Fin n) (Fin n) ℤ := fun i j => (((γ : Matrix (Fin n) (Fin n) (ZMod g)) i j).val : ℤ)
    have hA : (Int.castRingHom (ZMod g)).mapMatrix A = (γ : Matrix (Fin n) (Fin n) (ZMod g)) := by
      ext i j
      show ((((γ : Matrix (Fin n) (Fin n) (ZMod g)) i j).val : ℤ) : ZMod g) = _
      rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    have hdet : A.det ≠ 0 := by
      intro h0
      have h1 := congrArg (Int.castRingHom (ZMod g)) h0
      rw [RingHom.map_det, hA, map_zero] at h1
      exact (Matrix.isUnits_det_units γ).ne_zero h1
    let B : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) :=
      (Int.castRingHom (s.v.adicCompletion (maximalRealSubfield L))).mapMatrix A
    have hB : IsUnit B.det := by
      rw [isUnit_iff_ne_zero, ← RingHom.map_det, eq_intCast]
      exact Int.cast_ne_zero.mpr hdet
    obtain ⟨x, hx, hloc⟩ := GlobalTheory.T.exists_adelicUnitary_trivialOutside_splitPlace_loc_eq n s (Matrix.nonsingInvUnit B hB)
    refine ⟨x, hx, fun i j => ?_⟩
    have hij : (s.loc n x : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j =
        ((((γ : Matrix (Fin n) (Fin n) (ZMod g)) i j).val : ℕ) : s.v.adicCompletion (maximalRealSubfield L)) := by
      rw [hloc]
      show (Int.castRingHom (s.v.adicCompletion (maximalRealSubfield L))) (A i j) = _
      rw [eq_intCast]
      exact Int.cast_natCast _
    rw [hij, sub_self, map_zero]
    exact zero_lt_one
  choose ℓ hℓ using key
  exact ⟨ℓ, hℓ⟩

end Gen

theorem sum_serCoef_rt : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : Formalism.L2.Theta.GA D (D.sp.Y 0)) (PY : RowPsi (Yc D 0) D.R.r) (c : GAf D.host.E D.R.r) (red : X.B.I.Gf → G0g D.nd) (sec : G0g D.nd → X.B.I.Gf) (lf : G0g D.nd → GAf D.host.E D.R.r), FrameRed X h t PY c red → IsSec X red sec → (∀ γ, PY.ψ (lf γ) = kap X h t (sec γ)) → ∀ (π : Formalism.L2.NG.FinTyp D.host.E D.R.r) (τ : Tup2 D), HasTuple D π τ → ∀ φ ∈ π.S, (∀ k ∈ X.B.I.Kg X.B.g, ∀ κ, PY.ψ κ = kap X h t k → Formalism.L2.NG.rt D.host.E D.R.r κ φ = φ) → ∑ᶠ γ, serCoef τ γ • Formalism.L2.NG.rt D.host.E D.R.r (lf γ) φ = φ := by
  intro D X h t PY c red sec lf hFR hsec hlf π τ hτ φ hφ hfix
  classical
  obtain ⟨hred, hex, hlift⟩ := hFR
  obtain ⟨-, hmul, -, hker⟩ := hred
  haveI : ∀ k : Fin 2, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  have kap_mul : ∀ k k' : X.B.I.Gf, kap X h t (k * k') = kap X h t k * kap X h t k' := by
    intro k k'
    have e : ((1, k * k') : X.B.I.GA) = (1, k) * (1, k') := by rw [Prod.mk_mul_mk, one_mul]
    have cm : ∀ a b : Formalism.L2.Theta.GA D (D.sp.Y 0), t⁻¹ * (a * b) * t = t⁻¹ * a * t * (t⁻¹ * b * t) := by
      intro a b; group
    unfold kap
    rw [e, map_mul]
    exact cm _ _
  have kap_inv : ∀ k : X.B.I.Gf, kap X h t k⁻¹ = (kap X h t k)⁻¹ := by
    intro k
    have e : ((1, k⁻¹) : X.B.I.GA) = (1, k)⁻¹ := by rw [Prod.inv_mk, inv_one]
    have ci : ∀ a : Formalism.L2.Theta.GA D (D.sp.Y 0), t⁻¹ * a⁻¹ * t = (t⁻¹ * a * t)⁻¹ := by
      intro a; group
    unfold kap
    rw [e, map_inv]
    exact ci _
  have K_one : (1 : X.B.I.Gf) ∈ X.B.I.Kset := by
    simp only [Formalism.MainNotions.S.AutInst.Kset, Set.mem_setOf_eq, OneMemClass.coe_one]
    exact one_mem _
  have K_mul : ∀ a b : X.B.I.Gf, a ∈ X.B.I.Kset → b ∈ X.B.I.Kset → a * b ∈ X.B.I.Kset := by
    intro a b ha hb
    simp only [Formalism.MainNotions.S.AutInst.Kset, Set.mem_setOf_eq, Subgroup.coe_mul] at *
    exact mul_mem ha hb
  have K_inv : ∀ a : X.B.I.Gf, a ∈ X.B.I.Kset → a⁻¹ ∈ X.B.I.Kset := by
    intro a ha
    simp only [Formalism.MainNotions.S.AutInst.Kset, Set.mem_setOf_eq, InvMemClass.coe_inv] at *
    exact inv_mem ha
  have red_one : red 1 = 1 := by
    have e := hmul 1 K_one 1 K_one
    rw [one_mul] at e
    exact mul_left_cancel (e.symm.trans (mul_one _).symm)
  have red_inv : ∀ k ∈ X.B.I.Kset, red k⁻¹ = (red k)⁻¹ := by
    intro k hk
    have e := hmul k⁻¹ (K_inv k hk) k hk
    rw [inv_mul_cancel, red_one] at e
    exact eq_inv_of_mul_eq_one_left e.symm
  have key : ∀ (γ : G0g D.nd) (y : GAf D.host.E D.R.r) (k : X.B.I.Gf), k ∈ X.B.I.Kset → red k = γ →
      PY.ψ y = kap X h t k → Formalism.L2.NG.rt D.host.E D.R.r y φ = Formalism.L2.NG.rt D.host.E D.R.r (lf γ) φ := by
    intro γ y k hk hrk hy
    obtain ⟨hs1, hs2⟩ := hsec γ
    have hm : (sec γ)⁻¹ * k ∈ X.B.I.Kg X.B.g := by
      refine (hker _ (K_mul _ _ (K_inv _ hs1) hk)).1 ?_
      rw [hmul _ (K_inv _ hs1) _ hk, red_inv _ hs1, hs2, hrk, inv_mul_cancel]
    have hψ : PY.ψ ((lf γ)⁻¹ * y) = kap X h t ((sec γ)⁻¹ * k) := by
      rw [map_mul, map_inv, hlf, hy, kap_mul, kap_inv]
    have e := hfix _ hm _ hψ
    calc Formalism.L2.NG.rt D.host.E D.R.r y φ
        = Formalism.L2.NG.rt D.host.E D.R.r (lf γ * ((lf γ)⁻¹ * y)) φ := by rw [mul_inv_cancel_left]
      _ = Formalism.L2.NG.rt D.host.E D.R.r (lf γ) (Formalism.L2.NG.rt D.host.E D.R.r ((lf γ)⁻¹ * y) φ) := rt_mul _ _ _
      _ = Formalism.L2.NG.rt D.host.E D.R.r (lf γ) φ := by rw [e]
  set φ' := Formalism.L2.NG.rt D.host.E D.R.r c⁻¹ φ with hφ'
  have hφ'S : φ' ∈ π.S := π.stable _ _ hφ
  have back : Formalism.L2.NG.rt D.host.E D.R.r c φ' = φ := by
    rw [hφ', ← rt_mul, mul_inv_cancel, rt_one]
  have fix1 : ∀ (kv : (Σ k : Fin 2, D.nd.PlG k)) (s : SplitPlace D.host.E), s.w = D.naut.plGw kv.1 kv.2 →
      ∀ x, IsLift s x (1 : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) → Formalism.L2.NG.rt D.host.E D.R.r x φ' = φ' := by
    intro kv s hs x hx
    obtain ⟨k, hk, hψ, hr1, hr2⟩ := hlift kv s hs x 1 hx
    have hrk : red k = 1 := by
      funext kv'
      rw [Pi.one_apply]
      by_cases e : kv' = kv
      · subst e; exact hr1
      · exact hr2 kv' e
    have e := hfix k ((hker k hk).1 hrk) _ hψ
    calc Formalism.L2.NG.rt D.host.E D.R.r x φ'
        = Formalism.L2.NG.rt D.host.E D.R.r c⁻¹ (Formalism.L2.NG.rt D.host.E D.R.r (c * x * c⁻¹) φ) := by
          rw [hφ', ← rt_mul, ← rt_mul]; congr 1; group
      _ = φ' := by rw [e]
  have step : ∀ (kv : (Σ k : Fin 2, D.nd.PlG k)) (γ : G0g D.nd), γ kv = 1 →
      ∑ β : GL (Fin D.R.r) (ZMod (D.host.g kv.1)), (D.ntypes.eSer kv.1 (τ kv.1 kv.2)).coeff β •
        Formalism.L2.NG.rt D.host.E D.R.r (lf (Function.update γ kv β)) φ = Formalism.L2.NG.rt D.host.E D.R.r (lf γ) φ := by
    intro kv γ hγ
    obtain ⟨s, hs⟩ := hex kv
    obtain ⟨ℓ, hℓ⟩ := exists_lifts D.R.r s (D.host.g kv.1) (D.host.g_prime kv.1)
    have hser := ((hτ kv.1 kv.2).2 s hs) ℓ hℓ φ' hφ'S (fix1 kv s hs)
    rw [finsum_eq_sum_of_fintype] at hser
    have hterm : ∀ β, Formalism.L2.NG.rt D.host.E D.R.r (lf (Function.update γ kv β)) φ =
        Formalism.L2.NG.rt D.host.E D.R.r (lf γ) (Formalism.L2.NG.rt D.host.E D.R.r c (Formalism.L2.NG.rt D.host.E D.R.r (ℓ β) φ')) := by
      intro β
      obtain ⟨k, hk, hψ, hr1, hr2⟩ := hlift kv s hs (ℓ β) β (hℓ β)
      obtain ⟨hs1, hs2⟩ := hsec γ
      have hred : red (sec γ * k) = Function.update γ kv β := by
        rw [hmul _ hs1 _ hk, hs2]
        funext kv'
        by_cases e : kv' = kv
        · subst e; simp [hγ, hr1]
        · simp [Function.update_of_ne e, hr2 kv' e]
      have e := key _ (lf γ * (c * ℓ β * c⁻¹)) (sec γ * k) (K_mul _ _ hs1 hk) hred
        (by rw [map_mul, hlf, hψ, kap_mul])
      rw [← e, hφ', ← rt_mul, ← rt_mul, ← rt_mul]
      congr 1
      group
    calc ∑ β : GL (Fin D.R.r) (ZMod (D.host.g kv.1)), (D.ntypes.eSer kv.1 (τ kv.1 kv.2)).coeff β •
          Formalism.L2.NG.rt D.host.E D.R.r (lf (Function.update γ kv β)) φ
        = ∑ β : GL (Fin D.R.r) (ZMod (D.host.g kv.1)), (D.ntypes.eSer kv.1 (τ kv.1 kv.2)).coeff β •
          Formalism.L2.NG.rt D.host.E D.R.r (lf γ) (Formalism.L2.NG.rt D.host.E D.R.r c (Formalism.L2.NG.rt D.host.E D.R.r (ℓ β) φ')) :=
          Finset.sum_congr rfl fun β _ => by rw [hterm]
      _ = Formalism.L2.NG.rt D.host.E D.R.r (lf γ) (Formalism.L2.NG.rt D.host.E D.R.r c
          (∑ β, (D.ntypes.eSer kv.1 (τ kv.1 kv.2)).coeff β • Formalism.L2.NG.rt D.host.E D.R.r (ℓ β) φ')) := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [map_sum, map_smul]
      _ = Formalism.L2.NG.rt D.host.E D.R.r (lf γ) φ := by rw [hser, back]
  have hfin := GlobalTheory.T.sum_prod_fixed_place_average_alt (ι := Σ k : Fin 2, D.nd.PlG k) (G := fun kv => GL (Fin D.R.r) (ZMod (D.host.g kv.1)))
    (fun kv β => (D.ntypes.eSer kv.1 (τ kv.1 kv.2)).coeff β) (fun γ => Formalism.L2.NG.rt D.host.E D.R.r (lf γ) φ) step
  have h1 : Formalism.L2.NG.rt D.host.E D.R.r (lf 1) φ = φ :=
    hfix (sec 1) ((hker _ (hsec 1).1).1 ((hsec 1).2)) _ (hlf 1)
  letI : Fintype (G0g D.nd) := Pi.instFintype
  rw [finsum_eq_sum_of_fintype]
  exact hfin.trans h1

end GlobalTheory.LabFix

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

namespace GlobalTheory.SplitPlaceOfFixed

theorem exists_splitPlace_plGw : ∀ (D : D7) (kv : Σ k : Fin 2, D.nd.PlG k), ∃ s : ReciprocityTheory.Aut.SplitPlace D.host.E, s.w = D.naut.plGw kv.1 kv.2 := by
  intro D kv
  obtain ⟨s, -, h, -⟩ := GlobalTheory.SplitConjPlace.splitEx_all D _ (GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D kv.1 kv.2)
  refine ⟨GlobalTheory.SplitConjPlace.conjSP s, IsDedekindDomain.HeightOneSpectrum.ext (Ideal.ext fun x => ?_)⟩
  have hm : x ∈ (GlobalTheory.SplitConjPlace.conjSP s).w.asIdeal ↔
      IsCMField.ringOfIntegersComplexConj D.host.E x ∈ s.w.asIdeal := by
    show Valued.v ((GlobalTheory.SplitConjPlace.conjSP s).i (x : D.host.E)) < 1 ↔
      Valued.v (s.i ((IsCMField.ringOfIntegersComplexConj D.host.E x : 𝓞 D.host.E) : D.host.E)) < 1
    rw [IsCMField.coe_ringOfIntegersComplexConj]
    rfl
  rw [hm]
  refine (h x _ ?_).symm
  rw [IsCMField.coe_ringOfIntegersComplexConj]
  exact D.host.φ₀.injective (by
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])

end GlobalTheory.SplitPlaceOfFixed
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

theorem _root_.GlobalTheory.T.convolution_range_cuspidal_of_lowestKType : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v)) (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) → (∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) → LocDec B h → HBig B 40 h → FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re) → ∀ T, B.I.IsRConv B.μf B.fund B.R (phe B d) T → ∀ y : B.I.L2 B.μf B.fund, (∀ f : B.I.GA → ℂ, IsContRep B (T y) f → ∀ W, B.I.IsIsot W → ∀ ν : Measure B.I.GA, B.I.IsNQuotMeas W ν → ∀ x, ∫ m, f (m * x) ∂ν = 0) ∧ B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext (T y)) := by
  first | exact @GlobalTheory.Dec.range_cuspidal_of_lowKType | exact GlobalTheory.Dec.range_cuspidal_of_lowKType | (intros; apply GlobalTheory.Dec.range_cuspidal_of_lowKType <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped ENNReal

theorem _root_.GlobalTheory.T.besselUnitary_haar_transport_diagonal : ∀ (k r : ℕ) (μG : Measure (Mt k r)) (ε : Fin (2 * r + k + 1) → Bool) (P : Mat k r), IsHaarOn (GG k r) μG → IsUnit P.det → Pᴴ * Formalism.REAL.Jm ε * P = Hpk k r → ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ φ : Mt k r → ℝ≥0∞, Measurable φ → ∫⁻ y, φ (Matrix.of.symm (P⁻¹ * umat y * P)) ∂(Formalism.REAL.muG ε) = c * ∫⁻ x, φ x ∂μG := by
  first | exact @GlobalTheory.HaarTransport.haar_transport | exact GlobalTheory.HaarTransport.haar_transport | (intros; apply GlobalTheory.HaarTransport.haar_transport <;> assumption)
end

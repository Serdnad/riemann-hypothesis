module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle167
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryPointsDiscreteFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle201
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle184
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordOfMemXa
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummary
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicStabilizerRadicalStructure
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LebesgueCommonStabilizerEqRadicalLeviMap
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle212
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle002
public import Formalism.LocalToGlobal.Divisibility.DivisionCompatibleToSub2Indef2
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermDef
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle213
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle004
public import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle214
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle154
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

namespace GlobalTheory.StabUnfold

theorem exists_stab_emb_baseChange {E R : Type} [Field E] [StarRing E] [CommRing R] (φ : E →+* R)
    (σ : R →+* R) (hσ : ∀ a, σ (φ a) = φ (star a)) {n m : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (J' : Matrix (Fin m) (Fin m) E) (x : Fin n → E) (A : Matrix (Fin n) (Fin m) E)
    (hn : m + 1 = n) (hJ : Jᴴ = J) (hd : J'.det ≠ 0) (hx : star x ⬝ᵥ (J *ᵥ x) ≠ 0)
    (hxA : star x ᵥ* (J * A) = 0) (hA : Aᴴ * J * A = J') :
    ∃ j : Formalism.UG.UJ σ (J'.map φ) →* Formalism.UG.UJ σ (J.map φ),
      (∀ g, ((j g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ (fun i => φ (x i)) = (fun i => φ (x i)) ∧
        ((j g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * A.map φ =
          A.map φ * ((g : GL (Fin m) R) : Matrix (Fin m) (Fin m) R)) ∧
      ∀ h : Formalism.UG.UJ σ (J.map φ),
        ((h : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ (fun i => φ (x i)) = (fun i => φ (x i)) →
          h ∈ j.range := by
  obtain ⟨u, A', h1, h2, h3, h4, h5, h6⟩ := exists_dual_of_anisotropic_orthogonal E n m J J' x A hn hJ hd hx hxA hA
  have hsx : (fun i => σ (φ (x i))) = φ ∘ star x := by
    funext i; simp [hσ]
  have hcT : Formalism.UG.cT σ (A.map φ) = (Aᴴ).map φ := by
    ext i j; simp [Formalism.UG.cT, hσ]
  have mv : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) E) (v : Fin b → E),
      M.map φ *ᵥ (φ ∘ v) = φ ∘ (M *ᵥ v) := by
    intro a b M v; funext i; exact (RingHom.map_mulVec φ M v i).symm
  have vm : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) E) (v : Fin a → E),
      (φ ∘ v) ᵥ* M.map φ = φ ∘ (v ᵥ* M) := by
    intro a b M v; funext i; exact (RingHom.map_vecMul φ M v i).symm
  have z : ∀ {a : ℕ}, φ ∘ (0 : Fin a → E) = 0 := by
    intro a; funext i; simp
  have k1 : A'.map φ * A.map φ = 1 := by
    rw [← Matrix.map_mul, h1, Matrix.map_one φ (map_zero φ) (map_one φ)]
  have k2 : A'.map φ *ᵥ (φ ∘ x) = 0 := by rw [mv, h2, z]
  have k3 : (φ ∘ u) ᵥ* A.map φ = 0 := by rw [vm, h3, z]
  have k4 : (φ ∘ u) ⬝ᵥ (φ ∘ x) = 1 := by rw [← RingHom.map_dotProduct, h4, map_one]
  have k5 : vecMulVec (φ ∘ x) (φ ∘ u) + A.map φ * A'.map φ = 1 := by
    rw [← Matrix.map_one φ (map_zero φ) (map_one φ), ← h5, ← Matrix.map_mul]
    ext i j; simp [vecMulVec_apply, Matrix.mul_apply]
  obtain ⟨j, hj, hr⟩ := GlobalTheory.T.exists_unitary_orthogonal_embedding_stabilizer R σ n m (J.map φ) (J'.map φ) (φ ∘ x) (φ ∘ u) (A.map φ) (A'.map φ)
    (by
      change IsUnit ((fun i => σ (φ (x i))) ⬝ᵥ _)
      rw [hsx, mv, ← RingHom.map_dotProduct]
      exact (IsUnit.mk0 _ hx).map φ)
    (by
      change (fun i => σ (φ (x i))) ᵥ* _ = 0
      rw [hsx, ← Matrix.map_mul, vm, hxA, z])
    (by rw [hcT, mv, mv, h6, z])
    (by rw [hcT, ← Matrix.map_mul, ← Matrix.map_mul, hA])
    k1 k2 k3 k4 k5
  refine ⟨j, fun g => ⟨?_, ?_⟩, hr⟩
  · change _ *ᵥ (φ ∘ x) = φ ∘ x
    rw [hj, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, k2, Matrix.mulVec_zero, add_zero,
      Matrix.vecMulVec_mulVec, k4]
    simp
  · rw [hj, Matrix.add_mul, Matrix.mul_assoc, k1, Matrix.mul_one, Matrix.vecMulVec_mul, k3]
    ext a b; simp [vecMulVec_apply]

theorem exists_finEmb : ∀ (I : AutInst) (D : Sib I) (s : Bool) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin D.n) I.E) (xf : I.Gf), IsPerp D s x A xf → ∃ jf : D.inst.Gf →* I.Gf, IsFinEmb D x A jf ∧ ∀ h : I.Gf, I.fmat h *ᵥ afVec I x = afVec I x → h ∈ jf.range := by
  intro I D s x A xf h
  obtain ⟨hn, hx, hxA, hA, -, -⟩ := h
  have hσ : ∀ a : I.E, Formalism.UG.sigR I.cm.sig (Af I.F) (Formalism.UG.inclE (F := I.F) (Af I.F) a) =
      Formalism.UG.inclE (F := I.F) (Af I.F) (star a) := by
    intro a
    have : I.cm.sig a = star a := rfl
    simp [Formalism.UG.sigR, Formalism.UG.inclE, this]
  have hx' : star x ⬝ᵥ (I.J *ᵥ x) ≠ 0 := by
    rw [hx]; cases s <;> simp [sgn]
  exact exists_stab_emb_baseChange (Formalism.UG.inclE (F := I.F) (Af I.F)) (Formalism.UG.sigR I.cm.sig (Af I.F)) hσ
    I.J D.J x A hn I.J_herm D.J_det hx' hxA hA

end GlobalTheory.StabUnfold
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

namespace GlobalTheory.StabUnfold.RatPts

open GlobalTheory.RatDiscrete

theorem eq_map_of_resolution {E R : Type} [CommRing E] [CommRing R] (ι : E →+* R) {n m : ℕ}
    {x u : Fin n → E} {A : Matrix (Fin n) (Fin m) E} {A' : Matrix (Fin m) (Fin n) E}
    (h : vecMulVec x u + A * A' = 1) (M : Matrix (Fin n) (Fin n) R) (g : Matrix (Fin m) (Fin m) E)
    (hx : M *ᵥ (fun i => ι (x i)) = fun i => ι (x i)) (hA : M * A.map ι = A.map ι * g.map ι) :
    M = (vecMulVec x u + A * g * A').map ι := by
  have h1 : (vecMulVec x u + A * A').map ι = 1 := by
    rw [h]; exact Matrix.map_one ι (map_zero ι) (map_one ι)
  have hvm : ∀ y w : Fin n → E, (vecMulVec y w).map ι = vecMulVec (fun i => ι (y i)) (fun i => ι (w i)) := by
    intro y w; ext i j; simp [vecMulVec_apply]
  have key : M * vecMulVec (fun i => ι (x i)) (fun i => ι (u i)) =
      vecMulVec (fun i => ι (x i)) (fun i => ι (u i)) := by
    ext i j
    have hi := congrFun hx i
    simp only [mulVec, dotProduct] at hi
    change (∑ k, M i k * (ι (x k) * ι (u j))) = ι (x i) * ι (u j)
    rw [← hi, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => (mul_assoc (M i k) (ι (x k)) (ι (u j))).symm
  calc M = M * (vecMulVec x u + A * A').map ι := by rw [h1, Matrix.mul_one]
    _ = (vecMulVec x u + A * g * A').map ι := by
      rw [Matrix.map_add _ (map_add ι), Matrix.map_add _ (map_add ι), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, hvm,
        Matrix.mul_add, key, ← Matrix.mul_assoc, hA]

theorem exists_isImage (I : AutInst) (γ : GL (Fin I.n) I.E)
    (hγ : γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J) : ∃ a : I.GA, IsImage I γ a := by
  have hU : Formalism.UG.cT (starRingEnd I.E) (γ : Matrix (Fin I.n) (Fin I.n) I.E) * I.J *
      (γ : Matrix (Fin I.n) (Fin I.n) I.E) = I.J := hγ
  have hG : ∀ v, ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v))ᴴ * I.J.map (I.φ v) *
      (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) = I.J.map (I.φ v) := by
    intro v
    have h2 := congrArg (fun M : Matrix (Fin I.n) (Fin I.n) I.E => M.map (I.φ v)) hU
    simp only [Matrix.map_mul] at h2
    convert h2 using 3
    ext i j
    simp [Formalism.UG.cT, Matrix.conjTranspose_apply]
    exact (I.cm.cmUnram.2.1 (I.φ v) _).symm
  have hR : ∀ v, Formalism.REAL.inUJ (I.ε v)
      ((I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) := by
    intro v
    have hd := (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)
    have hdH : IsUnit (I.P v)ᴴ.det := by rw [Matrix.det_conjTranspose]; exact hd.star
    unfold Formalism.REAL.inUJ
    rw [← I.P_spec v]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((I.P v)ᴴ)⁻¹ (I.P v)ᴴ, Matrix.nonsing_inv_mul _ hdH, Matrix.one_mul,
      ← Matrix.mul_assoc (I.P v) (I.P v)⁻¹, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul]
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hG v]
  have hC : ∀ v (X Y : Matrix (Fin I.n) (Fin I.n) ℂ),
      ((I.P v)⁻¹ * X * I.P v) * ((I.P v)⁻¹ * Y * I.P v) = (I.P v)⁻¹ * (X * Y) * I.P v := by
    intro v X Y
    have hd := (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (I.P v) (I.P v)⁻¹, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul]
  have hE : ∀ v (X : Matrix (Fin I.n) (Fin I.n) I.E) (Y : Matrix (Fin I.n) (Fin I.n) I.E), X * Y = 1 →
      ((I.P v)⁻¹ * X.map (I.φ v) * I.P v) * ((I.P v)⁻¹ * Y.map (I.φ v) * I.P v) = 1 := by
    intro v X Y hXY
    have hd := (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)
    rw [hC, ← Matrix.map_mul, hXY, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
      Matrix.nonsing_inv_mul _ hd]
  let ι := Formalism.UG.inclE (F := I.F) (E := I.E) (Af I.F)
  have hF : Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map ι) *
      I.J.map ι * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map ι = I.J.map ι := by
    have h2 := congrArg (fun M : Matrix (Fin I.n) (Fin I.n) I.E => M.map ι) hU
    simp only [Matrix.map_mul] at h2
    convert h2 using 3
    ext i j
    simp [ι, Formalism.UG.cT, Formalism.UG.sigR, Formalism.UG.inclE]
    rfl
  let af : GL (Fin I.n) (I.E ⊗[I.F] Af I.F) := Units.map (RingHom.mapMatrix ι).toMonoidHom γ
  have haf : af ∈ Formalism.UG.UPts I.cm.sig I.J (Af I.F) := by
    unfold Formalism.UG.UPts
    exact hF
  refine ⟨(fun v => ⟨⟨(I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v,
      (I.P v)⁻¹ * ((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v,
      hE v _ _ (Units.mul_inv γ), hE v _ _ (Units.inv_mul γ)⟩, hR v⟩, ⟨af, haf⟩), fun v => rfl, rfl⟩

theorem isImage_embA {I : AutInst} (D : Sib I) {x u : Fin I.n → I.E} {A : Matrix (Fin I.n) (Fin D.n) I.E}
    {A' : Matrix (Fin D.n) (Fin I.n) I.E} (h : vecMulVec x u + A * A' = 1)
    {jv : ∀ v, Formalism.REAL.UJ (D.ε v) →* Formalism.REAL.UJ (I.ε v)} {jf : D.inst.Gf →* I.Gf}
    (hv : IsInfEmb D x A jv) (hf : IsFinEmb D x A jf) {γ : Matrix (Fin D.n) (Fin D.n) I.E} {g : D.inst.GA}
    (hg : IsImage D.inst γ g) : IsImage I (vecMulVec x u + A * γ * A') (embA D jv jf g) := by
  obtain ⟨hg1, hg2⟩ := hg
  refine ⟨fun v => ?_, ?_⟩
  · have hPu := (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)
    have hDu := (Matrix.isUnit_iff_isUnit_det _).mp (D.P_unit v)
    obtain ⟨h1, h2⟩ := hv v (g.1 v)
    have hxv : (I.P v * uMat (jv v (g.1 v)) * (I.P v)⁻¹) *ᵥ (fun i => I.φ v (x i)) =
        fun i => I.φ v (x i) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      change I.P v *ᵥ (uMat (jv v (g.1 v)) *ᵥ infVec I v x) = _
      rw [h1, infVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hPu, Matrix.one_mulVec]
    have key : I.P v * uMat (jv v (g.1 v)) * (I.P v)⁻¹ * A.map (I.φ v) * D.P v =
        A.map (I.φ v) * γ.map (I.φ v) * D.P v := by
      calc I.P v * uMat (jv v (g.1 v)) * (I.P v)⁻¹ * A.map (I.φ v) * D.P v
          = I.P v * (uMat (jv v (g.1 v)) * ((I.P v)⁻¹ * A.map (I.φ v) * D.P v)) := by
            simp only [Matrix.mul_assoc]
        _ = I.P v * (((I.P v)⁻¹ * A.map (I.φ v) * D.P v) *
            ((D.P v)⁻¹ * γ.map (I.φ v) * D.P v)) :=
            congrArg (I.P v * ·) (h2.trans (congrArg (infMat D v A * ·) (hg1 v)))
        _ = A.map (I.φ v) * γ.map (I.φ v) * D.P v := by
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc (D.P v) (D.P v)⁻¹, Matrix.mul_nonsing_inv _ hDu, Matrix.one_mul,
              ← Matrix.mul_assoc (I.P v) (I.P v)⁻¹, Matrix.mul_nonsing_inv _ hPu, Matrix.one_mul]
    have hAv : (I.P v * uMat (jv v (g.1 v)) * (I.P v)⁻¹) * A.map (I.φ v) =
        A.map (I.φ v) * γ.map (I.φ v) := by
      calc (I.P v * uMat (jv v (g.1 v)) * (I.P v)⁻¹) * A.map (I.φ v)
          = (I.P v * uMat (jv v (g.1 v)) * (I.P v)⁻¹) * A.map (I.φ v) * D.P v * (D.P v)⁻¹ := by
            rw [Matrix.mul_assoc _ (D.P v), Matrix.mul_nonsing_inv _ hDu, Matrix.mul_one]
        _ = A.map (I.φ v) * γ.map (I.φ v) * D.P v * (D.P v)⁻¹ := by rw [key]
        _ = A.map (I.φ v) * γ.map (I.φ v) := by
            rw [Matrix.mul_assoc _ (D.P v), Matrix.mul_nonsing_inv _ hDu, Matrix.mul_one]
    have hM := eq_map_of_resolution (I.φ v) h (I.P v * uMat (jv v (g.1 v)) * (I.P v)⁻¹) γ hxv hAv
    change uMat (jv v (g.1 v)) = _
    rw [← hM]
    simp only [Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul _ hPu, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hPu,
      Matrix.one_mul]
  · change I.fmat (jf g.2) = _
    exact eq_map_of_resolution (Formalism.UG.inclE (F := I.F) (Af I.F)) h (I.fmat (jf g.2)) γ (hf g.2).1
      ((hf g.2).2.trans (congrArg (afMat I A * ·) hg2))

theorem inclE_injective (I : AutInst) :
    Function.Injective (Formalism.UG.inclE (F := I.F) (E := I.E) (Af I.F)) := by
  have hnf : ¬ IsField (𝓞 I.F) := by
    exact NumberField.RingOfIntegers.not_isField I.F
  obtain ⟨p, hp0, hpp⟩ := Ring.not_isField_iff_exists_prime.mp hnf
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 I.F) := ⟨p, hpp, hp0⟩
  have : Nontrivial (Af I.F) :=
    ⟨⟨1, 0, fun h => one_ne_zero (congrArg (fun a : Af I.F => (a.1 v : v.adicCompletion I.F)) h)⟩⟩
  intro a b hab
  exact Algebra.TensorProduct.includeLeft_injective (R := I.F) (S := I.F) (A := I.E) (B := Af I.F)
    (RingHom.injective _) hab

end GlobalTheory.StabUnfold.RatPts

namespace GlobalTheory.StabUnfold

open GlobalTheory.RatDiscrete RatPts

theorem image_rational_eq_stab : ∀ (I : AutInst) (D : Sib I) (s : Bool) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin D.n) I.E) (xf : I.Gf), IsPerp D s x A xf → ∀ (jv : ∀ v, Formalism.REAL.UJ (D.ε v) →* Formalism.REAL.UJ (I.ε v)) (jf : D.inst.Gf →* I.Gf), IsInfEmb D x A jv → IsFinEmb D x A jf → embA D jv jf '' D.inst.GFset = stabF I x := by
  intro I D s x A xf hP jv jf hv hf
  obtain ⟨hn, hβ, hxA, hAJ, -, -⟩ := hP
  have hJ : I.Jᴴ = I.J := by
    have hh := I.J_herm
    unfold Formalism.UG.IsHerm at hh
    ext i j
    have hij := congrFun (congrFun hh i) j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at hij
    rw [Matrix.conjTranspose_apply]
    exact hij
  have hβ0 : star x ⬝ᵥ (I.J *ᵥ x) ≠ 0 := by
    rw [hβ]; cases s <;> simp [GlobalTheory.GaussMean.sgn]
  obtain ⟨u, A', hA'A, hA'x, huA, hux, hres, hAJx⟩ :=
    exists_dual_of_anisotropic_orthogonal I.E I.n D.n I.J D.J x A hn hJ D.J_det hβ0 hxA hAJ
  obtain ⟨j, hjv, hjr⟩ := GlobalTheory.T.exists_unitary_orthogonal_embedding_stabilizer I.E (starRingEnd I.E) I.n D.n I.J D.J x u A A'
    (isUnit_iff_ne_zero.mpr hβ0) hxA hAJx hAJ hA'A hA'x huA hux hres
  ext y
  constructor
  · rintro ⟨g, ⟨γ, hγ, hg1, hg2⟩, rfl⟩
    have hIm := isImage_embA D hres hv hf (γ := (γ : Matrix (Fin D.n) (Fin D.n) I.E)) (g := g) ⟨hg1, hg2⟩
    have hj := hjv ⟨γ, hγ⟩
    refine ⟨⟨(j ⟨γ, hγ⟩ : GL (Fin I.n) I.E), (j ⟨γ, hγ⟩).2, ?_⟩, (hf g.2).1⟩
    change IsImage I _ _
    rw [hj]
    exact hIm
  · rintro ⟨⟨δ, hδ, hy1, hy2⟩, hyx⟩
    have h3 : (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (((δ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ x) i)) =
        fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (x i) := by
      rw [← GlobalTheory.Proof.rational_unipotentRadical_mem_adelic.map_mulVec_incl, ← hy2]
      exact hyx
    have hδx : (δ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ x = x := by
      funext i
      exact inclE_injective I (congrFun h3 i)
    obtain ⟨γ₀, hγ₀⟩ := hjr ⟨δ, hδ⟩ hδx
    obtain ⟨g, hg⟩ := exists_isImage D.inst (γ₀ : GL (Fin D.n) I.E) γ₀.2
    refine ⟨g, ⟨(γ₀ : GL (Fin D.n) I.E), γ₀.2, hg.1, hg.2⟩, ?_⟩
    have hIm := isImage_embA D hres hv hf hg
    have hM : vecMulVec x u + A * ((γ₀ : GL (Fin D.n) I.E) : Matrix (Fin D.n) (Fin D.n) I.E) * A' =
        (δ : Matrix (Fin I.n) (Fin I.n) I.E) := by
      rw [← hjv γ₀, hγ₀]
    rw [hM] at hIm
    exact subsingleton_isImage I _ hIm ⟨hy1, hy2⟩

end GlobalTheory.StabUnfold
end

section

open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

theorem _root_.GlobalTheory.T.realFrame_automorphism_unitriangular_rows_coords : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V) (r : ℕ) (N : NF H r) (k : ℕ) (σ : K →+* ℂ) (ρ : ℝ) (β : Fin r → ℕ) (Φ : V → Fin (2 * r + k + 1) → ℂ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mat k r), 0 < ρ → IsFrameOf N k σ ρ β Φ z z' g → ∀ (s : V ≃ₗ[K] V) (q : (UTin β → ℂ) × PTop k r N.j), (∀ x, crd k r N.j β q *ᵥ Φ x = Φ (s x)) → (∀ (i : UTin β) (u : Fin r → K), s (N.F.e i.1.1.2.castSucc) = N.F.e i.1.1.2.castSucc + ∑ c, u c • N.F.e c.castSucc → q.1 i = ((ρ ^ (i.1.1.2.val - i.1.1.1.val) : ℝ) : ℂ) * σ (u i.1.1.1)) ∧ (q.1 = 0 → ∀ a : Fin r, s (N.F.e a.castSucc) = N.F.e a.castSucc) ∧ (q.1 = 0 → ∀ (b : {a : Fin r // N.j ≤ a.val}) (y : V), s (N.ist b.1) - N.ist b.1 - y ∈ II N.F N.F' → q.2.1 b = ((ρ ^ (r - b.1.val) : ℝ) : ℂ) • fun l => Φ y (wI k r l)) := by
  first | exact @GlobalTheory.DegVol.RefCovTop.coords_top | exact GlobalTheory.DegVol.RefCovTop.coords_top | (intros; apply GlobalTheory.DegVol.RefCovTop.coords_top <;> assumption)
end

section

noncomputable section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

namespace GlobalTheory.DegVol.RefCovSkew

theorem herm_esI {k r : ℕ} (u : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    herm (Hpk k r) u (bvec (esI k r a)) = u (eI k r a) := by
  have ha := a.2
  have ht : WeylGroupFacts.tau k r (esI k r a) = eI k r a := by
    have h1 : (esI k r a).val < r ∨ r + k < (esI k r a).val := Or.inr (by simp only [esI]; omega)
    apply Fin.ext; unfold WeylGroupFacts.tau; dsimp only; rw [if_pos h1]; simp only [esI, eI]; omega
  have hs : WeylGroupFacts.sgn k r (esI k r a) = 1 := if_neg (by simp only [esI]; omega)
  unfold herm bvec
  rw [← Pi.single_star, star_one, single_one_dotProduct]
  simp only [mulVec, dotProduct, WeylGroupFacts.hpk_row, ht, hs]
  simp

theorem sum_eI_apply {k r : ℕ} (c : Fin r → ℂ) (a : Fin r) :
    (∑ b, c b • bvec (eI k r b)) (eI k r a) = c a := by
  simp [Finset.sum_apply, Rad.bvec_apply, Rad.eI_inj]

theorem coords_skew : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V) (r : ℕ) (N : NF H r) (k : ℕ) (σ : K →+* ℂ) (ρ : ℝ) (β : Fin r → ℕ) (Φ : V → Fin (2 * r + k + 1) → ℂ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mat k r), 0 < ρ → IsFrameOf N k σ ρ β Φ z z' g → ∀ (s : V ≃ₗ[K] V) (q : (UTin β → ℂ) × PTop k r N.j), (∀ x, crd k r N.j β q *ᵥ Φ x = Φ (s x)) → q.1 = 0 → q.2.1 = 0 → (∀ b : Fin r, N.j ≤ b.val → s (N.ist b) - N.ist b ∈ II N.F N.F') ∧ (∀ p : {p : UT r // N.j ≤ p.1.1.val}, q.2.2.1 p = ((ρ ^ ((r - p.1.1.1.val) + (r - p.1.1.2.val)) : ℝ) : ℂ) * σ (H.B (s (N.ist p.1.1.2)) (N.ist p.1.1.1))) ∧ ∀ a : {a : Fin r // N.j ≤ a.val}, q.2.2.2 a = ρ ^ (2 * (r - a.1.val)) * (σ (H.B (s (N.ist a.1)) (N.ist a.1))).im := by
  intro K V _ _ _ _ _ _ _ _ H r N k σ ρ β Φ z z' g hρ hF s q hq hq1 hq2
  obtain ⟨hr, -, -, -, -, he, hi, -⟩ := hF
  have he1 : ∀ a : Fin r, Φ (N.F.e a.castSucc) = ((ρ ^ (r - a.val) : ℝ) : ℂ) • bvec (eI k r a) := fun a => (he a).1
  have ht : ∀ n : ℕ, ((ρ ^ n : ℝ) : ℂ) ≠ 0 := fun n => by
    exact_mod_cast (pow_pos hρ n).ne'
  set S : Matrix (Fin r) (Fin r) ℂ := skewM (Swap.extS r N.j q.2.2).1 (Swap.extS r N.j q.2.2).2 with hSdef
  have hM : crd k r N.j β q = pEl k r 0 S := by
    rw [RefCovTop.crd_of_zero β q hq1, Swap.pTop_eq, pOf, hq2, map_zero]
  have hS0 : ∀ a b : Fin r, ¬ N.j ≤ a.val → S a b = 0 := fun a b ha => Swap.skew_ext_zero q.2.2 a b ha
  have hcol : ∀ b : Fin r, pEl k r 0 S *ᵥ bvec (esI k r b) = bvec (esI k r b) + ∑ a, S a b • bvec (eI k r a) := by
    intro b
    rw [((Rad.radical k r).1 0 S).2.2.1 b]
    simp [herm]
  have hsb : ∀ b : Fin r, N.j ≤ b.val → Φ (s (N.ist b)) =
      (((ρ ^ (r - b.val))⁻¹ : ℝ) : ℂ) • (bvec (esI k r b) + ∑ a, S a b • bvec (eI k r a)) := by
    intro b hb; rw [← hq, hM, hi b hb, mulVec_smul, hcol]
  have hB : ∀ a b : Fin r, N.j ≤ a.val → N.j ≤ b.val → σ (H.B (s (N.ist b)) (N.ist a)) =
      (((ρ ^ (r - a.val))⁻¹ : ℝ) : ℂ) * ((((ρ ^ (r - b.val))⁻¹ : ℝ) : ℂ) * S a b) := by
    intro a b ha hb
    rw [← hr.2.2.1, hsb b hb, hi a ha, RealMat.herm_smul_right, herm_esI, Pi.smul_apply, Pi.add_apply, sum_eI_apply,
      Rad.bvec_apply, if_neg (Rad.eI_ne_esI a b), zero_add, smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
  refine ⟨fun b hb => ?_, fun p => ?_, fun a => ?_⟩
  · have hΦy : Φ (s (N.ist b) - N.ist b) = ∑ a, ((((ρ ^ (r - b.val))⁻¹ : ℝ) : ℂ) * S a b) • bvec (eI k r a) := by
      rw [RealMat.phi_sub hr, hsb b hb, hi b hb, smul_add, add_sub_cancel_left, Finset.smul_sum]
      simp_rw [smul_smul]
    have hproj : NFGeom.proj N (s (N.ist b) - N.ist b) = s (N.ist b) - N.ist b := by
      apply RealMat.phi_inj hr
      rw [NFGeom.proj_apply, RealMat.phi_sum hr, hΦy, Finset.sum_filter]
      refine Finset.sum_congr rfl fun a _ => ?_
      split_ifs with ha
      · rw [hr.2.1, he1, ← hr.2.2.1, hΦy, hi a ha, RealMat.herm_smul_right, herm_esI, sum_eI_apply, smul_smul]
        congr 1
        rw [Complex.star_def, Complex.conj_ofReal, Complex.ofReal_inv, mul_comm, ← mul_assoc,
          mul_inv_cancel₀ (ht _), one_mul]
      · rw [hS0 a b ha, mul_zero, zero_smul]
    rw [← hproj]; exact NFGeom.proj_mem N _
  · obtain ⟨⟨⟨a, b⟩, hab⟩, ha⟩ := p
    have hab' : a < b := hab
    have ha' : N.j ≤ a.val := ha
    have hb : N.j ≤ b.val := le_trans ha' (le_of_lt hab')
    simp only
    rw [hB a b ha' hb]
    have hSab : S a b = q.2.2.1 ⟨⟨(a, b), hab⟩, ha⟩ := by
      simp [hSdef, skewM, hab', Swap.extS, Swap.extZ, ha']
    rw [hSab, pow_add, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_inv]
    have h1 := ht (r - a.val)
    have h2 := ht (r - b.val)
    field_simp
  · obtain ⟨a, ha⟩ := a
    simp only
    rw [hB a a ha ha]
    have hSaa : S a a = ((q.2.2.2 ⟨a, ha⟩ : ℝ) : ℂ) * Complex.I := by
      simp [hSdef, skewM, Swap.extS, Swap.extZ, ha]
    rw [hSaa]
    have e : ((((ρ ^ (r - a.val))⁻¹ : ℝ) : ℂ) * ((((ρ ^ (r - a.val))⁻¹ : ℝ) : ℂ) * (((q.2.2.2 ⟨a, ha⟩ : ℝ) : ℂ) * Complex.I))) =
        (((ρ ^ (r - a.val))⁻¹ * ((ρ ^ (r - a.val))⁻¹ * q.2.2.2 ⟨a, ha⟩) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [e, Complex.mul_I_im, Complex.ofReal_re, two_mul, pow_add]
    have h1 : ρ ^ (r - a.val) ≠ 0 := (pow_pos hρ _).ne'
    field_simp

end GlobalTheory.DegVol.RefCovSkew
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

theorem _root_.GlobalTheory.T.exists_nearest_point_coset_orthogonal_lieAlgebra : ∀ (n : ℕ) (ε : Fin n → Bool) (S : Set (Formalism.REAL.UJ ε)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), IsCut ε S E → S ⊆ maxK ε → (∀ i, (E i)ᴴ = -E i) → ∀ k ∈ maxK ε, ∃ l ∈ S, crd E (uMat (l * k) - 1) = 0 ∧ ∀ l' ∈ S, nrm (uMat (l * k) - 1) ≤ nrm (uMat (l' * k) - 1) := by
  first | exact @GlobalTheory.IwConstMin.exists_nearest | exact GlobalTheory.IwConstMin.exists_nearest | (intros; apply GlobalTheory.IwConstMin.exists_nearest <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

theorem _root_.GlobalTheory.T.iwasawaGauge_definite_and_unitBody_volume : ∀ (n : ℕ), ∀ (dN dM dK dL : ℕ) (EN : Fin dN → Matrix (Fin n) (Fin n) ℂ) (EM : Fin dM → Matrix (Fin n) (Fin n) ℂ) (EK : Fin dK → Matrix (Fin n) (Fin n) ℂ) (EL : Fin dL → Matrix (Fin n) (Fin n) ℂ), IsON EN → IsON EM → IsON EK → IsON EL → LieRel EN EM EK EL → dK = dN + dL → (∀ v, gau EN EM EK EL v = 0 → v = 0) ∧ volume {v | gau EN EM EK EL v ≤ 1} = ENNReal.ofReal ((2 : ℝ) ^ ((dN : ℝ) / 2)) * ballVol (2 * dN + dM) * ballVol dL := by
  first | exact @GlobalTheory.IwConst.gau_definite_and_volume | exact GlobalTheory.IwConst.gau_definite_and_volume | (intros; apply GlobalTheory.IwConst.gau_definite_and_volume <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

theorem _root_.GlobalTheory.T.discrete_series_coefficient_integrable_majorant : PhMaj := by
  first | exact @GlobalTheory.Dec.PhMajProof.phMaj | exact GlobalTheory.Dec.PhMajProof.phMaj | (intros; apply GlobalTheory.Dec.PhMajProof.phMaj <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.deepRegion_kernelDiagonal_bound : GlobalTheory.FlagMeas.AbsoluteVolume → GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.DeepKernelBound → GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.DeepBound := by
  first | exact @GlobalTheory.DeepRegion.deepBound | exact GlobalTheory.DeepRegion.deepBound | (intros; apply GlobalTheory.DeepRegion.deepBound <;> assumption)
end

section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef NumberField

theorem _root_.GlobalTheory.T.V0_map_iota_eq_top_definite : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 Ty T : Type) (m : ℕ) (A3 : FamIn3 D.what₂.LL G Pl0 I0 Ty T m) (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (Ps : Subgroup G) (ψs : Ps →* D.what₂.LLˣ) (Zs : DefSub A3.fam3.amb3) (S0 : IndefData (A3.side3 P0 ψ0 Zs)) (S1 : IndefData (A3.side3 Ps ψs Zs)) (X0 : BaseLevelRowSide D) (Dc : DefCols (A3.side3 Ps ψs Zs)) (Sp : SPer Dc) (C : ColData Dc Sp S1) (NuC : ∀ u, Submodule (𝓞 D.what₂.LL) (Fin (Dc.a u) → D.what₂.LL)) (I : DivisionCompatibilityDataThreeSided D A3 P0 ψ0 Ps ψs Zs S0 S1 X0 Dc), DivDef3 D A3 P0 ψ0 Ps ψs Zs S0 S1 X0 C NuC I → (∃ s, A3.A.fam.Ok s) → Function.Surjective ((A3.side3 Ps ψs Zs).Pq A3.A.μ0).mulVec → Function.Surjective (S1.ι A3.A.μ0).mulVec → (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ := by
  first | exact @GlobalTheory.V0_map_iota_eq_top_of_definite | exact GlobalTheory.V0_map_iota_eq_top_of_definite | (intros; apply GlobalTheory.V0_map_iota_eq_top_of_definite <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.leadMinor_gramMatrix_const_doubleCoset : ∀ (D : D7) (Λ : Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V) (T T' : D.host.E) (F : LFlag (D.sp.Y 0) D.R.rS T) (F₁ F₂ : LFlag (D.sp.Y 0) D.R.rS T'), Formalism.L2.SG.TermDef.DCRel Λ F F₁ F₂ → ∀ l : ℕ, leadMinorE (ZhatL F F₂) l = leadMinorE (ZhatL F F₁) l := by
  first | exact @GlobalTheory.leadMinorE_zhatL_dcrel | exact GlobalTheory.leadMinorE_zhatL_dcrel | (intros; apply GlobalTheory.leadMinorE_zhatL_dcrel <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

theorem _root_.GlobalTheory.T.criticalLevel_le_pow_allPlaces : Formalism.L2.SG.Pf.SzHypFD.DsigHC → ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), Ties D → Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → 40 ≤ Cl → ∀ u τ, Tcrit D u τ ≤ large₂.sc.b ^ ((4 * Cg + 12) * (D.R.m : ℝ)) := by
  first | exact @GlobalTheory.CritLevelUpper.tcrit_le_pow | exact GlobalTheory.CritLevelUpper.tcrit_le_pow | (intros; apply GlobalTheory.CritLevelUpper.tcrit_le_pow <;> assumption)
end

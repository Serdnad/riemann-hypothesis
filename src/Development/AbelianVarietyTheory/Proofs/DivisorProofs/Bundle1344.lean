module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1193
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1194
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
import Formalism.LocalToGlobal.IndefiniteReal.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DblScal

open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev UD (σ : E →ₐ[F] E) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) : Type := UG (cA σ) (dbl (incM F J))

def UDAt {R : Type} [Zero R] (σ : E →ₐ[F] E) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (ev : AF F → R) : Set (UD σ J) :=
  {p | At ev (((p : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) - 1)}

def dsum {k : Type} [CommRing k] {d : ℕ} (c : GL (Fin d) k) : GL (Fin d ⊕ Fin d) k where
  val := Matrix.fromBlocks c.val 0 0 c.val
  inv := Matrix.fromBlocks (c⁻¹).val 0 0 (c⁻¹).val
  val_inv := by simp [Matrix.fromBlocks_multiply]
  inv_val := by simp [Matrix.fromBlocks_multiply]

def locMatD {σ : E →ₐ[F] E} {v : Pl (F := F)} (t : E →ₐ[F] Fv F v) {d : ℕ} {J : Matrix (Fin d) (Fin d) E}
    (c : GL (Fin d) (Fv F v)) : UD σ J →* GL (Fin d ⊕ Fin d) (Fv F v) where
  toFun p := (dsum c)⁻¹ * Matrix.GeneralLinearGroup.map (piW t) p.1 * dsum c
  map_one' := by simp
  map_mul' p q := by simp [mul_assoc]

abbrev DblCo (σ : E →ₐ[F] E) {n d : ℕ} (X : Spc F E n) (W : Spc F E d) : Type :=
  Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (dbl (incM F W.J))) (Fin n × Fin d ⊕ Fin n × Fin d)

abbrev DblRep (σ : E →ₐ[F] E) {n d : ℕ} (W : Spc F E d) : Type :=
  UD σ W.J →* Module.End ℂ ((Fin n × Fin d ⊕ Fin n × Fin d → AF F) → ℂ)

structure IsLinD {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (ψ : AddChar (AF F) ℂ) (dd : DblCo σ X W)
    {v : Pl (F := F)} (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v))
    (ιd : ((Fin n × Fin d ⊕ Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v) → ℂ)) :
    Prop where
  bij : Set.BijOn ιd (SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v) : Set _)
    (SB (Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v)) : Set _)
  trans : ∀ u : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E), At (evFin F v) u → u.map (piW (t.comp σ)) = 0 →
    ∀ φ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v),
      Acts (evFin F v) (dd.rho ψ u) φ φ₁ →
      ∀ Y, ιd φ₁ Y = ιd φ (Y + (b⁻¹).val * u.map (piW t) * ((dsum c)⁻¹).valᵀ)
  mult : ∀ u : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E), At (evFin F v) u → u.map (piW t) = 0 →
    ∀ φ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v),
      Acts (evFin F v) (dd.rho ψ u) φ φ₁ →
      ∀ x : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E), At (evFin F v) x → x.map (piW (t.comp σ)) = 0 →
        ιd φ₁ ((b⁻¹).val * x.map (piW t) * ((dsum c)⁻¹).valᵀ) =
          ψ (symp (cA σ) (-1) (incM F X.J) (dbl (incM F W.J)) x u) * ιd φ ((b⁻¹).val * x.map (piW t) * ((dsum c)⁻¹).valᵀ)

def LocOps {σ : E →ₐ[F] E} {n d : ℕ} {W : Spc F E d} (omd : DblRep σ (n := n) W) (v : Pl (F := F)) : Prop :=
  ∀ p ∈ UDAt σ W.J (evFin F v), ∀ φ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v),
    ∃ φ₁ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v), Acts (evFin F v) (omd p) φ φ₁

def IsShapeD {σ : E →ₐ[F] E} {n d : ℕ} {W : Spc F E d} (omd : DblRep σ (n := n) W) {v : Pl (F := F)} (t : E →ₐ[F] Fv F v)
    (c : GL (Fin d) (Fv F v))
    (ιd : ((Fin n × Fin d ⊕ Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v) → ℂ))
    (cd : UD σ W.J → ℂ) : Prop :=
  ∀ p ∈ UDAt σ W.J (evFin F v), ∀ φ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v),
    ∀ φ₁ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v), Acts (evFin F v) (omd p) φ φ₁ →
      ιd φ₁ = cd p • fun Y => ιd φ (Y * (GlobalTheory.SplitFlip.invT (locMatD t c p)).val)

theorem exists_diag_one {σ : E →ₐ[F] E} {d : ℕ} {J : Matrix (Fin d) (Fin d) E} (h : UA σ J) :
    ∃ gd : UD σ J, ((gd : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) =
      Matrix.fromBlocks (mat h) 0 0 1 := by
  let A : Matrix (Fin d) (Fin d) (AE F E) := mat h
  let Ai : Matrix (Fin d) (Fin d) (AE F E) := (((h : GL (Fin d) (AE F E))⁻¹ : GL (Fin d) (AE F E)) : Matrix _ _ _)
  have h1 : A * Ai = 1 := (h : GL (Fin d) (AE F E)).mul_inv
  have h2 : Ai * A = 1 := (h : GL (Fin d) (AE F E)).inv_mul
  let G : GL (Fin d ⊕ Fin d) (AE F E) :=
    ⟨Matrix.fromBlocks A 0 0 1, Matrix.fromBlocks Ai 0 0 1, by simp [fromBlocks_multiply, h1],
      by simp [fromBlocks_multiply, h2]⟩
  have hu : Aᵀ * incM F J * A.map (cA σ) = incM F J := h.2
  refine ⟨⟨G, ?_⟩, rfl⟩
  show (Matrix.fromBlocks A 0 0 1)ᵀ * dbl (incM F J) * (Matrix.fromBlocks A 0 0 1).map (cA σ) = dbl (incM F J)
  rw [fromBlocks_transpose, fromBlocks_map, dbl, fromBlocks_multiply, fromBlocks_multiply]
  simp only [transpose_zero, transpose_one, Matrix.map_zero _ (map_zero (cA σ)), Matrix.map_one _ (map_zero (cA σ)) (map_one (cA σ)),
    Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.one_mul, Matrix.mul_one, hu]

theorem gdet_locMatD_diag {σ : E →ₐ[F] E} {v : Pl (F := F)} (t : E →ₐ[F] Fv F v) {d : ℕ} {J : Matrix (Fin d) (Fin d) E}
    (c : GL (Fin d) (Fv F v)) (h : UA σ J) (gd : UD σ J)
    (hgd : ((gd : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) =
      Matrix.fromBlocks (mat h) 0 0 1) :
    GlobalTheory.SplitFlip.gdet (locMatD t c gd) = GlobalTheory.SplitFlip.gdet (locMat t c h) := by
  apply Units.ext
  have e : (locMatD t c gd).val =
      Matrix.fromBlocks (locMat t c h).val 0 0 1 := by
    show ((dsum c)⁻¹).val * (((gd : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix _ _ _).map (piW t)) * (dsum c).val = _
    rw [hgd, locMat_val, fromBlocks_map]
    simp only [dsum, Units.inv_mk, fromBlocks_multiply, Matrix.map_zero _ (map_zero (piW t)),
      Matrix.map_one _ (map_zero (piW t)) (map_one (piW t)), Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
      Matrix.mul_one, Matrix.one_mul]
    congr 1
    simp [Units.mul_inv]
  simp only [GlobalTheory.SplitFlip.gdet, Matrix.GeneralLinearGroup.val_det_apply, e, det_fromBlocks_zero₂₁, det_one, mul_one]

def fixDiag {k : Type} [CommRing k] {d : ℕ} (A : GL (Fin d) k) : GL (Fin d ⊕ Fin d) k where
  val := Matrix.fromBlocks A.val (1 - A.val) 0 1
  inv := Matrix.fromBlocks (A⁻¹).val (1 - (A⁻¹).val) 0 1
  val_inv := by simp [fromBlocks_multiply, Matrix.mul_sub]
  inv_val := by simp [fromBlocks_multiply, Matrix.mul_sub]

theorem fixDiag_diag {k : Type} [CommRing k] {d : ℕ} (A : GL (Fin d) k) :
    ((fixDiag A).val : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) k) * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) k) =
      (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) k) * (1 : Matrix (Fin d) (Fin d) k) := by
  simp only [fixDiag, diagCols, Matrix.mul_one]
  rw [← fromCols_fromRows_eq_fromBlocks, fromCols_mul_fromRows, fromRows_mul, fromRows_mul]
  ext (i | i) j <;> simp

theorem gdet_fixDiag {k : Type} [Field k] {d : ℕ} (A : GL (Fin d) k) :
    GlobalTheory.SplitFlip.gdet (fixDiag A) = GlobalTheory.SplitFlip.gdet A := by
  apply Units.ext
  simp [GlobalTheory.SplitFlip.gdet, Matrix.GeneralLinearGroup.val_det_apply, fixDiag, det_fromBlocks_zero₂₁]

theorem fromBlocks_sub_one {R : Type} [CommRing R] {d : ℕ} (A : Matrix (Fin d) (Fin d) R) :
    Matrix.fromBlocks A (0 : Matrix (Fin d) (Fin d) R) 0 (1 : Matrix (Fin d) (Fin d) R) - 1 =
      Matrix.fromBlocks (A - 1) (0 : Matrix (Fin d) (Fin d) R) 0 0 := by
  ext (i | i) (j | j) <;> simp [Matrix.one_apply]

end GlobalTheory.DblScal

end
end

section

noncomputable section

open Matrix GlobalTheory.SplitWeil GlobalTheory.KSplit

namespace GlobalTheory.JacLine

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def blk3 (a b : ℕ) : Fin 1 ⊕ Fin (a + b) ⊕ Fin 1 ≃ Fin (a + (b + 2)) :=
  ((Equiv.sumCongr (Equiv.refl (Fin 1)) finSumFinEquiv).trans finSumFinEquiv).trans (finCongr (by omega))

def IsJacMap (a b : ℕ) (α β : kˣ →* ℂˣ) (χ₁ χ₂ : kˣ → ℂ) (φ : indSp a (b + 2) α β →ₗ[ℂ] indSp a b α β) : Prop :=
  (∀ (u : GL (Fin (a + (b + 2))) k) (X : Matrix (Fin 1) (Fin (a + b) ⊕ Fin 1) k) (Y : Matrix (Fin (a + b)) (Fin 1) k),
      u.val.submatrix (blk3 a b) (blk3 a b) = fromBlocks 1 X 0 (fromBlocks 1 Y 0 1) →
      ∀ f f₁ : indSp a (b + 2) α β, (∀ h, (f₁ : GL (Fin (a + (b + 2))) k → ℂ) h = (f : GL (Fin (a + (b + 2))) k → ℂ) (h * u)) →
        φ f₁ = φ f) ∧
  ∀ (m : GL (Fin (a + (b + 2))) k) (x y : kˣ) (g : GL (Fin (a + b)) k),
      m.val.submatrix (blk3 a b) (blk3 a b) =
        fromBlocks (of fun _ _ => (x : k)) 0 0 (fromBlocks g.val 0 0 (of fun _ _ => (y : k))) →
      ∀ f f₁ : indSp a (b + 2) α β, (∀ h, (f₁ : GL (Fin (a + (b + 2))) k → ℂ) h = (f : GL (Fin (a + (b + 2))) k → ℂ) (h * m)) →
        ∀ h, (φ f₁ : GL (Fin (a + b)) k → ℂ) h = χ₁ x * χ₂ y * (φ f : GL (Fin (a + b)) k → ℂ) (h * g)

end GlobalTheory.JacLine

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilAdm.HaarSplit

variable (F : Type) [Field F] [NumberField F] (κ : Type)

def splitE : ((κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) ≃+ (κ → AdeleRing (𝓞 F) F) where
  toFun p := fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i)
  invFun x := (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1, fun i => (x i).2)
  left_inv p := Prod.ext (funext fun i => RingEquiv.apply_symm_apply _ _) (funext fun i => rfl)
  right_inv x := funext fun i => Prod.ext (RingEquiv.symm_apply_apply _ _) rfl
  map_add' p q := funext fun i => Prod.ext (map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i) (q.1 i)) rfl

theorem splitE_apply (p : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) :
    splitE F κ p = fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i) := rfl

theorem continuous_splitE : Continuous (splitE F κ) := by
  rw [show ⇑(splitE F κ) = fun p : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F) =>
    fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i) from rfl]
  have hc : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
    refine continuous_pi fun v => ?_
    rcases v.isReal_or_isComplex with hv | hv
    · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
      exact ((continuous_apply _).comp continuous_fst).congr fun y =>
        (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
    · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
      exact ((continuous_apply _).comp continuous_snd).congr fun y =>
        (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
  exact continuous_pi fun i => (hc.comp
    ((continuous_apply i).comp continuous_fst)).prodMk ((continuous_apply i).comp continuous_snd)

theorem continuous_splitE_symm : Continuous (splitE F κ).symm := by
  rw [show ⇑(splitE F κ).symm = fun x : κ → AdeleRing (𝓞 F) F =>
    ((fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1, fun i => (x i).2) :
      (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) from rfl]
  have hc : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
    have he : (InfiniteAdeleRing.ringEquiv_mixedSpace F : InfiniteAdeleRing F → mixedEmbedding.mixedSpace F) =
        fun x => ((fun v : {w : InfinitePlace F // InfinitePlace.IsReal w} =>
            InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
          (fun v : {w : InfinitePlace F // InfinitePlace.IsComplex w} =>
            InfinitePlace.Completion.extensionEmbedding v.1 (x v))) := by
      funext x; exact InfiniteAdeleRing.ringEquiv_mixedSpace_apply F x
    rw [he]
    refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
    · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
    · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)
  exact (continuous_pi fun i => hc.comp
    (continuous_fst.comp (continuous_apply i))).prodMk (continuous_pi fun i => continuous_snd.comp (continuous_apply i))

theorem pureA_splitE (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (p : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) :
    GlobalTheory.WeilM.pureA F f g (splitE F κ p) = f p.1 * g p.2 := by
  simp only [GlobalTheory.WeilM.pureA, splitE_apply, RingEquiv.apply_symm_apply]

theorem continuous_comp_splitE [Fintype κ] (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ) :
    Continuous fun p => Φ (splitE F κ p) := by
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    simp only [pureA_splitE]
    exact (f.continuous.comp continuous_fst).mul (hg.1.continuous.comp continuous_snd)
  | zero => exact continuous_const
  | add x x' _ _ hx hx' => exact hx.add hx'
  | smul a x _ hx => exact hx.const_smul a

theorem splitE_add_finE (z : κ → mixedEmbedding.mixedSpace F) (y u : κ → FiniteAdeleRing (𝓞 F) F) :
    splitE F κ (z, y + u) = splitE F κ (z, y) + GlobalTheory.WeilAdm.finE F u :=
  funext fun i => Prod.ext (add_zero _).symm rfl

theorem volume_isAddHaar [Fintype κ] : (volume : Measure (κ → mixedEmbedding.mixedSpace F)).IsAddHaarMeasure := by
  haveI : MeasurableAdd (mixedEmbedding.mixedSpace F) := ContinuousAdd.measurableAdd
  exact Measure.pi.isAddHaarMeasure _

end GlobalTheory.WeilAdm.HaarSplit

namespace GlobalTheory.WeilAdm.HaarSplit

open GlobalTheory.WeilAdm.HaarSplit

theorem haar_pure_slice_bounds : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
    g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) → ∀ U : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F), IsOpen (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) →
      ∃ μ : @Measure (κ → AdeleRing (𝓞 F) F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ ∧
        ∃ C c : ℝ≥0∞, C ≠ ⊤ ∧ c ≠ 0 ∧ c ≠ ⊤ ∧
          (∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, ∫⁻ x, ‖GlobalTheory.WeilM.pureA F f g x‖ₑ ^ 2 ∂μ ≤ C * ∫⁻ z, ‖f z‖ₑ ^ 2) ∧
          ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, (∀ x, ∀ u ∈ U, Φ (x + GlobalTheory.WeilAdm.finE F u) = Φ x) →
            ∀ y, c * ∫⁻ z, ‖GlobalTheory.WeilAdm.slice F Φ y z‖ₑ ^ 2 ≤ ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
  intro F _ _ κ _ g hg U hU
  haveI := volume_isAddHaar F κ
  haveI : OpensMeasurableSpace (κ → mixedEmbedding.mixedSpace F) := inferInstance
  haveI : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI : SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  letI mY : MeasurableSpace (κ → FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  letI mA : MeasurableSpace (κ → AdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → AdeleRing (𝓞 F) F) := ⟨rfl⟩
  haveI : SigmaCompactSpace (κ → FiniteAdeleRing (𝓞 F) F) := sigmaCompactSpace_of_locallyCompact_secondCountable
  set ν : Measure (κ → FiniteAdeleRing (𝓞 F) F) := Measure.addHaar with hν
  haveI : SFinite ν := inferInstance
  haveI : MeasurableAdd (κ → mixedEmbedding.mixedSpace F) := ContinuousAdd.measurableAdd
  haveI : MeasurableAdd (κ → FiniteAdeleRing (𝓞 F) F) := ContinuousAdd.measurableAdd
  haveI : ν.IsAddHaarMeasure := by rw [hν]; infer_instance
  haveI : ((volume : Measure (κ → mixedEmbedding.mixedSpace F)).prod ν).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure (volume : Measure (κ → mixedEmbedding.mixedSpace F)) ν
  have hμH : Measure.IsAddHaarMeasure ((volume.prod ν).map (splitE F κ)) :=
    (splitE F κ).isAddHaarMeasure_map _ (continuous_splitE F κ) (continuous_splitE_symm F κ)
  let em : ((κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) ≃ᵐ (κ → AdeleRing (𝓞 F) F) :=
    (Homeomorph.mk (splitE F κ).toEquiv (continuous_splitE F κ) (continuous_splitE_symm F κ)).toMeasurableEquiv
  have hint : ∀ h : (κ → AdeleRing (𝓞 F) F) → ℝ≥0∞,
      ∫⁻ x, h x ∂((volume.prod ν).map (splitE F κ)) = ∫⁻ p, h (splitE F κ p) ∂(volume.prod ν) :=
    fun h => lintegral_map_equiv h em

  have hgc : Continuous g := hg.1.continuous
  have hC : ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν ≠ ⊤ := by
    have h1 : ∫⁻ y, ‖g y * g y‖ₑ ∂ν < ⊤ :=
      ((hgc.mul hgc).integrable_of_hasCompactSupport (hg.2.mul_left (f := g))).2
    refine ne_of_lt (lt_of_le_of_lt (le_of_eq (lintegral_congr fun y => ?_)) h1)
    rw [enorm_mul, sq]

  obtain ⟨K, hKc, hK0⟩ := exists_compact_mem_nhds (0 : κ → FiniteAdeleRing (𝓞 F) F)
  set S : Set (κ → FiniteAdeleRing (𝓞 F) F) := (U : Set _) ∩ K with hS
  have hSm : MeasurableSet S := hU.measurableSet.inter hKc.isClosed.measurableSet
  have hc0 : ν S ≠ 0 := by
    refine ne_of_gt (lt_of_lt_of_le ?_ (measure_mono (Set.inter_subset_inter_right _ interior_subset)))
    exact (hU.inter isOpen_interior).measure_pos ν ⟨0, U.zero_mem, mem_interior_iff_mem_nhds.2 hK0⟩
  have hcT : ν S ≠ ⊤ := ne_top_of_le_ne_top hKc.measure_lt_top.ne (measure_mono Set.inter_subset_right)
  refine ⟨(volume.prod ν).map (splitE F κ), hμH, ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν, ν S, hC, hc0, hcT, ?_, ?_⟩
  · intro f
    rw [hint]
    have e1 : ∀ p, ‖GlobalTheory.WeilM.pureA F f g (splitE F κ p)‖ₑ ^ 2 = ‖f p.1‖ₑ ^ 2 * ‖g p.2‖ₑ ^ 2 := by
      intro p
      rw [pureA_splitE, enorm_mul, mul_pow]
    simp_rw [e1]
    rw [lintegral_prod_mul (f.continuous.measurable.enorm.pow_const 2).aemeasurable
      (hgc.measurable.enorm.pow_const 2).aemeasurable, mul_comm]
  · intro Φ hΦ hinv y
    rw [hint]
    have hHm : Measurable fun p => ‖Φ (splitE F κ p)‖ₑ ^ 2 :=
      (continuous_comp_splitE F κ Φ hΦ).measurable.enorm.pow_const 2
    rw [lintegral_prod _ hHm.aemeasurable, ← lintegral_const_mul' _ _ hcT]
    refine lintegral_mono fun z => ?_
    set T : Set (κ → FiniteAdeleRing (𝓞 F) F) := (fun y' => y' + -y) ⁻¹' S with hT
    have hTm : MeasurableSet T := hSm.preimage (continuous_id.add continuous_const).measurable
    have hνT : ν T = ν S := measure_preimage_add_right ν (-y) S
    calc ν S * ‖GlobalTheory.WeilAdm.slice F Φ y z‖ₑ ^ 2
        = ∫⁻ y', T.indicator (fun _ => ‖GlobalTheory.WeilAdm.slice F Φ y z‖ₑ ^ 2) y' ∂ν := by
          rw [lintegral_indicator_const hTm, hνT, mul_comm]
      _ ≤ ∫⁻ y', ‖Φ (splitE F κ (z, y'))‖ₑ ^ 2 ∂ν := by
          refine lintegral_mono fun y' => (Set.indicator_le (g := fun y' => ‖Φ (splitE F κ (z, y'))‖ₑ ^ 2) (fun a ha => le_of_eq ?_)) y'
          have hu : a + -y ∈ U := ha.1
          have ha' : a = y + (a + -y) := by abel
          show ‖Φ (splitE F κ (z, y))‖ₑ ^ 2 = ‖Φ (splitE F κ (z, a))‖ₑ ^ 2
          rw [ha', splitE_add_finE, hinv _ _ hu]

end GlobalTheory.WeilAdm.HaarSplit
end
end

section

open scoped SchwartzMap Matrix TensorProduct Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchUniq

noncomputable section

namespace GlobalTheory.ArchUniqStd

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def bil {P : V → V → ℝ} (h : IsPairing P) : LinearMap.BilinForm ℝ V :=
  LinearMap.mk₂ ℝ P h.addL (fun c x y => by simpa [smul_eq_mul] using h.smulL c x y) h.addR
    (fun c x y => by simpa [smul_eq_mul] using h.smulR c x y)

theorem bil_apply {P : V → V → ℝ} (h : IsPairing P) (x y : V) : bil h x y = P x y := rfl

theorem exists_right [FiniteDimensional ℝ V] {P : V → V → ℝ} (h : IsPairing P) (L : V →L[ℝ] ℝ) :
    ∃ b, ∀ y, P y b = L y := by
  have hinj : Function.Injective (bil h).flip := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro b hb
    exact h.nondegR b fun x => by simpa [bil_apply] using LinearMap.congr_fun hb x
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq (K := ℝ) (V := V)).symm).1 hinj
  obtain ⟨b, hb⟩ := hsurj (L : V →ₗ[ℝ] ℝ)
  exact ⟨b, fun y => by simpa [bil_apply] using LinearMap.congr_fun hb y⟩

theorem exists_one [FiniteDimensional ℝ V] : ∃ Φ : 𝓢(V, ℂ), Φ 0 = 1 := by
  let b : ContDiffBump (0 : V) := ⟨1, 2, one_pos, one_lt_two⟩
  have h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  refine ⟨h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff), ?_⟩
  change ((b 0 : ℝ) : ℂ) = 1
  rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]
  simp

end GlobalTheory.ArchUniqStd

namespace GlobalTheory.ArchUniqStd

variable {V₁ : Type} [NormedAddCommGroup V₁] [NormedSpace ℝ V₁] [FiniteDimensional ℝ V₁]

end GlobalTheory.ArchUniqStd

namespace GlobalTheory.ArchUniqStd

variable {V₁ : Type} [NormedAddCommGroup V₁] [NormedSpace ℝ V₁] [FiniteDimensional ℝ V₁]

end GlobalTheory.ArchUniqStd
end
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix RealInnerProductSpace
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open scoped Classical

noncomputable section

namespace GlobalTheory.ArchRhoPure


variable (F : Type) [Field F] [NumberField F] in
def evHom : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

theorem evHom_apply {F : Type} [Field F] [NumberField F] (a : AF F) : evHom F a = evI F a := rfl

theorem rho_pureA_schrF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ)
    (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ), IsStd ψ → ∀ u : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u →
    ∀ (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (h : (κ → Af F) → ℂ),
      d.rho ψ u (pureA F f h) = pureA F (GlobalTheory.ArchUniq.schrF (GlobalTheory.ArchUniq.trP F κ)
        (GlobalTheory.ArchUniq.locV (d.e u).1, GlobalTheory.ArchUniq.locV (d.e u).2) f) h := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ ψ JA JB d hψ u hu f h
  have hw : At (evI F) (d.e u) := fun r hr => by rw [← map_smul, hu r hr, map_zero]
  show schr ψ (d.e u) (pureA F f h) = _
  generalize d.e u = w at hw ⊢
  obtain ⟨p, q⟩ := w
  funext x
  have hfin : (fun i => ((x + p) i).2) = fun i => (x i).2 := by
    funext i
    have h0 : evI F ((0, 1) : AF F) = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
    have h1 : (1 : Af F) * (p i).2 = 0 := congrArg (fun z : (κ → AF F) × (κ → AF F) => (z.1 i).2) (hw _ h0)
    change (x i).2 + (p i).2 = _
    rw [one_mul] at h1
    rw [h1, add_zero]
  have hAt : At (evI F) (x ⬝ᵥ q + ⅟(2 : AF F) * (p ⬝ᵥ q)) := by
    intro v hv
    have hq : v • q = 0 := congrArg Prod.snd (hw v hv)
    rw [smul_add, ← dotProduct_smul, smul_eq_mul, mul_left_comm, ← smul_eq_mul v, ← dotProduct_smul, hq]
    simp
  have harch : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + p) i).1) =
      (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) + ArchUniq.locV p :=
    funext fun i => map_add (evHom F) (x i) (p i)
  have htr : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (x ⬝ᵥ q + ⅟(2 : AF F) * (p ⬝ᵥ q))) =
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 * evI F (q i)) +
        Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, evI F (p i) * evI F (q i)) / 2 := by
    set z : mixedEmbedding.mixedSpace F := ∑ i, evI F (p i) * evI F (q i) with hz
    have hpq : evHom F (p ⬝ᵥ q) = z := by
      rw [RingHom.map_dotProduct]; rfl
    have hxq : evHom F (x ⬝ᵥ q) = ∑ i, InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 * evI F (q i) := by
      rw [RingHom.map_dotProduct]; rfl
    have key : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evHom F ⅟(2 : AF F) * z) +
        Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evHom F ⅟(2 : AF F) * z) =
        Algebra.trace ℝ (mixedEmbedding.mixedSpace F) z := by
      rw [← map_add (f := _), ← add_mul, ← map_add (f := _), invOf_two_add_invOf_two, map_one, one_mul]
    rw [← evHom_apply, map_add (f := _), map_mul, hpq, hxq, map_add (f := _)]
    linarith
  simp only [schr, pureA, GlobalTheory.ArchUniq.schrF, GlobalTheory.ArchUniq.trP, GlobalTheory.ArchUniq.locV] at harch ⊢
  rw [hψ.2.2 _ hAt, hfin, htr, harch, ← mul_assoc]

end GlobalTheory.ArchRhoPure
end
end

module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1910
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle009
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle177
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneParameterWeilOperatorDerivative
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle287
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle358
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle204
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle351
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle361
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
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.FockTransl

open Formalism.L2.Ker (VCx DVar derivAt0)

section Pure

variable {ι : Type} [Fintype ι] {a b : ℕ}

def gq (c : ι → ℝ) (z : VCx ι a b) : ℝ := ∑ τ, ∑ i, ∑ j, c τ * ‖z τ i j‖ ^ 2

def bk (c : ι → ℝ) (z₀ z : VCx ι a b) : ℂ := ∑ τ, ∑ i, ∑ j, (c τ : ℂ) * z₀ τ i j * conj (z τ i j)

def conjMono (m : DVar ι a b →₀ ℕ) (z : VCx ι a b) : ℂ := m.prod fun k n => conj (z k.1 k.2.1 k.2.2) ^ n

end Pure

variable {D : D7}

def fw (D : D7) (τ : D.what₂.Tau) : ℝ := 2 * Real.pi * ‖tauE D τ D.host.xi0‖

def fockMat {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (τ : D.what₂.Tau) (z : Fin T.rank → Fin S.rank → ℂ) :
    Matrix (Fin T.rank) (Fin S.rank) ℂ :=
  ∑ i, ∑ j, (((z i j).re : ℂ) • unitMap (A.onb τ) (B.onb τ) i j +
    ((z i j).im : ℂ) • cplxO (A.cart τ) (B.cart τ) (unitMap (A.onb τ) (B.onb τ) i j))

def fockPt (σ : (D.what₂.Tau → ℂ) →+ AE D) {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T)
    (z : VCx D.what₂.Tau S.rank T.rank) : WO S T :=
  GlobalTheory.FockCompare.iotaW σ T S fun τ => fockMat A B τ (z τ)

def rd (ψ : AddChar (AF D.host.F) ℂ) (σ : (D.what₂.Tau → ℂ) →+ AE D) {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S)
    (B : GlobalTheory.ChainFr.Fr T) (f : WO S T → ℂ) (x : WO S T) (z : VCx D.what₂.Tau S.rank T.rank) : ℂ :=
  (Real.exp (gq (fw D) z / 2) : ℂ) * heisO ψ S T (fockPt σ A B z) f x

theorem fw_pos (D : D7) (τ : D.what₂.Tau) : 0 < fw D τ := by
  unfold fw
  have h : tauE D τ D.host.xi0 ≠ 0 := (map_ne_zero _).2 GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero
  positivity

end GlobalTheory.FockTransl

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FlipMatch

section Generic

def pairM {k A C : Type} [CommRing k] [Fintype A] [Fintype C] (X Y : Matrix A C k) : k := ∑ i, ∑ j, X i j * Y i j

def chart {k k' A C A' C' : Type} [Field k] [Field k'] [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C]
    (j : k ≃+* k') (eA : A ≃ A') (eC : C ≃ C') (g : GL A k') (h : GL C k') (X : Matrix A C k) : Matrix A' C' k' :=
  reindex eA eC (g.val * X.map j * h.val)

def IsLocIso {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [Field k'] [ValuativeRel k'] [TopologicalSpace k']
    (j : k ≃+* k') : Prop :=
  Continuous j ∧ Continuous j.symm ∧ ∀ x, j x ∈ (ValuativeRel.valuation k').integer ↔ x ∈ (ValuativeRel.valuation k).integer

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def coX {n d : ℕ} {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v))
    (u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin n) (Fin d) (Fv F v) :=
  (b⁻¹).1 * u.map (piW t) * (c⁻¹).1ᵀ

def coY (σ : E →ₐ[F] E) {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (t : E →ₐ[F] Fv F v)
    (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)) (u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    Matrix (Fin n) (Fin d) (Fv F v) :=
  -(b.1ᵀ * X.J.map t * u.map (piW (t.comp σ)) * (Y.J.map t)ᵀ * c.1)

def IsMixChart {n d : ℕ} (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (A A' : Set (Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))))
    {k R C : Type} [Add k] [Zero k] (co tr mu : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Matrix R C k) (P : Finset C) : Prop :=
  (∀ u ∈ A, At (evFin F v) u ∧ (∀ r, ∀ s ∈ P, tr u r s = 0) ∧ (∀ r, ∀ s ∉ P, mu u r s = 0) ∧ co u = tr u + mu u) ∧
    ∀ u ∈ A', At (evFin F v) u ∧ (∀ r, ∀ s ∉ P, tr u r s = 0) ∧ ∀ r, ∀ s ∈ P, mu u r s = 0

end Generic

section Grid

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def mixHalfS {i j : ℕ} (e : Num G i j) (ε : AE D) :
    Set (Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) :=
  {u | IsHalf ε (mulG (spW₁ G i j) (colV e u)ᵀ) ∧ IsHalf ε (adjV₁ e u)}

def mixCoS (B : Frames G) (t : T) {i j : Fin D.R.m} (e : Num G i j) (w : Pl D.host.E)
    (u : Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) :
    Matrix (Fin ((locGrid G t w).rank (i, j))) ((locGrid G t w).Cols i j) (Kw w) :=
  fromCols (B.coord t w (X := (i, j + 1)) (Y := (i, j)) ⟨i.2.le, j.2⟩ ⟨i.2.le, j.2.le⟩
      ((mulG (spW₁ G i j) (colV e u)ᵀ).map fun a => cpt w (toEAf D a)))
    (B.coord t w (X := (i, j)) (Y := (i + 1, j)) ⟨i.2.le, j.2.le⟩ ⟨i.2, j.2.le⟩ ((adjV₁ e u).map fun a => cpt w (toEAf D a)))ᵀ

def colsEq (t : T) {i j : Fin D.R.m} (e : Num G i j) (w : Pl D.host.E) :
    Fin ((spW G i j).rank + (spW₁ G i j).rank) ≃ (locGrid G t w).Cols i j :=
  e.symm.trans (Equiv.sumCongr (finCongr (rank_vertex G t w (X := (i, j + 1)) ⟨i.2.le, j.2⟩).symm)
    (finCongr (rank_vertex G t w (X := (i + 1, j)) ⟨i.2, j.2.le⟩).symm))


variable (G) in
theorem rankW (t : T) (i j : Fin D.R.m) (w : Pl D.host.E) : (spW G i j).rank = (locGrid G t w).rank (i + 1, j + 1) := by
  rw [rank_vertex G t w (X := ((i : ℕ) + 1, (j : ℕ) + 1)) ⟨Nat.succ_le_of_lt i.2, Nat.succ_le_of_lt j.2⟩]


variable (G) in
theorem rankW₁ (t : T) (i j : Fin D.R.m) (w : Pl D.host.E) : (spW₁ G i j).rank = (locGrid G t w).rank (i, j) := by
  rw [rank_vertex G t w (X := ((i : ℕ), (j : ℕ))) ⟨le_of_lt i.2, le_of_lt j.2⟩]

def IsPlaceIso {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (w : Pl D.host.E) (j : Fv D.host.F v ≃+* Kw w) : Prop :=
  ∀ a : AE D, j (piW τ a) = cpt w (toEAf D a)

def xiAt (w : Pl D.host.E) : Kw w := algebraMap D.host.E (Kw w) D.host.xi0

def basCols (B : Frames G) {i j : ℕ} (e : Num G i j) (w : Pl D.host.E) :
    Matrix (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Kw w) :=
  GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e (loc w (B.β i (j + 1))).val (-(loc w (B.β (i + 1) j)).val)

def IsDoublyCompatible (t : T) (i j : ℕ) (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) : Prop :=
  IsTied t i j e Bs Γ X ∧ Γ.V'.L = GlobalTheory.TripleSpaceW.conjSub (G.Λ (.grid i j))

end Grid

end GlobalTheory.FlipMatch

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical

noncomputable section

theorem GlobalTheory.ArchLineAct.intertwine_pair_left : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ γ ∈ Lines σ X, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (γ (Multiplicative.ofAdd t), 1)) f (T t f)) →
        ∃ A : ℝ → ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →ₗ[ℝ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)),
          (∀ w, Continuous fun t => A t w) ∧ (∀ s t, A (s + t) = (A s).comp (A t)) ∧ A 0 = LinearMap.id ∧
          ∀ (t : ℝ) (p q : (Fin n × Fin d → mixedEmbedding.mixedSpace F)) (f g : SInf F (Fin n × Fin d)),
            ⇑g = GlobalTheory.GaussLine.heisFun (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d)) p q ⇑f →
            ⇑(T t g) = GlobalTheory.GaussLine.heisFun (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d)) (A t (p, q)).1 (A t (p, q)).2 ⇑(T t f) := by
  intro F E _ _ _ _ _ σ _hcm n d X W M ψ χX χW om hψ _ _ _ _ _ _ _ _ hWeil γ hγ T hTact
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.ArchRest.exists_rest_arch (F := F) (Fin n × Fin d)
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hWeil
  have hRsh : ∀ x z, At (evI F) z → R (x + z) = R x := (hR 0).1
  let L : ℝ → Matrix (Fin n) (Fin d) (AE F E) →ₗ[AF F] Matrix (Fin n) (Fin d) (AE F E) :=
    fun t => GlobalTheory.ArchLineAct.lmulL (k := d) (mat (γ (Multiplicative.ofAdd t)))
  have hmat : ∀ g h : UA σ X.J, mat (g * h) = mat g * mat h := fun _ _ => rfl
  have hmat1 : mat (1 : UA σ X.J) = 1 := rfl
  refine ⟨fun t => GlobalTheory.ArchLineAct.archMap M.co (L t), fun w => ?_, fun s t => ?_, ?_, fun t p q f g hg => ?_⟩
  · have hm : Continuous fun t : ℝ => (mat (γ (Multiplicative.ofAdd t))) :=
      (Units.continuous_val.comp (continuous_subtype_val.comp (hγ.1.comp continuous_ofAdd)))
    set u := M.co.e.symm (GlobalTheory.ArchLineAct.archLift w.1, GlobalTheory.ArchLineAct.archLift w.2) with hu
    let Ru : Matrix (Fin n) (Fin n) (AE F E) →ₗ[AF F] Matrix (Fin n) (Fin d) (AE F E) :=
      { toFun := fun x => x * u, map_add' := fun x y => Matrix.add_mul x y u,
        map_smul' := fun c x => Matrix.smul_mul c x u }
    let K := M.co.e.toLinearMap ∘ₗ Ru
    haveI : IsModuleTopology (AF F) (Matrix (Fin n) (Fin n) (AE F E)) :=
      inferInstanceAs (IsModuleTopology (AF F) (Fin n → Fin n → AE F E))
    have hK : Continuous K := IsModuleTopology.continuous_of_linearMap K
    have hc : Continuous fun t : ℝ => M.co.e (L t u) := hK.comp hm
    show Continuous fun t : ℝ => (GlobalTheory.ArchLineAct.archPart (M.co.e (L t u)).1,
      GlobalTheory.ArchLineAct.archPart (M.co.e (L t u)).2)
    exact Continuous.prodMk
      (continuous_pi fun i => GlobalTheory.ArchLineAct.continuous_evI.comp ((continuous_apply i).comp (continuous_fst.comp hc)))
      (continuous_pi fun i => GlobalTheory.ArchLineAct.continuous_evI.comp ((continuous_apply i).comp (continuous_snd.comp hc)))
  · show GlobalTheory.ArchLineAct.archMap M.co (L (s + t)) =
      (GlobalTheory.ArchLineAct.archMap M.co (L s)).comp (GlobalTheory.ArchLineAct.archMap M.co (L t))
    rw [GlobalTheory.ArchLineAct.archMap_comp]
    congr 1
    refine LinearMap.ext fun x => ?_
    show mat (γ (Multiplicative.ofAdd (s + t))) * x =
      mat (γ (Multiplicative.ofAdd s)) * (mat (γ (Multiplicative.ofAdd t)) * x)
    rw [ofAdd_add, map_mul, hmat, Matrix.mul_assoc]
  · show GlobalTheory.ArchLineAct.archMap M.co (L 0) = LinearMap.id
    have hL : L 0 = LinearMap.id := by
      refine LinearMap.ext fun x => ?_
      show mat (γ (Multiplicative.ofAdd 0)) * x = x
      rw [ofAdd_zero, map_one, hmat1, Matrix.one_mul]
    rw [hL, GlobalTheory.ArchLineAct.archMap_id]
  · set u := M.co.e.symm (GlobalTheory.ArchLineAct.archLift p, GlobalTheory.ArchLineAct.archLift q) with hu
    have hue : M.co.e u = (GlobalTheory.ArchLineAct.archLift p, GlobalTheory.ArchLineAct.archLift q) :=
      LinearEquiv.apply_symm_apply _ _
    have hu' : At (evI F) (L t u) := GlobalTheory.ArchLineAct.at_lin _ (GlobalTheory.ArchLineAct.at_symm _ p q)
    have hue' := GlobalTheory.ArchLineAct.coord_eq M.co hu'
    have himpl := hW.impl (γ (Multiplicative.ofAdd t), (1 : UA σ W.J)) u (tens (evI F) (⇑f) R) (hR f).2
    have hact : GlobalTheory.WeilM.actAB (cA σ) (γ (Multiplicative.ofAdd t), (1 : UA σ W.J)) u = L t u := by
      show (mat (γ (Multiplicative.ofAdd t))) * u * ((1 : UA σ W.J) : GL (Fin d) (AE F E)).1ᵀ =
        mat (γ (Multiplicative.ofAdd t)) * u
      rw [show ((1 : UA σ W.J) : GL (Fin d) (AE F E)).1 = 1 from rfl, Matrix.transpose_one, Matrix.mul_one]
    rw [hact, GlobalTheory.ArchLineAct.rho_tens hψ M.co u p q hue (⇑f) R hRsh, ← hg, hTact t g R (hR g),
      hTact t f R (hR f), GlobalTheory.ArchLineAct.rho_tens hψ M.co (L t u) _ _ hue' _ R hRsh] at himpl
    funext x
    have h := congrFun himpl (GlobalTheory.ArchLineAct.archLift x)
    rw [GlobalTheory.ArchLineAct.tens_archLift _ R hRsh, GlobalTheory.ArchLineAct.tens_archLift _ R hRsh] at h
    exact mul_right_cancel₀ hR0 h

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical

noncomputable section

theorem GlobalTheory.ArchLineAct.intertwine_pair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ γ ∈ Lines σ W, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) f (T t f)) →
        ∃ A : ℝ → ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →ₗ[ℝ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)),
          (∀ w, Continuous fun t => A t w) ∧ (∀ s t, A (s + t) = (A s).comp (A t)) ∧ A 0 = LinearMap.id ∧
          ∀ (t : ℝ) (p q : (Fin n × Fin d → mixedEmbedding.mixedSpace F)) (f g : SInf F (Fin n × Fin d)),
            ⇑g = GlobalTheory.GaussLine.heisFun (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d)) p q ⇑f →
            ⇑(T t g) = GlobalTheory.GaussLine.heisFun (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d)) (A t (p, q)).1 (A t (p, q)).2 ⇑(T t f) := by
  intro F E _ _ _ _ _ σ _hcm n d X W M ψ χX χW om hψ _ _ _ _ _ _ _ _ hWeil γ hγ T hTact
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.ArchRest.exists_rest_arch (F := F) (Fin n × Fin d)
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hWeil
  have hRsh : ∀ x z, At (evI F) z → R (x + z) = R x := (hR 0).1
  let L : ℝ → Matrix (Fin n) (Fin d) (AE F E) →ₗ[AF F] Matrix (Fin n) (Fin d) (AE F E) :=
    fun t => GlobalTheory.ArchLineAct.rmulT (mat (γ (Multiplicative.ofAdd t)))
  have hmat : ∀ g h : UA σ W.J, mat (g * h) = mat g * mat h := fun _ _ => rfl
  have hmat1 : mat (1 : UA σ W.J) = 1 := rfl
  refine ⟨fun t => GlobalTheory.ArchLineAct.archMap M.co (L t), fun w => ?_, fun s t => ?_, ?_, fun t p q f g hg => ?_⟩
  · have hm : Continuous fun t : ℝ => (mat (γ (Multiplicative.ofAdd t)))ᵀ :=
      (Units.continuous_val.comp (continuous_subtype_val.comp (hγ.1.comp continuous_ofAdd))).matrix_transpose
    set u := M.co.e.symm (GlobalTheory.ArchLineAct.archLift w.1, GlobalTheory.ArchLineAct.archLift w.2) with hu
    let K := M.co.e.toLinearMap ∘ₗ (GlobalTheory.ArchLineAct.lmulL (k := d) u)
    haveI : IsModuleTopology (AF F) (Matrix (Fin d) (Fin d) (AE F E)) :=
      inferInstanceAs (IsModuleTopology (AF F) (Fin d → Fin d → AE F E))
    have hK : Continuous K := IsModuleTopology.continuous_of_linearMap K
    have hc : Continuous fun t : ℝ => M.co.e (L t u) := hK.comp hm
    show Continuous fun t : ℝ => (GlobalTheory.ArchLineAct.archPart (M.co.e (L t u)).1,
      GlobalTheory.ArchLineAct.archPart (M.co.e (L t u)).2)
    exact Continuous.prodMk
      (continuous_pi fun i => GlobalTheory.ArchLineAct.continuous_evI.comp ((continuous_apply i).comp (continuous_fst.comp hc)))
      (continuous_pi fun i => GlobalTheory.ArchLineAct.continuous_evI.comp ((continuous_apply i).comp (continuous_snd.comp hc)))
  · show GlobalTheory.ArchLineAct.archMap M.co (L (s + t)) =
      (GlobalTheory.ArchLineAct.archMap M.co (L s)).comp (GlobalTheory.ArchLineAct.archMap M.co (L t))
    rw [GlobalTheory.ArchLineAct.archMap_comp]
    congr 1
    refine LinearMap.ext fun x => ?_
    show x * (mat (γ (Multiplicative.ofAdd (s + t))))ᵀ =
      (x * (mat (γ (Multiplicative.ofAdd t)))ᵀ) * (mat (γ (Multiplicative.ofAdd s)))ᵀ
    rw [ofAdd_add, map_mul, hmat, Matrix.transpose_mul, Matrix.mul_assoc]
  · show GlobalTheory.ArchLineAct.archMap M.co (L 0) = LinearMap.id
    have hL : L 0 = LinearMap.id := by
      refine LinearMap.ext fun x => ?_
      change x * (mat (γ (Multiplicative.ofAdd 0)))ᵀ = LinearMap.id x
      rw [LinearMap.id_apply, ofAdd_zero, map_one, hmat1, Matrix.transpose_one, Matrix.mul_one]
    rw [hL, GlobalTheory.ArchLineAct.archMap_id]
  · set u := M.co.e.symm (GlobalTheory.ArchLineAct.archLift p, GlobalTheory.ArchLineAct.archLift q) with hu
    have hue : M.co.e u = (GlobalTheory.ArchLineAct.archLift p, GlobalTheory.ArchLineAct.archLift q) :=
      LinearEquiv.apply_symm_apply _ _
    have hu' : At (evI F) (L t u) := GlobalTheory.ArchLineAct.at_lin _ (GlobalTheory.ArchLineAct.at_symm _ p q)
    have hue' := GlobalTheory.ArchLineAct.coord_eq M.co hu'
    have himpl := hW.impl (1, γ (Multiplicative.ofAdd t)) u (tens (evI F) (⇑f) R) (hR f).2
    have hact : GlobalTheory.WeilM.actAB (cA σ) ((1 : UA σ X.J), γ (Multiplicative.ofAdd t)) u = L t u := by
      show ((1 : UA σ X.J) : GL (Fin n) (AE F E)).1 * u * (mat (γ (Multiplicative.ofAdd t)))ᵀ =
        u * (mat (γ (Multiplicative.ofAdd t)))ᵀ
      rw [show ((1 : UA σ X.J) : GL (Fin n) (AE F E)).1 = 1 from rfl, Matrix.one_mul]
    rw [hact, GlobalTheory.ArchLineAct.rho_tens hψ M.co u p q hue (⇑f) R hRsh, ← hg, hTact t g R (hR g),
      hTact t f R (hR f), GlobalTheory.ArchLineAct.rho_tens hψ M.co (L t u) _ _ hue' _ R hRsh] at himpl
    funext x
    have h := congrFun himpl (GlobalTheory.ArchLineAct.archLift x)
    rw [GlobalTheory.ArchLineAct.tens_archLift _ R hRsh, GlobalTheory.ArchLineAct.tens_archLift _ R hRsh] at h
    exact mul_right_cancel₀ hR0 h

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinZeta.AbsZeta

theorem trivial_isUnitarisable (G : Type) [Group G] : IsUnitarisable (Representation.trivial ℂ G ℂ) := by
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun a b => a * starRingEnd ℂ b)
    (fun a a' b => add_mul a a' _) (fun c a b => by simp [smul_eq_mul, mul_assoc])
    (fun a b b' => by simp [mul_add]) (fun c a b => by simp [smul_eq_mul]; ring), ?_, ?_, ?_⟩
  · intro a b
    simp [mul_comm]
  · intro a ha
    simpa [Complex.mul_conj, Complex.normSq_pos] using ha
  · intro g a b
    simp

theorem kerGL_norm {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {r N : ℕ} {z : ℂˣ}
    {φ : GL (Fin r) (w.adicCompletion E) → ℂ} (hz : ‖(z : ℂ)‖ = 1) (hφ : KerGL w N z φ) :
    KerGL w N 1 (fun g => ((‖φ g‖ : ℝ) : ℂ)) := by
  intro ϖ hϖ d t ht k₁ hk₁ k₂ hk₂
  have hq : ∀ m : ℤ, (qV E w : ℂ) ^ (-((N : ℂ) / 2) * (m : ℂ)) =
      (((qV E w : ℝ) ^ (-((N : ℝ) / 2) * (m : ℝ)) : ℝ) : ℂ) := by
    intro m
    rw [Complex.ofReal_cpow (by positivity)]
    push_cast
    ring_nf
  have hpos : 0 ≤ (qV E w : ℝ) ^ (-((N : ℝ) / 2) * ((∑ i, |d i| : ℤ) : ℝ)) := by positivity
  beta_reduce
  rw [hφ ϖ hϖ d t ht k₁ hk₁ k₂ hk₂, hq]
  simp [norm_zpow, hz, Complex.norm_real, Real.norm_of_nonneg hpos]
  positivity

end GlobalTheory.FinZeta.AbsZeta


open GlobalTheory.FinZeta.AbsZeta in
theorem GlobalTheory.FinZeta.AbsZeta.hasSum_norm_kerGL : GlobalTheory.Published.UnramifiedDoublingGL → ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (r t : ℕ), r ≤ t → ∀ (z : ℂˣ) (φ : GL (Fin r) (w.adicCompletion E) → ℂ), ‖(z : ℂ)‖ = 1 → KerGL w (r + t) z φ → ∃ B : Multiset ℂˣ, B.card = r ∧ (∀ β ∈ B, ‖(β : ℂ)‖ ≤ (qV E w : ℝ) ^ (((r : ℝ) - 1) / 2) ∧ ‖((β⁻¹ : ℂˣ) : ℂ)‖ ≤ (qV E w : ℝ) ^ (((r : ℝ) - 1) / 2)) ∧ HasSum (fun a : GL (Fin r) (w.adicCompletion E) ⧸ KGL w (n := r) => ((‖φ a.out‖ : ℝ) : ℂ)) (eulerFac B (npow w (-((1 + (t : ℂ)) / 2))) * eulerFac (B.map fun β => β⁻¹) (npow w (-((1 + (t : ℂ)) / 2))) * ∏ i ∈ Finset.Ioc t (r + t), (1 - ((qV E w : ℂ) ^ i)⁻¹)) := by
  intro H E _ _ w r t hrt z φ hz hφ
  obtain ⟨B, hB, hbd⟩ := GlobalTheory.T.exists_satakeParam_trivialBound_unitaryGL E w r ℂ (Representation.trivial ℂ _ ℂ) (trivial_isUnitarisable _) 1 one_ne_zero
    (GlobalTheory.LGrp.mem_fixed.2 fun _ _ => rfl) (fun h _ => ⟨_, (mul_one _).symm⟩)
  have hs := GlobalTheory.T.unramified_zeta_sum_GL_cosets H E w r t hrt 1 (fun g => ((‖φ g‖ : ℝ) : ℂ)) (by simp) (kerGL_norm hz hφ) ℂ
    (Representation.trivial ℂ _ ℂ) 1 B hB hbd LinearMap.id ⟨1, fun g => by simp⟩
  refine ⟨B, ?_, hbd, ?_⟩
  · have hB' := hB
    unfold IsSatVecGL at hB'
    exact hB'.2.2.1
  · simpa using hs
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord GlobalTheory.ArchLine
open scoped Matrix Classical SchwartzMap
open MeasureTheory

namespace GlobalTheory.ArchimedeanLineL2

theorem archOp_lintegral_eq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    M.IsWeil ψ χX χW om → (∀ h ∈ UAt σ W (evI F), ∀ f : SInf F (Fin n × Fin d), ∃ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (1, h)) ⇑f ⇑f₁) →
    ∀ h ∈ UAt σ W (evI F), ∀ (N : ℕ) (C : (Fin n × Fin d → mixedEmbedding.mixedSpace F) ≃L[ℝ] EuclideanSpace ℝ (Fin N))
      (f : SInf F (Fin n × Fin d)),
      ∫⁻ x, ‖archOp om h f (C.symm x)‖ₑ ^ 2 = ∫⁻ x, ‖f (C.symm x)‖ₑ ^ 2 := by
  intro F E _ _ _ _ _ σ n d X W M ψ χX χW om hW hex h hh N C f
  haveI := GlobalTheory.ArchimedeanUnitaryL2.opensMeasurable F (Fin n × Fin d)
  set μ : Measure (Fin n × Fin d → mixedEmbedding.mixedSpace F) := Measure.map C.symm volume with hμ
  haveI : μ.IsAddHaarMeasure := C.symm.isAddHaarMeasure_map volume
  obtain ⟨g, hg, hg0⟩ : ∃ g : (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) → ℂ,
      g ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) ∧ g 0 ≠ 0 := by
    refine ⟨_, GlobalTheory.SchANonzero.indicator_intPts_mem_SB F _, ?_⟩
    have h0 : (0 : Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) ∈ GlobalTheory.SchANonzero.intPts F (Fin n × Fin d) :=
      fun i _ v => zero_mem (v.adicCompletionIntegers F)
    rw [Set.indicator_of_mem h0]
    exact one_ne_zero
  obtain ⟨μA, hμA, c, hc0, hct, hc⟩ := GlobalTheory.ArchimedeanUnitaryL2.exists_haar F _ μ g hg hg0
  let r : (Fin n × Fin d → AF F) → ℂ := fun x => g fun i => (x i).2
  have hS : ∀ f' : SInf F (Fin n × Fin d), tens (evI F) (⇑f') r ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) :=
    fun f' => Submodule.subset_span ⟨f', g, hg, rfl⟩
  have hr : ∀ x z, At (evI F) z → r (x + z) = r x := by
    intro x z hz
    refine congrArg g (funext fun i => ?_)
    show (x i).2 + (z i).2 = (x i).2
    rw [GlobalTheory.ArchimedeanUnitaryL2.snd_eq_zero hz i, add_zero]
  have hU := (IsUWeilPair.isUSplitting hW).unit μA hμA (1, h) (tens (evI F) (⇑f) r) (hS f)
  have hAct : om (1, h) (tens (evI F) (⇑f) r) = tens (evI F) (⇑(archOp om h f)) r :=
    acts_archOp om h f (hex h hh f) r ⟨hr, hS f⟩
  rw [hAct] at hU
  have h1 := ((hc (archOp om h f)).symm.trans hU).trans (hc f)
  have h2 := (ENNReal.mul_right_inj hc0 hct).1 h1
  rw [hμ, lintegral_map ((archOp om h f).continuous.measurable.enorm.pow_const 2) C.symm.continuous.measurable,
    lintegral_map (f.continuous.measurable.enorm.pow_const 2) C.symm.continuous.measurable] at h2
  exact h2

end GlobalTheory.ArchimedeanLineL2

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

theorem _root_.GlobalTheory.T.infiniteHeight_transposeGramUnitary_le : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E} (hJ : J = D.host.xi0 • reindex e e X.gramᵀ), ∃ C : NNReal, ∀ h : GA D X, ∏ w, GlobalTheory.AdelicU.htInf D.host.F w (Formalism.UG.bc (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) (kapX X e hJ h).1) ≤ C * ∏ τ, GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.infHt θ X τ h := by
  first | exact @GlobalTheory.HtInfKapX.htInf_kapX_le | exact GlobalTheory.HtInfKapX.htInf_kapX_le | (intros; apply GlobalTheory.HtInfKapX.htInf_kapX_le <;> assumption)
end

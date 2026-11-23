module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle103
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle334
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
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section

namespace GlobalTheory.PolMatchLin

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

section Ext
variable {ι : Type} (P : ι → Type) [∀ v, AddCommGroup (P v)] [∀ v, Module ℂ (P v)]


open Classical in
def extFam {S T : Finset ι} (w : ∀ v, P v) (g : ∀ v : S, P v) : ∀ v : T, P v :=
  fun v => if h : v.1 ∈ S then g ⟨v.1, h⟩ else w v.1

theorem extFam_update {S T : Finset ι} (hST : S ⊆ T) (w : ∀ v, P v) [DecidableEq S] [DecidableEq T]
    (g : ∀ v : S, P v) (i : S) (z : P i) :
    extFam P (T := T) w (Function.update g i z) = Function.update (extFam P w g) ⟨i.1, hST i.2⟩ z := by
  funext v
  by_cases hv : v = ⟨i.1, hST i.2⟩
  · subst hv
    simp [extFam, i.2]
  · rw [Function.update_of_ne hv]
    unfold extFam
    split_ifs with h
    · rw [Function.update_of_ne]
      intro e
      apply hv
      apply Subtype.ext
      simp [← e]
    · rfl

def extML {S T : Finset ι} (hST : S ⊆ T) (w : ∀ v, P v) :
    MultilinearMap (RingHom.id ℂ) (fun v : S => P v) (PiTensorProduct ℂ fun v : T => P v) where
  toFun g := PiTensorProduct.tprod ℂ (extFam P w g)
  map_update_add' g i x y := by
    classical
    simp only [extFam_update P hST]
    exact MultilinearMap.map_update_add _ _ _ _ _
  map_update_smul' g i c x := by
    classical
    simp only [extFam_update P hST]
    exact MultilinearMap.map_update_smul _ _ _ _ _

def extL {S T : Finset ι} (hST : S ⊆ T) (w : ∀ v, P v) :
    (PiTensorProduct ℂ fun v : S => P v) →ₗ[ℂ] PiTensorProduct ℂ fun v : T => P v :=
  PiTensorProduct.lift (extML P hST w)

theorem extL_tprod {S T : Finset ι} (hST : S ⊆ T) (w : ∀ v, P v) (g : ∀ v : S, P v) (g' : ∀ v : T, P v)
    (h1 : ∀ (v : T) (h : v.1 ∈ S), g' v = g ⟨v.1, h⟩) (h2 : ∀ v : T, v.1 ∉ S → g' v = w v.1) :
    extL P hST w (PiTensorProduct.tprod ℂ g) = PiTensorProduct.tprod ℂ g' := by
  unfold extL
  rw [PiTensorProduct.lift.tprod]
  show PiTensorProduct.tprod ℂ (extFam P w g) = _
  congr 1
  funext v
  unfold extFam
  split_ifs with h
  · exact (h1 v h).symm
  · exact (h2 v h).symm

end Ext

section Main

theorem pure_smul {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (c : ℂ) (f : SInf F κ)
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c • f) φ = c • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, smul_eq_mul, mul_assoc]

theorem transport {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W)
    (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a') (hF : IsFinMaps B G X om om' Rf)
    {T₁ T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))} (hX : X.T ⊆ T₁) (hST : T₁ ⊆ T) {m m' : ℕ} (f : Fin m → SInf F (Fin a × Fin (a + a')))
    (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin a × Fin (a + a') → Fv F v) → ℂ) (f' : Fin m' → SInf F (Fin a' × Fin (a + a')))
    (φ' : Fin m' → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin a' × Fin (a + a') → Fv F v) → ℂ)
    (hφ : ∀ i, ∀ v ∉ T₁, φ i v = G.M.vac v) (hφ' : ∀ j, ∀ v ∉ T₁, φ' j v = G.M'.vac v)
    (he : ∑ i, R.p (f i) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T₁ => Rf.p v (φ i v)) =
      ∑ j, R.p' (f' j) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T₁ => Rf.p' v (φ' j v))) :
    ∑ i, R.p (f i) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf.p v (φ i v)) =
      ∑ j, R.p' (f' j) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf.p' v (φ' j v)) := by
  set w : ∀ v, Rf.Pi v := fun v => Rf.p v (G.M.vac v)
  have k1 : ∀ i, extL Rf.Pi hST w (PiTensorProduct.tprod ℂ fun v : T₁ => Rf.p v (φ i v)) =
      PiTensorProduct.tprod ℂ fun v : T => Rf.p v (φ i v) := fun i =>
    extL_tprod _ _ _ _ _ (fun v h => rfl) (fun v h => by simp only [w]; rw [hφ i v h])
  have k2 : ∀ j, extL Rf.Pi hST w (PiTensorProduct.tprod ℂ fun v : T₁ => Rf.p' v (φ' j v)) =
      PiTensorProduct.tprod ℂ fun v : T => Rf.p' v (φ' j v) := fun j =>
    extL_tprod _ _ _ _ _ (fun v h => rfl) (fun v h => by
      simp only [w]; rw [hφ' j v h, (hF.sph v.1 (fun hv => h (hX hv))).1])
  have := congrArg (LinearMap.lTensor R.Pi (extL Rf.Pi hST w)) he

  simp only [map_sum, LinearMap.lTensor_tmul, k1, k2] at this
  exact this

theorem polMatch_linear : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ} (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsFinMaps B G X om om' Rf → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf 0 0 ∧ ∀ (Φ Ψ : (Fin a × Fin (a + a') → AF F) → ℂ) (Φ' Ψ' : (Fin a' × Fin (a + a') → AF F) → ℂ) (c : ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf Φ Φ' → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf Ψ Ψ' → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf (Φ + c • Ψ) (Φ' + c • Ψ') := by
  intro F E _ _ _ _ _ σ a a' B G X om om' R Rf hF
  refine ⟨?_, ?_⟩
  · refine ⟨X.T, subset_rfl, 0, 0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, ?_, ?_, ?_, ?_, ?_⟩ <;> simp
  · rintro Φ Ψ Φ' Ψ' c ⟨T₁, hX₁, m₁, m₁', f₁, φ₁, f₁', φ₁', h1, h1', rfl, rfl, e1⟩
      ⟨T₂, hX₂, m₂, m₂', f₂, φ₂, f₂', φ₂', h2, h2', rfl, rfl, e2⟩
    classical
    have s1 : T₁ ⊆ T₁ ∪ T₂ := Finset.subset_union_left
    have s2 : T₂ ⊆ T₁ ∪ T₂ := Finset.subset_union_right
    refine ⟨T₁ ∪ T₂, hX₁.trans s1, m₁ + m₂, m₁' + m₂', Fin.append f₁ (fun j => c • f₂ j), Fin.append φ₁ φ₂,
      Fin.append f₁' (fun j => c • f₂' j), Fin.append φ₁' φ₂', ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · simp only [Fin.append_left]
        exact ⟨(h1 i).1, (h1 i).2.1, fun v hv => (h1 i).2.2 v (fun h => hv (s1 h))⟩
      · simp only [Fin.append_right]
        exact ⟨Submodule.smul_mem _ c (h2 j).1, (h2 j).2.1, fun v hv => (h2 j).2.2 v (fun h => hv (s2 h))⟩
    · intro i
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · simp only [Fin.append_left]
        exact ⟨(h1' i).1, (h1' i).2.1, fun v hv => (h1' i).2.2 v (fun h => hv (s1 h))⟩
      · simp only [Fin.append_right]
        exact ⟨Submodule.smul_mem _ c (h2' j).1, (h2' j).2.1, fun v hv => (h2' j).2.2 v (fun h => hv (s2 h))⟩
    · rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, pure_smul, Finset.smul_sum]
    · rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, pure_smul, Finset.smul_sum]
    · rw [Fin.sum_univ_add, Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, map_smul, ← TensorProduct.smul_tmul', ← Finset.smul_sum]
      rw [transport B G X om om' R Rf hF hX₁ s1 f₁ φ₁ f₁' φ₁' (fun i v hv => (h1 i).2.2 v hv)
          (fun j v hv => (h1' j).2.2 v hv) e1,
        transport B G X om om' R Rf hF hX₂ s2 f₂ φ₂ f₂' φ₂' (fun i v hv => (h2 i).2.2 v hv)
          (fun j v hv => (h2' j).2.2 v hv) e2]

end Main

end GlobalTheory.PolMatchLin
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

open Filter Topology

noncomputable section
open scoped Classical

namespace GlobalTheory.LineAdd

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

section
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem tens_add_smul (f s : SInf F κ) (t : ℝ) (r : (κ → AF F) → ℂ) :
    tens (evI F) ⇑(f + t • s) r = tens (evI F) ⇑f r + (t : ℂ) • tens (evI F) ⇑s r := by
  funext x
  simp only [tens, SchwartzMap.add_apply, SchwartzMap.smul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Complex.real_smul]
  ring

theorem hasDerivAt_of_curve {T : ℝ → ((κ → AF F) → ℂ) → (κ → AF F) → ℂ} {f g : SInf F κ} {c : ℝ → SInf F κ}
    {r : (κ → AF F) → ℂ} (hc : ∀ t, T t (tens (evI F) ⇑f r) = tens (evI F) ⇑(c t) r) (hc0 : c 0 = f)
    (hlim : Tendsto (fun t : ℝ => t⁻¹ • (c t - f)) (𝓝[≠] 0) (𝓝 g)) :
    ∀ x, HasDerivAt (fun t => T t (tens (evI F) ⇑f r) x) (tens (evI F) ⇑g r x) 0 := by
  intro x
  have ev : ∀ y : κ → mixedEmbedding.mixedSpace F, Continuous fun s : SInf F κ => s y := by
    intro y
    have h1 := (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ).continuous
    exact (continuous_eval_const (F := BoundedContinuousFunction (κ → mixedEmbedding.mixedSpace F) ℂ) y).comp h1
  have e : (fun t => T t (tens (evI F) ⇑f r) x) = fun t => tens (evI F) ⇑(c t) r x := by
    funext t; rw [hc t]
  rw [e, hasDerivAt_iff_tendsto_slope]
  refine ((((ev _).tendsto g).comp hlim).mul_const (r x)).congr' (Filter.Eventually.of_forall fun t => ?_)
  simp only [Function.comp_apply, tens]
  rw [slope_def_module, hc0]
  simp only [SchwartzMap.smul_apply, SchwartzMap.sub_apply, sub_zero, Complex.real_smul, smul_eq_mul]
  ring

end

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}

theorem om_prod_one (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd) (a b : UA σ Y.J) (Φ : (Fin n × Fin d → AF F) → ℂ) :
    om (a * b, 1) Φ = om (a, 1) (om (b, 1) Φ) := by
  have e : ((a * b, (1 : UA σ Wd.J)) : UA σ Y.J × UA σ Wd.J) = (a, 1) * (b, 1) := by
    simp [Prod.mk_mul_mk]
  rw [e, map_mul, Module.End.mul_apply]

theorem om_one_one (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd) (Φ : (Fin n × Fin d → AF F) → ℂ) :
    om ((1 : UA σ Y.J), (1 : UA σ Wd.J)) Φ = Φ := by
  rw [show ((1 : UA σ Y.J), (1 : UA σ Wd.J)) = (1 : UA σ Y.J × UA σ Wd.J) from rfl, map_one, Module.End.one_apply]

end GlobalTheory.LineAdd

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
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.ThetaLineDeriv
open GlobalTheory.WeilM GlobalTheory.LFun Filter Topology
open scoped Classical

theorem rho_sum {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    {m : ℕ} (φ : Fin m → (Fin n × Fin d → AF F) → ℂ) :
    M.co.rho ψ u (∑ i, φ i) = ∑ i, M.co.rho ψ u (φ i) := by
  funext x
  simp only [Darboux.rho, schr, Finset.sum_apply, Finset.mul_sum]

theorem rho_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    M.co.rho ψ u 0 = 0 := by
  funext x
  simp only [Darboux.rho, schr, Pi.zero_apply, mul_zero]

private theorem hasDerivAt_clm_comp_of_tendsto_slope {κ : Type} [Fintype κ] {F : Type} [Field F] [NumberField F] (c : ℝ → SInf F κ)
    (f c' : SInf F κ) (hc0 : c 0 = f) (hl : Tendsto (fun t : ℝ => t⁻¹ • (c t - f)) (𝓝[≠] 0) (𝓝 c'))
    (T : SInf F κ →L[ℂ] ℂ) : HasDerivAt (fun t => T (c t)) (T c') 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hT := ((T.restrictScalars ℝ).continuous.tendsto c').comp hl
  refine hT.congr fun t => ?_
  simp only [Function.comp_apply, slope_def_module, sub_zero, hc0]
  rw [← map_sub]
  exact (T.restrictScalars ℝ).map_smul t⁻¹ (c t - f)

theorem hasDerivAt_eval {κ : Type} [Fintype κ] {F : Type} [Field F] [NumberField F] (c : ℝ → SInf F κ) (f c' : SInf F κ)
    (hc0 : c 0 = f) (hl : Tendsto (fun t : ℝ => t⁻¹ • (c t - f)) (𝓝[≠] 0) (𝓝 c')) (y : κ → mixedEmbedding.mixedSpace F) :
    HasDerivAt (fun t => c t y) (c' y) 0 := by
  have h := hasDerivAt_clm_comp_of_tendsto_slope c f c' hc0 hl
    ((BoundedContinuousFunction.evalCLM ℂ y).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ))
  simpa using h

theorem hasDerivAt_clm {κ : Type} [Fintype κ] {F : Type} [Field F] [NumberField F] (c : ℝ → SInf F κ) (f c' : SInf F κ)
    (hc0 : c 0 = f) (hl : Tendsto (fun t : ℝ => t⁻¹ • (c t - f)) (𝓝[≠] 0) (𝓝 c')) (T : SInf F κ →L[ℂ] ℂ) :
    HasDerivAt (fun t => T (c t)) (T c') 0 :=
  hasDerivAt_clm_comp_of_tendsto_slope c f c' hc0 hl T

end GlobalTheory.ThetaLineDeriv

namespace GlobalTheory.ThetaLineDeriv
open GlobalTheory.WeilM GlobalTheory.LFun Filter Topology
open scoped Classical

end GlobalTheory.ThetaLineDeriv
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

noncomputable section

namespace GlobalTheory.HeisOrbit

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def archCo {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} (d : GlobalTheory.WeilM.Darboux B κ) (w : W) :
    (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F) :=
  (fun i => evI F ((d.e w).1 i), fun i => evI F ((d.e w).2 i))

def dOp (P Q : κ → mixedEmbedding.mixedSpace F) (h : (κ → mixedEmbedding.mixedSpace F) → ℂ)
    (y : κ → mixedEmbedding.mixedSpace F) : ℂ :=
  fderiv ℝ h y P - 2 * Real.pi * Complex.I *
    ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * Q i) : ℝ) : ℂ) * h y

end GlobalTheory.HeisOrbit
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.RegGood

theorem isTriple_atPlace {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E} {a a' : ℕ} {G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a'}
    {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E} {om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W} {om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om') (v : HeightOneSpectrum (𝓞 F)) (t : E →ₐ[F] Fv F v) (hv : X.Good v) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple { B with v₁ := v, τ₁ := t } G X om om' :=
  { h with
    base := { h.base with }
    geo := { h.geo with hV := { h.geo.hV with }, hV' := { h.geo.hV' with }, hW := { h.geo.hW with } }
    chars := { h.chars with good := hv } }

end GlobalTheory.RegGood

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
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

open GlobalTheory.WeilM

namespace GlobalTheory.ArchLineCont

theorem continuous_apply : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.W,
    ∀ T : ℝ → SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')),
    (∀ (t : ℝ) (f : SInf F (Fin a × Fin (a + a'))), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) f (T t f)) →
    ∀ (f : SInf F (Fin a × Fin (a + a'))) (x : Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F), Continuous fun t => T t f x := by
  intro F E _ _ _ _ _ σ a a' B G X om om' hT γ hγ T hAct f x
  classical
  let κ := Fin a × Fin (a + a')
  let g₀ : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := (GlobalTheory.SchANonzero.intPts F κ).indicator 1
  have hg₀ : g₀ ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) := GlobalTheory.SchANonzero.indicator_intPts_mem_SB F κ
  let r₀ : (κ → AF F) → ℂ := fun y => g₀ (fun i => (y i).2)
  have htens : ∀ h : SInf F κ, tens (evI F) (⇑h) r₀ = pureA F (⇑h) g₀ := fun h => rfl
  have hRest : ∀ h : SInf F κ, Rest (evI F) (⇑h) r₀ := by
    intro h
    refine ⟨fun y z hz => ?_, ?_⟩
    · have h2 : ∀ i, (z i).2 = 0 := by
        intro i
        have hu := hz ((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)) (by
          show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : InfiniteAdeleRing F) = 0
          exact map_zero _)
        have h1 : (1 : FiniteAdeleRing (𝓞 F) F) * (z i).2 = 0 := congrArg Prod.snd (congrFun hu i)
        rwa [one_mul] at h1
      show g₀ (fun i => (y i + z i).2) = g₀ (fun i => (y i).2)
      congr 1
      funext i
      show (y i).2 + (z i).2 = (y i).2
      rw [h2 i, add_zero]
    · rw [htens]
      exact Submodule.subset_span ⟨h, g₀, hg₀, rfl⟩
  let xh : κ → AF F := fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i), (0 : FiniteAdeleRing (𝓞 F) F))
  let l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj xh
  have hxh : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (xh i).1) = x := by
    funext i
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (x i)
  have hg0 : g₀ (fun i => (xh i).2) = 1 := by
    have hm : (fun i => (xh i).2) ∈ GlobalTheory.SchANonzero.intPts F κ := fun i _ v => by
      show (0 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F
      exact zero_mem (v.adicCompletionIntegers F)
    simp only [g₀, Set.indicator_of_mem hm, Pi.one_apply]
  have hl : l ∈ (adeleClass F).adm κ := by
    intro g _
    refine ⟨g (fun i => (xh i).2) • ((BoundedContinuousFunction.evalCLM ℂ x).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)), fun h => ?_⟩
    show pureA F (⇑h) g xh = _
    simp only [pureA, hxh, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      BoundedContinuousFunction.evalCLM_apply, SchwartzMap.toBoundedContinuousFunctionCLM_apply, smul_eq_mul]
    exact mul_comm _ _
  have hφ : pureA F (⇑f) g₀ ∈ (adeleClass F).sp κ := Submodule.subset_span ⟨f, g₀, hg₀, rfl⟩
  have hc := hT.weil.2.2 l hl _ hφ
  have key : (fun t : ℝ => T t f x) =
      (fun p => l (om p (pureA F (⇑f) g₀))) ∘ (fun t : ℝ => ((1 : UA σ G.V.J), γ (Multiplicative.ofAdd t))) := by
    funext t
    have e := hAct t f r₀ (hRest f)
    rw [htens, htens] at e
    simp only [Function.comp_apply]
    rw [e]
    show _ = pureA F _ g₀ xh
    simp only [pureA, hxh, hg0, mul_one]
  rw [key]
  exact hc.comp (continuous_const.prodMk (hγ.1.comp continuous_ofAdd))

end GlobalTheory.ArchLineCont
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.weil_model_projection_factorisation : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n d : ℕ}
    (Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Z) (ψ : AddChar (AF F) ℂ),
    M.IsGood ψ → ∀ (P : Type) [AddCommGroup P] [Module ℂ P] (pr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d) →ₗ[ℂ] P)
    (N : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F) → Type) [∀ v, AddCommGroup (N v)] [∀ v, Module ℂ (N v)]
    (pv : ∀ v, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] N v) (s : ∀ v, N v),
    (∀ᶠ v in Filter.cofinite, pv v (M.vac v) = s v) →
    ∃ q : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] P ⊗[ℂ] GlobalTheory.SmallThetaModules.RTens s,
      ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
        q (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = pr f ⊗ₜ GlobalTheory.SmallThetaModules.pureT s (fun v => pv v (φ v)) := by
  first | exact @GlobalTheory.PureLift.exists_pureLift | exact GlobalTheory.PureLift.exists_pureLift | (intros; apply GlobalTheory.PureLift.exists_pureLift <;> assumption)
end

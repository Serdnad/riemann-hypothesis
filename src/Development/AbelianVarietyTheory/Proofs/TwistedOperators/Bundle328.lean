module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle309
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle744
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle811
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle094
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefIntegralEq
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle310
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1830
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle089
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle187
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle312
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH
open scoped TensorProduct InnerProductSpace Classical Kronecker
open GlobalTheory.Chain.IoLift

noncomputable section

namespace GlobalTheory.Chain.IoLift.UImg

variable {p q : ℕ}

def sumAct (M : GKMod p q) (Y : Type) : Mat p q →ₗ[ℂ] Module.End ℂ (Y →₀ M.V) where
  toFun X := Finsupp.mapRange.linearMap (M.act X)
  map_add' X X' := by
    refine LinearMap.ext fun v => Finsupp.ext fun y => ?_
    simp
  map_smul' c X := by
    refine LinearMap.ext fun v => Finsupp.ext fun y => ?_
    simp

theorem sumAct_apply (M : GKMod p q) (Y : Type) (X : Mat p q) (v : Y →₀ M.V) (y : Y) :
    sumAct M Y X v y = M.act X (v y) := by
  simp [sumAct]

theorem sumAct_single (M : GKMod p q) (Y : Type) (X : Mat p q) (y : Y) (x : M.V) :
    sumAct M Y X (Finsupp.single y x) = Finsupp.single y (M.act X x) := by
  simp [sumAct]

def sumMod (M : GKMod p q) (Y : Type) : GKMod p q where
  V := Y →₀ M.V
  act := sumAct M Y
  lie X X' := by
    refine LinearMap.ext fun v => Finsupp.ext fun y => ?_
    rw [sumAct_apply, M.lie X X']
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Finsupp.sub_apply, sumAct_apply]
  kfin v := by
    induction v using Finsupp.induction_linear with
    | zero => exact ⟨⊥, inferInstance, Submodule.zero_mem _, fun X _ w hw => by
        rw [Submodule.mem_bot] at hw ⊢; rw [hw, map_zero]⟩
    | add f g hf hg =>
      obtain ⟨W, hW, hf, hK⟩ := hf
      obtain ⟨W', hW', hg, hK'⟩ := hg
      refine ⟨W ⊔ W', inferInstance, Submodule.add_mem_sup hf hg, fun X hX w hw => ?_⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hw
      rw [map_add (f := _)]
      exact Submodule.add_mem_sup (hK X hX a ha) (hK' X hX b hb)
    | single y x =>
      obtain ⟨W, hW, hx, hK⟩ := M.kfin x
      refine ⟨W.map (Finsupp.lsingle y), inferInstance, Submodule.mem_map_of_mem hx, ?_⟩
      rintro X hX _ ⟨w, hw, rfl⟩
      rw [Finsupp.lsingle_apply, sumAct_single]
      exact Submodule.mem_map_of_mem (f := Finsupp.lsingle y) (hK X hX w hw)
  wts v := by
    induction v using Finsupp.induction_linear with
    | zero => exact Submodule.zero_mem _
    | add f g hf hg => exact Submodule.add_mem _ hf hg
    | single y x =>
      have h : (⨆ μ : Ix p q → ℚ, wtSub M.act μ) ≤
          (⨆ μ : Ix p q → ℚ, wtSub (sumAct M Y) μ).comap (Finsupp.lsingle y) := by
        refine iSup_le fun μ x hx => ?_
        rw [Submodule.mem_comap]
        refine Submodule.mem_iSup_of_mem μ ?_
        simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
          LinearMap.smul_apply, LinearMap.id_apply] at hx ⊢
        intro a
        rw [Finsupp.lsingle_apply, sumAct_single, Finsupp.smul_single, ← Finsupp.single_sub, hx a,
          Finsupp.single_zero]
      exact h (M.wts x)

def fockMod (p q r s : ℕ) : GKMod p q where
  V := Pol p q r s
  act := fockAct1 p q r s
  lie X X' := by
    have h : ∀ U : Mat p q, fockAct1 p q r s U = omAct p q r s (U ⊗ₖ (1 : Mat r s)) := fun _ => rfl
    rw [map_sub]
    simp only [h]
    rw [← GlobalTheory.FockLie.omAct_lie, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      Matrix.mul_one, map_sub]
  kfin P := ((GlobalTheory.FockPolGK.pol_locFin_weights p q r s).1 P).1
  wts P := ((GlobalTheory.FockPolGK.pol_locFin_weights p q r s).1 P).2

theorem exists_unitary_image (M : GKMod p q) (Y Z : Type) [AddCommGroup Y] [Module ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] (B : M.V →ₗ[ℂ] Y →ₛₗ[starRingEnd ℂ] Z)
    (hB : ∀ (X : Mat p q) P P' y y',
      ⟪B (M.act X P) y, B P' y'⟫_ℂ = ⟪B P y, B (M.act (adjZ X) P') y'⟫_ℂ) :
    ∃ (A : UGKMod p q) (j : A.M.V →ₗ[ℂ] Z) (B' : M.V →ₗ[ℂ] Y →ₛₗ[starRingEnd ℂ] A.M.V),
      Function.Injective j ∧ (∀ P y, j (B' P y) = B P y) ∧
        Submodule.span ℂ {x | ∃ P y, B' P y = x} = ⊤ ∧
        ∀ X P y, B' (M.act X P) y = A.M.act X (B' P y) := by
  let E : (Y →₀ M.V) →ₗ[ℂ] Z := Finsupp.lsum ℂ fun y => B.flip y
  have hE1 : ∀ y P, E (Finsupp.single y P) = B P y := fun y P => by
    simp [E]
  have hE : ∀ X (x x' : Y →₀ M.V), ⟪E (sumAct M Y X x), E x'⟫_ℂ =
      ⟪E x, E (sumAct M Y (adjZ X) x')⟫_ℂ := by
    intro X x x'
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => simp only [map_add (f := _), inner_add_left, hf, hg]
    | single y P =>
      induction x' using Finsupp.induction_linear with
      | zero => simp
      | add f g hf hg => simp only [map_add (f := _), inner_add_right, hf, hg]
      | single y' P' => simp only [sumAct_single, hE1, hB]
  obtain ⟨A, f, j, hf, hj, hjf, hact⟩ :=
    GlobalTheory.GKQuot.exists_unitary_quotient p q (sumMod M Y) Z E hE
  let g : (Y →₀ M.V) →ₗ[ℂ] A.M.V := f
  have hjg : ∀ y P, j (g (Finsupp.single y P)) = B P y := fun y P => (hjf _).trans (hE1 y P)
  let B' : M.V →ₗ[ℂ] Y →ₛₗ[starRingEnd ℂ] A.M.V :=
    LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun P y => g (Finsupp.single y P))
      (fun P P' y => by rw [Finsupp.single_add, map_add (f := _)])
      (fun c P y => by rw [← Finsupp.smul_single, map_smul, RingHom.id_apply])
      (fun P y y' => hj (by rw [map_add (f := _), hjg, hjg, hjg, map_add (f := _)]))
      (fun c P y => hj (by rw [map_smul, hjg, hjg, map_smulₛₗ]))
  have hB' : ∀ P y, B' P y = g (Finsupp.single y P) := fun _ _ => rfl
  refine ⟨A, j, B', hj, fun P y => hjg y P, ?_, fun X P y => ?_⟩
  · rw [eq_top_iff]
    rintro x -
    obtain ⟨v, rfl⟩ : ∃ v, g v = x := hf x
    induction v using Finsupp.induction_linear with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
    | single y P => exact Submodule.subset_span ⟨P, y, rfl⟩
  · rw [hB', hB', ← sumAct_single]
    exact hact X _

theorem unitaryImage : ∀ p q r s : ℕ, UnitaryImage p q r s :=
  fun p q r s Y Z _ _ _ _ B hB => exists_unitary_image (fockMod p q r s) Y Z B hB

end GlobalTheory.Chain.IoLift.UImg

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RowVertexInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

def fnOf {t : T} (d : PureDat G t) : ∀ a, FactorFn G t a
  | .inl j => (d.1 j).fn
  | .inr i => (d.2 i).fn

def movFn (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (v : ∀ a, FactorFn G t a) : ∀ a, FactorFn G t a :=
  Function.update
    (Function.update v (.inr ⟨j, by omega⟩)
      (fun x => v (.inr ⟨j, by omega⟩)
        (actO _ _ (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.1 (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.2 x) :
        FactorFn G t (.inr ⟨j, by omega⟩)))
    (.inr ⟨j + 1, hj⟩)
    (fun x => v (.inr ⟨j + 1, hj⟩)
        (actO _ _ (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.1 (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.2 x) :
        FactorFn G t (.inr ⟨j + 1, hj⟩))

def scaleAt (j : ℕ) (hj : j + 1 < D.R.m) (c₁ c₂ : ℂ) : Fin D.R.m ⊕ Fin D.R.m → ℂ :=
  Function.update (Function.update (fun _ => 1) (.inr ⟨j, by omega⟩) c₁) (.inr ⟨j + 1, hj⟩) c₂

end GlobalTheory.RowVertexInv
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section

namespace GlobalTheory.RowVertexInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem negGA_mem_GfC_row (V : HSp D) {g : GA D V} (hg : g ∈ GfC V) : negGA V g ∈ GfC (negSp V) := by
  have e : matHom (negSp V) (negGA V g) = matHom V g := Units.ext (mt_negGA V g)
  simp only [GfC, MonoidHom.mem_ker, infHom, MonoidHom.comp_apply] at hg ⊢
  rw [e]
  exact hg

theorem ker_mul_row (W : G.Weil) (p : Pair T) (F : WO (G.pS p) (G.pT p) → ℂ) (g k : GA D (G.V p.small))
    (h k' : GA D (G.V p.big)) : W.ker p F (g * k) (h * k') = W.ker p (W.om p (G.toPair p k k') F) g h := by
  have e : G.toPair p (g * k) (h * k') = G.toPair p g h * G.toPair p k k' := by
    cases p <;> simp [GridData.toPair, map_mul, Prod.ext_iff]
  unfold GridData.Weil.ker
  rw [e]
  simp only [thetaKO, Prod.mk.eta, map_mul, Module.End.mul_apply]

theorem fockComp_mul_row (W : G.Weil) (B : VertexFrames G) (p : Pair T) (hp : p.InRange D.R.m)
    (f : WO (G.pS p) (G.pT p) → ℂ) (hf : IsThetaFunO W.ψ (G.pS p) (G.pT p) f) (x g : FinPt G p.small) (y h : FinPt G p.big) :
    fockComp W B p f (x * g) (y * h) = fockComp W B p (W.om p (G.toPair p g h) f) x y := by
  have hmem : (G.toPair p g h).1 ∈ GfC (G.pS p) ∧ (G.toPair p g h).2 ∈ GfC (G.pT p) := by
    cases p with
    | chi i j => exact ⟨negGA_mem_GfC_row _ h.2, g.2⟩
    | mu t i j => exact ⟨g.2, h.2⟩
    | core i => exact ⟨negGA_mem_GfC_row _ h.2, g.2⟩
    | top t j => exact ⟨g.2, h.2⟩
  have key : ∀ P, W.ker p (fockIn W B p f P) ((x : GA D (G.V p.small)) * (g : GA D (G.V p.small))) ((y : GA D (G.V p.big)) * (h : GA D (G.V p.big))) =
      W.ker p (fockIn W B p (W.om p (G.toPair p g h) f) P) x y := by
    intro P
    rw [ker_mul_row]
    congr 1
    have e := (GlobalTheory.OrientedHeis.om_pureTensorO D W.ψ W.θ _ _ _ _ (W.om p) (W.om_is p hp) W.θ_is
      (G.cartS W.cart p) (G.cartS W.cart p) (G.onS B p) (G.onS B p) (G.onT W.cart p) (G.onT W.cart p) (G.onT B p) (G.onT B p)
      (G.toPair p g h).1 (G.toPair p g h).2
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite W.θ τ hmem.1, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite W.θ τ hmem.2, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite W.θ τ hmem.1, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite W.θ τ hmem.2, Matrix.one_mul]) f hf P).2
    simp only [Prod.mk.eta] at e
    exact e
  unfold fockComp
  congr 1
  funext k
  exact key _

theorem kkV_mul_big (S : GridChoice W U) (p : Pair T) (hp : p.InRange D.R.m) (f : WO (G.pS p) (G.pT p) → ℂ)
    (hf : IsThetaFunO W.ψ (G.pS p) (G.pT p) f) (a : FinPt G p.small) (b h : FinPt G p.big) :
    kkV S p f a (b * h) =
      kkV S p (W.om p (G.toPair p 1 (((S.N.u p.big)⁻¹ * h * S.N.u p.big : FinPt G p.big) : GA D (G.V p.big))) f) a b := by
  have e := fockComp_mul_row W S.N.frC p hp f hf (a * S.N.u _) 1 (b * S.N.u _) ((S.N.u p.big)⁻¹ * h * S.N.u p.big)
  rw [mul_one, OneMemClass.coe_one] at e
  unfold kkV
  rw [show b * h * S.N.u p.big = b * S.N.u p.big * ((S.N.u p.big)⁻¹ * h * S.N.u p.big) by group, e]

theorem kkV_mul_small (S : GridChoice W U) (p : Pair T) (hp : p.InRange D.R.m) (f : WO (G.pS p) (G.pT p) → ℂ)
    (hf : IsThetaFunO W.ψ (G.pS p) (G.pT p) f) (a g : FinPt G p.small) (b : FinPt G p.big) :
    kkV S p f (a * g) b =
      kkV S p (W.om p (G.toPair p (((S.N.u p.small)⁻¹ * g * S.N.u p.small : FinPt G p.small) : GA D (G.V p.small)) 1) f) a b := by
  have e := fockComp_mul_row W S.N.frC p hp f hf (a * S.N.u _) ((S.N.u p.small)⁻¹ * g * S.N.u p.small) (b * S.N.u _) 1
  rw [mul_one, OneMemClass.coe_one] at e
  unfold kkV
  rw [show a * g * S.N.u p.small = a * S.N.u p.small * ((S.N.u p.small)⁻¹ * g * S.N.u p.small) by group, e]

theorem pairFn_update_moveV (S : GridChoice W U) {t : T} (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m))
    (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)) (v : ∀ a, FactorFn G t a)
    (hv : ∀ a, v a ∈ thetaSub W.ψ (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))) :
    pairFn S x (Function.update y (j + 1) (y (j + 1) * k)) v = pairFn S x y (moveV S j hj k v) := by
  have e : ∀ (i : ℕ) (h : i < D.R.m), moveV S j hj k v (.inl ⟨i, h⟩) = v (.inl ⟨i, h⟩) := fun i h =>
    (Function.update_of_ne Sum.inl_ne_inr _ _).trans (Function.update_of_ne Sum.inl_ne_inr _ _)
  have hcol : colV S (moveV S j hj k v) x = colV S v x := by
    simp only [colV, e]
  have key : ∀ (i : ℕ) (hi : i < D.R.m),
      kkV S (.chi i D.R.m) (v (.inr ⟨i, hi⟩)) (Function.update y (j + 1) (y (j + 1) * k) i)
        (Function.update y (j + 1) (y (j + 1) * k) (i + 1)) =
      kkV S (.chi i D.R.m) (moveV S j hj k v (.inr ⟨i, hi⟩)) (y i) (y (i + 1)) := by
    intro i hi
    by_cases h1 : i = j
    · subst h1
      rw [Function.update_of_ne (show i ≠ i + 1 by omega), Function.update_self]
      have hm : moveV S i hj k v (.inr ⟨i, hi⟩) =
          W.om (.chi i D.R.m) (G.toPair (.chi i D.R.m) 1 (moved S i k)) (v (.inr ⟨i, hi⟩)) :=
        (Function.update_of_ne (by simp) _ _).trans (Function.update_self _ _ _)
      rw [hm]
      exact kkV_mul_big S (.chi i D.R.m) (show i + 1 ≤ D.R.m ∧ D.R.m ≤ D.R.m from ⟨by omega, le_rfl⟩) _ (hv (.inr ⟨i, hi⟩)) (y i) (y (i + 1)) k
    by_cases h2 : i = j + 1
    · subst h2
      rw [Function.update_self, Function.update_of_ne (show j + 1 + 1 ≠ j + 1 by omega)]
      have hm : moveV S j hj k v (.inr ⟨j + 1, hi⟩) =
          W.om (.chi (j + 1) D.R.m) (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1) (v (.inr ⟨j + 1, hi⟩)) :=
        Function.update_self _ _ _
      rw [hm]
      exact kkV_mul_small S (.chi (j + 1) D.R.m) (show j + 1 + 1 ≤ D.R.m ∧ D.R.m ≤ D.R.m from ⟨by omega, le_rfl⟩) _ (hv (.inr ⟨j + 1, hi⟩))
        (y (j + 1)) k (y (j + 1 + 1))
    · rw [Function.update_of_ne h2, Function.update_of_ne (show i + 1 ≠ j + 1 by omega)]
      have hm : moveV S j hj k v (.inr ⟨i, hi⟩) = v (.inr ⟨i, hi⟩) :=
        (Function.update_of_ne (by simp; omega) _ _).trans (Function.update_of_ne (by simp; omega) _ _)
      rw [hm]
  have hrow : rowV S v (Function.update y (j + 1) (y (j + 1) * k)) = rowV S (moveV S j hj k v) y := by
    simp only [rowV, key]
  rw [pairFn, pairFn, hcol, hrow]

end GlobalTheory.RowVertexInv

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RowVertexInv

open Matrix

theorem mulVec_conj_mulVec_eq {n : ℕ} {R : Type} [CommRing R] (a g : GL (Fin n) R) (v : Fin n → R) :
    (a : Matrix (Fin n) (Fin n) R) *ᵥ (((a⁻¹ * g * a : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ v) =
      (g : Matrix (Fin n) (Fin n) R) *ᵥ ((a : Matrix (Fin n) (Fin n) R) *ᵥ v) := by
  simp only [Matrix.mulVec_mulVec, Units.val_mul, ← mul_assoc, Units.mul_inv, one_mul]



theorem moved_keeps_std : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)), finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le → ∀ v : Fin (G.V (.grid (j + 1) D.R.m)).rank → Formalism.IndefR.Lev.EAf D, (v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.grid (j + 1) D.R.m))) ↔ Matrix.mulVec (Formalism.IndefR.Lev.finE (G.V (.grid (j + 1) D.R.m)) (moved S j k)).1 v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.grid (j + 1) D.R.m)))) := by
  intro D T L sc G W U S t j hj k hk v
  have hD : DefNode D.R.m (.grid (j + 1) D.R.m) := ⟨hj.le, rfl⟩
  have hmax : finG (G.V (.grid (j + 1) D.R.m)) k ∈ G.levMax (.grid (j + 1) D.R.m) := by
    rw [← GlobalTheory.FunObj.GridChoice.levRow_succ_inf_UA W S t j hj.le]
    exact Subgroup.mem_inf.2 ⟨hk, GlobalTheory.LevSplit.finE_mem_UA _ _⟩
  rw [GridData.levMax, congLev_top] at hmax
  have hst := (Subgroup.mem_inf.1 hmax).2
  have e : Formalism.IndefR.Lev.finE (G.V (.grid (j + 1) D.R.m)) (moved S j k) =
      (Formalism.IndefR.Lev.finE (G.V (.grid (j + 1) D.R.m)) (S.N.u (.grid (j + 1) D.R.m)).1)⁻¹ * finG (G.V (.grid (j + 1) D.R.m)) k * Formalism.IndefR.Lev.finE (G.V (.grid (j + 1) D.R.m)) (S.N.u (.grid (j + 1) D.R.m)).1 := by
    rw [moved]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    rfl
  rw [S.N.u_lat _ hD v, S.N.u_lat _ hD, e, mulVec_conj_mulVec_eq]
  exact hst _

end GlobalTheory.RowVertexInv
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.TopZeroInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TopZeroInv

theorem kkVec_smul : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) (p : Pair T) (c : ℂ) (f : WO (G.pS p) (G.pT p) → ℂ) (x : FinPt G p.small) (y : FinPt G p.big),
    kkVec S p (c • f) x y = c • kkVec S p f x y := by
  intro D T L sc G W U S p c f x y
  unfold GlobalTheory.TopZeroInv.kkVec fockComp
  have hT : jetTab W S.N.frC p (c • f) (x * S.N.u _) (y * S.N.u _) =
      c • jetTab W S.N.frC p f (x * S.N.u _) (y * S.N.u _) := by
    funext k
    simp only [jetTab, kerFin, fockIn, GlobalTheory.FiniteFock.pureTensorO_smul, Pi.smul_apply, smul_eq_mul,
      GlobalTheory.ChiGrid.GridData.Weil.ker, thetaKO, map_smul]
  have h := (GlobalTheory.JetIdentity.jetOpL (K := ℂ) (wt G p.small) (wt G p.big) (nuEnd G p)).map_smul c
    (jetTab W S.N.frC p f (x * S.N.u _) (y * S.N.u _))
  simp only [GlobalTheory.JetIdentity.jetOpL, LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply] at h
  rw [hT, h, smul_comm]

end GlobalTheory.TopZeroInv
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaCoefCont

private theorem measure_fundamentalDomain_ratL_lt_infty {D : D7} (V W : HSp D) (ν : Measure (WO V W)) (𝓕 : Set (WO V W))
    (hν : ν.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratL W V) 𝓕 ν) : ν 𝓕 < ⊤ := by
  obtain ⟨hg, -, hsc, -, hdisc, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W V
  haveI := hg
  haveI := hsc
  haveI := hdisc
  haveI : BorelSpace (WO V W) := ⟨rfl⟩
  haveI : Countable (ratL W V) := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  exact GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (ratL W V) hK hcov ν h𝓕

theorem continuous_coef : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν → ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' → Continuous (fun y : Mx D a b => ∫ u in 𝓕, heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q y) G u * star (G' u) ∂ν) := by
  intro D V W a b P Q ψ hψ ν 𝓕 hν h𝓕 G G' hG hG'
  haveI : BorelSpace (WO V W) := ⟨rfl⟩
  have hfin : ν 𝓕 < ⊤ := measure_fundamentalDomain_ratL_lt_infty V W ν 𝓕 hν h𝓕
  haveI : IsFiniteMeasure (ν.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  obtain ⟨C', hC'⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hG'
  obtain ⟨C, hC⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hG
  have hE : Continuous (GlobalTheory.IsoMean.emb V W P Q) := by
    unfold GlobalTheory.IsoMean.emb
    exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  rw [continuous_iff_continuousAt]
  intro y₀
  haveI : SecondCountableTopology (Mx D a b) := (GlobalTheory.MixModel.lattice_Mx D a b).2.2.1
  haveI : FirstCountableTopology (Mx D a b) := TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
  refine MeasureTheory.continuousAt_of_dominated (bound := fun _ => C * C') ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun y =>
      (((hψ.1.1.comp (continuous_const.mul (GlobalTheory.SplitScalar.continuous_symplO V W continuous_id continuous_const))).mul
        (hG.cont.comp (continuous_id.add continuous_const))).mul
        (continuous_star.comp hG'.cont)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun y => Filter.Eventually.of_forall fun u => ?_
    rw [norm_mul, norm_star, heisO, norm_mul, hψ.1.2.1, one_mul]
    exact mul_le_mul (hC _) (hC' _) (norm_nonneg _) ((norm_nonneg (G u)).trans (hC u))
  · exact integrable_const _
  · refine Filter.Eventually.of_forall fun u => ?_
    exact (((hψ.1.1.comp (continuous_const.mul (GlobalTheory.SplitScalar.continuous_symplO V W continuous_const hE))).mul
      (hG.cont.comp (continuous_const.add hE))).mul continuous_const).continuousAt

end GlobalTheory.ThetaCoefCont

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

theorem _root_.GlobalTheory.T.hasSum_card_cosets_diagonalDoubleCoset_GL : GlobalTheory.Published.UnramifiedDoublingGL → ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (r : ℕ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → ∀ T : (Fin r → ℤ) → GL (Fin r) (w.adicCompletion E), (∀ d, (T d).1 = Matrix.diagonal fun i => ϖ ^ d i) → ∃ B₀ : Multiset ℂˣ, (∀ β ∈ B₀, ‖(β : ℂ)‖ ≤ (qV E w : ℝ) ^ (((r : ℝ) - 1) / 2) ∧ ‖((β⁻¹ : ℂˣ) : ℂ)‖ ≤ (qV E w : ℝ) ^ (((r : ℝ) - 1) / 2)) ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ X : ℝ, 0 < X → X < δ → HasSum (fun d : {d : Fin r → ℤ // Antitone d} => ((Nat.card {a : GL (Fin r) (w.adicCompletion E) ⧸ KGL w (n := r) // a.out ∈ DoubleCoset.doubleCoset (T d.1) (KGL w (n := r) : Set (GL (Fin r) (w.adicCompletion E))) (KGL w (n := r))} : ℝ) : ℂ) * (X : ℂ) ^ (∑ i, |d.1 i|).toNat) (eulerFac B₀ ((qV E w : ℂ) ^ (((r : ℂ) - 1) / 2) * X) * eulerFac (B₀.map (·⁻¹)) ((qV E w : ℂ) ^ (((r : ℂ) - 1) / 2) * X) * ∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ i * (X : ℂ) ^ 2)) := by
  first | exact @GlobalTheory.FinZeta.TrivCount.hasSum_card_cosets_diag | exact GlobalTheory.FinZeta.TrivCount.hasSum_card_cosets_diag | (intros; apply GlobalTheory.FinZeta.TrivCount.hasSum_card_cosets_diag <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_lattice_level_open_stabilizer_unitary : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ (N : AddSubgroup (WO S T)) (K : Subgroup (GA D T)), N ≤ U ∧ IsOpen (K : Set (GA D T)) ∧ (∀ x : WO S T, ∃ γ ∈ ratL T S, ∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T (x - γ) l) = 1) ∧ (∀ k ∈ K, k ∈ GfC T → ∀ u ∈ N, u.map (infPart D) = 0 → actO S T 1 k u ∈ N ∧ (actO S T 1 k u).map (infPart D) = 0) ∧ (∀ k ∈ K, k ∈ GfC T → ∀ w : WO S T, (∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T w l) = 1) → actO S T 1 k w - w ∈ N ∧ (actO S T 1 k w - w).map (infPart D) = 0 ∧ ψ (symplOH S T w (actO S T 1 k w - w)) = 1) := by
  first | exact @GlobalTheory.WeilLevelStab.exists_level_stab | exact GlobalTheory.WeilLevelStab.exists_level_stab | (intros; apply GlobalTheory.WeilLevelStab.exists_level_stab <;> assumption)
end

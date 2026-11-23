module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle328
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle329
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle696
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowColumnProductDataHaveVectors
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
import Mathlib.Tactic.Have
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
import Std.Tactic.BVDecide.Normalize.BitVec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle318
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle469
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle574

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.LastStepExt0

theorem model_last : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (hChr : ChrP ch) (hArr : ArrP ch) (hJac : JacP ch)
    (t : T) (w : Pl D.host.E) (hw : w ∈ locPl ch.G t) (p : Place D (Kw w)) (hp : IsPlc w p)
    (β : Cosets (G := locGrid ch.G t w) one_le_sLen (givenLevel ch.G t w))
    (M : Vol ch.G) (hM : M.Is t) (φ : EdgeDat ch t w) (v f : SchDown ch.G t)
    (hvf : ∀ j : Fin D.R.m, IsArrVec ch t w p.e φ j j.2 (v j) (f j))
    (j : ℕ) (hj : j + 2 * 0 + 2 = D.R.m)
    (h₃ : (locGrid ch.G t w).rank (D.R.m, j + 1 + 1) = (locGrid ch.G t w).rank (D.R.m, D.R.m))
    (h₄ : (locGrid ch.G t w).rank (D.R.m, j + 1) = topRank (locGrid ch.G t w) (j + 1)),
    ∃ T₂ : SB (Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, D.R.m))) (Fin (topRank (locGrid ch.G t w) (j + 1))) (Kw w)) →ₗ[ℂ]
        (WO (ch.G.V (.top (j + 1))) (ch.G.V (.grid D.R.m D.R.m)) → ℂ),
      p.IsModel ch.W.ψ (frTop ch.S.toGridChoice t w (j + 1) (by omega)) (frRow ch.S.B t w D.R.m le_rfl) T₂ ∧
      (∀ O, IsOne O → T₂ O = fun x => castSch ch.G (show j + 1 + 1 = D.R.m by omega) (v ⟨j + 1, by omega⟩)
        ((rowJac ch.G (j + 1) (by omega) 0 (by omega)).ext0 _ x)) ∧
      ∃ Φ : SB (Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, D.R.m))) (Fin (topRank (locGrid ch.G t w) (j + 1))) (Kw w)),
        (∀ z, Φ.1 z = phiM (locGrid ch.G t w) (epsV ch.G t w * (repsAt ch.G t w).elt β) ((repsAt ch.G t w).elt β) φ
          (.theta D.R.m (j + 1)) (z.submatrix (Fin.cast h₃) (Fin.cast h₄))ᵀ) ∧
        T₂ Φ = fun x => castSch ch.G (show j + 1 + 1 = D.R.m by omega) (f ⟨j + 1, by omega⟩)
          ((rowJac ch.G (j + 1) (by omega) 0 (by omega)).ext0 _ x) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch hChr hArr hJac t w hw p hp β M hM φ v f hvf j hj h₃ h₄
  suffices key : ∀ (n : ℕ) (hn : j + 1 + 1 = n) (hnm : n ≤ D.R.m)
      (h₃' : (locGrid ch.G t w).rank (D.R.m, j + 1 + 1) = (locGrid ch.G t w).rank (D.R.m, n)),
      ∃ T₂ : SB (Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, n))) (Fin (topRank (locGrid ch.G t w) (j + 1))) (Kw w)) →ₗ[ℂ]
        (WO (ch.G.V (.top (j + 1))) (ch.G.V (.grid D.R.m n)) → ℂ),
      p.IsModel ch.W.ψ (frTop ch.S.toGridChoice t w (j + 1) (by omega)) (frRow ch.S.B t w n hnm) T₂ ∧
      (∀ O, IsOne O → T₂ O = fun x => castSch ch.G hn (v ⟨j + 1, by omega⟩)
        ((rowJac ch.G (j + 1) (by omega) 0 (by omega)).ext0 _ x)) ∧
      ∃ Φ : SB (Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, n))) (Fin (topRank (locGrid ch.G t w) (j + 1))) (Kw w)),
        (∀ z, Φ.1 z = phiM (locGrid ch.G t w) (epsV ch.G t w * (repsAt ch.G t w).elt β) ((repsAt ch.G t w).elt β) φ
          (.theta D.R.m (j + 1)) (z.submatrix (Fin.cast h₃') (Fin.cast h₄))ᵀ) ∧
        T₂ Φ = fun x => castSch ch.G hn (f ⟨j + 1, by omega⟩)
          ((rowJac ch.G (j + 1) (by omega) 0 (by omega)).ext0 _ x)
  · exact key D.R.m (by omega) le_rfl h₃
  intro n hn hnm h₃'
  subst hn
  have hj1 : j + 1 < D.R.m := by omega
  have hc : topRank (locGrid ch.G t w) (j + 1) + 0 = (locGrid ch.G t w).rank (D.R.m, j + 1) := by omega
  have hloc : ∀ i (hi : i ≤ D.R.m), D.R.m ≤ i + 1 →
      p.IsLoc (frRow ch.S.B t w i hi) 1 ((epsV ch.G t w * (repsAt ch.G t w).elt β) (D.R.m, i)) := by
    intro i hi hmi
    rw [Pi.mul_apply, epsV_eq_one t w hmi, elt_eq_one t w β hmi, mul_one]
    refine ⟨fun a b => by simp [Formalism.L2.Theta.mt], ?_⟩
    have : Formalism.L2.Theta.mt (ch.G.V (.grid D.R.m i)) 1 = 1 := by simp [Formalism.L2.Theta.mt]
    rw [this, Matrix.map_one p.π (map_zero _) (map_one _)]
    simp [(frRow ch.S.B t w i hi).βγ]
  obtain ⟨Tm, hTm, hOne, Φ, hΦ, hTΦ⟩ := hArr t w hw p hp φ (j + 1) hj1 (v ⟨j + 1, hj1⟩) (f ⟨j + 1, hj1⟩) (hvf ⟨j + 1, hj1⟩)
    (epsV ch.G t w) ((repsAt ch.G t w).elt β) (fun X => epsV_mem t w X) 1 1 1 1 (hloc (j + 1) hj1.le (by omega))
    (hloc (j + 1 + 1) hj1 (by omega)) (Fin (topRank (locGrid ch.G t w) (j + 1)) ⊕ Fin 0)
    (Fin ((locGrid ch.G t w).rank (D.R.m, j + 1 + 1))) (frame hc) (Equiv.refl _)
  have hJ := hJac t w hw p hp M hM j 0 hj (GlobalTheory.Unf.Inhab.nonempty_volN (besDecAt ch.G j 0 hj)).some 1 (Or.inl ⟨rfl, rfl⟩) 0 hc
  have hFT : (mvFr p (1 : GA D (ch.G.V (.grid D.R.m (j + 1 + 1)))) (frRow ch.S.B t w (j + 1 + 1) hj1)
      (epsV ch.G t w (D.R.m, j + 1 + 1)) (Equiv.refl _)).β = (frRow ch.S.B t w (j + 1 + 1) hj1).β := by
    simp only [mvFr]
    rw [epsV_eq_one t w (by omega)]
    have : Formalism.L2.Theta.mt (ch.G.V (.grid D.R.m (j + 1 + 1))) 1 = 1 := by simp [Formalism.L2.Theta.mt]
    rw [this, Matrix.map_one p.π (map_zero _) (map_one _)]
    simp
  obtain ⟨Tm', hTm', hTT⟩ := Place.exists_isModel_chg D (Kw w) p _ _ _ _
    (mvFr p 1 (frRow ch.S.B t w (j + 1) hj1.le) (epsV ch.G t w (D.R.m, j + 1)) (frame hc))
    (mvFr p 1 (frRow ch.S.B t w (j + 1 + 1) hj1) (epsV ch.G t w (D.R.m, j + 1 + 1)) (Equiv.refl _)) _ _
    (mvFr p 1 (frRow ch.S.B t w (j + 1) hj1.le) (epsV ch.G t w (D.R.m, j + 1)) (frame hc))
    (frRow ch.S.B t w (j + 1 + 1) hj1) ch.W.ψ Tm hTm
  have hTT' : ∀ Ψ, Tm' Ψ = Tm Ψ := fun Ψ => hTT Ψ Ψ fun x => by
    rw [hFT, Frame.γβ, Frame.γβ, Matrix.one_mul, Matrix.mul_one]
  obtain ⟨T₂, hT₂, hval⟩ := RankZeroSrc.localModel_rankZeroWitt_source_isModel D (Kw w) p ch.W.ψ ch.W.ψ_std (jacAt ch.G hM (j + 1) 0 (by omega)) _ _ _ _
    (frTop ch.S.toGridChoice t w (j + 1) (by omega)) _ hJ _ (frRow ch.S.B t w (j + 1 + 1) hj1) Tm' hTm'
  haveI := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := Kw w) (n := Fin ((locGrid ch.G t w).rank (D.R.m, j + 1 + 1)))
    (n' := Fin (topRank (locGrid ch.G t w) (j + 1)) ⊕ Fin 0)
  haveI := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := Kw w) (n := Fin ((locGrid ch.G t w).rank (D.R.m, j + 1 + 1)))
    (n' := Fin (topRank (locGrid ch.G t w) (j + 1)))
  have hc1 : Continuous fun x : Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, j + 1 + 1)))
      (Fin (topRank (locGrid ch.G t w) (j + 1)) ⊕ Fin 0) (Kw w) => x.toCols₁ :=
    continuous_pi fun i => continuous_pi fun j => (continuous_apply (Sum.inl j)).comp (continuous_apply i)
  have hc2 : Continuous fun x : Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, j + 1 + 1)))
      (Fin (topRank (locGrid ch.G t w) (j + 1))) (Kw w) =>
        (fromCols x 0 : Matrix _ (Fin (topRank (locGrid ch.G t w) (j + 1)) ⊕ Fin 0) (Kw w)) :=
    continuous_pi fun i => continuous_pi fun j => by
      rcases j with j | j
      · exact (continuous_apply j).comp (continuous_apply i)
      · exact j.elim0
  refine ⟨T₂, hT₂, fun O hO => ?_, ?_⟩
  · let O' : SB (Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, j + 1 + 1)))
        (Fin (topRank (locGrid ch.G t w) (j + 1)) ⊕ Fin 0) (Kw w)) :=
      ⟨fun x => O.1 x.toCols₁, GlobalTheory.FinPl.Comm.comp_mem_SB O.2 hc1 hc2 RankZeroSrc.fromCols_toCols₁⟩
    have hO' : IsOne O' := by
      funext x
      show O.1 x.toCols₁ = _
      rw [hO]
      by_cases h2 : ∀ r q, x r q ∈ 𝒪[Kw w]
      · rw [Set.indicator_of_mem (s := {x : Matrix _ _ (Kw w) | ∀ r q, x r q ∈ 𝒪[Kw w]}) (a := x.toCols₁) (fun r q => h2 r (Sum.inl q)),
          Set.indicator_of_mem (s := {x : Matrix _ _ (Kw w) | ∀ r q, x r q ∈ 𝒪[Kw w]}) h2]
      · rw [Set.indicator_of_notMem (s := {x : Matrix _ _ (Kw w) | ∀ r q, x r q ∈ 𝒪[Kw w]}) h2, Set.indicator_of_notMem (a := x.toCols₁)]
        intro h1
        apply h2
        intro r q
        rcases q with q | q
        exacts [h1 r q, q.elim0]
    funext x
    refine (hval O O' (fun y => by simp [O', Matrix.toCols₁_fromCols]) x).trans ?_
    refine (congrFun (hTT' O') _).trans ?_
    refine (congrFun (hOne O' hO') _).trans ?_
    simp only [show ((1 : GA D (ch.G.V (.grid D.R.m (j + 1)))), (1 : GA D (ch.G.V (.grid D.R.m (j + 1 + 1))))) = 1 from rfl,
      map_one, Module.End.one_apply]
    rfl
  · let Φ₂ : SB (Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, j + 1 + 1))) (Fin (topRank (locGrid ch.G t w) (j + 1))) (Kw w)) :=
      ⟨fun x => Φ.1 (fromCols x 0), GlobalTheory.FinPl.Comm.comp_mem_SB Φ.2 hc2 hc1 fun x => Matrix.toCols₁_fromCols x 0⟩
    have hs : ∀ b, (frame hc).symm b = Sum.inl (Fin.cast h₄ b) := fun b => by
      rw [Equiv.symm_apply_eq]
      ext
      rfl
    refine ⟨Φ₂, fun z => ?_, ?_⟩
    · show Φ.1 (fromCols z 0) = _
      rw [hΦ]
      congr 2
      ext a b
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm, Equiv.refl_apply, hs, Matrix.fromCols_apply_inl]
      rfl
    · funext x
      refine (hval Φ₂ Φ (fun _ => rfl) x).trans ?_
      refine (congrFun (hTT' Φ) _).trans ?_
      refine (congrFun hTΦ _).trans ?_
      simp only [mul_one, show ((1 : GA D (ch.G.V (.grid D.R.m (j + 1)))), (1 : GA D (ch.G.V (.grid D.R.m (j + 1 + 1))))) = 1 from rfl,
        map_one, Module.End.one_apply]
      rfl

end GlobalTheory.LastStepExt0
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

namespace GlobalTheory.FlatScal

noncomputable section

open GlobalTheory.LocMod (Place Frame IsOne)
open GlobalTheory.SplitWeil (SB)
open GlobalTheory.SplitFlip (Grid Edge oppositePath gdet)
open GlobalTheory.FlatPlace

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def xiEdge (ξ : kˣ →* ℂˣ) : Edge → kˣ →* ℂˣ
  | .theta _ _ => ξ
  | .ex _ _ => 1

theorem kappa_split (Γ : Grid k) (μ₀ : ℕ → kˣ →* ℂˣ) (ξ : kˣ →* ℂˣ) (h : ∀ j, Γ.mu j = μ₀ j * ξ) (b : Edge) (X : ℕ × ℕ) :
    Γ.kappa b X = ({Γ with mu := μ₀} : Grid k).kappa b X * xiEdge ξ b := by
  cases b with
  | theta i j =>
    show Γ.mu (j + 1) / Γ.eta ^ ((Γ.rank X + 1) % 2) = μ₀ (j + 1) / Γ.eta ^ ((Γ.rank X + 1) % 2) * ξ
    rw [h, mul_div_right_comm]
  | ex i j =>
    show Γ.chi (Γ.m - i) / Γ.eta ^ ((Γ.rank X + 1) % 2) = Γ.chi (Γ.m - i) / Γ.eta ^ ((Γ.rank X + 1) % 2) * 1
    rw [mul_one]

def xiPart (Γ : Grid k) (ξ : kˣ →* ℂˣ) (g : Γ.VertexGroup) : ℂˣ :=
  ((oppositePath Γ.m).map fun b => xiEdge ξ b (gdet (g b.src)) * (xiEdge ξ b (gdet (g b.tgt)))⁻¹).prod

theorem charFactor_split (Γ : Grid k) (μ₀ : ℕ → kˣ →* ℂˣ) (ξ : kˣ →* ℂˣ) (h : ∀ j, Γ.mu j = μ₀ j * ξ)
    (g : Γ.VertexGroup) :
    charFactor Γ g = charFactor ({Γ with mu := μ₀} : Grid k) g * xiPart Γ ξ g := by
  simp only [charFactor, xiPart, kappa_split Γ μ₀ ξ h, ← List.prod_map_mul]
  refine congrArg List.prod (List.map_congr_left fun b _ => ?_)
  simp only [MonoidHom.mul_apply, mul_inv]
  exact mul_mul_mul_comm _ _ _ _

theorem xiPart_mem (Γ : Grid k) (ξ : kˣ →* ℂˣ) (g : Γ.VertexGroup) (H : Subgroup ℂˣ) (hH : ∀ x, ξ x ∈ H) :
    xiPart Γ ξ g ∈ H := by
  refine H.list_prod_mem fun x hx => ?_
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 hx
  have e : ∀ u, xiEdge ξ b u ∈ H := fun u => by
    cases b with
    | theta _ _ => exact hH u
    | ex _ _ => exact H.one_mem
  exact H.mul_mem (e _) (H.inv_mem (e _))

theorem prod_edgeFactor (Γ : Grid k) (ε : Γ.VertexGroup) (hε : ∀ X, ε X ∈ GlobalTheory.SplitWeil.KO k _) :
    ((oppositePath Γ.m).map (Γ.edgeFactor .one ε)).prod = ((charFactor Γ ε : ℂˣ) : ℂ) := by
  rw [charFactor, ← Units.coeHom_apply, map_list_prod, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun b _ => ?_)
  have ha : ∀ X (z : ℂ), GlobalTheory.SplitFlip.apow (gdet (GlobalTheory.SplitFlip.Assignment.one.read (ε X))) z = 1 := fun X z => by
    refine GlobalTheory.SplitFlip.apow_of_valuation_eq_one ?_ z
    rw [show GlobalTheory.SplitFlip.Assignment.one.read (ε X) = GlobalTheory.SplitFlip.invT (ε X) from rfl, GlobalTheory.SplitFlip.gdet_invT,
      Units.val_inv_eq_inv_val, map_inv₀, GlobalTheory.SplitFlip.valuation_gdet_of_mem_KO (hε X), inv_one]
  simp only [Grid.edgeFactor, ha, mul_one, Function.comp, Units.coeHom_apply, Units.val_mul]

theorem charFactor_eq_one (Γ : Grid k) (ε : Γ.VertexGroup) (hε : ∀ X, ε X ∈ GlobalTheory.SplitWeil.KO k _)
    (hrow : ∀ i < Γ.m, ε (i, Γ.m) = 1 ∧ ε (i + 1, Γ.m) = 1)
    (hμ : ∀ j < Γ.m, IsUnram (Γ.mu (j + 1))) (hη : IsUnram Γ.eta) : charFactor Γ ε = 1 := by
  refine List.prod_eq_one fun x hx => ?_
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hx
  simp only [oppositePath, List.mem_append, List.mem_map, List.mem_range, List.mem_reverse] at hb
  rcases hb with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
  · show Γ.kappa _ (i, Γ.m) (gdet (ε (i, Γ.m))) * (Γ.kappa _ (i + 1, Γ.m) (gdet (ε (i + 1, Γ.m))))⁻¹ = 1
    have g1 : ∀ n, gdet (1 : GL (Fin n) k) = 1 := fun _ => map_one _
    rw [(hrow i hi).1, (hrow i hi).2, g1, g1, map_one, map_one, inv_one, mul_one]
  · have hu : ∀ X, Γ.kappa (.theta Γ.m j) X (gdet (ε X)) = 1 := fun X => by
      have hv := GlobalTheory.SplitFlip.valuation_gdet_of_mem_KO (hε X)
      show (Γ.mu (j + 1) / Γ.eta ^ ((Γ.rank X + 1) % 2)) (gdet (ε X)) = 1
      rw [MonoidHom.div_apply, MonoidHom.pow_apply, hμ j hj _ hv, hη _ hv, one_pow, div_one]
    show Γ.kappa _ _ (gdet (ε _)) * (Γ.kappa _ _ (gdet (ε _)))⁻¹ = 1
    rw [hu, hu, inv_one, mul_one]

end Local

section Grid0

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}


variable (G : GridData L sc) in
def grid0 (w : Pl D.host.E) : Grid (Kw w) where
  m := D.R.m
  r := D.R.r
  t := D.R.t
  s := sLen D
  mu j := (muBase L j).loc w
  chi i := (G.ch.chiH i).loc w
  eta := L.C.eta.loc w


open Classical in
def eps0 (G : GridData L sc) (w : Pl D.host.E) : (grid0 G w).VertexGroup :=
  onColumn (G := grid0 G w) fun j => if j ∈ idx D then GlobalTheory.SplitFlip.diagGL fun a =>
    if Odd j ∧ topRank (grid0 G w) j + (D.R.m - 1 - j) / 2 ≤ a.1 then Units.map (Int.castRingHom (Kw w)).toMonoidHom (-1) else 1
    else 1


variable (G : GridData L sc) in
def stair0 (w : Pl D.host.E) : (grid0 G w).VertexGroup :=
  onColumn (G := grid0 G w) fun j => if j + 2 ≤ D.R.m then stair (grid0 G w) (unifAt w) (cosExp G w) j else 1

theorem elt_stair (G : GridData L sc) (t : T) (w : Pl D.host.E)
    (β : Cosets (G := locGrid G t w) one_le_sLen (givenLevel G t w))
    (hβ : ∀ i, β i = DoubleCoset.mk _ _ (stair (locGrid G t w) (unifAt w) (cosExp G w) (i + 1))) :
    (repsAt G t w).elt β = (stair0 G w : (locGrid G t w).VertexGroup) := by
  have hb : β = fun i : Fin _ => DoubleCoset.mk _ _ (stair (locGrid G t w) (unifAt w) (cosExp G w) (i.1 + 1)) := funext hβ
  subst hb
  funext X
  obtain ⟨i, j⟩ := X
  by_cases hi : i = D.R.m
  · subst hi
    have e1 : (stair0 G w : (locGrid G t w).VertexGroup) (D.R.m, j) =
        if j + 2 ≤ D.R.m then stair (locGrid G t w) (unifAt w) (cosExp G w) j else 1 := onColumn_apply (G := grid0 G w) _ j
    rw [e1]
    split_ifs with hj
    · exact through_elt _ hj
    · exact elt_eq_one t w _ (by omega)
  · show onColumn (G := locGrid G t w) _ (i, j) = onColumn (G := grid0 G w) _ (i, j)
    rw [onColumn, onColumn, dite_eq_right (show ¬ (i, j).1 = (locGrid G t w).m from hi),
      dite_eq_right (show ¬ (i, j).1 = (grid0 G w).m from hi)]
    rfl

end Grid0


open Classical in
theorem scal : Big fun ch => ScalP ch := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  refine ⟨fun w => if w ∈ ch.G.pl.W0 then
      ((charFactor (grid0 ch.G w) (eps0 ch.G w) * charFactor (grid0 ch.G w) (stair0 ch.G w) : ℂˣ) : ℂ) else 1,
    fun t w => (xiPart (locGrid ch.G t w) ((R.toLevCh.xiH t).loc w) (epsV ch.G t w) *
      if w ∈ ch.G.pl.W0 then xiPart (locGrid ch.G t w) ((R.toLevCh.xiH t).loc w) (stair0 ch.G w) else 1)⁻¹,
    fun t w => ?_, fun w hw => if_neg hw, fun t w hw β hβ => ?_⟩
  · have hH : ∀ x, (R.toLevCh.xiH t).loc w x ∈ xiVals R.toLevCh t := fun x => Subgroup.subset_closure ⟨w, x, rfl⟩
    refine inv_mem (mul_mem (xiPart_mem _ _ _ _ hH) ?_)
    split_ifs
    · exact xiPart_mem _ _ _ _ hH
    · exact one_mem _
  · have hmu : ∀ j, (locGrid ch.G t w).mu j = (fun j => (muBase R.toLevCh j).loc w) j * (R.toLevCh.xiH t).loc w :=
      fun j => MonoidHom.ext fun _ => rfl
    have hsplit := charFactor_split (locGrid ch.G t w) _ _ hmu
    dsimp only
    unfold zetaLoc
    rw [prod_edgeFactor _ _ (epsV_mem t w)]
    by_cases h0 : w ∈ ch.G.pl.W0
    · have hk : keepAt ch.G w = false := by simp [keepAt, h0]
      rw [hk, if_pos h0, if_pos h0, elt_stair ch.G t w β (hβ h0)]
      have key : charFactor (locGrid ch.G t w) (epsV ch.G t w) * charFactor (locGrid ch.G t w) (stair0 ch.G w) =
          (charFactor (grid0 ch.G w) (eps0 ch.G w) * charFactor (grid0 ch.G w) (stair0 ch.G w)) *
          ((xiPart (locGrid ch.G t w) ((R.toLevCh.xiH t).loc w) (epsV ch.G t w) *
            xiPart (locGrid ch.G t w) ((R.toLevCh.xiH t).loc w) (stair0 ch.G w))⁻¹)⁻¹ := by
        rw [inv_inv, hsplit (epsV ch.G t w), hsplit (stair0 ch.G w)]
        exact mul_mul_mul_comm _ _ _ _
      simp only [Bool.false_eq_true, if_false]
      rw [← Units.val_inv_eq_inv_val, ← Units.val_mul, ← Units.val_mul]
      exact congrArg Units.val key
    · have hk : keepAt ch.G w = true := by simp [keepAt, h0]
      rw [hk, if_neg h0, if_neg h0, if_pos rfl]
      have ha : w.under (𝓞 D.host.F) ∉ ch.G.pl.S0 := by
        rcases GlobalTheory.FunObj.Good.locPl_cases hw with ⟨a, b⟩ | ⟨a, -, -⟩
        · exact absurd (by rw [b]; exact Finset.mem_image_of_mem ch.G.pl.w a) h0
        · exact a
      have hoff : ∀ i j, i ≠ D.R.m → epsV ch.G t w (i, j) = 1 := fun i j hi => by
        show onColumn (G := locGrid ch.G t w) _ (i, j) = 1
        rw [onColumn, dite_eq_right (show ¬ (i, j).1 = (locGrid ch.G t w).m from hi)]
      have h1 : charFactor ({locGrid ch.G t w with mu := fun j => (muBase R.toLevCh j).loc w} : Grid (Kw w))
          (epsV ch.G t w) = 1 := by
        refine charFactor_eq_one _ _ (epsV_mem t w) (fun i hi => ⟨hoff i _ (Nat.ne_of_lt hi), ?_⟩) (fun j hj => ?_) ?_
        · by_cases e : i + 1 = D.R.m
          · show epsV ch.G t w (i + 1, D.R.m) = 1
            rw [show (i + 1, D.R.m) = (D.R.m, D.R.m) by rw [e]]
            exact epsV_eq_one t w (by omega)
          · exact hoff _ _ e
        · replace hj : j < D.R.m := hj
          show IsUnram ((muBase R.toLevCh (j + 1)).loc w)
          rw [muBase, dite_eq_left hj]
          refine GlobalTheory.FunObj.Good.isUnram_loc.2 ((R.toLevCh.C.isMu0 ⟨j, hj⟩).unr w fun k hk => ?_)
          refine ha (ch.G.pl.mem_S0_of_sum_eq.2 (Or.inr ((GlobalTheory.ChiGrid.S1_mem_OmF D).2 ?_)))
          have : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (w.under (𝓞 D.host.F)).asIdeal := by
            show algebraMap _ (𝓞 D.host.E) _ ∈ w.asIdeal
            rw [map_natCast]; exact hk
          fin_cases k
          · exact Or.inl this
          · exact Or.inr (Or.inl this)
        · exact GlobalTheory.FunObj.Good.isUnram_loc.2 (R.toLevCh.C.isEta.unr w)
      simp only [hsplit (epsV ch.G t w), h1, one_mul, mul_one, Units.val_inv_eq_inv_val, inv_inv]

end

end GlobalTheory.FlatScal
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rowTest_lastColumn_level_iff_gridVertexLevelVolumeOne : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ t i (hi : i ≤ D.R.m) (k : FinPt ch.G (.grid i D.R.m)), finG (ch.G.V (.grid i D.R.m)) k ∈ ch.S.toGridChoice.levRow t i hi ↔ finG (ch.G.V (.grid i D.R.m)) k ∈ levJ ch.G t (.grid i D.R.m) := by
  first | exact @GlobalTheory.RowLevelUnit.levRow_iff_levJ | exact GlobalTheory.RowLevelUnit.levRow_iff_levJ | (intros; apply GlobalTheory.RowLevelUnit.levRow_iff_levJ <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open GlobalTheory.FlipRun
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.last_row_column_product_data_have_vectors : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (e : AE D), IsIdemSum e (locPl ch.G t) → ∀ (φ : (∀ w : locPl ch.G t, ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ)), (∀ w : locPl ch.G t, ∀ b ∈ GlobalTheory.SplitFlip.oppositePath D.R.m, GlobalTheory.SplitFlip.IsNatDatum (unifAt w.1) (depthAt ch.G w.1) (φ w b)) → (∀ j : Fin D.R.m, ∃ f, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) f) ∧ ∀ i : Fin D.R.m, ∃ f, IsLocVec ch.W (.chi i D.R.m) e (ch.rm.vX i D.R.m) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.ex i D.R.m) (ch.S.B.coord t w.1 (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) f := by
  first | exact @GlobalTheory.VecsLast.vecs_last | exact GlobalTheory.VecsLast.vecs_last | (intros; apply GlobalTheory.VecsLast.vecs_last <;> assumption)
end

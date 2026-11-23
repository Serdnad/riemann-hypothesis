module

public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle521
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle620
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle570
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle539
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle073
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1780
public import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle154
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle579
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle578
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1244
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1782
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1783
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1784
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1270
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.OriginBox
open GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx

section Flat
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]


open Classical in
theorem flatTensor_moved_box (G : Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k) (hν : IsUnitVol ν)
    (ϖ : kˣ) (a a' : ℤ) (hψ : ∀ y : k, valuation k y ≤ valuation k ((ϖ ^ (a + a') : kˣ) : k) → ψ y = 1)
    (g : G.VertexGroup) (hg : ∀ j, g (G.m, j) = colDiag G ϖ a a' j) :
    flatTensor hs ψ ν (moved G false g (Set.indicator
      {z : G.Args | ∀ b ∈ oppositePath G.m, ∀ i j, (((ϖ ^ a)⁻¹ : kˣ) : k) * z b i j ∈ 𝒪[k]} 1)) 0 0 =
    ((oppositePath G.m).map fun b => apow (gdet (g b.src))⁻¹ ((G.rank b.tgt : ℂ) / 2) *
      apow (gdet (g b.tgt))⁻¹ (-(G.rank b.src : ℂ) / 2)).prod *
      ∏ j, ∏ v, ((nabs k (ϖ ^ boxExp G a a' j v) : ℝ) : ℂ) := by
  set P := ((oppositePath G.m).map fun b => apow (gdet (g b.src))⁻¹ ((G.rank b.tgt : ℂ) / 2) *
      apow (gdet (g b.tgt))⁻¹ (-(G.rank b.src : ℂ) / 2)).prod
  have key : flatIntegrand hs ψ (moved G false g (Set.indicator
      {z : G.Args | ∀ b ∈ oppositePath G.m, ∀ i j, (((ϖ ^ a)⁻¹ : kˣ) : k) * z b i j ∈ 𝒪[k]} 1)) 0 0 =
      (box G ϖ a a').indicator fun _ => P := by
    funext e
    rw [flatIntegrand, moved_false, GlobalTheory.T.indicator_moveArgs_origin_eq_box_indicator G hs ϖ a a' g hg e]
    by_cases he : e ∈ box G ϖ a a'
    · have h1 := GlobalTheory.T.unfoldingCharacterPhase_origin_valuation_le_box G ϖ a a' e he
      rw [Set.indicator_of_mem he, Set.indicator_of_mem he, hψ _ (by rwa [Valuation.map_neg])]
      simp only [Pi.one_apply, mul_one, Circle.coe_one, P]
    · rw [Set.indicator_of_notMem he, Set.indicator_of_notMem he]
      simp
  rw [flatTensor, key, integral_indicator_const _ (measurableSet_box G ϖ a a'), Measure.real, vol_box G ν hν ϖ a a',
    Complex.real_smul, mul_comm]
  push_cast
  rfl

end Flat
end GlobalTheory.OriginBox

namespace GlobalTheory.OriginBox
open GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx

section Expo
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k]

theorem flatTensor_moved_box_apow (G : Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k) (hν : IsUnitVol ν)
    (ϖ : kˣ) (a a' : ℤ) (hψ : ∀ y : k, valuation k y ≤ valuation k ((ϖ ^ (a + a') : kˣ) : k) → ψ y = 1)
    (g : G.VertexGroup) (hg : ∀ j, g (G.m, j) = colDiag G ϖ a a' j) (hg' : ∀ i j, i ≠ G.m → g (i, j) = 1) :
    flatTensor hs ψ ν (moved G false g (Set.indicator
      {z : G.Args | ∀ b ∈ oppositePath G.m, ∀ i j, (((ϖ ^ a)⁻¹ : kˣ) : k) * z b i j ∈ 𝒪[k]} 1)) 0 0 =
    apow ϖ (-(expo G a a' : ℂ) / 2) := by
  classical
  have hn : ∀ x : kˣ, ((nabs k x : ℝ) : ℂ) = apow x 1 := fun x => by simp [apow]
  rw [flatTensor_moved_box G hs ψ ν hν ϖ a a' hψ g hg]
  simp_rw [gdet_eq ϖ a a' g hg hg', ← _root_.zpow_neg, apow_zpow, ← apow_add, hn, apow_zpow, prod_apow_finset,
    prod_apow_list, ← apow_add]
  congr 1
  have hl : ∀ l : List Edge, (l.map fun b => ((-vtxDet G a a' b.src : ℤ) : ℂ) * ((G.rank b.tgt : ℂ) / 2) +
      ((-vtxDet G a a' b.tgt : ℤ) : ℂ) * (-(G.rank b.src : ℂ) / 2)).sum =
      -(((l.map fun b => vtxDet G a a' b.src * G.rank b.tgt - vtxDet G a a' b.tgt * G.rank b.src).sum : ℤ) : ℂ) / 2 := by
    intro l
    induction l with
    | nil => simp
    | cons b l ih => simp only [List.map_cons, List.sum_cons, ih]; push_cast; ring
  rw [hl, expo]
  push_cast
  simp only [mul_one]
  ring

end Expo
end GlobalTheory.OriginBox
namespace GlobalTheory.OriginBox
open GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx

section Generic
variable {k : Type} [Field k]

theorem colDiag_eq_one (G : Grid k) (hs : 1 ≤ G.s) (ϖ : kˣ) (a a' : ℤ) {j : ℕ} (hj : G.m - 1 ≤ j) :
    colDiag G ϖ a a' j = 1 := by
  refine Units.ext ?_
  rw [colDiag, diagGL_val, Units.val_one, ← diagonal_one]
  congr 1
  funext x
  have h := topRank_add hs j
  have hx := x.2
  rw [vtxExp, if_neg (by omega), zpow_zero, Units.val_one]

end Generic

variable {D : D7}

theorem aaElt_eq (w : Pl D.host.E) (j : ℕ) :
    aaElt w j = colDiag (bareGrid w) (unifAt w) (FractionalIdeal.count D.host.E w D.host.AA)
      (FractionalIdeal.count D.host.E w D.host.AAbar) j := by
  refine Units.ext ?_
  rw [aaElt, colDiag, diagGL_val, diagGL_val]
  congr 1
  funext x
  have h := topRank_add (G := bareGrid w) one_le_sLen j
  have hx := x.2
  simp only [vtxExp]
  split_ifs with h1
  · simp only [genAt, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_neg, ← _root_.zpow_add, Units.val_zpow_eq_zpow_val]
    congr 1
    have : x.val - topRank (bareGrid w) j < D.R.m - 1 - j := by
      change topRank (bareGrid w) j + D.R.m = (bareGrid w).rank ((bareGrid w).m, j) + j + 1 at h
      change (x : ℕ) < (bareGrid w).rank ((bareGrid w).m, j) at hx
      omega
    change _ = _ * (((D.R.m - 1 - j : ℕ) : ℤ) - _) - _
    push_cast [Nat.sub_sub]
    rw [show D.R.m - (1 + j + (x.val - topRank (bareGrid w) j)) = D.R.m - (1 + j) - (x.val - topRank (bareGrid w) j) by omega,
      Nat.cast_sub (by omega)]
    ring
  · simp

theorem aaElt_elt_col (w : Pl D.host.E) (j : ℕ) :
    (Reps.through (G := bareGrid w) one_le_sLen (fun _ => KO _ _) (aaElt w)).elt
      (fun i => DoubleCoset.mk _ _ (aaElt w (i + 1))) ((bareGrid w).m, j) =
    colDiag (bareGrid w) (unifAt w) (FractionalIdeal.count D.host.E w D.host.AA)
      (FractionalIdeal.count D.host.E w D.host.AAbar) j := by
  unfold Reps.elt
  rw [onColumn_apply]
  cases j with
  | zero => exact aaElt_eq w 0
  | succ i =>
    simp only [Reps.through]
    split_ifs with h
    · exact aaElt_eq w (i + 1)
    · exact (colDiag_eq_one _ one_le_sLen _ _ _ (by omega)).symm

theorem aaElt_elt_off (w : Pl D.host.E) (i j : ℕ) (hi : i ≠ (bareGrid w).m) :
    (Reps.through (G := bareGrid w) one_le_sLen (fun _ => KO _ _) (aaElt w)).elt
      (fun i => DoubleCoset.mk _ _ (aaElt w (i + 1))) (i, j) = 1 := by
  simp [Reps.elt, onColumn, hi]

theorem rank_le_bigN (w : Pl D.host.E) (i j : ℕ) (hi : i ≤ (bareGrid w).m) (hj : j ≤ (bareGrid w).m) :
    (bareGrid w).rank (i, j) ≤ bigN D := by
  have h1 := Nat.mul_le_mul_right D.R.t hj
  have h2 := Nat.mul_le_mul_right (sLen D) hi
  have hr : D.R.r ≤ D.R.k + D.R.m := by
    have : D.R.r = D.R.k + D.R.m - 1 := rfl
    omega
  change D.R.r + j * D.R.t + i * sLen D ≤ D.R.k + D.R.m * (D.R.t + sLen D + 1)
  change i ≤ D.R.m at hi
  change j ≤ D.R.m at hj
  nlinarith

theorem aaTerm_datum_origin : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (w : Pl D.host.E), (∀ a : Kw w, valuation (Kw w) a ≤ valuation (Kw w) ((genAt w D.host.AA * genAt w D.host.AAbar : (Kw w)ˣ) : Kw w) → psiAt W w a = 1) → ∃ n : ℤ, (aaTerm W w).datum 0 0 = (resCard (Kw w) : ℂ) ^ ((n : ℂ) / 2) ∧ |n| ≤ 8 * ((D.R.m : ℤ) ^ 3 * (bigN D : ℤ) ^ 2 * (|FractionalIdeal.count D.host.E w D.host.AA| + |FractionalIdeal.count D.host.E w D.host.AAbar|)) := by
  intro D T L sc G W w hψ
  have hψ' : ∀ y : Kw w, valuation (Kw w) y ≤ valuation (Kw w) (((unifAt w) ^ (FractionalIdeal.count D.host.E w D.host.AA +
      FractionalIdeal.count D.host.E w D.host.AAbar) : (Kw w)ˣ) : Kw w) → psiAt W w y = 1 := fun y hy =>
    hψ y (by rwa [genAt, genAt, ← _root_.zpow_add])
  have key := flatTensor_moved_box_apow (bareGrid w) one_le_sLen (psiAt W w) (unitVol w) (isUnitVol_unitVol w) (unifAt w)
    _ _ hψ' _ (aaElt_elt_col w) (aaElt_elt_off w)
  refine ⟨expo (bareGrid w) (FractionalIdeal.count D.host.E w D.host.AA) (FractionalIdeal.count D.host.E w D.host.AAbar),
    ?_, GlobalTheory.T.abs_originBoxValueExponent_le (bareGrid w) one_le_sLen _ _ (bigN D) (rank_le_bigN w)⟩
  change flatTensor _ _ _ _ 0 0 = _
  rw [aaVac, genAt] at *
  rw [key, IsUnif.apow_eq (isUnif_unifAt w)]
  congr 1
  ring

end GlobalTheory.OriginBox
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PullVanish

theorem isLocallyNoetherian_of_proj {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)]
    (hp : IsProjOver (strHom k (X := X))) : IsLocallyNoetherian X := by
  obtain ⟨N, ι, _, h⟩ := hp
  have : LocallyOfFiniteType (strHom k (X := X)) := h ▸ inferInstance
  exact LocallyOfFiniteType.isLocallyNoetherian (strHom k X)

theorem isProjOver_red {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)]
    (hp : IsProjOver (strHom k (X := X))) (Z : Closeds X) :
    letI := algebraΓAlong k (redι Z)
    IsProjOver (strHom k (X := (Scheme.IdealSheafData.vanishingIdeal Z).subscheme)) := by
  letI := algebraΓAlong k (redι Z)
  rw [← comp_strHom (g := redι Z) fun _ => rfl]
  exact ProjSpace.isProjOver_comp_of_isClosedImmersion _ hp

theorem dim_closure_add_one_le {T : Type*} [TopologicalSpace T] [QuasiSober T] {x y : T}
    (hyx : y ⤳ x) {U : Set T} (hU : IsOpen U) (hy : y ∈ U) (hx : x ∉ U) :
    topologicalKrullDim (closure ({x} : Set T)) + 1 ≤ topologicalKrullDim (closure ({y} : Set T)) := by
  refine topologicalKrullDim_add_one_le isClosed_closure isClosed_closure fun z hz => ⟨y, subset_closure rfl, fun h => ?_, hyx.trans (specializes_iff_mem_closure.2 hz)⟩
  exact hx ((specializes_iff_mem_closure.2 h).mem_open hU hy)

theorem withBot_le_of_add_one_le {a : WithBot ℕ∞} {n : ℕ} (h : a + 1 ≤ ((n + 1 : ℕ) : WithBot ℕ∞)) :
    a ≤ (n : WithBot ℕ∞) := by
  first
  | exact @_root_.GlobalTheory.NatCastUpperBound.le_natCast_of_add_one_le
  | exact _root_.GlobalTheory.NatCastUpperBound.le_natCast_of_add_one_le
  | (apply _root_.GlobalTheory.NatCastUpperBound.le_natCast_of_add_one_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatCastUpperBound.le_natCast_of_add_one_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatCastUpperBound.le_natCast_of_add_one_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatCastUpperBound.le_natCast_of_add_one_le ..)

theorem withBot_lt_of_add_one_lt {a : WithBot ℕ∞} {n : ℕ} (h : a + 1 < ((n + 1 : ℕ) : WithBot ℕ∞)) :
    a < (n : WithBot ℕ∞) := by
  first
  | exact @_root_.GlobalTheory.NatCastStrictBound.lt_natCast_of_add_one_lt_succ
  | exact _root_.GlobalTheory.NatCastStrictBound.lt_natCast_of_add_one_lt_succ
  | (apply _root_.GlobalTheory.NatCastStrictBound.lt_natCast_of_add_one_lt_succ <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatCastStrictBound.lt_natCast_of_add_one_lt_succ <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatCastStrictBound.lt_natCast_of_add_one_lt_succ <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatCastStrictBound.lt_natCast_of_add_one_lt_succ ..)

def sumOptionEquiv (e r : ℕ) : Fin e ⊕ Option (Fin r) ≃ Option (Fin e ⊕ Fin r) where
  toFun
    | .inl i => some (.inl i)
    | .inr none => none
    | .inr (some b) => some (.inr b)
  invFun
    | none => .inr none
    | some (.inl i) => .inl i
    | some (.inr b) => .inr (some b)
  left_inv := by rintro (i | _ | b) <;> rfl
  right_inv := by rintro (_ | i | b) <;> rfl

def frontEquiv (e r : ℕ) : Fin e ⊕ Fin (r + 1) ≃ Fin (e + r + 1) :=
  ((Equiv.sumCongr (Equiv.refl _) (finSuccEquiv r)).trans (sumOptionEquiv e r)).trans
    ((Equiv.optionCongr finSumFinEquiv).trans (finSuccEquiv (e + r)).symm)

theorem cons_comp_frontEquiv {X : Scheme.{0}} {e r : ℕ} (P : Fin e → LB X) (B : Fin (r + 1) → LB X) :
    (Fin.cons (B 0) (Sum.elim P (fun a => B a.succ) ∘ finSumFinEquiv.symm) : Fin (e + r + 1) → LB X) ∘
      frontEquiv e r = Sum.elim P B := by
  funext x
  rcases x with i | a
  · simp [frontEquiv, sumOptionEquiv]
  · refine Fin.cases ?_ (fun b => ?_) a
    · simp [frontEquiv, sumOptionEquiv]
    · simp [frontEquiv, sumOptionEquiv]

end GlobalTheory.PullVanish

namespace GlobalTheory.PullVanish

theorem redι_genericPoint {X : Scheme.{0}} (w : X)
    [IsIntegral (Scheme.IdealSheafData.vanishingIdeal (⟨closure {w}, isClosed_closure⟩ : Closeds X)).subscheme] :
    redι (⟨closure {w}, isClosed_closure⟩ : Closeds X) (genericPoint _) = w := by
  set ι := redι (⟨closure {w}, isClosed_closure⟩ : Closeds X)
  have hr := range_redι (⟨closure {w}, isClosed_closure⟩ : Closeds X)
  have h₁ : w ⤳ ι (genericPoint _) :=
    specializes_iff_mem_closure.2 (by
      have : ι (genericPoint _) ∈ Set.range ι := ⟨_, rfl⟩
      rw [hr] at this; exact this)
  obtain ⟨y, hy⟩ : w ∈ Set.range ι := by rw [hr]; exact subset_closure rfl
  have h₂ : ι (genericPoint _) ⤳ w := by
    have := (genericPoint_specializes y).map ι.continuous
    rwa [hy] at this
  exact (h₁.antisymm h₂).eq.symm

theorem interNum_pull_eq_zero : ∀ (κ : Type) [Field κ] (e r : ℕ) (Z W : Scheme.{0}) [IsIntegral Z] [Algebra κ Γ(Z, ⊤)], IsProjOver (strHom κ (X := Z)) → topologicalKrullDim Z ≤ (e + r : ℕ) → ∀ g : Z ⟶ W, topologicalKrullDim (closure ({g (genericPoint Z)} : Set W)) < (r : ℕ) → ∀ (P : Fin e → LB Z), (∀ i, (P i).IsLB) → ∀ (A : Fin r → LB W), (∀ i, (A i).IsLB) → interNum κ (structureModule Z) (Sum.elim P fun a => (A a).pull g) = 0 := by
  intro κ _ e r
  induction r with
  | zero =>
    intro Z W _ _ _ _ g hg
    exfalso
    have h0 : (0 : WithBot ℕ∞) ≤ topologicalKrullDim (closure ({g (genericPoint Z)} : Set W)) := by
      haveI : Nonempty (IrreducibleCloseds (closure ({g (genericPoint Z)} : Set W))) :=
        ⟨⟨closure {⟨g (genericPoint Z), subset_closure rfl⟩}, isIrreducible_singleton.closure,
          isClosed_closure⟩⟩
      exact Order.krullDim_nonneg
    rw [Nat.cast_zero] at hg
    exact absurd hg (not_lt.2 h0)
  | succ r ih =>
    intro Z W _ _ hp hd g hg P hP A hA
    have := isLocallyNoetherian_of_proj hp
    obtain ⟨i₀, hi₀⟩ : ∃ i, g (genericPoint Z) ∈ (A 0).U i := by
      have : g (genericPoint Z) ∈ (⨆ i, (A 0).U i : W.Opens) := by
        rw [(hA 0).cover]; trivial
      exact TopologicalSpace.Opens.mem_iSup.1 this
    set M : LB Z := (A 0).pull g with hMdef
    have hM : M.IsLB := pull_isLB (hA 0) g
    let j₀ : M.ι := fun _ => i₀
    have hmem : ∀ x : Z, x ∈ M.U j₀ ↔ g x ∈ (A 0).U i₀ := fun x =>
      ⟨fun h => Set.mem_iInter.1 h PUnit.unit, fun h => Set.mem_iInter.2 fun _ => h⟩
    have hη : genericPoint Z ∈ M.U j₀ := (hmem _).2 hi₀
    have hs := isRatSec_frameRat hM j₀ hη
    set Q : Fin (e + r) → LB Z := Sum.elim P (fun a : Fin r => (A a.succ).pull g) ∘ finSumFinEquiv.symm with hQdef
    have hQ' : ∀ x, (Sum.elim P (fun a : Fin r => (A a.succ).pull g) x).IsLB := by
      rintro (i | a)
      · exact hP i
      · exact pull_isLB (hA _) g
    have hQ : ∀ i, (Q i).IsLB := fun i => hQ' _
    have key : interNum κ (structureModule Z) (Sum.elim P fun a => (A a).pull g) =
        interNum κ (structureModule Z) (Fin.cons M Q : Fin (e + r + 1) → LB Z) := by
      rw [← interNum_comp_equiv κ _ (isLB_cons hM hQ) (frontEquiv e r)]
      exact congrArg _ (cons_comp_frontEquiv P (fun a => (A a).pull g)).symm
    rw [key, GlobalTheory.T.rational_section_cycle_formula_projective κ Z hp (e + r) hd M hM Q hQ _ hs]
    refine finsum_eq_zero_of_forall_eq_zero fun w => ?_
    by_cases hw : (divOfRatSec hM hs).mult w = 0
    · rw [hw, zero_mul]
    have hwU : w ∉ M.U j₀ := fun h => hw (by
      rw [((presents_divOfRatSec hM hs).isEqn j₀ w h).mult_eq, frameRat_self hM j₀ hη, Units.val_one]
      exact (unitAt_one w).ord_eq_zero)
    suffices h : interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds Z) Q = 0 by rw [h, mul_zero]
    set C : Closeds Z := ⟨closure {w}, isClosed_closure⟩ with hC
    haveI : IsIntegral (Scheme.IdealSheafData.vanishingIdeal C).subscheme :=
      isIntegral_red isIrreducible_singleton.closure
    letI := algebraΓAlong κ (redι C)
    have hιw : redι C (genericPoint _) = w := redι_genericPoint w
    rw [interNumRed_def, interNumSub_def,
      interNumOn_eq_interNum_pull (k := κ) (f := redι C) (fun _ => rfl) hQ]
    have e1 : interNum κ (structureModule _) (fun i => (Q i).pull (redι C)) =
        interNum κ (structureModule _)
          (fun x => (Sum.elim P (fun a : Fin r => (A a.succ).pull g) x).pull (redι C)) :=
      by
        set_option maxHeartbeats 12000000 in
          exact interNum_comp_equiv κ _ (fun x => pull_isLB (hQ' x) (redι C)) finSumFinEquiv.symm
    have e2 : interNum κ (structureModule _)
          (fun x => (Sum.elim P (fun a : Fin r => (A a.succ).pull g) x).pull (redι C)) =
        interNum κ (structureModule _)
          (Sum.elim (fun i => (P i).pull (redι C)) fun a : Fin r => (A a.succ).pull (redι C ≫ g)) := by
      refine interNum_congr_cls κ _ (fun x => pull_isLB (hQ' x) (redι C)) ?_ ?_
      · rintro (i | a)
        · exact pull_isLB (hP i) _
        · exact pull_isLB (hA _) _
      · rintro (i | a)
        · rfl
        · simp only [Sum.elim_inr]
          rw [CechPic.cls_pull (pull_isLB (hA _) g), CechPic.cls_pull (hA _) g,
            CechPic.cls_pull (hA _) (redι C ≫ g), CechPic.pull_comp]
    rw [e1, e2]
    refine ih _ W (isProjOver_red hp C) ?_ (redι C ≫ g) ?_ _ (fun i => pull_isLB (hP i) _) _
      (fun a => hA _)
    · rw [topologicalKrullDim_red]
      have h1 := dim_closure_add_one_le (genericPoint_specializes w) (M.U j₀).isOpen hη hwU
      have h2 : topologicalKrullDim (closure ({genericPoint Z} : Set Z)) = topologicalKrullDim Z := by
        rw [(genericPoint_spec Z).def]
        exact (Homeomorph.Set.univ Z).isHomeomorph.topologicalKrullDim_eq
      exact withBot_le_of_add_one_le (h1.trans (h2.trans_le hd))
    · rw [Scheme.Hom.comp_apply, hιw]
      have h1 := dim_closure_add_one_le ((genericPoint_specializes w).map g.continuous)
        ((A 0).U i₀).isOpen hi₀ (fun h => hwU ((hmem w).2 h))
      exact withBot_lt_of_add_one_lt (lt_of_le_of_lt h1 hg)

end GlobalTheory.PullVanish
end
end

section

open MeasureTheory GlobalTheory.Orb GlobalTheory.PsCo.Pc1
open Formalism.REAL (UJ KG toM expG inG)

namespace GlobalTheory.PsCo.Pc1

theorem orbInt_adSpan_eq_zero : GlobalTheory.PsCo.Pc1.StOrbAd := by
  intro n ε μ _ s hs dt _ _ φ hφ
  haveI : μ.IsMulRightInvariant := GlobalTheory.T.indefiniteUnitaryGroup_haar_isMulRightInvariant n ε μ
  have hp := isProperOrbit_realUJ hs
  induction hφ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨Z, H, P, hZ, hH, rfl⟩ := hφ
    have hZ' : inG ε Z := (GlobalTheory.T.indefiniteUnitaryLieAlgebra_mem_iff_entries n ε Z).2 hZ
    obtain ⟨hc, hinv⟩ := GlobalTheory.expG_continuous_inv n ε Z hZ'
    obtain ⟨hsh, hd⟩ := GlobalTheory.PsCo.Pc1.B.cutoffPolynomial_conjugation_deriv_mem_shapeSpan n ε Z H P hZ hH
    have hb : bas ε H P ∈ ShapeM ε P.totalDegree := Submodule.subset_span ⟨H, P, hH, le_rfl, rfl⟩
    obtain ⟨-, -, h1, h2⟩ := GlobalTheory.T.pseudoCoeffShape_smooth_compactSupport n ε _ _ hb
    obtain ⟨-, -, h3, h4⟩ := GlobalTheory.T.pseudoCoeffShape_smooth_compactSupport n ε _ _ hsh
    refine hasOrbInt_zero_of_hasDerivAt_conj (UJ ε) μ s hp dt (fun t => expG ε Z t) hc _ _ h1 h2 h3 h4 fun g u => ?_
    have e : ∀ v : ℝ, toM ((expG ε Z v)⁻¹ * g * expG ε Z v) =
        NormedSpace.exp (-((v : ℂ) • Z)) * toM g * NormedSpace.exp ((v : ℂ) • Z) := fun v => by
      rw [← hinv v, ← Formalism.REAL.toM_expG ε Z v hZ']
      rfl
    simp only [e]
    exact hd (toM g) u
  | zero =>
    have h := (hp.hasOrbInt (dh := μ) (dt := dt) (f := fun _ => (0 : ℂ)) continuous_const HasCompactSupport.zero).smul 0
    rw [zero_mul, zero_smul] at h
    exact h
  | add φ ψ _ _ h1 h2 =>
    have h := h1.add h2
    rw [add_zero] at h
    exact h
  | smul a φ _ h1 =>
    have h := h1.smul a
    rw [mul_zero] at h
    exact h

end GlobalTheory.PsCo.Pc1
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

theorem _root_.GlobalTheory.T.normCommuting_twistedConj_compact_mem_twistedCentralizer_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : GLw n w), (nrmL n w y).val.charpoly.Separable → ∀ C : Set (GLw n w), IsCompact C → ∃ D : Set (GLw n w), IsCompact D ∧ ∀ z : GLw n w, z * nrmL n w y = nrmL n w y * z → z⁻¹ * y * thL n w z ∈ C → ∃ t ∈ twCent (thL n w) y, ∃ d ∈ D, z = t * d := by
  first | exact @GlobalTheory.NormOneProper.main | exact GlobalTheory.NormOneProper.main | (intros; apply GlobalTheory.NormOneProper.main <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct Pointwise

theorem _root_.GlobalTheory.T.regular_orbit_conj_compact_mod_centralizer_unitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : UL n w), y.1.val.charpoly.Separable → ∀ C : Set (UL n w), IsCompact C → ∃ Ω : Set (UL n w), IsCompact Ω ∧ ∀ g : UL n w, g⁻¹ * y * g ∈ C → ∃ t ∈ twCent (MonoidHom.id (UL n w)) y, ∃ ω ∈ Ω, g = t * ω := by
  first | exact @GlobalTheory.OrbitU.orbit_cpt_U | exact GlobalTheory.OrbitU.orbit_cpt_U | (intros; apply GlobalTheory.OrbitU.orbit_cpt_U <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

theorem _root_.GlobalTheory.T.continuous_involutive_local_transpose_inverse : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E), Continuous (thL n w) ∧ ∀ g : GLw n w, thL n w (thL n w g) = g := by
  first | exact @GlobalTheory.BCT.thL_continuous_involutive | exact GlobalTheory.BCT.thL_continuous_involutive | (intros; apply GlobalTheory.BCT.thL_continuous_involutive <;> assumption)
end

module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle108
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle418
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle008
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle009
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle081
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle433
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle434
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle435
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle061
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle082
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle431
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomog IsRelevant IsMultiProjPrime divSupp multAt geoNum charOf)
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ GlobalTheory GlobalTheory.ProjBlowup

namespace GlobalTheory.CompanionTheory.MPDict.ClsRep

open GlobalTheory.CompanionTheory.MPDict.IsomT GlobalTheory.CompanionTheory.MPDict.TensRep

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

def HasFrame (L : LB (MP ℤ m n)) (a : Fin (m + 1) → ℤ) : Prop :=
  ∃ u : ∀ (i : L.ι) (c : ∀ k, Bk n k), Γ(MP ℤ m n, L.U i ⊓ mchart c)ˣ,
    (∀ i j c,
      Semi.res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          L.U i ⊓ L.U j ⊓ mchart c ≤ L.U j ⊓ mchart c) (u j c) =
        Semi.res (inf_le_left : L.U i ⊓ L.U j ⊓ mchart c ≤ L.U i ⊓ L.U j) (L.g i j) *
          Semi.res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
            L.U i ⊓ L.U j ⊓ mchart c ≤ L.U i ⊓ mchart c) (u i c)) ∧
    (∀ i c c',
      Semi.res (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
          L.U i ⊓ (mchart c ⊓ mchart c') ≤ L.U i ⊓ mchart c) (u i c) =
        Semi.res (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
          L.U i ⊓ (mchart c ⊓ mchart c') ≤ L.U i ⊓ mchart c') (u i c') *
        ∏ k, blockUnit (c k) (c' k) (fun _ hx =>
          ⟨mchart_le c k hx.2.1, mchart_le c' k hx.2.2⟩ :
            L.U i ⊓ (mchart c ⊓ mchart c') ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k))) ^ a k)

theorem hasFrame_of_isHermRep {M : HermLB (mpStr ℤ m n)} {A : Geo.HermLine (Bk n)} (h : IsHermRep M A) :
    HasFrame M.B A.a := by
  obtain ⟨u, h₁, h₂, -⟩ := h
  exact ⟨u, h₁, h₂⟩

theorem iSup_mchart : ⨆ c : (∀ k, Bk n k), mchart c = (⊤ : (MP ℤ m n).Opens) := by
  refine top_le_iff.1 fun x _ => Opens.mem_iSup.2 ⟨fun k => ptChart x k, ?_⟩
  exact Set.mem_iInter.2 fun k => mem_ptChart x k

theorem cg₃ {G : Type*} [CommGroup G] {x x' y y' P : G} (h : x = x' * P) (h' : y = y' * P) :
    x * y⁻¹ = x' * y'⁻¹ := by
  subst h h'
  rw [mul_inv, mul_mul_mul_comm, mul_inv_cancel, mul_one]

theorem cg₄ {G : Type*} [CommGroup G] {x x' y y' g g' : G} (h : x' = g' * x) (h' : y' = g * y) :
    x * y⁻¹ = g * g'⁻¹ * (x' * y'⁻¹) := by
  subst h h'
  simp only [mul_inv]
  rw [show g * g'⁻¹ * (g' * x * (g⁻¹ * y⁻¹)) = (g * g⁻¹) * (g'⁻¹ * g') * (x * y⁻¹) by ac_rfl]
  simp

theorem lbIso_of_hasFrame {L N : LB (MP ℤ m n)} {a : Fin (m + 1) → ℤ} (hL : HasFrame L a) (hN : HasFrame N a) :
    LBIso L N := by
  obtain ⟨u, u₁, u₂⟩ := hL
  obtain ⟨v, v₁, v₂⟩ := hN
  have hglue (p : N.ι × L.ι) : ∃ t : Γ(MP ℤ m n, N.U p.1 ⊓ L.U p.2)ˣ, ∀ c,
      Semi.res inf_le_left t =
        Semi.res (ofMem fun _ hx => ⟨hx.1.2, hx.2⟩ : (N.U p.1 ⊓ L.U p.2) ⊓ mchart c ≤ L.U p.2 ⊓ mchart c) (u p.2 c) *
        (Semi.res (ofMem fun _ hx => ⟨hx.1.1, hx.2⟩ : (N.U p.1 ⊓ L.U p.2) ⊓ mchart c ≤ N.U p.1 ⊓ mchart c) (v p.1 c))⁻¹ := by
    refine exists_glue mchart iSup_mchart _ _ fun c c' => ?_
    have e₁ := (congrArg (Semi.res (ofMem fun _ hx => ⟨hx.1.1.2, hx.1.2, hx.2.2⟩ :
      ((N.U p.1 ⊓ L.U p.2) ⊓ mchart c) ⊓ ((N.U p.1 ⊓ L.U p.2) ⊓ mchart c') ≤ L.U p.2 ⊓ (mchart c ⊓ mchart c'))) (u₂ p.2 c c')).trans
      (res_mul_prod c c' a _ _ _)
    have e₂ := (congrArg (Semi.res (ofMem fun _ hx => ⟨hx.1.1.1, hx.1.2, hx.2.2⟩ :
      ((N.U p.1 ⊓ L.U p.2) ⊓ mchart c) ⊓ ((N.U p.1 ⊓ L.U p.2) ⊓ mchart c') ≤ N.U p.1 ⊓ (mchart c ⊓ mchart c'))) (v₂ p.1 c c')).trans
      (res_mul_prod c c' a _ _ _)
    simp only [map_mul, map_inv, res_twice] at e₁ e₂ ⊢
    exact cg₃ e₁ e₂
  choose t ht using hglue
  have htT (p : N.ι × L.ι) (c : ∀ k, Bk n k) {T : (MP ℤ m n).Opens} (hT : T ≤ (N.U p.1 ⊓ L.U p.2) ⊓ mchart c) :
      Semi.res (hT.trans inf_le_left) (t p) =
        Semi.res (ofMem fun _ hx => ⟨(hT hx).1.2, (hT hx).2⟩ : T ≤ L.U p.2 ⊓ mchart c) (u p.2 c) *
        (Semi.res (ofMem fun _ hx => ⟨(hT hx).1.1, (hT hx).2⟩ : T ≤ N.U p.1 ⊓ mchart c) (v p.1 c))⁻¹ := by
    have e := congrArg (Semi.res hT) (ht p c)
    simpa only [map_mul, map_inv, res_twice] using e
  refine ⟨⟨t⟩, fun (p q : N.ι × L.ι) => units_ext_cover mchart iSup_mchart fun c => ?_⟩
  change Semi.res (inf_le_left : (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ⊓ mchart c ≤ (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2))
      (Semi.res (inf_le_left : (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ≤ N.U p.1 ⊓ L.U p.2) (t p)) =
    Semi.res (inf_le_left : (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ⊓ mchart c ≤ (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2))
      ((Semi.res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
          (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ≤ N.U p.1 ⊓ N.U q.1) (N.g p.1 q.1) *
        (Semi.res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
          (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ≤ L.U p.2 ⊓ L.U q.2) (L.g p.2 q.2))⁻¹) *
        Semi.res (inf_le_right : (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ≤ N.U q.1 ⊓ L.U q.2) (t q))
  simp only [map_mul, map_inv, res_twice]
  rw [htT p c (T := (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ⊓ mchart c) (ofMem fun _ hx => ⟨hx.1.1, hx.2⟩),
    htT q c (T := (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ⊓ mchart c) (ofMem fun _ hx => ⟨hx.1.2, hx.2⟩)]
  have hU : (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ⊓ mchart c ≤ L.U p.2 ⊓ L.U q.2 ⊓ mchart c :=
    ofMem fun _ hx => ⟨⟨hx.1.1.2, hx.1.2.2⟩, hx.2⟩
  have hV : (N.U p.1 ⊓ L.U p.2) ⊓ (N.U q.1 ⊓ L.U q.2) ⊓ mchart c ≤ N.U p.1 ⊓ N.U q.1 ⊓ mchart c :=
    ofMem fun _ hx => ⟨⟨hx.1.1.1, hx.1.2.1⟩, hx.2⟩
  have e₁ := congrArg (Semi.res hU) (u₁ p.2 q.2 c)
  have e₂ := congrArg (Semi.res hV) (v₁ p.1 q.1 c)
  simp only [map_mul, res_twice] at e₁ e₂
  exact cg₄ e₁ e₂

theorem hasFrame_tens {L N : LB (MP ℤ m n)} {a b : Fin (m + 1) → ℤ} (hL : HasFrame L a) (hN : HasFrame N b) :
    HasFrame (GlobalTheory.CechPic.tens L N) (a + b) := by
  obtain ⟨u, hu₁, hu₂⟩ := hL
  obtain ⟨v, hv₁, hv₂⟩ := hN
  refine ⟨fun p c => mulUnit (u p.1 c) (v p.2 c), ?_, ?_⟩
  · rintro ⟨i, i'⟩ ⟨j, j'⟩ c
    exact frame_mulUnit _ _ _ _ _ _ _ _ _ _ _ _ (hu₁ i j c) (hv₁ i' j' c) _ _ _ _ _
  · rintro ⟨i, i'⟩ c c'
    exact mono_mulUnit a b _ _ _ _ _ _ _ _ _ _ (hu₂ i c c') (hv₂ i' c c') _ _ _

theorem hasFrame_dual {L : LB (MP ℤ m n)} {a : Fin (m + 1) → ℤ} (hL : HasFrame L a) :
    HasFrame (GlobalTheory.CechPic.dual L) (-a) := by
  obtain ⟨u, h1, h2⟩ := hL
  refine ⟨fun i c => (u i c)⁻¹, ?_, ?_⟩
  · intro i j c
    have e := h1 i j c
    change Semi.res _ (u j c)⁻¹ = Semi.res _ (L.g i j)⁻¹ * Semi.res _ (u i c)⁻¹
    rw [map_inv, map_inv, map_inv]
    exact (congrArg (·⁻¹) e).trans (mul_inv _ _)
  · intro i c c'
    have e := h2 i c c'
    change Semi.res _ (u i c)⁻¹ = Semi.res _ (u i c')⁻¹ * ∏ k, blockUnit (c k) (c' k) _ ^ (-a k)
    simp only [zpow_neg, Finset.prod_inv_distrib, map_inv]
    exact (congrArg (·⁻¹) e).trans (mul_inv _ _)

theorem hasFrame_triv : HasFrame (LB.triv (MP ℤ m n)) 0 := by
  refine ⟨fun _ _ => 1, ?_, ?_⟩
  · intro i j c
    simp only [map_one, mul_one]
  · intro i c c'
    simp

theorem res_pullO_g (k : Fin (m + 1)) (i j : Bk n k) {V : (MP ℤ m n).Opens}
    (h : V ≤ (pullO (prB n k) 1).U i ⊓ (pullO (prB n k) 1).U j) :
    Semi.res h ((pullO (prB n k) 1).g i j) = blockUnit i j h := by
  refine Units.ext ((val_res_pullO_g (prB n k) 1 i j h).trans ?_)
  rw [pow_one]
  exact (GlobalTheory.CompanionTheory.MPDict.Inhab.val_blockUnit i j h).symm

theorem hasFrame_pullO (k : Fin (m + 1)) : HasFrame (pullO (prB n k) 1) (Pi.single k 1) := by
  refine ⟨fun i c => blockUnit (c k) i (le_inf (inf_le_right.trans (mchart_le c k)) inf_le_left), ?_, ?_⟩
  · intro i j c
    refine (GlobalTheory.CompanionTheory.MPDict.res_blockUnit _ _ _ _).trans (Eq.trans ?_
      (congrArg₂ (· * ·) (res_pullO_g k i j _) (GlobalTheory.CompanionTheory.MPDict.res_blockUnit _ _ _ _)).symm)
    rw [mul_comm]
    exact (GlobalTheory.CompanionTheory.MPDict.Inhab.blockUnit_mul _ _ _ _ _ _).symm
  · intro i c c'
    refine (GlobalTheory.CompanionTheory.MPDict.res_blockUnit _ _ _ _).trans (Eq.trans ?_
      (congrArg₂ (· * ·) (GlobalTheory.CompanionTheory.MPDict.res_blockUnit _ _ _ _)
        (GlobalTheory.CompanionTheory.MPDict.Inhab.prod_blockUnit_single k c c' _)).symm)
    rw [mul_comm]
    exact (GlobalTheory.CompanionTheory.MPDict.Inhab.blockUnit_mul _ _ _ _ _ _).symm

theorem exists_hasFrame_cls (a : Fin (m + 1) → ℤ) : ∃ (L : LB (MP ℤ m n)) (hL : L.IsLB), HasFrame L a ∧
    cls L hL = ∑ k, a k • cls (pullO (prB n k) 1) (isLB_pullO _ 1) := by
  classical
  let H : AddSubgroup (Fin (m + 1) → ℤ) :=
    { carrier := {a | ∃ (L : LB (MP ℤ m n)) (hL : L.IsLB), HasFrame L a ∧
        cls L hL = ∑ k, a k • cls (pullO (prB n k) 1) (isLB_pullO _ 1)}
      add_mem' := by
        rintro a b ⟨L, hL, fL, eL⟩ ⟨N, hN, fN, eN⟩
        refine ⟨_, isLB_tens hL hN, hasFrame_tens fL fN, ?_⟩
        rw [cls_tens hL hN, eL, eN, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => (add_smul _ _ _).symm
      zero_mem' := ⟨_, LB.isLB_triv _, hasFrame_triv, by simp; rfl⟩
      neg_mem' := by
        rintro a ⟨L, hL, fL, eL⟩
        refine ⟨_, isLB_dual hL, hasFrame_dual fL, ?_⟩
        rw [cls_dual hL, eL, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun k _ => (neg_smul _ _).symm }
  have hs (k : Fin (m + 1)) : (Pi.single k 1 : Fin (m + 1) → ℤ) ∈ H := by
    refine ⟨_, isLB_pullO _ 1, hasFrame_pullO k, ?_⟩
    rw [Finset.sum_eq_single k (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zero_smul]) (by simp),
      Pi.single_eq_same, one_smul]
  have e : a = ∑ k, a k • (Pi.single k 1 : Fin (m + 1) → ℤ) := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  have : a ∈ H := e ▸ H.sum_mem fun k _ => H.zsmul_mem (hs k) _
  exact this

end GlobalTheory.CompanionTheory.MPDict.ClsRep

theorem GlobalTheory.CompanionTheory.MPDict.ClsRep.cls_eq_of_isHermRep : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (M : HermLB (mpStr ℤ m n)) (A : Geo.HermLine (Bk n)), IsHermRep M A → cls M.B M.isLB = ∑ k, A.a k • cls (pullO (prB n k) 1) (isLB_pullO _ 1) := by
  intro m n M A h
  obtain ⟨L, hL, fL, eL⟩ := GlobalTheory.CompanionTheory.MPDict.ClsRep.exists_hasFrame_cls (m := m) (n := n) A.a
  exact ((cls_eq_iff M.isLB hL).2 (GlobalTheory.CompanionTheory.MPDict.ClsRep.lbIso_of_hasFrame
    (GlobalTheory.CompanionTheory.MPDict.ClsRep.hasFrame_of_isHermRep h) fL)).trans eL
end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.positivity_pulls_back_to_subspace : ∀ (m n : ℕ) (G : Matrix (Fin m) (Fin m) ℂ) (y : Matrix (Fin m) (Fin n) ℂ) (ε : ℝ) (S : Submodule ℂ (Fin n → ℂ)), GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.PosOn ε (y.conjTranspose * G * y) S → ∃ T : Submodule ℂ (Fin m → ℂ), GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.PosOn ε G T ∧ Module.finrank ℂ T = Module.finrank ℂ S := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.exists_posOn_of_gram | exact GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.exists_posOn_of_gram | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.exists_posOn_of_gram <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch NumberField


theorem _root_.GlobalTheory.T.hermitian_archimedean_complex_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (e : Ainf F ≃+* (InfinitePlace F → ℝ)) (τ : InfinitePlace F → (E →+* ℂ))
  (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)), IsCoord σ e τ Θ →
  ∀ n : ℕ, ∃ Ψ : HermR (Ainf F) σ n ≃+ (InfinitePlace F → hermC n),
    (∀ b w, ((Ψ b w : hermC n) : Matrix (Fin n) (Fin n) ℂ) = matC Θ (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) w) ∧
    ∀ ν : Measure (HermR (Ainf F) σ n), ν.IsAddHaarMeasure →
      (ν.map Ψ).IsAddHaarMeasure ∧ ∀ G : (InfinitePlace F → hermC n) → ℂ, Integrable G (ν.map Ψ) → Integrable (fun b => G (Ψ b)) ν := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HermCoord.exists_hermEquiv | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HermCoord.exists_hermEquiv | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HermCoord.exists_hermEquiv <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch NumberField


theorem _root_.GlobalTheory.T.archimedean_character_in_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
  (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)) (τ : InfinitePlace F → (E →+* ℂ))
  (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)), IsCoord σ e τ Θ →
  (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) →
  ∀ (a : F) (ψ : AddChar (AF F) ℂ),
  (∀ x : Ainf F, ψ (pairA F x 0) = Complex.exp (2 * Real.pi * Complex.I * ((∑ w, ρ w a * e x w : ℝ) : ℂ))) →
  ∀ (M n : ℕ) (J : Matrix (Fin M) (Fin M) E) (B : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E))
    (X : Fin n → Fin M → Ainf F ⊗[F] E),
  psiInf F ψ (algebraMap F (Ainf F) (1 / 2) * Algebra.trace (Ainf F) (Ainf F ⊗[F] E)
      (Matrix.trace (B * gramR (Ainf F) σ J X))) =
    Complex.exp (2 * Real.pi * Complex.I * ((phaseM (fun w => ((ρ w a : ℝ) : ℂ) • J.map (τ w))
      (fun w => matC Θ B w) (tupC Θ X) : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.PhaseCoord.psiInf_phase | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.PhaseCoord.psiInf_phase | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.PhaseCoord.psiInf_phase <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Phase

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable {R S : Type} [CommRing R] [Algebra F R] [CommRing S] [Algebra F S]

theorem repr_tmap (f : R →ₐ[F] S) {ι : Type} (b : Module.Basis ι F E) (z : R ⊗[F] E) (k : ι) :
    (Algebra.TensorProduct.basis S b).repr (Algebra.TensorProduct.map f (AlgHom.id F E) z) k =
      f ((Algebra.TensorProduct.basis R b).repr z k) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e =>
    simp [Algebra.TensorProduct.basis_repr_tmul, Finsupp.mapRange_apply, Algebra.smul_def]
  | add x y hx hy => simp [map_add (f := _), hx, hy]

theorem trace_tmap [Module.Finite F E] (f : R →ₐ[F] S) (z : R ⊗[F] E) :
    f (Algebra.trace R (R ⊗[F] E) z) =
      Algebra.trace S (S ⊗[F] E) (Algebra.TensorProduct.map f (AlgHom.id F E) z) := by
  classical
  let b := Module.Free.chooseBasis F E
  rw [Algebra.trace_eq_matrix_trace (Algebra.TensorProduct.basis R b),
    Algebra.trace_eq_matrix_trace (Algebra.TensorProduct.basis S b)]

  simp only [Matrix.trace, Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← repr_tmap, map_mul]
  simp only [Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.map_tmul, map_one, AlgHom.coe_id, id_eq]

theorem tmap_sigR (f : R →ₐ[F] S) (σ : E →ₐ[F] E) (z : R ⊗[F] E) :
    Algebra.TensorProduct.map f (AlgHom.id F E) (sigR R σ z) =
      sigR S σ (Algebra.TensorProduct.map f (AlgHom.id F E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem tmap_inclR (f : R →ₐ[F] S) (e : E) :
    Algebra.TensorProduct.map f (AlgHom.id F E) (inclR R e) = inclR S e := by
  simp [inclR]

theorem tmap_gramR (f : R →ₐ[F] S) (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → R ⊗[F] E) :
    (gramR R σ J X).map (Algebra.TensorProduct.map f (AlgHom.id F E)) =
      gramR S σ J (fun a i => Algebra.TensorProduct.map f (AlgHom.id F E) (X a i)) := by
  ext a c

  simp only [Matrix.map_apply, gramR, hR, Formalism.UG.hform, JR, map_sum, map_mul, tmap_sigR, tmap_inclR]

theorem tmap_phase [Module.Finite F E] (f : R →ₐ[F] S) (σ : E →ₐ[F] E) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (B : Matrix (Fin n) (Fin n) (R ⊗[F] E))
    (X : Fin n → Fin M → R ⊗[F] E) :
    f (algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (Matrix.trace (B * gramR R σ J X))) =
      algebraMap F S (1 / 2) * Algebra.trace S (S ⊗[F] E)
        (Matrix.trace (B.map (Algebra.TensorProduct.map f (AlgHom.id F E)) *
          gramR S σ J (fun a i => Algebra.TensorProduct.map f (AlgHom.id F E) (X a i)))) := by
  rw [map_mul, AlgHom.commutes, trace_tmap, ← tmap_gramR]

  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul]

end Gen

theorem adelic_phase_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (ψ : AddChar (AF F) ℂ)
  (b : HermR (AF F) σ n) (X : Fin n → Fin M → AF F ⊗[F] E),
  ψ (algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
      (Matrix.trace ((b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * gramR (AF F) σ J X))) =
    psiInf F ψ (algebraMap F (Ainf F) (1 / 2) * Algebra.trace (Ainf F) (Ainf F ⊗[F] E)
      (Matrix.trace (((hermInf σ b : HermR (Ainf F) σ n) : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) *
        gramR (Ainf F) σ J (projInf X)))) *
    psiFin F ψ (algebraMap F (Af F) (1 / 2) * Algebra.trace (Af F) (Af F ⊗[F] E)
      (Matrix.trace (((hermFin σ b : HermR (Af F) σ n) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) *
        gramR (Af F) σ J (projFin X)))) := by
  intro F E _ _ _ _ _ σ _ M J n ψ b X
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have h1 := tmap_phase (fstA F) σ J (b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) X
  have h2 := tmap_phase (sndA F) σ J (b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) X
  have key : ∀ T : AF F, ψ T = psiInf F ψ (fstA F T) * psiFin F ψ (sndA F T) := by
    intro T
    simp only [psiInf, psiFin]
    rw [← AddChar.map_add_eq_mul]
    congr 1
    exact (Prod.fst_add_snd T).symm
  rw [key, h1, h2]
  rfl

end GlobalTheory.CompanionTheory.SiegelND.Integ.Phase
end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

noncomputable section
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PairAdd

theorem psiFin_add' (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (x y : Af F) :
    psiFin F ψ (x + y) = psiFin F ψ x * psiFin F ψ y := by
  have h : pairA F 0 (x + y) = pairA F 0 x + pairA F 0 y := by
    simp only [pairA]
    exact Prod.ext (add_zero 0).symm rfl
  simp only [psiFin]
  rw [h, AddChar.map_add_eq_mul]

theorem hR_add_left {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x x' y : Fin M → R ⊗[F] E) :
    hR R σ J (x + x') y = hR R σ J x y + hR R σ J x' y := by
  simp [hR, Formalism.UG.hform, Pi.add_apply, map_add (f := _), Matrix.mulVec_add, Matrix.add_mulVec, dotProduct_add,
    add_dotProduct, Finset.sum_add_distrib, add_mul, mul_add]

theorem hR_add_right {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y y' : Fin M → R ⊗[F] E) :
    hR R σ J x (y + y') = hR R σ J x y + hR R σ J x y' := by
  simp [hR, Formalism.UG.hform, Pi.add_apply, map_add (f := _), Matrix.mulVec_add, Matrix.add_mulVec, dotProduct_add,
    add_dotProduct, Finset.sum_add_distrib, add_mul, mul_add]

theorem pairB_add : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (ψ : AddChar (AF F) ℂ)
    (b : HermR (Af F) σ n),
    (∀ X X' Y : Fin n → Fin M → Af F ⊗[F] E, pairB σ J (psiFin F ψ) b (X + X') Y =
      pairB σ J (psiFin F ψ) b X Y * pairB σ J (psiFin F ψ) b X' Y) ∧
    (∀ X Y Y' : Fin n → Fin M → Af F ⊗[F] E, pairB σ J (psiFin F ψ) b X (Y + Y') =
      pairB σ J (psiFin F ψ) b X Y * pairB σ J (psiFin F ψ) b X Y') := by
  intro F E _ _ _ _ _ σ M J n ψ b
  have hg1 : ∀ X X' Y : Fin n → Fin M → Af F ⊗[F] E,
      gram2 σ J (X + X') Y = gram2 σ J X Y + gram2 σ J X' Y := by
    intro X X' Y
    ext a c
    simp only [gram2, Pi.add_apply, Matrix.add_apply]
    exact hR_add_left _ σ J _ _ _
  have hg2 : ∀ X Y Y' : Fin n → Fin M → Af F ⊗[F] E,
      gram2 σ J X (Y + Y') = gram2 σ J X Y + gram2 σ J X Y' := by
    intro X Y Y'
    ext a c
    simp only [gram2, Pi.add_apply, Matrix.add_apply]
    exact hR_add_right _ σ J _ _ _
  refine ⟨fun X X' Y => ?_, fun X Y Y' => ?_⟩
  · simp only [pairB, hg1, Matrix.mul_add, Matrix.trace_add, map_add (f := _), psiFin_add']
  · simp only [pairB, hg2, Matrix.mul_add, Matrix.trace_add, map_add (f := _), psiFin_add']

end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PairAdd
end
end

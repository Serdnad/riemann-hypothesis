module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle271
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FlatSpaceComponents
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.LocalRingCardinality.Bundle008
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
public import Formalism.LocalToGlobal.ClassRec
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
public import Formalism.LocalToGlobal.Divisibility.Bundle003
public import Formalism.LocalToGlobal.HilbertRowConditions.Bundle002
import Formalism.LocalToGlobal.HilbertRowConditions.IsHilbertCF
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle003
import Formalism.LocalToGlobal.SiegelLatticeTheory.PtEquivApply

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section
namespace GlobalTheory.SeeConjGroup

open Classical Formalism.L2.SG.HidaSetting

abbrev II (D : D7) : AutInst := Formalism.L2.SG.InstExistsPf.instOf D

section Red
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def redV (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (PP : Pl E) (v : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) : Fin n → kP PP :=
  fun i => if h : ((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _).mulVec v i ∈
      Formalism.L2.Herm.intAf F E then resS F PP ⟨_, h⟩ else 0

end Red

def basisOrRevDual {M : Type} {k : ℕ} (w : Bool) (b bd : Fin k → M) : Fin k → M := if w then b else fun i => bd (Fin.rev i)

def dualOrRevBasis {M : Type} {k : ℕ} (w : Bool) (b bd : Fin k → M) : Fin k → M := if w then bd else fun i => b (Fin.rev i)

def LocAt {D : D7} (g : ℕ) (e0 f0 : Fin D.R.rS → VA (II D)) (z0 : VA (II D)) (bw bwd : Fin D.R.k → VA (II D))
    (ew : EAf D) (β : GL (Fin (Yc D 0).rank) (EAf D)) (PP : Pl D.host.E) (w : Bool) : Prop :=
  ((g : 𝓞 D.host.E) ∈ PP.asIdeal) ∧
    (∀ h1 : ew ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, resS D.host.F PP ⟨ew, h1⟩ = if w then 1 else 0) ∧
    (∀ h1 : sigA (II D) ew ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
      resS D.host.F PP ⟨sigA (II D) ew, h1⟩ = if w then 0 else 1) ∧
    RedIs β PP (flagV D.R.rS D.R.k (Yc D 0).rank e0 f0 (basisOrRevDual w bw bwd) z0)

end GlobalTheory.SeeConjGroup
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjChar

open Classical GlobalTheory.SeeConjRead

variable {D : D7}

def resT (PP : Pl D.host.E) (x : EAf D) : kP PP :=
  if hx : x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E then Formalism.L2.DIV.resS D.host.F PP ⟨x, hx⟩ else 0

def hT (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (x y : Fin (Yc D 0).rank → EAf D) : EAf D :=
  cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) h)
    (Formalism.L2.SG.HidaSetting.hA X.B.I (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) h.symm) x)
      (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) h.symm) y))

def argT (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (M : GL (Fin (Yc D 0).rank) (EAf D)) : EAf D :=
  (∑ a, hT X h (f0T X h a) (Matrix.mulVec M.val (Formalism.L2.SG.HidaSetting.nxt (e0T X h) (z0T X h) a))) +
    ∑ i : Fin D.R.k, if hi : i.1 + 1 < D.R.k then
      hT X h (bwdT X h i) (Matrix.mulVec M.val (bwT X h ⟨i.1 + 1, hi⟩)) else 0

def sideAt (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (PP : Pl D.host.E) : Bool :=
  decide (GlobalTheory.StdFrames.cpt PP (ewT X h) = 1)

def wA (ρ k : ℕ) (s : Bool) {r : ℕ} (i _j : Fin r) : ℤ :=
  if i.1 < ρ then 1 else if i.1 + 1 < ρ + k then (if s then 1 else 0) else 0

def wB (ρ k : ℕ) (s : Bool) {r : ℕ} (i _j : Fin r) : ℤ :=
  if i.1 < ρ then 0 else if i.1 + 1 < ρ + k then (if s then 0 else -1) else if i.1 = ρ + k then 1 else -1

theorem conjPrime_asIdeal (PP : Pl D.host.E) :
    (GlobalTheory.IdemSupport.cP PP).asIdeal = PP.asIdeal.map (GlobalTheory.IdemSupport.cO D) := by
  ext x
  rw [GlobalTheory.IdemSupport.mem_cP, Ideal.mem_map_of_equiv]
  constructor
  · intro hx
    exact ⟨GlobalTheory.IdemSupport.cO D x, hx, GlobalTheory.IdemSupport.cO_cO x⟩
  · rintro ⟨y, hy, rfl⟩
    rw [GlobalTheory.IdemSupport.cO_cO]
    exact hy

def conjRes (PP : Pl D.host.E) : kP PP ≃+* kP (GlobalTheory.IdemSupport.cP PP) :=
  Ideal.quotientEquiv _ _ (GlobalTheory.IdemSupport.cO D) (conjPrime_asIdeal PP)

end GlobalTheory.SeeConjChar
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeConjRead

open Classical

variable {D : D7}

def colMat {n : ℕ} (w : Fin n → Fin n → EAf D) : Matrix (Fin n) (Fin n) (EAf D) := Matrix.of fun i j => w j i

def pairAt (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (PP : Pl D.host.E) :
    Fin (Yc D 0).rank → Fin (Yc D 0).rank → EAf D :=
  if GlobalTheory.StdFrames.cpt PP (ewT X h) = 1 then
    flagV D.R.rS D.R.k (Yc D 0).rank (f0T X h) (e0T X h) (bwdT X h) (z0T X h)
  else flagV D.R.rS D.R.k (Yc D 0).rank (f0T X h) (e0T X h) (fun i => bwT X h (Fin.rev i)) (z0T X h)

def hY (D : D7) (x y : Fin (Yc D 0).rank → EAf D) : EAf D :=
  Formalism.UG.hform (GlobalTheory.StdFrames.sg D) (GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.ratM (Yc D 0).gram) x y

def SmallAt (PP : Pl D.host.E) (x : EAf D) : Prop := Valued.v (GlobalTheory.StdFrames.cpt PP x) < 1

def PairTable {M A : Type} [Ring A] (p : M → M → A) (sm : A → Prop) {ρ k : ℕ} (e f : Fin ρ → M) (b b' : Fin k → M)
    (z : M) : Prop :=
  (∀ a c, sm (p (f a) (e c) - if a = c then 1 else 0)) ∧ (∀ a j, sm (p (f a) (b j))) ∧ (∀ a, sm (p (f a) z)) ∧
  (∀ a c, sm (p (f a) (f c))) ∧
  (∀ i a, sm (p (b' i) (e a))) ∧ (∀ i j, sm (p (b' i) (b j) - if i = j then 1 else 0)) ∧ (∀ i, sm (p (b' i) z)) ∧
  (∀ i a, sm (p (b' i) (f a))) ∧
  (∀ a, sm (p z (e a))) ∧ (∀ j, sm (p z (b j))) ∧ sm (p z z + 1) ∧ (∀ a, sm (p z (f a))) ∧
  (∀ a c, sm (p (e a) (e c))) ∧ (∀ a j, sm (p (e a) (b j))) ∧ (∀ a, sm (p (e a) z)) ∧
  (∀ a c, sm (p (e a) (f c) - if a = c then 1 else 0))

def sgnD {A : Type} [Ring A] (ρ k : ℕ) {n : ℕ} (a : Fin n) : A := if a.1 = ρ + k then -1 else 1

end GlobalTheory.SeeConjRead
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjScale


open Classical in
noncomputable def forestLift {G : Type} [Group G] {r : ℕ} (Ed : Fin r → Fin r → Prop) (hlt : ∀ i j, Ed i j → i < j)
    (w : Fin r → Fin r → G) (j : Fin r) : G :=
  if h : ∃ i, Ed i j then forestLift Ed hlt w (Classical.choose h) * w (Classical.choose h) j else 1
termination_by j.val
decreasing_by all_goals (try simp_wf); exact hlt _ _ (Classical.choose_spec h)

theorem forestLift_edge {G : Type} [Group G] {r : ℕ} (Ed : Fin r → Fin r → Prop) (hlt : ∀ i j, Ed i j → i < j)
    (huniq : ∀ i i' j, Ed i j → Ed i' j → i = i') (w : Fin r → Fin r → G) {i j : Fin r} (h : Ed i j) :
    (forestLift Ed hlt w i)⁻¹ * forestLift Ed hlt w j = w i j := by
  have hex : ∃ i, Ed i j := ⟨i, h⟩
  have hc : Classical.choose hex = i := huniq _ _ _ (Classical.choose_spec hex) h
  have e : forestLift Ed hlt w j = forestLift Ed hlt w i * w i j := by
    rw [forestLift, dite_eq_left hex, hc]
  rw [e, inv_mul_cancel_left]

theorem symEdge_lt {r : ℕ} (ρ k : ℕ) : ∀ i j : Fin r, symEdge ρ k i j → i < j := by
  intro i j h
  show i.val < j.val
  unfold symEdge at h
  omega

theorem symEdge_uniq {r : ℕ} (ρ k : ℕ) : ∀ i i' j : Fin r, symEdge ρ k i j → symEdge ρ k i' j → i = i' := by
  intro i i' j h h'
  apply Fin.ext
  unfold symEdge at h h'
  omega

theorem scale_conj : ∀ {κf : Type} [CommRing κf] [Finite κf], IsField κf → ∀ {r : ℕ} (ρ k : ℕ) (ψ' ψ0 : AddChar κf ℂ), ψ' ≠ 1 → ψ0 ≠ 1 → ∀ a : Fin r → Fin r → κfˣ, ∃ d : Fin r → κfˣ, ∀ u : GL (Fin r) κf, u ∈ unipSym κf r ρ k → ψ' (∑ i, ∑ j, if symEdge ρ k i j then (a i j : κf) * u.val i j else 0) = ψ0 (edgeSum (symEdge ρ k) ((diagGL d)⁻¹ * u * diagGL d)) := by
  intro κf _ _ hF r ρ k ψ' ψ0 h1 h0 a
  let _ : Field κf := hF.toField
  have := Fintype.ofFinite κf
  have hprim : ψ0.IsPrimitive := AddChar.IsPrimitive.of_ne_one h0
  have hinj : Function.Injective ψ0.mulShift := AddChar.to_mulShift_inj_of_isPrimitive hprim
  have hbij : Function.Bijective ψ0.mulShift := by
    classical
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hinj, (AddChar.card_eq).symm⟩
  obtain ⟨c, hc⟩ := hbij.2 ψ'
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply h1
    rw [← hc]
    exact AddChar.mulShift_zero ψ0
  let w : Fin r → Fin r → κfˣ := fun i j => Units.mk0 c hc0 * a i j
  refine ⟨forestLift (symEdge ρ k) (symEdge_lt ρ k) w, fun u _ => ?_⟩
  rw [← hc, AddChar.mulShift_apply]
  congr 1
  unfold edgeSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · rw [diagGL_conj_apply]
    have e := congrArg Units.val (forestLift_edge (symEdge ρ k) (symEdge_lt ρ k) (symEdge_uniq ρ k) w h)
    rw [Units.val_mul] at e
    have e2 : (((forestLift (symEdge ρ k) (symEdge_lt ρ k) w i)⁻¹ : κfˣ) : κf) *
        ((forestLift (symEdge ρ k) (symEdge_lt ρ k) w j : κfˣ) : κf) = c * (a i j : κf) := by
      rw [e]; rfl
    symm
    calc (((forestLift (symEdge ρ k) (symEdge_lt ρ k) w i)⁻¹ : κfˣ) : κf) * u.val i j *
          ((forestLift (symEdge ρ k) (symEdge_lt ρ k) w j : κfˣ) : κf)
        = ((((forestLift (symEdge ρ k) (symEdge_lt ρ k) w i)⁻¹ : κfˣ) : κf) *
          ((forestLift (symEdge ρ k) (symEdge_lt ρ k) w j : κfˣ) : κf)) * u.val i j := by ring
      _ = c * ((a i j : κf) * u.val i j) := by rw [e2]; ring
  · rw [mul_zero]

end GlobalTheory.SeeConjScale
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.FrameRescale

open Matrix

variable {D : D7}

local notation "𝒪" => Formalism.L2.Herm.intAf D.host.F D.host.E


theorem exists_unit_res (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)) (d : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ) :
    ∃ u : (𝒪)ˣ, ∀ PP ∈ Pg, Formalism.L2.DIV.resS D.host.F PP (u : 𝒪) = d PP := by
  classical
  choose a ha using fun PP : Formalism.L2.DIV.Pl D.host.E =>
    Ideal.Quotient.mk_surjective (I := PP.asIdeal) ((d PP : Formalism.L2.DIV.kP PP))
  have hv : ∀ PP : Formalism.L2.DIV.Pl D.host.E,
      Valued.v (algebraMap D.host.E (PP.adicCompletion D.host.E) ((a PP : 𝓞 D.host.E) : D.host.E)) = 1 := by
    intro PP
    rw [Formalism.UG.P.levelaf_valued_algebraMap]
    refine le_antisymm (HeightOneSpectrum.valuation_le_one _ _) (not_lt.1 fun h => ?_)
    have hm := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := D.host.E) PP (a PP)).1 h
    have h0 : (Ideal.Quotient.mk PP.asIdeal (a PP)) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hm
    rw [ha PP] at h0
    exact (d PP).ne_zero h0
  let t : ∀ Q : Formalism.L2.DIV.Pl D.host.E, Q.adicCompletion D.host.E := fun Q =>
    if Q ∈ Pg then algebraMap D.host.E (Q.adicCompletion D.host.E) ((a Q : 𝓞 D.host.E) : D.host.E) else 1
  have ht : ∀ Q, Valued.v (t Q) = 1 := fun Q => by
    simp only [t]; split_ifs
    · exact hv Q
    · exact Valuation.map_one _
  obtain ⟨z, hz, hzc⟩ := GlobalTheory.AdIsom.exists_of_cpt (D := D) t (fun Q => (ht Q).le)
  obtain ⟨z', hz', hzc'⟩ := GlobalTheory.AdIsom.exists_of_cpt (D := D) (fun Q => (t Q)⁻¹)
    (fun Q => by rw [map_inv₀, ht Q, inv_one])
  have htn : ∀ Q, t Q ≠ 0 := fun Q h => by simpa [h] using ht Q
  have hzz : z * z' = 1 := GlobalTheory.StdFrames.cpt_ext fun Q => by
    rw [map_mul, hzc, hzc', map_one, mul_inv_cancel₀ (htn Q)]
  have hzz' : (⟨z, hz⟩ : 𝒪) * ⟨z', hz'⟩ = 1 := Subtype.ext hzz
  refine ⟨⟨⟨z, hz⟩, ⟨z', hz'⟩, hzz', by rw [mul_comm]; exact hzz'⟩, fun PP hPP => ?_⟩
  have hc : ((Formalism.L2.DIV.oToS D.host.F D.host.E (a PP) : 𝒪) : EAf D) =
      GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.inc D ((a PP : 𝓞 D.host.E) : D.host.E) := rfl
  have h2 : Valued.v (GlobalTheory.StdFrames.cpt PP
      (((⟨z, hz⟩ : 𝒪) - Formalism.L2.DIV.oToS D.host.F D.host.E (a PP) : 𝒪) : EAf D)) < 1 := by
    rw [AddSubgroupClass.coe_sub, hc, map_sub, GlobalTheory.AdIsom.cpt_inc, hzc]
    simp only [t, ite_eq_left hPP, sub_self, map_zero]
    exact zero_lt_one
  have h1 : Formalism.L2.DIV.resS D.host.F PP ((⟨z, hz⟩ : 𝒪) - Formalism.L2.DIV.oToS D.host.F D.host.E (a PP)) = 0 :=
    (GlobalTheory.AdIsom.resS_eq_zero_iff_cpt (D := D) PP ((⟨z, hz⟩ : 𝒪) - Formalism.L2.DIV.oToS D.host.F D.host.E (a PP))).2 h2
  have h3 : Formalism.L2.DIV.resS D.host.F PP (⟨z, hz⟩ : 𝒪) = d PP := by
    have h4 : Formalism.L2.DIV.resS D.host.F PP (Formalism.L2.DIV.oToS D.host.F D.host.E (a PP)) =
        Ideal.Quotient.mk PP.asIdeal (a PP) := Formalism.L2.DIV.resS_oToS (F := D.host.F) PP (a PP)
    have h5 := (RingHom.map_sub (Formalism.L2.DIV.resS D.host.F PP) (⟨z, hz⟩ : 𝒪) (Formalism.L2.DIV.oToS D.host.F D.host.E (a PP))).symm.trans h1
    exact (sub_eq_zero.1 h5).trans (h4.trans (ha PP))
  exact h3

theorem upperLeftBlock_diagonal_conj_eq {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) (dn : Fin n → κˣ) (d : Fin r → κˣ)
    (hd : ∀ i : Fin r, dn (Fin.castLE hr i) = d i) (X : GL (Fin n) κ) :
    Formalism.L2.DIV.upperLeftBlock hr ((diagGL dn)⁻¹ * X * diagGL dn) = (diagGL d)⁻¹ * Formalism.L2.DIV.upperLeftBlock hr X * diagGL d := by
  have key : ∀ (e : Fin n → κˣ) (Y : GL (Fin n) κ), Y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) →
      (diagGL e)⁻¹ * Y * diagGL e ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) := by
    intro e Y hY i j hij
    rw [diagGL_conj_apply, hY hij, mul_zero, zero_mul]
  by_cases hX : X ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r)
  · apply Units.ext
    rw [Formalism.L2.DIV.upper_block_val_submatrix hr (key dn X hX)]
    ext i j
    rw [Matrix.submatrix_apply, diagGL_conj_apply, diagGL_conj_apply, Formalism.L2.DIV.upper_block_val_submatrix hr hX,
      Matrix.submatrix_apply, hd, hd]
  · have hY : (diagGL dn)⁻¹ * X * diagGL dn ∉ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) := by
      intro h
      apply hX
      have := key (fun i => (dn i)⁻¹) _ h
      rwa [← diagGL_inv, inv_inv, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, mul_assoc,
        mul_inv_cancel, mul_one] at this
    unfold Formalism.L2.DIV.upperLeftBlock Formalism.L2.DIV.ext1
    rw [dite_eq_right hX, dite_eq_right hY, mul_one, inv_mul_cancel]

theorem intGL_diagGL_val {n : ℕ} (u : Fin n → (𝒪)ˣ) :
    (Formalism.L2.DIV.intGL D.host.F D.host.E n (diagGL u)).val =
      Matrix.diagonal fun i => ((u i : 𝒪) : EAf D) := by
  ext i j
  show (((diagGL u : GL (Fin n) 𝒪) : Matrix (Fin n) (Fin n) 𝒪) i j : EAf D) = _
  rw [diagGL_val, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> rfl

theorem frGL_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F))) (δ y : GL (Fin n) (Formalism.L2.Herm.intAf F E)) :
    Formalism.L2.DIV.frGL (β * Formalism.L2.DIV.intGL F E n δ) y = Formalism.L2.DIV.frGL β (δ * y * δ⁻¹) := by
  have h1 : Formalism.L2.DIV.intGL F E n (δ * y * δ⁻¹) =
      Formalism.L2.DIV.intGL F E n δ * Formalism.L2.DIV.intGL F E n y * (Formalism.L2.DIV.intGL F E n δ)⁻¹ := by
    rw [MonoidHom.map_mul, MonoidHom.map_mul, MonoidHom.map_inv]
  show β * Formalism.L2.DIV.intGL F E n δ * Formalism.L2.DIV.intGL F E n y * (β * Formalism.L2.DIV.intGL F E n δ)⁻¹ =
    β * Formalism.L2.DIV.intGL F E n (δ * y * δ⁻¹) * β⁻¹
  rw [h1]
  group

theorem bc_conj {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {n : ℕ} (δ y : GL (Fin n) A) :
    Formalism.UG.bc φ (δ⁻¹ * y * δ) = (Formalism.UG.bc φ δ)⁻¹ * Formalism.UG.bc φ y * Formalism.UG.bc φ δ := by
  rw [MonoidHom.map_mul, MonoidHom.map_mul, MonoidHom.map_inv]



theorem exists_rescale : ∀ {D : D7} {n r : ℕ} (hr : r ≤ n) (β : GL (Fin n) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), IsFrame β Λ → ∀ (Pg : Finset (Pl D.host.E)) (d : ∀ PP : Pl D.host.E, Fin r → (kP PP)ˣ), ∃ β' : GL (Fin n) (EAf D), IsFrame β' Λ ∧ (∀ M, M ∈ St β' ↔ M ∈ St β) ∧ ∀ PP ∈ Pg, ∀ M ∈ St β, upperLeftBlock hr (redFn β' PP M) = (diagGL (d PP))⁻¹ * upperLeftBlock hr (redFn β PP M) * diagGL (d PP) := by
  intro D n r hr β Λ hβ Pg d
  classical
  let dn : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Fin n → (Formalism.L2.DIV.kP PP)ˣ :=
    fun PP j => if h : j.val < r then d PP ⟨j.val, h⟩ else 1
  choose u hu using fun j : Fin n => exists_unit_res (D := D) Pg (fun PP => dn PP j)
  refine ⟨β * Formalism.L2.DIV.intGL D.host.F D.host.E n (diagGL u), ?_, ?_, ?_⟩
  · intro x
    rw [hβ x]
    have hinv : ((β * Formalism.L2.DIV.intGL D.host.F D.host.E n (diagGL u))⁻¹).val = Matrix.diagonal (fun i => ((((u i)⁻¹ : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ) : (Formalism.L2.Herm.intAf D.host.F D.host.E)) : EAf D)) *
          (β⁻¹).val := by
      rw [_root_.mul_inv_rev, Units.val_mul, ← map_inv, diagGL_inv, intGL_diagGL_val]
    rw [hinv]
    refine forall_congr' fun i => ?_
    rw [← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]
    have hm : ((u i : (Formalism.L2.Herm.intAf D.host.F D.host.E)) : EAf D) * ((((u i)⁻¹ : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ) : (Formalism.L2.Herm.intAf D.host.F D.host.E)) : EAf D) = 1 := congrArg Subtype.val (u i).mul_inv
    constructor
    · intro h
      exact Subring.mul_mem _ ((u i)⁻¹ : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ).val.2 h
    · intro h
      have h2 := Subring.mul_mem _ (u i).val.2 h
      rwa [← mul_assoc, hm, one_mul] at h2
  · intro M
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨diagGL u * y * (diagGL u)⁻¹, (frGL_mul β (diagGL u) y).symm⟩
    · rintro ⟨y, rfl⟩
      refine ⟨(diagGL u)⁻¹ * y * diagGL u, ?_⟩
      rw [frGL_mul]
      congr 1
      group
  · intro PP hPP M hM
    obtain ⟨y, rfl⟩ := hM
    have e1 : Formalism.L2.DIV.frGL β y =
        Formalism.L2.DIV.frGL (β * Formalism.L2.DIV.intGL D.host.F D.host.E n (diagGL u)) ((diagGL u)⁻¹ * y * diagGL u) := by
      rw [frGL_mul]
      congr 1
      group
    have hred : Formalism.UG.bc (Formalism.L2.DIV.resS D.host.F PP) (diagGL u) = diagGL (dn PP) := by
      apply Units.ext
      ext i j
      show Formalism.L2.DIV.resS D.host.F PP (((diagGL u : GL (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E)) : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E)) i j) =
        ((diagGL (dn PP) : GL (Fin n) (Formalism.L2.DIV.kP PP)) : Matrix (Fin n) (Fin n) (Formalism.L2.DIV.kP PP)) i j
      rw [diagGL_val, diagGL_val, Matrix.diagonal_apply, Matrix.diagonal_apply]
      split_ifs with h
      · subst h
        exact hu i PP hPP
      · exact map_zero _
    have e2 : Formalism.L2.DIV.redFn (β * Formalism.L2.DIV.intGL D.host.F D.host.E n (diagGL u)) PP (Formalism.L2.DIV.frGL β y) =
        (diagGL (dn PP))⁻¹ * Formalism.L2.DIV.redFn β PP (Formalism.L2.DIV.frGL β y) * diagGL (dn PP) := by
      have e3 := Formalism.L2.DIV.redFn_frGL (β * Formalism.L2.DIV.intGL D.host.F D.host.E n (diagGL u)) PP ((diagGL u)⁻¹ * y * diagGL u)
      have e4 := Formalism.L2.DIV.redFn_frGL β PP y
      rw [← e1] at e3
      rw [e3, e4, bc_conj, hred]
    refine (congrArg (Formalism.L2.DIV.upperLeftBlock hr) e2).trans (upperLeftBlock_diagonal_conj_eq hr (dn PP) (d PP) (fun i => ?_) _)
    show (if h : (Fin.castLE hr i).val < r then d PP ⟨(Fin.castLE hr i).val, h⟩ else 1) = d PP i
    rw [dite_eq_left (show (Fin.castLE hr i).val < r from i.2)]
    rfl

end GlobalTheory.FrameRescale
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open Formalism.L2.Rows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ClassSumLift

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}
  {Rc : Formalism.L2.RecT ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem theta_cast (j : ℕ) (μ ν : D.what₂.Tup) (h : μ = ν) (x : D.what₂.MtL μ j) :
    D.what₂.thetaP ν j (D.what₂.jMt ν j (h ▸ x)) = D.what₂.thetaP μ j (D.what₂.jMt μ j x) := by
  subst h; rfl

theorem exists_heq_fin {K : Type} {a b : ℕ} (h : a = b) (z : Fin a → K) : ∃ y : Fin b → K, HEq z y := by
  subst h; exact ⟨z, HEq.rfl⟩

theorem exists_cast (j : ℕ) (μ ν : D.what₂.Tup) (h : μ = ν) (x : D.what₂.MtL ν j) :
    ∃ x' : D.what₂.MtL μ j, x = h ▸ x' := by
  subst h; exact ⟨x, rfl⟩


end GlobalTheory.ClassSumLift

end
end

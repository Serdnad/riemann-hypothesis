module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFrameReorderingLevelData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Formalism.LocalToGlobal.Columns.DecoFin
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle261
public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle160
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle262
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle253
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle265
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle271
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle170
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjRead

theorem mem_levS_dat0_PsharpSym_iff : ∀ {D : D7} {T : Type} (Lc : LevCh D T) (β : GL (Fin (Yc D 0).rank) (EAf D)) (ψ0 : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (κ : GA D (Yc D 0)), (κ ∈ levS (Yc D 0) β (Lc.dat0 (PsharpSym Lc.Pg D.R.r D.R.rS D.R.k ψ0)) ↔ κ ∈ GfC (Yc D 0) ∧ finE (Yc D 0) κ ∈ UA D.sp.cm (Yc D 0).gram ∧ finE (Yc D 0) κ ∈ St β ∧ ∀ PP ∈ Lc.Pg, upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ)) ∈ unipSym (kP PP) D.R.r D.R.rS D.R.k) ∧ (κ ∈ levS (Yc D 0) β (Lc.dat0 (PsharpSym Lc.Pg D.R.r D.R.rS D.R.k ψ0)) → levChi (Yc D 0) β (Lc.dat0 (PsharpSym Lc.Pg D.R.r D.R.rS D.R.k ψ0)) κ = ∏ PP ∈ Lc.Pg, ψ0 PP (edgeSum (symEdge D.R.rS D.R.k) (upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ))))) := by
  intro D T Lc β ψ0 κ
  have hH : ∀ g : G0 Lc.Pg D.R.r, g ∈ (PsharpSym Lc.Pg D.R.r D.R.rS D.R.k ψ0).H ↔
      ∀ PP : ↥Lc.Pg, g PP ∈ unipSym (kP PP.1) D.R.r D.R.rS D.R.k := by
    intro g
    show g ∈ Subgroup.pi Set.univ _ ↔ _
    rw [Subgroup.mem_pi]
    simp
  refine ⟨?_, fun hκ => ?_⟩
  · rw [GlobalTheory.SeeConjReord.mem_levelSubgroup_principalDatum_iff, hH]
    simp only [GlobalTheory.SeeConjReord.r0]
    constructor
    · rintro ⟨⟨h0, h1, h2⟩, h3⟩
      exact ⟨h0, h1, h2, fun PP hPP => h3 ⟨PP, hPP⟩⟩
    · rintro ⟨h0, h1, h2, h3⟩
      exact ⟨⟨h0, h1, h2⟩, fun PP => h3 PP.1 PP.2⟩
  · have hm := ((GlobalTheory.SeeConjReord.mem_levelSubgroup_principalDatum_iff Lc _ β κ).1 hκ).2
    rw [GlobalTheory.SeeConjReord.principalRowLevelCharacter_trivial, extendOne_of_mem _ hm]
    letI : IsOneApply ((PsharpSym Lc.Pg D.R.r D.R.rS D.R.k ψ0).H →* ℂˣ) := ⟨fun _ => rfl⟩
    letI : IsMulApply ((PsharpSym Lc.Pg D.R.r D.R.rS D.R.k ψ0).H →* ℂˣ) := ⟨fun _ _ _ => rfl⟩
    erw [prod_apply, Units.coe_prod]
    rw [← Finset.prod_coe_sort Lc.Pg]
    rfl

end GlobalTheory.SeeConjRead
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom

namespace GlobalTheory.TransportUnique

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {A : Type} [CommRing A]

theorem exists_inv {m n : ℕ} {x : Matrix (Fin m) (Fin n) A}
    (h : Function.Bijective (x.mulVec : (Fin n → A) → (Fin m → A))) :
    ∃ y : Matrix (Fin n) (Fin m) A, y * x = 1 ∧ x * y = 1 := by
  let e : (Fin n → A) ≃ₗ[A] (Fin m → A) := LinearEquiv.ofBijective (Matrix.toLin' x) h
  have hx : x = LinearMap.toMatrix' e.toLinearMap := (LinearMap.toMatrix'_toLin' x).symm
  refine ⟨LinearMap.toMatrix' e.symm.toLinearMap, ?_, ?_⟩
  · rw [hx, ← LinearMap.toMatrix'_comp]
    simp
  · rw [hx, ← LinearMap.toMatrix'_comp]
    simp

theorem hform_mulVec (σ : A →+* A) {n : ℕ} (J k : Matrix (Fin n) (Fin n) A) (a b : Fin n → A) :
    Formalism.UG.hform σ J (k *ᵥ a) (k *ᵥ b) = Formalism.UG.hform σ (Formalism.UG.cT σ k * J * k) a b := by
  have e2 : ∀ (J : Matrix (Fin n) (Fin n) A) a b, Formalism.UG.hform σ J a b = (σ ∘ a) ⬝ᵥ J *ᵥ b := by
    intro J a b
    simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, Function.comp_apply, mul_assoc]
  have e3 : σ ∘ (k *ᵥ a) = (σ ∘ a) ᵥ* Formalism.UG.cT σ k := by
    funext i
    rw [Formalism.UG.cT, vecMul_transpose, Function.comp_apply, RingHom.map_mulVec]
  rw [e2, e2, e3, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]

theorem unitary_iff (σ : A →+* A) {n : ℕ} (J k : Matrix (Fin n) (Fin n) A) :
    Formalism.UG.cT σ k * J * k = J ↔ ∀ a b, Formalism.UG.hform σ J (k *ᵥ a) (k *ᵥ b) = Formalism.UG.hform σ J a b := by
  refine ⟨fun h a b => by rw [hform_mulVec, h], fun h => ?_⟩
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  rw [hform_mulVec] at this
  simpa [Formalism.UG.hform, Pi.single_apply, apply_ite σ] using this

theorem smul_eq_of_fix {m n : ℕ} {e : A} (β : GL (Fin m) A) {B : Matrix (Fin m) (Fin n) A}
    {k : Matrix (Fin m) (Fin m) A} (h : ∀ j, ∃ c, e • (β.val *ᵥ Pi.single j 1) = B *ᵥ c) (hk : k * B = B) :
    e • k = e • (1 : Matrix (Fin m) (Fin m) A) := by
  have h1 : k * (e • β.val) = e • β.val := by
    ext i j
    obtain ⟨c, hc⟩ := h j
    have : k *ᵥ (e • (β.val *ᵥ Pi.single j 1)) = e • (β.val *ᵥ Pi.single j 1) := by
      rw [hc, mulVec_mulVec, hk]
    have := congrFun this i
    simpa [Matrix.mul_apply, mulVec, dotProduct, Pi.single_apply] using this
  have h2 := congrArg (· * (β⁻¹).val) h1
  simpa only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] using h2

theorem fix_of_smul_eq {m n : ℕ} {e : A} {B : Matrix (Fin m) (Fin n) A} {k : Matrix (Fin m) (Fin m) A}
    (h : e • k = e • (1 : Matrix (Fin m) (Fin m) A)) (hB : e • B = B) : k * B = B := by
  rw [← hB, Matrix.mul_smul, ← Matrix.smul_mul, h, Matrix.smul_mul, Matrix.one_mul]

theorem conj_smul_eq (σ : A →+* A) (hσ : ∀ a, σ (σ a) = a) {n : ℕ} {J k : Matrix (Fin n) (Fin n) A} (hJ : IsUnit J)
    (hk : Formalism.UG.cT σ k * J * k = J) {e : A} (he : e • k = e • (1 : Matrix (Fin n) (Fin n) A)) :
    σ e • k = σ e • (1 : Matrix (Fin n) (Fin n) A) := by
  have h1 : (e • Formalism.UG.cT σ k) * J = (e • (1 : Matrix (Fin n) (Fin n) A)) * J := by
    calc (e • Formalism.UG.cT σ k) * J = Formalism.UG.cT σ k * J * (e • (1 : Matrix (Fin n) (Fin n) A)) := by
          rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
      _ = _ := by rw [← he, Matrix.mul_smul, hk, he, Matrix.smul_mul, Matrix.one_mul]
  have h2 := hJ.mul_right_cancel h1
  ext i j
  have := congrArg σ (congrFun (congrFun h2 j) i)
  simpa [Formalism.UG.cT, hσ, Matrix.one_apply, apply_ite σ, eq_comm] using this

theorem bc_eq_one_iff {B : Type} [CommRing B] (φ : A →+* B) {n : ℕ} (k : GL (Fin n) A) :
    Formalism.UG.bc φ k = 1 ↔ ∀ i j, φ (k.val i j - (1 : Matrix (Fin n) (Fin n) A) i j) = 0 := by
  rw [Units.ext_iff, ← Matrix.ext_iff]
  refine forall₂_congr fun i j => ?_
  rw [RingHom.map_sub, sub_eq_zero]
  simp [Formalism.UG.bc, Matrix.one_apply, apply_ite φ]

end Gen

variable {D : D7}

theorem idem_smul_iff (w : Pl D.host.E) {n : ℕ} (k l : Matrix (Fin n) (Fin n) (EAf D)) :
    idem w • k = idem w • l ↔ ∀ i j, GlobalTheory.StdFrames.cpt w (k i j - l i j) = 0 := by
  rw [← Matrix.ext_iff]
  refine forall₂_congr fun i j => ?_
  rw [RingHom.map_sub, sub_eq_zero, ← idem_mul_eq_iff]
  rfl

theorem bc_prV_eq_one_iff (w : Pl D.host.E) {n : ℕ} (k : GL (Fin n) (EAf D)) :
    Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) (w.under (𝓞 D.host.F))) k = 1 ↔
      idem w • k.val = idem w • (1 : Matrix (Fin n) (Fin n) (EAf D)) ∧
      idem (GlobalTheory.IdemSupport.cP w) • k.val = idem (GlobalTheory.IdemSupport.cP w) • (1 : Matrix (Fin n) (Fin n) (EAf D)) := by
  rw [idem_smul_iff, idem_smul_iff]
  refine (bc_eq_one_iff _ k).trans ?_
  have h := fun z => GlobalTheory.AdeleBaseChange.prV_eq_zero_iff (GlobalTheory.StdFrames.toAd_spec D) (w.under (𝓞 D.host.F)) z
  constructor
  · intro H
    exact ⟨fun i j => (h _).1 (H i j) w rfl, fun i j => (h _).1 (H i j) _ (GlobalTheory.IdemSupport.under_cP w)⟩
  · rintro ⟨H1, H2⟩ i j
    refine (h _).2 fun P hP => ?_
    rcases GlobalTheory.IdemSupport.eq_or_eq_cP hP with rfl | rfl
    · exact H1 i j
    · exact H2 i j

theorem mem_level_iff (W : HSp D) (L : Lat W) (k : GL (Fin W.rank) (EAf D)) :
    k ∈ Formalism.UG.levelAfL D.sp.cm.sig W.gram L ↔
      Formalism.UG.cT (cjA D) k.val * W.gram.map (inc D) * k.val = W.gram.map (inc D) ∧
        ∀ a, a ∈ hat L ↔ k.val *ᵥ a ∈ hat L := Iff.rfl

theorem col_mem_gen {A : Type} [CommRing A] (S : Subring A) {n : ℕ} (β : GL (Fin n) A) (j i : Fin n) :
    ((β⁻¹).val *ᵥ (β.val *ᵥ Pi.single j 1)) i ∈ S := by
  rw [mulVec_mulVec, Units.inv_mul, one_mulVec, Pi.single_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem idem_smul_eq_of_fix {W : HSp D} {L : Lat W} (hL : Submodule.IsFullLattice D.host.E L) {w : Pl D.host.E} {n : ℕ}
    {B : Matrix (Fin W.rank) (Fin n) (EAf D)} (hB : IsBasisAt W w L B) {k : Matrix (Fin W.rank) (Fin W.rank) (EAf D)}
    (h1 : HMul.hMul k B = B) : idem w • k = idem w • (1 : Matrix (Fin W.rank) (Fin W.rank) (EAf D)) := by
  obtain ⟨-, e, he, -, hc⟩ := hB
  obtain rfl := eq_idem he
  obtain ⟨β, rfl⟩ := GlobalTheory.AdIsom.exists_eq_lat (D := D) (Λ := L) hL
  refine smul_eq_of_fix β (fun j => ?_) h1
  have h := (mem_hat_lat β _).2 (col_mem_gen (OA D) β j)
  obtain ⟨c, hc'⟩ := (hc _).1 ⟨smul_mem_hat (idem_mem w) h, by rw [smul_smul, idem_mul_self]⟩
  exact ⟨_, hc'⟩

theorem transport_unique : ∀ (D : D7) (W Y : HSp D) (L : Lat W) (Λ : Lat Y) (S : Finset (Pl D.host.E)), IsSplitSet S → ∀ (n : ℕ) (be : Pl D.host.E → Matrix (Fin W.rank) (Fin n) (EAf D)) (be' : Pl D.host.E → Matrix (Fin Y.rank) (Fin n) (EAf D)), Submodule.IsFullLattice D.host.E L → (∀ w ∈ S, IsBasisAt W w L (be w)) → ∀ x, IsTransport W Y L Λ S be be' x → ∀ x', IsTransport W Y L Λ S be be' x' ↔ ∃ k, InStabAway W L S k ∧ x' = HMul.hMul x (k.1 : Matrix (Fin W.rank) (Fin W.rank) (EAf D)) := by
  intro D W Y L Λ S _ n be be' hL hbe x hx x'
  obtain ⟨⟨hb, hf⟩, hl, hs⟩ := hx
  constructor
  · rintro ⟨⟨hb', hf'⟩, hl', hs'⟩
    obtain ⟨y, y1, y2⟩ := exists_inv hb
    obtain ⟨y', y1', y2'⟩ := exists_inv hb'
    let k : GL (Fin W.rank) (EAf D) := ⟨HMul.hMul y x', HMul.hMul y' x,
      by rw [Matrix.mul_assoc, ← Matrix.mul_assoc x', y2', Matrix.one_mul, y1],
      by rw [Matrix.mul_assoc, ← Matrix.mul_assoc x, y2, Matrix.one_mul, y1']⟩
    have hk : HMul.hMul x k.val = x' := by
      change HMul.hMul x (HMul.hMul y x') = x'
      rw [← Matrix.mul_assoc, y2, Matrix.one_mul]
    have hkv : ∀ a, x *ᵥ (k.val *ᵥ a) = x' *ᵥ a := fun a => by rw [mulVec_mulVec, hk]
    have hU : Formalism.UG.cT (cjA D) k.val * W.gram.map (inc D) * k.val = W.gram.map (inc D) :=
      (unitary_iff _ _ _).2 fun a b => by
        rw [← hA_eq, ← hA_eq, ← hf, hkv, hkv, hf']
    refine ⟨k, ⟨(mem_level_iff W L k).2 ⟨hU, fun a => ?_⟩, fun w hw => ?_⟩, hk.symm⟩
    · rw [hl (k.val *ᵥ a), hkv, hl']
    · have h1 : HMul.hMul k.val (be w) = be w := by
        change HMul.hMul (HMul.hMul y x') (be w) = be w
        rw [Matrix.mul_assoc, hs' w hw, ← hs w hw, ← Matrix.mul_assoc, y1, Matrix.one_mul]
      have h2 : idem w • k.val = idem w • (1 : Matrix (Fin W.rank) (Fin W.rank) (EAf D)) :=
        idem_smul_eq_of_fix hL (hbe w hw) h1
      refine (bc_prV_eq_one_iff w k).2 ⟨h2, ?_⟩
      rw [← cjA_idem]
      exact conj_smul_eq (cjA D) cjA_cjA (GlobalTheory.StdFrames.isUnit_gram W) hU h2
  · rintro ⟨k, ⟨hk, hk1⟩, rfl⟩
    obtain ⟨hU, hst⟩ := (mem_level_iff W L k).1 hk
    refine ⟨⟨?_, fun a b => ?_⟩, fun a => ?_, fun w hw => ?_⟩
    · have : (HMul.hMul x k.val : Matrix (Fin Y.rank) (Fin W.rank) (EAf D)).mulVec = x.mulVec ∘ k.val.mulVec := funext fun a => (mulVec_mulVec _ _ _).symm
      rw [this]
      refine hb.comp (Function.bijective_iff_has_inverse.2 ⟨(k⁻¹).val.mulVec, fun a => ?_, fun a => ?_⟩)
      · rw [mulVec_mulVec, Units.inv_mul, one_mulVec]
      · rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
    · rw [← mulVec_mulVec, ← mulVec_mulVec, hf, hA_eq, hA_eq]
      exact (unitary_iff _ _ _).1 hU b a
    · rw [← mulVec_mulVec, ← hl, ← hst]
    · obtain ⟨-, e, he, hB, -⟩ := hbe w hw
      obtain rfl := eq_idem he
      have h2 := ((bc_prV_eq_one_iff w k).1 (hk1 w hw)).1
      have h3 : HMul.hMul k.val (be w) = be w := fix_of_smul_eq h2 hB
      rw [Matrix.mul_assoc, h3, hs w hw]

end GlobalTheory.TransportUnique

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdIsom.GlueBase

open GlobalTheory.IdemSupport (cP)

section Alg

variable {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]

theorem split_prime {e a t t' : A} (ht : t' * t = 1) {y f : M} (hy : e • y = y) :
    y = e • (y - a • f) + (a * (e * t')) • (t • f) := by
  have key : a * (e * t') * t = e * a := by linear_combination (a * e) * ht
  rw [smul_sub, hy, smul_smul, smul_smul, key, sub_add_cancel]

theorem mem_of_mul_sub (S : Subring A) {b h t : A} (hb : b ∈ S) (h1 : b * h ∈ S) (h2 : h - t ∈ S) : b * t ∈ S := by
  have hd := S.sub_mem h1 (S.mul_mem hb h2)
  rwa [mul_sub, sub_sub_cancel] at hd

theorem mem_of_sub (S : Subring A) {a b : A} (ha : a ∈ S) (h : a - b ∈ S) : b ∈ S := by
  have hd := S.sub_mem ha h
  rwa [sub_sub_cancel] at hd

theorem idem_smul_smul {e : A} (he : e * e = e) (x : M) : e • e • x = e • x := by
  rw [smul_smul, he]

end Alg

variable {D : D7}

theorem inc_inv_mul (u : D.what₂.Word) : inc D (Tu D u)⁻¹ * inc D (Tu D u) = 1 := by
  rw [← map_mul, inv_mul_cancel₀ (Tu_ne_zero u), map_one]

theorem cjA_inc_inv (u : D.what₂.Word) : cjA D (inc D (Tu D u)⁻¹) = inc D (Tu D u)⁻¹ := by
  rw [cjA_inc]
  congr 1
  simp [Tu, star_inv₀]

theorem hA_idem {X : HSp D} {e : EAf D} {y : Fin X.rank → EAf D} (hy : cjA D e • y = y) (x : Fin X.rank → EAf D) :
    hA X x y = hA X (e • x) y := by
  conv_lhs => rw [← hy]
  rw [hA_smul_right, hA_smul_left, cjA_cjA]

theorem isBasePair_of_isGlueVec (D : D7) (u : D.what₂.Word) (π : 𝓞 D.host.E) (hπ : IsPi u π) (X : HSp D) (L₀ : Lat X)
    (f : Fin X.rank → EAf D) (hL : Submodule.IsFullLattice D.host.E L₀) (hf : IsGlueVec X u L₀ f) :
    IsBasePair X u π L₀ fun w => idem w • f := by
  have ht : inc D (Tu D u)⁻¹ * inc D (Tu D u) = 1 := inc_inv_mul u
  have := hL
  unfold IsBasePair
  refine ⟨by infer_instance, fun w e he hT y => ?_, fun w e he hπw => ?_⟩
  ·
    obtain rfl := eq_idem he
    have hinv : idem w * inc D (Tu D u)⁻¹ ∈ OA D := (idem_mul_inv_mem_iff u w).2 hT
    simp only [InCmp]
    constructor
    · rintro ⟨hy, hey⟩
      exact ⟨(mem_hat_dualL_iff hL y).2 fun x hx => hf.int x hx y hy, hey⟩
    · rintro ⟨hy, hey⟩
      obtain ⟨a, ha, hya⟩ := hf.dual y ((mem_hat_dualL_iff hL y).1 hy)
      refine ⟨?_, hey⟩
      rw [split_prime (a := a) (f := f) ht hey]
      exact add_mem_hat (smul_mem_hat (idem_mem w) hya) (smul_mem_hat ((OA D).mul_mem ha hinv) hf.mul_mem)
  ·
    obtain rfl := eq_idem he
    have hTw : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := by
      rw [← pi_mul_cO hπ]
      exact w.asIdeal.mul_mem_right _ hπw
    have hnot : idem w * inc D (Tu D u)⁻¹ ∉ OA D := fun h => (idem_mul_inv_mem_iff u w).1 h hTw
    have hff : hA X f f - inc D (Tu D u)⁻¹ ∈ OA D := hf.norm
    refine ⟨idem_smul_smul (idem_mul_self w) f, ?_, ?_, ?_⟩
    · show inc D (Tu D u) • (idem w • f) ∈ hat L₀
      rw [smul_smul, mul_comm, ← smul_smul]
      exact smul_mem_hat (idem_mem w) hf.mul_mem
    ·
      intro hmem
      apply hnot
      refine mem_of_mul_sub (OA D) (idem_mem w) ?_ hff
      rw [← hA_smul_left, ← cjA_hA]
      exact cjA_mem (hf.pair _ hmem)
    · intro y
      simp only [InCmp]
      constructor
      · rintro ⟨hy, hey⟩
        refine ⟨hey, fun x hx => hf.int x hx.1 y hy, ?_⟩
        rw [hA_smul_left]
        exact (OA D).mul_mem (idem_mem w) (hf.pair y hy)
      · rintro ⟨hey, hx, hfy⟩
        have hdual : ∀ x ∈ hat L₀, hA X x y ∈ OA D := by
          intro x hx'
          rw [hA_idem hey]
          exact hx _ ⟨smul_mem_hat (idem_mem w) hx', idem_smul_smul (idem_mul_self w) x⟩
        obtain ⟨a, ha, hya⟩ := hf.dual y hdual
        refine ⟨?_, hey⟩
        have h1 : cjA D a * idem w * hA X f f ∈ OA D := by
          have hp : hA X (idem w • f) (a • f) ∈ OA D := by
            refine mem_of_sub (OA D) hfy ?_
            rw [← hA_sub_right, hA_smul_left]
            exact (OA D).mul_mem (idem_mem w) (hf.pair _ hya)
          rwa [hA_smul_left, hA_smul_right, ← mul_assoc, mul_comm (idem w)] at hp
        have h2 : cjA D a * idem w * inc D (Tu D u)⁻¹ ∈ OA D :=
          mem_of_mul_sub (OA D) ((OA D).mul_mem (cjA_mem ha) (idem_mem w)) h1 hff
        have h3 : a * (cjA D (idem w) * inc D (Tu D u)⁻¹) ∈ OA D := by
          have hc := cjA_mem h2
          rwa [map_mul, map_mul, cjA_cjA, cjA_inc_inv, mul_assoc] at hc
        rw [split_prime (a := a) (f := f) ht hey]
        exact add_mem_hat (smul_mem_hat (cjA_mem (idem_mem w)) hya) (smul_mem_hat h3 hf.mul_mem)

end GlobalTheory.AdIsom.GlueBase
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField


theorem _root_.GlobalTheory.T.exists_heckeElement_lattice_between_prime_mul_split : ∀ (D : D7) (V : HSp D) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D) (ϖ : 𝓞 D.host.E) (k : ℕ) (g : GA D V)
    (M : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    Formalism.L2.NTheta.IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 →
    P.asIdeal • latG V g ≤ M → M ≤ latG V g →
    M.toAddSubgroup.relIndex (latG V g).toAddSubgroup = Ideal.absNorm P.asIdeal ^ k →
    ∃ a₀ : GA D V, Formalism.L2.NTheta.IsHeckeElt V e (ϖ : D.host.E) k a₀ ∧ latG V (g * a₀) ⊓ latG V g = M ∧
      (Formalism.L2.Col.conjPrime₂ P).asIdeal • latG V (g * a₀) ≤ latG V g := by
  first | exact @GlobalTheory.HeckeLocStep.exists_hecke | exact GlobalTheory.HeckeLocStep.exists_hecke | (intros; apply GlobalTheory.HeckeLocStep.exists_hecke <;> assumption)
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)

open Classical

namespace GlobalTheory.TwistTypePlaces

private theorem isConjPl_lev_of_isConjPl_div {D : D7} {PP PP' : Pl D.host.E} (h : Formalism.L2.DIV.IsConjPl PP PP') :
    Formalism.IndefR.Lev.IsConjPl PP PP' := by
  intro c hc
  exact ⟨Formalism.DivisionValues.cO D.host.E c, (h c (Formalism.DivisionValues.cO D.host.E c) rfl).1 hc, rfl⟩

private theorem conjPl_ne_and_under_eq_of_ncard_primesOver_two {D : D7} (P : Pl D.host.E)
    (h2 : (Ideal.primesOver (P.under (𝓞 D.host.F)).asIdeal (𝓞 D.host.E)).ncard = 2) :
    Formalism.DivisionValues.conjPl P ≠ P ∧ (Formalism.DivisionValues.conjPl P).under (𝓞 D.host.F) = P.under (𝓞 D.host.F) := by
  rw [GlobalTheory.QuadSignLocal.ncard_primesOver] at h2
  have hsub : {u : HeightOneSpectrum (𝓞 D.host.E) | u.under (𝓞 D.host.F) = P.under (𝓞 D.host.F)} ⊆
      {P, Formalism.DivisionValues.conjPl P} := by
    intro u hu
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq hu with hq | hq
    · exact Or.inl hq
    · exact Or.inr hq
  have hle : ({P, Formalism.DivisionValues.conjPl P} : Set (HeightOneSpectrum (𝓞 D.host.E))).ncard ≤
      {u : HeightOneSpectrum (𝓞 D.host.E) | u.under (𝓞 D.host.F) = P.under (𝓞 D.host.F)}.ncard := by
    rw [h2]
    calc ({P, Formalism.DivisionValues.conjPl P} : Set (HeightOneSpectrum (𝓞 D.host.E))).ncard
        ≤ ({Formalism.DivisionValues.conjPl P} : Set (HeightOneSpectrum (𝓞 D.host.E))).ncard + 1 := Set.ncard_insert_le _ _
      _ = 2 := by rw [Set.ncard_singleton]
  have hS := Set.eq_of_subset_of_ncard_le hsub hle
  refine ⟨fun hc => ?_, ?_⟩
  · rw [hS, hc, Set.pair_eq_singleton, Set.ncard_singleton] at h2
    exact absurd h2 (by decide)
  · have hmem : Formalism.DivisionValues.conjPl P ∈
        {u : HeightOneSpectrum (𝓞 D.host.E) | u.under (𝓞 D.host.F) = P.under (𝓞 D.host.F)} := by
      rw [hS]
      exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
    exact hmem

theorem isSplitSet_union : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ t : T, Formalism.L2.DIV.IsSplitSet (R.Pg ∪ R.Q t) ∧ Disjoint R.Pg (R.Q t) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC t
  obtain ⟨hdisj, hinj, hcard⟩ := GlobalTheory.TwistTypePlaces.places_split R F hC t
  refine ⟨?_, hdisj⟩
  unfold Formalism.L2.DIV.IsSplitSet
  intro PP hPP PP' hPP' hc

  have hPP' : PP' = Formalism.DivisionValues.conjPl PP := GlobalTheory.GoodPrimes.isConjPl_iff.mp (isConjPl_lev_of_isConjPl_div hc)
  obtain ⟨hne, hund⟩ := conjPl_ne_and_under_eq_of_ncard_primesOver_two PP (hcard PP hPP).1
  have hsame : PP' = PP :=
    hinj (Finset.mem_coe.mpr (hPP' ▸ ‹PP' ∈ R.Pg ∪ R.Q t›)) (Finset.mem_coe.mpr hPP) (by rw [hPP']; exact hund)
  exact hne (hPP' ▸ hsame)

end GlobalTheory.TwistTypePlaces
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.tameHeckeChar_splitSupported_eq_prod_residue : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (P : Finset (Pl D.host.E)) (e : AE D) (ρ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), ChrEq c χ → IsIdemSum e P → (∀ PP ∈ P, χ.TameAt PP ∧ IsRes χ PP (ρ PP)) → ∀ (x : (AE D)ˣ) (a : AE D) (a' : Formalism.L2.Herm.intAf D.host.F D.host.E) (u : ∀ PP : Pl D.host.E, (kP PP)ˣ), (x : AE D) = e * a + (1 - e) → (a' : Lev.EAf D) = toEAf D a → (∀ PP ∈ P, (u PP : kP PP) = resS D.host.F PP a') → ((c x : Circle) : ℂ) = ∏ PP ∈ P, ((ρ PP (u PP) : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.TameSplitChar.char_eq_prod_res | exact GlobalTheory.TameSplitChar.char_eq_prod_res | (intros; apply GlobalTheory.TameSplitChar.char_eq_prod_res <;> assumption)
end

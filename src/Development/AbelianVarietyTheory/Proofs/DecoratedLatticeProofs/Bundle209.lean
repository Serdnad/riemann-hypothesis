module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContinuesConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle187
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumThetaJointlyContinuous
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle198
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1730
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PairedThetaKernelContinuousAndRationallyInvarian
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle185
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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle016
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open scoped NNReal Matrix TensorProduct Topology
open Filter NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.EisCont GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Core.Rk.SWLaw (dblDec zeroSp)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EisCont

variable {D : D7}

theorem mem_stab_onX_of_mul {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) {p : GA D T} {b : GL (Fin r) (AE D)}
    (h : mt T p ⬝ d.jX = d.jX ⬝ b.1) : ∃ hp : p ∈ stab d, onX d ⟨p, hp⟩ = b :=
  ⟨⟨b, h⟩, Units.ext ((eq_of_mul_jX d (mul_jX d ⟨p, ⟨b, h⟩⟩)).trans (eq_of_mul_jX d h).symm)⟩

theorem parFlag_zero_eq_stab {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) :
    (parFlag D.sp.cm.sig T.gram d.e fun _ => 0) = stab d := by
  ext p
  constructor
  · rintro ⟨⟨B, -, hB⟩, B', -, hB'⟩
    change mt T p ⬝ d.jX = d.jX ⬝ B at hB
    change mt T p⁻¹ ⬝ d.jX = d.jX ⬝ B' at hB'
    have e1 : B ⬝ B' = 1 := by
      rw [eq_of_mul_jX d hB]
      simp only [Matrix.mul_assoc]
      rw [← hB', ← Matrix.mul_assoc (mt T p), mt_mul_inv, Matrix.one_mul, d.pX_jX]
    have e2 : B' ⬝ B = 1 := by
      rw [eq_of_mul_jX d hB']
      simp only [Matrix.mul_assoc]
      rw [← hB, ← Matrix.mul_assoc (mt T p⁻¹), mt_inv_mul, Matrix.one_mul, d.pX_jX]
    exact ⟨⟨B, B', e1, e2⟩, hB⟩
  · intro hp
    obtain ⟨α, h⟩ := hp
    obtain ⟨β, h'⟩ := (stab d).inv_mem (show p ∈ stab d from ⟨α, h⟩)
    exact ⟨⟨α.1, fun i j hij => absurd hij (lt_irrefl _), h⟩, β.1, fun i j hij => absurd hij (lt_irrefl _), h'⟩

theorem det_onX_rat {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) (q : stab d) (hq : (q : GA D T) ∈ GQ T) :
    ∃ u : D.host.Eˣ, Units.map (incA D : D.host.E →* AE D) u =
      Matrix.GeneralLinearGroup.det (onX d q) := by
  have hr : ∀ q : stab d, (q : GA D T) ∈ GQ T → (onX d q).1 ∈ ratMx D r r := fun q hq => by
    rw [eq_of_mul_jX d (mul_jX d q)]
    exact ratMx_mul ⟨_, rfl⟩ (ratMx_mul ((mem_GQ_iff T _).1 hq) ⟨_, rfl⟩)
  obtain ⟨A, hA⟩ := hr q hq
  obtain ⟨A', hA'⟩ := hr q⁻¹ ((GQ T).inv_mem hq)
  change rat A = _ at hA
  change rat A' = _ at hA'
  have hAA : A * A' = 1 := by
    apply rat_injective
    rw [rat_mul, rat_one, hA, hA', map_inv, Units.mul_inv]
  have hA'A : A' * A = 1 := by
    apply rat_injective
    rw [rat_mul, rat_one, hA, hA', map_inv, Units.inv_mul]
  refine ⟨⟨A.det, A'.det, by rw [← Matrix.det_mul, hAA, Matrix.det_one], by rw [← Matrix.det_mul, hA'A, Matrix.det_one]⟩,
    Units.ext ?_⟩
  change incA D A.det = (onX d q).1.det
  rw [← hA, RingHom.map_det]
  rfl

theorem indLaw_inv {T T₀ : HSp D} {r : ℕ} {d : HypDec T T₀ r} {μ : (AE D)ˣ →* Circle} {t : ℂ} {φ : GA D T → ℂ}
    (hφ : IndLaw (absDet d) (detChar d μ) t φ) (q : stab d) (h1 : detChar d μ q = 1) (h2 : absDet d q = 1) (g : GA D T) :
    φ (q * g) = φ g := by
  rw [hφ q g, h1, h2]
  simp [npow]

theorem leftInv_leftGrp_of_indLaw {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) {μ : (AE D)ˣ →* Circle}
    (hμ : IsHeckeChar D μ) {t : ℂ} {φ : GA D T → ℂ} (hφ : IndLaw (absDet d) (detChar d μ) t φ) :
    GlobalTheory.AutomorphicL2Unitary.LeftInv (leftGrp D.sp.cm.sig T.gram d.e fun _ => 0) φ := by
  let H : Subgroup (GA D T) :=
    { carrier := {γ | ∀ g, φ (γ * g) = φ g}
      one_mem' := fun g => by rw [one_mul]
      mul_mem' := fun {a b} ha hb g => by rw [mul_assoc, ha, hb]
      inv_mem' := fun {a} ha g => by rw [← ha, mul_inv_cancel_left] }
  have hH : (leftGrp D.sp.cm.sig T.gram d.e fun _ => 0) ≤ H := by
    refine sup_le ((Subgroup.closure_le _).2 fun u hu => ?_) fun γ hγ => ?_
    · obtain ⟨A, hA, e⟩ := lower_iff.1 hu.1
      rw [show A = 0 from Matrix.ext fun j i => hA j i le_rfl, Matrix.mul_zero, Matrix.sub_mul, Matrix.one_mul,
        sub_eq_zero] at e
      obtain ⟨hp, h1⟩ := mem_stab_onX_of_mul d (p := u) (b := 1) (e.trans (Matrix.mul_one _).symm)
      refine indLaw_inv hφ ⟨u, hp⟩ ?_ ?_
      · rw [detChar, MonoidHom.comp_apply, MonoidHom.comp_apply, h1, map_one, map_one]
      · rw [absDet, MonoidHom.comp_apply, MonoidHom.comp_apply, h1, map_one, map_one]
    · have hp : γ ∈ stab d := parFlag_zero_eq_stab d ▸ hγ.2
      obtain ⟨u, hu⟩ := det_onX_rat d ⟨γ, hp⟩ hγ.1
      refine indLaw_inv hφ ⟨γ, hp⟩ ?_ ?_
      · rw [detChar, MonoidHom.comp_apply, MonoidHom.comp_apply, ← hu]
        exact hμ.2 u
      · rw [absDet, MonoidHom.comp_apply, MonoidHom.comp_apply, ← hu]
        exact absE_inclR u
  exact fun γ hγ => hH hγ

theorem parFlag_stab_leftInv : ∀ (D : D7) (T T₀ : HSp D) (r : ℕ) (d : HypDec T T₀ r), (parFlag D.sp.cm.sig T.gram d.e fun _ => 0) = stab d ∧ ratPts D.sp.cm.sig T.gram = GQ T ∧ (∀ (p : GA D T) (b : GL (Fin r) (AE D)), (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig T.gram p).1 * adMat D.host.F d.e = adMat D.host.F d.e * b.1 → ∃ hp : p ∈ stab d, onX d ⟨p, hp⟩ = b) ∧ ∀ (μ : (AE D)ˣ →* Circle), IsHeckeChar D μ → ∀ (t : ℂ) (φ : GA D T → ℂ), IndLaw (absDet d) (detChar d μ) t φ → GlobalTheory.AutomorphicL2Unitary.LeftInv (leftGrp D.sp.cm.sig T.gram d.e fun _ => 0) φ :=
  fun _ _ _ _ d => ⟨parFlag_zero_eq_stab d, rfl, fun _ _ h => mem_stab_onX_of_mul d h,
    fun _ hμ _ _ hφ => leftInv_leftGrp_of_indLaw d hμ hφ⟩

end GlobalTheory.EisCont

end
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP


theorem _root_.GlobalTheory.T.weilRep_preserves_fockDegree_of_commute_cartan : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : WRep S T) (sS : RealMat S) (sT : RealMat T), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ k : GA D S, (∀ τ, compAt θ τ (Formalism.L2.Theta.mt S k) * sS τ = sS τ * compAt θ τ (Formalism.L2.Theta.mt S k)) → ∀ (N : ℕ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → (∀ l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ), l.length = N → l.foldr (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 f) f = 0) → ∀ l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ), l.length = N → l.foldr (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 f) (om (k, 1) f) = 0 := by
  first | exact @GlobalTheory.CartanFockDeg.om_keeps_fockDeg | exact GlobalTheory.CartanFockDeg.om_keeps_fockDeg | (intros; apply GlobalTheory.CartanFockDeg.om_keeps_fockDeg <;> assumption)
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section

namespace GlobalTheory.IkedaK

variable {D : D7}

theorem bdd_om_compact {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : WRep S T}
    (hW : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {P : Set (GA D S × GA D T)}
    (hP : IsCompact P) : ∃ C : ℝ, ∀ p ∈ P, ∀ x, ‖om p f x‖ ≤ C := by
  obtain ⟨-, -, -, -, -, K, hK, hKc⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank S.rank
  have hc := GlobalTheory.Unf.jointCont_all D ψ S T χS χT om hW f hf
  obtain ⟨C, hC⟩ := (hP.prod hK).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, fun p hp x => ?_⟩
  obtain ⟨γ, ⟨γ', rfl⟩, hx⟩ := hKc x
  have hq := (hW.om_pres p f hf).quasi γ' x
  have e : (((incA D).toAddMonoidHom.mapMatrix (m := Fin T.rank) (n := Fin S.rank)) γ') = ratW T S γ' := rfl
  rw [e] at hx
  have h1 := hW.std.1.2.1 (-(symplOH S T (ratW T S γ') x))
  have := hC (p, ratW T S γ' + x) ⟨hp, hx⟩
  simp only at this
  rw [hq, norm_mul, h1, one_mul] at this
  exact this

theorem om_mul_apply {S T : HSp D} (om : WRep S T) (p q : GA D S × GA D T) (f : WO S T → ℂ) :
    om p (om q f) = om (p * q) f := by
  rw [map_mul]; rfl

theorem weilRepUnitaryPair_left_apply_right {S T : HSp D} (om : WRep S T) (g : GA D S) (k : GA D T) (f : WO S T → ℂ) :
    om (g, 1) (om (1, k) f) = om (g, k) f := by
  rw [om_mul_apply]; congr 1; ext <;> simp

theorem weilRepUnitaryPair_right_apply_left {S T : HSp D} (om : WRep S T) (g : GA D S) (k : GA D T) (f : WO S T → ℂ) :
    om (1, k) (om (g, 1) f) = om (g, k) f := by
  rw [om_mul_apply]; congr 1; ext <;> simp

end GlobalTheory.IkedaK
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.FlatLevel

variable {D : D7}

theorem prod_diagonal_block_dets_eq_lower_block_det {κ : Type} [CommRing κ] {r t j n : ℕ} (hn : n = r + j * t) {g : GL (Fin n) κ}
    (hg : g ∈ blockTri (blkOf r t)) :
    ∏ c ∈ Finset.range j, dBlk (blkOf r t) (c + 1) g = dBlk (blk2 r) 1 g := by
  classical
  have hg2 : g ∈ blockTri (blk2 r) := blockTri_blkOf_le r t hg
  set M : Matrix (Fin n) (Fin n) κ := (g : Matrix (Fin n) (Fin n) κ) with hM
  have sq : ∀ (b : Fin n → ℕ) (c : ℕ), g ∈ blockTri b → ((dBlk b c g : κˣ) : κ) = (M.toSquareBlock b c).det := by
    intro b c h; rw [diag_block_det_val c h]; rfl
  have emp : ∀ (b : Fin n → ℕ) (c : ℕ), c ∉ Finset.univ.image b → (M.toSquareBlock b c).det = 1 := by
    intro b c hc
    haveI : IsEmpty {a : Fin n // b a = c} := ⟨fun a => hc (Finset.mem_image.2 ⟨a.1, Finset.mem_univ _, a.2⟩)⟩
    exact Matrix.det_isEmpty
  have hdet : ∀ (b : Fin n → ℕ) (N : ℕ), (∀ a, b a < N) → M.BlockTriangular b →
      M.det = ∏ c ∈ Finset.range N, (M.toSquareBlock b c).det := by
    intro b N hb hB
    rw [hB.det]
    refine Finset.prod_subset (fun c hc => ?_) (fun c _ hc => emp b c hc)
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hc
    exact Finset.mem_range.2 (hb a)
  have h1 := hdet (blkOf r t) (j + 1) (fun a => by
      unfold blkOf
      split_ifs with h
      · omega
      · have ha : a.val - r < j * t := by have := a.2; omega
        have ht : 0 < t := by
          rcases Nat.eq_zero_or_pos t with h0 | h0
          · simp [h0] at ha
          · exact h0
        have : (a.val - r) / t < j := Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact ha)
        omega) hg
  have h2 := hdet (blk2 r) 2 (fun a => by unfold blk2; split_ifs <;> omega) hg2
  rw [Finset.prod_range_succ'] at h1
  rw [Finset.prod_range_succ', Finset.prod_range_one] at h2
  have h0 : (M.toSquareBlock (blkOf r t) 0).det = (M.toSquareBlock (blk2 r) 0).det := by
    rw [← Matrix.det_submatrix_equiv_self (Equiv.subtypeEquivRight (p := fun a : Fin n => blk2 r a = 0)
      (q := fun a : Fin n => blkOf r t a = 0) (fun a => by unfold blk2 blkOf; split_ifs <;> simp_all))]
    rfl
  have hu : IsUnit (M.toSquareBlock (blk2 r) 0).det := by rw [← sq _ 0 hg2]; exact Units.isUnit _
  apply Units.ext
  rw [Units.coe_prod, sq _ 1 hg2]
  rw [Finset.prod_congr rfl (fun c _ => sq _ (c + 1) hg)]
  rw [h0] at h1
  exact hu.mul_right_cancel (h1.symm.trans h2)

end GlobalTheory.FlatLevel

namespace GlobalTheory.FlatLevel

variable {D : D7}

theorem multT_le {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) {J J' : Set (GA D V)}
    {χ χ' : GA D V → ℂ} (h : ∀ k ∈ J', k ∈ J ∧ χ k = χ' k) : MultT θ M J χ ≤ MultT θ M J' χ' :=
  Submodule.map_mono (Submodule.span_mono fun X hX =>
    ⟨hX.aut, hX.cusp, fun v k hk g => (h k hk).2 ▸ hX.lev v k (h k hk).1 g, hX.equiv, hX.cont⟩)


open Classical in
theorem lev_flat_le (c : Com D) (w : Twist D) (hw : w.Is c) (j : ℕ) {n : ℕ} (hn : n = D.R.r + j * D.R.t)
    (J : Matrix (Fin n) (Fin n) D.host.E) (β : GL (Fin n) (Lev.EAf D)) (hr hr' : D.R.r ≤ n)
    (x : GL (Fin n) (Lev.EAf D))
    (hx : x ∈ lev D.sp.cm J β (Lev.datY n D.R.r D.R.t j hr c.Pg ∅ c.P c.chi w.ξ Lev.Frm.B)) :
    x ∈ lev D.sp.cm J β (Lev.datY n D.R.r D.R.t j hr' w.Pg w.Q (LevelP.triv _ _ _) w.chi w.ξ Lev.Frm.B) ∧
      levFn β (Lev.datY n D.R.r D.R.t j hr c.Pg ∅ c.P c.chi w.ξ Lev.Frm.B) x =
        levFn β (Lev.datY n D.R.r D.R.t j hr' w.Pg w.Q (LevelP.triv _ _ _) w.chi w.ξ Lev.Frm.B) x := by
  obtain ⟨hp, hP⟩ := mem_lev.1 hx
  obtain ⟨hUA, hSt, h3, -⟩ := mem_parLev.1 hp
  have h3' : ∀ PP ∈ c.Pg, redFn β PP x ∈ blockTri (blkOf D.R.r D.R.t) := h3
  have hP' : (fun PP : c.Pg => upperLeftBlock hr (redFn β PP.1 x)) ∈ c.P.H := hP
  have hone := (hw.grp _).1 hP'
  have hPg : ∀ PP ∈ w.Pg, PP ∈ c.Pg := fun PP h => hw.union ▸ Finset.mem_union_left _ h
  have hQ : ∀ PP ∈ w.Q, PP ∈ c.Pg := fun PP h => hw.union ▸ Finset.mem_union_right _ h
  refine ⟨mem_lev.2 ⟨mem_parLev.2 ⟨hUA, hSt, fun PP h => h3' PP (hPg PP h),
    fun PP h => blockTri_blkOf_le _ _ (h3' PP (hQ PP h))⟩, ?_⟩, ?_⟩
  · show _ ∈ (⊥ : Subgroup (G0 w.Pg D.R.r))
    refine Subgroup.mem_bot.2 (funext fun PP => ?_)
    exact hone ⟨PP.1, hPg PP.1 PP.2⟩ PP.2
  · unfold levFn
    have e1 : ext1 (Lev.datY n D.R.r D.R.t j hr c.Pg ∅ c.P c.chi w.ξ Lev.Frm.B).P.H
        (Lev.datY n D.R.r D.R.t j hr c.Pg ∅ c.P c.chi w.ξ Lev.Frm.B).P.chi
        (rTup β (Lev.datY n D.R.r D.R.t j hr c.Pg ∅ c.P c.chi w.ξ Lev.Frm.B) x) = 1 := by
      show ext1 c.P.H c.P.chi _ = 1
      unfold ext1
      split_ifs
      · rw [hw.chr]; rfl
      · rfl
    have e2 : ext1 (Lev.datY n D.R.r D.R.t j hr' w.Pg w.Q (LevelP.triv _ _ _) w.chi w.ξ Lev.Frm.B).P.H
        (Lev.datY n D.R.r D.R.t j hr' w.Pg w.Q (LevelP.triv _ _ _) w.chi w.ξ Lev.Frm.B).P.chi
        (rTup β (Lev.datY n D.R.r D.R.t j hr' w.Pg w.Q (LevelP.triv _ _ _) w.chi w.ξ Lev.Frm.B) x) = 1 := by
      show ext1 (LevelP.triv w.Pg D.R.r ℂ).H (LevelP.triv w.Pg D.R.r ℂ).chi _ = 1
      unfold ext1
      split_ifs
      · rfl
      · rfl
    rw [e1, e2]
    show 1 * (∏ PP ∈ c.Pg, ∏ c' ∈ Finset.range j, c.chi (c' + 1) PP (dBlk (blkOf D.R.r D.R.t) (c' + 1) (redFn β PP x))) *
        ∏ PP ∈ (∅ : Finset (Pl D.host.E)), (w.ξ PP)⁻¹ (dBlk (blk2 D.R.r) 1 (redFn β PP x)) =
      1 * (∏ PP ∈ w.Pg, ∏ c' ∈ Finset.range j, w.chi (c' + 1) PP (dBlk (blkOf D.R.r D.R.t) (c' + 1) (redFn β PP x))) *
        ∏ PP ∈ w.Q, (w.ξ PP)⁻¹ (dBlk (blk2 D.R.r) 1 (redFn β PP x))
    rw [Finset.prod_empty, mul_one, one_mul, one_mul, hw.union, Finset.prod_union hw.disj]
    congr 1
    · refine Finset.prod_congr rfl fun PP hP => Finset.prod_congr rfl fun c' _ => ?_
      rw [hw.chiPg (c' + 1) PP hP]
    · refine Finset.prod_congr rfl fun PP hP => ?_
      simp_rw [hw.chiQ _ PP hP]
      rw [← map_prod, prod_diagonal_block_dets_eq_lower_block_det hn (h3' PP (hQ PP hP))]


open Classical in
theorem flatLe : ∀ D : D7, FlatLe D := by
  intro D c w hw j _ s hs hr
  obtain ⟨hr', hL, hflat⟩ := hs
  have hn : s.V.rank = D.R.r + j * D.R.t := hflat.rank
  show MultT c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) ≤
    MultT c.θ s.M (levS s.V s.β (Lev.datY s.V.rank D.R.r D.R.t j hr c.Pg ∅ c.P c.chi w.ξ Lev.Frm.B))
      (Lev.levChi s.V s.β (Lev.datY s.V.rank D.R.r D.R.t j hr c.Pg ∅ c.P c.chi w.ξ Lev.Frm.B))
  rw [hL]
  refine multT_le c.θ s.M fun k hk => ?_
  obtain ⟨h1, h2⟩ := lev_flat_le c w hw j hn s.V.gram s.β hr hr' _ hk.2
  exact ⟨⟨hk.1, h1⟩, (congrArg (fun u : ℂˣ => (u : ℂ)) h2).symm⟩

end GlobalTheory.FlatLevel
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section

namespace GlobalTheory.ChainTw.QuotUnr

theorem loc_eq_of_isRes {D : D7} {H H' : Formalism.L2.Host.HChar D.host.E} {PP : Pl D.host.E} {a : (kP PP)ˣ →* ℂˣ}
    (h : IsRes H PP a) (h' : IsRes H' PP a) (x : (PP.adicCompletion D.host.E)ˣ) (hx : Formalism.L2.Host.IsUnitAt PP x) :
    H.loc PP x = H'.loc PP x := by
  have ht := GlobalTheory.ChainOnto.TameRes.tameAt_of_isRes D H PP a h
  have ht' := GlobalTheory.ChainOnto.TameRes.tameAt_of_isRes D H' PP a h'
  obtain ⟨b, hb⟩ := GlobalTheory.GaussModulus.exists_int_approx PP (x := (x : PP.adicCompletion D.host.E)) (le_of_eq hx) 1
  have hlt : WithZero.exp (-((1 : ℕ) : ℤ)) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have hbv : Valued.v (algebraMap D.host.E (PP.adicCompletion D.host.E) (b : D.host.E)) = 1 := by
    have hx1 : Valued.v (x : PP.adicCompletion D.host.E) = 1 := hx
    have e : Valued.v (algebraMap D.host.E (PP.adicCompletion D.host.E) (b : D.host.E)) = Valued.v (x : PP.adicCompletion D.host.E) :=
      Valuation.map_eq_of_sub_lt _ (by rw [Valuation.map_sub_swap, hx1]; exact lt_of_le_of_lt hb hlt)
    rw [e, hx1]
  have hbP : b ∉ PP.asIdeal := by
    intro hm
    have h1 : PP.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E b) < 1 := (PP.valuation_lt_one_iff_mem b).2 hm
    have h2 : PP.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E b) = 1 := by
      rw [← GlobalTheory.GaussModulus.valued_algebraMap]; exact hbv
    exact (ne_of_lt h1) h2
  have hb0 : (b : D.host.E) ≠ 0 := fun h0 => hbP (by rw [RingOfIntegers.coe_eq_zero_iff.1 h0]; exact zero_mem _)
  let kb : D.host.Eˣ := Units.mk0 _ hb0
  haveI : PP.asIdeal.IsMaximal := PP.isMaximal
  letI : Field (kP PP) := Ideal.Quotient.field PP.asIdeal
  have hu0 : (Ideal.Quotient.mk PP.asIdeal b : kP PP) ≠ 0 := fun h0 => hbP (Ideal.Quotient.eq_zero_iff_mem.1 h0)
  let u : (kP PP)ˣ := Units.mk0 _ hu0
  have e1 := h b kb u rfl rfl
  have e2 := h' b kb u rfl rfl

  obtain ⟨y, hy⟩ : ∃ y : (PP.adicCompletion D.host.E)ˣ, y = x * (Formalism.L2.Host.atFin PP kb)⁻¹ := ⟨_, rfl⟩
  have hkv : Valued.v ((Formalism.L2.Host.atFin PP kb : (PP.adicCompletion D.host.E)ˣ) : PP.adicCompletion D.host.E) = 1 := hbv
  have hyu : Formalism.L2.Host.IsUnitAt PP y := by
    show Valued.v ((y : (PP.adicCompletion D.host.E)ˣ) : PP.adicCompletion D.host.E) = 1
    rw [hy, Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hkv, inv_one, mul_one]
    exact hx
  have hy1 : Valued.v ((y : PP.adicCompletion D.host.E) - 1) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
    have hk0 : ((Formalism.L2.Host.atFin PP kb : (PP.adicCompletion D.host.E)ˣ) : PP.adicCompletion D.host.E) =
        algebraMap D.host.E (PP.adicCompletion D.host.E) (b : D.host.E) := rfl
    have e : (y : PP.adicCompletion D.host.E) - 1 =
        ((x : PP.adicCompletion D.host.E) - algebraMap D.host.E (PP.adicCompletion D.host.E) (b : D.host.E)) *
          (algebraMap D.host.E (PP.adicCompletion D.host.E) (b : D.host.E))⁻¹ := by
      have hne : algebraMap D.host.E (PP.adicCompletion D.host.E) (b : D.host.E) ≠ 0 := by
        rw [← hk0]; exact Units.ne_zero _
      rw [hy, Units.val_mul, Units.val_inv_eq_inv_val, hk0, sub_mul, mul_inv_cancel₀ hne]
    rw [e, map_mul, map_inv₀, hbv, inv_one, mul_one]
    exact hb
  have hxy : x = Formalism.L2.Host.atFin PP kb * y := by rw [hy, mul_left_comm, mul_inv_cancel, mul_one]
  rw [hxy, map_mul, map_mul, ht y hyu hy1, ht' y hyu hy1, mul_one, mul_one]
  exact e1.symm.trans e2

end GlobalTheory.ChainTw.QuotUnr


open GlobalTheory.ChainTw.QuotUnr in
theorem GlobalTheory.ChainTw.quot_unrAt_twist : ∀ (D : D7) (c : Com D) (w : Twist D), w.Is c → ∀ PP ∈ w.Q, ∀ i j : ℕ, 1 ≤ i → i ≤ D.R.m → 1 ≤ j → j ≤ D.R.m → GlobalTheory.LFun.UnrAt (F := D.host.F) (c.μ i * (c.μ j)⁻¹) PP := by
  intro D c w hw PP hPP i j hi1 him hj1 hjm
  have hPg : PP ∈ c.Pg := by classical rw [hw.union]; exact Finset.mem_union_right _ hPP
  obtain ⟨Hi, hci, hri⟩ := hw.com.res ⟨i - 1, by omega⟩
  obtain ⟨Hj, hcj, hrj⟩ := hw.com.res ⟨j - 1, by omega⟩
  simp only [Nat.sub_add_cancel hi1, Nat.sub_add_cancel hj1] at hci hri hcj hrj
  have ri := hri PP hPg
  have rj := hrj PP hPg
  rw [hw.chiQ i PP hPP] at ri
  rw [hw.chiQ j PP hPP] at rj
  intro x hx
  have li := DFunLike.congr_fun (GlobalTheory.LFun.locChar_eq_of_chrEq hci PP) x
  have lj := DFunLike.congr_fun (GlobalTheory.LFun.locChar_eq_of_chrEq hcj PP) x
  have split : GlobalTheory.LFun.locChar (c.μ i * (c.μ j)⁻¹) PP x =
      GlobalTheory.LFun.locChar (c.μ i) PP x * (GlobalTheory.LFun.locChar (c.μ j) PP x)⁻¹ := by
    simp only [GlobalTheory.LFun.locChar, MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, map_mul, map_inv]
  rw [split, li, lj, loc_eq_of_isRes ri rj x hx, mul_inv_cancel]

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.pairedThetaKernel_continuous_and_rationally_invariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (Ξ : WO J.W₀ B.V₀ → ℂ), IsQuasiFam ψ J.W₀ B.L Y → IsThetaFunO ψ J.W₀ B.V₀ Ξ → Continuous (Function.uncurry (pairKer s vL Y Ξ)) ∧ (∀ γ ∈ GQ J.W₀, ∀ h₀ h₁, pairKer s vL Y Ξ (γ * h₀) h₁ = pairKer s vL Y Ξ h₀ h₁) ∧ ∀ γ ∈ GQ B.A, ∀ h₀ h₁, pairKer s vL Y Ξ h₀ (γ * h₁) = pairKer s vL Y Ξ h₀ h₁ := by
  first | exact @GlobalTheory.PairKer.pairKer_law | exact GlobalTheory.PairKer.pairKer_law | (intros; apply GlobalTheory.PairKer.pairKer_law <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rightDerivative_smoothCuspidal_same_level : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (U : Subgroup (GA D V)) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ), X ∈ lieAt V τ → ∀ (A : ℕ) (φ : GA D V → ℂ), IsAutFun V φ → (∀ k ∈ U, k ∈ GfC V → ∀ g, φ (g * k) = φ g) → SmoothW θ V φ → (∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) → GlobalTheory.Grow.ModGrowthExp V A (l.foldr (fun p f => Rder θ V p.1 p.2 f) φ)) → IsCuspFun V φ → IsAutFun V (Rder θ V τ X φ) ∧ (∀ k ∈ U, k ∈ GfC V → ∀ g, Rder θ V τ X φ (g * k) = Rder θ V τ X φ g) ∧ SmoothW θ V (Rder θ V τ X φ) ∧ (∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) → GlobalTheory.Grow.ModGrowthExp V A (l.foldr (fun p f => Rder θ V p.1 p.2 f) (Rder θ V τ X φ))) ∧ IsCuspFun V (Rder θ V τ X φ) := by
  first | exact @GlobalTheory.CuspStab.rder_stab | exact GlobalTheory.CuspStab.rder_stab | (intros; apply GlobalTheory.CuspStab.rder_stab <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_finiteComponent_unitary_acting_on_finiteSupported : ∀ (D : D7) (S : HSp D) (g : GA D S), ∃ x ∈ GfC S, ∀ (P : Pl D → Prop) (y : Fin S.rank → AE D), (∀ i, y i ∈ idAt D P) → mt S g *ᵥ y = mt S x *ᵥ y := by
  first | exact @GlobalTheory.GlobFin.fin_rep | exact GlobalTheory.GlobFin.fin_rep | (intros; apply GlobalTheory.GlobFin.fin_rep <;> assumption)
end

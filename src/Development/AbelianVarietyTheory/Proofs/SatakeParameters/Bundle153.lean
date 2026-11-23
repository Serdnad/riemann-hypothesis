module

public import Formalism.LocalToGlobal.Columns.Bundle023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CongruenceLevelEqDepthSucc
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle147
public import Formalism.LocalToGlobal.Columns.ChainInstY
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwChainWtSharpDivDe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumPeriodicMulLatticeFinal
public import Formalism.LocalToGlobal.Columns.Bundle024
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.KernelLattices.Bundle003
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle149
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle010
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSp
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

noncomputable section

namespace GlobalTheory.KerStd.HypCoord.FrobMove

theorem inv_map_field {E K : Type*} [Field E] [Field K] (f : E →+* K) {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n E) : (M.map f)⁻¹ = M⁻¹.map f := by
  have hd : (M.map f).det = f M.det := (RingHom.map_det f M).symm
  have ha : (M.map f).adjugate = M.adjugate.map f := (RingHom.map_adjugate f M).symm
  rw [Matrix.inv_def, Matrix.inv_def, hd, ha]
  ext i j
  simp [Ring.inverse_eq_inv', map_inv₀]

theorem conj_conj (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x :=
  D.host.φ₀.injective (by
    rw [Formalism.HC.HostAx.conjE_apply, Formalism.HC.HostAx.conjE_apply, Complex.conj_conj])

theorem frob_moves_coords : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p), UnrOK (MaximalUnramifiedExtension p) p σ → (IsResidueClassZero D p ∨ IsSg D p) → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), StdBases D lam L P → StdBases D lam L' P' → ∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), (∀ z a b₀ i, σ (gK D lam P P' b z a b₀ i) = hK D lam P P' b (posPl D p z 1) a b₀ i) ∧ (∀ w a b₀ i, σ (hK D lam P P' b w a b₀ i) = gK D lam P P' b (posPl D p w 1) a b₀ i) := by
  intro D p _ lam σ hσ hcl N N' L L' P P' hP hP' r b
  choose ρ hρ using fun z => exists_ringHom_rhoK D lam σ hσ hcl z
  have hfun : ∀ z, rhoK D lam z = ⇑(ρ z) := fun z => funext fun y => (hρ z y).1
  have hs : ∀ z y, σ (ρ z y) = ρ (posPl D p z 1) (D.host.conj y) := fun z y => by
    rw [← (hρ z y).1, ← (hρ _ _).1]; exact sigma_rhoK D lam σ hσ hcl z y
  have hsm : ∀ {n : ℕ} z (Q : Matrix (Fin n) (Fin n) D.host.E),
      (Q.map (ρ z)).map σ = (Q.map D.host.conj).map (ρ (posPl D p z 1)) := fun z Q => by
    ext i j; simp [hs]
  have hinv : ∀ {n : ℕ} z (Q : Matrix (Fin n) (Fin n) D.host.E) i j,
      σ ((Q.map (ρ z))⁻¹ i j) = ((Q.map D.host.conj).map (ρ (posPl D p z 1)))⁻¹ i j := fun z Q i j => by
    rw [← hsm, inv_map_field σ]; rfl
  have K : ∀ {n : ℕ} (Q : D.what₂.Tau → Matrix (Fin n) (Fin n) D.host.E),
      (∀ z, ((Q (tauPl D (posPl D p z 1))).map D.host.conj).transpose * Q (tauPl D z) = 1) → ∀ z,
      ((Q (tauPl D (posPl D p z 1))).map (ρ (posPl D p z 1))).transpose *
        ((Q (tauPl D z)).map D.host.conj).map (ρ (posPl D p z 1)) = 1 := by
    intro n Q hQ z
    have e : ((Q (tauPl D (posPl D p z 1))).map (ρ (posPl D p z 1))).transpose *
        ((Q (tauPl D z)).map D.host.conj).map (ρ (posPl D p z 1)) =
        ((((Q (tauPl D (posPl D p z 1))).map D.host.conj).transpose * Q (tauPl D z)).map
          (D.host.conj : D.host.E →+* D.host.E)).map (ρ (posPl D p z 1)) := by
      rw [Matrix.map_mul, Matrix.map_mul]
      congr 1
      ext i j
      simp [conj_conj]
    rw [e, hQ z]
    simp
  have K1 : ∀ {n : ℕ} (Q : D.what₂.Tau → Matrix (Fin n) (Fin n) D.host.E),
      (∀ z, ((Q (tauPl D (posPl D p z 1))).map D.host.conj).transpose * Q (tauPl D z) = 1) → ∀ z,
      (((Q (tauPl D z)).map D.host.conj).map (ρ (posPl D p z 1)))⁻¹ =
        ((Q (tauPl D (posPl D p z 1))).map (ρ (posPl D p z 1))).transpose := fun Q hQ z =>
    Matrix.inv_eq_left_inv (K Q hQ z)
  have K2 : ∀ {n : ℕ} (Q : D.what₂.Tau → Matrix (Fin n) (Fin n) D.host.E),
      (∀ z, ((Q (tauPl D (posPl D p z 1))).map D.host.conj).transpose * Q (tauPl D z) = 1) → ∀ z,
      ((Q (tauPl D z)).map D.host.conj).map (ρ (posPl D p z 1)) =
        (((Q (tauPl D (posPl D p z 1))).map (ρ (posPl D p z 1)))⁻¹).transpose := fun Q hQ z => by
    rw [Matrix.transpose_nonsing_inv]; exact (Matrix.inv_eq_right_inv (K Q hQ z)).symm
  have hPc := hP.2.1 hcl
  have hP'c := hP'.2.1 hcl
  refine ⟨fun z a b₀ i => ?_, fun w a b₀ i => ?_⟩

  · simp only [gK, hK, hfun, map_sum, map_mul]
    refine Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun a₁ _ => ?_
    rw [hs, hs, conj_conj, hinv, K1 P hPc z]
    have e2 := congrFun (congrFun (K2 P' hP'c z) b₁) b₀
    simp only [Matrix.map_apply, Matrix.transpose_apply] at e2 ⊢
    rw [e2]; ring

  · simp only [gK, hK, hfun, map_sum, map_mul]
    refine Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun a₁ _ => ?_
    rw [hs, hs, hinv, K1 P' hP'c w]
    have e2 := congrFun (congrFun (K2 P hPc w) a₁) a
    simp only [Matrix.map_apply, Matrix.transpose_apply] at e2 ⊢
    rw [e2]; ring

end GlobalTheory.KerStd.HypCoord.FrobMove
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2

theorem _root_.GlobalTheory.T.typePrimeLevel_lastStep_symmetricRows_eq_twistLevel : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m), X.Ok → Pr.Ok → Ch.Ok → levGTop Ch (rPsymF Ch) = twLt Ch R.m := by
  first | exact @GlobalTheory.levGTop_rPsymF_eq_twLt | exact GlobalTheory.levGTop_rPsymF_eq_twLt | (intros; apply GlobalTheory.levGTop_rPsymF_eq_twLt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col NumberField IsDedekindDomain Classical

noncomputable section

namespace GlobalTheory.TopXiInvQ

open Formalism.L2.Col.LocE Formalism.L2.Col.Loc GlobalTheory.GO

theorem phiTopG_add {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
    (sharp : Bool) (i : ℕ) (hc : cOf R i = 0) (P : HeightOneSpectrum (𝓞 X.E))
    (x z : HomE X.E (R.N i + cOf R i) ((R.N (i + 1) - 1) + 0))
    (hz : ∀ s l, IntAt P (z (Pi.single s 1) l / (qOf P : X.E))) :
    PhiTopG Ch mu sharp i (i + 1) (R.N (i + 1)) P (x + z) = PhiTopG Ch mu sharp i (i + 1) (R.N (i + 1)) P x := by
  unfold PhiTopG
  split_ifs
  · exact GlobalTheory.TopInv.PhiGS_add (GlobalTheory.TopInv.qOf_mem P) (GlobalTheory.TopInv.qOf_ne P) _ _ _ _ _ _ _ _ _ _ hc x z hz
  · exact GlobalTheory.TopInv.PhiG_add (GlobalTheory.TopInv.qOf_mem P) (GlobalTheory.TopInv.qOf_ne P) _ _ _ _ _ _ _ _ _ _ hc x z hz
  · exact GlobalTheory.TopInv.PhiQ_add (GlobalTheory.TopInv.qOf_mem P) (GlobalTheory.TopInv.qOf_ne P) _ _ _ _ _ _ hc x z hz

theorem xiTop_invQ : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), X.Ok → Pr.Ok → IsSel X sel → (∀ i, Pr.g i ∈ S) → (∀ v, Pr.T v ∈ S) → L.Ok Ch sel mu cst G m2 → ∀ (u : Pr.Word) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (p' : ChPt (R := R) sel mu u (m2 + 1 + 1)) x z, Y ∈ ybSet sel mu cst p.deco.1.N → z ∈ mulLat (cBof sel mu cst u) (homAt (Sall sel mu u) p.deco.1.N p'.deco.1.N) → XiTop Ch sel mu cst (m2 + 1) p Y p' (x + z) = XiTop Ch sel mu cst (m2 + 1) p Y p' x := by
  intro X Pr R Ch sel S mu cst L G m2 _hX hPr _hsel _hg _hT hL u p Y p' x z hY hz
  have hc := hL.cst_ok
  have hm := hL.hm
  have hc0 : cOf R (m2 + 1) = 0 := by unfold cOf; omega
  obtain ⟨h1, h2⟩ := loc_of_mem_mulLat (cst := cst) hPr p p' x hz
  rw [XiTop_eq, XiTop_eq, h1]
  congr 1
  refine Finset.prod_congr rfl fun P _ => ?_
  have hq0 := GlobalTheory.TopInv.qOf_ne P.1
  rw [GlobalTheory.TopInv.inFr_add]
  have hZ := h2 P
  generalize inFr (frsF sel mu p P) (frsF sel mu p' P) z = Z at hZ ⊢
  unfold topDat
  rw [LinearMap.add_comp, LinearMap.comp_add, LinearMap.comp_add]
  refine congrArg₂ (· * ·) (phiTopG_add Ch mu _ (m2 + 1) hc0 P.1 _ _ fun s l => ?_)
    (GlobalTheory.TopInv.ftY_add sel mu cst hc P (hL.depthQ P) _ _ _ (fun s => ?_) fun l => ?_)
  · obtain ⟨s, rfl⟩ : ∃ t, s = Fin.castAdd _ t := ⟨⟨s.1, by have := s.2; omega⟩, rfl⟩
    rw [LinearMap.comp_apply, LinearMap.comp_apply, GlobalTheory.TopStep.castAdd_single, ← pow_one (qOf P.1 : X.E)]
    refine GlobalTheory.TopInv.intAt_div_pow_le hq0 hc.B_pos ?_
    rw [div_eq_inv_mul]
    exact hZ s _
  · refine GlobalTheory.TopInv.atNL_int _ _ _ fun l => ?_
    rw [div_eq_inv_mul]
    exact hZ s l
  · have h3 := GlobalTheory.TopInv.repY_mem sel mu cst _ _ hY P
    rw [← (frsF sel mu p P).apply_symm_apply (_ • _)] at h3
    replace h3 := (GlobalTheory.TopStep.frsF_mem p P _).1 h3
    rw [map_smul] at h3
    exact (mem_localization_standardLattice _ _).1 h3 l

end GlobalTheory.TopXiInvQ
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links NumberField Matrix Formalism.DivisionValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GoodGenericInv

theorem typeSum_inv_eq {K G : Type} [Field K] [Group G] (P : Subgroup G) [Fintype P] (ψ : P →* Kˣ) (χ : G → K)
    (hχ : ∀ g h, χ (g * h * g⁻¹) = χ h) (t : G) (ht : ∀ h ∈ P, t * h * t⁻¹ ∈ P)
    (hψ : ∀ (h : G) (hh : h ∈ P), ψ ⟨t * h * t⁻¹, ht h hh⟩ = (ψ ⟨h, hh⟩)⁻¹) :
    ∑ h : P, χ (h : G) * ((((ψ⁻¹) h)⁻¹ : Kˣ) : K) = ∑ h : P, χ (h : G) * (((ψ h)⁻¹ : Kˣ) : K) := by
  have hinj : Function.Injective (fun h : P => (⟨t * h * t⁻¹, ht h h.2⟩ : P)) := by
    intro a b e
    apply Subtype.ext
    have := congrArg Subtype.val e
    simpa using this
  have hbij : Function.Bijective (fun h : P => (⟨t * h * t⁻¹, ht h h.2⟩ : P)) :=
    (Finite.injective_iff_bijective).1 hinj
  rw [← (Equiv.ofBijective _ hbij).sum_comp]
  refine Finset.sum_congr rfl fun h _ => ?_
  simp only [Equiv.ofBijective_apply, MonoidHom.inv_apply, inv_inv]
  rw [hχ, hψ h h.2]

def sgnDiag (κ : Type) [CommRing κ] (r : ℕ) : GL (Fin r) κ where
  val := Matrix.diagonal fun i => (-1) ^ i.val
  inv := Matrix.diagonal fun i => (-1) ^ i.val
  val_inv := by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; rw [← pow_add, ← two_mul, pow_mul]; simp
  inv_val := by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; rw [← pow_add, ← two_mul, pow_mul]; simp

theorem sgnDiag_conj_apply {κ : Type} [CommRing κ] {r : ℕ} (u : GL (Fin r) κ) (i j : Fin r) :
    ((sgnDiag κ r * u * (sgnDiag κ r)⁻¹ : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) i j =
      (-1) ^ i.val * (-1) ^ j.val * (u : Matrix (Fin r) (Fin r) κ) i j := by
  show (Matrix.diagonal (fun i : Fin r => ((-1 : κ)) ^ i.val) * (u : Matrix (Fin r) (Fin r) κ) *
    Matrix.diagonal (fun i : Fin r => ((-1 : κ)) ^ i.val)) i j = _
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  ring

end GlobalTheory.GoodGenericInv

namespace GlobalTheory.GoodGenericInv

variable {κ : Type} [CommRing κ] {r : ℕ}

theorem sgnDiag_conj_mem_unip {u : GL (Fin r) κ} (hu : u ∈ unip κ r) :
    sgnDiag κ r * u * (sgnDiag κ r)⁻¹ ∈ unip κ r := by
  refine ⟨?_, fun i => ?_⟩
  · intro i j h
    rw [sgnDiag_conj_apply, unip_lower hu (show j < i from h), mul_zero]
  · rw [sgnDiag_conj_apply, unip_diag hu i, ← pow_add, ← two_mul, pow_mul]
    simp

theorem edgeSum_sup_conj (u : GL (Fin r) κ) :
    edgeSum supEdge (sgnDiag κ r * u * (sgnDiag κ r)⁻¹) = - edgeSum supEdge u := by
  unfold edgeSum
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · rw [sgnDiag_conj_apply]
    unfold supEdge at h
    have hs : ((-1 : κ)) ^ (i : ℕ) * (-1) ^ (i : ℕ) = 1 := by rw [← mul_pow]; simp
    rw [h, pow_succ]
    linear_combination (-(u : Matrix (Fin r) (Fin r) κ) i j) * hs
  · simp

end GlobalTheory.GoodGenericInv

namespace GlobalTheory.GoodGenericInv

variable {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ}

def alternatingSignDiagonalLevelGroup (Pg : Finset (Pl E)) (r : ℕ) : G0 Pg r := fun PP => sgnDiag (kP PP.1) r

theorem alternatingSignDiagonal_conj_mem_genericLevel (ψ : ∀ PP : Pl E, AddChar (kP PP) ℂ) {x : G0 Pg r} (hx : x ∈ (P0 Pg r ψ).H) :
    alternatingSignDiagonalLevelGroup Pg r * x * (alternatingSignDiagonalLevelGroup Pg r)⁻¹ ∈ (P0 Pg r ψ).H := by
  intro PP _
  exact sgnDiag_conj_mem_unip (hx PP (Set.mem_univ _))

theorem genericLevelCharacter_alternatingSign_conj_inv (ψ : ∀ PP : Pl E, AddChar (kP PP) ℂ) {x : G0 Pg r} (hx : x ∈ (P0 Pg r ψ).H) :
    (P0 Pg r ψ).chi ⟨alternatingSignDiagonalLevelGroup Pg r * x * (alternatingSignDiagonalLevelGroup Pg r)⁻¹, alternatingSignDiagonal_conj_mem_genericLevel ψ hx⟩ = ((P0 Pg r ψ).chi ⟨x, hx⟩)⁻¹ := by
  letI : IsOneApply ((Subgroup.pi Set.univ (fun PP : ↥Pg => unip (kP PP.1) r)) →* ℂˣ) := ⟨fun _ => rfl⟩
  letI : IsMulApply ((Subgroup.pi Set.univ (fun PP : ↥Pg => unip (kP PP.1) r)) →* ℂˣ) := ⟨fun _ _ _ => rfl⟩
  show (∏ PP : ↥Pg, (addCharHom (ψ PP.1) (supHom (kP PP.1) r)).comp (LevelP.prj (fun PP => unip (kP PP.1) r) PP))
      ⟨alternatingSignDiagonalLevelGroup Pg r * x * (alternatingSignDiagonalLevelGroup Pg r)⁻¹, alternatingSignDiagonal_conj_mem_genericLevel ψ hx⟩ =
    ((∏ PP : ↥Pg, (addCharHom (ψ PP.1) (supHom (kP PP.1) r)).comp (LevelP.prj (fun PP => unip (kP PP.1) r) PP)) ⟨x, hx⟩)⁻¹
  rw [prod_apply, prod_apply, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun PP _ => ?_
  apply Units.ext
  simp only [MonoidHom.comp_apply, addCharHom, MonoidHom.coe_toHomUnits, Units.val_inv_eq_inv_val]
  show ψ PP.1 (Multiplicative.toAdd (Multiplicative.ofAdd (edgeSum supEdge (sgnDiag (kP PP.1) r * x PP * (sgnDiag (kP PP.1) r)⁻¹)))) =
    (ψ PP.1 (Multiplicative.toAdd (Multiplicative.ofAdd (edgeSum supEdge (x PP)))))⁻¹
  rw [toAdd_ofAdd, toAdd_ofAdd, edgeSum_sup_conj, AddChar.map_neg_eq_inv]

end GlobalTheory.GoodGenericInv

namespace GlobalTheory.GoodGenericInv

theorem level_character_eq_of_eq {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ} {LL : Type} [CommRing LL]
    {L L' : LevelP Pg r LL} (h : L = L') (x : G0 Pg r) (hx : x ∈ L.H) (hx' : x ∈ L'.H) :
    L.chi ⟨x, hx⟩ = L'.chi ⟨x, hx'⟩ := by
  subst h; rfl

end GlobalTheory.GoodGenericInv
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.divisorsAt_inv_dualLabel_and_stabilizer_mul : ∀ {D : D7} (V : HSp D) (e : Formalism.L2.Theta.AE D) (ϖ : D.host.E) (d : List ℤ) (α : GA D V), e * e = e → ϖ ≠ 0 → DivAt V e ϖ d α → DivAt V e ϖ (dualLab d) α⁻¹ ∧ ∀ a ∈ KsphC V ∅, ∀ b ∈ KsphC V ∅, DivAt V e ϖ d (a * α * b) := by
  first | exact @GlobalTheory.DivDual.divAt_inv_and_mul | exact GlobalTheory.DivDual.divAt_inv_and_mul | (intros; apply GlobalTheory.DivDual.divAt_inv_and_mul <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

theorem _root_.GlobalTheory.T.padicSeries_linearCoords_eq_flatTaylor : ∀ (D : D7) (X : Fields) (s : Seam D X) (N N' : ℕ) (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ ≃+* ℂ_[p]), Formalism.L2.KerInert.IotaExt lm ι → ∀ G : TaylorLogMetric.VC D N N' → ℂ, AnalyticOnNhd ℂ G Set.univ → TaylorLogMetric.CoefIn D G TaylorLogMetric.Qbar → ∀ (ν : Type) [Fintype ν] (M : D.what₂.Tau × Fin N' × Fin N → ν → ℂ_[p]), TaylorLogMetric.atLin M (fun j => MvPowerSeries.X j) (TaylorLogMetric.pSer D lm G) = Formalism.L2.Th1.G.linSub (fun (i : DVar X.Tau N N') x => M (s.iT i.1, i.2) x) (MvPowerSeries.map (ι : ℂ →+* ℂ_[p]) (taylorMv fun z => G (s.flatV N N' z))) := by
  first | exact @GlobalTheory.FlatTaylorBridge.bridge | exact GlobalTheory.FlatTaylorBridge.bridge | (intros; apply GlobalTheory.FlatTaylorBridge.bridge <;> assumption)
end

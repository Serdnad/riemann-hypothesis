module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PairValPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle052
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle001
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCount
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle047
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle067
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle035
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle051
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle057
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle054
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle064
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle066
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle013
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle065
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle048
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.IsLoUniConjTranspose
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle060

@[expose] public section

section

noncomputable section

namespace Formalism.L2.SG.Pf.TupGlobApprox

open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.Pf.ProdEApprox Formalism.L2.SG.Pf.PCount ValuativeRel

section Theta

variable {K : Type*} [CommRing K] {r : ℕ}

theorem signMatrix_transpose : (Sg K r).transpose = Sg K r := Matrix.diagonal_transpose _

theorem theta_mul (M N : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    Sg K r * (M * N).transpose * Sg K r = (Sg K r * N.transpose * Sg K r) * (Sg K r * M.transpose * Sg K r) := by
  rw [Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Sg K r) (Sg K r), sg_sq, Matrix.one_mul]

theorem theta_theta (M : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    Sg K r * (Sg K r * M.transpose * Sg K r).transpose * Sg K r = M := by
  rw [Matrix.transpose_mul, Matrix.transpose_mul, signMatrix_transpose, Matrix.transpose_transpose]
  simp only [Matrix.mul_assoc]
  rw [sg_sq, Matrix.mul_one, ← Matrix.mul_assoc, sg_sq, Matrix.one_mul]

theorem theta_stab {a Y b : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : a * Y * b = Y) :
    (Sg K r * b.transpose * Sg K r) * (Sg K r * Y.transpose * Sg K r) * (Sg K r * a.transpose * Sg K r) =
      Sg K r * Y.transpose * Sg K r := by
  rw [← theta_mul, ← theta_mul, ← Matrix.mul_assoc, h]

theorem theta_sub_one (M : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    Sg K r * (M - 1).transpose * Sg K r = Sg K r * M.transpose * Sg K r - 1 := by
  rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, sg_sq]

theorem theta_lo {U : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : IsUp U) : IsLo (Sg K r * U.transpose * Sg K r) :=
  isLo_conj (isLo_transpose h) _ _ (fun a => sgn_sq' r a)

theorem theta_up {L : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : IsLo L) : IsUp (Sg K r * L.transpose * Sg K r) :=
  isUp_conj (isUp_transpose h) _ _ (fun a => sgn_sq' r a)

theorem neg_one_pow_mem (J : AddSubgroup K) (k : ℕ) {x : K} (hx : x ∈ J) : (-1 : K) ^ k * x ∈ J := by
  rcases neg_one_pow_eq_or K k with h | h <;> rw [h]
  · rwa [one_mul]
  · rw [neg_one_mul]; exact J.neg_mem hx

theorem ent_theta {J : AddSubgroup K} {M : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : EntIn J M) :
    EntIn J (Sg K r * M.transpose * Sg K r) := by
  intro i j
  simp only [Sg, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply]
  rw [mul_comm]
  exact neg_one_pow_mem J _ (neg_one_pow_mem J _ (h j i))

theorem sign_transpose_twisted (s e : K) (cf : Fin (r + 1) → K) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    Sg K r * (s • (Matrix.diagonal cf * (Z.transpose * Sg K r) * Matrix.diagonal cf) - e • Ecorner r).transpose *
      Sg K r = s • (Matrix.diagonal cf * (Z * Sg K r) * Matrix.diagonal cf) - e • Ecorner r := by
  ext i j
  simp only [Sg, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, Ecorner, Matrix.of_apply]
  have hs := sgn_sq' (R := K) r
  by_cases hij : i = Fin.last r ∧ j = Fin.last r
  · obtain ⟨rfl, rfl⟩ := hij
    rw [if_pos ⟨rfl, rfl⟩]
    simp only [Fin.val_last, Nat.sub_self, pow_zero]
    ring
  · have hji : ¬ (j = Fin.last r ∧ i = Fin.last r) := fun h => hij ⟨h.2, h.1⟩
    rw [if_neg hij, if_neg hji]
    linear_combination (s * cf i * cf j * Z i j * (-1 : K) ^ (r - j.val)) * hs i

theorem theta_move (cf cfi : Fin (r + 1) → K) (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    Sg K r * (Matrix.diagonal cfi * (Sg K r * A.transpose * Sg K r) * Matrix.diagonal cf).transpose * Sg K r =
      Matrix.diagonal cf * A * Matrix.diagonal cfi := by
  ext i j
  simp only [Sg, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply]
  have hs := sgn_sq' (R := K) r
  linear_combination (cf i * A i j * cfi j * (-1 : K) ^ (r - j.val) * (-1 : K) ^ (r - j.val)) * hs i +
    (cf i * A i j * cfi j) * hs j

end Theta

section ModelR

variable {Fp Ep : Type} [Field Fp] [ValuativeRel Fp] [TopologicalSpace Fp] [CommRing Ep] [Algebra Fp Ep]
  [TopologicalSpace Ep] [MeasurableSpace Ep]

theorem mem_R_of (M : Formalism.MainNotions.S.Loc.Model Fp Ep) (g : Formalism.MainNotions.S.Loc.SplitG M.L) (hM : M.split = some g) (x : Ep)
    (h1 : (g.e x).1 ∈ 𝒪[Fp]) (h2 : (g.e x).2 ∈ 𝒪[Fp])
    (h3 : ∃ t ∈ 𝒪[Fp], (g.e x).1 - (g.e x).2 = (g.q : Fp) * t) : x ∈ M.R := by
  obtain ⟨L, sp, mu⟩ := M
  change Formalism.MainNotions.S.Loc.SplitG L at g
  obtain rfl : sp = some g := hM
  exact (Formalism.MainNotions.LocalModelPeriodLattices.mem_R_split L g mu x).2 ⟨h1, h2, h3⟩

end ModelR

section Place

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.TupGlob
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D)

theorem ptMat_mono' (w : Point D.host.E (D.R.rS + 1)) : ptMat w = mono (fσ w) (fun a => pv w.1 a) := by
  ext a b
  rw [ptMat_fσ]
  rfl

def gX (L₁ X' : PairVal.MatR D) : PairVal.MatR D := L₁ * X' * L₁⁻¹

def gY (w : Point D.host.E (D.R.rS + 1)) (U₁ X' : PairVal.MatR D) : PairVal.MatR D :=
  U₁⁻¹ * (cOf (fσ w) (fun a => pv w.1 a) X')⁻¹ * U₁

theorem glob_stab (w : Point D.host.E (D.R.rS + 1)) {Z₁ L₁ U₁ X' : PairVal.MatR D} (hL₁ : IsLo L₁) (hU₁ : IsUp U₁)
    (hZ : Z₁ * Sg D.host.E D.R.rS = L₁ * ptMat w * U₁) (hX' : IsLo X')
    (hpat : ∀ i j, fσ w j < fσ w i → X' i j = 0) :
    IsLo (gX L₁ X') ∧ IsUp (gY w U₁ X') ∧
      gX L₁ X' * (Z₁ * Sg D.host.E D.R.rS) * gY w U₁ X' = Z₁ * Sg D.host.E D.R.rS := by
  have hν : ∀ a : Fin (D.R.rS + 1), IsUnit (pv w.1 a) := fun a => IsUnit.mk0 _ (pv_ne' w a)
  have hup := cOf_up (fσ_fσ w) (fun a => pv w.1 a) X' hX'.1 hpat hν
  have hc : IsUp (cOf (fσ w) (fun a => pv w.1 a) X') := ⟨hup.1, fun a b hab => hup.2 b a hab⟩
  have hdc : IsUnit (cOf (fσ w) (fun a => pv w.1 a) X').det := by rw [det_up' hc]; exact isUnit_one
  have hdL : IsUnit L₁.det := by rw [det_lo' hL₁]; exact isUnit_one
  have hdU : IsUnit U₁.det := by rw [det_up' hU₁]; exact isUnit_one
  refine ⟨isLo_mul (isLo_mul hL₁ hX') (isLo_inv hL₁), isUp_mul (isUp_mul (isUp_inv hU₁) (isUp_inv hc)) hU₁, ?_⟩
  have hfix := fix_cOf (fσ_fσ w) (fun a => pv w.1 a) hν X'
  rw [hZ, ptMat_mono']
  simp only [gX, gY, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc L₁⁻¹ L₁, Matrix.nonsing_inv_mul _ hdL, Matrix.one_mul, ← Matrix.mul_assoc U₁ U₁⁻¹,
    Matrix.mul_nonsing_inv _ hdU, Matrix.one_mul, ← Matrix.mul_assoc X' (mono (fσ w) (fun a => pv w.1 a)), hfix,
    Matrix.mul_assoc (mono (fσ w) (fun a => pv w.1 a)),
    ← Matrix.mul_assoc (cOf (fσ w) (fun a => pv w.1 a) X') (cOf (fσ w) (fun a => pv w.1 a) X')⁻¹,
    Matrix.mul_nonsing_inv _ hdc, Matrix.one_mul]

theorem locL_lo (p : PlF D) {A B : PairVal.MatR D} (hA : IsLo A) (hB : IsUp B) : IsLo (locL Zd p A B) := by
  rcases hM : (Zd.M p).split with _ | g <;> simp only [locL, hM]
  · exact isLo_conj (isLo_map _ hA) _ _ (fun a => by simp only [← map_mul, cf_cfi, map_one])
  · exact isLo_glue _ (isLo_conj (isLo_map _ hA) _ _ (cf_cfi Zd p))
      (isLo_conj (theta_lo (isUp_map _ hB)) _ _ (cf_cfi Zd p))

theorem locR_up (p : PlF D) {A B : PairVal.MatR D} (hA : IsLo A) (hB : IsUp B) : IsUp (locR Zd p A B) := by
  rcases hM : (Zd.M p).split with _ | g <;> simp only [locR, hM]
  · exact isUp_conj (isUp_map _ hB) _ _ (fun a => by simp only [← map_mul, cfi_cf, map_one])
  · exact isUp_glue _ (isUp_conj (isUp_map _ hB) _ _ (cfi_cf Zd p))
      (isUp_conj (theta_up (isLo_map _ hA)) _ _ (cfi_cf Zd p))

theorem key_stab (p : PlF D) {l ρ L R Yp : MatP D p} (hl : TieN.IntLow (Zd.M p) l) (hρ : TieN.IntUp (Zd.M p) ρ)
    (h : L * Yp * R = l * Yp * ρ) : (l⁻¹ * L) * Yp * (R * ρ⁻¹) = Yp := by
  obtain ⟨-, hll, -⟩ := ZsVolGrp.intLow_inv (Zd.M p) hl
  obtain ⟨-, -, hρρ⟩ := ZsVolGrp.intUp_inv (Zd.M p) hρ
  calc (l⁻¹ * L) * Yp * (R * ρ⁻¹) = l⁻¹ * (L * Yp * R) * ρ⁻¹ := by simp only [Matrix.mul_assoc]
    _ = Yp := by
      rw [h]
      simp only [Matrix.mul_assoc]
      rw [hρρ, Matrix.mul_one, ← Matrix.mul_assoc, hll, Matrix.one_mul]

theorem corr_move (u u' : D.what₂.Word) (p : PlF D) {Z₁ A₀ B₀ X Y : PairVal.MatR D} (hA₀ : IsLo A₀) (hB₀ : IsUp B₀)
    (hX : IsLo X) (hY : IsUp Y) (hst : X * (Z₁ * Sg D.host.E D.R.rS) * Y = Z₁ * Sg D.host.E D.R.rS) :
    locL Zd p (A₀ * X) (Y * B₀) * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) *
        locR Zd p (A₀ * X) (Y * B₀) =
      locL Zd p A₀ B₀ * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) * locR Zd p A₀ B₀ := by
  have h2 : A₀ * (Z₁ * Sg D.host.E D.R.rS) * B₀ * Sg D.host.E D.R.rS * Sg D.host.E D.R.rS =
      A₀ * (Z₁ * Sg D.host.E D.R.rS) * B₀ := by
    rw [Matrix.mul_assoc (A₀ * (Z₁ * Sg D.host.E D.R.rS) * B₀), sg_sq, Matrix.mul_one]
  have h3 : A₀ * (Z₁ * Sg D.host.E D.R.rS) * B₀ * Sg D.host.E D.R.rS * Sg D.host.E D.R.rS =
      (A₀ * X) * (Z₁ * Sg D.host.E D.R.rS) * (Y * B₀) := by
    rw [h2]
    conv_lhs => rw [← hst]
    simp only [Matrix.mul_assoc]
  exact (locMove Zd u u' p (isLo_mul hA₀ hX) (isUp_mul hY hB₀) h3).symm.trans (locMove Zd u u' p hA₀ hB₀ h2)

theorem locL_L (p : PlF D) (hM : (Zd.M p).split = none) (A B : PairVal.MatR D) :
    locL Zd p A B = Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) *
      A.map (D.s.atP p).ιE * Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)) := by
  simp only [locL, hM]

theorem locR_L (p : PlF D) (hM : (Zd.M p).split = none) (A B : PairVal.MatR D) :
    locR Zd p A B = Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)) *
      B.map (D.s.atP p).ιE * Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) := by
  simp only [locR, hM]

section Typed

variable (p : PlF D) {g : Loc.SplitG (Zd.M p).L} (hM : (Zd.M p).split = some g)
  {e : (D.s.atP p).Ep ≃ₐ[(D.s.atP p).Fp] (D.s.atP p).Fp × (D.s.atP p).Fp} (hge : g.e = e)
include hM hge

theorem leftLocal_firstProj (A B : PairVal.MatR D) : (locL Zd p A B).map (p1 e) =
    Matrix.diagonal (cf Zd p) * A.map ((p1 e).comp (D.s.atP p).ιE) * Matrix.diagonal (cfi Zd p) := by
  simp only [locL, hM, hge, glue_map_fst]

theorem rightLocal_secondProj (A B : PairVal.MatR D) : (locR Zd p A B).map (p2 e) =
    Matrix.diagonal (cfi Zd p) * (Sg (D.s.atP p).Fp D.R.rS * (A.map ((p2 e).comp (D.s.atP p).ιE)).transpose *
      Sg (D.s.atP p).Fp D.R.rS) * Matrix.diagonal (cf Zd p) := by
  simp only [locR, hM, hge, glue_map_snd]

end Typed

end Place

end Formalism.L2.SG.Pf.TupGlobApprox
end
end

section

namespace Formalism.L2.SG.Pf.MassDataX

open Formalism.L2.SG.TypedSets

theorem inMassesAt_holds :
    ∀ {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
      (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word)
      (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (L : LocIn (TypX X)) (A : AnIn),
      InMassesAt X hb hK FdN FdN' u u' X0 L A :=
  massDataMasses_of' hinfCompact_holds kCompactOpen_holds classFinite_holds strongApproxN_holds

end Formalism.L2.SG.Pf.MassDataX
end

section

noncomputable section

open scoped Classical Matrix
open ValuativeRel

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW IsDedekindDomain
  Formalism.L2.SG.TermLoc Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.PCount

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem tupFun_holds {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Formalism.L2.SG.Pf.FibPart.TupFun M δ u u' F0 what₂ := by
  intro hpre γ w Z hel hZ hrep
  obtain ⟨hAg, -, -, hN, hR, hE⟩ := hpre
  let Zd : LocDat D := ⟨δ, M, hAg⟩
  have hex : ∃ x : Point D.host.E (D.R.rS + 1) × LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) ×
      Formalism.L2.SG.PairVal.MatR D × Formalism.L2.SG.PairVal.MatR D,
      Formalism.L2.SG.PairVal.NormRep γ x.1 x.2.1 x.2.2.1 x.2.2.2 := by
    obtain ⟨y, hy⟩ := hN γ w hel.2 (hE γ w hel) hel.1.1
    exact ⟨(w, y), hy⟩
  have hzT : zT γ = ZhatL (lf D F0) hex.choose.2.1 := by
    unfold zT nrep
    rw [dite_eq_left hex]
  obtain ⟨⟨hPD₁, hmk₁⟩, hA₁, -⟩ := hex.choose_spec
  obtain ⟨F₂, hF₂, hPD₂, hmk₂⟩ := hrep
  have hRL : IsRowLat D F0 γ.lam := hR.1 γ.lam γ.mem
  have hdc : Formalism.L2.SG.TermDef.DCRel γ.lam (lf D F0) hex.choose.2.1 F₂ :=
    (Formalism.L2.SG.Pf.double_coset_equivalence γ.lam (lf D F0) (Formalism.L2.SG.TermDef.PD D γ.lam (lf D F0) u') ⟨_, hPD₁⟩
      ⟨F₂, hPD₂⟩).1 (hmk₁.trans hmk₂.symm)
  have hZ2 : ZhatL (lf D F0) F₂ = Z := hF₂.2.2.2.2
  funext p
  obtain ⟨l, ρ, hl, hρ, h1⟩ := one_dir Zd hRL _ F₂ hPD₁ hA₁ hF₂.2.1 hdc p
  obtain ⟨l', ρ', hl', hρ', h2⟩ := one_dir Zd hRL F₂ _ hPD₂ hF₂.2.1 hA₁
    (Formalism.L2.SG.Pf.dcrel_symm γ.lam (lf D F0) hdc) p
  have key := kkOrb_eq_of hl' hρ' hl hρ h2 h1
  show kkOrb M p (Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (zT γ) * sgnP p) =
    kkOrb M p (Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p Z * sgnP p)
  rw [hzT, ← hZ2]
  exact key

end Formalism.L2.SG.Pf.FibQ
end
end

section

noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

def starInU (γ : TermDef.Term D u u' F0 what₂) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) : Prop :=
  ∀ b, frame F'₂ b ∈ Submodule.span D.host.E (Set.range (Sum.elim (frame (lf D F0)) (starFrame γ)))

def starOmL (f f' : Fin (D.R.rS + 1) → (VS D).V) : (VS D).V :=
  ∑ a, star ((starZh f f').adjugate (Fin.last D.R.rS) a) • f a

theorem star_frame_lead_minor (γ : TermDef.Term D u u' F0 what₂) (l : ℕ) :
    leadMinorE (starZh (frame (lf D F0)) (starFrame γ)) l = leadMinorE (ZhatL (lf D F0) (repF γ)) l := by
  obtain ⟨hξ1, hξ2⟩ := inv_unitri _ (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).1 (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).2
  have hZ : starZh (frame (lf D F0)) (starFrame γ) =
      1 * ZhatL (lf D F0) (repF γ) *
        (Matrix.of fun a b => (((admXi D γ.lam (lf D F0) (repF γ))⁻¹ a b : 𝓞 D.host.E) : D.host.E)) := by
    rw [Matrix.one_mul]
    exact FsLA.gram_comb_left (S := VS D) (frame (repF γ)) _ (frame (lf D F0))
  rw [hZ, Formalism.L2.SG.Pf.leadMinor_uni 1 _ _ (fun a c h => Matrix.one_apply_ne (ne_of_lt h))
    (fun a => Matrix.one_apply_eq a) (fun d b h => by simp [Matrix.of_apply, hξ1 d b h])
    (fun b => by simp [Matrix.of_apply, hξ2 b]) l]

theorem starG_ne (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)) (hγ : EligAt γ w) :
    (starZh (frame (lf D F0)) (starFrame γ)).det * star (starZh (frame (lf D F0)) (starFrame γ)).det -
      CntLocal.Tn u * ((Tu D u' : ℕ) : D.host.E) *
        (leadMinorE (starZh (frame (lf D F0)) (starFrame γ)) D.R.rS *
          star (leadMinorE (starZh (frame (lf D F0)) (starFrame γ)) D.R.rS)) ≠ 0 := by
  obtain ⟨-, hG⟩ := hγ.1
  obtain ⟨h2, h2e⟩ := starRepF_rep γ
  have hrel2 := (Formalism.L2.SG.Pf.double_coset_equivalence γ.lam (lf D F0) (PD D γ.lam (lf D F0) u') (Quot.out γ.cls)
    ⟨repF γ, h2⟩).1 ((Quot.out_eq γ.cls).trans h2e.symm)
  have hGv : Gval (lf D F0) (repF γ) ≠ 0 := by
    have he := Formalism.L2.SG.Pf.gval_rel (lf D F0) hrel2
    change Gval (lf D F0) (repF γ) = _ at he
    rw [he]; exact hG
  rw [← FsLA.leadMinorE_full, star_frame_lead_minor, star_frame_lead_minor]
  exact hGv

theorem starGlob (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (hC : Ctx γ Z)
    (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (hZ : ZhatL (lf D F0) F'₂ = Z)
    (hU : starInU γ F'₂) :
    ∃ (g : (VS D).V ≃ₗ[D.host.E] (VS D).V) (y : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → (VS D).V),
      (∀ x x', (VS D).hT (g x) (g x') = (VS D).hT x x') ∧ (∀ b, g (starFrame γ b) = frame F'₂ b) ∧
      (∀ v, g v = v + ∑ k, (VS D).hT (Sum.elim (frame (lf D F0)) (starFrame γ) k) v • y k) ∧
      star (starZh (frame (lf D F0)) (starFrame γ)).det • starOmL (frame (lf D F0)) (frame F'₂) -
        star Z.det • g (starOmL (frame (lf D F0)) (starFrame γ)) ∈ Xsp F'₂ := by
  obtain ⟨w, hγ, -⟩ := id hC
  obtain ⟨hZd, hZ₁d, hx⟩ := starMinors_holds u u' F0 what₂ γ Z hC
  set f := frame (lf D F0) with hf
  set f₁ := starFrame γ with hf₁
  set Z₁ := starZh f f₁ with hZ₁
  set F₂ := F'₂.fl with hF₂
  have hfF : f = F0.fvec := rfl
  have hf₂ : frame F'₂ = F₂.fvec := rfl
  have hZe : ∀ a b, (VS D).hT (f a) (F₂.fvec b) = Z a b := fun a b => by rw [← hZ]; rfl
  have hg2 : FsLA.gram (VS D) f F₂.fvec = Zᴴ := by
    refine Matrix.ext fun i j => ?_
    simp only [FsLA.gram, Matrix.conjTranspose_apply]
    rw [← hZe, ← (LinearMap.isSymm_def.1 (VS D).herm) (f j) (F₂.fvec i), starRingEnd_apply]
  have hZ1e : FsLA.gram (VS D) f₁ F0.fvec = Z₁ := rfl
  obtain ⟨hf1a, hf1b⟩ := star_frame_orthogonal γ
  have h1f : ∀ a b, (a ≠ Fin.last D.R.rS ∨ b ≠ Fin.last D.R.rS) → (VS D).hT (f a) (f b) = 0 :=
    fun a b h => FsLA.gram_fvec_zero F0 a b h
  have h2f : (VS D).hT (f (Fin.last D.R.rS)) (f (Fin.last D.R.rS)) = -CntLocal.Tn u := FsLA.gram_fvec_last F0
  have hdZ1h : Z₁ᴴ.det ≠ 0 := by rw [Matrix.det_conjTranspose]; exact star_ne_zero.2 hZ₁d
  have hdg2 : (FsLA.gram (VS D) f F₂.fvec).det ≠ 0 := by
    rw [hg2, Matrix.det_conjTranspose]; exact star_ne_zero.2 hZd
  have hx2 : leadMinorE (FsLA.gram (VS D) f F₂.fvec) D.R.rS * Z₁ᴴ.det =
      leadMinorE Z₁ᴴ D.R.rS * (FsLA.gram (VS D) f F₂.fvec).det := by
    rw [hg2, FsLA.lm_conjTranspose, FsLA.lm_conjTranspose, Matrix.det_conjTranspose, Matrix.det_conjTranspose,
      ← star_mul', ← star_mul', mul_comm (leadMinorE Z D.R.rS), hx, mul_comm]
  obtain ⟨F₃, hZ3, hom3, hsp3⟩ := FsLA.frame_la F₂ f h1f h2f Z₁ᴴ hdZ1h hdg2 hx2
  set h := F₃.fvec with hh
  set uu := Sum.elim f f₁ with huu
  set uu' := Sum.elim h F₂.fvec with huu'
  have hZ3e : ∀ a b, (VS D).hT (F₂.fvec a) (h b) = Z₁ᴴ a b := fun a b => congrFun (congrFun hZ3 a) b
  have k1 : ∀ a b, (VS D).hT (h a) (h b) = (VS D).hT (f a) (f b) := by
    intro a b
    by_cases hab : a ≠ Fin.last D.R.rS ∨ b ≠ Fin.last D.R.rS
    · exact (FsLA.gram_fvec_zero F₃ a b hab).trans (FsLA.gram_fvec_zero F0 a b hab).symm
    · push_neg at hab
      rw [hab.1, hab.2]
      exact (FsLA.gram_fvec_last F₃).trans (FsLA.gram_fvec_last F0).symm
  have k2 : ∀ a b, (VS D).hT (h a) (F₂.fvec b) = (VS D).hT (f a) (f₁ b) := by
    intro a b
    rw [← (LinearMap.isSymm_def.1 (VS D).herm) (F₂.fvec b) (h a), hZ3e, starRingEnd_apply,
      Matrix.conjTranspose_apply, star_star]
    rfl
  have k3 : ∀ a b, (VS D).hT (F₂.fvec a) (h b) = (VS D).hT (f₁ a) (f b) := by
    intro a b
    rw [hZ3e, Matrix.conjTranspose_apply, ← starRingEnd_apply]
    exact (LinearMap.isSymm_def.1 (VS D).herm) (f b) (f₁ a)
  have k4 : ∀ a b, (VS D).hT (F₂.fvec a) (F₂.fvec b) = (VS D).hT (f₁ a) (f₁ b) := by
    intro a b
    by_cases hab : a ≠ Fin.last D.R.rS ∨ b ≠ Fin.last D.R.rS
    · exact (FsLA.gram_fvec_zero F₂ a b hab).trans (hf1a a b hab).symm
    · push_neg at hab
      rw [hab.1, hab.2]
      exact (FsLA.gram_fvec_last F₂).trans hf1b.symm
  have hGr : FsLA.gram (VS D) uu' uu' = FsLA.gram (VS D) uu uu := by
    refine Matrix.ext fun i j => ?_
    rcases i with a | a <;> rcases j with b | b
    · exact k1 a b
    · exact k2 a b
    · exact k3 a b
    · exact k4 a b
  have hdet : (FsLA.gram (VS D) uu uu).det ≠ 0 :=
    FsLA.gram_pair_det F0 f₁ hf1a hf1b hZ₁d (starG_ne γ w hγ)
  have hsp : ∀ i, uu' i ∈ Submodule.span D.host.E (Set.range uu) := by
    have hsub : Set.range (Sum.elim F₂.fvec f) ⊆ Submodule.span D.host.E (Set.range uu) := by
      rintro _ ⟨k, rfl⟩
      rcases k with b | a
      · exact hU b
      · exact Submodule.subset_span ⟨Sum.inl a, rfl⟩
    intro i
    rcases i with a | b
    · exact Submodule.span_le.2 hsub (hsp3 a)
    · exact hU b
  obtain ⟨g, hiso, hgu, -, hform⟩ := FsLA.isom_ext uu uu' hGr hdet hsp
  refine ⟨g, fun k => ∑ m, (FsLA.gram (VS D) uu uu)⁻¹ m k • (uu' m - uu m), hiso, fun b => hgu (Sum.inr b),
    hform, ?_⟩

  have homf : FsLA.om (VS D) F₂.fvec f = starOmL f (frame F'₂) := by
    rw [FsLA.om, hg2, ← Matrix.adjugate_conjTranspose]
    simp only [starOmL, Matrix.conjTranspose_apply]
    rw [← hZ]
    rfl
  have homh : FsLA.om (VS D) F₂.fvec h = g (starOmL f f₁) := by

    simp only [FsLA.om, starOmL, map_sum, map_smul]
    have e : FsLA.gram (VS D) h F₂.fvec = Z₁ᴴ := hZ3
    rw [e]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Matrix.adjugate_conjTranspose, Matrix.conjTranspose_apply]
    congr 1
    exact (hgu (Sum.inl a)).symm
  have e1 : Z₁ᴴ.det = star Z₁.det := Matrix.det_conjTranspose _
  have e2 : (FsLA.gram (VS D) f F₂.fvec).det = star Z.det := by rw [hg2, Matrix.det_conjTranspose]
  rw [e1, e2, homf, homh] at hom3
  exact hom3

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

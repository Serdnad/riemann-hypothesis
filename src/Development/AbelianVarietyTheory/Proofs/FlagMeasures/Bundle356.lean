module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle017
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsInvLower
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle340
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle032
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle050
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellBru
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellFin
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellGeo
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle002
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagFramesSameGradedDefinitePartLatticeEq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfA
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle146
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle004
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalTermWeightEqCharacterMulInv
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq

@[expose] public section

section

noncomputable section

namespace GlobalTheory.TypeAsm.NFEx

section Mat
variable {K : Type} [Field K] [StarRing K]


open Classical in
noncomputable def cb (b : K × ℕ) : Kˣ × ℕ+ :=
  if h : b.1 ≠ 0 ∧ 1 ≤ b.2 then (Units.mk0 (star b.1) (star_ne_zero.2 h.1), ⟨b.2, h.2⟩) else (1, 1)

theorem entry_cb (bs : List (K × ℕ)) (hb : ∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) (a c : ℕ) :
    Formalism.MainNotions.S.Loc.ptEntryL (bs.map cb) a c = star (Formalism.MainNotions.S.ptEntry bs a c) := by
  induction bs generalizing a c with
  | nil => simp [Formalism.MainNotions.S.Loc.ptEntryL, Formalism.MainNotions.S.ptEntry]
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    have h := hb (t, s) (by simp)
    have ih' := ih (fun b hb' => hb b (by simp [hb']))
    simp only [List.map_cons, cb, dif_pos h, Formalism.MainNotions.S.Loc.ptEntryL, Formalism.MainNotions.S.ptEntry, PNat.mk_coe, Units.val_mk0]
    simp only [ih', apply_ite star, star_zero]
    exact if_congr Iff.rfl (if_congr Iff.rfl rfl rfl) (if_congr Iff.rfl rfl rfl)

theorem size_cb (bs : List (K × ℕ)) (hb : ∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) :
    ((bs.map cb).map (fun b => (b.2 : ℕ))).sum = (bs.map Prod.snd).sum := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    have h := hb b (by simp)
    have ih' := ih (fun b hb' => hb b (by simp [hb']))
    simp only [List.map_cons, List.sum_cons, cb, dif_pos h, PNat.mk_coe, ih']

end Mat
end GlobalTheory.TypeAsm.NFEx

namespace GlobalTheory.TypeAsm.NFEx
section Mat2
variable {K : Type} [Field K] [StarRing K]

noncomputable def toPt {n : ℕ} (p : Formalism.MainNotions.S.Point K n) : Formalism.MainNotions.S.Loc.Pt K n where
  blocks := p.1.map cb
  size := (size_cb p.1 p.2.1).trans p.2.2

theorem toPt_mat {n : ℕ} (p : Formalism.MainNotions.S.Point K n) (a b : Fin n) :
    (toPt p).mat a b = star (Formalism.MainNotions.S.ptMat p a b) :=
  entry_cb p.1 p.2.1 a.val b.val

def sgnR (r : ℕ) {n : ℕ} (b : Fin n) : ℤˣ := (-1) ^ (r - b.val)

theorem decomp {n r : ℕ} (Z : Matrix (Fin n) (Fin n) K) (p : Formalism.MainNotions.S.Point K n)
    (h : Formalism.MainNotions.S.IsInCell (fun a b => (-1 : K) ^ (r - b.val) * Z a b) p) :
    ∃ A B : Matrix (Fin n) (Fin n) K, (∀ a b, a < b → A a b = 0 ∧ B b a = 0) ∧ (∀ a, A a a = 1 ∧ B a a = 1) ∧
      Z.map star = A * Matrix.of (fun a b => (toPt p).mat a b * (((sgnR r b : ℤˣ) : ℤ) : K)) * B := by
  obtain ⟨L, U, hL, hU, hZ⟩ := h
  set s : Fin n → K := fun b => (-1 : K) ^ (r - b.val) with hs_def
  have hs : ∀ b, s b * s b = 1 := fun b => by
    simp only [hs_def, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  have hss : ∀ b, star (s b) = s b := fun b => by simp [hs_def]
  have hsg : ∀ b : Fin n, (((sgnR r b : ℤˣ) : ℤ) : K) = s b := fun b => by
    simp [sgnR, hs_def]
  have hZ' : Z = L * Formalism.MainNotions.S.ptMat p * U * Matrix.diagonal s := by
    ext a b
    rw [Matrix.mul_diagonal, ← hZ]
    show Z a b = s b * Z a b * s b
    rw [mul_comm (s b), mul_assoc, hs, mul_one]
  have hD : Matrix.diagonal s * Matrix.diagonal s = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    ext a b
    by_cases hab : a = b
    · subst hab; simp [hs]
    · simp [Matrix.diagonal_apply_ne _ hab, Matrix.one_apply_ne hab]
  have hDs : (Matrix.diagonal s).map star = Matrix.diagonal s := by
    ext a b
    by_cases hab : a = b
    · subst hab; simp [hss]
    · simp [Matrix.diagonal_apply_ne _ hab]
  refine ⟨L.map star, Matrix.diagonal s * U.map star * Matrix.diagonal s, fun a b hab => ⟨?_, ?_⟩, fun a => ⟨?_, ?_⟩, ?_⟩
  · simp [(hL a b).1 hab]
  · rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp [(hU b a).1 hab]
  · simp [(hL a a).2 rfl]
  · rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp [(hU a a).2 rfl, hs]
  · have hP : Matrix.of (fun a b => (toPt p).mat a b * (((sgnR r b : ℤˣ) : ℤ) : K)) =
        (Formalism.MainNotions.S.ptMat p).map star * Matrix.diagonal s := by
      ext a b
      rw [Matrix.mul_diagonal, Matrix.of_apply, toPt_mat, hsg, Matrix.map_apply]
    have hmap : ∀ M N : Matrix (Fin n) (Fin n) K, (M * N).map star = M.map star * N.map star := fun M N =>
      (Matrix.map_mul (f := starRingEnd K) (L := M) (M := N))
    rw [hP, hZ', hmap, hmap, hmap, hDs]
    calc L.map star * (Formalism.MainNotions.S.ptMat p).map star * U.map star * Matrix.diagonal s
        = L.map star * (Formalism.MainNotions.S.ptMat p).map star * (Matrix.diagonal s * Matrix.diagonal s) * U.map star *
            Matrix.diagonal s := by rw [hD, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]

end Mat2
end GlobalTheory.TypeAsm.NFEx

namespace GlobalTheory.TypeAsm.NFEx
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.MainNotions.S.Cnt
  Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LatticeGluingRadicals

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem zhat_eq {D : D7} {X : HidaSetting D} {Y : Full X} {u : D.what₂.Word} (t : GTu Y u)
    (j : ℕ) (hj : j ≤ D.R.rS + 1) :
    (Formalism.HermitianLatticeCounting.S6.Zhat (F0 X u) (Ft t)).submatrix (Fin.castLE hj) (Fin.castLE hj) =
      ((Formalism.MainNotions.S.Zhat (lf D (X.Fu u)).fl (frq X t.rep).fl).submatrix (Fin.castLE hj) (Fin.castLE hj)).map (star : D.host.E → D.host.E) := by
  refine Matrix.ext fun a b => ?_
  exact a_herm (S := VS D) ((F0 X u).e (Fin.castLE hj a)) ((Ft t).e (Fin.castLE hj b))

end GlobalTheory.TypeAsm.NFEx

namespace GlobalTheory.TypeAsm.NFEx
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.MainNotions.S.Cnt
  Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LatticeGluingRadicals

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem nfExC (hHost : HostC) : NFExC := by
  intro D large₂ X Y u hStd t ht
  obtain ⟨hr, hG, -⟩ := relevantSet_zeroG_not_identity ht
  obtain ⟨j, hj, c, hN⟩ := exists_nfFull_of_relevant_of_G_eq_zero Y t hr hG
  have hjT := index_eq_normalForm t hN
  have hH := hHost D large₂ hStd
  obtain ⟨hrel, -⟩ := relRepC D X Y u u t hr hG
  have hTu := tie_Tu_pos D u
  have hj' : j ≤ D.R.rS + 1 := hj.trans (Nat.le_succ _)
  have geo := cell_geom D.host.F D.host.E (hS D) D.R.rS _ _ (lf D (X.Fu u)).fl (frq X t.rep).fl (tie_trace D.sp.cm)
    (tie_aniso D _ hTu (lf D (X.Fu u))) (tie_aniso D _ hTu (frq X t.rep)) hrel
  have hDG : Formalism.MainNotions.S.Dl (lf D (X.Fu u)).fl (frq X t.rep).fl j ≠ 0 := by
    exact (nf_Dl (lf D (X.Fu u)).fl (frq X t.rep).fl
      (fixedFlag_level_ne_zero D u) (nf_T_ne D u) j hj').trans_ne (star_ne_zero.2 hN.2.2.1)
  obtain ⟨p, hp⟩ := cell_of_matRel cell_inv cell_sign cell_bruhat cell_mono cell_point hj'
    ((Formalism.MainNotions.S.Zhat (lf D (X.Fu u)).fl (frq X t.rep).fl).submatrix (Fin.castLE hj') (Fin.castLE hj'))
    (by rw [← tie_Dl_eq']; exact hDG) (geo j hj' (Or.inl ⟨hj, hDG⟩))
  obtain ⟨A, B, h0, h1, hZ⟩ := decomp _ p hp
  obtain ⟨N, hNj, -, hNT, hN𝔡, hF, hF'⟩ := GlobalTheory.DegCnt.RatNormal.exists_nf D.host.E (VS D).V (HV D) hH.1 D.R.rS
    (F0 X u) (Ft t) j hj c (Tu D u) (dI D) (toPt p) (fun b => sgnR D.R.rS b) A B hN rfl rfl
    (fun σ => nf_pos _ _ (p_posX D _ hTu _) σ) hH.2.2.2.2.2.2.2.1 hH.2.2.2.2.2.2.2.2.1 h0 h1
    (by rw [zhat_eq t j hj']; exact hZ)
  exact ⟨N, ⟨hN𝔡, hF, hF'⟩, hNj.trans hjT.symm, hNT⟩

end GlobalTheory.TypeAsm.NFEx

theorem GlobalTheory.TypeAsm.nfExC_holds : GlobalTheory.TypeAsm.NFExC := GlobalTheory.TypeAsm.NFEx.nfExC GlobalTheory.T.unitaryHostFieldArithmeticConditions
end
end

section

noncomputable section
open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc
namespace GlobalTheory.TypeAsm.HasLabelling
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem frameExp_cast (r l : ℕ) (hl : l ≤ r + 1) :
    ((frameExp r l : ℕ) : ℤ) = ∑ a ∈ Finset.range l, ((r : ℤ) - a) := by
  induction l with
  | zero => simp [frameExp]
  | succ l ih =>
    have h1 : frameExp r (l + 1) = frameExp r l + (r + 1 - (l + 1)) := by
      unfold frameExp
      rw [Finset.sum_Icc_succ_top (by omega)]
    have h2 : ((r + 1 - (l + 1) : ℕ) : ℤ) = (r : ℤ) - l := by omega
    rw [h1, Nat.cast_add, ih (by omega), Finset.sum_range_succ, h2]

theorem nloc_eq (D : D7) (r l : ℕ) (x : D.host.E) :
    ((Nloc (ddS D) r l x : ℚ) : ℝ) =
      |((Algebra.norm ℚ x : ℚ) : ℝ)| * (Ideal.absNorm (dI D) : ℝ) ^ (-(2 * (frameExp r l : ℤ))) := by
  unfold Nloc
  rw [map_mul, FractionalIdeal.absNorm_span_singleton (𝓞 D.host.E), map_zpow₀,
    show ddS D = ((dI D : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) from rfl,
    FractionalIdeal.coeIdeal_absNorm]
  push_cast
  rfl

theorem norm_star (D : D7) (x : D.host.E) : Algebra.norm ℚ (star x) = Algebra.norm ℚ x := by
  have := Algebra.norm_eq_of_algEquiv ((starRingAut : D.host.E ≃+* D.host.E).toRatAlgEquiv) x
  simpa using this

theorem nloc_ne_zero (D : D7) (hd : dI D ≠ ⊥) (r l : ℕ) (x : D.host.E) :
    ((Nloc (ddS D) r l x : ℚ) : ℝ) ≠ 0 ↔ x ≠ 0 := by
  have hA : (Ideal.absNorm (dI D) : ℝ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 hd)
  rw [nloc_eq, mul_ne_zero_iff, abs_ne_zero, Rat.cast_ne_zero, Algebra.norm_ne_zero_iff]
  simp only [ne_eq, zpow_neg, inv_eq_zero, and_iff_left_iff_imp]
  intro _
  exact zpow_ne_zero _ hA

theorem T_eq {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ}
    (F G : Formalism.HermitianLatticeCounting.S6.FlagD H r) (h : G.e (Fin.last r) - F.e (Fin.last r) ∈ F.X) : G.T = F.T := by
  have hX : ∀ w : V, (∀ a : Fin r, H.B (F.e a.castSucc) w = 0) → ∀ y ∈ F.X, H.B y w = 0 := by
    intro w hw y hy
    have hle : F.X ≤ LinearMap.ker (H.B.flip w) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨b, -, rfl⟩
      simpa using hw b
    simpa using hle hy
  set x := G.e (Fin.last r) - F.e (Fin.last r) with hxdef
  have hxz : H.B x (F.e (Fin.last r)) = 0 := hX _ F.zperp x h
  have hzx : H.B (F.e (Fin.last r)) x = 0 := by rw [← H.herm, hxz, star_zero]
  have hxx : H.B x x = 0 := by
    refine hX x (fun a => ?_) x h
    have := hX (F.e a.castSucc) (fun b => F.iso b a) x h
    rw [← H.herm, this, star_zero]
  have hG : G.e (Fin.last r) = F.e (Fin.last r) + x := by rw [hxdef]; abel
  have h1 := G.zz
  rw [hG] at h1
  simp only [map_add (f := _), LinearMap.add_apply, hxz, hzx, hxx, F.zz, add_zero] at h1
  exact (neg_inj.1 h1).symm

end GlobalTheory.TypeAsm.HasLabelling

namespace GlobalTheory.TypeAsm
open GlobalTheory.TypeAsm.HasLabelling
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem labC : LabC := by
  intro D large₂ X Y u hS t N hN
  have hK : Formalism.HermitianLatticesTheory.IsCMUnram D.host.E := by
    obtain ⟨C', Cl, Cg, cb, Cw, cT, CT, C0, hH⟩ := hS
    exact hH.2.2.2.2.2.2.2
  obtain ⟨-, -, -, -, hj, hDl, -, -, -⟩ :=
    GlobalTheory.DegAsm.adapt_invariants D.host.E (VS D).V (HV D) hK D.R.rS (F0 X u) (Ft t) (dI D) N hN
  have hII : Formalism.HermitianLatticeCounting.S6.II (F0 X u) (Ft t) = Isp (lf D (X.Fu u)).fl (frq X t.rep).fl := nf_II _ _ _ _
  have hjT : N.j = jT t := by rw [hj, hII]; rfl
  have hjle : jT t ≤ D.R.rS := by unfold jT; omega
  have hnf : ∀ (l : ℕ) (hl : l ≤ D.R.rS + 1),
      Dl (lf D (X.Fu u)).fl (frq X t.rep).fl l = star (Formalism.HermitianLatticeCounting.S6.Dl (F0 X u) (Ft t) l hl) :=
    fun l hl => nf_Dl _ _ _ _ l hl
  have hd : N.𝔡 = dI D := hN.1
  have hdne : dI D ≠ ⊥ := hd ▸ N.𝔡_ne
  have key : ∀ l, l ≤ jT t → N.nD l = ((Nloc (ddS D) D.R.rS l (labT t l) : ℚ) : ℝ) := by
    intro l hl
    have hl' : l ≤ D.R.rS + 1 := by omega
    have hlab : labT t l = star (Formalism.HermitianLatticeCounting.S6.Dl (F0 X u) (Ft t) l hl') := by
      simp only [labT, if_pos hl]
      exact hnf l hl'
    unfold GlobalTheory.DegCnt.NF.nD
    rw [dite_eq_left hl', hDl l hl', nloc_eq, hlab, norm_star, hd, frameExp_cast _ _ hl']
  refine ⟨hjT, ?_, ?_, ?_, ?_⟩
  · have hz : N.F.e (Fin.last D.R.rS) - (F0 X u).e (Fin.last D.R.rS) ∈ (F0 X u).X := hN.2.1 (Fin.last _)
    have h1 : ((N.T : ℕ) : D.host.E) = ((Tu D u : ℕ) : D.host.E) := by
      rw [← N.hT, T_eq (F0 X u) N.F hz]
      rfl
    exact_mod_cast h1
  · unfold GlobalTheory.DegCnt.NF.Del
    rw [hjT, key _ le_rfl]
    rfl
  · unfold GlobalTheory.DegCnt.NF.Db DbL
    rw [hjT]
    have hset : (Finset.Icc 1 (jT t)).filter (fun l => N.nD l ≠ 0) = k2ends D (jT t) (labT t) := by
      ext l
      simp only [k2ends, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨⟨h1, h2⟩, ?_⟩
        rw [key l h2] at h3
        exact (nloc_ne_zero D hdne _ _ _).1 h3
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨⟨h1, h2⟩, ?_⟩
        rw [key l h2]
        exact (nloc_ne_zero D hdne _ _ _).2 h3
    rw [hset]
    refine Finset.prod_congr rfl fun l hl => ?_
    have h2 : l ≤ jT t := by
      simp only [k2ends, Finset.mem_filter, Finset.mem_Icc] at hl
      exact hl.1.2
    exact key l h2
  · funext l
    unfold GlobalTheory.DegAsm.lab
    by_cases hl : l ≤ jT t
    · have hl' : l ≤ D.R.rS + 1 := by omega
      rw [dite_eq_left ⟨hl, hl'⟩]
      simp only [labT, if_pos hl]
      rw [hnf l hl', star_star]
    · rw [dite_eq_right (fun h => hl h.1)]
      simp only [labT, if_neg hl, star_zero]

end GlobalTheory.TypeAsm
end
end

section

open scoped Classical ENNReal Pointwise
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Sloc.AdaptExpand

variable {D : D7}

theorem frame_castSucc {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (i : Fin D.R.rS) :
    frame F (Fin.castSucc i) = F.fl.e i := by
  simp [frame, Formalism.MainNotions.S.FlagG.fvec]

theorem exists_coeff {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (b : Fin (D.R.rS + 1)) (x : (VS D).V)
    (hx : x ∈ Xflag F b.val) :
    ∃ l : Fin D.R.rS → D.host.E, (∀ i, b.val ≤ i.val → l i = 0) ∧ x = ∑ i, l i • F.fl.e i := by
  have hx' : x ∈ Submodule.span D.host.E (F.fl.e '' {i | i.1 < b.val}) := hx
  rw [Finsupp.mem_span_image_iff_linearCombination] at hx'
  obtain ⟨l, hl, rfl⟩ := hx'
  refine ⟨l, fun i hi => ?_, ?_⟩
  · by_contra h
    have := hl (Finsupp.mem_support_iff.2 h)
    simp only [Set.mem_setOf_eq] at this
    omega
  · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    intro i; simp

theorem exists_coeff_frame {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (b : Fin (D.R.rS + 1)) (x : (VS D).V)
    (hx : x ∈ Xflag F b.val) :
    ∃ u : Fin (D.R.rS + 1) → D.host.E, (∀ c, b ≤ c → u c = 0) ∧ x = ∑ c, u c • frame F c := by
  obtain ⟨l, hl, rfl⟩ := exists_coeff F b x hx
  refine ⟨Fin.snoc (α := fun _ => D.host.E) l 0, fun c hc => ?_, ?_⟩
  · induction c using Fin.lastCases with
    | last => simp
    | cast i =>
      simp only [Fin.snoc_castSucc]
      exact hl i (by simpa [Fin.le_def] using hc)
  · rw [Fin.sum_univ_castSucc]
    simp [frame_castSucc]

theorem adapt_expand : ∀ (D : D7) {T : D.host.E} (F0 F : LFlag (D.sp.Y 0) D.R.rS T) (g : GV D), Adapt g F0 F → ∀ (Z : LocDat D) (p : PlF D) (Af : Fin (D.R.rS + 1) → Vp D p), Af = (fun a => frFac Z.δ p a • baseChange₂ D p (frame F a)) → ∃ B : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep, (∀ a b, b < a → B a b = 0) ∧ (∀ a, B a a = Ring.inverse (frFac Z.δ p a)) ∧ ∀ b, baseChange₂ D p (g (frame F0 b)) = ∑ a, B a b • Af a := by
  intro D T F0 F g hg Z p Af hAf
  subst hAf
  have hu := fun c => Formalism.L2.SG.Pf.ScalarFramePf.isUnit_frFac Z p c
  choose u hu0 hux using fun b => exists_coeff_frame F b _ (hg.2 b)
  refine ⟨fun a b => ((D.s.atP p).ιE (u b a) + if a = b then 1 else 0) * Ring.inverse (frFac Z.δ p a),
    fun a b hab => ?_, fun a => ?_, fun b => ?_⟩
  · simp [hu0 b a hab.le, (ne_of_lt hab).symm]
  · simp [hu0 a a le_rfl]
  · have e1 : g (frame F0 b) = frame F b + ∑ c, u b c • frame F c := by
      rw [← hux b]; abel

    rw [e1, map_add (f := _), map_sum]
    simp only [baseChange_smul₂]
    have e2 : ∀ a, (((D.s.atP p).ιE (u b a) + if a = b then 1 else 0) * Ring.inverse (frFac Z.δ p a)) •
        (frFac Z.δ p a • baseChange₂ D p (frame F a)) =
        (D.s.atP p).ιE (u b a) • baseChange₂ D p (frame F a) + if a = b then baseChange₂ D p (frame F a) else 0 := by
      intro a
      rw [smul_smul, mul_assoc, Ring.inverse_mul_cancel _ (hu a), mul_one, add_smul]
      split_ifs <;> simp
    simp only [e2, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    abel

end GlobalTheory.Sloc.AdaptExpand
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

open Formalism.MainNotions.BridgeLemma IsDedekindDomain

namespace GlobalTheory.RowLev.FixedChoice

theorem isChoice_wB_plGw : ∀ (D : D7) (X : HidaSetting D), GlobalTheory.RowLev.IsChoice X.B.I D.host.g D.nd.PlG (fun k v => Formalism.L2.SG.Pf.RowDictPf.wB X (D.naut.plGw k v)) := by
  intro D X
  let e : 𝓞 X.B.I.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv X.ιE
  have he : ∀ a : 𝓞 X.B.I.E, ((e a : 𝓞 D.host.E) : D.host.E) = X.ιE (a : X.B.I.E) := fun a => rfl
  have hnat : ∀ m : ℕ, e (m : 𝓞 X.B.I.E) = (m : 𝓞 D.host.E) := fun m => map_natCast e m
  have hmemB : ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (a : 𝓞 X.B.I.E),
      a ∈ (Formalism.L2.SG.Pf.RowDictPf.wB X w).asIdeal ↔ e a ∈ w.asIdeal := fun w a => Iff.rfl

  have hspl : ∀ k, SplitsCompl D.host.E (D.host.g k) := by
    intro k
    have hp := D.host.g_prime k
    have := span_isMaximal hp
    apply splitsCompl_of_ncard _ _ hp
    rw [← IsDedekindDomain.coe_primesOverFinset (span_ne_bot hp) (𝓞 D.host.E), ← image_plOver _ hp,
      (injOn_asIdeal _ _).ncard_image]
    exact D.nd.g_split k
  have hsp : ∀ k (P : Ideal (𝓞 X.B.I.E)), P.IsMaximal → ((D.host.g k : ℕ) : 𝓞 X.B.I.E) ∈ P →
      Ideal.absNorm P = D.host.g k ∧ ((D.host.g k : ℕ) : 𝓞 X.B.I.E) ∉ P ^ 2 := by
    intro k P hP hg
    have hQ : (P.map e).IsMaximal := Ideal.map_isMaximal_of_equiv e
    have hgQ : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.map e := by
      rw [← hnat]; exact Ideal.mem_map_of_mem _ hg
    obtain ⟨h1, h2⟩ := hspl k _ hQ hgQ
    refine ⟨?_, fun h => h2 ?_⟩
    · rw [← h1, Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
      exact Nat.card_congr (Ideal.quotientEquiv P (P.map e) e rfl).toEquiv
    · rw [← hnat, ← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ h
  have hf : X.B.I.f = D.R.f := Formalism.L2.SG.Pf.RowDictPf.f_eq X
  refine (GlobalTheory.SplitChoice.exists_isChoice_and_isChoice_of_card X.B.I D.host.g D.host.g_prime D.host.g_ne hsp).2
    D.nd.PlG _ (fun k => by rw [hf]; convert D.nd.card_PlG k) (fun k v => ?_) (fun k => ?_) (fun k v v' hc => ?_)
  · rw [hmemB, hnat]; exact D.naut.plGw_over k v
  · intro v v' h
    simp only at h
    apply D.naut.plGw_inj k
    apply HeightOneSpectrum.ext
    have h1 : ∀ w : HeightOneSpectrum (𝓞 D.host.E), (Formalism.L2.SG.Pf.RowDictPf.wB X w).asIdeal.map e = w.asIdeal :=
      fun w => Ideal.map_comap_of_surjective _ e.surjective w.asIdeal
    rw [← h1, ← h1 (D.naut.plGw k v'), h]
  · apply D.naut.plGw_nconj k v v'
    intro x y hxy
    have hst : ((e.symm y : 𝓞 X.B.I.E) : X.B.I.E) = star ((e.symm x : 𝓞 X.B.I.E) : X.B.I.E) := by
      apply X.ιE.injective
      rw [X.ιE_conj, ← he, ← he, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, hxy]
    have := hc (e.symm x) (e.symm y) hst
    rwa [hmemB, hmemB, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply] at this

end GlobalTheory.RowLev.FixedChoice
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.localTermWeight_eq_character_mul_inv : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E) {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (r k : ℕ) (P : LocNG.FPair H r) (S : Frames M.L r k) (c : WCoord P S) (d : LocNG.Datum P) (t : Loc.Term V M r), LocNG.IsTermOver P d t → ∀ m m' : S.GLV, (∀ b, c.e (t.f b) = m (S.f b)) → (∀ b, c.e (t.f' b) = m' (S.f' b)) → LocNG.om P t = S.psi m * (S.psi' m')⁻¹ := by
  first | exact @GlobalTheory.HL.TermPhase.om_eq_psi_mul_inv | exact GlobalTheory.HL.TermPhase.om_eq_psi_mul_inv | (intros; apply GlobalTheory.HL.TermPhase.om_eq_psi_mul_inv <;> assumption)
end

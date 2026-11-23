module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle007
public import Development.AutomorphicArithmetic.PrimeDiscriminants.Bundle003
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle072
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MaxVSpanSingleton
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Counterexamples.PlaceInjectivity.StandardDeterminantUnits
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle011
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

noncomputable section

namespace GlobalTheory.EX


open Classical in
def cutScale {eps x1 la y : ℝ} (S : Scales la) (h0 : 0 < eps) (h1 : eps < 1 / 52) (hx : 1 < x1) (hy : x1 ≤ y) (x : ℝ) : Scale :=
  S.scale (if x1 < x ∧ x ∈ S.Win then x else y) eps (by split_ifs with h; exacts [hx.trans h.1, hx.trans_le hy]) h0 h1

private theorem cutScale_alt {eps x1 la y : ℝ} (S : Scales la) (h0 : 0 < eps) (h1 : eps < 1 / 52) (hx : 1 < x1) (hy : x1 ≤ y)
    (x : ℝ) (h : x1 < x) (hw : x ∈ S.Win) : (cutScale S h0 h1 hx hy x).x = x := if_pos ⟨h, hw⟩

private theorem cutScale_ge {eps x1 la y : ℝ} (S : Scales la) (h0 : 0 < eps) (h1 : eps < 1 / 52) (hx : 1 < x1) (hy : x1 ≤ y)
    (x : ℝ) : x1 ≤ (cutScale S h0 h1 hx hy x).x := by
  unfold cutScale Scales.scale
  dsimp only
  split_ifs with h
  exacts [h.1.le, hy]

private theorem cutScale_mem {eps x1 la y : ℝ} (S : Scales la) (h0 : 0 < eps) (h1 : eps < 1 / 52) (hx : 1 < x1) (hy : x1 ≤ y)
    (hw : y ∈ S.Win) (x : ℝ) : S.Mem (cutScale S h0 h1 hx hy x) := by
  refine ⟨rfl, ?_⟩
  unfold cutScale Scales.scale
  dsimp only
  split_ifs with h
  exacts [h.2, hw]

theorem Kit.bTopOf_eq {C : FC} {cD ch : ℝ} {s : Scale} (k : Kit C cD ch s) (i i' : k.Ix) :
    bTopOf (k.pt i).L = bTopOf (k.pt i').L := by
  unfold bTopOf
  rw [(k.val i).La_eq, (k.val i').La_eq, k.sc_eq i, k.sc_eq i', (k.same i i').1]

theorem bTopOf_ge {D : D7} (L : SizeData₂ D) (h : L.sc.x ^ L.sc.eps ≤ L.LaG) :
    L.sc.b' + 2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ (2 * L.sc.eps) * L.sc.b' / (D.R.k : ℝ) ≤ bTopOf L := by
  have hsx : (0 : ℝ) < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  have hb : 0 ≤ L.sc.b' := by
    unfold Scale.b' Scale.a Scale.b Scale.X'
    positivity
  have hd : 0 ≤ L.sc.delta1 := by
    unfold Scale.delta1
    positivity
  have e : L.sc.x ^ (2 * L.sc.eps) = L.sc.x ^ L.sc.eps * L.sc.x ^ L.sc.eps := by
    rw [two_mul, Real.rpow_add hsx]
  unfold bTopOf
  rw [e, ← mul_assoc]
  gcongr

def famOfKits {eps : ℝ} (C : FC) (cD ch x1 : ℝ) (hx1 : 1 < x1) (hS : Std C) (hG : C.GK.Nonneg)
    (J : ℝ) (Wn : Set ℝ) (hW : ∀ y : ℝ, ∃ x ∈ Wn, y ≤ x)
    (s : ℝ → Scale) (he : ∀ x, (s x).eps = eps) (hJ : ∀ x, (s x).J = J) (hs : ∀ x, x1 < x → x ∈ Wn → (s x).x = x)
    (k : ∀ x, Kit C cD ch (s x)) (nu : ∀ x i, NumAt C ((k x).pt i).L) : FamP eps where
  x1 := x1
  one_lt_family_threshold := hx1
  Ix x := {_i : (k x).Ix // x ≤ x1 ∨ x ∈ Wn}
  Win := Wn
  Win_unb := hW
  Ix_win x hx := ⟨⟨(k x).ne.some, Or.inr hx⟩⟩
  Ix_zero := ⟨⟨(k 0).ne.some, Or.inl (zero_le_one.trans hx1.le)⟩⟩
  D x i := ((k x).pt i.1).D
  L x i := ((k x).pt i.1).L
  L_x x i hx := by rw [(k x).sc_eq i.1, hs x hx (i.2.resolve_left hx.not_ge)]
  L_eps x i := by rw [(k x).sc_eq i.1, he x]
  J := J
  L_J x i := by rw [(k x).sc_eq i.1, hJ x]
  R_eq x i i' := ((k x).same i.1 i'.1).1
  TTn x := ((k x).pt (k x).ne.some).D.host.TT.image Formalism.HC.Frame.A.val
  TT_eq x i := ((k x).same i.1 _).2.1
  realisedChain_torus_eq x i i' := ((k x).same i.1 i'.1).2.2.1
  q_eq x i i' := ((k x).same i.1 i'.1).2.2.2.1
  d_eq x i i' := ((k x).same i.1 i'.1).2.2.2.2.1
  QS_eq x i i' := ((k x).same i.1 i'.1).QS_eq
  art_eq x i i' := ((k x).same i.1 i'.1).art_eq
  rd_eq x i i' := ((k x).same i.1 i'.1).rd_eq
  Co := C.P.Cpde
  o_le_Co x i _ := ((k x).val i.1).host.o_le
  QS_le_Co x i _ := ((k x).val i.1).host.QS_le
  g_eq x i i' := ((k x).same i.1 i'.1).2.2.2.2.2.1
  pde_eq x i i' := ⟨((k x).same i.1 i'.1).2.2.2.2.2.2.1, ((k x).same i.1 i'.1).2.2.2.2.2.2.2.1⟩
  W x := (k x).W
  eW x i := (k x).eW i.1
  eW_code x i i' := (k x).eW_code i.1 i'.1
  CGam := C.CGam
  CGam_eq x i := (nu x i.1).CGam_eq
  Cc := C.Cc
  Cc_eq x i := (nu x i.1).Cc_eq
  Ct := C.Ct
  Ct_eq x i := (nu x i.1).Ct_eq
  CT2 := C.CT2
  secondConstant_eq x i := (nu x i.1).secondConstant_eq
  bTop x := bTopOf ((k x).pt (k x).ne.some).L
  bTop_eq x hx i := by
    rw [(k x).bTopOf_eq _ i.1]
    unfold bTopOf
    rw [show ((k x).pt i.1).L.sc.x = x by rw [(k x).sc_eq i.1, hs x hx (i.2.resolve_left hx.not_ge)],
      show ((k x).pt i.1).L.sc.eps = eps by rw [(k x).sc_eq i.1, he x]]
  bTop_ge x hx i := by
    rw [(k x).bTopOf_eq _ i.1]
    have h := bTopOf_ge _ (nu x i.1).LaG_ge
    rwa [show ((k x).pt i.1).L.sc.x = x by rw [(k x).sc_eq i.1, hs x hx (i.2.resolve_left hx.not_ge)],
      show ((k x).pt i.1).L.sc.eps = eps by rw [(k x).sc_eq i.1, he x]] at h
  bT_le x _ i t := by
    rw [(k x).bTopOf_eq _ i.1]
    exact (nu x i.1).bT_le t
  coverS x _ i0 u0 hu := by
    obtain ⟨i, hi⟩ := (k x).cover_weights i0.1 u0 hu
    exact ⟨⟨i, i0.2⟩, hi⟩
  params x _ i := (nu x i.1).params
  PK := C.PK
  params_K x _ i := (nu x i.1).params_K
  parT x _ i := (nu x i.1).parT
  PT := C.PT
  parT_K x _ i := (nu x i.1).parT_K
  CTu := C.CTu
  sizes x _ i := (nu x i.1).sizes
  ties x i := ((k x).pt i.1).xa.ties
  gatT x i := ((k x).pt i.1).gatT
  X x i := ((k x).pt i.1).xa.X
  Gx x i := ((k x).pt i.1).ta.Gx
  Gy x i := ((k x).pt i.1).ta.Gy
  GK := C.GK
  GK_nonneg := hG
  supp_sat x _ i := ((k x).pt i.1).ta.supp_sat
  tw_supp x _ i := ((k x).pt i.1).ta.tw_supp
  fills x _ i := ((k x).pt i.1).ta.fills
  lats0 x _ i := ((k x).pt i.1).ta.lats0
  latTied x _ i := ((k x).pt i.1).ta.latTied
  Csz := C.Csz
  nuDef x _ i := ((k x).pt i.1).xa.nuDef
  nprimeDef x _ i := ((k x).pt i.1).xa.nprimeDef
  rrDef x _ i := ((k x).pt i.1).xa.rrDef
  h_eq x _ i := ((k x).pt i.1).xa.h_eq
  cX := C.cX
  ex x _ i := ((k x).pt i.1).xa.ex
  rho_le x hx i := by
    have h := (nu x i.1).rho_le
    rwa [show ((k x).pt i.1).L.sc.x = x by rw [(k x).sc_eq i.1, hs x hx (i.2.resolve_left hx.not_ge)]] at h
  Cr := C.Cr
  one_le_Cr := hS.1.2.2.2.2.2.2.1.ge
  drop_iff x _ i := ((k x).pt i.1).ta.drop_iff
  fixed := by
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, _⟩ := hS.1
    exact ⟨a1, a2, a3, a4, a5, a6, a7, fun x _ i => ⟨(nu x i.1).CnW_eq.trans a8, (nu x i.1).eP_eq ▸ a9⟩⟩
  eta_eq x i i' := ((k x).same i.1 i'.1).2.2.2.2.2.2.2.2.1
  Sc_shared x i i' := ((k x).same i.1 i'.1).2.2.2.2.2.2.2.2.2.1
  hP_eq x i i' := ((k x).same i.1 i'.1).2.2.2.2.2.2.2.2.2.2.1
  bs_eq x i i' := ((k x).same i.1 i'.1).2.2.2.2.2.2.2.2.2.2.2.1
  off_eq x i i' := ((k x).same i.1 i'.1).2.2.2.2.2.2.2.2.2.2.2.2.1
  kapI_eq x i i' := ((k x).same i.1 i'.1).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  ep_eq x i i' := ((k x).same i.1 i'.1).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem exists_famP_of_kits : ∀ (eps : ℝ) (C : FC) (cD ch x1 la : ℝ) (S : Scales la), 0 < eps → eps < 1 / 52 → 1 < x1 → 1 ≤ la → Std C → C.GK.Nonneg → ∀ k : ∀ s : Scale, s.eps = eps → x1 ≤ s.x → S.Mem s → Kit C cD ch s, (∀ s h h' h'' i, Nonempty (NumAt C ((k s h h' h'').pt i).L)) → ∃ Fm : FamP eps, Fm.x1 = x1 ∧ Fm.cPre = C.cPre ∧ Fm.cOut = C.cOut.set 15 C.P.Cpde ∧ Fm.cMid = C.cMid ∧ Fm.cLast = C.cLast ∧ Fm.CTu = C.CTu ∧ (∀ Q : PtProp, (∀ s h h' h'' i, ((k s h h' h'').pt i).Has Q) → classOf Q Fm) ∧ (∀ Rr : ∀ (D : D7) (L : SizeData₂ D), G.Inst D L → Prop, (∀ s h h' h'' i, Rr ((k s h h' h'').pt i).D ((k s h h' h'').pt i).L ((k s h h' h'').pt i).ta.Gx) → ∀ x, ∀ i : Fm.Ix x, Rr (Fm.D x i) (Fm.L x i) (Fm.Gx x i)) ∧ Fm.J = S.J ∧ Fm.Win = S.Win ∧ Fm.Co = C.P.Cpde := by
  intro eps C cD ch x1 la S h0 h1 hx hla hS hG k hN
  obtain ⟨y, hw, hy⟩ := S.unb hla x1
  have hJ : S.J ≤ C.P.Cpde := by
    have k0 := k (cutScale S h0 h1 hx hy 0) rfl (cutScale_ge S h0 h1 hx hy 0) (cutScale_mem S h0 h1 hx hy hw 0)
    have h := (k0.val k0.ne.some).host.J_le
    rwa [k0.sc_eq] at h
  refine ⟨famOfKits C cD ch x1 hx hS hG S.J S.Win (S.unb hla) (cutScale S h0 h1 hx hy) (fun _ => rfl) (fun _ => rfl)
    (cutScale_alt S h0 h1 hx hy)
    (fun x => k (cutScale S h0 h1 hx hy x) rfl (cutScale_ge S h0 h1 hx hy x) (cutScale_mem S h0 h1 hx hy hw x))
    (fun x i => (hN _ _ _ _ i).some),
    rfl, rfl, ?_, rfl, rfl, rfl, fun Q hQ x _ i => hQ _ _ _ _ i.1, fun Rr hR x i => hR _ _ _ _ i.1, rfl, rfl, rfl⟩
  rw [← congrArg (C.cOut.set 15) (max_eq_left hJ)]
  rfl

end GlobalTheory.EX

end
end

section

noncomputable section

namespace GlobalTheory.LvT

open Formalism.BasicNotions Classical NumberField
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

namespace LocF

variable {q : ℕ} {F : Type} [Field F] {Lc : LocF q F} {n : ℕ}

theorem uext_mem_std (x : Fin n → Lc.K) : x ∈ Lc.std n ↔ ∀ a, x a ∈ Lc.O := by
  simp only [std, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]
  refine forall_congr' fun a => ⟨?_, fun h => ⟨⟨x a, h⟩, rfl⟩⟩
  rintro ⟨y, hy⟩
  rw [← hy]; exact y.2

theorem uext_ker {Λ : Submodule Lc.O (Fin n → Lc.K)} {h : GL (Fin n) Lc.K} (hh : Lc.IsFrame n h Λ)
    {V : Type*} [AddCommGroup V] [Module F V] (hV : Module.finrank F V = n) (π : (Fin n → Lc.K) → V)
    (hadd : ∀ x ∈ Λ, ∀ y ∈ Λ, π (x + y) = π x + π y)
    (hsmul : ∀ (a : Lc.O), ∀ x ∈ Λ, π (a • x) = Lc.res a • π x)
    (hsurj : ∀ y, ∃ x ∈ Λ, π x = y) {x : Fin n → Lc.K} (hx : x ∈ Λ) (h0 : π x = 0) :
    ((q : Lc.K))⁻¹ • x ∈ Λ := by
  let π' : Λ →+ V := AddMonoidHom.mk' (fun x => π x) (fun x y => hadd x x.2 y y.2)
  have hb : ∀ a : Fin n, Matrix.mulVec (h : Matrix (Fin n) (Fin n) Lc.K) (Pi.single a 1) ∈ Λ := by
    intro a
    rw [hh, uext_mem_std]
    intro b
    by_cases hab : b = a
    · subst hab; simp
    · simp [Pi.single_eq_of_ne hab]
  let b : Fin n → Λ := fun a => ⟨_, hb a⟩
  have key : ∀ x ∈ Λ, ∃ z : Fin n → Lc.O,
      x = Matrix.mulVec (h : Matrix (Fin n) (Fin n) Lc.K) (fun a => (z a : Lc.K)) ∧
      π x = ∑ a, Lc.res (z a) • π (b a) := by
    intro x hx
    have e1 : Matrix.mulVec (h : Matrix (Fin n) (Fin n) Lc.K)
        (Matrix.mulVec ((h⁻¹ : GL (Fin n) Lc.K) : Matrix (Fin n) (Fin n) Lc.K) x) = x := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    have e2 := (uext_mem_std _).1 ((hh _).1 (e1.symm ▸ hx))
    let z : Fin n → Lc.O := fun a => ⟨_, e2 a⟩
    have e0 : x = Matrix.mulVec (h : Matrix (Fin n) (Fin n) Lc.K) (fun a => (z a : Lc.K)) := e1.symm
    refine ⟨z, e0, ?_⟩
    have e3 : (⟨x, hx⟩ : Λ) = ∑ a, z a • b a := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      change x = ∑ a, (z a : Lc.K) • Matrix.mulVec (h : Matrix (Fin n) (Fin n) Lc.K) (Pi.single a 1)
      simp only [← Matrix.mulVec_smul]
      rw [← Matrix.mulVec_sum, e0]
      congr 1
      ext c
      simp [Finset.sum_apply, Pi.single_apply]
    have e4 : π x = π' ⟨x, hx⟩ := rfl

    rw [e4, e3, map_sum]
    exact Finset.sum_congr rfl fun a _ => hsmul (z a) _ (b a).2
  have hli : LinearIndependent F (fun a => π (b a)) := by
    apply linearIndependent_of_top_le_span_of_card_eq_finrank
    · intro y _
      obtain ⟨x, hx, rfl⟩ := hsurj y
      obtain ⟨z, -, hz⟩ := key x hx
      rw [hz]
      exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    · simp [hV]
  obtain ⟨z, hz1, hz2⟩ := key x hx
  have hz3 := Fintype.linearIndependent_iff.1 hli (fun a => Lc.res (z a)) (by rw [← hz2, h0])
  rw [hz1, ← Matrix.mulVec_smul, hh, uext_mem_std]
  intro a
  obtain ⟨y, hy⟩ := (Lc.res_ker _).1 (hz3 a)
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hy, ← mul_assoc, inv_mul_cancel₀ Lc.q_ne, one_mul]
  exact y.2

theorem uext_mem_of_ne (p : PP Lc n) {x : Fin n → Lc.K} (hx : p.1.f x = 1) : x ∈ p.1.L := by
  by_contra h
  exact one_ne_zero (hx.symm.trans (p.2.off x h))

theorem uext_sub_mem {p p₁ : PP Lc n} {x y : Fin n → Lc.K} (hx : p.IsUp x p₁) (hy : p.IsUp y p₁) :
    ((q : Lc.K))⁻¹ • (x - y) ∈ p.1.L := by
  have h1 := uext_mem_of_ne p₁ hx.2.2
  have h2 := uext_mem_of_ne p₁ hy.2.2
  have h3 : ((q : Lc.K))⁻¹ • (x - y) ∈ p₁.1.L := by rw [smul_sub]; exact p₁.1.L.sub_mem h1 h2
  have h4 := p₁.2.add _ h3 _ h2
  rw [← smul_add, sub_add_cancel, hx.2.2, hy.2.2] at h4
  have h5 : ((q : Lc.K))⁻¹ • (x - y) ∈ p₁.ker := ⟨h3, by linear_combination -h4⟩
  rw [hx.2.1] at h5
  exact h5

theorem uext_isUp_of_sub {p p₁ : PP Lc n} {x y : Fin n → Lc.K} (hy : p.IsUp y p₁) (hx : x ∈ p.1.L)
    (hxy : ((q : Lc.K))⁻¹ • (x - y) ∈ p.1.L) : p.IsUp x p₁ := by
  refine ⟨hx, hy.2.1, ?_⟩
  have h2 := uext_mem_of_ne p₁ hy.2.2
  have h5 : ((q : Lc.K))⁻¹ • (x - y) ∈ p₁.ker := by rw [hy.2.1]; exact hxy
  have h4 := p₁.2.add _ h5.1 _ h2
  rw [← smul_add, sub_add_cancel, hy.2.2, h5.2, zero_add] at h4
  exact h4

end LocF

variable {D : D7} {u : D.what₂.Word} {X : Ch D u} {i : ℕ} (M : PtModel X i)

theorem PtModel.uext_piL_eq_iff (v : X.A.vT) (c : X.C.cls i) {x y : Fin (D.R.N i) → (M.Lc v).K}
    (hx : x ∈ ((M.rep c).2 v).1.L) (hy : y ∈ ((M.rep c).2 v).1.L) :
    M.piL v c x = M.piL v c y ↔ ((X.A.T : (M.Lc v).K))⁻¹ • (x - y) ∈ ((M.rep c).2 v).1.L := by
  have hxy := Submodule.sub_mem _ hx hy
  have e := M.piL_add v c _ hxy _ hy
  rw [sub_add_cancel] at e
  constructor
  · intro h
    obtain ⟨f, hf⟩ := ((M.rep c).2 v).2.lat
    refine LocF.uext_ker hf (X.fm.lv_rank i v c) (M.piL v c) (M.piL_add v c) (M.piL_smul v c) (M.piL_surj v c) hxy ?_
    rw [h] at e
    simpa using e
  · intro h
    have e2 := M.piL_smul v c (X.A.T : (M.Lc v).O) _ h
    have e3 : (M.Lc v).res (X.A.T : (M.Lc v).O) = 0 := ((M.Lc v).res_ker _).2 ⟨1, by simp⟩
    rw [e3, zero_smul, Subring.smul_def, smul_smul, Subring.coe_natCast, mul_inv_cancel₀ (M.Lc v).q_ne, one_smul] at e2
    rw [e, e2, zero_add]

theorem uop_isExt : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u) (i : ℕ) (M : PtModel X i) (v : X.A.vT) (φ : Fn X i)
    (Φ : M.Pt → M.Val), M.IsExt φ Φ → M.IsExt (Uop X i v φ) (fun p => ∑ᶠ p₁ ∈ {p₁ | M.Inc v p p₁}, Φ p₁) := by
  intro D u X i M v φ Φ hΦ
  obtain ⟨hfin, hact, huniq⟩ := GlobalTheory.T.levelPrime_incidence_finite_fibres_stable D u X i M v
  constructor
  · intro c
    choose s hs1 hs2 using M.piL_surj v c
    have hf : ∀ y, X.fm.fv i v c y = 1 → ((M.rep c).2 v).1.f (s y) = 1 := by
      intro y hy
      rw [← M.piL_f v c _ (hs1 y), hs2, hy]
    let t : X.fm.lv i v c → LocF.PP (M.Lc v) (D.R.N i) := fun y =>
      if hy : X.fm.fv i v c y = 1 then (huniq (M.rep c) _ (hf y hy)).exists.choose else (M.rep c).2 v
    have ht : ∀ y, X.fm.fv i v c y = 1 → ((M.rep c).2 v).IsUp (s y) (t y) := by
      intro y hy
      simp only [t, dif_pos hy]
      exact (huniq (M.rep c) _ (hf y hy)).exists.choose_spec
    let P : X.fm.lv i v c → M.Pt := fun y => ((M.rep c).1, Function.update (M.rep c).2 v (t y))
    have hbij : Set.BijOn P
        ((Finset.univ.filter (fun x : X.fm.lv i v c => X.fm.fv i v c x = 1) : Finset _) : Set _)
        {p₁ | M.Inc v (M.rep c) p₁} := by
      refine ⟨?_, ?_, ?_⟩
      · intro y hy
        have hy' : X.fm.fv i v c y = 1 := by simpa using hy
        refine ⟨rfl, fun v' hv' => Function.update_of_ne hv' _ _, s y, hf y hy', ?_⟩
        simp only [P, Function.update_self]
        exact ht y hy'
      · intro y hy y' hy' e
        have h1 : X.fm.fv i v c y = 1 := by simpa using hy
        have h2 : X.fm.fv i v c y' = 1 := by simpa using hy'
        have e1 : t y = t y' := by
          have := congrFun (congrArg Prod.snd e) v
          simpa only [P, Function.update_self] using this
        have h3 := LocF.uext_sub_mem (ht y h1) (e1 ▸ ht y' h2)
        rw [← hs2 y, ← hs2 y']
        exact (M.uext_piL_eq_iff v c (hs1 y) (hs1 y')).2 h3
      · rintro p₁ ⟨h1, h2, x, hx1, hx2⟩
        have hy : X.fm.fv i v c (M.piL v c x) = 1 := by rw [M.piL_f v c x hx2.1, hx1]
        refine ⟨M.piL v c x, by simpa using hy, ?_⟩
        have h3 := LocF.uext_isUp_of_sub hx2 (hs1 _)
          ((M.uext_piL_eq_iff v c (hs1 _) hx2.1).1 (hs2 _))
        have h4 := (huniq (M.rep c) _ (hf _ hy)).unique (ht _ hy) h3
        refine Prod.ext h1.symm (funext fun v' => ?_)
        by_cases hv : v' = v
        · subst hv
          simp only [P, Function.update_self]
          exact h4
        · simp only [P, Function.update_of_ne hv]
          exact (h2 v' hv).symm
    have e1 := finsum_mem_eq_of_bijOn (f := fun y => Φ (P y)) (g := Φ) P hbij (fun _ _ => rfl)
    beta_reduce
    rw [← e1, finsum_mem_coe_finset, Submodule.coe_sum]
    simp only [Uop, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      LinearEquiv.coe_coe]
    refine Finset.sum_congr rfl fun y hy => ?_
    have hy' : X.fm.fv i v c y = 1 := by simpa using hy
    obtain ⟨g, hg1, hg2⟩ := M.up_eq v c (s y) (t y) (hf y hy') (ht y hy')
    rw [hs2] at hg1 hg2
    rw [hΦ.1, hg2, ← hΦ.2, hg1]
  · intro g p
    have hbij : Set.BijOn (fun p₁ : M.Pt => g • p₁) {p₁ | M.Inc v p p₁} {p₁ | M.Inc v (g • p) p₁} := by
      refine ⟨fun p₁ h => (hact g p p₁).1 h, fun a _ b _ e => MulAction.injective g e, fun p₁ h => ?_⟩
      refine ⟨g⁻¹ • p₁, (hact g p _).2 ?_, smul_inv_smul g p₁⟩
      rw [smul_inv_smul]; exact h
    have e1 := finsum_mem_eq_of_bijOn (f := fun p₁ => M.act g (Φ p₁)) (g := Φ) _ hbij (fun a _ => (hΦ.2 g a).symm)
    beta_reduce

    rw [← e1, finsum_mem_eq_finite_toFinset_sum _ (hfin p).1, finsum_mem_eq_finite_toFinset_sum _ (hfin p).1, map_sum]

end GlobalTheory.LvT
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions GlobalTheory.CharVal GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation

namespace GlobalTheory.CharVal.DetFrame

theorem maxV_detLat (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) (N : Submodule (𝓞 E) (Sp E n))
    (P : HeightOneSpectrum (𝓞 E)) (f : Sp E n ≃ₗ[E] Sp E n)
    (hf : ∀ x, f x ∈ localization₂ P.asIdeal N ↔ x ∈ stdAt E n P) :
    MaxV P (detLat N) (P.valuation E ((LinearEquiv.det f : Eˣ) : E)) := by
  classical
  rw [LinearEquiv.coe_det]
  refine ⟨val_le_of_span ?_, ?_⟩
  · rintro a ⟨A, hA, rfl⟩
    let g : Sp E n →ₗ[E] Sp E n := Matrix.toLin' A
    have hg : ∀ x ∈ stdAt E n P, ((f.symm : Sp E n →ₗ[E] Sp E n) ∘ₗ g) x ∈ stdAt E n P := by
      intro x hx
      rw [← hf]
      obtain ⟨s, hs, hx⟩ := (mem_locP P _ _).1 hx
      refine (mem_locP P _ _).2 ⟨s, hs, ?_⟩
      have h1 := hA _ hx
      have h2 : A.mulVec (s • x) = s • f (((f.symm : Sp E n →ₗ[E] Sp E n) ∘ₗ g) x) := by
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
        rw [Matrix.mulVec_smul]
        rfl
      rwa [h2] at h1
    have h := GlobalTheory.Survey.StandardDeterminantUnits.val_det_le_one _ hg
    have h3 : LinearMap.det (f : Sp E n →ₗ[E] Sp E n) *
        LinearMap.det ((f.symm : Sp E n →ₗ[E] Sp E n) ∘ₗ g) = A.det := by
      rw [LinearMap.det_comp, ← mul_assoc, LinearEquiv.det_mul_det_symm, one_mul]
      exact LinearMap.det_toLin' A
    rw [← h3, map_mul]
    exact mul_le_of_le_one_right' h
  · have h1 : ∀ i : Fin n, ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • f (Pi.single i (1 : E)) ∈ N := fun i =>
      (mem_locP P _ _).1 ((hf _).2 (le_locP P _ (by simpa using single_mem_stdLat (E := E) i 1)))
    choose s hs hs' using h1
    set t : 𝓞 E := ∏ i, s i with ht
    have htP : t ∉ P.asIdeal := by
      intro hm
      obtain ⟨i, -, h⟩ := (Ideal.IsPrime.prod_mem_iff (hp := P.isPrime)).1 hm
      exact hs i h
    have ht' : ∀ i, t • f (Pi.single i (1 : E)) ∈ N := by
      intro i
      rw [ht, ← Finset.prod_erase_mul _ s (Finset.mem_univ i), mul_smul]
      exact N.smul_mem _ (hs' i)
    let g : Sp E n →ₗ[E] Sp E n := (algebraMap (𝓞 E) E t) • (f : Sp E n →ₗ[E] Sp E n)
    refine ⟨(LinearMap.toMatrix' g).det, Submodule.subset_span ⟨LinearMap.toMatrix' g, ?_, rfl⟩, ?_⟩
    · intro v hv
      have h2 : (LinearMap.toMatrix' g).mulVec v = t • f v := by
        rw [LinearMap.toMatrix'_mulVec]
        simp [g]
      rw [h2]
      clear h2
      rw [stdLat_eq_span] at hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact ht' i
      | zero => simp
      | add x y _ _ hx hy => rw [map_add (f := _), smul_add]; exact N.add_mem hx hy
      | smul r x _ hx =>
        rw [← algebraMap_smul E r x, map_smul, algebraMap_smul, smul_comm]
        exact N.smul_mem r hx
    · rw [LinearMap.det_toMatrix', LinearMap.det_smul, map_mul, map_pow,
        (HeightOneSpectrum.valuation_eq_one_iff_notMem P).2 htP, one_pow, one_mul]

end GlobalTheory.CharVal.DetFrame
end

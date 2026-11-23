module

public import Formalism.LocalToGlobal.Divisibility.Inputs
public import Formalism.LocalToGlobal.Divisibility.Bundle002
public import Formalism.LocalToGlobal.Divisibility.Numbers
public import Formalism.LocalToGlobal.Divisibility.NumbersLink
public import Formalism.LocalToGlobal.Divisibility.TwistedPlaceEtaSumLeExtended
public import Formalism.LocalToGlobal.Divisibility.DivisionCompatibleToSub2Indef2
public import Formalism.LocalToGlobal.Divisibility.Bundle004
public import Formalism.SharpRestriction.Bundle002
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef Formalism.BasicNotions

def NumDatum.unitE (Nd : NumDatum) (Nc : ℝ) : ℝ := Nd.sc.x ^ Nd.sc.eps * (Nd.B0 + Nc)

theorem NumDatum.logLog_le (Nd : NumDatum) (h : Real.log Nd.sc.x ≤ Nd.sc.L) :
    Real.log (Real.log Nd.sc.x) ≤ Nd.sc.x ^ Nd.sc.eps := by
  have hl : 0 < Real.log Nd.sc.x := Real.log_pos Nd.sc.one_lt_alt
  have h1 := Real.log_le_sub_one_of_pos hl
  have h2 : Nd.sc.L = Nd.sc.x ^ Nd.sc.eps := rfl
  linarith

theorem NumDatum.loss_bound_nonneg (Nd : NumDatum) : 0 ≤ Nd.B0 := by
  unfold NumDatum.B0
  have := Nd.b_pos
  have := Real.rpow_nonneg Nd.x_pos.le Nd.sc.eps
  positivity

theorem NumDatum.one_le_B0 (Nd : NumDatum) : 1 ≤ Nd.B0 := by
  unfold NumDatum.B0
  have hf : (1 : ℝ) ≤ Nd.R.f := by
    have : 1 ≤ Nd.R.f := by
      have h1 : Nd.R.f = 2 * Nd.R.ord := rfl
      have h2 := Nd.R.ord_pos
      omega
    exact_mod_cast this
  have hm : (1 : ℝ) ≤ Nd.R.m := by
    have := Nd.R.two_le_m
    exact_mod_cast (show 1 ≤ Nd.R.m by omega)
  have hb := Nd.one_le_b
  have hx : 1 ≤ Nd.sc.x ^ Nd.sc.eps := Real.one_le_rpow Nd.sc.one_lt_alt.le Nd.sc.eps_pos.le
  have h1 := one_le_mul_of_one_le_of_one_le hf hm
  have h2 := one_le_mul_of_one_le_of_one_le h1 hb
  exact one_le_mul_of_one_le_of_one_le h2 hx

theorem NumDatum.one_le_m_unitE (Nd : NumDatum) {Nc : ℝ} (hNc : 0 ≤ Nc) : 1 ≤ (Nd.R.m : ℝ) * Nd.unitE Nc := by
  unfold NumDatum.unitE
  have hm : (1 : ℝ) ≤ Nd.R.m := by
    have := Nd.R.two_le_m
    exact_mod_cast (show 1 ≤ Nd.R.m by omega)
  have hx : 1 ≤ Nd.sc.x ^ Nd.sc.eps := Real.one_le_rpow Nd.sc.one_lt_alt.le Nd.sc.eps_pos.le
  have hB : 1 ≤ Nd.B0 + Nc := by linarith [Nd.one_le_B0]
  exact one_le_mul_of_one_le_of_one_le hm (one_le_mul_of_one_le_of_one_le hx hB)

section Scale

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

def ZscOfNum (A : FamIn K G Pl0 T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (Nd : NumDatum) (eJ : A.fam.base.J ≃ Fin Nd.R.m)
    (Nc : ℝ) (Zs : DefSub A.fam.amb) : IndefScale A.fam.base where
  F0 y j := Nd.Fj ((eJ j).1 + 1) y
  J0 t y j := ((A.fam.JJ P0 ψ0 Zs j t y : ℚ) : ℝ)
  E1u := Nd.unitE Nc
  l3m j := ∑ ρ : RPl Nd.R, (((Nd.R.k : ℝ) + (((eJ j).1 + 1 : ℕ) : ℝ) - 1) - ((Nd.R.m : ℝ) - (((eJ j).1 + 1 : ℕ) : ℝ))) *
    Nd.w ((eJ j).1 + 1) ρ * Nd.logOm
  l3u := Nd.B0 * Real.log (Real.log Nd.sc.x)
  l6m j := ∑ ρ : RPl Nd.R, Nd.logHook ((eJ j).1 + 1) ρ
  l6u := (Nd.R.f : ℝ) * (Nd.R.nV : ℝ) ^ 2 * Nd.Lp
  x := Nd.sc.x
  b := Nd.sc.b
  la := Real.log (Fintype.card G)
  de := 8 * (Nd.R.f : ℝ) * (Nd.R.r : ℝ) / ((min (Nd.g 0) (Nd.g 1) : ℕ) : ℝ)

variable (A : FamIn K G Pl0 T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (Nd : NumDatum) (eJ : A.fam.base.J ≃ Fin Nd.R.m) (Nc : ℝ)

def dgOf (hT : Finite T) : ℕ :=
  letI := Fintype.ofFinite T
  Finset.univ.lcm fun p : Fin m × T => (A.fam.L p.1 p.2).DG (A.fam.lvlA P0 ψ0)

theorem dgOf_dvd (hT : Finite T) (j : Fin m) (t : T) : (A.fam.L j t).DG (A.fam.lvlA P0 ψ0) ∣ dgOf A P0 ψ0 hT := by
  letI := Fintype.ofFinite T
  exact Finset.dvd_lcm (f := fun p : Fin m × T => (A.fam.L p.1 p.2).DG (A.fam.lvlA P0 ψ0)) (Finset.mem_univ (j, t))

theorem dgOf_pos (hT : Finite T) : 0 < dgOf A P0 ψ0 hT := by
  letI := Fintype.ofFinite T
  have hpos : ∀ j t, 0 < (A.fam.L j t).DG (A.fam.lvlA P0 ψ0) := by
    intro j t
    unfold BlockDat.DG
    refine Nat.mul_pos Nat.card_pos (Nat.pos_of_ne_zero ?_)
    unfold CSD.DGam
    rw [Ne, Finset.lcm_eq_zero_iff]
    rintro ⟨c, -, hc⟩
    exact (Fintype.card_pos (α := ((A.fam.L j t).S.Gam c))).ne' hc
  refine Nat.pos_of_ne_zero ?_
  unfold dgOf
  rw [Ne, Finset.lcm_eq_zero_iff]
  rintro ⟨p, -, hp⟩
  exact (hpos p.1 p.2).ne' hp

end Scale

section Q

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df0 Df1 : DefSide Bs} {Dc : DefCols Df1}
  {Sp : SPer Dc} {N : IndefNum Bs}

def QOf (P : IndefCore Df0 Df1 Dc Sp N) (LG E3 : ℝ) (E2 : Bs.J → ℝ) : ℝ :=
  max 1 (boundB P LG E3 E2 + N.hh + 28 * N.la)

end Q

section Sizes

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
variable (A : FamIn K G Pl0 T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (Nd : NumDatum) (eJ : A.fam.base.J ≃ Fin Nd.R.m) (Nc : ℝ)

def LamSizeAt (s : ℕ) (cG : ℝ) : Prop :=
  Real.log (Fintype.card G) + Real.log (s : ℝ) ≤ cG * ((Nd.R.m : ℝ) * Nd.unitE Nc)

def DGamSize (hT : Finite T) (s : ℕ) (cD : ℝ) : Prop :=
  Real.log (dgOf A P0 ψ0 hT : ℝ) + Real.log (s : ℝ) ≤ cD * Nd.unitE Nc

end Sizes

section Assemble

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

end Assemble

end Formalism.L2.DIV
end
end

section

noncomputable section

open Module NumberField IsDedekindDomain

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef

section Arith

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}

structure ArithAt (A3 : FamIn3 K G Pl0 I0 Ty T m) (s : ℕ) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G)
    (ψ1 : P1 →* Kˣ) (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs))
    (Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)) (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3)
    (cf : ConvFace A3.fam3.base3) (C CH : ℝ)
    (Pk : IndefPkgR A3.fam3.amb3 (Formalism.IndefR.Cx.faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) cf C CH)
    {Pl : Type} [Fintype Pl] [DecidableEq Pl] (R : RecNums A3.fam3.base3.J Pl) (bd : Fin m → ℝ) (dg : ℕ) : Prop where
  eig6 : ∑ j, R.hX j ≤ ∑ j, ((Zsc Pk.Zs).num C CH).l6 j
  hG0 : Real.log (Fintype.card G) ≤ R.lam0
  l3 : ∃ El3 : ℝ, ∑ j, ((Zsc Pk.Zs).num C CH).l3 j ≤ (∑ j, ∑ ρ, R.pq j * R.w j ρ * R.logOm) + El3 ∧
    El3 + lgDef R s + (∑ j, (((Zsc Pk.Zs).num C CH).E1 j + etaSumBound bd dg s j)) + 1 ≤ R.errB
  q : ∃ Q : ℝ, 0 ≤ ((Zsc Pk.Zs).num C CH).de ∧ 3 * ((Zsc Pk.Zs).num C CH).de * Q ≤ 1 ∧ 1 ≤ Q ∧
    boundBR Pk.core (lgDef R s) 1 (etaSumBound bd dg s) + ((Zsc Pk.Zs).num C CH).hh + 28 * ((Zsc Pk.Zs).num C CH).la ≤ Q
  la_le : ((Zsc Pk.Zs).num C CH).la ≤ R.lam0
  constant_ge_twenty_eight : 28 ≤ R.C0

variable {A3 : FamIn3 K G Pl0 I0 Ty T m} {s : ℕ} {P0 : Subgroup G} {ψ0 : P0 →* Kˣ} {P1 : Subgroup G}
  {ψ1 : P1 →* Kˣ} {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)} {Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)}
  {Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3} {cf : ConvFace A3.fam3.base3} {C CH : ℝ}
  {Pk : IndefPkgR A3.fam3.amb3 (Formalism.IndefR.Cx.faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) cf C CH}
  {Pl : Type} [Fintype Pl] [DecidableEq Pl] {R : RecNums A3.fam3.base3.J Pl} {u : (Dc Pk.Zs).Mem}
  {Nu : Submodule (𝓞 K) (Fin ((Dc Pk.Zs).a u) → K)} {sg : HeightOneSpectrum (𝓞 K) → ℝ} {bd : Fin m → ℝ}

def DivisionInputsWithoutNorm.ofRows (hNu : Submodule.IsFullLattice K Nu) (hsg : (Function.support (shiftZ sg)).Finite)
    (hXc : ∀ v, IsUnit ((Dc Pk.Zs).Xc u v).det) (ha : 0 < (Dc Pk.Zs).a u)
    (X0 : InfinitePlace K → Matrix (Fin ((A3.side3 P1 ψ1 Pk.Zs).nV A3.fam3.base3.μ0))
      (Fin ((A3.side3 P1 ψ1 Pk.Zs).nV A3.fam3.base3.μ0)) ℂ)
    (hX0 : ∀ v, IsUnit (X0 v).det ∧
      ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = ((A3.side3 P1 ψ1 Pk.Zs).HV A3.fam3.base3.μ0).map v.embedding)
    (ch : ColChain (Dc Pk.Zs) u) (hn : HtNums R (InfinitePlace K))
    (nP : ∀ v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (ch.c (Fin.last ch.mm)))) (ch.X (Fin.last ch.mm))
      (Pi.basisFun K (Fin ((A3.side3 P1 ψ1 Pk.Zs).nV A3.fam3.base3.μ0))).dualBasis (Formalism.HN.dualFrame X0) v ch.PtL ^ 2 ≤
        Real.exp hn.hPn)
    (cb : CBData ch.X ch.Kj) (nKcb : ∀ j v, Real.log (cb.sq j v) ≤ ∑ l ∈ Finset.univ.filter (fun l => ch.lf l = j), hn.sz l v)
    (h11 : LiftExponentAtTwisted A3.A P0 ψ0 (A3.fam3.toSub2 Pk.Zs) Pk.core.base.μ Pk.core.base.Tw (Zsc Pk.Zs).J0)
    (dg : ℕ) (hdg : 0 < dg) (hdvd : ∀ j t, (A3.A.fam.L j t).DG (A3.A.fam.lvlA P0 ψ0) ∣ dg)
    (hA : ArithAt A3 s P0 ψ0 P1 ψ1 Dc Sp Zsc cf C CH Pk R bd dg) :
    DivisionInputsWithoutNorm A3 s P0 ψ0 P1 ψ1 Dc Sp Zsc cf C CH Pk R u Nu sg bd where
  Nu_lat := hNu
  sg_fin := hsg
  Xc_unit := hXc
  a_pos := ha
  X0 := X0
  base_matrix_det_unit := hX0
  ch := ch
  hn := hn
  nP := nP
  cb := cb
  nKcb := nKcb
  eig6 := hA.eig6
  h11 := h11
  dg := dg
  dg_pos := hdg
  dg_dvd := hdvd
  hG0 := hA.hG0
  El3 := Classical.choose hA.l3
  L3main := (Classical.choose_spec hA.l3).1
  errB := (Classical.choose_spec hA.l3).2
  Q := Classical.choose hA.q
  de0 := (Classical.choose_spec hA.q).1
  deQ := (Classical.choose_spec hA.q).2.1
  Q1 := (Classical.choose_spec hA.q).2.2.1
  Qb := (Classical.choose_spec hA.q).2.2.2
  la_le := hA.la_le
  constant_ge_twenty_eight := hA.constant_ge_twenty_eight

end Arith

end Formalism.L2.DIV

end
end

section

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef

section N

open Formalism.BasicNotions Formalism.MainNotions

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

theorem lw_eq_lwP (D : D7) (y : HeightOneSpectrum (𝓞 D.what₂.LL)) : Formalism.DivisionValues.lw y = SizeData₂.lwP (D.plEq.symm y) := by
  unfold SizeData₂.lwP
  rw [Equiv.apply_symm_apply]
  rfl

theorem ramw_eq_ramIdx (D : D7) (y : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    ((ramw y : ℤ) : ℝ) = ((D.what₂.places.ramIdx (D.plEq.symm y) : ℕ) : ℝ) := by
  rw [D.ram_eq, Equiv.apply_symm_apply, ← lf_eW_eq_ramw]
  rfl

theorem sum_le_etaSum_num (L : SizeData₂ D) (A : FamIn D.what₂.LL G Pl0 T m) {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ}
    {Zs : DefSub A.fam.amb} {S0 : IndefData (A.side P0 ψ0 Zs)} {tup : T → D.what₂.Tup} (hnum : NumTie D A S0 tup)
    (hTw : TieTwRec L S0.Tw) (i : Fin m) :
    ∑ y ∈ S0.Tw, Formalism.DivisionValues.lw y * (A.fam.etaJW P0 ψ0 Zs i (S0.μ y) y : ℝ) ≤ Formalism.MainNotions.etaSum L ((i : ℕ) + 1) := by
  classical
  obtain ⟨g, hg⟩ : ∃ g : D.what₂.places.Pl → ℝ,
      g = fun w => SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) * (D.what₂.etaJ ((i : ℕ) + 1) w : ℝ) := ⟨_, rfl⟩
  have hterm : ∀ y ∈ S0.Tw, Formalism.DivisionValues.lw y * (A.fam.etaJW P0 ψ0 Zs i (S0.μ y) y : ℝ) = g (D.plEq.symm y) := by
    intro y hy
    have h1 : Formalism.DivisionValues.lw y = SizeData₂.lwP (D.plEq.symm y) := lw_eq_lwP D y
    have h2 : ((ramw y : ℤ) : ℝ) = ((D.what₂.places.ramIdx (D.plEq.symm y) : ℕ) : ℝ) := ramw_eq_ramIdx D y
    have h3 : D.what₂.etaJ ((i : ℕ) + 1) (D.plEq.symm y) = A.fam.etaJ P0 ψ0 Zs i (S0.μ y) y := by
      rw [hnum.etaJ i (D.plEq.symm y), Equiv.apply_symm_apply, if_pos hy]
    rw [hg]
    dsimp only
    rw [← A.fam.etaJ_ramw P0 ψ0 Zs i (S0.μ y) y, h1, h2, h3]
    ring
  have hsi : ∑ w ∈ S0.Tw.image D.plEq.symm, g w = ∑ y ∈ S0.Tw, g (D.plEq.symm y) :=
    Finset.sum_image (fun x _ y _ hxy => D.plEq.symm.injective hxy)
  have hE : Formalism.MainNotions.etaSum L ((i : ℕ) + 1) = ∑ w ∈ L.supp.filter (fun w => D.what₂.muAt w ≠ D.what₂.mu0), g w := by
    rw [hg]
    unfold Formalism.MainNotions.etaSum
    rfl
  rw [Finset.sum_congr rfl hterm, ← hsi, hE]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro w hw
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hw
    exact Finset.mem_filter.2 (hTw y hy)
  · intro w _ _
    rw [hg]
    exact mul_nonneg (mul_nonneg (zero_le_logWeight w) (Nat.cast_nonneg _)) (by exact_mod_cast D.what₂.etaJ_nonneg _ w)

theorem inEta_num (L : SizeData₂ D) (A : FamIn D.what₂.LL G Pl0 T m) {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ}
    {Zs : DefSub A.fam.amb} {S0 : IndefData (A.side P0 ψ0 Zs)} {tup : T → D.what₂.Tup} (Ce : ℝ)
    (hN : ∀ j ∈ SizeData₂.lifts D, Formalism.MainNotions.DIVinN_at L j Ce) (hm : m = D.R.m) (hnum : NumTie D A S0 tup)
    (hTw : TieTwRec L S0.Tw) (hD : D.what₂.D0 = (A.fam.R A.fam.μ0).dZ (A.fam.lvl P0 ψ0) (Zs.Z A.fam.μ0)) :
    InEta A.fam P0 ψ0 Zs S0.μ S0.Tw (fun _ => divSize L Ce) := by
  intro i
  have h1 := sum_le_etaSum_num L A hnum hTw i
  have hi : (i : ℕ) + 1 ∈ SizeData₂.lifts D := by
    unfold SizeData₂.lifts
    exact Finset.mem_Icc.2 ⟨by omega, by have := i.isLt; omega⟩
  have h2 := hN ((i : ℕ) + 1) hi
  unfold Formalism.MainNotions.DIVinN_at at h2
  rw [hD] at h2
  unfold divSize
  exact h1.trans (h2.trans_eq (mul_comm _ _))

variable {I0 Ty : Type}

theorem inEta3_num (L : SizeData₂ D) (A3 : FamIn3 D.what₂.LL G Pl0 I0 Ty T m) {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ}
    {Zs : DefSub A3.fam3.amb3} {S0 : IndefData (A3.side3 P0 ψ0 Zs)} {tup : T → D.what₂.Tup} (Ce : ℝ)
    (hN : ∀ j ∈ SizeData₂.lifts D, Formalism.MainNotions.DIVinN_at L j Ce) (hm : m = D.R.m)
    (hnum : NumTie D A3.A (A3.indefDown S0) tup) (hTw : TieTwRec L S0.Tw)
    (hD : D.what₂.D0 = (A3.A.fam.R A3.A.fam.μ0).dZ (A3.A.fam.lvl P0 ψ0) (Zs.Z A3.A.fam.μ0)) :
    InEta A3.A.fam P0 ψ0 (A3.fam3.toSub2 Zs) S0.μ S0.Tw (fun _ => divSize L Ce) :=
  inEta_num L A3.A (Zs := A3.fam3.toSub2 Zs) (S0 := A3.indefDown S0) Ce hN hm hnum hTw hD

end N

end Formalism.L2.DIV

end
end

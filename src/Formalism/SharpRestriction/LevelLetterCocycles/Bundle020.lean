module

public import Formalism.SharpRestriction.LevelLetterCocycles.CoordHomMapTrace
public import Formalism.SharpRestriction.LevelLetterCocycles.ExponentWindowSubsetShort
public import Formalism.SharpRestriction.LevelLetterCocycles.LatticeBoundsOfThreeParts
public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle014
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle015
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.WachCoordinates.Br

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] (W : LocWach PD LL O v n)

structure BrData (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) where
  I : BaseId W
  C₁ : Coord W I T₁
  C₂ : Coord W I T₂
  C₀ : Coord W I W.one
  h : CoordHom C₁ C₂ F
  e₀ : C₀.V
  ϖ : O
  eO : ℕ
  u : Oˣ
  x : Oˣ
  Ks : ℕ → Type
  [ksRing : ∀ s, CommRing (Ks s)]
  [ksAlg : ∀ s, Algebra LL (Ks s)]
  Δ : Type

attribute [instance] BrData.ksRing BrData.ksAlg

variable {W}

structure BrProps {T₁ T₂ : LocLat G Qp LL O} {F : LatHom T₁.L T₂.L} (D : BrData W T₁ T₂ F)
    (Cu : Formalism.ExponentWindows.E.Cuts n) (kd : ZMod n → Formalism.ExponentWindows.Kind) (bb : ZMod n → ℕ)
    (j g G₀ Sz η hh sig rr : ℕ) : Prop where

  irr : Irreducible D.ϖ

  prim : Formalism.ExponentWindows.E.PrimBase D.I.Bs D.ϖ D.eO

  u_eq : (D.u : O) = 1 + (D.I.Bs.ℓ : O) * (D.x : O)

  lat₁ : Formalism.ExponentWindows.E.FinalLat (latOf D.C₁) Cu kd bb j G₀ Sz η hh

  lat₂ : Formalism.ExponentWindows.E.FinalLat (latOf D.C₂) Cu kd bb j G₀ Sz η hh

  unit : Formalism.ExponentWindows.E.PrimUnit (latOf D.C₀) D.e₀

  rho : ∀ c ∈ Cu.cuts, ∀ w,
    (latOf D.C₁).Wc Cu (Formalism.ExponentWindows.E.LamOf D.I.Bs Cu (Formalism.ExponentWindows.E.HArc g G₀ Sz η kd bb)) c w →
    ∀ y z, (latOf D.C₁).IsRho c j (Formalism.ExponentWindows.E.parM D.I.Bs.ℓ hh g) g sig w y z → (y, z) ∈ Zf D.C₁

  ext : ∀ κ ∈ Zf D.C₂, ∃ Y : Formalism.ExponentWindows.E.Ext (latOf D.C₂) (latOf D.C₀), Y.Rep D.e₀ κ.1 κ.2 ∧
    Formalism.ExponentWindows.E.PrimExt Y D.e₀ Cu j G₀ rr (Formalism.ExponentWindows.E.HArc g G₀ Sz η kd bb)

  wprime : Formalism.ExponentWindows.E.WPrimeCuts (latHomOf D.h) Cu rr

  arcs : ∀ c ∈ Cu.cuts, Formalism.ExponentWindows.E.FinalArc (latHomOf D.h) c (Cu.ell c)
    (Formalism.ExponentWindows.E.HArc g G₀ Sz η kd bb c) LL D.Ks D.Δ D.ϖ D.u j (Formalism.ExponentWindows.E.parM D.I.Bs.ℓ hh g) g G₀ Sz η
    (Formalism.ExponentWindows.E.kindAt kd c) (Formalism.ExponentWindows.E.sizeAt bb c)

variable (W) [Fintype (K →ₐ[Qp] LL)]

def Realised : Prop :=
  ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L),
    GoodCoeffs (K := K) (Qp := Qp) (LL := LL) (O := O) (V := T₁.V) →
    CrysLat PD T₁ → CrysLat PD T₂ → F.Onto →
    ∀ (j Gp S η h : ℕ) (ty : ZMod n → LT) (cuts : Finset (ZMod n)) (arcLen : ZMod n → ℕ)
      (Mb₁ hb₁ Mb₂ hb₂ : ZMod n → ℕ) (hC : CutsOK n j ty cuts arcLen),
      KindJumps PD T₁ W.emb Gp S η ty →
      (∀ τ : K →ₐ[Qp] LL, JumpsInV PD T₁.ρ τ (Set.Icc (-(h : ℤ)) h)) →
      gPar Gp S η ≤ h → SizesOK (gPar Gp S η) S h ty → ThickLe2 ty cuts arcLen →
      (∀ i, JumpsAtE PD T₁ W.emb i (Set.Icc (-(Mb₁ i : ℤ)) (hb₁ i))) →
      (∀ i, JumpsAtE PD T₂ W.emb i (Set.Icc (-(Mb₂ i : ℤ)) (hb₂ i))) →
      WordOK PD.p (initialExponentBound PD.p n j (gPar Gp S η) h (Mb₁ + hb₁) (Mb₂ + hb₂) cuts arcLen) ty cuts
        arcLen →
      ∃ D : BrData W T₁ T₂ F, BrProps D (cutsOf hC) (kdOf ty) (bbOf ty) j (gPar Gp S η) Gp S η h
        (sigPar PD.p (gPar Gp S η) h j) (rrPar PD.p n (Mb₁ + hb₁) (Mb₂ + hb₂) cuts)

variable {W}

end Formalism.MainNotions.WachCoordinates.Br
end
end

section

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains

section LemGCut

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def lemG_sig (l H : ℕ) : ℕ := ⌈((2 * H : ℕ) : ℝ) / ((l : ℝ) - 1) ^ 2 + 1⌉₊

def LemGPair [NeZero n] (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (b : ZMod n → ℕ)
    (S η : ℕ) (i : ZMod n) (x la : W.DD T) : Prop :=
  x ∈ W.N T ∧ Formalism.MainNotions.CrystallineLiftingInputs.DL W T i x ∧
    Formalism.MainNotions.LiftingTheory.qp W ^ b i • x = Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S) • la ∧
    ∃ z ∈ W.N T, Formalism.MainNotions.CrystallineLiftingInputs.DL W T i z ∧
      Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S) • (W.γ T la - la) =
        (W.π₀ * Formalism.MainNotions.LiftingTheory.qp W ^ (⌈aR PD.p (hpar n b S + η)⌉₊ + b i)) • z

def LemGA [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i : ZMod n, (i.val + d) % 2 = 1 →
    ∀ (y : W.DD T₂) (hy : y ∈ W.N T₂), Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ (i - 2) y →
      φVB PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) (W.cmp T₂ ⟨y, hy⟩)) ∈
        FilCris PD T₂.ρ (b i : ℤ) →
      ∃ (x la : W.DD T₂) (hP : LemGPair W T₂ b S η i x la),
        W.cmp T₂ ⟨x, hP.1⟩ =
          (PD.p : LL) ^ ((lemG_sig PD.p (hpar n b S + η) : ℤ) + ((b (i - 1) + S : ℕ) : ℤ) - (b i : ℤ)) •
            φVB PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) (W.cmp T₂ ⟨y, hy⟩))

def LemGB [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i : ZMod n, (i.val + d) % 2 = 1 →
    ∃ E : ℕ, (E : ℝ) ≤ (3 * aR PD.p (hpar n b S + η) + S + 2 * η) / ((PD.p : ℝ) - 1) +
        lam PD.p (hpar n b S + η) ∧
      ∀ x la : W.DD T₂, LemGPair W T₂ b S η i x la →
        ∃ y ∈ W.N T₁, Formalism.MainNotions.CrystallineLiftingInputs.DL W T₁ i y ∧ W.map F y = ((PD.p : O) ^ E) • x

theorem lemG_ceil_eq (l H E h b : ℕ) :
    (⌈(E : ℝ) + Formalism.MainNotions.CrystallineLiftingInputs.sig2 l H + ((h : ℕ) : ℝ) - (b : ℝ)⌉ : ℤ) =
      (E : ℤ) + ((lemG_sig l H : ℤ) + (h : ℤ) - (b : ℤ)) := by
  have hs : Formalism.MainNotions.CrystallineLiftingInputs.sig2 l H = ((2 * H : ℕ) : ℝ) / ((l : ℝ) - 1) ^ 2 + 1 := by
    simp only [Formalism.MainNotions.CrystallineLiftingInputs.sig2]
    push_cast
    ring
  have h0 : 0 ≤ ((2 * H : ℕ) : ℝ) / ((l : ℝ) - 1) ^ 2 + 1 := by positivity
  have hc : ((lemG_sig l H : ℕ) : ℤ) = ⌈((2 * H : ℕ) : ℝ) / ((l : ℝ) - 1) ^ 2 + 1⌉ := by
    unfold lemG_sig
    exact Int.natCast_ceil_eq_ceil h0
  rw [show (E : ℝ) + Formalism.MainNotions.CrystallineLiftingInputs.sig2 l H + ((h : ℕ) : ℝ) - (b : ℝ) =
      (((2 * H : ℕ) : ℝ) / ((l : ℝ) - 1) ^ 2 + 1) + (((E : ℤ) + h - b : ℤ) : ℝ) by
        rw [hs]; push_cast; ring,
    Int.ceil_add_intCast, ← hc]
  ring

theorem lemmaGs_of_lemGAB [NeZero n] (W : LocWach PD LL O v n) (hA : LemGA W) (hB : LemGB W) :
    LemmaGs W := by
  intro d T₁ T₂ F b S η m hset i hi
  obtain ⟨E, hEb, hEx⟩ := hB d T₁ T₂ F b S η m hset i hi
  refine ⟨E, hEb, ?_⟩
  rintro _ ⟨_, ⟨y, hy, hyD, rfl⟩, rfl⟩ hfil
  obtain ⟨x, la, hP, hcmp⟩ := hA d T₁ T₂ F b S η m hset i hi y hy hyD hfil
  obtain ⟨y1, hy1N, hy1D, hmap⟩ := hEx x la hP
  have hp0 : (PD.p : LL) ≠ 0 := by
    obtain ⟨ζ, hζ⟩ := hset.2.2.2.2.1
    haveI : NeZero PD.p := ⟨by have := hset.2.1; omega⟩
    exact hζ.neZero'.out
  have hnat : ((PD.p : ℕ) : O) ^ E • x = (PD.p ^ E : ℕ) • x := by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  have hx' : W.map F y1 ∈ W.N T₂ := by
    rw [hmap, hnat]
    exact nsmul_mem hP.1 _
  refine ⟨y1, hy1N, hx', hy1D, ?_⟩
  rw [lemG_ceil_eq, zpow_add₀ hp0, mul_smul, ← hcmp]
  have hsub : (⟨W.map F y1, hx'⟩ : W.N T₂) = (PD.p ^ E : ℕ) • (⟨x, hP.1⟩ : W.N T₂) :=
    Subtype.ext (by show W.map F y1 = (PD.p ^ E : ℕ) • x; rw [hmap, hnat])
  rw [hsub, map_nsmul, zpow_natCast, ← Nat.cast_smul_eq_nsmul LL, Nat.cast_pow]

def LemGLa [NeZero n] (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (b : ZMod n → ℕ)
    (S η : ℕ) (i : ZMod n) (y la : W.DD T) : Prop :=
  Formalism.MainNotions.CrystallineLiftingInputs.IsTrunc W T (i - 2) 2 1 (2 * (hpar n b S + η)) (lemG_sig PD.p (hpar n b S + η)) y la ∧
    Formalism.MainNotions.CrystallineLiftingInputs.DL W T i la ∧
    Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S) • la ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T (i - 1) 1 ∧
    ∃ z ∈ W.N T, Formalism.MainNotions.CrystallineLiftingInputs.DL W T i z ∧
      Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S) • (W.γ T la - la) =
        (W.π₀ * Formalism.MainNotions.LiftingTheory.qp W ^ (⌈aR PD.p (hpar n b S + η)⌉₊ + b i)) • z

def LemGA_la [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i : ZMod n, (i.val + d) % 2 = 1 →
    ∀ y : W.DD T₂, y ∈ W.N T₂ → Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ (i - 2) y →
      ∃ la : W.DD T₂, LemGLa W T₂ b S η i y la

def GammaActionLemma [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i : ZMod n, (i.val + d) % 2 = 1 →
    ∀ (y : W.DD T₂) (hy : y ∈ W.N T₂), Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ (i - 2) y →
      φVB PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) (W.cmp T₂ ⟨y, hy⟩)) ∈
        FilCris PD T₂.ρ (b i : ℤ) →
      ∀ la : W.DD T₂, LemGLa W T₂ b S η i y la →
        ∃ x : W.DD T₂, x ∈ W.N T₂ ∧ Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ i x ∧
          Formalism.MainNotions.LiftingTheory.qp W ^ b i • x = Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S) • la

def LemGA_0 [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i : ZMod n, (i.val + d) % 2 = 1 →
    ∀ (y : W.DD T₂) (hy : y ∈ W.N T₂), Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ (i - 2) y →
      ∀ la : W.DD T₂, LemGLa W T₂ b S η i y la →
      ∀ (x : W.DD T₂) (hx : x ∈ W.N T₂), Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ i x →
        Formalism.MainNotions.LiftingTheory.qp W ^ b i • x = Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S) • la →
        W.cmp T₂ ⟨x, hx⟩ =
          (PD.p : LL) ^ ((lemG_sig PD.p (hpar n b S + η) : ℤ) + ((b (i - 1) + S : ℕ) : ℤ) - (b i : ℤ)) •
            φVB PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) (W.cmp T₂ ⟨y, hy⟩))

theorem lemGA_of_pieces [NeZero n] (W : LocWach PD LL O v n) (hla : LemGA_la W) (hx : GammaActionLemma W)
    (h0 : LemGA_0 W) : LemGA W := by
  intro d T₁ T₂ F b S η m hset i hi y hy hyD hfil
  obtain ⟨la, hla⟩ := hla d T₁ T₂ F b S η m hset i hi y hy hyD
  obtain ⟨x, hxN, hxD, hxeq⟩ := hx d T₁ T₂ F b S η m hset i hi y hy hyD hfil la hla
  exact ⟨x, la, ⟨hxN, hxD, hxeq, hla.2.2.2⟩,
    h0 d T₁ T₂ F b S η m hset i hi y hy hyD la hla x hxN hxD hxeq⟩

end LemGCut

end Formalism.MainNotions.RamifiedCoefficientChains.S9
end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section Local

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l)

def quotA : Prop :=
  ∀ (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (F : LatHom T₁.L T₂.L),
    IsCrys (P.PD K) T₁.ρ → IsCrys (P.PD K) T₂.ρ → F.Onto →
    ∀ τ (X : Set ℤ), JumpsInV (P.PD K) T₁.ρ τ X → JumpsInV (P.PD K) T₂.ρ τ X

def normA : Prop :=
  ∀ (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (F : LatHom T₁.L T₂.L) (r S η m h : ℕ)
    (up : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → Bool) (b : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℕ),
    HypA P K LL T₁ T₂ F r S η m h up b →
    (∀ τ (X : Set ℤ), JumpsInV (P.PD K) T₁.ρ τ X → JumpsInV (P.PD K) T₂.ρ τ X) →
    ∃ (η₁ h' : ℕ) (b' : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℕ), η₁ ≤ η ∧ h' ≤ h + S + 1 ∧
      HypN P K LL T₁ T₂ F S η₁ m h' up b'

end Local

def quotR (D : D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ K LL : FinExt l, Good K 1 LL → quotA (D.loc l) K LL

def normR (D : D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ K LL : FinExt l, Good K 1 LL → normA (D.loc l) K LL

def dvdR : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ K LL : FinExt l, Good K 1 LL → eK K ∣ l - 1

def p9R (D : D7) (HW : HWOf D.loc) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (K LL : FinExt l) (hG : Good K 1 LL)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys ((D.loc l).PD K) T.ρ →
    ∃ (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
      (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL)),
      Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E

def splitR (D : D7) (HW : HWOf D.loc) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (K LL : FinExt l) (hG : Good K 1 LL)
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
    (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL)),
    Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E →
    ∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (h' : ℕ), 1 ≤ h' → IsCrys ((D.loc l).PD K) T.ρ →
    (∀ τ, JumpsInV ((D.loc l).PD K) T.ρ τ (Set.Icc (-(h' : ℤ)) h')) →
    ∀ κ ∈ latticeFiniteCocycles ((D.loc l).PD K) T.L,
      (l ^ (rhoA l (eK K) h' + sigA l (sK l K) h') : ℕ) • κ ∈
        (⨆ c, JZ ((HW l).W K 1 LL hG) T π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' (MK l K h') c) ⊔ latticeCoboundaries T.L

def univR (D : D7) (HW : HWOf D.loc) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (K LL : FinExt l) (hG : Good K 1 LL)
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
    (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL)),
    Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E →
    ∀ (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (F : LatHom T₁.L T₂.L) (S η m h' : ℕ)
      (up : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → Bool) (b : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℕ),
      HypN (D.loc l) K LL T₁ T₂ F S η m h' up b →
      ∀ c : ZMod (finrank ℚ_[l] ↥(K0 K)), ∃ s₀ : Finset (↥(GK K) → T₂.V),
        s₀.card ≤ eK K * (eK K + 1) * m ∧
        (s₀ : Set (↥(GK K) → T₂.V)) ⊆ latticeFiniteCocycles ((D.loc l).PD K) T₂.L ∧
        ∀ x ∈ JZ ((HW l).W K 1 LL hG) T₂ π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' (MK l K h') c,
          (l ^ (sigA l (sK l K) h' + y2K l K h' S η) : ℕ) • x ∈
            F.ImF ((D.loc l).PD K) ⊔ Submodule.span ↥(OL LL) (s₀ : Set (↥(GK K) → T₂.V))

theorem YA_split (l e s h' S η : ℕ) :
    YA l e s h' S η = (rhoA l e h' + sigA l s h') + (sigA l s h' +
      (2 * sigA l s h' + kapA l e h' S + rhoA l e h' + max (2 * sigA l s h') (ycA l h' η))) := by
  unfold YA
  ring

theorem YA_mono (l e s h' S : ℕ) {η₁ η : ℕ} (h : η₁ ≤ η) : YA l e s h' S η₁ ≤ YA l e s h' S η := by
  rw [YA_split, YA_split]
  unfold ycA
  gcongr

theorem annihilation_of_scaled_spans {O M ι : Type} [CommRing O] [AddCommGroup M] [Module O M] [Fintype ι] [DecidableEq M]
    (J : ι → Submodule O M) (B Im : Submodule O M) (s : ι → Finset M) (hB : B ≤ Im) (a b : ℕ) (p : M)
    (hp : a • p ∈ (⨆ c, J c) ⊔ B) (hU : ∀ c, ∀ x ∈ J c, b • x ∈ Im ⊔ Submodule.span O (s c : Set M)) :
    b • a • p ∈ Submodule.span O ((Finset.univ.biUnion s : Finset M) : Set M) ⊔ Im := by
  classical
  have key : (⨆ c, J c) ≤
      (Submodule.span O ((Finset.univ.biUnion s : Finset M) : Set M) ⊔ Im).comap
        (b • LinearMap.id : M →ₗ[O] M) := by
    refine iSup_le fun c y hy => ?_
    have h1 := hU c y hy
    have hle : Im ⊔ Submodule.span O (s c : Set M) ≤
        Submodule.span O ((Finset.univ.biUnion s : Finset M) : Set M) ⊔ Im := by
      refine sup_le le_sup_right (le_sup_of_le_left (Submodule.span_mono ?_))
      intro z hz
      exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨c, Finset.mem_univ _, Finset.mem_coe.1 hz⟩)
    show b • y ∈ (Submodule.span O ((Finset.univ.biUnion s : Finset M) : Set M) ⊔ Im)
    exact hle h1
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 hp
  rw [← hxy, smul_add]
  have hx' : b • x ∈ Submodule.span O ((Finset.univ.biUnion s : Finset M) : Set M) ⊔ Im := key hx
  exact Submodule.add_mem _ hx' (Submodule.mem_sup_right (nsmul_mem (hB hy) b))



theorem killR_of_steps (D : D7) (HW : HWOf D.loc) (hd : dvdR) (hq : quotR D) (hn : normR D)
    (h9 : p9R D HW) (hS : splitR D HW) (hU : univR D HW) : killR D := by
  classical
  unfold killR
  intro l _ hl K LL hG
  unfold killA
  intro T₁ T₂ F r S η m h up b hA
  have hjmp : ∀ τ (X : Set ℤ), JumpsInV ((D.loc l).PD K) T₁.ρ τ X → JumpsInV ((D.loc l).PD K) T₂.ρ τ X :=
    hq l hl K LL hG T₁ T₂ F hA.1 hA.2.1 hA.2.2.1
  obtain ⟨η₁, h', b', hη, hh', hN⟩ := hn l hl K LL hG T₁ T₂ F r S η m h up b hA hjmp
  have hc2 := hN.2.1
  have hj2 := hN.2.2.2.2.1
  have hηb := hN.2.2.2.2.2.1
  have hbS := hN.2.2.2.2.2.2.1
  have hh1 := hN.2.2.2.2.2.2.2.1
  obtain ⟨π', E, h9'⟩ := h9 l hl K LL hG T₂ hc2
  have hjmp2 : ∀ τ, JumpsInV ((D.loc l).PD K) T₂.ρ τ (Set.Icc (-(h' : ℤ)) h') := by
    intro τ a ha
    have hmem := hj2 τ a ha
    have h1 := hηb τ
    have h2 := hbS τ
    rcases hmem with hmem | hmem
    · unfold deep at hmem
      split_ifs at hmem
      · obtain ⟨x1, x2⟩ := hmem
        constructor <;> omega
      · obtain ⟨x1, x2⟩ := hmem
        constructor <;> omega
    · obtain ⟨x1, x2⟩ := hmem
      constructor <;> omega
  have hSp := hS l hl K LL hG π' E h9' T₂ h' hh1 hc2 hjmp2
  choose s₀ hs₀card hs₀sub hs₀J using fun c => hU l hl K LL hG π' E h9' T₁ T₂ F S η₁ m h' up b' hN c
  have hB : latticeCoboundaries T₂.L ≤ F.ImF ((D.loc l).PD K) := by
    unfold LatHom.ImF
    exact le_sup_right
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  haveI : NeZero (finrank ℚ_[l] ↥(K0 K)) := by
    first
    | infer_instance
    | exact ⟨Module.finrank_pos.ne'⟩
    | exact ⟨(Formalism.MainNotions.N.Ln34.max_unramified_finrank_pos K).ne'⟩
    | exact ⟨(Formalism.MainNotions.N.PreambleDegrees.finrank_maxUnramifiedSubfield_padicFinExt_pos K).ne'⟩
    | (haveI := Formalism.MainNotions.WachCoordinates.Br.finiteDimensional_max_unramified K; exact ⟨Module.finrank_pos.ne'⟩)
    | (haveI := FiniteDimensional.left ℚ_[l] ↥(K0 K) ↥K.1; exact ⟨Module.finrank_pos.ne'⟩)
  refine ⟨sK l K, h', Nat.mul_div_cancel' (hd l hl K LL hG), hh1, hh', Finset.univ.biUnion s₀, ?_, ?_, ?_⟩
  · calc (Finset.univ.biUnion s₀).card ≤ ∑ c, (s₀ c).card := Finset.card_biUnion_le
      _ ≤ ∑ _c : ZMod (finrank ℚ_[l] ↥(K0 K)), eK K * (eK K + 1) * m :=
        Finset.sum_le_sum fun c _ => hs₀card c
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul]
        ring
  · intro x hx
    obtain ⟨c, -, hc⟩ := Finset.mem_biUnion.1 (Finset.mem_coe.1 hx)
    exact hs₀sub c hc
  · intro p hp
    have hk := annihilation_of_scaled_spans _ _ _ s₀ hB _ _ p (hSp p hp) (fun c x hx => hs₀J c x hx)
    have hY : (l ^ YA l (eK K) (sK l K) h' S η₁ : ℕ) • p ∈
        Submodule.span ↥(OL LL) ((Finset.univ.biUnion s₀ : Finset _) : Set (↥(GK K) → T₂.V)) ⊔
          F.ImF ((D.loc l).PD K) := by
      rw [YA_split, pow_add, mul_comm, mul_smul]
      exact hk
    have e1 : YA l (eK K) (sK l K) h' S η =
        (YA l (eK K) (sK l K) h' S η - YA l (eK K) (sK l K) h' S η₁) + YA l (eK K) (sK l K) h' S η₁ :=
      (Nat.sub_add_cancel (YA_mono l (eK K) (sK l K) h' S hη)).symm
    rw [e1, pow_add, mul_smul]
    exact nsmul_mem hY _

end Formalism.MainNotions.N.Ln34

end
end

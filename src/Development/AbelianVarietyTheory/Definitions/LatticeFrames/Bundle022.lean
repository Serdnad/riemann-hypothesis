module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlaceLaws
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Formalism.DoubleCosetMeasures.StatementZ
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGLEmbeddingUnitaryAdelicSplitPlaceBasis
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle049
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsDiscriminantTwelfthRootOfIdealLatticeIffDelta1
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle011
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ToOneSucc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonarchimedeanLocalFieldSecondCountableT2Space

@[expose] public section

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LocMod.PinModel

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

theorem exists_isOne : ∃ Φ : SB (Matrix Y Y' k), IsOne Φ ∧ Φ.1 0 = 1 := by
  refine ⟨⟨Set.indicator {x | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1, mem_SB_of_periodic (fun x hx => ?_) fun x y hy => ?_⟩, rfl, ?_⟩
  · exact (Set.mem_of_indicator_ne_zero hx)
  · have : (∀ r q, (x + y) r q ∈ 𝒪[k]) ↔ ∀ r q, x r q ∈ 𝒪[k] :=
      ⟨fun h r q => by simpa using sub_mem (h r q) (hy.intM r q), fun h r q => add_mem (h r q) (hy.intM r q)⟩
    by_cases hx : ∀ r q, x r q ∈ 𝒪[k]
    · rw [Set.indicator_of_mem (by exact this.2 hx), Set.indicator_of_mem (by exact hx)]
    · rw [Set.indicator_of_notMem (by exact fun h => hx (this.1 h)), Set.indicator_of_notMem (by exact hx)]
  · simp

variable {u : D.what₂.Word}

end GlobalTheory.LocMod.PinModel
end
end

section

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SplitWeil GlobalTheory.LocMod ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

variable {D : D7}

structure LocPl (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (M : GlobalTheory.FinPl.Lat S) (M' : GlobalTheory.FinPl.Lat T) where
  k : Type
  [fld : Field k]
  [val : ValuativeRel k]
  [top : TopologicalSpace k]
  [loc : IsNonarchimedeanLocalField k]
  q : GlobalTheory.FinPl.SplitPt D k
  unit : q.UnitAA
  Y : Type
  Y' : Type
  [fY : Fintype Y]
  [dY : DecidableEq Y]
  [fY' : Fintype Y']
  [dY' : DecidableEq Y']
  FS : Frame k S.rank Y'
  FT : Frame k T.rank Y
  Φ : SB (Matrix Y Y' k)
  e : WO S T →₀ ℂ
  e_is : (ofSplit q).IsCombAt ψ FS FT e Φ.1
  o : WO S T →₀ ℂ
  o_at : ∀ x ∈ o.support, IsHalf (q.e + cA D q.e) x
  o_is : ∀ Tm, (ofSplit q).IsModel ψ FS FT Tm → ∀ Φ₀ Φ₁, IsOne Φ₁ →
    Φ₀.1 = Set.indicator {x | (ofSplit q).up FS FT x ∈ latO S T (M : Set _) (M' : Set _) (· = q.v)} (fun _ => 1) →
    Tm Φ₁ = comb ψ S T o (Tm Φ₀)

attribute [instance] LocPl.fld LocPl.val LocPl.top LocPl.loc LocPl.fY LocPl.dY LocPl.fY' LocPl.dY'


open Classical in
def prodDat {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T} {n : ℕ}
    (L : Fin n → LocPl ψ S T M M') (x : WO S T) : ℂ :=
  if IsHalf (∑ i, (L i).q.e) x then ∏ i, (L i).Φ.1 ((ofSplit (L i).q).down (L i).FS (L i).FT x) else 0

end GlobalTheory.SeeSaw

end
end

section

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LatPair GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

variable {D : D7} {u : D.what₂.Word}

structure XPart (D : D7) (u : D.what₂.Word) where
  c : GlobalTheory.ChainOnto.Com D
  top : StAt D.sp.X'
  x : ∀ j, DefSp (D.sp.X j)
  k : ∀ j, KerDat (D.sp.X j) (D.sp.X (j + 1))
  Lz : HSp D
  oT : ∀ n, n = D.R.m → OrthDec (D.sp.X n) D.sp.X' Lz
  Ram : ∀ j, Submodule ℂ (Col D u j)
  rd : ∀ j, Col D u j → (D.mem u).C.Y j → GA D (D.sp.X j) → ℂ
  eT : (D.mem u).P.Mt →ₗ[ℂ] top.st.CC c

@[reducible] def XPart.geo (a : XPart D u) (bot : StAt (D.sp.Y 0)) (mid : ℕ → GlobalTheory.ChainOnto.PiLocalization₂ D) : Geo D := ⟨a.c, bot, mid, a.top⟩



structure YPart (a : XPart D u) where
  bot : StAt (D.sp.Y 0)
  mid : ℕ → GlobalTheory.ChainOnto.PiLocalization₂ D
  p : ∀ j, GlobalTheory.ChainOnto.Step a.c ((a.geo bot mid).st j) ((a.geo bot mid).st (j + 1))
  pT : ∀ j, j + 2 * 0 + 2 = D.R.m → GlobalTheory.ChainOnto.Step a.c ((a.geo bot mid).st (j + 1)) a.top.st
  t : ∀ j, GA D ((a.geo bot mid).st j).V
  bes : ∀ j ρ, j + 2 * ρ + 2 = D.R.m → BesAt ((a.geo bot mid).st j).V (D.sp.X j) ρ
  jac : ∀ j ρ, j + 2 * ρ + 2 = D.R.m → JacAt ((a.geo bot mid).st (j + 1)).V (D.sp.X (j + 1)) ρ
  sBF : ∀ j ρ h, StepBF a.c.ψ ((bes j ρ h).lev (a.x j).vol) ((jac j ρ h).lev (a.x (j + 1)).vol)
  sFB : ∀ j σ h, StepFB a.c.ψ ((jac j (σ + 1) h).lev (a.x (j + 1)).vol)
    ((bes (j + 1 + 1) σ (idx_step h)).lev (a.x (j + 1 + 1)).vol)
  lnk : ∀ j σ h, Link ((bes j (σ + 1) h).lev (a.x j).vol) (bes (j + 1 + 1) σ (idx_step h)).L (bes (j + 1 + 1) σ (idx_step h)).ζ
  vL : ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), VolM D (bes (j + 1 + 1) σ (idx_step h)).L.rank (D.sp.X (j + 1)).rank

section Off

open GlobalTheory.FinPl

structure OffX (a : XPart D u) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ι : Type) where
  p : ι → SplitPt D k
  I : List ι
  q : Unif k
  χ : ι → AddChar k Circle
  hχ : ∀ i, HasConductor (χ i) 1
  β : ∀ j i, Frame (p i) (D.sp.X j) (Fin (D.sp.X j).rank)
  Q : ∀ j, ι → Pair k (Fin (D.sp.X j).rank)
  cT : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ
  cG : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ
  ζ₀ : Fin a.Lz.rank → D.host.E
  γ : ∀ i, Frame (p i) D.sp.X' (Fin D.sp.X'.rank)
  γ₀ : ∀ n, n = D.R.m → ∀ i, Frame (p i) (D.sp.X n) (Fin D.sp.X'.rank ⊕ Fin 1)

variable {a : XPart D u} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}

def OffX.atT (o : OffX a k ι) (v : Pl D) : Prop := ∃ i, v = (o.p i).v

end Off

section AtLevel

open GlobalTheory.LocMod

structure GX (a : XPart D u) (ζ₀ : Fin a.Lz.rank → D.host.E) (PP : Formalism.L2.DIV.Pl D.host.E) where
  k : Type
  [fld : Field k]
  [val : ValuativeRel k]
  [top : TopologicalSpace k]
  [loc : IsNonarchimedeanLocalField k]
  [mea : MeasurableSpace k]
  [bor : BorelSpace k]
  ν : Measure k
  unitVol : IsUnitVol ν
  q : GlobalTheory.FinPl.SplitPt D k
  idem : Formalism.L2.NTheta.IsIdemAt q.e PP
  unit : q.UnitAA
  s : ℕ
  hs : s + 1 + 1 = D.R.m
  S : SymData k s D.R.k
  char : (ofSplit q).IsChar a.c.ψ S.ψ
  mu : ∀ j, 1 ≤ j → j ≤ D.R.m → (ofSplit q).IsComp (a.c.chS j)⁻¹ (S.μ j)
  FX : ∀ j, j ≤ s + 1 → Frame k (D.sp.X j).rank (XIx (Fin D.R.k) (Fin D.R.t) j)
  FT : Frame k D.sp.X'.rank (Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2))
  FM : Frame k (D.sp.X (s + 1 + 1)).rank (Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ⊕ Unit)
  z₀ : Fin a.Lz.rank → k
  z₀_unit : ∃ c : k, valuation k c = 1 ∧ z₀ = c • fun i => (ofSplit q).pr (ζ₀ i)
  last : FM.β = fromCols ((a.oT (s + 1 + 1) hs).iA.map (ofSplit q).pr * FT.β)
    (Matrix.of fun r _ => ((a.oT (s + 1 + 1) hs).iB.map (ofSplit q).pr *ᵥ z₀) r)
  latX : ∀ j hj (y : XIx (Fin D.R.k) (Fin D.R.t) j → k), (∀ i, y i ∈ 𝒪[k]) ↔
    (fun i => q.sec (((FX j hj).β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV (D.sp.X j) (a.x j).L (· = q.v)
  latM : ∀ y : Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ⊕ Unit → k, (∀ i, y i ∈ 𝒪[k]) ↔
    (fun i => q.sec ((FM.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV (D.sp.X (s + 1 + 1)) (a.x (s + 1 + 1)).L (· = q.v)
  frameTop : ∃ e : Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ≃ Fin D.sp.X'.rank,
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧ MovedTo (ofSplit q) D.sp.X' 1 a.top.β (FT.β.submatrix id e.symm)
  cg : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ
  cg_mid : ∀ j c (H : j + 1 + c = s), (ofSplit q).IsCombAt a.c.ψ (FX j (by omega)) (FX (j + 1) (by omega)) (cg j)
    ((S.T (Fin D.R.t)).entry S.ψ ν j c H 1 1)
  cg_pen : (ofSplit q).IsCombAt a.c.ψ (FX s (by omega)) (FX (s + 1) le_rfl) (cg s)
    fun x₀ => (S.T (Fin D.R.t)).Psi 1 x₀ (S.y0 (Fin D.R.t))
  cg_top : (ofSplit q).IsCombAt a.c.ψ (FX (s + 1) le_rfl) FM (cg (s + 1))
    ((S.T (Fin D.R.t)).xiTop (box _ (1 : kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk (S.y0 (Fin D.R.t))))

attribute [instance] GX.fld GX.val GX.top GX.loc GX.mea GX.bor

variable {a : XPart D u} {ζ₀ : Fin a.Lz.rank → D.host.E}

end AtLevel

section World

open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Core.Rk

variable {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} (w : World I l Z) {v : B.Word}
  (a : XPart (I.rec7 l Z) v) {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
  (o : OffX a k ι) (G : ∀ PP : a.c.Pg, GX a o.ζ₀ PP.1)

end World

end GlobalTheory.SeeSaw

end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod ValuativeRel
open GlobalTheory.PosOne (toOne Covers)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.QPl.Model

section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

def sph (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n]
    [DecidableEq n] : Level (GL n k) := ⟨KO k n, 1⟩




theorem exists_haar (ν : Measure k) [ν.IsAddHaarMeasure] (n : Type) [Fintype n] [DecidableEq n] :
    ∃ m : Measure (GL n k), m.IsHaarMeasure ∧ m (KO k n) = 1 := by
  obtain ⟨h0, _, _, h1, h2, -⟩ := volGL_haar k n ν
  haveI : BorelSpace (GL n k) := h0
  haveI := (GlobalTheory.RootExchangeFixed.nonarchimedeanLocalField_secondCountable_t2Space (k := k)).2
  let K : TopologicalSpace.PositiveCompacts (GL n k) := ⟨⟨KO k n, h1⟩, by rw [h2.interior_eq]; exact ⟨1, one_mem _⟩⟩
  exact ⟨Measure.haarMeasure K, inferInstance, Measure.haarMeasure_self⟩


end Local

variable {D : D7}

theorem exists_gl {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (V : HSp D) {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k V.rank Y) :
    ∃ gl : GL Y k →* GA D V, ∀ g, (ofSplit q).IsLoc F (gl g) g :=
  let ⟨gl, h1, h2⟩ := GlobalTheory.GlEmbed.exists_gl D k q V Y F.β F.γ F.βγ F.γβ
  ⟨gl, fun g => ⟨h1 g, h2 g⟩⟩



end GlobalTheory.QPl.Model
end
end

section

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod ValuativeRel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

variable {D : D7} {c : Comm D}

def withMu {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {s κ : ℕ} (S : SymData k s κ)
    (μ : ℕ → kˣ →* ℂˣ) (h : ∀ j, IsTame (μ j)) : SymData k s κ := { S with μ := μ, tame := h }

def VCom.withCG (v : VCom c) (a : ℕ → ℂ) : VCom c := { v with cG := a }

def Comm.VolLast (c : Comm D) : Prop :=
  ∀ j (h : j + 2 * 0 + 2 = D.R.m), (c.vol (j + 1)).μ = Measure.map (c.jac j 0 h).d.emb0 (c.x (j + 1)).vol.μ

def IntIn {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k)
    (S : HSp D) {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k S.rank Y) (L : GlobalTheory.FinPl.Lat S) : Prop :=
  ∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((F.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S L (· = q.v)

structure GLoc (v : VCom c) where
  k : Type
  [fld : Field k]
  [val : ValuativeRel k]
  [top : TopologicalSpace k]
  [loc : IsNonarchimedeanLocalField k]
  [mea : MeasurableSpace k]
  [bor : BorelSpace k]
  ν : Measure k
  unitVol : IsUnitVol ν
  q : GlobalTheory.FinPl.SplitPt D k
  unit : q.UnitAA
  s : ℕ
  hs : s + 1 + 1 = D.R.m
  S : SymData k s D.R.k
  char : (ofSplit q).IsChar c.ψ S.ψ
  FX : ∀ j, j ≤ s + 1 → Frame k (c.X j).rank (XIx (Fin D.R.k) (Fin D.R.t) j)
  FT : Frame k c.T.rank (Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2))
  FM : Frame k (c.X (s + 1 + 1)).rank (Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ⊕ Unit)
  FY : ∀ j a, j + a = s + 1 → Frame k (c.V j).rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin a)
  sc : ℕ → k
  sc_unit : ∀ j, valuation k (sc j) = 1
  sc_step : ∀ j, sc (j + 1 + 1) = sc j * (ofSplit q).xi
  hz_unit : ∀ j ρ h, valuation k ((ofSplit q).hz (c.B j ρ h)) = 1
  bes : ∀ j ρ h a (ha : j + a = s + 1), (ofSplit q).IsBesFrame (c.B j ρ h) (sc j) (FX j (by omega)) (FY j a ha)
  jac : ∀ j ρ h a (ha : j + 1 + a = s + 1), (ofSplit q).IsJacFrame (c.J j ρ h) (sc j)
    ((ofSplit q).hz (c.B j ρ h)) (FX (j + 1) (by omega)) (FY (j + 1) a ha)
  z₀ : Fin c.Lz.rank → k
  last : FM.β = fromCols ((c.oT (s + 1 + 1) hs).iA.map (ofSplit q).pr * FT.β)
    (Matrix.of fun r _ => ((c.oT (s + 1 + 1) hs).iB.map (ofSplit q).pr *ᵥ z₀) r)
  tau : ∀ h, (v.τ s h).map (ofSplit q).pr *ᵥ z₀ = (-((ofSplit q).xi * sc s)) • fun i => (ofSplit q).pr ((c.bes s 0 h).ζ i)
  latX : ∀ j hj, IntIn q (c.X j) (FX j hj) (c.x j).L
  latM : IntIn q (c.X (s + 1 + 1)) FM (c.x (s + 1 + 1)).L
  latY : ∀ j a ha, IntIn q (c.V j) (FY j a ha) (v.N j)
  latT : IntIn q c.T FT v.NT

  eg : ∀ j, WO (c.V j) (c.V (j + 1)) →₀ ℂ
  eg_is : ∀ j a (H : j + a = s), (ofSplit q).IsCombAt c.ψ (FY j (a + 1) (by omega)) (FY (j + 1) a (by omega)) (eg j)
    ((S.T (Fin D.R.t)).Phi j a H)
  egT : WO (c.V (s + 1)) c.T →₀ ℂ
  egT_is : (ofSplit q).IsCombAt c.ψ (FY (s + 1) 0 rfl) FT egT (S.T (Fin D.R.t)).PhiTop

  cg : ∀ j, WO (c.X j) (c.X (j + 1)) →₀ ℂ
  cg_mid : ∀ j a (H : j + 1 + a = s), (ofSplit q).IsCombAt c.ψ (FX j (by omega)) (FX (j + 1) (by omega)) (cg j)
    ((S.T (Fin D.R.t)).entry S.ψ ν j a H 1 1)
  cg_pen : (ofSplit q).IsCombAt c.ψ (FX s (by omega)) (FX (s + 1) le_rfl) (cg s)
    fun x₀ => (S.T (Fin D.R.t)).Psi 1 x₀ (S.y0 (Fin D.R.t))
  cg_top : (ofSplit q).IsCombAt c.ψ (FX (s + 1) le_rfl) FM (cg (s + 1))
    ((S.T (Fin D.R.t)).xiTop (box _ (1 : kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk (S.y0 (Fin D.R.t))))

attribute [instance] GLoc.fld GLoc.val GLoc.top GLoc.loc GLoc.mea GLoc.bor

variable {v : VCom c}

def GLoc.Mat (G : GLoc v) (j a : ℕ) (ha : j + a = G.s + 1) (g : GA D (c.V j))
    (x : GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin a) G.k) : Prop :=
  (mt (c.V j) g).map G.q.pr = (G.FY j a ha).β * x.val * (G.FY j a ha).γ

structure GPin {n : ℕ} (G : Fin n → GLoc v) : Prop where
  inj : Function.Injective fun i => (G i).q.v
  places : ∀ p, p ∈ v.gP ↔ ∃ i, p = (G i).q.v
  lev : ∀ j, j < D.R.m → ∀ g, g ∈ v.JG j ↔ g ∈ GlobalTheory.FinPl.grpAt (c.V j) (· ∈ v.gP) ∧
    ∀ i a ha x, (G i).Mat j a ha g x → x ∈ (((G i).S.T (Fin D.R.t)).lev j a ha).J
  eG : ∀ j, j + 1 < D.R.m → ∀ f, IsThetaFunO c.ψ _ _ f → comb c.ψ _ _ (v.eG j) f =
    (List.finRange n).foldr (fun i f' => comb c.ψ _ _ ((G i).eg j) f') f
  eGT : ∀ j h, ∃ e : Fin n → WO (c.V (j + 1)) c.T →₀ ℂ, (∀ i, HEq (e i) (G i).egT) ∧
    ∀ f, IsThetaFunO c.ψ _ _ f → comb c.ψ _ _ (v.eGT j h) f = (List.finRange n).foldr (fun i f' => comb c.ψ _ _ (e i) f') f
  dG : ∀ j, j < D.R.m → ∀ f, IsThetaFunO c.ψ _ _ f → comb c.ψ _ _ (v.dG j) f =
    (List.finRange n).foldr (fun i f' => comb c.ψ _ _ ((G i).cg j) f') f

def GLoc.Chars (G : GLoc v) (t : Tup c) : Prop :=
  ∃ μ : ℕ → G.kˣ →* ℂˣ, (∀ j, IsTame (μ j)) ∧ (∀ j (x : G.kˣ), valuation G.k (x : G.k) = 1 → μ j x = G.S.μ j x) ∧
    (∀ j ρ h, (ofSplit G.q).IsComp (t.sBF j ρ h).χV⁻¹ (μ (j + 1)) ∧
      ∃ μ', (ofSplit G.q).IsComp (t.sBF j ρ h).χW μ' ∧ ∀ x : G.kˣ, valuation G.k (x : G.k) = 1 → μ' x * μ (j + 1) x = 1) ∧
    ∀ j σ h, (ofSplit G.q).IsComp (t.sFB j σ h).χV⁻¹ (μ (j + 1 + 1)) ∧
      ∃ μ', (ofSplit G.q).IsComp (t.sFB j σ h).χW μ' ∧ ∀ x : G.kˣ, valuation G.k (x : G.k) = 1 → μ' x * μ (j + 1 + 1) x = 1

def GLam {n : ℕ} (G : Fin n → GLoc v) (j : ℕ) (g : GA D (c.V j)) (a : ℂ) : Prop :=
  ∃ (b : Fin n → ℕ) (hb : ∀ i, j + b i = (G i).s + 1) (x : ∀ i, (((G i).S.T (Fin D.R.t)).lev j (b i) (hb i)).J),
    (∀ i, (G i).Mat j (b i) (hb i) g (x i).1) ∧ a = ∏ i, ((((G i).S.T (Fin D.R.t)).lev j (b i) (hb i)).lam (x i) : ℂ)

end GlobalTheory.SeeSaw

end
end

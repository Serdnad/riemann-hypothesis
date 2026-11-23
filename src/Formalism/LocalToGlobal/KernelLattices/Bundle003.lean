module

public import Formalism.LocalToGlobal.AlgebraicTheory.StatementKer
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
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
open scoped BigOperators
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker

open Formalism.MainNotions Formalism.L2.Col
open Formalism.L2.Th1.H (cmL CmOK matH stdLat pow4 imgLat relIdx IsIsom)
open Formalism.L2.Th1.E (IntCurve curveL)
open Formalism.L2.Th1.GD (LocNorm)
open Formalism.L2.AlgTh (KerStd lamF)

section Defs

variable {D : D7} {X : Fields} (s : Seam D X)

def Seam.flatV (a b : ℕ) : (DVar X.Tau a b → ℂ) ≃ₗ[ℂ] TaylorLogMetric.VC D a b where
  toFun z := fun τ i j => z (s.iT.symm τ, i, j)
  invFun w := fun k => w (s.iT k.1) k.2.1 k.2.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv z := by funext k; simp
  right_inv w := by funext τ i j; simp

def Seam.laF (T : TaylorLogMetric.Tor D) {a b : ℕ} (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) :
    AddSubgroup (DVar X.Tau a b → ℂ) :=
  (TaylorLogMetric.La D T L L').comap (s.flatV a b).toLinearMap.toAddMonoidHom

def Seam.StdAtP (p : ℕ) {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) : Prop :=
  TaylorLogMetric.EqAt D p (StandardLatticesGL3.stdL D n) (s.lat N)

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)

def Base.IsCm (a₀ : ℕ) (b₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0) : Prop :=
  B.L = cmL a₀ b₀ D.host.d ha hd lam hlam ∧ B.ω₀ = lam * a₀

def Base.latA : AddSubgroup (Fin 4 × D.what₂.Tau → ℂ) :=
  imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM)

def Base.KappaAt (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) : Prop :=
  ∀ u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ),
    IsIsom (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau))
      (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) →
    relIdx (stdLat B.L (Fin 4 × D.what₂.Tau)) (imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) B.latA) ≠ 0 →
    ¬ p ∣ relIdx (stdLat B.L (Fin 4 × D.what₂.Tau)) (imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) B.latA) →
    relIdx (imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) B.latA) (stdLat B.L (Fin 4 × D.what₂.Tau)) ≠ 0 →
    ‖ι B.kappa‖ ^ 2 * ‖ι (LinearMap.det (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)))‖ = 1

def Base.LocNormMM (a₀ : ℕ) (b₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0) (p : ℕ) [Fact p.Prime]
    (ι : ℂ ≃+* ℂ_[p]) : Prop :=
  LocNorm a₀ b₀ D.host.d ha hd lam hlam (hOne B.L D.what₂.Tau) B.lamM B.thMM p ι

end Defs

def KappaOn (Q : D7 → ℕ → Prop) (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), Q D p → B.KappaAt p ι

def KappaAll (D : D7) : Prop := KappaOn (fun _ _ => True) D

def KappaSplit (D : D7) : Prop := KappaOn SplitK D

def LamTie : Prop :=
  ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)
    (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), s.Ok →
    lamF (ambOf s B χ cD) N N' = s.laF B.tor (s.lat N) (s.lat N')

def KerStdLatOn (Q : D7 → ℕ → Prop) : Prop :=
  ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)
    (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]),
    s.Ok → TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → TaylorLogMetric.IsChi D χ → CmOK a₀ b₀ c₀ D.host.d →
    (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ →
    Even a → Even b → IsSdLat N → IsSdLat N' → s.StdAtP p N → s.StdAtP p N' →
    ¬ (p : ℤ) ∣ NumberField.discr X.E → (∀ τ, ‖ι (cD τ)‖ ≤ 1) → 5 ≤ p → Q D p →
    KerStd (ambOf s B χ cD) N N' a₀ b₀ c₀ ha hd lam hlam p ι

def KerStdExOn (Q : D7 → ℕ → Prop) : Prop :=
  ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ),
    s.Ok → TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → TaylorLogMetric.IsChi D χ →
    ∃ (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ D.host.d ∧
      (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ ∧
      ∀ (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]),
        Even a → Even b → IsSdLat N → IsSdLat N' → s.StdAtP p N → s.StdAtP p N' →
        ¬ (p : ℤ) ∣ NumberField.discr X.E → (∀ τ, ‖ι (cD τ)‖ ≤ 1) → 5 ≤ p → Q D p →
        KerStd (ambOf s B χ cD) N N' a₀ b₀ c₀ ha hd lam hlam p ι

def KerStdEx : Prop := KerStdExOn fun _ _ => True

end Formalism.L2.Ker
end
end

section

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Th1.H Formalism.MainNotions

section Field

variable {X : Fields} (A : Amb X) (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ)

end Field


section KR

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (cD : D.what₂.Tau → ℂ) (D0 : ℕ) (α : TaylorLogMetric.Mono D 1 1)

end KR

section Norm

variable {D : D7} {X : Fields} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)
  (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D0 : ℕ)

end Norm

section Tied

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}

def KerEntTied.VQTie {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) (lam : ∀ (_ : D.what₂.Word) (i : ℕ), D.what₂.Tau → DomWeight (D.R.N i))
    (sh : D.what₂.Word → ℕ → D.what₂.Tau → ℤ) : Prop :=
  ∀ u μ i, i ≤ D.R.m → ∀ c : (D.chTw u μ).cls i, Set.range (t.ent.ev u μ i c) =
    {f | ∃ P ∈ DIV.VV D.what₂.LL (lam u i), f = evG ((t.O u μ).frm i) (sh u i) D.what₂.embLL P}

def KerEntTied.WtTie {ex : Extra D L hT Gi Gl K Y cX} (_t : KerEntTied ex) (lam : ∀ (_ : D.what₂.Word) (i : ℕ), D.what₂.Tau → DomWeight (D.R.N i))
    (sh : D.what₂.Word → ℕ → D.what₂.Tau → ℤ) (n : D.what₂.Word → ℕ → D.what₂.Tau → ℕ) : Prop :=
  ∀ u μ i, i < D.R.m → (∀ τ r, (lam u i τ).natW r + n u i τ = nuT D u i τ r) ∧ (∀ τ, sh u i τ + (D.chTw u μ).sSharp i τ = n u i τ) ∧
    (∀ τ, sh u (i + 1) τ = -(D.chTw u μ).sDiv i τ) ∧ JetInVV D.what₂.LL (lam u i) (lam u (i + 1)) (n u i)

end Tied

section Choice

end Choice


open Classical in
def degAt {ι : Type} {a b : ℕ} (m : DVar ι a b →₀ ℕ) (τ : ι) : ℕ := (m.support.filter fun k => k.1 = τ).sum fun k => m k

def Amb.JetsRatDeg {X : Fields} (A : Amb X) (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ) (dg : X.Tau → ℕ) : Prop :=
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x : HomE X.E a b), InRange Sall D c N N' x →
    ∀ m : DVar X.Tau a b →₀ ℕ, (∀ τ, degAt m τ = dg τ) → ∃ k : X.K, A.σ₀ k = (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd Sall N N' c x) m

def JetLocal : Prop :=
  ∀ (K : Type) [Field K] [Infinite K] (ι : Type) [Fintype ι] (a b : ℕ) (lam : ι → DomWeight a) (n : ι → ℕ) (J J' : (DVar ι a b →₀ ℕ) → K),
    (∀ m, (∀ τ, degAt m τ = ∑ r, ((lam τ).natW r + n τ)) → J m = J' m) → ∀ P ∈ DIV.VV K lam, jetMap J n P = jetMap J' n P

def KerEntTied.RK {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) : Prop :=
  ∀ u μ, Formalism.BasicNotions.DV.Used D μ → ∀ i, i < D.R.m → ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)) (m : DVar D.what₂.Tau (D.R.N i) (D.R.N (i + 1)) →₀ ℕ),
    (∀ τ, degAt m τ = ∑ r, nuT D u i τ r) →
    ∃ k : D.what₂.LL, D.what₂.embLL k = ((D.chTw u μ).rhoDet i c * (D.chTw u μ).rhoDet' i c') * jetC (t.O u μ).dgen ((t.O u μ).Th i c c') m

end Formalism.L2.Ker
end
end

section

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Gen

variable {X : Fields} {Pr : Primes X} {m : ℕ}

def OffG (Pr : Primes X) (v : HeightOneSpectrum (𝓞 X.E)) : Prop := ∀ i, ((Pr.g i : ℕ) : 𝓞 X.E) ∉ v.asIdeal

def MuValTie (Ch : Chars X Pr m) (G : ChGlob X m) : Prop :=
  ∀ (j : Fin m) (v : HeightOneSpectrum (𝓞 X.E)), OffG Pr v → G.σ₀ ((Ch.muVal j v : X.Kˣ) : X.K) = (((G.mu0 j).val v : ℂˣ) : ℂ)

end Gen

section Mem

variable {D : D7} {u : D.what₂.Word}

def MemLatAt (O : GL3Theta.LiftObj D (D.mem u).C) (π : 𝓞 D.host.E) : Prop :=
  letI := D.host.cmStar
  ∀ i, i ≤ D.R.m → ∃ co : (D.sp.X i).V ≃ₗ[D.host.E] (Fin (D.R.N i) → D.host.E),
    (∀ x y, stdH D.host.E (D.R.N i) (co x) (co y) = (D.sp.X i).hT x y) ∧
    (∀ y, co y ∈ (O.L0 i).1 ↔ y ∈ (D.sp.X i).L0) ∧
    ∀ (c : (D.mem u).C.cls i) y, co y ∈ (O.lat i c).1 ↔
      ∃ a ∈ D.clsLat u i c, ∃ b ∈ Formalism.HermitianLatticesTheory.dual (D.sp.X i).hT (D.clsLat u i c),
        y = a + D.host.conj (π : D.host.E) • b

def IsMemAt (O : GL3Theta.LiftObj D (D.mem u).C) (π : 𝓞 D.host.E) : Prop :=
  O.mt = D.muTil ∧ (∀ i c, O.dt i c = D.detCls u i c) ∧ MemLatAt O π

end Mem

section Comparison₂

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}

def KerEntTied.PiSide {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) : Prop :=
  ∀ u, t.seam.iE ((t.Pr.piT (t.word u) : 𝓞 t.X.E) : t.X.E) = ((ex.errX.piT u : 𝓞 D.host.E) : D.host.E)

def KerEntTied.memObj {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) (u : D.what₂.Word) : GL3Theta.LiftObj D (D.mem u).C :=
  D.memberColumns_twistedChain_base u ▸ t.O u D.what₂.mu0

def KerEntTied.MemSide {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) : Prop :=
  ∀ u, (t.memObj u).IsMem → IsMemAt (t.memObj u) (ex.errX.piT u)

structure KerEntTied.ChTie {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) : Prop where

  ch_ok : t.Ch.Ok

  muVal : MuValTie t.Ch t.glob

  piT : t.PiSide

  mem : t.MemSide

end Comparison₂

end Formalism.L2.Ker
end
end

section

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def twMt (D : D7) (ξ : D.Dt →* ℂˣ) : ℕ → D.Dt →* ℂˣ := fun j =>
  if 1 ≤ j ∧ j ≤ D.R.m then D.muTil j * ξ else D.muTil j

section Comparison₂

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}

def KerEntTied.IsUnitNormOneQuotient {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) (q : (AfE t.X.F t.X.E)ˣ →* D.Dt) : Prop :=
  Function.Surjective q ∧
  ∀ (k : t.X.Eˣ) (z : unitary D.host.E), (z : D.host.E) * D.host.conj (t.seam.iE (k : t.X.E)) = t.seam.iE (k : t.X.E) →
    q (ratId t.X.F t.X.E k) = D.e1Dt z

def KerEntTied.XiTil {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) (q : (AfE t.X.F t.X.E)ˣ →* D.Dt) (μ : D.what₂.Tup)
    (ξ : D.Dt →* ℂˣ) : Prop :=
  ∀ x, ξ (q x) = Units.map t.seam.σ₀.toMonoidHom ((t.tup μ : Chr t.X.F t.X.E t.X.K) x)

def KerEntTied.MtTwAt {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) (q : (AfE t.X.F t.X.E)ˣ →* D.Dt) (P : D.what₂.Tup → Prop) : Prop :=
  ∀ μ, μ ≠ D.what₂.mu0 → P μ → ∃ ξ : D.Dt →* ℂˣ, t.XiTil q μ ξ ∧ ∀ u, (t.O u μ).mt = twMt D ξ

def KerEntTied.MtTwOn {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) (P : D.what₂.Tup → Prop) : Prop :=
  ∃ q : (AfE t.X.F t.X.E)ˣ →* D.Dt, t.IsUnitNormOneQuotient q ∧ t.MtTwAt q P

def KerEntTied.MtTwTie {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) : Prop := t.MtTwOn fun _ => True

end Comparison₂

end Formalism.L2.Ker
end
end

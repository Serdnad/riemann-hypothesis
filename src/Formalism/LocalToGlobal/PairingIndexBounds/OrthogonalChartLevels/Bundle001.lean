module

public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.Bundle003
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.PtStep0
public import Formalism.LocalToGlobal.GroupLattices.LevelCharts.FiniteClassSetOfFiniteIndex
public import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.Bundle003
public import Formalism.LocalToGlobal.GroupLattices.StdSubAtOfRing
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
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.UG Formalism.MainNotions.G Formalism.FrobeniusOrbits Formalism.MainNotions.FormalGroupSystem Formalism.L2.G Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker
open scoped TensorProduct

namespace Formalism.L2.PairingIndexBounds.F

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {p : ℕ} [hp : Fact p.Prime] (D : D7) (u : D.what₂.Word) (h : D.R.MA)
  (L : IntermediateField (KO p (orderOf (zPsi D.R.toFrame h))) (Om p (orderOf (zPsi D.R.toFrame h))))
  [FiniteDimensional (KO p (orderOf (zPsi D.R.toFrame h))) L]
  (h5 : 5 ≤ p) (h2 : 2 ≤ orderOf (zPsi D.R.toFrame h)) (he : Even (orderOf (zPsi D.R.toFrame h))) (r : ℕ)
  (Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (I : LocId Lc p (nOrb (zPsi D.R.toFrame h)) (WQ p (orderOf (zPsi D.R.toFrame h))) (QQ p (orderOf (zPsi D.R.toFrame h))))
  (ψ : Formalism.L2.Herm.awayFrom₂ Lc p →* (OL p (orderOf (zPsi D.R.toFrame h)) L)ˣ) (e : ℕ)
  (c : ℕ) (hc : CloudBound D u c)
  (hg : ∀ a, D.host.g a ≠ 0)
  (hpg : ∀ a, Nat.Coprime p (D.host.g a))
  (Cb : ∀ i, i < D.R.m → Type) [∀ i hi, Finite (Cb i hi)]
  (Sx : ∀ i (hi : i < D.R.m), Cb i hi → StepX I (OL p (orderOf (zPsi D.R.toFrame h)) L)ˣ (D.mem u).A.T D.R.f (i + 1))
  (Ch : Chain (levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx))
  (hr1 : 1 ≤ r) (hr2 : 2 * r ≤ D.R.k)
  (hfin : ∀ j c', ((levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx).lev j c').FinClasses)

variable (a : 𝓞 D.host.E) (bad : Finset (HeightOneSpectrum (𝓞 D.host.F)))


include h5 h2 he r ψ e c hc Ch hr1 hr2 hfin in
def ptRec : ∀ j, (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt j →
    PtD D.host.F D.host.E (((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj j).m + 1)
  | 0, La => ptStep0 (I := I) (isUnit_det_gram0 D.sp) (k_pred D.R) (repP Lc p) a bad La.1 La.2
  | i + 1, La =>
      let X := Sx i La.1.1 La.1.2.1
      let S : StepG I (D.sp.X (i + 1)).rank :=
        { J := (D.sp.X (i + 1)).gram
          hJ := gram_herm D.sp.cm (D.sp.X (i + 1))
          hdet := gram_det_unit D.sp.cm (D.sp.X (i + 1))
          Lb := X.lev.Lb
          Uloc := X.lev.Uloc
          fr := X.fr
          U := X.lev.U
          U_eq := X.lev.U_eq }
      ptStep S (rank_step D i La.1.1) a bad La.1.2.2 La.2

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (lam : TaylorLogMetric.Qbar →+* ℂ_[p])
  (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
  (Ξ₀ : ∀ j, (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt j → (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt (j + 1) → Formalism.L2.Col.HomE D.host.E
    (((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj j).m + 1)
    (((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj (j + 1)).m + 1) → ℂ)
  (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ)



include h5 h2 he r ψ e c hc Ch hr1 hr2 hfin in
def twC (v : (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pl) (s : Fin ((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).G.P.n' v)) : (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).G.P.Qq v →+* ℂ_[p] :=
  letI := algKfC (cembCL D u h L h5 h2 he r Lc I ψ e).toCEmb
  tw (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin) ℂ_[p] v s


variable {g : Formalism.MainNotions.GL3Theta.G1 p} (hLT : LTIso g)


variable (hst : FinStab (levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx))

end Formalism.L2.PairingIndexBounds.F
end
end

section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms
open scoped TensorProduct

namespace Formalism.L2.PairingIndexBounds.F

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure Lev0Data (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) where
  A : LocAt D.host.F D.host.E (D.R.N 0) (D.gat u w h)
  J : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E
  Lb : Submodule (𝓞 D.host.E) (Fin (D.R.N 0) → D.host.E)
  Uloc : ∀ v : HeightOneSpectrum (𝓞 D.host.F),
    Subgroup (GL (Fin (D.R.N 0)) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F))

def lev0AtOf {D : D7} {X : Formalism.L2.Herm.Herm0 D} {T : ∀ u : D.what₂.Word, Forms0 D u} {Gt : GatTies D} {c : LatCmp D}
    (K : CmpTied D X T Gt c) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) : Lev0Data D u w h where
  A := locAt X u w h K.B
  J := gramN D 0 (Nat.zero_le _)
  Lb := (T u).cls0.lev.Lb
  Uloc := (T u).cls0.lev.Uloc

def lev0At {D : D7} {Gt : GatTies D} {c : LatCmp D} (Gd : GroupCompatibilityAll D Gt c) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) : Lev0Data D u w h :=
  lev0AtOf Gd.cmp u w h

def lev0AtOf_compatible {D : D7} {X : Formalism.L2.Herm.Herm0 D} {T : ∀ u : D.what₂.Word, Forms0 D u} {Gt : GatTies D} {c : LatCmp D}
    (K : CmpTied D X T Gt c) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    CmpTie ((T u).cls0).lev (embT D) D.what₂.embLL (tEL D) (D.gat u w h) (c.embW u w h)
      (lev0AtOf K u w h).A (Gt.gat_pos u w h)
      (fun x cl z => (D.fm u).emb 0 x cl (((T u).val0).eY.symm z))
      ((T u).cls0).y (c.cmp u w h) :=
  K.tie u w h

end Formalism.L2.PairingIndexBounds.F

end
end

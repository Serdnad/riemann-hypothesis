module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle019
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.Bundle001
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TrueWtAddSSNonneg
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsMulOfApprox
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RenameMemDualWeyl
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle011
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle008
public import Formalism.LocalToGlobal.InertKernelTheory.ScalG
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle011
import Formalism.LocalToGlobal.InertKernelTheory.DefsRepFrame
import Formalism.LocalToGlobal.InertKernelTheory.FirstKernelGeneratorOfOrthogonal
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.OrbitOfPts

@[expose] public section

section

noncomputable section

namespace GlobalTheory.TwV.DelA

open Formalism.BasicNotions NumberField Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG
open Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)

theorem rkS {j : ℕ} (hN : RankTie X D j) : (X.Pj j).m + 1 = D.R.N j := (rankJ X j).trans hN.1.symm

theorem rkT {j : ℕ} (hN : RankTie X D j) : (X.Pj (j + 1)).m + 1 = D.R.N (j + 1) := (rankJ X (j + 1)).trans hN.2.symm

theorem rk_le {j : ℕ} (hN : RankTie X D j) : D.R.N j ≤ D.R.N (j + 1) := by
  rw [hN.1, hN.2]; exact NN_le X j

def zT {n : ℕ} (f : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (τ : D.what₂.Tau) : Matrix (Fin n) (Fin n) ℂ :=
  if IsOddPos (pos.symm τ).2 then ((f τ)⁻¹).transpose.submatrix id Fin.rev else f τ

def dfr {j : ℕ} (hN : RankTie X D j) (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ)
    (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ) (τ : D.what₂.Tau) : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) ℂ :=
  (d τ * f' τ).submatrix id (Fin.castLE (rk_le X D hN))

def evD {Kc : Type} [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) {j : ℕ} (hN : RankTie X D j)
    (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ)
    (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ) : DA X Kc j →+* Kc :=
  MvPolynomial.eval₂Hom
    (MvPolynomial.eval fun y : Var (X.Pj (j + 1)) =>
      ι (zT X D pos f' (pos ⟨y.1, y.2.1⟩) (Fin.cast (rkT X D hN) y.2.2.1) (Fin.cast (rkT X D hN) y.2.2.2)))
    (fun z : X.ZA j => ι (d (pos ⟨z.1, z.2.1⟩) (Fin.cast hN.1.symm z.2.2.1) (Fin.cast hN.2.symm z.2.2.2)))

def valZ (i : ℕ) {n : ℕ} (h : (X.Pj i).m + 1 = n) (R : XR (X.Pj i) ℂ) (f : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  MvPolynomial.eval (fun y : Var (X.Pj i) => zT X D pos f (posJ X D pos i ⟨y.1, y.2.1⟩) (Fin.cast h y.2.2.1) (Fin.cast h y.2.2.2)) R

def eT (i : ℕ) (τ : D.what₂.Tau) : ℤ := eAt (X.Pj i) ((posJ X D pos i).symm τ).1 ((posJ X D pos i).symm τ).2

def cT1 (j : ℕ) (τ : D.what₂.Tau) : ℤ := cMu X j (pos.symm τ).1 (pos.symm τ).2

end GlobalTheory.TwV.DelA

end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong

namespace GlobalTheory.CongL

def UnitaryAutomorphicTypeClass : Type 1 :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l a : ℕ), HeightOneSpectrum (𝓞 E) → Submodule ℂ (UA E a → ℂ) → Prop

def FieldOK (E : Type) [Field E] [NumberField E] [IsCMField E] (l d : ℕ) [Fact l.Prime] : Prop :=
  ImQ E d ∧ SqAt d l ∧ Even (Module.finrank ℚ (maximalRealSubfield E)) ∧
    ∀ w : HeightOneSpectrum (𝓞 E), ¬ IsSplitAt w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∧
      Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsCMField E] {l : ℕ} [Fact l.Prime] {a : ℕ}

def AutOffT (T : Finset (HeightOneSpectrum (𝓞 E))) (U : Submodule ℂ (UA E a → ℂ)) : Prop :=
  IsAutRepU U ∧ ∀ w, ¬ IsSplitAt w → w ∉ T → IsUnramU U w

def SatU (U : Submodule ℂ (UA E a → ℂ)) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) : Prop :=
  ∃ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ ∧
    GlobalTheory.LFun.HasSatGL w σ.ρ B

def SphOffU (w₀ : HeightOneSpectrum (𝓞 E)) (S : Finset (HeightOneSpectrum (𝓞 E))) (U : Submodule ℂ (UA E a → ℂ)) : Prop :=
  ∀ w, IsSplitAt w → Apart w w₀ → ApartAll S w → ∃ B, SatU U w B

def GenAtU (Gen : ℕ → ℕ → Multiset ℂˣ → Prop) (U : Submodule ℂ (UA E a → ℂ)) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ B, SatU U w B → Gen a (normV w) B

def CrysDRU (U : Submodule ℂ (UA E a → ℂ)) (ι : Qbar l ≃+* ℂ) (r : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l))
    (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω), _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (_root_.ReciprocityTheory.Gal.Dec (F := E) A) O), Pst.Induces Bw →
    IsCrysAt P Bw (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype) ∧ IsdRAt P Bw (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype) ∧
      ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
        ∀ (lam : DomWeight a) (J : Multiset ℤ), HasWeightAt U (ι.toRingHom.comp τ) lam →
          J.map (fun n : ℤ => (n : ℂ)) = (infOfWeight lam).map (fun z => ((a : ℂ) - 1) / 2 - z) →
          IsJumpsAt P Bw (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype) τ J

def IsSysU {ι : Qbar l ≃+* ℂ} {Kw : Levels E a} {J : Type} (O : LocOps l ι Kw J) (U : Submodule ℂ (UA E a → ℂ))
    (θ : J → Qbar l) : Prop :=
  ∀ j (σ : SmIrr (GL (Fin a) ((O.pl j).adicCompletion E))),
    IsCompAlong U (locU a (O.pl j)) ((cLoc (O.pl j)).comp (locU a (O.pl j)).subtype) σ.ρ → θ j = ι.symm (O.z j σ)

end GlobalTheory.CongL

end
end

section

noncomputable section

namespace GlobalTheory.GO

open NumberField _root_.Formalism.L2.Col Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Forms

section Exp

open MvPolynomial Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint

variable {ι : Type} [Fintype ι] {a b : ℕ}

end Exp

namespace ChSrc

open Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint

variable {X : Fields} {R : Ranks} (σ : X.K →+* ℂ)

theorem jetInVV_trueWt (hc : X.Tau → HCParam R) {i : ℕ} (hi : i < R.m) : JetInVV X.K (trueWt hc i) (trueWt hc (i + 1)) (nuEnd hc i) := by
  have hab : R.N i < R.N (i + 1) := by
    simp only [Ranks.N]
    nlinarith
  have hW : WtCompat hab (trueWt hc i) (trueWt hc (i + 1)) (sD hc i) (sS hc i) (nuEnd hc i) := by
    refine ⟨fun τ a => ?_, fun τ j hj => trueWt_new hc hi τ j (by omega), fun τ => nuEnd_cast hc hi τ⟩
    have h1 := trueWt_old hc hi τ (Fin.castLE hab.le a) (by simp)
    simp only [Fin.coe_castLE] at h1
    rw [h1]
    ring
  haveI : Infinite X.K := Infinite.of_injective (Nat.cast : ℕ → X.K) Nat.cast_injective
  intro J P hP
  exact GlobalTheory.JetPoint.jetMap_mem hab.le (nuEnd hc i) P _
    (fun ap => GlobalTheory.SubstMem.substAdj_sharp_mem X.K X.Tau _ _ hab _ _ _ _ _ hW ap P hP) J

end ChSrc

end GlobalTheory.GO
end
end

section

noncomputable section

namespace GlobalTheory.TwV.Lt

section A

open scoped Matrix
open Formalism.MainNotions.FormalGroupSystem Formalism.L2.KerInert.K1 NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker
open Formalism.L2.G.Pend (Frm)
open Formalism.L2.KerInert.RepFrame (Gm Gp)

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf]
  (M : ∀ j, X.Lt j → ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
  (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7)
  (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
  (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))

def FrameLatMapLt (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v) : Prop :=
  ∀ j, j < X.mm → ∀ (L0 : X.Lt j), L0 ∈ Formalism.L2.G.Pend.repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1),
    (X.Pj (j + 1)).IsLatTup La'.2 →
    ∀ (φ : Frm X j L0 La') (r : ℕ) (b : Fin r → Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) D.host.E),
      LocBasis D p (YYl D (large₂ j L0 La') (Lg' j L0 La')) b → Orthonormal D b →
      ∀ (i : Fin r) (v : X.Pl),
        (∀ c, ((b i).map (ρ v)).mulVec (fun x => Gm X M φ v x c) ∈ Formalism.MainNotions.G.colSpan (X.G.P.W v) (Gp X M φ v)) ∧
        (∀ c, ((b i).map (fun y => ρ v (D.host.conj y)))ᵀ.mulVec (fun x => Gp X M φ v x c) ∈
          Formalism.MainNotions.G.colSpan (X.G.P.W v) (Gm X M φ v))

end A

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert
open Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ
open Formalism.L2.KerInert.AdmLoc (pendG CurveIn XiIn)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section B

variable {p : ℕ} [Fact p.Prime] {D : D7}

def AdmGLt (X : Sys p) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7) (fd : Formalism.L2.PairingIndexBounds.F.FData X D) : Prop :=
  ∀ j, j < X.mm → ∀ (L0 : X.Lt j), L0 ∈ repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1), (X.Pj (j + 1)).IsLatTup La'.2 →
    TaylorLogMetric.admitted D _ _ (fd.kerN j L0) (fd.kerN (j + 1) La')

def ScalGLt (X : Sys p) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (fd : Formalism.L2.PairingIndexBounds.F.FData X D) (χ : TaylorLogMetric.IdE D → ℂ)
    (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ) (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) : Prop :=
  ∀ j, j < X.mm → ∀ (L0 : X.Lt j), L0 ∈ repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1), (X.Pj (j + 1)).IsLatTup La'.2 →
    Formalism.L2.KerInert.KG.scalG fd χ muT j L0 La' ∈ TaylorLogMetric.Qbar ∧
      ‖(p : ℂ_[p]) ^ Formalism.L2.KerInert.KG.expG X j L0 La' * TaylorLogMetric.lamC lam (Formalism.L2.KerInert.KG.scalG fd χ muT j L0 La')‖ ≤ 1

end B

def XiAwayLt {p : ℕ} [Fact p.Prime] (X : Sys p) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7)
    (Ξ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ) : Prop :=
  ∃ S₀ : Finset ℕ, p ∉ S₀ ∧ ∀ j, j < X.mm → ∀ (L0 : X.Lt j), L0 ∈ repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1),
    (X.Pj (j + 1)).IsLatTup La'.2 → ∀ y, IntOff S₀ (Ξ j L0 La' y)

section Law

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmb X.G)
  (hfin : ∀ j c, (X.Lv.lev j c).FinClasses)

def StabLawLt (ThR : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) ℂ_[p]) : Prop :=
  letI := wittFractionAlgebraCp p
  letI := algKfC E
  ∀ j < X.mm, ∀ (c : X.Lv.comp j) (L0 : (X.Pj j).Tup) (La' : X.Lt (j + 1)) (ε : (X.Lv.lev j c).Γ),
    (c, L0) ∈ repOf X.Lv hfin j → (X.Pj (j + 1)).IsLatTup La'.2 → (X.Lv.lev j c).smul ε L0 = L0 →
      MvPowerSeries.C ((kapG X ℂ_[p] j c ε)⁻¹) * SA X ℂ_[p] j (gamAt X j c ε) (ThR j (c, L0) La') = ThR j (c, L0) La'

end Law

section Gen

variable {p : ℕ} [Fact p.Prime] {D : D7}

def ThetaSeriesDataHypothesesBelowMaximalLevel (X : Sys p) (E : CEmbC X.G) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses)
    (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : FData X D) (χ : TaylorLogMetric.IdE D → ℂ)
    (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (cl : ℕ)
    (Ξ₀ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ)
    (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ) : Prop :=
  AdmGLt X hfin D fd ∧ Formalism.L2.KerInert.RepRec.ClAway p cl ∧ XiAwayLt X hfin D Ξ₀ ∧
    ScalGLt X hfin fd χ muT lam ∧
    ∃ ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v,
      Formalism.L2.KerInert.RepFrame.LamPosG X E D pos lam ρ ∧ Formalism.L2.KerInert.RepFrame.MInv X fd.frM ∧
      FrameLatMapLt X fd.frM hfin D (fun j La _ => fd.kerN j La) (fun j _ La' => fd.kerN (j + 1) La') ρ

def LawInLt (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (E : CEmbC X.G)
    {g : GL3Theta.G1 p} (hLT : LTIso g) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
    (fd : FData X D) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ)
    (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (Ξ₀ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ)
    (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ) : Prop :=
  letI := wittFractionAlgebraCp p
  letI := algKfC E.toCEmb
  StabLawLt X E.toCEmb hfin (thFOf X pos (FrecG E.toCEmb pos fd B χ lam SS cl Ξ₀ muT (ltC g hLT)))

end Gen


open Formalism.L2.KerInert.SecondKernelInstances in
def AdmAtEnt2 : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (Kc0 : G.Consts) (Dx : DivX D)
    (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc0 Dx cX) (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) [Fact (D.what₂.places.resChar w).Prime]
    (Fl : Fills (D.gat u w h)) (Lv : Levels Fl) (Ch : Chain Lv) (KA : TwTie.KerAtMu D ex.cmp ex.tw u μ w h Ch)
    (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _) (dG_spec : _) (om : _)
    [IsFractionRing (sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.O (sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.Kf] (E : CEmbC (sysAt Ch std vp unif eO eO_spec dG dG_spec om).G)
    (hfin : ∀ j c, ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lv.lev j c).FinClasses) (hst : FinStab (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lv)
    (g : GL3Theta.G1 (D.what₂.places.resChar w)) (hLT : LTIso g)
    (pos : (Σ v : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pl, Fin ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.P.n' v)) ≃ D.what₂.Tau)
    (Tw : TwForms D) (I : Formalism.MainNotions.G.CmpJ.CmpJIn Tw u μ w h Lv) (L0 : Formalism.L2.PairingIndexBounds.F.Lev0Data D u w h)
    (a : 𝓞 D.host.E) (bad : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ)
    (lam : TaylorLogMetric.Qbar →+* ℂ_[D.what₂.places.resChar w]) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (Ξ₀ : ∀ j, (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt j → (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (j + 1) →
      Formalism.L2.Col.HomE D.host.E (((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj j).m + 1) (((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj (j + 1)).m + 1) → ℂ)
    (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ),
    CurveIn D (D.what₂.places.resChar w) cc δ g B χ lam →
    ThetaSeriesDataHypothesesBelowMaximalLevel (sysAt Ch std vp unif eO eO_spec dG dG_spec om) E hfin pos (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad) χ lam cl Ξ₀ muT →
    XiIn (sysAt Ch std vp unif eO eO_spec dG dG_spec om) E hfin hst hLT pos (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad) B χ lam SS cl Ξ₀ muT →
    LawInLt (sysAt Ch std vp unif eO eO_spec dG dG_spec om) hfin E hLT pos (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad) B χ lam SS cl Ξ₀ muT →
    (∃ ι Rd Sr, ∀ j < D.R.m,
      TiesAt (Y := pendG (sysAt Ch std vp unif eO eO_spec dG dG_spec om) E hfin hst hLT pos (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad) B χ lam SS cl Ξ₀ muT) t u μ KA.cls KA.cmp ι Rd Sr j) →
      admitted D (sysAt Ch std vp unif eO eO_spec dG dG_spec om) (pendG (sysAt Ch std vp unif eO eO_spec dG dG_spec om) E hfin hst hLT pos (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad) B χ lam SS cl Ξ₀ muT)

def CurveEx : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ),
    TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → TaylorLogMetric.IsChi D χ →
    ∀ (p : ℕ) [Fact p.Prime], Nat.Coprime (Ideal.absNorm cc) p → 5 ≤ p → GL3Theta.InertK D p →
    ∀ lam : TaylorLogMetric.Qbar →+* ℂ_[p], ∃ (g : GL3Theta.G1 p) (_ : LTIso g), CurveIn D p cc δ g B χ lam

def dGT (D : D7) (u : D.what₂.Word) (p : ℕ) : ℕ → ℕ := fun j => if j = 0 then 0 else padicValNat p (D.mem u).C.DGam

theorem dGT_zero (D : D7) (u : D.what₂.Word) (p : ℕ) : dGT D u p 0 = 0 := by simp [dGT]

theorem dGT_spec {D : D7} {c : LatCmp D} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
    {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} [Fact (D.what₂.places.resChar w).Prime]
    {Fl : Fills (D.gat u w h)} {Lv : Levels Fl} {Ch : Chain Lv} (KA : TwTie.KerAtMu D c Tw u μ w h Ch) :
    ∀ j ≤ Fl.mm, ∀ (a : Lv.comp j) (L : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L →
      padicValNat (D.what₂.places.resChar w) (Nat.card {γ : (Lv.lev j a).Γ // (Lv.lev j a).smul γ L = L}) ≤
        dGT D u (D.what₂.places.resChar w) j := by
  intro j hj a L hL
  by_cases h0 : j = 0
  · subst h0
    rw [KA.stab_zero a L hL]
    simp [dGT, Nat.padicValNat_def]
  · have hm : j ≤ D.R.m := by rw [← KA.fl_m]; exact hj
    obtain ⟨_, hdvd⟩ := KA.stab_dvd j hm a L hL
    simp only [dGT, if_neg h0]
    exact ((by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) (D.mem u).C.DGam_pos.ne').1 (dvd_trans (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _)) hdvd)

def StdAtW (D : D7) (Gl : G.LatInst D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) : Prop :=
  ∀ v, Std (D.what₂.places.resChar w) ((D.gat u w hg).P.n' v) (D.gat u w hg).P.m (Gl.Fl u w hg).t (Gl.Fl u w hg).mm
    (Gl.Fl u w hg).c (D.gat u w hg).P.r ((Gl.Fl u w hg).TT v) ((Gl.Fl u w hg).a v) ((Gl.Fl u w hg).b v)
    ((D.gat u w hg).P.lam0 v) ((Gl.Fl u w hg).w v)

theorem fracAt {D : D7} (Gl : G.LatInst D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) : IsFractionRing (D.gat u w hg).O (D.gat u w hg).Kf :=
  ((D.gat u w hg).P.setting (Gl.vOf u w hg 0)).frac_O

end GlobalTheory.TwV.Lt

end
end

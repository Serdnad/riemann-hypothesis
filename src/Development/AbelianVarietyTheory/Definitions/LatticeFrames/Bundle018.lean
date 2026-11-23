module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle016
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle006
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle011
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
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

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw
open scoped TensorProduct Classical

namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι)

abbrev ColT (i : ℕ) : Type := (I.chain l u a).cls i → (I.chain l u a).Y i → ℂ



structure TwDat (Ch : ℕ → Type) where
  bad : ℕ → Set (HeightOneSpectrum (𝓞 B.host.F))
  chOf : ∀ i, (I.stp u a i).Cl → Ch i
  K : ∀ i (hi : i ≤ B.R.m) (β : Ch i), LevelChart (I.rec7 l Z) (B.T u) (bad i) i hi
    (fun c : {c // chOf i c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))

  kb : ∀ i, Ch i → TC.GA B (B.R.N i)
  kA : ∀ i, Ch i → GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i)
  xr : ∀ i, Ch i → (AE (I.rec7 l Z))ˣ
  b0 : ∀ i, Ch i → Idx I.sel (I.tup a) (I.idx a) i
  p0 : ∀ i, Ch i → PtAt B.R I.sel (I.tup a) (I.cst a) u i

  U : ∀ i, Ch i → Subgroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i))
  chi : ∀ i β, U i β →* ℂˣ
  h : ∀ i (β : Ch i), {c // chOf i c = β} → GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i)

  chr : ℕ → ((AE (I.rec7 l Z))ˣ →* Circle)
  e : AE (I.rec7 l Z)

variable {I l Z u a} {Ch : ℕ → Type}

namespace TwDat
variable (A : TwDat I l Z u a Ch)

structure Is : Prop where
  reads : ∀ i (hi : i ≤ B.R.m), I.Reads u a i (A.chOf i) (fun β => (A.K i hi β).lev.Lb) (fun β => (A.K i hi β).lev.U)
    (fun β => (A.K i hi β).lev.chi) (fun c => ((A.K i hi (A.chOf i c)).y ⟨c, rfl⟩).1)
    (fun c s => ((A.K i hi (A.chOf i c)).stabI ⟨c, rfl⟩ s).1) (A.kb i)
  top : ∀ β, I.TopPt l Z u a (A.kb B.R.m β)
  kA : ∀ i (hi : i ≤ B.R.m) β, A.kA i β ∈ GfC _ ∧ finM _ (rankN (I.rec7 l Z) i hi) (A.kA i β) = (A.kb i β).1 ∧
    IsDetRoot _ (A.kA i β) (A.xr i β)
  base : ∀ i, i ≤ B.R.m → ∀ β, TC.PtOf (A.kb i β) (extTo I.SQ (A.p0 i β).1.1) ∧
    (A.p0 i β).1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N i)
  rep : ∀ i, i ≤ B.R.m → ∀ c, c.1 = A.b0 i (A.chOf i c) ∧ cosetIn ((I.stp u a i).rep c) = cosetIn (A.p0 i (A.chOf i c))
  U : ∀ i (hi : i ≤ B.R.m) β g, g ∈ A.U i β ↔ g ∈ GfC _ ∧ ∃ κ : (A.K i hi β).lev.U, κ.1.1 = finM _ (rankN (I.rec7 l Z) i hi) g
  chi : ∀ i (hi : i ≤ B.R.m) β (g : A.U i β) (κ : (A.K i hi β).lev.U), κ.1.1 = finM _ (rankN (I.rec7 l Z) i hi) g.1 →
    A.chi i β g = (A.K i hi β).lev.chi κ
  h : ∀ i (hi : i ≤ B.R.m) β c, A.h i β c ∈ GfC _ ∧ finM _ (rankN (I.rec7 l Z) i hi) (A.h i β c) = ((A.K i hi β).y c).1.1
  chr : ∀ j : Fin B.R.m, ChrEq (A.chr ((j : ℕ) + 1)) (I.C.mu0 j * I.xi a)
  idem : IsIdemSum A.e (Formalism.L2.Col.Sall (Pr := B.primes X) I.sel (I.tup a) u)

  fin : ∀ i (hi : i ≤ B.R.m) β, ∃ n : ℕ, 0 < n ∧ ∀ κ, (A.K i hi β).lev.chi κ ^ n = 1

  bad_le : ∀ i, i ≤ B.R.m → ∀ v ∈ A.bad i, v ∈ Formalism.L2.Forms.badG (I.rec7 l Z) ∨ I.UnderQ a v

def xi (i : ℕ) (hi : i + 1 ≤ B.R.m) (α : Ch i) (γ : Ch (i + 1))
    (z : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) : ℂ :=
  B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i (A.b0 i α) (A.b0 (i + 1) γ) (A.p0 i α) (A.p0 (i + 1) γ)
    (toHom _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) z))

def abelian₂ (_A : TwDat I l Z u a Ch) (i : ℕ) (c : (I.stp u a i).Cl) (c' : (I.stp u a (i + 1)).Cl) :
    FP (I.rec7 l Z).what₂.Tau (B.R.N i) (B.R.N (i + 1)) →ₗ[ℂ] ℂ :=
  ((I.chIn u a).rho i c * (I.chIn u a).rho' i c') •
    jetL I.J.cD (I.th u a i _ _ ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c'))

def rd (θ : InfFam (I.rec7 l Z)) (i : ℕ) (hi : i ≤ B.R.m) (β : Ch i) (ψ : ColT I l u a i) (y : (I.chain l u a).Y i) :
    GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i) → ℂ :=
  rdS θ _ (rankN (I.rec7 l Z) i hi) (A.K i hi β).lev (A.K i hi β).y (fun c z => ψ c.1 ⟨z.1, z.2⟩) ⟨y.1, y.2⟩

end TwDat

def RamT (i : ℕ) (φ : ColT I l u a i) : Prop :=
  φ ∈ (I.fm l u a).Fi i ∧ ∀ v c, ∑ᶠ s : ((I.atT l u a).Fv v)ˣ, (I.fm l u a).dilT i v s c (φ ((I.fm l u a).dil i v s c)) = 0

def VacT (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (θ : InfFam (I.rec7 l Z)) (i : ℕ) (hi : i + 1 ≤ B.R.m) (c₀ : ℂ)
    (μ : (AE (I.rec7 l Z))ˣ →* Circle) (om : Om ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)))
    (vac : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ) : Prop :=
  ∀ g ∈ GfC _, ∀ h ∈ GfC _, ∀ N N', Moves _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) g N →
    Moves _ (rankN (I.rec7 l Z) (i + 1) hi) h N' → ∀ x y, IsDetRoot _ g x → IsDetRoot _ h y →
      ColDat.xiS θ i hi (om (g, h) vac) = fun z => c₀ * (μ x : ℂ)⁻¹ * (μ y : ℂ) * I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) N N' z

structure PinX (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (ψ : AddChar (AF (I.rec7 l Z).host.F) ℂ) (θ : InfFam (I.rec7 l Z))
    (x : ∀ j, DefSp ((I.rec7 l Z).sp.X j)) (vac : ∀ j, WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) → ℂ) (c₀ : ℕ → ℂ) : Prop where
  std : IsStdChar (I.rec7 l Z) ψ (-1)
  inf : IsInfFam θ
  xs : ∀ j, j ≤ B.R.m → (x j).s = (fun _ => 1) ∧ (x j).B = (fun _ => 1) ∧ ∀ z, z ∈ (x j).L ↔ z ∈ intVec (I.rec7 l Z) _
  vc : ∀ j, j < B.R.m → IsVacO ψ θ _ _ (fun _ => 1) (fun _ => 1) (intVec _ _) (intVec _ _) (vac j)
  mv : ∀ j (hj : j + 1 ≤ B.R.m), c₀ j ≠ 0 ∧ ∀ (a : I.ι) μ om, ChrEq μ (I.C.mu0 ⟨j, hj⟩ * I.xi a) → IsWeilDatumO ψ _ _ μ μ om →
    VacT I l Z θ j hj (c₀ j) μ om (vac j)

namespace TwDat.Is
variable {A : TwDat I l Z u a Ch}

theorem chOf_onto (hA : A.Is) (i : ℕ) (hi : i ≤ B.R.m) : Function.Surjective (A.chOf i) := (hA.reads i hi).onto

theorem chart_ext (hA : A.Is) (i : ℕ) (hi : i ≤ B.R.m) (α β : Ch i) (hb : A.b0 i α = A.b0 i β)
    (hc : cosetIn (A.p0 i α) = cosetIn (A.p0 i β)) : α = β := by
  obtain ⟨c, rfl⟩ := hA.chOf_onto i hi α
  obtain ⟨c', rfl⟩ := hA.chOf_onto i hi β
  obtain ⟨h1, h2⟩ := hA.rep i hi c
  obtain ⟨h3, h4⟩ := hA.rep i hi c'
  exact ((hA.reads i hi).key c c').2 ⟨by rw [h1, h3, hb], by rw [h2, h4, hc]⟩

theorem chi_pow (hA : A.Is) (i : ℕ) (hi : i ≤ B.R.m) (β : Ch i) : ∃ n : ℕ, 0 < n ∧ ∀ g, A.chi i β g ^ n = 1 := by
  obtain ⟨n, hn, h⟩ := hA.fin i hi β
  refine ⟨n, hn, fun g => ?_⟩
  obtain ⟨κ, hκ⟩ := ((hA.U i hi β g.1).1 g.2).2
  rw [hA.chi i hi β g κ hκ]
  exact h κ

theorem norm_chi (hA : A.Is) (i : ℕ) (hi : i ≤ B.R.m) (β : Ch i) (g : A.U i β) : ‖((A.chi i β g : ℂˣ) : ℂ)‖ = 1 := by
  obtain ⟨n, hn, h⟩ := hA.chi_pow i hi β
  have e : ((A.chi i β g : ℂˣ) : ℂ) ^ n = 1 := by rw [← Units.val_pow_eq_pow_val, h g, Units.val_one]
  exact Complex.norm_eq_one_of_pow_eq_one e hn.ne'

theorem lev_chi_eq_one (hA : A.Is) (i : ℕ) (hi : i ≤ B.R.m) (β : Ch i) (κ : (A.K i hi β).lev.U)
    (h : ∀ v, v ∈ Formalism.L2.Forms.badG (I.rec7 l Z) ∨ I.UnderQ a v →
      Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) : (A.K i hi β).lev.chi κ = 1 :=
  (A.K i hi β).lev.chi_triv κ fun v hv => h v (hA.bad_le i hi v hv)

end TwDat.Is

section Pin
variable {A : TwDat I l Z u a Ch} {ψ : AddChar (AF (I.rec7 l Z).host.F) ℂ} {θ : InfFam (I.rec7 l Z)}
    {x : ∀ j, DefSp ((I.rec7 l Z).sp.X j)} {vac : ∀ j, WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) → ℂ} {c₀ : ℕ → ℂ}
    {kom : ∀ j, Om ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1))}
    {dd : ∀ j, Ch j → Ch (j + 1) → WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) →₀ ℂ}
    {w : ∀ j, Ch j → Ch (j + 1) → ℂ} {Ram : ∀ j, Set (ColT I l u a j)}
    {rd : ∀ j, Ch j → ColT I l u a j → (I.chain l u a).Y j → GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) → ℂ} {cK : ℕ → ℂ}

end Pin

end GlobalTheory.AdForm
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

variable {D : D7}

def IsBiSmooth {A S A' : HSp D} (C : WO A S → WO S A' → ℂ) : Prop :=
  ∀ (n : ℕ) (L : (Fin n → ℝ) →+ WO A S) (L' : (Fin n → ℝ) →+ WO S A'), Continuous L → Continuous L' →
    (∀ t, (L t).map (finPart D) = 0) → (∀ t, (L' t).map (finPart D) = 0) →
    ∀ u v, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => C (u + L t) (v + L' t)

structure IsBiTheta (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (C : WO A S → WO S A' → ℂ) : Prop where
  cont : Continuous fun p : WO A S × WO S A' => C p.1 p.2
  smooth : IsBiSmooth C
  quasiL : ∀ γ u v, C (ratW S A γ + u) v = ψ (-(symplOH A S (ratW S A γ) u)) * C u v
  quasiR : ∀ γ u v, C u (ratW A' S γ + v) = ψ (-(symplOH S A' (ratW A' S γ) v)) * C u v
  levL : ∃ U : AddSubgroup (WO A S), IsOpen (U : Set (WO A S)) ∧
    ∀ a ∈ U, a.map (infPart D) = 0 → ∀ v, heisO ψ A S a (fun u => C u v) = fun u => C u v
  levR : ∃ U : AddSubgroup (WO S A'), IsOpen (U : Set (WO S A')) ∧
    ∀ a ∈ U, a.map (infPart D) = 0 → ∀ u, heisO ψ S A' a (C u) = C u

def BiAct (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (χA χS χS' χA' : (AE D)ˣ →* Circle) (oma : Om A S) (omb : Om S A'),
    IsWeilDatumO ψ A S χA χS oma → IsWeilDatumO ψ S A' χS' χA' omb → ∀ C, IsBiTheta ψ A S A' C →
      (∀ p, IsBiTheta ψ A S A' fun u v => oma p (fun u' => C u' v) u) ∧
      (∀ q, IsBiTheta ψ A S A' fun u v => omb q (C u) v) ∧
      (∀ p q u v, omb q (fun v' => oma p (fun u' => C u' v') u) v = oma p (fun u' => omb q (C u') v) u) ∧
      Continuous fun x : (GA D A × GA D S) × (GA D S × GA D A') × WO A S × WO S A' =>
        omb x.2.1 (fun v => oma x.1 (fun u => C u v) x.2.2.1) x.2.2.2

def FockRed (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (A S A' : HSp D) (x : DefSp A) (y : DefSp S) (z : DefSp A'),
    x.Is → y.Is → z.Is → ∀ (k : KerDat A S) (k' : KerDat S A'), k.Is ψ θ x y → k'.Is ψ θ y z →
    ∀ (χ : GA D A → ℂ) (C : WO A S → WO S A' → ℂ), IsBiVac ψ A S A' x.L y.L z.L C → IsBiSmooth C →
      ∃ (n : ℕ) (P : Fin n → PolF D S.rank A.rank) (P' : Fin n → PolF D A'.rank S.rank),
        ∀ φ, IsContAut A φ → HasCen A χ φ →
          biLift k.om k'.om x.vol y.vol φ (biComb ψ A S A' k.c k'.c C) =
            ∑ i, k'.lift ψ θ y z (P' i) (k.lift ψ θ x y (P i) φ)

namespace Dat

variable {u : D.what₂.Word} (d : Dat D u)

end Dat

section Examples

variable {ψ : AddChar (AF D.host.F) ℂ} {A S A' : HSp D}

end Examples

end GlobalTheory.SeeSaw

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

open GlobalTheory.ChainOnto (Com PiLocalization₂)

def RapidVal (D : D7) : Prop :=
  ∀ (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ),
    ∀ G ∈ MultT θ M J χ, ∀ v, RapidDec V (G v)

def ValMove (D : D7) : Prop :=
  ∀ (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ),
    (∀ G ∈ MultT θ M J χ, ∀ v, ∀ k ∈ J, rTrans k (G v) = χ k • G v) ∧
    ∀ a ∈ GinfC V, ∀ v, ∃ w, ∀ G ∈ MultT θ M J χ, rTrans a (G v) = G w

def PerSum (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ρ : ℕ) (B : BesLev D ρ) (f : GA D B.V → ℂ), IsContAut B.V f →
    ∀ (I : Type) (s : Finset I) (a : I → ℂ) (φ : I → GA D B.A → ℂ), (∀ i ∈ s, IsContAut B.A (φ i)) →
      B.per ψ (∑ i ∈ s, a i • φ i) f = ∑ i ∈ s, a i * B.per ψ (φ i) f

def LiftSum (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : HSp D) (x : DefSp S) (y : DefSp T), x.Is → y.Is →
    ∀ k : KerDat S T, k.Is ψ θ x y → ∀ P, IsThetaFunO ψ S T (k.pt ψ θ x y P) ∧
      (∀ φ, IsContAut S φ → IsContAut T (k.lift ψ θ x y P φ)) ∧
      ∀ (I : Type) (s : Finset I) (a : I → ℂ) (φ : I → GA D S → ℂ), (∀ i ∈ s, IsContAut S (φ i)) →
        k.lift ψ θ x y P (∑ i ∈ s, a i • φ i) = ∑ i ∈ s, a i • k.lift ψ θ x y P (φ i)

namespace Dat

variable {D : D7} {u : D.what₂.Word} (d : Dat D u)

end Dat

def CenFock (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : HSp D) (x : DefSp S) (y : DefSp T), x.Is → y.Is →
    ∀ k : KerDat S T, k.Is ψ θ x y → ∀ χ : GA D S → ℂ, ∃ W : Submodule ℂ (PolF D T.rank S.rank), FiniteDimensional ℂ W ∧
      ∀ f, IsThetaFunO ψ S T f → IsLatVac (heisO ψ S T) (latO S T x.L y.L fun _ => True) f →
        (∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → k.om (z, 1) f = χ z • f) →
        ∃ P ∈ W, f = pureTensorO ψ θ S T x.s y.s x.B y.B k.vac P

end GlobalTheory.SeeSaw

end
end

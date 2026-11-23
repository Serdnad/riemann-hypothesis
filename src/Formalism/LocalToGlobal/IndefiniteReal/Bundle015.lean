module

public import Formalism.LocalToGlobal.GlobalTheory.Bundle001
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle014
public import Formalism.LocalToGlobal.IndefiniteReal.PrimitiveStatementsWithPassage
public import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.UnitBracket
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle012

@[expose] public section

section

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.CxPass

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.L2.GlobalTheoryTheory.DivPassage

structure In3 (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G] (Pl0 I0 Ty T : Type)
    (m : ℕ) where
  A3 : FamIn3 K G Pl0 I0 Ty T m
  P0 : Subgroup G
  ψ0 : P0 →* Kˣ
  P1 : Subgroup G
  ψ1 : P1 →* Kˣ
  Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)
  Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)
  Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3
  X : CxData A3.fam3.amb3
  gE : Representation ℂ G X.EE

namespace In3

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
  (I : In3 K G Pl0 I0 Ty T m)

abbrev A : FamIn K G Pl0 T m := I.A3.A

abbrev cr : Crd I.A3.fam3.amb3 (faceOf3 I.A3 I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc) := crdOf3 I.A3 I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc

abbrev cg : Crd I.A3.fam3.amb3 (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc) := crdOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc

def lvP : Bool → Subgroup G := fun b => cond b I.P1 I.P0

def lvψ : ∀ b, I.lvP b →* Kˣ
  | false => I.ψ0
  | true => I.ψ1

abbrev Sb (b : Bool) := I.X.data I.cr b

abbrev Sg := (prin I.X).data I.cg false

abbrev iCg := I.X.iC I.cg false I.A3.fam3.base3.μ0

def Jm (b : Bool) : Matrix (Fin I.Sg.D) (Fin (I.Sb b).D) K :=
  kMat I.A3.fam3.base3.v0.embedding (relMat I.iCg (I.X.iC I.cr b I.A3.fam3.base3.μ0))

def ρf (g : G) : Matrix (Fin I.Sg.D) (Fin I.Sg.D) K :=
  kMat I.A3.fam3.base3.v0.embedding (relMat I.iCg ((I.gE g).comp I.iCg))

def Jt (b : Bool) (t : I.A3.fam3.base3.Tup) :
    Matrix (Fin ((lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).dQ t))
      (Fin ((lv (faceOf3 I.A3 I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) b).dQ t)) K :=
  kMat I.A3.fam3.base3.v0.embedding (relMat (I.X.iC I.cg false t) (I.X.iC I.cr b t))


open Classical in
def epM (P : Subgroup G) (ψ : P →* Kˣ) : Matrix (Fin I.Sg.D) (Fin I.Sg.D) K :=
  haveI : Fintype P := Fintype.ofFinite P
  ((Nat.card P : K)⁻¹) • ∑ h : P, (((ψ h)⁻¹ : Kˣ) : K) • I.ρf (h : G)

def eMat {W : Type} [AddCommGroup W] [Module K W] (τ : Representation K G W) : Matrix (Fin I.Sg.D) (Fin I.Sg.D) K :=
  (Formalism.IndefR.TransferLatticeStatement.charOf τ 1 / (Fintype.card G : K)) • ∑ x : G, Formalism.IndefR.TransferLatticeStatement.charOf τ x⁻¹ • I.ρf x

abbrev LA {S : Type} [Fintype S] {Ws : S → Type} [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)]
    (τ : ∀ s, Representation K G (Ws s)) (nbar : ℝ) : LevelAmb K (I.Sb false).D (I.Sb true).D where
  Dg := I.Sg.D
  Xg := I.Sg.XE
  Rg := I.Sg.RR
  ep0 := I.epM I.P0 I.ψ0
  ep1 := I.epM I.P1 I.ψ1
  S := S
  fS := inferInstance
  es s := I.eMat (τ s)
  nS s := Formalism.IndefR.IndefiniteEpsilonOperator.nOf (τ s) ⟨I.P1, I.ψ1⟩
  nbar := nbar
  G := Fintype.card G
  h0 := Nat.card I.P0
  h1 := Nat.card I.P1
  ι0 := I.Jm false
  ι1 := I.Jm true

structure Hyp (s : ℕ) : Prop where
  ok : I.A3.fam3.Ok3 s
  sep : I.A3.fam3.TypesSep3
  stable : I.X.zs.Stable
  inBlock : I.X.zs.InBlock
  h4pos : I.X.H4pos
  pos0 : (I.A3.side3 I.P0 I.ψ0 I.X.zs).Pos
  pos1 : (I.A3.side3 I.P1 I.ψ1 I.X.zs).Pos
  h2 : ∀ b, I.X.H2 I.cr b
  ratMu : ∀ b, I.X.RATmu I.cr b
  h2g : PrincipalLevelBijectivity I.A3 I.X (P1 := I.P1) (ψ1 := I.ψ1) (Dc := I.Dc) (Sp := I.Sp) (Zsc := I.Zsc)
  ratMug : I.X.RATmu I.cg false
  gunit : ∀ (g : G) (x y : I.X.EE), ⟪I.gE g x, I.gE g y⟫_ℂ = ⟪x, y⟫_ℂ
  gequiv : GEquiv3 I.A3 I.X I.gE
  np0 : I.X.nP false = (Nat.card I.P0 : ℝ)
  np1 : I.X.nP true = (Nat.card I.P1 : ℝ)

def PRho : Prop :=
  ∀ s, I.Hyp s → I.ρf 1 = 1 ∧ (∀ g h, I.ρf (g * h) = I.ρf g * I.ρf h) ∧
    ∀ g (x : Fin I.Sg.D → K), I.iCg (cpt I.A3.fam3.base3.v0.embedding (I.ρf g *ᵥ x)) =
      I.gE g (I.iCg (cpt I.A3.fam3.base3.v0.embedding x))

def PJ : Prop :=
  ∀ s, I.Hyp s → ∀ b, (∀ x : Fin (I.Sb b).D → K, I.iCg (cpt I.A3.fam3.base3.v0.embedding (I.Jm b *ᵥ x)) =
      I.X.iC I.cr b I.A3.fam3.base3.μ0 (cpt I.A3.fam3.base3.v0.embedding x)) ∧ Function.Injective (I.Jm b).mulVec

def PJt : Prop :=
  ∀ s, I.Hyp s → ∀ b t,
    (∀ x, I.X.iC I.cg false t (cpt I.A3.fam3.base3.v0.embedding (I.Jt b t *ᵥ x)) =
      I.X.iC I.cr b t (cpt I.A3.fam3.base3.v0.embedding x)) ∧
    (∀ x, I.cg.toR I.X.zs false t (I.Jt b t *ᵥ x) = I.cr.toR I.X.zs b t x) ∧
    ∀ x, I.Jm b *ᵥ (I.X.rowMat I.cr b t *ᵥ x) = I.X.rowMat I.cg false t *ᵥ (I.Jt b t *ᵥ x)

def PRange : Prop :=
  ∀ s, I.Hyp s → ∀ b, LinearMap.range (I.Jm b).mulVecLin = LinearMap.range (I.epM (I.lvP b) (I.lvψ b)).mulVecLin

def PMet : Prop :=
  ∀ s, I.Hyp s → ∀ b v (x y : Fin (I.Sb b).D → K),
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin (I.Sb b).D)) (I.Sb b).XE v x y =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin I.Sg.D)) (Formalism.BranchingDeterminantCap.scaleFrame (Real.sqrt (Nat.card (I.lvP b))) I.Sg.XE) v
        (I.Jm b *ᵥ x) (I.Jm b *ᵥ y)

def PFrames : Prop := ∀ s, I.Hyp s → ∀ v, IsUnit (I.Sg.XE v).det

def PUni : Prop :=
  ∀ s, I.Hyp s → ∀ v (g : G) (x y : Fin I.Sg.D → K),
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin I.Sg.D)) I.Sg.XE v (I.ρf g *ᵥ x) (I.ρf g *ᵥ y) =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin I.Sg.D)) I.Sg.XE v x y

def PLat : Prop := ∀ s, I.Hyp s → Submodule.IsLattice K I.Sg.RR

def PGLat : Prop := ∀ s, I.Hyp s → ∀ (g : G), ∀ x ∈ I.Sg.RR, I.ρf g *ᵥ x ∈ I.Sg.RR

def PSand : Prop :=
  ∀ s, I.Hyp s → ∀ b,
    (∀ x ∈ (I.Sb b).RR, I.Jm b *ᵥ x ∈ I.Sg.RR) ∧
    ∀ y ∈ I.Sg.RR, y ∈ LinearMap.range (I.epM (I.lvP b) (I.lvψ b)).mulVecLin →
      ∃ x ∈ (I.Sb b).RR, I.Jm b *ᵥ x = ((Nat.card (I.lvP b) : ℕ) : 𝓞 K) • y

def PGood {S : Type} [Fintype S] {Ws : S → Type} [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)]
    (τ : ∀ s, Representation K G (Ws s)) : Prop :=
  ∀ s, I.Hyp s → Formalism.IndefR.TransferLatticeStatement.IsGood τ → CharsX τ I.A.fam.X → ∑ t, I.eMat (τ t) = 1

end In3

end Formalism.IndefR.CxPass
end
end

section

noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Heis Formalism.IndefR.InjectiveDecompositionAction
  IsDedekindDomain NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.IndefR.flipTwoThree

def DeterminantInUnitaryOne : Prop :=
  ∀ (D : D7) (V : HSp D) (g : GA D V), (mt V g).det * cA D (mt V g).det = 1

def SplitDetP : Prop :=
  ∀ (D : D7) (V : HSp D), 0 < V.rank → ∀ e, IsSplitIdem D e → ∀ x : (AE D)ˣ, (x : AE D) * cA D (x : AE D) = 1 →
    SuppAtU D e x → ∃ g : GA D V, SuppAt e V g ∧ (∃ x', IsDetAt e V g x') ∧ (mt V g).det = x

variable {D : D7}

theorem mt_one' (V : HSp D) : L2.Theta.mt V 1 = 1 := by
  simp [L2.Theta.mt, map_one]

section Scalar

variable (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χ χ' : (AE D)ˣ →* Circle)
    (ω ω' : GA D V × GA D W →* Module.End ℂ (Hth ψ V W))

end Scalar

section Side

end Side

end Formalism.IndefR.flipTwoThree

end
end

section

noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Heis
  IsDedekindDomain NumberField Formalism.IndefR.PHeisFC
open scoped TensorProduct ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.IndefR.PHeisTh

section Tens

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]

theorem repr_snd (z : AF F ⊗[F] E) (k : Fin (Module.finrank F E)) :
    (Algebra.TensorProduct.basis (Af F) (Module.finBasis F E)).repr
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z) k = (cE F E z k).2 := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, Finsupp.zero_apply]; rfl
  | tmul a e =>
    show _ = ((bA F E).equivFun (a ⊗ₜ[F] e) k).2
    rw [Algebra.TensorProduct.map_tmul, Module.Basis.equivFun_apply, Algebra.TensorProduct.basis_repr_tmul,
      Algebra.TensorProduct.basis_repr_tmul]
    simp [sndA]
    rfl
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy, Pi.add_apply]; rfl

theorem repr_fst (z : AF F ⊗[F] E) (k : Fin (Module.finrank F E)) :
    (Algebra.TensorProduct.basis (Ainf F) (Module.finBasis F E)).repr
      (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z) k = (cE F E z k).1 := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, Finsupp.zero_apply]; rfl
  | tmul a e =>
    show _ = ((bA F E).equivFun (a ⊗ₜ[F] e) k).1
    rw [Algebra.TensorProduct.map_tmul, Module.Basis.equivFun_apply, Algebra.TensorProduct.basis_repr_tmul,
      Algebra.TensorProduct.basis_repr_tmul]
    simp [fstA]
    rfl
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy, Pi.add_apply]; rfl

theorem trace_tmul (e : E) :
    Algebra.trace (AF F) (AF F ⊗[F] E) ((1 : AF F) ⊗ₜ[F] e) = algebraMap F (AF F) (Algebra.trace F E e) := by
  have h : Algebra.lmul (AF F) (AF F ⊗[F] E) ((1 : AF F) ⊗ₜ[F] e) =
      (Algebra.lmul F E e).baseChange (AF F) := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a m => simp [LinearMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  rw [Algebra.trace_apply, h, LinearMap.trace_baseChange]
  rfl

end Tens

section Sympl

variable {D : D7}

theorem cA_algebraMap (c : AF D.host.F) :
    cA D (algebraMap (AF D.host.F) (AE D) c) = algebraMap (AF D.host.F) (AE D) c := by
  show (Algebra.TensorProduct.map (AlgHom.id D.host.F (AF D.host.F)) D.sp.cm.sig) (c ⊗ₜ[D.host.F] (1 : D.host.E)) =
    c ⊗ₜ[D.host.F] (1 : D.host.E)
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl

theorem cA_smul (c : AF D.host.F) (z : AE D) : cA D (c • z) = c • cA D z := by
  rw [Algebra.smul_def, map_mul, cA_algebraMap, ← Algebra.smul_def]

end Sympl

end Formalism.IndefR.PHeisTh

end
end

section

noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Heis
  IsDedekindDomain NumberField Formalism.IndefR.PHeisFC
open scoped TensorProduct ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.IndefR.PHeisTh

abbrev Ix {D : D7} (V W : HSp D) : Type := Fin V.rank × Fin W.rank × Fin (nE D)

def Co {D : D7} (V W : HSp D) (x : WA V W) (a : Ix V W) : AF D.host.F := Phi V W x a.1 a.2.1 a.2.2

def CoordFinP : Prop :=
  ∀ (D : D7) (V W : HSp D) (x : WA V W), x.map (finPart D) = 0 → ∀ a, (Co V W x a).2 = 0



def PsiOpenP : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    ∃ G : AddSubgroup (Af F), IsOpen (G : Set (Af F)) ∧ (∀ y ∈ G, ∀ z ∈ Ohat F, z * y ∈ G) ∧
      ∀ y ∈ G, ψ (pairA F 0 y) = 1

def PsiSmoothP : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (k : ℕ) (s : (Fin k → ℝ) →+ Ainf D.host.F), Continuous s →
      ContDiff ℝ ∞ fun t => ψ (pairA D.host.F (s t) 0)

end Formalism.IndefR.PHeisTh

end
end

section

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.CxPass

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx

def CutPassage3S : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (G : Type) [Group G] [Fintype G]
    (Pl0 I0 Ty T : Type) (m : ℕ) (A3 : FamIn3 K G Pl0 I0 Ty T m) (s : ℕ) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ)
    (P1 : Subgroup G) (ψ1 : P1 →* Kˣ) (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs))
    (Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)) (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3)
    (X : CxData A3.fam3.amb3) (C CH : ℝ)
    (gE : Representation ℂ G X.EE) (S : Type) [Fintype S] (Ws : S → Type) [∀ s, AddCommGroup (Ws s)]
    [∀ s, Module K (Ws s)] [∀ s, FiniteDimensional K (Ws s)] (τ : ∀ s, Representation K G (Ws s)) (nbar : ℝ),
    A3.fam3.Ok3 s → A3.fam3.TypesSep3 →
    X.zs.Stable → X.zs.InBlock → X.H4pos →
    (A3.side3 P0 ψ0 X.zs).Pos → (A3.side3 P1 ψ1 X.zs).Pos →
    (∀ b, X.H2 (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) b) → (∀ b, X.RATmu (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) b) →
    PrincipalLevelBijectivity A3 X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) →
    X.RATmu (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false →
    (∀ (g : G) (x y : X.EE), ⟪gE g x, gE g y⟫_ℂ = ⟪x, y⟫_ℂ) → GEquiv3 A3 X gE →
    X.nP false = (Nat.card P0 : ℝ) → X.nP true = (Nat.card P1 : ℝ) →
    Formalism.IndefR.TransferLatticeStatement.IsGood τ → CharsX τ A3.A.fam.X → Formalism.IndefR.IndefiniteEpsilonOperator.M1 τ ⟨P0, ψ0⟩ → 0 < nbar →
    NearConstantMultiplicities τ ⟨P1, ψ1⟩ nbar ((faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH).de →
    ((faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH).la = Formalism.IndefR.IndefiniteEpsilonOperator.la G →
      Passage ((faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)
        (X.data (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false) (X.data (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) true)

end Formalism.IndefR.CxPass
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
  Formalism.IndefR.Fock.Sk MeasureTheory IsDedekindDomain NumberField Matrix

namespace Formalism.IndefR.WeilFull

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def SuppV (ε : AF D.host.F) (V : HSp D) (g : GA D V) : Prop :=
  ∀ i j, algebraMap (AF D.host.F) (AE D) ε * (mt V g - 1) i j = (mt V g - 1) i j

def UnrAtV (ε : AF D.host.F) (χ : (AE D)ˣ →* Circle) : Prop :=
  ∀ x : (AE D)ˣ, (1 - algebraMap (AF D.host.F) (AE D) ε) * (x : AE D) = 1 - algebraMap (AF D.host.F) (AE D) ε →
    finPart D (x : AE D) ∈ intAE D → finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D → χ x = 1

def SphInertAtO (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) : Prop :=
  S.rank ≠ T.rank → (Even S.rank ∨ Even T.rank) →
    ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
      IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)),
      Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT →
    ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε →
      (2 : 𝓞 D.host.F) ∉ v.asIdeal →
      (∀ e, IsSplitIdem D e → e * algebraMap (AF D.host.F) (AE D) ε = 0) →
      UnrAtV ε χS → UnrAtV ε χT →
    ∀ (g : GA D S) (h : GA D T), SuppV ε S g → SuppV ε T h →
      Lev.finE S g ∈ Formalism.L2.DIV.St βS → Lev.finE T h ∈ Formalism.L2.DIV.St βT →
    ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f →
      IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun w => w = v) f → om (g, h) f = f

def RealAtO (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) : Prop :=
  LineAtExists D →
  ∀ (θ : InfFam D) sS sT BS BT (pS pT : D.what₂.Tau → ℕ), PairSetup ψ θ S T sS sT BS BT pS pT →
    ∀ (τ : D.what₂.Tau) (αS αT : ℚ), HasInfExp D χS τ αS → HasInfExp D χT τ αT →
    ∀ (XS : Matrix (Fin S.rank) (Fin S.rank) ℂ) (XT : Matrix (Fin T.rank) (Fin T.rank) ℂ),
      XS ∈ lieAt S τ → XT ∈ lieAt T τ →
        ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f →
          ∀ (P : MvPolynomial (FVar D T.rank S.rank) ℂ) (x : WO S T),
            HasDerivAt (fun t : ℝ => om (oneP θ S τ XS t, oneP θ T τ XT t) (pureTensorO ψ θ S T sS sT BS BT f P) x)
              (pureTensorO ψ θ S T sS sT BS BT f
                (quadOp τ (sS τ) (BS τ) XS (sT τ) (BT τ) XT (pS τ) (pT τ) P +
                  (halfTrJ (sS τ) (BS τ) XS (sT τ) (BT τ) XT (pS τ) (pT τ) + (αS : ℂ) * XT.trace -
                    (αT : ℂ) * XS.trace) • P) x) 0

structure IsWeilFull (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) : Prop where
  datum : IsWeilDatumO ψ S T χS χT om
  inert : SphInertAtO ψ S T χS χT om
  real : RealAtO ψ S T χS χT om

def WeilExistsFull (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle),
    IsStdChar D ψ (-1) → IsHeckeChar D χS → IsHeckeChar D χT → ResEta D χS S.rank → ResEta D χT T.rank →
    ∃ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeilFull ψ S T χS χT om

def InertAllO (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → SphInertAtO ψ S T χS χT om

def RealAllO (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → RealAtO ψ S T χS χT om

theorem weilExistsFull_of (h : AutomorphicFormsHyp.WeilExistsO D) (hi : InertAllO D) (hr : RealAllO D) : WeilExistsFull D := by
  intro ψ S T χS χT hψ hS hT hrS hrT
  obtain ⟨om, hom⟩ := h ψ S T χS χT hψ hS hT hrS hrT
  exact ⟨om, hom, hi ψ S T χS χT om hom, hr ψ S T χS χT om hom⟩

end Formalism.IndefR.WeilFull

end
end

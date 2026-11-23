module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle337
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfAutomorphicEmbedding
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle048
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockOrderedSumEquivTrueIndex
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OneMemEntries
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle077
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FunObj

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}

def RealMatch.Tied (ρ : RealMatch W) : Prop :=
  ∀ (i j : Fin D.R.m) (A : Fr (G.V (.grid (i + 1) (j + 1)))) (A₁ : Fr (G.V (.grid i j))) (AV : Fr (G.V (.grid i (j + 1))))
    (AV₁ : Fr (G.V (.grid (i + 1) j))), IsGridFr W _ A → IsGridFr W _ A₁ → IsGridFr W _ AV → IsGridFr W _ AV₁ →
    ∀ (t : T) ωA ωB Pi rf rl p p', IsMatch W.ψ W.θ A A₁ (frSum AV AV₁) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j)
      ωA ωB Pi rf rl p p' →
    ∀ (B : Frames G) n Φ τ τ', (∀ w ∈ locPl G t, depthAt G w ≤ n w ∧ IsNatDatum (unifAt w) (n w) (Φ w)) →
      HasFlip B t ρ i j n Φ τ τ' → ∃ c : ℂ, ∀ a b, ρ.Matched (t := t) (i := i) (j := j) a b →
        p (datumA W (tensT W a τ)) = c • p' (datumB W (tensT W b τ'))

end GlobalTheory.FunObj

end
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj)
open GlobalTheory.PRep (IsAdmissible)

noncomputable section

namespace GlobalTheory.TrMult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def finFn (V : HSp D) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ) : GfC V → ℂ :=
  fun g => ∏ᶠ v, ff v (proj D.sp.cm.sig V.gram v (g : GA D V))

def IsFinMeas (V : HSp D) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (ν : Measure (GfC V)) : Prop :=
  ν.IsHaarMeasure ∧ ∀ ff, IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff → ∫ g, finFn V ff g ∂ν = ∏ᶠ v, ∫ x, ff v x ∂μf v

def HasTypeVec {V : HSp D} (T : TypeDataG V) {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W) : Prop :=
  ∃ x : W, x ≠ 0 ∧ (∀ v ∉ T.S, ∀ k ∈ Kv V v, σ (locFin V v k) x = x) ∧
    ∀ v : T.S, x ∈ Submodule.span ℂ {y | ∃ φ : T.W v →ₗ[ℂ] W,
      (∀ (k : Kv V v) z, φ (T.τ v ((T.frame v).red k) z) = σ (locFin V v k) (φ z)) ∧ y ∈ LinearMap.range φ}

def SphRest {V : HSp D} (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ) : Prop :=
  ∀ v ∉ T.S, v ≠ U.u → ∀ k ∈ Kv V v, ∀ k' ∈ Kv V v, ∀ g, ff v (k * g * k') = ff v g

def IsIrrFam {V : HSp D} {n : ℕ} {W : Fin n → Type} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (σ : ∀ i, Representation ℂ (GfC V) (W i)) : Prop :=
  (∀ i, (σ i).IsIrreducible) ∧ (∀ i, IsAdmissible (σ i)) ∧ ∀ i j, i ≠ j → IsEmpty ((σ i).Equiv (σ j))

def SpecFin : Prop :=
  ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant],
    (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ →
      mCuspDS μ σ M < Cardinal.aleph0) ∧
    ∀ K : Subgroup (GfC V), IsOpen (K : Set (GfC V)) →
      ∃ (n : ℕ) (Ws : Fin n → Type) (_ : ∀ i, AddCommGroup (Ws i)) (_ : ∀ i, Module ℂ (Ws i))
        (σs : ∀ i, Representation ℂ (GfC V) (Ws i)), IsIrrFam σs ∧
        ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ →
          mCuspDS μ σ M ≠ 0 → (∃ x : W, x ≠ 0 ∧ ∀ k ∈ K, σ k x = x) → ∃ i, Nonempty (σ.Equiv (σs i))

def SpecTrace : Prop :=
  ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S)
    (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w))
    (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ),
    IsTestData V lam M T U μa μf μ fa ff → ∀ ν, IsFinMeas V μf ν →
    ∀ (n : ℕ) (Ws : Fin n → Type) [∀ i, AddCommGroup (Ws i)] [∀ i, Module ℂ (Ws i)] (σs : ∀ i, Representation ℂ (GfC V) (Ws i)),
      IsIrrFam σs →
      (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ →
        mCuspDS μ σ M ≠ 0 → ¬ GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V ff) 0 → ∃ i, Nonempty (σ.Equiv (σs i))) →
      ∀ c : Fin n → ℂ, (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace ν (σs i) (finFn V ff) (c i)) →
        HasTrace (RopG V μ (tensor D.sp.cm.sig V.gram fa ff)) (∑ i, ((mCuspDS μ (σs i) M).toNat : ℂ) * c i)

def Separation : Prop :=
  ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V), U.u ∉ T.S →
    ∀ (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → (∀ᶠ v in cofinite, μf v (Kv V v) = 1) →
    ∀ ν, IsFinMeas V μf ν →
    ∀ (n : ℕ) (Ws : Fin n → Type) [∀ i, AddCommGroup (Ws i)] [∀ i, Module ℂ (Ws i)] (σs : ∀ i, Representation ℂ (GfC V) (Ws i)),
      IsIrrFam σs → ∀ a : Fin n → ℂ,
      (∀ ff, IsTestFin T U μf ff → SphRest T U ff →
        ∀ c : Fin n → ℂ, (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace ν (σs i) (finFn V ff) (c i)) → ∑ i, a i * c i = 0) →
      ∀ i, HasTypeVec T (σs i) → a i = 0

end GlobalTheory.TrMult

end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.ChernCalc
open GlobalTheory.FlagFibre (Low)
open scoped Matrix

namespace GlobalTheory.FlagCell2

variable {ι : Type} {m : ι → ℕ} {n d : ℕ}

abbrev Cell (m : ι → ℕ) : Type := Σ τ, Low (m τ)

def upU {K : Type} [Zero K] [One K] {s : ℕ} (y : Low s → K) : Matrix (Fin s) (Fin s) K :=
  Matrix.of fun a b => if h : a < b then y ⟨(b, a), h⟩ else if a = b then 1 else 0

def upM {K : Type} [Zero K] [One K] (y : Cell m → K) : Mat m K := fun τ => upU fun s => y ⟨τ, s⟩

def Cell.root (j : Cell m) : Root m := ⟨j.1, j.2.1.2⟩

def bsL {J : Type} (ε : Fin n ≃ Fin d ⊕ J) : V n →L[ℂ] V d :=
  (EuclideanSpace.equiv (Fin d) ℂ).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun a => EuclideanSpace.proj (ε.symm (.inl a))

def fb {J : Type} (ε : Fin n ≃ Fin d ⊕ J) (w : V n) (j : J) : ℂ := w (ε.symm (.inr j))

def pt {J : Type} (ε : Fin n ≃ Fin d ⊕ J) (v : V d) (y : J → ℂ) : V n := WithLp.toLp 2 fun a => Sum.elim (fun b => v b) y (ε a)

def cellPot (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (x : Root m) (w : V n) : ℝ :=
  -Real.log (grD (upM (fb ε w) x.1 * G (bsL ε w) x.1 * (upM (fb ε w) x.1)ᴴ) x.2)

variable [Fintype ι]

def cellFib (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (w : V n) : Ev n :=
  MvPolynomial.aeval (fun x => ofValues (ddc (cellPot ε G x) w)) ((fibrePoint m).map (algebraMap ℝ ℂ))

def cellForm (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (a : V d → Alt d) (w : V n) : Alt n :=
  pull (bsL ε) (a (bsL ε w)) * (cellFib ε G w : Alt n)

def fibDens (G : Mat m ℂ) (y : Cell m → ℂ) : ℝ :=
  ∏ τ, GlobalTheory.TrueCx.flagConst (m τ) * (G τ).det.re ^ ((m τ : ℤ) - 1) * GlobalTheory.FlagFibre.dens (G τ)ᵀ fun s => y ⟨τ, s⟩


omit [Fintype ι] in
theorem upU_eq {s : ℕ} (y : Low s → ℂ) : upU y = (GlobalTheory.FlagFibre.uni y)ᵀ := by
  ext a b
  simp only [upU, GlobalTheory.FlagFibre.uni, Matrix.of_apply, Matrix.transpose_apply, eq_comm]


omit [Fintype ι] in
theorem bsL_apply {J : Type} (ε : Fin n ≃ Fin d ⊕ J) (w : V n) (a : Fin d) : bsL ε w a = w (ε.symm (.inl a)) := rfl


omit [Fintype ι] in
theorem bsL_pt {J : Type} (ε : Fin n ≃ Fin d ⊕ J) (v : V d) (y : J → ℂ) : bsL ε (pt ε v y) = v := by
  ext a
  simp [bsL_apply, pt]


omit [Fintype ι] in
theorem fb_pt {J : Type} (ε : Fin n ≃ Fin d ⊕ J) (v : V d) (y : J → ℂ) : fb ε (pt ε v y) = y := by
  funext j
  simp [fb, pt]

section Variety

variable {F : Type} [Field F] {X Y : Var F} {σ : F →+* ℂ}

def InCell (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (A : Mat m X.Fn)
    (u : Cell m → Y.Fn) (y : Y.X) : Prop :=
  A ∈ E.S (f y) ∧ upM u * A.map φ ∈ E'.S y

def cellMap (ε : Fin n ≃ Fin X.dim ⊕ Cell m) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str) (c : AlgChart X.str σ X.dim)
    (u : Cell m → Y.Fn) (y : CxPts Y.str σ) : V n :=
  pt ε (c.e (ptMap σ f hf y)) fun j => ratVal (u j) y

def cellSet (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X)
    (hf : f ≫ X.str = Y.str) (c : AlgChart X.str σ X.dim) (A : Mat m X.Fn) (u : Cell m → Y.Fn) : Set (CxPts Y.str σ) :=
  {y | InCell E E' φ f A u (under y) ∧ ptMap σ f hf y ∈ c.e.source}

end Variety

end GlobalTheory.FlagCell2
end
end

section

noncomputable section

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open Formalism.UG (cT bc)
open scoped TensorProduct NNReal

namespace GlobalTheory.SphEis

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {j m : ℕ}

structure Fr (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E) : Prop where
  cm : IsCMExt F E σ
  herm : IsHermND σ J
  herm₀ : IsHermND σ J₀
  cc : cT (σ : E →+* E) C * J * C = 0
  dd : cT (σ : E →+* E) D * J * D = 0
  cd : cT (σ : E →+* E) C * J * D = 1
  dc : cT (σ : E →+* E) D * J * C = 1
  cz : cT (σ : E →+* E) C * J * Z = 0
  dz : cT (σ : E →+* E) D * J * Z = 0
  zc : cT (σ : E →+* E) Z * J * C = 0
  zd : cT (σ : E →+* E) Z * J * D = 0
  zz : cT (σ : E →+* E) Z * J * Z = J₀
  sum : C * (cT (σ : E →+* E) D * J) + Z * (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) + D * (cT (σ : E →+* E) C * J) = 1
  dim : m + 2 * j = n

def fixG {k : ℕ} (C : Matrix (Fin n) (Fin k) E) : Subgroup (GAd σ J) where
  carrier := {g | (matHom _ σ J g).1 * adMat F C = adMat F C}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    change _ * _ = _ at ha hb ⊢
    rw [map_mul, Units.val_mul, Matrix.mul_assoc, hb, ha]
  inv_mem' := fun {a} ha => by
    change _ * _ = _ at ha ⊢
    conv_lhs => rw [← ha]
    rw [← Matrix.mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul]

structure IsLv (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E)
    (lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J) : Prop where
  cont : Continuous lv
  onC : ∀ α, (matHom _ σ J (lv α)).1 * adMat F C = adMat F C * α.1
  onD : ∀ α, (matHom _ σ J (lv α)).1 * adMat F D = adMat F D * cT (sigR (AF F) σ) (α⁻¹).1
  onZ : ∀ α, (matHom _ σ J (lv α)).1 * adMat F Z = adMat F Z
  rat : ∀ δ : GL (Fin j) E, lv (bc (inclR (F := F) (AF F)) δ) ∈ ratPts σ J

def plus (J₀ : Matrix (Fin m) (Fin m) E) (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) : Matrix (Fin m) (Fin j) (AF F ⊗[F] E) :=
  adMat F J₀⁻¹ * cT (sigR (AF F) σ) b

structure Crd (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E) (u : GAd σ J)
    (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) (c : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) : Prop where
  onC : (matHom _ σ J u).1 * adMat F C = adMat F C
  onZ : (matHom _ σ J u).1 * adMat F Z = adMat F Z + adMat F C * b
  onD : (matHom _ σ J u).1 * adMat F D = adMat F D - adMat F Z * plus σ J₀ b + adMat F C * c


variable (F E) in
abbrev tor (l : Fin j → ℤ) : GL (Fin j) (AF F ⊗[F] E) := GlobalTheory.Eis.Conv.dg (GlobalTheory.Eis.Conv.halfE F E) l


variable (F) in
abbrev bse : ℝ := 4 ^ Fintype.card (InfinitePlace F)

end GlobalTheory.SphEis

end
end

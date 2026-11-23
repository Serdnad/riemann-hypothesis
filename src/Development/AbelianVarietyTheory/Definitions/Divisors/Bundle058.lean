module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AbelianVarietyTheory.Definitions.Foundations.TableDegreeElevenProduct
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.IsPrimeToPLat
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
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
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.LogAbsVpOfNormalised
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2145
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatCM

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CM GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.HTLat.OmegaRank GlobalTheory.EigenSplit GlobalTheory.Frames ReciprocityTheory.ChartRestriction.G.Pdiv Formalism.L2.Pj
open scoped CategoryTheory.Obj NNReal

section Index

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]


variable (K) in
def detSpan (m : ℕ) (L : Submodule (𝓞 K) V) : Submodule (𝓞 K) (⋀[K]^m V) :=
  Submodule.span (𝓞 K) {w | ∃ y : Fin m → V, (∀ i, y i ∈ L) ∧ w = exteriorPower.ιMulti K m y}


variable (K) in
def idx (m : ℕ) (L N : Submodule (𝓞 K) V) : Ideal (𝓞 K) := (detSpan K m N).colon (detSpan K m L)

end Index

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
  {ρ : 𝓞 K} {σ₁ : K →+* ℂ} {p q : ℕ} (X : CMObj H K ρ σ₁ p q)

def phiP (a : Fin p) : (X.A true).t.G ⟶ X.B.t.G := X.φ (Sum.inl a)

def phiQ (a : Fin q) : (X.A false).t.G ⟶ X.B.t.G := X.φ (Sum.inr a)

def IsGram (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin q) (Fin q) (𝓞 E)) : Prop :=
  (∀ a b, WeilEq X.B.t.PP.L (phiP X a) (phiP X b) (X.A true).t.PP.L ((X.A true).t.act.act (gP a b)) (𝟙 _)
    (spMap (σ₁.comp (algebraMap (𝓞 K) K)))) ∧
  ∀ a b, WeilEq X.B.t.PP.L (phiQ X a) (phiQ X b) (X.A false).t.PP.L ((X.A false).t.act.act (gQ a b)) (𝟙 _)
    (spMap (σ₁.comp (algebraMap (𝓞 K) K)))

variable {X} (FP : GenFib (X.A true).pol) (FQ : GenFib (X.A false).pol) (FB : GenFib X.B.pol)
  (MP : Fin p → ((Fin FP.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))) (MQ : Fin q → ((Fin FQ.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K)))

def IsDiffs : Prop := (∀ a, FP.IsDiffOf FB (phiP X a) (MP a)) ∧ ∀ a, FQ.IsDiffOf FB (phiQ X a) (MQ a)

def subP (τ : 𝓞 E →+* 𝓞 K) : Submodule (𝓞 K) (Fin FB.P₀.g → K) :=
  ⨆ a, (FP.eigLat (X.A true).t.act τ).map ((MP a).restrictScalars (𝓞 K))

def subQ (τ : 𝓞 E →+* 𝓞 K) : Submodule (𝓞 K) (Fin FB.P₀.g → K) :=
  ⨆ a, (FQ.eigLat (X.A false).t.act τ).map ((MQ a).restrictScalars (𝓞 K))

end GlobalTheory.FlatCM

end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing GlobalTheory.Vanishing.H0 GlobalTheory.HermTools GlobalTheory.HilbertSamuel
open GlobalTheory.AllWt (Psi secZ exOf wtOf cuspOn latOn normOn petOn GoodOn suppOn LiesOn LiesOff)
open GlobalTheory.FlagMod (FlagCover FlagModel Frames frX ev)
open GlobalTheory.FlagTan (dimFlag psiSet TIx IsTanFrame)
open GlobalTheory.CompHt (hodgeWt uPrime)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

section Data

variable {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c)

def tanOrd (Dw : Datum H) : Fin (dimFlag Dw) ≃ TIx Dw (psiSet H) := by
  classical exact (Fintype.equivFinOfCardEq (FlagTan.card_TIx (FlagTan.isHalf_psiSet H))).symm

variable {X Z} (M : Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw))

abbrev toFlag : M.X ⟶ X.YY := M.σ ≫ inc₀ X Z

abbrev flagIdx (la : AllWt.Weight Dw) (k : X.F.J) : ((L₀ X Z la).pull M.σ).ι := ((common₀ X Z).pull M.σ).idx la k


open Classical in
def IsKS (ω : H0 M.str (LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)) M.off) : Prop :=
  ∀ (K : Type) [Field K] [Algebra c.F K] (P Q : FrPt Xo c K) (t : Ix Dw → Kˣ)
    (v : TIx Dw (psiSet H) → FrPt Xo c (DualNumber K)) (z : Sp K ⟶ M.X)
    (zv : TIx Dw (psiSet H) → (Sp (DualNumber K) ⟶ M.X)) (i : M.K.bundle.ι) (k : X.F.J) (O : M.X.Opens)
    (hO : O ≤ M.K.bundle.U i) (g : Fin (dimFlag Dw) → Γ(M.X, O)) (hz : ⊤ ≤ z ⁻¹ᵁ O) (hzv : ∀ b, ⊤ ≤ zv b ⁻¹ᵁ O)
    (hk : ⊤ ≤ (z ≫ toFlag M) ⁻¹ᵁ X.F.U k) (ho : ⊤ ≤ z ⁻¹ᵁ M.off)
    (hi : ⊤ ≤ z ⁻¹ᵁ (LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).U (i, flagIdx M _ k)),
    X.F.ChartFr k (z ≫ toFlag M) hk Q → FrBor t Q P → IsTanFrame (psiSet H) P v →
    (∀ b, zv b ≫ toFlag M = X.ptY (v b)) →
    H0.val (B := LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)) z (i, flagIdx M _ k) ho hi ω *
        (Matrix.of fun a b => (evalPt (zv (tanOrd Dw b)) O (hzv _) (g a)).snd).det =
      (∏ ix, t ix ^ exOf Dw (FlagTan.kap Dw) 0 ix).val * evalPt z O hz (M.K.jacobian i hO g)

structure CanId where

  ω : H0 M.str (LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)) M.off

  unit : NowhereZero ω

  isKS : IsKS M ω

variable {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : WtPar Dw)


variable (Z) in
instance (priority := high) cuspAddCommGroup (la : AllWt.Weight Dw) : AddCommGroup (Cusp Z U la) :=
  Submodule.addCommGroup _


variable (Z) in
instance (priority := high) cuspModule (la : AllWt.Weight Dw) : Module c.F (Cusp Z U la) := Submodule.module _


variable (X Z) in
abbrev Choice : Type 1 :=
  Resol (common₀ X Z) (U₀ X Z) (dimFlag Dw) (space X Z U P.u₁) (space X Z U P.u₂)

variable {U P} (R : Choice X Z U P) (ω : CanId R.toModif)

def adjSec (h₁ : FreeOnOpen X Z U P.u₁) (j : ℕ) : Cusp Z U (P.wt j) →ₗ[c.F] H0 R.str (R.adj j) R.off :=
  (R.adjEquiv ω.ω ω.unit h₁ j (P.kap_add j)).toLinearMap ∘ₗ R.pullOff ∘ₗ cuspSec X Z U (P.wt j)

theorem adjSec_injective (h₁ : FreeOnOpen X Z U P.u₁) (j : ℕ) : Function.Injective (adjSec R ω h₁ j) :=
  (R.adjEquiv ω.ω ω.unit h₁ j (P.kap_add j)).injective.comp
    ((R.bijective_pullOff (isLB_L₀ X Z _)).1.comp (cuspSec_injective X Z U _))

theorem mulPole_adjSec (h₁ : FreeOnOpen X Z U P.u₁) (j : ℕ) (f : Cusp Z U (P.wt j)) :
    R.mulPole j R.off (adjSec R ω h₁ j f) = R.mulCan ω.ω (P.kap_add j) (R.pullOff (cuspSec X Z U _ f)) :=
  R.mulPole_adjEquiv _ ω.unit h₁ _ _ _

def adjGlobal (j : ℕ) : Submodule c.F (H0 R.str (R.adj j) R.off) := LinearMap.range (restr le_top)

variable (x : ℝ) {D : Formalism.BasicNotions.D7} (V : (c.F →+* ℂ) → Formalism.BasicNotions.TH.HSp D)
  (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r)


variable (Z U) in
abbrev CuspFrame (la : AllWt.Weight Dw) : Type :=
  LatFrame (normOn U x V dict Z (wtOf Dw la 0)) (latOn U Z (wtOf Dw la 0))


variable {x V dict} in
theorem nonempty_cuspFrame {la : AllWt.Weight Dw} (h : GoodOn U x V dict Z (wtOf Dw la 0)) :
    Nonempty (CuspFrame Z U x V dict la) :=
  let ⟨N, n, b, w, A, hf⟩ := CompHt.exists_isFrame CompHt.conj_comp_ne
    (fun σ f => CompHt.petOn_conj U x V dict Z _ σ f.1) h.1 h.2.1 h.2.2
  ⟨⟨N, n, b, w, A, hf⟩⟩

structure Ready : Prop where

  conn : GeometricallyConnected R.str

  one_le : 1 ≤ dimFlag Dw

  le_T : dimFlag Dw + 1 ≤ P.T

  ext₁ : Extends X Z U P.u₁

  ext₂ : Extends X Z U P.u₂

  free₁ : FreeOnOpen X Z U P.u₁

  free₂ : FreeOnOpen X Z U P.u₂

  good : ∀ j ≤ P.T, GoodOn U x V dict Z (wtOf Dw (P.wt j) 0)

  global_le : ∀ j ≤ P.T, adjGlobal R j ≤ LinearMap.range (adjSec R ω free₁ j)

  le_global : LinearMap.range (adjSec R ω free₁ 0) ≤ adjGlobal R 0

variable {R ω x V dict} (h : Ready R ω x V dict) (f₁ : CuspFrame Z U x V dict P.u₁) (f₂ : CuspFrame Z U x V dict P.u₂)
  (th : R.L.Sec) (k : Consts)

def Ready.geo : Geo c.F :=
  R.geo (dense_U₀ X Z) h.conn h.one_le h.free₁ h.free₂ h.ext₁.equiv h.ext₂.equiv f₁ f₂ th k.abelian₂

def Ready.data : Data c.F :=
  dataOf (S := fun j => Cusp Z U (P.wt j)) (Nm := fun j => normOn U x V dict Z (wtOf Dw (P.wt j) 0))
    (M := fun j => latOn U Z (wtOf Dw (P.wt j) 0)) (h.geo f₁ f₂ th k) P.T h.le_T (adjSec R ω h.free₁) (adjSec_injective R ω h.free₁)
    (fun j hj => nonempty_cuspFrame (h.good j hj)) h.global_le h.le_global k

namespace Ready

theorem data_numbers : (h.data f₁ f₂ th k).D = dimFlag Dw ∧ (h.data f₁ f₂ th k).T = P.T ∧ (h.data f₁ f₂ th k).j₀ = 1 ∧
    (h.data f₁ f₂ th k).n = f₁.n ∧ (h.data f₁ f₂ th k).abelian₂ = k.abelian₂ ∧ (h.data f₁ f₂ th k).beta = k.beta ∧
    (h.data f₁ f₂ th k).LamD = k.LamD ∧ (h.data f₁ f₂ th k).LamT = k.LamT ∧ (h.data f₁ f₂ th k).J = k.J :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def equivV {j : ℕ} (hj : j ≤ P.T) : Cusp Z U (P.wt j) ≃ₗ[c.F] (h.data f₁ f₂ th k).V j :=
  dataEquiv (S := fun j => Cusp Z U (P.wt j)) (Nm := fun j => normOn U x V dict Z (wtOf Dw (P.wt j) 0))
    (M := fun j => latOn U Z (wtOf Dw (P.wt j) 0)) (h.geo f₁ f₂ th k) P.T h.le_T (adjSec R ω h.free₁) (adjSec_injective R ω h.free₁)
    (fun j hj => nonempty_cuspFrame (h.good j hj)) h.global_le h.le_global k hj

theorem coe_equivV {j : ℕ} (hj : j ≤ P.T) (f : Cusp Z U (P.wt j)) :
    (h.equivV f₁ f₂ th k hj f).1 = adjSec R ω h.free₁ j f :=
  coe_dataEquiv (S := fun j => Cusp Z U (P.wt j)) (Nm := fun j => normOn U x V dict Z (wtOf Dw (P.wt j) 0))
    (M := fun j => latOn U Z (wtOf Dw (P.wt j) 0)) (h.geo f₁ f₂ th k) P.T h.le_T (adjSec R ω h.free₁)
    (adjSec_injective R ω h.free₁) (fun j hj => nonempty_cuspFrame (h.good j hj)) h.global_le h.le_global k hj f

theorem equivV_mem {j : ℕ} (hj : j ≤ P.T) (f : Cusp Z U (P.wt j)) :
    h.equivV f₁ f₂ th k hj f ∈ (h.data f₁ f₂ th k).M j ↔ f ∈ latOn U Z (wtOf Dw (P.wt j) 0) :=
  dataEquiv_mem (S := fun j => Cusp Z U (P.wt j)) (Nm := fun j => normOn U x V dict Z (wtOf Dw (P.wt j) 0))
    (M := fun j => latOn U Z (wtOf Dw (P.wt j) 0)) (h.geo f₁ f₂ th k) P.T h.le_T (adjSec R ω h.free₁)
    (adjSec_injective R ω h.free₁) (fun j hj => nonempty_cuspFrame (h.good j hj)) h.global_le h.le_global k hj f

theorem nrm_equivV {j : ℕ} (hj : j ≤ P.T) (σ : c.F →+* ℂ) (f : Cusp Z U (P.wt j)) :
    ((h.data f₁ f₂ th k).nm j).nrm σ (h.equivV f₁ f₂ th k hj f) = petOn U x V dict Z (wtOf Dw (P.wt j) 0) σ f :=
  nrm_dataEquiv (S := fun j => Cusp Z U (P.wt j)) (Nm := fun j => normOn U x V dict Z (wtOf Dw (P.wt j) 0))
    (M := fun j => latOn U Z (wtOf Dw (P.wt j) 0)) (h.geo f₁ f₂ th k) P.T h.le_T (adjSec R ω h.free₁)
    (adjSec_injective R ω h.free₁) (fun j hj => nonempty_cuspFrame (h.good j hj)) h.global_le h.le_global k hj σ f

theorem ofSec_comb (w : Cusp Z U P.u₁) : H0.ofSec R.str ⊤ ((h.data f₁ f₂ th k).comb (f₁.b.equivFun w)) =
    R.Δ₁.lift (h.ext₁.equiv w) :=
  (R.ofSec_comb R.Δ₁ h.ext₁.equiv f₁ k.abelian₂ _).trans (by rw [LinearEquiv.symm_apply_apply])

theorem mem_lattice (w : Cusp Z U P.u₁) :
    f₁.b.equivFun w ∈ (h.data f₁ f₂ th k).lattice ↔ w ∈ latOn U Z (wtOf Dw P.u₁ 0) := f₁.mem_span_iff w

theorem normAt_eq (σ : c.F →+* ℂ) (w : Cusp Z U P.u₁) :
    (h.data f₁ f₂ th k).normAt σ (f₁.b.equivFun w) = petOn U x V dict Z (wtOf Dw P.u₁ 0) σ w := f₁.isFrame.norm σ w

theorem d_eq : (h.data f₁ f₂ th k).d = Module.finrank c.F (Cusp Z U (P.wt P.T)) :=
  (h.data f₁ f₂ th k).d_eq_finrank.trans (h.equivV f₁ f₂ th k le_rfl).finrank_eq.symm

theorem mulW_adjSec (j : ℕ) (w : Cusp Z U P.u₁) (f : Cusp Z U (P.wt j)) (g : Cusp Z U (P.wt (j + 1)))
    (hg : g.1 = w.1 * f.1) :
    (h.data f₁ f₂ th k).mulW j (f₁.b.equivFun w) (adjSec R ω h.free₁ j f) = adjSec R ω h.free₁ (j + 1) g := by
  have e₀ : cuspSec X Z U _ g = ((common₀ X Z).addChart (P.u₁_add_wt j)).mul (cuspSec X Z U _ w) (cuspSec X Z U _ f) :=
    sec₀_mul X Z ((exOf_add_zero _ _).symm.trans (congrArg (exOf Dw · 0) (P.u₁_add_wt j))) _ _ _ hg
  have e₁ : R.pullOff (cuspSec X Z U _ w) = restr le_top (H0.pull R.σ le_top (h.ext₁.equiv w).1) :=
    (congrArg R.pullOff (h.ext₁.restr_equiv w).symm).trans
      ((pull_restr _ _ _ _).trans (restr_pull (isLB_L₀ X Z _) _ _ _ _).symm)
  have e₂ : R.pullOff (cuspSec X Z U _ g) = (R.com.addChart (P.u₁_add_wt j)).mul (R.pullOff (cuspSec X Z U _ w))
      (R.pullOff (cuspSec X Z U _ f)) :=
    (congrArg R.pullOff e₀).trans (((common₀ X Z).addChart (P.u₁_add_wt j)).pull_mul R.σ R.off_eq.le _ _)
  have e₃ := R.adjEquiv_mul ω.ω ω.unit h.free₁ j (P.kap_add j) (P.kap_add (j + 1)) (P.u₁_add_wt j) (h.ext₁.equiv w)
    (R.pullOff (cuspSec X Z U _ f))
  have e₄ : restr le_top (R.Δ₁.lift (h.ext₁.equiv w)) =
      H0.ofSec R.str R.off ((h.data f₁ f₂ th k).comb (f₁.b.equivFun w)) :=
    (congrArg (restr le_top) (h.ofSec_comb f₁ f₂ th k w).symm).trans (restr_ofSec _ _)
  rw [← e₁, ← e₂, e₄] at e₃
  exact (LinearMap.congr_fun ((h.geo f₁ f₂ th k).mulW_apply j _) _).trans e₃.symm

end Ready

end Data

def be (N : OT.Num) : ℝ := Real.exp N.lbe

def Consts.ofTable (N : OT.Num) (h : 0 ≤ N.lbe) (lam lamD lamT J : ℝ) (hD : 0 ≤ lamD) (hT : 0 ≤ lamT) : Consts :=
  ⟨Real.exp lam, be N, Real.exp lamD, Real.exp lamT, J, Real.one_le_exp h, Real.one_le_exp hD, Real.one_le_exp hT⟩

end GlobalTheory.CompHS
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix
open IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct Classical ComplexOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LKGeo

variable {p : ℕ} [Fact p.Prime]

abbrev VQ (D : Datum p) : Type := ℚ ⊗[ℤ] D.La

def actQ (D : Datum p) (b : D.O) : Module.End ℚ (VQ D) :=
  (DistribSMul.toLinearMap ℤ D.La b).baseChange ℚ

def actOn {C V : Type} [Ring C] [Algebra ℚ C] [AddCommGroup V] [Module ℚ V] (rep : C →ₐ[ℚ] Module.End ℚ V)
    (R : Type) [CommRing R] [Algebra ℚ R] : R ⊗[ℚ] C →ₐ[R] Module.End R (R ⊗[ℚ] V) :=
  Algebra.TensorProduct.lift (Algebra.ofId R _) ((Module.End.baseChangeHom ℚ R V).comp rep)
    (fun x _ => Algebra.commute_algebraMap_left x _)

structure Link (D : Datum p) (G : HTGroup p) where

  e : D.F ≃+* G.F
  n_eq : G.n = D.n

  rep : G.C →ₐ[ℚ] Module.End ℚ (VQ D)
  rep_inj : Function.Injective rep
  rep_range : ∀ A : Module.End ℚ (VQ D), (∃ x, rep x = A) ↔ ∀ b, A * actQ D b = actQ D b * A
  rep_F : ∀ c : 𝓞 D.F, rep (algebraMap G.F G.C (e c)) = actQ D (algebraMap (𝓞 D.F) D.O c)
  adj : ∀ x v w, D.EF.baseChange ℚ (rep x v) w = D.EF.baseChange ℚ v (rep (sh G x) w)

  ρp : ℤ_[p]
  ρp_eq : ∃ h : e D.ω ∈ G.Kq, G.u ⟨e D.ω, h⟩ = (ρp : ℚ_[p])

  s : Fin D.a → (G.F →+* AlgebraicClosure ℚ)
  s_C : ∀ i x, G.iotaC (s i (e x)) = D.tau i x

  w : Fin D.a → Fin G.m
  s_P : ∀ i x, G.iotaP (s i x) = G.emb (w i) x
  sig : ∀ v, sigPosH (G.gram_herm v) = 1 ↔ ∃ i, v = InfinitePlace.mk (G.iotaC.comp (s i))
  orient : ∃ J : ℝ ⊗[ℚ] G.C, J * J = -1 ∧ (starT G.star ℝ J).unop = -J ∧
    (∀ x, x ≠ 0 → 0 < (D.EF.baseChange ℚ).baseChange ℝ (actOn rep ℝ J x) x) ∧
    ∀ v : InfinitePlace G.F,
      ((if v.embedding (e D.ω) = D.ρc then -Complex.I else Complex.I) • (G.gram v * G.psiR v J)).PosDef

def HasDivPlace (G : HTGroup p) : Prop :=
  ∃ w : HeightOneSpectrum (𝓞 G.F), (p : 𝓞 G.F) ∉ w.asIdeal ∧
    ∀ x : w.adicCompletion G.F ⊗[G.F] G.C, x ≠ 0 → IsUnit x

def RegAf (G : HTGroup p) (ga : G.GAf) : Prop :=
  ∃ v : AwayP p, ∀ x y : v.1.adicCompletion ℚ ⊗[ℚ] G.C,
    Commute x ((ubcMap (AfP.eval v) ga).1.1 : v.1.adicCompletion ℚ ⊗[ℚ] G.C) →
    Commute y ((ubcMap (AfP.eval v) ga).1.1 : v.1.adicCompletion ℚ ⊗[ℚ] G.C) → Commute x y

def IsIntAf (a : AfP p) : Prop := ∀ v : AwayP p, AfP.eval v a ∈ v.1.adicCompletionIntegers ℚ

def LaHat (D : Datum p) : AddSubgroup (AfP p ⊗[ℚ] VQ D) :=
  AddSubgroup.closure {z | ∃ (a : AfP p) (x : D.La), IsIntAf a ∧ z = a ⊗ₜ ((1 : ℚ) ⊗ₜ x)}

def inAf (D : Datum p) (x : D.La) : AfP p ⊗[ℚ] VQ D := (1 : AfP p) ⊗ₜ ((1 : ℚ) ⊗ₜ x)

def mulKQ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ) : KQ p K r →ₐ[ℚ_[p]] PadicAlgCl p :=
  Algebra.TensorProduct.lift K.val (Qr p r).val (fun _ _ => Commute.all _ _)

namespace Link

variable {D : Datum p} {G : HTGroup p} (L : Link D G)

def actG : G.GAf →* Module.End (AfP p) (AfP p ⊗[ℚ] VQ D) :=
  ((actOn L.rep (AfP p)).toRingHom.toMonoidHom.comp (Units.coeHom _)).comp
    ((MonoidHom.fst _ _).comp (UPts G.star (AfP p)).subtype)

def CongOne (N : ℕ) (g : G.GAf) : Prop := ∀ v ∈ LaHat D, ∃ w ∈ LaHat D, L.actG g v = v + N • w

theorem CongOne.mul {N : ℕ} {g h : G.GAf} (hg : L.CongOne N g) (hh : L.CongOne N h) : L.CongOne N (g * h) := by
  intro v hv
  obtain ⟨w, hw, e1⟩ := hh v hv
  obtain ⟨w', hw', e2⟩ := hg (v + N • w) (add_mem hv (nsmul_mem hw N))
  refine ⟨w + w', add_mem hw hw', ?_⟩
  rw [map_mul, Module.End.mul_apply, e1, e2, smul_add, add_assoc]

def KN (N : ℕ) : Subgroup G.GAf where
  carrier := {g | L.CongOne N g ∧ L.CongOne N g⁻¹}
  one_mem' := by
    have h : L.CongOne N 1 := fun v _ => ⟨0, zero_mem _, by simp⟩
    exact ⟨h, by simpa using h⟩
  mul_mem' := fun hg hh => ⟨CongOne.mul L hg.1 hh.1, by rw [_root_.mul_inv_rev]; exact CongOne.mul L hh.2 hg.2⟩
  inv_mem' := fun hg => ⟨hg.2, by simpa using hg.1⟩

end Link

section Points

variable {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {k : Type} [Field k] {β : R →+* k} {N N' : ℕ}

abbrev TIso (o : Obj b N (spMap β)) : Type :=
  TateIsoO D k (Over.mk (𝟙 (Sp k)) ⟶ o.A) (fun c g => g ≫ o.act.act c)
    (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z))

variable {G : HTGroup p} (L : Link D G)

variable [CharP k p] [PerfectRing k p]

def Compat (b : Base D R) (β : R →+* k) (red : (Obar p).toSubring →+* k) : Prop :=
  WittVector.constantCoeff (GlobalTheory.IsogParam.zpW p k L.ρp) = β b.ρ ∧
    ∀ (i : Fin D.a) (c : 𝓞 D.F) (z : (Obar p).toSubring), (z : PadicAlgCl p) = G.emb (L.w i) (L.e c) →
      red z = β (b.t i c)

structure Frame (T : Theory p) (red : (Obar p).toSubring →+* k) (r : ℕ) (H : PDivGroup p k) (act : D.O → (H ⟶ H))
    (rat : ℤ → (H ⟶ H) → Prop) (d : (w : Fin G.m) → GL (Fin G.n) (KQ p (G.Fw w) r)) where

  io : GlobalTheory.LKLoc.intR p (_root_.GlobalTheory.LKRes.Q0 p) r →+* WittVector p k
  io_red : ∀ (a : GlobalTheory.LKLoc.intR p (_root_.GlobalTheory.LKRes.Q0 p) r) (z : (Obar p).toSubring),
    (z : PadicAlgCl p) = ((a : Qr p r) : PadicAlgCl p) → WittVector.constantCoeff (io a) = red z

  sp : ∀ w, D.O →+* Matrix (Fin D.m) (Fin D.m) (intKQ p (G.Fw w) r)
  sp_F : ∀ w (c : 𝓞 D.F), (sp w (algebraMap (𝓞 D.F) D.O c)).map (intKQ p (G.Fw w) r).subtype =
    Matrix.scalar (Fin D.m) (inclK p (G.Fw w) r (G.embW w (L.e c)))

  B : ∀ w, Matrix (Fin D.m) (Fin G.n) (intKQ p (G.Fw w) r) →+ T.M H
  B_smul : ∀ w (a : GlobalTheory.LKLoc.intR p (_root_.GlobalTheory.LKRes.Q0 p) r) (a' : intKQ p (G.Fw w) r), (a' : KQ p (G.Fw w) r) = inclQ p (G.Fw w) r a →
    ∀ X, B w (a' • X) = io a • B w X
  B_act : ∀ w c X, T.map (act c) (B w X) = B w ((sp w c)ᵀ * X)
  B_span : Submodule.span (WittVector p k) (⋃ w, Set.range (B w)) =
    LinearMap.ker (T.map (act (algebraMap (𝓞 D.F) D.O D.ω)) - GlobalTheory.IsogParam.zpW p k L.ρp • LinearMap.id)
  B_rat : ∀ w m ψ X, rat m ψ → T.map ψ (B w X) = m • (fun x => T.F H x)^[r] (B w X)
  B_F : ∀ w X, ∃ Y : Matrix (Fin D.m) (Fin G.n) (intKQ p (G.Fw w) r), Y.map (intKQ p (G.Fw w) r).subtype =
    HMul.hMul (α := Matrix (Fin D.m) (Fin G.n) (KQ p (G.Fw w) r)) (β := Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) r))
      ((X.map (intKQ p (G.Fw w) r).subtype).map (sigKQ p (G.Fw w) r)) ((d w)⁻¹).val ∧ T.F H (B w X) = B w Y

end Points

structure Setup {D : Datum p} {G : HTGroup p} (L : Link D G) {R : Type} [CommRing R] (b : Base D R)
    (β : R →+* AlgebraicClosure (ZMod p)) (red : (Obar p).toSubring →+* AlgebraicClosure (ZMod p)) (N r : ℕ) : Prop where
  simple : D.IsSimple
  div : HasDivPlace G
  three : 3 ≤ N
  cop : N.Coprime p
  pos : 0 < r
  rat : ∀ x, β x ^ p ^ r = β x
  compat : Compat L b β red

end GlobalTheory.LKGeo
end
end

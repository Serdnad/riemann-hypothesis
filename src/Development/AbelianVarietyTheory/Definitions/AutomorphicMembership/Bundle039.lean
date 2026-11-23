module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsUnitOfNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle024
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.KerMemAbLocus
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.SubsingletonOfLeOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle107
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle024
public import Formalism.LocalToGlobal.LatticeGeometry.Bundle002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.TrueGeo GlobalTheory.Cartier

namespace GlobalTheory.ShFam.Pad

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)

abbrev Letter : Type := Σ τ : E →+* ℂ, Fin (Dw.mult τ)

def letters : List (Letter Dw) :=
  (List.finRange (Fintype.card (E →+* ℂ))).flatMap fun a =>
    (List.finRange (Dw.mult ((Fintype.equivFin (E →+* ℂ)).symm a))).map fun i => ⟨_, i⟩

abbrev Sym (E : Type) [Field E] : Type := (ℕ → Bool) × Option ℝ × (((E →+* ℂ) × ℕ) ⊕ ℕ)

def letterOf : ((E →+* ℂ) × ℕ) ⊕ ℕ → Option (Letter Dw)
  | .inl (τ, k) => if h : k < Dw.mult τ then some ⟨τ, ⟨k, h⟩⟩ else none
  | .inr k => (letters Dw)[k]?


open Classical in
def expo (w : Sym E →₀ ℤ) (x : Letter Dw) : ℤ := w.sum fun a n => if letterOf Dw a.2.2 = some x then n else 0


open Classical in
def parOf (w : Sym E →₀ ℤ) : Option ℝ := if h : w.support.Nonempty then h.choose.2.1 else none

variable {Dw}


open Classical in
def lnStep {X : Scheme.{0}} (t : SAB H X) {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] (x : Sp C ⟶ X)
    (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber C) ⟶ t.G.left)) (p : ℕ) (b : Bool) :
    ((E →+* ℂ) × ℕ) ⊕ ℕ → ℝ
  | .inl (τ, k) => if h : k < Dw.mult τ then Real.log (grNorm t x (lat t p x b) (u τ) ⟨k, h⟩) -
      (if b ∧ τ (H.rt : E) = H.rt0 then vDiff E p * Real.log p else 0) else 0
  | .inr k => if h : k < (letters Dw).length then
      Real.log (grNorm t x (lat t p x b) (fun i => u ((letters Dw).get i).1 ((letters Dw).get i).2) ⟨k, h⟩) else 0

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

def divOf (n : Letter Dw → ℤ) : Y.Y.Dv := ∑ x, n x • Y.gr x.1 x.2

def resP (v : HeightOneSpectrum (𝓞 F)) : ℕ := ringChar (𝓞 F ⧸ v.asIdeal)

def ioOf (p : ℕ) [Fact p.Prime] {v : HeightOneSpectrum (𝓞 F)} (ε : Ext v) : AlgebraicClosure F →+* ℂ_[p] :=
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure F) := Algebra.IsAlgebraic.trans ℚ F _
  haveI : Nonempty (AlgebraicClosure F →+* ℂ_[p]) := ⟨(IsAlgClosed.lift : AlgebraicClosure F →ₐ[ℚ] ℂ_[p]).toRingHom⟩
  Classical.epsilon fun io => ∀ a, ‖io a‖ ≤ 1 ↔ a ∈ ε.O


open Classical in
def lgOf (w : Sym E →₀ ℤ) (v : HeightOneSpectrum (𝓞 F)) (ε : Ext v) (y : AlgPt Y.Y) : ℝ :=
  if hp : (resP v).Prime then
    haveI := Fact.mk hp
    let f := (Y.gr_spec (below y.1)).choose_spec.choose
    let t := (Y.gr_spec (below y.1)).choose_spec.choose_spec.choose
    let ψ : Y.Y.X.presheaf.stalk (below y.1) →+* ℂ_[resP v] := (ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom
    Real.log (ε.w (valAt y.1 (((∏ x : Letter Dw, t x.1 x.2 ^ expo Dw w x) *
        (eqn (divOf Y (expo Dw w)) (below y.1))⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn))) +
      (-Real.log (ε.w (resP v)) / Real.log (resP v)) *
        w.sum fun a n => (n : ℝ) * lnStep Z.t (spMap ψ ≫ stalkPt Y.Y (below y.1) ≫ Y.π ≫ genι Z)
          (fun τ i => spMap (dualMap ψ) ≫ f.v τ i) (resP v) (a.1 (resP v)) a.2.2
  else 0

abbrev Mets (C : CxSt F) : Type := ∀ (_ : Option ℝ) (σ : F →+* ℂ) (n : Letter Dw → ℤ), C.Met Y.Y σ (divOf Y n)

def adlOf {C : CxSt F} (hm : Mets Y C) (w : Sym E →₀ ℤ) : Adl C Y.Y where
  D := divOf Y (expo Dw w)
  n := 1
  m σ := hm (parOf w) σ _
  ci := 0
  lg := lgOf Y w


variable (Dw) in
def rootSym (a : ℕ → Bool) (R : Option ℝ) (τ : E →+* ℂ) (i : ℕ) : Sym E →₀ ℤ :=
  if i < Dw.p then Finsupp.single (a, R, .inl (τ, i)) 1
  else Finsupp.single (a, R, .inl (conjEmb τ, Dw.p + Dw.q - 1 - i)) (-1)

def wholeSym (a : ℕ → Bool) (R : Option ℝ) {g : ℕ} : Fin g ⊕ Fin g → (Sym E →₀ ℤ)
  | .inl k => Finsupp.single (a, R, .inr k) 1
  | .inr k => Finsupp.single (a, R, .inr (Fin.rev k)) (-1)


variable (Dw) in
def detSym (a : ℕ → Bool) (R : Option ℝ) (τ : E →+* ℂ) : Sym E →₀ ℤ :=
  ∑ i ∈ Finset.range (Dw.p + Dw.q), rootSym Dw a R τ i

def IsFlat (τ : E →+* ℂ) (σ : Y.Y.Fn) : Prop :=
  ∀ y : Y.Y.X, (divOf Y (expo Dw (detSym Dw (fun _ => false) none τ))).GeneratesAt y σ

def IsCoord {k : Type} [Field k] {φ : c.F →+* k} {x : Sp k ⟶ Z.X} (p : Sp k ⟶ Y.Y.X) (g : EigFrame Z φ x)
    (n : Letter Dw → ℤ) (σ : Y.Y.Fn) (a : k) : Prop :=
  ∃ (y : Y.Y.X) (ψ : Y.Y.X.presheaf.stalk y →+* k) (φ₁ : c.F →+* Y.Y.X.presheaf.stalk y)
    (f : EigFrame Z φ₁ (stalkPt Y.Y y ≫ Y.π ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Y.Fnˣ)
    (t' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ) (r : Y.Y.X.presheaf.stalk y),
    p = spMap ψ ≫ stalkPt Y.Y y ∧ f.Tri (algebraMap (Y.Y.X.presheaf.stalk y) Y.Y.X.functionField) Y.f0 t ∧
      f.Tri ψ g t' ∧
      algebraMap (Y.Y.X.presheaf.stalk y) Y.Y.X.functionField r =
        σ * ((∏ z : Letter Dw, t z.1 z.2 ^ n z : Y.Y.Fnˣ) : Y.Y.Fn) ∧
      a = ψ r * ((∏ z : Letter Dw, t' z.1 z.2 ^ (-n z) : kˣ) : k)

def FlagPt.frame {Ω : Type} [Field Ω] (y : FlagPt Z Ω) : EigFrame Z y.fK (y.y ≫ genι Z) :=
  ⟨y.u, y.tan, y.eig, y.basis⟩

end Free

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ) (fl : s.Flag)
  {C : CxSt D.what₂.LL} (hm : ∀ k, Mets (fl.C k) C)

def arIn : ArIn D.what₂.Tau N (D.R.f * N) s.Comp where
  A _ := Sym D.host.E →₀ ℤ
  num k := polar fun w => (adlOf (fl.C k) (hm k) w).arTop
  root a R x _ := rootSym S.Dw a (some R) (DV.tauEmb D x.1) x.2
  whole a R x _ := wholeSym a (some R) x

def setB (κ : Lv A) (B : ℝ) : Finset ℕ :=
  (Finset.range (⌊B⌋₊ + 1)).filter Nat.Prime ∪ (2 * (NumberField.discr D.host.E).natAbs * κ.l.M').primeFactors

def flatSec (k : s.Comp) (τ : D.what₂.Tau) : (fl.C k).Y.Fn := Classical.epsilon (IsFlat (fl.C k) (DV.tauEmb D τ))

def innerPt (k : s.Comp) : (fl.C k).Y.X :=
  Classical.epsilon fun x => IsClosed ({x} : Set (fl.C k).Y.X) ∧ (fl.C k).π x ∉ genBd s.T.Z

def flatSt : FlatSt s where
  sv τ y := Classical.epsilon fun a => ∃ (k : s.Comp) (p : Sp Qb ⟶ (fl.C k).Y.X), p ≫ (fl.C k).π = y.y ∧
    IsCoord (fl.C k) p y.frame (expo S.Dw (detSym S.Dw (fun _ => false) none (DV.tauEmb D τ))) (flatSec s fl k τ) a
  ht B k τ := (adlOf (fl.C k) (hm k) (detSym S.Dw (ArIn.ind (setB κ B)) none (DV.tauEmb D τ))).ht (innerPt s fl k)

def degFrame (k : s.Comp) (τ : D.what₂.Tau) : ℝ :=
  (adlOf (fl.C k) (hm k) (detSym S.Dw (fun _ => false) none (DV.tauEmb D τ))).ht (innerPt s fl k)

def degFlat (k : s.Comp) (τ : D.what₂.Tau) : ℝ :=
  degFrame s fl hm k τ + (S.Dw.q : ℝ) * (Real.log A.H.d -
    Real.log (NumberField.discr D.host.E).natAbs / (Module.finrank ℚ D.host.E : ℝ))

end GlobalTheory.ShFam.Pad
end
end

section



noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.BoundaryLocalData GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)

namespace GlobalTheory.LocM

section Dim

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
variable {Y : Model Xo c β} {p : ℕ} {C : SCF p} {P : PointsOfFlagModel.PtC Y C}

theorem generic_dim (A : DatAt Y P) : A.U.A.g = Module.finrank ℚ E / 2 * (Dw.p + Dw.q) := by
  have := A.t.semi.smooth
  have := A.t.semi.geomConnected
  have d₀ : SmoothOfRelativeDimension (0 + A.U.A.g) (pullback.snd A.t.G.hom (Out.jK A.R)) := by
    have := A.U.A.smoothDim
    have : IsIso A.U.U.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map A.U.U.gen.hom))
    rw [show pullback.snd A.t.G.hom (Out.jK A.R) = A.U.U.gen.hom.left ≫ A.U.A.A.hom from (Over.w A.U.U.gen.hom).symm]
    infer_instance
  have d₁ := GenericDim.smoothOfRelativeDimension_of_generic A.R A.t.G _ d₀
  have e : spMap (DatAtCheck.fC A) ≫ A.ι = P.y ≫ Y.jQ ≫ pullback.fst _ _ := by
    refine Eq.trans ?_ P.ext
    rw [← A.fac, ← Category.assoc]
    exact congrArg (· ≫ A.ι) (Spec.map_comp (CommRingCat.ofHom A.f) (CommRingCat.ofHom (intO ↥C.S).subtype))
  have p₁ := (IsPullback.of_hasPullback A.t.G.hom (spMap (DatAtCheck.fC A))).paste_horiz A.m.cart.1
  have p₂ := (IsPullback.of_hasPullback Y.oF.t.G.hom P.y).paste_horiz Y.m.cart.1
  rw [e] at p₁
  have d₂ : SmoothOfRelativeDimension (0 + A.U.A.g) (pullback.snd A.t.G.hom (spMap (DatAtCheck.fC A))) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) d₁
  have d₃ : SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) (pullback.snd Y.oF.t.G.hom P.y) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _)
      (ObjDim.smoothOfRelativeDimension Y.oF)
  have d₄ : SmoothOfRelativeDimension (0 + Module.finrank ℚ E / 2 * (Dw.p + Dw.q))
      (pullback.snd A.t.G.hom (spMap (DatAtCheck.fC A))) := by
    rw [← p₁.isoIsPullback_hom_snd _ _ p₂]
    infer_instance
  have : Surjective A.t.G.hom := inferInstance
  obtain ⟨x, -⟩ := (pullback.snd A.t.G.hom (spMap (DatAtCheck.fC A))).surjective (Per.gen ↥C.S)
  simpa using H1.dim_unique _ d₂ d₄ x

theorem dim_add_rank (A : DatAt Y P) :
    A.U.D.toPre.P.g + Module.finrank ℤ A.Ylat = Module.finrank ℚ E / 2 * (Dw.p + Dw.q) := by
  have h := UT.dim_eq_rank_add_dim firstFiveLaws A.R _ ⟨A.noeth, inferInstance, A.normal, A.complete⟩ A.U.D A.U.A A.t.G
    A.t.semi A.U.U
  rw [← generic_dim A, add_comm]
  exact h.symm

end Dim

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

theorem finrank_host_eq (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  rw [D.host.finrank_cmField]
  unfold Ranks.f Ranks.n
  ring

theorem complexConj_eq_conj (D : D7) (x : D.host.E) : IsCMField.complexConj D.host.E x = D.host.conj x := by
  apply D.host.φ₀.injective
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

namespace At

variable (ct : At S κ p) {Z : ct.Mdl} (y : ct.Pt Z)

def beLin : ct.Ylat y →ₗ[ℤ] ct.Ylat y →ₗ[ℤ] ℝ := (ct.dat y).beLin (PointLawsEdge.betaAdd _ p)

def evidence : Per.Reading (ct.dat y) := (Per.nonempty_reading ct.hp.one_lt (ct.dat y)).some

def tauVal (a : ct.Ylat y) (χ : ct.chX y) : ((ct.fld y).C)ˣ := (ct.evidence y).t a ((ct.phi y).symm χ)

def lineShift (a : ct.Ylat y) : ct.chX y := ct.phi y a

def mulFst (a b : ct.Ylat y) : ct.chX y := ct.lineShift y (a + b) - ct.lineShift y a

def mulSnd (a b : ct.Ylat y) : ct.chX y := ct.lineShift y (a + b) - ct.lineShift y b

def mulConst (a b : ct.Ylat y) : ((ct.fld y).C)ˣ :=
  Exists.choose (p := fun t : (↥y.C.S)ˣ => Per.IsTauVal (ct.dat y).f ((ct.evidence y).e a b) (t : ↥y.C.S))
    ⟨(ct.evidence y).t a b, (ct.evidence y).isVal a b⟩

def abDim : ℕ := (ct.dat y).U.D.toPre.P.g

theorem isTauVal_mulConst (a b : ct.Ylat y) :
    Per.IsTauVal (ct.dat y).f ((ct.evidence y).e a b) ((ct.mulConst y a b : ((ct.fld y).C)ˣ) : (ct.fld y).C) :=
  Exists.choose_spec (p := fun t : (↥y.C.S)ˣ => Per.IsTauVal (ct.dat y).f ((ct.evidence y).e a b) (t : ↥y.C.S)) _

theorem mulFst_eq (a b : ct.Ylat y) : ct.mulFst y a b = ct.phi y b := by
  rw [mulFst, lineShift, lineShift, map_add (f := _), add_sub_cancel_left]

theorem mulSnd_eq (a b : ct.Ylat y) : ct.mulSnd y a b = ct.phi y a := by
  rw [mulSnd, lineShift, lineShift, map_add (f := _), add_sub_cancel_right]

theorem mulConst_eq (a b : ct.Ylat y) : ct.mulConst y a b = ct.tauVal y a (ct.phi y b) :=
  Units.ext ((ct.evidence y).eq_of_isTauVal (ct.isTauVal_mulConst y a b))

theorem abDim_add : ct.abDim y + Module.finrank ℤ (ct.Ylat y) = D.R.f * N := by
  have h := dim_add_rank (ct.dat y)
  rw [finrank_host_eq, S.rank_eq, Nat.mul_div_cancel_left _ two_pos] at h
  exact h

end At

def motTrue (ct : At S κ p) : MotSt ct where
  be y := ct.beLin y
  be_symm y a b := (ct.dat y).beta_symm a b
  be_bal y c c' h a b := PointLawsEdge.betaBal _ p _ _ (ct.dat y) c c' (h.trans (complexConj_eq_conj D _).symm) a b
  be_posDef y := PointLawsEdge.betaPosDef _ ct.hp.one_lt _ _ (ct.dat y)
  yl_rank y := by
    obtain ⟨ρ, h₁, h₂, h₃⟩ := PointLawsEdge.rank_le (ct.dat y)
    rw [finrank_host_eq, Nat.mul_div_cancel_left _ two_pos] at h₁
    have := S.p_eq
    have := S.rank_eq
    exact ⟨ρ, h₁, fun _ _ => by omega⟩
  psiV y a := vU p (ct.mulConst y a (w0 D • a))
  tau y := ct.tauVal y
  tau_add_left y a a' χ := (ct.evidence y).add_left a a' _
  tau_add_right y a χ χ' := (ct.evidence y).add_right a χ χ'
  tau_symm y a b := (ct.evidence y).symm a b
  tau_smul y c a χ := (ct.evidence y).bal c a χ
  be_tau y a b := (ct.evidence y).beta_eq a b
  multiplicationLatticeFirst y := ct.mulFst y
  multiplicationLatticeSecond y := ct.mulSnd y
  mulC y := ct.mulConst y
  psiV_def _ _ := rfl
  dimB y := ct.abDim y
  dimB_add y := ct.abDim_add y
  be_eq _ _ _ := rfl

section Api

variable (ct : At S κ p) {Z : ct.Mdl} (y : ct.Pt Z)

theorem motTrue_mul (a b : ct.Ylat y) : (motTrue ct).multiplicationLatticeFirst y a b = ct.phi y b ∧ (motTrue ct).multiplicationLatticeSecond y a b = ct.phi y a ∧
    (motTrue ct).mulC y a b = (motTrue ct).tau y a (ct.phi y b) :=
  ⟨ct.mulFst_eq y a b, ct.mulSnd_eq y a b, ct.mulConst_eq y a b⟩

theorem motTrue_psiV_eq_be (a : ct.Ylat y) : (motTrue ct).psiV y a = (motTrue ct).be y a (w0 D • a) := by
  rw [(motTrue ct).psiV_def, (motTrue_mul ct y _ _).2.2, (motTrue ct).be_tau]

theorem motTrue_psiV_half (a : ct.Ylat y) : (motTrue ct).psiV y a = (motTrue ct).be y a a / 2 := by
  have h := (motTrue ct).be_bal y (w0 D) (1 - w0 D) (one_sub_halfSqrt_eq_conj D) a a
  rw [sub_smul, one_smul, map_sub, (motTrue ct).be_symm y (w0 D • a)] at h
  rw [motTrue_psiV_eq_be]
  linarith

end Api

end GlobalTheory.LocM
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.TrueGeo

namespace GlobalTheory.ShFam

variable {D : D7} {A : Amb D}

structure CmList (A : Amb D) : Type where
  ψ : D.what₂.Tau ≃ GlobalTheory.AllWt.Psi A.H
  ψ_val : ∀ t, (ψ t).1 = DV.tauEmb D t

section One

variable {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ) (L : CmList A)

theorem Lv.good_σ₀ (κ : Lv A) : Formalism.L2.PjFree.GoodEmb κ.c κ.σ₀ := rfl

theorem FinalTheorems.isUnf : Formalism.L2.PjFree.IsUnf (s.U κ.σ₀) := (s.unf _ κ.good_σ₀).1

instance FinalTheorems.compNe : Nonempty s.Comp := (s.unf _ κ.good_σ₀).2.1

abbrev FinalTheorems.Bd : Type :=
  ∀ k : s.Comp, GlobalTheory.HodgeDomain.BdData D.what₂.Tau j (N - j)
    (GlobalTheory.TrueCx.gammaU ((s.U κ.σ₀).X k) (GlobalTheory.TrueCx.le_of_isUnf _ s.isUnf S.p_eq) (GlobalTheory.TrueCx.cmEquiv _ s.isUnf L.ψ k))

def FinalTheorems.cx (B : s.Bd L) (fl : s.Comp → D.what₂.Tau → ℂˣ) : CxPkg D.what₂.Tau N j s.Comp :=
  GlobalTheory.TrueCx.cxTrue (s.U κ.σ₀) s.isUnf S.p_eq (lt_of_lt_of_le two_pos S.two_le) L.ψ B fl

def Sig.wt (S : Sig A N j) (L : CmList A) : (D.what₂.Tau → Fin N → ℤ) →+ GlobalTheory.AllWt.Weight S.Dw where
  toFun la := fun τ i => la (L.ψ.symm τ) (Fin.cast S.rank_eq i)
  map_zero' := rfl
  map_add' _ _ := rfl

def FinalTheorems.Lw (Φ : s.Flag) (k : s.Comp) : (D.what₂.Tau → Fin N → ℤ) →+ (Φ.C k).Y.Dv :=
  AddMonoidHom.mk' (fun la => (Φ.C k).Lw (S.wt L la)) fun a b => by
    have h := GlobalTheory.AllWt.exOf_add (Dw := S.Dw) (S.wt L a) (S.wt L b) 0 0
    rw [add_zero] at h
    simp only [FlagCpt.Lw, map_add (f := _), h]

variable (C : CxSt D.what₂.LL) (K : CutSt C) (R : ResSt C)

def FinalTheorems.alg (Φ : s.Flag) (hd : ∀ k, (Φ.C k).Y.dim = Formalism.DegreeFormula.dimFl D.what₂.Tau N)
    (Mb : ℝ → (D.what₂.Tau → Fin N → ℝ) → ℚ → ∀ k, Adl C (Φ.C k).Y) :
    AlgPkg (geoOf C K R) D.what₂.Tau N s.Comp where
  Yv k := (Φ.C k).Y
  Ybd k := (Φ.C k).Ybd
  bd k := (Φ.C k).bd
  bd_supp _ := rfl
  Lw k := s.Lw L Φ k
  dim_eq := hd
  degA _ M := Adl.deg M
  degA_ofW k Δ W ι := deg_ofW C _ Δ W ι
  degA_twist _ M ci cf := deg_twist M ci cf
  semipos M := ∀ k, Adl.SemiPos (M k)
  nefFib M := ∀ k, Adl.NefFib (M k)
  Mbar := Mb

structure Kit (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)) (ng : NgPkg) : Type 1 where
  Φ : s.Flag
  dim_eq : ∀ k, (Φ.C k).Y.dim = Formalism.DegreeFormula.dimFl D.what₂.Tau N
  key : KeySec s.Xo κ.c
  B : s.Bd L
  fl : s.Comp → D.what₂.Tau → ℂˣ
  Mb : ℝ → (D.what₂.Tau → Fin N → ℝ) → ℚ → ∀ k, Adl C (Φ.C k).Y
  pad : PadPkg D N j s.Comp jC ng
  levIn : ∀ M, pad.levIn M ↔ κ.inK M

end One

section Fam

variable (F : SrcFam A) (L : CmList A) (C : CxSt D.what₂.LL) (K : CutSt C) (R : ResSt C)
  (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)) (ng : NgPkg)

abbrev Kits : Type 1 := ∀ N j hN hj (κ : Lv A), Kit (F.src N j hN hj κ) L C jC ng

variable {F L C jC ng} (k : Kits F L C jC ng)

abbrev Kits.at (w : Dat D (Lv A)) : Kit (F.at w) L C jC ng := k w.N w.j w.two_le w.j_le w.κ

def shimOf (w : Dat D (Lv A)) : ShimU D (geoOf C K R) jC ng w where
  Comp := (F.at w).Comp
  cx := (F.at w).cx L (k.at w).B (k.at w).fl
  alg := (F.at w).alg L C K R (k.at w).Φ (k.at w).dim_eq (k.at w).Mb
  pad := (k.at w).pad

abbrev FormsOver : Type 1 :=
  FormsPkg D (geoOf C K R) (fun j => (datW D F.κg j).N) (fun j => (shimOf K R k (datW D F.κg j)).Comp)
    (fun j => (shimOf K R k (datW D F.κg j)).alg)
    (fun j p => ((shimOf K R k (datW D F.κg j)).pad.loc p).Pt ((shimOf K R k (datW D F.κg j)).pad.loc p).YY)

def famOf (hg : F.κg.primes = Finset.univ.image D.host.g) (P : FormsOver K R k) : ShimFam D (geoOf C K R) (Lv A) where
  levPr := Lv.primes
  levPr_prime _ _ hp := Nat.prime_of_mem_primeFactors hp
  κg := F.κg
  levPr_κg := hg
  jC := jC
  ng := ng
  U := shimOf K R k
  forms := P

end Fam

section Comparison₂

def ambOf (Q : Par D) (h : Q.PinHost) : Amb D := ⟨Q.H, h.1, h.2.1, h.2.2.1⟩

abbrev MD {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : Type 1 :=
  Σ (l : Level H) (Dw : Datum H), Moduli Dw l

structure ParTie (Q : Par D) (h : Q.PinHost) (F : SrcFam (ambOf Q h)) : Prop where
  same : ∀ j, InR D j → (⟨Q.l, Q.Dw j, Q.Xo j⟩ : MD Q.H) =
    ⟨F.κg.l, (F.sig _ _ (datW D F.κg j).two_le (datW D F.κg j).j_le).Dw, (F.at (datW D F.κg j)).Xo⟩
  le : Q.c.F ≤ F.κg.c.F

variable {T : Top D} (h : LawsP T) {F : SrcFam (ambOf T.Q h.pins.1)} (t : ParTie T.Q h.pins.1 F) {L : CmList (ambOf T.Q h.pins.1)}
  {C : CxSt D.what₂.LL} (K : CutSt C) (R : ResSt C) {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)} {ng : NgPkg}
  (k : Kits F L C jC ng)

end Comparison₂

end GlobalTheory.ShFam
end
end

module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle035
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers

open scoped ComplexOrder

namespace GlobalTheory.HSCore

section Lattice

variable {K : Type} [Field K] [NumberField K]

def vecHt {n : ℕ} (a : Fin n → K) (c : (K →+* ℂ) → ℝ) : ℝ :=
  ((∑ᶠ v : FinitePlace K, Real.log (⨆ k, v (a k))) + ∑ τ : K →+* ℂ, Real.log (c τ)) / (Module.finrank ℚ K : ℝ)

end Lattice

section Geometry

variable {K : Type} [Field K] [NumberField K] (X : Data K) (s : Fin X.D → Fin X.N → K)

def filV (a : ℕ) : Submodule K (X.V X.T) := (Fil (X.ideal s) a (spaceV X s)).comap (X.V X.T).subtype

variable {X s}

def symV {hs : X.IsGood s} {δ : ℕ} (Co : Coord X.toGeo hs δ) (a : ℕ) :
    filV X s a →ₗ[K] (MonoDeg (Fin X.D) a × Fin δ → K) :=
  if h : a ≤ X.T then
    (LinearMap.pi fun q : MonoDeg (Fin X.D) a × Fin δ =>
      (LinearMap.proj q.2 : (Fin δ → K) →ₗ[K] K) ∘ₗ (Co.ev (X.T - a)).toLinearMap ∘ₗ LinearMap.proj q.1) ∘ₗ
      hs.sym (Nat.sub_add_cancel h) (spaceV X s) ∘ₗ (X.V X.T).subtype.restrict fun _ hx => hx
  else 0

def Coord.gen {G : Geo K} {s : Fin G.D → Fin G.N → K} {hs : G.IsGood s} {δ : ℕ} (Co : Coord G hs δ) (k : Fin G.n) (p : Fin δ) : K :=
  ∑ j, G.w j k * Co.y p j

def Coord.c₁ {G : Geo K} {s : Fin G.D → Fin G.N → K} {hs : G.IsGood s} {δ : ℕ} (Co : Coord G hs δ) (σ : K →+* ℂ) (p : Fin δ) : ℝ :=
  archSize (G.A σ) fun k => σ (Co.y p k)


end Geometry

def RegSeq {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) (F : Y.Modules) (t : List L.Sec) : Prop :=
  List.rec (motive := fun _ => Y.Modules → Prop) (fun _ => True)
    (fun a _ ih G => Mono (GlobalTheory.cutHom G hL a) ∧ ih (GlobalTheory.cut G hL a)) t F

theorem regSeq_cons {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) (F : Y.Modules) (a : L.Sec) (r : List L.Sec) :
    RegSeq hL F (a :: r) ↔ Mono (GlobalTheory.cutHom F hL a) ∧ RegSeq hL (GlobalTheory.cut F hL a) r := Iff.rfl

def VanishFrom {Y : Scheme.{0}} (L : LB Y) (F : Y.Modules) (j₀ : ℤ) : Prop :=
  ∀ j : ℤ, j₀ ≤ j → ∀ q : ℕ, 0 < q → Subsingleton (coh (GlobalTheory.twistZ F L j) q)

end GlobalTheory.HSCore
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

section Point

variable {n : ℕ} {r : Type} [Fintype r] [DecidableEq r]

def curvEv (G : V n → Matrix r r ℂ) (v : V n) : Matrix r r (Ev n) := (curvPoly G v).map (MvPolynomial.aeval sym)

def powAt (G : V n → Matrix r r ℂ) (v : V n) (k : ℕ) : Ev n := (curvEv G v ^ k).trace

def transAt (G G' : V n → Matrix r r ℂ) (v : V n) (k : ℕ) : Alt n :=
  ∑ a, ∑ i ∈ Finset.range k, ((curvEv G v ^ i *
    (conn G v (coordVec a) - conn G' v (coordVec a)).map (algebraMap ℂ (Ev n)) * curvEv G' v ^ (k - 1 - i)).trace : Ev n) * dz a

end Point

section Minors

variable {s : ℕ}

def leadMinor (G : Matrix (Fin s) (Fin s) ℂ) (j : ℕ) : ℂ :=
  (G.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < j} → Fin s) Subtype.val).det

def grD (G : Matrix (Fin s) (Fin s) ℂ) (i : Fin s) : ℝ := (leadMinor G (i + 1)).re / (leadMinor G i).re

def ldPart (G : Matrix (Fin s) (Fin s) ℂ) : Matrix (Fin s) (Fin s) ℂ := Matrix.of fun i j =>
  (G.submatrix (fun a : {a : Fin s // (a : ℕ) < j + 1} => if a.1 = j then i else a.1) Subtype.val).det / leadMinor G j

end Minors

section Manifold

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) {r : Type} [Fintype r] [DecidableEq r]

def HolUnitAt (T : M → Matrix r r ℂ) (y : M) : Prop :=
  IsUnit (T y).det ∧ ∀ i, y ∈ (A.e i).source → ∀ a b,
    ∀ᶠ v in 𝓝 (A.e i y), DifferentiableAt ℂ (fun u => T ((A.e i).symm u) a b) v

def SmoothUnitAt (G : M → Matrix r r ℂ) (y : M) : Prop :=
  IsUnit (G y).det ∧ ∀ i, y ∈ (A.e i).source → ∀ᶠ v in 𝓝 (A.e i y), MContDiffAt ∞ (fun u => G ((A.e i).symm u)) v

structure IsGramPair (G G' : M → M → Matrix r r ℂ) : Prop where

  smooth : ∀ y, SmoothUnitAt A (G y) y ∧ SmoothUnitAt A (G' y) y

  trans : ∀ y, ∀ᶠ z in 𝓝 y, ∃ T K K' : M → Matrix r r ℂ, HolUnitAt A T z ∧ HolUnitAt A K z ∧ HolUnitAt A K' z ∧
    ∀ᶠ w in 𝓝 z, G z w = T w * G y w * (K w)ᴴ ∧ G' z w = T w * G' y w * (K' w)ᴴ

def powFld (G : M → M → Matrix r r ℂ) (k : ℕ) (x : A.Pt) : Ev n := powAt (fun v => G x.pt (x.ch.symm v)) x.crd k

def chernFld (G : M → M → Matrix r r ℂ) (j : ℕ) (x : A.Pt) : Ev n := A.chern (G x.pt) j x

def transFld (G G' : M → M → Matrix r r ℂ) (k : ℕ) : A.Fld := fun x =>
  transAt (fun v => G x.pt (x.ch.symm v)) (fun v => G' x.pt (x.ch.symm v)) x.crd k

def DbarCoh (w w' : A.Pt → Ev n) : Prop :=
  A.IsForm (LineForm.fld A w) ∧ A.IsForm (LineForm.fld A w') ∧ A.dbar (LineForm.fld A w) = 0 ∧
    A.dbar (LineForm.fld A w') = 0 ∧ ∃ u, A.IsForm u ∧ LineForm.fld A w - LineForm.fld A w' = A.dbar u

end Manifold

section Variety

variable {F : Type} [Field F] {ι : Type} {m k : ι → ℕ} {X Y : Var F} {σ : F →+* ℂ}

def atlas (X : Var F) (σ : F →+* ℂ) : HolAtlas (CxPts X.str σ) X.dim where
  ι := AlgChart X.str σ X.dim
  e c := c.e
  cover y := have := X.smooth_str; AlgChart.exists_mem_source y
  holo c c' := c.holo_trans c'

structure IsMetricFr (E : Fr (ratOf X) m k) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ) : Prop where

  posDef : ∀ y, ∀ A ∈ E.S (under y), ∀ τ, (H A y τ).PosDef

  smooth : ∀ y, ∀ A ∈ E.S (under y), ∀ τ i j, CInfAt (fun z => (H A z τ i j).re) y ∧ CInfAt (fun z => (H A z τ i j).im) y

  trans : ∀ y, ∀ A ∈ E.S (under y), ∀ A' ∈ E.S (under y), ∀ τ,
    H A' y τ = (A' * A⁻¹).map (ratVal · y) τ * H A y τ * ((A' * A⁻¹).map (ratVal · y) τ)ᴴ

theorem isMetricFr_of_isMetricOn {E : Fr (ratOf X) m 0} {H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ}
    (h : IsMetricOn E ⊤ H) : IsMetricFr E H :=
  ⟨fun y => h.posDef y mem_ptsIn_top, fun y => h.smooth y mem_ptsIn_top, fun y => h.trans y mem_ptsIn_top⟩

variable (E : Fr (ratOf X) m k) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ)

def gramAt (τ : ι) (y z : CxPts X.str σ) : Matrix (Fin (m τ)) (Fin (m τ)) ℂ := H (E.nonempty (under y)).choose z τ

def chernF (x : ι × ℕ) : (atlas X σ).Pt → Ev X.dim := chernFld (atlas X σ) (gramAt E H x.1) x.2

def grF (x : Root m) (p : (atlas X σ).Pt) : Ev X.dim :=
  ofValues (ddc (fun v => -Real.log (grD (gramAt E H x.1 p.pt (p.ch.symm v)) x.2)) p.crd)

def c1W {L : LB X.X} (ψ : Weight X.str σ L) (p : (atlas X σ).Pt) : Ev X.dim :=
  ofValues (ddc (fun v => ψ.φ (pick ψ.isLB p.pt) (p.ch.symm v)) p.crd)

def ptMap (σ : F →+* ℂ) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str) : CxPts Y.str σ → CxPts X.str σ := PtsOver.map f hf _

def pullGram (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str) (B : Mat m Y.Fn) (z : CxPts Y.str σ) : Mat m ℂ :=
  fun τ => (B * (Mat.map (E.nonempty (under (ptMap σ f hf z))).choose φ)⁻¹).map (ratVal · z) τ *
    H (E.nonempty (under (ptMap σ f hf z))).choose (ptMap σ f hf z) τ *
    ((B * (Mat.map (E.nonempty (under (ptMap σ f hf z))).choose φ)⁻¹).map (ratVal · z) τ)ᴴ

end Variety

section Inhabitants

end Inhabitants

end GlobalTheory.ChernCalc
end
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FactorDepth

namespace GlobalTheory.RefSum

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) {c : Coeff l} {p : ℕ}

def PolyBetween (la : PointsOfFlagModel.abelian₂ p c) {n : ℕ} (P : MvPolynomial (LtN Dw n) c.F) (A B : ℝ) : Prop :=
  letI := H.starRing
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∀ y : IntFr Xo c T io, y.IsAlg →
    ∀ (Ch : IntegralChartA3 Xo c T io y) (k : ℕ),
      (A : EReal) ≤ nuLocOf Ch (vV T.V (p : T.Fr)).toNat k (MvPolynomial.map io P) ∧
        nuLocOf Ch (vV T.V (p : T.Fr)).toNat k (MvPolynomial.map io P) ≤ (B : EReal)


variable (l) in
def HalfSplit (g g' : ℕ) (π π' : 𝓞 E) : Prop :=
  g.Prime ∧ g'.Prime ∧ g ≠ g' ∧ l.M = g' * g ∧ π * H.bar π = (g : 𝓞 E) ∧ π' * H.bar π' = (g' : 𝓞 E) ∧
    l.Mb = Ideal.span {π * π'} ∧ GlobalTheory.PtTie.SplitsIn E g ∧ GlobalTheory.PtTie.SplitsIn E g'

theorem HalfSplit.symm {g g' : ℕ} {π π' : 𝓞 E} (h : HalfSplit l g g' π π') : HalfSplit l g' g π' π := by
  obtain ⟨a, b, c, d, e, f, i, j, k⟩ := h
  exact ⟨b, a, c.symm, d.trans (mul_comm _ _), f, e, by rw [i, mul_comm], k, j⟩

end Free

def JetNum (D : D7) (dF : ℕ) (cst : ℝ) : Prop :=
  ∀ k, 4 * dF + 4 ≤ D.host.g k ∧ (dF : ℝ) * (2 * Real.sqrt (2 * D.R.f * D.R.m)) < D.host.g k ∧
    GlobalTheory.PtTie.rr0 D * (2 * D.R.f * D.R.m : ℝ) ^ 3 * ((D.R.r : ℝ) * (2 * D.R.f * D.R.m) / 4 + 2 * (dF : ℝ) ^ 2) / D.host.g k ≤ cst

end GlobalTheory.RefSum

end
end

section

open NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct Classical

namespace GlobalTheory.AdTh

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def IdxIs {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} (c : Coeff l) (σ : c.F →+* ℂ) {r g : ℕ} (X : Data E r) (idx : Fin g ≃ X.Ψ × Fin r)
    (e : Fin g ≃ Lt1 Dw) : Prop :=
  (∀ x v j, pv X idx x v j = perFr X x v (relab c σ (e j).1) (e j).2) ∧ ∀ j, rowType X (idx j) = relab c σ (e j).1

def GenReads {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r g : ℕ} (U : Unf Xo c σ r) (k : U.Comp)
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.X k).Λ) (idx : Fin g ≃ (U.X k).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw)
    (x : (U.X k).dom) (ϑ : (Fin g → ℂ) → ℂ) : Prop :=
  letI : Algebra c.F ℂ := σ.toAlgebra
  ∃ A : AnFib (U.X k) bas idx e x.1 (U.X k).Λ (unC (Formalism.L2.PjFree.Unf.ofPj U) k x),
    A.Reads 1 (unC (Formalism.L2.PjFree.Unf.ofPj U) k x).s ϑ

variable {D : D7}

def AtComp (θ : InfFam D) (W : HSp D) {r : ℕ} (hr : W.rank = r) {Comp : Type} (X : Comp → Data D.host.E r)
    (dict : GA D W → Σ k, Frame (X k).Ψ r) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (h γ : GA D W) : Prop :=
  γ ∈ GQ W ∧ latR hr (latG W (γ * h)) = (X (dict h).1).Λ ∧
    (dict h).2 = frMove θ W hr (X (dict h).1) (γ * h) (fun τ => x₀ τ.1)

def CcIs (θ : InfFam D) (V W : HSp D) {r : ℕ} (hr : W.rank = r) {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} (U : Unf Xo c σ r)
    (dict : GA D W → Σ k, Frame (U.X k).Ψ r) (mu : GA D W → ℂ) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f₀ : WO V W → ℂ) (cc : U.Comp → ℂ) : Prop :=
  (∀ k, ‖cc k‖ = 1) ∧ ∀ h γ : GA D W, AtComp θ W hr U.X dict x₀ h γ →
    ∀ (hx' : (dict h).2 ∈ (U.X (dict h).1).dom) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.X (dict h).1).Λ)
      (idx : Fin g ≃ (U.X (dict h).1).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw), IsSympl (U.X (dict h).1) bas →
      IdxIs c σ (U.X (dict h).1) idx e → ∀ ϑ : (Fin g → ℂ) → ℂ, GenReads U (dict h).1 bas idx e ⟨(dict h).2, hx'⟩ ϑ →
      ∀ w : WO V W, w.map (finPart D) = 0 →
        om (1, γ * h) f₀ w = cc (dict h).1 * mu h *
          cexp (-(Real.pi / 2 : ℂ) * ∑ b, hx (U.X (dict h).1) bas idx (dict h).2
            (zOf θ V W hr (U.X (dict h).1) idx (dict h).2 w b) (zOf θ V W hr (U.X (dict h).1) idx (dict h).2 w b)) *
          ∏ b, ϑ (zOf θ V W hr (U.X (dict h).1) idx (dict h).2 w b)

theorem CcIs.norm {θ : InfFam D} {V W : HSp D} {r : ℕ} {hr : W.rank = r} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E}
    {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {U : Unf Xo c σ r}
    {dict : GA D W → Σ k, Frame (U.X k).Ψ r} {mu : GA D W → ℂ} {x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ}
    {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {f₀ : WO V W → ℂ} {cc : U.Comp → ℂ}
    (h : CcIs θ V W hr U dict mu x₀ om f₀ cc) (k : U.Comp) : ‖cc k‖ = 1 := h.1 k

end

end GlobalTheory.AdTh
end

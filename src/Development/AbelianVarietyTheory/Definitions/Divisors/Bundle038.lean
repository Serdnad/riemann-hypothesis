module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008

@[expose] public section

section

noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TowU

section Coord

variable {R : Type} [CommRing R] {κ κ₁ : Type}

variable [Fintype κ] [Fintype κ₁] {W W₁ : Type} [AddCommGroup W] [Module R W] [AddCommGroup W₁] [Module R W₁]
  {B : W → W → R} {B₁ : W₁ → W₁ → R}

end Coord

section Frame

variable {R : Type} [CommRing R] {A : Type} [CommRing A] [Algebra R A] (c : A →ₐ[R] A)
  {α α₁ ν : Type} [Fintype α] [DecidableEq α] [Fintype α₁] [DecidableEq α₁] [Fintype ν] [DecidableEq ν]

structure IsFrame (J : Matrix α α A) (C D : Matrix α ν A) (ι : Matrix α α₁ A) : Prop where
  cc : Cᵀ * J * C.map c = 0
  dd : Dᵀ * J * D.map c = 0
  cd : Cᵀ * J * D.map c = 1
  ic : ιᵀ * J * C.map c = 0
  ci : Cᵀ * J * ι.map c = 0
  id : ιᵀ * J * D.map c = 0
  di : Dᵀ * J * ι.map c = 0
  basis : ∃ M : Matrix ((ν ⊕ ν) ⊕ α₁) α A, Matrix.fromCols (Matrix.fromCols C D) ι * M = 1 ∧
    M * Matrix.fromCols (Matrix.fromCols C D) ι = 1

end Frame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


def IsRat {α β κ : Type} [Fintype κ] {B : Matrix α β (AE F E) → Matrix α β (AE F E) → AF F} (d : Darboux B κ) : Prop :=
  ∀ x : Matrix α β E, ∃ y z : κ → F, d.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))

variable (σ : E →ₐ[F] E)

variable {σ}


end GlobalTheory.TowU

end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.HSNef

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

def Le (B A : HermLB p) : Prop :=
  ∃ P : Pair p, P.L = A ∧ P.A = B ∧ (1 : X.functionField) ∈ P.Bl 1 (-1) 1


omit [IsIntegral X] in
def HtNef (M : HermLB p) (D : ℕ) : Prop :=
  M.SemiPos D ∧ ∀ h : X → ℝ, M.IsArithHeight h → ∀ x, 0 ≤ h x

def Total {J : Type} (f : J → X.functionField) : Prop :=
  (∀ j, f j ≠ 0) ∧ ∀ (x : X) (j l : J), RegAt x (f j / f l) ∨ RegAt x (f l / f j)

def SmallFam (B : HermLB p) {J : Type} (f : J → X.functionField) (w : J → ℝ) : Prop :=
  ∃ β : B.B.ι → X.functionFieldˣ, IsRatSec B.B β ∧
    (∀ (x : X) c, x ∈ B.B.U c → ∀ j, RegAt x (f j * (β c : X.functionField))) ∧
    ∀ (σ : k →+* ℂ) (y : CxPts p σ) c, y ∈ ptsIn p σ (B.B.U c) → ∀ j,
      ‖ratVal (f j * (β c : X.functionField)) y‖ * Real.exp (-(B.φ σ).φ c y / 2) ≤ Real.exp (-w j)

def IsFS (M : HermLB p) {J : Type} [Fintype J] (f : J → X.functionField) (w : J → ℝ) : Prop :=
  ∃ ρ : M.B.ι → X.functionFieldˣ, IsRatSec M.B ρ ∧
    (∀ (x : X) c, x ∈ M.B.U c → (∀ j, RegAt x (f j * (ρ c : X.functionField))) ∧ ∃ j, UnitAt x (f j * (ρ c : X.functionField))) ∧
    ∀ (σ : k →+* ℂ) (y : CxPts p σ) c, y ∈ ptsIn p σ (M.B.U c) →
      (M.φ σ).φ c y = Real.log (∑ j, ‖ratVal (f j * (ρ c : X.functionField)) y‖ ^ 2 * Real.exp (2 * w j))

structure IsModel {Y : Scheme.{0}} [IsIntegral Y] (π : Y ⟶ X) (φ : X.functionField →+* Y.functionField) : Prop where

  gen : π (genericPoint Y) = genericPoint X

  deg : π.residueDegree (genericPoint Y) = 1

  compat : ∀ (y : Y) (a : X.presheaf.stalk (π y)),
    φ (algebraMap _ X.functionField a) = algebraMap _ Y.functionField (π.stalkMap y a)

def boxFam {K J : Type} [Field K] {D : ℕ} (e : J → K) (x : Fin D → K) : J × Finset (Fin D) → K :=
  fun c => e c.1 * ∏ i ∈ c.2, x i

def shiftA (P : Pair p) (u : ℝ) : Pair p :=
  ⟨P.L, P.A.shift (fun _ => u) fun _ => rfl, P.r, P.r', P.hr, P.hr'⟩

def GenAt (P : Pair p) (c : ℕ) : Prop :=
  ∃ (n : ℕ) (v : Fin n → X.functionField), (∀ i, v i ∈ P.H 0 c) ∧
    ∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ i, P.nu 0 c σ y (v i) ≠ 0

def Regime (P : Pair p) (D : ℕ) : Prop :=
  ∃ α β : ℝ, ∀ t : ℝ, 0 ≤ t →
    Tendsto (fun m : ℕ => P.lc 0 m (Real.exp (t * m)) / (m : ℝ) ^ (D + 1)) atTop (𝓝 (α + β * t))

def bound (D q : ℕ) (b g : ℝ) : ℝ :=
  let Δ := Real.log ((q : ℝ) / 2)
  let α := (b + (D + 1) * (Δ + D * Real.log 2 / 2) * g) / ((D + 1).factorial * Δ)
  let β := (D + 1) * g / (2 * ((D + 1).factorial * Δ))
  Real.log q * (α + β * Real.log ((α + 2 * β + 1) ^ 2))

def AmpleHS : Prop :=
  ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (P : Pair p) (a : ℝ), IsAmpleLB P.L.B → P.L.SemiPos D → P.L.IsSelfInter a →
      ∃ t₀ : ℝ, ∀ t : ℝ, t₀ ≤ t →
        Tendsto (fun m : ℕ => P.lc m 1 (Real.exp (t * m)) / (m : ℝ) ^ (D + 1)) atTop
          (𝓝 ((a + ((D : ℝ) + 1) * t * gdeg P.L D) / ((D + 1).factorial : ℝ)))

def SemiPull : Prop :=
  ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D E : ℕ), IsArithVar p D → IsArithVar q E →
    ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p), L.SemiPos D → (L.pull π hπ).SemiPos E

theorem shiftA_H (P : Pair p) (u : ℝ) (a b : ℤ) : (shiftA P u).H a b = P.H a b := rfl

end GlobalTheory.HSNef
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.Ex.OneGen GlobalTheory.ThetaPtMove
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.Model

theorem polFib_self {R : Type} [CommRing R] (P : PolAV (Sp R)) : PolFib P.A P.L P.g (𝟙 _) := by
  exact ⟨P, 𝟙 _, rfl, @isGrpPullback_of_iso _ _ _ _ _ (Iso.refl P.A) (inferInstanceAs (IsMonHom (𝟙 P.A))),
    LBIso.chartPull (chartPullId _) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl) (GlobalTheory.PolBaseChange.lbIso_refl P.isLB)⟩

end GlobalTheory.UMin.Model
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.QCoh

namespace GlobalTheory.FlagPush

def IsPull {Z W : Scheme.{0}} [IsIntegral Z] [IsIntegral W] (q : Z ⟶ W) [IsDominant q] (D : CartierDiv Z)
    (E : CartierDiv W) : Prop :=
  ∀ y b, E.IsEqn y b → ∀ x, q x = y → D.IsEqn x (Units.map (functionFieldMap q).toMonoidHom b)

variable {F : Type} [Field F]

structure Dbl (Y : Var F) where

  Z : Scheme.{0}
  [integral : IsIntegral Z]

  p₁ : Z ⟶ Y.X

  p₂ : Z ⟶ Y.X

  δ : Y.X ⟶ Z
  str_eq : p₁ ≫ Y.str = p₂ ≫ Y.str
  proj : IsProjOver (p₁ ≫ Y.str)
  closed : IsClosedImmersion δ
  δ₁ : δ ≫ p₁ = 𝟙 _
  δ₂ : δ ≫ p₂ = 𝟙 _
  diag : ∀ (K : Type) [Field K] (w : Sp K ⟶ Z), w ≫ p₁ = w ≫ p₂ → w (IsLocalRing.closedPoint K) ∈ Set.range δ

attribute [instance] Dbl.integral Dbl.closed

theorem isDominant_of_section {Z W : Scheme.{0}} {p : Z ⟶ W} {s : W ⟶ Z} (h : s ≫ p = 𝟙 _) : IsDominant p :=
  ⟨Function.Surjective.denseRange fun y => ⟨s y, by rw [← Scheme.Hom.comp_apply, h]; rfl⟩⟩

namespace Dbl

variable {Y : Var F} (W : Dbl Y)

instance : IsDominant W.p₁ := isDominant_of_section W.δ₁

instance : IsDominant W.p₂ := isDominant_of_section W.δ₂

def α₁ : Y.Fn →+* W.Z.functionField := functionFieldMap W.p₁

def α₂ : Y.Fn →+* W.Z.functionField := functionFieldMap W.p₂

def num {n : ℕ} (y : Fin n → CartierDiv W.Z) : ℤ :=
  letI := algebraΓOfHom (W.p₁ ≫ Y.str)
  interNum F (structureModule W.Z) fun i => toLB (y i)

def Small : Prop := topologicalKrullDim W.Z ≤ (Y.dim + 1 : ℕ)

def triv (Y : Var F) : Dbl Y where
  Z := Y.X
  p₁ := 𝟙 _
  p₂ := 𝟙 _
  δ := 𝟙 _
  str_eq := rfl
  proj := by rw [Category.id_comp]; exact Y.isProjOver
  closed := inferInstance
  δ₁ := Category.id_comp _
  δ₂ := Category.id_comp _
  diag _ _ _ _ := ⟨_, rfl⟩

end Dbl

section Square

open CategoryTheory.Limits

def Dbl.prod (Y : Var F) : Dbl Y where
  Z := pullback Y.str Y.str
  integral := by
    have : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.str
    exact GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (pullback.fst Y.str Y.str)
  p₁ := pullback.fst _ _
  p₂ := pullback.snd _ _
  δ := pullback.diagonal Y.str
  str_eq := pullback.condition
  proj := ProjSpace.isProjOver_pullback Y.isProjOver Y.isProjOver
  closed := inferInstance
  δ₁ := pullback.diagonal_fst _
  δ₂ := pullback.diagonal_snd _
  diag K _ w h := ⟨(w ≫ pullback.fst _ _) (IsLocalRing.closedPoint K), by
    have e : (w ≫ pullback.fst _ _) ≫ pullback.diagonal Y.str = w := by
      apply pullback.hom_ext <;> simp [h]
    exact (Scheme.Hom.comp_apply _ _ _).symm.trans
      (congrArg (fun u : Sp K ⟶ _ => u (IsLocalRing.closedPoint K)) e)⟩

theorem Dbl.prod_dim (Y : Var F) : topologicalKrullDim (Dbl.prod Y).Z = (Y.dim + Y.dim : ℕ) := by
  have h1 := smoothOfRelativeDimension_isStableUnderBaseChange.{0} Y.dim
  have : SmoothOfRelativeDimension Y.dim (pullback.fst Y.str Y.str) :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension Y.dim)
      (IsPullback.of_hasPullback Y.str Y.str).flip Y.smooth
  have : SmoothOfRelativeDimension (Y.dim + Y.dim) (pullback.fst Y.str Y.str ≫ Y.str) := inferInstance
  have := SmoothOfRelativeDimension.smooth Y.dim (pullback.fst Y.str Y.str)
  have : GeometricallyConnected (pullback.fst Y.str Y.str ≫ Y.str) := GeometricallyConnected.comp _ _
  obtain ⟨V, e, hd, -⟩ := Var.exists_iso (pullback.fst Y.str Y.str ≫ Y.str) (Y.dim + Y.dim) (Dbl.prod Y).proj
  rw [← hd, ← V.topologicalKrullDim_eq]
  exact IsHomeomorph.topologicalKrullDim_eq _ e.hom.homeomorph.isHomeomorph

theorem Dbl.prod_small (Y : Var F) (h : Y.dim ≤ 1) : (Dbl.prod Y).Small := by
  unfold Dbl.Small
  rw [Dbl.prod_dim]
  exact_mod_cast (by omega : Y.dim + Y.dim ≤ Y.dim + 1)

theorem Dbl.prod_ne (Y : Var F) (h : 0 < Y.dim) : (Dbl.prod Y).p₁ ≠ (Dbl.prod Y).p₂ := fun e => by
  have e' : pullback.fst Y.str Y.str = pullback.snd Y.str Y.str := e
  let i : pullback Y.str Y.str ≅ Y.X := ⟨pullback.fst _ _, pullback.diagonal Y.str,
    by apply pullback.hom_ext <;> simp [← e'], pullback.diagonal_fst _⟩
  have h2 := (IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso i).isHomeomorph).trans Y.topologicalKrullDim_eq
  have h3 := (Dbl.prod_dim Y).symm.trans h2
  have : Y.dim + Y.dim = Y.dim := by exact_mod_cast h3
  omega

end Square

def GenPair (Y : Var F) {K : Type} [Field K] (ψ₁ ψ₂ : Y.Fn →+* K) : Prop :=
  ψ₁.comp (algebraMap F Y.Fn) = ψ₂.comp (algebraMap F Y.Fn) ∧
    ∃ (V : ValuationSubring K) (v₁ v₂ : Sp V ⟶ Y.X), spMap (algebraMap V K) ≫ v₁ = spMap ψ₁ ≫ (ratOf Y).pt ∧
      spMap (algebraMap V K) ≫ v₂ = spMap ψ₂ ≫ (ratOf Y).pt ∧
      spMap (IsLocalRing.residue V) ≫ v₁ = spMap (IsLocalRing.residue V) ≫ v₂ ∧
      v₁ (IsLocalRing.closedPoint V) = genericPoint Y.X

variable {ι : Type} {m : ι → ℕ}

def AlmostLow (τ : ι) (a b : Fin (m τ)) {K : Type} [Field K] (C : Mat m K) : Prop :=
  (∀ σ, (C σ).det ≠ 0) ∧ C τ a b ≠ 0 ∧
    ∀ σ (i j : Fin (m σ)), i < j → ¬ ((⟨σ, i⟩ : Root m) = ⟨τ, a⟩ ∧ (⟨σ, j⟩ : Root m) = ⟨τ, b⟩) → C σ i j = 0


open Classical in
def shear (τ : ι) (a b : Fin (m τ)) {K : Type} [CommRing K] (t : K) : Mat m K := fun σ =>
  1 + Matrix.of fun i j => if (⟨σ, i⟩ : Root m) = ⟨τ, a⟩ ∧ (⟨σ, j⟩ : Root m) = ⟨τ, b⟩ then t else 0

def minor (τ : ι) (a b : Fin (m τ)) {K : Type} [CommRing K] (C : Mat m K) : K :=
  C τ a a * C τ b b - C τ a b * C τ b a

end GlobalTheory.FlagPush
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy

namespace GlobalTheory.PairStep

variable {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]

def IsQCart [IsLocallyNoetherian X] (D : X → ℚ) : Prop :=
  ∃ (m : ℕ) (D₀ : CartierDiv X), 0 < m ∧ D₀.Eff ∧ D = qWeil D₀ m

def QNum [IsLocallyNoetherian X] (p : X ⟶ Sp k) (N : LB X) (b : ℚ) (D : X → ℚ) : Prop :=
  letI := algebraΓOfHom p
  ∃ (m : ℕ) (D₀ : CartierDiv X), 0 < m ∧ D₀.Eff ∧ D = qWeil D₀ m ∧
    ∀ C : Closeds X, IsCompleteCurve k C →
      (interNumRed k C ![toLB D₀] : ℚ) / m = b * interNumRed k C ![N]


omit [IsIntegral X] in
def Off (B : X → ℚ) (z : X) : Prop := ∀ w, w ⤳ z → B w = 0

def CentreAt {p : X ⟶ Sp k} (E : DivOver p) (z : X) : Prop :=
  E.Through z ∧ ∀ f : X.functionFieldˣ, RegAt z (f : X.functionField) → E.ord f = 0 →
    RegAt z ((f⁻¹ : X.functionFieldˣ) : X.functionField)

def IsNkltCentre (p : X ⟶ Sp k) (n : ℕ) (Γ : X → ℚ) (z : X) : Prop :=
  ∃ (E : DivOver p) (η : RatForms p n) (m : ℕ) (g : X.functionFieldˣ),
    η ≠ 0 ∧ 0 < m ∧ IsLogEqn p Γ η z m g ∧ CentreAt E z ∧ discrep E η m g ≤ -1

def LcCut (p : X ⟶ Sp k) (n : ℕ) (Γ : X → ℚ) (x : X) (j : ℕ) : Prop :=
  LcAt p n Γ x ∧ ¬ KltAt p n Γ x ∧
    ∀ z, z ⤳ x → ¬ KltAt p n Γ z → topologicalKrullDim (closure ({z} : Set X)) ≤ j

theorem QNum.isQCart [IsLocallyNoetherian X] {p : X ⟶ Sp k} {N : LB X} {b : ℚ} {D : X → ℚ}
    (h : QNum p N b D) : IsQCart D := by
  obtain ⟨m, D₀, hm, he, hD, -⟩ := h
  exact ⟨m, D₀, hm, he, hD⟩

end GlobalTheory.PairStep
end
end

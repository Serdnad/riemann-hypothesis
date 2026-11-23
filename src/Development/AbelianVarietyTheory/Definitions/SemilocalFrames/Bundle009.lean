module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle002
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.HermitianCurvature.StatementD
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section
open NumberField GlobalTheory.DegCnt
namespace GlobalTheory.DegAsm

def pairBd (K : Type) [Field K] [NumberField K] (k g j T x x' : ℕ) : ℝ :=
  let f : ℕ := Formalism.HermitianLatticesTheory.fDeg K
  let Mb : ℝ := (20 * (f : ℝ) * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ 2) ^ (2 * (f : ℝ) * (6 + cf K))
  let D₀ : ℝ := (T : ℝ) ^ (2 * f)
  let Y : ℝ := (x : ℝ) * x' * D₀ ^ 2
  ((x : ℝ) * x') ^ ((k : ℝ) / 2) * Y ^ (6 * (j : ℝ) + 10 + 4 * cf K) *
    (1 + Mb * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ f *
        (∑ s ∈ Finset.Ico 1 k, ((32 / (g : ℝ)) ^ (k * f) * ((4 * k * f : ℕ) : ℝ) ^ (4 * f) * Y ^ 7) ^ s) +
      ((2 / (g : ℝ)) ^ (k * f) * ((4 * k * f : ℕ) : ℝ) ^ (4 * f) * D₀ * x * x') ^ k)

open NumberField in
private lemma vInv_nonneg' (K : Type) [Field K] [NumberField K] :
    0 ≤ _root_.Formalism.HermitianLatticesTheory.vInv K := by
  unfold _root_.Formalism.HermitianLatticesTheory.vInv
  positivity


open NumberField in
theorem _root_.GlobalTheory.DegAsm.pairBd_nonneg (K : Type) [Field K] [NumberField K]
    (k g j T x x' : ℕ) : 0 ≤ _root_.GlobalTheory.DegAsm.pairBd K k g j T x x' := by
  have hv := vInv_nonneg' K
  unfold _root_.GlobalTheory.DegAsm.pairBd
  dsimp only
  have hMb : 0 ≤ (20 * ((_root_.Formalism.HermitianLatticesTheory.fDeg K : ℕ) : ℝ) * (2 * _root_.Formalism.HermitianLatticesTheory.vInv K) ^ 2) ^
      (2 * ((_root_.Formalism.HermitianLatticesTheory.fDeg K : ℕ) : ℝ) * (6 + _root_.GlobalTheory.DegCnt.cf K)) :=
    Real.rpow_nonneg (by positivity) _
  have hY : 0 ≤ (x : ℝ) * x' * ((T : ℝ) ^ (2 * _root_.Formalism.HermitianLatticesTheory.fDeg K)) ^ 2 := by positivity
  have hxx : 0 ≤ (x : ℝ) * x' := by positivity
  refine mul_nonneg (mul_nonneg (Real.rpow_nonneg hxx _) (Real.rpow_nonneg hY _)) ?_
  refine add_nonneg (add_nonneg zero_le_one (mul_nonneg (mul_nonneg hMb (by positivity)) ?_))
    (by positivity)
  exact Finset.sum_nonneg fun s _ => by positivity

end GlobalTheory.DegAsm
end
end

section

noncomputable section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
namespace GlobalTheory.DegAsm
variable {K V W : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
  {H : HermSpace K V} {r : ℕ}

def SameGr (F G : FlagD H r) : Prop := ∀ a : Fin (r + 1), G.e a - F.e a ∈ F.Xa a.val

def Adapt (F F' : FlagD H r) (𝔡 : Ideal (𝓞 K)) (N : NF H r) : Prop := N.𝔡 = 𝔡 ∧ SameGr F N.F ∧ SameGr F' N.F'

def omI (F F' : FlagD H r) (𝔡 : Ideal (𝓞 K)) (Λ : Submodule (𝓞 K) V) : ℝ :=
  sInf ((fun N : NF H r => N.om Λ) '' {N | Adapt F F' 𝔡 N})

def pairM (F F' : FlagD H r) (j : ℕ) : Fin (r + 1) → Fin (r + 1) → K :=
  fun a b => if a.val < j ∧ b.val < j then H.B (F.e a) (F'.e b) else 0

def lab (F F' : FlagD H r) (j : ℕ) : ℕ → K := fun l => if h : l ≤ j ∧ l ≤ r + 1 then Dl F F' l h.2 else 0

def IsEmb (F : FlagD H r) (HW : HermSpace K W) (e : W →ₗ[K] V) : Prop :=
  (∀ x y, H.B (e x) (e y) = HW.B x y) ∧
    ∀ v : V, (∀ a : Fin (r + 1), H.B (F.e a) v = 0) ↔ v ∈ LinearMap.range e ⊔ F.X

def lat0 (F : FlagD H r) (e : W →ₗ[K] V) (Λ : Submodule (𝓞 K) V) : Submodule (𝓞 K) W :=
  (Λ ⊔ rs (𝓞 K) F.X).comap (e.restrictScalars (𝓞 K))

def datOf (F F' : FlagD H r) (e : W →ₗ[K] V) (g : ℕ) (Λ : Submodule (𝓞 K) V) :
    Submodule (𝓞 K) W × Submodule (𝓞 K) (W × W) :=
  ((flagPairDefinitePartLattice F' F Λ ⊔ rs (𝓞 K) F.X).comap (e.restrictScalars (𝓞 K)),
    (iotaGraph F F' Λ (g : 𝓞 K) ⊔ (rs (𝓞 K) F.X).prod (rs (𝓞 K) F.X)).comap ((e.prodMap e).restrictScalars (𝓞 K)))

def IsH (F F' : FlagD H r) (e : W →ₗ[K] V) (γ : V ≃ₗ[K] V) (h : W ≃ₗ[K] W) : Prop :=
  ∀ w : W, ∃ y ∈ wSp F F', y - e (h w) ∈ F.X ∧ y - γ (e w) ∈ F'.X

def FrEqv (F : FlagD H r) (Λ : Submodule (𝓞 K) V) (G G' : FlagD H r) : Prop :=
  ∃ n : V ≃ₗ[K] V, F.InN (n : V →ₗ[K] V) ∧ n • Λ = Λ ∧ ∀ a : Fin (r + 1), n (G.e a) - G'.e a ∈ G'.Xa a.val

def datBd (K : Type) [Field K] [NumberField K] [StarRing K] (k r : ℕ) (Del Db NT x : ℝ) : ℝ :=
  (Del / x) ^ ((k : ℝ) / 2) *
    (8 ^ (r + 1) * (Formalism.HermitianLatticesTheory.fDeg K : ℝ) ^ 2 * Del ^ (3 * cf K + 6) * NT ^ 2 * (Db * Del * NT) ^ (10000 * (r + 1) ^ 3))

theorem adapt_self (N : NF H r) : Adapt N.F N.F' N.𝔡 N :=
  ⟨rfl, fun a => by simp, fun a => by simp⟩
end GlobalTheory.DegAsm
end
end

section

open MeasureTheory NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.FlagMeas

open Formalism.MainNotions.S GlobalTheory.Count

def flagAt (I : AutInst) {a : ℕ} (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (v : InfinitePlace I.F) :
    Fin (a + 1) → Submodule ℂ (Fin I.n → ℂ) :=
  fun i => Submodule.span ℂ ((fun y : Fin I.n → I.E => (I.P v)⁻¹ *ᵥ fun l => I.φ v (y l)) '' (S i : Set _))

def IsSatFlag (I : AutInst) (Λ : Submodule (𝓞 I.E) (Fin I.n → I.E)) {a : ℕ} (j : Fin a → ℕ)
    (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) : Prop :=
  S 0 = ⊥ ∧ Monotone S ∧ (∀ i : Fin a, Formalism.HN.rkK (S i.succ) = Formalism.HN.rkK (S i.castSucc) + j i) ∧
    (∀ i, ∀ y, y ∈ S i ↔ y ∈ Λ ∧ y ∈ Submodule.span I.E (S i : Set (Fin I.n → I.E))) ∧
    ∀ x ∈ S (Fin.last a), ∀ y ∈ S (Fin.last a), Formalism.UG.hform (starRingEnd I.E) I.J x y = 0

def IsGaugeAll (I : AutInst) (c : InfinitePlace I.F → ℝ) : Prop := ∀ v, IsGauge (I.ε v) (c v)

def cIw (p q : ℕ) {a : ℕ} (j : Fin a → ℕ) : ℝ :=
  (2 : ℝ) ^ (-((dimN (p + q) j : ℝ) / 2)) * (volU p * volU q) /
    ((∏ i, volU (j i) * (2 : ℝ) ^ (((j i : ℝ)) ^ 2 / 2)) * volU (p - ∑ i, j i) * volU (q - ∑ i, j i))

def rankFac (E : Type) [Field E] [NumberField E] [StarRing E] (M : ℕ) : ℝ :=
  (2 * Formalism.HermitianLatticesTheory.vInv E) ^ ((Formalism.HermitianLatticesTheory.fDeg E : ℝ) * ((M : ℝ) - 1 / 2)) * Formalism.HermitianLatticesTheory.lValEta E M

end GlobalTheory.FlagMeas
end
end

section

open MeasureTheory NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.Deep

open Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis

def frame (I : AutInst) (x : I.GA) (v : InfinitePlace I.F) : Matrix (Fin I.n) (Fin I.n) ℂ :=
  I.P v * uMat (x.1 v)

def crd (I : AutInst) (x : I.GA) (v : InfinitePlace I.F) (y : Fin I.n → I.E) : EuclideanSpace ℂ (Fin I.n) :=
  WithLp.toLp 2 ((frame I x v)⁻¹ *ᵥ fun i => I.φ v (y i))

def SatX (I : AutInst) (x : I.GA) (S : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Prop :=
  Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) S

def SizesGe (I : AutInst) (x : I.GA) (B B' : Submodule (𝓞 I.E) (Fin I.n → I.E)) (lo : ℝ) : Prop :=
  ∀ N : Submodule (𝓞 I.E) (Fin I.n → I.E), B' < N → N ≤ B → lo ≤ Formalism.HN.sizeQ (bas I) (frm I x) N B'

def SizesLe (I : AutInst) (x : I.GA) (A A' : Submodule (𝓞 I.E) (Fin I.n → I.E)) (hi : ℝ) : Prop :=
  ∀ N : Submodule (𝓞 I.E) (Fin I.n → I.E), A' ≤ N →
    Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) A N → N ≠ A →
      Formalism.HN.sizeQ (bas I) (frm I x) A N ≤ hi

def omega (I : AutInst) (x : I.GA) (W : Submodule I.E (Fin I.n → I.E)) (ρ : ℝ) : Set I.GA :=
  {y | y.2 = x.2 ∧ ∃ A Z : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ,
    (∀ v, Formalism.REAL.inG (I.ε v) (A v) ∧ Formalism.REAL.inG (I.ε v) (Z v)) ∧
    Real.sqrt (∑ v, Formalism.REAL.hs (A v)) + Real.sqrt (∑ v, Formalism.REAL.hs (Z v)) ≤ ρ ∧
    (∀ v, uMat (y.1 v) = uMat (x.1 v) * NormedSpace.exp (A v) * NormedSpace.exp (Z v)) ∧
    ∀ s t : ℝ, ∃ m : I.Ginf, ((m, 1) : I.GA) ∈ I.NA W ∧
      ∀ v, uMat (m v) * uMat (x.1 v) =
        uMat (x.1 v) * NormedSpace.exp ((s : ℂ) • A v) * NormedSpace.exp ((t : ℂ) • Z v)}

def IsReps (B : RowsAut) (T : B.Hs →L[ℂ] B.I.L2 B.μf B.fund) (Fr : B.Hs → B.I.GA → ℂ) : Prop :=
  ∀ P : ℕ, ∀ u ∈ VP B P, GlobalTheory.Dec.IsContRep B (T u) (Fr u) ∧
    (∀ k ∈ B.I.Kg B.g, ∀ y, Fr u (y * (1, k)) = Fr u y) ∧
    ∀ (E : gInf B) (y : B.I.GA),
      HasDerivAt (fun t : ℝ => Fr u (y * ((fun v => expU (t • E v)), 1))) (Fr (dAct B E u) y) 0

def vv (B : RowsAut) {D : ℕ} (Fr : Fin D → B.Hs → B.I.GA → ℂ) (u : B.Hs) (y : B.I.GA) :
    EuclideanSpace ℂ (Fin D) :=
  WithLp.toLp 2 fun i => Fr i u y

end GlobalTheory.Deep
end
end

section

open MeasureTheory NumberField Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace

namespace GlobalTheory.Dec

theorem locDec_of_decGap (hD : GlobalTheory.DSId.DecGap) (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ)
    (hB : IsDSData B d) (hg : GapGe B h)
    (hh : ∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) : LocDec B h := by
  intro v g
  obtain ⟨h1, h2, h3, -⟩ := hB v
  simpa [h3.1] using (hD _ _ _ _ _ h1 h2 h (hg v) (hh v) (uMat g) g.2 _ h3.2 _ h3.2).2

end GlobalTheory.Dec
end

section

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp

def Zr (k r : ℕ) (g : Mat k r) : Matrix (Fin r) (Fin r) ℂ := fun a b => g (esI k r a) (eI k r b)

def BlockAnti {r : ℕ} (β : Fin r → ℕ) (Z : Matrix (Fin r) (Fin r) ℂ) : Prop :=
  Monotone β ∧ Z.det ≠ 0 ∧ (∀ a b, Z a b ≠ 0 → β a = β b) ∧
    ∀ a b a' b', Z a b ≠ 0 → Z a' b' ≠ 0 → β a = β a' → ‖Z a b‖ = ‖Z a' b'‖ ∧ (a = a' → b = b') ∧ (a < a' → b' < b)

def IsNormal (k r : ℕ) (β : Fin r → ℕ) (g : Mat k r) : Prop :=
  g ∈ GG k r ∧ (∀ a : Fin r, g⁻¹ *ᵥ bvec (eI k r a) ∈ Xst k r ∧ g *ᵥ bvec (eI k r a) ∈ Xst k r) ∧ BlockAnti β (Zr k r g)

def lebR (k r : ℕ) (β : Fin r → ℕ) : Measure (Mt k r) :=
  (volume : Measure (UTin β → ℂ)).map fun x => Matrix.of.symm (uEmb k r (upperIn β x))

def NormR (k r : ℕ) (γ : Mat k r) (s : ℝ) (μR : Measure (Mt k r)) : Prop :=
  ∃ n₁ ∈ Nset k r, ∃ n₂ ∈ Nset k r, ∃ (g₀ : Mat k r) (β : Fin r → ℕ), IsNormal k r β g₀ ∧ γ = n₁ * g₀ * n₂ ∧
    μR = (ENNReal.ofReal s • lebR k r β).map (conjM n₂⁻¹)

def muProd {k r : ℕ} (μW μN : Measure (Mt k r)) : Measure (Mt k r) :=
  (μW.prod μN).map fun p : Mt k r × Mt k r => lmulM (Matrix.of p.1) p.2

def OneSide {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (ψ : Mat k r → ℂ) (μG μW μN νS : Measure (Mt k r))
    (Φ : Mat k r → Wp) (c : ℝ) : Prop :=
  inWb k r z ∧ 0 < Tz k r z ∧ Nontrivial Wp ∧ IsURepOn (UWset k r z) π ∧ IsIrredOn (UWset k r z) π ∧
    IsHaarOn (GG k r) μG ∧ IsHaarOn (UWset k r z) μW ∧ μW Set.univ = 1 ∧ IsHaarOn (Nset k r) μN ∧
    IsQuotMeas μG (muProd μW μN) νS ∧ (∀ n ∈ Nset k r, ‖ψ n‖ = 1) ∧ IsSPsiEquiv z ψ π Φ ∧ ContinuousOn Φ (GG k r) ∧
    0 < c ∧ l2SG νS Φ = ENNReal.ofReal (c * Module.finrank ℂ Wp)

def MomBd {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] (z : Fin (2 * r + k + 1) → ℂ) (νS : Measure (Mt k r))
    (Φ : Mat k r → Wp) (q : ℕ) (H₁ : ℝ) : Prop :=
  ∀ a : Fin (r + 1), ∫⁻ x, ENNReal.ofReal (lA k r z (Matrix.of x) a ^ (2 * q)) * (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂νS ≤
    ENNReal.ofReal (H₁ ^ (2 * q)) * l2SG νS Φ

def absBd (k r : ℕ) (H₁ De D : ℝ) : ℝ :=
  (4 * r : ℝ) ^ (44 * r ^ 3) * H₁ ^ (24 * r ^ 3) * De ^ (14 * r ^ 2) *
    (8 * Real.pi * Real.exp 1 / k) ^ (r * (k - 2 - r)) * (D ^ (k - 2 - r))⁻¹

end GlobalTheory.Amp
end
end

section

namespace GlobalTheory.ThA

open Formalism.FourierDecayAlt MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace

noncomputable section

def aT (k r : ℕ) (α : ℂ) : B.Mat k r :=
  Matrix.diagonal fun i => if i.val < r then α ^ (r - i.val)
    else if i.val ≤ r + k then 1 else ((star α) ^ (i.val - (r + k)))⁻¹

def conjF {k r : ℕ} {V : Type*} (α : ℂ) (F : B.Mat k r → V) : B.Mat k r → V :=
  fun x => F (aT k r α * x * (aT k r α)⁻¹)

def KH (k r : ℕ) : Set (B.Mat k r) :=
  UH (Hpk k r) ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _)

def IsStdOf {k r : ℕ} (L : Formalism.MainNotions.S.LocBessel k r) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (Bs : B.RealPlaceData k r L.Wp L.Wq) : Prop :=
  Bs.z = L.z ∧ Bs.z' = L.z' ∧ Bs.π = L.π ∧ Bs.π' = L.π' ∧ Bs.μW = L.μW ∧ Bs.μW' = L.μW' ∧
    Bs.μN = D.muN k r ∧ Bs.μsec = μsec

def IsRatioN (k r : ℕ) (cN : ℝ) : Prop :=
  0 < cN ∧ Formalism.MainNotions.S.haarLie (Nset k r) 1 = ENNReal.ofReal cN • D.muN k r

def lamN {k r : ℕ} (L : Formalism.MainNotions.S.LocBessel k r) (cN : ℝ) : ℝ :=
  L.κN.toReal * cN * ‖cStd / L.c‖ ^ B.kap k r

end

end GlobalTheory.ThA
end

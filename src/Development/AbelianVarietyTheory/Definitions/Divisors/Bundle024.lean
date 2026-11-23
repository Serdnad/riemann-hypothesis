module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst
public import GroundTheory.AutomorphicForms.FourierWhittaker
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open NumberField GlobalTheory.CuspRep

namespace GlobalTheory.HCF

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def CentralNilGL (χ : Module.End ℂ (Sm E a) → ℂ) (N : ℕ) (φ : Sm E a) : Prop :=
  ∀ zs : List (Module.End ℂ (Sm E a)), zs.length = N → (∀ z ∈ zs, z ∈ Zalg E a) →
    zs.foldr (fun z f => z f - χ z • f) φ = 0


variable (E a) in
def formsGL (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Kinf E a → ℂ)) (X : Set (Module.End ℂ (Sm E a) → ℂ))
    (N : ℕ) : Set (Sm E a) :=
  {φ | IsAutForm φ ∧ (∀ k ∈ L, finRep E a k φ = φ) ∧ (∀ g : GA E a, (fun k : Kinf E a => (cptRep E a k φ).1 g) ∈ W) ∧
    ∃ χ ∈ X, CentralNilGL χ N φ}

def CoreFiniteGL : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))),
    IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W →
      ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ,
        FiniteDimensional ℂ (Submodule.span ℂ (formsGL E a L W X N))

end GlobalTheory.HCF

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory
open scoped ContDiff

namespace GlobalTheory.JSW

def schur (n : ℕ) (l : Fin n → ℕ) : MvPolynomial (Fin n) ℤ :=
  Matrix.det (Matrix.of fun i j : Fin n =>
    if ((l i : ℤ) - i + j) < 0 then 0 else MvPolynomial.hsymm (Fin n) ℤ (((l i : ℤ) - i + j).toNat))

def schurAt {n : ℕ} (l : Fin n → ℕ) (α : Fin n → ℂ) : ℂ := MvPolynomial.eval₂ (Int.castRingHom ℂ) α (schur n l)

def sphW (q : ℕ) {n : ℕ} (α : Fin n → ℂ) (l : Fin n → ℕ) : ℂ :=
  if Antitone l then
    (q : ℂ) ^ (-(∑ i : Fin n, (((n : ℂ) - 1 - 2 * (i : ℕ)) * (l i : ℂ))) / 2) * schurAt l α
  else 0

theorem schur_zero (n : ℕ) : schur n (fun _ => 0) = 1 := by
  rw [schur, Matrix.det_of_upperTriangular]
  · simp
  · intro i j h
    have h' : (j : ℕ) < i := h
    rw [Matrix.of_apply, if_pos (by push_cast; omega)]

theorem sphW_of_not_antitone (q : ℕ) {n : ℕ} (α : Fin n → ℂ) {l : Fin n → ℕ} (h : ¬ Antitone l) : sphW q α l = 0 :=
  if_neg h

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

open GlobalTheory.CuspRep


omit [_root_.NumberField.IsTotallyComplex E] in
instance isAddHaarMeasure_volume_lie : Measure.IsAddHaarMeasure (volume : Measure (Lie E a)) :=
  haveI : Measure.IsAddHaarMeasure (volume : Measure (Fin a → Cinf E)) := Measure.pi.isAddHaarMeasure _
  Measure.pi.isAddHaarMeasure _

def smoothInf (f : Lie E a → ℂ) (φ : GA E a → ℂ) (g : GA E a) : ℂ := ∫ x, f x * chart φ g x

def IsTestInf (f : Lie E a → ℂ) : Prop :=
  ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ invSet E a

def smoothSpan (π : CuspSub E a) : Submodule ℂ (GA E a → ℂ) :=
  Submodule.span ℂ {F | ∃ (f : Lie E a → ℂ) (φ : Sm E a), IsTestInf f ∧ φ ∈ π.V ∧ F = smoothInf f φ.1}



omit [_root_.NumberField.IsTotallyComplex E] in
theorem exists_isTestInf {y : Lie E a} (hy : y ∈ invSet E a) {U : Set (Lie E a)} (hU : U ∈ nhds y) :
    ∃ ρ : Lie E a → ℝ, IsTestInf (fun x => (ρ x : ℂ)) ∧ tsupport ρ ⊆ U ∧ (∀ x, ρ x ∈ Set.Icc (0 : ℝ) 1) ∧ ρ y = 1 := by
  obtain ⟨f, h1, h2, h3, h4, h5⟩ := exists_contDiff_tsupport_subset (n := ⊤) (s := invSet E a ∩ U) (x := y)
    (Filter.inter_mem (isOpen_invSet.mem_nhds hy) hU)
  refine ⟨f, ⟨Complex.ofRealCLM.contDiff.comp h3, h2.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp), ?_⟩,
    h1.trans Set.inter_subset_right, fun x => h4 ⟨x, rfl⟩, h5⟩
  exact (tsupport_comp_subset (g := fun r : ℝ => (r : ℂ)) (by simp) f).trans (h1.trans Set.inter_subset_left)

theorem smoothInf_rt_fin (f : Lie E a → ℂ) (φ : GA E a → ℂ) (k : GL (Fin a) (Af E)) (g : GA E a) :
    smoothInf f (fun x => φ (x * finGL E a k)) g = smoothInf f φ (g * finGL E a k) := by
  simp only [smoothInf, chart_rt_fin]

end GlobalTheory.JSW
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
  IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum iterD defCoord polydisc)
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
open scoped Classical

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatJet

abbrev Idx (I : Type) [Fintype I] (n : ℕ) : Type := {ν : I → ℕ // ∑ i, ν i ≤ n + 1}

structure JetRing (R : Type) [CommRing R] (I : Type) [Fintype I] (n : ℕ) where

  B : Type
  [cr : CommRing B]
  [alg : Algebra R B]

  b : Module.Basis (Idx I n) R B

  one : b ⟨0, by simp⟩ = 1

  mul : ∀ ν ν' : Idx I n, b ν * b ν' =
    if h : ∑ i, (ν.1 + ν'.1) i ≤ n + 1 then (∏ i, (ν.1 i + ν'.1 i).choose (ν.1 i)) • b ⟨ν.1 + ν'.1, h⟩ else 0

  π : B →+* R

  π_eq : ∀ x, π x = b.repr x ⟨0, by simp⟩

  κ : DividedPowers (RingHom.ker π)

  nil : IsNilDP κ

attribute [instance] JetRing.cr JetRing.alg

section Alg

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R : Type} [CommRing R] {I : Type} [Fintype I] {n : ℕ}

def admitted (X : Obj F 𝔠 (Sp R)) (N : I → Module.End R (HdR X.A)) : Prop :=
  (∀ i (a : 𝓞 F), Commute (N i) (act (dp0 R) (𝟙 _) X.rm a)) ∧ (∀ i j, N i * N j = 0) ∧
    ∀ (c : 𝔠.elt) (ψ : LinearMap.BilinForm R (HdR X.A)), IsPolForm (dp0 R) (𝟙 _) X.A (X.diag c) ψ →
      (∀ i x y, ψ (N i x) y + ψ x (N i y) = 0) ∧ ∀ i j x y, ψ (N i x) (N j y) = 0

end Alg

abbrev FR (E : Type) [Field E] : Type := maximalRealSubfield E

section Cx

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {𝔠 : FracId (FR E)}

structure Unif (φ : I → E →+* ℂ) (L : Set E) (z : I → ℂ) (X : Obj (FR E) 𝔠 (Sp ℂ)) where

  e : Fin (Module.finrank ℚ (FR E)) ≃ I

  c : 𝔠.elt

  pos : IsTotPos (c : FR E)

  u : HolUnif X.A (X.diag c) (Module.finrank ℚ (FR E))

  lat : ∀ w, w ∈ u.Λ ↔ ∃ x ∈ L, w = fun j ↦ defCoord φ z x (e j)

  act : ∀ (a : 𝓞 (FR E)) w, u.ex (fun j ↦ φ (e j) ((a : FR E) : E) * w j) = u.ex w ≫ X.rm.act a

  h : I → ℝ

  ah : ∃ χ, u.IsAH (Matrix.diagonal fun j ↦ (h (e j) : ℂ)) χ

variable {φ : I → E →+* ℂ} {L : Set E} {z : I → ℂ} {X : Obj (FR E) 𝔠 (Sp ℂ)}

def Unif.IsDet (U : Unif φ L z X) (δ : X.DetOmega) (C : ℂ) : Prop :=
  ∀ (v : Fin (Module.finrank ℚ (FR E)) → X.Lie) (W : Matrix (Fin (Module.finrank ℚ (FR E))) (Fin (Module.finrank ℚ (FR E))) ℂ),
    (∀ j, U.u.IsDiff (W j) (v j).hom) → δ v = C * W.det

def Unif.IsCMVec (U : Unif φ L z X) (i : I) (y : HdR X.A) (w : ℂ) : Prop :=
  (∀ (a : E) (α : X.A ⟶ X.A) [IsMonHom α], (∀ w', U.u.ex (fun j ↦ φ (U.e j) a * w' j) = U.u.ex w' ≫ α) →
    push (dp0 ℂ) (𝟙 _) α y = φ i a • y) ∧
  ∃ v, IsLieImage y v ∧ U.u.IsDiff (Pi.single (U.e.symm i) w) v

structure CxPt (𝔠 : FracId (FR E)) (φ : I → E →+* ℂ) (L : Set E) where

  X : Obj (FR E) 𝔠 (Sp ℂ)

  U : Unif φ L 0 X

  δ : X.DetGen

  C : ℂ

  det : U.IsDet δ.1 C

  ψ : LinearMap.BilinForm ℂ (HdR X.A)

  pol : IsPolForm (dp0 ℂ) (𝟙 _) X.A (X.diag U.c) ψ

  y : I → HdR X.A

  w : I → ℂ

  s : I → ℂ

  cm : ∀ i, U.IsCMVec i (y i) (w i)

def CxPt.low (T : CxPt 𝔠 φ L) (i : I) : Module.End ℂ (HdR T.X.A) :=
  T.s i • (T.ψ.flip (T.y i)).smulRight (T.y i)

def CxPt.A (T : CxPt 𝔠 φ L) (i : I) : ℂ := Real.pi * T.U.h i * T.s i * T.w i ^ 2

def CxPt.IsOver (T : CxPt 𝔠 φ L) {R : Type} [CommRing R] (σ : R →+* ℂ)
    (X₀ : Obj (FR E) 𝔠 (Sp R)) (δ₀ : X₀.DetGen) (N : I → Module.End R (HdR X₀.A)) : Prop :=
  ∃ (p : T.X.A.left ⟶ X₀.A.left) (m : GrpMor (dp0 R) (𝟙 _) X₀.A (dp0 ℂ) (𝟙 _) T.X.A σ (spMap σ) p),
    T.X.IsPullBy X₀ (spMap σ) p ∧ Obj.DetCorr σ p δ₀.1 T.δ.1 ∧
      ∀ i x₀ x, m.Corr x₀ x → m.Corr (N i x₀) (T.low i x)

end Cx

def IsEis {F : Type} [Field F] [NumberField F] (𝔞 𝔟 : FracId F) (k : ℕ) (G : ((F →+* ℝ) → ℂ) → ℂ) : Prop :=
  (k ≠ 2 → ∀ z ∈ halfSpace F, HasSum (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 k 0 z) (G z)) ∧
    (k = 2 → ∃ H, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsContinuation 𝔞 𝔟 H ∧ G = H 0)

def EisExp : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (𝔞 𝔟 : FracId F) (s : ℕ), 1 ≤ s →
    ∃ G, IsEis 𝔞 𝔟 (2 * s) G ∧ DifferentiableOn ℂ G (halfSpace F) ∧ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.HasExpansion 𝔞 𝔟 (2 * s) G

def EisFourier : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔞 𝔟 : FracId F) (k : ℕ), 1 ≤ k → ∀ G,
    GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.HasExpansion 𝔞 𝔟 k G → ∃ (Z : ℂ → ℂ) (a : (𝔞 * 𝔟).elt → ℂ),
      GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta (ClassGroup.mk F 𝔞)⁻¹ Z ∧
      HasFourier 𝔞 𝔟 (fun z ↦ (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.cK F k : ℂ) * G z / (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) ^ k) a ∧
      a 0 = (2 : ℂ)⁻¹ ^ Module.finrank ℚ F * Z (1 - (k : ℂ)) ∧ ∀ ξ, ξ ≠ 0 → ∃ n : ℤ, a ξ = n

def ModelInt : Prop := AllLat fun E _ _ I _ d φ _ _ 𝔣 Λ l L =>
  ∀ [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (Ω : ℂ), Ω ^ 12 = latDisc Λ →
    ∃ (𝔠 : FracId (FR E)) (R : Subring ℂ) (_ : IsLocalRing R) (X₀ : Obj (FR E) 𝔠 (Sp R)) (δ₀ : X₀.DetGen)
      (N : I → Module.End R (HdR X₀.A)) (T : CxPt 𝔠 φ L) (a b : I → ℂ),
      (∀ x ∈ R, Sz l lam 0 x) ∧ (∀ q : ℚ, 0 ≤ padicValRat l q → (q : ℂ) ∈ R) ∧ admitted X₀ N ∧ T.IsOver R.subtype X₀ δ₀ N ∧
      (∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ T.A i ≠ 0 ∧ Sz l lam (a0 𝔣 l) (a i / Ω) ∧
        Sz l lam (c_vp 𝔣 l + if l = d then 1 / 2 else 0) (a i * b i * (Real.sqrt d : ℝ) / (2 * Real.pi))⁻¹ ∧
        Sz l lam (c_vp 𝔣 l) (b i / (a i * T.A i))) ∧
      Sz l lam (Fintype.card I * c_vp 𝔣 l) (T.C / ∏ i, a i)

def JetInt : Prop := AllLat fun _ _ _ I _ d φ s z 𝔣 Λ l L =>
  ∀ [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (Ω : ℂ), Ω ^ 12 = latDisc Λ →
  ∃ a b : I → ℂ, (∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ Sz l lam (a0 𝔣 l) (a i / Ω) ∧
      Sz l lam (c_vp 𝔣 l + if l = d then 1 / 2 else 0) (a i * b i * (Real.sqrt d : ℝ) / (2 * Real.pi))⁻¹) ∧
    ∀ (g : (I → ℂ) → ℂ) (κ : I → ℕ) (u : List I), IsDefSum φ (2 * s) L g → (∀ i, u.count i = κ i) →
      Sz l lam ((cE_vp l z : ℝ) + ((2 * s * Fintype.card I : ℕ) : ℝ) * c_vp 𝔣 l + ((∑ i, κ i : ℕ) : ℝ) * c_vp 𝔣 l)
        (iterD u g 0 * ∏ i, ((b i / a i) ^ κ i / a i ^ (2 * s)))

end GlobalTheory.LatJet
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix

namespace GlobalTheory.JSW

open GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def whit (F : GA E a → ℂ) (g : GA E a) : ℂ := GroundTheory.Automorphic.FourierWhittaker.whittaker F g


variable (E a) in
def NA : Set (GA E a) :=
  {u | (∀ i j : Fin a, j < i → (u : Matrix (Fin a) (Fin a) (Ad E)) i j = 0) ∧ ∀ i, (u : Matrix (Fin a) (Fin a) (Ad E)) i i = 1}

def psiN (u : GA E a) : ℂ := (GroundTheory.Global.adelicChar E (GlobalTheory.Whittaker.superDiag u) : ℂ)


variable (E a) in
def supS (S : Finset (HeightOneSpectrum (𝓞 E))) : Set (GA E a) :=
  {g | ∀ w ∉ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g = 1}


variable (E) in
def mirS (S : Finset (HeightOneSpectrum (𝓞 E))) (m : ℕ) : Set (GA E (m + 1)) :=
  supS E (m + 1) S ∩ {g | ∀ j, (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j = if j = Fin.last m then 1 else 0}

def diagPow {K : Type} [CommRing K] {n : ℕ} (ϖ : Kˣ) (l : Fin n → ℕ) : GL (Fin n) K :=
  Units.map (Matrix.diagonalRingHom (Fin n) K).toMonoidHom (MulEquiv.piUnits.symm fun i => ϖ ^ l i)

def tl (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (l : HeightOneSpectrum (𝓞 E) →₀ (Fin a → ℕ)) : GA E a :=
  (l.support.toList.map fun w => finGL E a (locGL E a w (diagPow (ϖ w) (l w)))).prod

def IsRapidInf {X : Type} [MeasurableSpace X] (ν : MeasureTheory.Measure X) (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)) : Prop :=
  Measurable k ∧ Measurable (fun x => (γ x : Matrix (Fin a) (Fin a) (Cinf E))) ∧
    ∀ N : ℕ, MeasureTheory.Integrable (fun x => ‖k x‖ * height (γ x) ^ N) ν

def mspanR [_root_.NumberField.IsTotallyComplex E] (π : CuspSub E a) : Submodule ℂ (GA E a → ℂ) :=
  sInf {S | (∀ φ ∈ π.V, φ.1 ∈ S) ∧ (∀ F ∈ S, ∀ h : GA E a, (fun g => F (g * h)) ∈ S) ∧
    ∀ F ∈ S, ∀ (X : Type) (_ : MeasurableSpace X) (ν : MeasureTheory.Measure X) (_ : MeasureTheory.SFinite ν) (k : X → ℂ)
      (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ → (fun g => ∫ x, k x * F (g * infGL E a (γ x)) ∂ν) ∈ S}

def psiLoc (w : HeightOneSpectrum (𝓞 E)) (x : w.adicCompletion E) : ℂ := (GroundTheory.Global.adelicChar E (sFin E (sLoc E w x)) : ℂ)

end GlobalTheory.JSW
end
end

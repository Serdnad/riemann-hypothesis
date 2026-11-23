module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle006
public import Mathlib.RepresentationTheory.Character
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

@[expose] public section

section

noncomputable section

namespace GlobalTheory.GLq

open Polynomial Formalism.MainNotions.ArithmeticCylinders
open scoped Classical

abbrev Gn (g n : ℕ) : Type := GL (Fin n) (ZMod g)

abbrev Mt (g n : ℕ) : Type := Matrix (Fin n) (Fin n) (ZMod g)

def IsClass {G : Type} [Group G] (χ : G → ℂ) : Prop := ∀ x y : G, χ (y * x * y⁻¹) = χ x

def IsChar {G : Type} [Group G] (χ : G → ℂ) : Prop := ∃ V : FDRep ℂ G, ∀ x, V.character x = χ x

def IsIrr {G : Type} [Group G] (χ : G → ℂ) : Prop :=
  ∃ V : FDRep ℂ G, CategoryTheory.Simple V ∧ ∀ x, V.character x = χ x

def ip {G : Type} [Group G] [Fintype G] (α β : G → ℂ) : ℂ :=
  (Fintype.card G : ℂ)⁻¹ * ∑ x, α x * β x⁻¹

def tr {G : Type} [Group G] [Fintype G] (a : MonoidAlgebra ℂ G) (χ : G → ℂ) : ℂ := ∑ x, a.coeff x * χ x

def zOf {G : Type} [Group G] [Fintype G] (χ : G → ℂ) : MonoidAlgebra ℂ G :=
  ∑ x, MonoidAlgebra.single x (χ 1 / (Fintype.card G : ℂ) * χ x⁻¹)

variable {g : ℕ} [Fact g.Prime]

def tl (a : ℕ) {n : ℕ} (M : Mt g n) : Mt g a := fun i j => entN M i j

def br (a b : ℕ) {n : ℕ} (M : Mt g n) : Mt g b := fun i j => entN M (a + i) (a + j)

def InPar (a : ℕ) {n : ℕ} (M : Mt g n) : Prop := ∀ i j : Fin n, (j : ℕ) < a → a ≤ (i : ℕ) → M i j = 0

def toG {n : ℕ} (M : Mt g n) : Gn g n := if h : IsUnit M then h.unit else 1

def hcT (a b : ℕ) (Φ : Gn g a → Gn g b → ℂ) (n : ℕ) : Gn g n → ℂ := fun x =>
  ((Finset.univ.filter fun p : Gn g n => InPar a (p : Mt g n)).card : ℂ)⁻¹ *
    ∑ y : Gn g n, if InPar a ((y⁻¹ * x * y : Gn g n) : Mt g n) then
      Φ (toG (tl a ((y⁻¹ * x * y : Gn g n) : Mt g n))) (toG (br a b ((y⁻¹ * x * y : Gn g n) : Mt g n))) else 0

def hc (a b : ℕ) (α : Gn g a → ℂ) (β : Gn g b → ℂ) (n : ℕ) : Gn g n → ℂ := hcT a b (fun x y => α x * β y) n

def res (a b : ℕ) {n : ℕ} (χ : Gn g n → ℂ) : Gn g a → Gn g b → ℂ := fun h₁ h₂ =>
  ((g : ℂ) ^ (a * b))⁻¹ * ∑ x : Gn g n,
    if InPar a (x : Mt g n) ∧ tl a (x : Mt g n) = (h₁ : Mt g a) ∧ br a b (x : Mt g n) = (h₂ : Mt g b) then χ x else 0

abbrev Pc (g : ℕ) : Type := Σ d : ℕ, Gn g d → ℂ

def degL (L : List (Pc g)) : ℕ := (L.map fun p => p.1).sum

def hcL (L : List (Pc g)) : (n : ℕ) → Gn g n → ℂ :=
  List.rec (motive := fun _ => (n : ℕ) → Gn g n → ℂ) (fun _ _ => 1)
    (fun p L ih n => hc p.1 (degL L) p.2 (ih (degL L)) n) L

theorem hcL_nil (n : ℕ) : hcL ([] : List (Pc g)) n = fun _ => 1 := rfl

theorem hcL_cons (p : Pc g) (L : List (Pc g)) (n : ℕ) :
    hcL (p :: L) n = hc p.1 (degL L) p.2 (hcL L (degL L)) n := rfl

def IsCusp {d : ℕ} (χ : Gn g d → ℂ) : Prop :=
  0 < d ∧ IsIrr χ ∧ ∀ a, 0 < a → a < d → res a (d - a) χ 1 1 = 0

def wh (ψ₀ : AddChar (ZMod g) ℂ) {n : ℕ} (χ : Gn g n → ℂ) : ℂ := tr (eU g n ψ₀) χ

def der (ψ₀ : AddChar (ZMod g) ℂ) (m : ℕ) {n : ℕ} (χ : Gn g n → ℂ) : Gn g m → ℂ := fun h =>
  wh ψ₀ (res m (n - m) χ h)

def gg (ψ₀ : AddChar (ZMod g) ℂ) (n : ℕ) : Gn g n → ℂ := fun x =>
  ((Finset.univ.filter fun u : Gn g n => IsUniUp (u : Mt g n)).card : ℂ)⁻¹ *
    ∑ y : Gn g n, if IsUniUp ((y⁻¹ * x * y : Gn g n) : Mt g n) then
      ψ₀ (∑ i ∈ Finset.range (n - 1), entN ((y⁻¹ * x * y : Gn g n) : Mt g n) i (i + 1)) else 0

def eJ' (g N : ℕ) [NeZero g] (k : ℕ) (ψ₀ : AddChar (ZMod g) ℂ) : MonoidAlgebra ℂ (GL (Fin N) (ZMod g)) :=
  eDat g N (fun M => IsUniUp M ∧ ∀ a, a < k → entN M a k = 0)
    (fun M => ∑ i ∈ Finset.range (N - 1), entN M i (i + 1)) ψ₀

structure LabelDatum (g : ℕ) [Fact g.Prime] where
  teich : Formalism.CyclotomicNorms.Fbar g →* ℂ
  teich_inj : ∀ x y, x ≠ 0 → y ≠ 0 → teich x = teich y → x = y
  gen : ℕ → Formalism.CyclotomicNorms.Fbar g
  gen_order : ∀ d, 0 < d → orderOf (gen d) = g ^ d - 1
  gen_norm : ∀ d e, 0 < d → 0 < e → gen (d * e) ^ ((g ^ (d * e) - 1) / (g ^ d - 1)) = gen d

def thetaOf (L : LabelDatum g) (d : ℕ) (x z : Formalism.CyclotomicNorms.Fbar g) : ℂ :=
  if h : ∃ n : ℕ, z = L.gen d ^ n then L.teich x ^ h.choose else 0

def IsPrimeLab (d : ℕ) (P : (ZMod g)[X]) : Prop := P.Monic ∧ Irreducible P ∧ P.coeff 0 ≠ 0 ∧ P.natDegree = d

def IsCuspOf (L : LabelDatum g) (P : (ZMod g)[X]) {d : ℕ} (χ : Gn g d → ℂ) : Prop :=
  IsPrimeLab d P ∧ IsCusp χ ∧ ∀ x ∈ Formalism.CyclotomicNorms.rootsBar P, ∀ y : Gn g d, Irreducible (y : Mt g d).charpoly →
    ∀ z ∈ Formalism.CyclotomicNorms.rootsBar (y : Mt g d).charpoly,
      χ y = (-1) ^ (d - 1) * ∑ i ∈ Finset.range d, thetaOf L d x (z ^ (g ^ i))

def HasLabel (L : LabelDatum g) {n : ℕ} (χ : Gn g n → ℂ) (f : (ZMod g)[X]) : Prop :=
  ∃ Q : List ((ZMod g)[X] × Pc g), (∀ p ∈ Q, IsCuspOf L p.1 p.2.2) ∧ degL (Q.map Prod.snd) = n ∧
    f = (Q.map Prod.fst).prod ∧ ip χ (hcL (Q.map Prod.snd) n) ≠ 0

def eSerC (L : LabelDatum g) (n : ℕ) (f : (ZMod g)[X]) : MonoidAlgebra ℂ (Gn g n) :=
  ∑ᶠ χ ∈ {χ : Gn g n → ℂ | IsIrr χ ∧ HasLabel L χ f}, zOf χ

def wtC (L : LabelDatum g) {n : ℕ} (a : MonoidAlgebra ℂ (Gn g n)) (f : (ZMod g)[X]) : ℝ :=
  ((a * eSerC L n f).coeff 1).re / (a.coeff 1).re

def Green : Prop :=
  ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (d : ℕ), 0 < d → ∃ τ : (ZMod g)[X] → Gn g d → ℂ,
    (∀ P, IsPrimeLab d P → IsCuspOf L P (τ P) ∧ τ P 1 = ∏ i ∈ Finset.Ico 1 d, ((g : ℂ) ^ i - 1)) ∧
    (∀ P P', IsPrimeLab d P → IsPrimeLab d P' → τ P = τ P' → P = P') ∧
    ∀ χ : Gn g d → ℂ, IsCusp χ → ∃ P, IsPrimeLab d P ∧ χ = τ P

def ESerTie (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ k : Fin 2, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ∃ L : LabelDatum (D.host.g k), L.teich = D.ntypes.teichC k ∧ ∀ f, D.ntypes.eSer k f = eSerC L D.R.r f

end GlobalTheory.GLq
end
end

section

noncomputable section

namespace GlobalTheory.BK

open Formalism.BasicNotions.Loc

variable {l : ℕ} [Fact l.Prime] (LL : FinExt l)

instance isUnitBall_OL : IsUnitBall ↥(OL LL) ↥LL.1 where
  inj := Subtype.val_injective
  mem_range_iff x := ⟨fun ⟨y, h⟩ => h ▸ (GlobalTheory.mem_integralClosure_padicInt_iff LL.1 y).1 y.2,
    fun h => ⟨⟨x, (GlobalTheory.mem_integralClosure_padicInt_iff LL.1 x).2 h⟩, rfl⟩⟩

instance normedAlgebra_finExt : NormedAlgebra ℚ_[l] ↥LL.1 where
  norm_smul_le c x := norm_smul_le c (x : Om l)

instance isUltrametricDist_finExt : IsUltrametricDist ↥LL.1 :=
  IsUltrametricDist.of_normedAlgebra ℚ_[l]

instance completeSpace_finExt : CompleteSpace ↥LL.1 :=
  haveI := LL.2
  FiniteDimensional.complete ℚ_[l] ↥LL.1

end GlobalTheory.BK
end
end

section

noncomputable section

namespace GlobalTheory.Cyc

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation

variable {l : ℕ} [Fact l.Prime]

def IsTheta {P : LocPrime l} (AI : LocAinf l P) (θ : Ainf l →+* OC l) : Prop :=
  (∀ (x : OCb l) (y : OC l),
    PreTilt.coeff 0 x = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) y →
      θ (WittVector.teichmuller l x) - y ∈ Ideal.span {((l : ℕ) : OC l)}) ∧
  Function.Surjective θ ∧
  (∀ (g : GQ l) (a : Ainf l), ((θ (AI.actW g a) : OC l) : PadicComplex l) =
    AI.actC g ((θ a : OC l) : PadicComplex l)) ∧
  (∀ a : Ainf l, θ a = 0 ↔ AI.ξ ∣ a) ∧
  ∀ j : ℕ, θ (WittVector.teichmuller l (AI.εroot j)) = AI.ζ j

def zC (x : ℤ_[l]) : PadicComplex l := algebraMap ℚ_[l] (PadicComplex l) (x : ℚ_[l])

def IsMat (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) {d : ℕ}
    (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l))
    (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) : Prop :=
  letI := zlMod LL T
  ∃ b : Module.Basis (Fin d) ℤ_[l] ↥T.L.T,
    (∀ (g : ↥(GK K)) (i j : Fin d), M (g : GQ l) i j = zC (b.repr (actTZ LL T g (b j)) i)) ∧
    ∀ (a : ↥(OL LL)) (i j : Fin d), A a i j = zC (b.repr (⟨_, T.L.T.smul_mem a (b j).2⟩ : ↥T.L.T) i)

def IsDec (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ) (K : FinExt l)
    (m : ℕ) {d : ℕ} (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l))
    (D : Matrix (Fin d) (Fin d) (PadicComplex l))
    (U : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (g : GQ l) : Prop :=
  IsUnit D.det ∧ (∀ a b, ‖D a b‖ ≤ 1) ∧ (∀ a b, ‖(l : PadicComplex l) * D⁻¹ a b‖ ≤ 1) ∧
    Frame χ K m U g ∧ ∀ σ ∈ Gj K m, D * U σ = M σ * D.map (act σ)

def ExpStar (LT : LocTheory) (G : Subgroup (GQ l)) (e : ℕ) (z : GQ l → ℚ_[l]) (α : Om l) : Prop :=
  CocOn G (fun σ y => (((LT l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * y) Set.univ z ∧
  ∃ b ∈ ((LT l).PD (botExt l)).Fil 0, ∀ σ ∈ G,
    algebraMap ℚ_[l] (LT l).R.BdR (z σ) -
      algebraMap ℚ_[l] (LT l).R.BdR ((logChi LT σ : ℤ_[l]) : ℚ_[l]) *
        (algebraMap (Om l) (LT l).R.BdR α * (LT l).ιB (LT l).tB ^ e) -
      (algebraMap ℚ_[l] (LT l).R.BdR (((LT l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) *
        (LT l).actQdR σ b - b) ∈ ((LT l).PD (botExt l)).Fil ((e : ℤ) + 1)

def betaE (l s e : ℕ) : ℤ :=
  if e = 0 then -1 else (s : ℤ) - 1 - e - padicValNat l (e - 1).factorial

def repQ {P : LocPrime l} (AI : LocAinf l P) (G : Subgroup (GQ l)) {T : Type} [AddCommGroup T]
    [Module ℤ_[l] T] (ρ : ↥G →* (T →ₗ[ℤ_[l]] T)) (a b : ℤ) :
    Representation ℤ_[l] ↥G (TensorProduct ℤ_[l] T (Qab (AinfSub l) (xiU AI) a b)) :=
  repX (act := AI.actWCbHom.comp G.subtype) ρ
    ⟨fun g x hx => (xiOK AI).1 (g : GQ l) x hx, (xiOK AI).2.1, fun g => (xiOK AI).2.2 (g : GQ l)⟩ a b

end GlobalTheory.Cyc
end
end

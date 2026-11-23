module

public import Formalism.HermitianCurvature.Bundle001
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.Algebra.AffineMonoid.Basic
public import Formalism.HermitianCurvature.StatementTB
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Formalism.LatticeRigidity.StatementC
public import Formalism.LatticeTheta.Statement
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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

namespace Formalism.FourierDecayAlt.S6

open NumberField NumberField.IsCMField Module MeasureTheory
open scoped nonZeroDivisors

section Defs

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

abbrev FI := FractionalIdeal (𝓞 E)⁰ E

noncomputable def deg : ℕ := finrank ℚ (maximalRealSubfield E)

noncomputable def dd : FI E := ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FI E)

def Unram : Prop :=
  differentIdeal ℤ (𝓞 E) =
    (differentIdeal ℤ (𝓞 (maximalRealSubfield E))).map
      (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))

def UnramAbove (g : ℕ) : Prop :=
  IsCoprime (differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E)) (Ideal.span {(g : 𝓞 E)})

def PrimeToDifferent (g : ℕ) : Prop :=
  IsCoprime (differentIdeal ℤ (𝓞 E)) (Ideal.span {(g : 𝓞 E)})

noncomputable def rd : ℝ := ((|discr E| : ℤ) : ℝ) ^ ((finrank ℚ E : ℝ)⁻¹)

noncomputable def idl (g : ℕ) (k ν : ℤ) : FI E :=
  dd E ^ ν * FractionalIdeal.spanSingleton _ ((g : E) ^ k)

def zsub (A : FI E) : Submodule ℤ E := (A : Submodule (𝓞 E) E).restrictScalars ℤ

noncomputable def conjZ : E →ₗ[ℤ] E :=
  (complexConj E).toAlgHom.toRingHom.toAddMonoidHom.toIntLinearMap

def ConjStable (A : FI E) : Prop := ∀ x ∈ A, complexConj E x ∈ A

noncomputable def twLat (A B : FI E) (s : ℕ) : Submodule ℤ E :=
  zsub E A ⊓ (zsub E B).comap (LinearMap.id - ((-1 : ℤ) ^ s) • conjZ E)

noncomputable def perLat (g : ℕ) (ν : ℤ) (s : ℕ) : Submodule ℤ E :=
  twLat E (idl E g 1 ν) (idl E g 2 ν) s

noncomputable def liftLat (g : ℕ) (ν : ℤ) (s : ℕ) : Submodule ℤ E :=
  twLat E (idl E g (-1) (-ν)) (idl E g 0 (-ν)) s

noncomputable def dualIdl (g : ℕ) (ν : ℤ) : FI E := idl E g (-1) (-(ν + 1))

noncomputable def liftIdl (g : ℕ) (ν : ℤ) : FI E := idl E g (-1) (-ν)

def dualLat (g : ℕ) (L : Submodule ℤ E) : Submodule ℤ E where
  carrier := {x | ∀ y ∈ L, Algebra.trace ℚ E (x * y / g) ∈ (algebraMap ℤ ℚ).range}
  zero_mem' := fun y _ => by simp
  add_mem' := fun {a b} ha hb y hy => by
    have h : (a + b) * y / g = a * y / g + b * y / g := by ring
    rw [h, map_add (f := _)]
    exact add_mem (ha y hy) (hb y hy)
  smul_mem' := fun n a ha y hy => by
    have h : (n • a) * y / g = n • (a * y / g) := by
      simp only [zsmul_eq_mul]; ring
    rw [h, map_zsmul]
    exact zsmul_mem (ha y hy) n

noncomputable def idx (L M : Submodule ℤ E) : ℕ := L.toAddSubgroup.relIndex M.toAddSubgroup

noncomputable def frameLat (L : Submodule ℤ E) (c : ℝ) :
    Submodule ℤ (mixedEmbedding.mixedSpace E) :=
  (L.map (mixedEmbedding E).toAddMonoidHom.toIntLinearMap).map
    ((c • (LinearMap.id : mixedEmbedding.mixedSpace E →ₗ[ℝ] mixedEmbedding.mixedSpace E)).restrictScalars ℤ)

def locAt (P : Ideal (𝓞 (maximalRealSubfield E))) (L : Submodule ℤ E) : Set E :=
  {t | ∃ a : 𝓞 (maximalRealSubfield E), a ∉ P ∧ algebraMap (𝓞 (maximalRealSubfield E)) E a * t ∈ L}

def nuBlock (r i s : ℤ) : ℤ := 2 * r + 3 - 2 * i - s

end Defs

section Small

def DegreeFacts : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    finrank ℚ E = 2 * deg E ∧ Fintype.card (InfinitePlace E) = deg E ∧ 0 < deg E

def PowConjStable : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (k ν : ℤ),
    ConjStable E (idl E g k ν)

def UnramRelative : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unram E →
    differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E) = ⊤ ∧ ∀ g : ℕ, UnramAbove E g

def Between : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A B : FI E) (s : ℕ),
    B ≤ A → ConjStable E B → zsub E B ≤ twLat E A B s ∧ twLat E A B s ≤ zsub E A

def IndexCore : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : FI E) (g s : ℕ),
    A ≠ 0 → ConjStable E A → 0 < g → UnramAbove E g →
    idx E (twLat E A (A * FractionalIdeal.spanSingleton _ (g : E)) s) (zsub E A) = g ^ deg E ∧
    idx E (zsub E (A * FractionalIdeal.spanSingleton _ (g : E)))
      (twLat E A (A * FractionalIdeal.spanSingleton _ (g : E)) s) = g ^ deg E

def DualSubset : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (ν : ℤ) (s : ℕ), 0 < g →
    dualLat E g (perLat E g ν s) ≤ twLat E (dualIdl E g ν) (idl E g 0 (-(ν + 1))) (s + 1)

def DualSupset : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unram E →
    ∀ (g : ℕ) (ν : ℤ) (s : ℕ), 0 < g →
      twLat E (dualIdl E g ν) (idl E g 0 (-(ν + 1))) (s + 1) ≤ dualLat E g (perLat E g ν s)

def NormIdl : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (k ν : ℤ), 0 < g →
    √(FractionalIdeal.absNorm (idl E g k ν) : ℝ) = ((g : ℝ) ^ k * rd E ^ ν) ^ deg E


open scoped Classical in
def CovolumeIndex : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : FI E) (L : Submodule ℤ E) (c : ℝ),
    B ≠ 0 → c ≠ 0 → zsub E B ≤ L → idx E (zsub E B) L ≠ 0 →
    DiscreteTopology (frameLat E L c) ∧
    Submodule.span ℝ (frameLat E L c : Set (mixedEmbedding.mixedSpace E)) = ⊤ ∧
    ZLattice.covolume (E := mixedEmbedding.mixedSpace E) (frameLat E L c) =
      |c| ^ (2 * deg E) * (FractionalIdeal.absNorm B : ℝ) * (2⁻¹ : ℝ) ^ deg E *
        √((|discr E| : ℤ) : ℝ) / (idx E (zsub E B) L : ℝ)

def IdealsMatch : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (r i s : ℤ),
    dualIdl E g (nuBlock r i s) = liftIdl E g (nuBlock r i (s - 1)) ∧
    dualIdl E g (nuBlock r i s) = idl E g (-1) (-(2 * r + 4 - 2 * i - s)) ∧
    nuBlock r i s = 2 * (r + 1) - i - (i - 1 + s)

def LocTw : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A B : FI E) (s : ℕ)
    (P : Ideal (𝓞 (maximalRealSubfield E))), P.IsPrime → ∀ t : E,
    (t ∈ locAt E P (twLat E A B s) ↔
      t ∈ locAt E P (zsub E A) ∧ t - (-1) ^ s * complexConj E t ∈ locAt E P (zsub E B))

def LocOrdinary : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (k ν : ℤ)
    (P : Ideal (𝓞 (maximalRealSubfield E))), P.IsPrime → (g : 𝓞 (maximalRealSubfield E)) ∉ P →
    locAt E P (zsub E (idl E g k ν)) = locAt E P (zsub E (idl E g 0 ν))

def IsFLattice (E : Type) [Field E] [NumberField E] [IsCMField E] (L : Submodule ℤ E) : Prop :=
  (∀ (a : 𝓞 (maximalRealSubfield E)) (t : E), t ∈ L →
    algebraMap (𝓞 (maximalRealSubfield E)) E a * t ∈ L) ∧
  ∀ t : E, ∃ n : ℕ, 0 < n ∧ (n : E) * t ∈ L

def TwIsFLattice : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A B : FI E) (s : ℕ),
    B ≠ 0 → B ≤ A → ConjStable E B → IsFLattice E (twLat E A B s)

end Small

section Text


open scoped Classical in
def LatticeFacts (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (ν : ℤ) (s : ℕ) :
    Prop :=
  zsub E (idl E g 2 ν) ≤ perLat E g ν s ∧
  perLat E g ν s ≤ zsub E (idl E g 1 ν) ∧
  idx E (perLat E g ν s) (zsub E (idl E g 1 ν)) = g ^ deg E ∧
  idx E (zsub E (idl E g 2 ν)) (perLat E g ν s) = g ^ deg E ∧
  dualLat E g (perLat E g ν s) ≤ zsub E (dualIdl E g ν) ∧
  idx E (dualLat E g (perLat E g ν s)) (zsub E (dualIdl E g ν)) = g ^ deg E ∧
  liftLat E g ν s ≤ zsub E (liftIdl E g ν) ∧
  idx E (liftLat E g ν s) (zsub E (liftIdl E g ν)) = g ^ deg E ∧
  √(FractionalIdeal.absNorm (dualIdl E g ν) : ℝ) = ((g : ℝ) * rd E ^ (ν + 1)) ^ (-(deg E : ℤ)) ∧
  DiscreteTopology (frameLat E (perLat E g ν s) (rd E ^ (-ν))) ∧
  Submodule.span ℝ
    (frameLat E (perLat E g ν s) (rd E ^ (-ν)) : Set (mixedEmbedding.mixedSpace E)) = ⊤ ∧
  ZLattice.covolume (E := mixedEmbedding.mixedSpace E) (frameLat E (perLat E g ν s) (rd E ^ (-ν))) =
    (rd E / 2) ^ deg E * (g : ℝ) ^ (3 * deg E)

def LatticesGeneral : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unram E →
    ∀ (g : ℕ) (ν : ℤ) (s : ℕ), 0 < g → LatticeFacts E g ν s

def AssembleLattices : Prop :=
  DegreeFacts → PowConjStable → UnramRelative → Between → IndexCore →
    DualSubset → DualSupset → NormIdl → CovolumeIndex → LatticesGeneral

def TypedModel : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (ν : ℤ) (s : ℕ), 0 < g →
    PrimeToDifferent E g →
    ∀ P : Ideal (𝓞 (maximalRealSubfield E)), P.IsPrime → (g : 𝓞 (maximalRealSubfield E)) ∈ P →
    ∀ (K : Type) [Field K] (o : Subring K) (σ : E →+* K),
      (∀ x : E, x ∈ locAt E P (zsub E 1) ↔ σ x ∈ o ∧ σ (complexConj E x) ∈ o) →
      ∀ t : E, (t ∈ locAt E P (perLat E g ν s) ↔
        (σ t / (g : K), (-1) ^ s * σ (complexConj E t) / (g : K)) ∈ Formalism.FourierDecayAlt.I.orderR o (g : K))

end Text

end Formalism.FourierDecayAlt.S6
end

section

namespace Formalism.FourierDecayAlt.crystallineComparison

open MeasureTheory Filter Topology Finset

noncomputable section

open Classical

abbrev V (f : ℕ) := Fin f → ℂ

def mfac (K : ℕ) (L a : ℝ) : ℝ := if a = 0 then 1 else min 1 ((L / a) ^ K)

def mL {f : ℕ} (K : ℕ) (L : Fin f → ℝ) (σ : V f) : ℝ := ∏ v, mfac K (L v) ‖σ v‖

def pat {f : ℕ} (L : Fin f → ℝ) (σ : V f) : Finset (Fin f) := univ.filter (fun v => L v < ‖σ v‖)

def psi {f : ℕ} (z : V f) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ∑ v, (z v + starRingEnd ℂ (z v)))

def dualSet {f : ℕ} (La : Submodule ℤ (V f)) : Set (V f) := {σ | ∀ z ∈ La, psi (σ * z) = 1}

def fourier {f : ℕ} (g : V f → ℝ) (σ : V f) : ℂ := ∫ z, (g z : ℂ) * psi (σ * z)

def PDOn {f : ℕ} (T : Set (V f)) (A : V f → ℂ) : Prop :=
  ∀ (S : Finset (V f)) (c : V f → ℂ), (∀ σ ∈ S, σ ∈ T) →
    0 ≤ (∑ σ ∈ S, ∑ σ' ∈ S, A (σ - σ') * c σ * starRingEnd ℂ (c σ')).re

def Bdd {α : Type} (g : α → ℂ) : Prop := ∃ B : ℝ, ∀ x, ‖g x‖ ≤ B

def IsMean {Λ : Type} [AddCommGroup Λ] (LIM : (Λ → ℂ) → ℂ) : Prop :=
  (∀ g h, Bdd g → Bdd h → LIM (g + h) = LIM g + LIM h) ∧
  (∀ (c : ℂ) g, Bdd g → LIM (c • g) = c * LIM g) ∧
  (∀ g, Bdd g → (∀ x, 0 ≤ (g x).re ∧ (g x).im = 0) → 0 ≤ (LIM g).re ∧ (LIM g).im = 0) ∧
  LIM (fun _ => 1) = 1 ∧
  (∀ g (σ : Λ), Bdd g → LIM (fun x => g (x + σ)) = LIM g)

def atInfAll (f : ℕ) : Filter (V f) :=
  ⨅ v : Fin f, Filter.comap (fun x : V f => ‖x v‖) Filter.atTop

def IsMeanInf {f : ℕ} (Λ : AddSubgroup (V f)) (LIM : (Λ → ℂ) → ℂ) : Prop :=
  IsMean LIM ∧ ∀ g : Λ → ℂ, Bdd g →
    Tendsto g (Filter.comap (fun x : Λ => (x : V f)) (atInfAll f)) (𝓝 0) → LIM g = 0

def MajIntegral : Prop :=
  ∀ (K : ℕ) (x : ℝ), 2 < K → 0 < x →
    Integrable (fun l : ℂ => mfac K x ‖l‖) ∧
      ∫ l : ℂ, mfac K x ‖l‖ = Real.pi * x ^ 2 * K / ((K : ℝ) - 2)

def MajIntegralProd : Prop :=
  ∀ (f K : ℕ) (x : Fin f → ℝ), 2 < K → (∀ v, 0 < x v) →
    Integrable (fun l : V f => mL K x l) ∧
      ∫ l : V f, mL K x l = ∏ v, (Real.pi * x v ^ 2 * K / ((K : ℝ) - 2))

def MeanBound : Prop :=
  ∀ (Λ : Type) [AddCommGroup Λ] (LIM : (Λ → ℂ) → ℂ) (g : Λ → ℂ) (B : ℝ),
    IsMean LIM → (∀ x, ‖g x‖ ≤ B) → ‖LIM g‖ ≤ B

def MeanExists : Prop :=
  ∀ (f : ℕ) (La : Submodule ℤ (V f)) [DiscreteTopology La] [IsZLattice ℝ La],
    ∃ LIM : (La.toAddSubgroup → ℂ) → ℂ, IsMeanInf La.toAddSubgroup LIM

def MeanSplit : Prop :=
  ∀ (f : ℕ) (Λ : AddSubgroup (V f)) (LIM : (Λ → ℂ) → ℂ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (a r : V f → H) (Nh : V f → ℂ) (B : ℝ),
    IsMeanInf Λ LIM → (∀ x, ‖a x‖ ≤ B ∧ ‖r x‖ ≤ B) →
    (∀ σ ∈ Λ, Tendsto (fun x => inner ℂ (a x) (a (x + σ))) (atInfAll f) (𝓝 (Nh σ))) →
    (∀ σ ∈ Λ, Tendsto (fun x => inner ℂ (a x) (r (x + σ))) (atInfAll f) (𝓝 0)) →
    (∀ σ ∈ Λ, Tendsto (fun x => inner ℂ (r x) (a (x + σ))) (atInfAll f) (𝓝 0)) →
    (∀ σ ∈ Λ, LIM (fun x : Λ => inner ℂ (a x + r x) (a ((x : V f) + σ) + r ((x : V f) + σ))) =
        Nh σ + LIM (fun x : Λ => inner ℂ (r x) (r ((x : V f) + σ)))) ∧
    PDOn (Λ : Set (V f)) (fun σ => LIM (fun x : Λ => inner ℂ (r x) (r ((x : V f) + σ))))

def LatticeHerglotzBound : Prop :=
  ∀ (f : ℕ) (La : Submodule ℤ (V f)) [DiscreteTopology La] [IsZLattice ℝ La]
    (N : V f → ℝ) (A : V f → ℂ),
    (∀ z, 0 ≤ N z) → LowerSemicontinuous N → Integrable N → PDOn (dualSet La) A →
    Summable (fun σ : dualSet La => ‖fourier N σ + A σ‖) →
    ∀ (z₀ : V f) (S : Finset (V f)), (∀ z ∈ S, z - z₀ ∈ La) →
      ZLattice.covolume La * ∑ z ∈ S, N z ≤ ∑' σ : dualSet La, ‖fourier N σ + A (σ : V f)‖

def SumForm {E W : Type} [Field E] (D : TB.Data E W) (ε : ℝ) (i s : ℕ) (w : W) (Mv : ℝ) : Prop :=
  ∃ θ : W → ℝ, TB.IsProb (D.Wb (D.cnt w + s * D.K)) θ ∧
    ∀ Y : Finset (TB.Pt E), (∀ h ∈ Y, TB.level h = i - s) → ∀ κ, TB.PSDOn Y κ →
      ∀ (t₀ : E) (S : Finset E), (∀ t ∈ S, t ≠ 0 ∧ t - t₀ ∈ D.La (i - s + 1) s) →
        ∑ t ∈ S, (D.Nst ε i s w Y κ t t).re ≤
          Mv * ∑ w' ∈ D.Wb (D.cnt w + s * D.K), θ w' * D.N0 ε (i - s) w' Y κ

def EstBlockOfSumForm : Prop :=
  ∀ (E W : Type) [Field E] (D : TB.Data E W) (C₄ : ℝ), D.GramPSD → D.WordsPos →
    (∀ ε, 0 < ε → ∀ i s, 2 ≤ s → s ≤ i → i ≤ D.r + 1 → ∀ w ∈ D.Wall,
      D.cnt w + (s + 1) * D.K ≤ D.Ntop → D.vol (i - s + 1) s ≤ 1 →
      ∃ Mv, Mv ≤ C₄ ^ (D.f * s) * (∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s') ∧ SumForm D ε i s w Mv) →
    D.EstBlock C₄

end

end Formalism.FourierDecayAlt.crystallineComparison
end

section

namespace Formalism.FourierDecayAlt.F7

open Finset Polynomial

noncomputable section

abbrev Sesq (M : Type) [AddCommGroup M] [Module ℂ M] : Type := M →ₗ[ℂ] M →ₛₗ[starRingEnd ℂ] ℂ

section Defs

variable {R M : Type} [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M] [Module R M]

end Defs

def lagCo {d : ℕ} (y : Fin (d + 1) → ℝ) (j : Fin (d + 1)) : ℝ := ∏ i ∈ univ.erase j, (y j - y i)⁻¹

def PolyStep {V : Type} [AddCommGroup V] [Module ℂ V] (K d : ℕ) (s : Fin K → ℂ)
    (W : ℕ → (Fin K → ℝ) → V) : Prop :=
  ∀ (a : Fin K) (y : Fin K → ℝ), ∃ c : Fin (d + 1) → V, c (Fin.last d) = s a • W (a : ℕ) y ∧
    ∀ t : ℝ, W ((a : ℕ) + 1) (Function.update y a t) = ∑ k : Fin (d + 1), ((t : ℂ) ^ (k : ℕ)) • c k

def ExtractK : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (K d : ℕ) (s : Fin K → ℂ)
    (W : ℕ → (Fin K → ℝ) → V) (grid : Fin K → Fin (d + 1) → ℝ),
    PolyStep K d s W → (∀ a, Function.Injective (grid a)) → ∀ y₀ : Fin K → ℝ,
    (∏ a, s a) • W 0 y₀ =
      ∑ j : Fin K → Fin (d + 1), ((∏ a, lagCo (grid a) (j a) : ℝ) : ℂ) • W K fun a => grid a (j a)

def thGrid {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (j : Fin K → Fin (d + 1)) : ℝ :=
  ∏ a, (|lagCo (grid a) (j a)| / ∑ i, |lagCo (grid a) i|)

def DualWeights : Prop :=
  ∀ (Ls : Type) [Fintype Ls] (ω N N' : Ls → ℝ), (∀ L, 0 ≤ ω L) → (∀ L, 0 ≤ N L) → (∀ L, 0 ≤ N' L) →
    0 < ∑ L, ω L →
    (∑ L, (ω L / (2 * ∑ L', ω L') + ω L / (2 * ∑ L', ω L'))) = 1 ∧
    (∑ L, ω L * √(N L * N' L)) ≤
      (∑ L, ω L) * (∑ L, (ω L / (2 * ∑ L', ω L') * N L + ω L / (2 * ∑ L', ω L') * N' L))

def ExtractCheb : Prop :=
  ∀ (V : Type) [SeminormedAddCommGroup V] [NormedSpace ℂ V] (K d : ℕ) (s : Fin K → ℂ)
    (W : ℕ → (Fin K → ℝ) → V) (α β : Fin K → ℝ),
    1 ≤ d → (∀ a, α a < β a) → PolyStep K d s W → ∀ (y₀ : Fin K → ℝ) (B : ℝ),
    (∀ j : Fin K → Fin (d + 1), ‖W K fun a => Formalism.SA.C.chebPt (α a) (β a) d (j a)‖ ≤ B) →
    (∏ a, ‖s a‖) * ‖W 0 y₀‖ ≤ (∏ a, (1 / 2) * (4 / (β a - α a)) ^ d) * B

def ChebSharp : Prop :=
  ∀ (α β : ℝ) (n : ℕ), α < β → 1 ≤ n →
    Function.Injective (Formalism.SA.C.chebPt α β n) ∧
      ∑ j, |lagCo (Formalism.SA.C.chebPt α β n) j| = (1 / 2) * (4 / (β - α)) ^ n

def ChebCoValue : Prop :=
  ∀ (α β : ℝ) (n : ℕ), α < β → 1 ≤ n → ∀ j : Fin (n + 1),
    lagCo (Formalism.SA.C.chebPt α β n) j =
      (-1) ^ (j : ℕ) * (if (j : ℕ) = 0 ∨ (j : ℕ) = n then 1 / 2 else 1) *
        ((2 : ℝ) ^ (n - 1) / n) * (2 / (β - α)) ^ n

section Poisson

open MeasureTheory Formalism.H
open scoped FourierTransform RealInnerProductSpace

def PoissonAt {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] [FiniteDimensional ℝ V] (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (φ : V → ℂ) (x : V) : Prop :=
  Summable (fun μ : dual Λ =>
      (𝓕 φ : V → ℂ) μ * Complex.exp (2 * Real.pi * Complex.I * (⟪(μ : V), x⟫ : ℝ))) ∧
  HasSum (fun l : Λ => φ ((l : V) + x))
    ((ZLattice.covolume Λ : ℂ)⁻¹ * ∑' μ : dual Λ,
      (𝓕 φ : V → ℂ) μ * Complex.exp (2 * Real.pi * Complex.I * (⟪(μ : V), x⟫ : ℝ)))

def poissonBound {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] [FiniteDimensional ℝ V] (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (φ : V → ℝ) : ℝ :=
  (ZLattice.covolume Λ)⁻¹ * (((𝓕 (fun v => (φ v : ℂ)) : V → ℂ) 0).re +
    ∑' μ : {μ : dual Λ // μ ≠ 0}, ‖(𝓕 (fun v => (φ v : ℂ)) : V → ℂ) (μ : dual Λ)‖)

def PoissonStep : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
    [FiniteDimensional ℝ V] (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (φ : V → ℝ) (x : V),
    PoissonAt Λ (fun v => (φ v : ℂ)) x → (∀ l : Λ, 0 ≤ φ ((l : V) + x)) →
    ∀ S : Finset Λ, ∑ l ∈ S, φ ((l : V) + x) ≤ poissonBound Λ φ

def LocSummable {V : Type} [NormedAddCommGroup V] (Λ : Submodule ℤ V) (φ : V → ℂ) : Prop :=
  ∀ Kc : Set V, IsCompact Kc → ∃ b : Λ → ℝ, Summable b ∧ ∀ (l : Λ), ∀ x ∈ Kc, ‖φ ((l : V) + x)‖ ≤ b l

def PoissonSummable : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
    [FiniteDimensional ℝ V] (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (φ : V → ℂ),
    Continuous φ → LocSummable Λ φ → Summable (fun μ : dual Λ => ‖(𝓕 φ : V → ℂ) μ‖) →
    ∀ x : V, PoissonAt Λ φ x

def ProductDecaySummable : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (ι : Type) [Fintype ι] (π : ι → V →L[ℝ] ℂ), (Function.Bijective fun (c : V) (v : ι) => π v c) →
    ∀ (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (φ : V → ℂ) (C : ℝ),
    (∀ c, ‖φ c‖ ≤ C * ∏ v, ((1 + ‖π v c‖) ^ 3)⁻¹) → LocSummable Λ φ

def PoissonStepText : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
    [FiniteDimensional ℝ V] (ι : Type) [Fintype ι] (π : ι → V →L[ℝ] ℂ),
    (Function.Bijective fun (c : V) (v : ι) => π v c) →
    ∀ (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (φ : V → ℝ) (C : ℝ) (x : V),
    Continuous φ → (∀ c, |φ c| ≤ C * ∏ v, ((1 + ‖π v c‖) ^ 3)⁻¹) →
    Summable (fun μ : dual Λ => ‖(𝓕 (fun v => (φ v : ℂ)) : V → ℂ) μ‖) →
    (∀ l : Λ, 0 ≤ φ ((l : V) + x)) →
    PoissonAt Λ (fun v => (φ v : ℂ)) x ∧
      ∀ S : Finset Λ, ∑ l ∈ S, φ ((l : V) + x) ≤ poissonBound Λ φ

end Poisson

structure WLetter (K : Type) where

  plus : Bool

  pt : K

  first : Bool

section Weights

variable {K : Type} [Field K]

def qW (q : K → K) : List (WLetter K) → K → K
  | [], Y => q Y
  | l :: w, Y => qW q w Y *
      (if l.plus then (Y - l.pt + 1) / (Y - l.pt) else (l.pt - Y) / (l.pt - Y - 1))

end Weights

end

end Formalism.FourierDecayAlt.F7
end

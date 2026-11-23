module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle012
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenOf
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Bundle001
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def SD.Indep (d : SD σ) (w : InfinitePlace F) (Ψ : Mx F E d.m d.n → ℂ) : Prop :=
  ∀ X Z, (∀ w', w' ≠ w → d.cw w' Z = 0) → finOne F • Z = 0 → Ψ (X + Z) = Ψ X

def AdDecomp : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ), ∀ ε w, d.IsW ε w → ∀ (e : AF F), e * e = e → ∀ x : d.G,
  e • inFrame d.b x = e • (1 : Matrix _ _ (AE F E)) →
  ∃ (x₁ x₂ x₃ x₄ : d.G) (t c b : Mx F E d.n d.n) (a a' : GL (Fin d.n) (AE F E)), x = x₁ * (w * x₂ * w⁻¹) * x₃ * x₄ ∧
    inFrame d.b x₁ = Matrix.fromBlocks 1 t 0 1 ∧ inFrame d.b x₂ = Matrix.fromBlocks 1 c 0 1 ∧
    inFrame d.b x₃ = Matrix.fromBlocks a.1 0 0 a'.1 ∧ inFrame d.b x₄ = Matrix.fromBlocks 1 b 0 1 ∧
    e • t = 0 ∧ e • c = 0 ∧ e • b = 0 ∧ e • a.1 = e • (1 : Mx F E d.n d.n) ∧ e • a'.1 = e • (1 : Mx F E d.n d.n)

def AwayAct : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (R : RD d), ∀ w (x : d.G), d.cw w (inFrame d.b x) = 1 →
  ∃ A : (Mx F E d.m d.n → ℂ) → Mx F E d.m d.n → ℂ, ∀ Ψ, d.Indep w Ψ → d.Indep w (A Ψ) ∧
    ∀ f, IsSw f → ∀ Φ ∈ d.sch, d.T Φ = R.tens w f Ψ → d.T (d.om x Φ) = R.tens w f (A Ψ)

def FinAct : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ), ∀ x : d.G, (∀ w, d.cw w (inFrame d.b x) = 1) →
  ∀ g ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F), ∃ g' ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F),
    ∀ f : Mx F E d.m d.n → ℂ, (∀ X Z, (∀ w, d.cw w Z = 0) → f (X + Z) = f X) → ∀ Φ ∈ d.sch,
      d.T Φ = (fun X => f X * g fun k => (d.crd X k).2) → d.T (d.om x Φ) = fun X => f X * g' fun k => (d.crd X k).2

end PositivityTheory.SiegelWeilFormula

end
end

section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula

def TUnit : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ), ∀ ν : Measure (Mx F E d.m d.n), ν.IsAddHaarMeasure → ∀ x, ∀ Φ ∈ d.sch, ∀ Φ' ∈ d.sch,
  ∫ X, d.T (d.om x Φ) X * star (d.T (d.om x Φ') X) ∂ν = ∫ X, d.T Φ X * star (d.T Φ' X) ∂ν

def THeis : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ), ∀ Φ ∈ d.sch, ∀ Z X : Mx F E d.m d.n,
  d.T (d.dd.rho d.B.ψ (Z * (incM F d.b.1.toCols₂)ᵀ) Φ) X = d.T Φ (X + Z) ∧
  d.T (d.dd.rho d.B.ψ (Z * (incM F d.b.1.toCols₁)ᵀ) Φ) X = d.B.ψ (d.tt (d.gram Z X)) * d.T Φ X

end PositivityTheory.SiegelWeilFormula

end
end

section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def zOf {n : ℕ} (y : GR n) : Matrix (Fin n) (Fin n) ℂ :=
  (Complex.I • (mR y).toBlocks₁₁ + (mR y).toBlocks₁₂) * (u1 (mR y))⁻¹

def IsHolW {n : ℕ} (p q : ℕ) (e : ℤ) (φ : GR n → ℂ) : Prop :=
  ∃ H : (Fin n → Fin n → ℂ) → ℂ, DifferentiableOn ℂ H {Z | ((-(Complex.I / 2)) • (Matrix.of Z - (Matrix.of Z)ᴴ)).PosDef} ∧
    ∀ y, φ y = F0 p q e y * H (if q = 0 then zOf y else -(zOf y)ᴴ)

def HolLead : Prop :=
  ∀ (m n p q : ℕ) (e : ℤ), 1 ≤ m → m < n → (p = m ∧ q = 0 ∨ p = 0 ∧ q = m) →
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] (Pp Γ : Subgroup G) (ι : GR n →* G) (s₀ : ℂ) (Ht : G → ℝ≥0) (f : G → ℂ), Continuous ι →
      (∀ g, ∃ (x : G) (y : GR n) (S : ℂ) (r : ℝ), 0 < r ∧ g = x * ι y ∧
        ∀ y' : GR n, (Ht (x * ι y') : ℝ) = r * hLoc y' ∧ f (x * ι y') = S * F0 p q e y') →
      ∀ (U : Set ℂ) (d : Polynomial ℂ) (Ê : ℂ → G → ℂ) (t : ℝ), IsOpen U → IsRightDomain U → s₀ ∈ U →
        (∀ g, DifferentiableOn ℂ (Ê · g) U) → ContinuousOn (fun y : ℂ × G => Ê y.1 y.2) (U ×ˢ Set.univ) →
        (∀ z : ℂ, t < z.re → (∀ C : Set G, IsCompact C → ∃ u : GlobalTheory.Eis.Cosets Pp Γ → ℝ, Summable u ∧ ∀ g ∈ C, ∀ c,
            ‖GlobalTheory.Eis.term Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (z - s₀) * f x) g c‖ ≤ u c) ∧
          ∀ g, Ê z g = d.eval z * GlobalTheory.Eis.cosetSum Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (z - s₀) * f x) g) →
        ∀ j : ℕ, (∀ i < j, ∀ g, iteratedDeriv i (Ê · g) s₀ = 0) →
          (∀ ψ, IsSingTest ψ → ∀ nb : (Fin n → Fin n → ℝ) → GR n, (∀ x, mR (nb x) = nU (herm x)) →
            ∀ (g : G) (a b : GR n), ∫ x, iteratedDeriv j (Ê · (g * ι (a * nb x * b))) s₀ * ψ x = 0) →
          ∀ g, IsHolW p q e fun y => iteratedDeriv j (Ê · (g * ι y)) s₀

def HolT : Prop :=
  (∀ (n p q : ℕ) (e : ℤ) (φ : GR n → ℂ), IsHolW p q e φ → ∀ β : Matrix (Fin n) (Fin n) ℂ,
    (∀ (h : Matrix (Fin n) (Fin n) ℂ) (x y : GR n), h.IsHermitian → mR x = nU h →
      φ (x * y) = Complex.exp (Complex.I * (β * h).trace) * φ y) →
    ∀ (a a' : Matrix (Fin n) (Fin n) ℂ) (x y : GR n), mR x = Matrix.fromBlocks a 0 0 a' → aᴴ * β * a = β →
      φ (x * y) = F0 p q e x * φ y) ∧
  ∀ (n p q : ℕ) (e : ℤ) (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (ι : GR n →* G), Continuous ι →
    ∀ A : G → ℂ, Continuous A → (∀ g, IsHolW p q e fun y => A (g * ι y)) →
    ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν] (c : X → G) (u : X → ℂ) (C : Set G), IsCompact C →
      (∀ x, c x ∈ C) → (∀ x, ‖u x‖ ≤ 1) → (∀ y, AEStronglyMeasurable (fun x => A (c x * ι y) * u x) ν) →
      IsHolW p q e fun y => ∫ x, A (c x * ι y) * u x ∂ν

def RD.vac {d : SD σ} (R : RD d) : Submodule ℂ (Mx F E d.m d.n → ℂ) :=
  Submodule.span ℂ {f | ∃ g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ, g ∈ SB _ ∧
    f = fun X => (∏ w, fP 1 (R.loc w X)) * g fun k => (d.crd X k).2}

structure LowerRankDatum (d : SD σ) : Type 1 where
  n : ℕ
  Y : Spc F E n
  κ : Type
  [fin : Fintype κ]
  dd : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) d.A.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) Y.J))) κ
  om : G2 σ Y →* Module.End ℂ ((κ → AF F) → ℂ)
  S : UA σ d.A.J →* Module.End ℂ ((κ → AF F) → ℂ)
  l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ
  b : GL (Fin n ⊕ Fin n) E
  K : Subgroup (G2 σ Y)
  a : G2 σ Y → ℝ
  ok : Wk (σ := σ) d.B d.A Y d.r d.s d.χ κ dd om S l b K a d.μ d.D

attribute [instance] LowerRankDatum.fin

abbrev LowerRankDatum.sd {d : SD σ} (L : LowerRankDatum d) : SD σ :=
  { B := d.B, m := d.m, n := L.n, A := d.A, Y := L.Y, r := d.r, s := d.s, χ := d.χ, κ := L.κ, dd := L.dd, om := L.om, S := L.S,
    l := L.l, b := L.b, K := L.K, a := L.a, μ := d.μ, D := d.D, bs := d.bs, ok := L.ok }

structure LD (d : SD σ) extends LowerRankDatum d where
  i₀ : Fin d.n
  em : Fin n → Fin d.n
  inj : Function.Injective em
  rng : ∀ i, i ≠ i₀ ↔ i ∈ Set.range em
  j : G2 σ Y →* d.G
  cont : Continuous j
  j_in : ∀ g, (inFrame d.b (j g)).submatrix (Sum.map em em) (Sum.map em em) = inFrame b g
  j_out : ∀ g, ∀ u ∈ ({Sum.inl i₀, Sum.inr i₀} : Set (Fin d.n ⊕ Fin d.n)), ∀ v,
    inFrame d.b (j g) u v = (1 : Matrix _ _ (AE F E)) u v ∧ inFrame d.b (j g) v u = (1 : Matrix _ _ (AE F E)) v u
  res : ∀ Φ ∈ d.sch, ∀ Φ' ∈ toLowerRankDatum.sd.sch,
    (∀ X : Mx F E d.m d.n, (∀ a, X a i₀ = 0) → toLowerRankDatum.sd.T Φ' (X.submatrix id em) = d.T Φ X) →
    ∀ g (X : Mx F E d.m d.n), (∀ a, X a i₀ = 0) → toLowerRankDatum.sd.T (om g Φ') (X.submatrix id em) = d.T (d.om (j g) Φ) X

namespace LD

variable {d : SD σ} (L : LD d)

def IsRes (Φ : d.Fn) (Φ' : L.sd.Fn) : Prop :=
  Φ' ∈ L.sd.sch ∧ ∀ X : Mx F E d.m d.n, (∀ a, X a L.i₀ = 0) → L.sd.T Φ' (X.submatrix id L.em) = d.T Φ X

def ratV : AddSubgroup (Fin L.n → AE F E) := AddSubgroup.closure (Set.range (GlobalTheory.ThK.incV F : (Fin L.n → E) → _))

def UData (uM : (Fin L.n → AE F E) → d.G) (ν : Measure (Fin L.n → AE F E)) (𝓤 : Set (Fin L.n → AE F E)) : Prop :=
  (∀ u, ∃ a', inFrame d.b (uM u) = Matrix.fromBlocks (1 + ∑ j, Matrix.single L.i₀ (L.em j) (u j)) 0 0 a') ∧
    ν.IsAddHaarMeasure ∧ IsAddFundamentalDomain L.ratV 𝓤 ν ∧ ν 𝓤 = 1

def IsSub (T : nF σ d.Y d.b) (T' : nF σ L.Y L.b) : Prop :=
  (∀ i, T.1.1 L.i₀ i = 0 ∧ T.1.1 i L.i₀ = 0) ∧ T'.1.1 = T.1.1.submatrix L.em L.em

end LD

def MainV (c : ℂ) {d : SD σ} (R : RD d) : Prop := ∀ Φ ∈ d.sch, d.T Φ ∈ R.vac → ∀ x,
  HolValueAt (fun z => d.eis (d.sec0 Φ) (s0 d.m d.n) z x) (s0 d.m d.n) (c * d.I Φ x)

def MainC (c : ℂ) (d : SD σ) : Prop := ∀ Φ, d.KFin Φ → ∀ x,
  HolValueAt (fun z => d.eis (d.sec0 Φ) (s0 d.m d.n) z x) (s0 d.m d.n) (c * d.I Φ x)

def WhitAt (c : ℂ) (d : SD σ) (Φ : d.Fn) : Prop :=
  ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → ∀ ε w, d.IsW ε w → ∀ T, IsND T → ∀ x,
    HolValueAt (fun z => ∫ β, flat d.a (d.sec0 Φ) (s0 d.m d.n) z (w * nb β * x) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam)
      (s0 d.m d.n) (c * d.orb T (d.om x Φ))

def EisWk : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ), ∀ s₁ f, IsSec d.K d.χ s₁ f → d.Eis f s₁

def WhitEq : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ), d.m = d.n → ∀ Φ, d.KFin Φ → WhitAt 2 d Φ

def WhitLow : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (R : RD d), d.m < d.n → ∀ Φ ∈ d.sch, d.T Φ ∈ R.vac → WhitAt 0 d Φ

def MainEq : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ), d.m = d.n → MainC 2 d

def LDEx : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ), 2 ≤ d.n → Nonempty (LD d)

def VacK : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (R : RD d), (∀ Φ ∈ d.sch, d.T Φ ∈ R.vac → ∀ k ∈ d.K, d.T (d.om k Φ) ∈ R.vac) ∧ R.vac ≤ R.fock ∧
  ∀ (L : LD d) (R' : RD L.sd), ∀ Φ ∈ d.sch, d.T Φ ∈ R.vac → ∃ Φ', L.IsRes Φ Φ' ∧ L.sd.T Φ' ∈ R'.vac

def IwaQ : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (L : LD d), ∀ x : d.G, ∃ (q : d.G) (g : L.sd.G) (k : d.G) (r : ℝ) (c : ℂ), k ∈ d.K ∧
  x = q * L.j g * k ∧ 0 < r ∧ (∀ g' : L.sd.G, d.a (L.j g' * x) = r * L.a (g' * g)) ∧
  ∀ Φ ∈ d.sch, ∀ g' (X : Mx F E d.m d.n), (∀ a, X a L.i₀ = 0) →
    d.T (d.om (L.j g' * q) Φ) X = c * d.T (d.om (L.j g') Φ) X

def CTSplit : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (R : RD d) (L : LD d), ∀ s₁ f, IsSec d.K d.χ s₁ f → d.Eis f s₁ → ∃ t : ℝ, ∀ z : ℂ, t < z.re →
  ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → ∀ nb' lam' 𝓖', CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖' →
  ∀ uM ν 𝓤, L.UData uM ν 𝓤 → ∀ T T', L.IsSub T T' → ∃ c₂ : d.G → ℂ,
    (∀ x, ∫ u in 𝓤, fc d.B.ψ d.b nb lam 𝓖 (d.eis f s₁ z) T (uM u * x) ∂ν =
      fc d.B.ψ L.b nb' lam' 𝓖' (GlobalTheory.Eis.cosetSum (par2 σ L.Y) (rat2 σ L.Y) fun g =>
        ((d.Ht (L.j g * x) : ℝ) : ℂ) ^ (z - s₁) * f (L.j g * x)) T' 1 + c₂ x) ∧
    ∀ w (τ : ℝ) (y : GR d.n) x, IsDil (Pi.single L.i₀ 1) τ y →
      c₂ (R.ι w y * x) = Complex.exp (τ * (d.n - 2 * z)) * c₂ x

def UEx : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (R : RD d) (L : LD d), (∃ uM ν 𝓤, L.UData uM ν 𝓤) ∧ ∀ uM ν 𝓤, L.UData uM ν 𝓤 → ∀ w (φ : d.G → ℂ), Continuous φ →
  (∀ u ∈ L.ratV, ∀ x, φ (uM u * x) = φ x) →
  (∀ u (y : GR d.n), uM u = R.ι w y → ∀ x, φ (uM u * x) = φ x) → ∀ u x, φ (uM u * x) = φ x

def FcConj : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (L : LD d), ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 →
  (∀ T, ¬ IsND T → ∃ γ ∈ rat2 σ d.Y, ∃ T₀ T', L.IsSub T₀ T' ∧ ∀ φ : d.G → ℂ, Continuous φ →
    (∀ γ' ∈ rat2 σ d.Y, ∀ g, φ (γ' * g) = φ g) → ∀ x, fc d.B.ψ d.b nb lam 𝓖 φ T x = fc d.B.ψ d.b nb lam 𝓖 φ T₀ (γ * x)) ∧
  ∀ uM ν 𝓤, L.UData uM ν 𝓤 → ∀ T T', L.IsSub T T' → ∀ φ : d.G → ℂ, Continuous φ →
    (∀ γ' ∈ rat2 σ d.Y, ∀ g, φ (γ' * g) = φ g) → ∀ u ∈ L.ratV, ∀ x,
      fc d.B.ψ d.b nb lam 𝓖 φ T (uM u * x) = fc d.B.ψ d.b nb lam 𝓖 φ T x

def OrbRes : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ), (d.m < d.n → ∀ T, IsND T → ∀ Φ, d.orb T Φ = 0) ∧
  ∀ (L : LD d) T T', L.IsSub T T' → ∀ Φ Φ', L.IsRes Φ Φ' → d.orb T Φ = L.sd.orb T' Φ'

def Step : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (R : RD d) (L : LD d), ∀ R' : RD L.sd, d.m < d.n → MainV 2 R' → MainV 2 R

def StepOf : Prop :=
  HolLead → HolT → TAll → ThetaCoef → AuxiliaryPrimeFunction → CoefEx → FockMem → LiftEx → LocOpEx → LocInst → GSplit → PolyKFin → SecK → EisWk →
    LamBd → LamSing → FourierZero → Unfold → WhitLow → VacK → IwaQ → CTSplit → UEx → FcConj → OrbRes → Step

def VacAll : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (R : RD d), ∀ c : ℂ, MainV c R → MainC c d

def MainLe : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ), d.m ≤ d.n → MainC 2 d

def MainLeOf : Prop := RDEx → LDEx → VacK → PolyKFin → MainEq → Step → VacAll → MainLe

def FieldOf : Prop := EisBL → SecK → SWStdLt → MainLe → SiegelWeilStd

end PositivityTheory.SiegelWeilFormula

end
end

section

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Gen

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw Filter
open scoped TensorProduct Matrix Classical Topology

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


variable (E) in
def eSp (v : HeightOneSpectrum (𝓞 F)) : ℂ := if IsField (Fv F v ⊗[F] E) then -1 else 1

structure Dat0 (σ : E →ₐ[F] E) {M n d : ℕ} (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E)
    (bs : Module.Basis (Fin d) F E) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι] (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ)
    (ε : ι → Fin M → Bool) (fr : ι → GL (Fin M) ℂ) (g : ι → GL (Fin n) ℂ) (P : ι → PX M n)
    (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fv F v ⊗[F] E))
    (L₁ L₂ : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (Fin n → Fv F v ⊗[F] E))
    (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ)
    (μ : Measure (Fin n → Fin M → AF F ⊗[F] E)) (ν : Measure (HermR (AF F) σ n)) : Prop where
  cm : IsCMExt F E σ
  herm : IsHermND σ J
  hT : ∀ a b, σ (T b a) = T a b
  det : T.det ≠ 0
  chr : IsCharAF F ψ
  places : IsPlaces σ ψ θ l
  frames : IsFrames J θ ε fr
  haar : ∀ v, (lam v).IsAddHaarMeasure
  co : ∀ v, IsCO (L₁ v) ∧ IsCO (L₂ v)
  std : ∀ᶠ v in cofinite, (L₁ v : Set (Fin n → Fv F v ⊗[F] E)) = latO bs v ∧ (L₂ v : Set (Fin n → Fv F v ⊗[F] E)) = latO bs v
  pure : IsPureFin bs Φf Φv
  prod : IsProdInfFin Φ (phiInf θ l fr g P) Φf
  sdW : SdW F E σ M J (AF F) ψ n μ
  sdH : SdHerm F E σ (AF F) ψ n ν

def LocFinX : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ,
  ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
  ∀ (v : HeightOneSpectrum (𝓞 F)) (μv : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (νv : Measure (HermR (Fv F v) σ n))
    (lam : Measure (Fin n → Fv F v ⊗[F] E)) (L₁ L₂ : AddSubgroup (Fin n → Fv F v ⊗[F] E)),
    SdW F E σ M J (Fv F v) (psiV F ψ v) n μv → SdHerm F E σ (Fv F v) (psiV F ψ v) n νv → lam.IsAddHaarMeasure →
    IsCO L₁ → IsCO L₂ →
  ∀ (Φv : (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ), IsSB Φv →
  ∀ g : HermR (Fv F v) σ n → ℂ,
    IsContDensityOn μv (gramR (Fv F v) σ J) Subtype.val νv
      {S | IsUnit (S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)).det} Φv g →
  ∀ T : HermR (Fv F v) σ n, IsUnit (T : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)).det →
    ∃ W : ℂ → ℂ, Differentiable ℂ W ∧ W (((M : ℂ) - n) / 2) = g T ∧ ∃ t : ℝ, ∀ z : ℂ, t < z.re →
      Integrable (whI (Fv F v) σ J (psiV F ψ v) μv Φv (nu2 lam L₁ L₂) T.1 z) νv ∧
      W z = ∫ b, whI (Fv F v) σ J (psiV F ψ v) μv Φv (nu2 lam L₁ L₂) T.1 z b ∂νv

def UnrWhitX : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ,
  ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 →
  ∀ (d : ℕ) (bs : Module.Basis (Fin d) F E) (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∃ t : ℝ,
  ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
    ∀ (μv : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (νv : Measure (HermR (Fv F v) σ n))
      (lam : Measure (Fin n → Fv F v ⊗[F] E)) (L : AddSubgroup (Fin n → Fv F v ⊗[F] E)),
      SdW F E σ M J (Fv F v) (psiV F ψ v) n μv → SdHerm F E σ (Fv F v) (psiV F ψ v) n νv → lam.IsAddHaarMeasure →
      (L : Set (Fin n → Fv F v ⊗[F] E)) = latO bs v → ∀ z : ℂ, t < z.re →
        Integrable (whI (Fv F v) σ J (psiV F ψ v) μv ((latV bs v).indicator 1) (nu2 lam L L) (hermOf (Fv F v) σ T hT).1 z) νv ∧
        ∫ b, whI (Fv F v) σ J (psiV F ψ v) μv ((latV bs v).indicator 1) (nu2 lam L L) (hermOf (Fv F v) σ T hT).1 z b ∂νv =
          ∏ i : Fin n, (1 - eSp E v ^ (M + (i : ℕ)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(2 * z + n - (i : ℕ))))

def RealWhitEq : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, n ≤ M →
  ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (ι : Type) [Fintype ι] (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ),
    IsPlaces σ ψ θ l → ∀ ε fr, IsFrames J θ ε fr → ∀ (g : ι → GL (Fin n) ℂ) (P : ι → PX M n)
    (μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ n)),
    SdW F E σ M J (Ainf F) (psiInf F ψ) n μ → SdHerm F E σ (Ainf F) (psiInf F ψ) n ν →
    IsSchwartzInf (phiInf θ l fr g P) ∧
  ∀ gi : HermR (Ainf F) σ n → ℂ,
    IsContDensityOn μ (gramR (Ainf F) σ J) Subtype.val ν
      {S | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det} (phiInf θ l fr g P) gi →
  ∀ T : HermR (Ainf F) σ n, IsUnit (T : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det →
    ∃ W : ℂ → ℂ, Differentiable ℂ W ∧ W (((M : ℂ) - n) / 2) = gi T ∧ ∃ t : ℝ, ∀ z : ℂ, t < z.re →
      Integrable (whI (Ainf F) σ J (psiInf F ψ) μ (phiInf θ l fr g P) (nuInf θ g) T.1 z) ν ∧
      W z = ∫ b, whI (Ainf F) σ J (psiInf F ψ) μ (phiInf θ l fr g P) (nuInf θ g) T.1 z b ∂ν

def FactorX : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M n d : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E) (bs : Module.Basis (Fin d) F E) ψ (ι : Type) [Fintype ι]
    θ l ε fr g P lam L₁ L₂ Φ Φf Φv μ ν, Dat0 (ι := ι) σ J T bs ψ θ l ε fr g P lam L₁ L₂ Φ Φf Φv μ ν →
    ∀ μi νi (μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E))
      (νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (HermR (Fv F v) σ n)),
      SdW F E σ M J (Ainf F) (psiInf F ψ) n μi → SdHerm F E σ (Ainf F) (psiInf F ψ) n νi →
      (∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) n (μv v)) → (∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) n (νv v)) →
    ∀ z : ℂ, Integrable (whI (AF F) σ J ψ μ Φ (nuA θ g lam L₁ L₂) (T.map (inclR (AF F))) z) ν →
      Integrable (whI (Ainf F) σ J (psiInf F ψ) μi (phiInf θ l fr g P) (nuInf θ g) (T.map (inclR (Ainf F))) z) νi →
      (∀ v, Integrable (whI (Fv F v) σ J (psiV F ψ v) (μv v) (Φv v) (nu2 (lam v) (L₁ v) (L₂ v)) (T.map (inclR (Fv F v))) z)
        (νv v)) →
      Tendsto (fun s : Finset (HeightOneSpectrum (𝓞 F)) =>
          (∫ b, whI (Ainf F) σ J (psiInf F ψ) μi (phiInf θ l fr g P) (nuInf θ g) (T.map (inclR (Ainf F))) z b ∂νi) *
          ∏ v ∈ s, ∫ b, whI (Fv F v) σ J (psiV F ψ v) (μv v) (Φv v) (nu2 (lam v) (L₁ v) (L₂ v)) (T.map (inclR (Fv F v))) z b
            ∂(νv v))
        atTop (nhds (∫ b, whI (AF F) σ J ψ μ Φ (nuA θ g lam L₁ L₂) (T.map (inclR (AF F))) z b ∂ν))

def WROrd : Prop :=
  ∀ (m n : ℕ), m < n → ∀ (b : Bool) (c t : ℝ), 0 < c → (t = c ∨ t = -c) → ∀ β : WR.E n, (herm β).det ≠ 0 →
    ∃ W : ℂ → ℂ, Differentiable ℂ W ∧ ∃ σ₀ : ℝ, ∀ z : ℂ, σ₀ < z.re →
      Integrable (fun y => ((WR.dP y : ℝ) : ℂ) ^ (-z) * secN (fun _ : Fin m => b) c t 1 (herm y) * WR.chr t β y) ∧
      z ^ (n - m) * W z = ∫ y, ((WR.dP y : ℝ) : ℂ) ^ (-z) * secN (fun _ : Fin m => b) c t 1 (herm y) * WR.chr t β y

def RealLow : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, M < n →
  ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (ι : Type) [Fintype ι] (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ),
    IsPlaces σ ψ θ l → ∀ (e : ι → Bool) fr, IsFrames J θ (fun i _ => e i) fr → ∀ (g : ι → GL (Fin n) ℂ)
    (μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ n)),
    SdW F E σ M J (Ainf F) (psiInf F ψ) n μ → SdHerm F E σ (Ainf F) (psiInf F ψ) n ν →
  ∀ T : HermR (Ainf F) σ n, IsUnit (T : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det →
    ∃ W : ℂ → ℂ, Differentiable ℂ W ∧ ∃ t : ℝ, ∀ z : ℂ, t < z.re →
      Integrable (whI (Ainf F) σ J (psiInf F ψ) μ (phiInf θ l fr g fun _ => 1) (nuInf θ g) T.1 z) ν ∧
      (z - ((M : ℂ) - n) / 2) ^ (Module.finrank ℚ F * (n - M)) * W z =
        ∫ b, whI (Ainf F) σ J (psiInf F ψ) μ (phiInf θ l fr g fun _ => 1) (nuInf θ g) T.1 z b ∂ν

def LOrd : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (j : ℤ), ∃ Z : ℂ → ℂ, MeromorphicOn Z Set.univ ∧
    (∀ s : ℂ, 1 < s.re → HasProd (fun v : {v // v ∉ S} => 1 - eSp E v.1 ^ j * (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s)) (Z s)) ∧
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H j ∧ ∀ᶠ s in 𝓝[≠] (j : ℂ), H s =
      (s - j) ^ (if 1 ≤ j then 0 else if j = 0 then S.card + Module.finrank ℚ F - 1 else Module.finrank ℚ F) * Z s

def DensEq : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (M : ℕ), 1 ≤ M → ∀ (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → (∀ x : Fin M → E, hE σ J x x = 0 → x = 0) →
  ∀ (T : Matrix (Fin M) (Fin M) E) (hT : ∀ a b, σ (T b a) = T a b),
    T.det ≠ 0 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E)
    (Φ : (Fin M → Fin M → AF F ⊗[F] E) → ℂ) (Φinf : (Fin M → Fin M → Ainf F ⊗[F] E) → ℂ)
    (Φf : (Fin M → Fin M → Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin M → Fin M → Fv F v ⊗[F] E) → ℂ),
    IsSchwartzInf Φinf → IsPureFin b Φf Φv → IsProdInfFin Φ Φinf Φf →
    AllSome (IsHaarH F E σ M J) fun μ => AllSome (IsFDH F E σ M J μ) fun 𝓕 =>
    AllSome (HeckeCharacterZeroLocus.SiegelWeilU.IsCharAF F) fun ψ =>
    AllSome (SdW F E σ M J (Ainf F) (psiInf F ψ) M) fun μinf =>
    AllSome (SdHerm F E σ (Ainf F) (psiInf F ψ) M) fun νinf =>
    AllSome (fun μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin M → Fin M → Fv F v ⊗[F] E) =>
      ∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) M (μv v)) fun μv =>
    AllSome (fun νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (HermR (Fv F v) σ M) =>
      ∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) M (νv v)) fun νv =>
    ∃ (ginf : HermR (Ainf F) σ M → ℂ) (gv : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ M → ℂ),
      IsContDensityOn μinf (gramR (Ainf F) σ J) Subtype.val νinf
        {S | IsUnit (S : Matrix (Fin M) (Fin M) (Ainf F ⊗[F] E)).det} Φinf ginf ∧
      (∀ v, IsContDensityOn (μv v) (gramR (Fv F v) σ J) Subtype.val (νv v)
        {S | IsUnit (S : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)).det} (Φv v) (gv v)) ∧
      Multipliable (fun v => gv v (hermOf (Fv F v) σ T hT) / (1 - eSp E v / (Ideal.absNorm v.asIdeal : ℂ))) ∧
      ∀ lam : ℂ, Tendsto (fun s : ℝ => ∏' v : HeightOneSpectrum (𝓞 F), (1 - eSp E v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s : ℂ))))
          (𝓝[>] 1) (𝓝 lam) →
        2 * meanC μ 𝓕 (thetaS F E σ M J Φ {X | gramE σ J X = T}) = ginf (hermOf (Ainf F) σ T hT) * lam *
          ∏' v, gv v (hermOf (Fv F v) σ T hT) / (1 - eSp E v / (Ideal.absNorm v.asIdeal : ℂ))

def WhitGenX (ok : ℕ → ℕ → Prop) (vac : Prop) (c : ℂ) : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M n d : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E) (bs : Module.Basis (Fin d) F E) ψ (ι : Type) [Fintype ι]
    θ l ε fr g P lam L₁ L₂ Φ Φf Φv μ ν, Dat0 (ι := ι) σ J T bs ψ θ l ε fr g P lam L₁ L₂ Φ Φf Φv μ ν → ok M n →
    (n + 2 ≤ M ∨ ∀ x : Fin M → E, hE σ J x x = 0 → x = 0) →
    (vac → (∀ i, P i = 1) ∧ ∃ e : ι → Bool, ε = fun i _ => e i) →
    (∃ t : ℝ, ∀ z : ℂ, t < z.re → Integrable (whI (AF F) σ J ψ μ Φ (nuA θ g lam L₁ L₂) (T.map (inclR (AF F))) z) ν) →
    ∀ μH 𝓕, IsHaarH F E σ M J μH → IsFDH F E σ M J μH 𝓕 →
      HolValueAt (fun z => ∫ b, whI (AF F) σ J ψ μ Φ (nuA θ g lam L₁ L₂) (T.map (inclR (AF F))) z b ∂ν) (((M : ℂ) - n) / 2)
        (c * meanC μH 𝓕 (thetaS F E σ M J Φ {X | gramE σ J X = T}))

def WhitGenLt : Prop := WhitGenX (fun M n => n < M) False 1

def WhitGenEq : Prop := WhitGenX (fun M n => M = n ∧ 1 ≤ M) False 2

def WhitGenLow : Prop := WhitGenX (fun M n => M < n ∧ 1 ≤ M) True 0

def WhitGenEqOf : Prop := LocFinX → UnrWhitX → RealWhitEq → FactorX → LOrd → DensEq → WhitGenEq

def WhitGenLowOf : Prop := LocFinX → UnrWhitX → RealLow → FactorX → LOrd → WhitGenLow

end PositivityTheory.SiegelWeilFormula.Gen

end
end

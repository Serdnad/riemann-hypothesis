module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.Bundle001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.Bundle001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle020
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle006
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.VaceigenDual
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.VaceigenAlg
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def RD_k.vac {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : Submodule ℂ (Mx F E d.m d.n → ℂ) :=
  Submodule.span ℂ {f | ∃ g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ, g ∈ SB _ ∧
    f = fun X => (∏ w, fP 1 (R.loc w X)) * g fun k => (d.crd X k).2}
structure LiftedSchrodingerDatum (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : Type 1 where
  n : ℕ
  Y : Spc F E n
  κ : Type
  [fin : Fintype κ]
  dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F d.A.J) (dbl (incM F Y.J))) κ
  om : G2 σ Y →* Module.End ℂ ((κ → AF F) → ℂ)
  S : UA σ d.A.J →* Module.End ℂ ((κ → AF F) → ℂ)
  l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ
  b : GL (Fin n ⊕ Fin n) E
  K : Subgroup (G2 σ Y)
  a : G2 σ Y → ℝ
  ok : _root_.PositivityTheory.SiegelWeilFormula.Wk_k (σ := σ) d.B d.A Y d.r d.s d.χ κ dd om S l b K a d.μ d.D
attribute [instance] _root_.PositivityTheory.SiegelWeilFormula.LiftedSchrodingerDatum.fin
abbrev LiftedSchrodingerDatum.sd {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LiftedSchrodingerDatum d) : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ :=
  { B := d.B, m := d.m, n := L.n, A := d.A, Y := L.Y, r := d.r, s := d.s, χ := d.χ, κ := L.κ, dd := L.dd, om := L.om, S := L.S,
    l := L.l, b := L.b, K := L.K, a := L.a, μ := d.μ, D := d.D, bs := d.bs, ok := L.ok }
structure LD_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) extends _root_.PositivityTheory.SiegelWeilFormula.LiftedSchrodingerDatum d where
  i₀ : Fin d.n
  em : Fin n → Fin d.n
  inj : Function.Injective em
  rng : ∀ i, i ≠ i₀ ↔ i ∈ Set.range em
  j : G2 σ Y →* d.G
  cont : Continuous j
  j_in : ∀ g, (inFrame d.b (j g)).submatrix (Sum.map em em) (Sum.map em em) = inFrame b g
  j_out : ∀ g, ∀ u ∈ ({Sum.inl i₀, Sum.inr i₀} : Set (Fin d.n ⊕ Fin d.n)), ∀ v,
    inFrame d.b (j g) u v = (1 : Matrix _ _ (AE F E)) u v ∧ inFrame d.b (j g) v u = (1 : Matrix _ _ (AE F E)) v u
  res : ∀ Φ ∈ d.sch, ∀ Φ' ∈ toLiftedSchrodingerDatum.sd.sch,
    (∀ X : Mx F E d.m d.n, (∀ a, X a i₀ = 0) → toLiftedSchrodingerDatum.sd.T Φ' (X.submatrix id em) = d.T Φ X) →
    ∀ g (X : Mx F E d.m d.n), (∀ a, X a i₀ = 0) → toLiftedSchrodingerDatum.sd.T (om g Φ') (X.submatrix id em) = d.T (d.om (j g) Φ) X
namespace LD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
def _root_.PositivityTheory.SiegelWeilFormula.LD_k.IsRes (Φ : d.Fn) (Φ' : L.sd.Fn) : Prop :=
  Φ' ∈ L.sd.sch ∧ ∀ X : Mx F E d.m d.n, (∀ a, X a L.i₀ = 0) → L.sd.T Φ' (X.submatrix id L.em) = d.T Φ X
def _root_.PositivityTheory.SiegelWeilFormula.LD_k.ratV : AddSubgroup (Fin L.n → AE F E) := AddSubgroup.closure (Set.range (GlobalTheory.ThK.incV F : (Fin L.n → E) → _))
def _root_.PositivityTheory.SiegelWeilFormula.LD_k.UData (uM : (Fin L.n → AE F E) → d.G) (ν : Measure (Fin L.n → AE F E)) (𝓤 : Set (Fin L.n → AE F E)) : Prop :=
  (∀ u, ∃ a', inFrame d.b (uM u) = Matrix.fromBlocks (1 + ∑ j, Matrix.single L.i₀ (L.em j) (u j)) 0 0 a') ∧
    ν.IsAddHaarMeasure ∧ IsAddFundamentalDomain L.ratV 𝓤 ν ∧ ν 𝓤 = 1
def _root_.PositivityTheory.SiegelWeilFormula.LD_k.IsSub (T : nF σ d.Y d.b) (T' : nF σ L.Y L.b) : Prop :=
  (∀ i, T.1.1 L.i₀ i = 0 ∧ T.1.1 i L.i₀ = 0) ∧ T'.1.1 = T.1.1.submatrix L.em L.em
end LD
def MainV_k (c : ℂ) {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : Prop := ∀ Φ ∈ d.sch, d.T Φ ∈ R.vac → ∀ x,
  HolValueAt (fun z => d.eis (d.sec0 Φ) (s0 d.m d.n) z x) (s0 d.m d.n) (c * d.I Φ x)
def MainC_k (c : ℂ) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : Prop := ∀ Φ, d.KFin Φ → ∀ x,
  HolValueAt (fun z => d.eis (d.sec0 Φ) (s0 d.m d.n) z x) (s0 d.m d.n) (c * d.I Φ x)
def WhitAt_k (c : ℂ) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Φ : d.Fn) : Prop :=
  ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → ∀ ε w, d.IsW ε w → ∀ T, IsND T → ∀ x,
    HolValueAt (fun z => ∫ β, flat d.a (d.sec0 Φ) (s0 d.m d.n) z (w * nb β * x) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam)
      (s0 d.m d.n) (c * d.orb T (d.om x Φ))
def EisWk_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∀ s₁ f, IsSec d.K d.χ s₁ f → d.Eis f s₁
def WhitEq_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), d.m = d.n → ∀ Φ, d.KFin Φ → _root_.PositivityTheory.SiegelWeilFormula.WhitAt_k 2 d Φ
def WhitLow_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), d.m < d.n → ∀ Φ ∈ d.sch, d.T Φ ∈ R.vac → _root_.PositivityTheory.SiegelWeilFormula.WhitAt_k 0 d Φ
def MainEq_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), d.m = d.n → _root_.PositivityTheory.SiegelWeilFormula.MainC_k 2 d
def LDEx_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), 2 ≤ d.n → Nonempty (_root_.PositivityTheory.SiegelWeilFormula.LD_k d)
def VacK_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), (∀ Φ ∈ d.sch, d.T Φ ∈ R.vac → ∀ k ∈ d.K, d.T (d.om k Φ) ∈ R.vac) ∧ R.vac ≤ R.fock ∧
  ∀ (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (R' : _root_.PositivityTheory.SiegelWeilFormula.RD_k L.sd), ∀ Φ ∈ d.sch, d.T Φ ∈ R.vac → ∃ Φ', L.IsRes Φ Φ' ∧ L.sd.T Φ' ∈ R'.vac
def IwaQ_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d), ∀ x : d.G, ∃ (q : d.G) (g : L.sd.G) (k : d.G) (r : ℝ) (c : ℂ), k ∈ d.K ∧
  x = q * L.j g * k ∧ 0 < r ∧ (∀ g' : L.sd.G, d.a (L.j g' * x) = r * L.a (g' * g)) ∧
  ∀ Φ ∈ d.sch, ∀ g' (X : Mx F E d.m d.n), (∀ a, X a L.i₀ = 0) →
    d.T (d.om (L.j g' * q) Φ) X = c * d.T (d.om (L.j g') Φ) X
def CTSplit_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d), ∀ s₁ f, IsSec d.K d.χ s₁ f → d.Eis f s₁ → ∃ t : ℝ, ∀ z : ℂ, t < z.re →
  ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → ∀ nb' lam' 𝓖', CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖' →
  ∀ uM ν 𝓤, L.UData uM ν 𝓤 → ∀ T T', L.IsSub T T' → ∃ c₂ : d.G → ℂ,
    (∀ x, ∫ u in 𝓤, fc d.B.ψ d.b nb lam 𝓖 (d.eis f s₁ z) T (uM u * x) ∂ν =
      fc d.B.ψ L.b nb' lam' 𝓖' (GlobalTheory.Eis.cosetSum (par2 σ L.Y) (rat2 σ L.Y) fun g =>
        ((d.Ht (L.j g * x) : ℝ) : ℂ) ^ (z - s₁) * f (L.j g * x)) T' 1 + c₂ x) ∧
    ∀ w (τ : ℝ) (y : GR d.n) x, IsDil (Pi.single L.i₀ 1) τ y →
      c₂ (R.ι w y * x) = Complex.exp (τ * (d.n - 2 * z)) * c₂ x
def UEx_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d), (∃ uM ν 𝓤, L.UData uM ν 𝓤) ∧ ∀ uM ν 𝓤, L.UData uM ν 𝓤 → ∀ w (φ : d.G → ℂ), Continuous φ →
  (∀ u ∈ L.ratV, ∀ x, φ (uM u * x) = φ x) →
  (∀ u (y : GR d.n), uM u = R.ι w y → ∀ x, φ (uM u * x) = φ x) → ∀ u x, φ (uM u * x) = φ x
def FcConj_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d), ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 →
  (∀ T, ¬ IsND T → ∃ γ ∈ rat2 σ d.Y, ∃ T₀ T', L.IsSub T₀ T' ∧ ∀ φ : d.G → ℂ, Continuous φ →
    (∀ γ' ∈ rat2 σ d.Y, ∀ g, φ (γ' * g) = φ g) → ∀ x, fc d.B.ψ d.b nb lam 𝓖 φ T x = fc d.B.ψ d.b nb lam 𝓖 φ T₀ (γ * x)) ∧
  ∀ uM ν 𝓤, L.UData uM ν 𝓤 → ∀ T T', L.IsSub T T' → ∀ φ : d.G → ℂ, Continuous φ →
    (∀ γ' ∈ rat2 σ d.Y, ∀ g, φ (γ' * g) = φ g) → ∀ u ∈ L.ratV, ∀ x,
      fc d.B.ψ d.b nb lam 𝓖 φ T (uM u * x) = fc d.B.ψ d.b nb lam 𝓖 φ T x
def OrbRes_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), (d.m < d.n → ∀ T, IsND T → ∀ Φ, d.orb T Φ = 0) ∧
  ∀ (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) T T', L.IsSub T T' → ∀ Φ Φ', L.IsRes Φ Φ' → d.orb T Φ = L.sd.orb T' Φ'
def Step_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d), ∀ R' : _root_.PositivityTheory.SiegelWeilFormula.RD_k L.sd, d.m < d.n → _root_.PositivityTheory.SiegelWeilFormula.MainV_k 2 R' → _root_.PositivityTheory.SiegelWeilFormula.MainV_k 2 R
def StepOf_k : Prop :=
  HolLead → HolT → _root_.PositivityTheory.SiegelWeilFormula.TAll_k → _root_.PositivityTheory.SiegelWeilFormula.ThetaCoef_k → _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties → _root_.PositivityTheory.SiegelWeilFormula.CoefEx_k → _root_.PositivityTheory.SiegelWeilFormula.FockMem_k → _root_.PositivityTheory.SiegelWeilFormula.LiftEx_k → _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k → _root_.PositivityTheory.SiegelWeilFormula.LocInst_k → _root_.PositivityTheory.SiegelWeilFormula.GSplit_k → _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k → _root_.PositivityTheory.SiegelWeilFormula.SecK_k → _root_.PositivityTheory.SiegelWeilFormula.EisWk_k →
    _root_.PositivityTheory.SiegelWeilFormula.LamBd_k → _root_.PositivityTheory.SiegelWeilFormula.LamSing_k → _root_.PositivityTheory.SiegelWeilFormula.FourierZero_k → _root_.PositivityTheory.SiegelWeilFormula.Unfold_k → _root_.PositivityTheory.SiegelWeilFormula.WhitLow_k → _root_.PositivityTheory.SiegelWeilFormula.VacK_k → _root_.PositivityTheory.SiegelWeilFormula.IwaQ_k → _root_.PositivityTheory.SiegelWeilFormula.CTSplit_k → _root_.PositivityTheory.SiegelWeilFormula.UEx_k → _root_.PositivityTheory.SiegelWeilFormula.FcConj_k → _root_.PositivityTheory.SiegelWeilFormula.OrbRes_k → _root_.PositivityTheory.SiegelWeilFormula.Step_k
def VacAll_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), ∀ c : ℂ, _root_.PositivityTheory.SiegelWeilFormula.MainV_k c R → _root_.PositivityTheory.SiegelWeilFormula.MainC_k c d
def MainLe_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), d.m ≤ d.n → _root_.PositivityTheory.SiegelWeilFormula.MainC_k 2 d
def MainLeOf_k : Prop := _root_.PositivityTheory.SiegelWeilFormula.RDEx_k → _root_.PositivityTheory.SiegelWeilFormula.LDEx_k → _root_.PositivityTheory.SiegelWeilFormula.VacK_k → _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k → _root_.PositivityTheory.SiegelWeilFormula.MainEq_k → _root_.PositivityTheory.SiegelWeilFormula.Step_k → _root_.PositivityTheory.SiegelWeilFormula.VacAll_k → _root_.PositivityTheory.SiegelWeilFormula.MainLe_k
def FieldOf_k : Prop := _root_.GlobalTheory.ThK.Dbl.EisBL_k → _root_.PositivityTheory.SiegelWeilFormula.SecK_k → _root_.PositivityTheory.SiegelWeilFormula.SWStdLt_k → _root_.PositivityTheory.SiegelWeilFormula.MainLe_k → _root_.GlobalTheory.ThK.Dbl.SiegelWeilStd_k
end PositivityTheory.SiegelWeilFormula
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def IsPureBy_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (Φ : d.Fn) (P : InfinitePlace F → PX d.m d.n)
    (gf : ∀ v : HeightOneSpectrum (𝓞 F), (Fin d.m × Fin d.n × Fin 2 → v.adicCompletion F) → ℂ) : Prop :=
  (∀ v, IsLocallyConstant (gf v) ∧ HasCompactSupport (gf v)) ∧
    (∀ᶠ v in cofinite, gf v = Set.indicator {c | ∀ k, c k ∈ v.adicCompletionIntegers F} 1) ∧
    d.T Φ = fun X => (∏ w, fP (P w) (R.loc w X)) * ∏ᶠ v, gf v (fun k => HeckeCharacterZeroLocus.SiegelWeilU.evalV F v (d.crd X k).2)
def Jd_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (η : E) : Matrix (Fin d.m) (Fin d.m) E := (η • d.A.J)ᵀ
structure Rel_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (x : d.G) (t u : GL (Fin d.n) (AE F E)) (T : nF σ d.Y d.b) (η : E)
    (T₀ : Matrix (Fin d.n) (Fin d.n) E) (hOf : nA σ d.Y d.b → HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n)
    (θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ)) (fr : InfinitePlace F → GL (Fin d.m) ℂ)
    (g : InfinitePlace F → GL (Fin d.n) ℂ) : Prop where
  levi : inFrame d.b x = Matrix.fromBlocks t.1 0 0 u.1
  rat : T.1.1 = incM F T₀
  ne : η ≠ 0
  herm : ∀ i j, σ (η * d.A.J j i) = η * d.A.J i j
  hof : ∀ β, β.1 = -(incM F (Matrix.scalar (Fin d.n) η) * ((hOf β).1 : Mx F E d.n d.n)ᵀ)
  th : ∀ w y, θ w (Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.fstA F) (AlgHom.id F E) y) = star (piInf (d.B.emb w) y)
  frc : ∀ w, (fr w).1 = ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • (R.fr w).1.map star
  gc : ∀ w, (g w).1 * ((d.cw w u.1)ᵀ).map star = ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • 1
def RelEx_k : Prop := _root_.PositivityTheory.SiegelWeilFormula.TAll_k → _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), ∀ Φ, d.KFin Φ → ∀ P gf, _root_.PositivityTheory.SiegelWeilFormula.KWhit.IsPureBy_k R Φ P gf →
  ∀ x t u, inFrame d.b x = Matrix.fromBlocks t.1 0 0 u.1 → ∀ T : nF σ d.Y d.b, IsND T →
  ∃ (η : E) (T₀ : Matrix (Fin d.n) (Fin d.n) E) (hOf : nA σ d.Y d.b → HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n)
    (θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ)) (fr : InfinitePlace F → GL (Fin d.m) ℂ)
    (g : InfinitePlace F → GL (Fin d.n) ℂ) (l : InfinitePlace F → ℝ) (εs : InfinitePlace F → Fin d.m → Bool)
    (Φg : (Fin d.n → Fin d.m → AF F ⊗[F] E) → ℂ) (Φf : (Fin d.n → Fin d.m → HeckeCharacterZeroLocus.SiegelWeilU.Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin d.n → Fin d.m → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) → ℂ)
    (μ : Measure (Fin d.n → Fin d.m → AF F ⊗[F] E)) (ν : Measure (HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n)),
    _root_.PositivityTheory.SiegelWeilFormula.KWhit.Rel_k d R x t u T η T₀ hOf θ fr g ∧ (∀ Y, Φg Y = d.T Φ (toMx Y * ((u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ)) ∧
    (∀ y : Fin d.m → E, HeckeCharacterZeroLocus.SiegelWeilU.hE σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) y y = 0 → y = 0) ∧ (∃ e : InfinitePlace F → Bool, εs = fun i _ => e i) ∧
    HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ ∧ HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) ∧ (∀ a b, σ (Td η T₀ b a) = Td η T₀ a b) ∧
    (Td η T₀).det ≠ 0 ∧ HeckeCharacterZeroLocus.SiegelWeilU.IsCharAF F d.B.ψ ∧ Gen.IsPlaces σ d.B.ψ θ l ∧ Gen.IsFrames (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) θ εs fr ∧
    HeckeCharacterZeroLocus.SiegelWeilU.IsPureFin d.bs Φf Φv ∧ HeckeCharacterZeroLocus.SiegelWeilU.IsProdInfFin Φg (Gen.phiInf θ l fr g P) Φf ∧
    HeckeCharacterZeroLocus.SiegelWeilU.SdW F E σ d.m (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) (AF F) d.B.ψ d.n μ ∧
    HeckeCharacterZeroLocus.SiegelWeilU.SdHerm F E σ (AF F) d.B.ψ d.n ν
def HeightDict_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) x t u T η T₀ hOf θ fr g, _root_.PositivityTheory.SiegelWeilFormula.KWhit.Rel_k d R x t u T η T₀ hOf θ fr g →
  ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → ∀ ε w, d.IsW ε w →
  ∃ (lv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin d.n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E))
    (L₁ L₂ : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (Fin d.n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) (C : ℝ), 0 < C ∧
    (∀ v, (lv v).IsAddHaarMeasure) ∧ (∀ v, Gen.IsCO (L₁ v) ∧ Gen.IsCO (L₂ v)) ∧
    (∀ᶠ v in cofinite, (L₁ v : Set (Fin d.n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) = PositivityTheory.PfSWUS.Loc.latO d.bs v ∧
      (L₂ v : Set (Fin d.n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) = PositivityTheory.PfSWUS.Loc.latO d.bs v) ∧
    ∀ β, 0 < Gen.nuA θ g lv L₁ L₂ (hOf β).1 ∧ d.a (w * nb β * x) = C * (Gen.nuA θ g lv L₁ L₂ (hOf β).1)⁻¹
def MeasDict_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) x t u T η T₀ hOf θ fr g, _root_.PositivityTheory.SiegelWeilFormula.KWhit.Rel_k d R x t u T η T₀ hOf θ fr g →
  (∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → ∀ ν,
    HeckeCharacterZeroLocus.SiegelWeilU.SdHerm F E σ (AF F) d.B.ψ d.n ν → MeasurableEmbedding hOf ∧ MeasurePreserving hOf lam ν) ∧
  ∀ μ νc, HeckeCharacterZeroLocus.SiegelWeilU.SdW F E σ d.m (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) (AF F) d.B.ψ d.n μ → d.IsCov νc →
    MeasurableEmbedding (toMx (F := F) (E := E) (m := d.m) (n := d.n)) ∧ MeasurePreserving toMx μ νc
def ThetaDict_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (η : E), η ≠ 0 → (∀ i j, σ (η * d.A.J j i) = η * d.A.J i j) →
  ∃ μH 𝓕, HeckeCharacterZeroLocus.SiegelWeilU.IsHaarH F E σ d.m (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) μH ∧ HeckeCharacterZeroLocus.SiegelWeilU.IsFDH F E σ d.m (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) μH 𝓕 ∧
    ∀ (T : nF σ d.Y d.b) T₀, T.1.1 = incM F T₀ → ∀ Φ ∈ d.sch,
      d.orb T Φ = HeckeCharacterZeroLocus.SiegelWeilU.meanC μH 𝓕 (HeckeCharacterZeroLocus.SiegelWeilU.thetaS F E σ d.m (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) (fun Y => d.T Φ (toMx Y))
        {X | HeckeCharacterZeroLocus.SiegelWeilU.gramE σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) X = Td η T₀})
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
end

section



section
noncomputable section
namespace PositivityTheory.ThK.Vac
open scoped Matrix TensorProduct nonZeroDivisors
open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.LatVac
open GlobalTheory.StdDual (codiff codiff_ne_zero)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
theorem mem_latW_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {W : Spc F E d} {r s : ℕ} (hW : W.IsSkew σ B r s) (v : Pl F)
    {w : Fin d → AE F E} (hw : At (evFin F v) w)
    (h : ∀ y ∈ W.L, ∀ a ∈ v.adicCompletionIntegers F, B.ψ (liftV v a * trF σ W.J y w) = 1) : w ∈ latW W v := by
  have hσ := sigma_sigma hB.cm
  have hfull : Submodule.span E (W.L : Set (Fin d → E)) = ⊤ := by
    let T := Submodule.span E (W.L : Set (Fin d → E))
    change T = ⊤
    by_contra hT
    let g : (Fin d → E) →ₗ[E] Module.Dual E T :=
      ((dotProductBilin E E).compl₂ (Matrix.mulVecLin W.Jᵀ)).domRestrict₂ T
    have hdim : Module.finrank E (Module.Dual E T) < Module.finrank E (Fin d → E) := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt hT
    obtain ⟨z, hz, hz₀⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
    let y : Fin d → E := fun i => σ (z i)
    have hy₀ : y ≠ 0 := by
      intro hy
      apply hz₀
      exact funext fun i => σ.injective ((congrFun hy i).trans (map_zero σ).symm)
    have horth (x : Fin d → E) (hx : x ∈ W.L) : form σ W.J y x = 0 := by
      have hz' : z ⬝ᵥ W.Jᵀ *ᵥ x = 0 :=
        congrArg (fun f : Module.Dual E T => f ⟨x, Submodule.subset_span hx⟩)
          (LinearMap.mem_ker.mp hz)
      rw [Matrix.dotProduct_transpose_mulVec] at hz'
      have hz'' : form σ W.J x y = 0 := by
        simpa only [form, y, sigma_sigma hB.cm] using hz'
      have hs : σ (form σ W.J y x) = (-1 : E) * form σ W.J x y := by

        simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hW.skew, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      rw [hz'', mul_zero] at hs
      exact (map_eq_zero σ).1 hs
    have hline (a : E) : a • y ∈ W.L := (hW.dual _).2 fun x hx => by
      have he : form σ W.J (a • y) x = 0 := by
        change (a • y) ⬝ᵥ W.J *ᵥ (fun i => σ (x i)) = 0
        rw [smul_dotProduct, smul_eq_mul, show y ⬝ᵥ W.J *ᵥ (fun i => σ (x i)) = 0 from horth x hx, mul_zero]
      simp only [he, mul_zero, map_zero]
      exact fun _ => isIntegral_zero
    let i : E →ₗ[𝓞 E] W.L :=
      ((LinearMap.toSpanSingleton E _ y).restrictScalars (𝓞 E)).codRestrict W.L hline
    let : Module.Finite (𝓞 E) W.L := Module.Finite.iff_fg.mpr hW.lat.fg
    let : Module.Finite (𝓞 E) E := Module.Finite.of_injective i fun a b hab =>
      smul_left_injective E hy₀ (congrArg Subtype.val hab)
    exact RingOfIntegers.not_isField E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))
  have : Module.Finite (𝓞 F) (𝓞 E) := Module.Finite.of_restrictScalars_finite ℤ _ _
  obtain ⟨m, g, f, hg, hf, hid⟩ := dual_family (𝓞 F) F (W.L.restrictScalars (𝓞 F)) (hW.lat.fg.restrictScalars) (by
    rw [eq_top_iff]
    intro x _
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (Algebra.algebraMapSubmonoid (𝓞 E) ℤ⁰) E
      (W.L : Set (Fin d → E)) x (hfull ▸ Submodule.mem_top)
    obtain ⟨_, k, hk, rfl⟩ := t
    rw [Submodule.span_eq] at ht
    have hk0 : (k : F) ≠ 0 := Int.cast_ne_zero.2 (nonZeroDivisors.ne_zero hk)
    have ht' : (k : F) • x ∈ W.L := by
      rw [Int.cast_smul_eq_zsmul, ← algebraMap_smul (𝓞 E) k x]; exact ht
    rw [← inv_smul_smul₀ hk0 x]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ht'))
  choose u hu using fun i => exists_tr_rep hσ (skew_det hW) (f i)
  have hdec : ∀ z : Fin d → AE F E, z = ∑ i, trF σ W.J (u i) z • incV (g i) := fun z => by
    have hz := span_incV z
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, rfl⟩ := hz
      simp only [trF_incV, ← hu]
      ext j
      conv_lhs => rw [hid x]

      simp only [incV, Finset.sum_apply, Pi.smul_apply, map_sum, algebraMap_smul]
      exact Finset.sum_congr rfl fun i _ =>
        map_smul (Algebra.TensorProduct.includeRight : E →ₐ[F] AF F ⊗[F] E) _ _
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add (f := _), add_smul, Finset.sum_add_distrib, ← hx, ← hy]
    | smul a x _ hx => simp only [map_smul, smul_eq_mul, mul_smul, ← Finset.smul_sum, ← hx]
  rw [hdec w]
  refine sum_mem fun i _ => AddSubgroup.subset_closure ⟨_, fun a ha => ?_, ?_, g i, hg i, rfl⟩
  · rw [← map_smul, hw a ha, map_zero]
  · refine mem_int_of_psi hB.std v _ fun t ht a ha => ?_
    have hm : algebraMap F E t • u i ∈ W.L := (hW.dual _).2 fun x hx o => by
      let o' : 𝓞 E := ⟨σ o, (RingOfIntegers.isIntegral_coe o).map (σ.restrictScalars ℤ)⟩
      obtain ⟨c, hc⟩ := hf i _ (W.L.smul_mem o' hx)
      have e : (o : E) * form σ W.J (algebraMap F E t • u i) x = t • form σ W.J (u i) (o' • x) := by
        rw [form_eq, form_eq, Algebra.smul_def t, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        have : (o' • x) l = σ o * x l := rfl
        rw [this, map_mul, hσ, Matrix.smul_vecMul, Pi.smul_apply, smul_eq_mul]
        ring
      rw [e, ← Algebra.trace_trace (S := F), map_smul, ← hu, ← hc, smul_eq_mul]
      obtain ⟨k, hk⟩ := (FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 F)⁰ F))).1 ht _
        ((FractionalIdeal.mem_one_iff _).2 ⟨c, rfl⟩)
      rw [Algebra.traceForm_apply] at hk
      rw [← hk]
      exact isIntegral_algebraMap
    have := h _ hm a ha
    rwa [trF_smul, liftV_mul, map_mul (evFin F v), AlgHom.commutes] at this
theorem mem_latAtV_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {X : Spc F E n} {W : Spc F E d} {r s r' s' : ℕ} (hX : X.IsHerm σ B r s)
    (hW : W.IsSkew σ B r' s') (v : Pl F) {z : Matrix (Fin n) (Fin d) (AE F E)} (hz : At (evFin F v) z)
    (h : ∀ γ ∈ latAtV X W v, B.ψ (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) γ z) = 1) : z ∈ latAtV X W v := by
  have hσ := sigma_sigma hB.cm
  have hfull : Submodule.span E (X.L : Set (Fin n → E)) = ⊤ := by
    let T := Submodule.span E (X.L : Set (Fin n → E))
    change T = ⊤
    by_contra hT
    let g : (Fin n → E) →ₗ[E] Module.Dual E T :=
      ((dotProductBilin E E).compl₂ (Matrix.mulVecLin X.Jᵀ)).domRestrict₂ T
    have hdim : Module.finrank E (Module.Dual E T) < Module.finrank E (Fin n → E) := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt hT
    obtain ⟨z, hz, hz₀⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
    let y : Fin n → E := fun i => σ (z i)
    have hy₀ : y ≠ 0 := by
      intro hy
      apply hz₀
      exact funext fun i => σ.injective ((congrFun hy i).trans (map_zero σ).symm)
    have horth (x : Fin n → E) (hx : x ∈ X.L) : form σ X.J y x = 0 := by
      have hz' : z ⬝ᵥ X.Jᵀ *ᵥ x = 0 :=
        congrArg (fun f : Module.Dual E T => f ⟨x, Submodule.subset_span hx⟩)
          (LinearMap.mem_ker.mp hz)
      rw [Matrix.dotProduct_transpose_mulVec] at hz'
      have hz'' : form σ X.J x y = 0 := by
        simpa only [form, y, sigma_sigma hB.cm] using hz'
      have hs : σ (form σ X.J y x) = (1 : E) * form σ X.J x y := by

        simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hX.herm, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      rw [hz'', mul_zero] at hs
      exact (map_eq_zero σ).1 hs
    have hline (a : E) : a • y ∈ X.L := (hX.dual _).2 fun x hx => by
      have he : form σ X.J (a • y) x = 0 := by
        change (a • y) ⬝ᵥ X.J *ᵥ (fun i => σ (x i)) = 0
        rw [smul_dotProduct, smul_eq_mul, show y ⬝ᵥ X.J *ᵥ (fun i => σ (x i)) = 0 from horth x hx, mul_zero]
      rw [he]
      exact isIntegral_zero
    let i : E →ₗ[𝓞 E] X.L :=
      ((LinearMap.toSpanSingleton E _ y).restrictScalars (𝓞 E)).codRestrict X.L hline
    let : Module.Finite (𝓞 E) X.L := Module.Finite.iff_fg.mpr hX.lat.fg
    let : Module.Finite (𝓞 E) E := Module.Finite.of_injective i fun a b hab =>
      smul_left_injective E hy₀ (congrArg Subtype.val hab)
    exact RingOfIntegers.not_isField E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))
  obtain ⟨m, g, f, hg, hf, hid⟩ := dual_family (𝓞 E) E X.L hX.lat.fg hfull
  let a : Fin m → Fin n → E := fun i k => f i (Pi.single k 1)
  let u : Fin m → Fin n → E := fun i => (fun k => σ (a i k)) ᵥ* X.J⁻¹
  have hu : ∀ i, u i ᵥ* X.J = fun k => σ (a i k) := fun i => by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (herm_det hX), Matrix.vecMul_one]
  have huL : ∀ i, u i ∈ X.L := fun i => (hX.dual _).2 fun x hx => by
    obtain ⟨c, hc⟩ := hf i x hx
    have e : form σ X.J (u i) x = σ (f i x) := by

      rw [form_eq, hu, LinearMap.pi_apply_eq_sum_univ (f i) x, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_eq_mul, map_mul, mul_comm]
      have : (fun j => if k = j then (1 : E) else 0) = Pi.single k 1 := funext fun j => by
        rw [Pi.single_apply]; exact if_congr eq_comm rfl rfl
      rw [this]
    rw [e, ← hc]
    exact (RingOfIntegers.isIntegral_coe c).map (σ.restrictScalars ℤ)
  have hdec : z = ∑ i, Matrix.vecMulVec (incV (g i)) (incV (a i) ᵥ* z) := by
    ext p l
    have e : ∀ k, ∑ i, incV (F := F) (g i) p * incV (a i) k = (1 : Matrix (Fin n) (Fin n) (AE F E)) p k := fun k => by
      have := congrFun (hid (Pi.single k 1)) p
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this

      simp only [incV, ← map_mul, ← map_sum, mul_comm (g _ p), a, ← this, Pi.single_apply, Matrix.one_apply]
      split_ifs <;> simp
    simp only [Matrix.sum_apply, Matrix.vecMulVec_apply, Matrix.vecMul, dotProduct, Finset.mul_sum, ← mul_assoc]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, e]
    exact (congrFun (congrFun (Matrix.one_mul z) p) l).symm
  rw [hdec]
  refine sum_mem fun i _ => vecMulVec_mem (hg i) (_root_.PositivityTheory.ThK.Vac.mem_latW_k hB hW v (fun c hc => ?_) fun y hy c hc => ?_)
  · rw [← Matrix.vecMul_smul, hz c hc, Matrix.vecMul_zero]
  · have := h _ (neg_mem (AddSubgroup.subset_closure ⟨liftV v c, at_liftV v c, by rwa [evFin_liftV], u i, huL i, y, hy, rfl⟩))
    rw [GlobalTheory.LatVacArith.symp_neg_left, ← one_smul (AF F) z, symp_smul_smul, symp_vecMulVec hσ, hu] at this
    simpa only [hσ, mul_one, mul_neg, neg_neg] using this
end PositivityTheory.ThK.Vac
end
end
end

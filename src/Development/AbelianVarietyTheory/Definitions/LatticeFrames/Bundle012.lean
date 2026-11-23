module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
public import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle007
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle001
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle011
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso

@[expose] public section

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk
open scoped TensorProduct Classical

namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen
variable {D : D7}

def realPt (θ : InfFam D) {m n : ℕ} (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) : Mx D m n :=
  Classical.epsilon fun w : Mx D m n => w.map (finPart D) = 0 ∧ ∀ τ, compAt θ τ w = z τ

variable (θ : InfFam D) (S T : HSp D) {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ)

def xiN (f : WO S T → ℂ) (z : VCx D.what₂.Tau a b) : ℂ :=
  Complex.exp ((Real.pi : ℂ) / 2 * HV sc z z) *
    f (realPt θ fun τ => Matrix.of fun i j => -(δ⁻¹ * z τ (Fin.cast hT i) (Fin.cast hS j)))

def toHom (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : (Fin a → D.host.E) →ₗ[D.host.E] (Fin b → D.host.E) :=
  Matrix.toLin' (γ.reindex (finCongr hT) (finCongr hS))

def jetP (s : ℂ) (G : VCx D.what₂.Tau a b → ℂ) (P : MvPolynomial (FVar D T.rank S.rank) ℂ) : ℂ :=
  ∑ k ∈ P.support, P.coeff k * jetC (fun _ => s) G (k.mapDomain fun v => (v.1, Fin.cast hT v.2.1, Fin.cast hS v.2.2))

def latFr (V : HSp D) {n : ℕ} (hn : V.rank = n) (N : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin V.rank → D.host.E) :=
  {x | (fun i => x (Fin.cast hn.symm i)) ∈ N}

def Moves (V : HSp D) {n : ℕ} (hn : V.rank = n) (g : GA D V) (N : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Prop :=
  ∀ x : Fin n → D.host.E, x ∈ N ↔ ∀ i, (finM V hn g⁻¹ *ᵥ fun j => eToEAf D (x j)) i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E

structure StdPair (ψ : AddChar (AF D.host.F) ℂ) : Prop where
  std : IsStdChar D ψ (-1)
  inf : IsInfFam θ
  gS : S.gram = 1
  gT : T.gram = 1
  sigS : S.SigOK
  sigT : T.SigOK
  rk : 0 < S.rank ∧ S.rank < T.rank ∧ Even S.rank ∧ Even T.rank
  cc : D.host.ccK = ⊤
  ne : δ ≠ 0
  xi : ∀ τ, tauE D τ D.host.xi0 = Complex.I * ((Real.sqrt D.host.d)⁻¹ : ℝ)
  scale : sc * ‖δ‖ ^ 2 = 2 * (Real.sqrt D.host.d)⁻¹

def IsHol (ψ : AddChar (AF D.host.F) ℂ) (f : WO S T → ℂ) : Prop :=
  IsThetaFunO ψ S T f ∧ ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 1) f

def splitPart (V : HSp D) : Subgroup (GA D V) := Subgroup.closure {g | ∃ e, IsSplitIdem D e ∧ SuppAt e V g}

def IsRatFin (V : HSp D) (g : GA D V) : Prop := g ∈ GfC V ∧ ∃ γ ∈ GQ V, finHom V γ = finHom V g

end Gen

section World
variable {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {Ch : ℕ → Type}
  (A : ColDat I l Z u Ch) (θ : InfFam (I.rec7 l Z)) (i : ℕ) (hi : i + 1 ≤ B.R.m)

abbrev ColDat.xiS (f : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ) : VCx (I.rec7 l Z).what₂.Tau (B.R.N i) (B.R.N (i + 1)) → ℂ :=
  xiN θ _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) I.A.δ I.A.sc f

end World

end GlobalTheory.AdForm
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unf.Model

variable {D : D7}

open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule

variable {ρ : ℕ} {B : BesLev D ρ} {L' : HSp D} {ζ' : Fin L'.rank → D.host.E} (l : Link B L' ζ')

include l in
theorem tau_gram (h : IsLineVec L' ζ') :
    l.τᴴ * (B.L.gram * l.τ) = (D.host.xi0 * star D.host.xi0) • L'.gram := by
  have : Unique (Fin L'.rank) := by rw [h.1]; infer_instance
  have hn := l.norm
  have hm : B.ζ = -(l.τ *ᵥ ζ') := by rw [l.map, neg_neg]
  have h0 := h.2
  rw [hm, star_neg, Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg, Matrix.star_mulVec, ← dotProduct_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc] at hn
  refine Matrix.ext fun i j => ?_
  obtain rfl := Subsingleton.elim i default
  obtain rfl := Subsingleton.elim j default
  generalize l.τᴴ * (B.L.gram * l.τ) = M at hn ⊢
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_unique, Pi.star_apply] at hn h0
  have hz : ζ' default ≠ 0 := fun e => h0 (by rw [e]; simp)
  have hz' : star (ζ' default) ≠ 0 := star_ne_zero.2 hz
  rw [Matrix.smul_apply, smul_eq_mul]
  apply mul_right_cancel₀ hz
  apply mul_left_cancel₀ hz'
  rw [hn]; ring


end GlobalTheory.Unf.Model

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unf.StCheck

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}


theorem link_simil {σ : ℕ} {B : BesLev D σ} {L' : HSp D} {ζ' : Fin L'.rank → D.host.E} (h : IsLineVec L' ζ')
    (l : Link B L' ζ') : l.τᴴ * (B.L.gram * l.τ) = (D.host.xi0 * star D.host.xi0) • L'.gram := by
  have e : star ζ' ⬝ᵥ (l.τᴴ * (B.L.gram * l.τ)) *ᵥ ζ' =
      star ζ' ⬝ᵥ ((D.host.xi0 * star D.host.xi0) • L'.gram) *ᵥ ζ' := by
    rw [← Matrix.mulVec_mulVec, dotProduct_mulVec, ← Matrix.star_mulVec, ← Matrix.mulVec_mulVec, l.map, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul, ← l.norm, star_neg, Matrix.mulVec_neg, neg_dotProduct_neg]
  have hu : Unique (Fin L'.rank) := by rw [h.1]; infer_instance
  have h2 := h.2
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_unique] at e h2
  funext i j
  rw [Subsingleton.elim i default, Subsingleton.elim j default]
  have a : star ζ' default ≠ 0 := left_ne_zero_of_mul h2
  have b : ζ' default ≠ 0 := right_ne_zero_of_mul (right_ne_zero_of_mul h2)
  have c := mul_left_cancel₀ a e
  have c' := mul_right_cancel₀ b c
  exact c'

end GlobalTheory.Unf.StCheck

end
end

section

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.Core.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Dense

variable {V W : HSp D} {S S' : D.what₂.Tau → SPar}


open Classical in
def SepCont (M : DSModel V S) (Λ : SmT M →ₗ[ℂ] ℂ) : Prop :=
  ∀ τ (v : M.Vec), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧
    ∀ w : M.sm τ, ℓ w = Λ (PiTensorProduct.tprod ℂ (Function.update v τ w))

def KVecP (M : DSModel V S) (v : M.Vec) : Prop := ∀ τ, IsKFin (M.ε τ) (M.σ τ) (v τ : M.H τ)

def ItSpans (M : DSModel V S) (M' : DSModel W S') (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M) : Prop :=
  ∀ v : M.Vec, KVecP M v → PiTensorProduct.tprod ℂ v ∈
    Submodule.span ℂ {x | ∃ (P : PolF D W.rank V.rank) (y : M'.Vec), KVecP M' y ∧ x = It P (PiTensorProduct.tprod ℂ y)}

end Dense

def PropTo {I : Type} (f τ : I → ℂ) : Prop := ∃ a : ℂ, ∀ i, f i = a * τ i

def DenseExt (D : D7) : Prop :=
  ∀ (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (S : D.what₂.Tau → SPar) (M : DSModel B.V S)
    (J : Set (GA D B.V)) (χ : GA D B.V → ℂ) (t : GA D B.V) (I : Type) (τ : I → ℂ) (φ : I → GA D B.A → ℂ)
    (T : I → SmT M →ₗ[ℂ] (GA D B.V → ℂ)), IsInfFam θ → IsStdChar D ψ (-1) → (∀ i, IsContAut B.A (φ i)) →
    (∀ i, T i ∈ MultT θ M J χ) →
    (∀ v : M.Vec, KVecP M v → PropTo (fun i => B.per ψ (φ i) (rTrans t (T i (PiTensorProduct.tprod ℂ v)))) τ) →
    ∀ x : SmT M, PropTo (fun i => B.per ψ (φ i) (rTrans t (T i x))) τ

def TowerSpans (W : Tower D) : Prop :=
  (∀ k, k + 1 < D.R.m → ItSpans (W.MY k) (W.MY (k + 1)) (W.ItY k)) ∧ ItSpans (W.MY (D.R.m - 1)) W.MX W.ItX

section Model

variable (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)

def IdE : Prop := ∀ x : X.B.I.E, HEq (X.ιE x) x

def rowJ : Set (GA D (D.sp.Y 0)) := iotaX X h ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}

def rowChi (k : GA D (D.sp.Y 0)) : ℂ := star (X.chi2 (iotaX X h k).2)

def Matches (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) : Prop :=
  t ∈ GfC (D.sp.Y 0) ∧ ConjLevel t⁻¹ J χ (rowJ X h) (rowChi X h)

def evS (t : GA D (D.sp.Y 0)) (F : GA D (D.sp.Y 0) → ℂ) : X.B.I.GA → ℂ := fun x => F ((iotaX X h).symm x * t)

def ConjVec (θ : InfFam D) {S : D.what₂.Tau → SPar} (M : DSModel (D.sp.Y 0) S) (v₀ : M.Vec) : Prop :=
  ∃ c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ),
    (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ (M.rep τ g w) =
      X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) ∧
    ∀ τ, c τ (v₀ τ : M.H τ) = X.B.w (X.pl.symm τ)

def RealSplit (θ : InfFam D) : Prop :=
  (∀ k : GA D (D.sp.Y 0), k ∈ GfC (D.sp.Y 0) ↔ (iotaX X h k).1 = 1) ∧
  (∀ k : GA D (D.sp.Y 0), k ∈ GinfC (D.sp.Y 0) ↔ (iotaX X h k).2 = 1) ∧
  (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), (iotaX X h (atTau θ (D.sp.Y 0) τ g)).2 = 1 ∧
    (∀ v, v ≠ X.pl.symm τ → (iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 v = 1) ∧
    HEq (uMat ((iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ)))
      ((fun Pm : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ => Pm⁻¹ * g * Pm)
        ((Formalism.L2.SG.InstExistsPf.instOf D).P (Formalism.L2.Host.tauPl D τ)))) ∧
  ∀ τ (y : Formalism.REAL.UJ (X.B.I.ε (X.pl.symm τ))), ∃ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ),
    (iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ) = y

def EvalAll (θ : InfFam D) {S : D.what₂.Tau → SPar} (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0)))
    (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (v₀ : M.Vec) : Prop :=
  ∃ j : MultT θ M J χ →ₗ⋆[ℂ] HHX X, Function.Bijective j ∧ ∀ T : MultT θ M J χ,
    (((j T : HHX X) : L2X X) : X.B.I.GA → ℂ) =ᵐ[muX X] fun x => star (evS X h t (T.1 (PiTensorProduct.tprod ℂ v₀)) x)

structure RowFun (f : X.B.I.GA → ℂ) : Prop where
  cont : Continuous f
  bdd : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C
  left : ∀ γ ∈ X.B.I.GFset, ∀ x, f (γ * x) = f x
  right : ∀ k ∈ X.K2, ∀ x, f (x * (1, k)) = star (X.chi2 k) * f x

structure SBes (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) where
  V₀ : HSp D
  L : HSp D
  d : HypDec (D.sp.Y 0) V₀ D.R.rS
  o : OrthDec V₀ A L
  ζ : Fin L.rank → D.host.E
  line : IsLineVec L ζ
  cpt : CoCpt A
  vA : Vol A
  vN : VolN d
  tieN : ∀ n, n ∈ flagN d ↔ (iotaX X h n).1 ∈ X.NinfU u ∧ (iotaX X h n).2 ∈ X.NfinU u
  tieH : ∀ g, g ∈ (embA d o).range ↔ (iotaX X h g).1 ∈ Hinf X u ∧ (iotaX X h g).2 ∈ Hfin X u
  tieψ : ∀ n ∈ flagN d, star (psiBes ψ d 1 (vecB o ζ) n) = X.psiInfU u (iotaX X h n).1 * X.psiFinU u (iotaX X h n).2

namespace SBes

variable {X h} {u : D.what₂.Word} {ψ : AddChar (AF D.host.F) ℂ} {A : HSp D} (B : SBes X h u ψ A)

abbrev lev : BesLev D D.R.rS := ⟨D.sp.Y 0, B.V₀, A, B.L, B.d, B.o, B.ζ, B.line, B.cpt, B.vA, B.vN⟩

def toH (a : GA D A) : Hinf X u × Hfin X u :=
  (⟨(iotaX X h (embA B.d B.o a)).1, ((B.tieH _).1 ⟨a, rfl⟩).1⟩, ⟨(iotaX X h (embA B.d B.o a)).2, ((B.tieH _).1 ⟨a, rfl⟩).2⟩)

def colForm (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) (ξ : X.Vpi u) : GA D A → ℂ := fun a => T ξ (B.toH a)

def PerLaw (Y : Formalism.L2.SG.Full.Full X) : Prop :=
  ∃ c : ℂ, ∀ (T : Cu X u Y.hK) (f : X.B.I.GA → ℂ) (φ : L2X X), RowFun X f → (φ : X.B.I.GA → ℂ) =ᵐ[muX X] f →
    ⟪star φ, PuFun X u Y.hK (Y.Dt u) T⟫_ℂ =
      c * ∫ y, B.lev.per ψ (B.colForm T.1 (X.Wu u y)) (fun g => f (iotaX X h g * (y, X.xu u))) ∂(X.nuQ u)

end SBes

theorem rank_eq (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) : (D.sp.Y 0).rank = X.B.I.n := by
  rw [h]; rfl

def SBes.Adapted {X : HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
    {ψ : AddChar (AF D.host.F) ℂ} (B : SBes X h u ψ (D.sp.X 0)) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Prop :=
  ∀ k j, (B.d.i₀ * B.o.iA) k j = X.ιE (X.crd (Formalism.L2.SG.ColDict.qFr wt
    (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) j)) (Fin.cast (rank_eq X h) k))

end Model

section MI

variable {F₀ : ∀ u, Formalism.L2.Forms.Forms0 D u} (S : STrue D F₀) (u : D.what₂.Word) (W : Tower D) (L : Link D u W)

end MI


end GlobalTheory.Core.Mi

end
end

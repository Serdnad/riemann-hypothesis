module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

abbrev EigSys (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ


open Classical in
def badPl (t : T) : Finset (HeightOneSpectrum (𝓞 D.host.F)) :=
  (R.Pg ∪ R.Q t).image fun PP => (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)

def rowPart (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (c : EigSys D) : Submodule ℂ (MMap (R.MY 0)) :=
  partDual R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) Sb c ⊓ R.EEat R.triv

def IsLValue (t : T) (B : GlobalTheory.LFun.Fam D.host.E) (j : ℕ) (l : ℝ) : Prop :=
  GlobalTheory.LFun.Converges (GlobalTheory.LFun.above D.host.E (badPl R t : Set (HeightOneSpectrum (𝓞 D.host.F))))
               (GlobalTheory.LFun.twist B (GlobalTheory.LFun.val (R.toLevCh.mu t j))⁻¹) ((1 + (D.R.t : ℂ)) / 2) ∧
    0 < l ∧ GlobalTheory.LFun.LSD D (badPl R t) B (R.toLevCh.mu t j) ((1 + (D.R.t : ℂ)) / 2) = (l : ℂ)

def IsIP (t : T) (k : ℕ) (u u' : MMap (R.MY k)) (a : ℂ) : Prop :=
  IsMultIP (R.MY k) (R.νY t k) (R.fdY t k) u u' a

def IsUp (t : T) (k : ℕ) (u : MMap (R.MY k)) (x : MMap (R.MY (k + 1))) : Prop :=
  PiTensorProduct.lift x ∈ R.CC t (k + 1) ∧ ∀ y : R.CC t (k + 1), ∃ a : ℂ,
    IsIP R t (k + 1) x (PiTensorProduct.lift.symm y.1) a ∧ IsIP R t k u (PiTensorProduct.lift.symm (R.ioY t k y).1) a

def topStep (t : T) (y : (R.HX t).H) : MMap (R.MY (D.R.m - 1)) :=
  PiTensorProduct.lift.symm (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y)).1

def IsUpTop (t : T) (u : MMap (R.MY (D.R.m - 1))) (x : (R.HX t).H) : Prop :=
  ∀ y : (R.HX t).H, IsIP R t (D.R.m - 1) u (topStep R t y) ⟪x, y⟫_ℂ

def reached (t : T) (c : EigSys D) (k : ℕ) : Set (MMap (R.MY k)) :=
  Nat.rec (motive := fun k => Set (MMap (R.MY k))) (rowPart R (badPl R t) c : Set (MMap (R.MY 0)))
    (fun k P => {x | ∃ u ∈ P, IsUp R t k u x}) k

theorem reached_zero (t : T) (c : EigSys D) : reached R t c 0 = (rowPart R (badPl R t) c : Set (MMap (R.MY 0))) := rfl

theorem reached_succ (t : T) (c : EigSys D) (k : ℕ) :
    reached R t c (k + 1) = {x | ∃ u ∈ reached R t c k, IsUp R t k u x} := rfl

def StepScalar (t : T) (c : EigSys D) (k : ℕ) (Λ : ℝ) : Prop :=
  (∀ u ∈ reached R t c k, ∃ x, IsUp R t k u x) ∧
  ∀ u₁ ∈ reached R t c k, ∀ u₂ ∈ reached R t c k, ∀ x₁ x₂, IsUp R t k u₁ x₁ → IsUp R t k u₂ x₂ →
    ∃ a : ℂ, IsIP R t k u₁ u₂ a ∧ IsIP R t (k + 1) x₁ x₂ ((Λ : ℂ) * a)

def TopScalar (t : T) (c : EigSys D) (Λ : ℝ) : Prop :=
  (∀ u ∈ reached R t c (D.R.m - 1), ∃ x, IsUpTop R t u x) ∧
  ∀ u₁ ∈ reached R t c (D.R.m - 1), ∀ u₂ ∈ reached R t c (D.R.m - 1), ∀ x₁ x₂, IsUpTop R t u₁ x₁ → IsUpTop R t u₂ x₂ →
    ∃ a : ℂ, IsIP R t (D.R.m - 1) u₁ u₂ a ∧ ⟪x₁, x₂⟫_ℂ = (Λ : ℂ) * a

def ScalarsWith (κ : ℕ → ℝ) : Prop :=
  ∀ (t : T) (c : EigSys D), rowPart R (badPl R t) c ≠ ⊥ →
    (∃ B, GlobalTheory.LFun.IsSysParamD D (badPl R t) D.R.r c B) ∧
    ∀ B, GlobalTheory.LFun.IsSysParamD D (badPl R t) D.R.r c B →
      (∀ k, k + 1 < D.R.m → ∃ l, IsLValue R t B (k + 1) l ∧ StepScalar R t c k (κ (k + 1) * l)) ∧
      ∃ l, IsLValue R t B D.R.m l ∧ TopScalar R t c (κ D.R.m * l)

def Scalars : Prop := ∃ κ : ℕ → ℝ, (∀ j, 1 ≤ j → j ≤ D.R.m → 0 < κ j) ∧ ScalarsWith R κ

theorem rowPart_mono {Sb Sb' : Finset (HeightOneSpectrum (𝓞 D.host.F))} (h : Sb ⊆ Sb') (c : EigSys D) :
    rowPart R Sb c ≤ rowPart R Sb' c := by
  refine inf_le_inf_right _ fun u hu => ?_
  rw [partDual, mem_partFull] at hu ⊢
  refine ⟨hu.1, fun P d Rp hR => hu.2 P d Rp ?_⟩
  obtain ⟨e, f, ϖ, α, h1, h2⟩ := hR
  exact ⟨e, f, ϖ, α, fun v hv => h1 v (h hv), h2⟩

theorem IsLValue.unique {R : RealDat D A Ks} {t : T} {B : GlobalTheory.LFun.Fam D.host.E} {j : ℕ} {l l' : ℝ}
    (h : IsLValue R t B j l) (h' : IsLValue R t B j l') : l = l' := by
  exact_mod_cast h.2.2.symm.trans h'.2.2

end GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Links Formalism.IndefR.Mult Matrix

namespace GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def SignCompat {p q n : ℕ} (ε : Fin n → Bool) (e : Ix p q ≃ Fin n) : Prop := ∀ a, ε (e a) = a.isLeft

def plainMat {p q n : ℕ} (e : Ix p q ≃ Fin n) (g : Mat p q) : Matrix (Fin n) (Fin n) ℂ := Matrix.reindex e e g

def barMat {p q n : ℕ} (e : Ix p q ≃ Fin n) (g : Mat p q) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.reindex e e (g.map (starRingEnd ℂ))

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def toFrame (M : DSModel V S) (τ : D.what₂.Tau) (Y : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    Matrix (Fin V.rank) (Fin V.rank) ℂ := (M.fr τ)⁻¹ * Y * M.fr τ


open Classical in
structure Matches {p q : ℕ} {T : GrpData p q} (R : DSRep T) (M : DSModel V S) (τ : D.what₂.Tau)
    (φ : Mat p q → Matrix (Fin V.rank) (Fin V.rank) ℂ) (m : ℤ) (U : M.H τ → R.U.H) : Prop where

  grp : ∀ (g : T.G) (x : M.H τ),
    R.U.π g (U x) = ((T.sq g : ℂˣ) : ℂ) ^ (-m) • U (M.σ τ (φ ((T.cov g : GL (Ix p q) ℂ) : Mat p q)) x)

  kfin : ∀ x : M.H τ, Formalism.MainNotions.S.IsKFin (M.ε τ) (M.σ τ) x ↔ U x ∈ Set.range R.ι

  smooth : ∀ x : M.H τ, U x ∈ Set.range R.ι → SmoothVec (lieAt V τ) (M.rep τ) x

  lie : (fun Z => toFrame M τ (φ Z)) '' upq p q = lieAt V τ

  der : ∀ Z ∈ upq p q, ∀ (v : R.HK.V) (x : M.H τ), U x = R.ι v →
    U (dRep (M.rep τ) (toFrame M τ (φ Z)) x) = R.ι (R.HK.act Z v + ((m : ℂ) / 2 * Z.trace) • v)

  derT : ∀ Z ∈ upq p q, ∀ (v : R.HK.V) (x : M.Vec) (y : M.sm τ), U (x τ : M.H τ) = R.ι v →
    U (y : M.H τ) = R.ι (R.HK.act Z v + ((m : ℂ) / 2 * Z.trace) • v) →
    DerT M τ (toFrame M τ (φ Z)) (PiTensorProduct.tprod ℂ x) (PiTensorProduct.tprod ℂ (Function.update x τ y))

def HidaSetting (X : ProvA) (p q : ℕ) (l₁ l₂ : List ℚ) (c : ℚ) (S : D.what₂.Tau → SPar) (τ : D.what₂.Tau) : Prop :=
  1 ≤ p + q ∧ l₁.length = p ∧ l₂.length = q ∧ IsParam (ofBlocks l₁ l₂ : Ix p q → ℚ) ∧
    HasParam (X.ds p q (ofBlocks l₁ l₂)) (ofBlocks l₁ l₂) ∧ S τ = dualPar (GlobalTheory.Chain.signed l₁ l₂ c)

def SourceBridge (D : D7) : Prop :=
  ∀ (X : ProvA) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau)
    (p q : ℕ) (l₁ l₂ : List ℚ) (c : ℚ), HidaSetting X p q l₁ l₂ c S τ →
    (∃ e : Ix p q ≃ Fin V.rank, SignCompat (M.ε τ) e) ∧
    ∃ m : ℤ, (m : ℚ) = 2 * c ∧ ∀ e : Ix p q ≃ Fin V.rank, SignCompat (M.ε τ) e →
      ∃ U : M.H τ ≃ₗᵢ[ℂ] (X.ds p q (ofBlocks l₁ l₂)).U.H,
        Matches (X.ds p q (ofBlocks l₁ l₂)) M τ (barMat e) m U

def TargetBridge (D : D7) : Prop :=
  ∀ (X : ProvA) (W : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel W S) (τ : D.what₂.Tau)
    (r s : ℕ) (l₁ l₂ : List ℚ) (c : ℚ), HidaSetting X r s l₁ l₂ c S τ →
    (∃ e : Ix r s ≃ Fin W.rank, SignCompat (M.ε τ) e) ∧
    ∃ m : ℤ, (m : ℚ) = 2 * c ∧ ∀ e : Ix r s ≃ Fin W.rank, SignCompat (M.ε τ) e →
      ∃ U : M.H τ ≃ₗᵢ⋆[ℂ] (X.ds r s (ofBlocks l₁ l₂)).U.H,
        Matches (X.ds r s (ofBlocks l₁ l₂)) M τ (plainMat e) m U

def ModelsAreCoverSeries (D : D7) : Prop := SourceBridge D ∧ TargetBridge D

theorem reindex_form {p q n : ℕ} {ε : Fin n → Bool} {e : Ix p q ≃ Fin n} (h : SignCompat ε e) :
    Matrix.reindex e e (Formalism.UG.Jpq p q) = Formalism.REAL.Jm ε := by
  ext a b
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  have ha := h a
  rcases a with a | a <;> rcases b with b | b <;>
    simp_all [Formalism.UG.Jpq, Formalism.REAL.Jm, Matrix.diagonal_apply, Matrix.one_apply] <;> split_ifs <;> simp_all

theorem plainMat_mem {p q n : ℕ} {ε : Fin n → Bool} {e : Ix p q ≃ Fin n} (h : SignCompat ε e) {g : Mat p q}
    (hg : gᴴ * Formalism.UG.Jpq p q * g = Formalism.UG.Jpq p q) : plainMat e g ∈ Formalism.MainNotions.S.UJset ε := by
  change (plainMat e g)ᴴ * Formalism.REAL.Jm ε * plainMat e g = Formalism.REAL.Jm ε
  rw [← reindex_form h]
  simp only [plainMat, Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hg]

theorem barMat_mem {p q n : ℕ} {ε : Fin n → Bool} {e : Ix p q ≃ Fin n} (h : SignCompat ε e) {g : Mat p q}
    (hg : gᴴ * Formalism.UG.Jpq p q * g = Formalism.UG.Jpq p q) : barMat e g ∈ Formalism.MainNotions.S.UJset ε := by
  refine plainMat_mem h ?_
  have hJ : (Formalism.UG.Jpq p q).map (starRingEnd ℂ) = Formalism.UG.Jpq p q := by
    ext a b
    rcases a with a | a <;> rcases b with b | b <;> simp [Formalism.UG.Jpq, Matrix.one_apply] <;> split_ifs <;> simp
  have h1 := congrArg (fun A : Mat p q => A.map (starRingEnd ℂ)) hg
  simp only [Matrix.map_mul, hJ] at h1
  exact h1

end GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField
open GlobalTheory.Chain

namespace GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def signCard (S : SPar) (b : Bool) : ℕ := (S.filter fun x => x.2 = b).card

def SigLowered (S : D.what₂.Tau → SPar) (i : ℕ) (V' : HSp D) : Prop :=
  ∀ τ, ∃ p' q' : ℕ, p' + i = signCard (S τ) true ∧ q' + i = signCard (S τ) false ∧
    Formalism.UG.HasSignature (gramAt D V' τ) p' q'

def LowVanish (D : D7) : Prop :=
  ∀ (k : Fin D.R.m) (i : ℕ) (V' W : HSp D) (M' : DSModel W (parB (Ptw D) (k + 1)))
    (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ → ChainPar D k →
    1 ≤ i → SigLowered (parB (Ptw D) k) i V' →
    ∀ ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ), IsStepWeil k ψ V' W ω' →
    ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)), ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν →
    ∀ (J : Set (GA D W)) (χ : GA D W → ℂ), ∀ F ∈ MultT θ M' J χ, ∀ (v : SmT M') (f' : WO V' W → ℂ),
      IsThetaFunO ψ V' W f' → Lift.liftInt ν 𝓕 (thetaKO ω') f' (F v) = 0

theorem signCard_dualPar (S : SPar) (b : Bool) : signCard (dualPar S) b = signCard S b := by
  unfold signCard dualPar
  rw [Finset.filter_image, Finset.card_image_of_injective]
  intro x y h
  simp only [Prod.mk.injEq, neg_inj] at h
  exact Prod.ext h.1 h.2

end GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix GlobalTheory.Chain

namespace GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def sgn (e : Bool) : ℂ := if e then 1 else -1

def idx {n : ℕ} (ε : Fin n → Bool) : ℚ := ∑ a, if ε a then (1 : ℚ) else -1

def wtS {b : ℕ} (ε' : Fin b → Bool) (aT : ℚ) (e : Bool) : ℚ := (if e then -(idx ε' / 2) else idx ε' / 2) - aT

def wtT {a : ℕ} (ε : Fin a → Bool) (aS : ℚ) (e : Bool) : ℚ := (if e then idx ε / 2 else -(idx ε / 2)) + aS

def signBlockDeterminant {n : ℕ} (ε : Fin n → Bool) (e : Bool) (g : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  (g.submatrix (Subtype.val : {a // ε a = e} → Fin n) (Subtype.val : {a // ε a = e} → Fin n)).det

def elt {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (τ : D.what₂.Tau)
    (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : GA D V :=
  atTau θ V τ ((M.fr τ)⁻¹ * g * M.fr τ)

section Fock

variable {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool)

def raiO (i : Fin b) (j : Fin a) : Module.End ℂ (PolF D b a) := by
  classical
  exact sgn (ε j) • (if ε' i = ε j then LinearMap.mulLeft ℂ (MvPolynomial.X (τ, i, j))
    else -(MvPolynomial.pderiv (τ, i, j)).toLinearMap)

def lowO (i : Fin b) (j : Fin a) : Module.End ℂ (PolF D b a) := by
  classical
  exact sgn (ε j) • (if ε' i = ε j then (MvPolynomial.pderiv (τ, i, j)).toLinearMap
    else LinearMap.mulLeft ℂ (MvPolynomial.X (τ, i, j)))

def fockS (X : Matrix (Fin a) (Fin a) ℂ) : Module.End ℂ (PolF D b a) :=
  ∑ j, ∑ k, X j k • ∑ i, (raiO τ ε ε' i j * lowO τ ε ε' i k + if j = k then (1 / 2 : ℂ) • 1 else 0)

def fockT (Y : Matrix (Fin b) (Fin b) ℂ) : Module.End ℂ (PolF D b a) :=
  ∑ i, ∑ l, Y i l • ∑ j, (raiO τ ε ε' i j * lowO τ ε ε' l j + if i = l then (1 / 2 : ℂ) • 1 else 0)

def subst (g : Matrix (Fin a) (Fin a) ℂ) (k : Matrix (Fin b) (Fin b) ℂ) : PolF D b a →ₐ[ℂ] PolF D b a := by
  classical
  exact MvPolynomial.aeval fun v : FVar D b a =>
    if v.1 = τ then
      ∑ l, ∑ m, (if ε' v.2.1 = ε v.2.2 then k l v.2.1 * g m v.2.2 else star (k l v.2.1 * g m v.2.2)) •
        MvPolynomial.X (τ, l, m)
    else MvPolynomial.X v

end Fock

section Clauses

variable {V W : HSp D} {S S' : D.what₂.Tau → SPar} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
  (M : DSModel V S) (M' : DSModel W S') (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ)
  (τ : D.what₂.Tau) (aS aT : ℚ)

def TorusVac : Prop :=
  ∀ (t : Fin V.rank → ℝ) (t' : Fin W.rank → ℝ),
    ω (elt θ M τ (diagonal fun j => Complex.exp (Complex.I * t j)),
        elt θ M' τ (diagonal fun i => Complex.exp (Complex.I * t' i))) f =
      Complex.exp (Complex.I * (∑ j, (wtS (M'.ε τ) aT (M.ε τ j) : ℂ) * t j +
        ∑ i, (wtT (M.ε τ) aS (M'.ε τ i) : ℂ) * t' i)) • f

def CompactFock : Prop :=
  ∃ x y : Bool → ℤ, (∀ j, (x (M.ε τ j) : ℚ) = wtS (M'.ε τ) aT (M.ε τ j)) ∧
    (∀ i, (y (M'.ε τ i) : ℚ) = wtT (M.ε τ) aS (M'.ε τ i)) ∧
    ∀ h ∈ Formalism.REAL.Kset (M.ε τ), ∀ k ∈ Formalism.REAL.Kset (M'.ε τ), ∀ P : PolF D W.rank V.rank,
      ω (elt θ M τ h, elt θ M' τ k) (ptOf ψ θ M M' f P) =
        (signBlockDeterminant (M.ε τ) true h ^ x true * signBlockDeterminant (M.ε τ) false h ^ x false *
          (signBlockDeterminant (M'.ε τ) true k ^ y true * signBlockDeterminant (M'.ε τ) false k ^ y false)) •
          ptOf ψ θ M M' f (subst τ (M.ε τ) (M'.ε τ) (h.map (starRingEnd ℂ)) k P)

def LieFock : Prop :=
  (∀ X ∈ lieAt V τ, ∀ (P : PolF D W.rank V.rank) (z : WO V W),
    HasDerivAt (fun t : ℝ => ω (oneP θ V τ X t, 1) (ptOf ψ θ M M' f P) z)
      (ptOf ψ θ M M' f (fockS τ (M.ε τ) (M'.ε τ) ((M.fr τ * X * (M.fr τ)⁻¹).map (starRingEnd ℂ)) P -
        ((aT : ℂ) * X.trace) • P) z) 0) ∧
  ∀ Y ∈ lieAt W τ, ∀ (P : PolF D W.rank V.rank) (z : WO V W),
    HasDerivAt (fun t : ℝ => ω (1, oneP θ W τ Y t) (ptOf ψ θ M M' f P) z)
      (ptOf ψ θ M M' f (fockT τ (M.ε τ) (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) P +
        ((aS : ℂ) * Y.trace) • P) z) 0

end Clauses

def VacChar (D : D7) : Prop :=
  ∀ (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D)
    (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle)
    (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ) (τ : D.what₂.Tau) (aS aT : ℚ),
    IsInfFam θ → IsWeilDatumO ψ V W χS χT ω → HasInfExp D χS τ aS → HasInfExp D χT τ aT → IsVacVec ψ θ M M' f →
      TorusVac θ M M' ω f τ aS aT ∧ CompactFock ψ θ M M' ω f τ aS aT ∧ LieFock ψ θ M M' ω f τ aS aT

end GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators

end
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.IndefiniteRowSideFullHecke.HeckeTransferRankOne

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
  Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Real

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

end Real

theorem rank_Vc (i : Fin D.R.m) : (Vc D i).rank = D.R.nV ∧ D.R.nV = D.R.r + D.R.t :=
  ⟨D.sp.V_rank _ (Nat.le_add_left _ _) i.2, rfl⟩

end GlobalTheory.IndefiniteRowSideFullHecke.HeckeTransferRankOne
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT

namespace GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Model

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def LowIrr (M : DSModel V S) : Prop :=
  ∀ τ, IsKTypeOf (M.ε τ) (M.σ τ) (Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) (lowKSub (M.ε τ) (M.lam τ) (M.σ τ))

end Model

section Base

variable {D : D7}

abbrev pW (i : Fin D.R.m) (τ : D.what₂.Tau) : ℕ := ((Wc D i).sig (tauE D τ)).1

abbrev qW (i : Fin D.R.m) (τ : D.what₂.Tau) : ℕ := ((Wc D i).sig (tauE D τ)).2

theorem pW_add_qW (i : Fin D.R.m) (τ : D.what₂.Tau) : pW i τ + qW i τ = (Wc D i).rank :=
  sig_sum _ (D.sp.W_sig _) _

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


end Base

end GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType

end
end

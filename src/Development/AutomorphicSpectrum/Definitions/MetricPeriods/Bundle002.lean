module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
public import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Linter.Style
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

namespace GlobalTheory.CompanionTheory.Ar.Cusp

open NumberField Matrix MeasureTheory GlobalTheory.CompanionTheory.Ar
open scoped ComplexOrder

section Ball

variable {Ψ : Type} [Fintype Ψ] {j j' n : ℕ}

def ballMat (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) (τ : Ψ) : Matrix (Fin j) (Fin j') ℂ :=
  Matrix.of fun a b => t (q (τ, a, b))

def ballDom (q : Ψ × Fin j × Fin j' ≃ Fin n) : Set (Fin n → ℂ) :=
  {t | ∀ τ, (1 - (ballMat q t τ)ᴴ * ballMat q t τ).PosDef}

def ballPot (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) : ℝ :=
  -∑ τ, Real.log (1 - (ballMat q t τ)ᴴ * ballMat q t τ).det.re

def ballDens (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) : ℝ := Real.exp ((j + j' : ℕ) * ballPot q t)

end Ball

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

def autGrp (form : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ) : Subgroup (Λ ≃ₗ[𝓞 E] Λ) where
  carrier := {γ | ∀ x y, form (γ x) (γ y) = form x y}
  one_mem' _ _ := rfl
  mul_mem' {a b} ha hb x y := by
    show form (a (b x)) (a (b y)) = form x y
    rw [ha, hb]
  inv_mem' {a} ha x y := by
    have h := ha (a.symm x) (a.symm y)
    simp only [LinearEquiv.apply_symm_apply] at h
    exact h.symm

def RiemLat.HasSig {Ψ : Type} (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (j j' : ℕ) : Prop :=
  ∀ τ, Module.finrank ℂ (eigSp R.B (σ τ)) = j' ∧ Module.finrank ℂ (eigSp R.B ((starRingEnd ℂ).comp (σ τ))) = j

def RiemLat.EqvBy (R R' : RiemLat E g Λ) (γ : Λ ≃ₗ[𝓞 E] Λ) : Prop :=
  ∃ h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ x, R'.P (γ x) = h (R.P x)


variable (E) in
structure UnivFam (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] where

  q : Ψ × Fin j × Fin j' ≃ Fin n

  σ : Ψ → (𝓞 E →+* ℂ)
  cm : IsCMFam σ

  form : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ

  R : (Fin n → ℂ) → RiemLat E g Λ
  form_eq : ∀ t, (R t).form = form
  hol : IsHolFam (ballDom q) R
  sig : ∀ t ∈ ballDom q, (R t).HasSig σ j j'

  b : Ψ → Fin j' → (Fin n → ℂ) → Fin g → ℂ
  frames : IsEigFrames (ballDom q) (fun t => (R t).B) σ b
  logDet_eq : ∀ t ∈ ballDom q, (R t).logDet (fun τ i => b τ i t) = ballPot q t
  univ : ∀ R' : RiemLat E g Λ, R'.form = form → R'.HasSig σ j j' → ∃! t, t ∈ ballDom q ∧ (R t).EqvBy R' 1

namespace UnivFam

variable {Ψ : Type} [Fintype Ψ] {j j' n : ℕ} (F : UnivFam E Ψ j j' n g Λ)

def Eqv (Γ : Subgroup (Λ ≃ₗ[𝓞 E] Λ)) (t t' : Fin n → ℂ) : Prop := ∃ γ ∈ Γ, (F.R t).EqvBy (F.R t') γ

def IsFundSet (Γ : Subgroup (Λ ≃ₗ[𝓞 E] Λ)) (FF : Set (Fin n → ℂ)) : Prop :=
  MeasurableSet FF ∧ FF ⊆ ballDom F.q ∧ (∀ t ∈ ballDom F.q, ∃ t' ∈ FF, F.Eqv Γ t t') ∧
    ∀ t ∈ FF, ∀ t' ∈ FF, F.Eqv Γ t t' → t = t'

def IsArith (Γ : Subgroup (Λ ≃ₗ[𝓞 E] Λ)) : Prop := Γ ≤ autGrp F.form ∧ Γ.relIndex (autGrp F.form) ≠ 0

end UnivFam

end GlobalTheory.CompanionTheory.Ar.Cusp
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open MvPolynomial Filter Topology
open scoped ComplexOrder ContDiff

structure AnSq {d : ℕ} {σ : Type} [Fintype σ] (SY : AnSys (d + 1) σ) (a₀ : σ) (ε : σ → ℤ) where
  eps_a₀ : ε a₀ = -2

  SW : AnSys (d + 2) (Option σ)

  q : Fin 2 → SW.X → SY.X
  holo : ∀ j, HoloMap SW.A SY.A (q j)
  bdry_eq : ∀ j, SW.open' = q j ⁻¹' SY.open'
  t₀_le : SW.t₀ ≤ SY.t₀
  th0 : ∀ a, SamePot SW.A Set.univ (SW.th (some a)) ((SY.th a).pullback (q 0) (holo 0).1)
  th1 : SamePot SW.A Set.univ (SW.th none) ((SY.th a₀).pullback (q 1) (holo 1).1)
  ph0 : ∀ a, SW.ph (some a) = SY.ph a ∘ q 0
  ph1 : SW.ph none = SY.ph a₀ ∘ q 1
  phase_some_eq_comp_first_projection : ∀ a t, SW.phT (some a) t = SY.phT a t ∘ q 0
  phase_none_eq_comp_second_projection : ∀ t, SW.phT none t = SY.phT a₀ t ∘ q 1
  base_ph : ∀ a, a ≠ a₀ → SY.ph a ∘ q 0 = SY.ph a ∘ q 1
  base_phT : ∀ a, a ≠ a₀ → ∀ t, SY.phT a t ∘ q 0 = SY.phT a t ∘ q 1

  L' : LocPot SW.X

  v : SW.X → SW.X → ℂ

  Dg : Set SW.X

  cst : ℝ
  potL' : IsPotential SW.A L'
  secv : IsSection SW.A L' v
  sncv : IsSNC SW.A L' v ![1] ![Dg]
  sncsv : IsSNC SW.A (SW.L + L') (fun x y => SW.s x y * v x y) (Fin.snoc SW.m 1) (Fin.snoc SW.W Dg)
  normv : ∀ y, logNormSec L' v y ≤ 0

  U : ℕ → Set (Fin d → ℂ)

  B : ℕ → Set (Fin d → ℂ)

  G : ℕ → (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ

  α : ℕ → σ → (Fin d → ℂ) → ℝ

  ΦY : ℕ → (Fin (d + 1) → ℂ) → SY.X

  ΦW : ℕ → (Fin (d + 2) → ℂ) → SW.X
  U_open : ∀ n, IsOpen (U n)
  B_meas : ∀ n, MeasurableSet (B n) ∧ B n ⊆ U n
  G_pos : ∀ n, ∀ y ∈ U n, (G n y).PosDef
  G_smooth : ∀ n p r, ContDiffOn ℝ ∞ (fun y => G n y p r) (U n)
  α_smooth : ∀ n a, ContDiffOn ℝ ∞ (α n a) (U n)
  coverY : IsParamCover SY.A (fun n => {z | Fin.tail z ∈ U n}) (fun n => {z | Fin.tail z ∈ B n}) ΦY
  coverW : IsParamCover SW.A (fun n => {z | Fin.tail (Fin.tail z) ∈ U n})
    (fun n => {z | Fin.tail (Fin.tail z) ∈ B n}) ΦW
  ΦY_open : ∀ n (z : Fin (d + 1) → ℂ), Fin.tail z ∈ U n → ΦY n z ∈ SY.open'
  first_projection_chart_compat : ∀ n (z : Fin (d + 2) → ℂ), Fin.tail (Fin.tail z) ∈ U n → q 0 (ΦW n z) = ΦY n (Fin.cons (z 0) (Fin.tail (Fin.tail z)))
  second_projection_chart_compat : ∀ n (z : Fin (d + 2) → ℂ), Fin.tail (Fin.tail z) ∈ U n → q 1 (ΦW n z) = ΦY n (Fin.tail z)
  xi_pot : ∀ n (z : Fin (d + 1) → ℂ), Fin.tail z ∈ U n → ∃ H : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ H z ∧ ∀ᶠ z' in 𝓝 z,
    ∑ a, (ε a : ℝ) * (SY.potH a).φ (ΦY n z) (ΦY n z') = xiPot (G n (Fin.tail z')) (z' 0) + (H z').re
  base_pot : ∀ n a, a ≠ a₀ → ∀ z : Fin (d + 1) → ℂ, Fin.tail z ∈ U n → ∃ H : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ H z ∧
    ∀ᶠ z' in 𝓝 z, (SY.potH a).φ (ΦY n z) (ΦY n z') = α n a (Fin.tail z') + (H z').re
  norm_hom : ∀ n (z : Fin (d + 2) → ℂ), Fin.tail (Fin.tail z) ∈ U n → z 0 ≠ z 1 →
    logNormSec L' v (ΦW n z) + cst +
        (1 / 2) * ∑ a, (ε a : ℝ) * (SY.ph a (q 0 (ΦW n z)) + SY.ph a (q 1 (ΦW n z))) =
      logSin (G n (Fin.tail (Fin.tail z))) (z 0) (z 1)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

structure AlgSq (P : Ideal (MRing ι)) (d : ℕ) (k₀ : K) (xi2 : K → ℤ) where
  arithY : IsArithVar P (d + 2)
  xi_two_base_eq_neg_two : xi2 k₀ = -2

  KW : Type
  [finKW : Fintype KW]

  ιW : KW → Type
  [finιW : ∀ k, Fintype (ιW k)]

  PW : Ideal (MRing ιW)
  arithW : IsArithVar PW (d + 3)

  κ : Fin 2 → K → KW

  v : Fin 2 → (Σ k, ι k) → (Σ k, ιW k)
  block : ∀ j, IsBlockMap (κ j) (v j)
  image : ∀ j, imageZ (v j) PW = P
  same : ∀ p : Σ k, ι k, p.1 ≠ k₀ → v 0 p = v 1 p
  new : κ 1 k₀ ∉ Set.range (κ 0)
  all : ∀ k', k' ∈ Set.range (κ 0) ∨ k' = κ 1 k₀
  fibre_line : ∀ G : GenFibre (v 0) PW, ∃ T : Set (MRingOver G.Φ (fibreIdx ιW (κ 0))),
    (∀ f ∈ T, IsMultiHomog f fun _ => 1) ∧ fibreIdeal (κ 0) G = Ideal.span T

  Δ : Ideal (MRing ιW)
  arithΔ : IsArithVar Δ (d + 2)
  PW_le : PW ≤ Δ
  diag : ∀ i i' : ι k₀, X (v 0 ⟨k₀, i⟩) * X (v 1 ⟨k₀, i'⟩) - X (v 0 ⟨k₀, i'⟩) * X (v 1 ⟨k₀, i⟩) ∈ Δ

  g : MRing ιW

  h : MRing ιW

  dg : KW → ℕ

  dh : KW → ℕ
  g_deg : IsMultiHomog g dg
  h_deg : IsMultiHomog h dh
  g_nmem : g ∉ PW
  h_nmem : h ∉ PW
  deg_eq : ∀ k', 2 * ((dg k' : ℤ) - dh k') = -(pullDeg (κ 0) xi2 k' + pullDeg (κ 1) xi2 k')
  div_eq : divCycle PW g = divCycle PW h + Finsupp.single Δ 1

attribute [instance] AlgSq.finKW AlgSq.finιW

def AlgSq.logNormT {P : Ideal (MRing ι)} {d : ℕ} {k₀ : K} {xi2 : K → ℤ} (Q : AlgSq P d k₀ xi2)
    (Xi : HermLine ι) (z : (Σ k, Q.ιW k) → ℂ) : ℝ :=
  Real.log (‖eval z (map (Int.castRingHom ℂ) Q.g)‖ / ‖eval z (map (Int.castRingHom ℂ) Q.h)‖) +
    (Real.log (Xi.h fun p => z (Q.v 0 p)) + Real.log (Xi.h fun p => z (Q.v 1 p))) / 2

def FromBase (k₀ : K) (A : HermLine ι) : Prop :=
  A.a k₀ = 0 ∧ ∀ z z' : (Σ k, ι k) → ℂ, (∀ p : Σ k, ι k, p.1 ≠ k₀ → z p = z' p) → A.h z = A.h z'

structure SqSys {d : ℕ} {σ : Type} [Fintype σ] {SY : AnSys (d + 1) σ} {P : Ideal (MRing ι)} (Re : Realis SY P)
    (a₀ : σ) (ε : σ → ℤ) where

  k₀ : K

  an : AnSq SY a₀ ε

  alg : AlgSq P d k₀ (combLine Re.ref ε).a

  ReW : Realis an.SW alg.PW
  deg_eq : ReW.deg = Re.deg
  base : ∀ a, a ≠ a₀ → ∀ t, FromBase k₀ (Re.line a t)
  pull0 : ∀ a t, IsPullHerm (alg.κ 0) (alg.v 0) (Re.line a t) (ReW.line (some a) t)
  pull1 : ∀ t, IsPullHerm (alg.κ 1) (alg.v 1) (Re.line a₀ t) (ReW.line none t)
  norm_eq : ∃ N : Set ReW.R.X, IsNull ReW.R.A N ∧ ∀ t, 0 < t → t ≤ an.SW.t₀ → ∀ x ∉ N,
    alg.logNormT (combLine (fun a => Re.line a t) ε) (ReW.R.lift x x) =
      logNormSec an.L' an.v (ReW.π x) + an.cst +
        (1 / 2) * ∑ a, (ε a : ℝ) * (SY.phT a t (an.q 0 (ReW.π x)) + SY.phT a t (an.q 1 (ReW.π x)))

end GlobalTheory.CompanionTheory.Ar.PB
end
end

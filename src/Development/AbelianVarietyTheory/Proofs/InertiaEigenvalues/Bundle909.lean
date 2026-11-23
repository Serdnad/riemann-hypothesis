module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle567
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle534
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle854
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle843
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarmVecEqPhaseLetters
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle492
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle879
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle495
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle896
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle871
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CellDecompositionLatticeIntegralUnfolding
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle883
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle897
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import GroundTheory.AutomorphicForms.Bundle012
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle899
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle727
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle900
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle901
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1648
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelExtensionFirst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

noncomputable section

namespace GlobalTheory.DownLift.SplitCoef.Decomp

variable {D : D7}

theorem heisO_lin_sub (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (x : WO S T) (f g : WO S T → ℂ) :
    heisO ψ S T x (f - g) = heisO ψ S T x f - heisO ψ S T x g := by
  rw [← GlobalTheory.SplitScalar.heisL_apply, map_sub]; rfl

theorem heisO_lin_add (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (x : WO S T) (f g : WO S T → ℂ) :
    heisO ψ S T x (f + g) = heisO ψ S T x f + heisO ψ S T x g := by
  rw [← GlobalTheory.SplitScalar.heisL_apply, map_add (f := _)]; rfl

theorem heisO_lin_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (x : WO S T) :
    heisO ψ S T x (0 : WO S T → ℂ) = 0 := by
  rw [← GlobalTheory.SplitScalar.heisL_apply, map_zero]

theorem theta_of_mem_span {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {𝒯 : Set (WO S T → ℂ)}
    (h0 : IsThetaFunO ψ S T 0) (h𝒯 : ∀ φ ∈ 𝒯, IsThetaFunO ψ S T φ) {φ : WO S T → ℂ} (hφ : φ ∈ Submodule.span ℂ 𝒯) : IsThetaFunO ψ S T φ := by
  induction hφ using Submodule.span_induction with
  | mem x hx => exact h𝒯 x hx
  | zero => exact h0
  | add x y _ _ hx hy => exact theta_add hx hy
  | smul c x _ hx => exact theta_smul c hx

theorem exists_decomp (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a : AE D) (f : WO S T → ℂ) (X : Finset (WO S T))
    (hX : ∀ x, IsHalf a x → (∀ ℓ, InvForm ψ S T a ℓ → ℓ (heisO ψ S T x f) = 0) ∨
      ∃ x₁ ∈ X, heisO ψ S T x f = heisO ψ S T x₁ f) :
    ∃ L : WO S T → ((WO S T → ℂ) →ₗ[ℂ] ℂ), (∀ x₁, InvForm ψ S T a (L x₁)) ∧
      ∀ ℓ, InvForm ψ S T a ℓ → ∀ x, IsHalf a x →
        ℓ (heisO ψ S T x f) = ∑ x₁ ∈ X, L x₁ (heisO ψ S T x f) * ℓ (heisO ψ S T x₁ f) := by
  classical
  let K : Submodule ℂ (WO S T → ℂ) := Submodule.span ℂ
    {h | ∃ u g, IsHalf (cA D a) u ∧ IsThetaFunO ψ S T g ∧ h = heisO ψ S T u g - g}
  have inv_iff : ∀ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ, InvForm ψ S T a ℓ ↔ K ≤ LinearMap.ker ℓ := by
    intro ℓ
    constructor
    · intro hℓ
      rw [Submodule.span_le]
      rintro h ⟨u, g, hu, hg, rfl⟩
      simp [LinearMap.mem_ker, map_sub, hℓ u hu g hg]
    · intro hle u hu g hg
      have := hle (Submodule.subset_span ⟨u, g, hu, hg, rfl⟩)
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
      exact this
  have inv_comp : ∀ μ : ((WO S T → ℂ) ⧸ K) →ₗ[ℂ] ℂ, InvForm ψ S T a (μ ∘ₗ K.mkQ) := by
    intro μ
    rw [inv_iff]
    intro h hh
    simp [LinearMap.mem_ker, (Submodule.Quotient.mk_eq_zero K).2 hh]
  let Fq : WO S T → (WO S T → ℂ) ⧸ K := fun x => K.mkQ (heisO ψ S T x f)
  let A : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) ⧸ K :=
    ∑ x₁ ∈ X, (LinearMap.proj x₁ : (WO S T → ℂ) →ₗ[ℂ] ℂ).smulRight (Fq x₁)
  have hA : ∀ c, A c = ∑ x₁ ∈ X, c x₁ • Fq x₁ := by
    intro c
    simp [A, LinearMap.sum_apply]
  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective (LinearMap.range A).subtype (Submodule.ker_subtype _)
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective A.rangeRestrict (LinearMap.range_rangeRestrict A)
  let s := g ∘ₗ p
  have hs : ∀ q ∈ LinearMap.range A, A (s q) = q := by
    intro q hq
    have h1 : p q = ⟨q, hq⟩ := by
      have := LinearMap.congr_fun hp ⟨q, hq⟩
      simpa using this
    have h2 := LinearMap.congr_fun hg (p q)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h2
    have h3 : A (g (p q)) = ((A.rangeRestrict (g (p q)) : LinearMap.range A) : (WO S T → ℂ) ⧸ K) := rfl
    simp only [s, LinearMap.comp_apply]
    rw [h3, h2, h1]
  refine ⟨fun x₁ => (LinearMap.proj x₁ ∘ₗ s) ∘ₗ K.mkQ, fun x₁ => inv_comp _, ?_⟩
  intro ℓ hℓ x hx
  have hle := (inv_iff ℓ).1 hℓ
  have hmem : Fq x ∈ LinearMap.range A := by
    rcases hX x hx with h0 | ⟨x₁, hx₁, he⟩
    · have : Fq x = 0 := by
        rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
        intro μ
        exact h0 (μ ∘ₗ K.mkQ) (inv_comp μ)
      rw [this]
      exact Submodule.zero_mem _
    · refine ⟨Pi.single x₁ 1, ?_⟩
      rw [hA, Finset.sum_eq_single x₁]
      · simp [Fq, he]
      · intro b _ hb
        simp [Pi.single_apply, hb]
      · intro h
        exact absurd hx₁ h
  have key := congrArg (K.liftQ ℓ hle) (hs _ hmem)

  rw [hA, map_sum] at key
  simp only [map_smul, smul_eq_mul] at key
  have hb : ∀ y, K.liftQ ℓ hle (Fq y) = ℓ (heisO ψ S T y f) := fun y => rfl
  simp only [hb] at key
  rw [← key]
  rfl

theorem mem_span_of_coef_mem_span : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ a : AE D, IsSplitIdem D a → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ 𝒢 𝒯 : Set (WO S T → ℂ), (∀ φ ∈ 𝒯, IsThetaFunO ψ S T φ) → (∀ Ψ ∈ 𝒢, ∀ x₁, IsHalf a x₁ → ∃ φ ∈ Submodule.span ℂ 𝒯, ∀ ℓ, InvForm ψ S T a ℓ → ∀ x, IsHalf a x → ℓ (heisO ψ S T x φ) = Ψ x * ℓ (heisO ψ S T x₁ f)) → (∀ ℓ, InvForm ψ S T a ℓ → coef ψ S T a ℓ f ∈ Submodule.span ℂ 𝒢) → f ∈ Submodule.span ℂ 𝒯 := by
  intro D ψ S T hψ a ha f hf 𝒢 𝒯 h𝒯 h𝒢 hcoef
  obtain ⟨-, -, X, hXh, hX⟩ := GlobalTheory.T.thetaCoefficient_isSchwartzBruhat_uniform_split D ψ S T hψ (GlobalTheory.PlaceModel.latFrame S) (GlobalTheory.PlaceModel.latFrame T)
    (GlobalTheory.PlaceModel.isSelfDualC_latFrame S) (GlobalTheory.PlaceModel.isSelfDualC_latFrame T) a ha f hf
  obtain ⟨L, hLinv, hL⟩ := exists_decomp ψ S T a f X hX
  have hspan : ∀ Ψ ∈ Submodule.span ℂ 𝒢, ∀ x₁, IsHalf a x₁ → ∃ φ ∈ Submodule.span ℂ 𝒯, ∀ ℓ, InvForm ψ S T a ℓ →
      ∀ x, IsHalf a x → ℓ (heisO ψ S T x φ) = Ψ x * ℓ (heisO ψ S T x₁ f) := by
    intro Ψ hΨ x₁ hx₁
    induction hΨ using Submodule.span_induction with
    | mem Ψ hΨ => exact h𝒢 Ψ hΨ x₁ hx₁
    | zero => exact ⟨0, Submodule.zero_mem _, fun ℓ _ x _ => by simp [heisO_lin_zero]⟩
    | add Ψ₁ Ψ₂ _ _ h1 h2 =>
      obtain ⟨φ₁, m1, e1⟩ := h1
      obtain ⟨φ₂, m2, e2⟩ := h2
      refine ⟨φ₁ + φ₂, add_mem m1 m2, fun ℓ hℓ x hx => ?_⟩
      rw [heisO_lin_add, map_add (f := _), e1 ℓ hℓ x hx, e2 ℓ hℓ x hx, Pi.add_apply, add_mul]
    | smul c Ψ _ h =>
      obtain ⟨φ, m, e⟩ := h
      refine ⟨c • φ, Submodule.smul_mem _ c m, fun ℓ hℓ x hx => ?_⟩
      rw [GlobalTheory.SplitScalar.heisO_smul, map_smul, e ℓ hℓ x hx, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_assoc]
  have hφ : ∀ x₁ ∈ X, ∃ φ ∈ Submodule.span ℂ 𝒯, ∀ ℓ, InvForm ψ S T a ℓ → ∀ x, IsHalf a x →
      ℓ (heisO ψ S T x φ) = coef ψ S T a (L x₁) f x * ℓ (heisO ψ S T x₁ f) :=
    fun x₁ hx₁ => hspan _ (hcoef _ (hLinv x₁)) x₁ (hXh x₁ hx₁)
  choose! φ hφm hφe using hφ
  have hsum : (∑ x₁ ∈ X, φ x₁) ∈ Submodule.span ℂ 𝒯 := Submodule.sum_mem _ hφm
  have h0 : IsThetaFunO ψ S T 0 := by simpa using theta_sub hf hf
  have hzero := GlobalTheory.T.splitPlace_invariantForms_separate_thetaFunctions D ψ S T hψ a ha (f - ∑ x₁ ∈ X, φ x₁)
    (theta_sub hf (theta_of_mem_span h0 h𝒯 hsum)) (by
      intro ℓ hℓ x hx

      rw [heisO_lin_sub, GlobalTheory.SplitScalar.heisO_sum, map_sub, map_sum, hL ℓ hℓ x hx, sub_eq_zero]
      refine Finset.sum_congr rfl fun x₁ hx₁ => ?_
      rw [hφe x₁ hx₁ ℓ hℓ x hx, coef, if_pos hx])
  rw [sub_eq_zero] at hzero
  exact hzero ▸ hsum

end GlobalTheory.DownLift.SplitCoef.Decomp
end
end

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries

noncomputable section
namespace GlobalTheory.SerIntLetters
open GlobalTheory.AdTh.PhaseMap GlobalTheory.SerLetters



theorem io_eq_phase_smul_harmLetters : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) → ∀ c0 : VsV D i ℂ →ₗ[ℂ] (R.cV i).W, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsCoefMap R i c0 → ∀ lt : LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank ≃ FVar D (Wc D i).rank (Vc D i).rank, IsLetters (T.Q.Dw ((i : ℕ) + 1)) lt → ∃ ka : ℂ, ‖ka‖ = 1 ∧ ∃ J : VsV D i ℂ →ₗ[ℂ] MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) ℂ, (∀ v, J v ∈ HHa (T.Q.Dw ((i : ℕ) + 1)).mult (Vc D i).rank ℂ ComplexEmbedding.conjugate (InPsi T.Q.H) (fun τ j => wtA (κ i) (τ, j))) ∧ (∀ k : Subfield ℂ, (∀ x ∈ T.Q.c.F, x ∈ k) → ∀ v : VsV D i ℂ, (∀ m, AddMonoidAlgebra.coeff (v : Formalism.L2.DIV.Pol ℂ D.what₂.Tau (Vc D i).rank) m ∈ k) → ∀ mo, (J v).coeff mo ∈ k) ∧ ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ v, pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) f (R.ioP i (PiTensorProduct.tprod ℂ u) (c0 v)) = ka • stdF R.ψ R.θ (Vc D i) (Wc D i) (cart (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) f (MvPolynomial.rename lt (J v)) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hLaws hL hGrp hFam hMod hThP hTie i hstd u hu c0 hc lt hlt
  obtain ⟨ka, hka, io, hio, hJ⟩ := io_eq_phase_smul_letters D G Pl0 T0 A T R κ v₀ hL hFam hMod hThP hTie i hstd u hu c0 hc
    (⇑lt) (fun ℓ => hlt ℓ)
  let b : Formalism.L2.DIV.VVIdx (lamV D i) → VsV D i ℂ := fun j =>
    GlobalTheory.AdTh.CoefExt.up (inC T.Q.c) (lamV D i) (Formalism.L2.DIV.bVV T.Q.c.F (lamV D i) j)
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range b) := fun x _ => by
    obtain ⟨a, rfl⟩ := GlobalTheory.AdTh.CoefExt.exists_coord (inC T.Q.c) (lamV D i) x
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hli : LinearIndependent ℂ b := by
    refine linearIndependent_of_top_le_span_of_card_eq_finrank hsp ?_
    rw [Module.finrank_eq_card_basis (Formalism.L2.DIV.bVV ℂ (lamV D i))]
  let e : Formalism.L2.DIV.VVIdx (lamV D i) → MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) ℂ := fun j =>
    MvPolynomial.map (inC T.Q.c) (io (Formalism.L2.DIV.bVV T.Q.c.F (lamV D i) j))
  let J : VsV D i ℂ →ₗ[ℂ] MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) ℂ := (Module.Basis.mk hli hsp).constr ℂ e
  have hJv : ∀ a : Formalism.L2.DIV.VVIdx (lamV D i) → ℂ, J (∑ j, a j • b j) = ∑ j, a j • e j := fun a => by

    simp only [map_sum, map_smul, J]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show b j = Module.Basis.mk hli hsp j from (Module.Basis.mk_apply hli hsp j).symm, Module.Basis.constr_basis]
  refine ⟨ka, hka, J, fun v => ?_, fun k hk v hv mo => ?_, fun f hf v => ?_⟩
  · obtain ⟨a, rfl⟩ := GlobalTheory.AdTh.CoefExt.exists_coord (inC T.Q.c) (lamV D i) v
    rw [hJv]
    refine GlobalTheory.PtId.mem_HHa_of_span _ _ _ _ _ _ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_))
    exact GlobalTheory.SerLetters.map_mem_HHa (inC T.Q.c) (GlobalTheory.PtId.mem_HHa_of_span _ _ _ _ _ _ (hio _))
  · obtain ⟨a, rfl⟩ := GlobalTheory.AdTh.CoefExt.exists_coord (inC T.Q.c) (lamV D i) v
    have hF : ∀ x : T.Q.c.F, inC T.Q.c x ∈ k := fun x => hk _ (by rw [show inC T.Q.c x = (x : ℂ) from rfl]; exact x.2)
    let φ : T.Q.c.F →+* k := (inC T.Q.c).codRestrict k hF
    let eK : Formalism.L2.DIV.VVIdx (lamV D i) → Formalism.L2.DIV.Pol k D.what₂.Tau (Vc D i).rank := fun j =>
      MvPolynomial.map φ (Formalism.L2.DIV.bVV T.Q.c.F (lamV D i) j : Formalism.L2.DIV.Pol T.Q.c.F D.what₂.Tau (Vc D i).rank)
    have hmap : ∀ j, MvPolynomial.map k.subtype (eK j) = (b j : Formalism.L2.DIV.Pol ℂ D.what₂.Tau (Vc D i).rank) := fun j => by
      show MvPolynomial.map k.subtype (MvPolynomial.map φ _) = MvPolynomial.map (inC T.Q.c) _
      rw [MvPolynomial.map_map]
      rfl
    have hli' : LinearIndependent ℂ fun j => MvPolynomial.map k.subtype (eK j) := by
      have h2 := hli.map' (Submodule.subtype _) (Submodule.ker_subtype _)
      have e2 : (fun j => MvPolynomial.map k.subtype (eK j)) = (Submodule.subtype _) ∘ b := funext hmap
      rw [e2]
      exact h2
    have hsum : (∑ j, a j • MvPolynomial.map k.subtype (eK j)) =
        ((∑ j, a j • b j : VsV D i ℂ) : Formalism.L2.DIV.Pol ℂ D.what₂.Tau (Vc D i).rank) := by
      rw [Submodule.coe_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Submodule.coe_smul, hmap]
    have hcoef : ∀ m, AddMonoidAlgebra.coeff (∑ j, a j • MvPolynomial.map k.subtype (eK j)) m ∈ k.subtype.fieldRange := fun m => by
      rw [hsum]
      exact RingHom.mem_fieldRange.2 ⟨⟨_, hv m⟩, rfl⟩
    have ha : ∀ j, a j ∈ k := fun j => by
      obtain ⟨y, hy⟩ := RingHom.mem_fieldRange.1 (coord_mem_fieldRange k.subtype eK hli' a hcoef j)
      rw [← hy]
      exact y.2
    rw [hJv, MvPolynomial.coeff_sum]
    refine Subfield.sum_mem _ fun j _ => ?_
    rw [MvPolynomial.coeff_smul, smul_eq_mul]
    exact Subfield.mul_mem _ (ha j) (by rw [MvPolynomial.coeff_map]; exact hF _)
  · obtain ⟨a, rfl⟩ := GlobalTheory.AdTh.CoefExt.exists_coord (inC T.Q.c) (lamV D i) v
    rw [hJv]

    simp only [map_sum, map_smul]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hJ f hf, GlobalTheory.AdTh.PhaseMap.toF_apply, smul_comm]

end GlobalTheory.SerIntLetters
end
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

theorem _root_.GlobalTheory.T.cell_decomposition_lattice_integral_unfolding : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (F : GA E (m + 1) → ℂ) (l₀ : GlobalTheory.CellDec.abelian₂ E (m + 1) T) (U : Subgroup (GL (Fin (m + 1)) (Af E))) (Φ : (Fin (m + 1) → Cinf E) → ℂ)
      (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (C : Set (GA E (m + 1))), IsCompact C →
    (∀ w, l₀.1 w (Fin.last m) = 0) → (∀ u ∈ U, ∀ g, GlobalTheory.JSW.whit F (g * finGL E (m + 1) u) = GlobalTheory.JSW.whit F g) →
    (∀ k ∈ GlobalTheory.CellDec.US E (m + 1) T, GeneralLinearGroup.map (pInf E) k = 1 →
      (∀ w ∈ T, GlobalTheory.CellDec.compV E (m + 1) w k = 1) → ∀ g, GlobalTheory.JSW.whit F (g * k) = GlobalTheory.JSW.whit F g) →
    (∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g, ‖GlobalTheory.JSW.whit F (u * g)‖ = ‖GlobalTheory.JSW.whit F g‖) →
    (∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) T ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) ≠ 0 → ∃ u ∈ GlobalTheory.CellDec.NA E (m + 1), u * p ∈ C) →
    HasCompactSupport Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) → (∀ w ∉ T, FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E) = 0) →
    (∀ y : Fin (m + 1) → Af E, y - Pi.single (Fin.last m) 1 ∈ GlobalTheory.ThetaPoisson.latt (m + 1) J →
      ∃ κ ∈ U, (∀ w, GeneralLinearGroup.map (pLoc E w) κ ∈ KGL w (n := (m + 1))) ∧ (∀ w ∉ T, GeneralLinearGroup.map (pLoc E w) κ = 1) ∧
        ∀ w ∈ T, ∀ j, (GeneralLinearGroup.map (pLoc E w) κ : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j =
          pLoc E w (y j)) →
    ∃ K : Set (GA E (m + 1)), IsCompact K ∧ ∀ (x : ℝ) (g : GA E (m + 1)), g ∈ GlobalTheory.CellDec.C0 E (m + 1) T →
      GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 * g) ≠ 0 → ∃ u ∈ GlobalTheory.CellDec.NA E (m + 1), u * g ∈ K := by
  first | (exact @GlobalTheory.RSCell.CptMod.exists_isCompact_mod_NA) | (exact GlobalTheory.RSCell.CptMod.exists_isCompact_mod_NA) | (intros; apply GlobalTheory.RSCell.CptMod.exists_isCompact_mod_NA  <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

theorem _root_.GlobalTheory.T.tsum_schurSquareCellProduct_eq_eulerProduct : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin n → ℂ) (x : ℝ) (l₀ : GlobalTheory.CellDec.abelian₂ E n T),
    ∑' l : GlobalTheory.CellDec.abelian₂ E n T, GlobalTheory.RSCell.cellProd T α x (l.1 - l₀.1) =
      GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal) α x := by
  first | exact @GlobalTheory.RSCellSum.tsum_cellProd_sub_eq_eulD | exact GlobalTheory.RSCellSum.tsum_cellProd_sub_eq_eulD | (intros; apply GlobalTheory.RSCellSum.tsum_cellProd_sub_eq_eulD <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

theorem _root_.GlobalTheory.T.unfoldedRankinSelbergIntegrand_continuous_invariant : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ℓ : Fin a), (ℓ : ℕ) + 1 = a →
    ∀ (F : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E),
    Continuous (GlobalTheory.JSW.whit F) → (∀ u ∈ GlobalTheory.CellDec.NA E a, ∀ g, ‖GlobalTheory.JSW.whit F (u * g)‖ = ‖GlobalTheory.JSW.whit F g‖) →
    Continuous Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ →
    Continuous (fun p : ℝ × GA E a => GlobalTheory.RSCell.bInt ℓ F Φ J η p.1 p.2) ∧
      (∀ x, ∀ u ∈ GlobalTheory.CellDec.NA E a, ∀ g, GlobalTheory.RSCell.bInt ℓ F Φ J η x (u * g) = GlobalTheory.RSCell.bInt ℓ F Φ J η x g) ∧
      ∀ x g, GlobalTheory.RSCell.bInt ℓ F Φ J η x g ≠ ⊤ := by
  first | exact @GlobalTheory.RSCellB.bInt_continuous_invariant_finite | exact GlobalTheory.RSCellB.bInt_continuous_invariant_finite | (intros; apply GlobalTheory.RSCellB.bInt_continuous_invariant_finite <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

theorem _root_.GlobalTheory.T.unfoldedRankinSelbergIntegrand_ne_zero_identity : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (F : GA E (m + 1) → ℂ) (Φ : (Fin (m + 1) → Cinf E) → ℂ)
    (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (l₀ : GlobalTheory.CellDec.abelian₂ E (m + 1) T), (∀ w, l₀.1 w (Fin.last m) = 0) →
    GlobalTheory.JSW.whit F (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) ≠ 0 → Φ (Pi.single (Fin.last m) 1) ≠ 0 → ∀ x : ℝ, GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) ≠ 0 := by
  first | exact @GlobalTheory.RSCell.bInt_tl_last_ne_zero | exact GlobalTheory.RSCell.bInt_tl_last_ne_zero | (intros; apply GlobalTheory.RSCell.bInt_tl_last_ne_zero <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

theorem _root_.GlobalTheory.T.spherical_local_factor_norm_sq : ∀ (q : ℕ), 0 < q → ∀ (n : ℕ) (α : Fin (n + 1) → ℂ) (x : ℝ) (ν : Fin (n + 1) → ℤ), 0 ≤ ν (Fin.last n) →
    ENNReal.ofReal ((q : ℝ) ^ GlobalTheory.CellDec.wtS (n + 1) ν) * ENNReal.ofReal ((q : ℝ) ^ (-((∑ i, (ν i : ℝ)) * x))) *
      ‖GlobalTheory.RSCell.sphZ q α ν‖ₑ ^ 2 = GlobalTheory.RSCell.locFac q α x ν := by
  first | exact @GlobalTheory.RSCell.locFac_eq_wtS_sphZ | exact GlobalTheory.RSCell.locFac_eq_wtS_sphZ | (intros; apply GlobalTheory.RSCell.locFac_eq_wtS_sphZ <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

theorem _root_.GlobalTheory.T.exists_level_nat_bump_rankinSelbergCell : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))),
    (∀ w ∈ S, ∀ w' : HeightOneSpectrum (𝓞 E), Ideal.comap (algebraMap ℤ (𝓞 E)) w'.asIdeal =
      Ideal.comap (algebraMap ℤ (𝓞 E)) w.asIdeal → w' ∈ S) →
    ∀ V : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (V : Set (GL (Fin (m + 1)) (Af E))) →
    (∀ w ∉ S, ∀ k ∈ KGL w (n := (m + 1)), locGL E (m + 1) w k ∈ V) →
    ∃ (N : ℕ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (Φ : (Fin (m + 1) → Cinf E) → ℂ), 0 < N ∧
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧ tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) ∧
      (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) ∧ Φ (Pi.single (Fin.last m) 1) ≠ 0 ∧
      (∀ v ∈ S, 0 < FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)) ∧
      GlobalTheory.RSLocalPart.levelAt (m + 1) S J ⊆ V ∧
      (∀ z ∈ GlobalTheory.RSJ.natLat E N, ∀ v : HeightOneSpectrum (𝓞 E), z v ∈ v.adicCompletionIntegers E) ∧
      (∀ z ∈ GlobalTheory.RSJ.natLat E N, ∀ v ∈ S,
        Valued.v (z v) ≤ WithZero.exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E))) ∧
      (∀ z z' : Af E, (∀ v ∈ S, z v = z' v) → (∀ v ∉ S, z v ∈ v.adicCompletionIntegers E) →
        (∀ v ∉ S, z' v ∈ v.adicCompletionIntegers E) → (z ∈ GlobalTheory.RSJ.natLat E N ↔ z' ∈ GlobalTheory.RSJ.natLat E N)) := by
  first | exact @GlobalTheory.RSParams.exists_level_nat_bump | exact GlobalTheory.RSParams.exists_level_nat_bump | (intros; apply GlobalTheory.RSParams.exists_level_nat_bump <;> assumption)
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped nonZeroDivisors ComplexConjugate


theorem _root_.GlobalTheory.T.isFundamentalDomain_det_shell_latticeGL : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 0 < a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → IsFundamentalDomain (latticeGL E a) (𝓕 ∩ {g | Real.exp (-((a : ℝ) * (Module.finrank ℚ E : ℝ))) < (ideleModule E (GeneralLinearGroup.det g) : ℝ) ∧ (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}) μ := by
  first | (exact @GlobalTheory.ShellFD.isFundamentalDomain_shell) | (exact GlobalTheory.ShellFD.isFundamentalDomain_shell) | (intros; apply GlobalTheory.ShellFD.isFundamentalDomain_shell  <;> assumption)
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglandsBridge

theorem localLanglandsGL_of_depthZero_zelevinsky_bernstein : LocalLanglandsExists → LocalConverseGL → DepthZeroCuspidalLL → DepthZeroInduction →
    BrauerDegreeZero → ChevalleyUnits → GlobalArtinReciprocity → LanglandsExhaustionGL → LanglandsMultisegments →
    StandardCosocleGL → ZelevinskyPolynomialRing → GeometricLemma → BernsteinZelevinskyFiniteness → LocalLanglandsGL := by
  intro hEx hConv hDep hInd hBr hChev hArt hExh hMult hCos hZel hGeo hBZ
  have hRec := GlobalTheory.T.rec_of_rec_literal hDep hInd hExh hMult hCos hZel hGeo hBZ
  have hComp := GlobalTheory.T.local_langlands_transport hArt hChev hBr hEx hConv hExh hBZ
  refine ⟨?_, ?_⟩
  · intro E Ω _ _ _ _ _ A w h
    obtain ⟨rc, hrc⟩ := hEx E Ω A w h
    refine ⟨rc, hRec E Ω A w h rc hrc, ?_⟩
    intro rc' hrc'
    funext x
    obtain ⟨n, c⟩ := x
    have hC := hComp E Ω A w h E Ω A w h rc' rc hrc'.toLit hrc
      (RingEquiv.refl Ω) (RingHom.id E) (RingEquiv.refl _) (fun _ => Iff.rfl) (fun _ => rfl) continuous_id
      (fun _ => rfl) n c.rep c.rep (LinearEquiv.refl ℂ _) (fun g v => by
        have hg : GeneralLinearGroup.map (RingEquiv.refl (w.adicCompletion E)).toRingHom g = g :=
          Units.ext (Matrix.ext fun _ _ => rfl)
        rw [hg]; rfl)
    obtain ⟨b, b', hb, hb', hN, hρ⟩ := hC
    have hbb : WD.mk b = WD.mk b' := WD.sound ⟨LinearEquiv.refl ℂ _, fun σ v => by
      simp only [LinearEquiv.refl_apply]; rw [hρ σ σ (fun _ => rfl)], fun v => by
      simp only [LinearEquiv.refl_apply]; rw [hN]⟩
    have hx : (⟨n, c⟩ : IrrGL (k := w.adicCompletion E)) = cls c.rep := congrArg (Sigma.mk _) c.cl_rep.symm
    rw [hx, ← hb, ← hb', hbb]
  · intro E Ω _ _ _ _ _ A w h E' Ω' _ _ _ _ _ A' w' h' rc rc' hrc hrc'
    exact hComp E Ω A w h E' Ω' A' w' h' rc rc' hrc.toLit hrc'.toLit

end GlobalTheory.LocLanglandsBridge
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

theorem _root_.GlobalTheory.T.adelicCharacter_factor_primitive_on_idempotentSum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (Q : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Q → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → (∀ Z : AE D, e * Z = Z → (toEAf D Z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ ∀ Z' : AE D, e * Z' = Z' → toEAf D Z' ∈ Formalism.L2.Herm.intAf D.host.F D.host.E → ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * (Z * Z'))) = 1)) → ∃ ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ, (∀ PP ∈ Q, (ψP PP).IsPrimitive) ∧ ∀ Z : AE D, e * Z = Z → ∀ h : toEAf D (incA D (ϖ : D.host.E) * Z) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * Z)) = ∏ PP ∈ Q.attach, ψP PP.1 (resS D.host.F PP.1 ⟨toEAf D (incA D (ϖ : D.host.E) * Z), h⟩) := by
  first | exact @GlobalTheory.IdemCharLift.factor_prim | exact GlobalTheory.IdemCharLift.factor_prim | (intros; apply GlobalTheory.IdemCharLift.factor_prim <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

theorem _root_.GlobalTheory.T.frameMatrix_integral_iff_uniformiser_multiple_on_half : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (Q : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Q → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∀ x : WO S T, IsHalf e x → (IsIntM (frMapO S T βS βT x) ↔ IsIntM (frMapO S T βS βT (x.map fun w => incA D (ϖ : D.host.E) * w)) ∧ ∀ PP ∈ Q, redM PP (frMapO S T βS βT (x.map fun w => incA D (ϖ : D.host.E) * w)) = 0) := by
  first | exact @GlobalTheory.HalfUniInt.half_int_iff | exact GlobalTheory.HalfUniInt.half_int_iff | (intros; apply GlobalTheory.HalfUniInt.half_int_iff <;> assumption)
end

module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle043
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfAeFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinTensAlgebraMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle048
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle049
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle052
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1510
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1709
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1861
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1862
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermCColMulVec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1779
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1786
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1840
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle186
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartPhiE
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSplit
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle005
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelSpanOverClasses
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

@[expose] public section

section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.ShortSeries

section Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}

theorem heisG_smul (y : Matrix (Fin n) (Fin r) E) (c : ℂ) (φ : TF n g) :
    heisG X bas y (c • φ) = c • heisG X bas y φ := by
  funext x
  simp only [heisG, heisS, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem projA_smul (w : E) (A : AddSubgroup (Matrix (Fin n) (Fin r) E)) (a : ℂ) (φ : TF n g) :
    projA X bas w A (a • φ) = a • projA X bas w A φ := by
  by_cases ha : a = 0
  · subst ha
    have h0 : ∀ y : Matrix (Fin n) (Fin r) E, heisG X bas y (0 : TF n g) = 0 := fun y => by
      have := heisG_smul (X := X) (bas := bas) y 0 (0 : TF n g)
      rwa [zero_smul, zero_smul] at this
    rw [zero_smul, zero_smul, projA, finsum_mem_eq_zero_of_forall_eq_zero, smul_zero]
    rintro _ ⟨y, -, rfl⟩
    simp only [h0, smul_zero]
  have hi : Function.Injective fun ψ : TF n g => a • ψ := smul_right_injective _ ha
  have e : (fun y => epsW X w y • heisG X bas y (a • φ)) '' A =
      (fun ψ : TF n g => a • ψ) '' ((fun y => epsW X w y • heisG X bas y φ) '' A) := by
    rw [Set.image_image]
    congr 1
    funext y
    rw [heisG_smul, smul_comm]
  unfold projA
  rw [e, Set.ncard_image_of_injective _ hi, finsum_mem_image hi.injOn, smul_comm a]
  congr 1
  rw [smul_finsum]
  simp only [smul_finsum]

theorem theta_smul₂ (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) (hn : Even n) {q0 : ℕ} (hq : X.p0 + q0 = r)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) (c : ℂ) (φ : TF n g) (h : GlobalTheory.SW.IsSB (c • φ))
    (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) : thP X hq bas idx (c • φ) P x = c * thP X hq bas idx φ P x := by
  have key : ∀ (a : ℂ) (ψ : TF n g), GlobalTheory.SW.IsSB ψ → thP X hq bas idx (a • ψ) P x = a * thP X hq bas idx ψ P x := by
    intro a ψ hψ
    have := (theta_bilinear_heisenberg E r g n X bas idx hs hn q0 hq x hx ψ hψ P).1 ψ hψ a 0
    rwa [zero_smul, add_zero, zero_mul, add_zero] at this
  by_cases hc : c = 0
  · have := key 0 _ h
    rw [zero_smul] at this
    rw [hc, zero_smul, this, zero_mul, zero_mul]
  · refine key c φ ?_
    have := (isSB_algebra_haar_linear ℚ _ _ _ _ h h).2.1 c⁻¹
    rwa [inv_smul_smul₀ hc] at this

theorem finite_levQ {H : Geo.Tor.Host E} (Dw : Datum H) (l : Geo.Tor.Level H) : Finite (LevQ Dw l) := by
  have hM : l.Mb ≠ ⊥ := by
    intro h
    have h₁ := l.prod
    rw [h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot] at h₁
    have h₂ : l.M = 0 := by exact_mod_cast h₁
    have := l.three_le
    omega
  have := l.Mb.finiteQuotientOfFreeOfNeBot hM
  have := Dw.fin
  exact Submodule.finite_quotient_smul l.Mb (N := (⊤ : Submodule (𝓞 E) Dw.La)) Module.Finite.fg_top

theorem cmHost_idempotent_trace_eq_one (H : Geo.Tor.Host E) : (H.w0 : E) + cc (H.w0 : E) = 1 := by
  rw [cc, ← H.bar_eq]
  exact_mod_cast congrArg (fun t : 𝓞 E => (t : E)) (PullbackSections.CVA.cmHostUnit_add_conj_eq_one H)

end Classical

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D} {r g : ℕ}

theorem isInvOf_move (hr : W.rank = r) (X : Data D.host.E r) {x : Frame X.Ψ r}
    {s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ} (hs : IsInvOf W hr X x s) (k : GA D W) :
    IsInvOf W hr X (frMove θ W hr X k x)
      fun τ => compAt θ τ (Formalism.L2.Theta.mt W k) * s τ * compAt θ τ (Formalism.L2.Theta.mt W k⁻¹) := by
  subst hr
  intro ρ τ hτ
  have h := hs ρ τ hτ
  have e : mat (frMove θ W rfl X k x) τ = compAt θ ρ (Formalism.L2.Theta.mt W k) * mat x τ := by
    rw [← RealCoord.realM_tauE, ← hτ]
    rfl
  change s ρ * mat x τ = _ at h
  change (compAt θ ρ (Formalism.L2.Theta.mt W k) * s ρ * compAt θ ρ (Formalism.L2.Theta.mt W k⁻¹)) * _ = _
  rw [e, Matrix.mul_assoc, ← Matrix.mul_assoc (compAt θ ρ (Formalism.L2.Theta.mt W k⁻¹)),
    GlobalTheory.WeilVacMove.compAt_mt_inv_mul, Matrix.one_mul, Matrix.mul_assoc, h, Matrix.mul_neg, Matrix.mul_assoc]

theorem isBasOf_move (hr : W.rank = r) (X : Data D.host.E r) {q0 : ℕ} (hq : X.p0 + q0 = r) {x : Frame X.Ψ r}
    {B : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ} (hB : IsBasOf W hr X hq x B) (k : GA D W) :
    IsBasOf W hr X hq (frMove θ W hr X k x) fun τ => compAt θ τ (Formalism.L2.Theta.mt W k) * B τ := by
  subst hr
  intro ρ τ hτ j i a hi
  have e : mat (frMove θ W rfl X k x) τ = compAt θ ρ (Formalism.L2.Theta.mt W k) * mat x τ := by
    rw [← RealCoord.realM_tauE, ← hτ]
    rfl
  refine Eq.trans ?_ (congrFun (congrFun e a) (rowIdx hq j)).symm
  simp only [Matrix.mul_apply]
  exact Finset.sum_congr rfl fun b _ => congrArg _ (hB ρ τ hτ j i b hi)

theorem isONFr_move (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (hV : V.gram = 1) (he : Even V.rank) (hr : W.rank = r)
    (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (hM : IsMod W hr X)
    (hS : IsSympl X bas) {x : Frame X.Ψ r} (hx : IsONFr X x) (k : GA D W) : IsONFr X (frMove θ W hr X k x) := by
  subst hr
  obtain ⟨X', m, hq', hq, bas', idx', hs, -, -, -, -, -, -, hfr⟩ :=
    GlobalTheory.T.orthonormal_frame_reading_eq_conjugate_datum_theta D ψ θ V W g X bas idx hψ hθ he hV hM hS
  obtain ⟨⟨B, hB⟩, hBx⟩ := hfr x hx
  obtain ⟨-, -, -, -, -, -, -, hmv, -⟩ := hBx B hB
  exact (hmv k).1

theorem reads_sum (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (hV : V.gram = 1) (he : Even V.rank) (hr : W.rank = r)
    (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (hM : IsMod W hr X)
    (hS : IsSympl X bas) {x : Frame X.Ψ r} (hx : IsONFr X x) {f : WO V W → ℂ} {φ : TF V.rank g}
    (hf : IsThetaFunO ψ V W f) (hR : Reads θ V W hr X bas idx f φ x) {Q : Type} (c : Q → ℂ)
    (γ : Q → Matrix (Fin W.rank) (Fin V.rank) D.host.E) (u : Q → WO V W) (hu : ∀ q, IsFinOf V W (γ q) (u q))
    (s : Finset Q) :
    IsThetaFunO ψ V W (∑ q ∈ s, c q • heisO ψ V W (u q) f) ∧
      Reads θ V W hr X bas idx (∑ q ∈ s, c q • heisO ψ V W (u q) f)
        (∑ q ∈ s, c q • heisG X bas (-(colsR hr (γ q))) φ) x := by
  have hlin := reads_linear_injective D ψ θ V W r g hr X bas idx hψ hθ hV he hM hS x hx
  induction s using Finset.induction_on with
  | empty =>
    have := (hlin _ _ _ _ hR hR).1 0 0
    simp only [zero_smul, add_zero] at this
    exact ⟨GlobalTheory.OrientedHeis.theta_zero, this⟩
  | insert q s hq ih =>
    rw [Finset.sum_insert hq, Finset.sum_insert hq]
    have h1 := reads_heisO_finOf D ψ θ V W r g hr X bas idx hψ hθ hV he hM hS x hx f φ hf hR _ _ (hu q)
    have := (hlin _ _ _ _ h1 ih.2).1 (c q) 1
    rw [one_smul, one_smul] at this
    exact ⟨GlobalTheory.OrientedHeis.theta_add (GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.FinTranslate.isThetaFunO_heisO hψ.1.1 hψ.1.2.1 hf (hu q).1)) ih.1, this⟩

theorem kernel_of_reads {χV χW : (AE D)ˣ →* Circle} {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}
    (hP : IsPair ψ θ V W χV χW om) (hr : W.rank = r)
    (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (hM : IsMod W hr X)
    (hS : IsSympl X bas) {q0 : ℕ} (hq : X.p0 + q0 = r) {x : Frame X.Ψ r} (hx : IsONFr X x)
    {s B : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ} (hs : IsInvOf W hr X x s) (hB : IsBasOf W hr X hq x B)
    {vr : Harm.Var X.Ψ q0 X.p0 (Fin V.rank) ≃ FVar D W.rank V.rank} (hvr : IsVarOf V W X q0 vr)
    {h : GA D V} (hh : h ∈ GfC V) (k : GA D W) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) {φ : TF V.rank g}
    (hR : Reads θ V W hr X bas idx (om (h, k) f) φ (frMove θ W hr X k x))
    (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin V.rank)) (d : ℕ) (hd : P.IsHomogeneous d) :
    thetaKO om h k (pureTensorO ψ θ V W (fun _ => 1) s (fun _ => 1) B f (MvPolynomial.rename vr P)) =
      ((Real.sqrt (2 * Real.pi * xiR D) : ℝ) : ℂ)⁻¹ ^ d * thP X hq bas idx φ P (frMove θ W hr X k x) := by
  have h1 := (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ V W χV χW om hP.weil hP.inf (fun _ => 1) (fun _ => 1) (fun _ => 1)
    (fun _ => 1) s (fun τ => compAt θ τ (Formalism.L2.Theta.mt W k) * s τ * compAt θ τ (Formalism.L2.Theta.mt W k⁻¹)) B
    (fun τ => compAt θ τ (Formalism.L2.Theta.mt W k) * B τ) h k
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one])
    (fun τ => by rw [Matrix.mul_assoc, GlobalTheory.WeilVacMove.compAt_mt_inv_mul, Matrix.mul_one])
    (fun τ => by rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ V hh, Matrix.mul_one]) (fun _ => rfl) f hf
    (MvPolynomial.rename vr P)).2
  rw [thetaKO, h1]
  exact GlobalTheory.T.fock_pure_tensor_at_origin_eq_theta_series D ψ θ V W r g hr X bas idx hP.weil.std hP.inf hP.std hP.even hM hS q0 hq _ _ _ vr
    (isONFr_move hP.weil.std hP.inf hP.std hP.even hr X bas idx hM hS hx k) (isInvOf_move hr X hs k)
    (isBasOf_move hr X hq hB k) hvr _ φ (hP.weil.om_pres _ _ hf) hR P d hd

theorem exists_finOf (V W : HSp D) (hr : W.rank = r) (y : Matrix (Fin V.rank) (Fin r) D.host.E) :
    ∃ p : Matrix (Fin W.rank) (Fin V.rank) D.host.E × WO V W, colsR hr p.1 = y ∧ IsFinOf V W p.1 p.2 := by
  subst hr
  exact ⟨(yᵀ, GlobalTheory.LatVac.finTens 1 yᵀ), rfl, (GlobalTheory.VacSign.isFinOf_iff _ _).2 rfl⟩


end GlobalTheory.AdTh.ShortSeries
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx.PeriodicClassFixedPoints

variable {p : ℕ} [Fact p.Prime]

theorem sh_mul' (G : HTGroup p) (a b : G.C) : sh G (a * b) = sh G b * sh G a := by
  simp only [sh, map_mul, MulOpposite.unop_mul]

theorem sh_one' (G : HTGroup p) : sh G 1 = 1 := by simp [sh]

theorem sh_mul_inv' (G : HTGroup p) (e : G.Cˣ) : sh G (e : G.C) * sh G ((e⁻¹ : G.Cˣ) : G.C) = 1 := by
  rw [← sh_mul', Units.inv_mul, sh_one']

theorem commute_ratio (G : HTGroup p) (β β₁ γ : G.Cˣ) (c : ℚ) (hc : c ≠ 0)
    (h : (γ : G.C) * β * sh G γ = algebraMap ℚ G.C c * β)
    (h₁ : (γ : G.C) * β₁ * sh G γ = algebraMap ℚ G.C c * β₁) :
    Commute ((β : G.C) * ((β₁⁻¹ : G.Cˣ) : G.C)) (γ : G.C) := by
  have hs : sh G γ = ((β₁⁻¹ : G.Cˣ) : G.C) * ((γ⁻¹ : G.Cˣ) : G.C) * (algebraMap ℚ G.C c * β₁) := by
    rw [← h₁]; simp [mul_assoc]
  rw [hs, ← Algebra.smul_def, ← Algebra.smul_def] at h
  simp only [mul_smul_comm] at h
  have h2 : (γ : G.C) * β * (((β₁⁻¹ : G.Cˣ) : G.C) * ((γ⁻¹ : G.Cˣ) : G.C) * β₁) = β := smul_right_injective G.C hc h
  have h3 : (γ : G.C) * β * ((β₁⁻¹ : G.Cˣ) : G.C) * ((γ⁻¹ : G.Cˣ) : G.C) = β * ((β₁⁻¹ : G.Cˣ) : G.C) := by
    conv_rhs => rw [← h2]
    simp [mul_assoc]
  show (β : G.C) * ((β₁⁻¹ : G.Cˣ) : G.C) * γ = γ * (β * ((β₁⁻¹ : G.Cˣ) : G.C))
  calc (β : G.C) * ((β₁⁻¹ : G.Cˣ) : G.C) * γ
      = ((γ : G.C) * β * ((β₁⁻¹ : G.Cˣ) : G.C) * ((γ⁻¹ : G.Cˣ) : G.C)) * γ := by rw [h3]
    _ = γ * (β * ((β₁⁻¹ : G.Cˣ) : G.C)) := by simp [mul_assoc]

theorem tau_ratio (G : HTGroup p) (β β₁ : G.Cˣ) (h : sh G β = β) (h₁ : sh G β₁ = β₁) :
    (β₁ : G.C) * sh G ((β : G.C) * ((β₁⁻¹ : G.Cˣ) : G.C)) * ((β₁⁻¹ : G.Cˣ) : G.C) =
      (β : G.C) * ((β₁⁻¹ : G.Cˣ) : G.C) := by
  have e : (β₁ : G.C) * sh G ((β₁⁻¹ : G.Cˣ) : G.C) = 1 := by
    conv_lhs => rw [← h₁]
    exact sh_mul_inv' G β₁
  rw [sh_mul', h, ← mul_assoc, e, one_mul]

theorem rel_of_same (G : HTGroup p) (β₁ γ₀ : G.Cˣ) (a₀ : G.C) (P Q : Pair G) (hP : P.γ = γ₀) (hQ : Q.γ = γ₀)
    (r r' : ℚˣ) (e e' : G.Cˣ) (he : Commute (e : G.C) γ₀) (he' : Commute (e' : G.C) γ₀)
    (hr : (0 < (r : ℚ)) ↔ (0 < (r' : ℚ)))
    (hPβ : (P.β : G.C) = algebraMap ℚ G.C r * ((e : G.C) * a₀ * β₁ * sh G (e : G.C)))
    (hQβ : (Q.β : G.C) = algebraMap ℚ G.C r' * ((e' : G.C) * a₀ * β₁ * sh G (e' : G.C))) : Pair.Rel P Q := by
  refine ⟨e' * e⁻¹, (r' : ℚ) / r, ?_, ?_, ?_⟩
  · rcases lt_or_gt_of_ne r.ne_zero with h | h
    · have hn : ¬ (0 < (r' : ℚ)) := fun h0 => absurd (hr.2 h0) (not_lt.2 h.le)
      exact div_pos_of_neg_of_neg (lt_of_le_of_ne (not_lt.1 hn) r'.ne_zero) h
    · exact div_pos (hr.1 h) h
  · rw [hQβ, hPβ, ← Algebra.smul_def, ← Algebra.smul_def, ← Algebra.smul_def]
    simp only [mul_smul_comm, smul_mul_assoc, smul_smul]
    have hrr : (r' : ℚ) / r * r = r' := by field_simp
    rw [hrr]
    congr 1
    rw [Units.val_mul, sh_mul']
    calc (e' : G.C) * a₀ * β₁ * sh G (e' : G.C)
        = (e' : G.C) * (((e⁻¹ : G.Cˣ) : G.C) * e) * a₀ * β₁ * (sh G (e : G.C) * sh G ((e⁻¹ : G.Cˣ) : G.C)) * sh G (e' : G.C) := by
          rw [Units.inv_mul, sh_mul_inv', mul_one, mul_one]
      _ = _ := by simp only [mul_assoc]
  · have hc : Commute ((e' * e⁻¹ : G.Cˣ) : G.C) (γ₀ : G.C) := by
      rw [Units.val_mul]; exact he'.mul_left he.units_inv_left
    ext
    rw [hP, hQ, Units.val_mul, Units.val_mul, hc.eq, mul_assoc, Units.mul_inv, mul_one]

theorem exists_point_of_term_ne_zero' {G : HTGroup p} (P : Pair G) (Kf : Subgroup G.GAf)
    (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ) (h : P.term Kf f r K φ ≠ 0) :
    ∃ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (g : G.GAf),
      f (g⁻¹ * P.toAf x t hx P.self * g) ≠ 0 := by
  unfold Pair.term at h
  split_ifs at h with hd
  · unfold Pair.termAt pointSum at h
    obtain ⟨q, hq⟩ := not_forall.1 (fun hc => h (finsum_eq_zero_of_forall_eq_zero hc))
    refine ⟨_, _, P.trivAf.choose_spec.choose_spec, (Quotient.out q).1, fun h0 => hq ?_⟩
    rw [h0, zero_mul, mul_zero]
  · exact absurd rfl h

theorem finite_fixed (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ)
    (hf : IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f) (hreg : ∀ g, f g ≠ 0 → RegAf G g)
    (γ₀ : G.Cˣ) (c₀ : ℚˣ) :
    {q : Cls G | ∃ P : Pair G, (Quot.mk Pair.Rel P : Cls G) = q ∧ P.γ = γ₀ ∧ P.c = c₀ ∧
      ∃ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (g : G.GAf),
        f (g⁻¹ * P.toAf x t hx P.self * g) ≠ 0}.Finite := by
  by_cases hne : ∃ P₁ : Pair G, P₁.γ = γ₀ ∧ P₁.c = c₀
  swap
  · refine Set.finite_empty.subset ?_
    rintro q ⟨P, -, hγ, hc, -⟩
    exact hne ⟨P, hγ, hc⟩
  obtain ⟨P₁, rfl, rfl⟩ := hne
  obtain ⟨S, hS⟩ := GlobalTheory.T.kottwitzPair_form_ratio_local_scalar_norm p G L f hf hreg P₁
  obtain ⟨A, hA⟩ := GlobalTheory.T.finite_fixed_unit_classes_centralizer_regular p G P₁.β P₁.sym P₁.γ P₁.c P₁.sim P₁.reg.2 P₁.reg.1 S
  let D : G.C × Bool → Pair G → Prop := fun ab P => P.γ = P₁.γ ∧ ∃ (r : ℚˣ) (e : G.Cˣ),
    Commute (e : G.C) P₁.γ ∧ decide (0 < (r : ℚ)) = ab.2 ∧
    (P.β : G.C) = algebraMap ℚ G.C r * ((e : G.C) * ab.1 * P₁.β * sh G (e : G.C))
  let ρ : G.C × Bool → Cls G := fun ab => if h : ∃ P, D ab P then Quot.mk _ h.choose else Quot.mk _ P₁
  refine (Finset.finite_toSet ((A ×ˢ (Finset.univ : Finset Bool)).image ρ)).subset ?_
  rintro q ⟨P, rfl, hγ, hc, x, t, hx, g, hg⟩
  have hcomm := commute_ratio G P.β P₁.β P₁.γ P₁.c P₁.c.ne_zero (by rw [← hγ, ← hc]; exact P.sim) P₁.sim
  have hτ := tau_ratio G P.β P₁.β P.sym P₁.sym
  have hu : IsUnit ((P.β : G.C) * ((P₁.β⁻¹ : G.Cˣ) : G.C)) := by
    simpa using (P.β * P₁.β⁻¹).isUnit
  obtain ⟨a₀, ha₀, r, e, he, hre⟩ := hA _ hu hcomm hτ (fun ℓ _ hℓ => hS P hγ hc x t hx g hg ℓ hℓ)
  have hβeq : (P.β : G.C) = algebraMap ℚ G.C r * ((e : G.C) * a₀ * P₁.β * sh G (e : G.C)) := by
    calc (P.β : G.C) = ((P.β : G.C) * ((P₁.β⁻¹ : G.Cˣ) : G.C)) * P₁.β := by simp [mul_assoc]
      _ = _ := by rw [hre]; simp [mul_assoc]
  have hex : ∃ P', D (a₀, decide (0 < (r : ℚ))) P' := ⟨P, hγ, r, e, he, rfl, hβeq⟩
  refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨(a₀, decide (0 < (r : ℚ))),
    Finset.mem_product.2 ⟨ha₀, Finset.mem_univ _⟩, ?_⟩)
  have hρ : ρ (a₀, decide (0 < (r : ℚ))) = Quot.mk _ hex.choose := dif_pos hex
  rw [hρ]
  obtain ⟨hγ', r', e', he', hb', hβ'⟩ := hex.choose_spec
  refine Quot.sound (rel_of_same G P₁.β P₁.γ a₀ _ P hγ' hγ r' r e' e he' he ?_ hβ' hβeq)
  rw [← decide_eq_decide]; exact hb'

theorem finite_classes_of_pol_a_one : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → (∀ g, f g ≠ 0 → RegAf G g) → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ P0 : Polynomial G.F, {q : Cls G | (Quot.out q).pol = P0 ∧ (∃ μ, (Quot.out q).Mark μ) ∧ (Quot.out q).term L.K.toSubgroup f 1 K' f' ≠ 0}.Finite := by
  intro p _ G _ L f hf hreg K' f' _ P0
  by_cases hne : {q : Cls G | (Quot.out q).pol = P0 ∧ (∃ μ, (Quot.out q).Mark μ) ∧
      (Quot.out q).term L.K.toSubgroup f 1 K' f' ≠ 0}.Nonempty
  · obtain ⟨q₀, hq₀⟩ := hne
    refine ((finite_fixed G L f hf hreg (Quot.out q₀).γ (Quot.out q₀).c).union
      (finite_fixed G L f hf hreg (Quot.out q₀).γ (-(Quot.out q₀).c))).subset ?_
    intro q hq
    obtain ⟨x, t, hx, g, hg⟩ := exists_point_of_term_ne_zero' _ _ _ _ _ _ hq.2.2
    obtain ⟨y, hy⟩ := GlobalTheory.LKCx.ClsReg.units_conj_of_minpoly_eq_of_separable G (Quot.out q).γ (Quot.out q₀).γ
      (hq.1.trans hq₀.1.symm) (Quot.out q₀).reg.2 (Quot.out q₀).reg.1
    obtain ⟨P', hrel, hγ, -, htr⟩ := GlobalTheory.LKMid.Pair.exists_conj p G (Quot.out q) y⁻¹
    obtain ⟨x', hx', he⟩ := htr x t hx
    have hq' : (Quot.mk Pair.Rel P' : Cls G) = q := by
      rw [← Quot.sound hrel]; exact Quot.out_eq q
    have hγ' : P'.γ = (Quot.out q₀).γ := by
      rw [hγ]; ext
      rw [Units.val_mul, Units.val_mul, hy]
      simp [mul_assoc]
    have hg' : f (g⁻¹ * P'.toAf x' t hx' P'.self * g) ≠ 0 := by rw [he]; exact hg
    rcases GlobalTheory.LKMid.Pair.c_eq_or_eq_neg p G (Quot.out q₀) P' hγ' with hc | hc
    · exact Or.inl ⟨P', hq', hγ', hc, x', t, hx', g, hg'⟩
    · exact Or.inr ⟨P', hq', hγ', hc, x', t, hx', g, hg'⟩
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne]; exact Set.finite_empty

end GlobalTheory.LKCx.PeriodicClassFixedPoints
end
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

theorem _root_.GlobalTheory.T.curvaturePowerSum_transgression_isForm : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (r : Type) [Fintype r] [DecidableEq r] (G G' : M → M → Matrix r r ℂ), IsGramPair A G G' → ∀ k, A.IsForm (fld A (powFld A G k)) ∧ A.IsForm (transFld A G G' k) := by
  first | exact @GlobalTheory.ChernCalc.PairForm.isForm_pow_trans | exact GlobalTheory.ChernCalc.PairForm.isForm_pow_trans | (intros; apply GlobalTheory.ChernCalc.PairForm.isForm_pow_trans <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

theorem _root_.GlobalTheory.T.flag_graded_metrics_weights_on_line_bundles : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m : ι → ℕ) (E : Fr (ratOf X) m m) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ) (gr : Root m → X.Dv), IsGraded E gr → IsMetricFr E H → ∀ x : Root m, ∃ (L : LB X.X) (r : L.ι → X.Fnˣ) (ψ : Weight X.str σ L), Presents (gr x) L r ∧ ψ.IsCInf ∧ c1W ψ = grF E H x := by
  first | exact @GlobalTheory.ChernCalc.graded_weight | exact GlobalTheory.ChernCalc.graded_weight | (intros; apply GlobalTheory.ChernCalc.graded_weight <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

theorem _root_.GlobalTheory.T.hilbertSamuelDegreeZeroResidues_range_eq_top : Quoted → ∀ (K : Type) [Field K] [NumberField K] (X : Data K) (s : Fin X.D → Fin X.N → K) (hs : X.IsGood s) (δ : ℕ) (Co : Coord X.toGeo hs δ), IsNef K X.L₂ → IsBig K X.L₂ → (LinearMap.range (incl X 0)).map (totRes Co) = ⊤ := by
  first | exact @GlobalTheory.HSShort.map_totRes_range_incl_zero | exact GlobalTheory.HSShort.map_totRes_range_incl_zero | (intros; apply GlobalTheory.HSShort.map_totRes_range_incl_zero <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

theorem _root_.GlobalTheory.T.twisted_kernel_class_scalar_integral : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)) (N : ℕ), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (e : AE D) (Ps : Finset (Pl D.host.E)) (yd : (AE D)ˣ), h ∈ GfC (Vc D i) → IsIdemSum e Ps → (∀ PP ∈ Ps, ((badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → SuppAt e (Vc D i) h → IsDetAt e (Vc D i) h yd → Nat.card (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂) ≠ 0 → ∀ a : D.what₂.LL, D.what₂.embLL a = (((O i).s0 (betaH (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ))⁻¹ * (((Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 yd : Circle) : ℂ) * (Real.sqrt ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℝ) ^ D.R.r) : ℂ)) → ∀ lam : HeightOneSpectrum (𝓞 D.what₂.LL), Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) → ∃ s : 𝓞 D.what₂.LL, s ∉ lam.asIdeal ∧ IsIntegral ℤ ((s : D.what₂.LL) * a) := by
  first | exact @GlobalTheory.ClassScalarIntegral.class_scalar_integral | exact GlobalTheory.ClassScalarIntegral.class_scalar_integral | (intros; apply GlobalTheory.ClassScalarIntegral.class_scalar_integral <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LocPlSplit

theorem nonempty_of_not_isConjPl {D : D7} {w : HeightOneSpectrum (𝓞 D.host.E)}
    (h : ¬ Formalism.IndefR.Lev.IsConjPl (D := D) w w) :
    Nonempty (D.host.E →ₐ[D.host.F] Fv D.host.F (w.under (𝓞 D.host.F))) := by
  obtain ⟨-, ι, -⟩ := Formalism.IndefR.Fin.idem_data w h (w.under (𝓞 D.host.F)) rfl
  exact ⟨ι⟩

theorem locPl_split : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (w : HeightOneSpectrum (𝓞 D.host.E)), w ∈ locPl G t →
      Nonempty (D.host.E →ₐ[D.host.F] Fv D.host.F (w.under (𝓞 D.host.F))) := by
  intro D T L sc G μ₀ hL t w hw
  refine nonempty_of_not_isConjPl ?_
  rcases Finset.mem_union.1 hw with h | h
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
    obtain ⟨e, he⟩ := G.pl.w_split v hv
    exact Formalism.IndefR.Fin.idemAt_split he
  · exact (hL.Q_pl t w h).2 w h

end GlobalTheory.LocPlSplit
end

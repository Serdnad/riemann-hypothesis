module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle385
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle226
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle320
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle386
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefIntegralEq
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle343
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle392
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle187
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle345
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle349
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelOfDualParameter
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle006
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle394
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle393
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace ENNReal NNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift GlobalTheory.Size GlobalTheory.Grow GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift

namespace GlobalTheory.PairLift.LowAllPf

variable {D : D7}

section Kernel

variable {V W : HSp D} (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (g : GA D V) (h : GA D W)

theorem kernel_zero : thetaKO ω g h 0 = 0 := by simp [thetaKO]

theorem kernel_add (f f' : WO V W → ℂ) : thetaKO ω g h (f + f') = thetaKO ω g h f + thetaKO ω g h f' := by
  simp [thetaKO, map_add (f := _)]

theorem kernel_sub (f f' : WO V W → ℂ) : thetaKO ω g h (f - f') = thetaKO ω g h f - thetaKO ω g h f' := by
  simp [thetaKO, map_sub]

theorem kernel_smul (c : ℂ) (f : WO V W → ℂ) : thetaKO ω g h (c • f) = c * thetaKO ω g h f := by
  simp [thetaKO, map_smul]

end Kernel

theorem multT_apply_smooth_cusp {W : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel W S)
    (J : Set (GA D W)) (χ : GA D W → ℂ) (F : SmT M →ₗ[ℂ] (GA D W → ℂ)) (hF : F ∈ MultT θ M J χ) (v : SmT M) :
    IsAutFunSm θ W (F v) ∧ IsCuspFun W (F v) := by
  obtain ⟨T, hT, rfl⟩ := hF
  have hT' := (GlobalTheory.MultMem.mem_mult_iff D θ W S M J χ T).1 hT
  induction v using PiTensorProduct.induction_on with
  | smul_tprod c w =>
    simp only [map_smul, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod]
    exact ⟨GlobalTheory.MultMem.isAutFunSm_smul c (hT'.aut w), GlobalTheory.MultMem.isCuspFun_smul c (hT'.cusp w)⟩
  | add x y hx hy =>
    rw [map_add (f := _)]
    exact ⟨GlobalTheory.MultMem.isAutFunSm_add hx.1 hy.1,
      GlobalTheory.MultMem.isCuspFun_add hx.1.toIsAutFun hy.1.toIsAutFun hx.2 hy.2⟩

theorem liftInt_span_zero {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {ν : Measure (GA D W)} {𝓕 : Set (GA D W)} {Φ : GA D W → ℂ}
    (hI : ∀ f, IsThetaFunO ψ V W f → ∀ x, IntegrableOn (fun h => thetaKO ω x h f * Φ h) 𝓕 ν)
    {s : Set (WO V W → ℂ)} (hs : ∀ g ∈ s, IsThetaFunO ψ V W g ∧ Lift.liftInt ν 𝓕 (thetaKO ω) g Φ = 0) :
    ∀ g ∈ Submodule.span ℂ s, IsThetaFunO ψ V W g ∧ Lift.liftInt ν 𝓕 (thetaKO ω) g Φ = 0 := by
  intro g hg
  induction hg using Submodule.span_induction with
  | mem g hg => exact hs g hg
  | zero =>
    refine ⟨GlobalTheory.OrientedHeis.theta_zero, funext fun x => ?_⟩
    simp [Lift.liftInt, kernel_zero]
  | add a b _ _ ha hb =>
    refine ⟨GlobalTheory.OrientedHeis.theta_add ha.1 hb.1, funext fun x => ?_⟩
    have e : Lift.liftInt ν 𝓕 (thetaKO ω) (a + b) Φ x =
        Lift.liftInt ν 𝓕 (thetaKO ω) a Φ x + Lift.liftInt ν 𝓕 (thetaKO ω) b Φ x := by
      simp only [Lift.liftInt, kernel_add, add_mul]
      exact integral_add (hI a ha.1 x) (hI b hb.1 x)
    simp [e, congrFun ha.2 x, congrFun hb.2 x]
  | smul c a _ ha =>
    refine ⟨GlobalTheory.OrientedHeis.theta_smul c ha.1, funext fun x => ?_⟩
    have e : Lift.liftInt ν 𝓕 (thetaKO ω) (c • a) Φ x = c * Lift.liftInt ν 𝓕 (thetaKO ω) a Φ x := by
      simp only [Lift.liftInt, kernel_smul, mul_assoc]
      exact integral_const_mul c _
    simp [e, congrFun ha.2 x]

theorem eq_zero_of_le_mul_all {a K : ℝ≥0∞} (hK : K ≠ ∞) (h : ∀ δ : ℝ≥0∞, 0 < δ → a ≤ K * δ) : a = 0 := by
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) zero_le
  rw [zero_add]
  rcases eq_or_ne K 0 with hK0 | hK0
  · have h1 := h 1 one_pos
    rw [hK0, zero_mul] at h1
    exact h1.trans zero_le
  · refine (h (ε / K) (ENNReal.div_pos (ENNReal.coe_ne_zero.2 hε.ne') hK)).trans (le_of_eq ?_)
    exact ENNReal.mul_div_cancel hK0 hK

theorem liftInt_zero_of_approx {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {ν : Measure (GA D W)} {𝓕 : Set (GA D W)}
    {cls : (GA D W → ℂ) → Prop} (hL : LiftLaws θ ψ ω ν 𝓕 cls) {Φ : GA D W → ℂ} (hΦ : cls Φ)
    {μ : Measure (WO V W)} {𝓓 : Set (WO V W)} (hμ : μ.IsAddHaarMeasure)
    (h𝓓 : IsAddFundamentalDomain (ratL W V) 𝓓 μ) {U : AddSubgroup (WO V W)} (hU : IsOpen (U : Set (WO V W)))
    {f : WO V W → ℂ} (hf : f ∈ GlobalTheory.Size.thetaLevel ψ V W U)
    (happ : ∀ (d : ℕ) (δ : ℝ≥0∞), 0 < δ → ∃ g ∈ GlobalTheory.Size.thetaLevel ψ V W U,
      Lift.liftInt ν 𝓕 (thetaKO ω) g Φ = 0 ∧ sobO ψ θ μ 𝓓 d (f - g) < δ) :
    Lift.liftInt ν 𝓕 (thetaKO ω) f Φ = 0 := by
  obtain ⟨A, hA⟩ := hL.bound
  obtain ⟨d, hd⟩ := hA 0
  obtain ⟨C, hC⟩ := hd μ 𝓓 hμ h𝓓 U hU
  have hKt : (C : ℝ≥0∞) * decayInt ν 𝓕 A Φ ≠ ∞ := ENNReal.mul_ne_top ENNReal.coe_ne_top (hL.decay_ne_top Φ hΦ A)
  funext x
  have hI : ∀ f', IsThetaFunO ψ V W f' → IntegrableOn (fun h => thetaKO ω x h f' * Φ h) 𝓕 ν := fun f' hf' => by
    simpa only [rTr, mul_one] using hL.integ f' Φ hf' hΦ x 1
  have key : ∀ δ : ℝ≥0∞, 0 < δ → ENNReal.ofReal (‖Lift.liftInt ν 𝓕 (thetaKO ω) f Φ x‖ / height V x ^ A) ≤
      (C : ℝ≥0∞) * decayInt ν 𝓕 A Φ * δ := by
    intro δ hδ
    obtain ⟨g, hgU, hg0, hlt⟩ := happ d δ hδ
    have hfg : f - g ∈ GlobalTheory.Size.thetaLevel ψ V W U := sub_mem hf hgU
    have e : Lift.liftInt ν 𝓕 (thetaKO ω) f Φ x = Lift.liftInt ν 𝓕 (thetaKO ω) (f - g) Φ x := by
      have e' : Lift.liftInt ν 𝓕 (thetaKO ω) (f - g) Φ x =
          Lift.liftInt ν 𝓕 (thetaKO ω) f Φ x - Lift.liftInt ν 𝓕 (thetaKO ω) g Φ x := by
        simp only [Lift.liftInt, kernel_sub, sub_mul]
        exact integral_sub (hI f hf.1) (hI g hgU.1)
      rw [e', congrFun hg0 x, Pi.zero_apply, sub_zero]
    have h2 : ENNReal.ofReal (‖Lift.liftInt ν 𝓕 (thetaKO ω) (f - g) Φ x‖ / height V x ^ A) ≤
        growthSob θ V 0 A (lift ω ν 𝓕 (f - g) Φ) := by
      simp only [growthSob, wordSum_zero, growthSize]
      exact le_iSup (fun y => ENNReal.ofReal (‖lift ω ν 𝓕 (f - g) Φ y‖ / height V y ^ A)) x
    rw [e]
    calc _ ≤ _ := h2
      _ ≤ C * sobO ψ θ μ 𝓓 d (f - g) * decayInt ν 𝓕 A Φ := hC (f - g) hfg Φ hΦ
      _ = (C : ℝ≥0∞) * decayInt ν 𝓕 A Φ * sobO ψ θ μ 𝓓 d (f - g) := by ring
      _ ≤ (C : ℝ≥0∞) * decayInt ν 𝓕 A Φ * δ := by gcongr
  have h0 := eq_zero_of_le_mul_all hKt key
  rw [ENNReal.ofReal_eq_zero] at h0
  have hpos : 0 < height V x ^ A := pow_pos (height_pos V x) A
  have h3 : ‖Lift.liftInt ν 𝓕 (thetaKO ω) f Φ x‖ ≤ 0 := by
    simpa using (div_le_iff₀ hpos).1 h0
  exact norm_le_zero_iff.1 h3

end GlobalTheory.PairLift.LowAllPf

namespace GlobalTheory.PairLift

theorem lowAll_of_lowFock : ∀ (D : D7) (X : ProvA), Inputs D X → LowFock D X → LowAll D X := by
  intro D X hIn hLF S S' aS aT hR i V' W M' θ ψ hθ hi hs ω' hω ν 𝓕 hν h𝓕 F hF v f' hf
  obtain ⟨χS, χT, hW, -⟩ := id hω
  have hL := hIn.laws V' W θ ψ χS χT ω' hθ hW ν 𝓕 hν h𝓕
  have hFv := LowAllPf.multT_apply_smooth_cusp θ M' ∅ 1 F hF v
  obtain ⟨A⟩ := (GlobalTheory.FrameExists.frame_exists_signCompat D V').1
  obtain ⟨μ, 𝓓, hμ⟩ := GlobalTheory.Size.exists_isCovolOne V' W
  obtain ⟨U, hU, hfU, happ⟩ := hIn.dense V' W A (Fr.ofModel M') θ ψ hW.std hθ μ 𝓓 hμ f' hf
  have hI : ∀ f, IsThetaFunO ψ V' W f → ∀ x, IntegrableOn (fun h => thetaKO ω' x h f * F v h) 𝓕 ν :=
    fun f hf x => by simpa only [rTr, mul_one] using hL.integ f (F v) hf hFv x 1
  have hspan := LowAllPf.liftInt_span_zero hI
    (s := {g | ∃ f₀ P, IsVacF ψ θ A (Fr.ofModel M') f₀ ∧ f₀ ∈ GlobalTheory.Size.thetaLevel ψ V' W U ∧
      g = ptF ψ θ A (Fr.ofModel M') f₀ P})
    (by
      rintro _ ⟨f₀, P, hv, -, rfl⟩
      exact ⟨GlobalTheory.Chain.InnerSteps.theta_pureTensorO hW.std hθ _ _ _ _ hv.1 P,
        hLF S S' aS aT hR i V' W M' θ ψ hθ hi hs ω' hω ν 𝓕 hν h𝓕 F hF v A f₀ hv P⟩)
  refine LowAllPf.liftInt_zero_of_approx hL hFv hμ.1 hμ.2.1 hU hfU fun d δ hδ => ?_
  obtain ⟨g, hg, hgU, hlt⟩ := happ d δ hδ
  exact ⟨g, hgU, (hspan g hg).2, hlt⟩

end GlobalTheory.PairLift

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

namespace GlobalTheory.SgnIdent

variable {D : D7}

theorem uj_neg_eq {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A) :
    Formalism.UG.UJ σ (-J) = Formalism.UG.UJ σ J := by
  ext g
  show Formalism.UG.cT σ (g : Matrix (Fin n) (Fin n) A) * (-J) * (g : Matrix (Fin n) (Fin n) A) = -J ↔
    Formalism.UG.cT σ (g : Matrix (Fin n) (Fin n) A) * J * (g : Matrix (Fin n) (Fin n) A) = J
  rw [Matrix.mul_neg, Matrix.neg_mul, neg_inj]

theorem uh_neg_eq {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) : Formalism.QuantumDeterminants.UH (-H) = Formalism.QuantumDeterminants.UH H := by
  ext g
  simp only [Formalism.QuantumDeterminants.UH, Set.mem_setOf_eq, Matrix.mul_neg, Matrix.neg_mul, neg_inj]

theorem gramAt_neg_eq (V : HSp D) (τ : D.what₂.Tau) : gramAt D (neg V) τ = -gramAt D V τ := by
  ext i j; simp [gramAt, neg_gram]

theorem mem_GQ_sgn (ε : Bool) (V : HSp D) (g : GA D (sgn ε V)) : g ∈ GQ (sgn ε V) ↔ ofSgn ε V g ∈ GQ V := by
  cases ε
  · exact Iff.rfl
  · constructor
    · rintro ⟨x, hx, e⟩
      exact ⟨x, by rw [← uj_neg_eq]; exact hx, e⟩
    · rintro ⟨x, hx, e⟩
      exact ⟨x, by rw [← uj_neg_eq] at hx; exact hx, e⟩

theorem mem_GfC_sgn (ε : Bool) (V : HSp D) (g : GA D (sgn ε V)) : g ∈ GfC (sgn ε V) ↔ ofSgn ε V g ∈ GfC V := Iff.rfl

theorem mem_GinfC_sgn (ε : Bool) (V : HSp D) (g : GA D (sgn ε V)) : g ∈ GinfC (sgn ε V) ↔ ofSgn ε V g ∈ GinfC V :=
  Iff.rfl

theorem uh_sgn (ε : Bool) (V : HSp D) (τ : D.what₂.Tau) :
    Formalism.QuantumDeterminants.UH (gramAt D (sgn ε V) τ) = Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
  cases ε
  · rfl
  · rw [gramAt_neg_eq, uh_neg_eq]

theorem lieAt_sgn (ε : Bool) (V : HSp D) (τ : D.what₂.Tau) : lieAt (sgn ε V) τ = lieAt V τ := by
  cases ε
  · rfl
  · ext X
    show Xᴴ * gramAt D (neg V) τ + gramAt D (neg V) τ * X = 0 ↔ Xᴴ * gramAt D V τ + gramAt D V τ * X = 0
    rw [gramAt_neg_eq, Matrix.mul_neg, Matrix.neg_mul, ← neg_add, neg_eq_zero]

theorem isAtTau_sgn (θ : InfFam D) (ε : Bool) (V : HSp D) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (x : GA D (sgn ε V)) : IsAtTau θ (sgn ε V) τ g x ↔ IsAtTau θ V τ g (ofSgn ε V x) := Iff.rfl

theorem atTau_sgn (θ : InfFam D) (hθ : IsInfFam θ) (ε : Bool) (V : HSp D) (τ : D.what₂.Tau)
    (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : ofSgn ε V (atTau θ (sgn ε V) τ g) = atTau θ V τ g := by
  by_cases h : ∃ x, IsAtTau θ V τ g x
  · have h₁ : ∃ x, IsAtTau θ (sgn ε V) τ g x := by
      obtain ⟨x, hx⟩ := h
      refine ⟨(ofSgn ε V).symm x, (isAtTau_sgn θ ε V τ g _).2 ?_⟩
      rw [MulEquiv.apply_symm_apply]; exact hx
    have a : IsAtTau θ (sgn ε V) τ g (atTau θ (sgn ε V) τ g) := by
      unfold atTau; rw [dite_eq_left h₁]; exact h₁.choose_spec
    have b : IsAtTau θ V τ g (atTau θ V τ g) := by
      unfold atTau; rw [dite_eq_left h]; exact h.choose_spec
    exact GlobalTheory.Published.AutFin.Model.isAtTau_unique θ V hθ ((isAtTau_sgn θ ε V τ g _).1 a) b
  · have h₁ : ¬ ∃ x, IsAtTau θ (sgn ε V) τ g x := fun ⟨x, hx⟩ => h ⟨_, (isAtTau_sgn θ ε V τ g x).1 hx⟩
    have a : atTau θ (sgn ε V) τ g = 1 := by unfold atTau; rw [dite_eq_right h₁]
    have b : atTau θ V τ g = 1 := by unfold atTau; rw [dite_eq_right h]
    rw [a, b, map_one]

theorem meas_sgn (ε : Bool) (V : HSp D) (ν : Measure (GA D V)) (𝓕 : Set (GA D V)) (hν : ν.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 ν) :
    ∃ ν₁ : Measure (GA D (sgn ε V)), ν₁.IsHaarMeasure ∧ IsFundamentalDomain (GQ (sgn ε V)) (ofSgn ε V ⁻¹' 𝓕) ν₁ ∧
      ∀ φ : GA D V → ℂ, (IntegrableOn (fun g => φ (ofSgn ε V g)) (ofSgn ε V ⁻¹' 𝓕) ν₁ ↔ IntegrableOn φ 𝓕 ν) ∧
        ∫ g in ofSgn ε V ⁻¹' 𝓕, φ (ofSgn ε V g) ∂ν₁ = ∫ g in 𝓕, φ g ∂ν := by
  obtain ⟨-, -, -, hb, hg, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨-, -, -, hb₁, hg₁, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (sgn ε V)
  let h : GA D (sgn ε V) ≃ₜ GA D V :=
    { toEquiv := (ofSgn ε V).toEquiv, continuous_toFun := continuous_ofSgn ε V,
      continuous_invFun := continuous_ofSgn_symm ε V }
  have me : MeasurableEmbedding (ofSgn ε V) := h.toMeasurableEquiv.measurableEmbedding
  have hm : Measurable (ofSgn ε V) := (continuous_ofSgn ε V).measurable
  have hm' : Measurable (ofSgn ε V).symm := (continuous_ofSgn_symm ε V).measurable
  have mp : MeasurePreserving (ofSgn ε V) (ν.map (ofSgn ε V).symm) ν := by
    refine ⟨hm, ?_⟩
    rw [Measure.map_map hm hm']
    have : (⇑(ofSgn ε V) ∘ ⇑(ofSgn ε V).symm) = id := funext fun x => (ofSgn ε V).apply_symm_apply x
    rw [this, Measure.map_id]
  refine ⟨ν.map (ofSgn ε V).symm,
    (ofSgn ε V).symm.isHaarMeasure_map ν (continuous_ofSgn_symm ε V) (continuous_ofSgn ε V), ?_, fun φ => ?_⟩
  · refine h𝓕.preimage_of_equiv mp.quasiMeasurePreserving
      (e := fun γ : GQ V => (⟨(ofSgn ε V).symm γ, (mem_GQ_sgn ε V _).2 (by rw [MulEquiv.apply_symm_apply]; exact γ.2)⟩ :
        GQ (sgn ε V))) ⟨fun a b hab => ?_, fun δ => ?_⟩ fun γ x => ?_
    · exact Subtype.ext ((ofSgn ε V).symm.injective (congrArg Subtype.val hab))
    · exact ⟨⟨ofSgn ε V δ, (mem_GQ_sgn ε V δ).1 δ.2⟩, Subtype.ext ((ofSgn ε V).symm_apply_apply δ)⟩
    · show ofSgn ε V ((ofSgn ε V).symm (γ : GA D V) * x) = (γ : GA D V) * ofSgn ε V x
      rw [map_mul, MulEquiv.apply_symm_apply]
  · exact ⟨mp.integrableOn_comp_preimage me, mp.setIntegral_preimage_emb me φ 𝓕⟩

theorem sgnLaw_holds : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (ε : Bool) (V : HSp D), SgnLaw θ ε V :=
  fun _ θ hθ ε V => ⟨mem_GQ_sgn ε V, mem_GfC_sgn ε V, mem_GinfC_sgn ε V, uh_sgn ε V, lieAt_sgn ε V,
    fun τ g => atTau_sgn θ hθ ε V τ g, fun ν 𝓕 hν h𝓕 => meas_sgn ε V ν 𝓕 hν h𝓕⟩

end GlobalTheory.SgnIdent

end
end

section

namespace GlobalTheory.TracePairingBasisChange

open Matrix

theorem pair_eq_trace {K : Type} [Field K] {n d : ℕ} (X Y : Matrix (Fin n) (Fin d) K) :
    GlobalTheory.FlipMatch.pairM X Y = Matrix.trace (Xᵀ * Y) := by
  unfold GlobalTheory.FlipMatch.pairM
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_comm

theorem pair_change_basis {K : Type} [Field K] {n d : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (B : Matrix (Fin d) (Fin d) K) (b : GL (Fin n) K) (c : GL (Fin d) K)
    (P Q : Matrix (Fin n) (Fin d) K) :
    GlobalTheory.FlipMatch.pairM
                 ((↑b⁻¹ : Matrix (Fin n) (Fin n) K) * P * Matrix.transpose (↑c⁻¹ : Matrix (Fin d) (Fin d) K))
                 (-(Matrix.transpose (↑b : Matrix (Fin n) (Fin n) K) * A * Q * Matrix.transpose B *
                   (↑c : Matrix (Fin d) (Fin d) K))) =
      -∑ i : Fin n, ∑ j : Fin d, ∑ k : Fin n, ∑ l : Fin d, P i j * A i k * B j l * Q k l := by
  rw [pair_eq_trace, Matrix.mul_neg, Matrix.trace_neg, neg_inj]
  have hb : Matrix.transpose (↑b⁻¹ : Matrix (Fin n) (Fin n) K) * Matrix.transpose (↑b : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  have hc : (↑c : Matrix (Fin d) (Fin d) K) * (↑c⁻¹ : Matrix (Fin d) (Fin d) K) = 1 := Units.mul_inv c

  have key : Matrix.transpose ((↑b⁻¹ : Matrix (Fin n) (Fin n) K) * P * Matrix.transpose (↑c⁻¹ : Matrix (Fin d) (Fin d) K)) *
      (Matrix.transpose (↑b : Matrix (Fin n) (Fin n) K) * A * Q * Matrix.transpose B * (↑c : Matrix (Fin d) (Fin d) K)) =
      (↑c⁻¹ : Matrix (Fin d) (Fin d) K) * ((Matrix.transpose P * (A * (Q * Matrix.transpose B))) * (↑c : Matrix (Fin d) (Fin d) K)) := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Matrix.transpose (↑b⁻¹ : Matrix (Fin n) (Fin n) K)), hb, Matrix.one_mul]
  rw [key, Matrix.trace_mul_comm, Matrix.mul_assoc, hc, Matrix.mul_one]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => ?_
  ring

end GlobalTheory.TracePairingBasisChange
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

noncomputable section

namespace GlobalTheory.FockTransl

theorem integrable_exp_lin_sub_sq_norm_complex {c r : ℝ} (hc : 0 < c) (hr : 0 ≤ r) :
    Integrable fun w : ℂ => Real.exp (r * ‖w‖ - c * ‖w‖ ^ 2 / 2) := by
  have hg : Integrable fun w : ℂ => Real.exp (-(c / 4) * ‖w‖ ^ 2) := by
    have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (b := ((c / 4 : ℝ) : ℂ))
      (by simp; linarith) 0 0).norm
    refine h.congr (Filter.Eventually.of_forall fun w => ?_)
    simp [Complex.norm_exp, ← Complex.ofReal_pow]
  refine (hg.const_mul (Real.exp (r ^ 2 / c))).mono' (by fun_prop)
    (Filter.Eventually.of_forall fun w => ?_)
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have key : r ^ 2 / c + -(c / 4) * ‖w‖ ^ 2 - (r * ‖w‖ - c * ‖w‖ ^ 2 / 2)
      = (r - c * ‖w‖ / 2) ^ 2 / c := by
    field_simp
    ring
  have : 0 ≤ (r - c * ‖w‖ / 2) ^ 2 / c := by positivity
  linarith

theorem integrable_exp_lin_sub_gq (ι : Type) [Fintype ι] (a b : ℕ) (c : ι → ℝ) (hc : ∀ τ, 0 < c τ)
    (z₀ : VCx ι a b) :
    Integrable fun z : VCx ι a b => Real.exp ((∑ k : DVar ι a b,
      ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) - gq c z / 2) := by
  have key : ∀ z : VCx ι a b, Real.exp ((∑ k : DVar ι a b,
      ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) - gq c z / 2)
      = ∏ τ, ∏ i, ∏ j, Real.exp (‖(c τ : ℂ) * z₀ τ i j‖ * ‖z τ i j‖ - c τ * ‖z τ i j‖ ^ 2 / 2) := by
    intro z
    simp only [← Real.exp_sum, gq, DVar, Fintype.sum_prod_type, Finset.sum_div,
      ← Finset.sum_sub_distrib]
  simp_rw [key]
  refine Integrable.fintype_prod (f := fun τ (x : Fin b → Fin a → ℂ) =>
    ∏ i, ∏ j, Real.exp (‖(c τ : ℂ) * z₀ τ i j‖ * ‖x i j‖ - c τ * ‖x i j‖ ^ 2 / 2)) fun τ => ?_
  refine Integrable.fintype_prod (f := fun i (y : Fin a → ℂ) =>
    ∏ j, Real.exp (‖(c τ : ℂ) * z₀ τ i j‖ * ‖y j‖ - c τ * ‖y j‖ ^ 2 / 2)) fun i => ?_
  refine Integrable.fintype_prod (f := fun j (w : ℂ) =>
    Real.exp (‖(c τ : ℂ) * z₀ τ i j‖ * ‖w‖ - c τ * ‖w‖ ^ 2 / 2)) fun j => ?_
  exact integrable_exp_lin_sub_sq_norm_complex (hc τ) (norm_nonneg _)

end GlobalTheory.FockTransl

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IsoMean

theorem integrable_coef : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → (∀ y y' : Mx D a b, symplO V W (GlobalTheory.IsoMean.emb V W P Q y) (GlobalTheory.IsoMean.emb V W P Q y') = 0) → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D a b)), μ.IsAddHaarMeasure → ∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν → ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' → Integrable (fun y => ∫ u in 𝓕, heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q y) G u * star (G' u) ∂ν) μ := by
  intro D V W a b P Q hP hQ _hiso ψ hψ μ hμ ν 𝓕 hν h𝓕 G G' hG hG'
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨U, hU, hvan⟩ := GlobalTheory.T.thetaMatrixCoeff_eq_zero_unless_character_trivial D V W ψ hψ ν 𝓕 hν h𝓕 G G' hG hG'
  obtain ⟨K, hK, hKmem⟩ := GlobalTheory.T.finitePart_mem_compact_of_isotropicAnnihilator D V W a b P Q hP hQ ψ hψ U hU
  refine GlobalTheory.T.integrable_adelicMatrix_rapid_decay_compact_finite D a b μ hμ θ hθ _ (GlobalTheory.T.continuous_thetaMatrixCoeff_along_sandwich D V W a b P Q ψ hψ ν 𝓕 hν h𝓕 G G' hG hG') K hK ?_ ?_
  · intro y hy
    by_contra hne
    apply hy
    refine hKmem y fun u hu hu0 => ?_
    by_contra h1
    exact hne (hvan _ u hu hu0 h1)
  · refine GlobalTheory.T.rapid_decay_all_real_coordinates_of_functionals D V W a b P Q hP hQ θ hθ _ fun τ z m => ?_
    obtain ⟨C, hC⟩ := GlobalTheory.T.thetaMatrixCoeff_rapid_decay_real_functional D V W ψ hψ ν 𝓕 hν h𝓕 G G' hG hG' θ hθ τ z m
    exact ⟨C, fun y => hC _⟩

end GlobalTheory.IsoMean

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.conj_smooth_vector_conjugate_model_mem_smooth : ∀ (D : D7) (Y : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel Y S) (τ : D.what₂.Tau)
  (w : (GlobalTheory.ConjDS.conjModel M).H τ),
  GlobalTheory.Ell.SmV (GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ((GlobalTheory.ConjDS.conjModel M).ε τ))) ((GlobalTheory.ConjDS.conjModel M).σ τ) w →
  GlobalTheory.ConjDS.cj (M.H τ) w ∈ M.sm τ := by
  first | exact @GlobalTheory.ConjSmooth.cj_mem_sm | exact GlobalTheory.ConjSmooth.cj_mem_sm | (intros; apply GlobalTheory.ConjSmooth.cj_mem_sm <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unitary_haar_coordinate_reversal_positive_multiple : ∀ (m : ℕ) (ε : Fin m → Bool), ∃ lam : ℝ, 0 < lam ∧
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (F : Matrix (Fin m) (Fin m) ℂ → E),
    (Integrable (fun u : Formalism.REAL.UJ ε => F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) (Formalism.REAL.muG ε) ↔
      Integrable (fun h : Formalism.REAL.UJ (fun a => ε a.rev) => F (Formalism.MainNotions.S.umat h)) (Formalism.REAL.muG (fun a => ε a.rev))) ∧
    ∫ u, F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u)) ∂(Formalism.REAL.muG ε) =
      lam • ∫ h, F (Formalism.MainNotions.S.umat h) ∂(Formalism.REAL.muG (fun a => ε a.rev)) := by
  first | exact @GlobalTheory.HaarRev.haar_rev | exact GlobalTheory.HaarRev.haar_rev | (intros; apply GlobalTheory.HaarRev.haar_rev <;> assumption)
end

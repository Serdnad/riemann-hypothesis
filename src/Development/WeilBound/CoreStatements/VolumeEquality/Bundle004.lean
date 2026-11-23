module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle027
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle049
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle120
public import Development.WeilBound.CoreStatements.VolumeEquality.ContDiffAtBallPot
public import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.InfSpanNeBot
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HaarPushforwardEqBallDensity
public import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.EqVolSDOf
public import Development.WeilBound.CoreStatements.VolumeEquality.RootBranches
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushDefs
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory

namespace SheetDecomposition

theorem densU : ∃ κ : ℕ → ℕ → ℕ → ℝ, (∀ f j j', 0 < κ f j j') ∧
    ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n), ∀ t ∈ ballDom q,
      maDensity (fun (_ : Fin n) t' => ballPot q t' / 2) t = κ (Fintype.card Ψ) j j' * ballDens q t := by
  have hq : ∀ f j j' : ℕ, Nonempty (Fin f × Fin j × Fin j' ≃ Fin (f * j * j')) := fun f j j' =>
    ⟨Fintype.equivFinOfCardEq (by simp [_root_.mul_assoc])⟩
  choose κ hκ hκ' using fun f j j' : ℕ => GlobalTheory.T.monge_ampere_density_of_ball_potential (Fin f) j j' (f * j * j') (hq f j j').some
  refine ⟨κ, hκ, fun Ψ _ j j' n q t ht => ?_⟩
  obtain rfl : n = Fintype.card Ψ * j * j' := by
    have := Fintype.card_congr q
    simpa [_root_.mul_assoc] using this.symm
  obtain ⟨c, -, hc⟩ := GlobalTheory.T.monge_ampere_density_of_ball_potential Ψ j j' _ q
  rw [hc t ht]
  congr 1
  have h0 := hc 0 (zero_mem_ballDom q)
  have h1 := hκ' (Fintype.card Ψ) j j' 0 (zero_mem_ballDom _)
  rw [ballDens_zero, _root_.mul_one] at h0 h1
  rw [← h0, ← h1]
  obtain ⟨σ, hσ⟩ := ballPot_renumber (Fintype.equivFin Ψ) q (hq (Fintype.card Ψ) j j').some
  have h2 := GlobalTheory.T.monge_ampere_density_change_of_variables _ (fun t' => ballPot (hq (Fintype.card Ψ) j j').some t' / 2) (fun t' => ballPot q t' / 2)
    (fun t i => t (σ i)) (fun _ => 0) 0
    (analyticAt_pi_iff.2 fun i => (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ => ℂ) (σ i)).analyticAt 0)
    analyticAt_const (contDiffAt_ballPot _ (zero_mem_ballDom _))
    (Eventually.of_forall fun t' => by simp [hσ t'])
  rw [h2, norm_det_perm, one_pow, _root_.one_mul]
  rfl

theorem norm_det_id (n : ℕ) (t : Fin n → ℂ) :
    ‖LinearMap.det ((fderiv ℂ (fun t : Fin n → ℂ => t) t : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) :
      (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))‖ = 1 :=
  norm_det_perm (Equiv.refl _) t

theorem transferU : ∃ κ : ℕ → ℕ → ℕ → ℝ, (∀ f j j', 0 < κ f j j') ∧
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (Q : Pieces Or) (G : ((Σ k, J k) → ℂ) → ℝ) (Gk : Fin Q.np → (Fin Dc.n → ℂ) → ℝ), (∀ w ∈ Dc.Xo, ∀ w' ∈ torusSat {w}, G w' = G w) → (∀ m, ∀ t ∈ Q.V m, G (Q.γ m t) = Gk (Q.pc m) t) → (∀ k, IntegrableOn (fun t => Gk k t * ballDens (Q.F k).q t) (Q.FF k)) → ptsIntegral (e := Dc.n) (mCoordIdeal Dc.y) (fun _ => phMu Hd) G = κ Dc.f Dc.j Dc.j' * ∑ k, (Q.d k : ℝ) * ∫ t in Q.FF k, Gk k t * ballDens (Q.F k).q t := by
  obtain ⟨κ, hκ, hd⟩ := densU
  refine ⟨κ, hκ, ?_⟩
  intro E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or Q G Gk hG hGk hint
  have hdens : ∀ m, ∀ t ∈ Q.V m, maDensity (fun (_ : Fin Dc.n) t' => Real.log ((muLine Hd).h (Q.γ m t'))) t =
      κ Dc.f Dc.j Dc.j' * ballDens (Q.F (Q.pc m)).q t := by
    intro m t ht
    obtain ⟨g, hg, hev⟩ := Q.pot m t ht
    have h2 := GlobalTheory.T.monge_ampere_density_change_of_variables _ (fun t' => ballPot (Q.F (Q.pc m)).q t' / 2)
      (fun t' => Real.log ((muLine Hd).h (Q.γ m t'))) (fun t => t) g t analyticAt_id hg
      (contDiffAt_ballPot _ (Q.V_sub m ht)) hev
    rw [h2, norm_det_id, one_pow, _root_.one_mul]
    exact hd _ _ _ _ _ t (Q.V_sub m ht)
  have hsm : ∀ m, ContDiffOn ℝ 2 (fun t => Real.log ((muLine Hd).h (Q.γ m t))) (Q.V m) := by
    intro m t ht
    obtain ⟨g, hg, hev⟩ := Q.pot m t ht
    have hψ : ContDiffAt ℝ 2 (fun y => (g y).re) t :=
      Complex.reCLM.contDiff.contDiffAt.comp t (hg.contDiffAt.restrict_scalars ℝ)
    exact (((contDiffAt_ballPot _ (Q.V_sub m ht)).add hψ).congr_of_eventuallyEq hev).contDiffWithinAt
  have heq : ∀ m, Set.EqOn
      (fun t => G (Q.γ m t) * maDensity (fun (_ : Fin Dc.n) t' => Real.log ((muLine Hd).h (Q.γ m t'))) t)
      (fun t => κ Dc.f Dc.j Dc.j' * (Gk (Q.pc m) t * ballDens (Q.F (Q.pc m)).q t)) (Q.B m) := by
    intro m t ht
    have hV := (Q.cover.meas m).2 ht
    simp only
    rw [hdens m t hV, hGk m t hV]
    ring
  have hint' : ∀ k, IntegrableOn (fun t => κ Dc.f Dc.j Dc.j' * (Gk k t * ballDens (Q.F k).q t)) (Q.FF k) :=
    fun k => (hint k).const_mul _
  obtain ⟨hs1, hs2⟩ := sum_sheets volume Q.FF Q.pc Q.B Q.d (fun k => (Q.fund k).1) (fun m => (Q.cover.meas m).1)
    Q.B_sub (fun k t => κ Dc.f Dc.j Dc.j' * (Gk k t * ballDens (Q.F k).q t)) Q.count hint'
  have key := GlobalTheory.T.sheet_cover_of_arithmetic_variety K J (mCoordIdeal Dc.y) Dc.n Dc.nCharts Dc.Bd Dc.chart Q.V Q.B Q.γ (muLine Hd) G Dc.arith
    (fun z hz => by
      obtain ⟨a, t, ht, cc, hc, rfl⟩ := Dc.chart_cover z hz
      exact ⟨a, t, ht, _, rfl, cc, hc, rfl⟩)
    Q.cover hsm hG
    (fun m => ((hint' (Q.pc m)).mono_set (Q.B_sub m)).congr_fun (heq m).symm (Q.cover.meas m).1)
    (hs1.congr fun m => setIntegral_congr_fun (Q.cover.meas m).1 fun t ht => congrArg abs (heq m ht).symm)
  refine key.trans ?_
  rw [tsum_congr fun m => setIntegral_congr_fun (Q.cover.meas m).1 (heq m), hs2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul]
  ring

theorem sheet_pieces_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (Q : Pieces Or), ∃ κ : ℝ, 0 < κ ∧ ∀ (G : ((Σ k, J k) → ℂ) → ℝ) (Gk : Fin Q.np → (Fin Dc.n → ℂ) → ℝ), (∀ w ∈ Dc.Xo, ∀ w' ∈ torusSat {w}, G w' = G w) → (∀ m, ∀ t ∈ Q.V m, G (Q.γ m t) = Gk (Q.pc m) t) → (∀ k, IntegrableOn (fun t => Gk k t * ballDens (Q.F k).q t) (Q.FF k)) → ptsIntegral (e := Dc.n) (mCoordIdeal Dc.y) (fun _ => phMu Hd) G = κ * ∑ k, (Q.d k : ℝ) * ∫ t in Q.FF k, Gk k t * ballDens (Q.F k).q t := by
  obtain ⟨κ, hκ, h⟩ := transferU
  intro E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or Q
  exact ⟨κ Dc.f Dc.j Dc.j', hκ _ _ _, h E H D Xo l c Y II K J Ω W Dc Hd S₀ Or Q⟩

end SheetDecomposition
end

section

noncomputable section

namespace SheetDecomposition

open NumberField Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.Dict
  GlobalTheory.CompanionTheory.Ar.Cusp.DictMeas GlobalTheory.CompanionTheory.Ar.Cmp PositivityTheory.EqVol

def MFund {Ψ : Type} [Fintype Ψ] {j j' n : ℕ} {G : Type} [Group G] (q : Ψ × Fin j × Fin j' ≃ Fin n)
    (ρ : G → Ψ → Matrix (Sg j j') (Sg j j') ℂ) (Γ : Subgroup G) (S : Set (Fin n → ℂ)) : Prop :=
  MeasurableSet S ∧ S ⊆ ballDom q ∧ (∀ t ∈ ballDom q, ∃ γ ∈ Γ, moebBall q (ρ γ) t ∈ S) ∧
    ∀ t ∈ S, ∀ γ ∈ Γ, moebBall q (ρ γ) t ∈ S → γ = 1

def rho {E : Type} [Field E] {Ψ : Type} {j j' N : ℕ} (s : Ψ → (E →+* ℂ)) (A : Ψ → Matrix (Fin N) (Sg j j') ℂ)
    (Ai : Ψ → Matrix (Sg j j') (Fin N) ℂ) (γ : GL (Fin N) E) (τ : Ψ) : Matrix (Sg j j') (Sg j j') ℂ :=
  Ai τ * ((γ : Matrix (Fin N) (Fin N) E).map (s τ) * A τ)

def MoebVol : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q q' : Ψ × Fin j × Fin j' ≃ Fin n) (G : Type) [Group G] [Countable G]
    (ρ ρ' : G → Ψ → Matrix (Sg j j') (Sg j j') ℂ) (w : Ψ → Matrix (Sg j j') (Sg j j') ℂ) (U Γ Γ' : Subgroup G) (a : G)
    (S S' : Set (Fin n → ℂ)), (∀ τ, ρ 1 τ = 1) → (∀ x y τ, ρ (x * y) τ = ρ x τ * ρ y τ) → (∀ γ ∈ U, ∀ τ, IsSgU (ρ γ τ)) →
    (∀ γ ∈ Γ', ∀ τ, IsSgU (ρ' γ τ)) → (∀ τ, IsSgU (w τ)) → (∀ γ τ, w τ * ρ' γ τ = ρ (a * γ * a⁻¹) τ * w τ) →
    Γ ≤ U → conjBy a Γ' ≤ U → EqIdx Γ (conjBy a Γ') → MFund q ρ Γ S → MFund q' ρ' Γ' S' → ballMeas q S = ballMeas q' S'

def StdZ : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ]
    [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F), ∃ A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ,
    (∀ τ, (A τ)ᴴ * C.sgr τ * A τ = sgI j j') ∧ ∃ Z : (Fin n → ℂ) → Fin n → ℂ, Set.BijOn Z (ballDom F.q) (ballDom F.q) ∧
      (∀ S, MeasurableSet S → S ⊆ ballDom F.q → MeasurableSet (Z '' S) ∧ ballMeas F.q (Z '' S) = ballMeas F.q S) ∧
      ∀ (γ : GL (Fin (j + j')) E) (δ : Λ ≃ₗ[𝓞 E] Λ), (∀ x, C.e (δ x) = (γ : Matrix (Fin (j + j')) (Fin (j + j')) E) *ᵥ C.e x) →
        (∀ x y, F.form (δ x) (δ y) = F.form x y) →
        (∀ τ, ((γ : Matrix (Fin (j + j')) (Fin (j + j')) E).map (embOf (F.σ τ)))ᴴ * C.gr τ *
          (γ : Matrix (Fin (j + j')) (Fin (j + j')) E).map (embOf (F.σ τ)) = C.gr τ) →
        ∀ t ∈ ballDom F.q, ∀ t' ∈ ballDom F.q, ((F.R t).EqvBy (F.R t') δ ↔
          Z t' = moebBall F.q (rho (fun τ => embOf (F.σ τ)) A (fun τ => C.cinv (A τ) τ) γ) (Z t))

def StdModel : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] [Nonempty Ψ] (j j' n g : ℕ) (Λ : Type)
    [AddCommGroup Λ] [Module (𝓞 E) Λ] (_ : Host E) (F : UnivFam E Ψ j j' n g Λ) (ξ : E) (c₀ : ℝ), 0 < c₀ →
    (∀ τ, embOf (F.σ τ) ξ = Complex.I * (c₀ : ℂ)) →
    ∃ (G : Matrix (Fin (j + j')) (Fin (j + j')) E) (e : Λ →ₗ[𝓞 E] (Fin (j + j') → E))
      (A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ) (Ai : Ψ → Matrix (Sg j j') (Fin (j + j')) ℂ) (Z : (Fin n → ℂ) → Fin n → ℂ),
      (∀ a b, cc (G a b) = G b a) ∧ G.det ≠ 0 ∧ Function.Injective e ∧ IsLat (LinearMap.range e) ∧
      (∀ x y, ((F.form x y : ℤ) : ℚ) = EFf (-ξ) G (e x) (e y)) ∧
      (∀ τ, (A τ)ᴴ * (G.map (embOf (F.σ τ)))ᵀ * A τ = sgI j j' ∧ Ai τ * A τ = 1 ∧ A τ * Ai τ = 1) ∧
      Set.BijOn Z (ballDom F.q) (ballDom F.q) ∧
      (∀ S, MeasurableSet S → S ⊆ ballDom F.q → MeasurableSet (Z '' S) ∧ ballMeas F.q (Z '' S) = ballMeas F.q S) ∧
      ∀ γ ∈ uGrp (ccH E) G, ∀ δ : Λ ≃ₗ[𝓞 E] Λ, (∀ x, e (δ x) = (γ : Matrix (Fin (j + j')) (Fin (j + j')) E) *ᵥ e x) →
        ∀ t ∈ ballDom F.q, ∀ t' ∈ ballDom F.q, ((F.R t).EqvBy (F.R t') δ ↔
          Z t' = moebBall F.q (rho (fun τ => embOf (F.σ τ)) A Ai γ) (Z t))

def ArithIdx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)] (Ψ : Type)
    (j j' : ℕ) (s : Ψ → (E →+* ℂ)) (G G' : Matrix (Fin (j + j')) (Fin (j + j')) E)
    (L L' : Submodule (𝓞 E) (Fin (j + j') → E)) (ξ : E) (𝔞 : Ideal (𝓞 E)),
    (∀ u : E →+* ℂ, u ∈ Set.range s ∨ ComplexEmbedding.conjugate u ∈ Set.range s) → 0 < j → 0 < j' → 3 ≤ j + j' →
    (∀ a b, cc (G a b) = G b a) → (∀ a b, cc (G' a b) = G' b a) → G.det ≠ 0 → G'.det ≠ 0 →
    (∀ τ, ∃ (A : Matrix (Fin (j + j')) (Sg j j') ℂ), Aᴴ * (G.map (s τ))ᵀ * A = sgI j j') →
    (∀ τ, ∃ (A : Matrix (Fin (j + j')) (Sg j j') ℂ), Aᴴ * (G'.map (s τ))ᵀ * A = sgI j j') →
    IsLat L → IsLat L' → ξ ≠ 0 → cc ξ = -ξ → SDTrace ξ G L → SDTrace ξ G' L' → 𝔞 ≠ ⊥ → Neat (IsCMField.complexConj E) 𝔞 →
    ∃ a : GL (Fin (j + j')) E,
      (a : Matrix (Fin (j + j')) (Fin (j + j')) E)ᵀ * G * (a : Matrix (Fin (j + j')) (Fin (j + j')) E).map (ccH E) = G' ∧
      conjBy a (levelGrp (ccH E) G' L' 𝔞) ≤ uGrp (ccH E) G ∧
      EqIdx (levelGrp (ccH E) G L 𝔞) (conjBy a (levelGrp (ccH E) G' L' 𝔞))

def LevelDict : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (D : Datum H) (N : ℕ)
    (G : Matrix (Fin N) (Fin N) E) (e : D.La →ₗ[𝓞 E] (Fin N → E)) (ξ : E) (form : D.La →ₗ[ℤ] D.La →ₗ[ℤ] ℤ),
    (form = D.EF ∨ form = -D.EF) → Function.Injective e → IsLat (LinearMap.range e) → ξ ≠ 0 →
    (∀ x y, ((form x y : ℤ) : ℚ) = EFf ξ G (e x) (e y)) →
    SDTrace ξ G (LinearMap.range e) ∧
      (∀ γ ∈ levelGrp (ccH E) G (LinearMap.range e) (levIdeal l), ∃ δ, InLevel l D δ ∧
        ∀ x, e (δ x) = (γ : Matrix (Fin N) (Fin N) E) *ᵥ e x) ∧
      ∀ δ, InLevel l D δ → ∃ γ ∈ levelGrp (ccH E) G (LinearMap.range e) (levIdeal l),
        ∀ x, e (δ x) = (γ : Matrix (Fin N) (Fin N) E) *ᵥ e x

def FamVol : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (D D' : Datum H) (Ψ : Type) [Fintype Ψ]
    (j j' n g : ℕ) (F : UnivFam E Ψ j j' n g D.La) (F' : UnivFam E Ψ j j' n g D'.La) (Γ : Subgroup (D.La ≃ₗ[𝓞 E] D.La))
    (Γ' : Subgroup (D'.La ≃ₗ[𝓞 E] D'.La)) (FF FF' : Set (Fin n → ℂ)) (c₀ : ℝ), 0 < j → 0 < j' → 3 ≤ j + j' → 0 < c₀ →
    F'.σ = F.σ → (∀ τ, F.σ τ H.rt = Complex.I * (c₀ : ℂ)) → (F.form = D.EF ∨ F.form = -D.EF) →
    (F'.form = D'.EF ∨ F'.form = -D'.EF) → (∀ γ, γ ∈ Γ ↔ InLevel l D γ) → (∀ γ, γ ∈ Γ' ↔ InLevel l D' γ) →
    F.IsFundSet Γ FF → F'.IsFundSet Γ' FF' → ballMeas F.q FF = ballMeas F'.q FF'

end SheetDecomposition
end
end

section

noncomputable section

namespace SheetDecomposition

open MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

section Relabel

variable {Ψ Ψ' : Type} [Fintype Ψ] [DecidableEq Ψ] [Fintype Ψ'] [DecidableEq Ψ'] {N : ℕ} (e : Ψ ≃ Ψ')

theorem degFl_rename (F : RP Ψ N) : degFl (rename (e.prodCongr (Equiv.refl (Fin N))) F : RP Ψ' N) = degFl F := by
  unfold degFl
  have hd : dimFl Ψ' N = dimFl Ψ N := by
    unfold dimFl
    rw [Fintype.card_congr e]
  rw [hd, ← (Equiv.arrowCongr e (Equiv.refl (Equiv.Perm (Fin N)))).sum_comp]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hp : permExp ((Equiv.arrowCongr e (Equiv.refl (Equiv.Perm (Fin N)))) σ) =
      Finsupp.mapDomain (e.prodCongr (Equiv.refl (Fin N))) (permExp σ) := by
    ext ⟨τ', i⟩
    rw [Finsupp.mapDomain_equiv_apply]
    simp [permExp]
  rw [hp, coeff_rename_mapDomain _ (e.prodCongr (Equiv.refl (Fin N))).injective]
  congr 1
  exact Equiv.prod_comp e.symm (fun τ => ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ))

theorem rename_muSmall (j : ℕ) : (rename (e.prodCongr (Equiv.refl (Fin N))) (muSmall j : RP Ψ N) : RP Ψ' N) = muSmall j := by
  unfold muSmall
  split_ifs

  · simp only [map_sum, rename_X, Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply]
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)

  · simp only [pkLow, map_neg, map_sum, map_pow, rename_X, Equiv.prodCongr_apply, Prod.map_apply,
    Equiv.refl_apply]
    congr 1
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)

theorem rename_fibClass (j : ℕ) : (rename (e.prodCongr (Equiv.refl (Fin N))) (fibClass j : RP Ψ N) : RP Ψ' N) = fibClass j := by
  unfold fibClass
  simp only [map_prod, map_sub, rename_X, Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply]
  exact Fintype.prod_equiv e _ _ (fun _ => rfl)

end Relabel

theorem testRelabel : TestRelabel := by
  intro Ψ _ _ N j
  unfold testDeg
  rw [← degFl_rename (Fintype.equivFin Ψ), map_mul, map_pow, rename_muSmall, rename_fibClass]
  simp [dimX]

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {p q : ℕ}

theorem count_pairs : Fintype.card Ψ * p * q + Fintype.card (PairIx Ψ p q) = dimFl Ψ (p + q) := by
  classical
  have hL : (Finset.univ.filter fun ab : Fin (p + q) × Fin (p + q) => ab.1 < ab.2).card =
      (p + q) * (p + q - 1) / 2 := by
    rw [Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm, ← Finset.sum_range_id,
      ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.card_filter, Finset.filter_gt_eq_Iio, Fin.card_Iio]
  have hC : ((Finset.univ.filter fun ab : Fin (p + q) × Fin (p + q) => ab.1 < ab.2).filter
      fun ab => ¬ ((ab.1 : ℕ) < p ↔ (ab.2 : ℕ) < p)).card = p * q := by
    have e : ((Finset.univ.filter fun ab : Fin (p + q) × Fin (p + q) => ab.1 < ab.2).filter
        fun ab => ¬ ((ab.1 : ℕ) < p ↔ (ab.2 : ℕ) < p)) =
        (Finset.univ.filter fun a : Fin (p + q) => (a : ℕ) < p) ×ˢ
          (Finset.univ.filter fun b : Fin (p + q) => ¬ (b : ℕ) < p) := by
      ext ⟨a, b⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product, Fin.lt_iff_val_lt_val]
      omega
    have h1 : (Finset.univ.filter fun a : Fin (p + q) => (a : ℕ) < p).card = p := by
      rw [Fin.card_filter_val_lt]
      omega
    have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (p + q))))
      (fun a : Fin (p + q) => (a : ℕ) < p)
    rw [h1, Finset.card_univ, Fintype.card_fin] at h2
    rw [e, Finset.card_product, h1]
    congr 1
    omega
  have hS : Fintype.card {ab : Fin (p + q) × Fin (p + q) // ab.1 < ab.2 ∧ ((ab.1 : ℕ) < p ↔ (ab.2 : ℕ) < p)} +
      p * q = (p + q) * (p + q - 1) / 2 := by
    rw [Fintype.card_subtype, ← hL, ← hC, ← Finset.filter_filter]
    exact Finset.card_filter_add_card_filter_not _
  rw [Fintype.card_prod]
  unfold dimFl
  rw [← hS]
  ring

def muCoef (Ψ : Type) (p q : ℕ) : Ψ × Fin (p + q) → ℤ := fun x => if p ≤ (x.2 : ℕ) then 1 else 0

def fibCoef (t : PairIx Ψ p q) : Ψ × Fin (p + q) → ℤ := fun x =>
  (if x = (t.1, t.2.1.2) then 1 else 0) - if x = (t.1, t.2.1.1) then 1 else 0

theorem sum_muCoef {A : Type} [AddCommGroup A] (x : Ψ × Fin (p + q) → A) :
    ∑ r, muCoef Ψ p q r • x r = ∑ τ, ∑ i ∈ Finset.univ.filter (fun i : Fin (p + q) => p ≤ (i : ℕ)), x (τ, i) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [muCoef]
  split_ifs <;> simp

theorem sum_fibCoef {A : Type} [AddCommGroup A] (x : Ψ × Fin (p + q) → A) (t : PairIx Ψ p q) :
    ∑ r, fibCoef t r • x r = x (t.1, t.2.1.2) - x (t.1, t.2.1.1) := by
  simp [fibCoef, sub_smul, Finset.sum_sub_distrib, ite_smul]

theorem test_factor {n r : ℕ} (e : Fin r ≃ PairIx Ψ p q) (hq : q ≤ p) (hn : n = Fintype.card Ψ * p * q) :
    (muSmall p ^ dimX Ψ (p + q) p * fibClass p : RP Ψ (p + q)) =
      ∏ j : Fin (n + r), ∑ x, Fin.append (fun _ : Fin n => muCoef Ψ p q) (fun j => fibCoef (e j)) j x • X x := by
  have hN : p + q - p ≤ p := by omega
  have hmu : (muSmall p : RP Ψ (p + q)) = ∑ x, muCoef Ψ p q x • (X x : RP Ψ (p + q)) := by
    rw [sum_muCoef (X : Ψ × Fin (p + q) → RP Ψ (p + q))]
    unfold muSmall
    rw [if_pos hN]
  have hdim : dimX Ψ (p + q) p = n := by
    unfold dimX
    rw [hn, Nat.add_sub_cancel_left]
    ring
  have hfib : (fibClass p : RP Ψ (p + q)) = ∏ i : Fin r, ∑ x, fibCoef (e i) x • (X x : RP Ψ (p + q)) := by
    simp only [sum_fibCoef]
    rw [Fintype.prod_equiv e _ (fun t : PairIx Ψ p q => (X (t.1, t.2.1.2) - X (t.1, t.2.1.1) : RP Ψ (p + q)))
      (fun _ => rfl)]
    unfold fibClass
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← Finset.prod_subtype_eq_prod_filter, Finset.subtype_univ]
    try rfl
  rw [Fin.prod_univ_add, hmu, hdim, hfib]
  simp only [Fin.append_left, Fin.append_right, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end SheetDecomposition
end
end

section

noncomputable section

namespace SheetDecomposition

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI.I4

variable {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {K : Type} [Fintype K] {ι : K → Type} [∀ b, Fintype (ι b)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ b, Fintype (ι' b)] {K'' : Type} [Fintype K''] {ι'' : K'' → Type}
  [∀ b, Fintype (ι'' b)]

@[simp] theorem vdeg_zero (O : ValuationSubring Ω) (y : (Σ b, ι b) → Ω) : vdeg O y 0 = 1 := by simp [vdeg]

theorem vdeg_join (O : ValuationSubring Ω) (y : (Σ b, ι b) → Ω) (y' : (Σ b, ι' b) → Ω) (a : K → ℤ) (a' : K' → ℤ) :
    vdeg O (joinPt y y') (Sum.elim a a') = vdeg O y a * vdeg O y' a' := by
  unfold vdeg
  rw [Fintype.prod_sum_type]
  rfl

theorem vdeg_join_inl (O : ValuationSubring Ω) (y : (Σ b, ι b) → Ω) (y' : (Σ b, ι' b) → Ω) (a : K → ℤ) :
    vdeg O (joinPt y y') (Sum.elim a 0) = vdeg O y a := by rw [vdeg_join, vdeg_zero, mul_one]

theorem vdeg_join_inr (O : ValuationSubring Ω) (y : (Σ b, ι b) → Ω) (y' : (Σ b, ι' b) → Ω) (a' : K' → ℤ) :
    vdeg O (joinPt y y') (Sum.elim 0 a') = vdeg O y' a' := by rw [vdeg_join, vdeg_zero, one_mul]

namespace ValEq

variable {y : (Σ b, ι b) → Ω} {y' : (Σ b, ι' b) → Ω} {y'' : (Σ b, ι'' b) → Ω}

theorem of_eq {a : K → ℤ} {a' : K' → ℤ} (h : ∀ O : ValuationSubring Ω, vdeg O y a = vdeg O y' a') : ValEq k y a y' a' :=
  ⟨1, one_ne_zero, fun O _ => by rw [h O, map_one, one_mul]⟩

theorem symm {a : K → ℤ} {a' : K' → ℤ} (h : ValEq k y a y' a') : ValEq k y' a' y a := by
  obtain ⟨ρ, h0, h⟩ := h
  refine ⟨ρ⁻¹, inv_ne_zero h0, fun O hO => ?_⟩
  rw [h O hO, ← mul_assoc, ← map_mul, inv_mul_cancel₀ h0, map_one, one_mul]

theorem trans {a : K → ℤ} {a' : K' → ℤ} {a'' : K'' → ℤ} (h : ValEq k y a y' a') (h' : ValEq k y' a' y'' a'') :
    ValEq k y a y'' a'' := by
  obtain ⟨ρ, h0, h⟩ := h
  obtain ⟨ρ', h0', h'⟩ := h'
  exact ⟨ρ * ρ', mul_ne_zero h0 h0', fun O hO => by rw [h O hO, h' O hO, map_mul, mul_assoc]⟩

theorem join_inl (y : (Σ b, ι b) → Ω) (y' : (Σ b, ι' b) → Ω) (a : K → ℤ) : ValEq k (joinPt y y') (Sum.elim a 0) y a :=
  of_eq fun O => vdeg_join_inl O y y' a

theorem join_inr (y : (Σ b, ι b) → Ω) (y' : (Σ b, ι' b) → Ω) (a' : K' → ℤ) : ValEq k (joinPt y y') (Sum.elim 0 a') y' a' :=
  of_eq fun O => vdeg_join_inr O y y' a'

end ValEq

end SheetDecomposition
end
end

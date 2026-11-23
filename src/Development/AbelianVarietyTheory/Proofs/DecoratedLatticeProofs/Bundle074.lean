module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.HeightBoundSetup
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ToOneSucc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle031
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle037
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OrbitLocallyConstant
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralParabolicUnfolding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeSupportAndFourierRelation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle051
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle065
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle069
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle070
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CharacterArgumentCongrRootEntrySumMod
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelCongruenceIffFlagConditions
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle141
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum

@[expose] public section

section

noncomputable section

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

namespace GlobalTheory.CuspGeo.FirstMinPos

theorem norm_mulVec_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    ‖A *ᵥ x‖ ≤ (∑ i, ∑ j, ‖A i j‖) * ‖x‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  calc ‖(A *ᵥ x) i‖ = ‖∑ j, A i j * x j‖ := rfl
    _ ≤ ∑ j, ‖A i j * x j‖ := norm_sum_le _ _
    _ ≤ ∑ j, ‖A i j‖ * ‖x‖ := Finset.sum_le_sum fun j _ => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (norm_le_pi_norm x j) (norm_nonneg _)
    _ = (∑ j, ‖A i j‖) * ‖x‖ := by rw [Finset.sum_mul]
    _ ≤ (∑ i, ∑ j, ‖A i j‖) * ‖x‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact Finset.single_le_sum (f := fun i => ∑ j, ‖A i j‖)
          (fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ i)

variable (I : AutInst)

theorem exists_one_le_norm {a : I.E} (ha : IsIntegral ℤ a) (h0 : a ≠ 0) : ∃ v, 1 ≤ ‖I.φ v a‖ := by
  have hs : ∀ v (b : I.E), I.φ v (star b) = star (I.φ v b) := fun v b => I.cm.cmUnram.2.1 _ b
  by_contra hc
  push_neg at hc
  have hfin := CompanionTheory.D.gk.RF.PE.finite_bdd I hs 1
  have hmem : ∀ k : ℕ, a ^ k ∈ {x : I.E | IsIntegral ℤ x ∧ ∀ v, ‖I.φ v x‖ ≤ 1} := fun k =>
    ⟨ha.pow k, fun v => by rw [map_pow, norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hc v).le⟩
  obtain ⟨m, k, hmk, he⟩ := hfin.exists_lt_map_eq_of_forall_mem hmem
  obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace I.F))
  have hpos : 0 < ‖I.φ v a‖ := norm_pos_iff.2 ((map_ne_zero _).2 h0)
  have h1 := congrArg (fun b => ‖I.φ v b‖) he
  simp only [map_pow, norm_pow] at h1
  exact absurd h1 (pow_lt_pow_right_of_lt_one₀ hpos (hc v) hmk).ne'

theorem coords_eq (y : I.Ginf) (u : Fin I.n → I.E) (v : InfinitePlace I.F) :
    (fun i => I.φ v (u i)) = (I.P v * uMat (y v)) *ᵥ vec I y u v := by
  have hP : I.P v * (I.P v)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v))
  have hy : uMat (y v) * uMat (y v)⁻¹ = 1 := CompanionTheory.D.gk.RF.PE.uMat_mul_inv (y v)
  simp only [vec, mulVec_mulVec, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (uMat (y v)), hy, Matrix.one_mul, hP, one_mulVec]

def cst (y : I.Ginf) (v : InfinitePlace I.F) : ℝ := ∑ i, ∑ j, ‖(I.P v * uMat (y v)) i j‖

theorem cst_nonneg (y : I.Ginf) (v : InfinitePlace I.F) : 0 ≤ cst I y v :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem norm_phi_le (y : I.Ginf) (u : Fin I.n → I.E) (v : InfinitePlace I.F) (i : Fin I.n) :
    ‖I.φ v (u i)‖ ≤ cst I y v * ‖vec I y u‖ := by
  have e := congrFun (coords_eq I y u v) i
  calc ‖I.φ v (u i)‖ = ‖((I.P v * uMat (y v)) *ᵥ vec I y u v) i‖ := by rw [← e]
    _ ≤ ‖(I.P v * uMat (y v)) *ᵥ vec I y u v‖ := norm_le_pi_norm _ i
    _ ≤ cst I y v * ‖vec I y u v‖ := norm_mulVec_le _ _
    _ ≤ cst I y v * ‖vec I y u‖ := mul_le_mul_of_nonneg_left (norm_le_pi_norm _ v) (cst_nonneg I y v)

end GlobalTheory.CuspGeo.FirstMinPos

namespace GlobalTheory.CuspGeo


open FirstMinPos in
theorem firstMin_pos : ∀ (I : AutInst) (y : I.Ginf), ∃ t : ℝ, 0 < t ∧ NoShort I y t := by
  intro I y
  have hK0 : 0 < ∑ v, cst I y v + 1 :=
    add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun v _ => cst_nonneg I y v) one_pos
  refine ⟨1 / (∑ v, cst I y v + 1), by positivity, fun u hu h0 => ?_⟩
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra hc; push_neg at hc; exact h0 (funext hc)
  obtain ⟨v, hv⟩ := exists_one_le_norm I (hu i) hi
  have h2 : cst I y v ≤ ∑ v, cst I y v + 1 := by
    have := Finset.single_le_sum (f := cst I y) (fun v _ => cst_nonneg I y v) (Finset.mem_univ v)
    linarith
  rw [div_le_iff₀ hK0]
  calc (1 : ℝ) ≤ cst I y v * ‖vec I y u‖ := hv.trans (norm_phi_le I y u v i)
    _ ≤ (∑ v, cst I y v + 1) * ‖vec I y u‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    _ = ‖vec I y u‖ * (∑ v, cst I y v + 1) := mul_comm _ _

end GlobalTheory.CuspGeo

end
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)
open Filter Topology
open GlobalTheory.RootEx.Unfolding (omR omR_val omR_mul omR_smooth orbit_locallyConstant opL step_two)

noncomputable section
namespace GlobalTheory.PosOne.RrStep

theorem rr_step : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p < c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν) (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)) (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (B B₁ : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (_ : BilPos ψ μ p σ B) (_ : ∀ Ψ v, B₁ Ψ v = exUp ν p σ (B Ψ) v) (F : A) (ρ' : Representation ℂ (GL (n' ⊕ Fin (c + 1)) k) (SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))) (_ : IsSrc μ ρ') (Rr : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] ℂ) (_ : ∀ Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), IsQuotInt ν μX μG p (tInt ψ ν μ p σ B F Φ.1) (Rr Φ)) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), IsQuotInt ν μX μG (p + 1) (tInt ψ ν μ (p + 1) σ B₁ F Φ.1) (exUp ν p ρ' Rr Φ) := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p hp hc ψ hψ hψ1 ν hν μ hμ μX hμX μG hμG A _ _ σ hσ B B₁ hB hB₁ F ρ' hρ' Rr hRr Φ
  have := hν.1
  have := secondCountable k
  have := t2Space k
  let ω : Representation ℂ (GL (n' ⊕ Fin (c + 1)) k) (SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) :=
    (omR μ).comp (MonoidHom.inl _ _)
  obtain rfl : ρ' = ω :=
    MonoidHom.ext fun g => LinearMap.ext fun Φ => Subtype.ext (hρ' g Φ)
  have hω : IsSmoothRep ω := fun Φ =>
    (omR_smooth hμ Φ).preimage (continuous_id.prodMk continuous_const)

  let π' : Representation ℂ (GL n' k) (GL n' k →₀ ℂ) :=
    { toFun := fun g => Finsupp.lmapDomain ℂ ℂ (g * ·)
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp [mul_assoc] }
  let π : Representation ℂ (GL n k) (SB (Matrix n n' k)) := (omR μ).comp (MonoidHom.inr _ _)
  let θ : (GL n' k →₀ ℂ) →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] SB (Matrix n n' k) :=
    Finsupp.lsum ℂ fun g₀ => LinearMap.toSpanSingleton ℂ _ (omR μ (g₀⁻¹, 1))
  have hθ : ∀ g h φ Ψ Ψ', Ψ'.1 = om μ g h Ψ.1 → θ (π' g φ) Ψ' = π h (θ φ Ψ) := by
    intro g h φ Ψ Ψ' e
    obtain rfl : Ψ' = omR μ (g, h) Ψ := Subtype.ext e
    induction φ using Finsupp.induction_linear with
    | zero => simp
    | add f₁ f₂ h₁ h₂ => simp only [map_add (f := _), LinearMap.add_apply, h₁, h₂]
    | single g₀ a =>
      simp only [π', MonoidHom.coe_mk, OneHom.coe_mk, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, θ, Finsupp.lsum_single,
        LinearMap.toSpanSingleton_apply, LinearMap.smul_apply, map_smul, π, MonoidHom.coe_comp,
        Function.comp_apply, MonoidHom.inr_apply, omR_mul, smul_eq_mul]
      rw [show ((g * g₀)⁻¹ * g, 1 * h) = (1 * g₀⁻¹, h * 1) from Prod.ext (by group) (by group)]
  have hθ1 : ∀ Ψ, θ (Finsupp.single 1 1) Ψ = Ψ := fun Ψ => by
    simp only [θ, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply, one_smul, inv_one]
    exact Subtype.ext (om_one μ Ψ.1)
  have hb : IsPos ψ p π σ B := ⟨hB.1, fun g φ v => hB.2 g φ (π g φ) v rfl⟩
  have happ : ∀ (q : ℕ) (B₀ : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ)
      (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)),
      tInt ψ ν μ q σ B₀ F Φ.1 = fun h => B₀ (opL hψ ν q (omR μ (1, h) Φ)) (σ h F) := by
    intro q B₀ Φ
    funext h
    exact GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app_coe B₀ (opL hψ ν q (omR μ (1, h) Φ)) ▸ rfl
  have uniq := fun q h1 h2 f =>
    (@GlobalTheory.QuotInt.quotInt_unique_exists k _ _ _ _ _ _ n _ _ c q h1 h2 ν hν.1 μX hμX μG hμG f).1
  have hRr' : ∀ Φ, IsQuotInt ν μX μG p (fun h => B (opL hψ ν p (omR μ (1, h) Φ)) (σ h F)) (Rr Φ) :=
    fun Φ => happ p B Φ ▸ hRr Φ

  have hL : IsNEquiv ψ p ω Rr := fun g hg Φ => by
    rw [← smul_eq_mul, ← map_smul]
    refine uniq p hp hc.le _ _ _ (hRr' _) ?_
    have e : ∀ h, opL hψ ν p (omR μ (1, h) (ω g Φ)) =
        opL hψ ν p (omR μ (1, h) ((ψ (simpleSum g) : ℂ) • Φ)) := fun h => by
      have := GlobalTheory.RootExSource.opE_om_source k n n' c p hp hc.le ψ ν μ (omR μ (1, h) Φ).1 g hg
      rw [← omR_val, omR_mul, mul_one, one_mul] at this
      show opL hψ ν p (omR μ (1, h) (omR μ (g, 1) Φ)) = _
      rw [omR_mul, mul_one, one_mul, map_smul, map_smul]
      exact Subtype.ext this
    exact (funext fun h => congrArg (fun Ψ => B Ψ (σ h F)) (e h)) ▸ hRr' _

  obtain ⟨C, hC, H⟩ := step_two hψ ν (Finsupp.single 1 1) F hp hc hψ1 hμ hσ μX μG hθ hb hB₁ Φ
  have s1 := ((ExchangeSupport.exchange_support k n' (c + 1) p hp (by omega) ψ hψ hψ1 ν _ ω hω Rr Φ).1 hL).1
  obtain ⟨χ, hχ, h1⟩ := _root_.GlobalTheory.RootEx.exists_mem_SB_eq_one_on_compact k n' _ (hC.union s1.2)
  have hT : IsLocallyConstant fun u : n' → k => χ u • ω (rowE (c + 1) p u) Φ :=
    (hχ.1.prodMk ((orbit_locallyConstant hω Φ).comp_continuous ExchangeSupport.continuous_rowE)).comp
      fun q => q.1 • q.2
  obtain ⟨Φ', hΦ'⟩ := _root_.GlobalTheory.exists_weakIntegral_of_isLocallyConstant_of_isCompact (n' → k)
    (Measure.pi fun _ => ν) _ _ hT _ hχ.2
    fun u hu => by simp only [image_eq_zero_of_notMem_tsupport hu, zero_smul]
  simp only [map_smul, smul_eq_mul] at hΦ'
  obtain ⟨z, hz1, hz2⟩ := H χ hχ.1 (fun u hu => h1 u (Or.inl hu)) Φ' hΦ'
  have e : exUp ν p ω Rr Φ = Rr Φ' := by
    rw [hΦ', exUp]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    by_cases hu : u ∈ tsupport fun u : n' → k => Rr (ω (rowE (c + 1) p u) Φ)
    · simp only [h1 u (Or.inr hu), one_mul]
    · have := image_eq_zero_of_notMem_tsupport hu
      simp only [this, mul_zero]
  simp only [hθ1] at hz1 hz2
  rw [happ, e, ← uniq p hp hc.le _ _ _ hz1 (hRr' Φ')]
  exact hz2

end GlobalTheory.PosOne.RrStep
end
end

section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct

theorem _root_.GlobalTheory.T.liftFrame_gram_congr_flagGram : ∀ (I : AutInst) (g : ℕ) {ρ k : ℕ} (e0 f0 : Fin ρ → VA I) (z0 : VA I) (bw bwd : Fin k → VA I) (ew : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), IsRefFrame I g e0 f0 z0 bw bwd ew → I.n = 2 * ρ + k + 1 → ∀ β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), IsLiftFrame I g (flagVec e0 f0 z0 bw bwd) β → ZMod' I g (1 - ew - sigA I ew) ∧ (∀ i j, ZMod' I g (gramIn I β i j - flagGram (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) I.n ρ k i j)) := by
  first | exact @GlobalTheory.FlagBasis.GramLift.gramIn_lift | exact GlobalTheory.FlagBasis.GramLift.gramIn_lift | (intros; apply GlobalTheory.FlagBasis.GramLift.gramIn_lift <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct

theorem _root_.GlobalTheory.T.flagRootSum_dual_eq_symmetricEdge_sum : ∀ (K : Type) [CommRing K] (n ρ k : ℕ), n = 2 * ρ + k + 1 → ∀ ε ε' a₁ a₂ : K, (ε = 1 ∧ ε' = 0) ∨ (ε = 0 ∧ ε' = 1) → a₁ ≠ 0 → a₂ ≠ 0 → ∃ a : Fin n → Fin n → K, (∀ i j, symEdge ρ k i j → a i j ≠ 0) ∧ ∀ M M' : GL (Fin n) K, (M' : Matrix (Fin n) (Fin n) K)ᵀ * flagGram K n ρ k * (M : Matrix (Fin n) (Fin n) K) = flagGram K n ρ k → M ∈ unipSym K n ρ k → a₁ * rootSum ρ k ε (M : Matrix (Fin n) (Fin n) K) + a₂ * rootSum ρ k ε' (M' : Matrix (Fin n) (Fin n) K) = ∑ i, ∑ j, if symEdge ρ k i j then a i j * (M : Matrix (Fin n) (Fin n) K) i j else 0 := by
  first | exact @GlobalTheory.RootSumDual.rootSum_dual_edges | exact GlobalTheory.RootSumDual.rootSum_dual_edges | (intros; apply GlobalTheory.RootSumDual.rootSum_dual_edges <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct

theorem _root_.GlobalTheory.T.flagVec_mem_Lf_and_inMod : ∀ (I : AutInst) (g : ℕ) {ρ k : ℕ} (e0 f0 : Fin ρ → VA I) (z0 : VA I) (bw bwd : Fin k → VA I) (ew : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), IsRefFrame I g e0 f0 z0 bw bwd ew → I.n = 2 * ρ + k + 1 → (∀ j, flagVec e0 f0 z0 bw bwd j ∈ I.Lf) ∧ ∀ y ∈ I.Lf, InMod I g (Set.range fun j : Fin I.n => flagVec e0 f0 z0 bw bwd j.val) y := by
  first | exact @GlobalTheory.FlagBasis.flagVec_mem_and_span | exact GlobalTheory.FlagBasis.flagVec_mem_and_span | (intros; apply GlobalTheory.FlagBasis.flagVec_mem_and_span <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct

theorem _root_.GlobalTheory.T.symmetricUnipotent_mem_of_flagBasisDual : ∀ (K : Type) [CommRing K] (n ρ k : ℕ), n = 2 * ρ + k + 1 → ∀ M M' : GL (Fin n) K, (M' : Matrix (Fin n) (Fin n) K)ᵀ * flagGram K n ρ k * (M : Matrix (Fin n) (Fin n) K) = flagGram K n ρ k → M ∈ unipSym K n ρ k → M' ∈ unipSym K n ρ k := by
  first | exact @GlobalTheory.FlagDual.unipSym_of_dual | exact GlobalTheory.FlagDual.unipSym_of_dual | (intros; apply GlobalTheory.FlagDual.unipSym_of_dual <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct

theorem _root_.GlobalTheory.T.symmetricUnipotent_mem_of_flagCongruence_dual : ∀ (K : Type) [CommRing K] (n ρ k : ℕ), n = 2 * ρ + k + 1 → ∀ M M' : GL (Fin n) K, (M' : Matrix (Fin n) (Fin n) K)ᵀ * flagGram K n ρ k * (M : Matrix (Fin n) (Fin n) K) = flagGram K n ρ k → FlagCond (fun c : K => c = 0) ρ k 1 (M : Matrix (Fin n) (Fin n) K) → FlagCond (fun c : K => c = 0) ρ k 0 (M' : Matrix (Fin n) (Fin n) K) → M ∈ unipSym K n ρ k := by
  first | exact @GlobalTheory.FlagCase.flagCond_dual_unipSym | exact GlobalTheory.FlagCase.flagCond_dual_unipSym | (intros; apply GlobalTheory.FlagCase.flagCond_dual_unipSym <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct

theorem _root_.GlobalTheory.T.unitary_liftedFlagBasis_reduce_mod_level : ∀ (I : AutInst) (g ρ k : ℕ) (β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)), (∀ i j, ZMod' I g (gramIn I β i j - flagGram (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) I.n ρ k i j)) → ∀ (K : Type) [CommRing K] (p : Formalism.L2.Herm.intAf I.F I.E →+* K), (g : K) = 0 → ∀ (x : I.Gf) (m : GL (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)), frGL β m = (x : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) → ((m : Matrix (Fin I.n) (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)).map (p.comp (sigInt I)))ᵀ * flagGram K I.n ρ k * (m : Matrix (Fin I.n) (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)).map p = flagGram K I.n ρ k := by
  first | exact @GlobalTheory.FlagUnit.unitary_reduce | exact GlobalTheory.FlagUnit.unitary_reduce | (intros; apply GlobalTheory.FlagUnit.unitary_reduce <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct

theorem _root_.GlobalTheory.T.characterArgument_congr_rootEntrySum_mod : ∀ (I : AutInst) (g : ℕ) {ρ k : ℕ} (e0 f0 : Fin ρ → VA I) (z0 : VA I) (bw bwd : Fin k → VA I) (ew : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), IsRefFrame I g e0 f0 z0 bw bwd ew → I.n = 2 * ρ + k + 1 → ∀ β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), IsLiftFrame I g (flagVec e0 f0 z0 bw bwd) β → (∀ i j, ZMod' I g (gramIn I β i j - flagGram (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) I.n ρ k i j)) → ∀ x : I.Gf, (x : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) ∈ St β → ZMod' I g (chiArg I e0 f0 z0 bw bwd x - rootSum ρ k ew (matIn I β x)) := by
  first | exact @GlobalTheory.FlagChi.chiArg_sub_rootSum | exact GlobalTheory.FlagChi.chiArg_sub_rootSum | (intros; apply GlobalTheory.FlagChi.chiArg_sub_rootSum <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct

theorem _root_.GlobalTheory.T.levelCongruence_iff_flag_conditions : ∀ (I : AutInst) (g : ℕ) {ρ k : ℕ} (e0 f0 : Fin ρ → VA I) (z0 : VA I) (bw bwd : Fin k → VA I) (ew : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), IsRefFrame I g e0 f0 z0 bw bwd ew → I.n = 2 * ρ + k + 1 → ∀ β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), IsLiftFrame I g (flagVec e0 f0 z0 bw bwd) β → ∀ x : I.Gf, (x : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) ∈ St β → (K2cong I g e0 z0 bw x ↔ FlagCond (ZMod' I g) ρ k ew (matIn I β x)) := by
  first | exact @GlobalTheory.FlagBasis.Cong.k2cong_iff_flagCond | exact GlobalTheory.FlagBasis.Cong.k2cong_iff_flagCond | (intros; apply GlobalTheory.FlagBasis.Cong.k2cong_iff_flagCond <;> assumption)
end

section

open ValuativeRel NumberField IsDedekindDomain

namespace GlobalTheory.LocalResidue

theorem card_residue_of_ringEquiv : ∀ (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (φ : k ≃+* v.adicCompletion F), (∀ a, Valued.v (φ a) ≤ 1 ↔ a ∈ 𝒪[k]) → Nat.card 𝓀[k] = Ideal.absNorm v.asIdeal := by
  intro F _ _ v k _ _ _ _ φ hφ
  let ψ : 𝒪[k] ≃+* v.adicCompletionIntegers F :=
    { toFun := fun a => ⟨φ a, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ((hφ a).2 a.2)⟩
      invFun := fun b => ⟨φ.symm b, (hφ _).1 (by
        rw [RingEquiv.apply_symm_apply]
        exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 b.2)⟩
      left_inv := fun a => Subtype.ext (φ.symm_apply_apply a)
      right_inv := fun b => Subtype.ext (φ.apply_symm_apply b)
      map_mul' := fun a b => Subtype.ext (map_mul φ (a : k) (b : k))
      map_add' := fun a b => Subtype.ext (map_add φ (a : k) (b : k)) }
  have e := IsLocalRing.ResidueField.mapEquiv ψ
  have hF : ∀ s : 𝓞 F, Valued.v (algebraMap F (v.adicCompletion F) s) = v.intValuation s := fun s =>
    (v.valuedAdicCompletion_eq_valuation' _).trans (HeightOneSpectrum.valuation_of_algebraMap v s)
  have hc := GlobalTheory.SplitUnif.card_residueField v (algebraMap F (v.adicCompletion F)) v (fun _ => rfl) fun s => by
    rw [hF, HeightOneSpectrum.intValuation_lt_one_iff_mem]
  rw [Nat.card_congr e.toEquiv, hc]

end GlobalTheory.LocalResidue
end

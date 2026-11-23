module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle502
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle708
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle718
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle710
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle716
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaFiniteParameterProductMeasure
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle721
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle720
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle722
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle015

@[expose] public section

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

theorem term_after : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ b₀ : HermE D ρ, b₀.1.det ≠ 0 → ThTwist → ∀ (χ' : (AE D)ˣ →* Circle), IsHeckeChar D χ' → ∀ θ : InfFam D, IsInfFam θ → ∀ Ω, IsTh ψ χ' θ b₀ m.μ Ω → ∀ (χ : (AE D)ˣ →* Circle) (s : ℂ) (f : G D n → ℂ), IsLaw χ s f → ∀ (g γ : _), γ ∈ GF D p → ∀ (T : Mx D ρ p × Mx D ρ p → Mx D ρ p × Mx D ρ p), (∀ y x : Mx D ρ p, ∃ z' : hermA D ρ, M.emb γ * (M.nzx 0 x * M.sh y) = M.nzx z' (T (y, x)).2 * M.sh (T (y, x)).1 * M.emb γ) → ∀ v : Mx D ρ p × Mx D ρ p, (∀ η : Matrix (Fin ρ) (Fin p) D.host.E, ‖Wz M m ψ b₀ f (M.sh (GlobalTheory.CompanionTheory.FJE.rt η) * M.emb γ * (M.nzx 0 v.2 * (M.sh v.1 * g)))‖ = ‖Wz M m ψ b₀ f (M.sh (GlobalTheory.CompanionTheory.FJE.rt η + (T v).1) * M.emb γ * g)‖) ∧ (∑' η : Matrix (Fin ρ) (Fin p) D.host.E, Wz M m ψ b₀ f (M.sh (GlobalTheory.CompanionTheory.FJE.rt η) * M.emb γ * (M.nzx 0 v.2 * (M.sh v.1 * g)))) * conj (th ψ b₀ (Ω 1) 0 v.2 v.1) = GlobalTheory.CompanionTheory.FJE.Ap ψ b₀ (fun y => Wz M m ψ b₀ f (M.sh y * M.emb γ * g)) (Ω γ) (T v) := by
  intro D n ρ p hn M m ψ hψ b₀ hb₀ hTw χ' hχ' θ hθ Ω hΩ χ s f hf g γ hγ T hT v
  obtain ⟨z', hz'⟩ := hT v.1 v.2
  have hz : M.emb γ * (M.nzx 0 v.2 * M.sh v.1) = M.nzx z' (T v).2 * M.sh (T v).1 * M.emb γ := hz'
  have hterm : ∀ η : Matrix (Fin ρ) (Fin p) D.host.E,
      Wz M m ψ b₀ f (M.sh (rt η) * M.emb γ * (M.nzx 0 v.2 * (M.sh v.1 * g))) =
        chz ψ b₀ z' * (chv ψ b₀ (T v).2 (rt η) * Wz M m ψ b₀ f (M.sh (rt η + (T v).1) * M.emb γ * g)) := by
    intro η
    have e1 : M.sh (rt η) * M.emb γ * (M.nzx 0 v.2 * (M.sh v.1 * g)) =
        M.sh (rt η) * (M.nzx z' (T v).2 * (M.sh (T v).1 * M.emb γ * g)) := by
      calc M.sh (rt η) * M.emb γ * (M.nzx 0 v.2 * (M.sh v.1 * g))
          = M.sh (rt η) * ((M.emb γ * (M.nzx 0 v.2 * M.sh v.1)) * g) := by simp only [mul_assoc]
        _ = M.sh (rt η) * (M.nzx z' (T v).2 * (M.sh (T v).1 * M.emb γ * g)) := by
            rw [hz]; simp only [mul_assoc]
    have e2 : M.sh (rt η) * (M.sh (T v).1 * M.emb γ * g) = M.sh (rt η + (T v).1) * M.emb γ * g := by
      rw [← sh_add M (rt η) (T v).1]; simp only [mul_assoc]
    rw [e1, GlobalTheory.T.coefficient_heisenberg_equivariance M m ψ hψ b₀ χ s f hf (rt η) z' (T v).2 _, e2, mul_assoc]
  obtain ⟨-, hnorm, -, -⟩ := GlobalTheory.CompanionTheory.FJE.CentralChar.chz_facts ψ hψ b₀
  have hchv : ∀ x y : Mx D ρ p, ‖chv ψ b₀ x y‖ = 1 := fun x y => hψ.2.1 _
  have hth : th ψ b₀ (Ω 1) 0 v.2 v.1 = chz ψ b₀ z' * dsum ψ b₀ (Ω γ) (T v).2 (T v).1 := by
    rw [hTw D n ρ p hn M m ψ hψ b₀ hb₀ χ' hχ' θ hθ Ω hΩ γ hγ 0 v.2 v.1 z' (T v).2 (T v).1 hz]
    rfl
  have hcc : chz ψ b₀ z' * conj (chz ψ b₀ z') = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]; simp
  refine ⟨fun η => ?_, ?_⟩
  · rw [hterm η, norm_mul, norm_mul, hnorm, hchv, one_mul, one_mul]
  · simp_rw [hterm]
    rw [tsum_mul_left, hth, map_mul, Ap]
    have hd : (∑' η : Matrix (Fin ρ) (Fin p) D.host.E,
        chv ψ b₀ (T v).2 (rt η) * Wz M m ψ b₀ f (M.sh (rt η + (T v).1) * M.emb γ * g)) =
        dsum ψ b₀ (fun y => Wz M m ψ b₀ f (M.sh y * M.emb γ * g)) (T v).2 (T v).1 := rfl
    rw [hd]
    calc _ = (chz ψ b₀ z' * conj (chz ψ b₀ z')) *
          (dsum ψ b₀ (fun y => Wz M m ψ b₀ f (M.sh y * M.emb γ * g)) (T v).2 (T v).1 *
            conj (dsum ψ b₀ (Ω γ) (T v).2 (T v).1)) := by ring
      _ = _ := by rw [hcc, one_mul]

end GlobalTheory.CompanionTheory.FJE
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE.Domination

theorem summable_tsum_le_of_shift {ι : Type*} [AddCommGroup ι] {F c : ι → ℝ} (ζ : ι) (hF : ∀ i, 0 ≤ F i)
    (h : ∀ i, F (i + ζ) ≤ c i) (hc : Summable c) : Summable F ∧ ∑' i, F i ≤ ∑' i, c i := by
  have hs : Summable (F ∘ Equiv.addRight ζ) := Summable.of_nonneg_of_le (fun _ => hF _) h hc
  refine ⟨(Equiv.addRight ζ).summable_iff.1 hs, ?_⟩
  rw [← (Equiv.addRight ζ).tsum_eq F]
  exact hs.tsum_le_tsum h hc

variable {D : D7} {n ρ p : ℕ} {hn : ρ + p = n}

theorem rt_add_add (η ζ : Matrix (Fin ρ) (Fin p) D.host.E) (y : Mx D ρ p) :
    GlobalTheory.CompanionTheory.FJE.rt (η + ζ) + y = GlobalTheory.CompanionTheory.FJE.rt η + (GlobalTheory.CompanionTheory.FJE.rt ζ + y) := by
  have : GlobalTheory.CompanionTheory.FJE.rt (η + ζ) = GlobalTheory.CompanionTheory.FJE.rt η + GlobalTheory.CompanionTheory.FJE.rt ζ := by
    ext i j
    exact map_add (incA D) _ _
  rw [this, add_assoc]

theorem norm_Wz_shift (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ)
    (b₀ : HermE D ρ) (χ : (AE D)ˣ →* Circle) (s : ℂ) (f : G D n → ℂ) (hf : IsLaw χ s f) (g : G D n) (e : G D p)
    (η ζ₂ : Matrix (Fin ρ) (Fin p) D.host.E) (y' x₀ y₀ : Mx D ρ p) (z' : hermA D ρ)
    (hz : M.emb e * (M.nzx 0 x₀ * M.sh y₀) = M.nzx z' (GlobalTheory.CompanionTheory.FJE.rt ζ₂) * M.sh y' * M.emb e) :
    ‖Wz M m ψ b₀ f (M.sh (GlobalTheory.CompanionTheory.FJE.rt η + y') * M.emb e * g)‖ =
      ‖Wz M m ψ b₀ f (M.sh (η.map (incA D)) * M.emb e * (M.nzx 0 x₀ * (M.sh y₀ * g)))‖ := by
  have e1 : M.sh (η.map (incA D)) * M.emb e * (M.nzx 0 x₀ * (M.sh y₀ * g)) =
      M.sh (GlobalTheory.CompanionTheory.FJE.rt η) * (M.nzx z' (GlobalTheory.CompanionTheory.FJE.rt ζ₂) * (M.sh y' * M.emb e * g)) := by
    calc _ = M.sh (η.map (incA D)) * (M.emb e * (M.nzx 0 x₀ * M.sh y₀)) * g := by
          simp only [mul_assoc]
      _ = _ := by
          rw [hz]
          simp only [mul_assoc]
  have e2 : M.sh (GlobalTheory.CompanionTheory.FJE.rt η + y') * M.emb e * g =
      M.sh (GlobalTheory.CompanionTheory.FJE.rt η) * (M.sh y' * M.emb e * g) := by
    rw [← GlobalTheory.CompanionTheory.FJE.sh_add]
    simp only [mul_assoc]
  have hv : ‖GlobalTheory.CompanionTheory.FJE.chv ψ b₀ (GlobalTheory.CompanionTheory.FJE.rt ζ₂) (GlobalTheory.CompanionTheory.FJE.rt η)‖ = 1 := hψ.2.1 _
  rw [e1, e2, GlobalTheory.T.coefficient_heisenberg_equivariance M m ψ hψ b₀ χ s f hf, norm_mul, norm_mul,
    (GlobalTheory.CompanionTheory.FJE.CentralChar.chz_facts ψ hψ b₀).2.1, hv, one_mul, one_mul]

theorem apply_add_symm {A : Type*} [TopologicalSpace A] [AddCommGroup A] (T : (A × A) ≃ₜ+ (A × A)) {a₁ a₂ b₁ b₂ y : A}
    (h : T (a₁, a₂) = (b₁, b₂)) : T (a₁ + (T.symm (y, 0)).1, a₂ + (T.symm (y, 0)).2) = (b₁ + y, b₂) := by
  have e : (a₁ + (T.symm (y, 0)).1, a₂ + (T.symm (y, 0)).2) = (a₁, a₂) + T.symm (y, 0) := rfl
  rw [e, map_add (f := _), h, T.apply_symm_apply]
  simp



theorem domination : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p)
    (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (χ : (AE D)ˣ →* Circle) (s : ℂ)
    (f : G D n → ℂ), IsLaw χ s f → ∀ g : G D n,
    (∀ C : Set (G D n), IsCompact C →
      ∃ c : GlobalTheory.Eis.Cosets (P D p) (GF D p) × Matrix (Fin ρ) (Fin p) D.host.E → ℝ, Summable c ∧
        ∀ g ∈ C, ∀ u, ‖Wz M m ψ b₀ f (M.sh (u.2.map (incA D)) * M.emb (u.1.out : GF D p) * g)‖ ≤ c u) →
    ∃ t : GlobalTheory.Eis.Cosets (P D p) (GF D p) → ℝ, Summable t ∧
      ∀ (q : GlobalTheory.Eis.Cosets (P D p) (GF D p)) (y : Mx D ρ p),
        Summable (fun η : Matrix (Fin ρ) (Fin p) D.host.E =>
          ‖Wz M m ψ b₀ f (M.sh (GlobalTheory.CompanionTheory.FJE.rt η + y) * M.emb (q.out : GF D p) * g)‖) ∧
        ∑' η : Matrix (Fin ρ) (Fin p) D.host.E,
          ‖Wz M m ψ b₀ f (M.sh (GlobalTheory.CompanionTheory.FJE.rt η + y) * M.emb (q.out : GF D p) * g)‖ ≤ t q := by
  intro D n ρ p hn M m ψ hψ b₀ χ s f hf g hdom
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := lattice_Mx D ρ p
  have hΦ : Continuous fun v : Mx D ρ p × Mx D ρ p => M.nzx 0 v.2 * (M.sh v.1 * g) := by
    have h1 : Continuous fun v : Mx D ρ p × Mx D ρ p => M.nzx 0 v.2 :=
      M.nzx_cont.comp (continuous_const.prodMk continuous_snd)
    have h2 : Continuous fun v : Mx D ρ p × Mx D ρ p => M.sh v.1 := M.sh_cont.comp continuous_fst
    exact h1.mul (h2.mul continuous_const)
  obtain ⟨c, hc, hb⟩ := hdom _ ((hK.prod hK).image hΦ)
  refine ⟨fun q => ∑' η, c (q, η), hc.prod, fun q y => ?_⟩
  obtain ⟨T, hT1, -, hT3⟩ := GlobalTheory.T.lattice_translation_preserved M ((q.out : GF D p) : G D p) (q.out : GF D p).2
  obtain ⟨a₁, ha₁, hy⟩ := hKc (T.symm (y, 0)).1
  obtain ⟨a₂, ha₂, hx⟩ := hKc (T.symm (y, 0)).2
  obtain ⟨ξ₁, rfl⟩ : ∃ ξ, GlobalTheory.CompanionTheory.FJE.rt ξ = a₁ := ha₁
  obtain ⟨ξ₂, rfl⟩ : ∃ ξ, GlobalTheory.CompanionTheory.FJE.rt ξ = a₂ := ha₂
  obtain ⟨ζ₁, ζ₂, hζ⟩ := hT1 ξ₁ ξ₂
  have hTv := apply_add_symm (y := y) T hζ
  obtain ⟨z', hz'⟩ := hT3 (GlobalTheory.CompanionTheory.FJE.rt ξ₁ + (T.symm (y, 0)).1) (GlobalTheory.CompanionTheory.FJE.rt ξ₂ + (T.symm (y, 0)).2)
  rw [hTv] at hz'
  refine summable_tsum_le_of_shift ζ₁ (fun _ => norm_nonneg _) (fun η => ?_) (hc.prod_factor q)
  rw [rt_add_add, norm_Wz_shift M m ψ hψ b₀ χ s f hf g _ η ζ₂ _ _ _ z' hz']
  exact hb _ ⟨(_, _), ⟨hy, hx⟩, rfl⟩ (q, η)

end GlobalTheory.CompanionTheory.FJE.Domination
end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.integral_of_character_trivial_on_lattice : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (v : Pl D), GoodPsi D ψ v → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) (Fv D.host.F v)), (∀ X : Matrix (Fin n) (Fin n) (Fv D.host.F v), (∀ i j, X i j ∈ v.adicCompletionIntegers D.host.F) → psiV D.host.F ψ v (Matrix.trace (X * T)) = 1) → ∀ i j, T i j ∈ v.adicCompletionIntegers D.host.F := by
  first | exact @GlobalTheory.CompanionTheory.Jp.DualInt.mem_of_dual_integral | exact GlobalTheory.CompanionTheory.Jp.DualInt.mem_of_dual_integral | (intros; apply GlobalTheory.CompanionTheory.Jp.DualInt.mem_of_dual_integral <;> assumption)
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Jp.B3

variable {D : D7} {n : ℕ} {v : Pl D}

theorem term_eq {χ : (AE D)ˣ →* Circle} {τ : D.host.E →ₐ[D.host.F] Fv D.host.F v} (hχ : GoodChi D χ v τ) {z : ℂ}
    {f : G D n → ℂ} (hf : IsLaw χ z f) (hK : ∀ k ∈ KAt D n v, ∀ g, f (g * k) = f g) {nb : hermA D n → G D n}
    (hnb : IsNMap nb) (C : Cut D n v) (g : G D n) (p₀ : PV D n v) {k₀ : GLoc D.sp.cm.sig (Jst D n) v}
    (hk₀ : k₀ ∈ GlobalTheory.LocIntw.KUpFin D.sp.cm.sig (Jst D n) v) (e₀ : proj D.sp.cm.sig (Jst D n) v g = p₀ * k₀)
    {k : G D n} (hk : k ∈ KAt D n v) {x : hermA D n} (hx : x ∈ C.s) :
    f (g * (k * nb x)) = sphV D n v z (k₀ * proj D.sp.cm.sig (Jst D n) v (k * nb x)) * f g := by
  obtain ⟨p₁, k₁, hk₁, e₁⟩ := GlobalTheory.LocIntw.exists_mul_fin (GlobalTheory.LocIntw.exists_mul_adele D n) v
    (k₀ * proj D.sp.cm.sig (Jst D n) v (k * nb x))
  have hu : k * nb x ∈ atPts D.sp.cm.sig (Jst D n) {v} := mul_mem hk.2 (nb_mem_atPts hnb C hx)
  rw [shift hf hK g p₀ p₁ hk₀ hk₁ e₀ hu e₁, lawV, chi_one hχ hnb hk₀ hk₁ hk x p₁ e₁, e₁, Circle.coe_one, one_mul]
  congr 1
  exact (congrArg (fun r => npow r (z + (n : ℂ) / 2))
    (GlobalTheory.LocIntw.hgtUp_mul (GlobalTheory.LocIntw.isIwasawaUp_fin D n v) p₁ hk₁)).symm

theorem eigen_of_rightInvariant : SectionEigenfunctionMaximalCompact := by
  intro D n χ nb hnb v τ hχ C νv hν z c hc f hf hK g
  obtain ⟨p₀, k₀, hk₀, e₀⟩ := GlobalTheory.LocIntw.exists_mul_fin (GlobalTheory.LocIntw.exists_mul_adele D n) v
    (proj D.sp.cm.sig (Jst D n) v g)
  have hκ : emb D.sp.cm.sig (Jst D n) v k₀ ∈ KAt D n v :=
    ⟨GlobalTheory.LocIntw.emb_mem_KUpAd hk₀, by rw [← range_emb]; exact ⟨_, rfl⟩⟩
  have key : ∀ k : KAt D n v, cutR nb C f (g * k) =
      f g * (fun k : KAt D n v => ∑ x ∈ C.s, C.co x * sphV D n v z (proj D.sp.cm.sig (Jst D n) v ((k : G D n) * nb x)))
        (⟨_, hκ⟩ * k) := by
    intro k
    simp only [PositivityTheory.Rg.Rsw.L.cutR, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [mul_assoc g, term_eq hχ hf hK hnb C g p₀ hk₀ e₀ k.2 hx]
    have e : proj D.sp.cm.sig (Jst D n) v ((((⟨_, hκ⟩ : KAt D n v) * k : KAt D n v) : G D n) * nb x) =
        k₀ * proj D.sp.cm.sig (Jst D n) v ((k : G D n) * nb x) := by
      rw [Subgroup.coe_mul, mul_assoc, map_mul, proj_emb_self]
    rw [e]
    ring
  simp only [key]
  rw [integral_const_mul, integral_mul_left_eq_self
    (fun k : KAt D n v => ∑ x ∈ C.s, C.co x * sphV D n v z (proj D.sp.cm.sig (Jst D n) v ((k : G D n) * nb x))) ⟨_, hκ⟩,
    hc, mul_comm]

end GlobalTheory.CompanionTheory.Jp.B3

end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.orbit_measure_GL_right_scaling : ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ x₀ (g : GL (Fin t) (AE D)), (nuT hn I μ x₀).map (fun z => (z.1, mm z.2 g.1)) = ((absA D (Matrix.GeneralLinearGroup.det g))⁻¹ ^ (W.rank + t) : ℝ≥0) • nuT hn I μ x₀ := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.Cov.nuT_cov | exact GlobalTheory.CompanionTheory.ColumnSplitting.Cov.nuT_cov | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.Cov.nuT_cov <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unipotent_shift_invariance : Shift := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.shift | exact GlobalTheory.CompanionTheory.ColumnSplitting.shift | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.shift <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

theorem _root_.GlobalTheory.T.reverse_ordered_product_has_socle : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → LSegJacquet k → LUnlinkedIrr k → LUnlinkedComm k → ∀ {h N : ℕ} (Γ : Fin h → Segment k) (y : Fin h → IrrGL (k := k)) (hd : ∑ a, (y a).1 = N), IsRevOrdered Γ → (∀ i, IsLSeg (Γ i) (y i).rep) → ∃ τ : IrrRep (GL (Fin N) k), IsSocle τ.ρ (prodIrr y hd) := by
  first | exact @GlobalTheory.CompanionTheory.SocleRev.exists_isSocle_prodIrr_of_isRevOrdered | exact GlobalTheory.CompanionTheory.SocleRev.exists_isSocle_prodIrr_of_isRevOrdered | (intros; apply GlobalTheory.CompanionTheory.SocleRev.exists_isSocle_prodIrr_of_isRevOrdered <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

theorem _root_.GlobalTheory.T.langlands_injective_of_socle : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), LSocleGL k → LSegJacquet k → LInjective k := by
  first | exact @GlobalTheory.CompanionTheory.Multisegment.lInjective | exact GlobalTheory.CompanionTheory.Multisegment.lInjective | (intros; apply GlobalTheory.CompanionTheory.Multisegment.lInjective <;> assumption)
end

section

open scoped Classical
namespace PositivityTheory.Rg.BcB.SpectralAccumulation

theorem _root_.GlobalTheory.T.finite_discriminant_identity : PositivityTheory.Rg.BcB.SpectralAccumulation.FinDisc := by
  first | exact @GlobalTheory.CompanionTheory.FinDiscP.main | exact GlobalTheory.CompanionTheory.FinDiscP.main | (intros; apply GlobalTheory.CompanionTheory.FinDiscP.main <;> assumption)
end SpectralAccumulation
end BcB
end Rg
end PositivityTheory
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.height_power_summable_rational_hermitian : ∀ (D : D7) (ρ : ℕ) (H : G D ρ → ℝ≥0), IsHt H → ∀ (w : G D ρ) (nb : hermA D ρ → G D ρ),
  mat w = blk4 0 1 (-1) 0 → (∀ z : hermA D ρ, mat (nb z) = blk4 1 z.1 0 1) → ∀ τ : ℝ, (ρ : ℝ) < τ →
    Summable (fun ζ : ratHerm D ρ => (H (w * nb ζ.1) : ℝ) ^ τ) := by
  first | exact @GlobalTheory.CompanionTheory.HermSum.summable_height_rpow | exact GlobalTheory.CompanionTheory.HermSum.summable_height_rpow | (intros; apply GlobalTheory.CompanionTheory.HermSum.summable_height_rpow <;> assumption)
end

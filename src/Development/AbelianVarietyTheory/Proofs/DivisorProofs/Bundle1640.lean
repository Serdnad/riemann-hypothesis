module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1598
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle359
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzHaarWeil
import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle364
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle005
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle404
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle662
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1591
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle518
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle547
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle917
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1593
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle002
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle002
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1595
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

@[expose] public section

section

open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open scoped ComplexOrder ContDiff ComplexConjugate

set_option autoImplicit false

noncomputable section

open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)

namespace GlobalTheory.CxForm.DelForm

theorem coefwise_del_sum_smul {n : ℕ} {ι : Type} [Fintype ι] {v : V n} (g : ι → V n → ℂ) (Q : ι → V n → Alt n)
    (hg : ∀ k, DifferentiableAt ℝ (g k) v) (hQ : ∀ k S, DifferentiableAt ℝ (fun w => (bas n).repr (Q k w) S) v)
    (ξ : V n) :
    coefwise (fun f => del f v ξ) (fun w => ∑ k, g k w • Q k w) =
      ∑ k, (del (g k) v ξ • Q k v + g k v • coefwise (fun f => del f v ξ) (Q k)) := by
  refine (bas n).ext_elem fun S => ?_
  have e : (fun x => (bas n).repr (∑ k, g k x • Q k x) S) = fun x => ∑ k, g k x * (bas n).repr (Q k x) S :=
    funext fun x => by simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]

  rw [FormMul.repr_coefwise, e,
  del_sum (A := fun k x => g k x * (bas n).repr (Q k x) S) (fun k _ => (hg k).mul (hQ k S)),
  ContinuousLinearMap.sum_apply, map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [del_mul (hg k) (hQ k S), map_add (f := _), map_smul, map_smul, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.smul_apply,
    FormMul.repr_coefwise, smul_eq_mul, smul_eq_mul, add_comm]

theorem delAt_sum_smul : ∀ {n : ℕ} {ι : Type} [Fintype ι] {v : ReciprocityTheory.L2DbarEstimates.V n} (g : ι → ReciprocityTheory.L2DbarEstimates.V n → ℂ)
    (Q : ι → ReciprocityTheory.L2DbarEstimates.V n → GlobalTheory.CxForm.Alt n), (∀ k, DifferentiableAt ℝ (g k) v) →
    (∀ k S, DifferentiableAt ℝ (fun w => (GlobalTheory.CxForm.bas n).repr (Q k w) S) v) →
    GlobalTheory.CxForm.delAt (fun w => ∑ k, g k w • Q k w) v =
      ∑ k, (GlobalTheory.CxForm.DelForm.dOne (g k) v * Q k v + g k v • GlobalTheory.CxForm.delAt (Q k) v) := by
  intro n ι _ v g Q hg hQ
  simp only [delAt, dOne, coefwise_del_sum_smul g Q hg hQ, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum, mul_add,
    mul_smul_comm, smul_mul_assoc, ← Finset.sum_add_distrib]
  exact Finset.sum_comm

end GlobalTheory.CxForm.DelForm
end
end

section

open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open scoped ComplexOrder ContDiff ComplexConjugate

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CxForm.DelForm

open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)

theorem sum_coord_smul_coordVec {n : ℕ} (w : V n) : ∑ b, w b • coordVec b = w := by
  ext i
  simp [coordVec, Pi.single_apply]

theorem dOne_comp_holo {n : ℕ} {φ : V n → V n} {c : V n → ℂ} {v : V n}
    (hc : DifferentiableAt ℝ c (φ v)) (hφ : DifferentiableAt ℂ φ v) :
    dOne (fun w => c (φ w)) v = pull (fderiv ℂ φ v) (dOne c (φ v)) := by
  have key (a : Fin n) : del (fun w => c (φ w)) v (coordVec a) =
      ∑ b, fderiv ℂ φ v (coordVec a) b * del c (φ v) (coordVec b) := by
    rw [del_comp_holo hc hφ]
    conv_lhs => rw [← sum_coord_smul_coordVec (fderiv ℂ φ v (coordVec a))]

    simp [map_sum, map_smul, smul_eq_mul]

  simp only [dOne, map_sum, map_smul, (pull_dz _ _).1, Finset.smul_sum, smul_smul, key, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [mul_comm]

end GlobalTheory.CxForm.DelForm
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical


theorem _root_.GlobalTheory.T.adelic_schwartz_haar_weil : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), GlobalTheory.WeilL2Words.IsStdInf F ψ →
    ∀ (μ : @MeasureTheory.Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _)), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)), ∀ φ ∈ GlobalTheory.WeilM.schA F κ,
      Filter.Tendsto (fun n : ℕ => GlobalTheory.WeilL2Words.l2A F μ (fun a => ((n : ℂ) + 1) *
        (GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair F (((n : ℝ) + 1)⁻¹ • h)) φ a - φ a) - GlobalTheory.WeilL2Words.dS F ψ h φ a))
        Filter.atTop (nhds 0) := by
  first | exact @GlobalTheory.WeilL2Convergence.tendsto_l2A_diffQuot | exact GlobalTheory.WeilL2Convergence.tendsto_l2A_diffQuot | (intros; apply GlobalTheory.WeilL2Convergence.tendsto_l2A_diffQuot <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical


theorem _root_.GlobalTheory.T.isStandardArchimedeanAddChar_of_standardChar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → GlobalTheory.WeilL2Words.IsStdInf D.host.F ψ := by
  first | exact @GlobalTheory.WeilL2Words.StdTheta.isStdInf_of_isStdChar | exact GlobalTheory.WeilL2Words.StdTheta.isStdInf_of_isStdChar | (intros; apply GlobalTheory.WeilL2Words.StdTheta.isStdInf_of_isStdChar <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

theorem _root_.GlobalTheory.T.unitary_frames_strong_approximation : GlobalTheory.Published.TamagawaSpecialUnitary → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M m : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (Ψ : Finset (E →+* ℂ)) (X : Fin m → Data E r) (g : Fin m → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)) (x0 : ∀ i, Frame (X i).Ψ r) (S : Finset (Fin m)) (g0 : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)), 2 ≤ r → 3 ≤ M → Unr E → SelfDualLat G Λ → IsUA (IsCMField.complexConj E) G g0 → (∀ i, IsUA (IsCMField.complexConj E) G (g i)) → (∀ i ∈ S, TEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M g0.det (g i).det) → (∀ i ∈ S, ∀ j ∈ S, UEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M (g i) (g j) → i = j) → (∀ i ∈ S, (X i).Gm = G ∧ (X i).Ψ = Ψ ∧ ((X i).Λ : Set (Fin r → E)) = latOf (maximalRealSubfield E) (g i) (Λ : Set (Fin r → E)) ∧ (∀ γ, γ ∈ (X i).Γ ↔ IsUStab G (X i).Λ γ ∧ ∀ x ∈ (X i).Λ, ∃ y ∈ (X i).Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ x - x = M • y) ∧ IsOrth (X i) (x0 i)) → ∑ i ∈ S, covolume (inReal (X i).Ψ (X i).Gm (X i).Γ) (realSU (X i).Ψ (X i).Gm) (riemHaar (X i).Ψ (X i).Gm (x0 i)) ≤ ENNReal.ofReal ((M : ℝ) ^ (2 * fdeg E * r ^ 2) * rdE E ^ ((fdeg E : ℝ) * ((r : ℝ) ^ 2 - 1) / 2) * (Real.sqrt r * ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i) ^ fdeg E) := by
  first | exact @GlobalTheory.ClassSum.sum_covolume_le | exact GlobalTheory.ClassSum.sum_covolume_le | (intros; apply GlobalTheory.ClassSum.sum_covolume_le <;> assumption)
end

section

noncomputable section

open MeasureTheory GlobalTheory.SplitFlip
open scoped Topology Matrix

namespace GlobalTheory.FullRankCoinv

theorem sb_right_invariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n d : ℕ) (Ψ : Matrix (Fin n) (Fin d) k → ℂ), Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) →
    ∃ U ∈ nhds (1 : GL (Fin d) k), ∀ u ∈ U, ∀ X : Matrix (Fin n) (Fin d) k, Ψ (X * u.val) = Ψ X := by
  intro k _ _ _ _ n d Ψ hΨ
  have h1 : ∀ᶠ u in 𝓝 (1 : GL (Fin d) k), ∀ X ∈ tsupport Ψ, Ψ (X * u.val) = Ψ X := by
    refine IsCompact.eventually_forall_of_forall_eventually hΨ.2 fun y _ => ?_
    have h2 : IsLocallyConstant fun q : GL (Fin d) k × Matrix (Fin n) (Fin d) k => (Ψ (q.2 * q.1.val), Ψ q.2) :=
      (hΨ.1.comp_continuous (by fun_prop)).prodMk (hΨ.1.comp_continuous continuous_snd)
    filter_upwards [h2.eventually_eq (1, y)] with q hq
    simp only [Prod.mk.injEq, Units.val_one, Matrix.mul_one] at hq
    rw [hq.1, hq.2]
  have h3 : ∀ᶠ u in 𝓝 (1 : GL (Fin d) k), ∀ X ∈ tsupport Ψ, Ψ (X * (u⁻¹).val) = Ψ X := by
    have ht : Filter.Tendsto (fun u : GL (Fin d) k => u⁻¹) (𝓝 1) (𝓝 1) := by
      simpa using (continuous_inv.tendsto (1 : GL (Fin d) k))
    exact ht.eventually h1
  refine ⟨_, h1.and h3, fun u hu X => ?_⟩
  by_cases hX : X ∈ tsupport Ψ
  · exact hu.1 X hX
  by_cases hX' : X * u.val ∈ tsupport Ψ
  · have := hu.2 _ hX'
    rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hX, image_eq_zero_of_notMem_tsupport hX']

theorem fibre_coinvariants : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n d : ℕ) (ν : kˣ →* ℂˣ), n ≤ d → GlobalTheory.SmGL.IsSmoothChar ν →
    ∃ Z : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] (GL (Fin d) k → ℂ),
      (∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, Z Ψ ∈ GlobalTheory.FullRankCoinv.indSp k n d ν) ∧
      (∀ f ∈ GlobalTheory.FullRankCoinv.indSp k n d ν, ∃ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, Z Ψ = f) ∧
      (∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, Z Ψ = 0 → Ψ ∈ GlobalTheory.FullRankCoinv.augRk n d ν) ∧
      ∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, ∀ h₀ : GL (Fin d) k,
        Z (fun Y => Ψ (Y * h₀.1)) = fun h => Z Ψ (h * h₀) := by
  intro k _ _ _ _ n d ν hnd hν
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  let Z₀ : fullRk k n d →ₗ[ℂ] (GL (Fin d) k → ℂ) :=
    { toFun := fun Ψ h => smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ.1 (Y0 k n d * h.val)
      map_add' := fun Ψ Φ => by
        funext h
        simp only [smallF, Submodule.coe_add, Pi.add_apply]
        rw [← integral_add (GlobalTheory.T.integrable_full_rank_zeta k n d ν hν Ψ.1 Ψ.2 _) (GlobalTheory.T.integrable_full_rank_zeta k n d ν hν Φ.1 Φ.2 _)]
        congr 1; funext g; ring
      map_smul' := fun c Ψ => by
        funext h
        simp only [smallF, SetLike.val_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1; funext g; ring }
  obtain ⟨Z, hZ⟩ := LinearMap.exists_extend Z₀
  have hZΨ : ∀ Ψ (hΨ : Ψ ∈ fullRk k n d),
      Z Ψ = fun h => smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ (Y0 k n d * h.val) :=
    fun Ψ hΨ => LinearMap.congr_fun hZ ⟨Ψ, hΨ⟩
  refine ⟨Z, fun Ψ hΨ => ?_, fun f hf => ?_, fun Ψ hΨ h0 => ?_, fun Ψ hΨ h₀ => ?_⟩
  · rw [hZΨ Ψ hΨ]
    refine ⟨?_, fun b h D hD => ?_⟩
    · obtain ⟨U, hU, hinv⟩ := sb_right_invariant k n d Ψ hΨ.1
      refine ⟨U, hU, fun h u hu => ?_⟩
      simp only [smallF]
      congr 1; funext g
      rw [Units.val_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hinv u hu, Matrix.mul_assoc]
    · have e1 : Y0 k n d * (b * h).val = D.val * (Y0 k n d * h.val) := by
        rw [Units.val_mul, ← Matrix.mul_assoc, hD, Matrix.mul_assoc]
      have key := smallF_mul_left (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ D (Y0 k n d * h.val)
      simp only [Fintype.card_fin] at key
      show smallF _ ν Ψ (Y0 k n d * (b * h).val) = _
      rw [e1]
      beta_reduce
      rw [← key, Units.val_inv_eq_inv_val, neg_div, apow_neg]
      have h1 : (ν (gdet D) : ℂ) ≠ 0 := Units.ne_zero _
      have h2 := apow_ne_zero (gdet D) ((d : ℂ) / 2)
      field_simp
  · obtain ⟨Ψ, hΨ, hf'⟩ := GlobalTheory.T.full_rank_zeta_surjective k n d ν hnd hν f hf
    exact ⟨Ψ, hΨ, by rw [hZΨ Ψ hΨ]; funext h; exact hf' h⟩
  · refine GlobalTheory.T.full_rank_zeta_kernel k n d ν hnd hν Ψ hΨ fun h => ?_
    have := congrFun h0 h
    rwa [hZΨ Ψ hΨ] at this
  · have hmem : (fun Y => Ψ (Y * h₀.1)) ∈ fullRk k n d := by
      let e : Matrix (Fin n) (Fin d) k ≃ₜ Matrix (Fin n) (Fin d) k :=
        { toFun := fun X => X * h₀.1
          invFun := fun X => X * (h₀⁻¹).1
          left_inv := fun X => by simp [Matrix.mul_assoc]
          right_inv := fun X => by simp [Matrix.mul_assoc]
          continuous_toFun := by fun_prop
          continuous_invFun := by fun_prop }
      refine ⟨⟨hΨ.1.1.comp_continuous e.continuous, hΨ.1.2.comp_homeomorph e⟩, fun Y hY => hΨ.2 _ ?_⟩
      rwa [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnits_det_units h₀)]
    rw [hZΨ _ hmem, hZΨ _ hΨ]
    funext h
    simp only [smallF, Units.val_mul, Matrix.mul_assoc]

end GlobalTheory.FullRankCoinv
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin

noncomputable section
namespace GlobalTheory.UPel.HT.LieLin.LieAlgebraMultiplication
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {k : Type} [Field k] (t : Sp k ⟶ S)

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : C →+* A) :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem left_iff (c : k) (u v : epsPt t ⟶ G) :
    u.left = spMap (epsScale c) ≫ v.left ↔ u = smT t c v := by
  constructor
  · intro h; apply Over.OverMorphism.ext; rw [h, smT_left]; rfl
  · rintro rfl; rw [smT_left]; rfl

theorem tang_iff (v : epsPt t ⟶ G) :
    spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk t ⟶ G).left ↔ smT t 0 v = 1 := by
  have e0 : (epsMul (0 : k)) = (algebraMap k (DualNumber k)).comp (TrivSqZeroExt.fstHom k k k).toRingHom := by
    refine RingHom.ext fun x => ?_
    ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  constructor
  · intro h
    apply Over.OverMorphism.ext
    have h1 : (1 : epsPt t ⟶ G) = (Over.homMk (spMap (algebraMap k (DualNumber k))) rfl : epsPt t ⟶ Over.mk t) ≫ 1 :=
      (MonObj.comp_one _).symm
    rw [smT_left, e0, ← spMap_comp', Category.assoc, h, h1]
    rfl
  · intro h
    have hw : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (algebraMap k (DualNumber k)) ≫ t = t := by
      rw [← Category.assoc, spMap_comp']
      have : ((TrivSqZeroExt.fstHom k k k).toRingHom.comp (algebraMap k (DualNumber k))) = RingHom.id k := by
        refine RingHom.ext fun x => ?_; simp
      rw [this]
      simp [spMap]
    let s : Over.mk t ⟶ epsPt t := Over.homMk (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) hw
    have h2 := congrArg (fun φ => (s ≫ φ).left) h
    simp only [MonObj.comp_one] at h2
    rw [← h2]
    change _ = s.left ≫ (smT t 0 v).left
    rw [smT_left, ← Category.assoc]
    change _ = (spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (epsMul 0)) ≫ v.left
    rw [spMap_comp']
    congr 2
    refine RingHom.ext fun x => ?_
    simp [epsMul, s]

end GlobalTheory.UPel.HT.LieLin.LieAlgebraMultiplication

namespace GlobalTheory.UPel.HT.LieLin.LieAlgebraMultiplication
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {k : Type} [Field k] (t : Sp k ⟶ S)
variable {O : Type} [CommRing O] (act : OAct O G) (τ : O →+* k)

theorem lieEigen_tan {w : epsPt t ⟶ G} (h : IsLieEigen act t τ w) : smT t 0 w = 1 := (tang_iff t w).1 h.1

theorem mem_iff (x : TanM t G) :
    x ∈ eigSub (actR (x0 := t) (S := k) act) τ ↔ IsLieEigen act t τ (tv x) := by
  rw [mem_eigSub]
  refine ⟨fun h => ⟨(tang_iff t _).2 (tv_mem x), fun a => ?_⟩, fun h a => ?_⟩
  · rw [left_iff]
    have := congrArg tv (h a)
    rw [tv_actR, tv_smul] at this
    exact this
  · apply tanM_ext
    rw [tv_actR, tv_smul]
    exact (left_iff t _ _ _).1 (h.2 a)

theorem prod_eq {m : ℕ} (x : Fin m → TanM t G) (c : Fin m → k) :
    (List.ofFn (fun i => smT t (c i) (tv (x i)))).prod = tv (∑ i, c i • x i) := by
  rw [List.prod_ofFn]
  show _ = ((Additive.toMul (∑ i, c i • x i) : tanSub t G) : overAt t (DualNumber k) ⟶ G)
  rw [toMul_sum]
  change _ = (tanSub t G).subtype (∏ i, Additive.toMul (c i • x i))
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact (tv_smul (c i) (x i)).symm

end GlobalTheory.UPel.HT.LieLin.LieAlgebraMultiplication

namespace GlobalTheory.UPel.HT.LieLin
open ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj LieAlgebraMultiplication

theorem lieMult_iff_finrank : ∀ (O : Type) [CommRing O] (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G]
  (act : ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G) (k : Type) [Field k] (t : Sp k ⟶ S) (τ : O →+* k) (m : ℕ),
    Module.Finite k (ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM t G) →
      (LieMult act t τ m ↔ Module.finrank k (eigSub (ReciprocityTheory.ChartRestriction.G.PullbackSections.actR (x0 := t) (S := k) act) τ) = m) := by
  intro O _ S G _ _ act k _ t τ m hfin
  haveI := hfin
  constructor
  · rintro ⟨v, hv, huniq⟩
    let b : Fin m → eigSub (actR (x0 := t) (S := k) act) τ := fun i =>
      ⟨mkT (v i) (lieEigen_tan t act τ (hv i)), (mem_iff t act τ _).2 (hv i)⟩
    have key : ∀ (y : eigSub (actR (x0 := t) (S := k) act) τ) (e : Fin m → k),
        (y : TanM t G) = ∑ i, e i • (b i : TanM t G) →
        ∃ u : Fin m → (epsPt t ⟶ G), (∀ i, (u i).left = spMap (epsScale (e i)) ≫ (v i).left) ∧
          tv (y : TanM t G) = (List.ofFn u).prod := by
      intro y e he
      refine ⟨fun i => smT t (e i) (tv (b i : TanM t G)), fun i => (left_iff t _ _ _).2 rfl, ?_⟩
      rw [prod_eq t (fun i => (b i : TanM t G)) e, he]
    have hb : Function.Bijective (Fintype.linearCombination k b) := by
      constructor
      · intro c c' hcc
        rw [Fintype.linearCombination_apply, Fintype.linearCombination_apply] at hcc
        let y : eigSub (actR (x0 := t) (S := k) act) τ := ∑ i, c i • b i
        have hy : IsLieEigen act t τ (tv (y : TanM t G)) := (mem_iff t act τ _).1 y.2
        obtain ⟨d, _, hd⟩ := huniq _ hy
        have h1 := hd c (key y c (by simp [y, Submodule.coe_sum]))
        have h2 := hd c' (key y c' (by rw [show y = ∑ i, c' i • b i from hcc]; simp [Submodule.coe_sum]))
        exact h1.trans h2.symm
      · intro y
        have hy : IsLieEigen act t τ (tv (y : TanM t G)) := (mem_iff t act τ _).1 y.2
        obtain ⟨c, ⟨u, hu, hw⟩, _⟩ := huniq _ hy
        refine ⟨c, ?_⟩
        have hu' : u = fun i => smT t (c i) (tv (b i : TanM t G)) :=
          funext fun i => (left_iff t _ _ _).1 (hu i)
        rw [hu', prod_eq] at hw
        rw [Fintype.linearCombination_apply]
        apply Subtype.ext
        apply tanM_ext
        rw [hw]
        simp [Submodule.coe_sum]
    rw [← (LinearEquiv.ofBijective _ hb).finrank_eq, Module.finrank_fin_fun]
  · intro h
    let B := Module.finBasisOfFinrankEq k (eigSub (actR (x0 := t) (S := k) act) τ) h
    refine ⟨fun i => tv (B i : TanM t G), fun i => (mem_iff t act τ _).1 (B i).2, fun w hw => ?_⟩
    have h0 := lieEigen_tan t act τ hw
    let y : eigSub (actR (x0 := t) (S := k) act) τ := ⟨mkT w h0, (mem_iff t act τ _).2 hw⟩
    refine ⟨B.equivFun y, ⟨fun i => smT t (B.equivFun y i) (tv (B i : TanM t G)),
      fun i => (left_iff t _ _ _).2 rfl, ?_⟩, ?_⟩
    · rw [prod_eq]
      show tv (y : TanM t G) = _
      congr 1
      have hs : ((∑ i, B.repr y i • B i : eigSub (actR (x0 := t) (S := k) act) τ) : TanM t G) = y :=
        congrArg Subtype.val (B.sum_repr y)
      refine hs.symm.trans ?_
      rw [Submodule.coe_sum]
      rfl
    · rintro c ⟨u, hu, hwu⟩
      have hu' : u = fun i => smT t (c i) (tv (B i : TanM t G)) :=
        funext fun i => (left_iff t _ _ _).1 (hu i)
      rw [hu', prod_eq] at hwu
      have hy : y = ∑ i, c i • B i := by
        apply Subtype.ext
        apply tanM_ext
        show w = _
        rw [hwu]
        simp [Submodule.coe_sum]
      rw [hy, ← B.equivFun_symm_apply, LinearEquiv.apply_symm_apply]

end GlobalTheory.UPel.HT.LieLin
end
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

theorem _root_.GlobalTheory.T.exists_cusp_form_semi_local_whittaker_space : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (π : CuspSub E (m + 1)) (φ : Sm E (m + 1)), φ ∈ π.V → ∃ 𝒲 : Submodule ℂ (GA E (m + 1) → ℂ), GlobalTheory.JSW.whit φ.1 ∈ 𝒲 ∧ (∀ W ∈ 𝒲, ∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) ∧ (∀ W ∈ 𝒲, ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, (fun g => W (g * h)) ∈ 𝒲) ∧ (∀ W ∈ 𝒲, ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin (m + 1)) (Cinf E)), GlobalTheory.JSW.IsRapidInf ν k γ → GlobalTheory.JSW.kerInf ν k γ W ∈ 𝒲) ∧ (∀ W ∈ 𝒲, ∀ g, Continuous (fun y : GL (Fin (m + 1)) (Cinf E) => W (g * infGL E (m + 1) y)) ∧ ∃ (C : ℝ) (N : ℕ), ∀ y, ‖W (g * infGL E (m + 1) y)‖ ≤ C * height y ^ N) ∧ (∀ W ∈ 𝒲, ∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, W (g * finGL E (m + 1) u) = W g) ∧ ∀ W ∈ 𝒲, ∃ F ∈ GlobalTheory.JSW.MirSemi.locSpan S φ.1, ∀ g, GlobalTheory.JSW.whit F g = W g := by
  first | exact @GlobalTheory.JSW.MirSemi.whitSpace_exists | exact GlobalTheory.JSW.MirSemi.whitSpace_exists | (intros; apply GlobalTheory.JSW.MirSemi.whitSpace_exists <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

theorem _root_.GlobalTheory.T.whittaker_relation_passes_to_semi_local_span : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (π : CuspSub E a) (φ : Sm E a), φ ∈ π.V → ∀ (t : GA E a) (c : ℂ), GeneralLinearGroup.map (pInf E) t = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) → (∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := a) S, GlobalTheory.JSW.whit φ.1 (x * t) = c * GlobalTheory.JSW.whit φ.1 x) → ∀ F ∈ GlobalTheory.JSW.MirSemi.locSpan S φ.1, ∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := a) S, GlobalTheory.JSW.whit F (x * t) = c * GlobalTheory.JSW.whit F x := by
  first | exact @GlobalTheory.JSW.MirSemi.whit_rel_locSpan | exact GlobalTheory.JSW.MirSemi.whit_rel_locSpan | (intros; apply GlobalTheory.JSW.MirSemi.whit_rel_locSpan <;> assumption)
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.valuation_weierstrassP_sub_two_mul_eq_sq : ∀ (L : PeriodPair) (β u : ℂ) (V : ValuationSubring ℂ) (N : ℕ), MulStable L β → β.im ≠ 0 → V.valuation u ^ 12 = V.valuation (latticeCurve L).Δ → V.valuation (N : ℂ) = 1 → Odd N → ¬ 3 ∣ N → ∀ z, z ∉ L.lattice → (N : ℂ) * z ∈ L.lattice → 2 * z ∉ L.lattice ∧ V.valuation (L.weierstrassP z - L.weierstrassP (2 * z)) = V.valuation u ^ 2 := by
  first | exact @GlobalTheory.CMModel.weierstrassP_sub_two_mul_unit | exact GlobalTheory.CMModel.weierstrassP_sub_two_mul_unit | (intros; apply GlobalTheory.CMModel.weierstrassP_sub_two_mul_unit <;> assumption)
end

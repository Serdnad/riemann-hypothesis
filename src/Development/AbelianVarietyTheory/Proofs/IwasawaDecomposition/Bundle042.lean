module

import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle001
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Irreducible
import ReciprocityTheory.SemistableReduction.Bundle018
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm
public import ReciprocityTheory.L2DbarEstimates.Bundle001
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003
public import Mathlib.RingTheory.DedekindDomain.Different
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle033
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle021
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemBasicOpenOfMemBasicOpenNormCoeff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle035
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
public import Mathlib.RingTheory.Polynomial.GaussLemma

@[expose] public section

section

namespace GlobalTheory.SubrepTopBot

open Representation

theorem subrep_bot_toSubmodule {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) : (⊥ : Subrepresentation ρ).toSubmodule = ⊥ := rfl

theorem subrep_top_toSubmodule {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) : (⊤ : Subrepresentation ρ).toSubmodule = ⊤ := rfl

theorem main : ∀ {G : Type} [inst : Group G] {V : Type} [inst_1 : AddCommGroup V] [inst_2 : Module ℂ V] (ρ : Representation ℂ G V), Representation.IsIrreducible ρ ↔ Nontrivial V ∧ ∀ (U : Submodule ℂ V), (∀ (g : G), ∀ v ∈ U, ((ρ : G → V →ₗ[ℂ] V) g : V → V) v ∈ U) → U = ⊥ ∨ U = ⊤ := by
  apply GlobalTheory.CuspRep.isIrreducible_iff <;> assumption

end GlobalTheory.SubrepTopBot
end

section

namespace GlobalTheory.MulEqIntegerExists

open NumberField

theorem exists_mul_eq_integer {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ a b : RingOfIntegers E, b ≠ 0 ∧ (algebraMap (RingOfIntegers E) E b) * c
      = algebraMap (RingOfIntegers E) E a := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := RingOfIntegers E) c
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  refine ⟨a, b, hb0, ?_⟩
  have : algebraMap (RingOfIntegers E) E b ≠ 0 :=
    fun h => hb0 (IsFractionRing.injective (RingOfIntegers E) E (by rw [h, map_zero]))
  rw [mul_div_assoc', mul_div_cancel_left₀ _ this]

theorem exists_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (y : Fin n → E) :
    ∃ ν : RingOfIntegers E, ν ≠ 0 ∧ ν • y ∈ L := by
  apply ReciprocityTheory.MultiplicativeHeights.sc_scale <;> assumption

end GlobalTheory.MulEqIntegerExists
end

section

open Matrix
open scoped ComplexOrder Topology

namespace GlobalTheory.Proof.puncturedPolydisc_sum_negLog_eq_and_ge_logTwo

theorem tlog_sum_eq_and_log_two_le : ∀ (n a : ℕ) (ha : a ≤ n) (ρ : ℝ), ρ ≤ 1 / 2 → ∀ v : ReciprocityTheory.L2DbarEstimates.V n, v.ofLp ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.punctured ha ρ → (∑ i : Fin a, GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog (v.ofLp (Fin.castLE ha i)) = (∑ k ∈ Finset.univ.map (Fin.castLEEmb ha), |Real.log ‖v k‖|) / (2 * Real.pi)) ∧ (0 < a → Real.log 2 ≤ ∑ k ∈ Finset.univ.map (Fin.castLEEmb ha), |Real.log ‖v k‖|) := by
  intro n a ha ρ hρ v hv
  have hpos : ∀ i : Fin a, 0 < ‖v.ofLp (Fin.castLE ha i)‖ := fun i => norm_pos_iff.2 (hv.2 i)
  have hlt : ∀ i : Fin a, ‖v.ofLp (Fin.castLE ha i)‖ < 1 / 2 := fun i =>
    lt_of_lt_of_le (hv.1 (Fin.castLE ha i)) hρ
  have hneg : ∀ i : Fin a, Real.log ‖v.ofLp (Fin.castLE ha i)‖ < 0 := fun i =>
    Real.log_neg (hpos i) (by linarith [hlt i])
  refine ⟨?_, fun h0 => ?_⟩
  · rw [Finset.sum_map, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Fin.castLEEmb_apply, GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog]
    rw [abs_of_neg (hneg i)]
  · rw [Finset.sum_map]
    have hs := Finset.single_le_sum (f := fun i : Fin a => |Real.log ‖v (Fin.castLEEmb ha i)‖|)
      (fun i _ => abs_nonneg _) (Finset.mem_univ (⟨0, h0⟩ : Fin a))
    refine le_trans ?_ hs
    have e : |Real.log ‖v (Fin.castLEEmb ha ⟨0, h0⟩)‖| = -Real.log ‖v.ofLp (Fin.castLE ha ⟨0, h0⟩)‖ :=
      abs_of_neg (hneg _)
    simp only [] at e ⊢
    rw [e]
    have hl : Real.log ‖v.ofLp (Fin.castLE ha ⟨0, h0⟩)‖ ≤ Real.log (1 / 2) :=
      Real.log_le_log (hpos _) (hlt _).le
    have h2 : Real.log (1 / 2) = -Real.log 2 := by rw [one_div, Real.log_inv]
    linarith

end GlobalTheory.Proof.puncturedPolydisc_sum_negLog_eq_and_ge_logTwo
end

section

open Matrix
open scoped ComplexOrder Topology

theorem _root_.GlobalTheory.T.chernCurvature_inverse_realSymmetric_gram : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] {g : ℕ} (H : E → Matrix (Fin g) (Fin g) ℂ) (z : E), GlobalTheory.HermFrame.MContDiffAt 2 H z → IsUnit (H z).det → (∀ᶠ x in 𝓝 z, (H x).IsSymm) → (∀ᶠ x in 𝓝 z, (H x).IsHermitian) → (∀ ξ η, GlobalTheory.HermFrame.mddbar H z ξ η = 0) → ∀ ξ η, GlobalTheory.HermFrame.curv (fun x => (H x)⁻¹) z ξ η = -((GlobalTheory.HermFrame.conn H z η)ᵀᴴ * GlobalTheory.HermFrame.conn H z ξ)ᵀ := by
  first | exact @GlobalTheory.RealGram.curv_inv_of_real | exact GlobalTheory.RealGram.curv_inv_of_real | (intros; apply GlobalTheory.RealGram.curv_inv_of_real <;> assumption)
end

section

open Matrix
open scoped ComplexOrder Topology

theorem _root_.GlobalTheory.T.holomorphicDeriv_chernConnection_inverseSymmetricGram : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] {g : ℕ} (H : E → Matrix (Fin g) (Fin g) ℂ) (z : E), GlobalTheory.HermFrame.MContDiffAt 2 H z → IsUnit (H z).det → (∀ᶠ x in 𝓝 z, (H x).IsSymm) → ∀ ξ η, GlobalTheory.HermFrame.mdel (fun x => GlobalTheory.HermFrame.conn (fun y => (H y)⁻¹) x η) z ξ - GlobalTheory.HermFrame.mdel (fun x => GlobalTheory.HermFrame.conn (fun y => (H y)⁻¹) x ξ) z η = -(GlobalTheory.HermFrame.conn H z η * GlobalTheory.HermFrame.conn H z ξ - GlobalTheory.HermFrame.conn H z ξ * GlobalTheory.HermFrame.conn H z η)ᵀ := by
  first | exact @GlobalTheory.HermFrame.mdel_conn_inv_sub | exact GlobalTheory.HermFrame.mdel_conn_inv_sub | (intros; apply GlobalTheory.HermFrame.mdel_conn_inv_sub <;> assumption)
end

section

open scoped Matrix

theorem _root_.GlobalTheory.T.chernCurvature_inv_one_sub_conj_mul_transpose_at_zero : ∀ {n r s : ℕ} (f g : Fin r → Fin s → Fin n) (ξ η : ReciprocityTheory.L2DbarEstimates.V n), GlobalTheory.HermFrame.curv (fun u : ReciprocityTheory.L2DbarEstimates.V n => (1 - (Matrix.of fun i j => u (f i j)).map (starRingEnd ℂ) * (Matrix.of fun i j => u (g i j))ᵀ)⁻¹) 0 ξ η = -((Matrix.of fun i j => ξ (g i j)) * (Matrix.of fun i j => η (f i j))ᴴ) := by
  first | exact @GlobalTheory.HermFrame.curv_inv_one_sub_conj_mul_transpose_zero | exact GlobalTheory.HermFrame.curv_inv_one_sub_conj_mul_transpose_zero | (intros; apply GlobalTheory.HermFrame.curv_inv_one_sub_conj_mul_transpose_zero <;> assumption)
end

section

set_option autoImplicit false

open NumberField IsDedekindDomain GlobalTheory.NT

namespace GlobalTheory.UnramDiscr

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

theorem not_dvd_iff_inertia (P : Ideal (𝓞 L)) [P.IsPrime] (hP : P ≠ ⊥) :
    ¬ P ∣ differentIdeal (𝓞 K) (𝓞 L) ↔ P.inertia (L ≃ₐ[K] L) = ⊥ := by
  let _ : Algebra (FractionRing (𝓞 K)) (FractionRing (𝓞 L)) := FractionRing.liftAlgebra _ _
  haveI : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP
  rw [not_dvd_differentIdeal_iff, ← Ideal.ramificationIdx_eq_one_iff,
    ← Ideal.ramificationIdxIn_eq_ramificationIdx (P.under (𝓞 K)) P (L ≃ₐ[K] L),
    ← Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) (P.under (𝓞 K)) P,
    Subgroup.card_eq_one]

theorem unramIn_iff_differentIdeal_eq_top :
    (∀ 𝔭 : HeightOneSpectrum (𝓞 K), UnramIn L 𝔭) ↔ differentIdeal (𝓞 K) (𝓞 L) = ⊤ := by
  let _ : Algebra (FractionRing (𝓞 K)) (FractionRing (𝓞 L)) := FractionRing.liftAlgebra _ _
  have hD0 : differentIdeal (𝓞 K) (𝓞 L) ≠ ⊥ := differentIdeal_ne_bot
  unfold UnramIn InInertia
  constructor
  · intro h
    by_contra hD
    obtain ⟨M, hM, hDM⟩ := Ideal.exists_le_maximal _ hD
    haveI := hM
    have hMb : M ≠ ⊥ := by
      rintro rfl
      exact hD0 (le_bot_iff.mp hDM)
    have hMu : M.under (𝓞 K) ≠ ⊥ := mt Ideal.eq_bot_of_comap_eq_bot hMb
    have hb : M.inertia (L ≃ₐ[K] L) = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro σ hσ
      exact h ⟨M.under (𝓞 K), inferInstance, hMu⟩ σ ⟨M, inferInstance, ⟨rfl⟩, fun x => hσ x⟩
    exact (not_dvd_iff_inertia K L M hMb).mpr hb (Ideal.dvd_iff_le.mpr hDM)
  · rintro hD 𝔭 σ ⟨P, hP, hPo, hσ⟩
    haveI := hP
    haveI := hPo
    have hPb : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P
    have hnd : ¬ P ∣ differentIdeal (𝓞 K) (𝓞 L) := by
      rw [hD]
      exact fun hd => hP.ne_top (top_le_iff.mp (Ideal.dvd_iff_le.mp hd))
    have hb := (not_dvd_iff_inertia K L P hPb).mp hnd
    have hmem : σ ∈ P.inertia (L ≃ₐ[K] L) := fun x => hσ x
    rw [hb] at hmem
    exact Subgroup.mem_bot.mp hmem


omit K L in
theorem unramIn_iff_natAbs_discr :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L],
      (∀ 𝔭 : HeightOneSpectrum (𝓞 K), UnramIn L 𝔭) ↔
        (discr L).natAbs = (discr K).natAbs ^ Module.finrank K L := by
  intro K L _ _ _ _ _ _
  rw [unramIn_iff_differentIdeal_eq_top K L,
    natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) L (𝓞 L)]
  have h0 : 0 < (discr K).natAbs ^ Module.finrank K L :=
    pow_pos (Int.natAbs_pos.mpr (discr_ne_zero K)) _
  constructor
  · intro h
    rw [h, Ideal.absNorm_top, one_mul]
  · intro h
    apply Ideal.absNorm_eq_one_iff.mp
    apply Nat.eq_of_mul_eq_mul_right h0
    rw [h, one_mul]

end GlobalTheory.UnramDiscr
end

section

open AlgebraicGeometry CategoryTheory TopologicalSpace

theorem _root_.GlobalTheory.T.exists_local_section_of_isIntegralElem_normal_scheme : ∀ {T Z : Scheme.{0}} [GlobalTheory.IsNormalScheme Z] [IsLocallyNoetherian Z] (j : T ⟶ Z) [IsOpenImmersion j],
    Dense (Set.range j) → ∀ (U : Z.Opens) (s : Γ(T, j ⁻¹ᵁ U)), (j.app U).hom.IsIntegralElem s →
    ∀ u ∈ U, ∃ (W : Z.Opens) (hWU : W ≤ U), u ∈ W ∧
      ∃ h : Γ(Z, W), j.app W h = T.presheaf.map (homOfLE (j.preimage_mono hWU)).op s := by
  first | exact @GlobalTheory.exists_section_of_isIntegralElem_of_isOpenImmersion | exact GlobalTheory.exists_section_of_isIntegralElem_of_isOpenImmersion | (intros; apply GlobalTheory.exists_section_of_isIntegralElem_of_isOpenImmersion <;> assumption)
end

section

noncomputable section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.IwaCell

variable {k : Type} [Field k] {m : ℕ}

def tD (ϖ : kˣ) (a : Fin m → ℤ) : GL (Fin m) k := diagT k (Fin m) fun i => ϖ ^ a i

variable [ValuativeRel k]

def cell (ϖ : kˣ) (a : Fin m → ℤ) : Set (GL (Fin m) k) :=
  {g | ∃ u ∈ unipB k (Fin m), ∃ κ ∈ KO k (Fin m), g = u * tD ϖ a * κ}


theorem val_tD (ϖ : kˣ) (a : Fin m → ℤ) : (tD ϖ a).val = Matrix.diagonal fun i => ((ϖ ^ a i : kˣ) : k) :=
  val_diagT k _

theorem tD_add (ϖ : kˣ) (a b : Fin m → ℤ) : tD ϖ (a + b) = tD ϖ a * tD ϖ b := by
  rw [tD, tD, tD, ← map_mul]
  congr 1
  funext i
  simp [_root_.zpow_add]

variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem tD_zero (ϖ : kˣ) : tD ϖ (0 : Fin m → ℤ) = 1 := by
  rw [tD, ← map_one (diagT k (Fin m))]
  congr 1
  funext i
  simp

theorem tD_neg (ϖ : kˣ) (a : Fin m → ℤ) : tD ϖ (-a) = (tD ϖ a)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← tD_add, neg_add_cancel, tD_zero])

theorem diag_entry (ϖ : kˣ) (s t : Fin m → ℤ) {w : GL (Fin m) k} (hw : w ∈ unipB k (Fin m)) (i : Fin m) :
    (tD ϖ s * w * tD ϖ t).val i i = ((ϖ ^ (s i + t i) : kˣ) : k) := by
  rw [Units.val_mul, Units.val_mul, val_tD, val_tD, Matrix.mul_diagonal, Matrix.diagonal_mul, ((mem_unipB k).1 hw).2 i,
    mul_one, _root_.zpow_add, Units.val_mul]

theorem ord_zpow (x : kˣ) (n : ℤ) : ord k (x ^ n) = n * ord k x := by
  let o : kˣ →* Multiplicative ℤ := MonoidHom.mk' (fun x => .ofAdd (ord k x)) fun x y => by
    rw [ord_mul, ofAdd_add]
  have h := map_zpow o x n
  have h2 : Multiplicative.toAdd (o (x ^ n)) = Multiplicative.toAdd (o x ^ n) := congrArg _ h
  simpa [o, mul_comm] using h2

theorem eq_of_mem_cell {ϖ : kˣ} (hϖ : ord k ϖ = 1) {a b : Fin m → ℤ} {g : GL (Fin m) k} (ha : g ∈ cell ϖ a)
    (hb : g ∈ cell ϖ b) : a = b := by
  obtain ⟨u, hu, κ, hκ, rfl⟩ := ha
  obtain ⟨u', hu', κ', hκ', e⟩ := hb
  have hw : u'⁻¹ * u ∈ unipB k (Fin m) := mul_mem (inv_mem hu') hu
  have hx : tD ϖ (-b) * (u'⁻¹ * u) * tD ϖ a = κ' * κ⁻¹ := by
    rw [tD_neg]
    calc (tD ϖ b)⁻¹ * (u'⁻¹ * u) * tD ϖ a = (u' * tD ϖ b)⁻¹ * (u * tD ϖ a * κ) * κ⁻¹ := by group
      _ = (u' * tD ϖ b)⁻¹ * (u' * tD ϖ b * κ') * κ⁻¹ := by rw [e]
      _ = κ' * κ⁻¹ := by group
  have hxi : (tD ϖ (-b) * (u'⁻¹ * u) * tD ϖ a)⁻¹ = tD ϖ (-a) * (u'⁻¹ * u)⁻¹ * tD ϖ b := by
    simp only [tD_neg, _root_.mul_inv_rev, inv_inv]; group
  have hK := (GlobalTheory.SplitFlip.mem_KO_iff _).1 (hx ▸ mul_mem hκ' (inv_mem hκ))
  funext i
  have h1 := hK.1 i i
  have h2 := hK.2 i i
  rw [diag_entry ϖ _ _ hw] at h1
  rw [hxi, diag_entry ϖ _ _ (inv_mem hw)] at h2
  simp only [Pi.neg_apply] at h1 h2
  set y : kˣ := ϖ ^ (-b i + a i)
  have h2' : ((y⁻¹ : kˣ) : k) ∈ 𝒪[k] := by
    have : (ϖ ^ (-a i + b i) : kˣ) = y⁻¹ := by rw [← _root_.zpow_neg]; congr 1; ring
    rwa [this] at h2
  have v1 : valuation k (y : k) ≤ 1 := h1
  have v2 : valuation k ((y⁻¹ : kˣ) : k) ≤ 1 := h2'
  have hv : valuation k (y : k) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀] at v2
    have hpos : 0 < valuation k (y : k) := zero_lt_iff.2 (by simp)
    exact le_antisymm v1 ((inv_le_one₀ hpos).1 v2)
  have h3 : ord k y = 0 := by simp [ord, hv]
  rw [ord_zpow, hϖ, mul_one] at h3
  omega

end GlobalTheory.IwaCell
end
end

section

open AlgebraicGeometry CategoryTheory Polynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.NormalDescent

theorem _root_.GlobalTheory.T.exists_mem_basicOpen_of_mem_basicOpen_normCoeff' : ∀ {X Y : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] {V : X.Opens} (hV : IsAffineOpen V)
    [IsDomain Γ(X, V)] [IsIntegrallyClosed Γ(X, V)] (τ : Γ(Y, f ⁻¹ᵁ V)) (x : X) (k : ℕ), x ∈ V → 1 ≤ k →
    x ∈ X.basicOpen (normCoeff (f.app V).hom (f.finite_app V hV) τ k) → ∃ y ∈ Y.basicOpen τ, f y = x := by
  first | exact @GlobalTheory.NormalDescent.exists_mem_basicOpen_of_mem_basicOpen_normCoeff | exact GlobalTheory.NormalDescent.exists_mem_basicOpen_of_mem_basicOpen_normCoeff | (intros; apply GlobalTheory.NormalDescent.exists_mem_basicOpen_of_mem_basicOpen_normCoeff <;> assumption)
end

section

open CategoryTheory Polynomial GlobalTheory.NormalDescent TensorProduct

namespace GlobalTheory.NormalDescent

theorem exists_map_eq_charK : ∀ {A B K : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [Field K]
    [Algebra A K] [IsFractionRing A K] (φ : A →+* B) (hφ : φ.Finite) (b : B),
    ∃ P : A[X], P.map (algebraMap A K) = charK φ hφ K b := by
  intro A B K _ _ _ _ _ _ _ φ hφ b
  letI := φ.toAlgebra
  haveI : Module.Finite A B := hφ
  obtain ⟨g, hgm, hg⟩ := (Algebra.IsIntegral.isIntegral (R := A) b)
  have hT : aeval (Algebra.lmul K (K ⊗[A] B) (1 ⊗ₜ b)) (g.map (algebraMap A K)) = 0 := by
    rw [Polynomial.aeval_algHom_apply, Polynomial.aeval_map_algebraMap]
    have : (1 : K) ⊗ₜ[A] b = Algebra.TensorProduct.includeRight b := rfl
    rw [this, Polynomial.aeval_algHom_apply, show aeval b g = 0 from hg, map_zero, map_zero]
  have hd := GlobalTheory.T.charpoly_dvd_pow_finrank_of_aeval_eq_zero _ _ hT
  rw [← Polynomial.map_pow] at hd
  obtain ⟨P, hP⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K (hgm.pow _) hd
  refine ⟨P, ?_⟩
  have hm : (charK φ hφ K b).Monic := charK_monic φ hφ K b
  have : (Algebra.lmul K (K ⊗[A] B) (1 ⊗ₜ b)).charpoly = charK φ hφ K b := rfl
  rw [this, hm.leadingCoeff, C_1, mul_one] at hP
  exact hP

end GlobalTheory.NormalDescent
end

section

noncomputable section

open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology

namespace GlobalTheory.Mem.Lift

theorem IsQuadOf.apply_vec {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B]
    [NormedSpace ℂ B] {om : V → V → ℝ} {X : V → V} {κ : Type} [Fintype κ] {c : κ → ℂ} {p q : κ → V}
    (h : IsQuadOf om X c p q) (L : V →ₗ[ℝ] B) (v : V) :
    (2 * π * I : ℂ) • ∑ i, c i • ((om (q i) v : ℂ) • L (p i) + (om (p i) v : ℂ) • L (q i)) = L (X v) := by
  rw [SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)]
  intro φ
  have := h ((φ.restrictScalars ℝ).toLinearMap ∘ₗ L) v

  simpa [map_sum, ← mul_add] using this

theorem fderiv_eq_quad_comm : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] (om : V →L[ℝ] V →L[ℝ] ℝ) (ρ : V → B →L[ℂ] B), (∀ x, om x x = 0) → IsHeis (fun x y => om x y) ρ → ∀ (X : V → V) (κ : Type) [Fintype κ] (c : κ → ℂ) (p q : κ → V), IsQuadOf (fun x y => om x y) X c p q → ∀ f, Sm ρ f → ∀ w, fderiv ℝ (fun u => ρ u f) w (X w) = quad ρ c p q (ρ w f) - ρ w (quad ρ c p q f) := by
  intro V _ _ B _ _ om ρ h0 hH X κ _ c p q hQ f hf w
  have C := GlobalTheory.Mem.Lift.DCalc.dH_calculus V B om ρ h0 hH
  obtain ⟨h1, h2, h3, h4, -⟩ := C f hf
  have skew : om w (X w) = - om (X w) w := by
    have := h0 (w + X w)
    simp only [map_add (f := _), _root_.add_apply, h0] at this
    linarith
  have key : ∀ u v, dH ρ u (dH ρ v (ρ w f)) = ρ w (dH ρ u (dH ρ v f))
      + (2 * π * I : ℂ) • ρ w ((om v w : ℂ) • dH ρ u f + (om u w : ℂ) • dH ρ v f)
      + ((2 * π * I : ℂ) * ((2 * π * I : ℂ) * ((om v w : ℂ) * (om u w : ℂ)))) • ρ w f := by
    intro u v
    obtain ⟨-, g2, -, g4, -⟩ := C _ (h1 v)
    have hs : Sm ρ ((2 * π * I * (om v w : ℂ)) • ρ w f) := (smS ρ).smul_mem _ (h2 w)
    rw [h4 v w, dH_add u (g2 w) hs, dH_smul u _ (h2 w), g4 u w, h4 u w]
    simp only [map_add (f := _), map_smul]
    module
  have e1 := hQ.apply_vec (fderiv ℝ (fun u => ρ u f) 0).toLinearMap w
  have e1' : (2 * π * I : ℂ) • ∑ i, c i • ((om (q i) w : ℂ) • dH ρ (p i) f + (om (p i) w : ℂ) • dH ρ (q i) f)
      = dH ρ (X w) f := e1
  have e2 := hQ (Complex.ofRealCLM.toLinearMap ∘ₗ (om.flip w).toLinearMap) w
  have e2' : 2 * π * I * ∑ i, c i * ((om (q i) w : ℂ) * (om (p i) w : ℂ) + (om (p i) w : ℂ) * (om (q i) w : ℂ))
      = (om (X w) w : ℂ) := e2
  have e3 : ∑ i, c i * ((2 * π * I : ℂ) * ((2 * π * I : ℂ) * ((om (q i) w : ℂ) * (om (p i) w : ℂ))))
      = π * I * (om (X w) w : ℂ) := by
    rw [← e2', Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e4 : ∑ i, c i • (2 * π * I : ℂ) • ρ w ((om (q i) w : ℂ) • dH ρ (p i) f + (om (p i) w : ℂ) • dH ρ (q i) f)
      = ρ w (dH ρ (X w) f) := by

    rw [← e1', map_smul, map_sum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_comm]
  have e5 : quad ρ c p q (ρ w f) = ρ w (quad ρ c p q f) + ρ w (dH ρ (X w) f)
      + (π * I * (om (X w) w : ℂ)) • ρ w f := by
    rw [← e3, ← e4, Finset.sum_smul]
    unfold quad

    rw [map_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [key, smul_add, smul_add, map_smul, smul_smul (c i) _ (ρ w f)]
  rw [h3, e5, skew]
  push_cast
  module

end GlobalTheory.Mem.Lift

end
end

module

import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle033
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RingTheory.Ideal.Prime
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DoublingNormDetSplitPlaceLatticeIntersection
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.NumberTheory.Padics.Complex
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHeckeEigenfunctionalDepletedEisensteinNeZe
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle311
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle312
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle313
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle015
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Dynamics.Ergodic.Action.Regular
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003

@[expose] public section

section

namespace GlobalTheory.PrimeNatCastMembership

theorem exists_prime_natCast_mem {A : Type} [inst : CommRing A] (P : Ideal A) (hP : Ideal.IsPrime P)
    (n : ℕ) (hn : n ≠ (0 : ℕ)) (hmem : (↑n : A) ∈ P) :
    ∃ (q : ℕ), Nat.Prime q ∧ (↑q : A) ∈ P := by
  apply GlobalTheory.PlaceInt.LocBasis.exists_prime_mem <;> assumption

end GlobalTheory.PrimeNatCastMembership
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.IndefiniteRowSideFullHecke.GraphHeightLattice
open Formalism.UG (GLint)

theorem _root_.GlobalTheory.T.doublingNorm_det_splitPlace_lattice_intersection : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L] (v : HeightOneSpectrum (𝓞 F)), IsSelfDualAt σ J L v → ∀ (τ : E →ₐ[F] Fv F v) (β : GL (Fin n) (Fv F v)), IsSplitBasis τ L β → ∀ (g : GLoc σ J v) (α : GL (Fin n) (Fv F v ⊗[F] E)), (∀ y : Fin n → Fv F v ⊗[F] E, (y ∈ latLoc F L v ∧ y ∈ latMoved σ J L v g) ↔ ∃ x ∈ latLoc F L v, y = α.1 *ᵥ x) → ∀ d : Fin n → (Fv F v)ˣ, IsElemDiv (splitEquivIn h hJ τ β g) d → absEv F E v (Matrix.GeneralLinearGroup.det α) = ∏ i, min ‖(d i : Fv F v)‖₊ ‖(d i : Fv F v)‖₊⁻¹ := by
  first | exact @GlobalTheory.SplitInterDet.absEv_det_split | exact GlobalTheory.SplitInterDet.absEv_det_split | (intros; apply GlobalTheory.SplitInterDet.absEv_det_split <;> assumption)
end

section

open MeasureTheory GlobalTheory.AutomorphicL2Unitary
open scoped Pointwise Topology

namespace GlobalTheory.AutomorphicL2Local

theorem continuous_integral_inv_mul_of_locallyIntegrable {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G]
    [BorelSpace G] {μ : Measure G} {f φ : G → ℂ} (hf : Continuous f) (hc : HasCompactSupport f)
    (hφ : LocallyIntegrable φ μ) :
    (∀ x, Integrable (fun y => f (x⁻¹ * y) * φ y) μ) ∧ Continuous fun x => ∫ y, f (x⁻¹ * y) * φ y ∂μ := by
  have hi : ∀ x, Integrable (fun y => f (x⁻¹ * y) * φ y) μ := fun x =>
    hφ.integrable_smul_left_of_hasCompactSupport (g := fun y => f (x⁻¹ * y)) (by fun_prop)
      (hc.comp_homeomorph (Homeomorph.mulLeft x⁻¹))
  refine ⟨hi, continuous_iff_continuousAt.2 fun x₀ => ?_⟩
  obtain ⟨U, hU, hx⟩ := exists_compact_mem_nhds x₀
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hc
  have hK : IsCompact (U * tsupport f) := hU.mul hc.isCompact
  refine continuousAt_of_dominated (bound := (U * tsupport f).indicator fun y => M * ‖φ y‖)
    (.of_forall fun x => (hi x).1) ?_ ?_ (.of_forall fun y => ?_)
  · filter_upwards [hx] with x hxU
    refine .of_forall fun y => ?_
    by_cases hy : y ∈ U * tsupport f
    · rw [Set.indicator_of_mem hy, norm_mul]
      exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
    · rw [Set.indicator_of_notMem hy,
        image_eq_zero_of_notMem_tsupport (f := f) fun h => hy ⟨x, hxU, _, h, by simp⟩]
      simp
  · exact (integrable_indicator_iff hK.measurableSet).2 ((hφ.integrableOn_isCompact hK).norm.const_mul M)
  · exact Continuous.continuousAt (by fun_prop)

theorem continuous_convR_lift : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], ∀ f : G → ℂ, Continuous f → HasCompactSupport f → ∀ F : L2 Γ μ, (∀ x, Integrable (fun y => f y * lift Γ F (x * y)) μ) ∧ Continuous (convR μ f (lift Γ F)) := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ f hf hc F
  have hφ : LocallyIntegrable (lift Γ F) μ :=
    locallyIntegrable_iff.2 fun C hC => (memLp_restrict_compact G Γ μ F C hC).2
  obtain ⟨h1, h2⟩ := continuous_integral_inv_mul_of_locallyIntegrable hf hc hφ
  refine ⟨fun x => ?_, h2.congr fun x => (convR_eq f _ x).symm⟩
  simpa using (h1 x).comp_mul_left x

end GlobalTheory.AutomorphicL2Local
end

section

open MeasureTheory GlobalTheory.AutomorphicL2Unitary

theorem _root_.GlobalTheory.T.memLp_lift_L2DiscreteQuotient_on_compact : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], ∀ (F : L2 Γ μ) (C : Set G), IsCompact C → MemLp (lift Γ F) 2 (μ.restrict C) ∧ IntegrableOn (lift Γ F) C μ := by
  first | exact @GlobalTheory.AutomorphicL2Local.memLp_restrict_compact | exact GlobalTheory.AutomorphicL2Local.memLp_restrict_compact | (intros; apply GlobalTheory.AutomorphicL2Local.memLp_restrict_compact <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.exists_heckeEigenfunctional_depletedEisenstein_ne_zero : ∀ (l : ℕ) [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (e N : ℕ) (χ θ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ l) (g : ℕ → ℂ) (α β : ℂ), 1 ≤ e → 0 < N → ¬ l ∣ N → Prim (2 * e + 1) N χ g → α + β = χ⁻¹ l * g l → α * β = χ⁻¹ l * (l : ℂ) ^ (2 * e) → ‖ι.symm α‖ = 1 → θ (-1) = (-1) ^ e * ψ (-1) → θ * χ ≠ 1 → ∃ (B : ℕ) (c : ℕ → ℂ), EigF (2 * e + 1) N l χ⁻¹ (fun q => χ⁻¹ q * g q) α B c ∧ val B c l α 1 (Zs (2 * e + 1) l (ch θ) (hat ⇑(θ * χ)) (fun x y => ψ x * ψ⁻¹ y * ((y : ℂ) / x) ^ e)) ≠ 0 := by
  first | exact @GlobalTheory.EisM.eigF_value_ne_zero | exact GlobalTheory.EisM.eigF_value_ne_zero | (intros; apply GlobalTheory.EisM.eigF_value_ne_zero <;> assumption)
end

section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

theorem _root_.GlobalTheory.T.cgA_coeff_of_isThB_succ : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime], l ≠ 2 → ¬ l ∣ N → 1 ≤ N → ((l : Ω) ∈ A.nonunits) → ∀ (n : ℕ) (b : X.Fn l) (φ φ' : HahnSeries ℚ Ω),
  IsThB X A N l (n + 1) b φ → IsThB X A N l n b φ' → ∀ r, CgA A l n (φ.coeff r) (φ'.coeff r) := by
  first | (exact @GlobalTheory.ThBCompat.isThB_succ_coeff_cong) | (exact GlobalTheory.ThBCompat.isThB_succ_coeff_cong) | (intros; apply GlobalTheory.ThBCompat.isThB_succ_coeff_cong  <;> assumption)
end

section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

theorem _root_.GlobalTheory.T.cuspFunctionalValueModPrimePow_unique_oddWeight : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime], (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → l ≠ 2 → ¬ l ∣ N → 5 ≤ N → ((l : Ω) ∈ A.nonunits) → ∀ (n w : ℕ), Odd w → ∀ b : X.Fn l, b ∈ X.B N l w → ∀ φ φ' : HahnSeries ℚ Ω,
  IsThB X A N l n b φ → IsThB X A N l n b φ' → ∀ r, CgA A l n (φ.coeff r) (φ'.coeff r) := by
  intro Ω _ _ _ ε X A N l _ hj hl2 hlN hN
  exact GlobalTheory.isThB_coeff_cong Ω ε X A N l hj hl2 hlN (by omega)
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.kummerPotentialSpan_hecke_letter_stable : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] {E : Type} [Field E] [Algebra ℤ_[l] E] (T : Letter) (p : (E ⊗[ℤ_[l]] X.Fn l) × (ℂ → MvPolynomial (Fin 2) E)), p ∈ H3.abelian₂ X l E → (X.opV N l E T p.1, opL E N l T p.2) ∈ H3.abelian₂ X l E := by
  first | exact @GlobalTheory.KZ.H3.lam_stable | exact GlobalTheory.KZ.H3.lam_stable | (intros; apply GlobalTheory.KZ.H3.lam_stable <;> assumption)
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

theorem _root_.GlobalTheory.T.trivial_eigenvalue_congruence_vanishes : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], ∀ (E : Type) [Field E] [Algebra ℤ_[l] E], Function.Injective (algebraMap ℤ_[l] E) → ∀ (w : ℕ) (Γ : Subgroup SL(2, ℤ)) (M₀ : ℕ), 0 < M₀ → CongruenceSubgroup.Gamma M₀ ≤ Γ → ∀ p ∈ abelian₂ X l E, p.2 ∈ Triv E w Γ → p.1 = 0 := by
  first | exact @GlobalTheory.KZ.H3.lam_fst_eq_zero_of_triv | exact GlobalTheory.KZ.H3.lam_fst_eq_zero_of_triv | (intros; apply GlobalTheory.KZ.H3.lam_fst_eq_zero_of_triv <;> assumption)
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

theorem _root_.GlobalTheory.T.exists_kummerPotentialRelation_padic : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], [IsAlgClosed Ω] → JHol X → ∀ (N w : ℕ), 4 ≤ N → l ≠ 2 → ¬ l ∣ N → Odd w → ∀ b ∈ X.B N l w, ∃ F ∈ Pot ℤ_[l] w (Gam N l), Rel X l b F := by
  first | exact @GlobalTheory.KZ.H3.exists_pot_rel | exact GlobalTheory.KZ.H3.exists_pot_rel | (intros; apply GlobalTheory.KZ.H3.exists_pot_rel <;> assumption)
end

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

theorem _root_.GlobalTheory.T.exists_logDerivQExpansion_modPrimePow_of_translationInvariant : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (n L : ℕ) (f : X.K), 0 < L → f ≠ 0 → f ∈ KT X L → ∃ φ : HahnSeries ℚ Ω, IsDl X A l n L f φ ∧ ∀ r : ℚ, φ.coeff r ≠ 0 → (r * L).den = 1 := by
  first | exact @GlobalTheory.dl_exists | exact GlobalTheory.dl_exists | (intros; apply GlobalTheory.dl_exists <;> assumption)
end

section

open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal Pointwise

noncomputable section

namespace GlobalTheory.Cusp.Stages

section Alg

variable {G : Type} [Group G] (Γ : Subgroup G) {N N' : Subgroup G}

def pairs (hn : ∀ p ∈ N, ∀ n ∈ N', p * n * p⁻¹ ∈ N') : Subgroup (N × N) where
  carrier := {p | (p.1 : G) ∈ Γ ∧ (p.2 : G) ∈ Γ ∧ (p.1 : G) * (p.2 : G)⁻¹ ∈ N'}
  one_mem' := ⟨one_mem _, one_mem _, by simp⟩
  mul_mem' := fun {p q} hp hq => ⟨mul_mem hp.1 hq.1, mul_mem hp.2.1 hq.2.1, by
    simpa [mul_assoc] using mul_mem (hn _ p.1.2 _ hq.2.2) hp.2.2⟩
  inv_mem' := fun {p} hp => ⟨inv_mem hp.1, inv_mem hp.2.1, by
    simpa [mul_assoc] using hn _ (inv_mem p.1.2) _ (inv_mem hp.2.2)⟩

variable {Γ} {hn : ∀ p ∈ N, ∀ n ∈ N', p * n * p⁻¹ ∈ N'}

instance : MulAction (pairs Γ hn) (N' × N) where
  smul p z := (⟨p.1.1 * z.1 * (p.1.2 : G)⁻¹, by
    simpa [mul_assoc] using mul_mem p.2.2.2 (hn _ p.1.2.2 _ z.1.2)⟩, p.1.2 * z.2)
  one_smul z := Prod.ext (Subtype.ext (by
    change ((1 : N) : G) * _ * ((1 : N) : G)⁻¹ = _; simp)) (one_mul _)
  mul_smul p q z := Prod.ext (Subtype.ext (by
    change ((p.1.1 * q.1.1 : N) : G) * _ * ((p.1.2 * q.1.2 : N) : G)⁻¹ =
      p.1.1 * (q.1.1 * z.1 * (q.1.2 : G)⁻¹) * (p.1.2 : G)⁻¹
    simp [mul_assoc])) (mul_assoc _ _ _)

theorem smul_fst (p : pairs Γ hn) (z : N' × N) : ((p • z).1 : G) = p.1.1 * z.1 * (p.1.2 : G)⁻¹ := rfl

theorem smul_snd (p : pairs Γ hn) (z : N' × N) : (p • z).2 = p.1.2 * z.2 := rfl

theorem existsUnique_prod (hle : N' ≤ N) {A : Set N'} {B : Set N}
    (hA : ∀ m : N', ∃! δ : Γ.subgroupOf N', (δ : N') * m ∈ A)
    (hB : ∀ n : N, ∃! γ : Γ.subgroupOf N, (γ : N) * n ∈ B) (z : N' × N) :
    ∃! p : pairs Γ hn, p • z ∈ A ×ˢ B := by
  obtain ⟨b, hb, hb'⟩ := hB z.2
  obtain ⟨d, hd, hd'⟩ := hA ⟨(b.1 : G) * z.1 * (b.1 : G)⁻¹, hn _ b.1.2 _ z.1.2⟩
  refine ⟨⟨(⟨d.1.1, hle d.1.2⟩ * b.1, b.1), Γ.mul_mem (show d.1.1 ∈ Γ from d.2) (show b.1.1 ∈ Γ from b.2), b.2, by simp⟩, ⟨?_, hb⟩, fun q hq => ?_⟩
  · convert hd using 1
    exact Subtype.ext (by simp [smul_fst, mul_assoc])
  · have e : q.1.2 = b.1 := congrArg Subtype.val (hb' ⟨q.1.2, q.2.2.1⟩ hq.2)
    have e' := hd' ⟨⟨_, q.2.2.2⟩, mul_mem q.2.1 (inv_mem q.2.2.1)⟩ (by
      convert hq.1 using 1
      exact Subtype.ext (by simp [smul_fst, mul_assoc, e]))
    refine Subtype.ext (Prod.ext (Subtype.ext ?_) e)
    simp [← e', e]

theorem existsUnique_shear (hle : N' ≤ N) {A : Set N'} {B : Set N}
    (hA : ∀ m : N', ∃! δ : Γ.subgroupOf N', (δ : N') * m ∈ A)
    (hB : ∀ n : N, ∃! γ : Γ.subgroupOf N, (γ : N) * n ∈ B) (z : N' × N) :
    ∃! p : pairs Γ hn, p • z ∈ (fun z : N' × N => (z.1, Subgroup.inclusion hle z.1 * z.2)) ⁻¹' (A⁻¹ ×ˢ B) := by
  let s : pairs Γ hn → pairs Γ hn := fun p => ⟨p.1.swap, p.2.2.1, p.2.1, by simpa using inv_mem p.2.2.2⟩
  have hs : ∀ p : pairs Γ hn, p • z ∈ (fun z : N' × N => (z.1, Subgroup.inclusion hle z.1 * z.2)) ⁻¹' (A⁻¹ ×ˢ B) ↔
      s p • (z.1⁻¹, Subgroup.inclusion hle z.1 * z.2) ∈ A ×ˢ B := fun p => by
    refine and_congr (Iff.of_eq (congrArg (· ∈ A) (Subtype.ext ?_))) (Iff.of_eq (congrArg (· ∈ B) (Subtype.ext ?_)))
    · simp [smul_fst, s, mul_assoc]
    · simp [smul_fst, smul_snd, s, mul_assoc]
  obtain ⟨p, hp, hp'⟩ := existsUnique_prod (hn := hn) hle hA hB (z.1⁻¹, Subgroup.inclusion hle z.1 * z.2)
  exact ⟨s p, (hs _).2 hp, fun q hq => congrArg s (hp' _ ((hs q).1 hq))⟩

end Alg

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {Γ N N' : Subgroup G} [DiscreteTopology Γ] [LocallyCompactSpace N]
  [LocallyCompactSpace N']

theorem constTermOn_eq' {μ : Measure N} [μ.IsHaarMeasure] {𝓕 : Set N} (h : IsFundamentalDomain (Γ.subgroupOf N) 𝓕 μ)
    {φ : G → ℂ} {x : G} (hφ : LeftInv (Γ.subgroupOf N) fun n : N => φ (n * x)) :
    constTermOn Γ N φ x = (μ.real 𝓕)⁻¹ • ∫ n in 𝓕, φ (n * x) ∂μ := by
  rw [constTermOn, probMeasure_eq μ, integral_smul_measure, quotMeasure_univ h, integral_quotMeasure h,
    ENNReal.toReal_inv, measureReal_def]
  exact congrArg _ (integral_congr_ae (.of_forall hφ.descend_mk))

theorem measurePreserving_conj (hc : Cocompact Γ N) (μ : Measure N) [μ.IsHaarMeasure] {γ : G} (hγ : γ ∈ Γ)
    (h1 : ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) (h2 : ∀ n ∈ N, γ⁻¹ * n * γ⁻¹⁻¹ ∈ N) :
    MeasurePreserving (fun n : N => (⟨γ * n * γ⁻¹, h1 _ n.2⟩ : N)) μ μ := by
  let e : N ≃ₜ* N :=
    { toFun := fun n => ⟨γ * n * γ⁻¹, h1 _ n.2⟩
      invFun := fun n => ⟨γ⁻¹ * n * γ, by simpa using h2 _ n.2⟩
      left_inv := fun n => by simp [mul_assoc]
      right_inv := fun n => by simp [mul_assoc]
      map_mul' := fun a b => by simp [mul_assoc]
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hm : Measurable e := e.continuous.measurable
  have h := isFundamentalDomain_stdDom (Γ.subgroupOf N) μ
  have he := Measure.isMulLeftInvariant_eq_smul (μ.map e) μ
  have h' : IsFundamentalDomain (Γ.subgroupOf N) (e ⁻¹' stdDom (Γ.subgroupOf N)) μ :=
    h.preimage_of_equiv ⟨hm.aemeasurable, he ▸ Measure.smul_absolutelyContinuous⟩
      (e := fun δ => ⟨e.symm δ, mul_mem (mul_mem (inv_mem hγ) δ.2) hγ⟩)
      ⟨fun a b hab => Subtype.ext (e.symm.injective (congrArg Subtype.val hab)),
        fun δ => ⟨⟨e δ, mul_mem (mul_mem hγ δ.2) (inv_mem hγ)⟩, Subtype.ext (e.symm_apply_apply _)⟩⟩
      fun δ n => (map_mul e _ _).trans (congrArg (· * e n) (e.apply_symm_apply _))
  have h1 := h'.measure_eq h
  rw [← Measure.map_apply hm (measurableSet_stdDom _), he, Measure.smul_apply, ENNReal.smul_def,
    smul_eq_mul, ENNReal.mul_eq_right (h.measure_ne_zero (NeZero.ne μ)) (hc.measure_ne_top h), ENNReal.coe_eq_one] at h1
  refine ⟨hm, ?_⟩
  change μ.map e = μ
  rw [he, h1, one_smul]

theorem integral_integral (hle : N' ≤ N) (hn : ∀ p ∈ N, ∀ n ∈ N', p * n * p⁻¹ ∈ N') (hc : Cocompact Γ N)
    (hc' : Cocompact Γ N') (μ : Measure N) [μ.IsHaarMeasure] (μ' : Measure N') [μ'.IsHaarMeasure]
    {φ : G → ℂ} (hφ : LeftInv Γ φ) (hφc : Continuous φ) (x : G) :
    ∫ n in stdDom (Γ.subgroupOf N), ∫ m in stdDom (Γ.subgroupOf N'), φ (m * (n * x)) ∂μ' ∂μ =
      μ'.real (stdDom (Γ.subgroupOf N'))⁻¹ • ∫ n in stdDom (Γ.subgroupOf N), φ (n * x) ∂μ := by
  have hp : ∀ p : pairs Γ hn, MeasurePreserving (fun z : N' × N => p • z) (μ'.prod μ) (μ'.prod μ) := fun p => by
    have := ((measurePreserving_mul_left μ' ⟨_, p.2.2.2⟩).comp (measurePreserving_conj hc' μ' p.2.2.1
      (hn _ p.1.2.2) (hn _ (inv_mem p.1.2.2)))).prod (measurePreserving_mul_left μ p.1.2)
    convert this using 1
    funext z
    exact Prod.ext (Subtype.ext (by simp [smul_fst, mul_assoc])) rfl
  have : MeasurableConstSMul (pairs Γ hn) (N' × N) := ⟨fun p => (hp p).measurable⟩
  have : SMulInvariantMeasure (pairs Γ hn) (N' × N) (μ'.prod μ) :=
    ⟨fun p s hs => (hp p).measure_preimage hs.nullMeasurableSet⟩
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have : Countable (pairs Γ hn) :=
    Function.Injective.countable (f := fun p : pairs Γ hn => ((⟨_, p.2.1⟩, ⟨_, p.2.2.1⟩) : Γ × Γ)) fun p q h =>
      Subtype.ext (Prod.ext (Subtype.ext (congrArg (fun z : Γ × Γ => z.1.1) h))
        (Subtype.ext (congrArg (fun z : Γ × Γ => z.2.1) h)))
  have hA := measurableSet_stdDom (Γ.subgroupOf N')
  have hB := measurableSet_stdDom (Γ.subgroupOf N)
  have hi : Continuous (Subgroup.inclusion hle) := continuous_subtype_val.subtype_mk _
  have ht : MeasurePreserving (fun z : N' × N => (z.1, Subgroup.inclusion hle z.1 * z.2)) (μ'.prod μ) (μ'.prod μ) :=
    (MeasurePreserving.id μ').skew_product (g := fun m n => Subgroup.inclusion hle m * n)
      (Continuous.measurable (by fun_prop)) (.of_forall fun m => map_mul_left_eq_self μ _)
  have d1 := IsFundamentalDomain.mk' (μ := μ'.prod μ) (hA.prod hB).nullMeasurableSet
    (existsUnique_prod (hn := hn) hle (existsUnique_stdDom _) (existsUnique_stdDom _))
  have d2 := IsFundamentalDomain.mk' (μ := μ'.prod μ) (ht.measurable (hA.inv.prod hB)).nullMeasurableSet
    (existsUnique_shear (hn := hn) hle (existsUnique_stdDom _) (existsUnique_stdDom _))
  have e := d1.setIntegral_eq d2 (f := fun z : N' × N => φ (z.1 * (z.2 * x))) fun p z => by
    rw [smul_fst, smul_snd, ← hφ _ p.2.1 (z.1 * (z.2 * x))]
    simp [mul_assoc]
  have : IsFiniteMeasure (μ.restrict (stdDom (Γ.subgroupOf N))) :=
    isFiniteMeasure_restrict.2 (hc.measure_ne_top (isFundamentalDomain_stdDom _ _))
  have : IsFiniteMeasure (μ'.restrict (stdDom (Γ.subgroupOf N'))) :=
    isFiniteMeasure_restrict.2 (hc'.measure_ne_top (isFundamentalDomain_stdDom _ _))
  obtain ⟨K, hK, hs⟩ := id hc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (f := fun n : N => φ (n * x)) (by fun_prop)
  have hb : ∀ n : N, ‖φ (n * x)‖ ≤ C := fun n =>
    let ⟨γ, hγ, hk⟩ := hs n
    (congrArg norm (leftInv_integrand hφ x γ hγ n)).ge.trans (hC _ hk)
  rw [← Measure.prod_restrict, integral_prod_symm _ (.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) C
    (.of_forall fun z => by simpa [mul_assoc] using hb (Subgroup.inclusion hle z.1 * z.2)))] at e
  have e2 := integral_map (f := fun z : N' × N => φ (z.2 * x))
    (ht.restrict_preimage (hA.inv.prod hB)).aemeasurable (Continuous.aestronglyMeasurable (by fun_prop))
  rw [(ht.restrict_preimage (hA.inv.prod hB)).map_eq, ← Measure.prod_restrict,
    integral_fun_snd (fun n : N => φ (n * x)), measureReal_restrict_apply_univ] at e2
  rw [e, e2]
  simp [mul_assoc]

theorem constTermOn_stages (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (Γ N N' : Subgroup G) [DiscreteTopology Γ] [LocallyCompactSpace N] [LocallyCompactSpace N'] (hle : N' ≤ N)
    (hn : ∀ p ∈ N, ∀ n ∈ N', p * n * p⁻¹ ∈ N') (hc : Cocompact Γ N) (hc' : Cocompact Γ N') (φ : G → ℂ)
    (hφ : LeftInv Γ φ) (hφc : Continuous φ) (x : G) :
    constTermOn Γ N φ x = constTermOn Γ N (constTermOn Γ N' φ) x := by
  have h := isFundamentalDomain_stdDom (Γ.subgroupOf N) Measure.haar
  have h' := isFundamentalDomain_stdDom (Γ.subgroupOf N') Measure.haar
  have h0 := ENNReal.toReal_ne_zero.2 ⟨h.measure_ne_zero (NeZero.ne _), hc.measure_ne_top h⟩
  have h0' := ENNReal.toReal_ne_zero.2 ⟨h'.measure_ne_zero (NeZero.ne _), hc'.measure_ne_top h'⟩
  rw [← measureReal_def] at h0 h0'
  have e1 := integral_integral hle hn hc hc' Measure.haar Measure.haar (φ := fun _ => 1) (fun _ _ _ => rfl)
    continuous_const x
  have e2 : Measure.haar.real (stdDom (Γ.subgroupOf N'))⁻¹ = Measure.haar.real (stdDom (Γ.subgroupOf N')) := by
    simp only [integral_const, measureReal_restrict_apply_univ, smul_smul] at e1
    have := smul_left_injective ℝ (one_ne_zero (α := ℂ)) e1
    rw [mul_comm] at this
    exact (mul_right_cancel₀ h0 this).symm
  rw [constTermOn_eq h hφ, constTermOn_eq' h fun γ hγ n => by
    simp only [Subgroup.coe_mul, mul_assoc]
    exact constTermOn_mul_left_of_normalizer hφ hγ
      (fun m => ⟨hn _ γ.2 m, fun hm => by simpa [mul_assoc] using hn _ (inv_mem γ.2) _ hm⟩) _]
  simp only [constTermOn_eq h' hφ]
  rw [integral_smul, integral_integral hle hn hc hc' _ _ hφ hφc, e2, inv_smul_smul₀ h0']

end GlobalTheory.Cusp.Stages

end
end

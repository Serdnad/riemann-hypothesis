module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1357
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1365
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle265
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1362
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Formalism.DoubleCosetMeasures.StatementZ
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TwOrbLat

section Top

variable {E : Type} [Field E] [NumberField E] {w : Pl E} {a : ℕ}

theorem isCompact_boundedGL (R : ℝ) :
    IsCompact {g : GLw a w | ∀ i j, ‖g.val i j‖ ≤ R ∧ ‖(g⁻¹).val i j‖ ≤ R} := by
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion E w
  have hK : IsCompact {A : Matrix (Fin a) (Fin a) (w.adicCompletion E) | ∀ i j, ‖A i j‖ ≤ R} := by
    have h : IsCompact (Set.pi Set.univ fun _ : Fin a => Set.pi Set.univ fun _ : Fin a =>
        Metric.closedBall (0 : w.adicCompletion E) R) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
    have e : {A : Matrix (Fin a) (Fin a) (w.adicCompletion E) | ∀ i j, ‖A i j‖ ≤ R} =
        (Set.pi Set.univ fun _ : Fin a => Set.pi Set.univ fun _ : Fin a =>
          Metric.closedBall (0 : w.adicCompletion E) R) :=
      Set.ext fun A => ⟨fun hA i _ j _ => by simpa using hA i j, fun hA i j => by simpa using hA i trivial j trivial⟩
    rw [e]
    exact h
  have h := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin a) (Fin a) (w.adicCompletion E))).isCompact_preimage
    (hK.prod (hK.image MulOpposite.continuous_op))
  convert h using 1
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod,
    (MulOpposite.op_injective).mem_set_image]
  exact ⟨fun hg => ⟨fun i j => (hg i j).1, fun i j => (hg i j).2⟩, fun hg i j => ⟨hg.1 i j, hg.2 i j⟩⟩

theorem isCompact_closure_zpowers_iff (g : GLw a w) :
    IsCompact (closure (Subgroup.zpowers g : Set (GLw a w))) ↔
      ∃ R : ℝ, ∀ n : ℤ, ∀ i j, ‖(g ^ n).val i j‖ ≤ R := by
  constructor
  · intro hc
    have hb : ∀ i j : Fin a, ∃ C : ℝ, ∀ h ∈ closure (Subgroup.zpowers g : Set (GLw a w)), ‖h.val i j‖ ≤ C :=
      fun i j => hc.exists_bound_of_continuousOn (f := fun h : GLw a w => h.val i j)
        ((Units.continuous_val (M := Matrix (Fin a) (Fin a) (w.adicCompletion E))).matrix_elem i j).continuousOn
    choose C hC using hb
    refine ⟨∑ i, ∑ j, max (C i j) 0, fun n i j => ?_⟩
    have h1 := hC i j (g ^ n) (subset_closure (Subgroup.zpow_mem_zpowers g n))
    calc _ ≤ max (C i j) 0 := h1.trans (le_max_left _ _)
      _ ≤ ∑ j', max (C i j') 0 :=
        Finset.single_le_sum (f := fun j' => max (C i j') 0) (fun _ _ => le_max_right _ _) (Finset.mem_univ j)
      _ ≤ _ := Finset.single_le_sum (f := fun i' => ∑ j', max (C i' j') 0)
        (fun _ _ => Finset.sum_nonneg fun _ _ => le_max_right _ _) (Finset.mem_univ i)
  · rintro ⟨R, hR⟩
    refine (isCompact_boundedGL R).closure_of_subset ?_
    intro h hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    refine fun i j => ⟨hR n i j, ?_⟩
    rw [← _root_.zpow_neg]
    exact hR (-n) i j

end Top

section Alg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
  (e : K.E ≃+* w.adicCompletion E) {a : ℕ} {B : GlobalTheory.UnitLemma.InvAlg K} (b : Module.Basis (Fin a) K.E B.A)

omit [IsCMField E] in
theorem norm_le_one_iff_mem (he : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) (x : K.E) :
    ‖e x‖ ≤ 1 ↔ x ∈ (algebraMap K.O K.E).range := by
  rw [he]
  exact Valued.toNormedField.norm_le_one_iff


omit [IsCMField E] in
theorem exists_norm_ge (he : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) (R : ℝ) :
    ∃ c : K.E, c ≠ 0 ∧ R ≤ ‖e c‖ := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  have hπ0 : algebraMap K.O K.E π ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective K.O K.E)]
    exact hπ.ne_zero
  have hn : ¬ (algebraMap K.O K.E π)⁻¹ ∈ (algebraMap K.O K.E).range := by
    rintro ⟨o, ho⟩
    apply hπ.not_isUnit
    have h : π * o = 1 := IsFractionRing.injective K.O K.E (by rw [map_mul, ho, mul_inv_cancel₀ hπ0, map_one])
    exact isUnit_iff_exists_inv.2 ⟨o, h⟩
  have h1 : 1 < ‖e (algebraMap K.O K.E π)⁻¹‖ := by
    rw [← not_le, norm_le_one_iff_mem e he]
    exact hn
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt R h1
  refine ⟨((algebraMap K.O K.E π)⁻¹) ^ n, pow_ne_zero _ (inv_ne_zero hπ0), ?_⟩
  rw [map_pow, norm_pow]
  exact hn.le


omit [IsCMField E] in
theorem exists_fg_of_crd_le (he : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) (R : ℝ) :
    ∃ M : Submodule K.O B.A, M.FG ∧ ∀ y, (∀ i, ‖crd e b y i‖ ≤ R) → y ∈ M := by
  obtain ⟨c, hc0, hc⟩ := exists_norm_ge e he R
  refine ⟨Submodule.span K.O (Set.range fun j => c • b j), Submodule.fg_span (Set.finite_range _), fun y hy => ?_⟩
  have hec : e c ≠ 0 := by rwa [Ne, map_eq_zero_iff _ e.injective]
  rw [← b.sum_repr y]
  refine Submodule.sum_mem _ fun j _ => ?_
  have hm : b.repr y j / c ∈ (algebraMap K.O K.E).range := by
    rw [← norm_le_one_iff_mem e he, map_div₀, norm_div, div_le_one (norm_pos_iff.2 hec)]
    exact (hy j).trans hc
  obtain ⟨o, ho⟩ := hm
  have : b.repr y j • b j = o • (c • b j) := by
    rw [← algebraMap_smul K.E o, smul_smul, ho, div_mul_cancel₀ _ hc0]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem isIntegral_of_bounded (he : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) (u : B.A)
    (R : ℝ) (hR : ∀ n : ℕ, ∀ i j, ‖mulHom e b (u ^ n) i j‖ ≤ R) : IsIntegral K.O u := by
  obtain ⟨M, hMfg, hM⟩ := exists_fg_of_crd_le e b he (∑ j, R * ‖crd e b 1 j‖)
  have hle : Subalgebra.toSubmodule (Algebra.adjoin K.O {u}) ≤ M := by
    rw [Algebra.adjoin_eq_span, Submodule.span_le, ← Submonoid.powers_eq_closure]
    rintro _ ⟨n, rfl⟩
    refine hM _ fun i => ?_
    have h1 : crd e b (u ^ n) = mulHom e b (u ^ n) *ᵥ crd e b 1 := by rw [← crd_mul, mul_one]
    rw [h1]
    simp only [Matrix.mulVec, dotProduct]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hR n i j) (norm_nonneg _)
  haveI : IsNoetherian K.O M := isNoetherian_of_fg_of_noetherian M hMfg
  haveI : IsNoetherian K.O (Subalgebra.toSubmodule (Algebra.adjoin K.O {u})) := isNoetherian_of_le hle
  exact isIntegral_of_submodule_noetherian _ this u (Algebra.self_mem_adjoin_singleton K.O u)

theorem bounded_of_fg (he : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) (M : Submodule K.O B.A)
    (hM : M.FG) : ∃ R : ℝ, ∀ y ∈ M, ∀ i j, ‖mulHom e b y i j‖ ≤ R := by
  obtain ⟨S, rfl⟩ := hM
  refine ⟨∑ y ∈ S, ∑ i, ∑ j, ‖mulHom e b y i j‖, fun x hx i j => ?_⟩
  obtain ⟨f, -, rfl⟩ := Submodule.mem_span_finset.1 hx
  have hsum : mulHom e b (∑ y ∈ S, f y • y) i j = ∑ y ∈ S, e (algebraMap K.O K.E (f y)) * mulHom e b y i j := by
    rw [mulHom_apply]
    simp only [mulHom_apply, Finset.sum_mul, smul_mul_assoc]

    simp only [← algebraMap_smul K.E (f _), map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, smul_eq_mul, map_mul]
  rw [hsum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
  rw [norm_mul]
  have h1 : ‖e (algebraMap K.O K.E (f y))‖ ≤ 1 := (norm_le_one_iff_mem e he _).2 ⟨f y, rfl⟩
  calc _ ≤ 1 * ‖mulHom e b y i j‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = ‖mulHom e b y i j‖ := one_mul _
    _ ≤ ∑ j', ‖mulHom e b y i j'‖ :=
      Finset.single_le_sum (f := fun j' => ‖mulHom e b y i j'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', ‖mulHom e b y i' j'‖ :=
      Finset.single_le_sum (f := fun i' => ∑ j', ‖mulHom e b y i' j'‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)

end Alg

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
  (e : K.E ≃+* w.adicCompletion E) {a : ℕ} {B : GlobalTheory.UnitLemma.InvAlg K} (b : Module.Basis (Fin a) K.E B.A)

theorem mulGL_zpow_val (t : B.Aˣ) (n : ℤ) : ((mulGL e b t) ^ n).val = mulHom e b ((t ^ n : B.Aˣ) : B.A) := by
  rw [← map_zpow]
  rfl

theorem isCompact_closure_zpowers_mulGL_iff' (he : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1)
    (t : B.Aˣ) : IsCompact (closure (Subgroup.zpowers (mulGL e b t) : Set (GLw a w))) ↔
      t ∈ GlobalTheory.UnitLemma.intUnits K.O B.A := by
  rw [isCompact_closure_zpowers_iff]
  simp only [mulGL_zpow_val]
  constructor
  · rintro ⟨R, hR⟩
    refine ⟨isIntegral_of_bounded e b he _ R fun n i j => ?_, isIntegral_of_bounded e b he _ R fun n i j => ?_⟩
    · have := hR n i j
      rwa [zpow_natCast, Units.val_pow_eq_pow_val] at this
    · have := hR (-(n : ℤ)) i j
      rwa [_root_.zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val] at this
  · rintro ⟨h1, h2⟩
    obtain ⟨R, hR⟩ := bounded_of_fg e b he _
      (fg_adjoin_of_finite (s := {(t : B.A), ((t⁻¹ : B.Aˣ) : B.A)}) (Set.toFinite _)
        (by rintro x (rfl | rfl); exacts [h1, h2]))
    refine ⟨R, fun n i j => hR _ ((Subalgebra.mem_toSubmodule _).2 ?_) i j⟩
    obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg n
    · rw [zpow_natCast, Units.val_pow_eq_pow_val]
      exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_insert _ _)) k
    · rw [_root_.zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val]
      exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_insert_of_mem _ (Set.mem_singleton _))) k

end Main

theorem isCompact_closure_zpowers_mulGL_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (a : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K) (b : Module.Basis (Fin a) K.E B.A) (t : B.Aˣ), IsCompact (closure (Subgroup.zpowers (GlobalTheory.TwOrbLat.mulGL e b t) : Set (GLw a w))) ↔ t ∈ GlobalTheory.UnitLemma.intUnits K.O B.A :=
  fun _ _ _ _ _ _ e he _ _ b t => isCompact_closure_zpowers_mulGL_iff' e b he t

end GlobalTheory.TwOrbLat
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TwOrbLat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
  (e : K.E ≃+* w.adicCompletion E) {a : ℕ} {B : GlobalTheory.UnitLemma.InvAlg K} (b : Module.Basis (Fin a) K.E B.A)

theorem crd_smulO (c : K.O) (y : B.A) : crd e b (c • y) = e (algebraMap K.O K.E c) • crd e b y := by
  rw [← crd_smul, algebraMap_smul]

theorem crd_zero : crd e b (0 : B.A) = 0 := by
  funext i; simp [crd]

theorem mem_lat_iff (he : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) (q : GLw a w) (y : B.A) :
    y ∈ GlobalTheory.TwLat.lat e b q ↔ ∀ i, Valued.v (((q⁻¹ : GLw a w).val *ᵥ crd e b y) i) ≤ 1 := by
  rw [latOf_eq]
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      intro i
      rw [crd_ofCrd, ← col_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
    | zero => intro i; simp [crd_zero]
    | add x z _ _ hx hz =>
      intro i
      rw [crd_add, Matrix.mulVec_add, Pi.add_apply]
      exact (Valued.v.map_add _ _).trans (max_le (hx i) (hz i))
    | smul c x _ hx =>
      intro i
      rw [crd_smulO, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul]
      exact mul_le_one' ((he _).1 ⟨c, rfl⟩) (hx i)
  · intro h
    choose c hc using fun j => (he (e.symm (((q⁻¹ : GLw a w).val *ᵥ crd e b y) j))).2 (by
      rw [RingEquiv.apply_symm_apply]; exact h j)
    have hy : y = ∑ j, c j • ofCrd e b (fun i => q.val i j) := by
      apply crd_injective e b
      rw [crd_sum]
      have h1 : crd e b y = q.val *ᵥ ((q⁻¹ : GLw a w).val *ᵥ crd e b y) := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
      conv_lhs => rw [h1]
      funext i
      simp only [crd_smulO, hc, RingEquiv.apply_symm_apply, crd_ofCrd, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, Matrix.mulVec, dotProduct]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [hy]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem lat_le_iff (he : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) (q q' : GLw a w) :
    GlobalTheory.TwLat.lat e b q ≤ GlobalTheory.TwLat.lat e b q' ↔ ∀ i j, Valued.v ((q'⁻¹ * q : GLw a w).val i j) ≤ 1 := by
  constructor
  · intro hle i j
    have hm : ofCrd e b (fun i => q.val i j) ∈ GlobalTheory.TwLat.lat e b q := by
      rw [latOf_eq]; exact Submodule.subset_span ⟨j, rfl⟩
    have := (mem_lat_iff e b he q' _).1 (hle hm) i
    rw [crd_ofCrd, ← col_mul, ← Units.val_mul] at this
    exact this
  · intro h
    conv_lhs => rw [latOf_eq]
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, mem_lat_iff e b he, crd_ofCrd, ← col_mul, ← Units.val_mul]
    exact fun i => h i j

theorem lat_eq_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ)
    (e : K.E ≃+* w.adicCompletion E), (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) →
    ∀ (a : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K) (b : Module.Basis (Fin a) K.E B.A) (q q' : GLw a w),
    GlobalTheory.TwLat.lat e b q = GlobalTheory.TwLat.lat e b q' ↔ q⁻¹ * q' ∈ GlobalTheory.LFun.KGL w (n := a) := by
  intro E _ _ _ w K e he a B b q q'
  rw [le_antisymm_iff, lat_le_iff e b he, lat_le_iff e b he, GlobalTheory.LFun.KGL, GlobalTheory.AdelicU.mem_GLint_iff,
    _root_.mul_inv_rev, inv_inv]
  exact and_comm

end GlobalTheory.TwOrbLat
end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes ValuativeRel
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.StdPairCone
open GlobalTheory.Doubling (absE)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.SplitFlip GlobalTheory.SplitWeil

noncomputable section
namespace GlobalTheory.StdPairZetaB
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem blk₁_mul_left {m a a' : ℕ} (M : Matrix (Fin m) (Fin m) k) (X : Matrix (Fin m) (Fin (a + a')) k) :
    blk₁ (M * X) = M * blk₁ X := by
  ext i j; simp [blk₁, Matrix.mul_apply]

theorem blk₂_mul_left {m a a' : ℕ} (M : Matrix (Fin m) (Fin m) k) (X : Matrix (Fin m) (Fin (a + a')) k) :
    blk₂ (M * X) = M * blk₂ X := by
  ext i j; simp [blk₂, Matrix.mul_apply]

theorem cball_mul_left {m n : ℕ} {s : kˣ} {M : Matrix (Fin m) (Fin m) k} (hM : ∀ i j, M i j ∈ 𝒪[k])
    {N : Matrix (Fin m) (Fin n) k} (hN : ∀ i j, N i j ∈ cball s) : ∀ i j, (M * N) i j ∈ cball s := fun i j => by
  have hN' : ∀ i j, valuation k (N i j) ≤ valuation k (s : k) := hN
  change valuation k _ ≤ valuation k (s : k)
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [map_mul]
  exact (mul_le_mul' (hM i l) (hN' l j)).trans (by rw [one_mul])

theorem mem_KO_of_isGLO {n : ℕ} (g : GL (Fin n) k) (h : IsGLO g.val) : g ∈ KO k (Fin n) := by
  let A : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨g.val i j, h.1 i j⟩
  have e : (algebraMap 𝒪[k] k).mapMatrix A = g.val := rfl
  have hu : IsUnit A.det := by
    refine (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.2 ?_
    rw [RingHom.map_det, e]; exact h.2
  obtain ⟨u, hu'⟩ := (Matrix.isUnit_iff_isUnit_det A).2 hu
  refine ⟨u, Units.ext ?_⟩
  change (algebraMap 𝒪[k] k).mapMatrix u.val = g.val
  rw [hu', e]

theorem isGLO_of_mem_KO {n : ℕ} {g : GL (Fin n) k} (h : g ∈ KO k (Fin n)) : IsGLO g.val :=
  ⟨((mem_KO_iff g).1 h).1, valuation_gdet_of_mem_KO h⟩

end GlobalTheory.StdPairZetaB


open GlobalTheory.StdPairZetaB in
theorem GlobalTheory.StdPairZetaB.smallF_stdB : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ),
    (∀ Y : Matrix (Fin a') (Fin (a + a')) k, (blk₂ Y).det = 0 →
      smallF (haarVol (KO k (Fin a'))) ν (stdB ν ϖ c a a') Y = 0) ∧
    ∀ (Y : Matrix (Fin a') (Fin (a + a')) k) (g₂ : GL (Fin a') k), g₂.val = blk₂ Y →
      smallF (haarVol (KO k (Fin a'))) ν (stdB ν ϖ c a a') Y =
        (((ν (gdet g₂))⁻¹ : ℂˣ) : ℂ) * apow (gdet g₂) (-((Fintype.card (Fin (a + a')) : ℂ) / 2)) *
          Set.indicator {M : Matrix (Fin a') (Fin a) k | ∀ i j, M i j ∈ cball (ϖ ^ c)} 1 ((g₂⁻¹).val * blk₁ Y) := by
  intro k _ _ _ _ _ _ ν ϖ c a a'
  refine ⟨fun Y hY => ?_, fun Y g₂ hg₂ => ?_⟩
  · have h0 : ∀ g : GL (Fin a') k, stdB ν ϖ c a a' (g.val * Y) = 0 := fun g => by
      unfold stdB
      rw [dite_eq_right]
      rintro ⟨h0, -⟩
      apply h0
      rw [blk₂_mul_left, Matrix.det_mul, hY, mul_zero]
    simp [smallF, h0]
  · set d : ℂ := (Fintype.card (Fin (a + a')) : ℂ) / 2 with hd
    set C : ℂ := (((ν (gdet g₂))⁻¹ : ℂˣ) : ℂ) * apow (gdet g₂) (-d) *
      Set.indicator {M : Matrix (Fin a') (Fin a) k | ∀ i j, M i j ∈ cball (ϖ ^ c)} 1 ((g₂⁻¹).val * blk₁ Y) with hC
    set S : Set (GL (Fin a') k) := (fun g => g * g₂) ⁻¹' (KO k (Fin a') : Set (GL (Fin a') k)) with hSdef
    have hSm : @MeasurableSet (GL (Fin a') k) Units.instMeasurableSpace S := by
      letI : MeasurableSpace (GL (Fin a') k) := Units.instMeasurableSpace
      haveI : BorelSpace (GL (Fin a') k) := borel_GL
      exact (isOpen_KO.preimage (continuous_mul_const _)).measurableSet
    have hS1 : (haarVol (KO k (Fin a'))).real S = 1 := by
      simp [hSdef, Measure.real, measure_preimage_mul_right, haarVol_self isOpen_KO le_rfl]
    have hint : ∀ g : GL (Fin a') k, stdB ν ϖ c a a' (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) d =
        S.indicator (fun _ => C) g := by
      intro g
      have hb₂ : blk₂ (g.val * Y) = g.val * blk₂ Y := blk₂_mul_left _ _
      have hb₁ : blk₁ (g.val * Y) = g.val * blk₁ Y := blk₁_mul_left _ _
      by_cases hg : g ∈ S
      · rw [Set.indicator_of_mem hg]
        have hκ : g * g₂ ∈ KO k (Fin a') := hg
        have hG := isGLO_of_mem_KO hκ
        have e₂ : blk₂ (g.val * Y) = (g * g₂).val := by rw [hb₂, ← hg₂, Units.val_mul]
        have e₁ : blk₁ (g.val * Y) = (g * g₂).val * ((g₂⁻¹).val * blk₁ Y) := by
          rw [hb₁, ← Matrix.mul_assoc, Units.val_mul, Matrix.mul_assoc g.val, ← Units.val_mul, mul_inv_cancel,
            Units.val_one, Matrix.mul_one]
        have hgd : gdet g = gdet (g * g₂) * (gdet g₂)⁻¹ := by rw [gdet_mul]; group
        have hap : apow (gdet g) d = apow (gdet g₂) (-d) := by
          rw [hgd, apow_mul, apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hκ), one_mul, apow_inv]
        unfold stdB
        by_cases hP : ∀ i j, ((g₂⁻¹).val * blk₁ Y) i j ∈ cball (ϖ ^ c)
        · have hcond : (blk₂ (g.val * Y)).det ≠ 0 ∧ IsGLO (blk₂ (g.val * Y)) ∧
              ∀ i j, blk₁ (g.val * Y) i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) := by
            rw [e₂, e₁]
            exact ⟨(g * g₂).det_ne_zero, hG, cball_mul_left hG.1 hP⟩
          rw [dite_eq_left hcond, hC, Set.indicator_of_mem (show ((g₂⁻¹).val * blk₁ Y) ∈
            {M : Matrix (Fin a') (Fin a) k | ∀ i j, M i j ∈ cball (ϖ ^ c)} from hP), Pi.one_apply, mul_one, hap]
          have hu : Units.mk0 _ hcond.1 = gdet g * gdet g₂ := Units.ext (by
            rw [Units.val_mk0, Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply,
              Matrix.GeneralLinearGroup.val_det_apply, hb₂, ← hg₂, Matrix.det_mul])
          rw [hu, map_mul, mul_inv_rev, Units.val_mul]
          have h1 : ((ν (gdet g))⁻¹ : ℂˣ) * (ν (gdet g) : ℂ) = 1 := by
            rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
          linear_combination ((((ν (gdet g₂))⁻¹ : ℂˣ) : ℂ) * apow (gdet g₂) (-d)) * h1
        · have hcond : ¬ ((blk₂ (g.val * Y)).det ≠ 0 ∧ IsGLO (blk₂ (g.val * Y)) ∧
              ∀ i j, blk₁ (g.val * Y) i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c)) := by
            rintro ⟨-, -, h3⟩
            apply hP
            have hinv := (mem_KO_iff (g * g₂)).1 hκ
            have := cball_mul_left hinv.2 h3
            rwa [e₁, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul] at this
          rw [dite_eq_right hcond, hC, Set.indicator_of_notMem (show ((g₂⁻¹).val * blk₁ Y) ∉
            {M : Matrix (Fin a') (Fin a) k | ∀ i j, M i j ∈ cball (ϖ ^ c)} from hP)]
          simp
      · rw [Set.indicator_of_notMem hg]
        unfold stdB
        rw [dite_eq_right, zero_mul, zero_mul]
        rintro ⟨-, h2, -⟩
        apply hg
        show g * g₂ ∈ KO k (Fin a')
        apply mem_KO_of_isGLO
        rwa [Units.val_mul, hg₂, ← hb₂]
    rw [smallF, ← hd]
    simp_rw [hint]
    rw [integral_indicator_const (μ := haarVol (KO k (Fin a'))) C hSm, hS1, one_smul]
end
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

theorem _root_.GlobalTheory.T.slice_transform_schwartz_bijective : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {κ : Type} [Fintype κ] {n d : ℕ}
    (ι : ((κ → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ)),
    Set.BijOn ι (SB (κ → k) : Set ((κ → k) → ℂ)) (SB (Matrix (Fin n) (Fin d) k) : Set _) →
    Set.BijOn (GlobalTheory.SwapSlice.sliceT ι) (SB (κ ⊕ κ → k) : Set ((κ ⊕ κ → k) → ℂ))
      (SB (Matrix (Fin n) (Fin d) k × Matrix (Fin n) (Fin d) k) : Set _) := by
  first | exact @GlobalTheory.SwapSliceBij.sliceT_bijOn | exact GlobalTheory.SwapSliceBij.sliceT_bijOn | (intros; apply GlobalTheory.SwapSliceBij.sliceT_bijOn <;> assumption)
end

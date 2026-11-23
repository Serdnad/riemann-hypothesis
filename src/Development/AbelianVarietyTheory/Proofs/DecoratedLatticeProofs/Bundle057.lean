module

import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle082
public import Mathlib.MeasureTheory.Group.Measure
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle006
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymLevelChainTestFunctionAddRow
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle124
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle039
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle006
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle055
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle052
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricLevelsCharactersDoubleCosetsAgreeRation
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle056
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
public import Mathlib.Topology.Algebra.OpenSubgroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge
open scoped Pointwise ENNReal

namespace GlobalTheory.VolRatio

theorem relIndex_mul_measure_sub {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (H L : Subgroup G) (hHL : H ≤ L) [(H.subgroupOf L).FiniteIndex]
    (hH : MeasurableSet (H : Set G)) (μ : Measure G) [μ.IsMulLeftInvariant] :
    (H.relIndex L : ENNReal) * μ H = μ L := by
  apply GlobalTheory.IndexVolume.relIndex_mul_measure_subgroup <;> assumption

theorem vol_ratio : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] (A B : Subgroup G), IsOpen ((A ⊓ B : Subgroup G) : Set G) → IsCompact (A : Set G) → IsCompact (B : Set G) → (μ (A : Set G)).toReal / (μ (B : Set G)).toReal = (B.relIndex A : ℝ) / (A.relIndex B : ℝ) := by
  intro G _ _ _ _ _ μ _ A B hC hA hB
  have hCA : A ⊓ B ≤ A := inf_le_left
  have hCB : A ⊓ B ≤ B := inf_le_right
  haveI : CompactSpace A := isCompact_iff_compactSpace.mp hA
  haveI : CompactSpace B := isCompact_iff_compactSpace.mp hB
  haveI : ((A ⊓ B).subgroupOf A).FiniteIndex := by
    haveI := Subgroup.quotient_finite_of_isOpen ((A ⊓ B).subgroupOf A)
      (hC.preimage continuous_subtype_val)
    exact Subgroup.finiteIndex_of_finite_quotient
  haveI : ((A ⊓ B).subgroupOf B).FiniteIndex := by
    haveI := Subgroup.quotient_finite_of_isOpen ((A ⊓ B).subgroupOf B)
      (hC.preimage continuous_subtype_val)
    exact Subgroup.finiteIndex_of_finite_quotient
  have hCm : MeasurableSet ((A ⊓ B : Subgroup G) : Set G) := hC.measurableSet
  have h1 := relIndex_mul_measure_sub (A ⊓ B) A hCA hCm μ
  have h2 := relIndex_mul_measure_sub (A ⊓ B) B hCB hCm μ
  rw [Subgroup.inf_relIndex_left] at h1
  rw [Subgroup.inf_relIndex_right] at h2
  have hpos : 0 < μ ((A ⊓ B : Subgroup G) : Set G) := hC.measure_pos μ ⟨1, (A ⊓ B).one_mem⟩
  have hfin : μ ((A ⊓ B : Subgroup G) : Set G) < ⊤ :=
    lt_of_le_of_lt (measure_mono hCA) hA.measure_lt_top
  have hr : 0 < (μ ((A ⊓ B : Subgroup G) : Set G)).toReal := ENNReal.toReal_pos hpos.ne' hfin.ne
  rw [← h1, ← h2, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast, mul_div_mul_right _ _ hr.ne']

end GlobalTheory.VolRatio
end

section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX

theorem _root_.GlobalTheory.T.cloud_add_node_le_ten_base_size : ∀ (C : Formalism.MainNotions.Inhab.FC) (cD ch : ℝ) (D : D7) (L : SizeData₂ D), Val C cD ch L → SizesAt L → L.sc.x ≤ L.sc.X' → ∀ τ : D.what₂.Tau, (∀ i j, (((D.hc τ).v i : ℚ) : ℝ) + (((D.hc τ).b j : ℚ) : ℝ) ≤ 10 * L.sc.b) ∧ ∀ j j', (((D.hc τ).b j' : ℚ) : ℝ) - (((D.hc τ).b j : ℚ) : ℝ) ≤ 10 * L.sc.b := by
  first | exact @GlobalTheory.cloud_add_node_le_ten_b | exact GlobalTheory.cloud_add_node_le_ten_b | (intros; apply GlobalTheory.cloud_add_node_le_ten_b <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

theorem _root_.GlobalTheory.T.symLevelChain_testFunction_add_row : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.Pattern t → ∀ (j c : ℕ) (H : j + c = s) (q : Fin c), q.val + 1 ≤ S.ρ → ∀ (x : Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin c) (XIx (Fin κ) t j ⊕ Fin (c + 1)) k), (∀ s', x (Sum.inr q) (Sum.inl s') = 0) → ∀ v : XIx (Fin κ) t j → k, (S.T t).Phi j c H (x + Matrix.of fun r s' => if r = Sum.inr q then Sum.elim v 0 s' else 0) = if ∀ s', valuation k ((((S.ϖ ^ (q.val + 1))⁻¹ : kˣ) : k) * v s') ≤ 1 then (S.T t).Phi j c H x else 0 := by
  first | exact @GlobalTheory.SymChain.RowShift.phi_add_row | exact GlobalTheory.SymChain.RowShift.phi_add_row | (intros; apply GlobalTheory.SymChain.RowShift.phi_add_row <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.TwistRenumber

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem det_torusElt_eq {n : Type} [Fintype n] [DecidableEq n] (ϖ : kˣ) (e : n → ℤ) :
    GeneralLinearGroup.det (torusElt k n ϖ e) = ϖ ^ ∑ i, e i := by
  ext
  rw [GeneralLinearGroup.val_det_apply, val_torusElt, det_diagonal, Units.val_zpow_eq_zpow_val]
  induction (Finset.univ : Finset n) using Finset.induction_on with
  | empty => simp
  | insert i t hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, zpow_add₀ ϖ.ne_zero, ih]

theorem sum_indic {n : Type} [Fintype n] [DecidableEq n] (s : Finset n) : ∑ i, indic s i = (s.card : ℤ) := by
  simp [indic, Finset.sum_ite_mem]

theorem reGL_symm_reGL {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n)
    (g : GL m k) : GlobalTheory.ChainStepSupp.reGL k e.symm (GlobalTheory.ChainStepSupp.reGL k e g) = g := by
  ext i j
  simp [GlobalTheory.ChainStepSupp.val_reGL]

theorem reGL_mem_KO_iff {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n)
    {g : GL m k} : GlobalTheory.ChainStepSupp.reGL k e g ∈ KO k n ↔ g ∈ KO k m :=
  ⟨fun h => reGL_symm_reGL e g ▸ GlobalTheory.ChainStepSupp.reGL_mem_KO e.symm h, GlobalTheory.ChainStepSupp.reGL_mem_KO e⟩

theorem unram_det_KO {μ₀ : kˣ →* ℂˣ} (hμ : IsUnram μ₀) {n : Type} [Fintype n] [DecidableEq n] {κ : GL n k}
    (hκ : κ ∈ KO k n) : μ₀ (GeneralLinearGroup.det κ) = 1 :=
  hμ _ ((nabs_eq_one_iff _).1 (nabs_det_of_mem_KO hκ))

theorem unram_det_dcoset {μ₀ : kˣ →* ℂˣ} (hμ : IsUnram μ₀) {n : Type} [Fintype n] [DecidableEq n] {ϖ : kˣ}
    {s : Finset n} {g : GL n k}
    (h : ∃ κ ∈ KO k n, ∃ κ' ∈ KO k n, g = κ * torusElt k n ϖ (indic s) * κ') :
    μ₀ (GeneralLinearGroup.det g) = μ₀ ϖ ^ s.card := by
  obtain ⟨κ, hκ, κ', hκ', rfl⟩ := h
  rw [map_mul, map_mul, map_mul, map_mul, unram_det_KO hμ hκ, unram_det_KO hμ hκ', det_torusElt_eq, sum_indic,
    map_zpow, one_mul, mul_one, zpow_natCast]


open Classical in
theorem isRepsK_image {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n)
    {g₀ : GL m k} {R : Finset (GL m k)} (hR : IsRepsK g₀ R) :
    IsRepsK (GlobalTheory.ChainStepSupp.reGL k e g₀) (R.image (GlobalTheory.ChainStepSupp.reGL k e)) := by
  refine ⟨fun g' hg' => ?_, fun κ hκ => ?_⟩
  · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hg'
    obtain ⟨a, ha, b, hb, rfl⟩ := hR.1 g hg
    exact ⟨_, GlobalTheory.ChainStepSupp.reGL_mem_KO e ha, _, GlobalTheory.ChainStepSupp.reGL_mem_KO e hb, by simp only [map_mul]⟩
  · obtain ⟨g, ⟨hg, hgK⟩, huniq⟩ := hR.2 (GlobalTheory.ChainStepSupp.reGL k e.symm κ) (GlobalTheory.ChainStepSupp.reGL_mem_KO e.symm hκ)
    have key : ∀ x : GL m k, (GlobalTheory.ChainStepSupp.reGL k e x)⁻¹ * (κ * GlobalTheory.ChainStepSupp.reGL k e g₀) =
        GlobalTheory.ChainStepSupp.reGL k e (x⁻¹ * (GlobalTheory.ChainStepSupp.reGL k e.symm κ * g₀)) := by
      intro x
      rw [map_mul, map_mul, map_inv, GlobalTheory.ChainStepSupp.reGL_reGL_symm]
    refine ⟨GlobalTheory.ChainStepSupp.reGL k e g, ⟨Finset.mem_image_of_mem _ hg, ?_⟩, ?_⟩
    · rw [key]; exact GlobalTheory.ChainStepSupp.reGL_mem_KO e hgK
    · rintro y ⟨hy, hyK⟩
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
      rw [key, reGL_mem_KO_iff] at hyK
      rw [huniq x ⟨hx, hyK⟩]

theorem twist_renumber : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (D : Type) [Fintype D] [DecidableEq D] (N : ℕ) (ε : Fin N ≃ D) (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (μ₀ : kˣ →* ℂˣ), IsUnram μ₀ → ∀ (β : Multiset ℂˣ) (f : GL D k → ℂ), (∀ κ ∈ KO k D, ∀ m, f (κ * m) = f m ∧ f (m * κ) = f m) → (∀ (s : Finset D) R, IsRepsK (torusElt k D ϖ (indic s)) R → ∀ m, ∑ g ∈ R, f (m * g) = genVal (resCard k) 0 (Fintype.card D) β s.card * f m) → ∀ f₂ : GL (Fin N) k → ℂ, (∀ m, f₂ m = (((μ₀ (GeneralLinearGroup.det m))⁻¹ : ℂˣ) : ℂ) * f (GlobalTheory.ChainStepSupp.reGL k ε m)) → (∀ κ ∈ KO k (Fin N), ∀ m, f₂ (κ * m) = f₂ m ∧ f₂ (m * κ) = f₂ m) ∧ ∀ (s : Finset (Fin N)) R, IsRepsK (torusElt k (Fin N) ϖ (indic s)) R → ∀ m, ∑ g ∈ R, f₂ (m * g) = (((μ₀ ϖ)⁻¹ : ℂˣ) : ℂ) ^ s.card * genVal (resCard k) 0 N β s.card * f₂ m := by
  intro k _ _ _ _ D _ _ N ε ϖ hϖ μ₀ hμ β f hf hH f₂ hf₂
  classical
  refine ⟨fun κ hκ m => ?_, fun s R hR m => ?_⟩
  · have hk1 := unram_det_KO hμ hκ
    have hρ := hf (GlobalTheory.ChainStepSupp.reGL k ε κ) (GlobalTheory.ChainStepSupp.reGL_mem_KO ε hκ) (GlobalTheory.ChainStepSupp.reGL k ε m)
    simp only [hf₂, map_mul, hk1, one_mul, mul_one, hρ.1, hρ.2, and_self]
  · set ρ := GlobalTheory.ChainStepSupp.reGL k ε with hρdef
    set s' := s.map ε.toEmbedding with hs'
    have ht : ρ (torusElt k (Fin N) ϖ (indic s)) = torusElt k D ϖ (indic s') := by
      rw [hρdef, GlobalTheory.ChainStepSupp.reGL_torusElt]
      congr 1
      funext d
      simp [indic, hs', Finset.mem_map_equiv]
    have hR' : IsRepsK (torusElt k D ϖ (indic s')) (R.image ρ) := ht ▸ isRepsK_image ε hR
    have hcard : Fintype.card D = N := (Fintype.card_congr ε).symm.trans (Fintype.card_fin N)
    have hH' := hH s' _ hR' (ρ m)
    rw [Finset.sum_image (fun x _ y _ h => ρ.injective h), hs', Finset.card_map, hcard] at hH'
    have hterm : ∀ g ∈ R, f₂ (m * g) = ((((μ₀ (GeneralLinearGroup.det m))⁻¹ : ℂˣ) : ℂ) *
        (((μ₀ ϖ)⁻¹ : ℂˣ) : ℂ) ^ s.card) * f (ρ m * ρ g) := by
      intro g hg
      rw [hf₂, map_mul, map_mul, map_mul, unram_det_dcoset hμ (hR.1 g hg), mul_inv, Units.val_mul, ← inv_pow,
        Units.val_pow_eq_pow_val]
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hH', hf₂]
    ring

end GlobalTheory.TwistRenumber

end
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

namespace GlobalTheory.ParHecke

theorem isHgt_lower : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (H : GL (A ⊕ D) k → ℝ), IsHgt ϖ H → IsHgt ϖ (fun m : GL D k => H (emb₂ k (Equiv.refl (A ⊕ D)) (1, m))) := by
  intro k _ _ _ _ A D _ _ _ _ ϖ H hH
  refine ⟨fun κ hκ g => ?_, fun e => ?_⟩
  · have hK : emb₂ k (Equiv.refl (A ⊕ D)) (1, κ) ∈ KO k (A ⊕ D) :=
      (mem_parahoric.1 (GlobalTheory.ChainStepSupp.emb₂_mem_parahoric (one_mem _) hκ)).1
    have e1 : emb₂ k (Equiv.refl (A ⊕ D)) (1, κ * g) =
        emb₂ k (Equiv.refl (A ⊕ D)) (1, κ) * emb₂ k (Equiv.refl (A ⊕ D)) (1, g) := by
      rw [← map_mul]; simp
    have e2 : emb₂ k (Equiv.refl (A ⊕ D)) (1, g * κ) =
        emb₂ k (Equiv.refl (A ⊕ D)) (1, g) * emb₂ k (Equiv.refl (A ⊕ D)) (1, κ) := by
      rw [← map_mul]; simp
    exact ⟨by simp only [e1]; exact (hH.1 _ hK _).1, by simp only [e2]; exact (hH.1 _ hK _).2⟩
  · show H (emb₂ k (Equiv.refl (A ⊕ D)) (1, torusElt k D ϖ e)) = _
    rw [GlobalTheory.ChainStepSupp.emb₂_one_torusElt, mtor, hH.2]
    congr 2
    simp [sumAbs, Fintype.sum_sum_type]

end GlobalTheory.ParHecke
end

section

open GlobalTheory.KJInf Formalism.L2.Forms Formalism.BasicNotions MvPolynomial

noncomputable section
namespace GlobalTheory.KJInf.ClsVal
variable {ι : Type} [Fintype ι] {a b : ℕ}

theorem evalAt_jetLin (y' : ι → Matrix (Fin b) (Fin b) ℂ) (Λ : FP ι a b →ₗ[ℂ] ℂ)
    (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ Formalism.L2.Ker.DVar ι a b) ℂ) :
    evalAt y' (Formalism.L2.Ker.jetLin (fun m => Λ (monomial m 1)) Q) =
      Λ (aeval (Sum.elim (fun x : ι × Fin b × Fin b => (C (y' x.1 x.2.1 x.2.2) : FP ι a b)) X) Q) := by
  induction Q using MvPolynomial.induction_on' with
  | monomial m c =>
    have hm : (monomial m c : MvPolynomial ((ι × Fin b × Fin b) ⊕ Formalism.L2.Ker.DVar ι a b) ℂ) = c • monomial m 1 := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    have h1 : Formalism.L2.Ker.jetLin (fun m => Λ (monomial m 1)) (monomial m c) =
        c • monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn)
          (Λ (monomial (m.comapDomain Sum.inr Sum.inr_injective.injOn) 1)) := by
      rw [hm, map_smul]
      congr 1
      unfold Formalism.L2.Ker.jetLin
      have := (basisMonomials ((ι × Fin b × Fin b) ⊕ Formalism.L2.Ker.DVar ι a b) ℂ).constr_basis ℂ
        (fun m : ((ι × Fin b × Fin b) ⊕ Formalism.L2.Ker.DVar ι a b) →₀ ℕ => (monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn)
          (Λ (monomial (m.comapDomain Sum.inr Sum.inr_injective.injOn) 1)) : MvPolynomial (ι × Fin b × Fin b) ℂ)) m
      simpa using this
    rw [h1, evalAt, smul_eval, eval_monomial, aeval_monomial, Finsupp.prod_fintype _ _ (by simp),
      Finsupp.prod_fintype _ _ (by simp), Fintype.prod_sum_type]
    have h2 : (∏ i : ι × Fin b × Fin a, (X i : FP ι a b) ^ m (Sum.inr i)) =
        monomial (m.comapDomain Sum.inr Sum.inr_injective.injOn) 1 := by
      rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp)]
      rfl
    simp only [Sum.elim_inl, Sum.elim_inr, h2, ← map_pow, ← map_prod, algebraMap_eq]
    rw [show ∀ (u v : ℂ) (q : FP ι a b), C u * (C v * q) = (u * v) • q from fun u v q => by rw [smul_eq_C_mul, C_mul, mul_assoc], map_smul, smul_eq_mul]
    simp only [Finsupp.comapDomain_apply]
    ring
  | add p q hp hq => rw [map_add (f := _), evalAt, map_add (f := _), ← evalAt, ← evalAt, hp, hq, map_add (f := _), map_add (f := _)]

theorem evalAt_jetMap (hab : a ≤ b) (y' : ι → Matrix (Fin b) (Fin b) ℂ) (Λ : FP ι a b →ₗ[ℂ] ℂ) (k : ι → ℕ) (P : PY ι a) :
    evalAt y' (Formalism.L2.Ker.jetMap (fun m => Λ (monomial m 1)) k P) =
      Λ (subY hab y' (P * ∏ τ, Formalism.L2.Ker.frDet ℂ a τ ^ k τ)) := by
  rw [subY_eq_subD]
  exact evalAt_jetLin y' Λ _

theorem cSpan_eq_VV' {m : ℕ} (lam : ι → DomWeight m) : CSpan lam = Formalism.L2.DIV.VV ℂ lam := by
  unfold CSpan Formalism.L2.DIV.VV Formalism.GradedWeylDivisibility.tensorLat
  congr 1
  ext p
  simp only [Set.mem_ofPred_eq, Formalism.L2.Col.nablaSq_eq_delSq]
  rfl

end GlobalTheory.KJInf.ClsVal
end
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

namespace GlobalTheory.TwBridge.RepsInj

open GlobalTheory.TwBridge.Lev (dc_iff mem_par_iff phi)

theorem reps_injOn : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → IdxProd sel mu cst L → ∀ j c (h : j + 1 + c = s), Set.InjOn (DoubleCoset.mk (GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) (j + 1)) (c + 1) 1) ((W.T s R).lev (j + 1) (c + 1) (by omega)).J ) {g : GL (XIx (Fin R.k) (Fin R.t) (j + 1) ⊕ Fin (c + 1)) k | ∃ b : L.β (j + 1), IsGL ι (L.h (j + 1) b P) g} := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν _hν _hc hA L G _hL hI j c h
  have sameDC (i d : ℕ) (hd : i + d = s + 1) (γ γ' : AutY X R i)
      (g g' : GL (XIx (Fin R.k) (Fin R.t) i ⊕ Fin d) k) (hg : IsGL ι γ g) (hg' : IsGL ι γ' g')
      (hmk : DoubleCoset.mk (GlobalTheory.RootEx.R k _ d 1) ((W.T s R).lev i d hd).J g =
        DoubleCoset.mk (GlobalTheory.RootEx.R k _ d 1) ((W.T s R).lev i d hd).J g') :
      SameDC (Pr := Pr) cst.sharp i P.1 γ γ' := by
    have hc : d = cOf R i := by
      have := hA.steps
      unfold cOf
      omega
    subst d
    obtain ⟨e, he, hg⟩ := hg
    obtain ⟨e', he', hg'⟩ := hg'
    have heq : e' = e := Equiv.ext fun a => Fin.ext ((he' a).trans (he a).symm)
    subst e'
    obtain rfl : g = phi ι e γ := Units.ext hg
    obtain rfl : g' = phi ι e γ' := Units.ext hg'
    let o := stdOrd (Fin R.k) (Fin R.t) i (cOf R i) hd
    have hconj : ∀ g : GL _ k, (plainFrame (k := k) o).conj.symm g = (reGL o).symm g := by
      intro g
      rw [MulEquiv.symm_apply_eq, LatFrame.conj_apply,
        show (plainFrame (k := k) o).bas = 1 from rfl,
        show (plainFrame (k := k) o).ord = o from rfl, MulEquiv.apply_symm_apply]
      simp
    have hJ : ∀ g, g ∈ ((W.T s R).lev i (cOf R i) hd).J ↔
        (reGL o).symm g ∈ (parahoric _ (Fin i × Fin R.t) W.δ W.tame).J := by
      intro g
      rw [← hconj]
      rfl
    have hmem : ∀ γ : AutY X R i, phi ι e γ ∈ ((W.T s R).lev i (cOf R i) hd).J ↔
        γ ∈ Jat (Pr := Pr) cst.sharp i P.1 := by
      intro γ
      rw [hJ, Jat, ite_eq_right hA.nmem]
      exact mem_par_iff hA.compl W.unif hd rfl he W.tame γ
    exact (dc_iff ι hA.compl.dense (fun a => GlobalTheory.SymBridge.Coords.xPos_lt a) he _
      (fun u hu => (hJ u).2 (((parahoric _ (Fin i × Fin R.t) W.δ W.tame).reindex o).KOne_le hu))
      _ hmem γ γ').2 hmk
  rintro g₁ ⟨b, hb⟩ g₂ ⟨b', hb'⟩ hmk
  have hS := sameDC (j + 1) (c + 1) (by omega) _ _ g₁ g₂ hb hb' hmk
  have heq : L.h (j + 1) b P = L.h (j + 1) b' P := hI (j + 1) b b' P hS
  rw [← heq] at hb'
  obtain ⟨e₁, he₁, h₁⟩ := hb
  obtain ⟨e₂, he₂, h₂⟩ := hb'
  have he : e₁ = e₂ := by
    ext a
    exact (he₁ a).trans (he₂ a).symm
  subst he
  exact Units.ext (h₁.trans h₂.symm)

end GlobalTheory.TwBridge.RepsInj
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

theorem _root_.GlobalTheory.T.exists_twistIndex_representative_of_bounds : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → IdxProd sel mu cst L → ∀ j c (h : j + 1 + c = s) (γ : AutY X R (j + 1)), (∀ x ∈ lamYat (Pr := Pr) (R := R) (j + 1) P.1, γ⁻¹ x ∈ lamYat (Pr := Pr) (R := R) (j + 1) P.1 ∧ ((qOf P.1 : X.E) ^ (j + 1)) • γ x ∈ lamYat (Pr := Pr) (R := R) (j + 1) P.1) → (∃ al : L.β j, FiniteSumNonzeroLargeDepth Ch sel mu cst j P (L.h j al P) γ) → Nonempty (L.β (j + 1)) → ∃ b : L.β (j + 1), SameDC (Pr := Pr) cst.sharp (j + 1) P.1 (L.h (j + 1) b P) γ := by
  first | exact @GlobalTheory.MRepsPick.exists_rep_of_bounds | exact GlobalTheory.MRepsPick.exists_rep_of_bounds | (intros; apply GlobalTheory.MRepsPick.exists_rep_of_bounds <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

theorem _root_.GlobalTheory.T.existsUnique_completionMatrix_of_rationalTwistAut : ∀ (X : Fields) (R : Ranks) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (j c : ℕ), c = cOf R j → ∀ γ : AutY X R j, ∃! g : GL (XIx (Fin R.k) (Fin R.t) (j) ⊕ Fin c) k, IsGL ι γ g := by
  first | exact @GlobalTheory.TwBridge.existsUnique_isGL | exact GlobalTheory.TwBridge.existsUnique_isGL | (intros; apply GlobalTheory.TwBridge.existsUnique_isGL <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

theorem _root_.GlobalTheory.T.firstStep_completionRepresentatives_eq_one : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → IdxProd sel mu cst L → ∀ c (h : 0 + c = s), {g : GL (XIx (Fin R.k) (Fin R.t) (0) ⊕ Fin (c + 1)) k | ∃ b : L.β 0, IsGL ι (L.h 0 b P) g} = {1} := by
  first | exact @GlobalTheory.TwBridge.ZeroReps.reps_zero | exact GlobalTheory.TwBridge.ZeroReps.reps_zero | (intros; apply GlobalTheory.TwBridge.ZeroReps.reps_zero <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge GlobalTheory.SymBridge

theorem _root_.GlobalTheory.T.lastStepTestFunction_eq_columnsTestFunction : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), AtTwist (R := R) sel mu cst σ₀ P ι s W → PhiAgree Ch sel mu cst σ₀ P ι s W →
  ∀ (e' : XIx (Fin R.k) (Fin R.t) (s + 1) ≃ Fin (R.N (s + 1))) (e : Ix (Fin R.k ⊕ Fin (s + 1)) (Fin R.t) (s + 2) ⊕ Unit ≃ Fin (R.N R.m)),
    IsOrd xPos e' → IsOrd (Sum.elim zPos fun _ => R.N R.m - 1) e → ∀ (y : HomE X.E (R.N (s + 1)) (R.N R.m)),
      (W.T s R).PhiTop (fromCols (toLoc ι e e' y).toRows₁ 0) =
        σ₀ (PhiTop Ch mu cst.sharp s P.1 (prXp X.E R ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (s + 1))))) := by
  first | exact @GlobalTheory.TwBridge.TopPhi.topPhi | exact GlobalTheory.TwBridge.TopPhi.topPhi | (intros; apply GlobalTheory.TwBridge.TopPhi.topPhi <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

theorem _root_.GlobalTheory.T.parahoricLevels_characters_doubleCosets_agree_rational : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → LevelAgree Ch sel mu cst σ₀ P ι s W := by
  first | exact @GlobalTheory.TwBridge.Lev.levelAgree | exact GlobalTheory.TwBridge.Lev.levelAgree | (intros; apply GlobalTheory.TwBridge.Lev.levelAgree <;> assumption)
end

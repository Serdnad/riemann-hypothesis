module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Aesop.Main
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle048
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle024
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle041
public import GroundTheory.GlobalFields.TateThesis.Bundle001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle050
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle052
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
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.ColFourier
open scoped Pointwise

noncomputable section
namespace GlobalTheory.ColFourier

section Lemmas
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A C : Type} [Fintype A] [DecidableEq C]

theorem mem_maxIdeal_pow_iff {ϖ : kˣ} (hϖ : IsUnif ϖ) (n : ℕ) (r : 𝒪[k]) :
    r ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ n ↔ valuation k (r : k) ≤ valuation k ((ϖ ^ n : kˣ) : k) := by
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    ← (Valuation.integer.integers (valuation k)).le_iff_dvd]
  rfl

theorem natDatum_setCols_eq {ϖ : kˣ} {n : ℕ} {Φ : Matrix A C k → ℂ} (hΦ : IsNatDatum ϖ n Φ) (P : Finset C)
    (Y : Matrix A C k) {U V : Matrix A P k} (h : ∀ i j, U i j - V i j ∈ cball (ϖ ^ n)) :
    Φ (setCols P Y U) = Φ (setCols P Y V) := by
  have h0 : 0 < valuation k ((ϖ ^ n : kˣ) : k) := zero_lt_iff.2 (by simp)
  have hZ : setCols P 0 (U - V) ∈ matLat A ((ϖ ^ n) • stdLat k C) := by
    rw [mem_matLat]
    intro i
    rw [mem_smul_lat, mem_stdLat]
    intro j
    by_cases hj : j ∈ P
    · have h1 := h i ⟨j, hj⟩
      simp only [cball, Set.mem_setOf_eq] at h1
      simp only [Pi.smul_apply, Matrix.row, setCols, of_apply, dif_pos hj, Matrix.sub_apply, Units.smul_def,
        smul_eq_mul]
      rw [Valuation.mem_integer_iff, map_mul, Units.val_inv_eq_inv_val, map_inv₀, inv_mul_le_iff₀ h0, mul_one]
      exact h1
    · simp [Matrix.row, setCols, hj]
  have := hΦ.2 (setCols P Y V) _ hZ
  rw [← this]
  congr 1
  ext i j
  by_cases hj : j ∈ P <;> simp [setCols, hj]

theorem psi_pairCols_eq {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ϖ : kˣ} {n : ℕ} (P : Finset C)
    {Y : Matrix A C k} (hY : ∀ i, ∀ j ∈ P, ((ϖ ^ n : kˣ) : k) * Y i j ∈ 𝒪[k]) {U V : Matrix A P k}
    (h : ∀ i j, U i j - V i j ∈ cball (ϖ ^ n)) : ψ (pairCols P Y U) = ψ (pairCols P Y V) := by
  have h1 : pairCols P Y U = pairCols P Y V + pairCols P Y (U - V) := by
    simp only [pairCols, ← Finset.sum_add_distrib, Matrix.sub_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [h1, AddChar.map_add_eq_mul, hψ.eq_one (y := pairCols P Y (U - V)) ?_, mul_one]
  show valuation k _ ≤ valuation k ((1 : kˣ) : k)
  rw [Units.val_one, map_one]
  refine Valuation.map_sum_le _ fun i _ => Valuation.map_sum_le _ fun j _ => ?_
  have h2 := h i j
  have h3 := hY i j j.2
  rw [cball, Set.mem_setOf_eq] at h2
  rw [Valuation.mem_integer_iff, map_mul] at h3
  rw [map_mul, Matrix.sub_apply]
  exact (mul_le_mul' h2 le_rfl).trans (by rw [mul_comm] at h3 ⊢; exact h3)

end Lemmas

theorem fourierInt_eq_fourierSum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (A C : Type) [Fintype A] [DecidableEq A]
    [DecidableEq C] (ψ : AddChar k Circle) (m : Measure k) (ϖ : kˣ), IsUnif ϖ → HasConductor ψ 1 → IsUnitVol m →
    ∀ (P : Finset C) (n : ℕ) (Φ : Matrix A C k → ℂ), IsNatDatum ϖ n Φ →
      fourierInt ψ m P Φ = fourierSum ψ ϖ n P Φ := by
  intro k _ _ _ _ _ _ A C _ _ _ ψ m ϖ hϖ hψ hm P n Φ hΦ
  haveI := secondCountable k
  haveI := t2Space k
  haveI := hm.1
  have h0 : 0 < valuation k ((ϖ ^ n : kˣ) : k) := zero_lt_iff.2 (by simp)
  funext Y
  rw [fourierSum_apply]
  split_ifs with hY
  · rw [fourierInt]
    set F : Matrix A P k → ℂ := fun U => Φ (setCols P Y U) * (ψ (pairCols P Y U) : ℂ) with hF
    let S : (A → P → Res k n) → Set (Matrix A P k) := fun T =>
      Set.univ.pi fun i => Set.univ.pi fun j => (fun x => x + -liftRes T i j) ⁻¹' cball (ϖ ^ n)
    have hmemS : ∀ T U, U ∈ S T ↔ ∀ i j, U i j - liftRes T i j ∈ cball (ϖ ^ n) := by
      intro T U
      exact ⟨fun h i j => by simpa [sub_eq_add_neg] using h i trivial j trivial,
        fun h i _ j _ => by simpa [sub_eq_add_neg] using h i j⟩
    have hS : ∀ T, MeasurableSet (S T) := fun T =>
      MeasurableSet.univ_pi fun i => MeasurableSet.univ_pi fun j =>
        (isOpen_cball _).measurableSet.preimage (measurable_add_const _)
    have hcb : m (cball (ϖ ^ n)) = (distribHaarChar k (ϖ ^ n) : ENNReal) := by
      rw [measure_cball, hm.2, mul_one]
    have hvolE : ∀ T, (volM m A P) (S T) = (distribHaarChar k (ϖ ^ n) : ENNReal) ^ (Fintype.card A * P.card) := by
      intro T
      simp only [volM, S]
      refine (Measure.pi_pi (fun _ : A => Measure.pi fun _ : P => m)
        (fun i => Set.univ.pi fun j => (fun x => x + -liftRes T i j) ⁻¹' cball (ϖ ^ n))).trans ?_
      simp only [Measure.pi_pi, measure_preimage_add_right, hcb, Finset.prod_const, Finset.card_univ,
        Fintype.card_coe, ← pow_mul]
      rw [mul_comm]
    have hnabs : nabs k (ϖ ^ n) = ((resCard k : ℝ) ^ n)⁻¹ := by
      have h1 : ∀ l : ℕ, nabs k (ϖ ^ l) = nabs k ϖ ^ l := by
        intro l; induction l with
        | zero => simp [nabs_one]
        | succ l ih => rw [pow_succ, nabs_mul, ih, pow_succ]
      rw [h1, nabs_uniformiser hϖ.irreducible (x := ϖ) rfl, inv_pow]
    have hvol : ∀ T, (volM m A P).real (S T) = ((resCard k : ℝ) ^ (n * Fintype.card A * P.card))⁻¹ := by
      intro T
      rw [Measure.real, hvolE, ENNReal.toReal_pow, ENNReal.coe_toReal]
      have : ((distribHaarChar k (ϖ ^ n) : NNReal) : ℝ) = nabs k (ϖ ^ n) := rfl
      rw [this, hnabs, inv_pow, ← pow_mul, mul_assoc]
    have hfin : ∀ T, (volM m A P) (S T) ≠ ⊤ := fun T => by
      rw [hvolE]; exact ENNReal.pow_ne_top ENNReal.coe_ne_top
    have hpt : ∀ U, F U = ∑ T, (S T).indicator (fun _ => F (liftRes T)) U := by
      intro U
      by_cases hU : ∀ i j, U i j ∈ 𝒪[k]
      · let T0 : A → P → Res k n := fun i j => Ideal.Quotient.mk _ ⟨U i j, hU i j⟩
        have key1 : ∀ T i j, U i j - liftRes T i j ∈ cball (ϖ ^ n) ↔ T i j = T0 i j := by
          intro T i j
          have e : T i j = T0 i j ↔ (⟨U i j, hU i j⟩ - Quotient.out (T i j) : 𝒪[k]) ∈
              IsLocalRing.maximalIdeal 𝒪[k] ^ n := by
            conv_lhs => rw [← Ideal.Quotient.mk_out (T i j)]
            rw [eq_comm]
            exact Ideal.Quotient.eq
          rw [e, mem_maxIdeal_pow_iff hϖ]
          rfl
        have key : ∀ T, U ∈ S T ↔ T = T0 := by
          intro T
          rw [hmemS]
          simp only [key1]
          exact ⟨fun h => funext fun i => funext fun j => h i j, fun h i j => by rw [h]⟩
        rw [Finset.sum_eq_single T0 (fun T _ hT => Set.indicator_of_notMem (fun h => hT ((key T).1 h)) _)
          (by simp), Set.indicator_of_mem ((key T0).2 rfl)]
        have hd := (hmemS T0 U).1 ((key T0).2 rfl)
        simp only [hF]
        rw [natDatum_setCols_eq hΦ P Y hd, psi_pairCols_eq hψ P hY hd]
      · push_neg at hU
        obtain ⟨i, j, hij⟩ := hU
        have hz : F U = 0 := by
          simp only [hF]
          rw [hΦ.1 _ ?_, zero_mul]
          intro hm'
          apply hij
          have := mem_matLat_stdLat.1 hm' i j
          simpa [setCols, j.2] using this
        rw [hz]
        symm
        refine Finset.sum_eq_zero fun T _ => Set.indicator_of_notMem (fun h => hij ?_) _
        have h1 : valuation k (U i j - liftRes T i j) ≤ valuation k ((ϖ ^ n : kˣ) : k) := (hmemS T U).1 h i j
        have h2 : U i j - liftRes T i j ∈ 𝒪[k] := by
          rw [Valuation.mem_integer_iff]
          refine le_trans h1 ?_
          rw [Units.val_pow_eq_pow_val, map_pow]
          exact pow_le_one' (hϖ.mem) n
        simpa using add_mem h2 (liftRes_mem T i j)
    rw [show F = fun U => ∑ T, (S T).indicator (fun _ => F (liftRes T)) U from funext hpt]
    rw [integral_finsetSum _ (fun T _ => (integrable_indicator_iff (hS T)).2
      (integrableOn_const (lt_top_iff_ne_top.2 (hfin T)).ne)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [integral_indicator_const _ (hS T), hvol, Complex.real_smul]
    push_cast
    rfl
  · rw [fourierInt_eq_pi]
    refine GlobalTheory.SplitWeil.FourierPi.fourier_eq_zero_pi _ hψ (s := ϖ ^ n) (fun t ht x => ?_) ?_
    · exact natDatum_setCols_eq hΦ P Y fun i j => by simpa using ht ⟨i, j⟩ trivial
    · intro hmem
      apply hY
      intro i j hj
      have h1 : valuation k (Y i j) ≤ valuation k ((((1 : kˣ) * (ϖ ^ n)⁻¹ : kˣ)) : k) := hmem ⟨i, ⟨j, hj⟩⟩ trivial
      rw [one_mul, Units.val_inv_eq_inv_val, map_inv₀] at h1
      rw [Valuation.mem_integer_iff, map_mul]
      calc valuation k ((ϖ ^ n : kˣ) : k) * valuation k (Y i j)
          ≤ valuation k ((ϖ ^ n : kˣ) : k) * (valuation k ((ϖ ^ n : kˣ) : k))⁻¹ := mul_le_mul' le_rfl h1
        _ = 1 := mul_inv_cancel₀ h0.ne'

end GlobalTheory.ColFourier
end
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

theorem _root_.GlobalTheory.T.fourier_transform_inversion_localFieldPi : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν), ∀ f ∈ SB (n → k), (fun y : n → k => ∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν)) ∈ SB (n → k) ∧ ∫ y : n → k, (∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν)) ∂(Measure.pi fun _ => ν) = f 0 := by
  first | exact @GlobalTheory.SplitWeil.FourierPi.fourier_pi | exact GlobalTheory.SplitWeil.FourierPi.fourier_pi | (intros; apply GlobalTheory.SplitWeil.FourierPi.fourier_pi <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.IrrSubquot

theorem exists_covBy_submodule {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [Nontrivial M] :
    ∃ S T : Submodule R M, T ⋖ S := by
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  haveI := CompleteLattice.Iic_coatomic_of_compact_element (Submodule.singleton_span_isCompactElement (R := R) m)
  rcases IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Set.Iic (Submodule.span R {m})) with h0 | ⟨c, hc, -⟩
  · have h1 : (⊥ : Submodule R M) = Submodule.span R {m} := congrArg Subtype.val h0
    exact absurd (Submodule.mem_span_singleton_self m) (by rw [← h1]; simpa using hm)
  · refine ⟨Submodule.span R {m}, c.1, lt_of_le_of_ne c.2 fun h => hc.1 (Subtype.ext h), ?_⟩
    intro x h1 h2
    have := congrArg Subtype.val (hc.2 ⟨x, h2.le⟩ h1)
    exact h2.ne this

theorem exists_irreducible_subquotient : ∀ (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V), Nontrivial V → ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y)
      (σ : Representation ℂ G Y), σ.IsIrreducible ∧ IsSubquotient σ ρ := by
  intro G _ V _ _ ρ hV
  haveI : Nontrivial ρ.asModule := hV
  obtain ⟨S, T, h⟩ := exists_covBy_submodule (R := MonoidAlgebra ℂ G) (M := ρ.asModule)
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)
  have h' : e.symm T ⋖ e.symm S :=
    ⟨e.symm.lt_iff_lt.2 h.1, fun c h1 h2 => h.2 (c := e c) (by simpa using e.lt_iff_lt.2 h1)
      (by simpa using e.lt_iff_lt.2 h2)⟩
  refine ⟨_, _, _, subQuot (e.symm S) (e.symm T), isIrreducible_subQuot h', e.symm S,
    ⟨Submodule.mkQ _, fun g => ?_⟩, Submodule.mkQ_surjective _⟩
  ext x
  rfl

end GlobalTheory.IrrSubquot
end

section

open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TensorFactorUnique

open GlobalTheory.SmGL

variable {β : Type} [Fintype β] [DecidableEq β] {X : β → Type} [∀ a, AddCommGroup (X a)]
  [∀ a, Module ℂ (X a)]

def contr (l : ∀ a, X a →ₗ[ℂ] ℂ) (j : β) : (PiTensorProduct ℂ X) →ₗ[ℂ] X j := GlobalTheory.MultilinearContraction.contract l j

theorem contr_tprod (l : ∀ a, X a →ₗ[ℂ] ℂ) (j : β) (x : ∀ a, X a) :
    contr l j (PiTensorProduct.tprod ℂ x) = (∏ i ∈ Finset.univ.erase j, l i (x i)) • x j :=
  GlobalTheory.MultilinearContraction.contract_tprod l j x

theorem exists_contr_ne_zero (j : β) {y : PiTensorProduct ℂ X} (hy : y ≠ 0) :
    ∃ l : ∀ a, X a →ₗ[ℂ] ℂ, contr l j y ≠ 0 := by
  let b := fun a => Module.Free.chooseBasis ℂ (X a)
  let B := Basis.piTensorProduct b
  obtain ⟨p, hp⟩ : ∃ p, B.repr y p ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hy (B.repr.map_eq_zero_iff.1 (Finsupp.ext hcon))
  refine ⟨fun a => (b a).coord (p a), fun h => hp ?_⟩
  have e : (b j).coord (p j) ∘ₗ contr (fun a => (b a).coord (p a)) j = B.coord p := by
    ext w
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, contr_tprod, map_smul,
      Module.Basis.coord_apply, B, Basis.piTensorProduct_repr_tprod_apply, smul_eq_mul]
    exact Finset.prod_erase_mul _ _ (Finset.mem_univ j)
  have := LinearMap.congr_fun e y
  rw [LinearMap.comp_apply, h, map_zero] at this
  exact this.symm

variable {Γ : β → Type} [∀ a, Group (Γ a)]

theorem contr_mulSingle (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (l : ∀ a, X a →ₗ[ℂ] ℂ) (j : β)
    (g : Γ j) (y : PiTensorProduct ℂ X) :
    contr l j (piTensor ρ (Pi.mulSingle j g) y) = ρ j g (contr l j y) := by
  induction y using PiTensorProduct.induction_on with
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | smul_tprod c x =>
    simp only [map_smul, piTensor_tprod, contr_tprod, Pi.mulSingle_eq_same]
    congr 2
    exact Finset.prod_congr rfl fun a ha => by
      rw [Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase ha), map_one, Module.End.one_apply]


omit [Fintype β] in
theorem tprod_update_mulSingle (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (x : ∀ a, X a) (j : β)
    (g : Γ j) (v : X j) :
    PiTensorProduct.tprod ℂ (Function.update x j (ρ j g v)) =
      piTensor ρ (Pi.mulSingle j g) (PiTensorProduct.tprod ℂ (Function.update x j v)) := by
  rw [piTensor_tprod]
  congr 1
  funext a
  by_cases h : a = j
  · subst h; simp
  · simp [h, Pi.mulSingle_eq_of_ne h]

theorem cl_eq_of_piTensor_equiv : ∀ (β : Type) [Fintype β] (Γ : β → Type) [∀ j, Group (Γ j)] [∀ j, TopologicalSpace (Γ j)] (s s' : ∀ j, GlobalTheory.SmGL.IrrRep (Γ j)), Nonempty ((GlobalTheory.SmGL.piTensor fun j => (s j).ρ).Equiv (GlobalTheory.SmGL.piTensor fun j => (s' j).ρ)) → ∀ j, (s j).cl = (s' j).cl := by
  intro β _ Γ _ _ s s' ⟨φ⟩ j
  classical
  haveI := fun a => nontrivial_of_irreducible (s a).irr
  let b := fun a => Module.Free.chooseBasis ℂ (s a).V
  let p : ∀ a, Module.Free.ChooseBasisIndex ℂ (s a).V := fun a => (b a).index_nonempty.some
  let x : ∀ a, (s a).V := fun a => b a (p a)
  have hx : PiTensorProduct.tprod ℂ x ≠ 0 := by
    have := (Basis.piTensorProduct b).ne_zero p
    rwa [Basis.piTensorProduct_apply] at this
  have hy : φ (PiTensorProduct.tprod ℂ x) ≠ 0 := fun h => hx ((map_eq_zero_iff φ φ.injective).1 h)
  obtain ⟨l, hl⟩ := exists_contr_ne_zero j hy
  let ψ : (s j).ρ.IntertwiningMap (s' j).ρ :=
    { toLinearMap := contr l j ∘ₗ φ.toLinearMap ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap x j
      isIntertwining' := fun g => by
        ext v
        simp only [LinearMap.comp_apply, MultilinearMap.toLinearMap_apply]
        rw [tprod_update_mulSingle (fun a => (s a).ρ), ← contr_mulSingle (fun a => (s' a).ρ)]
        congr 1
        exact LinearMap.congr_fun (φ.isIntertwining' (Pi.mulSingle j g)) _ }
  have hψ : ψ ≠ 0 := fun h => hl (by
    have : ψ (x j) = 0 := by rw [h]; rfl
    rw [← this]
    show _ = contr l j (φ (PiTensorProduct.tprod ℂ (Function.update x j (x j))))
    rw [Function.update_eq_self])
  haveI := (s j).irr
  haveI := (s' j).irr
  have hb := (Representation.IsIrreducible.bijective_or_eq_zero ψ).resolve_right hψ
  exact IrrRep.cl_eq_iff.2 ⟨ψ.ofBijective hb⟩

end GlobalTheory.TensorFactorUnique
end
end

section

open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace Real ComplexOrder

theorem _root_.GlobalTheory.T.vacuumProjector_range_annihilated : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (J : V ≃ₗᵢ[ℝ] V) (ρ : V → B →L[ℂ] B), (∀ x, J (J x) = -x) → ∀ (h : IsHeis (omJ J) ρ) (x : B) (z : V), dH ρ z (proj h x) + I • dH ρ (J z) (proj h x) = 0 := by
  first | exact @GlobalTheory.Mem.Lift.VacAnn.proj_annihilated | exact GlobalTheory.Mem.Lift.VacAnn.proj_annihilated | (intros; apply GlobalTheory.Mem.Lift.VacAnn.proj_annihilated <;> assumption)
end

section

open GlobalTheory.RealWeil MeasureTheory
open scoped SchwartzMap

theorem _root_.GlobalTheory.T.eq_zero_of_orthogonal_schrodinger_gaussian : ∀ (l : Type) [Fintype l] (k : Sch l), (∀ w : l ⊕ l → ℝ, inner ℂ ((rhoSch w (GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l))).toLp 2 volume) (k.toLp 2 volume) = 0) → k = 0 := by
  first | exact @GlobalTheory.RealWeil.eq_zero_of_inner_rhoSch_gaussian | exact GlobalTheory.RealWeil.eq_zero_of_inner_rhoSch_gaussian | (intros; apply GlobalTheory.RealWeil.eq_zero_of_inner_rhoSch_gaussian <;> assumption)
end

section

open GlobalTheory.RealWeil MeasureTheory
open scoped SchwartzMap Matrix

theorem _root_.GlobalTheory.T.symplectic_and_flow_of_intertwining_unitary : ∀ (l : Type) [Fintype l] (A : ℝ → (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ)) (T : ℝ → Sch l →ₗ[ℂ] Sch l), (∀ s t f, T (s + t) f = T s (T t f)) → (∀ f, T 0 f = f) → (∀ t w (f f₁ : Sch l), ⇑f₁ = rhoFun w ⇑f → ⇑(T t f₁) = rhoFun (A t w) ⇑(T t f)) → (∀ t f, ∫ x, ‖T t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) → (∀ t w w', sympl (A t w) (A t w') = sympl w w') ∧ (∀ s t w, A (s + t) w = A s (A t w)) ∧ ∀ w, A 0 w = w := by
  first | exact @GlobalTheory.RealWeil.intertwining_symplectic_and_group_law | exact GlobalTheory.RealWeil.intertwining_symplectic_and_group_law | (intros; apply GlobalTheory.RealWeil.intertwining_symplectic_and_group_law <;> assumption)
end

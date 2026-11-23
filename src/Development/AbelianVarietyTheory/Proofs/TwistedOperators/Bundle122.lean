module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Formalism.DoubleCosetMeasures.StatementZ
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasurableSetPreSingleton
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.NotTrivialAndTwist
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle096
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle002
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
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VolumeFlatSection
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle073
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle120

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

noncomputable section
namespace GlobalTheory.BlockVolume

variable {k : Type} [MeasurableSpace k] (ν : Measure k) [SigmaFinite ν]

def rowSplit (A D : Type) [Fintype A] [Fintype D] :
    ((A ⊕ D) → k) ≃ᵐ ((A → k) × (D → k)) :=
  MeasurableEquiv.sumPiEquivProdPi (fun _ : A ⊕ D => k)

theorem rowSplit_mp (A D : Type) [Fintype A] [Fintype D] :
    MeasurePreserving (rowSplit (k := k) A D) (Measure.pi fun _ : A ⊕ D => ν)
      ((Measure.pi fun _ : A => ν).prod (Measure.pi fun _ : D => ν)) :=
  measurePreserving_sumPiEquivProdPi (fun _ : A ⊕ D => ν)

def colSplit (R A D : Type) [Fintype R] [Fintype A] [Fintype D] :
    (R → (A ⊕ D) → k) ≃ᵐ ((R → A → k) × (R → D → k)) :=
  (MeasurableEquiv.piCongrRight fun _ : R => rowSplit (k := k) A D).trans
    (MeasurableEquiv.arrowProdEquivProdArrow (A → k) (D → k) R)

theorem colSplit_mp (R A D : Type) [Fintype R] [Fintype A] [Fintype D] :
    MeasurePreserving (colSplit (k := k) R A D)
      (Measure.pi fun _ : R => Measure.pi fun _ : A ⊕ D => ν)
      ((Measure.pi fun _ : R => Measure.pi fun _ : A => ν).prod
        (Measure.pi fun _ : R => Measure.pi fun _ : D => ν)) := by
  have h1 := measurePreserving_pi (fun _ : R => Measure.pi fun _ : A ⊕ D => ν)
    (fun _ : R => (Measure.pi fun _ : A => ν).prod (Measure.pi fun _ : D => ν))
    (fun _ => rowSplit_mp ν A D)
  have h2 := measurePreserving_arrowProdEquivProdArrow (A → k) (D → k) R
    (fun _ => Measure.pi fun _ : A => ν) (fun _ => Measure.pi fun _ : D => ν)
  exact h2.comp h1

def blockSplit (A D : Type) [Fintype A] [Fintype D] :
    ((A ⊕ D) → (A ⊕ D) → k) ≃ᵐ (((A → A → k) × (A → D → k)) × ((D → A → k) × (D → D → k))) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : A ⊕ D => (A ⊕ D) → k)).trans
    (MeasurableEquiv.prodCongr (colSplit A A D) (colSplit D A D))

def blockEquiv (A D : Type) [Fintype A] [Fintype D] :
    Matrix (A ⊕ D) (A ⊕ D) k ≃ᵐ ((Matrix A A k × Matrix A D k) × (Matrix D A k × Matrix D D k)) :=
  blockSplit (k := k) A D

theorem blockSplit_mp (A D : Type) [Fintype A] [Fintype D] :
    MeasurePreserving (blockEquiv (k := k) A D) (volM ν (A ⊕ D) (A ⊕ D))
      (((volM ν A A).prod (volM ν A D)).prod ((volM ν D A).prod (volM ν D D))) := by
  have h1 := measurePreserving_sumPiEquivProdPi (fun _ : A ⊕ D => Measure.pi fun _ : A ⊕ D => ν)
  have h2 := (colSplit_mp ν A A D).prod (colSplit_mp ν D A D)
  exact h2.comp h1

end GlobalTheory.BlockVolume

theorem GlobalTheory.blockVolume_prod : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]
    (A D : Type) [Fintype A] [Fintype D] (S₁₁ : Set (Matrix A A k)) (S₁₂ : Set (Matrix A D k))
    (S₂₁ : Set (Matrix D A k)) (S₂₂ : Set (Matrix D D k)),
    volM ν (A ⊕ D) (A ⊕ D)
        {x | x.toBlocks₁₁ ∈ S₁₁ ∧ x.toBlocks₁₂ ∈ S₁₂ ∧ x.toBlocks₂₁ ∈ S₂₁ ∧ x.toBlocks₂₂ ∈ S₂₂} =
      volM ν A A S₁₁ * volM ν A D S₁₂ * volM ν D A S₂₁ * volM ν D D S₂₂ := by
  intro k _ _ _ _ _ _ ν _ A D _ _ S₁₁ S₁₂ S₂₁ S₂₂
  haveI := GlobalTheory.IndexVolume.secondCountable k
  haveI : SigmaFinite ν := inferInstance
  haveI hσ : ∀ (m n : Type) [Fintype m] [Fintype n], SigmaFinite (volM ν m n) := fun m n _ _ => by
    exact (inferInstance : SigmaFinite (Measure.pi fun _ : m => Measure.pi fun _ : n => ν :
      Measure (m → n → k)))
  haveI := hσ A A; haveI := hσ A D; haveI := hσ D A; haveI := hσ D D
  have hmp := GlobalTheory.BlockVolume.blockSplit_mp ν A D
  have hset : {x : Matrix (A ⊕ D) (A ⊕ D) k | x.toBlocks₁₁ ∈ S₁₁ ∧ x.toBlocks₁₂ ∈ S₁₂ ∧
      x.toBlocks₂₁ ∈ S₂₁ ∧ x.toBlocks₂₂ ∈ S₂₂} =
      GlobalTheory.BlockVolume.blockEquiv (k := k) A D ⁻¹' ((S₁₁ ×ˢ S₁₂) ×ˢ (S₂₁ ×ˢ S₂₂)) := by
    ext x
    exact ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨⟨h1, h2⟩, h3, h4⟩, fun ⟨⟨h1, h2⟩, h3, h4⟩ => ⟨h1, h2, h3, h4⟩⟩
  rw [hset]
  have h := hmp.measure_preimage_equiv ((S₁₁ ×ˢ S₁₂) ×ˢ (S₂₁ ×ˢ S₂₂))
  refine h.trans ?_
  rw [Measure.prod_prod, Measure.prod_prod, Measure.prod_prod]
  ring
end
end

section

noncomputable section

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.SmGL.UnramFixed

theorem occursTimes_of_twist {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ τ : Representation ℂ G V} {δ θ η : G →* ℂˣ} (h : ∀ g v, τ g v = (δ g : ℂ) • ρ g v)
    (hη : ∀ g, η g = θ g * δ g) {r : ℕ} (hr : OccursTimes (ofChar θ) ρ r) :
    OccursTimes (ofChar η) τ r := by
  obtain ⟨S, T, h1, h2, h3⟩ := hr
  have hst : ∀ (P : Subrepresentation ρ) (g : G) (v : V), v ∈ P.toSubmodule → τ g v ∈ P.toSubmodule :=
    fun P g v hv => by
      rw [h]
      exact P.toSubmodule.smul_mem _ (P.apply_mem_toSubmodule g hv)
  refine ⟨fun i => ⟨(S i).toSubmodule, hst (S i)⟩, fun i => ⟨(T i).toSubmodule, hst (T i)⟩,
    fun i => h1 i, fun i j hij => h2 i j hij, fun i => ?_⟩
  obtain ⟨f, hsurj, hint, hker⟩ := step_iff.1 (h3 i)
  refine step_iff.2 ⟨f, hsurj, fun g v hv => ?_, hker⟩
  have e := hint g v hv
  rw [ofChar_apply] at e
  show f (τ g v) = ofChar η g (f v)
  rw [h, map_smul, e, ofChar_apply, hη, Units.val_mul, smul_eq_mul]
  ring

theorem jhMult_of_twist {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ τ : Representation ℂ G V} {δ : G →* ℂˣ} (θ : G →* ℂˣ)
    (h : ∀ g v, τ g v = (((δ g)⁻¹ : ℂˣ) : ℂ) • ρ g v) :
    jhMult (ofChar θ) τ = jhMult (ofChar (θ * δ)) ρ := by
  have key : ∀ r, OccursTimes (ofChar θ) τ r ↔ OccursTimes (ofChar (θ * δ)) ρ r := fun r =>
    ⟨occursTimes_of_twist (δ := δ)
        (fun g v => by rw [h, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul])
        (fun g => MonoidHom.mul_apply θ δ g),
      occursTimes_of_twist (δ := δ⁻¹) (fun g v => by rw [MonoidHom.inv_apply]; exact h g v)
        (fun g => by rw [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_cancel_right])⟩
  simp only [jhMult, key]

private lemma pres_iterate_zero {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) {H : Subgroup G}
    (hH : IsCompact (H : Set G)) {θ : G →* ℂˣ} (hθ : ∀ t ∈ H, θ t = 1) (S : Subrepresentation ρ)
    (f : V →ₗ[ℂ] ℂ) (hf : ∀ g, ∀ v ∈ S.toSubmodule, f (ρ g v) = ofChar θ g (f v)) (v : V)
    (hv : v ∈ S.toSubmodule) : ∃ u ∈ fixed ρ H, u ∈ S.toSubmodule ∧ f u = f v := by

  obtain ⟨U, -, hU, hUv⟩ := GlobalTheory.LocGL.exists_normal_fix hρ hH v
  haveI : U.FiniteIndex := hU
  letI : Fintype (H ⧸ U) := Subgroup.fintypeQuotientOfFiniteIndex
  refine ⟨GlobalTheory.LocGL.idem hρ hH v, GlobalTheory.LocGL.idem_mem hρ hH v, ?_, ?_⟩
  · rw [GlobalTheory.LocGL.idem_eq_cosetSum hρ hH U hUv]
    exact S.toSubmodule.smul_mem _ (S.toSubmodule.sum_mem fun q _ => S.apply_mem_toSubmodule _ hv)

  · rw [GlobalTheory.LocGL.idem_eq_cosetSum hρ hH U hUv, map_smul, map_sum]
    have hq : ∀ q : H ⧸ U, f (ρ (q.out : H) v) = f v := fun q => by
      rw [hf _ v hv, ofChar_apply, hθ _ (q.out).2, Units.val_one, one_mul]
    have hc : (Fintype.card (H ⧸ U) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    simp only [hq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, smul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

theorem jhMult_onFixed {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) {H : Subgroup G}
    (hH : IsCompact (H : Set G)) (hn : ∀ g, MonoidHom.id G g ∈ Subgroup.normalizer (H : Set G))
    {θ : G →* ℂˣ} (hθ : ∀ t ∈ H, θ t = 1) :
    jhMult (ofChar θ) ρ = jhMult (ofChar θ) (onFixed ρ H (MonoidHom.id G) hn) := by
  let ι : (onFixed ρ H (MonoidHom.id G) hn).IntertwiningMap ρ :=
    { toLinearMap := (fixed ρ H).subtype
      isIntertwining' := fun g => by ext v; rfl }
  have hι : Function.Injective ι := Subtype.val_injective
  have key : ∀ r, OccursTimes (ofChar θ) ρ r ↔
      OccursTimes (ofChar θ) (onFixed ρ H (MonoidHom.id G) hn) r := by
    intro r
    constructor
    · rintro ⟨S, T, h1, h2, h3⟩
      refine ⟨fun i => subComap ι (S i), fun i => subComap ι (T i), fun i => subComap_mono ι (h1 i),
        fun i j hij => subComap_mono ι (h2 i j hij), fun i => ?_⟩
      obtain ⟨f, hsurj, hint, hker⟩ := step_iff.1 (h3 i)
      refine step_iff.2 ⟨f ∘ₗ (fixed ρ H).subtype, fun w => ?_, fun g u hu => hint g u.1 hu,
        fun u hu => hker u.1 hu⟩
      obtain ⟨v, hv, rfl⟩ := hsurj w
      obtain ⟨u, huF, huS, hfu⟩ := pres_iterate_zero hρ hH hθ (S i) f hint v hv
      exact ⟨⟨u, huF⟩, huS, hfu⟩
    · rintro ⟨S, T, h1, h2, h3⟩
      exact ⟨fun i => subMap ι (S i), fun i => subMap ι (T i), fun i => subMap_mono ι (h1 i),
        fun i j hij => subMap_mono ι (h2 i j hij),
        fun i => step_iff.2 (step_map ι hι (step_iff.1 (h3 i)))⟩
  simp only [jhMult, key]

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isCompact_unitsO : IsCompact {x : kˣ | valuation k (x : k) = 1} := by
  haveI : T1Space k := IsTopologicalAddGroup.t1Space k (by
    first
      | exact isClosed_singleton
      | (convert (Valuation.isClosed_sphere (v := valuation k) 0) using 1
         ext x
         simp))
  have hS : IsCompact (((valuation k).integer.toSubmonoid : Submonoid k) : Set k) :=
    IsNonarchimedeanLocalField.isCompact_closedBall k 1
  convert Submonoid.units_isCompact hS using 1
  ext x
  have h0 : valuation k (x : k) ≠ 0 := by simp
  simp only [Set.mem_setOf_eq, SetLike.mem_coe, Submonoid.mem_units_iff, Subring.mem_toSubmonoid,
    Valuation.mem_integer_iff, Units.val_inv_eq_inv_val, map_inv₀]
  constructor
  · intro hx
    simp [hx]
  · rintro ⟨h1, h2⟩
    rw [inv_le_one₀ (zero_lt_iff.2 h0)] at h2
    exact le_antisymm h1 h2

theorem isCompact_torusO (n : Type) : IsCompact (torusO k n : Set (n → kˣ)) :=
  isCompact_pi_infinite fun _ => isCompact_unitsO k

theorem deltaHalf_torusO {n : Type} [Fintype n] [LinearOrder n] {t : n → kˣ} (ht : t ∈ torusO k n) :
    deltaHalf k (fun _ : n => Unit) (leviTorus k n t) = 1 := by
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => ?_
  have hdet : Matrix.GeneralLinearGroup.det (leviTorus k n t a) = t a :=
    congrFun ((leviTorus k n).symm_apply_apply t) a
  have hv : valuation k (t a : k) = 1 := (show ∀ i, valuation k (t i : k) = 1 from ht) a
  apply Units.ext
  rw [hdet, val_absPow, nabs_eq_one k hv, Units.val_one]
  simp

variable {k} {n V : Type} [Fintype n] [DecidableEq n] [LinearOrder n] [AddCommGroup V] [Module ℂ V]

theorem jacB_apply (π : Representation ℂ (GL n k) V) (g : n → kˣ) (v : Jacquet π (unipB k n)) :
    jacB π g v = (((((deltaHalf k fun _ : n => Unit).comp
      (leviTorus k n).toMonoidHom) g)⁻¹ : ℂˣ) : ℂ) • jacBU π g v := by
  first
    | exact twist_apply (jacU (points n) π) (deltaHalf k fun _ : n => Unit)⁻¹ (leviTorus k n g) v
    | (show twist (jacU (points n) π) (deltaHalf k fun _ : n => Unit)⁻¹ (leviTorus k n g) v = _
       rw [twist_apply]
       rfl)

theorem jhMult_jacBU_eq_expMult {π : Representation ℂ (GL n k) V} (hπ : IsSmooth π)
    {θ : (n → kˣ) →* ℂˣ} (hθ : ∀ t ∈ torusO k n, θ t = 1) :
    jhMult (ofChar θ) (jacBU π) = expMult π θ := by
  unfold expMult jacBUFixed
  exact jhMult_onFixed (isSmooth_jacBU hπ) (isCompact_torusO k n) _ hθ

theorem jhMult_jacB_eq_expMult : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → ∀ θ : (Fin n → kˣ) →* ℂˣ, (∀ t ∈ torusO k (Fin n), θ t = 1) → jhMult (ofChar θ) (jacB π) = expMult π (θ * (deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom) := by
  intro k _ _ _ _ n V _ _ π hπ θ hθ
  rw [jhMult_of_twist θ (fun g v => jacB_apply π g v)]
  refine jhMult_jacBU_eq_expMult hπ fun t ht => ?_
  rw [MonoidHom.mul_apply, hθ t ht, one_mul]
  exact deltaHalf_torusO k ht

end GlobalTheory.SmGL.UnramFixed
end
end

section

noncomputable section

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel

namespace GlobalTheory.SmGL.RankOneProduct

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α : Type} [Fintype α] [LinearOrder α] {c : α → Type} [∀ i, Fintype (c i)] [∀ i, DecidableEq (c i)]


omit [Fintype α] [LinearOrder α] [∀ i, Fintype (c i)] [∀ i, DecidableEq (c i)] in
theorem isEmpty_of_ne (g : (Σ i, c i) ≃ Unit) {a : α} (ha : a ≠ (g.symm ()).1) : IsEmpty (c a) :=
  ⟨fun x => ha (congrArg Sigma.fst (g.injective (Subsingleton.elim (g ⟨a, x⟩) (g (g.symm ())))))⟩


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype α] [LinearOrder α] in
theorem det_eq_one_of_ne (g : (Σ i, c i) ≃ Unit) {a : α} (ha : a ≠ (g.symm ()).1) (x : GL (c a) k) :
    Matrix.GeneralLinearGroup.det x = 1 := by
  have := isEmpty_of_ne g ha
  ext
  simp


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype α]
  [∀ i, Fintype (c i)] [∀ i, DecidableEq (c i)] in
theorem mem_parab_unit (g : (Σ i, c i) ≃ Unit) (x : GL Unit k) : x ∈ parab k g :=
  by
    change Matrix.BlockTriangular (x : Matrix Unit Unit k) (blk g)
    intro i j h
    cases i
    cases j
    exact absurd h (lt_irrefl _)

theorem deltaHalf_eq_one (g : (Σ i, c i) ≃ Unit) (x : Levi k c) : deltaHalf k c x = 1 := by
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => ?_
  by_cases ha : a = (g.symm ()).1
  · have h : modExp c a = 0 := by
      unfold modExp
      rw [Finset.sum_eq_zero, Finset.sum_eq_zero, sub_zero]
      · intro b hb
        have := isEmpty_of_ne g (a := b) (ha ▸ (Finset.mem_filter.1 hb).2.ne)
        simp
      · intro b hb
        have := isEmpty_of_ne g (a := b) (ha ▸ (Finset.mem_filter.1 hb).2.ne')
        simp
    simp [h]
  · rw [det_eq_one_of_ne g ha, map_one]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem piTensor_leviProj (g : (Σ i, c i) ≃ Unit) (ψ : α → kˣ →* ℂˣ) (p : parab k g)
    (w : PiTensorProduct ℂ fun _ : α => ℂ) :
    piTensor (fun i => detRep (c i) (ψ i)) (leviProj k g p) w =
      (detChar Unit (ψ (g.symm ()).1) (p : GL Unit k) : ℂ) • w := by
  have hd : (∏ a, (detChar (c a) (ψ a) (leviProj k g p a) : ℂ)) =
      (detChar Unit (ψ (g.symm ()).1) (p : GL Unit k) : ℂ) := by
    rw [Finset.prod_eq_single (g.symm ()).1, detChar_apply, detChar_apply, det_parab,
      Finset.prod_eq_single (g.symm ()).1]
    · intro b _ hb
      exact det_eq_one_of_ne g hb _
    · simp
    · intro b _ hb
      rw [detChar_apply, det_eq_one_of_ne g hb, map_one, Units.val_one]
    · simp
  induction w using PiTensorProduct.induction_on with
  | add x y hx hy => rw [map_add (f := _), hx, hy, smul_add]
  | smul_tprod r x =>
    rw [map_smul, piTensor_tprod, ← hd, smul_comm]
    congr 1
    calc
      _ = (PiTensorProduct.tprod ℂ) (fun a => (detChar (c a) (ψ a) (leviProj k g p a) : ℂ) • x a) := by rfl
      _ = _ := MultilinearMap.map_smul_univ _ _ _

theorem nonempty_equiv_multiProd_unit (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (α : Type) [Fintype α] [LinearOrder α] (c : α → Type)
    [∀ i, Fintype (c i)] [∀ i, DecidableEq (c i)] (g : (Σ i, c i) ≃ Unit) (ψ : α → kˣ →* ℂˣ)
    (hψ : ∀ i, IsSmoothChar (ψ i)) :
    Nonempty ((multiProd g fun i => detRep (c i) (ψ i)).Equiv (detRep Unit (ψ (g.symm ()).1))) := by
  let L : (PiTensorProduct ℂ fun _ : α => ℂ) ≃ₗ[ℂ] ℂ :=
    (PiTensorProduct.constantBaseRingEquiv α ℂ).toLinearEquiv
  have law : ∀ (φ : IndSp g (piTensor fun i => detRep (c i) (ψ i))) (x : GL Unit k),
      φ.1.1 x = (detChar Unit (ψ (g.symm ()).1) x : ℂ) • φ.1.1 1 := fun φ x => by
    have := parInd_law g _ φ ⟨x, mem_parab_unit g x⟩ 1
    rw [deltaHalf_eq_one g, piTensor_leviProj, mul_one, Units.val_one, one_smul] at this
    exact this
  let f : IndSp g (piTensor fun i => detRep (c i) (ψ i)) →ₗ[ℂ] ℂ :=
    { toFun := fun φ => L (φ.1.1 1)
      map_add' := fun φ φ' => map_add L _ _
      map_smul' := fun r φ => map_smul L r _ }
  refine ⟨LocGL.equivOfBijective ⟨f, fun x => LinearMap.ext fun φ => ?_⟩ ⟨fun φ φ' h => ?_, fun z => ?_⟩⟩
  · show L (φ.1.1 (1 * x)) = detRep Unit (ψ (g.symm ()).1) x (L (φ.1.1 1))
    rw [one_mul, law, map_smul]
    exact (ofChar_apply _ _ _).symm
  · have h1 : φ.1.1 1 = φ'.1.1 1 := L.injective h
    refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    rw [law φ x, law φ' x, h1]
  · refine ⟨⟨⟨fun x => (detChar Unit (ψ (g.symm ()).1) x : ℂ) • L.symm z, fun p x => ?_⟩,
      mem_smoothPart_of_nhds (Filter.mem_of_superset
        (IsOpen.mem_nhds ((hψ (g.symm ()).1).detChar (n := Unit)) (one_mem _)) fun y hy => ?_)⟩, ?_⟩
    · show (detChar Unit (ψ (g.symm ()).1) (p * x) : ℂ) • L.symm z =
        (deltaHalf k c (leviProj k g p) : ℂ) • piTensor (fun i => detRep (c i) (ψ i)) (leviProj k g p)
          ((detChar Unit (ψ (g.symm ()).1) x : ℂ) • L.symm z)
      rw [deltaHalf_eq_one g, piTensor_leviProj, Units.val_one, one_smul, map_mul, Units.val_mul,
        mul_smul]
    · have hy' : detChar Unit (ψ (g.symm ()).1) y = 1 := hy
      apply Subtype.ext
      funext x
      show (detChar Unit (ψ (g.symm ()).1) (x * y) : ℂ) • L.symm z =
        (detChar Unit (ψ (g.symm ()).1) x : ℂ) • L.symm z
      rw [map_mul, hy', mul_one]
    · show L ((detChar Unit (ψ (g.symm ()).1) 1 : ℂ) • L.symm z) = z
      rw [map_one, Units.val_one, one_smul, L.apply_symm_apply]

end GlobalTheory.SmGL.RankOneProduct
end
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory.PolarU

theorem isClosed_Kset {p q : ℕ} (T : GrpData p q) : IsClosed T.Kset := by
  have h : T.Kset = ⋂ a, ⋂ b, ⋂ (_ : ¬ sameBlock a b), {x : T.G | matG T x a b = 0} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    exact Iff.rfl
  rw [h]
  refine isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun _ => ?_
  exact isClosed_eq ((continuous_matG T).matrix_elem a b) continuous_const

theorem isCompact_Kset : ∀ (p q : ℕ) (T : GrpData p q), IsCompact T.Kset := by
  intro p q T
  have hS : IsCompact ((Units.val : ℂˣ → ℂ) ⁻¹' Metric.sphere 0 1) := by
    refine (Units.isEmbedding_val₀.isInducing.isCompact_preimage_iff ?_).2 (isCompact_sphere 0 1)
    intro z hz
    have : z ≠ 0 := by rintro rfl; simp at hz
    exact ⟨Units.mk0 z this, rfl⟩
  have hc := Formalism.UG.P.isCompact_units_of_unitary (n := Ix p q) (T := {M | star M * M = 1})
    (isClosed_eq (continuous_star.matrix_mul continuous_id) continuous_const) (fun M hM => hM)
  refine ((GlobalTheory.RealPar.SqInt.isClosedEmbedding_emb T).isCompact_preimage (hc.prod hS)).of_isClosed_subset
    (isClosed_Kset T) fun x hx => ⟨matG_star_mul T hx, ?_⟩
  simpa using GlobalTheory.RealPar.Cover.norm_sq x

end GlobalTheory.PolarU
end

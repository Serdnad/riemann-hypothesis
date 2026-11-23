module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1971
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle266
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIteratedFDerivRemCompLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzVanishingDecomposition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1477
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1994
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1967
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1902
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmittedDiagonalIntegralLinearForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergLatticeSelfDualEveryFinitePlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalGaussSumIntegerDvdResidueCardPow
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1193
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1349
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1197
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1196

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

namespace GlobalTheory.CharInvForm

theorem exists_schwartz_one (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    ∃ f₀ : SchwartzMap V ℂ, f₀ 0 = 1 := by
  obtain ⟨f, -, hc, hs, -, h1⟩ :=
    exists_contDiff_tsupport_subset (x := (0 : V)) (s := Set.univ) (n := ⊤) Filter.univ_mem
  have hc' : HasCompactSupport (fun x => (f x : ℂ)) := hc.comp_left Complex.ofReal_zero
  have hs' : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (f x : ℂ)) := Complex.ofRealCLM.contDiff.comp hs
  exact ⟨hc'.toSchwartzMap hs', by simp [h1]⟩

theorem arch (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (T : SchwartzMap V ℂ →L[ℂ] ℂ)
    (hT : ∀ (L : V →L[ℝ] ℝ) (f f' : SchwartzMap V ℂ),
      (∀ x, f' x = Complex.exp (Complex.I * (L x : ℂ)) * f x) → T f' = T f) :
    ∃ a : ℂ, ∀ f : SchwartzMap V ℂ, T f = a * f 0 := by
  obtain ⟨f₀, hf₀⟩ := exists_schwartz_one V
  refine ⟨T f₀, fun f => ?_⟩
  have h0 : (f - f 0 • f₀) 0 = 0 := by simp [hf₀]
  obtain ⟨n, L, h, g, hg, hsum⟩ := GlobalTheory.SchwartzDiv.hadamard V _ h0
  have e : f - f 0 • f₀ = ∑ i, g i := by
    ext x
    rw [hsum x, SchwartzMap.sum_apply]
  have : T (f - f 0 • f₀) = 0 := by

    rw [e, map_sum]
    exact Finset.sum_eq_zero fun i _ => GlobalTheory.CharFormDeriv.charForm_kills_linear_mul V T hT (L i) (h i) (g i) (hg i)
  rw [map_sub, map_smul, sub_eq_zero] at this
  rw [this, smul_eq_mul, mul_comm]

end GlobalTheory.CharInvForm

namespace GlobalTheory.CharInvForm

open scoped Classical

variable {F : Type} [Field F] [NumberField F]

theorem pairA_zero_add (a b : Af F) : pairA F 0 (a + b) = pairA F 0 a + pairA F 0 b :=
  Prod.ext (zero_add (0 : Ainf F)).symm rfl

theorem dot_pairA_fin {κ : Type} [Fintype κ] (x : κ → AF F) (y : κ → Af F) :
    (x ⬝ᵥ fun i => pairA F 0 (y i)) = pairA F 0 ((fun i => (x i).2) ⬝ᵥ y) := by
  have h1 : (RingHom.fst (Ainf F) (Af F)) (x ⬝ᵥ fun i => pairA F 0 (y i)) = 0 := by

    simp only [dotProduct, map_sum, map_mul]
    exact Finset.sum_eq_zero fun i _ => by
      show (RingHom.fst (Ainf F) (Af F)) (x i) * 0 = 0
      exact mul_zero _
  have h2 : (RingHom.snd (Ainf F) (Af F)) (x ⬝ᵥ fun i => pairA F 0 (y i)) = (fun i => (x i).2) ⬝ᵥ y := by

    simp only [dotProduct, map_sum, map_mul]
    rfl
  exact Prod.ext h1 h2

theorem dot_pairA_inf {κ : Type} [Fintype κ] (x : κ → AF F) (y : κ → Ainf F) :
    (x ⬝ᵥ fun i => pairA F (y i) 0) = pairA F (∑ i, (x i).1 * y i) 0 := by
  have h1 : (RingHom.fst (Ainf F) (Af F)) (x ⬝ᵥ fun i => pairA F (y i) 0) = ∑ i, (x i).1 * y i := by

    simp only [dotProduct, map_sum, map_mul]
    rfl
  have h2 : (RingHom.snd (Ainf F) (Af F)) (x ⬝ᵥ fun i => pairA F (y i) 0) = 0 := by

    simp only [dotProduct, map_sum, map_mul]
    exact Finset.sum_eq_zero fun i _ => by
      show (RingHom.snd (Ainf F) (Af F)) (x i) * 0 = 0
      exact mul_zero _
  exact Prod.ext h1 h2

theorem mem_schA {κ : Type} [Fintype κ] (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) : pureA F f g ∈ schA F κ :=
  Submodule.subset_span ⟨f, g, hg, rfl⟩

theorem pureA_zero {κ : Type} (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → Af F) → ℂ) :
    pureA F f g 0 = f 0 * g 0 := by
  simp only [pureA]
  congr 2
  · funext i
    exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)

end GlobalTheory.CharInvForm

namespace GlobalTheory.CharInvForm

open scoped Classical

theorem psi_dot_inf {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {κ : Type} [Fintype κ]
    (x : κ → AF F) (Y : κ → mixedEmbedding.mixedSpace F) :
    ψ (x ⬝ᵥ fun i => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (Y i)) 0) =
      Complex.exp (Complex.I * ((-(2 * Real.pi) * ∑ i, Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
        ((fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) i * Y i) : ℝ) : ℂ)) := by
  have hat : At (evI F) (pairA F (∑ i, (x i).1 * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (Y i)) 0) := by
    intro u hu
    have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
    show (u.1 * _, u.2 * 0) = ((0 : Ainf F), (0 : Af F))
    rw [h1, zero_mul, mul_zero]
  rw [dot_pairA_inf, hψ.2.2 _ hat]
  show Complex.exp (_ * ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
    (InfiniteAdeleRing.ringEquiv_mixedSpace F (∑ i, (x i).1 * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (Y i))) : ℝ) : ℂ)) = _

  rw [map_sum, map_sum]
  simp only [map_mul, RingEquiv.apply_symm_apply]
  congr 1
  push_cast
  ring

theorem main : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    (l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ), l ∈ (adeleClass F).adm κ →
    (∀ (y : κ → AF F), ∀ φ ∈ schA F κ, l (fun x => ψ (x ⬝ᵥ y) * φ x) = l φ) →
    ∃ c : ℂ, ∀ φ ∈ schA F κ, l φ = c * φ 0 := by
  intro F _ _ ψ hψ κ _ l hl hinv

  have harch : ∀ g ∈ SB (κ → Af F), ∃ α : ℂ,
      ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, l (pureA F f g) = α * f 0 := by
    intro g hg
    obtain ⟨T, hT⟩ := hl g hg
    obtain ⟨α, hα⟩ := arch _ T (by
      intro L f f' hff'
      obtain ⟨Y, hY⟩ := GlobalTheory.TraceDual.exists_trace_rep F κ L
      rw [← hT, ← hT, ← hinv (fun i => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (Y i)) 0)
        (pureA F f g) (mem_schA f hg)]
      congr 1
      funext x
      simp only [pureA, hff', psi_dot_inf hψ, hY, mul_assoc])
    exact ⟨α, fun f => (hT f).trans (hα f)⟩

  obtain ⟨f₀, hf₀⟩ := exists_schwartz_one (κ → mixedEmbedding.mixedSpace F)
  let a : ((κ → Af F) → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun g => l (pureA F f₀ g)
      map_add' := fun g g' => by
        rw [← map_add (f := _)]
        congr 1
        funext x
        simp [pureA, mul_add]
      map_smul' := fun s g => by
        rw [RingHom.id_apply, ← map_smul]
        congr 1
        funext x
        simp [pureA, mul_comm, mul_assoc] }
  obtain ⟨c, hc⟩ := GlobalTheory.CharForm.exists_eq_mul_apply_zero (κ → Af F) {χ | ∃ y : κ → Af F, χ = fun x => ψ (pairA F 0 (x ⬝ᵥ y))}
    (by
      intro N hN
      obtain ⟨U, hUo, hUc, hUN, hsep⟩ := GlobalTheory.FinSepChar.finite_chars_separate F ψ hψ κ N hN
      refine ⟨U, hUo, hUc, hUN, fun x₀ hx₀ => ?_⟩
      obtain ⟨y, hyU, hy⟩ := hsep x₀ hx₀
      refine ⟨_, ⟨y, rfl⟩, fun u hu => ?_, hy⟩
      show ψ (pairA F 0 ((x₀ + u) ⬝ᵥ y)) = ψ (pairA F 0 (x₀ ⬝ᵥ y))
      rw [add_dotProduct, pairA_zero_add, AddChar.map_add_eq_mul, hyU u hu, mul_one])
    a
    (by
      rintro χ ⟨y, rfl⟩ g hg
      show l (pureA F f₀ _) = l (pureA F f₀ g)
      rw [← hinv (fun i => pairA F 0 (y i)) (pureA F f₀ g) (mem_schA f₀ hg)]
      congr 1
      funext x
      simp [pureA, dot_pairA_fin, mul_left_comm])
  refine ⟨c, fun φ hφ => ?_⟩
  induction hφ using Submodule.span_induction with
  | mem Φ hΦ =>
    obtain ⟨f, g, hg, rfl⟩ := hΦ
    obtain ⟨α, hα⟩ := harch g hg
    have hαc : α = c * g 0 := by
      have e1 := hα f₀
      rw [hf₀, mul_one] at e1
      rw [← e1]
      exact hc g hg
    rw [hα f, hαc, pureA_zero]
    ring
  | zero => simp
  | add φ φ' _ _ h h' => rw [map_add (f := _), h, h', Pi.add_apply, mul_add]
  | smul s φ _ h => rw [map_smul, h, Pi.smul_apply, smul_eq_mul, smul_eq_mul]; ring

end GlobalTheory.CharInvForm
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.skewHermitianLattice_splitPlace_components_dual : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (d : ℕ) (W : Spc F E d) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (c : GL (Fin d) (Fv F v)), IsSplitBasis t W.L c →
    ∃ (z : (Fv F v)ˣ) (c₂ : GL (Fin d) (Fv F v)), (PsiUnr B.ψ v → z = 1) ∧
      (c₂⁻¹).1 = (z : Fv F v) • (c.1ᵀ * W.J.map t) ∧ IsSplitBasis (t.comp σ) W.L c₂ := by
  first | exact @GlobalTheory.SkewSplitDual.skewSplitDual | exact GlobalTheory.SkewSplitDual.skewSplitDual | (intros; apply GlobalTheory.SkewSplitDual.skewSplitDual <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BoxSpan

theorem boxFun_mem_SB' {k : Type} [CommRing k] [TopologicalSpace k] [T2Space k] {κ κ' : Type}
    {φ₁ : (κ → k) → ℂ} {φ₂ : (κ' → k) → ℂ} (h₁ : φ₁ ∈ SB (κ → k)) (h₂ : φ₂ ∈ SB (κ' → k)) :
    boxFun φ₁ φ₂ ∈ SB (κ ⊕ κ' → k) := by
  have cl : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inl := continuous_pi fun i => continuous_apply _
  have cr : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inr := continuous_pi fun i => continuous_apply _
  refine ⟨(h₁.1.comp_continuous cl).mul (h₂.1.comp_continuous cr), ?_⟩
  let e := (Homeomorph.sumArrowHomeomorphProdArrow (X := k) (ι := κ) (ι' := κ'))
  refine HasCompactSupport.intro ((h₁.2.prod h₂.2).image e.symm.continuous) fun x hx => ?_
  have hx' : e x ∉ tsupport φ₁ ×ˢ tsupport φ₂ := fun h => hx ⟨e x, h, e.symm_apply_apply x⟩
  rw [Homeomorph.sumArrowHomeomorphProdArrow_apply, Set.mem_prod, not_and_or] at hx'
  simp only [boxFun]
  rcases hx' with h | h
  · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]

theorem schr_boxFun {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ κ' : Type} [Fintype κ]
    [Fintype κ'] (w : (κ ⊕ κ' → R) × (κ ⊕ κ' → R)) (φ₁ : (κ → R) → ℂ) (φ₂ : (κ' → R) → ℂ) :
    schr ψ w (boxFun φ₁ φ₂) = boxFun (schr ψ (w.1 ∘ Sum.inl, w.2 ∘ Sum.inl) φ₁)
      (schr ψ (w.1 ∘ Sum.inr, w.2 ∘ Sum.inr) φ₂) := by
  funext x
  simp only [schr, boxFun, dotProduct, Fintype.sum_sum_type, Function.comp_apply, Pi.add_apply]
  rw [show (∑ i, x (Sum.inl i) * w.2 (Sum.inl i)) + (∑ i, x (Sum.inr i) * w.2 (Sum.inr i)) +
      ⅟(2 : R) * ((∑ i, w.1 (Sum.inl i) * w.2 (Sum.inl i)) + (∑ i, w.1 (Sum.inr i) * w.2 (Sum.inr i))) =
      ((∑ i, x (Sum.inl i) * w.2 (Sum.inl i)) + ⅟(2 : R) * (∑ i, w.1 (Sum.inl i) * w.2 (Sum.inl i))) +
      ((∑ i, x (Sum.inr i) * w.2 (Sum.inr i)) + ⅟(2 : R) * (∑ i, w.1 (Sum.inr i) * w.2 (Sum.inr i))) by ring,
    AddChar.map_add_eq_mul]
  rw [show (x + w.1) ∘ Sum.inl = x ∘ Sum.inl + w.1 ∘ Sum.inl from rfl,
    show (x + w.1) ∘ Sum.inr = x ∘ Sum.inr + w.1 ∘ Sum.inr from rfl]
  ring

end GlobalTheory.BoxSpan


open GlobalTheory.BoxSpan in
theorem GlobalTheory.BoxSpan.boxSpan_ker : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ κ' : Type) [Fintype κ] [Fintype κ'] (ψ : AddChar (Fv F v) ℂ), Continuous ψ → ψ ≠ 1 →
    ∀ Λ : ((κ ⊕ κ' → Fv F v) → ℂ) →ₗ[ℂ] ℂ,
      (∀ φ₁ ∈ SB (κ → Fv F v), ∀ φ₂ ∈ SB (κ' → Fv F v), Λ (boxFun φ₁ φ₂) = 0) → ∀ Φ ∈ SB (κ ⊕ κ' → Fv F v), Λ Φ = 0 := by
  intro F _ _ v κ κ' _ _ ψ hψ h1 Λ hΛ Φ hΦ
  classical
  let N : Submodule ℂ ((κ ⊕ κ' → Fv F v) → ℂ) := Submodule.span ℂ
    {f | ∃ φ₁ ∈ SB (κ → Fv F v), ∃ φ₂ ∈ SB (κ' → Fv F v), f = boxFun φ₁ φ₂}
  have hN : N ≤ SB (κ ⊕ κ' → Fv F v) := by
    refine Submodule.span_le.2 ?_
    rintro f ⟨φ₁, h₁, φ₂, h₂, rfl⟩
    exact boxFun_mem_SB' h₁ h₂
  have hS : ∀ w, ∀ φ ∈ N, schr ψ w φ ∈ N := by
    intro w
    let Lw : ((κ ⊕ κ' → Fv F v) → ℂ) →ₗ[ℂ] ((κ ⊕ κ' → Fv F v) → ℂ) :=
      { toFun := schr ψ w
        map_add' := fun f g => by funext x; simp [schr, mul_add]
        map_smul' := fun c f => by funext x; simp [schr]; ring }
    have : N ≤ N.comap Lw := by
      refine Submodule.span_le.2 ?_
      rintro f ⟨φ₁, h₁, φ₂, h₂, rfl⟩
      show schr ψ w (boxFun φ₁ φ₂) ∈ N
      rw [schr_boxFun]
      exact Submodule.subset_span ⟨_, GlobalTheory.SchrSBFin.schr_mem_SB v ψ hψ _ _ h₁, _,
        GlobalTheory.SchrSBFin.schr_mem_SB v ψ hψ _ _ h₂, rfl⟩
    exact fun φ hφ => this hφ
  let i₁ := Set.indicator {x : κ → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} (1 : (κ → Fv F v) → ℂ)
  let i₂ := Set.indicator {x : κ' → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} (1 : (κ' → Fv F v) → ℂ)
  have h0 : boxFun i₁ i₂ ∈ N := Submodule.subset_span
    ⟨i₁, GlobalTheory.StdVacuum.indicator_mem_SB v, i₂, GlobalTheory.StdVacuum.indicator_mem_SB v, rfl⟩
  have hne : boxFun i₁ i₂ ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [boxFun, i₁, i₂, Set.indicator, zero_mem] at this
  have hall := GlobalTheory.SchrIrred.schr_irreducible v ψ hψ h1 N hN hS _ h0 hne
  have hk : N ≤ LinearMap.ker Λ := by
    refine Submodule.span_le.2 ?_
    rintro f ⟨φ₁, h₁, φ₂, h₂, rfl⟩
    exact hΛ φ₁ h₁ φ₂ h₂
  rw [← hall] at hΦ
  exact hk hΦ
end
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_admitted_diagonal_integral_linearForm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (a a' : ℕ) (G : Geo σ a a') (ψ : AddChar (AF F) ℂ)
    (d' : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J)) (Fin a' × Fin (a + a')))
    (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J))) ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')))),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) d' dd → ∀ v : Pl (F := F),
    ∃ l ∈ (adeleClass F).adm ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a'))),
      (∀ z : Matrix (Fin (a + a')) (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), ∀ φ ∈ (adeleClass F).sp ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a'))),
        l (dd.rho ψ (z * (diagCols (Fin a') : Matrix (Fin a' ⊕ Fin a') (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))ᵀ) φ) = l φ) ∧
      ∃ r₀ : ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → AF F) → ℂ, (∀ φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v), Rest (evFin F v) φ r₀) ∧
      ∃ c₀ : ℂ, c₀ ≠ 0 ∧ ∃ μ : @MeasureTheory.Measure ((Fin a' × Fin (a + a')) → Fv F v) (borel _),
        @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ ∧
        (∀ φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v), l (tens (evFin F v) φ r₀) = c₀ * ∫ x, φ (Sum.elim x x) ∂μ) ∧
        ∃ φ₀ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ∫ x, φ₀ x * φ₀ x ∂μ ≠ 0 := by
  first | exact @GlobalTheory.DiagLocal.exists_diag_form | exact GlobalTheory.DiagLocal.exists_diag_form | (intros; apply GlobalTheory.DiagLocal.exists_diag_form <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.InertLatSelfDual

theorem latAtV_selfDual_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ →
    ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ), X.IsHerm σ B r s → Y.IsSkew σ B r' s' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ z : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) z →
      (z ∈ latAtV X Y v ↔ ∀ γ ∈ latAtV X Y v,
        B.ψ (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) Y.J) z γ) = 1) := by
  intro F E _ _ _ _ _ σ B hB n d X Y r s r' s' hX hY v _w _hin z hz
  exact GlobalTheory.LatSelfDualAll.latAtV_selfDual F E σ B n d X Y r s r' s' hB hX hY v z hz

end GlobalTheory.InertLatSelfDual
end

section

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

theorem _root_.GlobalTheory.T.heisenbergLattice_selfDual_every_finitePlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (v : Pl (F := F)) (z : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), At (evFin F v) z →
      (z ∈ latAtV X W v ↔ ∀ γ ∈ latAtV X W v, B.ψ (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) z γ) = 1) := by
  first | exact @GlobalTheory.LatSelfDualAll.latAtV_selfDual | exact GlobalTheory.LatSelfDualAll.latAtV_selfDual | (intros; apply GlobalTheory.LatSelfDualAll.latAtV_selfDual <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (gauss unifAt PsiUnr)


theorem _root_.GlobalTheory.T.localGaussSum_integer_dvd_residueCard_pow : ∀ {F : Type} [Field F] [NumberField F] {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ)
    (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (ν : (Fv F v)ˣ →* ℂˣ), PsiUnr ψ v →
    Continuous (fun x : (Fv F v)ˣ => (ν x : ℂ)) → (∀ x, ‖(ν x : ℂ)‖ = 1) → 1 ≤ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν →
    (∀ x : (Fv F v)ˣ, (x : Fv F v) ∈ v.adicCompletionIntegers F → ((x⁻¹ : (Fv F v)ˣ) : Fv F v) ∈ v.adicCompletionIntegers F →
      (ν x : ℂ) ∈ Set.range σ) →
    (∀ ζ : ℂ, ζ ^ (Ideal.absNorm v.asIdeal ^ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν) = 1 → ζ ∈ Set.range σ) →
    ∃ g g' : 𝓞 K, σ g = gauss ψ ν ∧ g * g' = ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 K) ^ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν := by
  first | exact @GlobalTheory.GaussDiv.gauss_dvd_pow | exact GlobalTheory.GaussDiv.gauss_dvd_pow | (intros; apply GlobalTheory.GaussDiv.gauss_dvd_pow <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB

noncomputable section

namespace GlobalTheory.LeviSplit

open Matrix

section Ring

variable {R : Type} [CommRing R] {n n₁ k : ℕ}

end Ring

theorem exists_prod_equiv {G B : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group B] [TopologicalSpace B]
    (A T : Subgroup G) (m : B → A) (π : A → B) (hm : Continuous m) (hπ : Continuous π) (hmm : ∀ a b, m (a * b) = m a * m b)
    (hππ : ∀ a b, π (a * b) = π a * π b) (hπm : ∀ b, π (m b) = b) (hTA : T ≤ A) (hT : ∀ a : A, a.1 ∈ T ↔ π a = 1)
    (hc : ∀ τ ∈ T, ∀ b, τ * (m b : G) = m b * τ) : ∃ φ : T × B ≃ₜ* A, ∀ p, (φ p : G) = p.1 * m p.2 := by
  let π' := MonoidHom.mk' π hππ
  have h1 : ∀ τ : T, π' ⟨τ, hTA τ.2⟩ = 1 := fun τ => (hT ⟨τ, hTA τ.2⟩).1 τ.2
  have h2 : ∀ b, π' (m b) = b := hπm
  have h3 : ∀ (τ : T) b, π' (⟨τ, hTA τ.2⟩ * m b) = b := fun τ b => by rw [map_mul, h1, h2, one_mul]
  refine ⟨{ toFun := fun p => ⟨p.1, hTA p.1.2⟩ * m p.2
            invFun := fun a => (⟨(a * (m (π' a))⁻¹ : A), (hT _).2 (show π' _ = 1 by rw [map_mul, map_inv, h2, mul_inv_cancel])⟩, π' a)
            left_inv := fun p => Prod.ext (Subtype.ext ?_) (h3 _ _)
            right_inv := fun a => Subtype.ext ?_
            map_mul' := fun p q => Subtype.ext ?_
            continuous_toFun := ?_
            continuous_invFun := ?_ }, fun p => rfl⟩
  · simp only [h3]
    simp
  · simp
  · simp only [Prod.fst_mul, Prod.snd_mul, hmm, Subgroup.coe_mul]
    rw [mul_assoc, mul_assoc, ← mul_assoc (q.1 : G), hc _ q.1.2, mul_assoc]
  · exact ((continuous_subtype_val.comp continuous_fst).subtype_mk _).mul (hm.comp continuous_snd)
  · exact ((continuous_subtype_val.comp (continuous_id.mul (hm.comp hπ).inv)).subtype_mk _).prodMk hπ

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}





open GlobalTheory.StdPar GlobalTheory.SiegelSet in
theorem mem_leviOne {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E} {S : Finset (Fin r)}
    {g : GAd σ J} : g ∈ leviOne σ J X Y S ↔ ∀ k ∈ S,
      g ∈ frameStab σ J (initCols X k) ((⊤ : Subgroup (AE F E)ˣ).comap Matrix.GeneralLinearGroup.det) ∧
      g ∈ frameStab σ J (initCols Y k) ((⊤ : Subgroup (AE F E)ˣ).comap Matrix.GeneralLinearGroup.det) ∧
      g ∈ frameStab σ J (initCols X k) ((GlobalTheory.Doubling.absE F E).ker.comap Matrix.GeneralLinearGroup.det) := by
  simp only [leviOne, levi, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.comap_top, MonoidHom.comap_ker]
  exact ⟨fun h k hk => ⟨(h.1 k hk).1, (h.1 k hk).2, h.2 k hk⟩, fun h => ⟨fun k hk => ⟨(h k hk).1, (h k hk).2.1⟩,
    fun k hk => (h k hk).2.2⟩⟩


end GlobalTheory.LeviSplit
end
end

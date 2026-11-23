module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle297
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.ColMatMulGlEmbMat
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.EPGFalseEqLastIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle302
public import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.FiniteDimensionalHcSpace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle296
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.MapUgAlgebraMap
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.FormCos
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle299
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HodgeC

@[expose] public section

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Rodier.SmIntEl

open MeasureTheory

theorem finite_range {X W : Type} [TopologicalSpace X] [AddCommGroup W] {φ : X → W}
    (hl : IsLocallyConstant φ) (hc : HasCompactSupport φ) : (Set.range φ).Finite := by
  have : CompactSpace (tsupport φ) := isCompact_iff_compactSpace.mp hc
  have h1 : (Set.range (φ ∘ ((↑) : tsupport φ → X))).Finite :=
    (hl.comp_continuous continuous_subtype_val).range_finite
  refine (h1.insert 0).subset ?_
  rintro _ ⟨x, rfl⟩
  by_cases hx : x ∈ tsupport φ
  · exact Or.inr ⟨⟨x, hx⟩, rfl⟩
  · exact Or.inl (image_eq_zero_of_notMem_tsupport hx)

theorem measure_level_ne_top {X W : Type} [TopologicalSpace X] [MeasurableSpace X] [AddCommGroup W]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] {φ : X → W} (hc : HasCompactSupport φ) {v : W}
    (hv : v ≠ 0) : μ (φ ⁻¹' {v}) ≠ ⊤ := by
  refine ne_of_lt (lt_of_le_of_lt (measure_mono ?_) (IsCompact.measure_lt_top hc))
  intro x hx
  apply subset_tsupport
  rw [Function.mem_support, show φ x = v from hx]
  exact hv

theorem smInt_comp {X Y W : Type} [MeasurableSpace X] [AddCommGroup W] [Module ℂ W] (μ : Measure X)
    (ψ : X → Y) (g : Y → W) (S : Finset Y) (hS : ∀ x, ψ x ∈ S)
    (hm : ∀ y ∈ S, MeasurableSet (ψ ⁻¹' {y})) (hf : ∀ y ∈ S, g y ≠ 0 → μ (ψ ⁻¹' {y}) ≠ ⊤) :
    smInt μ (g ∘ ψ) = ∑ y ∈ S, (((μ (ψ ⁻¹' {y})).toReal : ℝ) : ℂ) • g y := by
  classical
  have hsupp : (Function.support fun v : W => (((μ ((g ∘ ψ) ⁻¹' {v})).toReal : ℝ) : ℂ) • v)
      ⊆ ↑(S.image g) := by
    intro v hv
    by_contra hvS
    apply hv
    have : (g ∘ ψ) ⁻¹' {v} = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro hx
      exact hvS (Finset.mem_coe.2 (Finset.mem_image.2 ⟨ψ x, hS x, hx⟩))
    simp [this]
  unfold smInt
  rw [finsum_eq_sum_of_support_subset _ hsupp,
    ← Finset.sum_fiberwise_of_maps_to (s := S) (t := S.image g) (g := g)
      (fun y hy => Finset.mem_image_of_mem g hy)]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases hv0 : v = 0
  · subst hv0
    rw [smul_zero]
    symm
    exact Finset.sum_eq_zero fun y hy => by rw [(Finset.mem_filter.1 hy).2, smul_zero]
  · have hset : (g ∘ ψ) ⁻¹' {v} = ⋃ y ∈ S.filter (fun y => g y = v), ψ ⁻¹' {y} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Function.comp, Set.mem_iUnion,
        Finset.mem_filter, exists_prop]
      constructor
      · intro hx
        exact ⟨ψ x, ⟨hS x, hx⟩, rfl⟩
      · rintro ⟨y, ⟨_, hy⟩, rfl⟩
        exact hy
    have hmeas : μ ((g ∘ ψ) ⁻¹' {v}) = ∑ y ∈ S.filter (fun y => g y = v), μ (ψ ⁻¹' {y}) := by
      rw [hset]
      refine measure_biUnion_finset ?_ fun y hy => hm y (Finset.mem_filter.1 hy).1
      intro a _ b _ hab
      exact Disjoint.preimage ψ (Set.disjoint_singleton.2 hab)
    rw [hmeas, ENNReal.toReal_sum (fun y hy => hf y (Finset.mem_filter.1 hy).1
      (by rw [(Finset.mem_filter.1 hy).2]; exact hv0)), Complex.ofReal_sum, Finset.sum_smul]
    exact Finset.sum_congr rfl fun y hy => by rw [(Finset.mem_filter.1 hy).2]

theorem smInt_add {X W : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [AddCommGroup W] [Module ℂ W] (μ : Measure X) [IsFiniteMeasureOnCompacts μ] {φ₁ φ₂ : X → W}
    (l₁ : IsLocallyConstant φ₁) (c₁ : HasCompactSupport φ₁)
    (l₂ : IsLocallyConstant φ₂) (c₂ : HasCompactSupport φ₂) :
    smInt μ (φ₁ + φ₂) = smInt μ φ₁ + smInt μ φ₂ := by
  classical
  let ψ : X → W × W := fun x => (φ₁ x, φ₂ x)
  let S : Finset (W × W) := (finite_range l₁ c₁).toFinset ×ˢ (finite_range l₂ c₂).toFinset
  have hS : ∀ x, ψ x ∈ S := fun x =>
    Finset.mem_product.2 ⟨(Set.Finite.mem_toFinset _).2 ⟨x, rfl⟩,
      (Set.Finite.mem_toFinset _).2 ⟨x, rfl⟩⟩
  have hm : ∀ y ∈ S, MeasurableSet (ψ ⁻¹' {y}) := fun y _ =>
    ((l₁.prodMk l₂).isOpen_fiber y).measurableSet
  have f₁ : ∀ y : W × W, y.1 ≠ 0 → μ (ψ ⁻¹' {y}) ≠ ⊤ := fun y hy =>
    ne_top_of_le_ne_top (measure_level_ne_top μ c₁ hy) (measure_mono fun x hx => by
      show φ₁ x = y.1
      rw [← show ψ x = y from hx])
  have f₂ : ∀ y : W × W, y.2 ≠ 0 → μ (ψ ⁻¹' {y}) ≠ ⊤ := fun y hy =>
    ne_top_of_le_ne_top (measure_level_ne_top μ c₂ hy) (measure_mono fun x hx => by
      show φ₂ x = y.2
      rw [← show ψ x = y from hx])
  have e₀ : smInt μ (φ₁ + φ₂) = ∑ y ∈ S, (((μ (ψ ⁻¹' {y})).toReal : ℝ) : ℂ) • (y.1 + y.2) :=
    smInt_comp μ ψ (fun y => y.1 + y.2) S hS hm fun y _ hy => by
      by_cases h : y.1 = 0
      · refine f₂ y fun h' => hy ?_
        show y.1 + y.2 = 0
        rw [h, h', add_zero]
      · exact f₁ y h
  have e₁ : smInt μ φ₁ = ∑ y ∈ S, (((μ (ψ ⁻¹' {y})).toReal : ℝ) : ℂ) • y.1 :=
    smInt_comp μ ψ (fun y => y.1) S hS hm fun y _ hy => f₁ y hy
  have e₂ : smInt μ φ₂ = ∑ y ∈ S, (((μ (ψ ⁻¹' {y})).toReal : ℝ) : ℂ) • y.2 :=
    smInt_comp μ ψ (fun y => y.2) S hS hm fun y _ hy => f₂ y hy
  rw [e₀, e₁, e₂, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun y _ => smul_add _ _ _

theorem smInt_linear {X W W' : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (μ : Measure X)
    [IsFiniteMeasureOnCompacts μ] (T : W →ₗ[ℂ] W') {φ : X → W}
    (l : IsLocallyConstant φ) (c : HasCompactSupport φ) :
    smInt μ (T ∘ φ) = T (smInt μ φ) := by
  classical
  let S : Finset W := (finite_range l c).toFinset
  have hS : ∀ x, φ x ∈ S := fun x => (Set.Finite.mem_toFinset _).2 ⟨x, rfl⟩
  have hm : ∀ y ∈ S, MeasurableSet (φ ⁻¹' {y}) := fun y _ => (l.isOpen_fiber y).measurableSet
  have e₀ : smInt μ (T ∘ φ) = ∑ y ∈ S, (((μ (φ ⁻¹' {y})).toReal : ℝ) : ℂ) • T y :=
    smInt_comp μ φ T S hS hm fun y _ hy =>
      measure_level_ne_top μ c fun h => hy (by rw [h, map_zero])
  have e₁ : smInt μ φ = ∑ y ∈ S, (((μ (φ ⁻¹' {y})).toReal : ℝ) : ℂ) • y :=
    smInt_comp μ φ id S hS hm fun y _ hy => measure_level_ne_top μ c hy

  rw [e₀, e₁, map_sum]
  exact Finset.sum_congr rfl fun y _ => (map_smul T _ y).symm

theorem smInt_comp_measurePreserving {X W : Type} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [AddCommGroup W] [Module ℂ W] (μ : Measure X) {c : X → X} {φ : X → W}
    (hc : MeasurePreserving c μ μ) (l : IsLocallyConstant φ) :
    smInt μ (φ ∘ c) = smInt μ φ := by
  unfold smInt
  refine finsum_congr fun v => ?_
  have h : μ (c ⁻¹' (φ ⁻¹' {v})) = μ (φ ⁻¹' {v}) :=
    hc.measure_preimage (l.isOpen_fiber v).measurableSet.nullMeasurableSet
  rw [Set.preimage_comp, h]

theorem smInt_indicator {X W : Type} [MeasurableSpace X] [AddCommGroup W] [Module ℂ W]
    (μ : Measure X) (A : Set X) (v : W) :
    smInt μ (A.indicator fun _ => v) = (((μ A).toReal : ℝ) : ℂ) • v := by
  classical
  unfold smInt
  by_cases hv : v = 0
  · subst hv
    rw [smul_zero]
    refine finsum_eq_zero_of_forall_eq_zero fun w => ?_
    by_cases hw : w = 0
    · rw [hw, smul_zero]
    · have : (A.indicator fun _ => (0 : W)) ⁻¹' {w} = ∅ := by
        ext x
        simp [Set.indicator_zero', Ne.symm hw]
      rw [this, measure_empty]
      simp
  · rw [finsum_eq_single _ v]
    · have : (A.indicator fun _ => v) ⁻¹' {v} = A := by
        ext x
        by_cases hx : x ∈ A
        · simp [hx]
        · simp [hx, Ne.symm hv]
      rw [this]
    · intro w hw
      by_cases hw0 : w = 0
      · rw [hw0, smul_zero]
      · have : (A.indicator fun _ => v) ⁻¹' {w} = ∅ := by
          ext x
          by_cases hx : x ∈ A
          · simp [hx, Ne.symm hw]
          · simp [hx, Ne.symm hw0]
        simp [this]

theorem smInt_properties : ∀ {X W W' : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (μ : MeasureTheory.Measure X) [MeasureTheory.IsFiniteMeasureOnCompacts μ], (∀ φ₁ φ₂ : X → W, IsLocallyConstant φ₁ → HasCompactSupport φ₁ → IsLocallyConstant φ₂ → HasCompactSupport φ₂ → smInt μ (φ₁ + φ₂) = smInt μ φ₁ + smInt μ φ₂) ∧ (∀ (T : W →ₗ[ℂ] W') (φ : X → W), IsLocallyConstant φ → HasCompactSupport φ → smInt μ (T ∘ φ) = T (smInt μ φ)) ∧ (∀ (c : X → X) (φ : X → W), MeasureTheory.MeasurePreserving c μ μ → IsLocallyConstant φ → smInt μ (φ ∘ c) = smInt μ φ) ∧ ∀ (A : Set X) (v : W), IsCompact A → IsOpen A → IsClosed A → smInt μ (A.indicator fun _ => v) = (((μ A).toReal : ℝ) : ℂ) • v := by
  intro X W W' _ _ _ _ _ _ _ μ _
  exact ⟨fun φ₁ φ₂ l₁ c₁ l₂ c₂ => smInt_add μ l₁ c₁ l₂ c₂,
    fun T φ l c => smInt_linear μ T l c,
    fun c φ hc l => smInt_comp_measurePreserving μ hc l,
    fun A v _ _ _ => smInt_indicator μ A v⟩

end GlobalTheory.CompanionTheory.Rodier.SmIntEl

end
end

section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG

section Group

variable (k : Type) [Field k]

abbrev Qp (i t : ℕ) : Subgroup (GL (Fin (i + t)) k) := parab k (two (stdSum (rfl : i + t = i + t)))

def qBlocks (i t : ℕ) : Qp k i t →* GL (Fin i) k × GL (Fin t) k :=
  MonoidHom.prod
    ((Pi.evalMonoidHom (fun x => GL (Two (Fin i) (Fin t) x) k) false).comp (leviProj k (two (stdSum rfl))))
    ((Pi.evalMonoidHom (fun x => GL (Two (Fin i) (Fin t) x) k) true).comp (leviProj k (two (stdSum rfl))))

def uM (n : ℕ) (y : Fin n → k) : Mir k n :=
  ⟨unip k n (Multiplicative.ofAdd y), MirU_le_Mir k n ⟨_, rfl⟩⟩

def topV (i t : ℕ) (x : Fin i → k) : Fin (i + t) → k := Fin.append x 0

def midV (i t : ℕ) (v : Fin t → k) : Fin (i + t) → k := Fin.append 0 v

theorem uM_add (n : ℕ) (a b : Fin n → k) : uM k n (a + b) = uM k n a * uM k n b := by
  apply Subtype.ext
  show unip k n (Multiplicative.ofAdd (a + b)) = unip k n (Multiplicative.ofAdd a) * unip k n (Multiplicative.ofAdd b)
  rw [ofAdd_add, map_mul]

theorem uM_zero (n : ℕ) : uM k n 0 = 1 := by
  apply Subtype.ext
  show unip k n (Multiplicative.ofAdd 0) = 1
  rw [ofAdd_zero, map_one]

theorem uM_mem (n : ℕ) (y : Fin n → k) : uM k n y ∈ MirUin k n := ⟨_, rfl⟩

theorem exists_uM_of_mem (n : ℕ) {u : Mir k n} (hu : u ∈ MirUin k n) : ∃ y, u = uM k n y := by
  obtain ⟨v, hv⟩ := (hu : (u : GL (Fin (n + 1)) k) ∈ MirU k n)
  exact ⟨v.toAdd, Subtype.ext hv.symm⟩

theorem levi_mul_uM (n : ℕ) (g : GL (Fin n) k) (y : Fin n → k) :
    levi k n g * uM k n y = uM k n ((g : Matrix (Fin n) (Fin n) k).mulVec y) * levi k n g := by
  apply Subtype.ext
  exact glEmb_mul_unip' k n g (Multiplicative.ofAdd y)

theorem topV_add_midV (i t : ℕ) (x : Fin i → k) (v : Fin t → k) :
    topV k i t x + midV k i t v = Fin.append x v := by
  funext j
  induction j using Fin.addCases <;> simp [topV, midV]

theorem exists_top_mid (i t : ℕ) (y : Fin (i + t) → k) : ∃ x v, y = topV k i t x + midV k i t v := by
  refine ⟨fun j => y (Fin.castAdd t j), fun j => y (Fin.natAdd i j), ?_⟩
  rw [topV_add_midV]
  funext j
  induction j using Fin.addCases <;> simp

end Group

section Rep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {i t : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def qRep (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) :
    Representation ℂ (Qp k i t) (Jacquet τ (MirUin k i) ⊗[ℂ] W) :=
  twist ((extTensor (psiMinus k τ) σ).comp (qBlocks k i t))
    ((detChar (Fin t) (absPow k (1 : ℂ))).comp ((MonoidHom.snd _ _).comp (qBlocks k i t)))

abbrev hRep (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) :
    Representation ℂ (HPG k i t) (V ⊗[ℂ] W) :=
  (extTensor τ σ).comp (pgProj k i t)

def clT (τ : Representation ℂ (Mir k i) V) (W : Type) [AddCommGroup W] [Module ℂ W] :
    V ⊗[ℂ] W →ₗ[ℂ] Jacquet τ (MirUin k i) ⊗[ℂ] W :=
  LinearMap.rTensor W (twKer τ (MirUin k i) 1).mkQ

def evL {τ : Representation ℂ (Mir k i) V} {σ : Representation ℂ (GL (Fin t) k) W} (p : Mir k (i + t)) :
    cIndSpace (HPG k i t) (hRep τ σ) →ₗ[ℂ] V ⊗[ℂ] W :=
  (LinearMap.proj p) ∘ₗ (indSpace (HPG k i t) (hRep τ σ)).subtype ∘ₗ (smoothPart (ind (HPG k i t) (hRep τ σ))).subtype ∘ₗ
    (cIndSpace (HPG k i t) (hRep τ σ)).subtype

def fibV {τ : Representation ℂ (Mir k i) V} {σ : Representation ℂ (GL (Fin t) k) W}
    (f : cIndSpace (HPG k i t) (hRep τ σ)) (g : GL (Fin (i + t)) k) (v : Fin t → k) : V ⊗[ℂ] W :=
  f.1.1.1 (uM k (i + t) (midV k i t v) * levi k (i + t) g)

def fibInt {τ : Representation ℂ (Mir k i) V} {σ : Representation ℂ (GL (Fin t) k) W}
    [MeasurableSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k))
    (f : cIndSpace (HPG k i t) (hRep τ σ)) (g : GL (Fin (i + t)) k) : Jacquet τ (MirUin k i) ⊗[ℂ] W :=
  clT τ W (smInt μ (fibV f g))

end Rep

end GlobalTheory.CompanionTheory.BZPsiPG

end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi.IotaMem

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem iotaM_castSucc_castSucc (n : ℕ) (y : Mir k n) (r c : Fin (n + 1)) :
    (((embedding₂ k n y : Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k) : Matrix _ _ k) (Fin.castSucc r) (Fin.castSucc c) =
      ((y : GL (Fin (n + 1)) k) : Matrix _ _ k) r c := by
  simp only [embedding₂, MonoidHom.coe_comp, Function.comp_apply]
  unfold levi
  simp [glEmb, glEmbHom, glEmbMat]

theorem iotaM_last_castSucc (n : ℕ) (y : Mir k n) (c : Fin (n + 1)) :
    (((embedding₂ k n y : Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k) : Matrix _ _ k) (Fin.last (n + 1)) (Fin.castSucc c) = 0 := by
  simp only [embedding₂, MonoidHom.coe_comp, Function.comp_apply]
  unfold levi
  simp [glEmb, glEmbHom, glEmbMat]

end GlobalTheory.CompanionTheory.LeibPhi.IotaMem

namespace GlobalTheory.CompanionTheory.LeibPhi


open GlobalTheory.CompanionTheory.LeibPhi.IotaMem in
theorem mem_mirabolicParabolic_iff_iotaM_mem (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (m j : ℕ) (y : Mir k (m + j)) :
    y ∈ MirabolicParabolic k m j ↔ embedding₂ k (m + j) y ∈ MirabolicParabolic k m (j + 1) := by
  have mem_iff (m j : ℕ) (g : Mir k (m + j)) :
      g ∈ MirabolicParabolic k m j ↔ ∀ (b : Fin (j + 1)) (a : Fin m),
        ((g : GL (Fin (m + j + 1)) k) : Matrix _ _ k)
          (eGP m j ⟨true, b⟩) (eGP m j ⟨false, a⟩) = 0 := by
    show (g : GL (Fin (m + j + 1)) k) ∈ parab k (eGP m j) ↔ _
    rw [mem_parab_iff]
    constructor
    · intro h b a
      exact h true false b a (by decide)
    · intro h x y i l hxy
      cases x <;> cases y <;> first | exact absurd hxy (by decide) | exact h i l
  rw [mem_iff, mem_iff]
  have eF : ∀ a : Fin m, eGP m (j + 1) ⟨false, a⟩ = Fin.castSucc (eGP m j ⟨false, a⟩) := by
    intro a
    ext
    simp [blockIndex_false_val]
  have eT : ∀ b : Fin (j + 1),
      eGP m (j + 1) ⟨true, Fin.castSucc b⟩ = Fin.castSucc (eGP m j ⟨true, b⟩) := by
    intro b
    ext
    simp [blockIndex_true_val]
  have eL : eGP m (j + 1) ⟨true, Fin.last (j + 1)⟩ = Fin.last (m + j + 1) := by
    ext
    simp [blockIndex_true_val]
    omega
  constructor
  · intro h b a
    induction b using Fin.lastCases with
    | last =>
      rw [eL, eF]
      exact iotaM_last_castSucc k (m + j) y _
    | cast b =>
      rw [eT, eF]
      rw [iotaM_castSucc_castSucc k (m + j) y]
      exact h b a
  · intro h b a
    have hb := h (Fin.castSucc b) a
    rw [eT, eF, iotaM_castSucc_castSucc k (m + j) y] at hb
    exact hb

end GlobalTheory.CompanionTheory.LeibPhi

end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi

theorem continuous_glEmbMat_comp {k X : Type} [Field k] [TopologicalSpace k] [TopologicalSpace X] (m : ℕ)
    {f : X → Matrix (Fin m) (Fin m) k} (hf : Continuous f) :
    Continuous fun x => glEmbMat k m (f x) := by
  refine continuous_matrix fun i j => ?_
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp only [GlobalTheory.BZMir.glEmbMat, Fin.lastCases_last, Fin.lastCases_castSucc] <;>
    first
    | exact continuous_const
    | exact hf.matrix_elem _ _

theorem continuous_iotaM : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ), Continuous (embedding₂ k n) := by
  intro k _ _ _ _ n
  have hemb : Continuous (GlobalTheory.BZMir.glEmb k (n + 1)) :=
    Continuous.units_map _ (GlobalTheory.CompanionTheory.LeibPhi.continuous_glEmbMat_comp (n + 1) continuous_id)
  exact continuous_induced_rng.2 (hemb.comp continuous_subtype_val)

end GlobalTheory.CompanionTheory.LeibPhi

end
end

section

open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open Polynomial CategoryTheory

theorem _root_.GlobalTheory.T.exists_cuspidal_with_label : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (C : LabelConv K) (d : ℕ), 1 ≤ d → ∀ P : K[X], P.Monic → Irreducible P → P ≠ X → P.natDegree = d →
    ∃ τ : FDRep ℂ (GL (Fin d) K), Simple τ ∧ IsCuspidal K τ ∧ HasCuspLabel C τ P := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.CuspLabel.exists_cuspidal_label | exact GlobalTheory.CompanionTheory.TyFin.CuspLabel.exists_cuspidal_label | (intros; apply GlobalTheory.CompanionTheory.TyFin.CuspLabel.exists_cuspidal_label <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

theorem _root_.GlobalTheory.T.expansion_eq_zero_iff_coeffs_mem : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (c : ℕ →₀ A.A), A.expand c = 0 ↔ ∀ k, c k ∈ Ideal.span {A.pi ^ l} := by
  first | exact @GlobalTheory.CompanionTheory.ExpandKer.expand_eq_zero_iff | exact GlobalTheory.CompanionTheory.ExpandKer.expand_eq_zero_iff | (intros; apply GlobalTheory.CompanionTheory.ExpandKer.expand_eq_zero_iff <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

theorem _root_.GlobalTheory.T.quotient_maps_surjective_with_kernels : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ), Function.Surjective (A.uToQ n) ∧ RingHom.ker (A.uToQ n) = Ideal.span {(l : A.U) ^ n} ∧ Function.Surjective (A.uToPQ n) ∧ (n ≠ 0 → RingHom.ker (A.uToPQ n) = Ideal.span {(l : A.U)}) := by
  first | exact @GlobalTheory.CompanionTheory.Untilt.uToQ_main | exact GlobalTheory.CompanionTheory.Untilt.uToQ_main | (intros; apply GlobalTheory.CompanionTheory.Untilt.uToQ_main <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

theorem _root_.GlobalTheory.T.cover_star_isCosieve : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (U : Cov q) (a : ℕ) (α : U.ι),
    Cosieve (Vk q U a α) := by
  first | exact @GlobalTheory.CompanionTheory.OmGlob.vk_cosieve | exact GlobalTheory.CompanionTheory.OmGlob.vk_cosieve | (intros; apply GlobalTheory.CompanionTheory.OmGlob.vk_cosieve <;> assumption)
end

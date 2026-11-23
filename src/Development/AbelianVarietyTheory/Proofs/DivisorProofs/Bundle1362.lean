module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1248
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianModelOfNormNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitLength
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle265
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNhdsTransportedActionFinitePointPreimage
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle547
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1257
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle651
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle704
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle916
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1258
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
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

noncomputable section

namespace GlobalTheory.InertUnitOrb.LatOnto

open GlobalTheory.InertUnitOrb.ModelOfN

theorem exists_orthonormal_mem {K : UQ} (n : ℕ) : ∀ (V : Type) [AddCommGroup V] [Module K.E V] [Module K.O V]
    [IsScalarTower K.O K.E V] [FiniteDimensional K.E V] (h : V → V → K.E),
    (∀ y y' z, h (y + y') z = h y z + h y' z) → (∀ (a : K.E) y z, h (a • y) z = a * h y z) →
    (∀ y z, h z y = K.c (h y z)) → Module.finrank K.E V = n → ∀ L : Submodule K.O V, L.FG →
    Submodule.span K.E (L : Set V) = ⊤ → (∀ y, y ∈ L ↔ ∀ z ∈ L, h y z ∈ (algebraMap K.O K.E).range) →
    ∃ v : Fin n → V, (∀ i, v i ∈ L) ∧ ∀ i j, h (v i) (v j) = if i = j then 1 else 0 := by
  first
  | exact @_root_.GlobalTheory.InvolutionTraceUnit.exists_orthonormal
  | exact _root_.GlobalTheory.InvolutionTraceUnit.exists_orthonormal
  | (apply _root_.GlobalTheory.InvolutionTraceUnit.exists_orthonormal <;> assumption)
  | (intros; apply _root_.GlobalTheory.InvolutionTraceUnit.exists_orthonormal <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InvolutionTraceUnit.exists_orthonormal <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InvolutionTraceUnit.exists_orthonormal ..)

end GlobalTheory.InertUnitOrb.LatOnto

namespace GlobalTheory.InertUnitOrb.LatOnto

open GlobalTheory.InertUnitOrb.ModelOfN

theorem exists_unitLat_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (x : B.Aˣ), B.σ (x : B.A) = x → (∀ y z, stdH K n (ψ y) (ψ z) = B.herm x y z) → ∀ L : Submodule K.O B.A, IsLat K.O K.E L → (∀ y, y ∈ L ↔ ∀ z ∈ L, B.herm x y z ∈ (algebraMap K.O K.E).range) → ∃ q : UL n w, unitLat e B ψ q = L := by
  intro E _ _ _ _ w hns K e he hint n B ψ x hσx hH L hLat hdual
  have hadd : ∀ y y' z, B.herm x (y + y') z = B.herm x y z + B.herm x y' z := by
    intro y y' z
    simp only [InvAlg.herm, mul_add, add_mul, map_add (f := _)]
  have hsmul : ∀ (a : K.E) y z, B.herm x (a • y) z = a * B.herm x y z := by
    intro a y z
    simp only [InvAlg.herm, mul_smul_comm, smul_mul_assoc, map_smul, smul_eq_mul]
  have hsym : ∀ y z, B.herm x z y = K.c (B.herm x y z) := by
    intro y z
    simp only [InvAlg.herm]
    rw [← trace_sigma B, map_mul B.σ, map_mul B.σ, B.σ_σ, hσx]
    congr 1
    ring
  have hn : Module.finrank K.E B.A = n := by rw [ψ.finrank_eq, Module.finrank_fin_fun]
  obtain ⟨v, hvL, hv⟩ := exists_orthonormal_mem n B.A (B.herm x) hadd hsmul hsym hn L hLat.1 hLat.2 hdual
  obtain ⟨b, hb⟩ := exists_basis_of_orthonormal (B.herm x) hadd hsmul hn v hv
  let P : Matrix (Fin n) (Fin n) K.E := Matrix.of fun i j => ψ (v j) i
  let Pc : Matrix (Fin n) (Fin n) K.E := Formalism.UG.cT (K.c : K.E →+* K.E) P
  have hPc : ∀ i k, Pc i k = K.c (ψ (v i) k) := fun i k => rfl
  have hPP : Pc * P = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    have h1 := hH (v j) (v i)
    simp only [stdH] at h1
    simp only [hPc, P, Matrix.of_apply]
    rw [show (∑ k, K.c (ψ (v i) k) * ψ (v j) k) = ∑ k, ψ (v j) k * K.c (ψ (v i) k) from
      Finset.sum_congr rfl fun k _ => mul_comm _ _, h1, hv]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  have hPP' : P * Pc = 1 := mul_eq_one_comm.1 hPP
  let eh : K.E →+* w.adicCompletion E := e.toRingHom
  have hmul1 : P.map eh * Pc.map eh = 1 := by
    rw [← Matrix.map_mul, hPP', Matrix.map_one _ (map_zero eh) (map_one eh)]
  have hmul2 : Pc.map eh * P.map eh = 1 := by
    rw [← Matrix.map_mul, hPP, Matrix.map_one _ (map_zero eh) (map_one eh)]
  let qG : GLw n w := ⟨P.map eh, Pc.map eh, hmul1, hmul2⟩
  have hcT : Formalism.UG.cT (cj w) (P.map eh) = Pc.map eh := by
    refine Matrix.ext fun i j => ?_
    change cj w (e (ψ (v i) j)) = e (K.c (ψ (v i) j))
    exact (he _).symm
  have hqU : qG ∈ UL n w := by
    unfold UL
    rw [if_neg hns]
    show Formalism.UG.cT (cj w) (P.map eh) * 1 * P.map eh = 1
    rw [hcT, Matrix.mul_one, hmul2]
  refine ⟨⟨qG, hqU⟩, ?_⟩
  have hinv : ((((⟨qG, hqU⟩ : UL n w)⁻¹ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map
      e.symm = Pc := by
    refine Matrix.ext fun i j => ?_
    show e.symm (e (Pc i j)) = Pc i j
    exact e.symm_apply_apply _
  have hcoef : ∀ y i, (Pc *ᵥ ψ y) i = B.herm x y (v i) := by
    intro y i
    rw [← hH]
    simp only [Matrix.mulVec, dotProduct, hPc, stdH]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hexp : ∀ y j, B.herm x y (v j) = b.repr y j := by
    intro y j
    conv_lhs => rw [← b.sum_repr y]
    rw [show B.herm x (∑ i, b.repr y i • b i) (v j) = ∑ i, b.repr y i * B.herm x (b i) (v j) from ?_]
    · simp only [hb, hv, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    · induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
      | empty =>
        simp only [Finset.sum_empty]
        have := hsmul 0 0 (v j)
        simpa using this
      | insert a s ha ih' =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, hsmul, ih']
  unfold unitLat
  rw [hinv]
  ext y
  show (∀ i, (Matrix.toLin' Pc (ψ y)) i ∈ (algebraMap K.O K.E).range) ↔ y ∈ L
  simp only [Matrix.toLin'_apply, hcoef]
  constructor
  · intro H
    choose a ha using H
    have hy : y = ∑ i, a i • v i := by
      conv_lhs => rw [← b.sum_repr y]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hexp, ← ha, algebraMap_smul, hb]
    rw [hy]
    exact Submodule.sum_mem _ fun i _ => L.smul_mem _ (hvL i)
  · intro hy i
    exact (hdual y).1 hy (v i) (hvL i)

end GlobalTheory.InertUnitOrb.LatOnto
end
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SwapSliceBij

open GlobalTheory.SwapSlice

theorem totDisc_localField (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : TotallyDisconnectedSpace k := by
  haveI : T2Space k := inferInstance
  haveI : NonarchimedeanAddGroup k := ⟨fun V hV => by
    obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_subset hV
    exact ⟨⟨⟨⟨⟨GlobalTheory.SplitWeil.cball s, GlobalTheory.SplitWeil.add_mem_cball⟩, by simp [GlobalTheory.SplitWeil.cball]⟩,
      GlobalTheory.SplitWeil.neg_mem_cball⟩, GlobalTheory.SplitWeil.isOpen_cball s⟩, hs⟩⟩
  infer_instance

theorem conj_mem_SB {X : Type} [TopologicalSpace X] {f : X → ℂ} (hf : f ∈ SB X) :
    (fun x => starRingEnd ℂ (f x)) ∈ SB X :=
  ⟨hf.1.comp (starRingEnd ℂ), hf.2.comp_left (map_zero _)⟩

theorem barL_bijOn {k Y : Type} [TopologicalSpace k] [TopologicalSpace Y] {κ : Type}
    (ι : ((κ → k) → ℂ) →ₗ[ℂ] (Y → ℂ)) (h : Set.BijOn ι (SB (κ → k) : Set ((κ → k) → ℂ)) (SB Y : Set (Y → ℂ))) :
    Set.BijOn (barL ι) (SB (κ → k) : Set ((κ → k) → ℂ)) (SB Y : Set (Y → ℂ)) := by
  refine ⟨fun φ hφ => conj_mem_SB (h.mapsTo (conj_mem_SB hφ)), fun φ hφ ψ hψ e => ?_, fun g hg => ?_⟩
  · have e' : ι (fun x => starRingEnd ℂ (φ x)) = ι (fun x => starRingEnd ℂ (ψ x)) := by
      funext y
      have := congrFun e y
      simp only [barL_apply] at this
      simpa using congrArg (starRingEnd ℂ) this
    have e'' := h.injOn (conj_mem_SB hφ) (conj_mem_SB hψ) e'
    funext x
    simpa using congrArg (starRingEnd ℂ) (congrFun e'' x)
  · obtain ⟨φ', hφ', e⟩ := h.surjOn (conj_mem_SB hg)
    refine ⟨fun x => starRingEnd ℂ (φ' x), conj_mem_SB hφ', ?_⟩
    funext y
    simp [barL_apply, e]

theorem boxFun_mem {k : Type} [CommRing k] [TopologicalSpace k] [T2Space k] {κ κ' : Type}
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

variable {k : Type} [CommRing k] [TopologicalSpace k] [T2Space k] [LocallyCompactSpace k] [TotallyDisconnectedSpace k]
  {κ : Type} [Fintype κ]

theorem SB_le_span_boxFun :
    SB (κ ⊕ κ → k) ≤ Submodule.span ℂ {f | ∃ φ₁ ∈ SB (κ → k), ∃ φ₂ ∈ SB (κ → k), f = boxFun φ₁ φ₂} := by
  intro Φ hΦ
  let e := Homeomorph.sumArrowHomeomorphProdArrow (X := k) (ι := κ) (ι' := κ)
  have hspan := GlobalTheory.LocFlat.CFac.Span.span_prodSB_eq_top (κ → k) (κ → k)
  let T : GlobalTheory.SplitWeil.SB ((κ → k) × (κ → k)) →ₗ[ℂ] ((κ ⊕ κ → k) → ℂ) :=
    (LinearMap.funLeft ℂ ℂ e) ∘ₗ (GlobalTheory.SplitWeil.SB _).subtype
  have hΦ' : Φ ∘ e.symm ∈ GlobalTheory.SplitWeil.SB ((κ → k) × (κ → k)) :=
    ⟨hΦ.1.comp_continuous e.symm.continuous, hΦ.2.comp_homeomorph e.symm⟩
  have key : Φ ∈ Submodule.map T ⊤ := ⟨⟨Φ ∘ e.symm, hΦ'⟩, trivial, by
    funext x; simp [T, LinearMap.funLeft]⟩
  rw [← hspan, Submodule.map_span, ← Set.range_comp] at key
  refine Submodule.span_mono ?_ key
  rintro _ ⟨q, rfl⟩
  exact ⟨q.1.1, q.1.2, q.2.1, q.2.2, by funext x; rfl⟩

theorem mem_of_boxFun {M : Type} [AddCommGroup M] [Module ℂ M] (L : ((κ ⊕ κ → k) → ℂ) →ₗ[ℂ] M) (P : Submodule ℂ M)
    (h : ∀ φ₁ ∈ SB (κ → k), ∀ φ₂ ∈ SB (κ → k), L (boxFun φ₁ φ₂) ∈ P) : ∀ Φ ∈ SB (κ ⊕ κ → k), L Φ ∈ P := by
  intro Φ hΦ
  have hle : Submodule.span ℂ {f | ∃ φ₁ ∈ SB (κ → k), ∃ φ₂ ∈ SB (κ → k), f = boxFun φ₁ φ₂} ≤ P.comap L :=
    Submodule.span_le.2 (by rintro _ ⟨φ₁, h₁, φ₂, h₂, rfl⟩; exact h φ₁ h₁ φ₂ h₂)
  exact hle (SB_le_span_boxFun hΦ)

end GlobalTheory.SwapSliceBij


open GlobalTheory.SwapSlice GlobalTheory.SwapSliceBij in
theorem GlobalTheory.SwapSliceBij.sliceT_bijOn : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {κ : Type} [Fintype κ] {n d : ℕ}
    (ι : ((κ → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ)),
    Set.BijOn ι (SB (κ → k) : Set ((κ → k) → ℂ)) (SB (Matrix (Fin n) (Fin d) k) : Set _) →
    Set.BijOn (GlobalTheory.SwapSlice.sliceT ι) (SB (κ ⊕ κ → k) : Set ((κ ⊕ κ → k) → ℂ))
      (SB (Matrix (Fin n) (Fin d) k × Matrix (Fin n) (Fin d) k) : Set _) := by
  intro k _ _ _ _ κ _ n d ι hι
  haveI : T2Space k := inferInstance
  haveI := totDisc_localField k
  haveI : LocallyCompactSpace k := inferInstance
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin d) k) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin d → k))
  haveI : TotallyDisconnectedSpace (Matrix (Fin n) (Fin d) k) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin d → k))
  haveI : T2Space (Matrix (Fin n) (Fin d) k) := inferInstanceAs (T2Space (Fin n → Fin d → k))
  have hbar := barL_bijOn ι hι

  have hslice : ∀ x₂ : κ → k, ∀ Φ ∈ SB (κ ⊕ κ → k), (fun x₁ => Φ (Sum.elim x₁ x₂)) ∈ SB (κ → k) := by
    intro x₂
    refine mem_of_boxFun (LinearMap.funLeft ℂ ℂ (fun x₁ : κ → k => Sum.elim x₁ x₂)) (SB (κ → k)) ?_
    intro φ₁ h₁ φ₂ h₂
    have e : LinearMap.funLeft ℂ ℂ (fun x₁ : κ → k => Sum.elim x₁ x₂) (boxFun φ₁ φ₂) = φ₂ x₂ • φ₁ := by
      funext x₁; simp [LinearMap.funLeft, boxFun, Function.comp_def, mul_comm]
    rw [e]; exact Submodule.smul_mem _ _ h₁

  have hcol : ∀ Z₁ : Matrix (Fin n) (Fin d) k, ∀ Φ ∈ SB (κ ⊕ κ → k),
      (fun x₂ => ι (fun x₁ => Φ (Sum.elim x₁ x₂)) Z₁) ∈ SB (κ → k) := by
    intro Z₁
    refine mem_of_boxFun (LinearMap.pi fun x₂ : κ → k => (LinearMap.proj Z₁) ∘ₗ ι ∘ₗ
      LinearMap.funLeft ℂ ℂ (fun x₁ : κ → k => Sum.elim x₁ x₂)) (SB (κ → k)) ?_
    intro φ₁ h₁ φ₂ h₂
    have e : (LinearMap.pi fun x₂ : κ → k => (LinearMap.proj Z₁) ∘ₗ ι ∘ₗ
        LinearMap.funLeft ℂ ℂ (fun x₁ : κ → k => Sum.elim x₁ x₂)) (boxFun φ₁ φ₂) = ι φ₁ Z₁ • φ₂ := by
      funext x₂
      have e' : LinearMap.funLeft ℂ ℂ (fun x₁ : κ → k => Sum.elim x₁ x₂) (boxFun φ₁ φ₂) = φ₂ x₂ • φ₁ := by
        funext x₁; simp [LinearMap.funLeft, boxFun, Function.comp_def, mul_comm]
      simp only [LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, e', map_smul, LinearMap.coe_proj,
        Function.eval, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e]; exact Submodule.smul_mem _ _ h₂
  have hz : ∀ Φ ∈ SB (κ ⊕ κ → k), sliceT ι Φ = 0 → Φ = 0 := by
    intro Φ hΦ h0
    have h1 : ∀ Z₁, (fun x₂ => ι (fun x₁ => Φ (Sum.elim x₁ x₂)) Z₁) = 0 := by
      intro Z₁
      refine hbar.injOn (hcol Z₁ Φ hΦ) (zero_mem _) ?_
      rw [map_zero]; funext Z₂; exact congrFun h0 (Z₁, Z₂)
    have h2 : ∀ x₂, (fun x₁ => Φ (Sum.elim x₁ x₂)) = 0 := by
      intro x₂
      refine hι.injOn (hslice x₂ Φ hΦ) (zero_mem _) ?_
      rw [map_zero]; funext Z₁; exact congrFun (h1 Z₁) x₂
    funext x
    have := congrFun (h2 (x ∘ Sum.inr)) (x ∘ Sum.inl)
    simpa [Sum.elim_comp_inl_inr] using this
  refine ⟨?_, fun Φ hΦ Ψ hΨ e => sub_eq_zero.1 (hz (Φ - Ψ) (sub_mem hΦ hΨ) (by rw [map_sub, e, sub_self])), ?_⟩
  · intro Φ hΦ
    refine mem_of_boxFun (sliceT ι) _ ?_ Φ hΦ
    intro φ₁ h₁ φ₂ h₂
    have e : sliceT ι (boxFun φ₁ φ₂) = GlobalTheory.LocFlat.CFac.prodFn (ι φ₁) (barL ι φ₂) := by
      funext Z; rw [sliceT_boxFun]; rfl
    rw [e]; exact GlobalTheory.LocFlat.CFac.prodFn_mem_SB (hι.mapsTo h₁) (hbar.mapsTo h₂)
  · intro g hg
    have hspan := GlobalTheory.LocFlat.CFac.Span.span_prodSB_eq_top (Matrix (Fin n) (Fin d) k) (Matrix (Fin n) (Fin d) k)
    have key : g ∈ Submodule.map (GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin d) k × Matrix (Fin n) (Fin d) k)).subtype ⊤ :=
      ⟨⟨g, hg⟩, trivial, rfl⟩
    rw [← hspan, Submodule.map_span, ← Set.range_comp] at key
    have hle : Submodule.span ℂ (Set.range ((GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin d) k × Matrix (Fin n) (Fin d) k)).subtype ∘
        fun q : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin d) k) × GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin d) k) =>
          GlobalTheory.LocFlat.CFac.prodSB q.1 q.2)) ≤ Submodule.map (sliceT ι) (SB (κ ⊕ κ → k)) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨q, rfl⟩
      obtain ⟨φ₁, h₁, e₁⟩ := hι.surjOn q.1.2
      obtain ⟨φ₂, h₂, e₂⟩ := hbar.surjOn q.2.2
      refine ⟨boxFun φ₁ φ₂, boxFun_mem h₁ h₂, ?_⟩
      funext Z
      rw [sliceT_boxFun, e₁, e₂]
      rfl
    obtain ⟨Φ, hΦ, e⟩ := Submodule.mem_map.1 (hle key)
    exact ⟨Φ, hΦ, e⟩
end
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

theorem _root_.GlobalTheory.T.exists_nhds_transportedAction_finitePoint_preimage : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (a b : ℕ) (JA : Matrix (Fin a) (Fin a) E) (JB : Matrix (Fin b) (Fin b) E) (ξ : AF F ⊗[F] E) (κ : Type) [Fintype κ]
    (co : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ξ ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) κ) (L₁ L₂ : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)),
    IsOpen (L₁ : Set (κ → FiniteAdeleRing (𝓞 F) F)) → IsOpen (L₂ : Set (κ → FiniteAdeleRing (𝓞 F) F)) →
    ∀ p0 : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) × UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB),
    ∃ N ∈ nhds p0, ∃ L₁' L₂' : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F),
      IsOpen (L₁' : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧ IsCompact (L₁' : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧
      IsOpen (L₂' : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧
      ∀ p ∈ N, ∀ x ∈ L₁', ∀ y ∈ L₂', ∃ x' ∈ L₁, ∃ y' ∈ L₂,
        co.e (actAB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) p (co.e.symm (GlobalTheory.WeilCont.adeleJoin F 0 x', GlobalTheory.WeilCont.adeleJoin F 0 y'))) =
          (GlobalTheory.WeilCont.adeleJoin F 0 x, GlobalTheory.WeilCont.adeleJoin F 0 y) := by
  first | exact @GlobalTheory.WeilTransNbhd.exists_nhds_finite_preimage | exact GlobalTheory.WeilTransNbhd.exists_nhds_finite_preimage | (intros; apply GlobalTheory.WeilTransNbhd.exists_nhds_finite_preimage <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.exists_harrisTaylorObject_of_levelLift : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N N' : ℕ) (hd : N ∣ N') (hc : N'.Coprime p) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (T : Over S) (lv : D.La → (T ⟶ o.A)), IsLift o N' T lv → ∃ (o'' : Obj b N' (T.hom ≫ s)) (mm : ObjMap (o''.forget N hd hc) o T.hom), ∀ a, (o''.eta a).left ≫ mm.φ = (lv a).left := by
  first | exact @GlobalTheory.HTLift.exists_obj_of_isLift | exact GlobalTheory.HTLift.exists_obj_of_isLift | (intros; apply GlobalTheory.HTLift.exists_obj_of_isLift <;> assumption)
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff

theorem _root_.GlobalTheory.T.adelicLinearCoordinates_rational_surjective_of_CM : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (nS nT N : ℕ)
    (e : Formalism.IndefR.DatumF.WOF F E nS nT ≃ₗ[AF F] GlobalTheory.ThetaTransform.VA F N),
    (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin N → F, e (Formalism.IndefR.DatumF.ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z)) →
    ∀ y z : Fin N → F, ∃ x : Matrix (Fin nT) (Fin nS) E, e (Formalism.IndefR.DatumF.ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z) := by
  first | exact @GlobalTheory.WeilSchrodinger.rat_onto_of_rat_maps_F | exact GlobalTheory.WeilSchrodinger.rat_onto_of_rat_maps_F | (intros; apply GlobalTheory.WeilSchrodinger.rat_onto_of_rat_maps_F <;> assumption)
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

namespace GlobalTheory.RealLift.Dbl.ColBlocks

theorem mul_transpose_doubledSpaceFrame_toCols1 {α β : Type} [Fintype β] {R S : ℕ} (M : Matrix α (Ix (R + S) (S + R)) ℂ) (C : Matrix β (Ix R S) ℂ) :
    (M * (dblM C)ᵀ).toCols₁ =
      M.submatrix id (Sum.elim (fun r => Sum.inl (Fin.castAdd S r)) (fun s => Sum.inr (Fin.castAdd R s))) * Cᵀ := by
  ext a i
  simp only [Matrix.toCols₁, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, id,
    dblM, Fintype.sum_sum_type, Fin.sum_univ_add, dblCol, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
    add_zero, zero_add]

theorem mul_transpose_doubledSpaceFrame_toCols2 {α β : Type} [Fintype β] {R S : ℕ} (M : Matrix α (Ix (R + S) (S + R)) ℂ) (C : Matrix β (Ix R S) ℂ) :
    (M * (dblM C)ᵀ).toCols₂ =
      M.submatrix id (Sum.elim (fun r => Sum.inr (Fin.natAdd S r)) (fun s => Sum.inl (Fin.natAdd R s))) * Cᵀ := by
  ext a i
  simp only [Matrix.toCols₂, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, id,
    dblM, Fintype.sum_sum_type, Fin.sum_univ_add, dblCol, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
    add_zero, zero_add]
  ring

theorem mul_submatrix_right {α γ δ ε : Type} [Fintype γ] (A : Matrix α γ ℂ) (c : Matrix γ δ ℂ) (e : ε → δ) :
    A * c.submatrix id e = (A * c).submatrix id e := rfl

theorem jm_right_L {γ : Type} {R S : ℕ} (X : Matrix γ (Ix (R + S) (S + R)) ℂ) :
    (X * Jm (R + S) (S + R)).submatrix id
        (Sum.elim (fun r => Sum.inl (Fin.castAdd S r)) (fun s => Sum.inr (Fin.castAdd R s))) =
      X.submatrix id (Sum.elim (fun r => Sum.inl (Fin.castAdd S r)) (fun s => Sum.inr (Fin.castAdd R s))) * Jm R S := by
  ext a k
  rcases k with r | s <;>
  simp [Jm, Formalism.UG.Jpq, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply]

theorem jm_right_R {γ : Type} {R S : ℕ} (X : Matrix γ (Ix (R + S) (S + R)) ℂ) :
    (X * Jm (R + S) (S + R)).submatrix id
        (Sum.elim (fun r => Sum.inr (Fin.natAdd S r)) (fun s => Sum.inl (Fin.natAdd R s))) =
      -(X.submatrix id (Sum.elim (fun r => Sum.inr (Fin.natAdd S r)) (fun s => Sum.inl (Fin.natAdd R s))) * Jm R S) := by
  ext a k
  rcases k with r | s <;>
  simp [Jm, Formalism.UG.Jpq, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply]

end GlobalTheory.RealLift.Dbl.ColBlocks

namespace GlobalTheory.RealLift.Dbl


open GlobalTheory.RealLift.Dbl.ColBlocks in
theorem dblM_colBlocks : ∀ (α β : Type) [Fintype β] (P Q R S : ℕ) (A : Matrix α (Ix P Q) ℂ) (C : Matrix β (Ix R S) ℂ)
    (c : Matrix (Ix P Q) (Ix (R + S) (S + R)) ℂ),
    (A * c * (dblM C)ᵀ).toCols₁ =
        A * c.submatrix id (Sum.elim (fun r => Sum.inl (Fin.castAdd S r)) (fun s => Sum.inr (Fin.castAdd R s))) * Cᵀ ∧
    (A * c * (dblM C)ᵀ).toCols₂ =
        A * c.submatrix id (Sum.elim (fun r => Sum.inr (Fin.natAdd S r)) (fun s => Sum.inl (Fin.natAdd R s))) * Cᵀ ∧
    (Jm P Q * c * Jm (R + S) (S + R)).submatrix id
        (Sum.elim (fun r => Sum.inl (Fin.castAdd S r)) (fun s => Sum.inr (Fin.castAdd R s))) =
      Jm P Q * c.submatrix id (Sum.elim (fun r => Sum.inl (Fin.castAdd S r)) (fun s => Sum.inr (Fin.castAdd R s))) *
        Jm R S ∧
    (Jm P Q * c * Jm (R + S) (S + R)).submatrix id
        (Sum.elim (fun r => Sum.inr (Fin.natAdd S r)) (fun s => Sum.inl (Fin.natAdd R s))) =
      -(Jm P Q * c.submatrix id (Sum.elim (fun r => Sum.inr (Fin.natAdd S r)) (fun s => Sum.inl (Fin.natAdd R s))) *
        Jm R S) := by
  intro α β _ P Q R S A C c
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mul_transpose_doubledSpaceFrame_toCols1, mul_submatrix_right]
  · rw [mul_transpose_doubledSpaceFrame_toCols2, mul_submatrix_right]
  · rw [jm_right_L, mul_submatrix_right]
  · rw [jm_right_R, mul_submatrix_right]

end GlobalTheory.RealLift.Dbl
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.Dieu.EtFromConn

theorem _root_.GlobalTheory.T.etaleDieudonneTranspose_comp : ∀ (p : ℕ) [Fact p.Prime] (B : Base p (fun _ _ G => G.IsConn)) (k k' k'' : Type) [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p] [PerfectRing k' p] [Field k''] [CharP k'' p] [PerfectRing k'' p] (σ : k →+* k') (τ : k' →+* k'') (υ : k →+* k'') (G'' : PDivGroup p k'') (G' : PDivGroup p k') (G : PDivGroup p k) (h'' : G''.IsEt) (h' : G'.IsEt) (h : G.IsEt) (s : SemiHom σ G' G) (t : SemiHom τ G'' G') (u : SemiHom υ G'' G), (∀ n a, u.app n a = t.app n (s.app n a)) → ∀ (l : Mod B G h) (l' : Mod B G' h') (l'' : Mod B G'' h''), IsTr B σ h' h s l l' → IsTr B τ h'' h' t l' l'' → IsTr B υ h'' h u l l'' := by
  first | exact @GlobalTheory.Dieu.EtFromConn.isTr_comp | exact GlobalTheory.Dieu.EtFromConn.isTr_comp | (intros; apply GlobalTheory.Dieu.EtFromConn.isTr_comp; all_goals assumption)
end

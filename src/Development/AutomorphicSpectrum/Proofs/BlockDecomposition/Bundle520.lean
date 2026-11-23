module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle500
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockDeterminantLaw
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviDecompOfBlockDet
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle502
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle035
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle496
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle001

@[expose] public section

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.RgEis GlobalTheory.CompanionTheory.SiegelFrame

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelFrameDet

theorem mul_fromRows_apply {R : Type} [CommRing R] {β : Type} [Fintype β] [DecidableEq β]
    (M : Matrix (β ⊕ β) (β ⊕ β) R) (C : Matrix (β ⊕ β) β R) (hC : C = Matrix.fromRows (1 : Matrix β β R) 0)
    (i : β ⊕ β) (j : β) : (M * C : Matrix (β ⊕ β) β R) i j = M i (Sum.inl j) := by
  subst hC
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem corner_conj {R : Type} [CommRing R] {β : Type} [Fintype β] [DecidableEq β]
    (B P Bi : Matrix (β ⊕ β) (β ⊕ β) R) (T Ti s : Matrix β β R) (C D : Matrix (β ⊕ β) β R)
    (hC : C = Matrix.fromRows (1 : Matrix β β R) 0)
    (hBi : Bi * B = 1) (hTi : T * Ti = 1)
    (hB : (B * C : Matrix (β ⊕ β) β R) = (D * T : Matrix (β ⊕ β) β R))
    (hP : (P * D : Matrix (β ⊕ β) β R) = (D * s : Matrix (β ⊕ β) β R)) (r c : β) :
    (Bi * P * B) (Sum.inl r) (Sum.inl c) = (Ti * s * T) r c := by
  have hD : D = B * C * Ti := by rw [hB, Matrix.mul_assoc, hTi, Matrix.mul_one]
  have key : Bi * P * B * C = C * (Ti * s * T) := by
    calc Bi * P * B * C = Bi * ((P * D) * T) := by
          rw [Matrix.mul_assoc (Bi * P) B C, hB]; simp only [Matrix.mul_assoc]
      _ = Bi * (D * s * T) := by rw [hP]
      _ = Bi * (B * C * Ti * s * T) := by rw [← hD]
      _ = (Bi * B) * C * (Ti * s * T) := by simp only [Matrix.mul_assoc]
      _ = C * (Ti * s * T) := by rw [hBi, Matrix.one_mul]
  have h1 := congrFun (congrFun key (Sum.inl r)) c
  rw [mul_fromRows_apply _ C hC] at h1
  rw [h1, hC, Matrix.fromRows_mul, Matrix.fromRows_apply_inl, Matrix.one_mul]

theorem bdet_frameEquiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (Y : Spc F E n), ∀ (χ : Chr F E) (ε : ℤˣ) (b : GL (Fin n ⊕ Fin n) E) (hb : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (t₀ : GL (Fin n) E), b.1.toCols₁ = diagCols (Fin n) * t₀.1 → ∀ (p : G2 σ Y) (t : GL (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), IsPar p t → bdet (Sum.inl '' (Set.univ : Set (Fin n))) (frameEquiv χ ε b hb p).1 = Matrix.GeneralLinearGroup.det t := by
  intro F E _ _ _ _ _ σ n Y χ ε b hb t₀ ht₀ p t hp
  obtain ⟨t₀A, ht₀A⟩ : ∃ g : GL (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      g = Matrix.GeneralLinearGroup.map (inclR (F := F) (E := E) (AF F)) t₀ := ⟨_, rfl⟩
  have hent : ∀ r c : Fin n, (((frameEquiv χ ε b hb p).1 : GL (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (Sum.inl r) (Sum.inl c) =
      ((t₀A⁻¹ * t * t₀A : GL (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) r c := by
    intro r c
    rw [frameEquiv_val]
    simp only [Units.val_mul]
    refine corner_conj _ _ _ _ _ _ _ _ rfl (Units.inv_mul _) (Units.mul_inv _) ?_ hp r c
    refine Matrix.ext fun i j => ?_
    rw [mul_fromRows_apply _ _ rfl, bA_val]
    have hij := congrFun (congrFun ht₀ i) j
    rw [Matrix.toCols₁_apply] at hij
    subst ht₀A
    show inclR (F := F) (E := E) (AF F) (b.1 i (Sum.inl j)) = _
    rw [hij]
    cases i with
    | inl r' =>
      show inclR (F := F) (E := E) (AF F)
        (∑ k, Matrix.fromRows (1 : Matrix (Fin n) (Fin n) E) 1 (Sum.inl r') k * t₀.1 k j) = _
      simp [diagCols, Matrix.mul_apply, Matrix.one_apply, Fintype.sum_sum_type]
    | inr r' =>
      show inclR (F := F) (E := E) (AF F)
        (∑ k, Matrix.fromRows (1 : Matrix (Fin n) (Fin n) E) 1 (Sum.inr r') k * t₀.1 k j) = _
      simp [diagCols, Matrix.mul_apply, Matrix.one_apply, Fintype.sum_sum_type]
  rw [GlobalTheory.CompanionTheory.RgEisLevi.bdet_inl Set.univ _ (t₀A⁻¹ * t * t₀A) hent, GlobalTheory.CompanionTheory.RgEis.bdet_univ,
    map_mul, map_mul, mul_comm, ← mul_assoc, map_inv, mul_inv_cancel, one_mul]

end GlobalTheory.CompanionTheory.SiegelFrameDet
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

variable {D : D7} {ρ p : ℕ}

theorem trA_add (a b : AE D) : trA (a + b) = trA a + trA b := map_add (Algebra.trace (AF D.host.F) (AE D)) a b

theorem pr_add_left (b₀ : HermE D ρ) (x x' y : Mx D ρ p) : pr b₀ (x + x') y = pr b₀ x y + pr b₀ x' y := by
  have h : adj (x + x') = adj x + adj x' := by
    ext i j
    simp only [adj, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, map_add (f := _)]
  simp only [pr, h]
  exact Matrix.add_mul _ _ _

theorem pr_add_right (b₀ : HermE D ρ) (x y y' : Mx D ρ p) : pr b₀ x (y + y') = pr b₀ x y + pr b₀ x y' := by
  simp only [pr]
  rw [show (HMul.hMul (b₀.1.map (incA D)) (y + y') : Mx D ρ p) = _ from Matrix.mul_add _ _ _]
  exact Matrix.mul_add _ _ _

theorem chv_add_left (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (x x' y : Mx D ρ p) :
    chv ψ b₀ (x + x') y = chv ψ b₀ x y * chv ψ b₀ x' y := by
  simp only [chv, pr_add_left, Matrix.trace_add, trA_add, AddChar.map_add_eq_mul]

theorem chv_add_right (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (x y y' : Mx D ρ p) :
    chv ψ b₀ x (y + y') = chv ψ b₀ x y * chv ψ b₀ x y' := by
  simp only [chv, pr_add_right, Matrix.trace_add, trA_add, AddChar.map_add_eq_mul]

theorem chv_norm (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ) (x y : Mx D ρ p) :
    ‖chv ψ b₀ x y‖ = 1 := hψ.2.1 _

theorem chv_zero_right (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (x : Mx D ρ p) : chv ψ b₀ x 0 = 1 := by
  have h : pr b₀ x 0 = 0 := by
    have := pr_add_right b₀ x 0 0
    simpa using this
  simp only [chv, h, Matrix.trace_zero]
  have h0 : trA (0 : AE D) = 0 := map_zero (Algebra.trace (AF D.host.F) (AE D))
  rw [h0, AddChar.map_zero_eq_one]

theorem chv_neg_right (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ) (x y : Mx D ρ p) :
    chv ψ b₀ x (-y) = conj (chv ψ b₀ x y) := by
  have h1 : chv ψ b₀ x y * chv ψ b₀ x (-y) = 1 := by
    rw [← chv_add_right, add_neg_cancel, chv_zero_right]
  have h2 : chv ψ b₀ x y * conj (chv ψ b₀ x y) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, chv_norm ψ hψ]
    simp
  exact mul_left_cancel₀ (left_ne_zero_of_mul_eq_one h1) (h1.trans h2.symm)

theorem trA_incA (t : D.host.E) :
    trA (incA D t) = algebraMap D.host.F (AF D.host.F) (Algebra.trace D.host.F D.host.E t) := by
  have h2 : Algebra.lmul (AF D.host.F) (AE D) (incA D t) =
      (Algebra.lmul D.host.F D.host.E t).baseChange (AF D.host.F) := by
    ext x
    simp [incA, inclR]
  show Algebra.trace (AF D.host.F) (AE D) (incA D t) = _
  rw [Algebra.trace_apply, h2, LinearMap.trace_baseChange, ← Algebra.trace_apply]

theorem pr_rt (b₀ : HermE D ρ) (ξ ξ' : Matrix (Fin ρ) (Fin p) D.host.E) :
    pr b₀ (rt ξ) (rt ξ') = ((ξ.map D.sp.cm.sig)ᵀ * (b₀.1 * ξ')).map (incA D) := by
  have h : adj (rt ξ) = ((ξ.map D.sp.cm.sig)ᵀ).map (incA D) := by
    ext i j
    simp only [adj, rt, Matrix.transpose_apply, Matrix.map_apply]
    rfl
  simp only [pr, h, Matrix.map_mul]

theorem chv_rt (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ)
    (ξ ξ' : Matrix (Fin ρ) (Fin p) D.host.E) : chv ψ b₀ (rt ξ) (rt ξ') = 1 := by
  have h : Matrix.trace (pr b₀ (rt ξ) (rt ξ')) = incA D (Matrix.trace ((ξ.map D.sp.cm.sig)ᵀ * (b₀.1 * ξ'))) := by
    rw [pr_rt]

    simp only [Matrix.trace, Matrix.diag_apply, Matrix.map_apply, map_sum]
  rw [chv, h, trA_incA]
  exact hψ.2.2.1 _

theorem chv_continuous (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ) :
    Continuous (fun v : Mx D ρ p × Mx D ρ p => chv ψ b₀ v.1 v.2) := by
  haveI : IsTopologicalRing (AE D) := (Formalism.IndefR.Eqv.ae_facts D).1
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have ht : Continuous (trA (D := D)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))
  have hc : Continuous (cA D) := GlobalTheory.FockCompare.ThetaCont.continuous_conj
  have ha : Continuous fun v : Mx D ρ p × Mx D ρ p => adj v.1 := by
    unfold adj
    exact ((continuous_fst.matrix_map hc)).matrix_transpose
  refine hψ.1.comp (ht.comp ?_)
  exact (ha.matrix_mul (continuous_const.matrix_mul continuous_snd)).matrix_trace

theorem chv_facts : ∀ {D : D7} {ρ p : ℕ} (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ b₀ : HermE D ρ, (∀ x x' y : Mx D ρ p, GlobalTheory.CompanionTheory.FJE.chv ψ b₀ (x + x') y = GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x y * GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x' y) ∧ (∀ x y y' : Mx D ρ p, GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x (y + y') = GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x y * GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x y') ∧ (∀ x y : Mx D ρ p, ‖GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x y‖ = 1) ∧ (∀ x y : Mx D ρ p, GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x (-y) = conj (GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x y)) ∧ (∀ ξ ξ' : Matrix (Fin ρ) (Fin p) D.host.E, GlobalTheory.CompanionTheory.FJE.chv ψ b₀ (GlobalTheory.CompanionTheory.FJE.rt ξ) (GlobalTheory.CompanionTheory.FJE.rt ξ') = 1) ∧ Continuous (fun v : Mx D ρ p × Mx D ρ p => GlobalTheory.CompanionTheory.FJE.chv ψ b₀ v.1 v.2) := by
  intro D ρ p ψ hψ b₀
  exact ⟨chv_add_left ψ b₀, chv_add_right ψ b₀, chv_norm ψ hψ b₀, chv_neg_right ψ hψ b₀, chv_rt ψ hψ b₀,
    chv_continuous ψ hψ b₀⟩

end GlobalTheory.CompanionTheory.FJE
end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Pointwise

namespace GlobalTheory.CompanionTheory.FJE.TransportInt

theorem isAddFundamentalDomain_prod {X : Type*} [AddCommGroup X] [MeasurableSpace X]
    (Γ : AddSubgroup X) {μ : Measure X} [SFinite μ] {F : Set X}
    (h : IsAddFundamentalDomain Γ F μ) :
    IsAddFundamentalDomain (Γ.prod Γ) (F ×ˢ F) (μ.prod μ) := by
  refine ⟨h.nullMeasurableSet.prod h.nullMeasurableSet, ?_, ?_⟩
  · have h1 : ∀ᵐ z ∂(μ.prod μ), ∃ g : Γ, g +ᵥ z.1 ∈ F :=
      Measure.quasiMeasurePreserving_fst.ae h.ae_covers
    have h2 : ∀ᵐ z ∂(μ.prod μ), ∃ g : Γ, g +ᵥ z.2 ∈ F :=
      Measure.quasiMeasurePreserving_snd.ae h.ae_covers
    filter_upwards [h1, h2] with z a b
    obtain ⟨g, hg⟩ := a
    obtain ⟨g', hg'⟩ := b
    exact ⟨⟨(g.1, g'.1), g.2, g'.2⟩, hg, hg'⟩
  · intro g g' hne
    have key : ∀ k : Γ.prod Γ, (k +ᵥ (F ×ˢ F)) =
        (((⟨k.1.1, k.2.1⟩ : Γ)) +ᵥ F) ×ˢ (((⟨k.1.2, k.2.2⟩ : Γ)) +ᵥ F) := by
      intro k
      ext z
      simp only [Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_prod]
      rfl
    show μ.prod μ ((g +ᵥ (F ×ˢ F)) ∩ (g' +ᵥ (F ×ˢ F))) = 0
    rw [key, key, Set.prod_inter_prod, Measure.prod_prod]
    by_cases h1 : g.1.1 = g'.1.1
    · have h2 : g.1.2 ≠ g'.1.2 := fun h2 => hne (Subtype.ext (Prod.ext h1 h2))
      have : ((⟨g.1.2, g.2.2⟩ : Γ)) ≠ ⟨g'.1.2, g'.2.2⟩ := fun h3 => h2 (congrArg Subtype.val h3)
      have h4 := h.aedisjoint this
      simp only [Function.onFun] at h4
      rw [show μ _ = 0 from h4, mul_zero]
    · have : ((⟨g.1.1, g.2.1⟩ : Γ)) ≠ ⟨g'.1.1, g'.2.1⟩ := fun h3 => h1 (congrArg Subtype.val h3)
      have h4 := h.aedisjoint this
      simp only [Function.onFun] at h4
      rw [show μ _ = 0 from h4, zero_mul]

section Generic

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem map_eq_of_fundamentalDomain (L : AddSubgroup G) [Countable L] (ν : Measure G)
    [ν.IsAddHaarMeasure] {F : Set G} (hF : IsAddFundamentalDomain L F ν) (h0 : ν F ≠ 0)
    (hT0 : ν F ≠ ∞) (T : G ≃ₜ+ G) (hr : ∀ x, T x ∈ L ↔ x ∈ L) :
    ν.map T = ν ∧ IsAddFundamentalDomain L (T '' F) ν := by
  have hemb : MeasurableEmbedding T := T.toHomeomorph.measurableEmbedding
  haveI hH : (ν.map T).IsAddHaarMeasure :=
    T.toAddEquiv.isAddHaarMeasure_map ν T.continuous T.symm.continuous
  have e := Measure.isAddLeftInvariant_eq_smul (ν.map T) ν
  have hF2 : IsAddFundamentalDomain L F (ν.map T) :=
    hF.mono (by rw [e]; exact Measure.smul_absolutelyContinuous)
  have hF3 : IsAddFundamentalDomain L (T '' F) (ν.map T) := by
    let g : L ≃ L :=
      { toFun := fun γ => ⟨T.symm γ, (hr _).1 (by rw [T.apply_symm_apply]; exact γ.2)⟩
        invFun := fun γ => ⟨T γ, (hr _).2 γ.2⟩
        left_inv := fun γ => Subtype.ext (T.apply_symm_apply _)
        right_inv := fun γ => Subtype.ext (T.symm_apply_apply _) }
    refine hF.image_of_equiv T.toEquiv ?_ g fun γ x => ?_
    · refine ⟨(T.symm.continuous.measurable : Measurable (T.symm : G → G)).aemeasurable, ?_⟩
      have : (ν.map T).map T.symm = ν := by
        have hs : Measurable (T.symm : G → G) := T.symm.continuous.measurable
        have ht : Measurable (T : G → G) := T.continuous.measurable
        rw [Measure.map_map hs ht]
        have : (T.symm ∘ T : G → G) = id := funext T.symm_apply_apply
        rw [this, Measure.map_id]
      exact this.absolutelyContinuous
    · change T (T.symm γ + x) = γ + T x
      rw [map_add (f := _), T.apply_symm_apply]
  have h3 : ν.map T F = ν.map T (T '' F) := hF2.measure_eq hF3
  have h4 : ν.map T (T '' F) = ν F := by
    rw [hemb.map_apply, Set.preimage_image_eq _ T.injective]
  have hc : Measure.addHaarScalarFactor (ν.map T) ν = 1 := by
    have h5 : ν.map T F = ν F := h3.trans h4
    rw [e, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h5
    have h6 := (ENNReal.mul_eq_right h0 hT0).1 h5
    simpa using h6
  have hm : ν.map T = ν := by rw [e, hc, one_smul]
  refine ⟨hm, ?_⟩
  rwa [hm] at hF3

theorem setIntegral_comp_eq (L : AddSubgroup G) [Countable L] (ν : Measure G)
    [ν.IsAddHaarMeasure] {F : Set G} (hF : IsAddFundamentalDomain L F ν) (h0 : ν F ≠ 0)
    (hT0 : ν F ≠ ∞) (T : G ≃ₜ+ G) (hr : ∀ x, T x ∈ L ↔ x ∈ L) (A : G → ℂ)
    (hA : ∀ γ ∈ L, ∀ v, A (γ + v) = A v) :
    ∫ v in F, A (T v) ∂ν = ∫ v in F, A v ∂ν := by
  obtain ⟨hm, hF3⟩ := map_eq_of_fundamentalDomain L ν hF h0 hT0 T hr
  have hemb : MeasurableEmbedding T := T.toHomeomorph.measurableEmbedding
  have h1 : ∫ v in T '' F, A v ∂(ν.map T) = ∫ v in F, A (T v) ∂ν := by
    rw [hemb.setIntegral_map, Set.preimage_image_eq _ T.injective]
  rw [← h1, hm]
  exact hF3.setIntegral_eq hF fun γ a => hA γ γ.2 a

end Generic

end GlobalTheory.CompanionTheory.FJE.TransportInt

namespace GlobalTheory.CompanionTheory.FJE.TransportInt

theorem transport_int : ∀ {D : D7} {ρ p : ℕ} (m : Meas D ρ p) (T : (Mx D ρ p × Mx D ρ p) ≃ₜ+ (Mx D ρ p × Mx D ρ p)), (∀ ξ₁ ξ₂ : Matrix (Fin ρ) (Fin p) D.host.E, ∃ ξ₁' ξ₂' : Matrix (Fin ρ) (Fin p) D.host.E, T (GlobalTheory.CompanionTheory.FJE.rt ξ₁, GlobalTheory.CompanionTheory.FJE.rt ξ₂) = (GlobalTheory.CompanionTheory.FJE.rt ξ₁', GlobalTheory.CompanionTheory.FJE.rt ξ₂')) → (∀ ξ₁ ξ₂ : Matrix (Fin ρ) (Fin p) D.host.E, ∃ ξ₁' ξ₂' : Matrix (Fin ρ) (Fin p) D.host.E, T.symm (GlobalTheory.CompanionTheory.FJE.rt ξ₁, GlobalTheory.CompanionTheory.FJE.rt ξ₂) = (GlobalTheory.CompanionTheory.FJE.rt ξ₁', GlobalTheory.CompanionTheory.FJE.rt ξ₂')) → ∀ A : Mx D ρ p × Mx D ρ p → ℂ, (∀ (ξ₁ ξ₂ : Matrix (Fin ρ) (Fin p) D.host.E) v, A (v + (GlobalTheory.CompanionTheory.FJE.rt ξ₁, GlobalTheory.CompanionTheory.FJE.rt ξ₂)) = A v) → ∫ v in m.𝓕 ×ˢ m.𝓕, A (T v) ∂(m.μ.prod m.μ) = ∫ v in m.𝓕 ×ˢ m.𝓕, A v ∂(m.μ.prod m.μ) := by
  intro D ρ p m T h1 h2 A hA
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D ρ p
  haveI : BorelSpace (Mx D ρ p) := ⟨rfl⟩
  haveI : Countable (ratMx D ρ p) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨hμ, hF, hone⟩ := m.hμ
  haveI : Countable ((ratMx D ρ p).prod (ratMx D ρ p)) :=
    (Function.Injective.countable (f := fun g : (ratMx D ρ p).prod (ratMx D ρ p) =>
      ((⟨g.1.1, g.2.1⟩ : ratMx D ρ p), (⟨g.1.2, g.2.2⟩ : ratMx D ρ p))) fun a b h =>
        Subtype.ext (Prod.ext (congrArg (fun z => z.1.1) h) (congrArg (fun z => z.2.1) h)))
  have hv : m.μ.prod m.μ (m.𝓕 ×ˢ m.𝓕) = 1 := by rw [Measure.prod_prod, hone, one_mul]
  have mem : ∀ z : Mx D ρ p × Mx D ρ p, z ∈ (ratMx D ρ p).prod (ratMx D ρ p) ↔
      ∃ ξ₁ ξ₂ : Matrix (Fin ρ) (Fin p) D.host.E, z = (GlobalTheory.CompanionTheory.FJE.rt ξ₁, GlobalTheory.CompanionTheory.FJE.rt ξ₂) := by
    rintro ⟨a, b⟩
    constructor
    · rintro ⟨⟨ξ₁, h₁⟩, ⟨ξ₂, h₂⟩⟩
      exact ⟨ξ₁, ξ₂, Prod.ext h₁.symm h₂.symm⟩
    · rintro ⟨ξ₁, ξ₂, h⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact ⟨⟨ξ₁, rfl⟩, ⟨ξ₂, rfl⟩⟩
  have hr : ∀ x, T x ∈ (ratMx D ρ p).prod (ratMx D ρ p) ↔ x ∈ (ratMx D ρ p).prod (ratMx D ρ p) := by
    intro x
    constructor
    · intro h
      obtain ⟨ξ₁, ξ₂, e⟩ := (mem _).1 h
      obtain ⟨ξ₁', ξ₂', e'⟩ := h2 ξ₁ ξ₂
      refine (mem _).2 ⟨ξ₁', ξ₂', ?_⟩
      rw [← e', ← e, T.symm_apply_apply]
    · intro h
      obtain ⟨ξ₁, ξ₂, e⟩ := (mem _).1 h
      obtain ⟨ξ₁', ξ₂', e'⟩ := h1 ξ₁ ξ₂
      exact (mem _).2 ⟨ξ₁', ξ₂', by rw [e, e']⟩
  refine setIntegral_comp_eq _ (m.μ.prod m.μ) (isAddFundamentalDomain_prod _ hF)
    (by rw [hv]; exact one_ne_zero) (by rw [hv]; exact ENNReal.one_ne_top) T hr A ?_
  intro γ hγ v
  obtain ⟨ξ₁, ξ₂, e⟩ := (mem _).1 hγ
  rw [e, add_comm]
  exact hA ξ₁ ξ₂ v

end GlobalTheory.CompanionTheory.FJE.TransportInt
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.PcFc

namespace GlobalTheory.CompanionTheory.PcFc

theorem rank_fromBlocks_ge {K : Type*} [Field K] {ρ p : ℕ} (a : Matrix (Fin ρ) (Fin ρ) K)
    (ha : a.det ≠ 0) (c : Matrix (Fin p) (Fin p) K) (hc : c ≠ 0) :
    ρ + 1 ≤ (Matrix.fromBlocks a 0 0 c).rank := by
  classical
  obtain ⟨i, j, hij⟩ : ∃ i j, c i j ≠ 0 := by
    by_contra h
    push Not at h
    exact hc (Matrix.ext h)
  have hsub : (Matrix.fromBlocks a 0 0 c).submatrix
      (Sum.map id fun _ : Unit => i) (Sum.map id fun _ : Unit => j) =
      Matrix.fromBlocks a 0 0 (Matrix.of fun _ _ : Unit => c i j) := by
    ext x y
    rcases x with x | x <;> rcases y with y | y <;> rfl
  have hdet : (Matrix.fromBlocks a 0 0
      (Matrix.of fun _ _ : Unit => c i j)).det ≠ 0 := by
    rw [Matrix.det_fromBlocks_zero₂₁]
    simpa using ⟨ha, hij⟩
  have hrank := Matrix.rank_of_isUnit _
    ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet))
  have hle := Matrix.rank_submatrix_le (Matrix.fromBlocks a 0 0 c)
    (Sum.map id fun _ : Unit => i) (Sum.map id fun _ : Unit => j)
  rw [hsub, hrank] at hle
  simpa using hle

theorem rank_dsum_ge : ∀ {D : D7} {n ρ p : ℕ} (hn : ρ + p = n) (b₀ : HermE D ρ), b₀.1.det ≠ 0 → ∀ β' : HermE D p, β'.1 ≠ 0 → ρ + 1 ≤ (dsum hn b₀ β').1.rank := by
  intro D n ρ p hn b₀ hb β' hβ
  have h := rank_fromBlocks_ge b₀.1 hb β'.1 hβ
  have e : (dsum hn b₀ β').1.rank = (Matrix.fromBlocks b₀.1 0 0 β'.1).rank :=
    Matrix.rank_submatrix _ (finSumFinEquiv.trans (finCongr hn)).symm
      (finSumFinEquiv.trans (finCongr hn)).symm
  rw [e]
  exact h

end GlobalTheory.CompanionTheory.PcFc
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.PcFc
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.PcFc

variable {D : D7} {n ρ p : ℕ}

theorem bT_add_right (hn : ρ + p = n) (z : hermA D ρ) (x : Mx D ρ p) (γ y : hermA D p) :
    bT hn z x (γ + y) = bT hn 0 0 γ + bT hn z x y := by
  apply Subtype.ext
  have h0 : adj (0 : Mx D ρ p) = 0 := by
    ext i j
    simp [adj]
  ext i j
  simp only [bT, AddSubgroup.coe_add, AddSubgroup.coe_zero, h0, Matrix.add_apply, bl, Matrix.submatrix_apply]
  rcases (finSumFinEquiv.trans (finCongr hn)).symm i with i' | i' <;>
    rcases (finSumFinEquiv.trans (finCongr hn)).symm j with j' | j' <;>
    simp

theorem bT_zero_mem_ratHerm (hn : ρ + p = n) {γ : hermA D p} (hγ : γ ∈ ratHerm D p) :
    bT hn 0 0 γ ∈ ratHerm D n := by
  obtain ⟨η, hη⟩ : γ.1 ∈ ratMx D p p := hγ
  have h0 : adj (0 : Mx D ρ p) = 0 := by
    ext i j
    simp [adj]
  refine (show (bT hn 0 0 γ : hermA D n).1 ∈ ratMx D n n from ⟨bl hn 0 0 0 η, ?_⟩)
  ext i j
  have hij : ∀ a b, (incA D) (η a b) = γ.1 a b := fun a b => by
    rw [← hη]
    rfl
  simp only [bT, AddSubgroup.coe_zero, h0, bl, AddMonoidHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply,
    RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe]
  rcases (finSumFinEquiv.trans (finCongr hn)).symm i with i' | i' <;>
    rcases (finSumFinEquiv.trans (finCongr hn)).symm j with j' | j' <;>
    simp [hij]

theorem isPer_pm {D : D7} {n ρ p : ℕ} (hn : ρ + p = n) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ)
    (Φ : hermA D n → ℂ) (hΦ : IsPer Φ) : IsPer (pm hn m ψ b₀ Φ) := by
  intro γ hγ y
  have h : ∀ x z, Φ (bT hn z x (γ + y)) = Φ (bT hn z x y) := fun x z => by
    rw [bT_add_right]
    exact hΦ _ (bT_zero_mem_ratHerm hn hγ) _
  simp only [pm, h]

end GlobalTheory.CompanionTheory.PcFc
end
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.nondegenerate_of_whittaker : PositivityTheory.PfSWUS.NDOfWhit := by
  first | exact @GlobalTheory.CompanionTheory.SWGlue.ndOfWhit | exact GlobalTheory.CompanionTheory.SWGlue.ndOfWhit | (intros; apply GlobalTheory.CompanionTheory.SWGlue.ndOfWhit <;> assumption)
end
end

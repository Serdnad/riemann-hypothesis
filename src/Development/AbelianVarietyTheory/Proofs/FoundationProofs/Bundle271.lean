module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle132
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle189
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle105
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle170
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle128
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle262
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle084
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.NumberTheory.LSeries.Basic
public import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle063
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle035
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle210
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle243
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle255
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle227
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle234
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle263
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle235
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle251
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle264
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle256
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle266
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle265
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem gal_sl_io_of_cong :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (a : GlobalTheory.FN.ring ε.range) (N w : ℕ), 0 < N → Lv ε.range N w a → ∀ (s : Ω ≃ₐ[ℚ] Ω) (d : ℤ), s (eOm ε (1 / N)) = eOm ε (1 / N) ^ d → ∀ γ γ' : SL(2, ℤ), Cong N d γ γ' → T.gal s (T.sl (ofSL γ) (T.io a)) = T.sl (ofSL γ') (T.gal s (T.io a)) := by
  intro Ω _ _ _ ε T a N w hN hLv s d hs γ γ' hC
  haveI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_complex_ringEquiv_extending_subfield_aut Ω ε s.toRingEquiv
  have hg' : ∀ x, g (ε x) = ε (s x) := hg
  obtain ⟨u, hu, hZ⟩ := (GlobalTheory.T.galois_exponent_rootOfUnity_expTwoPiI Ω ε s N hN).2 d hs
  have hE : ∀ x ∈ ε.range, g x ∈ ε.range := by
    rintro _ ⟨y, rfl⟩
    exact ⟨s y, (hg' y).symm⟩
  obtain ⟨f', hf'L, hf'C⟩ := GlobalTheory.T.levelN_function_galois_conj_qExpansion g ε.range N u w (a : ℍ → ℂ) hE (hZ g hg') hLv
  let a' : GlobalTheory.FN.ring ε.range := ⟨f', mem_ring_of_inR ⟨N, w, hN, hf'L⟩⟩
  obtain ⟨hext, hcmp, hexpinj, -⟩ := GlobalTheory.T.fractionField_ext_closure_injective Ω ε T
  obtain ⟨-, -, hSL, -⟩ := GlobalTheory.T.cmp_mul_ofSL_and_up_cmp_eq_up_mob

  have key : ∀ γ γ' : SL(2, ℤ), dg u * redGL N γ' = redGL N γ * dg u →
      T.gal s (T.sl (ofSL γ) (T.io a)) = T.sl (ofSL γ') (T.io a') := by
    intro γ γ' hM
    obtain ⟨b, hb, hbio⟩ := hcmp (ofSL γ) a
    obtain ⟨b', hb', hb'io⟩ := hcmp (ofSL γ') a'
    rw [hbio, hb'io]
    apply hexpinj
    ext r
    rw [T.gal_exp]
    have hb1 : (b : ℍ → ℂ) = fun τ => (a : ℍ → ℂ) (γ • τ) := by rw [hb, hSL]
    have hb2 : (b' : ℍ → ℂ) = fun τ => f' (γ' • τ) := by rw [hb', hSL]
    refine Eq.symm ?_
    refine GlobalTheory.T.cuspExpansion_coeff_conj_of_qExpansion_conj Ω ε s.toRingEquiv.toRingHom g N w b b' _ _ hg' hN ?_ ?_ (T.exp_io b) (T.exp_io b') r
    · rw [hb1]; exact hLv.2 γ
    · rw [hb1, hb2]; exact hf'C γ γ' hM
  have h1 : T.gal s (T.io a) = T.io a' := by
    have hM1 : dg u * redGL N 1 = redGL N 1 * dg u := by simp [redGL]
    have := key 1 1 hM1
    obtain ⟨c, hc, hcio⟩ := hcmp (ofSL 1) a
    obtain ⟨c', hc', hc'io⟩ := hcmp (ofSL 1) a'
    have e1 : c = a := Subtype.ext (by rw [hc, hSL]; funext τ; simp)
    have e2 : c' = a' := Subtype.ext (by rw [hc', hSL]; funext τ; simp [a'])
    rw [hcio, hc'io, e1, e2] at this
    exact this
  rw [h1]
  exact key γ γ' ((GlobalTheory.T.slTwoDiagConjCongruence_iff_diagOneUnit_matrix_eq N d u hu γ γ').mp hC)

end GlobalTheory.FN
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.rankin_unfolding_petersson_eisensteinLatticeSum : ∀ (e L N : ℕ) (ε : DirichletCharacter ℂ N) (φ : DirichletCharacter ℂ L) (χ : ℤ → ℂ) (ρ : ℍ → ℝ) (h b : ℕ → ℂ) (s : ℝ), 1 ≤ e → 0 < s → 0 < L → N ∣ L → Wt L ρ → φ ≠ 1 → CF (2 * e + 1) L (ch ε) h → MF e L χ b → (∀ d : ℤ, IsCoprime d L → χ d = ch φ d * ch ε d) → (∃ C : ℝ, ∀ n, n ≠ 0 → ‖b n‖ ≤ C * n.divisors.card * (n : ℝ) ^ (e - 1)) → pet (2 * e + 1) ρ (qs h) (fun τ => qs b τ * lat (e + 1) s L (0, 1) (latF L (fun _ => 1) φ) τ * ((τ.im ^ s : ℝ) : ℂ)) = LSeries (fun n => φ n) ((e + 1 : ℕ) + 2 * s) * (((Real.Gamma (2 * (e : ℝ) + s) / (4 * π) ^ (2 * (e : ℝ) + s) : ℝ) : ℂ) * LSeries (fun n => conj (h n) * b n) ((2 * (e : ℝ) + s : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.EisM.rankin_unfold | exact GlobalTheory.EisM.rankin_unfold | (intros; apply GlobalTheory.EisM.rankin_unfold <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory NumberField GlobalTheory.Mem.Vol Matrix Topology

namespace GlobalTheory.Mem.Vol.Scale

variable {n P Q : ℕ} {ε : Fin n → Bool}

def Sorts (ε : Fin n → Bool) (e : Fin P ⊕ Fin Q ≃ Fin n) : Prop :=
  (∀ i, ε (e (Sum.inl i)) = true) ∧ ∀ j, ε (e (Sum.inr j)) = false

theorem Sorts.reindex_Jpq {e : Fin P ⊕ Fin Q ≃ Fin n} (h : Sorts ε e) :
    Matrix.reindex e e (Formalism.UG.Jpq P Q) = Formalism.REAL.Jm ε := by
  ext i j
  obtain ⟨a, rfl⟩ := e.surjective i
  obtain ⟨b, rfl⟩ := e.surjective j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Formalism.REAL.Jm,
    Matrix.diagonal_apply, EmbeddingLike.apply_eq_iff_eq, Formalism.UG.Jpq]
  rcases a with a | a <;> rcases b with b | b <;> simp [Matrix.one_apply, h.1, h.2]
  split_ifs <;> simp

theorem Sorts.card_true {e : Fin P ⊕ Fin Q ≃ Fin n} (h : Sorts ε e) : Nat.card {a // ε a = true} = P := by
  have : Function.Bijective fun i : Fin P => (⟨e (Sum.inl i), h.1 i⟩ : {a // ε a = true}) := by
    refine ⟨fun i j hij => Sum.inl_injective (e.injective (congrArg Subtype.val hij)), ?_⟩
    rintro ⟨a, ha⟩
    obtain ⟨b | b, rfl⟩ := e.surjective a
    · exact ⟨b, rfl⟩
    · rw [h.2] at ha; cases ha
  rw [← Nat.card_eq_of_bijective _ this]; simp

theorem Sorts.add_eq (e : Fin P ⊕ Fin Q ≃ Fin n) : P + Q = n := by
  simpa using Fintype.card_congr e

theorem exists_sorts (ε : Fin n → Bool) : ∃ (P Q : ℕ) (e : Fin P ⊕ Fin Q ≃ Fin n), Sorts ε e := by
  refine ⟨_, _, (Equiv.sumCongr (Fintype.equivFin {a // ε a = true}).symm
    (Fintype.equivFin {a // ¬ ε a = true}).symm).trans (Equiv.sumCompl fun a => ε a = true), fun i => ?_, fun j => ?_⟩
  · exact ((Fintype.equivFin {a // ε a = true}).symm i).2
  · exact Bool.eq_false_iff.2 ((Fintype.equivFin {a // ¬ ε a = true}).symm j).2

def reindexUnits (e : Fin P ⊕ Fin Q ≃ Fin n) :
    GL (Fin P ⊕ Fin Q) ℂ ≃ₜ* (Matrix (Fin n) (Fin n) ℂ)ˣ where
  toMulEquiv := Units.mapEquiv (Matrix.reindexAlgEquiv ℂ ℂ e).toMulEquiv
  continuous_toFun := Units.continuous_map
    (f := ((Matrix.reindexAlgEquiv ℂ ℂ e).toMulEquiv.toMonoidHom))
    (continuous_id.matrix_reindex _ _)
  continuous_invFun := Units.continuous_map
    (f := ((Matrix.reindexAlgEquiv ℂ ℂ e).toMulEquiv.symm.toMonoidHom))
    ((continuous_id.matrix_reindex e.symm e.symm).congr fun _ => rfl)

theorem reindexUnits_val (e : Fin P ⊕ Fin Q ≃ Fin n) (g : GL (Fin P ⊕ Fin Q) ℂ) :
    (reindexUnits e g : Matrix (Fin n) (Fin n) ℂ) =
      Matrix.reindex e e (g : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) := rfl

theorem Sorts.mem_iff {e : Fin P ⊕ Fin Q ≃ Fin n} (h : Sorts ε e) (g : GL (Fin P ⊕ Fin Q) ℂ) :
    reindexUnits e g ∈ Formalism.REAL.UJ ε ↔ g ∈ Formalism.UG.Upq P Q := by
  change Formalism.REAL.inUJ ε (reindexUnits e g : Matrix (Fin n) (Fin n) ℂ) ↔
    (g : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ).conjTranspose * Formalism.UG.Jpq P Q *
      (g : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) = Formalism.UG.Jpq P Q
  rw [Formalism.REAL.inUJ, reindexUnits_val, ← h.reindex_Jpq, Matrix.conjTranspose_reindex]
  rw [← (Matrix.reindex (α := ℂ) e e).injective.eq_iff]
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]

def Sorts.equiv {e : Fin P ⊕ Fin Q ≃ Fin n} (h : Sorts ε e) : UpqT P Q ≃ₜ* Formalism.REAL.UJ ε where
  toFun g := ⟨reindexUnits e (g : Formalism.UG.Upq P Q).1, (h.mem_iff _).2 (g : Formalism.UG.Upq P Q).2⟩
  invFun k := (⟨(reindexUnits e).symm k.1, (h.mem_iff _).1 (by simpa using k.2)⟩ : Formalism.UG.Upq P Q)
  left_inv g := Subtype.ext ((reindexUnits e).symm_apply_apply _)
  right_inv k := Subtype.ext ((reindexUnits e).apply_symm_apply _)
  map_mul' g k := Subtype.ext (map_mul (reindexUnits e) _ _)
  continuous_toFun := ((reindexUnits e).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((reindexUnits e).symm.continuous.comp continuous_subtype_val).subtype_mk _

theorem Sorts.umat_equiv {e : Fin P ⊕ Fin Q ≃ Fin n} (h : Sorts ε e) (g : UpqT P Q) :
    umat (h.equiv g) = Matrix.reindex e e (UpqT.mat g) := rfl

theorem umat_injective : Function.Injective (umat : Formalism.REAL.UJ ε → _) :=
  fun _ _ h => Subtype.ext (Units.ext h)

theorem Sorts.set_eq {e : Fin P ⊕ Fin Q ≃ Fin n} (h : Sorts ε e) (A : Set (Formalism.REAL.UJ ε)) :
    {g | ∃ a ∈ A, umat a = Matrix.reindex e e (UpqT.mat g)} = h.equiv ⁻¹' A := by
  ext g
  constructor
  · rintro ⟨a, ha, hg⟩
    rw [← h.umat_equiv] at hg
    rw [Set.mem_preimage, ← umat_injective hg]
    exact ha
  · intro hg
    exact ⟨_, hg, rfl⟩

theorem Sorts.exists_conj {e e' : Fin P ⊕ Fin Q ≃ Fin n} (h : Sorts ε e) (h' : Sorts ε e') :
    ∃ u : UpqT P Q, ∀ g, h'.equiv g = h.equiv (u * g * u⁻¹) := by
  set σ : Fin P ⊕ Fin Q ≃ Fin P ⊕ Fin Q := e.trans e'.symm with hσ
  have hJ : (Formalism.UG.Jpq P Q).submatrix σ σ = Formalism.UG.Jpq P Q := by
    apply (Matrix.reindex (α := ℂ) e e).injective
    rw [h.reindex_Jpq, ← h'.reindex_Jpq]
    ext i j
    simp [hσ]
  have hmem : (1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ).submatrix σ id ∈
      Set.range (UpqT.mat (P := P) (Q := Q)) := by
    rw [GlobalTheory.UpqTopology.range_mat]
    change _ = _
    rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one]
    conv_lhs => rw [← hJ]
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
    simp
  obtain ⟨u, hu⟩ := hmem
  refine ⟨u, fun g => ?_⟩
  rw [← h.equiv.symm_apply_eq, eq_mul_inv_iff_mul_eq]
  apply GlobalTheory.UpqTopology.isClosedEmbedding_mat.injective
  have h1 : UpqT.mat (h.equiv.symm (h'.equiv g)) = (UpqT.mat g).submatrix σ σ := by
    apply (Matrix.reindex (α := ℂ) e e).injective
    rw [← h.umat_equiv, h.equiv.apply_symm_apply, h'.umat_equiv]
    ext i j
    simp [hσ]
  change UpqT.mat (h.equiv.symm (h'.equiv g)) * UpqT.mat u = UpqT.mat u * UpqT.mat g
  rw [h1, hu, Matrix.submatrix_mul_equiv, Matrix.mul_one]
  have := Matrix.submatrix_mul_equiv (1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) (UpqT.mat g) σ
    (Equiv.refl _) id
  simpa using this.symm

theorem Sorts.measurable_equiv {e : Fin P ⊕ Fin Q ≃ Fin n} (h : Sorts ε e) : Measurable h.equiv := by
  haveI : BorelSpace (UpqT P Q) := ⟨rfl⟩
  exact h.equiv.continuous.measurable

theorem Sorts.map_eq (cd : CDHaar) {P' Q' : ℕ} {e : Fin P ⊕ Fin Q ≃ Fin n} {e' : Fin P' ⊕ Fin Q' ≃ Fin n}
    (h : Sorts ε e) (h' : Sorts ε e') : (cd.cd P' Q').map h'.equiv = (cd.cd P Q).map h.equiv := by
  obtain rfl : P = P' := h.card_true.symm.trans h'.card_true
  obtain rfl : Q = Q' := by
    have h1 := Sorts.add_eq e
    have h2 := Sorts.add_eq e'
    omega
  haveI : IsTopologicalGroup (UpqT P Q) := inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq P Q))
  haveI : BorelSpace (UpqT P Q) := ⟨rfl⟩
  haveI := cd.haar P Q
  haveI := GlobalTheory.UpqHaarRight.isMulRightInvariant P Q _ (cd.haar P Q)
  obtain ⟨u, hu⟩ := h.exists_conj h'
  have : (h'.equiv : UpqT P Q → Formalism.REAL.UJ ε) = h.equiv ∘ (fun g => g * u⁻¹) ∘ fun g => u * g := funext hu
  rw [this, ← Measure.map_map h.measurable_equiv ((measurable_mul_const _).comp (measurable_const_mul _)),
    ← Measure.map_map (measurable_mul_const _) (measurable_const_mul _), map_mul_left_eq_self,
    map_mul_right_eq_self]

theorem Sorts.exists_scale (cd : CDHaar) {e : Fin P ⊕ Fin Q ≃ Fin n} (h : Sorts ε e) :
    ∃ c : NNReal, 0 < c ∧ (cd.cd P Q).map h.equiv = (c : ENNReal) • Formalism.REAL.muG ε := by
  haveI : IsTopologicalGroup (UpqT P Q) := inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq P Q))
  haveI : BorelSpace (UpqT P Q) := ⟨rfl⟩
  haveI := cd.haar P Q
  haveI : ((cd.cd P Q).map h.equiv).IsHaarMeasure := h.equiv.isHaarMeasure_map _
  exact ⟨_, Measure.haarScalarFactor_pos_of_isHaarMeasure _ _,
    Measure.isMulLeftInvariant_eq_smul ((cd.cd P Q).map h.equiv) (Formalism.REAL.muG ε)⟩

theorem exists_cdScaleIs (cd : CDHaar) :
    ∃ sc : ∀ n : ℕ, (Fin n → Bool) → NNReal, (∀ n ε, 0 < sc n ε) ∧ CdScaleIs cd sc := by
  choose P Q e he using fun (n : ℕ) (ε : Fin n → Bool) => exists_sorts ε
  choose sc hpos hsc using fun (n : ℕ) (ε : Fin n → Bool) => (he n ε).exists_scale cd
  refine ⟨sc, hpos, fun n ε P' Q' e' h1 h2 A hA => ?_⟩
  have h' : Sorts ε e' := ⟨h1, h2⟩
  rw [h'.set_eq, ← Measure.map_apply h'.measurable_equiv hA, (he n ε).map_eq cd h', hsc]

theorem cdScaleIs_trueScale : ∀ cd : CDHaar, CdScaleIs cd (trueScale cd) := by
  intro cd
  unfold trueScale
  rw [dite_eq_left (exists_cdScaleIs cd)]
  exact (Classical.choose_spec (exists_cdScaleIs cd)).2

theorem cdScaleIs_unique (cd : CDHaar) {sc sc' : ∀ n : ℕ, (Fin n → Bool) → NNReal}
    (h : CdScaleIs cd sc) (h' : CdScaleIs cd sc') : sc = sc' := by
  funext n ε
  obtain ⟨P, Q, e, he⟩ := exists_sorts ε
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts (Formalism.REAL.UJ ε)) := inferInstance
  have hm : MeasurableSet (K : Set (Formalism.REAL.UJ ε)) := K.isCompact.measurableSet
  have h0 : Formalism.REAL.muG ε K ≠ 0 := (Measure.measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
  have ht : Formalism.REAL.muG ε K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have := (h n ε P Q e he.1 he.2 K hm).trans (h' n ε P Q e he.1 he.2 K hm).symm
  rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul] at this
  exact ENNReal.coe_injective ((ENNReal.mul_left_inj h0 ht).1 this)

end GlobalTheory.Mem.Vol.Scale
end
end

section

open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical

namespace GlobalTheory.UnitaryTheta.Graph

theorem integral_kerSum_graph_eq : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (H : Sesq V), IsPosHerm H → ∀ a : V ≃ₗ[ℂ] V, (∀ z w, H (a z) (a w) = H z w) → LinearMap.det (1 - (a : V →ₗ[ℂ] V)) ≠ 0 → ∀ (B : V →ₗ[ℂ] V), (∀ x, B x - a (B x) = x) → ∀ (Λ Λ' : AddSubgroup V) [DiscreteTopology Λ], Λ' ≤ Λ → (∀ y ∈ Λ', a y ∈ Λ) → ∀ α : V → ℂ, IsSemichar H Λ α → (∀ y ∈ Λ', α (a y) = α y) → ∀ Fd : Set V, IsAddFundamentalDomain Λ' Fd μ → ∀ (M : Type) [Fintype M] (s : M → V), (∀ m, s m ∈ Λ) → (∀ x ∈ Λ, ∃! p : M × Λ', x = s p.1 - ((p.2 : V) - a p.2)) → ∃ κ : ℝ, 0 < κ ∧ ∫ z in Fd, kerSum H Λ α z (a z) * cexp (-(π : ℂ) * H z z) ∂μ = κ / LinearMap.det (1 - (a : V →ₗ[ℂ] V)) * ∑ m, α (s m) * cexp (-((π : ℂ) * I) * ((H (B (s m)) (s m)).im : ℂ)) := by
  intro V _ _ _ _ _ μ _ H hH a ha hdet B hB1 Λ Λ' _ hle haΛ α hα hαa Fd hFd M _ s hs huniq
  haveI : ProperSpace V := FiniteDimensional.proper ℂ V
  haveI : Countable Λ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : Countable Λ' := (AddSubgroup.inclusion_injective hle).countable
  obtain ⟨κ, hκ, hg⟩ := integral_gaussian_unitary_pos V μ H hH a ha hdet
  refine ⟨κ, hκ, ?_⟩
  have hint : ∀ x, Integrable (term H a α x) μ := fun x => by
    have : term H a α x = _ := funext fun z => term_eq H a ha α x (B x) z (hB1 x)
    rw [this]
    exact (hg (B x) _).1.const_mul _
  have hval : ∀ x, ∫ z, term H a α x z ∂μ = κ / LinearMap.det (1 - (a : V →ₗ[ℂ] V)) *
      (α x * cexp (-((π : ℂ) * I) * ((H (B x) x).im : ℂ))) := fun x => by
    simp only [fun z => term_eq H a ha α x (B x) z (hB1 x)]
    rw [integral_const_mul, (hg (B x) _).2, ← value_eq H hH a ha x (B x) (hB1 x)]
    ring
  let f : M × Λ' → Λ := fun p => ⟨s p.1 - ((p.2 : V) - a p.2),
    Λ.sub_mem (hs _) (Λ.sub_mem (hle p.2.2) (haΛ _ p.2.2))⟩
  have hf : Function.Bijective f := by
    constructor
    · intro p q hpq
      exact (huniq _ (f p).2).unique rfl (congrArg Subtype.val hpq)
    · intro x
      obtain ⟨p, hp, -⟩ := huniq x x.2
      exact ⟨p, Subtype.ext hp.symm⟩
  have hsum : ∀ z, kerSum H Λ α z (a z) * cexp (-(π : ℂ) * H z z) =
      ∑ m, ∑' y : Λ', term H a α (s m) (z + y) := fun z => by
    have h1 : Summable (fun x : Λ => term H a α x z) :=
      ((GlobalTheory.UnitaryTheta.KerSum.kerSum_spec V H hH Λ α hα).1 (a z) z).mul_right _
    have h2 := (Equiv.ofBijective f hf).summable_iff.2 h1
    rw [kerSum, ← tsum_mul_right]
    change ∑' x : Λ, term H a α x z = _
    rw [← (Equiv.ofBijective f hf).tsum_eq]
    refine (h2.tsum_prod).trans ?_
    rw [tsum_fintype]
    refine Finset.sum_congr rfl fun m _ => tsum_congr fun y => ?_
    exact term_shift H hH a ha Λ α hα (s m) y z (hs m) (hle y.2) (haΛ _ y.2) (hαa _ y.2)
  have hu := fun m => GlobalTheory.integral_unfold_fundamentalDomain V μ Λ' Fd hFd _ (hint (s m))
  simp only [hsum]
  rw [integral_finsetSum _ (fun m _ => (hu m).1)]
  simp only [fun m => (hu m).2, hval]
  rw [← Finset.mul_sum]

end GlobalTheory.UnitaryTheta.Graph
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

theorem _root_.GlobalTheory.T.heisenbergRelativeIndex_completedStandard_ne_zero : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' m : ℕ), 0 < m → ∀ T : Submodule (𝓞 D.host.E) (XA D N N'), (∀ ζ ∈ T, m • ζ ∈ latA D cc N N') → idx (latA D cc N N') T ≠ 0 := by
  first | exact @GlobalTheory.FinWeil.idx_latA_ne_zero | exact GlobalTheory.FinWeil.idx_latA_ne_zero | (intros; apply GlobalTheory.FinWeil.idx_latA_ne_zero <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui GlobalTheory.InertParity
open scoped BigOperators Pointwise

theorem _root_.GlobalTheory.T.finite_module_sign_eq_neg_one_pow_length : ∀ (D : D7) (M : Type) [AddCommGroup M] [Module (𝓞 D.host.E) M] [Finite M], Ev D (Nat.card M) ∧ ((∀ q : ℕ, q.Prime → q ∣ Nat.card M → InertQ D q) → sgn D (Nat.card M) = (-1 : ℂ) ^ (Module.length (𝓞 D.host.E) M).toNat) := by
  first | exact @GlobalTheory.InertParity.FiniteOrder.ev_card_and_sgn_card | exact GlobalTheory.InertParity.FiniteOrder.ev_card_and_sgn_card | (intros; apply GlobalTheory.InertParity.FiniteOrder.ev_card_and_sgn_card <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries

noncomputable section

namespace GlobalTheory.DerivTransport

theorem taylorCoeffAtZero_deriv (F : ℂ → ℂ) (n : ℕ) :
    coef1 (deriv F) n = ((n : ℂ) + 1) * coef1 F (n + 1) := by
  simp only [coef1]
  rw [← iteratedDeriv_succ', Nat.factorial_succ]
  have h1 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have h2 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  push_cast
  field_simp

theorem algEnt_deriv {F : ℂ → ℂ} (hF : AlgEnt F) : AlgEnt (deriv F) := by
  refine ⟨?_, fun n => ?_⟩
  · exact (contDiff_infty_iff_deriv.1 (hF.1.contDiff)).2.differentiable (by simp)
  · rw [taylorCoeffAtZero_deriv]
    exact mul_mem (add_mem (natCast_mem _ n) (one_mem _)) (hF.2 _)

variable {p : ℕ} [Fact p.Prime]

theorem padicTaylorSeries_deriv_eq_derivative (lam : Qbar →+* ℂ_[p]) {F : ℂ → ℂ} (hF : AlgEnt F) :
    GL3Theta.ser1 lam (deriv F) = PowerSeries.derivative (R := ℂ_[p]) (GL3Theta.ser1 lam F) := by
  obtain ⟨a, ha⟩ := GlobalTheory.SerTransport.exists_coef hF
  ext n
  have e : coef1 (deriv F) n = (((n + 1 : Qbar) * a (n + 1) : Qbar) : ℂ) := by
    rw [taylorCoeffAtZero_deriv, ha]; push_cast; rfl
  rw [PowerSeries.coeff_derivative, GlobalTheory.SerTransport.coeff_padicTransportSeries, GlobalTheory.SerTransport.coeff_padicTransportSeries, e, ha,
    GlobalTheory.SerTransport.lamC_coe, GlobalTheory.SerTransport.lamC_coe, map_mul]
  simp [mul_comm]

theorem atU_deriv : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p) (F : ℂ → ℂ), AlgEnt F → AlgEnt (deriv F) ∧ PowerSeries.derivative (R := ℂ_[p]) (g.atU F) = PowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * omegaW g.W g.wq * g.atU (deriv F) := by
  intro p _ g F hF
  refine ⟨algEnt_deriv hF, ?_⟩
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero'
    (GlobalTheory.SerTransport.const_Cl g ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]))
  rw [GlobalTheory.SerTransport.atU_eq, GlobalTheory.SerTransport.atU_eq, padicTaylorSeries_deriv_eq_derivative g.lam hF,
    PowerSeries.derivative_subst hs]
  have hd : PowerSeries.derivative (R := ℂ_[p]) (PowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * g.l) =
      PowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * omegaW g.W g.wq := by
    rw [Derivation.leibniz, PowerSeries.derivative_C, smul_zero, add_zero, smul_eq_mul, GL3Theta.G1.l,
      GlobalTheory.WpForm.derivative_flog]
  rw [hd]
  ring

end GlobalTheory.DerivTransport

end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

theorem _root_.GlobalTheory.T.latticeTranslate_halfPeriod_sigmaStar_pow_eight_mul_eq_one : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ t : ℂ, t ∉ Λ → 2 * t ∈ Λ → U1 Λ t (sgStar Λ) 0 ^ 8 * ((wpF Λ t ^ 2 + g2 Λ / 4) ^ 2 + 2 * g3 Λ * wpF Λ t) = 1 := by
  first | exact @GlobalTheory.HalfPeriodValue.U1_sgStar_pow_eight | exact GlobalTheory.HalfPeriodValue.U1_sgStar_pow_eight | (intros; apply GlobalTheory.HalfPeriodValue.U1_sgStar_pow_eight <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta

theorem IsLat.evenTheta_translate_sq_eq_sigmaStar : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ t₀ : ℂ, t₀ ∉ Λ → 2 * t₀ ∈ Λ → ∀ t, t ∉ Λ → ∀ z, U1 Λ t (sgStar Λ) 0 ^ 2 * U1 Λ t (GL3Theta.th0 Λ t₀) z ^ 2 = -(U1 Λ (2 * t) (sgStar Λ) z * sgStar Λ z) + (wpF Λ t - wpF Λ t₀) * U1 Λ t (sgStar Λ) 0 ^ 2 * U1 Λ t (sgStar Λ) z ^ 2 := by
  intro Λ h t₀ h0 h2 t ht z
  have hsq := (GlobalTheory.T.th0_zero_even_sq_zeros_and_periodicity Λ h t₀ h0 h2).2.2.2.1 (z + t)
  have hσ := (h.sg_eq_zero t).not.2 ht
  rw [h.sqTh_sub h0 ht] at hsq
  have hs : sqTh Λ t (z + t) * sgStar Λ t ^ 2 = -(sgStar Λ (z + 2 * t) * sgStar Λ z) := by
    rw [sqTh, div_mul_cancel₀ _ (pow_ne_zero 2 hσ), show t - (z + t) = -z by ring, h.sg_neg,
      show t + (z + t) = z + 2 * t by ring]
    ring
  simp only [U1, zero_add, mul_pow]
  rw [hsq]
  have he : Complex.exp (-↑Real.pi * z * (starRingEnd ℂ) (2 * t) / ↑(area Λ) -
        ↑Real.pi * (2 * t) * (starRingEnd ℂ) (2 * t) / (2 * ↑(area Λ))) =
      Complex.exp (-↑Real.pi * 0 * (starRingEnd ℂ) t / ↑(area Λ) -
        ↑Real.pi * t * (starRingEnd ℂ) t / (2 * ↑(area Λ))) ^ 2 *
      Complex.exp (-↑Real.pi * z * (starRingEnd ℂ) t / ↑(area Λ) -
        ↑Real.pi * t * (starRingEnd ℂ) t / (2 * ↑(area Λ))) ^ 2 := by
    rw [← mul_pow, ← Complex.exp_add, sq, ← Complex.exp_add, map_mul, map_ofNat]
    congr 1
    ring
  rw [he]
  generalize Complex.exp (-↑Real.pi * 0 * (starRingEnd ℂ) t / ↑(area Λ) -
    ↑Real.pi * t * (starRingEnd ℂ) t / (2 * ↑(area Λ))) = a
  generalize Complex.exp (-↑Real.pi * z * (starRingEnd ℂ) t / ↑(area Λ) -
    ↑Real.pi * t * (starRingEnd ℂ) t / (2 * ↑(area Λ))) = b
  linear_combination a ^ 2 * b ^ 2 * hs

end GlobalTheory.EvenTheta
end

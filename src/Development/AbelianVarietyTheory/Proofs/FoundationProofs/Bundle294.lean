module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle285
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle077
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle221
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle225
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle284
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle251
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle286
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle287
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionPointPadicAbscissaNormLeOne
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

theorem _root_.GlobalTheory.T.maxSlope_sum_weyl_and_dualWeyl_lattices_le : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (v₀ : InfinitePlace K), IsConjAt v₀ → ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (R : ℝ), 1 ≤ R → SpreadLe lam R → ∀ (G : ι → Matrix (Fin n) (Fin n) K), (∀ τ, IsDefGram (G τ)) → ∀ (C : Type) [Nonempty C] (M : C → ι → Submodule (𝓞 K) (Fin n → K)), (∀ c τ, IsSelfDualK (G τ) (M c τ)) → ∀ (N : ℕ) (e : Fin N ≃ C × VVIdx lam) (X : InfinitePlace K → Matrix (Fin N) (Fin N) ℂ), IsMetric (sumGram lam e G) X → TestLatticeCondition N X (sumLat lam e fun c => nabK lam (M c)) (bound (Fintype.card ι) n R) ∧ TestLatticeCondition N X (sumLat lam e fun c => delK lam (M c)) (bound (Fintype.card ι) n R) := by
  first | exact @GlobalTheory.TestLat.testLatticeCondition_sumLat_nabK_and_delK | exact GlobalTheory.TestLat.testLatticeCondition_sumLat_nabK_and_delK | (intros; apply GlobalTheory.TestLat.testLatticeCondition_sumLat_nabK_and_delK <;> assumption)
end

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

theorem _root_.GlobalTheory.T.edge_class_cup_product_geometric : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ c₁ : ℕ, ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : GlobalTheory.K5.Tower p Ω) (L n : ℕ), n ≤ L → ∀ (x y lz lq η : Gal p Ω → ZMod (p ^ n)) (f : Ω),
  (∀ g ∈ Gn T L, ∀ h ∈ Gn T L, x (g * h) = x g + x h ∧ y (g * h) = y g + y h) →
  IsKum T n (Gn T L) (T.ζ (L + n)) lz → IsKum T n (Gn T L) (T.qq (L + n)) lq → IsInt (p := p) f → (∀ g ∈ Gn T L, g f = f) →
  (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), ∀ h ∈ (Ggeo p Ω ⊓ Gn T L), x g * y h = η h - η (g * h) + η g) →
  (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), ∃ S : Finset Ω, ∀ h ∈ (Ggeo p Ω ⊓ Gn T L), (∀ z ∈ S, h z = g z) → η h = η g) →
  Cob2 n (Gn T L) (fun g h => (p : Ω) ^ c₁ * (((x g).val : Ω) * ((y h).val : Ω)) + (p : Ω) ^ c₁ * f * (((lz g).val : Ω) * ((lq h).val : Ω))) →
  ∃ o : Ω, IsInt (p := p) o ∧ (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), g o = o) ∧ ∀ σ ∈ Gn T L,
    Cob1 n (Ggeo p Ω ⊓ Gn T L) (fun h => (p : Ω) ^ c * ((η (σ * h * σ⁻¹) - η h - x h * y σ + x σ * y h).val : Ω) - (σ⁻¹ o - o - (p : Ω) ^ c * f * ((lz σ).val : Ω)) * ((lq h).val : Ω)) := by
  first | exact @GlobalTheory.EdgeAlg.edge_class_cup | exact GlobalTheory.EdgeAlg.edge_class_cup | (intros; apply GlobalTheory.EdgeAlg.edge_class_cup <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.Doubling GlobalTheory.Eis.Conv

noncomputable section

namespace GlobalTheory.Eis.Conv.CovSkew

theorem exists_delta (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) :
    ∃ δ : E, σ δ = -δ ∧ ∀ z : E, ∃ a b : F, z = a • (1 : E) + b • δ := by
  obtain ⟨-, hc, h2, hσ⟩ := h
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hnr : ¬ ComplexEmbedding.IsReal τ := IsTotallyComplex.complexEmbedding_not_isReal τ
  obtain ⟨x, hx⟩ : ∃ x, star (τ x) ≠ τ x := by
    by_contra hcon
    push Not at hcon
    apply hnr
    rw [ComplexEmbedding.isReal_iff]
    ext x
    exact hcon x
  have hδ : σ (x - σ x) = -(x - σ x) := by
    apply τ.injective
    rw [hσ, map_neg, map_sub, hσ, star_sub, star_star, neg_sub]
  have h0 : x - σ x ≠ 0 := by
    intro h0
    apply hx
    rw [← hσ, ← sub_eq_zero.mp h0]
  refine ⟨x - σ x, hδ, ?_⟩
  generalize x - σ x = δ at hδ h0
  have hli : LinearIndependent F ![(1 : E), δ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg σ hst
    have hsm : ∀ (a : F) (z : E), σ (a • z) = a • σ z := fun a z => σ.toLinearMap.map_smul a z
    rw [map_add (f := _), hsm, hsm, map_one, hδ, map_zero, smul_neg] at h1
    have hs : (2 * s) • (1 : E) = 0 := by
      rw [two_mul, add_smul]; linear_combination hst + h1
    have hs0 : s = 0 := by simpa using hs
    refine ⟨hs0, ?_⟩
    rw [hs0, zero_smul, zero_add] at hst
    exact (smul_eq_zero.mp hst).resolve_right h0
  intro z
  have hsp := hli.span_eq_top_of_card_eq_finrank' (by simp [h2])
  have hz : z ∈ Submodule.span F (Set.range ![(1 : E), δ]) := by rw [hsp]; trivial
  rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
    Set.singleton_union, Submodule.mem_span_pair] at hz
  obtain ⟨a, b, hab⟩ := hz
  exact ⟨a, b, hab.symm⟩

section
variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]

theorem exists_coords (δ : E) (h : ∀ z : E, ∃ a b : F, z = a • (1 : E) + b • δ) (z : R ⊗[F] E) :
    ∃ u v : R, z = u ⊗ₜ[F] (1 : E) + v ⊗ₜ[F] δ := by
  induction z with
  | tmul r e =>
    obtain ⟨a, b, rfl⟩ := h e
    exact ⟨a • r, b • r, by
      rw [TensorProduct.tmul_add, TensorProduct.smul_tmul, TensorProduct.smul_tmul]⟩
  | add x y hx hy =>
    obtain ⟨u, v, rfl⟩ := hx
    obtain ⟨u', v', rfl⟩ := hy
    exact ⟨u + u', v + v', by simp only [TensorProduct.add_tmul]; abel⟩

def psi (δ : E) (a a' : R) : R ⊗[F] E := (a - a') • (1 : R ⊗[F] E) + (a + a') • ((1 : R) ⊗ₜ[F] δ)

theorem psi_eq (δ : E) (a a' : R) :
    psi δ a a' = (a - a') ⊗ₜ[F] (1 : E) + (a + a') ⊗ₜ[F] δ := by
  simp [psi, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul']

theorem exists_psi [CharZero F] (σ : E →ₐ[F] E) (δ : E) (hδ : σ δ = -δ)
    (h : ∀ z : E, ∃ a b : F, z = a • (1 : E) + b • δ) {n : ℕ}
    (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (hS : cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ) S = -S) :
    ∃ T : Fin n → Fin n → R, ∀ i j, S i j = psi δ (T i j) (T j i) := by
  choose U V hUV using fun i j => exists_coords δ h (S i j)
  set c : R := algebraMap F R 2⁻¹ with hc
  have h2 : 2 * c = 1 := by
    rw [hc, ← map_ofNat (algebraMap F R) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]
  refine ⟨fun i j => c * c * (U i j - U j i + V i j + V j i), fun i j => ?_⟩
  have h1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ (S j i) = - S i j := congrFun (congrFun hS i) j
  have e1 : ∀ k l, S k l = U k l • (1 : R ⊗[F] E) + V k l • ((1 : R) ⊗ₜ[F] δ) := fun k l => by
    rw [hUV]; simp [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul']
  have e2 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ (S j i)
      = U j i • (1 : R ⊗[F] E) - V j i • ((1 : R) ⊗ₜ[F] δ) := by
    rw [hUV, map_add (f := _)]
    change U j i ⊗ₜ[F] σ 1 + V j i ⊗ₜ[F] σ δ = _
    simp [hδ, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', TensorProduct.tmul_neg,
      sub_eq_add_neg]
  rw [e2] at h1
  have e3 := e1 i j
  have h2' : 2 * algebraMap R (R ⊗[F] E) c = 1 := by
    rw [← map_ofNat (algebraMap R (R ⊗[F] E)) 2, ← map_mul, h2, map_one]
  unfold psi
  simp only [Algebra.smul_def, map_add (f := _), map_sub, map_mul] at h1 e3 ⊢
  generalize algebraMap R (R ⊗[F] E) = f at *
  generalize ((1 : R) ⊗ₜ[F] δ) = d at *
  linear_combination (f c) * e3 + (f c) * h1 - S i j * h2'
    - f c * (f (U i j) - f (U j i) + (f (V i j) + f (V j i)) * d) * h2'

theorem psi_split (δ : E) (x x' : F) (y y' t w w' : R) :
    psi δ (algebraMap F R x + y + t * w) (algebraMap F R x' + y' + t * w')
      = inclR (F := F) R ((x - x') • (1 : E) + (x + x') • δ) + psi δ y y'
        + algebraMap R (R ⊗[F] E) t * psi δ w w' := by
  have : inclR (F := F) R ((x - x') • (1 : E) + (x + x') • δ)
      = psi δ (algebraMap F R x) (algebraMap F R x') := by
    rw [psi_eq, ← map_sub, ← map_add (f := _), Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, TensorProduct.smul_tmul,
      ← TensorProduct.tmul_add]
    rfl
  rw [this]
  unfold psi
  simp only [Algebra.smul_def, map_add (f := _), map_sub, map_mul]
  ring

end

theorem cover_skew : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (b C₀ : ℝ) (Ω₀ : Set (AF F)), IsCompact Ω₀ → (∀ m : ℕ, ∃ Y : Finset (AF F), (Y.card : ℝ) ≤ C₀ * b ^ m ∧ ∀ a : AF F, ∃ x : F, ∃ y ∈ Y, ∃ ω ∈ Ω₀, a = algebraMap F (AF F) x + y + (halfInf F).1 ^ m * ω) → ∀ n : ℕ, ∃ (Ω : Set (AF F ⊗[F] E)) (C : ℝ), IsCompact Ω ∧ ∀ m : Fin n → ℕ, ∃ Y : Finset (Matrix (Fin n) (Fin n) (AF F ⊗[F] E)), (Y.card : ℝ) ≤ C * ∏ i, (b ^ 2) ^ (n * m i) ∧ ∀ S : Matrix (Fin n) (Fin n) (AF F ⊗[F] E), cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) S = -S → ∃ S₀ : Matrix (Fin n) (Fin n) E, ∃ y ∈ Y, ∃ ω : Matrix (Fin n) (Fin n) (AF F ⊗[F] E), (∀ i j, ω i j ∈ Ω) ∧ S = S₀.map (inclR (F := F) (AF F)) + y + Matrix.diagonal (fun i => (halfE F E).1 ^ m i) * ω * Matrix.diagonal (fun i => (halfE F E).1 ^ m i) := by
  intro F E _ _ _ _ _ σ hσ b C₀ Ω₀ hΩ₀ hcov n
  classical
  obtain ⟨δ, hδ, hsp⟩ := exists_delta F E σ hσ
  choose Y hY hYc using hcov
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := isTopologicalRing_tens
  have hcont : Continuous fun p : AF F × AF F => psi (F := F) δ p.1 p.2 := by
    unfold psi
    fun_prop
  refine ⟨_, C₀ ^ (n * n), (hΩ₀.prod hΩ₀).image hcont, fun m => ?_⟩
  refine ⟨(Fintype.piFinset fun p : Fin n × Fin n => Y (m p.1 + m p.2)).image
    (fun y => Matrix.of fun i j => psi δ (y (i, j)) (y (j, i))), ?_, fun S hS => ?_⟩
  · refine (Nat.cast_le.mpr Finset.card_image_le).trans ?_
    rw [Fintype.card_piFinset, Nat.cast_prod]
    refine (Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun p _ => hY _)).trans (le_of_eq ?_)
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, Finset.prod_pow_eq_pow_sum]
    congr 1
    simp only [← pow_mul]
    rw [Finset.prod_pow_eq_pow_sum, Fintype.sum_prod_type]
    congr 1
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, ← Finset.mul_sum]
    ring
  · obtain ⟨T, hT⟩ := exists_psi σ δ hδ hsp S hS
    choose x y hy ω hω hTe using fun i j => hYc (m i + m j) (T i j)
    refine ⟨Matrix.of fun i j => (x i j - x j i) • (1 : E) + (x i j + x j i) • δ, _,
      Finset.mem_image.mpr ⟨fun p => y p.1 p.2, Fintype.mem_piFinset.mpr fun p => hy _ _, rfl⟩,
      Matrix.of fun i j => psi δ (ω i j) (ω j i),
      fun i j => ⟨(ω i j, ω j i), ⟨hω _ _, hω _ _⟩, rfl⟩, ?_⟩
    ext i j
    rw [Matrix.add_apply, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, hT,
      hTe i j, hTe j i, add_comm (m j) (m i), psi_split]
    have : (halfE F E).1 = algebraMap (AF F) (AF F ⊗[F] E) (halfInf F).1 := rfl
    rw [this, map_pow]
    simp only [Matrix.map_apply, Matrix.of_apply]
    ring

end GlobalTheory.Eis.Conv.CovSkew

end
end

section

noncomputable section

namespace GlobalTheory.Eis.Conv

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.Doubling GlobalTheory.AdelicU

theorem norm_halfE (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h : Module.finrank F E = 2) :
    Algebra.norm (AF F) (halfE F E).1 = (halfInf F).1 ^ 2 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  haveI : Nontrivial (AF F) := (evInf F w).toRingHom.domain_nontrivial
  change Algebra.norm (AF F) (algebraMap (AF F) (AF F ⊗[F] E) (halfInf F).1) = _
  rw [Algebra.norm_algebraMap, Module.finrank_baseChange, h]

theorem evFin_halfInf (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    evFin F v (halfInf F).1 = 1 :=
  map_one (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v)

theorem evInf_halfInf (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) :
    evInf F w (halfInf F).1 = algebraMap F _ 2⁻¹ :=
  (GlobalTheory.AutFunCompare.evW w).commutes _

theorem nnnorm_evInf_halfInf (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) :
    ‖evInf F w (halfInf F).1‖₊ = 2⁻¹ := by
  rw [evInf_halfInf]
  have h2 : w (2⁻¹ : F) = 2⁻¹ := by
    rw [← InfinitePlace.norm_embedding_eq w, map_inv₀, norm_inv, map_ofNat]
    simp
  have e : ‖((2⁻¹ : F) : w.Completion)‖ = 2⁻¹ := (InfinitePlace.Completion.norm_coe w _).trans h2
  apply NNReal.eq
  rw [NNReal.coe_inv, NNReal.coe_ofNat]
  rw [InfinitePlace.Completion.algebraMap_apply]
  exact e

theorem absE_halfE (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (h : IsCMExt F E σ) : absE F E (halfE F E) = ((4 : ℝ≥0) ^ Fintype.card (InfinitePlace F))⁻¹ := by
  haveI := h.1
  have hn := norm_halfE F E h.2.2.1
  have hfin : ∀ v, absEv F E v (unitFin F E v (halfE F E)) = 1 := fun v => by
    rw [absEv_unitFin, hn, map_pow, evFin_halfInf]
    simp
  have hinf : ∀ w, absEw F E w (unitInf F E w (halfE F E)) = 4⁻¹ := fun w => by
    rw [absEw_unitInf, hn, map_pow, nnnorm_pow, nnnorm_evInf_halfInf, InfinitePlace.mult,
      if_pos (IsTotallyReal.isReal w), pow_one, inv_pow]
    norm_num
  rw [absE_apply, finprod_eq_one_of_forall_eq_one hfin, mul_one, Finset.prod_congr rfl fun w _ => hinf w,
    Finset.prod_const, Finset.card_univ, inv_pow]

end GlobalTheory.Eis.Conv

end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.Doubling GlobalTheory.Eis.Conv

theorem _root_.GlobalTheory.T.compact_adeles_rational_points_finite_eventually_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (Ω : Set (AF F ⊗[F] E)), IsCompact Ω → {x : E | inclR (F := F) (AF F) x ∈ Ω}.Finite ∧ ∃ m₀ : ℕ, ∀ m, m₀ ≤ m → ∀ ω ∈ Ω, ∀ x : E, inclR (F := F) (AF F) x = (halfE F E).1 ^ m * ω → x = 0 := by
  first | exact @GlobalTheory.Eis.Conv.Discr.finite_and_eventually_eq_zero | exact GlobalTheory.Eis.Conv.Discr.finite_and_eventually_eq_zero | (intros; apply GlobalTheory.Eis.Conv.Discr.finite_and_eventually_eq_zero <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.Doubling GlobalTheory.Eis.Conv

theorem _root_.GlobalTheory.T.exists_cmAdele_split_complex_finiteAdeles : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∃ e : (AF F ⊗[F] E) ≃+* (InfinitePlace E → ℂ) × FiniteAdeleRing (𝓞 E) E, Continuous e.symm ∧ (∀ x : E, e (inclR (F := F) (AF F) x) = (fun w : InfinitePlace E => w.embedding x, algebraMap E (FiniteAdeleRing (𝓞 E) E) x)) ∧ e (halfE F E).1 = (fun _ => 2⁻¹, 1) := by
  first | exact @GlobalTheory.Eis.Conv.AdeleCMSplit.exists_adele_split | exact GlobalTheory.Eis.Conv.AdeleCMSplit.exists_adele_split | (intros; apply GlobalTheory.Eis.Conv.AdeleCMSplit.exists_adele_split <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.norm_thetaTranslateValueAtZeroPadic_periodic : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p),
    GL3Theta.At D cc δ g → ∀ t ω : ℂ, InRationalLattice g.abelian₂ t → ω ∈ g.abelian₂ → ‖GlobalTheory.ThetaTransl.cval g (t + ω)‖ = ‖GlobalTheory.ThetaTransl.cval g t‖ := by
  first | exact @GlobalTheory.ThetaTransl.cval_norm_periodic | exact GlobalTheory.ThetaTransl.cval_norm_periodic | (intros; apply GlobalTheory.ThetaTransl.cval_norm_periodic <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui
open scoped BigOperators

theorem _root_.GlobalTheory.T.rationalMatrixMul_thetaLattices : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), (∀ (M' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E), (∀ i j, IsIntegral ℤ (M' i j)) → (∀ i j, IsIntegral ℤ (M i j)) → ∀ x ∈ La0 D (tor0 D cc δ) N N', mulV D M' M x ∈ La0 D (tor0 D cc δ) N N') ∧ (∀ (M' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E), ∃ m : ℕ, 0 < m ∧ ∀ x ∈ La0 D (tor0 D cc δ) N N', m • mulV D M' M x ∈ La0 D (tor0 D cc δ) N N') ∧ ∀ (γA : GA D N) (γA' : GA D N') (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), IsRat D (γA : GL (Fin N) (AE D)) γ → IsRat D (γA' : GL (Fin N') (AE D)) γ' → Moves D (γA : GL (Fin N) (AE D)) L₁ → Moves D (γA' : GL (Fin N') (AE D)) L₁' → ∀ x, x ∈ La0 D (tor0 D cc δ) N N' ↔ mulV D γ' (adj D γ) x ∈ La D (tor0 D cc δ) L₁ L₁' := by
  first | exact @GlobalTheory.ThetaStab.mulV_theta_lattices | exact GlobalTheory.ThetaStab.mulV_theta_lattices | (intros; apply GlobalTheory.ThetaStab.mulV_theta_lattices <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

theorem _root_.GlobalTheory.T.coeffNormLeOne_of_isogeny_series_identities : ∀ (p : ℕ) [Fact p.Prime] (k : ℕ) (e h S f : PowerSeries ℂ_[p]) (x₀ x₁ : ℂ_[p]) (y : Fin k → ℂ_[p]) (y' : Fin (2 * k) → ℂ_[p]), IntSer e → PowerSeries.constantCoeff e = 1 → IntSer h → PowerSeries.constantCoeff h = 0 → ‖PowerSeries.coeff 1 h‖ = 1 → ‖((2 * k : ℕ) : ℂ_[p])‖ < 1 → PowerSeries.constantCoeff S = 1 → PowerSeries.constantCoeff f = 1 → f ^ 2 = S * lineSer e x₀ → (PowerSeries.subst h f : PowerSeries ℂ_[p]) = S ^ k * ∏ i, lineSer e (y i) → (PowerSeries.subst h (S * lineSer e x₁) : PowerSeries ℂ_[p]) = S ^ (2 * k) * ∏ j, lineSer e (y' j) → (∀ i j, y i ≠ y' j) → (∃ j, y' j = x₀) → (∃ j, y' j = x₁) → x₀ ≠ x₁ → IntSer f ∧ ‖x₀‖ ≤ 1 := by
  first | exact @GlobalTheory.EvenTheta.intSer_of_isogeny_identities | exact GlobalTheory.EvenTheta.intSer_of_isogeny_identities | (intros; apply GlobalTheory.EvenTheta.intSer_of_isogeny_identities <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

theorem _root_.GlobalTheory.T.sigmaStar_mul_sq_eq_prod_kernel_quotients : ∀ (Λ : AddSubgroup ℂ), IsLat Λ → ∀ (β : ℂ) (k : ℕ), (∀ ω ∈ Λ, β * ω ∈ Λ) → β * starRingEnd ℂ β = ((k + 1 : ℕ) : ℂ) → ∃ Q : Fin k → ℂ, (∀ i, Q i ∉ Λ ∧ β * Q i ∈ Λ) ∧ ∀ z, sgStar Λ (β * z) ^ 2 = β ^ 2 * sgStar Λ z ^ 2 * ∏ i, sqTh Λ (Q i) z := by
  first | exact @GlobalTheory.EvenTheta.MulLat.sg_mul_sq | exact GlobalTheory.EvenTheta.MulLat.sg_mul_sq | (intros; apply GlobalTheory.EvenTheta.MulLat.sg_mul_sq <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.TorsionAbscissa

theorem norm_xAt_le_of_mul : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p), GL3Theta.At D cc δ g → ∀ (N : ℕ) (v : ℂ), 0 < N → Nat.Coprime N p → (N : ℂ) * v ∈ g.abelian₂ → v ∉ g.abelian₂ → ‖GlobalTheory.EvenTheta.xAt g v‖ ≤ 1 := by
  intro D p _ cc δ g hg N v hN hcop hNv hv
  exact norm_xAt_le D p cc δ g hg v ⟨hv, N, hN, hcop, hNv⟩

end GlobalTheory.TorsionAbscissa
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.torsionPoint_padicAbscissa_norm_le_one : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p),
    GL3Theta.At D cc δ g → ∀ t : ℂ, GL3Theta.Tors1 p g.abelian₂ t → ‖GlobalTheory.EvenTheta.xAt g t‖ ≤ 1 := by
  first | exact @GlobalTheory.TorsionAbscissa.norm_xAt_le | exact GlobalTheory.TorsionAbscissa.norm_xAt_le | (intros; apply GlobalTheory.TorsionAbscissa.norm_xAt_le <;> assumption)
end

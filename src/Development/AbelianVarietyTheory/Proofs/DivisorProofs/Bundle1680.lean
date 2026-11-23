module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1616
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle147
import GroundTheory.Brauer.TensorSimple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1623
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle093
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1629
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1571
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle156
public import Formalism.UnipotentAdelicQuotients.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle076
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BorelFiniteClassNumberCentraliserTorus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialZeroLocusCoordinates
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
import Std.Tactic.BVDecide.Normalize.BitVec

@[expose] public section

section

open MeasureTheory Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKDef
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.VanishNonEll

open GlobalTheory.BCT GlobalTheory.BCT.OrbProd GlobalTheory.LKCount GlobalTheory.LKCount.OrbKProd

section Transport

variable {A B : Type} [Group A] [Group B]

theorem map_twCent_id (e : A ≃* B) (δ : A) :
    (twCent (MonoidHom.id A) δ).map e.toMonoidHom = twCent (MonoidHom.id B) (e δ) := by
  ext b
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨a, ha, rfl⟩
    have ha' : a * δ = δ * a := ha
    show e a * e δ = e δ * e a
    rw [← map_mul, ha', map_mul]
  · intro hb
    have hb' : b * e δ = e δ * b := hb
    refine ⟨e.symm b, ?_, by simp⟩
    show e.symm b * δ = δ * e.symm b
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hb']

theorem map_conj_equiv (e : A ≃* B) (K : Subgroup A) (x : A) :
    (K.map (MulAut.conj x).toMonoidHom).map e.toMonoidHom =
      (K.map e.toMonoidHom).map (MulAut.conj (e x)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext k
  simp [MulAut.conj_apply]

theorem orbK_congr_equiv (e : A ≃* B) (K : Subgroup A) (δ : A) (F : A → ℂ)
    (hinv : ∀ t ∈ twCent (MonoidHom.id B) (e δ), ∀ k ∈ K.map e.toMonoidHom, ∀ x,
      oTerm (MonoidHom.id B) (K.map e.toMonoidHom) (twCent (MonoidHom.id B) (e δ) ⊓ K.map e.toMonoidHom) (e δ)
          (fun z => F (e.symm z)) (t * x * k) =
        oTerm (MonoidHom.id B) (K.map e.toMonoidHom) (twCent (MonoidHom.id B) (e δ) ⊓ K.map e.toMonoidHom) (e δ)
          (fun z => F (e.symm z)) x) :
    orbK (MonoidHom.id A) K δ F = orbK (MonoidHom.id B) (K.map e.toMonoidHom) (e δ) (fun z => F (e.symm z)) := by
  unfold orbK
  rw [orbC_eq, orbC_eq]
  set TB := twCent (MonoidHom.id B) (e δ)
  set KB := K.map e.toMonoidHom
  have hmemT : ∀ a ∈ TB, e.symm a ∈ twCent (MonoidHom.id A) δ := by
    intro a ha
    rw [← show (twCent (MonoidHom.id A) δ).map e.toMonoidHom = TB from map_twCent_id e δ] at ha
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    simpa using ha'
  have hmemK : ∀ b ∈ KB, e.symm b ∈ K := by
    intro b hb
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
    simpa using hb'
  have hpt : ∀ x : A, oTerm (MonoidHom.id A) K (twCent (MonoidHom.id A) δ ⊓ K) δ F x =
      oTerm (MonoidHom.id B) KB (TB ⊓ KB) (e δ) (fun z => F (e.symm z)) (e x) := by
    intro x
    unfold oTerm
    congr 1
    · have h1 : TB ⊓ KB = (twCent (MonoidHom.id A) δ ⊓ K).map e.toMonoidHom := by
        rw [Subgroup.map_inf_eq _ _ _ e.injective, map_twCent_id]
      have h2 : TB ⊓ KB.map (MulAut.conj (e x)).toMonoidHom =
          (twCent (MonoidHom.id A) δ ⊓ K.map (MulAut.conj x).toMonoidHom).map e.toMonoidHom := by
        rw [Subgroup.map_inf_eq _ _ _ e.injective, map_twCent_id, map_conj_equiv]
      rw [h1, h2]
      unfold vol
      rw [Subgroup.relIndex_map_map_of_injective _ _ e.injective,
        Subgroup.relIndex_map_map_of_injective _ _ e.injective]
    · simp
  let Φ : DoubleCoset.Quotient (twCent (MonoidHom.id A) δ : Set A) (K : Set A) →
      DoubleCoset.Quotient (TB : Set B) (KB : Set B) := fun q => DoubleCoset.mk TB KB (e (Quotient.out q))
  have hΦ : Function.Bijective Φ := by
    constructor
    · intro q1 q2 h
      obtain ⟨a, ha, b, hb, h'⟩ := (@DoubleCoset.eq _ _ _ _ _ _).mp h
      calc q1 = DoubleCoset.mk _ K (Quotient.out q1) := (DoubleCoset.out_eq' q1).symm
        _ = DoubleCoset.mk _ K (Quotient.out q2) := by
          rw [DoubleCoset.eq]
          refine ⟨e.symm a, hmemT a ha, e.symm b, hmemK b hb, ?_⟩
          apply e.injective
          simp [h']
        _ = q2 := DoubleCoset.out_eq' q2
    · intro p
      refine ⟨DoubleCoset.mk (twCent (MonoidHom.id A) δ) K (e.symm (Quotient.out p)), ?_⟩
      obtain ⟨a, ha, b, hb, h'⟩ := DoubleCoset.mk_out_eq_mul (twCent (MonoidHom.id A) δ) K (e.symm (Quotient.out p))
      show DoubleCoset.mk TB KB (e (Quotient.out (DoubleCoset.mk (twCent (MonoidHom.id A) δ) K (e.symm (Quotient.out p))))) = p
      rw [h']
      conv_rhs => rw [← DoubleCoset.out_eq' p]
      rw [DoubleCoset.eq]
      have ha' : e a ∈ TB := by rw [← show (twCent (MonoidHom.id A) δ).map e.toMonoidHom = TB from map_twCent_id e δ]; exact Subgroup.mem_map_of_mem _ ha
      have hb' : e b ∈ KB := Subgroup.mem_map_of_mem _ hb
      refine ⟨(e a)⁻¹, TB.inv_mem ha', (e b)⁻¹, KB.inv_mem hb', ?_⟩
      simp [mul_assoc]
  have hz : ∀ q : DoubleCoset.Quotient (twCent (MonoidHom.id A) δ : Set A) (K : Set A), oTerm (MonoidHom.id A) K (twCent (MonoidHom.id A) δ ⊓ K) δ F (Quotient.out q) =
      oTerm (MonoidHom.id B) KB (TB ⊓ KB) (e δ) (fun z => F (e.symm z)) (Quotient.out (Equiv.ofBijective Φ hΦ q)) := by
    intro q
    rw [hpt]
    obtain ⟨a, ha, b, hb, h'⟩ := DoubleCoset.mk_out_eq_mul TB KB (e (Quotient.out q))
    show _ = oTerm (MonoidHom.id B) KB (TB ⊓ KB) (e δ) (fun z => F (e.symm z)) (Quotient.out (DoubleCoset.mk TB KB (e (Quotient.out q))))
    rw [h', hinv a ha b hb]
  rw [finsum_congr hz]
  exact finsum_comp_equiv (Equiv.ofBijective Φ hΦ)
    (f := fun q => oTerm (MonoidHom.id B) KB (TB ⊓ KB) (e δ) (fun z => F (e.symm z)) (Quotient.out q))

end Transport

section Prod

variable {G₁ G₂ : Type} [Group G₁] [Group G₂] [TopologicalSpace G₁] [TopologicalSpace G₂]
  [IsTopologicalGroup G₁] [IsTopologicalGroup G₂]

end Prod

theorem natDegree_minpoly_le (F L C : Type) [Field F] [Field L] [Algebra F L] [Ring C]
    [Algebra F C] [Algebra.IsCentral F C] [IsSimpleRing C] [FiniteDimensional F C] (n : ℕ) (hn : 0 < n)
    (ι : C →ₐ[F] Matrix (Fin n) (Fin n) L) (a : C) : (minpoly F a).natDegree ≤ n := by
  haveI : NeZero n := ⟨hn.ne'⟩
  let g : L ⊗[F] C →ₐ[L] Matrix (Fin n) (Fin n) L :=
    Algebra.TensorProduct.lift (Algebra.ofId L _) ι (fun l y ↦ Algebra.commute_algebraMap_left l _)
  haveI : IsSimpleRing (L ⊗[F] C) := GroundTheory.Brauer.isSimpleRing_tensorProduct_of_right
  have hg : Function.Injective g := GlobalTheory.CsaCharpoly.injective_of_isSimpleRing g.toRingHom
  have eg : g ((1 : L) ⊗ₜ a) = ι a := by
    simp only [g]; erw [Algebra.TensorProduct.lift_tmul]; simp
  have hyi : IsIntegral L ((1 : L) ⊗ₜ[F] a) := IsIntegral.of_finite L _
  have hmin : minpoly L (ι a) = minpoly L ((1 : L) ⊗ₜ[F] a) := by
    rw [← eg]; exact minpoly.algHom_eq g hg _
  have h1 := GlobalTheory.CsaCharpoly.natDegree_minpoly_le_one_tmul L a hyi
  rw [← hmin] at h1
  have h2 : (minpoly L (ι a)).natDegree ≤ (ι a).charpoly.natDegree :=
    Polynomial.natDegree_le_of_dvd (Matrix.minpoly_dvd_charpoly _) (Matrix.charpoly_monic _).ne_zero
  rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at h2
  omega

theorem not_irreducible_map {F L : Type} [Field F] [Field L] (φ : F →+* L) (p : Polynomial F) (hp : p.Monic)
    (hirr : ¬ Irreducible p) : ¬ Irreducible (p.map φ) :=
  fun h => hirr (Polynomial.Monic.irreducible_of_irreducible_map φ p hp h)

end GlobalTheory.VanishNonEll
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.CtLevel

theorem blockDiagonalMatrixOfAddEq_entries_mem_subring {R : Type} [CommRing R] (O : Subring R) {a b n : ℕ} (h : a + b = n)
    (A : Matrix (Fin a) (Fin a) R) (D : Matrix (Fin b) (Fin b) R)
    (hA : ∀ i j, A i j ∈ O) (hD : ∀ i j, D i j ∈ O) (i j : Fin n) : dgMat h A D i j ∈ O := by
  simp only [dgMat, reindex_apply, submatrix_apply]
  rcases (blkEq h).symm i with i' | i' <;> rcases (blkEq h).symm j with j' | j' <;>
    simp [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, hA, hD, O.zero_mem]

theorem det_mem_subring_of_entries_mem_fin {R : Type} [CommRing R] (O : Subring R) {m : ℕ} (A : Matrix (Fin m) (Fin m) R)
    (hA : ∀ i j, A i j ∈ O) : A.det ∈ O := by
  rw [Matrix.det_apply']
  exact O.sum_mem fun σ _ => O.mul_mem (intCast_mem O _) (O.prod_mem fun i _ => hA _ _)

theorem one_matrix_apply_mem_subring {R : Type} [CommRing R] (O : Subring R) {m : ℕ} (i j : Fin m) :
    (1 : Matrix (Fin m) (Fin m) R) i j ∈ O := by
  rw [Matrix.one_apply]; split_ifs
  · exact O.one_mem
  · exact O.zero_mem

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem character_det_integralGL_eq_one_of_unramified (w : Pl E) (μ : (w.adicCompletion E)ˣ →* ℂˣ)
    (hμ : ∀ u ∈ GlobalTheory.LFun.KGL w (n := 1), μ (GeneralLinearGroup.det u) = 1) {m : ℕ} (k : GLw m w)
    (hk : k ∈ GlobalTheory.LFun.KGL w (n := m)) : μ (GeneralLinearGroup.det k) = 1 := by
  set d := GeneralLinearGroup.det k
  let u : GL (Fin 1) (w.adicCompletion E) := Units.map (Matrix.scalar (Fin 1)).toMonoidHom d
  have hu : GeneralLinearGroup.det u = d := by
    ext; simp [u]
  rw [← hu]
  apply hμ
  obtain ⟨h1, h2⟩ := GlobalTheory.AdelicU.mem_GLint_iff.1 hk
  refine GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩
  · have : (u : Matrix (Fin 1) (Fin 1) _) i j = (k.val).det := by
      simp [u, d, Subsingleton.elim i j]
    rw [this]; exact det_mem_subring_of_entries_mem_fin _ _ h1
  · have : (u⁻¹ : GL (Fin 1) _).val i j = (k⁻¹ : GLw m w).val.det := by
      simp [u, d, Subsingleton.elim i j, ← map_inv]
    rw [this]; exact det_mem_subring_of_entries_mem_fin _ _ h2

end GlobalTheory.BCT.CtLevel

namespace GlobalTheory.BCT.CtLevel

theorem lev_KGL_of_unram : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n)
    (w : Pl E) (μ : (w.adicCompletion E)ˣ →* ℂˣ), (∀ u ∈ GlobalTheory.LFun.KGL w (n := 1), μ (GeneralLinearGroup.det u) = 1) →
    lev₁ h w (GlobalTheory.LFun.KGL w (n := n)) μ = GlobalTheory.LFun.KGL w (n := a) ∧ lev₂ h w (GlobalTheory.LFun.KGL w (n := n)) μ = GlobalTheory.LFun.KGL w (n := b) := by
  intro E _ _ _ a b n h w μ hμ
  constructor
  · refine le_antisymm (fun x hx => hx.1.1) fun k hk => ⟨⟨hk, ?_⟩, character_det_integralGL_eq_one_of_unramified w μ hμ k hk⟩
    obtain ⟨h1, h2⟩ := GlobalTheory.AdelicU.mem_GLint_iff.1 hk
    show dgM h w (k, 1) ∈ GlobalTheory.LFun.KGL w (n := n)
    refine GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [dgM_val]
      exact blockDiagonalMatrixOfAddEq_entries_mem_subring _ h _ _ h1 (one_matrix_apply_mem_subring _) i j
    · rw [← map_inv, dgM_val]
      exact blockDiagonalMatrixOfAddEq_entries_mem_subring _ h _ _ h2 (fun i j => by simpa using one_matrix_apply_mem_subring (Ov E w) i j) i j
  · refine le_antisymm (fun x hx => hx.1.1) fun k hk => ⟨⟨hk, ?_⟩, character_det_integralGL_eq_one_of_unramified w μ hμ k hk⟩
    obtain ⟨h1, h2⟩ := GlobalTheory.AdelicU.mem_GLint_iff.1 hk
    show dgM h w (1, k) ∈ GlobalTheory.LFun.KGL w (n := n)
    refine GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [dgM_val]
      exact blockDiagonalMatrixOfAddEq_entries_mem_subring _ h _ _ (one_matrix_apply_mem_subring _) h1 i j
    · rw [← map_inv, dgM_val]
      exact blockDiagonalMatrixOfAddEq_entries_mem_subring _ h _ _ (fun i j => by simpa using one_matrix_apply_mem_subring (Ov E w) i j) h2 i j

end GlobalTheory.BCT.CtLevel
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LeviDesc

theorem intertwiner_eq_zero_of_isCoprime {K : Type} [Field K] {a b : ℕ}
    (A : Matrix (Fin a) (Fin a) K) (B : Matrix (Fin b) (Fin b) K) (C : Matrix (Fin b) (Fin a) K)
    (hc : IsCoprime A.charpoly B.charpoly) (hC : C * A = B * C) : C = 0 := by
  first
  | exact @_root_.GlobalTheory.IntertwiningOperators.main
  | exact _root_.GlobalTheory.IntertwiningOperators.main
  | (apply _root_.GlobalTheory.IntertwiningOperators.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntertwiningOperators.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntertwiningOperators.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntertwiningOperators.main ..)

theorem twCent_blk_le_parP : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E)
    (m : GLw a w × GLw b w), (m.1.val.charpoly * m.2.val.charpoly).Separable →
    twCent (MonoidHom.id (GLw n w)) (blk h w m 0) ≤ GlobalTheory.LeviDesc.parP a n w := by
  intro E _ _ n a b h w m hsep g hg
  have hcop := hsep.isCoprime
  have hM : IsUnit (Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (Matrix.fromBlocks m.1.val (m.1.val * (0 : Matrix (Fin a) (Fin b) (w.adicCompletion E))) 0 m.2.val)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_reindex_self, Matrix.mul_zero, Matrix.det_fromBlocks_zero₁₂]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp m.1.isUnit).mul ((Matrix.isUnit_iff_isUnit_det _).mp m.2.isUnit)
  have hval : ((blk h w m 0 : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
      Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
        (Matrix.fromBlocks m.1.val (m.1.val * (0 : Matrix (Fin a) (Fin b) (w.adicCompletion E))) 0 m.2.val) := by
    simp only [blk]
    rw [dite_eq_left hM]
    rfl
  rw [Matrix.mul_zero] at hval
  have hc : (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * (blk h w m 0 : GLw n w) =
      ((blk h w m 0 : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * g := by
    have := congrArg Units.val (show g * blk h w m 0 = blk h w m 0 * MonoidHom.id _ g from hg)
    simpa using this
  rw [hval] at hc
  set e := finSumFinEquiv.trans (finCongr h) with he
  set g' := Matrix.reindex e.symm e.symm (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hg'
  have hgg : (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = Matrix.reindex e e g' := by
    simp [hg']
  rw [hgg, ← Matrix.fromBlocks_toBlocks g'] at hc
  have hc2 := congrArg (Matrix.reindex e.symm e.symm) hc
  simp only [Matrix.reindex_apply, Equiv.symm_symm, Matrix.submatrix_mul_equiv, Matrix.submatrix_submatrix,
    Equiv.symm_comp_self, Matrix.submatrix_id_id, Matrix.fromBlocks_multiply] at hc2
  rw [Matrix.fromBlocks_inj] at hc2
  have hC : g'.toBlocks₂₁ * m.1.val = m.2.val * g'.toBlocks₂₁ := by
    have := hc2.2.2.1
    simpa using this
  have hC0 := intertwiner_eq_zero_of_isCoprime _ _ _ hcop hC
  show (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)).BlockTriangular fun i : Fin n => decide (a ≤ (i : ℕ))
  intro i j hij
  have hi : a ≤ (i : ℕ) := by
    by_contra hc'
    revert hij
    simp only [hc', decide_false]
    cases decide (a ≤ (j : ℕ)) <;> decide
  have hj : ¬ a ≤ (j : ℕ) := by
    intro hc'
    revert hij
    simp only [hc', decide_true]
    cases decide (a ≤ (i : ℕ)) <;> decide
  have hie : i = e (Sum.inr ⟨(i : ℕ) - a, by omega⟩) := by
    ext; simp [he]; omega
  have hje : j = e (Sum.inl ⟨(j : ℕ), by omega⟩) := by
    ext; simp [he]
  rw [hgg, hie, hje]
  have : g'.toBlocks₂₁ ⟨(i : ℕ) - a, by omega⟩ ⟨(j : ℕ), by omega⟩ = 0 := by rw [hC0]; rfl
  simpa [Matrix.toBlocks₂₁] using this

end GlobalTheory.LeviDesc
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LeviDesc.CentPar

theorem intertwiner_eq_zero {K : Type} [Field K] {a b : ℕ}
    (A : Matrix (Fin a) (Fin a) K) (B : Matrix (Fin b) (Fin b) K) (C : Matrix (Fin b) (Fin a) K)
    (hc : IsCoprime A.charpoly B.charpoly) (hC : C * A = B * C) : C = 0 := by
  first
  | exact @_root_.GlobalTheory.IntertwinerCoprimeCharpoly.main
  | exact _root_.GlobalTheory.IntertwinerCoprimeCharpoly.main
  | (apply _root_.GlobalTheory.IntertwinerCoprimeCharpoly.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntertwinerCoprimeCharpoly.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntertwinerCoprimeCharpoly.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntertwinerCoprimeCharpoly.main ..)

variable {E : Type} [Field E] [NumberField E]

theorem blk_zero_val {n a b : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w) :
    ((blk h w m 0 : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
      Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
        (Matrix.fromBlocks m.1.val 0 0 m.2.val) := by
  have hM : IsUnit (Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (Matrix.fromBlocks m.1.val (m.1.val * (0 : Matrix (Fin a) (Fin b) (w.adicCompletion E))) 0 m.2.val)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_reindex_self, Matrix.mul_zero, Matrix.det_fromBlocks_zero₁₂]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp m.1.isUnit).mul ((Matrix.isUnit_iff_isUnit_det _).mp m.2.isUnit)
  simp only [blk]
  rw [dite_eq_left hM]
  simp

theorem blk_zero_mul {n a b : ℕ} (h : a + b = n) (w : Pl E) (x y : GLw a w × GLw b w) :
    blk h w (x * y) 0 = blk h w x 0 * blk h w y 0 := by
  apply Units.ext
  rw [Units.val_mul, blk_zero_val, blk_zero_val, blk_zero_val]
  simp only [Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp [Prod.fst_mul, Prod.snd_mul]

end GlobalTheory.LeviDesc.CentPar


open GlobalTheory.LeviDesc.CentPar in
theorem GlobalTheory.LeviDesc.mem_twistedCentralizer_parabolic_iff : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E)
    (m : GLw a w × GLw b w), (m.1.val.charpoly * m.2.val.charpoly).Separable →
    ∀ (hγ : blk h w m 0 ∈ GlobalTheory.LeviDesc.parP a n w) (p : GlobalTheory.LeviDesc.parP a n w),
      p ∈ twCent (MonoidHom.id _) (⟨blk h w m 0, hγ⟩ : GlobalTheory.LeviDesc.parP a n w) ↔
        ∃ t ∈ twCent (MonoidHom.id _) m, blk h w t 0 = (p : GLw n w) := by
  intro E _ _ n a b h w m hsep hγ p
  have hcop := hsep.isCoprime
  have hmem : p ∈ twCent (MonoidHom.id _) (⟨blk h w m 0, hγ⟩ : GlobalTheory.LeviDesc.parP a n w) ↔
      (p : GLw n w) * blk h w m 0 = blk h w m 0 * (p : GLw n w) := by
    show p * _ = _ * MonoidHom.id _ p ↔ _
    rw [MonoidHom.id_apply, Subtype.ext_iff]
    rfl
  rw [hmem]
  constructor
  · intro hc
    set e := finSumFinEquiv.trans (finCongr h) with he
    set g' := Matrix.reindex e.symm e.symm ((p : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hg'
    have hgg : ((p : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = Matrix.reindex e e g' := by
      simp [hg']
    have hcM := congrArg Units.val hc
    rw [Units.val_mul, Units.val_mul, blk_zero_val, ← he, hgg, ← Matrix.fromBlocks_toBlocks g'] at hcM
    have hc2 := congrArg (Matrix.reindex e.symm e.symm) hcM
    simp only [Matrix.reindex_apply, Equiv.symm_symm, Matrix.submatrix_mul_equiv, Matrix.submatrix_submatrix,
      Equiv.symm_comp_self, Matrix.submatrix_id_id, Matrix.fromBlocks_multiply] at hc2
    rw [Matrix.fromBlocks_inj] at hc2
    obtain ⟨h11, h12, h21, h22⟩ := hc2
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at h11 h12 h21 h22
    have hC0 : g'.toBlocks₂₁ = 0 := intertwiner_eq_zero _ _ _ hcop h21
    have hB0 : g'.toBlocks₁₂ = 0 := intertwiner_eq_zero _ _ _ hcop.symm h12
    have hg'2 : g' = Matrix.fromBlocks g'.toBlocks₁₁ 0 0 g'.toBlocks₂₂ := by
      rw [← hB0, ← hC0, Matrix.fromBlocks_toBlocks]
    have hdet : IsUnit g'.det := by
      rw [hg', Matrix.det_reindex_self]
      exact (Matrix.isUnit_iff_isUnit_det _).mp (p : GLw n w).isUnit
    rw [hg'2, Matrix.det_fromBlocks_zero₂₁] at hdet
    have hA : IsUnit g'.toBlocks₁₁ := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_of_mul_isUnit_left hdet)
    have hD : IsUnit g'.toBlocks₂₂ := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_of_mul_isUnit_right hdet)
    refine ⟨(hA.unit, hD.unit), ?_, ?_⟩
    · show (hA.unit, hD.unit) * m = m * MonoidHom.id _ (hA.unit, hD.unit)
      rw [MonoidHom.id_apply]
      refine Prod.ext (Units.ext ?_) (Units.ext ?_)
      · simpa using h11
      · simpa using h22
    · apply Units.ext
      rw [blk_zero_val, ← he, hgg]
      conv_rhs => rw [hg'2]
      rfl
  · rintro ⟨t, ht, hp⟩
    have ht' : t * m = m * t := ht
    rw [← hp, ← blk_zero_mul, ← blk_zero_mul, ht']
end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.TorCls
open scoped TensorProduct Classical

namespace GlobalTheory.CentCls.Fin

theorem classes_finite_of_locus (hloc : ∀ (D : Type) [Ring D] [Algebra ℚ D] [FiniteDimensional ℚ D] (σ : D →+* Dᵐᵒᵖ) (β y : D),
  ∃ (N : ℕ) (S : Set (MvPolynomial (Fin N × Fin N) ℚ)) (hS : HeckeCharacterZeroLocus.IsGroupLocus S)
    (φ : ∀ (R : Type) [CommRing R] [Algebra ℚ R], HeckeCharacterZeroLocus.locusSubgroup S hS R →* (R ⊗[ℚ] D)ˣ × Rˣ),
    (∀ (R : Type) [CommRing R] [Algebra ℚ R], Function.Injective (φ R) ∧
      ∀ z : (R ⊗[ℚ] D)ˣ × Rˣ, GlobalTheory.TorCls.TC D σ β y R z ↔ z ∈ Set.range (φ R)) ∧
    (∀ (R R' : Type) [CommRing R] [Algebra ℚ R] [CommRing R'] [Algebra ℚ R'] (f : R →ₐ[ℚ] R')
      (g : HeckeCharacterZeroLocus.locusSubgroup S hS R) (g' : HeckeCharacterZeroLocus.locusSubgroup S hS R'),
      (g' : GL (Fin N) R') = Units.map (f.toRingHom.mapMatrix : Matrix (Fin N) (Fin N) R →+* Matrix (Fin N) (Fin N) R').toMonoidHom (g : GL (Fin N) R) →
      φ R' g' = (Units.map (Algebra.TensorProduct.map f (AlgHom.id ℚ D)).toRingHom.toMonoidHom (φ R g).1,
        Units.map f.toRingHom.toMonoidHom (φ R g).2)) ∧
    (∀ (R : Type) [CommRing R] [Algebra ℚ R] [TopologicalSpace R] [IsTopologicalRing R],
      letI : TopologicalSpace (R ⊗[ℚ] D) := moduleTopology R (R ⊗[ℚ] D)
      Continuous (φ R))) :
    ∀ (D : Type) [Ring D] [Algebra ℚ D] [FiniteDimensional ℚ D] (σ : D →+* Dᵐᵒᵖ) (β y : D) (p : ℕ) [Fact p.Prime], letI : TopologicalSpace (AfP p ⊗[ℚ] D) := moduleTopology (AfP p) (AfP p ⊗[ℚ] D); letI : TopologicalSpace (ℚ_[p] ⊗[ℚ] D) := moduleTopology ℚ_[p] (ℚ_[p] ⊗[ℚ] D); ∀ U : Subgroup (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)), (∃ O : Set (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)), IsOpen O ∧ 1 ∈ O ∧ ∀ z ∈ O, GlobalTheory.CentCls.TC D σ β y (AfP p) z.1 → GlobalTheory.CentCls.TC D σ β y ℚ_[p] z.2 → z ∈ U) → ∃ S : Finset (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)), ∀ z : ((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ), GlobalTheory.CentCls.TC D σ β y (AfP p) z.1 → GlobalTheory.CentCls.TC D σ β y ℚ_[p] z.2 → ∃ γ : Dˣ × ℚˣ, (γ.1 : D) * β * (σ (γ.1 : D)).unop = algebraMap ℚ D (γ.2 : ℚ) * β ∧ Commute (γ.1 : D) y ∧ ∃ s ∈ S, ∃ u ∈ U, z = GlobalTheory.TorCls.dg D p γ * s * u :=
  fun D _ _ _ σ β y p _ => GlobalTheory.TorCls.Borel.classes_finite hloc GlobalTheory.classNumberFinite_holds D σ β y p

theorem classes_finite :
    ∀ (D : Type) [Ring D] [Algebra ℚ D] [FiniteDimensional ℚ D] (σ : D →+* Dᵐᵒᵖ) (β y : D) (p : ℕ) [Fact p.Prime], letI : TopologicalSpace (AfP p ⊗[ℚ] D) := moduleTopology (AfP p) (AfP p ⊗[ℚ] D); letI : TopologicalSpace (ℚ_[p] ⊗[ℚ] D) := moduleTopology ℚ_[p] (ℚ_[p] ⊗[ℚ] D); ∀ U : Subgroup (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)), (∃ O : Set (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)), IsOpen O ∧ 1 ∈ O ∧ ∀ z ∈ O, GlobalTheory.CentCls.TC D σ β y (AfP p) z.1 → GlobalTheory.CentCls.TC D σ β y ℚ_[p] z.2 → z ∈ U) → ∃ S : Finset (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)), ∀ z : ((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ), GlobalTheory.CentCls.TC D σ β y (AfP p) z.1 → GlobalTheory.CentCls.TC D σ β y ℚ_[p] z.2 → ∃ γ : Dˣ × ℚˣ, (γ.1 : D) * β * (σ (γ.1 : D)).unop = algebraMap ℚ D (γ.2 : ℚ) * β ∧ Commute (γ.1 : D) y ∧ ∃ s ∈ S, ∃ u ∈ U, z = GlobalTheory.TorCls.dg D p γ * s * u :=
  classes_finite_of_locus GlobalTheory.TorLoc.exists_locus

end GlobalTheory.CentCls.Fin
end

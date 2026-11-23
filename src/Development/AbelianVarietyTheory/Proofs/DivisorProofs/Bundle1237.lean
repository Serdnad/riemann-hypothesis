module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BddCpt

theorem bdd_entries_of_isCompact_closure_zpowers : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (t : UL n w),
    IsCompact (closure (Subgroup.zpowers t : Set (UL n w))) →
    ∃ a : w.adicCompletion E, a ≠ 0 ∧ ∀ k : ℤ, ∀ i j, a * (t ^ k).1.1 i j ∈ Ov E w := by
  intro E _ _ _ n w t hK
  have hO : IsOpen ((Ov E w : Set (w.adicCompletion E))) := Valued.isOpen_valuationSubring _
  have hNe : (nhdsWithin (0 : w.adicCompletion E) {0}ᶜ).NeBot := by
    letI : NontriviallyNormedField (w.adicCompletion E) := Valued.toNontriviallyNormedField _ _
    exact NormedField.nhdsNE_neBot 0
  have hev : ∀ᶠ a in nhds (0 : w.adicCompletion E),
      ∀ s ∈ closure (Subgroup.zpowers t : Set (UL n w)), ∀ i j, a * s.1.1 i j ∈ Ov E w := by
    refine hK.eventually_forall_of_forall_eventually fun s _ => ?_
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    have hc : Continuous (fun z : w.adicCompletion E × UL n w => z.1 * z.2.1.1 i j) := by fun_prop
    have h0 : (fun z : w.adicCompletion E × UL n w => z.1 * z.2.1.1 i j) (0, s) ∈ (Ov E w : Set _) := by
      simp only [zero_mul]; exact (Ov E w).zero_mem
    exact hc.continuousAt.preimage_mem_nhds (hO.mem_nhds h0)
  obtain ⟨a, ha, ha0⟩ := ((hev.filter_mono (nhdsWithin_le_nhds (s := ({0}ᶜ : Set (w.adicCompletion E))))).and
    (self_mem_nhdsWithin (s := ({0}ᶜ : Set (w.adicCompletion E))))).exists
  exact ⟨a, ha0, fun k i j => ha _ (subset_closure ⟨k, rfl⟩) i j⟩

end GlobalTheory.BddCpt
end

section

namespace GlobalTheory.DZA.OrbSupp

open GlobalTheory.BCT

variable {G : Type} [Group G] [TopologicalSpace G]

theorem exists_twConj_ne_zero (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) (h : twOrb θ K δ f ≠ 0) :
    ∃ x, f (x⁻¹ * δ * θ x) ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply h
  unfold twOrb
  simp only [hc]
  simp [avg]

theorem twOrb_eq_zero_of_forall (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ)
    (h : ∀ x, f (x⁻¹ * δ * θ x) = 0) : twOrb θ K δ f = 0 := by
  by_contra hne
  obtain ⟨x, hx⟩ := exists_twConj_ne_zero θ K δ f hne
  exact hx (h x)

theorem exists_conj_ne_zero (K : Subgroup G) (γ : G) (f : G → ℂ) (h : twOrb (MonoidHom.id G) K γ f ≠ 0) :
    ∃ x, f (x⁻¹ * γ * x) ≠ 0 :=
  exists_twConj_ne_zero (MonoidHom.id G) K γ f h

theorem twOrb_id_eq_zero_of_forall (K : Subgroup G) (γ : G) (f : G → ℂ) (h : ∀ x, f (x⁻¹ * γ * x) = 0) :
    twOrb (MonoidHom.id G) K γ f = 0 :=
  twOrb_eq_zero_of_forall (MonoidHom.id G) K γ f h

end GlobalTheory.DZA.OrbSupp
end

section

noncomputable section

open NumberField IsDedekindDomain Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open scoped Classical TensorProduct

namespace GlobalTheory.BCT

def tens {G H : Type} (f : G → ℂ) (g : H → ℂ) : G × H → ℂ := fun y => f y.1 * g y.2

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def geomSt2 (a b : ℕ) (S : Set (Pl E)) (l₁ : InfinitePlace E → DomWeight a) (l₂ : InfinitePlace E → DomWeight b)
    (φ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) : ℂ :=
  ∑ᶠ p ∈ {p : E[X] × E[X] | p.1 ∈ Ell E a ∧ p.2 ∈ Ell E b ∧ IsCoprime p.1 p.2},
    kap p.1 * kap p.2 * chW l₁ p.1 * chW l₂ p.2 * ∏ᶠ w ∈ S, stTw2 a b w (atPl w p.1) (atPl w p.2) (φ w)

end GlobalTheory.BCT
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CharpolyInt

theorem charpoly_coeff_det_int {E : Type} [Field E] [NumberField E] {n : ℕ} (w : HeightOneSpectrum (𝓞 E))
    (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (hA : ∀ i j, A i j ∈ w.adicCompletionIntegers E) :
    (∀ k, A.charpoly.coeff k ∈ w.adicCompletionIntegers E) ∧ A.det ∈ w.adicCompletionIntegers E := by
  let M : Matrix (Fin n) (Fin n) (w.adicCompletionIntegers E) := Matrix.of fun i j => ⟨A i j, hA i j⟩
  have hMA : M.map (w.adicCompletionIntegers E).subtype = A := by ext i j; rfl
  refine ⟨fun k => ?_, ?_⟩
  · rw [← hMA, Matrix.charpoly_map, Polynomial.coeff_map]
    exact (M.charpoly.coeff k).2
  · have hdet : A.det = ((M.det : w.adicCompletionIntegers E) : w.adicCompletion E) := by
      rw [← hMA]; exact (RingHom.map_det (w.adicCompletionIntegers E).subtype M).symm
    rw [hdet]; exact M.det.2

theorem entries_int_of_mem_KGL {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)
    (g : GL (Fin n) (w.adicCompletion E)) (hg : g ∈ GlobalTheory.LFun.KGL w (n := n)) :
    (∀ i j, g.1 i j ∈ w.adicCompletionIntegers E) ∧ ∀ i j, (g⁻¹).1 i j ∈ w.adicCompletionIntegers E := by
  simp only [GlobalTheory.LFun.KGL] at hg
  unfold GLint at hg
  obtain ⟨h, rfl⟩ := hg
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · have : (bc (Ov E w).subtype h).1 i j = ((h.1 i j : Ov E w) : w.adicCompletion E) := rfl
    rw [this]; exact (h.1 i j).2
  · have : ((bc (Ov E w).subtype h)⁻¹).1 i j = (((h⁻¹).1 i j : Ov E w) : w.adicCompletion E) := by
      rw [← map_inv]; rfl
    rw [this]; exact ((h⁻¹).1 i j).2

theorem kint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (g : GLw n w),
    g ∈ GlobalTheory.LFun.KGL w (n := n) →
    (∀ k, Valued.v (g.val.charpoly.coeff k) ≤ 1) ∧ Valued.v (g.val.charpoly.coeff 0) = 1 := by
  intro E _ _ _ n w g hg
  obtain ⟨h1, h2⟩ := entries_int_of_mem_KGL w n g hg
  obtain ⟨hc, hd⟩ := charpoly_coeff_det_int w g.val h1
  obtain ⟨-, hd'⟩ := charpoly_coeff_det_int w (g⁻¹).val h2
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hd hd'
  refine ⟨fun k => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hc k), ?_⟩
  have hprod : g.val.det * (g⁻¹).val.det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have hv : Valued.v g.val.det * Valued.v (g⁻¹).val.det = 1 := by rw [← map_mul, hprod, map_one]
  have hdet : Valued.v g.val.det = 1 := by
    refine le_antisymm hd ?_
    calc (1 : _) = Valued.v g.val.det * Valued.v (g⁻¹).val.det := hv.symm
      _ ≤ Valued.v g.val.det * 1 := mul_le_mul' le_rfl hd'
      _ = Valued.v g.val.det := mul_one _
  have h0 : g.val.charpoly.coeff 0 = (-1) ^ Fintype.card (Fin n) * g.val.det := by
    rw [Matrix.det_eq_sign_charpoly_coeff, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
  rw [h0, map_mul, map_pow, Valuation.map_neg, map_one, one_pow, one_mul, hdet]

end GlobalTheory.CharpolyInt
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerTw

variable (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)

theorem continuous_sLoc_spl (v : Pl E) : Continuous (sLoc E v) := by
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (Pl E)) :=
    Filter.le_principal_iff.2 (Set.finite_singleton v).compl_mem_cofinite
  let f : v.adicCompletion E → RestrictedProduct (fun u : Pl E => u.adicCompletion E)
      (fun u => (u.adicCompletionIntegers E : Set (u.adicCompletion E))) (Filter.principal {v}ᶜ) :=
    fun a => ⟨Pi.single v a, fun u hu => by
      rw [Set.mem_setOf_eq, Pi.single_eq_of_ne hu]; exact zero_mem _⟩
  have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.2 (continuous_single v)
  exact (RestrictedProduct.continuous_inclusion hS).comp hf

theorem continuous_locGL_spl (w : Pl E) : Continuous (locGL E n w) :=
  Continuous.units_map _ (continuous_const.add (Continuous.matrix_map continuous_id (continuous_sLoc_spl E w)))

variable {E n}

end GlobalTheory.EulerTw
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GramParity

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem ordL_spec {x : L} (hx : x ≠ 0) :
    Valued.v x = ((Multiplicative.ofAdd (-ordL x) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  have h : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  unfold ordL
  rw [dite_eq_right h]
  simp

theorem ordL_eq_of {x : L} (hx : x ≠ 0) {a : ℤ}
    (h : Valued.v x = ((Multiplicative.ofAdd (-a) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) :
    ordL x = a := by
  have h2 := (ordL_spec hx).symm.trans h
  have h3 := WithZero.coe_injective h2
  simpa using h3

theorem ordL_mul {x y : L} (hx : x ≠ 0) (hy : y ≠ 0) : ordL (x * y) = ordL x + ordL y := by
  apply ordL_eq_of (mul_ne_zero hx hy)
  rw [Valuation.map_mul, ordL_spec hx, ordL_spec hy, ← WithZero.coe_mul, ← ofAdd_add]
  congr 2
  ring

theorem ordL_eq_zero_of_v_one {x : L} (h : Valued.v x = 1) : ordL x = 0 := by
  have hx : x ≠ 0 := by
    intro h0; rw [h0, Valuation.map_zero] at h; exact zero_ne_one h
  apply ordL_eq_of hx
  rw [h]; rfl

theorem ordL_congr {x y : L} (h : Valued.v x = Valued.v y) : ordL x = ordL y := by
  unfold ordL
  simp only [h]

end GlobalTheory.GramParity

namespace GlobalTheory.GramParity

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem gram_eq {n : ℕ} {α : Type} [Fintype α] (σ : L →+* L) (f : α → Fin n → L) :
    (Matrix.of fun i j => ∑ k, σ (f i k) * f j k) =
      (Matrix.of fun i k => f i k).map σ * (Matrix.of fun i k => f i k)ᵀ := by
  ext i j
  simp [Matrix.mul_apply]

theorem coords_eq {n : ℕ} (V : Submodule L (Fin n → L)) {ι : Type} [Fintype ι] [DecidableEq ι]
    (b c : Module.Basis ι L V) :
    (Matrix.of fun i k => (b i : Fin n → L) k) =
      (c.toMatrix b)ᵀ * (Matrix.of fun i k => (c i : Fin n → L) k) := by
  ext i k
  have h := c.sum_repr (b i)
  have h2 := congrArg (fun v : V => (v : Fin n → L) k) h
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h2
  simp [Matrix.mul_apply, Module.Basis.toMatrix_apply, ← h2]

theorem det_gram_change {n : ℕ} (σ : L →+* L) (V : Submodule L (Fin n → L)) {ι : Type} [Fintype ι]
    [DecidableEq ι] (b c : Module.Basis ι L V) :
    (Matrix.of fun i j => ∑ k, σ ((b i : Fin n → L) k) * (b j : Fin n → L) k).det =
      σ (c.toMatrix b).det *
        (Matrix.of fun i j => ∑ k, σ ((c i : Fin n → L) k) * (c j : Fin n → L) k).det *
        (c.toMatrix b).det := by
  rw [gram_eq σ (fun i => (b i : Fin n → L)), gram_eq σ (fun i => (c i : Fin n → L))]
  rw [coords_eq V b c]
  rw [Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc ((of fun i k ↦ ((c i : V) : Fin n → L) k).map σ), ← Matrix.mul_assoc,
    Matrix.det_mul, Matrix.det_mul]
  congr 2
  rw [RingHom.map_det, ← Matrix.det_transpose]
  rfl

end GlobalTheory.GramParity

namespace GlobalTheory.GramParity

theorem gram_parity_gen {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
    (σ : L →+* L) (hσ : ∀ x, Valued.v (σ x) = Valued.v x) (n : ℕ) (V : Submodule L (Fin n → L))
    {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (b : Module.Basis ι L V)
    (c : Module.Basis κ L V)
    (hc : Valued.v (Matrix.of fun i j => ∑ k, σ ((c i : Fin n → L) k) * (c j : Fin n → L) k).det = 1) :
    (-1 : ℂ) ^ ordL (Matrix.of fun i j => ∑ k, σ ((b i : Fin n → L) k) * (b j : Fin n → L) k).det = 1 := by
  set e : ι ≃ κ := b.indexEquiv c
  set c' : Module.Basis ι L V := c.reindex e.symm
  have hc' : (Matrix.of fun i j => ∑ k, σ ((c' i : Fin n → L) k) * (c' j : Fin n → L) k).det =
      (Matrix.of fun i j => ∑ k, σ ((c i : Fin n → L) k) * (c j : Fin n → L) k).det := by
    rw [← Matrix.det_submatrix_equiv_self e]
    congr 1
    ext i j
    simp [c', Module.Basis.reindex_apply]
  have hg1 : Valued.v (Matrix.of fun i j => ∑ k, σ ((c' i : Fin n → L) k) * (c' j : Fin n → L) k).det = 1 := by
    rw [hc', hc]
  have hg0 : (Matrix.of fun i j => ∑ k, σ ((c' i : Fin n → L) k) * (c' j : Fin n → L) k).det ≠ 0 := by
    intro h0; rw [h0, Valuation.map_zero] at hg1; exact zero_ne_one hg1
  have hd : (c'.toMatrix b).det ≠ 0 := by
    have := c'.invertibleToMatrix b
    exact (Matrix.isUnit_det_of_invertible _).ne_zero
  have hσd : σ (c'.toMatrix b).det ≠ 0 := (map_ne_zero σ).mpr hd
  rw [det_gram_change σ V b c', ordL_mul (mul_ne_zero hσd hg0) hd, ordL_mul hσd hg0,
    ordL_eq_zero_of_v_one hg1, ordL_congr (hσ _)]
  have : ordL (c'.toMatrix b).det + 0 + ordL (c'.toMatrix b).det = 2 * ordL (c'.toMatrix b).det := by ring
  rw [this, _root_.zpow_mul]
  norm_num

end GlobalTheory.GramParity

open GlobalTheory.GramParity in
theorem GlobalTheory.GramParity.gram_det_parity : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (σ : w.adicCompletion E →+* w.adicCompletion E),
    (∀ x, Valued.v (σ x) = Valued.v x) → ∀ (n : ℕ) (V : Submodule (w.adicCompletion E) (Fin n → w.adicCompletion E))
    {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (b : Module.Basis ι (w.adicCompletion E) V)
    (c : Module.Basis κ (w.adicCompletion E) V),
    Valued.v (Matrix.of fun i j => ∑ k, σ ((c i : Fin n → w.adicCompletion E) k) * (c j : Fin n → w.adicCompletion E) k).det = 1 →
    (-1 : ℂ) ^ ordL (Matrix.of fun i j => ∑ k, σ ((b i : Fin n → w.adicCompletion E) k) * (b j : Fin n → w.adicCompletion E) k).det = 1 := by
  intro E _ _ w σ hσ n V ι κ _ _ _ _ b c hc
  exact gram_parity_gen σ hσ n V b c hc
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT

theorem ev_int_exsplit {E : Type} [Field E] [NumberField E] (x : E) :
    ∀ᶠ w : Pl E in cofinite, algebraMap E (w.adicCompletion E) x ∈ w.adicCompletionIntegers E :=
  (algebraMap E (FiniteAdeleRing (𝓞 E) E) x).eventually

theorem coeff_zero_ne_zero_of_mem_ell {E : Type} [Field E] [NumberField E] {n : ℕ} {P : E[X]} (hP : P ∈ Ell E n) :
    P.coeff 0 ≠ 0 := by
  intro h0
  obtain ⟨hmon, -, -, hroots⟩ := hP
  let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (S := E) (M := ℂ)).toRingHom
  have hne : P.map τ ≠ 0 := (hmon.map τ).ne_zero
  have hr : (0 : ℂ) ∈ (P.map τ).roots := by
    rw [mem_roots hne, IsRoot.def, eval_map, eval₂_at_zero, h0, map_zero]
  have := hroots τ 0 hr
  simp at this

theorem exists_mat_charpoly {E : Type} [Field E] {n : ℕ} {P : E[X]} (hmon : P.Monic) (hdeg : P.natDegree = n) :
    ∃ M : Matrix (Fin n) (Fin n) E, M.charpoly = P := by
  let pb := AdjoinRoot.powerBasis hmon.ne_zero
  have hdim : pb.dim = n := by rw [AdjoinRoot.powerBasis_dim, hdeg]
  refine ⟨Matrix.reindex (finCongr hdim) (finCongr hdim) (Algebra.leftMulMatrix pb.basis pb.gen), ?_⟩
  rw [Matrix.charpoly_reindex, charpoly_leftMulMatrix, AdjoinRoot.minpoly_powerBasis_gen_of_monic hmon]

theorem exists_int_charpoly_atPl_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
    ∀ P ∈ Ell E n, ∀ᶠ w in cofinite, IsSplitAt w → ∃ γ : UL n w, γ ∈ KL n w ∧ γ.1.val.charpoly = atPl w P := by
  intro E _ _ _ _ n _ P hP
  obtain ⟨M, hM⟩ := exists_mat_charpoly hP.1 hP.2.1
  have hdet : M.det ≠ 0 := by
    rw [Matrix.det_eq_sign_charpoly_coeff, hM]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (coeff_zero_ne_zero_of_mem_ell hP)
  have hev1 : ∀ᶠ w : Pl E in cofinite, ∀ ij : Fin n × Fin n,
      algebraMap E (w.adicCompletion E) (M ij.1 ij.2) ∈ w.adicCompletionIntegers E :=
    Filter.eventually_all.2 fun ij => ev_int_exsplit (M ij.1 ij.2)
  have hev2 := ev_int_exsplit (E := E) M.det⁻¹
  filter_upwards [hev1, hev2] with w hent hinv hs
  let N : Matrix (Fin n) (Fin n) (Ov E w) := fun i j => ⟨_, hent (i, j)⟩
  have hN : (Ov E w).subtype.mapMatrix N = M.map (algebraMap E (w.adicCompletion E)) := by
    ext i j; rfl
  have hdetN : ((N.det : Ov E w) : w.adicCompletion E) = algebraMap E (w.adicCompletion E) M.det := by
    have := RingHom.map_det (Ov E w).subtype N
    rw [hN] at this
    exact this.trans (RingHom.map_det _ M).symm
  have hu : IsUnit N.det := by
    refine isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext ?_⟩
    change ((N.det : Ov E w) : w.adicCompletion E) * algebraMap E (w.adicCompletion E) M.det⁻¹ = 1
    rw [hdetN, ← map_mul, mul_inv_cancel₀ hdet, map_one]
  let g : GL (Fin n) (Ov E w) := ((Matrix.isUnit_iff_isUnit_det N).2 hu).unit
  have hmemU : bc (Ov E w).subtype g ∈ UL n w := by
    simp only [UL, if_pos hs]; exact Subgroup.mem_top _
  refine ⟨⟨_, hmemU⟩, ?_, ?_⟩
  · rw [KL, Subgroup.mem_subgroupOf]
    exact ⟨g, rfl⟩
  · change ((Ov E w).subtype.mapMatrix (g : Matrix (Fin n) (Fin n) (Ov E w))).charpoly = atPl w P
    rw [IsUnit.unit_spec, hN, Matrix.charpoly_map, hM]

end GlobalTheory.BCT
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerTw.Fact

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem mem_KGL_of {w : Pl E} (g : GL (Fin n) (w.adicCompletion E))
    (h1 : ∀ i j, g.1 i j ∈ w.adicCompletionIntegers E) (h2 : ∀ i j, g⁻¹.1 i j ∈ w.adicCompletionIntegers E) :
    g ∈ GlobalTheory.LFun.KGL w (n := n) := by
  have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) (Ov E w) => A.map (Ov E w).subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.mul_inv
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.inv_mul

theorem eventually_mem_KGL (x : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) :
    ∀ᶠ w : Pl E in cofinite, GeneralLinearGroup.map (pLoc E w) x ∈ GlobalTheory.LFun.KGL w (n := n) := by
  have h : ∀ g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E), ∀ᶠ w : Pl E in cofinite,
      ∀ i j, pLoc E w (g.val i j) ∈ w.adicCompletionIntegers E := fun g => by
    simp only [Filter.eventually_all]
    exact fun i j => (g.val i j).2
  filter_upwards [h x, h x⁻¹] with w a b
  exact mem_KGL_of _ a (by rw [← map_inv]; exact b)

end GlobalTheory.EulerTw.Fact
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.BCT.LevOpTmul

theorem finite_supp {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {K : Subgroup G}
    (hK : IsOpen (K : Set G)) {f : G → ℂ} (hf : HasCompactSupport f) : {q : G ⧸ K | f q.out ≠ 0}.Finite := by
  have hc : IsCompact (tsupport f) := hf
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover (fun x : G => (fun y : G => x⁻¹ * y) ⁻¹' (K : Set G))
    (fun x => hK.preimage (continuous_const.mul continuous_id))
    (fun x _ => Set.mem_iUnion.2 ⟨x, by simp [K.one_mem]⟩)
  refine (t.finite_toSet.image (fun x : G => (x : G ⧸ K))).subset ?_
  intro q hq
  have hmem : q.out ∈ tsupport f := subset_tsupport f hq
  obtain ⟨x, hx, hqx⟩ := Set.mem_iUnion₂.1 (ht hmem)
  refine ⟨x, hx, ?_⟩
  conv_rhs => rw [← QuotientGroup.out_eq' q]
  exact QuotientGroup.eq.2 hqx

theorem levOp_apply {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (K K₁ : Subgroup G) (f : G → ℂ) (A : V →ₗ[ℂ] V) (S : Finset (G ⧸ K₁)) (hS : ∀ q : G ⧸ K₁, f q.out ≠ 0 → q ∈ S)
    (v : V) : levOp ρ K K₁ f A v = ((K₁.relIndex K : ℕ) : ℂ)⁻¹ • ∑ q ∈ S, f q.out • ρ q.out (A v) := by
  unfold levOp
  rw [finsum_eq_sum_of_support_subset (s := S)]
  · simp only [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply]
  · intro q hq
    rw [Function.mem_support] at hq
    apply hS
    intro h0
    apply hq
    rw [h0, zero_smul]

theorem term_mk {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (K₁ : Subgroup G) (f : G → ℂ) (hf : ∀ k ∈ K₁, ∀ x, f (x * k) = f x) (w : V) (hw : ∀ k ∈ K₁, ρ k w = w) (g : G) :
    f (g : G ⧸ K₁).out = f g ∧ ρ (g : G ⧸ K₁).out w = ρ g w := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K₁ g
  rw [hk]
  exact ⟨hf k k.2 g, by rw [map_mul, Module.End.mul_apply, hw k k.2]⟩

end GlobalTheory.BCT.LevOpTmul
end

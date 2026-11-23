module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Matrix Filter Topology Polynomial
open scoped ComplexConjugate

namespace PositivityTheory.Rg.Sw.Glob.Vac

variable {n : ℕ}

theorem inG_JJ : InG (JJ n) := by
  unfold InG
  rw [JJ_conjTranspose, Matrix.mul_assoc, JJ_sq, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_one, neg_neg]

theorem nU_mul (b c : Matrix (Fin n) (Fin n) ℂ) : nU b * nU c = nU (b + c) := by
  simp [nU, fromBlocks_multiply, add_comm]

theorem nU_zero : nU (0 : Matrix (Fin n) (Fin n) ℂ) = 1 := by simp [nU, fromBlocks_one]

theorem inG_nU {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) : InG (nU b) := by
  unfold InG; simp [nU, JJ, fromBlocks_conjTranspose, fromBlocks_multiply, hb.eq]

def jjE : GR n := ⟨⟨JJ n, -JJ n, by rw [Matrix.mul_neg, JJ_sq, neg_neg], by rw [Matrix.neg_mul, JJ_sq, neg_neg]⟩, inG_JJ⟩

def nuE (b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsHermitian) : GR n :=
  ⟨⟨nU b, nU (-b), by rw [nU_mul, add_neg_cancel, nU_zero], by rw [nU_mul, neg_add_cancel, nU_zero]⟩, inG_nU hb⟩

def nbar (s : ℝ) : M2 n := fromBlocks 1 0 ((s : ℂ) • 1) 1

theorem nbar_mul (s t : ℝ) : nbar (n := n) s * nbar t = nbar (s + t) := by
  simp [nbar, fromBlocks_multiply, add_smul, add_comm]

theorem nbar_zero : nbar (n := n) 0 = 1 := by simp [nbar, fromBlocks_one]

theorem inG_nbar (s : ℝ) : InG (nbar (n := n) s) := by
  unfold InG
  simp [nbar, JJ, fromBlocks_conjTranspose, fromBlocks_multiply, Matrix.conjTranspose_smul, Complex.conj_ofReal]

def nbE (s : ℝ) : GR n :=
  ⟨⟨nbar s, nbar (-s), by rw [nbar_mul, add_neg_cancel, nbar_zero], by rw [nbar_mul, neg_add_cancel, nbar_zero]⟩, inG_nbar s⟩

theorem nbE_zero : nbE (n := n) 0 = 1 := Subtype.ext (Units.ext nbar_zero)

theorem cont_nbar : Continuous (nbar (n := n)) := by
  unfold nbar
  exact Continuous.matrix_fromBlocks continuous_const continuous_const
    (Complex.continuous_ofReal.smul continuous_const) continuous_const

theorem cont_nbE : Continuous (nbE (n := n)) := by
  refine Continuous.subtype_mk ?_ _
  refine Units.continuous_iff.mpr ⟨cont_nbar, ?_⟩
  exact cont_nbar.comp continuous_neg

theorem lower_left_block_mul_lowering (g : GR n) (s : ℝ) :
    (mR (g * nbE s)).toBlocks₂₁ = (mR g).toBlocks₂₁ + (s : ℂ) • (mR g).toBlocks₂₂ := by
  rw [mR_mul]
  conv_lhs => rw [← fromBlocks_toBlocks (mR g)]
  show (fromBlocks _ _ _ _ * nbar s).toBlocks₂₁ = _
  simp [nbar, fromBlocks_multiply]

theorem finite_bad (g : GR n) :
    {s : ℝ | ((mR g).toBlocks₂₁ + (s : ℂ) • (mR g).toBlocks₂₂).det = 0}.Finite := by
  set C := (mR g).toBlocks₂₁
  set D := (mR g).toBlocks₂₂
  set P : Polynomial ℂ := det (C.map Polynomial.C + (Polynomial.X : Polynomial ℂ) • D.map Polynomial.C) with hP
  have hev : ∀ z : ℂ, P.eval z = (C + z • D).det := by
    intro z
    rw [hP, ← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp
    ring
  have hP0 : P ≠ 0 := by
    intro h0
    have hz := hev Complex.I
    rw [h0, Polynomial.eval_zero] at hz
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hz.symm
    apply hv
    apply vec_zero g (-Complex.I) (by simp) v
    have hm : (-Complex.I) • C + D = (-Complex.I) • (C + Complex.I • D) := by
      rw [smul_add, smul_smul]
      simp
    rw [hm, Matrix.vecMul_smul, hv0, smul_zero]
  apply ((P.roots.toFinset.finite_toSet).preimage Complex.ofReal_injective.injOn).subset
  intro s hs
  simp only [Set.mem_setOf_eq] at hs
  simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hP0,
    Polynomial.IsRoot, hev]
  exact hs

theorem dense_cell : Dense {g : GR n | ((mR g).toBlocks₂₁).det ≠ 0} := by
  intro g
  have hT : Tendsto (fun s : ℝ => g * nbE s) (𝓝[≠] 0) (𝓝 g) := by
    have hc : Continuous fun s : ℝ => g * nbE s := continuous_const.mul cont_nbE
    have h := hc.tendsto 0
    rw [nbE_zero, mul_one] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto hT ?_
  have hfin := finite_bad g
  have hZ : IsClosed ({s : ℝ | ((mR g).toBlocks₂₁ + (s : ℂ) • (mR g).toBlocks₂₂).det = 0} \ {0}) :=
    (hfin.subset Set.sdiff_subset).isClosed
  have h0 : (0 : ℝ) ∉ ({s : ℝ | ((mR g).toBlocks₂₁ + (s : ℂ) • (mR g).toBlocks₂₂).det = 0} \ {0}) := by simp
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hZ.isOpen_compl.mem_nhds h0), self_mem_nhdsWithin] with s hs hs0
  show ((mR (g * nbE s)).toBlocks₂₁).det ≠ 0
  rw [lower_left_block_mul_lowering]
  intro hdet
  exact hs ⟨hdet, hs0⟩

theorem bigcell (g : GR n) (hγ : ((mR g).toBlocks₂₁).det ≠ 0) :
    ∃ (y h : GR n) (b : Matrix (Fin n) (Fin n) ℂ), (mR y).toBlocks₂₁ = 0 ∧ b.IsHermitian ∧ mR h = JJ n * nU b ∧
      g = y * h := by
  set C := (mR g).toBlocks₂₁ with hC
  set D := (mR g).toBlocks₂₂ with hD
  have hu : IsUnit C.det := isUnit_iff_ne_zero.mpr hγ
  have huH : IsUnit Cᴴ.det := by
    rw [det_conjTranspose]
    exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hγ)
  have hb : (C⁻¹ * D).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [conjTranspose_mul, conjTranspose_nonsing_inv]
    calc Dᴴ * Cᴴ⁻¹ = C⁻¹ * (C * Dᴴ) * Cᴴ⁻¹ := by rw [nonsing_inv_mul_cancel_left C _ hu]
      _ = C⁻¹ * (D * Cᴴ) * Cᴴ⁻¹ := by rw [hC, hD, lagr g]
      _ = C⁻¹ * D := by rw [← Matrix.mul_assoc, mul_nonsing_inv_cancel_right Cᴴ _ huH]
  refine ⟨g * (jjE * nuE (C⁻¹ * D) hb)⁻¹, jjE * nuE (C⁻¹ * D) hb, C⁻¹ * D, ?_, hb, ?_, by group⟩
  · have hinv : mR (jjE * nuE (C⁻¹ * D) hb)⁻¹ = nU (-(C⁻¹ * D)) * (-JJ n) := by
      rw [_root_.mul_inv_rev, mR_mul]
      rfl
    rw [mR_mul, hinv]
    conv_lhs => rw [← fromBlocks_toBlocks (mR g)]
    simp [nU, JJ, fromBlocks_multiply, fromBlocks_neg, ← hC, ← hD]
    rw [mul_nonsing_inv_cancel_left C D hu, neg_add_cancel]
  · rw [mR_mul]
    rfl

end PositivityTheory.Rg.Sw.Glob.Vac
end
end

section

noncomputable section

set_option linter.unusedSectionVars false

open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GenFinLocAH

variable {R S : Type} [CommRing R] [CommRing S] {n : ℕ}

def bf (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R :=
  M.submatrix finSumFinEquiv finSumFinEquiv

theorem bf_mul (M N : Matrix (Fin (n + n)) (Fin (n + n)) R) : bf (M * N) = bf M * bf N := by
  unfold bf; exact (Matrix.submatrix_mul_equiv M N _ _ _).symm

theorem block_matrix_to_fromBlocks (a b c d : Matrix (Fin n) (Fin n) R) : bf (GlobalTheory.StdUnn.blk4 a b c d) = fromBlocks a b c d := by
  unfold bf GlobalTheory.StdUnn.blk4; simp [Matrix.submatrix_submatrix]

theorem blkDm_eq (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : blkDm M = (bf M).toBlocks₂₂ := rfl

theorem bf_map (f : R →+* S) (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : bf (M.map f) = (bf M).map f := rfl

theorem bf_one : bf (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) = 1 := Matrix.submatrix_one_equiv _

theorem bf_injective : Function.Injective (bf : Matrix (Fin (n + n)) (Fin (n + n)) R → _) := by
  intro M N h
  ext i j
  have := congrFun (congrFun h (finSumFinEquiv.symm i)) (finSumFinEquiv.symm j)
  simpa [bf] using this

theorem block_matrix_one : GlobalTheory.StdUnn.blk4 (1 : Matrix (Fin n) (Fin n) R) 0 0 1 = 1 :=
  bf_injective (by rw [block_matrix_to_fromBlocks, bf_one, fromBlocks_one])

theorem blkDm_map (f : R →+* S) (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : (blkDm M).map f = blkDm (M.map f) := rfl

theorem det_map (f : R →+* S) (M : Matrix (Fin n) (Fin n) R) : f M.det = (M.map f).det := by
  rw [RingHom.map_det]; rfl

theorem block_matrix_map (f : R →+* S) (a b c d : Matrix (Fin n) (Fin n) R) :
    (GlobalTheory.StdUnn.blk4 a b c d).map f = GlobalTheory.StdUnn.blk4 (a.map f) (b.map f) (c.map f) (d.map f) :=
  bf_injective (by rw [bf_map, block_matrix_to_fromBlocks, block_matrix_to_fromBlocks, fromBlocks_map])

theorem eI_map (f : R →+* S) (I : Finset (Fin n)) : (eI I : Matrix (Fin n) (Fin n) R).map f = eI I := by
  ext i j; simp only [eI, map_apply, diagonal_apply]; split_ifs <;> simp

theorem wIm_map (f : R →+* S) (I : Finset (Fin n)) : (wIm I : Matrix (Fin (n + n)) (Fin (n + n)) R).map f = wIm I := by
  unfold wIm; rw [block_matrix_map]; simp [Matrix.map_sub, Matrix.map_one, Matrix.map_neg, eI_map]

theorem standard_symplectic_matrix_map (f : R →+* S) : (J2 R n).map f = J2 S n := by
  unfold J2; rw [block_matrix_map]; simp [Matrix.map_one, Matrix.map_neg]

theorem cT_map (σ : R →+* R) (σ' : S →+* S) (f : R →+* S) (hf : ∀ x, f (σ x) = σ' (f x)) {m p : Type}
    (M : Matrix m p R) : (Formalism.UG.cT σ M).map f = Formalism.UG.cT σ' (M.map f) := by
  ext i j; simp [Formalism.UG.cT, hf]

theorem isUnit_of (σ : R →+* R) (𝔪 : Ideal R) (horb : ∀ 𝔫 : Ideal R, 𝔫.IsMaximal → 𝔫 = 𝔪 ∨ 𝔫 = 𝔪.comap σ)
    (z : R) (h1 : z ∉ 𝔪) (h2 : σ z ∉ 𝔪) : IsUnit z := by
  by_contra hz
  obtain ⟨𝔫, h𝔫, hz𝔫⟩ := Ideal.exists_le_maximal (Ideal.span {z}) (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hz' : z ∈ 𝔫 := hz𝔫 (Ideal.subset_span rfl)
  rcases horb 𝔫 h𝔫 with rfl | rfl
  · exact h1 hz'
  · exact h2 hz'

end PositivityTheory.Rg.Sw.Glob.GenFinLocAH
end
end

section

noncomputable section

open Matrix Topology

namespace PositivityTheory.Rg.Sw.Glob.DenseP

variable {n : ℕ}

theorem inG_nUh {b : Matrix (Fin n) (Fin n) ℂ} (hb : bᴴ = b) : InG (nU b) := by
  simp only [InG, nU, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hb]
  simp

theorem inG_mL {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsUnit A.det) : InG (fromBlocks A 0 0 (A⁻¹)ᴴ) := by
  have h1 : Aᴴ * (A⁻¹)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul _ hA, Matrix.conjTranspose_one]
  have h2 : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul _ hA
  simp only [InG, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_zero]
  simp [h1, h2]

def hpart (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℂ) • (A + Aᴴ)

theorem hpart_herm (A : Matrix (Fin n) (Fin n) ℂ) : (hpart A)ᴴ = hpart A := by
  simp only [hpart, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose]
  rw [add_comm]
  congr 1
  simp

theorem hpart_of_herm {b : Matrix (Fin n) (Fin n) ℂ} (hb : bᴴ = b) : hpart b = b := by
  rw [hpart, hb, ← two_smul ℂ b, smul_smul]; norm_num

def nuE (A : Matrix (Fin n) (Fin n) ℂ) : GR n := mkGR (nU (hpart A)) (inG_nUh (hpart_herm A))

theorem continuous_hpart : Continuous (hpart (n := n)) := by
  have h : Continuous fun A : Matrix (Fin n) (Fin n) ℂ => A + Aᴴ :=
    (continuous_id (X := Matrix (Fin n) (Fin n) ℂ)).add (continuous_id (X := Matrix (Fin n) (Fin n) ℂ)).matrix_conjTranspose
  exact h.const_smul (1 / 2 : ℂ)

theorem nU_mul_neg (b : Matrix (Fin n) (Fin n) ℂ) : nU b * nU (-b) = 1 := by
  simp [nU, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]

theorem continuous_nU : Continuous (nU (n := n)) :=
  Continuous.matrix_fromBlocks continuous_const continuous_id continuous_const continuous_const

theorem continuous_nuE : Continuous (nuE (n := n)) := by
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · show Continuous fun A => nU (hpart A)
    exact continuous_nU.comp continuous_hpart
  · show Continuous fun A : Matrix (Fin n) (Fin n) ℂ => (nU (hpart A))⁻¹
    have e : (fun A : Matrix (Fin n) (Fin n) ℂ => (nU (hpart A))⁻¹) = fun A => nU (-hpart A) := by
      funext A
      exact Matrix.inv_eq_right_inv (nU_mul_neg _)
    rw [e]
    exact continuous_nU.comp continuous_hpart.neg


open Classical in
def mlE (A : Matrix (Fin n) (Fin n) ℂ) : GR n :=
  if h : IsUnit A.det then mkGR (fromBlocks A 0 0 (A⁻¹)ᴴ) (inG_mL h) else 1

theorem mlE_of {A : Matrix (Fin n) (Fin n) ℂ} (h : IsUnit A.det) :
    mlE A = mkGR (fromBlocks A 0 0 (A⁻¹)ᴴ) (inG_mL h) := by
  unfold mlE; exact dif_pos h

theorem isOpen_unitDet : IsOpen {A : Matrix (Fin n) (Fin n) ℂ | IsUnit A.det} := by
  have : {A : Matrix (Fin n) (Fin n) ℂ | IsUnit A.det} = (fun A : Matrix (Fin n) (Fin n) ℂ => A.det) ⁻¹' {z | z ≠ 0} :=
    Set.ext fun A => isUnit_iff_ne_zero
  rw [this]
  exact isOpen_ne.preimage (Continuous.matrix_det (continuous_id (X := Matrix (Fin n) (Fin n) ℂ)))

theorem continuousOn_inv_mat : ContinuousOn (fun A : Matrix (Fin n) (Fin n) ℂ => A⁻¹) {A | IsUnit A.det} := by
  have e : (fun A : Matrix (Fin n) (Fin n) ℂ => A⁻¹) = fun A => (A.det)⁻¹ • A.adjugate := by
    funext A; rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [e]
  have h1 : ContinuousOn (fun A : Matrix (Fin n) (Fin n) ℂ => (A.det)⁻¹) {A | IsUnit A.det} :=
    ContinuousOn.inv₀ (Continuous.matrix_det (continuous_id (X := Matrix (Fin n) (Fin n) ℂ))).continuousOn
      fun A hA => isUnit_iff_ne_zero.1 hA
  have h2 : Continuous fun A : Matrix (Fin n) (Fin n) ℂ => A.adjugate :=
    Continuous.matrix_adjugate (continuous_id (X := Matrix (Fin n) (Fin n) ℂ))
  exact h1.smul h2.continuousOn

theorem inv_mL {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsUnit A.det) :
    (fromBlocks A 0 0 (A⁻¹)ᴴ)⁻¹ = fromBlocks A⁻¹ 0 0 Aᴴ := by
  refine Matrix.inv_eq_right_inv ?_
  have h1 : (A⁻¹)ᴴ * Aᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hA, Matrix.conjTranspose_one]
  rw [Matrix.fromBlocks_multiply]
  simp [Matrix.mul_nonsing_inv _ hA, h1, ← Matrix.fromBlocks_one]

theorem continuousOn_mlE : ContinuousOn (mlE (n := n)) {A | IsUnit A.det} := by
  have hind : Topology.IsInducing (fun g : GR n => Units.embedProduct _ (g : GL (Fin n ⊕ Fin n) ℂ)) :=
    Units.isEmbedding_embedProduct.isInducing.comp Topology.IsInducing.subtypeVal
  rw [hind.continuousOn_iff]
  have hi := continuousOn_inv_mat (n := n)
  have hc : ContinuousOn (fun A : Matrix (Fin n) (Fin n) ℂ =>
      (fromBlocks A 0 0 (A⁻¹)ᴴ, MulOpposite.op (fromBlocks A⁻¹ 0 0 Aᴴ))) {A | IsUnit A.det} := by
    rw [continuousOn_iff_continuous_restrict]
    have hi' : Continuous fun A : {A : Matrix (Fin n) (Fin n) ℂ | IsUnit A.det} => A.1⁻¹ := hi.restrict
    refine Continuous.prodMk ?_ ?_
    · exact Continuous.matrix_fromBlocks continuous_subtype_val continuous_const continuous_const
        hi'.matrix_conjTranspose
    · exact MulOpposite.continuous_op.comp (Continuous.matrix_fromBlocks hi' continuous_const continuous_const
        continuous_subtype_val.matrix_conjTranspose)
  refine ContinuousOn.congr hc fun A hA => ?_
  simp only [Function.comp_apply, mlE_of hA]
  show ((fromBlocks A 0 0 (A⁻¹)ᴴ), MulOpposite.op (fromBlocks A 0 0 (A⁻¹)ᴴ)⁻¹) = _
  rw [inv_mL hA]

theorem nuE_mem_closure {K : Type} [Field K] (τ : K →+* ℂ) (hτ : DenseRange τ) (A : Matrix (Fin n) (Fin n) ℂ) :
    nuE A ∈ closure (Set.range fun e : Matrix (Fin n) (Fin n) K => nuE (e.map τ)) := by
  have hd : DenseRange (fun e : Matrix (Fin n) (Fin n) K => e.map τ) :=
    DenseRange.piMap fun _ => DenseRange.piMap fun _ => hτ
  have h1 : nuE A ∈ nuE '' closure (Set.range fun e : Matrix (Fin n) (Fin n) K => e.map τ) := by
    rw [hd.closure_range]; exact ⟨A, trivial, rfl⟩
  have h2 := image_closure_subset_closure_image continuous_nuE h1
  rwa [← Set.range_comp] at h2

theorem mlE_mem_closure {K : Type} [Field K] (τ : K →+* ℂ) (hτ : DenseRange τ) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : IsUnit A.det) :
    mlE A ∈ closure (mlE '' ({A | IsUnit A.det} ∩ Set.range fun e : Matrix (Fin n) (Fin n) K => e.map τ)) := by
  have hd : DenseRange (fun e : Matrix (Fin n) (Fin n) K => e.map τ) :=
    DenseRange.piMap fun _ => DenseRange.piMap fun _ => hτ
  have hc : ContinuousAt (mlE (n := n)) A := (continuousOn_mlE (n := n)).continuousAt (isOpen_unitDet.mem_nhds hA)
  rw [mem_closure_iff_nhds]
  intro t ht
  have h1 : mlE ⁻¹' t ∩ {A | IsUnit A.det} ∈ 𝓝 A := Filter.inter_mem (hc ht) (isOpen_unitDet.mem_nhds hA)
  obtain ⟨U, hU, hUo, hAU⟩ := mem_nhds_iff.1 h1
  obtain ⟨e, he⟩ := hd.exists_mem_open hUo ⟨A, hAU⟩
  exact ⟨mlE (e.map τ), (hU he).1, e.map τ, ⟨(hU he).2, e, rfl⟩, rfl⟩

end PositivityTheory.Rg.Sw.Glob.DenseP
end
end

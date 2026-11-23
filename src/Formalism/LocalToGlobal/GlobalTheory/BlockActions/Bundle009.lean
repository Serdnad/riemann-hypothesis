module

public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.Bundle005
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.Bundle006
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.Bundle008
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.Bundle007
import Formalism.LocalToGlobal.GlobalTheory.Bundle002
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle004
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.Bundle003
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.NfAllSmulReB
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalToGlobal.HermitianForms.Bundle004
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.InterlaceDifferenceShiftInvariant
public import Formalism.SharpRestriction.GlobalSchurBounds.FiniteModelOfAdmissibleTransports
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

@[expose] public section

section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms NumberField Formalism.UG Matrix
open scoped TensorProduct
open IsDedekindDomain

theorem unitary_of_hform {E : Type} [Field E] {n : ℕ} (σ : E →+* E) (J δ : Matrix (Fin n) (Fin n) E)
    (h : ∀ x y, hform σ J (δ *ᵥ x) (δ *ᵥ y) = hform σ J x y) : cT σ δ * J * δ = J := by
  ext a b
  have h1 := h (Pi.single a 1) (Pi.single b 1)
  rw [Formalism.L2.GlobalTheoryTheory.Comp.hform_mulVec_rect] at h1
  simpa [hform, Pi.single_apply, apply_ite, ite_mul, mul_ite, Finset.sum_ite_eq', Finset.sum_ite_eq] using h1

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem isUnit_of_extE (Tf : FormsTiedSym D u Ch chOf) (δ : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (Γ : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E) (hΓ : IsUnit Γ.det)
    (hE : IsExt D Tf.til.z0 (RingHom.id D.host.E) δ Γ) : IsUnit δ.det := by
  obtain ⟨P, hP1, -⟩ := exists_projP Tf
  have hm : (iXm D).map (RingHom.id D.host.E) = iXm D := by ext i j; rfl
  have h1 : HMul.hMul Γ (iXm D) = HMul.hMul (iXm D) δ := by have := hE.1; rw [hm] at this; exact this
  have hQ : HMul.hMul (HMul.hMul Γ⁻¹ (iXm D)) δ = iXm D := by
    rw [Matrix.mul_assoc, ← h1, ← Matrix.mul_assoc, nonsing_inv_mul _ hΓ, Matrix.one_mul]
  have hl : HMul.hMul (HMul.hMul P (HMul.hMul Γ⁻¹ (iXm D))) δ = 1 := by
    rw [Matrix.mul_assoc, hQ, hP1]
  exact Matrix.isUnit_det_of_left_inverse hl



theorem til_injective (Tf : FormsTiedSym D u Ch chOf)
    (hSD : ∀ c, dualSet (sigD D : D.host.E →+* D.host.E) (gramP D) (Tf.clsP.lat c) = (Tf.clsP.lat c : Set (Fin (D.R.N D.R.m - 1) → D.host.E)))
    (hdeg : Module.finrank ℚ D.host.E < (D.mem u).A.T - 1) (v : (D.mem u).A.vT) :
    Function.Injective (D.fm u).til := by
  intro c c' h
  obtain ⟨δ, k, G, hδE, hδi, hkE, hG, hy⟩ := til_eq_level Tf (crdFacts_of Tf) hSD hdeg v c c' h
  have hku := lev_isUnit Tf k G hkE
  have hΓ : IsUnit ((Tf.til.ga c').1.1 * ((Tf.til.ga c)⁻¹).1.1).det := by
    rw [← Units.val_mul]
    exact (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)
  have hδu := isUnit_of_extE Tf δ _ hΓ hδE
  set Δ : GL (Fin (D.R.N D.R.m - 1)) D.host.E := ((Matrix.isUnit_iff_isUnit_det δ).mpr hδu).unit with hΔdef
  have hΔv : (Δ : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E) = δ := IsUnit.unit_spec _
  have hΔ : Δ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramP D) := by
    show cT _ (Δ : Matrix _ _ _) * gramP D * (Δ : Matrix _ _ _) = gramP D
    rw [hΔv]; exact unitary_of_hform _ _ _ hδi
  set K : GL (Fin (D.R.N D.R.m - 1)) (D.host.E ⊗[D.host.F] (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := ((Matrix.isUnit_iff_isUnit_det k).mpr hku).unit with hKdef
  have hKv : K.1 = k := IsUnit.unit_spec _
  have hK : K ∈ Tf.clsP.lev.U := lev_mem Tf K G (by rw [hKv]; exact hkE) hG
  have hKU : K ∈ UPts (sigD D) (gramP D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := ((Tf.clsP.lev.U_eq K).1 hK).1
  have hc : (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)).comp (sigD D : D.host.E →+* D.host.E) =
      (sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)).comp (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
    ext e
    simp [sigR, inclE, Algebra.TensorProduct.includeLeftRingHom_apply]
  have hrU : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) Δ ∈ UPts (sigD D) (gramP D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
    Formalism.UG.P.base_change_mem_holds _ _ _ _ _ _ hc _ Δ hΔ
  apply Tf.clsP.y_bij.1
  show (Quotient.mk'' (Tf.clsP.y c) : Cls Tf.clsP.lev) = Quotient.mk'' (Tf.clsP.y c')
  apply (@DoubleCoset.eq _ _ _ _ _ _).2
  refine ⟨⟨_, hrU⟩, ?_, ⟨K⁻¹, inv_mem hKU⟩, ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨Δ, hΔ, rfl⟩)
  · exact Subgroup.mem_subgroupOf.2 (inv_mem hK)
  · apply Subtype.ext
    apply Units.ext
    have hKi : k * (K⁻¹).1 = 1 := by
      rw [← hKv, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hbc : ((bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) Δ : GL _ _) : Matrix _ _ _) = δ.map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
      rw [← hΔv]; rfl
    have e : (Tf.clsP.y c').1.1 = δ.map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) * (Tf.clsP.y c).1.1 * (K⁻¹).1 := by
      rw [← hy, Matrix.mul_assoc, hKi, Matrix.mul_one]
    rw [e, ← hbc]
    rfl

theorem class_injective_of_degree
    (hSD : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf),
      ∀ c, dualSet (sigD D : D.host.E →+* D.host.E) (gramP D) (Tf.clsP.lat c) = (Tf.clsP.lat c : Set (Fin (D.R.N D.R.m - 1) → D.host.E)))
    (hdeg : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i), FormsTiedSym D u Ch chOf →
      Module.finrank ℚ D.host.E < (D.mem u).A.T - 1)
    (hv : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i), FormsTiedSym D u Ch chOf →
      Nonempty (D.mem u).A.vT) :
    ClassMapInjective := fun D u Ch chOf Tf =>
  til_injective Tf (hSD D u Ch chOf Tf) (hdeg D u Ch chOf Tf) (hv D u Ch chOf Tf).some

theorem vT_nonempty (D : D7) (u : D.what₂.Word) : Nonempty (D.mem u).A.vT := by
  rw [← Fintype.card_pos_iff, (D.mem u).A.card_vT]
  simp only [Ranks.f, Ranks.n]
  exact Nat.mul_pos (by decide) D.R.toFrame.ord_pos

theorem classMapInjective_of_finrank_lt
    (hSD : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf),
      ∀ c, dualSet (sigD D : D.host.E →+* D.host.E) (gramP D) (Tf.clsP.lat c) = (Tf.clsP.lat c : Set (Fin (D.R.N D.R.m - 1) → D.host.E)))
    (hdeg : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i), FormsTiedSym D u Ch chOf →
      Module.finrank ℚ D.host.E < (D.mem u).A.T - 1) :
    ClassMapInjective :=
  class_injective_of_degree hSD hdeg (fun D u _ _ _ => vT_nonempty D u)

end Formalism.L2.GlobalTheoryTheory.Br
end
end

section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Matrix
open scoped ComplexOrder

variable {D : D7}

theorem sig_at (ι : D.host.E →+* ℂ) (x : D.host.E) : ι (sigD D x) = starRingEnd ℂ (ι x) :=
  D.sp.cm.cmUnram.2.1 ι x

theorem map_cT_at {m n : Type} (ι : D.host.E →+* ℂ) (M : Matrix m n D.host.E) :
    ((M.map (sigD D : D.host.E →+* D.host.E))ᵀ).map ι = (M.map ι)ᴴ := by
  ext i j
  simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply, RingHom.coe_coe]
  rw [sig_at]
  rfl

theorem gramN_posDef_at {Ch : ℕ → Type} {u : D.what₂.Word} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (Tf : FormsTiedSym D u Ch chOf)
    (ι : D.host.E →+* ℂ) : ((gramN D D.R.m le_rfl).map ι).PosDef := by
  obtain ⟨C, hC, -, -⟩ := (Tf.val D.R.m le_rfl (Or.inr rfl)).de
  have hC' : ((C.1.map (sigD D : D.host.E →+* D.host.E))ᵀ * C.1) = gramN D D.R.m le_rfl := hC
  set A : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) ℂ := C.1.map ι with hA
  have hG : (gramN D D.R.m le_rfl).map ι = Aᴴ * A := by
    rw [← hC', Matrix.map_mul, map_cT_at, hA]
  have hinj : Function.Injective A.mulVec := by
    intro x y hxy
    have hCi : IsUnit C.1.det := (Matrix.isUnit_iff_isUnit_det _).mp C.isUnit
    have h1 : (C.1⁻¹ * C.1).map ι = 1 := by
      rw [Matrix.nonsing_inv_mul _ hCi, Matrix.map_one _ (map_zero _) (map_one _)]
    have h2 := congrArg (fun v => ((C.1⁻¹).map ι) *ᵥ v) hxy
    simp only [Matrix.mulVec_mulVec, hA, ← Matrix.map_mul, h1, Matrix.one_mulVec] at h2
    exact h2
  rw [hG]
  exact Matrix.PosDef.conjTranspose_mul_self A hinj

theorem gramP_posDef_at {Ch : ℕ → Type} {u : D.what₂.Word} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (Tf : FormsTiedSym D u Ch chOf)
    (ι : D.host.E →+* ℂ) : ((gramP D).map ι).PosDef := by
  obtain ⟨C, hC, -, -⟩ := (Tf.val D.R.m le_rfl (Or.inr rfl)).de
  have hC' : ((C.1.map (sigD D : D.host.E →+* D.host.E))ᵀ * C.1) = gramN D D.R.m le_rfl := hC
  obtain ⟨L, hL⟩ := iXm_leftInv D
  set A : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m - 1)) ℂ := (C.1 * iXm D).map ι with hA
  have hG : (gramP D).map ι = Aᴴ * A := by
    have e1 : ((iXm D).map (sigD D : D.host.E →+* D.host.E))ᵀ * (((C.1).map (sigD D : D.host.E →+* D.host.E))ᵀ * C.1) * iXm D =
        ((C.1 * iXm D).map (sigD D : D.host.E →+* D.host.E))ᵀ * (C.1 * iXm D) := by
      rw [Matrix.map_mul, Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
    rw [gramP_eq, ← hC', e1, Matrix.map_mul, map_cT_at, hA]
  have hinj : Function.Injective A.mulVec := by
    intro x y hxy
    have hCi : IsUnit C.1.det := (Matrix.isUnit_iff_isUnit_det _).mp C.isUnit
    have h1 : ((L * C.1⁻¹) * (C.1 * iXm D)).map ι = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc C.1⁻¹, Matrix.nonsing_inv_mul _ hCi, Matrix.one_mul, hL,
        Matrix.map_one _ (map_zero _) (map_one _)]
    have h2 := congrArg (fun v => ((L * C.1⁻¹).map ι) *ᵥ v) hxy
    simp only [Matrix.mulVec_mulVec, hA, ← Matrix.map_mul, h1, Matrix.one_mulVec] at h2
    exact h2
  rw [hG]
  exact Matrix.PosDef.conjTranspose_mul_self A hinj

theorem framesAt : FramesAt := by
  intro D u Ch chOf Tf s
  constructor
  · have h := fun τ => exists_on_of_posDef (gramC (gramN D D.R.m le_rfl) (embS D s) τ) (gramN_posDef_at Tf (embS D s τ))
    choose o ho1 ho2 using h
    exact ⟨⟨o, ho1⟩, fun τ => Or.inl (ho2 τ)⟩
  · have h := fun τ => exists_on_of_posDef (gramC (gramP D) (embS D s) τ) (gramP_posDef_at Tf (embS D s τ))
    choose o ho1 ho2 using h
    exact ⟨⟨o, ho1⟩, fun τ => Or.inl (ho2 τ)⟩

theorem norm_bound_of_classes (h1 : ClassMapInjective) (h2 : StabiliserMapBijective) (hC : NormClsAt) : NormBoundAtInfinity :=
  norm_bound_of_classes_frames h1 h2 framesAt hC

end Formalism.L2.GlobalTheoryTheory.Br
end
end

section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open MvPolynomial Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Matrix Formalism.UG

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem brOne_gFull (Tf : FormsTiedSym D u Ch chOf) (τ : D.what₂.Tau) (g : GL (Fin (D.R.N D.R.m - 1)) ℂ)
    (f : MvPolynomial (Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ) :
    Formalism.L2.Ker.brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) (sqAct ℂ _ (lamTr D u τ) (gFull D u g) f) =
      (((sqrtT D u) ^ ((D.fm u).deg τ) : ℂˣ) : ℂ) •
        sqAct ℂ _ (sgTr D u τ) g (Formalism.L2.Ker.brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) f) := by
  have hI0 := interlaceTr D u (sg_interlace Tf.valP) τ
  have hS := Formalism.L2.Ker.sameShiftTr D u τ hI0
  have hI := (Formalism.L2.Ker.interlace_iff _ _ (Nm_succ D.R)).1 hI0
  unfold gFull
  rw [(factSqActMul ℂ _ _ _ _ f).1, Formalism.L2.Ker.brOne_sqAct _ _ _ hS g _, Formalism.L2.Ker.brOne_last _ _ _ hI _ f, deg_eq_degZ]
  unfold sqAct
  rw [map_smul, smul_comm]

theorem transpose_gFull_eq_dOT_of_eq_transpose (o' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ) (g : GL (Fin (D.R.N D.R.m - 1)) ℂ)
    (hg : (g : Matrix _ _ ℂ) = o'ᵀ) : ((gFull D u g : GL (Fin (D.R.N D.R.m)) ℂ) : Matrix _ _ ℂ)ᵀ = dOT u o' := by
  have hl : ((Formalism.MainNotions.PrimeDegreeVariant.lastGL ℂ (D.R.N D.R.m) (sqrtT D u) : GL _ ℂ) : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) ℂ)ᵀ =
      Matrix.reindex (eN D) (eN D) (Matrix.fromBlocks 1 0 0 (Matrix.of fun _ _ => ((sqrtT D u : ℂˣ) : ℂ))) := by
    rw [← lastGL_eq]
    show (Matrix.diagonal _)ᵀ = Matrix.diagonal _
    exact Matrix.diagonal_transpose _
  have he : ((Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ _ _ (Nm_succ D.R) g : GL (Fin (D.R.N D.R.m)) ℂ) : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) ℂ)ᵀ =
      Matrix.reindex (eN D) (eN D) (Matrix.fromBlocks o' 0 0 1) := by
    rw [embGL_val, Matrix.transpose_reindex, Matrix.fromBlocks_transpose, hg, Matrix.transpose_transpose,
      Matrix.transpose_zero, Matrix.transpose_zero, Matrix.transpose_one]
  unfold gFull dOT
  rw [Units.val_mul, Matrix.transpose_mul, hl, he, reindex_mulB, Matrix.fromBlocks_multiply]
  congr 1
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul]

theorem det_dOT (o' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ) :
    (dOT u o').det = o'.det * ((sqrtT D u : ℂˣ) : ℂ) := by
  unfold dOT
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
  congr 1
  rw [Matrix.det_unique]
  rfl

end Formalism.L2.GlobalTheoryTheory.Br
end
end

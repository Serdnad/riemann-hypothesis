module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle203
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1347
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle204
public import GroundTheory.GlobalFields.Adele.Bundle002
public import GroundTheory.GlobalFields.Adele.Bundle003
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.SplitDblPar

section Gen
variable {A : Type} [CommRing A] {ι : Type} [Fintype ι] [DecidableEq ι]

def shear (ι : Type) [DecidableEq ι] (s : A) : Matrix (ι ⊕ ι) (ι ⊕ ι) A :=
  Matrix.fromBlocks ((1 + s) • 1) ((-s) • 1) (s • 1) ((1 - s) • 1)

theorem shear_mul (s t : A) : shear ι s * shear ι t = shear ι (s + t) := by
  simp only [shear, Matrix.fromBlocks_multiply, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, ← add_smul]
  congr 2 <;> ring

omit [Fintype ι] in
theorem shear_zero : shear ι (0 : A) = 1 := by
  simp [shear, Matrix.fromBlocks_one]

omit [Fintype ι] in
theorem shear_map (f : A →+* A) (s : A) : (shear ι s).map f = shear ι (f s) := by
  ext (i | i) (j | j) <;> by_cases h : i = j <;> simp [shear, Matrix.one_apply, h]

theorem shear_unitary (J : Matrix ι ι A) (s : A) : (shear ι s)ᵀ * dbl J * shear ι (-s) = dbl J := by
  simp only [shear, dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.transpose_smul,
    Matrix.transpose_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, add_zero,
    zero_add, smul_smul, smul_neg, Matrix.neg_mul, smul_zero]
  congr 1 <;> module

theorem shear_mulVec_inl (s : A) (z : ι ⊕ ι → A) :
    (fun i => (shear ι s *ᵥ z) (Sum.inl i)) =
      (fun i => z (Sum.inl i)) + s • (fun i => z (Sum.inl i)) - s • (fun i => z (Sum.inr i)) := by
  funext i
  simp [shear, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply]
  ring

theorem shear_mulVec_inr (s : A) (z : ι ⊕ ι → A) :
    (fun i => (shear ι s *ᵥ z) (Sum.inr i)) =
      (fun i => z (Sum.inr i)) + s • (fun i => z (Sum.inl i)) - s • (fun i => z (Sum.inr i)) := by
  funext i
  simp [shear, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply]
  ring

theorem shear_diagCols (s : A) : shear ι s * (diagCols ι : Matrix (ι ⊕ ι) ι A) = (diagCols ι : Matrix (ι ⊕ ι) ι A) * (1 : Matrix ι ι A) := by
  rw [Matrix.mul_one]
  ext (i | i) j <;> by_cases h : i = j <;>
    simp [shear, diagCols, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, h]

theorem shear_eq (s : A) : shear ι s = 1 + s • ((diagCols ι : Matrix (ι ⊕ ι) ι A) * (Matrix.fromRows (1 : Matrix ι ι A) (-1))ᵀ) := by
  ext (i | i) (j | j) <;> by_cases h : i = j <;>
    simp [shear, diagCols, Matrix.mul_apply, Matrix.one_apply, h, sub_eq_add_neg]
  all_goals (intro h'; exact absurd h'.symm h)

end Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem diagonalFixingDoublingMatrix_eq_shear (c : AE F E) (d : ℕ) : GlobalTheory.SplitDblGen.diagonalFixingDoublingMatrix c d = shear (Fin d) (GlobalTheory.SplitDblGen.half * c) :=
  (shear_eq _).symm

theorem shear_mem_latAtD {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) (s : AE F E)
    (hs : ∀ z ∈ GlobalTheory.InertSph.latAt W v, s • z ∈ GlobalTheory.InertSph.latAt W v) {z : Fin d ⊕ Fin d → AE F E}
    (hz : z ∈ GlobalTheory.InertDbl.latAtD W v) : shear (Fin d) s *ᵥ z ∈ GlobalTheory.InertDbl.latAtD W v := by
  refine ⟨?_, ?_⟩
  · rw [shear_mulVec_inl]; exact sub_mem (add_mem hz.1 (hs _ hz.1)) (hs _ hz.2)
  · rw [shear_mulVec_inr]; exact sub_mem (add_mem hz.2 (hs _ hz.1)) (hs _ hz.2)

theorem diagonalFixingDoublingMatrix_mem_integralSiegelParabolic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ) (W : Spc F E d) (v : Pl (F := F)), (2 : 𝓞 F) ∉ v.asIdeal →
    ∀ c : AE F E, cA σ c = -c → At (evFin F v) c → (∀ z ∈ GlobalTheory.InertSph.latAt W v, c • z ∈ GlobalTheory.InertSph.latAt W v) →
    ∃ p ∈ GlobalTheory.InertDbl.ParD σ W v, GlobalTheory.InertDbl.matD p = GlobalTheory.SplitDblGen.diagonalFixingDoublingMatrix c d := by
  intro F E _ _ _ _ _ σ d W v h2 c hc hat hlat
  set s : AE F E := GlobalTheory.SplitDblGen.half * c with hsdef
  have hσ : cA σ s = -s := by
    rw [hsdef, map_mul, hc, GlobalTheory.SplitDblGen.half, AlgHom.commutes, mul_neg]
  have hs : ∀ z ∈ GlobalTheory.InertSph.latAt W v, s • z ∈ GlobalTheory.InertSph.latAt W v := by
    intro z hz
    rw [hsdef, mul_smul, GlobalTheory.SplitDblGen.half, algebraMap_smul]
    exact GlobalTheory.InertSph.invTwo_smul_mem_latAt F E d W v h2 _ (hlat z hz)
  have hs' : ∀ z ∈ GlobalTheory.InertSph.latAt W v, (-s) • z ∈ GlobalTheory.InertSph.latAt W v := by
    intro z hz
    rw [neg_smul]; exact neg_mem (hs z hz)
  have hu : (shear (Fin d) s)ᵀ * dbl (incM F W.J) * (shear (Fin d) s).map (cA σ) = dbl (incM F W.J) := by
    have h := shear_map (ι := Fin d) (cA σ : AE F E →+* AE F E) s
    have h' : (shear (Fin d) s).map (cA σ) = shear (Fin d) (-s) := by rw [← hσ]; exact h
    rw [h', shear_unitary]
  let p : GlobalTheory.InertDbl.UD σ W :=
    ⟨⟨shear (Fin d) s, shear (Fin d) (-s), by rw [shear_mul, add_neg_cancel, shear_zero],
      by rw [shear_mul, neg_add_cancel, shear_zero]⟩, hu⟩
  have hp : GlobalTheory.InertDbl.matD p = shear (Fin d) s := rfl
  have hpi : GlobalTheory.InertDbl.matD p⁻¹ = shear (Fin d) (-s) := rfl
  refine ⟨p, ⟨⟨fun u hu => ?_, fun z hz => ?_⟩, 1, ?_⟩, (diagonalFixingDoublingMatrix_eq_shear c d).symm⟩
  · have h0 : u • s = 0 := by rw [hsdef, ← mul_smul_comm, hat u hu, mul_zero]
    rw [hp, shear_eq, add_sub_cancel_left, ← smul_assoc, h0, zero_smul]
  · rw [hp, hpi]
    exact ⟨shear_mem_latAtD W v s hs hz, shear_mem_latAtD W v (-s) hs' hz⟩
  · exact shear_diagCols s

end GlobalTheory.SplitDblPar
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord GlobalTheory.ArchLine
open scoped Matrix Classical SchwartzMap

noncomputable section

namespace GlobalTheory.ArchLine

theorem archAct_linear_mul : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W),
    (∀ (h : UA σ W.J) (v v' : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)),
      archAct M h (v + v') = archAct M h v + archAct M h v') ∧
    (∀ (h : UA σ W.J) (c : ℝ) (v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)),
      archAct M h (c • v) = c • archAct M h v) ∧
    (∀ (h h' : UA σ W.J) (v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)),
      archAct M (h * h') v = archAct M h (archAct M h' v)) := by
  intro F E _ _ _ _ _ σ n d X W M
  refine ⟨fun h v v' => ?_, fun h c v => ?_, fun h h' v => ?_⟩
  · unfold archAct
    rw [Prod.fst_add, Prod.snd_add, lift_add, lift_add, ← Prod.mk_add_mk, map_add (f := _)]
    simp only [actAB, Matrix.mul_add, Matrix.add_mul]
    rw [coordI_add]
  · unfold archAct
    rw [Prod.smul_fst, Prod.smul_snd, lift_smul, lift_smul, ← Prod.smul_mk, map_smul]
    simp only [actAB, Matrix.mul_smul, Matrix.smul_mul]
    rw [coordI_smul]
  · unfold archAct
    rw [lift_coordI]
    simp only [actAB, Matrix.mul_smul, Matrix.smul_mul, coordI_one]
    congr 1
    simp only [one_mul, Units.val_one, Subgroup.coe_one, Subgroup.coe_mul, Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]
    simp only [Matrix.one_mul]

end GlobalTheory.ArchLine
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord GlobalTheory.ArchLine
open scoped Matrix Classical SchwartzMap

namespace GlobalTheory.ArchLine

theorem hTens_actAB_unitary {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {JA : Matrix α α E} {JB : Matrix β β E}
    (p : UG c JA × UG c JB) (x y : Matrix α β E) :
    hTens c JA JB (actAB c p x) (actAB c p y) = hTens c JA JB x y := by
  have tr : ∀ N : Matrix α α E, ∑ i, ∑ k, JA i k * N i k = (JAᵀ * N).trace := fun N => by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_comm
  have h1 : ((p.1 : GL α E) : Matrix α α E)ᵀ * JA * ((p.1 : GL α E) : Matrix α α E).map c = JA := p.1.2
  have h2 : ((p.2 : GL β E) : Matrix β β E)ᵀ * JB * ((p.2 : GL β E) : Matrix β β E).map c = JB := p.2.2
  rw [Coord.hTens_eq, Coord.hTens_eq, tr, tr, actAB, actAB]
  generalize ((p.1 : GL α E) : Matrix α α E) = g at h1 ⊢
  generalize ((p.2 : GL β E) : Matrix β β E) = h at h2 ⊢
  have e1 : ((g * y * hᵀ).map c)ᵀ = h.map c * (y.map c)ᵀ * (g.map c)ᵀ := by
    rw [Matrix.map_mul (f := c), Matrix.map_mul (f := c), Matrix.transpose_mul, Matrix.transpose_mul, Matrix.mul_assoc]
    rfl
  have e2 : JAᵀ * (g * x * hᵀ * JB * (h.map c * (y.map c)ᵀ * (g.map c)ᵀ)) =
      JAᵀ * g * (x * (hᵀ * JB * h.map c) * (y.map c)ᵀ) * (g.map c)ᵀ := by simp only [Matrix.mul_assoc]
  have e3 : (g.map c)ᵀ * (JAᵀ * g) = JAᵀ := by
    conv_rhs => rw [← h1]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [e1, e2, h2, Matrix.trace_mul_comm, ← Matrix.mul_assoc, e3]

theorem omega_archAct {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (h : UA σ W.J)
    (v v' : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :
    omega (trP F (Fin n × Fin d)) (archAct M h v) (archAct M h v') = omega (trP F (Fin n × Fin d)) v v' := by
  have hv := coordI_lift M v
  have hv' := coordI_lift M v'
  conv_rhs => rw [← hv, ← hv']
  rw [archAct, archAct, omega_coordI, omega_coordI]
  simp only [sympM, symp, hTens_actAB_unitary]

end GlobalTheory.ArchLine
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord GlobalTheory.ArchLine
open scoped Matrix Classical SchwartzMap

noncomputable section

namespace GlobalTheory.ArchLine.Laws

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

def intInd (κ : Type) : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
  (Set.pi Set.univ fun _ : κ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F))).indicator 1

theorem intInd_mem (κ : Type) [Fintype κ] :
    intInd (F := F) κ ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  have hOo : IsOpen (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) := by
    unfold GroundTheory.Global.integralFiniteAdeles
    exact RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      (fun v => Valued.isOpen_valuationSubring (v.adicCompletion F))
  have hOc : IsCompact (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) :=
    GroundTheory.Global.isCompact_integralFiniteAdeles F
  have hOcl : IsClosed (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) :=
    hOc.isClosed
  have hU : IsClopen (Set.pi Set.univ fun _ : κ =>
      (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F))) :=
    ⟨isClosed_set_pi fun _ _ => hOcl, isOpen_set_pi Set.finite_univ fun _ _ => hOo⟩
  show IsLocallyConstant (intInd (F := F) κ) ∧ HasCompactSupport (intInd (F := F) κ)
  refine ⟨(LocallyConstant.indicator (1 : LocallyConstant (κ → FiniteAdeleRing (𝓞 F) F) ℂ) hU).isLocallyConstant, ?_⟩
  exact HasCompactSupport.intro' (isCompact_univ_pi fun _ => hOc) hU.isClosed
    fun x hx => Set.indicator_of_notMem hx _

theorem snd_eq_zero_of_at {κ : Type} {z : κ → AF F} (hz : At (evI F) z) (i : κ) : (z i).2 = 0 := by
  let u : AF F := ((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F))
  have hu : evI F u = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  have h0 : u * z i = 0 := congrFun (hz u hu) i
  have h1 : (u * z i).2 = (1 : FiniteAdeleRing (𝓞 F) F) * (z i).2 := rfl
  rw [h0, one_mul] at h1
  exact h1.symm

def refFun (κ : Type) : (κ → AF F) → ℂ := fun x => intInd κ (fun i => (x i).2)

theorem refFun_rest {κ : Type} [Fintype κ] (f : SInf F κ) :
    Rest (evI F) (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (refFun κ) := by
  refine ⟨fun x z hz => ?_, Submodule.subset_span ⟨f, intInd κ, intInd_mem κ, rfl⟩⟩
  show intInd κ (fun i => (x i + z i).2) = intInd κ (fun i => (x i).2)
  congr 1
  funext i
  change (x i).2 + (z i).2 = (x i).2
  rw [snd_eq_zero_of_at hz i, add_zero]

theorem refFun_lift {κ : Type} (t : κ → mixedEmbedding.mixedSpace F) : refFun κ (liftV t) = 1 := by
  show intInd κ (fun i => (liftV t i).2) = 1
  unfold intInd
  rw [Set.indicator_of_mem]
  · rfl
  · intro i _
    change (0 : FiniteAdeleRing (𝓞 F) F) ∈ (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F))
    exact zero_mem _

theorem tens_lift {κ : Type} (φ : (κ → mixedEmbedding.mixedSpace F) → ℂ) (t : κ → mixedEmbedding.mixedSpace F) :
    tens (evI F) φ (refFun κ) (liftV t) = φ t := by
  show φ (fun i => evI F (liftV t i)) * refFun κ (liftV t) = φ t
  rw [refFun_lift, mul_one]
  congr 1
  funext i
  exact RingEquiv.apply_symm_apply _ _

theorem eq_of_tens {κ : Type} [Fintype κ] {f₁ f₂ : SInf F κ}
    (h : tens (evI F) (f₁ : (κ → mixedEmbedding.mixedSpace F) → ℂ) (refFun κ) = tens (evI F) (f₂ : _ → ℂ) (refFun κ)) :
    f₁ = f₂ := by
  ext t
  have key := congrFun h (liftV t)
  rwa [tens_lift, tens_lift] at key

theorem tens_add {κ : Type} [Fintype κ] (f f' : SInf F κ) (r : (κ → AF F) → ℂ) :
    tens (evI F) (⇑(f + f') : (κ → mixedEmbedding.mixedSpace F) → ℂ) r = tens (evI F) ⇑f r + tens (evI F) ⇑f' r := by
  funext x
  change (f + f') (fun i => evI F (x i)) * r x = f (fun i => evI F (x i)) * r x + f' (fun i => evI F (x i)) * r x
  rw [SchwartzMap.add_apply, add_mul]

theorem tens_smul {κ : Type} [Fintype κ] (c : ℂ) (f : SInf F κ) (r : (κ → AF F) → ℂ) :
    tens (evI F) (⇑(c • f) : (κ → mixedEmbedding.mixedSpace F) → ℂ) r = c • tens (evI F) ⇑f r := by
  funext x
  change (c • f) (fun i => evI F (x i)) * r x = c • (f (fun i => evI F (x i)) * r x)
  rw [SchwartzMap.smul_apply, smul_mul_assoc]

theorem img (om : Rep σ X W) (h : UA σ W.J) (f : SInf F (Fin n × Fin d))
    (hx : ∃ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, h)) ⇑f ⇑f₁) :
    om (1, h) (tens (evI F) ⇑f (refFun _)) = tens (evI F) ⇑(archOp om h f) (refFun _) := acts_archOp om h f hx _ (refFun_rest f)

theorem archOp_eq_of_acts (om : Rep σ X W) (h : UA σ W.J) (f f₁ : SInf F (Fin n × Fin d))
    (hA : Acts (evI F) (om (1, h)) ⇑f ⇑f₁) : archOp om h f = f₁ := by
  apply eq_of_tens
  rw [← img om h f ⟨f₁, hA⟩]
  exact hA _ (refFun_rest f)

end GlobalTheory.ArchLine.Laws

namespace GlobalTheory.ArchLine


open GlobalTheory.ArchLine.Laws in
theorem archOp_laws : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    M.IsWeil ψ χX χW om → (∀ h ∈ UAt σ W (evI F), ∀ f : SInf F (Fin n × Fin d), ∃ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (1, h)) ⇑f ⇑f₁) →
    (∀ h ∈ UAt σ W (evI F), ∀ f f' : SInf F (Fin n × Fin d), archOp om h (f + f') = archOp om h f + archOp om h f') ∧
    (∀ h ∈ UAt σ W (evI F), ∀ (c : ℂ) (f : SInf F (Fin n × Fin d)), archOp om h (c • f) = c • archOp om h f) ∧
    (∀ f : SInf F (Fin n × Fin d), archOp om 1 f = f) ∧
    (∀ h ∈ UAt σ W (evI F), ∀ h' ∈ UAt σ W (evI F), ∀ f : SInf F (Fin n × Fin d),
      archOp om (h * h') f = archOp om h (archOp om h' f)) := by
  intro F E _ _ _ _ _ σ n d X W M ψ χX χW om _ hex
  refine ⟨fun h hh f f' => ?_, fun h hh c f => ?_, fun f => ?_, fun h hh h' hh' f => ?_⟩
  · apply eq_of_tens
    rw [tens_add, ← img om h (f + f') (hex h hh _), ← img om h f (hex h hh f), ← img om h f' (hex h hh f'),
      tens_add, map_add]
  · apply eq_of_tens
    rw [tens_smul, ← img om h (c • f) (hex h hh _), ← img om h f (hex h hh f), tens_smul, map_smul]
  · apply archOp_eq_of_acts
    intro r _
    have e1 : om (1, 1) = 1 := map_one om
    rw [e1]
    rfl
  · have hmul : h * h' ∈ UAt σ W (evI F) := by
      intro u hu
      have e : mat (h * h') - 1 = (mat h - 1) * mat h' + (mat h' - 1) := by
        change mat h * mat h' - 1 = _
        noncomm_ring
      have a1 : u • (mat h - 1) = 0 := (show ∀ u, evI F u = 0 → u • (mat h - 1) = 0 from hh) u hu
      have a2 : u • (mat h' - 1) = 0 := (show ∀ u, evI F u = 0 → u • (mat h' - 1) = 0 from hh') u hu
      rw [e, smul_add, ← Matrix.smul_mul, a1, a2, zero_mul, add_zero]
    apply eq_of_tens
    rw [← img om (h * h') f (hex _ hmul f), ← img om h (archOp om h' f) (hex h hh _),
      ← img om h' f (hex h' hh' f)]
    have e2 : ((1 : UA σ X.J), h * h') = (1, h) * (1, h') := by rw [Prod.mk_mul_mk, one_mul]
    rw [e2, map_mul]
    rfl

end GlobalTheory.ArchLine
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord GlobalTheory.ArchLine
open scoped Matrix Classical SchwartzMap

noncomputable section

namespace GlobalTheory.ArchLine.OpCont

theorem evI_fin {F : Type} [Field F] [NumberField F] : evI F ((0, 1) : AF F) = 0 :=
  map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)

theorem snd_eq_zero_of_at {F : Type} [Field F] [NumberField F] {κ : Type} {z : κ → AF F} (hz : At (evI F) z) (i : κ) :
    (z i).2 = 0 := by
  have := congrArg Prod.snd (congrFun (hz (0, 1) evI_fin) i)
  change (((0, 1) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F).2 * (z i).2) = (0 : AF F).2 at this
  rw [one_mul] at this
  exact this

def intInd {F : Type} [Field F] [NumberField F] (κ : Type) : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
  (Set.pi Set.univ fun _ : κ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F))).indicator 1

theorem intInd_mem {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    intInd (F := F) κ ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  set B := Set.pi Set.univ fun _ : κ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) with hB
  have hO : IsOpen B := isOpen_set_pi Set.finite_univ fun _ _ => GroundTheory.Global.isOpen_integralFiniteAdeles
  have hK : IsCompact B := isCompact_univ_pi fun _ => GroundTheory.Global.isCompact_integralFiniteAdeles F
  have hC : IsClosed B := hK.isClosed
  refine ⟨?_, HasCompactSupport.intro hK fun x hx => Set.indicator_of_notMem hx _⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  by_cases hx : x ∈ B
  · refine ⟨_, hO, hx, fun y hy => ?_⟩
    simp only [intInd, ← hB, Set.indicator_of_mem hy, Set.indicator_of_mem hx, Pi.one_apply]
  · refine ⟨_, hC.isOpen_compl, hx, fun y hy => ?_⟩
    simp only [intInd, ← hB, Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

end GlobalTheory.ArchLine.OpCont

namespace GlobalTheory.ArchLine

theorem archOp_apply_continuous : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    M.IsWeil ψ χX χW om → (∀ h ∈ UAt σ W (evI F), ∀ f : SInf F (Fin n × Fin d), ∃ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (1, h)) ⇑f ⇑f₁) → ∀ γ ∈ Lines σ W,
    ∀ (f : SInf F (Fin n × Fin d)) (x : Fin n × Fin d → mixedEmbedding.mixedSpace F),
      Continuous fun t : ℝ => archOp om (γ (Multiplicative.ofAdd t)) f x := by
  intro F E _ _ _ _ _ σ n d X W M ψ χX χW om hW hex γ hγ f x
  have hC := hW.2.2

  set r₀ : (Fin n × Fin d → AF F) → ℂ := fun y => GlobalTheory.ArchLine.OpCont.intInd (F := F) (Fin n × Fin d) (fun i => (y i).2)
    with hr₀
  have hr₀1 : ∀ y : Fin n × Fin d → AF F, (∀ i, (y i).2 = 0) → r₀ y = 1 := by
    intro y hy
    have : (fun i => (y i).2) = 0 := funext hy
    simp only [hr₀, this, GlobalTheory.ArchLine.OpCont.intInd]
    rw [Set.indicator_of_mem (show (0 : Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) ∈ Set.pi Set.univ
      fun _ : Fin n × Fin d => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) from
        fun i _ => zero_mem (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F))]
    rfl
  have hrest : ∀ g : SInf F (Fin n × Fin d), Rest (evI F) (g : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) r₀ := by
    intro g
    refine ⟨fun y z hz => ?_, ?_⟩
    · have : (fun i => ((y + z) i).2) = fun i => (y i).2 := by
        funext i
        change (y i).2 + (z i).2 = (y i).2
        rw [GlobalTheory.ArchLine.OpCont.snd_eq_zero_of_at hz i, add_zero]
      simp only [hr₀, this]
    · exact Submodule.subset_span ⟨g, GlobalTheory.ArchLine.OpCont.intInd _, GlobalTheory.ArchLine.OpCont.intInd_mem _, rfl⟩

  let l : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun Φ => Φ (liftV x), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hl : l ∈ (adeleClass F).adm (Fin n × Fin d) := by
    intro g _
    refine ⟨g 0 • ((BoundedContinuousFunction.evalCLM ℂ x).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ)), fun f' => ?_⟩
    rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
    show pureA F f' g (liftV x) = _
    simp only [pureA, liftV, RingEquiv.apply_symm_apply]
    change f' x * g 0 = g 0 * f' x
    ring
  have hφ : tens (evI F) (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) r₀ ∈ (adeleClass F).sp (Fin n × Fin d) :=
    (hrest f).2
  have hcont := hC l hl _ hφ
  have hpath : Continuous fun t : ℝ => (((1 : UA σ X.J), γ (Multiplicative.ofAdd t)) : UA σ X.J × UA σ W.J) :=
    continuous_const.prodMk (hγ.1.comp continuous_ofAdd)
  have key := hcont.comp hpath
  convert key using 1
  funext t
  have hh : γ (Multiplicative.ofAdd t) ∈ UAt σ W (evI F) := hγ.2 _
  have ha := acts_archOp om (γ (Multiplicative.ofAdd t)) f (hex _ hh f) r₀ (hrest f)
  simp only [Function.comp_apply]
  show _ = om _ _ (liftV x)
  change _ = om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) (⇑f) r₀) (liftV x)
  rw [ha]
  have h1 : r₀ (liftV x) = 1 := hr₀1 _ fun i => rfl
  have h2 : (fun i => evI F (liftV x i)) = x := by
    funext i
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _
  simp only [tens, h1, h2, mul_one]

end GlobalTheory.ArchLine
end
end

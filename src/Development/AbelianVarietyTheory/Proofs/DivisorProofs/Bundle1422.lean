module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle043
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1321
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1319
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1320

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ResW

theorem dchi_absC_one_finrank (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (s : ℂ) :
    dchi (GlobalTheory.CuspRep.Model.absC E s) 1 = s * (Module.finrank ℚ E : ℂ) := by
  let A : Cinf E →L[ℝ] ℂ :=
    s • ∑ w, (2 : ℝ) • (Complex.ofRealCLM.comp (Complex.reCLM.comp (ContinuousLinearMap.proj w)))
  have h : dchi (GlobalTheory.CuspRep.Model.absC E s) = A := fderiv_extZero (continuous_chiInf _) fun z => by
    change Complex.exp (s * GlobalTheory.Mem.Chr.CharModel.logNorm E (infId E (expU z))) = _
    rw [GlobalTheory.CuspRep.Model.logNorm_infId]
    congr 1
    simp [A, expU, Complex.norm_exp]
  have h2 : Module.finrank ℚ E = 2 * Fintype.card (InfinitePlace E) := by
    rw [IsTotallyComplex.finrank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
  rw [h, h2]
  simp [A, mul_comm]

theorem exists_abs_cpow : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (z : ℂ), ∃ χ : HChar E, (∀ (a : ℕ) (φ : Sm E a), zc E a (mulChi a χ φ) = mulChi a χ (zc E a φ + (a * (Module.finrank ℚ E : ℂ) * z) • φ)) ∧ (∀ v, χ.UnrAt v ∧ ((χ.val v : ℂˣ) : ℂ) = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-z)) ∧ (∀ x, ‖((χ.1 x : ℂˣ) : ℂ)‖ = ‖(((nu E z.re).1 x : ℂˣ) : ℂ)‖) ∧ (z.im = 0 → χ = nu E z.re) := by
  intro E _ _ _ z
  refine ⟨GlobalTheory.CuspRep.Model.absC E z, fun a φ => ?_, fun v => ⟨fun x hx => Units.ext ?_, ?_⟩, fun x => ?_, fun hz => ?_⟩
  · unfold zc
    rw [lie_mulChi]
    have e : (Matrix.of (fun i j : Fin a => if i = j then (1 : Cinf E) else 0)).trace = (a : ℝ) • (1 : Cinf E) := by
      simp [Matrix.trace, Nat.cast_smul_eq_nsmul]
    rw [e, map_smul, dchi_absC_one_finrank]
    congr 3
    simp only [Complex.real_smul, Complex.ofReal_natCast]; ring
  · change Complex.exp (z * GlobalTheory.Mem.Chr.CharModel.logNorm E (GlobalTheory.Mem.Chr.localIdele E v x)) = 1
    rw [GlobalTheory.Mem.Chr.CharModel.logNorm_local v x 0 (by simpa [IsUnitAt] using hx)]; simp
  · change Complex.exp (z * GlobalTheory.Mem.Chr.CharModel.logNorm E (GlobalTheory.Mem.Chr.localIdele E v (atFin v (unif v)))) = _
    have h0 : (Ideal.absNorm v.asIdeal : ℕ) ≠ 0 := by simpa [Ideal.absNorm_eq_zero_iff] using v.ne_bot
    rw [GlobalTheory.Mem.Chr.CharModel.logNorm_local v _ 1 (unif_spec v), Complex.cpow_def_of_ne_zero (by exact_mod_cast h0),
      ← Complex.natCast_log]
    congr 1; push_cast; ring
  · change ‖Complex.exp (z * GlobalTheory.Mem.Chr.CharModel.logNorm E x)‖ =
      ‖Complex.exp ((z.re : ℂ) * GlobalTheory.Mem.Chr.CharModel.logNorm E x)‖
    rw [Complex.norm_exp, Complex.norm_exp]; simp
  · have e : z = (z.re : ℂ) := Complex.ext rfl (by simpa using hz)
    conv_lhs => rw [e]
    rfl

end GlobalTheory.ResW

end
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.UnipDom

noncomputable section

namespace GlobalTheory.ThK.UnipClosed

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def carrierSet (σ : E →ₐ[F] E) {d d₁ : ℕ} (W : Spc F E d) (H' : Plane E d d₁) : Set (UA σ W.J) :=
  {u | mat u *ᵥ incV F H'.x = incV F H'.x ∧
    ∀ z, ∃ a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), mat u *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x}

theorem mat_mul {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g h : UA σ J) :
    mat (g * h) = mat g * mat h := rfl

theorem mat_inv_mul {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) :
    mat g⁻¹ * mat g = 1 := by
  show ((g⁻¹ : UA σ J).1.1) * g.1.1 = 1
  rw [← Units.val_mul]
  show (((g⁻¹ * g : UA σ J) : GL (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = 1
  simp

theorem mat_one {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} :
    mat (1 : UA σ J) = 1 := rfl

def carrierSub (σ : E →ₐ[F] E) {d d₁ : ℕ} (W : Spc F E d) (H' : Plane E d d₁) : Subgroup (UA σ W.J) where
  carrier := carrierSet σ W H'
  one_mem' := ⟨by rw [mat_one, Matrix.one_mulVec], fun z => ⟨0, by rw [mat_one, Matrix.one_mulVec, zero_smul, add_zero]⟩⟩
  mul_mem' := by
    rintro u v ⟨hu1, hu2⟩ ⟨hv1, hv2⟩
    refine ⟨by rw [mat_mul, ← Matrix.mulVec_mulVec, hv1, hu1], fun z => ?_⟩
    obtain ⟨a, ha⟩ := hu2 z
    obtain ⟨b, hb⟩ := hv2 z
    refine ⟨a + b, ?_⟩
    rw [mat_mul, ← Matrix.mulVec_mulVec, hb, Matrix.mulVec_add, ha, Matrix.mulVec_smul, hu1, add_smul, add_assoc]
  inv_mem' := by
    rintro u ⟨hu1, hu2⟩
    have hx : mat u⁻¹ *ᵥ incV F H'.x = incV F H'.x := by
      conv_lhs => rw [← hu1]
      rw [Matrix.mulVec_mulVec, mat_inv_mul, Matrix.one_mulVec]
    refine ⟨hx, fun z => ?_⟩
    obtain ⟨a, ha⟩ := hu2 z
    refine ⟨-a, ?_⟩
    have h1 : mat u⁻¹ *ᵥ (mat u *ᵥ (incM F H'.ι *ᵥ z)) = incM F H'.ι *ᵥ z := by
      rw [Matrix.mulVec_mulVec, mat_inv_mul, Matrix.one_mulVec]
    rw [ha, Matrix.mulVec_add, Matrix.mulVec_smul, hx] at h1
    rw [neg_smul, ← sub_eq_add_neg, eq_sub_iff_add_eq]
    exact h1

theorem unip_eq (σ : E →ₐ[F] E) {d d₁ : ℕ} (W : Spc F E d) (H' : Plane E d d₁) :
    unip σ W H' = carrierSub σ W H' := by
  apply le_antisymm
  · exact (Subgroup.closure_le _).2 fun u hu => hu
  · intro u hu
    exact Subgroup.subset_closure hu

section Top

variable [T2Space (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))] [IsTopologicalRing (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))]

theorem isClosed_line {d : ℕ} (x : Fin d → E) : IsClosed {w : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) | ∃ a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), w = a • incV F x} := by
  by_cases hx : x = 0
  · have : {w : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) | ∃ a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), w = a • incV F x} = {0} := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      have h0 : incV F x = 0 := by
        funext i
        simp [incV, hx]
      simp [h0]
    rw [this]
    exact isClosed_singleton
  · obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx (funext h)
    have hinv : incV F x i * inclR (F := F) (AF F) (x i)⁻¹ = 1 := by
      simp only [incV, ← map_mul, mul_inv_cancel₀ hi, map_one]
    have : {w : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) | ∃ a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), w = a • incV F x} =
        {w | w = (w i * inclR (F := F) (AF F) (x i)⁻¹) • incV F x} := by
      ext w
      simp only [Set.mem_setOf_eq]
      constructor
      · rintro ⟨a, rfl⟩
        congr 1
        simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, hinv, mul_one]
      · intro h
        exact ⟨_, h⟩
    rw [this]
    exact isClosed_eq continuous_id
      (((continuous_apply i).mul continuous_const).smul continuous_const)

end Top

variable [T2Space (AE F E)] [IsTopologicalRing (AE F E)] in
theorem isClosed_carrierSet (σ : E →ₐ[F] E) {d d₁ : ℕ} (W : Spc F E d) (H' : Plane E d d₁) :
    IsClosed (carrierSet σ W H') := by
  have hm : Continuous fun u : UA σ W.J => mat u := Units.continuous_val.comp continuous_subtype_val
  have h1 : IsClosed {u : UA σ W.J | mat u *ᵥ incV F H'.x = incV F H'.x} :=
    isClosed_eq (hm.matrix_mulVec continuous_const) continuous_const
  have h2 : ∀ z : Fin d₁ → AE F E, IsClosed {u : UA σ W.J | ∃ a : AE F E,
      mat u *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x} := by
    intro z
    have : {u : UA σ W.J | ∃ a : AE F E, mat u *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x} =
        (fun u : UA σ W.J => mat u *ᵥ (incM F H'.ι *ᵥ z) - incM F H'.ι *ᵥ z) ⁻¹'
          {w | ∃ a : AE F E, w = a • incV F H'.x} := by
      ext u
      simp only [Set.mem_setOf_eq, Set.mem_preimage, sub_eq_iff_eq_add']
    rw [this]
    exact (isClosed_line H'.x).preimage ((hm.matrix_mulVec continuous_const).sub continuous_const)
  have : carrierSet σ W H' = {u : UA σ W.J | mat u *ᵥ incV F H'.x = incV F H'.x} ∩
      ⋂ z : Fin d₁ → AE F E, {u : UA σ W.J | ∃ a : AE F E,
        mat u *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x} := by
    ext u
    simp [carrierSet]
  rw [this]
  exact h1.inter (isClosed_iInter h2)

theorem isClosed_unip : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (d d₁ : ℕ) (W : Spc F E d) (H' : Plane E d d₁), IsClosed ((unip σ W H' : Subgroup (UA σ W.J)) : Set (UA σ W.J)) := by
  intro F E _ _ _ _ _ σ d d₁ W H'
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  rw [unip_eq]
  exact isClosed_carrierSet σ W H'

end GlobalTheory.ThK.UnipClosed
end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixedLagr
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixedLagr

theorem symplectic_isotropic_embedded_vanishes : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n d d₁ : ℕ) (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E) (H' : Plane E d d₁),
    (∀ u, form σ JW (H'.ι *ᵥ u) H'.x = 0) → ∀ u ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))),
      ∀ z : Matrix (Fin n) (Fin d₁) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
        symp (cA σ) (-1) (incM F JX) (incM F JW) (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) u = 0 := by
  intro F E _ _ _ _ _ σ n d d₁ JX JW H' hH u hu z
  obtain ⟨y, rfl⟩ := hu
  have hm : ∀ m, ∑ j, ∑ l, H'.ι j m * JW j l * σ (H'.x l) = 0 := by
    intro m
    have := hH (Pi.single m 1)
    simp only [form, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
  have hm' : ∀ m, ∑ j, ∑ l, inclR (F := F) (AF F) (H'.ι j m) * inclR (F := F) (AF F) (JW j l) * inclR (F := F) (AF F) (σ (H'.x l)) = 0 := fun m => by
    have := congrArg (inclR (F := F) (AF F)) (hm m)

    simpa only [map_sum, map_mul, map_zero] using this
  have hc : ∀ e : E, cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun e => by simp [cA, inclR]
  have h1 : (incM F (1 : Matrix (Fin n) (Fin n) E)) = 1 := by simp [incM]
  unfold symp
  suffices h : hTens (cA σ) (incM F JX) (incM F JW) (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) (Matrix.vecMulVec y (incV F H'.x)) = 0 by
    rw [h, mul_zero, map_zero]
  rw [h1, Matrix.one_mul]
  simp only [hTens, Matrix.mul_apply, Matrix.transpose_apply, incM, Matrix.map_apply, Matrix.vecMulVec_apply, incV, map_mul, hc]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun k _ => ?_
  calc _ = ∑ m, (z i m * inclR (F := F) (AF F) (JX i k) * cA σ (y k)) *
        ∑ j, ∑ l, inclR (F := F) (AF F) (H'.ι j m) * inclR (F := F) (AF F) (JW j l) * inclR (F := F) (AF F) (σ (H'.x l)) := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
        conv_lhs => rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
        ring
    _ = 0 := Finset.sum_eq_zero fun m _ => by rw [hm' m, mul_zero]
end GlobalTheory.MixedLagr

end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixedLagr
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.MixedLagr

theorem hTens_vecMulVec {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A)
    {α β : Type} [Fintype α] [Fintype β] (JA : Matrix α α A) (JB : Matrix β β A) (a a' : α → A) (x x' : β → A) :
    hTens c JA JB (Matrix.vecMulVec a x) (Matrix.vecMulVec a' x') =
      (∑ i, ∑ k, a i * JA i k * c (a' k)) * ∑ j, ∑ l, x j * JB j l * c (x' l) := by
  simp only [hTens, Matrix.vecMulVec_apply, map_mul]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem symplectic_isotropic_plane_vanishes (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n d d₁ : ℕ) (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E) (H' : Plane E d d₁) :
    form σ JW H'.x H'.x = 0 → ∀ u ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))),
      ∀ u' ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))), symp (cA σ) (-1) (incM F JX) (incM F JW) u u' = 0 := by
  rintro h0 u ⟨a, rfl⟩ u' ⟨a', rfl⟩
  have hc : ∀ x : E, cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := fun x => rfl
  have h : ∑ j, ∑ l, incV F H'.x j * incM F JW j l * cA σ (incV F H'.x l) = 0 := by
    have h1 := congrArg (inclR (F := F) (AF F)) h0
    rw [map_zero] at h1
    rw [← h1]

    simp only [form, incV, incM, Matrix.map_apply, hc, dotProduct, Matrix.mulVec, Finset.mul_sum, map_sum, map_mul, mul_assoc]
  rw [symp, hTens_vecMulVec, h, mul_zero, mul_zero, map_zero]

end GlobalTheory.MixedLagr
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.IndLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d d₁ : ℕ} {Y : Spc F E n} {W : Spc F E d}

def PGen (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (V : Submodule ℂ P) : Prop :=
  ∀ N : Submodule ℂ P, V ≤ N →
    (∀ γ ∈ Lines σ W, (∀ s, γ s ∈ unip σ W H') → ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      ActsD (evI F) (fun s => om (1, γ (Multiplicative.ofAdd s))) f f₁ → p f ∈ N → p f₁ ∈ N) →
    (∀ γ ∈ Lines σ W, (∃ (t : Multiplicative ℝ →* (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ) (γ₁ : Multiplicative ℝ →* UA σ W₁.J), γ₁ ∈ Lines σ W₁ ∧
        ∀ s, IsLevi H' (t s) (γ₁ s) (γ s)) → ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      ActsD (evI F) (fun s => om (1, γ (Multiplicative.ofAdd s))) f f₁ → p f ∈ N → p f₁ ∈ N) →
    N = ⊤

def KStab (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (V : Submodule ℂ P) : Prop :=
  (∀ k ∈ KInf σ W B.emb, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (1, k)) f f₁ → p f ∈ V → p f₁ ∈ V) ∧
    ∀ γ ∈ Lines σ W, (∀ s, γ s ∈ KInf σ W B.emb) → ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      ActsD (evI F) (fun s => om (1, γ (Multiplicative.ofAdd s))) f f₁ → p f ∈ V → p f₁ ∈ V

end GlobalTheory.IndLine
end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThK.CycGen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem smul_pure {κ : Type} [Fintype κ] (c : ℂ) (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) :
    c • pure f φ = pure (c • f) φ := by
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

theorem exists_decOn_some {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W)
    (Φ : (Fin n × Fin d → AF F) → ℂ) (hΦ : Φ ∈ PolData B M) :
    ∃ (T₀ : Finset (Pl (F := F))) (m : ℕ) (f : Fin m → SInf F (Fin n × Fin d))
      (φ : Fin m → ∀ v : Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ), DecOn B M T₀ Φ m f φ := by
  classical
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, φ, hφ, hcof, rfl⟩ := hx
    have hfin : {v | ¬ φ v = M.vac v}.Finite := Filter.eventually_cofinite.1 hcof
    refine ⟨hfin.toFinset, 1, fun _ => f, fun _ => φ, fun _ => ⟨hf, hφ, fun v hv => ?_⟩, ?_⟩
    · by_contra h
      exact hv (hfin.mem_toFinset.2 h)
    · simp
  | zero =>
    exact ⟨∅, 0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨T, m, f, φ, h1, rfl⟩ := hx
    obtain ⟨T', m', f', φ', h1', rfl⟩ := hy
    refine ⟨T ∪ T', m + m', Fin.append f f', Fin.append φ φ', fun j => ?_, ?_⟩
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simp only [Fin.append_left]
        exact ⟨(h1 i).1, (h1 i).2.1, fun v hv => (h1 i).2.2 v fun h => hv (Finset.mem_union_left _ h)⟩
      · simp only [Fin.append_right]
        exact ⟨(h1' i).1, (h1' i).2.1, fun v hv => (h1' i).2.2 v fun h => hv (Finset.mem_union_right _ h)⟩
    · rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
  | smul c x _ hx =>
    obtain ⟨T, m, f, φ, h1, rfl⟩ := hx
    refine ⟨T, m, fun j => c • f j, φ, fun j => ⟨Submodule.smul_mem _ c (h1 j).1, (h1 j).2.1, (h1 j).2.2⟩, ?_⟩
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => smul_pure c (f j) (φ j)

end GlobalTheory.ThK.CycGen

end
end

section

noncomputable section

namespace GlobalTheory.IwLine

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cA_eq_sigR (σ : E →ₐ[F] E) (z : AE F E) : cA σ z = sigR (AF F) σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem UG_eq_HR (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    GlobalTheory.WeilM.UG (cA σ) (incM F J) = HR (AF F) σ Jᵀ := by
  have hc : ∀ M : Matrix (Fin n) (Fin n) (AE F E), M.map (cA σ) = M.map (sigR (AF F) σ) := fun M => by
    ext i j; exact cA_eq_sigR σ _
  have hJ : JR (AF F) Jᵀ = (incM F J)ᵀ := rfl
  ext g
  change (g.1)ᵀ * incM F J * (g.1).map (cA σ) = incM F J ↔ cT (sigR (AF F) σ) g.1 * JR (AF F) Jᵀ * g.1 = JR (AF F) Jᵀ
  rw [hc, hJ, cT]
  constructor
  · intro h
    have := congrArg Matrix.transpose h
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  · intro h
    have := congrArg Matrix.transpose h
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

def ofGAd : GAd σ Jᵀ ≃* UA σ J := MulEquiv.subgroupCongr (UG_eq_HR σ J).symm

theorem mat_ofGAd (g : GAd σ Jᵀ) : mat (ofGAd σ J g) = (matHom (AF F) σ Jᵀ g).1 := rfl

def lineStab (x : Fin n → E) : Subgroup (UA σ J) where
  carrier := {g | ∃ a : (AE F E)ˣ, mat g *ᵥ incV F x = (a : AE F E) • incV F x}
  one_mem' := ⟨1, by simp [mat, Matrix.one_mulVec]⟩
  mul_mem' := by
    rintro g h ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨b * a, ?_⟩
    show (mat g * mat h) *ᵥ incV F x = _
    rw [← Matrix.mulVec_mulVec, hb, Matrix.mulVec_smul, ha, smul_smul, Units.val_mul]
  inv_mem' := by
    rintro g ⟨a, ha⟩
    refine ⟨a⁻¹, ?_⟩
    have e : mat g⁻¹ *ᵥ (mat g *ᵥ incV F x) = incV F x := by
      rw [Matrix.mulVec_mulVec, GlobalTheory.StabHaar.mat_inv_mul, Matrix.one_mulVec]
    rw [ha, Matrix.mulVec_smul] at e
    calc mat g⁻¹ *ᵥ incV F x = ((a⁻¹ : (AE F E)ˣ) : AE F E) • ((a : AE F E) • mat g⁻¹ *ᵥ incV F x) := by
          rw [smul_smul, Units.inv_mul, one_smul]
      _ = _ := by rw [e]

theorem mem_lineStab {x : Fin n → E} {g : UA σ J} :
    g ∈ lineStab σ J x ↔ ∃ a : (AE F E)ˣ, mat g *ᵥ incV F x = (a : AE F E) • incV F x := Iff.rfl

end GlobalTheory.IwLine
end
end

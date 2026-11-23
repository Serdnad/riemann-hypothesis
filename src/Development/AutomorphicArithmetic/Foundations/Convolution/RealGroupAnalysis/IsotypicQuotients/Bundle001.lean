module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.IsotypQuot
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Pp

private theorem real_dec {ι : Type} (X : GL (Fin 2) (ι → ℝ)) :
    ∃ (s : (ι → ℝ)ˣ) (g : GL (Fin 2) (ι → ℝ)) (k : Matrix.unitaryGroup (Fin 2) (ι → ℝ)),
      Matrix.GeneralLinearGroup.det g = 1 ∧
        X = Matrix.GeneralLinearGroup.scalar (Fin 2) s * (g * Unitary.toUnits k) := by
  classical
  set D : (ι → ℝ)ˣ := Matrix.GeneralLinearGroup.det X with hD
  have hw : ∀ w, (D : ι → ℝ) w ≠ 0 := fun w => ((Pi.isUnit_iff.1 D.isUnit) w).ne_zero
  have hpos : ∀ w, 0 < Real.sqrt |(D : ι → ℝ) w| := fun w => Real.sqrt_pos.2 (abs_pos.2 (hw w))
  let s : (ι → ℝ)ˣ :=
    ⟨fun w => Real.sqrt |(D : ι → ℝ) w|, fun w => (Real.sqrt |(D : ι → ℝ) w|)⁻¹,
      funext fun w => mul_inv_cancel₀ (hpos w).ne', funext fun w => inv_mul_cancel₀ (hpos w).ne'⟩
  let e : ι → ℝ := fun w => if 0 < (D : ι → ℝ) w then 1 else -1
  have hee : e * e = 1 := by
    funext w
    by_cases h : 0 < (D : ι → ℝ) w <;> simp [e, h]
  have hse : (s : ι → ℝ) * s * e = D := by
    funext w
    have h2 : Real.sqrt |(D : ι → ℝ) w| * Real.sqrt |(D : ι → ℝ) w| = |(D : ι → ℝ) w| :=
      Real.mul_self_sqrt (abs_nonneg _)
    change Real.sqrt |(D : ι → ℝ) w| * Real.sqrt |(D : ι → ℝ) w| * e w = _
    rw [h2]
    by_cases h : 0 < (D : ι → ℝ) w
    · simp [e, h, abs_of_pos h]
    · have h' : (D : ι → ℝ) w < 0 := lt_of_le_of_ne (not_lt.1 h) (hw w)
      simp [e, h, abs_of_neg h']
  have hstar : star e = e := by
    funext w
    simp
  let K : Matrix (Fin 2) (Fin 2) (ι → ℝ) := !![1, 0; 0, e]
  have hKK : K * K = 1 := by
    ext i j : 1
    fin_cases i <;> fin_cases j <;> simp [K, Matrix.mul_apply, Fin.sum_univ_two, hee]
  have hKs : star K = K := by
    ext i j : 1
    fin_cases i <;> fin_cases j <;> simp [K, Matrix.star_eq_conjTranspose, hstar]
  have hKmem : K ∈ Matrix.unitaryGroup (Fin 2) (ι → ℝ) := by
    rw [Matrix.mem_unitaryGroup_iff, hKs]
    exact hKK
  let k : Matrix.unitaryGroup (Fin 2) (ι → ℝ) := ⟨K, hKmem⟩
  have hk : (Unitary.toUnits k) * (Unitary.toUnits k) = 1 := Units.ext hKK
  have hdetk : (Matrix.GeneralLinearGroup.det (Unitary.toUnits k) : ι → ℝ) = e := by
    change K.det = e
    simp [K, Matrix.det_fin_two]
  have hdets : ∀ t : (ι → ℝ)ˣ,
      (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) t) : ι → ℝ) = t * t := by
    intro t
    change (Matrix.GeneralLinearGroup.scalar (Fin 2) t).val.det = _
    simp [Matrix.det_fin_two, sq]
  refine ⟨s, Matrix.GeneralLinearGroup.scalar (Fin 2) s⁻¹ * X * Unitary.toUnits k, k, ?_, ?_⟩
  · refine Units.ext ?_
    rw [map_mul, map_mul]
    simp only [Units.val_mul, hdetk, hdets, Units.val_one]
    rw [← hD, ← hse]
    funext w
    have h1 := congrFun hee w
    have h2 : (s : ι → ℝ) w * ((s⁻¹ : (ι → ℝ)ˣ) : ι → ℝ) w = 1 := congrFun s.mul_inv w
    simp only [Pi.mul_apply, Pi.one_apply] at h1 ⊢
    calc _ = (((s : ι → ℝ) w * ((s⁻¹ : (ι → ℝ)ˣ) : ι → ℝ) w) ^ 2) * (e w * e w) := by ring
      _ = 1 := by rw [h2, h1]; simp
  · have hsc : Matrix.GeneralLinearGroup.scalar (Fin 2) s * Matrix.GeneralLinearGroup.scalar (Fin 2) s⁻¹ = 1 := by
      rw [← map_mul]; simp
    rw [mul_assoc _ _ (Unitary.toUnits k), hk, mul_one, ← mul_assoc, hsc, one_mul]

theorem UpperTheory.ConvolutionTheory.R2.Pp.infDec :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], UpperTheory.ConvolutionTheory.R2.Pp.InfDec F := by
  intro F _ _ _ x
  obtain ⟨s, g, k, hg, hx⟩ := real_dec (GeneralLinearGroup.map (TR.pInf F) x)
  have hdet : GeneralLinearGroup.det (TR.infGL F 2 g) = 1 := by
    rw [TR.det_infGL, hg, map_one]
  have hdet' : (TR.infGL F 2 g).val.det = 1 := congrArg Units.val hdet
  let G : G1 F := ⟨(TR.infGL F 2 g).val, hdet'⟩
  have hG : gl G = TR.infGL F 2 g := Units.ext rfl
  have hsc : Matrix.GeneralLinearGroup.scalar (Fin 2) (TR.infId F s) =
      TR.infGL F 2 (Matrix.GeneralLinearGroup.scalar (Fin 2) s) := by
    have hs : ∀ y, TR.pInf F (TR.sInf F y) = y := fun y => (TR.infEq F).symm_apply_apply y
    have hi : TR.pInf F (TR.infId F s).val = s.val := by
      change TR.pInf F (1 - TR.sInf F 1 + TR.sInf F _) = _
      simp [hs]
    have hf : pFin F (TR.infId F s).val = 1 := by
      change (1 : Af F) - 0 + 0 = 1
      simp
    refine TR.ga_ext ?_ ?_
    · rw [TR.pInf_infGL]
      ext i j
      by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, hi]
    · rw [TR.pFin_infGL]
      ext i j
      by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, hf]
  refine ⟨G, TR.infId F s, k, GeneralLinearGroup.map (pFin F) x, ?_, ?_⟩
  · intro i j
    have h := congrArg (fun h : GL (Fin 2) (Af F) => h.val i j) (TR.pFin_infGL (E := F) g)
    have h1 : ((1 : Matrix (Fin 2) (Fin 2) (A F)) i j).2 = (1 : GL (Fin 2) (Af F)).val i j := by
      by_cases e : i = j
      · simp only [Matrix.one_apply, e, if_true, Units.val_one]
        rfl
      · simp [Matrix.one_apply, e]
    rw [h1]
    exact h
  · rw [hsc, hG]
    conv_lhs => rw [← TR.infGL_mul_finGL x, hx]
    simp only [map_mul, mul_assoc]
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Pp
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker

namespace UpperTheory.ConvolutionTheory.R2.Pp

variable {F : Type} [Field F] [NumberField F]

theorem vn (q : A F) : (nU q).val = !![1, q; 0, 1] := rfl

theorem n_add (x y : A F) : gl (nU (x + y)) = gl (nU x) * gl (nU y) := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vn, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem n_zero : gl (nU (0 : A F)) = 1 := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vn]

theorem cont_n : Continuous fun q : A F => gl (nU q) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [vn] <;> fun_prop
  · have e : ∀ q : A F, (gl (nU q))⁻¹ = gl (nU (-q)) := fun q =>
      inv_eq_of_mul_eq_one_right (by rw [← n_add, add_neg_cancel, n_zero])
    simp only [e]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [vn] <;> fun_prop

theorem rat_n (k : F) : ∃ γ : GL (Fin 2) F, ratGL F 2 γ = gl (nU (rt k)) := by
  refine ⟨Matrix.SpecialLinearGroup.toGL ⟨!![1, k; 0, 1], by simp [Matrix.det_fin_two]⟩, Units.ext ?_⟩
  ext i j
  change algebraMap F (A F) (!![1, k; 0, 1] i j) = _
  fin_cases i <;> fin_cases j <;> simp [vn]

theorem rat_a (t : Fˣ) : ∃ γ : GL (Fin 2) F, ratGL F 2 γ = aE (IdeleGroup.diagonal F t) := by
  refine ⟨⟨!![(t : F), 0; 0, 1], !![((t⁻¹ : Fˣ) : F), 0; 0, 1], by ext i j; fin_cases i <;> fin_cases j <;> simp,
    by ext i j; fin_cases i <;> fin_cases j <;> simp⟩, Units.ext ?_⟩
  ext i j
  change algebraMap F (A F) (!![(t : F), 0; 0, 1] i j) = _
  fin_cases i <;> fin_cases j <;> simp [aE]

theorem a_n (t : (A F)ˣ) (b : A F) : aE t * gl (nU b) = gl (nU ((t : A F) * b)) * aE t := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vn, aE, Matrix.mul_apply, Fin.sum_univ_two]

theorem ψ_add (x y : A F) : ψ (x + y) = ψ x * ψ y := by simp [ψ, AddChar.map_add_eq_mul]

theorem ψ_rt (k : F) : ψ (rt k) = 1 := by simp [ψ, adelicChar_algebraMap]

theorem norm_ψ (x : A F) : ‖ψ x‖ = 1 := Circle.norm_coe _

theorem cont_ψ : Continuous (ψ (F := F)) := continuous_subtype_val.comp continuous_adelicChar

theorem exists_cpt : ∃ C : Set (A F), IsCompact C ∧ fundamentalSet F ⊆ C :=
  ⟨_, (isCompact_closure_fundamentalSetInfinite F).prod (isCompact_integralFiniteAdeles F),
    fun _ hx => ⟨subset_closure hx.1, hx.2⟩⟩

theorem int_one {ι : Type} [Fintype ι] [Unique ι] (h : A F → ℂ) :
    ∫ x in vecDomain F ι, h (x default) ∂(vecMeasure F ι) = ∫ b in fundamentalSet F, h b ∂(adeleMeasure F) := by
  have hp := measurePreserving_funUnique (adeleMeasure F) ι
  have e : vecDomain F ι = MeasurableEquiv.funUnique ι (A F) ⁻¹' fundamentalSet F := by
    ext x
    exact ⟨fun hx => hx default trivial, fun hx i _ => by rw [Unique.eq_default i]; exact hx⟩
  rw [e]
  convert hp.setIntegral_preimage_emb (MeasurableEquiv.measurableEmbedding _) h (fundamentalSet F) using 2
  all_goals first | rfl | congr!

theorem int_add {h : A F → ℂ} (hh : ∀ k x, h (rt k + x) = h x) (a : A F) :
    ∫ b in fundamentalSet F, h (b + a) ∂(adeleMeasure F) = ∫ b in fundamentalSet F, h b ∂(adeleMeasure F) := by
  rw [← int_one (ι := Fin 1), ← int_one (ι := Fin 1) h]
  refine setIntegral_comp_add (fun _ => a) (h := fun x => h (x default)) fun ξ hξ x => ?_
  obtain ⟨η, rfl⟩ := mem_vecLattice.1 hξ
  exact hh _ _

theorem int_mul {h : A F → ℂ} (hh : ∀ k x, h (rt k + x) = h x) (t : Fˣ) :
    ∫ b in fundamentalSet F, h (rt (t : F) * b) ∂(adeleMeasure F) = ∫ b in fundamentalSet F, h b ∂(adeleMeasure F) := by
  rw [← int_one (ι := Fin 1), ← int_one (ι := Fin 1) h,
    ← setIntegral_comp_matVec (Matrix.GeneralLinearGroup.scalar (Fin 1) t) (f := fun x => h (x default)) fun ξ hξ x => by
      obtain ⟨η, rfl⟩ := mem_vecLattice.1 hξ
      exact hh _ _]
  simp [matVec_apply]

theorem Lf.per {f : GL (Fin 2) (A F) → ℂ} (hf : Lf f) (k : F) (x : A F) (g : GL (Fin 2) (A F)) :
    f (gl (nU (rt k + x)) * g) = f (gl (nU x) * g) := by
  obtain ⟨γ, hγ⟩ := rat_n k
  rw [n_add, ← hγ, mul_assoc, hf.2]

theorem intOn {h : A F → ℂ} (hc : Continuous h) : IntegrableOn h (fundamentalSet F) (adeleMeasure F) := by
  obtain ⟨C, hC, hs⟩ := exists_cpt (F := F)
  exact (hc.continuousOn.integrableOn_compact hC).mono_set hs

theorem norm_Wf_le {f : GL (Fin 2) (A F) → ℂ} {g : GL (Fin 2) (A F)} {B : ℝ} (h : ∀ b, ‖f (gl (nU b) * g)‖ ≤ B) :
    ‖Wf f g‖ ≤ B := by
  have := norm_setIntegral_le_of_norm_le_const (μ := adeleMeasure F) (s := fundamentalSet F)
    (f := fun b => f (gl (nU b) * g) * ψ b) (C := B) (by rw [adeleMeasure_fundamentalSet]; exact ENNReal.one_lt_top)
    fun b _ => by rw [norm_mul, norm_ψ, mul_one]; exact h b
  rwa [measureReal_def, adeleMeasure_fundamentalSet, ENNReal.toReal_one, mul_one] at this

end UpperTheory.ConvolutionTheory.R2.Pp
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Pp

theorem UpperTheory.ConvolutionTheory.R2.Pp.isotyp :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], UpperTheory.ConvolutionTheory.R2.Pp.Isotyp F := by
  intro F _ _ _ π v σ h x
  have h1 : (⨆ f : {f : σ.V →ₗ[ℂ] π.V // ∀ g u, f (σ.ρ g u) = π.locRep v g (f u)}, LinearMap.range f.1) = ⊤ := by
    have cpt_fin (k : TR.Kinf F 2) (g : GL (Fin 2) (Af F)) (y : π.V) :
        π.op (.cpt k) (π.finPart g y) = π.finPart g (π.op (.cpt k) y) := by
      refine Subtype.ext ?_
      change (TR.rt F 2 (TR.infGL F 2 (Unitary.toUnits k)) * TR.rt F 2 (GlobalTheory.CuspRep.finGL F 2 g)) y.1 =
        (TR.rt F 2 (GlobalTheory.CuspRep.finGL F 2 g) * TR.rt F 2 (TR.infGL F 2 (Unitary.toUnits k))) y.1
      rw [← map_mul, ← map_mul, TR.infGL_comm]
    have fin_loc {k : GL (Fin 2) (Af F)}
        (hk : GeneralLinearGroup.map (GlobalTheory.CuspRep.pLoc F v) k = 1)
        (g : GL (Fin 2) (v.adicCompletion F)) (y : π.V) :
        π.finPart k (π.locRep v g y) = π.locRep v g (π.finPart k y) := by
      simp only [TR.CuspSub.locRep, MonoidHom.comp_apply]
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, GlobalTheory.CuspRep.LocUniq.comm_locGL v hk]
    let W : Submodule ℂ π.V := ⨆ f : {f : σ.V →ₗ[ℂ] π.V // ∀ g u, f (σ.ρ g u) = π.locRep v g (f u)}, LinearMap.range f.1
    have hact : ∀ g, ∀ x ∈ W, π.locRep v g x ∈ W := by
      intro g x hx
      refine Submodule.mem_comap.1 ((iSup_le (a := Submodule.comap (π.locRep v g) _) fun f => ?_) hx)
      rintro _ ⟨u, rfl⟩
      exact Submodule.mem_iSup_of_mem f ⟨σ.ρ g u, f.2 g u⟩
    have hcomm : ∀ T : Module.End ℂ π.V, (∀ g x, T (π.locRep v g x) = π.locRep v g (T x)) → ∀ x ∈ W, T x ∈ W := by
      intro T hT x hx
      refine Submodule.mem_comap.1 ((iSup_le (a := Submodule.comap T _) fun f => ?_) hx)
      rintro _ ⟨u, rfl⟩
      exact Submodule.mem_iSup_of_mem ⟨T ∘ₗ f.1, fun g u => by
        rw [LinearMap.comp_apply, f.2]; exact hT g _⟩ ⟨u, rfl⟩
    have hop : ∀ o, ∀ x ∈ W, π.op o x ∈ W := fun o x hx => by
      cases o with
      | fin k =>
        have h3 := hact (GeneralLinearGroup.map (GlobalTheory.CuspRep.pLoc F v) k) _ (hcomm
          (π.finPart ((GlobalTheory.CuspRep.locGL F 2 v (GeneralLinearGroup.map (GlobalTheory.CuspRep.pLoc F v) k))⁻¹ * k))
          (fin_loc (GlobalTheory.CuspRep.LocEx.map_pLoc_inv_mul v k)) x hx)
        rwa [TR.CuspSub.locRep, MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] at h3
      | cpt k => exact hcomm _ (fun g y => cpt_fin k _ y) x hx
      | lie X => exact hcomm _ (fun g y => Subtype.ext (LinearMap.congr_fun (TR.lie_rt_fin X (GlobalTheory.CuspRep.locGL F 2 v g)) y.1)) x hx
    have hi := Submodule.map_injective_of_injective π.V.injective_subtype
    rcases π.irred (W.map π.V.subtype) (Submodule.map_subtype_le _ _) (by
      rintro o _ ⟨y, hy, rfl⟩
      exact ⟨_, hop o y hy, rfl⟩) with hb | ht
    · have e : W = ⊥ := hi (hb.trans (Submodule.map_bot _).symm)
      obtain ⟨f, h0, hf⟩ := h
      exact False.elim (h0 (LinearMap.range_eq_bot.1 ((iSup_eq_bot.1 e) ⟨f, hf⟩)))
    · exact hi (ht.trans (Submodule.map_subtype_top _).symm)
  refine (show (⊤ : Submodule ℂ π.V) ≤ _ from h1 ▸ iSup_le fun f => ?_) Submodule.mem_top
  exact fun y hy => Submodule.subset_span ⟨f.1, f.2, hy⟩
end

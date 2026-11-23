module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialOfLocal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle148
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle304
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CountableOfNumberField
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle044
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFieldAdicCompletionTensorOfInert
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle007
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DiscreteTopologyRationalPointsHermitianSpace
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
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
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.DatumF

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
open Filter Topology

noncomputable section

namespace GlobalTheory.DenseAvoid

theorem finite_maximal_not_mem {F B E K : Type} [Field F] [CommRing B] [Algebra F B] [Field E] [Algebra F E]
    [FiniteDimensional F E] [CommRing K] [Algebra F K] [IsArtinianRing K]
    (ρ : B →ₐ[F] K) (hρ : Function.Surjective ρ) (f : B) (hf : f * f = f)
    (hk : ∀ x, ρ x = 0 → f * x = 0) :
    {m : Ideal (B ⊗[F] E) | m.IsMaximal ∧ algebraMap B (B ⊗[F] E) f ∉ m}.Finite := by
  classical
  let Φ : B ⊗[F] E →+* K ⊗[F] E := (Algebra.TensorProduct.map ρ (AlgHom.id F E)).toRingHom
  have hΦ : Function.Surjective Φ :=
    Algebra.TensorProduct.map_surjective ρ (AlgHom.id F E) hρ (fun y => ⟨y, rfl⟩)
  haveI : IsArtinianRing (K ⊗[F] E) := IsArtinianRing.of_finite K (K ⊗[F] E)
  refine ((IsArtinianRing.setOfPred_isMaximal_finite (K ⊗[F] E)).image (Ideal.comap Φ)).subset ?_
  rintro m ⟨hm, hfm⟩
  have h1 : 1 - algebraMap B (B ⊗[F] E) f ∈ m := by
    have h0 : algebraMap B (B ⊗[F] E) f * (1 - algebraMap B (B ⊗[F] E) f) ∈ m := by
      rw [mul_sub, mul_one, ← map_mul, hf, sub_self]; exact m.zero_mem
    exact (hm.isPrime.mem_or_mem h0).resolve_left hfm
  have hker : RingHom.ker Φ ≤ m := by
    have h := Algebra.TensorProduct.rTensor_ker (R := F) (C := E) ρ hρ
    change RingHom.ker (Algebra.TensorProduct.map ρ (AlgHom.id F E)) ≤ m
    rw [h, Ideal.map_le_iff_le_comap]
    intro x hx
    have hx' : f * x = 0 := hk x hx
    change x ⊗ₜ[F] (1 : E) ∈ m
    have e1 : algebraMap B (B ⊗[F] E) f * (x ⊗ₜ[F] (1 : E)) = 0 := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        Algebra.TensorProduct.tmul_mul_tmul, hx', TensorProduct.zero_tmul]
    have e2 : x ⊗ₜ[F] (1 : E) = (1 - algebraMap B (B ⊗[F] E) f) * (x ⊗ₜ[F] (1 : E)) := by
      rw [sub_mul, one_mul, e1, sub_zero]
    rw [e2]; exact m.mul_mem_right _ h1
  have hc : Ideal.comap Φ (m.map Φ) = m := by
    rw [Ideal.comap_map_of_surjective' Φ hΦ, sup_eq_left.2 hker]
  refine ⟨m.map Φ, ?_, hc⟩
  rcases Ideal.map_eq_top_or_isMaximal_of_surjective Φ hΦ hm with h | h
  · exact absurd (by rw [← hc, h, Ideal.comap_top]) hm.ne_top
  · exact h

end GlobalTheory.DenseAvoid

namespace GlobalTheory.DenseAvoid

open GlobalTheory.LocalGlobalChar

variable {F : Type} [Field F] [NumberField F]

theorem eps_eq_sum (S : Finset (HeightOneSpectrum (𝓞 F))) :
    eps S = pairA F 1 0 + ∑ v ∈ S, pairA F 0 (ind {v}) := by
  classical
  have hext : ∀ a b : AF F, fstA F a = fstA F b → sndA F a = sndA F b → a = b := fun a b h1 h2 => Prod.ext h1 h2
  refine hext _ _ ?_ (fin_ext fun u => ?_)

  · rw [map_add (f := _), map_sum]
    change (1 : Ainf F) = 1 + ∑ v ∈ S, (0 : Ainf F)
    rw [Finset.sum_const_zero, add_zero]

  · rw [map_add (f := _), map_sum, map_add (f := _), map_sum]
    change evalV F u (ind S) = evalV F u 0 + ∑ v ∈ S, evalV F u (ind {v})
    simp_rw [ev_ind, Finset.mem_singleton, map_zero, zero_add]
    rw [Finset.sum_ite_eq]

variable {E : Type} [Field E] [Algebra F E] [FiniteDimensional F E]

theorem finite_maximal_not_mem_eps (S : Finset (HeightOneSpectrum (𝓞 F))) :
    {m : Ideal (AF F ⊗[F] E) | m.IsMaximal ∧ algebraMap (AF F) (AF F ⊗[F] E) (eps S) ∉ m}.Finite := by
  classical
  haveI : IsArtinianRing (Ainf F) := inferInstanceAs (IsArtinianRing ((w : InfinitePlace F) → w.Completion))
  have hinf := finite_maximal_not_mem (E := E) (fstA F) (fun y => ⟨pairA F y 0, rfl⟩) (pairA F 1 0)
    (Prod.ext (mul_one _) (mul_zero _)) (fun x hx => Prod.ext (by
      change (1 : Ainf F) * x.1 = 0
      rw [one_mul]; exact hx) (zero_mul _))
  have hfin : ∀ v : HeightOneSpectrum (𝓞 F),
      {m : Ideal (AF F ⊗[F] E) | m.IsMaximal ∧ algebraMap (AF F) (AF F ⊗[F] E) (pairA F 0 (ind {v})) ∉ m}.Finite :=
    fun v => finite_maximal_not_mem (E := E) ((evalV F v).comp (sndA F))
      (fun y => ⟨pairA F 0 (singleV F v y), GlobalTheory.SplitCoord.evalV_single v y⟩) (pairA F 0 (ind {v}))
      (pl_mul_self v) (fun x hx => Prod.ext (zero_mul _) (fin_ext fun u => by
        change evalV F u (ind {v} * x.2) = evalV F u 0
        rw [map_mul, ev_ind, map_zero]
        split_ifs with h
        · rw [Finset.mem_singleton] at h
          subst h
          change evalV F u x.2 = 0 at hx
          rw [hx, mul_zero]
        · exact zero_mul _))
  refine (hinf.union (S.finite_toSet.biUnion fun v _ => hfin v)).subset ?_
  rintro m ⟨hm, hem⟩
  by_contra hn
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion, not_or, not_and, not_not, not_exists] at hn
  apply hem

  rw [eps_eq_sum, map_add (f := _), map_sum]
  exact m.add_mem (hn.1 hm) (m.sum_mem fun v hv => hn.2 v hv hm)

end GlobalTheory.DenseAvoid


open GlobalTheory.DenseAvoid in
theorem GlobalTheory.DenseAvoid.exists_unit_eval : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (S : Finset (HeightOneSpectrum (𝓞 F))) (ψ : Polynomial (AE F E)), (∀ (Ω : Type) [Field Ω] (φ : AE F E →+* Ω), φ (algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S)) = 1 → ψ.map φ ≠ 0) → ∃ t : F, IsUnit (algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S) * ψ.eval (algebraMap F (AE F E) t) + (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S))) := by
  intro F E _ _ _ _ _ S ψ hψ
  classical
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : Infinite F := Infinite.of_injective (Nat.cast : ℕ → F) Nat.cast_injective
  set e := algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S) with he_def
  have he : e * e = e := by rw [he_def, ← map_mul, GlobalTheory.LocalGlobalChar.eps_mul_self]
  have hone : ∀ m : Ideal (AE F E), m.IsPrime → e ∉ m → 1 - e ∈ m := fun m hm hem => by
    have h0 : e * (1 - e) ∈ m := by rw [mul_sub, mul_one, he, sub_self]; exact m.zero_mem
    exact (hm.mem_or_mem h0).resolve_left hem
  have hM := finite_maximal_not_mem_eps (E := E) S
  let bad : Set F := ⋃ m ∈ {m : Ideal (AE F E) | m.IsMaximal ∧ e ∉ m},
    {t : F | Ideal.Quotient.mk m (ψ.eval (algebraMap F (AE F E) t)) = 0}
  have hbad : bad.Finite := by
    refine hM.biUnion fun m hm => ?_
    haveI := hm.1
    letI := Ideal.Quotient.field m
    have h1 : Ideal.Quotient.mk m e = 1 := by
      rw [← map_one (Ideal.Quotient.mk m), Ideal.Quotient.eq, ← neg_sub]
      exact m.neg_mem (hone m hm.1.isPrime hm.2)
    have hne := hψ (AE F E ⧸ m) (Ideal.Quotient.mk m) h1
    let j : F →+* AE F E ⧸ m := (Ideal.Quotient.mk m).comp (algebraMap F (AE F E))
    refine ((Polynomial.finite_setOf_isRoot hne).preimage j.injective.injOn).subset fun t ht => ?_
    change Ideal.Quotient.mk m (ψ.eval (algebraMap F (AE F E) t)) = 0 at ht
    change Polynomial.IsRoot _ (j t)
    rw [Polynomial.IsRoot.def, Polynomial.eval_map, RingHom.comp_apply, Polynomial.eval₂_hom, ht]
  obtain ⟨t, ht⟩ := hbad.infinite_compl.nonempty
  refine ⟨t, ?_⟩
  by_contra hn
  obtain ⟨m, hm, hxm⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hn)
  by_cases hem : e ∈ m
  · have h2 : 1 - e ∈ m := by
      have := m.sub_mem hxm (m.mul_mem_right (ψ.eval (algebraMap F (AE F E) t)) hem)
      rwa [add_sub_cancel_left] at this
    exact hm.ne_top ((Ideal.eq_top_iff_one m).2 (by simpa using m.add_mem hem h2))
  · have h2 : e * ψ.eval (algebraMap F (AE F E) t) ∈ m := by
      have := m.sub_mem hxm (hone m hm.isPrime hem)
      rwa [add_sub_cancel_right] at this
    have h3 := (hm.isPrime.mem_or_mem h2).resolve_left hem
    apply ht
    simp only [bad, Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨m, ⟨hm, hem⟩, Ideal.Quotient.eq_zero_iff_mem.2 h3⟩
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.VacAny

variable {F : Type} [Field F] [NumberField F]

scoped instance invTwoV (v : HeightOneSpectrum (𝓞 F)) : Invertible (2 : Fv F v) :=
  invertibleOfNonzero (by
    rw [← map_ofNat (algebraMap F (Fv F v)) 2]
    exact (map_ne_zero _).2 two_ne_zero)

def psiV (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) : AddChar (Fv F v) ℂ :=
  ψ.compAddMonoidHom (GlobalTheory.EmbChart.atPlace v).toAddMonoidHom

theorem psiV_apply (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (t : Fv F v) :
    psiV ψ v t = ψ (GlobalTheory.EmbChart.atPlace v t) := rfl

theorem psiV_eq_psiLoc (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (t : Fv F v) :
    psiV ψ v t = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.psiLoc ψ v t := rfl

theorem continuous_atPlace (v : HeightOneSpectrum (𝓞 F)) : Continuous (GlobalTheory.EmbChart.atPlace v) := by
  have h : (GlobalTheory.EmbChart.atPlace v : Fv F v → AF F) = fun t => (0, GlobalTheory.AdelicU.singleFin v t) := rfl
  rw [h]
  exact continuous_const.prodMk (GlobalTheory.AdelicU.continuous_singleFin v)

theorem continuous_psiV {ψ : AddChar (AF F) ℂ} (hψ : Continuous ψ) (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (psiV ψ v) :=
  hψ.comp (continuous_atPlace v)

section At

variable {v : HeightOneSpectrum (𝓞 F)}

local notation "ev" => GlobalTheory.AdelicU.evFin F v

theorem evFin_invOf_two : ev (⅟(2 : AF F)) = ⅟(2 : Fv F v) := by
  refine (invOf_eq_right_inv ?_).symm
  have h : ev (2 * ⅟(2 : AF F)) = 1 := by rw [mul_invOf_self, map_one]
  rwa [map_mul, map_ofNat] at h

theorem at_atPlace (t : Fv F v) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At ev (GlobalTheory.EmbChart.atPlace v t) := fun u hu => by
  rw [smul_eq_mul, mul_comm, GlobalTheory.EmbChart.atPlace_mul_right, hu, mul_zero, map_zero]

theorem at_mul_right {x : AF F} (hx : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At ev x) (y : AF F) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At ev (x * y) := fun u hu => by
  rw [smul_eq_mul, ← mul_assoc, show u * x = 0 from hx u hu, zero_mul]

theorem at_mul_left (x : AF F) {y : AF F} (hy : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At ev y) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At ev (x * y) := by
  rw [mul_comm]; exact at_mul_right hy x

theorem at_add {x y : AF F} (hx : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At ev x) (hy : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At ev y) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At ev (x + y) := fun u hu => by rw [smul_add, hx u hu, hy u hu, add_zero]

theorem at_zero : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At ev (0 : AF F) := fun u _ => smul_zero u

theorem at_neg {x : AF F} (hx : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At ev x) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At ev (-x) := fun u hu => by
  rw [smul_neg, hx u hu, neg_zero]

theorem at_sub {x y : AF F} (hx : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At ev x) (hy : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At ev y) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At ev (x - y) := by
  rw [sub_eq_add_neg]; exact at_add hx (at_neg hy)

theorem at_sum {ι : Type} (s : Finset ι) {f : ι → AF F} (h : ∀ i ∈ s, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At ev (f i)) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At ev (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact at_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact at_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem at_pi {κ : Type} {z : κ → AF F} (h : ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At ev (z i)) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At ev z := fun u hu => funext fun i => h i u hu

end At

end GlobalTheory.VacAny
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

open MeasureTheory

namespace GlobalTheory.NormModule

theorem norm_inclR (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (z : E) :
    Algebra.norm (AF F) (inclR (F := F) (AF F) z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = algebraMap F (AF F) (Algebra.norm F z) := by
  have e : (inclR (F := F) (AF F) z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = (1 : AF F) ⊗ₜ[F] z := rfl
  rw [e, Algebra.norm_apply, Algebra.norm_apply, ← Algebra.baseChange_lmul, LinearMap.det_baseChange]

theorem modu_rat (F : Type) [Field F] [NumberField F] (w : (AF F)ˣ) (t : F) (hw : (w : AF F) = algebraMap F (AF F) t) :
    distribHaarChar (AdeleRing (𝓞 F) F) w = 1 := by
  haveI : Nontrivial (AF F) :=
    nontrivial_of_ne 0 1 (fun h => zero_ne_one (congrArg (fun a : AF F => a.1) h))
  have ht : t ≠ 0 := by
    rintro rfl
    rw [map_zero] at hw
    exact not_isUnit_zero (hw ▸ w.isUnit)
  obtain ⟨ν, hν⟩ := GlobalTheory.SWQ.exists_adeles_haarMeasure_covolume_one F
  haveI := hν.1
  have h1 := GlobalTheory.SWQ.modrat_main F 0 ν hν t ht
  have h2 := GlobalTheory.SWQ.map_unit_mul_eq F ν w
  have e : (fun x : AF F => w • x) = fun x => algebraMap F (AF F) t * x := by
    funext x; rw [Units.smul_def, smul_eq_mul, hw]
  rw [e, h1] at h2
  obtain ⟨K, hKc, hK0⟩ : ∃ K : Set (AF F), IsCompact K ∧ K ∈ nhds (0 : AF F) := exists_compact_mem_nhds 0
  have h3 := congrArg (fun m : Measure (AF F) => m K) h2
  simp only [Measure.smul_apply, smul_eq_mul] at h3
  have h4 : ((distribHaarChar (AF F) w⁻¹ : NNReal) : ENNReal) = 1 :=
    ((ENNReal.mul_left_inj (Measure.measure_pos_of_mem_nhds ν hK0).ne' hKc.measure_lt_top.ne).1
      (h3.symm.trans (one_mul _).symm))
  have h5 : distribHaarChar (AF F) w⁻¹ = 1 := by exact_mod_cast h4
  rw [map_inv, inv_eq_one] at h5
  exact h5

end GlobalTheory.NormModule

theorem GlobalTheory.NormModule.modu_norm_rat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (u : (AE F E)ˣ) (z : E), (u : AE F E) = inclR (AF F) z → (adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) u) = 1 := by
  intro F E _ _ _ _ _ u z hu
  apply GlobalTheory.NormModule.modu_rat F _ (Algebra.norm F z)
  rw [Units.coe_map, hu, GlobalTheory.NormModule.norm_inclR]
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.InertTensorField

theorem isField_tensor_of_isInertAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → IsField (Fv F v ⊗[F] E) := by
  intro F E _ _ _ _ _ σ B hB v w hvw
  have hp : (v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))).IsPrime := by
    rw [show v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) = w.asIdeal from hvw]
    exact w.isPrime
  exact GlobalTheory.InertField.isField_of_inert F E hB.cm.2.2.1 v hp

end GlobalTheory.InertTensorField
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

noncomputable section

namespace GlobalTheory.DiagThetaRatF

open MeasureTheory

theorem setIntegral_comp_aut {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G)
    [Countable Γ] {K : Set G} (hK : IsCompact K) (hcov : ∀ x : G, ∃ γ ∈ Γ, γ + x ∈ K) (ν : Measure G)
    [ν.IsAddHaarMeasure] {𝓕 : Set G} (h𝓕 : IsAddFundamentalDomain Γ 𝓕 ν) (e : G ≃+ G) (he : Continuous e)
    (he' : Continuous e.symm) (hΓ : ∀ x ∈ Γ, e x ∈ Γ) (hΓ' : ∀ x ∈ Γ, e.symm x ∈ Γ) (φ : G → ℂ)
    (hφ : ∀ γ ∈ Γ, ∀ x, φ (γ + x) = φ x) : ∫ x in 𝓕, φ (e x) ∂ν = ∫ x in 𝓕, φ x ∂ν := by
  let h : G ≃ₜ G := .mk e.toEquiv he he'
  let m : G ≃ᵐ G := h.toMeasurableEquiv
  haveI : (ν.map e).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map ν e he he'
  have hmp : MeasurePreserving m ν (ν.map e) := ⟨he.measurable, rfl⟩
  have hT : IsAddFundamentalDomain Γ (m.symm ⁻¹' 𝓕) (ν.map e) := by
    refine h𝓕.preimage_of_equiv hmp.symm.quasiMeasurePreserving (e := fun γ : Γ => (⟨e γ, hΓ _ γ.2⟩ : Γ)) ⟨?_, ?_⟩ ?_
    · intro a b hab
      exact Subtype.ext (e.injective (congrArg Subtype.val hab))
    · intro a
      exact ⟨⟨e.symm a, hΓ' _ a.2⟩, Subtype.ext (e.apply_symm_apply _)⟩
    · intro γ x
      show e.symm (e γ + x) = γ + e.symm x
      rw [map_add (f := _), e.symm_apply_apply]
  obtain ⟨c, hc⟩ : ∃ c : NNReal, ν.map e = c • ν := ⟨_, Measure.isAddLeftInvariant_eq_smul _ ν⟩
  have hac : ν.map e ≪ ν := hc ▸ Measure.smul_absolutelyContinuous
  have hF' : IsAddFundamentalDomain Γ 𝓕 (ν.map e) := h𝓕.mono hac
  have hpre : m ⁻¹' (m.symm ⁻¹' 𝓕) = 𝓕 := by
    ext x
    simp
  have h0 : ν 𝓕 ≠ 0 := h𝓕.measure_ne_zero (NeZero.ne ν)
  have h1 : ν 𝓕 ≠ ⊤ := (GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact Γ hK hcov ν h𝓕).ne
  have e1 : ν.map e (m.symm ⁻¹' 𝓕) = ν 𝓕 := by
    have := m.map_apply (μ := ν) (m.symm ⁻¹' 𝓕)
    rw [hpre] at this
    exact this
  have hc1 : (c : ENNReal) = 1 := by
    have e2 := hT.measure_eq hF'
    rw [e1, hc, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at e2
    exact ((ENNReal.mul_left_inj h0 h1).1 ((one_mul _).trans e2)).symm
  have hν : ν.map e = ν := by
    rw [hc, ENNReal.coe_eq_one.1 hc1, one_smul]
  have e3 := hmp.setIntegral_preimage_emb m.measurableEmbedding φ (m.symm ⁻¹' 𝓕)
  rw [hpre] at e3
  refine e3.trans ?_
  rw [hT.setIntegral_eq hF' fun g x => hφ g g.2 x, hν]

section Mat

variable {R : Type} [CommRing R] {m n : ℕ}

end Mat

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem inclR_injective : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
  Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F)

theorem det_ne_zero_of_unit {n : ℕ} (g : GL (Fin n) (AF F ⊗[F] E)) (g₀ : Matrix (Fin n) (Fin n) E)
    (h : g.1 = incM F g₀) : g₀.det ≠ 0 := fun h0 => by
  haveI : Nontrivial (AF F ⊗[F] E) := (inclR_injective (F := F) (E := E)).nontrivial
  have := (Matrix.GeneralLinearGroup.det g).ne_zero
  rw [Matrix.GeneralLinearGroup.val_det_apply, h] at this
  refine this ?_
  have e : (incM F g₀).det = inclR (F := F) (AF F) g₀.det := by
    rw [RingHom.map_det]; rfl
  rw [e, h0, map_zero]

variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}

end Adelic

end GlobalTheory.DiagThetaRatF

end
end

section

open scoped TensorProduct Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.RatUDiscrete

theorem discreteTopology_ratU : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), DiscreteTopology (ratU σ J) := by
  intro F E _ _ _ _ _ σ n J
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := F) (E := E)
  obtain ⟨U, hU, h⟩ := GlobalTheory.RationalDiscrete.exists_nhds_zero_inclR (F := F) (E := E)
  refine discreteTopology_of_isOpen_singleton_one ?_
  let f : ratU σ J → Matrix (Fin n) (Fin n) (AF F ⊗[F] E) :=
    fun g => ((g.1.1 : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) - 1
  have hf : Continuous f :=
    (Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)).sub
      continuous_const
  have hf1 : f 1 = 0 := sub_self _
  rw [isOpen_singleton_iff_nhds_eq_pure]
  refine le_antisymm (fun s hs => Filter.mem_of_superset (x := {1}) ?_ (Set.singleton_subset_iff.2 hs))
    (pure_le_nhds _)
  have hW : (⋂ i, ⋂ j, (fun g => f g i j) ⁻¹' U) ∈ 𝓝 (1 : ratU σ J) :=
    Filter.iInter_mem.2 fun i => Filter.iInter_mem.2 fun j =>
      (hf.matrix_elem i j).continuousAt.preimage_mem_nhds (by
        show U ∈ 𝓝 (f 1 i j)
        rw [hf1]; exact hU)
  refine Filter.mem_of_superset hW fun g hg => ?_
  obtain ⟨γ, hγ⟩ := MonoidHom.mem_range.1 (Subgroup.mem_subgroupOf.1 g.2)
  have hfg : ∀ i j, f g i j =
      inclR (F := F) (AF F) (((γ : Matrix (Fin n) (Fin n) E) - 1 : Matrix (Fin n) (Fin n) E) i j) := by
    intro i j
    show (((g.1.1 : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) - 1) i j = _
    rw [← hγ, Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.one_apply, Matrix.one_apply,
      apply_ite (inclR (F := F) (AF F)), map_one, map_zero]
    rfl
  have hγ1 : γ = 1 := by
    refine Units.ext (sub_eq_zero.1 (Matrix.ext fun i j => h _ ?_))
    rw [Units.val_one, ← hfg]
    exact Set.mem_iInter.1 (Set.mem_iInter.1 hg i) j
  refine Subtype.ext (Subtype.ext ?_)
  rw [← hγ, hγ1, map_one]
  rfl

end GlobalTheory.RatUDiscrete
end

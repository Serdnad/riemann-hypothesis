module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.Bundle003
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.AdeleLC
import GroundTheory.GlobalFields.LocalFieldAtPlace
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open PositivityTheory.SiegelWeilFormula.KWhit.Ht

namespace PositivityTheory.SiegelWeilFormula.HeightDict

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem isModuleTopology_tens (v : HeightOneSpectrum (𝓞 F)) :
    IsModuleTopology (v.adicCompletion F) (v.adicCompletion F ⊗[F] E) := ⟨rfl⟩

theorem OE_eq_image (v : HeightOneSpectrum (𝓞 F)) :
    (OE E v : Set (v.adicCompletion F ⊗[F] E)) =
      (fun c : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → v.adicCompletion F =>
        ∑ j, c j ⊗ₜ[F] ((RingOfIntegers.basis E j : 𝓞 E) : E)) ''
        Set.pi Set.univ (fun _ => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
  set ω := RingOfIntegers.basis E
  ext z
  constructor
  · intro hz
    refine AddSubgroup.closure_induction (p := fun z _ => z ∈ (fun c : Module.Free.ChooseBasisIndex ℤ (𝓞 E) →
        v.adicCompletion F => ∑ j, c j ⊗ₜ[F] ((ω j : 𝓞 E) : E)) ''
        Set.pi Set.univ (fun _ => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨a, ha, o, rfl⟩
      refine ⟨fun j => (ω.repr o j) • a, fun j _ => zsmul_mem ha _, ?_⟩
      have ho : (o : E) = ∑ j, (ω.repr o j) • ((ω j : 𝓞 E) : E) := by
        conv_lhs => rw [← ω.sum_repr o]
        simp
      simp only
      rw [ho, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show a ⊗ₜ[F] ((ω.repr o j) • ((ω j : 𝓞 E) : E)) = (ω.repr o j) • (a ⊗ₜ[F] ((ω j : 𝓞 E) : E)) from
          map_zsmul (TensorProduct.mk F (v.adicCompletion F) E a) _ _,
        show ((ω.repr o j) • a) ⊗ₜ[F] ((ω j : 𝓞 E) : E) = (ω.repr o j) • (a ⊗ₜ[F] ((ω j : 𝓞 E) : E)) from
          map_zsmul ((TensorProduct.mk F (v.adicCompletion F) E).flip ((ω j : 𝓞 E) : E)) _ _]
    · exact ⟨0, fun j _ => zero_mem _, by simp⟩
    · rintro x y - - ⟨c, hc, rfl⟩ ⟨c', hc', rfl⟩
      exact ⟨c + c', fun j _ => add_mem (hc j trivial) (hc' j trivial),
        by simp [TensorProduct.add_tmul, Finset.sum_add_distrib]⟩
    · rintro x - ⟨c, hc, rfl⟩
      exact ⟨-c, fun j _ => neg_mem (hc j trivial), by simp [TensorProduct.neg_tmul]⟩
  · rintro ⟨c, hc, rfl⟩
    exact AddSubgroup.sum_mem _ fun j _ => AddSubgroup.subset_closure ⟨c j, hc j trivial, ω j, rfl⟩

theorem OE_isCompact (v : HeightOneSpectrum (𝓞 F)) : IsCompact (OE E v : Set (v.adicCompletion F ⊗[F] E)) := by
  rw [OE_eq_image]
  haveI := isModuleTopology_tens (E := E) v
  haveI : IsTopologicalRing (v.adicCompletion F ⊗[F] E) := GlobalTheory.Doubling.isTopologicalRing_tens
  refine (isCompact_univ_pi fun _ => Formalism.L2.S.S7.AdeleLC.isCompact_integers v).image ?_
  refine continuous_finsetSum _ fun j _ => ?_
  have hc : Continuous fun a : v.adicCompletion F => a ⊗ₜ[F] ((RingOfIntegers.basis E j : 𝓞 E) : E) := by
    have : (fun a : v.adicCompletion F => a ⊗ₜ[F] ((RingOfIntegers.basis E j : 𝓞 E) : E)) =
        fun a => a • ((1 : v.adicCompletion F) ⊗ₜ[F] ((RingOfIntegers.basis E j : 𝓞 E) : E)) := by
      funext a; rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    haveI : ContinuousSMul (v.adicCompletion F) (v.adicCompletion F ⊗[F] E) := IsModuleTopology.toContinuousSMul _ _
    exact (continuous_id (X := v.adicCompletion F)).smul
      (continuous_const (y := ((1 : v.adicCompletion F) ⊗ₜ[F] ((RingOfIntegers.basis E j : 𝓞 E) : E))))
  exact hc.comp (continuous_apply j)

theorem OE_isOpen (v : HeightOneSpectrum (𝓞 F)) : IsOpen (OE E v : Set (v.adicCompletion F ⊗[F] E)) := by
  haveI := isModuleTopology_tens (E := E) v
  haveI : IsTopologicalRing (v.adicCompletion F ⊗[F] E) := GlobalTheory.Doubling.isTopologicalRing_tens
  obtain ⟨s, b, hb⟩ := FiniteDimensional.exists_is_basis_integral (𝓞 F) F E
  set B := Algebra.TensorProduct.basis (v.adicCompletion F) b
  have hcont : Continuous B.equivFun := IsModuleTopology.continuous_of_linearMap B.equivFun.toLinearMap
  set U := B.equivFun ⁻¹' Set.pi Set.univ (fun _ => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) with hUdef
  have hU : IsOpen U :=
    (isOpen_set_pi Set.finite_univ fun _ _ => Formalism.L2.S.S7.AdeleLC.isOpen_integers v).preimage hcont
  have hUO : U ⊆ OE E v := by
    intro z hz
    rw [← B.sum_equivFun z]
    refine AddSubgroup.sum_mem _ fun i _ => AddSubgroup.subset_closure
      ⟨B.equivFun z i, hz i trivial, ⟨b i, isIntegral_trans (R := ℤ) _ (hb i)⟩, ?_⟩
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rfl
  have h0 : (0 : v.adicCompletion F ⊗[F] E) ∈ U := by
    simp only [hUdef, Set.mem_preimage, map_zero, Set.mem_pi, Set.mem_univ, Pi.zero_apply, SetLike.mem_coe,
      forall_const]
    exact fun _ => zero_mem _
  exact AddSubgroup.isOpen_of_mem_nhds (OE E v) (Filter.mem_of_superset (hU.mem_nhds h0) hUO)

theorem lat_isCO (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) : Gen.IsCO (lat E v n) := by
  have hs : (lat E v n : Set (Fin n → v.adicCompletion F ⊗[F] E)) = Set.pi Set.univ fun _ => (OE E v : Set _) := by
    ext y; simp [lat, AddSubgroup.mem_pi]
  refine ⟨?_, ?_⟩
  · rw [hs]; exact isOpen_set_pi Set.finite_univ fun _ _ => OE_isOpen v
  · rw [hs]; exact isCompact_univ_pi fun _ => OE_isCompact v

end PositivityTheory.SiegelWeilFormula.HeightDict
end
end

section

noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain

namespace PositivityTheory.SiegelWeilFormula.HeightDict

open PositivityTheory.SiegelWeilFormula.KWhit.Ht

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem sig_sig (hcm : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨-, hE, -, h⟩ := hcm
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h, h, star_star]

theorem sgv_sgv (hcm : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ) (v : HeightOneSpectrum (𝓞 F)) (z : v.adicCompletion F ⊗[F] E) :
    HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ z) = z := by
  induction z using TensorProduct.inductionOn with
  | tmul a b => simp [HeckeCharacterZeroLocus.SiegelWeilU.sigR, sig_sig hcm]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

omit [NumberField E] in
theorem OE_gen_mul (v : HeightOneSpectrum (𝓞 F)) {a b : v.adicCompletion F ⊗[F] E}
    (ha : ∃ a₀ ∈ v.adicCompletionIntegers F, ∃ o : 𝓞 E, a = a₀ ⊗ₜ[F] (o : E))
    (hb : ∃ b₀ ∈ v.adicCompletionIntegers F, ∃ o : 𝓞 E, b = b₀ ⊗ₜ[F] (o : E)) :
    ∃ c₀ ∈ v.adicCompletionIntegers F, ∃ o : 𝓞 E, a * b = c₀ ⊗ₜ[F] (o : E) := by
  obtain ⟨a₀, ha₀, o, rfl⟩ := ha
  obtain ⟨b₀, hb₀, o', rfl⟩ := hb
  exact ⟨a₀ * b₀, mul_mem ha₀ hb₀, o * o', by simp [Algebra.TensorProduct.tmul_mul_tmul]⟩

omit [NumberField E] in
theorem OE_mul (v : HeightOneSpectrum (𝓞 F)) {a b : v.adicCompletion F ⊗[F] E} (ha : a ∈ OE E v) (hb : b ∈ OE E v) :
    a * b ∈ OE E v := by
  induction ha using AddSubgroup.closure_induction with
  | mem x hx =>
    induction hb using AddSubgroup.closure_induction with
    | mem y hy => exact AddSubgroup.subset_closure (OE_gen_mul v hx hy)
    | zero => simp
    | add y y' _ _ h h' => rw [mul_add]; exact add_mem h h'
    | neg y _ h => rw [mul_neg]; exact neg_mem h
  | zero => simp
  | add x x' _ _ h h' => rw [add_mul]; exact add_mem h h'
  | neg x _ h => rw [neg_mul]; exact neg_mem h

omit [NumberField E] in
theorem OE_one (v : HeightOneSpectrum (𝓞 F)) : (1 : v.adicCompletion F ⊗[F] E) ∈ OE E v :=
  AddSubgroup.subset_closure ⟨1, one_mem _, 1, by simp [Algebra.TensorProduct.one_def]⟩


variable (E) in
def OEsub (v : HeightOneSpectrum (𝓞 F)) : Subring (v.adicCompletion F ⊗[F] E) :=
  { OE E v with
    one_mem' := OE_one v
    mul_mem' := fun ha hb => OE_mul v ha hb }

omit [NumberField E] in
theorem OE_sig (v : HeightOneSpectrum (𝓞 F)) {z : v.adicCompletion F ⊗[F] E} (hz : z ∈ OE E v) :
    HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ z ∈ OE E v := by
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, o, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨a, ha, ⟨σ o, ?_⟩, ?_⟩
    · exact (o.2.map σ)
    · simp [HeckeCharacterZeroLocus.SiegelWeilU.sigR]
      rfl
  | zero => simp
  | add x x' _ _ h h' => rw [map_add]; exact add_mem h h'
  | neg x _ h => rw [map_neg]; exact neg_mem h

omit [NumberField E] in
theorem mem_lat (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (y : Fin n → v.adicCompletion F ⊗[F] E) :
    y ∈ lat E v n ↔ ∀ i, y i ∈ OE E v := by
  simp [lat, AddSubgroup.mem_pi]

end PositivityTheory.SiegelWeilFormula.HeightDict
end
end

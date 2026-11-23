module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.PairHermZeroRight
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.TraceEqAdd
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.ProdEta
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.BHRSmulRight
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle007
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
import Mathlib.RingTheory.PiTensorProduct
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
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle005

@[expose] public section

section

noncomputable section

namespace PI.OmLocU.SdB

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.VolStabSW
open scoped TensorProduct

section DualH

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

theorem b_tr_sig (hcm : IsCMExt F E σ) (w : Fv F v ⊗[F] E) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (sigR (Fv F v) σ w) = Algebra.trace (Fv F v) (Fv F v ⊗[F] E) w := by
  have hinv := b_sig_sig σ hcm
  have hnt := b_sig_nt σ hcm
  have hfin : Module.finrank F E = 2 := hcm.2.2.1
  apply (algebraMap (Fv F v) (Fv F v ⊗[F] E)).injective
  rw [trace_v v σ hinv hnt hfin, trace_v v σ hinv hnt hfin, sigR_sigR v σ hinv, add_comm]

def hm {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (i j : Fin a) (c : Fv F v ⊗[F] E) : HermR (Fv F v) σ a :=
  ⟨Matrix.single i j c + Matrix.single j i (sigR (Fv F v) σ c), fun p q => by
    simp only [Matrix.add_apply, Matrix.single_apply]
    rw [map_add (f := _), apply_ite (sigR (Fv F v) σ), apply_ite (sigR (Fv F v) σ), map_zero, sigR_sigR v σ hinv, add_comm]
    congr 1 <;> exact if_congr and_comm rfl rfl⟩

theorem coe_hm {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (i j : Fin a) (c : Fv F v ⊗[F] E) :
    (hm σ v hinv i j c : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) =
      Matrix.single i j c + Matrix.single j i (sigR (Fv F v) σ c) := rfl

theorem hm_mem {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (i j : Fin a) {c : Fv F v ⊗[F] E}
    (hc : c ∈ OEv (E := E) v) : hm σ v hinv i j c ∈ HO σ v a := by
  intro p q
  rw [coe_hm, Matrix.add_apply, Matrix.single_apply, Matrix.single_apply]
  refine Submodule.add_mem _ ?_ ?_
  · split_ifs
    · exact hc
    · exact Submodule.zero_mem _
  · split_ifs
    · exact b_sigR_mem v σ hc
    · exact Submodule.zero_mem _

theorem sum_eq_trace {a : ℕ} (M N : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :
    ∑ p, ∑ q, M p q * N q p = (M * N).trace := by
  rfl

theorem half_two : algebraMap F (Fv F v) (1 / 2) * 2 = 1 := by
  rw [← map_ofNat (algebraMap F (Fv F v)) 2, ← map_mul, one_div, inv_mul_cancel₀ two_ne_zero, map_one]

theorem half_mul (t : Fv F v) : algebraMap F (Fv F v) (1 / 2) * (t + t) = t := by
  rw [← two_mul, ← mul_assoc, half_two, one_mul]

theorem pair_hm (hcm : IsCMExt F E σ) {a : ℕ} (i j : Fin a) (c : Fv F v ⊗[F] E) (T : HermR (Fv F v) σ a) :
    pairHerm (Fv F v) σ a (hm σ v (b_sig_sig σ hcm) i j c) T =
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (c * (T : Matrix (Fin a) (Fin a) _) j i) := by
  unfold pairHerm
  rw [sum_eq_trace, coe_hm, add_mul, Matrix.trace_add, Matrix.trace_single_mul, Matrix.trace_single_mul,
    smul_eq_mul, smul_eq_mul, ← T.2 i j, ← map_mul (sigR (Fv F v) σ), map_add, b_tr_sig σ v hcm, half_mul]

theorem pairHerm_smul_right' {a : ℕ} (s : Fv F v) (S T : HermR (Fv F v) σ a) :
    pairHerm (Fv F v) σ a S (s • T) = s * pairHerm (Fv F v) σ a S T := by
  simp only [pairHerm, coe_hermSMul, Matrix.smul_apply, mul_smul_comm, ← Finset.smul_sum, map_smul,
    smul_eq_mul]
  ring

theorem pair_int (hcm : IsCMExt F E σ) {a : ℕ} {S T : HermR (Fv F v) σ a} (hS : S ∈ HO σ v a) (hT : T ∈ HO σ v a) :
    pairHerm (Fv F v) σ a S T ∈ v.adicCompletionIntegers F := by
  have hinv := b_sig_sig σ hcm
  have hnt := b_sig_nt σ hcm
  have hfin : Module.finrank F E = 2 := hcm.2.2.1
  set u := ∑ p, ∑ q, (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) p q * (T : Matrix (Fin a) (Fin a) _) q p
    with hudef
  have hu : u ∈ OEv (E := E) v :=
    sum_mem fun p _ => sum_mem fun q _ => b_mul_mem v (hS p q) (hT q p)
  have hfix : sigR (Fv F v) σ u = u := by

    rw [hudef, map_sum]

    simp only [map_sum, map_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [← S.2 p q, ← T.2 q p]
  have hsc : sc (E := E) v (pairHerm (Fv F v) σ a S T) = u := by
    have htr : sc (E := E) v (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) u) = u + u := by
      rw [b_sc_eq, trace_v v σ hinv hnt hfin, hfix]
    have h2 : sc (E := E) v (algebraMap F (Fv F v) (1 / 2)) * 2 = 1 := by
      have e2 : (2 : Fv F v ⊗[F] E) = sc (E := E) v 2 := by rw [b_sc_eq, map_ofNat]
      rw [e2, b_sc_eq, b_sc_eq, ← map_mul, half_two, map_one]
    have hm2 : ∀ x y : Fv F v, sc (E := E) v (x * y) = sc (E := E) v x * sc (E := E) v y := fun x y => by
      simp only [b_sc_eq, map_mul]
    unfold pairHerm
    rw [← hudef, hm2, htr, ← two_mul, ← mul_assoc, h2, one_mul]
  exact b_int_of_sc v (hsc ▸ hu)

theorem dualH_of_perf (a : ℕ) (hP : TrPerf σ J ψ v) : DualH σ J ψ v a := by
  intro hS hU
  have hcm := hS.1
  have hd0 := dV_ne_zero v
  ext T
  simp only [Set.mem_ofPred_eq, SetLike.mem_coe, mem_smulSub]
  constructor
  · intro h
    refine ⟨dV v • T, fun i j => ?_, by rw [smul_smul, inv_mul_cancel₀ hd0, one_smul]⟩
    rw [coe_hermSMul, Matrix.smul_apply, Algebra.smul_def]
    refine hP hS hU _ fun c hc => ?_
    have h1 := h _ (hm_mem σ v (b_sig_sig σ hcm) j i hc)
    rw [pair_hm σ v hcm] at h1
    rw [mul_left_comm, ← b_sc_eq, b_tr_sc]
    exact h1
  · rintro ⟨T', hT', rfl⟩ S hS'
    rw [pairHerm_smul_right', ← mul_assoc, mul_inv_cancel₀ hd0, one_mul]
    exact pair_int σ v hcm hS' hT'

end DualH

end PI.OmLocU.SdB
end
end

section

noncomputable section

namespace PI.OmLocU.SdB

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.VolStabSW
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem genIdx {W : Type} [AddCommGroup W] [Module (Fv F v) W] {ι : Type} [Fintype ι] (M : AddSubgroup W)
    (b : ι → W) (hb : LinearIndependent (Fv F v) b)
    (hmem : ∀ x, x ∈ M ↔ ∃ c : ι → v.adicCompletionIntegers F, x = ∑ i, (c i : Fv F v) • b i)
    (ϖ : Fv F v) (hϖ : IsUnif v ϖ) :
    (smulSub ϖ M).relIndex M = (Ideal.absNorm v.asIdeal) ^ (Fintype.card ι) := by
  classical
  let φ : (ι → v.adicCompletionIntegers F) →+ M :=
    { toFun := fun c => ⟨∑ i, (c i : Fv F v) • b i, (hmem _).2 ⟨c, rfl⟩⟩
      map_zero' := by ext1; simp
      map_add' := fun c d => by
        ext1
        simp [add_smul, Finset.sum_add_distrib] }
  have hφs : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨c, rfl⟩ := (hmem x).1 hx
    exact ⟨c, rfl⟩
  have hsm : ∀ d : ι → v.adicCompletionIntegers F,
      ϖ • ∑ i, (d i : Fv F v) • b i = ∑ i, (ϖ * d i) • b i := by
    intro d
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_smul _ _ _
  have key : ((smulSub ϖ M).addSubgroupOf M).comap φ =
      AddSubgroup.pi Set.univ (fun _ => unifO v ϖ) := by
    ext c
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_pi]
    constructor
    · intro hc i _
      obtain ⟨z, hz, hze⟩ := (mem_smulSub ϖ M _).1 hc
      obtain ⟨d, rfl⟩ := (hmem z).1 hz
      refine ⟨d i, ?_⟩
      have e : ∑ i, (c i : Fv F v) • b i = ∑ i, (ϖ * d i) • b i := by
        rw [← hsm, hze]
        rfl
      have h0 := Fintype.linearIndependent_iff.1 hb (fun i => (c i : Fv F v) - ϖ * d i)
        (by simp only [sub_smul, Finset.sum_sub_distrib, e, sub_self])
      exact sub_eq_zero.1 (h0 i)
    · intro h
      choose d hd using fun i => h i (Set.mem_univ i)
      refine (mem_smulSub ϖ M _).2 ⟨∑ i, (d i : Fv F v) • b i, (hmem _).2 ⟨d, rfl⟩, ?_⟩
      rw [hsm]
      show ∑ i, (ϖ * d i) • b i = ∑ i, (c i : Fv F v) • b i
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hd i]
  rw [AddSubgroup.relIndex, ← AddSubgroup.index_comap_of_surjective _ hφs, key, AddSubgroup.index_pi]
  simp only [resIdx_holds v ϖ hϖ, Finset.prod_const, Finset.card_univ]

theorem oEv_basis : ∃ β : Fin (Module.finrank F E) → Fv F v ⊗[F] E, LinearIndependent (Fv F v) β ∧
    ∀ x, x ∈ OEv (E := E) v ↔ ∃ c : Fin (Module.finrank F E) → v.adicCompletionIntegers F,
      x = ∑ i, (c i : Fv F v) • β i := by
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  set M := Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ) with hM
  have : Module.Finite (v.adicCompletionIntegers F) M := Module.Finite.iff_fg.2 (b_fg v)
  have : Module.IsTorsionFree (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) :=
    Module.IsTorsionFree.of_smul_eq_zero fun r x h => by
      have h' : (r : Fv F v) • x = 0 := h
      rcases smul_eq_zero.1 h' with h0 | h0
      · exact Or.inl (Subtype.ext h0)
      · exact Or.inr h0
  have : Module.Free (v.adicCompletionIntegers F) M := Module.free_of_finite_type_torsion_free'
  let bM := Module.finBasis (v.adicCompletionIntegers F) M
  let b0 : Fin (Module.finrank (v.adicCompletionIntegers F) M) → Fv F v ⊗[F] E := fun i => (bM i : _)
  have hli0 : LinearIndependent (v.adicCompletionIntegers F) b0 :=
    bM.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have hli : LinearIndependent (Fv F v) b0 :=
    (LinearIndependent.iff_fractionRing (v.adicCompletionIntegers F) (Fv F v)).1 hli0
  have hmem : ∀ x, x ∈ M ↔ ∃ c : Fin (Module.finrank (v.adicCompletionIntegers F) M) → v.adicCompletionIntegers F,
      x = ∑ i, (c i : Fv F v) • b0 i := by
    intro x
    constructor
    · intro hx
      refine ⟨fun i => bM.repr ⟨x, hx⟩ i, ?_⟩
      have h := congrArg Subtype.val (bM.sum_repr ⟨x, hx⟩)
      rw [Submodule.coe_sum] at h
      exact h.symm.trans (Finset.sum_congr rfl fun i _ => rfl)
    · rintro ⟨c, rfl⟩
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem M (c i) (bM i).2
  have hsp : ⊤ ≤ Submodule.span (Fv F v) (Set.range b0) := by
    have hM0 : ∀ x ∈ M, x ∈ Submodule.span (Fv F v) (Set.range b0) := by
      intro x hx
      obtain ⟨c, rfl⟩ := (hmem x).1 hx
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    intro x _
    induction x using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | tmul c e =>
      have hal : IsAlgebraic ℤ e := IsFractionRing.isAlgebraic_iff ℤ ℚ E |>.mpr (.of_finite ℚ e)
      obtain ⟨m, hm0, hI⟩ := hal.exists_integral_multiple
      have hmF : (m : Fv F v) ≠ 0 := by
        rw [← map_intCast (algebraMap F (Fv F v))]
        exact (map_ne_zero _).2 (Int.cast_ne_zero.2 hm0)
      have e2 : inclR (F := F) (Fv F v) (m • e) = (m : Fv F v) • inclR (F := F) (Fv F v) e := by
        rw [map_zsmul, Int.cast_smul_eq_zsmul]
      have e3 : c ⊗ₜ[F] e = c • inclR (F := F) (Fv F v) e := by
        simp [inclR, TensorProduct.smul_tmul']
      have e1 : c ⊗ₜ[F] e = (c * (m : Fv F v)⁻¹) • inclR (F := F) (Fv F v) ((⟨m • e, hI⟩ : 𝓞 E) : E) := by
        show _ = (c * (m : Fv F v)⁻¹) • inclR (F := F) (Fv F v) (m • e)
        rw [e2, smul_smul, mul_assoc, inv_mul_cancel₀ hmF, mul_one, e3]
      rw [e1]
      exact Submodule.smul_mem _ _ (hM0 _ (b_inclR_mem (F := F) (E := E) v ⟨m • e, hI⟩))
    | add x y hx hy => exact Submodule.add_mem _ (hx trivial) (hy trivial)
  have hrk : Module.finrank (v.adicCompletionIntegers F) M = Module.finrank F E := by
    have h1 := Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)
    rw [Fintype.card_fin] at h1
    rw [← h1, Module.finrank_baseChange]
  refine ⟨fun i => b0 (Fin.cast hrk.symm i), ?_, fun x => ?_⟩
  · exact hli.comp _ (Fin.cast_injective _)
  · rw [show x ∈ OEv (E := E) v ↔ x ∈ M from Iff.rfl, hmem]
    constructor
    · rintro ⟨c, rfl⟩
      refine ⟨fun i => c (Fin.cast hrk.symm i), ?_⟩
      exact (Fintype.sum_equiv (finCongr hrk) _ _ (fun i => rfl))
    · rintro ⟨c, rfl⟩
      refine ⟨fun i => c (Fin.cast hrk i), ?_⟩
      exact Fintype.sum_equiv (finCongr hrk.symm) _ _ (fun i => by simp)

end PI.OmLocU.SdB
end
end

module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Finiteness.Quotient
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Bialgebra.Basic
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open scoped TensorProduct

namespace GlobalTheory

theorem mem_span_eigen_of_baseChange_eigen (l : ℕ) [Fact l.Prime] (M S : Type) [AddCommGroup M]
    [Module ℤ_[l] M] (B : Submodule ℤ_[l] M) [Module.Free ℤ_[l] B]
    (g : S → Module.End ℤ_[l] M) (χ : S → ℤ_[l]) (hB : ∀ s, ∀ b ∈ B, g s b ∈ B)
    (x : PadicAlgCl l ⊗[ℤ_[l]] M)
    (hx : x ∈ LinearMap.range (LinearMap.baseChange (PadicAlgCl l) B.subtype))
    (he : ∀ s, LinearMap.baseChange (PadicAlgCl l) (g s) x
      = algebraMap ℤ_[l] (PadicAlgCl l) (χ s) • x) :
    x ∈ Submodule.span (PadicAlgCl l)
      {y | ∃ b ∈ B, (∀ s, g s b = χ s • b) ∧ y = (1 : PadicAlgCl l) ⊗ₜ[ℤ_[l]] b} := by
  classical
  obtain ⟨x', rfl⟩ := hx
  have hinj0 : Function.Injective (algebraMap ℤ_[l] (PadicAlgCl l)) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (PadicAlgCl l), RingHom.coe_comp]
    exact (algebraMap ℚ_[l] (PadicAlgCl l)).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])
  haveI : FaithfulSMul ℤ_[l] (PadicAlgCl l) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj0
  haveI : Module.IsTorsionFree ℤ_[l] (PadicAlgCl l) := inferInstance
  haveI : Module.Flat ℤ_[l] (PadicAlgCl l) := inferInstance
  obtain ⟨P, hP, z, rfl⟩ := Submodule.exists_fg_le_eq_rTensor_subtype x'
  haveI : Module.Finite ℤ_[l] P := Module.Finite.iff_fg.2 hP
  haveI : Module.Free ℤ_[l] P := inferInstance
  let ω := Module.Free.chooseBasis ℤ_[l] P
  let Φ : P ⊗[ℤ_[l]] B →ₗ[ℤ_[l]] PadicAlgCl l ⊗[ℤ_[l]] M :=
    (B.subtype.lTensor (PadicAlgCl l)) ∘ₗ (P.subtype.rTensor B)
  have hΦ : Function.Injective Φ :=
    (Module.Flat.lTensor_preserves_injective_linearMap _ B.injective_subtype).comp
      (Module.Flat.rTensor_preserves_injective_linearMap _ P.injective_subtype)
  have hΦz : ∀ w, LinearMap.baseChange (PadicAlgCl l) B.subtype (P.subtype.rTensor B w) = Φ w :=
    fun w => rfl
  have hΦt : ∀ (a : P) (b : B), Φ (a ⊗ₜ b) = (a : PadicAlgCl l) ⊗ₜ (b : M) := fun a b => rfl
  rw [hΦz] at he ⊢
  let h : S → Module.End ℤ_[l] B := fun s => (g s).restrict (hB s) - χ s • LinearMap.id
  have hcomm : ∀ s w, Φ ((h s).lTensor P w)
      = LinearMap.baseChange (PadicAlgCl l) (g s) (Φ w) - χ s • Φ w := by
    intro s w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [LinearMap.lTensor_tmul, hΦt, hΦt, LinearMap.baseChange_tmul, ← TensorProduct.tmul_smul,
        ← TensorProduct.tmul_sub]
      rfl
    | add u v hu hv => simp only [map_add (f := _), hu, hv, smul_add]; abel
  have hz : ∀ s, (h s).lTensor P z = 0 := by
    intro s
    apply hΦ
    rw [hcomm, he s, algebraMap_smul, sub_self, map_zero]
  obtain ⟨c, rfl⟩ := (TensorProduct.equivFinsuppOfBasisLeft (N := B) ω).symm.surjective z
  have hc : ∀ s i, h s (c i) = 0 := by
    intro s i
    have e : (h s).lTensor P ((TensorProduct.equivFinsuppOfBasisLeft (N := B) ω).symm c)
        = (TensorProduct.equivFinsuppOfBasisLeft (N := B) ω).symm
          (c.mapRange (h s) (map_zero _)) := by
      rw [TensorProduct.equivFinsuppOfBasisLeft_symm_apply,
        TensorProduct.equivFinsuppOfBasisLeft_symm_apply,
        Finsupp.sum_mapRange_index (fun _ => TensorProduct.tmul_zero _ _), map_finsuppSum]
      rfl
    have e2 := hz s
    rw [e, LinearEquiv.map_eq_zero_iff] at e2
    simpa using DFunLike.congr_fun e2 i
  rw [TensorProduct.equivFinsuppOfBasisLeft_symm_apply, map_finsuppSum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have e : Φ (ω i ⊗ₜ c i) = (ω i : PadicAlgCl l) • ((1 : PadicAlgCl l) ⊗ₜ[ℤ_[l]] (c i : M)) := by
    rw [hΦt, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  change Φ (ω i ⊗ₜ c i) ∈ _
  rw [e]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨c i, (c i).2, fun s => ?_, rfl⟩)
  have := congrArg Subtype.val (hc s i)
  exact sub_eq_zero.1 this

end GlobalTheory
end

section

namespace GlobalTheory

theorem exists_generator_valuation_prime_dvd_pow_sub_of_finite_padicInt :
  ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra ℤ_[p] Ω], Function.Injective (algebraMap ℤ_[p] Ω) →
  ∀ v : Valuation Ω NNReal, (∀ x : Ω, IsIntegral ℤ_[p] x → v x ≤ 1) → v (p : Ω) < 1 →
  ∀ R : Subalgebra ℤ_[p] Ω, Module.Finite ℤ_[p] R → IsPrincipalIdealRing R →
  ∃ π ∈ R, π ≠ 0 ∧ v π < 1 ∧ (p : Ω) / π ∈ R ∧ ∃ f : ℕ, 0 < f ∧ ∀ t ∈ R, (t ^ p ^ f - t) / π ∈ R := by
  intro p _ Ω _ _ hinj v hint hp R hfin hpid
  have hle : ∀ x : R, v (x : Ω) ≤ 1 := fun x => hint _ ((IsIntegral.of_finite ℤ_[p] x).map R.val)
  obtain ⟨P, hP⟩ : ∃ P : Ideal R, ∀ x, x ∈ P ↔ v (x : Ω) < 1 := by
    refine ⟨{ carrier := {x | v (x : Ω) < 1}, add_mem' := ?_, zero_mem' := ?_, smul_mem' := ?_ }, fun x => Iff.rfl⟩
    · intro a b ha hb
      simp only [Set.mem_setOf_eq, Subalgebra.coe_add] at *
      exact lt_of_le_of_lt (v.map_add _ _) (max_lt ha hb)
    · simp
    · intro c x hx
      simp only [Set.mem_setOf_eq, smul_eq_mul, Subalgebra.coe_mul, map_mul] at *
      calc v (c:Ω) * v x ≤ 1 * v x := mul_le_mul' (hle c) le_rfl
        _ = v x := one_mul _
        _ < 1 := hx
  have hpR : ((p : R) : Ω) = (p : Ω) := by simp
  have hpP : (p : R) ∈ P := by rw [hP, hpR]; exact hp
  have hp0 : (p : Ω) ≠ 0 := by
    intro h
    have h1 : algebraMap ℤ_[p] Ω (p : ℤ_[p]) = algebraMap ℤ_[p] Ω 0 := by simp [h]
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) (hinj h1)
  have hPprime : P.IsPrime := by
    refine ⟨?_, ?_⟩
    · intro h
      have h1 : (1 : R) ∈ P := h ▸ Submodule.mem_top
      rw [hP] at h1; simp at h1
    · intro x y hxy
      rw [hP, hP]; rw [hP] at hxy
      simp only [Subalgebra.coe_mul, map_mul] at hxy
      by_contra hc
      push_neg at hc
      have hx1 : v x = 1 := le_antisymm (hle x) hc.1
      have hy1 : v y = 1 := le_antisymm (hle y) hc.2
      rw [hx1, hy1, one_mul] at hxy
      exact lt_irrefl _ hxy
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hpP
    apply hp0; rw [← hpR, hpP]; rfl
  haveI hPmax : P.IsMaximal := hPprime.isMaximal hPne
  set g := Submodule.IsPrincipal.generator P with hgdef
  have hgmem : g ∈ P := Submodule.IsPrincipal.generator_mem P
  have hg0 : g ≠ 0 := by
    intro h; apply hPne
    exact (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero P).mpr h
  have hdvd : ∀ x : R, x ∈ P → ∃ c : R, x = g * c := fun x hx =>
    (Submodule.IsPrincipal.mem_iff_generator_dvd P).mp hx

  letI : Field (R ⧸ P) := Ideal.Quotient.field P
  have hpk : ((p : ℕ) : R ⧸ P) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem]; exact hpP
  have hchar : CharP (R ⧸ P) p := by
    rw [← ringChar.eq_iff]
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp (ringChar.dvd hpk) with h | h
    · exact absurd h CharP.ringChar_ne_one
    · exact h
  have hunder : P.under ℤ_[p] = IsLocalRing.maximalIdeal ℤ_[p] := by
    apply le_antisymm
    · apply IsLocalRing.le_maximalIdeal
      intro h
      apply hPprime.ne_top
      rw [Ideal.eq_top_iff_one] at h ⊢
      simpa [Ideal.mem_comap] using h
    · rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_le, Set.singleton_subset_iff]
      show (p : ℤ_[p]) ∈ P.comap (algebraMap ℤ_[p] R)
      rw [Ideal.mem_comap, map_natCast]; exact hpP
  haveI : Finite (ℤ_[p] ⧸ P.under ℤ_[p]) := by
    rw [hunder]
    exact Finite.of_equiv (ZMod p) (PadicInt.residueField (p := p)).symm.toEquiv
  haveI : Finite (R ⧸ P) := Module.finite_of_finite (ℤ_[p] ⧸ P.under ℤ_[p])
  letI := Fintype.ofFinite (R ⧸ P)
  obtain ⟨n, -, hcard⟩ := FiniteField.card (R ⧸ P) p
  refine ⟨(g : Ω), g.2, ?_, ?_, ?_, (n : ℕ), n.pos, ?_⟩
  · exact fun h => hg0 (Subtype.ext h)
  · exact (hP g).mp hgmem
  · obtain ⟨c, hc⟩ := hdvd _ hpP
    have : (p : Ω) = (g : Ω) * (c : Ω) := by rw [← hpR, hc]; rfl
    rw [this, mul_div_cancel_left₀ _ (fun h => hg0 (Subtype.ext h))]
    exact c.2
  · intro t ht
    have hmk : Ideal.Quotient.mk P (⟨t, ht⟩ ^ p ^ (n : ℕ)) = Ideal.Quotient.mk P ⟨t, ht⟩ := by
      rw [map_pow, ← hcard, FiniteField.pow_card]
    rw [Ideal.Quotient.eq] at hmk
    obtain ⟨c, hc⟩ := hdvd _ hmk
    have : t ^ p ^ (n : ℕ) - t = (g : Ω) * (c : Ω) := by
      have := congrArg (fun x : R => (x : Ω)) hc
      simpa using this
    rw [this, mul_div_cancel_left₀ _ (fun h => hg0 (Subtype.ext h))]
    exact c.2

end GlobalTheory
end

section

noncomputable section

namespace GlobalTheory

open TensorProduct

theorem isPrecomplete_of_finite {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] : IsPrecomplete I M := by
  rw [← AdicCompletion.of_surjective_iff]
  intro y
  obtain ⟨t, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite I M y
  induction t with
  | tmul a m =>
    obtain ⟨r, rfl⟩ := AdicCompletion.of_surjective I R a
    refine ⟨r • m, ?_⟩
    rw [AdicCompletion.ofTensorProduct_tmul, show AdicCompletion.of I R r =
      algebraMap R (AdicCompletion I R) r by simp [AdicCompletion.algebraMap_apply],
      algebraMap_smul, map_smul]
  | add x y hx hy =>
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hy
    exact ⟨u + v, by simp [hu, hv]⟩

theorem isAdicComplete_of_finite {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    [IsAdicComplete I R] (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    IsAdicComplete I M := by
  rw [isAdicComplete_iff]
  exact ⟨IsHausdorff.of_le_jacobson I M (IsAdicComplete.le_jacobson I), isPrecomplete_of_finite I M⟩

theorem isAdicComplete_map_of_finite {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    [IsAdicComplete I R] (S : Type*) [CommRing S] [Algebra R S] [Module.Finite R S] :
    IsAdicComplete (I.map (algebraMap R S)) S := by
  rw [IsAdicComplete.map_algebraMap_iff]
  exact isAdicComplete_of_finite I S

section Tower

variable {R : Type*} [CommRing R] (I : Ideal R)

end Tower

section Quotient

variable {R : Type*} [CommRing R] (I : Ideal R)

variable [IsNoetherianRing R] [IsAdicComplete I R] {A B : Type*} [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

end Quotient

section Tensor

variable {R : Type*} [CommRing R] (I : Ideal R)

variable [IsNoetherianRing R] [IsAdicComplete I R]

section

variable {A B : Type*} [Ring A] [Ring B] [Algebra R A] [Algebra R B]

end


section

variable {A B : Type*} [Ring A] [Ring B] [Bialgebra R A] [Bialgebra R B]

end

end Tensor

end GlobalTheory
end
end

section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField

namespace GlobalTheory.ContinuousValuationExtension

theorem continuous_of_valuation_eq {A B Γ : Type} [Field A] [Field B]
    [LinearOrderedCommGroupWithZero Γ] [Valued A Γ] [Valued B Γ] (g : A →+* B)
    (hs : Function.Surjective (Valued.v : A → Γ))
    (hg : ∀ x : A, (Valued.v (g x) : Γ) = Valued.v x) : Continuous g := by
  refine continuous_of_continuousAt_zero g ?_
  rw [ContinuousAt, map_zero,
    (Valued.hasBasis_nhds_zero A Γ).tendsto_iff (Valued.hasBasis_nhds_zero B Γ)]
  intro γ _

  obtain ⟨a, ha⟩ := hs (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)
  have ha0 : (Valued.v : Valuation A Γ).restrict a ≠ 0 := by
    rw [Ne, Valuation.restrict_eq_zero_iff, ha]
    intro h0
    apply γ.ne_zero
    apply MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.injective
    rw [h0, map_zero]
  refine ⟨Units.mk0 _ ha0, trivial, fun x hx => ?_⟩
  simp only [Set.mem_ofPred_eq, Units.val_mk0, Valuation.restrict_lt_iff, ha] at hx
  show (Valued.v : Valuation B Γ).restrict (g x) < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding, hg]
  exact hx

theorem valuation_eq_of_denseRange {A B Γ ι : Type} [Field A] [Field B]
    [LinearOrderedCommGroupWithZero Γ] [Valued A Γ] [Valued B Γ] (φ : A →+* B)
    (hφ : Continuous φ) (j : ι → A) (hj : DenseRange j)
    (h : ∀ x : ι, (Valued.v (φ (j x)) : Γ) = Valued.v (j x)) (y : A) :
    (Valued.v (φ y) : Γ) = Valued.v y := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have hφy : φ y ≠ 0 := (map_ne_zero φ).2 hy

  have h1 : {z : A | (Valued.v z : Γ) = Valued.v y} ∈ nhds y :=
    Valued.locally_const ((Valuation.ne_zero_iff _).2 hy)
  have h2 : {z : A | (Valued.v (φ z) : Γ) = Valued.v (φ y)} ∈ nhds y :=
    hφ.continuousAt.preimage_mem_nhds (Valued.locally_const ((Valuation.ne_zero_iff _).2 hφy))
  obtain ⟨_, ⟨x, rfl⟩, hx1, hx2⟩ := hj.inter_nhds_nonempty (Filter.inter_mem h1 h2)
  have e1 : (Valued.v (j x) : Γ) = Valued.v y := hx1
  have e2 : (Valued.v (φ (j x)) : Γ) = Valued.v (φ y) := hx2
  rw [← e2, h x, e1]

theorem exists_continuous_extension {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] (w : HeightOneSpectrum (RingOfIntegers K))
    (u : HeightOneSpectrum (RingOfIntegers L)) (f : K →+* adicCompletion L u)
    (hf : ∀ x : K, (Valued.v (f x) : WithZero (Multiplicative ℤ)) = valuation K w x) :
    ∃ φ : adicCompletion K w →+* adicCompletion L u, Continuous φ ∧
      (∀ x : K, φ (algebraMap K (adicCompletion K w) x) = f x) ∧
      ∀ y : adicCompletion K w,
        (Valued.v (φ y) : WithZero (Multiplicative ℤ)) = Valued.v y := by
  let g : WithVal (w.valuation K) →+* adicCompletion L u :=
    f.comp (WithVal.equiv (w.valuation K)).toRingHom
  have hgv : ∀ x : WithVal (w.valuation K),
      (Valued.v (g x) : WithZero (Multiplicative ℤ)) = Valued.v x := fun x => hf x.ofVal
  have hsurj : Function.Surjective
      (Valued.v : WithVal (w.valuation K) → WithZero (Multiplicative ℤ)) := fun γ => by
    obtain ⟨a, ha⟩ := w.valuation_surjective K γ
    exact ⟨WithVal.toVal _ a, ha⟩
  have hgc : Continuous g := continuous_of_valuation_eq g hsurj hgv

  let φ : adicCompletion K w →+* adicCompletion L u :=
    (UniformSpace.Completion.extensionHom g hgc).comp (adicCompletion.equiv K w).toRingHom
  have hφc : Continuous φ :=
    UniformSpace.Completion.continuous_extension.comp (adicCompletion.continuous_toCompletion K w)
  have hφf : ∀ x : K, φ (algebraMap K (adicCompletion K w) x) = f x := fun x =>
    UniformSpace.Completion.extensionHom_coe g hgc (WithVal.toVal _ x)
  refine ⟨φ, hφc, hφf, fun y => ?_⟩
  refine valuation_eq_of_denseRange φ hφc (algebraMap K (adicCompletion K w))
    (denseRange_algebraMap (K := K) (v := w)) (fun x => ?_) y
  rw [hφf x, hf x]
  exact (adicCompletion.valued_coe K w x).symm

end GlobalTheory.ContinuousValuationExtension
end

section

open Polynomial

namespace GlobalTheory

theorem jets_mem_subalgebra_of_finiteType : ∀ (k A R : Type) [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [CommRing R] [Algebra k R] (N : ℕ) (Δ : ℕ → A →ₗ[k] R), Δ 0 1 = 1 → (∀ l, ∀ u w : A, Δ l (u * w) = ∑ p ∈ Finset.range (l + 1), l.choose p • (Δ p u * Δ (l - p) w)) →
 ∃ T : Finset R, ∀ S : Subalgebra k R, (∀ t ∈ T, t ∈ S) → ∀ l < N, ∀ u, Δ l u ∈ S := by
  intro k A R _ _ _ _ _ _ N Δ _ hL
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := k) (A := A)
  refine ⟨(Finset.range N ×ˢ insert 1 s).image (fun x => Δ x.1 x.2), ?_⟩
  intro S hT l hl u
  have key : ∀ u ∈ Algebra.adjoin k (s : Set A), ∀ l < N, Δ l u ∈ S := by
    intro u hu
    induction hu using Algebra.adjoin_induction with
    | mem x hx =>
      intro l hl
      exact hT _ (Finset.mem_image.2 ⟨(l, x), by simp [hl, Finset.mem_coe.1 hx], rfl⟩)
    | algebraMap c =>
      intro l hl
      rw [Algebra.algebraMap_eq_smul_one, map_smul]
      exact S.smul_mem (hT _ (Finset.mem_image.2 ⟨(l, 1), by simp [hl], rfl⟩)) c
    | add x y _ _ hx hy =>
      intro l hl
      rw [map_add (f := _)]
      exact S.add_mem (hx l hl) (hy l hl)
    | mul x y _ _ hx hy =>
      intro l hl
      rw [hL]
      refine S.sum_mem (fun p hp => nsmul_mem (S.mul_mem (hx p ?_) (hy (l - p) ?_)) _)
      · have := Finset.mem_range.1 hp; omega
      · omega
  exact key u (hs ▸ Algebra.mem_top) l hl

end GlobalTheory
end

section

universe u_1 u_2

namespace GlobalTheory.exists_mem_pow_sub_mem_pow_succ_facts

theorem exists_mem_pow_sub_mem_pow_succ {A : Type u_1} [CommRing A] {B : Type u_2} [CommRing B]
    {φ : A →+* B} {I : Ideal A} {J : Ideal B} (hIJ : I ≤ Ideal.comap φ J)
    (h0 : ∀ b : B, ∃ a : A, φ a - b ∈ J)
    (h1 : ∀ y ∈ J, ∃ x ∈ I, φ x - y ∈ J ^ (2 : ℕ)) (n : ℕ) :
    ∀ y ∈ J ^ n, ∃ x ∈ I ^ n, φ x - y ∈ J ^ (n + (1 : ℕ)) := by
  induction n with
  | zero =>
    intro y _
    obtain ⟨a, ha⟩ := h0 y
    exact ⟨a, by simp, by simpa using ha⟩
  | succ n ih =>
    intro y hy
    rw [pow_succ] at hy
    refine Submodule.mul_induction_on hy (fun p hp q hq => ?_) (fun y1 y2 h1' h2' => ?_)
    · obtain ⟨xp, hxp, hp'⟩ := ih p hp
      obtain ⟨xq, hxq, hq'⟩ := h1 q hq
      refine ⟨xp * xq, by rw [pow_succ]; exact Ideal.mul_mem_mul hxp hxq, ?_⟩
      have e : φ (xp * xq) - p * q = (φ xp - p) * φ xq + p * (φ xq - q) := by
        rw [map_mul]
        ring
      rw [e]
      refine Ideal.add_mem _ ?_ ?_
      · rw [pow_succ]
        exact Ideal.mul_mem_mul hp' (Ideal.mem_comap.1 (hIJ hxq))
      · rw [show n + 1 + 1 = n + 2 from rfl, pow_add]
        exact Ideal.mul_mem_mul hp hq'
    · obtain ⟨x1, hx1, e1⟩ := h1'
      obtain ⟨x2, hx2, e2⟩ := h2'
      refine ⟨x1 + x2, Ideal.add_mem _ hx1 hx2, ?_⟩
      have e : φ (x1 + x2) - (y1 + y2) = (φ x1 - y1) + (φ x2 - y2) := by
        rw [map_add (f := _)]
        ring
      rw [e]
      exact Ideal.add_mem _ e1 e2

end GlobalTheory.exists_mem_pow_sub_mem_pow_succ_facts
end

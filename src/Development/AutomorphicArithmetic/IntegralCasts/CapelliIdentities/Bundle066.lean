module

public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.NoetherNormalization
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.Finiteness.Basic
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.Ideal.BigOperators

@[expose] public section

section

namespace UpperTheory.Reformulated.B.Uc13

open IsDedekindDomain NumberField
open scoped TensorProduct

@[reducible] noncomputable def Af (F : Type) [Field F] [NumberField F] : Type :=
  FiniteAdeleRing (RingOfIntegers F) F

@[reducible] noncomputable def Fv (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F)) : Type :=
  v.adicCompletion F

theorem aux3 (F : Type) [Field F] [NumberField F]
    (i : HeightOneSpectrum (RingOfIntegers F)) :
    SubringClass (ValuationSubring (Fv F i)) (Fv F i) :=
  inferInstance

theorem aux4 (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F)) (x : F) :
    RestrictedProduct.evalRingHom (fun w => Fv F w) v (algebraMap F (Af F) x) =
      RestrictedProduct.evalRingHom (fun w => Fv F w) v (algebraMap F (Af F) x) :=
  rfl

noncomputable def evalV (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F)) : Af F →ₐ[F] Fv F v where
  toRingHom := RestrictedProduct.evalRingHom (fun w => Fv F w) v
  commutes' := aux4 F v

noncomputable def intAf (F : Type) [Field F] [NumberField F] : Set (Af F) :=
  {a | ∀ (v : HeightOneSpectrum (RingOfIntegers F)), evalV F v a ∈ v.adicCompletionIntegers F}

noncomputable def intA (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] :
    AddSubgroup (TensorProduct F (Af F) E) :=
  AddSubgroup.closure {y | ∃ a ∈ intAf F, ∃ x : RingOfIntegers E, y = a ⊗ₜ[F] (x : E)}

theorem mul_mem_intA (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {x y : TensorProduct F (Af F) E}
    (hx : x ∈ intA F E) (hy : y ∈ intA F E) : x * y ∈ intA F E := by
  unfold intA at *
  induction hx, hy using AddSubgroup.closure_induction₂ with
  | mem x y hx hy =>
    obtain ⟨a, ha, s, rfl⟩ := hx
    obtain ⟨b, hb, t, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨a * b, ?_, s * t, ?_⟩
    · intro v
      rw [map_mul]
      exact mul_mem (ha v) (hb v)
    · rw [Algebra.TensorProduct.tmul_mul_tmul]
      rfl
  | zero_left x hx => rw [zero_mul]; exact zero_mem _
  | zero_right x hx => rw [mul_zero]; exact zero_mem _
  | add_left x y z hx hy hz h1 h2 => rw [add_mul]; exact add_mem h1 h2
  | add_right y z x hy hz hx h1 h2 => rw [mul_add]; exact add_mem h1 h2
  | neg_left x y hx hy h => rw [neg_mul]; exact neg_mem h
  | neg_right x y hx hy h => rw [mul_neg]; exact neg_mem h

end UpperTheory.Reformulated.B.Uc13
end

section

namespace UpperTheory

open nonZeroDivisors

private theorem finite_of_finite_over_normal (P A K : Type*) [CommRing P] [IsDomain P]
    [CharZero P] [IsIntegrallyClosed P] [IsNoetherianRing P] [CommRing A] [IsDomain A]
    [Algebra P A] [FaithfulSMul P A] [Module.Finite P A] [Field K] [Algebra A K]
    [IsFractionRing A K] : Module.Finite A (integralClosure A K) := by
  letI : Algebra P K := ((algebraMap A K).comp (algebraMap P A)).toAlgebra
  haveI : IsScalarTower P A K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FaithfulSMul P K := (faithfulSMul_iff_algebraMap_injective P K).mpr
    ((IsFractionRing.injective A K).comp (FaithfulSMul.algebraMap_injective P A))
  letI : Algebra (FractionRing P) K := FractionRing.liftAlgebra P K
  haveI : IsScalarTower P (FractionRing P) K := FractionRing.isScalarTower_liftAlgebra P K
  haveI : IsLocalization (Algebra.algebraMapSubmonoid A P⁰) K := inferInstance
  haveI : FiniteDimensional (FractionRing P) K := Module.Finite.of_isLocalization P A P⁰
  haveI : CharZero (FractionRing P) := IsFractionRing.charZero P
  haveI : Algebra.IsSeparable (FractionRing P) K := inferInstance
  haveI : IsIntegralClosure (integralClosure A K) P K :=
    ⟨Subtype.val_injective, fun {x} =>
      ⟨fun hx => ⟨⟨x, hx.tower_top⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ isIntegral_trans _ y.2⟩⟩
  haveI : Module.Finite P (integralClosure A K) :=
    IsIntegralClosure.finite P (FractionRing P) K (integralClosure A K)
  exact Module.Finite.of_restrictScalars_finite P A (integralClosure A K)

theorem integralClosure_finite (k A K : Type*) [Field k] [CharZero k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] [Field K] [Algebra A K] [IsFractionRing A K] :
    Module.Finite A (integralClosure A K) := by
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  letI : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
  haveI : Module.Finite (MvPolynomial (Fin s) k) A := hfin
  haveI : FaithfulSMul (MvPolynomial (Fin s) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  exact finite_of_finite_over_normal (MvPolynomial (Fin s) k) A K

end UpperTheory
end

section

theorem UpperTheory.Reformulated.B.Qh10.fin_of_hom :
    ∀ {S R M : Type} [inst : CommRing S] [inst_1 : CommRing R]
    [inst_2 : AddCommGroup M] [inst_3 : _root_.Module S M] [inst_4 : _root_.Module R M] [Module.Finite S M] (f : S → R),
    (∀ (a : S) (m : M), a • m = f a • m) → Module.Finite R M := by
  intro S R M _ _ _ _ _ hfin f hf
  obtain ⟨T, hT⟩ := hfin.fg_top
  refine ⟨⟨T, ?_⟩⟩
  rw [eq_top_iff]
  intro m hm0
  clear hm0
  have hm : m ∈ Submodule.span S (T : Set M) := by
    rw [hT]
    exact Submodule.mem_top
  induction hm using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [hf]
    exact Submodule.smul_mem _ _ hx
end

section

open TensorProduct in
theorem UpperTheory.Reformulated.B.Qf1.lam0 :
    ∀ (O B M : Type) [inst : CommRing O] [IsDomain O] [inst_2 : CommRing B] [inst_3 : Algebra O B]
    [inst_4 : AddCommGroup M] [inst_5 : _root_.Module B M] [Module.Finite B M] (x : B →ₐ[O] O),
    Module.annihilator B M ≤ RingHom.ker x →
      ∃ (lam : M →+ O) (m₀ : M),
        (∀ (a : B) (m : M), (lam : M → O) (a • m) = (x : B → O) a * (lam : M → O) m) ∧ (lam : M → O) m₀ ≠ (0 : O) := by
  intro O B M _ _ _ _ _ _ _ x hx
  classical
  set p : Ideal B := RingHom.ker x with hp
  haveI hpp : p.IsPrime := RingHom.ker_isPrime x
  have hs : (⟨p, hpp⟩ : PrimeSpectrum B) ∈ Module.support B M :=
    Module.mem_support_iff_of_finite.mpr hx
  have hnt : Nontrivial (p.ResidueField ⊗[B] M) :=
    (Module.mem_support_iff_nontrivial_residueField_tensorProduct (⟨p, hpp⟩ : PrimeSpectrum B)).mp hs
  obtain ⟨v, hv⟩ := exists_ne (0 : p.ResidueField ⊗[B] M)
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero p.ResidueField hv
  let g : M →ₗ[B] p.ResidueField :=
    (f.restrictScalars B) ∘ₗ (TensorProduct.mk B p.ResidueField M 1)
  have hg : ∃ m₀, g m₀ ≠ 0 := by
    by_contra h
    push Not at h
    apply hf
    have : ∀ w, f w = 0 := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simp [ha, hb]
      | tmul k m =>
        have h1 : k ⊗ₜ[B] m = k • ((1 : p.ResidueField) ⊗ₜ[B] m) := by
          simp [TensorProduct.smul_tmul']
        have h2 : f ((1 : p.ResidueField) ⊗ₜ[B] m) = 0 := h m
        rw [h1, map_smul, h2, smul_zero]
    exact this v
  obtain ⟨m₀, hm₀⟩ := hg
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := B) (M := M)
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (B ⧸ p)) S
    (fun m => g m)
  let i : (B ⧸ p) →ₗ[B] p.ResidueField := (IsScalarTower.toAlgHom B (B ⧸ p) p.ResidueField).toLinearMap
  have hi : Function.Injective i := IsFractionRing.injective (B ⧸ p) p.ResidueField
  let c : p.ResidueField := algebraMap (B ⧸ p) p.ResidueField b
  have hc : c ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  let g' : M →ₗ[B] p.ResidueField := c • g
  have hr : ∀ m, g' m ∈ LinearMap.range i := by
    intro m
    have hm : m ∈ Submodule.span B (S : Set M) := hS ▸ Submodule.mem_top
    have : Submodule.span B (S : Set M) ≤ (LinearMap.range i).comap g' := by
      rw [Submodule.span_le]
      intro y hy
      obtain ⟨z, hz⟩ := hb y hy
      refine ⟨z, ?_⟩
      change algebraMap _ _ z = c * g y
      rw [hz, Algebra.smul_def]
    exact this hm
  let h : M →ₗ[B] (B ⧸ p) := LinearMap.codRestrictOfInjective g' i hi hr
  have hh : ∀ m, i (h m) = g' m := fun m =>
    LinearMap.codRestrictOfInjective_comp_apply g' i hi hr m
  let e : (B ⧸ p) →+* O := RingHom.kerLift (x : B →+* O)
  have he : Function.Injective e := RingHom.kerLift_injective (x : B →+* O)
  refine ⟨e.toAddMonoidHom.comp h.toAddMonoidHom, m₀, ?_, ?_⟩
  · intro a m
    change e (h (a • m)) = x a * e (h m)
    rw [map_smul, Algebra.smul_def, map_mul]
    rfl
  · change e (h m₀) ≠ 0
    intro h0
    have h1 : h m₀ = 0 := he (by rw [h0, map_zero])
    have h2 := hh m₀
    rw [h1, map_zero] at h2
    exact mul_ne_zero hc hm₀ h2.symm
end

section

theorem UpperTheory.compact_quotient_submodule :
    ∀ {LL O W Q : Type} [Field LL] [CommRing O] [Algebra O LL] [AddCommGroup W] [Module LL W] [Module O W]
        [IsScalarTower O LL W] [TopologicalSpace LL] [TopologicalSpace W] [ContinuousSMul LL W]
        [IsTopologicalAddGroup W] [T2Space W] [AddCommGroup Q] [Module O Q] [Finite Q]
        (Z : Submodule O W) (p : O) (f : Z →ₗ[O] Q),
        IsCompact (Set.range (algebraMap O LL)) →
        (∀ U ∈ nhds (0 : W), ∃ n : ℕ, ∀ z ∈ Z, p ^ n • z ∈ U) →
        (∀ z : Z, f z = 0 → ∃ w ∈ Z, (z : W) = p • w) →
        Z.FG := by
  intro LL O W Q _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Z p f hK hsmall hker
  classical
  have := Fintype.ofFinite Q
  let s : Q → Z := Function.invFun f
  have hs : ∀ z : Z, f (s (f z)) = f z := fun z => Function.invFun_eq ⟨z, rfl⟩
  let v : Q → W := fun q => (s q : W)
  let N : Submodule O W := Submodule.span O (Set.range v)
  have hNZ : N ≤ Z := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨q, rfl⟩
    exact (s q).2
  have hstep : ∀ z ∈ Z, ∃ a ∈ N, ∃ w ∈ Z, z = a + p • w := by
    intro z hz
    obtain ⟨w, hw, e⟩ := hker (⟨z, hz⟩ - s (f ⟨z, hz⟩)) (by rw [map_sub, hs, sub_self])
    refine ⟨v (f ⟨z, hz⟩), Submodule.subset_span ⟨_, rfl⟩, w, hw, ?_⟩
    rw [← e]
    simp [v]
  have hiter : ∀ n : ℕ, ∀ z ∈ Z, ∃ a ∈ N, ∃ w ∈ Z, z = a + p ^ n • w := by
    intro n
    induction n with
    | zero => exact fun z hz => ⟨0, N.zero_mem, z, hz, by simp⟩
    | succ n ih =>
      intro z hz
      obtain ⟨a, ha, w, hw, e⟩ := ih z hz
      obtain ⟨b, hb, u, hu, e'⟩ := hstep w hw
      refine ⟨a + p ^ n • b, N.add_mem ha (N.smul_mem _ hb), u, hu, ?_⟩
      rw [e, e', smul_add, smul_smul, pow_succ, add_assoc]
  have hcomp : IsCompact (N : Set W) := by
    have hc : Continuous (fun c : Q → LL => ∑ q, c q • v q) := by fun_prop
    have h1 := (isCompact_univ_pi (fun _ : Q => hK)).image hc
    convert h1 using 1
    ext x
    simp only [SetLike.mem_coe, N, Submodule.mem_span_range_iff_exists_fun, Set.mem_image]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨fun q => algebraMap O LL (c q), fun q _ => ⟨c q, rfl⟩, by simp⟩
    · rintro ⟨c, hc, rfl⟩
      choose d hd using fun q => hc q (Set.mem_univ q)
      exact ⟨d, by simp [← hd]⟩
  have hZN : Z ≤ N := by
    intro z hz
    by_contra hzN
    have hopen : IsOpen ((fun x : W => z - x) ⁻¹' (N : Set W)ᶜ) :=
      hcomp.isClosed.isOpen_compl.preimage (by fun_prop)
    obtain ⟨n, hn⟩ := hsmall _ (hopen.mem_nhds (by simpa using hzN))
    obtain ⟨a, ha, w, hw, e⟩ := hiter n z hz
    apply hn w hw
    have : z - p ^ n • w = a := by rw [e]; simp
    simpa [this] using ha
  rw [le_antisymm hZN hNZ]
  exact Submodule.fg_span (Set.finite_range v)
end

section

theorem UpperTheory.Reformulated.B.SpanOfVariable.span_X :
    ∀ {O σ : Type} [inst : CommRing O] (I : Ideal (MvPowerSeries σ O))
    (s : Finset σ),
    (∀ i ∈ s, MvPowerSeries.X i ∈ I) →
      ∀ (f : MvPowerSeries σ O),
        (∀ (n : σ →₀ ℕ),
            (∀ i ∈ s, (n : σ → ℕ) i = (0 : ℕ)) → (MvPowerSeries.coeff n : MvPowerSeries σ O → O) f = (0 : O)) →
          f ∈ I := by
  intro O σ inst I s
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro _ f hf
    have h0 : f = 0 := by
      ext n
      rw [hf n (by simp), map_zero]
    rw [h0]
    exact I.zero_mem
  | insert a s ha ih =>
    intro hX f hf
    let g : MvPowerSeries σ O := fun n => if n a = 0 then MvPowerSeries.coeff n f else 0
    have hg : ∀ n : σ →₀ ℕ, MvPowerSeries.coeff n g =
        if n a = 0 then MvPowerSeries.coeff n f else 0 := fun n => rfl
    have hgI : g ∈ I := by
      refine ih (fun i hi => hX i (Finset.mem_insert_of_mem hi)) g ?_
      intro n hn
      rw [hg]
      split_ifs with h
      · refine hf n ?_
        intro i hi
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact h
        · exact hn i hi
      · rfl
    have hd : MvPowerSeries.X a ∣ f - g := by
      rw [MvPowerSeries.X_dvd_iff]
      intro n hn
      rw [map_sub, hg, if_pos hn, sub_self]
    have hfg : f - g ∈ I := I.mem_of_dvd hd (hX a (Finset.mem_insert_self a s))
    have := I.add_mem hfg hgI
    rwa [sub_add_cancel] at this
end

section

theorem UpperTheory.Reformulated.B.Yhd1.mem_minimalPrimes_iff.{u_1} :
    ∀ {A : Type u_1} [inst : CommRing A] [IsDomain A] [IsNoetherianRing A] {z : A},
      z ≠ (0 : A) → ∀ (W : Ideal A), W ∈ (Ideal.span {z}).minimalPrimes ↔ W.IsPrime ∧ W.height = (1 : ℕ∞) ∧ z ∈ W := by
  intro A _ _ _ z hz
  have key : ∀ P : Ideal A, P.IsPrime → z ∈ P → (1 : ℕ∞) ≤ P.height := by
    intro P hP hzP
    have hlt : (⊥ : Ideal A) < P := by
      refine bot_lt_iff_ne_bot.mpr fun h => hz ?_
      rw [h] at hzP
      exact Ideal.mem_bot.mp hzP
    have := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    exact le_trans le_add_self this
  intro W
  constructor
  · intro hW
    have hP : W.IsPrime := hW.1.1
    have hzW : z ∈ W := hW.1.2 (Ideal.mem_span_singleton_self z)
    exact ⟨hP, le_antisymm
      (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hW) (key W hP hzW), hzW⟩
  · rintro ⟨hP, hh, hzW⟩
    obtain ⟨P, hPm, hPW⟩ := Ideal.exists_minimalPrimes_le
      ((Ideal.span_singleton_le_iff_mem W).mpr hzW)
    have hP' : P.IsPrime := hPm.1.1
    have hzP : z ∈ P := hPm.1.2 (Ideal.mem_span_singleton_self z)
    rcases hPW.eq_or_lt with h | h
    · exact h ▸ hPm
    · exfalso
      have h1 := Ideal.height_add_one_le_of_lt_of_isPrime h
      have h2 : (1 : ℕ∞) + 1 ≤ 1 := by
        calc (1 : ℕ∞) + 1 ≤ P.height + 1 := by gcongr; exact key P hP' hzP
          _ ≤ W.height := h1
          _ = 1 := hh
      exact absurd h2 (by decide)
end

section

theorem UpperTheory.Reformulated.B.MemSpanVariable.mem_span_X :
    ∀ {O σ : Type} [inst : CommRing O] [Fintype σ]
    (f : MvPowerSeries σ O),
    (MvPowerSeries.constantCoeff : MvPowerSeries σ O → O) f = (0 : O) → f ∈ Ideal.span (Set.range MvPowerSeries.X) := by
  intro O σ _ _ f hf
  classical
  have hc : ∀ n : σ →₀ ℕ, ∃ o : Option σ, n ≠ 0 → ∃ i, o = some i ∧ n i ≠ 0 := by
    intro n
    by_cases h : n = 0
    · exact ⟨none, fun h' => absurd h h'⟩
    · obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp h
      exact ⟨some i, fun _ => ⟨i, rfl, hi⟩⟩
  choose c hc using hc
  let g : σ → MvPowerSeries σ O := fun i m =>
    if c (m + Finsupp.single i 1) = some i then
      MvPowerSeries.coeff (m + Finsupp.single i 1) f else 0
  have hg : ∀ i m, MvPowerSeries.coeff m (g i) =
      if c (m + Finsupp.single i 1) = some i then
        MvPowerSeries.coeff (m + Finsupp.single i 1) f else 0 := fun _ _ => rfl
  have key : ∀ (i : σ) (n : σ →₀ ℕ), MvPowerSeries.coeff n (MvPowerSeries.X i * g i) =
      if n i ≠ 0 ∧ c n = some i then MvPowerSeries.coeff n f else 0 := by
    intro i n
    rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul]
    by_cases h : n i = 0
    · have h' : ¬ Finsupp.single i 1 ≤ n := by
        rw [Finsupp.single_le_iff]; omega
      rw [if_neg h', if_neg (fun hh => hh.1 h)]
    · have h' : Finsupp.single i 1 ≤ n := by
        rw [Finsupp.single_le_iff]; omega
      rw [if_pos h', one_mul, hg, tsub_add_cancel_of_le h']
      simp [h]
  have hsum : f = ∑ i, MvPowerSeries.X i * g i := by
    ext n

    rw [map_sum]
    simp only [key]
    by_cases h : n = 0
    · subst h
      simpa using hf
    · obtain ⟨i, hi, hn⟩ := hc n h
      rw [Finset.sum_eq_single i]
      · rw [if_pos ⟨hn, hi⟩]
      · intro j _ hj
        rw [if_neg]
        rintro ⟨_, h2⟩
        exact hj (Option.some.inj (h2.symm.trans hi))
      · intro h2
        exact absurd (Finset.mem_univ i) h2
  rw [hsum]
  exact Ideal.sum_mem _ fun i _ =>
    Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)
end

section

theorem UpperTheory.Reformulated.B.Qk57.eval₂_scale.{u_1, u_2} :
    ∀ {A : Type u_1} {S : Type u_2} [inst : CommRing A] [inst_1 : CommRing S] {n : ℕ} (g : A →+* S) (x : Fin n → S)
    (w : S) {m : ℕ} {a : MvPolynomial (Fin n) A},
    a.IsHomogeneous m → MvPolynomial.eval₂ g (fun (l : Fin n) ↦ w * x l) a = w ^ m * MvPolynomial.eval₂ g x a := by
  intro A S _ _ n g x w m a h
  rw [MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i, d i = m := by
    have h1 := h (MvPolynomial.mem_support_iff.mp hd)
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h1
    simpa using h1
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring
end

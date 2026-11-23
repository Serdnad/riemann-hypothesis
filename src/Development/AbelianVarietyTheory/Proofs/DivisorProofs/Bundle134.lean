module

public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.LaurentSeries
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Polynomial.Tower
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MvPolynomial

namespace GlobalTheory

theorem trace_monic_over_mvPolynomial {K : Type} [Field K] (F : Subfield K) [FiniteDimensional F K]
    {ι : Type} (z : ι → K) (hz : ∀ i, z i ∈ F) (v : K)
    (hv : IsIntegral (Subring.closure (Set.range z)) v) :
    ∃ f : Polynomial (MvPolynomial ι ℤ), f.Monic ∧
      f.eval₂ (aeval z).toRingHom (Algebra.trace F K v : K) = 0 := by
  set φ : MvPolynomial ι ℤ →+* K := (aeval z).toRingHom with hφdef
  set S : Subring K := Subring.closure (Set.range z) with hSdef
  have hφF : ∀ p, φ p ∈ F := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => simpa [hφdef] using F.intCast_mem a
    | add p q hp hq => simpa [map_add (f := _)] using F.add_mem hp hq
    | mul_X p i hp => simpa [map_mul, hφdef] using F.mul_mem hp (hz i)
  have hφS : ∀ p, φ p ∈ S := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => simpa [hφdef] using S.intCast_mem a
    | add p q hp hq => simpa [map_add (f := _)] using S.add_mem hp hq
    | mul_X p i hp =>
        simpa [map_mul, hφdef] using S.mul_mem hp (Subring.subset_closure ⟨i, rfl⟩)
  let ψ : MvPolynomial ι ℤ →+* F := φ.codRestrict F hφF
  let θ : MvPolynomial ι ℤ →+* S := φ.codRestrict S hφS
  letI : Algebra (MvPolynomial ι ℤ) K := φ.toAlgebra
  letI : Algebra (MvPolynomial ι ℤ) F := ψ.toAlgebra
  letI : Algebra (MvPolynomial ι ℤ) S := θ.toAlgebra
  haveI : IsScalarTower (MvPolynomial ι ℤ) F K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower (MvPolynomial ι ℤ) S K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hθsurj : Function.Surjective θ := by
    rintro ⟨s, hs⟩
    have hle : S ≤ φ.range := by
      rw [hSdef, Subring.closure_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨X i, by simp [hφdef]⟩
    obtain ⟨p, hp⟩ := hle hs
    exact ⟨p, Subtype.ext hp⟩
  haveI : Algebra.IsIntegral (MvPolynomial ι ℤ) S :=
    Algebra.IsIntegral.of_surjective (Algebra.ofId _ _) hθsurj
  have hvP : IsIntegral (MvPolynomial ι ℤ) v := isIntegral_trans v hv
  have hT : IsIntegral (MvPolynomial ι ℤ) (Algebra.trace F K v) := Algebra.isIntegral_trace hvP
  obtain ⟨f, hfm, hf⟩ := hT
  refine ⟨f, hfm, ?_⟩
  have h := congrArg F.subtype hf
  rw [Polynomial.hom_eval₂, map_zero] at h
  exact h

end GlobalTheory
end

section

open scoped TensorProduct Polynomial

namespace GlobalTheory

theorem kaehler_baseChange_independent_extend :
    ∀ (R B K : Type) [CommRing R] [CommRing B] [Field K] [Algebra R B] [Algebra B K]
      [Algebra.FiniteType R B] (d : ℕ) (ι : Type) (x : ι → B),
      Module.finrank K (K ⊗[B] Ω[B⁄R]) = d →
      LinearIndependent K (fun i => (1 : K) ⊗ₜ[B] KaehlerDifferential.D R B (x i)) →
      ∃ (t : Fin d → B) (e : ι ↪ Fin d), (∀ i, t (e i) = x i) ∧
        LinearIndependent K (fun a => (1 : K) ⊗ₜ[B] KaehlerDifferential.D R B (t a)) := by
  intro R B K _ _ _ _ _ _ d ι x hd hx
  set g : B → K ⊗[B] Ω[B⁄R] := fun b => (1 : K) ⊗ₜ[B] KaehlerDifferential.D R B b with hg
  have hspan : Submodule.span K (Set.range g) = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    induction z using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | tmul k ω =>
      have h1 : (1 : K) ⊗ₜ[B] ω ∈ Submodule.span K (Set.range g) := by
        have hω : ω ∈ Submodule.span B (Set.range (KaehlerDifferential.D R B)) := by
          rw [KaehlerDifferential.span_range_derivation]; trivial
        induction hω using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨b, rfl⟩ := hy
          exact Submodule.subset_span ⟨b, rfl⟩
        | zero => simp
        | add y z _ _ hy hz => rw [TensorProduct.tmul_add]; exact add_mem hy hz
        | smul c y _ hy =>
          rw [TensorProduct.tmul_smul, ← algebraMap_smul K c]
          exact Submodule.smul_mem _ _ hy
      have : k ⊗ₜ[B] ω = k • ((1 : K) ⊗ₜ[B] ω) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this]
      exact Submodule.smul_mem _ _ h1
    | add a b ha hb => exact add_mem ha hb
  have hxinj : Function.Injective x := fun i j h => hx.injective (by simp [h])
  have hs : LinearIndepOn K g (Set.range x) := (linearIndepOn_range_iff hxinj g).2 hx
  obtain ⟨b, -, hsb, htb, hli⟩ := exists_linearIndepOn_extension hs (Set.subset_univ _)
  have hspanb : ⊤ ≤ Submodule.span K (Set.range (fun y : b => g y)) := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    have := htb ⟨c, Set.mem_univ _, rfl⟩
    rwa [Set.image_eq_range] at this
  let bas := Module.Basis.mk hli hspanb
  haveI : Finite b := Module.Finite.finite_basis bas
  have hcard : Nat.card b = d := by
    rw [← hd, Module.finrank_eq_nat_card_basis bas]
  let eq : b ≃ Fin d := Finite.equivFinOfCardEq hcard
  refine ⟨fun a => (eq.symm a).1, ⟨fun i => eq ⟨x i, hsb ⟨i, rfl⟩⟩, ?_⟩, ?_, ?_⟩
  · intro i j h
    have := eq.injective h
    exact hxinj (congrArg Subtype.val this)
  · intro i
    show ((eq.symm (eq ⟨x i, hsb ⟨i, rfl⟩⟩)) : B) = x i
    rw [Equiv.symm_apply_apply]
  · exact hli.comp eq.symm eq.symm.injective

end GlobalTheory
end

section

open IsLocalRing

namespace GlobalTheory

theorem exists_prime_ne_maximalIdeal_of_one_le_ringKrullDim_quot
    (R : Type) [CommRing R] [IsLocalRing R] (f : R)
    (hdim : 1 ≤ ringKrullDim (R ⧸ Ideal.span {f})) :
    ∃ P : Ideal R, P.IsPrime ∧ f ∈ P ∧ P ≠ maximalIdeal R := by
  by_contra! hne
  have h0 : Ring.KrullDimLE 0 (R ⧸ Ideal.span {f}) := by
    refine Ring.krullDimLE_zero_iff.mpr fun Q hQ => ?_
    have hc : Q.comap (Ideal.Quotient.mk (Ideal.span {f})) = maximalIdeal R := by
      refine hne _ (Ideal.comap_isPrime _ _) ?_
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self f)]
      exact Q.zero_mem
    have hmax := (maximalIdeal.isMaximal R).map_of_surjective_of_ker_le
      (f := Ideal.Quotient.mk (Ideal.span {f})) Ideal.Quotient.mk_surjective
      (by rw [← hc]; exact Ideal.comap_mono bot_le)
    rwa [← hc, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at hmax
  have := (Ring.krullDimLE_iff (n := 0)).mp h0
  have h10 := hdim.trans this
  norm_num at h10

theorem cokernel_torsion_of_finiteLength_mod : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (f : R), 1 ≤ ringKrullDim (R ⧸ Ideal.span {f}) → ∀ (A B : Type) [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] [Module.Finite R B] (ψ : A →ₐ[R] B), (∃ k : ℕ, ∀ x ∈ maximalIdeal R ^ k, ∀ b : B, ∃ a : A, ∃ c : B, x • b = ψ a + f • c) → ∃ s : R, s ≠ 0 ∧ ∀ b : B, s • b ∈ ψ.range := by
  intro R _ _ _ f hdim A B _ _ _ _ _ ψ ⟨k, hk⟩
  obtain ⟨P, hP, hfP, hPm⟩ := exists_prime_ne_maximalIdeal_of_one_le_ringKrullDim_quot R f hdim

  obtain ⟨x, hxk, hxP⟩ : ∃ x ∈ maximalIdeal R ^ k, x ∉ P := by
    by_contra! h
    have hle : maximalIdeal R ≤ P := hP.le_of_pow_le h
    exact hPm (le_antisymm (le_maximalIdeal hP.ne_top) hle)
  set N : Submodule R B := LinearMap.range ψ.toLinearMap
  set I : Ideal R := Ideal.span {f}
  let φ : Module.End R (B ⧸ N) := algebraMap R (Module.End R (B ⧸ N)) x
  have hφ : LinearMap.range φ ≤ I • ⊤ := by
    rintro _ ⟨c, rfl⟩
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective N c
    obtain ⟨a, c', hac⟩ := hk x hxk b
    have : φ (Submodule.Quotient.mk b) = f • Submodule.Quotient.mk c' := by
      simp only [φ, Module.algebraMap_end_apply, ← Submodule.Quotient.mk_smul, hac]
      have ha0 : Submodule.Quotient.mk (p := N) (ψ a) = 0 := (Submodule.Quotient.mk_eq_zero N).mpr ⟨a, rfl⟩
      rw [Submodule.Quotient.mk_add, ha0, zero_add]
    rw [this]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self f) Submodule.mem_top
  obtain ⟨p, hmon, -, hcoeff, hzero⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero R φ I hφ
  refine ⟨p.eval x, ?_, ?_⟩
  · intro h0
    apply hxP
    apply hP.mem_of_pow_mem p.natDegree
    have hs : p.eval x ∈ P := h0 ▸ P.zero_mem
    rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ, hmon.coeff_natDegree, one_mul] at hs
    refine (P.add_mem_iff_right ?_).mp hs
    refine P.sum_mem fun i hi => P.mul_mem_right _ ?_
    have hi' : 0 < p.natDegree - i := Nat.sub_pos_of_lt (Finset.mem_range.mp hi)
    have hIP : I ≤ P := (Ideal.span_singleton_le_iff_mem P).mpr hfP
    exact hIP (Ideal.pow_le_self hi'.ne' (hcoeff i))
  · intro b
    have h1 : (Polynomial.aeval φ p) (Submodule.Quotient.mk b) = 0 := by rw [hzero]; rfl
    rw [show φ = algebraMap R _ x from rfl, Polynomial.aeval_algebraMap_apply,
      Module.algebraMap_end_apply, Polynomial.aeval_def] at h1
    change Polynomial.eval x p • Submodule.Quotient.mk (p := N) b = 0 at h1
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h1
    obtain ⟨a, ha⟩ := h1
    exact ⟨a, ha⟩

end GlobalTheory
end

section

open PowerSeries

namespace GlobalTheory.LaurentFlagBasis

variable {F : Type} [Field F]

noncomputable def red {n : ℕ} (y : Fin n → PowerSeries F) : Fin n → F := fun a => constantCoeff (y a)

noncomputable def lift {n : ℕ} (y : Fin n → PowerSeries F) : Fin n → LaurentSeries F :=
  fun a => (y a : LaurentSeries F)

lemma exists_primitive {n : ℕ} (u : Fin n → LaurentSeries F) (hu : u ≠ 0) :
    ∃ (i : Fin n) (y : Fin n → PowerSeries F), lift y = (u i)⁻¹ • u ∧ y i = 1 := by
  obtain ⟨l, hl⟩ : ∃ l, u l ≠ 0 := by
    by_contra h; push Not at h; exact hu (funext h)
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun a => Valued.v (u a))
    ⟨l, Finset.mem_univ _⟩
  have hvl : Valued.v (u l) ≠ 0 := (Valuation.ne_zero_iff _).mpr hl
  have hvi : 0 < Valued.v (u i) := by
    have := hi l (Finset.mem_univ _)
    exact lt_of_lt_of_le (zero_lt_iff.mpr hvl) this
  have hui : u i ≠ 0 := (Valuation.ne_zero_iff _).mp hvi.ne'
  have key : ∀ a, ∃ P : PowerSeries F, (P : LaurentSeries F) = (u i)⁻¹ * u a := by
    intro a
    have := (LaurentSeries.val_le_one_iff_eq_coe F ((u i)⁻¹ * u a)).mp (by
      rw [map_mul, map_inv₀, inv_mul_le_one₀ hvi]
      exact hi a (Finset.mem_univ _))
    exact this
  choose y hy using key
  refine ⟨i, y, funext fun a => ?_, ?_⟩
  · simp [lift, hy]
  · apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    rw [hy, inv_mul_cancel₀ hui, map_one]

lemma exists_indep {n : ℕ} : ∀ (d : ℕ) (U : Submodule (LaurentSeries F) (Fin n → LaurentSeries F)),
    d ≤ Module.finrank (LaurentSeries F) U →
    ∃ y : Fin d → (Fin n → PowerSeries F), (∀ b, lift (y b) ∈ U) ∧
      LinearIndependent F (fun b => red (y b)) := by
  intro d
  induction d with
  | zero =>
    intro U _
    exact ⟨Fin.elim0, fun b => b.elim0, linearIndependent_empty_type⟩
  | succ d ih =>
    intro U hd
    have hU : U ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hd
      omega
    obtain ⟨u, huU, hu0⟩ : ∃ u : Fin n → LaurentSeries F, u ∈ U ∧ u ≠ 0 :=
      Submodule.exists_mem_ne_zero_of_ne_bot hU
    obtain ⟨i, y0, hy0, hy0i⟩ := exists_primitive u hu0
    let f : U →ₗ[LaurentSeries F] LaurentSeries F := (LinearMap.proj i).comp U.subtype
    let U' : Submodule (LaurentSeries F) (Fin n → LaurentSeries F) := (LinearMap.ker f).map U.subtype
    have hU' : d ≤ Module.finrank (LaurentSeries F) U' := by
      have h1 := LinearMap.finrank_range_add_finrank_ker f
      have h2 : Module.finrank (LaurentSeries F) (LinearMap.range f) ≤ 1 := by
        simpa using Submodule.finrank_le (LinearMap.range f)
      have h3 : Module.finrank (LaurentSeries F) U' =
          Module.finrank (LaurentSeries F) (LinearMap.ker f) :=
        (Submodule.equivMapOfInjective _ U.injective_subtype _).finrank_eq.symm
      omega
    obtain ⟨y, hyU, hyi⟩ := ih U' hU'
    refine ⟨Fin.cons y0 y, ?_, ?_⟩
    · intro b
      refine Fin.cases ?_ (fun b => ?_) b
      · simp only [Fin.cons_zero]; rw [hy0]; exact U.smul_mem _ huU
      · simp only [Fin.cons_succ]
        obtain ⟨z, -, hz⟩ := Submodule.mem_map.mp (hyU b)
        rw [← hz]; exact z.2
    · have e : (fun b => red ((Fin.cons y0 y : Fin (d+1) → Fin n → PowerSeries F) b)) =
          Fin.cons (red y0) (fun b => red (y b)) := by
        ext b; refine Fin.cases ?_ (fun b => ?_) b <;> simp
      rw [e, linearIndependent_finCons]
      refine ⟨hyi, fun hmem => ?_⟩
      have hsub : Submodule.span F (Set.range fun b => red (y b)) ≤
          LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : Fin n => F) i) := by
        rw [Submodule.span_le]
        rintro _ ⟨b, rfl⟩
        obtain ⟨z, hz, hzz⟩ := Submodule.mem_map.mp (hyU b)
        have hz0 : (z : Fin n → LaurentSeries F) i = 0 := hz
        have h0 : ((y b i : PowerSeries F) : LaurentSeries F) = 0 := by
          have := congrFun hzz i
          simp only [Submodule.subtype_apply] at this
          rw [← hz0, this]; rfl
        have h00 : y b i = 0 := by
          apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
          rw [map_zero]; exact h0
        simp [red, h00]
      have := hsub hmem
      simp [red, hy0i] at this

lemma greedy {n : ℕ} (V : ℕ → Submodule (LaurentSeries F) (Fin n → LaurentSeries F))
    (hV : ∀ j, j < n → j < Module.finrank (LaurentSeries F) (V j)) :
    ∀ m, m ≤ n → ∃ c : Fin m → (Fin n → PowerSeries F), (∀ j : Fin m, lift (c j) ∈ V j) ∧
      LinearIndependent F (fun j => red (c j)) := by
  intro m
  induction m with
  | zero =>
    intro _
    exact ⟨Fin.elim0, fun j => j.elim0, linearIndependent_empty_type⟩
  | succ m ih =>
    intro hm
    obtain ⟨c, hcV, hci⟩ := ih (Nat.le_of_succ_le hm)
    obtain ⟨y, hyV, hyi⟩ := exists_indep (Module.finrank (LaurentSeries F) (V m)) (V m) le_rfl
    have : ∃ b, red (y b) ∉ Submodule.span F (Set.range fun j => red (c j)) := by
      by_contra h; push Not at h
      have h1 : Submodule.span F (Set.range fun b => red (y b)) ≤
          Submodule.span F (Set.range fun j => red (c j)) :=
        Submodule.span_le.mpr (by rintro _ ⟨b, rfl⟩; exact h b)
      have h2 := Submodule.finrank_mono h1
      rw [finrank_span_eq_card hyi, finrank_span_eq_card hci] at h2
      simp at h2
      have := hV m (by omega)
      omega
    obtain ⟨b, hb⟩ := this
    refine ⟨Fin.snoc (α := fun _ => Fin n → PowerSeries F) c (y b), ?_, ?_⟩
    · intro j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simp only [Fin.snoc_last, Fin.val_last]; exact hyV b
      · simp only [Fin.snoc_castSucc, Fin.val_castSucc]; exact hcV j
    · have e : (fun j => red ((Fin.snoc (α := fun _ => Fin n → PowerSeries F) c (y b)) j)) =
          Fin.snoc (α := fun _ => Fin n → F) (fun j => red (c j)) (red (y b)) := by
        ext j; refine Fin.lastCases ?_ (fun j => ?_) j <;> simp
      rw [e, linearIndependent_finSnoc]
      exact ⟨hci, hb⟩

end GlobalTheory.LaurentFlagBasis


open GlobalTheory.LaurentFlagBasis in
theorem GlobalTheory.LaurentFlagBasis.adapted_integral_basis : ∀ (F : Type) [Field F] (n R : ℕ)
    (W : Fin (R + 1) → Submodule (LaurentSeries F) (Fin n → LaurentSeries F)), Monotone W →
    ∃ g : (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ, ∀ (k : Fin (R + 1)) (j : Fin n),
      (j : ℕ) < Module.finrank (LaurentSeries F) (W k) →
      (fun a => (((g : Matrix (Fin n) (Fin n) (PowerSeries F)) a j : PowerSeries F) :
        LaurentSeries F)) ∈ W k := by
  intro F _ n R W hW
  let V : ℕ → Submodule (LaurentSeries F) (Fin n → LaurentSeries F) := fun j =>
    ⨅ (k : Fin (R + 1)) (_ : j < Module.finrank (LaurentSeries F) (W k)), W k
  have hV : ∀ j, j < n → j < Module.finrank (LaurentSeries F) (V j) := by
    intro j hj
    by_cases h : ∃ k, j < Module.finrank (LaurentSeries F) (W k)
    · obtain ⟨k, hk⟩ := h
      obtain ⟨k0, hk0, hmin⟩ := Finset.exists_min_image
        (Finset.univ.filter fun k => j < Module.finrank (LaurentSeries F) (W k)) id
        ⟨k, by simp [hk]⟩
      have hle : W k0 ≤ V j := le_iInf₂ fun k hk => hW (hmin k (by simp [hk]))
      have := Submodule.finrank_mono hle
      simp at hk0
      omega
    · push Not at h
      have hle : ⊤ ≤ V j := le_iInf₂ fun k hk => absurd hk (not_lt.mpr (h k))
      have := Submodule.finrank_mono hle
      rw [finrank_top, Module.finrank_fin_fun] at this
      omega
  obtain ⟨c, hcV, hci⟩ := greedy V hV n le_rfl
  let g : Matrix (Fin n) (Fin n) (PowerSeries F) := Matrix.of fun a j => c j a
  have hunit : IsUnit g := by
    rw [Matrix.isUnit_iff_isUnit_det, PowerSeries.isUnit_iff_constantCoeff, RingHom.map_det,
      ← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_col_iff_isUnit]
    convert hci using 1
    funext j a
    simp [g, red, Matrix.col]
  refine ⟨hunit.unit, fun k j hj => ?_⟩
  have hmem := hcV j
  have hVk : V j ≤ W k := iInf₂_le k hj
  exact hVk hmem
end

section

open PowerSeries

namespace GlobalTheory

theorem diagonal_entry_of_semilinear_mod_subspace : ∀ (F : Type) [Field F] (n : ℕ) (θ : PowerSeries F →+* PowerSeries F) (A : Matrix (Fin n) (Fin n) (PowerSeries F)) (W' W : Submodule (LaurentSeries F) (Fin n → LaurentSeries F)) (f' e' f e : Fin n → PowerSeries F) (w' w : (PowerSeries F)ˣ) (k' k m : ℤ) (d : PowerSeries F) (α : LaurentSeries F), ((θ PowerSeries.X : PowerSeries F) : LaurentSeries F) ≠ 0 → (∀ y : Fin n → PowerSeries F, (fun a => ((y a : PowerSeries F) : LaurentSeries F)) ∈ W' → (fun a => ((A.mulVec (fun c => θ (y c)) a : PowerSeries F) : LaurentSeries F)) ∈ W) → (fun a => ((f' a : PowerSeries F) : LaurentSeries F)) - (((w' : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ k') • (fun a => ((e' a : PowerSeries F) : LaurentSeries F)) ∈ W' → (fun a => ((f a : PowerSeries F) : LaurentSeries F)) - (((w : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ k) • (fun a => ((e a : PowerSeries F) : LaurentSeries F)) ∈ W → (fun a => ((e a : PowerSeries F) : LaurentSeries F)) ∉ W → (fun a => ((A.mulVec (fun c => θ (f' c)) a : PowerSeries F) : LaurentSeries F)) - ((d : PowerSeries F) : LaurentSeries F) • (fun a => ((f a : PowerSeries F) : LaurentSeries F)) ∈ W → (((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ m) • (fun a => ((A.mulVec (fun c => θ (e' c)) a : PowerSeries F) : LaurentSeries F)) - α • (fun a => ((e a : PowerSeries F) : LaurentSeries F)) ∈ W → ((θ (w' : PowerSeries F) : PowerSeries F) : LaurentSeries F) * ((θ PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ k' * α = ((d : PowerSeries F) : LaurentSeries F) * ((w : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ k * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ m := by
  intro F _ n θ A W' W f' e' f e w' w k' k m d α hξ hT hf' hf he hTf hTe
  have hx : ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ≠ 0 := by
    intro h
    apply PowerSeries.X_ne_zero (R := F)
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    simpa using h
  set x : LaurentSeries F := ((PowerSeries.X : PowerSeries F) : LaurentSeries F) with hxdef
  set ξ : LaurentSeries F := ((θ PowerSeries.X : PowerSeries F) : LaurentSeries F) with hξdef
  obtain ⟨N, j, hj⟩ : ∃ N j : ℕ, (j : ℤ) = (N : ℤ) + k' := ⟨k'.natAbs, (k'.natAbs + k').toNat, by omega⟩
  set a : PowerSeries F := (w' : PowerSeries F) * PowerSeries.X ^ j with hadef
  have ha : ((a : PowerSeries F) : LaurentSeries F) = (w' : LaurentSeries F) * x ^ N * x ^ k' := by
    rw [hadef, PowerSeries.coe_mul, PowerSeries.coe_pow, ← zpow_natCast, hj, zpow_add₀ hx, zpow_natCast, mul_assoc]
  have hθa : ((θ a : PowerSeries F) : LaurentSeries F) = ((θ (w' : PowerSeries F) : PowerSeries F) : LaurentSeries F) * ξ ^ N * ξ ^ k' := by
    rw [hadef, map_mul, map_pow, PowerSeries.coe_mul, PowerSeries.coe_pow, ← zpow_natCast, hj, zpow_add₀ hξ, zpow_natCast, mul_assoc]
  let y : Fin n → PowerSeries F := fun c => PowerSeries.X ^ N * f' c - a * e' c
  have hy : (fun c => ((y c : PowerSeries F) : LaurentSeries F)) ∈ W' := by
    have : (fun c => ((y c : PowerSeries F) : LaurentSeries F)) = (x ^ N) • ((fun a => ((f' a : PowerSeries F) : LaurentSeries F)) - (((w' : PowerSeries F) : LaurentSeries F) * x ^ k') • (fun a => ((e' a : PowerSeries F) : LaurentSeries F))) := by
      funext c
      simp only [y, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, PowerSeries.coe_sub, PowerSeries.coe_mul, PowerSeries.coe_pow, ha, ← hxdef]
      ring
    rw [this]; exact W'.smul_mem _ hf'
  have hvec : A.mulVec (fun c => θ (y c)) = (θ PowerSeries.X) ^ N • A.mulVec (fun c => θ (f' c)) - θ a • A.mulVec (fun c => θ (e' c)) := by
    have : (fun c => θ (y c)) = (θ PowerSeries.X) ^ N • (fun c => θ (f' c)) - θ a • (fun c => θ (e' c)) := by
      ext c; simp [y]
    rw [this, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul]
  have hTy := hT y hy
  set P : Fin n → LaurentSeries F := fun i => ((A.mulVec (fun c => θ (f' c)) i : PowerSeries F) : LaurentSeries F) with hP
  set Q : Fin n → LaurentSeries F := fun i => ((A.mulVec (fun c => θ (e' c)) i : PowerSeries F) : LaurentSeries F) with hQ
  set E : Fin n → LaurentSeries F := fun i => ((e i : PowerSeries F) : LaurentSeries F) with hE
  set Fv : Fin n → LaurentSeries F := fun i => ((f i : PowerSeries F) : LaurentSeries F) with hFv
  have h4 : ξ ^ N • P - ((θ a : PowerSeries F) : LaurentSeries F) • Q ∈ W := by
    have : (fun i => ((A.mulVec (fun c => θ (y c)) i : PowerSeries F) : LaurentSeries F)) = ξ ^ N • P - ((θ a : PowerSeries F) : LaurentSeries F) • Q := by
      funext i
      simp only [hvec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, PowerSeries.coe_sub, PowerSeries.coe_mul, PowerSeries.coe_pow, hP, hQ, hξdef]
    rw [← this]; exact hTy
  set c : LaurentSeries F := ((θ a : PowerSeries F) : LaurentSeries F) * α - x ^ m * ξ ^ N * ((d : PowerSeries F) : LaurentSeries F) * ((w : PowerSeries F) : LaurentSeries F) * x ^ k with hc
  have hcE : c • E ∈ W := by
    have h := W.sub_mem (W.sub_mem (W.add_mem (W.smul_mem (x ^ m * ξ ^ N) hTf) (W.smul_mem (x ^ m * ξ ^ N * ((d : PowerSeries F) : LaurentSeries F)) hf)) (W.smul_mem (((θ a : PowerSeries F) : LaurentSeries F)) hTe)) (W.smul_mem (x ^ m) h4)
    convert h using 1
    ext i
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul, hc]
    ring
  have hc0 : c = 0 := by
    by_contra hne
    apply he
    have := W.smul_mem c⁻¹ hcE
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
  have hξN : ξ ^ N ≠ 0 := pow_ne_zero _ hξ
  rw [hc, hθa, sub_eq_zero] at hc0
  apply mul_right_cancel₀ hξN
  linear_combination hc0

end GlobalTheory
end

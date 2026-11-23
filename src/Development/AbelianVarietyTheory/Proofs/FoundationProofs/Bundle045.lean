module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.NumberTheory.LSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle008
public import Mathlib.NumberTheory.LSeries.Convolution
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle013
public import Mathlib.NumberTheory.Padics.Complex
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle014
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle015
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
public import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Mathlib.FieldTheory.Galois.Infinite
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne

@[expose] public section

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory

theorem algEquiv_primitiveRoot_pow :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (s : Ω ≃ₐ[ℚ] Ω) (q : ℕ), 0 < q →
      ∃ e : ℤ, IsCoprime e (q : ℤ) ∧ ∀ ζ : Ω, IsPrimitiveRoot ζ q → s ζ = ζ ^ e := by
  intro Ω _ _ _ s q hq
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NeZero q := ⟨hq.ne'⟩
  haveI : NeZero (q : Ω) := ⟨Nat.cast_ne_zero.mpr hq.ne'⟩
  obtain ⟨ζ₀, hζ₀⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic q Ω)
    (by rw [Polynomial.degree_cyclotomic]; exact_mod_cast (Nat.totient_pos.mpr hq).ne')
  have h0 : IsPrimitiveRoot ζ₀ q := (Polynomial.isRoot_cyclotomic_iff).mp hζ₀
  have h1 : IsPrimitiveRoot (s ζ₀) q := h0.map_of_injective s.injective
  obtain ⟨i, -, hi⟩ := h0.eq_pow_of_pow_eq_one h1.pow_eq_one
  have hcop : i.Coprime q := (h0.pow_iff_coprime hq i).mp (hi ▸ h1)
  refine ⟨(i : ℤ), Int.isCoprime_iff_gcd_eq_one.mpr (by simpa [Int.gcd] using hcop), ?_⟩
  intro ζ hζ
  obtain ⟨k, -, hk⟩ := h0.eq_pow_of_pow_eq_one hζ.pow_eq_one
  subst hk
  rw [zpow_natCast, map_pow, ← hi, ← pow_mul, ← pow_mul, mul_comm]

end GlobalTheory
end

section

open GlobalTheory.K5 Polynomial
open scoped NNReal

namespace GlobalTheory

theorem exists_algEquiv_apply_eq_of_fixes_preimage_base :
    ∀ (Ω L K : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [Field L] [IsAlgClosed L] [Field K] [CharZero K] [Algebra K L] [Algebra.IsAlgebraic K L] (j : Ω →+* L) (s : Ω ≃ₐ[ℚ] Ω), (∀ a : Ω, j a ∈ Set.range (algebraMap K L) → s a = a) → ∀ x : Ω, ∃ g : L ≃ₐ[K] L, g (j x) = j (s x) := by
  intro Ω L K _ _ _ _ _ _ _ _ _ j s hs x
  classical
  haveI : IsAlgClosure K L := ⟨‹_›, ‹_›⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have hint : IsIntegral K (j x) := Algebra.IsIntegral.isIntegral _
  have hxint : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral _
  have hcomp : j.comp (algebraMap ℚ Ω) = (algebraMap K L).comp (algebraMap ℚ K) :=
    RingHom.ext_rat _ _
  set Q : Polynomial Ω := (minpoly ℚ x).map (algebraMap ℚ Ω) with hQ
  have hQ0 : Q ≠ 0 := Polynomial.map_ne_zero (minpoly.ne_zero hxint)
  have hQj : Q.map j = ((minpoly ℚ x).map (algebraMap ℚ K)).map (algebraMap K L) := by
    rw [hQ, Polynomial.map_map, Polynomial.map_map, hcomp]
  have hdvd : minpoly K (j x) ∣ (minpoly ℚ x).map (algebraMap ℚ K) := by
    apply minpoly.dvd
    rw [aeval_def, ← eval_map, ← hQj, eval_map, eval₂_at_apply, hQ, eval_map, ← aeval_def,
      minpoly.aeval, map_zero]
  set P : L[X] := (minpoly K (j x)).map (algebraMap K L) with hP
  have hPm : P.Monic := (minpoly.monic hint).map _
  have hPQ : P ∣ Q.map j := by
    rw [hQj]; exact Polynomial.map_dvd _ hdvd
  have hroots : ∀ r ∈ P.roots, r ∈ Set.range j := by
    intro r hr
    have h1 : r ∈ (Q.map j).roots :=
      Multiset.mem_of_le (roots.le_of_dvd (Polynomial.map_ne_zero hQ0) hPQ) hr
    rw [(IsAlgClosed.splits Q).roots_map j] at h1
    obtain ⟨a, -, ha⟩ := Multiset.mem_map.1 h1
    exact ⟨a, ha⟩
  have hlift : P ∈ lifts j := by
    rw [(IsAlgClosed.splits P).eq_prod_roots_of_monic hPm]
    refine Subsemiring.multiset_prod_mem _ _ ?_
    intro q hq
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hq
    obtain ⟨a, rfl⟩ := hroots r hr
    exact (mem_lifts _).2 ⟨X - C a, by simp⟩
  obtain ⟨M, hM⟩ := (mem_lifts _).1 hlift
  have hMs : M.map (s : Ω →+* Ω) = M := by
    ext n
    rw [coeff_map]
    refine hs _ ⟨(minpoly K (j x)).coeff n, ?_⟩
    rw [← coeff_map, ← coeff_map, hM]
  have hMx : M.eval x = 0 := by
    apply j.injective
    rw [← eval₂_at_apply, ← eval_map, hM, hP, eval_map, ← aeval_def, minpoly.aeval, map_zero]
  have hMsx : M.eval (s x) = 0 := by
    have h := eval₂_at_apply (p := M) (s : Ω →+* Ω) x
    rw [← eval_map, hMs, hMx, map_zero] at h
    exact h
  have hroot : aeval (j (s x)) (minpoly K (j x)) = 0 := by
    rw [aeval_def, ← eval_map, ← hP, ← hM, eval_map, eval₂_at_apply, hMsx, map_zero]
  exact (isConjRoot_of_aeval_eq_zero hint hroot).symm.exists_algEquiv

end GlobalTheory
end

section

open GlobalTheory.NeedB Polynomial

namespace GlobalTheory

theorem zeta_pow_val_add {Ω : Type} [Field Ω] {N : ℕ} [NeZero N] {ζ : Ω} (hζN : ζ ^ N = 1) (x y : ZMod N) :
    ζ ^ (x + y).val = ζ ^ x.val * ζ ^ y.val := by
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.div_add_mod (x.val + y.val) N, pow_add, pow_mul, hζN, one_pow, one_mul]

theorem kummer_generator_of_char : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (N : ℕ) (ζ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) → ∀ (E : IntermediateField K Ω) (χ : (Ω ≃ₐ[K] Ω) → ZMod N),
  IsLocallyConstant χ → (∀ g ∈ E.fixingSubgroup, ∀ h ∈ E.fixingSubgroup, χ (g * h) = χ g + χ h) →
  ∃ θ : Ω, θ ≠ 0 ∧ θ ^ N ∈ E ∧ ∀ g ∈ E.fixingSubgroup, g θ = ζ ^ (χ g).val * θ := by
  intro K Ω _ _ _ _ _ N ζ hN hζ hfix E χ hχ hadd
  haveI : NeZero N := ⟨hN.ne'⟩
  classical
  set H := E.fixingSubgroup with hH
  have hζN : ζ ^ N = 1 := hζ.pow_eq_one
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN.ne'
  have h1 : χ 1 = 0 := by
    have := hadd 1 H.one_mem 1 H.one_mem
    simpa using this

  have hV : {g : Ω ≃ₐ[K] Ω | χ g = 0} ∈ nhds (1 : Ω ≃ₐ[K] Ω) := by
    have := (hχ.isOpen_fiber (χ 1)).mem_nhds (show (1 : Ω ≃ₐ[K] Ω) ∈ χ ⁻¹' {χ 1} from rfl)
    simpa [h1] using this
  obtain ⟨F, hFfin, hFV⟩ := (krullTopology_mem_nhds_one_iff K Ω _).mp hV

  let r : (Ω ≃ₐ[K] Ω) → (F →ₐ[K] Ω) := fun g => (g : Ω →ₐ[K] Ω).comp F.val
  have hr : ∀ g x, r g x = g (x : Ω) := fun _ _ => rfl
  have hrχ : ∀ g ∈ H, ∀ h ∈ H, r g = r h → χ g = χ h := by
    intro g hg h hh he
    have hm : h⁻¹ * g ∈ H := H.mul_mem (H.inv_mem hh) hg
    have hF : h⁻¹ * g ∈ F.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have := congrArg (fun φ => φ ⟨x, hx⟩) he
      simp only [hr] at this
      simp [AlgEquiv.mul_apply, this]
    have h0 : χ (h⁻¹ * g) = 0 := hFV hF
    have := hadd h hh (h⁻¹ * g) hm
    rw [mul_inv_cancel_left, h0, add_zero] at this
    exact this
  haveI : FiniteDimensional K F := hFfin
  let ι := {φ : F →ₐ[K] Ω // ∃ g ∈ H, r g = φ}
  haveI : Finite (F →ₐ[K] Ω) := inferInstance
  haveI : Fintype ι := Fintype.ofFinite ι
  let s : ι → (Ω ≃ₐ[K] Ω) := fun i => i.2.choose
  have hsH : ∀ i, s i ∈ H := fun i => i.2.choose_spec.1
  have hsr : ∀ i, r (s i) = i.1 := fun i => i.2.choose_spec.2
  let a : (Ω ≃ₐ[K] Ω) → Ω := fun g => ζ ^ (χ g).val
  have ha0 : ∀ g, a g ≠ 0 := fun g => pow_ne_zero _ hζ0
  have hamul : ∀ g ∈ H, ∀ h ∈ H, a (g * h) = a g * a h := by
    intro g hg h hh
    simp only [a, hadd g hg h hh, zeta_pow_val_add hζN]
  have hafix : ∀ (g h : Ω ≃ₐ[K] Ω), g (a h) = a h := by
    intro g h; simp only [a, map_pow, hfix]
  let w : ι → Ω := fun i => (a (s i))⁻¹

  let v : ι → (F →* Ω) := fun i => (i.1 : F →+* Ω).toMonoidHom
  have hv : Function.Injective v := by
    intro i j hij
    apply Subtype.ext
    apply AlgHom.ext
    intro x
    exact DFunLike.congr_fun hij x
  have hli := (linearIndependent_monoidHom F Ω).comp v hv
  obtain ⟨c, hc⟩ : ∃ c : F, ∑ i, w i * i.1 c ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hz : ∑ i, w i • ((v i : F →* Ω) : F → Ω) = 0 := by
      funext x
      simpa [Finset.sum_apply, v] using hcon x
    have := Fintype.linearIndependent_iff.mp hli w hz ⟨r 1, 1, H.one_mem, rfl⟩
    exact inv_ne_zero (ha0 _) this
  have hmain : ∀ g ∈ H, g (∑ i, w i * i.1 c) = a g * ∑ i, w i * i.1 c := by
    intro g hg
    let e : ι → ι := fun i => ⟨r (g * s i), g * s i, H.mul_mem hg (hsH i), rfl⟩
    have hic : ∀ i : ι, i.1 c = s i (c : Ω) := by
      intro i; rw [← hsr i]; exact hr _ _
    have hec : ∀ i, (e i).1 c = g (i.1 c) := by
      intro i; rw [hic i]; rfl
    have hwe : ∀ i, w i = a g * w (e i) := by
      intro i
      have hχe : χ (s (e i)) = χ (g * s i) :=
        hrχ _ (hsH (e i)) _ (H.mul_mem hg (hsH i)) (hsr (e i))
      have : a (s (e i)) = a g * a (s i) := by
        rw [← hamul g hg (s i) (hsH i)]; simp only [a, hχe]
      simp only [w, this, mul_inv, ← mul_assoc, mul_inv_cancel₀ (ha0 g), one_mul]
    have he : Function.Injective e := by
      intro i j hij
      have h2 : r (g * s i) = r (g * s j) := congrArg Subtype.val hij
      apply Subtype.ext
      rw [← hsr i, ← hsr j]
      apply AlgHom.ext
      intro x
      have := DFunLike.congr_fun h2 x
      simp only [hr, AlgEquiv.mul_apply] at this
      simpa [hr] using g.injective this
    have hb : Function.Bijective e := Finite.injective_iff_bijective.mp he

    rw [map_sum, Finset.mul_sum]
    simp only [map_mul, hfix, w, map_inv₀, hafix]
    refine (Fintype.sum_bijective e hb _ _ ?_)
    intro i
    have h3 := hwe i
    simp only [w] at h3
    rw [h3, ← hec i]; ring
  refine ⟨∑ i, w i * i.1 c, hc, ?_, ?_⟩
  · haveI : IsGalois K Ω := IsAlgClosure.isGalois K Ω
    rw [← InfiniteGalois.fixedField_fixingSubgroup E, IntermediateField.mem_fixedField_iff]
    intro g hg
    have key := hmain g hg
    rw [map_pow, key, mul_pow]
    have : a g ^ N = 1 := by
      show (ζ ^ (χ g).val) ^ N = 1
      rw [← pow_mul, mul_comm, pow_mul, hζN, one_pow]
    rw [this, one_mul]
  · exact hmain

end GlobalTheory
end

section

open GlobalTheory.K5 Polynomial
open scoped NNReal

namespace GlobalTheory

theorem isClosed_setOf_algEquiv_apply_eq {K L : Type} [Field K] [Field L] [Algebra K L]
    [Algebra.IsIntegral K L] (a b : L) : IsClosed {g : L ≃ₐ[K] L | g a = b} := by
  by_cases h : ∃ g₀ : L ≃ₐ[K] L, g₀ a = b
  · obtain ⟨g₀, hg₀⟩ := h
    have hc : IsClosed ((MulAction.stabilizer (L ≃ₐ[K] L) a : Subgroup _) : Set (L ≃ₐ[K] L)) :=
      Subgroup.isClosed_of_isOpen _ (stabilizer_isOpen_of_isIntegral a)
    have hp := hc.preimage (continuous_const_mul g₀⁻¹)
    convert hp using 1
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, SetLike.mem_coe, MulAction.mem_stabilizer_iff,
      mul_smul, inv_smul_eq_iff]
    simp only [AlgEquiv.smul_def, hg₀]
  · have : {g : L ≃ₐ[K] L | g a = b} = ∅ := by
      ext g
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hg => h ⟨g, hg⟩
    rw [this]
    exact isClosed_empty

theorem exists_primitive_for_finset (k : Type) {Ω : Type} [Field k] [CharZero k] [Field Ω]
    [Algebra k Ω] [Algebra.IsAlgebraic k Ω]
    (u : Finset Ω) : ∃ x : Ω, ∀ {L : Type} [Field L] (φ ψ : Ω →+* L),
      φ.comp (algebraMap k Ω) = ψ.comp (algebraMap k Ω) → φ x = ψ x →
      ∀ y ∈ u, φ y = ψ y := by
  let F : IntermediateField k Ω := IntermediateField.adjoin k (u : Set Ω)
  haveI : FiniteDimensional k F :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  obtain ⟨α, hα⟩ := Field.exists_primitive_element k F
  refine ⟨α, fun {L} _ φ ψ hk hx y hy => ?_⟩
  have key : ∀ z : F, z ∈ IntermediateField.adjoin k {α} → φ z = ψ z := by
    intro z hz
    induction hz using IntermediateField.adjoin_induction with
    | mem x hx' =>
      rw [Set.mem_singleton_iff.mp hx']
      exact hx
    | algebraMap q =>
      exact DFunLike.congr_fun hk q
    | add x y _ _ hx hy => simp [hx, hy]
    | inv x _ hx => simp [hx]
    | mul x y _ _ hx hy => simp [hx, hy]
  exact key ⟨y, IntermediateField.subset_adjoin k _ hy⟩ (by rw [hα]; trivial)

theorem exists_algEquiv_inducing_of_forall_conj :
    ∀ (Ω L K : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [Field L] [IsAlgClosed L]
      [Field K] [CharZero K] [Algebra K L] [Algebra.IsAlgebraic K L] (j : Ω →+* L)
      (s : Ω ≃ₐ[ℚ] Ω), (∀ x : Ω, ∃ g : L ≃ₐ[K] L, g (j x) = j (s x)) →
      ∃ g : L ≃ₐ[K] L, ∀ x : Ω, g (j x) = j (s x) := by
  intro Ω L K _ _ _ _ _ _ _ _ _ j s h
  haveI : IsAlgClosure K L := ⟨inferInstance, inferInstance⟩
  haveI : IsGalois K L := {}
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have hne := (isCompact_univ (X := L ≃ₐ[K] L)).inter_iInter_nonempty
    (fun x : Ω => {g : L ≃ₐ[K] L | g (j x) = j (s x)})
    (fun x => isClosed_setOf_algEquiv_apply_eq _ _)
    (fun u => by
      obtain ⟨x, hx⟩ := exists_primitive_for_finset ℚ u
      obtain ⟨g, hg⟩ := h x
      refine ⟨g, Set.mem_univ _, ?_⟩
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
      intro y hy
      exact hx ((g : L →+* L).comp j) (j.comp (s : Ω →+* Ω)) (RingHom.ext_rat _ _) hg y hy)
  obtain ⟨g, -, hg⟩ := hne
  simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hg
  exact ⟨g, hg⟩

end GlobalTheory
end

section

open GlobalTheory.NeedB Polynomial

namespace GlobalTheory

theorem norm_isHomogeneous_poly_coords :
    ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L],
      ∃ f : MvPolynomial (Fin (Module.finrank K L)) K, f.IsHomogeneous (Module.finrank K L) ∧
        ∀ x : L, Algebra.norm K x =
          MvPolynomial.eval (fun i => (Module.finBasis K L).repr x i) f := by
  first
  | exact @_root_.GlobalTheory.IdealPowerMembership.main
  | exact _root_.GlobalTheory.IdealPowerMembership.main
  | (apply _root_.GlobalTheory.IdealPowerMembership.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IdealPowerMembership.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IdealPowerMembership.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IdealPowerMembership.main ..)

end GlobalTheory
end

section

open Complex Filter Topology

theorem _root_.GlobalTheory.T.lSeries_twist_natPow_eq_shift : ∀ (e : ℕ) (ψ g : ℕ → ℂ) (s : ℝ), 1 ≤ e → LSeries (fun n : ℕ => ψ n * (n : ℂ) ^ (e - 1) * g n) (((2 * (e : ℝ) + s : ℝ)) : ℂ) = LSeries (fun n => ψ n * g n) ((e + 1 : ℝ) + s : ℝ) := by
  first | exact @GlobalTheory.lseries_shift_twist | exact GlobalTheory.lseries_shift_twist | (intros; apply GlobalTheory.lseries_shift_twist <;> assumption)
end

section

open Complex Filter Topology

theorem _root_.GlobalTheory.T.lSeries_squares_eq_shift : ∀ (e : ℕ) (χ ψ θ : ℕ → ℂ) (s : ℝ), 1 ≤ e → 0 < s → (∀ n, ‖χ n‖ ≤ 1 ∧ ‖ψ n‖ ≤ 1 ∧ ‖θ n‖ ≤ 1) → LSeriesSummable (fun n : ℕ => if Nat.sqrt n * Nat.sqrt n = n then χ (Nat.sqrt n) * ψ (Nat.sqrt n) * θ (Nat.sqrt n) * (Nat.sqrt n : ℂ) ^ (3 * e - 1) else 0) (((2 * (e : ℝ) + s : ℝ)) : ℂ) ∧ LSeries (fun n : ℕ => if Nat.sqrt n * Nat.sqrt n = n then χ (Nat.sqrt n) * ψ (Nat.sqrt n) * θ (Nat.sqrt n) * (Nat.sqrt n : ℂ) ^ (3 * e - 1) else 0) (((2 * (e : ℝ) + s : ℝ)) : ℂ) = LSeries (fun n => χ n * ψ n * θ n) ((e + 1 : ℕ) + 2 * s) := by
  first | exact @GlobalTheory.lseriesSquares_eq | exact GlobalTheory.lseriesSquares_eq | (intros; apply GlobalTheory.lseriesSquares_eq <;> assumption)
end

section

open Complex Filter Topology

theorem _root_.GlobalTheory.T.lSeriesSummable_twist_pow_of_summable_sq_div : ∀ (e : ℕ) (ψ g : ℕ → ℂ) (s : ℝ), 1 ≤ e → 0 < s → (∀ n, ‖ψ n‖ ≤ 1) → (∀ t : ℝ, 0 < t → Summable fun n : ℕ => ‖g n‖ ^ 2 / (n : ℝ) ^ (((2 * e + 1 : ℕ) : ℝ) + t)) → LSeriesSummable (fun n : ℕ => ψ n * (n : ℂ) ^ (e - 1) * g n) (((2 * (e : ℝ) + s : ℝ)) : ℂ) := by
  first | exact @GlobalTheory.lseriesSummable_twist_pow_of_sq_summable | exact GlobalTheory.lseriesSummable_twist_pow_of_sq_summable | (intros; apply GlobalTheory.lseriesSummable_twist_pow_of_sq_summable <;> assumption)
end

section

open Complex Filter Topology

theorem _root_.GlobalTheory.T.convolution_twist_eq_convolution_squares : ∀ (e : ℕ) (χ ψ θ g b : ℕ → ℂ), (∀ m n, ψ (m * n) = ψ m * ψ n) → (∀ m n, θ (m * n) = θ m * θ n) → (∀ m n : ℕ, 0 < m → 0 < n → g m * g n = ∑ δ ∈ (Nat.gcd m n).divisors, χ δ * (δ : ℂ) ^ (2 * e) * g (m * n / δ ^ 2)) → (∀ n, n ≠ 0 → b n = ∑ p ∈ n.divisorsAntidiagonal, ψ p.1 * (p.1 : ℂ) ^ (e - 1) * θ p.2) → ∀ n : ℕ, n ≠ 0 → LSeries.convolution (fun n : ℕ => ψ n * (n : ℂ) ^ (e - 1) * g n) (fun n : ℕ => θ n * g n) n = LSeries.convolution (fun n : ℕ => if Nat.sqrt n * Nat.sqrt n = n then χ (Nat.sqrt n) * ψ (Nat.sqrt n) * θ (Nat.sqrt n) * (Nat.sqrt n : ℂ) ^ (3 * e - 1) else 0) (fun n : ℕ => g n * b n) n := by
  first | exact @GlobalTheory.rankin_convolution_coeff | exact GlobalTheory.rankin_convolution_coeff | (intros; apply GlobalTheory.rankin_convolution_coeff <;> assumption)
end

section

open scoped Matrix

theorem _root_.GlobalTheory.T.coboundary_of_padicAlgCl_uniform_approx : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) (S : Set Γ) (M : Γ → Matrix (Fin 2) (Fin 2) (PadicAlgCl l)) (f : ℕ → Γ → Fin 2 → PadicAlgCl l) (y : Γ → Fin 2 → PadicAlgCl l), (∀ s i j, ‖M s i j‖ ≤ 1) → (∀ r, ∃ v : Fin 2 → PadicAlgCl l, ∀ s ∈ S, f r s = M s *ᵥ v - v) → (∀ r s i, ‖y s i - f r s i‖ ≤ ‖((l : ℕ) : PadicAlgCl l) ^ r‖) → ∃ v : Fin 2 → PadicAlgCl l, ∀ s ∈ S, y s = M s *ᵥ v - v := by
  first | exact @GlobalTheory.UniformCoboundary.coboundary_of_padic_approx | exact GlobalTheory.UniformCoboundary.coboundary_of_padic_approx | (intros; apply GlobalTheory.UniformCoboundary.coboundary_of_padic_approx <;> assumption)
end

section


theorem _root_.GlobalTheory.T.mem_span_eigen_of_baseChange_eigen' : ∀ (l : ℕ) [Fact l.Prime] (M S : Type) [AddCommGroup M] [Module ℤ_[l] M] (B : Submodule ℤ_[l] M) [Module.Free ℤ_[l] B]
  (g : S → Module.End ℤ_[l] M) (χ : S → ℤ_[l]), (∀ s, ∀ b ∈ B, g s b ∈ B) →
  ∀ x ∈ LinearMap.range (LinearMap.baseChange (PadicAlgCl l) B.subtype),
  (∀ s, LinearMap.baseChange (PadicAlgCl l) (g s) x = algebraMap ℤ_[l] (PadicAlgCl l) (χ s) • x) →
  x ∈ Submodule.span (PadicAlgCl l) {y | ∃ b ∈ B, (∀ s, g s b = χ s • b) ∧ y = (1 : PadicAlgCl l) ⊗ₜ[ℤ_[l]] b} := by
  first | exact @GlobalTheory.mem_span_eigen_of_baseChange_eigen | exact GlobalTheory.mem_span_eigen_of_baseChange_eigen | (intros; apply GlobalTheory.mem_span_eigen_of_baseChange_eigen <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_uniformizer_valuation_lt_one_frobenius_congr : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra ℤ_[p] Ω], Function.Injective (algebraMap ℤ_[p] Ω) →
  ∀ v : Valuation Ω NNReal, (∀ x : Ω, IsIntegral ℤ_[p] x → v x ≤ 1) → v (p : Ω) < 1 →
  ∀ R : Subalgebra ℤ_[p] Ω, Module.Finite ℤ_[p] R → IsPrincipalIdealRing R →
  ∃ π ∈ R, π ≠ 0 ∧ v π < 1 ∧ (p : Ω) / π ∈ R ∧ ∃ f : ℕ, 0 < f ∧ ∀ t ∈ R, (t ^ p ^ f - t) / π ∈ R := by
  first | exact @GlobalTheory.exists_generator_valuation_prime_dvd_pow_sub_of_finite_padicInt | exact GlobalTheory.exists_generator_valuation_prime_dvd_pow_sub_of_finite_padicInt | (intros; apply GlobalTheory.exists_generator_valuation_prime_dvd_pow_sub_of_finite_padicInt <;> assumption)
end

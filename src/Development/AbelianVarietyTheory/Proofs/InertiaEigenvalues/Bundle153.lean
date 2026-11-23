module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.WittVector.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle137
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
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Mathlib.NumberTheory.GaussSum
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
import ReciprocityTheory.GaloisValuations.GlobalA
public import Mathlib.FieldTheory.Galois.Infinite

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory

theorem sqrt_neg_l_mem_adjoin_roots_of_unity :
    ∀ (l : ℕ) [Fact l.Prime], l % 4 = 3 → ∀ y : Om l, y ^ 2 = -(l : Om l) →
      y ∈ IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1} := by
  intro l _ h4 y hy
  set K := IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1} with hK
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) l
  have hchar : ringChar (ZMod l) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  have hm1 : quadraticChar (ZMod l) (-1) = -1 := by
    rw [quadraticChar_neg_one hchar, ZMod.card, ZMod.χ₄_nat_three_mod_four h4]
  set χ := (quadraticChar (ZMod l)).ringHomComp (Int.castRingHom (Om l)) with hχdef
  have hχm1 : χ (-1) = -1 := by
    simp [χ, MulChar.ringHomComp_apply, hm1]
  have h2 : (2 : Om l) ≠ 0 := two_ne_zero
  have hχ1 : χ ≠ 1 := by
    intro h
    rw [h, MulChar.one_apply (isUnit_one.neg)] at hχm1
    apply h2; linear_combination hχm1
  have hq : χ.IsQuadratic := (quadraticChar_isQuadratic (ZMod l)).comp _
  have hψ := AddChar.zmodChar_primitive_of_primitive_root l hζ
  have hsq := gaussSum_sq hχ1 hq hψ
  rw [hχm1, ZMod.card] at hsq
  set g := gaussSum χ (AddChar.zmodChar l hζ.pow_eq_one) with hg

  have hgK : g ∈ K := by
    rw [hg, gaussSum]
    refine sum_mem fun a _ => mul_mem ?_ ?_
    · rw [hχdef, MulChar.ringHomComp_apply]
      exact intCast_mem K _
    · rw [AddChar.zmodChar_apply]
      refine pow_mem (IntermediateField.subset_adjoin _ _ ?_) _
      show ζ ^ (l ^ 1) = 1
      rw [pow_one]; exact hζ.pow_eq_one

  have hyg : (y - g) * (y + g) = 0 := by
    linear_combination hy - hsq
  rcases mul_eq_zero.1 hyg with h | h
  · rw [sub_eq_zero.1 h]; exact hgK
  · rw [eq_neg_of_add_eq_zero_left h]; exact neg_mem hgK

end GlobalTheory
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.UnramDisjoint

theorem coeff_eq_zero_of_stable {F Ω ι : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
    [Fintype ι] (K N : IntermediateField F Ω)
    (hN : ∀ (g : Ω ≃ₐ[F] Ω) (y : Ω), y ∈ N → g y ∈ N) (x : ι → Ω) (hx : ∀ i, x i ∈ K)
    (hind : ∀ c : ι → Ω, (∀ i, c i ∈ K ⊓ N) → ∑ i, c i * x i = 0 → ∀ i, c i = 0)
    (c : ι → Ω) (hc : ∀ i, c i ∈ N) (h : ∑ i, c i * x i = 0) : ∀ i, c i = 0 := by
  classical
  suffices H : ∀ n : ℕ, ∀ c : ι → Ω, (Finset.univ.filter (fun i => c i ≠ 0)).card = n →
      (∀ i, c i ∈ N) → ∑ i, c i * x i = 0 → ∀ i, c i = 0 from H _ c rfl hc h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro c hcard hc h
  by_contra hne
  obtain ⟨j, hj⟩ := not_forall.mp hne

  set d : ι → Ω := fun i => c i * (c j)⁻¹ with hd
  have hdN : ∀ i, d i ∈ N := fun i => N.mul_mem (hc i) (N.inv_mem (hc j))
  have hdj : d j = 1 := mul_inv_cancel₀ hj
  have hdsum : ∑ i, d i * x i = 0 := by
    calc ∑ i, d i * x i = (∑ i, c i * x i) * (c j)⁻¹ := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl (fun i _ => by simp only [hd]; ring)
      _ = 0 := by rw [h, zero_mul]

  have hfix : ∀ g ∈ K.fixingSubgroup, ∀ i, g (d i) = d i := by
    intro g hg
    have hgx : ∀ i, g (x i) = x i := fun i => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg _ (hx i)
    set e : ι → Ω := fun i => g (d i) - d i with he
    have heN : ∀ i, e i ∈ N := fun i => N.sub_mem (hN g _ (hdN i)) (hdN i)
    have h2 : ∑ i, g (d i) * x i = 0 := by
      have := congrArg g hdsum

      rw [map_sum, map_zero] at this
      simpa only [map_mul, hgx] using this
    have hesum : ∑ i, e i * x i = 0 := by
      simp only [he, sub_mul, Finset.sum_sub_distrib, h2, hdsum, sub_zero]
    have hej : e j = 0 := by simp only [he, hdj, map_one, sub_self]
    have hlt : (Finset.univ.filter (fun i => e i ≠ 0)).card < n := by
      rw [← hcard]
      apply Finset.card_lt_card
      refine (Finset.ssubset_iff_of_subset ?_).mpr ⟨j, ?_, ?_⟩
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        intro hci
        apply hi
        have hdi : d i = 0 := by simp only [hd, hci, zero_mul]
        simp only [he, hdi, map_zero, sub_zero]
      · simp [hj]
      · simp [hej]
    intro i
    exact sub_eq_zero.mp (ih _ hlt e rfl heN hesum i)

  have hdK : ∀ i, d i ∈ K := by
    intro i
    rw [← InfiniteGalois.fixedField_fixingSubgroup K, IntermediateField.mem_fixedField_iff]
    exact fun g hg => hfix g hg i
  have h0 := hind d (fun i => ⟨hdK i, hdN i⟩) hdsum j
  rw [hdj] at h0
  exact one_ne_zero h0

theorem apply_mem_Kur {l : ℕ} [Fact l.Prime] (g : GQ l) (y : Om l) (hy : y ∈ MaximalUnramifiedExtension l) :
    g y ∈ MaximalUnramifiedExtension l := by
  delta MaximalUnramifiedExtension at hy ⊢
  have hmap : (IntermediateField.adjoin ℚ_[l] {x : PadicAlgCl l | ∃ m, 0 < m ∧ ¬l ∣ m ∧ x ^ m = 1}).map
      (g : PadicAlgCl l →ₐ[ℚ_[l]] PadicAlgCl l) ≤
      IntermediateField.adjoin ℚ_[l] {x : PadicAlgCl l | ∃ m, 0 < m ∧ ¬l ∣ m ∧ x ^ m = 1} := by
    rw [IntermediateField.adjoin_map]
    apply IntermediateField.adjoin.mono
    rintro _ ⟨z, ⟨m, hm, hl, hz⟩, rfl⟩
    exact ⟨m, hm, hl, by rw [← map_pow, hz, map_one]⟩
  exact hmap ⟨y, hy, rfl⟩

theorem linearIndependent_Kur (l : ℕ) [Fact l.Prime] (K : FinExt l) (m : ℕ) (x : Fin m → ↥K.1)
    (hx : LinearIndependent ↥(K0 K) x) :
    LinearIndependent ↥(MaximalUnramifiedExtension l) (fun i => (x i : Om l)) := by
  rw [Fintype.linearIndependent_iff] at hx ⊢
  intro a ha
  have hcoe : ∀ z : ↥(K0 K), ((algebraMap ↥(K0 K) ↥K.1 z : ↥K.1) : Om l) = z := fun z => rfl
  have hzero := coeff_eq_zero_of_stable (F := ℚ_[l]) K.1 (MaximalUnramifiedExtension l) (fun g y hy => apply_mem_Kur g y hy)
    (fun i => (x i : Om l)) (fun i => (x i).2)
    (fun c hc hsum => by
      have hc0 := hx (fun i => ⟨c i, hc i⟩) (by
        apply Subtype.ext
        simpa [Algebra.smul_def, hcoe] using hsum)
      intro i
      simpa using congrArg Subtype.val (hc0 i))
    (fun i => (a i : Om l)) (fun i => (a i).2)
    (by simpa [Algebra.smul_def] using ha)
  intro i
  exact Subtype.ext (hzero i)

end GlobalTheory.UnramDisjoint
end

section

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory

theorem exists_primitiveRoot_coeffRing_of_good {l : ℕ} [Fact l.Prime] (K LL : FinExt l)
    (h : Good K 1 LL) : ∃ ζ : ↥(OL LL), IsPrimitiveRoot ζ l := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have hdeg : (Polynomial.cyclotomic l (Om l)).degree ≠ 0 :=
    (Polynomial.degree_cyclotomic_pos l (Om l) hl).ne'
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root _ hdeg
  haveI : NeZero (l : Om l) := ⟨Nat.cast_ne_zero.mpr hl.ne'⟩
  have hζ : IsPrimitiveRoot z l := Polynomial.isRoot_cyclotomic_iff.mp hz
  have hmem : z ∈ Ks K 1 := by
    refine (le_sup_right : _ ≤ Ks K 1) ?_
    apply IntermediateField.subset_adjoin
    change z ^ (l ^ 1) = 1
    rw [pow_one]
    exact hζ.pow_eq_one
  have hLL : z ∈ LL.1 := h.2.2.2 (Ks K 1).val ⟨z, hmem⟩
  have hζ' : IsPrimitiveRoot (⟨z, hLL⟩ : ↥LL.1) l :=
    IsPrimitiveRoot.of_map_of_injective (f := LL.1.val) hζ Subtype.val_injective
  have hint : IsIntegral ℤ_[l] (⟨z, hLL⟩ : ↥LL.1) :=
    IsIntegral.of_pow hl (by rw [hζ'.pow_eq_one]; exact isIntegral_one)
  exact ⟨⟨⟨z, hLL⟩, hint⟩,
    IsPrimitiveRoot.of_map_of_injective (f := (OL LL).val) hζ' Subtype.val_injective⟩

end GlobalTheory
end

section

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory

theorem exists_padicInt_of_mem_OL {l : ℕ} [Fact l.Prime] (LL : FinExt l) (x : ℚ_[l])
    (hx : algebraMap ℚ_[l] ↥LL.1 x ∈ OL LL) : ∃ y : ℤ_[l], algebraMap ℤ_[l] ℚ_[l] y = x := by
  have hint : IsIntegral ℤ_[l] (algebraMap ℚ_[l] ↥LL.1 x) := hx
  have hint' : IsIntegral ℤ_[l] x :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ_[l] ℚ_[l] ↥LL.1)
      (algebraMap ℚ_[l] ↥LL.1).injective).mp hint
  exact IsIntegrallyClosed.isIntegral_iff.mp hint'

theorem algebraMap_padicInt_finExt_injective {l : ℕ} [Fact l.Prime] (LL : FinExt l) :
    Function.Injective (algebraMap ℤ_[l] ↥LL.1) := by
  rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] ↥LL.1]
  exact (algebraMap ℚ_[l] ↥LL.1).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])

theorem algebraMap_padicInt_OL_injective {l : ℕ} [Fact l.Prime] (LL : FinExt l) :
    Function.Injective (algebraMap ℤ_[l] ↥(OL LL)) := by
  intro a b h
  exact algebraMap_padicInt_finExt_injective LL (congrArg Subtype.val h)

private theorem associated_prime_of_valuation_eq_one {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l)
    (c : ℤ_[l]) (hc : P.v LL (algebraMap ℤ_[l] ↥LL.1 c) = 1) : Associated c (l : ℤ_[l]) := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero, AddValuation.map_zero] at hc
    exact WithTop.top_ne_one hc
  have hspec := PadicInt.unitCoeff_spec hc0
  set u := PadicInt.unitCoeff hc0
  have hnn : ∀ w : ℤ_[l], 0 ≤ P.v LL (algebraMap ℤ_[l] ↥LL.1 w) := fun w =>
    (P.v_O LL _).mpr (Subalgebra.algebraMap_mem _ w)
  have hu0 : P.v LL (algebraMap ℤ_[l] ↥LL.1 (u : ℤ_[l])) = 0 := by
    have h1 : P.v LL (algebraMap ℤ_[l] ↥LL.1 (u : ℤ_[l])) +
        P.v LL (algebraMap ℤ_[l] ↥LL.1 ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l])) = 0 := by
      rw [← AddValuation.map_mul, ← map_mul, Units.mul_inv, map_one, AddValuation.map_one]
    exact ((add_eq_zero_iff_of_nonneg (hnn _) (hnn _)).mp h1).1
  have hval : c.valuation = 1 := by
    rw [hspec, map_mul, AddValuation.map_mul, hu0, zero_add, map_pow, AddValuation.map_pow,
      map_natCast, P.v_l LL, nsmul_one] at hc
    exact_mod_cast hc
  refine ⟨u⁻¹, ?_⟩
  conv_lhs => rw [hspec]
  rw [hval, pow_one, mul_comm, ← mul_assoc, Units.inv_mul, one_mul]

theorem associated_of_v_sub_one {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l)
    (y : ℤ_[l]) (x : ↥(OL LL)) (hy : algebraMap ℤ_[l] ↥(OL LL) y = x)
    (h : P.v LL (algebraMap ↥(OL LL) ↥LL.1 x - 1) = 1) : Associated (y - 1) (l : ℤ_[l]) := by
  apply associated_prime_of_valuation_eq_one P LL
  have hx : algebraMap ↥(OL LL) ↥LL.1 x = algebraMap ℤ_[l] ↥LL.1 y := by
    rw [← hy]
    rfl
  rw [map_sub, map_one, ← hx]
  exact h

theorem exists_units_hom_lift {Γ R S : Type} [Group Γ] [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Injective φ) (c : Γ →* Sˣ) (hex : ∀ g, ∃ y : R, φ y = (c g : S)) :
    ∃ χ : Γ →* Rˣ, ∀ g, φ (χ g : R) = (c g : S) := by
  choose y hy using hex
  have hinv : ∀ g, y g * y g⁻¹ = 1 := fun g => hφ (by
    rw [map_mul, hy, hy, map_one, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one])
  have hinv' : ∀ g, y g⁻¹ * y g = 1 := fun g => by simpa using hinv g⁻¹
  let u : Γ → Rˣ := fun g => ⟨y g, y g⁻¹, hinv g, hinv' g⟩
  refine ⟨{ toFun := u, map_one' := ?_, map_mul' := ?_ }, fun g => hy g⟩
  · ext
    apply hφ
    simp [u, hy]
  · intro g h
    ext
    apply hφ
    simp [u, hy]

theorem exists_cyclotomicChar_padicInt_units : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) {n : ℕ} (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n), ∃ χ : W.Gam →* ℤ_[l]ˣ, (∀ g, algebraMap ℤ_[l] ↥(OL LL) (χ g : ℤ_[l]) = (W.χΓ g : ↥(OL LL))) ∧ (W.s = 1 → Associated ((χ W.gam : ℤ_[l]) - 1) (l : ℤ_[l])) := by
  intro l _ P K LL n W
  have hex : ∀ g, ∃ y : ℤ_[l], algebraMap ℤ_[l] ↥(OL LL) y = (W.χΓ g : ↥(OL LL)) := by
    intro g
    obtain ⟨h, rfl⟩ := W.resΓ_onto g
    have hmem : algebraMap ℚ_[l] ↥LL.1 ((P.PD K).χ h : ℚ_[l]) ∈ OL LL := by
      rw [← W.χΓ_res h]
      exact (W.χΓ (W.resΓ h) : ↥(OL LL)).2
    obtain ⟨y, hy⟩ := exists_padicInt_of_mem_OL LL _ hmem
    refine ⟨y, Subtype.ext ?_⟩
    show algebraMap ℤ_[l] ↥LL.1 y = _
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1, hy, ← W.χΓ_res h]
    rfl
  obtain ⟨χ, hχ⟩ := exists_units_hom_lift (algebraMap ℤ_[l] ↥(OL LL))
    (algebraMap_padicInt_OL_injective LL) W.χΓ hex
  refine ⟨χ, hχ, fun hs => ?_⟩
  apply associated_of_v_sub_one P LL _ _ (hχ W.gam)
  have hg := W.gam_gen
  rw [hs, Nat.cast_one] at hg
  exact hg

end GlobalTheory
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory

theorem exists_isPt_primitiveRoot {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P)
    {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL)
    (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) :
    ∃ (ζ : ↥LL.1) (τ : ↥(Ks K s) →ₐ[ℚ_[l]] ↥LL.1), H.IsPt h i ζ τ ∧ IsPrimitiveRoot ζ (l ^ s) := by
  have hs : 1 ≤ s := h.1
  have hLL := h.2.2.2
  have hprim : IsPrimitiveRoot (P.ζQ s) (l ^ s) := by
    obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := ⟨s - 1, by omega⟩
    have hpow : ∀ k, P.ζQ (k + 1) ^ l ^ k = P.ζQ 1 := by
      intro k
      induction k with
      | zero => simp
      | succ j ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]
    have h1 : ¬ P.ζQ (m + 1) ^ l ^ m = 1 := by rw [hpow]; exact P.ζQ_one
    have h2 : P.ζQ (m + 1) ^ l ^ (m + 1) = 1 := by
      rw [pow_succ, pow_mul, hpow, P.ζQ_succ, P.ζQ_zero]
    have h3 := orderOf_eq_prime_pow h1 h2
    rw [← h3]
    exact IsPrimitiveRoot.orderOf _
  have hmem : P.ζQ s ∈ Ks K s :=
    (le_sup_right : IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ l ^ s = 1} ≤ Ks K s)
      (IntermediateField.subset_adjoin _ _ hprim.pow_eq_one)
  let Φ : Om l →ₐ[ℚ_[l]] Om l := ((H.W K s LL h).emb i).liftNormal (Om l)
  have hΦ : ∀ x : ↥(K0 K), Φ (x : Om l) = (((H.W K s LL h).emb i x : ↥LL.1) : Om l) := fun x =>
    AlgHom.liftNormal_commutes ((H.W K s LL h).emb i) (Om l) x
  let τ₀ : ↥(Ks K s) →ₐ[ℚ_[l]] Om l := Φ.comp (Ks K s).val
  let τ : ↥(Ks K s) →ₐ[ℚ_[l]] ↥LL.1 := τ₀.codRestrict LL.1.toSubalgebra (hLL τ₀)
  have hτ : ∀ y : ↥(Ks K s), ((τ y : ↥LL.1) : Om l) = Φ (y : Om l) := fun _ => rfl
  refine ⟨τ ⟨P.ζQ s, hmem⟩, τ, ⟨?_, ?_⟩, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    rw [hτ, hxy, hΦ]
  · intro y hy
    congr 1
    exact Subtype.ext hy
  · have h1 : IsPrimitiveRoot (⟨P.ζQ s, hmem⟩ : ↥(Ks K s)) (l ^ s) :=
      IsPrimitiveRoot.of_map_of_injective (f := (Ks K s).val) hprim (Ks K s).val.injective
    exact h1.map_of_injective τ.injective

end GlobalTheory
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct

namespace GlobalTheory.PrismS

variable {l : ℕ} [Fact l.Prime]

abbrev unr (K : FinExt l) : FinExt l :=
  ⟨K0 K, by
    have := K.2
    exact FiniteDimensional.of_injective
      (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective (inf_le_left : K0 K ≤ K.1))⟩

abbrev WK (K : FinExt l) : Type := ↥(OL (unr K))

def embW {K LL : FinExt l} (e : ↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1) : WK K →ₐ[ℤ_[l]] ↥(OL LL) :=
  (e.restrictScalars ℤ_[l]).mapIntegralClosure

theorem embW_injective {K LL : FinExt l} (e : ↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1) : Function.Injective (embW e) :=
  fun _ _ h => Subtype.ext (e.toRingHom.injective (congrArg Subtype.val h))

def letEmb {K LL : FinExt l} {n : ℕ} (emb : ZMod n → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1)) :
    PowerSeries (WK K) →+* LetA ↥(OL LL) n :=
  RingHom.pi fun i => PowerSeries.map (embW (emb i)).toRingHom

theorem letEmb_apply {K LL : FinExt l} {n : ℕ} (emb : ZMod n → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1))
    (x : PowerSeries (WK K)) (i : ZMod n) :
    letEmb emb x i = PowerSeries.map (embW (emb i)).toRingHom x := rfl

end GlobalTheory.PrismS
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory

theorem natCard_algHom_intermediateField_of_range_le {F E A : Type} [Field F] [Field E] [Field A]
    [Algebra F E] [Algebra F A] [FiniteDimensional F E] [Algebra.IsSeparable F E] [IsAlgClosed A]
    (M : IntermediateField F A) (h : ∀ (f : E →ₐ[F] A) (x : E), f x ∈ M) :
    Nat.card (E →ₐ[F] ↥M) = finrank F E := by

  have e : (E →ₐ[F] ↥M) ≃ (E →ₐ[F] A) :=
    { toFun := fun g => M.val.comp g
      invFun := fun f => f.codRestrict M.toSubalgebra (h f)
      left_inv := fun _ => AlgHom.ext fun _ => rfl
      right_inv := fun _ => AlgHom.ext fun _ => rfl }
  rw [Nat.card_congr e]
  exact AlgHom.natCard_of_splits F E A fun _ => IsAlgClosed.splits _

private theorem exists_fd_intermediateField_contains_embeddings (l : ℕ) [Fact l.Prime] (E : Type) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    ∃ N : IntermediateField ℚ_[l] (Om l), FiniteDimensional ℚ_[l] ↥N ∧
      ∀ (f : E →ₐ[ℚ_[l]] Om l) (x : E), f x ∈ N := by
  have hfin : ∀ f : E →ₐ[ℚ_[l]] Om l, FiniteDimensional ℚ_[l] ↥f.fieldRange :=
    fun f => f.toLinearMap.finiteDimensional_range
  exact ⟨⨆ f : E →ₐ[ℚ_[l]] Om l, f.fieldRange,
    IntermediateField.finiteDimensional_iSup_of_finite,
    fun f x => (le_iSup (fun g : E →ₐ[ℚ_[l]] Om l => g.fieldRange) f) ⟨x, rfl⟩⟩

theorem exists_finExt_embedding_splitting (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type)
    [Field LL] [Algebra ℚ_[l] LL] [FiniteDimensional ℚ_[l] LL] :
    ∃ LL' : FinExt l, Nonempty (LL →ₐ[ℚ_[l]] ↥LL'.1) ∧
      Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL'.1) = finrank ℚ_[l] ↥K.1 ∧
      Nat.card (↥(K0 K) →ₐ[ℚ_[l]] ↥LL'.1) = finrank ℚ_[l] ↥(K0 K) := by
  have : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have : FiniteDimensional ℚ_[l] ↥(K0 K) := Module.Finite.left ℚ_[l] ↥(K0 K) ↥K.1
  obtain ⟨N1, hN1, hK1⟩ := exists_fd_intermediateField_contains_embeddings l ↥K.1
  obtain ⟨N0, hN0, hK0⟩ := exists_fd_intermediateField_contains_embeddings l ↥(K0 K)

  let φ : LL →ₐ[ℚ_[l]] Om l := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have : FiniteDimensional ℚ_[l] ↥φ.fieldRange := φ.toLinearMap.finiteDimensional_range

  refine ⟨⟨φ.fieldRange ⊔ N1 ⊔ N0, inferInstance⟩,
    ⟨φ.codRestrict (φ.fieldRange ⊔ N1 ⊔ N0).toSubalgebra fun x => ?_⟩, ?_, ?_⟩
  · exact (le_sup_left.trans le_sup_left : φ.fieldRange ≤ _) ⟨x, rfl⟩
  · exact natCard_algHom_intermediateField_of_range_le _ fun f x =>
      (le_sup_right.trans le_sup_left : N1 ≤ _) (hK1 f x)
  · exact natCard_algHom_intermediateField_of_range_le _ fun f x =>
      (le_sup_right : N0 ≤ _) (hK0 f x)

end GlobalTheory
end

section


theorem _root_.GlobalTheory.T.wittVector_gaussNorm_mul : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] [CharP R l] [PerfectRing R l] (a : R → ℝ), (∀ x, 0 ≤ a x ∧ a x ≤ 1) → a 0 = 0 → a 1 = 1 → (∀ x y, a (x * y) = a x * a y) → (∀ x y, a (x + y) ≤ max (a x) (a y)) → ∀ r : ℝ, 0 < r → r < 1 → ∀ N : WittVector l R → ℝ, (∀ x, N x = ⨆ n : ℕ, a (x.coeff n) ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n) → ∀ x y, N (x * y) = N x * N y := by
  first | exact @GlobalTheory.witt_gaussNorm_mul | exact GlobalTheory.witt_gaussNorm_mul | (intros; apply GlobalTheory.witt_gaussNorm_mul <;> assumption)
end

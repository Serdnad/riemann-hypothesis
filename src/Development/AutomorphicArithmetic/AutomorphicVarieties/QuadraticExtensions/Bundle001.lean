module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.Bundle002
public import Formalism.GaloisCohomology.Statement
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle006
public import Mathlib.Topology.LocallyConstant.Basic
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTameGenAtOfValuationSubring
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle124
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle078
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
public import Mathlib.NumberTheory.Cyclotomic.Gal
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.abProps :
    ∀ (A : AbF) (L : Type) [Field L] [NumberField L], IsAbField A L → IsAbelianGalois ℚ L ∧ Module.finrank ℚ L = A.deg ∧ Nonempty (L →ₐ[ℚ] CyclotomicField A.m ℚ) := by
  intro A L _ _ hA
  obtain ⟨N, hN, j, ζ, hmN, hζ, h⟩ := hA
  haveI := hN
  haveI hcN : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := CyclotomicField.isCyclotomicExtension N ℚ
  haveI hab : IsAbelianGalois ℚ (CyclotomicField N ℚ) :=
    IsCyclotomicExtension.isAbelianGalois {N} ℚ (CyclotomicField N ℚ)
  have hfix : ∀ τ : Gal(CyclotomicField N ℚ/ℚ),
      τ ∈ j.fieldRange.fixingSubgroup ↔ ∀ y : L, τ (j y) = j y := by
    intro τ
    rw [IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro H y
      exact H _ (AlgHom.mem_fieldRange.2 ⟨y, rfl⟩)
    · intro H x hx
      obtain ⟨y, rfl⟩ := AlgHom.mem_fieldRange.1 hx
      exact H y
  have hpow : ∀ τ : Gal(CyclotomicField N ℚ/ℚ), τ ζ = ζ ^ ((hζ.autToPow ℚ τ : ZMod N).val) :=
    fun τ => (IsPrimitiveRoot.autToPow_spec ℚ hζ τ).symm
  have hker : ∀ v : (ZMod N)ˣ, A.ker ((v : ZMod N).val) ↔ ZMod.unitsMap hmN v ∈ A.H := by
    intro v
    have hc : ((ZMod.unitsMap hmN v : (ZMod A.m)ˣ) : ZMod A.m) = (((v : ZMod N).val : ℕ) : ZMod A.m) := by
      rw [ZMod.natCast_val]
      rfl
    constructor
    · rintro ⟨u, hu, hua⟩
      have : u = ZMod.unitsMap hmN v := Units.ext (hua.trans hc.symm)
      rwa [← this]
    · intro hv
      exact ⟨_, hv, hc⟩
  have hinj : Function.Injective (hζ.autToPow ℚ) := hζ.autToPow_injective ℚ
  have hcard : Nat.card Gal(CyclotomicField N ℚ/ℚ) = Nat.card (ZMod N)ˣ :=
    Nat.card_congr (IsCyclotomicExtension.autEquivPow (CyclotomicField N ℚ)
      (Polynomial.cyclotomic.irreducible_rat (Nat.pos_of_neZero N))).toEquiv
  have hsurj : Function.Surjective (hζ.autToPow ℚ) :=
    ((Nat.bijective_iff_injective_and_card _).2 ⟨hinj, hcard⟩).2
  refine ⟨IsAbelianGalois.of_algHom j, ?_, ?_⟩
  · rw [(AlgEquiv.ofInjectiveField j).toLinearEquiv.finrank_eq]
    change Module.finrank ℚ j.fieldRange = _
    rw [IntermediateField.finrank_eq_fixingSubgroup_index]
    have hS : j.fieldRange.fixingSubgroup = (A.H.comap (ZMod.unitsMap hmN)).comap (hζ.autToPow ℚ) := by
      ext τ
      rw [hfix, h τ _ (hpow τ)]
      exact hker _
    rw [hS, Subgroup.index_comap_of_surjective _ hsurj,
      Subgroup.index_comap_of_surjective _ (ZMod.unitsMap_surjective hmN)]
    rfl
  · have hdvd : N / A.m ∣ N := Nat.div_dvd_of_dvd hmN
    have hp0 : N / A.m ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_neZero N) hmN) A.pos).ne'
    have hζm : IsPrimitiveRoot (ζ ^ (N / A.m)) A.m := by
      have := hζ.pow_of_dvd hp0 hdvd
      rwa [Nat.div_div_self hmN (NeZero.ne N)] at this
    haveI : NeZero A.m := ⟨A.pos.ne'⟩
    haveI hcm : IsCyclotomicExtension {A.m} ℚ (CyclotomicField A.m ℚ) :=
      CyclotomicField.isCyclotomicExtension A.m ℚ
    haveI : IsCyclotomicExtension {A.m} ℚ (IntermediateField.adjoin ℚ {ζ ^ (N / A.m)}) :=
      hζm.intermediateField_adjoin_isCyclotomicExtension ℚ
    have hMC : j.fieldRange ≤ IntermediateField.adjoin ℚ {ζ ^ (N / A.m)} := by
      rw [← IsGalois.fixedField_fixingSubgroup (IntermediateField.adjoin ℚ {ζ ^ (N / A.m)}),
        IntermediateField.le_iff_le]
      intro τ hτ
      rw [hfix, h τ _ (hpow τ)]
      rw [IntermediateField.mem_fixingSubgroup_iff] at hτ
      have h1 : τ (ζ ^ (N / A.m)) = ζ ^ (N / A.m) :=
        hτ _ (IntermediateField.mem_adjoin_simple_self ℚ _)
      rw [map_pow, hpow τ, ← pow_mul, mul_comm, pow_mul] at h1
      generalize ((hζ.autToPow ℚ τ : ZMod N)).val = a at h1 ⊢
      have hfo : IsOfFinOrder (ζ ^ (N / A.m)) :=
        isOfFinOrder_iff_pow_eq_one.2 ⟨A.m, A.pos, hζm.pow_eq_one⟩
      have h2 : a ≡ 1 [MOD A.m] := by
        rw [hζm.eq_orderOf]
        exact hfo.pow_eq_pow_iff_modEq.1 (by rw [pow_one]; exact h1)
      refine ⟨1, one_mem _, ?_⟩
      rw [Units.val_one, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
      exact h2.symm
    exact ⟨(IsCyclotomicExtension.algEquiv {A.m} ℚ (IntermediateField.adjoin ℚ {ζ ^ (N / A.m)})
      (CyclotomicField A.m ℚ)).toAlgHom.comp
        ((IntermediateField.inclusion hMC).comp (AlgEquiv.ofInjectiveField j).toAlgHom)⟩
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.abExists :
    ∀ A : AbF, ∃ (L : Type) (_ : Field L) (_ : NumberField L), IsAbField A L := by
  intro A
  obtain ⟨L, hF, hN, h, -⟩ := UpperTheory.V.exists_numberField_isAbField_finrank_eq_deg A
  exact ⟨L, hF, hN, h⟩
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.subqLen :
    ∀ (l : ℕ) [Fact l.Prime] (N : Submodule ℤ_[l] (QZ l)) (Q P : Type) [AddCommGroup Q] [Module ℤ_[l] Q] [AddCommGroup P] [Module ℤ_[l] P] (π : N →ₗ[ℤ_[l]] Q) (j : P →ₗ[ℤ_[l]] Q),
      Function.Surjective π → Function.Injective j → (∀ x : P, (l : ℤ_[l]) • x = 0) → Module.length ℤ_[l] P ≤ 1 := by
  intro l _ N Q P _ _ _ _ π j hπ hj htor
  have key : ∀ a b : QZ l, ∃ c : ℤ_[l], a = c • b ∨ b = c • a := by
    intro a b
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (ZlSub l) a
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (ZlSub l) b
    have step : ∀ x y : ℚ_[l], ‖x‖ ≤ ‖y‖ → ∃ c : ℤ_[l], x = c • y := by
      intro x y h
      by_cases hy : y = 0
      · subst hy
        refine ⟨0, ?_⟩
        rw [norm_zero] at h
        rw [norm_le_zero_iff.mp h, zero_smul]
      · refine ⟨⟨x / y, ?_⟩, ?_⟩
        · rw [PadicInt.mem_subring_iff, norm_div]
          exact div_le_one_of_le₀ h (norm_nonneg _)
        · show x = (x / y) * y
          rw [div_mul_cancel₀ _ hy]
    rcases le_total ‖x‖ ‖y‖ with h | h
    · obtain ⟨c, hc⟩ := step x y h
      exact ⟨c, Or.inl (by rw [hc]; rfl)⟩
    · obtain ⟨c, hc⟩ := step y x h
      exact ⟨c, Or.inr (by rw [hc]; rfl)⟩
  have hQ : ∀ q1 q2 : Q, ∃ c : ℤ_[l], q1 = c • q2 ∨ q2 = c • q1 := by
    intro q1 q2
    obtain ⟨n1, rfl⟩ := hπ q1
    obtain ⟨n2, rfl⟩ := hπ q2
    obtain ⟨c, h | h⟩ := key (n1 : QZ l) (n2 : QZ l)
    · refine ⟨c, Or.inl ?_⟩
      rw [← map_smul]
      congr 1
      exact Subtype.ext h
    · refine ⟨c, Or.inr ?_⟩
      rw [← map_smul]
      congr 1
      exact Subtype.ext h
  have hP : ∀ x y : P, x ≠ 0 → y ∈ Submodule.span ℤ_[l] {x} := by
    intro x y hx
    obtain ⟨c, h | h⟩ := hQ (j y) (j x)
    · rw [← map_smul] at h
      rw [hj h]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
    · rw [← map_smul] at h
      have hxy := hj h
      by_cases hc : IsUnit c
      · obtain ⟨u, rfl⟩ := hc
        have hy : y = ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) • x := by
          rw [hxy, smul_smul, Units.inv_mul, one_smul]
        rw [hy]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
      · exfalso
        have hn : ‖c‖ < 1 := PadicInt.mem_nonunits.mp hc
        obtain ⟨d, rfl⟩ := (PadicInt.norm_lt_one_iff_dvd c).mp hn
        apply hx
        rw [hxy, mul_comm, mul_smul, htor, smul_zero]
  rcases subsingleton_or_nontrivial P with hsub | hnt
  · rw [Module.length_eq_zero]
    exact zero_le
  · haveI : IsSimpleModule ℤ_[l] P := by
      rw [isSimpleModule_iff]
      refine IsSimpleOrder.mk (fun S => ?_)
      by_cases hS : S = ⊥
      · exact Or.inl hS
      · right
        obtain ⟨x, hxS, hx0⟩ := (Submodule.ne_bot_iff S).mp hS
        rw [eq_top_iff]
        intro y _
        exact (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hxS)) (hP x y hx0)
    rw [Module.length_eq_one]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.qzEnd :
    ∀ (l : ℕ) [Fact l.Prime] (f : QZ l →ₗ[ℤ_[l]] QZ l), ∃ c : ℤ_[l], ∀ x, f x = c • x := by
  intro l _ f
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hz : ∀ q : ℚ_[l], QZ.mk l q = 0 ↔ ‖q‖ ≤ 1 := by
    intro q
    show (Submodule.Quotient.mk q : ℚ_[l] ⧸ ZlSub l) = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero]
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro h
      exact ⟨⟨q, h⟩, rfl⟩
  set x : ℕ → QZ l := fun k => QZ.mk l (((l : ℚ_[l]) ^ k)⁻¹) with hx
  have hA : ∀ (c : ℤ_[l]) (k : ℕ), c • x k = 0 ↔ ‖c‖ ≤ (l : ℝ) ^ (-(k : ℤ)) := by
    intro c k
    show QZ.mk l ((c : ℚ_[l]) * ((l : ℚ_[l]) ^ k)⁻¹) = 0 ↔ _
    have hpos : (0 : ℝ) < (l : ℝ) ^ (-(k : ℤ)) := by positivity
    rw [hz, norm_mul, norm_inv, Padic.norm_p_pow, mul_inv_le_iff₀ hpos, one_mul]
    exact Iff.rfl
  have hC : ∀ (k : ℕ) (y : QZ l), (l ^ k) • y = 0 → ∃ a : ℤ_[l], y = a • x k := by
    intro k y hy
    obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective (ZlSub l) y
    have h1 : QZ.mk l ((l : ℚ_[l]) ^ k * q) = 0 := by
      rw [← hy]
      show _ = (Submodule.Quotient.mk ((l ^ k) • q) : ℚ_[l] ⧸ ZlSub l)
      rw [nsmul_eq_mul]
      push_cast
      rfl
    rw [hz] at h1
    refine ⟨⟨(l : ℚ_[l]) ^ k * q, h1⟩, ?_⟩
    show QZ.mk l q = QZ.mk l (((l : ℚ_[l]) ^ k * q) * ((l : ℚ_[l]) ^ k)⁻¹)
    congr 1
    field_simp
  have hstep : ∀ k, x k = (l : ℤ_[l]) • x (k + 1) := by
    intro k
    show QZ.mk l (((l : ℚ_[l]) ^ k)⁻¹) = QZ.mk l ((l : ℚ_[l]) * ((l : ℚ_[l]) ^ (k + 1))⁻¹)
    congr 1
    rw [pow_succ]
    field_simp
  have hkill : ∀ k, (l ^ k) • x k = 0 := by
    intro k
    rw [← Nat.cast_smul_eq_nsmul ℤ_[l], hA]
    push_cast
    rw [PadicInt.norm_p_pow]
  have hex : ∀ k, ∃ a : ℤ_[l], f (x k) = a • x k := by
    intro k
    apply hC
    rw [← map_nsmul, hkill, map_zero]
  choose a ha using hex
  have hdiff : ∀ k, ‖a (k + 1) - a k‖ ≤ (l : ℝ) ^ (-(k : ℤ)) := by
    intro k
    rw [← hA, sub_smul, sub_eq_zero, ← ha k, hstep k, map_smul, ha (k + 1)]
    exact smul_comm _ _ _
  have hr : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl
  have hcs : CauchySeq a := by
    refine cauchySeq_of_le_geometric ((l : ℝ)⁻¹) 1 hr (fun n => ?_)
    rw [dist_comm, dist_eq_norm, one_mul, inv_pow, ← zpow_natCast, ← zpow_neg]
    exact hdiff n
  obtain ⟨c, hc⟩ := cauchySeq_tendsto_of_complete hcs
  have hmono : ∀ k m, k ≤ m → ‖a m - a k‖ ≤ (l : ℝ) ^ (-(k : ℤ)) := by
    intro k m hkm
    induction m, hkm using Nat.le_induction with
    | base =>
      rw [sub_self, norm_zero]
      positivity
    | succ m hkm ih =>
      have := PadicInt.nonarchimedean (a (m + 1) - a m) (a m - a k)
      rw [sub_add_sub_cancel] at this
      refine this.trans (max_le ((hdiff m).trans ?_) ih)
      exact zpow_le_zpow_right₀ hl.le (by omega)
  have hck : ∀ k, ‖c - a k‖ ≤ (l : ℝ) ^ (-(k : ℤ)) := by
    intro k
    have ht : Filter.Tendsto (fun m => ‖a m - a k‖) Filter.atTop (nhds ‖c - a k‖) :=
      (hc.sub_const (a k)).norm
    exact le_of_tendsto ht (Filter.eventually_atTop.2 ⟨k, fun m hm => hmono k m hm⟩)
  have hfx : ∀ k, f (x k) = c • x k := by
    intro k
    have := (hA (c - a k) k).2 (hck k)
    rw [sub_smul, sub_eq_zero] at this
    rw [this, ha k]
  refine ⟨c, fun y => ?_⟩
  obtain ⟨k, hk⟩ := (qzBasic l).2.1 y
  obtain ⟨b, rfl⟩ := hC k y hk
  rw [map_smul, hfx, smul_comm]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.tameGen :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ¬ A.valuation (l : Ω) < 1 →
      ∃ γ : Ine (F := F) A, ∀ φ : Ine (F := F) A → ZMod l, IsLocallyConstant φ → (∀ a b, φ (a * b) = φ a + φ b) → φ γ = 0 → ∀ σ, φ σ = 0 := by
  intro F Ω _ _ _ _ _ l _ A hvl
  obtain ⟨γ, hγ⟩ := GlobalTheory.TameInertiaGen.exists_tameGenAt_of_valuationSubring (E := F) A
  refine ⟨⟨γ, hγ.1⟩, fun t ht hm h0 => ?_⟩
  have hl : l.Prime := Fact.out
  have t1 : t 1 = 0 := by simpa using hm 1 1
  have tinv : ∀ a, t a⁻¹ = -t a := fun a => by
    have := hm a⁻¹ a
    rw [inv_mul_cancel, t1] at this
    exact eq_neg_of_add_eq_zero_left this.symm
  have tpow : ∀ a (n : ℕ), t (a ^ n) = n • t a := fun a n => by
    induction n with
    | zero => simp [t1]
    | succ n ih => rw [pow_succ, hm, ih, succ_nsmul]
  have hvl1 : A.valuation (l : Ω) = 1 :=
    le_antisymm ((A.valuation_le_one_iff _).mpr (natCast_mem A l)) (not_lt.mp hvl)
  have : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  let T : Subgroup (Ine (F := F) A) :=
    { carrier := t ⁻¹' {0}
      one_mem' := t1
      mul_mem' := fun {a b} ha hb => by
        show t (a * b) = 0
        rw [hm, show t a = 0 from ha, show t b = 0 from hb, add_zero]
      inv_mem' := fun {a} ha => by
        show t a⁻¹ = 0
        rw [tinv, show t a = 0 from ha, neg_zero] }
  have ho : IsOpen (t ⁻¹' {0}) := ht _
  refine GlobalTheory.TameCharUnique.mem_of_tameGen hγ T (T.isClosed_of_isOpen ho) h0 fun σ hσ => ?_
  obtain ⟨V, hV, hVU⟩ := isOpen_induced_iff.1 ho
  have hV1 : (1 : G F Ω) ∈ V := by
    have : (1 : Ine (F := F) A) ∈ t ⁻¹' {0} := t1
    rw [← hVU] at this
    exact this
  obtain ⟨L, hL, hsub⟩ := (krullTopology_mem_nhds_one_iff F Ω _).mp (hV.mem_nhds hV1)
  have hidx : L.fixingSubgroup.index ≠ 0 := by
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact Module.finrank_pos.ne'
  obtain ⟨N, hN, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hidx σ.1
  obtain ⟨a, m, hm', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' l hl.ne_one
  have hτ : σ.1 ^ m ∈ L.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff] at hmem ⊢
    intro x hx
    refine GlobalTheory.WildInertiaChar.fixed_of_pow_fixed A (σ.1 ^ m)
      (GlobalTheory.WildInertiaChar.wild_pow A σ.1 hσ m) (l ^ a) ?_ x ?_
    · rw [Nat.cast_pow, map_pow, hvl1, one_pow]; exact lt_irrefl _
    · rw [← pow_mul, mul_comm]; exact hmem x hx
  have h2 : σ ^ m ∈ t ⁻¹' {0} := by
    rw [← hVU]
    exact hsub hτ
  have h4 : t (σ ^ m) = 0 := h2
  rw [tpow, nsmul_eq_mul] at h4
  exact (mul_eq_zero.1 h4).resolve_left fun h => hm' ((ZMod.natCast_eq_zero_iff m l).1 h)
end

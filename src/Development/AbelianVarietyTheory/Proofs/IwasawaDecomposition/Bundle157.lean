module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle416
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.PicardGroup
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle064
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle074
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle065
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle063
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle061
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle146
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle072
public import Formalism.LocalToGlobal.Columns.Bundle010
public import Formalism.LocalToGlobal.Columns.Bundle009
public import Formalism.LocalToGlobal.HermitianForms.Bundle002
public import Formalism.LocalToGlobal.Columns.RecLevelLoc
public import Formalism.LocalToGlobal.Columns.Bundle017
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
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.GaloisValuations.GlobalB
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle080
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle002
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsDiscriminantTwelfthRootOfIdealLatticeIffDelta1
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.WeilSurj

open GlobalTheory.WeilRestrict Polynomial

theorem card_le_of_forall_pow_eq {F : Type*} [Field F] [Finite F] {m : ℕ} (hm : 1 < m)
    (h : ∀ x : F, x ^ m = x) : Nat.card F ≤ m := by
  classical
  haveI := Fintype.ofFinite F
  have hdeg : (X : F[X]).natDegree < (X ^ m : F[X]).natDegree := by
    rw [natDegree_X, natDegree_X_pow]; exact hm
  have hp : (X ^ m - X : F[X]) ≠ 0 := by
    intro h0
    have := congrArg natDegree h0
    rw [natDegree_sub_eq_left_of_natDegree_lt hdeg, natDegree_X_pow, natDegree_zero] at this
    omega
  have hsub : (Finset.univ : Finset F) ⊆ (X ^ m - X : F[X]).roots.toFinset := by
    intro x _
    rw [Multiset.mem_toFinset, mem_roots hp, IsRoot.def]
    simp [h x]
  calc Nat.card F = (Finset.univ : Finset F).card := by rw [Nat.card_eq_fintype_card, Finset.card_univ]
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Multiset.toFinset_card_le _
    _ ≤ _ := card_roots' _
    _ = m := by rw [natDegree_sub_eq_left_of_natDegree_lt hdeg, natDegree_X_pow]

theorem exists_weil_of_fixes : ∀ (E K Ω : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra E K] [IsScalarTower E K Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (W : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A w) (h' : IsPlaceOver A W) (σ : Weil h), (∀ x : K, (σ : G E Ω) (algebraMap K Ω x) = algebraMap K Ω x) → ∃ τ : Weil h', ∀ z : Ω, (σ : G E Ω) z = (τ : G K Ω) z := by
  intro E K Ω _ _ _ _ _ _ _ _ _ _ _ A w W h h' σ hσ
  obtain ⟨f, hf⟩ := normV_eq_pow_of_isPlaceOver h h'
  have hq1 : 1 < normV w := one_lt_normV w
  have hf0 : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · have := one_lt_normV W
      rw [hf, h0, pow_zero] at this
      exact absurd this (lt_irrefl 1)
    · exact h0
  have hφdeg : deg (resWeil h h' (frob h')) = f := by
    have h1 : ActsAs A (normV w ^ f) (frob h' : G K Ω) 1 0 := by
      rw [← hf]; exact actsAs_one_iff.mpr isFrob_frob
    have h2 := actsAs_resG (K := E) h1
    have := deg_eq (σ := resWeil h h' (frob h')) h2
    simpa using this
  obtain ⟨k, r, hr0, hrf, hdr⟩ : ∃ k r : ℤ, 0 ≤ r ∧ r < f ∧ r + f * k = deg σ :=
    ⟨deg σ / f, deg σ % f, Int.emod_nonneg _ (by exact_mod_cast hf0.ne'),
      Int.emod_lt_of_pos _ (by exact_mod_cast hf0), Int.emod_add_mul_ediv _ _⟩
  set σ' : Weil h := σ * (resWeil h h' (frob h' ^ k))⁻¹ with hσ'
  have hdeg' : deg σ' = r := by
    rw [hσ', deg_mul, deg_inv, map_zpow, deg_zpow, hφdeg]
    linear_combination -hdr
  have hfix' : ∀ x : K, (σ' : G E Ω) (algebraMap K Ω x) = algebraMap K Ω x := by
    intro x
    rw [hσ', Subgroup.coe_mul, AlgEquiv.mul_apply, ← map_inv, resWeil_apply, AlgEquiv.commutes, hσ]
  have hr : r = 0 := by
    by_contra hne
    have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hne)
    set n := r.toNat with hn'
    have hn : (n : ℤ) = r := Int.toNat_of_nonneg hr0
    have hact := actsAs_of_deg (σ := σ') (a := n) (b := 0) (by rw [hdeg', hn]; simp)
    have hmem : ∀ x : 𝓞 K, x ^ (normV w ^ n) - x ∈ W.asIdeal := by
      intro x
      rw [← h' _]
      have hx : A.valuation (algebraMap K Ω x) ≤ 1 :=
        (A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A (map_isIntegral_int (algebraMap K Ω) x.isIntegral_coe))
      have := hact.2 _ hx
      rw [hfix', pow_zero, pow_one, Valuation.map_sub_swap] at this
      have e : algebraMap K Ω ((x ^ (normV w ^ n) - x : 𝓞 K) : K) =
          (algebraMap K Ω x) ^ (normV w ^ n) - algebraMap K Ω x := by simp
      rw [e]; exact this
    haveI : W.asIdeal.IsMaximal := W.isMaximal
    letI : Field (𝓞 K ⧸ W.asIdeal) := Ideal.Quotient.field _
    haveI : Finite (𝓞 K ⧸ W.asIdeal) := W.asIdeal.finiteQuotientOfFreeOfNeBot W.ne_bot
    have hall : ∀ y : 𝓞 K ⧸ W.asIdeal, y ^ (normV w ^ n) = y := by
      intro y
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [← map_pow, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
      exact hmem x
    have hn0 : n ≠ 0 := by omega
    have hcard := card_le_of_forall_pow_eq (one_lt_pow₀ hq1 hn0) hall
    have hQ : Nat.card (𝓞 K ⧸ W.asIdeal) = normV w ^ f := hf
    rw [hQ] at hcard
    have : normV w ^ n < normV w ^ f := Nat.pow_lt_pow_right hq1 (by omega)
    omega
  have hine : (σ' : G E Ω) ∈ Ine (F := E) A := deg_eq_zero_iff.mp (by rw [hdeg', hr])
  let τ0 : G K Ω := { (σ' : G E Ω).toRingEquiv with commutes' := fun x => hfix' x }
  have hτ0 : τ0 ∈ Ine (F := K) A := hine
  refine ⟨ineIncl h' ⟨τ0, hτ0⟩ * frob h' ^ k, fun z => ?_⟩
  have key : (((resWeil h h' (frob h' ^ k))⁻¹ : Weil h) : G E Ω)
      (((frob h' ^ k : Weil h') : G K Ω) z) = z := by
    rw [← map_inv, resWeil_apply, ← AlgEquiv.mul_apply, ← Subgroup.coe_mul, inv_mul_cancel,
      Subgroup.coe_one, AlgEquiv.one_apply]
  show (σ : G E Ω) z = (σ' : G E Ω) (((frob h' ^ k : Weil h') : G K Ω) z)
  rw [hσ', Subgroup.coe_mul, AlgEquiv.mul_apply, key]

end GlobalTheory.WeilSurj
end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

namespace GlobalTheory.NormCompat

theorem val_div_sub_one_le {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {a c : K}
    (hc : c ≠ 0) {N m : ℕ} (hm : (WithZero.log (w.valuation K c)).natAbs ≤ m)
    (h : w.valuation K (a - c) ≤ WithZero.exp (-((N : ℤ) + m))) :
    w.valuation K (a / c - 1) ≤ WithZero.exp (-(N : ℤ)) := by
  have hv : w.valuation K c ≠ 0 := (Valuation.ne_zero_iff _).mpr hc
  rw [div_sub_one hc, map_div₀, ← WithZero.exp_log hv, div_le_iff₀ (by simp), ← WithZero.exp_add]
  refine h.trans (WithZero.exp_le_exp.mpr ?_)
  have : -(m : ℤ) ≤ WithZero.log (w.valuation K c) := by omega
  omega

theorem val_le_of_le {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {x : K} {N N' : ℤ}
    (h : w.valuation K x ≤ WithZero.exp (-N)) (hN : N' ≤ N) : w.valuation K x ≤ WithZero.exp (-N') :=
  h.trans (WithZero.exp_le_exp.mpr (by omega))

theorem res_art_eq_art_norm : ∀ (E Ω : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (K : IntermediateField E Ω) [FiniteDimensional E K] [NumberField K] [IsAlgClosure K Ω]
    (art : Ideles E →* Gab E Ω) (artK : Ideles K →* Gab K Ω), IsGlobalArtin art → IsGlobalArtin artK →
    ∀ (v : HeightOneSpectrum (𝓞 E)) (W : HeightOneSpectrum (𝓞 K)),
      W.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal →
      (∀ W' : HeightOneSpectrum (𝓞 K), W'.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal → W' = W) →
      ∀ (y : Kˣ) (τ : Formalism.ConjugateSelfDual.G K Ω),
        toAb K Ω τ = artK (localIdele K W (Units.map (algebraMap K (W.adicCompletion K)).toMonoidHom y)) →
        toAb E Ω (τ.restrictScalars E) =
          art (localIdele E v (Units.map (algebraMap E (v.adicCompletion E)).toMonoidHom
            (Units.map (Algebra.norm E (S := K)) y))) := by
  intro E Ω _ _ _ _ _ _ K _ _ _ art artK ha haK v W hW hWu y τ hτ
  classical
  haveI : IsTotallyComplex K := GlobalTheory.T.isTotallyComplex_of_algebra_of_isTotallyComplex E K
  haveI : IsClosed ((commutator (Formalism.ConjugateSelfDual.G E Ω)).topologicalClosure : Set (Formalism.ConjugateSelfDual.G E Ω)) :=
    Subgroup.isClosed_topologicalClosure _
  let r : Formalism.ConjugateSelfDual.G K Ω →* Gab E Ω := (toAb E Ω).comp (AlgEquiv.restrictScalarsHom E)
  have hr : Continuous r := QuotientGroup.continuous_mk.comp (GlobalTheory.T.continuous_restrictScalarsHom' E Ω K)
  let ρ : Gab K Ω →* Gab E Ω := liftAb r hr
  have hρ : ∀ σ : Formalism.ConjugateSelfDual.G K Ω, ρ (toAb K Ω σ) = toAb E Ω (σ.restrictScalars E) := fun σ => rfl
  have hρc : Continuous ρ := continuous_liftAb r hr
  let NK : Kˣ →* Eˣ := Units.map (Algebra.norm E (S := K))
  have hdE : ∀ k : Eˣ, art (diagUnits E k) = 1 := fun k => by
    have hk : diagUnits E k ∈ art.ker := by
      rw [ha.ker]
      exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left ⟨k, rfl⟩)
    exact hk
  have hdK : ∀ k : Kˣ, artK (diagUnits K k) = 1 := fun k => by
    have hk : diagUnits K k ∈ artK.ker := by
      rw [haK.ker]
      exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left ⟨k, rfl⟩)
    exact hk
  show toAb E Ω (τ.restrictScalars E) = art (locUnit E v (NK y))
  rw [← hρ, hτ]
  change ρ (artK (locUnit K W y)) = art (locUnit E v (NK y))
  rw [← div_eq_one]
  refine GlobalTheory.T.absoluteGaloisAbelianization_eq_one_of_mem_open_subgroups E Ω _ fun U hU => ?_
  let χ : Gab E Ω →* Gab E Ω ⧸ U := QuotientGroup.mk' U
  suffices h : χ (ρ (artK (locUnit K W y))) = χ (art (locUnit E v (NK y))) by
    have h2 : χ (ρ (artK (locUnit K W y)) / art (locUnit E v (NK y))) = 1 := by
      rw [map_div, h, div_self']
    exact (QuotientGroup.eq_one_iff _).mp h2
  let ψ1 : Ideles K →* Gab E Ω ⧸ U := χ.comp (ρ.comp artK)
  let ψ2 : Ideles E →* Gab E Ω ⧸ U := χ.comp art
  have hker1 : (ψ1.ker : Set (Ideles K)) = (ρ.comp artK) ⁻¹' U := by
    ext x; simp [ψ1, χ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  have hker2 : (ψ2.ker : Set (Ideles E)) = art ⁻¹' U := by
    ext x; simp [ψ2, χ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  have ho1 : IsOpen (ψ1.ker : Set (Ideles K)) := by
    rw [hker1]; exact hU.preimage (hρc.comp haK.quot.continuous)
  have ho2 : IsOpen (ψ2.ker : Set (Ideles E)) := by
    rw [hker2]; exact hU.preimage ha.quot.continuous

  obtain ⟨SE, ME, hvS, hSu, hSc⟩ := GlobalTheory.T.isOpen_idele_subgroup_contains_congruence_units E ψ2.ker ho2 {v}
  have hvSE : v ∈ SE := hvS (Finset.mem_singleton_self v)
  obtain ⟨TSK, hTSK⟩ := GlobalTheory.T.exists_finset_places_over_finset_places E K SE
  have hWT : W ∈ TSK := (hTSK W).mpr ⟨v, hvSE, hW⟩
  obtain ⟨MainNotions, MK, hTS, -, hSKc⟩ := GlobalTheory.T.isOpen_idele_subgroup_contains_congruence_units K ψ1.ker ho1 TSK
  choose M' hM' using fun v' : HeightOneSpectrum (𝓞 E) => GlobalTheory.T.norm_close_to_one_of_close_above_place E K v' ME
  let M'' : ℕ := SE.sup M'
  let m : ℕ := (WithZero.log (W.valuation K (y : K))).natAbs
  obtain ⟨a, ha'⟩ := GlobalTheory.T.exists_approx_finite_places_numberField_target K TSK (fun w => if w = W then (y : K) else 1) (MK + M'' + m + 1)
  have haW : W.valuation K (a - y) ≤ WithZero.exp (-(((MK + M'' + 1 : ℕ) : ℤ) + m)) := by
    have := ha' W hWT
    rw [ite_eq_left rfl] at this
    exact val_le_of_le W this (by push_cast; omega)
  have hz : W.valuation K (a / y - 1) ≤ WithZero.exp (-((MK + M'' + 1 : ℕ) : ℤ)) :=
    val_div_sub_one_le W y.ne_zero le_rfl haW
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_div, zero_sub, Valuation.map_neg, map_one, ← WithZero.exp_zero, WithZero.exp_le_exp] at hz
    omega
  let au : Kˣ := Units.mk0 a ha0
  let zu : Kˣ := au / y
  have hzu : (zu : K) = a / y := by simp [zu, au]
  have hauy : au = y * zu := by simp [zu]

  have F1 : ψ1 (locUnit K W au) = ψ1 (locUnit K W y) := by
    have hm : locUnit K W zu ∈ ψ1.ker := hSKc W (hTS hWT) zu (by
      rw [hzu]; exact val_le_of_le W hz (by push_cast; omega))
    rw [hauy, map_mul, map_mul, MonoidHom.mem_ker.mp hm, mul_one]

  have F2 : ψ2 (locUnit E v (NK au)) = ψ2 (locUnit E v (NK y)) := by
    have hm : locUnit E v (NK zu) ∈ ψ2.ker := hSc v hvSE (NK zu) (by
      refine hM' v (zu : K) fun w hw => ?_
      rw [hWu w hw, hzu]
      exact val_le_of_le W hz (by
        have : M' v ≤ M'' := Finset.le_sup hvSE
        push_cast; omega))
    rw [hauy, map_mul, map_mul, map_mul, MonoidHom.mem_ker.mp hm, mul_one]

  have F3 : ∀ w ∈ TSK, w ≠ W → ψ1 (locUnit K w au) = 1 := fun w hw hne => by
    have := ha' w hw
    rw [ite_eq_right hne] at this
    exact MonoidHom.mem_ker.mp (hSKc w (hTS hw) au (val_le_of_le w this (by push_cast; omega)))
  have F4 : ∀ v' ∈ SE, v' ≠ v → ψ2 (locUnit E v' (NK au)) = 1 := fun v' hv' hne => by
    refine MonoidHom.mem_ker.mp (hSc v' hv' (NK au) ?_)
    refine hM' v' (au : K) fun w hw => ?_
    have hwT : w ∈ TSK := (hTSK w).mpr ⟨v', hv', hw⟩
    have hwW : w ≠ W := by
      rintro rfl
      exact hne (HeightOneSpectrum.ext (hw.symm.trans hW))
    have := ha' w hwT
    rw [ite_eq_right hwW] at this
    exact val_le_of_le w this (by
      have : M' v' ≤ M'' := Finset.le_sup hv'
      push_cast; omega)

  have hunitE : ∀ v' ∉ SE, ∀ x, IsUnitAt v' x → ψ2 (localIdele E v' x) = 1 := fun v' hv' x hx =>
    MonoidHom.mem_ker.mp (hSu v' hv' x hx)
  have hchi := fun (v' : HeightOneSpectrum (𝓞 E)) (hv' : v' ∉ SE) (w : HeightOneSpectrum (𝓞 K))
      (hw : w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v'.asIdeal) =>
    GlobalTheory.T.character_globalArtin_units_trivial_uniformiser_power E Ω K art artK ha haK ρ hρ (Gab E Ω ⧸ U) χ v' w hw (hunitE v' hv')
  obtain ⟨TK, TE, hTK1, hTK2, hTE1, hTE2, hprod⟩ := GlobalTheory.T.prod_localValues_global_over_places_above E K (Gab E Ω ⧸ U) ψ1 ψ2 SE hunitE
    (fun v' hv' w hw => (hchi v' hv' w hw).1) (fun v' hv' w hw => (hchi v' hv' w hw).2) au

  have hPK : (∏ w ∈ TK, ψ1 (locUnit K w au)) * ψ1 (locUnit K W au) = 1 := by
    have hdisj : Disjoint TK TSK := by
      rw [Finset.disjoint_left]
      intro w h1 h2
      obtain ⟨v', hv', e⟩ := (hTSK w).mp h2
      exact hTK1 w h1 v' hv' e
    have h := GlobalTheory.T.prod_idele_char_global_unit_eq_one K (Gab E Ω ⧸ U) ψ1 ho1 (fun k => by simp [ψ1, hdK]) au (TK ∪ TSK) fun w hw => by
      rw [Finset.mem_union, not_or] at hw
      refine hTK2 w hw.1 fun v' hv' e => hw.2 ((hTSK w).mpr ⟨v', hv', e⟩)
    rw [Finset.prod_union hdisj, Finset.prod_eq_single_of_mem W hWT F3] at h
    exact h
  have hPE : (∏ v' ∈ TE, ψ2 (locUnit E v' (NK au))) * ψ2 (locUnit E v (NK au)) = 1 := by
    have hdisj : Disjoint TE SE := by
      rw [Finset.disjoint_left]
      intro v' h1 h2
      exact hTE1 v' h1 h2
    have h := GlobalTheory.T.prod_idele_char_global_unit_eq_one E (Gab E Ω ⧸ U) ψ2 ho2 (fun k => by simp [ψ2, hdE]) (NK au) (TE ∪ SE) fun v' hv' => by
      rw [Finset.mem_union, not_or] at hv'
      exact hTE2 v' hv'.1 hv'.2
    rw [Finset.prod_union hdisj, Finset.prod_eq_single_of_mem v hvSE F4] at h
    exact h
  have key : ψ1 (locUnit K W au) = ψ2 (locUnit E v (NK au)) := by
    rw [← hprod] at hPE
    exact mul_left_cancel (hPK.trans hPE.symm)
  show ψ1 (locUnit K W y) = ψ2 (locUnit E v (NK y))
  rw [← F1, key, F2]

end GlobalTheory.NormCompat
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.LevStd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem gloRho_eq_of_compat (v : HeightOneSpectrum (𝓞 F))
    (spl : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (halg : ∀ a : v.adicCompletion F, spl ((1 : E) ⊗ₜ[F] a) = (a, a)) (w : Pl E) (e : (𝓞 E ⧸ w.asIdeal) ≃+* kv F v)
    (he : ∀ z : Formalism.L2.Herm.intAf F E, ∃ hz : gloPhi v spl (prV (E := E) v z.1) ∈ v.adicCompletionIntegers F,
      IsLocalRing.residue (v.adicCompletionIntegers F) ⟨_, hz⟩ = e (resS F w z)) (z : Formalism.L2.Herm.intAf F E) :
    gloRho v spl halg z = e (resS F w z) := by
  obtain ⟨hz, h⟩ := he z
  rw [gloRho_apply]
  exact h

theorem gloRho_zero_of_compat (v : HeightOneSpectrum (𝓞 F))
    (spl : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (halg : ∀ a : v.adicCompletion F, spl ((1 : E) ⊗ₜ[F] a) = (a, a)) (w : Pl E) (e : (𝓞 E ⧸ w.asIdeal) ≃+* kv F v)
    (he : ∀ z : Formalism.L2.Herm.intAf F E, ∃ hz : gloPhi v spl (prV (E := E) v z.1) ∈ v.adicCompletionIntegers F,
      IsLocalRing.residue (v.adicCompletionIntegers F) ⟨_, hz⟩ = e (resS F w z)) :
    ∀ a ∈ w.asIdeal, gloRho v spl halg (oToS F E a) = 0 := by
  intro a ha
  rw [gloRho_eq_of_compat v spl halg w e he, resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]

theorem gloE_eq_of_compat (v : HeightOneSpectrum (𝓞 F))
    (spl : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (halg : ∀ a : v.adicCompletion F, spl ((1 : E) ⊗ₜ[F] a) = (a, a)) (w : Pl E) (e : (𝓞 E ⧸ w.asIdeal) ≃+* kv F v)
    (he : ∀ z : Formalism.L2.Herm.intAf F E, ∃ hz : gloPhi v spl (prV (E := E) v z.1) ∈ v.adicCompletionIntegers F,
      IsLocalRing.residue (v.adicCompletionIntegers F) ⟨_, hz⟩ = e (resS F w z)) (t : kP w) :
    gloE v spl halg w (gloRho_zero_of_compat v spl halg w e he) t = e t := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective t
  rw [← resS_oToS (F := F), gloE_resS, gloRho_eq_of_compat v spl halg w e he]

end GlobalTheory.Mem.LevStd


open GlobalTheory.Mem.LevStd in
theorem GlobalTheory.Mem.LevStd.levU_prod_glevH : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (HeightOneSpectrum (𝓞 E))) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (gp : Fin 2 → ℕ) (Jm : Matrix (Fin n) (Fin n) E) (S : StepLevel F E hc.sig Jm T f bad) (G : GLoc F E hc.sig gp) (Hw : ∀ w : SG, Subgroup (GL (Fin n) (𝓞 E ⧸ w.1.asIdeal))) (lamw : ∀ w, Hw w →* ℂˣ) (H : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp a : 𝓞 F) ∈ v.asIdeal → Subgroup (GL (Fin n) (kv F v))) (lam : ∀ a v h, H a v h →* ℂˣ) (wOf : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp a : 𝓞 F) ∈ v.asIdeal → SG) (e : ∀ a v h, (𝓞 E ⧸ (wOf a v h).1.asIdeal) ≃+* kv F v), Jm = 1 → S.Lb = baseLb E n ST → ∀ hU : S.U = levU hc n ST SG (Subgroup.pi Set.univ Hw), (∀ x : S.U, S.chi x = ∏ w : SG, (lamw w ⟨(levRed hc n ST SG (Subgroup.pi Set.univ Hw) ⟨x.1, hU ▸ x.2⟩).1 w, (levRed hc n ST SG (Subgroup.pi Set.univ Hw) ⟨x.1, hU ▸ x.2⟩).2 w trivial⟩)⁻¹) → (∀ a v (_ : (gp a : 𝓞 F) ∈ v.asIdeal), v ∉ plUnder F ST) → (∀ a v h (w : SG), IsOver v w.1 ↔ w = wOf a v h) → (∀ φ : SG → ℂ, ∏ w : SG, φ w = ∏ a : Fin 2, ∏ᶠ (v : HeightOneSpectrum (𝓞 F)) (h : (gp a : 𝓞 F) ∈ v.asIdeal), φ (wOf a v h)) → (∀ a v h (z : Formalism.L2.Herm.intAf F E), ∃ hz : G.phi a v h (prV (E := E) v z.1) ∈ v.adicCompletionIntegers F, IsLocalRing.residue (v.adicCompletionIntegers F) ⟨_, hz⟩ = e a v h (resS F (wOf a v h).1 z)) → (∀ a v h M, M ∈ Hw (wOf a v h) ↔ Matrix.GeneralLinearGroup.map (e a v h).toRingHom M ∈ H a v h) → (∀ a v h (M : Hw (wOf a v h)) (M' : H a v h), M'.1 = Matrix.GeneralLinearGroup.map (e a v h).toRingHom M.1 → lam a v h M' = lamw (wOf a v h) M) → ∃ V : GLevH S G H lam, ∀ a v h, V.fr a v h = 1 := by
  intro F E _ _ _ _ _ _ hc n _ ST SG T f bad gp Jm S G Hw lamw H lam wOf e hJ hLb hU hchi hST hover hprod hcomp hH hlam
  subst hJ
  have hcomp' : ∀ a v h (z : Formalism.L2.Herm.intAf F E), ∃ hz : gloPhi v (G.sp a v h) (prV (E := E) v z.1) ∈ v.adicCompletionIntegers F,
      IsLocalRing.residue (v.adicCompletionIntegers F) ⟨_, hz⟩ = e a v h (resS F (wOf a v h).1 z) := hcomp
  have hw := fun a v h => gloRho_zero_of_compat v (G.sp a v h) (G.sp_alg a v h) (wOf a v h).1 (e a v h) (hcomp' a v h)
  have hgE := fun a v h => gloE_eq_of_compat v (G.sp a v h) (G.sp_alg a v h) (wOf a v h).1 (e a v h) (hcomp' a v h)
  have hloc : ∀ v x, x ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) →
      (x ∈ S.Uloc v ↔ x ∈ levLoc hc n ST SG (Subgroup.pi Set.univ Hw) v) := by
    intro v x hx
    constructor
    · intro hxv
      have hxU : x ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F) := hx.1
      have hp : rll_put n v x ∈ S.U := by
        refine (S.U_eq _).2 ⟨rll_put_mem_UAd hc n v hxU, fun v' => ?_⟩
        by_cases hv : v' = v
        · subst hv; rw [rll_put_self]; exact hxv
        · rw [rll_put_ne n v v' hv]; exact Subgroup.one_mem _
      rw [hU] at hp
      exact ⟨_, hp, rll_put_self n v x⟩
    · rintro ⟨k, hk, rfl⟩
      rw [← hU] at hk
      exact ((S.U_eq k).1 hk).2 v
  have hxL : ∀ x : S.U, x.1 ∈ levU hc n ST SG (Subgroup.pi Set.univ Hw) := fun x => hU ▸ x.2
  have hkJ : ∀ x : S.U, x.1 ∈ J0 hc n ST := fun x => ((mem_levU hc n ST SG _).1 (hxL x)).1
  refine ⟨{ fr := fun _ _ _ => 1
            fr_lat := ?_
            mem := ?_
            red := fun a v h x => ⟨Matrix.GeneralLinearGroup.map (e a v h).toRingHom
                ((levRed hc n ST SG (Subgroup.pi Set.univ Hw) ⟨x.1, hU ▸ x.2⟩).1 (wOf a v h)),
              (hH a v h _).1 ((levRed hc n ST SG (Subgroup.pi Set.univ Hw) ⟨x.1, hU ▸ x.2⟩).2 (wOf a v h) trivial)⟩
            red_eq := ?_
            chi_eq := ?_
            chi_unit := ?_ }, fun _ _ _ => rfl⟩
  · intro a v h x
    rw [hLb]
    exact gco_fr_lat n ST v (G.sp a v h) (G.sp_alg a v h) (hST a v h) x
  · intro a v h x hx
    rw [hLb] at hx
    have hG : ∀ y : GL (Fin n) (E ⊗[F] v.adicCompletion F), G.mat a v h 1 y =
        ((bc (gloPhi v (G.sp a v h)) y : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
      intro y; simp only [GLoc.mat, inv_one, one_mul, mul_one]; rfl
    rw [hloc v x hx, gco_mem_levLoc hc n ST SG v (G.sp a v h) (G.sp_alg a v h) Hw (wOf a v h) (hw a v h)
      ((hover a v h _).2 rfl) (fun w' hw' => (hover a v h w').1 hw') (hST a v h) x hx, hG]
    constructor
    · rintro ⟨M, hM, hMx⟩
      refine ⟨Matrix.GeneralLinearGroup.map (e a v h).toRingHom M, (hH a v h M).1 hM, ?_⟩
      rw [← hMx]
      ext i j
      rw [Matrix.map_apply, hgE]
      rfl
    · rintro ⟨M', hM', hM'x⟩
      refine ⟨Matrix.GeneralLinearGroup.map (e a v h).symm.toRingHom M', (hH a v h _).2 ?_, ?_⟩
      · convert hM' using 1
        ext i j
        simp
      · rw [← hM'x]
        ext i j
        rw [Matrix.map_apply, hgE]
        simp
  · intro a v h x
    have h1 := gco_red_map n v (G.sp a v h) (G.sp_alg a v h) (wOf a v h).1 (hw a v h) (congruence_subgroup_le_stabilizer hc n ST (hkJ x))
    have hG : G.mat a v h 1 (bc (prV (E := E) v) x.1) =
        ((bc (gloPhi v (G.sp a v h)) (bc (prV (E := E) v) x.1) : GL (Fin n) (v.adicCompletion F)) :
          Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
      simp only [GLoc.mat, inv_one, one_mul, mul_one]; rfl
    rw [hG, ← h1]
    ext i j
    rw [Matrix.map_apply, hgE]
    rfl
  · intro x
    rw [hchi x, Units.coe_prod]
    simp only [Units.val_inv_eq_inv_val]
    rw [hprod]
    congr 1; funext a; congr 1; funext v; congr 1; funext h
    rw [hlam a v h ⟨(levRed hc n ST SG (Subgroup.pi Set.univ Hw) ⟨x.1, hxL x⟩).1 (wOf a v h),
      (levRed hc n ST SG (Subgroup.pi Set.univ Hw) ⟨x.1, hxL x⟩).2 (wOf a v h) trivial⟩ _ rfl]
  · intro x
    rw [hchi x, Units.coe_prod, norm_prod]
    refine Finset.prod_eq_one fun w _ => ?_
    rw [Units.val_inv_eq_inv_val, norm_inv, inv_eq_one]
    generalize (⟨_, _⟩ : Hw w) = m
    have hfo : IsOfFinOrder m := isOfFinOrder_of_finite m
    obtain ⟨N, hN, hpow⟩ := hfo.exists_pow_eq_one
    have hp : ((lamw w m : ℂˣ) : ℂ) ^ N = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, hpow, map_one, Units.val_one]
    exact Complex.norm_eq_one_of_pow_eq_one hp hN.ne'
end
end

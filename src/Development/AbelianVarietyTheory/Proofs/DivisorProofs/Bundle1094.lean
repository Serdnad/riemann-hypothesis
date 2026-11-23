module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle342
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle677
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1057
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle009
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle609
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle594
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle505
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Mathlib.NumberTheory.NumberField.CMField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1064
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1061
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
public import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle266
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle637
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle007
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle005

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Adelic.HeightExt

open NumberField IsDedekindDomain GlobalTheory.ChowHt GlobalTheory.Adelic

section Places

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def locDeg (K : Type) [Field K] [NumberField K] [Algebra K L] (w : HeightOneSpectrum (𝓞 L)) : ℕ :=
  w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K)

theorem mk_algebraMap (w : HeightOneSpectrum (𝓞 L)) (x : K) :
    FinitePlace.mk w (algebraMap K L x) = FinitePlace.mk (w.under (𝓞 K)) x ^ locDeg K w := by
  set v := w.under (𝓞 K) with hv
  have : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  have he : 0 < w.asIdeal.ramificationIdx (𝓞 K) := Ideal.ramificationIdx_pos _ _
  have hf : 0 < w.asIdeal.inertiaDeg (𝓞 K) := Ideal.inertiaDeg_pos _ _
  rcases eq_or_ne x 0 with rfl | hx
  · rw [map_zero, map_zero, map_zero, locDeg, zero_pow (Nat.mul_pos he hf).ne']
  have hn := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver w.asIdeal v.asIdeal v.isPrime v.ne_bot
  rw [Ideal.inertiaDeg'_eq_inertiaDeg] at hn
  have h0 : v.valuation K x ≠ 0 := (v.valuation K).ne_zero_iff.2 hx
  rw [FinitePlace.mk_apply, FinitePlace.mk_apply, FinitePlace.norm_embedding', FinitePlace.norm_embedding',
    ← HeightOneSpectrum.valuation_liesOver L v w x, map_pow, WithZeroMulInt.toNNReal_neg_apply _ h0,
    WithZeroMulInt.toNNReal_neg_apply _ h0, hn, locDeg]
  push_cast
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_mul]
  congr 1
  push_cast
  ring

theorem finite_fiber (v : HeightOneSpectrum (𝓞 K)) :
    {w : HeightOneSpectrum (𝓞 L) | w.under (𝓞 K) = v}.Finite := by
  have h : (v.asIdeal.primesOver (𝓞 L)).Finite := Set.toFinite _
  refine (h.preimage (f := fun w : HeightOneSpectrum (𝓞 L) => w.asIdeal)
    (fun a _ b _ hab => HeightOneSpectrum.ext hab)).subset fun w hw => ?_
  exact ⟨w.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal hw).symm⟩⟩

theorem sum_locDeg (v : HeightOneSpectrum (𝓞 K)) :
    ∑ w ∈ (finite_fiber (L := L) v).toFinset, locDeg K w = Module.finrank K L := by
  classical
  have hsumN : ∑ q : v.asIdeal.primesOver (𝓞 L), q.1.ramificationIdx (𝓞 K) * q.1.inertiaDeg (𝓞 K) =
      Module.finrank K L := by
    rw [Ideal.sum_ramification_inertia_eq_finrank, IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L]
  rw [← hsumN]
  refine Finset.sum_bij (fun w hw => ⟨w.asIdeal, w.isPrime,
    ⟨(congrArg HeightOneSpectrum.asIdeal (((finite_fiber (L := L) v).mem_toFinset).1 hw)).symm⟩⟩) (fun _ _ => Finset.mem_univ _)
    (fun a _ b _ h => HeightOneSpectrum.ext (congrArg Subtype.val h)) (fun q _ => ?_) fun _ _ => rfl
  refine ⟨⟨q.1, q.2.1, fun h0 => v.ne_bot ?_⟩, (Set.Finite.mem_toFinset _).2 (HeightOneSpectrum.ext q.2.2.over.symm),
    rfl⟩
  have h1 : v.asIdeal = q.1.comap (algebraMap (𝓞 K) (𝓞 L)) := q.2.2.over
  rw [h1, h0]
  exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)

theorem finsum_locDeg_mul (g : HeightOneSpectrum (𝓞 K) → ℝ) (hg : (Function.support g).Finite) :
    ∑ᶠ w : HeightOneSpectrum (𝓞 L), (locDeg K w : ℝ) * g (w.under (𝓞 K)) = Module.finrank K L * ∑ᶠ v, g v := by
  classical
  have hS : {w : HeightOneSpectrum (𝓞 L) | w.under (𝓞 K) ∈ Function.support g}.Finite :=
    (hg.biUnion fun v _ => finite_fiber (L := L) v).subset fun w hw => Set.mem_biUnion hw rfl
  rw [finsum_eq_sum_of_support_subset _ (s := hS.toFinset) fun w hw => by
      simpa using right_ne_zero_of_mul hw,
    finsum_eq_sum g hg, Finset.mul_sum,
    ← Finset.sum_fiberwise_of_maps_to (t := hg.toFinset) (g := fun w => w.under (𝓞 K)) fun w hw => by simpa using hw]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [← sum_locDeg v, Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr ?_ fun w hw => by rw [(Set.Finite.mem_toFinset _).1 hw]
  ext w
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hv ⊢
  exact ⟨fun h => h.2, fun h => ⟨h ▸ hv, h⟩⟩

theorem sum_comp_algebraMap (f : (K →+* ℂ) → ℝ) :
    ∑ σ : L →+* ℂ, f (σ.comp (algebraMap K L)) = Module.finrank K L * ∑ τ : K →+* ℂ, f τ := by
  classical
  have hfib : ∀ τ : K →+* ℂ, (Finset.univ.filter fun σ : L →+* ℂ => σ.comp (algebraMap K L) = τ).card =
      Module.finrank K L := by
    intro τ
    let _ : Algebra K ℂ := τ.toAlgebra
    let e : {σ : L →+* ℂ // σ.comp (algebraMap K L) = τ} ≃ (L →ₐ[K] ℂ) :=
      { toFun := fun σ => ⟨σ.1, fun a => congrFun (congrArg DFunLike.coe σ.2) a⟩
        invFun := fun φ => ⟨φ.toRingHom, RingHom.ext fun a => φ.commutes a⟩
        left_inv := fun σ => rfl
        right_inv := fun φ => rfl }
    rw [← Fintype.card_subtype, Fintype.card_congr e, AlgHom.card]
  rw [← Finset.sum_fiberwise Finset.univ (fun σ : L →+* ℂ => σ.comp (algebraMap K L))
    (fun σ => f (σ.comp (algebraMap K L))), Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_congr rfl fun σ hσ => by rw [(Finset.mem_filter.1 hσ).2], Finset.sum_const, hfib τ,
    nsmul_eq_mul]

end Places

theorem iSup_pow {ι : Type} [Finite ι] [Nonempty ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (m : ℕ) :
    ⨆ i, a i ^ m = (⨆ i, a i) ^ m := by
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := a)
  refine le_antisymm (ciSup_le fun j => pow_le_pow_left₀ (ha j) (le_ciSup (Set.finite_range _).bddAbove j) m) ?_
  rw [← hi]
  exact le_ciSup (f := fun i => a i ^ m) (Set.finite_range _).bddAbove i

theorem finite_support_log_iSup {K ι : Type} [Field K] [NumberField K] [Finite ι] {z : ι → K} (hz : z ≠ 0) :
    (Function.support fun v : FinitePlace K => Real.log (⨆ k, v (z k))).Finite := by
  obtain ⟨k₀, hk₀⟩ := Function.ne_iff.1 hz
  have : Nonempty ι := ⟨k₀⟩
  refine (Set.finite_iUnion fun k : {k // z k ≠ 0} => FinitePlace.hasFiniteMulSupport k.2).subset fun v hv => ?_
  by_contra h
  simp only [Set.mem_iUnion, Function.mem_mulSupport, not_exists, not_not] at h
  refine hv ?_
  have : ⨆ k, v (z k) = 1 := le_antisymm (ciSup_le fun k => by
      rcases eq_or_ne (z k) 0 with h0 | h0
      · rw [h0, map_zero]; exact zero_le_one
      · exact (h ⟨k, h0⟩).le)
    ((h ⟨k₀, hk₀⟩).ge.trans (le_ciSup (f := fun k => v (z k)) (Set.finite_range _).bddAbove k₀))
  simp only [this, Real.log_one]

theorem finsum_log_iSup_algebraMap {K L ι : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [Finite ι] {z : ι → K} (hz : z ≠ 0) :
    ∑ᶠ w : FinitePlace L, Real.log (⨆ k, w (algebraMap K L (z k))) =
      Module.finrank K L * ∑ᶠ v : FinitePlace K, Real.log (⨆ k, v (z k)) := by
  obtain ⟨k₀, -⟩ := Function.ne_iff.1 hz
  have : Nonempty ι := ⟨k₀⟩
  rw [← finsum_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := L)).symm,
    ← finsum_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := K)).symm,
    ← finsum_locDeg_mul _ ((finite_support_log_iSup hz).preimage
      (FinitePlace.equivHeightOneSpectrum (K := K)).symm.injective.injOn)]
  refine finsum_congr fun w => ?_
  rw [← Real.log_pow, ← iSup_pow _ fun _ => apply_nonneg _ _]
  exact congrArg Real.log (iSup_congr fun k => mk_algebraMap w (z k))

theorem pointHeight_algebraMap : ∀ (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
    (N n : ℕ) (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ),
    Submodule.span F (Set.range w.col) = ⊤ → (∀ σ, (A σ).det ≠ 0) →
    ∀ (K' : Type) [Field K'] [NumberField K'] [Algebra F K'] [Algebra K K'] [IsScalarTower F K K'] (y : Fin N → K),
      y ≠ 0 → pointHeight w A (fun j => algebraMap K K' (y j)) = pointHeight w A y := by
  intro F K _ _ _ _ _ N n w A hw _ K' _ _ _ _ _ y hy
  classical
  have hz : (fun k => ∑ j, algebraMap F K (w j k) * y j) ≠ 0 := fun h => by
    have hp := finSize_pos hw (algebraMap F K) AbsoluteValue.trivial hy
    have h' : ∀ k, ∑ j, algebraMap F K (w j k) * y j = 0 := congrFun h
    simp [finSize, h'] at hp
  have h₁ := finsum_log_iSup_algebraMap (L := K') hz
  have h₂ := sum_comp_algebraMap (L := K')
    fun τ : K →+* ℂ => Real.log (archSize (A (τ.comp (algebraMap F K))) fun j => τ (y j))

  simp only [map_sum, map_mul, ← IsScalarTower.algebraMap_apply] at h₁
  simp only [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, RingHom.comp_apply] at h₂
  have hK : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hKL : (0 : ℝ) < Module.finrank K K' := by exact_mod_cast Module.finrank_pos
  rw [pointHeight_eq, pointHeight_eq, h₂, ← Module.finrank_mul_finrank ℚ K K']
  simp only [finSize, ← FinitePlace.coe_apply]
  rw [h₁]
  push_cast
  field_simp

end GlobalTheory.Adelic.HeightExt
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC
theorem sh_of_isSepClosed (Ω : Type) [Field Ω] [IsSepClosed Ω] : SH Ω := by
  refine ⟨inferInstance, ?_⟩
  haveI : Algebra.IsIntegral Ω (IsLocalRing.ResidueField Ω) :=
    Algebra.IsIntegral.of_surjective (Algebra.ofId Ω (IsLocalRing.ResidueField Ω)) IsLocalRing.residue_surjective
  exact Algebra.IsAlgebraic.isSepClosed (F := Ω)

theorem cech_level_acyclic : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (k : ℕ) (m : ℕ), 0 < m → ∀ y : H R (disc.obj ((cech (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj (op ⦋k⦌))) F m, y = 0 := by
  intro R _ F hF K Ω _ _ _ _ k m hm y
  haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
  haveI : Algebra.IsSeparable K Ω := IsSepClosure.separable
  have hf : IsIntegralHom (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) :=
    IsIntegralHom.SpecMap_iff.2 fun x => Algebra.IsIntegral.isIntegral x
  obtain ⟨Z, π, e, hπ, -⟩ := GlobalTheory.T.exists_representable_cech_level_of_stable @IsIntegralHom _ _ _ hf (op ⦋k⦌)
  haveI : IsIntegralHom π := hπ
  haveI : IsAffine Z := isAffine_of_isAffineHom π
  let φ : Ω →+* Γ(Z, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv ≫ π.appTop).hom
  letI : Algebra Ω Γ(Z, ⊤) := φ.toAlgebra
  have hint : (π.app ⊤).hom.IsIntegral := π.isIntegral_app ⊤ (isAffineOpen_top _)
  haveI : Algebra.IsIntegral Ω Γ(Z, ⊤) := by
    refine ⟨fun b => ?_⟩
    obtain ⟨p, hp, h⟩ := hint b
    refine ⟨p.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom, hp.map _, ?_⟩
    have hc : (algebraMap Ω Γ(Z, ⊤)).comp (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom = (π.app ⊤).hom := by
      ext x
      change ((Scheme.ΓSpecIso (CommRingCat.of Ω)).hom ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv ≫ π.app ⊤).hom x = _
      rw [Iso.hom_inv_id_assoc]
      rfl
    rw [Polynomial.eval₂_map, hc]
    exact h
  have hac : AcycF R (sp Γ(Z, ⊤)) F := GlobalTheory.T.integral_strictHenselian_acyclic_finitary R F hF Ω Γ(Z, ⊤) (sh_of_isSepClosed Ω)
  let i : sp Γ(Z, ⊤) ≅ disc.obj ((cech (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj (op ⦋k⦌)) :=
    sch.mapIso Z.isoSpec.symm ≪≫ disc.mapIso e
  have heq : Eqv R i.hom F := (GlobalTheory.T.etaleCohomologyEquivalence_basic_properties R F).1 _ _ i.hom inferInstance
  have hs := ((GlobalTheory.T.etaleCohomologyEquivalence_basic_properties R F).2.2.2 _ _ i.hom heq).1 hac (m : ℤ) (by exact_mod_cast hm)
  exact Subsingleton.elim _ _

end GlobalTheory.EtC
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

theorem evA_comp_coe {K A : Type} [Field K] [CommRing A] [Algebra K A] {d : ℕ}
    (x : Fin d → A) (hx : ∀ i, IsNilpotent (x i)) :
    (evA K x hx).comp (MvPolynomial.coeToMvPowerSeries.algHom K) = MvPolynomial.aeval x := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [AlgHom.comp_apply, MvPolynomial.coeToMvPowerSeries.algHom_apply, MvPolynomial.aeval_X]
  simp only [MvPolynomial.coe_X, map_X]
  exact GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate K (Fin d) A x hx i

theorem exists_chart_of_isConn (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0)
    (G : PDivGroup p K) (hG : G.IsConn) : ∃ d, Nonempty (Chart G d) := by
  obtain ⟨x, hres, haug, hsurj⟩ := GlobalTheory.T.exists_coordinates_generate_connected_levels p K h G hG
  have hmem : ∀ n i, x n i ∈ augIdeal K (G.A n) := fun n i => by
    simp [augIdeal, haug n i]
  have hnil : ∀ n i, IsNilpotent (x n i) := fun n i => hG n _ (hmem n i)
  refine ⟨_, ⟨{ x := x, nil := hnil, res := hres, aug := haug, presents := ⟨?_, ?_⟩ }⟩⟩
  · intro n a
    obtain ⟨P, hP⟩ := hsurj n a
    refine ⟨(P : MvPowerSeries _ K), ?_⟩
    have := congrArg (fun φ => φ P) (evA_comp_coe (x n) (hnil n))
    simp only [AlgHom.comp_apply, MvPolynomial.coeToMvPowerSeries.algHom_apply] at this
    rw [← hP, ← this]
    rfl
  · intro N
    refine ⟨N, fun f hf α hα => ?_⟩
    have hq : ∀ i, x N i ^ (p ^ N) ∈ frobKerIdeal (p ^ N) K (G.A N) :=
      fun i => pow_mem_frobKerIdeal (hmem N i)
    exact GlobalTheory.T.coeff_eq_zero_of_evA_eq_zero_of_le_finrank' K (G.A N) _ (p ^ N) (x N) (hnil N) _ (hsurj N) hq
      (GlobalTheory.T.pow_finrank_omega_le_finrank_frobeniusKernel p K h G N) f hf α
      (lt_of_lt_of_le hα (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le)

end GlobalTheory.Katz
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.CMVal.NormConj

theorem norm_sigma_ratio {E : Type} [Field E] [NumberField E] [IsCMField E] (σ : ℂ ≃+* ℂ) (φ : E →+* ℂ) (α : Eˣ) :
    ‖σ (φ (α : E) / starRingEnd ℂ (φ (α : E)))‖ = 1 := by
  rw [← IsCMField.complexEmbedding_complexConj, map_div₀]
  have e2 : σ (φ (IsCMField.complexConj E (α : E))) = starRingEnd ℂ (((σ : ℂ →+* ℂ).comp φ) (α : E)) := by
    rw [← IsCMField.complexEmbedding_complexConj]; rfl
  have e1 : σ (φ (α : E)) = ((σ : ℂ →+* ℂ).comp φ) (α : E) := rfl
  have h0 : ((σ : ℂ →+* ℂ).comp φ) (α : E) ≠ 0 := by simp
  rw [e2, e1, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.2 h0)]

end GlobalTheory.CMVal.NormConj


open GlobalTheory.CMVal.NormConj in
theorem GlobalTheory.CMVal.norm_conj_finPart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I]
    (φ : I → E →+* ℂ) (hφ : IsCMType φ) (s : ℕ) (κ : I → ℕ) (c : Ideal (OF E)) (hc : c ≠ ⊥) (χ : HChar E)
    (hχ : HasInf χ φ (fun i => (κ i : ℤ) + s)) (hu : ∀ u ∈ hatOUnits c, finPart χ u = 1) (σ : ℂ ≃+* ℂ) (y : (Af E)ˣ),
    ‖σ (finPart χ y : ℂ)‖ = 1 := by
  intro E _ _ _ I _ φ _ s κ c hc χ hinf hχ σ y
  classical
  have hfin := GlobalTheory.CMVal.PicFin.finite_picO E c hc
  have hpos : 0 < Nat.card (PicO c) := Nat.card_pos
  have hmem : y ^ Nat.card (PicO c) ∈ (princ ⊔ hatOUnits c : Subgroup (Af E)ˣ) := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact pow_card_eq_one'
  obtain ⟨p, ⟨α, rfl⟩, u, hu, hpu⟩ := Subgroup.mem_sup.1 hmem
  set h := Nat.card (PicO c)
  have hf : ((finPart χ y : ℂ)) ^ h = ((χ.inf α : ℂˣ) : ℂ)⁻¹ := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, ← hpu, map_mul, hχ u hu, mul_one,
      eq_inv_of_mul_eq_one_left (finPart_mul_inf χ α), Units.val_inv_eq_inv_val]
  have hn : ‖σ (finPart χ y : ℂ)‖ ^ h = 1 := by
    rw [← norm_pow, ← map_pow, hf, (hasInfRatio_iff χ φ _).1 hinf α, map_inv₀, norm_inv, map_prod, norm_prod]
    simp only [map_zpow₀, norm_zpow, norm_sigma_ratio, one_zpow, Finset.prod_const_one, inv_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hpos.ne').1 hn
end
end

section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

namespace GlobalTheory.LieCoordMult

theorem lieMult_iff_finrank_eig : ∀ (W : Type) [CommRing W] (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G] (O : Type) [CommRing O] (act : OAct O G) (n : ℕ) (k : Type) [Field k] (β : W →+* k) (T : (Fin n → k) → (epsPtR (spMap β) ⟶ G)) (A : O → Matrix (Fin n) (Fin n) k), Function.Injective T → (∀ v : epsPtR (spMap β) ⟶ G, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk (spMap β) ⟶ G).left ↔ v ∈ Set.range T) → (∀ c c', T (c + c') = T c * T c') → (∀ (s : k) c, (T (s • c)).left = spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScaleR s) ≫ (T c).left) → (∀ a c, T c ≫ act.act a = T ((A a).mulVec c)) → ∀ (τ : O →+* k) (N : ℕ), LieMult act (spMap β) τ N ↔ Module.finrank k (⨅ a, LinearMap.ker (Matrix.mulVecLin (A a) - τ a • LinearMap.id) : Submodule k (Fin n → k)) = N := by
  intro W _ G _ _ O _ act n k _ β T A hinj htan hadd hsc hact τ N
  set E : Submodule k (Fin n → k) :=
    ⨅ a, LinearMap.ker (Matrix.mulVecLin (A a) - τ a • LinearMap.id) with hE
  have memE : ∀ x, x ∈ E ↔ ∀ a, (A a).mulVec x = τ a • x := by
    intro x
    simp [hE, Submodule.mem_iInf, sub_eq_zero]
  have T0 : T 0 = 1 := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  have Tsum : ∀ (m : ℕ) (y : Fin m → (Fin n → k)), (List.ofFn (fun i => T (y i))).prod = T (∑ i, y i) := by
    intro m
    induction m with
    | zero => intro y; simp [T0]
    | succ m ih => intro y; rw [List.ofFn_succ, List.prod_cons, ih, Fin.sum_univ_succ, hadd]
  have eig : ∀ w, IsLieEigen act (spMap β) τ w ↔ ∃ x ∈ E, w = T x := by
    intro w
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨x, rfl⟩ := (htan w).1 h1
      refine ⟨x, (memE x).2 fun a => hinj (Over.OverMorphism.ext ?_), rfl⟩
      rw [← hact, h2 a, hsc]
      rfl
    · rintro ⟨x, hx, rfl⟩
      refine ⟨(htan _).2 ⟨x, rfl⟩, fun a => ?_⟩
      rw [hact, (memE x).1 hx a, hsc]
      rfl
  have comb : ∀ (x : Fin N → (Fin n → k)) (y : Fin n → k) (c : Fin N → k),
      (∃ u : Fin N → (epsPt (spMap β) ⟶ G), (∀ i, (u i).left = spMap (epsScale (c i)) ≫ (T (x i)).left) ∧
        T y = (List.ofFn u).prod) ↔ y = ∑ i, c i • x i := by
    intro x y c
    constructor
    · rintro ⟨u, hu, hy⟩
      have hu' : u = fun i => T (c i • x i) := funext fun i => Over.OverMorphism.ext ((hu i).trans (hsc _ _).symm)
      rw [hu', Tsum] at hy
      exact hinj hy
    · intro hy
      exact ⟨fun i => T (c i • x i), fun i => hsc _ _, by rw [Tsum, hy]⟩
  show (∃ v : Fin N → (epsPt (spMap β) ⟶ G), (∀ i, IsLieEigen act (spMap β) τ (v i)) ∧ ∀ w, IsLieEigen act (spMap β) τ w →
    ∃! c : Fin N → k, ∃ u : Fin N → (epsPt (spMap β) ⟶ G),
      (∀ i, (u i).left = spMap (epsScale (c i)) ≫ (v i).left) ∧ w = (List.ofFn u).prod) ↔ _
  constructor
  · rintro ⟨v, hv, H⟩
    choose x hxE hx using fun i => (eig _).1 (hv i)
    obtain rfl : v = fun i => T (x i) := funext hx
    let b : Fin N → E := fun i => ⟨x i, hxE i⟩
    have bij : Function.Bijective (Fintype.linearCombination k b) := by
      refine (Function.bijective_iff_existsUnique _).2 fun y => ?_
      refine (existsUnique_congr fun c => ?_).1 (H (T y) ((eig _).2 ⟨y, y.2, rfl⟩))
      rw [comb x y c, Subtype.ext_iff, Fintype.linearCombination_apply]
      simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, b]
      exact eq_comm
    rw [← (LinearEquiv.ofBijective _ bij).finrank_eq, Module.finrank_fin_fun]
  · intro h
    let b := Module.finBasisOfFinrankEq k E h
    refine ⟨fun i => T (b i), fun i => (eig _).2 ⟨_, (b i).2, rfl⟩, fun w hw => ?_⟩
    obtain ⟨y, hy, rfl⟩ := (eig w).1 hw
    refine (existsUnique_congr fun c => ?_).2
      ((Function.bijective_iff_existsUnique _).1 b.equivFun.symm.bijective ⟨y, hy⟩)
    rw [comb (fun i => (b i : Fin n → k)) y c, Module.Basis.equivFun_symm_apply, Subtype.ext_iff]
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul]
    exact eq_comm

end GlobalTheory.LieCoordMult
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.UPel.HT

theorem objMap_comp : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S₁ S₂ S₃ : Scheme.{0}) (s₁ : S₁ ⟶ Sp R) (s₂ : S₂ ⟶ Sp R) (s₃ : S₃ ⟶ Sp R) (o₁ : Obj b N s₁) (o₂ : Obj b N s₂) (o₃ : Obj b N s₃) (f : S₁ ⟶ S₂) (g : S₂ ⟶ S₃), ObjMap o₁ o₂ f → ObjMap o₂ o₃ g → Nonempty (ObjMap o₁ o₃ (f ≫ g)) := by
  intro p _ D R _ b N S₁ S₂ S₃ s₁ s₂ s₃ o₁ o₂ o₃ f g h₁ h₂
  have sq : IsSquare (h₁.φ ≫ h₂.φ) (h₁.φ₂ ≫ h₂.φ₂) := by
    constructor
    · rw [Category.assoc, h₂.sq.1, ← Category.assoc, h₁.sq.1, Category.assoc]
    · rw [Category.assoc, h₂.sq.2, ← Category.assoc, h₁.sq.2, Category.assoc]
  have act : ∀ c, (o₁.act.act c).left ≫ (h₁.φ ≫ h₂.φ) = (h₁.φ ≫ h₂.φ) ≫ (o₃.act.act c).left := by
    intro c
    rw [← Category.assoc, h₁.act, Category.assoc, h₂.act, Category.assoc]
  have eta : ∀ y, (o₁.eta y).left ≫ (h₁.φ ≫ h₂.φ) = (f ≫ g) ≫ (o₃.eta y).left := by
    intro y
    rw [← Category.assoc, h₁.eta, Category.assoc, h₂.eta, Category.assoc]
  have H : LBIso (o₂.P.pull h₁.φ₂) ((o₃.P.pull h₂.φ₂).pull h₁.φ₂) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull o₂.P h₁.φ₂ h₁.φ₂ rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (o₃.P.pull h₂.φ₂) h₁.φ₂ h₁.φ₂ rfl) h₂.pol
  have H' : LBIso (o₂.P.pull h₁.φ₂) (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.chartPull (chartPullId _) (chartPullIn o₃.P (fun _ : PUnit => h₂.φ₂) (fun _ => 1) h₁.φ₂) H
  have pol : LBIso o₁.P (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) h₁.pol H'
  exact ⟨⟨h₁.φ ≫ h₂.φ, h₁.φ₂ ≫ h₂.φ₂, h₁.cart.comp h₂.cart, sq, act, pol, eta⟩⟩

end GlobalTheory.UPel.HT
end
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.prodDerivWeierstrassPOverSquares_ne_zero : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → (∀ k : Sq p, sqPt p t k ∉ L.lattice ∧ (p : ℂ) * sqPt p t k ∈ L.lattice) ∧ sqProd p L t ≠ 0 := by
  first | exact @GlobalTheory.CMModel.SqNe.sqPt_and_sqProd_ne_zero | exact GlobalTheory.CMModel.SqNe.sqPt_and_sqProd_ne_zero | (intros; apply GlobalTheory.CMModel.SqNe.sqPt_and_sqProd_ne_zero <;> assumption)
end

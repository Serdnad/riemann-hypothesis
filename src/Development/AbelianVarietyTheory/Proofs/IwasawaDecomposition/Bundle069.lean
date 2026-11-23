module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Mathlib.RingTheory.PicardGroup
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle065
public import Formalism.LocalToGlobal.ProjectiveLattices.EmbKCoe
public import Mathlib.LinearAlgebra.Lagrange
public import Formalism.SharpRestriction.GrowthBounds.Bundle001
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle049
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Mathlib.Tactic.TypeStar
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle003

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

namespace GlobalTheory.NormCompat

theorem chi_artin_restrict : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (K : IntermediateField E Ω) [FiniteDimensional E K] [NumberField K] [IsAlgClosure K Ω] (art : Ideles E →* Gab E Ω) (artK : Ideles K →* Gab K Ω), IsGlobalArtin art → IsGlobalArtin artK → ∀ (ρ : Gab K Ω →* Gab E Ω), (∀ τ : G K Ω, ρ (toAb K Ω τ) = toAb E Ω (τ.restrictScalars E)) → ∀ (B : Type) [CommGroup B] (χ : Gab E Ω →* B) (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 K)), w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal → (∀ x, IsUnitAt v x → χ (art (localIdele E v x)) = 1) → (∀ x, IsUnitAt w x → χ (ρ (artK (localIdele K w x))) = 1) ∧ ∀ x ϖ, IsUnifAt w x → IsUnifAt v ϖ → χ (ρ (artK (localIdele K w x))) = χ (art (localIdele E v ϖ)) ^ w.asIdeal.inertiaDeg (𝓞 E) := by
  intro E Ω _ _ _ _ _ K _ _ _ art artK ha haK ρ hρ B _ χ v w hwv hχ
  obtain ⟨A, hAw⟩ := exists_isPlaceOver (F := K) Ω w
  obtain ⟨hAv, -, hine, hfrob⟩ := GlobalTheory.T.frobenius_restrictScalars_pow_mod_inertia E Ω K v w hwv A hAw

  have hI : ∀ ι ∈ Ine (F := E) A, χ (toAb E Ω ι) = 1 := by
    intro ι hι
    obtain ⟨u, hu, e⟩ := (ha.ine v A hAv (toAb E Ω ι)).mpr ⟨ι, hι, rfl⟩
    rw [← e]
    exact hχ u hu
  refine ⟨fun x hx => ?_, fun x ϖ hx hϖ => ?_⟩
  · obtain ⟨ι, hι, e⟩ := (haK.ine w A hAw _).mp ⟨x, hx, rfl⟩
    rw [← e, hρ]
    exact hI _ (hine ι hι)
  · obtain ⟨σ, hσ, e⟩ := (haK.frob w A hAw _).mp ⟨x, hx, rfl⟩
    obtain ⟨φ, hφ, e'⟩ := (ha.frob v A hAv _).mp ⟨ϖ, hϖ, rfl⟩
    have hm := hI _ (hfrob σ φ hσ hφ)
    have hr : (σ⁻¹).restrictScalars E = (σ.restrictScalars E)⁻¹ := AlgEquiv.ext fun _ => rfl
    rw [← e, hρ, ← e', hr, map_inv, map_inv, map_inv, map_inv, inv_pow]
    rw [map_mul, map_mul, map_inv, map_inv, map_pow, map_pow] at hm
    rw [inv_inj]
    exact mul_inv_eq_one.mp hm

end GlobalTheory.NormCompat
end

section

noncomputable section

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor Polynomial IntermediateField

namespace GlobalTheory.EigDecomp

theorem exists_integral_separating (E : Type) [Field E] [NumberField E] :
    ∃ α : 𝓞 E, (∀ τ τ' : E →+* ℂ, τ (α : E) = τ' (α : E) → τ = τ') ∧
      ∀ a : 𝓞 E, ∃ N : ℤ, N ≠ 0 ∧ ∃ g : ℤ[X], aeval α g = N • a := by
  obtain ⟨α0, hα0⟩ := Field.exists_primitive_element ℚ E
  obtain ⟨d, hd, hint⟩ := exists_integral_multiples ℤ ℚ ({α0} : Finset E)
  have hi : IsIntegral ℤ (d • α0) := hint α0 (Finset.mem_singleton_self _)
  let α : 𝓞 E := ⟨d • α0, hi⟩
  have hαE : (α : E) = d • α0 := rfl
  have hadjF : ℚ⟮(α : E)⟯ = ⊤ := by
    refine top_le_iff.mp (hα0 ▸ IntermediateField.adjoin_simple_le_iff.mpr ?_)
    have h1 : α0 = ((d : ℚ)⁻¹) • (α : E) := by
      rw [hαE, zsmul_eq_mul, Algebra.smul_def, ← mul_assoc, ← map_intCast (algebraMap ℚ E) d, ← map_mul,
        inv_mul_cancel₀ (Int.cast_ne_zero.mpr hd), map_one, one_mul]
    rw [h1]
    exact IntermediateField.smul_mem _ (IntermediateField.mem_adjoin_simple_self ℚ _)
  have hadj : Algebra.adjoin ℚ {(α : E)} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (α : E)), hadjF, IntermediateField.top_toSubalgebra]
  refine ⟨α, fun τ τ' h => ?_, fun a => ?_⟩
  · have := AlgHom.ext_of_adjoin_eq_top hadj (φ₁ := τ.toRatAlgHom) (φ₂ := τ'.toRatAlgHom)
      (by rintro x rfl; exact h)
    ext x
    exact congrArg (fun f : E →ₐ[ℚ] ℂ => f x) this
  · have ha : (a : E) ∈ Algebra.adjoin ℚ {(α : E)} := hadj ▸ Algebra.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
    obtain ⟨g, hg⟩ := ha
    obtain ⟨b, hbM, hb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) g
    refine ⟨b, nonZeroDivisors.ne_zero hbM, IsLocalization.integerNormalization (nonZeroDivisors ℤ) g, ?_⟩
    apply RingOfIntegers.coe_injective
    have hg' : aeval (algebraMap (𝓞 E) E α) g = algebraMap (𝓞 E) E a := hg
    rw [← aeval_algebraMap_apply, ← aeval_map_algebraMap ℚ, hb, map_zsmul, hg', map_zsmul]

end GlobalTheory.EigDecomp

namespace GlobalTheory.EigDecomp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}

theorem nodal_eq_minpoly_map (c : Coeff l) (α : 𝓞 E)
    (hinj : Function.Injective fun τ : E →+* ℂ => embK c τ α) :
    Lagrange.nodal Finset.univ (fun τ : E →+* ℂ => embK c τ α) = (minpoly ℤ α).map (Int.castRingHom c.F) := by
  have hint : IsIntegral ℤ α := Algebra.IsIntegral.isIntegral α
  have hintE : IsIntegral ℤ (α : E) := RingOfIntegers.isIntegral_coe α
  symm
  refine eq_of_monic_of_dvd_of_natDegree_le Lagrange.nodal_monic ((minpoly.monic hint).map _) ?_ ?_
  · rw [Lagrange.nodal]
    refine Finset.prod_dvd_of_coprime ((pairwise_coprime_X_sub_C hinj).set_pairwise _) fun τ _ => dvd_iff_isRoot.mpr ?_
    have h := aeval_algHom_apply (embK c τ).toIntAlgHom α (minpoly ℤ α)
    rw [minpoly.aeval, map_zero] at h
    rw [IsRoot.def, eval_map, ← algebraMap_int_eq, ← aeval_def]
    exact h
  · rw [natDegree_map_eq_of_injective (RingHom.injective_int _), Lagrange.natDegree_nodal, Finset.card_univ,
      NumberField.Embeddings.card E ℂ, ← RingOfIntegers.minpoly_coe,
      ← natDegree_map_eq_of_injective (algebraMap ℤ ℚ).injective_int,
      ← minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hintE]
    exact minpoly.natDegree_le _

end GlobalTheory.EigDecomp

namespace GlobalTheory.EigDecomp

theorem X_sub_C_mul_basis {ι F : Type*} [Field F] [DecidableEq ι] {s : Finset ι} {v : ι → F} {i : ι}
    (hi : i ∈ s) :
    (X - C (v i)) * Lagrange.basis s v i = C (Lagrange.nodalWeight s v i) * Lagrange.nodal s v := by
  rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div hi, mul_left_comm]
  congr 1
  exact EuclideanDomain.mul_div_cancel' (X_sub_C_ne_zero _) (Lagrange.X_sub_C_dvd_nodal v hi)

theorem exists_unique_eigen_sum : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {l : Level H} (c : Coeff l) {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] (φ : c.F →+* R)
    (ρ : 𝓞 E →+* Module.End R V) (v : V), ∃! w : (E →+* ℂ) → V,
      (∀ τ a, ρ a (w τ) = φ (embK c τ a) • w τ) ∧ ∑ τ, w τ = v := by
  intro E _ _ _ H l c R V _ _ _ φ ρ v
  classical
  obtain ⟨α, hinj, hden⟩ := exists_integral_separating E
  let lam : (E →+* ℂ) → c.F := fun τ => embK c τ α
  have hlinj : Function.Injective lam := fun τ τ' h => hinj τ τ' (by
    have := congrArg (fun x : c.F => (x : ℂ)) h
    simpa [lam, embK_coe] using this)
  let A : Module.End R V := ρ α
  let ψ : c.F →+* Module.End R V := (algebraMap R (Module.End R V)).comp φ
  have hc : ∀ x, Commute (ψ x) A := fun x => Algebra.commute_algebraMap_left (φ x) A
  let ev : Polynomial c.F →+* Module.End R V := eval₂RingHom' ψ A hc
  have hev : ∀ p, ev p = p.eval₂ ψ A := fun p => rfl
  have hev_int : ∀ g : ℤ[X], ev (g.map (Int.castRingHom c.F)) = aeval A g := by
    intro g
    rw [hev, eval₂_map, aeval_def]
    congr 1
    exact RingHom.ext_int _ _
  have heig : ∀ (μ : c.F) (x : V), A x = φ μ • x → ∀ p : Polynomial c.F, ev p x = φ (p.eval μ) • x := by
    intro μ x hx p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add (f := _), LinearMap.add_apply, hp, hq, eval_add, map_add (f := _), add_smul]
    | monomial k a =>
      have hk : ∀ k : ℕ, (A ^ k) x = φ μ ^ k • x := by
        intro k
        induction k with
        | zero => simp
        | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hx, smul_smul, pow_succ, mul_comm]
      rw [hev, eval₂_monomial, eval_monomial, Module.End.mul_apply, hk, map_mul, map_pow]
      simp [ψ, smul_smul, mul_comm]
  have hnodal : ev (Lagrange.nodal Finset.univ lam) = 0 := by
    rw [nodal_eq_minpoly_map c α hlinj, hev_int]
    have h := aeval_algHom_apply ρ.toIntAlgHom α (minpoly ℤ α)
    rw [minpoly.aeval, map_zero] at h
    exact h
  let P : (E →+* ℂ) → Module.End R V := fun τ => ev (Lagrange.basis Finset.univ lam τ)
  have hPeig : ∀ τ x, A (P τ x) = φ (lam τ) • P τ x := by
    intro τ x
    have h := congrArg (fun p => ev p x) (X_sub_C_mul_basis (s := Finset.univ) (v := lam) (Finset.mem_univ τ))
    simp only [map_mul, map_sub, hnodal, mul_zero, Module.End.mul_apply, LinearMap.sub_apply,
      LinearMap.zero_apply] at h
    rw [hev X, eval₂_X, hev (C _), eval₂_C] at h
    simpa [ψ, sub_eq_zero, P] using h
  have hsum : ∑ τ, P τ = 1 := by
    simp only [P]

    rw [← map_sum, Lagrange.sum_basis hlinj.injOn Finset.univ_nonempty, map_one]
  have hall : ∀ τ x, A x = φ (lam τ) • x → ∀ a, ρ a x = φ (embK c τ a) • x := by
    intro τ x hx a
    obtain ⟨N, hN, g, hg⟩ := hden a
    have h1 : ρ (N • a) x = φ (embK c τ (N • a)) • x := by
      rw [← hg]
      have e1 := aeval_algHom_apply ρ.toIntAlgHom α g
      have e2 := aeval_algHom_apply (embK c τ).toIntAlgHom α g
      change ρ (aeval α g) x = φ (embK c τ (aeval α g)) • x
      rw [← show aeval A g = ρ (aeval α g) from e1, ← show aeval (lam τ) g = embK c τ (aeval α g) from e2,
        ← hev_int, heig _ _ hx, eval_map, ← algebraMap_int_eq, ← aeval_def]
    have hu : IsUnit (N : R) := by
      rw [← map_intCast φ]
      exact (isUnit_iff_ne_zero.mpr (Int.cast_ne_zero.mpr hN)).map φ
    rw [map_zsmul, map_zsmul, map_zsmul, LinearMap.smul_apply, ← Int.cast_smul_eq_zsmul R,
      ← Int.cast_smul_eq_zsmul R, smul_assoc] at h1
    exact hu.smul_left_cancel.mp h1
  refine ⟨fun τ => P τ v, ⟨fun τ a => hall τ _ (hPeig τ v) a, ?_⟩, ?_⟩
  · show ∑ τ, P τ v = v
    rw [← LinearMap.sum_apply, hsum, Module.End.one_apply]
  · rintro w ⟨hw, hws⟩
    funext τ
    show w τ = P τ v

    rw [← hws, map_sum, Finset.sum_eq_single τ]
    · rw [heig (lam τ) _ (hw τ α), Lagrange.eval_basis_self hlinj.injOn (Finset.mem_univ τ), map_one, one_smul]
    · intro τ' _ hne
      rw [heig (lam τ') _ (hw τ' α), Lagrange.eval_basis_of_ne (Ne.symm hne) (Finset.mem_univ τ'), map_zero, zero_smul]
    · simp

end GlobalTheory.EigDecomp
end
end

section

open MvPolynomial Formalism.MainNotions.G Formalism.GradedWeylDivisibility

noncomputable section

namespace GlobalTheory.ClassRank

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {P : Places p O Kf}

theorem gPos_mul (v : Fin P.nV) (s : Fin (P.n' v)) (A B : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v)) :
    P.gPos v s (A * B) = P.gPos v s A * P.gPos v s B := by
  ext a b

  simp only [Places.gPos, Matrix.mul_apply, map_sum, map_mul]

theorem gPos_one (v : Fin P.nV) (s : Fin (P.n' v)) : P.gPos v s 1 = 1 := by
  ext a b
  by_cases h : a = b <;> simp [Places.gPos, Matrix.one_apply, h]

theorem subst_comp (G H : ∀ v, Fin (P.n' v) → Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) Kf) :
    (P.subst G).comp (P.subst H) = P.subst fun v s => H v s * G v s := by
  apply MvPolynomial.algHom_ext
  intro x

  simp only [Places.subst, AlgHom.comp_apply, aeval_X, map_sum, map_mul, algHom_C, algebraMap_eq,
  Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

theorem subst_one : (P.subst fun _ _ => 1) = AlgHom.id Kf _ := by
  apply MvPolynomial.algHom_ext
  intro x
  simp only [Places.subst, aeval_X, AlgHom.id_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single x.2.2.1]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

theorem natAct_mul (A B : ∀ v, GL (Fin (P.m + 1)) (P.Qq v)) (F : P.Xsp) :
    P.natAct (fun v => A v * B v) F = P.natAct A (P.natAct B F) := by
  have h := congrArg (fun φ => φ F) (subst_comp (P := P)
    (fun v s => P.gPos v s ((A v)⁻¹ : GL (Fin (P.m + 1)) (P.Qq v)))
    (fun v s => P.gPos v s ((B v)⁻¹ : GL (Fin (P.m + 1)) (P.Qq v))))
  simp only [AlgHom.comp_apply] at h
  simp only [Places.natAct, LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_smul, smul_smul, h,
    mul_inv_rev, Units.val_mul, gPos_mul, Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib]
  first | rfl | (congr 1; exact mul_comm _ _)

theorem natAct_one (F : P.Xsp) : P.natAct (fun _ => 1) F = F := by
  simp only [Places.natAct, inv_one, Units.val_one, gPos_one, Matrix.det_one, one_zpow, Finset.prod_const_one,
    one_smul, subst_one, AlgHom.toLinearMap_apply, AlgHom.id_apply]

variable (C : Level P)

theorem actX_mul (γ δ : C.Γ) (F : P.Xsp) : C.actX (γ * δ) F = C.actX γ (C.actX δ F) := by
  simp only [Level.actX, map_mul]
  exact natAct_mul _ _ F

theorem actX_one (F : P.Xsp) : C.actX 1 F = F := by
  simp only [Level.actX, map_one]
  exact natAct_one F

theorem smul_mul (γ δ : C.Γ) (L : P.Tup) : C.smul (γ * δ) L = C.smul γ (C.smul δ L) := by
  funext v
  simp only [Level.smul, map_mul, Units.val_mul, Matrix.mulVecLin_mul, ← Submodule.map_comp]
  rfl

theorem smul_one (L : P.Tup) : C.smul 1 L = L := by
  funext v
  simp only [Level.smul, map_one, Units.val_one, Matrix.mulVecLin_one]
  exact Submodule.map_id _

theorem isLatTup_smul (γ : C.Γ) {L : P.Tup} (hL : P.IsLatTup L) : P.IsLatTup (C.smul γ L) := by
  intro v
  obtain ⟨g, hg, e⟩ := hL v
  refine ⟨(C.act v γ : Matrix _ _ _) * g, ?_, ?_⟩
  · rw [Matrix.det_mul]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (C.act v γ).isUnit).mul hg
  · simp only [Level.smul, e, colSpan, Submodule.map_span, ← Set.range_comp]
    congr 2

theorem isLatTup_smul_iff (γ : C.Γ) (L : P.Tup) : P.IsLatTup (C.smul γ L) ↔ P.IsLatTup L := by
  refine ⟨fun h => ?_, isLatTup_smul C γ⟩
  have := isLatTup_smul C γ⁻¹ h
  rwa [← smul_mul, inv_mul_cancel, smul_one] at this

theorem mem_funMod_iff (Hv : P.Tup → Submodule O P.Xsp) (F : P.Tup → P.Xsp) :
    F ∈ C.funMod Hv ↔ (∀ L, P.IsLatTup L → F L ∈ Hv L) ∧ (∀ L, ¬ P.IsLatTup L → F L = 0) ∧
      ∀ γ L, F (C.smul γ L) = (C.χ γ : O) • C.actX γ (F L) := by
  simp only [Level.funMod, Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mem_ker,
    LinearMap.proj_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, sub_eq_zero, and_assoc,
    LinearMap.restrictScalars_apply]

structure IsReps {ι : Type} (rep : ι → P.Tup) : Prop where
  lat : ∀ i, P.IsLatTup (rep i)
  surj : ∀ L, P.IsLatTup L → ∃ i γ, L = C.smul γ (rep i)
  inj : ∀ i j γ, C.smul γ (rep i) = rep j → i = j

def evalReps (Hv : P.Tup → Submodule O P.Xsp) {ι : Type} {rep : ι → P.Tup} (hr : IsReps C rep) :
    C.funMod Hv →ₗ[O] ∀ i, Hv (rep i) where
  toFun F i := ⟨F.1 (rep i), ((mem_funMod_iff C Hv F.1).1 F.2).1 _ (hr.lat i)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem evalReps_injective (Hv : P.Tup → Submodule O P.Xsp) {ι : Type} {rep : ι → P.Tup} (hr : IsReps C rep) :
    Function.Injective (evalReps C Hv hr) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro F hF
  obtain ⟨-, h0, hγ⟩ := (mem_funMod_iff C Hv F.1).1 F.2
  apply Subtype.ext
  funext L
  by_cases hL : P.IsLatTup L
  · obtain ⟨i, γ, rfl⟩ := hr.surj L hL
    have : F.1 (rep i) = 0 := congrArg Subtype.val (congrFun hF i)
    rw [hγ, this, map_zero, smul_zero]
    rfl
  · exact h0 L hL

theorem evalReps_surjective (Hv : P.Tup → Submodule O P.Xsp)
    (hact : ∀ (γ : C.Γ) (L : P.Tup), P.IsLatTup L →
      (Hv L).map ((C.actX γ).restrictScalars O) = Hv (C.smul γ L))
    (htriv : C.TrivStab) {ι : Type} {rep : ι → P.Tup} (hr : IsReps C rep) :
    Function.Surjective (evalReps C Hv hr) := by
  classical
  intro x
  choose idx gam hgam using hr.surj
  let F : P.Tup → P.Xsp := fun L =>
    if h : P.IsLatTup L then (C.χ (gam L h) : O) • C.actX (gam L h) (x (idx L h) : P.Xsp) else 0
  have key : ∀ i γ, F (C.smul γ (rep i)) = (C.χ γ : O) • C.actX γ (x i : P.Xsp) := by
    intro i γ
    have h := isLatTup_smul C γ (hr.lat i)
    have e := hgam _ h
    simp only [F, dif_pos h]
    generalize idx _ h = j at e ⊢
    generalize gam _ h = δ at e ⊢
    have e' : C.smul (δ⁻¹ * γ) (rep i) = rep j := by
      rw [smul_mul, e, ← smul_mul, inv_mul_cancel, smul_one]
    obtain rfl := hr.inj _ _ _ e'
    obtain rfl : δ = γ := inv_mul_eq_one.1 (htriv _ _ (hr.lat i) e')
    rfl
  refine ⟨⟨F, (mem_funMod_iff C Hv F).2 ⟨fun L hL => ?_, fun L hL => dif_neg hL, fun γ L => ?_⟩⟩, ?_⟩
  · obtain ⟨i, γ, rfl⟩ := hr.surj L hL
    rw [key, ← hact γ _ (hr.lat i)]
    exact Submodule.smul_mem _ _ ⟨_, (x i).2, rfl⟩
  · by_cases hL : P.IsLatTup L
    · obtain ⟨i, δ, rfl⟩ := hr.surj L hL
      rw [← smul_mul, key, key, map_mul, Units.val_mul, mul_smul, actX_mul]
      congr 1
      exact (((C.actX γ).restrictScalars O).map_smul _ _).symm
    · have h1 : F L = 0 := dif_neg hL
      have h2 : F (C.smul γ L) = 0 := dif_neg (fun h => hL ((isLatTup_smul_iff C γ L).1 h))
      rw [h1, h2, map_zero, smul_zero]
  · funext i
    apply Subtype.ext
    have := key i 1
    rw [smul_one, map_one, Units.val_one, one_smul, actX_one] at this
    exact this

def evalRepsEquiv (Hv : P.Tup → Submodule O P.Xsp)
    (hact : ∀ (γ : C.Γ) (L : P.Tup), P.IsLatTup L →
      (Hv L).map ((C.actX γ).restrictScalars O) = Hv (C.smul γ L))
    (htriv : C.TrivStab) {ι : Type} {rep : ι → P.Tup} (hr : IsReps C rep) :
    C.funMod Hv ≃ₗ[O] ∀ i, Hv (rep i) :=
  LinearEquiv.ofBijective (evalReps C Hv hr) ⟨evalReps_injective C Hv hr, evalReps_surjective C Hv hact htriv hr⟩

theorem d_eq_card_mul (G : GAtP p) (hinj : Function.Injective (algebraMap G.O G.Kf)) (htriv : G.TrivStab)
    (hact : ∀ c, (G.lev c).ActHW) {ι : G.comp → Type} [∀ c, Fintype (ι c)] (rep : ∀ c, ι c → G.P.Tup)
    (hr : ∀ c, IsReps (G.lev c) (rep c)) (hfg : ∀ c i, (G.P.HtupW (rep c i)).FG) (n : ℕ)
    (hn : ∀ c i, Module.finrank G.O (G.P.HtupW (rep c i)) = n) :
    G.d = (∑ c, Fintype.card (ι c)) * n := by
  have : FaithfulSMul G.O G.Kf := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have : Module.IsTorsionFree G.O G.P.Xsp := Module.IsTorsionFree.trans G.Kf
  have : ∀ c i, Module.Finite G.O (G.P.HtupW (rep c i)) := fun c i => Module.Finite.iff_fg.2 (hfg c i)
  have : ∀ c i, Module.Free G.O (G.P.HtupW (rep c i)) := fun c i => inferInstance
  let e0 : G.M ≃ₗ[G.O] ∀ c, (G.lev c).funMod G.P.HtupW :=
    { toFun := fun F c => ⟨F.1 c, F.2 c (Set.mem_univ c)⟩
      invFun := fun F => ⟨fun c => (F c).1, fun c _ => (F c).2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e1 := e0.trans (LinearEquiv.piCongrRight fun c =>
    evalRepsEquiv (G.lev c) G.P.HtupW (hact c) (htriv c) (hr c))
  rw [GAtP.d, e1.finrank_eq, Module.finrank_pi_fintype, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Module.finrank_pi_fintype]
  simp [hn]

end GlobalTheory.ClassRank
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open scoped TensorProduct

namespace GlobalTheory.IdealPushCover

theorem mem_map_ideal_of_cover : ∀ {X Y' : Scheme.{0}} (ρ : Y' ⟶ X) [QuasiCompact ρ] (I : Y'.IdealSheafData) (U : X.affineOpens) {ι : Type} (W : ι → Y'.affineOpens) (hW : ∀ i, (W i : Y'.Opens) ≤ ρ ⁻¹ᵁ (U : X.Opens)), ρ ⁻¹ᵁ (U : X.Opens) ≤ ⨆ i, (W i : Y'.Opens) → ∀ b : Γ(X, U), (∀ i, (ρ.appLE U (W i) (hW i)).hom b ∈ I.ideal (W i)) → b ∈ (I.map ρ).ideal U := by
  intro X Y' ρ _ I U ι W hW hcov b hb
  have hk : ∀ V : Y'.affineOpens, I.ideal V = RingHom.ker (I.subschemeι.app V.1).hom := fun V => by
    rw [← Scheme.Hom.ker_apply, Scheme.IdealSheafData.ker_subschemeι]
  rw [Scheme.IdealSheafData.map, Scheme.Hom.ker_apply, RingHom.mem_ker, Scheme.Hom.comp_app]
  change (I.subschemeι.app (ρ ⁻¹ᵁ U.1)).hom ((ρ.app U.1).hom b) = 0
  refine GlobalTheory.Cartier.ext_germ fun z hz => ?_
  rw [map_zero]
  have hz' : I.subschemeι z ∈ ⨆ i, (W i : Y'.Opens) := hcov hz
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz'
  have hzi : z ∈ I.subschemeι ⁻¹ᵁ (W i : Y'.Opens) := hi
  have h0 : (I.subschemeι.app (W i).1).hom ((ρ.appLE U (W i) (hW i)).hom b) = 0 := by
    have := hb i
    rw [hk, RingHom.mem_ker] at this
    exact this
  have e1 : (ρ.appLE U (W i) (hW i)).hom b = resG Y' (hW i) ((ρ.app U.1).hom b) := rfl
  rw [e1, GlobalTheory.Cartier.app_resG] at h0
  rw [← GlobalTheory.Cartier.germ_resG (I.subschemeι.preimage_mono (hW i)) z hzi, h0, map_zero]

end GlobalTheory.IdealPushCover
end

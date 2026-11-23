module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle007
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DenseGen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.SelBaseEig
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
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

theorem UpperTheory.V.Base.gammaGen :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (U : Subgroup (G k Ω)), IsClosed (U : Set (G k Ω)) → U ≤ gamU l ⊤ → ¬ U ≤ (cycZ k Ω l).ker →
      ∃ (κ : U →* Multiplicative ℤ_[l]) (γ : U), Continuous κ ∧ Function.Surjective κ ∧ κ.ker = (cycU l U).subgroupOf U ∧
        κ γ = Multiplicative.ofAdd 1 ∧ U ≤ (Subgroup.zpowers γ.1 ⊔ cycU l U).topologicalClosure ∧ ¬ IsOfFinOrder (cycZ k Ω l γ.1) := by
  intro k Ω _ _ _ _ _ l _ U hUc hUg hUk
  have hχc : Continuous (cycZ k Ω l) := continuous_cycZ k Ω l
  have hHc : IsClosed ((U.map (cycZ k Ω l) : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) := by
    rw [Subgroup.coe_map]
    exact (hUc.isCompact.image hχc).isClosed
  have hHp : U.map (cycZ k Ω l) ≤ KStar.TotallyRealRoots.princ l (qExp l) := by
    rintro _ ⟨u, hu, rfl⟩
    have h := hUg hu
    simp only [gamU, levU, Subgroup.mem_inf, Subgroup.mem_comap] at h
    exact h.2
  have hHb : U.map (cycZ k Ω l) ≠ ⊥ := by
    intro h
    apply hUk
    intro u hu
    have hm : cycZ k Ω l u ∈ U.map (cycZ k Ω l) := ⟨u, hu, rfl⟩
    rw [h] at hm
    exact MonoidHom.mem_ker.mpr (Subgroup.mem_bot.mp hm)
  obtain ⟨⟨e⟩, htor⟩ := princZl l _ hHc hHp hHb
  let ψ : U →* U.map (cycZ k Ω l) := (cycZ k Ω l).subgroupMap U
  have hψc : Continuous ψ := by
    apply Continuous.subtype_mk
    exact hχc.comp continuous_subtype_val
  let κ : U →* Multiplicative ℤ_[l] := e.toMulEquiv.toMonoidHom.comp ψ
  have hκc : Continuous κ := e.continuous.comp hψc
  have hκs : Function.Surjective κ := e.surjective.comp (MonoidHom.subgroupMap_surjective _ U)
  have hkκ : ∀ x : U, κ x = 1 ↔ cycZ k Ω l x = 1 := by
    intro x
    have h1 : κ x = e (ψ x) := rfl
    rw [h1, map_eq_one_iff e e.injective, Subtype.ext_iff]
    exact Iff.rfl
  obtain ⟨γ, hγ⟩ := hκs (Multiplicative.ofAdd 1)
  refine ⟨κ, γ, hκc, hκs, ?_, hγ, ?_, ?_⟩
  · ext x
    rw [MonoidHom.mem_ker, hkκ, Subgroup.mem_subgroupOf]
    simp only [cycU, Subgroup.mem_inf, MonoidHom.mem_ker]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  · set V := (Subgroup.zpowers γ.1 ⊔ cycU l U).topologicalClosure with hV
    have hVc : IsClosed (V : Set (G k Ω)) := Subgroup.isClosed_topologicalClosure _
    have hsub : Subgroup.zpowers γ.1 ⊔ cycU l U ≤ V := Subgroup.le_topologicalClosure _
    have hcU : CompactSpace U := isCompact_iff_compactSpace.mp hUc.isCompact
    let S : Set U := Subtype.val ⁻¹' (V : Set (G k Ω))
    have hSc : IsClosed S := hVc.preimage continuous_subtype_val
    have hIc : IsClosed (κ '' S) := (hSc.isCompact.image hκc).isClosed
    let T : Set ℤ_[l] := Multiplicative.ofAdd ⁻¹' (κ '' S)
    have hTc : IsClosed T := hIc.preimage continuous_ofAdd
    have hTz : Set.range (Int.cast : ℤ → ℤ_[l]) ⊆ T := by
      rintro _ ⟨n, rfl⟩
      refine ⟨γ ^ n, ?_, ?_⟩
      · show ((γ ^ n : U) : G k Ω) ∈ V
        rw [Subgroup.coe_zpow]
        exact hsub (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers _ n))
      · rw [map_zpow, hγ, ← ofAdd_zsmul, zsmul_one]
    have hT : T = Set.univ := by
      apply Set.eq_univ_of_univ_subset
      rw [← PadicInt.denseRange_intCast.closure_range]
      exact closure_minimal hTz hTc
    intro u hu
    have ha : Multiplicative.toAdd (κ ⟨u, hu⟩) ∈ T := by rw [hT]; trivial
    obtain ⟨s, hs, hks⟩ := ha
    have hks' : κ s = κ ⟨u, hu⟩ := hks
    have hq : κ (⟨u, hu⟩ * s⁻¹) = 1 := by rw [map_mul, map_inv, ← hks', mul_inv_cancel]
    have hq' := (hkκ _).mp hq
    have hmem : ((⟨u, hu⟩ * s⁻¹ : U) : G k Ω) ∈ V := by
      apply hsub
      apply Subgroup.mem_sup_right
      simp only [cycU, Subgroup.mem_inf, MonoidHom.mem_ker]
      exact ⟨(⟨u, hu⟩ * s⁻¹ : U).2, hq'⟩
    have hu' : u = ((⟨u, hu⟩ * s⁻¹ : U) : G k Ω) * (s : G k Ω) := by
      simp
    rw [hu']
    exact V.mul_mem hmem hs
  · intro hfin
    have hm : cycZ k Ω l γ.1 ∈ U.map (cycZ k Ω l) := ⟨γ.1, γ.2, rfl⟩
    have h1 := (hkκ γ).mpr (htor _ hm hfin)
    rw [hγ] at h1
    exact one_ne_zero (ofAdd_eq_one.mp h1)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base


theorem UpperTheory.V.Base.inflUnique :
    ∀ (k E Ω : Type) [Field k] [NumberField k] [Field E] [NumberField E] [Field Ω] [Algebra k E] [Algebra k Ω] [Algebra E Ω]
      [IsScalarTower k E Ω] [IsAlgClosure k Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (D : LData E Ω l) (e : ℤ),
      (∀ x, ∃ y, Infl k D e x y) ∧ ∀ x x' y y', Infl k D e x y → Infl k D e x' y' → (x = x' ↔ y = y') := by
  intro k E Ω _ _ _ _ _ _ _ _ _ _ _ l _ D e
  obtain ⟨hemb, -, -⟩ := galEmbTop k E Ω
  let ψ : G E Ω →* galOf k E Ω := (galEmb k E Ω).codRestrict _ (galEmb_mem k E Ω)
  have hsurj : Function.Surjective ψ := by
    rintro ⟨τ, hτ⟩
    refine ⟨AlgEquiv.ofRingEquiv (f := τ.toRingEquiv) (fun x => hτ x), ?_⟩
    apply Subtype.ext
    ext x
    rfl
  let Ψ : G E Ω ≃* galOf k E Ω :=
    MulEquiv.ofBijective ψ ⟨fun a b h => hemb.injective (congrArg Subtype.val h), hsurj⟩
  have hΨ : ∀ σ, Ψ σ = ⟨galEmb k E Ω σ, galEmb_mem k E Ω σ⟩ := fun _ => rfl
  have hcont : Continuous (fun u : galOf k E Ω => Ψ.symm u) := by
    rw [hemb.continuous_iff]
    have hc : (galEmb k E Ω) ∘ (fun u : galOf k E Ω => Ψ.symm u) = Subtype.val := by
      funext u
      show ((Ψ (Ψ.symm u) : galOf k E Ω) : G k Ω) = u
      rw [Ψ.apply_symm_apply]
    rw [hc]
    exact continuous_subtype_val
  have hEk : ∀ σ : G E Ω, LDataCardLeFinrank.qzG k Ω l e (galEmb k E Ω σ) = LDataCardLeFinrank.qzG E Ω l e σ := by
    intro σ
    have hχ : (cycZ k Ω l ^ (-e)).comp (galEmb k E Ω) = cycZ E Ω l ^ (-e) := by
      refine MonoidHom.ext fun τ => ?_
      rw [MonoidHom.comp_apply]
      simp only [MonoidHom.zpow_apply]
      rfl
    show scalRep (QZ l) (cycZ k Ω l ^ (-e)) (galEmb k E Ω σ) = scalRep (QZ l) (cycZ E Ω l ^ (-e)) σ
    rw [← hχ]
    rfl
  have hrep : ∀ σ : G E Ω, LDataCardLeFinrank.qzG k Ω l e (galEmb k E Ω σ) = qzTw D e (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) σ) := by
    intro σ
    have h := DFunLike.congr_fun (LDataCardLeFinrank.qzTw_comp_toGS D e) σ
    rw [MonoidHom.comp_apply] at h
    rw [hEk]
    exact h.symm
  have hu : ∀ u : galOf k E Ω, (u : G k Ω) = galEmb k E Ω (Ψ.symm u) := by
    intro u
    conv_lhs => rw [← Ψ.apply_symm_apply u]
    rfl
  have hTs : Function.Surjective (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E)))) :=
    QuotientGroup.mk'_surjective _
  constructor
  · intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    let f : galOf k E Ω → QZ l := fun u => (z : GS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) → QZ l) (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) (Ψ.symm u))
    have hf : f ∈ Z1U (LDataCardLeFinrank.qzG k Ω l e) (galOf k E Ω) := by
      refine ⟨z.2.1.comp ((continuous_toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E)))).comp hcont), ?_⟩
      intro u v
      show (z : GS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) → QZ l) (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) (Ψ.symm (u * v))) =
        (z : GS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) → QZ l) (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) (Ψ.symm u)) +
          ((LDataCardLeFinrank.qzG k Ω l e).comp (galOf k E Ω).subtype u) ((z : GS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) → QZ l) (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) (Ψ.symm v)))
      rw [map_mul, map_mul, z.2.2, MonoidHom.comp_apply, Subgroup.coe_subtype, hu u, hrep]
    refine ⟨Submodule.Quotient.mk ⟨f, hf⟩, z, ⟨f, hf⟩, rfl, rfl, ?_⟩
    intro σ
    show (z : GS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) → QZ l) (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) (Ψ.symm ⟨galEmb k E Ω σ, _⟩)) = _
    rw [← hΨ, Ψ.symm_apply_apply]
  · rintro x x' y y' ⟨z1, w1, rfl, rfl, h1⟩ ⟨z2, w2, rfl, rfl, h2⟩
    rw [mk_eq_mk, Submodule.Quotient.eq, Submodule.mem_comap, Submodule.coe_subtype, mem_coboundaries1]
    apply exists_congr
    intro m
    constructor
    · intro h u
      obtain ⟨σ, rfl⟩ := Ψ.surjective u
      have h3 := h (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) σ)
      rw [Submodule.coe_sub, Pi.sub_apply] at h3
      rw [hΨ, h1, h2, h3]
      exact congrArg (fun T => T m - m) (hrep σ).symm
    · intro h g
      obtain ⟨σ, rfl⟩ := hTs g
      have h3 := h (Ψ σ)
      rw [hΨ, h1, h2] at h3
      rw [Submodule.coe_sub, Pi.sub_apply, h3]
      exact congrArg (fun T => T m - m) (hrep σ)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base TensorProduct

private theorem length_quotient_span_eq_addVal (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (x : R) (hx : x ≠ 0) :
    Module.length R (R ⧸ Ideal.span {x}) = IsDiscreteValuationRing.addVal R x := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
  rw [IsDiscreteValuationRing.addVal_def _ u hϖ m rfl, Ideal.span_singleton_mul_left_unit u.isUnit,
    ← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq,
    IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]

theorem UpperTheory.V.Base.qoExt :
    ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra ℤ_[l] O'] [Module.Finite ℤ_[l] O'] [Algebra O O'] [IsScalarTower ℤ_[l] O O'] (θ : G →* Oˣ)
      (U : Subgroup G) (𝒟 : Set (Subgroup G)),
      Module.length O' (LocSel (twist₂ l ((Units.map (algebraMap O O').toMonoidHom).comp θ)) U 𝒟) * eO l O = Module.length O (LocSel (twist₂ l θ) U 𝒟) * eO l O' ∧
      ∀ [U.Normal] (h𝒟 : ConjStable 𝒟) (W : Subgroup G) (ψ : W →* Oˣ),
        Module.length O' (selEig (twist₂ l ((Units.map (algebraMap O O').toMonoidHom).comp θ)) U h𝒟 W ((Units.map (algebraMap O O').toMonoidHom).comp ψ)) * eO l O =
          Module.length O (selEig (twist₂ l θ) U h𝒟 W ψ) * eO l O' := by
  intro l _ G _ _ _ O _ _ _ _ _ O' _ _ _ _ _ _ _ θ U 𝒟
  obtain ⟨hiO, -, hlocO, -, -, -, -, hvO, -⟩ := dvrFacts l O
  obtain ⟨hiO', -, -, -, -, -, -, hvO', -⟩ := dvrFacts l O'
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hl0 : (l : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  have hlO : (l : O) ≠ 0 := by
    intro h
    apply hl0
    apply hiO
    rw [map_natCast, h, map_zero]
  have hlmax : (l : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← map_natCast (algebraMap ℤ_[l] O),
      isUnit_map_iff]
    exact PadicInt.p_nonunit
  have hdvd : ϖ ∣ (l : O) := by
    rwa [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hlmax
  have hϖ' : algebraMap O O' ϖ ≠ 0 := by
    intro h
    obtain ⟨c, hc⟩ := hdvd
    apply hl0
    apply hiO'
    rw [map_zero, IsScalarTower.algebraMap_apply ℤ_[l] O O', map_natCast, hc, map_mul, h, zero_mul]
  have hinj : Function.Injective (algebraMap O O') := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
    rw [map_mul, map_pow] at hx
    rcases mul_eq_zero.mp hx with h | h
    · exact (u.isUnit.map (algebraMap O O')).ne_zero h
    · exact hϖ' (pow_eq_zero_iff'.mp h).1
  haveI : FaithfulSMul O O' := (faithfulSMul_iff_algebraMap_injective O O').mpr hinj
  haveI : Module.Finite O O' := Module.Finite.of_restrictScalars_finite ℤ_[l] O O'
  haveI : Module.Free O O' := Module.free_of_finite_type_torsion_free'
  haveI : IsLocalHom (algebraMap O O') := inferInstance
  have hf : Module.length O' (O' ⧸ Ideal.map (algebraMap O O') (IsLocalRing.maximalIdeal O)) * eO l O =
      eO l O' := by
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hlO hϖ
    have hlO' : ((l : O') ) = algebraMap O O' u * (algebraMap O O' ϖ) ^ n := by
      rw [← map_natCast (algebraMap O O'), hu, map_mul, map_pow]
    rw [hvO, hvO', hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, length_quotient_span_eq_addVal O' _ hϖ',
      IsDiscreteValuationRing.addVal_def _ u hϖ n hu, hlO', IsDiscreteValuationRing.addVal_mul,
      IsDiscreteValuationRing.addVal_pow,
      (IsDiscreteValuationRing.addVal_eq_zero_iff).mpr (u.isUnit.map _), zero_add, nsmul_eq_mul,
      mul_comm]
  letI : Module O (QO l O') := TensorProduct.leftModule
  haveI : IsScalarTower O O' (QO l O') :=
    (inferInstance : IsScalarTower O O' (TensorProduct ℤ_[l] O' (QZ l)))
  haveI : IsScalarTower ℤ_[l] O (QO l O') :=
    (inferInstance : IsScalarTower ℤ_[l] O (TensorProduct ℤ_[l] O' (QZ l)))
  let j : QO l O →ₗ[O] QO l O' :=
    TensorProduct.AlgebraTensorModule.map (Algebra.linearMap O O') LinearMap.id
  have hj : IsBaseChange O' j := by
    refine (QO.isBaseChange l O).of_comp ?_
    convert QO.isBaseChange l O' using 1
    apply LinearMap.ext
    intro m
    change TensorProduct.AlgebraTensorModule.map (Algebra.linearMap O O') LinearMap.id
        ((1 : O) ⊗ₜ[ℤ_[l]] m) = (1 : O') ⊗ₜ[ℤ_[l]] m
    rw [TensorProduct.AlgebraTensorModule.map_tmul, Algebra.linearMap_apply, map_one,
      LinearMap.id_apply]
  have hcomp : ∀ (g : G) (m : QO l O), j ((twist₂ l θ) g m) =
      (twist₂ l ((Units.map (algebraMap O O').toMonoidHom).comp θ)) g (j m) := by
    intro g m
    simp only [twist₂, scalRep, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.smul_apply, LinearMap.id_coe,
      id_eq, map_smul, MonoidHom.coe_comp, Function.comp_apply, Units.coe_map,
      RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    rw [algebraMap_smul]
  refine ⟨?_, ?_⟩
  · rw [selBase O G (QO l O) (twist₂ l θ) O' (QO l O') _ j hj hcomp U 𝒟, mul_assoc, hf]
  · intro _ h𝒟 W ψ
    rw [(selBaseEig O G (QO l O) (twist₂ l θ) O' (QO l O') _ j hj hcomp U 𝒟 h𝒟).1 W ψ, mul_assoc, hf]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

theorem UpperTheory.V.Base.qoBase :
    ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (χ : G →* ℤ_[l]ˣ) (U : Subgroup G) (𝒟 : Set (Subgroup G)),
      Module.length O (LocSel (twist₂ l ((Units.map (algebraMap ℤ_[l] O).toMonoidHom).comp χ)) U 𝒟) = Module.length ℤ_[l] (LocSel (scalRep (QZ l) χ) U 𝒟) * eO l O ∧
      ∀ [U.Normal] (h𝒟 : ConjStable 𝒟) (g : G) (s : ℤ_[l]),
        Module.length O (Module.End.eigenspace (selRep (twist₂ l ((Units.map (algebraMap ℤ_[l] O).toMonoidHom).comp χ)) U h𝒟 g) (algebraMap ℤ_[l] O s)) =
          Module.length ℤ_[l] (Module.End.eigenspace (selRep (scalRep (QZ l) χ) U h𝒟 g) s) * eO l O := by
  intro l _ G _ _ _ O _ _ _ _ _ χ U 𝒟
  obtain ⟨-, hfree, hloc, -, he, -⟩ := dvrFacts l O
  have hj : ∀ g m, QO.incl l O (scalRep (QZ l) χ g m) =
      twist₂ l ((Units.map (algebraMap ℤ_[l] O).toMonoidHom).comp χ) g (QO.incl l O m) := fun g m => by
    show QO.incl l O (((χ g : ℤ_[l]ˣ) : ℤ_[l]) • m) = algebraMap ℤ_[l] O (χ g : ℤ_[l]ˣ) • QO.incl l O m
    rw [map_smul, algebraMap_smul]
  rw [he]
  exact ⟨selBase ℤ_[l] G (QZ l) (scalRep (QZ l) χ) O (QO l O) _ (QO.incl l O) (QO.isBaseChange l O) hj U 𝒟,
    fun h𝒟 g s => (selBaseEig ℤ_[l] G (QZ l) (scalRep (QZ l) χ) O (QO l O) _ (QO.incl l O)
      (QO.isBaseChange l O) hj U 𝒟 h𝒟).2 g s⟩
end

section

open ReciprocityTheory.Gal UpperTheory.V.Base

private theorem H2_subsingleton_of_mulEquiv {R Q Q' N : Type} [CommRing R] [Group Q] [TopologicalSpace Q] [Group Q'] [TopologicalSpace Q']
    [AddCommGroup N] [Module R N] [TopologicalSpace N] [IsTopologicalAddGroup N] [ContinuousConstSMul R N]
    (σ : Representation R Q N) (e : Q ≃* Q') (he : Continuous e) (he' : Continuous e.symm)
    (hs : Subsingleton (H2 (σ.comp e.symm.toMonoidHom : Representation R Q' N))) : Subsingleton (H2 σ) := by
  have hc : ∀ g m, (LinearMap.id : N →ₗ[R] N) ((σ.comp e.symm.toMonoidHom : Representation R Q' N) (e.toMonoidHom g) m)
      = σ g ((LinearMap.id : N →ₗ[R] N) m) := fun g m => by simp
  have hsurj : Function.Surjective
      (compatiblePairH2 (σ.comp e.symm.toMonoidHom : Representation R Q' N) σ e.toMonoidHom he LinearMap.id continuous_id hc) := by
    intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    refine ⟨Submodule.Quotient.mk (restrictCocycles2 σ e.symm.toMonoidHom he' z), ?_⟩
    show Submodule.Quotient.mk (compatiblePairCocycles2 _ σ e.toMonoidHom he LinearMap.id continuous_id hc _) = _
    congr 1
    refine Subtype.ext (funext fun p => ?_)
    obtain ⟨g, h⟩ := p
    show z.1 (e.symm (e g), e.symm (e h)) = _
    simp
  exact hsurj.subsingleton

private theorem cont_quot {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup M] [Module R M] [TopologicalSpace M]
    (ρ : Representation R G M) (hρ : ReciprocityTheory.Gal.ContAction ρ) (S : Subgroup G) [S.Normal] :
    ReciprocityTheory.Gal.ContAction (ρ.quotientToInvariants S) := by
  unfold ReciprocityTheory.Gal.ContAction
  have hq := (QuotientGroup.isOpenQuotientMap_mk (N := S)).prodMap
    (IsOpenQuotientMap.id (X := Representation.invariants (ρ.comp S.subtype)))
  rw [← hq.continuous_comp_iff]
  refine Continuous.subtype_mk (f := fun p : G × Representation.invariants (ρ.comp S.subtype) => ρ p.1 p.2.1) ?_ _
  exact hρ.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

private theorem H2_quotientToInvariants_subsingleton_of_zl_quotient (l : ℕ) [Fact l.Prime] {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousConstSMul R M] [DiscreteTopology M]
    (ρ : Representation R G M) (hρ : ReciprocityTheory.Gal.ContAction ρ) (hl : ∀ m : M, ∃ n : ℕ, l ^ n • m = 0) (S : Subgroup G) [S.Normal]
    (κ : G →* Multiplicative ℤ_[l]) (hκ : Continuous κ) (hs : Function.Surjective κ) (hk : κ.ker = S) :
    Subsingleton (H2 (ρ.quotientToInvariants S)) := by
  let e : G ⧸ S ≃* Multiplicative ℤ_[l] :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans (QuotientGroup.quotientKerEquivOfSurjective κ hs)
  have he : Continuous e := by
    rw [← (QuotientGroup.isOpenQuotientMap_mk (N := S)).continuous_comp_iff]
    exact hκ
  have he' : Continuous e.symm := (Continuous.homeoOfEquivCompactToT2 (f := e.toEquiv) he).symm.continuous
  refine H2_subsingleton_of_mulEquiv _ e he he' (h2Zl l R _ _ ?_ ?_)
  · exact (cont_quot ρ hρ S).comp ((he'.comp continuous_fst).prodMk continuous_snd)
  · intro m
    obtain ⟨n, hn⟩ := hl m.1
    exact ⟨n, Subtype.ext (by simpa using hn)⟩

theorem UpperTheory.V.Base.resZl :
    ∀ (l : ℕ) [Fact l.Prime], ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M) [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G], ContAction ρ → (∀ m : M, ∃ n : ℕ, l ^ n • m = 0) →
      ∀ (U' U : Subgroup G) [U'.Normal] (h : U' ≤ U), IsClosed (U : Set G) → ∀ κ : U →* Multiplicative ℤ_[l], Continuous κ →
      Function.Surjective κ → κ.ker = U'.subgroupOf U → invariantsUnderSubgroupH1 ρ U U' ≤ LinearMap.range (resU ρ h) := by
  intro l _ R G M _ _ _ _ _ _ _ _ _ _ ρ _ _ _ hρ hl U' U _ h hU κ hκ hs hk
  haveI : CompactSpace U := isCompact_iff_compactSpace.1 hU.isCompact
  have hρU : ReciprocityTheory.Gal.ContAction (ρ.comp U.subtype : Representation R U M) :=
    hρ.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  haveI : Subsingleton (H2 (quotRep ρ U U')) := H2_quotientToInvariants_subsingleton_of_zl_quotient l _ hρU hl _ κ hκ hs hk
  have hc : IsClosed (U'.subgroupOf U : Set U) := by
    rw [← hk]
    exact isClosed_singleton.preimage hκ
  have hc' : IsClosed (U' : Set G) := by
    have := hU.isClosedEmbedding_subtypeVal.isClosedMap _ hc
    convert this using 1
    ext x
    exact ⟨fun hx => ⟨⟨x, h hx⟩, hx, rfl⟩, fun ⟨y, hy, e⟩ => e ▸ hy⟩
  obtain ⟨tg, htg⟩ := transg R G M ρ hρ U' U h hU hc'
  intro x hx
  have h0 : (Submodule.Quotient.mk ⟨x, hx⟩ : resCoker ρ h) = 0 := htg (Subsingleton.elim _ _)
  exact Submodule.mem_comap.1 ((Submodule.Quotient.mk_eq_zero _).1 h0)
end

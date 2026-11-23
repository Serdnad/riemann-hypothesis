module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.Bundle003
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsConj
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.Bundle001
public import GroundTheory.GlobalFields.CyclotomicCharacters.PadicUnitsLog
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle062
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
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

private theorem mem_nhds_one_gal_iff_exists_finset_fixing (K L : Type) [Field K] [Field L] [Algebra K L] [Algebra.IsIntegral K L]
    (s : Set Gal(L/K)) :
    s ∈ nhds (1 : Gal(L/K)) ↔ ∃ S : Finset L, {σ : Gal(L/K) | ∀ x ∈ S, σ x = x} ⊆ s := by
  classical
  constructor
  · intro hs
    obtain ⟨F, hF, hFs⟩ := (krullTopology_mem_nhds_one_iff K L s).mp hs
    let b := Module.finBasis K F
    refine ⟨Finset.univ.image (fun i => (b i : L)), fun σ hσ => hFs ?_⟩
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    have hb : ∀ i, σ (b i : L) = b i := fun i => hσ _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    have hy' : y = ∑ i, (b.repr ⟨y, hy⟩ i) • (b i : L) := by
      have h := congrArg (fun z : F => (z : L)) (b.sum_repr ⟨y, hy⟩)
      simp only [IntermediateField.coe_sum, IntermediateField.coe_smul] at h
      exact h.symm

    rw [hy', map_sum]
    simp [map_smul, hb]
  · rintro ⟨S, hS⟩
    refine Filter.mem_of_superset ?_ hS
    have : {σ : Gal(L/K) | ∀ x ∈ S, σ x = x} =
        ⋂ x ∈ S, (MulAction.stabilizer Gal(L/K) x : Set Gal(L/K)) := by
      ext σ
      simp [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
    rw [this]
    exact (isOpen_biInter_finset fun x _ => stabilizer_isOpen_of_isIntegral x).mem_nhds (by simp)

theorem UpperTheory.V.Base.galEmbTop :
    ∀ (k E Ω : Type) [Field k] [NumberField k] [Field E] [NumberField E] [Field Ω] [Algebra k E] [Algebra k Ω] [Algebra E Ω]
      [IsScalarTower k E Ω] [IsAlgClosure k Ω] [IsAlgClosure E Ω],
      Topology.IsEmbedding (galEmb k E Ω) ∧ IsOpen (galOf k E Ω : Set (G k Ω)) ∧ (galOf k E Ω).index = Module.finrank k E := by
  intro k E Ω
  intros
  have hE : FiniteDimensional k E := Module.Finite.of_restrictScalars_finite ℚ k E
  let L : IntermediateField k Ω := (IsScalarTower.toAlgHom k E Ω).fieldRange
  have hL : FiniteDimensional k L :=
    LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom k E Ω)).toLinearEquiv
  have hset : galOf k E Ω = L.fixingSubgroup := by
    ext σ
    rw [IntermediateField.mem_fixingSubgroup_iff]
    show (∀ x : E, σ (algebraMap E Ω x) = algebraMap E Ω x) ↔ _
    constructor
    · rintro h y ⟨x, rfl⟩
      simpa using h x
    · intro h x
      simpa using h _ ⟨x, rfl⟩
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [IsTopologicalGroup.isInducing_iff_nhds_one]
    ext s
    rw [Filter.mem_comap]
    constructor
    · intro hs
      obtain ⟨S, hS⟩ := (mem_nhds_one_gal_iff_exists_finset_fixing E Ω s).mp hs
      exact ⟨{σ : G k Ω | ∀ x ∈ S, σ x = x}, (mem_nhds_one_gal_iff_exists_finset_fixing k Ω _).mpr ⟨S, subset_rfl⟩,
        fun σ hσ => hS hσ⟩
    · rintro ⟨t, ht, hts⟩
      obtain ⟨S, hS⟩ := (mem_nhds_one_gal_iff_exists_finset_fixing k Ω t).mp ht
      exact (mem_nhds_one_gal_iff_exists_finset_fixing E Ω s).mpr ⟨S, fun σ hσ => hts (hS hσ)⟩
  · intro σ τ h
    ext x
    exact DFunLike.congr_fun h x
  · rw [hset]
    exact L.fixingSubgroup_isOpen
  · rw [hset, ← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom k E Ω)).toLinearEquiv.finrank_eq.symm
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

private theorem cont_smul (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] (Γ : Type) [Group Γ]
    [TopologicalSpace Γ] (χ : Γ →* ℤ_[l]ˣ) (hχ : Continuous fun g => ((χ g : ℤ_[l]ˣ) : ℤ_[l])) (m : QO l O) :
    Continuous fun g => ((χ g : ℤ_[l]ˣ) : ℤ_[l]) • m := by
  refine (QO.isBaseChange l O).inductionOn m
    (motive := fun m => Continuous fun g => ((χ g : ℤ_[l]ˣ) : ℤ_[l]) • m) ?_ ?_ ?_
  · intro x
    have h1 : Continuous fun g => ((χ g : ℤ_[l]ˣ) : ℤ_[l]) • x :=
      Continuous.comp (LDataCardLeFinrank.contScal l Γ χ hχ) (Continuous.prodMk_left x)
    have h2 : Continuous (QO.incl l O) := continuous_of_discreteTopology
    refine (h2.comp h1).congr fun g => ?_
    exact map_smul (QO.incl l O) _ x
  · intro s x hx
    have h2 : Continuous fun y : QO l O => s • y := continuous_of_discreteTopology
    exact (h2.comp hx).congr fun g => smul_comm _ _ _
  · intro x y hx hy
    exact (hx.add hy).congr fun g => (smul_add _ _ _).symm

private theorem locConst {Γ A : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group A] (ψ : Γ →* A)
    (h : IsOpen (ψ.ker : Set Γ)) : IsLocallyConstant ψ :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantFunctions.locConst ψ h

theorem UpperTheory.V.Base.contTw :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime],
      Continuous (cycZ k Ω l) ∧ (∀ e : ℤ, ContAction (UpperTheory.V.LDataCardLeFinrank.qzG k Ω l e)) ∧
      ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] (ψ : G k Ω →* Oˣ) (n : ℤ), IsOpen (ψ.ker : Set (G k Ω)) →
        ContAction (twist₂ l (ψ * chiO (k := k) (Ω := Ω) l O ^ n)) := by
  intro k Ω _ _ _ _ _ l _
  have hc := ReciprocityTheory.Gal.continuous_cycZ k Ω l
  have hcPow (n : ℤ) : Continuous fun g : G k Ω => (((cycZ k Ω l ^ n) g : ℤ_[l]ˣ) : ℤ_[l]) :=
    Units.continuous_val.comp
      (show Continuous fun g : G k Ω => cycZ k Ω l g ^ n from hc.zpow n)
  refine ⟨hc, fun e => LDataCardLeFinrank.contScal l _ (cycZ k Ω l ^ (-e)) (hcPow (-e)),
    fun O _ _ ψ n hψ => ?_⟩
  refine continuous_prod_of_discrete_right.2 fun m => ?_
  have h1 := cont_smul l O _ (cycZ k Ω l ^ n) (hcPow n) m
  have h2 := ((locConst ψ hψ).prodMk ((IsLocallyConstant.iff_continuous _).2 h1)).comp
    fun p : Oˣ × QO l O => (p.1 : O) • p.2
  refine h2.continuous.congr fun g => ?_
  show (ψ g : O) • (((cycZ k Ω l g ^ n : ℤ_[l]ˣ) : ℤ_[l]) • m) =
    ((ψ g * chiO (k := k) (Ω := Ω) l O g ^ n : Oˣ) : O) • m
  have e : chiO (k := k) (Ω := Ω) l O g ^ n = Units.map (algebraMap ℤ_[l] O).toMonoidHom (cycZ k Ω l g ^ n) :=
    (map_zpow (Units.map (algebraMap ℤ_[l] O).toMonoidHom) (cycZ k Ω l g) n).symm
  rw [Units.val_mul, mul_smul, e]
  exact congrArg _ (algebraMap_smul O _ m).symm
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

theorem UpperTheory.V.Base.galQuot :
    ∀ (k E Ω : Type) [Field k] [NumberField k] [Field E] [NumberField E] [Field Ω] [Algebra k E] [Algebra k Ω] [Algebra E Ω]
      [IsScalarTower k E Ω] [IsAlgClosure k Ω] [IsAlgClosure E Ω] [Normal k E],
      Function.Surjective (AlgEquiv.restrictNormalHom E : G k Ω →* (E ≃ₐ[k] E)) ∧
      (AlgEquiv.restrictNormalHom E : G k Ω →* (E ≃ₐ[k] E)).ker = galOf k E Ω ∧
      ∀ σ : G k Ω, IsLift (AlgEquiv.restrictNormalHom E σ : E ≃ₐ[k] E).toRingEquiv σ.toRingEquiv := by
  intro k E Ω _ _ _ _ _ _ _ _ _ _ _ _
  have hN : Normal k Ω := IsAlgClosure.normal k Ω
  have hc : ∀ (σ : G k Ω) (x : E),
      σ (algebraMap E Ω x) = algebraMap E Ω (AlgEquiv.restrictNormalHom E σ x) := by
    intro σ x
    exact (AlgEquiv.restrictNormal_commutes σ E x).symm
  refine ⟨AlgEquiv.restrictNormalHom_surjective Ω, ?_, ?_⟩
  · ext σ
    rw [MonoidHom.mem_ker]
    change _ ↔ ∀ x : E, σ (algebraMap E Ω x) = algebraMap E Ω x
    constructor
    · intro h x
      rw [hc, h]
      rfl
    · intro h
      ext x
      apply (algebraMap E Ω).injective
      rw [← hc, h]
      rfl
  · intro σ x
    exact hc σ x
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

theorem UpperTheory.V.Base.inflAct :
    ∀ (k E Ω : Type) [Field k] [NumberField k] [Field E] [NumberField E] [Field Ω] [Algebra k E] [Algebra k Ω] [Algebra E Ω]
      [IsScalarTower k E Ω] [IsAlgClosure k Ω] [IsAlgClosure E Ω] [Normal k E] (l : ℕ) [Fact l.Prime] (D : LData E Ω l) (e : ℤ) (τ : E ≃+* E) (σ : G k Ω), IsLift τ σ.toRingEquiv →
      ∀ x y, Infl k D e x y → Infl k D e (galoisActionOnCohomology D e τ x) (conjRep (LDataCardLeFinrank.qzG k Ω l e) (galOf k E Ω) σ y) := by
  intro k E Ω _ _ _ _ _ _ _ _ _ _ _ _ l _ D e τ σ h x y hxy
  obtain ⟨z, z', rfl, rfl, hz⟩ := hxy
  obtain ⟨z₁, e₁, f₁⟩ := exists_cocycle_h1TwistConjByLift_mk_eq_mk D e h z
  obtain ⟨z₂, e₂, f₂⟩ := conjU_mk (LDataCardLeFinrank.qzG k Ω l e) (galOf k E Ω) σ z'
  refine ⟨z₁, z₂, by rw [galois_action_cohomology_eq_conj D e h, e₁], by rw [conjRep_apply, e₂], fun g => ?_⟩
  have hc : conjHom (galOf k E Ω) σ ⟨galEmb k E Ω g, galEmb_mem k E Ω g⟩ =
      ⟨galEmb k E Ω (conjGal h g), galEmb_mem k E Ω _⟩ := Subtype.ext (AlgEquiv.ext fun _ => rfl)
  rw [f₂, f₁, conjGS_toGS, hc, hz]
  rfl
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

theorem UpperTheory.V.Base.princZl :
    ∀ (l : ℕ) [Fact l.Prime] (H : Subgroup ℤ_[l]ˣ), IsClosed (H : Set ℤ_[l]ˣ) → H ≤ KStar.TotallyRealRoots.princ l (qExp l) → H ≠ ⊥ →
      Nonempty (H ≃ₜ* Multiplicative ℤ_[l]) ∧ ∀ u ∈ H, IsOfFinOrder u → u = 1 := by
  intro l _ H hHc hHp hH1
  have tors : ∀ u ∈ H, IsOfFinOrder u → u = 1 := by
    intro u hu hfin
    have hpr := hHp hu
    have hmem : u ∈ CommGroup.torsion ℤ_[l]ˣ := (CommGroup.mem_torsion u).2 hfin
    by_cases h2 : l = 2
    · subst h2
      rcases (GroundTheory.Global.Cyclotomic.mem_torsion_two_iff u).1 hmem with h | h
      · exact h
      · exfalso
        rw [KStar.TotallyRealRoots.mem_princ, h] at hpr
        obtain ⟨c, hc⟩ := hpr
        have hc2 : (2 : ℤ_[2]) * (1 + 2 * c) = 0 := by
          push_cast [qExp] at hc
          linear_combination -hc
        have h2ne : (2 : ℤ_[2]) ≠ 0 := two_ne_zero
        have h1 : (1 : ℤ_[2]) + 2 * c = 0 := (mul_eq_zero.1 hc2).resolve_left h2ne
        have hn : ‖(2 : ℤ_[2]) * c‖ = 1 := by
          rw [show (2 : ℤ_[2]) * c = -1 by linear_combination h1, norm_neg, norm_one]
        have hn2 : ‖(2 : ℤ_[2])‖ = 1 / 2 := by
          have := PadicInt.norm_p (p := 2)
          norm_num at this ⊢
          exact this
        rw [norm_mul, hn2] at hn
        have := PadicInt.norm_le_one c
        linarith
    · have ht : u ^ GroundTheory.Global.Cyclotomic.torsionExponent l = 1 :=
        (GroundTheory.Global.Cyclotomic.mem_torsion_iff l u).1 hmem
      have hq : qExp l = 1 := by simp [qExp, h2]
      rw [hq] at hpr
      have hte : GroundTheory.Global.Cyclotomic.torsionExponent l = l - 1 := by
        simp [GroundTheory.Global.Cyclotomic.torsionExponent, h2]
      rw [hte] at ht
      have hl := (Fact.out : l.Prime).two_le
      refine KStar.TotallyRealRoots.eq_one_of_mem_princ_one (o := l - 1) ?_ ?_ hpr
      · intro hd
        have := Nat.le_of_dvd (by omega) hd
        omega
      · rw [mem_rootsOfUnity]
        exact ht
  refine ⟨?_, tors⟩
  classical
  let L : ℤ_[l]ˣ →* Multiplicative ℤ_[l] := GroundTheory.Global.Cyclotomic.padicUnitsLog l
  have hker : L.ker = CommGroup.torsion ℤ_[l]ˣ := GroundTheory.Global.Cyclotomic.ker_padicUnitsLog l
  let f : H → ℤ_[l] := fun h => Multiplicative.toAdd (L h)
  have hfc : Continuous f :=
    (GroundTheory.Global.Cyclotomic.continuous_padicUnitsLog l).comp continuous_subtype_val
  have hmul : ∀ a b : H, f (a * b) = f a + f b := by
    intro a b
    simp [f, L]
  have hpow : ∀ (a : H) (n : ℤ), f (a ^ n) = n * f a := by
    intro a n
    simp [f, L, zsmul_eq_mul]
  have hf1 : f 1 = 0 := by simp [f, L]
  have hinj : Function.Injective f := by
    intro a b hab
    have hL : L a = L b := hab
    have hk : (a : ℤ_[l]ˣ) * (b : ℤ_[l]ˣ)⁻¹ ∈ L.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hL, mul_inv_cancel]
    rw [hker, CommGroup.mem_torsion] at hk
    have := tors _ (H.mul_mem a.2 (H.inv_mem b.2)) hk
    exact Subtype.ext (mul_inv_eq_one.1 this)
  haveI : CompactSpace H := isCompact_iff_compactSpace.1 hHc.isCompact
  have hcl : IsClosed (Set.range f) := (isCompact_range hfc).isClosed
  let I : Ideal ℤ_[l] :=
    { carrier := Set.range f
      add_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
        exact ⟨a * b, hmul a b⟩
      zero_mem' := ⟨1, hf1⟩
      smul_mem' := by
        rintro c _ ⟨a, rfl⟩
        have hm : Continuous (fun t : ℤ_[l] => t * f a) := continuous_mul_const (f a)
        have hsub := hm.range_subset_closure_image_dense (PadicInt.denseRange_intCast (p := l))
        have himg : (fun t : ℤ_[l] => t * f a) '' Set.range (Int.cast : ℤ → ℤ_[l]) ⊆ Set.range f := by
          rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
          exact ⟨a ^ n, hpow a n⟩
        exact closure_minimal himg hcl (hsub ⟨c, rfl⟩) }
  have hI : ∀ y, y ∈ Set.range f ↔ ∃ c, c * Submodule.IsPrincipal.generator I = y := by
    intro y
    have h : y ∈ I ↔ y ∈ Ideal.span {Submodule.IsPrincipal.generator I} := by
      rw [Ideal.span_singleton_generator]
    rw [Ideal.mem_span_singleton'] at h
    exact h
  set g := Submodule.IsPrincipal.generator I with hgdef
  obtain ⟨a0, ha0⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hH1
  have hg0 : g ≠ 0 := by
    intro hg
    obtain ⟨c, hc⟩ := (hI (f a0)).1 ⟨a0, rfl⟩
    rw [hg, mul_zero, ← hf1] at hc
    exact ha0 (hinj hc).symm
  let e : H → ℤ_[l] := fun h => Classical.choose ((hI (f h)).1 ⟨h, rfl⟩)
  have he : ∀ h, e h * g = f h := fun h => Classical.choose_spec ((hI (f h)).1 ⟨h, rfl⟩)
  have hminj : Function.Injective (fun t : ℤ_[l] => t * g) := mul_left_injective₀ hg0
  have hmemb := ((continuous_mul_const g).isClosedEmbedding hminj).isEmbedding
  have hec : Continuous e := by
    rw [hmemb.continuous_iff]
    have : ((fun t : ℤ_[l] => t * g) ∘ e) = f := funext he
    rw [this]
    exact hfc
  have hemul : ∀ a b : H, e (a * b) = e a + e b := by
    intro a b
    apply hminj
    simp only
    rw [he, add_mul, he, he, hmul]
  have heinj : Function.Injective e := by
    intro a b hab
    apply hinj
    rw [← he, ← he, hab]
  have hesurj : Function.Surjective e := by
    intro c
    obtain ⟨h, hh⟩ := (hI (c * g)).2 ⟨c, rfl⟩
    refine ⟨h, hminj ?_⟩
    simp only
    rw [he, hh]
  let φ : H →* Multiplicative ℤ_[l] :=
    MonoidHom.mk' (fun h => Multiplicative.ofAdd (e h)) (by
      intro a b
      rw [hemul]
      rfl)
  let E : H ≃* Multiplicative ℤ_[l] := MulEquiv.ofBijective φ ⟨heinj, hesurj⟩
  have hEc : Continuous E := hec
  let Φ := Continuous.homeoOfEquivCompactToT2 (f := E.toEquiv) hEc
  exact ⟨{ toMulEquiv := E, continuous_toFun := hEc, continuous_invFun := Φ.symm.continuous }⟩
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

private theorem norm_le_one_of_int (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) :
    ‖x‖ ≤ 1 :=
  _root_.UpperTheory.Reformulated.B.NormLeOneOfIsIntegral.norm_le_one_of_isIntegral l x hx

theorem UpperTheory.V.Base.normO :
    ∀ (l : ℕ) [Fact l.Prime] (O : Subalgebra ℤ_[l] (PadicAlgCl l)) [IsDiscreteValuationRing O] [Module.Finite ℤ_[l] O] (a : O), a ≠ 0 →
      ‖(a : PadicAlgCl l)‖ ^ (eO l O).toNat = ((l : ℝ)⁻¹) ^ (IsDiscreteValuationRing.addVal O a).toNat := by
  intro l _ O _ _ a ha
  have hle : ∀ x : O, ‖(x : PadicAlgCl l)‖ ≤ 1 := fun x =>
    norm_le_one_of_int l _ ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) x).map O.val)
  have hu : ∀ u : Oˣ, ‖((u : O) : PadicAlgCl l)‖ = 1 := by
    intro u
    have h1 : ‖((u : O) : PadicAlgCl l)‖ * ‖((u⁻¹ : Oˣ) : O).1‖ = 1 := by
      rw [← norm_mul, ← Subalgebra.coe_mul, Units.mul_inv]; simp
    have h2 := hle u
    have h3 := hle (u⁻¹ : Oˣ)
    have h4 := norm_nonneg ((u : O) : PadicAlgCl l)
    nlinarith
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have key : ∀ x : O, x ≠ 0 → ‖(x : PadicAlgCl l)‖ = ‖(ϖ : PadicAlgCl l)‖ ^ (IsDiscreteValuationRing.addVal O x).toNat := by
    intro x hx
    obtain ⟨n, u, h⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
    rw [IsDiscreteValuationRing.addVal_def x u hϖ n h, h]
    simp [hu]
  have hl0 : (l : O) ≠ 0 := by
    intro h
    have h' : ((l : O) : PadicAlgCl l) = 0 := by rw [h]; rfl
    have : (l : PadicAlgCl l) = 0 := by simpa using h'
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) this
  have hl : ‖((l : O) : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
    have : ((l : O) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [this, norm_algebraMap', Padic.norm_p]
  have he : eO l O = IsDiscreteValuationRing.addVal O (l : O) := Ring.ord_eq_addVal (l : O)
  rw [he, ← hl, key a ha, key _ hl0, ← pow_mul, ← pow_mul, mul_comm]
end

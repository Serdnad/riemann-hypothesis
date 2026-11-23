module

public import GroundTheory.LocalFields.LocalArtinMap
public import GroundTheory.ProfiniteCohomology.CupProducts
public import GroundTheory.ProfiniteCohomology.LocalClassFormation.InvariantSplit
public import GroundTheory.ProfiniteCohomology.PoincareDuality.Torsion
public import GroundTheory.ProfiniteCohomology.Bundle010
public import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbol
public import GroundTheory.ProfiniteCohomology.LocalTateDuality.Bockstein
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle348
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Formalism.ConjugateSelfDual.Bundle001
public import GroundTheory.ProfiniteCohomology.CyclicCup
public import GroundTheory.ProfiniteCohomology.Bundle009
import ReciprocityTheory.GaloisValuations.GlobalA
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle317
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle335
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle313
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.EPGFalseEqLastIff
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.TwKerLeComapOf
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipApplyCastSuccLast
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.Index
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.Topology.Algebra.OpenSubgroup

@[expose] public section

section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GroundTheory.ProfCoh GroundTheory.LocalField ValuativeRel CategoryTheory
set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.KummerCupInv

attribute [local instance 2000] Rep.hV2

theorem pow_identity {F : Type} [Field F] {n m p q r s : ℕ} {ζ y : F} (hy : y ≠ 0) (hζ : ζ ^ n = 1)
    (h : s + q = n * m + r) :
    (ζ ^ p * y) ^ q / y ^ r * y ^ s = ζ ^ ((p * q) % n) * (y ^ n) ^ m := by
  have e : y ^ s * y ^ q = (y ^ n) ^ m * y ^ r := by
    rw [← pow_add, ← pow_mul, ← pow_add, h]
  rw [mul_pow, ← pow_mul, ← pow_eq_pow_mod _ hζ]
  have hr : y ^ r ≠ 0 := pow_ne_zero _ hy
  field_simp
  linear_combination (ζ ^ (p * q)) * e

theorem kummer_key {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {n m p q r s k : ℕ} (ζ y u : Ωˣ)
    (g : Ω ≃ₐ[K] Ω) (hζ : ζ ^ n = 1) (hu : (u : Ω) = (y : Ω) ^ n)
    (hg : g (y : Ω) = (ζ : Ω) ^ p * y) (hk : k = (p * q) % n) (h : s + q = n * m + r) :
    (Additive.ofMul (ζ ^ k) + (m : ℤ) • Additive.ofMul u : Additive Ωˣ) =
      Additive.ofMul (galUnitsHom K Ω g (y ^ q)) - Additive.ofMul (y ^ r) +
        Additive.ofMul (y ^ s) := by
  apply Additive.toMul.injective
  simp only [natCast_zsmul, toMul_nsmul, toMul_add, toMul_sub, toMul_ofMul]
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_div_eq_div_val,
    coe_galUnitsHom_apply, map_pow, hg]
  rw [hu, pow_identity y.ne_zero (by rw [← Units.val_pow_eq_pow_val, hζ, Units.val_one]) h, hk]

theorem unramifiedDegree_liftNormal_localArtinMap {K Ω : Type} [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω]
    {a : Kˣ} (ha : ord (a : K) = 1) :
    unramifiedDegree K Ω ((localArtinMap K Ω a).liftNormal Ω) = Multiplicative.ofAdd 1 := by
  rw [← restrictNormal_eq_maximalUnramifiedExtensionFrobenius_iff]
  ext y
  have h1 := AlgEquiv.restrictNormal_commutes ((localArtinMap K Ω a).liftNormal Ω)
    (maximalUnramifiedExtension K Ω) y
  have h2 := AlgEquiv.liftNormal_commutes (localArtinMap K Ω a) Ω
    ⟨(y : Ω), maximalUnramifiedExtension_le_maximalAbelianExtension y.2⟩
  have h3 := localArtinMap_uniformizer_apply (Ω := Ω) ha y.2
  simp only [IntermediateField.algebraMap_apply] at h1 h2
  rw [h1, h2]
  exact h3

theorem inv_kummerCup : ∀ (K Ω : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω] (n : ℕ) [NeZero n] (ζ y : Ωˣ) (a : Kˣ), ζ ^ n = 1 → ord (a : K) = 1 → (y : Ω) ^ n = algebraMap K Ω a → ∀ (κ χ : Gal(Ω/K) → ZMod n), (∀ g : Gal(Ω/K), g (y : Ω) = (ζ : Ω) ^ (κ g).val * y) → (∀ g h, χ (g * h) = χ g + χ h) → Continuous χ → (∀ g, unramifiedDegree K Ω g = Multiplicative.ofAdd 1 → χ g = 1) → ∀ x : cocycles (galUnits.{0} K Ω) 2, (∀ s : Fin 2 → Gal(Ω/K), cochainOf _ (cocycleι _ 2 x) s = Additive.ofMul (ζ ^ (κ (s 0) * χ (s 1)).val)) → brauerInv K Ω (cohomologyπ _ 2 x) = - zmodToQZ n 1 := by
  intro K Ω _ _ _ _ _ _ _ _ _ _ _ n _ ζ y a hζ hord hy κ χ hκ hadd hcont hdeg x hx
  have hlc : IsLocallyConstant χ := (IsLocallyConstant.iff_continuous χ).2 hcont
  let ψ : Additive Gal(Ω/K) →ₜ+ QZ :=
    { toFun := fun σ => zmodToQZ n (χ (Additive.toMul σ))
      map_zero' := by
        have h1 : χ 1 = 0 := by simpa using hadd 1 1
        simp [h1]
      map_add' := fun σ τ => by simp [hadd]
      continuous_toFun :=
        ((hlc.comp_continuous continuous_toMul).comp (zmodToQZ n)).continuous }
  let z : cocycles (galUnitsZ K Ω) 2 := cocyclesULiftInt (galUnits.{0} K Ω) x
  obtain ⟨w, hw, hwc⟩ := exists_cocycle_cupCharClassProf (galUnitsZ K Ω) ψ (unitsInvariant K Ω a)
  let f : Gal(Ω/K) → galUnitsZ K Ω := fun g => Additive.ofMul (y ^ (χ g).val)
  have hf : IsLocallyConstant f := hlc.comp fun c : ZMod n => (Additive.ofMul (y ^ c.val) : galUnitsZ K Ω)
  have hz : cohomologyπ (galUnitsZ K Ω) 2 (z + w) = 0 := by
    refine (cohomologyπ_two_eq_zero_iff _ _).2 ⟨f, hf, fun g h => ?_⟩
    have ez : cochainOf (galUnitsZ K Ω) (cocycleι _ 2 z) ![g, h] =
        Additive.ofMul (ζ ^ (κ g * χ h).val) :=
      (congrFun (cochainOf_cocycleι_cocyclesULiftInt (galUnits.{0} K Ω) x) ![g, h]).trans (hx _)
    set m : ℕ := ((χ g).val + (χ h).val) / n with hm
    have em : charCocycle (charAdd ψ) ((![g, h] : Fin 2 → Gal(Ω/K)) 0, (![g, h] : Fin 2 → Gal(Ω/K)) 1) =
        (m : ℤ) :=
      charCocycle_eq_bockInt χ (charAdd ψ) (fun _ => rfl) g h
    have hsum : (χ g).val + (χ h).val = n * m + (χ (g * h)).val := by
      rw [hadd, ZMod.val_add]
      exact (Nat.div_add_mod _ _).symm
    let u : Ωˣ := Units.map (algebraMap K Ω : K →* Ω) a
    have key := kummer_key ζ y u g hζ (show (u : Ω) = (y : Ω) ^ n from hy.symm) (hκ g)
      (show (κ g * χ h).val = ((κ g).val * (χ h).val) % n from ZMod.val_mul _ _) hsum
    rw [map_add (f := _), cochainOf_add, Pi.add_apply, ez, hwc, em]
    exact key
  have e1 : cohomologyULiftIntAddEquiv (galUnits.{0} K Ω) 2 (cohomologyπ _ 2 x) =
      cohomologyπ (galUnitsZ K Ω) 2 z :=
    cohomologyULiftIntAddEquiv_cohomologyπ' _ x
  have e2 : brauerInv K Ω (cohomologyπ _ 2 x) = brauerInvZ K Ω (cohomologyπ (galUnitsZ K Ω) 2 z) := by
    rw [← e1, brauerInvZ_cohomologyULiftIntAddEquiv]
  have e3 : cohomologyπ (galUnitsZ K Ω) 2 z + galCupClass K Ω ψ a = 0 := by
    rw [galCupClass, ← hw, ← map_add (f := _)]
    exact hz
  have e4 := brauerInvZ_galCupClass_liftNormal ψ a
  have e5 : ψ (Additive.ofMul ((localArtinMap K Ω a).liftNormal Ω)) = zmodToQZ n 1 := by
    change zmodToQZ n (χ ((localArtinMap K Ω a).liftNormal Ω)) = _
    rw [hdeg _ (unramifiedDegree_liftNormal_localArtinMap hord)]
  have e6 := congrArg (brauerInvZ K Ω) e3
  rw [map_add (f := _), map_zero, e4, e5] at e6
  rw [e2]
  exact eq_neg_of_add_eq_zero_left e6

end GlobalTheory.CompanionTheory.KummerCupInv
end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO

theorem exists_compactOpen_between_mul_small
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hbase : ∀ O ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (K₀ C : Subgroup G) (hK₀o : IsOpen (K₀ : Set G)) (hK₀c : IsCompact (K₀ : Set G)) (hC : C ≤ K₀)
    (N : Set G) (hN : N ∈ 𝓝 (1 : G)) :
    ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ C ≤ K ∧ K ≤ K₀ ∧
      ∀ x ∈ K, ∃ n ∈ N, ∃ c ∈ C, x = n * c := by
  obtain ⟨K₆, hK₆o, -, hK₆s⟩ := hbase ((K₀ : Set G) ∩ N)
    (Filter.inter_mem (hK₀o.mem_nhds K₀.one_mem) hN)
  haveI : CompactSpace K₀ := isCompact_iff_compactSpace.mp hK₀c

  set H : Subgroup K₀ := K₆.subgroupOf K₀ with hH
  have hHo : IsOpen (H : Set K₀) := hK₆o.preimage continuous_subtype_val
  haveI : Finite (K₀ ⧸ H) := H.quotient_finite_of_isOpen hHo
  haveI : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  set M : Subgroup K₀ := H.normalCore with hM
  have hMH : M ≤ H := Subgroup.normalCore_le H
  have hHc : IsClosed (H : Set K₀) := OpenSubgroup.isClosed ⟨H, hHo⟩
  have hMc : IsClosed (M : Set K₀) := by
    have : (M : Set K₀) = ⋂ b : K₀, (fun a : K₀ => b * a * b⁻¹) ⁻¹' (H : Set K₀) := by
      ext a
      simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
      exact Iff.rfl
    rw [this]
    exact isClosed_iInter fun b => hHc.preimage (by fun_prop)
  haveI : M.FiniteIndex := Subgroup.finiteIndex_normalCore H
  have hMo : IsOpen (M : Set K₀) := Subgroup.isOpen_of_isClosed_of_finiteIndex M hMc

  set D : Subgroup K₀ := C.subgroupOf K₀ with hD
  set L : Subgroup K₀ := M ⊔ D with hL
  have hLo : IsOpen (L : Set K₀) := Subgroup.isOpen_mono (le_sup_left : M ≤ L) hMo
  have hLc : IsClosed (L : Set K₀) := OpenSubgroup.isClosed ⟨L, hLo⟩
  have himg : ((L.map K₀.subtype : Subgroup G) : Set G) = Subtype.val '' (L : Set K₀) := by
    ext x; simp [Subgroup.mem_map]
  refine ⟨L.map K₀.subtype, ?_, ?_, ?_, ?_, ?_⟩
  · rw [himg]
    exact hK₀o.isOpenMap_subtype_val _ hLo
  · rw [himg]
    exact hLc.isCompact.image continuous_subtype_val
  · intro c hc
    refine ⟨⟨c, hC hc⟩, ?_, rfl⟩
    exact (le_sup_right : D ≤ L) (by simpa [hD, Subgroup.mem_subgroupOf] using hc)
  · exact Subgroup.map_subtype_le L
  · rintro x ⟨y, hy, rfl⟩
    have hy' : y ∈ ((M ⊔ D : Subgroup K₀) : Set K₀) := hy
    rw [Subgroup.normal_mul] at hy'
    obtain ⟨m, hm, d, hd, rfl⟩ := Set.mem_mul.mp hy'
    refine ⟨(m : G), (hK₆s (hMH hm)).2, (d : G), hd, rfl⟩

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

theorem _root_.GlobalTheory.T.induced_function_from_compact_data : ∀ {G : Type} [Group G] {W₁ : Type} [AddCommGroup W₁] [Module ℂ W₁] {Q P : Subgroup G} {x : G} (σ : Representation ℂ Q W₁) (φ : P → W₁) (C : Set P) (K : Subgroup G), (∀ c ∈ C, ∀ κ ∈ K, ∀ (q : Q) (p' : P), (q : G) * x * (c : G) * κ = x * (p' : G) → φ p' = σ q (φ c)) → (∀ p : P, φ p ≠ 0 → ∃ c ∈ C, ∃ q : Q, x * (p : G) = (q : G) * x * (c : G)) → ∃ f : G → W₁, (∀ (q : Q) (g : G), f ((q : G) * g) = σ q (f g)) ∧ (∀ (g : G), ∀ κ ∈ K, f (g * κ) = f g) ∧ (∀ p : P, f (x * (p : G)) = φ p) ∧ ∀ g : G, f g ≠ 0 → ∃ q : Q, ∃ c ∈ C, ∃ κ ∈ K, g = (q : G) * x * (c : G) * κ := by
  first | exact @GlobalTheory.CompanionTheory.BZRes.TwoOrbit.exists_equivariant_extension | exact GlobalTheory.CompanionTheory.BZRes.TwoOrbit.exists_equivariant_extension | (intros; apply GlobalTheory.CompanionTheory.BZRes.TwoOrbit.exists_equivariant_extension <;> assumption)
end

section

open MeasureTheory Topology
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.restricted_product_haar_measure : ∀ {ι : Type} [Fintype ι]
  {G₀ : Type} [Group G₀] [TopologicalSpace G₀] [IsTopologicalGroup G₀] [T2Space G₀]
  [LocallyCompactSpace G₀] [SecondCountableTopology G₀]
  {G : ι → Type} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
  [∀ i, T2Space (G i)] [∀ i, LocallyCompactSpace (G i)] [∀ i, SecondCountableTopology (G i)]
  {W₀ : Type} [TopologicalSpace W₀] [T2Space W₀] [LocallyCompactSpace W₀]
  [SecondCountableTopology W₀] [MeasurableSpace W₀] [BorelSpace W₀]
  {W : ι → Type} [∀ i, TopologicalSpace (W i)] [∀ i, T2Space (W i)] [∀ i, LocallyCompactSpace (W i)]
  [∀ i, SecondCountableTopology (W i)] [∀ i, MeasurableSpace (W i)] [∀ i, BorelSpace (W i)]
  (a₀ : G₀ → W₀ → W₀) (a : ∀ i, G i → W i → W i),
  (Continuous fun p : G₀ × W₀ => a₀ p.1 p.2) → (∀ x, a₀ 1 x = x) →
  (∀ g h x, a₀ (g * h) x = a₀ g (a₀ h x)) →
  (∀ i, Continuous fun p : G i × W i => a i p.1 p.2) → (∀ i x, a i 1 x = x) →
  (∀ i g h x, a i (g * h) x = a i g (a i h x)) →
  ∀ (U₀ : Set W₀) (U : ∀ i, Set (W i)), IsOpen U₀ → (∀ i, IsOpen (U i)) →
  (∀ g, ∀ x ∈ U₀, a₀ g x ∈ U₀) → (∀ i g, ∀ x ∈ U i, a i g x ∈ U i) →
  ∀ (Z₀ : Set W₀) (Z : ∀ i, Set (W i)), IsClosed Z₀ → (∀ i, IsClosed (Z i)) →
  (∀ g, ∀ x ∈ Z₀, a₀ g x ∈ Z₀) → (∀ i g, ∀ x ∈ Z i, a i g x ∈ Z i) →
  (∀ x ∈ Z₀ ∩ U₀, ∀ y ∈ Z₀ ∩ U₀, ∃ g, a₀ g x = y) →
  (∀ i, ∀ x ∈ Z i ∩ U i, ∀ y ∈ Z i ∩ U i, ∃ g, a i g x = y) →
  ∀ (m₀ : Measure W₀) (m : ∀ i, Measure (W i)),
  (∀ K, IsCompact K → K ⊆ U₀ → m₀ K < ⊤) → (∀ i K, IsCompact K → K ⊆ U i → m i K < ⊤) →
  (∀ g, m₀.map (a₀ g) = m₀) → (∀ i g, (m i).map (a i g) = m i) →
  m₀ (Z₀ ∩ U₀)ᶜ = 0 → (∀ i, m i (Z i ∩ U i)ᶜ = 0) →
  ((Z₀ ∩ U₀).Nonempty → m₀ ≠ 0) → (∀ i, (Z i ∩ U i).Nonempty → m i ≠ 0) →
  ∀ (P : Measure (W₀ × ∀ i, W i)), IsFiniteMeasureOnCompacts P →
  (∀ (g₀ : G₀) (g : ∀ i, G i),
      P.map (fun x => (a₀ g₀ x.1, fun i => a i (g i) (x.2 i))) = P) →
  P ((Z₀ ∩ U₀) ×ˢ Set.univ.pi fun i => Z i ∩ U i)ᶜ = 0 →
  ∃ c : ℝ≥0, ∀ (f₀ : W₀ → ℝ≥0∞) (f : ∀ i, W i → ℝ≥0∞), Measurable f₀ →
      (∀ i, Measurable (f i)) →
      ∫⁻ x, f₀ x.1 * ∏ i, f i (x.2 i) ∂P =
        (c : ℝ≥0∞) * ((∫⁻ x, f₀ x ∂m₀) * ∏ i, ∫⁻ x, f i x ∂(m i)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.FactS.OpenFactor.prod_factor_open | exact GlobalTheory.CompanionTheory.SW.FactS.OpenFactor.prod_factor_open | (intros; apply GlobalTheory.CompanionTheory.SW.FactS.OpenFactor.prod_factor_open <;> assumption)
end

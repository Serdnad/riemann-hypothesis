module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle536
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3095
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2926
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoUniformisationTranslateOrderTwo
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfCompatibleAbelianThickenings
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsAtTranslateTorsion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle012
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle082
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3135
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPsiMemMaximalIdealTendstoZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3136
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle628
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3137
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2596

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.ClosedFibreBpf

theorem thick_zero_apply (R : Type) [CommRing R] [IsLocalRing R]
    (z : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (0 + 1)))) :
    thick R (maximalIdeal R) 0 z = closedPoint R := by
  show (Spec.map _).base z = _
  rw [Spec.map_base]
  apply PrimeSpectrum.ext
  show Ideal.comap _ z.asIdeal = maximalIdeal R
  symm
  apply (IsLocalRing.maximalIdeal.isMaximal R).eq_of_le (by
    haveI := z.isPrime
    exact Ideal.IsPrime.ne_top inferInstance)
  intro a ha
  show _ ∈ z.asIdeal
  have : (Ideal.Quotient.mk (maximalIdeal R ^ (0 + 1))) a = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]; simpa using ha
  rw [show (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R ^ (0 + 1)))).hom a = 0 from this]
  exact z.asIdeal.zero_mem

theorem exists_sec_ne_zero_at : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ k : ℕ, 3 ≤ k → ∀ y : (thickObj R (maximalIdeal R) 0 G).left, ∃ (s : H0 U.LG.L k) (i : Fin 1 → U.LG.L.ι), y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen (((fstG (maximalIdeal R) 0 G).left.app (secChart U.LG.L i)).hom (s.f i)) := by
  intro R _ _ _ hB D A G _ _ hG U k hk y
  obtain ⟨σ, j, hx⟩ := GlobalTheory.T.exists_weightZero_section_not_vanishing_closedFibre R hB D k (by omega) ((U.gt 0).pG.left y) (by
    have h := congrArg (fun f => f.base y) (Over.w (U.gt 0).pG)
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
    exact h.trans (thick_zero_apply R _))
  obtain ⟨s, f, hf0, hfα, hexp⟩ := GlobalTheory.T.exists_section_expansion_weightZero_coefficient R hB D A G hG U k (by omega) σ
  obtain ⟨i, hi⟩ := GlobalTheory.T.section_nonzero_of_expansion_mod_maximalIdeal R D A G U.toUnifPre k s f hexp hfα y ⟨j, by
    subst hf0
    rw [← Scheme.preimage_basicOpen]
    exact hx⟩
  exact ⟨s, i, hi⟩

end GlobalTheory.Mum.ClosedFibreBpf
end
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

theorem exists_not_and_not_of_sub_closed {A : Type} [AddCommGroup A] (P Q : A → Prop)
    (hP : ∀ a b, P a → P b → P (a - b)) (hQ : ∀ a b, Q a → Q b → Q (a - b)) {a b : A} (ha : ¬ P a) (hb : ¬ Q b) :
    ∃ c, ¬ P c ∧ ¬ Q c := by
  by_cases h1 : Q a
  · by_cases h2 : P b
    · refine ⟨a + b, fun h => ha ?_, fun h => hb ?_⟩
      · simpa using hP _ _ h h2
      · simpa using hQ _ _ h h1
    · exact ⟨b, h2, hb⟩
  · exact ⟨a, ha, h1⟩

theorem mem_map_bar_iff {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (𝔭 : Ideal (𝓞 E)) (x : 𝓞 E) :
    x ∈ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) ↔ H.bar x ∈ 𝔭 := by
  rw [Ideal.mem_map_iff_of_surjective (H.bar : 𝓞 E →+* 𝓞 E) (fun a => ⟨H.bar a, bar_bar H a⟩)]
  constructor
  · rintro ⟨a, ha, rfl⟩
    have := bar_bar H a
    simpa [this] using ha
  · exact fun hx => ⟨_, hx, bar_bar H x⟩

theorem mem_of_smul_mem_of_not_mem {O X : Type} [CommRing O] [AddCommGroup X] [Module O X] {I : Ideal O}
    (hI : I.IsMaximal) (N : Submodule O X) {c : O} (hc : c ∉ I) {x : X} (hx : c • x ∈ N ⊔ I • (⊤ : Submodule O X)) :
    x ∈ N ⊔ I • (⊤ : Submodule O X) := by
  obtain ⟨d, i, hi, hd⟩ := hI.exists_inv hc
  have : x = d • (c • x) + i • x := by rw [smul_smul, ← add_smul, hd, one_smul]
  rw [this]
  exact add_mem (Submodule.smul_mem _ _ hx) (Submodule.mem_sup_right (Submodule.smul_mem_smul hi trivial))

theorem exists_improves_of_ne_conj : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (y : D.La →ₗ[𝓞 E] X) (n : ℕ)
    (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z') (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal) (hn𝔭 : (n : 𝓞 E) ∈ 𝔭)
    (hb : 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ 𝔭)
    (e : 𝓞 E) (he1 : e - 1 ∈ 𝔭) (he : ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → 𝔮 ≠ 𝔭 → e ∈ 𝔮)
    (e' : 𝓞 E) (he1' : e' - 1 ∈ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E))
    (he' : ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → 𝔮 ≠ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) → e' ∈ 𝔮)
    (v : Z') (hv : y v ∈ 𝔭 • (⊤ : Submodule (𝓞 E) X)) (ℓ₀ : Z' →ₗ[𝓞 E] 𝓞 E) (hℓ₀ : ℓ₀ v ∉ 𝔭)
    (v₂ : Z') (hv₂ : y v₂ ∈ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) X)) (ℓ₁ : Z' →ₗ[𝓞 E] 𝓞 E)
    (hℓ₁ : ℓ₁ v₂ ∉ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E))
    (θ : 𝓞 E →+ ℤ) (hθ : ∀ t, θ (H.bar t) = θ t) (s : 𝓞 E) (hs : s ∉ 𝔭) (hs' : H.bar s ∉ 𝔭)
    (hgen : ∀ ψ : 𝓞 E →+ ℤ, ∃ t : 𝓞 E, ∀ u, ψ (s * u) = θ (t * u))
    (hZ : ¬ Z.map y ≤ img D y Z' 𝔭),
    ∃ Z'', Improves D y n 𝔭 Z Z' Z'' := by
  intro E _ _ _ H D X _ _ y n Z Z' h 𝔭 h𝔭 hn𝔭 hb e he1 he e' he1' he' v hv ℓ₀ hℓ₀ v₂ hv₂ ℓ₁ hℓ₁ θ hθ s hs hs' hgen hZ
  set 𝔭' := 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) with h𝔭'def
  have hmem : ∀ x, x ∈ 𝔭' ↔ H.bar x ∈ 𝔭 := mem_map_bar_iff H 𝔭
  have h𝔭' : 𝔭'.IsMaximal := by
    have : 𝔭' = 𝔭.comap (H.bar : 𝓞 E →+* 𝓞 E) := Ideal.ext fun x => hmem x
    rw [this]
    exact Ideal.comap_isMaximal_of_surjective _ (fun a => ⟨H.bar a, bar_bar H a⟩)
  have hn' : (n : 𝓞 E) ∈ 𝔭' := (hmem _).2 (by simpa using hn𝔭)
  obtain ⟨ζ, hζZ, hζ, hζs, hopp⟩ := h.exists_rank_one (m := 0) (zero_mem _) θ (fun t => by simp [hθ])
  have himg : ∀ I : Ideal (𝓞 E), img D y Z' I = LinearMap.range (y ∘ₗ Z'.subtype) ⊔ I • ⊤ := fun I => by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have himg' : ∀ (ℓ : Z' →ₗ[𝓞 E] 𝓞 E) (I : Ideal (𝓞 E)),
      img D y (LinearMap.range (Z'.subtype + ℓ.smulRight (0 + ζ ℓ))) I =
        LinearMap.range (y ∘ₗ Z'.subtype + ℓ.smulRight (y (ζ ℓ))) ⊔ I • ⊤ := fun ℓ I => by
    have : y ∘ₗ Z'.subtype + ℓ.smulRight (y (ζ ℓ)) = y ∘ₗ (Z'.subtype + ℓ.smulRight (0 + ζ ℓ)) := by
      ext x; simp
    rw [this, LinearMap.range_comp]

  obtain ⟨ℓ₂, hℓ₂⟩ : ∃ ℓ₂, y (ζ ℓ₂) ∉ img D y Z' 𝔭 := by
    obtain ⟨_, ⟨z, hz, rfl⟩, hz'⟩ := SetLike.not_le_iff_exists.1 hZ
    obtain ⟨ℓ, hℓ⟩ := GlobalTheory.LowFilt.exists_linear_theta_factor D Z' θ s (fun h0 => hs (h0 ▸ zero_mem _)) hgen z
    have h0 : ζ ℓ - H.bar s • z = 0 := h.symm.eq_zero (sub_mem (hζZ ℓ) (Z.smul_mem _ hz)) fun x hx => by
      rw [ef_swap, map_sub, hζ ℓ ⟨x, hx⟩, hℓ ⟨x, hx⟩]; simp
    refine ⟨ℓ, fun hh => hz' ?_⟩
    rw [sub_eq_zero.1 h0, map_smul] at hh
    exact mem_of_smul_mem_of_not_mem h𝔭 _ hs' hh
  obtain ⟨ℓ', h1, h2⟩ := exists_not_and_not_of_sub_closed (fun ℓ : Z' →ₗ[𝓞 E] 𝓞 E => ℓ v₂ ∈ 𝔭')
    (fun ℓ => y (ζ ℓ) ∈ img D y Z' 𝔭) (fun a b ha hb => sub_mem ha hb)
    (fun a b ha hb => by simpa only [map_sub] using sub_mem ha hb) hℓ₁ hℓ₂
  have he𝔭' : e ∈ 𝔭' := he _ h𝔭' hn' hb
  have he'𝔭 : e' ∈ 𝔭 := he' _ h𝔭 hn𝔭 hb.symm
  set ℓ := e • ℓ₀ + e' • ℓ' with hℓdef
  have hℓx : ∀ x, ℓ x = e * ℓ₀ x + e' * ℓ' x := fun x => rfl
  have hv𝔭 : ℓ v ∉ 𝔭 := fun hh => hℓ₀ (by
    have : ℓ₀ v = ℓ v - (e - 1) * ℓ₀ v - e' * ℓ' v := by rw [hℓx]; ring
    rw [this]
    exact sub_mem (sub_mem hh (𝔭.mul_mem_right _ he1)) (𝔭.mul_mem_right _ he'𝔭))
  have hv𝔭' : ℓ v₂ ∉ 𝔭' := fun hh => h1 (by
    have : ℓ' v₂ = ℓ v₂ - (e' - 1) * ℓ' v₂ - e * ℓ₀ v₂ := by rw [hℓx]; ring
    show ℓ' v₂ ∈ 𝔭'
    rw [this]
    exact sub_mem (sub_mem hh (𝔭'.mul_mem_right _ he1')) (𝔭'.mul_mem_right _ he𝔭'))
  have k𝔭 := range_le_of_ker (y ∘ₗ Z'.subtype) ℓ (y (ζ ℓ)) 𝔭 h𝔭 (v := v) hv hv𝔭
  have k𝔭' := range_le_of_ker (y ∘ₗ Z'.subtype) ℓ (y (ζ ℓ)) 𝔭' h𝔭' (v := v₂) hv₂ hv𝔭'
  refine ⟨_, hopp ℓ, fun 𝔮 h𝔮 hn𝔮 => ?_, fun hle => h2 ?_⟩
  · rw [himg, himg']
    by_cases q1 : 𝔮 = 𝔭
    · rw [q1]; exact k𝔭.2
    by_cases q2 : 𝔮 = 𝔭'
    · rw [q2]; exact k𝔭'.2
    exact range_le_of_mem _ _ _ _ fun x => by
      rw [hℓx]
      exact add_mem (𝔮.mul_mem_right _ (he _ h𝔮 hn𝔮 q1)) (𝔮.mul_mem_right _ (he' _ h𝔮 hn𝔮 q2))
  · rw [himg'] at hle
    have hu := hle k𝔭.1
    have b1 : H.bar e ∈ 𝔭 := (hmem _).1 he𝔭'
    have b2 : H.bar e' - 1 ∈ 𝔭 := by simpa using (hmem _).1 he1'
    have : y (ζ ℓ') = y (ζ ℓ) - H.bar e • y (ζ ℓ₀) - (H.bar e' - 1) • y (ζ ℓ') := by
      rw [hℓdef, map_add (f := _), hζs, hζs, map_add (f := _), map_smul, map_smul, sub_smul, one_smul]; abel
    show y (ζ ℓ') ∈ img D y Z' 𝔭
    rw [this]
    exact sub_mem (sub_mem hu (Submodule.mem_sup_right (Submodule.smul_mem_smul b1 trivial)))
      (Submodule.mem_sup_right (Submodule.smul_mem_smul b2 trivial))

end GlobalTheory.LowFilt
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp.TranslLev

open GlobalTheory.MumCmp.Transl UnifCompare

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G]



theorem exists_iso_translate_levels [IsLocalRing R] (hR : AdmBase R I) (hG : IsSemiAbelian G) {D D' : DegData R I}
    {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))} (U : UnifPre I D A G) (U' : UnifPre I D' A' G)
    (a : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G) (ha : a ^ 2 = 1) (b : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.toPre.P.A)
    (hab : ∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ (thickObj R I e G).left),
      ae ≫ (thickObj R I e G).hom = 𝟙 _ → ae ≫ (fstG I e G).left = thick R I e ≫ a.left →
      ae ≫ (U.gt e).pG.left = thick R I e ≫ b.left)
    (wL : LB.Iso U'.LG.L (U.LG.L.pull (tr a).left)) (hw : wL.IsGen) (β : D'.toPre.P.A ≅ D.toPre.P.A)
    (hβ : ∀ e, (U'.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left) :
    ∃ w : LB.Iso D'.toPre.P.L (D.toPre.P.L.pull (padd D.toPre.P.A β.hom (toUnit D'.toPre.P.A ≫ b)).left),
      w.IsGen ∧ ∀ (e : ℕ) (h : (thickObj R I e G).left ⟶ (thickObj R I e G).left),
        h ≫ (fstG I e G).left = (fstG I e G).left ≫ (tr a).left →
        ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι)
          (jL : U.LG.L.ι) (jL' : U'.LG.L.ι),
        (U.gt e).pG.left (h (r z)) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' →
        (tr a).left ((fstG I e G).left (r z)) ∈ U.LG.L.U jL → (fstG I e G).left (r z) ∈ U'.LG.L.U jL' →
        gw w (r ≫ (U'.gt e).pG.left) z jM jM' * gw (U'.w e) r z jM' (fun _ => jL') =
          gw (U.w e) (r ≫ h) z jM (fun _ => jL) * gw wL (r ≫ (fstG I e G).left) z jL jL' := by
  rw [isGen_iff] at hw
  obtain ⟨hf, hs⟩ := surjective_appTop U
  obtain ⟨ae, hae⟩ : ∃ ae : ∀ e, 𝟙_ _ ⟶ thickObj R I e G,
      ∀ e, (ae e).left ≫ (fstG I e G).left = thick R I e ≫ a.left :=
    ⟨fun e => Over.homMk (pullback.lift (thick R I e ≫ a.left) (𝟙 _) (by
      rw [Category.assoc, Over.w a]; exact (Category.comp_id _).trans (Category.id_comp _).symm))
      (pullback.lift_snd _ _ _), fun e => pullback.lift_fst _ _ _⟩
  let Φ : D'.toPre.P.A ≅ D.toPre.P.A :=
    { hom := β.hom * (toUnit _ ≫ b)
      inv := (𝟙 _ * (toUnit _ ≫ b)⁻¹) ≫ β.inv
      hom_inv_id := by
        rw [← Category.assoc, MonObj.comp_mul, Category.comp_id, GrpObj.comp_inv, ← Category.assoc, comp_toUnit,
          mul_inv_cancel_right, β.hom_inv_id]
      inv_hom_id := by
        rw [MonObj.comp_mul, Category.assoc, β.inv_hom_id, Category.comp_id, ← Category.assoc, comp_toUnit,
          inv_mul_cancel_right] }
  let βe : ∀ e, thickObj R I e D'.toPre.P.A ≅ thickObj R I e D.toPre.P.A := fun e =>
    (Over.pullback (thick R I e)).mapIso Φ
  have hβe : ∀ e, (βe e).hom.left ≫ (fstG I e D.toPre.P.A).left = (fstG I e D'.toPre.P.A).left ≫ Φ.hom.left :=
    fun e => pullback.lift_fst _ _ _
  have hb : ∀ e, (tr (ae e)).left ≫ (U.gt e).pG.left =
      (U'.gt e).q.left ≫ (βe e).hom.left ≫ (fstG I e D.toPre.P.A).left := fun e => by
    have h₁ := TorusCoord.im_mul (U.gt e) (toUnit _ ≫ ae e) (𝟙 (thickObj R I e G))
    have h₂ : TorusCoord.im (U.gt e) (toUnit (thickObj R I e G) ≫ ae e) = toUnit _ ≫ b := by
      apply Over.OverMorphism.ext
      show ((thickObj R I e G).hom ≫ (ae e).left) ≫ (U.gt e).pG.left = ((thickObj R I e G).hom ≫ thick R I e) ≫ b.left
      rw [Category.assoc, Category.assoc]
      exact congrArg ((thickObj R I e G).hom ≫ ·) (hab e _ (Over.w (ae e)) (hae e))
    have h₃ : TorusCoord.im (U.gt e) (𝟙 (thickObj R I e G)) = (U'.gt e).pG ≫ β.hom :=
      Over.OverMorphism.ext ((Category.id_comp _).trans (hβ e).symm)
    have h₄ : (U'.gt e).pG ≫ Φ.hom = ((U'.gt e).pG ≫ β.hom) * (toUnit _ ≫ b) := by
      show (U'.gt e).pG ≫ (β.hom * (toUnit _ ≫ b)) = _
      rw [MonObj.comp_mul, ← Category.assoc _ (toUnit _), comp_toUnit]
    rw [h₂, h₃, _root_.mul_comm (toUnit _ ≫ b), ← h₄] at h₁
    rw [hβe]
    exact (congrArg (fun q => q.left) h₁).trans (Category.assoc (U'.gt e).q.left _ _)
  choose v hvg hv using fun e => exists_level (hae e) hw hG ha hf hs β.hom (hβ e) _ (hb e)
  have hc : ∀ e, thickMap R I e D'.toPre.P.A ≫ (βe (e + 1)).hom.left =
      (βe e).hom.left ≫ thickMap R I e D.toPre.P.A := fun e => thickMap_comm e _ _ _ (hβe e) (hβe (e + 1))
  have ht : ∀ e, thickMap R I e G ≫ (tr (ae (e + 1))).left = (tr (ae e)).left ≫ thickMap R I e G := fun e =>
    thickMap_comm e _ _ _ (tr_fst (hae e)) (tr_fst (hae (e + 1)))
  obtain ⟨hN, -, -, hC⟩ := hR
  obtain ⟨Ψ, w, hwg, H⟩ := exists_iso_of_compatible_thickenings GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
    GlobalTheory.abelianSchemeLaws_all.1.ample R I D.toPre.P D'.toPre.P βe v hvg hc (by
    intro e Z r z j j' hj hj'
    have := (U'.gt e).q_flat
    have := (U'.gt e).q_surj
    have hm : ∀ y : (thickObj R I e D'.toPre.P.A).left,
        y ∈ (D.toPre.P.L.pull ((βe e).hom.left ≫ (fstG I e D.toPre.P.A).left)).U (fun _ => j) ⊓
          (D'.toPre.P.L.pull (fstG I e D'.toPre.P.A).left).U (fun _ => j') →
        thickMap R I e D'.toPre.P.A y ∈
          (D.toPre.P.L.pull ((βe (e + 1)).hom.left ≫ (fstG I (e + 1) D.toPre.P.A).left)).U (fun _ => j) ⊓
          (D'.toPre.P.L.pull (fstG I (e + 1) D'.toPre.P.A).left).U (fun _ => j') := by
      intro y hy
      have k : thickMap R I e D'.toPre.P.A ≫ (βe (e + 1)).hom.left ≫ (fstG I (e + 1) D.toPre.P.A).left =
          (βe e).hom.left ≫ (fstG I e D.toPre.P.A).left :=
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (fstG I (e + 1) D.toPre.P.A).left) (hc e)).trans
          ((Category.assoc _ _ _).trans (congrArg ((βe e).hom.left ≫ ·) (trans_comp_proj e _))))
      exact ⟨mem_pull.2 ((congrArg (fun g => g y ∈ D.toPre.P.L.U j) k).mpr (mem_pull.1 hy.1)),
        mem_pull.2 ((congrArg (fun g => g y ∈ D'.toPre.P.L.U j') (trans_comp_proj e _)).mpr
          (mem_pull.1 hy.2))⟩
    have hz : r z ∈ (D.toPre.P.L.pull ((βe e).hom.left ≫ (fstG I e D.toPre.P.A).left)).U (fun _ => j) ⊓
          (D'.toPre.P.L.pull (fstG I e D'.toPre.P.A).left).U (fun _ => j') :=
      ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
    refine (gm_pull r _ z _ (hm _ hz) _).symm.trans
      (gm_eq_of_flat_surjective (U'.gt e).q.left _ _ (fun x _ hx => ?_) r z (hm _ hz) hz)
    refine (gm_pull _ _ x _ (hm _ hx) _).trans ?_
    obtain ⟨jL, hL⟩ := exists_chart U.LG.isLB ((tr a).left ((fstG I e G).left x))
    obtain ⟨jL', hL'⟩ := exists_chart U'.LG.isLB ((fstG I e G).left x)
    have hM : (U.gt e).pG.left ((tr (ae e)).left x) ∈ D.toPre.P.L.U j :=
      (congrArg (fun g => g x ∈ D.toPre.P.L.U j) (hb e)).mpr (mem_pull.1 hx.1)
    have hM' : (U'.gt e).pG.left x ∈ D'.toPre.P.L.U j' := mem_pull.1 hx.2
    have k₁ : (thickMap R I e G ≫ (tr (ae (e + 1))).left) ≫ (U.gt (e + 1)).pG.left =
        (tr (ae e)).left ≫ (U.gt e).pG.left :=
      (congrArg (· ≫ (U.gt (e + 1)).pG.left) (ht e)).trans ((Category.assoc _ _ _).trans
        (congrArg ((tr (ae e)).left ≫ ·) (U.gt_q e)))
    have h₀ := hv e _ (𝟙 _) x j j' jL jL' hM hM' hL hL'
    have h₁ := hv (e + 1) _ (thickMap R I e G) x j j' jL jL'
      ((congrArg (fun g => g x ∈ D.toPre.P.L.U j) k₁).mpr hM)
      ((congrArg (fun g => g x ∈ D'.toPre.P.L.U j') (U'.gt_q e)).mpr hM')
      ((congrArg (fun g => (tr a).left (g x) ∈ U.LG.L.U jL) (trans_comp_proj e G)).mpr hL)
      ((congrArg (fun g => g x ∈ U'.LG.L.U jL') (trans_comp_proj e G)).mpr hL')
    rw [gw_trans U' e x j' jL' hM' hL', ht, gw_trans' U e (tr (ae e)).left x j jL hM
      ((congrArg (fun g => g x ∈ U.LG.L.U jL) (tr_fst (hae e))).mpr hL), trans_comp_q, trans_comp_proj] at h₁
    rw [Category.id_comp, Category.id_comp, Category.id_comp] at h₀
    exact mul_right_cancel (h₁.trans h₀.symm))
  have := D'.toPre.P.isAb.proper
  have := D.toPre.P.isAb.proper
  have eΨ : Ψ.hom = padd D.toPre.P.A β.hom (toUnit D'.toPre.P.A ≫ b) :=
    hom_eq_of_thickenings_of_isProper R I (IsAdicComplete.le_jacobson_bot I) _ _ Ψ.hom Φ.hom
      fun e => (H e).1.trans (hβe e)
  have eΨ' : (padd D.toPre.P.A β.hom (toUnit D'.toPre.P.A ≫ b)).left = Ψ.hom.left := by rw [eΨ]
  rw [eΨ']
  refine ⟨w, hwg, fun e h hh Z r z jM jM' jL jL' a₁ a₂ a₃ a₄ => ?_⟩
  haveI := GlobalTheory.TorsionTranslate.mono_fst (I := I) e G
  have heq : h = (tr (ae e)).left := (cancel_mono (fstG I e G).left).1 (by rw [hh, tr_fst (hae e)])
  subst heq
  have hq : (U'.gt e).pG.left = (U'.gt e).q.left ≫ (fstG I e D'.toPre.P.A).left := rfl
  have m₁ : (fstG I e D.toPre.P.A).left ((βe e).hom.left ((r ≫ (U'.gt e).q.left) z)) ∈ D.toPre.P.L.U jM :=
    (congrArg (fun g => g (r z) ∈ D.toPre.P.L.U jM) (hb e)).mp a₁
  have m₂ : (fstG I e D'.toPre.P.A).left ((r ≫ (U'.gt e).q.left) z) ∈ D'.toPre.P.L.U jM' :=
    (congrArg (fun g => g (r z) ∈ D'.toPre.P.L.U jM') hq).mp a₂
  have k := (H e).2 Z (r ≫ (U'.gt e).q.left) z jM jM' m₁ m₂
  have k' : gw w (r ≫ (U'.gt e).pG.left) z jM jM' = gw (v e) (r ≫ (U'.gt e).q.left) z jM (fun _ => jM') :=
    (congrArg (fun g => gw w g z jM jM') (show r ≫ (U'.gt e).pG.left =
      (r ≫ (U'.gt e).q.left) ≫ (fstG I e D'.toPre.P.A).left by rw [hq, Category.assoc])).trans k
  rw [← hv e Z r z jM jM' jL jL' a₁ a₂ a₃ a₄, k']

end GlobalTheory.MumCmp.TranslLev

theorem GlobalTheory.MumCmp.TranslLev.exists_iso_translate_global : ∀ {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (hR : Base R) {D : DegData R (maximalIdeal R)} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (U : Unif (maximalIdeal R) D A G) (a : 𝟙_ (Over (Sp R)) ⟶ G) (ha : a ^ 2 = 1) (b : 𝟙_ (Over (Sp R)) ⟶ D.toPre.P.A)
    (hab : ∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ b.left)
    {A₂ : PolAV (Sp (FractionRing R))} {D₂ : DegData R (maximalIdeal R)} (U₂ : Unif (maximalIdeal R) D₂ A₂ G) (wL : LB.Iso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left)) (hwL : wL.IsGen) (β : D₂.toPre.P.A ≅ D.toPre.P.A) (hβ : ∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left),
    ∃ W : LB.Iso D₂.toPre.P.L (D.toPre.P.L.pull (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom b 0)), W.IsGen ∧
      ∀ (e : ℕ) (h : (thickObj R (maximalIdeal R) e G).left ⟶ (thickObj R (maximalIdeal R) e G).left), h ≫ (thickObj R (maximalIdeal R) e G).hom = (thickObj R (maximalIdeal R) e G).hom → h ≫ (fstG (maximalIdeal R) e G).left = (fstG (maximalIdeal R) e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left →
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D₂.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U₂.LG.L.ι),
        (U.gt e).pG.left (h (r z)) ∈ D.toPre.P.L.U jM → (U₂.gt e).pG.left (r z) ∈ D₂.toPre.P.L.U jM' →
        ((toUnit G ≫ a) * 𝟙 G).left ((fstG (maximalIdeal R) e G).left (r z)) ∈ U.LG.L.U jL → (fstG (maximalIdeal R) e G).left (r z) ∈ U₂.LG.L.U jL' →
        Geo.Tor.gw W (r ≫ (U₂.gt e).pG.left) z jM jM' * Geo.Tor.gw (U₂.w e) r z jM' (fun _ => jL') =
          Geo.Tor.gw (U.w e) (r ≫ h) z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ (fstG (maximalIdeal R) e G).left) z jL jL' := by
  intro R _ _ _ hR D A G _ _ hG U a ha b hab A₂ D₂ U₂ wL hwL β hβ
  obtain ⟨W, hW, hv⟩ := GlobalTheory.MumCmp.TranslLev.exists_iso_translate_levels hR.1 hG U.toUnifPre U₂.toUnifPre a ha b
    hab wL hwL β hβ
  exact ⟨W, hW, fun e h _ hh Z r z jM jM' jL jL' a₁ a₂ a₃ a₄ => hv e h hh Z r z jM jM' jL jL' a₁ a₂ a₃ a₄⟩
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.FibLat
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.characterLatticeAtFibre_unique_up_to_iso : ∀ (o Ω : Type) [CommRing o] [IsDomain o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (G : Over M.Z) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (I T : Type) (f : I → (G ⟶ G)) (gγ : T → (Over.mk M.pt ⟶ G)) (ζ : oˣ) (L : ℕ), 0 < L → IsPrimitiveRoot (ζ : o) L → IsUnit (L : o) → ∀ (X X' : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [AddCommGroup X'] [Module.Free ℤ X'] [Module.Finite ℤ X'] (m : I → X →+ X) (c : T → X →+ ZMod L) (m' : I → X' →+ X') (c' : T → X' →+ ZMod L) (w : M.Z), LatAt f gγ ζ L m c w → LatAt f gγ ζ L m' c' w → ∃ e : X ≃+ X', (∀ i x, e (m i x) = m' i (e x)) ∧ ∀ t x, c' t (e x) = c t x := by
  first | exact @GlobalTheory.UPoinc.GFibUniq.latAt_unique | exact GlobalTheory.UPoinc.GFibUniq.latAt_unique | (intros; apply GlobalTheory.UPoinc.GFibUniq.latAt_unique <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
open GlobalTheory.Mum.TensPos GlobalTheory.PsiScalUnit GlobalTheory.Mum.TensPol

noncomputable section

namespace GlobalTheory.Mum.TensPolRel

theorem tauCoord_rel : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : GlobalTheory.PolDeg.Data R) (k : Q.X → Q.X → (FractionRing R)ˣ), (∀ a b, Q.TauCoord a b (k a b)) → (∀ a b, ∃ u ∈ unitsK R, k b a = u * k a b) ∧ ∀ a a' b, ∃ u ∈ unitsK R, k (a + a') b = u * (k a b * k a' b) := by
  intro R _ _ _ Q k hk
  obtain ⟨z⟩ : Nonempty (TK R).left := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R)))
  haveI := Q.isAb.proper
  obtain ⟨J, hJ, iJ⟩ := GlobalTheory.Mum.TensPol.exists_int Q.B Q.M.L Q.M.isLB z
  let E : (FractionRing R)ˣ →* ((TK R).left.presheaf.stalk z)ˣ := Units.map (ev z).toMonoidHom
  have hE : Function.Injective E := Units.map_injective (ev_inj z)
  have hτ : ∀ a b, ∃ v ∈ unitsS z, val (Q.tau a b) (𝟙 _) z J = E (k a b) * v := fun a b => by
    obtain ⟨u, -, hu⟩ := hk a b
    refine ⟨_, GlobalTheory.Mum.TensPol.val_mem z iJ _ (fun i => ?_) _ u, (hu z J hJ).trans (congrArg (· * _) (gm_unitOn z _))⟩
    fin_cases i <;> exact Over.w _
  choose v hv ev' using hτ
  refine ⟨fun a b => ?_, fun a a' b => ?_⟩
  · refine ⟨k b a * (k a b)⁻¹, mem_unitsK z ?_, by rw [inv_mul_cancel_right]⟩
    have e := Q.tau_symm a b z J hJ
    rw [ev', ev'] at e
    have : E (k b a * (k a b)⁻¹) = v a b * (v b a)⁻¹ := by
      rw [map_mul, map_inv]
      apply Additive.ofMul.injective
      have e' := congrArg Additive.ofMul e
      simp only [ofMul_mul, ofMul_inv] at e' ⊢
      linear_combination (norm := abel) -e'
    exact this ▸ mul_mem (hv a b) (inv_mem (hv b a))
  · refine ⟨k (a + a') b * (k a b * k a' b)⁻¹, mem_unitsK z ?_, by rw [inv_mul_cancel_right]⟩
    have e := Q.tau_add a a' b z J hJ
    have hc : cubV Q.cub z J (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c a') (toUnit (TK R) ≫ Q.c b) ∈ unitsS z := by
      rw [← val_cub Q.cub (toUnit (TK R)) hJ]
      refine GlobalTheory.Mum.TensPol.val_mem z iJ _ (fun i => ?_) _ _
      exact Over.w (lift (Q.c a) (lift (Q.c a') (Q.c b)) ≫ psum Q.B (x3 Q.B) i.down)
    rw [ev', ev', ev'] at e
    generalize cubV Q.cub z J (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c a') (toUnit (TK R) ≫ Q.c b) = w at e hc
    have : E (k (a + a') b * (k a b * k a' b)⁻¹) = v a b * v a' b * (v (a + a') b)⁻¹ * w⁻¹ := by
      rw [map_mul, map_inv, map_mul]
      apply Additive.ofMul.injective
      have e' := congrArg Additive.ofMul e
      simp only [ofMul_mul, ofMul_inv] at e' ⊢
      linear_combination (norm := abel) e'
    exact this ▸ mul_mem (mul_mem (mul_mem (hv a b) (hv a' b)) (inv_mem (hv _ b))) (inv_mem hc)

end GlobalTheory.Mum.TensPolRel
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_sqrt_latticeHom_finiteExtension_complete : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (h : X → (FractionRing R)ˣ) (m : ℕ) (t : Fin m → R), IsCN R → (∀ a b, h (a + b) = h a * h b) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (gam : FractionRing R →+* FractionRing R') (r : Fin m → R') (eta : X → (FractionRing R')ˣ), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ (∀ x, gam (algebraMap R _ x) = algebraMap R' _ (ρ x)) ∧ (∀ i, r i ^ 2 = ρ (t i)) ∧ (∀ a b, eta (a + b) = eta a * eta b) ∧ ∀ a, eta a ^ 2 = Units.map gam.toMonoidHom (h a) := by
  first | exact @GlobalTheory.RootHom.exists_sqrt_hom | exact GlobalTheory.RootHom.exists_sqrt_hom | (intros; apply GlobalTheory.RootHom.exists_sqrt_hom <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

theorem _root_.GlobalTheory.T.exists_proper_normal_flagScheme_of_affine_cover : ∀ (K : Type) [Field K] (X : Scheme.{0}) (s : X ⟶ Sp K) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) [Finite B] (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1)) (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)), IsProjOver s → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsCover (RingHom.id K) s V α c D → (∀ x : X, ∃ b, x ∈ (V b).1) → ∃ (Z : Scheme.{0}) (π : Z ⟶ X) (g : ∀ en : En m, Z ⟶ PSpace K (plN M en.1)) (κ : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ Z)), IsProper π ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z ∧ HasPlk (RingHom.id K) V α c π g κ ∧ (∀ b w, IsOpenImmersion (κ b w)) ∧ (∀ z : Z, ∃ b w, z ∈ Set.range (κ b w)) ∧ ∀ (W : Scheme.{0}) (a a' : W ⟶ Z), a ≫ π = a' ≫ π → (∀ en, a ≫ g en = a' ≫ g en) → a = a' := by
  first | exact @GlobalTheory.FlagMod.FieldFlag.exists_properFlag | exact GlobalTheory.FlagMod.FieldFlag.exists_properFlag | (intros; apply GlobalTheory.FlagMod.FieldFlag.exists_properFlag <;> assumption)
end

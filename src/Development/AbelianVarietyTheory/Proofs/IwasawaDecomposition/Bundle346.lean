module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxUnramifiedSubfieldConjIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EncardSmulMemLeEncardSmulInterNonempty
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle163
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle160
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle173
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle335
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle025
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle110
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle411
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle330
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle299
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs

@[expose] public section

section

noncomputable section
namespace GlobalTheory.HeightCounting
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host NumberField IsDedekindDomain Polynomial GlobalTheory.Pst

theorem exists_bridges (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (pl : HeightOneSpectrum (𝓞 E) → ValuationSubring Ω) (hpl : ∀ w, IsPlaceOver (pl w) w) :
    ∃ (LL : FinExt l) (br : ∀ w : HeightOneSpectrum (𝓞 E), w ∈ placesOver E l → LocBridge l E Ω (Dec (F := E) (pl w)) ↥(OL LL)),
      ∀ w hw, Induces (br w hw) := by
  have hfin : (placesOver E l).Finite := by
    have h0 : Ideal.span {((l : ℕ) : 𝓞 E)} ≠ 0 := by
      simpa using (Fact.out : l.Prime).ne_zero
    refine (Ideal.finite_factors h0).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.mpr hv
  have := hfin.to_subtype
  choose j L0 hj hL using fun w : placesOver E l => GlobalTheory.PlaceBridge.exists_locBridge l E Ω w.1 (pl w.1) w.2 (hpl w.1)
  have := fun w => (L0 w).2
  let LL : FinExt l := ⟨⨆ w, (L0 w).1, inferInstance⟩
  choose br hb using fun w => hL w LL (le_iSup (fun w => (L0 w).1) w)
  exact ⟨LL, fun w hw => br ⟨w, hw⟩, fun w hw x => by rw [(hb _).1]; exact hj ⟨w, hw⟩ x⟩

theorem localPreds_of_isModel {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {O O' : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O']
    {pl : HeightOneSpectrum (𝓞 E) → ValuationSubring Ω}
    {br : ∀ w : HeightOneSpectrum (𝓞 E), w ∈ placesOver E l → LocBridge l E Ω (Dec (F := E) (pl w)) O}
    (hpl : ∀ w, IsPlaceOver (pl w) w) (hbr : ∀ w hw, Induces (br w hw))
    {m : ℕ} {r : G E Ω →* GL (Fin m) (Om l)} {w : HeightOneSpectrum (𝓞 E)}
    (hw : w ∈ placesOver E l) (B : LocBridge l E Ω (Dec (F := E) (pl w)) O') (hB : Induces B)
    {L : FinExt l} {r' : ↥(Dec (F := E) (pl w)) →* GL (Fin m) ↥L.1}
    (h : IsModel B (resDec pl r w) L r') :
    (IsCrysW P pl br r w ↔ B.IsCrysE P L r') ∧
    (IsdRW P pl br r w ↔ B.IsdRE P L r') ∧
    (IsPotCrysW P pl br r w ↔ B.IsPotCrysE P L r') ∧
    ∀ (τ : E →+* Om l) (τ' : ↥B.Kw.1 →ₐ[ℚ_[l]] ↥L.1), IsInduced B τ τ' →
      (B.IsdRE P L r' → ∀ a : ℤ, a ∈ jumpsW P pl br r τ ↔ B.IsJumpE P L r' τ' a) ∧
      (B.IsdRE P L r' → ∀ a : ℤ, ((jumpsW P pl br r τ).count a : ℤ) = B.multE P L r' τ' a) := by
  have := L.2
  have := (br w hw).LL.2
  let L' : FinExt l := ⟨L.1 ⊔ (br w hw).LL.1, inferInstance⟩
  have l₁ : L.1 ≤ L'.1 := le_sup_left
  have l₂ : (br w hw).LL.1 ≤ L'.1 := le_sup_right
  have h' : IsModel (br w hw) (resDec pl r w) L' (mapRep (IntermediateField.inclusion l₁).toRingHom r') :=
    ⟨l₂, (h.enlarge l₁).2⟩
  obtain ⟨a₁, b₁, c₁, d₁⟩ := local_of_isModel P hpl hbr h'
  obtain ⟨a₂, b₂, c₂, d₂⟩ := bridge_indep l P E Ω (pl w) O O' (br w hw) B (hbr w hw) hB L' l₂ m (mapRep (IntermediateField.inclusion l₁).toRingHom r')
  obtain ⟨a₃, b₃, c₃, d₃⟩ := local_ext P B l₁ r'
  have key : ∀ (τ : E →+* Om l) (τ' : ↥B.Kw.1 →ₐ[ℚ_[l]] ↥L.1), IsInduced B τ τ' → B.IsdRE P L r' →
      ∀ a : ℤ, ((jumpsW P pl br r τ).count a : ℤ) = B.multE P L r' τ' a := fun τ τ' hτ hd a => by
    obtain ⟨τ₁, t₁, e⟩ := d₂ τ ((IntermediateField.inclusion l₁).comp τ') hτ
    rw [(d₁ τ τ₁ t₁).2 (b₂.2 (b₃.2 hd)), e, d₃]
  refine ⟨a₁.trans (a₂.trans a₃), b₁.trans (b₂.trans b₃), c₁.trans (c₂.trans c₃), fun τ τ' hτ => ⟨fun hd a => ?_, key τ τ' hτ⟩⟩
  rw [isJumpE_iff P hd, ← key τ τ' hτ hd a, ← Multiset.count_ne_zero]
  exact Nat.cast_ne_zero.symm

theorem localPreds_of_bridge {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {O O' : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O']
    {pl : HeightOneSpectrum (𝓞 E) → ValuationSubring Ω}
    {br : ∀ w : HeightOneSpectrum (𝓞 E), w ∈ placesOver E l → LocBridge l E Ω (Dec (F := E) (pl w)) O}
    (hpl : ∀ w, IsPlaceOver (pl w) w) (hbr : ∀ w hw, Induces (br w hw)) {w : HeightOneSpectrum (𝓞 E)}
    (hw : w ∈ placesOver E l) (B : LocBridge l E Ω (Dec (F := E) (pl w)) O') (hB : Induces B)
    (φ : O' →+* Om l) (hφ : ∀ x, φ x = ((B.toLL x : ↥B.LL.1) : Om l)) :
    (∀ (m : ℕ) (ρ : G E Ω →* GL (Fin m) O'),
      (IsCrysW P pl br (mapRep φ ρ) w ↔ B.IsCrysW P (ρ.comp (Dec (F := E) (pl w)).subtype)) ∧
      (IsdRW P pl br (mapRep φ ρ) w ↔ B.IsdRW P (ρ.comp (Dec (F := E) (pl w)).subtype)) ∧
      (IsPotCrysW P pl br (mapRep φ ρ) w ↔ B.IsPotCrysW P (ρ.comp (Dec (F := E) (pl w)).subtype)) ∧
      (∀ (τ : E →+* Om l) (τ' : ↥B.Kw.1 →ₐ[ℚ_[l]] ↥B.LL.1), IsInduced B τ τ' →
        (B.IsdRW P (ρ.comp (Dec (F := E) (pl w)).subtype) → ∀ a : ℤ,
          a ∈ jumpsW P pl br (mapRep φ ρ) τ ↔ B.IsJumpW P (ρ.comp (Dec (F := E) (pl w)).subtype) τ' a) ∧
        (B.IsdRW P (ρ.comp (Dec (F := E) (pl w)).subtype) → ∀ a : ℤ,
          ((jumpsW P pl br (mapRep φ ρ) τ).count a : ℤ) = B.multW P (ρ.comp (Dec (F := E) (pl w)).subtype) τ' a))) ∧
    ∀ (LL' : FinExt l), B.LL.1 ≤ LL'.1 → ∀ (m : ℕ) (ρ : G E Ω →* GL (Fin m) ↥LL'.1),
      (IsCrysW P pl br (mapRep (algebraMap ↥LL'.1 (Om l)) ρ) w ↔ B.IsCrysE P LL' (ρ.comp (Dec (F := E) (pl w)).subtype)) ∧
      (IsdRW P pl br (mapRep (algebraMap ↥LL'.1 (Om l)) ρ) w ↔ B.IsdRE P LL' (ρ.comp (Dec (F := E) (pl w)).subtype)) ∧
      (IsPotCrysW P pl br (mapRep (algebraMap ↥LL'.1 (Om l)) ρ) w ↔ B.IsPotCrysE P LL' (ρ.comp (Dec (F := E) (pl w)).subtype)) ∧
      (∀ (τ : E →+* Om l) (τ' : ↥B.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced B τ τ' →
        (B.IsdRE P LL' (ρ.comp (Dec (F := E) (pl w)).subtype) → ∀ a : ℤ,
          a ∈ jumpsW P pl br (mapRep (algebraMap ↥LL'.1 (Om l)) ρ) τ ↔ B.IsJumpE P LL' (ρ.comp (Dec (F := E) (pl w)).subtype) τ' a) ∧
        (B.IsdRE P LL' (ρ.comp (Dec (F := E) (pl w)).subtype) → ∀ a : ℤ,
          ((jumpsW P pl br (mapRep (algebraMap ↥LL'.1 (Om l)) ρ) τ).count a : ℤ) =
            B.multE P LL' (ρ.comp (Dec (F := E) (pl w)).subtype) τ' a)) := by
  refine ⟨fun m ρ => ?_, fun LL' hL m ρ => ?_⟩
  · have h : IsModel B (resDec pl (mapRep φ ρ) w) B.LL (mapRep B.toLL (ρ.comp (Dec (F := E) (pl w)).subtype)) :=
      ⟨le_rfl, by ext g i j; exact (hφ _).symm⟩
    obtain ⟨a, b, c, d⟩ := localPreds_of_isModel P hpl hbr hw B hB h
    exact ⟨a, b, c, d⟩
  · have h : IsModel B (resDec pl (mapRep (algebraMap ↥LL'.1 (Om l)) ρ) w) LL' (ρ.comp (Dec (F := E) (pl w)).subtype) := ⟨hL, rfl⟩
    exact localPreds_of_isModel P hpl hbr hw B hB h



theorem nonempty_wdSide_of_tie (hB : GlobalTheory.Published.DeRhamPotSemistable) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) : Nonempty (WDSide D T) := by
  classical
  choose LL br hbr using fun (l : ℕ) (hl : Fact l.Prime) => exists_bridges l D.host.E D.nd.Om D.nd.plOm.1 D.nd.plOm.2
  let wd : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a}, (G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) → ∀ w, D.naut.LP w :=
    fun l hl ι a r w => (T.e w).symm (if hw : w ∈ placesOver D.host.E l then
      wdL (D.loc l) ι D.nd.plOm.1 (br l hl) r D.nd.plOm.2 (hbr l hl) w hw else GlobalTheory.WeilDeligne.wdOf (D.nd.plOm.2 w) hw ι r)
  have h1 : ∀ (l : ℕ) [hl : Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a} (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) w
      (hw : w ∈ placesOver D.host.E l), T.e w (wd l ι r w) = wdL (D.loc l) ι D.nd.plOm.1 (br l hl) r D.nd.plOm.2 (hbr l hl) w hw :=
    fun l hl ι a r w hw => by simp only [wd, Equiv.apply_symm_apply, dif_pos hw]
  have h2 : ∀ (l : ℕ) [hl : Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a} (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) w
      (hw : w ∉ placesOver D.host.E l), T.e w (wd l ι r w) = GlobalTheory.WeilDeligne.wdOf (D.nd.plOm.2 w) hw ι r :=
    fun l hl ι a r w hw => by simp only [wd, Equiv.apply_symm_apply, dif_neg hw]
  have hL := fun (l : ℕ) [hl : Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a} (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) w hw =>
    GlobalTheory.PstLaws.wdL_laws hB l (D.loc l) (D.locA l) (D.locT l) ι D.host.E D.nd.Om _ D.nd.plOm.1 (br l hl) D.nd.plOm.2 (hbr l hl) r w hw
  have hA := fun (l : ℕ) [hl : Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a} (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) w
    (hw : w ∉ placesOver D.host.E l) => GlobalTheory.WeilDeligne.wdOf_laws (D.nd.plOm.2 w) hw ι r
  refine ⟨{
    wdOf := wd
    wdOf_dim := fun l hl ι a r w => ?_
    wdOf_unr := fun l hl ι a r w hw hc => by rw [T.unr, h2 l ι r w hw]; exact ((hA l ι r w hw).2 hc).2.2.1
    wdOf_frob := fun l hl ι a r w hw hc hu B σ hp hσ => ?_
    wdOf_ine := fun l hl ι a r w hw hc σ hσ => by rw [T.inePol _ _ σ hσ, h2 l ι r w hw]; exact ((hA l ι r w hw).2 hc).2.2.2.2.1 σ hσ
    wdOf_mono0 := fun l hl ι a r w hw hc => by rw [T.mono0, h2 l ι r w hw]; exact ((hA l ι r w hw).2 hc).2.2.2.2.2
    IsCrysW := fun l hl _ _ r w => IsCrysW (D.loc l) D.nd.plOm.1 (br l hl) r w
    IsPotCrysW := fun l hl _ _ r w => IsPotCrysW (D.loc l) D.nd.plOm.1 (br l hl) r w
    IsdRW := fun l hl _ _ r w => IsdRW (D.loc l) D.nd.plOm.1 (br l hl) r w
    jumpsW := fun l hl _ _ r τ => jumpsW (D.loc l) D.nd.plOm.1 (br l hl) r τ
    wdOf_unrL := fun l hl ι a r w hw hc hd => by rw [T.unr, h1 l ι r w hw]; exact ((hL l ι r w hw).2 hc hd).1
    wdOf_mono0L := fun l hl ι a r w hw hc hd => by rw [T.mono0, h1 l ι r w hw]; exact ((hL l ι r w hw).2 hc hd).2
    away := fun l hl ι a r w hw => h2 l ι r w hw
    above := fun l hl ι a r w hw => ⟨LL l hl, br l hl w hw, hbr l hl w hw, h1 l ι r w hw⟩
    loc := fun l hl ι w hw O _ _ _ Bw hj φ hφ => ⟨fun m ρ _ => ?_, fun LL' hL' m ρ _ => ?_⟩ }⟩
  · rw [← T.dim]
    by_cases hw : w ∈ placesOver D.host.E l
    · rw [h1 l ι r w hw]; exact (hL l ι r w hw).1
    · rw [h2 l ι r w hw]; exact (hA l ι r w hw).1
  · rw [T.frobEig _ _ hu, h2 l ι r w hw]
    rw [T.unr, h2 l ι r w hw] at hu
    exact ((hA l ι r w hw).2 hc).2.2.2.1 hu B σ hp hσ
  · exact (localPreds_of_bridge (D.loc l) D.nd.plOm.2 (hbr l hl) hw Bw hj φ hφ).1 m ρ
  · exact (localPreds_of_bridge (D.loc l) D.nd.plOm.2 (hbr l hl) hw Bw hj φ hφ).2 LL' hL' m ρ

end GlobalTheory.HeightCounting
end
end

section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct Pointwise

namespace GlobalTheory.Mem.VolFin

theorem measure_lt_top_of_cover {G A B : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]
    [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [LocallyCompactSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]
    [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [LocallyCompactSpace B] [SecondCountableTopology B]
    [MeasurableSpace B] [BorelSpace B]
    (e : G ≃ₜ* A × B) (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsHaarMeasure]
    (S : Finset B) (K : Set B) (hK : IsCompact K) (Ω : B → Set A)
    (hΩ : ∀ s, (Measure.haar : Measure A) (Ω s) < ⊤)
    (hcov : ∀ g : G, ∃ γ : Γ, ∃ s ∈ S, (e (γ • g)).1 ∈ Ω s ∧ (e (γ • g)).2 ∈ s • K)
    (𝓕 : Set G) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) : μ 𝓕 < ⊤ := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup Γ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup Γ μ
  have h1 : (μ.map e).IsHaarMeasure := e.isHaarMeasure_map μ
  have h2 := Measure.isMulLeftInvariant_eq_smul (μ.map e)
    ((Measure.haar : Measure A).prod (Measure.haar : Measure B))
  have hle : μ 𝓕 ≤ μ (⋃ s ∈ S, e ⁻¹' (Ω s ×ˢ (s • K))) := by
    refine GlobalTheory.measure_le_of_isFundamentalDomain_of_ae_covers h𝓕 (.of_forall fun g => ?_)
    obtain ⟨γ, s, hs, h⟩ := hcov g
    exact ⟨γ, Set.mem_biUnion hs h⟩
  refine hle.trans_lt ((measure_biUnion_finset_le _ _).trans_lt (ENNReal.sum_lt_top.2 fun s _ => ?_))
  refine (Measure.le_map_apply (map_continuous e).measurable.aemeasurable _).trans_lt ?_
  rw [h2, Measure.smul_apply, Measure.prod_prod]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.mul_lt_top (hΩ s) (hK.smul s).measure_lt_top)

section Rat

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem sigR_inclR (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (x : E) :
    sigR R σ (inclR (F := F) R x) = inclR (F := F) R (σ x) := by
  simp [sigR, inclR]

noncomputable def ratPt (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) : Formalism.UG.UJ (σ : E →+* E) J →* HA R σ J where
  toFun γ := (⟨Formalism.UG.bc (inclR (F := F) R) γ.1, by
    have := congrArg (fun N => N.map (inclR (F := F) R)) (show Formalism.UG.cT _ _ * _ * _ = _ from γ.2)
    simp only [Matrix.map_mul] at this
    change Formalism.UG.cT _ _ * _ * _ = _
    refine Eq.trans ?_ this
    refine congrArg₂ (· * ·) (congrArg₂ (· * ·) ?_ rfl) rfl
    ext i j
    exact sigR_inclR R σ _⟩ : HR R σ J)
  map_one' := Subtype.ext (map_one (Formalism.UG.bc (inclR (F := F) R)))
  map_mul' a b := Subtype.ext (map_mul (Formalism.UG.bc (inclR (F := F) R)) _ _)

theorem topGroup_HA [FiniteDimensional F E] (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    IsTopologicalGroup (HA R σ J) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  exact inferInstanceAs (IsTopologicalGroup (HR R σ J))

theorem countable_HFinIn [Countable E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) : Countable (HFinIn R σ J) := by
  haveI : Countable (Matrix (Fin M) (Fin M) E) := inferInstanceAs (Countable (Fin M → Fin M → E))
  haveI : Countable (GL (Fin M) E) := Units.val_injective.countable
  refine Function.Surjective.countable
    (f := fun γ : Formalism.UG.UJ (σ : E →+* E) J => (⟨ratPt R σ J γ, γ.1, γ.2, rfl⟩ : HFinIn R σ J)) ?_
  rintro ⟨g, γ, hγ, h⟩
  exact ⟨⟨γ, hγ⟩, Subtype.ext (Subtype.ext h)⟩

variable [NumberField F]

theorem mulVec_fv {M : ℕ} (m : Matrix (Fin M) (Fin M) E) (x : Fin M → E) :
    (m.map (inclR (F := F) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F))).mulVec (GlobalTheory.AdLat.fv F x) = GlobalTheory.AdLat.fv F (m.mulVec x) := by
  ext i
  exact (RingHom.map_mulVec (inclR (F := F) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)) m x i).symm

theorem mulVec_mem_hat_of_rat {M : ℕ} (m : Matrix (Fin M) (Fin M) E) (Λ : Submodule (𝓞 E) (Fin M → E))
    (h : ∀ x ∈ Λ, m.mulVec x ∈ Λ) {z : Fin M → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E} (hz : z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin M → E))) :
    (m.map (inclR (F := F) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F))).mulVec z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin M → E)) := by
  refine GlobalTheory.AdLat.Translate.mulVec_mem_hat (fun x hx => ?_) hz
  rw [SetLike.mem_coe, GlobalTheory.AdLat.Translate.mem_pre, mulVec_fv]
  exact GlobalTheory.AdLat.Translate.fv_mem_hat (h x hx)

theorem stabHat_conj {M : ℕ} (δ : GL (Fin M) E) (L Λ : Submodule (𝓞 E) (Fin M → E))
    (s : GL (Fin M) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E))
    (hΛ : (GlobalTheory.AdLat.hat F (Λ : Set (Fin M → E)) : Set (Fin M → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E)) =
      (s : Matrix (Fin M) (Fin M) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E)).mulVec '' (GlobalTheory.AdLat.hat F (L : Set (Fin M → E))))
    (h : ∀ x, x ∈ Λ ↔ (δ : Matrix (Fin M) (Fin M) E).mulVec x ∈ Λ) :
    StabHat F (L : Set (Fin M → E))
      ((s⁻¹ * Formalism.UG.bc (inclR (F := F) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)) δ * s : GL (Fin M) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E)) :
        Matrix (Fin M) (Fin M) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E)) := by
  have him : ∀ y, y ∈ latHat F E (L : Set (Fin M → E)) ↔
      (s : Matrix (Fin M) (Fin M) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E)).mulVec y ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin M → E)) := by
    intro y
    rw [← SetLike.mem_coe (p := GlobalTheory.AdLat.hat F (Λ : Set (Fin M → E))), hΛ]
    constructor
    · exact fun hy => ⟨y, hy, rfl⟩
    · rintro ⟨u, hu, huy⟩
      have := congrArg ((s⁻¹ : GL (Fin M) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E)) : Matrix (Fin M) (Fin M) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E)).mulVec huy
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Matrix.one_mulVec] at this
      exact this ▸ hu
  intro y
  rw [him, him, Matrix.mulVec_mulVec y, ← Units.val_mul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul,
    Units.val_mul, ← Matrix.mulVec_mulVec]
  refine ⟨mulVec_mem_hat_of_rat _ Λ fun x hx => (h x).1 hx, fun hz => ?_⟩
  have := mulVec_mem_hat_of_rat ((δ⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) Λ (fun x hx => by
    rw [h, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]; exact hx) hz
  change ((Formalism.UG.bc (inclR (F := F) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)) δ⁻¹ : GL (Fin M) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E)) :
    Matrix (Fin M) (Fin M) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E)).mulVec _ ∈ _ at this
  rwa [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
    Matrix.one_mulVec] at this

end Rat

theorem finVol : FiniteVolume₂ := by
  intro F E _ _ _ _ _ σ hCM M J hJ μ hμ 𝓕 h𝓕
  classical
  haveI := topGroup_HA (AF F) σ J
  haveI := topGroup_HA (Ainf F) σ J
  haveI := topGroup_HA (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J
  haveI : BorelSpace (HA (AF F) σ J) := ⟨rfl⟩
  haveI : BorelSpace (HA (Ainf F) σ J) := ⟨rfl⟩
  haveI : BorelSpace (HA (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J) := ⟨rfl⟩
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_infiniteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_infiniteAdeleRing_of_numberField_field F
  obtain ⟨_, _, -⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_HA (Ainf F) σ M J
  obtain ⟨_, _, -⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_HA (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ M J
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  let Γ : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J
  haveI : Countable Γ := countable_HFinIn (AF F) σ J
  obtain ⟨e, he⟩ := GlobalTheory.Mem.VolSplit.exists_adelic_split F E σ M J
  have herat : ∀ γ, e (ratPt (AF F) σ J γ) = (ratPt (Ainf F) σ J γ, ratPt (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J γ) := by
    intro γ
    refine Prod.ext (Subtype.ext (Units.ext ((he _).2.trans ?_))) (Subtype.ext (Units.ext ((he _).1.trans ?_)))
    · ext i j
      change Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (inclR (F := F) (AF F) _) = inclR (F := F) (Ainf F) _
      simp [inclR]
    · ext i j
      change Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (inclR (F := F) (AF F) _) = inclR (F := F) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) _
      simp [inclR]
  let b := Pi.basisFun E (Fin M)
  let L : Submodule (𝓞 E) (Fin M → E) := Submodule.span (𝓞 E) (Set.range b)
  have hL : L.FG := Submodule.fg_span (Set.finite_range b)
  have hLs : Submodule.span E (L : Set (Fin M → E)) = ⊤ := by
    rw [eq_top_iff, ← b.span_eq]
    exact Submodule.span_mono Submodule.subset_span
  obtain ⟨K, hK, hKo, hKc⟩ := GlobalTheory.T.completedLattice_stabilizer_compact_open F E σ M J L hL hLs
  obtain ⟨S, hS⟩ := GlobalTheory.T.finite_classSet_hermitianUnitary_openLevel F E σ hCM M J hJ K hKo
  choose Λ _ hΛ1 hΛ2 hΛ3 using fun s : HA (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J =>
    GlobalTheory.AdLat.exists_lattice_latOf F E M L (HA.mat (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J s) hL hLs
  choose Ω _ hΩ1 hΩ2 using fun s : HA (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J =>
    GlobalTheory.T.finite_covolume_latticeStabiliser_unitaryRealPoints F E σ hCM M J hJ (Λ s) (hΛ1 s) (hΛ2 s) Measure.haar inferInstance
  refine measure_lt_top_of_cover e Γ μ S K hKc Ω hΩ1 (fun g => ?_) 𝓕 h𝓕
  obtain ⟨⟨γ', γ, hγ, hγγ⟩, s, hs, k, hk, hg⟩ := hS (e g).2
  have hg2 : (e g).2 = ratPt (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J ⟨γ, hγ⟩ * (s * k) := by
    rw [hg]
    exact congrArg (· * (s * k)) (Subtype.ext hγγ.symm : (γ' : HA (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J) = ratPt (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J ⟨γ, hγ⟩)
  obtain ⟨δ, hδ, hδΛ, w, hw, hwe⟩ := hΩ2 s ((ratPt (Ainf F) σ J ⟨γ, hγ⟩)⁻¹ * (e g).1)
  have hw1 : (ratPt (Ainf F) σ J ⟨γ, hγ⟩)⁻¹ * (e g).1 = ratPt (Ainf F) σ J ⟨δ, hδ⟩ * w := Subtype.ext hwe
  have hkδ : s⁻¹ * ratPt (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J ⟨δ, hδ⟩ * s ∈ K :=
    (hK _).2 (stabHat_conj δ L (Λ s) (HA.mat (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J s) (hΛ3 s) hδΛ)
  let η : Formalism.UG.UJ (σ : E →+* E) J := (⟨δ, hδ⟩ : Formalism.UG.UJ (σ : E →+* E) J)⁻¹ * (⟨γ, hγ⟩ : Formalism.UG.UJ (σ : E →+* E) J)⁻¹
  refine ⟨⟨ratPt (AF F) σ J η, η.1, η.2, rfl⟩, s, hs, ?_, ?_⟩
  · change (e (ratPt (AF F) σ J η * g)).1 ∈ _
    rw [map_mul, herat, Prod.fst_mul, map_mul, map_inv, map_inv, mul_assoc, hw1, inv_mul_cancel_left]
    exact hw
  · change (e (ratPt (AF F) σ J η * g)).2 ∈ _
    rw [map_mul, herat, Prod.snd_mul]
    dsimp only
    rw [map_mul, map_inv, map_inv, mul_assoc, hg2, inv_mul_cancel_left]
    refine ⟨_, K.mul_mem (K.inv_mem hkδ) hk, ?_⟩
    simp only [smul_eq_mul]
    group

end GlobalTheory.Mem.VolFin
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HeckeEigCoset

open GlobalTheory.LFun.ConjPlace

theorem heckeVec_Tj_inv_conj_eq_sum : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L)
    (ϖ : s.v.adicCompletion (maximalRealSubfield L)), IsUnif L s.v ϖ → ∀ (k : ℕ), k ≤ n →
    ∀ (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* (GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L), Continuous i →
    ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) ((GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L)) V)
    (R : Finset (GAf L n)), (∀ γ ∈ R, γ ∈ tSet L n s ϖ k) → (∀ x ∈ tSet L n s ϖ k, ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ Umax L n) →
    ∀ e ∈ GlobalTheory.PRep.fixed ρ (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n),
      GlobalTheory.LFun.heckeVec ρ (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n)
                   (fun g => Formalism.UG.Tj ℂ n (Formalism.UG.Ov L (GlobalTheory.HeckeFrob.conjSplit s).w) (i ϖ) k g⁻¹) e =
        ∑ γ ∈ R, ρ (Matrix.GeneralLinearGroup.map i.toRingHom ((GlobalTheory.HeckeFrob.conjSplit s).loc n γ)) e := by
  intro L _ _ _ n s ϖ hϖ k hk i hi V _ _ ρ R hR1 hR2 e he
  classical
  have hO : ∀ a, i a ∈ Formalism.UG.Ov L (GlobalTheory.HeckeFrob.conjSplit s).w ↔
      a ∈ (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring := by
    intro a
    have h := GlobalTheory.T.valued_le_one_iff_of_continuous_ringEquiv _ _ s.v (GlobalTheory.HeckeFrob.conjSplit s).w i hi a
    exact h.trans (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).symm
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    have h0 : Valued.v (0 : s.v.adicCompletion (maximalRealSubfield L)) = WithZero.exp (-1 : ℤ) := hϖ
    rw [map_zero] at h0
    exact WithZero.exp_ne_zero h0.symm
  set ϖu : (s.v.adicCompletion (maximalRealSubfield L))ˣ := Units.mk0 ϖ hϖ0 with hϖu
  have ha : invT i n (dGL n ϖu k) = (dGL n (Units.map (i : _ →* _) ϖu) k)⁻¹ := by
    rw [← invT_dGL, map_inv, inv_inv]
  have h1 : (fun g => Formalism.UG.Tj ℂ n (Formalism.UG.Ov L (GlobalTheory.HeckeFrob.conjSplit s).w) (i ϖ) k g⁻¹) =
      Formalism.UG.dosetInd ℂ (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n) (invT i n (dGL n ϖu k)) := by
    funext g
    have hiϖ : i ϖ = ((Units.map (i : s.v.adicCompletion (maximalRealSubfield L) →* (GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L) ϖu :
        ((GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L)ˣ) : (GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L) := by
      rw [Units.coe_map, hϖu, Units.val_mk0]
      rfl
    rw [hiϖ, Tj_apply, Formalism.UG.dosetInd, Set.indicator_apply, Pi.one_apply]
    refine if_congr ?_ rfl rfl
    rw [DoubleCoset.mem_doubleCoset, ha]
    constructor
    · rintro ⟨x, hx, y, hy, h⟩
      exact ⟨y⁻¹, inv_mem hy, x⁻¹, inv_mem hx, by rw [← inv_inv g, h]; group⟩
    · rintro ⟨x, hx, y, hy, h⟩
      exact ⟨y⁻¹, inv_mem hy, x⁻¹, inv_mem hx, by rw [h]; group⟩
  have hK : ∀ x : GAf L n, TrivOutside {s.v} x → (x ∈ tSet L n s ϖ k ↔ invT i n (s.loc n x) ∈
      DoubleCoset.doubleCoset (invT i n (dGL n ϖu k)) (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n : Set _)
        (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n)) := by
    intro x hx
    rw [tSet, Set.mem_setOf_eq, DoubleCoset.mem_doubleCoset]
    constructor
    · rintro ⟨-, A, hA, B, hB, h⟩
      refine ⟨invT i n A, (mem_iff_invT i hO A).1 hA, invT i n B, (mem_iff_invT i hO B).1 hB, ?_⟩
      have : s.loc n x = A * dGL n ϖu k * B := Units.ext (by rw [Units.val_mul, Units.val_mul, h]; rfl)
      rw [this, map_mul, map_mul]
    · rintro ⟨A', hA', B', hB', h⟩
      obtain ⟨A, rfl⟩ := (invT i n).surjective A'
      obtain ⟨B, rfl⟩ := (invT i n).surjective B'
      rw [← map_mul, ← map_mul, (invT i n).apply_eq_iff_eq] at h
      refine ⟨hx, A, (mem_iff_invT i hO A).2 hA', B, (mem_iff_invT i hO B).2 hB', ?_⟩
      rw [h]
      rfl
  have hφK : ∀ x : GAf L n, TrivOutside {s.v} x →
      (invT i n (s.loc n x) ∈ GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n ↔ x ∈ Umax L n) :=
    fun x hx => (mem_iff_invT i hO _).symm.trans (GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff s hx)
  have hRa : ∀ γ' ∈ R.image (fun γ => invT i n (s.loc n γ)), γ' ∈ DoubleCoset.doubleCoset (invT i n (dGL n ϖu k))
      (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n : Set _) (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n) := by
    intro γ' hγ'
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.1 hγ'
    exact (hK γ (hR1 γ hγ).1).1 (hR1 γ hγ)
  have hRb : ∀ g ∈ DoubleCoset.doubleCoset (invT i n (dGL n ϖu k))
      (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n : Set _) (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n),
      ∃! γ', γ' ∈ R.image (fun γ => invT i n (s.loc n γ)) ∧ γ'⁻¹ * g ∈ GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n := by
    intro g hg
    obtain ⟨-, -, hlift⟩ := GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s
    obtain ⟨x, ⟨hx, hxg⟩, -⟩ := hlift ((invT i n).symm g)
    have hgx : g = invT i n (s.loc n x) := by rw [hxg]; simp
    have hxT : x ∈ tSet L n s ϖ k := (hK x hx).2 (hgx ▸ hg)
    obtain ⟨γ, ⟨hγ, hγx⟩, huniq⟩ := hR2 x hxT
    have key : ∀ δ ∈ R, (invT i n (s.loc n δ))⁻¹ * g ∈ GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n ↔
        δ⁻¹ * x ∈ Umax L n := by
      intro δ hδ
      rw [hgx, ← map_inv, ← map_inv, ← map_mul, ← map_mul]
      exact hφK _ (GlobalTheory.HeckeScalarSph.triv_mul (GlobalTheory.HeckeScalarSph.triv_inv (hR1 δ hδ).1) hx)
    refine ⟨invT i n (s.loc n γ), ⟨Finset.mem_image_of_mem _ hγ, (key γ hγ).2 hγx⟩, ?_⟩
    rintro γ' ⟨hγ', hγ'g⟩
    obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.1 hγ'
    rw [huniq δ ⟨hδ, (key δ hδ).1 hγ'g⟩]
  have hinj : Set.InjOn (fun γ => invT i n (s.loc n γ)) R := by
    intro γ₁ h₁ γ₂ h₂ heq
    have hγ₂ := hR1 γ₂ h₂
    obtain ⟨γ, -, huniq⟩ := hR2 γ₂ hγ₂
    have e1 : γ₁⁻¹ * γ₂ ∈ Umax L n := by
      rw [← hφK _ (GlobalTheory.HeckeScalarSph.triv_mul (GlobalTheory.HeckeScalarSph.triv_inv (hR1 γ₁ h₁).1) hγ₂.1), map_mul, map_mul,
        map_inv, map_inv]
      simp only at heq
      rw [heq, inv_mul_cancel]
      exact one_mem _
    exact (huniq γ₁ ⟨h₁, e1⟩).trans (huniq γ₂ ⟨h₂, by rw [inv_mul_cancel]; exact one_mem _⟩).symm
  rw [h1, GlobalTheory.LFun.heckeVec_dosetInd he hRa hRb, Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [GlobalTheory.HeckeEigConj.map_loc_conjSplit]

end GlobalTheory.HeckeEigCoset
end

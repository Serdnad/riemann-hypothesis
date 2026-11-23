module

public import Formalism.ConjugateSelfDual.Bundle001
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle003
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DerivationCoordinateChange
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalToGlobal.Columns.Bundle002
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle107
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.GaloisValuations.GlobalB
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle013
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.NeutralLocalFields.Bundle001
import Formalism.GaussJetBounds.Bundle001
public import Formalism.GaussJetBounds.Bundle003

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.OpenNormal

theorem exists_open_normal_le : ∀ (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] [IsAlgClosure F Ω] (U : Subgroup (Formalism.ConjugateSelfDual.G F Ω)), IsOpen (U : Set (Formalism.ConjugateSelfDual.G F Ω)) → ∃ N : Subgroup (Formalism.ConjugateSelfDual.G F Ω), N.Normal ∧ IsOpen (N : Set (Formalism.ConjugateSelfDual.G F Ω)) ∧ N.FiniteIndex ∧ N ≤ U := by
  intro Ω _ F _ _ _ _ U hU
  haveI : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  haveI : CompactSpace (Formalism.ConjugateSelfDual.G F Ω) := inferInstanceAs (CompactSpace Gal(Ω/F))
  haveI : Finite (Formalism.ConjugateSelfDual.G F Ω ⧸ U) := Subgroup.quotient_finite_of_isOpen U hU
  haveI : U.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  refine ⟨U.normalCore, U.normalCore_normal, ?_, inferInstance, U.normalCore_le⟩
  exact Subgroup.isOpen_of_isClosed_of_finiteIndex _ (U.normalCore_isClosed (U.isClosed_of_isOpen hU))

end GlobalTheory.OpenNormal
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL

private theorem coe_le_one {L Ω : Type} [Field Ω] [Field L] [NumberField L] [Algebra L Ω]
    (A : ValuationSubring Ω) (c : 𝓞 L) : A.valuation (algebraMap L Ω (c : L)) ≤ 1 :=
  (A.valuation_le_one_iff _).mpr
    (ReciprocityTheory.Gal.mem_of_isIntegral_int A (map_isIntegral_int (algebraMap L Ω) c.isIntegral_coe))

theorem exists_isPlaceOver_of_tower : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)), Formalism.ConjugateSelfDual.IsPlaceOver A v → ∃ v' : HeightOneSpectrum (𝓞 L), Formalism.ConjugateSelfDual.IsPlaceOver A v' ∧ v'.under (𝓞 K) = v := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v h
  let m : Ideal (𝓞 L) :=
    { carrier := {y | A.valuation (algebraMap L Ω (y : L)) < 1}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, map_add (f := _)] at ha hb ⊢
        exact Valuation.map_add_lt _ ha hb
      zero_mem' := by simp
      smul_mem' := by
        intro c y hy
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul] at hy ⊢
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (coe_le_one A c)) hy }
  have hmem : ∀ y : 𝓞 L, y ∈ m ↔ A.valuation (algebraMap L Ω (y : L)) < 1 := fun y => Iff.rfl
  have hprime : m.IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ne, Ideal.eq_top_iff_one, hmem]; simp
    · intro x y hxy
      rw [hmem, hmem] at *
      have e : ((x * y : 𝓞 L) : L) = (x : L) * y := rfl
      rw [e, map_mul, map_mul] at hxy
      by_contra hc
      push_neg at hc
      exact absurd hxy (not_lt.mpr (one_le_mul hc.1 hc.2))
  have hK : ∀ x : 𝓞 K, (algebraMap (𝓞 K) (𝓞 L) x ∈ m ↔ x ∈ v.asIdeal) := by
    intro x
    rw [hmem, ← h x]
    have : algebraMap L Ω ((algebraMap (𝓞 K) (𝓞 L) x : 𝓞 L) : L) = algebraMap K Ω (x : K) := by
      have e : ((algebraMap (𝓞 K) (𝓞 L) x : 𝓞 L) : L) = algebraMap K L (x : K) := rfl
      rw [e, ← IsScalarTower.algebraMap_apply]
    rw [this]
  have hne : m ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    intro hb
    have h1 : algebraMap (𝓞 K) (𝓞 L) x ∈ m := (hK x).mpr hx
    rw [hb, Ideal.mem_bot] at h1
    apply hx0
    exact (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L)) (by rw [h1, map_zero])
  refine ⟨⟨m, hprime, hne⟩, ?_, ?_⟩
  · intro y
    exact (hmem y).symm.trans Iff.rfl
  · apply HeightOneSpectrum.ext
    ext x
    exact hK x

end GlobalTheory.AboveL
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL

theorem exists_open_trace_ne_zero (Ω : Type) [Field Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
    (l : ℕ) [Fact l.Prime] (a : ℕ) (ha : 1 ≤ a) (r : Formalism.ConjugateSelfDual.G K Ω →* GL (Fin a) (Qbar l)) (hr : Continuous r) :
    ∃ N : Subgroup (Formalism.ConjugateSelfDual.G K Ω), IsOpen (N : Set (Formalism.ConjugateSelfDual.G K Ω)) ∧ ∀ n ∈ N, (r n).val.trace ≠ 0 := by
  have hc : Continuous fun g : Formalism.ConjugateSelfDual.G K Ω => (r g).val.trace :=
    (Units.continuous_val.comp hr).matrix_trace
  set U : Set (Formalism.ConjugateSelfDual.G K Ω) := {g | (r g).val.trace ≠ 0} with hU
  have hUo : IsOpen U := isOpen_ne_fun hc continuous_const
  have h1 : (1 : Formalism.ConjugateSelfDual.G K Ω) ∈ U := by
    simp only [hU, Set.mem_setOf_eq, map_one, Units.val_one, Matrix.trace_one, Fintype.card_fin]
    exact_mod_cast (by omega : a ≠ 0)
  obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff K Ω U).mp (hUo.mem_nhds h1)
  exact ⟨E.fixingSubgroup, E.fixingSubgroup_isOpen, fun n hn => hEU hn⟩

end GlobalTheory.AboveL
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker

namespace GlobalTheory

namespace ThetaCosetSum

open Formalism.L2.Th1.H

theorem xiL_eq_kernel {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (vol : ℝ) (SX SA SB : Finset V)
    (Φ e : V → ℂ) (z : V) :
    xiL H α vol SX SA SB Φ e z = (((Real.sqrt vol : ℝ) : ℂ)⁻¹ * ((vol : ℝ) : ℂ)) *
      ∑ x ∈ SX, ∑ y ∈ SB, ∑ t ∈ SA, Φ (t - x) *
        (α x * ((SA.card : ℂ)⁻¹ * (brk H y t)⁻¹ * α y * opU H y e (z + x)) *
          Complex.exp (-(Real.pi : ℂ) * H z x - (Real.pi : ℂ) * H x x / 2)) := by
  unfold xiL
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [opU]
  simp only [xiS, sumU, hatS, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun t _ => ?_
  ring

theorem sum_xiL {V ι : Type} [AddCommGroup V] [Module ℂ V] [Fintype ι] (H : Sesq V) (α : V → ℂ) (vol : ℝ) (hv : 0 < vol)
    (SX SA SB : Finset V) (c : ι → ℂ) (Φ : ι → V → ℂ) (Ψ e : V → ℂ) (hΨ : ∀ t, Ψ t = ∑ i, c i * Φ i t) (z : V) :
    ∑ i, c i * (((Real.sqrt vol : ℝ) : ℂ)⁻¹ * xiL H α vol SX SA SB (Φ i) e z) = xiL H α 1 SX SA SB Ψ e z := by
  have hs : ((Real.sqrt vol : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hv).ne'
  have h2 : ((vol : ℝ) : ℂ) = ((Real.sqrt vol : ℝ) : ℂ) * ((Real.sqrt vol : ℝ) : ℂ) := by
    exact_mod_cast (Real.mul_self_sqrt hv.le).symm
  have h3 : ∀ w : ℂ, ((Real.sqrt vol : ℝ) : ℂ)⁻¹ * ((((Real.sqrt vol : ℝ) : ℂ)⁻¹ * ((vol : ℝ) : ℂ)) * w) = w := by
    intro w
    generalize ((Real.sqrt vol : ℝ) : ℂ) = s at hs h2
    rw [h2]; field_simp
  simp only [xiL_eq_kernel, h3, Real.sqrt_one, Complex.ofReal_one, inv_one, one_mul, hΨ, Finset.sum_mul]
  simp only [Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_comm]


open Classical in
theorem eq_sum_coset {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (A B : Submodule R M) (hBA : B ≤ A)
    [Fintype (↥A ⧸ B.comap A.subtype)] (Ξ : M → ℂ) (h1 : ∀ x, Ξ x ≠ 0 → x ∈ A) (h2 : ∀ x, ∀ y ∈ B, Ξ (x + y) = Ξ x)
    (r : (↥A ⧸ B.comap A.subtype) → ↥A) (hr : ∀ q, Submodule.Quotient.mk (r q) = q) (t : M) :
    Ξ t = ∑ q, Ξ (r q) * (if t - (r q : M) ∈ B then 1 else 0) := by
  by_cases ht : t ∈ A
  · have key : ∀ q, t - (r q : M) ∈ B ↔ q = Submodule.Quotient.mk (⟨t, ht⟩ : ↥A) := by
      intro q
      rw [eq_comm]
      conv_rhs => rw [← hr q]
      rw [Submodule.Quotient.eq]
      rfl
    rw [Finset.sum_eq_single (Submodule.Quotient.mk (⟨t, ht⟩ : ↥A))]
    · have hm := (key _).mpr rfl
      rw [if_pos hm, mul_one, ← h2 (r (Submodule.Quotient.mk (⟨t, ht⟩ : ↥A)) : M) _ hm, add_sub_cancel]
    · intro q _ hq
      rw [if_neg (fun h => hq ((key q).mp h)), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · have h0 : Ξ t = 0 := by
      by_contra h
      exact ht (h1 t h)
    rw [h0]
    symm
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [if_neg, mul_zero]
    intro h
    apply ht
    have := A.add_mem (hBA h) (r q).2
    simpa using this

end ThetaCosetSum


open ThetaCosetSum in
theorem latSum_thInd_eq_thC : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (cA cB : ℕ) (Ξ : HomE X.E a b → ℂ), A.IndTieD a b S (cA * cB) → IsSdLat N → IsSdLat N' → 0 < cA → 0 < cB → 0 < volC A.AA S N N' → Finite (↥(divLat cA (homAt S N N')) ⧸ (mulLat cB (homAt S N N')).comap (divLat cA (homAt S N N')).subtype) → (∀ x, Ξ x ≠ 0 → x ∈ divLat cA (homAt S N N')) → (∀ x, ∀ y ∈ mulLat cB (homAt S N N'), Ξ (x + y) = Ξ x) → ∀ z, latSum (divLat cA (homAt S N N')) (mulLat cB (homAt S N N')) (fun x => Ξ x * A.thInd S N N' cB x z) = thC (X.embC A.σ₀) A.δ A.d A.sc A.AA S N N' (cA * cB) Ξ (A.e a b N N') z := by
  intro X A a b S N N' cA cB Ξ hT hN hN' hA hB hv hfin h1 h2 z
  classical
  let _ := Fintype.ofFinite (↥(divLat cA (homAt S N N')) ⧸ (mulLat cB (homAt S N N')).comap (divLat cA (homAt S N N')).subtype)
  have hle : mulLat cB (homAt S N N') ≤ divLat cA (homAt S N N') := by
    rintro _ ⟨y, hy, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hy)
  have hdiv : ∀ x ∈ divLat cA (homAt S N N'), x ∈ divLat (cA * cB) (homAt S N N') := by
    intro x hx
    have h : (cB : 𝓞 X.E) • (cA : 𝓞 X.E) • x ∈ homAt S N N' := Submodule.smul_mem _ _ hx
    rw [smul_smul, mul_comm, ← Nat.cast_mul] at h
    exact h
  unfold latSum
  rw [finsum_eq_sum_of_fintype]
  set r := Function.surjInv (Submodule.Quotient.mk_surjective
    ((mulLat cB (homAt S N N')).comap (divLat cA (homAt S N N')).subtype)) with hr
  have hrq : ∀ q, Submodule.Quotient.mk (r q) = q := fun q => Function.surjInv_eq _ q
  have hx : ∀ q, A.thInd S N N' cB (r q : HomE X.E a b) z = _ := fun q =>
    hT N N' cB (r q) ⟨hN, hN', hB, Dvd.intro_left _ rfl, hdiv _ (r q).2⟩ (Nat.mul_pos hA hB) z
  simp only [hx]
  unfold xiC thC xiV
  refine sum_xiL _ _ _ hv _ _ _ (fun q => Ξ (r q)) (fun q => onV (X.embC A.σ₀) A.δ (cosInd S N N' cB (r q))) _ _ ?_ z
  intro v
  unfold onV
  split_ifs with h
  · have := eq_sum_coset _ _ hle Ξ h1 h2 r hrq h.choose
    rw [this]
    refine Finset.sum_congr rfl fun q _ => ?_
    unfold cosInd
    congr
  · simp

end GlobalTheory
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric Classical
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

namespace GlobalTheory.Proof.IntegralEigenCombination

theorem eigGen_integral_comb : ∀ (D : D7) (cD : D.what₂.Tau → ℂ), Formalism.L2.Ker.IsDgen D cD → ∀ (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]), ∀ τ : D.what₂.Tau, ∃ (n : ℕ) (r : Fin n → ℂ_[p]) (a : Fin n → D.host.E), (∀ j, ‖r j‖ ≤ 1) ∧ (∀ j, a j ∈ D.host.AA0) ∧ ∀ τ', ∑ j, r j * tauEmb D lm τ' (a j) = if τ' = τ then lamC lm (cD τ) else 0 := by
  intro D cD hD p _ lm τ
  obtain ⟨M, hMnf, hM, hs⟩ := hD
  obtain ⟨s, hsc, hsp⟩ := hs τ
  have hmem : s ∈ TaylorLogMetric.ellT D M τ := by rw [hsp]; exact Submodule.mem_span_singleton_self s
  have hv : (LinearMap.single (𝓞 M) (fun _ : D.what₂.Tau => (M : Type)) τ) s ∈ TaylorLogMetric.mmM D M :=
    Submodule.mem_comap.1 hmem
  obtain ⟨n, f, v, hfv⟩ := Submodule.mem_span_set'.1 hv
  have hva : ∀ j, ∃ a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E),
      (v j : D.what₂.Tau → M) = fun τ => TaylorLogMetric.liftM M (TaylorLogMetric.embT D τ a) := fun j => (v j).2
  choose a ha hav using hva
  obtain ⟨g, hg⟩ := GlobalTheory.Proof.DirectionalDerivative.exists_lamHom lm (algebraMap M ℂ)
  have hg' : ∀ x : M, lamC lm (x : ℂ) = g x := hg
  refine ⟨n, fun j => g ((f j : 𝓞 M) : M), a, fun j => ?_, ha, fun τ' => ?_⟩
  · exact GlobalTheory.SplitEmbSep.norm_le_one_of_isIntegral (map_isIntegral_int g (f j).isIntegral_coe)
  · have e : ∀ j, tauEmb D lm τ' (a j) = g (TaylorLogMetric.liftM M (TaylorLogMetric.embT D τ' (a j))) := by
      intro j
      rw [← hg', TaylorLogMetric.liftM, dite_eq_left (hM _ _)]
      rfl
    have hc := congrFun hfv τ'
    simp only [Finset.sum_apply, Pi.smul_apply, hav] at hc
    simp only [e, ← map_mul]

    rw [← map_sum]
    have hc' : (∑ j, ((f j : 𝓞 M) : M) * TaylorLogMetric.liftM M (TaylorLogMetric.embT D τ' (a j))) =
        (LinearMap.single (𝓞 M) (fun _ : D.what₂.Tau => (M : Type)) τ) s τ' := by
      rw [← hc]; rfl
    rw [hc']
    by_cases h : τ' = τ
    · subst h; simp [hsc.symm, hg']
    · simp [h]
end GlobalTheory.Proof.IntegralEigenCombination
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col NumberField IsDedekindDomain

namespace GlobalTheory.ColumnField

theorem conj_notMem_inertia (D : D7) (X : Fields) (s : Seam D X) (hs : s.Ok) (P : HeightOneSpectrum (𝓞 X.E)) :
    ¬ ∀ x : 𝓞 X.E, X.conjO x - x ∈ P.asIdeal := by
  intro hall
  let φ : 𝓞 X.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv s.iE
  let P' : Ideal (𝓞 D.host.E) := P.asIdeal.comap (φ.symm : 𝓞 D.host.E →+* 𝓞 X.E)
  have hmax : P'.IsMaximal :=
    have := P.isMaximal
    Ideal.comap_isMaximal_of_surjective _ φ.symm.surjective
  obtain ⟨θ, t, h1, h2⟩ := Formalism.BasicNotions.Examples₂.unram_at D.host P' hmax
  have hcoe : ∀ y : 𝓞 X.E, algebraMap (𝓞 D.host.E) D.host.E (φ y) = s.iE (algebraMap (𝓞 X.E) X.E y) := fun _ => rfl
  have e : φ.symm t = X.conjO (φ.symm θ) := by
    apply φ.injective
    apply RingOfIntegers.ext
    rw [RingEquiv.apply_symm_apply]
    change algebraMap (𝓞 D.host.E) D.host.E t = algebraMap (𝓞 D.host.E) D.host.E (φ (X.conjO (φ.symm θ)))
    rw [hcoe, h1]
    change _ = s.iE (star (algebraMap (𝓞 X.E) X.E (φ.symm θ)))
    rw [hs.2, ← hcoe, RingEquiv.apply_symm_apply]
  apply h2
  change φ.symm (θ - t) ∈ P.asIdeal
  rw [map_sub, e, ← neg_sub]
  exact P.asIdeal.neg_mem (hall _)

theorem ramificationIdxIn_eq_one : ∀ (D : D7) (X : Fields) (s : Seam D X), X.Ok → s.Ok →
    ∀ v : HeightOneSpectrum (𝓞 X.F), v.asIdeal.ramificationIdxIn (𝓞 X.E) = 1 := by
  intro D X s hX hs v
  have : Algebra.IsQuadraticExtension X.F X.E := ⟨hX.rankE⟩
  have : IsGalois X.F X.E := inferInstance
  have := v.isMaximal
  obtain ⟨Q, hQ, hlo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 X.E) v.asIdeal
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
  let P : HeightOneSpectrum (𝓞 X.E) := ⟨Q, hQ.isPrime, hQ0⟩
  have hun := hX.unram_of_inertia (conj_notMem_inertia D X s hs) P
  have hcomap : Q.comap (algebraMap (𝓞 X.F) (𝓞 X.E)) = v.asIdeal := (Ideal.over_def Q v.asIdeal).symm
  have hun' : ¬ v.asIdeal.map (algebraMap (𝓞 X.F) (𝓞 X.E)) ≤ Q ^ 2 := by
    rw [← hcomap]
    exact hun
  have h1 : v.asIdeal.map (algebraMap (𝓞 X.F) (𝓞 X.E)) ≤ Q ^ 1 := by
    rw [pow_one, Ideal.map_le_iff_le_comap, hcomap]
  have he : v.asIdeal.ramificationIdx' Q = 1 := Ideal.ramificationIdx_spec h1 hun'
  have := hQ.isPrime
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ Q (X.E ≃ₐ[X.F] X.E),
    ← Ideal.ramificationIdx'_eq_ramificationIdx _ _ v.ne_bot]
  exact he

end GlobalTheory.ColumnField
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

theorem _root_.GlobalTheory.T.placeCompletion_le_maxUnramified_away_2qd : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} (nbr : Br.NBr N) (i : N.Loc) (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E (N.l i)), N.l i ∉ H.small → N.l i ≠ H.q → N.l i ≠ H.d → (nbr i w hw).Kw.1 ≤ Loc.MaximalUnramifiedExtension (N.l i) := by
  first | exact @GlobalTheory.bridge_field_le_unramified | exact GlobalTheory.bridge_field_le_unramified | (intros; apply GlobalTheory.bridge_field_le_unramified <;> assumption)
end

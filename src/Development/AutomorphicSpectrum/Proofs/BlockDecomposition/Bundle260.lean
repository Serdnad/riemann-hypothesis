module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle214
public import GroundTheory.PAdicHodge.Bundle004
public import GroundTheory.LocalFields.LubinTateTorsion
public import GroundTheory.LocalFields.UnramifiedHensel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemFiniteExtPadicRingOfIntegersIffNormLeOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfEq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle216
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle045
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle250
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle248
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle223
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.NeutralLocalFields.Bundle001

@[expose] public section

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.LTPer

theorem map_subst_comm {A B : Type} [CommRing A] [CommRing B] (h : A →+* B) {F G : PowerSeries A}
    {F' : PowerSeries B} (hF' : PowerSeries.map h F = F')
    (hF : PowerSeries.constantCoeff F = 0) (hG : PowerSeries.constantCoeff G = 0)
    (hs : PowerSeries.subst G F = PowerSeries.subst F G) :
    PowerSeries.subst (PowerSeries.map h G) F' = PowerSeries.subst F' (PowerSeries.map h G) := by
  subst hF'
  have h2 := congrArg (MvPowerSeries.map h) hs
  rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hG),
    PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hF)] at h2
  exact h2


open GlobalTheory.CompanionTheory.LTHodge.CharEx GroundTheory.LocalField GroundTheory.LocalField.FormalGroup ValuativeRel in
theorem exists_series_comm : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)), Irreducible π → ∀ a : ↥(OL K),
    ∃ φ : PowerSeries ↥(OL K), PowerSeries.constantCoeff φ = 0 ∧ PowerSeries.coeff 1 φ = a ∧
      PowerSeries.subst φ (ltSeries π) = PowerSeries.subst (ltSeries π) φ := by
  intro l _ K π hπ a
  have : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  let e : ↥(OL K) ≃+* 𝒪[↥K.1] := intEquiv K
  let es : 𝒪[↥K.1] →+* ↥(OL K) := (e.symm : 𝒪[↥K.1] →+* ↥(OL K))
  have hp : Irreducible (e π) := (MulEquiv.irreducible_iff e).mpr hπ
  have hf := isLubinTateSeries_ltPoly (e π)
  have hm := map_ltSeries K hp
  have hes : (intEquiv K).symm (e π) = π := e.symm_apply_apply π
  rw [hes] at hm
  have hF : PowerSeries.map es (ltPoly (e π) : PowerSeries 𝒪[↥K.1]) = ltSeries π := by
    rw [← hm]
    refine PowerSeries.ext fun n => ?_
    rw [PowerSeries.coeff_map, PowerSeries.coeff_map]
    exact e.symm_apply_apply _
  have hF0 : PowerSeries.constantCoeff (ltPoly (e π) : PowerSeries 𝒪[↥K.1]) = 0 :=
    hf.constantCoeff_eq_zero
  let h := lubinTateHom hp hf hf (e a)
  have h0 : PowerSeries.constantCoeff h.toPowerSeries = 0 := h.constantCoeff_eq_zero
  have h1 : PowerSeries.coeff 1 h.toPowerSeries = e a := coeff_one_lubinTateHom hp hf hf (e a)
  have hs := subst_lubinTateHom hp hf hf (e a)
  refine ⟨PowerSeries.map es h.toPowerSeries, ?_, ?_, ?_⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h0, map_zero]
  · rw [PowerSeries.coeff_map, h1]
    exact e.symm_apply_apply a
  · exact map_subst_comm es hF hF0 h0 hs

end GlobalTheory.CompanionTheory.LTPer
end
end

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

namespace GlobalTheory.CompanionTheory.LTHodge.UnitAct

section Ring

variable {l : ℕ} [Fact l.Prime] {K : FinExt l}
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Algebra F (Om l)] [ValuativeExtension F (Om l)]

theorem valuation_le_one_iff (x : F) :
    valuation F x ≤ 1 ↔ ‖algebraMap F (Om l) x‖ ≤ 1 := by
  rw [← map_one (valuation F), ← (valuation F).vle_iff_le, ← ValuativeExtension.vle_iff_vle (B := Om l),
    GroundTheory.PAdicHodge.CyclNorms.vle_iff_norm_le, map_one, norm_one]

theorem exists_ringEquiv (hR : Set.range (algebraMap F (Om l)) = (K.1 : Set (Om l))) :
    ∃ ρ : 𝒪[F] ≃+* ↥(OL K), ∀ a : 𝒪[F],
      (((ρ a : ↥(OL K)) : ↥K.1) : Om l) = algebraMap F (Om l) (a : F) := by
  have hmem : ∀ a : 𝒪[F], algebraMap F (Om l) (a : F) ∈ K.1 := fun a => by
    have h : algebraMap F (Om l) (a : F) ∈ (K.1 : Set (Om l)) := hR ▸ ⟨_, rfl⟩
    exact h
  have hO : ∀ a : 𝒪[F], (⟨_, hmem a⟩ : ↥K.1) ∈ OL K := fun a =>
    (GlobalTheory.IntNormFinExt.mem_OL_iff_norm_le_one l K _).mpr ((valuation_le_one_iff (a : F)).mp a.2)
  let f : 𝒪[F] →+* ↥(OL K) :=
    { toFun := fun a => ⟨⟨_, hmem a⟩, hO a⟩
      map_one' := Subtype.ext (Subtype.ext (by simp))
      map_mul' := fun a b => Subtype.ext (Subtype.ext (by simp))
      map_zero' := Subtype.ext (Subtype.ext (by simp))
      map_add' := fun a b => Subtype.ext (Subtype.ext (by simp)) }
  have hinj : Function.Injective f := fun a b hab => by
    have h : algebraMap F (Om l) (a : F) = algebraMap F (Om l) (b : F) :=
      congrArg (fun c : ↥(OL K) => ((c : ↥K.1) : Om l)) hab
    exact Subtype.ext ((algebraMap F (Om l)).injective h)
  have hsurj : Function.Surjective f := fun b => by
    have hb : ((b : ↥K.1) : Om l) ∈ (K.1 : Set (Om l)) := (b : ↥K.1).2
    rw [← hR] at hb
    obtain ⟨y, hy⟩ := hb
    have hn : ‖algebraMap F (Om l) y‖ ≤ 1 := by
      rw [hy]
      exact (GlobalTheory.IntNormFinExt.mem_OL_iff_norm_le_one l K _).mp b.2
    exact ⟨⟨y, (valuation_le_one_iff y).mpr hn⟩, Subtype.ext (Subtype.ext hy)⟩
  exact ⟨RingEquiv.ofBijective f ⟨hinj, hsurj⟩, fun a => rfl⟩

theorem card_quot (ρ : 𝒪[F] ≃+* ↥(OL K)) {π : 𝒪[F]} (hπ : Irreducible π) :
    Nat.card (↥(OL K) ⧸ Ideal.span {ρ π}) = Nat.card 𝓀[F] := by
  have e1 : (𝒪[F] ⧸ Ideal.span {π}) ≃ (↥(OL K) ⧸ Ideal.span {ρ π}) :=
    (Ideal.quotientEquiv (Ideal.span {π}) (Ideal.span {ρ π}) ρ
      (by rw [Ideal.map_span, Set.image_singleton]; simp)).toEquiv
  have e2 : 𝓀[F] ≃ (𝒪[F] ⧸ Ideal.span {π}) :=
    (Ideal.quotEquivOfEq hπ.maximalIdeal_eq).toEquiv
  exact Nat.card_congr (e2.trans e1).symm

theorem map_ltPoly (ρ : 𝒪[F] ≃+* ↥(OL K)) {π : 𝒪[F]} (hπ : Irreducible π) :
    PowerSeries.map (ρ : 𝒪[F] →+* ↥(OL K)) (ltPoly π : PowerSeries 𝒪[F]) = ltSeries (ρ π) := by
  rw [ltSeries, card_quot ρ hπ, ltPoly]
  simp

end Ring

theorem main : ∀ {l : ℕ} [Fact l.Prime] {K : FinExt l} {χ : ↥(GK K) →* (↥K.1)ˣ}, IsLTChar K χ →
    ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Algebra F (Om l)] [ValuativeExtension F (Om l)] [Algebra.IsAlgebraic F (Om l)],
    Set.range (algebraMap F (Om l)) = (K.1 : Set (Om l)) →
    ∃ (π : 𝒪[F]) (hπ : Irreducible π), ∀ (g : Om l ≃ₐ[F] Om l) (g' : ↥(GK K)), (∀ y, g y = (g' : GQ l) y) →
      ∃ u : 𝒪[F]ˣ, algebraMap F (Om l) ((u : 𝒪[F]) : F) = (((χ g' : (↥K.1)ˣ) : ↥K.1) : Om l) ∧
        ∀ n, ∀ x ∈ lubinTateTorsion (Om l) (hπ := hπ) (isLubinTateSeries_ltPoly π) n,
          lubinTateGalPointMap (hπ := hπ) (isLubinTateSeries_ltPoly π) g x = (u : 𝒪[F]) • x := by
  intro l _ K χ hχ F _ _ _ _ _ _ _ hR
  obtain ⟨πK, z, hπK, h0, h1, hs, hch⟩ := hχ
  obtain ⟨ρ, hρ⟩ := exists_ringEquiv (K := K) (F := F) hR
  have hρπ : ρ (ρ.symm πK) = πK := ρ.apply_symm_apply πK
  obtain ⟨π, hπdef⟩ : ∃ π : 𝒪[F], π = ρ.symm πK := ⟨_, rfl⟩
  rw [← hπdef] at hρπ
  have hπ : Irreducible π := hπdef ▸ (MulEquiv.irreducible_iff ρ.symm).mpr hπK
  have hf := isLubinTateSeries_ltPoly π
  have hcard : Nat.card (↥(OL K) ⧸ Ideal.span {πK}) = Nat.card 𝓀[F] := by
    have h := card_quot ρ hπ
    rwa [hρπ] at h
  have hcoe : ((πK : ↥K.1) : Om l) = algebraMap F (Om l) (π : F) := by
    rw [← hρ π, hρπ]
  have hs' : ∀ n, algebraMap F (Om l) (π : F) * z (n + 1) + z (n + 1) ^ Nat.card 𝓀[F] = z n :=
    fun n => by
      rw [← hcoe, ← hcard, add_comm]
      exact hs n
  have hv : ∀ n, valuation (Om l) (z n) < 1 := by
    intro n
    induction n with
    | zero => simp [h0]
    | succ n ih => exact CharEx.valuation_lt_one_of_eq hπ ih (hs' n)
  let Z : ℕ → IdealPoint (Om l) (lubinTateFormalGroup hπ hf) := fun n => IdealPoint.mk (z n) (hv n)
  have heval : ∀ (a : 𝒪[F]) (h : ↥(GK K)),
      (((ρ a : ↥(OL K)) : ↥K.1)) = ((χ h : (↥K.1)ˣ) : ↥K.1) →
      ∀ n, (a • Z n).val = (h : GQ l) (z n) := by
    intro a h ha n
    let Φ : PowerSeries 𝒪[F] := (lubinTateHom hπ hf hf a).toPowerSeries
    let ψ : PowerSeries ↥(OL K) := PowerSeries.map (ρ : 𝒪[F] →+* ↥(OL K)) Φ
    have hΦ0 : PowerSeries.constantCoeff Φ = 0 := (lubinTateHom hπ hf hf a).constantCoeff_eq_zero'
    have hψ0 : PowerSeries.constantCoeff ψ = 0 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, hΦ0, map_zero]
    have hψ1 : ((PowerSeries.coeff 1 ψ : ↥(OL K)) : ↥K.1) = ((χ h : (↥K.1)ˣ) : ↥K.1) := by
      rw [PowerSeries.coeff_map, coeff_one_lubinTateHom]
      exact ha
    have hF0 : PowerSeries.constantCoeff (ltPoly π : PowerSeries 𝒪[F]) = 0 :=
      hf.constantCoeff_eq_zero
    have hsub : PowerSeries.subst ψ (ltSeries πK) = PowerSeries.subst (ltSeries πK) ψ := by
      have h2 := congrArg (MvPowerSeries.map (ρ : 𝒪[F] →+* ↥(OL K)))
        (subst_lubinTateHom hπ hf hf a)
      rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hΦ0),
        PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hF0)] at h2
      change PowerSeries.subst ψ (PowerSeries.map (ρ : 𝒪[F] →+* ↥(OL K)) (ltPoly π : PowerSeries 𝒪[F])) =
        PowerSeries.subst (PowerSeries.map (ρ : 𝒪[F] →+* ↥(OL K)) (ltPoly π : PowerSeries 𝒪[F])) ψ at h2
      rwa [map_ltPoly ρ hπ, hρπ] at h2
    have hsum := hch h ψ hψ0 hψ1 hsub n
    have hsum2 := CharEx.hasSum_coeff_mul_pow (K := F) Φ (hv n)
    rw [lubinTate_smul_val]
    refine hsum2.unique ?_
    convert hsum using 2 with k
    simp only [ψ, PowerSeries.coeff_map]
    rw [← hρ]
    rfl
  have hZ0 : Z 0 = 0 := IdealPoint.ext h0
  have hZ1 : Z 1 ≠ 0 := fun h => h1 (congrArg IdealPoint.val h)
  have hstep : ∀ n, π • Z (n + 1) = Z n := fun n => IdealPoint.ext (by
    rw [lubinTate_uniformizer_smul_val]
    change psEval ((ltPoly π : Polynomial 𝒪[F]) : PowerSeries 𝒪[F]) (fun _ => z (n + 1)) = z n
    rw [psEval_polynomial, aeval_ltPoly]
    exact hs' n)
  have hpow : ∀ n, π ^ n • Z (n + 1) = Z 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, mul_smul, hstep, ih]
  have hunit : ∀ (a : 𝒪[F]) (h : ↥(GK K)),
      (((ρ a : ↥(OL K)) : ↥K.1)) = ((χ h : (↥K.1)ˣ) : ↥K.1) → IsUnit a := by
    intro a h ha
    by_contra hnu
    have hm := (IsLocalRing.mem_maximalIdeal a).mpr hnu
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hm
    obtain ⟨b, rfl⟩ := hm
    have h2 : (b * π) • Z 1 = 0 := by rw [mul_smul, hstep, hZ0, smul_zero]
    have h3 := heval _ h ha 1
    rw [h2] at h3
    exact h1 ((map_eq_zero_iff _ (h : GQ l).injective).mp h3.symm)
  refine ⟨π, hπ, fun g g' hg => ?_⟩
  obtain ⟨u, hu⟩ : ∃ u : 𝒪[F]ˣ,
      algebraMap F (Om l) ((u : 𝒪[F]) : F) = (((χ g' : (↥K.1)ˣ) : ↥K.1) : Om l) := by
    have hy : (((χ g' : (↥K.1)ˣ) : ↥K.1) : Om l) ∈ (K.1 : Set (Om l)) :=
      ((χ g' : (↥K.1)ˣ) : ↥K.1).2
    rw [← hR] at hy
    obtain ⟨y, hy⟩ := hy
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [map_zero] at hy
      exact (χ g').ne_zero (Subtype.ext hy.symm)
    rcases le_total (valuation F y) 1 with hle | hle
    · obtain ⟨w, hw⟩ := hunit ⟨y, hle⟩ g' (Subtype.ext (by rw [hρ]; exact hy))
      exact ⟨w, by rw [hw]; exact hy⟩
    · have hle' : valuation F y⁻¹ ≤ 1 := by
        rw [map_inv₀]
        exact inv_le_one_of_one_le₀ hle
      have hinv : (((χ (g'⁻¹) : (↥K.1)ˣ) : ↥K.1) : Om l) = algebraMap F (Om l) y⁻¹ := by
        rw [map_inv, map_inv₀, hy, Units.val_inv_eq_inv_val, IntermediateField.coe_inv]
      obtain ⟨w, hw⟩ := hunit ⟨y⁻¹, hle'⟩ g'⁻¹ (Subtype.ext (by rw [hρ, hinv]))
      refine ⟨w⁻¹, ?_⟩
      have hw2 : ((w : 𝒪[F]) : F) = y⁻¹ := by rw [hw]
      have hw3 : (((w⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) : F) * ((w : 𝒪[F]) : F) = 1 := by
        have h5 : ((w⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) * (w : 𝒪[F]) = 1 := Units.inv_mul w
        exact congrArg Subtype.val h5
      rw [hw2] at hw3
      rw [← hy, (eq_of_mul_inv_eq_one hw3)]
  refine ⟨u, hu, fun n x hx => ?_⟩
  have hgZ : lubinTateGalPointMap (hπ := hπ) hf g (Z (n + 1)) = (u : 𝒪[F]) • Z (n + 1) :=
    IdealPoint.ext (by
      rw [lubinTateGalPointMap_val, heval (u : 𝒪[F]) g' (Subtype.ext (by rw [hρ]; exact hu))]
      exact hg _)
  have hZt : Z (n + 1) ∈ lubinTateTorsion (Om l) (hπ := hπ) hf (n + 1) :=
    CharEx.mem_torsion hπ h0 hs' (n + 1) _ rfl
  have hZn : Z (n + 1) ∉ lubinTateTorsion (Om l) (hπ := hπ) hf (n + 1 - 1) := by
    rw [Nat.add_sub_cancel, mem_lubinTateTorsion, hpow]
    exact hZ1
  obtain ⟨-, hgen⟩ := primitive_spec hπ hf hZt hZn
  obtain ⟨a, rfl⟩ := hgen x (lubinTateTorsion_mono hπ hf n.le_succ hx)
  rw [map_smul, hgZ, smul_smul, smul_smul, mul_comm]

end GlobalTheory.CompanionTheory.LTHodge.UnitAct
end
end

section

noncomputable section

open MeasureTheory Matrix Topology Filter
open scoped ContDiff ENNReal ComplexOrder Pointwise

open PositivityTheory.RgTw (Mat G hb)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.ConeHaar

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ConeHaar.Fin

variable {n : ℕ}

theorem continuous_hOf : Continuous (hOf (n := n)) := by
  unfold hOf
  refine continuous_finsetSum _ fun p _ => ?_
  exact (Complex.continuous_ofReal.comp (continuous_apply p)).smul continuous_const

theorem continuous_detRe : Continuous fun v : Fin n × Fin n → ℝ => (hOf v).det.re :=
  Complex.continuous_re.comp (continuous_hOf.matrix_det)

theorem detRe_pos {v : Fin n × Fin n → ℝ} (hv : v ∈ cone n) : 0 < (hOf v).det.re := by
  have h : 0 < (hOf v).det := Matrix.PosDef.det_pos hv
  exact (Complex.pos_iff.1 h).1

theorem measurable_coneW : Measurable (coneW n) := by
  unfold coneW
  exact ENNReal.measurable_ofReal.comp ((continuous_detRe.measurable.pow_const n).inv)

theorem exists_hOf_eq_one : ∃ v : Fin n × Fin n → ℝ, hOf v = 1 := by
  refine ⟨fun p => ((1 * hb p : Mat n).trace).re, ?_⟩
  have hre : ∀ p : Fin n × Fin n, ((((1 * hb p : Mat n).trace).re : ℝ) : ℂ) = (1 * hb p : Mat n).trace := by
    intro p
    apply Complex.conj_eq_iff_re.1
    have h1 : star (hb p : Mat n).trace = (hb p : Mat n).trace := by
      rw [← Matrix.trace_conjTranspose, GlobalTheory.CompanionTheory.TwistHomotopy.hb_conjTranspose]
    simpa using h1
  have h := (GlobalTheory.CompanionTheory.TopClass.hbB n).sum_repr (1 : Mat n)
  simp only [GlobalTheory.CompanionTheory.TopClass.hbB_repr, GlobalTheory.CompanionTheory.TopClass.hbB_apply] at h
  conv_rhs => rw [← h]
  simp only [hOf, hre]

theorem cone_nonempty : (cone n).Nonempty := by
  obtain ⟨v, hv⟩ := exists_hOf_eq_one (n := n)
  refine ⟨v, ?_⟩
  show (hOf v).PosDef
  rw [hv]
  exact Matrix.PosDef.one

theorem coneW_pos {v : Fin n × Fin n → ℝ} (hv : v ∈ cone n) : coneW n v ≠ 0 := by
  unfold coneW
  have : 0 < ((hOf v).det.re ^ n)⁻¹ := inv_pos.2 (pow_pos (detRe_pos hv) n)
  exact (ENNReal.ofReal_pos.2 this).ne'

theorem coneMeas_ne_zero : coneMeas n ≠ 0 := by
  intro h0
  have hz := (withDensity_eq_zero measurable_coneW.aemeasurable h0)
  have hopen : IsOpen (cone n) := GlobalTheory.T.positive_cone_isOpen n
  have hvol : 0 < volume (cone n) := hopen.measure_pos volume cone_nonempty
  rw [Filter.EventuallyEq, ae_restrict_iff' hopen.measurableSet] at hz
  have hnull : volume (cone n) = 0 := by
    refine measure_mono_null (t := {v | ¬ (v ∈ cone n → coneW n v = (0 : (Fin n × Fin n → ℝ) → ℝ≥0∞) v)}) ?_ hz
    intro v hv
    simpa using ⟨hv, coneW_pos hv⟩
  exact hvol.ne' hnull

theorem coneMeas_lt_top (C : Set (Fin n × Fin n → ℝ)) (hC : IsCompact C) (hCc : C ⊆ cone n) :
    coneMeas n C < ⊤ := by
  have hcont : ContinuousOn (fun v : Fin n × Fin n → ℝ => ((hOf v).det.re ^ n)⁻¹) C :=
    ContinuousOn.inv₀ (continuous_detRe.pow n).continuousOn
      fun v hv => (pow_pos (detRe_pos (hCc hv)) n).ne'
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hcont
  have hle : ∀ v ∈ C, coneW n v ≤ ENNReal.ofReal M := fun v hv =>
    ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hM v hv))
  unfold coneMeas
  rw [withDensity_apply _ hC.measurableSet]
  calc ∫⁻ v in C, coneW n v ∂(volume.restrict (cone n))
      ≤ ∫⁻ _ in C, ENNReal.ofReal M ∂(volume.restrict (cone n)) :=
        setLIntegral_mono' hC.measurableSet hle
    _ = ENNReal.ofReal M * (volume.restrict (cone n)) C := by simp
    _ ≤ ENNReal.ofReal M * volume C := by
        gcongr
        exact Measure.restrict_le_self
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC.measure_lt_top

theorem coneMeas_ne_zero_and_lt_top : ∀ n : ℕ, coneMeas n ≠ 0 ∧ ∀ C : Set (Fin n × Fin n → ℝ), IsCompact C →
    C ⊆ PositivityTheory.RgBcC.cone n → coneMeas n C < ⊤ :=
  fun _ => ⟨coneMeas_ne_zero, coneMeas_lt_top⟩

end GlobalTheory.CompanionTheory.ConeHaar.Fin
end
end

section

noncomputable section

open Filter Topology
open scoped ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc

def phaseRoot (z : ℂ) : ℂ := z / ((Real.sqrt ‖z‖ : ℝ) : ℂ)

theorem norm_phaseRoot (z : ℂ) : ‖phaseRoot z‖ = Real.sqrt ‖z‖ := by
  unfold phaseRoot
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.div_sqrt

theorem continuous_phaseRoot : Continuous phaseRoot := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z = 0
  · subst hz
    have h0 : phaseRoot 0 = 0 := by simp [phaseRoot]
    unfold ContinuousAt
    rw [h0, tendsto_zero_iff_norm_tendsto_zero]
    simp only [norm_phaseRoot]
    have : Continuous fun w : ℂ => Real.sqrt ‖w‖ := by fun_prop
    simpa using this.tendsto 0
  · have hne : ((Real.sqrt ‖z‖ : ℝ) : ℂ) ≠ 0 := by
      have : 0 < Real.sqrt ‖z‖ := Real.sqrt_pos.mpr (norm_pos_iff.mpr hz)
      exact_mod_cast this.ne'
    have hc : Continuous fun w : ℂ => ((Real.sqrt ‖w‖ : ℝ) : ℂ) := by fun_prop
    exact continuousAt_id.div hc.continuousAt hne

theorem tendsto_pow_mul_of_norm_sqrt {h : C₀(ℝ, ℂ)} (hr : Rapid h) {k : ℝ → ℂ}
    (hn : ∀ y, ‖k y‖ = Real.sqrt ‖h y‖) (m : ℕ) :
    Tendsto (fun y : ℝ => (y : ℂ) ^ m * k y) (cocompact ℝ) (𝓝 0) := by
  obtain ⟨h', hh'⟩ := hr (2 * m)
  have h0 : Tendsto (fun y => ‖h' y‖) (cocompact ℝ) (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mp (h'.zero_at_infty')
  have h1 : Tendsto (fun y => Real.sqrt ‖h' y‖) (cocompact ℝ) (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp h0
    rw [Real.sqrt_zero] at this
    exact this
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine h1.congr fun y => ?_
  rw [hh', norm_mul, norm_mul, hn, norm_pow, norm_pow, Complex.norm_real, pow_mul',
    Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

theorem exists_rapid_of_norm_sqrt {h : C₀(ℝ, ℂ)} (hr : Rapid h) {k : ℝ → ℂ} (hc : Continuous k)
    (hn : ∀ y, ‖k y‖ = Real.sqrt ‖h y‖) : ∃ k' : C₀(ℝ, ℂ), (∀ y, k' y = k y) ∧ Rapid k' := by
  have key : ∀ m : ℕ, ∃ g : C₀(ℝ, ℂ), ∀ y, g y = (y : ℂ) ^ m * k y := fun m =>
    ⟨⟨⟨fun y => (y : ℂ) ^ m * k y, by fun_prop⟩, tendsto_pow_mul_of_norm_sqrt hr hn m⟩,
      fun _ => rfl⟩
  obtain ⟨k', hk'⟩ := key 0
  have hk : ∀ y, k' y = k y := fun y => by simp [hk']
  refine ⟨k', hk, fun m => ?_⟩
  obtain ⟨g, hg⟩ := key m
  exact ⟨g, fun y => by rw [hg, hk]⟩

theorem factorRapid : FactorRapid := by
  intro h hr
  obtain ⟨h₁, e₁, r₁⟩ := exists_rapid_of_norm_sqrt hr (k := fun y => phaseRoot (h y))
    (continuous_phaseRoot.comp h.continuous) (fun y => norm_phaseRoot _)
  obtain ⟨h₂, e₂, r₂⟩ := exists_rapid_of_norm_sqrt hr (k := fun y => ((Real.sqrt ‖h y‖ : ℝ) : ℂ))
    (by have := h.continuous; fun_prop)
    (fun y => by rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)])
  have hs : star h₂ = h₂ := by
    ext y
    rw [ZeroAtInftyContinuousMap.star_apply, e₂]
    simp
  refine ⟨h₁, h₂, r₁, r₂, by rwa [hs], ?_⟩
  ext y
  rw [ZeroAtInftyContinuousMap.mul_apply, e₁, e₂]
  by_cases hy : h y = 0
  · simp [hy, phaseRoot]
  · have hne : ((Real.sqrt ‖h y‖ : ℝ) : ℂ) ≠ 0 := by
      have : 0 < Real.sqrt ‖h y‖ := Real.sqrt_pos.mpr (norm_pos_iff.mpr hy)
      exact_mod_cast this.ne'
    simp only [phaseRoot]
    field_simp

end GlobalTheory.CompanionTheory.KerFc
end
end

module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle133
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardInversePrimeRepsIntegralRightMulHecke
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle207
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle213
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle146
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle193
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle141
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexMatrixLattice
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle017
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle112
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle099
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle120
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle118
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalToGlobal.UnitaryNorms.CharShare
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle402
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivOfNotLinearIndependent
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle029
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValSqNonsplit
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle142

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.L2.NTheta (IsIdemAt IsHeckeElt)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitDetValue

open GlobalTheory.SplitHecke

section Local

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem valued_unit (u : (v.adicCompletionIntegers F)ˣ) :
    Valued.v (algebraMap (v.adicCompletionIntegers F) (Fv F v) u) = 1 := by
  by_contra hne
  exact (GlobalTheory.SplitUnif.mem_max v u).2 (lt_of_le_of_ne (u : v.adicCompletionIntegers F).2 hne) u.isUnit

theorem valued_irreducible {p : v.adicCompletionIntegers F} (hp : Irreducible p) :
    Valued.v (algebraMap (v.adicCompletionIntegers F) (Fv F v) p) = WithZero.exp (-1) := by
  obtain ⟨t, ht⟩ := v.intValuation_exists_uniformizer
  have hφ : ∀ s : 𝓞 F, Valued.v (algebraMap F (Fv F v) s) = v.intValuation s := fun s =>
    (v.valuedAdicCompletion_eq_valuation' _).trans (HeightOneSpectrum.valuation_of_algebraMap v s)
  let p₀ : v.adicCompletionIntegers F := ⟨algebraMap F (Fv F v) t, GlobalTheory.SplitUnif.map_mem v _ t⟩
  have hp₀ : Valued.v (p₀ : Fv F v) = WithZero.exp (-1) := (hφ t).trans ht
  obtain ⟨w, hw⟩ := IsDiscreteValuationRing.associated_of_irreducible _ hp
    (GlobalTheory.SplitUnif.irreducible_of_valued v p₀ hp₀)
  have := congrArg (fun y : v.adicCompletionIntegers F => Valued.v (y : Fv F v)) hw
  change Valued.v ((p : Fv F v) * (w : v.adicCompletionIntegers F)) = Valued.v (p₀ : Fv F v) at this
  rw [map_mul, hp₀] at this
  have hw1 := valued_unit v w
  rw [← this]
  change _ = _ * Valued.v (algebraMap (v.adicCompletionIntegers F) (Fv F v) w)
  rw [hw1, mul_one]
  rfl

theorem card_residue_eq :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) = Ideal.absNorm v.asIdeal := by
  have hφ : ∀ s : 𝓞 F, Valued.v (algebraMap F (Fv F v) s) = v.intValuation s := fun s =>
    (v.valuedAdicCompletion_eq_valuation' _).trans (HeightOneSpectrum.valuation_of_algebraMap v s)
  exact GlobalTheory.SplitUnif.card_residueField v (algebraMap F (Fv F v)) v (fun _ => rfl) fun s => by
    rw [hφ, HeightOneSpectrum.intValuation_lt_one_iff_mem]

end Local

section Chart

variable {D : D7} {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v}

theorem chi_of_unit_gen (hπ : Chart e v π) {x d : (AE D)ˣ} (hx1 : (1 - e) * (x : AE D) = 1 - e)
    (hd1 : (1 - e) * (d : AE D) = 1 - e) {A : Type} [CommGroup A] {χ : (AE D)ˣ →* A}
    (hχ : ∀ y : (AE D)ˣ, (1 - e) * (y : AE D) = 1 - e → finPart D (e * (y : AE D)) ∈ intAE D →
      finPart D (e * ((y⁻¹ : (AE D)ˣ) : AE D)) ∈ intAE D → χ y = 1) {u : (Ov D v)ˣ}
    (h1 : π (d : AE D) = π (x : AE D) * algebraMap (Ov D v) (Fv D.host.F v) u) : χ d = χ x := by
  have h3 : π ((x⁻¹ * d : (AE D)ˣ) : AE D) = algebraMap (Ov D v) (Fv D.host.F v) u := by
    rw [Units.val_mul, π.map_mul, h1, ← mul_assoc, ← π.map_mul, Units.inv_mul, π.map_one, one_mul]
  have h4 := hχ (x⁻¹ * d) ?_ ((hπ.2.2.2 _).2 ⟨u, h3.symm⟩) ((hπ.2.2.2 _).2 ⟨(u⁻¹ : (Ov D v)ˣ), ?_⟩)
  · rwa [χ.map_mul, χ.map_inv, inv_mul_eq_one, eq_comm] at h4
  · have h5 : (1 - e) * ((x⁻¹ : (AE D)ˣ) : AE D) = 1 - e := by
      conv_lhs => rw [← hx1, mul_assoc, Units.mul_inv, mul_one]
    rw [Units.val_mul, ← mul_assoc, h5, hd1]
  · rw [map_units_inv, map_units_inv, h3]

end Chart



theorem det_modulus_chi : ∀ (D : D7) (V : HSp D) (P : Pl D.host.E) (e : AE D), IsIdemAt e P → ∀ ϖ : 𝓞 D.host.E, ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ∀ x : (AE D)ˣ, (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e) → ∀ (k : ℕ) (α : GA D V), IsHeckeElt V e (ϖ : D.host.E) k α → ∀ k₁ ∈ Mult.locPart V (KsphC V ∅) e, ∀ k₂ ∈ Mult.locPart V (KsphC V ∅) e, ∀ z : (AE D)ˣ, IsDetAt e V (k₁ * α * k₂) z → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D z = (((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ k)⁻¹ ∧ ∀ (A : Type) [CommGroup A] (χ : (AE D)ˣ →* A), (∀ y : (AE D)ˣ, (1 - e) * (y : AE D) = 1 - e → finPart D (e * (y : AE D)) ∈ intAE D → finPart D (e * ((y⁻¹ : (AE D)ˣ) : AE D)) ∈ intAE D → χ y = 1) → χ z = χ x ^ k := by
  intro D V P e hP ϖ hϖ hϖ2 x hx k α hα k₁ hk₁ k₂ hk₂ z hz
  have he := hP.1
  obtain ⟨v, π, hπ⟩ := GlobalTheory.T.exists_place_chart_of_splitIdempotent e he
  obtain ⟨⟨p, hpϖ, hp⟩, hq⟩ := GlobalTheory.T.splitChart_uniformiser_and_residueCard e P v π hP hπ ϖ hϖ hϖ2
  obtain ⟨β, hβ⟩ := GlobalTheory.T.exists_splitFrame_selfDualLattice_completion e v π he hπ V
  have st := GlobalTheory.T.mem_hyperspecial_iff_gInt_of_suppAt_split e v π he hπ V β hβ
  have hH : Hk (Ov D v) p k (rho V π β (k₁ * α * k₂)) := by
    rw [map_mul, map_mul]
    exact (GlobalTheory.T.heckeElement_component_mem_standardDoubleCoset e v π he hπ V β hβ (ϖ : D.host.E) p k α hpϖ hα).mul ((st _ hk₁.2).1 hk₁.1)
      ((st _ hk₂.2).1 hk₂.1)
  obtain ⟨u, hu⟩ := hH.2.2
  have hx1 : (1 - e) * (x : AE D) = 1 - e := by
    rw [hx]
    exact one_sub_mul_idem he.1 _
  have hx2 : π x = algebraMap (Ov D v) (Fv D.host.F v) p := by
    rw [hx, map_add π, π.map_mul, π.map_sub, π.map_one, hπ.map_e he.1, one_mul, sub_self, add_zero, hpϖ]
  have hz1 : (1 - e) * (z : AE D) = 1 - e := by
    rw [hz]
    exact one_sub_mul_idem he.1 _
  have hz2 : π (z : AE D) = algebraMap (Ov D v) (Fv D.host.F v) (p ^ k * u) := by
    rw [rho_val, Matrix.det_mul_comm, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mul] at hu
    rw [hz, map_add π, π.map_mul, π.map_sub, π.map_one, hπ.map_e he.1, one_mul, sub_self, add_zero]
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
    exact hu
  refine ⟨?_, fun A _ χ hχ => ?_⟩
  · rw [GlobalTheory.SplitLinear.absFin_split D e v π he hπ z hz1, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV]
    have e1 : ((Units.map π.toMonoidHom z : (Fv D.host.F v)ˣ) : Fv D.host.F v) = π (z : AE D) := rfl
    have e2 : Ideal.absNorm v.asIdeal = Ideal.absNorm P.asIdeal := by
      rw [← card_residue_eq, hq]
    have hv1 : Valued.v (algebraMap (Ov D v) (Fv D.host.F v) p) = WithZero.exp (-1) := valued_irreducible v hp
    have hv2 : Valued.v (algebraMap (Ov D v) (Fv D.host.F v) u) = 1 := valued_unit v u
    rw [e1, hz2, map_mul, map_mul, map_pow, map_pow, hv1, hv2, mul_one, e2,
      ← WithZero.exp_nsmul, WithZero.log_exp, nsmul_eq_mul, mul_neg_one, _root_.zpow_neg, zpow_natCast]
  · have h1 : π (z : AE D) = π ((x ^ k : (AE D)ˣ) : AE D) * algebraMap (Ov D v) (Fv D.host.F v) u := by
      rw [hz2, Units.val_pow_eq_pow_val, π.map_pow, hx2, ← RingHom.map_pow, ← RingHom.map_mul]
    have h2 : ∀ j : ℕ, (1 - e) * ((x ^ j : (AE D)ˣ) : AE D) = 1 - e := fun j => by
      induction j with
      | zero => rw [pow_zero, Units.val_one, mul_one]
      | succ j ih => rw [pow_succ, Units.val_mul, ← mul_assoc, ih, hx1]
    exact (chi_of_unit_gen hπ (h2 k) hz1 hχ h1).trans (χ.map_pow x k)

end GlobalTheory.SplitDetValue
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TameGenRep

open Formalism.L2.NT

theorem exists_zmod_eq {g : ℕ} [Fact g.Prime] (z : Formalism.CyclotomicNorms.Fbar g) (hz : z ^ g = z) :
    ∃ c : ZMod g, algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) c = z := by
  first
  | exact @_root_.GlobalTheory.RangeOfPowerFixed.main
  | exact _root_.GlobalTheory.RangeOfPowerFixed.main
  | (apply _root_.GlobalTheory.RangeOfPowerFixed.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.RangeOfPowerFixed.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RangeOfPowerFixed.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RangeOfPowerFixed.main ..)

theorem exists_rep : ∀ (D : D7), GrpSide D → ∀ (k : Fin 2) (v : D.nd.PlG k), normV (D.naut.plGw k v) = D.host.g k ∧ ∃ (u ϖ : 𝓞 D.host.E) (π : D.nd.Om), u ∉ (D.naut.plGw k v).asIdeal ∧ ϖ ∈ (D.naut.plGw k v).asIdeal ∧ ϖ ∉ (D.naut.plGw k v).asIdeal ^ 2 ∧ π ^ (normV (D.naut.plGw k v) - 1) = algebraMap D.host.E D.nd.Om (ϖ : D.host.E) ∧ (D.nd.plOm.1 (D.naut.plGw k v)).valuation (D.ntypes.tg k v π / π - algebraMap D.host.E D.nd.Om (u : D.host.E)) < 1 ∧ orderOf (D.ntypes.tg k v π / π) = normV (D.naut.plGw k v) - 1 := by
  intro D hG k v
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  haveI : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  haveI : CharZero D.nd.Om := charZero_of_injective_ringHom (f := algebraMap D.host.E D.nd.Om) (algebraMap D.host.E D.nd.Om).injective
  have hgp : (D.host.g k).Prime := D.host.g_prime k
  have hAP : IsPlaceOver (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)) (D.naut.plGw k v) :=
    D.nd.plOm.2 (D.naut.plGw k v)
  have hgP : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := D.naut.plGw_over k v
  have hspl := GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) hgp (D.nd.g_split k) (D.naut.plGw k v) hgP
  have hN : normV (D.naut.plGw k v) = D.host.g k := by
    rw [← hspl.1, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  have hg1 : 0 < D.host.g k - 1 := by have := hgp.two_le; omega
  have hgΩ : ((D.host.g k : ℕ) : D.nd.Om) ≠ 0 := Nat.cast_ne_zero.mpr hgp.ne_zero
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq ((D.host.g k : ℕ) : D.nd.Om) hg1
  have hT : redThrough (D.nd.plOm.1 (D.naut.plGw k v)) (hG.kv k v) (D.ntypes.tg k v π / π) = hG.ζ k 1 :=
    hG.tg_tame k v 1 one_pos π (by rw [pow_one]; exact hπ)
  have hq : D.ntypes.tg k v π / π ∈ D.nd.plOm.1 (D.naut.plGw k v) :=
    tameQuot_mem (D.nd.plOm.1 (D.naut.plGw k v)) (D.ntypes.tg k v) hg1 hgΩ hπ
  have hpow : (D.ntypes.tg k v π / π) ^ (D.host.g k - 1) = 1 := tameQuot_pow (D.ntypes.tg k v) hgΩ hπ
  have hζ := (hG.ζ_gen k 1 one_pos).1
  rw [pow_one] at hζ
  have hζ1 : hG.ζ k 1 ^ (D.host.g k - 1) = 1 := by rw [← hζ]; exact pow_orderOf_eq_one _
  have hζpow : hG.ζ k 1 ^ D.host.g k = hG.ζ k 1 := by
    calc _ = hG.ζ k 1 ^ (D.host.g k - 1) * hG.ζ k 1 := by rw [← pow_succ, Nat.sub_add_cancel hgp.one_le]
      _ = _ := by rw [hζ1, one_mul]
  have hζ0 : hG.ζ k 1 ≠ 0 := by
    intro h
    rw [h, zero_pow hg1.ne'] at hζ1
    exact zero_ne_one hζ1
  obtain ⟨c, hc⟩ := exists_zmod_eq _ hζpow
  have hca : ((c.val : ℕ) : Formalism.CyclotomicNorms.Fbar (D.host.g k)) = hG.ζ k 1 := by
    rw [← hc, ← map_natCast (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k))), ZMod.natCast_zmod_val]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = c.val := ⟨_, rfl⟩
  rw [← hn] at hca
  have hcast : algebraMap D.host.E D.nd.Om ((n : 𝓞 D.host.E) : D.host.E) = (n : D.nd.Om) := by
    simp
  have haA : (n : D.nd.Om) ∈ D.nd.plOm.1 (D.naut.plGw k v) := natCast_mem _ _
  have hra : redThrough (D.nd.plOm.1 (D.naut.plGw k v)) (hG.kv k v) (n : D.nd.Om) =
      hG.kv k v (IsLocalRing.residue _ ⟨_, haA⟩) := by
    unfold redThrough; rw [dite_eq_left haA]
  have hra' : hG.kv k v (IsLocalRing.residue _ ⟨_, haA⟩) = hG.ζ k 1 := by
    have : (⟨(n : D.nd.Om), haA⟩ : D.nd.plOm.1 (D.naut.plGw k v)) = (n : D.nd.plOm.1 (D.naut.plGw k v)) :=
      Subtype.ext (by simp)
    rw [this, map_natCast, map_natCast, hca]
  have hrq : redThrough (D.nd.plOm.1 (D.naut.plGw k v)) (hG.kv k v) (D.ntypes.tg k v π / π) =
      hG.kv k v (IsLocalRing.residue _ ⟨_, hq⟩) := by
    unfold redThrough; rw [dite_eq_left hq]
  have hval : (D.nd.plOm.1 (D.naut.plGw k v)).valuation (D.ntypes.tg k v π / π - (n : D.nd.Om)) < 1 := by
    have h1 := (hG.kv k v).injective (((hrq.symm.trans hT).trans hra'.symm))
    have h2 := Ideal.Quotient.eq.1 h1
    have h3 := ((D.nd.plOm.1 (D.naut.plGw k v)).valuation_lt_one_iff _).1 h2
    exact h3
  have hu : (n : 𝓞 D.host.E) ∉ (D.naut.plGw k v).asIdeal := by
    intro h
    have h1 := (hAP _).2 h
    have h2 : (n : D.nd.Om) ∈ D.nd.plOm.1 (D.naut.plGw k v) := haA
    have h3 : (⟨_, haA⟩ : D.nd.plOm.1 (D.naut.plGw k v)) ∈ IsLocalRing.maximalIdeal _ :=
      ((D.nd.plOm.1 (D.naut.plGw k v)).valuation_lt_one_iff _).2 (by rw [hcast] at h1; exact h1)
    rw [← IsLocalRing.residue_eq_zero_iff] at h3
    rw [h3, map_zero] at hra'
    exact hζ0 hra'.symm
  have hord : orderOf (D.ntypes.tg k v π / π) = D.host.g k - 1 := by
    apply Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hpow)
    rw [← hζ]
    apply orderOf_dvd_of_pow_eq_one
    have h1 : (⟨_, hq⟩ : D.nd.plOm.1 (D.naut.plGw k v)) ^ orderOf (D.ntypes.tg k v π / π) = 1 :=
      Subtype.ext (by simp [pow_orderOf_eq_one])
    rw [← hT, hrq, ← map_pow, ← map_pow, h1, map_one, map_one]
  refine ⟨hN, (n : 𝓞 D.host.E), ((D.host.g k : ℕ) : 𝓞 D.host.E), π, hu, hgP, hspl.2.1, ?_, ?_, ?_⟩
  · rw [hN]; simpa using hπ
  · rw [hcast]; exact hval
  · rw [hN]; exact hord

end GlobalTheory.TameGenRep

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Neutral.B1 GlobalTheory.HeckeGal GlobalTheory.GalChar

noncomputable section

namespace GlobalTheory.DeltaGal

theorem continuous_comp_of_isOpen_ker {Gp M Y : Type*} [Group Gp] [TopologicalSpace Gp] [IsTopologicalGroup Gp]
    [Group M] [TopologicalSpace Y] (f : Gp →* M) (h : IsOpen (f.ker : Set Gp)) (u : M → Y) :
    Continuous (fun g => u (f g)) := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  have hm : (fun x => g⁻¹ * x) ⁻¹' (f.ker : Set Gp) ∈ nhds g :=
    ((continuous_const.mul continuous_id).isOpen_preimage _ h).mem_nhds (by simp)
  refine (continuousAt_const (y := u (f g))).congr ?_
  filter_upwards [hm] with x hx
  simp only [Set.mem_preimage, SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv] at hx
  rw [inv_mul_eq_one.1 hx]

theorem delta_isGal : GlobalTheory.Published.ChebotarevDegreeOne → ∀ {D : D7} {cf : CharFrame D} {b0 b1 : Big D} {Sx : Finset (PlE D.host)} {T : TwR D.LL0 D.nd} (Sp : RingSpec D cf b0 b1 Sx T) {art : Ideles D.host.E →* Gab D.host.E D.nd.Om}, IsGlobalArtin art → ∀ (i : T.Tw) (κ : FractionRing (T.O0 i) →+* Qbar (T.l i)) (ι : Qbar (T.l i) ≃+* ℂ), (∀ x : D.LL0, ι (κ (T.emb0 i x)) = D.what₂.embLL (x : D.what₂.LL)) → IsGal art κ ι (cf.delAt (T.l i)) 0 (T.delta i) := by
  intro _ D cf b0 b1 Sx T Sp art hart i κ ι hι
  set χ := cf.delAt (T.l i) with hχ
  have hfin : ∃ n, 0 < n ∧ χ.OrderDvd n := by
    rw [hχ]; unfold CharFrame.delAt; split_ifs
    exacts [cf.isDel'.fin, cf.isDel.fin]
  obtain ⟨n, hn, hord⟩ := hfin
  have hpos : IsAlgPos χ 0 := fun k _ => by
    rw [HChar.inf_eq_one_of_order hn hord k]; simp
  refine ⟨hpos, continuous_comp_of_isOpen_ker (T.delta i) (T.delta_open i) (fun u => (u : T.O0 i)), ?_⟩
  obtain ⟨r', hr'c, hr'⟩ := hart.exists_isLAdicOf ι hpos
  suffices h : inQ κ (T.delta i) = r' by rw [h]; exact hr'
  have hc : Continuous (inQ κ (T.delta i)) :=
    continuous_comp_of_isOpen_ker (T.delta i) (T.delta_open i) (Units.map (toQ κ : T.O0 i →* Qbar (T.l i)))
  have h0 : Ideal.span {((T.l i : ℕ) : 𝓞 D.host.E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (T.lPrime i).out.ne_zero
  have hl : ∀ᶠ v : HeightOneSpectrum (𝓞 D.host.E) in Filter.cofinite, ((T.l i : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal :=
    (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)
  have hS := Filter.eventually_cofinite.1 (hl.and (GlobalTheory.Mem.UnrAe.unr_ae_and_level _ χ).1)
  refine mul_inv_eq_one.1 (GlobalTheory.FrobDense.eq_one_of_frob _ _ art hart _ (inQ κ (T.delta i) * r'⁻¹)
    (hc.mul hr'c.inv) hS.toFinset fun v hv A hA σ hσ => ?_)
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hv
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_eq_one]
  apply Units.ext
  rw [hr'.frob_unr hart (Or.inr rfl) hv.2 hA hσ]
  obtain ⟨x, hx1, hx2⟩ := Sp.deltaRead i v hv.1 hv.2 A σ hA hσ
  show κ (algebraMap _ _ ((T.delta i σ : T.O0 i))) = _
  rw [hx2]
  apply ι.injective
  rw [hι, hx1, map_inv₀, RingEquiv.apply_symm_apply, Units.val_inv_eq_inv_val]

end GlobalTheory.DeltaGal
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LamInstall
open ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2.NT

variable {D : D7} (hE : IsEmpty D.nd.Loc) {cf : CharFrame D} {b0 b1 : Big D} {Sx : Finset (PlE D.host)}
  {T : TwR D.LL0 D.nd} (Sp : RingSpec D cf b0 b1 Sx T) (F : TwF T)

abbrev recE (ex : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F (TwL.empty T)))
    (h0 : ∀ g : G0g D.nd, D.what₂.embLL ((ex.eLL0 g : ↥D.LL0) : D.what₂.LL) = D.ntypes.e0.coeff g)
    (th : NTh D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F (TwL.empty T)) ex) : TwNew D :=
  ⟨T.ntw hE F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩

abbrev recL (L : TwL T) (ex : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F (TwL.empty T)))
    (h0 : ∀ g : G0g D.nd, D.what₂.embLL ((ex.eLL0 g : ↥D.LL0) : D.what₂.LL) = D.ntypes.e0.coeff g)
    (th' : NTh D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L) ({ ex with } : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L))) :
    TwNew D :=
  ⟨T.ntw hE F L, ({ ex with } : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L)), h0, th', Sp.br, Sp.br_ind⟩

variable {hE Sp F} {L : TwL T} {ex : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F (TwL.empty T))}
  {h0 : ∀ g : G0g D.nd, D.what₂.embLL ((ex.eLL0 g : ↥D.LL0) : D.what₂.LL) = D.ntypes.e0.coeff g}
  {th : NTh D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F (TwL.empty T)) ex}
  {th' : NTh D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L) ({ ex with } : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L))}



def twFC (X : TwFrameC (recE hE Sp F ex h0 th).toD7) : TwFrameC (recL hE Sp F L ex h0 th').toD7 := { X with }



def expC (X : NExpTied (recE hE Sp F ex h0 th).toD7) : NExpTied (recL hE Sp F L ex h0 th').toD7 :=
  { X with
    mtV := fun i j b k Q ψ h1 h2 h =>
      letI := X.acgWt i j b
      letI : Module (FractionRing ((recL hE Sp F L ex h0 th').toD7.ntw.O i)) (X.Wt i j b) := X.modWt i j b
      { X.mtV i j b k Q ψ h1 h2 h with } }



theorem sideB_keep {Rw : RowSide D} {low : Finset ℕ}
    {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} {S : RatDat D.ntw}
    {hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)} {eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0}
    {θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ}
    (B : SideB (recE hE Sp F ex h0 th).toD7 ((recE hE Sp F ex h0 th).cf cf) ((recE hE Sp F ex h0 th).row Rw) low Pq
      ((recE hE Sp F ex h0 th).rat S) hL eig θ)
    (chiI : ∀ s, L.abelian₂ s → NC.HC D.host.E)
    (hqs : ∀ i lam P, P ∉ T.S0 i →
      B.twF.iCq i (L.qs i lam P) = ((((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-(L.s2 i lam : ℝ) / 2) : ℝ) : ℂ))
    (hlam : ∀ s lam, NC.Read D.nd.plOm.1 (L.lamG s lam) (algebraMap (T.O s) (FractionRing (T.O s)))
      (B.chiD.embO s (L.sideL s lam)) (NC.complexEmbeddingRestrictedToSubfield D) (id (α := NC.HC D.host.E) (B.chiD.mu0 (L.jL s lam)) * id (α := NC.HC D.host.E) (B.chiD.del s) * (chiI s lam)⁻¹) 0) :
    Nonempty (SideB (recL hE Sp F L ex h0 th').toD7 ((recL hE Sp F L ex h0 th').cf cf) ((recL hE Sp F L ex h0 th').row Rw) low Pq
      ((recL hE Sp F L ex h0 th').rat S) hL eig θ) :=
  ⟨{ B with
      twF := twFC B.twF
      tw := { B.tw with qs_pos := hqs }
      chiD := { B.chiD with chiI := chiI }
      chi := { B.chi with lamG := hlam }
      exp := expC B.exp }⟩

end GlobalTheory.LamInstall
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.FitTw

noncomputable section

namespace GlobalTheory.TwInputs.SideBLoc



theorem exists_sideB_withLoc : ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ), ∀ (L : LocAll (lay0 D)) (ψ : (withLoc L).nd.Loc → NC.HC D.host.E), (∀ a, NC.ReadC (withLoc L).nd.plOm.1 ((withLoc L).ntw.psiL a) (NC.iotaC (withLoc L) a) (ψ a) 0) → ∃ Rw' : RowSide (withLoc L), HEq Rw'.locR Rw.locR ∧ ∃ Bs' : SideB (withLoc L) (cfL L cf) Rw' low Pq ({ S with } : RatDat (withLoc L).ntw) hL eig θ, HEq Bs'.rowS Bs.rowS := by
  intro D cf Rw low Pq S hL eig θ Bs L ψ hψ
  refine ⟨⟨Rw.locR, Rw.satR, Rw.lab_eq⟩, HEq.rfl, ?_⟩
  exact ⟨{ Bs with
    twF := twFL L Bs.twF
    tw := twTiedL L Bs.tw
    chiD := chiDL L Bs.chiD ψ
    chi := chiL L Bs.chi ψ hψ
    deltaRead := deltaReadL L Bs.deltaRead
    exp := expL L Bs.exp }, HEq.rfl⟩

end GlobalTheory.TwInputs.SideBLoc

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Links (PolF)
open Formalism.L2.NTheta (IsIdemAt)
open scoped TensorProduct




namespace GlobalTheory.ExportSeries.DualType

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.StepLaw (ResAt UnrOff)

variable {D : D7} {S T : HSp D}


open Classical in
def allP (B : Base S T) (Q : Finset (Pl D.host.E)) : Finset (Pl D.host.E) := B.G.Pg ∪ (B.de.Q ∪ Q)


open Classical in
def resP (B : Base S T) (ν : Twist D Circle) (PP : Pl D.host.E) : (kP PP)ˣ →* ℂˣ :=
  (if PP ∈ B.G.Pg then B.G.muC PP else 1) * B.de.locC PP * ν.locC PP

def vacC (B : Base S T) (ν : Twist D Circle) (g : GA D S) (h : GA D T) : ℂˣ :=
  ∏ PP ∈ allP B ν.Q, (resP B ν PP (GeneralLinearGroup.det (redFn B.F.βS PP (Lev.finE S g))))⁻¹ *
    resP B ν PP (GeneralLinearGroup.det (redFn B.F.βT PP (Lev.finE T h)))

end GlobalTheory.ExportSeries.DualType
end
end

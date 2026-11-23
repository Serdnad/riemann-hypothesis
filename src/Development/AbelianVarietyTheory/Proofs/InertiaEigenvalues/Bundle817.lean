module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RationalRayLevels
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle005
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsDetRoot
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle043
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1268
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle305
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle306
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle798
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle118
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle452
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle216
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle226
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle214
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle082
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle325
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle326
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle317
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle320
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle511
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle082
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SerRatRay

theorem isRat_const_mul {D : D7} (T : CoreJ D) (i : Fin D.R.m) {σ : T.Q.c.F →+* ℂ} (hV : T.V ((i : ℕ) + 1) σ = Wc D i)
    (C : Cover T ((i : ℕ) + 1) σ) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (φ : GA D (Wc D i) → ℂ) (c : ℂ)
    (h : IsRat T i hV C κ φ) (hc : c ∈ C.σ₂.fieldRange) : IsRat T i hV C κ (fun g => c * φ g) := by
  obtain ⟨φ', ⟨f₂, hf₂, rfl⟩, rfl⟩ := h
  obtain ⟨c', rfl⟩ := RingHom.mem_fieldRange.1 hc
  refine ⟨C.rd (wtA κ) (c' • f₂), ⟨c' • f₂, ⟨(sec _ _ _ _).smul_mem c' hf₂.1, ?_⟩, rfl⟩, ?_⟩
  · rw [map_smulₛₗ]
    exact Submodule.smul_mem _ _ hf₂.2
  · funext g
    simp only [castDict, Cover.rd, map_smulₛₗ, map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

end GlobalTheory.SerRatRay
end
end

section

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistLeft

theorem exists_principal_root {D : D7} (V : HSp D) (γ : GA D V) (hγ : γ ∈ GQ V) :
    ∃ e : D.host.Eˣ, IsDetRoot V γ (Units.map (incA D).toMonoidHom e) := by
  obtain ⟨γ₀, -, h0⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hγ)
  have hdet : ((matHom V γ).1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).det =
      incA D γ₀.1.det := by
    rw [← GlobalTheory.DetRootRows.det_bc, h0]; rfl
  generalize γ₀.1.det = d at hdet
  have hc : ∀ e : D.host.E, cA D (incA D e) = incA D (star e) := fun e => rfl
  haveI : Nontrivial (AF D.host.F) := (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F).nontrivial
  have hn : star d * d = 1 := by
    have := det_conj_mul V γ
    apply GlobalTheory.DetRootRows.inclR_injective (F := D.host.F) (AF D.host.F)
    rw [map_mul, map_one, ← hc, ← hdet]
    exact this
  obtain ⟨e, he0, he⟩ : ∃ e : D.host.E, e ≠ 0 ∧ e = d * star e := by
    by_cases hd : d = -1
    · obtain ⟨a, ha⟩ := GlobalTheory.RecDict.cmData_sig_ne_id D.sp.cm
      refine ⟨a - star a, sub_ne_zero.2 (Ne.symm ha), ?_⟩
      rw [hd, star_sub, star_star]; ring
    · refine ⟨1 + d, fun h => hd (by linear_combination h), ?_⟩
      rw [star_add, star_one]; linear_combination -hn
  refine ⟨Units.mk0 e he0, ?_⟩
  unfold IsDetRoot
  rw [hdet]
  show incA D e = incA D d * cA D (incA D e)
  rw [hc, ← map_mul, ← he]

theorem muVal_left {D : D7} (V : HSp D) (χ : (AE D)ˣ →* Circle)
    (hE : ∀ x : D.host.Eˣ, χ (Units.map (incA D).toMonoidHom x) = 1) (mu : GA D V → ℂ) (hmu : MuVal V χ mu)
    (γ : GA D V) (hγ : γ ∈ GQ V) (h : GA D V) : mu (γ * h) = mu h := by
  obtain ⟨x, hx⟩ := hmu.1 h
  obtain ⟨e, he⟩ := exists_principal_root V γ hγ
  rw [hmu.2 _ _ (detRootMul_holds V γ h _ x he hx), hmu.2 h x hx, map_mul, hE e, one_mul]

theorem twist_left : ∀ (D : D7) (V : HSp D) (pd : ℕ) (k : Type) [Field k] (σ : k →+* ℂ) (δ : Formalism.L2.Host.HChar D.host.E)
    (δc : (AE D)ˣ →* Circle), IsTwist pd σ δ δc → ∀ dd : GA D V → ℂ, (MuVal V δc dd ∨ MuVal V δc⁻¹ dd) →
    ∀ γ ∈ GQ V, ∀ h : GA D V, dd (γ * h) = dd h := by
  intro D V pd k _ σ δ δc ht dd hdd γ hγ h
  have hE : ∀ x : D.host.Eˣ, δc (Units.map (incA D).toMonoidHom x) = 1 := ht.1.1.2
  rcases hdd with hm | hm
  · exact muVal_left V δc hE dd hm γ hγ h
  · exact muVal_left V δc⁻¹ (fun x => by rw [MonoidHom.inv_apply, hE x, inv_one]) dd hm γ hγ h

end GlobalTheory.TwistLeft
end
end

section

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistValues
variable {D : D7}

theorem pow_eq_one (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle) (hc : ChrEq δc δ) (n : ℕ)
    (hn : δ.OrderDvd n) (x : (AE D)ˣ) : δc x ^ n = 1 := by
  have hH : IsHeckeChar D (δc ^ n) := by
    refine ⟨?_, fun k => ?_⟩
    · exact (continuous_pow n).comp hc.1.1
    · rw [MonoidHom.pow_apply, hc.1.2 k, one_pow]
  have := GlobalTheory.HeckeFinTrivial.eq_one_of_trivial_on_finite D (δc ^ n) hH (fun y hy => by
    rw [MonoidHom.pow_apply]
    exact GlobalTheory.CharOrderFin.char_pow_eq_one_of_orderDvd D δc δ hc n hn y hy) x
  rwa [MonoidHom.pow_apply] at this

theorem exists_pow_of_snd {R A B I : Type} [CommRing R] [CommRing A] [CommRing B] (e : R ≃+* A × B)
    (s : A ≃+* (I → ℂ)) (n : ℕ) (hn : 0 < n) (x : Rˣ) (hx : (e x).2 = 1) : ∃ V : Rˣ, x = V ^ n := by
  have hz : ∀ τ, s (e x).1 τ ≠ 0 := by
    intro τ h0
    have h1 : s (e x).1 * s (e ((x⁻¹ : Rˣ) : R)).1 = 1 := by
      rw [← map_mul, ← Prod.fst_mul, ← map_mul, Units.mul_inv, map_one, Prod.fst_one, map_one]
    have := congrFun h1 τ
    rw [Pi.mul_apply, h0, zero_mul, Pi.one_apply] at this
    exact zero_ne_one this
  choose w hw using fun τ => IsAlgClosed.exists_pow_nat_eq (s (e x).1 τ) hn
  have hw0 : ∀ τ, w τ ≠ 0 := fun τ h0 => hz τ (by rw [← hw τ, h0, zero_pow hn.ne'])
  let wi : I → ℂ := fun τ => (w τ)⁻¹
  have hwi : w * wi = 1 := funext fun τ => mul_inv_cancel₀ (hw0 τ)
  have hiw : wi * w = 1 := funext fun τ => inv_mul_cancel₀ (hw0 τ)
  let U : (A × B)ˣ := ⟨(s.symm w, 1), (s.symm wi, 1), by
      rw [Prod.mk_mul_mk, ← map_mul, hwi, map_one, mul_one]; rfl, by
      rw [Prod.mk_mul_mk, ← map_mul, hiw, map_one, mul_one]; rfl⟩
  refine ⟨Units.map e.symm.toRingHom.toMonoidHom U, Units.ext ?_⟩
  rw [Units.val_pow_eq_pow_val, Units.coe_map]
  change (x : R) = (e.symm (s.symm w, 1)) ^ n
  rw [← map_pow, Prod.pow_mk, one_pow, ← map_pow,
    show w ^ n = s (e x).1 from funext fun τ => by rw [Pi.pow_apply, hw τ], RingEquiv.symm_apply_apply, ← hx,
    Prod.mk.eta, RingEquiv.symm_apply_apply]

theorem eq_one_of_finPart (c : (AE D)ˣ →* Circle) (n : ℕ) (hn : 0 < n) (hpow : ∀ x, c x ^ n = 1) (x : (AE D)ˣ)
    (hx : finPart D (x : AE D) = 1) : c x = 1 := by
  obtain ⟨e, he, -, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  obtain ⟨V, hV⟩ := exists_pow_of_snd e (Formalism.IndefR.Eqv.splitEquiv D) n hn x ((he _).2.trans hx)
  rw [hV, map_pow, hpow]

theorem exists_global_approx : ∀ (L : Type) [Field L] [NumberField L] (R : Finset (HeightOneSpectrum (𝓞 L))) (z : ∀ P : HeightOneSpectrum (𝓞 L), P.adicCompletion L), (∀ P ∈ R, z P ≠ 0) → ∃ k : Lˣ, ∀ P ∈ R, Valued.v (z P - algebraMap L (P.adicCompletion L) (k : L)) ≤ WithZero.exp (-1 : ℤ) * Valued.v (z P) :=
  GlobalTheory.T.exists_field_element_relative_approx_completions



open Formalism.L2.Host in
theorem mem_of_infPart {k : Type} [Field k] (σ : k →+* ℂ) (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle)
    (hc : ChrEq δc δ) (n : ℕ) (hn : 0 < n) (hord : δ.OrderDvd n) (htame : ∀ v, δ.TameAt v) (hval : δ.ValuesIn 0 σ)
    (x : (AE D)ˣ) (hx : infPart D (x : AE D) = 1) : ((δc x : Circle) : ℂ) ∈ σ.fieldRange := by
  classical
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  have h4 := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2 h4 δc δ hc
  have hev := GlobalTheory.HeckeSplit.eventually_unrAt δ.1 δ.2.1
  set Rm := (Filter.eventually_cofinite.1 hev).toFinset with hRmdef
  have hRm : ∀ P, P ∉ Rm → δ.UnrAt P := fun P hP => by
    by_contra h
    exact hP ((Set.Finite.mem_toFinset _).2 h)
  let zz : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ := Units.map ((ι : _ →+* _).comp (finPart D)).toMonoidHom x
  have hz0 : ∀ P, (zz : FiniteAdeleRing (𝓞 D.host.E) D.host.E) P ≠ 0 := (FiniteAdeleRing.isUnit_iff.1 zz.isUnit).1
  obtain ⟨k, hk⟩ := exists_global_approx D.host.E Rm (fun P => (zz : FiniteAdeleRing (𝓞 D.host.E) D.host.E) P)
    (fun P _ => hz0 P)
  let K : (AE D)ˣ := Units.map (incA D).toMonoidHom k
  obtain ⟨-, a, b, -, -, hab, ha, hb⟩ := GlobalTheory.IdeleParts.congr_open_and_parts D
  have e1 : δc x = δc (b (x * K⁻¹)) := by
    have : δc (x * K⁻¹) = δc x := by rw [map_mul, map_inv, hc.1.2 k, inv_one, mul_one]
    rw [← this]
    conv_lhs => rw [hab (x * K⁻¹)]
    rw [map_mul, eq_one_of_finPart δc n hn (pow_eq_one δ δc hc n hord) _ (ha _).2, one_mul]
  set y := b (x * K⁻¹) with hydef
  have hy : infPart D (y : AE D) = 1 := (hb _).1
  have hyP : ∀ P, ι (finPart D (y : AE D)) P =
      (zz : FiniteAdeleRing (𝓞 D.host.E) D.host.E) P * algebraMap D.host.E _ ((k⁻¹ : D.host.Eˣ) : D.host.E) := by
    intro P
    rw [(hb _).2, Units.val_mul, map_mul, map_mul]
    have : ((K⁻¹ : (AE D)ˣ) : AE D) = incA D ((k⁻¹ : D.host.Eˣ) : D.host.E) := rfl
    rw [this]
    show _ * ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] ((k⁻¹ : D.host.Eˣ) : D.host.E)) P = _
    rw [h1]
    rfl

  let yy : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ := Units.map ((ι : _ →+* _).comp (finPart D)).toMonoidHom y
  have hy0 : ∀ P, ι (finPart D (y : AE D)) P ≠ 0 := (FiniteAdeleRing.isUnit_iff.1 yy.isUnit).1
  obtain ⟨S0, -, -, hS0⟩ := GlobalTheory.finiteIdele_exists_local_approx D.host.E N hN yy
  choose kk hkk using fun P => GlobalTheory.adicCompletion_exists_unit_approx D.host.E N hN P _ (hy0 P)
  have key := hprod y hy (S0 ∪ Rm) kk (fun P _ => ⟨(hkk P).1, (hkk P).2.1⟩)
    (fun P hP => hS0 P fun h => hP (Finset.mem_union_left _ h))
  rw [e1, key]
  refine prod_mem fun P _ => ?_
  have hva : ∀ t : D.host.E, Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) t) = P.valuation D.host.E t :=
    fun t => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P t
  by_cases hR : P ∈ Rm
  ·
    set zP := (zz : FiniteAdeleRing (𝓞 D.host.E) D.host.E) P with hzP
    have hk0 : Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E)) ≠ 0 := by
      rw [hva]; exact (Valuation.ne_zero_iff _).2 k.ne_zero
    have hlt : WithZero.exp (-1 : ℤ) < 1 := by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
    have hzv : Valued.v zP = Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E)) := by
      refine (Valuation.map_eq_of_sub_lt _ ?_).symm
      rw [Valuation.map_sub_swap]
      exact (hk P hR).trans_lt (mul_lt_of_lt_one_left (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (hz0 P))) hlt)
    have hkinv : algebraMap D.host.E (P.adicCompletion D.host.E) ((k⁻¹ : D.host.Eˣ) : D.host.E) *
        algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have hkv' : Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) ((k⁻¹ : D.host.Eˣ) : D.host.E)) *
        Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E)) = 1 := by
      rw [← map_mul, hkinv, map_one]
    have hyv : Valued.v (ι (finPart D (y : AE D)) P) = 1 := by
      rw [hyP, map_mul, mul_comm, hzv]; exact hkv'
    have hy1 : Valued.v (ι (finPart D (y : AE D)) P - 1) ≤ WithZero.exp (-1 : ℤ) := by
      have : ι (finPart D (y : AE D)) P - 1 = (zP - algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E)) *
          algebraMap D.host.E (P.adicCompletion D.host.E) ((k⁻¹ : D.host.Eˣ) : D.host.E) := by
        rw [hyP, sub_mul, mul_comm (algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E)), hkinv]
      rw [this, map_mul]
      calc Valued.v (zP - _) * Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) ((k⁻¹ : D.host.Eˣ) : D.host.E))
          ≤ WithZero.exp (-1 : ℤ) * Valued.v zP *
            Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) ((k⁻¹ : D.host.Eˣ) : D.host.E)) :=
            mul_le_mul' (hk P hR) le_rfl
        _ = WithZero.exp (-1 : ℤ) := by rw [mul_assoc, hzv, mul_comm (Valued.v (algebraMap _ _ (k : D.host.E))), hkv', mul_one]
    obtain ⟨q1, q2, q3⟩ := hkk P
    have hq : Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) (kk P : D.host.E)) = 1 := by
      rw [hva, ← q1, hyv]
    have hq1 : Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) (kk P : D.host.E) - 1) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
      have e2 : algebraMap D.host.E (P.adicCompletion D.host.E) (kk P : D.host.E) - 1 =
          (ι (finPart D (y : AE D)) P - 1) - (ι (finPart D (y : AE D)) P - algebraMap D.host.E _ (kk P : D.host.E)) := by ring
      rw [e2]
      refine (Valuation.map_sub _ _ _).trans (max_le hy1 ?_)
      rw [← hva, hq, mul_one] at q3
      simpa using q3
    have ht := htame P (Formalism.L2.Host.atFin P (kk P)) hq hq1
    have : δ.locK P (kk P) = 1 := ht
    rw [this, Units.val_one]
    exact one_mem _
  ·
    have hu := hRm P hR
    have hkv0 : P.valuation D.host.E (kk P : D.host.E) ≠ 0 := (Valuation.ne_zero_iff _).2 (kk P).ne_zero
    have hm : P.valuation D.host.E (kk P : D.host.E) = WithZero.exp (-(-WithZero.log (P.valuation D.host.E (kk P : D.host.E)))) := by
      rw [neg_neg, WithZero.exp_log hkv0]
    rw [GlobalTheory.CharUnramVal.locK_eq_val_zpow δ P hu (kk P) _ hm, Units.val_zpow_eq_zpow_val]
    refine zpow_mem ?_ _
    obtain ⟨t, ht⟩ := hval P hu
    refine ⟨t, ht.trans ?_⟩
    simp [Formalism.L2.Host.HChar.valTw]

theorem mem_fieldRange : ∀ (D : D7) (V : HSp D) (pd : ℕ) (k : Type) [Field k] (σ : k →+* ℂ) (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle), IsTwist pd σ δ δc → ∀ dd : GA D V → ℂ, (MuVal V δc dd ∨ MuVal V δc⁻¹ dd) → ∀ g, dd g ∈ σ.fieldRange := by
  intro D V pd k _ σ δ δc hT dd hdd g
  obtain ⟨hc, ⟨n, hn, hord⟩, -, htame, -, hval⟩ := hT
  have key : ∀ x : (AE D)ˣ, ((δc x : Circle) : ℂ) ∈ σ.fieldRange := by
    intro x
    obtain ⟨-, a, b, -, -, hab, ha, hb⟩ := GlobalTheory.IdeleParts.congr_open_and_parts D
    rw [hab x, map_mul, eq_one_of_finPart δc n hn (pow_eq_one δ δc hc n hord) _ (ha x).2, one_mul]
    exact mem_of_infPart σ δ δc hc n hn hord htame hval _ (hb x).1
  rcases hdd with ⟨hex, hv⟩ | ⟨hex, hv⟩
  · obtain ⟨x, hx⟩ := hex g
    rw [hv g x hx]
    exact key x
  · obtain ⟨x, hx⟩ := hex g
    rw [hv g x hx, MonoidHom.inv_apply, Circle.coe_inv]
    exact inv_mem (key x)

end GlobalTheory.TwistValues
end
end

section

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilTwistSeries

theorem twist_val_mem {D : D7} {pd : ℕ} {k : Type} [Field k] {σ : k →+* ℂ} {δ : Formalism.L2.Host.HChar D.host.E}
    {δc : (AE D)ˣ →* Circle} (h : IsTwist pd σ δ δc) (x : (AE D)ˣ) : ((δc x : Circle) : ℂ) ∈ σ.fieldRange := by
  obtain ⟨hE, ⟨n, hn, ho⟩, -, ht, -, hv⟩ := h
  have : IsTotallyComplex D.host.E := D.sp.cm.cmUnram.1
  have hfin := (GlobalTheory.Mem.UnrAe.unr_ae_and_level _ δ).1
  have hu : ∀ v, v ∉ hfin.toFinset → δ.UnrAt v := fun v hv' => by
    by_contra hc
    exact hv' (hfin.mem_toFinset.2 hc)
  refine GlobalTheory.TwistValues.char_mem δc δ hE hn ho σ.fieldRange (fun P k => ?_) x
  exact GlobalTheory.TwistValues.locK_mem δ (GlobalTheory.RationalValues.unitsIn σ.fieldRange) hfin.toFinset ht
    (GlobalTheory.TypeValues.inf_eq_one δ hn ho) hu
    (fun v hv' => by
      obtain ⟨y, hy⟩ := hv v (hu v hv')
      show ((δ.val v : ℂˣ) : ℂ) ∈ σ.fieldRange
      refine ⟨y, ?_⟩
      rw [hy, Formalism.L2.Host.HChar.valTw]
      simp) P k

theorem theta_weil_twist : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i), GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV →
    ∀ gramR c0R c0L, Bridge.FamTie R.B R.pl (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) R.Q (labLL D)
        (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L →
    ∀ u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) →
      ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, GoodCover T R i C (κ i).n →
      ∀ (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle), IsTwist C.d.pd C.σ₂ δ δc →
      ∀ om : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ),
        IsWeilDatumO R.ψ (Vc D i) (Wc D i) (Lift.chrTh (Lift.tup R.mu0 δc) R.eta ((i : ℕ) + 1)).1
          (Lift.chrTh (Lift.tup R.mu0 δc) R.eta ((i : ℕ) + 1)).2 om →
      ∀ s ∈ GfC (Vc D i), ∀ f : WO (Vc D i) (Wc D i) → ℂ,
        IsLevDatum R.ψ (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) (T.Q.l.M * C.d.pd) C.σ₂.fieldRange (R.vacP i) f →
      ∀ w ∈ ratVec R i (c0L i) C.σ₂.fieldRange,
        ∃ c ∈ C.σ₂.fieldRange, ∃ dd : GA D (Wc D i) → ℂ, (MuVal (Wc D i) δc dd ∨ MuVal (Wc D i) δc⁻¹ dd) ∧
          ∀ g, thetaKO om s g (harmVec R i u w f) = c * (dd g * thetaKO (R.ωP i A.μ0) s g (harmVec R i u w f)) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hJ hL hG hFam hMod hP hT i hV hpin gramR c0R c0L hB u hu C hC δ δc hδ om hom s hs
    f hf w hw
  have hψ : IsStdChar D R.ψ (-1) := (hP.ωP i A.μ0).std
  have hvac := (hP.vP i A.μ0).1
  have hθ : IsInfFam R.θ := hvac.2.inf
  have hf0 : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vacP i) := GlobalTheory.OneMapRef.isThetaFunO_of_isVacO hvac
  obtain ⟨P, e, Φ, -, -, -, -, -, hTh⟩ := hf
  have hft : IsThetaFunO R.ψ (Vc D i) (Wc D i) f := GlobalTheory.VecTheta.isThetaFunO_of_thetaAt hψ hθ hTh hf0
  have hH : IsThetaFunO R.ψ (Vc D i) (Wc D i) (harmVec R i u w f) :=
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO hψ hθ _ _ _ _ hft _
  have hxi : R.xi A.μ0 = 1 :=
    MonoidHom.ext (GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (hL.xi_base ▸ hL.xi A.μ0))
  have hmu : R.toLevCh.mu A.μ0 = Lift.tup R.mu0 (1 : (AE D)ˣ →* Circle) := by
    unfold LevCh.mu
    rw [hxi]
  have hω : IsWeilDatumO R.ψ (Vc D i) (Wc D i) (Lift.chrTh R.mu0 R.eta ((i : ℕ) + 1)).1
      (Lift.chrTh R.mu0 R.eta ((i : ℕ) + 1)).2 (R.ωP i A.μ0) := by
    have h := hP.ωP i A.μ0
    rw [hmu, GlobalTheory.SplitChange.chrTh_tup] at h
    simpa only [mul_one] using h
  rw [GlobalTheory.SplitChange.chrTh_tup] at hom
  have hδH : IsHeckeChar D δc := hδ.1.1
  have hδF : ∀ a, δc (idF D a) = 1 := GlobalTheory.GridWeil.triv_base hδ.1 hδ.2.2.1
  obtain ⟨nV, hnV, -⟩ := GlobalTheory.Member.exists_muVal D (Vc D i) δc hδH hδF
  obtain ⟨nW, hnW, -⟩ := GlobalTheory.Member.exists_muVal D (Wc D i) δc hδH hδF
  obtain ⟨x, hx⟩ := hnV.1 s
  refine ⟨(nV s)⁻¹, ?_, nW, Or.inl hnW, fun g => ?_⟩
  · rw [hnV.2 s x hx]
    exact inv_mem (twist_val_mem hδ x)
  · rw [GlobalTheory.SplitChange.thetaKO_twist hω hδH hδF hom hnV hnW s g hH]
    ring

end GlobalTheory.WeilTwistSeries
end
end

section

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistFinPart

theorem eq_one_of_finPart_eq_one (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (h : ChrEq c χ)
    {n : ℕ} (hn : 0 < n) (ho : χ.OrderDvd n) (x : (AE D)ˣ) (hx : finPart D (x : AE D) = 1) : c x = 1 := by
  have key := GlobalTheory.HeckeFinTrivial.eq_one_of_trivial_on_finite D (c ^ n)
    ⟨h.1.1.pow n, fun x => by rw [MonoidHom.pow_apply, h.1.2 x, one_pow]⟩
    (GlobalTheory.CharOrderFin.char_pow_eq_one_of_orderDvd D c χ h n ho)
  obtain ⟨y, rfl⟩ := GlobalTheory.IdeleDiv.exists_pow_eq_of_finPart_eq_one D n hn x hx
  rw [map_pow]
  exact key y

theorem isDetRoot_mul' {D : D7} (V : HSp D) (g g' : GA D V) (x x' : (AE D)ˣ) (hx : IsDetRoot V g x)
    (hx' : IsDetRoot V g' x') : IsDetRoot V (g * g') (x * x') := by
  unfold IsDetRoot at *
  rw [Units.val_mul, (matHom V).map_mul, Units.val_mul, Matrix.det_mul, RingHom.map_mul]
  conv_lhs => rw [hx, hx']
  ring

theorem exists_isDetRoot_finPart_one {D : D7} (V : HSp D) (a : GA D V) (ha : finHom V a = 1) (z : (AE D)ˣ)
    (hz : IsDetRoot V a z) : ∃ y : (AE D)ˣ, finPart D (y : AE D) = 1 ∧ IsDetRoot V a y := by
  obtain ⟨y, hyi, hyf⟩ := GlobalTheory.PlaceIdem.parts_surj D (infPart D (z : AE D)) 1
  obtain ⟨y', hyi', hyf'⟩ := GlobalTheory.PlaceIdem.parts_surj D (infPart D ((z⁻¹ : (AE D)ˣ) : AE D)) 1
  have hyy : y * y' = 1 := GlobalTheory.PlaceIdem.parts_inj D _ _
    (by rw [RingHom.map_mul, hyi, hyi', ← RingHom.map_mul, Units.mul_inv, RingHom.map_one])
    (by rw [RingHom.map_mul, hyf, hyf', mul_one, RingHom.map_one])
  have hc : ∀ w : AE D, infPart D (sigR (AF D.host.F) D.sp.cm.sig w) =
      sigR (Ainf D.host.F) D.sp.cm.sig (infPart D w) := fun w => GlobalTheory.PlaceIdem.infPart_cA D w
  have hf : ∀ w : AE D, finPart D (sigR (AF D.host.F) D.sp.cm.sig w) =
      sigR (Af D.host.F) D.sp.cm.sig (finPart D w) := fun w => GlobalTheory.PlaceIdem.finPart_cA D w
  have e2 : finPart D (matHom V a).1.det = 1 := by
    have e : finPart D (matHom V a).1.det = (finHom V a).1.det := (finPart D).map_det _
    rw [e, ha]
    simp
  refine ⟨⟨y, y', hyy, by rw [mul_comm]; exact hyy⟩, hyf, ?_⟩
  show y = (matHom V a).1.det * sigR (AF D.host.F) D.sp.cm.sig y
  refine GlobalTheory.PlaceIdem.parts_inj D _ _ ?_ ?_
  · have h1 := congrArg (infPart D) hz
    unfold IsDetRoot at h1
    rw [RingHom.map_mul, hc] at h1
    rw [RingHom.map_mul, hc, hyi]
    exact h1
  · rw [RingHom.map_mul, hf, hyf, e2, RingHom.map_one, one_mul]

theorem eq_of_finHom_of_triv {D : D7} (V : HSp D) (χ : (AE D)ˣ →* Circle)
    (hχ : ∀ y : (AE D)ˣ, finPart D (y : AE D) = 1 → χ y = 1) (dd : GA D V → ℂ) (hd : MuVal V χ dd)
    (h h' : GA D V) (hh : finHom V h = finHom V h') : dd h = dd h' := by
  have ha : finHom V (h⁻¹ * h') = 1 := by rw [map_mul, map_inv, hh, inv_mul_cancel]
  obtain ⟨x, hx⟩ := hd.1 h
  obtain ⟨z, hz⟩ := hd.1 (h⁻¹ * h')
  obtain ⟨y, hy1, hy⟩ := exists_isDetRoot_finPart_one V _ ha z hz
  have hxy := isDetRoot_mul' V h (h⁻¹ * h') x y hx hy
  rw [mul_inv_cancel_left] at hxy
  rw [hd.2 h x hx, hd.2 h' _ hxy, map_mul, hχ y hy1, mul_one]

theorem twist_eq_of_finHom : ∀ (D : D7) (V : HSp D) (pd : ℕ) (k : Type) [Field k] (σ : k →+* ℂ)
    (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle), IsTwist pd σ δ δc → ∀ dd : GA D V → ℂ,
    (MuVal V δc dd ∨ MuVal V δc⁻¹ dd) → ∀ h h' : GA D V, finHom V h = finHom V h' → dd h = dd h' := by
  intro D V pd k _ σ δ δc hT dd hdd h h' hh
  obtain ⟨hc, ⟨n, hn, ho⟩, -⟩ := hT
  have h1 : ∀ y : (AE D)ˣ, finPart D (y : AE D) = 1 → δc y = 1 := eq_one_of_finPart_eq_one D δc δ hc hn ho
  rcases hdd with hd | hd
  · exact eq_of_finHom_of_triv V δc h1 dd hd h h' hh
  · exact eq_of_finHom_of_triv V δc⁻¹ (fun y hy => by rw [MonoidHom.inv_apply, h1 y hy, inv_one]) dd hd h h' hh

end GlobalTheory.TwistFinPart
end
end

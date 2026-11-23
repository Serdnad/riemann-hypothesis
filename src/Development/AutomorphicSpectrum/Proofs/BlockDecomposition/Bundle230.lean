module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle037
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle205
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle144
import GroundTheory.PAdicHodge.ACrisBdRGalois
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GalOCOkToOC
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.SchemeModels
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SchemeDescendsToSubalgebra
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MetaplecticLowRank.LowC
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle215
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.MoyPrasadJacquetIsoTrivial

@[expose] public section

section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.LatLevel

theorem dk_fk (l : ℕ) [Fact l.Prime] (k : ℕ) (w : Ainf l) :
    Lat.dk l k (Lat.fk l (k + 1) w) = Lat.fk l k w := by
  simp only [Lat.dk, Lat.fk, RingHom.comp_apply]
  exact Ideal.Quotient.factor_mk _ _

theorem dk_dpE (l : ℕ) [Fact l.Prime] (M k i : ℕ) :
    Lat.dk l k (Lat.dpE (Lat.fk l (k + 1)) (xi0 l) l M i) = Lat.dpE (Lat.fk l k) (xi0 l) l M i := by
  simp only [Lat.dpE, Lat.η, map_rat_smul, map_pow, dk_fk]

theorem dk_mem_sub (l : ℕ) [Fact l.Prime] (M k : ℕ) :
    ∀ x ∈ Lat.sub (Lat.fk l (k + 1)) (xi0 l) l M, Lat.dk l k x ∈ Lat.sub (Lat.fk l k) (xi0 l) l M := by
  intro x hx
  have hle : Lat.sub (Lat.fk l (k + 1)) (xi0 l) l M ≤
      (Lat.sub (Lat.fk l k) (xi0 l) l M).comap (Lat.dk l k) := by
    refine Subring.closure_le.2 ?_
    rintro y (⟨w, rfl⟩ | ⟨i, rfl⟩)
    · refine Subring.mem_comap.2 ?_
      rw [dk_fk]
      exact Subring.subset_closure (Or.inl ⟨w, rfl⟩)
    · refine Subring.mem_comap.2 ?_
      rw [dk_dpE]
      exact Subring.subset_closure (Or.inr ⟨i, rfl⟩)
  exact hle hx

end GlobalTheory.CompanionTheory.LatLevel
end

section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC

theorem iota_algebraMap_OK : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ a : OK l K, (lev h k).ι (algebraMap (OK l K) (lev h k).A a) = algebraMap K (lev h k).B (a : K) := by
  intro l _ K M h k a
  rfl

end GlobalTheory.CompanionTheory.LatC
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC

theorem algebraMap_pInv {l : ℕ} [Fact l.Prime] (z : ↥(algebraMap (BdRp l) (BdR l)).range) :
    algebraMap (BdRp l) (BdR l) (pInv l z) = z.1 :=
  congrArg Subtype.val ((RingEquiv.ofBijective (algebraMap (BdRp l) (BdR l)).rangeRestrict
    ⟨fun x y h => IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l) (congrArg Subtype.val h),
      RingHom.rangeRestrict_surjective _⟩).apply_symm_apply z)

theorem iota_lam_eq_toB {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ) :
    ∀ (c : (per l K).A) (y : (per l K).P), (y : (per l K).B) = (per l K).i c →
      (lev h k).ι ((lev h k).lam c) = (lev h k).toB y := by
  intro c y hy
  have h1 : (lev h k).ι ((lev h k).lam c) = pk l k (ACris.iota ℂ_[l] l c) := rfl
  have h2 : (lev h k).toB y = pk l k (pInv l y) := rfl
  rw [h1, h2]
  congr 1
  apply IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l)
  exact hy.symm.trans (algebraMap_pInv y).symm

end GlobalTheory.CompanionTheory.LatC
end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatLevel

theorem dk_gB {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}
    (h : LevHyp l K M) (k : ℕ) (g : K.fixingSubgroup) (x : Bk l (k + 1)) :
    dk l k (gB h (k + 1) g x) = gB h k g (dk l k x) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [dk, gB, Ideal.quotientMap_mk, Ideal.Quotient.factor_mk]

theorem levSys_dA_σA {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}
    (h : LevHyp l K M) : ∀ m g a,
    (levSys h).dA m (((levSys h).L (m + 1)).σA g a) = ((levSys h).L m).σA g ((levSys h).dA m a) := by
  intro m g a
  apply Subtype.ext
  exact dk_gB h (m + 1) g a.1

end GlobalTheory.CompanionTheory.LatLevel
end
end

section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatLevels

theorem pInv_surjective (l : ℕ) [Fact l.Prime] : Function.Surjective (pInv l) := by
  intro x
  refine ⟨(algebraMap (BdRp l) (BdR l)).rangeRestrict x, ?_⟩
  unfold pInv
  exact (RingEquiv.ofBijective (algebraMap (BdRp l) (BdR l)).rangeRestrict
    ⟨fun x y h => IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l)
      (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩).symm_apply_apply x

theorem toB_surjective {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}
    (h : LevHyp l K M) (k : ℕ) : Function.Surjective (lev h k).toB := by
  have h1 : Function.Surjective ((pk l k).comp (pInv l)) := by
    rw [RingHom.coe_comp]
    exact (Ideal.Quotient.mk_surjective).comp (pInv_surjective l)
  exact h1

end GlobalTheory.CompanionTheory.LatLevels
end

section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatCZp

theorem padicInt_mem_sub (l : ℕ) [Fact l.Prime] (M k : ℕ) (z : ℤ_[l]) :
    Lat.pk l k (algClToBdR l (algebraMap ℚ_[l] (PadicAlgCl l) (z : ℚ_[l]))) ∈
      Lat.sub (Lat.fk l k) (xi0 l) l M := by
  have h1 : algClToBdR l (algebraMap ℚ_[l] (PadicAlgCl l) (z : ℚ_[l])) =
      wittToBDeRhamPlus (normInteger ℂ_[l]) l (IsPerfectoidField.padicIntToWitt (K := ℂ_[l]) l z) :=
    ((algClToBdR l).commutes (z : ℚ_[l])).trans
      (IsPerfectoidField.algebraMap_padic_coe (K := ℂ_[l]) l z)
  rw [h1]
  exact Subring.subset_closure (Or.inl ⟨IsPerfectoidField.padicIntToWitt (K := ℂ_[l]) l z, rfl⟩)

end GlobalTheory.CompanionTheory.LatCZp
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatSigDP

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}

theorem exists_gB_xi (h : LevHyp l K M) (k : ℕ) (g : K.fixingSubgroup) :
    ∃ u : Ainf l, gB h k g (fk l k (xi0 l)) = fk l k (u * xi0 l) := by
  obtain ⟨u, hu⟩ := GlobalTheory.CompanionTheory.TwFil.exists_gal_xi (toBot g.1)
  refine ⟨u, ?_⟩
  have e : galBdRHom (toBot g.1) (wittToBDeRhamPlus (normInteger ℂ_[l]) l (xi0 l)) =
      wittToBDeRhamPlus (normInteger ℂ_[l]) l (u * xi0 l) := by
    rw [← hu, ← gal_smul_wittToBDeRhamPlus]
    rfl
  show Ideal.Quotient.mk _ (galBdRHom (toBot g.1) (wittToBDeRhamPlus (normInteger ℂ_[l]) l (xi0 l))) = _
  rw [e]
  rfl

theorem sigA_isDPMorphism (h : LevHyp l K M) (k : ℕ) (g : K.fixingSubgroup) :
    IsDPMorphism (lev h k).γ (lev h k).γ ((lev h k).σA g) := by
  obtain ⟨u, hu⟩ := exists_gB_xi h k g
  exact GlobalTheory.CompanionTheory.LatDP.isDPMorphism_map (fk l k) (xi0 l) (fk l k) (xi0 l) l M (gB h k g) (h.gal k g) u hu
    (h.hc k) (h.hc k)

end GlobalTheory.CompanionTheory.LatSigDP
end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatPdpB

variable (l : ℕ) [Fact l.Prime]

theorem span_xi_eq_span_fontaine_t :
    Ideal.span {wittToBDeRhamPlus (normInteger ℂ_[l]) l (xi0 l)} = Ideal.span {tBdR l} := by
  haveI : IsPerfectoidField ℂ_[l] l := IsPerfectoidField.padicComplex l
  have hg := IsPerfectoidField.ker_fontaineTheta_eq_span_kerThetaGenerator ℂ_[l] l
  generalize IsPerfectoidField.kerThetaGenerator ℂ_[l] l = g at hg
  have hnorm : ∀ z : normInteger ℂ_[l], ‖(z : ℂ_[l])‖ ≤ 1 := fun z => mem_normInteger.1 z.2
  have hbound : ∀ w : WittVector l (PreTilt (normInteger ℂ_[l]) l),
      WittVector.fontaineTheta (normInteger ℂ_[l]) l w = 0 →
      ‖((PreTilt.untilt (WittVector.constantCoeff w) : normInteger ℂ_[l]) : ℂ_[l])‖ ≤
        ‖((l : normInteger ℂ_[l]) : ℂ_[l])‖ := by
    intro w hw
    have h1 : Ideal.Quotient.mk (Ideal.span {(l : normInteger ℂ_[l])})
        (PreTilt.untilt (WittVector.constantCoeff w)) = 0 := by
      rw [PreTilt.mk_untilt_eq_coeff_zero]
      have h2 := WittVector.mk_fontaineTheta (R := normInteger ℂ_[l]) (p := l) w
      rw [hw, map_zero] at h2
      exact h2.symm
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at h1
    obtain ⟨z, hz⟩ := h1
    rw [← hz, Subring.coe_mul, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hnorm z)
  have hx : xi0 l ∈ RingHom.ker (WittVector.fontaineTheta (normInteger ℂ_[l]) l) := by
    rw [RingHom.mem_ker, CrystallineSemistableComparison.xi0, map_sub, map_natCast, WittVector.fontaineTheta_teichmuller,
      untilt_pFlat, sub_self]
  rw [hg, Ideal.mem_span_singleton'] at hx
  obtain ⟨c, hc⟩ := hx
  have hg0 : WittVector.fontaineTheta (normInteger ℂ_[l]) l g = 0 := by
    rw [← RingHom.mem_ker, hg]
    exact Ideal.mem_span_singleton_self g
  have hcn : WittVector.fontaineTheta (normInteger ℂ_[l]) l c ≠ 0 := by
    intro hc0
    have hcm : c ∈ RingHom.ker (WittVector.fontaineTheta (normInteger ℂ_[l]) l) := hc0
    rw [hg, Ideal.mem_span_singleton'] at hcm
    obtain ⟨d, hd⟩ := hcm
    have hxe : xi0 l = d * g * g := by rw [← hc, ← hd]
    have hco := congrArg WittVector.constantCoeff hxe
    have hT : WittVector.constantCoeff (WittVector.teichmuller l (pFlat l)) = pFlat l :=
      WittVector.teichmuller_coeff_zero l _
    rw [CrystallineSemistableComparison.xi0, map_sub, map_natCast, hT, map_mul, map_mul,
      CharP.cast_eq_zero (PreTilt (normInteger ℂ_[l]) l) l, zero_sub] at hco
    have hpf : pFlat l = (-WittVector.constantCoeff d) * WittVector.constantCoeff g *
        WittVector.constantCoeff g := by
      rw [neg_mul, neg_mul, ← hco, neg_neg]
    have hu := congrArg (fun y => ‖((PreTilt.untilt y : normInteger ℂ_[l]) : ℂ_[l])‖) hpf
    simp only [map_mul, Subring.coe_mul, norm_mul, untilt_pFlat] at hu
    have hb := hbound g hg0
    have hd1 := hnorm (PreTilt.untilt (-WittVector.constantCoeff d))
    have hpos : 0 < ‖((l : normInteger ℂ_[l]) : ℂ_[l])‖ := by
      rw [norm_pos_iff]; push_cast; exact natCast_p_ne_zero_cp
    have hlt : ‖((l : normInteger ℂ_[l]) : ℂ_[l])‖ < 1 :=
      IsPerfectoidField.norm_natCast_integer_lt_one (K := ℂ_[l]) l
    have hn0 := norm_nonneg ((PreTilt.untilt (WittVector.constantCoeff g) : normInteger ℂ_[l]) : ℂ_[l])
    have hn1 := norm_nonneg ((PreTilt.untilt (-WittVector.constantCoeff d) : normInteger ℂ_[l]) : ℂ_[l])
    nlinarith [mul_le_mul hb hb hn0 hpos.le, mul_le_mul_of_nonneg_right hd1 (mul_nonneg hn0 hn0),
      mul_lt_of_lt_one_left hpos hlt]
  have hcu : IsUnit (wittToBDeRhamPlus (normInteger ℂ_[l]) l c) := by
    by_contra hnu
    have hm : wittToBDeRhamPlus (normInteger ℂ_[l]) l c ∈
        IsLocalRing.maximalIdeal (BDeRhamPlus (normInteger ℂ_[l]) l) :=
      (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hnu)
    rw [IsPerfectoidField.maximalIdeal_bDeRhamPlus, RingHom.mem_ker,
      IsPerfectoidField.thetaBDeRhamPlusField_wittToBDeRhamPlus] at hm
    exact hcn (by exact_mod_cast hm)
  rw [← hc, map_mul, Ideal.span_singleton_mul_left_unit hcu,
    ← IsPerfectoidField.maximalIdeal_bDeRhamPlus_eq_span hg, maximalIdeal_eq_span_tBdR]

theorem span_fk_pow (k r : ℕ) :
    Ideal.span {fk l k (xi0 l) ^ r} = Ideal.span {pk l k (tBdR l) ^ r} := by
  have h2 : Ideal.span {wittToBDeRhamPlus (normInteger ℂ_[l]) l (xi0 l) ^ r} =
      Ideal.span {tBdR l ^ r} := by
    rw [← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow, span_xi_eq_span_fontaine_t]
  have h3 := congrArg (Ideal.map (pk l k)) h2
  simp only [Ideal.map_span, Set.image_singleton, map_pow] at h3
  exact h3

theorem pInv_eq_tBdR {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (t : (per l K).P)
    (ht : (t : (per l K).B) = (per l K).tB) : pInv l t = tBdR l := by
  have hi : GroundTheory.PAdicHodge.ACris.iota ℂ_[l] l (Formalism.Per6.tA l) = tBdR l :=
    GroundTheory.PAdicHodge.ACris.iota_periodT (ε := epsilon l) untilt_epsilon
  have key : (algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l)).rangeRestrict (tBdR l) = t := by
    apply Subtype.ext
    refine Eq.trans ?_ ht.symm
    show algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) (tBdR l) =
      algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l)
        (GroundTheory.PAdicHodge.ACris.iota ℂ_[l] l (Formalism.Per6.tA l))
    rw [hi]
  rw [← key]
  unfold CrystallineSemistableComparison.Pb.Lat.pInv
  simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  exact (RingEquiv.symm_apply_eq _).2 rfl

end GlobalTheory.CompanionTheory.LatPdpB


open GlobalTheory.CompanionTheory.LatPdpB in
theorem GlobalTheory.CompanionTheory.LatPdpB.dividedPowerFiltration_lev_eq_span_pow : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ (r : ℕ) (t : (per l K).P), (t : (per l K).B) = (per l K).tB → pdP (lev h k).γB r = Ideal.span {(lev h k).toB t ^ r} := by
  intro l _ K M h k r t ht
  show pdP (γB (fk l k) (xi0 l)) r = Ideal.span {(pk l k) (pInv l t) ^ r}
  rw [GlobalTheory.CompanionTheory.DPFiltration.pdP_γB, pInv_eq_tBdR l t ht, span_fk_pow]
end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC.Red

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}

theorem ι_lam_ainf (h : LevHyp l K M) (k : ℕ) (w : Ainf l) :
    (lev h k).ι ((lev h k).lam (algebraMap (Ainf l) (Acris l) w)) = fk l k w := by
  show pk l k (ACris.iota ℂ_[l] l (algebraMap (Ainf l) (Acris l) w)) = _
  rw [ACris.iota_algebraMap]
  rfl

theorem pk_mem_of_theta (k : ℕ) {d : BdRp l} (hd : IsPerfectoidField.thetaBDeRhamPlusField (K := ℂ_[l]) l d = 0) :
    pk l k d ∈ IB (fk l k) (xi0 l) := by
  have h1 : d ∈ RingHom.ker (IsPerfectoidField.thetaBDeRhamPlusField (K := ℂ_[l]) l) := hd
  rw [IsPerfectoidField.ker_thetaBDeRhamPlusField, ker_thetaBDeRhamPlus ker_theta0,
    Ideal.mem_span_singleton'] at h1
  obtain ⟨c, rfl⟩ := h1
  rw [map_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

theorem xi_and_sub_mem_I (h : LevHyp l K M) (k : ℕ) :
    (lev h k).lam (algebraMap (Ainf l) (Acris l) (xi0 l)) ∈ (lev h k).I ∧
      ∀ (a : OK l K) (w : Ainf l), theta0 l w = okToOC l K a →
        algebraMap (OK l K) (lev h k).A a - (lev h k).lam (algebraMap (Ainf l) (Acris l) w) ∈ (lev h k).I := by
  refine ⟨?_, fun a w hw => ?_⟩
  · show (lev h k).ι _ ∈ IB (fk l k) (xi0 l)
    rw [ι_lam_ainf]
    exact Ideal.mem_span_singleton_self _
  · show (lev h k).ι _ ∈ IB (fk l k) (xi0 l)
    have e : (lev h k).ι (algebraMap (OK l K) (lev h k).A a) = pk l k (kP l K (a : K)) := rfl
    have e2 : (lev h k).ι ((lev h k).lam (algebraMap (Ainf l) (Acris l) w)) =
        pk l k (wittToBDeRhamPlus (normInteger ℂ_[l]) l w) := ι_lam_ainf h k w
    have e3 : (lev h k).ι (algebraMap (OK l K) (lev h k).A a -
        (lev h k).lam (algebraMap (Ainf l) (Acris l) w)) =
        pk l k (kP l K (a : K) - wittToBDeRhamPlus (normInteger ℂ_[l]) l w) := by
      rw [map_sub, e, e2, map_sub]
    rw [e3]
    apply pk_mem_of_theta
    rw [map_sub, IsPerfectoidField.thetaBDeRhamPlusField_wittToBDeRhamPlus, sub_eq_zero]
    have := thetaAlgHom_algClToBdR l (K.val (a : K))
    rw [thetaAlgHom_apply] at this
    refine this.trans ?_
    show _ = ((theta0 l w : OC l) : ℂ_[l])
    rw [hw]
    rfl

end GlobalTheory.CompanionTheory.LatC.Red
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GlobalTheory.SpreadingModels

namespace GlobalTheory.CompanionTheory.NoethApprox

theorem schemeModels : GlobalTheory.SpreadingModels.SchemeModels := by
  intro R _ Y f h₁ h₂ h₃
  obtain ⟨R₀, i, φ, Y₀, f₀, π, a, b, c, d, e⟩ := GlobalTheory.SpreadScheme.hasModel (V := R) f
  exact ⟨R₀, i, φ, Y₀, f₀, π, a, b, d, c, e⟩

end GlobalTheory.CompanionTheory.NoethApprox
end

section

open PositivityTheory.LowerBoundConstant GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead Topology

theorem _root_.GlobalTheory.T.parahoric_unipotent_times_kernel : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), ∀ g ∈ Gx k e,
    ∃ u ∈ unipRad k e ⊓ KO k (Fin n), ∃ h ∈ KOne k (Fin n), g = u * h := by
  first | exact @GlobalTheory.CompanionTheory.GxSplit.gx_split | exact GlobalTheory.CompanionTheory.GxSplit.gx_split | (intros; apply GlobalTheory.CompanionTheory.GxSplit.gx_split <;> assumption)
end

section

open PositivityTheory.LowerBoundConstant GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead Topology

theorem _root_.GlobalTheory.T.isCompact_parahoric_subgroup : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), IsCompact (Gx k e : Set (GL (Fin n) k)) := by
  first | exact @GlobalTheory.CompanionTheory.MoyPrasad.isCompact_Gx | exact GlobalTheory.CompanionTheory.MoyPrasad.isCompact_Gx | (intros; apply GlobalTheory.CompanionTheory.MoyPrasad.isCompact_Gx <;> assumption)
end

end

section

@[expose] public section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

theorem _root_.GlobalTheory.T.lattice_sub_reduction_mem : ∀ (l : ℕ) [Fact l.Prime] (M k : ℕ), ∀ x ∈ Lat.sub (Lat.fk l (k + 1)) (xi0 l) l M, Lat.dk l k x ∈ Lat.sub (Lat.fk l k) (xi0 l) l M := by
  first | exact @GlobalTheory.CompanionTheory.LatLevel.dk_mem_sub | exact GlobalTheory.CompanionTheory.LatLevel.dk_mem_sub | (intros; apply GlobalTheory.CompanionTheory.LatLevel.dk_mem_sub <;> assumption)

end
end

section

@[expose] public section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

theorem _root_.GlobalTheory.T.level_filtration_span_t_pow : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ (r : ℕ) (t : (per l K).P), (t : (per l K).B) = (per l K).tB → pdP (lev h k).γB r = Ideal.span {(lev h k).toB t ^ r} := by
  first | exact @GlobalTheory.CompanionTheory.LatPdpB.dividedPowerFiltration_lev_eq_span_pow | exact GlobalTheory.CompanionTheory.LatPdpB.dividedPowerFiltration_lev_eq_span_pow | (intros; apply GlobalTheory.CompanionTheory.LatPdpB.dividedPowerFiltration_lev_eq_span_pow <;> assumption)

end
end

section

@[expose] public section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

theorem _root_.GlobalTheory.T.level_galois_isDPMorphism : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ g, IsDPMorphism (lev h k).γ (lev h k).γ ((lev h k).σA g) := by
  first | exact @GlobalTheory.CompanionTheory.LatSigDP.sigA_isDPMorphism | exact GlobalTheory.CompanionTheory.LatSigDP.sigA_isDPMorphism | (intros; apply GlobalTheory.CompanionTheory.LatSigDP.sigA_isDPMorphism <;> assumption)

end
end

section

@[expose] public section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

theorem _root_.GlobalTheory.T.level_iota_algebraMap_integers : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ a : OK l K, (lev h k).ι (algebraMap (OK l K) (lev h k).A a) = algebraMap K (lev h k).B (a : K) := by
  first | exact @GlobalTheory.CompanionTheory.LatC.iota_algebraMap_OK | exact GlobalTheory.CompanionTheory.LatC.iota_algebraMap_OK | (intros; apply GlobalTheory.CompanionTheory.LatC.iota_algebraMap_OK <;> assumption)

end
end

section

@[expose] public section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

theorem _root_.GlobalTheory.T.level_iota_lam_eq_toB : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ (c : (per l K).A) (y : (per l K).P), (y : (per l K).B) = (per l K).i c → (lev h k).ι ((lev h k).lam c) = (lev h k).toB y := by
  first | exact @GlobalTheory.CompanionTheory.LatC.iota_lam_eq_toB | exact GlobalTheory.CompanionTheory.LatC.iota_lam_eq_toB | (intros; apply GlobalTheory.CompanionTheory.LatC.iota_lam_eq_toB <;> assumption)

end
end

section

@[expose] public section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

theorem _root_.GlobalTheory.T.level_system_transition_galois_A : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M), ∀ m g a, (levSys h).dA m (((levSys h).L (m + 1)).σA g a) = ((levSys h).L m).σA g ((levSys h).dA m a) := by
  first | exact @GlobalTheory.CompanionTheory.LatLevel.levSys_dA_σA | exact GlobalTheory.CompanionTheory.LatLevel.levSys_dA_σA | (intros; apply GlobalTheory.CompanionTheory.LatLevel.levSys_dA_σA <;> assumption)

end
end

section

@[expose] public section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

theorem _root_.GlobalTheory.T.level_toB_surjective : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), Function.Surjective (lev h k).toB := by
  first | exact @GlobalTheory.CompanionTheory.LatLevels.toB_surjective | exact GlobalTheory.CompanionTheory.LatLevels.toB_surjective | (intros; apply GlobalTheory.CompanionTheory.LatLevels.toB_surjective <;> assumption)

end
end

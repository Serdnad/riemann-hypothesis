module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle034
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle917
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle902
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle915
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle868
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle507
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1804
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle862
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle500
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle919
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle305
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle246
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle517
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ShintaniUnfoldedIntegrandEvalTorusCell
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle906
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle918
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LamVal

theorem exists_of_pow {A : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] {a : FractionRing A} {n : ℕ}
    (hn : n ≠ 0) (h : a ^ n = 1) : ∃ y : A, algebraMap A (FractionRing A) y = a := by
  have hi : IsIntegral A a := ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hn, by simp [h]⟩
  exact IsIntegrallyClosed.isIntegral_iff.1 hi

variable {D : D7}

theorem e_mem_of_pow {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (b : Bool) {a : FractionRing (D.ntw.O i)} {n : ℕ}
    (hn : n ≠ 0) (h : a ^ n = 1) : ρ.e i b a ∈ (ρ.eOk i b 0).range := by
  obtain ⟨y, rfl⟩ := exists_of_pow hn h
  exact ⟨algebraMap _ _ y, hρ.ek_e i b 0 y⟩

theorem de_mem {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (z : (AE D)ˣ) :
    (((ρ.B i j b).de.chi z : Circle) : ℂ) ∈ (ρ.eOk i b 0).range := by
  obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym z
  have hopen : IsOpen ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker : Set (G D.host.E D.nd.Om)) := by
    have e : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker = (D.ntw.delta i).ker := by
      ext g
      cases b <;> simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]
    rw [e]
    exact D.ntw.delta_open i
  have : Finite (G D.host.E D.nd.Om ⧸ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  have hfi : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hn : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hpow : Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ ^ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.index = 1 := by
    rw [← map_pow]
    exact MonoidHom.mem_ker.1 (Subgroup.pow_index_mem _ σ)
  refine ⟨algebraMap (D.ntw.O i) (D.ntw.Ok i 0)
    (algebraMap (D.ntw.O0 i) (D.ntw.O i) ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)), ?_⟩
  rw [hρ.ek_e, hρ.delta i j b]
  exact (charOf_eq ρ.rc ((ρ.eO i b).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i))) hopen hσ hn hpow).symm

end GlobalTheory.LamVal

namespace GlobalTheory.LamVal

variable {D : D7} {X : RealSide D} {E : IntegralHeckeForms.XD D}

theorem typeCharacterExtension_mem_range_coefficientRing (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (g : G0 (Y.Z.ρ.B i j b).G.Pg (Wc D j).rank) :
    ((ext1 (Y.Z.ρ.B i j b).G.P.H (⇑(Y.Z.ρ.B i j b).G.P.chi) g : ℂˣ) : ℂ) ∈ (Y.Z.ρ.eOk i b 0).range := by
  unfold ext1
  split_ifs with h
  · set g' := (Y.Z.ρ.eG i j b).symm g with hg'
    have hg : Y.Z.ρ.eG i j b g' = g := MulEquiv.apply_symm_apply _ _
    have h' : Y.Z.ρ.eG i j b g' ∈ (Y.Z.ρ.B i j b).G.P.H := by rw [hg]; exact h
    have hu : g' ∈ D.nexp.U := ((Y.Z.tie i j b).U_eq g').1 h'
    have e1 := (Y.Z.tie i j b).psiU_eq ⟨g', hu⟩ h'
    have e2 : (Y.Z.ρ.B i j b).G.P.chi ⟨g, h⟩ = (Y.Z.ρ.B i j b).G.P.chi ⟨Y.Z.ρ.eG i j b g', h'⟩ := by
      congr 1
      exact Subtype.ext hg.symm
    rw [e2, e1]
    have hfin : ((Y.Z.ρ.B i j b).G.P.chi ⟨Y.Z.ρ.eG i j b g', h'⟩) ^ Nat.card (Y.Z.ρ.B i j b).G.P.H = 1 := by
      rw [← map_pow, pow_card_eq_one', map_one]
    refine e_mem_of_pow Y.Z.good i b (n := Nat.card (Y.Z.ρ.B i j b).G.P.H) Nat.card_pos.ne' ?_
    apply (Y.Z.ρ.e i b).injective
    rw [map_pow, ← e1, ← Units.val_pow_eq_pow_val, hfin, Units.val_one, map_one]
  · exact one_mem _

theorem loc_mem (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (PP : Pl D.host.E) (w : (kP PP)ˣ) :
    ((((Y.Z.ρ.B i j b).de.locC PP * (Y.Z.ρ.tw i b 0 ∅ 1).locC PP) w : ℂˣ) : ℂ) ∈ (Y.Z.ρ.eOk i b 0).range := by
  have hψ : (Y.Z.ρ.tw i b 0 ∅ 1).locC PP = 1 := by
    simp [Twist.locC, Setup.tw, twistOf, half_empty]
  rw [hψ, mul_one]
  unfold Twist.locC
  split_ifs with hq
  · have hB := Y.Z.good.base i j b
    obtain ⟨P, -, hQ, hsp⟩ := hB.places.split
    obtain ⟨x, hx⟩ := GlobalTheory.ConjTwist.exists_isLocUnit (hsp.isIdemAt (hQ hq)) w
    show (((Y.Z.ρ.B i j b).de.res PP w : Circle) : ℂ) ∈ _
    rw [← hx.eq (hB.de.res PP hq)]
    exact de_mem Y.Z.good i j b x
  · simp

end GlobalTheory.LamVal

namespace GlobalTheory.LamVal

variable {D : D7} {X : RealSide D} {E : IntegralHeckeForms.XD D}

theorem de_frac {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (z : (AE D)ˣ) :
    ∃ d, ρ.e i b d = (((ρ.B i j b).de.chi z : Circle) : ℂ) := by
  obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym z
  have hopen : IsOpen ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker : Set (G D.host.E D.nd.Om)) := by
    have e : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker = (D.ntw.delta i).ker := by
      ext g
      cases b <;> simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]
    rw [e]
    exact D.ntw.delta_open i
  have : Finite (G D.host.E D.nd.Om ⧸ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  have hfi : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hn : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hpow : Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ ^ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.index = 1 := by
    rw [← map_pow]
    exact MonoidHom.mem_ker.1 (Subgroup.pow_index_mem _ σ)
  refine ⟨algebraMap (D.ntw.O i) _
    (algebraMap (D.ntw.O0 i) (D.ntw.O i) ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)), ?_⟩
  rw [hρ.delta i j b]
  exact (charOf_eq ρ.rc ((ρ.eO i b).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i))) hopen hσ hn hpow).symm

theorem baseCharacter_finiteIdeles_mem_range_fractionRing (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (x : (AE D)ˣ) (hx : infPart D (x : AE D) = 1) :
    ∃ a, Y.Z.ρ.e i b a = (((Y.Z.ρ.B i j b).mu0 x : Circle) : ℂ) := by
  obtain ⟨y, hy⟩ := X.valKs j x hx
  refine ⟨sideEmb D.ntw i b (Y.S.kKs ((Y.YS.fi j).eK.symm y)), ?_⟩
  rw [Y.Z.good.e_LL0, Y.Z.pin.mu0 i j b]
  refine Eq.trans ?_ hy.symm
  change D.what₂.embLL ((Y.S.kKs ((Y.YS.fi j).eK.symm y) : D.LL0) : D.what₂.LL) = _
  rw [Y.S.kKs_spec, ← (Y.YS.fi j).eK_LL, RingEquiv.apply_symm_apply]

theorem muC_mem (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    {PP : Pl D.host.E} (hPP : PP ∈ (Y.Z.ρ.B i j b).G.Pg) (w : (kP PP)ˣ) :
    (((Y.Z.ρ.B i j b).G.muC PP w : ℂˣ) : ℂ) ∈ (Y.Z.ρ.eOk i b 0).range := by
  have hB := Y.Z.good.base i j b
  obtain ⟨P, hPg, -, hsp⟩ := hB.places.split
  obtain ⟨x, hx⟩ := GlobalTheory.ConjTwist.exists_isLocUnit (hsp.isIdemAt (hPg hPP)) w
  have e1 : (Y.Z.ρ.B i j b).G.mu PP w = (Y.Z.ρ.B i j b).mu x := (hx.eq (hB.tame PP hPP)).symm
  show (((Y.Z.ρ.B i j b).G.mu PP w : Circle) : ℂ) ∈ _
  obtain ⟨a, ha⟩ := baseCharacter_finiteIdeles_mem_range_fractionRing Y i j b x hx.inf
  obtain ⟨d, hd⟩ := de_frac Y.Z.good i j b x
  have e2 : (((Y.Z.ρ.B i j b).G.mu PP w : Circle) : ℂ) = Y.Z.ρ.e i b (a * d) := by
    rw [e1, Base.mu, MonoidHom.mul_apply, Circle.coe_mul, map_mul, ha, hd]
  haveI : Finite (kP PP)ˣ := inferInstance
  have hfin : ((Y.Z.ρ.B i j b).G.mu PP w) ^ Nat.card (kP PP)ˣ = 1 := by
    rw [← map_pow, pow_card_eq_one', map_one]
  rw [e2]
  refine e_mem_of_pow Y.Z.good i b (n := Nat.card (kP PP)ˣ) Nat.card_pos.ne' ?_
  apply (Y.Z.ρ.e i b).injective
  rw [map_pow, ← e2, ← Circle.coe_pow, hfin, Circle.coe_one, map_one]

theorem levLam_mem_coef : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (k : (Y.Z.ρ.B i j b).levJ (Y.Z.ρ.tw i b 0 ∅ 1)),
    (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) ∈ (Y.Z.ρ.eOk i b 0).range := by
  intro D X E Y i j b k
  rw [GlobalTheory.MtLatConj.levelCharacter_apply_eq_levelFunction_swap]
  simp only [levFn, Base.levS, Units.val_mul, Units.coe_prod]
  exact mul_mem (mul_mem (typeCharacterExtension_mem_range_coefficientRing Y i j b _) (prod_mem fun PP hPP => prod_mem fun _ _ => muC_mem Y i j b hPP _))
    (prod_mem fun PP _ => loc_mem Y i j b PP _)

end GlobalTheory.LamVal
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.Lev Formalism.L2.DIV Formalism.IndefR.Mult
open scoped TensorProduct




namespace GlobalTheory.SeriesTie.HkRat

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {Rl : RealDat3 D A3 Ks}
  {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)

theorem evK_hkFR {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (hL : ℕ → PlE D.host → Module.End D.what₂.LL (S.WL ((j : ℕ) + 1)))
    (hs : NX.HeckeStabR S ((j : ℕ) + 1) hL) (k : ℕ) (P : PlE D.host) (R : Finset (GA D (Wc D j))) (s : ℂ)
    (hR : ∀ x : S.WL ((j : ℕ) + 1), evW YS v₀ j (hL k P x) = s • heckeLin (Wc D j) R (evW YS v₀ j x))
    (y : NX.Fm S i ((j : ℕ) + 1) b) :
    evK YS v₀ hρ i j b (NX.hkFR S i ((j : ℕ) + 1) b hL hs k P y) = s • heckeLin (Wc D j) R (evK YS v₀ hρ i j b y) := by
  induction y using TensorProduct.induction_on with
  | zero => erw [LinearMap.map_zero, map_zero, map_zero, smul_zero]
  | add y z hy hz => erw [LinearMap.map_add, map_add, hy, hz, map_add, map_add, smul_add]
  | tmul a f0 =>
    have e1 : NX.hkFR S i ((j : ℕ) + 1) b hL hs k P (a ⊗ₜ f0) =
        a ⊗ₜ (((hL k P).restrictScalars S.Ks).restrict (p := (S.A ((j : ℕ) + 1)).WK) (q := (S.A ((j : ℕ) + 1)).WK)
          fun x hx => hs k P x hx) f0 := rfl
    erw [e1, evK_tmul, evK_tmul]
    change ρ.e i b a • evW YS v₀ j (hL k P f0.1) = _
    rw [hR, map_smul, smul_comm]

end GlobalTheory.SeriesTie.HkRat

namespace GlobalTheory.SeriesTie.HkRat

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {Rl : RealDat3 D A3 Ks}
  {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)

theorem evW_reads (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (hR : GlobalTheory.ExportPin.Reads Rl cG S YS hL)
    (j : Fin D.R.m) (k : ℕ) (P : PlE D.host) (hPs : IsSplitPl D.host P)
    (hso : Bridge.SplitOff P (Rl.Sb : Set (Pl D.host.E))) (hk : k ≤ D.R.r) (α : GA D (Wc D j)) (R : Finset (GA D (Wc D j)))
    (hα : IsHeckeAt (Wc D j) P k α) (hdc : Bridge.IsDC (levG (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv)) α R)
    (x : S.WL ((j : ℕ) + 1)) :
    evW YS v₀ j (hL ((j : ℕ) + 1) k P x) =
      ((((Rl.C.mu0 j).val P : ℂˣ) : ℂ)⁻¹ ^ k * (((Nat.card (kP P) : ℕ) : ℂ) ^ (k * (D.R.nV / 2)))⁻¹) •
        heckeLin (Wc D j) R (evW YS v₀ j x) := by
  have h := congrArg (fun F => F (v₀ j (sg0 D A3.A))) (hR j k P hPs hso hk α R hα hdc x)
  exact h

end GlobalTheory.SeriesTie.HkRat

namespace GlobalTheory.SeriesTie.HkRat
open GlobalTheory.SeriesTie.Setup

theorem ratHecke_realRd : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (ρ : Setup D.ntw) (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (ν : ℂ), RealPin Rl cG ρ → ChrEq (Rl.mu0 ((j : ℕ) + 1)) (Rl.C.mu0 j) → (∀ P, IsSplitPl D.host P → P ∉ D.ntw.S0 i → Bridge.SplitOff P (Rl.Sb : Set (Pl D.host.E))) → ∀ hL : ∀ n, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL n), NX.HeckeStabR S ((j : ℕ) + 1) (hL ((j : ℕ) + 1)) → GlobalTheory.ExportPin.Reads Rl cG S YS hL → RatHecke (realRd YS v₀ hρ i j b ν) := by
  intro D Γ _ _ Pl0 I0 T A3 Ks _ _ _ Rl cG S YS v₀ ρ hρ i j b ν hp hchr hsplit hL hs hR k P hk f
  obtain ⟨hk1, hkr, hPs, hPS0⟩ := hk
  have hso := hsplit P hPs hPS0
  have hPg : Bridge.SplitOff P (((ρ.B i j b).G.Pg : Finset _) : Set (Pl D.host.E)) :=
    GlobalTheory.T.split_off_outside_S0 hρ i _ (fun P' hP' => by
      obtain ⟨k', hk'⟩ := hρ.Pg i j b P' hP'
      exact D.ntw.placesOver_subset_exceptional i k' hk') P hPs hPS0
  have hdQ : Bridge.SplitOff P (((ρ.B i j b).de.Q : Finset _) : Set (Pl D.host.E)) :=
    GlobalTheory.T.split_off_outside_S0 hρ i _ (fun P' hP' => by
      rw [hρ.delta i j b] at hP'
      exact D.ntw.primes_subset_exceptional i (mem_half.1 hP').1) P hPs hPS0
  by_cases hd : ∃ α R z, ρ.IsHeckeDatum i j b k P α R z
  swap
  · exact ⟨0, fun α R z d => absurd ⟨α, R, z, d⟩ hd⟩
  obtain ⟨α₀, R₀, z₀, d₀⟩ := hd
  obtain ⟨a, ha⟩ := GlobalTheory.T.twisting_char_values_mem_coeff_field_range hρ i j b z₀
  have hde : ∀ α R z, ρ.IsHeckeDatum i j b k P α R z → (((ρ.B i j b).de.chi z : Circle) : ℂ) = ρ.e i b a :=
    fun α R z d => by
      rw [ha, GlobalTheory.T.heckeCharacter_value_at_splitPlace_determinant _ _ _ _ P k α z (hp.delta i j b) (hρ.base i j b).de.unram (hρ.base i j b).de.split hdQ d.elt d.det,
        GlobalTheory.T.heckeCharacter_value_at_splitPlace_determinant _ _ _ _ P k α₀ z₀ (hp.delta i j b) (hρ.base i j b).de.unram (hρ.base i j b).de.split hdQ d₀.elt d₀.det]
  have hchr' : ChrEq (ρ.B i j b).mu0 (Rl.C.mu0 j) := by rw [hp.mu0 i j b]; exact hchr
  have hmu0 : ∀ α R z, ρ.IsHeckeDatum i j b k P α R z →
      (((ρ.B i j b).mu0 z : Circle) : ℂ) = (((Rl.C.mu0 j).val P : ℂˣ) : ℂ) ^ k :=
    fun α R z d => GlobalTheory.T.heckeCharacter_value_at_splitPlace_determinant _ _ _ _ P k α z hchr' (hρ.base i j b).unram
      ((hρ.base i j b).places.split.elim fun _ h => h.2.2.mono h.1) hPg d.elt d.det
  refine ⟨a⁻¹ • (YS.eF i _ b (Nat.le_add_left _ _) j.2).symm
    (NX.hkFR S i ((j : ℕ) + 1) b (hL _) hs k P (YS.eF i _ b (Nat.le_add_left _ _) j.2 f)), ?_⟩
  rcases eq_or_ne ν 0 with rfl | hν
  · intro α R z d
    rw [realRd_apply, realRd_apply YS v₀ hρ i j b 0 f, inv_zero, zero_smul, zero_smul, map_zero]
  rw [heckeAt_realRd YS v₀ hρ i j b hν]
  intro α R z d
  have hdc := d.reps
  rw [GlobalTheory.T.complex_principal_level_eq_realisation_principal_level Rl hp i j b] at hdc
  have key := evK_hkFR YS v₀ hρ i j b (hL _) hs k P R _
    (evW_reads YS v₀ hL hR j k P hPs hso hkr α R d.elt hdc) (YS.eF i _ b (Nat.le_add_left _ _) j.2 f)
  funext x
  rw [Setup.hecke_apply, map_smulₛₗ]
  change ρ.e i b a⁻¹ * ((1 : ℂ)⁻¹ • evK YS v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2
    ((YS.eF i _ b (Nat.le_add_left _ _) j.2).symm _))) x = _ * _ *
      ∑ γ ∈ R, ((1 : ℂ)⁻¹ • evK YS v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 f)) (x * γ)
  rw [LinearEquiv.apply_symm_apply, key]
  simp only [inv_one, one_smul, Pi.smul_apply, smul_eq_mul, heckeLin, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Base.mu, MonoidHom.mul_apply, Circle.coe_mul, hmu0 α R z d, hde α R z d, map_inv₀]
  rw [show normV P = Nat.card (kP P) from rfl, D.sp.V_rank _ (Nat.le_add_left _ _) j.2]
  simp only [one_mul]
  ring

end GlobalTheory.SeriesTie.HkRat
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical




noncomputable section

namespace GlobalTheory.TwoStepModel

open GlobalTheory.ExportSeries

theorem datum_eq_tensorHalf {D : D7} {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    {Pg Q : Finset (Pl D.host.E)} {eg eQ : AE D} (hg : IsIdemSum eg Pg) (hq : IsIdemSum eQ Q) (hd : Disjoint Pg Q)
    (he : IsIdemSum (eg + eQ) (Pg ∪ Q)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) :
    (fun x => if IsHalf (cA D (eg + eQ)) x ∧ IsIntM (frMapAdj S T βS βT x) then
        omegaK Pg (fun PP => redM PP (frMapAdj S T βS βT x)) *
          omegaQ Q T.rank ξ (-1) (fun PP => redM PP (frMapAdj S T βS βT x)) else 0) =
      tensorHalf (cA D eQ) (cA D eg)
        (fun x => if IsHalf (cA D eg) x ∧ IsIntM (frMapAdj S T βS βT x) then
          omegaK Pg (fun PP => redM PP (frMapAdj S T βS βT x)) else 0)
        (fun x => if IsHalf (cA D eQ) x ∧ IsIntM (frMapAdj S T βS βT x) then
          omegaQ Q T.rank ξ (-1) (fun PP => redM PP (frMapAdj S T βS βT x)) else 0) := by
  have hA := GlobalTheory.T.adjointFrame_integral_iff_parts_conj_half D S T βS βT Pg Q eg eQ hg hq hd he
  have hB := GlobalTheory.T.reduction_adjointFrame_conj_half_two_parts D S T βS βT Pg Q eg eQ hg hq hd he
  have heg := GlobalTheory.PlaceVec.idemSum_mul_self hg
  have heQ := GlobalTheory.PlaceVec.idemSum_mul_self hq
  have hcg : ∀ x : WO S T, IsHalf (cA D eg) (cA D eg • x) :=
    fun x => GlobalTheory.ExportSeries.RestrictHalfModel.isHalf_smul (by rw [← map_mul, heg]) x
  have hcQ : ∀ x : WO S T, IsHalf (cA D eQ) (cA D eQ • x) :=
    fun x => GlobalTheory.ExportSeries.RestrictHalfModel.isHalf_smul (by rw [← map_mul, heQ]) x
  funext x
  rw [tensorHalf_apply]
  have hc : cA D (eg + eQ) = cA D eQ + cA D eg := by rw [map_add (f := _), add_comm]
  by_cases hx : IsHalf (cA D (eg + eQ)) x
  · have hx' : IsHalf (cA D eQ + cA D eg) x := hc ▸ hx
    rw [if_pos hx', mul_one]
    by_cases hi : IsIntM (frMapAdj S T βS βT x)
    · obtain ⟨i1, i2⟩ := (hA x hx).1 hi
      obtain ⟨r1, r2⟩ := hB x hx hi
      have c1 : IsHalf (cA D (eg + eQ)) x ∧ IsIntM (frMapAdj S T βS βT x) := ⟨hx, hi⟩
      have c2 : IsHalf (cA D eQ) (cA D eQ • x) ∧ IsIntM (frMapAdj S T βS βT (cA D eQ • x)) := ⟨hcQ x, i2⟩
      have c3 : IsHalf (cA D eg) (cA D eg • x) ∧ IsIntM (frMapAdj S T βS βT (cA D eg • x)) := ⟨hcg x, i1⟩
      rw [if_pos c1, if_pos c2, if_pos c3, mul_comm]
      congr 1
      · exact GlobalTheory.PlaceVec.omegaQ_congr Q _ ξ _ fun PP hPP => (r2 PP hPP).symm
      · exact GlobalTheory.PlaceVec.omegaK_congr Pg fun PP hPP => (r1 PP hPP).symm
    · have c1 : ¬ (IsHalf (cA D (eg + eQ)) x ∧ IsIntM (frMapAdj S T βS βT x)) := fun h => hi h.2
      rw [if_neg c1]
      have := mt (hA x hx).2 hi
      rcases not_and_or.1 this with h | h
      · have c3 : ¬ (IsHalf (cA D eg) (cA D eg • x) ∧ IsIntM (frMapAdj S T βS βT (cA D eg • x))) := fun h' => h h'.2
        rw [if_neg c3, mul_zero]
      · have c2 : ¬ (IsHalf (cA D eQ) (cA D eQ • x) ∧ IsIntM (frMapAdj S T βS βT (cA D eQ • x))) := fun h' => h h'.2
        rw [if_neg c2, zero_mul]
  · have c1 : ¬ (IsHalf (cA D (eg + eQ)) x ∧ IsIntM (frMapAdj S T βS βT x)) := fun h => hx h.1
    have hx' : ¬ IsHalf (cA D eQ + cA D eg) x := hc ▸ hx
    rw [if_neg c1, if_neg hx', mul_zero]

end GlobalTheory.TwoStepModel

namespace GlobalTheory.ConjTwist

theorem isThetaAt_vP_twoStep : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0) (eg eQ : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg → IsIdemSum eQ (R.Q t) → IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D eg) (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 (R.vacP i) (fun x => if IsHalf (cA D eg) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then omegaK R.Pg (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0) fg → IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D eQ) (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 fg (fun x => if IsHalf (cA D eQ) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then omegaQ (R.Q t) (Wc D i).rank (R.xiR t) (-1) (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0) (R.vP i t) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC _hG i t eg eQ fg hg hq hfg
  obtain ⟨⟨hψ, -⟩, e, he, hTe⟩ := hC.thP.vP i t
  have hSV := GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βV i))
  have hSW := GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βW i))
  have hd := GlobalTheory.TwistPlaces.typePlaces_disjoint_twistPlaces R F hC t
  have hsum : e = eg + eQ := by
    rw [← GlobalTheory.ExportSeries.idem_eq he, ← GlobalTheory.ExportSeries.idem_eq hg, ← GlobalTheory.ExportSeries.idem_eq hq]
    exact Finset.sum_union hd
  subst hsum
  have heg := GlobalTheory.PlaceVec.idemSum_mul_self hg
  have heQ := GlobalTheory.PlaceVec.idemSum_mul_self hq
  have hee := GlobalTheory.PlaceVec.idemSum_mul_self he
  have hgQ : eg * eQ = 0 := by
    refine GlobalTheory.PlaceVec.natCast_mul_eq_zero 2 _ two_pos ?_
    push_cast
    linear_combination hee - heg - heQ
  have hcg : cA D eg * cA D eg = cA D eg := by rw [← map_mul, heg]
  have hcQ : cA D eQ * cA D eQ = cA D eQ := by rw [← map_mul, heQ]
  have hQg : cA D eQ * cA D eg = 0 := by rw [← map_mul, mul_comm, hgQ, map_zero]
  have hgQ' : cA D eg * cA D eQ = 0 := by rw [mul_comm, hQg]
  have hΛ : ∀ a : AE D, a * a = a → ∀ u ∈ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True),
      a • u ∈ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) :=
    fun a ha u hu => GlobalTheory.PlaceModelSum.idem_smul_latO ha hu
  have hinfg : infPart D (cA D eg) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart hg)
  have hinfQ : infPart D (cA D eQ) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart hq)
  have hSBg := GlobalTheory.PlaceVec.isSBHalf_of_red (GlobalTheory.PlaceVec.selfDual_isFullLattice _ _ hSV) (GlobalTheory.PlaceVec.selfDual_isFullLattice _ _ hSW) hinfg (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i))
    (GlobalTheory.PlaceVec.frMapAdj_add _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_up _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_down _ _ _ _)
    R.Pg (fun y => omegaK R.Pg y) fun y y' h => GlobalTheory.PlaceVec.omegaK_congr R.Pg h
  have hSBQ := GlobalTheory.PlaceVec.isSBHalf_of_red (GlobalTheory.PlaceVec.selfDual_isFullLattice _ _ hSV) (GlobalTheory.PlaceVec.selfDual_isFullLattice _ _ hSW) hinfQ (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i))
    (GlobalTheory.PlaceVec.frMapAdj_add _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_up _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_down _ _ _ _)
    (R.Q t) (fun y => omegaQ (R.Q t) (Wc D i).rank (R.xiR t) (-1) y) fun y y' h => GlobalTheory.PlaceVec.omegaQ_congr _ _ _ _ h
  obtain ⟨⟨Te, hTe1⟩, hTe2⟩ := hTe
  have hc : cA D (eg + eQ) = cA D eQ + cA D eg := by rw [map_add (f := _), add_comm]
  have hc' : cA D (eg + eQ) = cA D eg + cA D eQ := map_add _ _ _
  have hm1 := GlobalTheory.TwoStepModel.isPlaceModel_comp_tensorHalf hcQ hcg hQg hΛ hSBg (hc ▸ hTe1)
  have hm2 := GlobalTheory.ExportSeries.isPlaceModel_comp_restrictHalf hcg hcQ hgQ' hΛ (hc' ▸ hTe1)
  have hbase := hfg.2 _ hm2
  simp only [LinearMap.comp_apply] at hbase
  rw [← hbase] at hm1
  refine ⟨⟨_, hm1⟩, fun T' hT' => ?_⟩
  rw [hTe2 Te hTe1, GlobalTheory.TwoStepModel.datum_eq_tensorHalf (R.βV i) (R.βW i) hg hq hd he (R.xiR t)]
  exact GlobalTheory.PlaceVec.placeModel_unique hψ hSV hSW hcQ hinfQ hm1 hT' hSBQ

end GlobalTheory.ConjTwist

end
end

section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

theorem _root_.GlobalTheory.T.shintani_unfoldedIntegrand_eval_torusCell : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))),
    (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) →
    ∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (b : GA E (m + 1) → ℂ) (α α' : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ) (φ φ' : GA E (m + 1) → ℂ)
      (N : ℕ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (Φ : (Fin (m + 1) → Cinf E) → ℂ),
    (∀ v ∈ S, 0 < FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)) →
    (∀ z ∈ GlobalTheory.RSJ.natLat E N, ∀ v : HeightOneSpectrum (𝓞 E), z v ∈ v.adicCompletionIntegers E) →
    (∀ z ∈ GlobalTheory.RSJ.natLat E N, ∀ v ∈ S,
        Valued.v (z v) ≤ WithZero.exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E))) →
    (∀ z z' : Af E, (∀ v ∈ S, z v = z' v) → (∀ v ∉ S, z v ∈ v.adicCompletionIntegers E) →
        (∀ v ∉ S, z' v ∈ v.adicCompletionIntegers E) → (z ∈ GlobalTheory.RSJ.natLat E N ↔ z' ∈ GlobalTheory.RSJ.natLat E N)) →
    tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) →
    (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, GlobalTheory.JSW.whit φ (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ g) →
    (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, GlobalTheory.JSW.whit φ' (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ' g) →
    (∀ κ ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J, ∀ g, GlobalTheory.JSW.whit φ (g * finGL E (m + 1) κ) = GlobalTheory.JSW.whit φ g) →
    (∀ κ ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J, ∀ g, GlobalTheory.JSW.whit φ' (g * finGL E (m + 1) κ) = GlobalTheory.JSW.whit φ' g) →
    (∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) → ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m),
      GlobalTheory.JSW.whit φ (p * GlobalTheory.JSW.tl ϖ l) = b p * ∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (l w)) →
    (∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) → ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m),
      GlobalTheory.JSW.whit φ' (p * GlobalTheory.JSW.tl ϖ l) = b p * ∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α' w i : ℂ)) (l w)) →
    ∀ x : ℝ, ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) S,
      GlobalTheory.ZEul.uInt φ φ' Φ N 0 g = GlobalTheory.ZEul.uInt φ φ Φ N 0 g ∧ GlobalTheory.ZEul.uInt φ' φ' Φ N 0 g = GlobalTheory.ZEul.uInt φ φ Φ N 0 g ∧
      ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) S,
        (GlobalTheory.CellDec.dinv (m + 1) l.1 : ℂ) * GlobalTheory.ZEul.uInt φ φ' Φ N x (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) =
          (l.1.prod fun w v => GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.asIdeal) (fun i => (α w i : ℂ)) (fun i => (α' w i : ℂ)) x v) *
            GlobalTheory.ZEul.uInt φ φ Φ N 0 g * (GlobalTheory.RSJ.detPow E (m + 1) x g : ℂ) := by
  first
  | exact @GlobalTheory.ZEul.uInt_cell_eval
  | exact GlobalTheory.ZEul.uInt_cell_eval
  | (intros; apply GlobalTheory.ZEul.uInt_cell_eval <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie
open scoped TensorProduct

theorem _root_.GlobalTheory.T.supLatticeRationalForm_mem_localUnitBall : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m) (T0 : CoreJ D) [Algebra T0.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T0.Q.c.F) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (fw : FWTie T0 Rl.toRealDat κ v₀) (i : D.ntw.Tw) (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]), (∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range) → ∀ (b : Bool) (j : Fin D.R.m), ∀ f : NX.FmK S ((j : ℕ) + 1), (show ↥(S.A ((j : ℕ) + 1)).WK from f).1 ∈ (S.A ((j : ℕ) + 1)).MK → f ∈ locBall YS fw iC b j := by
  first | exact @GlobalTheory.GeoTie.mem_locBall_of_mem_MK | exact GlobalTheory.GeoTie.mem_locBall_of_mem_MK | (intros; apply GlobalTheory.GeoTie.mem_locBall_of_mem_MK <;> assumption)
end

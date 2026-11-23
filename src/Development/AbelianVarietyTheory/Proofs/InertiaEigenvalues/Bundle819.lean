module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterAtDetRootCongOneOddEqOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle325
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle326
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle055
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle105
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle450
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle449
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle288
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle205
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle025

@[expose] public section

section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AntiCycRead

variable (D : D7)

def quo : (AE D)ˣ →* (Af D.host.F ⊗[D.host.F] D.host.E)ˣ :=
  MonoidHom.mk' (fun x => Units.map (finPart D).toMonoidHom x *
      (Units.map ((finPart D).comp (sigR (AF D.host.F) D.sp.cm.sig)).toMonoidHom x)⁻¹)
    (fun x y => by simp only [map_mul, mul_inv]; exact mul_mul_mul_comm _ _ _ _)

theorem quo_mul (x : (AE D)ˣ) :
    ((quo D x : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) *
        sigR (Af D.host.F) D.sp.cm.sig (finPart D (x : AE D)) = finPart D (x : AE D) := by
  have hsv : ((Units.map ((finPart D).comp (sigR (AF D.host.F) D.sp.cm.sig)).toMonoidHom x :
      (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) =
      sigR (Af D.host.F) D.sp.cm.sig (finPart D (x : AE D)) := GlobalTheory.DetRootChar.finPart_sigR D x
  rw [← hsv]
  show ((Units.map (finPart D).toMonoidHom x * (Units.map ((finPart D).comp (sigR (AF D.host.F) D.sp.cm.sig)).toMonoidHom x)⁻¹ :
      (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) * _ = _
  rw [← Units.val_mul, inv_mul_cancel_right]
  rfl

theorem quo_eq_of (x : (AE D)ˣ) (u : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ)
    (hu : (u : Af D.host.F ⊗[D.host.F] D.host.E) * sigR (Af D.host.F) D.sp.cm.sig (finPart D (x : AE D)) =
      finPart D (x : AE D)) : quo D x = u := by
  set s : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ :=
    Units.map ((finPart D).comp (sigR (AF D.host.F) D.sp.cm.sig)).toMonoidHom x with hs
  have hsv : (s : Af D.host.F ⊗[D.host.F] D.host.E) = sigR (Af D.host.F) D.sp.cm.sig (finPart D (x : AE D)) := by
    rw [hs]; exact GlobalTheory.DetRootChar.finPart_sigR D x
  have h1 := quo_mul D x
  rw [← hsv] at h1 hu
  have : ((quo D x * s : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ)) = u * s := Units.ext (by simp [h1, hu])
  exact mul_right_cancel this

theorem ker_trivial (δ : (AE D)ˣ →* Circle) (hF : ∀ a, δ (idF D a) = 1) (hfin : ∃ m : ℕ, 0 < m ∧ ∀ x, δ x ^ m = 1)
    (x : (AE D)ˣ) (hx : quo D x = 1) : δ x = 1 := by
  have h1 := quo_mul D x
  rw [hx, Units.val_one, one_mul] at h1
  obtain ⟨a, y, hy, hxy⟩ := GlobalTheory.DetRootChar.exists_idF_mul D x h1
  obtain ⟨m, hm, hδ⟩ := hfin
  obtain ⟨z, hz⟩ := GlobalTheory.IdeleDiv.exists_pow_eq_of_finPart_eq_one D m hm y hy
  rw [hxy, map_mul, hF, mul_one, ← hz, map_pow, hδ]

theorem quo_of_isDetRoot (W : HSp D) (g : GA D W) (x : (AE D)ˣ) (hx : IsDetRoot W g x) :
    quo D x = Matrix.GeneralLinearGroup.det (finHom W g) := by
  apply quo_eq_of
  have hdet : ((Matrix.GeneralLinearGroup.det (finHom W g) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) :
      Af D.host.F ⊗[D.host.F] D.host.E) = finPart D (matHom W g).1.det :=
    (GlobalTheory.DetRootChar.finPart_det D W g).symm
  rw [hdet, ← GlobalTheory.DetRootChar.finPart_sigR, ← RingHom.map_mul]
  exact (congrArg _ hx).symm

end GlobalTheory.AntiCycRead

end

noncomputable section

namespace GlobalTheory.AntiCycRead

variable (D : D7)

theorem val_of_quo (χ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* Circle) (Y : (AE D)ˣ) :
    (((Circle.toUnits.comp χ) (quo D Y) : ℂˣ) : ℂ) = ((χ (quo D Y) : Circle) : ℂ) := by
  simp

theorem exists_rat (x : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) (a : D.host.E)
    (hxa : (x : Af D.host.F ⊗[D.host.F] D.host.E) = 1 ⊗ₜ a) (hx : GlobalTheory.FinalJoin.NormOne x)
    [Nontrivial (Af D.host.F)] : ∃ w : D.host.Eˣ, quo D (Units.map (incA D).toMonoidHom w) = x := by
  have hN : (x : Af D.host.F ⊗[D.host.F] D.host.E) *
      sigR (Af D.host.F) D.sp.cm.sig (x : Af D.host.F ⊗[D.host.F] D.host.E) = 1 := hx
  rw [hxa] at hN
  have ha : a * D.sp.cm.sig a = 1 := by
    apply Algebra.TensorProduct.includeRight_injective (A := Af D.host.F) (R := D.host.F)
      (algebraMap D.host.F (Af D.host.F)).injective
    show (1 : Af D.host.F) ⊗ₜ[D.host.F] (a * D.sp.cm.sig a) = (1 : Af D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)
    rw [← Algebra.TensorProduct.one_def]
    simpa [sigR] using hN
  have hu : a ∈ unitary D.host.E := ⟨by rw [mul_comm]; exact ha, ha⟩
  obtain ⟨w, hw0, hw⟩ := GlobalTheory.NormOneHilbert90Units.exists_ne_zero_mul_conj_eq_of_unitary D ⟨a, hu⟩
  refine ⟨Units.mk0 w hw0, ?_⟩
  apply quo_eq_of
  have hfY : finPart D ((Units.map (incA D).toMonoidHom (Units.mk0 w hw0) : (AE D)ˣ) : AE D) =
      (1 : Af D.host.F) ⊗ₜ[D.host.F] w := rfl
  rw [hfY, hxa]
  simp only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [← Formalism.BasicNotions.Examples₂.star_eq_conj] at hw
  exact congrArg _ hw

theorem exists_cong (N : ℕ) (hN : Odd N) (x : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) (hx : GlobalTheory.FinalJoin.NormOne x)
    (w : Af D.host.F ⊗[D.host.F] D.host.E) (hw : w ∈ intAE D)
    (hwe : (x : Af D.host.F ⊗[D.host.F] D.host.E) - 1 = N • w) :
    ∃ Y : (AE D)ˣ, FinUnit Y ∧ (∃ y ∈ intAE D, finPart D (Y : AE D) - 1 = N • y) ∧ quo D Y = x := by
  have hn : (x : Af D.host.F ⊗[D.host.F] D.host.E) *
      sigR (Af D.host.F) D.sp.cm.sig (x : Af D.host.F ⊗[D.host.F] D.host.E) = 1 := hx
  obtain ⟨y, y', hy, hy', hyy, hroot, q, hq, hqe⟩ :=
    GlobalTheory.T.exists_normOne_root_congruent_odd_hostField D N hN (x : Af D.host.F ⊗[D.host.F] D.host.E) w hw hwe hn
  obtain ⟨Y, h1, h2, h3⟩ := GlobalTheory.DetRootCong.exists_idele D y y' hyy
  refine ⟨Y, ⟨h1, h2 ▸ hy, h3 ▸ hy'⟩, ⟨q, hq, h2 ▸ hqe⟩, ?_⟩
  apply quo_eq_of
  rw [h2]
  exact hroot.symm

theorem exists_normOne (x : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) (hx : GlobalTheory.FinalJoin.NormOne x) :
    ∃ Y : (AE D)ˣ, quo D Y = x := by
  obtain ⟨y, hy⟩ := (GlobalTheory.IdeleNinety.finiteIdeles_normOne_eq_div_conj_with_congruence D).1 x hx
  obtain ⟨Y, -, h1, -⟩ := GlobalTheory.DetRootCong.exists_idele D (y : Af D.host.F ⊗[D.host.F] D.host.E)
    ((y⁻¹ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : _) y.mul_inv
  have hc : ((Formalism.L2.Pj.cjFin D y : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) =
      sigR (Af D.host.F) D.sp.cm.sig (y : Af D.host.F ⊗[D.host.F] D.host.E) :=
    GlobalTheory.IdeleNinety.coe_cjFin D y
  refine ⟨Y, ?_⟩
  apply quo_eq_of
  rw [h1, ← hc, hy, ← Units.val_mul, div_mul_cancel]

end GlobalTheory.AntiCycRead

end

noncomputable section

namespace GlobalTheory.AntiCycRead

theorem read_anticyc : ∀ (D : D7) (W : HSp D) (L : Type) [Field L] (σ : L →+* ℂ) (p : ℕ), Odd p → ∀ δ : (AE D)ˣ →* Circle, IsHeckeChar D δ → (∀ a, δ (Formalism.L2.Theta.idF D a) = 1) → (∃ m : ℕ, 0 < m ∧ ∀ x, δ x ^ m = 1) → (∀ x, FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = p • y) → δ x = 1) → (∀ x, ∃ y : L, σ y = ((δ x : Circle) : ℂ)) → ∃ xi : (GlobalTheory.FinalJoin.AfE D)ˣ →* ℂˣ, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsTwist σ p xi ∧ ∀ (g : GA D W) (x : (AE D)ˣ), IsDetRoot W g x → ((xi (Matrix.GeneralLinearGroup.det (finHom W g)) : ℂˣ) : ℂ) = ((δ x : Circle) : ℂ) := by
  intro D W L _ σ p hp δ hH hF hfin hcong hval
  obtain ⟨χ, hχ⟩ := GlobalTheory.DetRootChar.circle_hom_factor (quo D) δ (ker_trivial D δ hF hfin)
  have hxi : ∀ Y : (AE D)ˣ, (((Circle.toUnits.comp χ) (quo D Y) : ℂˣ) : ℂ) = ((δ Y : Circle) : ℂ) := by
    intro Y
    rw [val_of_quo, hχ]
  refine ⟨Circle.toUnits.comp χ, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro x a hxa hx
    rcases subsingleton_or_nontrivial (Af D.host.F) with hs | hs
    · have h0 : ∀ z : Af D.host.F ⊗[D.host.F] D.host.E, z = 0 := by
        intro z
        induction z using TensorProduct.induction_on with
        | zero => rfl
        | tmul b e => rw [Subsingleton.elim b 0, TensorProduct.zero_tmul]
        | add u v hu hv => rw [hu, hv, add_zero]
      have hx1 : x = 1 := Units.ext ((h0 _).trans (h0 _).symm)
      rw [hx1, map_one]
    obtain ⟨w, hw⟩ := exists_rat D x a hxa hx
    apply Units.ext
    rw [← hw, hxi, hH.2 w]
    rfl
  · rintro x hx ⟨w, hw, hwe⟩
    obtain ⟨Y, hY, hYc, hQ⟩ := exists_cong D p hp x hx w hw hwe
    apply Units.ext
    rw [← hQ, hxi, hcong Y hY hYc]
    rfl
  · intro x hx
    obtain ⟨Y, hQ⟩ := exists_normOne D x hx
    obtain ⟨a, ha⟩ := hval Y
    refine ⟨a, ?_⟩
    rw [← hQ, hxi]
    exact ha
  · intro g x hx
    rw [← quo_of_isDetRoot D W g x hx, hxi]

end GlobalTheory.AntiCycRead

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain
open ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.RecT GlobalTheory.HeightCounting
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.UniDepthZero

theorem algHom_eq_or_conj {L K : Type} [Field L] [NumberField L] [IsCMField L] [Field K] [Algebra (maximalRealSubfield L) K]
    (φ ψ : L →ₐ[(maximalRealSubfield L)] K) : φ = ψ ∨ φ = ψ.comp (IsCMField.complexConj L).toAlgHom := by
  let e : L ≃ₐ[(maximalRealSubfield L)] ψ.fieldRange := AlgEquiv.ofInjectiveField ψ
  haveI : Normal (maximalRealSubfield L) ψ.fieldRange := Normal.of_algEquiv e
  have hR : φ.fieldRange = ψ.fieldRange := by
    have h := AlgHom.fieldRange_of_normal (E := ψ.fieldRange) (φ.comp e.symm.toAlgHom)
    rw [← h]
    ext x
    simp only [AlgHom.mem_fieldRange, AlgHom.comp_apply]
    constructor
    · rintro ⟨y, rfl⟩; exact ⟨e y, by simp⟩
    · rintro ⟨y, rfl⟩; exact ⟨_, rfl⟩
  have hmem : ∀ z, φ z ∈ ψ.fieldRange := fun z => hR ▸ ⟨z, rfl⟩
  let g₀ : L →ₐ[(maximalRealSubfield L)] L := e.symm.toAlgHom.comp (φ.codRestrict ψ.fieldRange.toSubalgebra hmem)
  have hg₀ : ∀ z, ψ (g₀ z) = φ z := fun z => by
    have := congrArg Subtype.val (e.apply_symm_apply ⟨φ z, hmem z⟩)
    exact this
  let σ : L ≃ₐ[(maximalRealSubfield L)] L := AlgEquiv.ofBijective g₀ (Algebra.IsAlgebraic.algHom_bijective g₀)
  have hσ : ∀ z, ψ (σ z) = φ z := hg₀
  have htop := IsCMField.zpowers_complexConj_eq_top L
  have hmemσ : σ ∈ Subgroup.zpowers (IsCMField.complexConj L) := by rw [htop]; trivial
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmemσ
  have hk2 : IsCMField.complexConj L ^ (k % 2) = σ := by
    have h := zpow_mod_orderOf (IsCMField.complexConj L) k
    rw [IsCMField.orderOf_complexConj L] at h
    rw [← hk]
    exact_mod_cast h
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    rw [h0, zpow_zero] at hk2
    ext z
    rw [← hσ, ← hk2]
    rfl
  · right
    rw [h1, zpow_one] at hk2
    ext z
    rw [← hσ, ← hk2]
    rfl

end GlobalTheory.UniDepthZero

namespace GlobalTheory.UniDepthZero

theorem proj_conj {L : Type} [Field L] [NumberField L] [IsCMField L]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (i i₀ : L →ₐ[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L))
    (hi : i = i₀.comp (IsCMField.complexConj L).toAlgHom) (x : AL L) :
    (SplitPlace.proj (⟨v, i⟩ : SplitPlace L)) x = (SplitPlace.proj (⟨v, i₀⟩ : SplitPlace L)) (conjAL L x) := by
  subst hi
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [SplitPlace.proj, conjAL, Algebra.TensorProduct.map_tmul]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]

theorem loc_conj_apply {L : Type} [Field L] [NumberField L] [IsCMField L]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (i i₀ : L →ₐ[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L))
    (hi : i = i₀.comp (IsCMField.complexConj L).toAlgHom) {n : ℕ} (κ : GA L n) (a b : Fin n) :
    (SplitPlace.loc (⟨v, i⟩ : SplitPlace L) n κ).val a b =
      (SplitPlace.loc (⟨v, i₀⟩ : SplitPlace L) n κ⁻¹).val b a := by
  have hm := κ.2
  simp only [GA, UGroup, Subgroup.mem_mk] at hm
  have h1 : ((κ.1⁻¹ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = conjT (conjAL L) κ.1 :=
    Units.inv_eq_of_mul_eq_one_right hm
  have h2 : (((κ⁻¹ : GA L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) b a = conjAL L ((κ.1 : Matrix (Fin n) (Fin n) (AL L)) a b) := by
    rw [InvMemClass.coe_inv, h1]; rfl
  simp only [SplitPlace.loc, MonoidHom.comp_apply, Subgroup.coe_subtype, GeneralLinearGroup.map_apply]
  rw [h2, proj_conj v i i₀ hi]

theorem loc_mem_KOne_of_same {L : Type} [Field L] [NumberField L] [IsCMField L]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (i i₀ : L →ₐ[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) {n : ℕ} (κ : GA L n)
    (h : SplitPlace.loc (⟨v, i⟩ : SplitPlace L) n κ ∈ KOne (v.adicCompletion (maximalRealSubfield L)) (Fin n)) :
    SplitPlace.loc (⟨v, i₀⟩ : SplitPlace L) n κ ∈ KOne (v.adicCompletion (maximalRealSubfield L)) (Fin n) := by
  rcases algHom_eq_or_conj i i₀ with rfl | hi
  · exact h
  · have h' : SplitPlace.loc (⟨v, i₀⟩ : SplitPlace L) n κ⁻¹ ∈ KOne (v.adicCompletion (maximalRealSubfield L)) (Fin n) := by
      refine (GlobalTheory.FixedAtSplit.mem_KOne_iff' _).2 fun a b => ?_
      have := (GlobalTheory.FixedAtSplit.mem_KOne_iff' _).1 h b a
      simp only [Matrix.sub_apply, Matrix.one_apply] at this ⊢
      rw [← loc_conj_apply v i i₀ hi]
      by_cases hab : a = b
      · subst hab; simpa using this
      · simpa [hab, Ne.symm hab] using this
    have := inv_mem h'
    rwa [map_inv, inv_inv] at this

end GlobalTheory.UniDepthZero

namespace GlobalTheory.UniDepthZero

theorem level_trivial {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (s₀ : SplitPlace L) (r : ℕ)
    (ψ₀ : AddChar (s₀.v.adicCompletion (maximalRealSubfield L)) ℂ)
    (ξ : (s₀.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ)
    (hJ : NG.LevelUni J χ s₀ r ψ₀ ξ) (hψ : NG.IsPsi0 s₀ ψ₀)
    (hξ : ∀ u : (s₀.v.adicCompletion (maximalRealSubfield L))ˣ,
      Valued.v ((u : s₀.v.adicCompletion (maximalRealSubfield L)) - 1) < 1 → ξ u = 1)
    (κ : GAf L n) (hκ : TrivOutside {s₀.v} κ)
    (hK : s₀.loc n κ ∈ KOne (s₀.v.adicCompletion (maximalRealSubfield L)) (Fin n)) :
    ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1 := by
  set g := s₀.loc n κ with hg
  have hv := (GlobalTheory.FixedAtSplit.mem_KOne_iff' g).1 hK
  have hoff : ∀ a b : Fin n, a ≠ b → Valued.v (g.val a b) < 1 := fun a b hab => by
    simpa [Matrix.sub_apply, Matrix.one_apply_ne hab] using hv a b
  have hdiag : ∀ a : Fin n, Valued.v (g.val a a - 1) < 1 := fun a => by
    simpa [Matrix.sub_apply] using hv a a
  have hint : g ∈ Formalism.UG.GLint (Fin n) (s₀.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring := by
    rw [(GlobalTheory.AdelicU.GLint_eq_KO_and_princ_eq_KOne s₀.v n).1]
    exact GlobalTheory.StepData.KOne_le_KO hK
  have huni : NG.UniRT s₀ r g := by
    refine ⟨⟨hint, fun a b ha hb => hoff a b ?_⟩, fun a b ha hb => ⟨fun hba => hoff a b ?_, fun hab => ?_⟩⟩
    · rintro rfl; omega
    · rintro rfl; omega
    · subst hab; exact hdiag a
  have hmem : κ ∈ J := (hJ.mem κ hκ).2 huni
  let D : Matrix {x : Fin n // r ≤ x.val} {x : Fin n // r ≤ x.val} (s₀.v.adicCompletion (maximalRealSubfield L)) :=
    Matrix.of fun a b => g.val a.1 b.1
  have hD : GlobalTheory.StepData.MaxM (D - 1) := by
    have hm := GlobalTheory.StepData.mem_KOne.1 hK
    intro a b
    have h3 := hm a.1 b.1
    by_cases hab : a = b
    · subst hab
      simpa [D, Matrix.sub_apply] using h3
    · have h4 : a.1 ≠ b.1 := fun h => hab (Subtype.ext h)
      simpa [D, Matrix.sub_apply, Matrix.one_apply_ne hab, Matrix.one_apply_ne h4] using h3
  obtain ⟨u', hu', hu'v⟩ := GlobalTheory.StepData.exists_mem_KOne hD
  have hdet := GlobalTheory.StepData.det_of_mem_KOne hu'
  have : (Valued.v : Valuation (s₀.v.adicCompletion (maximalRealSubfield L)) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (s₀.v.adicCompletion (maximalRealSubfield L)))
    (Valued.v : Valuation (s₀.v.adicCompletion (maximalRealSubfield L)) (WithZero (Multiplicative ℤ)))
  have hdetv : Valued.v (NG.detDD s₀ r g - 1) < 1 := by
    rw [← he.lt_one_iff_lt_one]
    convert hdet using 3
    rw [Matrix.GeneralLinearGroup.val_det_apply, hu'v]
    rfl
  have hne : NG.detDD s₀ r g ≠ 0 := fun h0 => by
    rw [h0, zero_sub, Valuation.map_neg, Valuation.map_one] at hdetv
    exact lt_irrefl _ hdetv
  have hχ := hJ.chr κ hmem hκ (Units.mk0 _ hne) rfl
  have h1 : ψ₀ (NG.supDiag s₀ r g) = 1 := by
    refine hψ.1 _ ?_
    refine Valuation.map_sum_lt _ one_ne_zero fun a _ => Valuation.map_sum_lt _ one_ne_zero fun b _ => ?_
    split_ifs with h
    · exact hoff a b (fun e => by subst e; omega)
    · simp
  have h2 : ξ (Units.mk0 _ hne) = 1 := hξ _ (by simpa using hdetv)
  refine ⟨hmem, Units.ext ?_⟩
  rw [hχ, h1, h2]
  simp

end GlobalTheory.UniDepthZero

namespace GlobalTheory.UniDepthZero

theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S → ∀ (J : Subgroup (GAf L n)) (χ : J →* ℂˣ), (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) → ∀ (s₀ : SplitPlace L) (r : ℕ) (ψ₀ : AddChar (s₀.v.adicCompletion (maximalRealSubfield L)) ℂ) (ξ : (s₀.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ), NG.LevelUni J χ s₀ r ψ₀ ξ → NG.IsPsi0 s₀ ψ₀ → (∀ u : (s₀.v.adicCompletion (maximalRealSubfield L))ˣ, Valued.v ((u : s₀.v.adicCompletion (maximalRealSubfield L)) - 1) < 1 → ξ u = 1) → ∀ f ∈ NG.isoTyp a.ρ S, f ∈ NG.TypeSp a.ρ J χ → f ≠ 0 → ∀ (s : SplitPlace L), s.v = s₀.v → ∀ (σ : IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S s σ → fixed (GlobalTheory.LocLanglands.cls σ).rep (KOne (s.w.adicCompletion L) (Fin n)) ≠ ⊥ := by
  intro L _ _ _ n a S hS J χ _ s₀ r ψ₀ ξ hJ hψ hξ f hf hfJ hf0 s hs σ hσ
  obtain ⟨c, T, hc, hci, -⟩ := id hσ
  have hfix : ∀ κ : GAf L n, TrivOutside {s.v} κ →
      s.loc n κ ∈ KOne (s.v.adicCompletion (maximalRealSubfield L)) (Fin n) → NG.rt L n κ f = f := by
    intro κ hκ hK
    obtain ⟨v, i⟩ := s
    obtain ⟨v₀, i₀⟩ := s₀
    obtain rfl : v = v₀ := hs
    have hK₀ := loc_mem_KOne_of_same _ i i₀ κ hK
    obtain ⟨hm, h1⟩ := level_trivial J χ _ r ψ₀ ξ hJ hψ hξ κ hκ hK₀
    have h2 := hfJ.2 ⟨κ, hm⟩
    rw [h1] at h2
    simpa using h2
  obtain ⟨u, hu0, hu⟩ := GlobalTheory.LocVec.main L n a S hS s σ hσ c hc hci
    (KOne (s.v.adicCompletion (maximalRealSubfield L)) (Fin n)) 1
    (fun g hg => by
      rw [(GlobalTheory.AdelicU.GLint_eq_KO_and_princ_eq_KOne s.v n).1]
      exact GlobalTheory.StepData.KOne_le_KO hg)
    (by rw [MonoidHom.ker_one, Subgroup.coe_top]; exact isOpen_univ)
    f hf hf0 (fun κ hκ h => by rw [hfix κ hκ h]; simp)
  refine GlobalTheory.LocLanglands.fixed_ne_bot_of_equiv (IrrRep.nonempty_equiv_rep σ).some.symm ?_
  rw [Submodule.ne_bot_iff]
  refine ⟨u, GlobalTheory.Parabolic.mem_fixed.2 fun h hh => ?_, hu0⟩
  have e : Matrix.GeneralLinearGroup.map c.toRingHom (Matrix.GeneralLinearGroup.map c.symm.toRingHom h) = h := by
    ext i j
    simp
  have hg := GlobalTheory.FixedAtSplit.mem_KOne_of_map c hc _ (e.symm ▸ hh)
  have h3 := hu _ hg
  rw [e] at h3
  simpa using h3

end GlobalTheory.UniDepthZero

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain
open ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.RecT GlobalTheory.HeightCounting
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SphHyp

theorem isSpherical_of_hypOutside : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S → ∀ (J : Subgroup (GAf L n)) (χ : J →* ℂˣ), (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) → ∀ (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))), NG.HypOutside J χ B → ∀ f ∈ NG.isoTyp a.ρ S, f ∈ NG.TypeSp a.ρ J χ → f ≠ 0 → ∀ (s : SplitPlace L), s.v ∉ B → ∀ (σ : IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S s σ → IsSpherical (GlobalTheory.LocLanglands.cls σ).rep := by
  intro L _ _ _ n a S hS J χ hlev B hB f hfiso hfT hf0 s hsB σ hσ
  classical
  obtain ⟨i, T₀, hi, hic, -, -, -⟩ := id hσ
  have hrt : ∀ κ, TrivOutside {s.v} κ → ∀ h : s.loc n κ ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring,
      NG.rt L n κ f = (((1 : (Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring) →* ℂˣ) ⟨s.loc n κ, h⟩ : ℂˣ) : ℂ) • f := by
    intro κ hκ h
    have hU := (GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff s hκ).1 h
    have hκB : TrivOutside Bᶜ κ := fun w hw => hκ w (by
      intro hm
      rw [Set.mem_singleton_iff] at hm
      rw [hm] at hw
      exact hsB (by simpa using hw))
    obtain ⟨hJ, hχ⟩ := hB κ hκB
    have hκJ := hJ.2 hU
    rw [hfT.2 ⟨κ, hκJ⟩, hχ hκJ]
    simp
  obtain ⟨u, hu0, hu⟩ := GlobalTheory.LocVec.main L n a S hS s σ hσ i hi hic
    (Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring) 1 (fun g hg => hg)
    (by simp) f hfiso hf0 hrt
  have key : ∀ y, i y ∈ Formalism.UG.Ov L s.w → Valued.v y ≤ 1 := fun y hy =>
    (GlobalTheory.CuspRep.ParLaws.valuation_le_one_iff s.v y).1 (GlobalTheory.SphLoc.le_one_of_map i.toRingHom hi
      ((GlobalTheory.CuspRep.ParLaws.valuation_le_one_iff s.w _).2 hy))
  have hfix : ∀ g ∈ KO (s.w.adicCompletion L) (Fin n), σ.ρ g u = u := by
    intro g hg
    rw [GlobalTheory.SmGL.SphCompletion.KO_completion s.w n, GlobalTheory.HeckeScalarSph.mem_GLint_iff] at hg
    let g' := Matrix.GeneralLinearGroup.map i.symm.toRingHom g
    have hg' : g' ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring := by
      rw [GlobalTheory.HeckeScalarSph.mem_GLint_iff]
      refine ⟨fun p q => ?_, fun p q => ?_⟩
      · show Valued.v (i.symm (g.1 p q)) ≤ 1
        exact key _ (by rw [RingEquiv.apply_symm_apply]; exact hg.1 p q)
      · rw [← map_inv]
        show Valued.v (i.symm ((g⁻¹).1 p q)) ≤ 1
        exact key _ (by rw [RingEquiv.apply_symm_apply]; exact hg.2 p q)
    have e : Matrix.GeneralLinearGroup.map i.toRingHom g' = g :=
      Units.ext (Matrix.ext fun p q => i.apply_symm_apply _)
    have := hu g' hg'
    rw [e] at this
    simpa using this
  have hsph : IsSpherical σ.ρ := by
    intro h
    apply hu0
    have hm : u ∈ fixed σ.ρ (KO (s.w.adicCompletion L) (Fin n)) := fun g => by
      simpa using hfix g.1 g.2
    rw [h] at hm
    exact hm
  exact GlobalTheory.BCOffT.isSpherical_of_equiv (equivRep σ) hsph
end GlobalTheory.SphHyp
end

module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.AttTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.FlagLaws
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.PotOfFlag
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.OverOf4
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RatTorsionFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.Bundle006
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.GoodOf4
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle010
import GroundTheory.GlobalFields.ExistenceTheorem.ExistsIsAbelianGaloisRangeIdeleClassNormEqOfFini
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SplitUnramifiedInduction.SplitOfDecAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HermitianCodeWordWeilElementMemQuadraticField
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.LocTrans
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SphericalOfHasSat

@[expose] public section

section

theorem UpperTheory.V.Z.Win.Birth.awTw :
    UpperTheory.V.Z.Win.Birth.AwTw := by
  intro F Ω _ _ _ _ _ _ l _ n hn ι r κ hκ haut hW
  obtain ⟨_, art, χ, a, hart, -, hL⟩ := hκ
  obtain ⟨π, hreg, hatt⟩ := haut
  obtain ⟨t, ht⟩ := hW π hreg hatt
  obtain ⟨b, hb⟩ := UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.winTw F χ
  exact UpperTheory.V.Z.Win.Birth.awOne F Ω l n hn ι _ (π.twist χ)
    (UpperTheory.V.Af.Cq.attTwist F Ω l ι n r π hatt art χ a κ hart hL)
    ⟨t + b, fun v => hb n (by omega) π t v (ht v)⟩
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N UpperTheory.V UpperTheory.V.Sd

theorem UpperTheory.V.Z.Win.Birth.potOrd :
    UpperTheory.V.Z.Win.Birth.PotOrd := by
  intro F Ω _ _ _ _ _ l _ n r m ψ κ hm H v hv
  have hp : UpperTheory.V.Z.Win.PotUnl r v := by
    refine UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.potOfFlag F Ω l n r m hm v hv fun A hA => ?_
    have hAl : A.valuation (l : Ω) < 1 := by
      have h1 := (hA ((l : ℕ) : 𝓞 F)).2 hv
      simpa only [map_natCast] using h1
    obtain ⟨c, hflag, hc, -⟩ := H A hAl
    exact ⟨c, 1, one_pos, hflag, fun i s hs => by rw [pow_one, pow_one]; exact hc i s hs⟩
  exact ((((UpperTheory.V.Z.Win.flagLaws F Ω l n r).2.1 κ).2.2 v).2).1 hp
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3 UpperTheory.V.Cu

open UpperTheory.V.Cu.AutomorphyOfRankFourLift in
theorem UpperTheory.V.Z.Win.Birth.autOf4W (hne : AlNe) :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (d : Cu.Dat Ω l) (T : Tower d.D), d.T₀.Le T → T.Ok →
    Irr (((d.Q T).map (algebraMap d.c₁.O (PadicAlgCl l))).r.comp T.G'.subtype) → Z.Win.Birth.OffW d.ι d.K' d.ρ (tenB d.ρ₁ d.τ) →
    Z.Win.Birth.AllW d.ι (Af.tw (((d.Q T).map (algebraMap d.c₁.O (PadicAlgCl l))).r.comp
      (resLe T.F_le)).toHomUnits ((toB d.δ).comp (resQ T.L))⁻¹) := by
  intro Ω _ _ _ l _ d T hT hok hirr hoff
  have h1 : Irr ((mapRep (algebraMap d.c₁.O (PadicAlgCl l)) (rep4 1 d.ρ₁ d.τ)).comp (resQ T.L)) := by
    refine irr_cover _ _ (fun x => ?_) hirr
    have hfix : ∀ z ∈ T.L, (x : G T.F Ω) z = z := by
      intro z hz
      have hz' : z ∈ T.F ⊔ T.K := T.hL ▸ hz
      have hle : T.F ⊔ T.K ≤ IntermediateField.fixedField (Subgroup.zpowers (resQ T.F x)) := by
        rw [sup_le_iff, IntermediateField.le_iff_le, IntermediateField.le_iff_le, Subgroup.zpowers_le,
          Subgroup.zpowers_le]
        refine ⟨?_, x.2.1⟩
        rw [IntermediateField.mem_fixingSubgroup_iff]
        exact fun y hy => x.1.commutes ⟨y, hy⟩
      exact (IntermediateField.mem_fixedField_iff _ _).1 (hle hz') _ (Subgroup.mem_zpowers _)
    let y : G T.L Ω := { (x : G T.F Ω).toRingEquiv with commutes' := fun z => hfix z.1 z.2 }
    refine ⟨y, ((toB d.δ (resQ T.F x) : (Qbar l)ˣ) : Qbar l), ?_⟩
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, q_apply,
      show resQ T.L y = resQ T.F (x : G T.F Ω) from AlgEquiv.ext fun _ => rfl]
    rfl
  have hL : IsIrr ((tenB d.ρ₁ d.τ).comp (resQ T.L)) := by
    have := ((irrIff (Qbar l)).1 _).1 h1
    convert this using 1
    ext g : 2
    rfl
  have hkL : ¬ d.K' ≤ T.L := fun hle => by
    obtain ⟨g, hg, hn⟩ := hne Ω l d T hT hok
    refine hn (IntermediateField.fixingSubgroup_le hle ?_)
    rw [T.hL, IntermediateField.fixingSubgroup_sup]
    exact ⟨(IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy => g.commutes ⟨y, hy⟩, hg.1⟩
  haveI : Algebra.IsQuadraticExtension ℚ T.K := { finrank_eq_two' := T.degK }
  have hK : IsAbelianGalois ℚ T.K := IsAbelianGalois.of_isCyclic ℚ T.K
  have hLa : IsAbelianGalois ℚ T.L := by
    have h := @GroundTheory.Global.isAbelianGalois_sup ℚ Ω _ _ _ _ T.F T.K
      T.nF.to_finiteDimensional T.nK.to_finiteDimensional T.abF hK
    rw [← T.hL] at h
    exact h
  have hatt := hoff T.L hLa hkL
    (goodOf4 Ω l d.c d.D d.T₀ T d.ctx.1 hT d.K' d.quad.splS d.quad.off d.w d.θ d.wp d.wsp d.wunr d.k _ d.ρ d.c₁ d.h d.ρ₁ d.x d.mod) hL
  have key : Af.tw (((d.Q T).map (algebraMap d.c₁.O (PadicAlgCl l))).r.comp (resLe T.F_le)).toHomUnits
      ((toB d.δ).comp (resQ T.L))⁻¹ = (tenB d.ρ₁ d.τ).comp (resQ T.L) := by
    ext g : 2
    rw [tw_val]
    change _ • ((d.Q T).map (algebraMap d.c₁.O (PadicAlgCl l))).r (resLe T.F_le g) = _
    rw [q_apply, smul_smul]
    simp only [MonoidHom.inv_apply, MonoidHom.comp_apply]
    rw [show resQ T.F (resLe T.F_le g) = resQ T.L g from AlgEquiv.ext fun _ => rfl, Units.inv_mul, one_smul]
    rfl
  rw [key]
  exact hatt
end
end

section

open UpperTheory.GalN.V UpperTheory.V.Z.Win.Birth

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Ws UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

private theorem val_iff_mem {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 F)} (hA : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A v) (p : ℕ) : A.valuation (p : Ω) < 1 ↔ ((p : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  have h := hA (p : 𝓞 F)
  change A.valuation (algebraMap F Ω (p : F)) < 1 ↔ (p : 𝓞 F) ∈ v.asIdeal at h
  rw [map_natCast] at h
  exact h

private theorem prime_mem {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ p : ℕ, p.Prime ∧ ((p : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  haveI := v.isMaximal
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field _
  letI : Nontrivial (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr v.isPrime.ne_top
  refine ⟨ringChar (𝓞 F ⧸ v.asIdeal), CharP.char_is_prime (𝓞 F ⧸ v.asIdeal) _, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

theorem UpperTheory.V.Z.Win.Birth.badOfW :
    UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.SplitOfDec → UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.UnrOfIne → SphOfUnrW → BadOfW := by
  intro hS hU hP Ω _ _ _ l _ ι K' L M _ _ _ _ _ _ _ hM ρ r π hG hr hpol hreg hatt hW hun v hv
  have hMfix : ∀ s : _root_.Formalism.ConjugateSelfDual.G L Ω, resQ L s ∈ K'.fixingSubgroup → ∀ x : M, s (algebraMap M Ω x) = algebraMap M Ω x := fun s hs x => by
    have : resQ L s ∈ M.fixingSubgroup := by
      rw [hM, IntermediateField.fixingSubgroup_sup]
      exact ⟨hs, (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy => s.commutes ⟨y, hy⟩⟩
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 this x x.2
  obtain ⟨p, hp, hpv⟩ := prime_mem v
  rcases hG p hp with h | ⟨hpl, h⟩
  · exact absurd (hS L M Ω v fun A hA s hs => hMfix s (h A ((val_iff_mem hA p).2 hpv) hs)) hv
  refine ⟨hU L M Ω v fun A hA s hs => hMfix s (h A ((val_iff_mem hA p).2 hpv) s hs).1, fun w hw => ?_⟩
  have hpw : ((p : ℕ) : 𝓞 M) ∈ w.asIdeal := by
    rw [← hw] at hpv
    change algebraMap (𝓞 L) (𝓞 M) p ∈ w.asIdeal at hpv
    rwa [map_natCast] at hpv
  have hlw : ((l : ℕ) : 𝓞 M) ∉ w.asIdeal := fun hl => by
    have hc : IsCoprime ((p : ℕ) : 𝓞 M) ((l : ℕ) : 𝓞 M) :=
      Nat.Coprime.cast ((Nat.coprime_primes hp Fact.out).2 hpl)
    obtain ⟨a, b, e⟩ := hc
    exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (e ▸ w.asIdeal.add_mem (w.asIdeal.mul_mem_left a hpw) (w.asIdeal.mul_mem_left b hl)))
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
  refine hP M Ω l ι 2 one_le_two r π hr hpol hreg hatt hW w hlw A hA fun s hs => ?_
  exact hun A (mt (val_iff_mem hA l).1 hlw) s hs (h A ((val_iff_mem hA p).2 hpw) (galEmb L M Ω s) ⟨hs.1, hs.2⟩).2
end

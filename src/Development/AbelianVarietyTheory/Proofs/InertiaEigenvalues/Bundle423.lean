module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle017
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle406
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoefRingTakenOfLocalisationCoefficientExte
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle005
import Development.AbelianVarietyTheory.Counterexamples.HeckeCharacterExamples.Bundle001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsJumpMultiset
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle401
public import Formalism.LocalRingCardinality.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle124
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle007
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle004
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle093
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle039
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle327
public import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle409
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle355
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle407
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Formalism.ConjugateSelfDual.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

theorem _root_.GlobalTheory.T.exists_globalObjects_every_family_wild : GlobalTheory.TwSys.Cheb → ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) (r₀ : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) (ρ₀ : N.X i → (GE N →* GL (Fin R.r) (N.O i))), GoodR N i r₀ → TakenWild N i r₀ ρ₀ → ∀ (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))), GoodR N i r → ∀ π ∈ N.Z i, (∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := R.t) (r π) (ρ π) (N.chi i) e) → ∃ S : IdempotentChoiceData N i, GoodCongruenceObjects N r ρ π S ∧ IsWildInertiaCyclotomicElement N i S.g0 := by
  first | exact @GlobalTheory.ConsEveryFamilyWild.main | exact GlobalTheory.ConsEveryFamilyWild.main | (intros; apply GlobalTheory.ConsEveryFamilyWild.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

theorem _root_.GlobalTheory.T.exists_coefRingTaken_of_localisationCoefficientExtension : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N₀ N₁ : NData R H what₂) (A₀ : NAut N₀) (A₁ : NAut N₁) (i₀ : N₀.Loc) (i₁ : N₁.Loc), LocExt N₀ N₁ A₀ A₁ i₀ i₁ → ∀ S : Set ℂ, Chosen N₀ A₀ i₀ S → Contains N₁ A₁ i₁ S → ∃ r ρ, GoodR N₁ i₁ r ∧ TakenWild N₁ i₁ r ρ := by
  first | exact @GlobalTheory.CoefDuty.Take.takenWild_of_locExt | exact GlobalTheory.CoefDuty.Take.takenWild_of_locExt | (intros; apply GlobalTheory.CoefDuty.Take.takenWild_of_locExt <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.BlockEnl

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore
open GlobalTheory.BlockJumps GlobalTheory.IndefiniteRowSideFullHecke.BlockJumpCount GlobalTheory.HTW.SumJumps GlobalTheory.Cmp.SmallJumps

theorem multV_oneByOne {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [Algebra.IsSeparable Qp K] [FiniteDimensional Qp LL]
    (hF : IsField BdR) (hs : ∃ s ∈ PD.Fil (-1), PD.ι PD.t * s = 1)
    (σ : Representation LL G (Fin 1 → LL)) (e : ℕ)
    (he : ∀ g u c, σ g u c = ((algebraMap Qp LL (PD.χ g : Qp))⁻¹) ^ e * u c)
    (τ : K →ₐ[Qp] LL) (a : ℤ) : multV PD σ τ a = if a = e then 1 else 0 := by
  let χ : Fin 1 → G →* LLˣ := fun _ => ((cycLL PD LL)⁻¹) ^ e
  have hχ : ∀ c g, ((χ c g : LLˣ) : LL) = ((algebraMap Qp LL (PD.χ g : Qp))⁻¹) ^ e := fun c g => by
    simp [χ, cycLL]
  have hσ : σ = diagRep χ := by
    refine MonoidHom.ext fun g => LinearMap.ext fun u => funext fun c => ?_
    rw [he, diagRep_apply, hχ c]
  rw [hσ, multV_diagRep PD hF, Fin.sum_univ_one]
  exact multV_twist PD hs (Formalism.WeaklyAdmissibleFiltrations.charRep (χ 0)) e (fun g x => by rw [← hχ 0]; rfl) τ a

theorem twistM_one_apply {O Γ : Type} [CommRing O] [Group Γ] (χ : Γ →* Oˣ) (g : Γ) :
    twistM (1 : Γ →* Matrix (Fin 1) (Fin 1) O) χ g 0 0 = ((χ g : Oˣ) : O) := by
  simp [twistM]



theorem blockE_of_isBlockSum (D : D7) (i : D.nd.Loc)
    (r : D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (hB : GlobalTheory.IndefiniteRowSideFullHecke.BlockJumpCount.IsBlockSum D.nd i r ρ π) : BlockE D i r ρ π := by
  obtain ⟨e, he⟩ := hB
  intro w hw L' hL τ
  haveI : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  haveI : FiniteDimensional ℚ_[D.nd.l i] ↥L'.1 := L'.2
  let s : Br.G D.nbr i w hw → Formalism.MainNotions.N.GE D.nd := fun g => decS D.nd w (Br.iota D.nbr i w hw g)
  let j := inc D i w hw L' hL
  let f := j.comp (Br.toLLK (D.nbr i w hw))
  have hf : ∀ c, f (toK D.nd i c) = j ((D.nbr i w hw).toLL c) :=
    fun c => congrArg j (Br.toLLK_alg (D.nbr i w hw) c)
  have hχ0 : ∀ (c : ℕ), c + 1 ≤ D.R.t → ∀ g, (chiU D.nd i 1)⁻¹ g * chiU D.nd i (c + 1) g =
      (epsU D.nd i g)⁻¹ ^ c := fun c hc g => by
    have h := D.nd.chi_def i (c + 1) (by omega) hc
    change (D.nd.chi i 1)⁻¹ g * D.nd.chi i (c + 1) g = _
    rw [h, MonoidHom.mul_apply, MonoidHom.inv_apply, inv_mul_cancel_left, Nat.cast_add, Nat.cast_one,
      add_sub_cancel_right, MonoidHom.zpow_apply, zpow_neg, zpow_natCast, inv_pow]
    rfl
  have hχ : ∀ (c : Fin D.R.t) g, (chiU D.nd i 1)⁻¹ g * chiU D.nd i ((c : ℕ) + 1) g =
      (epsU D.nd i g)⁻¹ ^ (c : ℕ) := fun c g => hχ0 c c.2 g
  have hε : ∀ g, j ((D.nbr i w hw).toLL ((epsU D.nd i (s g) : (D.nd.O i)ˣ) : D.nd.O i)) =
      algebraMap ℚ_[D.nd.l i] ↥L'.1 ((Br.PD D.loc D.nbr i w hw).χ g : ℚ_[D.nd.l i]) := by
    intro g
    have h1 : (D.nbr i w hw).toLL ((epsU D.nd i (s g) : (D.nd.O i)ˣ) : D.nd.O i) =
        algebraMap ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) ((Br.PD D.loc D.nbr i w hw).χ g : ℚ_[D.nd.l i]) := by
      rw [Br.PD, (D.loc _).PD_χ, ← cycZ_eq_chi (D.nbr i w hw) (D.loc _) g]
      exact congrArg Subtype.val ((D.nbr i w hw).eO_alg _)
    rw [h1]
    exact (IntermediateField.inclusion hL).commutes _
  have hM : ∀ {k : ℕ} (M : Formalism.MainNotions.N.GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) g v,
      matRep (locE D i w hw L' hL M) g v = ((mapM (toK D.nd i) M (s g)).map f).mulVec v := fun M g v => by
    rw [show (mapM (toK D.nd i) M (s g)).map f = locE D i w hw L' hL M g from
      Matrix.ext fun a b => hf _]
    rfl
  have hs : ∃ x ∈ (Br.PD D.loc D.nbr i w hw).Fil (-1),
      (Br.PD D.loc D.nbr i w hw).ι (Br.PD D.loc D.nbr i w hw).t * x = 1 := by
    obtain ⟨x, hx, hx1⟩ := GlobalTheory.ThetaTie.exists_inverse_fontaineElement_mem_fil_neg_one (D.locT (D.nd.l i))
    refine ⟨x, ?_, by rw [Br.PD, (D.loc _).PD_ι, (D.loc _).period_datum_t_eq, hx1]⟩
    exact ((D.locT _).fil _ _ _).2 (((D.locT _).fil _ _ _).1 hx)
  have hpow : ∀ g (n : ℕ), f (toK D.nd i (((epsU D.nd i (s g))⁻¹ ^ n : (D.nd.O i)ˣ) : D.nd.O i)) =
      (algebraMap ℚ_[D.nd.l i] ↥L'.1 ((Br.PD D.loc D.nbr i w hw).χ g : ℚ_[D.nd.l i]))⁻¹ ^ n := fun g n => by
    rw [hf, Units.val_pow_eq_pow_val, map_pow, map_pow, map_units_inv, map_inv₀, hε]
  refine ⟨fun a => ?_, fun c hc a => ?_⟩
  · obtain ⟨e', he'⟩ := split_map f (fun g => mapM (toK D.nd i) (rTwO D.nd i r π) (s g))
      (fun g => mapM (toK D.nd i) (WpO D.nd i ρ π) (s g))
      (fun g c => toK D.nd i (((epsU D.nd i (s g))⁻¹ ^ (c : ℕ) : (D.nd.O i)ˣ) : D.nd.O i)) e (fun g u => by
        have h1 : ∀ {k : ℕ} (M : Formalism.MainNotions.N.GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) v,
            (mapM (toK D.nd i) (twistM M (chiU D.nd i 1)⁻¹) (s g)).mulVec v =
              toK D.nd i (((chiU D.nd i 1)⁻¹ (s g) : (D.nd.O i)ˣ) : D.nd.O i) •
                (mapM (toK D.nd i) M (s g)).mulVec v := fun M v => by
          rw [← Matrix.smul_mulVec]
          congr 1
          ext a b
          exact map_mul (toK D.nd i) _ _
        rw [rTwO, WpO, h1, h1, map_smul, he]
        refine Prod.ext rfl (funext fun c => ?_)
        simp only [← hχ, Units.val_mul, map_mul, mul_assoc]
        rfl)
    obtain ⟨J, h1, h2⟩ := jumps_of_split (Br.PD D.loc D.nbr i w hw) (GlobalTheory.SmallJumpExample.isField_bdR D _) hs
      (matRep (locE D i w hw L' hL (rTwO D.nd i r π))) (matRep (locE D i w hw L' hL (WpO D.nd i ρ π))) e'
      (fun g u => by
        rw [hM, hM, he']
        exact Prod.ext rfl (funext fun c => congrArg (· * (e' u).2 c) (hpow g c))) τ
    rw [h1.2, h2.2, Multiset.count_add, count_blockJumps]
    push_cast
    rfl
  · obtain ⟨hc1, hc2⟩ := Finset.mem_Icc.1 hc
    obtain ⟨n, rfl⟩ : ∃ n, c = n + 1 := ⟨c - 1, by omega⟩
    rw [multV_oneByOne (Br.PD D.loc D.nbr i w hw) (GlobalTheory.SmallJumpExample.isField_bdR D _) hs _ n
      (fun g u b => ?_) τ a, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    rw [hM, ← hpow, ← hχ0 n hc2, Subsingleton.elim b 0]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one, Fin.isValue]
    congr 1
    change f (toK D.nd i (chiRatO D.nd i (n + 1) (s g) 0 0)) = _
    rw [chiRatO, twistM_one_apply, MonoidHom.mul_apply, mul_comm]

end GlobalTheory.BlockEnl
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore

namespace GlobalTheory.TameCycChoice

theorem zpow_iff {Γ L A F : Type} [Group Γ] [Field L] [CommRing A] [Field F] (e : L →+* F) (j : A →+* F)
    (hj : Function.Injective j) (ψ₀ : Γ →* Lˣ) (ψ : Γ →* Aˣ)
    (h : ∀ g, e ((ψ₀ g : Lˣ) : L) = j ((ψ g : Aˣ) : A)) (σ γ : Γ) (m : ℤ) :
    ψ σ = ψ γ ^ m ↔ ψ₀ σ = ψ₀ γ ^ m := by
  rw [← map_zpow, ← map_zpow, ← Units.val_inj, ← Units.val_inj, ← hj.eq_iff, ← e.injective.eq_iff, h, h]

theorem mem_zpowers_of_tameGen {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (B : ValuationSubring Ω) {Γ : Type} [Group Γ] (ψ : G E Ω →* Γ) (ho : IsOpen (ψ.ker : Set (G E Ω)))
    (hw : ∀ σ : G E Ω, (∀ y : Ω, y ≠ 0 → B.valuation (σ y / y - 1) < 1) → ψ σ = 1)
    {γ : G E Ω} (hγ : TameGenAt B γ) (σ : G E Ω) (hσ : σ ∈ Ine (F := E) B) :
    ψ σ ∈ Subgroup.zpowers (ψ γ) := by
  let K : Subgroup (G E Ω) := (Subgroup.zpowers (ψ γ)).comap ψ
  have hK : IsOpen (K : Set (G E Ω)) := Subgroup.isOpen_mono (H₁ := ψ.ker)
    (fun g hg => by rw [Subgroup.mem_comap, (MonoidHom.mem_ker).1 hg]; exact one_mem _) ho
  refine closure_minimal (t := (K : Set (G E Ω))) ?_ (K.isClosed_of_isOpen hK) (hγ.2 hσ)
  refine (Subgroup.closure_le K).2 ?_
  rintro g (rfl | hg)
  · exact Subgroup.mem_zpowers _
  · change ψ g ∈ Subgroup.zpowers _
    rw [hw g hg]; exact one_mem _

theorem tameCyc : ∀ (D : D7) (C : NChoice D), NChTie D C → TameCyc D C := by
  intro D C hT i v hv σ hσ
  obtain ⟨ψ₀, -, hW, hK⟩ := hT.psi_eq
  have hl : v ∉ placesOver D.host.E (D.nd.l i) := D.nd.SQ_l i v (Or.inr hv)
  have hmem := mem_zpowers_of_tameGen (D.nd.plOm.1 v) (D.ntw.psiL i) (D.ntw.psiL_open i)
    (fun g hg => GlobalTheory.WildInertiaChar.trivial_on_wild D.host.E D.nd.Om v (D.nd.plOm.1 v) (D.nd.l i)
      (D.nd.lPrime i).out hl (D.nd.plOm.2 v) _ (D.ntw.psiL i) (D.ntw.psiL_open i) (D.ntw.psiL_ord i) g hg)
    (D.nd.restN_tameGenerator_generates i v (Or.inr hv)) σ hσ
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hmem
  refine ⟨m, ?_⟩
  have h0 := (zpow_iff (D.nd.embK i) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))
    (IsFractionRing.injective _ _) (ψ₀ (D.nd.w i)) (D.ntw.psiL i) (hK i) σ (D.nd.gam0 i v) m).1 hm.symm
  exact (zpow_iff (C.embW (D.nd.w i))
    ((algebraMap (C.Oe (D.nd.w i)) (FractionRing (C.Oe (D.nd.w i)))).comp
      (algebraMap (D.ntw.Ok (C.twI (D.nd.w i)) (C.k' (D.nd.w i))) (C.Oe (D.nd.w i))))
    ((IsFractionRing.injective (C.Oe (D.nd.w i)) (FractionRing (C.Oe (D.nd.w i)))).comp (C.Oe_inj (D.nd.w i)))
    (ψ₀ (D.nd.w i)) (psiG D C (D.nd.w i)) (hW (D.nd.w i)) σ (D.nd.gam0 i v) m).2 h0

end GlobalTheory.TameCycChoice
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.ResAbsIrrGood

theorem absIrrSub_top_of_irred {k L : Type} [Field k] [Field L] [IsAlgClosed L] (φ : k →+* L)
    {Γ : Type} [Group Γ] {a : ℕ} (ha : 0 < a) (ρ : Γ →* GL (Fin a) k)
    (h : ∀ W : Submodule L (Fin a → L),
      (∀ g, ∀ x ∈ W, ((mapRep φ ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L).mulVec x ∈ W) →
        W = ⊥ ∨ W = ⊤) :
    AbsIrrSub ρ ⊤ := by
  classical
  set K := AlgebraicClosure k
  set f := algebraMap k K with hf
  letI : Algebra k L := φ.toAlgebra
  let ψ : K →ₐ[k] L := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hψ : ∀ x : k, ψ (f x) = φ x := fun x => ψ.commutes x
  have hψinj : Function.Injective ψ := ψ.toRingHom.injective
  haveI : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
  have hspan : Submodule.span K ((fun v : Fin a → k => f ∘ v) '' ((⊤ : Submodule k (Fin a → k)) : Set _)) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    rw [← Finset.univ_sum_single v]
    refine Submodule.sum_mem _ fun i _ => ?_
    have : (Pi.single i (v i) : Fin a → K) = v i • (f ∘ (Pi.single i (1 : k) : Fin a → k)) := by
      ext j
      by_cases hij : j = i
      · subst hij; simp
      · simp [Pi.single_apply, hij]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, trivial, rfl⟩)
  unfold AbsIrrSub
  rw [hspan]
  have hmat : ∀ g, ((mapRep φ ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) =
      (((mapRep f ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)).map ψ := by
    intro g
    ext i j
    simp [mapRep, hψ]
  refine ⟨top_ne_bot, fun _ _ _ => trivial, fun W' _ hW' => ?_⟩
  set W'' : Submodule L (Fin a → L) := Submodule.span L ((fun v : Fin a → K => ψ ∘ v) '' (W' : Set _))
  have hst : ∀ g, ∀ x ∈ W'', ((mapRep φ ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L).mulVec x ∈ W'' := by
    intro g x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, hu, rfl⟩ := hx
      refine Submodule.subset_span ⟨_, hW' g u hu, ?_⟩
      ext p
      rw [hmat g]
      exact RingHom.map_mulVec ψ.toRingHom _ u p
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ _ hx
  rcases h W'' hst with h1 | h1
  · left
    rw [Submodule.span_eq_bot] at h1
    rw [eq_bot_iff]
    intro v hv
    have := h1 _ ⟨v, hv, rfl⟩
    rw [Submodule.mem_bot]
    ext p
    apply hψinj
    simpa using congrFun this p
  · right
    by_contra hne
    obtain ⟨θ, hθ0, hθ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    let c : Fin a → L := fun i => ψ (θ (Pi.single i 1))
    have hθv : ∀ v : Fin a → K, θ v = ∑ i, v i * θ (Pi.single i 1) := by
      intro v
      conv_lhs => rw [← Finset.univ_sum_single v]

      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show (Pi.single i (v i) : Fin a → K) = v i • (Pi.single i (1 : K) : Fin a → K) by
        ext j; by_cases hij : j = i <;> simp [Pi.single_apply, hij], map_smul, smul_eq_mul]
    have hkill : ∀ X ∈ W'', ∑ i, X i * c i = 0 := by
      intro X hX
      induction hX using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨u, hu, rfl⟩ := hx
        have h0 : θ u = 0 := hθ hu
        have := congrArg ψ (hθv u)

        rw [h0, map_zero, map_sum] at this
        rw [this]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [c]
      | zero => simp
      | add x y _ _ hx hy => simp [add_mul, Finset.sum_add_distrib, hx, hy]
      | smul s x _ hx => simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, hx, mul_zero]
    apply hθ0
    apply LinearMap.pi_ext
    intro i x
    have hci : c i = 0 := by
      have := hkill (Pi.single i 1) (h1 ▸ Submodule.mem_top)
      simpa [Pi.single_apply] using this
    have : θ (Pi.single i 1) = 0 := hψinj (by simpa [c] using hci)
    rw [show (Pi.single i x : Fin a → K) = x • (Pi.single i (1 : K) : Fin a → K) by
      ext j; by_cases hij : j = i <;> simp [Pi.single_apply, hij], map_smul, this]
    simp

end GlobalTheory.ResAbsIrrGood

theorem GlobalTheory.PtCore.residualAbsIrredGoodPoint_of_residualIrred : ∀ D : D7, ResidualIrreducibleRankR D → GlobalTheory.PtCore.ResAbsIrr D := by
  intro D hN9 a π hπ ρ hρ
  obtain ⟨hcont, r, hr, e, he⟩ := hρ
  have hdec : Formalism.MainNotions.TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) a (fun _ => r) (fun _ => ρ) π := ⟨e, he⟩
  have hrb : IsRhoBar D.nd a (redRep D.nd a ρ) := by
    refine ⟨isOpen_ker_redRep D a ρ hcont, ?_⟩
    intro x w hw B σ hB hσ
    have e2 := congrArg (Polynomial.map (IsLocalRing.residue (D.nd.O a)))
      (charpoly_of_decomp D a _ _ π hdec σ)
    rw [Polynomial.map_mul, Polynomial.map_prod, ← Matrix.charpoly_map, ← Matrix.charpoly_map] at e2
    rw [heckePol_res D a x π w, ← hr.2.2 w hw B σ hB hσ, ← Matrix.charpoly_map]
    refine (e2.trans ?_).symm
    congr 1
    refine Finset.prod_congr rfl fun c _ => ?_
    simp
  have hHG : HG D.nd D.naut a := ⟨π, (D.Zgood_tie a π).1 hπ⟩
  have hirr := (hN9 a hHG _ hrb).1
  have hpos : 0 < D.R.r := by
    have := D.R.two_le_m
    unfold Ranks.r
    omega
  exact GlobalTheory.ResAbsIrrGood.absIrrSub_top_of_irred (D.naut.kFbar a) hpos _
    fun W hW => hirr W fun g _ x hx => hW g x hx
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocalFieldIso

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

theorem continuous_symm (i : k ≃+* k') (hi : Continuous i) : Continuous i.symm := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k')
  have ho : IsOpenMap i :=
    AddMonoidHom.isOpenMap_of_sigmaCompact i.toAddEquiv.toAddMonoidHom i.surjective hi
  exact (i.toEquiv.toHomeomorphOfContinuousOpen hi ho).symm.continuous


variable (k) in
theorem valuation_le_one_iff_ord (x : kˣ) : valuation k (x : k) ≤ 1 ↔ 0 ≤ GlobalTheory.SmGL.ord k x := by
  set φ := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k
  have h0 : φ (valuation k (x : k)) ≠ 0 := by simp
  rw [GlobalTheory.SmGL.ord, neg_nonneg, ← φ.strictMono.le_iff_le, map_one, ← WithZero.exp_log h0, ← WithZero.exp_zero,
    WithZero.exp_le_exp]
  simp [φ]


variable (k) in
theorem valuation_le_one_iff_nabs (x : kˣ) : valuation k (x : k) ≤ 1 ↔ GlobalTheory.SplitWeil.nabs k x ≤ 1 := by
  rw [valuation_le_one_iff_ord, GlobalTheory.LGrp.nabs_eq_zpow,
    zpow_le_one_iff_right₀ (by exact_mod_cast GlobalTheory.SplitWeil.one_lt_resCard k)]
  omega

theorem nabs_map (i : k ≃+* k') (hi : Continuous i) (x : kˣ) :
    GlobalTheory.SplitWeil.nabs k' (Units.map i.toRingHom.toMonoidHom x) = GlobalTheory.SplitWeil.nabs k x :=
  GlobalTheory.SplitWeil.nabs_map_of_homeomorph i hi (continuous_symm i hi) x

theorem valuation_map_le_one_iff (i : k ≃+* k') (hi : Continuous i) (x : k) :
    valuation k' (i x) ≤ 1 ↔ valuation k x ≤ 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have h := valuation_le_one_iff_nabs k' (Units.map i.toRingHom.toMonoidHom (Units.mk0 x hx))
  rw [nabs_map i hi, ← valuation_le_one_iff_nabs k] at h
  simpa using h

theorem map_integer (i : k ≃+* k') (hi : Continuous i) :
    (𝒪[k] : Subring k).map i.toRingHom = 𝒪[k'] := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (Valuation.mem_integer_iff _ _).2 ((valuation_map_le_one_iff i hi x).2 ((Valuation.mem_integer_iff _ _).1 hx))
  · intro hy
    refine ⟨i.symm y, (Valuation.mem_integer_iff _ _).2 ?_, i.apply_symm_apply y⟩
    rw [← valuation_map_le_one_iff i hi, RingEquiv.apply_symm_apply]
    exact (Valuation.mem_integer_iff _ _).1 hy

theorem resCard_eq (i : k ≃+* k') (hi : Continuous i) : GlobalTheory.SplitWeil.resCard k' = GlobalTheory.SplitWeil.resCard k := by
  let e : 𝒪[k] ≃+* 𝒪[k'] := (i.subringMap (s := 𝒪[k])).trans (RingEquiv.subringCongr (map_integer i hi))
  exact (Nat.card_congr (IsLocalRing.ResidueField.mapEquiv e).toEquiv).symm

theorem ord_map (i : k ≃+* k') (hi : Continuous i) (x : kˣ) :
    GlobalTheory.SmGL.ord k' (Units.map i.toRingHom.toMonoidHom x) = GlobalTheory.SmGL.ord k x := by
  have h := nabs_map i hi x
  rw [GlobalTheory.LGrp.nabs_eq_zpow, GlobalTheory.LGrp.nabs_eq_zpow, resCard_eq i hi] at h
  have hq : (1 : ℝ) < GlobalTheory.SplitWeil.resCard k := by exact_mod_cast GlobalTheory.SplitWeil.one_lt_resCard k
  exact neg_inj.1 (zpow_right_injective₀ (by linarith) hq.ne' h)

theorem absPow_map (i : k ≃+* k') (hi : Continuous i) (s : ℂ) (x : kˣ) :
    GlobalTheory.SmGL.absPow k' s (Units.map i.toRingHom.toMonoidHom x) = GlobalTheory.SmGL.absPow k s x := by
  ext
  rw [GlobalTheory.SmGL.val_absPow, GlobalTheory.SmGL.val_absPow, nabs_map i hi]

end GlobalTheory.LocalFieldIso

theorem GlobalTheory.LocalFieldIso.continuous_iso_keeps_valuation : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → Continuous i.symm ∧ (∀ x : k, valuation k' (i x) ≤ 1 ↔ valuation k x ≤ 1) ∧ (∀ x : kˣ, ord k' (Units.map i.toRingHom.toMonoidHom x) = ord k x) ∧ resCard k' = resCard k ∧ ∀ (s : ℂ) (x : kˣ), absPow k' s (Units.map i.toRingHom.toMonoidHom x) = absPow k s x := by
  intro k k' _ _ _ _ _ _ _ _ _ _ i hi
  exact ⟨GlobalTheory.LocalFieldIso.continuous_symm i hi, GlobalTheory.LocalFieldIso.valuation_map_le_one_iff i hi,
    GlobalTheory.LocalFieldIso.ord_map i hi, GlobalTheory.LocalFieldIso.resCard_eq i hi, GlobalTheory.LocalFieldIso.absPow_map i hi⟩
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_over_extension : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → admBK (D := D) → PotDRL D.loc → ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), finrank ℚ_[D.nd.l i] (Br.Kw D.nbr i w hw) = 1 → ∀ {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hM : Continuous fun g => M g) (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1), IsCrys ((D.loc (D.nd.l i)).PD K') ((GlobalTheory.Pass.LocDirect.ModuleGaloisRepresentation i w hw M hM).ρ.comp (Subgroup.inclusion (GK_le h))) → ∃ (U' : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw)), letI := U'.modO; letI := U'.towO; ∃ (LT' : Lattice (O := Br.OLL D.nbr i w hw) U'.ρ) (PU : (GlobalTheory.Pass.LocDirect.ModuleGaloisRepresentation i w hw M hM).V →ₗ[Br.LL D.nbr i w hw] U'.V →ₗ[Br.LL D.nbr i w hw] Br.LL D.nbr i w hw), IsDualLat1 (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw M) LT' PU ∧ finrank (Br.OLL D.nbr i w hw) ↥(latticeFiniteCohomology (Br.PD D.loc D.nbr i w hw) LT') ≤ k := by
  first | exact @GlobalTheory.Pass.LocDirect.dualLat_rank | exact GlobalTheory.Pass.LocDirect.dualLat_rank | (intros; apply GlobalTheory.Pass.LocDirect.dualLat_rank <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.ResDual

theorem _root_.GlobalTheory.T.mem_dualBlochKato_of_orthogonal_residual : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → ∀ (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K], IsRes i K → Function.Surjective (algebraMap (X.O0 i) K) → ∀ ρ, IsDual i s ρ → ∀ v ∈ placesOver D.host.E (X.l i), ∀ y : Z1 ((red i K ρ).comp (DecV N v).subtype), (∀ x : Z1 ((red i K (Tgl i s)).comp (DecV N v).subtype), Submodule.Quotient.mk x ∈ bkOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K v → CupCob (fun g : DecV N v => algebraMap (X.O0 i) K ((eps0 X i g.1 : (X.O0 i)ˣ) : X.O0 i)) ((red i K ρ).comp (DecV N v).subtype) (dotProductBilin K K) x.1 y.1) → Submodule.Quotient.mk y ∈ bkOn bkP i ρ (1 : GE N →* Kˣ) K v := by
  first | exact @GlobalTheory.ResDual.Perp.mem_bkOn_of_orthogonal | exact GlobalTheory.ResDual.Perp.mem_bkOn_of_orthogonal | (intros; apply GlobalTheory.ResDual.Perp.mem_bkOn_of_orthogonal <;> assumption)
end

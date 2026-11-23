module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle029
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle152
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle840
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle076
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle030
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResFinEqOneOfAway
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle305
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle306
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle317
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMatricesIntegralOfMemCompletedLattice
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle839
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle077
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle190
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle823
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
import Mathlib.GroupTheory.Nilpotent
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

theorem GlobalTheory.MeetsGen.exists_right_inv_generic_central_projector : ∀ (D : D7), GrpSide D → ∀ [Fintype (G0g D.nd)]
    (U : Subgroup (G0g D.nd)) [Fintype U],
    U = Formalism.L2.NX.Uup (fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) D.R.r →
    ∀ ψ : U →* ℂˣ, Formalism.L2.NX.IsStdGeneric (fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) D.R.r ψ →
    2 ≤ D.R.r → ∃ v : MonoidAlgebra ℂ (G0g D.nd),
      GlobalTheory.MeetsGen.uElt U (fun u => (((ψ u)⁻¹ : ℂˣ) : ℂ)) D.ntypes.e0 * v = 1 := by
  intro D S _ U _ hU ψ hψ hr
  obtain ⟨hc, hi⟩ := GlobalTheory.GoodLatCompare.goodSeriesIdempotent_central_idempotent D
  exact GlobalTheory.T.exists_right_inverse_centralProjectorUnitElement U ψ D.ntypes.e0 hi (fun a => ((Subalgebra.mem_center_iff.mp hc) a).symm)
    (GlobalTheory.T.good_idempotent_irreducible_character_generic_sum_ne_zero D S U hU ψ hψ hr)


open GlobalTheory.MeetsGen in
theorem GlobalTheory.TwInputs.meetsAll_of_ties : GlobalTheory.Published.GreenCuspidal → ∀ (D : D7), NExpTied D → GrpSide D → MeetsAll D := by
  intro hG D T S i j b W hW hst hfix
  classical
  by_cases hr : D.R.r ≤ 1
  · have hFm0 : Fm0 D.nexp i j b = ⊤ := by
      rw [eq_top_iff]
      intro x _
      simp only [Fm0, Submodule.mem_iInf, LinearMap.mem_ker]
      intro u
      have hu1 : u = 1 := Subtype.ext (GlobalTheory.MeetsGen.uup_eq_one_of_le_one _ _ hr _ (T.U_eq ▸ u.2))
      subst hu1
      simp
    rw [hFm0, inf_top_eq]
    exact hW
  have hr : 2 ≤ D.R.r := by omega
  haveI : ∀ k : Fin 2, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  haveI : Fintype (G0g D.nd) := Fintype.ofFinite _
  haveI : Fintype D.nexp.U := Fintype.ofFinite _
  obtain ⟨θ, hθ, hψ⟩ := T.psiU_gen i b
  let s : ↥D.LL0 →+* FractionRing (D.ntw.O i) :=
    (IsFractionRing.map (A := D.ntw.O0 i) (B := D.ntw.O i) (K := FractionRing (D.ntw.O0 i))
      (L := FractionRing (D.ntw.O i)) (D.ntw.O_inj i)).comp (if b then D.ntw.emb0 i else D.ntw.emb0b i)
  let t : ↥D.LL0 →+* ℂ := D.what₂.embLL.comp D.LL0.val.toRingHom
  let Z : Set (FractionRing (D.ntw.O i)) :=
    {z | ∃ (x : Σ k : Fin 2, D.nd.PlG k) (a : Multiplicative (ZMod (D.host.g x.1))), z = ((θ x a : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i))}
  have hZ : ∀ z ∈ Z, ∃ n : ℕ, 0 < n ∧ z ^ n = 1 := by
    rintro z ⟨x, a, rfl⟩
    haveI : NeZero (D.host.g x.1) := ⟨(D.host.g_prime x.1).ne_zero⟩
    refine ⟨Fintype.card (Multiplicative (ZMod (D.host.g x.1))), Fintype.card_pos, ?_⟩
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one, Units.val_one]
  obtain ⟨E, jE, hsE, hZE, hj⟩ := GlobalTheory.T.exists_subfield_adjoin_rootsOfUnity_embedding_complex s t Z hZ

  let θE : ∀ x : (Σ k : Fin 2, D.nd.PlG k), Multiplicative (ZMod (D.host.g x.1)) →* Eˣ := fun x =>
    { toFun := fun a => ⟨⟨((θ x a : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)), hZE ⟨x, a, rfl⟩⟩,
        ⟨(((θ x a)⁻¹ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)), hZE ⟨x, a⁻¹, by simp⟩⟩,
        Subtype.ext (by simp), Subtype.ext (by simp)⟩
      map_one' := by ext; simp
      map_mul' := fun a a' => by ext; simp }
  have hθE : ∀ x a, (((θE x a : Eˣ) : E) : FractionRing (D.ntw.O i)) = ((θ x a : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) :=
    fun _ _ => rfl
  let θ' : ∀ x : (Σ k : Fin 2, D.nd.PlG k), Multiplicative (ZMod (D.host.g x.1)) →* ℂˣ :=
    fun x => (Units.map jE.toMonoidHom).comp (θE x)
  have hθ' : 2 ≤ D.R.r → ∀ x, θ' x ≠ 1 := by
    intro h x h1
    apply hθ h x
    refine MonoidHom.ext fun a => Units.ext ?_
    have h2 := congrArg (fun φ : Multiplicative (ZMod (D.host.g x.1)) →* ℂˣ => ((φ a : ℂˣ) : ℂ)) h1
    simp only [θ', MonoidHom.comp_apply, Units.coe_map, MonoidHom.one_apply, Units.val_one] at h2
    have h3 : ((θE x a : Eˣ) : E) = 1 := jE.injective (by rw [map_one]; exact h2)
    have h4 : (((θE x a : Eˣ) : E) : FractionRing (D.ntw.O i)) = 1 := by rw [h3]; rfl
    rw [MonoidHom.one_apply, Units.val_one]
    exact (hθE x a).symm.trans h4
  let ψ' : D.nexp.U →* ℂˣ := (Formalism.L2.NX.psiStd _ _ θ').comp (Subgroup.inclusion T.U_eq.le)
  have hψ' : Formalism.L2.NX.IsStdGeneric (fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) D.R.r ψ' :=
    ⟨θ', hθ', fun u => rfl⟩
  obtain ⟨vC, hvC⟩ := GlobalTheory.MeetsGen.exists_right_inv_generic_central_projector D S D.nexp.U T.U_eq ψ' hψ' hr

  have hψE : ∀ u : D.nexp.U, ((D.nexp.psiU i b u : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) ∈ E := by
    intro u
    rw [hψ u]
    simp only [Formalism.L2.NX.stdVal, Units.coe_prod]
    exact E.prod_mem fun x _ => hZE ⟨x, _, rfl⟩
  let fE : D.nexp.U → E := fun u => ⟨(((D.nexp.psiU i b u)⁻¹ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)),
    by rw [Units.val_inv_eq_inv_val]; exact E.inv_mem (hψE u)⟩
  let eE : MonoidAlgebra E (G0g D.nd) :=
    MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm fun g => (⟨s (D.nexp.eLL0 g), hsE _⟩ : E))
  have hψval : ∀ u : D.nexp.U, jE ⟨((D.nexp.psiU i b u : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)), hψE u⟩ =
      ((ψ' u : ℂˣ) : ℂ) := by
    intro u
    have e1 : (⟨((D.nexp.psiU i b u : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)), hψE u⟩ : E) =
        ∏ x, ((θE x (Multiplicative.ofAdd (Formalism.L2.NX.supSum D.R.r
          (((u : G0g D.nd) x : GL (Fin D.R.r) (ZMod (D.host.g x.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g x.1))))) : Eˣ) : E) := by
      apply Subtype.ext
      simp only [SubmonoidClass.coe_finsetProd, hθE]
      rw [hψ u]
      simp [Formalism.L2.NX.stdVal, Units.coe_prod]
    rw [e1, map_prod]
    simp [ψ', Formalism.L2.NX.psiStd, Formalism.L2.NX.stdVal, θ', Units.coe_prod]
  have hC1 : MonoidAlgebra.mapRingHom (G0g D.nd) jE (uElt D.nexp.U fE eE) =
      uElt D.nexp.U (fun u => (((ψ' u)⁻¹ : ℂˣ) : ℂ)) D.ntypes.e0 := by
    rw [GlobalTheory.MeetsGen.map_uElt]
    congr 1
    · funext u
      have e2 : fE u = (⟨((D.nexp.psiU i b u : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)), hψE u⟩ : E)⁻¹ :=
        Subtype.ext (by simp [fE])
      rw [e2, map_inv₀, hψval, Units.val_inv_eq_inv_val]
    · refine MonoidAlgebra.ext (Finsupp.ext fun g => ?_)
      rw [MonoidAlgebra.coeff_mapRingHom]
      simp only [eE, MonoidAlgebra.coeff_ofCoeff, Finsupp.coe_equivFunOnFinite_symm]
      rw [hj, ← D.nStage_trivialCharacter_coeff_eq]
      rfl
  have hK1 : MonoidAlgebra.mapRingHom (G0g D.nd) E.subtype eE = D.nexp.eAlg i b := by
    refine MonoidAlgebra.ext (Finsupp.ext fun g => ?_)
    rw [MonoidAlgebra.coeff_mapRingHom, D.nexp.eAlg_def]
    simp only [eE, MonoidAlgebra.coeff_ofCoeff, Finsupp.coe_equivFunOnFinite_symm]
    rfl
  obtain ⟨vE, hvE⟩ := GlobalTheory.T.monoidAlgebra_exists_right_inv_of_map_field jE (uElt D.nexp.U fE eE) ⟨vC, by rw [hC1]; exact hvC⟩
  have hvK := congrArg (MonoidAlgebra.mapRingHom (G0g D.nd) E.subtype) hvE
  rw [map_mul, map_one, GlobalTheory.MeetsGen.map_uElt, hK1] at hvK
  have heq := GlobalTheory.MeetsGen.eq_sum_of_uElt_mul D.nexp.U _ (D.nexp.eAlg i b) _ (D.nexp.eAlg_idem i b) (D.nexp.eAlg_central i b) hvK
  exact GlobalTheory.T.stable_submodule_meets_character_type_vectors (D.nexp.actG i j b) D.nexp.U (D.nexp.psiU i b) (D.nexp.eAlg i b) _ heq W hW
    (fun g x hx => hst g x hx) (fun x hx => hfix x hx)

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwInputs.EigAll

theorem exists_smul_mem_of_mem_span {O K V : Type*} [CommRing O] [IsDomain O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] (N : Submodule O V)
    {v : V} (hv : v ∈ Submodule.span K (N : Set V)) : ∃ d : O, d ≠ 0 ∧ d • v ∈ N := by
  let S : Submodule K V :=
    { carrier := {v | ∃ d : O, d ≠ 0 ∧ d • v ∈ N}
      add_mem' := by
        rintro a c ⟨d, hd, ha⟩ ⟨e, he, hc⟩
        refine ⟨d * e, mul_ne_zero hd he, ?_⟩
        rw [smul_add]
        refine N.add_mem ?_ ?_
        · rw [mul_comm, mul_smul]; exact N.smul_mem _ ha
        · rw [mul_smul]; exact N.smul_mem _ hc
      zero_mem' := ⟨1, one_ne_zero, by rw [smul_zero]; exact N.zero_mem⟩
      smul_mem' := by
        rintro c a ⟨d, hd, ha⟩
        obtain ⟨n, m, hm, rfl⟩ := IsFractionRing.div_surjective (A := O) c
        have hm0 : m ≠ 0 := nonZeroDivisors.ne_zero hm
        have hmK : algebraMap O K m ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hm
        refine ⟨m * d, mul_ne_zero hm0 hd, ?_⟩
        have e1 : m • ((algebraMap O K n / algebraMap O K m) • a) = n • a := by
          rw [← algebraMap_smul K m, smul_smul, mul_div_cancel₀ _ hmK, algebraMap_smul]
        show (m * d) • ((algebraMap O K n / algebraMap O K m) • a) ∈ N
        rw [mul_comm, mul_smul, e1, smul_comm]
        exact N.smul_mem _ ha }
  have hle : Submodule.span K (N : Set V) ≤ S :=
    Submodule.span_le.2 fun x hx => ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  exact hle hv

theorem eq_zero_of_joint {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : ι → V →ₗ[K] V) (p : ι → Prop) (ev : ι → K) (M : Finset (ι → K)) :
    ∀ y : V, (∀ μ ∈ M, ∃ t, p t ∧ μ t ≠ ev t) → (∀ t, p t → T t y = ev t • y) →
      y ∈ Submodule.span K {z | ∃ μ ∈ M, ∀ t, p t → T t z = μ t • z} → y = 0 := by
  classical
  induction M using Finset.induction_on with
  | empty =>
    intro y _ _ hs
    have : {z : V | ∃ μ ∈ (∅ : Finset (ι → K)), ∀ t, p t → T t z = μ t • z} = ∅ := by
      ext z; simp
    rw [this, Submodule.span_empty, Submodule.mem_bot] at hs
    exact hs
  | insert μ0 M _ ih =>
    intro y hne hy hs
    obtain ⟨t0, hp0, hμ0⟩ := hne μ0 (Finset.mem_insert_self _ _)
    let L : V →ₗ[K] V := T t0 - μ0 t0 • LinearMap.id
    have hL : Submodule.span K {z | ∃ μ ∈ insert μ0 M, ∀ t, p t → T t z = μ t • z} ≤
        (Submodule.span K {z | ∃ μ ∈ M, ∀ t, p t → T t z = μ t • z}).comap L := by
      rw [Submodule.span_le]
      rintro z ⟨μ, hμ, hz⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      rcases Finset.mem_insert.1 hμ with rfl | hμ
      · have : L z = 0 := by
          simp only [L, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hz t0 hp0, sub_self]
        rw [this]; exact Submodule.zero_mem _
      · have : L z = (μ t0 - μ0 t0) • z := by
          simp only [L, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hz t0 hp0, sub_smul]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨μ, hμ, hz⟩)
    have hLy : L y = (ev t0 - μ0 t0) • y := by
      simp only [L, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hy t0 hp0, sub_smul]
    have h0 := ih ((ev t0 - μ0 t0) • y) (fun μ hμ => hne μ (Finset.mem_insert_of_mem hμ))
      (fun t ht => by rw [map_smul, hy t ht, smul_comm]) (hLy ▸ hL hs)
    rcases smul_eq_zero.1 h0 with h | h
    · exact absurd (sub_eq_zero.1 h).symm hμ0
    · exact h

variable {D : D7} {cf : CharFrame D} {Rw : RowSide D} {low : Finset ℕ}
  {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} {S : RatDat D.ntw}
  {hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)} {eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0}
  {θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ}


open Classical in
def trEig (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) : Set (D.nexp.Fm i j b) :=
  {z | ∃ μ ∈ (Finset.univ.filter fun s : D.ntw.Sig i => D.ntw.jS i s = j ∧ D.ntw.side i s = b).image
      (fun s (t : ℕ × PlE D.host) => GlobalTheory.EigTie.sigEv s t.1 t.2),
    ∀ t : ℕ × PlE D.host, HkIdx i t.1 t.2 → D.nexp.hkF i j b t.1 t.2 z = μ t • z}

theorem good_part_le_span_triple_eigenvectors (Bs : SideB D cf Rw low Pq S hL eig θ) (hF : FullAll D) (i : D.ntw.Tw) (j : ℕ)
    (hj : j ∈ Finset.Icc 1 D.R.m) (b : Bool) :
    V0 D.nexp i j b ≤ Submodule.span (FractionRing (D.ntw.O i)) (trEig D i j b) := by
  classical
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
  set K := FractionRing (D.ntw.O i)
  let Φ : K ⊗[D.ntw.O i] D.ntw.B i j b →ₗ[K] D.nexp.Fm i j b := (D.nexp.embB i j b).liftBaseChange K
  have hΦ : ∀ k P, HkIdx i k P → ∀ z, Φ (((D.ntw.hk i j b k P).baseChange K) z) = D.nexp.hkF i j b k P (Φ z) := by
    intro k P hP z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      simp only [Φ, LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul, map_smul]
      rw [Bs.hk_emb i j b k P x h1 h2 hP.2.2.2 hP.2.2.1 hP.2.1]
    | add z w hz hw => simp only [map_add (f := _), hz, hw]

  have hrange : ∀ x : D.ntw.B i j b, D.nexp.embB i j b x ∈ Submodule.span K (trEig D i j b) := by
    intro x
    have hx : (1 : K) ⊗ₜ[D.ntw.O i] x ∈ (⊤ : Submodule K (K ⊗[D.ntw.O i] D.ntw.B i j b)) := trivial
    rw [← Bs.sigSpan i j b h1 h2] at hx
    have hx' := Submodule.mem_map_of_mem (f := Φ) hx
    rw [Submodule.map_span] at hx'
    have e : Φ ((1 : K) ⊗ₜ[D.ntw.O i] x) = D.nexp.embB i j b x := by
      show (D.nexp.embB i j b).liftBaseChange K ((1 : K) ⊗ₜ[D.ntw.O i] x) = _
      rw [LinearMap.liftBaseChange_tmul, one_smul]
    rw [e] at hx'
    refine Submodule.span_mono ?_ hx'
    rintro _ ⟨z, ⟨s, hs1, hs2, hz⟩, rfl⟩
    refine ⟨fun t => GlobalTheory.EigTie.sigEv s t.1 t.2, Finset.mem_image.2 ⟨s, by simp [hs1, hs2], rfl⟩, ?_⟩
    intro t ht
    rw [← hΦ t.1 t.2 ht, hz t.1 t.2 ht.1 ht.2.1 ht.2.2.1 ht.2.2.2, map_smul]
    rfl
  intro v hv
  obtain ⟨d, hd, hdv⟩ := exists_smul_mem_of_mem_span (K := K) (D.nexp.Bsup i j b) (by rw [hF i j hj b]; trivial)
  have hdV : d • v ∈ V0 D.nexp i j b := by
    rw [← algebraMap_smul K d v]; exact Submodule.smul_mem _ _ hv
  have hmem : d • v ∈ LinearMap.range (D.nexp.embB i j b) := by
    rw [Bs.tw.B_range i j b]; exact ⟨hdv, hdV⟩
  obtain ⟨x, hx⟩ := hmem
  have hdK : algebraMap (D.ntw.O i) K d ≠ 0 := by
    intro h; exact hd (IsFractionRing.injective (D.ntw.O i) K (h.trans (map_zero _).symm))
  have : v = (algebraMap (D.ntw.O i) K d)⁻¹ • (d • v) := by
    rw [← algebraMap_smul K d v, smul_smul, inv_mul_cancel₀ hdK, one_smul]
  rw [this, ← hx]
  exact Submodule.smul_mem _ _ (hrange x)

theorem sig_all_of_sideB : ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw)
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0)
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ),
    NoFormsOff D → MeetsAll D → CommAll D → FullAll D → D.nexp.sig_all := by
  intro D cf Rw low Pq S hL eig θ Bs hN hM hC hF
  classical
  refine EigModel.sig_all_of hN hM hC ?_
  rintro i j hj b ev ⟨y, hyV, hy0, hyE⟩
  by_contra hno
  push_neg at hno
  apply hy0
  refine eq_zero_of_joint (fun t : ℕ × PlE D.host => D.nexp.hkF i j b t.1 t.2) (fun t => HkIdx i t.1 t.2)
    (fun t => ev t.1 t.2) _ y ?_ (fun t ht => hyE t.1 t.2 ht) (good_part_le_span_triple_eigenvectors Bs hF i j hj b hyV)
  intro μ hμ
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hμ
  obtain ⟨hs1, hs2⟩ := (Finset.mem_filter.1 hs).2
  obtain ⟨k, P, hk, hne⟩ := hno s hs1 hs2
  exact ⟨(k, P), hk, hne⟩

end GlobalTheory.TwInputs.EigAll

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnramPull


theorem unramOutside_of_corr : ∀ (D : D7) (N : NData D.R D.host D.what₂) (art : Neutral.B1.Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E N.Om), GlobalTheory.HeckeGal.IsGlobalArtin art → ∀ (r : G D.host.E N.Om →* ℂˣ) (l n : ℕ), l.Prime → (∀ σ, r σ ^ (l ^ n) = 1) → ∀ (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ → GlobalTheory.ToricDistribution.Corr art r χ → ∀ Q : Finset (Pl D.host.E), SplitSet Q → (∀ P ∈ Q, ((l : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → (∀ v : Pl D.host.E, v ∉ Q → (∀ P ∈ Q, ¬ Formalism.BasicNotions.IsConjPl D.host P v) → ∀ B : ValuationSubring N.Om, IsPlaceOver B v → ∀ σ ∈ Ine (F := D.host.E) B, r σ = 1) → GlobalTheory.ExportSeries.UnramOutside c Q := by
  intro D N art hart r l n hl hp c χ hc hcorr Q hQ hlQ hine
  intro x hx1 hx2 hx3 hxQ
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  have hidem := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3
  obtain ⟨M, hM, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2 hidem c χ hc
  choose e he hinf he1 he0 using hidem
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨S, k, hS, hS'⟩ := GlobalTheory.finiteIdele_exists_local_approx D.host.E M hM
    (Units.map ((ι : _ →+* _).comp (finPart D)).toMonoidHom x)
  set f := idem Q + cA D (idem Q) with hf
  have hcf : cA D f = f := by rw [hf, map_add (f := _), GlobalTheory.DualPairCheck.cA_cA, add_comm]
  have hfe : ∀ P ∈ Q, idemAt P * f = idemAt P := by
    intro P hP
    have k1 : idemAt P * idem Q = idemAt P :=
      GlobalTheory.PlaceModelSum.mul_sum_orth (fun a ha => (hQ.isIdemAt ha).1) (fun a ha b hb hab => hQ.mul_eq_zero ha hb hab) hP
    have k2 : idemAt P * cA D (idem Q) = 0 := by

      rw [idem, map_sum, Finset.mul_sum]
      exact Finset.sum_eq_zero fun j hj => hQ.mul_conj hP hj
    rw [hf, mul_add, k1, k2, add_zero]
  have hdelta : ∀ P e', GlobalTheory.IdemSupport.IsDelta Φ P e' → e P = e' := fun P e' h' =>
    GlobalTheory.IdemSupport.delta_unique hΦ ((GlobalTheory.IdemSupport.tie_iff hΦ (he P).1 (hinf P) P).1 (he P).2.2) h'
  have hcomp : ∀ P, (∃ a, e P = a ∧ a * f = a) → ι (finPart D (x : AE D)) P = 1 := by
    rintro P ⟨a, hea, haf⟩
    have k : e P * (x : AE D) = e P := by rw [hea, ← haf, mul_assoc, hxQ]
    have k' : ι (finPart D (e P * (x : AE D))) P = ι (finPart D (e P)) P := by rw [k]
    have e5 : ι (finPart D (e P * (x : AE D))) = ι (finPart D (e P)) * ι (finPart D (x : AE D)) := by
      rw [map_mul (finPart D) (e P) (x : AE D), map_mul ι]
    rw [e5] at k'
    change ι (finPart D (e P)) P * ι (finPart D (x : AE D)) P = ι (finPart D (e P)) P at k'
    rwa [he1 P, one_mul] at k'
  have hstar : ∀ z : D.host.E, star z = D.host.conj z := bridge_star_holds D.R D.host
  have hconj : ∀ P' v : Pl D.host.E, Formalism.BasicNotions.IsConjPl D.host P' v → v = GlobalTheory.IdemSupport.cP P' := by
    intro P' v h
    refine (GlobalTheory.IdemSupport.eq_of_le fun y hy => ?_).symm
    refine (h (GlobalTheory.IdemSupport.cO D y) y ?_).1 hy
    rw [GlobalTheory.IdemSupport.cO_coe, ← hstar, star_star]
  have hlconj : ∀ P' v : Pl D.host.E, Formalism.BasicNotions.IsConjPl D.host P' v →
      (((l : ℕ) : 𝓞 D.host.E) ∈ P'.asIdeal ↔ ((l : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal) := by
    intro P' v h
    refine h _ _ ?_
    push_cast
    exact (map_natCast _ l).symm
  have hv : ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι (finPart D (x : AE D)) P) = 1 := by
    intro P
    have a := (h2 _).1 hx2 P
    have b := (h2 _).1 hx3 P
    have e' : Valued.v (ι (finPart D (x : AE D)) P) * Valued.v (ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) P) = 1 := by
      rw [← map_mul]
      have : ι (finPart D (x : AE D)) P * ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) P = 1 := by
        change (ι (finPart D (x : AE D)) * ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D))) P = 1
        rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
        rfl
      rw [this, map_one]
    refine le_antisymm a ?_
    calc (1 : WithZero (Multiplicative ℤ)) = _ := e'.symm
      _ ≤ Valued.v (ι (finPart D (x : AE D)) P) * 1 := mul_le_mul_right b _
      _ = _ := mul_one _
  have key := hprod x hx1 S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS'
  apply Subtype.ext
  refine key.trans (Finset.prod_eq_one fun P hP => ?_)
  obtain ⟨a, -, b⟩ := hS P hP
  have a' : Valued.v (ι (finPart D (x : AE D)) P) = P.valuation D.host.E (k P : D.host.E) := a
  have b' : Valued.v (ι (finPart D (x : AE D)) P - algebraMap D.host.E _ (k P : D.host.E)) ≤
      WithZero.exp (-1 : ℤ) * P.valuation D.host.E (k P : D.host.E) := b
  rw [hv P] at a'
  rw [← a', mul_one] at b'
  have hun : Formalism.L2.Host.IsUnitAt P (Formalism.L2.Host.atFin P (k P)) := by
    show Valued.v (((k P : D.host.E)) : P.adicCompletion D.host.E) = _
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ← a']
  have : χ.locK P (k P) = 1 := by
    show χ.loc P (Formalism.L2.Host.atFin P (k P)) = 1
    by_cases hPQ : P ∈ Q ∨ ∃ P' ∈ Q, Formalism.BasicNotions.IsConjPl D.host P' P
    · have hlP : ((l : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
        rcases hPQ with hPQ | ⟨P', hP', hc'⟩
        · exact hlQ P hPQ
        · exact fun hm => hlQ P' hP' ((hlconj P' P hc').2 hm)
      have h1P : ι (finPart D (x : AE D)) P = 1 := by
        refine hcomp P ?_
        rcases hPQ with hPQ | ⟨P', hP', hc'⟩
        · exact ⟨idemAt P, hdelta P _ (GlobalTheory.IdemSupport.delta_of_isIdemAt hΦ (hQ.isIdemAt hPQ)), hfe P hPQ⟩
        · refine ⟨cA D (idemAt P'), ?_, ?_⟩
          · rw [hconj P' P hc']
            exact hdelta _ _ (GlobalTheory.IdemSupport.delta_conj hΦ (GlobalTheory.IdemSupport.delta_of_isIdemAt hΦ (hQ.isIdemAt hP')))
          · rw [← hcf, ← map_mul, hfe P' hP']
      have ht := GlobalTheory.ToricDistribution.levelLe_one_of_pow hl (hcorr.pow hp) hlP
      refine ht _ hun ?_
      rw [h1P] at b'
      have e4 : ((Formalism.L2.Host.atFin P (k P) : (P.adicCompletion D.host.E)ˣ) : P.adicCompletion D.host.E) - 1 =
          -(1 - algebraMap D.host.E _ (k P : D.host.E)) := by
        show algebraMap D.host.E _ (k P : D.host.E) - 1 = _
        ring
      rw [e4, Valuation.map_neg]
      simpa using b'
    · push_neg at hPQ
      obtain ⟨B, hB⟩ := ReciprocityTheory.Gal.exists_isPlaceOver N.Om P
      exact GlobalTheory.ToricDistribution.Corr.unr hart hcorr hB (hine P hPQ.1 hPQ.2 B hB) _ hun
  show ((χ.locK P (k P) : ℂˣ) : ℂ) = 1
  rw [this, Units.val_one]

end GlobalTheory.UnramPull
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem _root_.GlobalTheory.T.frameMatrices_integral_of_mem_completedLattice : ∀ {D : D7} {S T : HSp D} {F : Frame S T}, F.Good → ∀ {R : Finset (Pl D.host.E)}, PlacesOK ∅ R → ∀ {x : WO S T}, IsHalf (idem R) x → x ∈ F.lat → IsIntM (frMapO S T F.βS F.βT x) ∧ IsIntM (frMapAdj S T F.βS F.βT x) := by
  first | exact @GlobalTheory.LatHalfInt.frMap_int_of_mem_lat | exact GlobalTheory.LatHalfInt.frMap_int_of_mem_lat | (intros; apply GlobalTheory.LatHalfInt.frMap_int_of_mem_lat <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.NgalFil

theorem ENStable_and_jumps : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → (∀ m ∈ P.M, P.EN m ∈ P.Man) ∧ ∀ U : Set ℤ, (∀ τ, JumpsInV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ τ U) → P.jumps ⊆ U := by
  intro hB l _ a e _ _ ϖ LL _ _ hl ι _ _ P T I jB Pl AI hS hC hH
  have h1 := GlobalTheory.T.monodromyOperator_maps_into_completion hB l a e ϖ LL hl ι P T I jB Pl AI hS hC hH
  exact ⟨h1, GlobalTheory.T.filtration_jumps_breuilKisin_subset_galoisJumps hB l a e ϖ LL hl ι P T I jB Pl AI hS hC hH h1⟩

end GlobalTheory.NgalFil
end

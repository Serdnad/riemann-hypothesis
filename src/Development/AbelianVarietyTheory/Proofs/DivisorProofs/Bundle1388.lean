module

import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle126
public import Formalism.LocalRingCardinality.DataTheta
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1284
public import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle238
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle197
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle117
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.AdelicScalarSectionLift
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CuspLatticeAnyLevel
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHasCentChar
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

namespace GlobalTheory.HoweD

theorem jm_conjTranspose (p q : ℕ) : (Formalism.BasicNotions.TH.Jm p q)ᴴ = Formalism.BasicNotions.TH.Jm p q := by
  unfold Formalism.BasicNotions.TH.Jm Formalism.UG.Jpq
  rw [Matrix.fromBlocks_conjTranspose]
  simp

theorem jm_mul_self (p q : ℕ) : Formalism.BasicNotions.TH.Jm p q * Formalism.BasicNotions.TH.Jm p q = 1 := by
  unfold Formalism.BasicNotions.TH.Jm Formalism.UG.Jpq
  rw [Matrix.fromBlocks_multiply]
  simp [Matrix.fromBlocks_one]

theorem upq_span (p q : ℕ) (Z : Mat p q) : ∃ X ∈ upq p q, ∃ Y ∈ upq p q, Z = X + Complex.I • Y := by
  apply GlobalTheory.FockTensor.exists_upq_add <;> assumption

end GlobalTheory.HoweD
end

section

open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

namespace GlobalTheory.HolDS

theorem raisingSpan_eq_span_words : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D), IsKMod ε σ D E → ∀ S : Submodule ℂ H, S ≤ D → raisingSpan ε σ S = (Submodule.span ℂ {y : D | ∃ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) ∧ ∃ x ∈ S.comap D.subtype, y = (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x}).map D.subtype := by
  intro n ε H _ _ σ D E hK S hSD
  set Y : Set D := {y : D | ∃ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) ∧
    ∃ x ∈ S.comap D.subtype, y = (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x} with hY
  have hcmp := GlobalTheory.T.complexifiedDerivedAction_eq_sum_kFiniteModule n ε H σ D E hK

  have hstab : ∀ a b, ε a = true → ε b = false → ∀ y ∈ Submodule.span ℂ Y, E a b y ∈ Submodule.span ℂ Y := by
    intro a b ha hb y hy
    have hle : Submodule.span ℂ Y ≤ (Submodule.span ℂ Y).comap (E a b) := by
      rw [Submodule.span_le]
      rintro z ⟨l, hl, x, hx, rfl⟩
      apply Submodule.subset_span
      refine ⟨(a, b) :: l, ?_, x, hx, ?_⟩
      · intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        · exact ⟨ha, hb⟩
        · exact hl p hp
      · simp [List.map_cons, List.prod_cons, Module.End.mul_apply]
    exact hle hy
  apply le_antisymm
  · rw [raisingSpan, Submodule.span_le]
    rintro w ⟨l, hl, v, hv, rfl⟩
    have key : ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ Z ∈ l, Z ∈ pPlus ε) →
        ∃ y ∈ Submodule.span ℂ Y, (y : H) = l.foldr (GlobalTheory.SmVec.dRepC (Jm ε) σ) v := by
      intro l
      induction l with
      | nil =>
        intro _
        refine ⟨⟨v, hSD hv⟩, Submodule.subset_span ⟨[], by simp, ⟨v, hSD hv⟩, hv, by simp⟩, rfl⟩
      | cons Z l ih =>
        intro hl
        obtain ⟨y, hy, hyv⟩ := ih (fun Z' hZ' => hl Z' (List.mem_cons_of_mem _ hZ'))
        have hZ := hl Z List.mem_cons_self
        refine ⟨∑ a, ∑ b, Z a b • E a b y, ?_, ?_⟩
        · refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
          by_cases h : ε a = true ∧ ε b = false
          · exact Submodule.smul_mem _ _ (hstab a b h.1 h.2 y hy)
          · rw [hZ a b h, zero_smul]
            exact Submodule.zero_mem _
        · rw [List.foldr_cons, ← hyv, hcmp Z y]
    obtain ⟨y, hy, hyv⟩ := key l hl
    exact ⟨y, hy, hyv⟩
  · rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨y, ⟨l, hl, x, hx, rfl⟩, rfl⟩
    have key : ∀ l : List (Fin n × Fin n),
        (((l.map fun p : Fin n × Fin n => E p.1 p.2).prod x : D) : H) =
          (l.map fun p : Fin n × Fin n => Matrix.single p.1 p.2 (1 : ℂ)).foldr (GlobalTheory.SmVec.dRepC (Jm ε) σ) (x : H) := by
      intro l
      induction l with
      | nil => simp
      | cons p l ih =>
        rw [List.map_cons, List.map_cons, List.foldr_cons, ← ih, hcmp, List.prod_cons, Module.End.mul_apply]
        congr 1
        rw [Finset.sum_eq_single p.1, Finset.sum_eq_single p.2]
        · simp
        · intro b _ hb; simp [Matrix.single_apply, Ne.symm hb]
        · simp
        · intro a _ ha
          refine Finset.sum_eq_zero fun b _ => ?_
          simp [Matrix.single_apply, Ne.symm ha]
        · simp
    refine Submodule.subset_span ⟨l.map fun p : Fin n × Fin n => Matrix.single p.1 p.2 (1 : ℂ), ?_, (x : H), hx, key l⟩
    intro Z hZ
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hZ
    exact single_mem_pPlus (hl p hp).1 (hl p hp).2 1

end GlobalTheory.HolDS
end

section

noncomputable section

open NumberField MeasureTheory Matrix Polynomial Formalism.L2.Host
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspRep.Central
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele GlobalTheory.IdeleCovolume

namespace GlobalTheory.CuspQuot

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem commute_Zalg {T : Module.End ℂ (Sm E a)} (hT : ∀ X, Commute T (lie E a X)) {z : Module.End ℂ (Sm E a)}
    (hz : z ∈ Zalg E a) : Commute T z := by
  let S : Subalgebra ℂ (Module.End ℂ (Sm E a)) := Subalgebra.centralizer ℂ {T}
  have hS : ∀ {z}, z ∈ S ↔ Commute T z := by
    intro z
    simp [S, Subalgebra.mem_centralizer_iff, Commute, SemiconjBy]
  have hV : ∀ X, lie E a X ∈ S := fun X => hS.2 (hT X)
  have hE : ∀ τ i j, Eop τ i j ∈ S := fun τ i j =>
    S.smul_mem (S.sub_mem (hV _) (S.smul_mem (hV _) _)) _
  refine hS.1 ((Algebra.adjoin_le (S := S) ?_) hz)
  rintro _ ⟨τ, u, rfl⟩
  refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  refine S.add_mem ?_ (hE _ _ _)
  split_ifs
  · exact S.algebraMap_mem _
  · exact S.zero_mem


variable (E) in
def cpowChar (s : ℂ) : HChar E :=
  ⟨MonoidHom.toHomUnits
      { toFun := fun x => Complex.exp (s * Real.log (ideleNorm (E := E) x))
        map_one' := by simp
        map_mul' := fun x y => by
          rw [map_mul, Real.log_mul (ideleNorm_ne_zero _) (ideleNorm_ne_zero _), ← Complex.exp_add]
          push_cast; ring_nf },
    Units.isEmbedding_val₀.continuous_iff.2 (Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_ideleNorm.log fun _ => ideleNorm_ne_zero _)))),
    fun k => Units.ext (by
      have h := ideleNorm_principalIdele (E := E) k
      exact (congrArg (fun r : ℝ => Complex.exp (s * Real.log r)) h).trans (by simp))⟩

theorem exists_chiDet_splitCentre (ha : 0 < a) (c : ℂ) :
    ∃ χ : HChar E, ∀ t : ℝ, ((chiDet a χ (splitCentre E a t) : ℂˣ) : ℂ) = Complex.exp (c * t) := by
  let D : ℝ →+ ℝ := AddMonoidHom.mk'
    (fun t => Real.log (ideleNorm (E := E) (GeneralLinearGroup.det (splitCentre E a t)))) fun x y => by
      rw [splitCentre_add, map_mul, map_mul, Real.log_mul (ideleNorm_ne_zero _) (ideleNorm_ne_zero _)]
  have hD : Continuous D :=
    (continuous_ideleNorm.comp (GeneralLinearGroup.continuous_det.comp
      GlobalTheory.OneRep.SplitTwist.continuous_splitCentre)).log fun _ => ideleNorm_ne_zero _
  have hDt : ∀ t, D t = t * D 1 := fun t => by simpa using map_real_smul D hD t 1
  have hD1 : 0 < D 1 := by
    change 0 < Real.log (ideleNorm (E := E) (GeneralLinearGroup.det (splitCentre E a 1)))
    rw [det_splitCentre_one, map_pow, Real.log_pow]
    exact mul_pos (by exact_mod_cast ha) (Real.log_pos (one_lt_ideleNorm_eIdele E))
  refine ⟨cpowChar E (c / D 1), fun t => ?_⟩
  change Complex.exp (c / D 1 * (D t : ℝ)) = _
  have : (D 1 : ℂ) ≠ 0 := by exact_mod_cast hD1.ne'
  rw [hDt t]; push_cast
  congr 1; field_simp

end GlobalTheory.CuspQuot

end
end

section

open NumberField IsDedekindDomain

noncomputable section

open Formalism.L2.Host GlobalTheory.UnitaryBC GlobalTheory.CuspRep ReciprocityTheory.Neutral.Bridge.HCFR

namespace GlobalTheory.PolChar

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [IsCMField E] in
theorem continuous_infAdeleMap (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    Continuous (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap K L) :=
  continuous_fst.comp ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_adeleMap K L).comp
    (Continuous.prodMk_left (0 : FiniteAdeleRing (𝓞 K) K)))

omit [IsCMField E] in
theorem continuous_finAdeleMap (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    Continuous (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap K L) :=
  continuous_snd.comp ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_adeleMap K L).comp
    (Continuous.prodMk_right (0 : InfiniteAdeleRing K)))

end GlobalTheory.PolChar

namespace GlobalTheory.PolChar

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open Classical in
theorem pInf_ideleMap_infIdele (v : InfinitePlace (maximalRealSubfield E)) (w : InfinitePlace E) :
    pInf E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (infIdele _ v (-1)) : Ad E) w =
      if w.comap (algebraMap (maximalRealSubfield E) E) = v then -1 else 1 := by
  show (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w))
    (AbsoluteValue.Completion.map (w.comap (algebraMap (maximalRealSubfield E) E)).1 w.1
      (Pi.mulSingle v ((-1 : (v.Completion)ˣ) : v.Completion) (w.comap (algebraMap (maximalRealSubfield E) E)))) = _
  split_ifs with h
  · subst h
    rw [Pi.mulSingle_eq_same]
    simp
  · rw [Pi.mulSingle_eq_of_ne h]
    simp

theorem pFin_ideleMap_infIdele (v : InfinitePlace (maximalRealSubfield E)) :
    pFin E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (infIdele _ v (-1)) : Ad E) = 1 :=
  map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap (maximalRealSubfield E) E)

end GlobalTheory.PolChar

namespace GlobalTheory.PolChar

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


open Classical in
def iAt (v : InfinitePlace (maximalRealSubfield E)) : (Cinf E)ˣ where
  val w := if w.comap (algebraMap (maximalRealSubfield E) E) = v then Complex.I else 1
  inv w := if w.comap (algebraMap (maximalRealSubfield E) E) = v then -Complex.I else 1
  val_inv := by
    funext w
    simp only [Pi.mul_apply, Pi.one_apply]
    split_ifs <;> simp
  inv_val := by
    funext w
    simp only [Pi.mul_apply, Pi.one_apply]
    split_ifs <;> simp

theorem apply_ideleMap_infIdele_neg_one (χ : HChar E)
    (hc : ∀ x : (AdeleRing (𝓞 E) E)ˣ, χ.1 (Units.map (conjAd E).toMonoidHom x) = χ.1 x)
    (v : InfinitePlace (maximalRealSubfield E)) :
    χ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (infIdele _ v (-1))) = 1 := by
  classical
  have h1 : pInf E (infId E (iAt v)).val = (iAt v).val := by
    change (infEq E).symm (1 - infEq E 1 + infEq E (iAt v).val) = _
    simp
  have h2 : pFin E (infId E (iAt v)).val = 1 := by
    change (1 : Af E) - 0 + 0 = 1
    simp
  have key : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (infIdele _ v (-1)) =
      infId E (iAt v) * (Units.map (conjAd E).toMonoidHom (infId E (iAt v)))⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    refine Units.ext (ad_ext ?_ ?_)
    · funext w
      change pInf E ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (infIdele _ v (-1))).val *
        conjAd E (infId E (iAt v)).val) w = pInf E (infId E (iAt v)).val w
      rw [map_mul, Pi.mul_apply, GlobalTheory.ThetaPull.pInf_conjAd, h1, pInf_ideleMap_infIdele]
      change _ * starRingEnd ℂ ((iAt v).val w) = (iAt v).val w
      simp only [iAt]
      split_ifs <;> simp
    · change pFin E ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (infIdele _ v (-1))).val *
        conjAd E (infId E (iAt v)).val) = pFin E (infId E (iAt v)).val
      rw [map_mul, GlobalTheory.ThetaPull.pFin_conjAd, h2,
        pFin_ideleMap_infIdele, map_one, one_mul]
  rw [key, map_mul, map_inv, hc, mul_inv_cancel]

end GlobalTheory.PolChar

namespace GlobalTheory.PolChar

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem apply_conjAd_of_isAbsPow {χ : HChar E} {u : ℝ} (h : χ.IsAbsPow u) (x : (AdeleRing (𝓞 E) E)ˣ) :
    χ.1 (Units.map (conjAd E).toMonoidHom x) = χ.1 x := by
  have e : χ * GlobalTheory.ThetaPull.thetaChar χ = 1 := GlobalTheory.HeckeUnrTrivial.eq_one_of_val_eq_one _ fun v _ => by
    have h2 := (GlobalTheory.ThetaPull.isAbsPow_thetaChar h).2.1 v
    have h0 : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.2 fun h0 => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    refine Units.ext ?_
    rw [HChar.val_mul, Units.val_mul, h.2.1 v, h2, Units.val_one, ← Complex.cpow_add _ _ h0]
    simp
  have h3 := congrArg (fun c : HChar E => c.1 x) e
  change χ.1 x * (χ.1 (Units.map (conjAd E).toMonoidHom x))⁻¹ = 1 at h3
  exact (mul_inv_eq_one.1 h3).symm

theorem adeleMap_conj_eq (x : AdeleRing (𝓞 E) E) :
    @GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap E E _ _ _ _
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E).toRingEquiv.toRingHom.toAlgebra x = conjAd E x := by
  letI : Algebra E E := (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E).toRingEquiv.toRingHom.toAlgebra
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_infiniteAdeleRing_of_numberField_field E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField E
  have key : ∀ k : E, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap E E (algebraMap E (AdeleRing (𝓞 E) E) k) =
      conjAd E (algebraMap E (AdeleRing (𝓞 E) E) k) := by
    intro k
    rw [conjAd_algebraMap]
    exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap_algebraMap E E k
  have hsymm : Continuous (infEq E).symm := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)
  refine Prod.ext ?_ ?_
  · exact congrFun ((InfiniteAdeleRing.denseRange_algebraMap E).equalizer (continuous_infAdeleMap E E)
      ((continuous_infEq E).comp (continuous_star.comp hsymm))
      (funext fun k => congrArg Prod.fst (key k))) x.1
  · exact congrFun ((GlobalTheory.AdeleCharTwist.denseRange_fin (F := E)).equalizer
      (continuous_finAdeleMap E E) (continuous_conjFin _)
      (funext fun k => congrArg Prod.snd (key k))) x.2

theorem ideleConj_eq (x : (AdeleRing (𝓞 E) E)ˣ) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E x = Units.map (conjAd E).toMonoidHom x :=
  Units.ext (adeleMap_conj_eq x.val)

end GlobalTheory.PolChar

namespace GlobalTheory.PolChar

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def resReal (χ : HChar E) : HChar (maximalRealSubfield E) :=
  ⟨χ.1.comp (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E),
    χ.2.1.comp (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_ideleMap _ E), fun k =>
      (congrArg χ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap_principalIdele _ E k)).trans (χ.2.2 _)⟩

theorem resReal_apply (χ : HChar E) (x : (AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E))ˣ) :
    (resReal χ).1 x = χ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E x) := rfl

theorem resReal_locInf_neg_one {χ : HChar E} {u : ℝ} (h : χ.IsAbsPow u) (v : InfinitePlace (maximalRealSubfield E)) :
    (resReal χ).locInf v (-1) = 1 :=
  apply_ideleMap_infIdele_neg_one χ (apply_conjAd_of_isAbsPow h) v

end GlobalTheory.PolChar
end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.LiftScalarCompare

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.FWT Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Places

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem primeToHost (h : R.toLevCh.Is A.μ0) : AdelicScalarSectionLift.PrimeToHost R := by
  intro PP hP
  obtain ⟨k, hk⟩ := (h.Pg PP).1 hP
  refine GlobalTheory.CoverHalf.not_mem_of_coprime PP.isPrime.ne_top (a := D.host.g k) ?_ (R.C.P.overP hk)
  have hc := D.ntypes.g_cond k
  have h1 : Nat.Coprime (D.host.g k) (D.host.QS * D.host.q * D.host.d) := by
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hc, Nat.gcd_one_left]
  refine Nat.Coprime.mul_right h1 ?_
  refine (D.host.ccK_coprime _ ?_).symm
  simp [D.host.g_level k]

end Places

section Coord

variable {V : HSp D} (c : CoefA V) {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}

variable {c}

end Coord

theorem adjoint_idem {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (ρ : Representation ℂ G H) (hu : ∀ g x, ‖ρ g x‖ = ‖x‖) {a : G → ℂ} (ha : GoodBasisCentralIdempotents.IsCentralIdem a) {x : H}
    (hx : (∑ g, a g • ρ g) x = x) (y : H) : ⟪x, (∑ g, a g • ρ g) y⟫_ℂ = ⟪x, y⟫_ℂ := by
  set E : H →ₗ[ℂ] H := ∑ g, a g • ρ g with hE
  have hin : ∀ g u w, ⟪ρ g u, ρ g w⟫_ℂ = ⟪u, w⟫_ℂ := fun g => LinearIsometry.inner_map_map ⟨ρ g, hu g⟩
  have hcomm : ∀ g u, E (ρ g u) = ρ g (E u) := fun g u => by

    simp only [hE, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, ← Module.End.mul_apply, ← map_mul]
    refine (Fintype.sum_equiv (MulAut.conj g).toEquiv _ _ fun h => ?_).symm
    show _ = a (g * h * g⁻¹) • ρ (g * h * g⁻¹ * g) u
    rw [ha.1, inv_mul_cancel_right]
  have hidem : ∀ u, E (E u) = E u := fun u => by
    have h1 : E u = ∑ g, ∑ h, (a h * a (h⁻¹ * g)) • ρ g u := by
      simp only [← Finset.sum_smul, ha.2, hE, LinearMap.sum_apply, LinearMap.smul_apply]
    have h2 : E (E u) = ∑ h, ∑ g, (a h * a g) • ρ h (ρ g u) := by

      simp only [hE, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp only [mul_comm]
    rw [h2, h1, Finset.sum_comm (f := fun g h => (a h * a (h⁻¹ * g)) • ρ g u)]
    refine Finset.sum_congr rfl fun h _ => Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => ?_
    simp only [Equiv.coe_mulLeft, inv_mul_cancel_left, map_mul, Module.End.mul_apply]

  have hadj : ∀ u, LinearMap.adjoint E u = ∑ g, star (a g) • ρ g⁻¹ u := fun u => by
    refine ext_inner_right ℂ fun w => ?_
    rw [LinearMap.adjoint_inner_left, sum_inner, hE, LinearMap.sum_apply, inner_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [LinearMap.smul_apply, inner_smul_right, inner_smul_left, ← hin g (ρ g⁻¹ u), ← Module.End.mul_apply, ← map_mul,
      mul_inv_cancel, map_one, Module.End.one_apply]
    simp
  have hfix : E (LinearMap.adjoint E x) = LinearMap.adjoint E x := by

    rw [hadj, map_sum]
    simp only [map_smul, hcomm, hx]

  have hz : LinearMap.adjoint E x - x = 0 := by
    rw [← inner_self_eq_zero (𝕜 := ℂ)]
    have h1 : E (LinearMap.adjoint E x - x) = LinearMap.adjoint E x - x := by rw [map_sub, hfix, hx]
    rw [inner_sub_left, LinearMap.adjoint_inner_left, h1, sub_self]
  rw [← LinearMap.adjoint_inner_left, sub_eq_zero.1 hz]

end GlobalTheory.LiftScalarCompare

end
end

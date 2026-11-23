module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle301
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle555
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle404
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle289
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle531
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle304
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle617
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle568
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TameAnyAtOfIsConjPl
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle015
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle297

@[expose] public section

section



section
noncomputable section
namespace GlobalTheory.IneAway
open GlobalTheory.TypeLeaf
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
end GlobalTheory.IneAway
namespace GlobalTheory.TypeLeaf
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.TameLabels
end GlobalTheory.TypeLeaf
namespace GlobalTheory.TypeLeaf.ConjPlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.TameLabels GlobalTheory.AntiRamConj GlobalTheory.TwistDet
open scoped Pointwise
theorem tame_any_at_of_is_conj_pl_tame_gen : ∀ D : D7, WildOne D → (∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k), D.nd.l i ≠ D.host.g k → ∀ s ∈ wildSet D.nd (D.nd.plOm.1 (D.naut.plGw k v)), D.nd.chi i 1 s = 1) → _root_.UpperTheory.GalS.GalAwayN D → FrobDense D → ∀ (i : D.nd.Loc) (π : D.naut.CG D.R.r) (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)), D.naut.csd π → D.naut.ralg π → _root_.UpperTheory.GalS.FullLabS D [⟨D.R.r, π, 1⟩] → IsRepOfSig D.nd D.naut i [⟨D.R.r, π, 1⟩] ρ → ∀ k : Fin 2, D.nd.l i ≠ D.host.g k → ∀ (v : D.nd.PlG k) (w : PlE D.host), IsConjPl D.host (D.naut.plGw k v) w → TameGen D.nd (D.nd.plOm.1 w) (D.nd.gam0 i w) → TameAnyAt D i [⟨D.R.r, π, 1⟩] ρ k w := by
  intro D hW hχ hG hF i π ρ hc ha hfull hρ k hl v w hvw hgen
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hP := not_mem_of_ne (D := D) (v := v) (D.nd.lPrime i).out hl
  have hw : w ∉ placesOver D.host.E (D.nd.l i) := fun h => hP (mem_placesOver_conj (isConjPl_symm hvw) h)
  have hγ0 : TameGenAt (D.nd.plOm.1 (D.naut.plGw k v)) (D.nd.gam0 i (D.naut.plGw k v)) := by
    refine D.nd.restN_tameGenerator_generates i _ (Or.inl ((D.nd.S_def i _).2 ⟨?_, hP⟩))
    have hv := D.naut.plGw_over k v
    fin_cases k
    · exact Or.inl hv
    · exact Or.inr (Or.inl hv)
  have hγw : TameGenAt (D.nd.plOm.1 w) (D.nd.gam0 i w) := ⟨D.nd.locNd_chebotarevPlace_mem i w, hgen⟩
  obtain ⟨g, hg⟩ := exists_tameGenAt_conj D hvw hγw
  have hkill : ∀ s : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om,
      (∀ y : D.nd.Om, y ≠ 0 → (D.nd.plOm.1 (D.naut.plGw k v)).valuation (s y / y - 1) < 1) →
      ((redF D i ρ).prod (chiBar D i)) s = 1 := by
    intro u hu
    have huI := mem_ine_of_wild hu
    obtain ⟨ι, -, hred⟩ := GlobalTheory.T.exists_reduction_teichmullerEmbedding_at_localisation D i k hl
    have hf := _root_.UpperTheory.GalS.fl0' hfull k v
    unfold labSig at hf
    rw [isoLoc_single] at hf
    have h1 := (_root_.GlobalTheory.IneAway.ineAt' D hG hF i π ρ hc ha hfull hρ k v _ rfl hP u huI).trans (hW k v _ hf u huI hu)
    rw [D.naut.locG_dim] at h1
    have h2 : ((redF D i ρ u : GL (Fin D.R.r) _) :
        Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar (D.nd.l i))).charpoly = (X - 1) ^ D.R.r := by
      rw [charpoly_redF, hred _ (Multiset.replicate D.R.r 1) (by rw [h1]; simp)]
      simp
    have hgv : (D.nd.plOm.1 (D.naut.plGw k v)).valuation ((D.host.g k : ℕ) : D.nd.Om) < 1 := by
      have h4 := D.nd.plOm.2 (D.naut.plGw k v)
      have h5 : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := D.naut.plGw_over k v
      simpa using (h4 _).2 h5
    have h3 := GlobalTheory.T.wild_eq_one_of_charpoly_unipotent_mod_l _ _ _ (D.host.g k) (D.nd.l i) D.R.r hl hgv _ (redF D i ρ)
      (GlobalTheory.T.residualRep_ker_isOpen D i ρ hρ.1) u hu h2
    refine Prod.ext h3 ?_
    change Units.map _ (D.nd.chi i 1 u) = 1
    rw [hχ i k v hl u hu, map_one]
  have hopen : IsOpen ((((redF D i ρ).prod (chiBar D i)).ker : Subgroup _) : Set (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om)) := by
    rw [MonoidHom.ker_prod, Subgroup.coe_inf]
    exact (GlobalTheory.T.residualRep_ker_isOpen D i ρ hρ.1).inter (isOpen_ker_chiBar D i)
  obtain ⟨n, hn, hM, hpow⟩ := GlobalTheory.T.tameGenerator_image_eq_coprime_pow _ _ _ _ _ hγ0 hg _ _ hopen hkill
  set γ0 := D.nd.gam0 i (D.naut.plGw k v) with hγ0def
  set M := orderOf (((redF D i ρ).prod (chiBar D i)) γ0) with hMdef
  have hone : ((redF D i ρ).prod (chiBar D i)) γ0 ^ M = 1 := pow_orderOf_eq_one _
  have hinv : ((redF D i ρ).prod (chiBar D i)) (g * cConj D.ntw (D.nd.gam0 i w) * g⁻¹)⁻¹ =
      ((redF D i ρ).prod (chiBar D i)) γ0 ^ (n * (M - 1)) := by
    rw [map_inv, hpow, inv_eq_iff_mul_eq_one, ← pow_add, ← mul_one_add, show 1 + (M - 1) = M by omega, mul_comm, pow_mul,
      hone, one_pow]
  have hn' : (n * (M - 1)).Coprime M := hn.mul_left ((Nat.coprime_self_sub_left hM).2 (Nat.coprime_one_left _))
  obtain ⟨θ, hθ, hθo, hθn⟩ := GlobalTheory.T.exists_order_preserving_power_hom_algClosure_primeField (D.host.g k) M _ hM hn'
  obtain ⟨hcp, hcχ⟩ := GlobalTheory.T.inertia_compatible_conjugation_representation D hF i π ρ hc hρ w _ hw (D.nd.plOm.2 w) _ (Subgroup.inv_mem _ hγw.1)
    (cConj D.ntw (D.nd.gam0 i w)⁻¹) (fun y => by rw [cConj_apply, RingEquiv.symm_apply_apply])
  rw [inv_inv] at hcp hcχ
  have econj : (g * cConj D.ntw (D.nd.gam0 i w) * g⁻¹)⁻¹ = g * cConj D.ntw (D.nd.gam0 i w)⁻¹ * g⁻¹ := by
    rw [map_inv]
    group
  rw [econj] at hinv
  have hρ1 : redF D i ρ (g * cConj D.ntw (D.nd.gam0 i w)⁻¹ * g⁻¹) = redF D i ρ γ0 ^ (n * (M - 1)) :=
    congrArg Prod.fst hinv
  have hχ1 : chiBar D i (g * cConj D.ntw (D.nd.gam0 i w)⁻¹ * g⁻¹) = chiBar D i γ0 ^ (n * (M - 1)) :=
    congrArg Prod.snd hinv
  have hρM : redF D i ρ γ0 ^ M = 1 := congrArg Prod.fst hone
  have hχM : chiBar D i γ0 ^ M = 1 := congrArg Prod.snd hone
  obtain ⟨v', j, ι, e₁, e₂, he₁, he₂, hι, hch, hχ0⟩ := _root_.GlobalTheory.T.tame_any_at_pl_gw D hG hF i π ρ hc ha hfull hρ k hl v
  refine ⟨v', j, ι.comp θ, e₁, e₂, he₁, he₂, injPrimeTo_comp hι hθ hθo, ?_, ?_⟩
  · have h1 := charpoly_pow_of_prod _ _ _ hch (n * (M - 1))
    rw [← Units.val_pow_eq_pow_val, ← hρ1, map_mul, map_mul, map_inv _ g, Units.val_mul, Units.val_mul, Matrix.coe_units_inv,
      Matrix.charpoly_units_conj, charpoly_redF, hcp, ← charpoly_redF] at h1
    rw [h1]
    refine congrArg _ (Multiset.map_congr rfl fun x hx => ?_)
    rw [comp_pow_eq (D.nd.lPrime i).out hM hι hθ hθn he₁ x
      (pow_eq_one_of_prod _ _ _ hch (by rw [← Units.val_pow_eq_pow_val, hρM, Units.val_one]) hx)]
  · rw [← chiBar_val] at hχ0
    rw [comp_pow_eq (D.nd.lPrime i).out hM hι hθ hθn he₂ _
      (by rw [← hχ0, ← Units.val_pow_eq_pow_val, hχM, Units.val_one]), ← hχ0, ← Units.val_pow_eq_pow_val, ← hχ1,
      map_mul, map_mul, map_inv _ g, mul_inv_cancel_comm, chiBar_val, chi1, chi1, hcχ]
end GlobalTheory.TypeLeaf.ConjPlace
namespace GlobalTheory.AdmTame
end GlobalTheory.AdmTame
end
end
end

section



section
noncomputable section
namespace Formalism.MainNotions.SumRepresentations
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal Topology
section BN
variable {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ}
end BN
section G1
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
end G1
section SS
variable {Γ : Type} [Group Γ] {a : ℕ}
variable {K L : Type} [Field K] [Field L] [Algebra K L]
end SS
section Cont
end Cont
section Main
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
end Main
section C42
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
namespace At
end At
namespace At
end At
end C42
section Del
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
end Del
section G5c
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) {i : N.Loc}
  (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) {ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))}
  {π : N.X i} {S : IdempotentChoiceData N i}
end G5c
section Quad
end Quad
section G5c
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) {i : N.Loc}
  (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) {ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))}
  {π : N.X i} {S : IdempotentChoiceData N i}
end G5c
section G5c
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) {i : N.Loc}
  (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) {ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))}
  {π : N.X i} {S : IdempotentChoiceData N i}
end G5c
section Cont
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)
end Cont
section G5b
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) {i : N.Loc}
  (r : N.X i → (Formalism.ConjugateSelfDual.G H.E N.Om →* GL (Fin R.nV) (N.O i)))
end G5b
section Maschke
variable {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ}
end Maschke
section G5a
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) {i : N.Loc}
  (r : N.X i → (Formalism.ConjugateSelfDual.G H.E N.Om →* GL (Fin R.nV) (N.O i)))
theorem splitI_of_monodromyInertiaType_of_lgCatN (A : NAut N) (hr : GoodR N i r) (hTY : At.MonodromyInertiaType N A) (w : PlE H)
    (hSQ : w ∈ N.S i ∨ w ∈ N.Q i)
    (hcond : w ∈ N.Q i ∨ (At.Del N i ∧
      (w ∈ placesOver H.E H.pde ∨ (N.l i = H.pde ∧ w ∈ placesOver H.E H.pde'))))
    (hL : _root_.UpperTheory.GalS.LGCatN N r A w) (x : N.X i) : SplitI N r w x :=
  _root_.UpperTheory.GalS.SplitI_of_TY N r A hr w (N.SQ_l i w hSQ) hL (fun P => hTY.1 i P w hSQ hcond) x
end G5a
section H0
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) {i : N.Loc}
end H0
section Lin
end Lin
section Z
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
namespace At
end At
end Z
namespace At
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
def SufficientGaloisClauseAlt (i : N.Loc) : Prop :=
  HG N A i → ∀ r, GoodR N i r → ∀ w : PlE H, (w ∈ N.S i ∨ w ∈ N.Q i) →
    _root_.UpperTheory.GalS.LGCatN N r A w ∧
    (w ∈ N.S i → (∃ rb, IsRhoBar N i rb) ∧ ∀ rb, IsRhoBar N i rb →
      ¬ (((rb (N.gam0 i w) : GL _ _) : Matrix (Fin R.r) (Fin R.r) _).charpoly).IsRoot
        (IsLocalRing.residue (N.O i) (chi1 N i (N.gam0 i w))) ∧
      ∀ e : ℤ, HOneTwoZero N i w (Formalism.MainNotions.N.twistRep (Formalism.MainNotions.N.glRep rb) (chiEpsBar N i e)))
theorem galois_clause_of_sufficient_alt (hC : Cheb N) (hT : TieGal N A) (hTY : MonodromyInertiaType N A) (i : N.Loc) (hDel : Del N i)
    (h : _root_.Formalism.MainNotions.SumRepresentations.At.SufficientGaloisClauseAlt N A i) : ConclusionG5 N A i := by
  rw [galois_clause_iff_reduced N A i hDel]
  intro hg r hr w hw hl
  obtain ⟨hL, hS⟩ := h hg r hr w hw
  refine ⟨fun hq x => _root_.Formalism.MainNotions.SumRepresentations.splitI_of_monodromyInertiaType_of_lgCatN N r A hr hTY w hw ?_ hL x, fun hgk hS' => ?_,
    fun hS' rb hrb e => ?_⟩
  · rcases hq with hq | hq
    · exact Or.inl hq
    · exact Or.inr ⟨hDel, hq⟩
  · obtain ⟨⟨rb, hrb⟩, hall⟩ := hS hS'
    exact _root_.UpperTheory.GalS.exists_inertia_charpoly_factor_of_tame_type N r A hC hr hT hTY w hS' hgk hL rb hrb (hall rb hrb).1
  · exact (HStarZero_iff N rb w hl ((hS hS').2 rb hrb).1 e).2 (((hS hS').2 rb hrb).2 e)
end At
def SufficientGaloisClauseAlt (D : D7) : Prop := ∀ i, _root_.Formalism.MainNotions.SumRepresentations.At.SufficientGaloisClauseAlt D.nd D.naut i
theorem galois_clause_of_sufficient_alt (D : D7) (h : _root_.Formalism.MainNotions.SumRepresentations.AdmAAlt D) (ho : _root_.Formalism.MainNotions.SumRepresentations.SufficientGaloisClauseAlt D) : ConclusionG5 D := fun i =>
  _root_.Formalism.MainNotions.SumRepresentations.At.galois_clause_of_sufficient_alt D.nd D.naut h.2.2.2.2.2.2.2.2.1 h.1.2.2 h.2.2.2.2.2.1 i (Del_holds D i) (ho i)
end Formalism.MainNotions.SumRepresentations
end
end
end

end

section

@[expose] public section



section
open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.tame_any_at_conj_of_frobenius_dense : ∀ D : D7, WildOne D → (∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k), D.nd.l i ≠ D.host.g k → ∀ s ∈ wildSet D.nd (D.nd.plOm.1 (D.naut.plGw k v)), D.nd.chi i 1 s = 1) → _root_.UpperTheory.GalS.GalAwayN D → FrobDense D → ∀ (i : D.nd.Loc) (π : D.naut.CG D.R.r) (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)), D.naut.csd π → D.naut.ralg π → _root_.UpperTheory.GalS.FullLabS D [⟨D.R.r, π, 1⟩] → IsRepOfSig D.nd D.naut i [⟨D.R.r, π, 1⟩] ρ → ∀ k : Fin 2, D.nd.l i ≠ D.host.g k → ∀ (v : D.nd.PlG k) (w : PlE D.host), IsConjPl D.host (D.naut.plGw k v) w → TameGen D.nd (D.nd.plOm.1 w) (D.nd.gam0 i w) → TameAnyAt D i [⟨D.R.r, π, 1⟩] ρ k w := by
  first | exact @_root_.GlobalTheory.TypeLeaf.ConjPlace.tame_any_at_of_is_conj_pl_tame_gen | exact _root_.GlobalTheory.TypeLeaf.ConjPlace.tame_any_at_of_is_conj_pl_tame_gen | (intros; apply _root_.GlobalTheory.TypeLeaf.ConjPlace.tame_any_at_of_is_conj_pl_tame_gen <;> assumption)
end

end
end

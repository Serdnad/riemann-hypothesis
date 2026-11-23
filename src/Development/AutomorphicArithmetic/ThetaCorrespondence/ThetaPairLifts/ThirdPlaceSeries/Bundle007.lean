module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle003
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle009
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle051
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle433
public import Formalism.SharpRestriction.LevelLetterCocycles.CongruenceAnnihilatesCharacterPart
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle004
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleOfTheorem
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle057
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle005
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle079
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle073
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeCharacterEqualityOfRealisation
public import Formalism.SharpRestriction.LevelLetterCocycles.SecondPropositionEveryLocalisation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section



section
noncomputable section
namespace GlobalTheory.ParamRep
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.LocalInv
open GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
section Twist
variable {Γ : Type} [Group Γ]
end Twist
end GlobalTheory.ParamRep
section Final
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead
theorem GlobalTheory.ParamRep.jointCond_33_rho_of_signature_adm5 : ∀ D : D7, Formalism.MainNotions.SumRepresentations.tie0 D → _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → Formalism.MainNotions.SumRepresentations.ArchimedeanSignatureMatching D → Formalism.MainNotions.SumRepresentations.adm5 D → _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → GlobalTheory.LocalInv.GoodCuspidal D.nd D.naut → XiOverO D.nd D.naut → Formalism.MainNotions.N.GlobalDatumResidualRepCondition D := by
  intro D h0 h2 _ h5 h41 hGC hXi a x _ Sig hSig hgood
  exact _root_.GlobalTheory.ParamRep.rep_at_point_alt_alt D.nd D.naut h0.1 h0.2.1 (GlobalTheory.LocalInv.weightRegular_definite D) h2 h5 h41 hGC hXi
    a x Sig hSig hgood
end Final
end
end
end

section



section
noncomputable section
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal
end
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
namespace GlobalTheory.CrysFromGTwo
end GlobalTheory.CrysFromGTwo
end
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
namespace GlobalTheory.DualTwistCrys
end GlobalTheory.DualTwistCrys
end
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
namespace GlobalTheory.CrysChiOne
variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
  {hw : w ∈ placesOver D.host.E (D.nd.l i)}
theorem rx_crys_alt_alt (h41 : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (hr : GoodR D.nd i r) (hl0 : D.nd.l i ≠ D.host.g 0) (hl1 : D.nd.l i ≠ D.host.g 1)
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (x : D.nd.X i) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x))) := by
  have h1 := (_root_.UpperTheory.GalS.g2a' ((h41 i).2.2 r hr).2.1 w hw hl0 hl1 x).1
  have h2 : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (rO D.nd i r x))) :=
    ((D.loc_tie i w hw).2.1 D.R.nV (r x) (by simpa [rO] using (hr x).1)).1.1 h1
  exact GlobalTheory.CrysCoef.isCrys_inclusion (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw (D.nbr i w hw).LL C.LL C.le
    D.R.nV _ h2
end GlobalTheory.CrysChiOne
end
section
namespace Formalism.MainNotions.N
end Formalism.MainNotions.N
end
section
namespace GlobalTheory.AbsoluteIrreducibilityOfTraceSpan
end GlobalTheory.AbsoluteIrreducibilityOfTraceSpan
end
section
end
end
end
end

section



section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
noncomputable section
namespace GlobalTheory.ResidualRankCount
section Alg
variable {Γ : Type} [Group Γ]
end Alg
section Lists
end Lists
section Psi
end Psi
theorem residual_count_alt_alt : ValRingModel → SSList → SSRankUnique → _root_.GlobalTheory.StringRepresentationDecomposition.ResidueCount := by
  intro hV hS hU D hA hRb i hg r hr x Pa R hR hcp
  classical
  obtain ⟨B, _, _, _, j, hj, hran, hmax, hmod⟩ := hV (D.nd.l i)
  obtain ⟨ψ, hψ, φ, hφ⟩ := exists_psi D.nd D.naut i j hj hran hmax
  choose ρ0 P hP using fun k : Fin Pa.length => hmod (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om) (Pa.get k).a (R k) (_root_.UpperTheory.GalS.strN' (hR k)).1
  choose L hL1 hL2 using fun k : Fin Pa.length =>
    hS (IsLocalRing.ResidueField B) (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om) (Pa.get k).a (mapRep (IsLocalRing.residue B) (ρ0 k))
  obtain ⟨rb, hrb⟩ := hRb i hg
  have hC : Formalism.MainNotions.SumRepresentations.Cheb D.nd := hA.1.1.2.2.2.2.2.2.2.2.1
  have hirr := (hA.2.1 i hg rb hrb).1
  have hr1 : 1 ≤ D.R.r := by
    have := D.R.m_add_three_le_k
    show 1 ≤ D.R.k + D.R.m - 1
    omega
  let cR : ℕ → (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin 1) (IsLocalRing.ResidueField B)) := fun c =>
    (Units.map (algebraMap (IsLocalRing.ResidueField B)
      (Matrix (Fin 1) (Fin 1) (IsLocalRing.ResidueField B))).toMonoidHom).comp
      ((Units.map (φ.comp (IsLocalRing.residue (D.nd.O i))).toMonoidHom).comp (D.nd.chi i c))
  let τ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (IsLocalRing.ResidueField B)ˣ :=
    (Units.map ((IsLocalRing.residue B).comp ψ).toMonoidHom).comp (Formalism.MainNotions.N.Glob.epsO D.nd i)⁻¹
  let L1 : List (Σ m : ℕ, Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin m) (IsLocalRing.ResidueField B)) :=
    ⟨D.R.r, mapRep φ rb⟩ :: (Finset.Icc 1 D.R.t).toList.map fun c => ⟨1, cR c⟩
  let L2 : List (Σ m : ℕ, Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin m) (IsLocalRing.ResidueField B)) :=
    (List.finRange Pa.length).flatMap fun k => (List.range (Pa.get k).d).flatMap fun a =>
      (L k).map fun p => ⟨p.1, Formalism.MainNotions.SumRepresentations.At.twGL p.2 (τ ^ a)⟩
  have h1 : ∀ p ∈ L1, 1 ≤ p.1 ∧ AbsIrrSub p.2 ⊤ := by
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact ⟨hr1, GlobalTheory.T.absIrrSub_map_of_irredOn_map_Fbar hr1 rb (D.naut.kFbar i) hirr φ⟩
    · obtain ⟨c, -, rfl⟩ := List.mem_map.1 hp
      exact ⟨le_rfl, absIrr_id le_rfl _ fun W _ => sub_fin_one W⟩
  have h2 : ∀ p ∈ L2, 1 ≤ p.1 ∧ AbsIrrSub p.2 ⊤ := by
    intro p hp
    obtain ⟨k, -, hp⟩ := List.mem_flatMap.1 hp
    obtain ⟨a, -, hp⟩ := List.mem_flatMap.1 hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    obtain ⟨hq1, hq2⟩ := hL1 k q hq
    exact ⟨hq1, absIrr_id hq1 _ fun W hW => hq2.2.2 W le_top (isInv_of_twGL _ _ W hW)⟩
  have hjψ : j.comp ψ = iotaOQ D.nd D.naut i := RingHom.ext hψ
  have hs : ∀ g, j (ψ (((Formalism.MainNotions.N.Glob.epsO D.nd i g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i)) = (epsQ D i g)⁻¹ := by
    intro g
    rw [hψ, map_units_inv]
    rfl
  have hBid : ∀ g, (((r x g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).charpoly).map ψ =
      ∏ k : Fin Pa.length, ∏ a ∈ Finset.range (Pa.get k).d,
        (((ρ0 k g : GL _ _) : Matrix (Fin (Pa.get k).a) (Fin (Pa.get k).a) B).charpoly).scaleRoots
          (ψ (((Formalism.MainNotions.N.Glob.epsO D.nd i g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) ^ a) := by
    intro g
    apply Polynomial.map_injective j hj
    rw [Polynomial.map_map, hjψ, ← Matrix.charpoly_map]
    show ((mapRep (iotaOQ D.nd D.naut i) (r x) g : GL _ _) :
      Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))).charpoly = _
    rw [hcp g, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Polynomial.map_prod]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [map_scaleRoots _ _ _ (by rw [(Matrix.charpoly_monic _).leadingCoeff, map_one]; exact one_ne_zero),
      ← Matrix.charpoly_map, map_pow, hs, hP k g, Matrix.charpoly_mul_comm, ← mul_assoc, Units.inv_mul, one_mul]
  have hkA : ∀ g, (((r x g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).charpoly).map
        ((IsLocalRing.residue B).comp ψ) =
      ∏ k : Fin Pa.length, ∏ a ∈ Finset.range (Pa.get k).d,
        (((mapRep (IsLocalRing.residue B) (ρ0 k) g : GL _ _) :
          Matrix (Fin (Pa.get k).a) (Fin (Pa.get k).a) (IsLocalRing.ResidueField B)).charpoly).scaleRoots
          ((τ g : IsLocalRing.ResidueField B) ^ a) := by
    intro g
    rw [← Polynomial.map_map, hBid g, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Polynomial.map_prod]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [map_scaleRoots _ _ _ (by rw [(Matrix.charpoly_monic _).leadingCoeff, map_one]; exact one_ne_zero),
      ← Matrix.charpoly_map, map_pow]
    all_goals rfl
  have hcpL1 : ∀ g, (L1.map fun p => ((p.2 g : GL _ _) :
        Matrix (Fin p.1) (Fin p.1) (IsLocalRing.ResidueField B)).charpoly).prod =
      (((r x g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).charpoly).map
        ((IsLocalRing.residue B).comp ψ) := by
    intro g
    have hφ' : φ.comp (IsLocalRing.residue (D.nd.O i)) = (IsLocalRing.residue B).comp ψ := RingHom.ext hφ
    have hf : (((r x g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).map
        (IsLocalRing.residue (D.nd.O i))).charpoly = _ :=
      (Formalism.MainNotions.SumRepresentations.rhobar_fac D.nd r hC hr rb hrb x g).symm
    rw [← hφ', ← Polynomial.map_map, ← Matrix.charpoly_map, hf, Polynomial.map_mul, Polynomial.map_prod]
    simp only [L1, List.map_cons, List.prod_cons, List.map_map]
    congr 1
    · exact Matrix.charpoly_map _ φ
    · rw [Finset.prod_map_toList]
      refine Finset.prod_congr rfl fun c _ => ?_
      show (algebraMap (IsLocalRing.ResidueField B) (Matrix (Fin 1) (Fin 1) (IsLocalRing.ResidueField B))
        (φ (IsLocalRing.residue (D.nd.O i) ((D.nd.chi i c g : (D.nd.O i)ˣ) : D.nd.O i)))).charpoly = _
      rw [charpoly_scal, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  have hcpL2 : ∀ g, (L2.map fun p => ((p.2 g : GL _ _) :
        Matrix (Fin p.1) (Fin p.1) (IsLocalRing.ResidueField B)).charpoly).prod =
      ∏ k : Fin Pa.length, ∏ a ∈ Finset.range (Pa.get k).d,
        (((mapRep (IsLocalRing.residue B) (ρ0 k) g : GL _ _) :
          Matrix (Fin (Pa.get k).a) (Fin (Pa.get k).a) (IsLocalRing.ResidueField B)).charpoly).scaleRoots
          ((τ g : IsLocalRing.ResidueField B) ^ a) := by
    intro g
    simp only [L2]
    rw [prod_map_flatMap, Fin.prod_univ_def]
    congr 1
    refine List.map_congr_left fun k _ => ?_
    rw [prod_map_flatMap, prod_range_list]
    congr 1
    refine List.map_congr_left fun a _ => ?_
    rw [hL2 k g, scaleRoots_list_prod]
    simp only [List.map_map]
    congr 1
    refine List.map_congr_left fun q _ => ?_
    show ((Formalism.MainNotions.SumRepresentations.At.twGL q.2 (τ ^ a) g : GL _ _) :
      Matrix (Fin q.1) (Fin q.1) (IsLocalRing.ResidueField B)).charpoly = _
    rw [charpoly_twGL, MonoidHom.pow_apply, Units.val_pow_eq_pow_val]
    rfl
  have h3 : ∀ g, (L1.map fun p => ((p.2 g : GL _ _) :
        Matrix (Fin p.1) (Fin p.1) (IsLocalRing.ResidueField B)).charpoly).prod =
      (L2.map fun p => ((p.2 g : GL _ _) :
        Matrix (Fin p.1) (Fin p.1) (IsLocalRing.ResidueField B)).charpoly).prod := fun g => by
    rw [hcpL1 g, hcpL2 g, hkA g]
  have hrk := hU (IsLocalRing.ResidueField B) (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om) L1 L2 h1 h2 h3
  refine ⟨fun k => (((L k).map fun p => p.1 : List ℕ) : Multiset ℕ), fun k => ⟨?_, ?_⟩, ?_⟩
  · show (((L k).map fun p => p.1 : List ℕ) : Multiset ℕ).sum = _
    rw [Multiset.sum_coe, ← (charpoly_list_monic (L k) 1).2, ← hL2 k 1, Matrix.charpoly_natDegree_eq_dim,
      Fintype.card_fin]
  · intro a ha
    rw [Multiset.mem_coe, List.mem_map] at ha
    obtain ⟨p, hp, rfl⟩ := ha
    exact (hL1 k p hp).1
  · have e1 : ((L1.map fun p => p.1 : List ℕ) : Multiset ℕ) = D.R.r ::ₘ Multiset.replicate D.R.t 1 := by
      have : (L1.map fun p => p.1) = D.R.r :: List.replicate D.R.t 1 := by
        simp only [L1, List.map_cons, List.map_map, List.cons.injEq, true_and]
        refine List.eq_replicate_iff.2 ⟨by simp, fun b hb => ?_⟩
        obtain ⟨c, -, rfl⟩ := List.mem_map.1 hb
        rfl
      rw [this, ← Multiset.cons_coe, Multiset.coe_replicate]
    have e2 : ((L2.map fun p => p.1 : List ℕ) : Multiset ℕ) =
        ∑ k, (Pa.get k).d • (((L k).map fun p => p.1 : List ℕ) : Multiset ℕ) := by
      simp only [L2, List.map_flatMap, List.map_map, Function.comp_def, coe_flatMap, sum_range_const]
      rw [Fin.sum_univ_def]
    show ∑ k, (Pa.get k).d • (((L k).map fun p => p.1 : List ℕ) : Multiset ℕ) = _
    rw [← e2, ← hrk, e1]
end GlobalTheory.ResidualRankCount
end
end
end

section



section
noncomputable section
namespace GlobalTheory.EigenPoint
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
section Alg
variable {Γ : Type} [Group Γ] {K : Type} [Field K]
end Alg
variable (D : D7) (i : D.nd.Loc)
theorem eq_one_twist_t_of_mulVec_eigen (_h3 : _root_.GlobalTheory.StringRepresentationDecomposition.HeckeCharEqOfLAdicRealisation') (h4 : _root_.GlobalTheory.StringRepresentationDecomposition.MuCharacterCondition) (hA : _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D) (hg : HG D.nd D.naut i)
    (p : Part D.naut.CG) (Rk : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin p.a) (Qbar (D.nd.l i)))
    (hR : UpperTheory.GalS.IsStringRepN D i p Rk) (ha : p.a = 1) (hd : p.d = D.R.t) (u : Fin p.a → Qbar (D.nd.l i)) (hu0 : u ≠ 0)
    (hu : ∀ g, ((Rk g : GL _ _) : Matrix (Fin p.a) (Fin p.a) (Qbar (D.nd.l i))).mulVec u =
      iotaOQ D.nd D.naut i (chi1 D.nd i g) • u) :
    p = ⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩ := by
  have h3 := _root_.GlobalTheory.HeckeCharacterEquality.hecke_character_equality_of_realisation
  rcases p with ⟨a, π, d⟩
  dsimp only at ha hd
  subst ha hd
  have hu00 : u 0 ≠ 0 := fun h => hu0 (funext fun j => by rw [Fin.fin_one_eq_zero j]; exact h)
  have h00 : ∀ g, ((Rk g : GL _ _) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0 =
      iotaOQ D.nd D.naut i (chi1 D.nd i g) := fun g => by
    have := congrFun (hu g) 0
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one, Pi.smul_apply, smul_eq_mul] at this
    exact mul_right_cancel₀ hu00 this
  have hπ := h3 D hA i π (D.naut.tw (D.naut.muC i) D.naut.etaTinv) _ Rk hR.2.2 (h4 D hA i hg Rk h00)
  subst hπ
  rfl
end GlobalTheory.EigenPoint
end
end
end

section



section
noncomputable section
namespace GlobalTheory.HeckeCharacterEquality
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
theorem sixth_character_equality_holds_alt_alt : _root_.GlobalTheory.StringRepresentationDecomposition.HeckeCharEqOfLAdicRealisation' := by
  intro D hA i χ χ' s ρ h h'
  have hAN := hA.1.1.2.2.2.2.2.2.1
  have hloc : ∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.locG χ w = D.naut.locG χ' w := by
    intro w hw
    have e := congrArg (fun a => D.naut.lpTw a (-s)) ((h w hw).symm.trans (h' w hw))
    simpa [D.naut.lpTw_add, D.naut.lpTw_zero] using e
  have hp := hAN [⟨1, χ, 1⟩] [⟨1, χ', 1⟩] (by simp) (by simp) (by
    have hfin := placesOver_finite_joint_conditions_zpowers D.host.E (D.nd.l i) (D.nd.lPrime i).out.ne_zero
    filter_upwards [hfin.compl_mem_cofinite] with w hw
    simp only [isoLoc, spehLoc, List.foldr]
    rw [hloc w hw])
  have := List.perm_singleton.1 hp
  simpa using this
end GlobalTheory.HeckeCharacterEquality
end
end
end

section



section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations
namespace GlobalTheory
theorem lemma_open_of_integrality_alt (D : D7) (h41 : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D) : TypePrimeCongruences.CongruenceModules.SupplierRemainingLemmas D :=
  fun i _ _ _ r ρ hr =>
    ⟨LargeLevelLemmas.span_lemma_clause i r (_root_.Formalism.MainNotions.N.galois_condition_one_of_alt D i r h41 hr),
      fun π _ _ => ⟨LargeLevelLemmas.eigenspace_lemma_clause i r ρ π, LargeLevelLemmas.relation_lemma_clause i r ρ π⟩⟩
theorem typePrimeCongruences_forall : ∀ D : D7, _root_.Formalism.MainNotions.TypePrimeCongruences.TypePrimeLemmasStatement D :=
  fun D hA => TypePrimeCongruences.CongruenceModules.supplier_of_choice_and_lemmas D hA.2.2.2 (_root_.GlobalTheory.lemma_open_of_integrality_alt D hA.2.1)
end GlobalTheory
end
end

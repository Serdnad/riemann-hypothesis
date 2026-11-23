module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle003
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyEqOfEqOnDense
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle080
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SixthDecomposition
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.HeckeCharacterEqualityOfRealisation
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.EtaPiece
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.RhoBar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle797
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle086
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle304
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle456
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.CardRootsBar
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Bundle005
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Bundle008
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.ConstituentConditionAtDistinguishedPrime
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle026
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle694
public import Development.DiscreteGroups.GlobalIrreducibility.IneEqOfHasGreenLe
public import Development.DiscreteGroups.GlobalIrreducibility.LocTypeOfSerParamLe
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle705
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle027
public import Development.DiscreteGroups.GlobalIrreducibility.SerLocOfTiesLe
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section



section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
noncomputable section
namespace GlobalTheory.StringDecomp
open Formalism.MainNotions.SumRepresentations.At Topology
section Alg
variable {Γ : Type} [Group Γ] {K : Type} [Field K]
end Alg
end GlobalTheory.StringDecomp
namespace GlobalTheory.StringDecomp
open Formalism.MainNotions.SumRepresentations.At Topology
section Frob
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}
end Frob
end GlobalTheory.StringDecomp
namespace GlobalTheory.StringDecomp
open Formalism.MainNotions.SumRepresentations.At Topology
section Eps
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)
end Eps
end GlobalTheory.StringDecomp
namespace GlobalTheory.StringDecomp
open Formalism.MainNotions.SumRepresentations.At Topology
theorem exists_stringRep_alt_alt (D : D7) (hA : _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D) (i : D.nd.Loc) (P : D.naut.AV i)
    (Pa : List (Part D.naut.CG)) (hBC : IsBCV D.nd D.naut i P Pa) (p : Part D.naut.CG) (hp : p ∈ Pa) :
    ∃ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin p.a) (Qbar (D.nd.l i)), UpperTheory.GalS.IsStringRepN D i p ρ := by
  obtain ⟨⟨⟨hLP, hAut, hGal⟩, -, -, hG, -, -, -⟩, -⟩ := hA.1
  obtain ⟨ha, hd, hc⟩ := hBC.1 p hp
  have hw := GlobalTheory.BCGal.galois_relation_away_from_l D.nd D.naut i hLP hAut hGal (_root_.UpperTheory.GalS.weak' hG) ha p.π hc
    ((p.d : ℤ) - 1 + p.a - D.R.nV) fun τ => by
    have hW : (D.naut.infWt i τ).Nodup ∧
        ∀ z ∈ D.naut.infWt i τ, ∃ k : ℤ, z = (k : ℂ) + ((D.R.nV : ℂ) - 1) / 2 := by
      rw [D.nbc.embAV_inf i P]
      exact D.nbc.infW_alg _ _ τ
    have hle : (D.naut.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - ((0 : ℕ) : ℂ))) ≤ D.naut.infWt i τ := by
      rw [← hBC.2.2.2.2.2 τ]
      refine le_trans (List.single_le_sum (fun _ _ => Multiset.zero_le _) _ ?_)
        (List.single_le_sum (fun _ _ => Multiset.zero_le _) _ (List.mem_map_of_mem hp))
      exact List.mem_map.2 ⟨0, by simp; exact ⟨0, by omega, by simp⟩, by simp⟩
    refine ⟨(Multiset.nodup_of_le hle hW.1).of_map _, fun z hz => ?_⟩
    obtain ⟨n, hn⟩ := hW.2 _ (Multiset.mem_of_le hle (Multiset.mem_map_of_mem _ hz))
    exact ⟨n, by push_cast at hn ⊢; linear_combination hn⟩
  obtain ⟨ρ, hcont, hss, hwd⟩ := hw
  refine ⟨ρ, hcont, hss, fun w hwl => ?_⟩
  convert hwd w hwl using 2
  push_cast
  ring_nf
theorem stringDecomp_holds_alt_alt :
    ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D → ∀ (i : D.nd.Loc) (x : D.nd.X i) (P : D.naut.AV i)
    (Pa : List (Part D.naut.CG)), D.naut.ptV i P = some x → IsBCV D.nd D.naut i P Pa →
    ∀ r, GoodR D.nd i r →
    ∃ R : ∀ k : Fin Pa.length, Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin (Pa.get k).a) (Qbar (D.nd.l i)),
      (∀ k, UpperTheory.GalS.IsStringRepN D i (Pa.get k) (R k)) ∧
      ∀ g, ((mapRep (iotaOQ D.nd D.naut i) (r x) g : GL _ _) :
          Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))).charpoly =
        ∏ k : Fin Pa.length, ∏ a ∈ Finset.range (Pa.get k).d,
          (((R k g : GL _ _) : Matrix (Fin (Pa.get k).a) (Fin (Pa.get k).a) (Qbar (D.nd.l i))).charpoly).scaleRoots
            ((epsQ D i g)⁻¹ ^ a) := by
  intro D hA i x P Pa hx hBC r hr
  have hC := hA.1.1.2.2.2.2.2.2.2.2.1
  have hex : ∀ p : Part D.naut.CG, ∃ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin p.a) (Qbar (D.nd.l i)),
      p ∈ Pa → UpperTheory.GalS.IsStringRepN D i p ρ := by
    intro p
    by_cases hp : p ∈ Pa
    · obtain ⟨ρ, hρ⟩ := _root_.GlobalTheory.StringDecomp.exists_stringRep_alt_alt D hA i P Pa hBC p hp
      exact ⟨ρ, fun _ => hρ⟩
    · exact ⟨1, fun h => absurd h hp⟩
  choose Rp hRp using hex
  refine ⟨fun k => Rp (Pa.get k), fun k => hRp _ (List.get_mem Pa k), ?_⟩
  have hrk : rkL Pa = D.R.nV := (rkL_eq Pa).trans hBC.2.2.1
  have hcL := cont_listRep Rp _ (cont_epsQU_inv D.nd D.naut i) Pa (fun p hp => (hRp p hp).1)
  obtain ⟨ρ', hρ'⟩ := exists_cast hrk (listRep Rp (epsQU D.nd D.naut i)⁻¹ Pa)
  have hQ := GlobalTheory.NRows.isHeckeGaloisQ_of_isHeckeGalois D i x (r x) (hr x)
  have hfin : (placesOver D.host.E (D.nd.l i) ∪ ↑(D.nd.S i) ∪ ↑(D.nd.Q i) : Set (PlE D.host)).Finite :=
    ((placesOver_finite' D.host.E (D.nd.l i) (D.nd.lPrime i).out.ne_zero).union (D.nd.S i).finite_toSet).union
      (D.nd.Q i).finite_toSet
  have key := GlobalTheory.charpoly_eq_of_eqOn_dense
    (fun g => ((mapRep (iotaOQ D.nd D.naut i) (r x) g : GL _ _) :
      Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))))
    (fun g => ((ρ' g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))))
    hQ.1 (hρ'.1 hcL) _ (dense_iff_closure_eq.2 (hC _ hfin)) (by
      rintro σ ⟨w, hw, hsp, B, hB, hσ⟩
      simp only [Set.mem_union, not_or, Finset.mem_coe] at hw
      have hso : SplitOut D.nd i w := ⟨hsp, hw.1.1, hw.1.2, hw.2⟩
      show _ = _
      rw [hQ.2.2 w hso B σ hB hσ, hρ'.2 σ, charpoly_listRep]
      apply Polynomial.map_injective (D.naut.iotaQC i).toRingHom (D.naut.iotaQC i).injective
      rw [Polynomial.map_map, show (D.naut.iotaQC i).toRingHom.comp (iotaOQ D.nd D.naut i) =
        ((D.naut.iotaQC i).toRingHom.comp (D.naut.iotaQ i)).comp (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))
        from rfl, D.naut.pt_loc i P x hx w hso, ← hBC.2.2.2.1 w hsp]
      exact (iso_poly i w hso.2.1 B σ hB hσ Rp _ _ (epsQU_frob D.nd D.naut i hso.2.1 hB hσ) Pa
        (fun p hp => (hRp p hp).1) (fun p hp => ((hRp p hp).2.2 w hso.2.1).eq_of_unr ((D.naut.unr_tw _ _).2
          (UpperTheory.GalN.unr_part Pa (iso_unr i hBC w hso) p hp (hBC.1 p hp).2.1))) (iso_unr i hBC w hso)).symm)
  intro g
  rw [key g, hρ'.2 g, charpoly_listRep, epsQU_inv_val, ← prod_get]
  rfl
end GlobalTheory.StringDecomp
end
end
end

section



section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal
noncomputable section
namespace UpperTheory.GalS
theorem de_rham_points_weight_jumps_alt (D : D7) (h0 : SumRepresentations.tie0 D) (h1 : SumRepresentations.adm1 D) (h2' : _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D) (h5 : SumRepresentations.adm5 D)
    (hC : UpperTheory.GalC.CutRec D) : (∀ i r, GoodR D.nd i r → G2a D.nd D.naut i r) ∧ DeRhamJumpsDistinctCondition D := by
  have h2 := _root_.UpperTheory.GalS.weak' h2'
  have all : ∀ i r, GoodR D.nd i r → ∀ x, ∀ w ∈ placesOver D.host.E (D.nd.l i),
      D.naut.IsdRW i (mapRep (iotaOQ D.nd D.naut i) (r x)) w ∧
      ∀ τ, InducesW D.nd i τ w → D.naut.jumpsW i (mapRep (iotaOQ D.nd D.naut i) (r x)) τ = D.naut.locAutHodgeTateWeightsLevelZero i τ := by
    intro i r hr x w hw
    obtain ⟨P, hP⟩ := D.naut.pt_surj i x
    obtain ⟨Pa, hB⟩ := h1 i P
    have hn : Nc D.nd D.naut (isoLoc D.nd D.naut Pa w) := by
      have hg : ∀ k, D.nd.l i = D.host.g k → Nc D.nd D.naut (isoLoc D.nd D.naut Pa w) := fun k hk => by
        have hw' : w ∈ placesOver D.host.E (D.host.g k) := hk ▸ hw
        rw [hB.2.2.2.1 w (GlobalTheory.DepthZeroType.isSplitPl_of_over D k w hw')]
        exact hC i P (by rw [hP]; simp) k w hw'
      by_cases a : D.nd.l i = D.host.g 0
      · exact hg 0 a
      by_cases b : D.nd.l i = D.host.g 1
      · exact hg 1 b
      exact .of_unr (Parts.iso_unr_l D i P Pa w hB hw a b)
    have h := compatR D h0 h2 h5 i r hr x P Pa hP hB w hw hn
    exact ⟨h.1, h.2.2⟩
  exact ⟨fun i r hr => (Parts.crys_unram_of_lgc D h0 h1 (Parts.lgc D h0 h2 h5) i r fun x => GlobalTheory.T.isHeckeGaloisQ_of_isHeckeGalois' D i x (r x) (hr x)).1,
    fun i r hr _ w hw x => all i r hr x w hw, fun i r hr => Parts.constituentCondition_of_hodgeJumps D h0 i r hr (all i r hr)⟩
end UpperTheory.GalS
end
end
end

section



section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open Polynomial
open GlobalTheory.TypeAbove
noncomputable section
namespace UpperTheory.GalS
open UpperTheory.Lit.Car (IneAb comm_le_ine)
theorem stepType_alt : _root_.GlobalTheory.Pass.stepType_proof_tyz := by
  intro D P hDZ h0 h1 h2' h5 i k hl r hr x PI hPI v τ hτ hsq hroot
  have h2 := _root_.UpperTheory.GalS.weak' h2'
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hnc := nc_of_label P hDZ h1 i k v PI τ hτ hsq hroot
  obtain ⟨u, hu, hm0, hlab, hconj⟩ := hDZ i k v PI τ hτ hsq hroot
  refine ⟨u, hu, ?_⟩
  have hcard : ∀ a : (ZMod (D.host.g k))[X], Multiset.card (Formalism.CyclotomicNorms.rootsBar a) = a.natDegree := fun a => by
    unfold Formalism.CyclotomicNorms.rootsBar
    rw [← (IsAlgClosed.splits _).natDegree_eq_card_roots, natDegree_map]
  have hroot0 : ∀ y ∈ Formalism.CyclotomicNorms.rootsBar ((P.lz k).lab τ * (X - C (u : ZMod (D.host.g k))) ^ D.R.t), y ≠ 0 := by
    rintro y hy rfl
    unfold Formalism.CyclotomicNorms.rootsBar at hy
    have h := isRoot_of_mem_roots hy
    rw [IsRoot.def, ← coeff_zero_eq_eval_zero, coeff_map, map_eq_zero, mul_coeff_zero, coeff_zero_eq_eval_zero (_ ^ _)] at h
    rcases mul_eq_zero.1 h with h | h
    · exact ((P.lz k).lab_spec τ).2.2 h
    · simp at h
  have key : ∀ w, w ∈ placesOver D.host.E (D.host.g k) → IsSplitPl D.host w → Nc D.nd D.naut (D.naut.locV i PI w) →
      D.naut.mono0 (D.naut.locV i PI w) →
      (D.naut.items₂ k w (D.naut.locV i PI w)).natDegree = D.R.nV →
      (∀ y ∈ Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w (D.naut.locV i PI w)), y ≠ 0) →
      D.naut.IsdRW i (mapRep (iotaOQ D.nd D.naut i) (r x)) w ∧
      D.naut.mono0 (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (r x)) w) ∧
      ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w),
        D.naut.inePol (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (r x)) w) σ =
          ((Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w (D.naut.locV i PI w))).map
            fun y => X - C (P.om k w y σ)).prod := by
    intro w hw hs hn hm hdeg hnz
    have hwl : w ∈ placesOver D.host.E (D.nd.l i) := hl ▸ hw
    obtain ⟨Pa, hB⟩ := h1 i PI
    obtain ⟨hdR, heq, -⟩ := compatR D h0 h2 h5 i r hr x PI Pa hPI hB w hwl (by rw [hB.2.2.2.1 w hs]; exact hn)
    rw [hB.2.2.2.1 w hs] at heq
    have hdim : D.naut.lpDim (D.naut.locV i PI w) = D.R.nV := by
      have h := D.naut.wdOf_dim i (mapRep (iotaOQ D.nd D.naut i) (r x)) w
      rwa [heq.dim, D.naut.lpDim_tw] at h
    refine ⟨hdR, ?_, fun σ hσ => ?_⟩
    · refine heq.mono ?_
      rw [D.naut.monomial_twist_iff]; exact hm
    · have hab : IneAb D.nd D.naut (D.naut.lpTw (D.naut.locV i PI w) ((1 - (D.R.nV : ℝ)) / 2)) := fun s hs' => by
        rw [D.naut.inePol_tw _ _ s (comm_le_ine w hs'), D.naut.lpDim_tw,
          P.inertiaCharpoly_eigenvalues k w hw _ (hdeg.trans hdim.symm) s (comm_le_ine w hs'),
          Multiset.map_congr rfl (fun y hy => by rw [comm_triv _ (P.om k w y) (P.om_one k w y (hnz y hy)) (P.om_mul k w y (hnz y hy)) s hs', C_1]),
          Multiset.map_const', Multiset.prod_replicate, hcard, hdeg, hdim]
      rw [heq.ine ⟨(D.naut.monomial_twist_iff _ _).2 hm, hab⟩ σ hσ, D.naut.inePol_tw _ _ σ hσ]
      exact P.inertiaCharpoly_eigenvalues k w hw _ (hdeg.trans hdim.symm) σ hσ
  intro w M hwM
  rcases hwM with ⟨rfl, rfl⟩ | ⟨hc, rfl⟩
  · have hdeg : (D.naut.items₂ k (D.naut.plGw k v) (D.naut.locV i PI (D.naut.plGw k v))).natDegree = D.R.nV := by
      rw [hlab, ((P.lz k).lab_spec τ).1.natDegree_mul ((monic_X_sub_C _).pow _),
        ((P.lz k).lab_spec τ).2.1, (monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one]
      rfl
    have h := key _ (D.naut.plGw_over k v) (GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k v) (hnc _ (Or.inl rfl)) hm0 hdeg (by rw [hlab]; exact hroot0)
    rw [hlab] at h
    exact h
  · obtain ⟨hw, hs⟩ := conj_over_split D (D.naut.plGw_over k v) (GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k v) hc
    obtain ⟨hm, hdeg, hroots⟩ := hconj w hc
    have h := key w hw hs (hnc w (Or.inr hc)) hm hdeg (by
      rw [hroots]
      intro y hy
      obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hy
      exact inv_ne_zero (hroot0 z hz))
    rw [hroots] at h
    exact h
end UpperTheory.GalS
end
end
end

section



section
noncomputable section
namespace DiscreteGroups.sglob.DzType.Rt
open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders GlobalTheory.TypeLeaf GlobalTheory.SerSys GlobalTheory.SerSys.Bridge
open scoped Classical
attribute [local instance] GlobalTheory.SerSys.Bridge.factT
theorem serLocLe_of_alt (D : D7) (L : ∀ k, LabelDatum (D.host.g k)) (rc : Corr D) (hG : Green)
    (hL : LabTie D L) (hU : IneUnr D) (hC : _root_.GlobalTheory.SerSys.LocalCompatibility D rc) (hP : LabParamLe D.R.nV D L rc) : SerLoc D :=
  have hS : ∀ k, (OfLabel.ofLabel (L k) (five_le D k) hG).IsOf (L k) := fun _ _ _ => rfl
  GlobalTheory.SerLocal.serLoc D _ (hL.sysTie hS) hU (_root_.DiscreteGroups.sglob.DzType.Rt.locType_of_labTie_locComp_labParamLe hL hS hC hP)
theorem serLoc_of_tame_param_le (D : D7) (L : ∀ k, LabelDatum (D.host.g k)) (rc : Corr D) (hG : Green)
    (hL : LabTie D L) (hU : IneUnr D) (hC : _root_.GlobalTheory.SerSys.LocalCompatibility D rc)
    (h1 : ∀ k v, TameGen.SupportCompat (fun a => D.naut.inePol a (D.ntypes.tg k v))
      (fun π : GLRep _ => rc k v π.1 π.2))
    (h2 : ∀ k, TameGen.DepthZeroCuspidal (D.host.g k))
    (h3 : ∀ k v, TameParamLe D.R.nV (L k) (fun a => D.naut.inePol a (D.ntypes.tg k v))
      (fun π : GLRep _ => rc k v π.1 π.2)) : SerLoc D :=
  _root_.DiscreteGroups.sglob.DzType.Rt.serLocLe_of_alt D L rc hG hL hU hC (labParamLe_of D L rc hG h1 h2 h3)
end DiscreteGroups.sglob.DzType.Rt
end
end
end

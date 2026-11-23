module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.RhoBar
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle059
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle006
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle192
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.GoodRCongr
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Bundle003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Bundle002
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle016
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Development.DiscreteGroups.GlobalIrreducibility.LocTypeOfSerParamLe
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle026
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle009
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008

@[expose] public section

section



section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
noncomputable section
namespace UpperTheory.GalS
theorem lgc_of_cut'_alt (D : D7) (hA : _root_.Formalism.MainNotions.SumRepresentations.AdmAAlt D) (hC : UpperTheory.GalC.CutRec D) : LGCN D := by
  intro i r hr w hw x
  have ht := hA.1
  have h1 := hA.2.2.1
  have h2 := _root_.UpperTheory.GalS.weak' hA.2.2.2.1
  have h5 := hA.2.2.2.2.2.2
  obtain ⟨P, hP⟩ := D.naut.pt_surj i x
  obtain ⟨Pa, hPa⟩ := h1 i P
  obtain ⟨ρ, hc, hss, hwd, -⟩ := isoRep D ht h2 i P Pa hPa
  obtain ⟨Pm, hPm⟩ := rep_conj D h5 i r hr x P Pa hP hPa ρ hc hss hwd
  have hsp := D.nd.SQ_split i w hw
  have hwl := D.nd.SQ_l i w hw
  have rel : RelW D.nd D.naut (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (r x)) w)
      (D.naut.lpTw (D.naut.locV i P w) ((1 - (D.R.nV : ℝ)) / 2)) := by
    rw [← hPa.2.2.2.1 w hsp, ((ht.2.2.2.2.2 i).2.1 _ ρ _ hc Pm hPm).2.1 w (Or.inl hwl)]
    exact hwd w hwl
  refine ⟨P, hP, rel, (nc_tw _ _).2 ?_⟩
  have hd : D.naut.lpDim (D.naut.locV i P w) = D.R.nV := by
    rw [← D.naut.lpDim_tw _ ((1 - (D.R.nV : ℝ)) / 2), ← rel.dim, D.naut.wdOf_dim]
  have hne : D.naut.ptV i P ≠ none := by rw [hP]; simp
  rcases hw with hS | hQ
  · rcases ((D.nd.S_def i w).1 hS).1 with h | h | h
    · exact hC i P hne 0 w h
    · exact hC i P hne 1 w h
    · refine nonCritical_localParam_of_full_dim D hA.2.2.2.2.2.1 i P w (Or.inl hS) (Or.inr ⟨hS, ?_⟩) hd
      split_ifs at h with he
      · exact Or.inr ⟨he, h⟩
      · exact Or.inl h
  · exact nonCritical_localParam_of_full_dim D hA.2.2.2.2.2.1 i P w (Or.inr hQ) (Or.inl hQ) hd
end UpperTheory.GalS
end
end
end

section



section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
theorem UpperTheory.GalS.galIsoN_of_tie0_adm2_adm7 : ∀ D : D7, Formalism.MainNotions.SumRepresentations.tie0 D → _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D →
    ∀ i, UpperTheory.GalS.GalIsoN D.nd D.naut i := by
  intro D hT hG _ i P Pa hB
  obtain ⟨ρ, c, s, o, -⟩ := UpperTheory.GalS.isoRep D hT (_root_.UpperTheory.GalS.weak' hG) i P Pa hB
  exact ⟨ρ, c, s, o⟩
end
end

section



section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open GlobalTheory.BCPerm
noncomputable section
namespace UpperTheory.GalS
theorem bcPerm_alt : _root_.GlobalTheory.BCPerm.mainTheorem := by
  intro D ht h2 h5 i x P0 PI Pa0 Pa hx hx' hB0 hB
  have hG : GalIsoN D.nd D.naut i := by
    intro P Pb hPb
    obtain ⟨ρ, hc, hss, hw, -⟩ := isoRep D ht (_root_.UpperTheory.GalS.weak' h2) i P Pb hPb
    exact ⟨ρ, hc, hss, hw⟩
  have hC : GlobalTheory.RowTie.ChebSplit D.nd := by
    intro S
    rw [dense_iff_closure_eq]
    exact h5.2.2.1 (S : Set (PlE D.host)) S.finite_toSet
  have hAN : GlobalTheory.RowCopy.IsobaricDiscreteSelfDualStrongMultiplicityOne D.nd D.naut := h5.2.1
  have hS := splitBC_of_galIso D.R D.host D.what₂ D.nd D.naut i hG hC hAN
  have hd0 : (if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde) ≠ 0 := by
    split_ifs
    exacts [D.host.pde'_prime.ne_zero, D.host.pde_prime.ne_zero]
  have hfin : (placesOver D.host.E (D.nd.l i) ∪ (D.nd.S i : Set (PlE D.host)) ∪ (D.nd.Q i : Set (PlE D.host)) ∪
      placesOver D.host.E (D.host.g 0) ∪ placesOver D.host.E (D.host.g 1) ∪
      placesOver D.host.E (if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde)).Finite := by
    refine (((((GlobalTheory.RowTie.placesOver_finite_of_ne_zero _ _ (D.nd.lPrime i).out.ne_zero).union
      (D.nd.S i).finite_toSet).union (D.nd.Q i).finite_toSet).union
      (GlobalTheory.RowTie.placesOver_finite_of_ne_zero _ _ (D.host.g_prime 0).ne_zero)).union
      (GlobalTheory.RowTie.placesOver_finite_of_ne_zero _ _ (D.host.g_prime 1).ne_zero)).union
      (GlobalTheory.RowTie.placesOver_finite_of_ne_zero _ _ hd0)
  have hev : ∀ᶠ v in Filter.cofinite, IsSplitPl D.host v → D.naut.locV i P0 v = D.naut.locV i PI v := by
    rw [Filter.eventually_cofinite]
    refine hfin.subset fun v hv => ?_
    by_contra hn
    simp only [Set.mem_union, Finset.mem_coe, not_or] at hn
    obtain ⟨⟨⟨⟨⟨hl, hSv⟩, hQv⟩, hg0⟩, hg1⟩, hdv⟩ := hn
    refine hv fun hsp => GlobalTheory.RowTie.locV_eq_of_pt D.nd D.naut i hx hx' ⟨hsp, hl, hSv, hQv⟩ ?_ hdv
    intro k
    fin_cases k
    exacts [hg0, hg1]
  exact hS P0 PI hev Pa0 Pa hB0 hB
end UpperTheory.GalS
end
end
end

section



section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition Topology
open GlobalTheory.TameEig
noncomputable section
namespace UpperTheory.GalS
theorem eigPd_holds_alt : _root_.GlobalTheory.TameEig.eigPd_holds_tyz := by
  intro D hA hLGC _ i _ w hS hw rb hrb hroot
  have hC : Formalism.MainNotions.SumRepresentations.Cheb D.nd := hA.2.2.2.2.2.2.2.2.1
  have hDel := Formalism.MainNotions.SumRepresentations.Del_holds D i
  have hq : (if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde).Prime := by
    split_ifs
    · exact D.host.pde'_prime
    · exact D.host.pde_prime
  have hq15 : (if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde) % 15 = 1 := by
    split_ifs
    · exact D.host.pde_mod.2
    · exact D.host.pde_mod.1
  have hne := residue_ne_one D.nd i w hS _ hq hq15 hw (hDel w hS hw)
  have hcond : w ∈ D.nd.Q i ∨ (Formalism.MainNotions.SumRepresentations.At.Del D.nd i ∧ (w ∈ placesOver D.host.E D.host.pde ∨
      (D.nd.l i = D.host.pde ∧ w ∈ placesOver D.host.E D.host.pde'))) := by
    refine Or.inr ⟨hDel, ?_⟩
    by_cases hlp : D.nd.l i = D.host.pde
    · rw [if_pos hlp] at hw
      exact Or.inr ⟨hlp, hw⟩
    · rw [if_neg hlp] at hw
      exact Or.inl hw
  have x : D.nd.X i := Classical.choice (D.nd.neX i)
  have hQ : ∀ x, ∃ ρ, Formalism.MainNotions.SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ := fun x => by
    obtain ⟨P, hP⟩ := D.naut.pt_surj i x
    obtain ⟨Pa, hPa⟩ := hA.2.2.1 i P
    obtain ⟨ρ, h1, h2, h3, -⟩ := isoRep D hA.1 (_root_.UpperTheory.GalS.weak' hA.2.2.2.1) i P Pa hPa
    exact ⟨ρ, heckeQ D i x P Pa hP hPa ρ h1 h2 h3⟩
  choose rq hrq using hQ
  obtain ⟨r, hr⟩ := Formalism.MainNotions.SumRepresentations.exists_GoodR D.nd D.naut hA.2.1 i ⟨rq, hrq⟩
  have hL := hLGC i r hr w (Or.inl hS)
  have hs := _root_.Formalism.MainNotions.SumRepresentations.splitI_of_monodromyInertiaType_of_lgCatN D.nd r D.naut hr hA.2.2.2.2.2.1 w (Or.inl hS) hcond hL x
  have hg := D.nd.locNd_chebotarevPlace_mem i w
  have hwl := D.nd.SQ_l i w (Or.inl hS)
  have fac := Formalism.MainNotions.SumRepresentations.rhobar_fac D.nd r hC hr rb hrb x (D.nd.gam0 i w)
  rw [charpoly_red D.nd r hs _ hg] at fac
  have hprod : ∏ c ∈ Finset.Icc 1 D.R.t, (X - C (IsLocalRing.residue (D.nd.O i)
      ((D.nd.chi i c (D.nd.gam0 i w) : (D.nd.O i)ˣ) : D.nd.O i))) =
      ∏ _c ∈ Finset.Icc 1 D.R.t, (X - C (IsLocalRing.residue (D.nd.O i) (chi1 D.nd i (D.nd.gam0 i w)))) :=
    Finset.prod_congr rfl fun c hc => by
      rw [Formalism.MainNotions.SumRepresentations.character_eq_first_off_l D.nd w hwl c (Finset.mem_Icc.1 hc).1 (Finset.mem_Icc.1 hc).2 _ hg]
      rfl
  rw [hprod, Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel] at fac
  have hcp := mul_right_cancel₀ (pow_ne_zero _ (X_sub_C_ne_zero _)) fac
  have h0 : ((X - 1 : Polynomial (IsLocalRing.ResidueField (D.nd.O i))) ^ D.R.r).eval
      (IsLocalRing.residue (D.nd.O i) (chi1 D.nd i (D.nd.gam0 i w))) = 0 := by
    rw [← hcp]
    exact hroot
  rw [eval_pow, eval_sub, eval_X, eval_one] at h0
  exact pow_ne_zero _ (sub_ne_zero.2 hne) h0
end UpperTheory.GalS
end
end
end

section



section
noncomputable section
namespace DiscreteGroups.sglob.DzType.Rt
open Polynomial GlobalTheory.GLq GlobalTheory.GLp Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders GlobalTheory.SerSys
open scoped Classical
attribute [local instance] GlobalTheory.SerSys.factTypePrime
variable {g : ℕ} [Fact g.Prime]
theorem locType_of_serParamLe_alt {D : D7} {S : ∀ k, Sys (D.host.g k)} {rc : Corr D} (hC : _root_.GlobalTheory.SerSys.LocalCompatibility D rc)
    (hP : ∀ k v, SerParamLe D.R.nV (S k).e (D.ntypes.teichC k) fun n π => D.naut.inePol (rc k v n π) (D.ntypes.tg k v)) :
    LocType D S := by
  intro i P k v
  obtain ⟨μ, χ, hμ, h1, h2⟩ := hC.2 i k v
  obtain ⟨π, hπ, h3, h4⟩ := h2 P
  obtain ⟨f, hf, hm, hd, -⟩ := Loc.exists_charIn (S k) χ 1
  obtain ⟨c, rfl⟩ : ∃ c, f = X - C c := ⟨-f.coeff 0, by rw [C_neg, sub_neg_eq_add]; exact hm.eq_X_add_C hd⟩
  refine ⟨π, χ, c, fun F hF a ha h0 => h4.exists_parVec hF ha h0, Loc.charIn_pow _ χ hf _, ?_,
    fun f' hf' => h3 ▸ hP k v _ le_rfl π hπ f' hf'⟩
  rw [h1, ← Loc.prod_linear]
  exact hP k v 1 (one_le_nV D) _ (Loc.irrSm_det hμ) _ ((Loc.has_det hμ (S k) _).2 hf)
theorem locType_of_labTie_locComp_labParamLe {D : D7} {L : ∀ k, LabelDatum (D.host.g k)} {S : ∀ k, Sys (D.host.g k)} {rc : Corr D}
    (hL : LabTie D L) (hS : ∀ k, (S k).IsOf (L k)) (hC : _root_.GlobalTheory.SerSys.LocalCompatibility D rc) (hP : LabParamLe D.R.nV D L rc) :
    LocType D S :=
  _root_.DiscreteGroups.sglob.DzType.Rt.locType_of_serParamLe_alt hC fun k v => by
    rw [← (hL k).1, show (S k).e = eSerC (L k) from _root_.funext fun n => _root_.funext (hS k n)]
    exact hP k v
end DiscreteGroups.sglob.DzType.Rt
end
end
end

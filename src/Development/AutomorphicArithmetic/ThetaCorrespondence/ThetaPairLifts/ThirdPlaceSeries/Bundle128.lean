module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle102
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2439
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle894
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2509
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2476
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle100
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle106
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseMovesVectorZ
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle351
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle400
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle399
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle026
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle365
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle111
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle374
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle023

@[expose] public section

section



section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp


attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp.TupLe
variable {D : D7}
open Classical in
theorem placesSt_alt : _root_.GlobalTheory.BigOn.Exp.TupLe.PlacesCondition := by
  intro D L hT Gi Gl Kc Y cX ex Csz p j hr hm w hw hok ρ hρ hpin _ _
  have hPA := placesAt (j := j) hw hρ hpin
  have hL := _root_.GlobalTheory.BigOn.links2_of_rows_alt _ _ _ _ _ _ _ _ _ _ p hr hm.1
  have hC : GlobalTheory.Hk3.Core (R2 p) (F2 p) := ⟨hL.1.lev, hL.1.grp, hL.1.fam, hL.1.models, hL.1.chain, hL.1.thP⟩
  have hXs : SplitSet (p.R.Q (p.R.mu (D.plEq w))) := by
    obtain ⟨-, e, he, -⟩ := hC.thP.vP j (p.R.mu (D.plEq w))
    exact SplitSet.mono ⟨e, he⟩ Finset.subset_union_right
  have hl : ∀ P ∈ p.R.Q (p.R.mu (D.plEq w)), ((D.ntw.l (ex.nch.twI w) : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    intro P hP
    rcases (hPA.2 P).1 (Or.inl hP) with hD | hQ
    · have h1 : P ∈ (↑(D.ntw.pD (ex.nch.twI w)) : Set (Pl D.host.E)) := hD
      rw [D.ntw.pD_eq] at h1
      have hlp := (D.ntw.lPrime (ex.nch.twI w)).out
      refine not_mem_of_coprime h1 ?_
      split_ifs with h
      · exact (Nat.coprime_primes hlp D.host.pde'_prime).2 (by rw [h]; exact D.host.pde_ne)
      · exact (Nat.coprime_primes hlp D.host.pde_prime).2 h
    · exact fun hlP => Finset.disjoint_left.1 hok.2.1 hQ (D.ntw.twistExcludedPlaces_contains_residueChar _ hlP)
  refine ⟨hXs, hl, ?_⟩
  obtain ⟨-, hadm, -⟩ := GlobalTheory.TwistGood.tw_good D _ D.ntw ρ hρ _ j (ex.nch.sd w) _ _ _ hok
  obtain ⟨R, -, hR, hRs⟩ := hadm.1.split
  have hYs := hRs.mono hR
  have hXC : ∀ P, P ∈ p.R.Q (p.R.mu (D.plEq w)) ∪ (p.R.Q (p.R.mu (D.plEq w))).image Formalism.L2.DIV.conjPl ↔
      (P ∈ D.ntw.pD (ex.nch.twI w) ∨ P ∈ ex.nch.Q w) := fun P => by
    rw [← hPA.2 P, Finset.mem_union, Finset.mem_image]
    refine or_congr Iff.rfl (exists_congr fun P' => and_congr Iff.rfl ?_)
    rw [lev_isConjPl_iff, eq_comm]
  have hne : ∀ P, P ∈ D.ntw.pD (ex.nch.twI w) ∨ P ∈ ex.nch.Q w → Formalism.L2.DIV.conjPl P ≠ P := fun P hP e => by
    rcases Finset.mem_union.1 ((hXC P).2 hP) with h | h
    · exact Finset.disjoint_left.1 (disjoint_conj hXs) h (Finset.mem_image.2 ⟨P, h, e⟩)
    · obtain ⟨P', hP', rfl⟩ := Finset.mem_image.1 h
      rw [Formalism.L2.DIV.conjPl_conjPl] at e
      exact Finset.disjoint_left.1 (disjoint_conj hXs) hP' (Finset.mem_image.2 ⟨P', hP', e.symm⟩)
  have hcl : ∀ P, P ∈ D.ntw.pD (ex.nch.twI w) ∨ P ∈ ex.nch.Q w →
      Formalism.L2.DIV.conjPl P ∈ D.ntw.pD (ex.nch.twI w) ∨ Formalism.L2.DIV.conjPl P ∈ ex.nch.Q w := fun P hP => by
    rw [← hXC] at hP ⊢
    rcases Finset.mem_union.1 hP with h | h
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ h)
    · obtain ⟨P', hP', rfl⟩ := Finset.mem_image.1 h
      rw [Formalism.L2.DIV.conjPl_conjPl]
      exact Finset.mem_union_left _ hP'
  have hY : (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).de.Q ∪
      (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).Q =
      half (ρ.ch (ex.nch.twI w)) (D.ntw.pD (ex.nch.twI w)) ∪ half (ρ.ch (ex.nch.twI w)) (ex.nch.Q w) := by
    rw [hρ.delta]
    rfl
  rw [hY] at hYs ⊢
  exact idem_add_cA_eq hXs hYs fun P =>
    (hXC P).trans (mem_half_closure ((hρ.ch _).pair) hcl hne P).symm
end GlobalTheory.BigOn.Exp.TupLe
end
end
end

section



section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Datum
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open GlobalTheory.ConjTwist (BaseOf)


attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.TraceFlatLevel
open GlobalTheory.TraceLevelPf
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
end GlobalTheory.TraceFlatLevel
namespace GlobalTheory.BigOn.Exp.TupLe
theorem traceSt_alt : _root_.GlobalTheory.BigOn.Exp.TupLe.TraceCondition := by
  intro D L hT Gi Gl Kc Y cX ex Csz p j hr hm ρ hρ hpin hlev i b ψ ω hψ hQ hω h P
  have hL := _root_.GlobalTheory.BigOn.links2_of_rows_alt _ _ _ _ _ _ _ _ _ _ p hr hm.1
  have hC : GlobalTheory.Hk3.Core (R2 p) (F2 p) := ⟨hL.1.lev, hL.1.grp, hL.1.fam, hL.1.models, hL.1.chain, hL.1.thP⟩
  have hBo : BaseOf (R2 p) j (ρ.B i j b) := { baseOf_of_realPin_at (cG := p.cG) hC.lev hρ hpin i j b with }
  refine GlobalTheory.TraceFlatLevel.traceLevel_flat (R2 p) j (ρ.B i j b) (hρ.base i j b) hBo (F2 p).P0 (F2 p).ψ0⁻¹
    ((p.R.eG.trans p.cG).trans (ρ.eG i j b)) (fun g P h h' a c => ?_) (fun g => mem_level_iff hm.2.2 hlev i j b g)
    (fun u hu => ?_) ψ hψ hQ ω hω h P
  · have e1 := hpin.grp i j b (p.cG (p.R.eG g)) P h h' a c
    rw [MulEquiv.symm_apply_apply] at e1
    exact e1
  · refine (level_chi hm.2.2 hρ hlev i j b u hu).1.trans ?_
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, map_inv₀]
    rfl
end GlobalTheory.BigOn.Exp.TupLe
end
end
end

section



section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.LocMod Matrix
noncomputable section
namespace GlobalTheory.MiTop.MoveZ
section Two
variable {D : D7} {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']
end Two
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
theorem addChar_uniformizer_eq_chi_of_gRead (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (PP : (_root_.GlobalTheory.Fam.pk_z W).Pg) : ∃ χ : 𝓞 D.host.E → ℂ, ∀ u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (v : VCom f.c) (n : ℕ)
    (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ i, pl i = PP → ∀ z : 𝓞 D.host.E,
      ((G i).S.ψ ((((G i).S.ϖ⁻¹ : (G i).kˣ) : (G i).k) * (ofSplit (G i).q).pr (z : D.host.E)) : ℂ) = χ z := by
  classical
  have hr : 2 ≤ D.R.r := by have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Ranks.r; omega
  have hk : 2 ≤ D.R.k := by have := D.R.two_le_m; have := D.R.m_add_three_le_k; omega
  let a : Fin D.R.r := ⟨0, by omega⟩
  let b : Fin D.R.r := ⟨1, by omega⟩
  have hab : a ≠ b := fun e => by have := congrArg Fin.val e; simp [a, b] at this
  let g : 𝓞 D.host.E → ∀ P : (_root_.GlobalTheory.Fam.pk_z W).Pg, GL (Fin D.R.r) (kP P.1) := fun z P =>
    elem a b hab (Ideal.Quotient.mk P.1.asIdeal (if P = PP then z else 0))
  refine ⟨fun z => if h : g z ∈ (_root_.GlobalTheory.Fam.complexLevelStructure W).H then (((_root_.GlobalTheory.Fam.complexLevelStructure W).chi ⟨g z, h⟩ : ℂˣ) : ℂ) else 0, ?_⟩
  intro u f v n G pl hG i hi z
  have hex : ∀ j, ∃ x, GlobalTheory.LevZero.Red (G j) (pl j).1 x (g z (pl j)) := fun j =>
    (GlobalTheory.LevZero.exists_red_iff_isPat (G j) (pl j).1 (hG.idem j).1 _).2
      (isPat_elem a b hab (Or.inl ⟨by simp only [a]; omega, by simp only [b]; omega, by simp [a, b]⟩) _)
  have hmem : g z ∈ (_root_.GlobalTheory.Fam.complexLevelStructure W).H := (hG.lev (g z)).1.2 hex
  choose x hx using hex
  have hchi := (hG.lev (g z)).2 hmem x hx
  have hlam : ∀ j, (((G j).S.P.lam (x j) : ℂˣ) : ℂ) = (G j).S.ψ ((((G j).S.ϖ⁻¹ : (G j).kˣ) : (G j).k) *
      (ofSplit (G j).q).pr ((if pl j = PP then z else 0 : 𝓞 D.host.E) : D.host.E)) := fun j =>
    GlobalTheory.LevZero.lam_eq_of_red (G j) (pl j).1 (hG.idem j).1 (x j) _ (hx j) _
      (edgeSum_elem a b hab ⟨rfl, by simp only [a]; omega⟩ _).symm
  simp only [dif_pos hmem]
  rw [hchi, Units.coe_prod, Finset.prod_eq_single i (fun j _ hj => ?_) (by simp), hlam, if_pos hi]
  rw [hlam, if_neg (fun e => hj (pl.injective (e.trans hi.symm)))]
  simp [Place.pr]

theorem base_inv_alt_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0))
    {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
    (v : VCom f.c) (o : TDat f.c k ι) {n : ℕ} (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg) (hG : _root_.GlobalTheory.Fam.LocalGroupReading f G pl)
    (hB : _root_.GlobalTheory.MiTop.LocalBottomCompatibility f B v o G) (i : Fin n) : ∃ j₀ : Fin (Yc D 0).rank, j₀.val = D.R.k + D.R.rS ∧ ∀ r,
      toEAf D (G i).q.e * (((Formalism.IndefR.Lev.finE (Yc D 0) (f.g.b 0))⁻¹).val *ᵥ
        (fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D)
          (W.S.X.ιE (W.S.X.zR u (Fin.cast (rank_eq W.S.X W.Q.instEq) r))))) r =
      toEAf D ((G i).q.sec (((((G i).S.ϖ⁻¹ : (G i).kˣ) : (G i).k)) ^ (D.R.rS + 1))) * ((_root_.GlobalTheory.Fam.pk_z W).βY 0).val r j₀ := by
  have hs := (G i).hs
  have hodd := (G i).S.odd
  have hρ : D.R.rS = (G i).S.ρ := by unfold Ranks.rS; omega
  have h₀ : 0 + 2 * D.R.rS + 2 = D.R.m := by omega
  have he := (hG.idem i).1
  obtain ⟨μ, lam, hμ, hv, hτ⟩ := hB.norm
  have hsc := sc_mul_mu (G i) μ lam hμ o.ζ₀ hτ (hB.last i)
  obtain ⟨e, hord, hM⟩ := hG.frame i 0 ((G i).s + 1) (Nat.zero_add _)
  let p : Fin ((G i).s + 1) := ⟨D.R.rS, by omega⟩
  refine ⟨e (.inl (.inr p)), hord _, fun r => ?_⟩
  refine e_mul_of_prF (G i).q he _ _ _ ?_
  refine map_inv_mulVec ((G i).q.prF he) _ _ (fun r => ((_root_.GlobalTheory.Fam.pk_z W).βY 0).val r (e (.inl (.inr p)))) _ (fun r => ?_) r
  choose lf hlf using fun x : Formalism.IndefR.Datum.EAf D => GlobalTheory.ResLoc.toEAf_surj x
  have h1 := congrFun (congrFun (hM (((_root_.GlobalTheory.Fam.pk_z W).βY 0).val.map lf) (Matrix.ext fun a b => hlf _)) r) (e (.inl (.inr p)))
  have h2 : (G i).q.prF he (((Formalism.IndefR.Lev.finE (Yc D 0) (f.g.b 0)).val *ᵥ
      fun r => ((_root_.GlobalTheory.Fam.pk_z W).βY 0).val r (e (.inl (.inr p)))) r) =
      (ofSplit (G i).q).π ((Formalism.L2.Theta.mt (Yc D 0) (f.g.b 0) * ((_root_.GlobalTheory.Fam.pk_z W).βY 0).val.map lf) r (e (.inl (.inr p)))) := by

    rw [Matrix.mul_apply, map_sum, mulVec, dotProduct, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hlf (((_root_.GlobalTheory.Fam.pk_z W).βY 0).val a _)]
    exact (congrArg ((G i).q.prF he) ((toEAf D).map_mul _ _).symm).trans ((G i).q.prF_toEAf he _)
  have h3 : (ofSplit (G i).q).π ((Formalism.L2.Theta.mt (Yc D 0) (f.g.b 0) * ((_root_.GlobalTheory.Fam.pk_z W).βY 0).val.map lf) r (e (.inl (.inr p)))) =
      ((G i).FY 0 ((G i).s + 1) (Nat.zero_add _)).β r (.inr p) * ((G i).S.ϖ : (G i).k) ^ (D.R.rS + 1) := by
    refine h1.trans ?_
    rw [submatrix_apply, Equiv.symm_apply_apply, GlobalTheory.LevZeroUp.bas_val, mul_diagonal]
    rw [GlobalTheory.StepData.standardOrderExtendedBasis_apply_low_block (Fin D.R.k) (Fin D.R.t) (l := (G i).s + 1) 0 ((G i).s + 1) (Nat.zero_add _) p]
    rfl
  have h4 := ((G i).bes 0 D.R.rS h₀ ((G i).s + 1) (Nat.zero_add _)).2.2.2.1 p rfl r
  have h5 : B.d.i₀ *ᵥ vecB B.o B.ζ = (f.c.B 0 D.R.rS h₀).d.i₀ *ᵥ vecB (f.c.B 0 D.R.rS h₀).o (f.c.B 0 D.R.rS h₀).ζ :=
    eq_of_heq (congr_arg_heq (fun B' : BesLev D D.R.rS => B'.d.i₀ *ᵥ vecB B'.o B'.ζ) (hB.lev h₀))
  rw [← h5, hv r] at h4
  have h6 : (G i).q.prF he (algebraMap D.host.E (Formalism.IndefR.Lev.EAf D)
      (W.S.X.ιE (W.S.X.zR u (Fin.cast (rank_eq W.S.X W.Q.instEq) r)))) =
      (ofSplit (G i).q).pr (W.S.X.ιE (W.S.X.zR u (Fin.cast (rank_eq W.S.X W.Q.instEq) r))) :=
    (G i).q.prF_toEAf he (incA D _)
  have h7 : ∀ x y, (ofSplit (G i).q).pr (x * y) = (ofSplit (G i).q).pr x * (ofSplit (G i).q).pr y := fun x y =>
    ((G i).q.pr.comp (incA D)).map_mul x y
  rw [h7, ← mul_assoc, hsc, one_mul] at h4
  rw [h6, h2, h3, h4, mul_comm, mul_assoc, ← mul_pow, Units.mul_inv, one_pow, mul_one]
theorem inv_mulVec_adelic_embedding_eq_self (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (hW : _root_.GlobalTheory.Fam.PackageHypotheses W) {u : D.what₂.Word} (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0))
    (g : GA D (D.sp.X 0)) :
    ((Formalism.IndefR.Lev.finE (D.sp.Y 0) (embA B.d B.o g))⁻¹).val *ᵥ (fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D)
      (W.S.X.ιE (W.S.X.zR u (Fin.cast (rank_eq W.S.X W.Q.instEq) r)))) =
      fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (W.S.X.ιE (W.S.X.zR u (Fin.cast (rank_eq W.S.X W.Q.instEq) r))) := by
  have h := GlobalTheory.MiTop.fixAux W.S.X W.Q.instEq hW.bot.idE (Formalism.L2.SG.PoincareInHH.PoincareSetting.fixSet W.S.X u) (W.S.X.zR u)
    (Or.inr rfl) (embA B.d B.o g)⁻¹ ((B.tieH _).1 ((embA B.d B.o).range.inv_mem ⟨g, rfl⟩))
  funext r
  rw [← map_inv]
  exact ((toEAf D).map_mulVec _ _ r).symm.trans (congrArg (toEAf D) (congrFun h r))
end GlobalTheory.MiTop.MoveZ
open GlobalTheory.MiTop.MoveZ in

theorem GlobalTheory.MiTop.base_moves_vector_z_alt_bis : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → 1 ≤ D.R.rS → ∀ PP ∈ (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true)).Pg, ∃ Γ : Fin (Yc D 0).rank → Formalism.IndefR.Lev.EAf D, ∀ u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedAlt f B → ∀ a₀ a, _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a → ∃ (θ : Formalism.IndefR.Lev.EAf D) (hθ : θ ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), Formalism.L2.DIV.resS D.host.F PP ⟨θ, hθ⟩ = 1 ∧ ∀ ei : AE D, Formalism.L2.NTheta.IsIdemAt ei PP → toEAf D ei • Matrix.mulVec (((Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from f.g.b 0))))⁻¹ : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)).val (fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (W.S.X.ιE (W.S.X.zR u (Fin.cast (rank_eq W.S.X W.Q.instEq) r)))) = toEAf D ei • (θ • Γ) := by
  intro D L hT Gi Gl Kc Yd cX ex W hW hr PP hPP
  obtain ⟨χ, hχ⟩ := _root_.GlobalTheory.MiTop.MoveZ.addChar_uniformizer_eq_chi_of_gRead W ⟨PP, hPP⟩
  by_cases hex : ∃ u, ∃ (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedAlt f B
  swap
  · exact ⟨0, fun u f B h => absurd ⟨u, f, B, h⟩ hex⟩
  obtain ⟨u₀, f₀, B₀, k₀, _, _, _, _, ι₀, v₀, o₀, n₀, G₀, pl₀, -, -, -, -, -, hG₀, hB₀⟩ := hex
  obtain ⟨i₀, hi₀⟩ := pl₀.surjective ⟨PP, hPP⟩
  have he₀ : Formalism.L2.NTheta.IsIdemAt (G₀ i₀).q.e PP := by have := (hG₀.idem i₀).1; rwa [hi₀] at this
  obtain ⟨j₀, hj₀, -⟩ := _root_.GlobalTheory.MiTop.MoveZ.base_inv_alt_alt W f₀ B₀ v₀ o₀ G₀ pl₀ hG₀ hB₀ i₀
  refine ⟨fun r => toEAf D ((G₀ i₀).q.sec (((((G₀ i₀).S.ϖ⁻¹ : (G₀ i₀).kˣ) : (G₀ i₀).k)) ^ (D.R.rS + 1))) *
    ((_root_.GlobalTheory.Fam.pk_z W).βY 0).val r j₀, ?_⟩
  rintro u f B ⟨k, _, _, _, _, ι, v, o, n, G, pl, -, -, -, -, -, hG, hB⟩ a₀ a -
  obtain ⟨i, hi⟩ := pl.surjective ⟨PP, hPP⟩
  have he : Formalism.L2.NTheta.IsIdemAt (G i).q.e PP := by have := (hG.idem i).1; rwa [hi] at this
  have hee : (G₀ i₀).q.e = (G i).q.e := GlobalTheory.LocMod.PinInhab.idem_unique he₀ he
  obtain ⟨j, hj, hz⟩ := _root_.GlobalTheory.MiTop.MoveZ.base_inv_alt_alt W f B v o G pl hG hB i
  obtain rfl : j = j₀ := Fin.ext (hj.trans hj₀.symm)
  have hrat := unif_ratio (G₀ i₀).q (G i).q he₀ hee (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (G₀ i₀).char (G i).char (G₀ i₀).S.cond _ _
    (G₀ i₀).S.unif (G i).S.unif fun z => (hχ u₀ f₀ v₀ n₀ G₀ pl₀ hG₀ i₀ hi₀ z).trans (hχ u f v n G pl hG i hi z).symm
  obtain ⟨θ, hθ, h1, h2⟩ := exists_theta (G₀ i₀).q he₀ _ (pow_sub_one_lt hrat (D.R.rS + 1))
  refine ⟨θ, hθ, h1, fun ei hei => ?_⟩
  obtain rfl : ei = (G i).q.e := GlobalTheory.LocMod.PinInhab.idem_unique hei he
  have h3 : toEAf D ((G i).q.sec (((((G i).S.ϖ⁻¹ : (G i).kˣ) : (G i).k)) ^ (D.R.rS + 1))) = toEAf D (G i).q.e * θ *
      toEAf D ((G₀ i₀).q.sec (((((G₀ i₀).S.ϖ⁻¹ : (G₀ i₀).kˣ) : (G₀ i₀).k)) ^ (D.R.rS + 1))) := by
    rw [← hee, h2, ← RingHom.map_mul, ← _root_.GlobalTheory.MiTop.MoveZ.sec_mul_sec, ← mul_pow, mul_right_comm, Units.mul_inv, one_mul, ← map_pow, sec_chg]
  have h4 : (((Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from embA B.d B.o (a₀ * a) *
      (show GA D (D.sp.Y 0) from f.g.b 0))))⁻¹ : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)).val =
      ((Formalism.IndefR.Lev.finE (Yc D 0) (f.g.b 0))⁻¹).val *
        ((Formalism.IndefR.Lev.finE (Yc D 0) (embA B.d B.o (a₀ * a)))⁻¹).val := by
    have := (Formalism.IndefR.Lev.finE (D.sp.Y 0)).map_mul (embA B.d B.o (a₀ * a)) (f.g.b 0)
    exact congrArg Units.val ((congrArg Inv.inv this).trans (_root_.mul_inv_rev _ _))
  funext r
  rw [h4, ← mulVec_mulVec]
  have h5 := _root_.GlobalTheory.MiTop.MoveZ.inv_mulVec_adelic_embedding_eq_self W hW B (a₀ * a)
  refine Eq.trans ?_ ((hz r).trans ?_)
  · exact congrArg (fun w => toEAf D (G i).q.e * (((Formalism.IndefR.Lev.finE (Yc D 0) (f.g.b 0))⁻¹).val *ᵥ w) r) h5
  · rw [h3, mul_assoc, mul_assoc]
    rfl
end
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option genSizeOfSpec false
set_option genInjectivity false
noncomputable section
namespace GlobalTheory.QPl
variable {D : D7} {c : Comm D} {v : VCom c} {t : Tup c}
end GlobalTheory.QPl
namespace GlobalTheory.Fam
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word}
def QuadraticExtensionData.eps {a : _root_.GlobalTheory.Fam.GeometricFamily W u} {t : W.P.T} (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (j : ℕ) (α : J.Ch j) : GA (I.rec7 l Z) (Yc (I.rec7 l Z) j) →₀ ℂ :=
  if (∃ ρ, j + 2 * ρ + 2 = (I.rec7 l Z).R.m) ∨ j = 0 then J.wt j α • conv (List.ofFn fun i => (J.E i).εL j (α i)) else 0
variable (a : _root_.GlobalTheory.Fam.GeometricFamily W u) (J : ∀ t, _root_.GlobalTheory.Fam.QuadraticExtensionData a t)
def columnChoiceOfCoefficients (kom : ∀ (_ : W.P.T) j, Om ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)))
    (dd : ∀ t j, (J t).Ch j → (J t).Ch (j + 1) → WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) →₀ ℂ)
    (S : ∀ t j, GlobalTheory.AdForm.ColT I l u (W.P.I.tup t) j → GlobalTheory.AdForm.ColT I l u (W.P.I.tup t) j)
    (s : ∀ t j, (J t).Ch j → ℂ) (cV cK : W.P.T → ℕ → ℂ) (cP : W.P.T → ℂ) (t : W.P.T) :
    ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t)) where
  kom := kom t
  Ch := (J t).Ch
  dd := dd t
  e := fun j α => (s t j α • (J t).eps j α).mapDomain (· * a.g.b j)
  eT := fun n _ β => (s t n β • Finsupp.single (1 : GA (I.rec7 l Z) (I.rec7 l Z).sp.X') ((J t).wt n β)).mapDomain (· * a.g.bT)
  Ram := fun j => {φ | (J t).A.RamL (J t).ι j φ}
  S := S t
  rd := fun j α φ y => if hj : j ≤ B.R.m then (J t).A.rd (_root_.GlobalTheory.Fam.pk_z W).θ j hj ((J t).ι j α) φ y else 0
  cV := cV t
  cK := cK t
  cP := cP t
def trivialColumnChoice (t : W.P.T) : ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t)) where
  kom := fun _ => 1
  Ch := fun _ => Empty
  dd := fun _ α => α.elim
  e := fun _ α => α.elim
  eT := fun _ _ α => α.elim
  Ram := fun _ => ∅
  S := fun _ φ => φ
  rd := fun _ α => α.elim
  cV := 0
  cK := 0
  cP := 0
def familyOfRowColumnChoices (row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t) (col : ∀ t : W.P.T, ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t)))
    (hCh : ∀ t, (col t).Ch = (J t).Ch) (t : W.P.T) : GlobalTheory.QPl.QFam a.v ((a.fam row col).t t) where
  χ := _root_.GlobalTheory.Fam.chrK_alt W t
  r := (J t).r
  Q := fun i => ((J t).E i).toAt
  eqv := fun j => Equiv.cast (congrFun (hCh t) j)
end GlobalTheory.Fam
end
end
end

section



section
set_option genSizeOfSpec false
set_option genInjectivity false
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word}
  {a : _root_.GlobalTheory.Fam.GeometricFamily W u} {t : W.P.T}
structure QuadraticExtensionData.ReadsStd (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) : Prop where
  is : J.A.Is
  inj : Function.Injective J.pl
  surj : ∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, ∃ i, J.pl i = PP
  chr : ∀ j, j < B.R.m → J.A.chr (j + 1) = _root_.GlobalTheory.Fam.chrK_alt W t j
  res : ∀ i, (J.G i).Res (J.E i).δ ((_root_.GlobalTheory.Fam.pk_z W).xiR t (J.pl i))
  eq : ∀ i, (J.P i).1 = J.pl i
  sg : ∀ i, J.sg i = 1 ∨ J.sg i = -1
  tw : ∀ i, GlobalTheory.TwBridge.AtTwist (R := B.R) (k := (J.G i).k) I.sel (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) B.embLL (J.P i)
    ((J.G i).q.pr.comp (incA (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G))) (J.G i).s ((J.E i).tw (J.hψ i) (J.sg i))
  M : ∀ i, (J.E i).M = (I.cst (W.P.I.tup t)).M
  rep : ∀ i j d (h : j + d = (J.G i).s) (hj : j < B.R.m) β,
    GlobalTheory.TwBridge.IsGL (X := B.fields) (R := B.R) (k := (J.G i).k) ((J.G i).q.pr.comp (incA (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)))
      ((I.idx (W.P.I.tup t)).h j ((J.A.b0 j β).get hj) (J.P i)) ((J.E i).rep j d h (J.π i j β))
  orb : ∀ i β (e : XIx (Fin B.R.k) (Fin B.R.t) ((J.G i).s + 1) ≃ Fin (B.R.N ((J.G i).s + 1))),
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e →
      SameOrb (((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).lev ((J.G i).s + 1) 0 rfl).J (box _ ((J.G i).ϖ ^ (J.E i).M))
        ((J.E i).cos (J.π i ((J.G i).s + 1) β))
        (Submodule.Quotient.mk fun r => (ofSplit (J.G i).q).pr (Formalism.L2.Col.repY (J.A.p0 ((J.G i).s + 1) β).1.2 (e r)))
  std : ∀ j, j < B.R.m → ∀ β, J.A.kb j β = TC.kStd X u (B.R.N j)
  last : Nonempty (Unique (J.Ch₀ B.R.m))
  sec : ∀ j, j ≤ B.R.m → ∀ y i, J.π i j (J.ι j y) = y i
  cosG : ∀ (n : Fin a.n) y (e : XIx (Fin B.R.k) (Fin B.R.t) ((a.G n).s + 1) ≃ Fin (B.R.N ((a.G n).s + 1))),
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e → ∀ r,
      (ofSplit (a.G n).q).pr (Formalism.L2.Col.repY (J.A.p0 ((a.G n).s + 1) (J.ι _ y)).1.2 (e r)) - (a.G n).S.y0 (Fin B.R.t) r ∈ 𝒪[(a.G n).k]
  live : J.A.Live J.ι
structure QuadraticExtensionData.ReadsLow (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) : Prop where
  is : J.A.Is
  inj : Function.Injective J.pl
  surj : ∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, ∃ i, J.pl i = PP
  chr : ∀ j, j < B.R.m → J.A.chr (j + 1) = _root_.GlobalTheory.Fam.chrK_alt W t j
  res : ∀ i, (J.G i).Res (J.E i).δ ((_root_.GlobalTheory.Fam.pk_z W).xiR t (J.pl i))
  eq : ∀ i, (J.P i).1 = J.pl i
  sg : ∀ i, J.sg i = 1 ∨ J.sg i = -1
  tw : ∀ i, GlobalTheory.TwBridge.AtTwist (R := B.R) (k := (J.G i).k) I.sel (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) B.embLL (J.P i)
    ((J.G i).q.pr.comp (incA (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G))) (J.G i).s ((J.E i).tw (J.hψ i) (J.sg i))
  M : ∀ i, (J.E i).M = (I.cst (W.P.I.tup t)).M
  rep : ∀ i j d (h : j + d = (J.G i).s) (hj : j < B.R.m) β,
    GlobalTheory.TwBridge.IsGL (X := B.fields) (R := B.R) (k := (J.G i).k) ((J.G i).q.pr.comp (incA (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)))
      ((I.idx (W.P.I.tup t)).h j ((J.A.b0 j β).get hj) (J.P i)) ((J.E i).rep j d h (J.π i j β))
  std : ∀ j, j < B.R.m → ∀ β, J.A.kb j β = TC.kStd X u (B.R.N j)
  last : Nonempty (Unique (J.Ch₀ B.R.m))
  sec : ∀ j, j ≤ B.R.m → j + 1 ≠ B.R.m → ∀ y i, J.π i j (J.ι j y) = y i
  injCh : ∀ j, j + 1 ≠ B.R.m → Function.Injective (J.ι j)
  first : Function.Surjective (J.ι 0)
  onto : Function.Surjective (J.ι B.R.m)
  dead : ∀ j (hj : j + 1 ≤ B.R.m), j + 1 + 1 ≠ B.R.m → ∀ γ, γ ∉ Set.range (J.ι (j + 1)) → ∀ α z, J.A.xi j hj α γ z = 0
end GlobalTheory.Fam
end
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
noncomputable section
namespace GlobalTheory.LevProd
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word} {a : _root_.GlobalTheory.Fam.GeometricFamily W u} {t : W.P.T}
theorem step_index_le_s_alt (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (i : Fin J.r) {j : ℕ} (hj : j + 2 ≤ B.R.m) : j ≤ (J.G i).s := by
  have h1 := (J.G i).hs
  change (J.G i).s + 1 + 1 = B.R.m at h1
  omega
def localHomProduct (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (j : ℕ) (hj : j + 2 ≤ B.R.m) :
    GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →* ((i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k) :=
  Pi.monoidHom fun i => GlobalTheory.LevIdx.locHom (J.G i).q _ ((J.G i).FX j (by have := _root_.GlobalTheory.LevProd.step_index_le_s_alt J i hj; omega))
def levelSubgroupAtPlace (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (j : ℕ) (hj : j + 2 ≤ B.R.m) (α : J.Ch j) (i : Fin J.r) :
    Subgroup (GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k) :=
  prX (Cgrp (((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).lev j ((J.G i).s - j + 1) (by have := _root_.GlobalTheory.LevProd.step_index_le_s_alt J i hj; omega)).J
    ((J.E i).rep j ((J.G i).s - j) (Nat.add_sub_cancel' (_root_.GlobalTheory.LevProd.step_index_le_s_alt J i hj)) (α i)))
def quadraticTwistAtPlace (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) : GlobalTheory.FinPl.Pl (I.rec7 l Z) → Prop := fun v => ∃ i, (J.G i).q.v = v
def relaxedLevelSubgroup (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (j : ℕ) (hj : j + 2 ≤ B.R.m) (α : J.Ch j) : Subgroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) :=
  (J.A.U j (J.ι j α) ⊔ GlobalTheory.FinPl.grpAt _ (_root_.GlobalTheory.LevProd.quadraticTwistAtPlace J)) ⊓ GfC _ ⊓
    (Subgroup.pi Set.univ fun i => KO (J.G i).k (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j)).comap (_root_.GlobalTheory.LevProd.localHomProduct J j hj)
def upperLevelSubgroup (a : _root_.GlobalTheory.Fam.GeometricFamily W u) (j : ℕ) (hj : j + 2 ≤ B.R.m) : Subgroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) :=
  if h : ∃ t, ∃ J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t, J.Reads ∧ Nonempty (J.Ch j) then
    _root_.GlobalTheory.LevProd.relaxedLevelSubgroup h.choose_spec.choose j hj h.choose_spec.choose_spec.2.some
  else ⊥
theorem upperLevelSubgroup_le_GfC (a : _root_.GlobalTheory.Fam.GeometricFamily W u) (j : ℕ) (hj : j + 2 ≤ B.R.m) : _root_.GlobalTheory.LevProd.upperLevelSubgroup a j hj ≤ GfC _ := by
  unfold _root_.GlobalTheory.LevProd.upperLevelSubgroup
  split_ifs
  · intro g hg
    exact (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hg).1).2
  · exact bot_le
theorem wt_eq_inv_measure_levelSubgroupAtPlace {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word} {a : _root_.GlobalTheory.Fam.GeometricFamily W u} {t : W.P.T} (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (j : ℕ) (hj : j + 2 ≤ B.R.m) (α : J.Ch j) (i : Fin J.r) :
    (J.E i).wt j (α i) = ((((J.E i).m j (_root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i)).toReal⁻¹ : ℝ) : ℂ) :=
  (J.E i).wt_mid j ((J.G i).s - j) (Nat.add_sub_cancel' (_root_.GlobalTheory.LevProd.step_index_le_s_alt J i hj)) (α i)
end GlobalTheory.LevProd
end
end
end

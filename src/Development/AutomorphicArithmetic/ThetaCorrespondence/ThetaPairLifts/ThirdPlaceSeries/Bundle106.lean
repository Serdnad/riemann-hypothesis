module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle077
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle074
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle096
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle089
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle486
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartTraceCharacterIdempotentInverseDiffere
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle160
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntOfSmul
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle487
import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle002
public import Formalism.LocalRingCardinality.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle166
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle143
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle172
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle118
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle092
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle093
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019

@[expose] public section

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.base_chain_top_weil_datum_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ j (h : j + 2 * 0 + 2 = D.R.m), IsWeilDatumO (_root_.GlobalTheory.BaseChain.com_z W).ψ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).V (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).V ((_root_.GlobalTheory.BaseChain.com_z W).chS (j + 1 + 1)) ((_root_.GlobalTheory.BaseChain.com_z W).chT (j + 1 + 1)) (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).ω ∧ ∃ ξ f₀, IsStepVecOf (_root_.GlobalTheory.BaseChain.com_z W).ψ (_root_.GlobalTheory.BaseChain.com_z W).θ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).V (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).V (cart (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).M) (cart (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).M) (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).Λ (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).Λ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).β (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).β (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).L ((_root_.GlobalTheory.BaseChain.com_z W).chi (j + 1 + 1)) ∅ ξ f₀ (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).f := by
  first | exact @_root_.GlobalTheory.BaseChain.stepX_weil_vec_alt | exact _root_.GlobalTheory.BaseChain.stepX_weil_vec_alt | (intros; apply _root_.GlobalTheory.BaseChain.stepX_weil_vec_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.base_chain_step_weil_datum_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ j, j + 1 < D.R.m → IsWeilDatumO (_root_.GlobalTheory.BaseChain.com_z W).ψ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W j).V (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).V ((_root_.GlobalTheory.BaseChain.com_z W).chS (j + 1)) ((_root_.GlobalTheory.BaseChain.com_z W).chT (j + 1)) (_root_.GlobalTheory.BaseChain.transitionBetweenSpacesY f j).ω ∧ ∃ ξ f₀, IsStepVecOf (_root_.GlobalTheory.BaseChain.com_z W).ψ (_root_.GlobalTheory.BaseChain.com_z W).θ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W j).V (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).V (cart (_root_.GlobalTheory.BaseChain.stageOfSpaceY W j).M) (cart (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).M) (_root_.GlobalTheory.BaseChain.stageOfSpaceY W j).Λ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).Λ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W j).β (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).β (_root_.GlobalTheory.BaseChain.stageOfSpaceY W j).L ((_root_.GlobalTheory.BaseChain.com_z W).chi (j + 1)) ∅ ξ f₀ (_root_.GlobalTheory.BaseChain.transitionBetweenSpacesY f j).f := by
  first | exact @_root_.GlobalTheory.BaseChain.stepY_weil_vec_alt | exact _root_.GlobalTheory.BaseChain.stepY_weil_vec_alt | (intros; apply _root_.GlobalTheory.BaseChain.stepY_weil_vec_alt <;> assumption)
end
end

section



section
noncomputable section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeSaw GlobalTheory.Fam Matrix ValuativeRel IsLocalRing GlobalTheory.LocMod
namespace GlobalTheory.MiTop
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u)
  (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0))
def PlacedAlt : Prop :=
  ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k) (ι : Type)
    (v : VCom f.c) (o : TDat f.c k ι) (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg),
    f.c.Is ∧ v.Is ∧ _root_.GlobalTheory.Fam.CommutingVectorTie f v ∧ ShapeOff v o ∧ GPin G ∧ _root_.GlobalTheory.Fam.LocalGroupReading f G pl ∧ _root_.GlobalTheory.MiTop.LocalBottomCompatibility f B v o G
def translationElement (a₀ a : GA D (D.sp.X 0)) : GA D (D.sp.Y 0) :=
  ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from f.g.b 0)
def IsTranslate' (a₀ a : GA D (D.sp.X 0)) : Prop :=
  IsTransportAdelicCorrection (W.S.tr u) a₀ ∧ a ∈ GfC (D.sp.X 0) ∧ a ∈ Subgroup.center (GA D (D.sp.X 0)) ∧
    Matches W.S.X W.Q.instEq (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W) (_root_.GlobalTheory.MiTop.translationElement f B a₀ a)
end GlobalTheory.MiTop
end
end
end

section



section
noncomputable section


open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
open Matrix GlobalTheory.GoodPos
namespace GlobalTheory.LineOffT
variable {D : D7}
theorem lat_zero_line_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (hr : 1 ≤ D.R.rS) u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v' : VCom f.c) (o : TDat f.c k ι) (n : ℕ) (G : Fin n → GLoc v') (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), f.c.Is → v'.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v' → ShapeOff v' o → GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → _root_.GlobalTheory.MiTop.LocalBottomCompatibility f B v' o G → GlobalTheory.MiTop.PrimTop (c := f.c) v'.tP o.ζ₀ → ∀ x : GlobalTheory.FinPl.Pl D, x ∉ v'.gP → x ∉ v'.tP → ∀ u'' : D.what₂.Word, (((D.mem u'').A.T : ℕ) : 𝓞 D.host.F) ∈ x.asIdeal → ∀ c ∈ GlobalTheory.FinPl.idAt D (· = x), ((fun i => c * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i)))) ∈ GlobalTheory.FinPl.latV (D.sp.Y 0) (v'.N 0) (· = x) ↔ c ∈ GlobalTheory.FinPl.intAt D (· = x)) := by
  intro D L hT Gi Gl Kc Yd cX ex W hW hr u f B k _ _ _ _ ι v o n G pl hc _ _ sh _ _ hb hp x _ hx u'' hu'' a ha
  have hTp : (D.mem u'').A.T.Prime := (D.mem u'').A.T_prime
  have hcop : Nat.Coprime (Ideal.absNorm D.host.ccK) (D.mem u'').A.T := by
    obtain ⟨P, hP⟩ := exists_place D.host.E hTp
    refine ((Nat.Prime.coprime_iff_not_dvd hTp).2 fun ⟨t, ht⟩ => hW.aa P (Or.inr (Or.inr ⟨u'', hP⟩)) ?_).symm
    rw [ht, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hP
  obtain ⟨α, hα⟩ := GlobalTheory.IdeleAA.exists_idele_AA D _ hc.std
  have hψ : ∀ s ∈ idAt D (· = x), (∀ o ∈ intAt D (· = x), psiE f.c.ψ (s * o) = 1) ↔
      (((xiU D * α * cU α)⁻¹ : (AE D)ˣ) : AE D) * s ∈ intAt D (· = x) := fun s hs => by
    rw [(hα x).2 s hs, mul_inv, mul_inv, Units.val_mul, Units.val_mul, cU_inv, xiU, inU_inv]
  have uξ := isU_xi_of_prime hTp hu'' (D.T_ne_d u'') hcop
  have uα := isU_alpha_of_prime hTp hu'' (UpperTheory.Small.not_mem_of_mod D.host (D.T_mod_cond u'')) (D.T_ne_q u'') (D.T_ne_d u'') hcop sh.pre.line (hα x).1
  have ug : IsU x (incA D (W.S.X.B.g : D.host.E)) := by
    refine isU_nat (UnitAt.notMem_of_coprime hu'' ?_)
    rw [W.S.X.g_eq]
    exact Nat.Coprime.mul_left ((Nat.coprime_primes (D.host.g_prime 0) hTp).2 (D.T_ne_g u'' 0).symm)
      ((Nat.coprime_primes (D.host.g_prime 1) hTp).2 (D.T_ne_g u'' 1).symm)
  have uc : IsU x (cU α : AE D) := uα.conj
  obtain ⟨μ, lam, n1, n2, n3⟩ := hb.norm
  have hξ : -D.host.xi0 ^ (D.R.m / 2) ≠ 0 := neg_ne_zero.2 (pow_ne_zero _ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D))
  have hμ : μ ≠ 0 := left_ne_zero_of_mul (n1 ▸ hξ)
  have hlam : lam ≠ 0 := right_ne_zero_of_mul (n1 ▸ hξ)
  have h₀ : 0 + 2 * D.R.rS + 2 = D.R.m := by
    obtain ⟨c, hc⟩ := D.R.m_even
    have := D.R.two_le_m
    unfold Ranks.rS
    omega
  obtain ⟨s, hs, he⟩ := GlobalTheory.LineIdeal.first_vec (_root_.GlobalTheory.MiTop.formsAtZero W u) (W.S.tr u) hW.bot.idE hc.std B hμ n2 ⟨0, hr⟩ rfl
  have hI := GlobalTheory.LineIdeal.all_ideal hc sh (fun n h x hx => by subst h; exact hp x hx) (fun j hj => by
      change 0 < (D.sp.X (j + 1)).rank
      rw [Formalism.L2.Forms.rankN D _ hj]
      unfold Ranks.N
      have := D.R.m_add_three_le_k
      omega) hlam n3 hx (hα x).1 hψ 0 D.R.rS h₀ (D.R.rS - 1) ⟨0, hr⟩ (by simp only; omega)
  have hd : B.d.e = (f.c.bes 0 D.R.rS h₀).d.e := eq_of_heq (Sigma.mk.inj (congrArg
    (fun Z : BesLev D D.R.rS => (⟨Z.V.rank, Z.d.e⟩ : Σ n, Matrix (Fin n) (Fin D.R.rS) D.host.E)) (hb.lev h₀))).2
  rw [← mul_assoc (α * α), ← mul_assoc ((xiU D * α * cU α) ^ _)] at hI
  have uK : IsU x (((xiU D * α * cU α) ^ (D.R.rS - 1) * (α * α * (α * (xiU D * cU α)⁻¹) ^ D.R.rS) : (AE D)ˣ) : AE D) := by
    have h1 : IsU x (((xiU D * cU α)⁻¹ : (AE D)ˣ) : AE D) := (uξ.mul uc).inv (xiU D * cU α).mul_inv
    rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
    exact (((uξ.mul uα).mul uc).pow _).mul ((uα.mul uα).mul ((uα.mul h1).pow _))
  generalize (xiU D * α * cU α) ^ (D.R.rS - 1) * (α * α * (α * (xiU D * cU α)⁻¹) ^ D.R.rS) = K at hI uK
  have uS : IsU x (incA D (-s * (D.host.xi0 ^ (D.R.m / 2) * (W.S.X.B.g : D.host.E) ^ D.R.rS))) := by
    have h1 : IsU x (incA D (D.host.xi0 ^ (D.R.m / 2) * (W.S.X.B.g : D.host.E) ^ D.R.rS)) := by
      rw [map_mul, map_pow, map_pow]
      exact (IsU.pow (u := incA D D.host.xi0) uξ _).mul (ug.pow _)
    rcases hs with rfl | rfl
    · rw [neg_one_mul, map_neg]; exact h1.neg
    · rwa [neg_neg, one_mul]
  have hg0 : (W.S.X.B.g : D.host.E) ≠ 0 := by
    rw [W.S.X.g_eq]
    exact Nat.cast_ne_zero.2 (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> simp
  obtain ⟨w, hw⟩ : ∃ w, w = s * (μ * (W.S.X.B.g : D.host.E) ^ D.R.rS) := ⟨_, rfl⟩
  have hw0 : w ≠ 0 := hw ▸ mul_ne_zero hs0 (mul_ne_zero hμ (pow_ne_zero _ hg0))
  have hlw : -s * (D.host.xi0 ^ (D.R.m / 2) * (W.S.X.B.g : D.host.E) ^ D.R.rS) = lam * w := by
    rw [hw]
    linear_combination (-s * (W.S.X.B.g : D.host.E) ^ D.R.rS) * n1
  rw [← hw] at he
  rw [hlw, map_mul] at uS
  have e1 : incA D w * incA D w⁻¹ = 1 := (inU w hw0).mul_inv
  have hy : (fun i => a * incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (rank_eq W.S.X W.Q.instEq) i)))) =
      colMul B.d.jX ⟨0, hr⟩ (incA D w⁻¹ * a) := by
    funext i
    change _ = _ * incA D (B.d.e i ⟨0, hr⟩)
    rw [he, map_mul]
    generalize incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (rank_eq W.S.X W.Q.instEq) i))) = t
    linear_combination (-a * t) * e1
  have hj : B.d.jX = (f.c.bes 0 D.R.rS h₀).d.jX := congrArg rat hd
  have h1 := hI (incA D w⁻¹ * a) (Ideal.mul_mem_left _ _ ha)
  rw [← hj] at h1
  refine (iff_of_eq (congrArg (· ∈ latV (D.sp.Y 0) (v.N 0) (· = x)) hy)).trans (h1.trans ?_)
  rw [(uK.mul uS) _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ ha))]
  have e2 := (K * inU lam hlam).mul_inv
  rw [Units.val_mul, inU_val] at e2
  refine iff_of_eq (congrArg (· ∈ _) ?_)
  linear_combination (incA D w * incA D w⁻¹ * a) * e2 + a * e1
end GlobalTheory.LineOffT
end
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.ColMatchFam
theorem col_level_match_fam_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.LevTraceAlt f B → B.Adapted (W.S.tr u).wt → ∀ a₀ : GA D (D.sp.X 0), IsTransportAdelicCorrection (W.S.tr u) a₀ → ∀ x ∈ GfC (D.sp.X 0), ((show GA D (D.sp.Y 0) from f.g.b 0)⁻¹ * embA B.d B.o x * (show GA D (D.sp.Y 0) from f.g.b 0) ∈ _root_.GlobalTheory.MiTop.rJ_z W ↔ ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ * embA B.d B.o (a₀ * x * a₀⁻¹) * ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u)) ∈ rowJ W.S.X W.Q.instEq) ∧ ((show GA D (D.sp.Y 0) from f.g.b 0)⁻¹ * embA B.d B.o x * (show GA D (D.sp.Y 0) from f.g.b 0) ∈ _root_.GlobalTheory.MiTop.rJ_z W → rowChi W.S.X W.Q.instEq (((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ * embA B.d B.o (a₀ * x * a₀⁻¹) * ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))) = _root_.GlobalTheory.MiTop.realCharacter W ((show GA D (D.sp.Y 0) from f.g.b 0)⁻¹ * embA B.d B.o x * (show GA D (D.sp.Y 0) from f.g.b 0))) := by
  intro D L hT Gi Gl Kc Yd cX ex W hP u f B hLev hAd a₀ hH0 b hb
  have hE : GlobalTheory.Core.Mi.IdE W.S.X := hP.bot.idE
  have hLM := hP.bot.hyp.2.1 u
  obtain ⟨y, hy⟩ := GlobalTheory.AdForm.RdVal.finM_mem (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _))
    (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) rfl b
  obtain ⟨hU, hchi⟩ := hLev b hb y hy.symm
  have hgf : a₀ * b * a₀⁻¹ ∈ GfC (D.sp.X 0) := mul_mem (mul_mem hH0.1 hb) (inv_mem hH0.1)
  have hRep := GlobalTheory.Core.Mi.FinFrame.repM_toH D W.S.X W.Q.instEq u W.Q.Rl.ψ B (_root_.GlobalTheory.MiTop.formsAtZero W u) (W.S.tr u) hE hAd (a₀ * b * a₀⁻¹)
  have e0 : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a₀ =
      ((W.S.tr u).h0.1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) := hH0.2
  have hh0 : (((W.S.tr u).h0⁻¹).1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) *
      ((W.S.tr u).h0.1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one]
  have hfa : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a₀⁻¹ =
      (((W.S.tr u).h0⁻¹).1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) :=
    GlobalTheory.ColMatch.unitaryAdelicPointFiniteMatrix_inv_eq_of_mul_eq_one a₀ _ (by rw [e0]; exact hh0)
  have hfg : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) (a₀ * b * a₀⁻¹) =
      (((W.S.tr u).h0 * y * (W.S.tr u).h0⁻¹).1.1 : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) := by
    refine (unitaryAdelicPointFiniteMatrix_base_space_mul _ _).trans ((congrArg₂ (· * ·) ((unitaryAdelicPointFiniteMatrix_base_space_mul _ _).trans (congrArg₂ (· * ·) e0 hy.symm)) hfa).trans ?_)
    simp only [Subgroup.coe_mul, Units.val_mul]
  have hRF : Formalism.L2.SG.ColDict.RepF W.S.X (W.S.tr u).wt (W.S.tr u).ιA ((B.toH (a₀ * b * a₀⁻¹)).2 : W.S.X.B.I.Gf)
      ((W.S.tr u).h0 * y * (W.S.tr u).h0⁻¹) := by
    have h := hRep
    rw [hfg] at h
    exact h
  obtain ⟨hmemIff, hpsi⟩ := hLM.2 (B.toH (a₀ * b * a₀⁻¹)).2 _ hRF
  have hconj : (W.S.tr u).h0⁻¹ * ((W.S.tr u).h0 * y * (W.S.tr u).h0⁻¹) * (W.S.tr u).h0 = y := by group
  have hfinE : embA B.d B.o (a₀ * b * a₀⁻¹) ∈ GfC (D.sp.Y 0) := GlobalTheory.Core.Mi.CenAct.embA_mem_GfC B.d B.o hgf
  have hfst : (iotaX W.S.X W.Q.instEq (embA B.d B.o (a₀ * b * a₀⁻¹))).1 = 1 :=
    GlobalTheory.Core.Mi.CenAct.iotaX_fst W.Q.instEq hfinE
  have hio : iotaX W.S.X W.Q.instEq (((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ * embA B.d B.o (a₀ * b * a₀⁻¹) *
      (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u)) =
      (1, (W.S.X.xu u)⁻¹ * ((B.toH (a₀ * b * a₀⁻¹)).2 : W.S.X.B.I.Gf) * W.S.X.xu u) := by
    rw [map_mul, map_mul, map_inv, (iotaX W.S.X W.Q.instEq).apply_symm_apply]
    ext
    · simp only [Prod.fst_mul, Prod.fst_inv, hfst, mul_one, inv_one]
    · rfl
  have hrow : ∀ k, k ∈ rowJ W.S.X W.Q.instEq ↔
      (iotaX W.S.X W.Q.instEq k).1 = 1 ∧ (iotaX W.S.X W.Q.instEq k).2 ∈ W.S.X.K2 := fun k => Iff.rfl
  have hU' : ∀ hyU : (y : GL _ _) ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.U,
      ((((W.S.tr u).h0⁻¹ * ((W.S.tr u).h0 * y * (W.S.tr u).h0⁻¹) * (W.S.tr u).h0 :
        Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
          GL _ _) ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.U) := fun hyU => by rw [hconj]; exact hyU
  refine ⟨⟨fun hk => ?_, fun hr => ?_⟩, fun hk => ?_⟩
  · have hm := hmemIff.2 (hU' (hU.2 hk))
    rw [hrow, hio]
    exact ⟨rfl, hm⟩
  · rw [hrow, hio] at hr
    have h2 := hmemIff.1 hr.2
    rw [hconj] at h2
    exact hU.1 h2
  · have hyU := hU.2 hk
    have hm := hmemIff.2 (hU' hyU)
    have hp := hpsi hm (hU' hyU)
    have hc := hchi hyU
    have hchieq : (((_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.chi ⟨_, hU' hyU⟩ : ℂˣ) : ℂ) = (((_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.chi ⟨_, hyU⟩ : ℂˣ) : ℂ) := by
      have key : ∀ (z : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
          (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (hz : z.1 ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.U), z = y →
          (((_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.chi ⟨_, hz⟩ : ℂˣ) : ℂ) = (((_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.chi ⟨_, hyU⟩ : ℂˣ) : ℂ) := by
        rintro z hz rfl
        rfl
      exact key _ _ hconj
    unfold rowChi
    rw [hio]
    have hpv : ((psiK W.S.X u _ ⟨_, hm⟩ : ℂˣ) : ℂ) =
        W.S.X.chi2 ((W.S.X.xu u)⁻¹ * ((B.toH (a₀ * b * a₀⁻¹)).2 : W.S.X.B.I.Gf) * W.S.X.xu u) := rfl
    have hn : ‖W.S.X.chi2 ((W.S.X.xu u)⁻¹ * ((B.toH (a₀ * b * a₀⁻¹)).2 : W.S.X.B.I.Gf) * W.S.X.xu u)‖ = 1 :=
      W.S.Y.hK.2.2.2.2 _ hm
    have h1 : W.S.X.chi2 ((W.S.X.xu u)⁻¹ * ((B.toH (a₀ * b * a₀⁻¹)).2 : W.S.X.B.I.Gf) * W.S.X.xu u) *
        _root_.GlobalTheory.MiTop.realCharacter W ((show GA D (D.sp.Y 0) from f.g.b 0)⁻¹ * embA B.d B.o b * (show GA D (D.sp.Y 0) from f.g.b 0)) = 1 := by
      rw [← hpv, hp, hchieq]
      exact hc
    generalize W.S.X.chi2 ((W.S.X.xu u)⁻¹ * ((B.toH (a₀ * b * a₀⁻¹)).2 : W.S.X.B.I.Gf) * W.S.X.xu u) = c at hn h1 ⊢
    generalize _root_.GlobalTheory.MiTop.realCharacter W ((show GA D (D.sp.Y 0) from f.g.b 0)⁻¹ * embA B.d B.o b * (show GA D (D.sp.Y 0) from f.g.b 0)) = L at h1 ⊢
    have hsc : star c * c = 1 := by
      rw [Complex.star_def, Complex.conj_mul', hn]
      simp
    calc star c = star c * (c * L) := by rw [h1, mul_one]
      _ = (star c * c) * L := by ring
      _ = L := by rw [hsc, one_mul]
end GlobalTheory.ColMatchFam
end
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

theorem _root_.GlobalTheory.T.descent_top_self_dual_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ j (h : j + 2 * 0 + 2 = D.R.m) d₀, _root_.GlobalTheory.Fam.IsDivisorGlobal W (j + 1) (_root_.GlobalTheory.Fam.pk_z W).MX (_root_.GlobalTheory.Fam.pk_z W).ΛX (_root_.GlobalTheory.Fam.pk_z W).βX (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) d₀ → IsSelfDualC (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ∧ IsSelfDualC D.sp.X' (_root_.GlobalTheory.Fam.pk_z W).ΛX ∧ ∃ M : GlobalTheory.FinPl.Lat (Yc D (j + 1)), IsSelfDualC (Yc D (j + 1)) M ∧ (∀ P, GlobalTheory.FinPl.Moves (Yc D (j + 1)) (f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) M P) ∧ GlobalTheory.FinPl.Vac f.c.ψ (Yc D (j + 1)) D.sp.X' M f.g.LT (fun _ => True) (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h)) := by
  first | exact @_root_.GlobalTheory.TopVac.moved_vacuum_alt | exact _root_.GlobalTheory.TopVac.moved_vacuum_alt | (intros; apply _root_.GlobalTheory.TopVac.moved_vacuum_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_selfDual_lattice : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ j, j < D.R.m → ∃ L : GlobalTheory.FinPl.Lat (Yc D j), IsSelfDualC (Yc D j) L := by
  first | exact @_root_.GlobalTheory.SDLatY.exists_selfDual_latY_alt | exact _root_.GlobalTheory.SDLatY.exists_selfDual_latY_alt | (intros; apply _root_.GlobalTheory.SDLatY.exists_selfDual_latY_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.finite_level_places : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → Set.Finite {PP : Pl D.host.E | PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ _root_.GlobalTheory.Fam.QAllAlt W PP} := by
  first | exact @_root_.GlobalTheory.Fam.finite_levelPlaces_or_tuplePlaces_alt | exact _root_.GlobalTheory.Fam.finite_levelPlaces_or_tuplePlaces_alt | (intros; apply _root_.GlobalTheory.Fam.finite_levelPlaces_or_tuplePlaces_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_selfDual_lattice_moves : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ j, j < D.R.m → ∀ g : GA D (Yc D j), ∃ M : GlobalTheory.FinPl.Lat (Yc D j), IsSelfDualC (Yc D j) M ∧ ∀ P, GlobalTheory.FinPl.Moves (Yc D j) g ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) M P := by
  first | exact @_root_.GlobalTheory.MovedLat.movedLat_alt | exact _root_.GlobalTheory.MovedLat.movedLat_alt | (intros; apply _root_.GlobalTheory.MovedLat.movedLat_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

theorem _root_.GlobalTheory.T.descent_data_step_self_dual_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ j, j + 1 < D.R.m → ∀ (M : GlobalTheory.FinPl.Lat (Yc D j)) (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))), GlobalTheory.FinPl.Moves (Yc D j) (f.g.b j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) M (fun _ => True) → GlobalTheory.FinPl.Moves (Yc D (j + 1)) (f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) M' (fun _ => True) → ∀ p, p ∉ v.gP → GlobalTheory.FinPl.latV (Yc D j) (v.N j) (· = p) = GlobalTheory.FinPl.latV (Yc D j) M (· = p) ∧ GlobalTheory.FinPl.latV (Yc D (j + 1)) (v.N (j + 1)) (· = p) = GlobalTheory.FinPl.latV (Yc D (j + 1)) M' (· = p) := by
  first | exact @_root_.GlobalTheory.Fam.latV_N_eq_off_level_alt | exact _root_.GlobalTheory.Fam.latV_N_eq_off_level_alt | (intros; apply _root_.GlobalTheory.Fam.latV_N_eq_off_level_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_level_elements_step_vector_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ t j, j + 1 < D.R.m → ∀ [Fintype (_root_.GlobalTheory.Fam.complexLevelStructure W).H], ∃ κ : (_root_.GlobalTheory.Fam.complexLevelStructure W).H → GA D (Yc D j), (∀ p, κ p ∈ levS (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W))) ∧ ∀ v, IsStepVecOf (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D j) (Yc D (j + 1)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) ((_root_.GlobalTheory.Fam.pk_z W).chi (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).Q t) ((_root_.GlobalTheory.Fam.pk_z W).xiR t) ((_root_.GlobalTheory.Fam.pk_z W).vac j) v → ∀ Q, pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D j) (Yc D (j + 1)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) v Q = ∑ p, (levChi (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) (κ p))⁻¹ • ((_root_.GlobalTheory.Fam.pk_z W).ωY t j (κ p, 1)) ((_root_.GlobalTheory.Fam.pk_z W).ptY t j Q) := by
  first | exact @_root_.GlobalTheory.FockVecSum.fockVec_eq_sum_alt | exact _root_.GlobalTheory.FockVecSum.fockVec_eq_sum_alt | (intros; apply _root_.GlobalTheory.FockVecSum.fockVec_eq_sum_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.realEq_of_colOK' : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ f : _root_.GlobalTheory.Fam.FamilyCharacter W u, f.ColOK → RealEq f.t := by
  first | exact @_root_.GlobalTheory.Fam.realEq_of_colOK_alt | exact _root_.GlobalTheory.Fam.realEq_of_colOK_alt | (intros; apply _root_.GlobalTheory.Fam.realEq_of_colOK_alt <;> assumption)
end
end

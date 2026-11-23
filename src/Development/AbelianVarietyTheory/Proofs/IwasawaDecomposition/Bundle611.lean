module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle607
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyAgreeRealOfReadGalois
import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle003
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle409
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532

import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodProjectorSmallestSpaceForms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle278
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle271
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle151
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Formalism.LocalToGlobal.Divisibility.RowLatLemmas
import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
import Formalism.LocalToGlobal.IndefiniteReal.Bundle027
import Formalism.LocalToGlobal.IndefiniteReal.LiftCoordinatesInGoodPartFamily
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle022
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar


noncomputable section

namespace GlobalTheory.HeightCounting.Up.ThirdAgree

open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.RecTie GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting.Up.RealOfReading

section Gen

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}

theorem agree_of_data (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0) {cf : CharFrame D} {nch : NChoice D}
    (tp : TupTied D cf nch) (hC : R.C = cf) (Xd : DivX D) (E : EigIdx D Xd) (labPi : E.Pi → A3.A.fam.base.Ix) (hb htup hg hf)
    (M : MtFam D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (hrep : ∀ σ, (rep σ).Iso (principalLevelFrame.rowRepR R.θ (Y.eFT σ)))
    (c : ∀ i, CoefA (Vc D i)) (hc : R.cV = c) (PV : ∀ i : Fin D.R.m, principalLevelFrame.RowPsi (Vc D i) D.R.nV)
    (std : ∀ i, R3.StdFrame Y.hF (PV i))
    (eW : ∀ μ, Used0 D μ → ∀ i : Fin D.R.m, (M μ (i.1 + 1) (by omega) (by omega)).wt.W ≃ₗ[ℂ] (c i).W)
    (jm : ∀ μ, Used0 D μ → ∀ i : Fin D.R.m, D.what₂.Mt μ (i.1 + 1) → GA D (Vc D i) → (c i).W)
    (hj : ∀ μ h i x, HEq (Y.IL.jMt μ h i x).1 (jm μ h i x))
    (read : ∀ μ (h : Used0 D μ) (i : Fin D.R.m) (x : D.what₂.Mt μ (i.1 + 1)) (g : GAf D.host.E D.R.nV),
      eW μ h i ((M μ (i.1 + 1) (by omega) (by omega)).real x g) = jm μ h i x ((PV i).ψ g))
    (rat : ∀ (i : Fin D.R.m) (g : GAf D.host.E D.R.nV), g ∈ ReciprocityTheory.Aut.GQ D.host.E D.R.nV ↔
      ∃ γ ∈ Formalism.L2.Theta.GQ (Vc D i), finHom (Vc D i) γ = finHom (Vc D i) ((PV i).ψ g))
    (wt : ∀ μ (h : Used0 D μ) (i : Fin D.R.m) (g : ReciprocityTheory.Aut.GQ D.host.E D.R.nV), ∀ γ ∈ Formalism.L2.Theta.GQ (Vc D i),
      finHom (Vc D i) γ = finHom (Vc D i) ((PV i).ψ g) → ∀ v,
        eW μ h i ((M μ (i.1 + 1) (by omega) (by omega)).wt.ρ g v) = (c i).ρ γ (eW μ h i v)) :
    Nonempty (GlobalTheory.NJoin.Agree (realOfRead R.toRealDat F.lv2 Y tp hC Xd E labPi hb htup hg hf) M rep) := by
  subst hc
  refine ⟨⟨Y.hF, PV, fun j => (StandardFrameAgreement.stdFrame_iff _ _).1 (std j), fun j => (StandardFrameAgreement.stdFrame_iff _ _).1 (Y.stdPsi.2 j),
    fun _ => 1, ?_, fun μ hμ j => (eW μ hμ j).symm, ?_, ?_, hrep⟩⟩
  · intro j h
    simp only [inv_one, one_mul, mul_one]
    exact rat j h
  · intro μ hμ j h γ hγ he v
    have he' := he
    simp only [inv_one, one_mul, mul_one] at he'
    have key := wt μ hμ j h γ hγ he' ((eW μ hμ j).symm v)
    refine (LinearEquiv.symm_apply_eq _).2 ?_
    refine Eq.trans ?_ key.symm
    exact congrArg _ (LinearEquiv.apply_symm_apply _ v).symm
  · intro μ hμ j x h
    refine (LinearEquiv.eq_symm_apply _).2 ?_
    refine (read μ hμ j x h).trans ?_
    simp only [inv_one, one_mul]
    exact (congrFun (eq_of_heq (hj μ hμ j x)) _).symm

theorem heq_apply {Mt : D.what₂.Tup → ℕ → Hs} {c c' : ∀ i, CoefA (Vc D i)} (h : c = c')
    (j : ∀ μ (i : Fin D.R.m), (Mt μ ((i : ℕ) + 1)).T →ₗ[ℂ] (GA D (Vc D i) → (c i).W))
    (j' : ∀ μ (i : Fin D.R.m), (Mt μ ((i : ℕ) + 1)).T →ₗ[ℂ] (GA D (Vc D i) → (c' i).W)) (hj : HEq j j') (μ i x) :
    HEq (j μ i x) (j' μ i x) := by
  subst h
  cases hj
  rfl

end Gen

section Copy

variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C) {px : PreX B.toPre} {I : ColIn B px} {hX : B.fields.Ok} {T : TwDat B}
  {Wt : Set B.places.Pl}

def cpR (z : Dat a.st I hX T Wt) :
    @RealDat3 b.st.toD7 _ _ _ _ _ _ (famR b.st I hX (usedOf I T Wt) z.Xg z.tr) (coreJ b z.core).Q.c.F _ _ ((by exact @alg B C a b (↥(@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instField (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instNF (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (Pj.instCMHost (@Late.st B C a).toD7) (@Pj.Par.H (@Late.st B C a).toD7 (@Pj.Core.Q (@Late.st B C a).toD7 (@Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Pj.Par.l (@Late.st B C a).toD7 (@Pj.Core.Q (@Late.st B C a).toD7 (@Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Pj.Par.c (@Late.st B C a).toD7 (@Pj.Core.Q (@Late.st B C a).toD7 (@Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))))) (@IntermediateField.toField Rat Complex Rat.instField Complex.instField (@DivisionRing.toRatAlgebra Complex (@Field.toDivisionRing Complex Complex.instField) Complex.instCharZero) (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instField (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instNF (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (Pj.instCMHost (@Late.st B C a).toD7) (@Pj.Par.H (@Late.st B C a).toD7 (@Pj.Core.Q (@Late.st B C a).toD7 (@Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Pj.Par.l (@Late.st B C a).toD7 (@Pj.Core.Q (@Late.st B C a).toD7 (@Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Pj.Par.c (@Late.st B C a).toD7 (@Pj.Core.Q (@Late.st B C a).toD7 (@Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))))) (@Dat.alg (@Late.st B C a) px I hX T Wt z))) :=
  (by with_unfolding_all exact ((real3 b (iK := z.alg) z.R) :))

def cpV (c : ∀ i, CoefA (Vc a.D i)) : ∀ i, CoefA (Vc b.D i) := fun i => (by with_unfolding_all exact ((coefA b (c ((by with_unfolding_all exact (i :))))) :))

theorem cV_copy (z₀ : Dat a.st I hX T Wt) (z : Dat b.st I hX T Wt) (h1 : z.Xg = z₀.Xg) (h2 : z.tr = z₀.tr)
    (h3 : HEq z.core (coreJ b z₀.core)) (h4 : HEq z.R (real3 b (iK := z₀.alg) z₀.R)) : z.R.cV = cpV b z₀.R.cV := by
  obtain @⟨Xg, tr, core, al, alg_eq, R, cG, geo, pins, lev, idG, good, mu, l1, l2⟩ := z
  dsimp only at h1 h2 h3 h4
  subst h1 h2
  obtain rfl : core = coreJ b z₀.core := eq_of_heq h3
  have e : al = (by with_unfolding_all exact ((alg b z₀.alg) :)) := by
    refine Algebra.algebra_ext _ _ fun y => B.embLL.injective ?_
    exact (alg_eq y).trans ((by with_unfolding_all exact ((z₀.alg_eq ((by with_unfolding_all exact (y :)))).symm :)))
  subst e
  obtain rfl : R = cpR b z₀ := eq_of_heq (h4.trans ((by with_unfolding_all exact ((HEq.refl (cpR b z₀)) :))))
  exact (by with_unfolding_all exact ((Eq.refl (cpV b z₀.R.cV)) :))

theorem cV_two (b' : Late B C) {c₀ : ∀ i, CoefA (Vc a.D i)} {c : ∀ i, CoefA (Vc b.D i)} {c' : ∀ i, CoefA (Vc b'.D i)}
    (h : c = cpV b c₀) (h' : c' = cpV b' c₀) : c' = cpV b' c := by
  subst h h'
  exact (by with_unfolding_all exact ((Eq.refl (cpV b' c₀)) :))

end Copy

section Main

theorem iso_of_eq {Lf : Type} [Field Lf] [NumberField Lf] [IsCMField Lf] {n : ℕ} {π π' : NG.FinTyp Lf n} (h : π = π') : π.Iso π' :=
  h ▸ NG.IsoRep.refl _


end Main

end GlobalTheory.HeightCounting.Up.ThirdAgree

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section
namespace GlobalTheory.KapRec.Eigen

theorem exists_scaled_ext {K : Type} [Field K] (σ : K →+* ℂ) {n : ℕ} {W H : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (j : (Fin n → K) →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun i => j (Pi.single i 1))
    (hsp : Submodule.span ℂ (Set.range fun i => j (Pi.single i 1)) = ⊤) (k : (Fin n → K) →ₛₗ[σ] H) {c : ℝ}
    (hc : ∀ x y, ⟪k x, k y⟫_ℂ = (c : ℂ) * ⟪j x, j y⟫_ℂ) :
    ∃ u : W →ₗ[ℂ] H, (∀ w, ‖u w‖ ^ 2 = c * ‖w‖ ^ 2) ∧ ∀ x, u (j x) = k x := by
  let b : Module.Basis (Fin n) ℂ W := Module.Basis.mk hli (le_of_eq hsp.symm)
  let u := b.constr ℂ (fun i => k (Pi.single i 1))
  have hb : ∀ i, b i = j (Pi.single i 1) := fun i => Module.Basis.mk_apply _ _ _
  have hu : ∀ i, u (b i) = k (Pi.single i 1) := fun i => Module.Basis.constr_basis _ _ _ _
  have hdec : ∀ x : Fin n → K, x = ∑ i, x i • Pi.single i 1 := fun x => by
    ext l
    simp [Finset.sum_apply, Pi.single_apply]
  have hj : ∀ x, j x = ∑ i, σ (x i) • b i := fun x => by
    conv_lhs => rw [hdec x]

    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smulₛₗ, hb]
  have hk : ∀ x, k x = ∑ i, σ (x i) • k (Pi.single i 1) := fun x => by
    conv_lhs => rw [hdec x]

    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smulₛₗ]
  have hA : ∀ x, u (j x) = k x := fun x => by

    rw [hj, map_sum, hk]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hu]
  have hbas : ∀ i l, ⟪u (b i), u (b l)⟫_ℂ = (c : ℂ) * ⟪b i, b l⟫_ℂ := fun i l => by
    rw [hu, hu, hb, hb, hc]
  have key : ∀ z w, ⟪u z, u w⟫_ℂ = (c : ℂ) * ⟪z, w⟫_ℂ := fun z w => by
    rw [← b.sum_repr z, ← b.sum_repr w]

    simp only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right, hbas, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
  refine ⟨u, fun w => ?_, hA⟩
  have h := key w w
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  exact Complex.ofReal_injective (by push_cast; exact h)



theorem topMap_exists : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → ∃ uA : D.what₂.Amb (Y.tup A3.A.μ0) →ₗ[ℂ] (R.HX A3.A.μ0).H, (∀ x, ‖uA x‖ ^ 2 = RealDat.nP F.lv2 true * ‖x‖ ^ 2) ∧ ∀ x, uA (Y.jA A3.A.μ0 x) = R.jX A3.A.μ0 (rowForm A3.A F.P1 F.ψ1 A3.A.μ0 x) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH
  have hFT := Y.formsA A3.A.μ0
  have hpos : (0 : ℝ) < RealDat.nP F.lv2 true := by
    unfold RealDat.nP
    exact_mod_cast Nat.card_pos
  let rf : (Fin (rDim D A3.A F.P1 F.ψ1 A3.A.μ0) → D.what₂.LL) →ₗ[D.what₂.LL] A3.A.fam.amb.FR A3.A.μ0 :=
    { toFun := rowForm A3.A F.P1 F.ψ1 A3.A.μ0
      map_add' := DatApi.rowForm_add A3.A F.P1 F.ψ1 A3.A.μ0
      map_smul' := DatApi.rowForm_smul A3.A F.P1 F.ψ1 A3.A.μ0 }
  refine exists_scaled_ext D.what₂.embLL (Y.jA A3.A.μ0) hFT.li hFT.span ((R.jX A3.A.μ0).comp rf) fun x y => ?_
  have h1 : (((RealDat.nP F.lv2 true)⁻¹ : ℝ) : ℂ) * ⟪R.jX A3.A.μ0 (rowForm A3.A F.P1 F.ψ1 A3.A.μ0 x), R.jX A3.A.μ0 (rowForm A3.A F.P1 F.ψ1 A3.A.μ0 y)⟫_ℂ = D.what₂.embLL (Formalism.DivisionValues.hform (rH D A3.A F.P1 F.ψ1 A3.A.μ0) x y) :=
    GlobalTheory.T.hilbert_inner_rowForms_eq_level_class_sum D G Pl0 T A3.A Ks R.toRealDat F.lv2 hP.char.base true A3.A.μ0 x y
  have alg : ∀ a : ℂ, a = ((RealDat.nP F.lv2 true : ℝ) : ℂ) * ((((RealDat.nP F.lv2 true)⁻¹ : ℝ) : ℂ) * a) := fun a => by
    rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hpos.ne', Complex.ofReal_one, one_mul]
  rw [hFT.inner x y]
  refine Eq.trans ?_ (congrArg (fun z => ((RealDat.nP F.lv2 true : ℝ) : ℂ) * z) h1)
  exact alg ⟪R.jX A3.A.μ0 (rowForm A3.A F.P1 F.ψ1 A3.A.μ0 x), R.jX A3.A.μ0 (rowForm A3.A F.P1 F.ψ1 A3.A.μ0 y)⟫_ℂ

theorem iiStar_apply_eq {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    (S : RowSide D EE) (μ : D.what₂.Tup) (y : EE) :
    (S.iotaQ μ ∘ₗ LinearMap.adjoint (S.iotaQ μ)) y = S.iota μ (S.eOp μ (LinearMap.adjoint (S.iota μ) y)) := by
  set w := LinearMap.adjoint (S.iotaQ μ) y with hw
  set z := LinearMap.adjoint (S.iota μ) y with hz
  have hQ : ∀ q : S.Qsp μ, ⟪(q : S.Amb μ), (w : S.Amb μ)⟫_ℂ = ⟪(q : S.Amb μ), z⟫_ℂ := by
    intro q
    rw [← Submodule.coe_inner, hw, hz, LinearMap.adjoint_inner_right, LinearMap.adjoint_inner_right]
    rfl
  have heV : ∀ x ∈ S.V0 μ, S.eOp μ x = x := by
    rintro _ ⟨a, rfl⟩
    exact congrArg (fun f : S.Amb μ →ₗ[ℂ] S.Amb μ => f a) (S.eOp_idem μ)
  set d := S.eOp μ z - (w : S.Amb μ) with hd
  have hdV : d ∈ S.V0 μ := sub_mem (LinearMap.mem_range_self _ _) w.2.1
  have hdQ : ∀ q : S.Qsp μ, ⟪(q : S.Amb μ), d⟫_ℂ = 0 := by
    intro q
    rw [hd, inner_sub_right, hQ, ← S.eOp_sa μ, heV _ q.2.1, sub_self]
  have hdU : d ∈ S.Usp μ := by
    set r := d - (S.Usp μ).starProjection d with hr0
    have hUV : S.Usp μ ≤ S.V0 μ := inf_le_left
    have hr : r ∈ S.Qsp μ :=
      ⟨sub_mem hdV (hUV (Submodule.starProjection_apply_mem _ _)), Submodule.sub_starProjection_mem_orthogonal d⟩
    have h1 : ⟪r, d⟫_ℂ = 0 := hdQ ⟨r, hr⟩
    have h2 : ⟪r, (S.Usp μ).starProjection d⟫_ℂ = 0 :=
      Submodule.inner_left_of_mem_orthogonal (Submodule.starProjection_apply_mem _ _) hr.2
    have h3 : ⟪r, r⟫_ℂ = 0 := by
      conv_lhs => rw [hr0]
      rw [inner_sub_right, ← hr0, h1, h2, sub_zero]
    have h4 : r = 0 := inner_self_eq_zero.1 h3
    rw [hr0, sub_eq_zero] at h4
    rw [h4]
    exact Submodule.starProjection_apply_mem _ _
  have hk : S.iota μ d = 0 := hdU.2
  rw [hd, map_sub, sub_eq_zero] at hk
  exact hk.symm

theorem transport_eig {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    (S : RowSide D EE) {E H : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (Θ : E →ₗ[ℂ] H) {μ μ' : D.what₂.Tup}
    (hμ : μ = μ') (uA : S.Amb μ →ₗ[ℂ] E) (uE : EE →ₗ[ℂ] H) {n : ℝ} (hn : 0 < n) (nA : ∀ x, ‖uA x‖ ^ 2 = n * ‖x‖ ^ 2)
    (nE : ∀ y, ‖uE y‖ ^ 2 = n * ‖y‖ ^ 2) (hι : ∀ x, uE (S.iota μ x) = Θ (uA x)) (y : EE)
    (hy : LinearMap.adjoint Θ (uE y) ∈ (S.V0 μ).map uA) {a : ℂ} (ha : Θ (LinearMap.adjoint Θ (uE y)) = a • uE y) :
    S.iota μ' (S.eOp μ' (LinearMap.adjoint (S.iota μ') y)) = a • y := by
  subst hμ
  rw [← iiStar_apply_eq]
  exact GlobalTheory.KappaLevels.iota_adjoint_transport Θ (S.iota μ) (S.V0 μ) uA uE hn nA nE (fun x _ => hι x) y hy ha



theorem eigen : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → Lam3 Z → (∀ σ (i : Fin D.R.m), D.what₂.isot ((i : ℕ) + 1) (D.what₂.ft σ) ≠ ⊥) → ∀ σ, (RowSide.sharp D).iota D.what₂.mu0 ((RowSide.sharp D).eOp D.what₂.mu0 (LinearMap.adjoint ((RowSide.sharp D).iota D.what₂.mu0) (D.what₂.onb σ))) = ((R.kap * ∏ j ∈ Finset.Icc 1 D.R.m, D.what₂.lamP D.what₂.mu0 j (D.what₂.ft σ) : ℝ) : ℂ) • D.what₂.onb σ := by
  intro hCRD D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH hL hI σ
  obtain ⟨uE, -, nE, hE⟩ := GlobalTheory.Adopt.levelRowsReading_embedding_goodRowsModel_with_norm D G Pl0 T A3.A Ks R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop true D.what₂.EE
    (RowSide.sharp D) Y.Ish hP.char.base.models.HE Y.tied.sharp.ee
  obtain ⟨uA, nA, hA⟩ := topMap_exists D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH
  obtain ⟨p, hp, hl⟩ := GlobalTheory.T.basisRow_mem_definiteFamily_type_part hCRD D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hL hI uE hE σ
  have hup := GlobalTheory.T.adjoint_compositeLift_row_mem_span_goodRationalForms hCRD.2.2.2.2 D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH uE hE (D.what₂.onb σ)
  have hdt := (GlobalTheory.T.compositeIntertwiner_eq_thetaLift_goodProjector hCRD D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH).1 A3.A.μ0
  have ha : R.Th A3.A.μ0 (LinearMap.adjoint (R.Th A3.A.μ0) (uE (D.what₂.onb σ))) =
      ((R.kap * ∏ j ∈ Finset.Icc 1 D.R.m, D.what₂.lamP D.what₂.mu0 j (D.what₂.ft σ) : ℝ) : ℂ) • uE (D.what₂.onb σ) := by
    refine (hH.prim.thmB A3.A.μ0 p (uE (D.what₂.onb σ)) hp).trans ?_
    rw [hl]
  have hpos : (0 : ℝ) < RealDat.nP F.lv2 true := by
    unfold RealDat.nP
    exact_mod_cast Nat.card_pos
  have hFT := Y.formsA A3.A.μ0
  have hι : ∀ a, uE ((RowSide.sharp D).iota (Y.tup A3.A.μ0) a) = R.Th A3.A.μ0 (uA a) := by
    have key : uE ∘ₗ (RowSide.sharp D).iota (Y.tup A3.A.μ0) = R.Th A3.A.μ0 ∘ₗ uA := by
      refine LinearMap.ext_on_range hFT.span fun i => ?_
      show uE ((RowSide.sharp D).iota (Y.tup A3.A.μ0) (Y.jA A3.A.μ0 (Pi.single i 1))) =
        R.Th A3.A.μ0 (uA (Y.jA A3.A.μ0 (Pi.single i 1)))
      rw [← GlobalTheory.Mem.R3.DTheta.iota_sharp, hA]
      have h1 := hdt (Pi.single i 1)
      rw [hE] at h1
      exact hP.char.base.models.HE.1 (PiTensorProduct.lift.injective h1)
    exact fun a => LinearMap.congr_fun key a
  have hy : LinearMap.adjoint (R.Th A3.A.μ0) (uE (D.what₂.onb σ)) ∈
      ((RowSide.sharp D).V0 (Y.tup A3.A.μ0)).map uA := by
    refine (Submodule.span_le.2 ?_) hup
    rintro _ ⟨x, rfl⟩
    exact ⟨Y.jA A3.A.μ0 ((rE D A3.A F.P1 F.ψ1 A3.A.μ0).mulVec x), ⟨Y.jA A3.A.μ0 x, hFT.op_eq x⟩, hA _⟩
  exact transport_eig (RowSide.sharp D) (R.Th A3.A.μ0) Y.tup0 uA uE hpos nA nE hι (D.what₂.onb σ) hy ha

end GlobalTheory.KapRec.Eigen
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open scoped ComplexOrder
open Formalism.L2.Indef Formalism.IndefR.Cx

noncomputable section

namespace GlobalTheory.Mem.R3.IotaRd

open Formalism.IndefR.Cx.CxData

theorem theta_eq_proj {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
    {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (cv : CrdV A) (b : Bool)
    (eV : ∀ t, (Fin ((lv (fc X.zs) b).nV t) → K) →ₗ[K] A.FR t) (hJ : X.JIsoR cv)
    (hRL : X.RatLev cr cv b) (hDn : X.DnLev cv b) (hUp : X.UpLev cv b) (hC : X.CoordinatesInGoodPart cr cv b)
    (hV : ∀ t F, eV t F ∈ cv.v0R X.zs b t)
    (hO : ∀ t F (x : Fin ((lv (fc X.zs) b).dQ t) → K),
      cv.hR t (cr.toR X.zs b t x) (eV t F) = cv.hR t (cr.toR X.zs b t x) (cr.toR X.zs b t (((lv (fc X.zs) b).Pq t).mulVec F)))
    (t : Bs.Tup) (F : Fin ((lv (fc X.zs) b).nV t) → K) :
    X.Θ t (X.jR t (eV t F)) = X.Θ t (X.jR t (cr.toR X.zs b t (((lv (fc X.zs) b).Pq t).mulVec F))) := by
  set q : A.FR t := cr.toR X.zs b t (((lv (fc X.zs) b).Pq t).mulVec F) with hq
  have hdV : eV t F - q ∈ cv.v0R X.zs b t := sub_mem (hV t F) (hC t _)
  have hdo : ∀ x, cv.hR t (cr.toR X.zs b t x) (eV t F - q) = 0 := by
    intro x; rw [map_sub, hO t F x, sub_self]
  have hjV : X.jR t (eV t F - q) ∈ X.V0C cv b t := Submodule.subset_span ⟨_, hdV, rfl⟩
  have hΘE : X.Θ t (X.jR t (eV t F - q)) ∈ X.EEl b := hDn t ⟨_, hjV, rfl⟩
  have horth : ∀ e ∈ X.EEl b, ⟪e, X.Θ t (X.jR t (eV t F - q))⟫_ℂ = 0 := by
    intro e he
    rw [← LinearMap.adjoint_inner_left]
    have h1 : LinearMap.adjoint (X.Θ t) e ∈
        Submodule.span ℂ (Set.range fun x : Fin ((lv (fc X.zs) b).dQ t) → K => X.jR t (cr.toR X.zs b t x)) := by
      rw [hRL t]
      exact Submodule.mem_inf.2 ⟨LinearMap.mem_range_self _ e, hUp t (Submodule.mem_map_of_mem he)⟩
    have h2 : Submodule.span ℂ (Set.range fun x : Fin ((lv (fc X.zs) b).dQ t) → K => X.jR t (cr.toR X.zs b t x)) ≤
        (Submodule.span ℂ {X.jR t (eV t F - q)})ᗮ := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right, inner_eq_zero_symm, hJ, hdo x, map_zero]
    have h3 := Submodule.mem_orthogonal_singleton_iff_inner_right.1 (h2 h1)
    rwa [inner_eq_zero_symm] at h3
  have h0 : X.Θ t (X.jR t (eV t F - q)) = 0 := inner_self_eq_zero.1 (horth _ hΘE)
  rw [map_sub, map_sub, sub_eq_zero] at h0
  exact h0

end GlobalTheory.Mem.R3.IotaRd

namespace GlobalTheory.Mem.R3.IotaRd

open Formalism.IndefR.Cx.CxData Formalism.IndefR.Links.EvTie

theorem sharp_downTo' (D : D7) (μ) (j : ℕ) : (RowSide.sharp D).downTo μ j = D.what₂.downTo μ j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show ((RowSide.sharp D).downTo μ j).comp (D.what₂.io μ j) = (D.what₂.downTo μ j).comp (D.what₂.io μ j)
    rw [ih]; rfl

theorem sharp_iota' (D : D7) (μ) : (RowSide.sharp D).iota μ = D.what₂.iota μ := by
  unfold RowSide.iota Rows.Data.iota
  rw [sharp_downTo']; rfl

theorem rowSideDef3_both : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → RowSideDef3 D A3.A (RowSide.sharp D) F.P1 F.ψ1 (A3.fam3.toSub2 (zsOf R F)) (A3.indefDown (s1Of R F)) Y.tup Z.eRR Y.jA ∧ RowSideDef3 D A3.A X0.s F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) (A3.indefDown (s0Of R F)) Y.tup Z.eRR0 Y.jA0 := by
  intro hCusp D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH
  obtain ⟨h1, h0⟩ := GlobalTheory.T.compositeIntertwiner_eq_thetaLift_goodProjector hCusp D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH
  have hC := complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim
  have hOk := hH.ok
  have hout : ∀ t y, Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) ((R.toCx3 F).Θ t ((R.toCx3 F).jR t y)) = R.Th t (R.jX t y) :=
    fun t y => rfl
  have hb : ∀ t (P : Subgroup G) (ψ : P →* D.what₂.LLˣ), BlockHyp (A3.A.fam.R t) (A3.A.fam.lvl P ψ) A3.A.fam.v0 1 :=
    fun t P ψ => ⟨hOk.ok2.conj, hOk.ok2.irr, hOk.ok2.what₂ t⟩
  have hrow : ∀ t (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) x, rowForm A3.A P ψ t ((rV0 D A3.A P ψ t) *ᵥ x) =
      (A3.A.fam.R t).S.basis.equivFun.symm ((A3.A.fam.R t).vE (A3.A.fam.lvl P ψ) *ᵥ x) := by
    intro t P ψ x
    unfold rowForm rV0
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, BlockDat.lf_lvl_vE (hb t P ψ)]
  have k1 : ∀ t x, R.Th t (R.jX t (rowForm A3.A F.P1 F.ψ1 t (rV0 D A3.A F.P1 F.ψ1 t *ᵥ x))) =
      Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) ((R.toCx3 F).iC F.cr true A3.A.μ0 (cpt A3.A.v0.embedding
        ((A3.indefDown (s1Of R F)).ι t *ᵥ ((A3.A.side F.P1 F.ψ1 (A3.fam3.toSub2 (zsOf R F))).Pq t *ᵥ x)))) := by
    intro t x
    have e := theta_eq_proj (R.toCx3 F) F.cr F.cv true (F.eV (R.toCx3 F).zs) hC.jIsoR (hC.levs true).1 (hC.levs true).2.1
      (hC.levs true).2.2 (definite_coordinates_in_good_part _ true) (evTie_of_ok hOk F _).1 (evTie_of_ok hOk F _).2 t x
    have k := ((R.toCx3 F).key_row F.cr true (hC.what₂ true).1 (hC.ratMu true) t
      (((A3.A.side F.P1 F.ψ1 (A3.fam3.toSub2 (zsOf R F))).Pq t *ᵥ x))).trans ((R.toCx3 F).iC_cpt' F.cr true t _)
    exact (congrArg (fun y => R.Th t (R.jX t y)) (hrow t F.P1 F.ψ1 x)).trans
      ((hout t _).symm.trans (congrArg (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H)) (e.trans k.symm)))
  have k0 : ∀ t x, R.Th t (R.jX t (rowForm A3.A F.P0 F.ψ0 t (rV0 D A3.A F.P0 F.ψ0 t *ᵥ x))) =
      Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) ((R.toCx3 F).iC F.cr false A3.A.μ0 (cpt A3.A.v0.embedding
        ((A3.indefDown (s0Of R F)).ι t *ᵥ ((A3.A.side F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F))).Pq t *ᵥ x)))) := by
    intro t x
    let eV0 : ∀ t, (Fin ((lv (F.fc (R.toCx3 F).zs) false).nV t) → D.what₂.LL) →ₗ[D.what₂.LL] A3.fam3.amb3.FR t := fun t =>
      ((A3.A.fam.R t).S.basis.equivFun.symm : (Fin (A3.A.fam.R t).S.dim → D.what₂.LL) →ₗ[D.what₂.LL] (A3.A.fam.R t).S.Forms) ∘ₗ
        ((A3.A.fam.R t).vE (A3.A.fam.lvl F.P0 F.ψ0)).mulVecLin
    have e := theta_eq_proj (R.toCx3 F) F.cr F.cv false eV0 hC.jIsoR (hC.levs false).1 (hC.levs false).2.1
      (hC.levs false).2.2 (definite_coordinates_in_good_part _ false) (fun t y => ⟨y, rfl⟩)
      (fun t y x => evTie_block (A3.A.fam.R t) (A3.A.fam.lvl F.P0 F.ψ0) ((R.toCx3 F).zs.Z t)
        (BlockDat.HZ_det hOk.ok2.conj (hOk.ok2.what₂ t) (fun χ hχ => hOk.ok2.irr χ hχ)) x y) t x
    have k := ((R.toCx3 F).key_row F.cr false (hC.what₂ false).1 (hC.ratMu false) t
      (((A3.A.side F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F))).Pq t *ᵥ x))).trans ((R.toCx3 F).iC_cpt' F.cr false t _)
    exact (congrArg (fun y => R.Th t (R.jX t y)) (hrow t F.P0 F.ψ0 x)).trans
      ((hout t _).symm.trans (congrArg (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H)) (e.trans k.symm)))
  refine ⟨⟨Y.formsA, Y.latA, ?_⟩, ⟨Y.formsAtBottomLevel, Y.latA0, ?_⟩⟩
  · intro t x
    apply Y.Ish.jE.injective
    apply Subtype.val_injective
    have e1 := h1 t ((rV0 D A3.A F.P1 F.ψ1 t).mulVec x)
    have e2 := Z.jEE (((A3.indefDown (s1Of R F)).ι t).mulVec (((A3.A.side F.P1 F.ψ1 (A3.fam3.toSub2 (zsOf R F))).Pq t).mulVec x))
    rw [k1] at e1
    rw [sharp_iota']
    exact e1.trans e2.symm
  · intro t x
    apply Y.Iz.jE.injective
    apply Subtype.val_injective
    have e1 := h0 t ((rV0 D A3.A F.P0 F.ψ0 t).mulVec x)
    have e2 := Z.jEE0 (((A3.indefDown (s0Of R F)).ι t).mulVec (((A3.A.side F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F))).Pq t).mulVec x))
    rw [k0] at e1
    exact e1.trans e2.symm

end GlobalTheory.Mem.R3.IotaRd
end
end

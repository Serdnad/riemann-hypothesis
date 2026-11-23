module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2180
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle341
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle608
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle429
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealSymplecticFormAlternatingInvariantDefinite
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle600
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle609
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestKTypeFockMapHarmonicOfDiscreteSeries
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle023
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle610
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle602
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.PiTensorProduct
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle170
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle287
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw




noncomputable section

namespace GlobalTheory.CutStdLat

open GlobalTheory.FunObj Matrix

theorem latO_iff_of_St {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T} (j : ℕ) (βS : GL (Fin (G.V (.top j)).rank) (Lev.EAf D))
    (βT : GL (Fin (G.V (.top (j + 1))).rank) (Lev.EAf D)) (hβS : IsFrame βS (colLat (S.N.fr (.top j))))
    (hβT : IsFrame βT (colLat (S.N.fr (.top (j + 1))))) (g : GA D (G.V (.top (j + 1))))
    (hT : Lev.finE (G.V (.top (j + 1))) g ∈ St βT) (x : WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T))) :
    x ∈ stdLatO S (.top t j) ↔ actO _ _ 1 g x ∈ stdLatO S (.top t j) := by
  unfold stdLatO
  exact GlobalTheory.VecInv.mem_latO_iff (S := G.V (.top j)) (T := G.V (.top (j + 1))) hβS hβT (g := 1) (h := g)
    (by rw [map_one]; exact one_mem _) hT x

theorem keep_stdLatO : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T},
    t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ e : AE D, IsIdemSum e (locPl G t) →
    ∀ g : GA D (G.V (.top (j + 1))),
      Formalism.L2.Theta.mt _ g = (1 - (e + cA D e)) • Formalism.L2.Theta.mt _ ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) :
        FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))) + (e + cA D e) • (1 : Matrix (Fin (G.V (.top (j + 1))).rank)
        (Fin (G.V (.top (j + 1))).rank) (AE D)) →
      ∀ x : WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)),
        x ∈ stdLatO S (.top t j) ↔ actO _ _ 1 g x ∈ stdLatO S (.top t j) := by
  intro D T L sc G W U S t ht Φ β j hj k hk e he g hg x
  classical
  have hfull {n : ℕ} (B : GL (Fin n) D.host.E) : (colLat B).IsFullLattice D.host.E := by
    letI := GlobalTheory.FunObj.VecEx.isLattice_colLat B
    refine ⟨?_⟩
    rw [colLat, Submodule.span_span_of_tower]
    change Submodule.span D.host.E (Set.range (B : Matrix (Fin n) (Fin n) D.host.E).col) = ⊤
    rw [← Matrix.range_mulVecLin]
    exact LinearMap.range_eq_top.mpr (Matrix.mulVec_surjective_iff_isUnit.mpr B.isUnit)
  obtain ⟨βS, hβS⟩ := frame_exists_alt D.host.F D.host.E _ (colLat (S.N.fr (.top j))) (hfull _)
  obtain ⟨βT, hβT⟩ := frame_exists_alt D.host.F D.host.E _ (colLat (S.N.fr (.top (j + 1)))) (hfull _)
  set a : AE D := e + cA D e with ha
  set b : Lev.EAf D := toEAf D (1 - a) with hbdef
  have hcb : ∀ w, GlobalTheory.StdFrames.cpt (D := D) w b = 1 - GlobalTheory.StdFrames.cpt (D := D) w (toEAf D a) := fun w => by
    rw [hbdef, RingHom.map_sub, RingHom.map_one, RingHom.map_sub, RingHom.map_one]
  have hca := GlobalTheory.T.idempotentSum_add_conj_component_indicator he
  have hb : b * b = b := GlobalTheory.StdFrames.cpt_ext fun w => by
    rw [RingHom.map_mul, hcb]
    by_cases h1 : w ∈ locPl G t ∨ GlobalTheory.IdemSupport.cP w ∈ locPl G t
    · rw [(hca w).1 h1]; ring
    · push_neg at h1; rw [(hca w).2 h1.1 h1.2]; ring
  have hfh : Lev.finE (G.V (.top (j + 1))) (((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) :
      GA D (G.V (.top (j + 1)))) = (finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))))⁻¹ * finG (G.V (.top (j + 1))) k * finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))) := by
    have e0 : Lev.finE (G.V (.top (j + 1))) (((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) :
        GA D (G.V (.top (j + 1)))) = finG (G.V (.top (j + 1))) ((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1))) := rfl
    rw [e0, map_mul, map_mul, map_inv]
  have hfg : Lev.finE (G.V (.top (j + 1))) g = GlobalTheory.UnitaryIdemCut.cutGL b hb
      ((finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))))⁻¹ * finG (G.V (.top (j + 1))) k * finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1)))) := by
    apply Units.ext
    rw [GlobalTheory.UnitaryIdemCut.cutGL_val, ← hfh, GlobalTheory.VecInv.finE_val, GlobalTheory.VecInv.finE_val, hg]
    ext i l
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, RingHom.map_add (f := _), RingHom.map_mul, hbdef,
      RingHom.map_sub, RingHom.map_one, Matrix.one_apply]
    split_ifs <;> simp only [RingHom.map_one, RingHom.map_zero] <;> ring
  obtain ⟨Pu, eu, heu, hsu, hoff⟩ := S.N.u_supp (.top (j + 1)) (show j + 1 ≤ D.R.m by omega)
  have hnot : ∀ Q ∈ Pu, ∀ w : Pl D.host.E, w.under (𝓞 D.host.F) = Q.under (𝓞 D.host.F) → w ∉ locPl G t := by
    intro Q hQ w hw hwl
    obtain ⟨h1, h2, -⟩ := S.N.off Q (hoff Q hQ)
    unfold locPl at hwl
    rcases Finset.mem_union.1 hwl with h3 | h3
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h3
      have h4 := G.pl.w_over v hv
      exact h1 ((hw.symm.trans h4) ▸ hv)
    · exact h2 t ht w h3 hw.symm
  have hub : b * toEAf D (eu + cA D eu) = toEAf D (eu + cA D eu) := GlobalTheory.StdFrames.cpt_ext fun w => by
    rw [RingHom.map_mul, hcb]
    have hu := GlobalTheory.T.idempotentSum_add_conj_component_indicator heu w
    by_cases h1 : w ∈ Pu ∨ GlobalTheory.IdemSupport.cP w ∈ Pu
    · rw [hu.1 h1]
      have hw1 : w ∉ locPl G t := by
        rcases h1 with h1 | h1
        · exact hnot w h1 w rfl
        · exact hnot _ h1 w (GlobalTheory.IdemSupport.under_cP w).symm
      have hw2 : GlobalTheory.IdemSupport.cP w ∉ locPl G t := by
        rcases h1 with h1 | h1
        · exact hnot w h1 _ (GlobalTheory.IdemSupport.under_cP w)
        · exact hnot _ h1 _ rfl
      rw [(hca w).2 hw1 hw2]; ring
    · push_neg at h1; rw [hu.2 h1.1 h1.2, mul_zero]
  have hU : GlobalTheory.UnitaryIdemCut.cutGL b hb (finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1)))) = finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))) := by
    apply Units.ext
    rw [GlobalTheory.UnitaryIdemCut.cutGL_val]
    show b • (Lev.finE (G.V (.top (j + 1))) (S.N.u (.top (j + 1))).1).val + (1 - b) • 1 = (Lev.finE (G.V (.top (j + 1))) (S.N.u (.top (j + 1))).1).val
    rw [GlobalTheory.VecInv.finE_val]
    ext i l
    have h0 := hsu i l
    have h3 : b * toEAf D ((Formalism.L2.Theta.mt _ (S.N.u (.top (j + 1))).1 - 1) i l) =
        toEAf D ((Formalism.L2.Theta.mt _ (S.N.u (.top (j + 1))).1 - 1) i l) := by
      rw [← h0, RingHom.map_mul, ← mul_assoc, hub]
    have h4 : toEAf D ((1 : Matrix (Fin (G.V (.top (j + 1))).rank) (Fin (G.V (.top (j + 1))).rank) (AE D)) i l) =
        (1 : Matrix (Fin (G.V (.top (j + 1))).rank) (Fin (G.V (.top (j + 1))).rank) (Lev.EAf D)) i l := by
      rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
    rw [Matrix.sub_apply, RingHom.map_sub, h4] at h3
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    linear_combination h3
  have hK : GlobalTheory.UnitaryIdemCut.cutGL b hb (finG (G.V (.top (j + 1))) k) ∈ St (S.βp (j + 1)) :=
    GlobalTheory.T.idempotentCut_mem_latticeStabilizer_of_productLevel _ _ _ _ _ hk b hb fun w ⟨PP, hPP, hw⟩ => by
      rw [hcb]
      rcases GlobalTheory.IdemSupport.eq_or_eq_cP hw with rfl | rfl
      · rw [(hca _).1 (Or.inl hPP)]; ring
      · rw [(hca _).1 (Or.inr (by rwa [GlobalTheory.StdFrames.cP_cP]))]; ring
  have hcut : Lev.finE (G.V (.top (j + 1))) g = (finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))))⁻¹ * GlobalTheory.UnitaryIdemCut.cutGL b hb (finG (G.V (.top (j + 1))) k) *
      finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))) := by
    rw [hfg, map_mul, map_mul, map_inv, hU]
  have hp := S.βp_is (j + 1) (by omega)
  have hl := S.N.u_lat (.top (j + 1)) (show j + 1 ≤ D.R.m by omega)
  have keep : ∀ X ∈ St (S.βp (j + 1)), ∀ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.top (j + 1)))),
      ((finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))))⁻¹ * X * finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1)))).val *ᵥ y ∈
        Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.top (j + 1)))) := by
    intro X hX y hy
    have h1 : (finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1)))).val *ᵥ y ∈
        Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.top (j + 1))) := (hl y).1 hy
    have h2 := ((GlobalTheory.LevSplit.mem_St_iff _ _ hp X).1 hX).1 _ h1
    refine (hl _).2 ?_
    change (finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1)))).val *ᵥ _ ∈ _
    generalize finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))) = Uu at h2 ⊢
    have e3 : Uu.val * (Uu⁻¹ * X * Uu).val = X.val * Uu.val := by
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    rw [Matrix.mulVec_mulVec y Uu.val (Uu⁻¹ * X * Uu).val, e3, ← Matrix.mulVec_mulVec y X.val Uu.val]
    exact h2
  have st : ∀ X ∈ St (S.βp (j + 1)),
      (finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))))⁻¹ * X * finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))) ∈ St βT := by
    intro X hX
    refine (GlobalTheory.LevSplit.mem_St_iff _ _ hβT _).2 ⟨keep X hX, fun y hy => ?_⟩
    have h5 := keep _ (inv_mem hX) y hy
    generalize finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))) = Uu at h5 ⊢
    have e1 : (Uu⁻¹ * X * Uu)⁻¹ = Uu⁻¹ * X⁻¹ * Uu := by group
    rw [e1]
    exact h5
  have hT : Lev.finE (G.V (.top (j + 1))) g ∈ St βT := by
    rw [hcut]
    exact st _ hK
  exact latO_iff_of_St S j βS βT hβS hβT g hT x

end GlobalTheory.CutStdLat

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

noncomputable section

namespace GlobalTheory.FockTransl.Jet

open Complex

variable {D : D7}

theorem map_inv_ringHom {K L : Type} [Field K] [Field L] (f : K →+* L) {n : ℕ} (M : Matrix (Fin n) (Fin n) K) :
    (M⁻¹).map f = (M.map f)⁻¹ := by
  have h1 : M.adjugate.map f = (M.map f).adjugate := by
    have := RingHom.map_adjugate f M; simpa [RingHom.mapMatrix_apply] using this
  have h2 : (M.map f).det = f M.det := by
    have := RingHom.map_det f M; simpa [RingHom.mapMatrix_apply] using this.symm
  rw [Matrix.inv_def, Matrix.inv_def, Matrix.map_smul' _ _ _ (map_mul f), h1, h2, Ring.inverse_eq_inv',
    Ring.inverse_eq_inv', map_inv₀]

theorem formAt_eq_omAt (S T : HSp D) (τ : D.what₂.Tau) (x y : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    GlobalTheory.OrientedHeis.formAt S T τ x y = GlobalTheory.VacUnique.omAt S T τ x y := by
  unfold GlobalTheory.OrientedHeis.formAt GlobalTheory.VacUnique.omAt GlobalTheory.VacUnique.hAt
  congr 3
  rw [gramAt, gramAt, ← map_inv_ringHom]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul, RCLike.star_def]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]

theorem omF_eq {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (z e : VCx D.what₂.Tau S.rank T.rank) :
    omF A B z e = GlobalTheory.VacUnique.omO S T (fmR A B z) (fmR A B e) := by
  rw [GlobalTheory.VacUnique.omO_apply]
  exact Finset.sum_congr rfl fun τ _ => formAt_eq_omAt S T τ _ _

theorem cplxO_smulC' {m n : ℕ} (s : Matrix (Fin n) (Fin n) ℂ) (t : Matrix (Fin m) (Fin m) ℂ) (c : ℂ)
    (x : Matrix (Fin m) (Fin n) ℂ) : cplxO s t (c • x) = c • cplxO s t x := by
  simp only [cplxO, Matrix.mul_smul, Matrix.smul_mul]
  exact smul_comm _ _ _

theorem cplxO_sum' {m n p q : ℕ} (s : Matrix (Fin n) (Fin n) ℂ) (t : Matrix (Fin m) (Fin m) ℂ)
    (x : Fin p → Fin q → Matrix (Fin m) (Fin n) ℂ) :
    cplxO s t (∑ i, ∑ j, x i j) = ∑ i, ∑ j, cplxO s t (x i j) := by
  simp only [cplxO, Matrix.mul_sum, Matrix.sum_mul, Finset.smul_sum]

theorem fmR_I {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (z : VCx D.what₂.Tau S.rank T.rank) :
    fmR A B (I • z) = GlobalTheory.VacUnique.jO S T A.cart B.cart (fmR A B z) := by
  funext τ
  show fockMat A B τ ((I • z) τ) = cplxO (A.cart τ) (B.cart τ) (fockMat A B τ (z τ))
  have hs := (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv A τ).1
  have ht := (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv B τ).1
  unfold fockMat
  rw [cplxO_sum']
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [GlobalTheory.VacUnique.cplxO_add, cplxO_smulC', cplxO_smulC', GlobalTheory.RealSymplForm.cplxO_cplxO hs ht]
  have e1 : ((I • z) τ i j).re = -(z τ i j).im := by simp
  have e2 : ((I • z) τ i j).im = (z τ i j).re := by simp
  rw [e1, e2]
  simp only [smul_neg, Complex.ofReal_neg, neg_smul]
  abel

theorem fmR_add {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (z w : VCx D.what₂.Tau S.rank T.rank) :
    fmR A B (z + w) = fmR A B z + fmR A B w := by
  funext τ
  show fockMat A B τ (z τ + w τ) = fockMat A B τ (z τ) + fockMat A B τ (w τ)
  simp only [fockMat, Pi.add_apply, Complex.add_re, Complex.add_im, Complex.ofReal_add, add_smul,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  abel

theorem fmR_smul {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (c : ℝ) (z : VCx D.what₂.Tau S.rank T.rank) :
    fmR A B (c • z) = c • fmR A B z := by
  funext τ
  show fockMat A B τ (c • z τ) = c • fockMat A B τ (z τ)
  simp only [fockMat, Pi.smul_apply, Complex.smul_re, Complex.smul_im, smul_eq_mul, Complex.ofReal_mul,
    mul_smul, Finset.smul_sum, smul_add]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Complex.coe_smul]

theorem omF_add {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (z w e : VCx D.what₂.Tau S.rank T.rank) :
    omF A B (z + w) e = omF A B z e + omF A B w e := by
  rw [omF_eq, omF_eq, omF_eq, fmR_add, map_add (f := _), LinearMap.add_apply]

theorem omF_smul {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (c : ℝ) (z e : VCx D.what₂.Tau S.rank T.rank) :
    omF A B (c • z) e = c * omF A B z e := by
  rw [omF_eq, omF_eq, fmR_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]

theorem omF_I {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (z e : VCx D.what₂.Tau S.rank T.rank) :
    omF A B (I • z) e = -omF A B z (I • e) := by
  obtain ⟨hJJ, -, hinv, -⟩ := GlobalTheory.RealSymplForm.form_alt_inv_def D S T A.cart B.cart
    (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv A) (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv B)
  rw [omF_eq, omF_eq, fmR_I, fmR_I]
  set J := GlobalTheory.VacUnique.jO S T A.cart B.cart
  set x := fmR A B z
  set y := fmR A B e
  have hy : y = -J (J y) := by rw [hJJ, neg_neg]
  conv_lhs => rw [hy]
  rw [map_neg, hinv]

theorem omF_I_I {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (z e : VCx D.what₂.Tau S.rank T.rank) :
    omF A B (I • z) (I • e) = omF A B z e := by
  rw [omF_I, smul_smul, I_mul_I, neg_one_smul, omF_eq, omF_eq]
  have : fmR A B (-e) = -fmR A B e := by
    have h := fmR_smul A B (-1) e
    rw [neg_one_smul, neg_one_smul] at h
    exact h
  rw [this, map_neg, neg_neg]

variable {ι : Type} [Fintype ι] {a b : ℕ}

theorem gD_add (c : ι → ℝ) (z w e : VCx ι a b) : gD c (z + w) e = gD c z e + gD c w e := by
  simp only [gD, Pi.add_apply, add_mul, Complex.add_re, mul_add, Finset.sum_add_distrib]

theorem gD_smul (c : ι → ℝ) (r : ℝ) (z e : VCx ι a b) : gD c (r • z) e = r * gD c z e := by
  simp only [gD, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, Complex.real_smul, mul_assoc, Complex.re_ofReal_mul]
  ring

theorem gD_I (c : ι → ℝ) (z e : VCx ι a b) : gD c (I • z) e = -gD c z (I • e) := by
  simp only [gD, ← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_I, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im]
  ring

theorem gD_I_I (c : ι → ℝ) (z e : VCx ι a b) : gD c (I • z) (I • e) = gD c z e := by
  simp only [gD]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_I, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im]
  ring

end GlobalTheory.FockTransl.Jet

namespace GlobalTheory.FockTransl.Jet

open Complex

variable {D : D7}

theorem lamF_add {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank)
    (z w : VCx D.what₂.Tau S.rank T.rank) : lamF A B l (z + w) = lamF A B l z + lamF A B l w := by
  simp only [lamF, omF_add, gD_add]
  push_cast
  ring

theorem lamF_smul {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank)
    (r : ℝ) (z : VCx D.what₂.Tau S.rank T.rank) : lamF A B l (r • z) = r * lamF A B l z := by
  simp only [lamF, omF_smul, gD_smul]
  push_cast
  ring

theorem lamF_I {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank)
    (z : VCx D.what₂.Tau S.rank T.rank) : lamF A B l (I • z) = -I * lamF A B l z := by
  simp only [lamF]
  rw [omF_I_I, omF_I, gD_I_I, gD_I]
  push_cast
  linear_combination (-(1 / 2 : ℂ) * (Real.pi : ℂ) * (omF A B z (Formalism.L2.Ker.coordX l) : ℂ) +
    (1 / 4 : ℂ) * (gD (fw D) z (I • Formalism.L2.Ker.coordX l) : ℂ)) * Complex.I_sq

theorem lamF_antilinear : ∀ (D : D7) (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank), (∀ a b, GlobalTheory.FockTransl.Jet.lamF A B l (a + b) = GlobalTheory.FockTransl.Jet.lamF A B l a + GlobalTheory.FockTransl.Jet.lamF A B l b) ∧ ∀ (t : ℂ) a, GlobalTheory.FockTransl.Jet.lamF A B l (t • a) = conj t * GlobalTheory.FockTransl.Jet.lamF A B l a := by
  intro D S T A B l
  refine ⟨fun a b => lamF_add A B l a b, fun t a => ?_⟩
  have e : t • a = (t.re : ℝ) • a + (t.im : ℝ) • (I • a) := by
    funext τ i j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    conv_lhs => rw [← Complex.re_add_im t]
    ring
  have hc : conj t = (t.re : ℂ) - t.im * I := by apply Complex.ext <;> simp
  rw [e, lamF_add, lamF_smul, lamF_smul, lamF_I, hc]
  ring

end GlobalTheory.FockTransl.Jet

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

theorem _root_.GlobalTheory.T.realUnitaryFockColumnAction_surjective : ∀ {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (hV : HSpace.gram V = 1), Function.Surjective (GlobalTheory.RealColAct.realCol θ hθ V hV) := by
  first | exact @GlobalTheory.RealColAct.realCol_surjective | exact GlobalTheory.RealColAct.realCol_surjective | (intros; apply GlobalTheory.RealColAct.realCol_surjective <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

theorem _root_.GlobalTheory.T.lieAlgebrasAtPlace_act_fockVectors_by_fockOperators : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (τ : D.what₂.Tau), IsInfFam θ → IsWeilDatumO ψ S T χS χT ω → ∀ aS aT : ℚ, HasInfExp D χS τ aS → HasInfExp D χT τ aT → ∀ (sS frS : Mn S.rank) (εS : Fin S.rank → Bool) (sT frT : Mn T.rank) (εT : Fin T.rank → Bool), IsFrameOf (gramAt D S τ) sS εS frS → IsFrameOf (gramAt D T τ) sT εT frT → ∀ f, IsThetaFunO ψ S T f → IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) f → LieAt ψ θ τ ω εS frS εT frT aS aT (ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ f) := by
  first | exact @GlobalTheory.ArchRec.LieAtPlace.lieAt_of_vacAt | exact GlobalTheory.ArchRec.LieAtPlace.lieAt_of_vacAt | (intros; apply GlobalTheory.ArchRec.LieAtPlace.lieAt_of_vacAt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

theorem _root_.GlobalTheory.T.lowestKTypeFockMap_harmonic_of_discreteSeries : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ D : D7, IoHarm D := by
  first | exact @GlobalTheory.ArchRec.IoHarmPf.ioHarm | exact GlobalTheory.ArchRec.IoHarmPf.ioHarm | (intros; apply GlobalTheory.ArchRec.IoHarmPf.ioHarm <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_lastStep_intertwiner_chain : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.IsChainW → R.ex_ItX := by
  first | exact @GlobalTheory.Twist.LastStepExists.exists_lastStep_intertwiner | exact GlobalTheory.Twist.LastStepExists.exists_lastStep_intertwiner | (intros; apply GlobalTheory.Twist.LastStepExists.exists_lastStep_intertwiner <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.weilAction_liftPair_stepVector_invLevelChar : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.models_inf → R.thP_ωP → R.thP_vP → ∀ i t (g0 : G0 R.Pg D.R.r) κ κ', IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ → IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ' → R.ωP i t (κ, κ') (R.vP i t) = (levChi _ (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • R.vP i t := by
  first | exact @GlobalTheory.VecInv.omega_lifts_vP | exact GlobalTheory.VecInv.omega_lifts_vP | (intros; apply GlobalTheory.VecInv.omega_lifts_vP <;> assumption)
end

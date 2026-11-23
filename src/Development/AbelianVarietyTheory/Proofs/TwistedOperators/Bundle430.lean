module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle386
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenPtSubset
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrientedHermitianFormQuadSumEqTrace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle319
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1946
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle315
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOrthogonalSumLatticeSameLatticedSpace
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle396
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle008
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle017
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
public import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle394
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle013
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumB skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (At)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.SmallDat

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ}


variable (G i j) in
abbrev PtS : Type := Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)


variable (G i j) in
abbrev IxS : Type := Fin (spW₁ G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank)


variable (G) in
abbrev HomA (t : T) (i j : ℕ) : Type := WO (G.pS (.mu t i j)) (G.pT (.mu t i j))


variable (G i j) in
abbrev HomB : Type := WO (G.pS (.chi i j)) (G.pT (.chi i j))

abbrev mapA (t : T) (e : Num G i j) (u : PtS G i j) : HomA G t i j := mulG (spW₁ G i j) (colV e u)ᵀ

abbrev mapB (e : Num G i j) (u : PtS G i j) : HomB G i j := adjV₁ e u

def ofMaps (t : T) (e : Num G i j) (x : HomA G t i j × HomB G i j) : PtS G i j :=
  (fromCols (GlobalTheory.BigDat.divG (spW₁ G i j) x.1)ᵀ ((GlobalTheory.BigDat.divG (spV₁ G i j) (-x.2)).map (cA D))).submatrix id e.symm

theorem mapA_ofMaps (t : T) (e : Num G i j) (x : HomA G t i j × HomB G i j) : mapA t e (ofMaps t e x) = x.1 := by
  have h1 : (colV e (ofMaps t e x))ᵀ = GlobalTheory.BigDat.divG (spW₁ G i j) x.1 := Matrix.ext fun a b => by
    simp only [colV, ofMaps, transpose_apply, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inl]
  exact (congrArg (mulG (spW₁ G i j)) h1).trans (GlobalTheory.BigDat.mulG_divG _ _)

theorem mapB_ofMaps (t : T) (e : Num G i j) (x : HomA G t i j × HomB G i j) : mapB e (ofMaps t e x) = x.2 := by
  have h2 : ((ofMaps t e x).submatrix id fun k => e (.inr k)).map (cA D) = GlobalTheory.BigDat.divG (spV₁ G i j) (-x.2) :=
    Matrix.ext fun a b => by
      simp only [ofMaps, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inr, map_apply,
        GlobalTheory.DualPairCheck.cA_cA]
  exact (congrArg (fun y => -mulG (spV₁ G i j) y) h2).trans ((congrArg Neg.neg (GlobalTheory.BigDat.mulG_divG _ _)).trans (neg_neg _))

theorem ofMaps_maps (t : T) (e : Num G i j) (u : PtS G i j) : ofMaps t e (mapA t e u, mapB e u) = u := by
  have h1 : GlobalTheory.BigDat.divG (spW₁ G i j) (mapA t e u) = (colV e u)ᵀ := GlobalTheory.BigDat.divG_mulG _ _
  have h2 : GlobalTheory.BigDat.divG (spV₁ G i j) (-mapB e u) = (u.submatrix id fun k => e (.inr k)).map (cA D) :=
    (congrArg (GlobalTheory.BigDat.divG (spV₁ G i j)) (neg_neg _)).trans (GlobalTheory.BigDat.divG_mulG _ _)
  ext a b
  obtain ⟨k | k, rfl⟩ := e.surjective b
  · simp only [ofMaps, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inl, transpose_apply]
    exact congrFun (congrFun h1 k) a
  · simp only [ofMaps, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inr, map_apply]
    exact (congrArg (cA D) (congrFun (congrFun h2 a) k)).trans (GlobalTheory.DualPairCheck.cA_cA _)

theorem mapA_add (t : T) (e : Num G i j) (u u' : PtS G i j) : mapA t e (u + u') = mapA t e u + mapA t e u' :=
  GlobalTheory.RouteCoords.mulG_colV_add e u u'

theorem mapB_add (e : Num G i j) (u u' : PtS G i j) : mapB e (u + u') = mapB e u + mapB e u' :=
  GlobalTheory.RouteCoords.adjV₁_add e u u'

theorem mapA_smul (t : T) (e : Num G i j) (c : AF D.host.F) (u : PtS G i j) : mapA t e (c • u) = c • mapA t e u :=
  GlobalTheory.BigDat.mulG_smul (spW₁ G i j) c (colV e u)ᵀ

theorem mapB_smul (e : Num G i j) (c : AF D.host.F) (u : PtS G i j) : mapB e (c • u) = c • mapB e u := by
  have h : ((c • u).submatrix id fun k => e (.inr k)).map (cA D) = c • (u.submatrix id fun k => e (.inr k)).map (cA D) :=
    Matrix.ext fun a b => map_smul (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) c _
  exact (congrArg (fun y => -mulG (spV₁ G i j) y) h).trans
    ((congrArg Neg.neg (GlobalTheory.BigDat.mulG_smul _ _ _)).trans (smul_neg _ _).symm)

def maps (t : T) (e : Num G i j) : PtS G i j ≃ₗ[AF D.host.F] HomA G t i j × HomB G i j where
  toFun u := (mapA t e u, mapB e u)
  invFun := ofMaps t e
  map_add' u u' := Prod.ext (mapA_add t e u u') (mapB_add e u u')
  map_smul' c u := Prod.ext (mapA_smul t e c u) (mapB_smul e c u)
  left_inv := ofMaps_maps t e
  right_inv x := Prod.ext (mapA_ofMaps t e x) (mapB_ofMaps t e x)

theorem maps_apply (t : T) (e : Num G i j) (u : PtS G i j) : maps t e u = (mapA t e u, mapB e u) := rfl

abbrev sympS (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (u u' : PtS G i j) : AF D.host.F :=
  symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J)
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) u u'

theorem sympS_eq (t : T) (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (hW₁ : Γ.V'.J = (-1 : D.host.E) • (spW₁ G i j).gram) (hWW : Γ.W.J = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram (spV G i j) (spV₁ G i j) e)
    (x x' : PtS G i j) :
    sympS Γ x x' = symplO _ _ (mapA t e x) (mapA t e x') + symplO _ _ (mapB e x) (mapB e x') :=
  GlobalTheory.RouteCoords.symp_eq t e Γ hW₁ hWW x x'

def boxS (t : T) (e : Num G i j) (f₁ : HomA G t i j → ℂ) (f₂ : HomB G i j → ℂ) (u : PtS G i j) : ℂ :=
  f₁ (mapA t e u) * f₂ (mapB e u)

def heisS (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (ψ : AddChar (AF D.host.F) ℂ) (u₀ : PtS G i j) (f : PtS G i j → ℂ)
    (u : PtS G i j) : ℂ :=
  ψ (⅟(2 : AF D.host.F) * sympS Γ u u₀) * f (u + u₀)

theorem heisS_box (t : T) (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (hW₁ : Γ.V'.J = (-1 : D.host.E) • (spW₁ G i j).gram) (hWW : Γ.W.J = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram (spV G i j) (spV₁ G i j) e)
    (ψ : AddChar (AF D.host.F) ℂ) (u₀ : PtS G i j) (f₁ : HomA G t i j → ℂ) (f₂ : HomB G i j → ℂ) :
    heisS Γ ψ u₀ (boxS t e f₁ f₂) = boxS t e (heisO ψ _ _ (mapA t e u₀) f₁) (heisO ψ _ _ (mapB e u₀) f₂) := by
  funext u
  unfold heisS boxS heisO symplOH
  rw [sympS_eq t e Γ hW₁ hWW, mul_add, AddChar.map_add_eq_mul, mapA_add, mapB_add, GlobalTheory.BigDat.invOf_two]
  ring

abbrev thetaS (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (ψ : AddChar (AF D.host.F) ℂ) (Φ : (IxS G i j → AF D.host.F) → ℂ)
    (u : PtS G i j) : ℂ := thetaSum D.host.F (Γ.M'.co.rho ψ u Φ)

theorem thetaS_rho (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (ψ : AddChar (AF D.host.F) ℂ) (Φ : (IxS G i j → AF D.host.F) → ℂ)
    (u₀ : PtS G i j) : thetaS Γ ψ (Γ.M'.co.rho ψ u₀ Φ) = heisS Γ ψ u₀ (thetaS Γ ψ Φ) :=
  funext fun u => (congrArg (thetaSum D.host.F) (GlobalTheory.BigDat.rho_rho Γ.M'.co ψ u u₀ Φ)).trans tsum_mul_left

theorem thetaS_smul (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (ψ : AddChar (AF D.host.F) ℂ) (c : ℂ)
    (Φ : (IxS G i j → AF D.host.F) → ℂ) (u : PtS G i j) : thetaS Γ ψ (c • Φ) u = c * thetaS Γ ψ Φ u :=
  (tsum_congr fun _ => mul_left_comm _ _ _).trans tsum_mul_left


variable (G) in
abbrev latA (t : T) (i j : ℕ) : AddSubgroup (HomA G t i j) :=
  latO (G.pS (.mu t i j)) (G.pT (.mu t i j)) (G.latS (.mu t i j) : Set _) (G.latT (.mu t i j) : Set _) fun _ => True


variable (G i j) in
abbrev latB : AddSubgroup (HomB G i j) :=
  latO (G.pS (.chi i j)) (G.pT (.chi i j)) (G.latS (.chi i j) : Set _) (G.latT (.chi i j) : Set _) fun _ => True

def latPtS (t : T) (e : Num G i j) (v : Pl D.host.F) : AddSubgroup (PtS G i j) where
  carrier := {u | At (evFin D.host.F v) u ∧ mapA t e u ∈ latA G t i j ∧ mapB e u ∈ latB G i j}
  zero_mem' := ⟨fun u _ => smul_zero u, by
    rw [show mapA t e 0 = 0 from congrArg Prod.fst (map_zero (maps t e))]; exact zero_mem _, by
    rw [show mapB e 0 = 0 from congrArg Prod.snd (map_zero (maps t e))]; exact zero_mem _⟩
  add_mem' := fun {a b} ha hb => ⟨fun u hu => by rw [smul_add, ha.1 u hu, hb.1 u hu, add_zero],
    by rw [mapA_add]; exact add_mem ha.2.1 hb.2.1, by rw [mapB_add]; exact add_mem ha.2.2 hb.2.2⟩
  neg_mem' := fun {a} ha => ⟨fun u hu => by rw [smul_neg, ha.1 u hu, neg_zero], by
    rw [show mapA t e (-a) = -mapA t e a from congrArg Prod.fst (map_neg (maps t e) a)]; exact neg_mem ha.2.1, by
    rw [show mapB e (-a) = -mapB e a from congrArg Prod.snd (map_neg (maps t e) a)]; exact neg_mem ha.2.2⟩

def genPtS (t : T) (e : Num G i j) (v : Pl D.host.F) : Set (PtS G i j) :=
  {γ | (∃ γ' ∈ latPtS t e v, γ = 2 • γ') ∨ γ ∈ latPtS t e v ∧ ∃ ε, IsSplitIdem D ε ∧ γ ∈ GlobalTheory.FlipMatch.mixHalfS e ε}

theorem genPtS_subset (t : T) (e : Num G i j) (v : Pl D.host.F) : genPtS t e v ⊆ latPtS t e v := by
  rintro _ (⟨γ, h, rfl⟩ | h)
  exacts [nsmul_mem h 2, h.1]

end GlobalTheory.SmallDat

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

noncomputable section

namespace GlobalTheory.FlipMatch

open GlobalTheory.LFun GlobalTheory.LFun.SplitTie

section Place

variable {D : D7} {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)

theorem complMap_apply_under {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : Pl F} {w : Pl E} (h : w.under (𝓞 F) = v) (b : Af F) :
    complMap h (b v) = GlobalTheory.AdeleBaseChange.locMap F w (b (w.under (𝓞 F))) := by
  subst h; rfl

theorem piW_tmul (b : AF D.host.F) (x : D.host.E) : piW τ (b ⊗ₜ[D.host.F] x) = evFin D.host.F v b * τ x := by
  show splitProj τ (compFin D.host.F D.host.E v (b ⊗ₜ[D.host.F] x)) = _
  rw [compFin, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul]
  rfl

theorem cpt_tmul (w : Pl D.host.E) (b : AF D.host.F) (x : D.host.E) :
    cpt (D := D) w (toEAf D (b ⊗ₜ[D.host.F] x)) =
      algebraMap D.host.E _ x * GlobalTheory.AdeleBaseChange.locMap D.host.F w (b.2 (w.under (𝓞 D.host.F))) := by
  have e : toEAf D (b ⊗ₜ[D.host.F] x) = x ⊗ₜ[D.host.F] b.2 := rfl
  rw [e]
  show (toAd D (x ⊗ₜ[D.host.F] b.2)) w = _
  rw [toAd_spec]
  rfl

theorem isPlaceIso_complEquiv : IsPlaceIso τ (splitPrime τ) (complEquiv τ (splitPrime_under τ)) := by
  intro a
  induction a using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul b x =>
    rw [piW_tmul, cpt_tmul, complEquiv_apply, map_mul, complMap_apply_emb, mul_comm]
    congr 1
    exact complMap_apply_under (splitPrime_under τ) b.2
  | add x y hx hy =>
    rw [RingHom.map_add (piW τ), RingEquiv.map_add (e := _), RingHom.map_add (toEAf D), RingHom.map_add (cpt _), hx, hy]

theorem isEquiv_Fv {F : Type} [Field F] [NumberField F] (v : Pl F) :
    (ValuativeRel.valuation (Fv F v)).IsEquiv (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))) :=
  haveI : (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  ValuativeRel.isEquiv _ _

theorem valued_complEquiv_symm (y : Kw (D := D) (splitPrime τ)) :
    Valued.v ((complEquiv τ (splitPrime_under τ)).symm y) = Valued.v y := by
  conv_rhs => rw [← (complEquiv τ (splitPrime_under τ)).apply_symm_apply y]
  rw [complEquiv_apply, SplitTie.valued_complMap]

theorem continuous_complEquiv_symm : Continuous (complEquiv τ (splitPrime_under τ)).symm := by
  refine continuous_of_continuousAt_zero (complEquiv τ (splitPrime_under τ)).symm ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_right_iff]
  intro γ _
  have h0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
  obtain ⟨k, hk⟩ : ∃ k : ℤ, MonoidWithZeroHom.ValueGroup₀.embedding γ.1 = WithZero.exp k :=
    ⟨_, (WithZero.exp_log h0).symm⟩
  filter_upwards [(GlobalTheory.Idele.isOpen_valued_le (K := D.host.E) (splitPrime τ) (-((k.natAbs + 1 : ℕ) : ℤ))).mem_nhds
    (by simp)] with a ha
  rw [Valuation.restrict_lt_iff_lt_embedding, hk, valued_complEquiv_symm]
  exact ha.trans_lt (WithZero.exp_lt_exp.2 (by omega))

theorem isLocIso_complEquiv : IsLocIso (complEquiv τ (splitPrime_under τ)) := by
  refine ⟨SplitChart.continuous_complMap _, continuous_complEquiv_symm τ, fun x => ?_⟩
  rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff, (Good.isEquiv_Kw (D := D) _).le_one_iff_le_one,
    (isEquiv_Fv v).le_one_iff_le_one, complEquiv_apply, SplitTie.valued_complMap]

end Place

section Chars

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem chrW_nu {μ₀ : T} (hL : L.Is μ₀) (t : T) (i j : Fin D.R.m) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (hα : X.α = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) (hβ : X.β = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j)
    {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (x : (Fv D.host.F v)ˣ) :
    chrW X.ν τ x = (locGrid G t (splitPrime τ)).nu i j
      (Units.map ((complEquiv τ (splitPrime_under τ) : Fv D.host.F v →* Kw (splitPrime τ))) x) := by
  have e1 : X.ν = G.nu t i (j + 1) := by
    show X.α / X.β = _
    rw [hα, hβ]
    exact mul_div_mul_right_eq_div _ _ _
  have e2 : chrW X.ν τ x = locChar X.ν (splitPrime τ)
      (Units.map ((complEquiv τ (splitPrime_under τ) : Fv D.host.F v →* Kw (splitPrime τ))) x) := rfl
  rw [e2, e1, locChar_eq_of_chrEq (SqNum.chrEq_nu G t i j hL)]
  have hj : (j : ℕ) < D.R.m := j.2
  simp only [SqNum.nuH, Grid.nu, locGrid, muBase, dif_pos hj, MonoidHom.div_apply, div_eq_mul_inv]
  rfl

end Chars

section Psi

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem at_atPl {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (y : Kw (D := D) (splitPrime τ)) :
    At (evFin D.host.F v) (atPl (splitPrime τ) y) := by
  classical
  intro u hu
  refine ae_ext ?_ fun Q => ?_
  · rw [Algebra.smul_def, RingHom.map_mul, (atPl_spec _ y).1, mul_zero, map_zero]
  · rw [Algebra.smul_def, RingHom.map_mul, RingHom.map_mul, (atPl_spec _ y).2, map_zero, map_zero]
    by_cases h : Q = splitPrime τ
    · subst h
      have h1 : cpt (D := D) (splitPrime τ) (toEAf D (algebraMap (AF D.host.F) (AE D) u)) =
          GlobalTheory.AdeleBaseChange.locMap D.host.F (splitPrime τ) (u.2 ((splitPrime τ).under (𝓞 D.host.F))) :=
        (comp_toAd D).base u (splitPrime τ)
      rw [h1, ← complMap_apply_under (splitPrime_under τ)]
      have h2 : u.2 v = 0 := hu
      rw [h2, map_zero, zero_mul]
    · rw [Pi.single_eq_of_ne h, mul_zero]

theorem psiLoc_eq_psiAt (W : G.Weil) {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (x : Fv D.host.F v) :
    psiLoc W.ψ v x = psiAt W (splitPrime τ) ((xiAt (splitPrime τ))⁻¹ * complEquiv τ (splitPrime_under τ) x) := by
  classical
  set w := splitPrime τ with hw
  set jj := complEquiv τ (splitPrime_under τ) with hjj
  have hξ : xiAt (D := D) w ≠ 0 := (map_ne_zero _).2 cmHost_imaginaryGenerator_ne_zero
  have hz : incA D D.host.xi0 * atPl w ((xiAt w)⁻¹ * jj x) = atPl w (jj x) := by
    rw [← Good.atPl_mul]
    congr 1
    rw [← mul_assoc]
    change xiAt w * (xiAt w)⁻¹ * jj x = jj x
    rw [mul_inv_cancel₀ hξ, one_mul]
  have hcm := isCMExt_host D
  have hp1 : piW τ (atPl w (jj x)) = x :=
    jj.injective (by rw [isPlaceIso_complEquiv τ, (atPl_spec w _).2, Pi.single_eq_same])
  have hp2 : piW (τ.comp D.sp.cm.sig) (atPl w (jj x)) = 0 :=
    (complEquiv (τ.comp D.sp.cm.sig) (splitPrime_under _)).injective (by
      rw [isPlaceIso_complEquiv (τ.comp D.sp.cm.sig), (atPl_spec w _).2, Pi.single_eq_of_ne (splitPrime_comp_ne hcm τ),
        map_zero])
  show psiLoc W.ψ v x = W.ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * atPl w ((xiAt w)⁻¹ * jj x)))
  rw [hz, GlobalTheory.T.adelicTrace_supportedAtSplitPlace hcm v τ _ (at_atPl τ _), hp1, hp2, add_zero]
  rfl

end Psi

theorem exists_placeIso_chars : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (t : T) (i j : Fin D.R.m) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E), X.α = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j → X.β = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j →
    ∀ {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (w : Pl D.host.E), splitPrime τ = w →
    ∃ jj : Fv D.host.F v ≃+* Kw w, IsPlaceIso τ w jj ∧ IsLocIso jj ∧
      (∀ x, chrW X.ν τ x = (locGrid G t w).nu i j (Units.map (jj : Fv D.host.F v →* Kw w) x)) ∧
      ∀ x, psiLoc W.ψ v x = psiAt W w ((xiAt w)⁻¹ * jj x) := by
  intro D T L sc G μ₀ hL W t i j X hα hβ v τ w hw
  subst hw
  exact ⟨complEquiv τ (splitPrime_under τ), isPlaceIso_complEquiv τ, isLocIso_complEquiv τ,
    fun x => chrW_nu hL t i j X hα hβ τ x, fun x => psiLoc_eq_psiAt W τ x⟩

end GlobalTheory.FlipMatch
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowLift

open GlobalTheory.GridJoin

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

structure RowMatchS (ch : Choice R) (G' : GlobalTheory.Grid.GridPre R) : Prop where

  V : ∀ i, i ≤ D.R.m → SameSp (ch.G.V (.grid i 0)) (G'.V i 0).V

  ν : ∀ i, i ≤ D.R.m → HEq (G'.measCol i).ν (ch.M.ν (.grid i 0))

  fd : ∀ i, i ≤ D.R.m → HEq (G'.measCol i).fd (ch.M.fd (.grid i 0))

  ker : ∀ (ρ : ch.G.RealVec) (Φ : ch.G.Datum) (i : Fin D.R.m), ∃ f,
    GlobalTheory.Grid.IsFinVec R.ψ R.θ true (G'.V ((i : ℕ) + 1) 0) (G'.V i 0) f ∧ ∃ p,
      HEq (fun h g => thetaKO (G'.X i 0).ω h g (GlobalTheory.Grid.fock R.ψ R.θ true (G'.V ((i : ℕ) + 1) 0) (G'.V i 0) f p))
        (fun h g => ch.W.kerA (.right (i : ℕ) 0) (ch.W.datum ρ Φ i) g h)

theorem transport_stepS {A A' B B' : HSp D} (eA : SameSp A' A) (eB : SameSp B' B)
    {ν : Measure (GA D A)} {fd : Set (GA D A)} {ν' : Measure (GA D A')} {fd' : Set (GA D A')}
    (hν : HEq ν ν') (hfd : HEq fd fd') {K : GA D B → GA D A → ℂ} {K' : GA D A' → GA D B' → ℂ}
    (hK : HEq K (fun h g => K' g h)) {φ : GA D A → ℂ} {φ' : GA D A' → ℂ} (hφ : HEq φ φ') {ψ : GA D B → ℂ}
    (hI : ∀ h, IntegrableOn (fun g => K h g * φ g) fd ν) (hE : ∀ h, ∫ g in fd, K h g * φ g ∂ν = ψ h) :
    (∀ h, IntegrableOn (fun g => K' g h * φ' g) fd' ν') ∧ HEq ψ (fun h => ∫ g in fd', K' g h * φ' g ∂ν') := by
  obtain ⟨L, h1, h2, rfl⟩ := eA
  obtain ⟨L', h1', h2', rfl⟩ := eB
  obtain rfl := eq_of_heq hν
  obtain rfl := eq_of_heq hfd
  obtain rfl := eq_of_heq hφ
  obtain rfl := eq_of_heq hK
  exact ⟨hI, heq_of_eq (funext hE).symm⟩

theorem isAutFun_transportS {V V' : HSp D} (e : SameSp V' V) {φ : GA D V → ℂ} {φ' : GA D V' → ℂ} (h : HEq φ φ')
    (hφ : IsAutFun V φ) : IsAutFun V' φ' := by
  obtain ⟨L, h1, h2, rfl⟩ := e
  obtain rfl := eq_of_heq h
  exact ⟨hφ.left, hφ.level, hφ.cont⟩

end GlobalTheory.RowLift

end
end

section

open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.satakeTransform_eq_at_thetaLift_of_vacuum_eq : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ) (n n' : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : GU σ n × GU σ n' →* Module.End ℂ M) (s : M), IsStd ϖ σ q δ ψ ρ ω s → CayleyRule q n' ρ (ω.comp (MonoidHom.inl _ _)) s → CayleyRule q n ρ (ω.comp (MonoidHom.inr _ _)) s → n ≤ n' → ∀ h ∈ Hecke ℂ (KU σ n), ∀ h' ∈ Hecke ℂ (KU σ n'), heckeVec (ω.comp (MonoidHom.inl _ _)) (KU σ n) h s = heckeVec (ω.comp (MonoidHom.inr _ _)) (KU σ n') h' s → ∀ qu : ℂˣ, (qu : ℂ) = q → ∀ α : Fin (n / 2) → ℂˣ, SatU ϖ q h (fun i => (α i : ℂ)) = SatU ϖ q h' (fun i => (liftPar qu n n' α i : ℂ)) := by
  first | exact @GlobalTheory.SphTheta.satU_eq_satU_liftPar_of_heckeVec_eq | exact GlobalTheory.SphTheta.satU_eq_satU_liftPar_of_heckeVec_eq | (intros; apply GlobalTheory.SphTheta.satU_eq_satU_liftPar_of_heckeVec_eq <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.schurMult_multiplicitySpaces_of_rapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → SchurMult θ M J χ μ 𝓕 := by
  first | exact @GlobalTheory.SchurConst.schurMult_all | exact GlobalTheory.SchurConst.schurMult_all | (intros; apply GlobalTheory.SchurConst.schurMult_all <;> assumption)
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.discrete_series_test_function_trace : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.HarishChandraCharacters → GlobalTheory.IndefiniteRowSideFullHecke.PseudoCoefficientSeparation.PseudoCoeffSeparation → ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestData V lam M T U μa μf μ fa ff → ∀ (ρ : D.what₂.Tau) (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X] (δ : GArch D.sp.cm.sig V.gram (placeOf D ρ) →* (X →L[ℂ] X)), IsIrrUnitary δ → ∃ c, HasTrace (repOp δ (μa (placeOf D ρ)) (fa (placeOf D ρ))) c ∧ (c ≠ 0 → IsUnitEquiv δ (dsRep M ρ)) := by
  first | exact @GlobalTheory.ArchTrace.trace_pseudoCoeff_arch | exact GlobalTheory.ArchTrace.trace_pseudoCoeff_arch | (intros; apply GlobalTheory.ArchTrace.trace_pseudoCoeff_arch <;> assumption)
end

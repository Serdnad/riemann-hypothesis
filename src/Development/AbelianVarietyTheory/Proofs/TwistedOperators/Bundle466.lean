module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle431
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1129
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle009
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle008
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle017
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle430
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1994
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle405
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle411
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle027
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionTensorProductHasFiniteLength
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle382
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLieImg IsLinHom IsThGen IsHeckeIsog)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeckeLieBC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

theorem epsMul_comp_epsMul {R : Type} [CommRing R] (a b : R) :
    (epsMul a).comp (epsMul b) = epsMul (a * b) :=
  RingHom.ext fun z => by
    ext <;> simp [epsMul, mul_smul]

theorem epsMul_one' {R : Type} [CommRing R] : epsMul (1 : R) = RingHom.id _ :=
  RingHom.ext fun z => by
    ext <;> simp [epsMul]

theorem spMap_epsMul_cancel {R : Type} [CommRing R] {u : R} (hu : IsUnit u) {Z : Scheme.{0}}
    {f g : Sp (DualNumber R) ⟶ Z} (h : spMap (epsMul u) ≫ f = spMap (epsMul u) ≫ g) : f = g := by
  obtain ⟨u, rfl⟩ := hu
  have e : spMap (epsMul ((u⁻¹ : Rˣ) : R)) ≫ spMap (epsMul (u : R)) = 𝟙 _ := by
    rw [GlobalTheory.Frames.ChgBC.spMap_comp_ring, epsMul_comp_epsMul, Units.inv_mul, epsMul_one',
      GlobalTheory.Frames.ChgBC.spMap_id]
  calc f = spMap (epsMul ((u⁻¹ : Rˣ) : R)) ≫ spMap (epsMul (u : R)) ≫ f := by
        rw [← Category.assoc, e, Category.id_comp]
    _ = g := by rw [h, ← Category.assoc, e, Category.id_comp]

end GlobalTheory.HeckeLieBC

namespace GlobalTheory.HeckeLieBC

open GlobalTheory.HeckeFrCompare (toFib_fst toFib_snd)

theorem lieImg_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (T Ω : Type) [CommRing T] [CommRing Ω] (χ : T →+* Ω) (x x' : Sp T ⟶ Xo.X)
    (x₁ x₁' : Sp Ω ⟶ Xo.X) (Ψ : Gx x ⟶ Gx x') (Ψ₁ : Gx x₁ ⟶ Gx x₁') (p : ℕ)
    (v w : Sp (DualNumber T) ⟶ Xo.univ.t.G.left) (w₁ : Sp (DualNumber Ω) ⟶ Xo.univ.t.G.left),
    IsUnit (p : Ω) → IsFib χ Ψ Ψ₁ → IsLieImg p Ψ v w → IsLieImg p Ψ₁ (spMap (dualMap χ) ≫ v) w₁ →
      w₁ = spMap (dualMap χ) ≫ w := by
  intro E _ _ _ H Dw l Xo T Ω _ _ χ x x' x₁ x₁' Ψ Ψ₁ p v w w₁ hp hF hL hL₁
  obtain ⟨pm, pm', hc, hc', hcomm, -⟩ := hF
  obtain ⟨-, -, a, ha, hw⟩ := hL
  obtain ⟨-, -, a₁, ha₁, hw₁⟩ := hL₁

  have hfib : GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori.toFib x₁ (spMap (algebraMap Ω (DualNumber Ω))) a₁ ≫ pm =
      spMap (dualMap χ) ≫ GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori.toFib x (spMap (algebraMap T (DualNumber T))) a := by
    apply GlobalTheory.Frames.ChgBC.gx_ext
    · rw [Category.assoc, hc.2.1, toFib_snd, Category.assoc, toFib_snd, ha₁, ha]
    · rw [Category.assoc, hc.2.2, GlobalTheory.HeckeFrCompare.toFib_fst_assoc, Category.assoc, toFib_fst,
        GlobalTheory.Frames.ChgBC.spMap_comp_ring, GlobalTheory.Frames.ChgBC.spMap_comp_ring, GlobalTheory.Frames.ChgBC.dualMap_alg]
  have hpush : GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori.push Ψ₁ (spMap (algebraMap Ω (DualNumber Ω))) a₁ =
      spMap (dualMap χ) ≫ GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori.push Ψ (spMap (algebraMap T (DualNumber T))) a := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori.push
    rw [← hc'.2.1, reassoc_of% hcomm, reassoc_of% hfib]
  apply spMap_epsMul_cancel hp
  rw [hw₁, hpush, ← hw, ← Category.assoc, ← Category.assoc, GlobalTheory.Frames.ChgBC.spMap_comp_ring,
    GlobalTheory.Frames.ChgBC.spMap_comp_ring, GlobalTheory.Frames.ChgBC.dualMap_eps, map_natCast]

end GlobalTheory.HeckeLieBC
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

noncomputable section

namespace GlobalTheory.SmallDat

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ}

theorem ofMaps_inlS (t : T) (e : Num G i j) (x : HomA G t i j × HomB G i j) (p : Fin (spW₁ G i j).rank)
    (k : Fin (spV G i j).rank) : ofMaps t e x p (e (.inl k)) = GlobalTheory.BigDat.divG (spW₁ G i j) x.1 k p := by
  simp only [ofMaps, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inl, transpose_apply]

theorem ofMaps_inrS (t : T) (e : Num G i j) (x : HomA G t i j × HomB G i j) (p : Fin (spW₁ G i j).rank)
    (k : Fin (spV₁ G i j).rank) : ofMaps t e x p (e (.inr k)) = cA D (GlobalTheory.BigDat.divG (spV₁ G i j) (-x.2) p k) := by
  simp only [ofMaps, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inr, map_apply]

theorem ofMaps_genA (t : T) (e : Num G i j) (β : AF D.host.F) (a : D.host.E) (s : Fin (spW₁ G i j).rank → D.host.E)
    (r : Fin (spV G i j).rank → D.host.E) :
    ofMaps t e (Matrix.of fun i' j' => β ⊗ₜ[D.host.F] (a * r i' * ∑ k, star (s k) * (spW₁ G i j).gram k j'), 0) =
      β • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (vecMulVec (star s) (Sum.elim (a • r) 0 ∘ e.symm)) := by
  ext p q
  obtain ⟨k | k, rfl⟩ := e.surjective q
  · refine (ofMaps_inlS t e _ p k).trans ((GlobalTheory.BigDat.divG_gen (spW₁ G i j) β a s r k p).trans ?_)
    rw [GlobalTheory.BigDat.smul_incM_apply, vecMulVec_apply, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl, mul_comm]
    rfl
  · refine (ofMaps_inrS t e _ p k).trans ?_
    rw [GlobalTheory.BigDat.smul_incM_apply, vecMulVec_apply, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr, neg_zero,
      GlobalTheory.BigDat.divG_zero, Pi.zero_apply, mul_zero, TensorProduct.tmul_zero]
    exact map_zero _

theorem ofMaps_genB (t : T) (e : Num G i j) (β : AF D.host.F) (a : D.host.E) (s : Fin (spV₁ G i j).rank → D.host.E)
    (r : Fin (spW₁ G i j).rank → D.host.E) :
    ofMaps t e (0, Matrix.of fun i' j' => β ⊗ₜ[D.host.F] (a * r i' * ∑ k, star (s k) * (negSp (spV₁ G i j)).gram k j')) =
      β • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (vecMulVec (star r) (Sum.elim 0 (star (a • star s)) ∘ e.symm)) := by
  have hneg : -(Matrix.of fun i' j' => β ⊗ₜ[D.host.F] (a * r i' * ∑ k, star (s k) * (negSp (spV₁ G i j)).gram k j') :
      Matrix _ _ (AE D)) = Matrix.of fun i' j' => β ⊗ₜ[D.host.F] (a * r i' * ∑ k, star (s k) * (spV₁ G i j).gram k j') := by
    ext p q
    simp only [Matrix.neg_apply, of_apply, negSp_gram, Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib, neg_neg,
      TensorProduct.tmul_neg]
  ext p q
  obtain ⟨k | k, rfl⟩ := e.surjective q
  · refine (ofMaps_inlS t e _ p k).trans ((congrFun (congrFun (GlobalTheory.BigDat.divG_zero (spW₁ G i j)) k) p).trans ?_)
    rw [GlobalTheory.BigDat.smul_incM_apply, vecMulVec_apply, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl,
      Pi.zero_apply, mul_zero, TensorProduct.tmul_zero]
    rfl
  · refine (ofMaps_inrS t e _ p k).trans ?_
    rw [GlobalTheory.BigDat.smul_incM_apply, vecMulVec_apply, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr, hneg,
      GlobalTheory.BigDat.divG_gen]
    change β ⊗ₜ[D.host.F] star (a * r p * star (s k)) = β ⊗ₜ[D.host.F] (star (r p) * star (a * star (s k)))
    rw [← star_mul']
    congr 2
    ring

theorem smul_ofMaps_inl_memS {t : T} {e : Num G i j} {Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E} {Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j}
    {X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E} (h : IsDoublyCompatible t i j e Bs Γ X) (v : Pl D.host.F) {x : HomA G t i j}
    (hx : x ∈ latA G t i j) : GlobalTheory.LatVac.liftV v 1 • ofMaps t e (x, 0) ∈ latAtV Γ.V' Γ.W v := by
  refine GlobalTheory.BigDat.map_mem_of_closure ((DistribSMul.toAddMonoidHom (PtS G i j) (GlobalTheory.LatVac.liftV v 1)).comp
    ((maps t e).symm.toLinearMap.toAddMonoidHom.comp (AddMonoidHom.inl _ _))) ?_ hx
  rintro _ ⟨α, hα, -, a, ha, s, hs, r, hr, rfl⟩
  exact (congrArg (fun z => GlobalTheory.LatVac.liftV v 1 • z ∈ latAtV Γ.V' Γ.W v) (ofMaps_genA t e (pairA _ 0 α) a s r)).mpr
    (GlobalTheory.BigDat.one_smul_gen_mem _ _ v hα (h.2.ge (GlobalTheory.BigDat.star_mem_conjSub hs))
      (h.1.2.1.ge (GlobalTheory.BigDat.pair_mem e (GlobalTheory.BigDat.smul_mem_scLat_of_mem ha hr) (zero_mem _))))

theorem smul_ofMaps_inr_memS {t : T} {e : Num G i j} {Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E} {Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j}
    {X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E} (h : IsDoublyCompatible t i j e Bs Γ X) (v : Pl D.host.F) {x : HomB G i j}
    (hx : x ∈ latB G i j) : GlobalTheory.LatVac.liftV v 1 • ofMaps t e (0, x) ∈ latAtV Γ.V' Γ.W v := by
  refine GlobalTheory.BigDat.map_mem_of_closure ((DistribSMul.toAddMonoidHom (PtS G i j) (GlobalTheory.LatVac.liftV v 1)).comp
    ((maps t e).symm.toLinearMap.toAddMonoidHom.comp (AddMonoidHom.inr _ _))) ?_ hx
  rintro _ ⟨α, hα, -, a, ha, s, hs, r, hr, rfl⟩
  exact (congrArg (fun z => GlobalTheory.LatVac.liftV v 1 • z ∈ latAtV Γ.V' Γ.W v) (ofMaps_genB t e (pairA _ 0 α) a s r)).mpr
    (GlobalTheory.BigDat.one_smul_gen_mem _ _ v hα (h.2.ge (GlobalTheory.BigDat.star_mem_conjSub hr))
      (h.1.2.1.ge (GlobalTheory.BigDat.pair_mem e (zero_mem _)
        (GlobalTheory.BigDat.star_mem_conjSub (GlobalTheory.BigDat.smul_mem_scLat_of_mem ha (GlobalTheory.BigDat.star_mem_conjSub hs))))))

theorem latPtS_le_latAtV : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (t : T) (i j : ℕ) (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E), GlobalTheory.FlipMatch.IsDoublyCompatible t i j e Bs Γ X →
    ∀ v : Pl D.host.F, ∀ u ∈ GlobalTheory.SmallDat.latPtS t e v, u ∈ latAtV Γ.V' Γ.W v := by
  intro D T L sc G t i j e Bs Γ X h v u hu
  obtain ⟨hat, h1, h2⟩ := hu
  have e1 : GlobalTheory.LatVac.liftV v 1 • u = u := by
    have := hat (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
    rw [sub_smul, one_smul, sub_eq_zero] at this
    exact this.symm
  have e2 : u = ofMaps t e (mapA t e u, 0) + ofMaps t e (0, mapB e u) :=
    ((ofMaps_maps t e u).symm.trans (congrArg (ofMaps t e) (Prod.ext (add_zero _).symm (zero_add _).symm))).trans
      (map_add (maps t e).symm (mapA t e u, 0) (0, mapB e u))
  have e3 := add_mem (smul_ofMaps_inl_memS h v h1) (smul_ofMaps_inr_memS h v h2)
  rwa [← smul_add, ← e2, e1] at e3

end GlobalTheory.SmallDat

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.XCharBF

noncomputable section

namespace GlobalTheory.XCharBF.DiagCoord

variable {D : D7}

theorem auxiliaryCoordinate_mem_staircaseIdeal {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
    {t : Fin B.rank → D.host.E} (ht : t ∈ d.lat Λ 𝔟) (r : Fin c) (hr : r.1 + r.1 + 1 ≠ c) :
    ((d.aᴴ * B.gram) *ᵥ t) r ∈ 𝔟 r.rev := by
  obtain ⟨y, -, v, hv, rfl⟩ := ht
  have hG : B.gramᴴ = B.gram := Matrix.ext fun i j => (B.herm.eq (B.frame j) (B.frame i) : star (B.gram j i) = B.gram i j)
  have hperp : d.aᴴ * B.gram * frameMat B A d.ι = 0 := by
    have h1 := congrArg Matrix.conjTranspose d.perp
    have e : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat B A d.ι) = (frameMat B A d.ι)ᴴ := rfl
    rw [e, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hG, conjTranspose_zero] at h1
    rw [← h1, Matrix.mul_assoc]
  have hgram : d.aᴴ * B.gram * d.a = antiDiagonalSignGramMatrix c ε := d.gram
  rw [mulVec_add, mulVec_mulVec, mulVec_mulVec, hperp, hgram, zero_mulVec, zero_add]
  rw [mulVec, dotProduct, Finset.sum_eq_single r.rev]
  · have : antiDiagonalSignGramMatrix c ε r r.rev = 1 := by
      have := r.2
      simp only [antiDiagonalSignGramMatrix, Fin.val_rev]
      rw [if_pos (by omega), if_neg (fun h => hr (by rw [Fin.ext_iff, Fin.val_rev] at h; omega))]
    rw [this, one_mul]; exact hv _
  · intro q _ hq
    have : antiDiagonalSignGramMatrix c ε r q = 0 := by
      have := r.2; have := q.2
      simp only [antiDiagonalSignGramMatrix]
      rw [if_neg (fun h => hq (by rw [Fin.ext_iff, Fin.val_rev]; omega))]
    rw [this, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem negPair_colsOf {n c k : ℕ} (G : Matrix (Fin n) (Fin n) D.host.E) (hG : ∀ i j, star (G j i) = G i j)
    (a : Matrix (Fin n) (Fin c) D.host.E) (f : Fin k → Fin c) (w : Fin k → D.host.E) (s : Fin n → D.host.E) (p : Fin k) :
    ∑ j, (∑ l, star (s l) * (-G) l j) * colsOf a f w j p = -(w p * star (((aᴴ * G) *ᵥ s) (f p))) := by
  simp only [colsOf, mulVec, dotProduct, Matrix.mul_apply, conjTranspose_apply, star_sum, star_mul', star_star, hG,
    Matrix.neg_apply, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem entry_rankOne {m n k l : ℕ} (q : Matrix (Fin k) (Fin m) D.host.E) (e : Matrix (Fin n) (Fin l) D.host.E) (a : D.host.E)
    (t : Fin m → D.host.E) (g : Fin n → D.host.E) (p : Fin k) (p' : Fin l) :
    (q * Matrix.of (fun i j => a * t i * g j) * e) p p' = a * (q *ᵥ t) p * ∑ j, g j * e j p' := by
  simp only [Matrix.mul_apply, Matrix.of_apply, mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem rat_tmul_entry {m n k l : ℕ} (q : Matrix (Fin k) (Fin m) D.host.E) (C : Matrix (Fin m) (Fin n) D.host.E)
    (e : Matrix (Fin n) (Fin l) D.host.E) (X : AF D.host.F) (p : Fin k) (p' : Fin l) :
    (rat q ⬝ (Matrix.of fun i j => X ⊗ₜ[D.host.F] C i j : Mx D m n) ⬝ rat e) p p' = X ⊗ₜ[D.host.F] (q * C * e) p p' := by
  have hinc : ∀ x, incA D x = (1 : AF D.host.F) ⊗ₜ[D.host.F] x := fun _ => rfl
  simp only [Matrix.mul_apply, rat, Matrix.map_apply, Matrix.of_apply, hinc, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    mul_one, ← TensorProduct.tmul_sum]

theorem stairId_mul_inv_succ (𝔞 𝔞' : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (h𝔞 : 𝔞 ≠ 0) (h𝔞' : 𝔞' ≠ 0) {c₁ c₂ : ℕ}
    (q₁ : Fin c₁) (q₂ : Fin c₂) (hc : c₂ = c₁ + 1) (hq : q₂.1 = q₁.1 + 1) :
    stairId 𝔞 𝔞' c₁ q₁ * (stairId 𝔞 𝔞' c₂ q₂)⁻¹ = 𝔞' := by
  unfold stairId
  rw [show c₂ - q₂.1 = c₁ - q₁.1 by omega, hq, pow_succ 𝔞' (q₁.1 + 1)]
  have h1 : 𝔞 ^ (c₁ - q₁.1) ≠ 0 := pow_ne_zero _ h𝔞
  have h2 : 𝔞' ^ (q₁.1 + 1) ≠ 0 := pow_ne_zero _ h𝔞'
  field_simp

theorem colsOf_gram {n c k : ℕ} (G : Matrix (Fin n) (Fin n) D.host.E) (a : Matrix (Fin n) (Fin c) D.host.E) (f g : Fin k → Fin c)
    (w w' : Fin k → D.host.E) (p q : Fin k) :
    ((colsOf a f w)ᴴ * G * colsOf a g w') p q = star (w p) * w' q * (aᴴ * G * a) (f p) (g q) := by
  simp only [colsOf, Matrix.mul_apply, conjTranspose_apply, star_mul', Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring



theorem diag_mem_complId : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {F : GlobalTheory.Asc.Frames G}, Std F →
    ∀ (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) (u : WO (negSp (G.V (.grid (2 * ρ + 2) 0))) (G.V (.grid (2 * ρ + 1) 0))),
    u ∈ latO _ _ (G.Λ (.grid (2 * ρ + 2) 0) : Set _) (G.Λ (.grid (2 * ρ + 1) 0) : Set _) (fun _ => True) →
    ∀ p : Fin ρ, ((F.dJ ρ h).pY ⬝ u ⬝ (F.dB ρ h).jY) p p ∈ complId (D.host.AA * G.pl.stAbar sc) := by
  intro D T L sc G F hF ρ h u hu p
  obtain ⟨hcJ, heJ, -⟩ := hF.hJ ρ h
  obtain ⟨hcB, heB, sB, he'B⟩ := hF.hB ρ h
  set aJ := G.colDec (2 * ρ + 1) (by omega) (by omega) with haJ
  set aB := G.colDec (2 * ρ + 2) (by omega) h with haB
  obtain ⟨hAA, -⟩ := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).1
  obtain ⟨hA, hconj⟩ := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).2 T L G.pl sc
  have hAb : G.pl.stAbar sc ≠ 0 := by
    intro h0
    apply hA
    rw [FractionalIdeal.eq_zero_iff] at h0 ⊢
    intro y hy
    have h1 : star y ∈ G.pl.stAbar sc := (hconj _).2 (by rwa [star_star])
    have h2 := h0 _ h1
    rwa [star_eq_zero] at h2

  have hJ : ∀ t ∈ G.Λ (.grid (2 * ρ + 1) 0), ((F.dJ ρ h).qY *ᵥ t) p =
      star ((-D.host.xi0) ^ (p.1 + 1)) * ((aJ.aᴴ * (G.V (.grid (2 * ρ + 1) 0)).gram) *ᵥ t) (Fin.castLE (by omega) p) := by
    intro t _
    simp only [HypDec.qY, heJ, mulVec, dotProduct, Matrix.mul_apply, conjTranspose_apply, colsOf, star_mul', Finset.mul_sum,
      Finset.sum_mul, mul_assoc]
  have hJmem : ∀ t ∈ G.Λ (.grid (2 * ρ + 1) 0), ((aJ.aᴴ * (G.V (.grid (2 * ρ + 1) 0)).gram) *ᵥ t) (Fin.castLE (by omega) p) ∈
      stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) (Fin.castLE (by omega) p).rev := by
    intro t ht
    have ht' : t ∈ aJ.lat (G.sp.P (2 * ρ + 1)).lat (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1)) := by
      rw [haJ, ← G.sp.colLat (2 * ρ + 1) (by omega) (by omega)]; exact ht
    exact auxiliaryCoordinate_mem_staircaseIdeal aJ _ _ ht' _ (by simp only [Fin.val_castLE]; omega)

  have hBmem : ∀ s ∈ G.Λ (.grid (2 * ρ + 2) 0),
      star (((aB.aᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram) *ᵥ s) (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev) ∈
      (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1) (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev)⁻¹ := by
    intro s hs
    have hs' : s ∈ aB.lat (G.sp.P (2 * ρ + 2)).lat (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1)) := by
      rw [haB, ← G.sp.colLat (2 * ρ + 2) (by omega) h]; exact hs
    have h1 := auxiliaryCoordinate_mem_staircaseIdeal aB _ _ hs' (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev
      (by simp only [Fin.val_rev, Fin.val_castLE]; omega)
    exact ((GlobalTheory.ChiGrid.stairId_ne_zero_and_mem_rev_iff D _ _ hA hconj _ _).2 _).1 h1

  have hsc : star ((-D.host.xi0) ^ (p.1 + 1)) * sB p = 1 := by
    have h1 := congrFun (congrFun (F.dB ρ h).e'e p) p
    rw [he'B, heB, colsOf_gram, Matrix.one_apply_eq] at h1
    have h2 : (aB.aᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram * aB.a) (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev
        (Fin.castLE (by omega) p) = 1 := by
      rw [show aB.aᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram * aB.a = antiDiagonalSignGramMatrix (2 * ρ + 2 - 1) (-1) from aB.gram]
      simp only [antiDiagonalSignGramMatrix, Fin.val_rev, Fin.val_castLE]
      rw [if_pos (by omega), if_neg (fun e => by rw [Fin.ext_iff, Fin.val_rev, Fin.val_castLE] at e; omega)]
    rw [h2, mul_one] at h1
    have h3 := congrArg star h1
    rw [star_mul', star_star, star_one] at h3
    rw [mul_comm]; exact h3
  have hGB : ∀ i j, star ((G.V (.grid (2 * ρ + 2) 0)).gram j i) = (G.V (.grid (2 * ρ + 2) 0)).gram i j := fun i j =>
    (G.V (.grid (2 * ρ + 2) 0)).herm.eq ((G.V (.grid (2 * ρ + 2) 0)).frame j) ((G.V (.grid (2 * ρ + 2) 0)).frame i)

  have keyE : ∀ a ∈ D.host.AA, ∀ s ∈ G.Λ (.grid (2 * ρ + 2) 0), ∀ t ∈ G.Λ (.grid (2 * ρ + 1) 0),
      ((F.dJ ρ h).qY * Matrix.of (fun i j => a * t i * ∑ k, star (s k) * (negSp (G.V (.grid (2 * ρ + 2) 0))).gram k j) *
        (F.dB ρ h).e') p p ∈ D.host.AA * G.pl.stAbar sc := by
    intro a ha s hs t ht
    rw [entry_rankOne _ _ a t (fun j => ∑ k, star (s k) * (negSp (G.V (.grid (2 * ρ + 2) 0))).gram k j), hJ t ht, he'B,
      negSp_gram, negPair_colsOf _ hGB]
    have e : a * (star ((-D.host.xi0) ^ (p.1 + 1)) *
          ((aJ.aᴴ * (G.V (.grid (2 * ρ + 1) 0)).gram) *ᵥ t) (Fin.castLE (by omega) p)) *
        -(sB p * star (((aB.aᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram) *ᵥ s) (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev)) =
        -(a * (((aJ.aᴴ * (G.V (.grid (2 * ρ + 1) 0)).gram) *ᵥ t) (Fin.castLE (by omega) p) *
          star (((aB.aᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram) *ᵥ s) (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev))) := by
      linear_combination (-(a * ((aJ.aᴴ * (G.V (.grid (2 * ρ + 1) 0)).gram) *ᵥ t) (Fin.castLE (by omega) p) *
          star (((aB.aᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram) *ᵥ s) (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev))) * hsc
    rw [e]
    refine Submodule.neg_mem _ (FractionalIdeal.mul_mem_mul ha ?_)
    rw [← stairId_mul_inv_succ (G.pl.stA sc) (G.pl.stAbar sc) hA hAb (Fin.castLE (by omega) p : Fin (2 * ρ + 1 - 1)).rev
      (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev (by omega) (by simp only [Fin.val_rev, Fin.val_castLE]; omega)]
    exact FractionalIdeal.mul_mem_mul (hJmem t ht) (hBmem s hs)
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hw
    have key : ((F.dJ ρ h).pY ⬝ (Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F]
        (a * t i * ∑ k, star (s k) * (negSp (G.V (.grid (2 * ρ + 2) 0))).gram k j)) ⬝ (F.dB ρ h).jY) p p =
        (pairA D.host.F 0 α) ⊗ₜ[D.host.F] ((F.dJ ρ h).qY * Matrix.of (fun i j => a * t i * ∑ k, star (s k) *
          (negSp (G.V (.grid (2 * ρ + 2) 0))).gram k j) * (F.dB ρ h).e') p p :=
      rat_tmul_entry _ _ _ _ _ _
    rw [key]
    exact tmul_mem_complId hα (keyE a ha s hs t ht)
  | zero => simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_apply]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply]; exact neg_mem hx

end GlobalTheory.XCharBF.DiagCoord
end
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

namespace GlobalTheory

theorem isIsotypic_of_uEquiv_left {G X Y K : Type} [Group G] [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    {δ : G →* (X →L[ℂ] X)} {δ' : G →* (Y →L[ℂ] Y)} {ρ : G →* (K →L[ℂ] K)}
    (e : ∃ A : X ≃ₗᵢ[ℂ] Y, ∀ g x, A (δ g x) = δ' g (A x)) (h : IsIsotypic δ ρ) : IsIsotypic δ' ρ := by
  obtain ⟨A, hA⟩ := e
  refine eq_top_iff.2 (h.ge.trans (isoPart_le (Submodule.isClosed_topologicalClosure _) fun T hT x => ?_))
  have hs : ∀ g y, A.symm (δ' g y) = δ g (A.symm y) := fun g y => by
    apply A.injective
    rw [hA g, LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]
  have hx : T x = (T ∘L (A.symm : Y →L[ℂ] X)) (A x) := by simp
  rw [hx]
  refine apply_mem_isoPart (mem_homIn_top.2 fun g y => ?_) _
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rw [hs]
  exact (mem_homIn_top.1 hT) g _

theorem hasDSComp_of_trace_ne_zero : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.FlathFactorisation → GlobalTheory.Published.HarishChandraCharacters → GlobalTheory.IndefiniteRowSideFullHecke.PseudoCoefficientSeparation.PseudoCoeffSeparation → ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestData V lam M T U μa μf μ fa ff → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → ∀ c : ℂ, HasTrace (repOp π μ (tensor D.sp.cm.sig V.gram fa ff)) c → c ≠ 0 → HasDSComp M π := by
  intro hDS hFl hHC hPC D V lam S M T U μa μf μ _ _ fa ff hTD H _ _ _ π hπ c hc hc0 τ
  obtain ⟨δ, hδ⟩ := hFl.exists_hasCompPl (isCMExt_host D) (isHermND_gram (V := V)) hπ (.inl (placeOf D τ))
  have hδ' : IsIsotypic (G := GArch D.sp.cm.sig V.gram (placeOf D τ)) δ.π
      (π.comp (embArch D.sp.cm.sig V.gram (placeOf D τ))) := hδ
  obtain ⟨c', hc', himp⟩ := GlobalTheory.T.discrete_series_test_function_trace hDS hHC hPC D V lam S M T U μa μf μ fa ff hTD τ δ.H δ.π δ.isIrr
  by_cases hc'0 : c' = 0
  · exfalso
    have hRP : IsRestrictedProd D.sp.cm.sig V.gram (frameLat V) μa μf μ := hTD.2.2.2.2.1
    have hmem : ∀ w, fa w ∈ CcArch D.sp.cm.sig V.gram w := hTD.2.2.2.2.2.1.mem
    have hfin : IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff := hTD.2.2.2.2.2.2.isFinFamily
    obtain ⟨Q, hQ, hrep⟩ := GlobalTheory.T.pureTensorOperator_split_oneRealPlace D V μa μf μ hRP fa ff hmem hfin H π hπ.unitary (placeOf D τ)
    haveI : (μa (placeOf D τ)).IsHaarMeasure := hRP.1 _
    have hint : Integrable (fa (placeOf D τ)) (μa (placeOf D τ)) :=
      (continuous_of_mem_ccSmooth (continuous_archCoord _ _ _) (hmem _)).integrable_of_hasCompactSupport (hmem _).1
    have hπw : IsUnitaryRep (π.comp (embArch D.sp.cm.sig V.gram (placeOf D τ))) :=
      isUnitaryRep_comp hπ.unitary (continuous_embArch _ _ _)
    have htc : IsTraceClass (repOp (π.comp (embArch D.sp.cm.sig V.gram (placeOf D τ))) (μa (placeOf D τ)) (fa (placeOf D τ)) * Q) := hrep ▸ hc.1
    let δw : GArch D.sp.cm.sig V.gram (placeOf D τ) →* (δ.H →L[ℂ] δ.H) := δ.π
    have hδirr : IsIrrUnitary δw := δ.isIrr
    have hδw : IsIsotypic δw (π.comp (embArch D.sp.cm.sig V.gram (placeOf D τ))) := hδ'
    have hc'w : HasTrace (repOp δw (μa (placeOf D τ)) (fa (placeOf D τ))) 0 := hc'0 ▸ hc'
    have h0 := GlobalTheory.T.trace_integratedOp_mul_eq_zero_of_isotypic (GArch D.sp.cm.sig V.gram (placeOf D τ)) _ _ hint δ.H H δw _ hδirr hπw hδw Q hQ hc'w htc
    exact hc0 (hc.2.symm.trans (hrep ▸ h0))
  · show IsIsotypic (dsRep M τ) (π.comp (embW V (placeOf D τ)))
    exact isIsotypic_of_uEquiv_left (G := GArch D.sp.cm.sig V.gram (placeOf D τ)) (himp hc'0) hδ'

end GlobalTheory
end

section

open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ExtTensorIrr

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

theorem piTensor_isIrreducible : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (β : Type) [Fintype β]
    (c : β → Type) [∀ j, Fintype (c j)] [∀ j, DecidableEq (c j)] (s : ∀ j, GlobalTheory.SmGL.IrrRep (GL (c j) k)),
    (GlobalTheory.SmGL.piTensor fun j => (s j).ρ).IsIrreducible := by
  intro hBZ k _ _ _ _ β _ c _ _ s
  obtain ⟨hAdm, -, -, -⟩ := hBZ k
  exact GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur (fun j => (s j).ρ) (fun j => (s j).irr)
    fun j φ hφ => GlobalTheory.SchurAdm.schur_admissible (GL (c j) k) (KO k (c j)) GlobalTheory.SplitFlip.isOpen_KO
      GlobalTheory.SplitFlip.isCompact_KO (s j).V (s j).ρ (s j).irr
      (hAdm (c j) (s j).V (s j).ρ (s j).smooth (s j).irr) φ hφ

end GlobalTheory.ExtTensorIrr
end
end

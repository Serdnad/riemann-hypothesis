module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.StConj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.HodgeTrAt
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle025
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PhiOfDivOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.CocharacterLieDivisors.CocharacterLieAlgebra.StCochar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle680
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.CocharacterLieDivisors.CocharacterLieAlgebra.PCocharToLie
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle227
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
public import Mathlib.RepresentationTheory.Semisimple
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012

@[expose] public section

section

open Formalism.MainNotions.N
open GlobalTheory.BlockSum (blockRep vecComp vecComp_mulVec)

namespace UpperTheory.Gal.Int.Div

section Bridge

variable {Γ k : Type} [Group Γ] [Field k] {n : ℕ}

private def colRep (ρ : Γ →* GL (Fin n) k) : Representation k Γ (Fin n → k) where
  toFun g := Matrix.mulVecLin (ρ g).val
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [Matrix.mulVecLin_mul]

private theorem colRep_apply (ρ : Γ →* GL (Fin n) k) (g : Γ) (v : Fin n → k) :
    colRep ρ g v = (ρ g).val.mulVec v := rfl

private theorem isSSRep_iff (ρ : Γ →* GL (Fin n) k) : IsSSRep ρ ↔ (colRep ρ).IsSemisimpleRepresentation := by
  constructor
  · intro h
    refine ⟨fun a => ?_⟩
    obtain ⟨W', hW', hc⟩ := h a.toSubmodule fun g v hv => a.apply_mem_toSubmodule g hv
    exact ⟨⟨W', fun g v hv => hW' g v hv⟩,
      disjoint_iff.2 (Subrepresentation.toSubmodule_injective hc.inf_eq_bot),
      codisjoint_iff.2 (Subrepresentation.toSubmodule_injective hc.sup_eq_top)⟩
  · intro h W hW
    obtain ⟨b, hb⟩ := exists_isCompl (⟨W, fun g v hv => hW g v hv⟩ : Subrepresentation (colRep ρ))
    exact ⟨b.toSubmodule, fun g v hv => b.apply_mem_toSubmodule g hv,
      disjoint_iff.2 (congrArg Subrepresentation.toSubmodule hb.inf_eq_bot),
      codisjoint_iff.2 (congrArg Subrepresentation.toSubmodule hb.sup_eq_top)⟩

end Bridge

theorem sSBlock_of : SSBlock := by
  intro Γ k _ _ a m n e r hr
  rw [isSSRep_iff, Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  haveI := (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).1
    ((isSSRep_iff r).1 hr)
  set R := blockRep (a := fun _ : Fin m => a) e fun _ => r
  let L : (colRep R).asModule ≃ₗ[k] (Fin m → (colRep r).asModule) :=
    (colRep R).asModuleEquiv.trans ((vecComp e k).trans
      (LinearEquiv.piCongrRight fun _ => (colRep r).asModuleEquiv.symm))
  have hL : ∀ (g : Γ) (x : (colRep R).asModule),
      L (MonoidAlgebra.single g (1 : k) • x) = MonoidAlgebra.single g (1 : k) • L x := by
    intro g x
    funext j
    apply (colRep r).asModuleEquiv.injective
    simp only [L, LinearEquiv.trans_apply, LinearEquiv.piCongrRight_apply, Pi.smul_apply,
      Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_single_one,
      LinearEquiv.apply_symm_apply, colRep_apply]
    exact vecComp_mulVec e (fun _ => r) g _ j
  exact IsSemisimpleModule.of_injective
    (MonoidAlgebra.equivariantOfLinearOfComm L.toLinearMap hL) L.injective

end UpperTheory.Gal.Int.Div
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

private theorem aeval_matrix_map {K L : Type} [Field K] [Field L] (f : K →+* L) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (Q : K[X]) :
    aeval (M.map f) (Q.map f) = (aeval M Q).map f := by
  simp only [aeval_def, eval₂_map]
  have h := hom_eval₂ Q (algebraMap K (Matrix (Fin n) (Fin n) K)) f.mapMatrix M
  rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at h
  rw [h]
  congr 1
  ext a : 1
  simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_map]

theorem UpperTheory.Gal.Int.Div.genPin_of :
    GenPin := by
  intro l _ ι a M s hcard hgen hann hdet
  set P := (Multiset.map (fun b ↦ X - C b) s).prod with hPdef
  have hround : map ι.toRingHom (map ι.symm.toRingHom P) = P := by
    rw [Polynomial.map_map]
    convert Polynomial.map_id
    ext z
    simp
  have hann2 : aeval (M.map ι.toRingHom) (UpperTheory.Gal.crystallineComparison.rootPol s) = 0 := by
    show aeval (M.map ι.toRingHom) P = 0
    rw [← hround, aeval_matrix_map, hann]
    simp
  have hdet2 : (M.map ι.toRingHom).det = s.prod := by
    have hd := RingHom.map_det ι.toRingHom M
    rw [RingHom.mapMatrix_apply] at hd
    rw [← hd]
    exact hdet
  rw [← Matrix.charpoly_map]
  exact UpperTheory.Gal.crystallineComparison.charAnn_of ℂ a _ s hcard hgen hann2 hdet2
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.dGenMul_of :
    DGenMul := by
  classical
  intro a q B ha hc hG
  obtain ⟨α, rfl⟩ : ∃ α : Fin a → ℂˣ, Finset.univ.val.map α = B := by
    induction B using Quotient.inductionOn with
    | h l =>
      have hl : l.length = a := hc
      subst hl
      exact ⟨l.get, by rw [Fin.univ_val_map, List.ofFn_get]; rfl⟩
  refine UpperTheory.Gal.crystallineComparison.genMul_of ℂˣ a α ?_
  intro m hs hp
  have hne := hG α rfl
  unfold DGen at hne
  rw [map_mul] at hne
  have h3 := right_ne_zero_of_mul hne
  rw [map_prod] at h3
  have hle : ∀ i, m i < a + 1 := fun i => Nat.lt_succ_of_le
    (hs ▸ Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  have hone : ((1 : Fin (a + 1)) : ℕ) = 1 := by
    rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
  by_cases hm : (fun i => (⟨m i, hle i⟩ : Fin (a + 1))) = fun _ => 1
  · intro i
    have h := congrArg Fin.val (congrFun hm i)
    rw [hone] at h
    exact h
  · exfalso
    have hmem : (fun i => (⟨m i, hle i⟩ : Fin (a + 1))) ∈
        (Finset.univ : Finset (Fin a → Fin (a + 1))).filter
          (fun m => (∑ i, (m i : ℕ)) = a ∧ m ≠ fun _ => 1) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs, hm⟩
    refine Finset.prod_ne_zero_iff.mp h3 _ hmem ?_
    have hp' : ∏ i, (α i : ℂ) ^ m i = ∏ i, (α i : ℂ) := by
      have h := congrArg Units.val hp
      simpa [Units.coe_prod] using h
    simpa [map_sub, map_prod, map_pow, MvPolynomial.aeval_X] using sub_eq_zero.mpr hp'
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

namespace UpperTheory.Gal.Int.Div

theorem htCochar_of (hJ : JumpCard) : PositivityTheory.AutomorphicGaloisHodgeTate.Div.HTCochar := by
  intro E Ω _ _ _ _ _ l _ N n V _ ⟨P, AI, hT, w, A, _, _, O, i1, i2, i3, Bw, _, τ, J, hj, ks, k1, k2, k3⟩
  have hc : J.card = N := by
    obtain ⟨L, r', hm, hd, τ', ht, hcnt⟩ := id hj
    obtain ⟨J', h1, h2⟩ := hJ l P AI hT E Ω A O Bw N _ ⟨L, r', hm, hd⟩ τ L τ' ht
    rw [← h2]
    congr 1
    ext a
    exact_mod_cast (hcnt a).trans (h1.count_eq P hm ht a).symm
  obtain ⟨T⟩ := hT
  obtain ⟨Pm, k, hk, hf⟩ := GlobalTheory.HodgeTateCochar.mem_closure_of_jumps l P AI T Bw _ τ J hj hc
  refine ⟨ℂ_[l], inferInstance, inferInstance, inferInstance, Pm.val, k, ks, (Matrix.isUnit_iff_isUnit_det _).1 Pm.isUnit, k1, k3,
    fun i => ?_, fun f h0 t ht => ?_⟩
  · have := k2 i
    rw [← hk] at this
    obtain ⟨j, -, e⟩ := Multiset.mem_map.1 this
    exact ⟨j, e⟩
  · rw [← Matrix.coe_units_inv]
    refine hf Bw.Kw le_rfl _ (fun g _ => ?_) t ht
    have := congrArg (algebraMap (Qbar l) ℂ_[l]) (h0 g)
    rw [map_zero, MvPolynomial.eval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left] at this
    rw [MvPolynomial.eval_map]
    exact this

theorem senWLac_of (hJ : JumpCard) : SenWLac := PositivityTheory.AutomorphicGaloisHodgeTate.Div.cocharToLie_holds (htCochar_of hJ)

end UpperTheory.Gal.Int.Div
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.Int.Geo (GeoOne)

namespace UpperTheory.Gal.Int.Div

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem apart_cpl {w u : HeightOneSpectrum (𝓞 E)} (hu : IsSplitAt u) : Apart w (cpl u) ↔ Apart w u := by
  unfold Apart
  rw [(GlobalTheory.SplitPts.over_split hu).2.1]

private theorem apart_symm {w u : HeightOneSpectrum (𝓞 E)} (h : Apart w u) : Apart u w := Ne.symm h

private theorem mem_cpl (hC : CplMem) {l : ℕ} {u : HeightOneSpectrum (𝓞 E)} (h : ((l : ℕ) : 𝓞 E) ∈ u.asIdeal) :
    ((l : ℕ) : 𝓞 E) ∈ (cpl u).asIdeal := (hC E u l l (by simp)).2 h

private theorem move (hC : CplMem) (hS : SameOr) {l d : ℕ} (hl : l.Prime) (hd : 0 < d) {x : E} (hx : x ^ 2 = -(d : E))
    {u w : HeightOneSpectrum (𝓞 E)} (hs : IsSplitAt u) (hu : ((l : ℕ) : 𝓞 E) ∈ u.asIdeal) (hw : ((l : ℕ) : 𝓞 E) ∈ w.asIdeal)
    {p : HeightOneSpectrum (𝓞 E) → Prop} (h1 : p u) (h2 : p (cpl u)) :
    ∃ u', ((l : ℕ) : 𝓞 E) ∈ u'.asIdeal ∧ SameK x u' w ∧ p u' ∧ ∀ y, Apart y u' ↔ Apart y u := by
  rcases hS E l d hl hd x hx u w hu hw with h | h
  · exact ⟨u, hu, h, h1, fun _ => Iff.rfl⟩
  · exact ⟨cpl u, mem_cpl hC hu, h, h2, fun _ => apart_cpl hs⟩

end

theorem seedFinOdd_of (hD : DivAll) (hC : CplMem) (hS : SameOr) (hSat : SatConj) (hTy : TyConj) (hLac : LacConj) (hGap : GapLac)
    (hGen : DGenMul) (hG : GeoOne) : SeedFinOdd := by
  intro E Ω _ _ _ _ _ _ l _ ι a ha hodd d hd T hT w₀ v' hw₀ hs₀ hv' hs' hap U₀ S Y
  refine ⟨∅, by simp, fun U hA hty hwt hsph hsv _ => ?_⟩
  obtain ⟨hd0, x, hx⟩ := hd.1
  have hlac : LacWtAt ι v' U := by
    obtain ⟨-, τ, hτ, h⟩ := hwt
    obtain ⟨lam, hlam⟩ := GlobalTheory.Cong.exists_weight_of_isAutRepU E a U hA.1
    exact ⟨τ, hτ, lam τ, hlam τ, hGap a _ (card_wtJumps _) (h _ (hlam τ) _ (wtJumps_val _))⟩
  have geo : ∀ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → ∃ u₀ u', SameK x w u' ∧ (∀ y, Apart y u₀ ↔ Apart y w₀) ∧
      (∀ y, Apart y u' ↔ Apart y v') ∧ _ := fun w hw => by
    obtain ⟨u₀, a1, a2, a3, a4⟩ := move hC hS (Fact.out : l.Prime) hd0 hx hs₀ hw₀ hw
      (p := fun u => GlobalTheory.CongW.TyEll E l a u U) hty (hTy E l a U w₀ hs₀ hty)
    obtain ⟨u', b1, b2, b3, b4⟩ := move hC hS (Fact.out : l.Prime) hd0 hx hs' hv' hw
      (p := fun u => (∃ B, SatU U u B) ∧ LacWtAt ι u U) ⟨hsv, hlac⟩ ⟨hSat E a U hA.1 v' hs' hsv, hLac E l ι a ha U v' hlac⟩
    exact ⟨u₀, u', fun y hy => (b2 y hy).symm, a4, b4, hG E Ω l ι a hodd d hd x hx T hT u₀ u' a1 b1
      ((a4 u').2 (apart_symm ((b4 w₀).2 (apart_symm hap)))) (fun y hy => (a2 y hy).trans (b2 y hy).symm) S U hA a3
      (fun y h1 h2 h3 => hsph y h1 ((a4 y).1 h2) h3) b3.1 b3.2⟩
  obtain ⟨_, _, -, -, -, g1, g2, -⟩ := geo v' hv'
  obtain ⟨r, ⟨r1, r2, V, X, v1, v2, v3⟩, hr⟩ := hD E Ω l ι a ha d hd.1 U hA.1 g1
  have hgm : ∀ w B, SatU U w B → GlobalTheory.CongW.GenOf DGen a (normV w) B → GenericMul B := fun w B hB hg =>
    hGen a _ B ha hB.choose_spec.2.card hg
  have hsp : ∀ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → IsSplitAt w := fun w hw => by
    by_contra h
    exact (hd.2.2.2 w h).1 hw
  refine ⟨r, r1, r2, ⟨V, X, v1, v2, fun w h1 h2 h3 _ => v3 w h1 h2 h3⟩, fun w _ h1 h2 _ B hB hg => ?_,
    fun w _ h1 h2 h3 h4 => ?_, fun w _ h1 h2 h3 _ B hB hg => ?_⟩
  · obtain ⟨dd, ρ, k1, k2⟩ := g2 w h1 h2 ⟨B, hB⟩
    exact (hr dd ρ k1 w).1 h1.1 h2 B hB (hgm w B hB hg) (k2 B hB)
  · obtain ⟨u₀, u', c1, c2, c3, -, -, g3⟩ := geo w h1
    obtain ⟨⟨dd, ρ, k1, k2, k3⟩, -⟩ := g3 w h1 c1 ((c2 w).2 h2) ((c3 w).2 h3) (hsph w (hsp w h1) h2 h4)
    exact (hr dd ρ k1 w).2.1 k2 k3
  · obtain ⟨u₀, u', c1, c2, c3, -, -, g3⟩ := geo w h1
    obtain ⟨-, dd, ρ, k1, k2⟩ := g3 w h1 c1 ((c2 w).2 h2) ((c3 w).2 h3) ⟨B, hB⟩
    exact ((hr dd ρ k1 w).2.2 (hsp w h1) B hB (hgm w B hB hg) (k2 B hB)).2.phiAt

end UpperTheory.Gal.Int.Div

end
end

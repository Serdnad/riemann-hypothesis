module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1384
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2535
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle763
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1539
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefMapNormEquivariantBasisOfFive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1546
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsEtaConj
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LUnifOfRhoGeoEquivAll
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle305
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle059
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle057
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAdmissibleThetaLatticeGenerators
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle066
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RunWeightDom
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ThetaArchimedeanDataIndefiniteModels
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsScalarWeightAuxiliaryFormOfRunConditions
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

def semiToLin {S R : Type} [CommRing S] [CommRing R] [Algebra S R] {M N : Type} [AddCommGroup M] [Module S M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower S R N] (f : M →ₛₗ[algebraMap S R] N) :
    M →ₗ[S] N where
  toFun := f
  map_add' := f.map_add
  map_smul' s m := by simp [f.map_smulₛₗ, algebraMap_smul]

theorem fp_of_tensor_equiv {S R M N : Type} [CommRing S] [CommRing R] [Algebra S R] [AddCommGroup M] [Module S M]
    [AddCommGroup N] [Module R N] {g : ℕ} (e : R ⊗[S] M ≃ₗ[R] N) (h : FP S M g) : FP R N g := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨Module.Finite.equiv e, Module.Projective.of_equiv e, fun p => ?_⟩
  rw [← Module.rankAtStalk_eq_of_equiv e, Module.rankAtStalk_baseChange, h3]

theorem wedge_of_isBaseChange {S R M N M₂ N₂ : Type} [CommRing S] [CommRing R] [Algebra S R]
    [AddCommGroup M] [Module S M] [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower S R N]
    [AddCommGroup M₂] [Module S M₂] [AddCommGroup N₂] [Module R N₂] [Module S N₂] [IsScalarTower S R N₂]
    {φ : M →ₗ[S] N} {ψ : M₂ →ₗ[S] N₂} (hφ : IsBaseChange R φ) (hψ : IsBaseChange R ψ)
    (cM : M →ₗ[S] M →ₗ[S] M₂) (cN : N →ₗ[R] N →ₗ[R] N₂) (hc : ∀ m m', ψ (cM m m') = cN (φ m) (φ m'))
    (eM : ⋀[S]^2 M ≃ₗ[S] M₂) (heM : ∀ a b, eM (exteriorPower.ιMulti S 2 ![a, b]) = cM a b) :
    ∃ e : ⋀[R]^2 N ≃ₗ[R] N₂, ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = cN a b := by
  have hE := GlobalTheory.TopForm.isBaseChange_exteriorPower hφ 2
  let e : ⋀[R]^2 N ≃ₗ[R] N₂ := hE.equiv.symm ≪≫ₗ eM.baseChange S R _ _ ≪≫ₗ hψ.equiv
  refine ⟨e, ?_⟩
  have key : ∀ m m', e (exteriorPower.ιMulti R 2 ![φ m, φ m']) = cN (φ m) (φ m') := by
    intro m m'
    have h1 : exteriorPower.ιMulti R 2 ![φ m, φ m'] =
        GlobalTheory.exteriorPowerMapOver R 2 φ (exteriorPower.ιMulti S 2 ![m, m']) := by
      rw [GlobalTheory.exteriorPowerMapOver_ιMulti]
      congr 1
      funext k
      fin_cases k <;> rfl
    have h2 : hE.equiv.symm (GlobalTheory.exteriorPowerMapOver R 2 φ (exteriorPower.ιMulti S 2 ![m, m'])) =
        1 ⊗ₜ exteriorPower.ιMulti S 2 ![m, m'] := by
      rw [LinearEquiv.symm_apply_eq, IsBaseChange.equiv_tmul, one_smul]
    rw [h1]
    change hψ.equiv (eM.baseChange S R _ _ (hE.equiv.symm _)) = _
    rw [h2, LinearEquiv.baseChange_tmul, IsBaseChange.equiv_tmul, one_smul, heM, hc]
  let iw := exteriorPower.ιMulti R 2 (M := N)
  have u0 : ∀ a b x : N, (![x, b] : Fin 2 → N) = Function.update ![a, b] 0 x := by
    intro a b x; funext k; fin_cases k <;> simp
  have u1 : ∀ a b x : N, (![a, x] : Fin 2 → N) = Function.update ![a, b] 1 x := by
    intro a b x; funext k; fin_cases k <;> simp
  have add0 : ∀ a a' b : N, iw ![a + a', b] = iw ![a, b] + iw ![a', b] := by
    intro a a' b
    have := iw.map_update_add ![a, b] 0 a a'
    rwa [← u0 a b (a + a'), ← u0 a b a, ← u0 a b a'] at this
  have add1 : ∀ a b b' : N, iw ![a, b + b'] = iw ![a, b] + iw ![a, b'] := by
    intro a b b'
    have := iw.map_update_add ![a, b] 1 b b'
    rwa [← u1 a b (b + b'), ← u1 a b b, ← u1 a b b'] at this
  have smul0 : ∀ (r : R) (a b : N), iw ![r • a, b] = r • iw ![a, b] := by
    intro r a b
    have := iw.map_update_smul ![a, b] 0 r a
    rwa [← u0 a b (r • a), ← u0 a b a] at this
  have smul1 : ∀ (r : R) (a b : N), iw ![a, r • b] = r • iw ![a, b] := by
    intro r a b
    have := iw.map_update_smul ![a, b] 1 r b
    rwa [← u1 a b (r • b), ← u1 a b b] at this
  have zero0 : ∀ b : N, iw ![0, b] = 0 := fun b => by
    simpa using smul0 0 0 b
  have zero1 : ∀ a : N, iw ![a, 0] = 0 := fun a => by
    simpa using smul1 0 a 0
  intro a b
  induction a using hφ.inductionOn with
  | add x y hx hy => simp only [iw] at add0; rw [add0, map_add (f := _), hx, hy, map_add (f := _), LinearMap.add_apply]
  | smul r x hx => simp only [iw] at smul0; rw [smul0, map_smul, hx, map_smul, LinearMap.smul_apply]
  | tmul m =>
    induction b using hφ.inductionOn with
    | add x y hx hy => simp only [iw] at add1; rw [add1, map_add (f := _), hx, hy, map_add (f := _)]
    | smul r x hx => simp only [iw] at smul1; rw [smul1, map_smul, hx, map_smul]
    | tmul m' => exact key m m'

theorem tensor_equiv_of_tower {S R R' M N P : Type} [CommRing S] [CommRing R] [CommRing R'] [Algebra S R]
    [Algebra R R'] [Algebra S R'] [IsScalarTower S R R'] [AddCommGroup M] [Module S M] [AddCommGroup N]
    [Module R N] [AddCommGroup P] [Module R' P]
    (φ : M →ₛₗ[algebraMap S R] N) (χ : N →ₛₗ[algebraMap R R'] P) (θ : M →ₛₗ[algebraMap S R'] P)
    (hθ : ∀ m, χ (φ m) = θ m) (e1 : R ⊗[S] M ≃ₗ[R] N) (he1 : ∀ m, e1 (1 ⊗ₜ m) = φ m)
    (e2 : R' ⊗[S] M ≃ₗ[R'] P) (he2 : ∀ m, e2 (1 ⊗ₜ m) = θ m) :
    ∃ e : R' ⊗[R] N ≃ₗ[R'] P, ∀ c, e (1 ⊗ₜ c) = χ c := by
  refine ⟨(e1.symm.baseChange R R' _ _) ≪≫ₗ AlgebraTensorModule.cancelBaseChange S R R' R' M ≪≫ₗ e2,
    fun c => ?_⟩
  obtain ⟨x, rfl⟩ := e1.surjective c
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r m =>
    have h1 : e1 (r ⊗ₜ m) = r • φ m := by
      rw [← he1, ← e1.map_smul, smul_tmul', smul_eq_mul, _root_.mul_one]
    have h2 : (algebraMap R R' r) ⊗ₜ[S] m = (algebraMap R R' r) • ((1 : R') ⊗ₜ[S] m) := by
      rw [smul_tmul', smul_eq_mul, _root_.mul_one]
    simp only [LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul, LinearEquiv.symm_apply_apply,
      AlgebraTensorModule.cancelBaseChange_tmul]
    rw [Algebra.smul_def, _root_.mul_one, h2, e2.map_smul, he2, h1, χ.map_smulₛₗ, hθ]
  | add x y hx hy => simp only [tmul_add, map_add (f := _), hx, hy]

theorem oStr_of_noetherian : OStr := by
  intro R _ A _ g hA hg
  obtain ⟨S, B, _, φ, -, hfg, hB, hBg, hpb⟩ :=
    GlobalTheory.AbelianLimit.abelianScheme_descends_to_fg_subring R g A ∅ hA hg
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℤ S
  obtain ⟨hFP, hW, hBC1, hBC2⟩ := GlobalTheory.T.abelianScheme_structureSheafCohomology_noetherian S B g hB hBg
  have hAB : IsPullback φ A.hom B.hom (spMap (algebraMap S R)) := hpb.1
  obtain ⟨e1, he1⟩ := hBC1 R A.left A.hom φ hAB
  obtain ⟨e2, he2⟩ := hBC2 R A.left A.hom φ hAB
  have hp1 : IsBaseChange R (semiToLin (pullHO1 hAB.w)) := IsBaseChange.of_equiv e1 he1
  have hp2 : IsBaseChange R (semiToLin (pullHO2 hAB.w)) := IsBaseChange.of_equiv e2 he2
  have hcomp := GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id
  refine ⟨fp_of_tensor_equiv e1 hFP, ?_, ?_, ?_⟩
  · obtain ⟨eM, heM⟩ := hW
    exact wedge_of_isBaseChange hp1 hp2 (cup _) (cup _)
      ((hcomp.2.1 S R B.left A.left B.hom A.hom (algebraMap S R) φ hAB.w).1) eM heM
  · intro R' _ _ X' s' ψ h
    letI : Algebra S R' := ((algebraMap R R').comp (algebraMap S R)).toAlgebra
    haveI : IsScalarTower S R R' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have es : spMap (algebraMap R R') ≫ spMap (algebraMap S R) = spMap (algebraMap S R') := by
      simp only [spMap, ← Spec.map_comp]; rfl
    have hc : IsPullback (ψ ≫ φ) s' B.hom (spMap (algebraMap S R')) := es ▸ h.paste_horiz hAB
    obtain ⟨e3, he3⟩ := hBC1 R' X' s' (ψ ≫ φ) hc
    exact tensor_equiv_of_tower (pullHO1 hAB.w) (pullHO1 h.w) (pullHO1 hc.w)
      ((hcomp.1 S R B.left A.left B.hom A.hom (algebraMap S R) φ hAB.w R' X' s' (algebraMap R R') ψ h.w
        (algebraMap S R') (ψ ≫ φ) hc.w rfl (fun _ => rfl)).1) e1 he1 e3 he3
  · intro R' _ _ X' s' ψ h
    letI : Algebra S R' := ((algebraMap R R').comp (algebraMap S R)).toAlgebra
    haveI : IsScalarTower S R R' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have es : spMap (algebraMap R R') ≫ spMap (algebraMap S R) = spMap (algebraMap S R') := by
      simp only [spMap, ← Spec.map_comp]; rfl
    have hc : IsPullback (ψ ≫ φ) s' B.hom (spMap (algebraMap S R')) := es ▸ h.paste_horiz hAB
    obtain ⟨e3, he3⟩ := hBC2 R' X' s' (ψ ≫ φ) hc
    exact tensor_equiv_of_tower (pullHO2 hAB.w) (pullHO2 h.w) (pullHO2 hc.w)
      ((hcomp.1 S R B.left A.left B.hom A.hom (algebraMap S R) φ hAB.w R' X' s' (algebraMap R R') ψ h.w
        (algebraMap S R') (ψ ≫ φ) hc.w rfl (fun _ => rfl)).2.1) e2 he2 e3 he3

end GlobalTheory.AbCoh
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.GalLift.overK_iff_good_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → ∀ (fw : FWTie T R κw v₀) (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), OverK σ ↔ GoodEmb T.Q.c (res T σ) :=
  GlobalTheory.GalLift.overK_iff_good_ofFive

theorem GlobalTheory.EtaValues.etaVals_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), EtaVals R := by
  classical
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR _ P e he x hx
  have htie := hR.fam.tie
  obtain ⟨_, _, _, hT⟩ := htie
  have hok := hT.ok A.μ0
  have h := GlobalTheory.EtaValues.hv_mem_host D R.C.eta R.C.isEta (R.Sb ∪ R.Q A.μ0) (fun v hs => by
    rw [Finset.coe_union] at hs
    obtain ⟨Q, rfl⟩ := hR.fam.pl_onto v (GlobalTheory.EtaValues.splitOff_mono hs Set.subset_union_left)
    exact ⟨_, (hR.fam.etaVal Q ((hok Q).2 hs)).trans (GlobalTheory.EtaValues.valTw_eq _ _)⟩) P
  obtain ⟨y, hy⟩ := h
  refine ⟨y, hy.trans ?_⟩
  rw [hR.lev.eta.2 P e he _ x hx]
  simp [GlobalTheory.EtaValues.hv, Formalism.L2.Host.HChar.val, Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem GlobalTheory.EtaConjExist.exists_isEtaConj_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), EtaVals R → ∀ (σ : D.what₂.LL →+* ℂ), OverK σ → ∃ η', IsEtaConj σ R.eta η' := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR _ hV σ hσ
  refine GlobalTheory.EtaConjExist.exists_conj R.eta R.C.eta hR.lev.eta R.C.isEta (fun P => ?_) σ hσ
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
  obtain ⟨y, hy⟩ := hV P e he (Formalism.L2.JoinChr.locU he.1 (Formalism.L2.Host.unif P)) rfl
  refine ⟨y, hy.trans ?_⟩
  rw [hR.lev.eta.2 P e he _ (Formalism.L2.JoinChr.locU he.1 (Formalism.L2.Host.unif P)) rfl]
  simp [Formalism.L2.Host.HChar.val, Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem GlobalTheory.EtaConjType.resEta_hasInfExp_of_isEtaConj_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), OverK σ → ∀ η', IsEtaConj σ R.eta η' → ResEta D η' 1 ∧ ∀ ρ, HasInfExp D η' ρ (1 / 2) :=
  GlobalTheory.EtaConjType.resEta_hasInfExp_of_isEtaConj_ofFive

theorem GlobalTheory.GalLift.hypConj_of_chars_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), Function.Bijective (lab (D := D) σ) → (∀ ρ, labE σ (lab σ ρ) = tauE D ρ) → logHookSum i (lab σ) = logHookSum i id ∧ ∀ (μ' η' : (AE D)ˣ →* Circle), ChiAt R i σ μ' → IsEtaConj σ R.eta η' → ResEta D η' 1 → (∀ ρ, HasInfExp D η' ρ (1 / 2)) → HypConj R i σ μ' η' :=
  GlobalTheory.GalLift.hypConj_of_chars_ofFive

theorem GlobalTheory.ConjCharUnique.conjChar_unique_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), (∀ μ' μ'', ChiAt R i σ μ' → ChiAt R i σ μ'' → μ' = μ'') ∧ ∀ η' η'', IsEtaConj σ R.eta η' → IsEtaConj σ R.eta η'' → η' = η'' :=
  GlobalTheory.ConjCharUnique.conjChar_unique_ofFive

theorem GlobalTheory.GalLift.ConjWeil.exists_conj_weil_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ) (μ' η' : (AE D)ˣ →* Circle), ChiAt R i σ μ' → IsEtaConj σ R.eta η' → HypConj R i σ μ' η' → ∃ ω, IsWeilDatumO R.ψ (Vc D i) (Wc D i) μ' (μ' * η'⁻¹) ω := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i σ μ' η' hμ hη hH
  have hV : (Vc D i).rank = D.R.nV := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have hW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  exact GlobalTheory.GalLift.ConjWeil.exists_of_datum (hR.thP.ωP i A.μ0) hμ.1 (GlobalTheory.GalLift.ConjWeil.hecke_mul_inv hμ.1 hη.1)
    (resEta_parity hH.mu_res ((GlobalTheory.GalLift.ConjWeil.even_im_hermitian_sub D.R).1.trans (congrArg (· % 2) hV.symm)))
    (resEta_parity (resEta_mul hH.mu_res (resEta_inv hH.eta_res))
      ((GlobalTheory.GalLift.ConjWeil.even_im_hermitian_sub D.R).2.trans (congrArg (· % 2) hW.symm)))

theorem GlobalTheory.GalLift.reading_base_injective_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → ∀ (fw : FWTie T R κw v₀) (i : Fin D.R.m), fw.Evaluates → EvInj T R v₀ → JUnif T R κw v₀ → Function.Injective ((R.FW i).j (sg0 D A)) := by
  intro D G _ _ Pl0 T0 A T _ R F κw v₀ _ fw i hev hinj hu
  have hg : GoodEmb T.Q.c (res T (sg0 D A)) := base_embedding_good T R fw.alg_eq fw.laws.pins.2.2.1
  have hV : T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i := fw.laws.spaceW _ (inR i) _ hg
  have h1 := fw.jK_eq hev hinj hg hV
  have h2 : ∀ f, fw.jK i (sg0 D A) f = (1 : ℂ) • jTop T R κw v₀ i (sg0 D A) f := fun f =>
    (LinearMap.congr_fun h1 f).trans (one_smul ℂ _).symm
  have h3 := GlobalTheory.TiedUnif.indep_span (C := Cu T κw i) (R.FW i) (fw.ks i) (fw.e i) (sg0 D A) one_ne_zero h2
    (hu i _).1 (hu i _).2
  exact GlobalTheory.TiedUnif.injective_of_indep (W := fun σ => (R.HW i σ).H) _ h3.1

theorem GlobalTheory.GalLift.conjChars_five : (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → ∀ (fw : FWTie T R κw v₀) (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), OverK σ ↔ GoodEmb T.Q.c (res T σ)) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), EtaVals R) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), EtaVals R → ∀ (σ : D.what₂.LL →+* ℂ), OverK σ → ∃ η', IsEtaConj σ R.eta η') ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), OverK σ → ∀ η', IsEtaConj σ R.eta η' → ResEta D η' 1 ∧ ∀ ρ, HasInfExp D η' ρ (1 / 2)) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), Function.Bijective (lab (D := D) σ) → (∀ ρ, labE σ (lab σ ρ) = tauE D ρ) → logHookSum i (lab σ) = logHookSum i id ∧ ∀ (μ' η' : (AE D)ˣ →* Circle), ChiAt R i σ μ' → IsEtaConj σ R.eta η' → ResEta D η' 1 → (∀ ρ, HasInfExp D η' ρ (1 / 2)) → HypConj R i σ μ' η') ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), (∀ μ' μ'', ChiAt R i σ μ' → ChiAt R i σ μ'' → μ' = μ'') ∧ ∀ η' η'', IsEtaConj σ R.eta η' → IsEtaConj σ R.eta η'' → η' = η'') ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ) (μ' η' : (AE D)ˣ →* Circle), ChiAt R i σ μ' → IsEtaConj σ R.eta η' → HypConj R i σ μ' η' → ∃ ω, IsWeilDatumO R.ψ (Vc D i) (Wc D i) μ' (μ' * η'⁻¹) ω) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → ∀ (fw : FWTie T R κw v₀) (i : Fin D.R.m), fw.Evaluates → EvInj T R v₀ → JUnif T R κw v₀ → Function.Injective ((R.FW i).j (sg0 D A))) :=
  ⟨GlobalTheory.GalLift.overK_iff_good_five, GlobalTheory.EtaValues.etaVals_five, GlobalTheory.EtaConjExist.exists_isEtaConj_five,
    GlobalTheory.EtaConjType.resEta_hasInfExp_of_isEtaConj_five, GlobalTheory.GalLift.hypConj_of_chars_five,
    GlobalTheory.ConjCharUnique.conjChar_unique_five, GlobalTheory.GalLift.ConjWeil.exists_conj_weil_five,
    GlobalTheory.GalLift.reading_base_injective_five⟩

end
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open GlobalTheory.RunJoin

namespace GlobalTheory.ShareOn

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem archOne_congr {X X' : Data E r} (hX : X = X') {L Fp : Wt X.Ψ r} {L' Fp' : Wt X'.Ψ r} {T : ℕ}
    (hL : ∀ τ (h1 : τ ∈ X.Ψ) (h2 : τ ∈ X'.Ψ) a, L ⟨τ, h1⟩ a = L' ⟨τ, h2⟩ a)
    (hF : ∀ τ (h1 : τ ∈ X.Ψ) (h2 : τ ∈ X'.Ψ) a, Fp ⟨τ, h1⟩ a = Fp' ⟨τ, h2⟩ a) (h : ArchOne X' L' Fp' T) :
    ArchOne X L Fp T := by
  subst hX
  have e1 : L = L' := funext fun τ => funext fun a => hL τ.1 τ.2 τ.2 a
  have e2 : Fp = Fp' := funext fun τ => funext fun a => hF τ.1 τ.2 τ.2 a
  subst e1 e2
  exact h

theorem archOn_of_comps {U C K : Type} [Group U] [MulAction U C] [Nonempty C] (M : TwoLevels E r U C) (ka : Wt M.Ψ r)
    (X : K → Data E r) (e : C ≃ K) (hX : ∀ c, (M.comp c).toData = X (e c)) (lK lL lF : ∀ k, Wt (X k).Ψ r) (T n : ℕ)
    (hn : n = M.dimY)
    (hka : ∀ c τ (h1 : τ ∈ M.Ψ) (h2 : τ ∈ (X (e c)).Ψ) a, ka ⟨τ, h1⟩ a = lK (e c) ⟨τ, h2⟩ a)
    (hsum : ∀ k, lK k = lF k + T • lL k)
    (hLi : ∀ k k' τ (h : τ ∈ (X k).Ψ) (h' : τ ∈ (X k').Ψ) a, lL k ⟨τ, h⟩ a = lL k' ⟨τ, h'⟩ a)
    (hFi : ∀ k k' τ (h : τ ∈ (X k).Ψ) (h' : τ ∈ (X k').Ψ) a, lF k ⟨τ, h⟩ a = lF k' ⟨τ, h'⟩ a)
    (hW : ∀ k, GapsGe (X k).p0 (lL k) 1 ∧ PairGe (lL k) (1.9 * T) ∧
      GapsGe (X k).p0 (lF k - kLog (X k).Ψ r - (n + 2) • lL k) 0 ∧ PairGe (lF k - kLog (X k).Ψ r - (n + 2) • lL k) 1)
    (hA : ∀ k, ArchOne (X k) (lL k) (lF k) T) : ArchOn M ka T := by
  obtain ⟨c0⟩ := ‹Nonempty C›
  have hΨ : ∀ c, (X (e c)).Ψ = M.Ψ := fun c => (congrArg Data.Ψ (hX c)).symm.trans (M.comp_Ψ c)
  have hp : ∀ c, (X (e c)).p0 = M.p0 := fun c => (congrArg Data.p0 (hX c)).symm.trans (M.comp_basePoint c)
  have mem : ∀ c τ, τ ∈ M.Ψ → τ ∈ (X (e c)).Ψ := fun c τ h => (hΨ c).symm ▸ h
  let L : Wt M.Ψ r := fun τ a => lL (e c0) ⟨τ.1, mem c0 τ.1 τ.2⟩ a
  let Fp : Wt M.Ψ r := fun τ a => lF (e c0) ⟨τ.1, mem c0 τ.1 τ.2⟩ a
  have hW0 := hW (e c0)
  rw [hp c0, hn] at hW0
  obtain ⟨w1, w2, w3, w4⟩ := hW0
  refine ⟨L, Fp, ?_, fun τ a b h1 h2 => w1 ⟨τ.1, mem c0 τ.1 τ.2⟩ a b h1 h2,
    fun τ a b h1 h2 => w2 ⟨τ.1, mem c0 τ.1 τ.2⟩ a b h1 h2, fun τ a b h1 h2 => w3 ⟨τ.1, mem c0 τ.1 τ.2⟩ a b h1 h2,
    fun τ a b h1 h2 => w4 ⟨τ.1, mem c0 τ.1 τ.2⟩ a b h1 h2, fun c => ?_⟩
  · funext τ a
    rw [hka c0 τ.1 τ.2 (mem c0 τ.1 τ.2) a, hsum]
    rfl
  · refine archOne_congr (hX c) (fun τ h1 h2 a => ?_) (fun τ h1 h2 a => ?_) (hA (e c))
    · exact hLi (e c0) (e c) τ _ h2 a
    · exact hFi (e c0) (e c) τ _ h2 a

end Model

section Run

theorem row_pair {r p q : ℕ} (hpq : p + q = r) (Dm nL nF : ℤ) (hnF : 0 ≤ nF)
    (LP LM FP FM : ℕ → ℤ) (L F : Fin r → ℤ)
    (hL : ∀ a : Fin r, L a = if q ≤ (a : ℕ) then LP (a - q) + nL else -LM (q - 1 - a) - nL)
    (hF : ∀ a : Fin r, F a = if q ≤ (a : ℕ) then FP (a - q) + nF else -FM (q - 1 - a) - nF)
    (p4 : (Dm + 2) * LP (p - 1) + ((Dm + 2) * (2 * nL) + 2 * r) ≤ FP (p - 1))
    (m4 : (Dm + 2) * LM (q - 1) + 0 ≤ FM (q - 1)) (a b : Fin r) (ha : (a : ℕ) = 0) (hb : (b : ℕ) = r - 1)
    (hp : 0 < p) (hq : 0 < q) :
    1 ≤ (F b - (2 * (b : ℤ) - ((r : ℤ) - 1)) - (Dm + 2) * L b) -
      (F a - (2 * (a : ℤ) - ((r : ℤ) - 1)) - (Dm + 2) * L a) := by
  have hq1 : q ≤ (b : ℕ) := by omega
  have hq2 : ¬ q ≤ (a : ℕ) := by omega
  have e1 : (a : ℤ) = 0 := by omega
  have e2 : (b : ℤ) = r - 1 := by omega
  have e3 : (r : ℤ) = p + q := by omega
  rw [hL a, hL b, hF a, hF b, e1, e2]
  simp only [if_pos hq1, if_neg hq2]
  rw [show (b : ℕ) - q = p - 1 by omega, show q - 1 - (a : ℕ) = q - 1 by omega]
  nlinarith

theorem expand_weight {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Ψ : Finset (E →+* ℂ)} (F L : Wt Ψ r)
    (n : ℕ) (τ : Ψ) (c : Fin r) :
    (F - kLog Ψ r - (n + 2) • L) τ c = F τ c - (2 * (c : ℤ) - ((r : ℤ) - 1)) - ((n : ℤ) + 2) * L τ c := by
  show F τ c - kLog Ψ r τ c - ((n + 2) • L τ c) = _
  rw [nsmul_eq_mul]
  simp only [kLog]
  push_cast
  ring



theorem run_weight_arch (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp)
    (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ)
    (hP : FamilyHypotheses.HypPage large₂ (recPJ h j hj) H C2 A2 CR CT ka wL wF Tn nP nW h0) (hjm : j < D.R.m)
    (k : (T.U j T.σ₀).Comp) :
    GapsGe ((T.U j T.σ₀).X k).p0 (laR T j wL k) 1 ∧ PairGe (laR T j wL k) (1.9 * Tn) ∧
      GapsGe ((T.U j T.σ₀).X k).p0
        (laR T j wF k - kLog ((T.U j T.σ₀).X k).Ψ D.R.r - (WeightFamilies.dimY D j + 2) • laR T j wL k) 0 ∧
      PairGe (laR T j wF k - kLog ((T.U j T.σ₀).X k).Ψ D.R.r - (WeightFamilies.dimY D j + 2) • laR T j wL k) 1 := by
  obtain ⟨-, hS, -, -, -⟩ := hP
  obtain ⟨-, g1, g2, h4, -, h6, h7, -, -, -, -, -, -, -, hL, hF, -, -, -, h40, h21, -⟩ := hS
  obtain ⟨-, -, -, -, -, hp0, -, tt, hla⟩ := GlobalTheory.Shares.WtDic.weights_dictionary D T h j hj k
  have hk := D.R.m_add_three_le_k
  have hj1 := hj.1
  have hp : 0 < (D.R.sigW j).1 := by show 0 < D.R.k + j - 1; omega
  have hq : 0 < (D.R.sigW j).2 := by show 0 < D.R.m - j; omega
  have hpq : (D.R.sigW j).1 + (D.R.sigW j).2 = D.R.r := by
    show D.R.k + j - 1 + (D.R.m - j) = D.R.k + D.R.m - 1; omega
  have hTp : ((Tp D j Tn : ℕ) : ℤ) = (Tn : ℤ) + (WeightFamilies.dimY D j : ℤ) + 2 := by unfold Tp; push_cast; ring
  have h40' : 40 * ((WeightFamilies.dimY D j : ℤ) + 2) ≤ Tn := by exact_mod_cast h40
  have h21' : ((WeightFamilies.dimY D j : ℤ) + 2) * nW + 2 * D.R.r ≤ Tn := by exact_mod_cast h21
  have hn : (nW : ℤ) = 2 * ((wL.n / 2 : ℕ) : ℤ) := by
    have := hL.1
    obtain ⟨c, hc⟩ := wL.n_even
    omega
  have key := fun τ : ((T.U j T.σ₀).X k).Ψ => by
    have bP := GlobalTheory.RunWeightDom.block hp (ka.aP (tt τ)) (wL.aP (tt τ)) (wF.aP (tt τ)) Tn (WeightFamilies.dimY D j) D.R.r
      (((WeightFamilies.dimY D j : ℤ) + 2) * nW + 2 * D.R.r) (Int.natCast_nonneg _) (Int.natCast_nonneg _) h40' h21'
      (fun i hi => by have := g1 (tt τ) i hi; push_cast at this; rwa [hTp] at this)
      (fun i hi => by
        have h1 : 2 * (Tn : ℝ) ^ 2 ≤ (ka.aP (tt τ) i : ℝ) := by have := h6 (tt τ) i hi; linarith
        exact_mod_cast h1)
      (fun i => by have := hL.2.1 (tt τ) i; rwa [hTp, sub_sub] at this) (hF.2.1 (tt τ))
    have bM := GlobalTheory.RunWeightDom.block hq (ka.aM (tt τ)) (wL.aM (tt τ)) (wF.aM (tt τ)) Tn (WeightFamilies.dimY D j) D.R.r
      0 (Int.natCast_nonneg _) (Int.natCast_nonneg _) h40' (Int.natCast_nonneg _)
      (fun i hi => by have := g2 (tt τ) i hi; push_cast at this; rwa [hTp] at this)
      (fun i hi => by
        have h1 : 2 * (Tn : ℝ) ^ 2 ≤ (ka.aM (tt τ) i : ℝ) := by have := h7 (tt τ) i hi; linarith
        exact_mod_cast h1)
      (fun i => by have := hL.2.2 (tt τ) i; rwa [hTp, ← sub_zero (ka.aM (tt τ) i : ℤ)] at this) (hF.2.2 (tt τ))
    rw [hn] at bP
    exact And.intro (GlobalTheory.RunWeightDom.row hpq Tn (WeightFamilies.dimY D j) ((wL.n / 2 : ℕ) : ℤ) ((wF.n / 2 : ℕ) : ℤ)
      (Int.natCast_nonneg _) (Int.natCast_nonneg _) _ _ _ _ (laR T j wL k τ) (laR T j wF k τ) (Int.natCast_nonneg _)
      (fun a => by rw [hla, hp0]) (fun a => by rw [hla, hp0]) bP.1 bP.2.1 bP.2.2.1 bP.2.2.2
      bM.1 bM.2.1 bM.2.2.1 bM.2.2.2)
      (row_pair hpq (WeightFamilies.dimY D j) ((wL.n / 2 : ℕ) : ℤ) ((wF.n / 2 : ℕ) : ℤ) (Int.natCast_nonneg _)
        (fun i => (ext0 (wL.aP (tt τ)) i : ℤ)) (fun i => (ext0 (wL.aM (tt τ)) i : ℤ))
        (fun i => (ext0 (wF.aP (tt τ)) i : ℤ)) (fun i => (ext0 (wF.aM (tt τ)) i : ℤ))
        (laR T j wL k τ) (laR T j wF k τ) (fun a => by rw [hla, hp0]) (fun a => by rw [hla, hp0]) bP.2.2.2 bM.2.2.2)
  rw [← hp0] at key hq
  have hq' : ((T.U j T.σ₀).X k).p0 < D.R.r := by omega
  have e : ∀ (τ : ((T.U j T.σ₀).X k).Ψ) (c : Fin D.R.r),
      (laR T j wF k - kLog ((T.U j T.σ₀).X k).Ψ D.R.r - (WeightFamilies.dimY D j + 2) • laR T j wL k) τ c =
        laR T j wF k τ c - (2 * (c : ℤ) - ((D.R.r : ℤ) - 1)) - ((WeightFamilies.dimY D j : ℤ) + 2) * laR T j wL k τ c := by
    intro τ c
    exact expand_weight _ _ _ τ c
  refine ⟨fun τ a b hab hb => ?_, fun τ a b ha hb => ?_, fun τ a b hab hb => ?_, fun τ a b ha hb => ?_⟩
  · obtain ⟨⟨k1, k2, -, -, -⟩, -⟩ := key τ
    have hab' : (a : ℕ) < b := by omega
    by_cases hc : (b : ℕ) < ((T.U j T.σ₀).X k).p0
    · have := k1 a b hab' hc; omega
    · have := k2 a b (by omega) hab'; omega
  · obtain ⟨⟨-, -, -, k4, -⟩, -⟩ := key τ
    have := k4 a b (by omega) (by omega)
    have h' : (19 : ℝ) * Tn ≤ 10 * ((laR T j wL k τ b - laR T j wL k τ a : ℤ) : ℝ) := by exact_mod_cast this
    linarith
  · obtain ⟨⟨-, -, k3, -, -⟩, -⟩ := key τ
    have := k3 a b hab hb
    rw [e τ a, e τ b]
    linarith
  · obtain ⟨-, k5⟩ := key τ
    have := k5 a b ha hb hp hq
    rw [e τ a, e τ b]
    have h1 : (1 : ℤ) ≤ (laR T j wF k τ b - (2 * (b : ℤ) - ((D.R.r : ℤ) - 1)) - ((WeightFamilies.dimY D j : ℤ) + 2) * laR T j wL k τ b) -
      (laR T j wF k τ a - (2 * (a : ℤ) - ((D.R.r : ℤ) - 1)) - ((WeightFamilies.dimY D j : ℤ) + 2) * laR T j wL k τ a) := this
    exact_mod_cast h1

theorem archOne_of_run (D : D7) (T : Top D) (h : LawsP T) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D)
    (p j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ)
    (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ)
    (hpar : ParOK T EX p j) (hpg : PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0)
    (hC : HypC large₂ (recPJ h j hj) H C2 A2 7 0 CT (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) ka wL wF Tn nP nW h0 nus)
    (hjm : j < D.R.m) :
    ∀ k : (T.U j T.σ₀).Comp, ArchOne ((T.U j T.σ₀).X k) (GlobalTheory.Shares.laR T j wL k) (GlobalTheory.Shares.laR T j wF k) Tn := by
  obtain ⟨G, hG⟩ := GlobalTheory.RunJoin.exists_genOK D T h hinj EX p j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hpar.orient hpg
  obtain ⟨i, et, he⟩ := GlobalTheory.EtaBoundForm.exists_etaOK D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hpg hjm
  let G' := FamilyHypotheses.refill G G.del G.th' G.rz G.alz G.th0 G.zc G.rq G.th i et
  have hG' : GenOK h j hj large₂ G' _ _ := genOK_refill h j hj large₂ G _ _ hG G.del G.th' G.rz G.alz G.th0 G.zc G.rq G.th i et
  obtain ⟨A⟩ := GlobalTheory.RunJoin.archAt_of_run D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 EX p _ nus hpar hpg hC hjm G' hG' he
  obtain ⟨t, -, ⟨Fl⟩⟩ := GlobalTheory.GenericFlat.exists_generic_flatAt D T h j hj _ wL wF G'.w Tn _ A
  intro k
  exact ⟨A.Xa k, A.hL k, A.hF k, A.hT k, A.mar k, ⟨Fl.Fl k⟩⟩

end Run

section Point

open Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar


end Point

end GlobalTheory.ShareOn

end
end

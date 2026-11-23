module

public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GoodIdempotentBadPlaces
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.RatDatOfReal
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.InfPartOfSplitIdem
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle311
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentSumSelfDualFramesBound
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle227
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle550
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle030
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle548
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatA
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle020
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
namespace GlobalTheory.ZRepBlock

theorem zrep_block : ∀ (D : D7) (S T : HSp D) {m k : ℕ} (Λ Λ' : AddSubgroup (WO S T)) (e : AE D) (Q : Finset (Pl D.host.E)) (fm : WO S T → Matrix (Fin m) (Fin k) (EAf D)), (∀ w w', fm (w - w') = fm w - fm w') → (∀ w, IsHalf e w → (w ∈ Λ ↔ IsIntM (fm w))) → (∀ w ∈ Λ, ∀ w' ∈ Λ, IsHalf e w → IsHalf e w' → (w - w' ∈ Λ' ↔ ∀ PP ∈ Q, redM PP (fm w) = redM PP (fm w'))) → (∀ Y : ∀ PP : Pl D.host.E, Matrix (Fin m) (Fin k) (kP PP), ∃ w, IsHalf e w ∧ IsIntM (fm w) ∧ ∀ PP ∈ Q, redM PP (fm w) = Y PP) → ∃ X : Finset (WO S T), (∀ x ∈ X, x ∈ Λ ∧ IsHalf e x) ∧ (∀ w ∈ Λ, IsHalf e w → ∃! x, x ∈ X ∧ w - x ∈ Λ') ∧ X.card = (∏ PP ∈ Q, Nat.card (kP PP)) ^ (m * k) ∧ (∀ Y : ∀ PP : Pl D.host.E, Matrix (Fin m) (Fin k) (kP PP), ∃! x, x ∈ X ∧ ∀ PP ∈ Q, redM PP (fm x) = Y PP) := by
  intro D S T m k Λ Λ' e Q fm _hsub H1 H2 H3
  classical

  let Ix := ∀ PP : Q, Matrix (Fin m) (Fin k) (kP (PP : Pl D.host.E))
  haveI : ∀ PP : Pl D.host.E, Fintype (kP PP) := fun PP => Fintype.ofFinite _
  let ext : Ix → ∀ PP : Pl D.host.E, Matrix (Fin m) (Fin k) (kP PP) :=
    fun Y PP => if h : PP ∈ Q then Y ⟨PP, h⟩ else 0
  choose w hwh hwi hwr using H3
  let g : Ix → WO S T := fun Y => w (ext Y)
  have hgr : ∀ Y : Ix, ∀ PP (h : PP ∈ Q), redM PP (fm (g Y)) = Y ⟨PP, h⟩ := by
    intro Y PP h
    have := hwr (ext Y) PP h
    simpa [g, ext, h] using this
  have hginj : Function.Injective g := by
    intro Y Y' hYY
    funext PP
    rw [← hgr Y PP.1 PP.2, ← hgr Y' PP.1 PP.2, hYY]
  have hgΛ : ∀ Y, g Y ∈ Λ ∧ IsHalf e (g Y) :=
    fun Y => ⟨(H1 _ (hwh _)).2 (hwi _), hwh _⟩
  refine ⟨Finset.univ.image g, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨Y, -, rfl⟩ := Finset.mem_image.1 hx
    exact hgΛ Y
  · intro v hv hvh
    let Y : Ix := fun PP => redM (PP : Pl D.host.E) (fm v)
    refine ⟨g Y, ⟨Finset.mem_image.2 ⟨Y, Finset.mem_univ _, rfl⟩, ?_⟩, ?_⟩
    · refine (H2 v hv (g Y) (hgΛ Y).1 hvh (hgΛ Y).2).2 ?_
      intro PP h
      rw [hgr Y PP h]
    · rintro x ⟨hx, hvx⟩
      obtain ⟨Y', -, rfl⟩ := Finset.mem_image.1 hx
      congr 1
      funext PP
      have h1 := (H2 v hv (g Y') (hgΛ Y').1 hvh (hgΛ Y').2).1 hvx PP.1 PP.2
      rw [hgr Y' PP.1 PP.2] at h1
      exact h1.symm
  · rw [Finset.card_image_of_injective _ hginj, Finset.card_univ, Fintype.card_pi]
    calc ∏ i : Q, Fintype.card (Fin m → Fin k → kP (i : Pl D.host.E))
        = ∏ i : Q, Nat.card (kP (i : Pl D.host.E)) ^ (m * k) := by
          refine Finset.prod_congr rfl (fun i _ => ?_)
          simp only [Fintype.card_fun, Fintype.card_fin, Nat.card_eq_fintype_card]
          ring
      _ = (∏ PP ∈ Q, Nat.card (kP PP)) ^ (m * k) := by
          rw [Finset.prod_pow, Finset.prod_coe_sort Q (fun PP => Nat.card (kP PP))]
  · intro Y
    let Y' : Ix := fun PP => Y PP
    refine ⟨g Y', ⟨Finset.mem_image.2 ⟨Y', Finset.mem_univ _, rfl⟩, fun PP h => hgr Y' PP h⟩, ?_⟩
    rintro x ⟨hx, hxr⟩
    obtain ⟨Y'', -, rfl⟩ := Finset.mem_image.1 hx
    congr 1
    funext PP
    rw [← hgr Y'' PP.1 PP.2, hxr PP.1 PP.2]

end GlobalTheory.ZRepBlock
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms NumberField Polynomial Formalism.IndefR.NX
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.GoodSS.Idem

def rhoTw {D : D7} (S : RatDat D.ntw) (j : ℕ) : G0g D.nd →* Module.End D.what₂.LL (S.WL j) where
  toFun g := ((((S.A j).chi (S.eG.symm g))⁻¹ : D.what₂.LLˣ) : D.what₂.LL) • (S.A j).ρ (S.eG.symm g)
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul, mul_inv, Units.val_mul]
    rw [smul_mul_smul_comm]

theorem goodProjW_idem : ∀ (D : D7) (S : RatDat D.ntw) (j : ℕ), D.ntw.Tw →
    goodProjW S j D.nexp.eLL0 * goodProjW S j D.nexp.eLL0 = goodProjW S j D.nexp.eLL0 := by
  intro D S j i
  set s := (D.nexp.eAlg i true).coeff.support with hs
  have hsupp : ∀ g, g ∉ s → D.nexp.eLL0 g = 0 := fun g hg => by
    have h0 : (D.nexp.eAlg i true).coeff g = 0 := Finsupp.notMem_support_iff.1 hg
    have hcoef : (D.nexp.eAlg i true).coeff g = readLL0 S i true (D.nexp.eLL0 g) := by
      rw [D.nexp.eAlg_def]; rfl
    rw [hcoef] at h0
    exact (map_eq_zero_iff _ (readLL0 S i true).injective).1 h0
  let rd : ↥D.LL0 →+* FractionRing (D.ntw.O i) := readLL0 S i true
  have hrd : Function.Injective rd := (readLL0 S i true).injective
  let eL : MonoidAlgebra ↥D.LL0 (G0g D.nd) :=
    MonoidAlgebra.ofCoeff (Finsupp.onFinset s D.nexp.eLL0 fun g hg => by
      by_contra h
      exact hg (hsupp g h))
  have heL : ∀ g, eL.coeff g = D.nexp.eLL0 g := fun g => by
    simp only [eL, MonoidAlgebra.coeff_ofCoeff, Finsupp.onFinset_apply]
  have hmap : MonoidAlgebra.mapRingHom (G0g D.nd) rd eL = D.nexp.eAlg i true := by
    apply MonoidAlgebra.ext
    apply Finsupp.ext
    intro g
    rw [MonoidAlgebra.coeff_mapRingHom, heL, D.nexp.eAlg_def]
    rfl
  have hinj : Function.Injective (MonoidAlgebra.mapRingHom (G0g D.nd) rd) := by
    intro x y hxy
    apply MonoidAlgebra.ext
    apply Finsupp.ext
    intro g
    apply hrd
    rw [← MonoidAlgebra.coeff_mapRingHom, ← MonoidAlgebra.coeff_mapRingHom, hxy]
  have hidem : eL * eL = eL := hinj (by rw [map_mul, hmap, D.nexp.eAlg_idem])
  let eLL := MonoidAlgebra.mapRingHom (G0g D.nd) (algebraMap ↥D.LL0 D.what₂.LL) eL
  have hP : goodProjW S j D.nexp.eLL0 =
      MonoidAlgebra.lift D.what₂.LL (Module.End D.what₂.LL (S.WL j)) (G0g D.nd) (rhoTw S j) eLL := by
    rw [MonoidAlgebra.lift_apply]
    unfold goodProjW
    rw [finsum_eq_sum_of_support_subset _ (s := s) fun g hg => by
      by_contra hgs
      exact hg (by simp only [hsupp g hgs, IntermediateField.coe_zero, zero_mul, zero_smul])]
    rw [Finsupp.sum_of_support_subset _ (s := s) (fun g hg => by
      by_contra hgs
      apply Finsupp.mem_support_iff.1 hg
      simp only [eLL, MonoidAlgebra.coeff_mapRingHom, heL, hsupp g hgs, map_zero]) (fun a b => b • rhoTw S j a) (fun _ _ => zero_smul _ _)]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp only [eLL, MonoidAlgebra.coeff_mapRingHom, heL, rhoTw, MonoidHom.coe_mk, OneHom.coe_mk, mul_smul,
      Units.val_inv_eq_inv_val]
    rfl
  rw [hP, ← map_mul, ← map_mul, hidem]

end GlobalTheory.GoodSS.Idem
end
end

section

open NumberField Formalism.IndefR.NX

theorem _root_.GlobalTheory.T.isKsForm_of_algebraicFormsIso : ∀ {LL Ks Ks' WL WL' G G' : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks]
    [Algebra Ks LL] [Field Ks'] [NumberField Ks'] [Algebra Ks' LL] [AddCommGroup WL] [Module LL WL] [Module Ks WL]
    [IsScalarTower Ks LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL] [AddCommGroup WL'] [Module LL WL']
    [Module Ks' WL'] [IsScalarTower Ks' LL WL'] [Module (𝓞 Ks') WL'] [IsScalarTower (𝓞 Ks') Ks' WL']
    {W W' : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
    [∀ σ, NormedAddCommGroup (W' σ)] [∀ σ, InnerProductSpace ℂ (W' σ)] [Group G] [Group G']
    (A : Formalism.IndefR.Arith.FormsL LL Ks WL W G) (A' : Formalism.IndefR.Arith.FormsL LL Ks' WL' W' G'),
    FormsIso A A' → A'.IsKsForm → A.IsKsForm := by
  first | exact @GlobalTheory.isKsForm_of_formsIso | exact GlobalTheory.isKsForm_of_formsIso | (intros; apply GlobalTheory.isKsForm_of_formsIso <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical



noncomputable section

namespace GlobalTheory.HalfOInt

open Formalism.IndefR.Fin.LevelGroupLemmas.Lat Matrix

theorem idem_mem_at (D : D7) (e : AE D) (PP : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E))
    (he : Formalism.L2.NTheta.IsIdemAt e PP)
    (hP : ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    (a : D.host.E) (ha : a ∈ D.host.AA) :
    toEAf D e * eToEAf D a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  set n : ℕ := Ideal.absNorm D.host.𝔟 with hn
  have hnP : (n : 𝓞 D.host.E) ∉ PP.asIdeal := by
    intro h
    obtain ⟨p, hp, hpP⟩ := GlobalTheory.HalfCompare.exists_prime_under PP
    exact hP ((hpP _).2 (((GlobalTheory.HalfCompare.prime_dvd_absNorm_halfDifferent D hp).1 ((hpP _).1 h)).mul_right _))
  have hn0 : (n : 𝓞 D.host.E) ≠ 0 := fun h => hnP (h ▸ zero_mem _)
  have hn0' : (n : D.host.E) ≠ 0 := by
    intro h
    apply hn0
    have : n = 0 := by exact_mod_cast h
    rw [this, Nat.cast_zero]
  have h1 : finPart D (e * incA D (((n : 𝓞 D.host.E) : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra h
    exact hnP ((he.2 _ hn0).2 h)
  have h2 := GlobalTheory.IdemIntegral.toEAf_mem_of_finPart h1
  obtain ⟨c, hc⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.int_of_mem_b D (Ideal.absNorm_mem D.host.𝔟) ha
  have h3 := mul_mem h2 (GlobalTheory.IdemIntegral.eToEAf_int D c)
  rw [map_mul, GlobalTheory.IdemIntegral.toEAf_incA, mul_assoc, ← map_mul] at h3
  convert h3 using 3
  have hc' : (c : D.host.E) = a * n := hc
  have hcast : ((n : 𝓞 D.host.E) : D.host.E) = n := map_natCast (algebraMap (𝓞 D.host.E) D.host.E) n
  rw [hc', hcast]
  field_simp

theorem idem_mem_intAf (D : D7) (e : AE D) (P : Finset (Pl D.host.E)) (he : IsIdemSum e P)
    (hP : ∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    (a : D.host.E) (ha : a ∈ D.host.AA) :
    toEAf D e * eToEAf D a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he

  rw [map_sum, Finset.sum_mul]
  exact sum_mem fun PP hPP => idem_mem_at D _ PP (hes PP hPP) (hP PP hPP) a ha

theorem smul_genE {D : D7} {S T : HSp D} (e : AE D) (c : EAf D) (τ : Fin T.rank → EAf D)
    (σ : Fin S.rank → EAf D) :
    e • genE (S := S) (T := T) c τ σ = genE (toEAf D e * c) τ σ := by
  ext i j
  simp only [genE, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, mul_liftE, mul_assoc]

end GlobalTheory.HalfOInt

namespace GlobalTheory.HalfOInt
open Formalism.IndefR.Fin.LevelGroupLemmas.Lat Matrix



theorem frMapO_int_of_half {D : D7} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)}
    (hS : IsSelfDualC S ΛS) (fS : Formalism.L2.DIV.IsFrame βS ΛS) (fT : Formalism.L2.DIV.IsFrame βT ΛT)
    {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P)
    (hP : ∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    {u : WO S T} (hu : u ∈ latO S T ΛS ΛT (fun _ => True)) (hh : IsHalf e u) :
    IsIntM (frMapO S T βS βT u) := by
  have hx : e • u = u := Matrix.ext fun i j => hh i j
  rw [← hx]
  clear hx hh
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, _, a, ha, s, hs, t, ht, rfl⟩ := hw
    show IsIntM (frMapO S T βS βT (e • genL S T α a s t))
    rw [genL_eq_genE, smul_genE, genE, frMapO_mapLiftE, mul_vecMulVec_mul]
    intro i j
    simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
    refine mul_mem ?_ (mul_mem ?_ ?_)
    · rw [← mul_assoc]
      exact mul_mem (idem_mem_intAf D e P he hP a ha)
        (Subring.subset_closure (Or.inr ⟨⟨α, fun v => hα v⟩, rfl⟩))
    · exact (fT _).1 (mem_hatL_of_mem ht) i
    · rw [Matrix.vecMul_vecMul]
      have e : (fun l => (S.gram.map (eToEAf D) * (βS : Matrix (Fin S.rank) (Fin S.rank) (EAf D))) l j) =
          S.gram.map (eToEAf D) *ᵥ (fun i => (βS : Matrix (Fin S.rank) (Fin S.rank) (EAf D)) i j) := by
        funext l; rw [Matrix.mul_apply]; rfl
      show (fun k => sR D (eToEAf D (s k))) ⬝ᵥ
        (fun l => (S.gram.map (eToEAf D) * (βS : Matrix (Fin S.rank) (Fin S.rank) (EAf D))) l j) ∈ _
      rw [e]
      exact hform_int hS hs (col_mem_hatL fS j)
  | zero =>
    rw [smul_zero, frMapO_zero]
    exact fun _ _ => zero_mem _
  | add x y _ _ hx hy =>
    rw [smul_add, frMapO_add]
    exact isIntM_add hx hy
  | neg x _ hx =>
    rw [smul_neg, frMapO_neg]
    exact fun i j => neg_mem (hx i j)

end GlobalTheory.HalfOInt

namespace GlobalTheory.HalfOInt
open Formalism.IndefR.Fin.LevelGroupLemmas.Lat Matrix

theorem sum_decomp {R : Type} [CommRing R] {m n N : ℕ} (M : Matrix (Fin m) (Fin n) R) (g Y : Fin N → Fin n → R)
    (hb : ∑ k, vecMulVec (g k) (Y k) = 1) (c z : R) (hM : (c * z) • M = M) :
    ∑ k, c • vecMulVec (z • (M *ᵥ g k)) (Y k) = M := by
  have h : ∀ k, c • vecMulVec (z • (M *ᵥ g k)) (Y k) = (c * z) • (M * vecMulVec (g k) (Y k)) := by
    intro k
    ext i j
    simp only [Matrix.smul_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, Matrix.mul_apply,
      Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [Finset.sum_congr rfl fun k _ => h k, ← Finset.smul_sum, ← Matrix.mul_sum, hb, Matrix.mul_one, hM]



theorem mem_latO_of_int {D : D7} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)}
    (hS : IsSelfDualC S ΛS) (fS : Formalism.L2.DIV.IsFrame βS ΛS) (fT : Formalism.L2.DIV.IsFrame βT ΛT)
    {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P)
    (hP : ∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    {t : WO S T} (ht : IsHalf e t) (hN : IsIntM (frMapO S T βS βT t)) :
    t ∈ latO S T ΛS ΛT (fun _ => True) := by
  have ha := GlobalTheory.HalfAdjLattice.natCast_mem_AA (D := D) (D.host.QS * D.host.q)
  generalize D.host.QS * D.host.q * Ideal.absNorm D.host.ccK = n at hP ha
  obtain ⟨N, g, s, hg, hs, hb⟩ := GlobalTheory.HalfAdjLattice.exists_dual_families S hS
  have hz := GlobalTheory.HalfAdjLattice.toEAf_int (GlobalTheory.HalfAdjLattice.idem_div_int he hP)
  have hze := GlobalTheory.HalfAdjLattice.natCast_mul_idem_div he hP
  generalize e * incA D (n : D.host.E)⁻¹ = z at hz hze
  set M : Matrix (Fin T.rank) (Fin S.rank) (EAf D) := Matrix.map t (toEAf D) with hMdef
  have hN' : IsIntM ((βT⁻¹).val * M * βS.val) := hN
  have hb' : ∑ k, vecMulVec (fun i => eToEAf D (g k i))
      (vecMul (fun a => sR D (eToEAf D (s k a))) (S.gram.map (eToEAf D))) = 1 := by
    ext i j
    have h1 := congrArg (eToEAf D) (congrFun (hb (Pi.single j 1)) i)

    rw [Finset.sum_apply, map_sum] at h1
    rw [Matrix.sum_apply]
    have h2 : eToEAf D ((Pi.single j 1 : Fin S.rank → D.host.E) i) = (1 : Matrix (Fin S.rank) (Fin S.rank) (EAf D)) i j := by
      rw [Pi.single_apply, Matrix.one_apply]
      split_ifs <;> simp
    rw [← h2, ← h1]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mulVec_single_one]

    simp only [vecMulVec_apply, vecMul, dotProduct, map_apply, sR_eTo, Pi.smul_apply, smul_eq_mul, map_mul, map_sum,
    Matrix.col, transpose_apply]
    exact mul_comm _ _
  have hM : ((eToEAf D (n : D.host.E) * ((1 : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F))) * toEAf D z) • M = M := by
    have h1 : (eToEAf D (n : D.host.E) * ((1 : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F))) * toEAf D z = toEAf D e := by
      rw [← hze, map_mul, toEAf_incA, ← Algebra.TensorProduct.one_def, mul_one]
    rw [h1]
    ext i j
    simp only [hMdef, Matrix.smul_apply, map_apply, smul_eq_mul]
    rw [← map_mul, ht i j]
  have key := sum_decomp M (fun k i => eToEAf D (g k i))
    (fun k => vecMul (fun a => sR D (eToEAf D (s k a))) (S.gram.map (eToEAf D))) hb' _ _ hM
  have hdec : t = ∑ k, genE (S := S) (T := T)
      (eToEAf D (n : D.host.E) * ((1 : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F)))
      (toEAf D z • (M *ᵥ fun i => eToEAf D (g k i))) (fun a => eToEAf D (s k a)) := by
    ext i j
    have h1 := congrFun (congrFun key i) j
    rw [Matrix.sum_apply] at h1
    rw [Matrix.sum_apply]
    unfold genE
    simp only [map_apply]
    rw [← liftE_sum, h1]
    have h0 : infPart D (t i j) = 0 := by rw [← ht i j, map_mul, infPart_of_idemSum he, zero_mul]
    exact (liftE_toEAf _ h0).symm
  rw [hdec]
  refine AddSubgroup.sum_mem _ fun k _ => genE_mem ?_ ha ?_ (mem_hatL_of_mem (hs k))
  · intro v; rw [map_one]; exact one_mem _
  · exact Submodule.smul_mem _ (⟨_, hz⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E)
      (GlobalTheory.HalfAdjLattice.mulVec_mem_hatL fT fS hN' (mem_hatL_of_mem (hg k)))

end GlobalTheory.HalfOInt

namespace GlobalTheory.HalfOInt

theorem mem_latO_iff_frMapO_int : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P → (∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ w : WO S T, IsHalf e w → (w ∈ latO S T ΛS ΛT (fun _ => True) ↔ IsIntM (frMapO S T βS βT w)) := by
  intro D S T ΛS ΛT βS βT hS _ fS fT P e he hP w hw
  exact ⟨fun hu => frMapO_int_of_half hS fS fT he hP hu hw, fun hN => mem_latO_of_int hS fS fT he hP hw hN⟩

end GlobalTheory.HalfOInt
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.VacFix

variable {D : D7}

theorem symplO_eq_zero (S T : HSp D) (x y : WO S T)
    (h : ∀ c b d a, cA D (y c b) * x d a = 0) : symplO S T x y = 0 := by
  have h0 : hO S T x y = 0 := by
    unfold hO
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ =>
      Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
    have := h c b d a
    calc _ = incA D ((HSpace.gram S)⁻¹ a b) * incA D (HSpace.gram T c d) *
        (cA D (y c b) * x d a) := by ring
      _ = 0 := by rw [this, mul_zero]
  unfold symplO
  rw [h0, mul_zero, map_zero]

theorem heisO_fix_of_isThetaAt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D) (Λ : AddSubgroup (WO S T)) (c : ℂ) (f₀ Φ f : WO S T → ℂ) (u : WO S T), IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ f → (∀ i j, e * u i j = 0) → (∀ i j, cA D e * u i j = 0) → heisO ψ S T u f₀ = f₀ → heisO ψ S T u f = f := by
  intro D ψ S T e Λ c f₀ Φ f u hf h1 h2 h0
  obtain ⟨⟨M, hM⟩, hall⟩ := hf
  have hM' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c f₀
      ((GlobalTheory.SplitScalar.heisL ψ S T u) ∘ₗ M) := by
    refine ⟨fun Ψ hΨ x hx => ?_, fun Ψ hΨ y hy => ?_, ?_⟩
    · simp only [LinearMap.comp_apply, GlobalTheory.SplitScalar.heisL_apply]
      rw [hM.trans Ψ hΨ x hx, GlobalTheory.SplitScalar.heisO_comm, symplO_eq_zero, AddChar.map_zero_eq_one,
        one_smul]
      intro c b d a
      rw [← hx c b, map_mul]
      linear_combination cA D (x c b) * h2 d a
    · simp only [LinearMap.comp_apply, GlobalTheory.SplitScalar.heisL_apply]
      rw [hM.modul Ψ hΨ y hy, GlobalTheory.SplitScalar.heisO_comm ψ S T y u, symplO_eq_zero,
        AddChar.map_zero_eq_one, one_smul]
      intro c b d a
      have h3 : cA D e * cA D (u c b) = 0 := by rw [← map_mul, h1, map_zero]
      rw [← hy d a]
      linear_combination y d a * h3
    · simp only [LinearMap.comp_apply, GlobalTheory.SplitScalar.heisL_apply]
      rw [hM.vac, h0]
  have e1 := hall M hM
  have e2 := hall _ hM'
  simp only [LinearMap.comp_apply, GlobalTheory.SplitScalar.heisL_apply] at e2
  rw [← e1] at e2
  exact e2.symm

end GlobalTheory.VacFix
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open GlobalTheory.RawLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rational_source_acts_on_orientedTheta_by_substitution : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT ω → ∀ f, IsThetaFunO ψ S T f → ∀ γ ∈ GQ S, ∀ x, ω (γ, 1) f x = f (actO S T γ⁻¹ 1 x) := by
  first | exact @GlobalTheory.RatSubst.om_rat_left_apply | exact GlobalTheory.RatSubst.om_rat_left_apply | (intros; apply GlobalTheory.RatSubst.om_rat_left_apply <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.linear_relation_sections_span_eq : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (σ : T.Q.c.F →+* ℂ), Formalism.L2.Pj.RdIndep (T.Q.Xo j) T.Q.c (T.U j) σ → ∀ (w : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom w n → ∀ (κ ι : Type) [Fintype κ] [Fintype ι] (A : κ → ι → Rul (T.Q.Xo j) T.Q.c), (∀ k i, A k i ∈ sec (T.Q.Xo j) T.Q.c w n) → ∀ z : κ → ℂ, (∀ i, ∑ k, z k • rdU (T.U j σ) (A k i) = 0) → z ∈ Submodule.span ℂ ((fun c : κ → T.Q.c.F => fun k => σ (c k)) '' {c | ∀ i, ∑ k, c k • A k i = 0}) := by
  first | exact @GlobalTheory.kerC_span_rat | exact GlobalTheory.kerC_span_rat | (intros; apply GlobalTheory.kerC_span_rat <;> assumption)
end

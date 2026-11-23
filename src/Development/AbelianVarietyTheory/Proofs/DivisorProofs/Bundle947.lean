module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle533
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle544
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle450
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle507
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HdimEqZeroOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.BijectiveToPushforwardComp
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsPowMulPowEqOfIsZeroCechH
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle023
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParIndJacPlacing
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Mathlib.NumberTheory.LocalField.Basic
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle512
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle039
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FinrankOfIsSecBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle923
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle925
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.HTPair

namespace GlobalTheory.QuotField

variable {p : ℕ} {O : Type} [CommRing O] (G : PDivGroup p O)

def levelRes (m : ℕ) : G.A (m + 1) →ₐc[O] G.A 1 :=
  Nat.rec (motive := fun m => G.A (m + 1) →ₐc[O] G.A 1) (BialgHom.id O _)
    (fun m f => f.comp (G.res (m + 1))) m

theorem levelRes_surjective (m : ℕ) : Function.Surjective (levelRes G m) := by
  induction m with
  | zero => exact Function.surjective_id
  | succ m ih =>
    intro c
    obtain ⟨a, rfl⟩ := ih c
    obtain ⟨b, rfl⟩ := G.res_surjective (m + 1) a
    exact ⟨b, rfl⟩

theorem ker_succ {C : Type} [CommRing C] [Bialgebra O C] (π : G.A 1 →ₐc[O] C) (m : ℕ) :
    RingHom.ker (π.comp (levelRes G (m + 1))) =
      Ideal.comap (G.res (m + 1) : G.A (m + 2) →ₐ[O] G.A (m + 1))
        (RingHom.ker (π.comp (levelRes G m))) :=
  Ideal.ext fun _ => Iff.rfl

theorem torsion_le {C : Type} [CommRing C] [Bialgebra O C] (π : G.A 1 →ₐc[O] C) (m : ℕ) :
    torsionIdeal (R := O) (A := G.A (m + 1)) p ≤ RingHom.ker (π.comp (levelRes G m)) := by
  refine (kerIdeal_le_ker_iff _
    ((π.comp (levelRes G m) : G.A (m + 1) →ₐc[O] C) : G.A (m + 1) →ₐ[O] C)).2 fun c => ?_
  change π (levelRes G m (mulBy (R := O) (A := G.A (m + 1)) p c)) = _
  have h := G.mulBy_pow_self 1 (levelRes G m c)
  rw [pow_one] at h
  rw [map_mulBy, h, AlgHomClass.commutes, CoalgHomClass.counit_comp_apply]

end GlobalTheory.QuotField


open GlobalTheory.QuotField GlobalTheory.HTPair.QuotIsog in
theorem GlobalTheory.HTPair.exists_quot_field : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    (G : PDivGroup p k) (C : Type) [CommRing C] [HopfAlgebra k C] [IsCocomm k C]
    [Module.Finite k C] (π : G.A 1 →ₐc[k] C), Function.Surjective π →
    ∃ (Q : PDivGroup p k) (q : G ⟶ Q) (q' : Q ⟶ G), q ≫ q' = (p : ℤ_[p]) • 𝟙 G ∧
      q' ≫ q = (p : ℤ_[p]) • 𝟙 Q ∧ kerIdeal (q.app 1) = RingHom.ker π := by
  intro p _ k _ _ G C _ _ _ _ π hπ
  have hsurj : ∀ m, Function.Surjective (π.comp (levelRes G m)) := fun m =>
    hπ.comp (levelRes_surjective G m)
  choose B iR iH iC iF j hinj hker huniv using
    fun m => GlobalTheory.T.exists_quotient_finiteCommGroupScheme_closedSubgroup k (G.A (m + 1)) C (π.comp (levelRes G m)) (hsurj m)
  letI := iR
  letI := iH
  letI := iC
  letI := iF
  have hρ : ∀ m, ∃ ρ : G.A (m + 1) →ₗ[k] B m, ∀ b, ρ (j m b) = b := fun m => by
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective
      ((j m : B m →ₐ[k] G.A (m + 1)).toLinearMap) (LinearMap.ker_eq_bot.2 (hinj m))
    exact ⟨g, fun b => LinearMap.congr_fun hg b⟩
  choose ρ hρ using hρ
  have hfac : ∀ m (D : Type) [CommRing D] [Bialgebra k D] (f : D →ₐc[k] G.A (m + 1)),
      kerIdeal f ≤ RingHom.ker (π.comp (levelRes G m)) →
        ∃ g : D →ₐc[k] B m, ∀ d, j m (g d) = f d := fun m D _ _ f hf =>
    GlobalTheory.T.bialgHom_factor_through_split_injection k (G.A (m + 1)) (B m) D (j m) (ρ m) f (hρ m) (huniv m D f hf)
  choose r hr using fun m => hfac m (B (m + 1)) ((G.res (m + 1)).comp (j (m + 1))) (by
    rw [kerIdeal_comp, hker (m + 1), ker_succ]
    exact Ideal.map_comap_le)
  choose s hs using fun m => hfac m (G.A m) (G.mulP m) (by
    rw [← kerIdeal_comp_of_surjective _ (G.res_surjective m), G.mulP_comp_res]
    exact torsion_le G π m)
  have hkr : ∀ m, kerIdeal (j m) =
      Ideal.map (G.res (m + 1) : G.A (m + 2) →ₐ[k] G.A (m + 1)) (kerIdeal (j (m + 1))) := by
    intro m
    rw [hker, hker, ker_succ]
    exact (Ideal.map_comap_of_surjective (G.res (m + 1) : G.A (m + 2) →ₐ[k] G.A (m + 1))
      (G.res_surjective (m + 1)) _).symm
  let τ : QuotTower G :=
    { B := B
      commRing := iR
      hopf := iH
      cocomm := iC
      finite := iF
      projective := fun _ => inferInstance
      j := j
      ρ := ρ
      r := r
      s := s
      ρ_j := hρ
      r_surjective := fun m => GlobalTheory.T.quotientTransition_surjective_same_subgroup k (G.A (m + 1)) (G.A (m + 2)) (B m) (B (m + 1))
        (G.res (m + 1)) (j m) (j (m + 1)) (r m) (ρ m) (hρ m) (fun b => hr m b) (hkr m)
      j_r := fun m b => hr m b
      j_s := hs
      tors_le := fun m => (hker m).symm ▸ torsion_le G π m }
  obtain ⟨H, q, hqs, hqk, hqc⟩ := GlobalTheory.HTPair.exists_quotPDivGroup p k G τ
  refine ⟨H, toQuot τ q hqs hqk hqc, fromQuot τ q hqc, ?_, ?_, ?_⟩
  · refine PDivGroup.Hom.ext (funext fun n => ?_)
    rw [natCast_smul_id_app, comp_app]
    refine BialgHom.ext fun a => ?_
    change (toQuot τ q hqs hqk hqc).app n (q n (τ.s n a)) = _
    rw [toQuot_app_q, τ.j_s, G.res_mulP]
  · refine PDivGroup.Hom.ext (funext fun n => ?_)
    rw [natCast_smul_id_app, comp_app]
    refine BialgHom.ext fun c => ?_
    obtain ⟨b, rfl⟩ := hqs n c
    change q n (τ.s n ((toQuot τ q hqs hqk hqc).app n (q n b))) = _
    rw [toQuot_app_q, s_res_j, map_mulBy]
  · have h1 : ((toQuot τ q hqs hqk hqc).app 1).comp (q 1) = (G.res 1).comp (τ.j 1) :=
      BialgHom.ext fun b => toQuot_app_q τ q hqs hqk hqc 1 b
    rw [← kerIdeal_comp_of_surjective _ (hqs 1), h1, kerIdeal_comp]
    exact (τ.map_res_kerIdeal 0).trans ((hker 0).trans (Ideal.ext fun _ => Iff.rfl))
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory

theorem coh_subsingleton_of_disjoint_cover : ∀ (X : Scheme.{0}) (M : LB X) (κ : Type) (U : κ → X.Opens), M.IsLB → ⨆ c, U c = ⊤ → (Pairwise fun a b => Disjoint (U a) (U b)) → ∀ q : ℕ, (∀ c, Subsingleton (coh (LB.toMod (M.pull (U c).ι)) q)) → Subsingleton (coh (LB.toMod M) q) := by
  intro X M κ U hM hc hd q h
  have hj : ∀ (i : κ) (r : ℤ), (U i).ι.appTop (algebraMap ℤ Γ(X, ⊤) r) =
      algebraMap ℤ Γ((U i).toScheme, ⊤) r := fun i r => by simp
  have hs : ∀ i, Subsingleton (coh ((LB.toMod M).restrict (U i).ι) q) := fun i =>
    (cohOn.mapIso ℤ ⊤ q ((Scheme.Modules.restrictFunctorIsoPullback (U i).ι).app _ ≪≫
      LB.pullbackIso hM (U i).ι)).toEquiv.subsingleton_congr.2 (h i)
  exact (coh.disjointRestrictEquiv ℤ (fun i => (U i).ι) hj (by simpa using hc)
    (by simpa using hd) (LB.toMod M) q).toEquiv.subsingleton

end GlobalTheory
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic
open scoped TensorProduct

namespace GlobalTheory.GenericMember

noncomputable def genVar (k : Type) [Field k] (N : ℕ) {X' : Scheme.{0}}
    (f' : X' ⟶ Sp (FractionRing (MvPolynomial (Fin N) k))) (i : Fin N) : Γ(X', ⊤) :=
  f'.appTop ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing (MvPolynomial (Fin N) k)))).inv
    (algebraMap (MvPolynomial (Fin N) k) (FractionRing (MvPolynomial (Fin N) k)) (MvPolynomial.X i)))

noncomputable def genSec (k : Type) [Field k] (N : ℕ) {X X' : Scheme.{0}}
    (f' : X' ⟶ Sp (FractionRing (MvPolynomial (Fin N) k))) (π : X' ⟶ X) (L : LB X)
    (b : Fin N → L.Sec) : (L.pull π).Sec :=
  ∑ i, genVar k N f' i • secPull (b i) π

end GlobalTheory.GenericMember
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace TwistCube

open Twist

variable {X : Scheme.{0}} (F : X.Modules) {L : LB X}

theorem mulSecOfEq_zpowSec_comp (σ : LB.Sec (lbZPow L 1)) {n d e : ℤ} (a b : ℕ)
    (h₁ : n + a * 1 = d) (h₂ : d + b * 1 = e) (h₃ : n + ((a + b : ℕ) : ℤ) * 1 = e) :
    mulSecOfEq F (zpowSec σ a) h₁ ≫ mulSecOfEq F (zpowSec σ b) h₂ =
      mulSecOfEq F (zpowSec σ (a + b)) h₃ := by
  ext V s : 3
  exact mulSecOfEq_zpowSec_app σ rfl h₁ h₂ h₃ s

def powMap (hL : L.IsLB) (σ : LB.Sec (lbZPow L 1)) (c : ℕ) : F ⟶ twistZ F L c :=
  (twistZZeroIso F hL).hom ≫ mulSecOfEq F (zpowSec σ c) (by omega)

theorem powMap_comp (hL : L.IsLB) (σ : LB.Sec (lbZPow L 1)) (j c d : ℕ) (h : c + j = d)
    (h' : (c : ℤ) + (j : ℤ) * 1 = d) :
    powMap F hL σ c ≫ mulSecOfEq F (zpowSec σ j) h' = powMap F hL σ d := by
  subst h
  rw [powMap, powMap, Category.assoc, mulSecOfEq_zpowSec_comp F σ c j _ _ (by push_cast; ring)]

theorem bijective_powMap_app (hL : L.IsLB) (σ : LB.Sec (lbZPow L 1)) (c : ℕ) {W : X.Opens}
    (hW : W ≤ nonzeroLocus σ) : Function.Bijective ((powMap F hL σ c).app W) := by
  rw [powMap, Scheme.Modules.Hom.comp_app, ConcreteCategory.coe_comp]
  exact (bijective_mulSecOfEq_app hL _ (by omega) (hW.trans (nonzeroLocus_le_zpowSec hL σ c))).comp
    (ConcreteCategory.bijective_of_isIso ((twistZZeroIso F hL).hom.app W))

variable {ι : Type} (U : ι → X.Opens)

theorem isIso_cechCubeMap_powMap (hL : L.IsLB) (σ : LB.Sec (lbZPow L 1)) (c : ℕ) {V : X.Opens}
    (hV : V ≤ nonzeroLocus σ) : IsIso (cechCubeMap ℤ V U (powMap F hL σ c)) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun s => ?_
  rw [ConcreteCategory.isIso_iff_bijective]
  exact bijective_powMap_app F hL σ c ((cechOpen_le V U s).trans hV)

theorem cechCubeRes_naturality {G : X.Modules} (φ : F ⟶ G) {V : X.Opens} :
    cechCubeMap ℤ ⊤ U φ ≫ cechCubeRes ℤ G (cechOpen_mono (le_top (a := V)) fun _ => le_rfl) =
      cechCubeRes ℤ F (cechOpen_mono (le_top (a := V)) fun _ => le_rfl) ≫ cechCubeMap ℤ V U φ :=
  presheafCubeRes_naturality (sectionsPresheafMap ℤ φ) _

def cubeDiv (hL : L.IsLB) (σ : LB.Sec (lbZPow L 1)) (c : ℕ) {V : X.Opens}
    (hV : V ≤ nonzeroLocus σ) : cechCube ℤ (twistZ F L c) ⊤ U ⟶ cechCube ℤ F V U :=
  haveI := isIso_cechCubeMap_powMap F U hL σ c hV
  cechCubeRes ℤ (twistZ F L c) (cechOpen_mono (le_top (a := V)) fun _ => le_rfl) ≫
    inv (cechCubeMap ℤ V U (powMap F hL σ c))

theorem cubeDiv_comp (hL : L.IsLB) (σ : LB.Sec (lbZPow L 1)) (c : ℕ) {V : X.Opens}
    (hV : V ≤ nonzeroLocus σ) : cubeDiv F U hL σ c hV ≫ cechCubeMap ℤ V U (powMap F hL σ c) =
      cechCubeRes ℤ (twistZ F L c) (cechOpen_mono (le_top (a := V)) fun _ => le_rfl) := by
  haveI := isIso_cechCubeMap_powMap F U hL σ c hV
  simp [cubeDiv]

theorem cubeDiv_app (hL : L.IsLB) (σ : LB.Sec (lbZPow L 1)) (c : ℕ) {V : X.Opens}
    (hV : V ≤ nonzeroLocus σ) (s : Finset ι) (a : (cechCube ℤ (twistZ F L c) ⊤ U).obj s) :
    (cechCubeMap ℤ V U (powMap F hL σ c)).app s ((cubeDiv F U hL σ c hV).app s a) =
      (cechCubeRes ℤ (twistZ F L c) (cechOpen_mono (le_top (a := V)) fun _ => le_rfl)).app s a := by
  rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, cubeDiv_comp]

theorem cechCubeMap_mul_comp_cubeDiv (hL : L.IsLB) (σ : LB.Sec (lbZPow L 1)) (j c d : ℕ)
    (h : c + j = d) (h' : (c : ℤ) + (j : ℤ) * 1 = d) {V : X.Opens} (hV : V ≤ nonzeroLocus σ) :
    cechCubeMap ℤ ⊤ U (mulSecOfEq F (zpowSec σ j) h') ≫ cubeDiv F U hL σ d hV =
      cubeDiv F U hL σ c hV := by
  haveI := isIso_cechCubeMap_powMap F U hL σ c hV
  haveI := isIso_cechCubeMap_powMap F U hL σ d hV
  unfold cubeDiv
  rw [← Category.assoc, cechCubeRes_naturality, Category.assoc]
  congr 1
  rw [IsIso.comp_inv_eq, IsIso.eq_inv_comp]
  exact congrArg (cechCubeMap ℤ V U) (powMap_comp F hL σ j c d h h')

end TwistCube

end GlobalTheory

theorem GlobalTheory.cechCube_nonzeroLocus_colimit : ∀ (X : Scheme.{0}) (F : X.Modules) [F.IsQuasicoherent] (L : LB X), L.IsLB → ∀ (σ : L.Sec) {ι : Type} [LinearOrder ι] [Fintype ι] (U : ι → X.Opens), (∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i)) → ∃ (μ : ∀ (j c d : ℕ), c + j = d → (cechCube ℤ (twistZ F L c) ⊤ U ⟶ cechCube ℤ (twistZ F L d) ⊤ U)) (ρ : ∀ c : ℕ, cechCube ℤ (twistZ F L c) ⊤ U ⟶ cechCube ℤ F (nonzeroLocus σ) U), (∀ j c d h, μ j c d h ≫ ρ d = ρ c) ∧ (∀ (j j' c d e : ℕ) (h : c + j = d) (h' : d + j' = e) (h'' : c + (j + j') = e), μ j c d h ≫ μ j' d e h' = μ (j + j') c e h'') ∧ (∀ s : Finset ι, s.Nonempty → ∀ b : (cechCube ℤ F (nonzeroLocus σ) U).obj s, ∃ c : ℕ, ∃ a : (cechCube ℤ (twistZ F L c) ⊤ U).obj s, (ρ c).app s a = b) ∧ (∀ s : Finset ι, s.Nonempty → ∀ (c : ℕ) (a : (cechCube ℤ (twistZ F L c) ⊤ U).obj s), (ρ c).app s a = 0 → ∃ j, (μ j c (c + j) rfl).app s a = 0) := by
  intro X F _ L hL σ₀ ι _ _ U hU
  have hVσ : nonzeroLocus σ₀ ≤ nonzeroLocus (Twist.zofSec σ₀) := (Twist.nonzeroLocus_zofSec hL σ₀).ge
  refine ⟨fun j c d h => cechCubeMap ℤ ⊤ U
      (Twist.mulSecOfEq F (Twist.zpowSec (Twist.zofSec σ₀) j) (by omega)),
    fun c => TwistCube.cubeDiv F U hL (Twist.zofSec σ₀) c hVσ, ?_, ?_, ?_, ?_⟩
  · intro j c d h
    exact TwistCube.cechCubeMap_mul_comp_cubeDiv F U hL _ j c d h _ hVσ
  · intro j j' c d e h h' h''
    exact congrArg (cechCubeMap ℤ ⊤ U) (TwistCube.mulSecOfEq_zpowSec_comp F _ j j' (by omega) _ _)
  · intro s hs b
    have hA : IsAffineOpen (cechOpen ⊤ U s) := by rw [cechOpen_top]; exact hU s hs
    have hle : cechOpen (nonzeroLocus σ₀) U s ≤ cechOpen ⊤ U s :=
      cechOpen_mono le_top (fun _ => le_rfl) s
    have hV : cechOpen (nonzeroLocus σ₀) U s =
        cechOpen ⊤ U s ⊓ nonzeroLocus (Twist.zofSec σ₀) := by
      rw [cechOpen, cechOpen, top_inf_eq, Twist.nonzeroLocus_zofSec hL, inf_comm]
    obtain ⟨k, hk⟩ := (Twist.eventually_exists_resM_eq_mulSecOfEq_zpowSec hL (Twist.zofSec σ₀)
      hA.isCompact hA.isQuasiSeparated hle hV ((Twist.twistZZeroIso F hL).hom.app _ b)).exists
    obtain ⟨a, ha⟩ := hk k (by omega)
    exact ⟨k, a, (TwistCube.bijective_powMap_app F hL _ k ((cechOpen_le _ U s).trans hVσ)).1
      ((TwistCube.cubeDiv_app F U hL (Twist.zofSec σ₀) k hVσ s a).trans ha)⟩
  · intro s hs c a ha
    have hA : IsAffineOpen (cechOpen ⊤ U s) := by rw [cechOpen_top]; exact hU s hs
    have hle : cechOpen (nonzeroLocus σ₀) U s ≤ cechOpen ⊤ U s :=
      cechOpen_mono le_top (fun _ => le_rfl) s
    have hV : cechOpen (nonzeroLocus σ₀) U s =
        cechOpen ⊤ U s ⊓ nonzeroLocus (Twist.zofSec σ₀) := by
      rw [cechOpen, cechOpen, top_inf_eq, Twist.nonzeroLocus_zofSec hL, inf_comm]
    have h0 : Twist.resM _ hle a = 0 := by
      have e := TwistCube.cubeDiv_app F U hL (Twist.zofSec σ₀) c hVσ s a
      rw [ha, map_zero] at e
      exact e.symm
    obtain ⟨k, hk⟩ := (Twist.eventually_mulSecOfEq_zpowSec_eq_zero hL (Twist.zofSec σ₀)
      hA.isCompact hle hV.ge a h0).exists
    exact ⟨k, hk _ (by push_cast; ring)⟩
end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

namespace GlobalTheory.PlacingProd

theorem multiProd_placing_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h n : ℕ) (d : Fin h → ℕ) (e e' : (Σ a, Fin (d a)) ≃ Fin n) (X : Fin h → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)), Nonempty ((multiProd e π).Equiv (multiProd e' π)) := by
  intro k _ _ _ _ h n d e e' X _ _ π
  exact (GlobalTheory.SmGL.Placing.parInd_jac_placing k (Fin h) (Fin n) (fun a => Fin (d a)) e e' _).1 _

end GlobalTheory.PlacingProd
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ContraProd

section General

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

end General

end GlobalTheory.ContraProd

noncomputable section

namespace GlobalTheory.ContraProd

section Fixed

theorem finiteDimensional_fixed_piTensor {α : Type} [Finite α] {Γ X : α → Type} [∀ a, Group (Γ a)]
    [∀ a, TopologicalSpace (Γ a)] [∀ a, IsTopologicalGroup (Γ a)] [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (hρ : ∀ a, IsSmooth (ρ a))
    (K : ∀ a, Subgroup (Γ a)) (hK : ∀ a, IsCompact (K a : Set (Γ a)))
    (hf : ∀ a, FiniteDimensional ℂ (fixed (ρ a) (K a))) :
    FiniteDimensional ℂ (fixed (piTensor ρ) (Subgroup.pi Set.univ K)) :=
  GlobalTheory.T.finiteDimensional_compact_fixed_vectors_piTensor_smooth ρ hρ K hK hf

end Fixed

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_compactOpen_GL (n : Type) [Fintype n] [DecidableEq n] (U : Set (GL n k)) (hU : U ∈ nhds 1) :
    ∃ K : Subgroup (GL n k), IsOpen (K : Set (GL n k)) ∧ IsCompact (K : Set (GL n k)) ∧ (K : Set (GL n k)) ⊆ U := by
  obtain ⟨J, h1, h2, h3, -⟩ := exists_open_normalised_subgroup_subset k n U hU
  exact ⟨J, h1, GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset (J.isClosed_of_isOpen h1) h3, h2⟩

theorem exists_pi_compactOpen {α : Type} [Finite α] (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    (U : Set (Levi k m)) (hU : U ∈ nhds (1 : Levi k m)) :
    ∃ K : ∀ a, Subgroup (GL (m a) k), (∀ a, IsOpen (K a : Set (GL (m a) k))) ∧
      (∀ a, IsCompact (K a : Set (GL (m a) k))) ∧ ((Subgroup.pi Set.univ K : Subgroup (Levi k m)) : Set (Levi k m)) ⊆ U := by
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, -, t, ht, hts⟩ := hU
  choose K hKo hKc hKt using fun a => exists_compactOpen_GL (k := k) (m a) (t a) (ht a)
  refine ⟨K, hKo, hKc, ?_⟩
  rw [Subgroup.coe_pi]
  exact fun g hg => hts fun a _ => hKt a (hg a (Set.mem_univ a))

theorem isAdmissible_piTensor {α : Type} [Finite α] (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (ρ : ∀ a, Representation ℂ (GL (m a) k) (X a)) (hρ : ∀ a, IsAdmissible (ρ a)) :
    IsAdmissible (piTensor ρ : Representation ℂ (Levi k m) _) := by
  refine ⟨isSmooth_piTensor fun a => (hρ a).1, fun K hKo hKc => ?_⟩
  obtain ⟨K', hKo', hKc', hK'⟩ := exists_pi_compactOpen m (K : Set (Levi k m)) (hKo.mem_nhds K.one_mem)
  haveI := finiteDimensional_fixed_piTensor ρ (fun a => (hρ a).1) K' hKc'
    fun a => (hρ a).2 (K' a) (hKo' a) (hKc' a)
  exact Submodule.finiteDimensional_of_le (S₁ := fixed (piTensor ρ : Representation ℂ (Levi k m) _) K)
    (S₂ := fixed (piTensor ρ) (Subgroup.pi Set.univ K'))
    (fun v hv => GlobalTheory.ContraRefl.mem_fix.2 fun h hh => GlobalTheory.ContraRefl.mem_fix.1 hv h (hK' hh))

end GlobalTheory.ContraProd

noncomputable section

namespace GlobalTheory.ContraProd

section Pairing

variable {α : Type} [Fintype α] {Γ X : α → Type} [∀ a, Group (Γ a)] [∀ a, TopologicalSpace (Γ a)]
  [∀ a, IsTopologicalGroup (Γ a)] [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
  (ρ : ∀ a, Representation ℂ (Γ a) (X a))

end Pairing

end GlobalTheory.ContraProd

noncomputable section

namespace GlobalTheory.ContraProd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end GlobalTheory.ContraProd
end
end
end
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.sectionBases_transfer_totalSpaceIso : ∀ {S S' : Scheme.{0}} (A : Over S) [GrpObj A] (Ag : Over S') [GrpObj Ag] (φ : Ag.left ⟶ A.left) (L : LB A.left), L.IsLB → ∀ (k : ℤ) (R : Type) [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S') (y : Spec (CommRingCat.of R) ⟶ S) (h : (Over.mk x ⊗ Ag).left ⟶ (Over.mk y ⊗ A).left) (hc : ∀ _ : Fin 1, (snd (Over.mk x) Ag).left ≫ φ = h ≫ (snd (Over.mk y) A).left), IsIso h → h ≫ (fst (Over.mk y) A).left = (fst (Over.mk x) Ag).left → ∀ (m : ℕ) (b : Fin m → LB.Sec (LPow A L k (Over.mk y))) (b' : Fin m → LB.Sec (LPow Ag (L.pull φ) k (Over.mk x))), (∀ i, b' i = GlobalTheory.SecTwist.pullSec (chartPullLinComb L φ (fun _ : Fin 1 => (snd (Over.mk x) Ag).left) (fun _ : Fin 1 => (snd (Over.mk y) A).left) (fun _ => k) h hc) (b i)) → LinearIndependent Γ((Over.mk y).left, ⊤) (fun i => (SecM.ofSec A (b i) : SecM A L k (Over.mk y))) → Submodule.span Γ((Over.mk y).left, ⊤) (Set.range fun i => (SecM.ofSec A (b i) : SecM A L k (Over.mk y))) = ⊤ → LinearIndependent Γ((Over.mk x).left, ⊤) (fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) k (Over.mk x))) ∧ Submodule.span Γ((Over.mk x).left, ⊤) (Set.range fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) k (Over.mk x))) = ⊤ := by
  first | (exact @GlobalTheory.SecBasisTransfer.bases_transfer) | (exact GlobalTheory.SecBasisTransfer.bases_transfer) | (intros; apply GlobalTheory.SecBasisTransfer.bases_transfer  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.exists_birigidified_bundle_of_descent : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (M : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b M s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (ψ : o.A ⟶ A'), IsMonHom ψ → ∀ (m : ℕ) (P₀ : LB (G2 A').left), P₀.IsLB → LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P m) (P₀.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) → ∃ P' : LB (G2 A').left, P'.IsLB ∧ (∃ t : (P'.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) ∧ (∃ t : (P'.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) ∧ LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P m) (P'.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) := by
  first | (exact @GlobalTheory.UPel.HT.Hecke.exists_birigidified_of_descent) | (exact GlobalTheory.UPel.HT.Hecke.exists_birigidified_of_descent) | (intros; apply GlobalTheory.UPel.HT.Hecke.exists_birigidified_of_descent  <;> assumption)
end

end

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory
theorem _root_.GlobalTheory.T.cech_twist_nonzero_locus_maps : ∀ (X : Scheme.{0}) (F : X.Modules) [F.IsQuasicoherent] (L : LB X), L.IsLB → ∀ (σ : L.Sec) {ι : Type} [LinearOrder ι] [Fintype ι] (U : ι → X.Opens), (∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i)) → ∃ (μ : ∀ (j c d : ℕ), c + j = d → (cechCube ℤ (twistZ F L c) ⊤ U ⟶ cechCube ℤ (twistZ F L d) ⊤ U)) (ρ : ∀ c : ℕ, cechCube ℤ (twistZ F L c) ⊤ U ⟶ cechCube ℤ F (nonzeroLocus σ) U), (∀ j c d h, μ j c d h ≫ ρ d = ρ c) ∧ (∀ (j j' c d e : ℕ) (h : c + j = d) (h' : d + j' = e) (h'' : c + (j + j') = e), μ j c d h ≫ μ j' d e h' = μ (j + j') c e h'') ∧ (∀ s : Finset ι, s.Nonempty → ∀ b : (cechCube ℤ F (nonzeroLocus σ) U).obj s, ∃ c : ℕ, ∃ a : (cechCube ℤ (twistZ F L c) ⊤ U).obj s, (ρ c).app s a = b) ∧ (∀ s : Finset ι, s.Nonempty → ∀ (c : ℕ) (a : (cechCube ℤ (twistZ F L c) ⊤ U).obj s), (ρ c).app s a = 0 → ∃ j, (μ j c (c + j) rfl).app s a = 0) := by
  first | exact @_root_.GlobalTheory.cechCube_nonzeroLocus_colimit | exact _root_.GlobalTheory.cechCube_nonzeroLocus_colimit | (intros; apply _root_.GlobalTheory.cechCube_nonzeroLocus_colimit <;> assumption)

end
end

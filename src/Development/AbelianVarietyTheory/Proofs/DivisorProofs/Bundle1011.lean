module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle601
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle858
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle940
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle620
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsHomOfVeryAmpleBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle644
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle117
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle788
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle118
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle821
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle820
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle984
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle876
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle854
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle992
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle987
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.L2ExtensionEtaleCoordinatesFiniteZeros
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle878

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Div.HypFlatBaseChange

theorem square {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {X X' : Scheme.{0}}
    {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X} (w : φ ≫ s = s' ≫ spMap σ)
    {J : Type} [Preorder J] (U : J → X.affineOpens) (hU : Monotone U) (U' : J → X'.affineOpens)
    (hU' : Monotone U') (hle : ∀ i, (U' i).1 ≤ φ ⁻¹ᵁ (U i).1)
    (g : CoefMap σ (hU.functor.op ⋙ OAff s) (hU'.functor.op ⋙ OAff s')) (θ : 𝟭 _ ⟶ g.G)
    (hg : ∀ T b, g.α T (mp (hU.functor.op ⋙ OAff s) (θ.app T) b) =
      GlobalTheory.CechDR.secPull s s' ⟨(U' T.unop, U T.unop), hle _⟩ b) (c : HH1 s) :
    pullHyp1 (CoefMap.restrict (OAff s') hU'.functor.op) (pullHH1 w c) =
      pullHyp1 g (pullHyp1 (CoefMap.restrict (OAff s) hU.functor.op) c) := by
  have hp : Monotone fun i : J ↦ (⟨(U' i, U i), hle i⟩ : Pair φ) := fun i j hij ↦ ⟨hU' hij, hU hij⟩
  have k := congrArg (pullHyp1 (CoefMap.restrict (OPair φ s') hp.functor.op)) (isPull1_pullHH1 w c)
  rw [← pullHyp1_comp, ← pullHyp1_comp] at k
  rw [← pullHyp1_comp]
  have k1 := pullHyp1_eq_of_natTrans
    (F' := hU'.functor.op ⋙ OAff s')
    ((pairRes φ s').comp (CoefMap.restrict (OPair φ s') hp.functor.op))
    (CoefMap.restrict (OAff s') hU'.functor.op) (𝟙 _) (fun T b ↦ mp_id (OAff s') _ b) (pullHH1 w c)
  have k2 := pullHyp1_eq_of_natTrans
    (F' := hU'.functor.op ⋙ OAff s')
    ((pairPull w).comp (CoefMap.restrict (OPair φ s') hp.functor.op))
    ((CoefMap.restrict (OAff s) hU.functor.op).comp g) (Functor.whiskerRight θ hU.functor.op)
    (fun T b ↦ hg T b) c
  exact k1.symm.trans (k.symm.trans k2)

theorem main : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap (algebraMap R R'))), IsSeparated s → QuasiCompact s → Function.Bijective (liftSemi (pullHH1 h.w)) := by
  intro R R' _ _ _ _ X X' s s' φ h hs hq
  obtain ⟨J, _, _, U, hU, hinf, hcov⟩ := GlobalTheory.exists_finite_affine_cover_infClosed R X s hs hq
  haveI : IsAffineHom φ := MorphismProperty.of_isPullback (P := @IsAffineHom) h.flip inferInstance
  let U' : J → X'.affineOpens := fun i ↦ ⟨φ ⁻¹ᵁ (U i).1, (U i).2.preimage φ⟩
  have hU' : Monotone U' := fun i j hij x hx ↦ hU hij hx
  have hinf' : ∀ i j, (U' (i ⊓ j)).1 = (U' i).1 ⊓ (U' j).1 := fun i j ↦ by
    change φ ⁻¹ᵁ (U (i ⊓ j)).1 = _
    rw [hinf]; rfl
  have hcov' : ⨆ i, (U' i).1 = ⊤ := by
    change ⨆ i, φ ⁻¹ᵁ (U i).1 = ⊤
    rw [← Scheme.Hom.preimage_iSup, hcov]; rfl
  have hp : Monotone fun i : J ↦ (⟨(U' i, U i), le_rfl⟩ : Pair φ) := fun i j hij ↦ ⟨hU' hij, hU hij⟩
  haveI : Finite Jᵒᵖ := Finite.of_equiv J Opposite.equivToOpposite
  haveI : ∀ T T' : Jᵒᵖ, Finite (T ⟶ T') := fun T T' ↦
    Finite.of_injective (β := T'.unop ⟶ T.unop) Quiver.Hom.unop Quiver.Hom.unop_inj
  have hb := GlobalTheory.T.deRhamHypercohomologyOne_baseChange_flat_bijective R R' Jᵒᵖ (hU.functor.op ⋙ OAff s) (hU'.functor.op ⋙ OAff s')
    (fun T ↦ GlobalTheory.CechDR.secPull s s' ⟨(U' T.unop, U T.unop), le_rfl⟩)
    (fun a b ↦ (pairPull h.w).naturality (hp.functor.op.map a) b)
    (fun T ↦ semiHom_secPull h.w ⟨(U' T.unop, U T.unop), le_rfl⟩)
    (fun T f hf ↦ GlobalTheory.CechDR.bijective_liftSemi_secPull R R' X X' s s' φ h ⟨(U' T.unop, U T.unop), le_rfl⟩ rfl f hf)
  have hsq := fun c ↦ square h.w U hU U' hU' (fun _ ↦ le_rfl)
    ⟨𝟭 _, fun T ↦ GlobalTheory.CechDR.secPull s s' ⟨(U' T.unop, U T.unop), le_rfl⟩,
      fun a b ↦ (pairPull h.w).naturality (hp.functor.op.map a) b,
      fun T ↦ semiHom_secPull h.w ⟨(U' T.unop, U T.unop), le_rfl⟩⟩ (𝟙 _)
    (fun T b ↦ congrArg (GlobalTheory.CechDR.secPull s s' ⟨(U' T.unop, U T.unop), le_rfl⟩)
      (mp_id (hU.functor.op ⋙ OAff s) T b)) c
  exact (GlobalTheory.Div.BaseChangeIso.main R R' (HH1 s) (Hyp1 (hU.functor.op ⋙ OAff s)) (HH1 s')
    (Hyp1 (hU'.functor.op ⋙ OAff s')) (pullHyp1 (CoefMap.restrict (OAff s) hU.functor.op))
    (pullHyp1 (CoefMap.restrict (OAff s') hU'.functor.op)) (pullHH1 h.w) _
    (GlobalTheory.T.cech_hyper_cohomology_affine_lattice_cover R X s J U hU hinf hcov) (GlobalTheory.T.cech_hyper_cohomology_affine_lattice_cover R' X' s' J U' hU' hinf' hcov') hsq).2 hb

end GlobalTheory.Div.HypFlatBaseChange
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section
namespace GlobalTheory.HomFixUniv.MapIff

theorem eval₂_mul_of_isHomogeneous' {R S σ : Type} [CommRing R] [CommRing S] [Fintype σ] (g : R →+* S)
    (x : σ → S) (u : S) {F : MvPolynomial σ R} {d : ℕ} (hF : F.IsHomogeneous d) :
    MvPolynomial.eval₂ g (fun j => u * x j) F = u ^ d * MvPolynomial.eval₂ g x F := by
  rw [MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ i, m i = d := by
    have := hF (MvPolynomial.mem_support_iff.1 hm)
    rw [← this, Finsupp.weight_apply]
    simp [Finsupp.sum_fintype]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

section
variable {X Z : Scheme.{0}}

def gsH (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) : Γ(X, U) →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ (r ⁻¹ᵁ U) z h).hom.comp (r.app U).hom

theorem gsH_apply (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)) :
    gsH r z U h a = gs r z U a := (gs_eq r z U h a).symm

theorem gs_eval₂Hom {R σ : Type} [CommRing R] (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U)
    (g : R →+* Γ(X, U)) (x : σ → Γ(X, U)) (F : MvPolynomial σ R) :
    gs r z U (MvPolynomial.eval₂Hom g x F) =
      MvPolynomial.eval₂Hom ((gsH r z U h).comp g) (fun j => gs r z U (x j)) F := by
  rw [← gsH_apply r z U h, ← RingHom.comp_apply, MvPolynomial.comp_eval₂Hom]
  congr 2
  funext j
  exact gsH_apply r z U h _

theorem gs_cst_gc {R : Type} [CommRing R] (f : X ⟶ Sp R) (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (c : R) :
    gs r z U (GlobalTheory.AbLaw.cst f U c) = gc (r ≫ f) z c := by
  rw [GlobalTheory.MapToProj.gs_cst f r z U h c, gs_eq _ z ⊤ trivial]
  rfl

theorem gs_eval_cst {R σ : Type} [CommRing R] (f : X ⟶ Sp R) (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U)
    (x : σ → Γ(X, U)) (F : MvPolynomial σ R) :
    gs r z U (MvPolynomial.eval₂Hom (GlobalTheory.AbLaw.cst f U) x F) =
      MvPolynomial.eval₂Hom (gc (r ≫ f) z) (fun j => gs r z U (x j)) F := by
  rw [gs_eval₂Hom r z U h, show (gsH r z U h).comp (GlobalTheory.AbLaw.cst f U) = gc (r ≫ f) z from
    RingHom.ext fun c => (gsH_apply r z U h _).trans (gs_cst_gc f r z U h c)]

end

variable {A₀ B₀ X T : Scheme.{0}} {N : LB A₀} {H : LB B₀} {mA mB : ℕ}

theorem exists_combSec (hN : N.IsLB) (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T)
    (c : Fin mA → Fin mB → Γ(T, ⊤)) : ∃ s : Fin mB → LB.Sec (N.pull φ), ∀ j z q, φ z ∈ N.U q →
      gs (𝟙 X) z ((N.pull φ).U (fun _ => q)) ((s j).f (fun _ => q)) = comb a φ p c z q j := by
  have le : ∀ J : PUnit → N.ι, (N.pull φ).U J ≤ φ ⁻¹ᵁ N.U (J PUnit.unit) := fun J _ hy => mem_pull.1 hy
  let F : Fin mB → ∀ J : PUnit → N.ι, Γ(X, (N.pull φ).U J) := fun j J =>
    ∑ i, (p.appLE ⊤ ((N.pull φ).U J) le_top).hom (c i j) *
      (φ.appLE (N.U (J PUnit.unit)) ((N.pull φ).U J) (le J)).hom ((a i).f (J PUnit.unit))
  have hF : ∀ j (J : PUnit → N.ι) z, z ∈ (N.pull φ).U J →
      gs (𝟙 X) z ((N.pull φ).U J) (F j J) = comb a φ p c z (J PUnit.unit) j := by
    intro j J z hz
    simp only [F, comb]
    rw [GlobalTheory.AmpleSpan.gs_sum' (𝟙 X) z _ hz]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [gs_mul (𝟙 X) z _ hz]
    exact congrArg₂ (· * ·) ((gs_appLE p ⊤ _ _ (𝟙 X) z hz _).trans (by rw [Category.id_comp]))
      ((gs_appLE φ _ _ _ (𝟙 X) z hz _).trans (by rw [Category.id_comp]))
  refine ⟨fun j => ⟨F j, fun J J' => fn_ext fun y hy => ?_⟩, fun j z q hz => hF j _ z (mem_pull.2 hz)⟩
  have hJ : φ y ∈ N.U (J PUnit.unit) := mem_pull.1 hy.1
  have hJ' : φ y ∈ N.U (J' PUnit.unit) := mem_pull.1 hy.2
  rw [gs_res (𝟙 X) y _ hy, gs_mul (𝟙 X) y _ hy, gs_res (𝟙 X) y _ hy, gs_unit (𝟙 X) y _ hy,
    gm_pull_g N φ (𝟙 X) y J J' hy.1 hy.2, hF j J y hy.1, hF j J' y hy.2, Category.id_comp]
  simp only [comb, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gs_compat (a i) φ y hJ hJ']
  ring

end GlobalTheory.HomFixUniv.MapIff

namespace GlobalTheory.HomFixUniv

open MapIff

theorem formsOK_iff_exists_proport : ∀ (Rg : Type) [CommRing Rg] (A₀ B₀ X T : Scheme.{0}) (f : A₀ ⟶ Sp Rg)
    (fB : B₀ ⟶ Sp Rg) (N : LB A₀) (H : LB B₀) (mA mB : ℕ) (a : Fin mA → LB.Sec N) (b : Fin mB → LB.Sec H)
    (φ : X ⟶ A₀) (p : X ⟶ T) (t : T ⟶ Sp Rg) (c : Fin mA → Fin mB → Γ(T, ⊤)),
    GlobalTheory.AmpleSpan.EmbedsBy fB b → H.IsLB → N.IsLB → φ ≫ f = p ≫ t → GlobalTheory.HomFixUniv.Generates a φ p c →
    (GlobalTheory.HomFixUniv.FormsOK a fB b φ p t c ↔
      ∃ Ψ : X ⟶ B₀, Ψ ≫ fB = p ≫ t ∧ GlobalTheory.HomFixUniv.Proport a b φ p Ψ c) := by
  intro Rg _ A₀ B₀ X T f fB N H mA mB a b φ p t c hE hH hN _ hG
  constructor
  · intro hF
    cases mB with
    | zero =>
      have : IsEmpty X := ⟨fun z => by
        obtain ⟨q, hq⟩ := exists_chart hN (φ z)
        obtain ⟨j, -⟩ := hG z q hq
        exact j.elim0⟩
      exact ⟨isInitialOfIsEmpty.to B₀, isInitialOfIsEmpty.hom_ext _ _, fun z => (IsEmpty.false z).elim⟩
    | succ n =>
      obtain ⟨s, hs⟩ := exists_combSec (mB := n + 1) hN a φ p c
      have hva : GlobalTheory.AbLaw.VeryAmpleBy fB H b := (GlobalTheory.AmpleSpan.embedsBy_spec_iff fB b).1 hE
      have hcov : ⨆ j, nonzeroLocus (s j) = ⊤ := by
        refine eq_top_iff.2 fun z _ => ?_
        obtain ⟨q, hq⟩ := exists_chart hN (φ z)
        obtain ⟨j, hj⟩ := hG z q hq
        have hk : (𝟙 X : X ⟶ X) z ∈ (N.pull φ).U (fun _ => q) := mem_pull.2 hq
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, (GlobalTheory.AmpleSpan.mem_nonzeroLocus_iff_gs (s j) (𝟙 X) z hk).2
          (by rw [hs j z q hq]; exact hj)⟩
      have hforms : ∀ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) Rg), F.IsHomogeneous d →
          (∀ k : H.ι, MvPolynomial.eval₂Hom (GlobalTheory.AbLaw.cst fB (H.U k)) (fun j => (b j).f k) F = 0) →
          ∀ k : (N.pull φ).ι,
            MvPolynomial.eval₂Hom (GlobalTheory.AbLaw.cst (p ≫ t) ((N.pull φ).U k)) (fun j => (s j).f k) F = 0 := by
        intro d F hFd hK k
        obtain ⟨q, rfl⟩ : ∃ q, k = fun _ => q := ⟨k PUnit.unit, rfl⟩
        refine fn_ext fun z hz => ?_
        have hq : φ z ∈ N.U q := mem_pull.1 hz
        have e : (fun j => gs (𝟙 X) z ((N.pull φ).U (fun _ => q)) ((s j).f (fun _ => q))) = comb a φ p c z q :=
          funext fun j => hs j z q hq
        rw [gs_eval_cst (p ≫ t) (𝟙 X) z _ hz, Category.id_comp, e, gs_eq (𝟙 X) z _ hz 0, map_zero, map_zero]
        exact hF d F hFd hK z q hq
      obtain ⟨Ψ, w, hΨ, -, hrel⟩ := GlobalTheory.exists_hom_of_veryAmpleBy Rg B₀ fB H n b hH hva X (p ≫ t) (N.pull φ) s
        (LB.isLB_linComb hN _ _) hcov hforms
      refine ⟨Ψ, hΨ, fun z q k hq hk j j' => ?_⟩
      have hz : z ∈ (N.pull φ).U (fun _ => q) := mem_pull.2 hq
      rw [hrel j z k (fun _ => q) hk hz, hrel j' z k (fun _ => q) hk hz, hs j z q hq, hs j' z q hq]
      ring
  · rintro ⟨Ψ, hΨ, hP⟩ d F hFd hK z q hq
    obtain ⟨j₀, hj₀⟩ := hG z q hq
    obtain ⟨j', hj'⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show Ψ z ∈ ⨆ j, nonzeroLocus (b j) by rw [hE.1]; trivial)
    obtain ⟨k, hk⟩ := GlobalTheory.AmpleSpan.exists_chart_of_mem (b j') hj'
    have hu' : IsUnit (gs Ψ z _ ((b j').f k)) := (GlobalTheory.AmpleSpan.mem_nonzeroLocus_iff_gs (b j') Ψ z hk).1 hj'
    have hPr := hP z q k hq hk
    have hB0 : IsUnit (gs Ψ z (H.U k) ((b j₀).f k)) := by
      have hu : IsUnit (gs Ψ z (H.U k) ((b j₀).f k) * comb a φ p c z q j') := hPr j' j₀ ▸ hu'.mul hj₀
      exact isUnit_of_mul_isUnit_left hu
    obtain ⟨u, hu⟩ := hj₀
    have hBC : ∀ j, gs Ψ z (H.U k) ((b j).f k) =
        (gs Ψ z (H.U k) ((b j₀).f k) * ↑u⁻¹) * comb a φ p c z q j := fun j => by
      have h1 := hPr j j₀
      rw [← hu] at h1
      calc gs Ψ z (H.U k) ((b j).f k) = gs Ψ z (H.U k) ((b j).f k) * ↑u * ↑u⁻¹ := by simp
        _ = gs Ψ z (H.U k) ((b j₀).f k) * comb a φ p c z q j * ↑u⁻¹ := by rw [h1]
        _ = _ := by ring
    have hK' := congrArg (gs Ψ z (H.U k)) (hK k)
    rw [gs_eval_cst fB Ψ z _ hk, hΨ, gs_eq Ψ z _ hk 0, map_zero, map_zero, funext hBC,
      MvPolynomial.coe_eval₂Hom, eval₂_mul_of_isHomogeneous' _ _ _ hFd] at hK'
    have hl : IsUnit ((gs Ψ z (H.U k) ((b j₀).f k) * ↑u⁻¹) ^ d) := (hB0.mul u⁻¹.isUnit).pow d
    rw [MvPolynomial.coe_eval₂Hom]
    exact hl.mul_right_eq_zero.1 hK'

end GlobalTheory.HomFixUniv
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES

theorem tjAt_pull_one_left {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    (1 : T ⟶ G').left ≫ φ = (1 : Over.mk (T.hom ≫ f) ⟶ G).left := by
  have hw : ((1 : T ⟶ G').left ≫ φ) ≫ G.hom = (Over.mk (T.hom ≫ f)).hom := by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]
    rfl
  let x₀ : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ φ) hw
  have e := h.2 T 1 1 x₀ x₀ rfl rfl
  rw [_root_.mul_one] at e
  have hxx : x₀ * x₀ = x₀ := by
    ext
    exact e
  have h1 : x₀ = 1 := mul_eq_right.mp hxx
  exact congrArg Over.Hom.left h1

theorem tjAt_iff_tjAt_pull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (T Y : Scheme.{0}) (s₁ : T ⟶ Sp R) (s : Y ⟶ Sp R) (t : T ⟶ Y) (o₁ : Obj b N s₁) (o : Obj b N s) (m : ObjMap o₁ o t) (B₁ : Over T) [GrpObj B₁] [IsCommMonObj B₁] (B : Over Y) [GrpObj B] [IsCommMonObj B] (θ : B₁.left ⟶ B.left) (ψ₁ : o₁.A ⟶ B₁) (ψ : o.A ⟶ B) (r : ℤ) (w : Ideal (𝓞 D.F)) (j : ℕ), IsGrpPullback B₁ B t θ → m.φ ≫ ψ.left = ψ₁.left ≫ θ → (TjAt r w j o ψ t ↔ TjAt r w j o₁ ψ₁ (𝟙 T)) := by
  intro p _ D R _ b N T Y s₁ s t o₁ o m B₁ _ _ B _ _ θ ψ₁ ψ r w j hB hψ
  have key : ∀ (k : Type) [Field k] (σ : Sp k ⟶ T),
      ((∀ g : Over.mk (σ ≫ t) ⟶ o.A, g ≫ ψ = 1 → (∃ e : ℕ, KilledBy o (uIdeal D r ^ e) g) → KilledBy o w g) ∧
        Nat.card {g : Over.mk (σ ≫ t) ⟶ o.A // g ≫ ψ = 1 ∧ KilledBy o w g} = Ideal.absNorm w ^ (D.m * j)) ↔
      ((∀ g : Over.mk σ ⟶ o₁.A, g ≫ ψ₁ = 1 → (∃ e : ℕ, KilledBy o₁ (uIdeal D r ^ e) g) → KilledBy o₁ w g) ∧
        Nat.card {g : Over.mk σ ⟶ o₁.A // g ≫ ψ₁ = 1 ∧ KilledBy o₁ w g} = Ideal.absNorm w ^ (D.m * j)) := by
    intro k _ σ
    obtain ⟨e, he, -⟩ := m.exists_ptEquiv (Over.mk (σ ≫ t)) σ rfl
    have hker : ∀ g : Over.mk σ ⟶ o₁.A, e g ≫ ψ = 1 ↔ g ≫ ψ₁ = 1 := by
      intro g
      have h1 : (e g ≫ ψ).left = (g ≫ ψ₁).left ≫ θ := by
        rw [Over.comp_left, he, Category.assoc, hψ, Over.comp_left, Category.assoc]
      have h2 : (1 : Over.mk (σ ≫ t) ⟶ B).left = (1 : Over.mk σ ⟶ B₁).left ≫ θ :=
        (tjAt_pull_one_left hB (Over.mk σ)).symm
      constructor
      · intro h
        apply Over.OverMorphism.ext
        apply hB.1.hom_ext
        · rw [← h1, ← h2, h]
        · rw [Over.w, Over.w]
      · intro h
        apply Over.OverMorphism.ext
        rw [h1, h2, h]
    have hact : ∀ (g : Over.mk σ ⟶ o₁.A) (c : D.O), e g ≫ o.act.act c = e (g ≫ o₁.act.act c) := fun g c => by
      ext
      rw [Over.comp_left, he, he, Over.comp_left, Category.assoc, Category.assoc, m.act]
    have hkill : ∀ (v : Ideal (𝓞 D.F)) (g : Over.mk σ ⟶ o₁.A), KilledBy o v (e g) ↔ KilledBy o₁ v g :=
      fun v g => forall₂_congr fun a _ => by rw [hact]; exact map_eq_one_iff _ e.injective
    refine and_congr ⟨fun h g hg hu => ?_, fun h g hg hu => ?_⟩ ?_
    · rw [← hkill]
      rw [← hker] at hg
      obtain ⟨n, hn⟩ := hu
      exact h (e g) hg ⟨n, (hkill _ g).2 hn⟩
    · obtain ⟨g₀, rfl⟩ := e.surjective g
      rw [hkill]
      rw [hker] at hg
      obtain ⟨n, hn⟩ := hu
      exact h g₀ hg ⟨n, (hkill _ g₀).1 hn⟩
    · rw [Nat.card_congr ((Equiv.subtypeEquiv e.toEquiv fun g₀ => by
        change _ ↔ e g₀ ≫ ψ = 1 ∧ KilledBy o w (e g₀)
        rw [hker, hkill]).symm)]
  constructor
  · intro h k _ _ _ x₁ _
    exact (key k x₁).1 (h k (x₁ ≫ t) ⟨x₁, rfl⟩)
  · intro h k _ _ _ x ⟨σ, hσ⟩
    subst hσ
    exact (key k σ).2 (h k σ ⟨σ, Category.comp_id σ⟩)

end GlobalTheory.UPel.HT.ES
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.ActFin.DiagPow

theorem eSec_diag {S : Scheme.{0}} (A : Over S) [GrpObj A] :
    eSec A ≫ (lift (𝟙 A) (𝟙 A)).left = eSec A ≫ (lift (1 : A ⟶ A) (𝟙 A)).left := by
  unfold eSec
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  rw [comp_lift, comp_lift]
  congr 1
  rw [Hom.one_def, ← Category.assoc, Category.comp_id, toUnit_unique (η[A] ≫ toUnit A) (𝟙 _), Category.id_comp]

theorem diagPow_isLB_rigidified_relAmple : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A]
    (Q : LB (A ⊗ A).left), QHyp A Q → ∀ (d : ℕ), 0 < d →
      (diagPow A Q d).IsLB ∧ Out.Rigidified A (diagPow A Q d) ∧ Out.RelAmple A (diagPow A Q d) := by
  intro S A _ _ Q hQ d hd
  obtain ⟨hA, hQL, ⟨t₁, ht₁⟩, -, -, hamp⟩ := hQ
  have hM : (Q.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hQL _
  have hD : (diagPow A Q d).IsLB := LB.isLB_linComb hQL _ _
  have hcls : CechPic.cls _ hD = d • CechPic.cls _ hM := by
    refine (CechPic.cls_linComb hQL (K := Fin 1) (fun _ => (lift (𝟙 A) (𝟙 A)).left) (fun _ => (d : ℤ)) hD).trans ?_
    rw [Fintype.sum_unique, CechPic.cls_pull hQL _ hM]
    exact natCast_zsmul _ d
  refine ⟨hD, ?_, GlobalTheory.SiegelOfTheta.relAmple_of_pow hA hM hD hd hcls hamp⟩
  have h₁ : CechPic.cls _ (pull_isLB hQL (lift (1 : A ⟶ A) (𝟙 A)).left) = 0 :=
    (CechPic.cls_eq_zero_iff _).2 ⟨t₁, ht₁⟩
  refine (CechPic.cls_eq_zero_iff (pull_isLB hD (eSec A))).1 ?_
  rw [CechPic.cls_pull hD, hcls, map_nsmul, CechPic.cls_pull hQL, ← CechPic.pull_comp, eSec_diag,
    CechPic.pull_comp, ← CechPic.cls_pull hQL _ (pull_isLB hQL _), h₁, map_zero, nsmul_zero]

end GlobalTheory.ActFin.DiagPow
end
end

section

namespace GlobalTheory.GenericProduct

theorem oneGenericVector : OneGenericVector := GlobalTheory.T.whittakerSpaceDim_parabolicInduction_cuspidal_eq_one

theorem genericMultOne_holds : GlobalTheory.IndefiniteRowSideFullHecke.GenericMultiplicityOne.GenericMultOne := genericMultOne oneGenericVector

theorem oneWhittakerVector_holds : GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.OneWhittakerVector :=
  GlobalTheory.CuspidalIdempotentCharacters.genericMultOne_iff.1 genericMultOne_holds

end GlobalTheory.GenericProduct
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_lieCondition_summand_residueCharP : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] (I : Ideal C), I ^ 2 = ⊥ → (p : C) ∈ IsLocalRing.maximalIdeal C → ∀ (tR : R →+* C) (H : Type 1) [AddCommGroup H] [Module C H] [Module.Finite C H] [Module.Projective C H] (ρ : D.O →+* Module.End C H), (letI := GlobalTheory.HTSummand.tensorModOf (ρ.comp (algebraMap (𝓞 D.F) D.O)); Module.Projective (C ⊗[ℤ] 𝓞 D.F) H) → ∀ (e : Module.End C H), e * e = e → (∀ c, ρ c * e = e * ρ c) → (∀ x, ρ (algebraMap (𝓞 D.F) D.O D.ω) (e x) = tR b.ρ • e x) → ∀ (F : Submodule C H), I • ⊤ ≤ F → (∀ (c : D.O), ∀ x ∈ F, ρ c x ∈ F) → (∀ x ∈ F, e x ∈ F) → (∃ E' M : Submodule C H, IsCompl E' M ∧ E' ⊔ I • ⊤ = F) → (∀ d ∈ LinearMap.range e, ∃ w : Fin D.a → H, (∀ i (c : 𝓞 D.F), ρ (algebraMap (𝓞 D.F) D.O c) (w i) - tR (b.t i c) • w i ∈ F) ∧ d - ∑ i, w i ∈ F) → ∃ G M : Submodule C H, G ⊓ M = ⊥ ∧ G ⊔ M = LinearMap.range e ∧ (∀ (c : D.O), ∀ x ∈ G, ρ c x ∈ G) ∧ G ⊔ (I • ⊤ ⊓ LinearMap.range e) = F ⊓ LinearMap.range e ∧ ∀ d ∈ LinearMap.range e, ∃ w : Fin D.a → H, (∀ i (c : 𝓞 D.F), ρ (algebraMap (𝓞 D.F) D.O c) (w i) - tR (b.t i c) • w i ∈ G) ∧ d - ∑ i, w i ∈ G := by
  first | exact @GlobalTheory.HTSummand.Corep.exists_summand_lie_p | exact GlobalTheory.HTSummand.Corep.exists_summand_lie_p | (intros; apply GlobalTheory.HTSummand.Corep.exists_summand_lie_p <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.DeRham GlobalTheory.DeRhamSheaf

namespace GlobalTheory.LinFrob

open GlobalTheory.Twist GlobalTheory.ConjSeq

theorem pull_frobDR (p : ℕ) [Fact p.Prime] {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
    (hR : (p : R) = 0) (hR' : (p : R') = 0) {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp R')}
    [GrpObj A'] {φ : A'.left ⟶ A.left} (hφ : IsGrpPullback A' A (spMap (algebraMap R R')) φ)
    (c : primDR A) :
    (GlobalTheory.Published.AbelianDeRham.bcMor hφ).pull (frobDR p R hR A c) =
      frobDR p R' hR' A' ((GlobalTheory.Published.AbelianDeRham.bcMor hφ).pull c) := by
  have k := (frobMor p R hR A (cast_left p R hR A)).comp (GlobalTheory.Published.AbelianDeRham.bcMor hφ)
  refine (GrpMor.pull_pull _ _ k (fun _ ↦ rfl) rfl c).trans
    (GrpMor.pull_pull _ _ k (fun r ↦ ?_) (GlobalTheory.VB.frob_naturality p _ φ _) c).symm
  rw [RingHom.comp_apply, frobR_apply, frobR_apply, map_pow]

theorem frobDR_smul (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] (hR : (p : R) = 0)
    {A : Over (Sp R)} [GrpObj A] (r : R) (c : primDR A) :
    frobDR p R hR A (r • c) = r ^ p • frobDR p R hR A c := by
  rw [LinearMap.map_smulₛₗ, frobR_apply]

end GlobalTheory.LinFrob
end
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.l2_extension_etale_coordinates_finite_zeros : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), 1 ≤ n → ∀ (E L : La) (s : Fin n → ι → Y → ℂ), (∀ k, A.IsSec L (s k)) → ∀ hS : (A.zeroSet s).Finite, (∀ P ∈ A.zeroSet s, jacAt A s P ≠ 0) → (∀ y, A.sqn L s y ≤ 1) → ∀ δ : ℝ, 0 < δ → (∀ α ∈ Set.Icc (1 : ℝ) (1 + δ), ∀ i y, y ∈ (A.chart i).source → y ∉ A.zeroSet s → ∀ ξ : Fin n → ℂ, 0 ≤ A.leviAt i (fun x => A.ph E i x + α * psi A L s x) y ξ) → ∀ (Λ : La) (τ : ι → Y → ℂ) (z : Y → V n) (β : ι → Y → ℂ), (A.IsSec Λ τ ∧ A.Pos Λ (fun _ => 0) ∧ Etale A (nz A τ) z ∧ A.IsFrameOn (A.kap + E) (nz A τ) β ∧ Dense (nz A τ) ∧ ∃ C : ℝ, 0 < C ∧ ∀ y, A.nsq Λ τ y ≤ C * A.sqn L s y) → ∀ f : Y → ℂ, ∃ F : ι → Y → ℂ, A.IsSec (A.kap + E) F ∧ (∀ P ∈ A.zeroSet s, F (A.pick P) P = f P) ∧ ∫⁻ y, ENNReal.ofReal (2 ^ n * (1 / (1 + (δ * psi A L s y) ^ 2) * A.nsq (A.kap + E) F y * Real.exp (-psi A L s y))) ∂A.mu ≤ ENNReal.ofReal (34 / δ * (resConst n * ∑ P ∈ hS.toFinset, resSq A E L s P (f P))) := by
  first | exact @GlobalTheory.l2_extension_of_etale_coordinates | exact GlobalTheory.l2_extension_of_etale_coordinates | (intros; apply GlobalTheory.l2_extension_of_etale_coordinates <;> assumption)
end

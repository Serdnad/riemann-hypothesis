module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.InvariantVectorFieldsBasisVerticalDerivations
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle006
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle049
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsPowerGrowthVolumePullFiniteEndomorphism
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinrankSectionsPullbackMulByNTwists
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilPairingOfPolarisationFormLinComb
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqBasicOpen
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle003
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsIntegralOfIsAbelianSchemeField
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHomOfDerivation
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle103
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle051
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle102
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle105
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle050
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle061
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle107
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle106
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
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
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.PowDominates

open LBGerm GlobalTheory.AbLaw GlobalTheory.TwistGen ReciprocityTheory.ChartRestriction.G.Out

variable {X : Scheme.{0}}

def chartPullTw (L N : LB X) (t : ℕ) : ChartPull (LB.div (lbPow L t) N) (tw (pw N (-1)) L (t : ℤ)) (𝟙 X) where
  idx p := (p.2, p.1 PUnit.unit)
  le _ _ hy := ⟨hy.2, mem_powChart.1 hy.1⟩
  g y p q hp hq := by
    refine (gm_div N (lbPow L t) (𝟙 X) y p q ⟨hp, hq⟩).trans (Eq.symm (Units.ext ?_))
    refine (gm_tw_g (pw N (-1)) L t y (p.2, p.1 PUnit.unit) (q.2, q.1 PUnit.unit)
      ⟨hp.2, mem_powChart.1 hp.1⟩ ⟨hq.2, mem_powChart.1 hq.1⟩).trans ?_
    rw [gm_lbPow_g t (𝟙 X) y p.1 q.1 hp.1 hq.1, ← Units.val_pow_eq_pow_val, ← Units.val_mul, _root_.mul_comm]
    refine congrArg Units.val (congrArg₂ (· * ·) rfl ?_)
    exact (map_zpow _ _ _).trans (zpow_neg_one _)

theorem exists_sec_div [CompactSpace X] [QuasiSeparatedSpace X] {L N : LB X} (hL : L.IsLB) (hN : N.IsLB) {n : ℕ}
    (s : (lbPow L n).Sec) (ha : IsAffineOpen (nonzeroLocus s)) (y : X) (hy : y ∈ nonzeroLocus s) :
    ∃ (t : ℕ) (u : (LB.div (lbPow L t) N).Sec), y ∈ nonzeroLocus u := by
  obtain ⟨k, hk⟩ := exists_chart hN y
  obtain ⟨a, hle, hya⟩ := ha.exists_basicOpen_le (V := N.U k) ⟨y, hk⟩ hy
  obtain ⟨m, -, σ, hσ⟩ := exists_nonzeroLocus_eq_basicOpen hL s a
  obtain ⟨e, u, hu⟩ := exists_sec_of_le_chart (M := pw N (-1)) (isLB_pw hN (-1)) hL (n * m) (powSecFn σ)
    (fun z j j' hj hj' => by
      have hz : z ∈ L.U j ⊓ L.U j' := ⟨hj, hj'⟩
      have e := congrArg (gs (𝟙 X) z _) (powSecFn_compat σ j j')
      rwa [gs_res _ z _ hz, gs_mul _ z _ hz, gs_res _ z _ hz, gs_pow _ z _ hz, gs_unit _ z _ hz] at e)
    (X.basicOpen a) (fun z j hj => by
      rw [isUnit_gs_iff (𝟙 X) z _ hj, ← nonzeroLocus_inf_powSecFn, hσ]
      exact ⟨fun h => ⟨h, hj⟩, fun h => h.1⟩) k hle
  refine ⟨n * m * e, chartSec (chartPullTw L N _) u, ?_⟩
  rw [nonzeroLocus_chartSec_id (chartPullTw L N _) u fun z j hj =>
    ⟨((fun _ => j.2 : PUnit → L.ι), j.1),
      (⟨mem_powChart.2 hj.2, hj.1⟩ : z ∈ powChart L (fun _ => j.2) ⊓ N.U j.1)⟩]
  exact hu hya

theorem exists_f_ne_zero {M : LB X} (u : M.Sec) {y : X} (hy : y ∈ nonzeroLocus u) : ∃ j, u.f j ≠ 0 := by
  have hy' : y ∈ ⨆ k, X.basicOpen (u.f k) := hy
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hy'
  refine ⟨k, fun h0 => ?_⟩
  rw [h0, Scheme.basicOpen_zero] at hk
  exact absurd hk (by simp)

end GlobalTheory.PowDominates

namespace GlobalTheory

open PowDominates

theorem exists_sec_lbPow_div_ne_zero : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N : LB P.A.left), N.IsLB → ∃ (n : ℕ) (s : (LB.div (lbPow P.L n) N).Sec), ∃ j, s.f j ≠ 0 := by
  intro h K _ _ P N hN
  obtain ⟨m, s, hc, hs⟩ := veryAmple_lbPow h.ample K P 4 le_rfl
  have := polAV_isIntegral_of_isAlgClosed K P
  obtain ⟨_, _⟩ := TwistGen.compact_quasiSeparated (isLB_lbPow P.isLB 4) s hc fun i => (hs i).1
  obtain ⟨y⟩ : Nonempty P.A.left := inferInstance
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show y ∈ ⨆ i, Out.nonzeroLocus (s i) by rw [hc]; trivial)
  obtain ⟨t, u, hu⟩ := exists_sec_div P.isLB hN (s i) (hs i).1 y hi
  exact ⟨t, u, exists_f_ne_zero u hu⟩

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

theorem _root_.GlobalTheory.T.invariantVectorFields_basis_verticalDerivations : ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (g : ℕ) (v : Fin g → (epsR K ⟶ A₀)) (dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)), Smooth A₀.hom → IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (R : Type) [CommRing R] (x₀ : R →+* K) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : A₀.left ⟶ X), IsPullback m A₀.hom p (spMap x₀) → ∀ (T : Scheme.{0}) (y : T ⟶ A₀.left) (W₀ : X.Opens) (d : ∀ W : X.Opens, Γ(X, W) → Γ(T, (y ≫ m) ⁻¹ᵁ W)), LocDerK (y ≫ A₀.hom) p (y ≫ m) (fun _ => 0) W₀ d → ∃! c : Fin g → Γ(T, (y ≫ m) ⁻¹ᵁ W₀), ∀ W, W ≤ W₀ → ∀ f, d W f = ∑ a, rsT (c a) _ * pbT y (dd a (m ⁻¹ᵁ W) ((m.app W).hom f)) _ := by
  first | exact @GlobalTheory.InvFieldBasis.existsUnique_coeff | exact GlobalTheory.InvFieldBasis.existsUnique_coeff | (intros; apply GlobalTheory.InvFieldBasis.existsUnique_coeff <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ThetaObjPull

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A']
  {φ : A'.left ⟶ A.left}

theorem pushHom_injective (h : IsGrpPullback A' A f φ) (T : Over S') : Function.Injective (pushHom h T) :=
  fun x y e => Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun z => z.left) e) (by rw [Over.w, Over.w]))

theorem pushHom_surjective (h : IsGrpPullback A' A f φ) (T : Over S') : Function.Surjective (pushHom h T) :=
  fun y => ⟨Over.homMk (h.1.lift y.left T.hom (Over.w y)) (h.1.lift_snd _ _ _),
    Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

theorem map_linComb {T : Over S} {T' : Over S'} (ρ : (T' ⟶ A') →* (T ⟶ A)) {n : ℕ} (y : Fin n → (T' ⟶ A'))
    (a : Fin n → ℕ) : ρ (Out.linComb y a) = Out.linComb (fun i => ρ (y i)) a := by
  unfold Out.linComb
  rw [map_list_prod, List.map_ofFn]
  congr 2
  funext i
  exact map_pow ρ _ _

def toBase (f : S' ⟶ S) : Over.mk ((Out.baseOver S').hom ≫ f) ⟶ Out.baseOver S := Over.homMk f (by simp)

theorem exists_sec (h : IsGrpPullback A' A f φ) (x : Out.baseOver S ⟶ A) :
    ∃ x' : Out.baseOver S' ⟶ A', pushHom h _ x' = toBase f ≫ x :=
  pushHom_surjective h _ _

end GlobalTheory.ThetaObjPull

namespace GlobalTheory

open ThetaObjPull PolBaseChange

theorem tObj_pull : ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (S S' : Scheme.{0})
    (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (f : S' ⟶ S) (t : TObj g k J b s), f ≫ s = s' →
    ∃ t' : TObj g k J b s', TMap t' t f := by
  intro o _ g k J b S S' s s' f t hs
  subst hs
  have h := isGrpPullback_pullback t.A f
  have hL' := pull_isLB t.isLB (pullback.fst t.A.hom f)
  have hiso := lbIso_refl hL'
  obtain ⟨hab, hamp, hk⟩ := pol_pull _ _ _ _ _ _ _ _ t.isLB hL' t.ab h hiso
  choose pt hpt using fun i => exists_sec h (t.pt i)
  have hpt' : ∀ i, (pt i).left ≫ pullback.fst t.A.hom f = f ≫ (t.pt i).left := fun i =>
    congrArg (fun z => z.left) (hpt i)
  have := t.hom
  have := t.ab.comm
  refine ⟨{ A := (Over.pullback f).obj t.A
            ab := hab
            dim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 t.dim
            L := t.L.pull (pullback.fst t.A.hom f)
            isLB := hL'
            rigid := rigidified_pull h t.rigid
            sym := sym_pull h t.sym
            ample := hamp t.ample
            ktriv := hk t.ktriv
            pt := pt
            torsion := fun i => pushHom_injective h _ ?_
            bij := fun K _ _ x y hy => ?_
            pairing := fun i j => ?_
            act := fun j => (Over.pullback f).map (t.act j)
            hom := fun j => inferInstance }, pullback.fst t.A.hom f, h, hiso, hpt', fun j => pullback.lift_fst _ _ _⟩
  · rw [map_pow, map_one, hpt]
    exact (map_pow (preHom (toBase f)) _ _).symm.trans (by rw [t.torsion, map_one])
  · have key : ∀ c : Ix g k, pushHom h (Over.mk x) (Out.linComb (fun i =>
        (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S') ≫ pt i) (fun i => (c i).val)) =
        Out.linComb (fun i => (Over.homMk (x ≫ f) (by simp) : Over.mk (x ≫ f) ⟶ Out.baseOver S) ≫ t.pt i)
          (fun i => (c i).val) := fun c => by
      rw [map_linComb]
      congr 1
      funext i
      apply Over.OverMorphism.ext
      show (x ≫ (pt i).left) ≫ _ = (x ≫ f) ≫ (t.pt i).left
      rw [Category.assoc, hpt', Category.assoc]
    have hy' : pushHom h (Over.mk x) y ^ k = 1 := by rw [← map_pow, hy, map_one]
    obtain ⟨c, hc, hu⟩ := t.bij K (x ≫ f) (pushHom h (Over.mk x) y) hy'
    exact ⟨c, pushHom_injective h _ ((key c).trans hc), fun c' hc' => hu c' ((key c').symm.trans (congrArg _ hc'))⟩
  · refine (weilIs_grpPullback_of_comm _ _ _ _ f _ _ _ t.isLB hL' h hiso (Out.baseOver S') k (pt i) (pt j)
      (toBase f ≫ t.pt i) (toBase f ≫ t.pt j) _ (hpt' i).symm (hpt' j).symm).2 ?_
    have w := CommPairing.weilIs_pull globalFns_holds t.ab t.isLB (toBase f) (t.pairing i j)
    rw [map_zpow] at w
    have e : Units.map (toBase f).left.appTop.hom.toMonoidHom (unitS s b.ζ) = unitS (f ≫ s) b.ζ := by
      apply Units.ext
      show f.appTop.hom (s.appTop.hom _) = (f ≫ s).appTop.hom _
      rw [Scheme.Hom.comp_appTop]
      rfl
    exact e ▸ w

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS

theorem exists_isConstK_of_locDerK :
    Out.Laws → ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (R : Type) [CommRing R] (xD : R →+* DualNumber K) (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (ψ : A'.left ⟶ A.left) (j : A₀.left ⟶ A'.left) (d : ∀ W : A.left.Opens, Γ(A.left, W) → Γ(A₀.left, (j ≫ ψ) ⁻¹ᵁ W)), IsAbelianScheme A₀ → IsAbelianScheme A' → IsGrpPullback A' A (spMap xD) ψ → IsGrpPullback A₀ A' (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) j → LocDerK A₀.hom A.hom (j ≫ ψ) (fun r => (xD r).snd) ⊤ d → ∃ ρ, IsConstK A' A₀ ρ j := by
  intro hL K _ A₀ _ R _ xD A _ A' _ ψ j d hA₀ hA' hψ hj hd

  have hra : spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ spMap (algebraMap K (DualNumber K)) = 𝟙 (Sp K) := by
    rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    convert Spec.map_id (CommRingCat.of K)
    ext x
    simp
  have : Flat A₀.hom := inferInstance

  have hρ : IsPullback (pullback.fst A₀.hom (spMap (algebraMap K (DualNumber K)))) (pullback.snd _ _)
      A₀.hom (spMap (algebraMap K (DualNumber K))) := IsPullback.of_hasPullback _ _
  obtain ⟨j₀, hj₀ρ, hj₀π⟩ : ∃ j₀ : A₀.left ⟶ pullback A₀.hom (spMap (algebraMap K (DualNumber K))),
      j₀ ≫ pullback.fst _ _ = 𝟙 _ ∧
        j₀ ≫ pullback.snd _ _ = A₀.hom ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom :=
    ⟨pullback.lift (𝟙 _) (A₀.hom ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom)
      (by rw [Category.assoc, hra, Category.comp_id, Category.id_comp]),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hj₀ : IsPullback j₀ A₀.hom (pullback.snd A₀.hom (spMap (algebraMap K (DualNumber K))))
      (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) := by
    refine IsPullback.of_right ?_ hj₀π hρ
    rw [hj₀ρ, hra]
    exact IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩

  have hm : (j ≫ ψ) ≫ A.hom = A₀.hom ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ spMap xD := by
    rw [Category.assoc, hψ.1.w, ← Category.assoc, hj.1.w, Category.assoc]
  obtain ⟨Φ, hΦj, hΦp, -⟩ := DerMorK.exists_hom_of_derivation K A₀.left _ A₀.hom (pullback.snd _ _)
    (pullback.fst _ _) j₀ hρ hj₀ρ hj₀π R xD A.left A.hom (j ≫ ψ) d hm hd

  obtain ⟨e, heψ, heh⟩ : ∃ e : pullback A₀.hom (spMap (algebraMap K (DualNumber K))) ⟶ A'.left,
      e ≫ ψ = Φ ∧ e ≫ A'.hom = pullback.snd _ _ :=
    ⟨hψ.1.lift Φ _ hΦp, hψ.1.lift_fst _ _ _, hψ.1.lift_snd _ _ _⟩
  have hje : j₀ ≫ e = j := by
    apply hψ.1.hom_ext
    · rw [Category.assoc, heψ, hΦj]
    · rw [Category.assoc, heh, hj₀π, hj.1.w]

  have : IsIso e := GlobalTheory.T.isIso_of_id_mod_eps_thickening K A₀.left _ A'.left A₀.hom (pullback.snd _ _) A'.hom j₀ j e hj₀ hj.1
    inferInstance heh hje
  refine exists_isConstK_of_isPullback hL K A₀ A' (inv e ≫ pullback.fst _ _) j hA₀ hA' hj ?_ ?_
  · have h1 : IsPullback (inv e) A'.hom (pullback.snd A₀.hom (spMap (algebraMap K (DualNumber K)))) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, IsIso.inv_comp_eq, heh]⟩
    have h2 := h1.paste_horiz hρ
    rwa [Category.id_comp] at h2
  · rw [← hje, Category.assoc, IsIso.hom_inv_id_assoc, hj₀ρ]

end GlobalTheory.KS
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

namespace GlobalTheory.FormFinite

open GlobalTheory.CechPic GlobalTheory.AmpleStabFinite

theorem lam_inv_eq {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] (m l : CechPic.Pic A.left) (s : A ⟶ A)
    [IsMonHom s] (h : ∀ u v : T ⟶ A, lam m u v = lam l u (v ≫ s)) {x y : T ⟶ A} (e : x ≫ s = y ≫ s) :
    lam m x⁻¹ x = lam m y y⁻¹ := by
  rw [h, e, ← h, lam_comm, h, GrpObj.inv_comp, e, ← GrpObj.inv_comp, ← h]

theorem isFinite_of_lam_eq {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] [IsProper A.hom]
    {M : LB A.left} (hM : IsAmpleLB M) (l : CechPic.Pic A.left) (s : A ⟶ A) [IsMonHom s]
    (h : ∀ (T : Over (Sp K)) (u v : T ⟶ A), lam (cls M hM.isLB) u v = lam l u (v ≫ s)) : IsFinite s.left := by
  obtain ⟨n, -, N, t, hc, ha⟩ := hM.exists_cover
  have : IsProper (s.left ≫ A.hom) := by rw [Over.w s]; infer_instance
  have : IsProper s.left := .of_comp _ A.hom
  suffices LocallyQuasiFinite s.left from .of_isProper_of_locallyQuasiFinite _
  refine LocallyQuasiFinite.of_finite_preimage_singleton _ fun z => ?_
  rcases Set.eq_empty_or_nonempty (s.left ⁻¹' {z}) with h0 | ⟨a, hz⟩
  · rw [h0]; exact Set.finite_empty
  let k : Type := A.left.residueField a
  let y₀ : Spec (CommRingCat.of k) ⟶ A.left := A.left.fromSpecResidueField a
  let P : Over (Sp K) := Over.mk (y₀ ≫ A.hom)
  let y : P ⟶ A := Over.homMk y₀ rfl
  let π : pullback s.left (y₀ ≫ s.left) ⟶ A.left := pullback.fst _ _
  let q : pullback s.left (y₀ ≫ s.left) ⟶ Spec (CommRingCat.of k) := pullback.snd _ _
  have w : π ≫ s.left = q ≫ y₀ ≫ s.left := pullback.condition
  let F : Over (Sp K) := Over.mk (π ≫ A.hom)
  let x : F ⟶ A := Over.homMk π rfl
  let r : F ⟶ P := Over.homMk q (by
    change q ≫ y₀ ≫ A.hom = π ≫ A.hom
    rw [← Over.w s, reassoc_of% w])
  have : IsAffineHom (y₀ ≫ s.left) := .of_comp _ A.hom
  have : IsAffineHom π := MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom.{0})
    (IsPullback.of_hasPullback s.left (y₀ ≫ s.left)).flip this
  have key := lam_inv_eq _ l s (h F) (x := x) (y := r ≫ y) (Over.OverMorphism.ext w)
  have triv : ∀ (b : P ⟶ A) (c : CechPic.Pic A.left), CechPic.pull (r ≫ b).left c = 0 := fun b c => by
    rw [Over.comp_left, pull_comp, pull_spec_local (K := k) b.left, map_zero]
  have one : ∀ c : CechPic.Pic A.left, CechPic.pull (1 : F ⟶ A).left c = 0 := fun c => by
    rw [← MonObj.comp_one r, triv]
  simp only [lam, inv_mul_cancel, ← GrpObj.comp_inv, ← MonObj.comp_mul, one, triv] at key
  have : CompactSpace ↥(pullback s.left (y₀ ≫ s.left)) := QuasiCompact.compactSpace_of_compactSpace q
  have : (pullback s.left (y₀ ≫ s.left)).IsQuasiAffine := quasiAffine_of_pull_add π (x⁻¹).left
    (isLB_lbPow hM.isLB n) t hc ha (by
      have e : CechPic.pull x.left (cls M hM.isLB) + CechPic.pull (x⁻¹).left (cls M hM.isLB) = 0 := by
        linear_combination (norm := abel) - key
      change CechPic.pull x.left _ + CechPic.pull (x⁻¹).left _ = 0
      rw [cls_lbPow hM.isLB, map_nsmul, map_nsmul, ← nsmul_add, e, nsmul_zero])
  have : IsAffine (pullback s.left (y₀ ≫ s.left)) := isAffine_of_quasiAffine q
  have : IsFinite q := IsFinite.iff_isProper_and_isAffineHom.2 ⟨inferInstance, inferInstance⟩
  have hfin : (Set.univ : Set ↥(pullback s.left (y₀ ≫ s.left))).Finite :=
    (q.finite_preimage_singleton (IsLocalRing.closedPoint k)).subset fun t _ => Subsingleton.elim _ _
  refine (hfin.image π).subset fun b hb => ?_
  have e : s.left b = (y₀ ≫ s.left) (IsLocalRing.closedPoint k) := by
    have e₀ : y₀ (IsLocalRing.closedPoint k) = a := Scheme.fromSpecResidueField_apply a _
    exact (show s.left b = z from hb).trans ((show s.left a = z from hz).symm.trans (congrArg s.left e₀).symm)
  obtain ⟨c, hc, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := s.left) (g := y₀ ≫ s.left) b _ e
  exact ⟨c, trivial, hc⟩

theorem isFinite_and_surjective_of_formIs : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left) (s : P.A ⟶ P.A), M.IsLB → Out.RelAmple P.A M → FormIs P M s → IsFinite s.left ∧ Surjective s.left := by
  intro _ _ K _ _ P M s hM hA ⟨hs, H⟩
  have := P.isAb.proper
  have := P.isAb.comm
  have e := (cls_eq_iff (LB.isLB_linComb hM _ _) (LB.isLB_linComb P.isLB _ _)).2 H
  have e' := (cls_cube_two hM _ _ _).symm.trans (e.trans (cls_cube_two P.isLB _ _ _))
  have hf : IsFinite s.left :=
    isFinite_of_lam_eq (isAmpleLB_of_relAmple_of_isAffine P.A hM hA) (cls P.L P.isLB) s fun T u v => by
      simpa only [pull_lam, lift_fst, lift_snd, lift_snd_assoc] using congrArg (CechPic.pull (lift u v).left) e'
  exact ⟨hf, (flat_and_surjective_of_isFinite_abelianEnd
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K P.A P.isAb s hs hf).2⟩

end GlobalTheory.FormFinite
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

theorem _root_.GlobalTheory.T.sectionsPowerGrowthVolume_pull_finite_endomorphism : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (α : P.A ⟶ P.A) (D : ℕ) (M : LB P.A.left) (δ : ℝ), IsMonHom α → IsFinite α.left → MapDeg α.left D → M.IsLB → Out.RelAmple P.A M → Vol P.A.hom M P.g δ → Vol P.A.hom (M.pull α.left) P.g (D * δ) := by
  first | exact @GlobalTheory.vol_pull_of_isFinite | exact GlobalTheory.vol_pull_of_isFinite | (intros; apply GlobalTheory.vol_pull_of_isFinite <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

theorem _root_.GlobalTheory.T.sectionsHaveFiniteDimension_lbDiv_linComb : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left) (k r : ℕ), M.IsLB → (k : K) ≠ 0 → (∀ y : 𝟙_ (Over (Sp K)) ⟶ P.A, y ^ k = 1 → SectionsHaveFiniteDimension P.A.hom (LB.div M (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, ((toUnit P.A ≫ y) * 𝟙 P.A).left] ![1, -1])) r) → SectionsHaveFiniteDimension P.A.hom (M.pull (Out.mulA P.A k).left) (k ^ (2 * P.g) * r) := by
  first | exact @GlobalTheory.TwistSplit.finrank_sections_pullback_mulByN_twists | exact GlobalTheory.TwistSplit.finrank_sections_pullback_mulByN_twists | (intros; apply GlobalTheory.TwistSplit.finrank_sections_pullback_mulByN_twists <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

theorem _root_.GlobalTheory.T.weilPairing_of_polarisationForm_linComb : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (I : Type) [Fintype I] (φ : I → (P.A ⟶ P.A)) (ε : I → ℤ) (s : P.A ⟶ P.A) (k : ℕ) (x y : Out.baseOver (Sp K) ⟶ P.A) (c : I → Kˣ), (k : K) ≠ 0 → (∀ i, IsMonHom (φ i)) → FormIs P (LB.LinComb P.L (fun i => (φ i).left) ε) s → x ^ k = 1 → y ^ k = 1 → (∀ i, Out.WeilIs P.A P.L k (x ≫ φ i) (y ≫ φ i) (unitOn (c i))) → Out.WeilIs P.A P.L k x (y ≫ s) (unitOn (∏ i, c i ^ ε i)) := by
  first | exact @GlobalTheory.weilIs_of_formIs_linComb | exact GlobalTheory.weilIs_of_formIs_linComb | (intros; apply GlobalTheory.weilIs_of_formIs_linComb <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

theorem _root_.GlobalTheory.T.kodairaSpencer_matrix_linear_in_derivation : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (o R : Type) [CommRing o] [CommRing R] [Algebra o R] [Algebra o ℂ] [Algebra R ℂ] [IsScalarTower o R ℂ] (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap (algebraMap R ℂ)) → ∃ κ : Derivation o R ℂ →ₗ[ℂ] Matrix (Fin P₀.g) (Fin P₀.g) ℂ, ∀ D : Derivation o R ℂ, ∃ s, KSRel u p m (fun r => D r) (κ D) s := by
  first | exact @GlobalTheory.KS.Lin.ks_linear | exact GlobalTheory.KS.Lin.ks_linear | (intros; apply GlobalTheory.KS.Lin.ks_linear <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS

theorem top_le_preimage_of_mem {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (p : Sp ℂ) (U : X.Opens)
    (hp : x p ∈ U) : ⊤ ≤ x ⁻¹ᵁ U := by
  intro q _
  obtain rfl : q = p := Subsingleton.elim q p
  exact hp

theorem algebraic_coboundary_of_holomorphic_coboundary : Out.Laws → ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (I : Type) (O : I → P₀.A.left.Opens) (c : ∀ i i', Γ(P₀.A.left, O i ⊓ O i')) (h : I → (Fin P₀.g → ℂ) → ℂ), ⨆ i, O i = ⊤ → (∀ i, DifferentiableOn ℂ (h i) {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ O i} ∧ ∀ (l : u.Λ) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ O i → h i (z + l) = h i z) → (∀ i i' z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (O i ⊓ O i') → valAt' (u.ex z).left (O i ⊓ O i') (c i i') = h i' z - h i z) → ∀ i, ∃ a : Γ(P₀.A.left, O i), ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ O i → valAt' (u.ex z).left (O i) a = h i z := by
  intro hL P₀ u Hm χ hU I O c h hcov hhol hcoc i

  refine (GlobalTheory.T.existsUnique_section_of_locally_given_values P₀ u Hm χ hU (O i) (h i) ?_).exists
  intro z hz
  obtain ⟨p⟩ : Nonempty (Sp ℂ) := inferInstance
  have hy : (u.ex z).left p ∈ O i := hz (Set.mem_univ p)
  obtain ⟨n, σ, hyσ, hσ⟩ := GlobalTheory.T.exists_nonzeroLocus_le_open_polarisation_complex hL P₀ (O i) _ hy
  obtain ⟨a, ha⟩ := GlobalTheory.T.primitive_regular_on_section_nonzeroLocus P₀ u Hm χ hU I O c h hcov hhol hcoc i n σ hσ
  exact ⟨Out.nonzeroLocus σ, a, hσ, top_le_preimage_of_mem _ p _ hyσ, ha⟩

end GlobalTheory.KS
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.exists_sections_cover_cube_effective_abelianVariety : (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N : LB P.A.left) (s : N.Sec), N.IsLB → (∃ j, s.f j ≠ 0) → ∃ (r : ℕ) (u : Fin r → (lbPow N 3).Sec), ⨆ i, Out.nonzeroLocus (u i) = ⊤ := by
  first | exact @GlobalTheory.EffectiveCube.exists_sections_cube_cover | exact GlobalTheory.EffectiveCube.exists_sections_cube_cover | (intros; apply GlobalTheory.EffectiveCube.exists_sections_cube_cover <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.appellHumbert_uniformisation_riemannForm : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ), u.IsAH Hm χ → ∃ Ef : LinearMap.BilinForm ℤ u.Λ, (∀ a b : u.Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧ Function.Bijective Ef ∧ (∀ l, χ l = 1 ∨ χ l = -1) ∧ (∀ l m, χ (l + m) = χ l * χ m * (-1) ^ Ef l m) ∧ (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) ∧ (∀ n : ℕ, (∀ s, ∃! θ, u.IsThetaFn Hm χ n θ ∧ u.IsFnPow n s θ) ∧ ∀ θ, u.IsThetaFn Hm χ n θ → ∃! s, u.IsFnPow n s θ) ∧ ∀ (k : ℕ) (a b : u.Λ) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (Ef a b : ℂ) / k) → Out.WeilIs P.A P.L k (u.ex ((k : ℂ)⁻¹ • (a : Fin P.g → ℂ))) (u.ex ((k : ℂ)⁻¹ • (b : Fin P.g → ℂ))) (unitOn c) := by
  first | exact @GlobalTheory.AnyAppellHumbert.isAH_properties | exact GlobalTheory.AnyAppellHumbert.isAH_properties | (intros; apply GlobalTheory.AnyAppellHumbert.isAH_properties <;> assumption)
end

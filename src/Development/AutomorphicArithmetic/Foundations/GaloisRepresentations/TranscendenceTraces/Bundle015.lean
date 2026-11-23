module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.Bundle013
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle458
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle652
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle651
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle654
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.dSOne_of :
    LocFinSec → DSOne := by
  intro hL R _ Z S p _ T hT U u b hb
  obtain ⟨-, hmono, -, -, -, -, -⟩ := GlobalTheory.T.etaleLocal_property_calculus_rules
  have h1 := (GlobalTheory.T.etaleSheaf_shortComplex_exact_iff_locally R T).1 hT (pullback p u) b hb
  have h2 := hL R T.f (pullback.snd p u) b h1
  apply hmono _ _ _ h2
  intro U' g hg
  obtain ⟨a, ha⟩ := hg (pullback p (g ≫ u)) (pbm p g u (g ≫ u) rfl) (pullback.snd p (g ≫ u))
    (pbm_snd p g u (g ≫ u) rfl)
  refine ⟨inc p T.X₁ (g ≫ u) a, ?_⟩
  rw [DS.map_inc, ha, DS.res_inc p T.X₂ g u (g ≫ u) rfl]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem ds_res_map_comm {R : Type} [CommRing R] {Z S : Scheme} (p : Z ⟶ S) {G G' : Shv R}
    (f : G ⟶ G') {W V : Scheme} (k : W ⟶ V) (x : DS p G V) :
    DS.res p G' k (DS.map p f V x) = DS.map p f W (DS.res p G k x) := by
  have h := congrArg (fun φ => ModuleCat.Hom.hom φ x) (((phiPF p R).map f).naturality k.op)
  simp only [phiPF, phiP, ModuleCat.hom_comp, ModuleCat.hom_ofHom] at h
  exact h.symm

theorem UpperTheory.Gal.TranscendenceTraces.phiExact_of :
    DSLoc → PhiExact := by
  intro hD R _ Z S p _ T hT
  obtain ⟨-, hmono, -, -, hloc, -, -⟩ := GlobalTheory.T.etaleLocal_property_calculus_rules
  rw [GlobalTheory.T.etaleSheaf_shortComplex_exact_iff_locally]
  intro U b hb
  change Sec ((phi p R).obj T.X₂) U at b
  change Sec.map ((phi p R).map T.g) b = 0 at hb
  have h1 := (GlobalTheory.T.etaleToSheafify_locally_bijective_and_lift R (phiP p T.X₂)).1 U b
  apply hloc
  apply hmono _ _ _ h1
  rintro V g ⟨x0, hx0⟩
  obtain ⟨x, hx⟩ : ∃ x : DS p T.X₂ V, phiSec p T.X₂ V x = Sec.res g b := ⟨x0, hx0⟩
  have hz : phiSec p T.X₃ V (DS.map p T.g V x) = 0 := by
    rw [← phiSec_map, hx, map_res, hb]
    exact map_zero _
  have h2 := (GlobalTheory.T.etaleToSheafify_locally_bijective_and_lift R (phiP p T.X₃)).2.1 V _ hz
  apply hloc
  apply hmono _ _ _ h2
  intro W k hk
  have hk' : DS.res p T.X₃ k (DS.map p T.g V x) = 0 := hk
  have h0 : DS.map p T.g W (DS.res p T.X₂ k x) = 0 := by
    rw [← ds_res_map_comm]
    exact hk'
  apply hmono _ _ _ (hD R p T hT W (DS.res p T.X₂ k x) h0)
  rintro W' k' ⟨a, ha⟩
  refine ⟨phiSec p T.X₁ W' a, ?_⟩
  change Sec.map ((phi p R).map T.f) (phiSec p T.X₁ W' a) = Sec.res ((k' ≫ k) ≫ g) b
  rw [phiSec_map, ha, ← phiSec_res, ← phiSec_res, hx]
  exact (res_res k' k (Sec.res g b)).trans (res_res (k' ≫ k) g b)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.trRed_of :
    GlobalTheory.EtC.A8 → TrChar → TrSum → OpEq → FamSemi → RedZero → RpBasic → RpOp → PtInj → FibFin → TrRed := by
  intro hA8 hChar hSum hOp hFS hRZ hRp hRpOp hPt hFib Q q _ _ hd n i Z S p _ w hw hQ x
  have hq := isUnit_of_dvd_unit (Nat.cast_dvd_cast hd) hQ
  obtain ⟨hovQ, -, -⟩ := hChar Q i p w hw hQ
  obtain ⟨hovq, -, -⟩ := hChar q i p w hw hq
  obtain ⟨f, hfn, hf0⟩ := hRZ Q q hd i
  obtain ⟨σ1, hσ1⟩ := (hFS (ZMod Q) (ZMod Q) (ZMod q)).1 (trFam p w Q i) (redMap Q q i)
  obtain ⟨σ2, hσ2⟩ := (hFS (ZMod Q) (ZMod q) (ZMod q)).2 (redMap Q q i) (trFam p w q i)
  obtain ⟨τ1, hτ1⟩ := (hFS (ZMod Q) (ZMod q) (ZMod Q)).1 σ1
    (restrMap (ZMod.castHom hd (ZMod q)) (tw q i))
  obtain ⟨τ2, hτ2⟩ := (hFS (ZMod Q) (ZMod q) (ZMod Q)).1 σ2
    (restrMap (ZMod.castHom hd (ZMod q)) (tw q i))
  have key : ∀ (A : Sq p) (a : Sec (tw Q i) A.V),
      ((tr0 p w q i).app A) ((f A.V) a) = (f A.U) (((tr0 p w Q i).app A) a) := by
    intro A a
    haveI := Sq.finite A
    apply hPt q i A.U
    intro Ω _ _ y
    have hfin := hFib A.r Ω y
    rw [hSum q i p w hw hq A ((f A.V) a) Ω y, hfn, hSum Q i p w hw hQ A a Ω y,
      (f (gp Ω)).map_finsum_mem _ hfin]
    refine finsum_mem_congr rfl fun z _ => ?_
    rw [map_zsmul, hfn]
  let t : Fam0 p (tw Q i) ((restr (ZMod.castHom hd (ZMod q))).obj (tw q i)) :=
    { app := fun A => (f A.U).comp ((tr0 p w Q i).app A)
      nat := fun {A B} k a => (hfn _ _ k.g _).trans (congrArg (f A.U) ((tr0 p w Q i).nat k a)) }
  have hov1 : τ1.Over t := by
    intro A a
    rw [hτ1, hσ1, hovQ A a, hf0, GlobalTheory.T.restrictScalarsResolutionMap_augmentation_spec]
    rfl
  have hov2 : τ2.Over t := by
    intro A a
    rw [hτ2, hσ2, hf0, hovq A, GlobalTheory.T.restrictScalarsResolutionMap_augmentation_spec, key]
    rfl
  obtain ⟨a, ha⟩ := (hRp (ZMod Q) (res (ZMod Q) (tw Q i)) Z n).1 x
  have r1 := (hRp (ZMod Q) (res (ZMod Q) (tw Q i)) S n).2.2.2.2 (ZMod q) (res (ZMod q) (tw q i))
    (redMap Q q i) _ _ (hRpOp (ZMod Q) (ZMod Q) (trFam p w Q i) n x a ha)
  have r2 := hRpOp (ZMod q) (ZMod q) (trFam p w q i) n _ _
    ((hRp (ZMod Q) (res (ZMod Q) (tw Q i)) Z n).2.2.2.2 (ZMod q) (res (ZMod q) (tw q i))
      (redMap Q q i) x a ha)
  have s1 := (hRp (ZMod q) (res (ZMod q) (tw q i)) S n).2.2.2.2 (ZMod Q) _
    (restrMap (ZMod.castHom hd (ZMod q)) (tw q i)) _ _ r1
  have s2 := (hRp (ZMod q) (res (ZMod q) (tw q i)) S n).2.2.2.2 (ZMod Q) _
    (restrMap (ZMod.castHom hd (ZMod q)) (tw q i)) _ _ r2
  have u1 := hRpOp (ZMod Q) (ZMod Q) τ1 n x a ha
  have u2 := hRpOp (ZMod Q) (ZMod Q) τ2 n x a ha
  have e1 := ((hRp (ZMod Q) _ S n).2.2.1 _ _ _ _ s1 u1).2.1
    ((hτ1 n (Sq.self p) a).trans (congrArg _ (hσ1 n (Sq.self p) a))).symm
  have e2 := ((hRp (ZMod Q) _ S n).2.2.1 _ _ _ _ s2 u2).2.1
    ((hτ2 n (Sq.self p) a).trans (congrArg _ (hσ2 n (Sq.self p) a))).symm
  apply (hA8 (ZMod Q) (ZMod q) (ZMod.castHom hd (ZMod q)) (sch.obj S) (tw q i) n).1
  exact e1.trans ((DFunLike.congr_fun (hOp Q p (tw Q i) _ t τ1 τ2 hov1 hov2 n) x).trans e2.symm)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem q_smul_sec (q : ℕ) (i : ℤ) {V : Scheme.{0}} (t : Sec (tw q i) V) : q • t = 0 := by
  have h0 : ((q : ℕ) : ULift.{1} (ZMod q)) = 0 := by
    apply ULift.ext
    simp
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)) q t, h0, zero_smul]

private theorem res_sub' {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (a b : Sec F U) :
    Sec.res g (a - b) = Sec.res g a - Sec.res g b := map_sub (F.obj.map g.op).hom a b

private theorem res_zero' {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) :
    Sec.res g (0 : Sec F U) = 0 := map_zero (F.obj.map g.op).hom

private theorem res_nsmul' {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (c : ℕ) (a : Sec F U) :
    Sec.res g (c • a) = c • Sec.res g a := map_nsmul (F.obj.map g.op).hom c a

private theorem sec_empty {R : Type} [CommRing R] (F : Shv R) {V : Scheme.{0}} [IsEmpty V] (a b : Sec F V) : a = b :=
  (GlobalTheory.T.etaleSheafSections_ext_and_glue R F V).1 a b ((GlobalTheory.T.etaleLocal_property_calculus_rules).2.2.2.2.2.2 V _)

theorem UpperTheory.Gal.TranscendenceTraces.ptInj_of :
    PtEx → PtInj := by
  intro hEx q _ i U b b' h
  have hy : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : gp Ω ⟶ U), Sec.res x (b - b') = 0 := by
    intro Ω _ _ x
    rw [res_sub', h Ω x, sub_self]
  refine (GlobalTheory.T.etaleSheafSections_ext_and_glue (ZMod q) (tw q i) U).1 b b' ?_
  refine (GlobalTheory.T.etaleLocal_property_calculus_rules).2.1 U _ _ ((GlobalTheory.T.tateTwist_sections_locally_generated q i).1 U (b - b')) ?_
  intro V g hg
  have key : Sec.res g (b - b') = 0 := by
    rcases hg with hg | ⟨ζ, c, hc⟩
    · exact hg
    · rcases isEmpty_or_nonempty V with hV | ⟨⟨v⟩⟩
      · exact sec_empty _ _ _
      · obtain ⟨Ω, _, _, x, -⟩ := hEx V v
        have h1 : c • twGen i (ζ.map x.appTop.hom) = 0 := by
          have h2 := hy Ω (x ≫ g)
          rw [← res_res, hc, res_nsmul', (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.2.1] at h2
          exact h2
        haveI : Nonempty (gp Ω) := ⟨IsLocalRing.closedPoint Ω⟩
        obtain ⟨d, rfl⟩ := (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.1 (gp Ω) _ c h1
        rw [hc, mul_nsmul', q_smul_sec]
  rw [res_sub'] at key
  exact sub_eq_zero.1 key
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.sumExLoc_of :
    SecFun → FunSec → FibFin → SumExLoc := by
  intro hSF hFS hFF q _ i Z S p _ w hw A hζ a
  obtain ⟨ζ⟩ := hζ
  haveI : IsFinite A.r := Sq.finite A
  have hgen : twGen i (ζ.map A.r.appTop.hom) = Sec.res A.r (twGen i ζ) :=
    ((GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.2.1 A.V A.U A.r ζ).symm
  obtain ⟨φ, hφ, hv⟩ := hSF q i A.V (ζ.map A.r.appTop.hom) a
  obtain ⟨ψ, hψ, hs⟩ := hw A φ hφ
  obtain ⟨b, hb⟩ := hFS q i A.U ζ ψ hψ
  refine ⟨b, fun Ω _ _ x => ?_⟩
  have hfin : (fib A.r x).Finite := hFF A.r Ω x
  have hz : ∀ z ∈ fib A.r x, Sec.res z a = φ (pt z) • Sec.res x (twGen i ζ) := by
    intro z hz
    have hz' : z ≫ A.r = x := hz
    rw [hv Ω z, hgen, res_res, hz']
  rw [hb Ω x, hs Ω x, finsum_mem_eq_finite_toFinset_sum _ hfin,
    finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_smul]
  refine Finset.sum_congr rfl fun z hzm => ?_
  rw [hz z (hfin.mem_toFinset.mp hzm), mul_smul]
end

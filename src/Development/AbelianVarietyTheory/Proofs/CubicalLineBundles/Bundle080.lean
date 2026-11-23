module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle039
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle020
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusOfUnit
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemNonzeroLocusOfPull
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle029
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle030
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle031
import Formalism.LocalToGlobal.ProjectiveLattices.ThetaFramePf
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle068
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle044
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle045
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle040
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle052
public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LamPtClauses
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle025
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle021
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle019
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle044
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle071
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle078
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT

theorem secInt_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l), ∀ (T T' : CDVR) (ψ : T.V →+* T'.V) (i : T.Fr →+* T'.Fr), (algebraMap T'.V T'.Fr).comp ψ = i.comp (algebraMap T.V T.Fr) → ∀ (x : Sp T.Fr ⟶ Xo.X) (x' : Sp T'.Fr ⟶ Xo.X) (G : PAT H (Sp T.V)) (G' : PAT H (Sp T'.V)) (t : SAB H (Sp T.Fr)) (t' : SAB H (Sp T'.Fr)) (m1 : SABMap t Xo.univ.t x) (m2 : SABMap t G.t (spMap (algebraMap T.V T.Fr))) (m1' : SABMap t' Xo.univ.t x') (m2' : SABMap t' G'.t (spMap (algebraMap T'.V T'.Fr))) (n : SABMap G'.t G.t (spMap ψ)) (n' : SABMap t' t (spMap i)), x' = spMap i ≫ x → m1'.φ = n'.φ ≫ m1.φ → m2'.φ ≫ n.φ = n'.φ ≫ m2.φ → ∀ (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')), SecBC i 1 x x' s s' → SecInt T m1 m2 s → SecInt T' m1' m2' s' := by
  intro E _ _ _ H Dw l Xo T T' ψ i hψ x x' G G' t t' m1 m2 m1' m2' n n' hx h1 h2 s s' hb
  have isoMaps_iff {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F))
      (σ : LB.Sec L') (s : LB.Sec (L.pull F)) :
      IsoMaps w σ s ↔ ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : L.ι) (k : L'.ι), F (r z) ∈ L.U j → r z ∈ L'.U k →
        gs r z _ (s.f (fun _ => j)) = (gw w r z j k).val * gs r z _ (σ.f k) := by
    constructor
    · intro h Z r z j k hj hk
      have hz : r z ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
      have a := congrArg (gs r z _) (h (fun _ => j) k)
      exact (gs_res _ z _ hz _).symm.trans (a.trans ((gs_mul _ z _ hz _ _).trans
          (congrArg₂ (· * ·) (gs_unit _ z _ hz _) (gs_res _ z _ hz _))))
    · intro h (i : PUnit → L.ι) k
      exact fn_ext fun p hp =>
        (gs_res _ p _ hp _).trans ((h _ (𝟙 _) p (i PUnit.unit) k (mem_pull.1 hp.1) hp.2).trans
          (Eq.symm ((gs_mul _ p _ hp _ _).trans (congrArg₂ (· * ·) (gs_unit (𝟙 _) p _ hp _) (gs_res _ p _ hp _)))))

  rintro ⟨θ, hθ, w2, σ, θ2, r2, i2, p2, tie⟩
  have hS : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  obtain ⟨wn, gn, rn, -⟩ := n.lin
  obtain ⟨wn', gn', rn', -⟩ := n'.lin
  obtain ⟨w2', g2', r2', -⟩ := m2'.lin
  have Rn : RigIso n wn := ⟨gn, rn⟩
  have Rn' : RigIso n' wn' := ⟨gn', rn'⟩
  have R2' : RigIso m2' w2' := ⟨g2', r2'⟩
  obtain ⟨θ', hθ'⟩ := sec_pull_down ((isGen_iff wn).1 gn) G.t.PP.isLB G'.t.PP.isLB θ
  obtain ⟨σ', hσ'⟩ := sec_pull_down ((isGen_iff w2').1 g2') G'.t.PP.isLB t'.PP.isLB θ'
  have nz : ∀ y : Sp T.V, ∃ z : G.t.G.left, G.t.G.hom z = y ∧ z ∈ Out.nonzeroLocus θ := fun y => by
    obtain ⟨b, hb, -⟩ := GlobalTheory.KeyOnPol.exists_generator hS G.pol
    obtain ⟨z, hz, hm⟩ := hb y
    obtain ⟨a, ha, -⟩ := hθ b
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
    rw [ha k, Scheme.basicOpen_mul] at hk
    exact ⟨z, hz, TopologicalSpace.Opens.mem_iSup.2 ⟨k, hk.2⟩⟩
  have nz' := SectionBaseChange.fibre_nonzero_of_pull G'.t.PP.isLB hθ' n.cart.1 nz
  refine ⟨θ', SectionBaseChange.generates hS G.pol n.cart.1 G'.t.PP.isLB ⟨wn, gn⟩ θ' nz', w2', σ',
    thfPull G'.t.PP.L m2'.φ θ', R2', ?_, fun _ _ => rfl, ?_⟩
  · refine (isoMaps_iff _ _ _).2 fun Z r z j k hj hk => ?_
    exact (gs_appLE m2'.φ _ _ _ r z (mem_pull.2 hj) _).trans (hσ' Z r z j k hj hk)
  · refine (TieCalc.secTie_baseChange m1 tie i m1' n' s' wn' (thfPull t.PP.L n'.φ σ) σ' hx h1 hb Rn'
      (fun _ _ => rfl)).2 ((isoMaps_iff _ _ _).2 fun Z r z j k hj hk => ?_)
    have hbase : spMap (algebraMap T'.V T'.Fr) ≫ spMap ψ = spMap i ≫ spMap (algebraMap T.V T.Fr) := by
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hψ]
    obtain ⟨N, hN⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ n m2'
    have hN' : N.φ = m2'.φ ≫ n.φ := hN
    obtain ⟨wa, ra, Ta⟩ := GlobalTheory.LiftBaseChange.rigIso_comp n m2' N rfl hN' Rn R2'
    obtain ⟨wb, rb, Tb⟩ := GlobalTheory.LiftBaseChange.rigIso_comp m2 n' N hbase (hN'.trans h2) r2 Rn'
    have hp : IsProper t'.G.hom := MorphismProperty.of_isPullback (P := @IsProper) m2'.cart.1 G'.ab.proper
    have hab : IsAbelianScheme t'.G := ⟨t'.semi.comm, t'.semi.smooth, hp, t'.semi.geomConnected⟩
    obtain rfl : wa = wb := iso_unique_of_rig GlobalTheory.globalFns_holds t'.G hab t'.PP.isLB G.t.PP.isLB ra.1 rb.1 ra.2 rb.2
    obtain ⟨a, ha⟩ := exists_chart G.t.PP.isLB (m2.φ (n'.φ (r z)))
    obtain ⟨b, hb'⟩ := exists_chart G'.t.PP.isLB (m2'.φ (r z))
    have ha' : n.φ (m2'.φ (r z)) ∈ G.t.PP.L.U a := (congrArg (fun q => q (r z) ∈ G.t.PP.L.U a) h2).mpr ha
    have e1 := hθ' Z (r ≫ m2'.φ) z a b ha' hb'
    have e2 := hσ' Z r z b k hb' hk
    have le : (G.t.PP.L.pull m2.φ).U (fun _ => a) ≤ m2.φ ⁻¹ᵁ G.t.PP.L.U a := fun q hq => mem_pull.1 hq
    have e3 := (isoMaps_iff _ _ _).1 i2 Z (r ≫ n'.φ) z a j ha hj
    rw [p2 (fun _ => a) le, gs_appLE m2.φ _ _ le (r ≫ n'.φ) z (mem_pull.2 ha), Category.assoc, ← h2,
      ← Category.assoc, e1, e2, ← _root_.mul_assoc, ← Units.val_mul, ← Ta Z r z a b k ha' hb' hk,
      Tb Z r z a j k ha hj hk, Units.val_mul, _root_.mul_assoc] at e3
    exact (gs_appLE n'.φ _ _ _ r z (mem_pull.2 hj) _).trans ((Units.mul_right_inj _).1 e3).symm

end GlobalTheory.LamT
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CM GlobalTheory.LamT

namespace GlobalTheory.LamT

theorem nonempty_fibKey : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K : Type) [Field K] (x : Sp K ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → Nonempty (FibKey Xo K x) := by
  intro E _ _ _ H Dw l Xo K _ x hpq
  have hT : Out.SecTwistSt := GlobalTheory.lawsFieldsSeparately.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨U, hU, hg⟩ := exists_pat_of_obj E H Dw l _ _ _ _ Xo.univ
  obtain ⟨t, ⟨m⟩⟩ : ∃ t : SAB H (Sp K), Nonempty (SABMap t Xo.univ.t x) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull x Xo.univ.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨⟨T, rfl, hTg⟩, -⟩ := PAT.exists_of_sabMap E H _ _ x U t (hU ▸ m)
  have hpos : 1 ≤ Module.finrank ℚ E / 2 := by
    have h1 := (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E)
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E] at h1
    have h2 : 0 < Module.finrank ℚ (maximalRealSubfield E) := Module.finrank_pos
    omega
  obtain ⟨b, hb⟩ := principalPolarisation_exists_unique_section hT T.pol
  obtain ⟨a, -, hu⟩ := hb b
  obtain ⟨v, hv⟩ := KeyPow.exists_isLieBasis T.t.G T.dim
  refine ⟨⟨T, m, ?_, b, KeyPow.exists_mem_nonzeroLocus T.pol b ?_, v, hv⟩⟩
  · rw [hTg, hg]
    exact Nat.mul_pos hpos hpq
  · by_contra hn
    push Not at hn
    exact zero_ne_one ((hu 0 fun i => by rw [hn i, mul_zero]).trans (hu 1 fun i => by rw [hn i, mul_zero]).symm)

end GlobalTheory.LamT
end

section



noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT.LocSec

theorem exists_secTie {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {t : SAB H (Sp S)} (m : SABMap t Xo.univ.t x)
    (σ : LB.Sec t.PP.L) : ∃ s : LB.Sec (PPx x), SecTie m σ s := by
  obtain ⟨w, g1, r1, -⟩ := m.lin
  obtain ⟨s1, hs1⟩ := thf_secUp ((isGen_iff w).1 g1) Xo.univ.t.PP.isLB t.PP.isLB σ
  let A := Xo.univ.t.G
  have cond : (snd (Over.mk x) A).left ≫ A.hom = (fst (Over.mk x) A).left ≫ x :=
    (Over.w (snd (Over.mk x) A)).trans (Over.w (fst (Over.mk x) A)).symm
  let h : Gx x ⟶ t.G.left := m.cart.1.lift _ _ cond
  have hφ : h ≫ m.φ = (snd (Over.mk x) A).left := m.cart.1.lift_fst _ _ cond
  have hh : h ≫ t.G.hom = (fst (Over.mk x) A).left := m.cart.1.lift_snd _ _ cond
  have uniq : ∀ g : t.G.left ⟶ Gx x, g ≫ (snd (Over.mk x) A).left = m.φ → g ≫ (fst (Over.mk x) A).left = t.G.hom →
      g ≫ h = 𝟙 _ := fun g e₁ e₂ => m.cart.1.hom_ext (by rw [Category.assoc, hφ, e₁, Category.id_comp])
        (by rw [Category.assoc, hh, e₂, Category.id_comp])
  refine ⟨thfPull1 Xo.univ.t.PP.L h hφ s1, w, s1, ⟨g1, r1⟩,
    (TieCalc.isoMaps_iff w σ s1).2 fun Z r z j k hj hk => hs1 Z r z (fun _ => j) k (mem_pull.2 hj) hk,
    fun g e₁ e₂ (j : PUnit → Xo.univ.t.PP.L.ι) hj => fn_ext fun y hy => ?_⟩
  exact Eq.symm ((gs_appLE g _ _ hj (𝟙 _) y hy _).trans
      ((gs_appLE h _ _ (chart_le_pullback_open _ h hφ _) (𝟙 _ ≫ g) y (hj hy) _).trans
        (congrArg (fun q => gs q y _ (s1.f j)) (by rw [Category.id_comp, uniq g e₁ e₂]))))

theorem exists_unit_secInt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (G : PAT H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (x : Sp T.Fr ⟶ Xo.X) (m1 : SABMap t' Xo.univ.t x) (m2 : SABMap t' G.t (spMap (algebraMap T.V T.Fr))), letI := io.toAlgebra; ∀ y : FrPt Xo c T.Fr, y.x = x → ∃ a : T.Frˣ, ∀ (g : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) T.Fr)) (y' : FrPt Xo c T.Fr), FrChg g (a : T.Fr) y y' → SecInt T m1 m2 y'.s := by
  intro E _ _ _ H Dw l Xo c T io G t' x m1 m2
  let _ := io.toAlgebra
  intro y hy
  subst hy
  have hS : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  obtain ⟨θ, hne, -⟩ := KeyOnPol.exists_generator hS G.pol
  obtain ⟨w2, g2, r2, -⟩ := m2.lin
  obtain ⟨hθ, σ, hσ, -, hgen⟩ := SectionBaseChange.generates_and_baseChange hS T.V T.Fr (algebraMap T.V T.Fr) G.pol t'.G
    m2.φ t'.PP.L w2 θ m2.cart.1 t'.PP.isLB g2 hne
  obtain ⟨s, hs⟩ := exists_secTie m1 σ
  obtain ⟨a, ha, -⟩ := y.gen s
  have a0 : a ≠ 0 := by
    rintro rfl
    have z0 : ∀ i, s.f i = scal y.x 0 i * s.f i := fun i => by
      rw [ha i]
      simp only [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, toΓ, map_zero, zero_mul]
    have e0 := (TieCalc.secTie_scale m1 hs 0 z0).1 hs
    have e1 := (TieCalc.secTie_scale m1 hs 1 (fun i => by rw [SecCalc.scal_one', _root_.one_mul])).1 hs
    obtain ⟨b, -, hb⟩ := hgen σ
    exact zero_ne_one ((hb 0 e0).trans (hb 1 e1).symm)
  refine ⟨Units.mk0 a a0, fun g y' hc => ⟨θ, hθ, w2, σ, thfPull G.t.PP.L m2.φ θ, ⟨g2, r2⟩,
    fun (j : PUnit → G.t.PP.L.ι) k => Eq.trans (fn_ext fun p hp => (gs_res _ p _ hp _).trans
      ((gs_appLE m2.φ _ _ _ (𝟙 _) p hp.1 _).trans (gs_appLE m2.φ _ _ _ (𝟙 _) p hp _).symm))
      (hσ j k (inf_le_left.trans (LB.wchart_le G.t.PP.L _ j PUnit.unit))), fun j hj => rfl, ?_⟩⟩
  obtain ⟨hx, -, pm, p₁, p₂, hp⟩ := hc
  refine ((TieCalc.secTie_calc E H Dw l Xo T.Fr y.x t' m1 σ s hs).1 1 y'.x y'.s σ hx ⟨pm, p₁, p₂, fun i h => ?_⟩).2
    ((TieCalc.secTie_scale m1 hs 1 (fun i => by rw [SecCalc.scal_one', _root_.one_mul])).1 hs)
  have e : scal y.x 1 i * s.f i = scal y.x a i * y.s.f i :=
    ((congrArg (· * s.f i) (SecCalc.scal_one' y.x i)).trans (_root_.one_mul _)).trans (ha i)
  exact (congrArg _ e).trans (hp i h)

end GlobalTheory.LamT.LocSec
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem evR_frChg_tri {S : Type} [CommRing S] [Algebra c.F S] (hS : IsReduced S) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {F : Rul Xo c} (hF : F ∈ sec Xo c a n) (t : Ix Dw → Sˣ)
    (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (h0 : ∀ τ i j, i < j → g τ i j = 0)
    (hd : ∀ τ i, g τ i i = (t (some ⟨τ, i⟩) : S)) {y y' : FrPt Xo c S} (h : FrChg g (t none : S) y y') :
    evR Xo c F y' = wchar (ex Dw a n) t * evR Xo c F y :=
  (GlobalTheory.Frames.algebraic_laws GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c).2.2.2.2.2.2 S hS a n F hF t y y'
    (((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c S y y' y').1 t).2 ⟨g, h0, hd, h⟩)

theorem evalFr_mul_tri {K : Type} [CommRing K] [Algebra c.F K] {y : FrPt Xo c K} {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {F : Rul Xo c} (hF : F ∈ sec Xo c a n) {G : MvPolynomial (FrVar Dw.mult) K} (hG : IsFrPoly F y G)
    {S : Type} [CommRing S] [Algebra c.F S] (hS : IsReduced S) (φ : K →ₐ[c.F] S)
    (X T : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (hX : ∀ b, IsUnit (X b).det)
    (hT : ∀ b, IsUnit (T b).det) (h0 : ∀ τ i j, i < j → T τ j i = 0) (hd : ∀ τ i, IsUnit (T τ i i)) :
    evalFr (MvPolynomial.map φ.toRingHom G) (fun b => X b * T b) =
      (∏ b, ∏ i : Fin (Dw.mult b), T b i i ^ a (b, i)) * evalFr (MvPolynomial.map φ.toRingHom G) X := by
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c K S φ y
  obtain ⟨z1, h1, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c S z (fun b => (X b).transpose) 1
    (fun b => by rw [Matrix.det_transpose]; exact hX b)
  obtain ⟨z2, h2, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c S z1 (fun b => (T b).transpose) 1
    (fun b => by rw [Matrix.det_transpose]; exact hT b)
  have h3 := (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c S z z1 z2).2 _ _ _ _ h1 h2
  simp only [Units.val_one, _root_.mul_one, ← Matrix.transpose_mul] at h1 h2 h3
  rw [← hG S φ z z1 X hX hz h1, ← hG S φ z z2 (fun b => X b * T b)
    (fun b => by rw [Matrix.det_mul]; exact (hX b).mul (hT b)) hz h3]
  let t : Ix Dw → Sˣ := fun i => match i with
    | none => 1
    | some p => (hd p.1 p.2).unit
  rw [evR_frChg_tri hS hF t (fun b => (T b).transpose) h0 (fun _ _ => rfl) h2]
  congr 1
  simp [wchar, Fintype.prod_option, Fintype.prod_sigma, t, ex]

end



theorem isFrPoly_equiv_and_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ F ∈ sec Xo c a n, ∀ G : MvPolynomial (FrVar Dw.mult) K, IsFrPoly F y G → (∀ [DecidableEq (E →+* ℂ)] (σ : K →+* ℂ), IsEquiv (fun b (i : Fin (Dw.mult b)) => a (b, i)) (MvPolynomial.map σ G)) ∧ ∀ (σ : c.F →+* ℂ) (σ₁ : K →ₐ[c.F] CAt σ) (w : FrPt Xo c (CAt σ)), spMap σ₁.toRingHom ≫ y.x = w.x → evR Xo c F w ≠ 0 → G ≠ 0 := by
  intro E _ _ _ H Dw l Xo c K _ _ y a n F hF G hG
  refine ⟨fun σ X b t hX ht htri => ?_, fun σ σ₁ w hw hne hG0 => hne ?_⟩
  · have hred : IsReduced (CAt (σ.comp (algebraMap c.F K))) := inferInstanceAs (IsReduced ℂ)
    have hdiag : ∀ i, t i i ≠ 0 := by
      rw [Matrix.det_of_upperTriangular htri] at ht
      exact fun i => Finset.prod_ne_zero_iff.1 ht i (Finset.mem_univ i)
    let T : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ := Function.update (fun _ => 1) b t
    have hT : ∀ b', IsUnit (T b').det := by
      intro b'
      by_cases hb : b' = b
      · subst hb; simpa [T] using ht
      · simp [T, Function.update_of_ne hb]
    have h0 : ∀ τ i j, i < j → T τ j i = 0 := by
      intro b' i j hij
      by_cases hb : b' = b
      · subst hb; simpa [T] using htri hij
      · simp [T, Function.update_of_ne hb, Matrix.one_apply_ne hij.ne']
    have hd : ∀ τ i, IsUnit (T τ i i) := by
      intro b' i
      by_cases hb : b' = b
      · subst hb; simpa [T] using hdiag i
      · simp [T, Function.update_of_ne hb]
    have key : evalFr (MvPolynomial.map σ G) (fun b => X b * T b) =
        (∏ b, ∏ i : Fin (Dw.mult b), T b i i ^ a (b, i)) * evalFr (MvPolynomial.map σ G) X :=
      evalFr_mul_tri hF hG hred (embAlg (c := c) σ) X T (fun b' => (Ne.isUnit (hX b') : IsUnit (X b').det)) hT h0 hd
    have e1 : Function.update X b (X b * t) = fun b => X b * T b := by
      funext b'
      by_cases hb : b' = b
      · subst hb; simp [T]
      · simp [T, Function.update_of_ne hb]
    rw [e1, key]
    congr 1
    rw [Finset.prod_eq_single b]
    · simp [T, ReciprocityTheory.MultiplicativeHeights.triChar]
    · intro b' _ hb
      simp [T, Function.update_of_ne hb]
    · simp
  · have hred : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
    obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c K _ σ₁ y
    obtain ⟨g, s, hg, hzw⟩ := (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c _ z w).1 (hw.symm.trans hz.1.symm)
    obtain ⟨z1, h1, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c _ z g 1 hg
    obtain ⟨z2, h2, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c _ z1 (fun _ => 1) s (fun _ => by simp)
    have h3 := (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c _ z z1 z2).2 _ _ _ _ h1 h2
    simp only [Units.val_one, _root_.mul_one, _root_.one_mul] at h1 h3
    have e : z2 = w := (GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c _ z g s hg).unique h3 hzw
    subst e
    have hv := hG _ σ₁ z z1 (fun b => (g b).transpose) (fun b => by rw [Matrix.det_transpose]; exact hg b) hz h1
    let t : Ix Dw → (CAt σ)ˣ := fun i => match i with
      | none => s
      | some _ => 1
    rw [evR_frChg_tri hred hF t (fun _ => 1) (fun τ i j hij => Matrix.one_apply_ne hij.ne)
      (fun τ i => Matrix.one_apply_eq i) h2, hv, hG0]
    simp [evalFr]

end GlobalTheory.LamT
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

theorem GlobalTheory.LamF.lam_ind_len_deg :
    Formalism.L2.Pj.abelian₂.LamIndSt ∧ Formalism.L2.Pj.abelian₂.LamLenSt ∧
      ∀ (D : D7) (Q : Par D), Q.PinHost → ∀ large₂ : SizeData₂ D, Formalism.L2.Pj.abelian₂.LamDegSt Q.H large₂.logOm := by
  obtain ⟨hdeg, hind, hlen⟩ := GlobalTheory.T.cmLieStatements_iff_library
  have hL : ReciprocityTheory.ChartRestriction.G.Out.Laws := GlobalTheory.firstFiveLaws.1
  refine ⟨hind.1 GlobalTheory.LamF.Ind.lamInd, hlen.1 (GlobalTheory.LamF.lamLen GlobalTheory.thetaUnifAV_all hL), fun D Q hQ large₂ => ?_⟩
  obtain ⟨_, χ, hχ, h⟩ := GlobalTheory.T.exists_kronecker_cmLogPeriod_eq D Q hQ large₂
  rw [← h]
  exact (hdeg _ _ _).1 (GlobalTheory.LamF.lamDegSt_logOm GlobalTheory.thetaUnifAV_all hL _ Q.H χ hχ)
end

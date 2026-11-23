module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle029
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameBorelGroupoidProperties
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LinearDisjointAlgebraicClosure
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle033
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle528
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle108
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle028
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle015
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle035
import Formalism.LocalToGlobal.ProjectiveLattices.LocFrLoc
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle115
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle001
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.SplitMultiplicativeHopfOrder
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.Bundle013
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.Bundle004
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.Bundle006
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle061
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle260
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle274
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle273
public import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdaptedAtlasSncSection
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle012
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Bundle001
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

theorem _root_.GlobalTheory.T.exists_family_uniformisation : ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Z : Comp Xo c) (r : ℕ) (U : Unf Xo c c.F.val.toRingHom r), 1 ≤ r → IsUnf U → (∀ b : Om Z, IsAlgebraic c.F b → b ∈ (algebraMap c.F (Om Z)).range) → ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n), IsTypeFn H D.p D.q ty ∧ ∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → (Set.range y ⊆ (Z : Set (Xo.XF c)) ↔ ∃ P, IsPeriod (FU.Di i) ty P ∧ under y = FU.u i P) := by
  intro E _ _ _ H D l Xo c Z r U h1 hU hac
  have hσ : GoodEmb c c.F.val.toRingHom := rfl
  obtain ⟨-, -, hcov, -, -, g, e, F, ik, φ, hEF, hP⟩ := id hU
  have hty : IsTypeFn H D.p D.q (fun j => relab c c.F.val.toRingHom (e j).1) :=
    (GlobalTheory.Relab.relab_good E H l c _ hσ).2.2.2 D g e
  have hinj := (GlobalTheory.CompBij.ik_bijective E H D l Xo c _ r U h1 hσ hU g e F ik φ hEF
    fun k x => (hP k x).imp fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩).1
  obtain ⟨-, -, hG, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H D l Xo c
  choose q hq using GlobalTheory.UnifComp.exists_liesOn (Formalism.L2.PjFree.Unf.ofPj U) hU
  obtain ⟨k, hk⟩ := GlobalTheory.CompModel.exists_model (Formalism.L2.PjFree.Unf.ofPj U) hU hG Z
  have hqk : q k = Z := GlobalTheory.UnifComp.eq_of_carries hk (hq k)
  have comp_eq_of_algClosedAt {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf U) (h : GenFrEx Xo c)
      (Z : Comp Xo c) (hac : ∀ a : Om Z, IsAlgebraic c.F a → a ∈ (algebraMap c.F (Om Z)).range)
      (k k' : U.Comp) (x : (U.X k).dom) (x' : (U.X k').dom)
      (hk : ∃ (φ : Om Z →ₐ[c.F] CAt σ) (y' : FrPt Xo c (CAt σ)) (t : Ix D → (CAt σ)ˣ),
        FrMap φ (genFr h Z) y' ∧ FrBor t (U.un k x) y')
      (hk' : ∃ (φ : Om Z →ₐ[c.F] CAt σ) (y' : FrPt Xo c (CAt σ)) (t : Ix D → (CAt σ)ˣ),
        FrMap φ (genFr h Z) y' ∧ FrBor t (U.un k' x') y') : k = k' := by
    obtain ⟨hL, -, -, hA⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H D l Xo c
    obtain ⟨-, hmul, hinv, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H D l Xo c (CAt σ)
    obtain ⟨C, ψ, z, t, hz, ht⟩ := hA h (Om Z) (genFr h Z)
    let : Algebra c.F C.R := C.R.algebra
    have hCZ : C.Z = Z := by
      by_contra hne
      let s₀ : Sp (Om Z) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Om Z))
      refine Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj Xo c C.Z Z hne) ?_ (GlobalTheory.AllWt.liesOn_genFr h Z s₀)
      rw [GlobalTheory.UnifComp.ptF_frBor ht, GlobalTheory.UnifComp.ptF_frMap hz, Scheme.Hom.comp_apply]
      let η : Sp C.R := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum C.R)
      let sC : Sp (Om C.Z) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Om C.Z))
      have he : spMap C.R.val.toRingHom sC = η :=
        PrimeSpectrum.ext (Ideal.comap_bot_of_injective C.R.val.toRingHom Subtype.val_injective)
      have hη : GlobalTheory.AllWt.ptF C.y η ∈ (C.Z : Set (Xo.XF c)) := by
        have hgen := GlobalTheory.AllWt.liesOn_genFr h C.Z sC
        rw [← GlobalTheory.UnifComp.ptF_frBor C.bor, GlobalTheory.UnifComp.ptF_frMap C.gen,
          Scheme.Hom.comp_apply, he] at hgen
        exact hgen
      have hspec : η ⤳ spMap ψ.toRingHom s₀ :=
        (PrimeSpectrum.le_iff_specializes (R := C.R) _ _).1 bot_le
      exact (hspec.map (GlobalTheory.AllWt.ptF C.y).continuous).mem_closed
        (isClosed_of_mem_irreducibleComponents _ C.Z.2) hη
    have : Algebra.Smooth c.F C.R := C.sm
    have hread : ∀ (k : U.Comp) (x : (U.X k).dom), (∃ (φ : Om Z →ₐ[c.F] CAt σ) (y' : FrPt Xo c (CAt σ))
        (t : Ix D → (CAt σ)ˣ), FrMap φ (genFr h Z) y' ∧ FrBor t (U.un k x) y') →
        ∃ f : C.R → ℂ, GlobalTheory.GeomConn.ReadOn (Formalism.L2.PjFree.Unf.ofPj U) C.y f k := by
      rintro k x ⟨φ, y', t', hy', ht'⟩
      obtain ⟨w, hw⟩ := hL.bc _ _ φ z
      exact ⟨_, φ.comp ψ, w, x, _, fun _ => rfl, PullbackSections.frMap_trans _ _ hz hw,
        hmul _ _ _ _ _ ht' (hinv _ _ _ (GlobalTheory.SupGeneric.frBor_of_frMap φ ht hw hy'))⟩
    obtain ⟨f, hf⟩ := hread k x hk
    obtain ⟨f', hf'⟩ := hread k' x' hk'
    refine GlobalTheory.GeomConn.ReadOn.eq_of_isPreconnected (U := Formalism.L2.PjFree.Unf.ofPj U) hσ hU ?_ hf hf'
    have hac' : ∀ a : Om C.Z, IsAlgebraic c.F a → a ∈ (algebraMap c.F (Om C.Z)).range := by
      rw [hCZ]; exact hac
    exact GlobalTheory.GeomConn.isPreconnected_points_over C.R.val Subtype.val_injective hac' σ
  have huniq : ∀ k', q k' = Z → k' = k := by
    intro k' hk'
    obtain ⟨Z', hZ'⟩ := GlobalTheory.CompModel.exists_comp (Formalism.L2.PjFree.Unf.ofPj U) hσ hU hG k'
    obtain rfl : Z' = Z := (GlobalTheory.UnifComp.eq_of_carries hZ' (hq k')).symm.trans hk'
    obtain ⟨P, w, x, t, hw, ht⟩ := hk
    obtain ⟨P', w', x', t', hw', ht'⟩ := hZ'
    exact comp_eq_of_algClosedAt U hσ hU hG Z' hac k' k x' x
      ⟨P', w', t', hw', ht'⟩ ⟨P, w, t, hw, ht⟩
  have hfr : ∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) →
      ∃ (k' : U.Comp) (x : (U.X k').dom) (t : Ix D → (CAt c.F.val.toRingHom)ˣ)
        (z : FrPt Xo c (CAt c.F.val.toRingHom)),
        FrBor t (U.un k' x) z ∧ z.x = under y ∧ GlobalTheory.AllWt.ptF z = y := by
    intro y hy
    have hover : under y ≫ Xo.s = sOf c ℂ := by
      show (y ≫ pullback.fst _ _) ≫ Xo.s = _
      rw [Category.assoc, pullback.condition, ← Category.assoc, hy, sOf, ← Spec.map_comp]
      rfl
    obtain ⟨z, hz⟩ := Formalism.L2.Pj.exists_frPt_local (Xo := Xo) (c := c) (L := ℂ)
      GlobalTheory.firstFiveLaws.2.1.secTwist (under y) hover
    obtain ⟨k', x, t, hb⟩ := hcov z
    refine ⟨k', x, t, z, hb, hz, ?_⟩
    apply pullback.hom_ext
    · exact (pullback.lift_fst _ _ _).trans hz
    · exact (pullback.lift_snd _ _ _).trans hy.symm
  refine ⟨g, _, F, ik k, hty, fun y hy => ⟨fun hZ => ?_, fun ⟨P, hP', hPy⟩ => ?_⟩⟩
  · obtain ⟨k', x, t, z, hb, hzx, hzy⟩ := hfr y hy
    have hk' : q k' = Z := by
      by_contra hne
      let s₀ : Sp ℂ := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
      refine Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj Xo c _ _ hne) ?_ (hZ ⟨s₀, rfl⟩)
      have := hq k' x s₀
      change GlobalTheory.AllWt.ptF (U.un k' x) s₀ ∈ _ at this
      rwa [← GlobalTheory.UnifComp.ptF_frBor hb, hzy] at this
    obtain rfl := huniq k' hk'
    obtain ⟨Pm, -, hPm, hx, -⟩ := hP k' x
    exact ⟨Pm, hPm, hzx.symm.trans (hb.1.trans hx)⟩
  · obtain ⟨k', x, t, z, hb, hzx, hzy⟩ := hfr y hy
    obtain ⟨Pm, -, hPm, hx, -⟩ := hP k' x
    have e1 : ik k' = ik k := F.disj _ _ Pm P hPm hP' (hx.symm.trans (hb.1.symm.trans (hzx.trans hPy)))
    obtain rfl := hinj e1
    rintro _ ⟨s, rfl⟩
    rw [← hqk, ← hzy, GlobalTheory.UnifComp.ptF_frBor hb]
    exact hq k' x s
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT


theorem _root_.GlobalTheory.CompanionTheory.Relay.arith_variety_model_hodge_relay : GlobalTheory.CompanionTheory.Ar.GR.HodgeTateDatumStatement → GlobalTheory.CompanionTheory.Ar.GR.OrdinaryCurveStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∀ [DecidableEq F] [Fintype (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)] [DecidableEq (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)], ∀ (v : Valuation C NNReal), (∀ c, c ∈ RC ↔ v c ≤ 1) → v (p : C) < 1 → GlobalTheory.CompanionTheory.Ar.GR.IsAbFactor p (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testOrd P RC) ∧ GlobalTheory.CompanionTheory.Ar.GR.IsTight v p (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testOrd P RC) := by
  first | exact @PositivityTheory.Xgn.tight_hopf_order_test | exact PositivityTheory.Xgn.tight_hopf_order_test
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM

theorem flatDegree_mean_ext {M k : Type} [Field M] [NumberField M] [Field k] [NumberField k] (f : M →+* k)
    (F : (M →+* ℂ) → ℝ) :
    (∑ s : k →+* ℂ, F (s.comp f)) / Module.finrank ℚ k = (∑ s, F s) / Module.finrank ℚ M := by
  have h := GlobalTheory.T.sum_embeddings_base_change M k ℂ f F
  have hM : (Module.finrank ℚ M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have hk : (Module.finrank ℚ k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  rw [div_eq_div_iff hk hM]
  linear_combination h

theorem flatDegree_sum_conj {E A : Type} [Field E] [NumberField E] [IsCMField E] [Field A] [CharZero A]
    (F : A → ℝ) (t : E) :
    ∑ j : E →+* A, F (j (IsCMField.complexConj E t)) = ∑ j : E →+* A, F (j t) := by
  let c : E →+* E := RingHomClass.toRingHom (IsCMField.complexConj E)
  let σ : (E →+* A) ≃ (E →+* A) :=
    { toFun := fun j => j.comp c
      invFun := fun j => j.comp c
      left_inv := fun j => RingHom.ext fun x => congrArg j (IsCMField.complexConj_apply_apply E x)
      right_inv := fun j => RingHom.ext fun x => congrArg j (IsCMField.complexConj_apply_apply E x) }
  exact Equiv.sum_comp σ (fun j => F (j t))

theorem flatDegree_logOm_re (E : Type) [Field E] [NumberField E] {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) {x : ℝ}
    (hx : (x : ℂ) = (Real.eulerMascheroniConstant + Real.log (2 * Real.pi / √d) : ℝ) -
      deriv χ.LFunction 1 / χ.LFunction 1) :
    (logOm E χ).re = x - Real.log (rootDiscr E) + Real.log (Real.sqrt d) := by
  have hrd : 0 < rootDiscr E := by
    rw [NumberField.rootDiscr_def]
    apply Real.rpow_pos_of_pos
    exact_mod_cast abs_pos.mpr (NumberField.discr_ne_zero E)
  have hd : 0 < √(d : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d))
  have hL : deriv χ.LFunction 1 / χ.LFunction 1 =
      ((Real.eulerMascheroniConstant + Real.log (2 * Real.pi / √d) : ℝ) : ℂ) - x := by
    rw [hx]; ring
  unfold GlobalTheory.CM.logOm
  rw [hL]
  simp only [Complex.sub_re, Complex.ofReal_re]
  rw [Real.log_div (by positivity) hrd.ne', Real.log_div (by positivity) hd.ne']
  ring

theorem flatDegree : FlatDegree := by
  unfold FlatDegree
  intro E _ _ _ H D l Xo c g ty FU i U τ φ _ N _ χ hχ hty hrt hflat hN
  obtain ⟨mem, line, ⟨e, ρ, hli, hcm⟩⟩ := hflat
  obtain ⟨hNinf, hNfin⟩ := hN
  have hsq : ∀ b : Bool, sgnRt H b ^ 2 = -(H.d : ℂ) := by
    intro b
    cases b <;> simp [sgnRt, neg_sq, H.sqrt_neg_disc_sq]
  choose Z x hz hper hxv using fun b => GlobalTheory.T.chowla_selberg_period E H χ hχ (sgnRt H b) (hsq b)
  have hx : x false = x true := Complex.ofReal_injective ((hxv false).trans (hxv true).symm)
  haveI := (Z true).nf
  haveI := (Z false).nf
  obtain ⟨n₁, hn₁, hm₁⟩ := hper true
  obtain ⟨n₀, hn₀, hm₀⟩ := hper false
  obtain ⟨k, hkfd, r, hc, hM, hr0, hrz⟩ :=
    GlobalTheory.T.frame_function_cm_value E H D l Xo c g ty FU i Z U τ φ e ρ hty hrt mem line hli hcm
  haveI := hkfd
  haveI : NumberField k := ⟨⟩
  choose t ht1 ht2 ht3 using fun ℓ : Nat.Primes =>
    GlobalTheory.T.frame_function_cm_height E H D l Xo c g ty FU i Z U τ φ e ρ k hc hM r ℓ hty hrt mem line hli hcm hr0 hrz
  have hgram := GlobalTheory.T.gram_det_ne_zero_local_basis_cofinite E H (FU.Di i) (Fin D.p ⊕ Fin D.q) e
    (by rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, (FU.sig i).1, (FU.sig i).2]) hli
  have hrt2 : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have h := congrArg (algebraMap (NumberField.RingOfIntegers E) E) H.rt_sq
    rw [map_pow, map_neg, map_natCast] at h
    exact h
  have hmean₁ := flatDegree_mean_ext (IntermediateField.inclusion (hM true)).toRingHom
    (fun σ => Real.log (n₁ σ))
  have hmean₀ := flatDegree_mean_ext (IntermediateField.inclusion (hM false)).toRingHom
    (fun σ => Real.log (n₀ σ))
  have hfinite : {ℓ : Nat.Primes | ∃ j : E →+* ℂ_[ℓ], Real.log ‖j (t ℓ)‖ ≠ 0}.Finite := by
    apply hgram.2.subset
    intro ℓ hℓ hloc
    obtain ⟨j, hj⟩ := hℓ
    exact hj (ht2 ℓ hloc j)
  have key := GlobalTheory.T.hermitian_metric_log_norm_formula (↥k) E (RingHom.comp (IntermediateField.inclusion hc : ↥c.F →+* ↥k) (GlobalTheory.CompanionTheory.Ar.Fl.tauE c τ))
    (N.ext (IntermediateField.inclusion hc).toRingHom) r (GlobalTheory.CompanionTheory.Ar.Fl.gramE (FU.Di i) e).det
    (H.rt : E) D.p D.q H.d
    (fun s => n₁ (s.comp (IntermediateField.inclusion (hM true)).toRingHom))
    (fun s => n₀ (s.comp (IntermediateField.inclusion (hM false)).toRingHom))
    (x true) t (fun ℓ => IsCMField.complexConj E (t ℓ))
    hr0 hgram.1 (Nat.Prime.pos H.d_prime) hrt2
    (by rw [neg_div, hmean₁, ← hm₁]; rfl)
    (by rw [neg_div, hmean₀, ← hx, ← hm₀]; rfl)
    (fun s => GlobalTheory.T.frame_function_cm_number_field E H D l Xo c g ty FU i Z U τ φ e ρ k hc hM r s
      (n₁ (s.comp (IntermediateField.inclusion (hM true)).toRingHom))
      (n₀ (s.comp (IntermediateField.inclusion (hM false)).toRingHom))
      (N.inf (s.comp (IntermediateField.inclusion hc).toRingHom))
      hty hrt mem line hli hcm hr0 hrz
      (hn₁ _).1 (hn₀ _).1 (((hn₁ _).2 _).mpr rfl) (((hn₀ _).2 _).mpr rfl)
      (hNinf _))
    (fun ℓ => flatDegree_sum_conj (fun z : ℂ_[ℓ] => Real.log ‖z‖) (t ℓ))
    (fun ℓ j => ht1 ℓ j) hfinite
    (fun ℓ j => ht3 ℓ j _ (hNfin ℓ (j.comp (IntermediateField.inclusion hc).toRingHom)))
  obtain ⟨hAd, hdeg⟩ := key
  obtain ⟨hdeg', hAd'⟩ := GlobalTheory.CompanionTheory.Ar.Fl.logNorms_ext_deg_isAdelic (↥c.F) (↥k)
    (IntermediateField.inclusion hc).toRingHom N
  refine ⟨hAd'.mp hAd, ?_⟩
  rw [← hdeg', hdeg, flatDegree_logOm_re E χ (hxv true)]

end GlobalTheory.CompanionTheory.Ar.Fl
end
end

section

open GlobalTheory.CompanionTheory.Ar AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam
open MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open Classical


theorem _root_.GlobalTheory.T.adapted_atlas_snc_section : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (L : LocPot X)
    (s : X → X → ℂ) {n : ℕ} (m : Fin n → ℕ) (W : Fin n → Set X), IsPotential A L → IsSection A L s → IsSNC A L s m W →
    (∀ y, logNormSec L s y ≤ 0) → ∃ B : FinHolAtlas e X, IsAdaptedAtlas A B L s := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Adapt.exists_adaptedAtlas | exact GlobalTheory.CompanionTheory.Ar.Adapt.exists_adaptedAtlas | (intros; apply GlobalTheory.CompanionTheory.Ar.Adapt.exists_adaptedAtlas <;> assumption)
end

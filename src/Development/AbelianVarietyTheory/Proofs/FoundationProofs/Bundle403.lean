module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonnegOfMemCStarSet
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsNonzeroOfGenerator
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle176
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle014
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle004
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle032
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle105
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle109
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle016
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle341
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle034
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StrictVanishingDualOfLiterature
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle373
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle374
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalCochainsGlueGlobal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardOrdinaryLocalConditionModPrimePowLeConstMul
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoordIntOfJets
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle402
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnramifiedH1CardInvariants
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle194
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTermsNormsIndependentRepresenta
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivationDenominatorsAndHostFieldSizes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle221
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ
open scoped Matrix

theorem _root_.GlobalTheory.T.tate_discrete_inertia_kummer_coboundary_bound : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A →
  ∀ (m k : ℕ), k ≤ m → ∀ (ζ ζ' : Ω), IsPrimitiveRoot ζ (l ^ m) → ζ' ^ (l ^ m) = ζ → ∀ o x : Ω, o ∈ A → x ∈ A →
  (∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m s = 1 → s o = o) →
  (∀ s, s ∈ Ine (F := ℚ) A → cycMod ℚ Ω l m s = 1 → ∀ t : ZMod (l ^ m), s ζ' = ζ ^ t.val * ζ' →
    GlobalTheory.Glue.CgA A l k ((t.val : Ω) * o) (s x - x)) →
  GlobalTheory.Glue.CgA A l k ((l : Ω) ^ c * o) 0 := by
  first | exact @GlobalTheory.HTTrace.main | exact GlobalTheory.HTTrace.main | (intros; apply GlobalTheory.HTTrace.main <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.strict_vanishing_dual_of_literature : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ES W A → StrZero (dual1 W) A := by
  first | exact @GlobalTheory.Ord2.StrictKill.main | exact GlobalTheory.Ord2.StrictKill.main | (intros; apply GlobalTheory.Ord2.StrictKill.main <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SlopeRec

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.AllWt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem hasVal_of_irreducible {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ ϖ' : V}
    (h : Irreducible ϖ) (h' : Irreducible ϖ') {x : FractionRing V} {n : ℤ} (hx : HasVal ϖ' x n) : HasVal ϖ x n := by
  obtain ⟨v, rfl⟩ := IsDiscreteValuationRing.associated_of_irreducible V h h'
  obtain ⟨u, rfl⟩ := hx
  refine ⟨v ^ n * u, ?_⟩
  have e : algebraMap V (FractionRing V) ((v ^ n : Vˣ) : V) = algebraMap V (FractionRing V) v ^ n := by
    have := congrArg Units.val (map_zpow (Units.map (algebraMap V (FractionRing V)).toMonoidHom) v n)
    rwa [Units.val_zpow_eq_zpow_val] at this
  rw [Units.val_mul, map_mul, map_mul, mul_zpow, e, _root_.mul_assoc]

theorem nonempty_sabMap_of_models {T : CDVR} {x : Sp T.Fr ⟶ Xo.X} {G G' : SAB H (Sp T.V)} {t t' : SAB H (Sp T.Fr)}
    (m1 : SABMap t Xo.univ.t x) (m2 : SABMap t G (spMap (algebraMap T.V T.Fr)))
    (m1' : SABMap t' Xo.univ.t x) (m2' : SABMap t' G' (spMap (algebraMap T.V T.Fr))) :
    Nonempty (SABMap G' G (𝟙 _)) := by
  obtain ⟨k, -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ (𝟙 _) m1 ((Category.id_comp x).symm ▸ m1')
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m2 k
  have hp : IsProper t'.G.hom := MorphismProperty.of_isPullback (P := @IsProper) m1'.cart.1 Xo.univ.proper
  obtain ⟨ψ, -⟩ := GlobalTheory.semiAbelian_model_determined_by_generic_fibre E H T.V inferInstance G' G t' hp m2'
    (Category.id_comp (spMap (algebraMap T.V T.Fr)) ▸ n)
  exact ⟨ψ⟩

theorem HasPhi.unique {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {φ φ' : ℝ} (h : HasPhi y φ)
    (h' : HasPhi y φ') : φ = φ' := by
  obtain ⟨G, t, m1, m2, P, ϖ, Q, β, hϖ, hQ, -, hβ, rfl⟩ := h
  obtain ⟨G', t', m1', m2', P', ϖ', Q', β', hϖ', hQ', -, hβ', rfl⟩ := h'
  obtain ⟨ψ⟩ := nonempty_sabMap_of_models m1 m2 m1' m2'
  obtain ⟨d, hd⟩ := GlobalTheory.SameCoord.exists_equiv_psiCoord E H T.V G G' ψ P P' inferInstance inferInstance inferInstance
  have hQQ : ∀ χ, Q' (d χ) = Q χ := fun χ => by
    obtain ⟨r, hr, -⟩ := (GlobalTheory.PsiCoordLocal.main T.V P.D inferInstance χ).1
    obtain ⟨u, hu⟩ := hd χ r hr
    have h1 := hasVal_mul_unit (GlobalTheory.ValForm.hasVal_coord (hQ χ) hr) u
    have h2 := hasVal_of_irreducible hϖ hϖ' (GlobalTheory.ValForm.hasVal_coord (hQ' (d χ)) hu)
    rw [← map_mul, _root_.mul_comm] at h1
    exact hasVal_unique hϖ h2 h1
  obtain ⟨β₁, hβ₁, hφ⟩ := GlobalTheory.EtaVal.phiC_smul_pull E _ _ _ d β' 1 zero_le_one
  have hdiag : ∀ a, β₁.1 a a = β.1 a a := fun a => by
    rw [hβ₁, hβ', hβ, hQQ, _root_.one_mul]
  have e : β₁ = β := by
    refine Subtype.ext (LinearMap.ext fun a => LinearMap.ext fun b => ?_)
    have h1 := hdiag (a + b)
    have s1 := β₁.2.1 a b
    have s2 := β.2.1 a b
    simp only [map_add (f := _), LinearMap.add_apply] at h1
    linarith [hdiag a, hdiag b]
  rw [← e, hφ, _root_.one_mul]

theorem exists_ext_hasPhi {la : HeightOneSpectrum (𝓞 c.F)} {T : CDVR} {io : c.F →+* T.Fr} {e : ℕ}
    (ho : OverLa la T.V io e) (y : IntFr Xo c T io) (hy : y.IsAlg) :
    ∃ (T' : CDVR) (i : T.Fr →+* T'.Fr) (e' : ℕ) (y' : IntFr Xo c T' (i.comp io)) (φ : ℝ),
      i.Finite ∧ OverLa la T'.V (i.comp io) e' ∧ y'.IsAlg ∧ HasPhi y' φ ∧
      (letI := io.toAlgebra; letI := (i.comp io).toAlgebra;
        FrMap ({ i with commutes' := fun _ => rfl } : T.Fr →ₐ[c.F] T'.Fr) y.1 y'.1) ∧
      ∀ f : Rul Xo c, IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f →
        evI y' f = i (evI y f) ∧ nval T'.V e' (evI y' f) = nval T.V e (evI y f) := by
  let _ := H.starRing
  obtain ⟨T', i, y', e', hi, ho', hy', -, hm, hv, C, -, P, -⟩ :=
    GlobalTheory.IntegralExt.exists_ext_chart_unif E H Dw l Xo c T io y la e ho hy
  obtain ⟨φ, hφ⟩ := exists_hasPhi y' C.I.G C.I.t' C.I.m1 C.I.m2 P
  exact ⟨T', i, e', y', φ, hi, ho', hy', hφ, hm, hv⟩

theorem hasPhi_exists_ext_and_unique :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
      (l : Level H) (Xo : Moduli Dw l) (c : Coeff l),
      (∀ (p : ℕ) (la : PointsOfFlagModel.abelian₂ p c) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e →
        ∀ y : IntFr Xo c T io, y.IsAlg →
          ∃ (T' : CDVR) (i : T.Fr →+* T'.Fr) (e' : ℕ) (y' : IntFr Xo c T' (i.comp io)) (φ : ℝ),
            i.Finite ∧ OverLa la.1 T'.V (i.comp io) e' ∧ y'.IsAlg ∧ HasPhi y' φ ∧
            ∀ (w : Ix Dw → ℤ) (f : Rul Xo c), f ∈ secZ Xo c w →
              evI y' f = i (evI y f) ∧ nval T'.V e' (evI y' f) = nval T.V e (evI y f)) ∧
      ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (φ φ' : ℝ), HasPhi y φ → HasPhi y φ' → φ = φ' := by
  intro E _ _ _ H Dw l Xo c
  refine ⟨fun p la T io e ho y hy => ?_, fun _ _ _ _ _ => HasPhi.unique⟩
  obtain ⟨T', i, e', y', φ, hi, ho', hy', hφ, -, hv⟩ := exists_ext_hasPhi ho y hy
  exact ⟨T', i, e', y', φ, hi, ho', hy', hφ, fun w f hf => hv f hf.1⟩

end GlobalTheory.SlopeRec
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal

theorem _root_.GlobalTheory.T.mem_inertiaInvariantsCyclotomicAlgebra_iff : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ x : A, x ∈ cycAlg l A ↔ ∀ s ∈ ineCyc l A, s (x : Ω) = x := by
  first | (exact @GlobalTheory.RecOne.mem_cycAlg_iff) | (exact GlobalTheory.RecOne.mem_cycAlg_iff) | (intros; apply GlobalTheory.RecOne.mem_cycAlg_iff  <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.GwIneq

theorem exists_cc (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] :
    ∃ cc : InfinitePlace ℚ → G ℚ Ω, ∀ w, w.IsReal → IsCCAt w (cc w) := by
  have h : ∀ w : InfinitePlace ℚ, ∃ c : G ℚ Ω, w.IsReal → IsCCAt w c := fun w => by
    by_cases hw : w.IsReal
    · haveI : Module.IsTorsionFree ℚ Ω := DivisionSemiring.to_moduleIsTorsionFree
      haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
      haveI : IsGalois ℚ Ω := {}
      letI : Algebra ℚ ℂ := w.embedding.toAlgebra
      let j : Ω →ₐ[ℚ] ℂ := (by
        refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
        solve_by_elim* (maxDepth := 2) only [*,
          @_root_.DivisionSemiring.to_moduleIsTorsionFree,
          @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
      have hr : ComplexEmbedding.IsReal w.embedding := InfinitePlace.isReal_iff.1 hw
      let cj : ℂ →ₐ[ℚ] ℂ := { starRingEnd ℂ with commutes' := fun x => RingHom.congr_fun hr x }
      letI : Algebra Ω ℂ := j.toRingHom.toAlgebra
      haveI : IsScalarTower ℚ Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
      refine ⟨(cj.comp j).restrictNormal' Ω, fun _ => ⟨j.toRingHom, fun x => ?_, ?_⟩⟩
      · exact AlgHom.restrictNormal_commutes (cj.comp j) Ω x
      · rw [show j.toRingHom.comp (algebraMap ℚ Ω) = w.embedding from RingHom.ext fun x => j.commutes x]
        exact w.mk_embedding
    · exact ⟨1, fun h => absurd h hw⟩
  choose cc hcc using h
  exact ⟨cc, hcc⟩

theorem gw_ineq : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ c : Coef l, (∀ s i j, mat W s i j ∈ c.O) → ∃ C : ℕ, ∀ n : ℕ, 1 ≤ n → ∀ (N : ℕ) (y : Fin N → G ℚ Ω → Fin 2 → Qbar l), (∀ i, GwCount.SelN c n S A W (y i)) → (∀ i j, i ≠ j → ¬ Cob1 c n W ⊤ (y i - y j)) → ∃ (N' : ℕ) (z : Fin N' → G ℚ Ω → Fin 2 → Qbar l), N ≤ C * N' ∧ (∀ i, GwCount.SelN c n S A (dual1 W) (z i)) ∧ ∀ i j, i ≠ j → ¬ Cob1 c n (dual1 W) ⊤ (z i - z j) := by
  classical
  intro hL l _ Ω _ _ _ e S A W hW c hint
  have hN := kills_NS hW
  obtain ⟨C0, hC0⟩ := GlobalTheory.T.card_galoisInvariants_ordinaryRankTwo_mod_pow_bounded l Ω e S A W hW c hint hN
  obtain ⟨CA, hCA⟩ := GlobalTheory.T.card_ordinaryLocalConditionModPrimePow_le_const_mul hL l Ω e S A W hW c hint hN
  refine ⟨C0 * CA, fun n hn N y hy hyd => ?_⟩
  have hn0 : 0 < n := hn
  have hS := hW.above
  obtain ⟨μ, hμ⟩ := GlobalTheory.Published.PoitouTate.exists_lift_cycMod (F := ℚ) (Ω := Ω) (l := l) (r := n) (S := S) hS
  obtain ⟨cc, hcc⟩ := exists_cc Ω
  have hρ : ReciprocityTheory.Gal.ContAction (rhoS c n W hint S hN) := contAction_rhoS c n W hint S hN hW.cont
  have hgw := hL.gw ℚ Ω l n (Mn c n) S (rhoS c n W hint S hN) hn0 hW.l_odd hS hρ μ hμ (Av A S)
    (isPlaceOver_Av A S) cc hcc (Lc c n W hint S hN A)
  have hρd : ReciprocityTheory.Gal.ContAction (twDual μ (rhoS c n W hint S hN)) :=
    GlobalTheory.DualSide.contAction_twDual (GlobalTheory.Published.PoitouTate.contAction_charRep hμ) hρ
  haveI : Finite (TDual (ZMod (l ^ n)) (Mn c n)) := GlobalTheory.DualSide.finite_TDual
  haveI : Finite (H1 (rhoS c n W hint S hN)) := (hL.gf ℚ Ω l n (Mn c n) S _ hn0 hS hρ).2.1
  haveI : Finite (H1 (twDual μ (rhoS c n W hint S hN))) :=
    (hL.gf ℚ Ω l n (TDual (ZMod (l ^ n)) (Mn c n)) S _ hn0 hS hρd).2.1

  obtain ⟨v0, hA0, hl0⟩ := hW.atL
  let vA : S := ⟨v0, hS v0 hl0⟩
  have huniq : ∀ v w : Pl, IsPlaceOver A v → IsPlaceOver A w → v = w := fun v w hv hw =>
    HeightOneSpectrum.ext (Ideal.ext fun x => (hv x).symm.trans (hw x))
  have hLv : ∀ v : S, v ≠ vA → Nat.card (Lc c n W hint S hN A v) =
      Nat.card (H0 ((rhoS c n W hint S hN).comp (locFam S (Av A S) v))) := by
    intro v hv
    have hnp : ¬ IsPlaceOver A v.1 := fun h => hv (Subtype.ext (huniq _ _ h hA0))
    have e1 : Lc c n W hint S hN A v = H1ur ((rhoS c n W hint S hN).comp (locFam S (Av A S) v))
        ((Ine (F := ℚ) (Av A S v)).subgroupOf (Dec (F := ℚ) (Av A S v))) := if_neg hnp
    rw [e1]
    exact GlobalTheory.Ord2.UrCard.card_unramified_h1_eq_card_h0 ℚ Ω l n (Mn c n) (Av A S v) v.1 _
      (hρ.comp' (continuous_locFam S (Av A S) v)) (isPlaceOver_Av A S v)
  have harch := GlobalTheory.T.archimedean_invariants_card l Ω e S A W hW c hint hN n hn cc hcc
  rw [harch, ← Finset.mul_prod_erase _ _ (Finset.mem_univ vA),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ vA),
    Finset.prod_congr rfl fun v hv => hLv v (Finset.ne_of_mem_erase hv)] at hgw
  have hLA := hCA n hn vA hA0
  have hH0 := hC0 n hn
  have hP : 0 < ∏ v ∈ Finset.univ.erase vA, Nat.card (H0 ((rhoS c n W hint S hN).comp (locFam S (Av A S) v))) :=
    Finset.prod_pos fun v _ => Nat.card_pos
  have hq : 0 < Nat.card (Qn c n) := Nat.card_pos
  have h1d : 1 ≤ Nat.card (H0 (twDual μ (rhoS c n W hint S hN))) := Nat.card_pos
  have h1A : 1 ≤ Nat.card (H0 ((rhoS c n W hint S hN).comp (locFam S (Av A S) vA))) := Nat.card_pos
  set P := ∏ v ∈ Finset.univ.erase vA, Nat.card (H0 ((rhoS c n W hint S hN).comp (locFam S (Av A S) v)))
  have hsel : Nat.card (SelG c n W hint S hN A) ≤ C0 * CA * Nat.card (SelD c n W hint S hN A hW.cont μ) := by
    have key : Nat.card (SelG c n W hint S hN A) * (Nat.card (Qn c n) * P) ≤
        (C0 * CA * Nat.card (SelD c n W hint S hN A hW.cont μ)) * (Nat.card (Qn c n) * P) := by
      calc Nat.card (SelG c n W hint S hN A) * (Nat.card (Qn c n) * P)
          = Nat.card (SelG c n W hint S hN A) * 1 * (1 * P) * Nat.card (Qn c n) := by ring
        _ ≤ Nat.card (SelG c n W hint S hN A) * Nat.card (H0 (twDual μ (rhoS c n W hint S hN))) *
            (Nat.card (H0 ((rhoS c n W hint S hN).comp (locFam S (Av A S) vA))) * P) * Nat.card (Qn c n) := by
          gcongr
        _ = Nat.card (SelD c n W hint S hN A hW.cont μ) * Nat.card (H0 (rhoS c n W hint S hN)) *
            (Nat.card (Lc c n W hint S hN A vA) * P) := hgw
        _ ≤ Nat.card (SelD c n W hint S hN A hW.cont μ) * C0 * (CA * Nat.card (Qn c n) * P) := by
          gcongr
        _ = (C0 * CA * Nat.card (SelD c n W hint S hN A hW.cont μ)) * (Nat.card (Qn c n) * P) := by ring
    exact Nat.le_of_mul_le_mul_right key (Nat.mul_pos hq hP)

  obtain ⟨cls, hcls, hinj⟩ := GlobalTheory.T.ordinarySelmerModPrimePow_injects_residualSelmer l Ω e S A W hW c hint hN n hn
  have hN1 : N ≤ Nat.card (SelG c n W hint S hN A) := by
    let f : Fin N → SelG c n W hint S hN A := fun i => ⟨cls (y i), hcls _ (hy i)⟩
    have hf : Function.Injective f := by
      intro i j hij
      by_contra hne
      exact hyd i j hne (hinj _ _ (hy i) (hy j) (congrArg Subtype.val hij))
    simpa using Nat.card_le_card_of_injective f hf

  obtain ⟨z, hz, hzd⟩ := GlobalTheory.T.dualSelmer_classes_give_noncohomologous_cochains hL l Ω e S A W hW c hint hN n hn μ hμ
  let eqv := Finite.equivFin (SelD c n W hint S hN A hW.cont μ)
  refine ⟨Nat.card (SelD c n W hint S hN A hW.cont μ), fun i => z (eqv.symm i), ?_, fun i => hz _, ?_⟩
  · exact hN1.trans hsel
  · intro i j hij
    exact hzd _ _ (fun h => hij (eqv.symm.injective h))

end GlobalTheory.Ord2.GwIneq
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum.DenomBound

theorem sum_val_log_le (S : Finset ℕ) (hS : ∀ l ∈ S, l.Prime) (n : ℕ) :
    ∑ l ∈ S, (padicValNat l n : ℝ) * Real.log l ≤ Real.log n := by
  rw [Real.log_nat_eq_sum_factorization,
    Finsupp.sum_of_support_subset _ (Finset.subset_union_right (s₁ := S)) _ (by simp)]
  simp_rw [Nat.padicValNat_def]
  rw [← Finset.sum_congr rfl fun (l : ℕ) (hl : l ∈ S) =>
    congrArg (fun t : ℕ => (t : ℝ) * Real.log l) (Nat.factorization_def n (hS l hl))]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun l _ _ =>
    mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)

theorem log_order_le (x : ℕ) (hx : 2 ≤ x) :
    Real.log ((8 ^ (2 * x) * (4 * x).factorial : ℕ) : ℝ) ≤ 18 * x * Real.log x := by
  have h1 : 8 ^ (2 * x) ≤ x ^ (6 * x) := by
    rw [show 6 * x = 3 * (2 * x) by ring, pow_mul x]
    exact Nat.pow_le_pow_left (by simpa using Nat.pow_le_pow_left hx 3) _
  have h2 : (4 * x).factorial ≤ x ^ (12 * x) := by
    refine (Nat.factorial_le_pow _).trans ?_
    rw [show 12 * x = 3 * (4 * x) by ring, pow_mul x]
    refine Nat.pow_le_pow_left ?_ _
    rw [pow_succ]
    exact Nat.mul_le_mul_right _ (by simpa using Nat.pow_le_pow_left hx 2)
  have h3 : 8 ^ (2 * x) * (4 * x).factorial ≤ x ^ (18 * x) := by
    rw [show 18 * x = 6 * x + 12 * x by ring, pow_add]
    exact Nat.mul_le_mul h1 h2
  calc _ ≤ Real.log ((x ^ (18 * x) : ℕ) : ℝ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast h3)
    _ = _ := by rw [Nat.cast_pow, Real.log_pow]; push_cast; ring

noncomputable def expo_vp (f N d Q : ℕ) (B : ℝ) (dl : ℕ → ℝ) (p : ℕ) : ℝ :=
  (padicValNat p (8 ^ (4 * f * N) * (8 * f * N).factorial) : ℝ) +
    4 * f * N * B * (dl p + (if p = d then 1 / 4 else 0) + (padicValNat p Q : ℝ)) +
    4 * (N : ℝ) ^ 2 * (padicValNat p Q : ℝ)

theorem exists_exponents (f N d Q : ℕ) (B L : ℝ) (S : Finset ℕ) (dl : ℕ → ℝ) (hf : 1 ≤ f) (hN : 1 ≤ N) (hB : 1 ≤ B)
    (hL : 1 ≤ L) (hQ : 0 < Q) (h0 : ∀ l, 0 ≤ dl l) (hz : ∀ l, l ∉ S → dl l = 0)
    (hs : ∑ l ∈ S, dl l * Real.log l ≤ L) (hd : Real.log d ≤ 2 * L) :
    ∃ S' : Finset ℕ, Exponents S' (fun p => if p.Prime then expo_vp f N d Q B dl p else 0) (intBound 18 f N B L Q) := by
  set M : ℕ := 8 ^ (4 * f * N) * (8 * f * N).factorial with hM
  have hM0 : M ≠ 0 := by positivity
  set S' : Finset ℕ := (M.primeFactors ∪ S ∪ {d} ∪ Q.primeFactors).filter Nat.Prime with hS'
  have hP : ∀ l ∈ S', l.Prime := fun l hl => (Finset.mem_filter.1 hl).2
  refine ⟨S', hP, fun l => ?_, fun l hl => ?_, ?_⟩
  · have := h0 l
    have hB0 : 0 ≤ B := by linarith
    unfold expo_vp
    dsimp only
    split_ifs <;> positivity
  · dsimp only
    split_ifs with hp
    · simp only [hS', Finset.mem_filter, hp, and_true, Finset.mem_union, not_or, Finset.mem_singleton,
        Nat.mem_primeFactors, true_and, ne_eq, hM0, hQ.ne', not_false_eq_true] at hl
      obtain ⟨⟨⟨a1, a2⟩, a3⟩, a4⟩ := hl
      unfold expo_vp
      rw [← hM, Nat.padicValNat_def, Nat.padicValNat_def, padicValNat.eq_zero_of_not_dvd a1, padicValNat.eq_zero_of_not_dvd a4, hz l a2, if_neg a3]
      simp
    · rfl
  · have e1 := sum_val_log_le S' hP M
    have e2 := sum_val_log_le S' hP Q
    have e3 : ∑ l ∈ S', dl l * Real.log l ≤ L := by
      refine le_trans ?_ hs
      rw [Finset.sum_subset (s₁ := S) (s₂ := S ∪ S') Finset.subset_union_left (fun l _ hl => by rw [hz l hl, zero_mul])]
      exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right fun l _ _ =>
        mul_nonneg (h0 l) (Real.log_natCast_nonneg _)
    have e4 : ∑ l ∈ S', (if l = d then (1 / 4 : ℝ) else 0) * Real.log l ≤ L / 2 := by
      simp only [ite_mul, zero_mul, Finset.sum_ite_eq']
      split_ifs <;> linarith
    have e5 : Real.log M ≤ 18 * (f * (2 * N)) * Real.log (f * (2 * N)) := by
      have := log_order_le (f * (2 * N)) (by nlinarith)
      rw [show 2 * (f * (2 * N)) = 4 * f * N by ring, show 4 * (f * (2 * N)) = 8 * f * N by ring, ← hM] at this
      push_cast at this
      exact this
    have e6 : ∑ l ∈ S', (if l.Prime then expo_vp f N d Q B dl l else 0) * Real.log l =
        ∑ l ∈ S', (padicValNat l M : ℝ) * Real.log l + 4 * f * N * B * (∑ l ∈ S', dl l * Real.log l +
          ∑ l ∈ S', (if l = d then (1 / 4 : ℝ) else 0) * Real.log l + ∑ l ∈ S', (padicValNat l Q : ℝ) * Real.log l) +
          4 * (N : ℝ) ^ 2 * ∑ l ∈ S', (padicValNat l Q : ℝ) * Real.log l := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun l hl => ?_
      rw [if_pos (hP l hl), expo_vp, ← hM]
      ring
    have hfR : (1 : ℝ) ≤ f := by exact_mod_cast hf
    have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hq : 0 ≤ Real.log Q := Real.log_natCast_nonneg _
    have hc : 0 ≤ 4 * (f : ℝ) * N * B := by positivity
    have hfB : 1 ≤ (f : ℝ) * B := by nlinarith
    have g1 := mul_le_mul_of_nonneg_left (add_le_add (add_le_add e3 e4) e2) hc
    have g2 := mul_le_mul_of_nonneg_left e2 (show 0 ≤ 4 * (N : ℝ) ^ 2 by positivity)
    have g3 : (N : ℝ) * (f * N * B * Real.log Q) ≥ 1 * (f * N * B * Real.log Q) :=
      mul_le_mul_of_nonneg_right hNR (by positivity)
    have g4 : (f : ℝ) * B * (N ^ 2 * Real.log Q) ≥ 1 * (N ^ 2 * Real.log Q) :=
      mul_le_mul_of_nonneg_right hfB (by positivity)
    have g5 : 0 ≤ (f : ℝ) * N * B * L := by positivity
    have g6 : 0 ≤ (f : ℝ) * N ^ 2 * B * Real.log Q := by positivity
    show ∑ l ∈ S', (if l.Prime then expo_vp f N d Q B dl l else 0) * Real.log l ≤ _
    rw [e6, intBound]
    nlinarith

theorem exists_prime_mem {K : Type} [Field K] [NumberField K] (w : Formalism.PairingDivisionLocalBalance.Pl K) :
    ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ w.asIdeal := by
  have := w.isMaximal
  obtain ⟨p, n, -, h, hp, -⟩ := Ideal.exists_prime_and_absNorm_eq_pow w.asIdeal
  exact ⟨p, hp, h⟩

theorem intSt_of_forall_inp : (∀ D, Inp D) → IntSt := by
  intro hI
  refine ⟨18, by norm_num, fun D Q N B L hQ hN hB hL hr => ?_⟩
  obtain ⟨⟨S, dl, hLet⟩, hd, -, hf, -⟩ := letters_and_sizes D (hI D).g1
  obtain ⟨S', hE⟩ := exists_exponents (fF D) N D.host.d Q B L S dl hf hN hB hL hQ.1 hLet.2.1 hLet.2.2.1
    (hLet.2.2.2.1.trans hr) (by linarith)
  refine ⟨S', _, hE, ?_, ?_⟩
  · intro δ t0 p hp Q' hQ' P hP
    have := CoordBound.coordInt D (hI D) S dl hLet Q N B hQ (by linarith) δ t0 p Q' hQ' P hP
    simp only [if_pos hp.out]
    exact this
  · intro δ t0 K _ _ _ _ σ ι P P' zA zA' hs hc hn
    have ne : ∀ (R : Pair D ⊤ δ t0 Q) (z : K), (∃ h T, R.coord h T ≠ 0) → σ z = (R.norm : ℂ) → z ≠ 0 := by
      rintro R z h1 h2 rfl
      have := (RepInv.rep_indep D (hI D) ⊤ δ t0 Q R.crv R.pt0 R R.level_pos).2.2.2.2 h1
      rw [map_zero] at h2
      exact this.ne (by exact_mod_cast h2)
    have val : ∀ (R : Pair D ⊤ δ t0 Q) (z : K), R.Small N B → z ≠ 0 → σ z = (R.norm : ℂ) → ∀ w : Formalism.PairingDivisionLocalBalance.Pl K,
        -(3 * Formalism.PairingDivisionLocalBalance.wt S' (fun p => if p.Prime then expo_vp (fF D) N D.host.d Q B dl p else 0) w) ≤
          (Formalism.DivisionValues.vw w z : ℝ) := by
      intro R z h1 h2 h3 w
      obtain ⟨p, hp, hw⟩ := exists_prime_mem w
      have : Fact p.Prime := ⟨hp⟩
      rw [hE.wt_eq hp w hw, if_pos hp, ← mul_assoc]
      refine GlobalTheory.PadicPlaceBound.neg_mul_vw_le_vw K σ z p w _ h2 hw fun lam => ?_
      rw [h3]
      exact (GlobalTheory.T.definiteThetaPairNorm_padicValuation_bound D (hI D) S dl hLet δ t0 Q R.crv R.pt0 hQ R N B h1 p lam).2
    refine ⟨hE.wt_size.1, hE.wt_size.2, fun i => ?_⟩
    have a1 := ne _ _ (hc i).1 (hn i).1
    have a2 := ne _ _ (hc i).2 (hn i).2
    exact ⟨a1, a2, fun w => ⟨val _ _ (hs i).1 a1 (hn i).1 w, val _ _ (hs i).2 a2 (hn i).2 w⟩⟩

end GlobalTheory.NormSum.DenomBound
end

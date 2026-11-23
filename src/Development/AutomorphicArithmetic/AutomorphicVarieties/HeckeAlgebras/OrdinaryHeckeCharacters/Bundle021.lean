module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CoefficientRepTrivialOnUnramified
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle034
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DecompSigmaOrd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle727
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CoreEig
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle384
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle011
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle089
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle088
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle091
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle037
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsUnramifiedAtTotallyRealOfInertiaLeRestrictionR
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle007
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartAct0
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle006
import Development.AutomorphicArithmetic.AutomorphicVarieties.IntegralityNearIdentity.CharOfScalar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle047
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CLocConj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.WtOfForm
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Hi.coreH :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ) (P : Wt L l n → (H.Gq →* GL (Fin n) (Qbar l)) → Prop), H.Aut ι P →
    ∀ lam0 ∈ H.admitted, H.DenseWt θ lam0 → ∀ (a : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))] [Alg.IsCO c.O (H.TK θ a K)], ∀ (D : W.GDet n (H.TK θ a K) H.Gq) (ψ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* (H.TK θ a K)ˣ), H.IsUniv θ a K (maximalIdeal _) D ψ →
    H.Out θ a K P (maximalIdeal _) D ψ := by
  intro hL L Ω _ _ _ _ _ l _ n c H hA A _ _ _ θ hθ ι P hP _ _ _ a K _ _ D ψ hU
  refine ⟨hU, UpperTheory.V.Hi.coreSep hL L Ω l n c H hA A θ hθ ι P hP a K, fun lam hlam y hy => ?_⟩
  let x : A →ₐ[c.O] Qbar l := y.comp (IsScalarTower.toAlgHom c.O A (H.TK θ a K))
  have hx : y.toRingHom.comp (algebraMap A _) = x.toRingHom := rfl
  rw [hx] at hy ⊢
  obtain ⟨d, ξ, c0, sp, hsp⟩ := UpperTheory.V.Hi.spec L Ω l n c H hA A θ hθ ι x lam hy
  obtain ⟨-, -, -, -, -, hpt, -⟩ :=
    UpperTheory.V.Hi.partAct0 hL L Ω l n c H hA A θ hθ ι P hP x lam d ξ c0 sp hsp hlam a K _ rfl
  obtain ⟨Y, F, e, hY, he, hF0, hF, hop⟩ := hpt y hx
  obtain ⟨hD, hch⟩ := UpperTheory.V.Hi.coreEig hL L Ω l n c H hA A θ hθ ι a K D ψ hU y lam d ξ Y F hF.1 hF0
    fun w j => hop _
  refine ⟨Y.r, Y.cont, Y.ss, hY, hD, fun hg v => ?_⟩
  obtain ⟨ω, hsm, hPS, hinv, hU'⟩ := UpperTheory.V.Hi.goodScalB hL L Ω l n c H hA A θ hθ ι x lam d ξ c0 sp hsp hg Y K e he
    fun h0 => hF0 ((Submodule.mem_bot ℂ).1 (h0 ▸ hF))
  have hO := hch v (ω v) (hsm v) (hinv v) fun j =>
    smul_left_injective ℂ hF0 ((hop (.inr (v, j))).symm.trans ((hU' v j).2 F hF))
  obtain ⟨rc, hrc0⟩ := hL.loc.llc L Ω (H.pl v) (H.Sl v) (H.ovr v)
  have hrc : IsRec (H.ovr v) rc := GlobalTheory.T.rec_of_rec_literal hL.loc.dzc hL.loc.dzi hL.loc.exh hL.loc.multi hL.loc.cos hL.loc.zel
    hL.loc.geo hL.loc.bz L Ω _ _ _ rc hrc0
  obtain ⟨φ⟩ := hPS v
  have hpol := (UpperTheory.V.Hi.psRec hL L Ω n (H.Sl v) (H.pl v) (H.ovr v) (H.art v) (hA.art_spec v) rc hrc (Y.σl v) (ω v)
    (hsm v)).1 (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)
  have hdist : ∀ i j, i ≠ j → ∃ u : Uo ((H.Sl v).adicCompletion L), ω v i u ≠ ω v j u := fun i j hij => by
    obtain ⟨u, hu⟩ := hg.2.2 v i j hij
    refine ⟨u, fun h0 => hu (ι.injective (mul_left_cancel₀ (ω v j u).ne_zero ?_))⟩
    rw [hinv v j u, ← h0, hinv v i u]
  have hdr := Y.atL v (ω v) (hsm v) hdist ⟨φ⟩ rc hrc ((UpperTheory.V.Lev.ssCalc L Ω _ _ (H.ovr v)).1 n _ (fun j => (ω v j).comp (H.art v)) hpol)
  rw [funext hpol] at hdr
  refine UpperTheory.V.Loc.ordFlag hL L Ω l hA.odd ι n (H.Sl v) (hA.Sl_over v) (H.pl v) (H.ovr v) (H.art v) (hA.art_spec v)
    _ (Y.cont.comp (hA.prj_cont.comp continuous_subtype_val)) (htW lam) (fun τ i j hij => ?_) (ω v) _ hO
    (fun i j hij => ?_) hdr
  · have h1 := (lam τ).anti (Fin.rev_le_rev.2 hij.le)
    have h2 : (i : ℕ) < j := hij
    simp only [htW, lowW]
    omega
  · obtain ⟨u, hu⟩ := hg.2.2 v i j hij
    refine ⟨u, fun h0 => hu (ι.injective (mul_left_cancel₀ (ω v j u).ne_zero ?_))⟩
    rw [hinv v j u, ← h0, hinv v i u]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem UpperTheory.V.Hi.partU :
    Af.HypothesesH → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O), TypeFor r ι τ₀ →
    ∀ (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ →
    ∀ σ : Submodule ℂ (UA L n → ℂ), IsAutRepU σ → YOf Q ι τ₀ e ξ σ ≠ ⊥ → ∃ Y : (hset Q τ₀).Part ι lam ξ, Y.Y = YOf Q ι τ₀ e ξ σ ∧ PU r ι lam Y.r ∧ (∀ v : V.frame.Vl, IsCompAlong σ (locU n (s.w v.1)) ((cLoc (s.w v.1)).comp (locU n (s.w v.1)).subtype) (Y.σl v).ρ) ∧ ∀ w, IsSplitAt w → ∀ τ : SmIrr (GLw n w), IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ → Af.LocGlob ι (Y.r.comp V.pr) w τ := by
  intro PH l _ L Ω _ _ _ _ _ _ s n hn V Q c r ι m τ₀ hτ lam d e ξ hb σ hσ hY
  have P := PH.toClassicalTheorems
  have hAx := axU P.litN l L Ω s n hn V Q c m τ₀
  have hund : ∀ {A : ValuationSubring Ω} {w : Plc L}, IsPlaceOver A w → IsPlaceOver A (w.under (𝓞 (Lp L))) :=
    fun hA y => hA (algebraMap (𝓞 (Lp L)) (𝓞 L) y)
  have hwv : ∀ v, (s.w v).under (𝓞 (Lp L)) = v := fun v =>
    HeightOneSpectrum.ext (Ideal.ext fun y => (hund (s.hw v) y).symm.trans (s.hA v y))
  have hl : ∀ w : Plc L, ((l : ℕ) : 𝓞 L) ∈ w.asIdeal ↔ ((l : ℕ) : 𝓞 (Lp L)) ∈ (w.under (𝓞 (Lp L))).asIdeal := fun w => by
    rw [← map_natCast (algebraMap (𝓞 (Lp L)) (𝓞 L))]
    rfl
  have hsp : ∀ w : Plc L, w.under (𝓞 (Lp L)) ∈ V.S' → IsSplitAt w := fun w hw =>
    UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω _ _ (s.hA _) (V.split _ hw) w rfl
  have hspS : ∀ v ∈ s.S, IsSplitAt (s.w v) := fun v hv => hsp _ (by rw [hwv]; exact V.sub hv)
  have hspQ : ∀ q, IsSplitAt (Q.wq q) := fun q => hsp _ (by rw [Q.range]; exact Or.inr ⟨q, rfl⟩)
  have hin : ∀ w : Plc L, ((l : ℕ) : 𝓞 L) ∈ w.asIdeal → w.under (𝓞 (Lp L)) ∈ V.S' := fun w hw =>
    V.sub (Or.inl ((hl w).1 hw))
  have hpr : Function.Surjective V.pr := fun g => by
    obtain ⟨τ, hτ⟩ : ∃ τ, toGS Ω V.S' τ = g.1 := QuotientGroup.mk_surjective g.1
    obtain ⟨σ, rfl⟩ := (V.hη τ).1 (by rw [hτ]; exact g.2)
    exact ⟨σ, Subtype.ext hτ⟩
  have hunr := partUR2Unr l L Ω s n hn V Q c ι m τ₀ lam d e ξ hb σ hσ hY
  have hwt := partUR2Wt l L Ω s n hn V Q c ι m τ₀ lam d e ξ hb σ hσ hY
  have hex : ∀ w : Plc L, IsSplitAt w → ∃ τ : SmIrr (GLw n w),
      IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ ∧
        (IsUnramU σ w → Af.HasFixed τ.ρ (GlobalTheory.LFun.KGL w (n := n))) := fun w hw => by
    obtain ⟨τ, -, h1, h2⟩ := GlobalTheory.DefU.exists_locComp_split L n ⟨σ, hσ⟩ w hw
    refine ⟨τ, h1, fun h => ?_⟩
    obtain ⟨v, hv, h0⟩ := (Submodule.ne_bot_iff _).1 (h2.1 h)
    exact ⟨v, h0, fun u hu => by simpa using hv ⟨u, hu⟩⟩
  choose loc hloc hfix using hex
  obtain ⟨R, HT, hRc, hRs, hRu, hHT, hW, hLG, hpair, hcusp⟩ :=
    Af.galUnitary PH L Ω (UpperTheory.isUnramifiedAt_totallyReal_of_inertia_le_restriction_range L Ω s.unr) l s.odd ι n hn σ hσ
  obtain ⟨ρ, hρc, rfl, hform⟩ := UpperTheory.exists_descent_to_level_group_of_unramified l L Ω s n V c R hRc fun w hw A hA =>
    hRu w (mt (hin w) hw) (hunr w hw) A hA
  have hsat : ∀ w : (hset Q τ₀).Wp, ∃ a : ℕ → ℂ, a 0 = 1 ∧
      (∀ j, ∀ v ∈ fixd (loc w.1 w.2.2).ρ (KO (w.1.adicCompletion L) (Fin n)), sphOp (loc w.1 w.2.2).ρ j v = a j • v) ∧
      ∀ (B : ValuationSubring Ω) (g : G L Ω), IsPlaceOver B w.1 → IsFrob B (normV w.1) g →
        (ρ (V.pr g⁻¹) : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.map ι.toRingHom = heckePol n (normV w.1) a := fun w => by
    obtain ⟨b, hb'⟩ := (Af.satLoc P L n w.1 _).1 (hfix w.1 w.2.2 (hunr _ w.2.1))
    obtain ⟨-, a, h0, h1, h2⟩ := satT L n w.1 _ b hb'
    have hw := mt (hin w.1) w.2.1
    refine ⟨a, h0, h1, fun B g hB hg => ?_⟩
    rw [← h2]
    exact (Af.satFrob P L Ω l ι n _ hRc w.1 hw _ b hb'
      (fun A h rc hrc => (hLG w.1 w.2.2 _ (hloc _ _) A h rc hrc).1 hw) B hB).2 g hg
  choose a ha0 ha1 ha2 using hsat
  refine ⟨{ Y := YOf Q ι τ₀ e ξ σ
            le := inf_le_left
            ne := hY
            σl := fun v => loc (s.w v.1) (hspS _ (Or.inl v.2))
            isoL := fun v => partUR2IsoL l L Ω s n hn V Q c ι m τ₀ lam d e ξ hb σ hσ v _ (hloc _ _)
            σq := fun q => loc (Q.wq q) (hspQ q)
            isoQ := fun q => partUR2IsoQ l L Ω s n hn V Q c ι m τ₀ lam d e ξ hb σ hσ hAx q _ (hloc _ _)
            a := a
            a_zero := ha0
            sph := fun w j => partUR2Sph l L Ω s n hn V Q c ι m τ₀ lam d e ξ hb σ hσ hAx w.1 w.2.1 w.2.2 _ (hloc _ _) j _
              (ha1 w j)
            r := ρ
            cont := hρc
            ss := fun M hM => ?_
            frob := ha2
            atL := fun v => UpperTheory.hodge_tate_weights_of_local_global l L Ω ι n _ _ (s.hw v.1) (ρ.comp V.pr) HT _ lam hHT
              (hLG _ (hspS _ (Or.inl v.2)) _ (hloc _ _)) fun j => hW _ _ (hwt ⟨v, j⟩)
            atQ := fun q B h rc hrc => (hLG _ (hspQ q) _ (hloc _ _) B h rc hrc).1 (hAx.Q_away q) },
    rfl, ⟨?_, fun t ht u => ?_, fun hi => ?_, ?_, ⟨HT, hHT⟩⟩, fun v => hloc _ _, hLG⟩
  · obtain ⟨M', h1, h2⟩ := hRs M fun g => hM (V.pr g)
    refine ⟨M', fun g => ?_, h2⟩
    obtain ⟨g, rfl⟩ := hpr g
    exact h1 g
  · obtain ⟨P', hP'⟩ := hpair s.c s.hc
    exact ⟨P', hform P' hP'⟩
  · have hS : ∀ u : s.St, (u : Plc (Lp L)) ∈ s.S := fun u => Or.inr (Or.inl u.2)
    obtain ⟨rc, hrc⟩ : ∃ rc : IrrGL (k := (s.w u).adicCompletion L) → WD (s.hw u), IsRec (s.hw u) rc := by
      have Z := P.litN.loc
      obtain ⟨rc, hrc⟩ := Z.llc L Ω _ _ (s.hw u)
      exact ⟨rc, GlobalTheory.T.rec_of_rec_literal Z.dzc Z.dzi Z.exh Z.multi Z.cos Z.zel Z.geo Z.bz L Ω _ _ _ rc hrc⟩
    have hT := partUR2Type l L Ω s n hn V Q c ι m τ₀ lam d e ξ hb σ hσ hY _ (hτ t ht)
      (fun u => loc (s.w u) (hspS _ (hS u))) (fun u => hloc _ _) u rc hrc
    have hu : ((l : ℕ) : 𝓞 L) ∉ (s.w u).asIdeal := fun h => s.St_l u u.2 (by simpa only [hwv] using (hl _).1 h)
    obtain ⟨g, hg⟩ := UpperTheory.exists_conj_inertia_diagonal_of_isTypeWD l L Ω ι n _ _ (s.hw u) hu (ρ.comp V.pr)
      (fun i => W.pushCh (algebraMap c.O (Qbar l)) ((t i).comp (V.pr.comp (Ine (F := L) (s.A u)).subtype))) _
      ((hLG _ (hspS _ (hS u)) _ (hloc _ _) _ (s.hw u) rc hrc).1 hu) hT
    refine ⟨g, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hg ⟨x, hx⟩
  · obtain ⟨π, h1, h2, h3, h4⟩ := hcusp ⟨hi.1, fun _ _ _ => Submodule.mem_top, fun M hM hI => hi.2.2 M hM fun g => by
      obtain ⟨g, rfl⟩ := hpr g
      exact hI g⟩
    exact ⟨π, h1, h2, h3, fun v j => h4 _ _ (hwt ⟨v, j⟩)⟩
  · exact ⟨σ, hσ, hLG, hwt, hunr, fun w hw => ⟨_, hloc w hw⟩, loc _ (hspS _ (Or.inr (Or.inr rfl))), hloc _ _,
      partUR2V0 l L Ω s n hn V Q c ι m τ₀ lam d e ξ hb σ hσ hY _ (hloc _ _)⟩
end

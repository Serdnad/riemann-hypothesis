module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle458
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle447
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisConjDefiniteFormsSemilinearEquiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle523
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIntegralOfLine
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle517
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle531
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle534
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPelUnifPull
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle200
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle533
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
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LiePush
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.R3.Rw.OmExt

def mapVVι {K K' : Type} [Field K] [Field K'] (ι : K →+* K') {T : Type} [Fintype T] {n : ℕ} (lam : T → DomWeight n)
    (v : VV K lam) : VV K' lam :=
  ⟨MvPolynomial.map ι v.1, GlobalTheory.Proof.TensorMapDescent.map_mem_VV ι lam _ v.2⟩

theorem exists_smul_eq_enl {D : D7} {V : HSp D} (c : CoefA V) (hc : c.Is) {K' : Type} [Field K'] (ι : D.what₂.LL →+* K')
    (emb' : K' →+* ℂ) (hι : ∀ x, emb' (ι x) = D.what₂.embLL x) (tau : D.what₂.Tau → D.host.E →+* D.what₂.LL)
    (tau' : D.what₂.Tau → D.host.E →+* K') (htau : ∀ τ, emb'.comp (tau' τ) = D.what₂.embLL.comp (tau τ))
    {lam : D.what₂.Tau → DomWeight V.rank}
    (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.W) (h0 : Bridge.CoefMapTie V c.coef c0 (rhoVr tau lam))
    (c' : CoefA V) (hcc : c' = c) (c0' : VV K' lam →ₛₗ[emb'] c'.W)
    (h1 : ∀ γ γE, Bridge.IsRatMat V γ γE → ∀ v, c0' (rhoVr tau' lam γE v) = c'.coef.ρ γ (c0' v)) :
    ∃ μ : ℂ, ∀ (v : VV D.what₂.LL lam) (v' : VV K' lam),
      MvPolynomial.map emb' v'.1 = MvPolynomial.map D.what₂.embLL v.1 → HEq (c0' v') (μ • c0 v) := by
  subst c'
  have hcomp : emb'.comp ι = D.what₂.embLL := RingHom.ext hι
  have hinj : ∀ a b : VV K' lam, MvPolynomial.map emb' a.1 = MvPolynomial.map emb' b.1 → a = b := fun a b h =>
    Subtype.ext (MvPolynomial.map_injective emb' emb'.injective h)
  have hmap : ∀ v : VV D.what₂.LL lam, MvPolynomial.map emb' (mapVVι ι lam v).1 = MvPolynomial.map D.what₂.embLL v.1 := fun v => by
    show MvPolynomial.map emb' (MvPolynomial.map ι v.1) = _
    rw [MvPolynomial.map_map, hcomp]
  have hsm : ∀ (a : D.what₂.LL) (v : VV D.what₂.LL lam), mapVVι ι lam (a • v) = ι a • mapVVι ι lam v := fun a v =>
    Subtype.ext (by
      show MvPolynomial.map ι (a • v.1) = ι a • MvPolynomial.map ι v.1
      rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul])
  let c1 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.W :=
    { toFun := fun v => c0' (mapVVι ι lam v)
      map_add' := fun a b => by
        rw [← map_add (f := _)]
        congr 1
        exact Subtype.ext (map_add _ _ _)
      map_smul' := fun a v => by
        show c0' (mapVVι ι lam (a • v)) = D.what₂.embLL a • c0' (mapVVι ι lam v)
        rw [hsm, map_smulₛₗ, hι] }
  have hrho : ∀ γE v, mapVVι ι lam (rhoVr tau lam γE v) = rhoVr tau' lam γE (mapVVι ι lam v) := fun γE v => by
    refine hinj _ _ ?_
    rw [hmap]
    have e1 := congrArg Subtype.val (GlobalTheory.ConjTwist.mapVV_rhoVr D.what₂.embLL tau lam γE v)
    have e2 := congrArg Subtype.val (GlobalTheory.ConjTwist.mapVV_rhoVr emb' tau' lam γE (mapVVι ι lam v))
    rw [GlobalTheory.CoefModel.mapVV_coe] at e1 e2
    rw [e1, e2]
    have e3 : (fun τ => emb'.comp (tau' τ)) = fun τ => D.what₂.embLL.comp (tau τ) := funext htau
    have e4 : GlobalTheory.CoefModel.mapVV emb' lam (mapVVι ι lam v) = GlobalTheory.CoefModel.mapVV D.what₂.embLL lam v :=
      Subtype.ext (hmap v)
    rw [e3, e4]
  obtain ⟨μ, hμ⟩ := RowCoord.exists_smul_eq c hc h0 c1 fun γ γE hγ v => by
    show c0' (mapVVι ι lam (rhoVr tau lam γE v)) = c.coef.ρ γ (c0' (mapVVι ι lam v))
    rw [hrho]
    exact h1 γ γE hγ _
  refine ⟨μ, fun v v' hv => heq_of_eq ?_⟩
  have : v' = mapVVι ι lam v := hinj _ _ (hv.trans (hmap v).symm)
  subst this
  exact hμ v

end GlobalTheory.Mem.R3.Rw.OmExt
end

noncomputable section
namespace GlobalTheory.Mem.R3.Rw.OmExt

theorem coefA_eq {D : D7} {V : HSp D} (c c' : CoefA V) (hW : HEq c'.W c.W) (hρ : HEq c'.ρ c.ρ) (hn : HEq c'.nW c.nW)
    (hi : HEq c'.iW c.iW) : c' = c := by
  cases c
  cases c'
  dsimp only at hW hρ hn hi
  cases hW
  cases hn
  cases hi
  cases hρ
  rfl



theorem coef_schur : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl}
  (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq f' f → HEq w'.px w.px → z.Std →
  ∀ {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
    (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks)
    (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
    Pins R' (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) cG' → LevOf (w'.st Z') w'.I (usedOf w'.I T' Wt') R'.toLevCh →
    BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr R'.toRealDat → RSideW z Wt' R' →
    ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    ∀ c0L, GlobalTheory.Mem.R3.Rw.OmExt.CoefFam z.R.toRealDat c0L →
    ∀ c0L'', GlobalTheory.Mem.R3.Rw.OmExt.CoefFam R'.toRealDat c0L'' →
    ∃ μ : ℂ, ∀ (v : Formalism.IndefR.FWT.VsV (w.st Z).toD7 i (w.st Z).toD7.what₂.LL) (v' : Formalism.IndefR.FWT.VsV (w'.st Z').toD7 i' (w'.st Z').toD7.what₂.LL),
      HEq (MvPolynomial.map (w'.st Z').toD7.what₂.embLL v'.1) (MvPolynomial.map (w.st Z).toD7.what₂.embLL v.1) → HEq (c0L'' i' v') (μ • c0L i v) := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Wt' z hE hff hpx hstd Ks _ _ _ Xg tr R' cG' hP hL hB hRS i i' hii c0L hc c0L'' hc''
  obtain ⟨gR, c0R, ht⟩ := hc
  obtain ⟨gR', c0R', ht'⟩ := hc''
  have hs := hRS.2.2.2.2.2.2.2.2.2.2.2.2.1 i i' hii
  have hW := hs.1
  have hρ := hs.2.1
  have hnW := hs.2.2.1
  have hiW := hs.2.2.2.1
  have hcI := z.pins.char.base.models.cV i
  have hmapL := ht.mapL i
  have hmapL' := ht'.mapL i'
  have htau := ht.tauL_ok
  have htau' := ht'.tauL_ok
  obtain ⟨hpre, -, -, hR⟩ := hE
  cases B with | mk P => cases B' with | mk P' =>
  dsimp only at hpre
  subst hpre
  obtain rfl : i = i' := Fin.ext hii
  let ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL := (enlEmb hR)
  have hι : ∀ x, (w'.st Z').toD7.what₂.embLL (ι x) = (w.st Z).toD7.what₂.embLL x := (enlEmb_spec hR)
  let c'' : CoefA (Vc (w.st Z).toD7 i) :=
    { W := (R'.cV i).W, nW := (R'.cV i).nW, iW := (R'.cV i).iW, fW := (R'.cV i).fW, ρ := (R'.cV i).ρ }
  have hcc : c'' = z.R.cV i := coefA_eq _ _ hW hρ hnW hiW
  obtain ⟨μ, hμ⟩ := exists_smul_eq_enl (z.R.cV i) hcI ι (w'.st Z').toD7.what₂.embLL hι (labLL (w.st Z).toD7)
    (labLL (w'.st Z').toD7) (fun τ => (htau' τ).trans (htau τ).symm) (c0L i) hmapL c'' hcc (c0L'' i) hmapL'.1
  exact ⟨μ, fun v v' hv => hμ v v' (eq_of_heq hv)⟩

end GlobalTheory.Mem.R3.Rw.OmExt
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.Resize

theorem seeds_uniform_exists : ∀ (K : Ctx) (P : Pre) (f : GlobalTheory.Mem.Top.Fr P) (F : IntermediateField ℚ ℂ),
    ∃ (S : Finset ℕ) (S₂ : Finset ℂ), (∀ z ∈ S₂, IsAlgebraic ℚ z) ∧ ∀ px : PreX P,
      (∃ F₀, SeedW K P f F F₀ px Set.univ ⊤) →
        ∃ F₀, SeedW K P f F F₀ px (S : Set ℕ) (IntermediateField.adjoin ℚ (S₂ : Set ℂ)) := by
  classical
  intro K P f F
  have key : ∀ c : (Fin 2 → 𝓞 P.host.E) × (P.Word → 𝓞 P.host.E), ∃ (S : Finset ℕ) (S₂ : Finset ℂ),
      (∀ z ∈ S₂, IsAlgebraic ℚ z) ∧ ∀ Y : PreX P, (Y.piG, Y.piT) = c → (∃ F₀, SeedW K P f F F₀ Y Set.univ ⊤) →
        ∃ F₀, SeedW K P f F F₀ Y (S : Set ℕ) (IntermediateField.adjoin ℚ (S₂ : Set ℂ)) := by
    intro c
    by_cases hc : ∃ (X : PreX P) (F₀ : IntermediateField ℚ ℂ), (X.piG, X.piT) = c ∧ SeedW K P f F F₀ X Set.univ ⊤
    · obtain ⟨X, F₀, hX, hs⟩ := hc
      obtain ⟨S, S₂, hS₂, hb⟩ := seedW_bound hs
      refine ⟨S, S₂, hS₂, fun Y hY _ => ⟨F₀, ?_⟩⟩
      have e := hX.trans hY.symm
      exact seedW hb (congrArg Prod.fst e) (congrArg Prod.snd e)
    · exact ⟨∅, ∅, by simp, fun Y hY ⟨F₀, hs⟩ => absurd ⟨Y, F₀, hY, hs⟩ hc⟩
  choose S S₂ hS₂ hS using key
  have hfin := finite_gens P
  refine ⟨hfin.toFinset.biUnion S, hfin.toFinset.biUnion S₂, ?_, fun Y hs => ?_⟩
  · intro z hz
    obtain ⟨c, -, hz⟩ := Finset.mem_biUnion.1 hz
    exact hS₂ c z hz
  · have hm : (Y.piG, Y.piT) ∈ hfin.toFinset := hfin.mem_toFinset.2 ⟨Y, rfl⟩
    obtain ⟨F₀, h⟩ := hS _ Y rfl hs
    refine ⟨F₀, h.mono ?_ (IntermediateField.adjoin.mono _ _ _ ?_)⟩
    · intro p hp
      exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨_, hm, hp⟩)
    · intro p hp
      exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨_, hm, hp⟩)

end GlobalTheory.Mem.R3.Rw.Resize

end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.TorRef

namespace GlobalTheory.TorRef

theorem admissibleBase_of_completeNormalLocalCharZero {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (h : IsCN R) :
    AdmBase R (maximalIdeal R) :=
  ⟨h.1, inferInstance, h.2.1, h.2.2.1⟩

theorem pullSt : PullSt := by
  intro E _ _ _ H R R' _ _ _ _ _ _ φ t P hR hR' hφ hloc _
  obtain ⟨h1, -, h3, h4, h5, -⟩ := GlobalTheory.allSixLaws
  have aR := admissibleBase_of_completeNormalLocalCharZero hR
  have aR' := admissibleBase_of_completeNormalLocalCharZero hR'
  have : CharZero R' := hR'.2.2.2
  have hI : (maximalIdeal R).map φ ≤ maximalIdeal R' :=
    Ideal.map_le_iff_le_comap.2 fun a ha => (map_mem_nonunits_iff φ a).2 ha
  obtain ⟨t', m₀, P', hD, -, -, -, -, xl, -⟩ :=
    GlobalTheory.ArcDataDescent.exists_pelUnif_pull h3.cubePull h1.polBaseChange h4.unifBaseChange h5 aR aR' t P φ hφ hI
  let e : P'.D.toPre.X ≃ₗ[𝓞 E] P.D.toPre.X := { hD.xe with map_smul' := xl }
  exact ⟨t', m₀, P', e, GlobalTheory.FlatTors.torsionIso_holds E H R' _ aR' t' P',
    fun y r hr => GlobalTheory.PelCoordPull.psiCoord_pull hD y r hr⟩

end GlobalTheory.TorRef
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
open MonoidalCategory CartesianMonoidalCategory MonObj

noncomputable section

namespace GlobalTheory.ArcLieCoord

attribute [local instance] Over.cartesianMonoidalCategory

theorem zeroPt_sc {S : Type} [CommRing S] (c : S) : GlobalTheory.PowLie.zeroPt S ≫ GlobalTheory.PowLie.sc c = GlobalTheory.PowLie.zeroPt S := by
  ext1
  simp only [Over.comp_left, GlobalTheory.PowLie.zeroPt, GlobalTheory.PowLie.sc, Over.homMk_left]
  rw [← spMap_comp]
  congr 1
  refine RingHom.ext fun r => ?_
  simp [epsScaleR]

theorem isTangent_prod {S : Type} [CommRing S] {G' : Over (Sp S)} [GrpObj G'] [IsCommMonObj G'] {n : ℕ}
    (v : Fin n → (epsR S ⟶ G')) (hv : ∀ k, IsTangent (v k)) (c : Fin n → S) :
    IsTangent (∏ k, GlobalTheory.PowLie.sc (c k) ≫ v k) := by
  rw [GlobalTheory.PowLie.isTangent_iff]
  have e := map_prod (ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom (G := G') (GlobalTheory.PowLie.zeroPt S)) (fun k => GlobalTheory.PowLie.sc (c k) ≫ v k) Finset.univ
  refine (e.trans ?_)
  refine (Finset.prod_eq_one fun k _ => ?_).trans rfl
  change GlobalTheory.PowLie.zeroPt S ≫ GlobalTheory.PowLie.sc (c k) ≫ v k = 1
  rw [← Category.assoc, zeroPt_sc, (GlobalTheory.PowLie.isTangent_iff _).1 (hv k)]
  rfl

theorem sep : ∀ {S : Type} [CommRing S] {X : Scheme.{0}} {x : Sp S ⟶ X} {G : Over X} {G' : Over (Sp S)} [GrpObj G] [GrpObj G'] [IsCommMonObj G'] {φ : G'.left ⟶ G.left}, IsGrpPullback G' G x φ → ∀ {n : ℕ} (v : Fin n → (epsR S ⟶ G')), IsLieBasis v → ∀ {V : G.left.Opens}, IsAffineOpen V → ⊤ ≤ ((η[G']).left ≫ φ) ⁻¹ᵁ V → ∀ (b : Fin n → S), (∀ f : Γ(G.left, V), ∑ k, b k * (valR ((v k).left ≫ φ) V f).snd = 0) → b = 0 := by
  intro S _ X x G G' _ _ _ φ h n v hv V hA hV b hb
  set w₀ : epsR S ⟶ G' := ∏ k, GlobalTheory.PowLie.sc (b k) ≫ v k with hw₀
  set w₁ : epsR S ⟶ G' := ∏ k, GlobalTheory.PowLie.sc ((0 : Fin n → S) k) ≫ v k with hw₁
  have c₀ : IsLieComb b v w₀ := (GlobalTheory.PowLie.isLieComb_iff_prod b v w₀).2 rfl
  have c₁ : IsLieComb 0 v w₁ := (GlobalTheory.PowLie.isLieComb_iff_prod 0 v w₁).2 rfl
  have t₀ : IsTangent w₀ := isTangent_prod v hv.1 b
  have t₁ : IsTangent w₁ := isTangent_prod v hv.1 0
  have l₀ := tan_le h w₀ t₀ V hV
  have l₁ := tan_le h w₁ t₁ V hV
  have fst_eq : ∀ (w : epsR S ⟶ G'), IsTangent w → ∀ f : Γ(G.left, V),
      (valR (w.left ≫ φ) V f).fst = valR ((η[G']).left ≫ φ) V f := by
    intro w hw f
    have e1 := GlobalTheory.HolHom.valR_spMap (TrivSqZeroExt.fstHom S S S).toRingHom (w.left ≫ φ) V (tan_le h w hw V hV) f
    have e2 : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w.left ≫ φ = (η[G']).left ≫ φ := by
      rw [← Category.assoc]
      exact congrArg (· ≫ φ) hw
    rw [e2] at e1
    rw [e1]
    rfl
  have e : w₀.left ≫ φ = w₁.left ≫ φ := by
    refine GlobalTheory.HolHom.point_ext hA l₀ l₁ fun f => ?_
    refine TrivSqZeroExt.ext ((fst_eq w₀ t₀ f).trans (fst_eq w₁ t₁ f).symm) ?_
    rw [comb_snd h v hv.1 b w₀ c₀ V hV f, comb_snd h v hv.1 0 w₁ c₁ V hV f, hb f]
    simp
  have hw : w₀ = w₁ := ReciprocityTheory.ChartRestriction.G.Chart.inj_over h e
  exact (hv.2 w₀ t₀).unique c₀ (hw ▸ c₁)

end GlobalTheory.ArcLieCoord
end
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.GoodMetric.FibreAntisymm
open GlobalTheory.GoodMetric

theorem rename_chernRoots (ι : Type) [Fintype ι] (m : ι → ℕ) (w : ∀ τ, Equiv.Perm (Fin (m τ)))
    (R : MvPolynomial (ι × ℕ) ℝ) :
    rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) (chernRoots m R) = chernRoots m R := by
  have h : (rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m))).comp (chernRoots m) = chernRoots m := by
    apply MvPolynomial.algHom_ext
    intro x
    simp only [AlgHom.comp_apply, chernRoots, aeval_X, rename_rename]
    have e : ((fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) ∘ Sigma.mk x.1) = Sigma.mk x.1 ∘ (w x.1) := by
      funext i; rfl
    rw [e, ← rename_rename, rename_esymm]
  exact AlgHom.congr_fun h R

theorem antisymm_chernRoots_mul (ι : Type) [Fintype ι] (m : ι → ℕ) (R : MvPolynomial (ι × ℕ) ℝ)
    (Q : MvPolynomial (Root m) ℝ) : antisymm (chernRoots m R * Q) = chernRoots m R * antisymm Q := by
  unfold antisymm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [map_mul, rename_chernRoots, mul_smul_comm]

theorem prod_Ioi_rev {R : Type*} [CommRing R] {N : ℕ} (v : Fin N → R) :
    (∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (v (Fin.rev i) - v (Fin.rev j))) = ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (v j - v i) := by
  have h : ∀ f : Fin N → Fin N → R, (∏ i : Fin N, ∏ j ∈ Finset.Ioi i, f i j) =
      ∏ i : Fin N, ∏ j : Fin N, if i < j then f i j else 1 := by
    intro f
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Finset.prod_filter]
    congr 1
    ext j; simp
  rw [h, h, ← Fintype.prod_prod_type' (f := fun i j => if i < j then v (Fin.rev i) - v (Fin.rev j) else 1),
    ← Fintype.prod_prod_type' (f := fun i j => if i < j then v j - v i else 1)]
  refine Fintype.prod_equiv ((Equiv.prodComm _ _).trans (Fin.revPerm.prodCongr Fin.revPerm)) _ _ fun p => ?_
  simp [Fin.rev_lt_rev]

theorem sum_sign_prod_neg_pow {R : Type*} [CommRing R] {N : ℕ} (v : Fin N → R) :
    (∑ σ : Equiv.Perm (Fin N), (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : R) * ∏ i : Fin N, (-v (σ i)) ^ (N - 1 - (i : ℕ))) =
      ∏ j : Fin N, ∏ i ∈ Finset.Iio j, (v j - v i) := by
  let M : Matrix (Fin N) (Fin N) R := Matrix.of fun j i => (-v j) ^ (N - 1 - (i : ℕ))
  have h1 : M.det = ∑ σ : Equiv.Perm (Fin N), (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : R) * ∏ i : Fin N, (-v (σ i)) ^ (N - 1 - (i : ℕ)) := by
    rw [Matrix.det_apply']
    rfl
  have h2 : M.submatrix Fin.revPerm Fin.revPerm = Matrix.vandermonde (fun j => -v (Fin.rev j)) := by
    ext j i
    simp only [M, Matrix.submatrix_apply, Matrix.of_apply, Matrix.vandermonde_apply, Fin.revPerm_apply, Fin.val_rev]
    congr 1
    omega
  rw [← h1, ← Matrix.det_submatrix_equiv_self Fin.revPerm, h2, Matrix.det_vandermonde,
    GlobalTheory.GoodMetric.RootDiscrPerm.prod_Iio_eq_det, Matrix.det_vandermonde, ← prod_Ioi_rev]
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  simp only [Fin.rev_rev]
  ring

theorem antisymm_fibrePoint (ι : Type) [Fintype ι] (m : ι → ℕ) : antisymm (fibrePoint m) = rootDiscr m := by
  have hw : ∀ w : ∀ τ, Equiv.Perm (Fin (m τ)),
      ((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) • rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) (fibrePoint m) =
        ∏ τ, ((((Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) : MvPolynomial (Root m) ℝ) *
          ∏ i : Fin (m τ), (-(X (⟨τ, w τ i⟩ : Root m) : MvPolynomial (Root m) ℝ)) ^ (m τ - 1 - (i : ℕ))) := by
    intro w
    unfold fibrePoint
    rw [map_prod, Fintype.prod_sigma, zsmul_eq_mul, Units.coe_prod, Int.cast_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [map_pow, map_neg, rename_X]
  unfold antisymm
  rw [Finset.sum_congr rfl fun w _ => hw w]
  rw [← Fintype.prod_sum (fun τ (σ : Equiv.Perm (Fin (m τ))) => ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : MvPolynomial (Root m) ℝ) *
          ∏ i : Fin (m τ), (-(X (⟨τ, σ i⟩ : Root m) : MvPolynomial (Root m) ℝ)) ^ (m τ - 1 - (i : ℕ))))]
  unfold rootDiscr
  refine Finset.prod_congr rfl fun τ _ => ?_
  exact sum_sign_prod_neg_pow (fun i : Fin (m τ) => (X (⟨τ, i⟩ : Root m) : MvPolynomial (Root m) ℝ))

end GlobalTheory.GoodMetric.FibreAntisymm

namespace GlobalTheory.GoodMetric

theorem antisymm_chernRoots_mul_fibrePoint : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (R : MvPolynomial (ι × ℕ) ℝ),
    GlobalTheory.GoodMetric.antisymm (GlobalTheory.GoodMetric.chernRoots m R * GlobalTheory.GoodMetric.fibrePoint m) =
      GlobalTheory.GoodMetric.chernRoots m R * GlobalTheory.GoodMetric.rootDiscr m := by
  intro ι _ m R
  rw [FibreAntisymm.antisymm_chernRoots_mul, FibreAntisymm.antisymm_fibrePoint]

end GlobalTheory.GoodMetric
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

theorem _root_.GlobalTheory.T.flagRelativeTangentTopChern_dvd_of_differences_dvd : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (P : MvPolynomial (Root m) ℝ), (∀ (τ : ι) (i j : Fin (m τ)), i < j → (X ⟨τ, j⟩ - X ⟨τ, i⟩ : MvPolynomial (Root m) ℝ) ∣ P) → rootDiscr m ∣ P := by
  first | exact @GlobalTheory.GoodMetric.DiscrDvd.rootDiscr_dvd | exact GlobalTheory.GoodMetric.DiscrDvd.rootDiscr_dvd | (intros; apply GlobalTheory.GoodMetric.DiscrDvd.rootDiscr_dvd <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

theorem _root_.GlobalTheory.T.flagRelativeTangentTopChern_rename_block_perm : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (w : ∀ τ, Equiv.Perm (Fin (m τ))), rename (Equiv.sigmaCongrRight w) (rootDiscr m) = ((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) • rootDiscr m := by
  first | exact @GlobalTheory.GoodMetric.rename_sigmaCongrRight_rootDiscr | exact GlobalTheory.GoodMetric.rename_sigmaCongrRight_rootDiscr | (intros; apply GlobalTheory.GoodMetric.rename_sigmaCongrRight_rootDiscr <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

theorem _root_.GlobalTheory.T.weylAntisymmetrization_rename_block_perm_sign : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (Q : MvPolynomial (Root m) ℝ) (w : ∀ τ, Equiv.Perm (Fin (m τ))), rename (Equiv.sigmaCongrRight w) (antisymm Q) = ((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) • antisymm Q := by
  first | exact @GlobalTheory.GoodMetric.antisymm_rename_sigmaCongrRight | exact GlobalTheory.GoodMetric.antisymm_rename_sigmaCongrRight | (intros; apply GlobalTheory.GoodMetric.antisymm_rename_sigmaCongrRight <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

theorem _root_.GlobalTheory.T.weylAntisymmetrization_rename_swap_neg : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (m : ι → ℕ) (Q : MvPolynomial (Root m) ℝ) (τ : ι) (i j : Fin (m τ)), i ≠ j → rename (Equiv.swap (⟨τ, i⟩ : Root m) ⟨τ, j⟩) (antisymm Q) = -antisymm Q := by
  first | exact @GlobalTheory.AntisymmSwap.rename_swap_antisymm | exact GlobalTheory.AntisymmSwap.rename_swap_antisymm | (intros; apply GlobalTheory.AntisymmSwap.rename_swap_antisymm <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries


theorem _root_.GlobalTheory.T.exists_rescale_uniformisation_rigidification : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) (u : HolUnif A L g) (rig : LB.Gen (L.pull (eSec A))), L.IsLB → rig.IsGen → ∃ (u' : HolUnif A L g) (lam : ℂ), lam ≠ 0 ∧ u'.ex = u.ex ∧ u'.Λ = u.Λ ∧ u'.IsRig rig ∧ ∀ i z, u'.fr i z = lam * u.fr i z := by
  first | exact @GlobalTheory.RigRescale.exists_rescale_rig | exact GlobalTheory.RigRescale.exists_rescale_rig | (intros; apply GlobalTheory.RigRescale.exists_rescale_rig <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries


theorem _root_.GlobalTheory.T.keySection_eq_const_mul_thetaFunction_fibre : ∀ (x : KeyIn ℂ) (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (y : Sp ℂ ⟶ S) (Φ : x.P.A.left ⟶ G.left) (g : ℕ) (u : HolUnif x.P.A x.P.L g) (w : LB.Iso (L.pull Φ) x.P.L) (θ : (Fin g → ℂ) → ℂ) (fr : L.ι → (Fin g → ℂ) → ℂ) (s : (L.pull (pullback.fst G.hom y)).Sec), L.IsLB → IsPullback Φ x.P.A.hom G.hom y → w.IsGen → (∃ z, θ z ≠ 0) → (∀ j z, ⊤ ≤ ((u.ex z).left ≫ Φ) ⁻¹ᵁ L.U j → fr j z ≠ 0) → (∀ k j z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (x.P.L.U k ⊓ (L.pull Φ).U j) → u.fr k z = valAt' (u.ex z).left (x.P.L.U k ⊓ (L.pull Φ).U j) (w.s (k, j)).val * fr (j PUnit.unit) z) → (∀ j z (p : Sp ℂ ⟶ pullback G.hom y), p ≫ pullback.fst _ _ = (u.ex z).left ≫ Φ → p ≫ pullback.snd _ _ = 𝟙 _ → ⊤ ≤ ((u.ex z).left ≫ Φ) ⁻¹ᵁ L.U j → valAt' p ((L.pull (pullback.fst G.hom y)).U (fun _ => j)) (s.f (fun _ => j)) = θ z * fr j z) → ∃ c₀ : ℂ, u.IsFn x.th (fun z => c₀ * θ z) := by
  first | exact @GlobalTheory.FibreKeyTheta.th_isFn_const_mul | exact GlobalTheory.FibreKeyTheta.th_isFn_const_mul | (intros; apply GlobalTheory.FibreKeyTheta.th_isFn_const_mul <;> assumption)
end

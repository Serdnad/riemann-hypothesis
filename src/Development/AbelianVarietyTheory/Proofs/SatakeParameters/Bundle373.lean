module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle014
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle018
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle024
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle025
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle027
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle371
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle276
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle159
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle205
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle176
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle246
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle365
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle360
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle355
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle028
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle020
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle372
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle342
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle354
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle165
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle218
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle277
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle357
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle327
import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.Bundle001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle364
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThetaLocalEquivalence.Bundle001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle359
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle225
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle341
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle303
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.Bundle007
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
import Formalism.LocalToGlobal.InertKernelTheory.SubBSplit

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.trueKernelJets_mul_detCharacters_mem_coefficientField : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ColIn.JetsIn I → ∀ (u : B.Word) (a : I.ι) (i : ℕ), i < B.R.m → ∀ (c : (I.stp u a i).Cl) (c' : (I.stp u a (i + 1)).Cl) (e : DVar B.fields.Tau (B.R.N i) (B.R.N (i + 1)) →₀ ℕ), (∀ τ, (monoDeg e τ : ℤ) = nuDeg B u i τ) → ∃ k : B.LL, B.embLL k = (I.rho u a i c.1 ((I.stp u a i).rep c) * I.rho' u a i c'.1 ((I.stp u a (i + 1)).rep c')) * jetC I.J.cD (I.th u a i c.1 c'.1 ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c')) e := by
  first | exact @GlobalTheory.Mem.Col2.TC.rho_jet_mem | exact GlobalTheory.Mem.Col2.TC.rho_jet_mem | (intros; apply GlobalTheory.Mem.Col2.TC.rho_jet_mem <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3.Back

theorem exists_level_vec_in_parts : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → ∀ s, A3.fam3.Ok3 s → GoodGeneric A3.A.X F.P0 F.ψ0⁻¹ → R.toRealDat.LUnif → (R.toCx3 F).PartsW false → ∀ j c, R.Wc' j c ≠ ⊥ → ∃ w ∈ R.Wc' j c, w ≠ 0 ∧ w ∈ ⨆ p, R.Wp3 j p := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hCW hEx hSch s hOk hGG hLU hParts j c h0
  obtain ⟨w, hw, hw0, hws⟩ := GlobalTheory.T.exists_baseLevel_vector_in_goodAlgebraicForms_span R F hCW hEx hSch s hOk hGG hLU j c h0
  exact ⟨w, hw, hw0, GlobalTheory.T.mem_iSup_type_parts_of_good_base_forms R F hParts j w hws⟩

theorem blockProd_ne_zero {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
    (B : BlockDat K G Pl0) (P : B.Pl) : B.blockProd P ≠ 0 := by
  unfold BlockDat.blockProd
  rw [ne_eq, List.prod_eq_zero_iff]
  simp only [List.mem_map, not_exists, not_and]
  intro ν _ h
  unfold Formalism.L2.Col.blockPoly at h
  rw [Finset.prod_eq_zero_iff] at h
  obtain ⟨c, _, hc⟩ := h
  have := congrArg (fun q => _root_.AddMonoidAlgebra.coeff (M := ℕ) q 0) hc
  simp at this

theorem eig_in_sum {H : Type} [AddCommGroup H] [Module ℂ H] [FiniteDimensional ℂ H] {Q J K : Type} (ok : Q → Prop)
    (h : Q → J → Module.End ℂ H) (ev : K → Q → J → ℂ) (V : K → Submodule ℂ H) (S : K → Prop) (k0 : K)
    (hc : ∀ P P', ok P → ok P' → ∀ c c', Commute (h P c) (h P' c'))
    (hev : ∀ k P, ok P → ∀ cc, ∀ x ∈ V k, h P cc x = ev k P cc • x)
    (w : H) (hw : w ∈ V k0) (hw0 : w ≠ 0) (hwS : w ∈ ⨆ (k : K) (_ : S k), V k) :
    ∃ k, S k ∧ ∀ P, ok P → ∀ cc, ev k P cc = ev k0 P cc := by
  classical
  let op : {P // ok P} × J → Module.End ℂ H := fun i => h i.1.1 i.2
  have hpc : Formalism.L2.Col.PairComm op := fun i i' => hc _ _ i.1.2 i'.1.2 _ _
  let χ : K → {P // ok P} × J → ℂ := fun k i => ev k i.1.1 i.2
  have hV : ∀ k, V k ≤ Formalism.L2.Col.eigAt op (χ k) := fun k x hx =>
    Formalism.L2.Col.mem_eigAt_of_forall_apply fun i => hev k i.1.1 i.1.2 i.2 x hx
  by_contra hne
  push_neg at hne
  have h1 : (⨆ (k : K) (_ : S k), V k) ≤ Formalism.L2.Col.eigSum op (fun x => x ≠ χ k0) := by
    refine iSup₂_le fun k hk => (hV k).trans (Formalism.L2.Col.eigAt_le_eigSum ?_)
    intro he
    obtain ⟨P, hP, cc, hcc⟩ := hne k hk
    exact hcc (congrFun he (⟨P, hP⟩, cc))
  have h2 : V k0 ≤ Formalism.L2.Col.eigSum op (fun x => x = χ k0) :=
    (hV k0).trans (Formalism.L2.Col.eigAt_le_eigSum rfl)
  have hd := Formalism.L2.Col.disjoint_eigSum (op := op) hpc (C := fun x => x = χ k0) (C' := fun x => x ≠ χ k0)
    (fun x h h' => h' h)
  exact hw0 ((Submodule.disjoint_def.1 hd) w (h2 hw) (h1 hwS))

theorem types_eq {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} (hSep : A3.fam3.TypesSep3) (j : Fin D.R.m)
    (p p' : A3.fam3.base3.Ix) (y : (A3.liftI j A3.A.μ0).OpIx → ℂ)
    (hp : cxSys D.what₂.embLL ((A3.liftI j A3.A.μ0).HasRes3 (A3.fam3.tr3 j p.1)) y)
    (hp' : cxSys D.what₂.embLL ((A3.liftI j A3.A.μ0).HasRes3 (A3.fam3.tr3 j p'.1)) y) : p = p' := by
  obtain ⟨x, hx, rfl⟩ := hp
  obtain ⟨x', hx', hxx⟩ := hp'
  have hxe : x = x' := funext fun i => D.what₂.embLL.injective (congrFun hxx i)
  subst hxe
  by_contra hne
  have hne' : p.1 ≠ p'.1 := fun h => hne (Subtype.ext h)
  rcases hSep p.1 p.2 p'.1 p'.2 hne' j with ⟨P, hP⟩ | ⟨k, hk⟩
  · apply hP
    have h1 := hx.1 P
    have h2 := hx'.1 P
    rw [h1] at h2
    exact mul_right_cancel₀ (blockProd_ne_zero _ P) h2
  · exact hk ((hx.2 k).symm.trans (hx'.2 k))

theorem wc_le_wp_of_passage : HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → InertJunk A3 → ∀ s, A3.fam3.Ok3 s → GoodGeneric A3.A.X F.P0 F.ψ0⁻¹ → R.toRealDat.LUnif → R.PGUnit F → R.PGEquiv F → R.PLevW F → R.PThmA → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → R.TrISem F A3.trI → (R.toCx3 F).PartsW false → A3.fam3.TypesSep3 → ∀ j pl cV cW, LiftDict R j A3.A.μ0 pl cV cW → ∀ (p : A3.fam3.base3.Ix) c, cxSys D.what₂.embLL ((A3.liftI j A3.A.μ0).HasRes3 (A3.fam3.tr3 j p.1)) (labW j pl cW c) → R.Wc' j c ≤ R.Wp3 j p := by
  intro hHowe D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hLI hCW hEx hSch hJunk s hOk hGG hLU hPGU hPGE hPLW hA hPos hB hTr hParts hSep j pl cV cW hLD p c hsys
  obtain ⟨hcoreF, hSF, -, -, -, hWeq, -⟩ := GlobalTheory.T.heckeCharacterisation_places_of_weakCharacterisation R F hCW
  have hcore := hcoreF hEx
  obtain ⟨h, -, hNorm, -, hsum, -, hev, hchar⟩ :=
    GlobalTheory.T.sphericalOperators_forms_on_rank_space_normal R.toRealDat F.lv2 hcore hSch hOk.ok2.irr R.SF hSF j
  have hidem := (eH_laws R.toRealDat F.lv2 hcore hOk.ok2.irr j).1
  by_cases h0 : R.Wc' j c = ⊥
  · rw [h0]; exact bot_le
  obtain ⟨w, hwc, hw0, hwp⟩ := exists_level_vec_in_parts R F hCW hEx hSch s hOk hGG hLU hParts j c h0
  have hwp' : w ∈ ⨆ (c' : Pl D.host.E → List ℤ → ℂ) (_ : ∃ p', R.Carries p' c'), Wcc R.toRealDat R.SF j c' := by
    have hle : (⨆ p, R.Wp3 j p) ≤
        ⨆ (c' : Pl D.host.E → List ℤ → ℂ) (_ : ∃ p', R.Carries p' c'), Wcc R.toRealDat R.SF j c' := by
      refine iSup_le fun p' => iSup₂_le fun c' hc' => ?_
      rw [hWeq]
      exact le_iSup₂_of_le (f := fun c' (_ : ∃ p', R.Carries p' c') => Wcc R.toRealDat R.SF j c') c' ⟨p', hc'⟩ le_rfl
    exact hle hwp
  rw [hWeq] at hwc
  obtain ⟨c', ⟨p', hcar⟩, hag⟩ := eig_in_sum (Good R.toRealDat A3.A.μ0) h
    (fun c P cc => evC (Wc D j) P (c P) cc) (Wcc R.toRealDat R.SF j) (fun c' => ∃ p', R.Carries p' c') c hNorm.1
    (fun k P hP cc x hx => hev k P hP cc x hx) w hwc hw0 hwp'
  have hsub : Wcc R.toRealDat R.SF j c ≤ Wcc R.toRealDat R.SF j c' := by
    intro x hx
    refine hchar c' x ?_ ?_
    · have hr : x ∈ LinearMap.range (eH R.toRealDat j) := hsum ▸ (le_iSup (Wcc R.toRealDat R.SF j) c hx)
      obtain ⟨y, rfl⟩ := hr
      rw [← Module.End.mul_apply, hidem]
    · intro P d hP hd
      rw [hev c P hP _ x hx, ← hag P hP]
      simp [evC, hd]
  have hne : R.Wc' j c' ≠ ⊥ := by
    rw [hWeq]
    intro hb
    exact hw0 ((Submodule.eq_bot_iff _).1 hb w (hsub hwc))
  have hfwd := GlobalTheory.T.carriedPart_eigensystem_passage_of_type hHowe R F hLI hCW hEx hSch hJunk s hOk hGG hLU hPGU hPGE hPLW hA hPos hB hTr j pl cV cW hLD p' c' hcar hne
  have hlab : labW j pl cW c' = labW j pl cW c := funext fun i => hag (pl i) (hLD.good i) (cW i)
  rw [hlab] at hfwd
  have hpp : p' = p := types_eq hSep j p' p _ hfwd hsys
  subst hpp
  rw [hWeq]
  refine hsub.trans ?_
  rw [← hWeq]
  exact le_iSup₂_of_le (f := fun c (_ : R.Carries p' c) => R.Wc' j c) c' hcar le_rfl

end GlobalTheory.Hk3.Back
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.AtG

theorem _root_.GlobalTheory.T.periodValuationBound_typePrimePlace_of_chainAgreement : JetSplitAmb → ∀ (D : D7) (L : SizeData₂ D) (EX : ErrX D) (Dx : DivX D) (μ : D.what₂.Tup), TiesAt D EX Dx μ → ∀ i : Fin 2, GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.SizeAt D i → ∀ w, LiftErrorLocal.Over D i w → ∀ u : D.what₂.Word, D.what₂.places.resChar w ≠ (D.mem u).A.T → GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.BoundAt L EX 1 i w u μ := by
  first | exact @GlobalTheory.ColPeriodTies.boundAt_of_ties | exact GlobalTheory.ColPeriodTies.boundAt_of_ties | (intros; apply GlobalTheory.ColPeriodTies.boundAt_of_ties <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TwV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Hat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

theorem levU_mulVec_mem_hatL (S : StepLevel F E σ J T f bad) (g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hg : g ∈ S.U)
    (z : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F) (hz : z ∈ Formalism.L2.Herm.hatL (F := F) S.Lb) :
    (g : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ z ∈ Formalism.L2.Herm.hatL (F := F) S.Lb := by
  refine Formalism.L2.Geo.Def.PN.latS_of_loc S.Lb S.Lb_span _ fun v => ?_
  have h1 := Formalism.L2.Geo.Def.PN.prV_latS S.Lb v hz
  have h2 : bc (prV (E := E) v) g ∈ levelVL σ J v S.Lb := S.Uloc_lev v (((S.U_eq g).1 hg).2 v)
  have h3 := (h2.2 _).1 h1
  have e : (fun i => prV (E := E) v (((g : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ z) i)) =
      ((bc (prV (E := E) v) g : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ
        fun i => prV (E := E) v (z i) := by
    funext i
    exact RingHom.map_mulVec (prV (E := E) v) (g : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) z i
  rw [e]
  exact h3

theorem hatStab_of_levU (S : StepLevel F E σ J T f bad) (κ : S.U) : HatStab S.Lb κ.1 := by
  intro z
  constructor
  · intro hz
    have := levU_mulVec_mem_hatL S κ.1 κ.2 _ hz
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec] at this
  · intro hz
    exact levU_mulVec_mem_hatL S κ.1⁻¹ (S.U.inv_mem κ.2) z hz

end Hat

theorem isPtAd_mul_lev : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x' : UA D i hi) p (κ : ((St i hi).K β).lev.U), x'.1 = x.1 * κ.1 → IsPtAd A a i hi β x p → ∃ p', IsPtAd A a i hi β x' p') := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP H i hi β x x' p κ hx hp
  obtain ⟨p', hN, hf, hfr⟩ := GlobalTheory.T.chartPoint_frames_move_integralRightTranslate A dtU a hP H i p
    (fun P => ratA D.host.F (A.crd i hi) * x.1 * ratA D.host.F (A.fb i hi β P))
    (fun P => (ratA D.host.F (A.fb i hi β P))⁻¹ * κ.1 * ratA D.host.F (A.fb i hi β P))
    (GlobalTheory.T.chartLevel_baseFrame_congr_one_at_badPrime A dtU a hP H i hi β x p κ hp) hp.frame
  refine ⟨p', ⟨?_, ?_, ?_⟩⟩
  · rw [hN, hp.lat]
    unfold latCo
    rw [hx, latAd_stab _ _ _ (hatStab_of_levU _ κ)]
  · intro P
    have e : ratA D.host.F (A.crd i hi) * x'.1 * ratA D.host.F (A.fb i hi β P) =
        ratA D.host.F (A.crd i hi) * x.1 * ratA D.host.F (A.fb i hi β P) *
          ((ratA D.host.F (A.fb i hi β P))⁻¹ * κ.1 * ratA D.host.F (A.fb i hi β P)) := by
      rw [hx]; simp only [mul_assoc, mul_inv_cancel_left]
    rw [e]
    exact hfr P
  · intro P v h hv
    have e : ratA D.host.F (A.crd i hi) * x'.1 = ratA D.host.F (A.crd i hi) * x.1 * κ.1 := by
      rw [hx, mul_assoc]
    have h1 := GlobalTheory.T.functionalCondition_invariant_rightLevelTranslate t.seam _ P v h (iotaOf A i hi β P v h) _ κ _ (hp.fnl P v h hv)
    rw [e]
    intro w hw z hz
    have h2 := h1 w (by rw [← hN]; exact hw) z hz
    exact (congrFun (congrFun hf P) w).trans h2

end GlobalTheory.TwV

end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.Xc



theorem site_move : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    S.Pos → S.Pair → S.Move) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS hPos hPair
  obtain ⟨hmm, -, hN, -⟩ := GlobalTheory.TwV.DelB.sysS_ranks S
  intro j hj c L La' γ hL hLa'
  rw [hmm] at hj
  have hr := hN j
  obtain ⟨g, κ, hM⟩ : ∃ g κ, MoveBy std J j hj.le c L γ g κ := by
    cases j with
    | zero => exact GlobalTheory.T.stepZero_latticeTuple_move_by_rational_isometry S hD hS c L γ hL
    | succ i => exact GlobalTheory.T.kernelSite_move_latticeTuple_at_succStep S hD hS i hj.le c L γ hL
  have hU := ((GlobalTheory.TwV.Xc.eMat_unitary_det _ _ (fun _ => rfl) _ _ hr _ _ (J.pins.crd_orth j hj.le)).2 g hM.1).1
  obtain ⟨hcq, hxi⟩ := GlobalTheory.T.movedDatum_movedLatticeTuple S hD hS j hj c L γ g κ hr hL hM La'
  refine ⟨eMat hr (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj.le) g, _, hU, ?_,
    GlobalTheory.T.kernelLattice_movedLatticeTuple S hD hS j hj c L γ g κ hr hL hM, hcq, hxi, GlobalTheory.T.latticeTupleMove_scalar_power_of_p S hD hS hPos hPair j hj c L γ g κ hr hL hM La' hLa'⟩
  intro v
  rw [GlobalTheory.T.latticeTuple_frameMatrices_eq_of_same_component S hD hS j c (((sysS H X std).Lv.lev j c).smul γ L) L]
  exact hM.2.2.1 hr v

end GlobalTheory.TwV.Xc
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaSeries_scalar_bounded_of_pos_pair : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → S.Pair → S.Scal) := by
  first | exact @GlobalTheory.TwV.Xc.scal_of_pos_pair | exact GlobalTheory.TwV.Xc.scal_of_pos_pair | (intros; apply GlobalTheory.TwV.Xc.scal_of_pos_pair <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.latticeTupleKernel_eq_smul_pullback_classKernel : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → ∀ (d : Dec J std), ∀ j < D.R.m, d.PullAt S j) := by
  first | exact @GlobalTheory.TwV.DelB.pullAt_of_dict | exact GlobalTheory.TwV.DelB.pullAt_of_dict | (intros; apply GlobalTheory.TwV.DelB.pullAt_of_dict <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.kernelLattice_detIdeal_character_eq_const_mul_det : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j ≤ D.R.m), ∃ c0 : ℂ, ∀ La : (sysS H X std).Lt j, ((sysS H X std).Pj j).IsLatTup La.2 → IsSDLat D.host.E _ ((J.fd std).kerN j La) → t.χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) ((J.fd std).kerN j La)) = c0 * chiI J ((J.fd std).dt j La)) := by
  first | exact @GlobalTheory.TwV.Xc.chi_detId_kerN_eq | exact GlobalTheory.TwV.Xc.chi_detId_kerN_eq | (intros; apply GlobalTheory.TwV.Xc.chi_detId_kerN_eq <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.two_units_at_place_uniformizing_idele : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => KIn t → S.Pos → ∀ v π, IsUnifAt J v π → ∀ j < D.R.m, (sysS H X std).Lv.comp j → (sysS H X std).Lv.comp (j + 1) → ∃ a b : (sysS H X std).G.Kf, (sysS H X std).vEqK a 0 ∧ (sysS H X std).vEqK b 0 ∧ S.E.iK a = ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ (-((sysS H X std).vm v (j + 1))) * TaylorLogMetric.lamC S.lam (S.muT (j + 1) π * chiI J π ^ (((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ))) ∧ S.E.iK b = ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ ((sysS H X std).vm v (j + 1)) * TaylorLogMetric.lamC S.lam ((S.muT (j + 1) π)⁻¹ * chiI J π ^ (-((((j + 1) * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ))))) := by
  first | exact @GlobalTheory.TwV.Xc.two_units | exact GlobalTheory.TwV.Xc.two_units | (intros; apply GlobalTheory.TwV.Xc.two_units <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem source_scalar_const : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (d : Dec J std) j (hj : j < D.R.m), Nonempty (Lv.comp (j + 1)) → ∀ La : (sysS H X std).Lt j, dPow (mM d j hj.le La).1 (fun τ => -(wT (sysS H X std) D (hT.gat_pos u w hg) j τ)) * sPt d j hj.le La * d.uS S j La = kS J j hj.le La.1) := by
  unfold GlobalTheory.TwV.AllSites
  intro D _ hT _ _ _ _ _ ex u μ w hg Lv I H X _ std t J S d j hj hne La
  have hW := GlobalTheory.T.kernelSite_modelStageWeights_eq_chainWeights S j hj hne
  have hfr := (GlobalTheory.T.changedFrame_rational_unitary S d j hj.le (rkS _ _ hW.rk) La).2.2
  obtain ⟨e, he, hmu⟩ := GlobalTheory.T.stepCharacter_det_rationalIsometry S j hj
  have hgd := (GlobalTheory.T.det_rational_unitary_orthonormalChange_matrices S j hj.le).2 _ (d.mem j hj.le La)
  obtain ⟨q, hq⟩ := Formalism.L2.Ker.even_rankN D.R (j + 1)
  have hs : ∀ τ, (D.chTw u μ).sSharp j τ = e τ - ((D.R.N (j + 1) / 2 : ℕ) : ℤ) := by
    intro τ
    have h1 := (D.chTw u μ).sSharp_eq j hj τ
    rw [D.hcW_e u τ, ← he τ] at h1
    have h2 : D.R.N (j + 1) / 2 = q := by omega
    rw [h2]
    have h3 : ((D.R.N (j + 1) : ℕ) : ℚ) = (q : ℚ) + q := by exact_mod_cast hq
    unfold sExp' at h1
    rw [h3] at h1
    have h4 : ((D.chTw u μ).sSharp j τ : ℚ) = ((e τ - (q : ℤ) : ℤ) : ℚ) := by push_cast; rw [h1]; ring
    exact_mod_cast h4
  have hχ : d.chi j hj.le La ≠ 0 := by unfold Dec.chi; exact Units.ne_zero _
  have hcD : ((D.chiD ((t.O u μ).dt j (clsAt X H j La.1 La.2)) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  unfold dPow sPt Dec.uS kS dPow
  rw [dite_eq_left hj.le, hmu j hj.le _ (d.mem j hj.le La), hgd.1]
  simp only []
  set n : ℤ := ((D.R.N (j + 1) / 2 : ℕ) : ℤ) with hn
  set c : ℤ := cTw D j with hc
  rw [show ∀ (A χ C B Mu P : ℂ), A * (χ * C ^ c * B) * (χ⁻¹ * Mu⁻¹ * P * C ^ (-c)) = A * B * Mu⁻¹ * P * (χ * χ⁻¹) * (C ^ c * C ^ (-c)) from
    fun _ _ _ _ _ _ => by ring]
  rw [mul_inv_cancel₀ hχ, ← zpow_add₀ hcD, add_neg_cancel, zpow_zero, mul_one, mul_one]
  rw [← Finset.prod_zpow, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hm : (embT D τ) (mM d j hj.le La).1.det ≠ 0 := by rw [map_ne_zero]; exact (Matrix.isUnits_det_units _).ne_zero
  have hgn : (embT D τ) (d.gam j hj.le La).1.det ≠ 0 := by rw [map_ne_zero]; exact (Matrix.isUnits_det_units _).ne_zero
  have hb := congrArg (embT D τ) hfr
  rw [map_mul] at hb
  rw [← hb, hW.sh τ, hs τ]
  show (embT D τ) _ ^ _ * _ * ((embT D τ) _ ^ _)⁻¹ * ((embT D τ) (_ * _)) ^ _ = _
  rw [map_mul]
  generalize (embT D τ) (mM d j hj.le La).1.det = m at hm ⊢
  generalize (embT D τ) (d.gam j hj.le La).1.det = g at hgn ⊢
  generalize (embT D τ) (gMat J j hj.le 1).det = G
  generalize e τ = ee
  simp only [mul_zpow, zpow_neg, zpow_sub₀ hm, zpow_sub₀ hgn, zpow_add₀ hm, zpow_add₀ hgn]
  field_simp
  ring

end GlobalTheory.TwV.DelA
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.DelA

theorem actC_actC_inv {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (i : ℕ) {n : ℕ}
    (h : (X.Pj i).m + 1 = n) (M : GL (Fin n) D.host.E) (V : XR (X.Pj i) ℂ) :
    actC X D pos i h M (actC X D pos i h M⁻¹ V) = V := by
  let z : Frames (fun _ : D.what₂.Tau => (1 : Matrix (Fin n) (Fin n) ℂ)) := ⟨fun _ => 1, fun _ => by simp⟩
  let f : Fr1 D n := ⟨fun τ => (atR D (M * (1 : GL (Fin n) D.host.E)⁻¹) τ : Matrix (Fin n) (Fin n) ℂ) * z.1 τ, fun τ => by
    show IsUnit ((atR D (M * (1 : GL (Fin n) D.host.E)⁻¹) τ : Matrix (Fin n) (Fin n) ℂ) * 1).det
    rw [mul_one]
    exact (Matrix.GeneralLinearGroup.det (atR D (M * (1 : GL (Fin n) D.host.E)⁻¹) τ)).isUnit⟩
  exact (evC_crdB_actC X D pos i h (fun _ => 1) 1 M V z f (fun _ => rfl)).2

theorem embT_det_ne_zero (D : D7) {n : ℕ} (M : GL (Fin n) D.host.E) (τ : D.what₂.Tau) : embT D τ M.1.det ≠ 0 := by
  have h0 : M.1.det ≠ 0 := by
    have := (Matrix.GeneralLinearGroup.det M).ne_zero
    simpa using this
  exact (map_ne_zero _).2 h0

theorem transported_frame_realAt : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; ∀ (d : Dec J std) j (hj : j + 1 ≤ D.R.m) (h : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1)) (La' : (sysS H X std).Lt (j + 1)) (φ : (D.chTw u μ).cls (j + 1) → (D.chTw u μ).Y (j + 1) → ℂ) (P : MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ), P ∈ WtPol ℂ (extNu (D.R.N (j + 1)) (Formalism.L2.Ker.nuT D u j)) → (∀ y, φ (clsAt X H (j + 1) La'.1 La'.2) y = (∏ τ, (D.chTw u μ).de (j + 1) y τ ^ (D.chTw u μ).sDiv j τ)⁻¹ * frPoly (t.O u μ) (j + 1) P y) → ∃ V : XR ((sysS H X std).Pj (j + 1)) ℂ, RealAt d (j + 1) hj h La' φ V ∧ MvPolynomial.map ι V = scT d S ι j La'.1 La'.2 • GlobalTheory.FrameB.tauV ℂ_[D.what₂.places.resChar w] d.fd2 (ltC S.g S.hLT) j La' (phi0 (sysS H X std) D (hT.gat_pos u w hg) ι j P)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hPos ι hι
  intro d j hj h La' φ P hP hφ
  have hWt := GlobalTheory.T.kernelSite_modelStageWeights_eq_chainWeights S j (by omega) ⟨La'.1⟩
  obtain ⟨-, -, -, hle, -⟩ := size_first_last_rows (sysS H X std) D (hT.gat_pos u w hg) j hWt.rk (nuT D u j) hWt.nu
  have hR : Realises (sysS H X std) D (hT.gat_pos u w hg) (j + 1) h (wT (sysS H X std) D (hT.gat_pos u w hg) j) P
      (phiC (sysS H X std) D (hT.gat_pos u w hg) (j + 1) h (wT (sysS H X std) D (hT.gat_pos u w hg) j) P) := by
    obtain ⟨R0, hR0⟩ := GlobalTheory.T.frame_polynomials_weight_realised_next_level (sysS H X std) D (hT.gat_pos u w hg) j h _ hle P hP
    exact selOf_mem (relPhi (sysS H X std) D (hT.gat_pos u w hg) (j + 1) h _) P ⟨(P, R0), hR0, rfl⟩
  refine ⟨sPt d (j + 1) hj La' • actC (sysS H X std) D (hT.gat_pos u w hg) (j + 1) h (mM d (j + 1) hj La')⁻¹
    (phiC (sysS H X std) D (hT.gat_pos u w hg) (j + 1) h (wT (sysS H X std) D (hT.gat_pos u w hg) j) P), ?_, ?_⟩
  · rw [GlobalTheory.T.kernelSite_valuesAtPoint_iff_realisesInStdCoords S d (j + 1) hj h La' (fun τ => (D.chTw u μ).sDiv j τ) φ P hφ, map_smul, actC_actC_inv]
    have hw : (fun τ => (D.chTw u μ).sDiv j τ - cTw D (j + 1)) = wT (sysS H X std) D (hT.gat_pos u w hg) j :=
      funext fun τ => (hWt.dv τ).symm
    rw [hw]
    intro f
    have h1 := hR f
    simp only [GL3Theta.evFr, map_smul, Pi.smul_apply, smul_eq_mul, MvPolynomial.smul_eval] at h1 ⊢
    rw [h1]
    ring
  · letI := wittFractionAlgebraCp (D.what₂.places.resChar w)
    letI := algKfC S.E.toCEmb
    have hPT := (posTie_at S hPos ι hι).1
    have hFr := GlobalTheory.T.changedFrame_rational_unitary S d (j + 1) hj h La'
    have hτ := GlobalTheory.T.targetFrameMap_eq_complexBlockAction_scalar (sysS H X std) D (hT.gat_pos u w hg) ℂ_[D.what₂.places.resChar w] ι (J.rho std) hPT d.fd2
      (ltC S.g S.hLT) (ltC_ne_zero _ _) j hWt.rk La' (mM d (j + 1) hj La') hFr.1 hFr.2.1 (nuT D u j) hWt.nu P hP
    have h45 := GlobalTheory.T.targetStep_scalar_eq S d j hj La'
    have hprod : dPow (mM d (j + 1) hj La').1 (fun τ => -(wT (sysS H X std) D (hT.gat_pos u w hg) j τ)) *
        ∏ τ, embT D τ (mM d (j + 1) hj La').1.det ^ wT (sysS H X std) D (hT.gat_pos u w hg) j τ = 1 := by
      unfold dPow
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun τ _ => ?_
      rw [zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ (embT_det_ne_zero D _ τ))]
    have hc := ltC_ne_zero S.g S.hLT
    have key : ι (sPt d (j + 1) hj La') = scT d S ι j La'.1 La'.2 * (ltC S.g S.hLT ^ (∑ τ, szT (sysS H X std) D (hT.gat_pos u w hg) j τ) *
        ι (∏ τ, embT D τ (mM d (j + 1) hj La').1.det ^ wT (sysS H X std) D (hT.gat_pos u w hg) j τ)) := by
      rw [scT, dite_eq_left hj]
      have e1 : sPt d (j + 1) hj La' = d.uT S j (La'.1, La'.2) * kT J j hj La'.1 *
          ∏ τ, embT D τ (mM d (j + 1) hj La').1.det ^ wT (sysS H X std) D (hT.gat_pos u w hg) j τ := by
        rw [← h45, mul_comm (dPow _ _) (sPt _ _ _ _), mul_assoc, hprod, mul_one]
      rw [e1, map_mul, zpow_neg]
      field_simp
    rw [hτ, smul_smul, ← key, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]

end GlobalTheory.TwV.DelA

end
end

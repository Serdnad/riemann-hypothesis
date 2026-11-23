module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfTrivAxes
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle294
public import Formalism.LocalToGlobal.Columns.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle208
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle903
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle143
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle142
public import Formalism.LocalToGlobal.Divisibility.DivisionHeightBoundStatement
public import Formalism.LocalToGlobal.Columns.ToHLatLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1831
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Counterexamples.TwistSurvey.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1262
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1804
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1494
public import Formalism.SatakeDualWeyl.Statement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1085
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1174
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Mathlib.Topology.Sheaves.Presheaf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle001
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle005

@[expose] public section

section

open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

theorem _root_.GlobalTheory.T.del_dbar_comm_pullback_of_smooth_del_dbar : ∀ (M M' : Type) [TopologicalSpace M] [TopologicalSpace M'] (n n' : ℕ) (A : HolAtlas M n) (A' : HolAtlas M' n')
    (f : M' → M) (α : A.Fld), A.IsHolo A' f → A.IsForm α → A.IsForm (A.del α) → A.IsForm (A.dbar α) →
    A'.del (A.pullback A' f α) = A.pullback A' f (A.del α) ∧ A'.dbar (A.pullback A' f α) = A.pullback A' f (A.dbar α) := by
  first | exact @GlobalTheory.CxForm.HolAtlas.del_dbar_comm_pullback | exact GlobalTheory.CxForm.HolAtlas.del_dbar_comm_pullback | (intros; apply GlobalTheory.CxForm.HolAtlas.del_dbar_comm_pullback <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.DualCon
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.AbDual

theorem memKL_lift_one_of_triv_ev : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G], IsAbelianScheme G → ∀ P : LB (G ⊗ G).left, P.IsLB → (∃ t : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∀ (T : Over (Sp R)) (a : T ⟶ G), (∃ t : (P.pull (lift (snd G T ≫ a) (fst G T)).left).Gen, t.IsGen) → GlobalTheory.MemKL (G ⊗ G) P (lift a (1 : T ⟶ G)) := by
  intro R _ _ G _ hG P hP h0l h0r _ T a ha
  have hadd : IsAdditive P := CubeNoeth.isAdditive_of_triv_axes hG hG hP h0l h0r
  have hD : (Out.translDiff (G ⊗ G) P (lift a (1 : T ⟶ G))).IsLB := LB.isLB_linComb hP _ _
  have hz : cls _ hD = 0 := by
    have e₁ := pull_translDiff hP (lift a (1 : T ⟶ G)) hD (fst T (G ⊗ G)) (snd T (G ⊗ G))
    rw [lift_fst_snd, Over.id_left, pull_id] at e₁
    have em : (fst T (G ⊗ G) ≫ lift a (1 : T ⟶ G)) * snd T (G ⊗ G) =
        lift ((fst T (G ⊗ G) ≫ a) * (snd T (G ⊗ G) ≫ fst G G)) (snd T (G ⊗ G) ≫ snd G G) := by
      ext <;> simp [MonObj.mul_comp]
    have eu : snd T (G ⊗ G) = lift (snd T (G ⊗ G) ≫ fst G G) (snd T (G ⊗ G) ≫ snd G G) := by
      ext <;> simp
    have k₁ : CechPic.pull ((fst T (G ⊗ G) ≫ lift a (1 : T ⟶ G)) * snd T (G ⊗ G)).left (cls P hP) =
        evc hP ((fst T (G ⊗ G) ≫ a) * (snd T (G ⊗ G) ≫ fst G G)) (snd T (G ⊗ G) ≫ snd G G) := by
      rw [em]; rfl
    have k₂ : CechPic.pull (snd T (G ⊗ G)).left (cls P hP) =
        evc hP (snd T (G ⊗ G) ≫ fst G G) (snd T (G ⊗ G) ≫ snd G G) := by
      rw [evc, ← eu]
    have k₃ : evc hP (fst T (G ⊗ G) ≫ a) (snd T (G ⊗ G) ≫ snd G G) = 0 := by
      have e := congrArg (CechPic.pull (lift (snd T (G ⊗ G) ≫ snd G G) (fst T (G ⊗ G))).left)
        ((triv_ev_iff hP _ _).1 ha)
      rwa [pull_evc, map_zero, lift_snd_assoc, lift_fst] at e
    rw [e₁, k₁, k₂, (isAdditive_iff hP).1 hadd, add_sub_cancel_right, k₃]
  intro p
  refine ⟨⊤, trivial, (cls_eq_zero_iff (pull_isLB hD _)).1 ?_⟩
  rw [cls_pull hD, hz, map_zero]

end GlobalTheory.AbDual
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.DualCon
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.AbDual

theorem memKL_diag_of_triv_ev_of_symm : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G], IsAbelianScheme G → ∀ P : LB (G ⊗ G).left, P.IsLB → (∃ t : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∀ (T : Over (Sp R)) (a : T ⟶ G), (∃ t : (P.pull (lift (snd G T ≫ a) (fst G T)).left).Gen, t.IsGen) → GlobalTheory.MemKL G (P.pull (lift (𝟙 G) (𝟙 G)).left) a := by
  intro R _ _ G _ hA P hP h0l h0r hsym T a ha
  have hs : (swap P).IsLB := pull_isLB hP _
  have hadd := (isAdditive_iff hP).1 (CubeNoeth.isAdditive_of_triv_axes hA hA hP h0l h0r)
  have hadd' := (isAdditive_iff hs).1 (CubeNoeth.isAdditive_swap_of_triv_axes hA hA hP h0l h0r)
  have hadd2 : ∀ (Y : Over (Sp R)) (u v w : Y ⟶ G), evc hP u (v * w) = evc hP u v + evc hP u w := by
    intro Y u v w
    rw [← evc_swap hP hs, ← evc_swap hP hs, ← evc_swap hP hs]
    exact hadd' Y v w u
  have hc : cls P hP = cls (swap P) hs := (cls_eq_iff hP hs).2 hsym
  have hsymm : ∀ (Y : Over (Sp R)) (u v : Y ⟶ G), evc hP u v = evc hP v u := by
    intro Y u v
    rw [← evc_swap hP hs u v]
    simp only [evc, hc]
  have hL : (P.pull (lift (𝟙 G) (𝟙 G)).left).IsLB := pull_isLB hP _
  have hcL : ∀ (Y : Over (Sp R)) (u : Y ⟶ G), CechPic.pull u.left (cls _ hL) = evc hP u u := by
    intro Y u
    rw [cls_ev hP, pull_evc, Category.comp_id]
  have hx0 : evc hP (fst T G ≫ a) (snd T G) = 0 := by
    have e := congrArg (CechPic.pull (lift (snd T G) (fst T G)).left) ((triv_ev_iff hP _ _).1 ha)
    rwa [pull_evc, map_zero, lift_snd_assoc, lift_fst] at e
  have hD : (Out.translDiff G _ a).IsLB := LB.isLB_linComb hL _ _
  intro p
  obtain ⟨V, hV, hc'⟩ := exists_pull_eq_zero (evc hP a a) p
  refine ⟨V, hV, (cls_eq_zero_iff (pull_isLB hD _)).1 ?_⟩
  have e₁ := pull_translDiff hL a hD (fst T G) (snd T G)
  rw [lift_fst_snd, Over.id_left, pull_id, hcL, hcL] at e₁
  have e₂ : cls _ hD = CechPic.pull (fst T G).left (evc hP a a) := by
    rw [e₁, pull_evc, hadd, hadd2, hadd2, hsymm _ (snd T G) (fst T G ≫ a), hx0]
    abel
  rw [cls_pull hD, e₂, ← pull_comp]
  exact pull_eq_zero_of_mem V (((fst T G).left ⁻¹ᵁ V).ι ≫ (fst T G).left) (fun z ↦ z.2) hc'

end GlobalTheory.AbDual
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbDual

theorem memKL_of_triv_ev_left : ∀ (K : Type) [Field K] [IsAlgClosed K] (A B : Over (Sp K)) [GrpObj A] [GrpObj B]
    (P : LB (A ⊗ B).left) (L : LB A.left), IsAbelianScheme A → IsAbelianScheme B → IsDual A B P → L.IsLB →
    ∀ (T : Over (Sp K)) (x : T ⟶ A), Triv (ev P (fst T B ≫ x) (snd T B)) → GlobalTheory.MemKL A L x := by
  intro K _ _ A B _ _ P L hA _ hD hL T x hx
  haveI := hA.comm
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  have e : ∀ (Y : Over (Sp K)) (a b : Y ⟶ A), evc hP a b = lam (cls L hL) a b := fun Y a b ↦ by
    rw [evc, show cls _ hP = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hP, pull_lam, lift_fst,
      lift_snd]
  have hadd := GlobalTheory.CubeNoeth.isAdditive_of_triv_axes hA hA hP
    (by rw [triv_ev_iff hP, e, lam_one_left]) (by rw [triv_ev_iff hP, e, lam_one_right])
  obtain ⟨φ, hφ, -⟩ := hD.univ A (abelian₂ A L) hP hadd
  have hc : cls _ hP = evc hD.isLB (fst A A) (snd A A ≫ φ) :=
    (cls_eq_iff hP (pull_isLB hD.isLB _)).2 hφ
  have hx0 : lam (cls L hL) (fst T A ≫ x) (snd T A) = 0 := by
    have e₁ := congrArg (CechPic.pull (lift (fst T A) (snd T A ≫ φ)).left) ((triv_ev_iff hD.isLB _ _).1 hx)
    rw [pull_evc, map_zero, lift_fst_assoc, lift_snd] at e₁
    rw [← e, evc, hc, pull_evc, lift_fst, lift_snd_assoc]
    exact e₁
  have hD' : (Out.translDiff A L x).IsLB := LB.isLB_linComb hL _ _
  intro p
  obtain ⟨V, hV, hc'⟩ := exists_pull_eq_zero
    (CechPic.pull x.left (cls L hL) - CechPic.pull (1 : T ⟶ A).left (cls L hL)) p
  refine ⟨V, hV, (cls_eq_zero_iff (pull_isLB hD' _)).1 ?_⟩
  have e₁ := pull_translDiff hL x hD' (fst T A) (snd T A)
  rw [lift_fst_snd, Over.id_left, pull_id] at e₁
  have e₂ : cls _ hD' = CechPic.pull (fst T A).left
      (CechPic.pull x.left (cls L hL) - CechPic.pull (1 : T ⟶ A).left (cls L hL)) := by
    rw [e₁, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, MonObj.comp_one,
      ← sub_eq_zero, ← hx0, lam]
    abel
  rw [cls_pull hD', e₂, ← pull_comp]
  exact pull_eq_zero_of_mem V (((fst T A).left ⁻¹ᵁ V).ι ≫ (fst T A).left) (fun z ↦ z.2) hc'

end GlobalTheory.AbDual
end

section

open Formalism.MainNotions.S

theorem _root_.GlobalTheory.T.unitary_irreducible_is_admissible : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H] (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) π → IsIrredOn (UJset ε) π → GlobalTheory.RealInd.IsIrrAdm ε π := by
  first | exact @GlobalTheory.IrrAdm.isIrrAdm_of_irred | exact GlobalTheory.IrrAdm.isIrrAdm_of_irred | (intros; apply GlobalTheory.IrrAdm.isIrrAdm_of_irred <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open MeasureTheory

namespace GlobalTheory.MultPetersson

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem integrableOn_star_mul (μ : Measure (GA D V)) (𝓕 C : Set (GA D V)) (hμ : μ.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) (hC : IsCompact C)
    (hcov : ∀ h : GA D V, ∃ γ ∈ GQ V, ∃ c ∈ C, h = γ * c)
    {f f' : GA D V → ℂ} (hf : Continuous f) (hf' : Continuous f')
    (hl : ∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) (hl' : ∀ γ ∈ GQ V, ∀ g, f' (γ * g) = f' g) :
    IntegrableOn (fun g => star (f g) * f' g) 𝓕 μ :=
  GlobalTheory.CocompactIntegrable.integrableOn_fundamentalDomain V μ 𝓕 C hμ h𝓕 hC hcov _
    ((continuous_star.comp hf).mul hf') (fun γ hγ g => by simp only [hl γ hγ, hl' γ hγ])

variable (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) {ι : Type} [Fintype ι] (M : DSModel V S) (w : ι → M.Vec)

end GlobalTheory.MultPetersson

namespace GlobalTheory.MultPetersson

open MeasureTheory

end GlobalTheory.MultPetersson
end
end

section

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Matrix
open scoped ComplexOrder

namespace GlobalTheory

theorem change_of_level_classSum : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (W : Formalism.L2.Col.Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (P : LevFam X.E X.K R.r Pr.vGs) (hX : X.Ok) (v : InfinitePlace X.K) (F' : (mtildeKGSD W Ch sel mu).EqFun), F'.1 ∈ (mtildeGSD W Ch sel mu P).EqFun → (mtildeKGSD W Ch sel mu).ipAt (mtildeKOk W Ch sel mu hX) v F'.1 F'.1 = (Nat.card P.grp : ℂ) * (mtildeGSD W Ch sel mu P).ipAt (mtildeOk W Ch sel mu hX P) v F'.1 F'.1 := by
  intro X Pr R W Ch sel S mu P hX v F' hF
  obtain ⟨ι, hinj, hact, hidx⟩ := GlobalTheory.T.rowLevel_principal_firstBlock_index_eq_card W Ch sel mu P
  have hK := mtildeKOk W Ch sel mu hX
  have hP := mtildeOk W Ch sel mu hX P
  have hf : ∀ (g : (mtildeGSD W Ch sel mu P).G) (d : (mtildeGSD W Ch sel mu P).D),
      (mtildeGSD W Ch sel mu P).pairAt v (F'.1 (g • d)) (F'.1 (g • d)) =
      (mtildeGSD W Ch sel mu P).pairAt v (F'.1 d) (F'.1 d) := by
    intro g d
    rw [hF g d]
    exact GlobalTheory.PeriodOnStep.pairAt_rho v _ hP (GlobalTheory.PeriodOnStep.row_act_rat W Ch sel mu P hX) g _
  have hfi : ι.range.FiniteIndex := ⟨by rw [hidx]; exact Nat.card_pos.ne'⟩
  have key := @GlobalTheory.T.orbit_mass_formula_finiteIndex_subgroup (mtildeGSD W Ch sel mu P).G (mtildeKGSD W Ch sel mu).G (mtildeGSD W Ch sel mu P).D _ _ _ _ ι hinj hact hfi
    hP.fin_stab (mtildeOk W Ch sel mu hX P).fintypeCl (mtildeKOk W Ch sel mu hX).fintypeCl
    (fun d => (mtildeGSD W Ch sel mu P).pairAt v (F'.1 d) (F'.1 d)) hf
  rw [hidx] at key
  unfold GSD.ipAt
  refine Eq.trans ?_ (key.trans ?_)
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [@Nat.card_eq_fintype_card _ ((mtildeKOk W Ch sel mu hX).fintypeStab _)]
    rfl
  · congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [@Nat.card_eq_fintype_card _ ((mtildeOk W Ch sel mu hX P).fintypeStab _)]
    rfl

end GlobalTheory
end

section

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

noncomputable section

namespace GlobalTheory.ColFirstIso

section Generic

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S S' : GSD K}

def clEquiv (eG : S'.G ≃* S.G) (eD : S'.D ≃ S.D) (hs : ∀ g d, eD (g • d) = eG g • eD d) : S'.Cl ≃ S.Cl :=
  Quotient.congr eD fun a b => by
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨eG g, (hs g b).symm⟩
    · rintro ⟨g, hg⟩
      refine ⟨eG.symm g, eD.injective ?_⟩
      have hg' : g • eD b = eD a := hg
      show eD (eG.symm g • b) = eD a
      rw [hs, MulEquiv.apply_symm_apply, hg']

theorem clEquiv_cls (eG : S'.G ≃* S.G) (eD : S'.D ≃ S.D) (hs : ∀ g d, eD (g • d) = eG g • eD d) (d : S'.D) :
    clEquiv eG eD hs (S'.cls d) = S.cls (eD d) := rfl

theorem card_stab (eG : S'.G ≃* S.G) (eD : S'.D ≃ S.D) (hs : ∀ g d, eD (g • d) = eG g • eD d) (d : S'.D) :
    Nat.card (MulAction.stabilizer S'.G d) = Nat.card (MulAction.stabilizer S.G (eD d)) := by
  refine Nat.card_congr (eG.toEquiv.subtypeEquiv fun g => ?_)
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  show _ ↔ eG g • eD d = eD d
  rw [← hs, eD.injective.eq_iff]

theorem ipAt_transport (R : S.Rat) (h : S.Ok) (h' : S'.Ok) (eG : S'.G ≃* S.G) (eD : S'.D ≃ S.D)
    (hs : ∀ g d, eD (g • d) = eG g • eD d) (v : InfinitePlace K) (φ : S.EqFun) (φ' : S'.D → S'.V)
    (hp : ∀ d, S'.pairAt v (φ' d) (φ' d) = S.pairAt v ((φ : S.D → S.V) (eD d)) ((φ : S.D → S.V) (eD d))) :
    S'.ipAt h' v φ' φ' = S.ipAt h v φ φ := by
  let e := clEquiv eG eD hs
  let s : S.Sec :=
    { rep := fun c => eD (S'.outSec.rep (e.symm c))
      spec := fun c => by
        rw [← clEquiv_cls eG eD hs, S'.outSec.spec]
        exact e.apply_symm_apply c }
  rw [R.ipAt_indep h s v φ φ]
  let _ := h.fintypeCl
  let _ := h'.fintypeCl
  unfold GSD.ipAt
  refine Fintype.sum_equiv e _ _ fun c => ?_
  have h1 : s.rep (e c) = eD (S'.outSec.rep c) := by
    show eD (S'.outSec.rep (e.symm (e c))) = _
    rw [e.symm_apply_apply]
  rw [h1, S'.wt_eq h' S'.outSec c, card_stab eG eD hs, hp]

end Generic

section Frames

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

def decoEquiv (hQ : Q = ∅) : DecoF X.E n ST SG Q ≃ DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG) where
  toFun := DecoF.deco
  invFun d := ⟨(d, fun _ => 1), fun P => absurd P.2 (by simp [hQ])⟩
  left_inv p := Subtype.ext (Prod.ext rfl (funext fun P => absurd P.2 (by simp [hQ])))
  right_inv _ := rfl

def grpEquiv (hQ : Q = ∅) (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) : FrmG Λ Θ ≃* FormG Λ where
  toFun g := (g.1, g.2.1)
  invFun g := (g.1, g.2, 1)
  left_inv g := Prod.ext rfl (Prod.ext rfl (Subtype.ext (funext fun P => absurd P.2 (by simp [hQ]))))
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem ipAt_frm (hQ : Q = ∅) (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ Λ' : LevFam X.E X.K n SG) (hΛ : Λ' = Λ)
    (Θ : LevQFam X.E X.K n Q) (R : (formGSD C Λ).Rat) (h : (formGSD C Λ).Ok)
    (h' : (frmGSD (C.pull (DecoF.deco (Q := Q))) Λ' Θ).Ok) (v : InfinitePlace X.K) (φ : (formGSD C Λ).EqFun) :
    (frmGSD (C.pull (DecoF.deco (Q := Q))) Λ' Θ).ipAt h' v (fun p => (φ : _ → C.V) (DecoF.deco p))
      (fun p => (φ : _ → C.V) (DecoF.deco p)) = (formGSD C Λ).ipAt h v φ φ := by
  subst hΛ
  exact ipAt_transport R h h' (grpEquiv hQ Λ' Θ) (decoEquiv hQ) (fun _ _ => rfl) v φ _ fun _ => rfl

end Frames

theorem qe_one {X : Fields} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {Sg : Set ℕ} :
    QE sel ((1 : Tup X.F X.E X.K Sg) : Chr X.F X.E X.K) = ∅ := by
  have h : Qprime ((1 : Tup X.F X.E X.K Sg) : Chr X.F X.E X.K) = ∅ := by
    change Qprime (1 : Chr X.F X.E X.K) = ∅
    ext v
    simp [Qprime, MonoidHom.ker_one]
  unfold QE
  split_ifs with hf
  · rw [(Set.Finite.toFinset_eq_empty (h := hf)).2 h]
    rfl
  · rfl

theorem colsIn_isometry : ∀ (X : Fields) (hX : X.Ok) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ) (hL : I.Ok Ch sel mu cst G m2) (u : Pr.Word) (h : (chF W sel mu I u 0).Ok), mu = 1 → (∀ v, IsUnit ((MramH W Ch hX u).X v).det) ∧ ∀ (v : InfinitePlace X.K) (x : Fin (ramDim W Ch hX u) → X.K), ((Formalism.HermitianLatticesTheory.normAt (Pi.basisFun X.K (Fin (ramDim W Ch hX u))) (MramH W Ch hX u).X v x ^ 2 : ℝ) : ℂ) = famIpAt (chF W sel mu I u 0) h v (colsIn W Ch hX sel mu cst I hL u x) (colsIn W Ch hX sel mu cst I hL u x) := by
  intro X hX Pr R W Ch sel Sg mu cst I G m2 hL u h hmu
  refine ⟨(colPosH W Ch hX u 0).frameOK_sub (MramV W Ch u) (MramL W Ch u), fun v x => ?_⟩
  have hQ : QE sel (mu : Chr X.F X.E X.K) = ∅ := by
    subst hmu
    exact qe_one sel
  obtain ⟨b, hb⟩ := hL.zero_uniq
  have h1 : famIpAt (chF W sel mu I u 0) h v (colsIn W Ch hX sel mu cst I hL u x) (colsIn W Ch hX sel mu cst I hL u x) =
      (colGSD W Ch u 0).ipAt (colOk W Ch hX u 0) v (colOfCoord W Ch hX u x) (colOfCoord W Ch hX u x) := by
    unfold famIpAt
    rw [Fintype.sum_eq_single b fun b' hb' => absurd (hb b') hb']
    exact ipAt_frm hQ (colVal W u 0 (Pr.vT u) Pr.vGs) (colLev Ch 0) (I.levG 0 b) (hL.zero_G b) (I.levQ 0 b)
      (colRat W Ch hX u 0) (colOk W Ch hX u 0) (h b) v (colOfCoord W Ch hX u x)
  rw [h1, ← (colRat W Ch hX u 0).maj_eq]
  have h2 := (colPosH W Ch hX u 0).sub_maj (MramV W Ch u) v ((ramBas W Ch hX u).equivFun.symm x)
    ((ramBas W Ch hX u).equivFun.symm x)
  rw [thl_majAt_coord, LinearEquiv.apply_symm_apply] at h2
  refine Eq.trans ?_ h2
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.majAt Formalism.HermitianLatticesTheory.cnorm
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => by positivity)), Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  rfl

end GlobalTheory.ColFirstIso
end
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

theorem _root_.GlobalTheory.T.exists_unitary_heckeCharacter_phase_type_cm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∃ ξ : (AF F ⊗[F] E)ˣ →* Circle, IsHeckeCharF ξ ∧ HasExp B.emb ξ (fun _ => 1) := by
  first | exact @GlobalTheory.WeilTypeChar.exists_weil_char | exact GlobalTheory.WeilTypeChar.exists_weil_char | (intros; apply GlobalTheory.WeilTypeChar.exists_weil_char <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjEq

theorem exists_conjModel_cast {D : D7} {V : HSp D} {S S' : D.what₂.Tau → SPar} (e : S' = fun τ => dualPar (S τ))
    (M : DSModel V S) (v : M.Vec) (hv : IsExtVec M v) :
    ∃ (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ) (v' : M'.Vec),
      (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ y, c τ (M'.rep τ g y) = M.rep τ g (c τ y)) ∧ IsExtVec M' v' := by
  subst e
  exact GlobalTheory.ConjExt.exists_conjModel_ext D V S M v hv

theorem exists_conj_equiv : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.IsModels → TieIn T R κ v₀ → ∀ i σ, ¬ GoodEmb T.Q.c (res T σ) → ∃ c : ∀ τ, (R.MW i σ).H τ ≃ₗᵢ⋆[ℂ] (R.MW i ((starRingEnd ℂ).comp σ)).H τ, ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (Wc D i) τ), ∀ y, c τ ((R.MW i σ).rep τ g y) = (R.MW i ((starRingEnd ℂ).comp σ)).rep τ g (c τ y) := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hM hT i σ hσ
  have hg : GoodEmb T.Q.c (res T ((starRingEnd ℂ).comp σ)) := good_resC T hσ
  obtain ⟨hs, -, w, hw⟩ := GlobalTheory.HolDict.holShape_of_good D G Pl0 T0 A T R κ v₀ hT i ((starRingEnd ℂ).comp σ) hg
  obtain ⟨M', c, v', hc, hv'⟩ := exists_conjModel_cast (GlobalTheory.ConjReading.parAt_conj (Wc D i) σ) (R.MW i σ) (v₀ i σ)
    (hT.hv₀ i σ).1
  obtain ⟨U, hU⟩ := GlobalTheory.T.holomorphic_discrete_series_models_unitarily_equivalent D R.θ _ _ (R.MW i ((starRingEnd ℂ).comp σ)) M' w (v₀ i _) v' hM.inf hs hw
    (hT.hv₀ i _).1 hv'
  refine ⟨fun τ => (c τ).symm.trans (U τ), fun τ g hg y => ?_⟩
  show U τ ((c τ).symm _) = (R.MW i ((starRingEnd ℂ).comp σ)).rep τ g (U τ ((c τ).symm y))
  rw [← hU τ g hg]
  congr 1
  apply (c τ).injective
  rw [hc τ g hg, LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]

end GlobalTheory.ConjEq
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_unitary_conj_iff_exists_centralizer_norm : ∀ (K : Type) [Field K] (σ : K →+* K) (n : ℕ) (γ h : GL (Fin n) K), (∃ g ∈ UJ σ (1 : Matrix (Fin n) (Fin n) K), h⁻¹ * γ * h = g⁻¹ * γ * g) ↔ ∃ c : Matrix (Fin n) (Fin n) K, c * γ.val = γ.val * c ∧ cT σ c * c = (h.val * cT σ h.val)⁻¹ := by
  first | exact @GlobalTheory.UnitaryConj.main | exact GlobalTheory.UnitaryConj.main | (intros; apply GlobalTheory.UnitaryConj.main <;> assumption)
end

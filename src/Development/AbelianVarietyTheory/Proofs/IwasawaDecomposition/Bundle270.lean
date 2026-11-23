module

public import Formalism.LocalToGlobal.IndefiniteReal.Bridge
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle108
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle009
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle018
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainIntegralMulRight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle003
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotInjectiveTwoPrimesEqualNormCofinite
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsDiscriminantTwelfthRootOfIdealLatticeIffDelta1
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.RecTie
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle008
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003
import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.Mem GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.GsdIso

open _root_.Formalism.L2.Col Formalism.IndefR.Bridge

theorem exists_isom_vec : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] (S : Formalism.L2.Col.GSD K) (ok : S.Ok) {G Γ W : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ι : Γ →* G) (σ : K →+* ℂ) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (P : Bridge.ClassPres ι (S.toCSD ok) σ ρ J χ) (c : S.V →ₛₗ[σ] W) (d : G → S.D),
  (∀ (φ : S.EqFun) (h : G), P.extL (S.res ok φ) h = c (φ.1 (d h))) → (∃ φ : S.EqFun, φ ≠ 0) → ∃ v : S.V, c v ≠ 0 ∧ inner ℂ (c v) (c v) = σ (S.pair v v) := by
  classical
  intro K _ _ _ S ok G Γ W _ _ _ _ ι σ ρ J χ P c d H hne
  obtain ⟨φ, hφ⟩ := hne
  obtain ⟨k, hk⟩ : ∃ k, φ.1 (S.outSec.rep k) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hφ ((S.res ok).map_eq_zero_iff.1 (Subtype.ext (funext h)))
  set x := φ.1 (S.outSec.rep k) with hx
  have vi := (S.res ok φ).2 k
  let f : (S.toCSD ok).Forms := ⟨Pi.single k x, fun c' γ => by
    by_cases h : c' = k
    · subst h
      rw [Pi.single_eq_same]
      exact vi γ
    · rw [Pi.single_eq_of_ne h, map_zero]⟩
  have H1 := H ((S.res ok).symm f) (P.y k)
  rw [ClassPres.extL_apply, LinearEquiv.apply_symm_apply, GlobalTheory.PresBasic.ext_y] at H1
  have e2 : ((S.res ok).symm f).1 (d (P.y k)) =
      S.ρ (S.outSec.mv (d (P.y k))) ((Pi.single k x : S.Cl → S.V) (S.cls (d (P.y k)))) := rfl
  rw [e2] at H1
  have hfk : ((f : S.Cl → S.V)) k = x := by simp [f]
  rw [hfk] at H1
  have hc0 : P.coef x ≠ 0 := fun h => hk (GlobalTheory.PresBasic.coef_injective P (h.trans (map_zero _).symm))
  have hc : S.cls (d (P.y k)) = k := by
    by_contra h
    rw [Pi.single_eq_of_ne h, map_zero, map_zero] at H1
    exact hc0 H1
  rw [hc, Pi.single_eq_same] at H1
  refine ⟨S.ρ (S.outSec.mv (d (P.y k))) x, H1 ▸ hc0, ?_⟩
  rw [← H1, P.coef_pair, ok.inv]

end GlobalTheory.Mem.GsdIso
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2



namespace GlobalTheory.Mem.TransportRead

theorem transport_ext_eq : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {S : Formalism.L2.Col.GSD K} {G Γ G' Γ' : Type}
    [Group G] [Group Γ] [Group G'] [Group Γ'] {ι : Γ →* G} {J : Subgroup G} (A : Bridge.AdPts S ι J) (h : S.Ok)
    {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (σ : K →+* ℂ) (ρ : Γ →* Module.End ℂ W) (χ : J →* ℂˣ)
    (coef : S.V →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun i => coef (S.bV i))
    (hspan : Submodule.span ℂ (Set.range fun i => coef (S.bV i)) = ⊤)
    (hpair : ∀ x x', inner ℂ (coef x) (coef x') = σ (S.pair x x')) (hK1 : ∀ k : J, (k : G) ∈ A.K1 → χ k = 1)
    (hgl : ∀ (γ : Γ) (k : J) (v : S.V), coef (S.ρ (A.gl (γ, k)) v) = ((χ k)⁻¹ : ℂˣ) • ρ γ (coef v))
    {ι' : Γ' →* G'} {ρ' : Γ' →* Module.End ℂ W} {J' : Subgroup G'} {χ' : J' →* ℂˣ}
    (eG : G ≃* G') (eΓ : Γ ≃* Γ') (hι : ∀ γ, ι' (eΓ γ) = eG (ι γ)) (hρ : ∀ γ, ρ' (eΓ γ) = ρ γ)
    (hJ : J' = J.map eG.toMonoidHom) (hχ : ∀ (k : J) (hk : eG k ∈ J'), χ' ⟨eG k, hk⟩ = χ k)
    (f : (S.toCSD h).Forms) (g : G'),
    ((Bridge.classPresOf A h σ ρ χ coef hli hspan hpair hK1 hgl).transport eG eΓ hι hρ hJ hχ).ext (f : S.Cl → S.V) g =
      coef ((((S.res h).symm f : S.EqFun) : S.D → S.V) (A.q (eG.symm g))) := by
  intro K _ _ _ S G Γ G' Γ' _ _ _ _ ι J A h W _ _ σ ρ χ coef hli hspan hpair hK1 hgl ι' ρ' J' χ' eG eΓ hι hρ hJ hχ f g
  set P' := (Bridge.classPresOf A h σ ρ χ coef hli hspan hpair hK1 hgl).transport eG eΓ hι hρ hJ hχ with hP'
  have hJ' : ∀ x, x ∈ J' ↔ eG.symm x ∈ J := fun x => by subst hJ; exact Subgroup.mem_map_equiv
  have hspec := P'.dec_spec g
  set γ' := P'.decG g
  set c := P'.decC g
  set k' := P'.decK g
  have hy : P'.y c = eG (A.y c) := rfl
  have hc : P'.coef = coef := rfl
  let k'' : J := ⟨eG.symm (k' : G'), (hJ' _).1 k'.2⟩
  have hg : eG.symm g = ι (eΓ.symm γ') * A.y c * (k'' : G) := by
    have e : ι (eΓ.symm γ') = eG.symm (ι' γ') := by
      rw [MulEquiv.eq_symm_apply, ← hι, MulEquiv.apply_symm_apply]
    rw [e, hspec, hy]
    simp only [map_mul, MulEquiv.symm_apply_apply, k'']
  have hq : A.q (eG.symm g) = A.gl (eΓ.symm γ', k''⁻¹) • S.outSec.rep c := by
    rw [hg, A.q_mul, A.q_y]
  set φ := (S.res h).symm f with hφ
  have hφc : ((φ : S.EqFun) : S.D → S.V) (S.outSec.rep c) = (f : S.Cl → S.V) c := by
    have := Formalism.L2.Col.GSD.resOf_apply S h S.outSec φ c
    rw [← this]
    show (((S.res h) φ).1 : S.Cl → S.V) c = (f : S.Cl → S.V) c
    rw [hφ, LinearEquiv.apply_symm_apply]
  have hk : k' = ⟨eG (k'' : G), by simp only [k'', MulEquiv.apply_symm_apply]; exact k'.2⟩ :=
    Subtype.ext (by simp only [k'', MulEquiv.apply_symm_apply])
  rw [hq, φ.2, hφc, hgl]
  show (χ' k' : ℂ) • ρ' γ' (P'.coef ((f : S.Cl → S.V) c)) = _
  rw [hc, hk, hχ]
  have hγ : ρ' γ' = ρ (eΓ.symm γ') := by rw [← hρ, MulEquiv.apply_symm_apply]
  rw [hγ, map_inv, inv_inv, Units.smul_def]

end GlobalTheory.Mem.TransportRead
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.SchurPairingInvariant

theorem left_inv_of_mem_Minf {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {n : ℕ}
    {P : principalLevelFrame.RowPsi V n} {x : MMap M} (hx : x ∈ principalLevelFrame.Minf θ P M) (v : M.Vec) :
    ∀ γ ∈ GQ V, ∀ g, x v (γ * g) = x v g := by
  unfold principalLevelFrame.Minf at hx
  refine Submodule.iSup_induction _ (motive := fun z : MMap M => ∀ γ ∈ GQ V, ∀ g, z v (γ * g) = z v g) hx ?_ ?_ ?_
  · intro N z hz
    exact (PeterssonHilbertSpace.mult_cont_left M θ _ _ hz v).2
  · intro γ _ g
    rfl
  · intro z w hz hw γ hγ g
    simp only [MultilinearMap.add_apply, Pi.add_apply, hz γ hγ g, hw γ hγ g]

theorem ipM_congr_of_iff {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {μ : Measure (GA D V)}
    {𝓕 : Set (GA D V)} {T T' U U' : MMap M} (h : ∀ c, IsMultIP M μ 𝓕 T T' c ↔ IsMultIP M μ 𝓕 U U' c) :
    ipM M μ 𝓕 T T' = ipM M μ 𝓕 U U' := by
  have e : IsMultIP M μ 𝓕 T T' = IsMultIP M μ 𝓕 U U' := funext fun c => propext (h c)
  unfold ipM
  rw [e]

theorem ipM_actM : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (θ : InfFam D) (M : DSModel V S) (n : ℕ) (P : principalLevelFrame.RowPsi V n) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), SchurAll D → V.SigOK → IsInfFam θ → μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → ∀ (h : Formalism.AUTREP.GAf D.host.E n), ∀ x ∈ principalLevelFrame.Minf θ P M, ∀ y ∈ principalLevelFrame.Minf θ P M, ipM M μ 𝓕 (principalLevelFrame.actM P M h x) (principalLevelFrame.actM P M h y) = ipM M μ 𝓕 x y := by
  intro D V S θ M n P μ 𝓕 _ _ _ hμ h𝓕 h x hx y hy
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig V.gram
  have : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  have := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D V μ hμ
  apply ipM_congr_of_iff
  intro c
  have key : ∀ v v' : M.Vec, _ := fun v v' =>
    GlobalTheory.fundamentalDomain_integral_mul_right μ (GQ V) 𝓕 (fun g => star (x v g) * y v' g) (P.ψ h) h𝓕
      (fun γ hγ g => by simp only [left_inv_of_mem_Minf hx v γ hγ g, left_inv_of_mem_Minf hy v' γ hγ g])
  unfold IsMultIP
  simp only [principalLevelFrame.actM_apply]
  constructor
  · intro H v v'
    obtain ⟨k1, k2⟩ := key v v'
    exact ⟨k1.2 (H v v').1, k2 ▸ (H v v').2⟩
  · intro H v v'
    obtain ⟨k1, k2⟩ := key v v'
    exact ⟨k1.1 (H v v').1, k2.trans (H v v').2⟩

end GlobalTheory.SchurPairingInvariant
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.DecompKer

open Formalism.L2.NG (FinTyp)

def isoSetoid (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) : Setoid (FinTyp L n) where
  r π π' := π.Iso π'
  iseqv := ⟨fun π => Formalism.L2.NG.IsoRep.refl _, fun {π _} h => Formalism.L2.NG.IsoRep.symm π.stable h,
    fun h h' => Formalism.L2.NG.IsoRep.trans h h'⟩

theorem isotIn_le_of_iso {D : D7} {n : ℕ} {A : Type} [AddCommGroup A] [Module ℂ A]
    (ρ : Formalism.AUTREP.GAf D.host.E n →* Module.End ℂ A) (C : Submodule ℂ A) {π π' : FinTyp D.host.E n}
    (h : π.Iso π') : principalLevelFrame.isotIn (D := D) ρ C π' ≤ principalLevelFrame.isotIn (D := D) ρ C π := by
  obtain ⟨T, hT⟩ := h
  refine iSup₂_le fun Φ hΦ => ?_
  rintro _ ⟨f, rfl⟩
  have hE : principalLevelFrame.IsEqvA ρ π (Φ.comp T.toLinearMap) ∧ LinearMap.range (Φ.comp T.toLinearMap) ≤ C := by
    refine ⟨fun g a => ?_, ?_⟩
    · have e : T ⟨Formalism.L2.NG.rt D.host.E n g a, π.stable g a a.2⟩ =
          ⟨Formalism.L2.NG.rt D.host.E n g (T a), π'.stable g _ (T a).2⟩ :=
        Subtype.ext (hT g a _ rfl)
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [e]
      exact hΦ.1 g (T a)
    · rintro _ ⟨a, rfl⟩
      exact hΦ.2 ⟨T a, rfl⟩
  refine Submodule.mem_iSup_of_mem (Φ.comp T.toLinearMap) (Submodule.mem_iSup_of_mem hE ⟨T.symm f, ?_⟩)
  simp

end GlobalTheory.DecompKer


open GlobalTheory.DecompKer in
theorem GlobalTheory.decomp_kernels_isotIn : ∀ (D : D7) (n : ℕ) (A : Type) [AddCommGroup A] [Module ℂ A] (ρ : Formalism.AUTREP.GAf D.host.E n →* Module.End ℂ A) (C : Submodule ℂ A) (B : A → A → ℂ), (∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, ∀ c : ℂ, B x (y + c • z) = B x y + c * B x z) → (∀ x ∈ C, ∀ y ∈ C, B x y = starRingEnd ℂ (B y x)) → (∀ x ∈ C, x ≠ 0 → 0 < (B x x).re) → (∀ π π' : Formalism.L2.NG.FinTyp D.host.E n, ¬ π.Iso π' → ∀ x ∈ principalLevelFrame.isotIn (D := D) ρ C π, ∀ y ∈ principalLevelFrame.isotIn (D := D) ρ C π', B x y = 0) → ∀ (ι : Type) (O : ι → A →ₗ[ℂ] A), (∀ i π, ∀ x ∈ principalLevelFrame.isotIn (D := D) ρ C π, O i x ∈ principalLevelFrame.isotIn (D := D) ρ C π) → ∀ x ∈ ⨆ π : Formalism.L2.NG.FinTyp D.host.E n, principalLevelFrame.isotIn (D := D) ρ C π, (∀ i, O i x = 0) → x ∈ ⨆ π : Formalism.L2.NG.FinTyp D.host.E n, (principalLevelFrame.isotIn (D := D) ρ C π ⊓ ⨅ i, LinearMap.ker (O i)) := by
  intro D n A _ _ ρ C B h1 h2 h3 h4 ι O hO x hx hOx
  classical
  let S := isoSetoid D.host.E n
  let q : Formalism.L2.NG.FinTyp D.host.E n → Quotient S := Quotient.mk S
  have hC : ∀ π, principalLevelFrame.isotIn (D := D) ρ C π ≤ C := fun π => iSup₂_le fun Φ h => h.2
  obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ x).mp hx
  set t := f.support.image q with ht
  let y : Quotient S → A := fun c => ∑ π ∈ f.support with q π = c, f π
  have hxy : (f.sum fun _ xi => xi) = ∑ c ∈ t, y c := by
    rw [Finsupp.sum]
    exact (Finset.sum_fiberwise_of_maps_to (fun π hπ => Finset.mem_image_of_mem q hπ) _).symm
  have hrep : ∀ π c, q π = c → c.out.Iso π := fun π c hq =>
    Quotient.exact (s := S) (by rw [Quotient.out_eq]; exact hq.symm)
  have hyI : ∀ c, y c ∈ principalLevelFrame.isotIn (D := D) ρ C c.out := by
    intro c
    refine Submodule.sum_mem _ fun π hπ => ?_
    exact isotIn_le_of_iso ρ C (hrep π c (Finset.mem_filter.mp hπ).2) (hf π)
  have hni : ∀ c c' : Quotient S, c ≠ c' → ¬ c.out.Iso c'.out := by
    intro c c' hne hI
    apply hne
    rw [← Quotient.out_eq c, ← Quotient.out_eq c']
    exact Quotient.sound hI
  have hB0 : ∀ u ∈ C, B u 0 = 0 := by
    intro u hu
    have := h1 u hu 0 C.zero_mem 0 C.zero_mem 1
    simp only [smul_zero, add_zero, one_mul] at this
    simpa using this
  have hOy : ∀ i, ∀ c ∈ t, O i (y c) = 0 := by
    intro i c hc
    set u := O i (y c) with hu
    have huI : u ∈ principalLevelFrame.isotIn (D := D) ρ C c.out := hO i c.out (y c) (hyI c)
    have huC : u ∈ C := hC _ huI

    let Z : Submodule ℂ A :=
      { carrier := {v | v ∈ C ∧ B u v = 0}
        zero_mem' := ⟨C.zero_mem, hB0 u huC⟩
        add_mem' := fun {a b} ha hb => ⟨C.add_mem ha.1 hb.1, by
          have := h1 u huC a ha.1 b hb.1 1
          rw [one_smul] at this
          rw [this, ha.2, hb.2]; simp⟩
        smul_mem' := fun c' a ha => ⟨C.smul_mem c' ha.1, by
          have := h1 u huC 0 C.zero_mem a ha.1 c'
          rw [zero_add] at this
          rw [this, hB0 u huC, ha.2]; simp⟩ }
    have hsum : ∑ c' ∈ t, O i (y c') = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum, ← hxy]; exact hOx i
    have hrest : ∑ c' ∈ t.erase c, O i (y c') ∈ Z := by
      refine Submodule.sum_mem _ fun c' hc' => ?_
      have hne : c' ≠ c := (Finset.mem_erase.mp hc').1
      have hv : O i (y c') ∈ principalLevelFrame.isotIn (D := D) ρ C c'.out := hO i c'.out (y c') (hyI c')
      exact ⟨hC _ hv, h4 c.out c'.out (hni c c' (Ne.symm hne)) u huI _ hv⟩
    have hueq : u = -∑ c' ∈ t.erase c, O i (y c') := by
      rw [eq_neg_iff_add_eq_zero, hu, Finset.add_sum_erase t (fun c' => O i (y c')) hc, hsum]
    have huZ : u ∈ Z := by rw [hueq]; exact Z.neg_mem hrest
    by_contra hne
    have := h3 u huC hne
    rw [huZ.2] at this
    simp at this
  rw [hxy]
  refine Submodule.sum_mem _ fun c hc => ?_
  refine Submodule.mem_iSup_of_mem c.out (Submodule.mem_inf.mpr ⟨hyI c, ?_⟩)
  exact Submodule.mem_iInf _ |>.mpr fun i => LinearMap.mem_ker.mpr (hOy i c hc)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RowFix

open Formalism.L2.NG Formalism.IndefR.principalLevelFrame

theorem exists_fixed_of_mem_isot {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {A : Type} [AddCommGroup A] [Module ℂ A] (ρ : Formalism.AUTREP.GAf L n →* Module.End ℂ A)
    (π : FinTyp L n) (Q : (π.S →ₗ[ℂ] A) → Prop) (Kp : Formalism.AUTREP.GAf L n → Prop) {y : A}
    (hy : y ∈ ⨆ (Φ : π.S →ₗ[ℂ] A) (_ : IsEqvA ρ π Φ ∧ Q Φ), LinearMap.range Φ) (hy0 : y ≠ 0)
    (hfix : ∀ κ, Kp κ → ρ κ y = y) :
    ∃ f ∈ π.S, f ≠ 0 ∧ ∀ κ, Kp κ → rt L n κ f = f := by
  classical
  let ι := {Φ : π.S →ₗ[ℂ] A // IsEqvA ρ π Φ ∧ Q Φ}
  have hy' : y ∈ ⨆ j : ι, LinearMap.range j.1 := by
    rwa [iSup_subtype'] at hy
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hy'
  let Y : Finset ι → Submodule ℂ A := fun t => ⨆ j ∈ t, LinearMap.range j.1
  have hYst : ∀ (t : Finset ι) (g : Formalism.AUTREP.GAf L n) (x : A), x ∈ Y t → ρ g x ∈ Y t := by
    intro t g x hx
    have hle : Y t ≤ (Y t).comap (ρ g) := by
      refine iSup₂_le fun j hj => ?_
      rintro _ ⟨v, rfl⟩
      rw [Submodule.mem_comap, ← j.2.1 g v]
      exact (le_iSup₂ (f := fun j (_ : j ∈ t) => LinearMap.range j.1) j hj) (LinearMap.mem_range_self _ _)
    exact hle hx
  have key : ∀ (t : Finset ι) (x : A), x ∈ Y t → x ≠ 0 → (∀ κ, Kp κ → ρ κ x = x) →
      ∃ f ∈ π.S, f ≠ 0 ∧ ∀ κ, Kp κ → rt L n κ f = f := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro x hx hx0 _
      exact absurd (by simpa [Y] using hx) hx0
    | insert j t hjt ih =>
      intro x hx hx0 hxfix
      have hx' : x ∈ LinearMap.range j.1 ⊔ Y t := by
        simpa [Y, Finset.iSup_insert] using hx
      obtain ⟨_, ⟨v, rfl⟩, z, hz, rfl⟩ := Submodule.mem_sup.1 hx'
      let U : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ) := ((Y t).comap j.1).map π.S.subtype
      have hUst : ∀ h, ∀ f ∈ U, rt L n h f ∈ U := by
        rintro h _ ⟨a, ha, rfl⟩
        refine ⟨⟨rt L n h a, π.stable h a a.2⟩, ?_, rfl⟩
        have ha' : j.1 a ∈ Y t := ha
        show j.1 _ ∈ Y t
        rw [j.2.1 h a]
        exact hYst t h _ ha'
      rcases π.irr U (Submodule.map_subtype_le _ _) hUst with hU | hU
      ·
        have hvfix : ∀ κ, Kp κ → rt L n κ (v : Formalism.AUTREP.GAf L n → ℂ) = v := by
          intro κ hκ
          let v' : π.S := ⟨rt L n κ v, π.stable κ v v.2⟩
          have hmem : v' - v ∈ (Y t).comap j.1 := by
            rw [Submodule.mem_comap, map_sub, j.2.1 κ v]
            have h1 := hxfix κ hκ
            rw [map_add (f := _)] at h1
            have h3 : ρ κ (j.1 v) - j.1 v = z - ρ κ z := by
              rw [sub_eq_sub_iff_add_eq_add, h1, add_comm]
            rw [h3]
            exact sub_mem hz (hYst t κ z hz)
          have hU' : ((v' - v : π.S) : Formalism.AUTREP.GAf L n → ℂ) ∈ U := ⟨_, hmem, rfl⟩
          rw [hU, Submodule.mem_bot] at hU'
          exact sub_eq_zero.1 hU'
        by_cases hv : (v : Formalism.AUTREP.GAf L n → ℂ) = 0
        · have hv' : v = 0 := Subtype.ext hv
          subst hv'
          simp only [map_zero, zero_add] at hx0 hxfix
          exact ih z hz hx0 hxfix
        · exact ⟨v, v.2, hv, hvfix⟩
      · have hvU : (v : Formalism.AUTREP.GAf L n → ℂ) ∈ U := by rw [hU]; exact v.2
        obtain ⟨a, ha, hav⟩ := hvU
        have : a = v := Subtype.ext hav
        subst this
        exact ih _ (add_mem ha hz) hx0 hxfix
  exact key s y (by simpa [Y] using hs) hy0 hfix

theorem exists_fixed_rowRep : ∀ (D : D7) (V : HSp D) (n : ℕ) (Sp : D.what₂.Tau → SPar) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (P : principalLevelFrame.RowPsi V n) (M : Mult.DSModel V Sp) (J : Bool → Set (GA D V)) (χ : Bool → GA D V → ℂ) (e : Bool → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (σ : principalLevelFrame.FTR θ P M J χ e) (Kp : Formalism.AUTREP.GAf D.host.E n → Prop), (∀ b κ, Kp κ → P.ψ κ ∈ J b ∧ χ b (P.ψ κ) = 1) → ∃ f ∈ (principalLevelFrame.rowRepR θ σ).S, f ≠ 0 ∧ ∀ κ, Kp κ → NG.rt D.host.E n κ f = f := by
  intro D V n Sp θ P M J χ e σ Kp hK
  obtain ⟨b, hb⟩ := rowRepR_occ θ σ
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
  have hy' : y ∈ Formalism.IndefR.Mult.goodPart θ M (J b) (χ b) (e b) ⊓
      isotIn (actM P M) (Minf θ P M) (FinTyp.conjT (rowRepR θ σ)) := hy
  rw [Submodule.mem_inf] at hy'
  have hM : y ∈ Formalism.IndefR.Mult.Mult θ M (J b) (χ b) := (Submodule.mem_inf.1 hy'.1).1
  have hfixY : ∀ κ, Kp κ → actM P M κ y = y := by
    intro κ hκ
    have hle : Formalism.IndefR.Mult.Mult θ M (J b) (χ b) ≤ LinearMap.ker (actM P M κ - LinearMap.id) := by
      refine Submodule.span_le.2 ?_
      intro T hT
      have hT' : Formalism.IndefR.Mult.IsMultMap θ M (J b) (χ b) T := hT
      rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
      apply MultilinearMap.ext
      intro v
      funext g
      rw [actM_apply, hT'.lev v _ (hK b κ hκ).1 g, (hK b κ hκ).2, one_mul]
    have h := hle hM
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at h
    exact h
  obtain ⟨f, hf, hf0, hffix⟩ := exists_fixed_of_mem_isot (actM P M) (FinTyp.conjT (rowRepR θ σ))
    (fun Φ => LinearMap.range Φ ≤ Minf θ P M) Kp hy'.2 hy0 hfixY
  refine ⟨fun g => star (f g), (mem_conjSub).1 hf, ?_, fun κ hκ => ?_⟩
  · intro h0
    apply hf0
    funext g
    have := congrFun h0 g
    simpa using this
  · rw [← conj_rt, hffix κ hκ]

end GlobalTheory.RowFix
end

section

open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

namespace GlobalTheory.MemN

theorem nonempty_nbc_of_isEmpty_loc :
    ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (nd : NData R H what₂) (A : NAut nd),
      IsEmpty nd.Loc → Nonempty (NBC A) := by
  intro R H what₂ nd A hL
  exact ⟨{
    AU := fun _ => Empty
    multAU := fun _ x => x.elim
    sphAU := fun _ x => x.elim
    locAU := fun _ x => x.elim
    satAU := fun _ x => x.elim
    satAU_card := fun _ x => x.elim
    Wt := fun _ => Empty
    infW := fun _ x => x.elim
    infW_card := fun _ x => x.elim
    wtAU := fun _ x => x.elim
    infW_alg := fun _ x => x.elim
    embAV := fun i => hL.elim i
    embAV_inj := fun i => hL.elim i
    embAV_loc := fun i => hL.elim i
    embAV_sat := fun i => hL.elim i
    embAV_sph := fun i => hL.elim i
    embAV_inf := fun i => hL.elim i }⟩

end GlobalTheory.MemN
end

section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

theorem _root_.GlobalTheory.T.not_injective_two_primes_equal_norm_cofinite : ∀ (K F : Type) [Field K] [NumberField K] [Field F] [NumberField F] (S : Set (HeightOneSpectrum (𝓞 K))), S.Finite → ∀ f : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} × Bool → HeightOneSpectrum (𝓞 F), Function.Injective f → (∀ x, Ideal.absNorm (f x).asIdeal = Ideal.absNorm x.1.1.asIdeal) → False := by
  first | exact @GlobalTheory.Mem.ZetaPole.not_injective_double_primes | exact GlobalTheory.Mem.ZetaPole.not_injective_double_primes | (intros; apply GlobalTheory.Mem.ZetaPole.not_injective_double_primes <;> assumption)
end

module

public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle485
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelv
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle482
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle081
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle218
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle282
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle335
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle483
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle179
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotInjectiveTwoPrimesEqualNormCofinite
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.crystalline_coboundary_lift : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ A : GRep ↥(GK K) ℚ_[l] LL O, IsDR (P.PD K) A.ρ → ∀ (c : ↥(GK K) → A.V) (x : A.V ⊗[ℚ_[l]] P.R.B), (∀ g, c g ⊗ₜ[ℚ_[l]] (1 : P.R.B) = actVB (P.PD K) A.ρ g x - x) → x - φVB (P.PD K) (LL := LL) (V := A.V) x ∈ Dcris (P.PD K) A.ρ ∧ ∃ d ∈ DdR (P.PD K) A.ρ, ιV (P.PD K) (LL := LL) (V := A.V) x - d ∈ FilV (P.PD K) (LL := LL) (V := A.V) 0 := by
  first | exact @GlobalTheory.CobCrisLift.coboundary_lift | exact GlobalTheory.CobCrisLift.coboundary_lift | (intros; apply GlobalTheory.CobCrisLift.coboundary_lift <;> assumption)
end

section

noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SublevelFinIndex

variable {E : Type} [Field E] [NumberField E]

variable {F : Type} [Field F] [NumberField F] [StarRing E] [Algebra F E] {n : ℕ} {LL : Type} [CommRing LL]

theorem parLev_anti (hc : CMData F E) (J : Matrix (Fin n) (Fin n) E) (β : GL (Fin n) (E ⊗[F] GlobalTheoryTheory.GenusMassVolumes.Af F)) (D : LevDat E LL n)
    (Q' : Finset (Pl E)) (xq : ∀ PP : Pl E, (kP PP)ˣ →* LLˣ) (h : D.Q ⊆ Q') :
    parLev hc J β { D with Q := Q', xq := xq } ≤ parLev hc J β D := by
  intro x hx
  have h2 : x ∈ ⨅ PP ∈ Q', parah β PP (blk2 D.r) := hx.2
  have h3 : x ∈ ⨅ PP ∈ D.Q, parah β PP (blk2 D.r) :=
    Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h2 PP) (h hP)
  exact ⟨hx.1, h3⟩

theorem lev_of_red (hc : CMData F E) (J : Matrix (Fin n) (Fin n) E) (β : GL (Fin n) (E ⊗[F] GlobalTheoryTheory.GenusMassVolumes.Af F)) (D : LevDat E LL n)
    (Q' : Finset (Pl E)) (xq : ∀ PP : Pl E, (kP PP)ˣ →* LLˣ) {x : GL (Fin n) (E ⊗[F] GlobalTheoryTheory.GenusMassVolumes.Af F)}
    (hx : x ∈ lev hc J β D) (hr : ∀ PP ∈ Q', redFn β PP x = 1) : x ∈ lev hc J β { D with Q := Q', xq := xq } := by
  refine ⟨⟨hx.1.1, Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => mem_parah.2 ⟨parLev_St hx.1, ?_⟩⟩, hx.2⟩
  rw [hr PP hP]
  exact Subgroup.one_mem _

end GlobalTheory.SublevelFinIndex


open GlobalTheory.SublevelFinIndex in
theorem GlobalTheory.sublevel_finiteIndex : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSDFrame V β Λ 1 → ∀ (L : LevDat D.host.E ℂ V.rank) (Q' : Finset (Pl D.host.E)) (xq : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), L.Q ⊆ Q' → (levEnv V β { L with Q := Q', xq := xq }).J ≤ (levEnv V β L).J ∧ (levEnv V β { L with Q := Q', xq := xq }).Q ≤ (levEnv V β L).Q ∧ (((levEnv V β { L with Q := Q', xq := xq }).J).subgroupOf (levEnv V β L).J).FiniteIndex ∧ ∀ g : Bridge.Gf V, g ∈ (levEnv V β { L with Q := Q', xq := xq }).Q → g ∈ (levEnv V β L).J → g ∈ (levEnv V β { L with Q := Q', xq := xq }).J := by
  intro D V β Λ _ L Q' xq hQ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g hg
    have h : Formalism.UG.bc (Lev.swapAE D) g.1 ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Lev.flag1L { L with Q := Q', xq := xq }) := hg
    exact (⟨parLev_anti D.sp.cm V.gram β (Lev.flag1L L) Q' xq hQ h.1, h.2⟩ :
      Formalism.UG.bc (Lev.swapAE D) g.1 ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Lev.flag1L L))
  · intro g hg
    have h : Formalism.UG.bc (Lev.swapAE D) g.1 ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Lev.flagL { L with Q := Q', xq := xq }) := hg
    exact (⟨parLev_anti D.sp.cm V.gram β (Lev.flagL L) Q' xq hQ h.1, h.2⟩ :
      Formalism.UG.bc (Lev.swapAE D) g.1 ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Lev.flagL L))
  · refine ⟨Formalism.UG.P.levelv_relIndex_ne_zero _ _
      (fun (g : Bridge.Gf V) (PP : ↥Q') => redFn β PP.1 (Formalism.UG.bc (Lev.swapAE D) g.1)) ?_⟩
    intro a ha b hb hab
    have hab' : Formalism.UG.bc (Lev.swapAE D) (a⁻¹ * b).1 ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Lev.flag1L L) :=
      (levEnv V β L).J.mul_mem ((levEnv V β L).J.inv_mem ha) hb
    have ha' : Formalism.UG.bc (Lev.swapAE D) a.1 ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Lev.flag1L L) := ha
    have hb' : Formalism.UG.bc (Lev.swapAE D) b.1 ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Lev.flag1L L) := hb
    show Formalism.UG.bc (Lev.swapAE D) (a⁻¹ * b).1 ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Lev.flag1L { L with Q := Q', xq := xq })
    refine lev_of_red D.sp.cm V.gram β (Lev.flag1L L) Q' xq hab' fun PP hP => ?_
    have e := congrFun hab ⟨PP, hP⟩
    have hSa := parLev_St ha'.1
    have hSb := parLev_St hb'.1
    simp only at e
    rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, redFn_mul ((St β).inv_mem hSa) hSb, redFn_inv hSa, e,
      inv_mul_cancel]
  · intro g hgQ hgJ
    have h1 : Formalism.UG.bc (Lev.swapAE D) g.1 ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Lev.flagL { L with Q := Q', xq := xq }) := hgQ
    have h2 : Formalism.UG.bc (Lev.swapAE D) g.1 ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Lev.flag1L L) := hgJ
    exact (⟨h1.1, h2.2⟩ :
      Formalism.UG.bc (Lev.swapAE D) g.1 ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Lev.flag1L { L with Q := Q', xq := xq }))
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.InvLine

theorem spanQ : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), ∃ z0 : ↥(GK K) × ↥(GK K) → ℚ_[l], (Continuous z0 ∧ ∀ g h k, ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]) * z0 (h, k) - z0 (g * h, k) + z0 (g, h * k) - z0 (g, h) = 0) ∧ ∀ z : ↥(GK K) × ↥(GK K) → ℚ_[l], Continuous z → (∀ g h k, ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0) → ∃ x : ℚ_[l], CobL (P.PD K) (z - x • z0) := by
  intro hT l _ P K
  obtain ⟨hcpt, χ, c, hχc, hχ, hgen, hfin⟩ := GlobalTheory.T.exists_fundamentalTwoCocycle_of_localTateDuality hT l P K
  obtain ⟨⟨hcc, hcoc⟩, hsp⟩ := GlobalTheory.T.continuous_twoCocycle_multiple_of_fundamental l ↥(GK K) χ c hχc hgen hfin
  have hcyc : ∀ g, ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]) = ((χ g : ℤ_[l]) : ℚ_[l]) := fun g => by
    rw [hχ]; rfl
  refine ⟨fun p => (c p : ℚ_[l]), ⟨hcc, fun g h k => by rw [hcyc]; exact hcoc g h k⟩, fun z hz hzc => ?_⟩
  obtain ⟨x, f, hf, hfd⟩ := hsp z hz (fun g h k => by rw [← hcyc]; exact hzc g h k)
  refine ⟨x, f, hf, ?_⟩
  funext p
  obtain ⟨g, h⟩ := p
  have e := hfd g h
  rw [← hcyc] at e
  simp only [ReciprocityTheory.Def.d1, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [← e]
  simp [charRep]

theorem exists_inv : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∃ (Z : Submodule LL (↥(GK K) × ↥(GK K) → LL)) (inv : ↥Z →ₗ[LL] LL), (∀ z, z ∈ Z ↔ Continuous z ∧ ∀ g h k, ((cycLL (P.PD K) LL g : LLˣ) : LL) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0) ∧ ∀ z : ↥Z, inv z = 0 ↔ CobL (P.PD K) z.1 := by
  intro hT l _ P K LL _ _ _ O _ _ hO
  obtain ⟨z0, ⟨hz0c, hz0⟩, hspan⟩ := GlobalTheory.T.span_cyclotomic_twoCocycles_finite_extension l P K LL O hO (spanQ hT l P K)
  have htr : IsTopologicalRing LL := hO.2.2.2.1
  let Z : Submodule LL (↥(GK K) × ↥(GK K) → LL) :=
    { carrier := {z | Continuous z ∧ ∀ g h k, ((cycLL (P.PD K) LL g : LLˣ) : LL) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0}
      add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun g h k => by
        have e1 := ha.2 g h k
        have e2 := hb.2 g h k
        simp only [Pi.add_apply]
        linear_combination e1 + e2⟩
      zero_mem' := ⟨continuous_const, fun g h k => by simp⟩
      smul_mem' := fun c a ha => ⟨ha.1.const_smul c, fun g h k => by
        have e1 := ha.2 g h k
        simp only [Pi.smul_apply, smul_eq_mul]
        linear_combination c * e1⟩ }
  have hZ : ∀ z, z ∈ Z ↔ Continuous z ∧ ∀ g h k, ((cycLL (P.PD K) LL g : LLˣ) : LL) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0 := fun z => Iff.rfl
  let B : Submodule LL ↥Z :=
    { carrier := {z | CobL (P.PD K) z.1}
      add_mem' := fun {a b} ha hb => by
        obtain ⟨f1, hf1, e1⟩ := ha
        obtain ⟨f2, hf2, e2⟩ := hb
        exact ⟨f1 + f2, hf1.add hf2, by rw [map_add (f := _), e1, e2]; rfl⟩
      zero_mem' := ⟨0, continuous_const, by rw [map_zero]; rfl⟩
      smul_mem' := fun c a ha => by
        obtain ⟨f1, hf1, e1⟩ := ha
        exact ⟨c • f1, hf1.const_smul c, by rw [map_smul, e1]; rfl⟩ }
  have hB : ∀ z : ↥Z, z ∈ B ↔ CobL (P.PD K) z.1 := fun z => Iff.rfl
  let z0' : ↥Z := ⟨z0, hz0c, hz0⟩
  have hQ : ∀ z : ↥Z, ∃ x : LL, B.mkQ z = x • B.mkQ z0' := by
    intro z
    obtain ⟨x, hx⟩ := hspan z.1 z.2.1 z.2.2
    refine ⟨x, ?_⟩
    rw [← map_smul, ← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hx
  refine ⟨Z, ?_⟩
  by_cases h0 : B.mkQ z0' = 0
  · refine ⟨0, hZ, fun z => ?_⟩
    obtain ⟨x, hx⟩ := hQ z
    rw [h0, smul_zero, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    simp only [LinearMap.zero_apply, true_iff]
    exact hx
  · have htop : Submodule.span LL {B.mkQ z0'} = ⊤ := by
      rw [eq_top_iff]
      intro q _
      obtain ⟨z, rfl⟩ := B.mkQ_surjective q
      obtain ⟨x, hx⟩ := hQ z
      rw [hx]
      exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
    let φ := LinearEquiv.toSpanNonzeroSingleton LL _ _ h0
    let inv : ↥Z →ₗ[LL] LL :=
      (φ.symm.toLinearMap.comp (LinearEquiv.ofTop _ htop).symm.toLinearMap).comp B.mkQ
    have hinj : Function.Injective (φ.symm.toLinearMap.comp (LinearEquiv.ofTop _ htop).symm.toLinearMap) :=
      φ.symm.injective.comp (LinearEquiv.ofTop _ htop).symm.injective
    refine ⟨inv, hZ, fun z => ?_⟩
    have e1 : inv z = 0 ↔ B.mkQ z = 0 :=
      (injective_iff_map_eq_zero' _).1 hinj (B.mkQ z)
    rw [e1, ← hB, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

end GlobalTheory.InvLine
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.TateOrth

section Gen
variable {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  {ρ : Representation LL G V}

theorem mem_span_smul_top (L : Lattice (O := O) ρ) (a : O) (x : ↥L.T) :
    x ∈ (Ideal.span {a} • ⊤ : Submodule O ↥L.T) ↔ ∃ y : ↥L.T, x = a • y := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, -, rfl⟩; exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩; exact ⟨y, Submodule.mem_top, rfl⟩

theorem stable_span_smul_top (L : Lattice (O := O) ρ) (a : O) :
    StableSub L (Ideal.span {a} • ⊤ : Submodule O ↥L.T) := by
  intro g x hx
  rw [mem_span_smul_top] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  exact ⟨actT L g y, map_smul _ _ _⟩

theorem factor_actQ (L : Lattice (O := O) ρ) {I J : Submodule O ↥L.T} (hI : StableSub L I)
    (hJ : StableSub L J) (hIJ : I ≤ J) (g : G) (x : ↥L.T ⧸ I) :
    Submodule.factor hIJ (actQ L I hI g x) = actQ L J hJ g (Submodule.factor hIJ x) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective I x
  rfl

theorem factor_mem_Z1Q [TopologicalSpace G] (L : Lattice (O := O) ρ) {I J : Submodule O ↥L.T}
    (hI : StableSub L I) (hJ : StableSub L J) (hIJ : I ≤ J) {z : G → ↥L.T ⧸ I}
    (hz : z ∈ quotientCocycles L I hI) : (fun g => Submodule.factor hIJ (z g)) ∈ quotientCocycles L J hJ := by
  refine ⟨hz.1.comp _, fun g h => ?_⟩
  simp only [hz.2 g h, map_add (f := _), factor_actQ L hI hJ hIJ]

end Gen

theorem mem_BD_of_orthogonal : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ c ∈ divisibleCocycles LA', (∀ d ∈ latticeCocycles LA, CobO (P.PD K) L1 (cupLD LA' m d c)) → c ∈ BD LA' := by
  intro hT l _ P K LL _ _ _ O _ _ hO L1 hL1 A A' LA LA' m hm c hc horth
  obtain ⟨hDom, hDVR, hFrac⟩ := hO.1
  haveI := hDom; haveI := hDVR; haveI := hFrac
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  set π := algebraMap O LL ϖ with hπdef
  have hπ : π ≠ 0 := by
    intro h
    exact hϖ.ne_zero (IsFractionRing.injective O LL (by rw [← hπdef, h, map_zero]))
  by_contra hcB
  obtain ⟨r, hr⟩ := GlobalTheory.T.torsionCocycle_uniformizer_pow_smul_mem l K LL O hO A' LA' ϖ hϖ c hc
  let I : ℕ → Submodule O ↥LA.T := fun k => Ideal.span {ϖ ^ (r + k)} • ⊤
  have hI : ∀ k, StableSub LA (I k) := fun k => stable_span_smul_top LA _
  let Φ : ∀ k, (↥(GK K) → ↥LA.T ⧸ I k) → ↥(GK K) × ↥(GK K) → LL := fun k z x =>
    m (Formalism.MainNotions.LocalSituation.liftQ LA (I k) (z x.1)) (A'.ρ x.1 (liftD LA' (c x.2)))
  let Y : ∀ k, Set (↥(GK K) → ↥LA.T ⧸ I k) := fun k =>
    {z | z ∈ quotientCocycles LA (I k) (hI k) ∧ ¬ CobO (P.PD K) L1 (Φ k z)}
  have hle : ∀ k, I (k + 1) ≤ I k := fun k =>
    Submodule.smul_mono_left (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow ϖ (by omega)))
  have hle0 : ∀ k, I k ≤ I 0 := fun k =>
    Submodule.smul_mono_left (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow ϖ (by omega)))
  let f : ∀ k, (↥(GK K) → ↥LA.T ⧸ I (k + 1)) → (↥(GK K) → ↥LA.T ⧸ I k) := fun k z g =>
    Submodule.factor (hle k) (z g)

  have hmemPow : ∀ (j : ℕ) (x : ↥LA.T), x ∈ (Ideal.span {ϖ ^ j} • ⊤ : Submodule O ↥LA.T) →
      ∃ t ∈ LA.T, (x : A.V) = π ^ j • t := by
    intro j x hx
    obtain ⟨y, rfl⟩ := (mem_span_smul_top LA _ x).1 hx
    exact ⟨y, y.2, by rw [Submodule.coe_smul, hπdef, ← map_pow, algebraMap_smul]⟩
  have hliftMem : ∀ (J : Submodule O ↥LA.T) (x : ↥LA.T ⧸ J), Formalism.MainNotions.LocalSituation.liftQ LA J x ∈ LA.T :=
    fun J x => (Submodule.Quotient.mk_surjective J x).choose.2
  have hspec : ∀ (J : Submodule O ↥LA.T) (x : ↥LA.T ⧸ J), ∃ y : ↥LA.T,
      (y : A.V) = Formalism.MainNotions.LocalSituation.liftQ LA J x ∧ Submodule.Quotient.mk y = x := fun J x =>
    ⟨_, rfl, (Submodule.Quotient.mk_surjective J x).choose_spec⟩
  have hlift2 : ∀ k (x : ↥LA.T ⧸ I k) (y : ↥LA.T), x = Submodule.Quotient.mk y →
      ∃ t ∈ LA.T, Formalism.MainNotions.LocalSituation.liftQ LA (I k) x - (y : A.V) = π ^ (r + k) • t := by
    intro k x y hxy
    obtain ⟨y0, hy0, hmk0⟩ := hspec (I k) x
    have hmem : y0 - y ∈ I k := (Submodule.Quotient.eq _).1 (hmk0.trans hxy)
    obtain ⟨t, ht, he⟩ := hmemPow (r + k) _ hmem
    exact ⟨t, ht, by rw [← hy0, ← he, Submodule.coe_sub]⟩
  have hcong : ∀ (k : ℕ) (a b : A.V) (y : A'.V) (t : A.V), t ∈ LA.T → a - b = π ^ k • t →
      π ^ k • y ∈ LA'.T → m a y - m b y ∈ Set.range (algebraMap O LL) := by
    intro k a b y t ht hab hy
    obtain ⟨e, he⟩ := (hm.2 _).1 hy t ht
    have : m a y - m b y = m t (π ^ k • y) := by
      rw [← LinearMap.sub_apply, ← map_sub, hab, LinearMap.map_smul₂, (m t).map_smul]
    exact ⟨e, by rw [this, he]⟩
  have hcobO : ∀ z z' : ↥(GK K) × ↥(GK K) → LL, (∀ x, z x - z' x ∈ Set.range (algebraMap O LL)) →
      (CobO (P.PD K) L1 z → CobO (P.PD K) L1 z') := by
    intro z z' hzz hz
    have : (fun x => (Submodule.Quotient.mk (z x) : LL ⧸ L1.T)) =
        fun x => Submodule.Quotient.mk (z' x) := by
      funext x
      rw [Submodule.Quotient.eq, hL1]
      obtain ⟨e, he⟩ := hzz x
      exact ⟨e, he⟩
    unfold CobO at hz ⊢
    rwa [← this]
  have hT'pow : ∀ (k : ℕ) (g h : ↥(GK K)), π ^ (r + k) • A'.ρ g (liftD LA' (c h)) ∈ LA'.T := by
    intro k g h
    rw [← map_smul, add_comm, pow_add, mul_smul]
    apply LA'.stable
    rw [hπdef, ← map_pow, algebraMap_smul]
    exact LA'.T.smul_mem _ (hr h)

  have hfin : ∀ k, (Y k).Finite := fun k =>
    (GlobalTheory.T.finite_latticeCocycles_mod_uniformizer_pow hT l K LL O hO A LA ϖ hϖ (r + k) (hI k)).subset (fun z hz => hz.1)
  have hne : ∀ k, (Y k).Nonempty := by
    intro k
    have hI' : StableSub LA' (Ideal.span {ϖ ^ (r + k)} • ⊤ : Submodule O ↥LA'.T) :=
      stable_span_smul_top LA' _
    obtain ⟨c', hc'Z, hc'B, hc'l⟩ :=
      GlobalTheory.T.exists_torsionCocycle_finite_level_lift l K LL O hO A' LA' ϖ hϖ c hc hcB r hr (r + k) (by omega) hI'
    have h2 := (GlobalTheory.T.tate_pairing_lattice_quotients_nondegenerate hT l P K LL O hO L1 hL1 A A' LA LA' m hm ϖ hϖ (r + k) (hI k) hI').2 c' hc'Z
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    apply hc'B
    apply h2
    intro z hz
    have hzY : z ∉ Y k := by rw [hemp]; exact fun h => h
    have hC : CobO (P.PD K) L1 (Φ k z) := by
      by_contra hn; exact hzY ⟨hz, hn⟩
    refine hcobO _ _ ?_ hC
    intro x
    obtain ⟨t, ht, hteq⟩ := hc'l x.2
    obtain ⟨e, he⟩ := (hm.2 _).1 (LA'.stable x.1 t ht) _ (hliftMem (I k) (z x.1))
    refine ⟨-e, ?_⟩
    rw [map_neg, ← he]
    simp only [Φ, hteq, map_add (f := _), map_smul, smul_eq_mul, ← hπdef]
    rw [inv_pow]
    field_simp
    ring
  have hmap : ∀ k, ∀ z ∈ Y (k + 1), f k z ∈ Y k := by
    rintro k z ⟨hz, hnc⟩
    refine ⟨factor_mem_Z1Q LA (hI (k + 1)) (hI k) (hle k) hz, fun hc' => hnc (hcobO _ _ ?_ hc')⟩
    intro x
    obtain ⟨t, ht, hteq⟩ := hlift2 k (f k z x.1) ⟨_, hliftMem (I (k + 1)) (z x.1)⟩ (by
      obtain ⟨y0, hy0, hmk0⟩ := hspec (I (k + 1)) (z x.1)
      have hy : (⟨_, hliftMem (I (k + 1)) (z x.1)⟩ : ↥LA.T) = y0 := Subtype.ext hy0.symm
      rw [hy]
      show Submodule.factor (hle k) (z x.1) = _
      rw [← hmk0]
      rfl)
    exact hcong (r + k) _ _ _ t ht hteq (hT'pow k x.1 x.2)
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_compatible_seq_of_finite_nonempty' (fun k => ↥(GK K) → ↥LA.T ⧸ I k) f Y hfin hne hmap
  let w : ℕ → ↥(GK K) → ↥LA.T := fun k g => (Submodule.Quotient.mk_surjective (I k) (s k g)).choose
  have hwk : ∀ k g, (Submodule.Quotient.mk (w k g) : ↥LA.T ⧸ I k) = s k g := fun k g =>
    (Submodule.Quotient.mk_surjective (I k) (s k g)).choose_spec
  have hI'I : ∀ k, I k ≤ (Ideal.span {ϖ ^ k} • ⊤ : Submodule O ↥LA.T) := fun k =>
    Submodule.smul_mono_left (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow ϖ (by omega)))
  have hI' : ∀ n : ℕ, StableSub LA (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T) := fun n =>
    stable_span_smul_top LA _
  have hwZ : ∀ n, (fun g => (Submodule.Quotient.mk (w n g) :
      ↥LA.T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T))) ∈ quotientCocycles LA _ (hI' n) := by
    intro n
    have := factor_mem_Z1Q LA (hI n) (hI' n) (hI'I n) (hs n).1.1
    convert this using 1
    funext g
    rw [← hwk n g]
    rfl
  have hstep : ∀ k g, w (k + 1) g - w k g ∈ I k := by
    intro k g
    apply (Submodule.Quotient.eq _).1
    rw [hwk k g, ← (hs k).2]
    show _ = Submodule.factor (hle k) (s (k + 1) g)
    rw [← hwk (k + 1) g]
    rfl
  obtain ⟨d, hdZ, hd⟩ := GlobalTheory.T.exists_limit_cocycle_of_compatible_mod_pow l K LL O hO A LA ϖ hϖ hI' w hwZ (fun n g => hI'I n (hstep n g))
  have htele : ∀ n g, w n g - w 0 g ∈ I 0 := by
    intro n g
    induction n with
    | zero => simp
    | succ n ih =>
      have := (I 0).add_mem (hle0 n (hstep n g)) ih
      rwa [sub_add_sub_cancel] at this
  apply (hs 0).1.2
  refine hcobO _ _ ?_ (horth d hdZ)
  intro x
  obtain ⟨t1, ht1, hdt⟩ := hd r x.1
  have he : t1 + (w r x.1 - w 0 x.1) ∈ I 0 := (I 0).add_mem ht1 (htele r x.1)
  obtain ⟨u, hu, hue⟩ := hmemPow (r + 0) _ he
  obtain ⟨t3, ht3, ht3e⟩ := hlift2 0 (s 0 x.1) (w 0 x.1) (hwk 0 x.1).symm
  refine hcong (r + 0) _ _ _ (u - t3) (LA.T.sub_mem hu ht3) ?_ (hT'pow 0 x.1 x.2)
  rw [smul_sub, ← hue, ← ht3e, hdt]
  simp only [Submodule.coe_add, Submodule.coe_sub]
  abel

end GlobalTheory.TateOrth
end

section

open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical

namespace GlobalTheory


open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial in
open scoped ContDiff Classical in
theorem _root_.GlobalTheory.not_forall_exists_two_liesOver_absNorm_eq :
    ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] (S : Set (HeightOneSpectrum (𝓞 K))), S.Finite → ¬ ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∃ P P' : HeightOneSpectrum (𝓞 M), P ≠ P' ∧ P.asIdeal.LiesOver v.asIdeal ∧ P'.asIdeal.LiesOver v.asIdeal ∧ Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal ∧ Ideal.absNorm P'.asIdeal = Ideal.absNorm v.asIdeal := by
  intro K M _ _ _ _ _ S hS h
  choose P P' hne hP hP' hNP hNP' using h
  have key : ∀ {Q : HeightOneSpectrum (𝓞 M)} {v w : HeightOneSpectrum (𝓞 K)},
      Q.asIdeal.LiesOver v.asIdeal → Q.asIdeal.LiesOver w.asIdeal → v = w :=
    fun h₁ h₂ => HeightOneSpectrum.ext (h₁.over.trans h₂.over.symm)
  let f : {v // v ∉ S} × Bool → HeightOneSpectrum (𝓞 M) :=
    fun x => if x.2 then P x.1 x.1.2 else P' x.1 x.1.2
  have lies : ∀ x, (f x).asIdeal.LiesOver x.1.1.asIdeal := by
    rintro ⟨⟨v, hv⟩, b⟩
    cases b
    exacts [hP' v hv, hP v hv]
  refine _root_.GlobalTheory.Mem.ZetaPole.not_injective_double_primes K M S hS f ?_ ?_
  · rintro ⟨⟨v, hv⟩, b⟩ ⟨⟨w, hw⟩, c⟩ hfe
    have hvw : v = w := key (lies (⟨v, hv⟩, b)) (by rw [hfe]; exact lies _)
    subst hvw
    cases b <;> cases c
    · rfl
    · exact absurd hfe.symm (hne v hv)
    · exact absurd hfe (hne v hv)
    · rfl
  · rintro ⟨⟨v, hv⟩, b⟩
    cases b
    exacts [hNP' v hv, hNP v hv]

end GlobalTheory
end

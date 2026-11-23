module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChartNonempty
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StabOrd
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle341
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle087
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle086
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle263
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle272
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle352
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle128
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle226
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle180
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle168
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotInhAbsOfGamLe
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle046
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle148
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle042
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle321
import Formalism.PadicSubsetSums.StableGradedCounts.Bundle003
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

noncomputable section
namespace GlobalTheory.ChartReps

section Gen
variable {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
  (S : StepLevel D.host.F D.host.E (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) T f bad) {cl : Type}
  (y : cl → UPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
  (U : Subgroup (GA D V)) (hU : ∀ g, g ∈ U ↔ g ∈ GfC V ∧ ∃ κ : S.U, κ.1.1 = finM V hn g)
  (h : cl → GA D V) (hh : ∀ c, h c ∈ GfC V ∧ finM V hn (h c) = (y c).1.1)

def finHomN : GA D V →* GL (Fin n) (EF D) where
  toFun g := GlobalTheory.AdForm.Model.finGL V hn g
  map_one' := Units.ext (GlobalTheory.AdForm.Model.finM_one V hn)
  map_mul' g g' := Units.ext (GlobalTheory.AdForm.Model.finM_mul V hn g g')

theorem finHomN_val (g : GA D V) : (finHomN V hn g).1 = finM V hn g := rfl

theorem finHomN_eq_one (g : GA D V) : finHomN V hn g = 1 ↔ g ∈ GinfC V := by
  rw [Units.ext_iff, finHomN_val, Units.val_one, GlobalTheory.AdForm.finM_eq_one_iff_mem_GinfC D V n hn g]


include hU in
theorem lift_mem (e : ↥(GfC V) ≃* ↥(UPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
    (he : ∀ g, (e g).1.1 = finM V hn g.1) (κ : S.U) :
    (e.symm ⟨κ.1, ((S.U_eq κ.1).1 κ.2).1⟩).1 ∈ U ∧ finM V hn (e.symm ⟨κ.1, ((S.U_eq κ.1).1 κ.2).1⟩).1 = κ.1.1 := by
  have h1 : finM V hn (e.symm ⟨κ.1, ((S.U_eq κ.1).1 κ.2).1⟩).1 = κ.1.1 := by rw [← he, e.apply_symm_apply]
  exact ⟨(hU _).2 ⟨(e.symm _).2, κ, h1.symm⟩, h1⟩


include hU hh in

theorem reps_of_chart (hy : Function.Bijective (fun c => (Quotient.mk'' (y c) : Cls S))) : IsReps V U h := by
  letI := tensTopL (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
  obtain ⟨e, he⟩ := GlobalTheory.FinPartIso.exists_finIso D V n hn
  obtain ⟨r, hr⟩ := GlobalTheory.RatPtsEquiv.rat_equiv D V n hn
  have hmemU : ∀ (g : GfC V), g.1 ∈ U ↔ (e g).1 ∈ S.U := by
    intro g
    rw [hU]
    constructor
    · rintro ⟨_, κ, hκ⟩
      have : (e g).1 = κ.1 := Units.ext ((he g).trans hκ.symm)
      rw [this]; exact κ.2
    · intro hx; exact ⟨g.2, ⟨(e g).1, hx⟩, he g⟩
  have hΦe : ∀ g : GfC V, finHomN V hn g.1 = (e g).1 := fun g => Units.ext (he g).symm
  refine ⟨fun g hg => ((hU g).1 hg).1, ?_, ?_, fun c => (hh c).1, ?_, ?_⟩
  · have hset : (U : Set (GA D V)) = (fun x => (e.symm x).1) '' {x | x.1 ∈ S.U} := by
      ext g
      constructor
      · intro hg
        have hgf := ((hU g).1 hg).1
        exact ⟨e ⟨g, hgf⟩, (hmemU ⟨g, hgf⟩).1 hg, by simp only [e.symm_apply_apply]⟩
      · rintro ⟨x, hx, rfl⟩
        exact (hmemU _).2 (by rw [e.apply_symm_apply]; exact hx)
    have hc : IsCompact {x : ↥(UPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) | x.1 ∈ S.U} := by
      rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
      convert S.U_compact using 1
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩; exact hx
      · intro hz; exact ⟨⟨z, ((S.U_eq z).1 hz).1⟩, hz, rfl⟩
    rw [hset]
    exact hc.image (continuous_subtype_val.comp e.symm.continuous)
  · have : ((U.subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V)) = e ⁻¹' {x | x.1 ∈ S.U} := by
      ext g
      exact (Subgroup.mem_subgroupOf).trans (hmemU g)
    rw [this]
    exact S.U_open.preimage e.continuous
  · intro g
    obtain ⟨p, hpq⟩ : ∃ p : GinfC V × GfC V, g = p.1.1 * p.2.1 :=
      ⟨(GlobalTheory.AdelicSplit.splitEquiv V).symm g, ((GlobalTheory.AdelicSplit.splitEquiv V).apply_symm_apply g).symm⟩
    obtain ⟨⟨c, δ, κ0⟩, hδ, hdec⟩ := GlobalTheory.AdForm.Model.exists_dec V hn S y hy.2 p.2.1
    obtain ⟨κ, hκU, hκf⟩ : ∃ κ ∈ U, finM V hn κ = κ0.1.1 :=
      ⟨_, (lift_mem V hn S U hU e.toMulEquiv he κ0).1, (lift_mem V hn S U hU e.toMulEquiv he κ0).2⟩
    obtain ⟨γ, hγ, hΦγ⟩ : ∃ γ ∈ GQ V, finHomN V hn γ = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) δ := by
      refine ⟨(r.symm ⟨δ, hδ⟩).1, (r.symm ⟨δ, hδ⟩).2, ?_⟩
      apply Units.ext
      have h1 := hr (r.symm ⟨δ, hδ⟩)
      rw [MulEquiv.apply_symm_apply] at h1
      exact h1
    refine ⟨γ, hγ, c, (h c)⁻¹ * γ⁻¹ * g * κ⁻¹, ?_, κ, hκU, by group⟩
    rw [← finHomN_eq_one V hn]
    have e1 : finHomN V hn g = finHomN V hn p.2.1 := by
      rw [hpq, map_mul, (finHomN_eq_one V hn _).2 p.1.2, one_mul]
    have e2 : finHomN V hn p.2.1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) δ * (y c).1 * κ0.1 :=
      Units.ext (by rw [finHomN_val, hdec])
    have e3 : finHomN V hn (h c) = (y c).1 := Units.ext (by rw [finHomN_val, (hh c).2])
    have e4 : finHomN V hn κ = κ0.1 := Units.ext (by rw [finHomN_val, hκf])
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, map_inv, e1, e2, e3, e4, hΦγ]
    group
  · intro c c' γ hγ k hk κ hκ heq
    obtain ⟨_, κ0, hκ0⟩ := (hU κ).1 hκ
    have hΦγ : finHomN V hn γ = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (r ⟨γ, hγ⟩).1 :=
      Units.ext (by rw [finHomN_val, hr ⟨γ, hγ⟩])
    have e3 : ∀ c, finHomN V hn (h c) = (y c).1 := fun c => Units.ext (by rw [finHomN_val, (hh c).2])
    have e4 : finHomN V hn κ = κ0.1 := Units.ext (by rw [finHomN_val, ← hκ0])
    have key : (y c').1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (r ⟨γ, hγ⟩).1 * (y c).1 * κ0.1 := by
      rw [← e3, ← e3, heq, ← e4, ← hΦγ]
      simp only [map_mul, (finHomN_eq_one V hn k).2 hk, mul_one]
    have hmemγ : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (r ⟨γ, hγ⟩).1 ∈
        UPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
      rw [← hΦγ]; exact GlobalTheory.AdForm.Model.finGL_mem V hn γ
    apply hy.1
    show (Quotient.mk'' (y c) : Cls S) = Quotient.mk'' (y c')
    refine (@DoubleCoset.eq _ _ _ _ _ _).2 ⟨⟨_, hmemγ⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_map_of_mem _ (r ⟨γ, hγ⟩).2),
      ⟨κ0.1, ((S.U_eq κ0.1).1 κ0.2).1⟩, Subgroup.mem_subgroupOf.2 κ0.2, Subtype.ext key⟩

end Gen

section Gen2
variable {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
  (S : StepLevel D.host.F D.host.E (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) T f bad) {cl : Type}
  (y : cl → UPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
  (U : Subgroup (GA D V)) (hU : ∀ g, g ∈ U ↔ g ∈ GfC V ∧ ∃ κ : S.U, κ.1.1 = finM V hn g)
  (h : cl → GA D V) (hh : ∀ c, h c ∈ GfC V ∧ finM V hn (h c) = (y c).1.1)


include hU hh in

theorem stabOrd_of_chart {stab : cl → Type} [∀ c, Group (stab c)]
    (stabI : ∀ c, stab c →* UJ (sigD D : D.host.E →+* D.host.E) (V.gram.reindex (finCongr hn) (finCongr hn)))
    (hinj : ∀ c, Function.Injective (stabI c))
    (hran : ∀ c (γ : UJ (sigD D : D.host.E →+* D.host.E) (V.gram.reindex (finCongr hn) (finCongr hn))),
      γ ∈ (stabI c).range ↔ bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 ∈
        S.U.map (MulAut.conj (y c).1).toMonoidHom)
    (c : cl) : stabOrd U (h c) = Nat.card (stab c) := by
  letI := tensTopL (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
  obtain ⟨e, he⟩ := GlobalTheory.FinPartIso.exists_finIso D V n hn
  obtain ⟨r, hr⟩ := GlobalTheory.RatPtsEquiv.rat_equiv D V n hn
  have hΦγ : ∀ γ : GQ V, finHomN V hn γ.1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (r γ).1 :=
    fun γ => Units.ext (hr γ)
  have e3 : finHomN V hn (h c) = (y c).1 := Units.ext (by rw [finHomN_val, (hh c).2])
  have hcond : ∀ γ : GQ V, (∃ k ∈ GinfC V, ∃ κ ∈ U, γ.1 * h c = h c * k * κ) ↔ r γ ∈ (stabI c).range := by
    intro γ
    rw [hran]
    constructor
    · rintro ⟨k, hk, κ, hκ, heq⟩
      obtain ⟨_, κ0, hκ0⟩ := (hU κ).1 hκ
      have e4 : finHomN V hn κ = κ0.1 := Units.ext (by rw [finHomN_val, ← hκ0])
      have key := congrArg (finHomN V hn) heq
      rw [map_mul, map_mul, map_mul, hΦγ, e3, e4, (finHomN_eq_one V hn k).2 hk, mul_one] at key
      refine Subgroup.mem_map.2 ⟨κ0.1, κ0.2, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← key]
      group
    · intro hmem
      obtain ⟨κ1, hκ1, hconj⟩ := Subgroup.mem_map.1 hmem
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hconj
      obtain ⟨κ, hκU, hκf⟩ : ∃ κ ∈ U, finM V hn κ = κ1.1 :=
        ⟨_, (lift_mem V hn S U hU e.toMulEquiv he ⟨κ1, hκ1⟩).1, (lift_mem V hn S U hU e.toMulEquiv he ⟨κ1, hκ1⟩).2⟩
      have e4 : finHomN V hn κ = κ1 := Units.ext (by rw [finHomN_val, hκf])
      refine ⟨(h c)⁻¹ * γ.1 * h c * κ⁻¹, ?_, κ, hκU, by group⟩
      rw [← finHomN_eq_one V hn, map_mul, map_mul, map_mul, map_inv, map_inv, hΦγ, e3, e4, ← hconj]
      group
  unfold stabOrd
  rw [Nat.card_congr (r.toEquiv.subtypeEquiv hcond)]
  exact (Nat.card_congr (MonoidHom.ofInjective (hinj c)).toEquiv).symm

end Gen2



theorem twDat_reps : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i ≤ B.R.m) β, IsReps ((I.rec7 l Z).sp.X i) (A.U i β) (A.h i β) ∧ (Continuous fun κ => ((A.chi i β κ : ℂˣ) : ℂ)) ∧ ∀ c, stabOrd (A.U i β) (A.h i β c) = Nat.card ((I.chain l u a).stab i c.1) := by
  intro B X I hOk hP l Z u a Ch A hA i hi β
  exact ⟨reps_of_chart _ (rankN (I.rec7 l Z) i hi) (A.K i hi β).lev (A.K i hi β).y (A.U i β) (hA.U i hi β) (A.h i β)
      (hA.h i hi β) (A.K i hi β).y_bij,
    GlobalTheory.T.continuous_chartLevelCharacters_adelic_tuple I hOk hP l Z u a Ch A hA i hi β,
    fun c => stabOrd_of_chart _ (rankN (I.rec7 l Z) i hi) (A.K i hi β).lev (A.K i hi β).y (A.U i β) (hA.U i hi β) (A.h i β)
      (hA.h i hi β) (A.K i hi β).stabI (A.K i hi β).stabI_inj (A.K i hi β).stabI_range c⟩

end GlobalTheory.ChartReps
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.SeeSaw.CenFockPf

variable {D : D7}

theorem thPair_smul_smul {m n : ℕ} (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)) (a b : ℂ) (f g : Mx D m n → ℂ) :
    thPair μ 𝓕 (a • f) (b • g) = (a * star b) * thPair μ 𝓕 f g := by
  unfold thPair
  rw [← integral_const_mul]
  congr 1; funext w
  simp only [Pi.smul_apply, smul_eq_mul, star_mul']
  ring

theorem heisO_sub (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) (f g : WO S T → ℂ) :
    heisO ψ S T u (f - g) = heisO ψ S T u f - heisO ψ S T u g := by
  funext w; simp only [heisO, Pi.sub_apply]; ring

theorem isLatVac_sub (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {Λ : AddSubgroup (WO S T)} {f g : WO S T → ℂ}
    (hf : IsLatVac (heisO ψ S T) Λ f) (hg : IsLatVac (heisO ψ S T) Λ g) : IsLatVac (heisO ψ S T) Λ (f - g) :=
  ⟨fun u hu => by rw [heisO_sub, hf.1 u hu, hg.1 u hu],
    fun e he u hu hh => by rw [heisO_sub, hf.2 e he u hu hh, hg.2 e he u hu hh]⟩

theorem comb_single_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ) :
    comb ψ S T (Finsupp.single 0 1) f = f := by
  unfold comb
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same, one_smul]
  funext w
  simp [heisO, symplOH, symplO, hO]

theorem isFinComb_single_zero (S T : HSp D) : IsFinComb (Finsupp.single (0 : WO S T) (1 : ℂ)) := by
  intro u hu
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hu
  subst hu
  ext i j; simp

section Pair

variable {m n : ℕ} (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n))

theorem thPair_sum_right {ι : Type} (s : Finset ι) (a : ι → ℂ) (g : Mx D m n → ℂ) (h : ι → Mx D m n → ℂ)
    (hi : ∀ i, Integrable (fun w => g w * star (h i w)) (μ.restrict 𝓕)) :
    thPair μ 𝓕 g (∑ i ∈ s, a i • h i) = ∑ i ∈ s, star (a i) * thPair μ 𝓕 g (h i) := by
  unfold thPair
  have e : ∀ w, g w * star ((∑ i ∈ s, a i • h i) w) = ∑ i ∈ s, star (a i) * (g w * star (h i w)) := by
    intro w
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, star_sum, star_mul', Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [e]
  rw [integral_finsetSum _ fun i _ => (hi i).const_mul _]
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

theorem thPair_sub_sum_left {ι : Type} (s : Finset ι) (a : ι → ℂ) (f g : Mx D m n → ℂ) (h : ι → Mx D m n → ℂ)
    (hf : Integrable (fun w => f w * star (g w)) (μ.restrict 𝓕))
    (hi : ∀ i, Integrable (fun w => h i w * star (g w)) (μ.restrict 𝓕)) :
    thPair μ 𝓕 (f - ∑ i ∈ s, a i • h i) g = thPair μ 𝓕 f g - ∑ i ∈ s, a i * thPair μ 𝓕 (h i) g := by
  unfold thPair
  have e : ∀ w, (f - ∑ i ∈ s, a i • h i) w * star (g w) = f w * star (g w) - ∑ i ∈ s, a i * (h i w * star (g w)) := by
    intro w
    simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [e]
  rw [integral_sub hf (integrable_finsetSum _ fun i _ => (hi i).const_mul _),
    integral_finsetSum _ fun i _ => (hi i).const_mul _]
  congr 1
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

end Pair

theorem exists_orth_coeff {X : Type} [MeasurableSpace X] (ν : Measure X) {ι : Type} [Fintype ι] (f : X → ℂ) (h : ι → X → ℂ)
    (hf : MemLp f 2 ν) (hh : ∀ i, MemLp (h i) 2 ν) :
    ∃ c : ι → ℂ, ∀ j, ∫ w, f w * star (h j w) ∂ν = ∑ i, c i * ∫ w, h i w * star (h j w) ∂ν := by
  have ip : ∀ (a b : X → ℂ) (ha : MemLp a 2 ν) (hb : MemLp b 2 ν),
      inner ℂ (hb.toLp b) (ha.toLp a) = ∫ w, a w * star (b w) ∂ν := by
    intro a b ha hb
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with w h1 h2
    rw [h1, h2]
    simp
  let H : ι → Lp ℂ 2 ν := fun i => (hh i).toLp (h i)
  let K : Submodule ℂ (Lp ℂ 2 ν) := Submodule.span ℂ (Set.range H)
  haveI : FiniteDimensional ℂ K := FiniteDimensional.span_of_finite ℂ (Set.finite_range H)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (K.starProjection_apply_mem (hf.toLp f))
  refine ⟨c, fun j => ?_⟩
  have h0 := (Submodule.mem_orthogonal K _).1 (K.sub_starProjection_mem_orthogonal (hf.toLp f)) (H j)
    (Submodule.subset_span ⟨j, rfl⟩)
  rw [← hc, inner_sub_right, inner_sum, sub_eq_zero] at h0
  rw [← ip f (h j) hf (hh j)]
  refine h0.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [inner_smul_right, ← ip (h i) (h j) (hh i) (hh j)]

theorem isLatVac_pureTensorO {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {x : DefSp S} {y : DefSp T}
    {f₀ : WO S T → ℂ} (hvac : IsVacO ψ θ S T x.s y.s x.L y.L f₀) (φ : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    IsLatVac (heisO ψ S T) (latO S T x.L y.L fun _ => True) (pureTensorO ψ θ S T x.s y.s x.B y.B f₀ φ) := by
  have hth : ∀ φ, IsThetaFunO ψ S T (pureTensorO ψ θ S T x.s y.s x.B y.B f₀ φ) := fun φ =>
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO hvac.1 hvac.2.inf x.s x.B y.s y.B hvac.2.theta φ
  refine ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩
  · exact GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite ψ θ S T hvac.2.inf x.s y.s x.B y.B f₀ hth (2 • u)
      (GlobalTheory.VacGood.infPart_latO (AddSubgroup.nsmul_mem _ hu 2)) (hvac.2.lat.1 u hu) φ
  · exact GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite ψ θ S T hvac.2.inf x.s y.s x.B y.B f₀ hth u
      (GlobalTheory.VacGood.infPart_latO hu) (hvac.2.lat.2 e he u hu hh) φ

theorem thPair_eq_zero_of_eigen {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χ χ' : (AE D)ˣ →* Circle} {om : Om S T}
    (hW : IsWeilDatumO ψ S T χ χ' om) (v : VolM D T.rank S.rank) (p : GA D S × GA D T) {f g : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) {a b : ℂ} (ha : om p f = a • f) (hb : om p g = b • g)
    (hb1 : ‖b‖ = 1) (hab : b ≠ a) : thPair v.μ v.𝓕 f g = 0 := by
  have h := GlobalTheory.WeilPairing.thPair_om_eq D ψ S T χ χ' om hW v p f g hf hg
  rw [ha, hb] at h
  have h' := (thPair_smul_smul v.μ v.𝓕 a b f g).symm.trans h
  have hbb : star b * b = 1 := by
    have := Complex.conj_mul' b
    rw [hb1] at this
    simpa using this
  have : (a - b) * thPair v.μ v.𝓕 f g = 0 := by
    linear_combination b * h' - a * thPair v.μ v.𝓕 f g * hbb
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hab.symm)

theorem cenFock : ∀ D : D7, CenFock D := by
  intro D ψ θ hθ S T x y hx hy k hk χ
  classical
  obtain ⟨wt, hwt, hfin⟩ := GlobalTheory.T.exists_unit_weight_real_center_action_fock_monomial D ψ θ hθ S T x y hx hy k hk
  obtain ⟨χS, χT, hW⟩ := hk.weil
  obtain ⟨v⟩ := (GlobalTheory.Unf.VolExist.measures_exist D).2.2.1 T.rank S.rank
  set pt := pureTensorO ψ θ S T x.s y.s x.B y.B k.vac with hpt
  have hth : ∀ φ, IsThetaFunO ψ S T (pt φ) := fun φ =>
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO hk.vac.1 hθ x.s x.B y.s y.B hk.vac.2.theta φ
  have heig : ∀ α, ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) →
      k.om (z, 1) (pt (MvPolynomial.monomial α 1)) = wt α z • pt (MvPolynomial.monomial α 1) := by
    intro α z hz hzc
    have := (hwt α z hz hzc).2 _ (isFinComb_single_zero S T)
    rwa [comb_single_zero] at this
  have hL2 : ∀ {g : WO S T → ℂ}, IsThetaFunO ψ S T g → MemLp g 2 (v.μ.restrict v.𝓕) := fun hg =>
    GlobalTheory.Size.memLp_theta hk.vac.1 v.covol.1 v.covol.2.1 hg
  have hint : ∀ {g g' : WO S T → ℂ}, IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' →
      Integrable (fun w => g w * star (g' w)) (v.μ.restrict v.𝓕) := fun hg hg' =>
    GlobalTheory.Size.integrableOn_mul_conj hk.vac.1 v.covol.1 v.covol.2.1 hg hg'
  set A := (hfin χ).toFinset with hA
  have hmem : ∀ α, α ∈ A ↔ ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → wt α z = χ z := fun α => by
    rw [hA, Set.Finite.mem_toFinset]; rfl
  let mon : A → PolF D T.rank S.rank := fun α => MvPolynomial.monomial α.1 1
  refine ⟨Submodule.span ℂ (Set.range mon), FiniteDimensional.span_of_finite ℂ (Set.finite_range mon), ?_⟩
  intro f hf hlat hχ
  obtain ⟨c, hc⟩ := exists_orth_coeff (v.μ.restrict v.𝓕) f (fun α : A => pt (mon α)) (hL2 hf) (fun α => hL2 (hth _))
  refine ⟨∑ α, c α • mon α, (Submodule.mem_span_range_iff_exists_fun ℂ).2 ⟨c, rfl⟩, ?_⟩
  have hg := GlobalTheory.OrientedHeis.theta_sub hf (hth (∑ α, c α • mon α))
  have hgl := isLatVac_sub ψ S T hlat (isLatVac_pureTensorO hk.vac (∑ α, c α • mon α))
  have hsum : pt (∑ α, c α • mon α) = ∑ α, c α • pt (mon α) := by simp only [map_sum, map_smul]
  have hmono : ∀ β, thPair v.μ v.𝓕 (f - pt (∑ α, c α • mon α)) (pt (MvPolynomial.monomial β 1)) = 0 := by
    intro β
    rw [hsum]
    refine (thPair_sub_sum_left v.μ v.𝓕 Finset.univ c f _ (fun α => pt (mon α)) (hint hf (hth _))
      (fun α => hint (hth _) (hth _))).trans ?_
    by_cases hβ : β ∈ A
    · exact sub_eq_zero.2 (hc ⟨β, hβ⟩)
    · rw [hmem] at hβ
      push_neg at hβ
      obtain ⟨z, hz, hzc, hne⟩ := hβ
      rw [thPair_eq_zero_of_eigen hW v (z, 1) hf (hth _) (hχ z hz hzc) (heig β z hz hzc) (hwt β z hz hzc).1 hne, zero_sub,
        neg_eq_zero]
      refine Finset.sum_eq_zero fun α _ => ?_
      rw [thPair_eq_zero_of_eigen hW v (z, 1) (hth _) (hth _) (heig α.1 z hz hzc) (heig β z hz hzc) (hwt β z hz hzc).1
        (by rw [(hmem α.1).1 α.2 z hz hzc]; exact hne), mul_zero]
  refine sub_eq_zero.1 (GlobalTheory.FockTotal.eq_zero_of_orth_fock D ψ θ hθ S T x y hx hy k.vac hk.vac v _ hg hgl fun Q => ?_)
  have hQ : pt Q = ∑ β ∈ Q.support, AddMonoidAlgebra.coeff Q β • pt (MvPolynomial.monomial β 1) := by
    conv_lhs => rw [Q.as_sum]

    rw [map_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [← map_smul, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  show thPair v.μ v.𝓕 (f - pt (∑ α, c α • mon α)) (pt Q) = 0
  rw [hQ]
  refine (thPair_sum_right v.μ v.𝓕 Q.support (fun β => AddMonoidAlgebra.coeff Q β) _
    (fun β => pt (MvPolynomial.monomial β 1)) (fun β => hint hg (hth _))).trans ?_
  exact Finset.sum_eq_zero fun β _ => by rw [hmono, mul_zero]

end GlobalTheory.SeeSaw.CenFockPf
end

section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MiTop

open GlobalTheory.Core.Rk

theorem trueE_of_trueD {D : D7} (h : TrueD D) : TrueE D :=
  let ⟨B, X, I, l, Z, e, ⟨w⟩⟩ := h; ⟨B, X, I, l, Z, e, w, w.S.pin⟩

theorem puNZ_at (D : D7) (u : D.what₂.Word) (e δ : ℝ) (hS : DiagS D u e) (hR : RamBig D u δ) (hlt : e < 1 - δ)
    (hd : 0 < d0 D u) : ∃ φ : (D.mem u).A.Mram, D.s.Pu u ((D.s_Cu u).symm ⟨φ.1, φ.2.1⟩) ≠ 0 := by
  by_contra hne
  push_neg at hne
  let FF : (D.mem u).A.Mram →ₗ[ℂ] D.s.Cu u :=
    (D.s_Cu u).symm.toLinearMap ∘ₗ Submodule.inclusion (inf_le_left : (D.mem u).A.Mram ≤ (D.mem u).A.Mu0)
  have hFF : Function.Injective FF := (D.s_Cu u).symm.injective.comp (Submodule.inclusion_injective _)
  have hle : Module.finrank ℂ (D.mem u).A.Mram ≤
      Module.finrank ℂ (LinearMap.ker (D.s.Pu u : D.s.Cu u →ₗ[ℂ] D.s.HH)) := by
    let g : (D.mem u).A.Mram →ₗ[ℂ] LinearMap.ker (D.s.Pu u : D.s.Cu u →ₗ[ℂ] D.s.HH) :=
      FF.codRestrict _ (fun φ => by rw [LinearMap.mem_ker]; exact hne φ)
    exact LinearMap.finrank_le_finrank_of_injective (f := g) (fun x y h => hFF (congrArg Subtype.val h))
  have hk := finrank_ker_Pu_le_hsDev D u
  obtain ⟨-, hbig⟩ := hR
  have hU : (GlobalTheory.Core.Rk.dU D u : ℝ) ≤ (Module.finrank ℂ (LinearMap.ker (D.s.Pu u : D.s.Cu u →ₗ[ℂ] D.s.HH)) : ℝ) := by
    unfold GlobalTheory.Core.Rk.dU; exact_mod_cast hle
  have hd' : (0 : ℝ) < (d0 D u : ℝ) := by exact_mod_cast hd
  unfold DiagS at hS
  have : (1 - δ) * (d0 D u : ℝ) ≤ e * (d0 D u : ℝ) := by linarith
  have := le_of_mul_le_mul_right this hd'
  linarith

theorem puNZ_of_sDiag {D : D7} (large₂ : SizeData₂ D) {C C' Cl Cg cb Cu cT CT : ℝ} (hC : 1 ≤ C) (hCG : C + 1 ≤ large₂.CGam) (hD : TrueD D)
    (hH : GlobalTheory.Core.Rk.HD D large₂.sc.L C' Cl Cg cb Cu cT CT) (hmu : ∀ u, RankMu D u) (hS : ∀ u, SDiag D u large₂.sc.L C) : PuNZ D := by
  intro u
  obtain ⟨hm, hT, hd, -⟩ := hd_numbers D u _ C' Cl Cg cb Cu cT CT hH
  have hG : Real.log (D.mem u).A.GamP = large₂.CGam * mfL D large₂.sc.L := by rw [large₂.Gam_eq u]; unfold mfL; ring
  have hw : 1 + 2 * C * mfL D large₂.sc.L ≤ 2 * Real.log (D.mem u).A.GamP := by rw [hG]; nlinarith
  have hCm : 5 ≤ C * mfL D large₂.sc.L := by nlinarith
  have hdiag := diag_corollary.2.1 D u _ C (by linarith) (hS u) ((levelPrime_window D u).2.2 _ C (hmu u) hw)
  have hf : D.R.f ≠ 0 := by
    intro h0
    unfold mfL at hm
    rw [h0] at hm
    norm_num at hm
  have hR := ramBig_of_ramShare D u (ramShare_of_trueD D u hD) hd (by omega)
  have h2 := two_eDiag_lt D u _ C hCm hT
  have h0 : 0 ≤ eDiag D large₂.sc.L C := by unfold eDiag; positivity
  exact puNZ_at D u _ _ hdiag hR (by linarith) hd

theorem evP_cGam (J : ℝ → ℝ → ℝ) : EvP fun κ _ => J (κ.C.P.CYL + 1) κ.C.CTu ≤ κ.C.CGam :=
  ⟨1, one_pos, fun _ _ _ _ _ _ _ _ _ =>
    ⟨⟨0, fun _ => 0, fun l => J (l.getD 6 0 + 1) (l.getD 13 0), fun _ => 0⟩, fun C _ _ hL =>
      ⟨0, fun _ _ => ⟨0, fun _ _ _ => ⟨0, fun _ _ _ => hL.2.2.1 C.CGam (by simp [Formalism.MainNotions.Inhab.FC.cMid])⟩⟩⟩⟩⟩

end GlobalTheory.MiTop
end

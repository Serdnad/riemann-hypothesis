module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle693
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle692
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle387
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle305
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle690
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle306
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle694
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatSchwartzLinear
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle324
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle481
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsPreserveThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle196
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1545
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle328
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle012
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle143
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle469

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rowTest_support_families_staircase_cosets : Big fun ch => OneAt ch := by
  first | exact @GlobalTheory.RowVal.oneAt | exact GlobalTheory.RowVal.oneAt | (intros; apply GlobalTheory.RowVal.oneAt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.CellMass

noncomputable section

namespace GlobalTheory.RowGrpSemi

theorem finite_split {X Y : Type} [Group X] [TopologicalSpace X] [Group Y] [TopologicalSpace Y]
    (Xf : Subgroup X) (Yf : Subgroup Y) (N R K : Subgroup X) (s : Y →* X) (p : R → Y)
    (hR : R = N ⊔ s.range) (hconj : ∀ n ∈ N, ∀ h, s h * n * (s h)⁻¹ ∈ N) (hs : Continuous s) (hp : Continuous p)
    (hpn : ∀ n ∈ N, ∀ h (hm : n * s h ∈ R), p ⟨n * s h, hm⟩ = h) (hsf : ∀ y ∈ Yf, s y ∈ Xf)
    (hkey : ∀ n ∈ N, ∀ h, n * s h ∈ Xf → h ∈ Yf) (hK : K ≤ Xf) :
    ∃ (π : R.subgroupOf Xf →* Yf) (σ : Yf →* R.subgroupOf Xf),
      Continuous π ∧ Continuous σ ∧ (∀ y, π (σ y) = y) ∧ (∀ r, π r = 1 ↔ r.1 ∈ N.subgroupOf Xf) ∧
      ∀ b : Xf, {g : Yf | ∃ n ∈ N, (b.1)⁻¹ * (n * s g.1) * b.1 ∈ K} = π '' {r | b⁻¹ * r.1 * b ∈ K.subgroupOf Xf} := by

  have hnorm : s.range ≤ Subgroup.normalizer (N : Set X) := by
    rintro _ ⟨y, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨fun hn => hconj n hn y, fun hn => ?_⟩
    have := hconj _ hn y⁻¹
    have e : s y⁻¹ * (s y * n * (s y)⁻¹) * (s y⁻¹)⁻¹ = n := by rw [map_inv]; group
    rwa [e] at this
  have hdec : ∀ x ∈ R, ∃ n ∈ N, ∃ h, x = n * s h := by
    intro x hx
    rw [hR, ← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left N s.range hnorm] at hx
    obtain ⟨n, hn, _, ⟨h, rfl⟩, e⟩ := hx
    exact ⟨n, hn, h, e.symm⟩
  have hmemR : ∀ n ∈ N, ∀ h, n * s h ∈ R := fun n hn h => by
    rw [hR]; exact mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right ⟨h, rfl⟩)
  have hpeq : ∀ x y (hx : x ∈ R) (hy : y ∈ R), x = y → p ⟨x, hx⟩ = p ⟨y, hy⟩ := by
    rintro x _ hx hy rfl; rfl
  have hval : ∀ x (hx : x ∈ R), ∃ n ∈ N, x = n * s (p ⟨x, hx⟩) := by
    intro x hx
    obtain ⟨n, hn, h, rfl⟩ := hdec x hx
    exact ⟨n, hn, by rw [hpn n hn h hx]⟩
  have hpmul : ∀ x y (hx : x ∈ R) (hy : y ∈ R) (hxy : x * y ∈ R), p ⟨x * y, hxy⟩ = p ⟨x, hx⟩ * p ⟨y, hy⟩ := by
    intro x y hx hy hxy
    obtain ⟨n, hn, h, rfl⟩ := hdec x hx
    obtain ⟨n', hn', h', rfl⟩ := hdec y hy
    have e : n * s h * (n' * s h') = (n * (s h * n' * (s h)⁻¹)) * s (h * h') := by rw [map_mul]; group
    rw [hpeq _ _ hxy (hmemR _ (mul_mem hn (hconj n' hn' h)) _) e, hpn _ (mul_mem hn (hconj n' hn' h)),
      hpn n hn h, hpn n' hn' h']
  have hp1 : ∀ (h1 : (1 : X) ∈ R), p ⟨1, h1⟩ = 1 := by
    intro h1
    rw [hpeq 1 (1 * s 1) h1 (hmemR 1 N.one_mem 1) (by rw [map_one, one_mul]), hpn 1 N.one_mem 1]
  have hfin : ∀ x (hx : x ∈ R), x ∈ Xf → p ⟨x, hx⟩ ∈ Yf := by
    intro x hx hxf
    obtain ⟨n, hn, e⟩ := hval x hx
    exact hkey n hn _ (e ▸ hxf)
  have hRf : ∀ r : R.subgroupOf Xf, r.1.1 ∈ R := fun r => Subgroup.mem_subgroupOf.1 r.2
  let π : R.subgroupOf Xf →* Yf :=
    { toFun := fun r => ⟨p ⟨r.1.1, hRf r⟩, hfin _ _ r.1.2⟩
      map_one' := Subtype.ext (hp1 _)
      map_mul' := fun r r' => Subtype.ext (hpmul _ _ (hRf r) (hRf r') (hRf (r * r'))) }
  have hsR : ∀ y, s y ∈ R := fun y => by rw [hR]; exact Subgroup.mem_sup_right ⟨y, rfl⟩
  let σ : Yf →* R.subgroupOf Xf :=
    { toFun := fun y => ⟨⟨s y.1, hsf _ y.2⟩, Subgroup.mem_subgroupOf.2 (hsR _)⟩
      map_one' := Subtype.ext (Subtype.ext (map_one s))
      map_mul' := fun y y' => Subtype.ext (Subtype.ext (map_mul s _ _)) }
  have hπ : ∀ r, (π r).1 = p ⟨r.1.1, hRf r⟩ := fun r => rfl
  refine ⟨π, σ, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hp.comp ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)).subtype_mk _
  · exact ((hs.comp continuous_subtype_val).subtype_mk _).subtype_mk _
  · intro y
    apply Subtype.ext
    rw [hπ]
    exact (hpeq _ (1 * s y.1) _ (hmemR 1 N.one_mem _) (one_mul _).symm).trans (hpn 1 N.one_mem _ _)
  · intro r
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro h1
      have h1' : p ⟨r.1.1, hRf r⟩ = 1 := by rw [← hπ, h1]; rfl
      obtain ⟨n, hn, e⟩ := hval _ (hRf r)
      rw [h1', map_one, mul_one] at e
      exact e ▸ hn
    · intro hn
      apply Subtype.ext
      rw [hπ]
      exact (hpeq _ (r.1.1 * s 1) _ (hmemR _ hn 1) (by rw [map_one, mul_one])).trans (hpn _ hn 1 _)
  · intro b
    ext g
    constructor
    · rintro ⟨n, hn, hk⟩
      have hxf : n * s g.1 ∈ Xf := by
        have e : n * s g.1 = b.1 * ((b.1)⁻¹ * (n * s g.1) * b.1) * (b.1)⁻¹ := by group
        rw [e]
        exact mul_mem (mul_mem b.2 (hK hk)) (inv_mem b.2)
      refine ⟨⟨⟨n * s g.1, hxf⟩, Subgroup.mem_subgroupOf.2 (hmemR n hn _)⟩, ?_, ?_⟩
      · show ((b⁻¹ * ⟨n * s g.1, hxf⟩ * b : Xf) : X) ∈ K
        exact hk
      · apply Subtype.ext
        rw [hπ]
        exact hpn n hn _ _
    · rintro ⟨r, hr, rfl⟩
      obtain ⟨n, hn, e⟩ := hval _ (hRf r)
      refine ⟨n, hn, ?_⟩
      rw [hπ, ← e]
      exact hr

end GlobalTheory.RowGrpSemi

namespace GlobalTheory.RowGrpSemi

open GlobalTheory.Core.Mi

theorem key_jac {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {n : GA D S} (hn : n ∈ flagN d) (h : GA D S₀)
    (hf : n * d.emb0 h ∈ GfC S) : h ∈ GfC S₀ := by
  rw [CenAct.mem_GfC_iff] at hf ⊢
  have := GlobalTheory.LevNorm.finf_sand d.p0 _ d.j0 hf d.p0_j0
  rwa [GlobalTheory.JacProj.witt_anisotropic_block_flag_mul_embedded d hn h] at this

theorem jac_case {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (N R K : Subgroup (GA D S)) (s : GA D S₀ →* GA D S)
    (hN : N = flagN d) (hs : s = d.emb0) (hR : R = N ⊔ s.range) (hK : K ≤ GfC S) :
    ∃ (π : R.subgroupOf (GfC S) →* GfC S₀) (σ : GfC S₀ →* R.subgroupOf (GfC S)),
      Continuous π ∧ Continuous σ ∧ (∀ y, π (σ y) = y) ∧ (∀ r, π r = 1 ↔ r.1 ∈ N.subgroupOf (GfC S)) ∧
      ∀ b : GfC S, {g : GfC S₀ | ∃ n ∈ N, (b.1)⁻¹ * (n * s g.1) * b.1 ∈ K} =
        π '' {r | b⁻¹ * r.1 * b ∈ K.subgroupOf (GfC S)} := by
  subst hN hs hR
  exact finite_split (GfC S) (GfC S₀) (flagN d) _ K d.emb0 (GlobalTheory.JacProj.proj d) rfl
    (fun n hn h => GlobalTheory.MixPer.witt_anisotropic_group_normalizes_flag_unipotent D S S₀ ρ d n hn h) d.continuous_embed (GlobalTheory.JacProj.continuous_proj d)
    (fun n hn h _ => GlobalTheory.JacProj.proj_mul d h ⟨n, hn⟩) (fun y hy => CenAct.witt_embedding_mem_finite_unitary_points d hy)
    (fun n hn h hf => key_jac d hn h hf) hK

theorem bes_case {D : D7} {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (N R K : Subgroup (GA D S))
    (s : GA D A →* GA D S) (hN : N = flagN d) (hs : s = embA d o) (hR : R = N ⊔ s.range) (hK : K ≤ GfC S) :
    ∃ (π : R.subgroupOf (GfC S) →* GfC A) (σ : GfC A →* R.subgroupOf (GfC S)),
      Continuous π ∧ Continuous σ ∧ (∀ y, π (σ y) = y) ∧ (∀ r, π r = 1 ↔ r.1 ∈ N.subgroupOf (GfC S)) ∧
      ∀ b : GfC S, {g : GfC A | ∃ n ∈ N, (b.1)⁻¹ * (n * s g.1) * b.1 ∈ K} =
        π '' {r | b⁻¹ * r.1 * b ∈ K.subgroupOf (GfC S)} := by
  subst hN hs hR
  obtain ⟨p, hp, hpn⟩ := GlobalTheory.BesProj.exists_continuous_proj D S S₀ A L ρ d o
  refine finite_split (GfC S) (GfC A) (flagN d) _ K (embA d o) p rfl (fun n hn h => ?_)
    (d.continuous_embed.comp (o.continuous_emb.comp (continuous_id.prodMk continuous_const))) hp (fun n hn h _ => hpn h ⟨n, hn⟩) (fun y hy => CenAct.embA_mem_GfC d o hy)
    (fun n hn h hf => ?_) hK
  · rw [embA_apply]
    exact GlobalTheory.MixPer.witt_anisotropic_group_normalizes_flag_unipotent D S S₀ ρ d n hn _
  · rw [embA_apply] at hf
    have h0 := key_jac d hn _ hf
    have h1 : embA d o h ∈ GfC S := by rw [embA_apply]; exact CenAct.witt_embedding_mem_finite_unitary_points d h0
    exact GlobalTheory.LevNorm.mem_GfC_of_embA d o h1

end GlobalTheory.RowGrpSemi

namespace GlobalTheory.CellMass

theorem rowGrp_finite_semidirect : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R), ∀ j ∈ idx D,
    IsClosed (((rowGrp ch.G j).subgroupOf (GfC _) : Subgroup (GfC (ch.G.V (.grid D.R.m j)))) : Set (GfC (ch.G.V (.grid D.R.m j)))) ∧
    IsClosed (((rowN ch.G j).subgroupOf (GfC _) : Subgroup (GfC (ch.G.V (.grid D.R.m j)))) : Set (GfC (ch.G.V (.grid D.R.m j)))) ∧
    (rowN ch.G j).subgroupOf (GfC _) ≤ (rowGrp ch.G j).subgroupOf (GfC (ch.G.V (.grid D.R.m j))) ∧
    IsOpen (((latGrp ch.G j).subgroupOf (GfC _) : Subgroup (GfC (ch.G.V (.grid D.R.m j)))) : Set (GfC (ch.G.V (.grid D.R.m j)))) ∧
    IsCompact (((latGrp ch.G j).subgroupOf (GfC _) : Subgroup (GfC (ch.G.V (.grid D.R.m j)))) : Set (GfC (ch.G.V (.grid D.R.m j)))) ∧
    ∃ (π : (rowGrp ch.G j).subgroupOf (GfC (ch.G.V (.grid D.R.m j))) →* GfC (ch.G.V (.top j)))
      (σ : GfC (ch.G.V (.top j)) →* (rowGrp ch.G j).subgroupOf (GfC (ch.G.V (.grid D.R.m j)))),
      Continuous π ∧ Continuous σ ∧ (∀ y, π (σ y) = y) ∧ (∀ r, π r = 1 ↔ r.1 ∈ (rowN ch.G j).subgroupOf (GfC _)) ∧
      ∀ b : GfC (ch.G.V (.grid D.R.m j)), prSet ch.G j b = π '' {r | b⁻¹ * r.1 * b ∈ (latGrp ch.G j).subgroupOf (GfC _)} := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch j hj
  have hj' := List.mem_range'_1.1 hj
  have sp := GlobalTheory.RowGrpSplit.grpAt_all ch j hj
  have hNfl : ∃ (S₀ : HSp D) (ρ : ℕ) (d : HypDec (ch.G.V (.grid D.R.m j)) S₀ ρ), rowN ch.G j = flagN d := by
    by_cases h1 : j + 2 * ((D.R.m - 1 - j) / 2) + 1 = D.R.m
    · exact ⟨_, _, _, by unfold rowN; rw [dite_eq_left h1]⟩
    · have h2 : j + 2 * ((D.R.m - 2 - j) / 2) + 2 = D.R.m := by omega
      exact ⟨_, _, _, by unfold rowN; rw [dite_eq_right h1, dite_eq_left h2]⟩
  have hNc : IsClosed ((rowN ch.G j : Subgroup (GA D (ch.G.V (.grid D.R.m j)))) : Set (GA D (ch.G.V (.grid D.R.m j)))) := by
    obtain ⟨S₀, ρ, d, e⟩ := hNfl
    rw [e]
    exact GlobalTheory.Mem.TrueRecord.isClosed_NFlag _ (isIsoSub_e d)
  refine ⟨?_, ?_, ?_, sp.opn, ?_, ?_⟩
  · rw [Subgroup.coe_subgroupOf]
    exact sp.clR.preimage continuous_subtype_val
  · rw [Subgroup.coe_subgroupOf]
    exact hNc.preimage continuous_subtype_val
  · intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    rw [rowGrp_eq]
    exact Subgroup.mem_sup_left hx
  · rw [Subgroup.coe_subgroupOf]
    exact sp.clB.isClosedEmbedding_subtypeVal.isCompact_preimage sp.cpt
  · by_cases h1 : j + 2 * ((D.R.m - 1 - j) / 2) + 1 = D.R.m
    · exact GlobalTheory.RowGrpSemi.jac_case (rowJac ch.G j (by omega) ((D.R.m - 1 - j) / 2) (by omega)) _ _ _ _
        (by unfold rowN; rw [dite_eq_left h1]) (by unfold rowEmb; rw [dite_eq_left h1]) (rowGrp_eq ch.G j) sp.le
    · have h2 : j + 2 * ((D.R.m - 2 - j) / 2) + 2 = D.R.m := by omega
      exact GlobalTheory.RowGrpSemi.bes_case (besDecAt ch.G j _ h2) (GlobalTheory.OrthSumExists.orthDecHsum D _ _) _ _ _ _
        (by unfold rowN; rw [dite_eq_right h1, dite_eq_left h2]) (by unfold rowEmb; rw [dite_eq_right h1, dite_eq_left h2]) (rowGrp_eq ch.G j) sp.le

end GlobalTheory.CellMass
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ConnectionLinear

section Helpers
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem contr_comb_left (hψ : IsStdChar D ψ (-1)) {ρ σ : ℕ} {B : Unf.BesLev D ρ} {B' : Unf.BesLev D σ}
    (l : Unf.Link B B'.L B'.ζ) (S : HSp D) (vL : Unf.VolM D B'.L.rank S.rank) (c : ℂ) {X Y : WO B.V₀ S → ℂ}
    {Z : WO S B'.V₀ → ℂ} (hX : IsThetaFunO ψ B.V₀ S X) (hY : IsThetaFunO ψ B.V₀ S Y) (hZ : IsThetaFunO ψ S B'.V₀ Z)
    (u : WO B.A S) (v : WO S B'.A) :
    Unf.contr l S vL (c • X + Y) Z u v = c * Unf.contr l S vL X Z u v + Unf.contr l S vL Y Z u v := by
  have i1 := GlobalTheory.ContractionLocal.integrable_contr hψ l S vL hX hZ u v
  have i2 := GlobalTheory.ContractionLocal.integrable_contr hψ l S vL hY hZ u v
  unfold GlobalTheory.Unf.contr
  rw [← integral_const_mul, ← integral_add (i1.const_mul c) i2]
  congr 1
  funext w
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem contr_flatBF_smul_add (hψ : IsStdChar D ψ (-1)) {ρ σ : ℕ} {B : Unf.BesLev D ρ} {J : Unf.JacLev D ρ}
    {B' : Unf.BesLev D σ} (s : Unf.StepBF ψ B J) (l : Unf.Link B B'.L B'.ζ) (vL : Unf.VolM D B'.L.rank J.W₀.rank)
    (c : ℂ) {X Y : WO B.V J.W → ℂ} {Z : WO J.W₀ B'.V₀ → ℂ} (hX : IsThetaFunO ψ B.V J.W X)
    (hY : IsThetaFunO ψ B.V J.W Y) (hZ : IsThetaFunO ψ J.W₀ B'.V₀ Z) (u : WO B.A J.W₀) (v : WO J.W₀ B'.A) :
    Unf.contr l J.W₀ vL (Unf.flatBF s (c • X + Y)) Z u v =
      c * Unf.contr l J.W₀ vL (Unf.flatBF s X) Z u v + Unf.contr l J.W₀ vL (Unf.flatBF s Y) Z u v := by
  have hF := GlobalTheory.Unf.Flat.flatLaw D
  have fX := (GlobalTheory.T.flatThetaMaps_preserve_thetaFunctions D hF ψ).1 ρ B J s X hX
  have fY := (GlobalTheory.T.flatThetaMaps_preserve_thetaFunctions D hF ψ).1 ρ B J s Y hY
  have hcX := GlobalTheory.OrientedHeis.theta_smul c hX
  rw [(GlobalTheory.FlatLin.flatBF_linear D hF ψ ρ B J s (c • X) Y c hcX hY).1,
    (GlobalTheory.FlatLin.flatBF_linear D hF ψ ρ B J s X Y c hX hY).2]
  exact contr_comb_left hψ l J.W₀ vL c fX fY hZ u v

end Helpers

section Grid
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem fock_comb (W : G.Weil) (p : Pair T) (c : ℂ) {f g : WO (G.pS p) (G.pT p) → ℂ} (hf : IsThetaFunO W.ψ _ _ f)
    (hg : IsThetaFunO W.ψ _ _ g) (Q : PolF D (G.pT p).rank (G.pS p).rank) :
    W.fock p (c • f + g) Q = c • W.fock p f Q + W.fock p g Q := by
  unfold GridData.Weil.fock
  exact GlobalTheory.FockFiniteHeis.pureTensorO_lin W.ψ W.θ _ _ W.ψ_std W.θ_is _ _ _ _ c hf hg Q

theorem fock_theta (W : G.Weil) (p : Pair T) {f : WO (G.pS p) (G.pT p) → ℂ} (hf : IsThetaFunO W.ψ _ _ f)
    (Q : PolF D (G.pT p).rank (G.pS p).rank) : IsThetaFunO W.ψ _ _ (W.fock p f Q) := by
  unfold GridData.Weil.fock
  exact GlobalTheory.GalLift.Vec.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ hf Q

end Grid

theorem contrLin_left : Big fun ch => ContrLin ch 0 := by

  refine ⟨0, fun ε CF _ => ⟨0, ?_⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F _ ch _ _
  intro j hj hjm hm t M hM P h Φ a ha φ φ' c hΦ hφ hφ' u v
  obtain ⟨a, ha'⟩ := a
  simp only [add_zero] at ha
  subst ha

  have h1 : ¬ (a + 2 * 0 + 2 = D.R.m) := by omega
  have h2 : a + 2 * ((D.R.m - 4 - a) / 2 + 1) + 2 = D.R.m := by
    obtain ⟨k, hk⟩ := hj
    obtain ⟨n, hn⟩ := hm
    omega
  have hin : (Pair.mu t D.R.m a : Pair T).InRange D.R.m := show D.R.m ≤ D.R.m ∧ a + 1 ≤ D.R.m from ⟨le_rfl, by omega⟩
  have hin' : (Pair.mu t D.R.m (a + 1) : Pair T).InRange D.R.m :=
    show D.R.m ≤ D.R.m ∧ a + 1 + 1 ≤ D.R.m from ⟨le_rfl, by omega⟩
  simp only [conAt, dif_neg h1, fockD]
  simp (disch := simp) only [Function.update_self, Function.update_of_ne]
  simp only [h2, ↓reduceDIte]
  · rw [fock_comb ch.W (Pair.mu t D.R.m a) c hφ hφ' (P ⟨a, ha'⟩), map_add (f := _), map_smul]
    refine contr_flatBF_smul_add ch.W.ψ_std (B := besAt ch.G hM a ((D.R.m - 4 - a) / 2 + 1) h2 _)
      (J := jacAt ch.G hM (a + 1) ((D.R.m - 4 - a) / 2 + 1) (by omega)) _ _ _ c ?_ ?_ ?_ _ _
    · exact (ch.W.om_is _ hin).om_pres _ _ (fock_theta ch.W _ hφ _)
    · exact (ch.W.om_is _ hin).om_pres _ _ (fock_theta ch.W _ hφ' _)
    · exact (GlobalTheory.T.flatThetaMaps_preserve_thetaFunctions D (GlobalTheory.Unf.Flat.flatLaw D) _).2 _ _ _ _ _
        ((ch.W.om_is _ hin').om_pres _ _ (fock_theta ch.W _ (hΦ ⟨a + 1, by omega⟩) _))

end GlobalTheory.ConnectionLinear
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LastPositionLin
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) {M : Vol G} {t : T}

theorem lastDat_lin (hM : M.Is t) (j : ℕ) (hj : j + 2 * 0 + 2 = D.R.m) (vN : GlobalTheory.Unf.VolN (besDecAt G j 0 hj))
    (g : GA D (G.V (.grid D.R.m j)))
    (Φ Φ' : WO (G.V (.grid D.R.m j)) (G.V (.grid D.R.m (j + 1))) → ℂ) (c : ℂ)
    (hΦ : IsThetaFunO W.ψ _ _ Φ) (hΦ' : IsThetaFunO W.ψ _ _ Φ')
    (Φ₂ : WO (G.V (.grid D.R.m (j + 1))) (G.V (.grid D.R.m D.R.m)) → ℂ) (u v) :
    lastDat W hM j hj vN g (c • Φ + Φ') Φ₂ u v =
      c * lastDat W hM j hj vN g Φ Φ₂ u v + lastDat W hM j hj vN g Φ' Φ₂ u v := by
  set s := (lastAt G W t hM j hj vN).s with hs
  have hw := s.weil
  have h1 := hw.om_pres (g, 1) Φ hΦ
  have h2 := hw.om_pres (g, 1) Φ' hΦ'
  have h3 : IsThetaFunO W.ψ _ _ (c • s.om (g, 1) Φ) := GlobalTheory.LocMod.LinSpace.isThetaFunO_smul c h1
  have e1 : (s.om (g, 1)) (c • Φ + Φ') = c • (s.om (g, 1)) Φ + (s.om (g, 1)) Φ' := by
    have := (s.om (g, 1)).map_add (c • Φ) Φ'
    have h' := (s.om (g, 1)).map_smul c Φ
    exact this.trans (congrArg (· + (s.om (g, 1)) Φ') h')
  have key : GlobalTheory.Unf.flatBF s (s.om (g, 1) (c • Φ + Φ')) =
      c • GlobalTheory.Unf.flatBF s (s.om (g, 1) Φ) + GlobalTheory.Unf.flatBF s (s.om (g, 1) Φ') := by
    rw [e1, (GlobalTheory.FlatLin.flatBF_linear D (GlobalTheory.Unf.Flat.flatLaw D) _ _ _ _ s _ _ c h3 h2).1,
      (GlobalTheory.FlatLin.flatBF_linear D (GlobalTheory.Unf.Flat.flatLaw D) _ _ _ _ s _ _ c h1 h1).2]
  have keyx : ∀ x, GlobalTheory.Unf.flatBF s (s.om (g, 1) (c • Φ + Φ')) x =
      c * GlobalTheory.Unf.flatBF s (s.om (g, 1) Φ) x + GlobalTheory.Unf.flatBF s (s.om (g, 1) Φ') x := fun x => by
    rw [key]; rfl
  unfold lastDat GlobalTheory.FinPl.lastBi GlobalTheory.MixModel.OrthDec.boxT
  rw [← hs]
  beta_reduce
  erw [keyx]
  ring

theorem conAt_last_lin (hM : M.Is t) (P : PolDown G) (h : Pts G) (Φ : SchDown G t) (j : ℕ) (hj : j + 2 = D.R.m)
    (a : Fin D.R.m) (ha : (a : ℕ) = j + 0) (φ φ' : Sch G (.down t D.R.m a)) (c : ℂ)
    (hφ : IsThetaFunO W.ψ _ _ φ) (hφ' : IsThetaFunO W.ψ _ _ φ') (u v) :
    conAt W hM (fockD W t (Function.update Φ a (c • φ + φ')) P) h j u v =
      c * conAt W hM (fockD W t (Function.update Φ a φ) P) h j u v +
        conAt W hM (fockD W t (Function.update Φ a φ') P) h j u v := by
  obtain ⟨k, hk⟩ := a
  simp only [add_zero] at ha
  subst ha
  have h0 : k + 2 * 0 + 2 = D.R.m := by omega
  unfold conAt
  rw [dite_eq_left h0, dite_eq_left h0, dite_eq_left h0]
  have hne : (⟨k + 1, by omega⟩ : Fin D.R.m) ≠ ⟨k, hk⟩ := fun e => by simp at e
  simp only [fockD, Function.update_self, Function.update_of_ne hne]
  have hf : W.fock (.mu t D.R.m k) (c • φ + φ') (P ⟨k, hk⟩) =
      c • W.fock (.mu t D.R.m k) φ (P ⟨k, hk⟩) + W.fock (.mu t D.R.m k) φ' (P ⟨k, hk⟩) :=
    GlobalTheory.FockFiniteHeis.pureTensorO_lin W.ψ W.θ _ _ W.ψ_std W.θ_is _ _ _ _ c hφ hφ' _
  have th : ∀ f : Sch G (.down t D.R.m (⟨k, hk⟩ : Fin D.R.m)), IsThetaFunO W.ψ _ _ f →
      IsThetaFunO W.ψ (G.V (.grid D.R.m k)) (G.V (.grid D.R.m (k + 1))) (W.fock (.mu t D.R.m k) f (P ⟨k, hk⟩)) :=
    fun f hf => Formalism.IndefR.Fin.ptStable D W.ψ W.θ W.ψ_std W.θ_is _ _ _ _ _ _ f _ hf
  erw [hf]
  exact lastDat_lin W hM k h0 _ _ _ _ c (th φ hφ) (th φ' hφ') _ u v

end GlobalTheory.LastPositionLin


open GlobalTheory.RowClaim GlobalTheory.ConnectionLinear in
theorem GlobalTheory.LastPositionLin.lastLin_zero : Big fun ch => GlobalTheory.ConnectionLinear.LastLin ch 0 := by
  refine ⟨0, fun _ _ _ => ⟨0, ?_⟩⟩
  intros D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _
  intro j _ hj t M hM P h Φ a ha φ φ' c _ hφ hφ' u v
  exact GlobalTheory.LastPositionLin.conAt_last_lin ch.W hM P h Φ j hj a ha φ φ' c hφ hφ' u v
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.ConnectionLinear
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LastLinR

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem castSch_lin {V : HSp D} {n n' : ℕ} (e : n = n') (c : ℂ) (f g : WO V (G.V (.grid D.R.m n)) → ℂ) :
    castSch G e (c • f + g) = c • castSch G e f + castSch G e g := by
  subst e; rfl

theorem lastDat_lin (Wl : G.Weil) {t : T} {M : Vol G} (hM : M.Is t) (j : ℕ) (hj : j + 2 * 0 + 2 = D.R.m)
    (vN : GlobalTheory.Unf.VolN (besDecAt G j 0 hj)) (g : GA D (G.V (.grid D.R.m j)))
    (Φ₁ : WO (G.V (.grid D.R.m j)) (G.V (.grid D.R.m (j + 1))) → ℂ)
    (c : ℂ) (Φ₂ Φ₂' : WO (G.V (.grid D.R.m (j + 1))) (G.V (.grid D.R.m D.R.m)) → ℂ) (u v) :
    lastDat Wl hM j hj vN g Φ₁ (c • Φ₂ + Φ₂') u v = c * lastDat Wl hM j hj vN g Φ₁ Φ₂ u v + lastDat Wl hM j hj vN g Φ₁ Φ₂' u v := by
  simp only [lastDat, GlobalTheory.FinPl.lastBi, OrthDec.boxT, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

end GlobalTheory.LastLinR

namespace GlobalTheory.ConnectionLinear

section
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem lastLin_one (ch : Choice R) : LastLin ch 1 := by
  intro j hj hjm t M hM P h Φ a ha φ φ' c hΦ hφ hφ' u v
  have h0 : j + 2 * 0 + 2 = D.R.m := by omega
  have hlt : j + 1 < D.R.m := by omega
  obtain rfl : a = ⟨j + 1, hlt⟩ := Fin.ext ha
  have hne : (⟨j, by omega⟩ : Fin D.R.m) ≠ ⟨j + 1, hlt⟩ := fun e => by simp [Fin.ext_iff] at e
  unfold conAt
  rw [dite_eq_left h0, dite_eq_left h0, dite_eq_left h0]
  simp only [fockD, Function.update_of_ne hne, Function.update_self]
  have hlin : ch.W.fock (.mu t D.R.m (j + 1)) (c • φ + φ') (P ⟨j + 1, hlt⟩) =
      c • ch.W.fock (.mu t D.R.m (j + 1)) φ (P ⟨j + 1, hlt⟩) + ch.W.fock (.mu t D.R.m (j + 1)) φ' (P ⟨j + 1, hlt⟩) := by
    simp only [GridData.Weil.fock]
    exact GlobalTheory.FockFiniteHeis.pureTensorO_lin _ _ _ _ ch.W.ψ_std ch.W.θ_is _ _ _ _ c hφ hφ' _
  rw [hlin, GlobalTheory.LastLinR.castSch_lin, GlobalTheory.LastLinR.lastDat_lin]

end

theorem big_lastLin_one : Big fun ch => LastLin ch 1 :=
  by
  refine ⟨0, fun _ _ _ => ⟨0, ?_⟩⟩
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _
  exact lastLin_one ch

end GlobalTheory.ConnectionLinear
end
end

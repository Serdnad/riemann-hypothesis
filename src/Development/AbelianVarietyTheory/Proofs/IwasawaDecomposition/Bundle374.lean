module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle003
public import Formalism.LocalToGlobal.Columns.ColumnsProofs.Bundle001
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle016
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CharacterValueAtT
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle148
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle050
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelaf
public import Formalism.LocalToGlobal.Columns.Bundle007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsLevel
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle002
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle352
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
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
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle334
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

noncomputable section

namespace GlobalTheory.EigOcc

open Module Module.End

section Lin

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem inf_ker_ne_bot {a : End K V} {c : K} {U : Submodule K V} (hU : U ≠ ⊥)
    (hle : U ≤ a.maxGenEigenspace c) (hinv : ∀ y ∈ U, a y ∈ U) :
    U ⊓ LinearMap.ker (a - c • 1) ≠ ⊥ := by
  classical
  obtain ⟨y, hyU, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
  have hy := hle hyU
  rw [mem_maxGenEigenspace] at hy
  have hP : ∃ n : ℕ, ((a - c • (1 : End K V)) ^ n) y = 0 := hy
  have hm : ((a - c • 1) ^ Nat.find hP) y = 0 := Nat.find_spec hP
  have hm0 : Nat.find hP ≠ 0 := by
    intro h
    rw [h, pow_zero, Module.End.one_apply] at hm
    exact hy0 hm
  obtain ⟨m', hm'⟩ : ∃ m', Nat.find hP = m' + 1 := ⟨Nat.find hP - 1, by omega⟩
  have hne : ((a - c • 1) ^ m') y ≠ 0 := Nat.find_min hP (by omega)
  have hinv' : ∀ k : ℕ, ((a - c • 1) ^ k) y ∈ U := by
    intro k
    induction k with
    | zero => simpa using hyU
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
      exact U.sub_mem (hinv _ ih) (U.smul_mem c ih)
  intro hbot
  apply hne
  have hmem : ((a - c • 1) ^ m') y ∈ U ⊓ LinearMap.ker (a - c • 1) := by
    refine ⟨hinv' m', ?_⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, ← Module.End.mul_apply, ← pow_succ', ← hm']
    exact hm
  rw [hbot] at hmem
  exact (Submodule.mem_bot K).1 hmem

theorem exists_common_eigvec (S : Set (End K V)) (hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b) (χ : End K V → K)
    (W0 : Submodule K V) (hW : W0 ≠ ⊥) (hle : ∀ a ∈ S, W0 ≤ a.maxGenEigenspace (χ a))
    (hinv : ∀ a ∈ S, ∀ y ∈ W0, a y ∈ W0) :
    ∃ u ∈ W0, u ≠ 0 ∧ ∀ a ∈ S, a u = χ a • u := by
  classical
  have hP : ∃ n, ∃ U : Submodule K V, U ≤ W0 ∧ U ≠ ⊥ ∧ (∀ a ∈ S, ∀ y ∈ U, a y ∈ U) ∧ finrank K U = n :=
    ⟨_, W0, le_rfl, hW, hinv, rfl⟩
  obtain ⟨U, hUW, hU0, hUinv, hUn⟩ := Nat.find_spec hP
  have key : ∀ a ∈ S, U ≤ LinearMap.ker (a - χ a • 1) := by
    intro a ha
    have hU'0 : U ⊓ LinearMap.ker (a - χ a • 1) ≠ ⊥ := inf_ker_ne_bot hU0 (hUW.trans (hle a ha)) (hUinv a ha)
    have hU'inv : ∀ b ∈ S, ∀ y ∈ U ⊓ LinearMap.ker (a - χ a • 1), b y ∈ U ⊓ LinearMap.ker (a - χ a • 1) := by
      rintro b hb y ⟨hyU, hyk⟩
      refine ⟨hUinv b hb y hyU, ?_⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker] at hyk
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      have hc : Commute (a - χ a • 1) b := (hS a ha b hb).sub_left ((Commute.one_left b).smul_left _)
      rw [← Module.End.mul_apply, hc.eq, Module.End.mul_apply, hyk, map_zero]
    have hle' : finrank K U ≤ finrank K ↥(U ⊓ LinearMap.ker (a - χ a • 1)) := by
      rw [hUn]
      exact Nat.find_min' hP ⟨_, inf_le_left.trans hUW, hU'0, hU'inv, rfl⟩
    have heq : U ⊓ LinearMap.ker (a - χ a • 1) = U := Submodule.eq_of_le_of_finrank_le inf_le_left hle'
    rw [← heq]
    exact inf_le_right
  obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
  refine ⟨u, hUW huU, hu0, fun a ha => ?_⟩
  have h := key a ha huU
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at h
  exact h

end Lin

end GlobalTheory.EigOcc

namespace GlobalTheory.EigOcc

theorem mem_heckeEig_of_gen {O X M : Type} [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M]
    (T : Subalgebra O (X → O)) (act : T →ₐ[O] Module.End O M) (x : X) (G : Set (X → O))
    (hT : T = Algebra.adjoin O G) (z : TensorProduct O (FractionRing O) M)
    (hG : ∀ f : T, (f : X → O) ∈ G →
      ((act f).baseChange (FractionRing O)) z = algebraMap O (FractionRing O) ((f : X → O) x) • z) :
    z ∈ heckeEig T act x := by
  rw [heckeEig, Submodule.mem_iInf]
  intro f
  rw [Module.End.mem_eigenspace_iff]
  obtain ⟨g, hgT⟩ := f
  have hg : g ∈ Algebra.adjoin O G := hT ▸ hgT
  induction hg using Algebra.adjoin_induction with
  | mem g hg' => exact hG ⟨g, hgT⟩ hg'
  | algebraMap r =>
    have e1 : (⟨algebraMap O (X → O) r, hgT⟩ : T) = algebraMap O T r := rfl
    rw [e1, AlgHom.commutes, Algebra.algebraMap_eq_smul_one r, LinearMap.baseChange_smul, LinearMap.baseChange_one,
      LinearMap.smul_apply, Module.End.one_apply, ← algebraMap_smul (FractionRing O) r z]
    rfl
  | add g1 g2 h1 h2 ih1 ih2 =>
    have m1 : g1 ∈ T := hT ▸ h1
    have m2 : g2 ∈ T := hT ▸ h2
    have e1 : (⟨g1 + g2, hgT⟩ : T) = ⟨g1, m1⟩ + ⟨g2, m2⟩ := rfl
    rw [e1, map_add (f := _), LinearMap.baseChange_add, LinearMap.add_apply, ih1 m1, ih2 m2]
    simp only [Subalgebra.coe_add, Pi.add_apply, map_add (f := _), add_smul]
  | mul g1 g2 h1 h2 ih1 ih2 =>
    have m1 : g1 ∈ T := hT ▸ h1
    have m2 : g2 ∈ T := hT ▸ h2
    have e1 : (⟨g1 * g2, hgT⟩ : T) = ⟨g1, m1⟩ * ⟨g2, m2⟩ := rfl
    rw [e1, map_mul, LinearMap.baseChange_mul, Module.End.mul_apply, ih2 m2, LinearMap.map_smul, ih1 m1, smul_smul]
    simp only [Subalgebra.coe_mul, Pi.mul_apply, map_mul, mul_comm]

end GlobalTheory.EigOcc

namespace GlobalTheory.EigOcc

section Main

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}



theorem heckeEig_ne_bot (B : LocBase0 H what₂) (hs : HeckeStd0 B) (hd : FinDimV B) (hL : MtLoc B (partCompl_of hs hd))
    (hAct : ActEx B (partCompl_of hs hd)) (hH : ActHK B hs hd hL hAct) (i : LocT B) (x : XOf B i) :
    heckeEig (TOf B i) (actC B (partCompl_of hs hd) hAct i) x ≠ ⊥ := by
  classical
  haveI := hd (jOf B i) (wOf B i)
  let S : Set (Module.End (FractionRing (OOf B i)) (B.V (jOf B i) (wOf B i))) :=
    {f | ∃ v k, GenAt0 H (lOf B i) (B.Qw (wOf B i)) v k ∧ f = B.hK (jOf B i) (wOf B i) v k}
  let χ : Module.End (FractionRing (OOf B i)) (B.V (jOf B i) (wOf B i)) → FractionRing (OOf B i) :=
    fun a => if h : a ∈ hAlg B i then NCov.pt x.1 ⟨a, h⟩ else 0
  have hSc : ∀ a ∈ S, ∀ b ∈ S, Commute a b := std_comm (j := jOf B i) (w := wOf B i) hs i.2.2.2.1 i.2.2.2.2.1
  have hmem : ∀ a ∈ S, a ∈ hAlg B i := fun a ha => Algebra.subset_adjoin ha
  have hχ : ∀ a (ha : a ∈ S), χ a = NCov.pt x.1 ⟨a, hmem a ha⟩ := fun a ha => dif_pos (hmem a ha)
  obtain ⟨u, huW, hu0, hu⟩ := exists_common_eigvec S hSc χ (NCov.W (hAlg B i) (NCov.pt x.1)) x.2.2
    (fun a ha => by
      rw [hχ a ha]
      exact NCov.W_le (hAlg B i) (NCov.pt x.1) ⟨a, hmem a ha⟩)
    (fun a ha y hy => by
      rw [NCov.W, Submodule.mem_iInf] at hy ⊢
      intro t
      exact Module.End.mapsTo_maxGenEigenspace_of_comm (NCov.commute_adjoin hSc t.2 (hmem a ha)) _ (hy t))
  have hpart : u ∈ NCov.part (hAlg B i) i.2.1 :=
    (le_iSup₂ (f := fun (ψ : hAlg B i →ₐ[OOf B i] OOf B i) (_ : NCov.cls ψ = i.2.1) => NCov.W (hAlg B i) (NCov.pt ψ))
      x.1 x.2.1) huW
  obtain ⟨z, hz⟩ := (PsiC_range B (partCompl_of hs hd) hL i u).1 hpart
  have hG : ∀ f : TOf B i, (f : XOf B i → OOf B i) ∈ {f | ∃ v k, GenAt0 H (lOf B i) (B.Qw (wOf B i)) v k ∧ f = hTfun B i v k} →
      ((actC B (partCompl_of hs hd) hAct i f).baseChange (FractionRing (OOf B i))) z =
        algebraMap (OOf B i) (FractionRing (OOf B i)) ((f : XOf B i → OOf B i) x) • z := by
    rintro f ⟨v, k, hvk, hf⟩
    have e1 : f = hTOf B i v k := Subtype.ext (by rw [hf]; simp [hTOf, dif_pos hvk])
    subst e1
    apply PsiC_inj B (partCompl_of hs hd) hL i
    rw [hH i v k hvk z, hz, map_smul, hz, hu _ ⟨v, k, hvk, rfl⟩, hχ _ ⟨v, k, hvk, rfl⟩]
    exact congrArg (· • u) (congrArg (algebraMap (OOf B i) (FractionRing (OOf B i))) (ptX_val B i v k hvk x).symm)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [map_zero] at hz
    exact hu0 hz.symm
  intro hbot
  apply hz0
  have hzm : z ∈ heckeEig (TOf B i) (actC B (partCompl_of hs hd) hAct i) x :=
    mem_heckeEig_of_gen (TOf B i) (actC B (partCompl_of hs hd) hAct i) x _ rfl z hG
  rw [hbot] at hzm
  exact (Submodule.mem_bot _).1 hzm

end Main

end GlobalTheory.EigOcc
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

namespace GlobalTheory.HeckeLocN.BridgeAll




theorem exists_finExt_ge {l : ℕ} [Fact l.Prime] {ι : Type} (S : Set ι) (hS : S.Finite) (L : ι → Loc.FinExt l) :
    ∃ F : Loc.FinExt l, ∀ i ∈ S, (L i).1 ≤ F.1 := by
  induction S, hS using Set.Finite.induction_on with
  | empty => exact ⟨⟨⊥, inferInstance⟩, fun i hi => absurd hi (Set.notMem_empty i)⟩
  | @insert a s _ _ ih =>
    obtain ⟨F, hF⟩ := ih
    have h1 := F.2
    have h2 := (L a).2
    refine ⟨⟨(L a).1 ⊔ F.1, IntermediateField.finiteDimensional_sup _ _⟩, ?_⟩
    rintro i (rfl | hi)
    · exact le_sup_left
    · exact (hF i hi).trans le_sup_right

theorem placesOver_finite (E : Type) [Field E] [NumberField E] {l : ℕ} (hl : l.Prime) :
    (placesOver E l).Finite := by
  have h0 : Ideal.span {(l : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl.ne_zero
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  exact Ideal.dvd_span_singleton.2 hv

theorem exists_bridge_good {R : Ranks} (H : Host R) (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra H.E Ω]
    [IsAlgClosure H.E Ω] (u : HeightOneSpectrum (𝓞 H.E)) (A : ValuationSubring Ω) (hA : IsPlaceOver A u) :
    ∃ L0 : Loc.FinExt l, u ∈ placesOver H.E l → ∀ LL : Loc.FinExt l, L0.1 ≤ LL.1 →
      ∃ Bw : LocBridge l H.E Ω (Dec (F := H.E) A) ↥(Loc.OL LL),
        (∀ x, x ∈ A ↔ ‖Bw.j x‖ ≤ 1) ∧ Loc.GoodCoef H.condN Bw.LL ∧
        ∀ x : ↥(Loc.OL LL), ((Bw.toLL x : ↥Bw.LL.1) : Loc.Om l) = ((x : ↥LL.1) : Loc.Om l) := by
  by_cases hu : u ∈ placesOver H.E l
  · obtain ⟨j, L0, hj, hB⟩ := GlobalTheory.PlaceBridge.exists_locBridge l H.E Ω u A hu hA
    let L1 : Loc.FinExt l := UpperTheory.KStar.Cyc.rootsExt l _ (UpperTheory.KStar.Cyc.lcm_ne_zero (l := l) H.toHostRaw)
    have f0 := L0.2
    have f1 := L1.2
    refine ⟨⟨L0.1 ⊔ L1.1, IntermediateField.finiteDimensional_sup _ _⟩, fun _ LL hLL => ?_⟩
    obtain ⟨Bw, e1, e2, e3, e4⟩ := hB LL (le_sup_left.trans hLL)
    refine ⟨Bw, by rw [e1]; exact hj, ?_, e4⟩
    rw [e2]
    exact UpperTheory.KStar.Cyc.mem_of_rootsExt_le _ (le_sup_right.trans hLL)
  · exact ⟨⟨⊥, inferInstance⟩, fun h => absurd h hu⟩

theorem brAt_of_large : ∀ (D : D7) (w : D.what₂.places.Pl), ∃ F0 : Loc.FinExt (D.what₂.places.resChar w),
    ∀ (X : CoefIn D.what₂) (j : ℕ), F0.1 ≤ (X.Kx j w).1 → BrAt X j w := by
  intro D w
  choose L hL using fun u : PlE D.host =>
    exists_bridge_good D.host (D.what₂.places.resChar w) D.nd.Om u (D.nd.plOm.1 u) (D.nd.plOm.2 u)
  obtain ⟨F, hF⟩ := exists_finExt_ge _ (placesOver_finite D.host.E (D.what₂.places.resChar_prime w)) L
  refine ⟨F, fun X j hX u hu => ?_⟩
  obtain ⟨Bw, h1, h2, h3⟩ := hL u hu (X.Kx j w) ((hF u hu).trans hX)
  exact ⟨Bw, h1, h2, fun z => (iqC_alg X j w z).trans (h3 z).symm⟩

end GlobalTheory.HeckeLocN.BridgeAll
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

noncomputable section

namespace GlobalTheory.HeckeSplitField

open Module

theorem aeval_baseChange {L K M : Type} [Field L] [Field K] [Algebra L K] [AddCommGroup M] [Module L M]
    (f : Module.End L M) (p : L[X]) :
    aeval (f.baseChange K) (p.map (algebraMap L K)) = (aeval f p).baseChange K := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr => rw [Polynomial.map_add (f := _), map_add (f := _), hp, hr, map_add (f := _), LinearMap.baseChange_add]
  | monomial k c =>
    rw [Polynomial.map_monomial, aeval_monomial, aeval_monomial, ← LinearMap.baseChange_pow]
    apply TensorProduct.AlgebraTensorModule.curry_injective
    ext x
    simp [Module.algebraMap_end_apply, LinearMap.baseChange_tmul]

theorem iSup_maxGen_baseChange {L K M I : Type} [Field L] [Field K] [Algebra L K] [AddCommGroup M] [Module L M]
    [FiniteDimensional L M] (op : I → Module.End L M) (hc : ∀ x y, Commute (op x) (op y)) {p : L[X]}
    (hp : Formalism.L2.Col.HeckePolyFor op p) (hsp : (p.map (algebraMap L K)).Splits) (x : I) :
    ⨆ μ, Module.End.maxGenEigenspace ((op x).baseChange K) μ = ⊤ := by
  classical
  obtain ⟨hp0, s, hs, hd⟩ := hp
  obtain ⟨c, hcx⟩ := hs x
  have e : (op x).baseChange K = ∑ y ∈ s, algebraMap L K (c y) • (op y).baseChange K := by
    rw [hcx]
    change LinearMap.baseChangeHom L K M M (∑ y ∈ s, c y • op y) = _

    rw [map_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    change (c y • op y).baseChange K = _
    rw [LinearMap.baseChange_smul, algebraMap_smul]
  rw [e]
  refine Formalism.L2.Col.hfs_iSup_maxGen_sum s (fun y => (op y).baseChange K) (fun y => algebraMap L K (c y))
    (fun y _ z _ => ?_) (fun y hy => ?_)
  · change _ * _ = _ * _
    rw [← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul, (hc y z).eq]
  · apply Formalism.L2.Col.hfs_iSup_maxGen_of_splits
    refine hsp.of_dvd (Polynomial.map_ne_zero hp0) (minpoly.dvd K _ ?_)
    rw [aeval_baseChange, hd y hy, LinearMap.baseChange_zero]

theorem finiteDimensional_mtL {R : Ranks} (what₂ : Rows.Data R) (μ : what₂.Tup) (j : ℕ) :
    FiniteDimensional what₂.LL (what₂.MtL μ j) := by
  let b := Module.Free.chooseBasis what₂.LL (what₂.MtL μ j)
  haveI : Finite (Module.Free.ChooseBasisIndex what₂.LL (what₂.MtL μ j)) := ((what₂.jMt_basis μ j b).1).finite
  exact Module.Finite.of_basis b

end GlobalTheory.HeckeSplitField

namespace GlobalTheory.HeckeSplitField

open Module

theorem exists_finExt_split : ∀ (D : D7) (M : MtFam D) (C : NChoice D) (hR : HeckeLift0 (mt0 M) C.Q) (E0 : PlEmb D.what₂),
    (∀ j w v k v' k', Commute (hLC (mt0 M) C.Q hR j w v k) (hLC (mt0 M) C.Q hR j w v' k')) →
    ∀ (j : ℕ) (w : D.what₂.places.Pl), ∃ F0 : Loc.FinExt (D.what₂.places.resChar w), ∀ X : CoefIn D.what₂, X.E = E0 →
      F0.1 ≤ (X.Kx j w).1 → ∀ v k, GenAt0 D.host (D.what₂.places.resChar w) (C.Q w) v k →
        ⨆ μ, (hKC (mt0 M) C.Q hR X j w v k).maxGenEigenspace μ = ⊤ := by
  intro D M C hR E0 hcomm j w
  classical
  haveI : FiniteDimensional D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j) := finiteDimensional_mtL D.what₂ _ j
  let op : HeightOneSpectrum (𝓞 D.host.E) × ℕ → Module.End D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j) :=
    fun vk => hLC (mt0 M) C.Q hR j w vk.1 vk.2
  obtain ⟨p, hp⟩ := Formalism.L2.Col.hfs_exists_poly op
  let S : Set (PadicAlgCl (D.what₂.places.resChar w)) := ((p.map (E0.emb w)).roots.toFinset : Set _)
  haveI : Finite S := Finset.finite_toSet _
  have hfin : FiniteDimensional ℚ_[D.what₂.places.resChar w] (IntermediateField.adjoin ℚ_[D.what₂.places.resChar w] S) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  refine ⟨⟨IntermediateField.adjoin ℚ_[D.what₂.places.resChar w] S, hfin⟩, ?_⟩
  intro X hXE hF v k _
  have hmap : (p.map (ecC X j w)).map (iqC X j w) = p.map (E0.emb w) := by
    rw [Polynomial.map_map]
    congr 1
    ext x
    rw [RingHom.comp_apply, iqC_ec, hXE]
  have hsp : (p.map (algebraMap D.what₂.LL (FractionRing (OcC X j w)))).Splits := by
    refine Polynomial.Splits.of_splits_map (iqC X j w) ?_ fun a ha => ?_
    · change ((p.map (ecC X j w)).map (iqC X j w)).Splits
      rw [hmap]
      exact IsAlgClosed.splits _
    · change a ∈ ((p.map (ecC X j w)).map (iqC X j w)).roots at ha
      rw [hmap] at ha
      have haS : a ∈ S := by
        simp only [S, Finset.coe_sort_coe, Finset.mem_coe, Multiset.mem_toFinset]
        exact ha
      exact iqC_surj X j w a (hF (IntermediateField.subset_adjoin _ _ haS))
  exact iSup_maxGen_baseChange op (fun x y => hcomm j w x.1 x.2 y.1 y.2) hp hsp (v, k)

end GlobalTheory.HeckeSplitField
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

namespace GlobalTheory.HeckeLocN.CondConj

theorem unrAt_of_under_eq {E : Type} [Field E] [NumberField E] [StarRing E] {F : Type} [Field F] [NumberField F] [Algebra F E]
    (hF : ∀ x : F, star (algebraMap F E x) = algebraMap F E x) (hr : Module.finrank F E = 2)
    (hc : ∃ a : E, star a ≠ a) {χ : HChar E} (hχ : χ.TrivOn F) (ht : ∀ P, χ.TameAt P) {P Q : HeightOneSpectrum (𝓞 E)}
    (hPQ : Q.under (𝓞 F) = P.under (𝓞 F)) (hu : χ.UnrAt P) : χ.UnrAt Q := by
  by_cases e : Q = P
  · rwa [e]
  obtain rfl := ((GlobalTheory.NormOneUnit.under_eq_iff hF hr hc P Q).1 hPQ).resolve_left e
  intro x hx
  obtain ⟨k, y, hk, hy, hcong⟩ := (GlobalTheory.localUnit_congr_global E _ x hx).1
  have hv : (Col.conjPrime₂ P).valuation E (k : E) = 1 := by
    rw [hk]
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem _).2 hy
  have hkQ : IsUnitAt (Col.conjPrime₂ P) (atFin (Col.conjPrime₂ P) k) :=
    (Formalism.UG.P.levelaf_valued_algebraMap _ (k : E)).trans hv
  have hxk : IsUnitAt (Col.conjPrime₂ P) (x * (atFin (Col.conjPrime₂ P) k)⁻¹) := by
    unfold IsUnitAt at hx hkQ ⊢
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hx, hkQ, inv_one, one_mul]
  have h1 : χ.loc (Col.conjPrime₂ P) (x * (atFin (Col.conjPrime₂ P) k)⁻¹) = 1 := ht _ _ hxk (by simpa using hcong)
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  have hs0 : star (k : E) ≠ 0 := star_ne_zero.2 k.ne_zero
  have h2 := GlobalTheory.NormOneProd.split_unit hF hr hc hχ ht (Ne.symm e) (y' := Units.mk0 _ hs0) rfl hv
  rw [GlobalTheory.NormOneUnit.locK_unr hu (y := Units.mk0 _ hs0) ((GlobalTheory.CharVal.valuation_conjP P _).symm.trans hv), one_mul] at h2
  exact h1.trans h2

theorem cond_of_under_eq {R : Ranks} (H : Host R) {l : ℕ} {Q : Finset (HeightOneSpectrum (𝓞 H.E))} {χ : HChar H.E}
    (h : IsPsi l Q χ) {v v' : HeightOneSpectrum (𝓞 H.E)} (hv : v.under (𝓞 H.F) = v'.under (𝓞 H.F)) (hQ : v ∈ Q) : v' ∈ Q := by
  letI := H.cmStar
  haveI : IsCMField H.E := H.isCMField_hostE
  by_contra hn
  refine (h.ram v).1 (unrAt_of_under_eq (F := H.F) (fun x => ?_) ?_ ?_ h.triv h.tame hv ((h.ram v').2 hn)) hQ
  · exact IsCMField.complexConj_apply_eq_self H.E x
  · exact Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield H.E) H.E
  · by_contra hh
    push Not at hh
    exact IsCMField.complexConj_ne_one H.E (AlgEquiv.ext hh)

theorem under_eq_of_conj {R : Ranks} (H : Host R) {v v' : HeightOneSpectrum (𝓞 H.E)} (h : IsConjPl H v v') :
    v.under (𝓞 H.F) = v'.under (𝓞 H.F) := by
  ext a
  refine h (algebraMap (𝓞 H.F) (𝓞 H.E) a) (algebraMap (𝓞 H.F) (𝓞 H.E) a) ?_
  haveI : IsCMField H.E := H.isCMField_hostE
  apply H.φ₀.injective
  rw [Formalism.HC.HostAx.conjE_apply, ← IsCMField.complexEmbedding_complexConj]
  exact congrArg H.φ₀ (IsCMField.complexConj_apply_eq_self H.E (a : H.F)).symm

theorem cond_over_conj : ∀ (D : D7) (cf : CharFrame D) (C : NChoice D) (tp : TupTied D cf C), (∀ w, ¬ TwistedAt D w → C.Q w = ∅) → QOver C ∧ QConj C := by
  intro D cf C tp h0
  have key : ∀ w (v v' : PlE D.host), v.under (𝓞 D.host.F) = v'.under (𝓞 D.host.F) → v ∈ C.Q w → v' ∈ C.Q w := by
    intro w v v' hv hQ
    by_cases hw : TwistedAt D w
    · exact cond_of_under_eq D.host (tp.psi_is w hw) hv hQ
    · rw [h0 w hw] at hQ
      exact absurd hQ (Finset.notMem_empty _)
  refine ⟨fun w v v' hQ ⟨v₀, h1, h2⟩ => key w v v' (HeightOneSpectrum.ext (h1.trans h2.symm)) hQ,
    fun w v v' hQ hc => key w v' v (under_eq_of_conj D.host hc).symm hQ⟩

end GlobalTheory.HeckeLocN.CondConj
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TopCh

theorem levFam_chr_exp : ∀ {X : Fields} {n : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 X.E))} (Λ : LevFam X.E X.K n SG), ∃ m : ℕ, 0 < m ∧ ∀ h, Λ.chr h ^ m = 1 := by
  intro X n SG Λ
  have : ∀ w : SG, Finite (𝓞 X.E ⧸ w.1.asIdeal) := fun w => Ideal.finiteQuotientOfFreeOfNeBot _ w.1.ne_bot
  have : Finite ↥Λ.grp := inferInstance
  refine ⟨Nat.card ↥Λ.grp, Nat.card_pos, fun h => ?_⟩
  rw [← map_pow, pow_card_eq_one', map_one]

end GlobalTheory.Mem.Col2.TopCh
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.isotypic_heckeOperator_hyperspecial_acts_by_scalar : ∀ (D : D7) (μ : D.what₂.Tup) (j : ℕ) (Mr : MtReal D μ j) (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))), NG.IsProdLevel Mr.J → NG.HypOutside Mr.J Mr.χ B → ∀ (S : Submodule ℂ (GAf D.host.E D.R.nV → Mr.wt.W)), NG.IsIrrRep Mr.wt.ρ S → ∀ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)) (k : ℕ), s.v ∉ B → IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∃ c : ℂ, ∀ y ∈ (NG.isoTyp Mr.wt.ρ S).comap Mr.real, NG.tN Mr.J s ϖ k (Mr.real y) = c • Mr.real y := by
  first | exact @GlobalTheory.IsoTypScalar.main | exact GlobalTheory.IsoTypScalar.main | (intros; apply GlobalTheory.IsoTypScalar.main <;> assumption)
end

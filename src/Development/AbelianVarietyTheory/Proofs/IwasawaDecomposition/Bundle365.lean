module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
public import Formalism.LocalToGlobal.Columns.Adelic
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAuxiliaryVectorOrthogonalImage
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemberDatumOfFlagTie
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle345
import Formalism.LocalToGlobal.Columns.AdelicLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle337
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle162
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle334
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple

@[expose] public section

section

noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar



namespace GlobalTheory.Mem.Col2.ChiFinTop

open GlobalTheory.Mem.Col2.PtExist

theorem exists_isPtOf_of_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} [NeZero n] {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))} (hQ : Q = ∅)
    {g : GL (Fin n) (AfE F E)} (hg : g ∈ UAd hc n) : ∃ p : DecoF E n ST SG Q, IsPtOf hc g p := by
  classical
  obtain ⟨p, hd, -⟩ := GlobalTheory.Mem.ColAd.exists_near (ST := ST) (SG := SG) (Q := Q) hc 0 hg
  have hN : Formalism.UG.CS.globLat g (stdLat E n) = p.deco.1.N := congrArg Deco.N hd
  refine ⟨p, hg, hN ▸ carries_globLat g, fun P v hv i hi => ?_, fun P v hv i => ?_, fun P => absurd P.2 (by simp [hQ])⟩
  · have e : lastIdx n = i := Fin.ext (by simp [lastIdx]; omega)
    rw [← hN] at hv
    rw [← hd]
    simp only [decoRaw]
    rw [if_pos (le_locP _ _ hv), e]
    exact hasRes_redA _ ((mem_globLat g v).1 hv i)
  · rw [← hN] at hv
    rw [← hd]
    simp only [decoRaw]
    rw [if_pos (le_locP _ _ hv)]
    exact hasRes_redA _ ((mem_globLat g v).1 hv i)

end GlobalTheory.Mem.Col2.ChiFinTop

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TopCh

theorem decoRaw_mul_levelIwahori_reduction {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E)
    {n : ℕ} [NeZero n] (ST SG : Finset (HeightOneSpectrum (𝓞 E))) (g z : GL (Fin n) (AfE F E)) (hz : z ∈ J0 hc n ST) :
    decoRaw ST SG (g * z) = (decoRaw ST SG g).act 1 (redG hc n ST SG ⟨z, hz⟩)⁻¹ := by
  have h := decoRaw_rawSm hc ST SG 1 (⟨z, hz⟩⁻¹ : J0 hc n ST) g
  rw [map_one, map_inv] at h
  have e : Formalism.UG.bc (iA F E) ((1 : URat hc n) : GL (Fin n) E) * g *
      (((⟨z, hz⟩⁻¹ : J0 hc n ST) : J0 hc n ST) : GL (Fin n) (AfE F E))⁻¹ = g * z := by
    simp
  rw [e] at h
  exact h

theorem isPtOf_mul_J0 : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (g z : GL (Fin n) (AfE F E)) (p p' : DecoF E n ST SG Q) (h : GLG (E := E) (n := n) (SG := SG)), (IsPtOf hc g p → IsPtOf hc (g * z) p' → ((∃ hz : z ∈ J0 hc n ST, redG hc n ST SG ⟨z, hz⟩ = h⁻¹) ↔ p'.deco = ((1, h) : UF E n × GLG (E := E) (n := n) (SG := SG)) • p.deco)) ∧ (Q = ∅ → IsPtOf hc g p → ∀ hz : z ∈ J0 hc n ST, redG hc n ST SG ⟨z, hz⟩ = h⁻¹ → IsPtOf hc (g * z) (((1, h, 1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p)) ∧ (Q = ∅ → g ∈ UAd hc n → ∃ q : DecoF E n ST SG Q, IsPtOf hc g q) := by
  intro F E _ _ _ _ _ _ hc n _ ST SG Q g z p p' h
  refine ⟨fun hp hp' => ⟨?_, fun he => ?_⟩, fun hQ hp hz hr => ?_, fun hQ hg => ?_⟩
  · rintro ⟨hz, hr⟩
    apply Subtype.ext
    have h1 := decoRaw_mul_levelIwahori_reduction hc ST SG g z hz
    rw [hr, inv_inv, (near_of_isPtOf hp 0).deco, (near_of_isPtOf hp' 0).deco] at h1
    exact h1
  · have hx : decoRaw ST SG (g * z) = (decoRaw ST SG g).act 1 h := by
      rw [(near_of_isPtOf hp 0).deco, (near_of_isPtOf hp' 0).deco, he]
      rfl
    obtain ⟨hJ, hr⟩ := mem_congruence_of_action hc ST SG hp'.uni hp.uni h hx
    have e : (g * z)⁻¹ * g = z⁻¹ := by group
    have hz : z ∈ J0 hc n ST := by
      have h1 := inv_mem hJ
      rwa [e, inv_inv] at h1
    refine ⟨hz, ?_⟩
    have e' : (⟨(g * z)⁻¹ * g, hJ⟩ : J0 hc n ST) = (⟨z, hz⟩ : J0 hc n ST)⁻¹ := Subtype.ext e
    rw [e', map_inv] at hr
    rw [← hr, inv_inv]
  · refine (GlobalTheory.Mem.Col2.PtDeco.isPtOf_iff_decoRaw F E hc n ST SG Q (g * z) _ hQ).2
      ⟨mul_mem hp.uni (congruence_le_adelic_unitary hc n ST hz), ?_⟩
    have h1 := decoRaw_mul_levelIwahori_reduction hc ST SG g z hz
    rw [hr, inv_inv, (near_of_isPtOf hp 0).deco] at h1
    exact h1.symm
  · obtain ⟨q, hq⟩ := exists_near (ST := ST) (SG := SG) (Q := Q) hc 0 hg
    exact ⟨q, (GlobalTheory.Mem.Col2.PtDeco.isPtOf_iff_decoRaw F E hc n ST SG Q g q hQ).2 ⟨hg, hq.deco.symm⟩⟩

end GlobalTheory.Mem.Col2.TopCh

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoeffRational

theorem conj_closure {G : Type} [Group G] (S : Set G) (γ : G) (h : ∀ n ∈ S, γ * n * γ⁻¹ ∈ S) :
    ∀ n ∈ Subgroup.closure S, γ * n * γ⁻¹ ∈ Subgroup.closure S := by
  have : Subgroup.closure S ≤ (Subgroup.closure S).comap (MulAut.conj γ).toMonoidHom :=
    (Subgroup.closure_le _).2 fun n hn => Subgroup.subset_closure (h n hn)
  exact fun n hn => this hn

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def conjN (N : Subgroup G) (γ : G) (h1 : ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) (h2 : ∀ n ∈ N, γ⁻¹ * n * γ ∈ N) : N ≃ₜ* N where
  toFun n := ⟨γ⁻¹ * n * γ, h2 n n.2⟩
  invFun n := ⟨γ * n * γ⁻¹, h1 n n.2⟩
  left_inv n := Subtype.ext (by simp [mul_assoc])
  right_inv n := Subtype.ext (by simp [mul_assoc])
  map_mul' m n := Subtype.ext (by simp [mul_assoc])
  continuous_toFun := Continuous.subtype_mk (by fun_prop) _
  continuous_invFun := Continuous.subtype_mk (by fun_prop) _

theorem exists_pair [MeasurableSpace G] [BorelSpace G] (N Q : Subgroup G) (γ : G) (hγ : γ ∈ Q)
    (h1 : ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) (h2 : ∀ n ∈ N, γ⁻¹ * n * γ ∈ N) (ν : Measure N) (𝓝 : Set N)
    (hν : ν.IsHaarMeasure) (hF : IsFundamentalDomain (Q.subgroupOf N) 𝓝 ν) (hv : ν 𝓝 = 1) :
    ∃ (ν' : Measure N) (𝓝' : Set N), (ν'.IsHaarMeasure ∧ IsFundamentalDomain (Q.subgroupOf N) 𝓝' ν' ∧ ν' 𝓝' = 1) ∧
      ∀ f : G → ℂ, ∫ n in 𝓝', f n ∂ν' = ∫ n in 𝓝, f (γ⁻¹ * n * γ) ∂ν := by
  let c := conjN N γ h1 h2
  let cm : N ≃ᵐ N := c.toHomeomorph.toMeasurableEquiv
  have hmp : MeasurePreserving cm ν (ν.map cm) := ⟨cm.measurable, rfl⟩
  have hpre : cm ⁻¹' (cm.symm ⁻¹' 𝓝) = 𝓝 := by
    ext x; simp
  refine ⟨ν.map cm, cm.symm ⁻¹' 𝓝, ⟨c.isHaarMeasure_map ν, ?_, ?_⟩, fun f => ?_⟩
  · let e : Q.subgroupOf N → Q.subgroupOf N := fun q =>
      ⟨c q.1, Subgroup.mem_subgroupOf.2 (Q.mul_mem (Q.mul_mem (Q.inv_mem hγ) (Subgroup.mem_subgroupOf.1 q.2)) hγ)⟩
    have he : Function.Bijective e := by
      refine ⟨fun a b h => Subtype.ext (c.injective (congrArg Subtype.val h)), fun q => ?_⟩
      exact ⟨⟨c.symm q.1, Subgroup.mem_subgroupOf.2
        (Q.mul_mem (Q.mul_mem hγ (Subgroup.mem_subgroupOf.1 q.2)) (Q.inv_mem hγ))⟩,
        Subtype.ext (c.apply_symm_apply _)⟩
    refine hF.preimage_of_equiv (hmp.symm cm).quasiMeasurePreserving he fun q x => ?_
    show c.symm (c q.1 * x) = q.1 * c.symm x
    rw [map_mul, c.symm_apply_apply]
  · rw [cm.map_apply, hpre, hv]
  · rw [setIntegral_map_equiv, hpre]
    rfl

end General

section Conj

open GlobalTheory.BesselCompare

variable {D : D7} {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

theorem emb_fix {γ : GA D B} {h : GA D A} (hγ : EmbRel B A ι γ h) {v : B.V} (hv : ∀ x, B.hD v (ι x) = 0) :
    (mt B γ).mulVec (vecA B v) = vecA B v :=
  hγ.2 (co B v) (by funext i; rw [frameMat_eq, cT_mulVec]; exact hv _)

theorem emb_iA {γ : GA D B} {h : GA D A} (hγ : EmbRel B A ι γ h) (t : Fin A.rank → AE D) :
    (mt B γ).mulVec (iA ι t) = iA ι ((mt A h).mulVec t) := by
  unfold iA
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  exact congrArg (fun M => Matrix.mulVec M t) hγ.1

theorem vecA_add (v w : B.V) : vecA B (v + w) = vecA B v + vecA B w := by
  funext k; simp [vecA]

theorem vecA_emb (a : A.V) : vecA B (ι a) = iA ι (vecA A a) := by
  funext k
  have h1 := RingHom.map_mulVec (incA D) (frameMat B A ι) (A.frame.repr a) k
  rw [frameMat, LinearMap.toMatrix_mulVec_repr] at h1
  exact h1

theorem emb_move (hι : HSpace.IsIsomEmb A B ι) {γ : GA D B} {h : GA D A} (hγ : EmbRel B A ι γ h) (x : B.V) :
    ∃ t, (mt B γ).mulVec (vecA B x) = vecA B x + iA ι t := by
  obtain ⟨a, ha⟩ := exists_rep A ((B.hT x).comp ι)
  have h1 : ∀ y, B.hD (x - ι a) (ι y) = 0 := fun y => hD_swap_zero (by
    show B.hT (x - ι a) (ι y) = 0
    rw [map_sub, LinearMap.sub_apply, hι a y, ha, LinearMap.comp_apply, sub_self])
  have h2 : vecA B x = vecA B (x - ι a) + iA ι (vecA A a) := by
    rw [← vecA_emb, ← vecA_add, sub_add_cancel]
  refine ⟨(mt A h).mulVec (vecA A a) + -vecA A a, ?_⟩
  rw [h2, Matrix.mulVec_add, emb_fix hγ h1, emb_iA hγ, iA_add, iA_neg]
  abel


theorem conj_NSet (d : BesselDatum A B ι) {γ : GA D B} {h h' : GA D A} (hγ : EmbRel B A ι γ h)
    (hγ' : EmbRel B A ι γ⁻¹ h') {n : GA D B} (hn : n ∈ d.NSet) : γ * n * γ⁻¹ ∈ d.NSet := by
  have hsum : ∀ c : Fin d.ρ → AE D, (mt B γ).mulVec (∑ l, c l • vecA B (d.e l)) = ∑ l, c l • vecA B (d.e l) := by
    intro c

    rw [← Matrix.mulVecLin_apply, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, Matrix.mulVecLin_apply, emb_fix hγ (d.eA l)]
  refine ⟨fun i => ?_, fun x hx => ?_⟩
  · obtain ⟨c, hc, e⟩ := hn.1 i
    refine ⟨c, hc, ?_⟩
    unfold actV at e ⊢
    rw [mulVec_mul, mulVec_mul, emb_fix hγ' (d.eA i), e, Matrix.mulVec_add, emb_fix hγ (d.eA i), hsum]
  · obtain ⟨t, ht⟩ := emb_move d.isom hγ' x
    obtain ⟨c, e⟩ := hn.2 x hx
    choose a ha using fun k => hn.2 (ι (A.frame k)) fun i => hD_swap_zero (d.eA i _)
    unfold actV at e ha ⊢
    have e2 : (mt B n).mulVec (iA ι t) = iA ι t + ∑ l, (∑ k, t k * a k l) • vecA B (d.e l) := by

      rw [iA, frameMat_eq, eMat_mulVec, ← Matrix.mulVecLin_apply, map_sum]
      simp only [map_smul, Matrix.mulVecLin_apply, ha, smul_add, Finset.sum_add_distrib, Finset.smul_sum,
        Finset.sum_smul, smul_smul]
      rw [Finset.sum_comm]
    refine ⟨fun l => c l + ∑ k, t k * a k l, ?_⟩
    have e3 : (mt B n).mulVec ((mt B γ⁻¹).mulVec (vecA B x)) =
        (mt B γ⁻¹).mulVec (vecA B x) + ∑ l, (c l + ∑ k, t k * a k l) • vecA B (d.e l) := by
      rw [ht, Matrix.mulVec_add, e, e2]
      simp only [add_smul, Finset.sum_add_distrib]
      abel
    rw [mulVec_mul, mulVec_mul, e3, Matrix.mulVec_add]
    exact congrArg₂ (· + ·) (mulVec_cancel_inv γ (vecA B x)) (hsum fun l => c l + ∑ k, t k * a k l)

theorem conj_N (d : BesselDatum A B ι) {γ : GA D B} {h h' : GA D A} (hγ : EmbRel B A ι γ h)
    (hγ' : EmbRel B A ι γ⁻¹ h') : ∀ n ∈ d.N, γ * n * γ⁻¹ ∈ d.N := by
  have h1 : ∀ n ∈ d.NSet, γ * n * γ⁻¹ ∈ d.NSet := fun n hn => conj_NSet d hγ hγ' hn
  have h2 := conj_closure (G := GA D B) d.NSet γ h1
  unfold BesselDatum.N
  exact h2

theorem psiN_conj (d : BesselDatum A B ι) (ψ : AddChar (AF D.host.F) ℂ) {γ : GA D B} {h : GA D A}
    (hγ : EmbRel B A ι γ h) (n : GA D B) : d.psiN ψ (γ⁻¹ * n * γ) = d.psiN ψ n := by
  unfold BesselDatum.psiN BesselDatum.simpleSum actV
  congr 3
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mulVec_mul, mulVec_mul, emb_fix hγ (besselDatum_auxiliaryVector_orthogonal_image d _), hA_mt_left, inv_inv, emb_fix hγ (d.fA i)]

end Conj

theorem coeff_rational : ∀ (D : D7) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesselDatum A B ι) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ F : GA D B → ℂ, (∀ γ ∈ GQ B, ∀ g, F (γ * g) = F g) → ∀ ν 𝓝, d.IsUnitPair ν 𝓝 → ∀ γ h, EmbRel B A ι γ h → γ ∈ GQ B → ∀ g, d.coeff ψ ν 𝓝 F (γ * g) = d.coeff ψ ν 𝓝 F g := by
  intro D A B ι d ψ hψ F hF ν 𝓝 hν γ h hγ hQ g
  haveI : BorelSpace (GA D B) := ⟨rfl⟩
  haveI : IsTopologicalGroup (GA D B) := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B).2.2.2.2.1
  obtain ⟨s, -, hs, -⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D B A ι d.isom
  have hγ' : EmbRel B A ι γ⁻¹ h⁻¹ := by
    rw [hs] at hγ ⊢
    rw [hγ, map_inv]
  have h1 := conj_N d hγ hγ'
  have h2 : ∀ n ∈ d.N, γ⁻¹ * n * γ ∈ d.N := fun n hn => by
    have := conj_N d hγ' (by rwa [inv_inv]) n hn
    rwa [inv_inv] at this
  obtain ⟨ν', 𝓝', hν', hint⟩ := exists_pair d.N (GQ B) γ hQ h1 h2 ν 𝓝 hν.1 hν.2.1 hν.2.2
  have e := congrFun ((GlobalTheory.Mem.BesselCoeffIndep.coeff_indep_and_equivariant D A B ι d ψ hψ F hF ν 𝓝 hν).1 ν' 𝓝' hν') g
  rw [← e]
  unfold BesselDatum.coeff
  rw [hint fun n => F (n * g) * star (d.psiN ψ n)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun n => ?_)
  show F (n * (γ * g)) * star (d.psiN ψ n) = F (γ⁻¹ * n * γ * g) * star (d.psiN ψ (γ⁻¹ * n * γ))
  rw [psiN_conj d ψ hγ, mul_assoc, mul_assoc, hF _ ((GQ B).inv_mem hQ)]

end GlobalTheory.CoeffRational

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RootExch.ExStruct

open GlobalTheory.BesselCompare (mt_mul mt_one hA_add hA_smul hA_smul_right hA_vec cA_inc)

variable {D : D7} {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

theorem hA_half {ε : AE D} {y : Fin B.rank → AE D} (hy : ε • y = y) (x) : hA B x y = cA D ε * hA B x y := by
  rw [← hA_smul_right, hy]

theorem eps_hA {ε : AE D} (h0 : ε * cA D ε = 0) {y : Fin B.rank → AE D} (hy : ε • y = y) (x) :
    ε * hA B x y = 0 := by
  rw [hA_half hy, ← mul_assoc, h0, zero_mul]

theorem hA_smul_zero {ε : AE D} (h0 : ε * cA D ε = 0) {y y' : Fin B.rank → AE D} (hy : ε • y = y)
    (hy' : ε • y' = y') (x) : hA B x y' • y = 0 := by
  rw [← hy, smul_smul, mul_comm, eps_hA h0 hy', zero_smul]

theorem hA_halves {ε : AE D} (h0 : ε * cA D ε = 0) {y y' : Fin B.rank → AE D} (hy : ε • y = y)
    (hy' : ε • y' = y') : hA B y y' = 0 := by
  rw [← hy, hA_smul, eps_hA h0 hy']

theorem isK_mul {ε : AE D} (h0 : ε * cA D ε = 0) {v y y' : Fin B.rank → AE D} (hy : ε • y = y)
    (hy' : ε • y' = y') (hv' : hA B y' v = 0) (hv : hA B v y = 0) {k k' : GA D B} (hk : IsK B v y k)
    (hk' : IsK B v y' k') : IsK B v (y + y') (k * k') := by
  intro x
  rw [mulVec_mul, hk', hk]
  simp only [hA_add, hA_sub, hA_smul, hA_add_right, hv, hv', hA_halves h0 hy' hy, mul_zero, add_zero, sub_zero,
    add_smul, smul_add, mul_comm (hA B x y'), mul_smul, hA_smul_zero h0 hy hy', smul_zero, zero_smul]
  abel

theorem isK_eps {ε : AE D} (h0 : ε * cA D ε = 0) {v y : Fin B.rank → AE D} (hy : ε • y = y) {k : GA D B}
    (hk : IsK B v y k) (x) : ε • ((mt B k).mulVec x - x) = -(hA B x v • y) := by
  rw [hk, add_sub_assoc, add_sub_cancel_left, smul_sub, smul_smul, eps_hA h0 hy, zero_smul, zero_sub, smul_comm, hy]

theorem isK_supp {ε : AE D} (h1 : ε * ε = ε) (h0 : ε * cA D ε = 0) {v y : Fin B.rank → AE D} (hy : ε • y = y)
    {k : GA D B} (hk : IsK B v y k) : SuppAt ε B k := by
  rw [suppAt_iff_vec]
  intro x
  have hc : cA D ε • y = 0 := by rw [← hy, smul_smul, mul_comm, h0, zero_smul]
  rw [add_smul, isK_eps h0 hy hk, hk, add_sub_assoc, add_sub_cancel_left, smul_sub, smul_smul, ← hA_half hy,
    smul_comm, hc, smul_zero]
  abel

theorem eq_one_of_half {ε : AE D} {u : GA D B} (hu : SuppAt ε B u) (h : ∀ x, ε • ((mt B u).mulVec x - x) = 0) :
    u = 1 := by
  refine mt_ext fun x => ?_
  rw [mt_one, Matrix.one_mulVec, ← sub_eq_zero, ← suppAt_iff_vec.1 hu x, add_smul, h, zero_add]
  refine hA_nondeg fun y => ?_
  have e : (mt B u).mulVec (ε • y) = ε • y := by
    have := h y
    rwa [smul_sub, sub_eq_zero, ← Matrix.mulVec_smul] at this
  rw [hA_smul, ← hA_smul_right, hA_sub]
  conv_lhs => rw [← e]
  rw [hA_mt, e, sub_self]

theorem iA_eq (t : Fin A.rank → AE D) : iA ι t = ∑ l, t l • vecA B (ι (A.frame l)) := by
  rw [iA, GlobalTheory.BesselCompare.frameMat_eq, GlobalTheory.BesselCompare.eMat_mulVec]

theorem dual_iA (d : BesselDatum A B ι) (i) (t) : hA B (vecA B (dual d i)) (iA ι t) = 0 :=
  hA_vec_iA (dual_perp d i) t

theorem iA_dual (d : BesselDatum A B ι) (i) (t) : hA B (iA ι t) (vecA B (dual d i)) = 0 := by
  rw [← hA_herm, dual_iA, map_zero]

theorem vec_dual (d : BesselDatum A B ι) (i) (x : A.V) : hA B (vecA B (ι x)) (vecA B (dual d i)) = 0 := by
  rw [← hA_herm, hA_vec, dual_perp, map_zero, map_zero]

theorem mem_exSet (d : BesselDatum A B ι) {ε : AE D} (h1 : ε * ε = ε) (h0 : ε * cA D ε = 0) (i) {t} (ht : ε • t = t)
    {k : GA D B} (hk : IsK B (vecA B (dual d i)) (iA ι t) k) :
    SuppAt ε B k ∧
    (∀ x : A.V, ε • (actV B k (ι x) - vecA B (ι x)) = 0) ∧
    (∀ l, ε • (actV B k (d.f l) - vecA B (d.f l)) = 0) ∧
    (∀ l, l ≠ i → ε • (actV B k (d.aux l) - vecA B (d.aux l)) = 0) ∧
      ε • (actV B k (d.aux i) - vecA B (d.aux i)) = -iA ι t := by
  have hy : ε • iA ι t = iA ι t := by rw [← iA_smul, ht]
  obtain ⟨p1, p2, -⟩ := GlobalTheory.T.besselDatum_adelicVector_decomposition D A B ι d
  unfold actV
  refine ⟨isK_supp h1 h0 hy hk, fun x => ?_, fun l => ?_, fun l hl => ?_, ?_⟩
  · rw [isK_eps h0 hy hk, vec_dual, zero_smul, neg_zero]
  · rw [isK_eps h0 hy hk, hA_vec, p2, map_zero, zero_smul, neg_zero]
  · rw [isK_eps h0 hy hk, hA_vec, p1, if_neg hl, map_zero, zero_smul, neg_zero]
  · rw [isK_eps h0 hy hk, hA_vec, p1, if_pos rfl, map_one, one_smul]

theorem exists_k (d : BesselDatum A B ι) {ε : AE D} (h0 : ε * cA D ε = 0) (i) {t} (ht : ε • t = t) :
    ∃ k : GA D B, IsK B (vecA B (dual d i)) (iA ι t) k := by
  obtain ⟨K, -, hK⟩ := GlobalTheory.T.exists_continuous_unitaryRootExchangeMap D B ε h0 (vecA B (dual d i))
  exact ⟨_, hK ⟨iA ι t, by rw [← iA_smul, ht], dual_iA d i t⟩⟩

theorem isK_one (v : Fin B.rank → AE D) : IsK B v 0 1 := fun x => by
  rw [mt_one, Matrix.one_mulVec, hA_zero_right, zero_smul, smul_zero, add_zero, sub_zero]

theorem isK_unique {v y : Fin B.rank → AE D} {k k' : GA D B} (h : IsK B v y k) (h' : IsK B v y k') : k = k' :=
  mt_ext fun x => (h x).trans (h' x).symm

def kGrp (d : BesselDatum A B ι) {ε : AE D} (h0 : ε * cA D ε = 0) (i : Fin (d.ρ + 1)) : Subgroup (GA D B) where
  carrier := {g | ∃ t, ε • t = t ∧ IsK B (vecA B (dual d i)) (iA ι t) g}
  one_mem' := ⟨0, smul_zero _, by rw [iA, Matrix.mulVec_zero]; exact isK_one _⟩
  mul_mem' := by
    rintro g g' ⟨t, ht, hg⟩ ⟨t', ht', hg'⟩
    refine ⟨t + t', by rw [smul_add, ht, ht'], ?_⟩
    rw [iA_add]
    exact isK_mul h0 (by rw [← iA_smul, ht]) (by rw [← iA_smul, ht']) (iA_dual d i _) (dual_iA d i _) hg hg'
  inv_mem' := by
    rintro g ⟨t, ht, hg⟩
    have ht' : ε • (-t) = -t := by rw [smul_neg, ht]
    obtain ⟨k, hk⟩ := exists_k d h0 i ht'
    have := isK_mul h0 (by rw [← iA_smul, ht]) (by rw [← iA_smul, ht']) (iA_dual d i _) (dual_iA d i _) hg hk
    rw [iA_neg, add_neg_cancel] at this
    rw [inv_eq_of_mul_eq_one_right (isK_unique this (isK_one _))]
    exact ⟨-t, ht', hk⟩

theorem mulVec_comb (L : Matrix (Fin B.rank) (Fin B.rank) (AE D)) {a : ℕ} (u : Fin a → Fin B.rank → AE D)
    (hu : ∀ i, L.mulVec (u i) = 0) (r : Fin a → AE D) : L.mulVec (∑ i, r i • u i) = 0 := by
  refine Finset.sum_induction _ (fun x => L.mulVec x = 0) (fun x y hx hy => ?_) (Matrix.mulVec_zero _) fun i _ => ?_
  · rw [Matrix.mulVec_add, hx, hy, add_zero]
  · rw [Matrix.mulVec_smul, hu, smul_zero]

theorem mulVec_zero_of (d : BesselDatum A B ι) (L : Matrix (Fin B.rank) (Fin B.rank) (AE D))
    (a1 : ∀ x, L.mulVec (vecA B (ι x)) = 0) (a2 : ∀ l, L.mulVec (vecA B (d.f l)) = 0)
    (a3 : ∀ l, L.mulVec (vecA B (d.aux l)) = 0) (x) : L.mulVec x = 0 := by
  obtain ⟨t, e⟩ := (GlobalTheory.T.besselDatum_adelicVector_decomposition D A B ι d).2.2 x
  rw [e, iA_eq, Matrix.mulVec_add, Matrix.mulVec_add, mulVec_comb L _ (fun l => a1 (A.frame l)),
    mulVec_comb L _ a3, mulVec_comb L _ a2, add_zero, add_zero]

theorem eq_of_half {ε : AE D} {g k : GA D B} (g1 : SuppAt ε B g) (k1 : SuppAt ε B k)
    (h : ∀ x, ε • ((mt B g).mulVec x - x) = ε • ((mt B k).mulVec x - x)) : k = g := by
  refine inv_mul_eq_one.1 (eq_one_of_half (suppAt_mul (suppAt_inv k1) g1) fun x => ?_)
  have e : ε • (mt B g).mulVec x = ε • (mt B k).mulVec x := by
    have := h x
    rwa [smul_sub, smul_sub, sub_left_inj] at this
  have := congrArg (mt B k⁻¹).mulVec e
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, mulVec_inv_cancel, ← mulVec_mul] at this
  rw [smul_sub, this, sub_self]


theorem exSet_sub (d : BesselDatum A B ι) {ε : AE D} (h1 : ε * ε = ε) (h0 : ε * cA D ε = 0) (i) {g : GA D B}
    (hg : g ∈ d.ExSet ε i) : g ∈ kGrp d h0 i := by
  obtain ⟨g1, g2, g3, g4, y, g5⟩ := hg
  have ht : ε • (-(ε • y)) = -(ε • y) := by rw [smul_neg, smul_smul, h1]
  obtain ⟨k, hk⟩ := exists_k d h0 i ht
  obtain ⟨k1, k2, k3, k4, k5⟩ := mem_exSet d h1 h0 i ht hk
  obtain ⟨L, hL⟩ : ∃ L : Matrix (Fin B.rank) (Fin B.rank) (AE D),
      ∀ x, L.mulVec x = ε • ((mt B g).mulVec x - x) - ε • ((mt B k).mulVec x - x) :=
    ⟨ε • (mt B g - mt B k), fun x => by
      rw [← smul_sub, sub_sub_sub_cancel_right, ← Matrix.sub_mulVec, ← Matrix.smul_mulVec]⟩
  have a1 : ∀ x, L.mulVec (vecA B (ι x)) = 0 := fun x => by
    rw [hL]; exact sub_eq_zero.2 ((g2 x).trans (k2 x).symm)
  have a2 : ∀ l, L.mulVec (vecA B (d.f l)) = 0 := fun l => by
    rw [hL]; exact sub_eq_zero.2 ((g3 l).trans (k3 l).symm)
  have a3 : ∀ l, L.mulVec (vecA B (d.aux l)) = 0 := fun l => by
    rw [hL]
    by_cases hl : l = i
    · subst hl
      refine sub_eq_zero.2 (g5.trans (Eq.symm (k5.trans ?_)))
      rw [iA_neg, neg_neg, iA_smul]; rfl
    · exact sub_eq_zero.2 ((g4 l hl).trans (k4 l hl).symm)
  have a4 : ∀ x, L.mulVec x = 0 := mulVec_zero_of d L a1 a2 a3
  rw [← eq_of_half g1 k1 fun x => sub_eq_zero.1 ((hL x).symm.trans (a4 x))]
  exact ⟨_, ht, hk⟩

theorem mem_Ex_iff : ∀ (D : D7) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesselDatum A B ι) (ε : AE D), IsSplitIdem D ε → ∀ (i : Fin (d.ρ + 1)) (g : GA D B), g ∈ d.Ex ε i ↔ ∃ t, ε • t = t ∧ IsK B (vecA B (dual d i)) (iA ι t) g := by
  intro D A B ι d ε he i g
  have h1 : ε * ε = ε := he.1
  have h0 : ε * cA D ε = 0 := he.2.1
  refine ⟨fun hg => (Subgroup.closure_le (kGrp d h0 i)).2 (fun _ h => exSet_sub d h1 h0 i h) hg, ?_⟩
  rintro ⟨t, ht, hk⟩
  obtain ⟨k1, k2, k3, k4, k5⟩ := mem_exSet d h1 h0 i ht hk
  refine Subgroup.subset_closure ⟨k1, k2, k3, k4, -t, k5.trans ?_⟩
  show _ = ε • iA ι (-t)
  rw [← iA_smul, smul_neg, ht, iA_neg]

end GlobalTheory.RootExch.ExStruct

end
end

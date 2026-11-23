module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle412
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle155
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle094
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle404
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle415
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle414
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle153
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle120
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle433
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle306
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.PicardGroup
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
import Formalism.LocalToGlobal.IndefiniteReal.SelfDualFullLattice
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.OntoModPf

open NumberField

variable {K : Type} [Field K] [NumberField K]

theorem selfDual_isFullLattice {D : D7} : ∀ (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    IsSelfDualC V Λ → Submodule.IsFullLattice D.host.E Λ := by
  intro V Λ hΛ
  exact Formalism.IndefR.Datum.IsSelfDualC.isFullLattice V Λ hΛ

theorem exists_basis_in_lattice {n : ℕ} (Λ : Submodule (𝓞 K) (Fin n → K)) [hΛ : Λ.IsFullLattice K] (N : ℕ) (hN : 2 ≤ N) :
    ∃ b : Module.Basis (Fin n) K (Fin n → K), (∀ i, b i ∈ Λ) ∧ ∃ c : 𝓞 K, IsCoprime c (N : 𝓞 K) ∧
      ∀ w ∈ Λ, (c : K) • w ∈ Submodule.span (𝓞 K) (Set.range b) := by
  haveI : Module.Finite (𝓞 K) Λ := Module.Finite.iff_fg.2 hΛ.fg
  haveI : Module.Finite ℤ Λ := Module.Finite.trans (𝓞 K) Λ
  haveI : HasUniqueDiv Λ := ⟨fun k hk a b h => Subtype.ext
    (nsmul_right_injective hk (by simpa using congrArg Subtype.val h))⟩
  obtain ⟨r, x, hli, c, hc0, hcop, hspan⟩ := GlobalTheory.CoprimeBasis.exists_coprime_basis K Λ N hN
  set x' : Fin r → (Fin n → K) := fun i => (x i : Fin n → K) with hx'
  have hli' : LinearIndependent (𝓞 K) x' := hli.map' Λ.subtype (Submodule.ker_subtype Λ)
  have hliK : LinearIndependent K x' := (LinearIndependent.iff_fractionRing (𝓞 K) K).mp hli'
  have hmem : ∀ w ∈ Λ, (c : K) • w ∈ Submodule.span (𝓞 K) (Set.range x') := by
    intro w hw
    have h := Submodule.mem_map_of_mem (f := Λ.subtype) (hspan ⟨w, hw⟩)
    rw [Submodule.map_span, ← Set.range_comp] at h
    have e : (Λ.subtype (c • (⟨w, hw⟩ : Λ))) = (c : K) • w := by
      simp [Submodule.coe_smul, algebraMap_smul]
    rw [e] at h
    exact h
  have hcK : (c : K) ≠ 0 := by exact_mod_cast hc0
  have hspanK : ⊤ ≤ Submodule.span K (Set.range x') := by
    rw [← hΛ.span_eq_top, Submodule.span_le]
    intro w hw
    have h1 := Submodule.span_le_restrictScalars (𝓞 K) K (Set.range x') (hmem w hw)
    have h2 := Submodule.smul_mem (Submodule.span K (Set.range x')) (c : K)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hcK, one_smul] at h2
  let b0 : Module.Basis (Fin r) K (Fin n → K) := Module.Basis.mk hliK hspanK
  have hr : r = n := by
    have := Module.finrank_eq_card_basis b0
    simpa using this.symm
  subst hr
  refine ⟨b0, fun i => ?_, c, hcop, fun w hw => ?_⟩
  · rw [Module.Basis.mk_apply]; exact (x i).2
  · have : Set.range b0 = Set.range x' := by rw [Module.Basis.coe_mk]
    rw [this]; exact hmem w hw

end GlobalTheory.OntoModPf

namespace GlobalTheory.OntoModPf

open NumberField

variable {K : Type} [Field K] [NumberField K]


open Matrix in
theorem exists_onto_mod {n n' : ℕ} (hnn : n ≤ n') (Λ : Submodule (𝓞 K) (Fin n → K)) (Λ' : Submodule (𝓞 K) (Fin n' → K))
    [Λ.IsFullLattice K] [Λ'.IsFullLattice K] (𝔪 : Ideal (𝓞 K)) (h𝔪 : 𝔪 ≠ ⊥) :
    ∃ x : Matrix (Fin n) (Fin n') K, (∀ w ∈ Λ', x *ᵥ w ∈ Λ) ∧ ∃ y : Matrix (Fin n') (Fin n) K, (∀ v ∈ Λ, y *ᵥ v ∈ Λ') ∧
      ∃ a ∈ 𝔪, x * y - 1 = (a : K) • (1 : Matrix (Fin n) (Fin n) K) := by
  classical
  set N : ℕ := 2 * Ideal.absNorm 𝔪 with hNdef
  have hN0 : Ideal.absNorm 𝔪 ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have hN : 2 ≤ N := by omega
  have hNm : (N : 𝓞 K) ∈ 𝔪 := by
    rw [hNdef, Nat.cast_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.absNorm_mem 𝔪)
  obtain ⟨b, hb, c, hc, hcb⟩ := exists_basis_in_lattice Λ N hN
  obtain ⟨b', hb', c', hc', hcb'⟩ := exists_basis_in_lattice Λ' N hN
  obtain ⟨u, v, huv⟩ := hc.mul_left hc'
  let φ : (Fin n' → K) →ₗ[K] (Fin n → K) := b'.constr K fun j => if h : (j : ℕ) < n then b ⟨j, h⟩ else 0
  let ψ : (Fin n → K) →ₗ[K] (Fin n' → K) := b.constr K fun i => b' (Fin.castLE hnn i)
  have hφψ : φ ∘ₗ ψ = LinearMap.id := by
    refine b.ext fun i => ?_
    show φ (ψ (b i)) = b i
    simp only [φ, ψ, Module.Basis.constr_basis, Fin.coe_castLE]
    rw [dite_eq_left i.isLt]
  have hφ : Submodule.span (𝓞 K) (Set.range b') ≤ Λ.comap (φ.restrictScalars (𝓞 K)) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    show φ (b' j) ∈ Λ
    simp only [φ, Module.Basis.constr_basis]
    split_ifs
    · exact hb _
    · exact Λ.zero_mem
  have hψ : Submodule.span (𝓞 K) (Set.range b) ≤ Λ'.comap (ψ.restrictScalars (𝓞 K)) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    show ψ (b i) ∈ Λ'
    simp only [ψ, Module.Basis.constr_basis]
    exact hb' _
  refine ⟨LinearMap.toMatrix' (((u * c' : 𝓞 K) : K) • φ), fun w hw => ?_,
    LinearMap.toMatrix' ((c : K) • ψ), fun w hw => ?_, u * c * c' - 1, ?_, ?_⟩
  · rw [LinearMap.toMatrix'_mulVec, LinearMap.smul_apply]
    have h1 : φ ((c' : K) • w) ∈ Λ := hφ (hcb' w hw)
    have h2 := Λ.smul_mem u h1
    rw [← algebraMap_smul K u, map_smul, smul_smul] at h2
    convert h2 using 2
    push_cast; ring
  · rw [LinearMap.toMatrix'_mulVec, LinearMap.smul_apply, ← map_smul]
    exact hψ (hcb w hw)
  · have : u * c * c' - 1 = -(v * (N : 𝓞 K)) := by linear_combination huv
    rw [this]
    exact neg_mem (Ideal.mul_mem_left _ _ hNm)
  · rw [← LinearMap.toMatrix'_comp]
    have e : (((u * c' : 𝓞 K) : K) • φ) ∘ₗ ((c : K) • ψ) = ((u * c * c' : 𝓞 K) : K) • LinearMap.id := by
      rw [LinearMap.smul_comp, LinearMap.comp_smul, hφψ, smul_smul]
      congr 1; push_cast; ring
    rw [e, map_smul, LinearMap.toMatrix'_id]
    push_cast
    rw [sub_smul, one_smul]

end GlobalTheory.OntoModPf

namespace GlobalTheory.OntoModPf

open NumberField Matrix

theorem ontoModEx : OntoModEx := by
  intro D _ T L μ0 _ sc G W M _ i hi
  have h0 := G.sp.P_is i hi.le
  have h1 := G.sp.P_is (i + 1) hi
  haveI : (G.Λ (.core i)).IsFullLattice D.host.E := selfDual_isFullLattice _ _ h0.sd
  haveI : (G.Λ (.core (i + 1))).IsFullLattice D.host.E := selfDual_isFullLattice _ _ h1.sd
  have e0 : (G.V (.core i)).rank = rankP D i := h0.rank
  have e1 : (G.V (.core (i + 1))).rank = rankP D (i + 1) := h1.rank
  have hle : (G.V (.core i)).rank ≤ (G.V (.core (i + 1))).rank := by
    rw [e0, e1]; unfold rankP; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ i)) _
  obtain ⟨x, hx, y, hy, a, ha, hxy⟩ :=
    exists_onto_mod hle (G.Λ (.core i)) (G.Λ (.core (i + 1))) G.modul (G.pl.modul_ne_bot sc)
  refine ⟨x, hx, y, hy, ?_⟩
  have h1m : (1 : Matrix (Fin (G.V (.core i)).rank) (Fin (G.V (.core i)).rank) D.host.E) ∈
      homLat (G.Λ (.core i)) (G.Λ (.core i)) := fun v hv => by simpa using hv
  have e : x * y - 1 = a • (1 : Matrix (Fin (G.V (.core i)).rank) (Fin (G.V (.core i)).rank) D.host.E) := by
    rw [hxy]; exact algebraMap_smul D.host.E a _
  rw [e]
  exact Submodule.smul_mem_smul ha h1m

end GlobalTheory.OntoModPf
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ShortLineCusp

theorem sum_sqrt_le (ι : Type) [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ∑ i, Real.sqrt (a i) ≤ Real.sqrt (Fintype.card ι) * Real.sqrt (∑ i, a i) := by
  have h1 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) (fun i => Real.sqrt (a i))
  simp only [one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, one_mul,
    Real.sq_sqrt (ha _)] at h1
  rw [← Real.sqrt_mul (Nat.cast_nonneg _)]
  apply Real.le_sqrt_of_sq_le
  simpa [Real.sq_sqrt (ha _)] using h1

theorem sum_sqrt_add_le : ∀ (ι : Type) [Fintype ι] (a b : ι → ℝ), (∀ i, 0 ≤ a i) → (∀ i, 0 ≤ b i) → ∑ i, (Real.sqrt (a i) + Real.sqrt (b i)) ≤ Real.sqrt (Fintype.card ι) * (Real.sqrt (∑ i, a i) + Real.sqrt (∑ i, b i)) := by
  intro ι _ a b ha hb
  rw [Finset.sum_add_distrib, mul_add]
  exact add_le_add (sum_sqrt_le ι a ha) (sum_sqrt_le ι b hb)

theorem finrank_eq_card_and_rd : ∀ D : D7, Module.finrank ℚ D.host.F = Fintype.card D.what₂.Tau ∧ |(discr D.host.E : ℝ)| ^ ((1 : ℝ) / (2 * (Module.finrank ℚ D.host.F : ℝ))) = rdisc D := by
  intro D
  haveI := D.sp.cm.totReal
  refine ⟨?_, ?_⟩
  · rw [Fintype.card_congr (Formalism.L2.Host.tauPl D), ← NumberField.InfinitePlace.card_add_two_mul_card_eq_rank,
      NumberField.IsTotallyReal.nrComplexPlaces_eq_zero, mul_zero, add_zero,
      NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      NumberField.IsTotallyReal.nrComplexPlaces_eq_zero, add_zero]
  · unfold rdisc
    rw [← Module.finrank_mul_finrank ℚ D.host.F D.host.E, D.sp.cm.deg2]
    congr 1
    push_cast
    ring

theorem least_nonneg : ∀ (I : Formalism.MainNotions.S.AutInst) (x : I.GA), 0 ≤ GlobalTheory.Count.least I x := by
  intro I x
  unfold GlobalTheory.Count.least Formalism.HN.leastSize
  apply Real.sInf_nonneg
  rintro t ⟨R, -, -, rfl⟩
  unfold Formalism.HN.size Formalism.HN.ht Formalism.F.covol
  apply Real.rpow_nonneg
  apply mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg (abs_nonneg _) _))
  split_ifs <;> positivity

attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem norm_le_of_not_long : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (A : Fr V) (Λ : Lat V), IsSelfDualC V Λ → ∀ (g q : ℕ), 1 ≤ g → 1 ≤ q → 1 ≤ V.rank → (∀ τ, min (Finset.univ.filter fun a => A.ε τ a = true).card (Finset.univ.filter fun a => A.ε τ a = false).card ≤ q) → ∀ φ : GA D V → ℂ, IsAutFun V φ → IsCuspFun V φ → (∀ k ∈ Lev.levA V (congLev D.sp.cm V.gram Λ (Ideal.span {((g : ℕ) : 𝓞 D.host.E)})), ∀ x, φ (x * k) = φ x) → ∀ c : ℝ, 0 ≤ c → Lip θ A φ c → ∀ (x : GA D V) (s : ℝ), 0 < s → s ≤ 1 / 2 → ¬ Long θ A Λ x s → ‖φ x‖ ≤ c * ((V.rank : ℝ) ^ 2 * Fintype.card D.what₂.Tau * g * rdisc D * (2 * s) ^ ((1 : ℝ) / q)) := by
  intro D θ hθ V A Λ hΛ g q hg hq hn hrk φ hφ hcusp hlev c hc hlip x s hs hs2 hlong
  obtain ⟨fr, hfrΛ, hfr⟩ := GlobalTheory.T.exists_instanceFrames_of_diagonalFrame_selfDual D V A Λ hΛ
  subst hfrΛ
  obtain ⟨hfF, hrdE⟩ := finrank_eq_card_and_rd D
  have hfI : (Formalism.IndefR.Eqv.UI.instV fr).f = Fintype.card D.what₂.Tau := hfF
  have hrdI : (Formalism.IndefR.Eqv.UI.instV fr).rd = rdisc D := hrdE
  set x0 := (Formalism.IndefR.Eqv.UI.brg fr).symm x with hx0
  have hbx : Formalism.IndefR.Eqv.UI.brg fr x0 = x := by simp [hx0]
  have hl0 : 0 ≤ GlobalTheory.Count.least (Formalism.IndefR.Eqv.UI.instV fr) x0 := least_nonneg _ x0
  have hlt : GlobalTheory.Count.least (Formalism.IndefR.Eqv.UI.instV fr) x0 < s := by
    by_contra hge
    push_neg at hge
    apply hlong
    intro 𝔪 h𝔪 w hw hw0
    have hL := GlobalTheory.T.adelicPointRationalLattice_unitaryModelIso_eq D V fr x0
    rw [hbx] at hL
    rw [hL] at hw
    have h1 := GlobalTheory.T.leastSize_pow_mul_sqrt_absNorm_le_prod_norms (Formalism.IndefR.Eqv.UI.instV fr) x0 𝔪 h𝔪 w hw hw0
    rw [GlobalTheory.T.rationalVectorNorm_adelicPoint_twoModels_eq D θ hθ V A fr (fun τ => (hfr τ).2) x0 w, hbx, hfI] at h1
    exact le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs.le hge _) (Real.sqrt_nonneg _)) h1
  have hrkI : ∀ v, GlobalTheory.Count.rkR ((Formalism.IndefR.Eqv.UI.instV fr).ε v) ≤ q := by
    intro (v : InfinitePlace D.host.F)
    have h := (hfr ((Formalism.L2.Host.tauPl D).symm v)).1
    have e : (Formalism.L2.Host.tauPl D) ((Formalism.L2.Host.tauPl D).symm v) = v := Equiv.apply_symm_apply _ _
    rw [e] at h
    show GlobalTheory.Count.rkR (fr.ε v) ≤ q
    rw [h]
    exact hrk _
  obtain ⟨W, hW, hmv⟩ := GlobalTheory.T.automorphicPoint_exists_isotropic_reduction_of_small_size (Formalism.IndefR.Eqv.UI.instV fr) x0 g q hg hq hn hrkI (hlt.trans_le hs2)
  obtain ⟨hGQ, -, hN⟩ := GlobalTheory.BridgeDict.bridge_dict D θ hθ V fr
  obtain ⟨r, C₀, hC₀, hNI⟩ := hN W hW
  apply GlobalTheory.CuspGeo.norm_le_of_unipRad_variation D V φ hφ hcusp r C₀ hC₀ x
  intro m hm
  have hm' : (Formalism.IndefR.Eqv.UI.brg fr).symm m ∈ (Formalism.IndefR.Eqv.UI.instV fr).NA W :=
    hNI _ (by simpa using hm)
  obtain ⟨γ, hγ, k, hk, u, Av, Z, hAZ, hu, heq, hbd⟩ := hmv _ hm'
  have hmx : m * x = Formalism.IndefR.Eqv.UI.brg fr γ * (x * Formalism.IndefR.Eqv.UI.brg fr (u, 1)) * Formalism.IndefR.Eqv.UI.brg fr (1, k) := by
    have h2 := congrArg (Formalism.IndefR.Eqv.UI.brg fr) heq
    have h3 : ((u, k) : (Formalism.IndefR.Eqv.UI.instV fr).GA) = (u, 1) * (1, k) := by simp
    rw [h3] at h2
    simp only [map_mul, hbx, ContinuousMulEquiv.apply_symm_apply] at h2
    rw [h2]; group
  rw [hmx, hlev _ (GlobalTheory.T.principalCongruence_mem_latticeCongruenceLevel D V fr g hg k hk), hφ.left _ ((hGQ γ).2 hγ)]
  have h6 := GlobalTheory.T.lipschitz_bound_real_unipotent_action D θ hθ V A fr (fun τ => (hfr τ).2) φ c hc hlip u Av Z hAZ hu x
  have h7 := sum_sqrt_add_le (InfinitePlace D.host.F) (fun v => Formalism.REAL.hs (Av v)) (fun v => Formalism.REAL.hs (Z v))
    (fun v => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
    (fun v => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
  have hcard : Fintype.card (InfinitePlace D.host.F) = Fintype.card D.what₂.Tau :=
    Fintype.card_congr (Formalism.L2.Host.tauPl D).symm
  rw [hcard] at h7
  rw [hfI, hrdI] at hbd
  have hL : (2 * GlobalTheory.Count.least (Formalism.IndefR.Eqv.UI.instV fr) x0) ^ ((1 : ℝ) / q) ≤ (2 * s) ^ ((1 : ℝ) / q) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
  have hL0 : 0 ≤ (2 * GlobalTheory.Count.least (Formalism.IndefR.Eqv.UI.instV fr) x0) ^ ((1 : ℝ) / q) := by positivity
  have hrd0 : 0 ≤ rdisc D := by unfold rdisc; positivity
  have hN : Real.sqrt (Fintype.card D.what₂.Tau) * Real.sqrt (Fintype.card D.what₂.Tau) = Fintype.card D.what₂.Tau :=
    Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hP : 0 ≤ (V.rank : ℝ) ^ 2 * (Fintype.card D.what₂.Tau : ℝ) * (g : ℝ) * rdisc D := by positivity
  have hbd' : Real.sqrt (Fintype.card D.what₂.Tau) *
      (Real.sqrt (∑ v, Formalism.REAL.hs (Av v)) + Real.sqrt (∑ v, Formalism.REAL.hs (Z v))) ≤
      (V.rank : ℝ) ^ 2 * Fintype.card D.what₂.Tau * g * rdisc D * (2 * s) ^ ((1 : ℝ) / q) := by
    calc _ ≤ Real.sqrt (Fintype.card D.what₂.Tau) * ((V.rank : ℝ) ^ 2 * Real.sqrt (Fintype.card D.what₂.Tau) * g * rdisc D *
          (2 * GlobalTheory.Count.least (Formalism.IndefR.Eqv.UI.instV fr) x0) ^ ((1 : ℝ) / q) / 4) :=
          mul_le_mul_of_nonneg_left hbd (Real.sqrt_nonneg _)
      _ = (Real.sqrt (Fintype.card D.what₂.Tau) * Real.sqrt (Fintype.card D.what₂.Tau)) * ((V.rank : ℝ) ^ 2 * g * rdisc D *
          (2 * GlobalTheory.Count.least (Formalism.IndefR.Eqv.UI.instV fr) x0) ^ ((1 : ℝ) / q)) / 4 := by ring
      _ = ((V.rank : ℝ) ^ 2 * Fintype.card D.what₂.Tau * g * rdisc D) *
          (2 * GlobalTheory.Count.least (Formalism.IndefR.Eqv.UI.instV fr) x0) ^ ((1 : ℝ) / q) / 4 := by rw [hN]; ring
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hL hP, mul_nonneg hP hL0]
  calc _ ≤ _ := h6
    _ ≤ c * (Real.sqrt (Fintype.card D.what₂.Tau) *
      (Real.sqrt (∑ v, Formalism.REAL.hs (Av v)) + Real.sqrt (∑ v, Formalism.REAL.hs (Z v)))) := mul_le_mul_of_nonneg_left h7 hc
    _ ≤ _ := mul_le_mul_of_nonneg_left hbd' hc

end GlobalTheory.ShortLineCusp

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SepPer

theorem norm_sq_unitaryEmbedding_add : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (A : Fr Y) (B : Fr V), Adapted d A B → ∀ (x : GA D Y) (τ : D.what₂.Tau) (y : Fin Y.rank → D.host.E) (u : D.host.E), nrm θ B (stabilizerEmbedding d x) τ (frameMat V Y d.ι *ᵥ y + u • zv d) ^ 2 = nrm θ A x τ y ^ 2 + ‖tauE D τ u‖ ^ 2 := by
  intro D θ hθ Y V d A B hAd x τ y u
  let φ : AF D.host.F ⊗[D.host.F] D.host.E →+* ℂ :=
    (θ τ).comp (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
  have hinc : ∀ e, φ (incA D e) = tauE D τ e := by
    intro e
    have := (hθ τ).1 e
    simpa [φ, incA, inclR] using this
  have hcmp : ∀ {W : HSp D} (g : GA D W), cmp θ τ g = (matHom W g).1.map φ := by
    intro W g; rfl
  have hinv : (stabilizerEmbedding d x)⁻¹ = stabilizerEmbedding d x⁻¹ :=
    (map_inv (MonoidHom.mk' (stabilizerEmbedding d) (GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul d)) x).symm
  set P := (frameMat V Y d.ι).map (tauE D τ) with hP
  set Q := (GlobalTheory.UnitaryEmbeddingProperties.qM d).map (tauE D τ) with hQ
  have key : cmp θ τ (stabilizerEmbedding d x)⁻¹ = GlobalTheory.UnitaryEmbeddingProperties.ex P Q (cmp θ τ x⁻¹) := by
    rw [hinv, hcmp, hcmp, GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_matrix_formula, GlobalTheory.UnitaryEmbeddingProperties.ex_map, Matrix.map_map, Matrix.map_map]
    have hf : (⇑φ ∘ ⇑(incA D)) = ⇑(tauE D τ) := funext hinc
    rw [hf]
  have hQP : Q * P = 1 := GlobalTheory.UnitaryEmbeddingProperties.qM_mul_map (tauE D τ) d
  have hQz0 : GlobalTheory.UnitaryEmbeddingProperties.qM d *ᵥ zv d = 0 := by
    have hp := d.perp
    have h0 : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat V Y d.ι) * V.gram) *ᵥ zv d = 0 := by
      funext i
      have := congr_fun (congr_fun hp i) 0
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, zv] using this
    rw [GlobalTheory.UnitaryEmbeddingProperties.qM, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
  have hQz : Q *ᵥ (fun i => tauE D τ (zv d i)) = 0 := by
    funext i
    have := congr_fun hQz0 i
    rw [hQ]
    change ((GlobalTheory.UnitaryEmbeddingProperties.qM d).map (tauE D τ) *ᵥ (⇑(tauE D τ) ∘ zv d)) i = 0
    rw [← RingHom.map_mulVec, this]
    exact map_zero _
  have hvec : (fun i => tauE D τ ((frameMat V Y d.ι *ᵥ y + u • zv d) i)) =
      P *ᵥ (fun i => tauE D τ (y i)) + tauE D τ u • fun i => tauE D τ (zv d i) := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add (f := _), map_mul, hP, RingHom.map_mulVec]
    rfl
  have hex : ∀ (h : Matrix (Fin Y.rank) (Fin Y.rank) ℂ) (w : Fin Y.rank → ℂ) (a : ℂ),
      GlobalTheory.UnitaryEmbeddingProperties.ex P Q h *ᵥ (P *ᵥ w + a • fun i => tauE D τ (zv d i)) =
        P *ᵥ (h *ᵥ w) + a • fun i => tauE D τ (zv d i) := by
    intro h w a
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec, GlobalTheory.UnitaryEmbeddingProperties.ex_mul_P P Q hQP,
      ← Matrix.mulVec_mulVec]
    congr 2
    rw [GlobalTheory.UnitaryEmbeddingProperties.ex, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hQz,
      Matrix.mulVec_zero, add_zero]
  unfold nrm
  rw [key, hvec, hex]
  exact hAd τ _ _

end GlobalTheory.SepPer
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.HtWitt

theorem reduce (hT2 : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), ∃ C : ℝ, ∀ n ∈ flagN d, ∃ γ ∈ GQ S, γ ∈ flagN d ∧ height S (γ * n) ≤ C) (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) :
    ∃ C₁ : ℝ, ∀ n ∈ flagN d, ∀ h : GA D S₀, ∃ n' ∈ flagN d, ∃ h' : GA D S₀, height S n' ≤ C₁ ∧
      height S₀ h' ≤ 2 * quotHeight S₀ h ∧ quotHeight S₀ h' = quotHeight S₀ h ∧
      quotHeight S (n' * d.emb0 h') = quotHeight S (n * d.emb0 h) := by
  obtain ⟨C₁, hC₁⟩ := hT2 D S S₀ ρ d
  refine ⟨C₁, fun n hn h => ?_⟩
  obtain ⟨δ, hδ, hδh⟩ := exists_height_le_two_mul_quotHeight S₀ h
  have hm : d.emb0 δ * n * (d.emb0 δ)⁻¹ ∈ flagN d := GlobalTheory.MixPer.witt_anisotropic_group_normalizes_flag_unipotent D S S₀ ρ d n hn δ
  obtain ⟨γ, hγ, hγN, hγC⟩ := hC₁ _ hm
  refine ⟨γ * (d.emb0 δ * n * (d.emb0 δ)⁻¹), mul_mem hγN hm, δ * h, hγC, hδh, quotHeight_left S₀ hδ h, ?_⟩
  have e : γ * (d.emb0 δ * n * (d.emb0 δ)⁻¹) * d.emb0 (δ * h) = (γ * d.emb0 δ) * (n * d.emb0 h) := by
    rw [map_mul]; group
  rw [e, quotHeight_left S (mul_mem hγ (d.wittDecomp_anisotropicEmbedding_mem_rationalPoints hδ))]

theorem main (hT1 : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), ∃ C : ℝ, ∀ g : GA D S₀, height S (d.emb0 g) ≤ C * height S₀ g) (hT2 : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), ∃ C : ℝ, ∀ n ∈ flagN d, ∃ γ ∈ GQ S, γ ∈ flagN d ∧ height S (γ * n) ≤ C) (hT3 : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (C₀ : ℝ), ∃ (C : ℝ) (a : ℕ), ∀ n ∈ flagN d, height S n ≤ C₀ → ∀ h : GA D S₀, quotHeight S₀ h ≤ C * quotHeight S (n * d.emb0 h) ^ a) : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), ∃ (C : ℝ) (a : ℕ), ∀ n ∈ flagN d, ∀ h, quotHeight S₀ h ≤ C * quotHeight S (n * d.emb0 h) ^ a ∧ quotHeight S (n * d.emb0 h) ≤ C * quotHeight S₀ h ^ a := by
  intro D S S₀ ρ d
  obtain ⟨C₁, hC₁⟩ := reduce hT2 D S S₀ ρ d
  obtain ⟨C₂, hC₂⟩ := hT1 D S S₀ ρ d
  obtain ⟨C₃, a₃, hC₃⟩ := hT3 D S S₀ ρ d C₁
  have hC2 : 0 ≤ C₂ := by
    have := hC₂ 1
    rw [map_one, height_one, height_one] at this
    linarith
  refine ⟨max C₃ (C₁ * C₂ * 2) , max a₃ 1, fun n hn h => ?_⟩
  obtain ⟨n', hn', h', hn'C, hh', hq0, hq⟩ := hC₁ n hn h
  have hC1 : 0 ≤ C₁ := (height_pos S n').le.trans hn'C
  have q1 : 1 ≤ quotHeight S (n * d.emb0 h) := one_le_quotHeight S _
  have q0 : 1 ≤ quotHeight S₀ h := one_le_quotHeight S₀ _
  have hM : 0 ≤ max C₃ (C₁ * C₂ * 2) := le_max_of_le_right (by positivity)
  constructor
  · have h3 := hC₃ n' hn' hn'C h'
    rw [hq0, hq] at h3
    exact h3.trans (mul_le_mul (le_max_left _ _) (pow_le_pow_right₀ q1 (le_max_left _ _)) (by positivity) hM)
  · have hb : quotHeight S (n' * d.emb0 h') ≤ C₁ * C₂ * 2 * quotHeight S₀ h := by
      have h1 := height_mul_le S n' (d.emb0 h')
      have h2 := hC₂ h'
      have hp : 0 ≤ height S (d.emb0 h') := (height_pos S _).le
      calc quotHeight S (n' * d.emb0 h') ≤ height S n' * height S (d.emb0 h') := (quotHeight_le_height S _).trans h1
        _ ≤ C₁ * (C₂ * height S₀ h') := mul_le_mul hn'C h2 hp hC1
        _ ≤ C₁ * (C₂ * (2 * quotHeight S₀ h)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh' hC2) hC1
        _ = C₁ * C₂ * 2 * quotHeight S₀ h := by ring
    rw [hq] at hb
    refine hb.trans (mul_le_mul (le_max_right _ _) ?_ (by linarith) hM)
    calc quotHeight S₀ h = quotHeight S₀ h ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ q0 (le_max_right _ _)

end GlobalTheory.HtWitt

namespace GlobalTheory.HtWitt

theorem quotHeight_witt : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), ∃ (C : ℝ) (a : ℕ), ∀ n ∈ flagN d, ∀ h, quotHeight S₀ h ≤ C * quotHeight S (n * d.emb0 h) ^ a ∧ quotHeight S (n * d.emb0 h) ≤ C * quotHeight S₀ h ^ a :=
  main GlobalTheory.T.unitaryAdelicHeight_wittEmbedding_le_const_mul GlobalTheory.T.exists_rational_translate_flagUnipotent_height_le GlobalTheory.T.unitaryQuotientHeight_wittLevi_le_pow_of_boundedUnipotent

end GlobalTheory.HtWitt
end

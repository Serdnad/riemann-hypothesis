module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1742
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle033
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle384
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle037
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.UpOperatorEigenvalues.EigChar
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open UpperTheory.V.Z.J.D
open scoped TensorProduct

namespace UpperTheory.V.Z.J.D

private lemma box_tmul {G H W W' : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ G W) (τ : Representation ℂ H W')
    (a : G) (b : H) (w : W) (v : W') :
    box ρ τ (a, b) (w ⊗ₜ[ℂ] v) = ρ a w ⊗ₜ[ℂ] τ b v := by
  simp [box, Representation.tprod_apply]

private lemma isot_factor {G H W W' X Y : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [Nontrivial W] (ρ : Representation ℂ G W) (τ : Representation ℂ H W')
    (κ : Representation ℂ (G × H) X) (κ' : Representation ℂ H Y) (f : W ⊗[ℂ] Y ≃ₗ[ℂ] X)
    (hf : Intw (box ρ κ') κ f.toLinearMap) (h2 : Isot (κ.comp (MonoidHom.inr G H)) τ) :
    Isot κ' τ := by
  obtain ⟨w0, hw0⟩ := exists_ne (0 : W)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ W, φ w0 ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hw0 ((Module.forall_dual_apply_eq_zero_iff ℂ w0).1 hcon)
  let p : X →ₗ[ℂ] Y := (TensorProduct.lid ℂ Y).toLinearMap ∘ₗ
    (TensorProduct.map φ LinearMap.id) ∘ₗ f.symm.toLinearMap
  have hp1 : ∀ w y, p (f (w ⊗ₜ[ℂ] y)) = φ w • y := fun w y => by
    simp [p]
  have hp2 : ∀ (h : H) (x : X), p (κ (1, h) x) = κ' h (p x) := by
    intro h x
    obtain ⟨t, rfl⟩ := f.surjective x
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul w y =>
      have := hf (1, h) (w ⊗ₜ[ℂ] y)
      simp only [LinearEquiv.coe_coe] at this
      rw [← this, box_tmul, hp1, hp1]
      simp
  unfold Isot
  set S : Submodule ℂ Y := ⨆ g : {g : W' →ₗ[ℂ] Y // Intw τ κ' g}, LinearMap.range g.1 with hS
  have hle : (⊤ : Submodule ℂ X) ≤ S.comap p := by
    refine le_trans h2 (iSup_le fun u => ?_)
    rintro _ ⟨a, rfl⟩
    have hu : Intw τ κ' (p ∘ₗ u.1) := fun h v => by
      have := u.2 h v
      simp only [LinearMap.comp_apply]
      rw [this]
      exact hp2 h (u.1 v)
    exact (le_iSup (fun g : {g : W' →ₗ[ℂ] Y // Intw τ κ' g} => LinearMap.range g.1) ⟨_, hu⟩)
      ⟨a, rfl⟩
  intro y _
  have hy : p (f (w0 ⊗ₜ[ℂ] ((φ w0)⁻¹ • y))) ∈ S := hle (Submodule.mem_top)
  rw [hp1, smul_smul, mul_inv_cancel₀ hφ, one_smul] at hy
  exact hy

private lemma isot_tensor {G H W W' X Y : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ G W) (τ : Representation ℂ H W')
    (κ : Representation ℂ (G × H) X) (κ' : Representation ℂ H Y) (f : W ⊗[ℂ] Y ≃ₗ[ℂ] X)
    (hf : Intw (box ρ κ') κ f.toLinearMap) (h : Isot κ' τ) : Isot κ (box ρ τ) := by
  unfold Isot
  set T : Submodule ℂ X :=
    ⨆ F : {F : W ⊗[ℂ] W' →ₗ[ℂ] X // Intw (box ρ τ) κ F}, LinearMap.range F.1 with hT
  have hF : ∀ g : W' →ₗ[ℂ] Y, Intw τ κ' g →
      Intw (box ρ τ) κ (f.toLinearMap ∘ₗ TensorProduct.map LinearMap.id g) := by
    intro g hg ab t
    obtain ⟨a, b⟩ := ab
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add s t hs ht => simp only [map_add (f := _), hs, ht]
    | tmul w v =>
      have := hf (a, b) (w ⊗ₜ[ℂ] g v)
      simp only [LinearEquiv.coe_coe] at this
      rw [box_tmul] at this
      simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
        LinearEquiv.coe_coe, box_tmul]
      rw [hg b v, this]
  have hw : ∀ (w : W) (y : Y), f (w ⊗ₜ[ℂ] y) ∈ T := by
    intro w y
    have hle : (⊤ : Submodule ℂ Y) ≤
        T.comap (f.toLinearMap ∘ₗ TensorProduct.mk ℂ W Y w) := by
      refine le_trans h (iSup_le fun g => ?_)
      rintro _ ⟨a, rfl⟩
      exact (le_iSup (fun F : {F : W ⊗[ℂ] W' →ₗ[ℂ] X // Intw (box ρ τ) κ F} =>
        LinearMap.range F.1) ⟨_, hF g.1 g.2⟩) ⟨w ⊗ₜ[ℂ] a, by simp⟩
    exact hle (Submodule.mem_top (x := y))
  intro x _
  obtain ⟨t, rfl⟩ := f.surjective x
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add s t hs ht =>
    rw [map_add (f := _)]
    exact T.add_mem (hs (Submodule.mem_top)) (ht (Submodule.mem_top))
  | tmul w y => exact hw w y

end UpperTheory.V.Z.J.D

theorem UpperTheory.V.Z.J.D.boxIsot :
    Step → BoxIsot := by
  intro hStep G H W W' _ _ _ _ _ _ ρ τ hρ _ X _ _ κ h1 h2
  obtain ⟨Y, _, _, κ', f, hf⟩ := hStep G H X W κ ρ hρ h1
  haveI : Nontrivial W := by
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    obtain ⟨s, t, hst⟩ := hρ.1.toNontrivial.exists_pair_ne
    exact hst (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
  exact isot_tensor ρ τ κ κ' f hf (isot_factor ρ τ κ κ' f hf h2)
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open GlobalTheory.BCT.GlobLev GlobalTheory.SplitPts GroundTheory.Automorphic

namespace UpperTheory.V.Z.J.D

private theorem exists_avg {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (R : Representation ℂ G V)
    (K H : Subgroup G) (hfin : Finite (K ⧸ H.subgroupOf K)) :
    ∃ A : V →ₗ[ℂ] V, (∀ v, (∀ k ∈ K, R k v = v) → A v = v) ∧
      (∀ v, (∀ h ∈ H, R h v = v) → ∀ k ∈ K, R k (A v) = A v) ∧
      ∀ M : Submodule ℂ V, (∀ x, ∀ v ∈ M, R x v ∈ M) → ∀ v ∈ M, A v ∈ M := by
  classical
  letI := Fintype.ofFinite (K ⧸ H.subgroupOf K)
  have hc : (Fintype.card (K ⧸ H.subgroupOf K) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine ⟨(Fintype.card (K ⧸ H.subgroupOf K) : ℂ)⁻¹ • ∑ q : K ⧸ H.subgroupOf K, R ((q.out : K) : G), ?_, ?_, ?_⟩
  · intro v hv
    simp only [LinearMap.smul_apply, LinearMap.sum_apply]
    rw [Finset.sum_congr rfl fun q _ => hv _ (q.out : K).2]
    simp [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, hc]
  · intro v hv k hk

    simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
    congr 1
    have key : ∀ q : K ⧸ H.subgroupOf K, R k (R ((q.out : K) : G) v) =
        R ((((⟨k, hk⟩ : K) • q).out : K) : G) v := fun q => by
      have e : (QuotientGroup.mk (((⟨k, hk⟩ : K) • q).out) : K ⧸ H.subgroupOf K) =
          QuotientGroup.mk ((⟨k, hk⟩ : K) * q.out) := by
        rw [QuotientGroup.out_eq']
        conv_lhs => rw [← QuotientGroup.out_eq' q]
        rfl
      have h1 := QuotientGroup.eq.1 e
      have h2 : ((((⟨k, hk⟩ : K) • q).out : K) : G)⁻¹ * (k * ((q.out : K) : G)) ∈ H := h1
      have h3 := hv _ h2
      have h4 : k * ((q.out : K) : G) = ((((⟨k, hk⟩ : K) • q).out : K) : G) *
          (((((⟨k, hk⟩ : K) • q).out : K) : G)⁻¹ * (k * ((q.out : K) : G))) := by group
      rw [← Module.End.mul_apply, ← map_mul, h4, map_mul, Module.End.mul_apply, h3]
    rw [Finset.sum_congr rfl fun q _ => key q]
    exact Equiv.sum_comp (MulAction.toPerm (⟨k, hk⟩ : K)) fun q : K ⧸ H.subgroupOf K => R ((q.out : K) : G) v
  · intro M hM v hv
    exact M.smul_mem _ (by
      simp only [LinearMap.sum_apply]
      exact M.sum_mem fun q _ => hM _ v hv)

private theorem is_compact_integral_level {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {S : Set (Pl E)} (hS : IsSection S) :
    IsCompact (globLev S (KL n) : Set (finU (E := E) (n := n))) := by
  have hO : IsOpen (globLev S (KL n) : Set (finU (E := E) (n := n))) := by
    rw [globLev_KL_eq hS]
    exact (AdelicGLn.isOpen_integralFiniteGL E n).preimage continuous_finPart
  refine IsCompact.of_isClosed_subset (isClosedEmbedding_finU.isCompact_preimage
    ((AdelicGLn.isCompact_integralFiniteGL E n).image continuous_finGL_ad))
    (Subgroup.isClosed_of_isOpen _ hO) fun x hx => ⟨finPart E n x, ?_, ?_⟩
  · rw [globLev_KL_eq hS] at hx
    exact hx
  · have h1 : GeneralLinearGroup.map (pInf E) ((x : UA E n) : GA E n) = 1 := x.2
    exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL]; rfl)

private theorem finite_quot {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {S : Set (Pl E)} (hS : IsSection S)
    {K' : ∀ w : Pl E, Subgroup (UL n w)} (hle : ∀ w, K' w ≤ KL n w) (U : Subgroup (finU (E := E) (n := n))) (hU : IsOpen (U : Set (finU (E := E) (n := n)))) :
    Finite (globLev S K' ⧸ U.subgroupOf (globLev S K')) := by
  have hK : globLev S K' ≤ globLev S (KL n) := fun k hk =>
    (mem_globLev S _ k).2 fun w hw => hle w ((mem_globLev S _ k).1 hk w hw)
  haveI : CompactSpace (globLev S (KL n)) := isCompact_iff_compactSpace.1 (is_compact_integral_level hS)
  have h0 : Finite (globLev S (KL n) ⧸ U.subgroupOf (globLev S (KL n))) :=
    Subgroup.quotient_finite_of_isOpen _ (hU.preimage continuous_subtype_val)
  have h1 : U.relIndex (globLev S (KL n)) ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h2 : U.relIndex (globLev S K') ≠ 0 := mt (Subgroup.relIndex_eq_zero_of_le_right hK) h1
  haveI : (U.subgroupOf (globLev S K')).FiniteIndex := ⟨h2⟩
  exact Subgroup.finite_quotient_of_finiteIndex

private noncomputable def stabG {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (R : Representation ℂ G V) (v : V) : Subgroup G :=
  _root_.UpperTheory.Reformulated.B.StabilizerSubgroup.stabG R v

theorem indepS : IndepS := by
  intro E _ _ _ n S hS lam K' hK' J _ σ hd
  classical
  obtain ⟨h1, h2, -⟩ := hd
  have hst : ∀ j x, ∀ φ ∈ σ j, RU E n x φ ∈ σ j := fun j => (h1 j).1.stable
  intro i
  have hT : ∀ x, ∀ φ ∈ ⨆ (j) (_ : j ≠ i), σ j, RU E n x φ ∈ ⨆ (j) (_ : j ≠ i), σ j := by
    intro x φ hφ
    have hc : (⨆ (j) (_ : j ≠ i), σ j) ≤ (⨆ (j) (_ : j ≠ i), σ j).comap (RU E n x) :=
      iSup₂_le fun j hj y hy => Submodule.mem_comap.2 (le_iSup₂_of_le (f := fun j (_ : j ≠ i) => σ j) j hj le_rfl (hst j x y hy))
    exact hc hφ
  rcases (h1 i).1.irred (σ i ⊓ ⨆ (j) (_ : j ≠ i), σ j) inf_le_left
    (fun x φ hφ => ⟨hst i x φ hφ.1, hT x φ hφ.2⟩) with h0 | h0
  · exact disjoint_iff.2 h0
  exfalso
  obtain ⟨φ, hφ, hφ0⟩ := (Submodule.ne_bot_iff _).1 (h1 i).2.2
  have hφT : φ ∈ ⨆ (j) (_ : j ≠ i), σ j := (inf_eq_left.1 h0) hφ.1
  obtain ⟨f, hf, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hφT
  have hfσ : ∀ j, f j ∈ σ j := fun j => by
    by_cases hj : j = i
    · have := hf j
      rw [iSup_neg (not_not.2 hj)] at this
      rw [(Submodule.mem_bot ℂ).1 this]
      exact Submodule.zero_mem _
    · have := hf j
      rwa [iSup_pos hj] at this
  have hfi : f i = 0 := by
    have := hf i
    rw [iSup_neg (not_not.2 rfl)] at this
    exact (Submodule.mem_bot ℂ).1 this
  have hsum' : ∑ j, f j = φ := by
    rw [← hsum]
    exact (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => Finsupp.notMem_support_iff.1 hj).symm
  have hopen : IsOpen ((⨅ j, stabG (RF E n) (f j) : Subgroup (finU (E := E) (n := n))) : Set (finU (E := E) (n := n))) := by
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun j => ((h1 j).1.aut _ (hfσ j)).level
  obtain ⟨A, hA1, hA2, hA3⟩ := exists_avg (RF E n) (globLev S K') (⨅ j, stabG (RF E n) (f j))
    (finite_quot hS (fun w => (hK'.1 w).2.1) _ hopen)
  have hφfix : ∀ k ∈ globLev S K', RF E n k φ = φ := fun k hk => GlobalTheory.LGrp.mem_fixed.1 hφ.2 k hk
  have hφA : A φ = φ := hA1 φ hφfix
  have ha : ∀ j, A (f j) ∈ σ j ⊓ fixed (RF E n) (globLev S K') := fun j =>
    ⟨hA3 (σ j) (fun x v hv => hst j _ v hv) _ (hfσ j),
      GlobalTheory.LGrp.mem_fixed.2 fun k hk => hA2 _ (fun h hh => (Subgroup.mem_iInf.1 hh j)) k hk⟩
  have hmem : φ ∈ ⨆ (j) (_ : j ≠ i), σ j ⊓ fixed (RF E n) (globLev S K') := by

    rw [← hφA, ← hsum', map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hj : j = i
    · rw [hj, hfi, map_zero]
      exact Submodule.zero_mem _
    · exact le_iSup₂_of_le (f := fun j (_ : j ≠ i) => σ j ⊓ fixed (RF E n) (globLev S K')) j hj le_rfl (ha j)
  exact hφ0 ((Submodule.disjoint_def.1 (h2 i)) φ hφ hmem)

end UpperTheory.V.Z.J.D
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open scoped Matrix TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField



namespace UpperTheory.V.Z.J.D

theorem compsEx : CompsEx := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V hV σ hσ
  have hund : ∀ {A : ValuationSubring Ω} {w : Plc L}, IsPlaceOver A w → IsPlaceOver A (w.under (𝓞 (Lp L))) :=
    fun hA y => hA (algebraMap (𝓞 (Lp L)) (𝓞 L) y)
  have hwv : ∀ v, (s.w v).under (𝓞 (Lp L)) = v := fun v =>
    HeightOneSpectrum.ext (Ideal.ext fun y => (hund (s.hw v) y).symm.trans (s.hA v y))
  have hsp : ∀ v ∈ s.S, IsSplitAt (s.w v) := fun v hv =>
    UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω _ _ (s.hA v) (s.split v hv) _ (hwv v)
  have hex : ∀ w : Plc L, IsSplitAt w → ∃ τ : SmIrr (GLw n w), Cp σ w τ := fun w hw => by
    obtain ⟨τ, -, h1, -⟩ := GlobalTheory.DefU.exists_locComp_split L n ⟨σ, hσ⟩ w hw
    exact ⟨τ, h1⟩
  have hl : ∀ v : V.frame.Vl, v.1 ∈ s.S := fun v => Or.inl v.2
  have hu : ∀ u : s.St, u.1 ∈ s.S := fun u => Or.inr (Or.inl u.2)
  have ho : s.v0 ∈ s.S := Or.inr (Or.inr rfl)
  choose f hf using fun v (hv : v ∈ s.S) => hex (s.w v) (hsp v hv)
  exact ⟨⟨fun v => f _ (hl v), fun u => f _ (hu u), f _ ho, fun v => hf _ (hl v), fun u => hf _ (hu u), hf _ ho⟩⟩

end UpperTheory.V.Z.J.D
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Z.J.D
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField



private theorem norm_le_of_isIntegral {l : ℕ} [Fact l.Prime] {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    (x : B →+* PadicAlgCl l) (h : ∀ a, ‖x (algebraMap A B a)‖ ≤ 1) {t : B} (ht : IsIntegral A t) : ‖x t‖ ≤ 1 := by
  obtain ⟨p, hm, hp⟩ := ht
  let S := integralClosure ℤ_[l] (PadicAlgCl l)
  let g : A →+* S := (x.comp (algebraMap A B)).codRestrict S.toSubring (fun a => by
    show IsIntegral ℤ_[l] (x (algebraMap A B a))
    exact (UpperTheory.V.Hi.Up.intIff _).2 (h a))
  have hint : IsIntegral S (x t) := by
    refine ⟨p.map g, hm.map g, ?_⟩
    rw [Polynomial.eval₂_map]
    have hc : (algebraMap S (PadicAlgCl l)).comp g = x.comp (algebraMap A B) := by
      ext a
      rfl
    rw [hc, ← Polynomial.hom_eval₂, hp, map_zero]
  exact (UpperTheory.V.Hi.Up.intIff _).1 (isIntegral_trans (R := ℤ_[l]) _ hint)

private theorem isIntegral_of_subalgebra {A Y : Type} [CommRing A] [AddCommGroup Y] [Module A Y] [Module.Finite A Y]
    (T : Subalgebra A (Module.End A Y)) (t : T) : IsIntegral A t := by
  have h : IsIntegral A (t : Module.End A Y) := by
    obtain ⟨p, hp, he⟩ := LinearMap.exists_monic_and_aeval_eq_zero A (t : Module.End A Y)
    exact ⟨p, hp, by rwa [← Polynomial.aeval_def]⟩
  exact (isIntegral_algHom_iff T.val Subtype.val_injective).1 h

private theorem norm_unit {l : ℕ} [Fact l.Prime] {B : Type} [CommRing B] (x : B →+* PadicAlgCl l) (u : Bˣ)
    (h : ∀ t, ‖x t‖ ≤ 1) : ‖x u‖ = 1 := by
  have e : ‖x u‖ * ‖x (u⁻¹ : Bˣ)‖ = 1 := by
    rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
  refine le_antisymm (h _) ?_
  calc (1 : ℝ) = ‖x u‖ * ‖x (u⁻¹ : Bˣ)‖ := e.symm
    _ ≤ ‖x u‖ * 1 := mul_le_mul_of_nonneg_left (h _) (norm_nonneg _)
    _ = ‖x u‖ := mul_one _

theorem UpperTheory.V.Z.J.D.unitEv :
    UnitEv := by
  intro L Ω _ _ _ _ _ l _ n c H hAx A _ _ _ θ _ ι K a _ _ I D ψ hU z v j
  obtain ⟨s, hs⟩ := GlobalTheory.LocLanglands.IsLocalArtin.surj (hAx.art_spec v)
    (UpperTheory.V.Hi.unif (IsDedekindDomain.HeightOneSpectrum.adicCompletion L (H.Sl v)))
  let g : Dec (H.pl v) := ⟨s, GlobalTheory.WeilDeligne.Weil_le_Dec (H.ovr v) s.2⟩
  rw [← hU.ψ_unif v j s g rfl hs]
  apply norm_unit z.toRingHom
  intro t
  refine norm_le_of_isIntegral (A := A) z.toRingHom ?_ (isIntegral_of_subalgebra _ t)
  intro a0
  let y : A →ₐ[c.O] PadicAlgCl l := z.comp (IsScalarTower.toAlgHom c.O A (H.TK θ a K))
  show ‖y a0‖ ≤ 1
  obtain ⟨b, hb⟩ := UpperTheory.V.Alg.IsCO.res_surj (O := c.O) a0
  have hm := UpperTheory.V.Hi.Up.normLt (l := l) (O := c.O) y _ hb
  have hi1 : IsIntegral ℤ_[l] (y (a0 - algebraMap c.O A b)) :=
    (UpperTheory.V.Hi.Up.intIff _).2 hm.le
  have hbi : IsIntegral ℤ_[l] b := by
    haveI := c.fin
    exact IsIntegral.of_finite ℤ_[l] b
  have hi2 : IsIntegral ℤ_[l] (y (algebraMap c.O A b)) := by
    rw [AlgHom.commutes]
    exact (isIntegral_algHom_iff c.O.val Subtype.val_injective).2 hbi
  have := hi1.add hi2
  rw [← map_add (f := _), sub_add_cancel] at this
  exact (UpperTheory.V.Hi.Up.intIff _).1 this
end

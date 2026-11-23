module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle023
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle014
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle013
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle019
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle030
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Ideal.BigOperators
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.FieldTheory.IsAlgClosed.Basic

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Polynomial

noncomputable section

def germCompRingHom {σ τ : Type} [Fintype σ] [Fintype τ] (x : σ → ℂ) (L : (σ → ℂ) →L[ℂ] (τ → ℂ)) :
    Germ (𝓝 (L x)) ℂ →+* Germ (𝓝 x) ℂ where
  toFun s := s.compTendsto L (L.continuous.tendsto x)
  map_one' := rfl
  map_mul' s t := Germ.inductionOn₂ s t fun _ _ => rfl
  map_zero' := rfl
  map_add' s t := Germ.inductionOn₂ s t fun _ _ => rfl

def holGermsPullback {σ τ : Type} [Fintype σ] [Fintype τ] (x : σ → ℂ) (L : (σ → ℂ) →L[ℂ] (τ → ℂ)) :
    holGerms (L x) →+* holGerms x :=
  ((germCompRingHom x L).comp (holGerms (L x)).subtype).codRestrict (holGerms x) fun s => by
    obtain ⟨b, hb, hbs⟩ := s.2
    refine ⟨b ∘ L, hb.comp (L.analyticAt x), ?_⟩
    show _ = germCompRingHom x L s.1
    rw [← hbs]
    rfl

theorem FiniteModuloIntegral.proof : FiniteModuloIntegral.Statement := by
  classical
  intro σ τ _ _ x k f L hf hfin g hg
  obtain ⟨n, e, he, hrep⟩ := hfin
  set φ := holGermsPullback x L with hφdef
  set I : Ideal (holGerms x) :=
    Ideal.span (Set.range fun i => (⟨f i, f i, hf i, rfl⟩ : holGerms x)) with hIdef
  let _ : Algebra (holGerms (L x)) (holGerms x ⧸ I) := ((Ideal.Quotient.mk I).comp φ).toAlgebra
  have hsmul : ∀ (s : holGerms (L x)) (q : holGerms x),
      s • Ideal.Quotient.mk I q = Ideal.Quotient.mk I (φ s * q) := by
    intro s q
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    simp

  have hfg : Module.Finite (holGerms (L x)) (holGerms x ⧸ I) := by
    refine ⟨⟨Finset.univ.image fun m => Ideal.Quotient.mk I ⟨e m, e m, he m, rfl⟩, ?_⟩⟩
    rw [eq_top_iff]
    rintro q -
    obtain ⟨⟨_, u, hu, rfl⟩, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨b, h, hb, hh, hev⟩ := hrep u hu
    have hq : Ideal.Quotient.mk I ⟨u, u, hu, rfl⟩ = ∑ m, (⟨b m, b m, hb m, rfl⟩ : holGerms (L x)) •
        Ideal.Quotient.mk I ⟨e m, e m, he m, rfl⟩ := by

      simp only [hsmul, ← map_sum]
      rw [Ideal.Quotient.eq]
      have hmem : ∑ i, (⟨h i, h i, hh i, rfl⟩ : holGerms x) * ⟨f i, f i, hf i, rfl⟩ ∈ I :=
        Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
      convert hmem using 1
      apply Subring.subtype_injective
      have e1 : (holGerms x).subtype ((⟨u, u, hu, rfl⟩ : holGerms x) -
          ∑ m, φ ⟨b m, b m, hb m, rfl⟩ * ⟨e m, e m, he m, rfl⟩) =
          Germ.coeRingHom (𝓝 x) (u - ∑ m, (b m ∘ L) * e m) := by

        simp only [map_sub, map_sum, map_mul]
        rfl
      have e2 : (holGerms x).subtype (∑ i, (⟨h i, h i, hh i, rfl⟩ : holGerms x) * ⟨f i, f i, hf i, rfl⟩) =
          Germ.coeRingHom (𝓝 x) (∑ i, h i * f i) := by

        simp only [map_sum, map_mul]
        rfl
      rw [e1, e2]
      refine Germ.coe_eq.2 ?_
      filter_upwards [hev] with z hz
      simp only [Pi.sub_apply, Finset.sum_apply, Pi.mul_apply, Function.comp_apply]
      rw [hz]
      ring
    rw [hq]
    exact Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  have := Algebra.IsIntegral.of_finite (holGerms (L x)) (holGerms x ⧸ I)

  obtain ⟨p, hpm, hp⟩ :=
    Algebra.IsIntegral.isIntegral (R := holGerms (L x)) (Ideal.Quotient.mk I ⟨g, g, hg, rfl⟩)
  rw [RingHom.algebraMap_toAlgebra, ← Polynomial.hom_eval₂, Ideal.Quotient.eq_zero_iff_mem,
    hpm.as_sum] at hp
  simp only [eval₂_add, eval₂_X_pow, eval₂_finsetSum, eval₂_mul, eval₂_C] at hp
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 hp
  choose a ha hae using fun j : ℕ => (p.coeff j).2
  choose h hh hhe using fun i => (c i).2
  refine ⟨p.natDegree, fun j => a j, h, fun j => ha j, hh, ?_⟩
  have hcI : ∀ i, (holGerms x).subtype (c i) = Germ.coeRingHom (𝓝 x) (h i) := fun i => (hhe i).symm
  have hφI : ∀ j, (holGerms x).subtype (φ (p.coeff j)) = Germ.coeRingHom (𝓝 x) (a j ∘ L) := by
    intro j
    show germCompRingHom x L (p.coeff j).1 = _
    rw [← hae j]
    rfl
  have hgerm : Germ.coeRingHom (𝓝 x) (∑ i, h i * f i) = Germ.coeRingHom (𝓝 x)
      (g ^ p.natDegree + ∑ j ∈ Finset.range p.natDegree, (a j ∘ L) * g ^ j) := by
    have := congrArg (holGerms x).subtype hc

    simp only [map_add (f := _), map_sum, map_mul, map_pow, hcI, hφI] at this ⊢
    exact this
  filter_upwards [Germ.coe_eq.1 hgerm] with z hz
  simp only [Finset.sum_apply, Pi.mul_apply, Pi.add_apply, Pi.pow_apply, Function.comp_apply] at hz
  rw [Fin.sum_univ_eq_sum_range (fun j => a j (L z) * g z ^ j), hz]

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

theorem WeierstrassFiniteness.proof (hE : FiniteModuloEliminate.Statement)
    (hI : FiniteModuloIntegral.Statement) : WeierstrassFiniteness.Statement := by
  intro σ _ x k f d A hf hpow g hg
  classical

  let L : Finset σ → (σ → ℂ) →L[ℂ] (Fin d ⊕ σ → ℂ) := fun S =>
    ContinuousLinearMap.pi (Sum.elim (fun j => (ContinuousLinearMap.proj j).comp A)
      (fun l => if l ∈ S then ContinuousLinearMap.proj l else 0))
  have hL : ∀ S z c, L S z c = Sum.elim (fun j => A z j) (fun l => if l ∈ S then z l else 0) c := by
    intro S z c
    rcases c with j | l
    · simp [L]
    · by_cases hl : l ∈ S <;> simp [L, hl]
  have key : ∀ T : Finset σ, IsFiniteModuloOver x f (L (Finset.univ \ T)) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      rw [Finset.sdiff_empty]
      let P : (Fin d ⊕ σ → ℂ) →L[ℂ] (σ → ℂ) :=
        ContinuousLinearMap.pi fun l => ContinuousLinearMap.proj (Sum.inr l)
      have hPL : ∀ z, P (L Finset.univ z) = z := fun z => by
        funext l; simp [P, hL]
      refine ⟨1, fun _ _ => 1, fun _ => analyticAt_const, fun g hg => ?_⟩
      refine ⟨fun _ y => g (P y), fun _ _ => 0, fun _ => ?_, fun _ => analyticAt_const,
        Eventually.of_forall fun z => by simp only [hPL]; simp⟩
      have hg' : AnalyticAt ℂ g (P (L Finset.univ x)) := by rw [hPL]; exact hg
      exact hg'.comp (P.analyticAt _)
    | insert l T hl ih =>
      have heq : L (Finset.univ \ insert l T) = (zeroCoordinate (Sum.inr l)).comp (L (Finset.univ \ T)) := by
        ext z c
        rw [ContinuousLinearMap.comp_apply, zeroCoordinate_apply, hL, hL]
        rcases c with j | l'
        · simp
        · by_cases h1 : l' = l
          · subst h1; simp
          · by_cases h2 : l' ∈ T <;> simp [h1, h2]
      rw [heq]
      obtain ⟨r, h, h', hh, hh', hev⟩ := hpow l
      refine hE σ (Fin d ⊕ σ) x k f _ (Sum.inr l) hf ih
        ⟨r, h, Sum.elim h' (fun _ _ => 0), hh, ?_, ?_⟩
      · rintro (j | l')
        · exact hh' j
        · exact analyticAt_const
      · filter_upwards [hev] with z hz
        simp only [zeroCoordinate_apply, hL, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
          Finset.mem_sdiff, Finset.mem_univ, hl, not_false_eq_true, and_self, if_true,
          reduceCtorEq, if_false, zero_mul, Finset.sum_const_zero, add_zero]
        exact hz
  have hfin := key Finset.univ
  obtain ⟨N, a, h, ha, hh, hev⟩ := hI σ (Fin d ⊕ σ) x k f _ hf hfin g hg

  let J : (Fin d → ℂ) →L[ℂ] (Fin d ⊕ σ → ℂ) :=
    ContinuousLinearMap.pi (Sum.elim (fun j => ContinuousLinearMap.proj j) (fun _ => 0))
  have hJ : ∀ z, J (A z) = L (Finset.univ \ Finset.univ) z := fun z => by
    funext c; rcases c with j | l <;> simp [J, hL]
  refine ⟨N, fun j w => a j (J w), h, fun j => ?_, hh, ?_⟩
  · have haj : AnalyticAt ℂ (a j) (J (A x)) := by rw [hJ]; exact ha j
    exact haj.comp (J.analyticAt _)
  · filter_upwards [hev] with z hz
    simpa only [hJ] using hz

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem UnbranchedProperCountConstant.proof (hloc : UnbranchedProperCountLocallyConstant.Statement)
    (hconn : ManifoldZerosComplementConnected.Statement) : UnbranchedProperCountConstant.Statement := by
  intro σ _ Y d A D δ hD hDc hmap hprop hδ hsec
  by_cases hne : ∃ y ∈ D, δ y ≠ 0
  swap
  · push Not at hne
    exact ⟨0, fun y hy hy' => absurd (hne y hy) hy'⟩
  obtain ⟨y₀, hy₀D, hy₀⟩ := hne
  have hreg : ∀ y ∈ D, IsRegularPointOf D y := fun y hy =>
    ⟨hy, d, ContinuousLinearMap.id ℂ _, D, D, id, hD, hD, hy, analyticOnNhd_id, fun _ _ => rfl, by simp⟩
  have hS : IsPreconnected (D \ {z | δ z = 0}) := hconn (Fin d) D δ hDc hreg hδ ⟨y₀, hy₀D, hy₀⟩
  have hL := hloc σ Y d A D δ hD hmap hprop hsec
  let f : (Fin d → ℂ) → ℕ := fun y => {x | x ∈ Y ∧ A x = y}.ncard
  have hcont : ContinuousOn f (D \ {z | δ z = 0}) := by
    intro y hy
    refine ContinuousAt.continuousWithinAt ((continuousAt_const (y := f y)).congr ?_)
    filter_upwards [(hL y hy.1 hy.2).2] with y' hy'
    simp only [f, Set.ncard_def, hy']
  refine ⟨f y₀, fun y hy hyδ => ?_⟩
  rw [← (hL y hy hyδ).1.cast_ncard_eq]
  exact congrArg _ (hS.constant hcont ⟨hy, hyδ⟩ ⟨hy₀D, hy₀⟩)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open Filter Topology

noncomputable section

theorem RootSumHolomorphic.proof : RootSumHolomorphic.Statement := by
  intro d m W Φ hm hW hsep hΦ y₀ hy₀
  obtain ⟨R, hR⟩ : ∃ R : Finset ℂ, R = (m.map (MvPolynomial.eval y₀)).roots.toFinset := ⟨_, rfl⟩
  have hroot : ∀ τ ∈ R, (m.map (MvPolynomial.eval y₀)).IsRoot τ := fun τ hτ => by
    rw [hR] at hτ
    exact (Polynomial.mem_roots (hm.map _).ne_zero).1 (Multiset.mem_toFinset.1 hτ)
  have hder : ∀ τ ∈ R, (m.map (MvPolynomial.eval y₀)).derivative.eval τ ≠ 0 := fun τ hτ => by
    have h := (hsep y₀ hy₀).eval₂_derivative_ne_zero (RingHom.id ℂ) (x := τ)
      (by rw [Polynomial.eval₂_id]; exact hroot τ hτ)
    rwa [Polynomial.eval₂_id] at h
  have hbr := fun τ (hτ : τ ∈ R) => SimpleRootBranch.proof d m y₀ τ (hroot τ hτ) (hder τ hτ)
  choose! U B ψ hUo hyU hBo hτB hψd hψy hψroot using hbr
  have hloc := fun τ (hτ : τ ∈ R) => hΦ y₀ hy₀ τ (hroot τ hτ)
  choose! O hOo hyO Ψ hΨd hΨeq using hloc
  obtain ⟨V, hV, hVdisj⟩ := (R.finite_toSet).t2_separation

  have hev : ∀ᶠ y in 𝓝 y₀, ∀ τ ∈ R, y ∈ U τ ∧ ψ τ y ∈ B τ ∩ V τ ∧ (y, ψ τ y) ∈ O τ := by
    refine (Filter.eventually_all_finset R).2 fun τ hτ => ?_
    have hψc : ContinuousAt (ψ τ) y₀ :=
      ((hψd τ hτ).differentiableAt ((hUo τ hτ).mem_nhds (hyU τ hτ))).continuousAt
    have hBV : B τ ∩ V τ ∈ 𝓝 (ψ τ y₀) := by
      rw [hψy τ hτ]; exact ((hBo τ hτ).inter (hV τ).2).mem_nhds ⟨hτB τ hτ, (hV τ).1⟩
    have hO : O τ ∈ 𝓝 (y₀, ψ τ y₀) := by
      rw [hψy τ hτ]; exact (hOo τ hτ).mem_nhds (hyO τ hτ)
    have hpc : ContinuousAt (fun y => (y, ψ τ y)) y₀ := continuousAt_id.prodMk hψc
    exact Filter.Eventually.and ((hUo τ hτ).mem_nhds (hyU τ hτ))
      (Filter.Eventually.and (hψc.preimage_mem_nhds hBV) (hpc.preimage_mem_nhds hO))

  have heq : ∀ᶠ y in 𝓝 y₀, ((m.map (MvPolynomial.eval y)).roots.map (Φ y)).sum =
      ∑ τ ∈ R, Ψ τ (y, ψ τ y) := by
    filter_upwards [hev] with y hy
    have hisroot : ∀ τ ∈ R, (m.map (MvPolynomial.eval y)).IsRoot (ψ τ y) := fun τ hτ =>
      ((hψroot τ hτ y (hy τ hτ).1).2 _ (hy τ hτ).2.1.1).2 rfl
    have hinj : ∀ τ ∈ R.val, ∀ τ' ∈ R.val, ψ τ y = ψ τ' y → τ = τ' := by
      intro τ hτ τ' hτ' h
      by_contra hne
      have h' : ψ τ y ∈ V τ' := by rw [h]; exact (hy τ' hτ').2.1.2
      exact Set.disjoint_left.1 (hVdisj hτ hτ' hne) (hy τ hτ).2.1.2 h'
    have hM : R.val.map (fun τ => ψ τ y) = (m.map (MvPolynomial.eval y)).roots := by
      apply Multiset.eq_of_le_of_card_le
      · rw [Multiset.le_iff_subset (Multiset.Nodup.map_on hinj R.nodup)]
        intro s hs
        obtain ⟨τ, hτ, rfl⟩ := Multiset.mem_map.1 hs
        exact (Polynomial.mem_roots (hm.map _).ne_zero).2 (hisroot τ hτ)
      · have h1 : Multiset.card (R.val.map fun τ => ψ τ y) = m.natDegree := by
          rw [Multiset.card_map, Finset.card_val, hR,
            Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots (hsep y₀ hy₀)),
            IsAlgClosed.card_roots_eq_natDegree, hm.natDegree_map]
        rw [h1, ← hm.natDegree_map (MvPolynomial.eval y)]
        exact Polynomial.card_roots' _
    rw [← hM, Multiset.map_map, Finset.sum_eq_multiset_sum]
    congr 1
    refine Multiset.map_congr rfl fun τ hτ => ?_
    exact hΨeq τ hτ (y, ψ τ y) (hy τ hτ).2.2 (hisroot τ hτ)

  have hg : DifferentiableAt ℂ (fun y => ∑ τ ∈ R, Ψ τ (y, ψ τ y)) y₀ := by
    refine DifferentiableAt.fun_sum (A := fun τ y => Ψ τ (y, ψ τ y)) fun τ hτ => ?_
    have hψ : DifferentiableAt ℂ (ψ τ) y₀ :=
      (hψd τ hτ).differentiableAt ((hUo τ hτ).mem_nhds (hyU τ hτ))
    have hΨ : DifferentiableAt ℂ (Ψ τ) (y₀, ψ τ y₀) := by
      rw [hψy τ hτ]; exact (hΨd τ hτ).differentiableAt ((hOo τ hτ).mem_nhds (hyO τ hτ))
    exact hΨ.comp y₀ (differentiableAt_id.prodMk hψ)
  exact (hg.congr_of_eventuallyEq heq).differentiableWithinAt

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Filter Topology

namespace InjectiveHolomorphicJacobianNeZero

theorem det_fin_one (A : (Fin 1 → ℂ) →ₗ[ℂ] Fin 1 → ℂ) : LinearMap.det A = A 1 0 := by
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℂ (Fin 1)), Matrix.det_unique, LinearMap.toMatrix_apply]
  simp only [Pi.basisFun_apply, Pi.basisFun_repr]
  have h1 : (Pi.single (default : Fin 1) (1 : ℂ) : Fin 1 → ℂ) = 1 := by
    funext i
    fin_cases i
    rfl
  rw [h1]
  rfl

theorem one {U : Set (Fin 1 → ℂ)} {f : (Fin 1 → ℂ) → Fin 1 → ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hinj : Set.InjOn f U) {x : Fin 1 → ℂ} (hx : x ∈ U) :
    LinearMap.det (fderiv ℂ f x : (Fin 1 → ℂ) →ₗ[ℂ] Fin 1 → ℂ) ≠ 0 := by
  set e : (Fin 1 → ℂ) ≃L[ℂ] ℂ := ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ with he
  set φ : ℂ → ℂ := fun z => e (f (e.symm z)) with hφ
  have hD : IsOpen (e.symm ⁻¹' U) := hU.preimage e.symm.continuous
  have hφd : DifferentiableOn ℂ φ (e.symm ⁻¹' U) :=
    e.differentiable.comp_differentiableOn (hf.comp e.symm.differentiable.differentiableOn fun _ h => h)
  have hφi : Set.InjOn φ (e.symm ⁻¹' U) := fun s hs t ht h =>
    e.symm.injective (hinj hs ht (e.injective h))
  have hxD : e x ∈ e.symm ⁻¹' U := by simpa using hx
  have hne := InjectiveHolomorphicDerivNeZero.proof _ φ hD hφd hφi (e x) hxD
  have hfx : HasFDerivAt f (fderiv ℂ f x) x := (hf.differentiableAt (hU.mem_nhds hx)).hasFDerivAt
  have hφx : HasFDerivAt φ ((e : (Fin 1 → ℂ) →L[ℂ] ℂ).comp ((fderiv ℂ f x).comp
      (e.symm : ℂ →L[ℂ] Fin 1 → ℂ))) (e x) := by
    have h1 : HasFDerivAt f (fderiv ℂ f x) (e.symm (e x)) := by simpa using hfx
    exact e.hasFDerivAt.comp (e x) (h1.comp (e x) e.symm.hasFDerivAt)
  rw [hφx.hasDerivAt.deriv] at hne
  rw [det_fin_one]
  simpa [he] using hne

end InjectiveHolomorphicJacobianNeZero

theorem InjectiveHolomorphicJacobianNeZero.proof (hF : HolomorphicKernelFibre.Statement)
    (hC : CriticalFlatNotInjective.Statement) : InjectiveHolomorphicJacobianNeZero.Statement := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro U f hU hf hinj x hx hdet
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k
    · rw [LinearMap.det_eq_one_of_subsingleton] at hdet
      exact one_ne_zero hdet
    · exact InjectiveHolomorphicJacobianNeZero.one hU hf hinj hx hdet
  · by_cases hall : ∀ b ∈ U, LinearMap.det (fderiv ℂ f b : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) = 0 →
        fderiv ℂ f b = 0
    · exact hC k U f x hk hU hf hx hdet hall hinj
    push Not at hall
    obtain ⟨b, hb, hdb, hne⟩ := hall
    set d := Module.finrank ℂ (LinearMap.ker (fderiv ℂ f b : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ)) with hd
    have hd0 : 0 < d := by
      rw [hd, Module.finrank_pos_iff_exists_ne_zero]
      obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
        (LinearMap.bot_lt_ker_of_det_eq_zero hdb).ne'
      exact ⟨⟨v, hv⟩, by simpa using hv0⟩
    have hdk : d < k := by
      have hker : LinearMap.ker (fderiv ℂ f b : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) ≠ ⊤ := by
        rw [Ne, LinearMap.ker_eq_top]
        intro h0
        exact hne (ContinuousLinearMap.coe_injective (by simpa using h0))
      simpa [Module.finrank_fin_fun] using Submodule.finrank_lt hker
    obtain ⟨V, y, γ, ℓ, hV, hy, hγ, hmaps, hγinj, hfib, hzero⟩ := hF k U f b hU hf hb d rfl
    have hhd : DifferentiableOn ℂ (fun t => ℓ (f (γ t))) V :=
      ℓ.differentiable.comp_differentiableOn (hf.comp hγ hmaps)
    have hhinj : Set.InjOn (fun t => ℓ (f (γ t))) V := fun s hs t ht h =>
      hγinj hs ht (hinj (hmaps hs) (hmaps ht) (hfib s hs t ht h))
    apply ih d hdk V _ hV hhd hhinj y hy
    rw [hzero, ContinuousLinearMap.toLinearMap_zero, LinearMap.det_zero, Module.finrank_fin_fun]
    exact zero_pow hd0.ne'

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology ComplexSets

noncomputable section

def NormalDivisorChartAtPoint {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    (u : Fin n → ℂ) (d : ℕ) (w : Fin n ⊕ Fin M.m → ℂ) : Prop :=
  ∃ (r : ℝ) (φ : (Fin (d + 1) → ℂ) → Fin n ⊕ Fin M.m → ℂ) (k : ℕ), 0 < r ∧
    DifferentiableOn ℂ φ (Metric.ball 0 r) ∧ Set.InjOn φ (Metric.ball 0 r) ∧ φ 0 = w ∧
    Set.MapsTo φ (Metric.ball 0 r) (IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal) ∧
    (∀ s : ℝ, 0 < s → ∃ U ∈ 𝓝 w, IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∩ U ⊆ φ '' Metric.ball 0 s) ∧
    VanishesToOrder (fun t => linEval u (IndefiniteRowSideFullHecke.ComplexSets.firstCoords (φ t))) r k ∧
    ∀ v : Fin (d + 1) → ℂ, v 0 = 0 →
      fderiv ℂ (fun t => IndefiniteRowSideFullHecke.ComplexSets.firstCoords (φ t)) 0 v = 0 → v = 0

def NormalModelDivisorChartGeneric.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
      ∃ B : Ideal (MvPolynomial (Fin n ⊕ Fin M.m) ℂ),
        M.ideal ⊔ Ideal.span {rename (Sum.inl : Fin n → Fin n ⊕ Fin M.m) (linForm u)} ≤ B ∧
        ringKrullDim (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ B) < (d : ℕ) ∧
        ∀ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal, linEval u (IndefiniteRowSideFullHecke.ComplexSets.firstCoords w) = 0 →
          w ∉ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn B → NormalDivisorChartAtPoint M u d w

end

end GroundTheory.Heights₂.Heights
end

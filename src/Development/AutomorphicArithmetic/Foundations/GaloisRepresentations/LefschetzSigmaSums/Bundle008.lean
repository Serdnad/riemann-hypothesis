module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HodgeTraceFromLefschetzAndGroupSide
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelEqKN
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle004
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

section

open UpperTheory.Gal.LocalSmoothExtension


open AlgebraicGeometry CategoryTheory Limits GlobalTheory.HodgeCoh in
theorem UpperTheory.Gal.LocalSmoothExtension.occOf_of :
    MemOp → UpperTheory.Gal.G3.HodgeGood → UpperTheory.Gal.G3.HodgeTr → UpperTheory.Gal.G3.BcGood.{0} → UpperTheory.Gal.G3.OpBc.{0} → UpperTheory.Gal.G3.OpTr.{0} → UpperTheory.Gal.G3.BcSplits → OccOf := by
  intro memop hg htr bcg opbc optr bcs p _ D G L R _ _ gb k T N J g τ θ a b x hx hxe
  letI : Algebra R ℂ := τ.toAlgebra
  refine ⟨b, x, hx, fun j => ?_⟩
  obtain ⟨-, hfin, het, hop⟩ := memop p D G L R gb k T N J g j
  haveI := hfin
  haveI := het
  have hΘ := bcg (UpperTheory.Gal.G3.hodge ℂ a b) (Spec.map (CommRingCat.ofHom τ)) (hg ℂ a b)
  have hs : (T.tower N g).s j ≫ (T.tower N g).q = (T.tower N g).s j ≫ (T.tower N g).q := rfl
  have h2 := opbc (UpperTheory.Gal.G3.hodge ℂ a b) (Spec.map (CommRingCat.ofHom τ)) (T.tower N g).q
    ((T.tower N g).s j ≫ (T.tower N g).q) (T.tower N g).q ((T.tower N g).s j) ((T.tower N g).t j) hs
    ((T.tower N g).comm j) _ (hop _ hΘ)
  obtain ⟨hf', he', -⟩ := bcs (Spec.map (CommRingCat.ofHom τ)) (T.tower N g).q
    ((T.tower N g).s j ≫ (T.tower N g).q) ((T.tower N g).s j ≫ (T.tower N g).q) ((T.tower N g).s j) hs
    ((T.tower N g).s j) hs PEmpty (fun e => e.elim) (fun e => e.elim)
  haveI := hf'
  haveI := he'
  have ht' : UpperTheory.Gal.G3.bcMap (Spec.map (CommRingCat.ofHom τ)) ((T.tower N g).t j) ((T.tower N g).comm j) ≫
      pullback.snd (T.tower N g).q (Spec.map (CommRingCat.ofHom τ)) =
      UpperTheory.Gal.G3.bcMap (Spec.map (CommRingCat.ofHom τ)) ((T.tower N g).s j) hs ≫
      pullback.snd (T.tower N g).q (Spec.map (CommRingCat.ofHom τ)) := by
    unfold UpperTheory.Gal.G3.bcMap
    rw [pullback.lift_snd, pullback.lift_snd]
  have htr' := htr ℂ a b (pullback.snd (T.tower N g).q (Spec.map (CommRingCat.ofHom τ))) _
    (UpperTheory.Gal.G3.bcMap (Spec.map (CommRingCat.ofHom τ)) ((T.tower N g).s j) hs) rfl
  have hA := (optr (UpperTheory.Gal.G3.hodge ℂ a b) (hg ℂ a b) _ _ _ _ _ rfl ht' _ htr' _).1 h2
  have e1 : (UpperTheory.Gal.Int.Geo.bcAlong (T.tower N g) τ).s j =
      UpperTheory.Gal.G3.bcMap (Spec.map (CommRingCat.ofHom τ)) ((T.tower N g).s j) hs := rfl
  refine ⟨e1 ▸ hf', e1 ▸ he', Eq.trans ?_ (hxe j)⟩
  rw [hA]
  rfl
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField
open GlobalTheory.HodgeCoh GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCx GlobalTheory.LKDef GlobalTheory.RootSumWeights GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open UpperTheory.Gal.Int.Geo (KS Lv Sc)
open UpperTheory.Gal.G3 (hodge ind)
open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.hodgeTr_of :
    GroupTop → FnDecomp → HopWord → AltLin → GeoStep → CxLin → UpperTheory.Gal.G3.HodgeGood → HodgeTr := by
  classical
  intro hTop hFD hHW hAL hGS hCL hHG p _ D G L lam i₀ h hh
  obtain ⟨k₀, hk'⟩ := hTop p D G L lam i₀ h hh
  refine ⟨k₀, fun k hkk => ?_⟩
  obtain ⟨c, hc1, hc2⟩ := hk' k hkk
  refine ⟨c, fun hSc gb hStd T N d hsm V _ _ _ ξ hξ f hfn hG y => ?_⟩
  have hcard : 0 < Fintype.card {v : InfinitePlace G.F // sigPosH (G.gram_herm v) = 1} := by
    change 0 < G.a
    exact hSc.ga.symm ▸ Nat.zero_lt_one
  obtain ⟨⟨v, hv⟩⟩ := Fintype.card_pos_iff.1 hcard
  obtain ⟨Lv, hLv⟩ := GlobalTheory.LKGeo.KNLevel.exists_level_eq_KN p D G L N.1 (by have := N.2.1; omega)
  have hK := T.K_eq N
  obtain ⟨hHecke, m, g, cc, hΔ, hdec, hsupp⟩ := (hFD _ _ T.X (T.lev N) f).1 hfn
  rw [hK] at hHecke hdec hsupp
  have hreg : ∀ i x, ind ℂ (L.KN N.1) (g i)⁻¹ x ≠ 0 → RegAf G x := fun i x hx => hG.reg x (hsupp i x hx)
  have hfnu : ∀ i, T.X.IsFn (T.lev N) (ind ℂ (L.KN N.1) (g i)⁻¹) := fun i => by
    have e := (UpperTheory.Gal.G3.pFnRing T.X ℂ (T.lev N)).1 _ (hΔ i)
    rwa [hK] at e
  have hgeo := fun i α hα => hGS p D G L hSc gb hStd i₀ v hv k T N d hsm (g i) (hΔ i) (hreg i) α hα
  have hfin : ∀ i, CxFin G v (L.KN N.1) (ind ℂ (L.KN N.1) (g i)⁻¹) := fun i =>
    (hgeo i (fun _ => 2) (fun _ => ⟨two_ne_zero, dvd_rfl⟩)).1
  have hhk : ∀ a b, hk T N f a b = ∑ i, cc i • hk T N (ind ℂ (L.KN N.1) (g i)⁻¹) a b := fun a b => by
    have e := ((hHW _ _ T.X (hodge ℂ a b) (hHG ℂ a b) (T.lev N)).1 m _ cc hfnu).2
    rw [← hdec] at e
    exact e
  have e1 : altTr (qAt T N) d (fun a b => hk T N f a b ∘ₗ cutD T N c a b) y =
      ∑ i, cc i * c.sum fun α r => r * cxTotalM G v (cW L i₀ v α y) (L.KN N.1) (ind ℂ (L.KN N.1) (g i)⁻¹) (Kp G) (oneP G) := by
    have e := hAL _ (qAt T N) d m (Fin k → 𝓞 D.F) (fun i a b => hk T N (ind ℂ (L.KN N.1) (g i)⁻¹) a b) cc c
      (fun α a b => hodgePull (al_q T N α) a b) y
    simp only [hhk, cutD]
    rw [e]
    refine Finset.sum_congr rfl fun i _ => congrArg (cc i * ·) (Finsupp.sum_congr fun α hα => ?_)
    rw [(hgeo i α (hc1 α hα)).2 y]
  have e2 := hCL p G v (L.KN N.1) m _ cc hfin (Fin k → 𝓞 D.F) c (fun α => cW L i₀ v α y)
  rw [← hdec] at e2
  have e3 := hc2 hSc.a1 hSc.ga hSc.odd v hv V ξ hξ Lv f
  rw [hLv] at e3
  rw [e1, ← e2]
  exact e3 hHecke hG y
end

section

set_option autoImplicit false

noncomputable section

namespace UpperTheory.Gal.LocalSmoothExtension.FunctionDecomposition

variable {H : Type} [Group H] {K : Subgroup H} {f : H → ℂ}

private lemma val_of_mem (hb : ∀ k ∈ K, ∀ g, f (k * g) = f g ∧ f (g * k) = f g) {g x : H}
    (hg : g ∈ DoubleCoset.doubleCoset x (K : Set H) K) : f g = f x := by
  obtain ⟨a, ha, b, hb', rfl⟩ := DoubleCoset.mem_doubleCoset.1 hg
  rw [(hb b hb' _).2, (hb a ha _).1]

private lemma ind_mem {g x : H} (hg : g ∈ DoubleCoset.doubleCoset x (K : Set H) K) :
    UpperTheory.Gal.G3.ind ℂ K x g = 1 :=
  Set.indicator_of_mem hg _

private lemma ind_notMem {g x : H} (hg : g ∉ DoubleCoset.doubleCoset x (K : Set H) K) :
    UpperTheory.Gal.G3.ind ℂ K x g = 0 :=
  Set.indicator_of_notMem hg _

private lemma mem_of_ind {g x : H} (hg : UpperTheory.Gal.G3.ind ℂ K x g ≠ 0) :
    g ∈ DoubleCoset.doubleCoset x (K : Set H) K := by
  by_contra hn
  exact hg (ind_notMem hn)

private lemma mk_of_mem {g : H} {q : DoubleCoset.Quotient (K : Set H) K}
    (hg : g ∈ DoubleCoset.doubleCoset q.out (K : Set H) K) : DoubleCoset.mk K K g = q :=
  (DoubleCoset.mem_quotToDoubleCoset_iff q g).1 hg

private lemma mem_of_mk {g : H} {q : DoubleCoset.Quotient (K : Set H) K}
    (hg : DoubleCoset.mk K K g = q) : g ∈ DoubleCoset.doubleCoset q.out (K : Set H) K :=
  (DoubleCoset.mem_quotToDoubleCoset_iff q g).2 hg

private lemma coset_ne (hb : ∀ k ∈ K, ∀ g, f (k * g) = f g ∧ f (g * k) = f g) {g : H} (hg : f g ≠ 0) :
    (g : H ⧸ K) ∈ {y : H ⧸ K | f y.out ≠ 0} := by
  obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul K g
  show f (g : H ⧸ K).out ≠ 0
  rw [hc, (hb c c.2 g).2]
  exact hg

private lemma mem_hecke (hb : ∀ k ∈ K, ∀ g, f (k * g) = f g ∧ f (g * k) = f g)
    (hfin : {y : H ⧸ K | f y.out ≠ 0}.Finite) : f ∈ Formalism.UG.Hecke ℂ K := by
  classical
  have h : Formalism.UG.IsBiInv K f ∧ Formalism.UG.FinDosetSupp K f := by
    refine ⟨fun a b g => ?_, hfin.toFinset.image Quotient.out, fun g hg => ?_⟩
    · rw [(hb b b.2 _).2, (hb a a.2 _).1]
    · obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul K g
      refine ⟨(g : H ⧸ K).out, Finset.mem_image.2 ⟨_, hfin.mem_toFinset.2 (coset_ne hb hg), rfl⟩, 1, c⁻¹, ?_⟩
      rw [hc]
      simp
  exact h

private lemma decomp (hb : ∀ k ∈ K, ∀ g, f (k * g) = f g ∧ f (g * k) = f g)
    (hfin : {y : H ⧸ K | f y.out ≠ 0}.Finite) :
    ∃ (m : ℕ) (q : Fin m → H) (c : Fin m → ℂ), (∀ i, f (q i) ≠ 0) ∧
      f = ∑ i, c i • UpperTheory.Gal.G3.ind ℂ K (q i) ∧ ∀ i g, UpperTheory.Gal.G3.ind ℂ K (q i) g ≠ 0 → f g ≠ 0 := by
  classical
  let Q : Finset (DoubleCoset.Quotient (K : Set H) K) :=
    (hfin.toFinset.image fun y => DoubleCoset.mk K K y.out).filter fun q => f q.out ≠ 0
  have hQ : ∀ q : DoubleCoset.Quotient (K : Set H) K, f q.out ≠ 0 → q ∈ Q := by
    intro q hq
    refine Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨(q.out : H ⧸ K), hfin.mem_toFinset.2 (coset_ne hb hq), ?_⟩, hq⟩
    obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul K q.out
    refine mk_of_mem (DoubleCoset.mem_doubleCoset.2 ⟨1, K.one_mem, c, c.2, ?_⟩)
    rw [hc]
    simp
  have hne : ∀ q ∈ Q, f q.out ≠ 0 := fun q hq => (Finset.mem_filter.1 hq).2
  let e := Q.equivFin
  refine ⟨Q.card, fun i => (e.symm i).1.out, fun i => f (e.symm i).1.out, fun i => hne _ (e.symm i).2, ?_, ?_⟩
  · funext g
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hg : f g = 0
    · rw [hg]
      refine (Finset.sum_eq_zero fun i _ => ?_).symm
      rw [ind_notMem fun hm => hne _ (e.symm i).2 (by rw [← val_of_mem hb hm]; exact hg), mul_zero]
    · have hp : f (DoubleCoset.mk K K g).out = f g :=
        val_of_mem hb (by
          obtain ⟨a, ha, b, hb', e'⟩ := DoubleCoset.mk_out_eq_mul K K g
          exact DoubleCoset.mem_doubleCoset.2 ⟨a, ha, b, hb', e'⟩)
      have hpQ := hQ (DoubleCoset.mk K K g) (by rw [hp]; exact hg)
      rw [Finset.sum_eq_single (e ⟨_, hpQ⟩)]
      · rw [e.symm_apply_apply]
        show f g = f (DoubleCoset.mk K K g).out * _
        rw [ind_mem (mem_of_mk rfl), hp, mul_one]
      · intro i _ hi
        rw [ind_notMem, mul_zero]
        intro hm
        apply hi
        have : (⟨_, hpQ⟩ : Q) = e.symm i := Subtype.ext (mk_of_mem hm)
        rw [this, e.apply_symm_apply]
      · intro h
        exact absurd (Finset.mem_univ _) h
  · intro i g hg
    rw [val_of_mem hb (mem_of_ind hg)]
    exact hne _ (e.symm i).2

end UpperTheory.Gal.LocalSmoothExtension.FunctionDecomposition

open UpperTheory.Gal.LocalSmoothExtension.FunctionDecomposition in
private theorem UpperTheory.Gal.LocalSmoothExtension.FunctionDecomposition.fwd {B : AlgebraicGeometry.Scheme.{0}} {Γ : Type} [Group Γ]
    (X : UpperTheory.Gal.G3.Tower B Γ) (j : X.ι) (f : Γ → ℂ) (hf : X.IsFn j f) :
    f ∈ Formalism.UG.Hecke ℂ (X.K j) ∧ ∃ (m : ℕ) (h : Fin m → Γ) (c : Fin m → ℂ), (∀ i, h i ∈ X.Δ) ∧
      f = ∑ i, c i • UpperTheory.Gal.G3.ind ℂ (X.K j) (h i)⁻¹ ∧
      ∀ i g, UpperTheory.Gal.G3.ind ℂ (X.K j) (h i)⁻¹ g ≠ 0 → f g ≠ 0 := by
  obtain ⟨hb, hΔ, hfin⟩ := hf
  obtain ⟨m, q, c, hq, e, hs⟩ := decomp hb hfin
  refine ⟨mem_hecke hb hfin, m, fun i => (q i)⁻¹, c, fun i => hΔ _ (hq i), ?_, ?_⟩
  · simpa only [inv_inv] using e
  · simpa only [inv_inv] using hs

private theorem UpperTheory.Gal.LocalSmoothExtension.FunctionDecomposition.bwd {B : AlgebraicGeometry.Scheme.{0}} {Γ : Type} [Group Γ]
    (X : UpperTheory.Gal.G3.Tower B Γ) (j : X.ι) (f : Γ → ℂ) (hf : f ∈ Formalism.UG.Hecke ℂ (X.K j))
    (hΔ : ∀ g, f g ≠ 0 → g⁻¹ ∈ X.Δ) : X.IsFn j f := by
  classical
  obtain ⟨hb, S, hS⟩ : Formalism.UG.IsBiInv (X.K j) f ∧ Formalism.UG.FinDosetSupp (X.K j) f := hf
  have hbi : ∀ k ∈ X.K j, ∀ g, f (k * g) = f g ∧ f (g * k) = f g := fun k hk g =>
    ⟨by simpa using hb ⟨k, hk⟩ 1 g, by simpa using hb 1 ⟨k, hk⟩ g⟩
  refine ⟨hbi, hΔ, ?_⟩
  have hone : ∀ s : Γ, s⁻¹ ∈ X.Δ →
      {y : Γ ⧸ X.K j | UpperTheory.Gal.G3.ind ℂ (X.K j) s y.out ≠ 0}.Finite := by
    intro s hs
    have := ((UpperTheory.Gal.G3.pFnRing X ℂ j).1 s⁻¹ hs).2.2
    simpa only [inv_inv] using this
  refine ((S.filter fun s => s⁻¹ ∈ X.Δ).finite_toSet.biUnion
    (t := fun s => {y : Γ ⧸ X.K j | UpperTheory.Gal.G3.ind ℂ (X.K j) s y.out ≠ 0}) ?_).subset ?_
  · intro s hs
    exact hone s (Finset.mem_filter.1 hs).2
  · intro y hy
    obtain ⟨s, hs, a, b, e⟩ := hS y.out hy
    have hfs : f s ≠ 0 := by
      have h1 : f y.out = f s := by rw [e]; exact hb a b s
      rw [← h1]
      exact hy
    refine Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hs, hΔ s hfs⟩)) ?_
    show UpperTheory.Gal.G3.ind ℂ (X.K j) s y.out ≠ 0
    rw [UpperTheory.Gal.LocalSmoothExtension.FunctionDecomposition.ind_mem (K := X.K j)
      (DoubleCoset.mem_doubleCoset.2 ⟨(a : Γ), a.2, (b : Γ), b.2, e⟩)]
    exact one_ne_zero

open UpperTheory.Gal.LocalSmoothExtension in
theorem UpperTheory.Gal.LocalSmoothExtension.fnDecomp_of :
    FnDecomp := by
  intro B Γ _ X j f
  exact ⟨UpperTheory.Gal.LocalSmoothExtension.FunctionDecomposition.fwd X j f, UpperTheory.Gal.LocalSmoothExtension.FunctionDecomposition.bwd X j f⟩
end
end

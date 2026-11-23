module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.trBCQ_of :
    TrHl → TrBC → WtBC → TrBCQ := by
  intro hHl hBC hWt l _ n i Z' S' Z S v p' p g _ w hpb hw hl
  haveI : IsFinite p' := MorphismProperty.of_isPullback (P := @IsFinite) hpb inferInstance
  have hw' : IsWt p' (Wt.comap v w) := hWt v p' p g w hpb hw
  have hl' : IsUnit ((l : ℕ) : Γ(S', ⊤)) := by
    have := hl.map g.appTop.hom
    rwa [map_natCast] at this
  have key : pullHl l (sch.map g) n i ∘ₗ trHl l p w n i =
      trHl l p' (Wt.comap v w) n i ∘ₗ pullHl l (sch.map v) n i := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext k
    have hk : IsUnit ((↑(l ^ k) : ℕ) : Γ(S, ⊤)) := by
      rw [Nat.cast_pow]
      exact hl.pow k
    show (pull (ZMod (l ^ k)) (sch.map g) (tw (l ^ k) i) n) ((trHl l p w n i x).1 k) =
      (trHl l p' (Wt.comap v w) n i (pullHl l (sch.map v) n i x)).1 k
    rw [hHl l n i p w hw hl x k, hHl l n i p' (Wt.comap v w) hw' hl' _ k]
    exact hBC (l ^ k) n i v p' p g w hpb hw hk (x.1 k)
  unfold trHQ pullHQ
  rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, key]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem hl_rel (hTr : TrHl) (hC : CorrEq) (l : ℕ) [Fact l.Prime] (n i : ℤ) {S Y B : Scheme.{0}} (bS : S ⟶ B) (bY : Y ⟶ B)
    [IsSeparated bY] [LocallyOfFiniteType bY] (ι : Type) [Fintype ι] (c : ι → Corr S Y) (m : ι → ℤ)
    (hb : ∀ a, (c a).f ≫ bY = (c a).p ≫ bS) (hl : IsUnit (l : Γ(S, ⊤))) (D : Set S) (hD : Dense D)
    (hz : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : gp Ω ⟶ S) (y : gp Ω ⟶ Y), pt x ∈ D →
      ∑ a, m a * (c a).cyc Ω x y = 0) :
    ∑ a, m a • (trHl l (c a).p (c a).w n i ∘ₗ pullHl l (sch.map (c a).f) n i) = 0 := by
  refine LinearMap.ext fun x => Subtype.ext (funext fun k => ?_)
  haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hq : IsUnit ((l ^ k : ℕ) : Γ(S, ⊤)) := by
    rw [Nat.cast_pow]
    exact hl.pow k
  have h := hC (l ^ k) n i bS bY ι c m hb hq D hD hz (x.1 k)
  have e : ∀ a, ((trHl l (c a).p (c a).w n i ∘ₗ pullHl l (sch.map (c a).f) n i) x).1 k =
      (c a).op (l ^ k) n i (x.1 k) := fun a => by
    haveI := (c a).fin
    exact hTr l n i (c a).p (c a).w (c a).wt hl _ k
  rw [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
  refine Eq.trans (Finset.sum_congr rfl fun a _ => ?_) h
  change m a • ((trHl l (c a).p (c a).w n i ∘ₗ pullHl l (sch.map (c a).f) n i) x).1 k = _
  rw [e a]
  rfl

theorem UpperTheory.Gal.TranscendenceTraces.corrEqQ_of :
    TrHl → CorrEq → CorrEqQ := by
  intro hTr hC l _ n i S Y B bS bY _ _ ι _ c m hb hl D hD hz
  have h := hl_rel hTr hC l n i bS bY ι c m hb hl D hD hz
  have e : ∀ a, Corr.opQ l (c a) n i = LinearMap.baseChangeHom ℤ_[l] ℚ_[l] _ _
      (trHl l (c a).p (c a).w n i ∘ₗ pullHl l (sch.map (c a).f) n i) := by
    intro a
    rw [LinearMap.baseChangeHom_apply, LinearMap.baseChange_comp]
    rfl
  simp only [e, Int.cast_smul_eq_zsmul]
  simp_rw [← map_zsmul]

  rw [← map_sum, h, map_zero]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.trCompQ_of :
    TrHl → TrComp → WtComp → TrCompQ := by
  intro hHl hC hWC l _ n i W Z S r p _ _ w' w hr hp hl
  have hlZ : IsUnit ((l : ℕ) : Γ(Z, ⊤)) := by
    simpa using hl.map p.appTop.hom
  have hcomp : trHl l (r ≫ p) (Wt.mul r w' w) n i = trHl l p w n i ∘ₗ trHl l r w' n i := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext k
    haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    have hlk : IsUnit ((l ^ k : ℕ) : Γ(S, ⊤)) := by
      rw [Nat.cast_pow]
      exact hl.pow k
    rw [LinearMap.comp_apply, hHl l n i p w hp hl, hHl l n i r w' hr hlZ,
      hHl l n i (r ≫ p) _ (hWC r p w' w hr hp) hl]
    exact hC (l ^ k) n i r p w' w hr hp hlk _
  unfold trHQ
  rw [hcomp, LinearMap.baseChange_comp]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.trHl_of :
    TrRed → TrHl := by
  intro hR l _ n i Z S p _ w hw hl x k
  have hne : ∀ k : ℕ, NeZero (l ^ k) := fun k => ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hu : ∀ k : ℕ, IsUnit ((l ^ k : ℕ) : Γ(S, ⊤)) := fun k => by
    rw [Nat.cast_pow]
    exact hl.pow _
  have hT : ∃ T : Hl l (sch.obj Z) n i →ₗ[ℤ_[l]] Hl l (sch.obj S) n i,
      ∀ (x : Hl l (sch.obj Z) n i) (k : ℕ), (T x).1 k = tr p w (l ^ k) n i (x.1 k) := by
    refine ⟨{ toFun := fun x => ⟨fun k => tr p w (l ^ k) n i (x.1 k), fun k => ?_⟩
              map_add' := fun x y => Subtype.ext (funext fun k => map_add (tr p w (l ^ k) n i) (x.1 k) (y.1 k))
              map_smul' := fun r x => Subtype.ext (funext fun k => ?_) }, fun _ _ => rfl⟩
    · haveI := hne (k + 1)
      haveI := hne k
      exact (hR (l ^ (k + 1)) (l ^ k) (pow_dvd_pow l (Nat.le_succ k)) n i p w hw (hu (k + 1)) (x.1 (k + 1))).trans
        (congrArg _ (x.2 k))
    · let f : HtL l k (sch.obj Z) n i →+ HtL l k (sch.obj S) n i := tr p w (l ^ k) n i
      change f (r • x.1 k) = r • f (x.1 k)
      rw [HtL.smul_eq l k k le_rfl, HtL.smul_eq l k k le_rfl]
      exact map_nsmul f _ _
  exact pick_spec (P := fun T : Hl l (sch.obj Z) n i →ₗ[ℤ_[l]] Hl l (sch.obj S) n i =>
    ∀ (x : Hl l (sch.obj Z) n i) (k : ℕ), (T x).1 k = tr p w (l ^ k) n i (x.1 k)) hT x k
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem trHl_pullHl (hHl : TrHl) (hDeg : TrDeg) (l : ℕ) [Fact l.Prime] (n i : ℤ) {Z S : Scheme.{0}} (p : Z ⟶ S)
    [IsFinite p] (w : Wt Z) (d : ℤ) (hw : IsWt p w) (hl : IsUnit (l : Γ(S, ⊤))) (hd : w.push p = Wt.const S d)
    (x : Hl l (sch.obj S) n i) :
    trHl l p w n i (pullHl l (sch.map p) n i x) = d • x := by
  apply Subtype.ext
  funext k
  have hk : IsUnit ((↑(l ^ k) : ℕ) : Γ(S, ⊤)) := by
    rw [Nat.cast_pow]
    exact hl.pow k
  show (trHl l p w n i (pullHl l (sch.map p) n i x)).1 k = (d • x).1 k
  rw [hHl l n i p w hw hl _ k]
  exact hDeg (l ^ k) n i p w d hw hk hd (x.1 k)

theorem UpperTheory.Gal.TranscendenceTraces.trDegQ_of :
    TrHl → TrDeg → TrDegQ := by
  intro hHl hDeg l _ n i Z S p _ w d hw hl hd
  apply LinearMap.ext
  intro z
  unfold trHQ pullHQ
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
    rw [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
      trHl_pullHl hHl hDeg l n i p w d hw hl hd y]
    simp only [TensorProduct.tmul_smul, LinearMap.smul_apply, LinearMap.id_apply]
    exact (Int.cast_smul_eq_zsmul ℚ_[l] d _).symm
  | add u v hu hv =>
    simp only [map_add (f := _)] at hu hv ⊢
    rw [hu, hv]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.trPushQ_of :
    TrPush → TrHl → WtPush → TrPushQ := by
  intro hP hH hW l _ n i Z Z' S h p _ _ w hw hl
  have key : trHl l (h ≫ p) w n i ∘ₗ pullHl l (sch.map h) n i = trHl l p (Wt.push h w) n i := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext k
    rw [LinearMap.comp_apply, hH l n i (h ≫ p) w hw hl, hH l n i p (Wt.push h w) (hW h p w hw) hl]
    haveI : NeZero (l ^ k) := ⟨pow_ne_zero k (Fact.out : Nat.Prime l).ne_zero⟩
    exact hP (l ^ k) n i h p w hw (by push_cast; exact hl.pow k) (x.1 k)
  simp only [trHQ, pullHQ, ← key, LinearMap.baseChange_comp]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem pullHQ_comp' (l : ℕ) [Fact l.Prime] {A B C : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ C) (n i : ℤ) :
    pullHQ l (sch.map (f ≫ g)) n i = pullHQ l (sch.map f) n i ∘ₗ pullHQ l (sch.map g) n i := by
  simp only [pullHQ, Functor.map_comp, pullHl_comp, LinearMap.baseChange_comp]

theorem UpperTheory.Gal.TranscendenceTraces.corrBCQ_of :
    TrBCQ → CorrBCQ := by
  intro hT l _ n i S' Y' S Y c' c g g' v hpb hf hw hl
  haveI := c.fin
  haveI := c'.fin
  simp only [Corr.opQ]
  rw [← LinearMap.comp_assoc, hT l n i v c'.p c.p g c.w hpb c.wt hl, ← hw,
    LinearMap.comp_assoc, LinearMap.comp_assoc, ← pullHQ_comp', ← pullHQ_comp', hf]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.wtBC_of :
    WtBC := by
  intro Z' S' Z S v p' p g w h hw
  unfold IsWt at *
  intro A φ hφ
  obtain ⟨ψ, hψ, e⟩ := hw ⟨A.U, A.V, A.u ≫ g, A.v ≫ v, A.r, A.pb.paste_horiz h⟩ φ hφ
  refine ⟨ψ, hψ, ?_⟩
  intro Ω _ _ x
  rw [e]
  refine finsum_congr fun z => finsum_congr fun _ => ?_
  show w Ω (z ≫ A.v ≫ v) * _ = w Ω ((z ≫ A.v) ≫ v) * _
  rw [Category.assoc]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.trDeg_of :
    TrPush → TrLin → TrDeg := by
  intro hP hL q _ n i Z S p _ w d hw hq hpush x
  have h1 := hP q n i p (𝟙 S) w (by simpa using hw) hq x
  simp only [Category.comp_id] at h1
  rw [h1, hpush]
  exact (hL q n i).2.2 S d hq x
end

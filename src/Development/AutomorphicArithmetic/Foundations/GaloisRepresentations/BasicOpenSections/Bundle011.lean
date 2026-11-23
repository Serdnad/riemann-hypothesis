module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.Bundle010
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.Bundle002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.OpCover
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.AllHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpecHolds
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

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et NumberField IsDedekindDomain TensorProduct
open GlobalTheory.GalV (HTower Htot hop galV Splits IsCorrOp IsGalois pullTot)
open UpperTheory.Gal.TranscendenceTraces (Wt trHQ)
open UpperTheory.Gal UpperTheory.Gal.Mod UpperTheory.Gal.Int.Geo
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace UpperTheory.Gal.Mod.BlockProjectionMultiplicative

variable {d : ℕ} {L : Type} [Field L]

private def blkPart (c : Fin d → ℕ) (M : Matrix (Fin d) (Fin d) L) : Matrix (Fin d) (Fin d) L :=
  fun i j => if c i = c j then M i j else 0

private theorem blkPart_add (c : Fin d → ℕ) (M N : Matrix (Fin d) (Fin d) L) :
    blkPart c (M + N) = blkPart c M + blkPart c N := by
  ext i j
  simp only [blkPart, Matrix.add_apply]
  split_ifs <;> simp

private theorem blkPart_smul (c : Fin d → ℕ) (a : L) (M : Matrix (Fin d) (Fin d) L) :
    blkPart c (a • M) = a • blkPart c M := by
  ext i j
  simp only [blkPart, Matrix.smul_apply]
  split_ifs <;> simp

private theorem blkPart_one (c : Fin d → ℕ) : blkPart c (1 : Matrix (Fin d) (Fin d) L) = 1 := by
  ext i j
  simp only [blkPart]
  by_cases h : i = j
  · subst h; simp
  · rw [Matrix.one_apply_ne h]; simp

private theorem blkPart_mul (c : Fin d → ℕ) {M N : Matrix (Fin d) (Fin d) L}
    (hM : M.BlockTriangular c) (hN : N.BlockTriangular c) :
    blkPart c (M * N) = blkPart c M * blkPart c N := by
  ext i j
  rw [Matrix.mul_apply]
  change (if c i = c j then (M * N) i j else 0) =
    ∑ k, (if c i = c k then M i k else 0) * (if c k = c j then N k j else 0)
  by_cases h : c i = c j
  · rw [if_pos h, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h1 : c i = c k
    · have h2 : c k = c j := h1.symm.trans h
      rw [if_pos h1, if_pos h2]
    · rw [if_neg h1, zero_mul]
      rcases lt_or_gt_of_ne h1 with h3 | h3
      · have h4 : c j < c k := h ▸ h3
        rw [hN h4, mul_zero]
      · rw [hM h3, zero_mul]
  · rw [if_neg h]
    symm
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases h1 : c i = c k
    · have h2 : ¬ c k = c j := fun e => h (h1.trans e)
      rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]

private theorem blkTri_pow (c : Fin d → ℕ) {M : Matrix (Fin d) (Fin d) L}
    (hM : M.BlockTriangular c) (n : ℕ) : (M ^ n).BlockTriangular c := by
  induction n with
  | zero => rw [pow_zero]; exact Matrix.blockTriangular_one
  | succ n ih => rw [pow_succ]; exact ih.mul hM

private theorem blkPart_pow (c : Fin d → ℕ) {M : Matrix (Fin d) (Fin d) L}
    (hM : M.BlockTriangular c) (n : ℕ) : blkPart c (M ^ n) = blkPart c M ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, blkPart_one]
  | succ n ih => rw [pow_succ, pow_succ, blkPart_mul c (blkTri_pow c hM n) hM, ih]

private theorem blkPart_aeval (c : Fin d → ℕ) {M : Matrix (Fin d) (Fin d) L}
    (hM : M.BlockTriangular c) (P : Polynomial L) :
    blkPart c (Polynomial.aeval M P) = Polynomial.aeval (blkPart c M) P := by
  refine Polynomial.induction_on' P (fun p q hp hq => ?_) (fun n a => ?_)
  · rw [map_add (f := _), map_add (f := _), blkPart_add, hp, hq]
  · rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, ← Algebra.smul_def, ← Algebra.smul_def,
      blkPart_smul, blkPart_pow c hM]

end UpperTheory.Gal.Mod.BlockProjectionMultiplicative

open UpperTheory.Gal.Mod.BlockProjectionMultiplicative in
theorem UpperTheory.Gal.Mod.grPass :
    GrPass := by
  intro Γ L _ _ d ρ₀ ρ hG g P h0
  obtain ⟨c, hc⟩ := hG
  obtain ⟨hT, hD⟩ := hc g
  have e : (ρ g : Matrix (Fin d) (Fin d) L) = blkPart c (ρ₀ g : Matrix (Fin d) (Fin d) L) := by
    ext i j
    exact hD i j
  rw [e, ← blkPart_aeval c hT, h0]
  ext i j
  simp [blkPart]
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et NumberField IsDedekindDomain TensorProduct
open GlobalTheory.GalV (HTower Htot hop galV Splits IsCorrOp IsGalois pullTot)
open UpperTheory.Gal.TranscendenceTraces (Wt trHQ)
open UpperTheory.Gal UpperTheory.Gal.Mod UpperTheory.Gal.Int.Geo
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace UpperTheory.Gal.Mod.HopfOperations

private theorem isUnit_nat {k : Type} [Field k] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of k)) (m : ℕ)
    (h : (m : k) ≠ 0) : IsUnit (m : Γ(X, ⊤)) := by
  have := (h.isUnit).map ((q.appTop.hom).comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)
  simpa using this

private theorem isWt_one {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] [Etale p] : TranscendenceTraces.IsWt p (Wt.const Z 1) := by
  have h := TranscendenceTraces.multBasic_holds.2.2 p
  rw [← h]
  exact TranscendenceTraces.wtFlat_holds p

private theorem fin_of_pb {A B C D : Scheme.{0}} {u : A ⟶ B} {s : A ⟶ C} {p : B ⟶ D} {e : C ⟶ D}
    (h : IsPullback u s p e) [IsFinite p] : IsFinite s :=
  MorphismProperty.of_isPullback (P := @IsFinite) h ‹_›

private theorem et_of_pb {A B C D : Scheme.{0}} {u : A ⟶ B} {s : A ⟶ C} {p : B ⟶ D} {e : C ⟶ D}
    (h : IsPullback u s p e) [Etale p] : Etale s :=
  MorphismProperty.of_isPullback (P := @Etale) h ‹_›

private theorem pullQ_comp (l : ℕ) [Fact l.Prime] {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (n i : ℤ) :
    pullHQ l (f ≫ g) n i = pullHQ l f n i ∘ₗ pullHQ l g n i := by
  unfold pullHQ; rw [pullHl_comp]; exact LinearMap.baseChange_comp _ _

private theorem gm_fst {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X Y : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of k)) {q : Y ⟶ Spec (CommRingCat.of k)} (u : X ⟶ Y)
    (hu : u ≫ q = p) : geomMap Ω p u hu ≫ pullback.fst _ _ = pullback.fst _ _ ≫ u := pullback.lift_fst _ _ _

private theorem gm_snd {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X Y : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of k)) {q : Y ⟶ Spec (CommRingCat.of k)} (u : X ⟶ Y)
    (hu : u ≫ q = p) : geomMap Ω p u hu ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _

private theorem gm_pb {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X Y : Scheme.{0}}
    (q : Y ⟶ Spec (CommRingCat.of k)) (s : X ⟶ Y) :
    IsPullback (pullback.fst (s ≫ q) (sp (algebraMap k Ω))) (geomMap Ω (s ≫ q) s rfl) s
      (pullback.fst q (sp (algebraMap k Ω))) := by
  refine IsPullback.of_bot (v₂₁ := pullback.snd q (sp (algebraMap k Ω))) (v₂₂ := q) (h₃₁ := sp (algebraMap k Ω)) ?_
    (gm_fst Ω _ _ _).symm (IsPullback.of_hasPullback q _)
  rw [gm_snd]
  exact IsPullback.of_hasPullback _ _

private theorem card_pb {A B C D P : Scheme.{0}} {a : A ⟶ C} {v : A ⟶ B} {u : C ⟶ D} {b : B ⟶ D}
    (h : IsPullback a v u b) (x : P ⟶ B) :
    Nat.card {y : P ⟶ A // y ≫ v = x} = Nat.card {y : P ⟶ C // y ≫ u = x ≫ b} :=
  Nat.card_congr
    { toFun := fun y => ⟨y.1 ≫ a, by rw [Category.assoc, h.w, reassoc_of% y.2]⟩
      invFun := fun y => ⟨h.lift y.1 x y.2, h.lift_snd _ _ _⟩
      left_inv := fun y => Subtype.ext (h.hom_ext (h.lift_fst _ _ _) (by rw [h.lift_snd, y.2]))
      right_inv := fun y => Subtype.ext (h.lift_fst _ _ _) }

end UpperTheory.Gal.Mod.HopfOperations

open UpperTheory.Gal.Mod.HopfOperations in
theorem UpperTheory.Gal.Mod.hopOp :
    GalEx → CorrOpEq → HopOp := by
  intro hGal hOp l _ k _ H Ω _ _ hlΩ g d hd
  obtain ⟨hF, hE, hcard⟩ := hd
  haveI := hF
  haveI := hE
  have hpb : IsPullback (pullback.fst (H.s g ≫ H.q) (sp (algebraMap k Ω))) (H.sΩ Ω g) (H.s g)
      (pullback.fst H.q (sp (algebraMap k Ω))) := gm_pb Ω H.q (H.s g)
  haveI hsF : IsFinite (H.sΩ Ω g) := fin_of_pb hpb
  haveI hsE : Etale (H.sΩ Ω g) := et_of_pb hpb
  have hFEt : FEt (H.sΩ Ω g) d :=
    ⟨hsF, hsE, fun K _ _ x => (card_pb hpb x).trans (hcard K _)⟩
  have hlZ : IsUnit (l : Γ(H.geomZ Ω, ⊤)) :=
    isUnit_nat (pullback.snd H.q (sp (algebraMap k Ω))) l hlΩ.ne_zero
  obtain ⟨W, c, G, iG, fG, a, σ, hG, hs⟩ := hGal (H.sΩ Ω g) d hFEt
  obtain ⟨hσ, hiso⟩ := id hs
  have hsplit := fun n : ℤ => TranscendenceTraces.adic.2.2.2.2.2.2.2.2.2 l n 0 (H.sΩ Ω g) hlZ W c d σ hσ hiso
  let T : Htot l (sch.obj (H.geomZ Ω)) →ₗ[ℚ_[l]] Htot l (sch.obj (H.geomZ Ω)) :=
    DirectSum.lmap fun n : ℤ => trHQ l (H.sΩ Ω g) (Wt.const _ 1) n 0 ∘ₗ pullHQ l (sch.map (H.tΩ Ω g)) n 0
  have hcomp : pullTot l (sch.map c) ∘ₗ T = ∑ j, pullTot l (sch.map (σ j ≫ H.tΩ Ω g)) := by
    refine DirectSum.linearMap_ext _ fun n => LinearMap.ext fun y => ?_
    have h1 := LinearMap.congr_fun (hsplit n) (pullHQ l (sch.map (H.tΩ Ω g)) n 0 y)
    simp only [LinearMap.comp_apply, LinearMap.sum_apply] at h1 ⊢

    simp only [T, pullTot, DirectSum.lmap_lof, LinearMap.comp_apply, h1, map_sum, Functor.map_comp, pullQ_comp,
    LinearMap.sum_apply]
  have hT : IsCorrOp l (H.sΩ Ω g) (H.tΩ Ω g) T :=
    ⟨W, c, G, iG, fG, a, Fin d, inferInstance, σ, hG, hs, fun x => by
      rw [← LinearMap.sum_apply, ← hcomp]; rfl⟩
  let cc : TranscendenceTraces.Corr (H.geomZ Ω) (H.geomZ Ω) :=
    ⟨_, H.sΩ Ω g, H.tΩ Ω g, Wt.const _ 1, inferInstance, isWt_one _⟩
  haveI : Etale cc.p := hsE
  have hex : ∃ T, IsCorrOp l (H.sΩ Ω g) (H.tΩ Ω g) T := ⟨T, hT⟩
  have e1 := hOp l cc rfl hlZ T hT
  have e2 := hOp l cc rfl hlZ _ hex.choose_spec
  have hh : hop l H Ω g = hex.choose := by unfold hop; rw [dite_eq_left hex]
  rw [hh, e2]
  exact e1.symm
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et NumberField IsDedekindDomain TensorProduct
open GlobalTheory.GalV (HTower Htot hop galV Splits IsCorrOp IsGalois pullTot)
open UpperTheory.Gal.TranscendenceTraces (Wt trHQ gp fib IsWt)
open UpperTheory.Gal UpperTheory.Gal.Mod UpperTheory.Gal.Int.Geo
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace UpperTheory.Gal.Mod.LiesOverOperations

private theorem unit_nat {k : Type} [Field k] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of k)) (m : ℕ)
    (h : IsUnit (m : k)) : IsUnit (m : Γ(X, ⊤)) := by
  have := h.map ((q.appTop.hom).comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)
  simpa using this

private theorem wt_one {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] [Etale p] : IsWt p (Wt.const Z 1) := by
  rw [← TranscendenceTraces.multBasic_holds.2.2 p]
  exact TranscendenceTraces.wtFlat_holds p

private theorem pq_comp (l : ℕ) [Fact l.Prime] {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (n i : ℤ) :
    pullHQ l (f ≫ g) n i = pullHQ l f n i ∘ₗ pullHQ l g n i := by
  unfold pullHQ; rw [pullHl_comp]; exact LinearMap.baseChange_comp _ _

private theorem pq_id (l : ℕ) [Fact l.Prime] (E : Spc) (n i : ℤ) : pullHQ l (𝟙 E) n i = LinearMap.id := by
  unfold pullHQ; rw [pullHl_id]; exact LinearMap.baseChange_id

section Geo
variable {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω]

private theorem geo_fst {X Y : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) {q : Y ⟶ Spec (CommRingCat.of k)} (u : X ⟶ Y)
    (hu : u ≫ q = p) : geomMap Ω p u hu ≫ pullback.fst _ _ = pullback.fst _ _ ≫ u := pullback.lift_fst _ _ _

private theorem geo_snd {X Y : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) {q : Y ⟶ Spec (CommRingCat.of k)} (u : X ⟶ Y)
    (hu : u ≫ q = p) : geomMap Ω p u hu ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _

private theorem geo_pb {X Y : Scheme.{0}} (q : Y ⟶ Spec (CommRingCat.of k)) (s : X ⟶ Y) :
    IsPullback (pullback.fst (s ≫ q) (sp (algebraMap k Ω))) (geomMap Ω (s ≫ q) s rfl) s
      (pullback.fst q (sp (algebraMap k Ω))) := by
  refine IsPullback.of_bot (v₂₁ := pullback.snd q (sp (algebraMap k Ω))) (v₂₂ := q) (h₃₁ := sp (algebraMap k Ω)) ?_
    (geo_fst Ω _ _ _).symm (IsPullback.of_hasPullback q _)
  rw [geo_snd]
  exact IsPullback.of_hasPullback _ _

end Geo

private theorem card_fib {A B C D : Scheme.{0}} {a : A ⟶ C} {v : A ⟶ B} {u : C ⟶ D} {b : B ⟶ D}
    (h : IsPullback a v u b) {Ω : Type} [Field Ω] (x : gp Ω ⟶ B) : (fib v x).ncard = (fib u (x ≫ b)).ncard := by
  have himg : fib u (x ≫ b) = (fun z => z ≫ a) '' fib v x := by
    ext y
    constructor
    · intro hy
      have hy' : y ≫ u = x ≫ b := hy
      exact ⟨h.lift y x hy', h.lift_snd _ _ _, h.lift_fst _ _ _⟩
    · rintro ⟨z, hz, rfl⟩
      have hz' : z ≫ v = x := hz
      change (z ≫ a) ≫ u = x ≫ b
      rw [Category.assoc, h.w, reassoc_of% hz']
  rw [himg]
  symm
  apply Set.InjOn.ncard_image
  intro z hz z' hz' hzz
  have e1 : z ≫ v = x := hz
  have e2 : z' ≫ v = x := hz'
  exact h.hom_ext hzz (e1.trans e2.symm)

private theorem gen_ext {O k Ω : Type} [CommRing O] [Field k] [Algebra O k] [Field Ω] [Algebra k Ω] {Y A : Scheme.{0}}
    (g : Y ⟶ Spec (CommRingCat.of O)) (a b : A ⟶ geom Ω (pullback.snd g (sp (algebraMap O k))))
    (h1 : a ≫ pullback.fst _ _ ≫ pullback.fst _ _ = b ≫ pullback.fst _ _ ≫ pullback.fst _ _)
    (h2 : a ≫ pullback.snd _ _ = b ≫ pullback.snd _ _) : a = b := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simpa only [Category.assoc] using h1
    · have e : pullback.fst (pullback.snd g (sp (algebraMap O k))) (sp (algebraMap k Ω)) ≫ pullback.snd g (sp (algebraMap O k)) =
          pullback.snd _ _ ≫ sp (algebraMap k Ω) := pullback.condition
      rw [Category.assoc, Category.assoc, e, ← Category.assoc, h2, Category.assoc]
  · exact h2

end UpperTheory.Gal.Mod.LiesOverOperations

open UpperTheory.Gal.Mod.LiesOverOperations in
theorem UpperTheory.Gal.Mod.liesOp :
    HopOp → OpCover → LiesOp := by
  intro hHop hOC
  unfold LiesOp
  intro l _ p k L _ _ H θ O _ _ C Ω _ _ hl T g d m hF hLies c hBC
  obtain ⟨-, κ, h, hκt, hw⟩ := hLies
  obtain ⟨v, hvpb, hvf, hvb, hvw⟩ := hBC
  haveI := c.fin
  haveI : IsFinite (H.s g) := hF.1
  haveI : Etale (H.s g) := hF.2.1
  haveI : IsFinite (pullback.lift (H.s g) κ h) := hw.1
  let π := piG C Ω
  have hπs : π ≫ pullback.fst _ _ ≫ pullback.fst _ _ = pullback.fst H.q (sp (algebraMap k Ω)) ≫ C.π := by
    change geomMap Ω H.q (pullback.lift C.π H.q C.ov) (pullback.lift_snd _ _ _) ≫ _ ≫ _ = _
    rw [reassoc_of% (geo_fst Ω H.q (pullback.lift C.π H.q C.ov) (pullback.lift_snd _ _ _))]
    erw [pullback.lift_fst]
  have hπb : π ≫ pullback.snd _ _ = pullback.snd _ _ := geo_snd Ω _ _ _
  have P₁ := IsPullback.of_hasPullback c.p π
  have ha : (pullback.snd c.p π ≫ pullback.fst H.q (sp (algebraMap k Ω))) ≫ C.π = (pullback.fst c.p π ≫ v) ≫ T.p := by
    rw [Category.assoc, ← hπs, Category.assoc, hvpb.w, ← Category.assoc _ c.p, pullback.condition, Category.assoc]
  let a : pullback c.p π ⟶ pullback C.π T.p := pullback.lift _ _ ha
  have P₂ : IsPullback (a ≫ pullback.snd _ _) (pullback.snd c.p π) T.p (pullback.fst H.q (sp (algebraMap k Ω)) ≫ C.π) := by
    have := P₁.paste_horiz hvpb
    rw [hπs] at this
    rwa [show a ≫ pullback.snd _ _ = pullback.fst c.p π ≫ v from pullback.lift_snd _ _ _]
  have P₃ : IsPullback a (pullback.snd c.p π) (pullback.fst C.π T.p) (pullback.fst H.q (sp (algebraMap k Ω))) :=
    IsPullback.of_right P₂ (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback C.π T.p).flip
  have hfY : pullback.fst (H.s g ≫ H.q) (sp (algebraMap k Ω)) ≫ H.s g = H.sΩ Ω g ≫ pullback.fst _ _ :=
    (geo_fst Ω _ _ _).symm
  have hu : (pullback.fst (H.s g ≫ H.q) (sp (algebraMap k Ω)) ≫ pullback.lift (H.s g) κ h) ≫ pullback.fst C.π T.p =
      H.sΩ Ω g ≫ pullback.fst H.q (sp (algebraMap k Ω)) := by
    rw [Category.assoc, pullback.lift_fst, hfY]
  let u : geom Ω (H.s g ≫ H.q) ⟶ pullback c.p π := P₃.lift _ _ hu
  have hua : u ≫ a = pullback.fst (H.s g ≫ H.q) (sp (algebraMap k Ω)) ≫ pullback.lift (H.s g) κ h := P₃.lift_fst _ _ _
  have hus : u ≫ pullback.snd c.p π = H.sΩ Ω g := P₃.lift_snd _ _ _
  have P₄ : IsPullback (pullback.fst (H.s g ≫ H.q) (sp (algebraMap k Ω))) u (pullback.lift (H.s g) κ h) a := by
    refine IsPullback.of_bot ?_ hua.symm P₃
    rw [hus, pullback.lift_fst]
    exact geo_pb Ω H.q (H.s g)
  have hav : a ≫ pullback.snd _ _ = pullback.fst c.p π ≫ v := pullback.lift_snd _ _ _
  have hlS : IsUnit (l : Γ(H.geomZ Ω, ⊤)) := unit_nat (pullback.snd H.q _) l hl
  have hl₀ := unit_nat (pullback.snd (pullback.snd C.p (sp (algebraMap O k))) (sp (algebraMap k Ω))) l hl
  have hsF : IsFinite (H.sΩ Ω g) := MorphismProperty.of_isPullback (P := @IsFinite) (geo_pb Ω H.q (H.s g)) ‹_›
  have hsE : Etale (H.sΩ Ω g) := MorphismProperty.of_isPullback (P := @Etale) (geo_pb Ω H.q (H.s g)) ‹_›
  have hwt₁ : IsWt (pullback.snd c.p π) (Wt.const _ 1) := by
    have := TranscendenceTraces.all_holds.1.1 (pullback.fst c.p π) (pullback.snd c.p π) c.p π c.w P₁ c.wt
    rw [hvw] at this
    exact this
  let c₁ : TranscendenceTraces.Corr (H.geomZ Ω) (geom Ω (pullback.snd C.p (sp (algebraMap O k)))) :=
    ⟨pullback c.p π, pullback.snd _ _, pullback.fst _ _ ≫ c.f, Wt.const _ 1, inferInstance, hwt₁⟩
  let c₂ : TranscendenceTraces.Corr (H.geomZ Ω) (geom Ω (pullback.snd C.p (sp (algebraMap O k)))) :=
    ⟨geom Ω (H.s g ≫ H.q), H.sΩ Ω g, H.tΩ Ω g ≫ π, Wt.const _ 1, hsF, wt_one _⟩
  have huF : IsFinite u := MorphismProperty.of_isPullback (P := @IsFinite) P₄ ‹_›
  have e₁ : u ≫ pullback.fst c.p π ≫ v = pullback.fst (H.s g ≫ H.q) (sp (algebraMap k Ω)) ≫ κ := by
    rw [← hav, ← Category.assoc, hua, Category.assoc, pullback.lift_snd]
  have e₂ : u ≫ pullback.fst c.p π ≫ c.p = H.sΩ Ω g ≫ π := by
    rw [pullback.condition, ← Category.assoc, hus]
  have ht : H.tΩ Ω g ≫ pullback.fst H.q (sp (algebraMap k Ω)) = pullback.fst (H.s g ≫ H.q) (sp (algebraMap k Ω)) ≫ H.t g :=
    geo_fst Ω _ _ _
  have htb : H.tΩ Ω g ≫ pullback.snd H.q (sp (algebraMap k Ω)) = pullback.snd _ _ := geo_snd Ω _ _ _
  have hsb : H.sΩ Ω g ≫ pullback.snd H.q (sp (algebraMap k Ω)) = pullback.snd _ _ := geo_snd Ω _ _ _
  have huf : u ≫ c₁.f = c₂.f := by
    change u ≫ pullback.fst c.p π ≫ c.f = H.tΩ Ω g ≫ π
    apply gen_ext C.p
    · simp only [Category.assoc]
      rw [hvf, hπs, reassoc_of% e₁, hκt, reassoc_of% ht]
    · simp only [Category.assoc]
      rw [hvb, reassoc_of% e₂, hπb, hsb, htb]
  have hcnt : ∀ (Ω' : Type) [Field Ω'] [IsAlgClosed Ω'] (x : gp Ω' ⟶ c₁.Z), (fib u x).ncard = m := by
    intro Ω' _ _ x
    rw [card_fib P₄ x]
    exact (Nat.card_coe_set_eq _).symm.trans (hw.2.2 Ω' (x ≫ a))
  have hcov : ∀ n : ℤ, c₂.opQ l n 0 = (m : ℚ_[l]) • c₁.opQ l n 0 := fun n =>
    @hOC l _ _ _ c₂ c₁ u huF m rfl rfl hus huf hlS hcnt n 0
  have hbc : ∀ n : ℤ, pullHQ l (sch.map π) n 0 ∘ₗ c.opQ l n 0 = c₁.opQ l n 0 := fun n => by
    have := TranscendenceTraces.adic.2.2.2.2.2.2.1 l n 0 c₁ c π (𝟙 _) (pullback.fst c.p π) P₁ (Category.comp_id _)
      (by rw [hvw]; rfl) hl₀
    rw [this, CategoryTheory.Functor.map_id, pq_id]
    rfl
  have key : ∀ (n : ℤ) x, trHQ l (H.sΩ Ω g) (Wt.const _ 1) n 0 (pullHQ l (sch.map (H.tΩ Ω g)) n 0 (pullHQ l (sch.map π) n 0 x)) =
      (m : ℚ_[l]) • pullHQ l (sch.map π) n 0 (c.opQ l n 0 x) := fun n x => by
    have h₁ := LinearMap.congr_fun (hcov n) x
    have h₂ := LinearMap.congr_fun (hbc n) x
    rw [LinearMap.comp_apply] at h₂
    rw [h₂, LinearMap.smul_apply] at *
    rw [← h₁]
    change _ = trHQ l (H.sΩ Ω g) (Wt.const _ 1) n 0 (pullHQ l (sch.map (H.tΩ Ω g ≫ π)) n 0 x)
    rw [Functor.map_comp, pq_comp]
    rfl
  rw [hHop l k H Ω hl g d hF]
  refine DirectSum.linearMap_ext _ fun n => LinearMap.ext fun x => ?_
  unfold pullTot
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, DirectSum.lmap_lof]
  rw [key n x, map_smul]
end

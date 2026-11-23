module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle027
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Formalism.LocalToGlobal.Divisibility.NumbersLink
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HdimEqZeroOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle723
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle551
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle561
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle534
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsPowMulPowEqOfIsZeroCechH
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

theorem surjective_to_spec_field {T : Scheme.{0}} (K : Type) [Field K] (h : T ⟶ Spec (CommRingCat.of K))
    (t : T) : Surjective h := by
  refine ⟨fun x ↦ ⟨t, ?_⟩⟩
  have : Subsingleton (PrimeSpectrum K) := inferInstance
  exact Subsingleton.elim (α := PrimeSpectrum K) _ _

theorem geometricallyConnected_of_isPullback {X X' Y Y' : Scheme.{0}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {p : X' ⟶ X}
    {q : Y' ⟶ Y} (hsq : IsPullback p f' f q) [Surjective q] [GeometricallyConnected f'] :
    GeometricallyConnected f := by
  refine ⟨fun K _ y Z fst snd hz ↦ ?_⟩
  have hb : Surjective (pullback.snd q y) :=
    MorphismProperty.of_isPullback (P := @Surjective) (IsPullback.of_hasPullback q y) inferInstance
  have k : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
  obtain ⟨z, -⟩ := (pullback.snd q y).surjective k
  let t := (pullback q y).fromSpecResidueField z
  let L := (pullback q y).residueField z
  let W := pullback f' (t ≫ pullback.fst q y)
  have hW : ConnectedSpace W :=
    GeometricallyConnected.geometrically_connectedSpace (f := f') (t ≫ pullback.fst q y)
      (pullback.fst _ _) (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
  have hbig : IsPullback (pullback.fst f' (t ≫ pullback.fst q y) ≫ p) (pullback.snd _ _) f
      ((t ≫ pullback.fst q y) ≫ q) := (IsPullback.of_hasPullback _ _).paste_horiz hsq
  have hbig' : IsPullback (pullback.fst f' (t ≫ pullback.fst q y) ≫ p) (pullback.snd _ _) f
      ((t ≫ pullback.snd q y) ≫ y) := by
    convert hbig using 1
    simp [pullback.condition]
  let w : W ⟶ Z := hz.lift (pullback.fst _ _ ≫ p) (pullback.snd _ _ ≫ t ≫ pullback.snd q y) (by
    simpa using hbig'.w)
  have hw : IsPullback w (pullback.snd f' (t ≫ pullback.fst q y)) snd (t ≫ pullback.snd q y) := by
    refine IsPullback.of_right (h₁₂ := fst) (v₁₃ := f) (h₂₂ := y) ?_ (by simp [w]) hz
    convert hbig' using 1
    simp [w]
  have hs : Surjective (t ≫ pullback.snd q y) := surjective_to_spec_field K _ (IsLocalRing.closedPoint L)
  have : Surjective w := MorphismProperty.of_isPullback (P := @Surjective) hw.flip hs
  exact w.surjective.connectedSpace w.continuous

theorem good_of_isPullback_finite_surjective : ∀ (X X' Y Y' : Scheme.{0}) (f : X ⟶ Y) (f' : X' ⟶ Y') (p : X' ⟶ X)
    (q : Y' ⟶ Y) (g : ℕ), IsPullback p f' f q → IsFinite q → Surjective q → SmoothOfRelativeDimension g f →
    GlobalTheory.DualCon.Good g f' → GlobalTheory.DualCon.Good g f := by
  intro X X' Y Y' f f' p q g hsq hq hqs hf hf'
  have := hf'.proper
  have := hf'.conn
  have : Surjective p := MorphismProperty.of_isPullback (P := @Surjective) hsq.flip hqs
  have : IsFinite p := MorphismProperty.of_isPullback (P := @IsFinite) hsq.flip hq
  have : IsProper (p ≫ f) := by rw [hsq.w]; infer_instance
  have : UniversallyClosed f := UniversallyClosed.of_comp_surjective p f
  have : IsSeparated f := GlobalTheory.NilProper.isSeparated_of_comp_surjective p f
  have : Smooth f := hf.smooth
  have : LocallyOfFiniteType f := inferInstance
  exact ⟨{}, hf, geometricallyConnected_of_isPullback hsq⟩

end GlobalTheory.DualCon
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

section

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left}

theorem memKL_mul_inv_of_eq (hL : L.IsLB) {Z : Over S} (x x' : Z ⟶ A)
    (h : ∀ (W : Over S) (a : W ⟶ A) (z : W ⟶ Z),
      CechPic.pull (a * (z ≫ x)).left (cls L hL) - CechPic.pull (z ≫ x).left (cls L hL) =
        CechPic.pull (a * (z ≫ x')).left (cls L hL) - CechPic.pull (z ≫ x').left (cls L hL)) :
    GlobalTheory.MemKL A L (x * x'⁻¹) := by
  intro p
  have hD : (Out.translDiff A L (x * x'⁻¹)).IsLB := LB.isLB_linComb hL _ _
  obtain ⟨V, hV, hc⟩ := exists_pull_eq_zero
    (CechPic.pull x.left (cls L hL) - CechPic.pull x'.left (cls L hL)) p
  refine ⟨V, hV, (cls_eq_zero_iff (pull_isLB hD _)).1 ?_⟩
  have e₁ := pull_translDiff hL (x * x'⁻¹) hD (fst Z A) (snd Z A)
  rw [lift_fst_snd, Over.id_left, pull_id] at e₁
  have k₁ : ((fst Z A ≫ x')⁻¹ * snd Z A) * (fst Z A ≫ x) = (fst Z A ≫ (x * x'⁻¹)) * snd Z A := by
    rw [MonObj.comp_mul, GrpObj.comp_inv, mul_comm _ (fst Z A ≫ x)]
    exact (_root_.mul_assoc _ _ _).symm
  have k₂ : ((fst Z A ≫ x')⁻¹ * snd Z A) * (fst Z A ≫ x') = snd Z A := by
    rw [mul_comm, mul_inv_cancel_left]
  have e₃ := h (Z ⊗ A) ((fst Z A ≫ x')⁻¹ * snd Z A) (fst Z A)
  rw [k₁, k₂] at e₃
  have e₂ : cls _ hD = CechPic.pull (fst Z A).left
      (CechPic.pull x.left (cls L hL) - CechPic.pull x'.left (cls L hL)) := by
    rw [e₁, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left]
    exact sub_eq_sub_iff_sub_eq_sub.1 e₃
  rw [cls_pull hD, e₂, ← pull_comp]
  exact pull_eq_zero_of_mem V (((fst Z A).left ⁻¹ᵁ V).ι ≫ (fst Z A).left) (fun z ↦ z.2) hc

end

theorem inj_of_quotient : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (L : LB A.left) (hL : L.IsLB), Out.RelAmple A L → ∀ (B : Over (Sp R)) (P : LB (A ⊗ B).left) (q : A ⟶ B) (hP : Fam A P), IsFinite q.left → Flat q.left → Surjective q.left → (∀ (Y : Over (Sp R)) (a x : Y ⟶ A), evc hP.isLB a (x ≫ q) = GlobalTheory.CechPic.pull (a * x).left (cls L hL) - GlobalTheory.CechPic.pull a.left (cls L hL) - GlobalTheory.CechPic.pull x.left (cls L hL) + GlobalTheory.CechPic.pull (1 : Y ⟶ A).left (cls L hL)) → (∀ (Y : Over (Sp R)) (x y : Y ⟶ A), x ≫ q = y ≫ q ↔ GlobalTheory.MemKL A L (x * y⁻¹)) → Inj A P := by
  intro R _ _ A _ g hA _ L hL _ B P q hP _ hflat hsurj hev hKL
  haveI : IsCommMonObj A := hA.comm
  haveI : Flat q.left := hflat
  haveI : Surjective q.left := hsurj
  intro Y u u' hs
  rw [same_iff hP.isLB hP.isLB] at hs
  let s₁ := pullback.snd q.left u.left
  let f₁ := pullback.fst q.left u.left
  let s₂ := pullback.snd q.left (s₁ ≫ u'.left)
  let f₂ := pullback.fst q.left (s₁ ≫ u'.left)
  let Z : Over (Sp R) := Over.mk (s₂ ≫ s₁ ≫ Y.hom)
  let c : Z ⟶ Y := Over.homMk (s₂ ≫ s₁) (by simp [Z])
  have w₁ : f₁ ≫ A.hom = s₁ ≫ Y.hom := by
    rw [← Over.w q, pullback.condition_assoc, Over.w u]
  have w₂ : f₂ ≫ A.hom = s₂ ≫ s₁ ≫ Y.hom := by
    rw [← Over.w q, pullback.condition_assoc, Category.assoc, Over.w u']
  let x : Z ⟶ A := Over.homMk (s₂ ≫ f₁) (by simp [Z, w₁])
  let x' : Z ⟶ A := Over.homMk f₂ (by simpa [Z] using w₂)
  have hx : c ≫ u = x ≫ q := by
    ext1
    simp only [Over.comp_left, c, x, Over.homMk_left, Category.assoc]
    rw [pullback.condition]
  have hx' : c ≫ u' = x' ≫ q := by
    ext1
    simp only [Over.comp_left, c, x', Over.homMk_left, Category.assoc]
    rw [pullback.condition]
  have hK : GlobalTheory.MemKL A L (x * x'⁻¹) := by
    refine memKL_mul_inv_of_eq hL x x' fun W a z ↦ ?_
    have e := congrArg (CechPic.pull (lift a (z ≫ c)).left) hs
    rw [pull_evc, pull_evc, lift_fst, lift_snd_assoc, lift_snd_assoc] at e
    simp only [Category.assoc] at e
    rw [hx, hx', ← Category.assoc, ← Category.assoc, hev, hev] at e
    rw [← sub_eq_zero] at e ⊢
    convert e using 1
    abel
  have hq : x ≫ q = x' ≫ q := (hKL Z x x').2 hK
  have : Epi c.left := by
    have : Flat c.left := by simp only [c, Over.homMk_left]; infer_instance
    have : Surjective c.left := by simp only [c, Over.homMk_left]; infer_instance
    exact Flat.epi_of_flat_of_surjective _
  have : Epi c := Over.epi_of_epi_left c
  rw [← cancel_epi c, hx, hx', hq]

end GlobalTheory.DualCon
end
end

section

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

namespace GlobalTheory.ColRows.NumReads

open Formalism.LatticeIndexTer (ph)

theorem ph_zero : ph 0 = 0 := by simp [ph]

theorem N_pred_le (N : NumDatum) (j : ℕ) (hj : j < N.R.m) : N.R.N ((j + 1) - 1) ≤ N.Nm := by
  unfold NumDatum.Nm Ranks.N
  rw [Nat.add_sub_cancel]
  have := Nat.mul_le_mul_right (N.R.t + 1) hj.le
  omega

theorem ofNum_reads : ∀ (N : NumDatum) (J : Type) [Fintype J] (eJ : J ≃ Fin N.R.m) (δ : Code N) (T : ℕ)
    (Nc lam0 C0 ce Ch Sw C1 : ℝ) (H : N.NumFacts δ Nc lam0 C0 ce Ch Sw C1),
    Reads N eJ δ T (RecNums.ofNum N eJ δ T Nc lam0 C0 ce Ch Sw C1 H) := by
  intro N J _ eJ δ T Nc lam0 C0 ce Ch Sw C1 H
  refine ⟨?_, ?_, rfl, ?_, ?_, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  · intro z
    exact N.mem_topsPl z
  · intro t _
    rfl
  · intro j z
    have hle := N_pred_le N (eJ j).1 (eJ j).2
    show ∑ i : Fin N.Nm, ph (N.nuPad δ ((eJ j).1 + 1) z i) = _
    unfold NumDatum.nuPad
    have e : ∀ i : Fin N.Nm, ph (if i.1 < N.R.N ((eJ j).1 + 1 - 1) then ((N.nu δ ((eJ j).1 + 1) z i.1 : ℚ) : ℝ) else 0) =
        (if i.1 < N.R.N ((eJ j).1 + 1 - 1) then ph ((N.nu δ ((eJ j).1 + 1) z i.1 : ℚ) : ℝ) else 0) := by
      intro i
      split_ifs
      · rfl
      · exact ph_zero
    rw [Finset.sum_congr rfl (fun i _ => e i),
      NumDatum.sum_pad (fun i => ph ((N.nu δ ((eJ j).1 + 1) z i : ℚ) : ℝ)) hle, Nat.add_sub_cancel]
  · intro j z
    have hle := N_pred_le N (eJ j).1 (eJ j).2
    show ∑ i : Fin N.Nm, N.nuPad δ ((eJ j).1 + 1) z i = _
    unfold NumDatum.nuPad NumDatum.nuAbs
    rw [NumDatum.sum_pad (fun i => ((N.nu δ ((eJ j).1 + 1) z i : ℚ) : ℝ)) hle]
    push_cast
    rfl

end GlobalTheory.ColRows.NumReads
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LatCech

variable {ι : Type} [LinearOrder ι] {V : Type} [AddCommGroup V]
  (A : Cube.{0} ι ℤ) (φ : ∀ s : Finset ι, A.obj s →+ V)

def toFam (m : ℕ) (x : Cube.Term A m) : Finset ι → V :=
  fun s => if h : s.card = m then φ s (x ⟨s, h⟩) else 0

variable {A φ}

theorem toFam_zero (m : ℕ) : toFam A φ m 0 = 0 := by
  funext s; unfold toFam; split_ifs <;> simp

theorem nonempty_of_card {m : ℕ} (hm : 0 < m) {s : Finset ι} (h : s.card = m) : s.Nonempty :=
  Finset.card_pos.1 (by rw [h]; exact hm)

theorem delta_toFam {m : ℕ} (hm : 0 < m)
    (hres : ∀ (s t : Finset ι) (h : s ⊆ t), s.Nonempty → ∀ x, φ t (Cube.res A h x) = φ s x)
    (x : Cube.Term A m) : DI.delta (toFam A φ m x) = toFam A φ (m + 1) (Cube.d A m x) := by
  funext t
  unfold DI.delta toFam
  by_cases ht : t.card = m + 1
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [dite_eq_left ht, Cube.d_apply, map_sum, ← Finset.sum_coe_sort t]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hc : (t.erase i.1).card = m := by rw [Finset.card_erase_of_mem i.2, ht]; rfl
    rw [dite_eq_left hc, map_zsmul, hres _ _ _ (nonempty_of_card hm hc)]
  · rw [dite_eq_right ht]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hc : (t.erase i).card ≠ m := by
      have := Finset.card_pos.2 ⟨i, hi⟩
      rw [Finset.card_erase_of_mem hi]; omega
    rw [dite_eq_right hc, smul_zero]

theorem toFam_inCech {N : Finset ι → AddSubgroup V} {m : ℕ} (hm : 0 < m)
    (hrange : ∀ s, s.Nonempty → (φ s).range = N s) (x : Cube.Term A m) :
    DI.InCech N m (toFam A φ m x) := by
  refine ⟨?_, fun s => ?_, fun s hs => ?_⟩
  · unfold toFam; rw [dite_eq_right (by simp; omega)]
  · unfold toFam
    split_ifs with h
    · rw [← hrange s (nonempty_of_card hm h)]; exact AddMonoidHom.mem_range.2 ⟨_, rfl⟩
    · exact zero_mem _
  · unfold toFam; rw [dite_eq_right hs]

theorem toFam_injective {m : ℕ} (hm : 0 < m) (hinj : ∀ s, s.Nonempty → Function.Injective (φ s))
    {x y : Cube.Term A m} (h : toFam A φ m x = toFam A φ m y) : x = y := by
  funext s
  have := congrFun h s.1
  unfold toFam at this
  rw [dite_eq_left s.2, dite_eq_left s.2] at this
  exact hinj _ (nonempty_of_card hm s.2) this

theorem exists_toFam {N : Finset ι → AddSubgroup V} {m : ℕ} (hm : 0 < m)
    (hrange : ∀ s, s.Nonempty → (φ s).range = N s) {c : Finset ι → V} (hc : DI.InCech N m c) :
    ∃ x : Cube.Term A m, toFam A φ m x = c := by
  have hex : ∀ s : {s : Finset ι // s.card = m}, ∃ y, φ s.1 y = c s.1 := fun s =>
    AddMonoidHom.mem_range.1 (by rw [hrange _ (nonempty_of_card hm s.2)]; exact hc.2.1 s.1)
  choose g hg using hex
  refine ⟨g, funext fun s => ?_⟩
  unfold toFam
  split_ifs with h
  · exact hg ⟨s, h⟩
  · exact (hc.2.2 s h).symm

theorem exact_iff_cechZero {N : Finset ι → AddSubgroup V} {m : ℕ} (hm : 0 < m)
    (hinj : ∀ s, s.Nonempty → Function.Injective (φ s))
    (hrange : ∀ s, s.Nonempty → (φ s).range = N s)
    (hres : ∀ (s t : Finset ι) (h : s ⊆ t), s.Nonempty → ∀ x, φ t (Cube.res A h x) = φ s x) :
    Function.Exact (Cube.d A m) (Cube.d A (m + 1)) ↔ DI.CechZero N m := by
  have hm1 : 0 < m + 1 := Nat.succ_pos m
  constructor
  · intro hex c hc hdc
    obtain ⟨x, rfl⟩ := exists_toFam (A := A) hm1 hrange hc
    have hdx : Cube.d A (m + 1) x = 0 := toFam_injective (Nat.succ_pos _) hinj
      (by rw [← delta_toFam hm1 hres, hdc, toFam_zero])
    obtain ⟨y, hy⟩ := (hex x).1 hdx
    exact ⟨toFam A φ m y, toFam_inCech hm hrange y, by rw [delta_toFam hm hres, hy]⟩
  · intro hcz x
    constructor
    · intro hdx
      obtain ⟨y', hy'c, hy'd⟩ := hcz (toFam A φ (m + 1) x) (toFam_inCech hm1 hrange x)
        (by rw [delta_toFam hm1 hres, hdx, toFam_zero])
      obtain ⟨y, rfl⟩ := exists_toFam (A := A) hm hrange hy'c
      exact ⟨y, toFam_injective hm1 hinj (by rw [← delta_toFam hm hres, hy'd])⟩
    · rintro ⟨y, rfl⟩
      exact Cube.d_d A m y

end GlobalTheory.LatCech

namespace GlobalTheory

theorem cechZero_latSec_iff_subsingleton_coh : ∀ (X : Scheme.{0}) [IsIntegral X] [X.IsSeparated]
    {V : Type} [AddCommGroup V] [Module X.functionField V] (M : X → AddSubgroup V) (F : X.Modules)
    [F.IsQuasicoherent] {ι : Type} [Fintype ι] [LinearOrder ι] (U : ι → X.Opens), LatModel M F →
    (∀ i, IsAffineOpen (U i)) → (∀ i, genericPoint X ∈ U i) → ⨆ i, U i = ⊤ → ∀ b : ℕ, 0 < b →
    (DI.CechZero (fun s => latSec M (inter U s)) b ↔ Subsingleton (coh F b)) := by
  intro X _ hsepX V _ _ M F _ ι _ _ U hL hA hg hc b hb
  letI : X.IsSeparated := hsepX
  have hsep : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i) :=
    isAffineOpen_finset_biInf hA
  let e := fun (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) => cechHEquivCoh ℤ hc hsep F n
  have hO : ∀ s : Finset ι, cechOpen ⊤ U s = inter U s := fun s => by
    simp [cechOpen, inter, Finset.inf_eq_iInf]
  have hgen : ∀ s : Finset ι, genericPoint X ∈ cechOpen ⊤ U s := fun s => by
    rw [hO, ← SetLike.mem_coe, inter, Opens.coe_finset_inf]
    simp [hg]
  let φ : ∀ s : Finset ι, (cechCube ℤ F ⊤ U).obj s →+ V := fun s =>
    (hL.val (cechOpen ⊤ U s) (hgen s)).comp (sectionsOn.toΓ F (cechOpen ⊤ U s)).toAddMonoidHom
  have hinj : ∀ s : Finset ι, s.Nonempty → Function.Injective (φ s) := fun s _ =>
    (hL.inj _ (hgen s)).comp (sectionsOn.toΓ F (cechOpen ⊤ U s)).injective
  have hrange : ∀ s : Finset ι, s.Nonempty → (φ s).range = latSec M (inter U s) := by
    intro s _
    rw [← hO s, ← hL.range _ (hgen s)]
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact AddMonoidHom.mem_range.2 ⟨_, rfl⟩
    · rintro ⟨z, rfl⟩
      exact AddMonoidHom.mem_range.2 ⟨(sectionsOn.toΓ F (cechOpen ⊤ U s)).symm z,
        congrArg (hL.val _ (hgen s)) ((sectionsOn.toΓ F (cechOpen ⊤ U s)).apply_symm_apply z)⟩
  have hres : ∀ (s t : Finset ι) (h : s ⊆ t), s.Nonempty →
      ∀ x, φ t (Cube.res (cechCube ℤ F ⊤ U) h x) = φ s x := by
    intro s t h _ x
    show hL.val _ _ (sectionsOn.toΓ F _ (sectionsOn.res ℤ F (cechOpen_anti ⊤ U h) x)) =
      hL.val _ _ (sectionsOn.toΓ F _ x)
    exact hL.res (cechOpen ⊤ U s) (cechOpen ⊤ U t) (cechOpen_anti ⊤ U h) (hgen t)
      (sectionsOn.toΓ F _ x)
  obtain ⟨p, rfl⟩ : ∃ p, b = p + 1 := ⟨b - 1, by omega⟩
  have e' := e F (p + 1)
  rw [show Subsingleton (coh F (p + 1)) ↔ Subsingleton (cechH ℤ F ⊤ U (p + 1)) from
    ⟨fun h => haveI := h; e'.injective.subsingleton,
      fun h => haveI := h; e'.symm.injective.subsingleton⟩,
    ← ModuleCat.isZero_iff_subsingleton, cechH_def, cech_def,
    ← HomologicalComplex.exactAt_iff_isZero_homology, cechComplex_exactAt_succ_iff]
  exact (LatCech.exact_iff_cechZero (φ := φ) (Nat.succ_pos p) hinj hrange hres).symm

end GlobalTheory
end
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.CobModP

theorem constantCoeff_subst_of_zero' {σ τ R : Type} [CommRing R] [Finite σ]
    {a : σ → MvPowerSeries τ R} (ha0 : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ R) :
    constantCoeff (subst a f) = constantCoeff f := by
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero ha0
  have h := constantCoeff_subst_eq_zero ha ha0 (f := f - C (constantCoeff f)) (by simp)
  rw [subst_sub ha, subst_C, map_sub, constantCoeff_C, sub_eq_zero] at h
  exact h

theorem constantCoeff_formalGroupLawCoboundaryOne_eq_zero {R : Type} [CommRing R] {d : ℕ}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (h : ∀ i, constantCoeff (μ i) = 0)
    (f : MvPowerSeries (Fin d) R) : constantCoeff (cob1 μ f) = -constantCoeff f := by
  unfold cob1 inL inR
  rw [map_sub, map_sub, constantCoeff_subst_of_zero' h,
    constantCoeff_subst_of_zero' (fun _ => constantCoeff_X _),
    constantCoeff_subst_of_zero' (fun _ => constantCoeff_X _)]
  ring

theorem coboundary_mod_p : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (κ : MvPowerSeries (Fin d ⊕ Fin d) O) (B : MvPowerSeries (Fin d) O) (y : G.A 1), constantCoeff κ = 0 → IsCoc c.μ κ → (∀ α, (p : O) ∣ coeff α (cob1 c.μ B - pull2 (nmul c.μ p) κ)) → c.ev 1 B = (p : O) • y → ∃ t : MvPowerSeries (Fin d) O, constantCoeff t = 0 ∧ ∀ α, (p : O) ∣ coeff α (κ - cob1 c.μ t) := by
  intro p _ O _ G d c κ B y hκ0 hcoc hdiv hB
  set I : Ideal O := Ideal.span {(p : O)} with hI
  set r : O →+* O ⧸ I := Ideal.Quotient.mk I with hr
  obtain ⟨c', hlaw, hev, -⟩ := GlobalTheory.T.exists_formalChart_quotient_by_ideal_with_primePow p O G d c I 1 (by
    rw [pow_one]; exact Ideal.mem_span_singleton_self _)
  have hconst := c.isLaw.const
  obtain ⟨hm1, hm2, hm3, -, hm5⟩ := GlobalTheory.T.map_coboundary_swap_pullback_commute O d c.μ hconst (O ⧸ I) r
  obtain ⟨-, hn⟩ := GlobalTheory.T.isCommFormalGroupLaw_map_natMultiple O d c.μ c.isLaw (O ⧸ I) r
  have hnc : ∀ i, constantCoeff (nmul c.μ p i) = 0 := fun i => (hn p i).1
  have hcoc' : IsCoc (fun i => map r (c.μ i)) (map r κ) :=
    ⟨by rw [← hm2, hcoc.1, map_zero], by rw [← hm3, hcoc.2]⟩
  have heq : cob1 (fun i => map r (c.μ i)) (map r B) =
      pull2 (nmul (fun i => map r (c.μ i)) p) (map r κ) := by
    have h0 : map r (cob1 c.μ B - pull2 (nmul c.μ p) κ) = 0 :=
      ((GlobalTheory.mvPowerSeries_lift_quotient O (Fin d ⊕ Fin d) I).2.1 _).2
        (fun α => Ideal.mem_span_singleton.2 (hdiv α))
    rw [map_sub, hm1, (hm5 _ hnc).1, sub_eq_zero] at h0
    rw [h0]
    congr 1
    funext i
    exact (hn p i).2
  have hp1 : (p : O) • (1 : O ⧸ I) = 0 := by
    rw [Algebra.smul_def, mul_one]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  have hev0 : c'.ev 1 (map r B) = 0 := by
    rw [hev, hB, toBase_app, ← TensorProduct.smul_tmul, hp1, TensorProduct.zero_tmul]
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_coboundary_of_pullback_nmul_coboundary p (O ⧸ I) d (G.baseChange (O ⧸ I)) c' _ hlaw (map r κ) (map r B)
    hcoc' heq hev0
  have hs0 : constantCoeff s = 0 := by
    have h1 : constantCoeff (map r κ) = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hκ0,
        map_zero]
    have hc' : ∀ i, constantCoeff (map r (c.μ i)) = 0 := fun i => by
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
        hconst i, map_zero]
    rw [hs, constantCoeff_formalGroupLawCoboundaryOne_eq_zero hc'] at h1
    exact neg_eq_zero.1 h1
  obtain ⟨t, ht, ht0⟩ := (GlobalTheory.mvPowerSeries_lift_quotient O (Fin d) I).1 s
  refine ⟨t, ht0 hs0, fun α => ?_⟩
  have h2 : map r (κ - cob1 c.μ t) = 0 := by rw [map_sub, hm1, ht, hs, sub_self]
  exact Ideal.mem_span_singleton.1 (((GlobalTheory.mvPowerSeries_lift_quotient O (Fin d ⊕ Fin d) I).2.1 _).1 h2 α)

end GlobalTheory.CobModP
end

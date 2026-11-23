module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle022
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle035
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HolDifferentiableAt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle046
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle026
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle044
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle045
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues

@[expose] public section

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

open Filter Topology GlobalTheory.TangentOrigin GlobalTheory.HolLieFrame

namespace GlobalTheory.HolFrameMatrix

theorem differentiableAt_of_mul_eq_one {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {n : ℕ}
    (G A : V → Matrix (Fin n) (Fin n) ℂ) (b₀ : V) (hA : ∀ i j, DifferentiableAt ℂ (fun b => A b i j) b₀)
    (h : ∀ᶠ b in 𝓝 b₀, G b * A b = 1) (i j : Fin n) : DifferentiableAt ℂ (fun b => G b i j) b₀ := by
  refine differentiableAt_pi.1 (differentiableAt_of_forms (fun b => G b i) b₀ fun w hw => ?_) j
  have h0 : w ᵥ* A b₀ = 0 := by
    funext i'
    have := hw (fun b => ∑ j, A b j i' • ContinuousLinearMap.proj j)
      (DifferentiableAt.fun_sum fun j _ => (hA j i').smul_const _) ?_
    · simpa [Matrix.vecMul, dotProduct, mul_comm] using this
    · refine (differentiableAt_const ((1 : Matrix (Fin n) (Fin n) ℂ) i i')).congr_of_eventuallyEq ?_
      filter_upwards [h] with b hb
      rw [← hb]
      simp [Matrix.mul_apply, mul_comm]
  have h1 : A b₀ * G b₀ = 1 := mul_eq_one_comm.1 h.self_of_nhds
  have := congrArg (· ᵥ* G b₀) h0
  simpa [Matrix.vecMul_vecMul, h1] using this

theorem differentiableAt_coord {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (U : FamilyUnif Xo σ ty) (i : Fin U.n) {m : ℕ} {B : Set (Fin m → ℂ)}
    {P : (Fin m → ℂ) → ((U.Di i).La →+ (Fin g → ℂ))} {R : Type} [CommRing R]
    (v : Sp (DualNumber R) ⟶ Xo.univ.t.G.left) (ev : (Fin m → ℂ) → (R →+* ℂ)) (hB : IsOpen B)
    (hP : IsHolPeriods (U.Di i) ty B P) (W : (Fin m → ℂ) → Fin g → ℂ)
    (hW : ∀ b ∈ B, IsDerivAt0 (fun z => (U.ex i (P b) z).left) (W b) (spMap (Chart.dualMapR (ev b)) ≫ v))
    {b₀ : Fin m → ℂ} (hb₀ : b₀ ∈ B) (hev : ∀ t, DifferentiableAt ℂ (fun b => ev b t) b₀) :
    DifferentiableAt ℂ W b₀ := by
  obtain ⟨hol₁, hol₂⟩ := U.hol i m B P hB hP
  refine differentiableAt_of_forms _ b₀ fun w hw => ?_
  have hw' : ∀ (O : Xo.univ.t.G.left.Opens) (f : Γ(Xo.univ.t.G.left, O)), ⊤ ≤ (U.ex i (P b₀) 0).left ⁻¹ᵁ O →
      fderiv ℂ (fun z => valAt' (U.ex i (P b₀) z).left O f) 0 w = 0 := by
    intro O f hO
    refine hw (fun b => fderiv ℂ (fun z => valAt' (U.ex i (P b) z).left O f) 0)
      (differentiableAt_fderiv (e := fun b z => (U.ex i (P b) z).left) hol₂ hb₀ O f hO) ?_
    obtain ⟨F, hF, hF'⟩ := exists_hol_snd v ev b₀ hev O f
      ((top_le_preimage_iff _ O).2 (by rw [(hW b₀ hb₀).1]; exact hO))
    refine hF.congr_of_eventuallyEq ?_
    filter_upwards [hF', hB.mem_nhds hb₀] with b ⟨h, e⟩ hb
    exact ((hW b hb).2 O h f).symm.trans e
  have d₁ := LocalLift.isDerivAt0_const (fun z => (U.ex i (P b₀) z).left) w hw'
  have d₀ := LocalLift.isDerivAt0_const (fun z => (U.ex i (P b₀) z).left) 0 fun _ _ _ => map_zero _
  let v₀ : epsPt (U.u i (P b₀)) ⟶ Xo.univ.t.G :=
    Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ (U.ex i (P b₀) 0).left)
      ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Over.w (U.ex i (P b₀) 0))))
  exact ((U.ex_diff i _ (hP.1 b₀ hb₀)).2 v₀ d₁.1).unique d₁ d₀

theorem dualMap_eq {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) : dualMap φ = Chart.dualMapR φ := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [dualMap, Chart.dualMapR]

theorem differentiableOn_frameMatrix : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k) (R : Type) [CommRing R] [Algebra c.F R] (y₀ : FrPt Xo c R) (B : Set (Fin T.m → ℂ)) (ψ : (Fin T.m → ℂ) → (R →ₐ[c.F] CAt σ)) (κ : (Fin T.m → ℂ) → ℂ) (z y : (Fin T.m → ℂ) → FrPt Xo c (CAt σ)) (G : (Fin T.m → ℂ) → (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ))) (a : (Fin T.m → ℂ) → CAt σ), IsOpen B → B ⊆ T.co ⁻¹' (M.X k).dom → (∀ t : R, DifferentiableOn ℂ (fun b => toC (ψ b t)) B) → (∀ b ∈ B, FrMap (ψ b) y₀ (z b) ∧ FrChg (G b) (a b) (z b) (y b) ∧ IsThetaPt T b (κ b) (y b)) → ∀ τ i j, DifferentiableOn ℂ (fun b => toC (G b τ i j)) B := by
  intro E _ _ _ H Dw l Xo c σ g e F r M k T R _ _ y₀ B ψ κ z y G a hB hsub hψ h τ i j
  have hP : IsHolPeriods (F.Di k) (fun j => relab c σ (e j).1) B (fun b => T.Pf (T.co b)) :=
    ⟨fun b hb => T.holPer.1 b (hsub hb), fun x => (T.holPer.2 x).mono hsub⟩
  have hx : ∀ b ∈ B, (z b).x = F.u k (T.Pf (T.co b)) := fun b hb => (h b hb).2.1.1.symm.trans (h b hb).2.2.1
  have hI := fun b hb => GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F k _ (hP.1 b hb)
  have htan : ∀ b ∈ B, ∀ j, IsTanAt (S := ℂ) (F.u k (T.Pf (T.co b))) ((z b).u τ j) := fun b hb j => by
    rw [← hx b hb]; exact (z b).tan τ j
  choose! W hW using fun b hb j => ((hI b hb).2.2 _ (htan b hb j)).exists
  let ev : (Fin T.m → ℂ) → (R →+* ℂ) := fun b => (ψ b).toRingHom
  intro b₀ hb₀
  refine DifferentiableAt.differentiableWithinAt ?_
  refine differentiableAt_of_mul_eq_one (fun b => Matrix.of fun i j => toC (G b τ i j))
    (fun b => Matrix.of fun j i' => W b j (e.symm ⟨τ, i'⟩)) b₀ (fun j i' => ?_) ?_ i j
  · refine differentiableAt_pi.1 (differentiableAt_coord F k (y₀.u τ j) ev hB hP (fun b => W b j) (fun b hb => ?_) hb₀
      fun t => (hψ t).differentiableAt (hB.mem_nhds hb₀)) _
    have := hW b hb j
    rw [(h b hb).1.2.1 τ j] at this
    rw [← dualMap_eq]
    exact this
  · filter_upwards [hB.mem_nhds hb₀] with b hb
    ext i i'
    have hc : IsCombAt (S := ℂ) (F.u k (T.Pf (T.co b))) ((z b).u τ) (fun j => toC (G b τ i j)) ((y b).u τ i) := by
      rw [← hx b hb]; exact (h b hb).2.1.2.1 τ i
    have hd := (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F k _ (hP.1 b hb) _ _ _ (hW b hb) _ _).1 hc
    have hd' := (h b hb).2.2.2.1 τ i
    have := congrFun (((hI b hb).2.2 _ ((hI b hb).1 _ _ hd)).unique hd hd') (e.symm ⟨τ, i'⟩)
    rw [Matrix.mul_apply, Matrix.one_apply]
    simpa [Pi.single_apply, eq_comm] using this

end GlobalTheory.HolFrameMatrix
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.TanBasisLocal

theorem dual_ext {S : Type} [CommRing S] {Y : Scheme.{0}} {n : ℕ} {h : Fin n → S}
    (hs : Ideal.span (Set.range h) = ⊤) {w w' : Sp (DualNumber S) ⟶ Y}
    (e : ∀ i, spMap (dualMap (algebraMap S (Localization.Away (h i)))) ≫ w =
      spMap (dualMap (algebraMap S (Localization.Away (h i)))) ≫ w') : w = w' := by
  have key := GlobalTheory.Frames.existsUnique_glue_dual S Y n h hs
    (fun i => spMap (dualMap (algebraMap S (Localization.Away (h i)))) ≫ w') (by
      intro i j α β hα hβ
      rw [← Category.assoc, ← Category.assoc, spMap_comp_ring, spMap_comp_ring, ← dualMap_comp, ← dualMap_comp,
        hα, hβ])
  exact key.unique e (fun _ => rfl)

theorem base_ext {S : Type} [CommRing S] {Y : Scheme.{0}} {n : ℕ} {h : Fin n → S}
    (hs : Ideal.span (Set.range h) = ⊤) {w w' : Sp S ⟶ Y}
    (e : ∀ i, spMap (algebraMap S (Localization.Away (h i))) ≫ w =
      spMap (algebraMap S (Localization.Away (h i))) ≫ w') : w = w' :=
  (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of S) h hs).openCover.hom_ext _ _ e

theorem fst_dual {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) :
    (TrivSqZeroExt.fstHom T T T).toRingHom.comp (dualMap ψ) =
      ψ.comp (TrivSqZeroExt.fstHom S S S).toRingHom :=
  RingHom.ext fun x => by simp [dualMap]

theorem eps_alg {S : Type} [CommRing S] (a : S) :
    (epsMul a).comp (algebraMap S (DualNumber S)) = algebraMap S (DualNumber S) :=
  RingHom.ext fun x => by
    ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}

theorem one_pull {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X) :
    spMap ψ ≫ (1 : Over.mk x ⟶ Xo.univ.t.G).left = (1 : Over.mk (spMap ψ ≫ x) ⟶ Xo.univ.t.G).left := by
  have e : (Over.homMk (spMap ψ) rfl : Over.mk (spMap ψ ≫ x) ⟶ Over.mk x) ≫
      (1 : Over.mk x ⟶ Xo.univ.t.G) = 1 := by
    simp [Hom.one_def]
  rw [← e, Over.comp_left]
  rfl

theorem tan_pull {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) {x : Sp S ⟶ Xo.X}
    {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsTanAt x v) :
    IsTanAt (spMap ψ ≫ x) (spMap (dualMap ψ) ≫ v) := by
  obtain ⟨h1, h2⟩ := hv
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, h1, ← Category.assoc, spMap_comp_ring, dualMap_alg, ← spMap_comp_ring,
      Category.assoc]
  · rw [← Category.assoc, spMap_comp_ring, fst_dual, ← spMap_comp_ring, Category.assoc, h2, one_pull]

theorem tan_local {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {n : ℕ} {h : Fin n → S}
    (hs : Ideal.span (Set.range h) = ⊤) {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left}
    (hv : ∀ i, IsTanAt (spMap (algebraMap S (Localization.Away (h i))) ≫ x)
      (spMap (dualMap (algebraMap S (Localization.Away (h i)))) ≫ v)) : IsTanAt x v := by
  refine ⟨dual_ext hs fun i => ?_, base_ext hs fun i => ?_⟩
  · rw [← Category.assoc, (hv i).1, ← Category.assoc, ← Category.assoc, spMap_comp_ring, spMap_comp_ring,
      dualMap_alg]
  · rw [one_pull, ← (hv i).2, ← Category.assoc, ← Category.assoc, spMap_comp_ring, spMap_comp_ring, fst_dual]

theorem comb_unique {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} {a : Fin m → S}
    {w w' : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (h : IsCombAt x v a w) (h' : IsCombAt x v a w') : w = w' := by
  obtain ⟨u, hu, rfl⟩ := h
  obtain ⟨u', hu', rfl⟩ := h'
  have : u = u' := funext fun i => Over.OverMorphism.ext ((hu i).trans (hu' i).symm)
  rw [this]

theorem comb_exists {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} (hv : ∀ i, IsTanAt x (v i)) (a : Fin m → S) :
    ∃ w, IsCombAt x v a w := by
  refine ⟨_, fun i => Over.homMk (spMap (epsMul (a i)) ≫ v i) ?_, fun i => rfl, rfl⟩
  show (spMap (epsMul (a i)) ≫ v i) ≫ Xo.univ.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x
  rw [Category.assoc, (hv i).1, ← Category.assoc, spMap_comp_ring, eps_alg]

theorem comb_pull_comp {S A C : Type} [CommRing S] [CommRing A] [CommRing C] {φ : S →+* A} {χ : S →+* C}
    (α : A →+* C) (hα : α.comp φ = χ) {x : Sp S ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left}
    {a : Fin m → A}
    (ha : IsCombAt (spMap φ ≫ x) (fun k => spMap (dualMap φ) ≫ v k) a (spMap (dualMap φ) ≫ w)) :
    IsCombAt (spMap χ ≫ x) (fun k => spMap (dualMap χ) ≫ v k) (fun j => α (a j)) (spMap (dualMap χ) ≫ w) :=
  isCombAt_pull α (by rw [← Category.assoc, spMap_comp_ring, hα])
    (fun j => by rw [← Category.assoc, spMap_comp_ring, ← dualMap_comp, hα])
    (by rw [← Category.assoc, spMap_comp_ring, ← dualMap_comp, hα]) ha

theorem coeff_compat {S A B C : Type} [CommRing S] [CommRing A] [CommRing B] [CommRing C] {φ : S →+* A}
    {ψ : S →+* B} {χ : S →+* C} (α : A →+* C) (β : B →+* C) (hα : α.comp φ = χ) (hβ : β.comp ψ = χ)
    {x : Sp S ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left}
    (hw : IsTanAt x w) (hb : TanBasis (spMap φ ≫ x) (fun k => spMap (dualMap φ) ≫ v k))
    {a : Fin m → A} {b : Fin m → B}
    (ha : IsCombAt (spMap φ ≫ x) (fun k => spMap (dualMap φ) ≫ v k) a (spMap (dualMap φ) ≫ w))
    (hb' : IsCombAt (spMap ψ ≫ x) (fun k => spMap (dualMap ψ) ≫ v k) b (spMap (dualMap ψ) ≫ w)) :
    (fun j => α (a j)) = fun j => β (b j) := by
  have hB : TanBasis (spMap χ ≫ x) (fun k => spMap (dualMap χ) ≫ v k) := by
    have := GlobalTheory.Frames.tanBasis_baseChange E H Dw l Xo _ _ α _ m _ hb
    have e1 : spMap α ≫ spMap φ ≫ x = spMap χ ≫ x := by rw [← Category.assoc, spMap_comp_ring, hα]
    have e2 : (fun k => spMap (dualMap α) ≫ spMap (dualMap φ) ≫ v k) = fun k => spMap (dualMap χ) ≫ v k :=
      funext fun k => by rw [← Category.assoc, spMap_comp_ring, ← dualMap_comp, hα]
    rw [e1, e2] at this
    exact this
  exact (hB.2 _ (tan_pull χ hw)).unique (comb_pull_comp α hα ha) (comb_pull_comp β hβ hb')

theorem tanBasis_local : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (n : ℕ) (h : Fin n → S), Ideal.span (Set.range h) = ⊤ → ∀ (m : ℕ) (v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)), (∀ i, TanBasis (spMap (algebraMap S (Localization.Away (h i))) ≫ x) (fun k => spMap (dualMap (algebraMap S (Localization.Away (h i)))) ≫ v k)) → TanBasis x v := by
  intro E _ _ _ H Dw l Xo S _ x n h hs m v hb
  have hv : ∀ k, IsTanAt x (v k) := fun k => tan_local hs fun i => (hb i).1 k
  have hb' : ∀ f : Set.range h, TanBasis (spMap (algebraMap S (Localization.Away f.1)) ≫ x)
      (fun k => spMap (dualMap (algebraMap S (Localization.Away f.1))) ≫ v k) := by
    rintro ⟨_, i, rfl⟩
    exact hb i
  refine ⟨hv, fun w hw => ?_⟩
  choose d hd hdu using fun f : Set.range h =>
    (hb' f).2 _ (tan_pull (algebraMap S (Localization.Away f.1)) hw)
  have compat : ∀ (k : Fin m) (f g : Set.range h),
      IsLocalization.Away.awayToAwayRight (P := Localization.Away (f * g : S)) f.1 g (d f k) =
        IsLocalization.Away.awayToAwayLeft g.1 f (d g k) := by
    intro k f g
    let α : Localization.Away f.1 →+* Localization.Away (f * g : S) :=
      IsLocalization.Away.awayToAwayRight f.1 g
    let β : Localization.Away g.1 →+* Localization.Away (f * g : S) :=
      IsLocalization.Away.awayToAwayLeft g.1 f
    have hα : α.comp (algebraMap S _) = algebraMap S _ :=
      RingHom.ext fun s => IsLocalization.Away.awayToAwayRight_eq f.1 g.1 s
    have hβ : β.comp (algebraMap S _) = algebraMap S _ :=
      RingHom.ext fun s => IsLocalization.Away.awayToAwayLeft_eq g.1 f.1 s
    exact congrFun (coeff_compat α β hα hβ hw (hb' f) (hd f) (hd g)) k
  choose c hc hcu using fun k => Localization.existsUnique_algebraMap_eq_of_span_eq_top (Set.range h) hs
    (fun f => d f k) (compat k)
  refine ⟨c, ?_, fun a ha => funext fun k => hcu k _ fun f => ?_⟩
  · obtain ⟨w', hw'⟩ := comb_exists hv c
    have : w' = w := dual_ext hs fun i => by
      let f : Set.range h := ⟨h i, i, rfl⟩
      have h1 := isCombAt_pull (algebraMap S (Localization.Away f.1)) rfl (fun _ => rfl) rfl hw'
      have e : (fun j => algebraMap S (Localization.Away f.1) (c j)) = d f := funext fun j => hc j f
      rw [e] at h1
      exact comb_unique h1 (hd f)
    exact this ▸ hw'
  · exact congrFun (hdu f _ (isCombAt_pull (algebraMap S (Localization.Away f.1)) rfl (fun _ => rfl) rfl ha)) k

end GlobalTheory.TanBasisLocal
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem _root_.GlobalTheory.T.existsUnique_frameChangeByMatrices : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (g : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S)) (a : Sˣ), (∀ τ, IsUnit (g τ).det) → ∃! y' : FrPt Xo c S, FrChg g (a : S) y y' := by
  first | exact @GlobalTheory.Frames.existsUnique_frChg | exact GlobalTheory.Frames.existsUnique_frChg | (intros; apply GlobalTheory.Frames.existsUnique_frChg <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem _root_.GlobalTheory.T.frameChangeByMatrices_refl_and_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (y y' y'' : FrPt Xo c S), FrChg (fun _ => 1) 1 y y ∧ ∀ (g g' : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S)) (a a' : S), FrChg g a y y' → FrChg g' a' y' y'' → FrChg (fun τ => g' τ * g τ) (a' * a) y y'' := by
  first | exact @GlobalTheory.Frames.frChg_refl_and_comp | exact GlobalTheory.Frames.frChg_refl_and_comp | (intros; apply GlobalTheory.Frames.frChg_refl_and_comp <;> assumption)
end

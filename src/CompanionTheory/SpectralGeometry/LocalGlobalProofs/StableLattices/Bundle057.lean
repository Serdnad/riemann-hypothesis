module

public import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CocycleDefinesDescendedLineBundle
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle053
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle056
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SeesawTrivialityAbelianSchemeStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TheoremOfCubeGeneratorExists
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.SimpleDistinctness.ScalarCharacterOfL2Embedding
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle073
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRTWNeAlg
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.AnyAdj
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle005
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.RigDesc

theorem mul_mid {G : Type*} [CommGroup G] (x y z p q : G) : x * (p * q) * z⁻¹ = (x * p * y⁻¹) * (y * q * z⁻¹) := by
  simp only [_root_.mul_assoc, inv_mul_cancel_left]

theorem mul_fix {G : Type*} [CommGroup G] (x y t : G) : (x * y⁻¹ * t) * x⁻¹ = t * y⁻¹ := by
  rw [_root_.mul_comm x, _root_.mul_assoc, _root_.mul_assoc, _root_.mul_comm x, _root_.mul_assoc, inv_mul_cancel, _root_.mul_one, _root_.mul_comm]

theorem gs_appTop {W Y : Scheme.{0}} (φ : W ⟶ Y) (u : Γ(Y, ⊤)ˣ) (x : W) :
    gs (𝟙 W) x ⊤ (φ.appTop.hom u.val) = (gm φ x ⊤ u).val := by
  have e := gs_pull (𝟙 W) φ x ⊤ trivial u.val
  rw [Category.id_comp] at e
  exact e.trans (gs_unit φ x ⊤ trivial u)

theorem lbDescent (hH : H90) {P Q : Scheme.{0}} (f : P ⟶ Q) (hf : Flat f) (hl : LocallyOfFinitePresentation f)
    (hs : Surjective f) (M : LB P) (hM : M.IsLB)
    (c : LB.Gen (LB.LinComb M (K := Fin 2) ![pullback.fst f f, pullback.snd f f] ![-1, 1])) (hc : c.IsGen)
    (coc : ∀ (W : Scheme.{0}) (a b d : W ⟶ P) (hab : a ≫ f = b ≫ f) (hbd : b ≫ f = d ≫ f) (w : W)
      (J : (W ⟶ P) → M.ι), Good M w J →
      val c (pullback.lift a b hab) w J * val c (pullback.lift b d hbd) w J = val c (pullback.lift a d (hab.trans hbd)) w J) :
    ∃ N : LB Q, N.IsLB ∧ LBIso M (N.pull f) := by
  obtain ⟨Z, g, hg, hgl, hgs, τ, hτ⟩ := GlobalTheory.T.line_bundle_trivial_after_flat_cover M hM
  have h₁ : Flat (g ≫ f) := inferInstance
  have h₂ : LocallyOfFinitePresentation (g ≫ f) := inferInstance
  have h₃ : Surjective (g ≫ f) := inferInstance
  obtain ⟨u, hu, hv⟩ := GlobalTheory.T.generator_descent_unit_exists g f M hM c hc τ hτ
  have good : ∀ {W : Scheme.{0}} (w : W), ∃ J : (W ⟶ P) → M.ι, Good M w J := fun w =>
    ⟨fun χ => (exists_chart hM (χ w)).choose, fun χ => (exists_chart hM (χ w)).choose_spec⟩
  have cocu : ∀ (W : Scheme.{0}) (a b d : W ⟶ Z) (hab : a ≫ g ≫ f = b ≫ g ≫ f) (hbd : b ≫ g ≫ f = d ≫ g ≫ f),
      (pullback.lift a d (hab.trans hbd)).appTop u =
        (pullback.lift a b hab).appTop u * (pullback.lift b d hbd).appTop u := by
    intro W a b d hab hbd
    have e₀ : ∀ φ : W ⟶ pullback (g ≫ f) (g ≫ f), φ.appTop u = φ.appTop.hom hu.unit.val := fun _ => rfl
    refine fn_ext fun x _ => ?_
    obtain ⟨J, hJ⟩ := good x
    have hab' : (a ≫ g) ≫ f = (b ≫ g) ≫ f := by simpa using hab
    have hbd' : (b ≫ g) ≫ f = (d ≫ g) ≫ f := by simpa using hbd
    have key : gm (pullback.lift a d (hab.trans hbd)) x ⊤ hu.unit =
        gm (pullback.lift a b hab) x ⊤ hu.unit * gm (pullback.lift b d hbd) x ⊤ hu.unit := by
      rw [hv _ _ _ _ _ _ hJ, hv _ _ _ _ _ _ hJ, hv _ _ _ _ _ _ hJ]
      rw [← coc W (a ≫ g) (b ≫ g) (d ≫ g) hab' hbd' x J hJ]
      exact mul_mid _ _ _ _ _
    rw [gs_mul (𝟙 W) x ⊤ trivial, e₀, e₀, e₀, gs_appTop, gs_appTop, gs_appTop, key, Units.val_mul]
  obtain ⟨N, hN, T, hT, hTv⟩ := GlobalTheory.T.cocycle_defines_descended_line_bundle hH (g ≫ f) h₁ h₂ h₃ u hu cocu
  refine ⟨N, hN, GlobalTheory.T.lbIso_pull_of_generator_ratio_eq g f hg hgl hgs M hM N hN τ hτ T hT fun W a b hab w i k hi hk => ?_⟩
  have hab' : a ≫ g ≫ f = b ≫ g ≫ f := by rw [← Category.assoc, hab, Category.assoc]
  obtain ⟨J, hJ, hJk⟩ := exists_good M hM w (K := PUnit) (fun _ => a ≫ g) (fun _ => k) (fun _ _ _ => rfl) (fun _ => hk)
  have hJk' : J (a ≫ g) = k := hJk PUnit.unit
  have one : ∀ (x y : W ⟶ P) (h : x ≫ f = y ≫ f), x = y → val c (pullback.lift x y h) w J = 1 := by
    rintro x _ h rfl
    exact mul_eq_left.1 (coc W x x x h h w J hJ)
  have va : val τ a w J = gm a w ((M.pull g).U fun _ => k) (τ.s fun _ => k) := val_of τ a w J _ fun _ => hJk'
  have vb : val τ b w J = gm b w ((M.pull g).U fun _ => k) (τ.s fun _ => k) := val_of τ b w J _ fun _ => by rw [← hab]; exact hJk'
  have e := hTv W a b hab' w i hi
  rw [hv _ _ _ _ _ _ hJ, one _ _ _ hab, va, vb, _root_.mul_one] at e
  rw [e]
  exact mul_fix _ _ _

theorem rigDescent : H90 → RigDescent := by
  intro hH S A X Y _ hA q hq hl hs
  refine ⟨GlobalTheory.T.seesaw_triviality_abelian_scheme S A X Y hA q hq hl hs, fun M hM hr hinv => ?_⟩
  obtain ⟨hf, hfl, hfs⟩ := GlobalTheory.T.flat_cover_base_change_product S A X Y hA q hq hl hs
  obtain ⟨c, hc, coc⟩ := GlobalTheory.T.theorem_of_cube_generator_exists S A X Y hA q M hM hr hinv
  obtain ⟨N₀, hN₀, iso⟩ := lbDescent hH _ hf hfl hfs M hM c hc coc
  let eY := (lift (1 : Y ⟶ A) (𝟙 Y)).left
  let eX := (lift (1 : X ⟶ A) (𝟙 X)).left
  let pY := (snd A Y).left
  let pX := (snd A X).left
  let f := (lift (fst A X) (snd A X ≫ q)).left
  have e₁ : eY ≫ pY = 𝟙 _ := by
    rw [← Over.comp_left, lift_snd]; rfl
  have e₂ : f ≫ pY ≫ eY = pX ≫ eX ≫ f := by
    rw [← Over.comp_left, ← Over.comp_left, ← Over.comp_left, ← Over.comp_left]
    congr 1
    ext1 <;> simp
  obtain ⟨N, hN, hc'⟩ := cls_surj (cls N₀ hN₀ - CechPic.pull pY (CechPic.pull eY (cls N₀ hN₀)))
  have hm : cls M hM = CechPic.pull f (cls N₀ hN₀) := (cls_eq_iff hM (pull_isLB hN₀ _)).2 iso
  have z : CechPic.pull eX (cls M hM) = 0 := (triv_ev_iff hM _ _).1 hr
  refine' ⟨N, hN, (triv_ev_iff hN _ _).2 ?_, (cls_eq_iff hM (pull_isLB hN _)).1 ?_⟩
  · show CechPic.pull eY (cls N hN) = 0
    rw [hc', map_sub, ← pull_comp, e₁, pull_id, sub_self]
  · show cls M hM = CechPic.pull f (cls N hN)
    rw [hc', map_sub, ← pull_comp f pY, ← pull_comp (f ≫ pY) eY, Category.assoc, e₂, pull_comp pX, pull_comp eX, ← hm, z, map_zero,
      sub_zero, hm]

end GlobalTheory.CompanionTheory.RigDesc
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.RgCOBlock

open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

abbrev lt {n : ℕ} (p q : Fin n) : FreeAlgebra ℂ (Fin n × Fin n) := FreeAlgebra.ι ℂ (p, q)

def fa (n : ℕ) (Y : ℂ) : FreeAlgebra ℂ (Fin n × Fin n) :=
  qdet (fun p q : Fin n => lt p q) (Y + ((n : ℂ) - 1) / 2)

def shift {M : ℕ} (d : Fin M → ℕ) (i : Fin M) : ℂ :=
  ((d i : ℂ) - 1) / 2 - (modExp (fun i => Fin (d i)) i : ℂ) / 2

def fb {M n : ℕ} (d : Fin M → ℕ) (h : ∑ i, d i = n) (Y : ℂ) : FreeAlgebra ℂ (Fin n × Fin n) :=
  (List.ofFn fun i : Fin M => qdet (fun p q : Fin (d i) => lt (stdBlocks d h ⟨i, p⟩) (stdBlocks d h ⟨i, q⟩))
    (Y + shift d i)).prod

theorem map_qdet {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (ψ : A →ₐ[ℂ] B) {n : ℕ}
    (X : Fin n → Fin n → A) (u : ℂ) : ψ (qdet X u) = qdet (fun p q => ψ (X p q)) u := by
  unfold qdet qminor

  rw [map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, map_list_prod, List.map_ofFn]
  congr 1
  · simp
  · congr 2
    funext k
    simp [Function.comp, Tm]
    split_ifs <;> simp

abbrev lL {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (lev : Fin n → ℕ) (E : Fin n → Fin n → Module.End ℂ V)
    (l : Fin n × Fin n) : Module.End ℂ (Cn n V) := if lev l.1 = lev l.2 then lF E l.1 l.2 else 0

section Spaces
variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def cyc (lev : Fin n → ℕ) (E : Fin n → Fin n → Module.End ℂ V) (j : ℕ) : Submodule ℂ (Cn n V) where
  carrier := {x | SuppIn (inU lev) x ∧ Deg j x ∧ bd (allT n) E x = 0}
  add_mem' := by
    rintro x y ⟨h1, h2, h3⟩ ⟨g1, g2, g3⟩
    refine ⟨fun A hA i hi => ?_, fun A hA => ?_, by rw [map_add (f := _), h3, g3, add_zero]⟩
    · by_cases hx : x A = 0
      · have hy : y A ≠ 0 := fun hy => hA (by simp [hx, hy])
        exact g1 A hy i hi
      · exact h1 A hx i hi
    · by_cases hx : x A = 0
      · have hy : y A ≠ 0 := fun hy => hA (by simp [hx, hy])
        exact g2 A hy
      · exact h2 A hx
  zero_mem' := ⟨fun A hA => absurd rfl hA, fun A hA => absurd rfl hA, map_zero _⟩
  smul_mem' := by
    rintro c x ⟨h1, h2, h3⟩
    have hne : ∀ A, (c • x) A ≠ 0 → x A ≠ 0 := fun A hA hx => hA (by simp [hx])
    exact ⟨fun A hA => h1 A (hne A hA), fun A hA => h2 A (hne A hA), by rw [map_smul, h3, smul_zero]⟩

def bdy (lev : Fin n → ℕ) (E : Fin n → Fin n → Module.End ℂ V) (j : ℕ) : Submodule ℂ (Cn n V) where
  carrier := {x | ∃ w : Cn n V, SuppIn (inU lev) w ∧ Deg (j + 1) w ∧ bd (allT n) E w = x}
  add_mem' := by
    rintro _ _ ⟨x, h1, h2, rfl⟩ ⟨y, g1, g2, rfl⟩
    refine ⟨x + y, fun A hA i hi => ?_, fun A hA => ?_, map_add _ _ _⟩
    · by_cases hx : x A = 0
      · have hy : y A ≠ 0 := fun hy => hA (by simp [hx, hy])
        exact g1 A hy i hi
      · exact h1 A hx i hi
    · by_cases hx : x A = 0
      · have hy : y A ≠ 0 := fun hy => hA (by simp [hx, hy])
        exact g2 A hy
      · exact h2 A hx
  zero_mem' := ⟨0, fun A hA => absurd rfl hA, fun A hA => absurd rfl hA, map_zero _⟩
  smul_mem' := by
    rintro c _ ⟨x, h1, h2, rfl⟩
    have hne : ∀ A, (c • x) A ≠ 0 → x A ≠ 0 := fun A hA hx => hA (by simp [hx])
    exact ⟨c • x, fun A hA => h1 A (hne A hA), fun A hA => h2 A (hne A hA), map_smul _ _ _⟩

end Spaces

def sz {n : ℕ} (lev : Fin n → ℕ) (M : ℕ) : Fin M → ℕ := fun i => (univ.filter fun a => lev a = (i : ℕ)).card

end GlobalTheory.CompanionTheory.RgCOBlock
end
end

section

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.AdjointSignNormality

open CompanionTheory.RgExh CompanionTheory.RgExh.Fin ReciprocityTheory.ChartRestriction.DS
open Formalism.REAL (GlRel qdet)

variable {n : ℕ} {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

theorem exists_adj_sum {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} (hU : IsInfUnitary ε E)
    (l : List (ℂ × List (Fin n × Fin n))) :
    ∃ B : Module.End ℂ M, ∀ x y : M,
      inner ℂ ((l.map fun c => c.1 • (c.2.map fun p => E p.1 p.2).prod).sum x) y = inner ℂ x (B y) := by
  induction l with
  | nil => exact ⟨0, fun x y => by simp⟩
  | cons c l ih =>
    obtain ⟨B, hB⟩ := ih
    refine ⟨((starRingEnd ℂ) c.1 * (c.2.map fun p => adjSign ε p.1 p.2).prod) •
      ((c.2.reverse.map Prod.swap).map fun p => E p.1 p.2).prod + B, fun x y => ?_⟩
    simp only [List.map_cons, List.sum_cons, LinearMap.add_apply, LinearMap.smul_apply, inner_add_left,
      inner_add_right, inner_smul_left, inner_smul_right, hB, eword_adjoint hU]
    ring

theorem exists_adj_qdet {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} (hU : IsInfUnitary ε E) (u : ℂ) :
    ∃ B : Module.End ℂ M, ∀ x y : M, inner ℂ (qdet E u x) y = inner ℂ x (B y) := by
  obtain ⟨l, hl⟩ := qdet_eq_sum_words E u
  rw [hl]
  exact exists_adj_sum hU l

theorem adjSign_mul_self (ε : Fin n → Bool) (a b : Fin n) : adjSign ε a b * adjSign ε a b = 1 := by
  unfold adjSign
  split_ifs <;> simp

theorem commute_adj {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} (hU : IsInfUnitary ε E)
    {A B : Module.End ℂ M} (hA : ∀ a b, Commute A (E a b)) (hB : ∀ x y : M, inner ℂ (A x) y = inner ℂ x (B y))
    (c d : Fin n) : Commute B (E c d) := by
  have key : ∀ x y : M, inner ℂ x (B (E c d y)) = inner ℂ x (E c d (B y)) := by
    intro x y
    have h1 : inner ℂ (E d c (A x)) y = adjSign ε d c * inner ℂ (A x) (E c d y) := hU d c _ _
    have h2 : inner ℂ (E d c x) (B y) = adjSign ε d c * inner ℂ x (E c d (B y)) := hU d c _ _
    have h3 : E d c (A x) = A (E d c x) := LinearMap.congr_fun (hA d c).symm.eq x
    rw [h3, hB, h2] at h1
    have hs : adjSign ε d c ≠ 0 := left_ne_zero_of_mul_eq_one (adjSign_mul_self ε d c)
    rw [← hB]
    exact (mul_left_cancel₀ hs h1).symm
  refine LinearMap.ext fun y => ?_
  have h := key (B (E c d y) - E c d (B y)) y
  have h0 : inner ℂ (B (E c d y) - E c d (B y)) (B (E c d y) - E c d (B y)) = (0 : ℂ) := by
    rw [inner_sub_right, h, sub_self]
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h0)

theorem normal_sq {A B : Module.End ℂ M} (hB : ∀ x y : M, inner ℂ (A x) y = inner ℂ x (B y)) (hc : Commute A B)
    (y : M) (h : A (A y) = 0) : A y = 0 := by
  have hn : ∀ z : M, inner ℂ (B z) (B z) = inner ℂ (A z) (A z) := by
    intro z
    have h1 : inner ℂ (A (B z)) z = inner ℂ (B z) (B z) := hB _ _
    have h2 : inner ℂ (A z) (A z) = inner ℂ z (B (A z)) := hB _ _
    have h3 : A (B z) = B (A z) := LinearMap.congr_fun hc.eq z
    rw [← h1, h3, ← inner_conj_symm, ← h2, inner_self_conj]
  have h0 : B (A y) = 0 := by
    have := hn (A y)
    rw [h, inner_zero_left] at this
    exact inner_self_eq_zero.1 this
  have h1 : inner ℂ (A y) (A y) = (0 : ℂ) := by rw [hB, h0, inner_zero_right]
  exact inner_self_eq_zero.1 h1

theorem normal_pow {A B : Module.End ℂ M} (hB : ∀ x y : M, inner ℂ (A x) y = inner ℂ x (B y)) (hc : Commute A B)
    (k : ℕ) (y : M) (h : (A ^ k) y = 0) : A y = 0 := by
  induction k generalizing y with
  | zero =>
    have : y = 0 := by simpa using h
    simp [this]
  | succ k ih =>
    refine normal_sq hB hc y (ih (A y) ?_)
    rw [pow_succ] at h
    exact h

theorem qdet_shift_pow {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} (hE : GlRel E)
    (hU : IsInfUnitary ε E) (w s : ℂ) (k : ℕ) (y : M)
    (h : ((qdet E w - s • (1 : Module.End ℂ M)) ^ k) y = 0) : (qdet E w - s • (1 : Module.End ℂ M)) y = 0 := by
  obtain ⟨B, hB⟩ := exists_adj_qdet hU w
  have hA : ∀ a b, Commute (qdet E w) (E a b) := fun a b =>
    (Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.TW.qdet_comm hE w a b)
  have hBE := commute_adj hU hA hB
  have hQ : Commute B (qdet E w) := by
    have hm : qdet E w ∈ Subalgebra.centralizer ℂ {B} := by
      unfold qdet Formalism.REAL.qminor
      refine Subalgebra.sum_mem _ fun σ _ => Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ _) ?_
      refine Subalgebra.list_prod_mem _ fun x hx => ?_
      obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
      unfold Formalism.REAL.Tm
      refine Subalgebra.add_mem _ ?_ ?_
      · split_ifs
        · exact Subalgebra.algebraMap_mem _ _
        · exact Subalgebra.zero_mem _
      · exact (Subalgebra.mem_centralizer_iff ℂ).2 fun _ hg => by rw [hg]; exact hBE _ _
    exact (Subalgebra.mem_centralizer_iff ℂ).1 hm B rfl
  have hadj : ∀ x y : M, inner ℂ ((qdet E w - s • (1 : Module.End ℂ M)) x) y =
      inner ℂ x ((B - (starRingEnd ℂ) s • (1 : Module.End ℂ M)) y) := by
    intro x y
    simp [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, hB, mul_comm]
  have hc : Commute (qdet E w - s • (1 : Module.End ℂ M)) (B - (starRingEnd ℂ) s • (1 : Module.End ℂ M)) := by
    refine Commute.sub_left (Commute.sub_right hQ.symm ?_) (Commute.sub_right ?_ ?_)
    · exact (Commute.one_right _).smul_right _
    · exact (Commute.one_left _).smul_left _
    · exact ((Commute.one_left _).smul_left _).smul_right _
  exact normal_pow hadj hc k y h

theorem scalar_of_separating_smooth_l2_maps : ScalarCharacterOfL2Embedding := by
  rintro n ε X χ hL ⟨k, hk⟩ Y
  have hσ := rreg_isURepOn ε
  have hD := isDerivedOn_smE hσ
  have hU := isInfUnitary_of_isDerivedOn hσ hD
  have hE : GlRel (smE ε (rreg ε)) := hD.glRep
  refine sub_eq_zero.1 (LinearMap.ext fun u => ?_)
  by_contra hne
  obtain ⟨c, hc, hcu⟩ := hL _ hne
  apply hcu
  set w : ℂ := Y + ((n : ℂ) - 1) / 2
  set s : ℂ := Formalism.QuantumDeterminants.capP χ Y
  have hint : ∀ x, c ((qdet X.E w - s • (1 : Module.End ℂ X.V)) x) =
      (qdet (smE ε (rreg ε)) w - s • (1 : Module.End ℂ (smD ε (rreg ε)))) (c x) := by
    intro x
    simp [Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExA.qdet_int c hc]
  have hpow : ∀ (j : ℕ) x, c (((qdet X.E w - s • (1 : Module.End ℂ X.V)) ^ j) x) =
      ((qdet (smE ε (rreg ε)) w - s • (1 : Module.End ℂ (smD ε (rreg ε)))) ^ j) (c x) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      intro x
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hint]
  have h0 := hpow k u
  rw [hk Y, LinearMap.zero_apply, map_zero] at h0
  rw [hint]
  exact qdet_shift_pow hE hU w s k _ h0.symm

end GlobalTheory.CompanionTheory.AdjointSignNormality
end
end

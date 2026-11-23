module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle031
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle035
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsChartOfMemRedKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsUnivRingBc
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AwayToAwayRightEqOfComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermitianFormsSameSignatureSameSpace
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem _root_.GlobalTheory.T.exists_frameRing_over_testRing : ∀ (K : Type) [Field K] (J : Type) [Fintype J] (m : J → ℕ) (p : TRing K), ∃ (A : TRing K) (π : p.R →ₐ[K] A.R) (X : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) A.R) (s : (A.R)ˣ), FrameRing m π X s := by
  first | exact @GlobalTheory.exists_frameRing_testRing | exact GlobalTheory.exists_frameRing_testRing | (intros; apply GlobalTheory.exists_frameRing_testRing <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem _root_.GlobalTheory.T.exists_triangularFrameRing_over_testRing : ∀ (K : Type) [Field K] (J : Type) [Fintype J] (m : J → ℕ) (p : TRing K), ∃ (A : TRing K) (π : p.R →ₐ[K] A.R) (X : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) A.R) (s : (A.R)ˣ), TriRing m π X s := by
  first | exact @GlobalTheory.exists_testRing_triRing | exact GlobalTheory.exists_testRing_triRing | (intros; apply GlobalTheory.exists_testRing_triRing <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem _root_.GlobalTheory.T.scaledBaseChange_fibreSection_calculus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S T U : Type) [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) (x : Sp S ⟶ Xo.X) (x' : Sp T ⟶ Xo.X) (x'' : Sp U ⟶ Xo.X), x' = spMap φ ≫ x → x'' = spMap ψ ≫ x' → (∀ (a : S) s s' s'', SecBC φ a x x' s s' → (SecBC ψ 1 x' x'' s' s'' ↔ SecBC (ψ.comp φ) a x x'' s s'')) ∧ (∀ (a : S) (s t : LB.Sec (PPx x)), SecBC (RingHom.id S) a x x s t ↔ ∀ i, t.f i = scal x a i * s.f i) ∧ (∀ (a : S) s (s' t' : LB.Sec (PPx x')), SecBC φ 1 x x' s s' → (SecBC φ a x x' s t' ↔ ∀ i, t'.f i = scal x' (φ a) i * s'.f i)) ∧ (∀ (a b : S) i, scal x (a * b) i = scal x a i * scal x b i ∧ scal x (a + b) i = scal x a i + scal x b i ∧ scal x 1 i = 1) := by
  first | exact @GlobalTheory.Frames.SecCalc.sec_calc | exact GlobalTheory.Frames.SecCalc.sec_calc | (intros; apply GlobalTheory.Frames.SecCalc.sec_calc <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames.ChgOf

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

theorem scal_mul' {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a b : S) (i : (PPx x).ι) :
    scal x (a * b) i = scal x a i * scal x b i := by
  simp [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, map_mul]

theorem scal_one' {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (i : (PPx x).ι) : scal x 1 i = 1 := by
  simp [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, map_one]

theorem gen_unit' {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} (s s' : LB.Sec (PPx x))
    (hs : ∀ s'' : LB.Sec (PPx x), ∃! a : S, ∀ i, s''.f i = scal x a i * s.f i)
    (hs' : ∀ s'' : LB.Sec (PPx x), ∃! a : S, ∀ i, s''.f i = scal x a i * s'.f i) :
    ∃ u : Sˣ, ∀ i, s'.f i = scal x (u : S) i * s.f i := by
  obtain ⟨a, ha, -⟩ := hs s'
  obtain ⟨b, hb, -⟩ := hs' s
  obtain ⟨c1, -, hc1⟩ := hs s
  have h1 : b * a = 1 := by
    have e1 : ∀ i, s.f i = scal x (b * a) i * s.f i := fun i => by
      rw [scal_mul', _root_.mul_assoc, ← ha i, ← hb i]
    have e2 : ∀ i, s.f i = scal x 1 i * s.f i := fun i => by rw [scal_one', _root_.one_mul]
    exact (hc1 _ e1).trans (hc1 _ e2).symm
  exact ⟨⟨a, b, by rw [mul_comm]; exact h1, h1⟩, ha⟩

theorem appLE_id' {X : Scheme.{0}} (U : X.Opens) (h : U ≤ (𝟙 X : X ⟶ X) ⁻¹ᵁ U) (f : Γ(X, U)) :
    ((𝟙 X : X ⟶ X).appLE U U h).hom f = f := by
  simp only [Scheme.Hom.appLE]
  have e : (homOfLE h).op = 𝟙 _ := Subsingleton.elim _ _
  rw [e]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

theorem spMap_id' (S : Type) [CommRing S] : spMap (RingHom.id S) = 𝟙 (Sp S) := by
  unfold spMap
  exact Spec.map_id _

theorem secBC_id_iff {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a : S) (s t : LB.Sec (PPx x)) :
    SecBC (RingHom.id S) a x x s t ↔ ∀ i, t.f i = scal x a i * s.f i := by
  constructor
  · rintro ⟨pm, h1, h2, h3⟩ i
    have hp : pm = 𝟙 _ := by
      rw [spMap_id'] at h2
      erw [Category.comp_id] at h2
      refine pullback.hom_ext ?_ ?_
      · exact h2.trans (Category.id_comp _).symm
      · exact h1.trans (Category.id_comp _).symm
    subst hp
    rw [← h3 i le_rfl]
    exact appLE_id' _ _ _
  · intro h
    refine ⟨𝟙 _, Category.id_comp _, ?_, fun i hi => ?_⟩
    · rw [spMap_id']; exact (Category.id_comp _).trans (Category.comp_id _).symm
    · rw [h i]; exact appLE_id' _ _ _

end GlobalTheory.Frames.ChgOf


open GlobalTheory.Frames.ChgOf in
theorem GlobalTheory.Frames.frChg_exists_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S), (y'.x = y.x → ∃ (g : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S)) (a : Sˣ), (∀ τ, IsUnit (g τ).det) ∧ FrChg g (a : S) y y') ∧ ∀ (g g' : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S)) (a a' : S), FrChg g a y y' → FrChg g' a' y y' → g = g' ∧ a = a' := by
  intro E _ _ _ H Dw l Xo c S _ _ y y'
  obtain ⟨x', hover', u', tan', eig', basis', s', gen'⟩ := y'
  constructor
  · intro hx
    simp only at hx
    subst hx
    obtain ⟨N, _, _, v, ρ, hv, htan, hcomb, -, -⟩ := GlobalTheory.T.exists_tangent_module_universal_group E H Dw l Xo S y.x
    choose g hg using fun τ i => (y.basis τ (u' τ i) (tan' τ i) (eig' τ i)).exists
    choose h hh using fun τ i => (basis' τ (y.u τ i) (y.tan τ i) (y.eig τ i)).exists
    obtain ⟨a, ha⟩ := gen_unit' y.s s' y.gen gen'
    refine ⟨fun τ => Matrix.of (g τ), a, fun τ => ?_, rfl, fun τ i => hg τ i, (secBC_id_iff _ _ _ _).2 ha⟩
    choose b hb using fun i => (htan _).1 (y.tan τ i)
    choose b' hb' using fun i => (htan _).1 (tan' τ i)
    have eb : y.u τ = fun i => v (b i) := funext fun i => (hb i).symm
    have eb' : u' τ = fun i => v (b' i) := funext fun i => (hb' i).symm
    have h1 : ∀ i, b' i = ∑ j, g τ i j • b j := fun i => by
      have := hg τ i
      rw [eb, hcomb, ← hb' i] at this
      exact hv this
    have h2 : ∀ i, b i = ∑ j, h τ i j • b' j := fun i => by
      have := hh τ i
      rw [eb', hcomb, ← hb i] at this
      exact hv this
    have hm : Matrix.of (h τ) * Matrix.of (g τ) = 1 := by
      funext i
      refine (y.basis τ (y.u τ i) (y.tan τ i) (y.eig τ i)).unique ?_ ?_
      · rw [← hb i, eb, hcomb]
        congr 1
        rw [h2 i]
        simp only [h1, Finset.smul_sum, smul_smul, Matrix.mul_apply, Matrix.of_apply, Finset.sum_smul]
        exact Finset.sum_comm
      · rw [← hb i, eb, hcomb]
        congr 1
        simp [Matrix.one_apply]
    exact Matrix.isUnit_det_of_left_inverse hm
  · rintro g g' a a' ⟨hx, h1, h2⟩ ⟨-, h1', h2'⟩
    simp only at hx h1 h2 h1' h2'
    subst hx
    refine ⟨funext fun τ => funext fun i => ?_, ?_⟩
    · exact (y.basis τ (u' τ i) (tan' τ i) (eig' τ i)).unique (h1 τ i) (h1' τ i)
    · exact (y.gen s').unique ((secBC_id_iff _ _ _ _).1 h2) ((secBC_id_iff _ _ _ _).1 h2')
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

theorem basis_iff_of_split {S N J : Type} [CommRing S] [AddCommGroup N] [Module S N] [Fintype J]
    (m : J → ℕ) (M : J → Submodule S N)
    (hs : ∀ n : N, ∃! f : J → N, (∀ τ, f τ ∈ M τ) ∧ ∑ τ, f τ = n)
    (b : ∀ τ, Fin (m τ) → N) (hb : ∀ τ i, b τ i ∈ M τ) (g : ℕ) (e : Fin g ≃ Σ τ : J, Fin (m τ)) :
    (∀ τ n, n ∈ M τ → ∃! a : Fin (m τ) → S, n = ∑ i, a i • b τ i) ↔
      ∀ n : N, ∃! a : Fin g → S, n = ∑ j, a j • b (e j).1 (e j).2 := by
  classical
  have key : ∀ a : ∀ τ, Fin (m τ) → S,
      ∑ j, a (e j).1 (e j).2 • b (e j).1 (e j).2 = ∑ τ, ∑ i, a τ i • b τ i := by
    intro a
    rw [e.sum_comp (fun p : Σ τ : J, Fin (m τ) => a p.1 p.2 • b p.1 p.2), Fintype.sum_sigma]
  have key' : ∀ a : Fin g → S,
      ∑ j, a j • b (e j).1 (e j).2 = ∑ τ, ∑ i, a (e.symm ⟨τ, i⟩) • b τ i := by
    intro a
    rw [← key (fun τ i => a (e.symm ⟨τ, i⟩))]
    simp
  have hmem : ∀ τ (a : Fin (m τ) → S), ∑ i, a i • b τ i ∈ M τ := fun τ a =>
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hb τ i)
  constructor
  · intro h n
    obtain ⟨f, ⟨hf, hfn⟩, hu⟩ := hs n
    choose a ha hau using fun τ => h τ (f τ) (hf τ)
    refine ⟨fun j => a (e j).1 (e j).2, ?_, ?_⟩
    · change n = ∑ j, a (e j).1 (e j).2 • b (e j).1 (e j).2
      rw [key, ← hfn]
      exact Finset.sum_congr rfl fun τ _ => ha τ
    · intro a' ha'
      rw [key'] at ha'
      have h1 := hu (fun τ => ∑ i, a' (e.symm ⟨τ, i⟩) • b τ i) ⟨fun τ => hmem τ _, ha'.symm⟩
      funext j
      have h2 := hau (e j).1 (fun i => a' (e.symm ⟨(e j).1, i⟩)) (congrFun h1 (e j).1).symm
      have h3 := congrFun h2 (e j).2
      simpa using h3
  · intro h τ n hn
    obtain ⟨a', ha', hu'⟩ := h n
    have hA : ∀ a : Fin (m τ) → S, n = ∑ i, a i • b τ i →
        (fun j => (Pi.single τ a : ∀ σ, Fin (m σ) → S) (e j).1 (e j).2) = a' := by
      intro a ha
      apply hu'
      change n = ∑ j, (Pi.single τ a : ∀ σ, Fin (m σ) → S) (e j).1 (e j).2 • b (e j).1 (e j).2
      rw [key, Finset.sum_eq_single τ]
      · simpa using ha
      · intro σ _ hσ
        simp [Pi.single_eq_of_ne hσ]
      · simp
    refine ⟨fun i => a' (e.symm ⟨τ, i⟩), ?_, ?_⟩
    · have ha2 : n = ∑ j, a' j • b (e j).1 (e j).2 := ha'
      rw [key'] at ha2
      have h1 := (hs n).unique (y₁ := fun τ => ∑ i, a' (e.symm ⟨τ, i⟩) • b τ i)
        (y₂ := Pi.single τ n) ⟨fun τ => hmem τ _, ha2.symm⟩ ⟨fun σ => by
          by_cases hσ : σ = τ
          · subst hσ; simpa using hn
          · simp [Pi.single_eq_of_ne hσ], by simp⟩
      have h2 := congrFun h1 τ
      simpa using h2.symm
    · intro a ha
      funext i
      have h1 := congrFun (hA a ha) (e.symm ⟨τ, i⟩)
      rw [← h1, Equiv.apply_symm_apply]
      simp

theorem eigBasis_iff_tanBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (x : Sp S ⟶ Xo.X) (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)), (∀ τ i, IsTanAt x (u τ i)) → (∀ τ i, IsEigAt c τ (u τ i)) → ((∀ τ w, IsTanAt x w → IsEigAt c τ w → ∃! a : Fin (Dw.mult τ) → S, IsCombAt x (u τ) a w) ↔ TanBasis x (fun j => u (e j).1 (e j).2)) := by
  intro E _ _ _ H Dw l Xo c S _ _ x u g e ht he
  obtain ⟨N, _, _, v, ρ, hinj, htan, hcomb, hρ, hsm⟩ := GlobalTheory.T.exists_tangent_module_universal_group E H Dw l Xo S x
  choose b hb using fun τ i => (htan (u τ i)).1 (ht τ i)
  obtain rfl : u = fun τ i => v (b τ i) := by funext τ i; exact (hb τ i).symm
  let M : (E →+* ℂ) → Submodule S N := fun τ =>
    ⨅ a : 𝓞 E, Module.End.eigenspace (ρ a) (algebraMap c.F S (embK c τ a))
  have hM : ∀ τ n, n ∈ M τ ↔ ∀ a, ρ a n = algebraMap c.F S (embK c τ a) • n := by
    intro τ n
    simp only [M, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  have hE : ∀ τ n, IsEigAt c τ (v n) ↔ n ∈ M τ := by
    intro τ n
    rw [hM]
    refine forall_congr' fun a => ?_
    rw [← hρ, ← hsm, hinj.eq_iff]
  have hs : ∀ n : N, ∃! f : (E →+* ℂ) → N, (∀ τ, f τ ∈ M τ) ∧ ∑ τ, f τ = n := by
    intro n
    simp only [hM]
    exact GlobalTheory.T.existsUnique_cmEmbedding_eigenvector_sum E H l c S N ρ n
  have hmain := basis_iff_of_split (fun τ => Dw.mult τ) M hs b (fun τ i => (hE τ _).1 (he τ i)) g e
  have hT : ∀ n, IsTanAt x (v n) := fun n => (htan _).2 ⟨n, rfl⟩
  have hC : ∀ (k : ℕ) (b : Fin k → N) (a : Fin k → S) (n : N),
      IsCombAt x (fun i => v (b i)) a (v n) ↔ n = ∑ i, a i • b i := by
    intro k b a n
    rw [hcomb, hinj.eq_iff]
  constructor
  · intro h
    refine ⟨fun j => hT _, fun w hw => ?_⟩
    obtain ⟨n, rfl⟩ := (htan w).1 hw
    have h1 := hmain.1 (fun τ n hn => by
      have h2 := h τ (v n) (hT n) ((hE τ n).2 hn)
      simpa only [hC] using h2) n
    simpa only [hC] using h1
  · rintro ⟨-, h⟩ τ w hw hew
    obtain ⟨n, rfl⟩ := (htan w).1 hw
    have h1 := hmain.2 (fun n => by
      have h2 := h (v n) (hT n)
      simpa only [hC] using h2) τ n ((hE τ n).1 hew)
    simpa only [hC] using h1

end GlobalTheory.Frames
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding spMap spMap_comp IsTan
open TrivSqZeroExt (inl inr)

namespace GlobalTheory.LieBaseChange

open GlobalTheory.SqZero

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
  (G : Over (Spec (CommRingCat.of R))) [GrpObj G]

def pushRHom (P : Type) [CommRing P] [Algebra R' P] [Algebra R P] [IsScalarTower R R' P] :
    (sp (R₀ := R') P ⟶ (Over.pullback (fB R R')).obj G) →* (sp (R₀ := R) P ⟶ G) where
  toFun := pushR G
  map_one' := pushR_one G
  map_mul' y y' := by
    have h := map_mul (pushHom (isGrpPullback_pullback G (fB R R')) (sp (R₀ := R') P)) y y'
    exact (congrArg (iotaB ≫ ·) h).trans (MonObj.comp_mul _ _ _)

theorem isTan_iff_mem (w : sp (R₀ := R') (DualNumber R') ⟶ (Over.pullback (fB R R')).obj G) :
    IsTan w ↔ pushR G w ∈ redKer G (RingHom.ker ((fstD R').restrictScalars R)) := by
  have e : IsTan w ↔ spMap ((fstD R').restrictScalars R) ≫ pushR G w = 1 := by
    rw [← pushR_spMap, IsTan]
    exact ⟨fun h => by rw [h, pushR_one], fun h => pushR_inj G (by rw [h, pushR_one])⟩
  rw [e]
  exact ⟨mem_redKer_of_section _ ((Algebra.ofId R' (DualNumber R')).restrictScalars R)
    (fun a => rfl), fun h => comp_eq_one_of_mem_redKer h _ fun a ha => ha⟩

variable {G} {n : ℕ}

def bcVec (R' : Type) [CommRing R'] [Algebra R R'] (v : Fin n → (epsR R ⟶ G)) (i : Fin n) :
    epsR R' ⟶ (Over.pullback (fB R R')).obj G :=
  pullR (R' := R') G (spMap (dualMapA R R') ≫ v i)

theorem pushR_bcVec (v : Fin n → (epsR R ⟶ G)) (i : Fin n) :
    pushR G (bcVec R' v i) = spMap (dualMapA R R') ≫ v i := pushR_pullR G _

theorem bcVec_left_fst (v : Fin n → (epsR R ⟶ G)) (i : Fin n) :
    (bcVec R' v i).left ≫ pullback.fst G.hom (fB R R') =
      Geo.Tor.spMap (dualMapR (algebraMap R R')) ≫ (v i).left := by
  rw [← pushR_left, pushR_bcVec]
  rfl

theorem pushR_prodPts [IsCommMonObj G] (v : Fin n → (epsR R ⟶ G)) (c : Fin n → R') :
    pushR G (prodPts c (bcVec R' v)) =
      lieExp v (fun i => (inr (c i) : DualNumber R')) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _) := by
  refine (map_list_prod (pushRHom G (DualNumber R')) _).trans ?_
  rw [List.map_ofFn, List.prod_ofFn, lieExp]
  refine Finset.prod_congr rfl fun i _ => ?_
  change pushR G (spMap _ ≫ _) = _
  rw [pushR_spMap, pushR_bcVec, ← Category.assoc, spMap_comp]
  congr 2
  refine DualNumber.algHom_ext ?_
  rw [epsTo_eps, AlgHom.comp_apply]
  change TrivSqZeroExt.map _ (dualMapA R R' (inr 1)) = _
  rw [dualMapA_inr, TrivSqZeroExt.map_inr]
  simp

theorem isLieBasis_bcVec_of [IsCommMonObj G] {v : Fin n → (epsR R ⟶ G)} (hv : ∀ i, IsTangent (v i))
    (inj : ∀ c c' : Fin n → R',
      lieExp v (fun i => (inr (c i) : DualNumber R')) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _) =
      lieExp v (fun i => (inr (c' i) : DualNumber R')) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _) →
        c = c')
    (surj : ∀ y ∈ redKer G (RingHom.ker ((fstD R').restrictScalars R)), ∃ c : Fin n → R', y =
      lieExp v (fun i => (inr (c i) : DualNumber R')) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _)) :
    IsLieBasis (bcVec R' v) := by
  refine ⟨fun i => (isTan_iff _).1 ((isTan_iff_mem G _).2 ?_), fun w hw => ?_⟩
  · rw [pushR_bcVec]
    refine mem_redKer_of_section ((fstD R').restrictScalars R)
      ((Algebra.ofId R' (DualNumber R')).restrictScalars R) (fun a => rfl) ?_
    have : ((fstD R').restrictScalars R).comp (dualMapA R R') = (Algebra.ofId R R').comp (fstD R) := by
      refine DualNumber.algHom_ext ?_
      change (dualMapA R R' (inr 1)).fst = algebraMap R R' 0
      rw [dualMapA_inr]; simp
    rw [← Category.assoc, spMap_comp, this, ← spMap_comp, Category.assoc, (isTan_iff _).2 (hv i),
      comp_one']
  · obtain ⟨c, hc⟩ := surj _ ((isTan_iff_mem G _).1 ((isTan_iff _).2 hw))
    refine ⟨c, (isLieComb_iff _ _ _).2 (pushR_inj G (by rw [hc, pushR_prodPts])), fun c' hc' => ?_⟩
    refine inj _ _ ?_
    rw [← hc, (isLieComb_iff _ _ _).1 hc', pushR_prodPts]

theorem isLieBasis_bcVec [IsCommMonObj G] [Smooth G.hom] {v : Fin n → (epsR R ⟶ G)}
    (hv : IsLieBasis v) : IsLieBasis (bcVec R' v) := by
  obtain ⟨h₁, h₂⟩ := expBij (DualNumber R') hv (RingHom.ker ((fstD R').restrictScalars R))
    (ker_fst_sq (R := R) (S := R') R')
  refine isLieBasis_bcVec_of hv.1 (fun c c' h => funext fun i => ?_) fun y hy => ?_
  · exact congrArg TrivSqZeroExt.snd
      (congrFun (h₁ _ _ (fun i => inr_mem_kerD (c i)) (fun i => inr_mem_kerD (c' i)) _ _ h) i)
  · obtain ⟨c, hc, hcJ, e⟩ := h₂ y hy
    have hc' : ∀ i, c i = inr (c i).snd := fun i =>
      have h0 : (c i).fst = 0 := hcJ i
      TrivSqZeroExt.ext h0 rfl
    exact ⟨fun i => (c i).snd, e.trans (lieExp_congr v hc' _ _)⟩

end GlobalTheory.LieBaseChange

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (spMap)

theorem exists_isLieBasis_baseChange (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R')
    (G : Over (Sp R)) (G' : Over (Sp R')) [GrpObj G] [GrpObj G'] [IsCommMonObj G] [IsCommMonObj G']
    (φ : G'.left ⟶ G.left) (h : IsGrpPullback G' G (Geo.Tor.spMap f) φ) (hs : Smooth G.hom) (n : ℕ)
    (v : Fin n → (epsR R ⟶ G)) (hv : IsLieBasis v) :
    ∃ v' : Fin n → (epsR R' ⟶ G'), IsLieBasis v' ∧
      ∀ i, (v' i).left ≫ φ = Geo.Tor.spMap (Chart.dualMapR f) ≫ (v i).left := by
  let _ := f.toAlgebra
  obtain ⟨e, he, heφ⟩ := grpPullback_iso h (isGrpPullback_pullback G (fB R R'))
  refine ⟨fun i => LieBaseChange.bcVec R' v i ≫ e.inv, isLieBasis_iso e ?_, fun i => ?_⟩
  · simpa only [Category.assoc, e.inv_hom_id, Category.comp_id] using
      LieBaseChange.isLieBasis_bcVec (R' := R') hv
  · rw [← heφ, ← Category.assoc, ← Over.comp_left, Category.assoc, e.inv_hom_id, Category.comp_id]
    exact LieBaseChange.bcVec_left_fst v i

end GlobalTheory
end
end

section

open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.hermitian_forms_same_signature_same_space : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G G' : Matrix (Fin r) (Fin r) E), (∀ a b, FD.cc (G a b) = G b a) → (∀ a b, FD.cc (G' a b) = G' b a) → G.det ≠ 0 → G'.det ≠ 0 → (∀ τ : E →+* ℂ, ∃ p0 : ℕ, (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ FD.gram τ G Q = Matrix.diagonal fun a : Fin r => ((FD.sgn p0 (a : ℕ) : ℝ) : ℂ)) ∧ (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ FD.gram τ G' Q = Matrix.diagonal fun a : Fin r => ((FD.sgn p0 (a : ℕ) : ℝ) : ℂ))) → (∃ z : E, G'.det = z * FD.cc z * G.det) → ∃ γ : GL (Fin r) E, ∀ x y, FD.herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ x) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ y) = FD.herm G' x y) → (∀ (F : Type) [Field F] [NumberField F] (δ x : F), δ ≠ 0 → x ≠ 0 → (∀ σ : F →+* ℝ, ∃ a b : ℝ, σ x = a ^ 2 - σ δ * b ^ 2) → (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), ∃ a b : v.adicCompletion F, algebraMap F (v.adicCompletion F) x = a ^ 2 - algebraMap F (v.adicCompletion F) δ * b ^ 2) → ∃ a b : F, x = a ^ 2 - δ * b ^ 2) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D D' : Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E)), D'.p = D.p → D'.q = D.q → FD.cc ξ = -ξ → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ x) (φ y))) → ∃ φ' : D'.La →ₗ[𝓞 E] (Fin r → E), (Function.Injective φ' ∧ Submodule.span E (Set.range φ') = ⊤ ∧ (∀ a b, FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D'.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ' x) (φ' y))) := by
  first | exact @GlobalTheory.model_in_same_space | exact GlobalTheory.model_in_same_space | (intros; apply GlobalTheory.model_in_same_space <;> assumption)
end

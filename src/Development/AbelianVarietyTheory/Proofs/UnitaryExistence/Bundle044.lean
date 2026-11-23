module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEquivOfSumEq
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.EqZeroOfOppositeSign
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle035
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle034
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle040
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle033
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle016
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsometryApplyEqOfFormSubNeZero
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProbabilityMeasureAutQuotientNormalized
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Hermitian
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
import Mathlib.Tactic.ENatToNat
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle003

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} in
private theorem rt0_im_ne_zero (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : H.rt0.im ≠ 0 := by
  intro h
  have hd : H.d ≠ 0 := by
    have := H.2
    omega
  have hpos : (0 : ℝ) < H.d := by exact_mod_cast Nat.pos_of_ne_zero hd
  have := congrArg Complex.re H.sqrt_neg_disc_sq
  simp [sq, Complex.mul_re, h] at this
  nlinarith [mul_self_nonneg H.rt0.re]

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} in
private theorem embedding_rt_eq_or_eq_neg (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (τ : E →+* ℂ) :
    τ H.rt = H.rt0 ∨ τ H.rt = -H.rt0 := by
  have hsq : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have := congrArg (fun x : 𝓞 E => (x : E)) H.rt_sq
    push_cast at this
    exact this
  have h2 : (τ H.rt) ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, hsq, H.sqrt_neg_disc_sq]
    simp
  exact sq_eq_sq_iff_eq_or_eq_neg.1 h2

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} in
private theorem exists_pos_form_rt_eq_im_mul {D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {g : ℕ} {ty : Fin g → E →+* ℂ}
    {P : D.La →+ (Fin g → ℂ)} (hP : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod D ty P) (c : ℂ)
    (hc : ∀ x, P (H.rt • x) = c • P x) {a : D.La} (ha : a ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ (((D.EF (H.rt • a)) a : ℤ) : ℝ) = c.im * r := by
  obtain ⟨-, hinj, -, -, Hm, -, hpos, hform⟩ := hP
  have hPa : P a ≠ 0 := fun h => ha (hinj (h.trans (map_zero P).symm))
  refine ⟨(_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (P a) (P a)).re, hpos _ hPa, ?_⟩
  have h0 : (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (P a) (P a)).im = 0 := by
    rw [hform, D.alt, Int.cast_zero]
  rw [← hform, hc]
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm] at h0 ⊢
  rw [smul_dotProduct, smul_eq_mul, Complex.mul_im, h0]
  ring


open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} in
theorem _root_.GlobalTheory.CompRat.splitLat_of_definite : ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H),
    D.p = 0 ∨ D.q = 0 → _root_.GlobalTheory.CompRat.SplitLat D := by
  intro E _ _ _ H D hpq
  obtain ⟨g, ty, hty⟩ := _root_.GlobalTheory.PureTypeModel.exists_isTypeFn H D.p D.q
  obtain ⟨P, hP⟩ := _root_.GlobalTheory.PeriodNonempty.exists_isPeriod E H D g ty hty
  have hscal : ∀ c : ℂ, (∀ i, ty i H.rt = c) → ∀ x, P (H.rt • x) = c • P x := by
    intro c hc x
    funext i
    rw [hP.1, hc]
    rfl
  have hcard : ∀ i, Nat.card {j // ty j = ty i} ≠ 0 := by
    intro i
    haveI : Nonempty {j // ty j = ty i} := ⟨⟨i, rfl⟩⟩
    exact Nat.card_pos.ne'
  have him := rt0_im_ne_zero H
  have hsq := mul_self_pos.2 him
  unfold _root_.GlobalTheory.CompRat.SplitLat
  rcases hpq with hp | hq
  · have hc : ∀ i, ty i H.rt = -H.rt0 := by
      intro i
      rcases embedding_rt_eq_or_eq_neg H (ty i) with h | h
      · exact absurd ((hty (ty i)).1 h) (by rw [hp]; exact hcard i)
      · exact h
    refine ⟨⊥, ⊤, by simp, ?_, ?_, ?_, ?_, ?_⟩
    · intro a ha b _
      rw [(Submodule.mem_bot _).1 ha]
      simp
    · rw [finrank_bot, hp]
    · rw [finrank_top, D.rank, hp, zero_add]
    · intro a ha h0
      exact absurd ((Submodule.mem_bot _).1 ha) h0
    · intro a _ ha0
      obtain ⟨r, hr, he⟩ := exists_pos_form_rt_eq_im_mul hP _ (hscal _ hc) ha0
      rw [he, Complex.neg_im]
      nlinarith [mul_pos hsq hr]
  · have hc : ∀ i, ty i H.rt = H.rt0 := by
      intro i
      by_contra h
      exact absurd ((hty (ty i)).2 h) (by rw [hq]; exact hcard i)
    refine ⟨⊤, ⊥, by simp, ?_, ?_, ?_, ?_, ?_⟩
    · intro a _ b hb
      rw [(Submodule.mem_bot _).1 hb]
      simp
    · rw [finrank_top, D.rank, hq, add_zero]
    · rw [finrank_bot, hq]
    · intro a _ ha0
      obtain ⟨r, hr, he⟩ := exists_pos_form_rt_eq_im_mul hP _ (hscal _ hc) ha0
      rw [he]
      nlinarith [mul_pos hsq hr]
    · intro a ha h0
      exact absurd ((Submodule.mem_bot _).1 ha) h0

end GlobalTheory.CompRat
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

theorem existsUnique_comb_matrix {S N : Type} [CommRing S] [AddCommGroup N] [Module S N] {n : ℕ}
    (b : Fin n → N) (g : Matrix (Fin n) (Fin n) S) (hg : IsUnit g.det) (m : N)
    (h : ∃! a : Fin n → S, m = ∑ i, a i • b i) :
    ∃! a : Fin n → S, m = ∑ i, a i • ∑ j, g i j • b j := by
  have key : ∀ a : Fin n → S, ∑ i, a i • ∑ j, g i j • b j = ∑ j, (Matrix.vecMul a g) j • b j := by
    intro a
    simp only [Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Finset.sum_smul]
    rw [Finset.sum_comm]
  obtain ⟨a, ha, hu⟩ := h
  refine ⟨Matrix.vecMul a g⁻¹, ?_, fun a' ha' => ?_⟩
  · show m = _
    rw [key, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul g hg, Matrix.vecMul_one]
    exact ha
  · have h1 := hu (Matrix.vecMul a' g) (Eq.trans ha' (key a'))
    rw [← h1, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv g hg, Matrix.vecMul_one]

theorem existsUnique_frChg (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    (g : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S)) (a : Sˣ)
    (hg : ∀ τ, IsUnit (g τ).det) : ∃! y' : FrPt Xo c S, FrChg g (a : S) y y' := by
  obtain ⟨N, _, _, v, ρ, hinj, htan, hcomb, hρ, hsm⟩ := GlobalTheory.T.exists_tangent_module_universal_group E H Dw l Xo S y.x
  have hid : y.x = spMap (RingHom.id S) ≫ y.x := by
    have : spMap (RingHom.id S) = 𝟙 (Sp S) := by
      simp [spMap]
    rw [this, Category.id_comp]
  obtain ⟨-, hbc, -, hsc⟩ := GlobalTheory.T.scaledBaseChange_fibreSection_calculus E H Dw l Xo S S S (RingHom.id S) (RingHom.id S) y.x y.x y.x hid hid
  obtain ⟨s', hs', hs'u⟩ := GlobalTheory.T.existsUnique_scaledBaseChange_fibreSection E H Dw l Xo S S (RingHom.id S) (a : S) y.x y.x hid y.s
  have heig : ∀ τ m, IsEigAt c τ (v m) ↔ ∀ z : 𝓞 E, ρ z m = algebraMap c.F S (embK c τ z) • m := by
    intro τ m
    refine forall_congr' fun z => ?_
    rw [← hρ, ← hsm, hinj.eq_iff]
  choose b hb using fun τ i => (htan (y.u τ i)).1 (y.tan τ i)
  have hbu : ∀ τ, y.u τ = fun i => v (b τ i) := fun τ => funext fun i => (hb τ i).symm
  have hs'f := (hbc (a : S) y.s s').1 hs'
  refine ⟨⟨y.x, y.x_over, fun τ i => v (∑ j, g τ i j • b τ j), fun τ i => (htan _).2 ⟨_, rfl⟩,
    fun τ i => ?_, fun τ w hw hwe => ?_, s', fun t => ?_⟩, ⟨rfl, fun τ i => ?_, hs'⟩, ?_⟩
  · rw [heig]
    intro z

    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := (heig τ (b τ j)).1 (by rw [hb]; exact y.eig τ j) z
    rw [map_smul, this, smul_comm]
  · have h := y.basis τ w hw hwe
    obtain ⟨m, rfl⟩ := (htan w).1 hw
    rw [hbu τ] at h
    simp only [hcomb, hinj.eq_iff] at h ⊢
    exact existsUnique_comb_matrix (b τ) (g τ) (hg τ) m h
  · obtain ⟨e, he, heu⟩ := y.gen t
    refine ⟨e * (a⁻¹ : Sˣ), fun i => ?_, fun e' he' => ?_⟩
    · rw [hs'f, ← _root_.mul_assoc, ← (hsc _ _ i).1, Units.inv_mul_cancel_right]
      exact he i
    · have := heu (e' * a) (fun i => by rw [(hsc _ _ i).1, _root_.mul_assoc, ← hs'f]; exact he' i)
      rw [← this, Units.mul_inv_cancel_right]
  · rw [hbu τ, hcomb]
  · rintro ⟨x', hx', u', ht', he', hb', t', hg'⟩ ⟨hx, hu, hs⟩
    dsimp only at hx hu hs
    subst hx
    have e1 : t' = s' := hs'u t' hs
    have e2 : u' = fun τ i => v (∑ j, g τ i j • b τ j) := by
      funext τ i
      have := hu τ i
      rw [hbu τ, hcomb] at this
      exact this
    subst e1 e2
    rfl

end GlobalTheory.Frames
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem _root_.GlobalTheory.T.eigenBasis_iff_tangentBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (x : Sp S ⟶ Xo.X) (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)), (∀ τ i, IsTanAt x (u τ i)) → (∀ τ i, IsEigAt c τ (u τ i)) → ((∀ τ w, IsTanAt x w → IsEigAt c τ w → ∃! a : Fin (Dw.mult τ) → S, IsCombAt x (u τ) a w) ↔ TanBasis x (fun j => u (e j).1 (e j).2)) := by
  first | exact @GlobalTheory.Frames.eigBasis_iff_tanBasis | exact GlobalTheory.Frames.eigBasis_iff_tanBasis | (intros; apply GlobalTheory.Frames.eigBasis_iff_tanBasis <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem _root_.GlobalTheory.T.frameChange_exists_unique_of_same_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S), (y'.x = y.x → ∃ (g : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S)) (a : Sˣ), (∀ τ, IsUnit (g τ).det) ∧ FrChg g (a : S) y y') ∧ ∀ (g g' : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S)) (a a' : S), FrChg g a y y' → FrChg g' a' y y' → g = g' ∧ a = a' := by
  first | exact @GlobalTheory.Frames.frChg_exists_unique | exact GlobalTheory.Frames.frChg_exists_unique | (intros; apply GlobalTheory.Frames.frChg_exists_unique <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
open scoped CategoryTheory.Obj

namespace GlobalTheory.Frames

theorem tanBasis_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S T : Type) [CommRing S] [CommRing T] (φ : S →+* T) (x : Sp S ⟶ Xo.X) (n : ℕ) (v : Fin n → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)), TanBasis x v → TanBasis (spMap φ ≫ x) (fun i => spMap (dualMap φ) ≫ v i) := by
  intro E _ _ _ H Dw l Xo S T _ _ φ x n v hv
  have := Xo.univ.t.semi.comm
  have := Xo.univ.t.semi.smooth
  have h₁ := isGrpPullback_pullback Xo.univ.t.G x
  have h₂ := isGrpPullback_pullback ((Over.pullback x).obj Xo.univ.t.G) (spMap φ)
  have h₃ := h₂.comp h₁
  have : IsCommMonObj ((Over.pullback x).obj Xo.univ.t.G) := Functor.isCommMonObj_obj
  have : IsCommMonObj ((Over.pullback (spMap φ)).obj ((Over.pullback x).obj Xo.univ.t.G)) :=
    Functor.isCommMonObj_obj
  obtain ⟨a₁, b₁⟩ := GlobalTheory.T.lieBasis_iff_tangentBasis_pullback_universal E H Dw l Xo S x _ _ h₁
  obtain ⟨-, b₃⟩ := GlobalTheory.T.lieBasis_iff_tangentBasis_pullback_universal E H Dw l Xo T _ _ _ h₃
  choose u hu using fun i => a₁ (v i) (hv.1 i)
  have hb : IsLieBasis u := (b₁ n u).2 (by rw [funext hu]; exact hv)
  have hs : Smooth ((Over.pullback x).obj Xo.univ.t.G).hom :=
    inferInstanceAs (Smooth (pullback.snd Xo.univ.t.G.hom x))
  obtain ⟨u', hb', hu'⟩ := GlobalTheory.exists_isLieBasis_baseChange S T φ _ _ _ h₂ hs n u hb
  have e : Chart.dualMapR φ = dualMap φ := by
    ext a <;> rfl
  have key := (b₃ n u').1 hb'
  convert key using 2 with i
  rw [← Category.assoc, hu', e, Category.assoc, hu]

end GlobalTheory.Frames
end
end

section

set_option autoImplicit false

open MeasureTheory Topology Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume
open scoped ENNReal

namespace GlobalTheory.PeterssonRigid

theorem conjT_isHermitian {r : ℕ} {M : Matrix (Fin r) (Fin r) ℂ} (hM : M.IsHermitian)
    (x : Matrix (Fin r) (Fin r) ℂ) : (xᵀ * M * x.map (starRingEnd ℂ)).IsHermitian := by
  have h := Matrix.isHermitian_mul_mul_conjTranspose xᵀ hM
  have e : (xᵀ)ᴴ = x.map (starRingEnd ℂ) := by ext a b; rfl
  rwa [e] at h

theorem det_conjT {r : ℕ} {M x : Matrix (Fin r) (Fin r) ℂ} (hM : M.det ≠ 0) (hx : x.det ≠ 0) :
    (xᵀ * M * x.map (starRingEnd ℂ)).det ≠ 0 := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    show x.map (starRingEnd ℂ) = (starRingEnd ℂ).mapMatrix x from rfl, ← RingHom.map_det]
  exact mul_ne_zero (mul_ne_zero hx hM) ((map_ne_zero _).2 hx)

theorem conjT_mul {r : ℕ} (M x y : Matrix (Fin r) (Fin r) ℂ) :
    (x * y)ᵀ * M * (x * y).map (starRingEnd ℂ) = yᵀ * (xᵀ * M * x.map (starRingEnd ℂ)) * y.map (starRingEnd ℂ) := by
  rw [Matrix.transpose_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]

theorem conjT_one {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) :
    (1 : Matrix (Fin r) (Fin r) ℂ)ᵀ * M * (1 : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) = M := by
  simp

theorem conjT_cancel {r : ℕ} {x : Matrix (Fin r) (Fin r) ℂ} (hx : x.det ≠ 0) (M : Matrix (Fin r) (Fin r) ℂ) :
    (x⁻¹)ᵀ * (xᵀ * M * x.map (starRingEnd ℂ)) * (x⁻¹).map (starRingEnd ℂ) = M := by
  rw [← conjT_mul, Matrix.mul_nonsing_inv _ hx.isUnit, conjT_one]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem map_Gm_isHermitian {r : ℕ} (X : Data E r) (τ : E →+* ℂ) : (X.Gm.map τ).IsHermitian := by
  ext a b
  rw [Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.map_apply, ← X.Gm_herm b a]
  exact (IsCMField.complexEmbedding_complexConj E τ _).symm

theorem gram_isHermitian {r : ℕ} (X : Data E r) (τ : E →+* ℂ) (m : Matrix (Fin r) (Fin r) ℂ) :
    (gram τ X.Gm m).IsHermitian := by
  rw [FrameDegreeData.gram_eq]
  exact conjT_isHermitian (map_Gm_isHermitian X τ) m

theorem gram_zero_zero {n : ℕ} (X : Data E (n + 1)) {x : Frame X.Ψ (n + 1)} (hx : x ∈ X.dom) (τ : X.Ψ)
    (h1 : ∀ i, ‖dmin X.Gm x τ i‖ = 1) : gram τ.1 X.Gm (mat x τ) 0 0 = (psgn X.p0 1 : ℂ) := by
  let i : Fin (n + 1 + 1) := ⟨1, by omega⟩
  have e : dmin X.Gm x τ i = gram τ.1 X.Gm (mat x τ) 0 0 := by
    unfold dmin lminor
    exact Matrix.det_fin_one _
  have hp := (hx τ).2 i
  have hn := h1 i
  rw [e] at hp hn
  have hr : (((gram τ.1 X.Gm (mat x τ) 0 0).re : ℝ) : ℂ) = gram τ.1 X.Gm (mat x τ) 0 0 :=
    (gram_isHermitian X τ.1 _).coe_re_apply_self 0
  rw [← hr, Complex.norm_real, Real.norm_eq_abs] at hn
  rw [← hr]
  congr 1
  have ha := GlobalTheory.PeterssonCompare.abs_psgn X.p0 1
  change 0 < psgn X.p0 1 * _ at hp
  rcases (abs_eq zero_le_one).1 ha with h | h <;> rcases (abs_eq zero_le_one).1 hn with h' | h' <;>
    rw [h, h'] at hp <;> first | exact h'.trans h.symm | norm_num at hp

theorem rigid : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Comp : Type) (X : Comp → Data E r) (G : Type) [Group G] (Gi : Subgroup G) (dict : G → Σ k, Frame (X k).Ψ r) (ar : ∀ k, G → (X k).Ψ → Matrix (Fin r) (Fin r) ℂ) (J : ∀ k, (X k).Ψ → Matrix (Fin r) (Fin r) ℂ) (x0 : ∀ k, Frame (X k).Ψ r), (∀ k τ, (J k τ).IsHermitian ∧ (J k τ).det ≠ 0) → (∀ k (u : (X k).Ψ → Matrix (Fin r) (Fin r) ℂ), (∀ τ, (u τ)ᵀ * J k τ * (u τ).map (starRingEnd ℂ) = J k τ) → ∃ h ∈ Gi, ∀ τ, ar k h τ = u τ) → (∀ k, x0 k ∈ (X k).dom ∧ ∃ g, dict g = ⟨k, x0 k⟩) → (∀ g, ∀ h ∈ Gi, ∃ γ ∈ (X (dict g).1).Γ, dict (g * h) = ⟨(dict g).1, lact γ (rmul (dict g).2 fun τ => ((mat (x0 (dict g).1) τ)⁻¹ * ar (dict g).1 h τ * mat (x0 (dict g).1) τ : Matrix (Fin r) (Fin r) ℂ))⟩) → (∀ g, (dict g).2 ∈ (X (dict g).1).dom) → (∀ g τ i, ‖dmin (X (dict g).1).Gm (dict g).2 τ i‖ = 1) → (∀ k (τ : (X k).Ψ), ∃ t : ℝ, t ≠ 0 ∧ (X k).Gm.map τ.1 = (t : ℂ) • J k τ) ∧ ∀ g τ, gram τ.1 (X (dict g).1).Gm (mat (dict g).2 τ) = gram τ.1 (X (dict g).1).Gm (mat (x0 (dict g).1) τ) := by
  intro E _ _ _ r Comp X G _ Gi dict ar J x0 hJ hsurj hx0 hmul hdom hunit
  classical
  cases r with
  | zero => exact ⟨fun k τ => ⟨1, one_ne_zero, Subsingleton.elim _ _⟩, fun g τ => Subsingleton.elim _ _⟩
  | succ n =>
  have he : ∀ p : ℕ, (psgn p 1 : ℂ) ≠ 0 := by
    intro p h
    have ha := GlobalTheory.PeterssonCompare.abs_psgn p 1
    rw [Complex.ofReal_eq_zero.1 h] at ha
    norm_num at ha
  have h00 : ∀ g k x, dict g = ⟨k, x⟩ → ∀ τ : (X k).Ψ,
      gram τ.1 (X k).Gm (mat x τ) 0 0 = (psgn (X k).p0 1 : ℂ) := by
    intro g k x h τ
    have h1 := hdom g
    have h2 := hunit g
    rw [h] at h1 h2
    exact gram_zero_zero (X k) h1 τ (h2 τ)
  have key : ∀ g k x, dict g = ⟨k, x⟩ → ∀ τ : (X k).Ψ, ∃ t : ℝ, t ≠ 0 ∧
      gram τ.1 (X k).Gm (mat x τ) =
        (t : ℂ) • ((mat (x0 k) τ)ᵀ * J k τ * (mat (x0 k) τ).map (starRingEnd ℂ)) := by
    intro g k x h τ
    have hd : (mat (x0 k) τ).det ≠ 0 := ((hx0 k).1 τ).1
    refine GlobalTheory.hermitian_eq_smul_of_const_on_unitary_orbit _ _ _ 0 _ (he (X k).p0) (gram_isHermitian _ _ _) (conjT_isHermitian (hJ k τ).1 _)
      (det_conjT (hJ k τ).2 hd) fun u hu => ?_
    obtain ⟨a, ha, har⟩ := hsurj k (Function.update (fun _ => 1) τ (mat (x0 k) τ * u * (mat (x0 k) τ)⁻¹)) (by
      intro σ
      by_cases hσ : σ = τ
      · subst hσ
        rw [Function.update_self, conjT_mul, conjT_mul, hu, conjT_cancel hd]
      · rw [Function.update_of_ne hσ, conjT_one])
    have hm := hmul g a ha
    rw [h] at hm
    obtain ⟨γ, hγ, hm⟩ := hm
    have h1 := h00 _ _ _ hm τ
    rw [MajInv.gram_lact _ ((X k).Γ_stab γ hγ)] at h1
    have e : mat (rmul x fun τ => ((mat (x0 k) τ)⁻¹ * ar k a τ * mat (x0 k) τ :
        Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) τ = mat x τ * u := by
      show mat x τ * ((mat (x0 k) τ)⁻¹ * ar k a τ * mat (x0 k) τ) = _
      rw [har, Function.update_self, Matrix.mul_assoc (mat (x0 k) τ), Matrix.nonsing_inv_mul_cancel_left _ _ hd.isUnit,
        Matrix.nonsing_inv_mul_cancel_right _ _ hd.isUnit]
    dsimp only at h1
    rw [e, FrameDegreeData.gram_mul] at h1
    exact h1
  refine ⟨fun k τ => ?_, fun g τ => ?_⟩
  · obtain ⟨g, hg⟩ := (hx0 k).2
    obtain ⟨t, ht, h⟩ := key g k _ hg τ
    refine ⟨t, ht, ?_⟩
    have hd : (mat (x0 k) τ).det ≠ 0 := ((hx0 k).1 τ).1
    rw [← conjT_cancel hd ((X k).Gm.map τ.1), ← FrameDegreeData.gram_eq, h, Matrix.mul_smul, Matrix.smul_mul, conjT_cancel hd]
  · obtain ⟨g', hg'⟩ := (hx0 (dict g).1).2
    obtain ⟨t, -, h⟩ := key g _ _ rfl τ
    obtain ⟨t', -, h'⟩ := key g' _ _ hg' τ
    have a := h00 g _ _ rfl τ
    have a' := h00 g' _ _ hg' τ
    rw [h, Matrix.smul_apply, smul_eq_mul] at a
    rw [h', Matrix.smul_apply, smul_eq_mul] at a'
    have hb : ((mat (x0 (dict g).1) τ)ᵀ * J _ τ * (mat (x0 (dict g).1) τ).map (starRingEnd ℂ)) 0 0 ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at a
      exact he _ a.symm
    rw [h, h', mul_right_cancel₀ hb (a.trans a'.symm)]

end GlobalTheory.PeterssonRigid
end

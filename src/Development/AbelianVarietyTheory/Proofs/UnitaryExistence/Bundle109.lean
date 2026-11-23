module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionFractionalIdealDivisibleEqZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle023
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle086
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle082
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle093
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle083
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle043
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle041
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle035
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle048
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle052
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle026
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle046
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle106
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle047
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CyclotomicCharacterEqCmMultiplierNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFramedPointMoveUniversalTriple
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle107
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem onto_dom_nonempty {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) : ∃ x, x ∈ X.dom := by
  choose P hP hg using X.signature
  have hs : ∀ a : ℕ, sgn X.p0 a ≠ 0 := fun a => by unfold sgn; split_ifs <;> norm_num
  refine ⟨fun τ => P τ, fun τ => ⟨hP τ, fun i => ?_⟩⟩
  have e : dmin X.Gm (fun τ => P τ) τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
    unfold dmin lminor
    rw [show gram τ.1 X.Gm (mat (fun τ => P τ) τ) = gram τ.1 X.Gm (P τ) from rfl, hg τ,
      Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
    unfold psgn
    push_cast
    exact Fin.prod_univ_eq_prod_range (fun a => ((sgn X.p0 a : ℝ) : ℂ)) (i : ℕ)
  rw [e, Complex.ofReal_re]
  have h0 : psgn X.p0 i ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hs a
  exact mul_self_pos.2 h0

theorem onto_adelic_of_tower (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (L Λ : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) (hLs : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (hΛ : Λ.FG) (hΛs : Submodule.span E (Λ : Set (Fin n → E)) = ⊤)
    {A B : Type} [AddCommGroup A] [Module (𝓞 E) A] [AddCommGroup B] [Module (𝓞 E) B]
    (ι : A ≃ₗ[𝓞 E] L) (φ : B ≃ₗ[𝓞 E] Λ) (EA : A → A → ℤ) (EB : B → B → ℤ) (f : ℕ → A →ₗ[𝓞 E] B)
    (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (ξ : E) (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (hJ : ∀ z : E, z ∈ J ↔ ∀ a : 𝓞 E, ∃ m : ℤ, Algebra.trace ℚ E (ξ * (a * z)) = m)
    (hA : ∀ x y, Algebra.trace ℚ E (ξ * ∑ a, ∑ b, (ι x : Fin n → E) a * G a b * c ((ι y : Fin n → E) b)) =
      -(EA x y : ℚ))
    (hB : ∀ x y, Algebra.trace ℚ E (ξ * ∑ a, ∑ b, (φ x : Fin n → E) a * G a b * c ((φ y : Fin n → E) b)) =
      -(EB x y : ℚ))
    (h1 : ∀ N m : ℕ, 0 < N → 0 < m → ∀ a, ∃ e, f (N * m) a = f N a + N • e)
    (h2 : ∀ N : ℕ, 0 < N → (∀ a, (∃ e, f N a = N • e) ↔ ∃ e, a = N • e) ∧ ∀ a', ∃ a e, a' = f N a + N • e)
    (h3 : ∀ N : ℕ, 0 < N → ∀ a a', (N : ℤ) ∣ EB (f N a) (f N a') - EA a a') :
    ∃ g : GL (Fin n) (GlobalTheory.AdLat.RA F E),
      (g : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E)).mulVec '' (GlobalTheory.AdLat.hat F (L : Set (Fin n → E))) =
        GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)) ∧
      (∀ N : ℕ, 0 < N → ∀ a : A, ∃ w ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)),
        (g : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E)) *ᵥ GlobalTheory.AdLat.fv F (ι a : Fin n → E) =
          GlobalTheory.AdLat.fv F (φ (f N a) : Fin n → E) + N • w) ∧
      ∀ x y, GlobalTheory.AdLat.hermA c G ((g : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E)) *ᵥ x)
        ((g : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E)) *ᵥ y) = GlobalTheory.AdLat.hermA c G x y := by
  let f' : ℕ → (L →ₗ[𝓞 E] Λ) := fun N => φ.toLinearMap ∘ₗ f N ∘ₗ ι.symm.toLinearMap
  have hf' : ∀ N a, f' N (ι a) = φ (f N a) := fun N a => by simp [f']
  have hlin : ∀ (s : 𝓞 E) (x y : Fin n → E), (s : E) * ∑ a, ∑ b, x a * G a b * c (y b) =
      ∑ a, ∑ b, (s • x) a * G a b * c (y b) := by
    intro s x y
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    change _ = ((s : E) * x a) * _ * _
    ring
  obtain ⟨g, hg1, hg2, hg3⟩ := GlobalTheory.AdLat.exists_adelic_matrix_of_tower F E n L Λ f' hL hLs hΛ hΛs
    (fun N m hN hm a => by
      obtain ⟨a, rfl⟩ := ι.surjective a
      obtain ⟨e, he⟩ := h1 N m hN hm a
      exact ⟨φ e, by rw [hf', hf', he, map_add (f := _), map_nsmul]⟩)
    (fun N hN => ⟨fun a => by
      obtain ⟨a, rfl⟩ := ι.surjective a
      rw [hf']
      constructor
      · rintro ⟨v, hv⟩
        obtain ⟨e, he⟩ := ((h2 N hN).1 a).1 ⟨φ.symm v, by rw [← map_nsmul, ← hv, LinearEquiv.symm_apply_apply]⟩
        exact ⟨ι e, by rw [he, map_nsmul]⟩
      · rintro ⟨v, hv⟩
        obtain ⟨e, he⟩ := ((h2 N hN).1 a).2 ⟨ι.symm v, by rw [← map_nsmul, ← hv, LinearEquiv.symm_apply_apply]⟩
        exact ⟨φ e, by rw [he, map_nsmul]⟩, fun a' => by
      obtain ⟨a', rfl⟩ := φ.surjective a'
      obtain ⟨a, e, he⟩ := (h2 N hN).2 a'
      exact ⟨ι a, φ e, by rw [hf', he, map_add (f := _), map_nsmul]⟩⟩)
  refine ⟨g, hg1, fun N hN a => by rw [← hf']; exact hg2 N hN (ι a), hg3 c G J ?_ ?_⟩
  · intro x hx y hy
    obtain ⟨x', hx'⟩ := φ.surjective ⟨x, hx⟩
    obtain ⟨y', hy'⟩ := φ.surjective ⟨y, hy⟩
    rw [hJ]
    intro s
    refine ⟨-EB (s • x') y', ?_⟩
    rw [hlin, Int.cast_neg, ← hB, map_smul, hx', hy']
    rfl
  · intro N hN x y
    obtain ⟨x, rfl⟩ := ι.surjective x
    obtain ⟨y, rfl⟩ := ι.surjective y
    have hN0 : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    have hNq : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    rw [hf', hf']
    refine ⟨(N : E)⁻¹ * ((∑ a, ∑ b, (φ (f N x) : Fin n → E) a * G a b * c ((φ (f N y) : Fin n → E) b)) -
      ∑ a, ∑ b, (ι x : Fin n → E) a * G a b * c ((ι y : Fin n → E) b)), ?_, ?_⟩
    · rw [hJ]
      intro s
      obtain ⟨m, hm⟩ := h3 N hN (s • x) y
      refine ⟨-m, ?_⟩
      have e1 := hA (s • x) y
      have e2 := hB (f N (s • x)) (f N y)
      rw [map_smul, Submodule.coe_smul, ← hlin] at e1
      rw [show (φ (f N (s • x)) : Fin n → E) = s • (φ (f N x) : Fin n → E) by
        rw [map_smul, map_smul, Submodule.coe_smul], ← hlin] at e2
      have hm' : (EB (f N (s • x)) (f N y) : ℚ) - EA (s • x) y = N * m := by exact_mod_cast hm
      generalize (∑ a, ∑ b, (φ (f N x) : Fin n → E) a * G a b * c ((φ (f N y) : Fin n → E) b)) = u at e2 ⊢
      generalize (∑ a, ∑ b, (ι x : Fin n → E) a * G a b * c ((ι y : Fin n → E) b)) = v at e1 ⊢
      have e3 : ξ * ((s : E) * ((N : E)⁻¹ * (u - v))) = (N : ℚ)⁻¹ • (ξ * (s * u) - ξ * (s * v)) := by
        rw [Algebra.smul_def, map_inv₀, map_natCast]; ring
      rw [e3, map_smul, map_sub, e1, e2, smul_eq_mul]
      push_cast
      field_simp
      linear_combination -hm'
    · rw [nsmul_eq_mul, mul_inv_cancel_left₀ hN0, add_sub_cancel]

theorem onto_marking_sub (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n N : ℕ}
    {u v e : Fin n → E} {z w : Fin n → GlobalTheory.AdLat.RA F E} (h : u = v + N • e)
    (hz : z = GlobalTheory.AdLat.fv F u + N • w) : GlobalTheory.AdLat.fv F v - z = N • -(GlobalTheory.AdLat.fv F e + w) := by
  rw [hz, h, GlobalTheory.AdLat.cap_fv_add, GlobalTheory.AdLat.cap_fv_nsmul, smul_neg, smul_add]
  abel

theorem exists_finite_mark : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ k, ∃ h ∈ GfC V, C.Mark h k 1 := by
  intro D H Dw l Xo c σ V r C hC k
  obtain rfl : V.rank = r := C.hr
  have hneg := (GlobalTheory.T.exists_memberDictionaryContext_goodEmbedding D H Dw l Xo c σ V _ rfl C.ι hC.iota hC.pos hC.lA hC.good).2.1 C hC
  obtain ⟨Pf, -, -, hPf, -⟩ := GlobalTheory.exists_framePeriods D.host.E H Dw l Xo c σ C.g C.e C.F _ C.M hC.good hC.base hneg k
  obtain ⟨x, hx⟩ := onto_dom_nonempty (C.M.X k)
  obtain ⟨f, h1, h2, h3, h4⟩ := GlobalTheory.familyUnif_lattice_genus D.host.E H Dw l Xo _ C.g _ C.F k (Pf x) (hPf x hx)
  obtain ⟨-, hfv, -, -, -, hcc, -, -, -, hT, -⟩ := GlobalTheory.T.completedLattice_eq_adelicCompletion_and_gram D V
  obtain ⟨hL, hLs, -⟩ := GlobalTheory.T.adelicElementLattice_full_and_completion D V 1
  let ι : Dw.La ≃ₗ[𝓞 D.host.E] latG V 1 :=
    (LinearEquiv.ofInjective C.ι hC.iota.emb.1).trans (LinearEquiv.ofEq _ _ hC.iota.emb.2)
  have hι : ∀ a, (ι a : Fin V.rank → D.host.E) = C.ι a := fun a => rfl
  have hherm : ∀ x y : Fin V.rank → D.host.E, (∑ a, ∑ b, x a * V.gramᵀ a b * cF D (y b)) = -herm (-V.gramᵀ) x y := by
    intro x y
    simp only [herm, hcc, Matrix.neg_apply, mul_neg, neg_mul, Finset.sum_neg_distrib, neg_neg]
  have hGm : (C.M.X k).Gm = -V.gramᵀ := (hC.modelW k).1
  have hxi : (C.M.X k).ξ0 = -D.host.xi0 := (hC.modelW k).2
  obtain ⟨g, hg1, hg2, hg3⟩ := onto_adelic_of_tower D.host.F D.host.E V.rank (latG V 1) (C.M.X k).Λ hL hLs
    (C.M.X k).Λ_fg (C.M.X k).Λ_span ι (C.M.φ k) (fun a b => Dw.EF a b) (fun a b => (C.F.Di k).EF a b) f
    (cF D) V.gramᵀ D.host.xi0 _ (GlobalTheory.T.adelicUnitaryLattice_selfDual_traceForm D V 1 _ rfl).1
    (fun x y => by
      have halt : Dw.EF y x = -Dw.EF x y := by
        have := Dw.alt (x + y)
        simp only [map_add (f := _), LinearMap.add_apply, Dw.alt] at this
        linear_combination this
      rw [hherm, hι, hι, ← hT, ← hC.iota.isom, halt, Int.cast_neg])
    (fun x y => by
      rw [hherm, hC.base.ef k x y, hGm, hxi, neg_neg, mul_neg, map_neg])
    h1 h2 h3
  obtain ⟨h, hh, rfl⟩ := (GlobalTheory.T.adelicUnitary_eq_real_mul_finite_split D V).2.2.2.1 g hg3
  obtain ⟨-, -, hlat, hhat, -⟩ := GlobalTheory.T.adelicElementLattice_full_and_completion D V h
  have hcap := (GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E V.rank (C.M.X k).Λ (C.M.X k).Λ_fg
    (C.M.X k).Λ_span).1
  rw [hg1] at hhat
  refine ⟨h, hh, one_mem _, ?_, fun a ha => ?_⟩
  · rw [one_mul, hlat]
    ext v
    rw [SetLike.mem_coe, ← hcap, ← SetLike.mem_coe, ← hg1]
    constructor
    · intro hv
      exact ⟨v, hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact hv
  · rw [one_mul]
    obtain ⟨e, he⟩ := h4 a ha
    obtain ⟨w, hw, hw'⟩ := hg2 l.M (lt_of_lt_of_le (by norm_num) l.three_le) a
    refine ⟨-(GlobalTheory.AdLat.fv D.host.F (C.M.φ k e : Fin V.rank → D.host.E) + w), ?_, ?_⟩
    · have h0 := (hcap _).2 (C.M.φ k e).2
      have h5 := AddSubgroup.neg_mem _ (AddSubgroup.add_mem _ h0 hw)
      rw [← SetLike.mem_coe, ← hhat] at h5
      exact h5
    · rw [hfv, hfv, ← hι]
      change GlobalTheory.AdLat.fv D.host.F (C.M.φ k (C.F.t k a) : Fin V.rank → D.host.E) - _ = _
      have he' : (C.M.φ k (f l.M a) : Fin V.rank → D.host.E) =
          (C.M.φ k (C.F.t k a) : Fin V.rank → D.host.E) + l.M • (C.M.φ k e : Fin V.rank → D.host.E) := by
        rw [he, (C.M.φ k).map_add, map_nsmul (C.M.φ k)]
        rfl
      exact onto_marking_sub D.host.F he' hw'

end GlobalTheory.Member
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

theorem _root_.GlobalTheory.T.exists_component_lattice_marking_adelic : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ h : GA D V, ∃ k γ, C.Mark h k γ := by
  first | exact @GlobalTheory.Member.exists_mark | exact GlobalTheory.Member.exists_mark | (intros; apply GlobalTheory.Member.exists_mark <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

theorem _root_.GlobalTheory.T.marking_component_unique_frame_unique_arithmeticGroup : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ h, (∀ k k' γ γ', C.Mark h k γ → C.Mark h k' γ' → k = k') ∧ ∀ k γ γ', C.Mark h k γ → C.Mark h k γ' → ∃ δ ∈ (C.M.X k).Γ, C.fr (γ' * h) k = lact δ (C.fr (γ * h) k) := by
  first | exact @GlobalTheory.MarkUniq.mark_unique | exact GlobalTheory.MarkUniq.mark_unique | (intros; apply GlobalTheory.MarkUniq.mark_unique <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameUnif

theorem wchar_ex_sign {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) {S : Type} [CommRing S] (t : Ix Dw → Sˣ) (h0 : (t none : S) ^ 2 = 1)
    (h1 : ∀ p, t (some p) = 1) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hn : Even n) : wchar (ex Dw a n) t = 1 := by
  obtain ⟨m, rfl⟩ := hn
  unfold wchar
  rw [Fintype.prod_option]
  simp only [h1, Units.val_one, one_pow, Finset.prod_const_one, mul_one]
  show (t none : S) ^ (m + m) = 1
  rw [← two_mul, pow_mul, h0, one_pow]

theorem normUn_gamma : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => _root_.Formalism.L2.PjFree.relab c σ (e j).1)) (r : ℕ) (M : _root_.GlobalTheory.FrameUnif.ModelsOf F r) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)) (k : Fin F.n) (T : ThetaData e F M k), _root_.Formalism.L2.PjFree.GoodEmb c σ → ModelBase M → NegXi M → IsNormUn T (un k) → ∀ γ ∈ (M.X k).Γ, ∀ (x : (M.X k).dom) (h : lact γ x.1 ∈ (M.X k).dom), ∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (un k x) (un k ⟨_, h⟩) ∧ ∀ a n, Dom a n → _root_.Formalism.L2.PjFree.toC (wchar (ex Dw a n) t) = 1 := by
  intro hS E _ _ _ H Dw l Xo c σ g e F r M un k T hσ hM hN hun γ hγ x h
  obtain ⟨gam, hgam, hP⟩ := GlobalTheory.per_gam E H Dw l Xo c σ g e F r M hσ hM hN k T.Pf T.per γ hγ
  obtain ⟨κ, hκ, hy⟩ := hun x
  obtain ⟨κ', hκ', hy'⟩ := hun ⟨_, h⟩
  have hb : T.co.symm x.1 ∈ T.co ⁻¹' (M.X k).dom := by
    show T.co (T.co.symm x.1) ∈ (M.X k).dom
    rw [T.co.apply_symm_apply]; exact x.2
  have hb' : T.co.symm (lact γ x.1) ∈ T.co ⁻¹' (M.X k).dom := by
    show T.co (T.co.symm (lact γ x.1)) ∈ (M.X k).dom
    rw [T.co.apply_symm_apply]; exact h
  obtain ⟨hx, hd, t₀, hsec, ht⟩ := GlobalTheory.T.thetaPoints_change_levelIsometry_linearMap hS E H Dw l Xo c σ g e F r M k T _ hb _ hb' κ κ' (un k x)
    (un k ⟨_, h⟩) gam 1 hy hy' hgam (fun a => by
      rw [T.co.apply_symm_apply, T.co.apply_symm_apply, Matrix.one_mulVec]; exact hP x.1 x.2 a)
  have hu : ∀ τ i, (un k ⟨_, h⟩).u τ i = (un k x).u τ i := fun τ i => by
    have h1 := hd τ i
    rw [inv_one, Matrix.one_mulVec] at h1
    exact ((GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F k _ (T.isPer _ hb)).2.1 _).unique h1 (hy.2.1 τ i)
  have hC : (normConst (fun j => _root_.Formalism.L2.PjFree.relab c σ (e j).1) (M.X k).ξ0 : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    refine (Real.sqrt_pos.2 (div_pos (by positivity) (Finset.prod_pos fun j _ => ?_))).ne'
    have : _root_.Formalism.L2.PjFree.relab c σ (e j).1 (M.X k).ξ0 ≠ 0 := (map_ne_zero _).2 (M.X k).ξ0_ne
    positivity
  have ht2 : _root_.Formalism.L2.PjFree.toC (t₀ : CAt σ) ^ 2 = 1 := by
    have d1 := (T.norm _ hb).1.ne_zero
    have d2 := (T.norm _ hb').1.ne_zero
    rw [hκ, hκ', Matrix.det_one, mul_one] at ht
    refine mul_right_cancel₀ (mul_ne_zero (mul_ne_zero hC d1) d2) ?_
    rw [ht]; ring
  refine ⟨fun i => i.elim t₀ fun _ => 1, ?_, fun a n hn => ?_⟩
  · refine (frBor_iff_frChg _ _ _).2 ⟨fun _ => 1, fun τ i j hij => Matrix.one_apply_ne hij.ne,
      fun τ i => Matrix.one_apply_eq i, hx, fun τ i => ?_, hsec⟩
    rw [hu]
    exact (GlobalTheory.T.frameChangeByMatrices_refl_and_comp E H Dw l Xo c (CAt σ) (un k x) (un k x) (un k x)).1.2.1 τ i
  · exact wchar_ex_sign Dw _ ht2 (fun _ => rfl) a n hn.2

end GlobalTheory.FrameUnif
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.NormUnBor

theorem diag_ne_zero {T : Type} {m : T → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : T, Fin (m τ))
    (A : Matrix (Fin g) (Fin g) ℂ) (hA : A.det ≠ 0)
    (htri : ∀ j j', A j j' ≠ 0 → (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2) (j : Fin g) : A j j ≠ 0 := by
  have hdet : A.det = ∏ i, A i i := by
    rw [Matrix.det_apply, Finset.sum_eq_single (1 : Equiv.Perm (Fin g))]
    · simp
    · intro s _ hs
      by_contra hne
      have hp : ∏ i, A (s i) i ≠ 0 := fun h0 => hne (by rw [h0, smul_zero])
      have hall : ∀ i, A (s i) i ≠ 0 := fun i => Finset.prod_ne_zero_iff.1 hp i (Finset.mem_univ i)
      have hsum : ∑ i, ((e (s i)).2 : ℕ) = ∑ i, ((e i).2 : ℕ) :=
        Equiv.sum_comp s (fun i => ((e i).2 : ℕ))
      have heq := (Finset.sum_eq_sum_iff_of_le (fun i _ => (htri _ _ (hall i)).2)).1 hsum
      apply hs
      ext i
      have h1 := (htri _ _ (hall i)).1
      have h2 := heq i (Finset.mem_univ i)
      have : e (s i) = e i := Sigma.ext h1 ((Fin.heq_ext_iff (by rw [h1])).2 h2)
      simp [e.injective this]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hdet] at hA
  exact Finset.prod_ne_zero_iff.1 hA j (Finset.mem_univ j)

theorem col_eq_sum {T : Type} {m : T → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : T, Fin (m τ))
    (A : Matrix (Fin g) (Fin g) ℂ)
    (htri : ∀ j j', A j j' ≠ 0 → (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2) (τ : T) (i : Fin (m τ)) :
    ∑ i' : Fin (m τ), A (e.symm ⟨τ, i'⟩) (e.symm ⟨τ, i⟩) • (Pi.single (e.symm ⟨τ, i'⟩) (1 : ℂ) : Fin g → ℂ) =
      A *ᵥ Pi.single (e.symm ⟨τ, i⟩) 1 := by
  funext p
  obtain ⟨⟨τ', i'⟩, rfl⟩ := e.symm.surjective p
  rw [Matrix.mulVec_single_one, Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.col_apply]
  by_cases hτ : τ' = τ
  · subst hτ
    rw [Finset.sum_eq_single i']
    · simp
    · intro j _ hj
      rw [Pi.single_eq_of_ne, mul_zero]
      intro h
      exact hj (sigma_mk_injective (β := fun τ => Fin (m τ)) (e.symm.injective h)).symm
    · intro h; exact absurd (Finset.mem_univ _) h
  · have h0 : A (e.symm ⟨τ', i'⟩) (e.symm ⟨τ, i⟩) = 0 := by
      by_contra hne
      have := (htri _ _ hne).1
      rw [e.apply_symm_apply, e.apply_symm_apply] at this
      exact hτ this
    rw [h0]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Pi.single_eq_of_ne, mul_zero]
    intro h
    exact hτ (congrArg Sigma.fst (e.symm.injective h))

theorem normConst_ne_zero {E : Type} [Field E] {g : ℕ} (ty : Fin g → (E →+* ℂ)) {ξ₀ : E} (h : ξ₀ ≠ 0) :
    (normConst ty ξ₀ : ℂ) ≠ 0 := by
  refine Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (div_pos (by positivity) ?_)).ne'
  exact Finset.prod_pos fun j _ => mul_pos two_pos (norm_pos_iff.2 ((map_ne_zero _).2 h))

theorem normUn_bor : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => _root_.Formalism.L2.PjFree.relab c σ (e j).1)) (r : ℕ) (M : _root_.GlobalTheory.FrameUnif.ModelsOf F r) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)) (k : Fin F.n) (T : ThetaData e F M k), _root_.Formalism.L2.PjFree.GoodEmb c σ → ModelBase M → NegXi M → IsNormUn T (un k) → ∀ (x : (M.X k).dom) b (_hb : b ∈ Bor (M.X k).Ψ r) (h : rmul x.1 b ∈ (M.X k).dom), ∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (un k x) (un k ⟨_, h⟩) ∧ ∀ a n, Dom a n → _root_.Formalism.L2.PjFree.toC (wchar (ex Dw a n) t) = bchar (laU (unfOf e F M un) a n k) b := by
  intro hS E _ _ _ H Dw l Xo c σ g e F r M un k T hG hB hN hU x b hb h
  obtain ⟨h₀, hdet, hP, htri, -, -, hw⟩ :=
    GlobalTheory.T.triangularFrame_moves_period_blockTriangular E H Dw l Xo c σ g e F r M hG hB hN k T.Pf T.per x.1 x.2 b hb
  obtain ⟨κ, hκ, hy⟩ := hU x
  obtain ⟨κ', hκ', hy'⟩ := hU ⟨_, h⟩
  have hx : T.co.symm x.1 ∈ T.co ⁻¹' (M.X k).dom := by
    simpa only [Set.mem_preimage, ContinuousLinearEquiv.apply_symm_apply] using x.2
  have hx' : T.co.symm (rmul x.1 b) ∈ T.co ⁻¹' (M.X k).dom := by
    simpa only [Set.mem_preimage, ContinuousLinearEquiv.apply_symm_apply] using h
  obtain ⟨hxx, hder, t₀, hsec, ht₀⟩ := GlobalTheory.T.thetaPoints_change_levelIsometry_linearMap hS E H Dw l Xo c σ g e F r M k T _ hx _ hx' κ κ' _ _
    (LinearEquiv.refl _ _) h₀ hy hy'
    ⟨fun _ _ => rfl, fun a _ => ⟨0, by simp⟩, fun a => ⟨0, by simp⟩⟩
    (fun a => by
      simp only [ContinuousLinearEquiv.apply_symm_apply, LinearEquiv.refl_apply]
      exact hP a)
  have hsq : _root_.Formalism.L2.PjFree.toC (t₀ : CAt σ) ^ 2 * h₀.det = 1 := by
    have hc := normConst_ne_zero (fun j => _root_.Formalism.L2.PjFree.relab c σ (e j).1) (M.X k).ξ0_ne
    have h1 := (T.norm _ hx).1.ne_zero
    have h2 := (T.norm _ hx').1.ne_zero
    rw [hκ, hκ'] at ht₀
    apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hc h1) h2)
    linear_combination ht₀
  have hinv : (h₀⁻¹).det ≠ 0 := (Matrix.isUnit_nonsing_inv_det h₀ hdet).ne_zero
  have hdiag := diag_ne_zero e h₀⁻¹ hinv htri
  let d : Fin g → (CAt σ)ˣ := fun j => (Units.mk0 (h₀⁻¹ j j) (hdiag j) : ℂˣ)
  let t : Ix Dw → (CAt σ)ˣ := fun o => Option.elim o t₀ (fun p => d (e.symm p))
  refine ⟨t, ⟨hxx, fun τ i => ⟨fun i' => (h₀⁻¹ (e.symm ⟨τ, i'⟩) (e.symm ⟨τ, i⟩) : ℂ), rfl, ?_, ?_⟩, ?_⟩, ?_⟩
  · intro j hj
    by_contra hne
    have := (htri _ _ hne).2
    rw [e.apply_symm_apply, e.apply_symm_apply] at this
    exact absurd hj (not_lt.2 this)
  · rw [hy.1]
    refine (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F k _ (T.isPer _ hx) _ _ _ (hy.2.1 τ) _ _).2 ?_
    rw [col_eq_sum e h₀⁻¹ htri]
    exact hder τ i
  · obtain ⟨pm, h1, h2, h3⟩ := hsec
    refine ⟨pm, h1, ?_, h3⟩
    rw [h2]
    simp [spMap]
  · intro a n hD
    rw [← hw un a n (_root_.Formalism.L2.PjFree.toC (t₀ : CAt σ)) hD.2 hsq]
    show (∏ o : Ix Dw, _root_.Formalism.L2.PjFree.toC ((t o : (CAt σ)ˣ) : CAt σ) ^ ex Dw a n o) = _
    rw [Fintype.prod_option, mul_comm]
    congr 1
    rw [← Equiv.prod_comp e]
    refine Finset.prod_congr rfl fun j _ => ?_
    show h₀⁻¹ (e.symm (e j)) (e.symm (e j)) ^ a ((e j).1, (e j).2) = _
    rw [e.symm_apply_apply]

end GlobalTheory.NormUnBor
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_cmCurve_hom_of_pureType_vector_anyLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ C : Curve H, ∀ (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P), ∀ (ε : ℤˣ), ∀ a ∈ lat hP (((ε : ℤ) : ℂ) * H.rt0), ∃ φ : C.P.A.left ⟶ Xo.univ.t.G.left, φ ≫ Xo.univ.t.G.hom = C.P.A.hom ≫ F.u i P ∧ ∀ z : ℂ, C.pt z ≫ φ = (F.ex i P (z • P a)).left := by
  first | exact @GlobalTheory.CompRat.exists_hom_of_pureType_of_level | exact GlobalTheory.CompRat.exists_hom_of_pureType_of_level | (intros; apply GlobalTheory.CompRat.exists_hom_of_pureType_of_level <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_cmCurve_hom_of_pureType_vector : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → ∀ C : Curve H, ∀ (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P), ∀ (ε : ℤˣ), ∀ a ∈ lat hP (((ε : ℤ) : ℂ) * H.rt0), ∃ φ : C.P.A.left ⟶ Xo.univ.t.G.left, φ ≫ Xo.univ.t.G.hom = C.P.A.hom ≫ F.u i P ∧ ∀ z : ℂ, C.pt z ≫ φ = (F.ex i P (z • P a)).left := by
  first | exact @GlobalTheory.CompRat.exists_hom_of_pureType | exact GlobalTheory.CompRat.exists_hom_of_pureType | (intros; apply GlobalTheory.CompRat.exists_hom_of_pureType <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.cyclotomicCharacter_eq_cmMultiplier_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (C : Curve H), ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∀ (io : C.P.A.left ⟶ C.P.A.left) (n : ℕ) (s : ℤ × ℤ), 0 < n → C.ActsBy τ io n s → τ (zeta n) = zeta n ^ (s.1 ^ 2 + s.1 * s.2 + s.2 ^ 2 * (((H.d : ℤ) + 1) / 4)) := by
  first | exact @GlobalTheory.MultiplierNorm.map_zeta_eq_zpow_norm | exact GlobalTheory.MultiplierNorm.map_zeta_eq_zpow_norm | (intros; apply GlobalTheory.MultiplierNorm.map_zeta_eq_zpow_norm <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

theorem _root_.GlobalTheory.T.existsUnique_framedPoint_move_universalTriple : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ), ρ ≫ Xo.s = Xo.s → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), (∃ y' : FrPt Xo c S, FrMove ρ ν y y') ∧ ∀ y' y'' : FrPt Xo c S, ∀ ν' : SABMap Xo.univ.t Xo.univ.t ρ, ν'.φ = ν.φ → FrMove ρ ν y y' → FrMove ρ ν' y y'' → y' = y'' := by
  first | exact @GlobalTheory.exists_unique_frMove | exact GlobalTheory.exists_unique_frMove | (intros; apply GlobalTheory.exists_unique_frMove <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

theorem _root_.GlobalTheory.T.levelMove_moduli_unique_universalTriple : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (ρ ρ' : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (ν' : SABMap Xo.univ.t Xo.univ.t ρ') (gM gM' gA gA' : Dw.La →ₗ[𝓞 E] Dw.La), 1 ≤ Dw.p + Dw.q → (∀ a, gM a - gM' a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → (∀ a, Dw.ModN l.A (gA a - gA' a)) → IsIso ρ → IsIso ρ' → IsLevMove ρ ν gM gA → IsLevMove ρ' ν' gM' gA' → (∃ g : Sim Dw, (∀ a, g.f l.M a - gM a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) ∧ (∀ a, Dw.ModN l.A (g.f l.A a - gA a)) ∧ (l.A : ℤ) ∣ g.ν l.A - 1) → ρ = ρ' ∧ ν.φ = ν'.φ := by
  first | exact @GlobalTheory.levMove_unique | exact GlobalTheory.levMove_unique | (intros; apply GlobalTheory.levMove_unique <;> assumption)
end

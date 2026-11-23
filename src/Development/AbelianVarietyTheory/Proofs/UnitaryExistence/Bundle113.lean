module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle082
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle060
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle111
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle037
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle109
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle095
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsConjSplitPointLatticeLinearMap
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

@[expose] public section

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem frame_rmul_lact {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {r : ℕ}
    (γ : GL (Fin r) E) (x b : Frame Ψ r) : rmul (lact γ x) b = lact γ (rmul x b) := by
  funext τ
  exact Matrix.mul_assoc (α := ℂ) _ (mat x τ) (mat b τ)

theorem dict_eq_of_mark (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r) (hC : C.OK)
    (dict : GA D V → Σ k, Frame (C.M.X k).Ψ r) (hd : C.IsDict dict) (g : GA D V) (k : Fin C.F.n)
    (γ : GA D V) (hm : C.Mark g k γ) :
    ∃ δ ∈ (C.M.X k).Γ, dict g = ⟨k, lact δ (C.fr (γ * g) k)⟩ := by
  obtain ⟨γ', hm', he⟩ := hd.1 g
  have hu := GlobalTheory.T.marking_component_unique_frame_unique_arithmeticGroup D H Dw l Xo c σ V r C hC g
  have hk : k = (dict g).1 := hu.1 _ _ _ _ hm hm'
  subst hk
  obtain ⟨δ, hδ, e⟩ := hu.2 _ _ _ hm hm'
  refine ⟨δ, hδ, ?_⟩
  rw [← e, ← he]

theorem dict_real_equivariant_onto : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ dict, C.IsDict dict → (∀ g, ∀ h ∈ GinfC V, ∃ γ' ∈ (C.M.X (dict g).1).Γ, dict (g * h) = ⟨(dict g).1, lact γ' (rmul (dict g).2 (archMat V C.th C.hr (fun k => C.fr 1 k) h (dict g).1))⟩) ∧ ∀ k, ∀ x ∈ (C.M.X k).dom, ∃ g, ∃ γ ∈ (C.M.X k).Γ, ∃ b ∈ Bor (C.M.X k).Ψ r, dict g = ⟨k, rmul (lact γ x) b⟩ := by
  intro D H Dw l Xo c σ V r C hC dict hd
  refine ⟨fun g h hh => ?_, fun k x hx => ?_⟩
  · obtain ⟨γ, hm, he⟩ := hd.1 g
    have hm2 := (GlobalTheory.T.markingRule_translate_stable D H Dw l Xo c σ V r C hC g _ γ hm).2.2.1 h hh
    obtain ⟨δ, hδ, e⟩ := dict_eq_of_mark D H Dw l Xo c σ V r C hC dict hd (g * h) _ γ hm2
    refine ⟨δ, hδ, ?_⟩
    rw [e, ← mul_assoc, (GlobalTheory.T.memberDictionary_frames_orthonormal_unit D H Dw l Xo c σ V r C hC (γ * g) _).2.2.2.2.2.1 h, ← he]
  · obtain ⟨x₀, b, hb, ho, hx₀⟩ := (GlobalTheory.UnitFrames.frame_mul_triangular_orthonormal D.host.E r
      (C.M.X k).p0 (C.M.X k).Ψ (C.M.X k).Gm (C.M.X k).Gm_herm).1 x hx
    obtain ⟨u, hu, hux⟩ := (GlobalTheory.T.memberDictionary_frames_orthonormal_unit D H Dw l Xo c σ V r C hC 1 k).2.2.2.2.2.2 x₀ ho
    obtain ⟨f, hf, hm⟩ := GlobalTheory.T.exists_finiteAdelic_element_marking_component D H Dw l Xo c σ V r C hC k
    have hm2 := (GlobalTheory.T.markingRule_translate_stable D H Dw l Xo c σ V r C hC f k 1 hm).2.2.1 u hu
    obtain ⟨δ, hδ, e⟩ := dict_eq_of_mark D H Dw l Xo c σ V r C hC dict hd (f * u) k 1 hm2
    refine ⟨f * u, δ, hδ, b, hb, ?_⟩
    rw [e, one_mul, ← (GlobalTheory.T.adelicUnitary_eq_real_mul_finite_split D V).2.1 u hu f hf,
      (GlobalTheory.T.memberDictionary_frames_orthonormal_unit D H Dw l Xo c σ V r C hC u k).2.2.2.2.1 f hf, hux, hx₀, frame_rmul_lact]

end GlobalTheory.Member
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

theorem _root_.GlobalTheory.T.memberDictionary_invariant_rational_level : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ dict, C.IsDict dict → ∀ Kf : Subgroup (GA D V), IsLevelK V l.M Kf → (∀ γ ∈ GQ V, ∀ g, ∃ γ' ∈ (C.M.X (dict g).1).Γ, dict (γ * g) = ⟨(dict g).1, lact γ' (dict g).2⟩) ∧ (∀ k ∈ Kf, ∀ g, ∃ γ' ∈ (C.M.X (dict g).1).Γ, dict (g * k) = ⟨(dict g).1, lact γ' (dict g).2⟩) ∧ (∀ g, (dict g).2 ∈ (C.M.X (dict g).1).dom) ∧ (∀ g τ i, ‖dmin (C.M.X (dict g).1).Gm (dict g).2 τ i‖ = 1) ∧ ∀ g k γ, C.Mark g k γ → ∃ δ ∈ (C.M.X k).Γ, dict g = ⟨k, lact δ (C.fr (γ * g) k)⟩ := by
  first | exact @GlobalTheory.Member.dict_invariant | exact GlobalTheory.Member.dict_invariant | (intros; apply GlobalTheory.Member.dict_invariant <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
open GlobalTheory.ConjSplit hiding exists_lin exists_conj_lattice_map

namespace GlobalTheory.ConjSplitAnyLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Fam

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
  (F : FamilyUnif Xo σ ty) {i : Fin F.n} {P : (F.Di i).La →+ (Fin g → ℂ)} (hP : IsPeriod (F.Di i) ty P)

theorem exists_lin (h₁ : 1 ≤ D.p + D.q) (h₂ : σ (baseKA l).ρ = H.rt0) (h₃ : IsTypeFn H D.p D.q ty)
    (C : Curve H) (io : C.P.A.left ⟶ C.P.A.left) {i' : Fin F.n} {P' : (F.Di i').La →+ (Fin g → ℂ)}
    (hP' : IsPeriod (F.Di i') ty P') (U : Over.mk (F.u i' P') ⟶ Over.mk (F.u i P)) (f : ℂ → ℂ)
    (hadd : ∀ z w, ∃ a, f (z + w) - (f z + f w) = wC H a)
    (hw : ∀ z, ∃ a, f (wC H (0, 1) * z) - wC H (0, 1) * f z = wC H a)
    (hf : ∀ z, C.pt z ≫ io = U.left ≫ C.pt (f z)) (ε : ℤˣ) :
    ∃ Φ : lat hP (((ε : ℤ) : ℂ) * H.rt0) →ₗ[𝓞 E] (F.Di i').La,
      (∀ a, Φ a ∈ lat hP' (((ε : ℤ) : ℂ) * H.rt0)) ∧
      ∀ a (z : ℂ), F.ex i' P' (z • P' (Φ a)) = U ≫ F.ex i P (f z • P a) := by
  have key : ∀ a : lat hP (((ε : ℤ) : ℂ) * H.rt0), ∃ a' ∈ lat hP' (((ε : ℤ) : ℂ) * H.rt0),
      ∀ z : ℂ, U ≫ F.ex i P (f z • P a) = F.ex i' P' (z • P' a') := by
    rintro ⟨a, ha⟩
    obtain ⟨φ, -, hφ⟩ := GlobalTheory.T.exists_cmCurve_hom_of_pureType_vector_anyLevel E H D l Xo σ g ty F h₁ h₂ h₃ C i P hP ε a ha
    have hx : ∀ z w, F.ex i P (f (z + w) • P a) = F.ex i P (f z • P a) * F.ex i P (f w • P a) := fun z w => by
      rw [ex_congr_type F hP ε ha (hadd z w), add_smul, F.ex_add i P hP]
    refine GlobalTheory.T.cmCurveHom_exists_pureTypeVector_anyLevel E H D l Xo σ g ty F h₁ h₂ h₃ C i' P' hP' (io ≫ φ) (fun z => U ≫ F.ex i P (f z • P a)) ε
      (fun z => ?_) (fun z w => ?_) (fun z => ?_)
    · rw [← Category.assoc, hf, Category.assoc, hφ]; rfl
    · show U ≫ _ = (U ≫ _) * (U ≫ _)
      rw [hx, MonObj.comp_mul]
    · show U ≫ _ = (U ≫ _) ≫ _
      rw [Category.assoc, ← ex_smul F hP, period_w0_smul hP ha, smul_smul]
      congr 1
      have e0 : wC H (0, 1) = (1 + H.rt0) / 2 := by simp [wC]
      rw [e0] at hw
      rcases Int.units_eq_one_or ε with rfl | rfl
      · refine ex_congr_type F hP 1 ha ?_
        simpa [mul_comm] using hw z
      · have e1 := hx ((1 + -H.rt0) / 2 * z) ((1 + H.rt0) / 2 * z)
        rw [ex_congr_type F hP _ ha (hw z), ← F.ex_add i P hP, ← add_smul,
          show (1 + -H.rt0) / 2 * z + (1 + H.rt0) / 2 * z = z by ring] at e1
        have e2 := (F.ex_ker i P hP ((f ((1 + -H.rt0) / 2 * z) + (1 + H.rt0) / 2 * f z - f z) • P a)).1 (by
          have e3 := F.ex_add i P hP ((f ((1 + -H.rt0) / 2 * z) + (1 + H.rt0) / 2 * f z - f z) • P a) (f z • P a)
          rw [← add_smul, sub_add_cancel, ← e1] at e3
          exact mul_eq_right.1 e3.symm)
        refine ex_congr F hP ?_
        rw [← sub_smul]
        convert e2 using 2
        simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_mul]
        ring
  choose Φ hΦ hex using key
  refine ⟨{ toFun := Φ, map_add' := fun a b => ?_, map_smul' := fun s a => ?_ }, hΦ, fun a z => (hex a z).symm⟩
  · refine eq_of_ex F hP' fun z => ?_
    rw [map_add (f := _), smul_add, F.ex_add i' P' hP', ← hex, ← hex, ← hex, Submodule.coe_add, map_add (f := _), smul_add,
      F.ex_add i P hP, MonObj.comp_mul]
  · refine eq_of_ex F hP' fun z => ?_
    rw [RingHom.id_apply, ex_smul F hP', ← hex, ← hex, Submodule.coe_smul, ex_smul F hP, Category.assoc]

end Fam

theorem exists_conj_lattice_map : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∀ (C : Curve H) (io : C.P.A.left ⟶ C.P.A.left), IsGrpPullback C.P.A C.P.A (spMap (τ : ℂ →+* ℂ)) io → ∀ (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P), ∀ (i' : Fin F.n) (P' : (F.Di i').La →+ (Fin g → ℂ)) (hP' : IsPeriod (F.Di i') ty P'), IsSplit hP → spMap (τ : ℂ →+* ℂ) ≫ F.u i P = F.u i' P' → ∃ Φ : (F.Di i).La →ₗ[𝓞 E] (F.Di i').La, Function.Injective Φ ∧ (∀ a, Φ a ∈ lat hP' H.rt0 ↔ a ∈ lat hP H.rt0) ∧ (∀ a, Φ a ∈ lat hP' (-H.rt0) ↔ a ∈ lat hP (-H.rt0)) ∧ ∀ (n : ℕ) (s : ℤ × ℤ), 0 < n → C.ActsBy τ io n s → ∀ a ∈ lat hP H.rt0, ∀ b ∈ lat hP (-H.rt0), spMap (τ : ℂ →+* ℂ) ≫ (F.ex i P ((n : ℂ)⁻¹ • P (a + b))).left = (F.ex i' P' ((n : ℂ)⁻¹ • P' (Φ (wE H s • a + H.bar (wE H s) • b)))).left := by
  intro E _ _ _ H D l Xo σ g ty F h₁ h₂ h₃ τ hτ C io hio i P hP i' P' hP' hsp hu
  obtain ⟨f, hadd, hw, hon, hact, hf⟩ := exists_param C τ hτ io hio
  let U : Over.mk (F.u i' P') ⟶ Over.mk (F.u i P) := Over.homMk (spMap (τ : ℂ →+* ℂ)) hu
  have hU : ∀ x y : Over.mk (F.u i P) ⟶ Xo.univ.t.G, U ≫ x = U ≫ y → x = y := fun x y h =>
    Over.OverMorphism.ext (spMap_cancel τ (congrArg (fun m => m.left) h))
  have key : ∀ (ε : ℤˣ) (ρ : ℂ), ((ε : ℤ) : ℂ) * H.rt0 = ρ → ∃ Φ : lat hP ρ →ₗ[𝓞 E] (F.Di i').La,
      (∀ a, Φ a ∈ lat hP' ρ) ∧ (∀ a, Φ a = 0 → a = 0) ∧ ∀ (n : ℕ) (s : ℤ × ℤ), C.ActsBy τ io n s → ∀ a : lat hP ρ,
        U ≫ F.ex i P ((n : ℂ)⁻¹ • P a) = F.ex i' P' ((n : ℂ)⁻¹ • wC H s • P' (Φ a)) := by
    rintro ε _ rfl
    obtain ⟨Φ, hΦ, hex⟩ := exists_lin F hP h₁ h₂ h₃ C io hP' U f hadd hw hf ε
    refine ⟨Φ, hΦ, fun a ha => Subtype.ext (eq_of_ex F hP fun z' => ?_), fun n s hA a => ?_⟩
    · obtain ⟨z, hz⟩ := hon z'
      rw [← ex_congr_type F hP ε a.2 hz, ← ex_congr_type F hP ε (Submodule.coe_mem 0) hz]
      apply hU
      rw [← hex, ← hex, ha, map_zero Φ]
    · rw [smul_smul, mul_comm (n : ℂ)⁻¹, ← div_eq_mul_inv, hex, ex_congr_type F hP ε a.2 (hact n s hA), one_div]
  obtain ⟨Φp, hp, ip, tp⟩ := key 1 H.rt0 (by simp)
  obtain ⟨Φm, hm, im, tm⟩ := key (-1) (-H.rt0) (by simp)
  have hc : IsCompl (lat hP H.rt0) (lat hP (-H.rt0)) := ⟨disjoint_lat hP rt0_ne_neg, codisjoint_iff.2 hsp⟩
  have hd := Submodule.disjoint_def.1 (disjoint_lat hP (rt0_ne_neg (H := H)))
  have hd' := Submodule.disjoint_def.1 (disjoint_lat hP' (rt0_ne_neg (H := H)))
  have hdec : ∀ x, ∃ (a : lat hP H.rt0) (b : lat hP (-H.rt0)), x = a.1 + b.1 := fun x => by
    obtain ⟨a, ha, b, hb, e⟩ := Submodule.mem_sup.1 ((show lat hP H.rt0 ⊔ lat hP (-H.rt0) = ⊤ from hsp) ▸
      Submodule.mem_top (x := x))
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, e.symm⟩
  have hΦ : ∀ (a : lat hP H.rt0) (b : lat hP (-H.rt0)),
      LinearMap.ofIsCompl hc Φp Φm (a.1 + b.1) = Φp a + Φm b := fun a b => by
    rw [map_add (f := _), LinearMap.ofIsCompl_apply_left, LinearMap.ofIsCompl_apply_right]
  refine ⟨LinearMap.ofIsCompl hc Φp Φm, (injective_iff_map_eq_zero _).2 fun x hx => ?_, fun x => ?_, fun x => ?_,
    fun n s _ hA a ha b hb => ?_⟩
  · obtain ⟨a, b, rfl⟩ := hdec x
    rw [hΦ] at hx
    have e : Φp a = 0 := hd' _ (hp a) (by rw [eq_neg_of_add_eq_zero_left hx]; exact neg_mem (hm b))
    rw [e, zero_add] at hx
    rw [ip a e, im b hx]; simp
  · obtain ⟨a, b, rfl⟩ := hdec x
    rw [hΦ, Submodule.add_mem_iff_right _ (hp a), Submodule.add_mem_iff_right _ a.2]
    constructor
    · intro h
      rw [im b (hd' _ h (hm b))]; simp
    · intro h
      rw [show b = 0 from Subtype.ext (hd _ h b.2)]; simp
  · obtain ⟨a, b, rfl⟩ := hdec x
    rw [hΦ, Submodule.add_mem_iff_left _ (hm b), Submodule.add_mem_iff_left _ b.2]
    constructor
    · intro h
      rw [ip a (hd' _ (hp a) h)]; simp
    · intro h
      rw [show a = 0 from Subtype.ext (hd _ a.2 h)]; simp
  · have e := hΦ (wE H s • ⟨a, ha⟩) (H.bar (wE H s) • ⟨b, hb⟩)
    rw [map_smul, map_smul] at e
    have e' : LinearMap.ofIsCompl hc Φp Φm (wE H s • a + H.bar (wE H s) • b) = _ := e
    rw [e', map_add P', period_wE hP' (hp _), period_bar_wE hP' (hm _), smul_add, F.ex_add i' P' hP', ← tp n s hA,
      ← tm n s hA, ← MonObj.comp_mul, ← F.ex_add i P hP, ← smul_add, ← map_add]
    rfl

end GlobalTheory.ConjSplitAnyLevel
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_conj_split_point_lattice_linear_map : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∀ (C : Curve H) (io : C.P.A.left ⟶ C.P.A.left), IsGrpPullback C.P.A C.P.A (spMap (τ : ℂ →+* ℂ)) io → ∀ (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P), ∀ (i' : Fin F.n) (P' : (F.Di i').La →+ (Fin g → ℂ)) (hP' : IsPeriod (F.Di i') ty P'), IsSplit hP → spMap (τ : ℂ →+* ℂ) ≫ F.u i P = F.u i' P' → ∃ Φ : (F.Di i).La →ₗ[𝓞 E] (F.Di i').La, Function.Injective Φ ∧ (∀ a, Φ a ∈ lat hP' H.rt0 ↔ a ∈ lat hP H.rt0) ∧ (∀ a, Φ a ∈ lat hP' (-H.rt0) ↔ a ∈ lat hP (-H.rt0)) ∧ ∀ (n : ℕ) (s : ℤ × ℤ), 0 < n → C.ActsBy τ io n s → ∀ a ∈ lat hP H.rt0, ∀ b ∈ lat hP (-H.rt0), spMap (τ : ℂ →+* ℂ) ≫ (F.ex i P ((n : ℂ)⁻¹ • P (a + b))).left = (F.ex i' P' ((n : ℂ)⁻¹ • P' (Φ (wE H s • a + H.bar (wE H s) • b)))).left := by
  first | exact @GlobalTheory.ConjSplit.exists_conj_lattice_map | exact GlobalTheory.ConjSplit.exists_conj_lattice_map | (intros; apply GlobalTheory.ConjSplit.exists_conj_lattice_map <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.coeffField_algClosed_in_functionField_of_aut_fix_periods : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → (∀ x : KA l, σ x = (x : ℂ)) → ∀ c : Coeff l, (∀ τ : ℂ ≃+* ℂ, (∀ x ∈ c.F, τ x = x) → ConjugationPermutesPeriods F τ id) → FnAlgClosed (Xo := Xo) (c := c) := by
  first | exact @GlobalTheory.CompRat.FixedConstLevel.fnAlgClosed_of_permutes_id | exact GlobalTheory.CompRat.FixedConstLevel.fnAlgClosed_of_permutes_id | (intros; apply GlobalTheory.CompRat.FixedConstLevel.fnAlgClosed_of_permutes_id <;> assumption)
end

module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle012
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle037
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XFormsExist
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureDivisor
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.LineLatticeVectorBundle

theorem alt_det {Ω E N : Type} [Field Ω] [AddCommGroup E] [Module Ω E] [AddCommGroup N] [Module Ω N] {p : ℕ}
    (f : E [⋀^Fin p]→ₗ[Ω] N) (v : Fin p → E) (c : Matrix (Fin p) (Fin p) Ω) :
    f (fun i => ∑ j, c i j • v j) = c.det • f v := by
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff Ω]
  intro φ
  have h := AlternatingMap.eq_smul_basis_det (Pi.basisFun Ω (Fin p))
    (φ.compAlternatingMap (f.compLinearMap (Fintype.linearCombination Ω v)))
  have h2 := congrArg (fun g => g (fun i => c i)) h
  simp only [LinearMap.compAlternatingMap_apply, AlternatingMap.compLinearMap_apply,
    AlternatingMap.smul_apply, Pi.basisFun_det_apply, Pi.basisFun_apply,
    Fintype.linearCombination_apply_single, one_smul, smul_eq_mul] at h2
  simp only [Fintype.linearCombination_apply] at h2
  rw [map_sub, map_smul, h2, smul_eq_mul, mul_comm, sub_eq_zero]
  rfl

theorem line_of_span {Ω E N : Type} [Field Ω] [AddCommGroup E] [Module Ω E] [AddCommGroup N] [Module Ω N] {p : ℕ}
    (f : E [⋀^Fin p]→ₗ[Ω] N) (v v' : Fin p → E)
    (h : Submodule.span Ω (Set.range v') = Submodule.span Ω (Set.range v)) : ∃ c : Ω, f v' = c • f v := by
  have : ∀ i, ∃ c : Fin p → Ω, ∑ j, c j • v j = v' i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun Ω).1 (h ▸ Submodule.subset_span ⟨i, rfl⟩)
  choose c hc using this
  refine ⟨(Matrix.of c).det, ?_⟩
  rw [← alt_det]
  congr 1
  funext i
  exact (hc i).symm

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E]
  {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem wedge_frame {A : Lat ξ E} {p : ℕ} {v : Fin p → E} {x : Cpt ξ} (h : A.IsFrameAt v x) :
    A.wedge p x = Submodule.span (regAt ξ x) {exteriorPower.ιMulti Ω p v} := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro w ⟨b, hb, rfl⟩
    have : ∀ i, ∃ c : Fin p → regAt ξ x, ∑ j, c j • v j = b i := fun i =>
      (Submodule.mem_span_range_iff_exists_fun _).1 (h.2 ▸ hb i)
    choose c hc using this
    refine Submodule.mem_span_singleton.2 ⟨(Matrix.of c).det, ?_⟩
    have e := alt_det (exteriorPower.ιMulti Ω p) v ((regAt ξ x).subtype.mapMatrix (Matrix.of c))
    rw [← RingHom.map_det] at e
    refine e.symm.trans ?_
    congr 1
    funext i
    exact hc i
  · refine Submodule.span_mono ?_
    rintro w rfl
    exact ⟨v, fun i => h.2 ▸ Submodule.subset_span ⟨i, rfl⟩, rfl⟩

theorem span_unit {x : Cpt ξ} {u : Ω} (hu : unitAt ξ x u) (e : E) :
    Submodule.span (regAt ξ x) {u • e} = Submodule.span (regAt ξ x) {e} := by
  refine le_antisymm ?_ ?_ <;> rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
  · exact ⟨⟨u, hu.2.1⟩, rfl⟩
  · exact ⟨⟨u⁻¹, hu.2.2⟩, by
      change u⁻¹ • u • e = e
      rw [inv_smul_smul₀ hu.1]⟩

theorem coeff_unit {x : Cpt ξ} {a : E} (ha : a ≠ 0) {α α' : Ω} (h0 : α ≠ 0)
    (h : Submodule.span (regAt ξ x) {α • a} = Submodule.span (regAt ξ x) {α' • a}) :
    ∃ u, unitAt ξ x u ∧ α = u * α' := by
  obtain ⟨u, hu, e⟩ := ZUnit.exists_of_span_eq (smul_ne_zero h0 ha) h
  exact ⟨u, hu, smul_left_injective Ω ha (by simpa [mul_smul] using e)⟩

theorem on_line {A : Lat ξ E} {T : Set (Cpt ξ)} {p : ℕ} {V : Submodule Ω E} (hA : A.IsVBOn T p V)
    {a : ⋀[Ω]^p E} (ha : a ≠ 0) {x : Cpt ξ} (hx : x ∈ T) {α : Ω} (h0 : α ≠ 0)
    (h : A.wedge p x = Submodule.span (regAt ξ x) {α • a}) (v : Fin p → E)
    (hv : Submodule.span Ω (Set.range v) = V) : ∃ γ : Ω, γ ≠ 0 ∧ exteriorPower.ιMulti Ω p v = γ • a := by
  obtain ⟨U, hU, b, hb, hf⟩ := hA x hx
  have h1 := wedge_frame (hf x hx hU)
  obtain ⟨u, -, e⟩ := ZUnit.exists_of_span_eq (smul_ne_zero h0 ha) (h.symm.trans h1)
  obtain ⟨c, hc⟩ := line_of_span (exteriorPower.ιMulti Ω p) v b (hb.trans hv.symm)
  rw [hc, smul_smul] at e
  have huc : u * c ≠ 0 := by
    intro h'
    rw [h', zero_smul] at e
    exact smul_ne_zero h0 ha e
  refine ⟨(u * c)⁻¹ * α, mul_ne_zero (inv_ne_zero huc) h0, ?_⟩
  rw [mul_smul, e, inv_smul_smul₀ huc]

section
variable {A B : Lat ξ E} {p q : ℕ} {a : ⋀[Ω]^p E} {b : ⋀[Ω]^q E} {x : Cpt ξ}

theorem gen_of_coeff (ha : a ≠ 0) (hb : b ≠ 0) {f : Ω} (h : IsCoeffAt A B p q a b x f) :
    (lineLat A B p q a b).IsGenAt x f⁻¹ := by
  have h' := h
  obtain ⟨α, β, hα, hβ, hA, hB, e⟩ := h
  have hf : f ≠ 0 := by
    rintro rfl
    exact hβ (by rw [← e, zero_mul])
  refine ⟨inv_ne_zero hf, le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)⟩
  · rintro t ⟨g, ⟨α', β', hα', hβ', hA', hB', e'⟩, rfl⟩
    obtain ⟨u, hu, eu⟩ := coeff_unit ha hα' (hA'.symm.trans hA)
    obtain ⟨w, hw, ew⟩ := coeff_unit hb hβ (hB.symm.trans hB')
    refine Submodule.mem_span_singleton.2 ⟨⟨u * w, mul_mem hu.2.1 hw.2.1⟩, ?_⟩
    change u * w * f⁻¹ = g⁻¹
    have hg : g ≠ 0 := by
      rintro rfl
      exact hβ' (by rw [← e', zero_mul])
    have key : f * α = (w * g * u) * α := by rw [e, ew, ← e', eu]; ring
    have key2 : f = w * g * u := mul_right_cancel₀ hα key
    have := hu.1
    have := hw.1
    rw [key2]
    field_simp
  · rintro t rfl
    exact ⟨f, h', rfl⟩

theorem gen_iff (ha : a ≠ 0) (hb : b ≠ 0) {f : Ω} (h : IsCoeffAt A B p q a b x f) (t : Ω) :
    (lineLat A B p q a b).IsGenAt x t ↔ t ≠ 0 ∧ IsCoeffAt A B p q a b x t⁻¹ := by
  constructor
  · rintro ⟨ht, hL⟩
    refine ⟨ht, ?_⟩
    obtain ⟨u, hu, e⟩ := ZUnit.exists_of_span_eq ht (hL.symm.trans (gen_of_coeff ha hb h).2)
    obtain ⟨α, β, hα, hβ, hA, hB, e'⟩ := h
    refine ⟨u * α, β, mul_ne_zero hu.1 hα, hβ, ?_, hB, ?_⟩
    · rw [mul_smul, span_unit hu, hA]
    · have := hu.1
      rw [e, ← e', smul_eq_mul, mul_inv, inv_inv]
      field_simp
  · rintro ⟨-, h⟩
    simpa using gen_of_coeff ha hb h

theorem coeff_of_frames {v : Fin p → E} {w : Fin q → E} {α β : Ω} (hv : A.IsFrameAt v x) (hw : B.IsFrameAt w x)
    (hα : α ≠ 0) (hβ : β ≠ 0) (ev : exteriorPower.ιMulti Ω p v = α • a)
    (ew : exteriorPower.ιMulti Ω q w = β • b) : IsCoeffAt A B p q a b x (α / β)⁻¹ :=
  ⟨α, β, hα, hβ, ev ▸ wedge_frame hv, ew ▸ wedge_frame hw, by field_simp⟩

end

theorem ne_zero_of_frames {A : Lat ξ E} {p : ℕ} {a : ⋀[Ω]^p E} (ha : a ≠ 0) {x : Cpt ξ} {v v' : Fin p → E}
    {α α' : Ω} (hv : A.IsFrameAt v x) (hv' : A.IsFrameAt v' x) (e : exteriorPower.ιMulti Ω p v = α • a)
    (e' : exteriorPower.ιMulti Ω p v' = α' • a) (h : α' ≠ 0) : α ≠ 0 := by
  rintro rfl
  have h1 := (wedge_frame hv').symm.trans (wedge_frame hv)
  rw [e, e', zero_smul, Submodule.span_zero_singleton, Submodule.span_singleton_eq_bot] at h1
  exact smul_ne_zero h ha h1

end PositivityTheory.Xgn.LineLatticeVectorBundle

theorem PositivityTheory.Xgn.line_lattice_vector_bundle : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (A B : Lat ξ E) (p q : ℕ) (V V' : Submodule Ω E) (T : Set (Cpt ξ)) (a : ⋀[Ω]^p E) (b : ⋀[Ω]^q E), A.IsVBOn T p V → B.IsVBOn T q V' → a ≠ 0 → b ≠ 0 → (∃ x ∈ T, ∃ f, IsCoeffAt A B p q a b x f) → (lineLat A B p q a b).IsVBOn T 1 ⊤ ∧ (∀ x ∈ T, ∀ t : Ω, (lineLat A B p q a b).IsGenAt x t ↔ t ≠ 0 ∧ IsCoeffAt A B p q a b x t⁻¹) ∧ ∀ x ∈ T, ∀ (v : Fin p → E) (w : Fin q → E) (α β : Ω), A.IsFrameAt v x → B.IsFrameAt w x → exteriorPower.ιMulti Ω p v = α • a → exteriorPower.ιMulti Ω q w = β • b → (lineLat A B p q a b).IsGenAt x (α / β) := by
  intro X Ω _ ξ E _ _ A B p q V V' T a b hA hB ha hb hex
  obtain ⟨x₀, hx₀, f₀, α₀, β₀, hα₀, hβ₀, hA₀, hB₀, -⟩ := hex
  have loc : ∀ x ∈ T, ∃ U : X.Opens, x.1 ∈ U ∧ ∃ (v : Fin p → E) (w : Fin q → E) (α β : Ω), α ≠ 0 ∧ β ≠ 0 ∧
      exteriorPower.ιMulti Ω p v = α • a ∧ exteriorPower.ιMulti Ω q w = β • b ∧
      ∀ y ∈ T, y.1 ∈ U → A.IsFrameAt v y ∧ B.IsFrameAt w y := by
    intro x hx
    obtain ⟨U, hU, v, hv, hfv⟩ := hA x hx
    obtain ⟨U', hU', w, hw, hfw⟩ := hB x hx
    obtain ⟨α, hα, ev⟩ := PositivityTheory.Xgn.LineLatticeVectorBundle.on_line hA ha hx₀ hα₀ hA₀ v hv
    obtain ⟨β, hβ, ew⟩ := PositivityTheory.Xgn.LineLatticeVectorBundle.on_line hB hb hx₀ hβ₀ hB₀ w hw
    exact ⟨U ⊓ U', ⟨hU, hU'⟩, v, w, α, β, hα, hβ, ev, ew, fun y hy hyU => ⟨hfv y hy hyU.1, hfw y hy hyU.2⟩⟩
  refine ⟨fun x hx => ?_, fun x hx t => ?_, fun x hx v w α β hv hw ev ew => ?_⟩
  · obtain ⟨U, hU, v, w, α, β, hα, hβ, ev, ew, h⟩ := loc x hx
    have h0 : α / β ≠ 0 := div_ne_zero hα hβ
    have hr : Set.range (fun _ : Fin 1 => α / β) = {α / β} := Set.range_const
    refine ⟨U, hU, fun _ => α / β, ?_, fun y hy hyU => ⟨?_, ?_⟩⟩
    · rw [hr, eq_top_iff]
      intro s _
      exact Submodule.mem_span_singleton.2 ⟨s / (α / β), div_mul_cancel₀ s h0⟩
    · exact linearIndependent_unique_iff.2 h0
    · have := (PositivityTheory.Xgn.LineLatticeVectorBundle.gen_of_coeff ha hb
        (PositivityTheory.Xgn.LineLatticeVectorBundle.coeff_of_frames (h y hy hyU).1 (h y hy hyU).2 hα hβ ev ew)).2
      rw [inv_inv] at this
      rw [hr, this]
  · obtain ⟨U, hU, v, w, α, β, hα, hβ, ev, ew, h⟩ := loc x hx
    exact PositivityTheory.Xgn.LineLatticeVectorBundle.gen_iff ha hb
      (PositivityTheory.Xgn.LineLatticeVectorBundle.coeff_of_frames (h x hx hU).1 (h x hx hU).2 hα hβ ev ew) t
  · obtain ⟨U, hU, v', w', α', β', hα, hβ, ev', ew', h⟩ := loc x hx
    have := PositivityTheory.Xgn.LineLatticeVectorBundle.gen_of_coeff ha hb
      (PositivityTheory.Xgn.LineLatticeVectorBundle.coeff_of_frames hv hw
        (PositivityTheory.Xgn.LineLatticeVectorBundle.ne_zero_of_frames ha hv (h x hx hU).1 ev ev' hα)
        (PositivityTheory.Xgn.LineLatticeVectorBundle.ne_zero_of_frames hb hw (h x hx hU).2 ew ew' hβ) ev ew)
    rwa [inv_inv] at this
end

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.LineLatticeSpread

theorem exists_common {α : Type*} [TopologicalSpace α] [TopologicalSpace.NoetherianSpace α] [QuasiSober α]
    {O : Type*} [CommRing O] [IsDomain O] (f : α → PrimeSpectrum O) (hf : Continuous f) (C : Set α)
    (hC : IsClosed C) (h : ∀ x ∈ C, ∃ o : O, o ≠ 0 ∧ o ∈ (f x).asIdeal) :
    ∃ n : O, n ≠ 0 ∧ ∀ x ∈ C, n ∈ (f x).asIdeal := by
  classical
  obtain ⟨S, hS, hcl, hirr, hU⟩ := TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hC
  have key : ∀ Z ∈ S, ∃ o : O, o ≠ 0 ∧ ∀ x ∈ Z, o ∈ (f x).asIdeal := by
    intro Z hZ
    obtain ⟨η, hη⟩ := QuasiSober.sober (hirr Z hZ) (hcl Z hZ)
    obtain ⟨o, ho, hm⟩ := h η (by rw [hU]; exact ⟨Z, hZ, hη.mem⟩)
    refine ⟨o, ho, fun x hx => ?_⟩
    exact (PrimeSpectrum.le_iff_specializes _ _).2 ((hη.specializes hx).map hf) hm
  choose! o ho hm using key
  refine ⟨∏ Z ∈ hS.toFinset, o Z, Finset.prod_ne_zero_iff.2 fun Z hZ => ho Z (hS.mem_toFinset.1 hZ), ?_⟩
  intro x hx
  rw [hU] at hx
  obtain ⟨Z, hZ, hxZ⟩ := hx
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem o (hS.mem_toFinset.2 hZ)
  rw [hc]
  exact Ideal.mul_mem_right _ _ (hm Z hZ x hxZ)

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem isGenAt_iff (L : Lat ξ Ω) (b : Fin 1 → Ω) (q : Cpt ξ) (hb : L.IsFrameAt b q) (t : Ω) :
    L.IsGenAt q t ↔ unitAt ξ q (t / b 0) := by
  have h0 : b 0 ≠ 0 := hb.1.ne_zero 0
  have hr : Set.range b = {b 0} := Set.range_unique
  have hL : L q = Submodule.span (regAt ξ q) {b 0} := by rw [hb.2, hr]
  constructor
  · rintro ⟨ht, e⟩
    have e' := hL.symm.trans e
    refine ⟨div_ne_zero ht h0, ?_, ?_⟩
    · have : t ∈ Submodule.span (regAt ξ q) {b 0} := e' ▸ Submodule.mem_span_singleton_self t
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 this
      have hr' : (r : Ω) * b 0 = t := hr
      rw [← hr', mul_div_cancel_right₀ _ h0]
      exact r.2
    · have : b 0 ∈ Submodule.span (regAt ξ q) {t} := e' ▸ Submodule.mem_span_singleton_self (b 0)
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 this
      have hr' : (r : Ω) * t = b 0 := hr
      rw [inv_div, ← hr', mul_div_cancel_right₀ _ ht]
      exact r.2
  · rintro ⟨h1, h2, h3⟩
    have ht : t ≠ 0 := fun h => h1 (by rw [h, zero_div])
    refine ⟨ht, hL.trans (le_antisymm ?_ ?_)⟩
    · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
      refine ⟨⟨_, h3⟩, ?_⟩
      show (t / b 0)⁻¹ * t = b 0
      field_simp
    · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
      refine ⟨⟨_, h2⟩, ?_⟩
      show (t / b 0) * b 0 = t
      field_simp

end PositivityTheory.Xgn.LineLatticeSpread

open PositivityTheory.Xgn.LineLatticeSpread in
theorem PositivityTheory.Xgn.line_lattice_spread : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsNoetherianRing O] [LocallyOfFiniteType s] [QuasiCompact s], ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → Function.Injective (algebraMap O Ω) → IsCptGen ξ → ∀ (L : Lat ξ Ω) (T : Set (Cpt ξ)) (n₀ : O) (t : Ω), n₀ ≠ 0 → (∀ p, unitAt ξ p (algebraMap O Ω n₀) → p ∈ T) → L.IsVBOn T 1 ⊤ → (∀ p ∈ genFibre O ξ, L.IsGenAt p t) → ∃ n : O, n ≠ 0 ∧ ∀ p, unitAt ξ p (algebraMap O Ω n) → L.IsGenAt p t := by
  intro X Ω _ ξ O _ _ _ s _ _ _ hs _ hc L T n₀ t hn₀ hT hL hgen
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  haveI : IsNoetherian X := {}
  have hu : ∀ (p : Cpt ξ) (o : O), unitAt ξ p (algebraMap O Ω o) ↔ o ∉ (s p.1).asIdeal := fun p o =>
    (ConstReg.regular_const X Ω ξ O s hs p o).2 hc
  let W : Set X := ⋃ (U : X.Opens) (_ : ∀ q : Cpt ξ, q.1 ∈ U → L.IsGenAt q t), (U : Set X)
  have hW : IsOpen W := isOpen_iUnion fun U => isOpen_iUnion fun _ => U.isOpen
  obtain ⟨n, hn, H⟩ := exists_common (O := O) (fun x : X => s x) s.continuous (closure {genPt ξ} ∩ Wᶜ)
    (isClosed_closure.inter hW.isClosed_compl) (by
      rintro x ⟨hx, hxW⟩
      by_contra hcon
      let p : Cpt ξ := ⟨x, specializes_iff_mem_closure.2 hx⟩
      have hp : p ∈ genFibre O ξ := fun o ho => (hu p o).2 fun hm => hcon ⟨o, ho, hm⟩
      obtain ⟨U, hpU, b, -, hb⟩ := hL p (hT p (hp n₀ hn₀))
      have h1 := (isGenAt_iff L b p (hb p (hT p (hp n₀ hn₀)) hpU) t).1 (hgen p hp)
      obtain ⟨U₁, hp₁, H₁⟩ := (regAt_unitAt_open X Ω ξ p _).2 h1
      obtain ⟨U₂, hp₂, H₂⟩ := (regAt_unitAt_open X Ω ξ p _).2 (hp n₀ hn₀)
      refine hxW (Set.mem_iUnion₂.2 ⟨U ⊓ U₁ ⊓ U₂, ?_, ⟨⟨hpU, hp₁⟩, hp₂⟩⟩)
      rintro q ⟨⟨hq, hq₁⟩, hq₂⟩
      exact (isGenAt_iff L b q (hb q (hT q (H₂ q hq₂)) hq) t).2 (H₁ q hq₁))
  refine ⟨n, hn, fun p hp => ?_⟩
  have hpW : p.1 ∈ W := by
    by_contra hW'
    exact (hu p n).1 hp (H p.1 ⟨specializes_iff_mem_closure.1 p.2, hW'⟩)
  obtain ⟨U, hU, hpU⟩ := Set.mem_iUnion₂.1 hpW
  exact hU p hpU
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace PositivityTheory.Xgn.A_vertdiv_commensurable

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω] {K : Type} [Fintype K] [DecidableEq K]
  {ι : K → Type} [∀ k, Fintype (ι k)]

def Pair (x : (Σ k, ι k) → Ω) (c : K → ℤ) (u : Ω) (f g : MRing ι O) : Prop :=
  (∃ bf bg : K → ℕ, IsMultiHomog f bf ∧ IsMultiHomog g bg ∧ (fun k => (bf k : ℤ) - bg k) = c) ∧
    aeval x f = u * aeval x g

theorem cross {x : (Σ k, ι k) → Ω} {c : K → ℤ} {u : Ω} {f g f' g' : MRing ι O}
    (h : Pair x c u f g) (h' : Pair x c u f' g') : f * g' - f' * g ∈ pointIdeal O x := by
  obtain ⟨⟨bf, bg, hf, hg, hd⟩, hv⟩ := h
  obtain ⟨⟨bf', bg', hf', hg', hd'⟩, hv'⟩ := h'
  have he : bf + bg' = bf' + bg := by
    funext k
    have h1 := congrFun hd k
    have h2 := congrFun hd' k
    simp only [Pi.add_apply] at h1 h2 ⊢
    omega
  have h1 : IsWeightedHomogeneous (blockWeight ι) (f * g') (bf + bg') := IsWeightedHomogeneous.mul hf hg'
  have h2 : IsWeightedHomogeneous (blockWeight ι) (f' * g) (bf + bg') := by
    rw [he]; exact IsWeightedHomogeneous.mul hf' hg
  refine GenericProjClosureDivisor.mem_of_homog (b := bf + bg') ?_ ?_
  · exact (mem_weightedHomogeneousSubmodule _ _ _ _).mp
      (sub_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr h1)
        ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr h2))
  · rw [map_sub, map_mul, map_mul, hv, hv']
    ring

omit [∀ k, Fintype (ι k)] in
theorem mono_homog (s : ∀ k, ι k) (e : K → ℕ) :
    IsMultiHomog (∏ k, X ⟨k, s k⟩ ^ e k : MRing ι O) e := by
  have he : e = ∑ k, e k • blockWeight ι ⟨k, s k⟩ := by
    ext j
    simp [blockWeight, Pi.single_apply]
  unfold IsMultiHomog
  conv => enter [3]; rw [he]
  exact IsWeightedHomogeneous.prod _ _ _ fun k _ => (isWeightedHomogeneous_X O _ _).pow _

theorem product_powers_not_mem_prime {A : Type} [CommRing A] {W : Ideal A} (hW : W.IsPrime) {c : A} (hc : c ∉ W) (y : K → A)
    (hy : ∀ k, y k ∉ W) (n : ℕ) (e : K → ℕ) : c ^ n * ∏ k, y k ^ e k ∉ W := by
  intro hf
  rcases hW.mem_or_mem hf with h3 | h3
  · exact hc (hW.mem_of_pow_mem n h3)
  · obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (p := W)).1 h3
    exact hy k (hW.mem_of_pow_mem (e k) hk)

theorem zpow_aux (y : K → Ω) (hy : ∀ k, y k ≠ 0) (b b' : K → ℤ) (p q : K → ℕ)
    (h : ∀ k, b k + q k = b' k + p k) :
    (∏ k, y k ^ b k) * ∏ k, y k ^ q k = (∏ k, y k ^ b' k) * ∏ k, y k ^ p k := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hy k), ← zpow_add₀ (hy k), h k]

theorem mul_eq_one_of_covolume_identity {m m' t D P Q r u : Ω} (hm : m' ≠ 0) (h : t * m = r * (u * m')) (hb : m * Q = m' * P) :
    t * (D * P) = u * (r * D * Q) := by
  apply mul_left_cancel₀ hm
  linear_combination D * Q * h - D * t * hb

omit [∀ k, Fintype (ι k)] in
theorem pair_num {x : (Σ k, ι k) → Ω} {ϖ : O} {b b' : K → ℤ} {u : Ω} {s : ∀ k, ι k} (hs : mseg x s ≠ 0)
    {W : Ideal (MRing ι O)} (hW : W.IsPrime) (hϖ : (C ϖ : MRing ι O) ∉ W)
    (hX : ∀ k, (X ⟨k, s k⟩ : MRing ι O) ∉ W) {n : ℕ} {r : Ω} (hr : r ∈ chartRing O (mseg x) s)
    (h : algebraMap O Ω ϖ ^ n * chartMon x s b = r * (u * chartMon x s b')) :
    ∃ f g : MRing ι O, Pair x (b - b') u f g ∧ f ∉ W := by
  obtain ⟨d, F, hF, eF⟩ := A_forms_exist.chartRing_le_fracs x s hs hr
  have hx : ∀ k, x ⟨k, s k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hs k (Finset.mem_univ k)
  have hm : chartMon x s b' ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hx k)
  obtain ⟨p, hp⟩ : ∃ p : K → ℕ, ∀ k, p k = (b k - b' k).toNat := ⟨_, fun _ => rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : K → ℕ, ∀ k, q k = (b' k - b k).toNat := ⟨_, fun _ => rfl⟩
  have hpq : ∀ k, b k + q k = b' k + p k := fun k => by
    have e1 := hp k
    have e2 := hq k
    omega
  have hb : chartMon x s b * ∏ k, x ⟨k, s k⟩ ^ q k = chartMon x s b' * ∏ k, x ⟨k, s k⟩ ^ p k :=
    zpow_aux (fun k => x ⟨k, s k⟩) hx b b' p q hpq
  have h0 : IsMultiHomog (C ϖ ^ n : MRing ι O) 0 := by
    rw [← map_pow]
    exact isWeightedHomogeneous_C _ _
  have h1 : IsMultiHomog (C ϖ ^ n * ∏ k, X ⟨k, s k⟩ ^ (d + p) k : MRing ι O) (0 + (d + p)) :=
    IsWeightedHomogeneous.mul h0 (mono_homog s (d + p))
  have h2 : IsMultiHomog (F * ∏ k, X ⟨k, s k⟩ ^ q k : MRing ι O) (d + q) :=
    IsWeightedHomogeneous.mul hF (mono_homog s q)
  refine ⟨_, _, ⟨⟨_, _, h1, h2, ?_⟩, ?_⟩, product_powers_not_mem_prime hW hϖ (fun k => X ⟨k, s k⟩) hX n (d + p)⟩
  · funext k
    have e1 := hpq k
    simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply]
    omega
  · simp only [map_mul, map_prod, map_pow, aeval_X, aeval_C, eF, Pi.add_apply, pow_add,
      Finset.prod_mul_distrib]
    exact mul_eq_one_of_covolume_identity hm h hb

theorem pair_at {x : (Σ k, ι k) → Ω} {ϖ : O} {b b' : K → ℤ} {u : Ω} (hu : u ≠ 0)
    (H : ∀ s, mseg x s ≠ 0 → (∃ n : ℕ, ∃ r ∈ chartRing O (mseg x) s, algebraMap O Ω ϖ ^ n * chartMon x s b = r * (u * chartMon x s b')) ∧ ∃ n : ℕ, ∃ r ∈ chartRing O (mseg x) s, algebraMap O Ω ϖ ^ n * (u * chartMon x s b') = r * chartMon x s b)
    (W : Ideal (MRing ι O)) (hW : W.IsPrime) (hPW : pointIdeal O x ≤ W) (hrel : IsRelevant W)
    (hϖ : (C ϖ : MRing ι O) ∉ W) :
    ∃ f g : MRing ι O, Pair x (b - b') u f g ∧ f ∉ W ∧ g ∉ W := by
  choose s hX using hrel
  have hs : mseg x s ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun k _ h0 => hX k (hPW ?_)
    exact GenericProjClosureDivisor.mem_of_homog (isWeightedHomogeneous_X O _ _) (by rw [aeval_X, h0])
  obtain ⟨⟨n, r, hr, h⟩, n', r', hr', h'⟩ := H s hs
  obtain ⟨f, g, hp, hf⟩ := pair_num hs hW hϖ hX hr h
  have h'' : algebraMap O Ω ϖ ^ n' * chartMon x s b' = r' * (u⁻¹ * chartMon x s b) := by
    apply mul_left_cancel₀ hu
    rw [mul_left_comm r', ← mul_assoc u u⁻¹, mul_inv_cancel₀ hu, one_mul, ← h']
    ring
  obtain ⟨g', f', ⟨⟨bg, bf, hg1, hf1, hd⟩, hv⟩, hg'⟩ := pair_num hs hW hϖ hX hr' h''
  have hp' : Pair x (b - b') u f' g' := by
    refine ⟨⟨bf, bg, hf1, hg1, ?_⟩, ?_⟩
    · funext k
      have h1 := congrFun hd k
      simp only [Pi.sub_apply] at h1 ⊢
      omega
    · rw [hv, ← mul_assoc, mul_inv_cancel₀ hu, one_mul]
  refine ⟨f, g, hp, hf, fun hg => ?_⟩
  have h1 := W.add_mem (hPW (cross hp hp')) (W.mul_mem_left f' hg)
  rw [sub_add_cancel] at h1
  exact (hW.mem_or_mem h1).elim hf hg'

end PositivityTheory.Xgn.A_vertdiv_commensurable

theorem PositivityTheory.Xgn.t_vertdiv_commensurable : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (ϖ : O), Irreducible ϖ → ∀ d : ℕ, IsModelOver (pointIdeal O x) d → ∀ (b b' : K → ℤ) (u : Ω), u ≠ 0 → (∀ s, mseg x s ≠ 0 → (∃ n : ℕ, ∃ r ∈ chartRing O (mseg x) s, algebraMap O Ω ϖ ^ n * chartMon x s b = r * (u * chartMon x s b')) ∧ ∃ n : ℕ, ∃ r ∈ chartRing O (mseg x) s, algebraMap O Ω ϖ ^ n * (u * chartMon x s b') = r * chartMon x s b) → ∃ f g : MRing ι O, IsVerticalDivisor (pointIdeal O x) ϖ (b - b') f g ∧ aeval x f = u * aeval x g := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x ϖ hϖ d hM b b' u hu H
  have hϖP : (C ϖ : MRing ι O) ∉ pointIdeal O x := by
    intro hm
    have h1 : ϖ ∈ (pointIdeal O x).comap (C : O →+* MRing ι O) := hm
    rw [hM.noTorsion, Ideal.mem_bot] at h1
    exact hϖ.ne_zero h1
  obtain ⟨f, g, hp, hf, hg⟩ := A_vertdiv_commensurable.pair_at hu H _ hM.multiProj.isPrime le_rfl
    hM.multiProj.relevant hϖP
  refine ⟨f, g, IsVerticalDivisor.of_unit_off_special hp.1 hf hg fun W hW hPW hrel hϖW => ?_, hp.2⟩
  obtain ⟨f', g', hp', hf', hg'⟩ := A_vertdiv_commensurable.pair_at hu H W hW hPW hrel hϖW
  refine ⟨g', f', hg', hf', ?_⟩
  rw [mul_comm g' f]
  exact A_vertdiv_commensurable.cross hp hp'
end

module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle070
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle428
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle638
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle399
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivLift
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle022
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HolDifferentiableAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle012
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle035
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.Order
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle007
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm

@[expose] public section

section

open GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem exists_toReal_span_fintype {L : Type} [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
    (B : L →ₗ[ℤ] L →ₗ[ℤ] ℝ) : ∃ (κ : Type) (_ : Fintype κ) (w : κ → ℝ) (Q : κ → LinearMap.BilinForm ℤ L),
      B = ∑ j, w j • toReal (Q j) ∧ ∀ j, ∃ g : ℝ →+ ℝ, ∀ y z, (Q j y z : ℝ) = g (B y z) := by
  classical
  let b := Module.Free.chooseBasis ℤ L
  let H := Module.Free.chooseBasis ℚ ℝ
  let S : Finset (Module.Free.ChooseBasisIndex ℚ ℝ) :=
    Finset.univ.biUnion fun p : Module.Free.ChooseBasisIndex ℤ L × Module.Free.ChooseBasisIndex ℤ L =>
      (H.repr (B (b p.1) (b p.2))).support
  let f : S × Module.Free.ChooseBasisIndex ℤ L × Module.Free.ChooseBasisIndex ℤ L → ℚ :=
    fun t => H.repr (B (b t.2.1) (b t.2.2)) t.1
  obtain ⟨⟨D, hD⟩, hn⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) f
  choose m hm using hn
  have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hD
  have hm' : ∀ t, (m t : ℚ) = D * f t := fun t => by simpa [Submonoid.smul_def] using hm t
  let Q : S → LinearMap.BilinForm ℤ L := fun s => Matrix.toLinearMap₂ b b (fun i k => m (s, i, k))
  let g : S → ℝ →+ ℝ := fun s => (D : ℝ) • ((Rat.castHom ℝ).toAddMonoidHom.comp (H.coord s).toAddMonoidHom)
  have hQb : ∀ s i k, (Q s (b i) (b k) : ℝ) = D * (H.repr (B (b i) (b k)) s : ℝ) := fun s i k => by
    have h1 : Q s (b i) (b k) = m (s, i, k) := Matrix.toLinearMap₂_apply_basis _ _ _ _ _
    rw [h1]
    have := hm' (s, i, k)
    simp only [f] at this
    exact_mod_cast this
  have hQ : ∀ s y z, (Q s y z : ℝ) = g s (B y z) := by
    intro s
    have : toReal (Q s) = B.compr₂ (g s).toIntLinearMap := by
      refine LinearMap.ext_basis b b fun i k => ?_
      rw [toReal_apply, hQb]
      simp [g, H]
    intro y z
    simpa using LinearMap.congr_fun₂ this y z
  refine ⟨S, inferInstance, fun s => H s / D, Q, ?_, fun s => ⟨g s, hQ s⟩⟩
  refine LinearMap.ext_basis b b fun i k => ?_
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, hQb, smul_eq_mul]
  have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast hD'
  have key : ∀ h r : ℝ, h / D * (D * r) = r * h := fun h r => by field_simp
  have e1 : ∀ x : S, H x / D * (D * (H.repr (B (b i) (b k)) x : ℝ)) = H.repr (B (b i) (b k)) x • H x := fun x => by
    rw [Rat.smul_def]; exact key _ _
  rw [Finset.sum_congr rfl fun x _ => e1 x]
  rw [Finset.sum_coe_sort S (fun x => H.repr (B (b i) (b k)) x • H x)]
  conv_lhs => rw [← H.linearCombination_repr (B (b i) (b k))]
  rw [Finsupp.linearCombination_apply]
  refine Finsupp.sum_of_support_subset _ ?_ (fun (x : Module.Free.ChooseBasisIndex ℚ ℝ) (a : ℚ) => a • H x)
    fun x _ => zero_smul ℚ (H x)
  intro x hx
  exact Finset.mem_biUnion.2 ⟨(i, k), Finset.mem_univ _, hx⟩

theorem exists_sum_toReal_additive_images : ∀ {L : Type} [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
    (B : L →ₗ[ℤ] L →ₗ[ℤ] ℝ), ∃ (n : ℕ) (w : Fin n → ℝ) (Q : Fin n → LinearMap.BilinForm ℤ L),
      B = ∑ j, w j • toReal (Q j) ∧ ∀ j, ∃ g : ℝ →+ ℝ, ∀ y z, (Q j y z : ℝ) = g (B y z) := by
  intro L _ _ _ B
  obtain ⟨κ, _, w, Q, h1, h2⟩ := exists_toReal_span_fintype B
  let e := Fintype.equivFin κ
  refine ⟨Fintype.card κ, fun j => w (e.symm j), fun j => Q (e.symm j), ?_, fun j => h2 _⟩
  rw [h1]
  exact (e.symm.sum_comp fun s => w s • toReal (Q s)).symm

end GlobalTheory.PolFan
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory

theorem posReal_multiple_rat {X : Type} [AddCommGroup X] (x y : LinearMap.BilinForm ℤ X) (d : ℝ)
    (hd : 0 < d) (hy : y ≠ 0) (h : toReal x = d • toReal y) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ (a : ℤ) • x = (b : ℤ) • y := by
  have hpt : ∀ u v, (x u v : ℝ) = d * (y u v : ℝ) := by
    intro u v
    have := congrArg (fun f => f u v) h
    simpa [toReal] using this
  obtain ⟨u, v, huv⟩ : ∃ u v, y u v ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hy (LinearMap.ext₂ hc)
  set r : ℚ := (x u v : ℚ) / (y u v : ℚ) with hr_def
  have hy' : (y u v : ℝ) ≠ 0 := by exact_mod_cast huv
  have hdr : d = (r : ℝ) := by
    rw [hr_def]; push_cast; rw [hpt u v]; field_simp
  have hr : 0 < r := by exact_mod_cast (hdr ▸ hd)
  have hnum : 0 < r.num := Rat.num_pos.mpr hr
  have hcast : ((r.num.toNat : ℕ) : ℤ) = r.num := Int.toNat_of_nonneg hnum.le
  refine ⟨r.den, r.num.toNat, r.den_pos, by omega, ?_⟩
  apply LinearMap.ext₂
  intro p q
  simp only [LinearMap.smul_apply, smul_eq_mul]
  rw [hcast]
  apply Int.cast_injective (α := ℝ)
  push_cast
  rw [hpt p q, hdr]
  have hrr : (r : ℝ) = (r.num : ℝ) / (r.den : ℝ) := by
    rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
  have hden : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  rw [hrr]; field_simp

end GlobalTheory
end

section

noncomputable section

open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan

namespace GlobalTheory.PolFan

section OfCover

variable {X : Type} [AddCommGroup X]

theorem sum_mul_eq_of_sum_toReal_eq {L ι κ : Type} [AddCommGroup L] [Fintype ι] [Fintype κ]
    {j : L →ₗ[ℤ] LinearMap.BilinForm ℤ X} (hj : Function.Injective j) (ℓ : L →ₗ[ℤ] ℤ) {u : ι → L} {w : κ → L}
    {a : ι → ℝ} {b : κ → ℝ} (h : ∑ i, a i • toReal (j (u i)) = ∑ k, b k • toReal (j (w k))) :
    ∑ i, a i * (ℓ (u i) : ℝ) = ∑ k, b k * (ℓ (w k) : ℝ) := by
  have := sum_mul_eq_zero_of_sum_toReal hj ℓ (β := Sum.elim u w) (c := Sum.elim a (-b)) (by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, h, add_neg_cancel])
  rw [Fintype.sum_sum_type] at this
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib] at this
  linarith

theorem toReal_injective : Function.Injective (toReal : LinearMap.BilinForm ℤ X → X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :=
  fun β β' h => LinearMap.ext₂ fun a b => by
    have := LinearMap.congr_fun₂ h a b
    simp only [toReal_apply] at this
    exact_mod_cast this

end OfCover

end GlobalTheory.PolFan
end
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolFan

namespace Mark

section Defs

variable {O : Type} [CommRing O] (bar : O → O) (ψ lab : InvFun O) (i : ℕ)
  {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]

def InFace (β x : LinearMap.BilinForm ℤ X) : Prop :=
  x ∈ balForms bar X ∧ (∀ y, 0 ≤ x y y) ∧ (∀ y, β y y = 0 → x y y = 0) ∧
    ψ.evalZ (β + x) = ψ.evalZ β + ψ.evalZ x ∧ lab.evalZ (β + x) = lab.evalZ β

def IsIndec (β x : LinearMap.BilinForm ℤ X) : Prop :=
  InFace bar ψ lab β x ∧ x ≠ 0 ∧ ∀ y z, InFace bar ψ lab β y → InFace bar ψ lab β z → y ≠ 0 → z ≠ 0 → y + z ≠ x

variable (X) in
def IsMarked (β : LinearMap.BilinForm ℤ X) : Prop :=
  β ∈ balForms bar X ∧ (∀ y, 0 ≤ β y y) ∧ (∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = β → k = 1) ∧
    lab.evalZ β = ((i + 1 : ℕ) : ℝ) ∧
    ∃ S : Finset (LinearMap.BilinForm ℤ X), (∀ x, x ∈ S ↔ IsIndec bar ψ lab β x) ∧
      ∃ k : ℕ, 0 < k ∧ (k : ℤ) • β = ∑ x ∈ S, x

open Classical in
def markVal (n : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ) : ℝ :=
  if h : ∃ β : LinearMap.BilinForm ℤ (Fin n → O), ∀ a b, B a b = β a b then
    (if IsMarked bar ψ lab i (Fin n → O) h.choose then 1 else 0) else 0

end Defs

section Basic

variable {O : Type} [CommRing O] {bar : O → O} {ψ lab : InvFun O} {i : ℕ}
  {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]

open Classical in
theorem markVal_int (n : ℕ) (β : LinearMap.BilinForm ℤ (Fin n → O)) :
    markVal bar ψ lab i n (fun a b => (β a b : ℝ)) = if IsMarked bar ψ lab i (Fin n → O) β then 1 else 0 := by
  classical
  unfold markVal
  have h : ∃ β' : LinearMap.BilinForm ℤ (Fin n → O), ∀ a b, ((β a b : ℤ) : ℝ) = β' a b := ⟨β, fun _ _ => rfl⟩
  rw [dite_eq_left h]
  have e : h.choose = β := LinearMap.ext₂ fun a b => by
    have := h.choose_spec a b
    exact_mod_cast this.symm
  rw [e]

end Basic

end Mark

end GlobalTheory.PolFan
end
end

section

open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem isPartOfBasis_of_injective {L L' : Type} [AddCommGroup L] [AddCommGroup L'] {m : ℕ} (f : L →ₗ[ℤ] L')
    (hf : Function.Injective f) {v : Fin m → L} (h : IsPartOfBasis fun i => f (v i)) : IsPartOfBasis v := by
  classical
  obtain ⟨ψ, hψ⟩ := h.exists_dual
  obtain ⟨n', b, -⟩ := h
  let π : L →ₗ[ℤ] (Fin m → ℤ) := LinearMap.pi fun i => ψ i ∘ₗ f
  let s : (Fin m → ℤ) →ₗ[ℤ] L := ∑ i, (LinearMap.proj i : (Fin m → ℤ) →ₗ[ℤ] ℤ).smulRight (v i)
  have hs : ∀ c, s c = ∑ i, c i • v i := fun c => by simp [s, LinearMap.sum_apply]
  have hπ : ∀ c, π (s c) = c := fun c => by
    ext j

    simp [π, hs, map_sum, hψ]
  let K := LinearMap.ker π
  obtain ⟨n, bK'⟩ := Submodule.basisOfPid b (K.map f)
  let bK := bK'.map (Submodule.equivMapOfInjective f hf K).symm
  have hinj : Function.Injective (s.coprod K.subtype) := by
    refine (injective_iff_map_eq_zero _).2 ?_
    rintro ⟨c, k⟩ h0
    have h1 : s c + (k : L) = 0 := by simpa using h0
    have h2 : π (k : L) = 0 := k.2
    have h3 : c = 0 := by simpa [h2, hπ] using congrArg π h1
    subst h3
    have h4 : (k : L) = 0 := by simpa using h1
    exact Prod.ext rfl (Subtype.ext h4)
  have hsurj : Function.Surjective (s.coprod K.subtype) := fun x =>
    ⟨(π x, ⟨x - s (π x), by simp [K, LinearMap.mem_ker, hπ]⟩), by simp⟩
  let E : ((Fin m → ℤ) × K) ≃ₗ[ℤ] L := LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩
  refine ⟨n, ((Pi.basisFun ℤ (Fin m)).prod bK).map E, fun i => ?_⟩
  have h1 : E (Pi.single i 1, 0) = v i := by
    change (s.coprod K.subtype) (Pi.single i 1, 0) = v i
    simp [hs, Pi.single_apply]
  simpa using h1

theorem isCone_of_pull : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (X X₁ : Type) [AddCommGroup X] [Module O X]
    [Module.Finite O X] [AddCommGroup X₁] [Module O X₁] [Module.Finite O X₁] (r : X →ₗ[O] X₁) (m : ℕ)
    (γ : Fin m → LinearMap.BilinForm ℤ X₁), Function.Surjective r → IsCone bar φ (fun i => pull r (γ i)) →
    IsCone bar φ γ := by
  intro O _ bar φ X X₁ _ _ _ _ _ _ r m γ hr h
  have hmem : ∀ i, γ i ∈ balForms bar X₁ := fun i => by
    refine ⟨fun y z => ?_, fun a y z => ?_⟩
    · obtain ⟨y, rfl⟩ := hr y
      obtain ⟨z, rfl⟩ := hr z
      exact (h.mem i).1 y z
    · obtain ⟨y, rfl⟩ := hr y
      obtain ⟨z, rfl⟩ := hr z
      simpa only [pull_apply, map_smul] using (h.mem i).2 a y z
  have hinj : Function.Injective (pullBal bar r) := fun β β' e =>
    Subtype.ext (LinearMap.ext₂ fun a b => by
      obtain ⟨a, rfl⟩ := hr a
      obtain ⟨b, rfl⟩ := hr b
      exact LinearMap.congr_fun₂ (congrArg Subtype.val e) a b)
  refine ⟨hmem, fun i y => ?_, isPartOfBasis_of_injective (pullBal bar r) hinj h.basis,
    (linearOn_pull_iff hr).1 h.linear, IsStrict.of_pull hr h.strict⟩
  obtain ⟨y, rfl⟩ := hr y
  exact h.nonneg i y

end GlobalTheory.PolFan
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open GlobalTheory.ArcQ
open scoped ContDiff

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ModelExpCoord

open GlobalTheory.ShFam.Hor.LogCh
open ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows (isDerivAt0_unique)

theorem coord_holomorphic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (i : Fin Fu.n) (n : ℕ) (B : Set (Fin n → ℂ)) (P : (Fin n → ℂ) → ((Fu.Di i).La →+ (Fin g → ℂ))) (p : (Fin n → ℂ) → (Sp ℂ ⟶ Xo.XF c)) (hu : ∀ b, Fu.u i (P b) = p b ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) (V : (gen Z).affineOpens) (v : Sp (DualNumber Γ(gen Z, V.1)) ⟶ Z.t.G.left), IsOpen B → (∀ b, IsPeriod (Fu.Di i) ty (P b)) → (∀ a, DifferentiableOn ℂ (fun b => P b a) B) → (∀ b, p b ≫ pullback.snd _ _ = spMap σ) → IsTanAtG Z.t (LogKS.chart V ≫ genι Z) v → ∃ W : (Fin n → ℂ) → (Fin g → ℂ), DifferentiableOn ℂ W {b ∈ B | ⊤ ≤ (p b ≫ Z.jQ) ⁻¹ᵁ V.1} ∧ ∀ b ∈ B, ∀ (y : CxPts (genStr Z) σ) (hy : y ∈ ptsIn (genStr Z) σ V.1), y.1 = p b ≫ Z.jQ → IsDerivAt0 (fun z => GlobalTheory.ShFam.Hor.LogCh.liftEx Z Fu (p b) i (P b) (hu b) z ≫ Z.m.φ) (W b) (spMap (Formalism.L2.Pj.dualMap (evHom hy)) ≫ v) := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ g ty Fu i n B P p hu V v hB hP hPd hs hv
  classical
  have h1 := Fu.hol i n B P hB ⟨fun b _ => hP b, hPd⟩
  have hp : IsHolTo B p := TrueCx.TorHolo.isHolTo_of_fst _ _ hB (spMap σ) hs
    (LocLift.isHolTo_congr h1.1 fun b _ => (hu b).symm)
  have h2 := TrueCx.TorFrHolo.isHolTo_lift Z.m0.toSABMap.cart.1 hB (fun b z => (Fu.ex i (P b) z).left) p h1.2 hp
    (fun b z => by rw [Over.w (Fu.ex i (P b) z), ← hu b]; rfl)
  have hFt : IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin n → ℂ) × (Fin g → ℂ) =>
      liftEx Z Fu (p bz.1) i (P bz.1) (hu bz.1) bz.2 ≫ Z.m.φ) :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp h2 Z.m.φ
  have hY : IsHolTo B fun b => p b ≫ Z.jQ := ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp hp Z.jQ
  set B' := {b ∈ B | ⊤ ≤ (p b ≫ Z.jQ) ⁻¹ᵁ V.1} with hB'def
  have hB' : IsOpen B' := (hY V.1 0).1
  let yb : (Fin n → ℂ) → CxPts (genStr Z) σ := fun b =>
    ⟨p b ≫ Z.jQ, by rw [Category.assoc, Z.jQ_over]; exact hs b⟩
  have hm : ∀ b, ⊤ ≤ (p b ≫ Z.jQ) ⁻¹ᵁ V.1 → yb b ∈ ptsIn (genStr Z) σ V.1 := fun b h => h
  have hExp : ∀ b, IsExpAt Z.t (p b ≫ Z.jQ ≫ genι Z)
      (pushEx Z Fu (p b) i (P b) (p b ≫ Z.jQ ≫ genι Z) (hu b) rfl) := fun b =>
    isExpAt_pushEx E H Dw l Xo c O β Z g ty _ Fu (p b) i (P b) (p b ≫ Z.jQ ≫ genι Z) (hu b) rfl (hP b)
  have hTan : ∀ b (h : ⊤ ≤ (p b ≫ Z.jQ) ⁻¹ᵁ V.1),
      IsTanAtG Z.t (p b ≫ Z.jQ ≫ genι Z) (spMap (Formalism.L2.Pj.dualMap (evHom (hm b h))) ≫ v) := fun b h =>
    isTan_map (evHom (hm b h)) (by rw [← Category.assoc, spMap_evHom]; rfl) hv
  have hW0 : ∀ b (h : ⊤ ≤ (p b ≫ Z.jQ) ⁻¹ᵁ V.1), ∃! w, IsDerivAt0
      (fun z => liftEx Z Fu (p b) i (P b) (hu b) z ≫ Z.m.φ) w
      (spMap (Formalism.L2.Pj.dualMap (evHom (hm b h))) ≫ v) := fun b h =>
    (hExp b).2.2 _ (hTan b h)
  let W : (Fin n → ℂ) → Fin g → ℂ := fun b =>
    if h : ⊤ ≤ (p b ≫ Z.jQ) ⁻¹ᵁ V.1 then (hW0 b h).exists.choose else 0
  have hWd : ∀ b (h : ⊤ ≤ (p b ≫ Z.jQ) ⁻¹ᵁ V.1), IsDerivAt0
      (fun z => liftEx Z Fu (p b) i (P b) (hu b) z ≫ Z.m.φ) (W b)
      (spMap (Formalism.L2.Pj.dualMap (evHom (hm b h))) ≫ v) := fun b h => by
    have e : W b = (hW0 b h).exists.choose := dif_pos h
    rw [e]
    exact (hW0 b h).exists.choose_spec
  have : IsOpenImmersion (LogKS.chart V) := IsAffineOpen.isOpenImmersion_fromSpec V.2
  have hdiff : ∀ b₀ ∈ B', DifferentiableAt ℂ W b₀ := fun b₀ hb₀ => by
    have h₀ : ⊤ ≤ (p b₀ ≫ Z.jQ) ⁻¹ᵁ V.1 := hb₀.2
    let ev : (Fin n → ℂ) → (Γ(gen Z, V.1) →+* ℂ) := fun b =>
      if h : ⊤ ≤ (p b ≫ Z.jQ) ⁻¹ᵁ V.1 then evHom (hm b h) else evHom (hm b₀ h₀)
    have hevb : ∀ b (h : ⊤ ≤ (p b ≫ Z.jQ) ⁻¹ᵁ V.1), ev b = evHom (hm b h) := fun b h => dif_pos h
    have hev : ∀ cc, DifferentiableAt ℂ (fun b => ev b cc) b₀ :=
      HolLieFrame.differentiableAt_ev (B := B') (LocLift.isHolTo_mono hY hB' fun b hb => hb.1) (LogKS.chart V) ev
        (fun b hb => by rw [hevb b hb.2]; exact (spMap_evHom (hm b hb.2)).symm) hb₀
    have hder : ∀ b ∈ B', IsDerivAt0 (fun z => liftEx Z Fu (p b) i (P b) (hu b) z ≫ Z.m.φ) (W b)
        (spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (ev b)) ≫ v) := fun b hb => by
      rw [hevb b hb.2]
      exact hWd b hb.2
    refine HolLieFrame.differentiableAt_of_forms W b₀ fun w hw => ?_
    have hw' : ∀ (O : Z.t.G.left.Opens) (f : Γ(Z.t.G.left, O)),
        ⊤ ≤ (liftEx Z Fu (p b₀) i (P b₀) (hu b₀) 0 ≫ Z.m.φ) ⁻¹ᵁ O →
        fderiv ℂ (fun z => valAt' (liftEx Z Fu (p b₀) i (P b₀) (hu b₀) z ≫ Z.m.φ) O f) 0 w = 0 := by
      intro O f hO
      refine hw (fun b => fderiv ℂ (fun z => valAt' (liftEx Z Fu (p b) i (P b) (hu b) z ≫ Z.m.φ) O f) 0)
        (HolLieFrame.differentiableAt_fderiv
          (e := fun b z => liftEx Z Fu (p b) i (P b) (hu b) z ≫ Z.m.φ) hFt hb₀.1 O f hO) ?_
      obtain ⟨Fn, hF, hF'⟩ := HolLieFrame.exists_hol_snd v ev b₀ hev O f
        ((TangentOrigin.top_le_preimage_iff _ O).2 (by rw [(hder b₀ hb₀).1]; exact hO))
      refine hF.congr_of_eventuallyEq ?_
      filter_upwards [hF', hB'.mem_nhds hb₀] with b ⟨h, e'⟩ hb
      exact ((hder b hb).2 O h f).symm.trans e'
    have d₁ := LocalLift.isDerivAt0_const (fun z => liftEx Z Fu (p b₀) i (P b₀) (hu b₀) z ≫ Z.m.φ) w hw'
    have d₀ := LocalLift.isDerivAt0_const (fun z => liftEx Z Fu (p b₀) i (P b₀) (hu b₀) z ≫ Z.m.φ) 0
      fun _ _ _ => map_zero _
    obtain ⟨u, ⟨hut, hud⟩, -⟩ := (hExp b₀).2.1 0
    have hu0 := isDerivAt0_unique hud d₀
    obtain ⟨w', -, hw''⟩ := (hExp b₀).2.2 u hut
    have a1 : w = w' := hw'' w (by rw [hu0]; exact d₁)
    have a0 : (0 : Fin g → ℂ) = w' := hw'' 0 hud
    exact a1.trans a0.symm
  refine ⟨W, fun b hb => (hdiff b hb).differentiableWithinAt, fun b _ y hy hyb => ?_⟩
  have hyb' : y = yb b := Subtype.ext hyb
  subst hyb'
  exact hWd b hy

end GlobalTheory.ModelExpCoord
end
end

section

open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped MatrixOrder

namespace GlobalTheory.RedTh.RedBasis

theorem sum_sum_eq_dotProduct {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) :
    ∑ i, ∑ j, c i * c j * G i j = c ⬝ᵥ (G *ᵥ c) := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem exists_transpose_mul_self {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (hs : Gᵀ = G)
    (hp : ∀ c : Fin n → ℝ, c ≠ 0 → 0 < ∑ i, ∑ j, c i * c j * G i j) :
    ∃ g : Matrix (Fin n) (Fin n) ℝ, g.det ≠ 0 ∧ gᵀ * g = G := by
  have hT : G.PosSemidef := by
    rw [posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, fun x => ?_⟩
    · show Gᴴ = G
      rw [conjTranspose_eq_transpose_of_trivial, hs]
    · by_cases hx : x = 0
      · simp [hx]
      · have := (hp x hx).le
        rw [sum_sum_eq_dotProduct] at this
        simpa using this
  have h0 : 0 ≤ G := Matrix.nonneg_iff_posSemidef.mpr hT
  have hsq : (CFC.sqrt G).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg G)
  have hsym : (CFC.sqrt G)ᵀ = CFC.sqrt G := by
    have := hsq.1
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
    exact this
  have hgG : (CFC.sqrt G)ᵀ * CFC.sqrt G = G := by
    rw [hsym, CFC.sqrt_mul_sqrt_self G h0]
  refine ⟨CFC.sqrt G, fun hd => ?_, hgG⟩
  obtain ⟨v, hv, hgv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
  have h := hp v hv
  rw [sum_sum_eq_dotProduct, ← hgG, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose, hgv] at h
  simp at h

theorem exists_siegel_basis : ∀ (n : ℕ) (Y : Type) [AddCommGroup Y] (b₀ : Module.Basis (Fin n) ℤ Y)
    (B : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ), (∀ y z, B y z = B z y) → IsPosDef B → ∃ (b : Module.Basis (Fin n) ℤ Y)
    (d : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ), IsSiegel d u ∧ (∀ i, 0 < d i) ∧
    ∀ i j, B (b i) (b j) = gram d u i j := by
  intro n Y _ b₀ B hs hB
  let G : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => B (b₀ i) (b₀ j)
  obtain ⟨g, hg, hgG⟩ := exists_transpose_mul_self G (by ext i j; simp [G, hs])
    (by simpa [G] using (isPosDef_iff_basis b₀ B).1 hB)
  obtain ⟨γ, k, a, m, hγ, hk, ha, h1, h0, hup, hstep, hdec⟩ :=
    GlobalTheory.ClassFin.HermiteReduction.exists_reduced n g hg
  have hu : IsUnit γ.det := by rcases hγ with h | h <;> rw [h] <;> simp
  let e : Y ≃ₗ[ℤ] Y := Matrix.toLinearEquiv b₀ γ hu
  have hbe : ∀ j, b₀.map e j = ∑ i, γ i j • b₀ i := fun j => by
    simp [e, Matrix.toLinearEquiv_apply, Matrix.toLin_self]
  have hM : (γ.map (Int.cast : ℤ → ℝ))ᵀ * G * γ.map (Int.cast : ℤ → ℝ) = gram (fun i => a i ^ 2) m := by
    have e1 : (γ.map (Int.cast : ℤ → ℝ))ᵀ * G * γ.map (Int.cast : ℤ → ℝ) =
        (g * γ.map (Int.cast : ℤ → ℝ))ᵀ * (g * γ.map (Int.cast : ℤ → ℝ)) := by
      rw [← hgG, transpose_mul]; simp only [Matrix.mul_assoc]
    have e2 : (k * diagonal a * m)ᵀ * (k * diagonal a * m) = mᵀ * (diagonal a * (kᵀ * k) * diagonal a) * m := by
      simp only [transpose_mul, diagonal_transpose, Matrix.mul_assoc]
    rw [e1, hdec, e2, hk, Matrix.mul_one, diagonal_mul_diagonal, gram]
    simp only [sq]
  refine ⟨b₀.map e, fun i => a i ^ 2, m, ⟨fun i => sq_nonneg _, fun p q hq => ?_, h1, h0, hup⟩,
    fun i => pow_pos (ha i) 2, fun i j => ?_⟩
  · have h2 := hstep p q hq
    have h3 := ha p
    have h4 := ha q
    show a p ^ 2 ≤ 4 * a q ^ 2
    nlinarith
  · rw [← hM, hbe, hbe]

    simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, zsmul_eq_mul, Matrix.mul_apply,
    transpose_apply, map_apply, G, of_apply, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring

end GlobalTheory.RedTh.RedBasis
end

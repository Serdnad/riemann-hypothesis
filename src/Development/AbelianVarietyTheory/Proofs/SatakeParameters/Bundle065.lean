module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle053
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle002
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictRing
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle236
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle257
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
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
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead

namespace GlobalTheory.TameType

theorem irreducible_twist {Γ V : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ Γ V}
    (h : ρ.IsIrreducible) (ν : Γ →* ℂˣ) : (twist ρ ν).IsIrreducible := by
  let f : Subrepresentation (twist ρ ν) → Subrepresentation ρ := fun S =>
    ⟨S.toSubmodule, fun g v hv => by
      have h1 := S.toSubmodule.smul_mem ((ν g)⁻¹ : ℂˣ).1 (S.apply_mem_toSubmodule g hv)
      simpa [smul_smul] using h1⟩
  have hn : (⊥ : Submodule ℂ V) ≠ ⊤ := fun e =>
    (bot_ne_top (α := Subrepresentation ρ)) (Subrepresentation.toSubmodule_injective e)
  have : Nontrivial (Subrepresentation (twist ρ ν)) := ⟨⊥, ⊤, fun e =>
    hn (congrArg Subrepresentation.toSubmodule e)⟩
  refine ⟨fun S => ?_⟩
  rcases eq_bot_or_eq_top (f S) with e | e
  · exact Or.inl (Subrepresentation.toSubmodule_injective (congrArg Subrepresentation.toSubmodule e :))
  · exact Or.inr (Subrepresentation.toSubmodule_injective (congrArg Subrepresentation.toSubmodule e :))

theorem charpoly_scalar {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (z : ℂ) :
    (z • (1 : Module.End ℂ V)).charpoly = (X - C z) ^ Module.finrank ℂ V := by
  classical
  rw [← LinearMap.charpoly_toMatrix _ (Module.finBasis ℂ V), map_smul, LinearMap.toMatrix_one,
    Matrix.smul_one_eq_diagonal, Matrix.charpoly_diagonal]
  simp

section WD

open GlobalTheory.WeilDeligne

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w}

theorem weilDeligneParameter_monodromy_zero_of_unramified {a : WD h} (ha : a.unr) : a.mono0 := by
  induction a using WD.ind
  exact (WD.monodromyZero_ofWeilDeligneRepClass_iff _).2 ((WD.unr_mk _).1 ha).1

theorem inePol_of_unr {a : WD h} (ha : a.unr) {σ : G E Ω} (hσ : σ ∈ Ine (F := E) B) :
    a.inePol σ = (X - 1) ^ a.lpDim := by
  induction a using WD.ind
  rw [WD.inePol_of_mem_Ine _ hσ, WD.charPol_mk, ((WD.unr_mk _).1 ha).2, WD.lpDim_mk, LinearMap.charpoly_one]

theorem inePol_char_of_unr {a c : WD h} (ha : a.unr) (hc : c.lpDim = 1) {σ : G E Ω} (hσ : σ ∈ Ine (F := E) B)
    {z : ℂ} (hz : c.inePol σ = X - C z) : (a.lpChar c).inePol σ = (X - C z) ^ a.lpDim := by
  rw [← WD.lpDim_char a c hc]
  induction a using WD.ind with
  | hP m a =>
  induction c using WD.ind with
  | hP n c =>
    rw [WD.inePol_of_mem_Ine _ hσ, WD.charPol_mk] at hz
    have h1 := LinearMap.aeval_self_charpoly (c.ρ (ineIncl h ⟨σ, hσ⟩))
    rw [hz, map_sub, aeval_X, aeval_C, sub_eq_zero, Algebra.algebraMap_eq_smul_one] at h1
    rw [WD.lpChar_mk, WD.inePol_of_mem_Ine _ hσ, WD.charPol_mk, WD.lpDim_mk, WDRep.tensor_ρ,
      ((WD.unr_mk _).1 ha).2, h1, TensorProduct.map_smul_right, TensorProduct.map_one, charpoly_scalar]

end WD

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem inertialType_of_tame :
    ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N)
      (T : RowTie.WDTie N A) (S : SplitRead.Reading T) (i : N.Loc) (w : PlE H)
      (hw : IsSplitPl H w),
      TameSplitAll H.E → SplitRead.Laws S → SplitRead.TypeTame S i w hw →
      (∀ σ ∈ Ine (F := H.E) (N.plOm.1 w),
        A.inePol (A.locG (A.muC i) w) σ = X - C (iotaO N A i (chi1 N i σ))) →
      ∀ P : A.AV i, A.mono0 (A.locV i P w) ∧
        ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w),
          A.inePol (A.locV i P w) σ =
            (X - 1) ^ R.r * (X - C (iotaO N A i (chi1 N i σ))) ^ R.t := by
  intro R H what₂ N A T S i w hw hTS hL hT hmu P
  obtain ⟨htame, hram, hv⟩ := hT
  obtain ⟨v, hv0, hv⟩ := hv P
  have L := hL i w hw
  have hs := (S i w hw).mu_ok.1
  obtain ⟨π₁, π₂, h1, h2, he⟩ := hTS w _ _ _ _ v hs htame hram hv0 hv
  let c : Irr (w.adicCompletion H.E) 1 :=
    { V := ℂ, π := detRep (Fin 1) (S i w hw).mu, smooth := (isSmooth_ofChar_iff _).2 hs.detChar,
      irr := isIrreducible_ofChar _ }
  let τ : Irr (w.adicCompletion H.E) R.t :=
    { V := π₂.V, π := twist π₂.π (detChar (Fin R.t) (S i w hw).mu), smooth := isSmooth_twist π₂.smooth hs.detChar,
      irr := irreducible_twist π₂.irr _ }
  have hc : Nonempty (c.π.Equiv (detRep (Fin 1) (S i w hw).mu)) := ⟨Representation.Equiv.refl _⟩
  have e1 := L.prod _ _ π₁ τ _ he
  have e2 := L.twist _ _ c π₂ τ hc ⟨Representation.Equiv.refl _⟩
  have u1 := (L.sph _ π₁).2 h1
  have u2 := (L.sph _ π₂).2 h2
  have eV := (S i w hw).locV P
  have eM := (S i w hw).locMu c hc
  rw [e1, e2] at eV
  refine ⟨?_, fun σ hσ => ?_⟩
  · rw [T.mono0, eV, WeilDeligne.WD.monomial_sum_iff, WeilDeligne.WD.monomial_char_iff _ _ (L.dim 1 c)]
    exact ⟨weilDeligneParameter_monodromy_zero_of_unramified u1, weilDeligneParameter_monodromy_zero_of_unramified u2⟩
  · have hz := hmu σ hσ
    rw [T.inePol _ _ _ hσ, eM] at hz
    rw [T.inePol _ _ _ hσ, eV, WeilDeligne.WD.inePol_sum, inePol_of_unr u1 hσ,
      inePol_char_of_unr u2 (L.dim 1 c) hσ hz, L.dim, L.dim]

end GlobalTheory.TameType
end
end

section

open Formalism.BasicNotions Formalism.L2 Formalism.L2.NG Formalism.AUTREP
open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.AlgFormsFin

section General

variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)

local notation3 "L⁺" => maximalRealSubfield L

theorem ALint_le : ReciprocityTheory.Aut.ALint L ≤ Formalism.MainNotions.S.IntAf (L⁺) L := by
  rw [ReciprocityTheory.Aut.ALint, Subring.closure_le]
  rintro x (⟨y, rfl⟩ | ⟨a, ha, rfl⟩)
  · exact Subring.subset_closure (Or.inl ⟨⟨(y : L), y, rfl⟩, rfl⟩)
  · exact Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)

theorem le_ALint : Formalism.MainNotions.S.IntAf (L⁺) L ≤ ReciprocityTheory.Aut.ALint L := by
  show Subring.closure _ ≤ _
  rw [Subring.closure_le]
  rintro x (⟨⟨e, a, rfl⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
  · exact Subring.subset_closure (Or.inl ⟨a, rfl⟩)
  · exact Subring.subset_closure (Or.inr ⟨y, hy, rfl⟩)

theorem exists_approx {N : ℕ} (hN : 0 < N) {x : ReciprocityTheory.Aut.AL L} (hx : x ∈ ReciprocityTheory.Aut.ALint L) :
    ∃ a : 𝓞 L, ∃ r ∈ ReciprocityTheory.Aut.ALint L, x = ((a : L) ⊗ₜ[L⁺] (1 : ReciprocityTheory.Aut.AFplus L)) + (N : ReciprocityTheory.Aut.AL L) * r := by
  obtain ⟨a, r, hr, e⟩ := PIW.AdelClassFin.dual_dense (L⁺) L N hN x (ALint_le L hx)
  exact ⟨a, r, le_ALint L hr, e⟩

theorem exists_class {N : ℕ} (hN : 0 < N) : ∃ (Q : Type) (_ : Finite Q) (c : ReciprocityTheory.Aut.AL L → Q),
    ∀ x ∈ ReciprocityTheory.Aut.ALint L, ∀ y ∈ ReciprocityTheory.Aut.ALint L, c x = c y →
      ∃ r ∈ ReciprocityTheory.Aut.ALint L, x - y = (N : ReciprocityTheory.Aut.AL L) * r := by
  classical
  have hN0 : Ideal.span {(N : 𝓞 L)} ≠ ⊥ := by
    simp only [ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN.ne'
  have hfin : Finite (𝓞 L ⧸ Ideal.span {(N : 𝓞 L)}) := Ideal.finiteQuotientOfFreeOfNeBot _ hN0
  refine ⟨𝓞 L ⧸ Ideal.span {(N : 𝓞 L)}, hfin, fun x =>
    if h : x ∈ ReciprocityTheory.Aut.ALint L then Ideal.Quotient.mk _ (exists_approx L hN h).choose else 0, ?_⟩
  intro x hx y hy e
  simp only [dif_pos hx, dif_pos hy] at e
  obtain ⟨r, hr, ex⟩ := (exists_approx L hN hx).choose_spec
  obtain ⟨s, hs, ey⟩ := (exists_approx L hN hy).choose_spec
  set a := (exists_approx L hN hx).choose
  set b := (exists_approx L hN hy).choose
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at e
  obtain ⟨d, hd⟩ := e
  have hab : a = b + (N : 𝓞 L) * d := by rw [← hd]; ring
  have hi : ∀ z : 𝓞 L, ((z : L) ⊗ₜ[L⁺] (1 : ReciprocityTheory.Aut.AFplus L)) ∈ ReciprocityTheory.Aut.ALint L :=
    fun z => Subring.subset_closure (Or.inl ⟨z, rfl⟩)
  refine ⟨((d : L) ⊗ₜ[L⁺] (1 : ReciprocityTheory.Aut.AFplus L)) + r - s, sub_mem (add_mem (hi d) hr) hs, ?_⟩
  have hinc : ((a : L) ⊗ₜ[L⁺] (1 : ReciprocityTheory.Aut.AFplus L)) = ((b : L) ⊗ₜ[L⁺] (1 : ReciprocityTheory.Aut.AFplus L)) +
      (N : ReciprocityTheory.Aut.AL L) * ((d : L) ⊗ₜ[L⁺] (1 : ReciprocityTheory.Aut.AFplus L)) := by
    rw [hab, Algebra.TensorProduct.natCast_def, Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← TensorProduct.add_tmul]
    push_cast
    rfl
  rw [ex, ey, hinc]
  ring

theorem exists_cover {N : ℕ} (hN : 0 < N) : ∃ J : Finset (GAf L n), ∀ u ∈ ReciprocityTheory.Aut.Umax L n,
    ∃ j ∈ J, ∃ κ, Formalism.L2.NG.Cong L n N κ ∧ u = j * κ := by
  classical
  obtain ⟨Q, hQ, c, hc⟩ := exists_class L hN
  let φ : GAf L n → Fin n → Fin n → Q := fun g i j => c ((g.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) i j)
  let rep : (Fin n → Fin n → Q) → GAf L n := fun q =>
    if h : ∃ u ∈ ReciprocityTheory.Aut.Umax L n, φ u = q then h.choose else 1
  have hfin : Fintype (Fin n → Fin n → Q) := Fintype.ofFinite _
  refine ⟨Finset.univ.image rep, fun u hu => ?_⟩
  have hex : ∃ w ∈ ReciprocityTheory.Aut.Umax L n, φ w = φ u := ⟨u, hu, rfl⟩
  have hrep : rep (φ u) = hex.choose := dif_pos hex
  obtain ⟨hj, hφ⟩ := hex.choose_spec
  rw [← hrep] at hj hφ
  set j := rep (φ u) with hjdef
  refine ⟨j, Finset.mem_image.2 ⟨φ u, Finset.mem_univ _, rfl⟩, j⁻¹ * u, ⟨mul_mem (inv_mem hj) hu, ?_⟩, by simp⟩
  intro a b
  have hdiff : ∀ k, ∃ r ∈ ReciprocityTheory.Aut.ALint L, (u.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) k b -
      (j.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) k b = (N : ReciprocityTheory.Aut.AL L) * r := fun k =>
    hc _ (hu k b) _ (hj k b) (congrFun (congrFun hφ k) b).symm
  choose r hr e using hdiff
  have hinv : (((j⁻¹ : GAf L n)).1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) * (j.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
    rfl
  have hmat : (((j⁻¹ * u : GAf L n)).1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) - 1 =
      (((j⁻¹ : GAf L n)).1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) *
        ((u.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) - (j.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L))) := by
    rw [Matrix.mul_sub, hinv, Subgroup.coe_mul, Units.val_mul]
  refine ⟨∑ k, (((j⁻¹ : GAf L n)).1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) a k * r k,
    sum_mem fun k _ => mul_mem (inv_mem hj a k) (hr k), ?_⟩
  have := congrFun (congrFun hmat a) b
  rw [Matrix.sub_apply, Matrix.mul_apply] at this
  rw [this, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.sub_apply, e k]
  ring

variable {W : Type} [AddCommGroup W] [Module ℂ W]

def fixedForms (ρ : Representation ℂ (ReciprocityTheory.Aut.GQ L n) W) (N : ℕ) : Submodule ℂ (GAf L n → W) where
  carrier := {f | (∀ (γ : ReciprocityTheory.Aut.GQ L n) (g : GAf L n), f ((γ : GAf L n) * g) = ρ γ (f g)) ∧
    ∀ κ, Formalism.L2.NG.Cong L n N κ → ∀ g, f (g * κ) = f g}
  zero_mem' := ⟨fun γ g => by simp, fun _ _ _ => rfl⟩
  add_mem' := by
    rintro f f' ⟨h1, h2⟩ ⟨h1', h2'⟩
    exact ⟨fun γ g => by simp [h1 γ g, h1' γ g], fun κ hκ g => by simp [h2 κ hκ g, h2' κ hκ g]⟩
  smul_mem' := by
    rintro c f ⟨h1, h2⟩
    exact ⟨fun γ g => by simp [h1 γ g], fun κ hκ g => by simp [h2 κ hκ g]⟩

theorem fixedForms_finite [FiniteDimensional ℂ W] (ρ : Representation ℂ (ReciprocityTheory.Aut.GQ L n) W)
    (hT : ∃ T : Finset (GAf L n), ∀ g : GAf L n, ∃ (γ : ReciprocityTheory.Aut.GQ L n) (t : GAf L n) (u : GAf L n),
      t ∈ T ∧ u ∈ ReciprocityTheory.Aut.Umax L n ∧ g = (γ : GAf L n) * t * u)
    {N : ℕ} (hN : 0 < N) : FiniteDimensional ℂ (fixedForms L n ρ N) := by
  classical
  obtain ⟨T, hT⟩ := hT
  obtain ⟨J, hJ⟩ := exists_cover L n hN
  let Φ : fixedForms L n ρ N →ₗ[ℂ] (↥(T ×ˢ J) → W) :=
    { toFun := fun f p => (f : GAf L n → W) (p.1.1 * p.1.2)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective Φ ((injective_iff_map_eq_zero Φ).2 fun f hf => ?_)
  refine Subtype.ext (funext fun g => ?_)
  obtain ⟨γ, t, u, ht, hu, rfl⟩ := hT g
  obtain ⟨j, hj, κ, hκ, rfl⟩ := hJ u hu
  have h0 : (f : GAf L n → W) (t * j) = 0 :=
    congrFun hf ⟨(t, j), Finset.mem_product.2 ⟨ht, hj⟩⟩
  have e : (γ : GAf L n) * t * (j * κ) = ((γ : GAf L n) * (t * j)) * κ := by simp only [mul_assoc]
  show (f : GAf L n → W) _ = 0
  rw [e, f.2.2 κ hκ, f.2.1 γ, h0, map_zero]

end General

theorem finiteDimensional_forms : ∀ (D : D7) (n : ℕ) (a : AlgWt D.host.E n), (∃ T : Finset (GAf D.host.E n), ∀ g : GAf D.host.E n, ∃ (γ : ReciprocityTheory.Aut.GQ D.host.E n) (t : GAf D.host.E n) (u : GAf D.host.E n), t ∈ T ∧ u ∈ ReciprocityTheory.Aut.Umax D.host.E n ∧ g = (γ : GAf D.host.E n) * t * u) → ∀ N : ℕ, 0 < N → FiniteDimensional ℂ ↥(Submodule.span ℂ {f | f ∈ AFall D.host.E n a.ρ ∧ ∀ κ, Cong D.host.E n N κ → ∀ g, f (g * κ) = f g}) := by
  intro D n a hT N hN
  have hW : FiniteDimensional ℂ a.W := a.alg.1
  have h := fixedForms_finite D.host.E n a.ρ hT hN
  refine Submodule.finiteDimensional_of_le (S₂ := fixedForms D.host.E n a.ρ N) (Submodule.span_le.2 ?_)
  rintro f ⟨hf, hκ⟩
  exact ⟨hf.1, hκ⟩

end GlobalTheory.AlgFormsFin

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.BurnsideSub

theorem matRep_apply {k Γ : Type} [Field k] [Group Γ] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (g : Γ)
    (v : Fin a → k) :
    matRep ((Units.coeHom _).comp ρ) g v = (ρ g : Matrix (Fin a) (Fin a) k).mulVec v := by
  simp [matRep]

theorem isIrrSub_top_of_intertwine {K Γ : Type} [Field K] [Group Γ] {a d : ℕ}
    (ρ : Γ →* GL (Fin a) K) (σ : Γ →* GL (Fin d) K) (B : Matrix (Fin a) (Fin d) K)
    (C : Matrix (Fin d) (Fin a) K) (hCB : C * B = 1)
    (hint : ∀ g, (ρ g : Matrix (Fin a) (Fin a) K) * B = B * (σ g : Matrix (Fin d) (Fin d) K))
    (h : IsIrrSub ρ (LinearMap.range B.mulVecLin)) : IsIrrSub σ ⊤ := by
  have hinj : Function.Injective B.mulVecLin := by
    intro x y hxy
    have := congrArg C.mulVec hxy
    simpa [Matrix.mulVec_mulVec, hCB] using this
  have hmap : ∀ U : Submodule K (Fin d → K), (∀ g, ∀ v ∈ U, (σ g : Matrix (Fin d) (Fin d) K).mulVec v ∈ U) →
      IsInv ρ (U.map B.mulVecLin) := by
    rintro U hU g _ ⟨v, hv, rfl⟩
    refine ⟨_, hU g v hv, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hint g]
  refine ⟨fun h0 => h.1 ?_, fun g v _ => trivial, fun U _ hU => ?_⟩
  · rw [LinearMap.range_eq_map, h0, Submodule.map_bot]
  · have hle : U.map B.mulVecLin ≤ LinearMap.range B.mulVecLin := LinearMap.map_le_range
    rcases h.2.2 _ hle (hmap U hU) with h1 | h1
    · left
      exact Submodule.map_injective_of_injective hinj (h1.trans (Submodule.map_bot _).symm)
    · right
      rw [LinearMap.range_eq_map] at h1
      exact Submodule.map_injective_of_injective hinj h1

theorem span_restrict_eq_top_of_absIrrSub : ∀ {k Γ : Type} [Field k] [Group Γ] {a : ℕ} (ρ : Γ →* GL (Fin a) k)
    (W : Submodule k (Fin a → k)) (hW : Stable (matRep ((Units.coeHom _).comp ρ)) W),
    AbsIrrSub ρ W →
    Submodule.span k (Set.range fun g =>
      (matRep ((Units.coeHom _).comp ρ) g).restrict (hW g)) = ⊤ := by
  intro k Γ _ _ a ρ W hW habs
  classical
  set τ := matRep ((Units.coeHom (Matrix (Fin a) (Fin a) k)).comp ρ) with hτ
  let r : Γ → Module.End k W := fun g => (τ g).restrict (hW g)
  have hr1 : r 1 = 1 := by
    ext v; simp [r]
  have hrm : ∀ g h, r (g * h) = r g * r h := by
    intro g h; ext v; simp [r]
  let d := Module.finrank k W
  let e : W ≃ₗ[k] (Fin d → k) := (Module.finBasis k W).equivFun

  let φ : Module.End k W ≃ₗ[k] Matrix (Fin d) (Fin d) k :=
    e.conj.trans LinearMap.toMatrix'
  have hφa : ∀ x, φ x = LinearMap.toMatrix' ((e : W →ₗ[k] (Fin d → k)) ∘ₗ x ∘ₗ
      (e.symm : (Fin d → k) →ₗ[k] W)) := fun _ => rfl
  have hφ1 : φ 1 = 1 := by
    rw [hφa]
    have : (e : W →ₗ[k] (Fin d → k)) ∘ₗ (1 : Module.End k W) ∘ₗ
        (e.symm : (Fin d → k) →ₗ[k] W) = LinearMap.id := LinearMap.ext fun v => by simp
    rw [this, LinearMap.toMatrix'_id]
  have hφm : ∀ x y, φ (x * y) = φ x * φ y := by
    intro x y
    rw [hφa, hφa, hφa, ← LinearMap.toMatrix'_comp]
    congr 1
    exact LinearMap.ext fun v => by simp
  let S : Γ →* Matrix (Fin d) (Fin d) k :=
    { toFun := fun g => φ (r g)
      map_one' := by rw [hr1, hφ1]
      map_mul' := fun g h => by rw [hrm, hφm] }
  let σ : Γ →* GL (Fin d) k := MonoidHom.toHomUnits S
  have hσ : ∀ g, (σ g : Matrix (Fin d) (Fin d) k) = φ (r g) := fun g => rfl

  let L : (Fin d → k) →ₗ[k] (Fin a → k) := W.subtype ∘ₗ e.symm.toLinearMap
  have hLinj : Function.Injective L := by
    intro x y hxy
    exact e.symm.injective (Subtype.val_injective hxy)
  obtain ⟨L', hL'⟩ := LinearMap.exists_leftInverse_of_injective L (LinearMap.ker_eq_bot.2 hLinj)
  let B : Matrix (Fin a) (Fin d) k := LinearMap.toMatrix' L
  let C : Matrix (Fin d) (Fin a) k := LinearMap.toMatrix' L'
  have hCB : C * B = 1 := by
    rw [← LinearMap.toMatrix'_comp, hL', LinearMap.toMatrix'_id]
  have hBv : ∀ c, B.mulVec c = L c := fun c => LinearMap.toMatrix'_mulVec L c
  have hint : ∀ g, (ρ g : Matrix (Fin a) (Fin a) k) * B = B * (σ g : Matrix (Fin d) (Fin d) k) := by
    intro g
    have hM : (ρ g : Matrix (Fin a) (Fin a) k) = LinearMap.toMatrix' (τ g) := by
      have : τ g = Matrix.toLin' (ρ g : Matrix (Fin a) (Fin a) k) :=
        LinearMap.ext fun v => by rw [hτ, matRep_apply, Matrix.toLin'_apply]
      rw [this, LinearMap.toMatrix'_toLin']
    rw [hσ, hφa, hM, ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp]
    congr 1
    refine LinearMap.ext fun c => ?_
    change τ g ((e.symm c : W) : Fin a → k) = ((e.symm (e (r g (e.symm c))) : W) : Fin a → k)
    rw [e.symm_apply_apply]
    rfl
  set f := algebraMap k (AlgebraicClosure k) with hf
  have hspan : Submodule.span (AlgebraicClosure k) ((fun v => f ∘ v) '' W) =
      LinearMap.range (B.map f).mulVecLin := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨w, hw, rfl⟩
      refine ⟨f ∘ e ⟨w, hw⟩, ?_⟩
      funext i
      have h1 : B.mulVec (e ⟨w, hw⟩) = w := by
        rw [hBv]
        change ((e.symm (e ⟨w, hw⟩) : W) : Fin a → k) = w
        rw [e.symm_apply_apply]
      rw [Matrix.mulVecLin_apply, ← RingHom.map_mulVec, h1]
      rfl
    · rintro _ ⟨c, rfl⟩
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_eq_sum]
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [op_smul_eq_smul]
      refine Submodule.smul_mem _ _ ?_
      apply Submodule.subset_span
      refine ⟨L (Pi.single j 1), (e.symm (Pi.single j 1)).2, ?_⟩
      funext i
      simp [← hBv, Matrix.mulVec_single_one]
  unfold AbsIrrSub at habs
  rw [hspan] at habs
  have hirr : IsIrrSub (mapRep f σ) ⊤ := by
    refine isIrrSub_top_of_intertwine (mapRep f ρ) (mapRep f σ) (B.map f) (C.map f) ?_ ?_ habs
    · rw [← Matrix.map_mul, hCB]
      exact Matrix.map_one _ f.map_zero f.map_one
    · intro g
      change (ρ g : Matrix (Fin a) (Fin a) k).map f * B.map f =
        B.map f * (σ g : Matrix (Fin d) (Fin d) k).map f
      rw [← Matrix.map_mul, ← Matrix.map_mul, hint g]
  have h2 := GlobalTheory.BurnsideField.span_mat_eq_top_of_isIrrSub _ hirr
  have h3 : GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat (mapRep f σ) = fun g => (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat σ g).map f := by
    funext g
    ext p q
    simp [GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat, mapRep]
  rw [h3] at h2
  have h4 := GlobalTheory.BurnsideField.span_eq_top_of_span_map (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat σ) h2
  have h5 : Set.range (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat σ) = φ '' Set.range r := by
    rw [← Set.range_comp]; rfl
  have h6 := Submodule.map_span φ.toLinearMap (Set.range r)
  change Submodule.span k (Set.range r) = ⊤
  refine Submodule.map_injective_of_injective φ.injective ?_
  rw [h6, Submodule.map_top, LinearEquiv.range]
  rw [h5] at h4
  exact h4

end GlobalTheory.BurnsideSub
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.RepConjUniq

theorem main : ∀ D : D7, SumRepresentations.adm5 D → ∀ (i : D.nd.Loc) (x : D.nd.X i) (ρ ρ' : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar (D.nd.l i))), SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ → SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ' → ∃ Pm : GL (Fin D.R.nV) (Qbar (D.nd.l i)), ∀ g, ρ' g = Pm⁻¹ * ρ g * Pm := by
  intro D hAN i x ρ ρ' h1 h2
  obtain ⟨-, -, hCheb, hBN⟩ := hAN
  have hl : (D.nd.l i).Prime := Fact.out
  have hfin : (((placesOver D.host.E (D.nd.l i)) ∪ (D.nd.S i : Set _)) ∪ (D.nd.Q i : Set _)).Finite :=
    ((Formalism.MainNotions.SumRepresentations.placesOver_finite D.host.E (D.nd.l i) hl.ne_zero).union (D.nd.S i).finite_toSet).union
      (D.nd.Q i).finite_toSet
  have hdense := hCheb _ hfin
  have hfrob : ∀ g ∈ {σ : G D.host.E D.nd.Om | ∃ w ∉ (((placesOver D.host.E (D.nd.l i)) ∪ (D.nd.S i : Set _)) ∪
      (D.nd.Q i : Set _)), IsSplitPl D.host w ∧ ∃ B : ValuationSubring D.nd.Om,
      IsPlaceOver (F := D.host.E) B w ∧ IsFrob (F := D.host.E) B (normV w) σ},
      ((ρ g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))).charpoly =
      ((ρ' g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))).charpoly := by
    rintro σ ⟨w, hw, hsp, B, hB', hσ⟩
    simp only [Set.mem_union, not_or] at hw
    obtain ⟨⟨hwl, hwS⟩, hwQ⟩ := hw
    replace hwS : w ∉ D.nd.S i := by simpa using hwS
    replace hwQ : w ∉ D.nd.Q i := by simpa using hwQ
    have hso : SplitOut D.nd i w := ⟨hsp, hwl, hwS, hwQ⟩
    rw [h1.2.2 w hso B σ hB' hσ, h2.2.2 w hso B σ hB' hσ]
  have hall := GlobalTheory.BaseChangeConj.charpoly_eq_of_dense' ρ ρ' h1.1 h2.1 _ hdense hfrob
  exact hBN _ _ ρ ρ' h1.2.1 h2.2.1 hall

end GlobalTheory.RepConjUniq
end

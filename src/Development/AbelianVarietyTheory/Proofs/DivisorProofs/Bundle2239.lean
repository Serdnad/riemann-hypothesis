module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2205
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2207
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle044
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle052
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2208
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

theorem _root_.GlobalTheory.T.heightSlab_subset_unipotent_levi_compact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), DataJ σ J X Y L a h → ∀ b, IsFlowJ σ J X Y b → ∃ C : Set (GAd σ J), IsCompact C ∧ ∀ g, Real.exp (-1) ≤ h g → h g ≤ 1 → ∃ u ∈ unipRad σ J X, ∃ m ∈ GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r}, ∃ y ∈ C, g = u * m * y := by
  first | exact @GlobalTheory.ResidueEisenstein.slab_subset | exact GlobalTheory.ResidueEisenstein.slab_subset | (intros; apply GlobalTheory.ResidueEisenstein.slab_subset <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open scoped TensorProduct

theorem _root_.GlobalTheory.T.finiteAdeleAwayFromP_eq_zero_of_divisible_coprime : ∀ (p : ℕ) [Fact p.Prime] (α : AfP p), (∀ n : ℕ, 0 < n → n.Coprime p → ∃ β : AfP p, IsIntAf β ∧ α = n • β) → α = 0 := by
  first | (exact @GlobalTheory.AfPZero.main) | (exact GlobalTheory.AfPZero.main) | (intros; apply GlobalTheory.AfPZero.main <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnitApprox

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {p : ℕ} [Fact p.Prime]

theorem int_mul {a c : AfP p} (ha : IsIntAf a) (hc : IsIntAf c) : IsIntAf (a * c) := fun v => by
  rw [map_mul]; exact mul_mem (ha v) (hc v)

theorem int_sub {a c : AfP p} (ha : IsIntAf a) (hc : IsIntAf c) : IsIntAf (a - c) := fun v => by
  rw [map_sub]; exact sub_mem (ha v) (hc v)

theorem int_natCast (k : ℕ) : IsIntAf (k : AfP p) := fun v => by
  rw [map_natCast]; exact natCast_mem _ k

theorem exists_int_approx : ∀ (p : ℕ) [Fact p.Prime] (ε ε' : AfP p), IsIntAf ε → IsIntAf ε' → ε * ε' = 1 → ∃ u : ℕ → ℤ, (∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → (n : ℤ) ∣ u (n * m) - u n) ∧ ∀ n : ℕ, 0 < n → n.Coprime p → IsCoprime (u n) (n : ℤ) ∧ ∃ β : AfP p, IsIntAf β ∧ ε = (u n : AfP p) + (n : AfP p) * β := by
  intro p _ ε ε' hε hε' hεε'
  classical
  let u : ℕ → ℤ := fun n => if h : 0 < n ∧ n.Coprime p then
    Classical.choose (LaHatMod.exists_int_add_mul n h.1 h.2 ε hε) else 0
  have hu : ∀ n : ℕ, 0 < n → n.Coprime p → ∃ β : AfP p, IsIntAf β ∧ ε = (u n : AfP p) + (n : AfP p) * β := by
    intro n hn hnp
    have h : 0 < n ∧ n.Coprime p := ⟨hn, hnp⟩
    have hs := Classical.choose_spec (LaHatMod.exists_int_add_mul n h.1 h.2 ε hε)
    have e : u n = Classical.choose (LaHatMod.exists_int_add_mul n h.1 h.2 ε hε) := by
      simp only [u, dif_pos h]
    rw [e]; exact hs
  refine ⟨u, ?_, ?_⟩
  · intro n m hn hm hnmp
    have hnp : n.Coprime p := Nat.Coprime.coprime_mul_right hnmp
    obtain ⟨β, hβ, e1⟩ := hu n hn hnp
    obtain ⟨β', hβ', e2⟩ := hu (n * m) (Nat.mul_pos hn hm) hnmp
    apply IntDvdAdele.dvd_of_eq_mul_int p n hn hnp _ (β - (m : AfP p) * β')
      (int_sub hβ (int_mul (int_natCast m) hβ'))
    have : ((u (n * m) - u n : ℤ) : AfP p) = (u (n * m) : AfP p) - (u n : AfP p) := by push_cast; ring
    rw [this]
    have e3 : (u (n * m) : AfP p) = ε - ((n * m : ℕ) : AfP p) * β' := by rw [e2]; ring
    have e4 : (u n : AfP p) = ε - (n : AfP p) * β := by rw [e1]; ring
    rw [e3, e4]; push_cast; ring
  · intro n hn hnp
    obtain ⟨β, hβ, e1⟩ := hu n hn hnp
    refine ⟨?_, β, hβ, e1⟩
    obtain ⟨z', β', hβ', e2⟩ := LaHatMod.exists_int_add_mul n hn hnp ε' hε'
    have hd : (n : ℤ) ∣ u n * z' - 1 := by
      apply IntDvdAdele.dvd_of_eq_mul_int p n hn hnp _ ((n : AfP p) * β * β' - β * ε' - ε * β')
        (int_sub (int_sub (int_mul (int_mul (int_natCast n) hβ) hβ') (int_mul hβ hε')) (int_mul hε hβ'))
      have e4 : (u n : AfP p) = ε - (n : AfP p) * β := by rw [e1]; ring
      have e5 : (z' : AfP p) = ε' - (n : AfP p) * β' := by rw [e2]; ring
      push_cast
      rw [e4, e5]
      linear_combination hεε'
    obtain ⟨k, hk⟩ := hd
    exact ⟨z', -k, by linear_combination hk⟩

end GlobalTheory.UnitApprox
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_latticeVector_eq_nsmul_of_adelic_nsmul : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (n : ℕ), 0 < n → n.Coprime p → (∀ (c : ℤ) (a : AfP p), IsIntAf a → algebraMap ℚ (AfP p) (c : ℚ) = (n : AfP p) * a → (n : ℤ) ∣ c) → ∀ z : D.La, (∃ w ∈ LaHat D, inAf D z = n • w) → ∃ u : D.La, z = n • u := by
  first | (exact @GlobalTheory.LKGeo.LatDvd.exists_eq_nsmul_of_inAf) | (exact GlobalTheory.LKGeo.LatDvd.exists_eq_nsmul_of_inAf) | (intros; apply GlobalTheory.LKGeo.LatDvd.exists_eq_nsmul_of_inAf <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

namespace GlobalTheory.LKGeo.LiftSys

theorem exists_lift_sys : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (h₀ : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)), (∀ v ∈ LaHat D, h₀ v ∈ LaHat D) → ∃ h : ℕ → D.La →+ D.La, ∀ n : ℕ, 0 < n → n.Coprime p → ∀ x, ∃ w ∈ LaHat D, h₀ (inAf D x) = inAf D (h n x) + n • w := by
  intro p _ D h₀ hh
  classical
  haveI := D.freeLa
  haveI := D.finLa
  let Ix := Module.Free.ChooseBasisIndex ℤ D.La
  let b : Module.Basis Ix ℤ D.La := Module.Free.chooseBasis ℤ D.La
  let iA : D.La →+ AfP p ⊗[ℚ] VQ D :=
    AddMonoidHom.mk' (inAf D) (fun x y => by simp only [inAf, TensorProduct.tmul_add])
  have hiA : ∀ x, iA x = inAf D x := fun _ => rfl
  have key : ∀ n : ℕ, 0 < n → n.Coprime p → ∀ i : Ix, ∃ (x : D.La) (w : AfP p ⊗[ℚ] VQ D),
      w ∈ LaHat D ∧ h₀ (inAf D (b i)) = inAf D x + n • w := fun n hn hnp i =>
    exists_inAf_add_nsmul_of_mem_laHat p D n hn hnp _ (hh _ (AddSubgroup.subset_closure ⟨1, b i, fun v => by rw [map_one]; exact one_mem _, rfl⟩))
  let h : ℕ → D.La →+ D.La := fun n =>
    if hn : 0 < n ∧ n.Coprime p then
      (b.constr ℤ (fun i => (key n hn.1 hn.2 i).choose)).toAddMonoidHom
    else 0
  refine ⟨h, fun n hn hnp x => ?_⟩
  have hx : x ∈ Submodule.span ℤ (Set.range b) := by rw [b.span_eq]; trivial
  have hh' : h n = (b.constr ℤ (fun i => (key n hn hnp i).choose)).toAddMonoidHom := by
    simp only [h, dif_pos (And.intro hn hnp)]
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    obtain ⟨hw, e⟩ := (key n hn hnp i).choose_spec.choose_spec
    have hbi : h n (b i) = (key n hn hnp i).choose := by
      rw [hh']; simp [Module.Basis.constr_basis]
    refine ⟨_, hw, e.trans ?_⟩
    rw [hbi]
  | zero =>
    refine ⟨0, zero_mem _, ?_⟩
    rw [← hiA, ← hiA, map_zero, map_zero, map_zero, map_zero, smul_zero, add_zero]
  | add y z _ _ hy hz =>
    obtain ⟨w₁, hw₁, e₁⟩ := hy
    obtain ⟨w₂, hw₂, e₂⟩ := hz
    refine ⟨w₁ + w₂, add_mem hw₁ hw₂, ?_⟩
    rw [← hiA, ← hiA, map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hiA, hiA, hiA, hiA, e₁, e₂, smul_add]
    abel
  | smul c y _ hy =>
    obtain ⟨w, hw, e⟩ := hy
    refine ⟨c • w, zsmul_mem hw c, ?_⟩
    rw [← hiA, ← hiA, map_zsmul, map_zsmul, map_zsmul, hiA, hiA, e, smul_add, smul_comm c (n : ℕ) w]
    rw [← hiA (c • _), map_zsmul, hiA]

end GlobalTheory.LKGeo.LiftSys
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.LKGeo

theorem actG_form_eq_sim : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (g : G.GAf) (v w : AfP p ⊗[ℚ] VQ D), (D.EF.baseChange ℚ).baseChange (AfP p) (L.actG g v) (L.actG g w) = (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : (AfP p)ˣ) : AfP p) * (D.EF.baseChange ℚ).baseChange (AfP p) v w := by
  intro p _ D G L g v w
  set y : (AfP p ⊗[ℚ] G.C)ˣ := (g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 with hy
  set c : AfP p := (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : (AfP p)ˣ) : AfP p) with hc
  have hmem : (y : AfP p ⊗[ℚ] G.C) * (starT G.star (AfP p) (y : AfP p ⊗[ℚ] G.C)).unop =
      algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) c := mem_uGroup.1 g.2
  have hsy : (starT G.star (AfP p) (y : AfP p ⊗[ℚ] G.C)).unop * (y : AfP p ⊗[ℚ] G.C) =
      algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) c := by
    have h1 : (starT G.star (AfP p) (y : AfP p ⊗[ℚ] G.C)).unop =
        ((y⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) * algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) c := by
      rw [← hmem, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]
    rw [h1, _root_.mul_assoc, Algebra.commutes, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]
  have hact : ∀ u : AfP p ⊗[ℚ] VQ D, L.actG g u = actOn L.rep (AfP p) (y : AfP p ⊗[ℚ] G.C) u := fun u => rfl
  rw [hact, hact, GlobalTheory.LKGeo.adj_actOn_afP, ← Module.End.mul_apply, ← map_mul, hsy, AlgHom.commutes,
    Module.algebraMap_end_apply, LinearMap.map_smul, smul_eq_mul]

end GlobalTheory.LKGeo
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField

theorem _root_.GlobalTheory.T.latticeCompletion_eq_latticeVector_add_nsmul : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (n : ℕ), 0 < n → n.Coprime p → ∀ v ∈ LaHat D, ∃ (x : D.La) (w : TensorProduct ℚ (AfP p) (VQ D)), w ∈ LaHat D ∧ v = inAf D x + n • w := by
  first | (exact @GlobalTheory.LKGeo.exists_inAf_add_nsmul_of_mem_laHat) | (exact GlobalTheory.LKGeo.exists_inAf_add_nsmul_of_mem_laHat) | (intros; apply GlobalTheory.LKGeo.exists_inAf_add_nsmul_of_mem_laHat  <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c}


open GlobalTheory.FlagTan in
theorem der_fun_ver (M : Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw)) {K : Type} [Field K] [Algebra c.F K]
    (z : Sp K ⟶ M.X) (ho : ⊤ ≤ z ⁻¹ᵁ M.off)
    {Q : FrPt Xo c K} (hz : z ≫ toFlag M = X.ptY Q)
    {v : VIx Dw → FrPt Xo c (DualNumber K)} (hv : ∀ k : VIx Dw, IsVert Q (Pi.single k.toF (1 : K)) (v k))
    {zv : VIx Dw → (Sp (DualNumber K) ⟶ M.X)} (hl : ∀ b, zv b ≫ toFlag M = X.ptY (v b))
    {w : FrPt Xo c (DualNumber K)} {N : FIx Dw → K} (hw : IsVert Q N w)
    {zw : Sp (DualNumber K) ⟶ M.X} (hlw : zw ≫ toFlag M = X.ptY w)
    (O : M.X.Opens) (g : Γ(M.X, O)) (hzw : ⊤ ≤ zw ⁻¹ᵁ O) (hzv : ∀ b, ⊤ ≤ zv b ⁻¹ᵁ O) :
    (evalPt zw O hzw g).snd = ∑ k : VIx Dw, N k.toF * (evalPt (zv k) O (hzv _) g).snd := by
  choose vp hvp using fun m : FIx Dw → K => (existsUnique_isVert Q m).exists
  obtain ⟨y₀, h₀⟩ := GlobalTheory.FlagTan.exists_frMap (cst c K) Q
  obtain ⟨W₀, hW₀⟩ := GlobalTheory.FlagTan.exists_frMap (TrivSqZeroExt.inlAlgHom c.F K (FIx Dw → K)) Q
  let n : FIx Dw → FIx Dw → K := fun k => Pi.single k 1
  obtain ⟨W, hW, -⟩ :=
    GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c _ W₀ _ (isUnit_unip₀ (K := K) n).unit (isUnit_det_unip n)

  have hWm : ∀ m, FrMap (dir c m) W (vp m) := fun m => by
    obtain ⟨y₁, h₁, hs⟩ := hvp m
    obtain rfl := GlobalTheory.FlagTan.frMap_unique h₁ h₀
    refine (GlobalTheory.FlagTan.frMap_iff_frChg hW (GlobalTheory.FlagTan.frMap_of_comp hW₀ h₀ fun a => by ext <;> simp)).2 ?_
    unfold IsShift at hs
    convert hs using 2 with τ
    · ext i j <;> simp [unip, n, Pi.single_apply]
    · ext <;> simp [unip₀, n, Pi.single_apply]
  have hP : ∀ m, spMap (dir c m).toRingHom ≫ X.ptY W = X.ptY (vp m) := fun m => X.ptY_frMap (hWm m)
  obtain ⟨ZW, hZf, huniq⟩ := exists_thickLift M z ho hz
    (GlobalTheory.FlagTan.frMap_comp (hWm 0) (hvp 0).isDef fun a => by simp)
  have huniq' : ∀ m (x : Sp (DualNumber K) ⟶ M.X), x ≫ toFlag M = X.ptY (vp m) →
      x = spMap (dir c m).toRingHom ≫ ZW := fun m x hx => huniq m x (hx.trans (hP m).symm)
  have ew : zw = spMap (dir c N).toRingHom ≫ ZW :=
    huniq' N zw (by rw [hlw, (existsUnique_isVert Q N).unique hw (hvp N)])
  have hZO : ⊤ ≤ ZW ⁻¹ᵁ O :=
    le_preimage_of_comp primeSpectrum_trivSqZeroExt_eq (dir c N).toRingHom
      ((spMap (red c K).toRingHom) (IsLocalRing.closedPoint K)) ZW O (ew ▸ hzw)

  have hflag : ∀ N' : FIx Dw → K, (∀ σ i j, i < j → N' (some ⟨σ, i, j⟩) = 0) → X.ptY (vp N') = X.ptY y₀ :=
    fun N' hN' => by
      obtain ⟨y₁, h₁, hs⟩ := hvp N'
      obtain rfl := GlobalTheory.FlagTan.frMap_unique h₁ h₀
      exact (X.ptY_frBor (t := fun k => oneAddEps (Multiplicative.ofAdd (diagOf N' k)))
        ((GlobalTheory.Frames.frBor_iff_frChg _ _ _).2 ⟨unip K N', fun σ i j hij => by
          simp [unip, hN' σ i j hij, hij.ne], fun _ _ => by simp [unip, oneAddEps, diagOf], hs⟩)).symm
  have h0 : ∀ j : FIx Dw, j ∉ Set.range VIx.toF → (evalPt ZW O hZO g).snd j = 0 := fun j hj => by
    have hx : ⊤ ≤ (spMap (dir c (Pi.single j 1)).toRingHom ≫ ZW) ⁻¹ᵁ O := fun s _ => hZO (Set.mem_univ _)
    have e1 := huniq 0 (spMap (dir c (Pi.single j 1)).toRingHom ≫ ZW) (by
      rw [Category.assoc, hZf, hP, hP, hflag _ (fun σ i j' hij => Pi.single_eq_of_ne (by
        rintro rfl
        exact hj ⟨⟨σ, (i, j'), hij⟩, rfl⟩) _), hflag 0 fun _ _ _ _ => rfl])
    have a1 := snd_evalPt_dir ZW O hZO (Pi.single j 1) _ hx rfl g
    have a2 := snd_evalPt_dir ZW O hZO 0 _ hx e1 g
    simpa [Pi.single_apply] using a1.symm.trans a2
  have hk : ∀ k : VIx Dw, (evalPt (zv k) O (hzv k) g).snd = (evalPt ZW O hZO g).snd k.toF := fun k => by
    rw [snd_evalPt_dir ZW O hZO _ _ _
      (huniq' _ _ ((hl k).trans (congrArg X.ptY ((existsUnique_isVert Q _).unique (hv k) (hvp _))))) g]
    simp [Pi.single_apply]
  rw [snd_evalPt_dir ZW O hZO N zw hzw ew g]
  simp only [hk]
  have hz0 : ∑ k ∈ Finset.univ.filter (fun k => k ∉ Set.range VIx.toF), (evalPt ZW O hZO g).snd k * N k = 0 :=
    Finset.sum_eq_zero fun k hk => by rw [h0 k (Finset.mem_filter.1 hk).2, zero_mul]
  rw [sum_FIx, hz0, add_zero]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

end GlobalTheory.CompHS
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

theorem exists_isDef_lift_dualNumber : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) {K : Type} [Field K] [Algebra c.F K] (z : Sp K ⟶ M.X) (ho : ⊤ ≤ z ⁻¹ᵁ M.off) {Q : FrPt Xo c K} (hz : z ≫ toFlag M = X.ptY Q) (zw : Sp (DualNumber K) ⟶ M.X) (hw : spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ zw = z), ∃ w : FrPt Xo c (DualNumber K), IsDef Q w ∧ zw ≫ toFlag M = X.ptY w := by
  intro E _ _ _ H Dw l Xo c Y X Z M K _ _ z ho Q hz zw hw
  have hU : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ U₀ X Z := fun s _ => by
    have := ho (Set.mem_univ s)
    rw [M.off_eq] at this
    exact this
  have hwU : ⊤ ≤ (zw ≫ M.σ) ⁻¹ᵁ U₀ X Z :=
    le_preimage_of_dualNumber (TrivSqZeroExt.fstHom K K K).toRingHom _ _ (by rw [← Category.assoc, hw]; exact hU)
  have hF : ⊤ ≤ (zw ≫ toFlag M) ⁻¹ᵁ flagOpen X := hwU
  have hr : Set.range (zw ≫ toFlag M) ⊆ Set.range X.inc := by
    rintro _ ⟨s, rfl⟩
    exact (opensRange_inc X).ge (hF (Set.mem_univ s))
  obtain ⟨w, hwi⟩ : ∃ w, w ≫ X.inc = zw ≫ toFlag M := ⟨_, IsOpenImmersion.lift_fac X.inc _ hr⟩
  have hred : spMap (GlobalTheory.FlagTan.red c K).toRingHom ≫ w = X.pt Q := by
    rw [← cancel_mono X.inc, Category.assoc, hwi, X.pt_inc, ← hz, ← Category.assoc]
    exact congrArg (· ≫ toFlag M) hw

  have hnil : IsNilpotent (RingHom.ker (GlobalTheory.FlagTan.red c K).toRingHom) := ⟨2, by
    rw [Ideal.zero_eq_bot, eq_bot_iff, pow_two]
    refine Ideal.mul_le.2 fun a ha b hb => ?_
    have ha' : a.fst = 0 := ha
    have hb' : b.fst = 0 := hb
    rw [Ideal.mem_bot]
    ext <;> simp [ha', hb']⟩
  have hs : w ≫ pullback.snd _ _ ≫ pullback.snd _ _ = spMap (algebraMap c.F (DualNumber K)) := by
    obtain ⟨φ, hφ⟩ : ∃ φ : c.F →+* DualNumber K, spMap φ = w ≫ pullback.snd _ _ ≫ pullback.snd _ _ :=
      ⟨(Spec.preimage (w ≫ pullback.snd _ _ ≫ pullback.snd _ _)).hom, by
        rw [spMap, CommRingCat.ofHom_hom, Spec.map_preimage]⟩
    have h1 : spMap ((GlobalTheory.FlagTan.red c K).toRingHom.comp φ) = spMap (algebraMap c.F K) := by
      show Spec.map (CommRingCat.ofHom φ ≫ CommRingCat.ofHom (GlobalTheory.FlagTan.red c K).toRingHom) = _
      rw [Spec.map_comp]
      change spMap (GlobalTheory.FlagTan.red c K).toRingHom ≫ spMap φ = _
      rw [hφ, ← Category.assoc, hred, ← Category.assoc, X.pt_snd, frX_snd]
    have h2 : (GlobalTheory.FlagTan.red c K).toRingHom.comp φ = algebraMap c.F K :=
      congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
    haveI : FiniteDimensional ℚ c.F := c.fin
    haveI : Algebra.IsSeparable ℚ c.F := inferInstance
    haveI : Algebra.FormallyUnramified ℚ c.F := Algebra.FormallyUnramified.of_isSeparable ℚ c.F
    haveI : Algebra.FormallyUnramified ℤ ℚ := Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors ℤ)
    haveI : Algebra.FormallyUnramified ℤ c.F := Algebra.FormallyUnramified.comp ℤ ℚ c.F
    have h3 := Algebra.FormallyUnramified.ext' (R := ℤ) (A := c.F) (B := DualNumber K)
      (GlobalTheory.FlagTan.red c K).toRingHom hnil φ.toIntAlgHom (algebraMap c.F (DualNumber K)).toIntAlgHom
      (fun x => by
        show (GlobalTheory.FlagTan.red c K).toRingHom (φ x) =
          (GlobalTheory.FlagTan.red c K).toRingHom (algebraMap c.F (DualNumber K) x)
        exact (RingHom.congr_fun h2 x).trans ((GlobalTheory.FlagTan.red c K).commutes x).symm)
    rw [← hφ]
    exact congrArg spMap (congrArg AlgHom.toRingHom h3)
  obtain ⟨P', hP'⟩ := ((X.points (S := DualNumber K)).1 w).1 hs
  obtain ⟨P'', hP''⟩ := GlobalTheory.FlagMod.exists_frMap (GlobalTheory.FlagTan.red c K) P'
  have e1 : X.pt P'' = X.pt Q := by rw [← X.pt_frMap hP'', hP', hred]
  obtain ⟨t, ht⟩ := ((X.points (S := K)).2 P'' Q).1 e1
  obtain ⟨g, hgl, hgd, hc⟩ := (GlobalTheory.Frames.frBor_iff_frChg P'' Q t).1 ht
  have hdet : ∀ τ, IsUnit ((g τ).map (GlobalTheory.FlagTan.cst c K)).det := fun τ => by
    have h0 : IsUnit (g τ).det := by
      rw [Matrix.det_of_lowerTriangular (g τ) fun i j hij => hgl τ i j hij]
      exact IsUnit.prod_univ_iff.2 fun i => by rw [hgd]; exact Units.isUnit _
    have := h0.map (GlobalTheory.FlagTan.cst c K).toRingHom
    rwa [RingHom.map_det] at this
  obtain ⟨w', hW, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c _ P' (fun τ => (g τ).map (GlobalTheory.FlagTan.cst c K))
    (Units.map (GlobalTheory.FlagTan.cst c K).toRingHom.toMonoidHom (t none)) hdet
  have hdefQ : IsDef Q w' := by
    refine (GlobalTheory.FlagTan.frMap_iff_frChg hW hP'').2 ?_
    convert hc using 2 with τ
    · ext i j; simp
    · rfl
  have hB : FrBor (fun i => Units.map (GlobalTheory.FlagTan.cst c K).toRingHom.toMonoidHom (t i)) P' w' :=
    (GlobalTheory.Frames.frBor_iff_frChg P' w' _).2 ⟨fun τ => (g τ).map (GlobalTheory.FlagTan.cst c K),
      fun τ i j hij => by simp [hgl τ i j hij], fun τ i => by simp [hgd], hW⟩
  refine ⟨w', hdefQ, ?_⟩
  rw [← X.ptY_frBor hB, ← X.pt_inc, hP', hwi]

end GlobalTheory.CompHS
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

namespace GlobalTheory.LKGeo.ModLim

variable {p : ℕ} [Fact p.Prime]



theorem exists_limit : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (g : ℕ → D.La →+ D.La), (∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → ∀ x, ∃ z, g (n * m) x = g n x + n • z) → ∃ h₀ : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D), (∀ v ∈ LaHat D, h₀ v ∈ LaHat D) ∧ ∀ n : ℕ, 0 < n → n.Coprime p → ∀ x, ∃ w ∈ LaHat D, h₀ (inAf D x) = inAf D (g n x) + n • w := by
  first
  | exact @_root_.GlobalTheory.AdelicLimitCompactness.main
  | exact _root_.GlobalTheory.AdelicLimitCompactness.main
  | (apply _root_.GlobalTheory.AdelicLimitCompactness.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.AdelicLimitCompactness.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AdelicLimitCompactness.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AdelicLimitCompactness.main ..)

end GlobalTheory.LKGeo.ModLim
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag psiSet TIx IsTanFrame)
open scoped Classical

theorem _root_.GlobalTheory.T.existsUnique_modification_lift_sqZero_flag : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw)) {K : Type} [Field K] {ι : Type} (z : Sp K ⟶ M.X), ⊤ ≤ z ⁻¹ᵁ M.off → ∀ (w : Sp (TrivSqZeroExt K (ι → K)) ⟶ X.YY), spMap (TrivSqZeroExt.fstHom K K (ι → K)).toRingHom ≫ w = z ≫ toFlag M → ∃ w' : Sp (TrivSqZeroExt K (ι → K)) ⟶ M.X, w' ≫ toFlag M = w ∧ spMap (TrivSqZeroExt.fstHom K K (ι → K)).toRingHom ≫ w' = z ∧ ∀ O : M.X.Opens, ⊤ ≤ z ⁻¹ᵁ O → ⊤ ≤ w' ⁻¹ᵁ O := by
  first | exact @GlobalTheory.ModifLift.exists_lift_sqZero | exact GlobalTheory.ModifLift.exists_lift_sqZero | (intros; apply GlobalTheory.ModifLift.exists_lift_sqZero <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_coprime_nat_mul_finiteAdeleAwayP_integral : ∀ (p : ℕ) [Fact p.Prime] (a : AfP p), ∃ j : ℕ, 0 < j ∧ j.Coprime p ∧ IsIntAf ((j : AfP p) * a) := by
  first | (exact @GlobalTheory.DenAway.exists_coprime_nat_adele) | (exact GlobalTheory.DenAway.exists_coprime_nat_adele) | (intros; apply GlobalTheory.DenAway.exists_coprime_nat_adele  <;> assumption)
end

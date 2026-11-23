module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DpZeroRight
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.TwistedRepresentations.Tens
public import Mathlib.RingTheory.FiniteLength
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle001
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle040
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle074
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.XSmulSucc
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockDeterminantLaw
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle077
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.Descend
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle078
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.FormMem

theorem prod_fil_mem {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A}
    (hF : IsFil Φ Fil) (T : C) : ∀ (n : ℕ) (f : Fin n → Φ.A.obj T), (∀ k, f k ∈ (Fil 1).S T) →
      ∏ k, f k ∈ (Fil (n : ℤ)).S T := by
  intro n
  induction n with
  | zero =>
    intro f _
    rw [hF.top ((0 : ℕ) : ℤ) (by simp) T]
    exact Submodule.mem_top
  | succ n ih =>
    intro f h
    rw [Fin.prod_univ_succ]
    simpa only [Nat.add_comm 1 n] using
      hF.mul 1 n T (h 0) (ih (fun k => f k.succ) fun k => h k.succ)

theorem form_mem : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil)
    {d : ℕ} (E : Frame (Φ := Φ) d) (σ : ∀ T : C, E.D ⟶ T) (j q : ℕ) (I : Fin j → Fin d) (x : Φ.A.obj E.D), x ∈ (Fil q).S E.D →
    ∀ s : ComposableArrows C j, E.form σ I x s ∈ (Fil ((j + q : ℕ) : ℤ)).S (s.obj (Fin.last j)) := by
  intro R _ C _ Φ Fil hF d E σ j q I x hx s
  refine hF.mul j q _ (prod_fil_mem hF _ j _ fun k => (Fil 1).map_mem _ ?_) ((Fil q).map_mem (σ _) hx)
  rw [hF.one]
  exact E.mem _ _ _

end GlobalTheory.CompanionTheory.FormMem
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.frame_form_respects_filtration : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil)
    {d : ℕ} (E : Frame (Φ := Φ) d) (σ : ∀ T : C, E.D ⟶ T) (j q : ℕ) (I : Fin j → Fin d) (x : Φ.A.obj E.D), x ∈ (Fil q).S E.D →
    ∀ s : ComposableArrows C j, E.form σ I x s ∈ (Fil ((j + q : ℕ) : ℤ)).S (s.obj (Fin.last j)) := by
  intro R _ C _ Φ Fil hF d E σ j q I x hx s
  have prod_fil_mem (T : C) (n : ℕ) (f : Fin n → Φ.A.obj T)
      (hf : ∀ k, f k ∈ (Fil 1).S T) : ∏ k, f k ∈ (Fil (n : ℤ)).S T := by
    induction n with
    | zero =>
      rw [hF.top ((0 : ℕ) : ℤ) (by simp) T]
      exact Submodule.mem_top
    | succ n ih =>
      rw [Fin.prod_univ_succ]
      simpa only [Nat.add_comm 1 n] using
        hF.mul 1 n T (hf 0) (ih (fun k => f k.succ) fun k => hf k.succ)
  refine hF.mul j q _ (prod_fil_mem _ j _ fun k => (Fil 1).map_mem _ ?_) ((Fil q).map_mem (σ _) hx)
  rw [hF.one]
  exact E.mem _ _ _
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeZig

section SQ

variable {R : Type} [CommRing R] {D : Type 1} [Category.{0} D] {A : D ⥤ CommAlgCat.{0} R} (a b : IdF A)

def vl (T : D) : (sq a b).obj T →+ A.obj T ⧸ b.S T := (sqM a b T).subtype.toAddMonoidHom

def mk2 (T : D) : (CH.modF A).obj T →+ A.obj T ⧸ b.S T := (Ideal.Quotient.mk (b.S T)).toAddMonoidHom

def gC {q : ℕ} (x : CH.Cn (CH.modF A) q) (hx : ∀ s, x s ∈ a.S _) : CH.Cn (sq a b) q := fun s => sqMk a b (x s) (hx s)

variable {a b}

theorem mk2_eq_zero_iff_mem_S {T : D} (x : (CH.modF A).obj T) : mk2 b T x = 0 ↔ x ∈ b.S T := Ideal.Quotient.eq_zero_iff_mem

theorem map_val {T T' : D} (φ : T ⟶ T') (y : (sq a b).obj T) (x : (CH.modF A).obj T) (h : vl a b T y = mk2 b T x) :
    vl a b T' (((sq a b).map φ).hom y) = mk2 b T' (((CH.modF A).map φ).hom x) := by
  obtain ⟨y, hy⟩ := y
  have h' : y = mk2 b T x := h
  subst h'
  rfl

theorem d_val {q : ℕ} (f : CH.Cn (sq a b) q) (x : CH.Cn (CH.modF A) q)
    (h : ∀ s, vl a b _ (f s) = mk2 b _ (x s)) (s : ComposableArrows D (q + 1)) :
    vl a b _ (CH.d _ q f s) = mk2 b _ (CH.d _ q x s) := by
  change vl a b _ (∑ i : Fin (q + 2), (-1 : ℤ) ^ (i : ℕ) • ((sq a b).map (GlobalTheory.CatH.toLast i s)).hom (f (GlobalTheory.CatH.face i s))) =
    mk2 b _ (∑ i : Fin (q + 2), (-1 : ℤ) ^ (i : ℕ) • ((CH.modF A).map (GlobalTheory.CatH.toLast i s)).hom (x (GlobalTheory.CatH.face i s)))

  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, map_zsmul, map_val _ _ _ (h _)]

theorem lift_C {q : ℕ} (f : CH.Cn (sq a b) q) : ∃ x : CH.Cn (CH.modF A) q, (∀ s, x s ∈ a.S _) ∧
    ∀ s, vl a b _ (f s) = mk2 b _ (x s) := by
  have h : ∀ s, ∃ y : (CH.modF A).obj (s.obj (Fin.last q)), y ∈ a.S _ ∧ vl a b _ (f s) = mk2 b _ y := by
    intro s
    obtain ⟨y, hy, e⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 (show sqM a b _ from f s).2
    exact ⟨y, hy, e.symm⟩
  choose x hx hx' using h
  exact ⟨x, hx, hx'⟩

theorem vl_inj {T : D} {y y' : (sq a b).obj T} (h : vl a b T y = vl a b T y') : y = y' := Subtype.ext h

theorem gC_d {q : ℕ} (x : CH.Cn (CH.modF A) q) (hx : ∀ s, x s ∈ a.S _) (hd : ∀ s, CH.d _ q x s ∈ b.S _) :
    CH.d _ q (gC a b x hx) = 0 := by
  funext s
  refine vl_inj ?_
  rw [d_val _ x (fun _ => rfl) s, (mk2_eq_zero_iff_mem_S _).2 (hd s)]
  exact (map_zero (vl a b _)).symm

theorem ex_zero (hH : Subsingleton (CH.H (sq a b) 0)) (x : CH.Cn (CH.modF A) 0) (hx : ∀ s, x s ∈ a.S _)
    (hd : ∀ s, CH.d _ 0 x s ∈ b.S _) (s) : x s ∈ b.S _ := by
  have h0 := gC_d x hx hd
  have h1 : (CH.cx (sq a b)).cls (gC a b x hx) h0 = 0 := Subsingleton.elim _ _
  have h2 : gC a b x hx = 0 := ((CrystallineSemistableComparison.P.cls_surj (CH.cx (sq a b)) 0).2.1 _ h0).1 h1
  have h3 : vl a b _ (gC a b x hx s) = 0 := by rw [h2]; exact map_zero (vl a b _)
  exact (mk2_eq_zero_iff_mem_S _).1 h3

theorem ex_succ {q : ℕ} (hH : Subsingleton (CH.H (sq a b) (q + 1))) (x : CH.Cn (CH.modF A) (q + 1))
    (hx : ∀ s, x s ∈ a.S _) (hd : ∀ s, CH.d _ (q + 1) x s ∈ b.S _) :
    ∃ v : CH.Cn (CH.modF A) q, (∀ s, v s ∈ a.S _) ∧ ∀ s, (x - CH.d _ q v) s ∈ b.S _ := by
  have h0 := gC_d x hx hd
  have h1 : (CH.cx (sq a b)).cls (gC a b x hx) h0 = 0 := Subsingleton.elim _ _
  obtain ⟨u, hu⟩ := ((CrystallineSemistableComparison.P.cls_surj (CH.cx (sq a b)) (q + 1)).2.1 _ h0).1 h1
  obtain ⟨v, hv, hv'⟩ := lift_C u
  refine ⟨v, hv, fun s => ?_⟩
  have h3 := d_val u v hv' s
  have h4 : vl a b _ (CH.d _ q u s) = mk2 b _ (x s) :=
    congrArg (fun y : CH.Cn (sq a b) (q + 1) => vl a b _ (y s)) hu
  rw [h4] at h3
  refine (mk2_eq_zero_iff_mem_S _).1 ?_
  change mk2 b _ (x s - CH.d _ q v s) = 0
  rw [map_sub, h3, sub_self]

theorem cls_sub_sum {K : Cx.{1} R} {m : ℕ} {ι : Type} [Fintype ι] (g : K.X m) (hg : K.d m g = 0) (Y : ι → K.X m)
    (hY : ∀ k, K.d m (Y k) = 0) (h : K.d m (g - ∑ k, Y k) = 0) :
    K.cls g hg - ∑ k, K.cls (Y k) (hY k) = K.cls (g - ∑ k, Y k) h := by
  have e : (⟨g - ∑ k, Y k, h⟩ : K.Z m) = ⟨g, hg⟩ - ∑ k, (⟨Y k, hY k⟩ : K.Z m) := by
    refine Subtype.ext ?_
    rw [Submodule.coe_sub, Submodule.coe_sum]
  change _ = Submodule.mkQ _ (⟨g - ∑ k, Y k, h⟩ : K.Z m)

  rw [e, map_sub, map_sum]
  rfl

theorem rep_fin {m : ℕ} {ι : Type} [Fintype ι] {Cl E : CH.Cn (CH.modF A) m} {c : CH.H (sq a b) m} (hc : Rep a b Cl c)
    (Y : ι → CH.Cn (sq a b) m) (y : ι → CH.Cn (CH.modF A) m) (hY : ∀ k, CH.d _ m (Y k) = 0)
    (hy : ∀ k s, vl a b _ (Y k s) = mk2 b _ (y k s)) (hE : Cl - ∑ k, y k = E) :
    Rep a b E (c - ∑ k, (CH.cx (sq a b)).cls (Y k) (hY k)) := by
  obtain ⟨g, hg, rfl, hgs⟩ := hc
  have h : CH.d _ m (g - ∑ k, Y k) = 0 := by

    rw [map_sub, map_sum, hg]
    simp [hY]
  refine ⟨g - ∑ k, Y k, h, cls_sub_sum (K := CH.cx (sq a b)) g hg Y hY h, fun s => ?_⟩
  subst hE
  change vl a b _ (g s - (∑ k, Y k) s) = mk2 b _ (Cl s - (∑ k, y k) s)

  rw [Finset.sum_apply, Finset.sum_apply, map_sub, map_sub, map_sum, map_sum]
  exact congrArg₂ (· - ·) (hgs s) (Finset.sum_congr rfl fun k _ => hy k s)

end SQ

end GlobalTheory.CompanionTheory.ConeZig
end
end

section

open CrystallineSemistableComparison CrystallineSemistableComparison.Tw

namespace GlobalTheory.CompanionTheory.TowerSeq

theorem lseq_transport : ∀ (W : Type) [CommRing W] (l : ℕ) (S S' T T' : Sys.{1} W)
    (e : Sys.Hom S T (RingHom.id W)) (e' : Sys.Hom S' T' (RingHom.id W)),
    (∀ n, Function.Bijective (e.f n)) → (∀ n, Function.Bijective (e'.f n)) →
    LSeq l S S' → Nonempty (LSeq l T T') := by
  intro W _ l S S' T T' e e' h h' L
  let E : ∀ n, S.M n ≃ₗ[W] T.M n := fun n => LinearEquiv.ofBijective (e.f n) (h n)
  let E' : ∀ n, S'.M n ≃ₗ[W] T'.M n := fun n => LinearEquiv.ofBijective (e'.f n) (h' n)
  have hc : ∀ n y, T.r n (E (n + 1) y) = E n (S.r n y) := fun n y => e.comm n y
  have hc' : ∀ n y, T'.r n (E' (n + 1) y) = E' n (S'.r n y) := fun n y => e'.comm n y
  have hr : ∀ n x, (E n).symm (T.r n x) = S.r n ((E (n + 1)).symm x) := by
    intro n x
    apply (E n).injective
    rw [LinearEquiv.apply_symm_apply, ← hc, LinearEquiv.apply_symm_apply]
  refine ⟨{
    ρ := fun c b => (E b).toLinearMap ∘ₗ L.ρ c b ∘ₗ (E c).symm.toLinearMap
    ν := fun a c => (E c).toLinearMap ∘ₗ L.ν a c ∘ₗ (E a).symm.toLinearMap
    δ := fun b a => (E' a).toLinearMap ∘ₗ L.δ b a ∘ₗ (E b).symm.toLinearMap
    kill := ?_, ρ_self := ?_, ρ_succ := ?_, ν_ρ := ?_, ν_r := ?_, ex₁ := ?_, δ_r := ?_, ex₂ := ?_ }⟩
  · intro n x
    apply (E n).symm.injective
    rw [map_smul, L.kill, map_zero]
  · intro c x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [L.ρ_self, LinearEquiv.apply_symm_apply]
  · intro c b hb x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [L.ρ_succ c b hb, hr]
  · intro a c ha x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [L.ν_ρ a c ha, map_smul, LinearEquiv.apply_symm_apply]
  · intro a c ha y
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hc, L.ν_r a c ha, hr]
  · intro a b c hcab x hx
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hx
    have h0 : L.ρ c b ((E c).symm x) = 0 := by
      apply (E b).injective
      rw [hx, map_zero]
    obtain ⟨y, hy⟩ := L.ex₁ a b c hcab _ h0
    refine ⟨E a y, ?_⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [hy, LinearEquiv.apply_symm_apply]
  · intro b a x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hc', L.δ_r]
  · intro a b c hcab x hx
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hx
    have h0 : L.δ b a ((E b).symm x) = 0 := by
      apply (E' a).injective
      rw [hx, map_zero]
    obtain ⟨y, hy⟩ := L.ex₂ a b c hcab _ h0
    refine ⟨E c y, ?_⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [hy, LinearEquiv.apply_symm_apply]

end GlobalTheory.CompanionTheory.TowerSeq
end

section

open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw

namespace GlobalTheory.CompanionTheory.TowerLen

theorem isFiniteLength_of_ker_le_range {W : Type} [CommRing W] {A B C : Type 1}
    [AddCommGroup A] [Module W A] [AddCommGroup B] [Module W B] [AddCommGroup C] [Module W C]
    (v : A →ₗ[W] B) (f : B →ₗ[W] C) (h : LinearMap.ker f ≤ LinearMap.range v)
    (hA : IsFiniteLength W A) (hC : IsFiniteLength W C) : IsFiniteLength W B := by
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at hA hC ⊢
  obtain ⟨_, _⟩ := hA
  obtain ⟨_, _⟩ := hC
  have n1 : IsNoetherian W (LinearMap.range v) :=
    isNoetherian_of_surjective v.rangeRestrict (LinearMap.range_rangeRestrict v)
  have a1 : IsArtinian W (LinearMap.range v) :=
    isArtinian_of_surjective A v.rangeRestrict v.surjective_rangeRestrict
  have n2 : IsNoetherian W (LinearMap.ker f) :=
    isNoetherian_of_injective (Submodule.inclusion h) (Submodule.inclusion_injective h)
  have a2 : IsArtinian W (LinearMap.ker f) :=
    isArtinian_of_injective (Submodule.inclusion h) (Submodule.inclusion_injective h)
  have hr : LinearMap.range (LinearMap.ker f).subtype = LinearMap.ker f.rangeRestrict := by
    rw [Submodule.range_subtype, LinearMap.ker_rangeRestrict]
  exact ⟨isNoetherian_of_range_eq_ker _ _ hr, isArtinian_of_range_eq_ker _ _ hr⟩

theorem isFiniteLength_level : ∀ (W : Type) [CommRing W] (l : ℕ) (S S' : Sys.{1} W) (_ : LSeq l S S'),
    IsFiniteLength W (S.M 1) → ∀ n, IsFiniteLength W (S.M n) := by
  intro W _ l S S' L h1 n
  induction n with
  | zero =>
    have : Subsingleton (S.M 0) := ⟨fun x y => by
      have hx := L.kill 0 x
      have hy := L.kill 0 y
      simp only [pow_zero, one_smul] at hx hy
      rw [hx, hy]⟩
    exact IsFiniteLength.of_subsingleton
  | succ n ih =>
    refine isFiniteLength_of_ker_le_range (L.ν 1 (n + 1)) (L.ρ (n + 1) n) ?_ h1 ih
    intro x hx
    obtain ⟨y, hy⟩ := L.ex₁ 1 n (n + 1) (by omega) x hx
    exact ⟨y, hy⟩

end GlobalTheory.CompanionTheory.TowerLen
end

section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.CovComp

theorem cancel_lTensor (A : Type) [CommRing A] (B : Type) [CommRing B] [Algebra A B]
    (B₁ : Type) [CommRing B₁] [Algebra A B₁] [Algebra B B₁] [IsScalarTower A B B₁]
    {K₁ K₀ : Type} [AddCommGroup K₁] [Module A K₁] [AddCommGroup K₀] [Module A K₀]
    (d : K₁ →ₗ[A] K₀) (w : B₁ ⊗[B] (B ⊗[A] K₁)) :
    TensorProduct.AlgebraTensorModule.cancelBaseChange A B B₁ B₁ K₀ ((d.baseChange B).lTensor B₁ w) =
      d.lTensor B₁ (TensorProduct.AlgebraTensorModule.cancelBaseChange A B B₁ B₁ K₁ w) := by
  induction w with
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul b t =>
    induction t with
    | add x y hx hy => simp only [map_add (f := _), TensorProduct.tmul_add, hx, hy]
    | tmul c k => simp [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, TensorProduct.smul_tmul']

theorem cov_comp : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B](B₁ : Type) [CommRing B₁] [Algebra A B₁] [Algebra B B₁] [IsScalarTower A B B₁] (r : ℕ → A), Pf p A → Pf p B → IsRt p r → Cov p r B → Cov p (fun k => algebraMap A B (r k)) B₁ → Cov p r B₁ := by
  intro p _ A _ B _ _ B₁ _ _ _ _ r hA hB hr h1 h2
  unfold Cov at h1 h2 ⊢
  intro K₁ K₀ _ _ _ _ hK₁ hK₀ d hd z hz k
  have e1 : Pf p (B ⊗[A] K₁) := PerfectRing.pf_tensor p A B K₁ hA hB hK₁
  have e0 : Pf p (B ⊗[A] K₀) := PerfectRing.pf_tensor p A B K₀ hA hB hK₀
  have e2 : Good p (fun k => algebraMap A B (r k)) (d.baseChange B) :=
    GoodBaseChange.good_baseChange p A B r K₁ K₀ d hd
  have hz' : (1 : B₁) ⊗ₜ[B] ((1 : B) ⊗ₜ[A] z) ∈ (LinearMap.lTensor B₁ (d.baseChange B)).range := by
    obtain ⟨w, hw⟩ := hz
    refine ⟨(TensorProduct.AlgebraTensorModule.cancelBaseChange A B B₁ B₁ K₁).symm w, ?_⟩
    apply (TensorProduct.AlgebraTensorModule.cancelBaseChange A B B₁ B₁ K₀).injective
    rw [cancel_lTensor, LinearEquiv.apply_symm_apply, hw]
    simp
  have hB' := h2 _ _ e1 e0 (d.baseChange B) e2 _ hz' (k + 1)
  have h3 : (1 : B) ⊗ₜ[A] (r (k + 1) • z) ∈ (LinearMap.lTensor B d).range := by
    obtain ⟨v, hv⟩ := hB'
    refine ⟨v, ?_⟩
    change (d.baseChange B) v = _
    rw [hv, algebraMap_smul, ← TensorProduct.tmul_smul]
  have h4 := h1 K₁ K₀ hK₁ hK₀ d hd (r (k + 1) • z) h3 (k + 1)
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hrk : r k = r (k + 1) ^ (p - 2) * (r (k + 1) * r (k + 1)) := by
    rw [← hr k, ← sq, ← pow_add, Nat.sub_add_cancel hp]
  rw [hrk, mul_smul, mul_smul]
  exact Submodule.smul_mem _ _ h4

end GlobalTheory.CompanionTheory.CovComp
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

namespace GlobalTheory.CompanionTheory.LineUniv

theorem exists_line : ∀ {C : Type u} [Category.{v} C] (U : UF C) (P : ∀ ⦃T T' : C⦄, (T ⟶ T') → (T' ⟶ T') → Prop), (∀ T : C, ∃ (T₁ : C) (i : T ⟶ T₁) (η : U.U T₁), (∀ (T' : C) (φ : T ⟶ T') (a : U.U T'), ∃! ψ : T₁ ⟶ T', i ≫ ψ = φ ∧ U.map ψ η = a) ∧ ∀ g : T₁ ⟶ T₁, i ≫ g = i → U.map g η = U.q _ * η → P i g) → ∃ L : Line (𝟭 C) U, ∀ T, P (L.i.app T) (L.γ.app T) := by
  intro C _ U P h
  choose T₁ i η hu hP using h
  have hm : ∀ (T T' : C) (φ : T ⟶ T'), ∃ ψ : T₁ T ⟶ T₁ T', i T ≫ ψ = φ ≫ i T' ∧ U.map ψ (η T) = η T' :=
    fun T T' φ => (hu T _ (φ ≫ i T') (η T')).exists
  choose m hm1 hm2 using hm
  have hg : ∀ T, ∃ g : T₁ T ⟶ T₁ T, i T ≫ g = i T ∧ U.map g (η T) = U.q _ * η T :=
    fun T => (hu T _ (i T) _).exists
  choose g hg1 hg2 using hg
  have uniq : ∀ (T T' : C) (φ : T ⟶ T') (a : U.U T') (ψ ψ' : T₁ T ⟶ T'), i T ≫ ψ = φ → U.map ψ (η T) = a →
      i T ≫ ψ' = φ → U.map ψ' (η T) = a → ψ = ψ' :=
    fun T T' φ a ψ ψ' h1 h2 h3 h4 => (hu T T' φ a).unique ⟨h1, h2⟩ ⟨h3, h4⟩
  let Ξ : C ⥤ C :=
    { obj := T₁
      map := fun {T T'} φ => m T T' φ
      map_id := fun T => uniq T _ (i T) (η T) _ _ (by rw [hm1, Category.id_comp]) (hm2 _ _ _)
        (Category.comp_id _) (U.map_id _ _)
      map_comp := fun {T T' T''} φ ψ => uniq T _ (φ ≫ ψ ≫ i T'') (η T'') _ _
        (by rw [hm1, Category.assoc]) (hm2 _ _ _)
        (by rw [← Category.assoc, hm1, Category.assoc, hm1])
        (by rw [U.map_comp, hm2, hm2]) }
  let iN : 𝟭 C ⟶ Ξ :=
    { app := i
      naturality := fun {T T'} φ => (hm1 T T' φ).symm }
  let γN : Ξ ⟶ Ξ :=
    { app := g
      naturality := fun {T T'} φ => uniq T _ (φ ≫ i T') (U.q _ * η T') _ _
        (by
          change i T ≫ m T T' φ ≫ g T' = _
          rw [← Category.assoc, hm1, Category.assoc, hg1])
        (by
          change U.map (m T T' φ ≫ g T') (η T) = _
          rw [U.map_comp, hm2, hg2])
        (by
          change i T ≫ g T ≫ m T T' φ = _
          rw [← Category.assoc, hg1, hm1])
        (by
          change U.map (g T ≫ m T T' φ) (η T) = _
          rw [U.map_comp, hg2, map_mul, hm2, U.map_q]) }
  refine ⟨{ Ξ := Ξ, i := iN, η := η, map_η := fun {T T'} φ => hm2 T T' φ, γ := γN, iγ := ?_, γη := hg2, univ := ?_ }, ?_⟩
  · ext T
    exact hg1 T
  · intro T t φ a
    exact hu T t φ a
  · intro T
    exact hP T (g T) (hg1 T) (hg2 T)

end GlobalTheory.CompanionTheory.LineUniv
end

section


theorem _root_.GlobalTheory.T.block_determinant_law : PositivityTheory.RgEis.BdetLaw := by
  first | exact @GlobalTheory.CompanionTheory.RgEis.bdetLaw | exact GlobalTheory.CompanionTheory.RgEis.bdetLaw | (intros; apply GlobalTheory.CompanionTheory.RgEis.bdetLaw <;> assumption)
end

section


theorem _root_.GlobalTheory.T.extension_law : PositivityTheory.RgEis.ExtLaw := by
  first | exact @GlobalTheory.CompanionTheory.RgEisExt.extLaw | exact GlobalTheory.CompanionTheory.RgEisExt.extLaw | (intros; apply GlobalTheory.CompanionTheory.RgEisExt.extLaw <;> assumption)
end

section


theorem _root_.GlobalTheory.T.parabolic_law_of_block_det : PositivityTheory.RgEis.BdetLaw → PositivityTheory.RgEis.ExtLaw → PositivityTheory.RgEis.GrpTop → PositivityTheory.RgEis.ParLaw := by
  first | exact @GlobalTheory.CompanionTheory.RgEisPar.parLaw | exact GlobalTheory.CompanionTheory.RgEisPar.parLaw | (intros; apply GlobalTheory.CompanionTheory.RgEisPar.parLaw <;> assumption)
end

section


theorem _root_.GlobalTheory.T.general_linear_topological_group : PositivityTheory.RgEis.GrpTop := by
  first | exact @GlobalTheory.CompanionTheory.RgEisTop.grpTop | exact GlobalTheory.CompanionTheory.RgEisTop.grpTop | (intros; apply GlobalTheory.CompanionTheory.RgEisTop.grpTop <;> assumption)
end

section


theorem _root_.GlobalTheory.T.siegel_induction_from_gallery : PositivityTheory.RgEis.Gallery → PositivityTheory.RgEis.Transfer → PositivityTheory.RgEis.Twist → PositivityTheory.RgEis.GrpTop → PositivityTheory.RgEis.ParLaw → PositivityTheory.RgEis.LeviS → PositivityTheory.RgEis.LeviQ → PositivityTheory.RgEis.ConvGrOf → PositivityTheory.RgEis.ConvU → PositivityTheory.RgEis.SgStep := by
  first | exact @GlobalTheory.CompanionTheory.RgEis.sgStep | exact GlobalTheory.CompanionTheory.RgEis.sgStep | (intros; apply GlobalTheory.CompanionTheory.RgEis.sgStep <;> assumption)
end

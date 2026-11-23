module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle547
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle007
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle014
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle548
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
public import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle016
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.EtaleLie

variable {S : Scheme.{0}}

theorem fst_spMap_epsScaleR {R' : Type} [CommRing R'] (c : R') :
    spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ spMap (epsScaleR c) =
      spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact RingHom.ext fun r => TrivSqZeroExt.fst_map _ r

theorem existsUnique_dual_lift {R' : Type} [CommRing R'] {A B : Over S} [GrpObj A] [GrpObj B] (ψ : A ⟶ B)
    [IsMonHom ψ] [Etale ψ.left] (x : Sp R' ⟶ S) (h : Sp (DualNumber R') ⟶ B.left)
    (hh : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ h = (1 : Over.mk x ⟶ B).left) :
    ∃! l : Sp (DualNumber R') ⟶ A.left,
      spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ l = (1 : Over.mk x ⟶ A).left ∧ l ≫ ψ.left = h := by
  let π : CommRingCat.of (DualNumber R') ⟶ CommRingCat.of R' :=
    CommRingCat.ofHom (TrivSqZeroExt.fstHom R' R' R').toRingHom
  have hπ : Function.Surjective π := fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have hsq : ∀ a b : DualNumber R', a.fst = 0 → b.fst = 0 → a * b = 0 := fun a b ha hb => by
    ext <;> simp [ha, hb]
  have hnil : IsNilpotent (RingHom.ker π.hom) :=
    ⟨2, by
      rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
      exact fun a ha b hb => hsq a b ha hb⟩
  refine GlobalTheory.existsUnique_lift_of_etale_of_surjective ψ.left π hπ hnil _ h ?_
  show (1 : Over.mk x ⟶ A).left ≫ ψ.left = spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ h
  rw [hh]
  exact congrArg (·.left) (MonObj.one_comp ψ)

theorem lie_of_etale : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (M : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b M s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (act' : OActN D.O A') (ψ : o.A ⟶ A') (Ga : Type) [Group Ga] (ρ : Ga → (o.A.left ⟶ o.A.left)), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover Ga ρ ψ.left → (∀ c' : D.O, o.act.act c' ≫ ψ = ψ ≫ act'.act c') → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ S), x ≫ s = spMap β → ∀ v : epsPtR x ⟶ A', IsTanScal act' x (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) v → ∃ w : Fin D.a → (epsPtR x ⟶ A'), (∀ i, ∀ c : 𝓞 D.F, IsTanScal act' x (algebraMap (𝓞 D.F) D.O c) (β (b.t i c)) (w i)) ∧ v = (List.ofFn w).prod) ∧ (∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (β : R →+* κ), x ≫ s = spMap β → ∀ i, LieMult (act'.toF D) x (β.comp (b.t i)) D.m) := by
  intro p _ D R _ b M S s o A' _ _ act' ψ Ga _ ρ _hab hψ hG hact
  haveI := hψ
  haveI : Etale ψ.left := hG.etale
  refine ⟨?_, ?_⟩
  · intro R' _ β x hx v hv
    obtain ⟨l, ⟨hl₁, hl₂⟩, -⟩ := existsUnique_dual_lift ψ x v.left hv.1
    let u : epsPtR x ⟶ o.A := Over.homMk l (by
      show l ≫ o.A.hom = _
      rw [← Over.w ψ, ← Category.assoc, hl₂]; exact Over.w v)
    have hu : IsTanScal o.act x (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) u := by
      refine ⟨hl₁, ?_⟩
      have hh : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ (spMap (epsScaleR (β b.ρ)) ≫ v.left) =
          (1 : Over.mk x ⟶ A').left := by
        rw [← Category.assoc, fst_spMap_epsScaleR, hv.1]
      haveI := o.act.hom (algebraMap (𝓞 D.F) D.O D.ω)
      refine (existsUnique_dual_lift ψ x _ hh).unique ⟨?_, ?_⟩ ⟨?_, ?_⟩
      · show _ ≫ l ≫ (o.act.act _).left = _
        rw [← Category.assoc, hl₁]
        have e : ((1 : Over.mk x ⟶ o.A) ≫ o.act.act (algebraMap (𝓞 D.F) D.O D.ω)).left = (1 : Over.mk x ⟶ o.A).left :=
          congrArg Over.Hom.left (MonObj.one_comp _)
        exact e
      · show (l ≫ (o.act.act _).left) ≫ ψ.left = _
        rw [Category.assoc, ← Over.comp_left, hact, Over.comp_left, ← Category.assoc, hl₂, ← hv.2]
        rfl
      · show _ ≫ spMap _ ≫ l = _
        rw [← Category.assoc, fst_spMap_epsScaleR, hl₁]
      · show (spMap _ ≫ l) ≫ ψ.left = _
        rw [Category.assoc, hl₂]
    obtain ⟨w, hw, hvw⟩ := o.lie R' β x hx u hu
    refine ⟨fun i => w i ≫ ψ, fun i c => ⟨?_, ?_⟩, ?_⟩
    · show _ ≫ (w i).left ≫ ψ.left = _
      rw [← Category.assoc, (hw i c).1]
      have e : ((1 : Over.mk x ⟶ o.A) ≫ ψ).left = (1 : Over.mk x ⟶ A').left :=
        congrArg Over.Hom.left (MonObj.one_comp ψ)
      exact e
    · show ((w i ≫ ψ) ≫ act'.act _).left = spMap _ ≫ (w i).left ≫ ψ.left
      rw [Category.assoc, ← hact, ← Category.assoc, Over.comp_left, (hw i c).2, Category.assoc]
    · apply Over.OverMorphism.ext
      rw [← GlobalTheory.LieEtale.ofFn_prod_comp ψ w, ← hvw]
      exact hl₂.symm
  · intro κ _ _ x β hx i
    exact (GlobalTheory.LieEtale.lieMult_iff_of_etale (𝓞 D.F) S o.A A' ψ (o.act.toF D) (act'.toF D) hψ hG.etale
      (fun c => hact _) κ x (β.comp (b.t i)) D.m).mp (o.lieRank κ x β hx i)

end GlobalTheory.UPel.HT.EtaleLie
end
end

section

noncomputable section

namespace GlobalTheory.UPel.HT.HeckeAd

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

variable {S : Scheme.{0}} {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]

def heckeSubA {b : Base D R} {M : ℕ} {s : S ⟶ Sp R} (o : Obj b M s) (f : D.La →+ D.La) (N : ℕ) :
    Subgroup (𝟙_ (Over S) ⟶ o.A) where
  carrier := {h | ∃ x, h = o.eta (N • f x)}
  one_mem' := ⟨0, by rw [map_zero, smul_zero, eta_zero]⟩
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, by rw [map_add (f := _), smul_add, o.eta_add]⟩
  inv_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨-x, by rw [map_neg, smul_neg, eta_neg]⟩

theorem mem_heckeSubA {b : Base D R} {M : ℕ} {s : S ⟶ Sp R} (o : Obj b M s) (f : D.La →+ D.La) (N : ℕ)
    (x : D.La) : o.eta (N • f x) ∈ heckeSubA o f N := ⟨x, rfl⟩

theorem eta_pow {b : Base D R} {M : ℕ} {s : S ⟶ Sp R} (o : Obj b M s) (n : ℕ) (z : D.La) :
    (o.eta z) ^ n = o.eta (n • z) := by
  induction n with
  | zero => rw [pow_zero, zero_smul, eta_zero]
  | succ n ih => rw [pow_succ, ih, succ_nsmul, o.eta_add]

theorem pow_eq_one_of_mem {b : Base D R} {N k : ℕ} {s : S ⟶ Sp R} (o : Obj b (N * k) s) (f : D.La →+ D.La)
    (h : 𝟙_ (Over S) ⟶ o.A) (hh : h ∈ heckeSubA o f N) : h ^ k = 1 := by
  obtain ⟨x, rfl⟩ := hh
  rw [eta_pow, smul_smul, show k * N = N * k from mul_comm _ _, o.eta_ker]

theorem act_mem {b : Base D R} {N k : ℕ} {s : S ⟶ Sp R} (o : Obj b (N * k) s) (f : D.La →+ D.La)
    (hf : ∀ (a : D.O) (x : D.La), ∃ z, f (a • x) = a • f x + (N * k) • z) (a : D.O)
    (h : 𝟙_ (Over S) ⟶ o.A) (hh : h ∈ heckeSubA o f N) : h ≫ o.act.act a ∈ heckeSubA o f N := by
  obtain ⟨x, rfl⟩ := hh
  obtain ⟨z, hz⟩ := hf a x
  refine ⟨a • x, ?_⟩
  rw [hz, smul_add, o.eta_add, smul_smul, show N * (N * k) = (N * k) * N from mul_comm _ _, ← smul_smul,
    o.eta_ker, _root_.mul_one, ← o.eta_lin, smul_comm]

theorem heckeSubA_finite_free (b : Base D R) (f : D.La →+ D.La) (k N : ℕ) (hk : 0 < k) (hN : 0 < N)
    (hkp : k.Coprime p) (hNp : N.Coprime p) (s : S ⟶ Sp R) (o : Obj b (N * k) s) :
    Finite (heckeSubA o f N) ∧ ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (h : 𝟙_ (Over S) ⟶ o.A),
      h ∈ heckeSubA o f N → toUnit (Over.mk x) ≫ h = 1 → h = 1 := by
  refine ⟨?_, ?_⟩
  · haveI := D.finLa
    let K : Submodule ℤ D.La := LinearMap.range ((k : ℤ) • LinearMap.id)
    haveI : Finite (D.La ⧸ K) := by
      apply Module.finite_of_fg_torsion
      intro q
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective K q
      refine ⟨⟨(k : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hk.ne')⟩, ?_⟩
      show (k : ℤ) • (Submodule.Quotient.mk y : D.La ⧸ K) = 0
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact ⟨y, by simp⟩
    let σ := Function.surjInv (Submodule.Quotient.mk_surjective K)
    refine Finite.of_surjective
      (fun q : D.La ⧸ K => (⟨o.eta (N • f (σ q)), mem_heckeSubA o f N _⟩ : heckeSubA o f N)) ?_
    rintro ⟨h, x, rfl⟩
    refine ⟨Submodule.Quotient.mk x, Subtype.ext ?_⟩
    have e : Submodule.Quotient.mk (σ (Submodule.Quotient.mk x)) = (Submodule.Quotient.mk x : D.La ⧸ K) :=
      Function.surjInv_eq _ _
    rw [Submodule.Quotient.eq] at e
    obtain ⟨z, hz⟩ := e
    have hz' : σ (Submodule.Quotient.mk x) = x + k • z := by
      simp only [LinearMap.smul_apply, LinearMap.id_apply, natCast_zsmul] at hz
      rw [hz]; abel
    show o.eta (N • f (σ (Submodule.Quotient.mk x))) = o.eta (N • f x)
    rw [hz', map_add (f := _), map_nsmul, smul_add, smul_smul, o.eta_add, o.eta_ker, _root_.mul_one]
  · intro κ _ _ x h hh h1
    obtain ⟨x0, rfl⟩ := hh
    have hβ : x ≫ s = spMap (Spec.preimage (x ≫ s)).hom := (Spec.map_preimage _).symm
    obtain ⟨I, hI⟩ := o.geom κ x _ hβ
    have h2 : I.ev (N * k) (N • f x0) = 1 := by rw [← hI]; exact h1
    obtain ⟨y, hy⟩ := (I.ker (N * k) (Nat.mul_pos hN hk) (Nat.Coprime.mul_left hNp hkp) _).1 h2
    rw [hy, o.eta_ker]

end GlobalTheory.UPel.HT.HeckeAd
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.UPel.HT.TateCompare

variable {p : ℕ} [Fact p.Prime] {D : Datum p}
variable {k : Type} [Field k] {Q : Type} [Group Q] {act : D.O → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}

theorem ev_zsmul (I : TateIsoO D k Q act e) (n : ℕ) (c : ℤ) (x : D.La) : I.ev n (c • x) = I.ev n x ^ c := by
  let φ : Multiplicative D.La →* Q := MonoidHom.mk' (fun y => I.ev n y.toAdd) (fun a b => I.add n _ _)
  exact map_zpow φ (Multiplicative.ofAdd x) c

theorem ev_eq_iff (I : TateIsoO D k Q act e) {n : ℕ} (hn : 0 < n) (hc : n.Coprime p) {x y : D.La} :
    I.ev n x = I.ev n y ↔ ∃ z, x = y + n • z := by
  constructor
  · intro h
    have h₁ : I.ev n y * I.ev n (x - y) = I.ev n y * 1 := by
      rw [← I.add, add_sub_cancel, h, _root_.mul_one]
    obtain ⟨z, hz⟩ := (I.ker n hn hc _).1 (mul_left_cancel h₁)
    exact ⟨z, by rw [← hz, add_sub_cancel]⟩
  · rintro ⟨z, rfl⟩
    exact I.ev_add_nsmul hn hc _ _

theorem exists_lift (I₁ I₂ : TateIsoO D k Q act e) (n : ℕ) :
    ∃ g : D.La →+ D.La, 0 < n → n.Coprime p → ∀ y, I₁.ev n (g y) = I₂.ev n y := by
  by_cases h : 0 < n ∧ n.Coprime p
  swap
  · exact ⟨0, fun h₁ h₂ => (h ⟨h₁, h₂⟩).elim⟩
  obtain ⟨hn, hc⟩ := h
  have := D.freeLa
  let b := Module.Free.chooseBasis ℤ D.La
  have hpre : ∀ y, ∃ x, I₁.ev n x = I₂.ev n y := fun y =>
    (I₁.onto n hn hc _).1 ((I₂.onto n hn hc _).2 ⟨y, rfl⟩)
  choose f hf using hpre
  let g : D.La →ₗ[ℤ] D.La := b.constr ℤ (fun i => f (b i))
  refine ⟨g.toAddMonoidHom, fun _ _ y => ?_⟩
  show I₁.ev n (g y) = I₂.ev n y
  have hy : y ∈ Submodule.span ℤ (Set.range b) := by rw [b.span_eq]; trivial
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    simp only [g, Module.Basis.constr_basis, hf]
  | zero =>
    rw [map_zero, (I₁.ker n hn hc 0).2 ⟨0, (smul_zero _).symm⟩, (I₂.ker n hn hc 0).2 ⟨0, (smul_zero _).symm⟩]
  | add x y _ _ hx hy => rw [map_add (f := _), I₁.add, I₂.add, hx, hy]
  | smul c x _ hx => rw [map_zsmul, ev_zsmul, ev_zsmul, hx]

theorem exists_mult (I₁ I₂ : TateIsoO D k Q act e) (n : ℕ) :
    ∃ u : ℕ, 0 < n → n.Coprime p → I₁.ζ n ^ u = I₂.ζ n := by
  by_cases h : 0 < n ∧ n.Coprime p
  swap
  · exact ⟨0, fun h₁ h₂ => (h ⟨h₁, h₂⟩).elim⟩
  obtain ⟨hn, hc⟩ := h
  have : NeZero n := ⟨hn.ne'⟩
  have h₁ : IsPrimitiveRoot ((I₁.ζ n : kˣ) : k) n := IsPrimitiveRoot.coe_units_iff.2 (I₁.ζ_prim n hn hc)
  have h₂ : ((I₂.ζ n : kˣ) : k) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, (I₂.ζ_prim n hn hc).pow_eq_one, Units.val_one]
  obtain ⟨u, -, hu⟩ := h₁.eq_pow_of_pow_eq_one h₂
  exact ⟨u, fun _ _ => Units.ext (by rw [Units.val_pow_eq_pow_val, hu])⟩

end GlobalTheory.UPel.HT.TateCompare
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.EtLev

noncomputable section

namespace GlobalTheory.UPel.HT.EtLev

theorem exists_rep_pow_of_le : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r r' : ℕ), r ≤ r' → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (H : Over S) (i : H ⟶ o.A), IsFinite H.hom → Etale H.hom → (∀ c ∈ w0 ^ r', i ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → (∀ (T : Over S) (x : T ⟶ o.A), (∀ c ∈ w0 ^ r', x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃! y : T ⟶ H, y ≫ i = x) → ∃ (K : Over S) (κ : K ⟶ o.A), IsFinite K.hom ∧ Etale K.hom ∧ (∀ c ∈ w0 ^ r, κ ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) ∧ ∀ (T : Over S) (x : T ⟶ o.A), (∀ c ∈ w0 ^ r, x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃! y : T ⟶ K, y ≫ κ = x := by
  intro p _ D R _ b N w0 r r' hrr' S _ s o H i hHf hHe hi hH
  haveI := hHf
  haveI := hHe
  have hmh := o.act.hom

  let kil : ∀ (T : Over S) (x : T ⟶ o.A), Ideal (𝓞 D.F) := fun T x =>
    { carrier := {c | x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1}
      add_mem' := by
        intro a c ha hc
        simp only [Set.mem_ofPred_eq] at ha hc ⊢
        rw [map_add (f := _), o.act.add, comp_mul, ha, hc, _root_.mul_one]
      zero_mem' := by
        simp only [Set.mem_ofPred_eq, map_zero]
        have h0 := o.act.add 0 0
        rw [add_zero] at h0
        have h1 : x ≫ o.act.act 0 = x ≫ o.act.act 0 * x ≫ o.act.act 0 := by rw [← comp_mul, ← h0]
        exact mul_eq_left.1 h1.symm
      smul_mem' := by
        intro a c hc
        simp only [Set.mem_ofPred_eq, smul_eq_mul] at hc ⊢
        rw [map_mul, o.act.mul, ← Category.assoc, hc, one_comp] }
  obtain ⟨s0, hs0⟩ := IsNoetherian.noetherian (w0 ^ r)
  have hgen : ∀ (T : Over S) (x : T ⟶ o.A),
      (∀ c ∈ w0 ^ r, x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) ↔
        ∀ c : s0, x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
    intro T x
    constructor
    · intro h c
      exact h c (hs0 ▸ Submodule.subset_span c.2)
    · intro h c hc
      have hle : Submodule.span (𝓞 D.F) (s0 : Set (𝓞 D.F)) ≤ kil T x :=
        Submodule.span_le.2 fun c hc => h ⟨c, hc⟩
      rw [← hs0] at hc
      exact hle hc
  have hle : w0 ^ r' ≤ w0 ^ r := Ideal.pow_le_pow_right hrr'
  have hmono : ∀ (T : Over S) (y y' : T ⟶ H), y ≫ i = y' ≫ i → y = y' := by
    intro T y y' e
    have hk : ∀ c ∈ w0 ^ r', (y' ≫ i) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := fun c hc => by
      rw [Category.assoc, hi c hc, comp_one]
    exact (hH T _ hk).unique e rfl
  have hf0 : ∀ c : s0, ∃ f : H ⟶ H, f ≫ i = i ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) := by
    intro c
    refine (hH H _ fun c' hc' => ?_).exists
    rw [Category.assoc, ← o.act.mul, ← map_mul]
    exact hi _ (Ideal.mul_mem_right _ _ hc')
  choose f hf using hf0
  obtain ⟨e, he⟩ := (hH _ (1 : 𝟙_ (Over S) ⟶ o.A) fun c _ => one_comp _).exists
  have htr : ∀ (T : Over S) (h : T ⟶ H), (∀ c : s0, h ≫ f c = h ≫ toUnit H ≫ e) ↔
      ∀ c ∈ w0 ^ r, (h ≫ i) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
    intro T h
    rw [hgen]
    refine forall_congr' fun c => ⟨fun e1 => ?_, fun e1 => ?_⟩
    · have e2 := congrArg (· ≫ i) e1
      simp only [Category.assoc, hf, he, comp_one] at e2
      rw [Category.assoc]
      exact e2
    · apply hmono
      simp only [Category.assoc, hf, he, comp_one]
      rw [← Category.assoc]
      exact e1
  obtain ⟨U, hUc, hU⟩ := GlobalTheory.LevCover.ClopenCond.forall_finite (T := H)
    (P := fun (c : s0) (T' : Over S) (h : T' ⟶ H) => h ≫ f c = h ≫ toUnit H ≫ e)
    fun c => GlobalTheory.LevCover.clopenCond_eq (f c) (toUnit H ≫ e)
  obtain ⟨K, iK, hKf, hKe, hiKm, hiK⟩ := GlobalTheory.LevCover.exists_sub U hUc
  refine ⟨K, iK ≫ i, hKf, hKe, ?_, ?_⟩
  · exact (htr K iK).1 ((hU K iK).2 ((hiK K iK).2 ⟨𝟙 _, Category.id_comp _⟩))
  · intro T x hx
    have hx' : ∀ c ∈ w0 ^ r', x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := fun c hc => hx c (hle hc)
    obtain ⟨y0, hy0, -⟩ := hH T x hx'
    have hr : Set.range y0.left ⊆ U := (hU T y0).1 ((htr T y0).2 (by rw [hy0]; exact hx))
    obtain ⟨y, hy⟩ := (hiK T y0).1 hr
    refine ⟨y, show y ≫ iK ≫ i = x by rw [← Category.assoc, hy, hy0], fun y' hy' => ?_⟩
    haveI := hiKm
    apply (cancel_mono iK).1
    apply hmono
    rw [Category.assoc, Category.assoc, hy', ← Category.assoc, hy, hy0]

end GlobalTheory.UPel.HT.EtLev
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.HTPullTan

open GlobalTheory.UPel.HT

theorem isTanScal_iff_of_left_eq : ∀ {O : Type} [Ring O] {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] (f : S' ⟶ S) (φ : A'.left ⟶ A.left) (act : GlobalTheory.UPel.HT.OActN O A) (act' : GlobalTheory.UPel.HT.OActN O A'), IsGrpPullback A' A f φ → (∀ c, (act'.act c).left ≫ φ = φ ≫ (act.act c).left) → ∀ {R' : Type} [CommRing R'] (x : Sp R' ⟶ S') (b : O) (c : R') (v : GlobalTheory.UPel.HT.epsPtR x ⟶ A') (v₀ : GlobalTheory.UPel.HT.epsPtR (x ≫ f) ⟶ A), v₀.left = v.left ≫ φ → (GlobalTheory.UPel.HT.IsTanScal act' x b c v ↔ GlobalTheory.UPel.HT.IsTanScal act (x ≫ f) b c v₀) := by
  intro O _ S S' A A' _ _ f φ a a' h hact R' _ x b c v v₀ hv₀
  obtain ⟨e₀, he₀⟩ := GlobalTheory.LiePull.exists_pushEquiv h (Over.mk x) (x ≫ f) rfl
  have one : (1 : Over.mk (x ≫ f) ⟶ A).left = (1 : Over.mk x ⟶ A').left ≫ φ := by
    rw [← he₀, map_one]
  have sc : spMap (epsScaleR c) ≫ spMap (algebraMap R' (DualNumber R')) = spMap (algebraMap R' (DualNumber R')) := by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  have fs : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ spMap (algebraMap R' (DualNumber R')) = 𝟙 _ := by
    refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
    ext a
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  have hR : ∀ (u w : epsPtR x ⟶ A') (u₀ w₀ : epsPtR (x ≫ f) ⟶ A), u₀.left = u.left ≫ φ → w₀.left = w.left ≫ φ →
      (u.left = spMap (epsScaleR c) ≫ w.left ↔
      u₀.left = spMap (epsScaleR c) ≫ w₀.left) := fun u w u₀ w₀ hu hw => by
    rw [hu, hw]
    refine ⟨fun E => by rw [E]; exact Category.assoc _ _ _, fun E => h.1.hom_ext (E.trans (Category.assoc _ _ _).symm) ?_⟩
    refine (Over.w u).trans (Eq.symm ((Category.assoc _ _ _).trans ?_))
    refine (congrArg (spMap (epsScaleR c) ≫ ·) (Over.w w)).trans ?_
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ x) sc)
  refine and_congr ?_ ?_
  · rw [one, hv₀]
    refine ⟨fun E => by rw [← E]; exact (Category.assoc _ _ _).symm,
      fun E => h.1.hom_ext ((Category.assoc _ _ _).trans E) ?_⟩
    refine ((Category.assoc _ _ _).trans ?_).trans (Over.w (1 : Over.mk x ⟶ A')).symm
    refine (congrArg (spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ ·) (Over.w v)).trans ?_
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x) fs).trans (Category.id_comp _))
  · refine hR _ _ _ _ ?_ hv₀
    rw [Over.comp_left, Over.comp_left, hv₀, Category.assoc, Category.assoc, hact]

end GlobalTheory.HTPullTan
end

section

noncomputable section

namespace GlobalTheory.UPel.Sm.KSCount

open Module GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model

section Gen

variable {k H O : Type*} [Field k] [AddCommGroup H] [Module k H] [Ring O]

theorem ksDim_finrank [FiniteDimensional k H] (ρ : O →+* Module.End k H) (φ : LinearMap.BilinForm k H)
    (Fil Z : Submodule k H) : KSDim ρ φ Fil Z (finrank k ((ksSub ρ φ Fil Z).map (cls Fil))) := by
  set M := (ksSub ρ φ Fil Z).map (cls Fil) with hM
  let b := Module.finBasis k M
  have hb : ∀ i, ∃ f ∈ ksSub ρ φ Fil Z, cls Fil f = (b i : Fil →ₗ[k] H ⧸ Fil) := fun i => (b i).2
  choose f hf hfb using hb
  have key : ∀ (g : H →ₗ[k] H) (c : Fin (finrank k M) → k),
      (∀ x ∈ Fil, g x - ∑ i, c i • f i x ∈ Fil) ↔
        cls Fil g = ∑ i, c i • (b i : Fil →ₗ[k] H ⧸ Fil) := fun g c => by
    simp_rw [← hfb]

    simp only [← map_smul, ← map_sum, cls_eq_iff, LinearMap.sum_apply, LinearMap.smul_apply]
  refine ⟨f, hf, fun g hg => ?_⟩
  let m : M := ⟨cls Fil g, g, hg, rfl⟩
  have hsum : ∀ c : Fin (finrank k M) → k, (cls Fil g = ∑ i, c i • (b i : Fil →ₗ[k] H ⧸ Fil)) ↔
      m = ∑ i, c i • b i := fun c => by
    rw [Subtype.ext_iff]; simp [m]
  refine ⟨b.equivFun m, (key g _).2 ((hsum _).2 ?_), fun c hc => ?_⟩
  · rw [← b.equivFun_symm_apply, LinearEquiv.symm_apply_apply]
  · have := (hsum c).1 ((key g c).1 hc)
    rw [this, ← b.equivFun_symm_apply, LinearEquiv.apply_symm_apply]

theorem finrank_map_add_ker {M N : Type*} [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    [AddCommGroup N] [Module k N] (p : Submodule k M) (f : M →ₗ[k] N) :
    finrank k (p.map f) + finrank k (LinearMap.ker (f ∘ₗ p.subtype)) = finrank k p := by
  rw [← LinearMap.finrank_range_add_finrank_ker (f ∘ₗ p.subtype), LinearMap.range_comp,
    Submodule.range_subtype]

end Gen

end GlobalTheory.UPel.Sm.KSCount
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.quasiIso_hypercohomology_bijective : GlobalTheory.EtC.A1 := by
  first | (exact @GlobalTheory.EtC.quasiIso_hypercohomology_bijective') | (exact GlobalTheory.EtC.quasiIso_hypercohomology_bijective') | (intros; apply GlobalTheory.EtC.quasiIso_hypercohomology_bijective'  <;> assumption)
end

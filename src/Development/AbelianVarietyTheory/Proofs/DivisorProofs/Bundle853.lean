module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle593
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle250
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle822
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
public import Mathlib.NumberTheory.Padics.RingHoms
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle826
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerSpaceDimFiniteGLLeOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle827
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

noncomputable section

namespace GlobalTheory.MuLattice

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] {ε : PreTilt O p}

def muMap (hε : IsPrimitiveSystem ε) (a : Ainf p O) : TDual (PDivGroup.mu p O) where
  toFun t := ofPadic p O ((epsEquiv hε).symm t) * a
  map_add' s t := by rw [map_add (f := _), map_add (f := _), add_mul]
  map_smul' c t := by
    rw [map_smul, smul_eq_mul, map_mul, mul_assoc]; rfl

theorem muMap_apply (hε : IsPrimitiveSystem ε) (a : Ainf p O) (t) :
    muMap hε a t = ofPadic p O ((epsEquiv hε).symm t) * a := rfl

theorem epsEquiv_symm_eps (hε : IsPrimitiveSystem ε) : (epsEquiv hε).symm (epsTate hε) = 1 := by
  rw [LinearEquiv.symm_apply_eq]
  exact (one_smul ℤ_[p] (epsTate hε)).symm

theorem muMap_mem (hε : IsPrimitiveSystem ε) (hμ : ∀ n, ghost p O n (Sandwich.mu ε) = 0)
    (a : Ainf p O) : muMap hε (Sandwich.mu ε * a) ∈ latt (PDivGroup.mu p O) := fun n =>
  ⟨0, fun t => by
    rw [muMap_apply, ghost_mul, ghost_mul, hμ, zero_mul, mul_zero, LinearMap.zero_apply]⟩

def toLatt (hε : IsPrimitiveSystem ε) (hμ : ∀ n, ghost p O n (Sandwich.mu ε) = 0) :
    Ainf p O →ₗ[Ainf p O] latt (PDivGroup.mu p O) where
  toFun a := ⟨muMap hε (Sandwich.mu ε * a), muMap_mem hε hμ a⟩
  map_add' a b := by
    ext t
    simp only [muMap_apply, Submodule.coe_add, LinearMap.add_apply]
    ring_nf
  map_smul' c a := by
    ext t
    simp only [muMap_apply, Submodule.coe_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring_nf

theorem toLatt_eps (hε : IsPrimitiveSystem ε) (hμ : ∀ n, ghost p O n (Sandwich.mu ε) = 0)
    (a : Ainf p O) : (toLatt hε hμ a).1 (epsTate hε) = Sandwich.mu ε * a := by
  change ofPadic p O ((epsEquiv hε).symm (epsTate hε)) * _ = _
  rw [epsEquiv_symm_eps, map_one, one_mul]

theorem latt_mu_equiv : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∃ e : latt (PDivGroup.mu p O) ≃ₗ[Ainf p O] Ainf p O, ∀ y, Sandwich.mu ε * e y = y.1 (epsTate hε) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε
  have hμ : ∀ n, ghost p O n (Sandwich.mu ε) = 0 :=
    (GlobalTheory.T.ainfGhostThetaFrobIter_values_xi_mu_padic p C v O hv ε hε).2.2.1
  have hdom := GlobalTheory.ainf_isDomain_and_mu_ne_zero p C v O hv ε (by simpa [zeta] using hε 1)
  haveI := hdom.1
  have hbij : Function.Bijective (toLatt hε hμ) := by
    constructor
    · intro a b hab
      have h := congrArg (fun y : latt (PDivGroup.mu p O) => y.1 (epsTate hε)) hab
      simp only [toLatt_eps] at h
      exact mul_left_cancel₀ hdom.2 h
    · intro y
      have hg : ∀ n, ghost p O n (y.1 (epsTate hε)) = 0 := fun n => by
        obtain ⟨x, hx⟩ := y.2 n
        rw [hx, Subsingleton.elim (hodgeTate (PDivGroup.mu p O) (epsTate hε)) 0, map_zero]
      obtain ⟨a, ha⟩ := GlobalTheory.T.ainfTeichmullerMinusOne_dvd_of_ghost_components_zero p C v O hv ε hε _ hg
      refine ⟨a, Subtype.ext (LinearMap.ext fun t => ?_)⟩
      obtain ⟨c, rfl⟩ := (epsEquiv hε).surjective t
      change ofPadic p O ((epsEquiv hε).symm (epsEquiv hε c)) * (Sandwich.mu ε * a) = y.1 (epsEquiv hε c)
      rw [LinearEquiv.symm_apply_apply, ← ha]
      have hc : epsEquiv hε c = c • epsTate hε := rfl
      rw [hc, LinearMap.map_smulₛₗ, smul_eq_mul]
  refine ⟨(LinearEquiv.ofBijective _ hbij).symm, fun y => ?_⟩
  have h := toLatt_eps hε hμ ((LinearEquiv.ofBijective _ hbij).symm y)
  rw [← h]
  congr 2
  exact (LinearEquiv.ofBijective _ hbij).apply_symm_apply y

end GlobalTheory.MuLattice
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

namespace GlobalTheory.UPel.HT


open Polynomial in
theorem exists_idem_crys : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (C : Type) [CommRing C] (tR : R →+* C) (H : Type 1) [AddCommGroup H] [Module C H] (ρ : D.O →+* Module.End C H) (φ : LinearMap.BilinForm C H), (∀ (c : D.O) x y, φ (ρ c x) y = φ x (ρ (D.star c).unop y)) → ∃ e : Module.End C H, e * e = e ∧ (∀ c, ρ c * e = e * ρ c) ∧ (∀ x y, φ (e x) y = φ x (y - e y)) ∧ (∀ x, ρ (algebraMap (𝓞 D.F) D.O D.ω) (e x) = tR b.ρ • e x) ∧ (∃ v : C, IsUnit v ∧ ∀ x, e x = 0 → ρ (algebraMap (𝓞 D.F) D.O D.ω) x - tR b.ρ • x = v • x) ∧ ∀ N : Submodule C H, (∀ (c : D.O), ∀ x ∈ N, ρ c x ∈ N) → ∀ x ∈ N, e x ∈ N := by
  intro p _ D R _ b C _ tR H _ _ ρ φ hφ

  have hroot : tR b.ρ ^ 2 - (D.tr : C) * tR b.ρ + (D.nm : C) = 0 := by
    have := congrArg tR b.ρ_root
    simpa only [map_sub, map_add (f := _), map_mul, map_pow, map_intCast, map_zero] using this
  have hu2 : (tR b.ρ - ((D.tr : C) - tR b.ρ)) ^ 2 = ((D.tr ^ 2 - 4 * D.nm : ℤ) : C) := by
    push_cast; linear_combination 4 * hroot
  have hunit : IsUnit (tR b.ρ - ((D.tr : C) - tR b.ρ)) := by
    have hk : (D.tr ^ 2 - 4 * D.nm : ℤ) = -((D.tr ^ 2 - 4 * D.nm).natAbs : ℤ) := by
      rw [Int.ofNat_natAbs_of_nonpos (le_of_lt D.disc_neg)]; ring
    have hcop : (D.tr ^ 2 - 4 * D.nm).natAbs.Coprime p := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (Fact.out)]
      intro h; apply D.disc_p; exact Int.natCast_dvd.mpr h
    have h1 := (b.unit _ hcop).map tR
    have : IsUnit ((tR b.ρ - ((D.tr : C) - tR b.ρ)) ^ 2) := by
      rw [hu2, hk]; push_cast; simpa using h1.neg
    exact (isUnit_pow_iff two_ne_zero).mp this
  obtain ⟨uu, huu⟩ := hunit
  have hui : (↑uu⁻¹ : C) * (tR b.ρ - ((D.tr : C) - tR b.ρ)) = 1 := by rw [← huu]; exact uu.inv_mul

  set ui : C := (↑uu⁻¹ : C) with hui_def
  set r : C := tR b.ρ with hr_def
  set W : Module.End C H := ρ (algebraMap (𝓞 D.F) D.O D.ω) with hW_def

  have hωF : D.ω * D.ω - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F) = 0 := by
    linear_combination D.ω * D.tr_eq - D.nm_eq
  have hWrel : W * W - (D.tr : Module.End C H) * W + (D.nm : Module.End C H) = 0 := by
    have := congrArg (fun z => ρ (algebraMap (𝓞 D.F) D.O z)) hωF
    simpa only [map_sub, map_add (f := _), map_mul, map_intCast, map_zero] using this
  have hWx : ∀ x, W (W x) = (D.tr : C) • W x - (D.nm : C) • x := by
    intro x
    have := congrArg (fun f : Module.End C H => f x) hWrel
    simp only [LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply, Module.End.intCast_apply,
      LinearMap.zero_apply] at this
    rw [← Int.cast_smul_eq_zsmul C, ← Int.cast_smul_eq_zsmul C] at this
    rw [← sub_eq_zero, ← this]; abel

  have hcomm : ∀ c : D.O, ∀ x, ρ c (W x) = W (ρ c x) := by
    intro c x
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, Algebra.commutes]
  have hbar : D.bar D.ω = (D.tr : 𝓞 D.F) - D.ω := by rw [← D.tr_eq]; ring
  have hWadj : ∀ x y, φ (W x) y = φ x ((D.tr : C) • y - W y) := by
    intro x y
    rw [hW_def, hφ, D.star_F, MulOpposite.unop_op, hbar, map_sub, map_intCast, map_sub, map_intCast,
      LinearMap.sub_apply, Module.End.intCast_apply, ← Int.cast_smul_eq_zsmul C]
  refine ⟨ui • (W - ((D.tr : C) - r) • 1), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext x
    simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply, map_smul,
      map_sub, hWx]
    match_scalars
    all_goals first | linear_combination ui * hui | linear_combination (-ui * ((D.tr:C) - r)) * hui - ui ^ 2 * hroot | linear_combination (ui * ((D.tr:C) - r)) * hui + ui ^ 2 * hroot | linear_combination (-ui * ((D.tr:C) - r)) * hui + ui ^ 2 * hroot | linear_combination (ui * ((D.tr:C) - r)) * hui - ui ^ 2 * hroot
  · intro c; ext x
    simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply, map_smul,
      map_sub, hcomm]
  · intro x y
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply, map_smul, map_sub,
      LinearMap.smul_apply, LinearMap.sub_apply, hWadj, smul_eq_mul]
    linear_combination (φ x y) * hui
  · intro x
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply, map_smul, map_sub, hWx]
    match_scalars
    all_goals first | linear_combination (0:C) | linear_combination ui * hroot | linear_combination -ui * hroot
  · refine ⟨-(r - ((D.tr : C) - r)), by rw [← huu]; exact (Units.isUnit uu).neg, ?_⟩
    intro x hx
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply] at hx
    have h2 : W x - ((D.tr : C) - r) • x = 0 := by
      have := congrArg (fun z => (↑uu : C) • z) hx
      simpa [smul_smul, hui_def] using this
    rw [sub_eq_zero] at h2
    rw [h2]
    match_scalars
    ring
  · intro N hN x hx
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply]
    exact N.smul_mem _ (N.sub_mem (hN _ x hx) (N.smul_mem _ hx))

end GlobalTheory.UPel.HT
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.UPel.HT.MapComp

theorem lbIso_pull_comp {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {a : Y ⟶ X} (h : LBIso M (L.pull a)) (j : Z ⟶ Y)
    {a' : Z ⟶ X} (e : a' = j ≫ a) : LBIso (M.pull j) (L.pull a') :=
  LBIso.chartPull (Geo.Tor.chartPullPull M j j rfl) (Geo.Tor.chartPullSame L _ (fun _ => a) _ j fun _ => e) h

theorem isSquare_comp {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} {φ : G'.left ⟶ G.left}
    {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} {ψ : G''.left ⟶ G'.left} {ψ₂ : (G'' ⊗ G'').left ⟶ (G' ⊗ G').left}
    (h' : IsSquare ψ ψ₂) (h : IsSquare φ φ₂) : IsSquare (ψ ≫ φ) (ψ₂ ≫ φ₂) :=
  ⟨by rw [Category.assoc, h.1, ← Category.assoc, h'.1, Category.assoc],
    by rw [Category.assoc, h.2, ← Category.assoc, h'.2, Category.assoc]⟩

theorem isSquare_unique {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} {φ : G'.left ⟶ G.left}
    {a b : (G' ⊗ G').left ⟶ (G ⊗ G).left} (ha : IsSquare φ a) (hb : IsSquare φ b) : a = b := by
  apply pullback.hom_ext
  · exact ha.1.trans hb.1.symm
  · exact ha.2.trans hb.2.symm

theorem exists_isSquare {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
    (w : φ ≫ G.hom = G'.hom ≫ f) : ∃ φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left, IsSquare φ φ₂ :=
  ⟨_, congrArg (fun z => z.left) (lift_fst (pushPt w (fst G' G')) (pushPt w (snd G' G'))),
    congrArg (fun z => z.left) (lift_snd (pushPt w (fst G' G')) (pushPt w (snd G' G')))⟩

end GlobalTheory.UPel.HT.MapComp

namespace GlobalTheory.UPel.HT

open GlobalTheory.UPel.HT.MapComp

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

def MapComp.comp {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R}
    {o₁ : Obj b N s₁} {o₂ : Obj b N s₂} {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃}
    (m₁ : ObjMap o₁ o₂ f) (m₂ : ObjMap o₂ o₃ g) : ObjMap o₁ o₃ (f ≫ g) where
  φ := m₁.φ ≫ m₂.φ
  φ₂ := m₁.φ₂ ≫ m₂.φ₂
  cart := m₁.cart.comp m₂.cart
  sq := isSquare_comp m₁.sq m₂.sq
  act c := by rw [← Category.assoc, m₁.act, Category.assoc, m₂.act, Category.assoc]
  pol := LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) m₁.pol (lbIso_pull_comp m₂.pol m₁.φ₂ rfl)
  eta y := by rw [← Category.assoc, m₁.eta, Category.assoc, m₂.eta, Category.assoc]

theorem MapComp.cancel {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R}
    {o₁ : Obj b N s₁} {o₂ : Obj b N s₂} {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃}
    (m : ObjMap o₁ o₃ (f ≫ g)) (m₂ : ObjMap o₂ o₃ g) : Nonempty (ObjMap o₁ o₂ f) := by
  have w : m.φ ≫ o₃.A.hom = (o₁.A.hom ≫ f) ≫ g := by rw [m.cart.1.w, Category.assoc]
  set φ := m₂.cart.1.lift m.φ (o₁.A.hom ≫ f) w
  have hφ : φ ≫ m₂.φ = m.φ := m₂.cart.1.lift_fst _ _ _
  have hφ' : φ ≫ o₂.A.hom = o₁.A.hom ≫ f := m₂.cart.1.lift_snd _ _ _
  have n : IsGrpPullback o₁.A o₃.A (f ≫ g) (φ ≫ m₂.φ) := by rw [hφ]; exact m.cart
  obtain ⟨φ₂, sq⟩ := exists_isSquare hφ'
  have e : m.φ₂ = φ₂ ≫ m₂.φ₂ := isSquare_unique m.sq (hφ ▸ isSquare_comp sq m₂.sq)
  have hact : ∀ c, (o₁.act.act c).left ≫ φ = φ ≫ (o₂.act.act c).left := by
    intro c
    apply m₂.cart.1.hom_ext
    · rw [Category.assoc, hφ, m.act, Category.assoc, m₂.act, ← Category.assoc, hφ]
    · rw [Category.assoc, hφ', ← Category.assoc, Over.w, Category.assoc, Over.w, hφ']
  have heta : ∀ y, (o₁.eta y).left ≫ φ = f ≫ (o₂.eta y).left := by
    intro y
    apply m₂.cart.1.hom_ext
    · rw [Category.assoc, hφ, m.eta, Category.assoc, Category.assoc, m₂.eta]
    · rw [Category.assoc, hφ', ← Category.assoc, Over.w, Category.assoc, Over.w]
      show 𝟙 _ ≫ f = f ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]
  exact ⟨{ φ := φ
           φ₂ := φ₂
           cart := m₂.cart.cancel n hφ'
           sq := sq
           act := hact
           pol := LBIso.trans o₁.isLB (pull_isLB o₃.isLB _) (pull_isLB o₂.isLB _) m.pol
             (LBIso.symm (lbIso_pull_comp m₂.pol φ₂ e))
           eta := heta }⟩

theorem objMap_comp_cancel (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ)
    (S₁ S₂ S₃ : Scheme.{0}) (s₁ : S₁ ⟶ Sp R) (s₂ : S₂ ⟶ Sp R) (s₃ : S₃ ⟶ Sp R) (o₁ : Obj b N s₁) (o₂ : Obj b N s₂)
    (o₃ : Obj b N s₃) (f : S₁ ⟶ S₂) (g : S₂ ⟶ S₃) :
    (Nonempty (ObjMap o₁ o₂ f) → Nonempty (ObjMap o₂ o₃ g) → Nonempty (ObjMap o₁ o₃ (f ≫ g))) ∧
      (Nonempty (ObjMap o₁ o₃ (f ≫ g)) → Nonempty (ObjMap o₂ o₃ g) → Nonempty (ObjMap o₁ o₂ f)) :=
  ⟨fun ⟨m₁⟩ ⟨m₂⟩ => ⟨MapComp.comp m₁ m₂⟩, fun ⟨m⟩ ⟨m₂⟩ => MapComp.cancel m m₂⟩

end GlobalTheory.UPel.HT
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.HTLiftLie

theorem exists_factor_of_sq_zero {C C₀ k : Type} [CommRing C] [CommRing C₀] [Field k] (π : C →+* C₀)
    (hπ : Function.Surjective π) (hsq : RingHom.ker π ^ 2 = 0) (x : Sp k ⟶ Sp C) :
    ∃ ψ : C₀ →+* k, x = spMap ψ ≫ spMap π := by
  let φ : C →+* k := (Spec.preimage x).hom
  have hx : x = spMap φ := by
    show x = Spec.map (CommRingCat.ofHom (Spec.preimage x).hom)
    simp
  have hker : RingHom.ker π ≤ RingHom.ker φ := by
    intro a ha
    have h2 : a * a ∈ RingHom.ker π ^ 2 := by
      rw [pow_two]; exact Ideal.mul_mem_mul ha ha
    rw [hsq] at h2
    have h0 : a * a = 0 := by simpa using h2
    have : φ a * φ a = 0 := by rw [← map_mul, h0, map_zero]
    exact RingHom.mem_ker.2 (mul_self_eq_zero.1 this)
  have hc : (RingHom.liftOfSurjective π hπ ⟨φ, hker⟩).comp π = φ :=
    RingHom.liftOfRightInverse_comp _ _ _ _
  generalize RingHom.liftOfSurjective π hπ ⟨φ, hker⟩ = ψ at hc
  refine ⟨ψ, ?_⟩
  rw [hx, ← hc]
  show Spec.map (CommRingCat.ofHom (ψ.comp π)) = Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom π)
  rw [← Spec.map_comp]
  rfl

theorem lieMult_of_sqZeroLift : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ spMap tR)), ∀ (A : Over (Sp C)) [GrpObj A] [IsCommMonObj A] (i : o₀.A.left ⟶ A.left) (h : IsGrpPullback o₀.A A (spMap π) i) (act : GlobalTheory.UPel.HT.OActN D.O A), (∀ c, (o₀.act.act c).left ≫ i = i ≫ (act.act c).left) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp C) (β : R →+* k), x ≫ spMap tR = spMap β → ∀ j, LieMult (act.toF D) x (β.comp (b.t j)) D.m := by
  intro p _ D R _ b N C C₀ _ _ _ _ π hπ hsq tR o₀ A _ _ i h act hact k _ _ x β hx j
  obtain ⟨ψ, rfl⟩ := exists_factor_of_sq_zero π hπ hsq x
  have hact' : ∀ c, ((o₀.act.toF D).act c).left ≫ i = i ≫ ((act.toF D).act c).left :=
    fun c => hact _
  refine (GlobalTheory.LiePull.lieMult_pull (𝓞 D.F) (Sp C) (Sp C₀) A o₀.A (spMap π) i (act.toF D) (o₀.act.toF D)
    h hact' k (spMap ψ) (β.comp (b.t j)) D.m).1 ?_
  exact o₀.lieRank k (spMap ψ) β (by rw [← hx, Category.assoc]) j

end GlobalTheory.HTLiftLie
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
open IsLocalRing
universe u

namespace GlobalTheory

theorem padicInt_ringHom_eq_val {p : ℕ} [Fact p.Prime] {B : Type*} [Ring B] (k : ℕ) (hB : (p : B) ^ k = 0)
    (f : ℤ_[p] →+* B) (z : ℤ_[p]) : f z = (((PadicInt.toZModPow k z).val : ℕ) : B) := by
  set v : ℕ := (PadicInt.toZModPow k z).val with hv
  have hmem : z - (v : ℤ_[p]) ∈ RingHom.ker (PadicInt.toZModPow (p := p) k) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, hv, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hmem
  obtain ⟨y, hy⟩ := hmem
  have hz : z = (v : ℤ_[p]) + (p : ℤ_[p]) ^ k * y := by rw [← hy]; ring
  calc f z = f ((v : ℤ_[p]) + (p : ℤ_[p]) ^ k * y) := by rw [← hz]
    _ = (v : B) := by rw [map_add (f := _), map_mul, map_pow, map_natCast, map_natCast, hB, zero_mul, add_zero]

theorem exists_matrix_action_of_splitting : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (C : Type) [CommRing C] (k : ℕ), (p : C) ^ k = 0 →
  ∀ (H : Type u) [AddCommGroup H] [Module C H] (ρ : D.O →+* Module.End C H)
  (s : (D.O ⊗[ℤ] ℤ_[p]) ≃ₐ[𝓞 D.F] Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p])),
  ∃ Ψ : Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p]) →+* Module.End C H,
    (∀ c, Ψ (s (c ⊗ₜ 1)) = ρ c) ∧
    (∀ T : Module.End C H, (∀ c, ρ c * T = T * ρ c) → ∀ M, Ψ M * T = T * Ψ M) ∧
    (∀ N : Submodule C H, (∀ c, ∀ x ∈ N, ρ c x ∈ N) → ∀ M, ∀ x ∈ N, Ψ M x ∈ N) ∧
    ∀ y (N : Submodule C H), (∀ a, ∀ x ∈ N, ρ (algebraMap (𝓞 D.F) D.O a) x ∈ N) → ∀ x ∈ N, Ψ (Matrix.scalar _ y) x ∈ N := by
  intro p _ D C _ k hk H _ _ ρ s
  have hdvd : ringChar C ∣ p ^ k := ringChar.dvd (by rw [Nat.cast_pow]; exact hk)
  let ιp : ℤ_[p] →+* C := (ZMod.castHom hdvd C).comp (PadicInt.toZModPow k)
  let g : ℤ_[p] →+* Module.End C H := (algebraMap C (Module.End C H)).comp ιp
  let Φ : D.O ⊗[ℤ] ℤ_[p] →ₐ[ℤ] Module.End C H :=
    Algebra.TensorProduct.lift ρ.toIntAlgHom g.toIntAlgHom
      (fun c z => by
        show Commute (ρ c) (algebraMap C (Module.End C H) (ιp z))
        exact Algebra.commute_algebraMap_right _ _)
  have hΦ : ∀ c z, Φ (c ⊗ₜ z) = ρ c * algebraMap C (Module.End C H) (ιp z) := by
    intro c z; simp [Φ, g]

  have hind : ∀ P : Module.End C H → Prop, P 0 → (∀ a b, P a → P b → P (a + b)) →
      (∀ c r, P (ρ c * algebraMap C (Module.End C H) r)) → ∀ t, P (Φ t) := by
    intro P h0 hadd hgen t
    induction t using TensorProduct.induction_on with
    | zero => simpa using h0
    | tmul c z => rw [hΦ]; exact hgen c (ιp z)
    | add a b ha hb => rw [map_add (f := _)]; exact hadd _ _ ha hb
  let Ψ : Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p]) →+* Module.End C H :=
    (Φ : D.O ⊗[ℤ] ℤ_[p] →+* Module.End C H).comp (s.symm : _ →+* _)
  have hΨ : ∀ M, Ψ M = Φ (s.symm M) := fun M => rfl
  refine ⟨Ψ, ?_, ?_, ?_, ?_⟩
  · intro c
    rw [hΨ, AlgEquiv.symm_apply_apply, hΦ, map_one, map_one, _root_.mul_one]
  · intro T hT M
    rw [hΨ]
    refine hind (fun A => A * T = T * A) (by simp) (fun a b ha hb => by rw [_root_.add_mul, _root_.mul_add, ha, hb])
      (fun c r => ?_) _
    rw [_root_.mul_assoc, Algebra.commutes, ← _root_.mul_assoc, hT, _root_.mul_assoc]
  · intro N hN M x hx
    rw [hΨ]
    refine hind (fun A => ∀ x ∈ N, A x ∈ N) (by simp) (fun a b ha hb x hx => ?_) (fun c r x hx => ?_) _ x hx
    · rw [LinearMap.add_apply]; exact N.add_mem (ha x hx) (hb x hx)
    · rw [Module.End.mul_apply, Module.algebraMap_end_apply]
      exact hN c _ (N.smul_mem r hx)
  · intro y N hN
    have hpk : (p : Module.End C H) ^ k = 0 := by
      rw [← map_natCast (algebraMap C (Module.End C H)), ← map_pow, hk, map_zero]
    have hright : ∀ z : ℤ_[p], ∀ x ∈ N, Ψ (Matrix.scalar (Fin D.m) ((1 : 𝓞 D.F) ⊗ₜ[ℤ] z)) x ∈ N := by
      intro z x hx
      let f : ℤ_[p] →+* Module.End C H :=
        (Ψ.comp (Matrix.scalar (Fin D.m))).comp Algebra.TensorProduct.includeRight.toRingHom
      have hf : Ψ (Matrix.scalar (Fin D.m) ((1 : 𝓞 D.F) ⊗ₜ[ℤ] z)) = f z := rfl
      rw [hf, padicInt_ringHom_eq_val k hpk f z, Module.End.natCast_apply]
      exact N.nsmul_mem hx _
    have hleft : ∀ a : 𝓞 D.F, ∀ x ∈ N, Ψ (Matrix.scalar (Fin D.m) (a ⊗ₜ[ℤ] (1 : ℤ_[p]))) x ∈ N := by
      intro a x hx
      have h1 : Matrix.scalar (Fin D.m) (a ⊗ₜ[ℤ] (1 : ℤ_[p])) =
          algebraMap (𝓞 D.F) (Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p])) a := by
        rw [Matrix.algebraMap_eq_diagonal]; rfl
      have h2 : s.symm (algebraMap (𝓞 D.F) _ a) = algebraMap (𝓞 D.F) D.O a ⊗ₜ[ℤ] (1 : ℤ_[p]) := by
        rw [AlgEquiv.commutes]; rfl
      rw [h1, hΨ, h2, hΦ, map_one, map_one, _root_.mul_one]
      exact hN a x hx
    intro x hx
    induction y using TensorProduct.induction_on generalizing x with
    | zero => simpa using N.zero_mem
    | tmul a z =>
      have : (a ⊗ₜ[ℤ] z : 𝓞 D.F ⊗[ℤ] ℤ_[p]) = (a ⊗ₜ[ℤ] (1 : ℤ_[p])) * ((1 : 𝓞 D.F) ⊗ₜ[ℤ] z) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]
      rw [this, map_mul, map_mul, Module.End.mul_apply]
      exact hleft a _ (hright z x hx)
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), LinearMap.add_apply]; exact N.add_mem (ha x hx) (hb x hx)

end GlobalTheory
end

section

open GlobalTheory.FinGL GlobalTheory.FinGL.LeviWh Formalism.L2.DIV Module

theorem _root_.GlobalTheory.T.hecke_comm_of_irreducible_multiplicity_le_one : ∀ (H : Type) [Group H] [Finite H] (U : Subgroup H) (χ : H → ℂ), (∀ x ∈ U, ∀ y ∈ U, χ (x * y) = χ x * χ y) → χ 1 = 1 → (∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (τ : Representation ℂ H W), τ.IsIrreducible → finrank ℂ (eig τ (U : Set H) χ) ≤ 1) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (τ : Representation ℂ H V), ∃ e : Module.End ℂ V, e * e = e ∧ (∀ v ∈ eig τ (U : Set H) χ, e v = v) ∧ (∀ T : Module.End ℂ V, (∀ g, Commute T (τ g)) → Commute T e) ∧ ∀ g h : H, e * τ g * e * τ h * e = e * τ h * e * τ g * e := by
  first | exact @GlobalTheory.FinGL.LeviWh.exists_idem_hecke_comm | exact GlobalTheory.FinGL.LeviWh.exists_idem_hecke_comm | (intros; apply GlobalTheory.FinGL.LeviWh.exists_idem_hecke_comm <;> assumption)
end

section

open GlobalTheory.FinGL Formalism.L2.DIV Module

theorem _root_.GlobalTheory.T.whittakerSpaceDimFiniteGL_le_one : ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (τ : Representation ℂ (GL (Fin r) F) V), τ.IsIrreducible → whDim ψ τ ≤ 1 := by
  first | exact @GlobalTheory.FinGL.GGFree.whDim_le_one | exact GlobalTheory.FinGL.GGFree.whDim_le_one | (intros; apply GlobalTheory.FinGL.GGFree.whDim_le_one <;> assumption)
end

section

open CategoryTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.exists_verschiebung_of_dieudonneFunctorBase : ∀ (p : ℕ) [Fact p.Prime] (B : GlobalTheory.Dieu.Base p (fun _ _ _ => True)), ∃ V : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : GlobalTheory.PDivGroup p k), B.M G trivial →ₛₗ[((WittVector.frobeniusEquiv p k).symm : WittVector p k →+* WittVector p k)] B.M G trivial, (∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : GlobalTheory.PDivGroup p k) (m : B.M G trivial), B.F G trivial (V G m) = p • m) ∧ ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : GlobalTheory.PDivGroup p k) (m : B.M G trivial), V G (B.F G trivial m) = p • m := by
  first | exact @GlobalTheory.Dieu.exists_V_of_base | exact GlobalTheory.Dieu.exists_V_of_base | (intros; apply GlobalTheory.Dieu.exists_V_of_base <;> assumption)
end

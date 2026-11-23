module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle512
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle573
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle572
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle521
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle575
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle574
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007

@[expose] public section

section

open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace PDivGroup

variable {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)


open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv in
set_option autoImplicit false in
variable {p : ℕ} {R : Type} [CommRing R] (G : _root_.GlobalTheory.PDivGroup p R) in
theorem _root_.GlobalTheory.PDivGroup.transl_eq_of_cobOne_eq_pullTwo (n : ℕ) (x : G.A (n + 1))
    (t : G.A n ⊗[R] G.A n)
    (h : _root_.GlobalTheory.PDiv.cobOne R _ x = _root_.GlobalTheory.PDiv.pullbackTwo (G.mulP n) t)
    (h1 : G.resOne n x = 0) :
    G.transl n x = x ⊗ₜ 1 := by
  set f := G.mulP n
  set ρ := G.resOne n
  have hcomul : comul x = x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] x +
      TensorProduct.map (f : G.A n →ₗ[R] G.A (n + 1))
        (f : G.A n →ₗ[R] G.A (n + 1)) t := by
    have := h
    unfold _root_.GlobalTheory.PDiv.cobOne _root_.GlobalTheory.PDiv.pullbackTwo at this
    simp only [LinearMap.sub_apply, LinearMap.flip_apply, TensorProduct.mk_apply] at this
    rw [← this]; abel
  have hε : counit x = (0 : R) := by
    have := CoalgHomClass.counit_comp_apply ρ x
    rw [h1, map_zero] at this
    exact this.symm
  have hρf : (ρ : G.A (n + 1) →ₗ[R] G.A 1) ∘ₗ
      (f : G.A n →ₗ[R] G.A (n + 1))
        = Algebra.linearMap R _ ∘ₗ counit := by
    ext a
    exact _root_.GlobalTheory.PDivGroup.resOne_mulP G n a
  have hεf : (counit : _ →ₗ[R] R) ∘ₗ
      (f : G.A n →ₗ[R] G.A (n + 1)) = counit := by
    ext a
    exact CoalgHomClass.counit_comp_apply f a
  have hzero : TensorProduct.map (f : G.A n →ₗ[R] G.A (n + 1))
      (counit : _ →ₗ[R] R) t = 0 := by
    have := congrArg (LinearMap.lTensor _ (counit : _ →ₗ[R] R)) hcomul
    rw [Coalgebra.lTensor_counit_comul, map_add (f := _), map_add (f := _), LinearMap.lTensor_tmul,
      LinearMap.lTensor_tmul, hε, counit_one, ← LinearMap.comp_apply, LinearMap.lTensor_comp_map,
      hεf, tmul_zero, add_zero] at this
    simpa using this
  rw [_root_.GlobalTheory.PDivGroup.transl_apply, hcomul, map_add (f := _), map_add (f := _), LinearMap.lTensor_tmul,
    LinearMap.lTensor_tmul, ← LinearMap.comp_apply, LinearMap.lTensor_comp_map, hρf,
    ← LinearMap.lTensor_comp_map, LinearMap.comp_apply, hzero, map_zero, add_zero]
  have h1' : G.resOne n x = 0 := h1
  simp [h1']

end PDivGroup


open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv in
set_option autoImplicit false in
theorem _root_.GlobalTheory.cocycle_mem_range_cob_of_pullback_mulP :
    ∀ {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] (G : _root_.GlobalTheory.PDivGroup p R)
      (c : G.cocycles) (B : G.funs),
        G.cob B = _root_.GlobalTheory.PDivGroup.cocyclesMap ((p : ℤ_[p]) • 𝟙 G) c → B.1 1 = 0 →
        c ∈ LinearMap.range G.cob := by
  intro p _ R _ G c B hB hB1
  have hcobf : ∀ {m m' : ℕ} (f : G.A m →ₐc[R] G.A m') (a),
      _root_.GlobalTheory.PDiv.cobOne R _ (f a)
        = _root_.GlobalTheory.PDiv.pullbackTwo f (_root_.GlobalTheory.PDiv.cobOne R _ a) := by
    intro m m' f a
    unfold _root_.GlobalTheory.PDiv.cobOne _root_.GlobalTheory.PDiv.pullbackTwo
    simp only [LinearMap.sub_apply, LinearMap.flip_apply, TensorProduct.mk_apply, map_sub,
      TensorProduct.map_tmul]
    rw [← CoalgHomClass.map_comp_comul_apply f a]
    simp
  have hpull : ∀ {m m' m'' : ℕ} (f : G.A m' →ₐc[R] G.A m'')
      (g : G.A m →ₐc[R] G.A m') (z),
      _root_.GlobalTheory.PDiv.pullbackTwo (f.comp g) z
        = _root_.GlobalTheory.PDiv.pullbackTwo f (_root_.GlobalTheory.PDiv.pullbackTwo g z) := by
    intro m m' m'' f g z
    unfold _root_.GlobalTheory.PDiv.pullbackTwo
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]
    rfl
  have hlevel : ∀ n, _root_.GlobalTheory.PDiv.cobOne R _ (B.1 (n + 1))
      = _root_.GlobalTheory.PDiv.pullbackTwo (G.mulP n) (c.1 n) := by
    intro n
    have h := congrArg (fun z => z.1 (n + 1)) hB
    unfold _root_.GlobalTheory.PDivGroup.cob _root_.GlobalTheory.PDivGroup.cocyclesMap at h
    simp only [LinearMap.coe_mk, AddHom.coe_mk] at h
    rw [h, _root_.GlobalTheory.PDivGroup.natCast_smul_id_app, ← _root_.GlobalTheory.PDivGroup.mulP_comp_res, hpull]
    congr 1
    exact (c.2 n).2
  have hres1 : ∀ n, G.resOne n (B.1 (n + 1)) = 0 := by
    intro n
    rw [_root_.GlobalTheory.PDivGroup.resOne_funs, hB1]
  have hex : ∀ n, ∃ e, G.mulP n e = B.1 (n + 1) := fun n =>
    _root_.GlobalTheory.PDivGroup.exists_mulP_eq_of_transl_eq G n _
      (_root_.GlobalTheory.PDivGroup.transl_eq_of_cobOne_eq_pullTwo G n _ _ (hlevel n) (hres1 n))
  choose e he using hex
  have hcompat : ∀ n, G.res n (e (n + 1)) = e n := by
    intro n
    apply _root_.GlobalTheory.PDivGroup.Test.mulP_injective G n
    rw [_root_.GlobalTheory.PDivGroup.mulP_res, ← _root_.GlobalTheory.PDivGroup.res_mulP, he, he]
    exact B.2 (n + 1)
  refine ⟨⟨e, hcompat⟩, ?_⟩
  apply Subtype.ext
  funext n
  apply _root_.GlobalTheory.PDivGroup.pullbackTwo_mulP_injective G n
  rw [← hlevel, ← he, hcobf]
  rfl

end GlobalTheory
end
end

section

open Coalgebra

theorem GlobalTheory.T.additiveFunctionCartierDualTangent_bijective
    {R A : Type} [CommRing R] [CommRing A] [Bialgebra R A] [Module.Finite R A]
    [Module.Projective R A] [IsCocomm R A] :
    Function.Bijective (GlobalTheory.PDiv.primTangent R A) :=
  GlobalTheory.PDiv.primTangent_bijective
end

section

open GlobalTheory.PDiv

theorem GlobalTheory.T.additiveFunctions_flatBaseChange_bijective {R A : Type} (R' : Type)
    [CommRing R] [CommRing A] [Bialgebra R A] [CommRing R'] [Algebra R R'] [Module.Flat R R'] :
    Function.Bijective (liftSemi (toBaseChange R R' A).prim) :=
  liftSemi_prim_baseChange_bijective R'
end

section

open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.exists_mulP_eq_of_transl_invariant : ∀ {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R) (n : ℕ) (a : G.A (n + 1)), G.transl n a = a ⊗ₜ[R] 1 → ∃ e : G.A n, G.mulP n e = a := by
  first | exact @GlobalTheory.PDivGroup.exists_mulP_eq_of_transl_eq | exact GlobalTheory.PDivGroup.exists_mulP_eq_of_transl_eq | (intros; apply GlobalTheory.PDivGroup.exists_mulP_eq_of_transl_eq <;> assumption)
end

section

open GlobalTheory.PDiv

theorem GlobalTheory.T.omega_baseChange_bijective_of_p_eq_zero {p : ℕ} {R : Type}
    [CommRing R] (G : GlobalTheory.PDivGroup p R) (R' : Type) [CommRing R'] [Algebra R R']
    (hp : (p : R) = 0) : Function.Bijective (liftSemi (G.toBase R').omega) :=
  G.omega_baseChange_bijective R' hp
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.pDivGroup_mulP_unit_fiber_eq_level_one : ∀ (p : ℕ) (R k : Type) [CommRing R] [CommRing k] [Algebra R k], Function.Surjective (algebraMap R k) → ∀ (G : GlobalTheory.PDivGroup p R) (n : ℕ), Function.Surjective (fun a : G.A (n + 1) => ((1 : k) ⊗ₜ[R] G.resOne n a : k ⊗[R] G.A 1)) ∧ ∀ a : G.A (n + 1), ((1 : k) ⊗ₜ[R] G.resOne n a : k ⊗[R] G.A 1) = 0 ↔ a ∈ (RingHom.ker ((algebraMap R k).comp (Bialgebra.counitAlgHom R (G.A n) : G.A n →+* R))).map ((G.mulP n : G.A n →ₐ[R] G.A (n + 1)) : G.A n →+* G.A (n + 1)) := by
  exact @GlobalTheory.fibre_statement
end

section

open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.coboundary_translation_invariant_pTorsion : ∀ {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R) (n : ℕ) (x : G.A (n + 1)) (b : G.A 1), G.transl n x = x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b → ((G.transl n).toLinearMap - (TensorProduct.mk R (G.A (n + 1)) (G.A 1)).flip 1).rTensor (G.A (n + 1)) (cobOne R (G.A (n + 1)) x) = 0 ∧ ((G.transl n).toLinearMap - (TensorProduct.mk R (G.A (n + 1)) (G.A 1)).flip 1).lTensor (G.A (n + 1)) (cobOne R (G.A (n + 1)) x) = 0 := by
  first | exact @GlobalTheory.PDivGroup.cobOne_transl_invariant | exact GlobalTheory.PDivGroup.cobOne_transl_invariant | (intros; apply GlobalTheory.PDivGroup.cobOne_transl_invariant <;> assumption)
end

section

open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.transl_coaction_free_coassoc_counital : ∀ {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R) (n : ℕ), (∀ a, TensorProduct.assoc R (G.A (n + 1)) (G.A 1) (G.A 1) ((G.transl n).toLinearMap.rTensor (G.A 1) (G.transl n a)) = (Coalgebra.comul (R := R) (A := G.A 1)).lTensor (G.A (n + 1)) (G.transl n a)) ∧ (∀ a, TensorProduct.rid R (G.A (n + 1)) ((Coalgebra.counit (R := R) (A := G.A 1)).lTensor (G.A (n + 1)) (G.transl n a)) = a) ∧ Function.Surjective (Algebra.TensorProduct.productMap (Algebra.TensorProduct.includeLeft : G.A (n + 1) →ₐ[R] G.A (n + 1) ⊗[R] G.A 1) (G.transl n)) := by
  first | exact @GlobalTheory.PDivGroup.transl_free | exact GlobalTheory.PDivGroup.transl_free | (intros; apply GlobalTheory.PDivGroup.transl_free <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix
open GlobalTheory.OriginBox GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx

theorem _root_.GlobalTheory.T.abs_originBoxValueExponent_le : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (G : Grid k), 1 ≤ G.s → ∀ (a a' : ℤ) (N : ℕ), (∀ i j, i ≤ G.m → j ≤ G.m → G.rank (i, j) ≤ N) → |expo G a a'| ≤ 8 * ((G.m : ℤ) ^ 3 * (N : ℤ) ^ 2 * (|a| + |a'|)) := by
  first | exact @GlobalTheory.OriginBox.abs_expo_le | exact GlobalTheory.OriginBox.abs_expo_le | (intros; apply GlobalTheory.OriginBox.abs_expo_le <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

noncomputable section

namespace GlobalTheory.HomFixUniv

variable {A₀ B₀ X T : Scheme.{0}} {N : LB A₀} {H : LB B₀} {mA mB : ℕ}

def comb (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T) (c : Fin mA → Fin mB → Γ(T, ⊤)) (z : X) (q : N.ι)
    (j : Fin mB) : X.presheaf.stalk z :=
  ∑ i, gs p z ⊤ (c i j) * gs φ z (N.U q) ((a i).f q)

def Generates (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T) (c : Fin mA → Fin mB → Γ(T, ⊤)) : Prop :=
  ∀ z q, φ z ∈ N.U q → ∃ j, IsUnit (comb a φ p c z q j)

def Proport (a : Fin mA → LB.Sec N) (b : Fin mB → LB.Sec H) (φ : X ⟶ A₀) (p : X ⟶ T) (Ψ : X ⟶ B₀)
    (c : Fin mA → Fin mB → Γ(T, ⊤)) : Prop :=
  ∀ z q k, φ z ∈ N.U q → Ψ z ∈ H.U k → ∀ j j',
    gs Ψ z (H.U k) ((b j).f k) * comb a φ p c z q j' = gs Ψ z (H.U k) ((b j').f k) * comb a φ p c z q j

def gc {R : Type} [CommRing R] (f : X ⟶ Sp R) (z : X) : R →+* X.presheaf.stalk z :=
  (X.presheaf.germ ⊤ z trivial).hom.comp (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

def Kills {R : Type} [CommRing R] (fB : B₀ ⟶ Sp R) (b : Fin mB → LB.Sec H) (F : MvPolynomial (Fin mB) R) : Prop :=
  ∀ k, MvPolynomial.eval₂Hom (GlobalTheory.AbLaw.cst fB (H.U k)) (fun j => (b j).f k) F = 0

def FormsOK {R : Type} [CommRing R] (a : Fin mA → LB.Sec N) (fB : B₀ ⟶ Sp R) (b : Fin mB → LB.Sec H) (φ : X ⟶ A₀)
    (p : X ⟶ T) (t : T ⟶ Sp R) (c : Fin mA → Fin mB → Γ(T, ⊤)) : Prop :=
  ∀ (d : ℕ) (F : MvPolynomial (Fin mB) R), F.IsHomogeneous d → Kills fB b F →
    ∀ z q, φ z ∈ N.U q → MvPolynomial.eval₂Hom (gc (p ≫ t) z) (comb a φ p c z q) F = 0

def IsVal {S : Scheme.{0}} (e : S ⟶ A₀) (u : ∀ z : S, N.ι → (S.presheaf.stalk z)ˣ) (s : LB.Sec N) (α : Γ(S, ⊤)) :
    Prop :=
  ∀ z q, e z ∈ N.U q → gs e z (N.U q) (s.f q) = gs (𝟙 S) z ⊤ α * (u z q).val

def Normal {S : Scheme.{0}} (t : T ⟶ S) (c : Fin mA → Fin mB → Γ(T, ⊤)) (α : Fin mA → Γ(S, ⊤)) (β : Fin mB → Γ(S, ⊤)) :
    Prop :=
  ∀ j, t.appTop (β j) = ∑ i, c i j * t.appTop (α i)

def θ {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) : A.left ⟶ (topS Rg ⊗ A).left :=
  (lift (Over.homMk (A.hom ≫ (Sp Rg).topIso.inv) (by simp) : A ⟶ topS Rg) (𝟙 A)).left

theorem θ_snd {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) : θ A ≫ (snd (topS Rg) A).left = 𝟙 A.left := by
  rw [θ, ← Over.comp_left, lift_snd]; rfl

abbrev fA {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) : (topS Rg ⊗ A).left ⟶ Sp Rg := (topS Rg ⊗ A).hom

theorem coord_comp {Rg : Type} [CommRing Rg] {X' : Scheme.{0}} {n : ℕ} (h : X ⟶ X')
    (g : X' ⟶ Sp (MvPolynomial (Fin n) Rg)) (i : Fin n) : coord (h ≫ g) i = h.appTop (coord g i) := by
  rfl

def uFr {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) [GrpObj A] (L : LB A.left) (k : ℕ)
    (eA : LB.Gen (L.pull (eSec A))) (z : (𝟙_ (Over (Sp Rg))).left) (q : (LPow A L (k : ℤ) (topS Rg)).ι) :
    ((𝟙_ (Over (Sp Rg))).left.presheaf.stalk z)ˣ :=
  (gm (𝟙 _) z _ (eA.s fun _ => q 0)) ^ k

end GlobalTheory.HomFixUniv
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

theorem _root_.GlobalTheory.T.exists_coeff_pullback_baseChangeStableSectionBasis : ∀ (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) [GrpObj A] (L : LB A.left) (k : ℕ) (mA : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))), IsBCBasis A L k bA → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' : Over (Sp R)) (φA' : A'.left ⟶ A.left), IsPullback φA' A'.hom A.hom t → ∀ (ψA : A'.left ⟶ (topS Rg ⊗ A).left), ψA ≫ (snd (topS Rg) A).left = φA' → ∀ s : LB.Sec (powPull L (ψA ≫ (snd (topS Rg) A).left) (k : ℤ)), ∃ c : Fin mA → Γ(Sp R, ⊤), ∀ q : Fin 1 → L.ι, s.f q = ∑ i, (A'.hom.appLE ⊤ (LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) q) (fun _ _ => trivial)).hom (c i) * (ψA.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) q) (LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) q) (GlobalTheory.HomFixMat.wchart_comp_le L ψA (snd (topS Rg) A).left q)).hom ((bA i).f q) := by
  first | (exact @GlobalTheory.HomFixMat.exists_coeff_of_isBCBasis) | (exact GlobalTheory.HomFixMat.exists_coeff_of_isBCBasis) | (intros; apply GlobalTheory.HomFixMat.exists_coeff_of_isBCBasis  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

theorem _root_.GlobalTheory.T.exists_lineBundlePowerPullback_section_pullback : ∀ {X Y Z : Scheme.{0}} (L : LB Z) (φ : Y ⟶ Z) (h : X ⟶ Y) (a : ℤ) (s : LB.Sec (powPull L φ a)), ∃ s' : LB.Sec (powPull L (h ≫ φ) a), ∀ q : Fin 1 → L.ι, s'.f q = (h.appLE (LB.wchart L (fun _ : Fin 1 => φ) q) (LB.wchart L (fun _ : Fin 1 => h ≫ φ) q) (GlobalTheory.HomFixMat.wchart_comp_le L h φ q)).hom (s.f q) := by
  first | (exact @GlobalTheory.HomFixMat.pullSec_exists) | (exact GlobalTheory.HomFixMat.pullSec_exists) | (intros; apply GlobalTheory.HomFixMat.pullSec_exists  <;> assumption)
end

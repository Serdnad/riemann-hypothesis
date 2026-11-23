module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle002
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle393
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle400
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle338
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle396
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import ReciprocityTheory.DualLattices.Bundle010
import ReciprocityTheory.DualLattices.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp

@[expose] public section

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.prod_rootPowerSum_map_galois_eq : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (θ : AlgebraicClosure F' →* ℂ) (k : ℕ) (P : F'[X]), ∏ t : F' ≃ₐ[F] F', rootSum θ k (P.map (t : F' →+* F')) = ∏ j ∈ Finset.range (Module.finrank F F'), rootSum θ (k * Nat.card F ^ j) P := by
  first | (exact @GlobalTheory.Shin.prod_rootSum_map_algEquiv) | (exact GlobalTheory.Shin.prod_rootSum_map_algEquiv) | (intros; apply GlobalTheory.Shin.prod_rootSum_map_algEquiv  <;> assumption)
end

section

open ReciprocityTheory.PGsh.Up GlobalTheory.Sandwich Matrix

namespace GlobalTheory.Sandwich.HodgeTateBound

section General

variable {A O : Type} [CommRing A] [CommRing O] {h : ℕ}

end General

open Matrix in
variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n] in
private lemma mul_eq_smul_one_of_mul_eq_smul_one [IsDomain R] {A B : Matrix n n R} {c : R}
    (hc : c ≠ 0) (hBA : B * A = c • (1 : Matrix n n R)) : A * B = c • (1 : Matrix n n R) := by
  have hdet : A.det ≠ 0 := by
    intro h0
    have hprod : B.det * A.det = c ^ Fintype.card n := by
      rw [← det_mul, hBA, det_smul, det_one, mul_one]
    rw [h0, mul_zero] at hprod
    exact pow_ne_zero _ hc hprod.symm
  have key : A.det • (A * B) = A.det • (c • (1 : Matrix n n R)) := by
    calc A.det • (A * B) = (A * B) * (A * adjugate A) := by
          rw [mul_adjugate, Matrix.mul_smul, Matrix.mul_one]
      _ = A * (B * A) * adjugate A := by simp only [Matrix.mul_assoc]
      _ = A.det • (c • (1 : Matrix n n R)) := by
          rw [hBA, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, mul_adjugate, smul_smul,
            smul_smul, mul_comm]
  ext i j
  have hij := congrFun (congrFun key i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at hij
  exact mul_left_cancel₀ hdet hij

open Matrix in
variable {A O : Type*} [CommRing A] [CommRing O] {h : ℕ} in
private lemma smul_mem_range_of_mem_ker_of_mul_eq (θ : A →+* O) (hθ : Function.Surjective θ)
    {ξ ν : A} (hker : RingHom.ker θ = Ideal.span {ξ}) (hξ : ∀ y : A, y * ξ = 0 → y = 0)
    {P Q : Matrix (Fin h) (Fin h) A} (hQP : Q * P = (ξ * ν) • (1 : Matrix (Fin h) (Fin h) A))
    (t : Fin h → O) (ht : t ∈ LinearMap.ker (toLin' (P.map θ))) :
    θ ν • t ∈ LinearMap.range (toLin' (Q.map θ)) := by
  choose s hs using fun i => hθ (t i)
  have hst : (θ ∘ s) = t := funext hs
  rw [LinearMap.mem_ker, toLin'_apply] at ht
  have hmem : ∀ i, (P *ᵥ s) i ∈ Ideal.span {ξ} := by
    intro i
    rw [← hker, RingHom.mem_ker, RingHom.map_mulVec, hst]
    exact congrFun ht i
  choose g hg using fun i => Ideal.mem_span_singleton'.mp (hmem i)
  have hQg : Q *ᵥ g = ν • s := by
    funext i
    apply sub_eq_zero.mp
    apply hξ
    have h1 : Q *ᵥ (P *ᵥ s) = (ξ * ν) • s := by
      rw [mulVec_mulVec, hQP, Matrix.smul_mulVec, one_mulVec]
    have h2 : P *ᵥ s = fun j => g j * ξ := funext fun j => (hg j).symm
    have h3 := congrFun h1 i
    rw [h2] at h3
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h3 ⊢
    have h4 : ∑ j, Q i j * (g j * ξ) = (∑ j, Q i j * g j) * ξ := by
      rw [Finset.sum_mul]
      simp only [mul_assoc]
    rw [h4] at h3
    linear_combination h3
  refine ⟨θ ∘ g, ?_⟩
  rw [toLin'_apply]
  funext i
  rw [← RingHom.map_mulVec, hQg]
  simp [← hs]

open Matrix in
variable {O : Type*} [CommRing O] {h : ℕ} in
private lemma map_iInf_eigenspace_le_of_intertwine {ι : Type*} {X Y : ι → Matrix (Fin h) (Fin h) O}
    {Z : Matrix (Fin h) (Fin h) O} (c : ι → O) (hZ : ∀ a, Y a * Z = Z * X a) :
    (⨅ a, Module.End.eigenspace (toLin' (X a)) (c a)).map (toLin' Z) ≤
      ⨅ a, Module.End.eigenspace (toLin' (Y a)) (c a) := by
  rintro _ ⟨x, hx, rfl⟩
  simp only [SetLike.mem_coe, Submodule.mem_iInf] at hx
  rw [Submodule.mem_iInf]
  intro a
  have hxa := hx a
  rw [Module.End.mem_eigenspace_iff, toLin'_apply] at hxa ⊢
  rw [toLin'_apply, mulVec_mulVec, hZ, ← mulVec_mulVec, hxa, mulVec_smul]


open Matrix in
theorem _root_.GlobalTheory.Sandwich.HodgeTateBound.bound : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C]
    [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O →
    ∀ ε : PreTilt O p, IsPrimitiveRoot (_root_.GlobalTheory.Sandwich.root ε).untilt p →
    ∀ (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ], ∀ (h : ℕ) (D : _root_.GlobalTheory.Sandwich.Datum ε h Λ),
    D.F * D.G =
        _root_.GlobalTheory.Sandwich.mu ε • (1 : Matrix (Fin h) (Fin h) (_root_.GlobalTheory.Sandwich.Ainf p O)) ∧
      LinearMap.range D.al ≤ D.Fil ∧
      D.Lie ≤ LinearMap.ker D.al ∧
      (∀ f ∈ D.Fil, WittVector.fontaineTheta O p (_root_.GlobalTheory.Sandwich.nu ε) • f ∈
        LinearMap.range D.al) ∧
      (∀ t ∈ LinearMap.ker D.al,
        WittVector.fontaineTheta O p (_root_.GlobalTheory.Sandwich.nu ε) • t ∈ D.Lie) ∧
      (∀ τ : Λ →+* O, (D.Tsub τ).map D.al ≤
          D.Fil ⊓ D.Hsub τ ∧
        (D.Hsub τ).map D.bb ≤
          D.Lie ⊓ D.Tsub τ ∧
        D.Lie ⊓ D.Tsub τ ≤
          D.W τ) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ h D
  haveI : IsDomain (_root_.GlobalTheory.Sandwich.Ainf p O) := _root_.GlobalTheory.AinfXi.isDomain_ainf hv
  have hker := _root_.GlobalTheory.AinfXi.ker_theta hv ε hε
  have hξ := _root_.GlobalTheory.AinfXi.xi_nzd hv ε hε
  have hsurj : Function.Surjective (WittVector.fontaineTheta O p) := _root_.ReciprocityTheory.PGsh.Ainf.theta_surj p O hv
  have hμ := _root_.GlobalTheory.Sandwich.xi_mul_nu ε
  have hθξ : WittVector.fontaineTheta O p (_root_.GlobalTheory.Sandwich.xi ε) = 0 := by
    rw [← RingHom.mem_ker, hker]
    exact Ideal.mem_span_singleton_self _
  have hθμ : WittVector.fontaineTheta O p (_root_.GlobalTheory.Sandwich.mu ε) = 0 := by
    rw [← hμ, map_mul, hθξ, zero_mul]
  have hξ0 : _root_.GlobalTheory.Sandwich.xi ε ≠ 0 := by
    intro h0
    exact one_ne_zero (hξ 1 (by rw [h0, mul_zero]))
  have hν0 : _root_.GlobalTheory.Sandwich.nu ε ≠ 0 := by
    intro h0
    have h1 : WittVector.fontaineTheta O p (_root_.GlobalTheory.Sandwich.nu ε) =
        PreTilt.untilt (_root_.GlobalTheory.Sandwich.root ε) - 1 := by
      simp [_root_.GlobalTheory.Sandwich.nu, WittVector.fontaineTheta_teichmuller]
    rw [h0, map_zero] at h1
    exact hε.ne_one (Fact.out : p.Prime).one_lt (sub_eq_zero.mp h1.symm)
  have hμ0 : _root_.GlobalTheory.Sandwich.mu ε ≠ 0 := by
    rw [← hμ]
    exact mul_ne_zero hξ0 hν0
  have hGF := D.G_mul_F
  have hFG := mul_eq_smul_one_of_mul_eq_smul_one hμ0 hGF
  have hA : D.G.map (WittVector.fontaineTheta O p) *
      D.F.map (WittVector.fontaineTheta O p) = 0 := by
    rw [← Matrix.map_mul, hGF]
    ext i j
    simp [hθμ]
  have hB : D.F.map (WittVector.fontaineTheta O p) *
      D.G.map (WittVector.fontaineTheta O p) = 0 := by
    rw [← Matrix.map_mul, hFG]
    ext i j
    simp [hθμ]
  have hpad : ∀ M : Matrix (Fin h) (Fin h) ℤ_[p],
      (M.map (_root_.GlobalTheory.Sandwich.ofPadic p O)).map (WittVector.fontaineTheta O p) = M.map (_root_.GlobalTheory.Sandwich.padicToO p O) := by
    intro M
    ext i j
    simp [_root_.GlobalTheory.Sandwich.padicToO]
  have hact := D.F_act
  have hGact : ∀ a, (D.ρT a).map (_root_.GlobalTheory.Sandwich.ofPadic p O) * D.G =
      D.G * D.ρM a := by
    intro a
    have e : _root_.GlobalTheory.Sandwich.mu ε •
        ((D.ρT a).map (_root_.GlobalTheory.Sandwich.ofPadic p O) * D.G) =
        _root_.GlobalTheory.Sandwich.mu ε • (D.G * D.ρM a) := by
      calc _ = D.G * D.F *
              (D.ρT a).map (_root_.GlobalTheory.Sandwich.ofPadic p O) * D.G := by
            rw [hGF, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul]
        _ = D.G * (D.F *
              (D.ρT a).map (_root_.GlobalTheory.Sandwich.ofPadic p O)) * D.G := by
            simp only [Matrix.mul_assoc]
        _ = D.G * (D.ρM a * D.F) *
              D.G := by rw [hact a]
        _ = D.G * D.ρM a *
              (D.F * D.G) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hFG, Matrix.mul_smul, Matrix.mul_one]
    refine Matrix.ext fun i j => ?_
    have hij := congrFun (congrFun e i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at hij
    exact mul_left_cancel₀ hμ0 hij
  simp only [_root_.GlobalTheory.Sandwich.Datum.al, _root_.GlobalTheory.Sandwich.Datum.bb,
    _root_.GlobalTheory.Sandwich.Datum.Fil, _root_.GlobalTheory.Sandwich.Datum.Lie,
    _root_.GlobalTheory.Sandwich.Datum.Tsub, _root_.GlobalTheory.Sandwich.Datum.Hsub,
    _root_.GlobalTheory.Sandwich.Datum.W]
  have hrange : LinearMap.range (toLin' (D.F.map (WittVector.fontaineTheta O p))) ≤
      LinearMap.ker (toLin' (D.G.map (WittVector.fontaineTheta O p))) := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, toLin'_apply, toLin'_apply, mulVec_mulVec, hA, zero_mulVec]
  have hlie : LinearMap.range (toLin' (D.G.map (WittVector.fontaineTheta O p))) ≤
      LinearMap.ker (toLin' (D.F.map (WittVector.fontaineTheta O p))) := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, toLin'_apply, toLin'_apply, mulVec_mulVec, hB, zero_mulVec]
  refine ⟨hFG, hrange, hlie, ?_, ?_, ?_⟩
  · exact smul_mem_range_of_mem_ker_of_mul_eq _ hsurj hker hξ (by rw [hFG, hμ])
  · exact smul_mem_range_of_mem_ker_of_mul_eq _ hsurj hker hξ (by rw [hGF, hμ])
  · intro τ
    refine ⟨le_inf (LinearMap.map_le_range.trans hrange) ?_,
      le_inf LinearMap.map_le_range ?_, fun x hx => ⟨hx.2, hlie hx.1⟩⟩
    · refine map_iInf_eigenspace_le_of_intertwine τ fun a => ?_
      rw [← Matrix.map_mul, ← hact a, Matrix.map_mul, hpad]
    · refine map_iInf_eigenspace_le_of_intertwine τ fun a => ?_
      rw [← hpad, ← Matrix.map_mul, hGact a, Matrix.map_mul]

end GlobalTheory.Sandwich.HodgeTateBound
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

namespace GlobalTheory.AnPer.Charts

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}

theorem cochain_fromTriv_eq (K : Charts F) (h : C1 K.Oc) (l : Λ)
    (H : ∀ (k : K.K) (T : K.Obj) (χ : K.jet k ⟶ T), χ.deg = l → h _ _ (jet0 k ≫ χ) = h _ _ (jet1 k ≫ χ))
    {k : K.K} (T : K.Obj) (hle : K.le l T.k k) (ρ : Hol (K.W k) →+* T.C)
    (hρ : Close T.J (T.ρ.comp (K.sh hle)) ρ) :
    ∀ hc : ∀ f, ρ (K.cst k f) = algebraMap (Hol F.V) T.C f,
      h _ _ (fromTriv T hle ρ hc hρ) = h _ _ (ptHom T hle) := by
  induction hρ with
  | refl => intro hc; rfl
  | @tail ρ₁ ρ₂ hab s ih =>
    intro hc₂
    obtain ⟨n, h1, h2, h3⟩ := s
    have hc₁ : ∀ f, ρ₁ (K.cst k f) = algebraMap (Hol F.V) T.C f := fun f ↦ by
      rw [← hc₂ f, h3]
      simp [dw_cst]
    rw [← ih hc₁]
    obtain ⟨χ, hdeg, e0, e1, -⟩ := GlobalTheory.AnPer.Charts.exists_jet_factor K (fromTriv T hle ρ₁ hc₁ hab)
      (fromTriv T hle ρ₂ hc₂ (Relation.ReflTransGen.tail hab ⟨n, h1, h2, h3⟩)) n rfl h1 h2 (fun x ↦ h3 x)
    rw [← e0, ← e1]
    exact (H k T χ hdeg).symm

theorem cochain_eq_ptHom {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
    (K : Charts F) (h : C1 K.Oc) (l : Λ)
    (H : ∀ (k : K.K) (T : K.Obj) (χ : K.jet k ⟶ T), χ.deg = l → h _ _ (jet0 k ≫ χ) = h _ _ (jet1 k ≫ χ))
    (k : K.K) (T : K.Obj) (f : K.triv k ⟶ T) (hf : f.deg = l) :
    h _ _ f = h _ _ (ptHom T (Charts.Hom.le f)) := by
  subst hf
  letI := (K.triv k).alg
  exact cochain_fromTriv_eq K h f.deg H T (Charts.Hom.le f) f.φ.toRingHom (Charts.Hom.close f)
    (fun x ↦ f.φ.commutes x)

end GlobalTheory.AnPer.Charts
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

namespace GlobalTheory.AnPer.ClosedSq

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F)

theorem diff (h : C1 K.Oc) (hh : ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 →
      h T T'' (φ ≫ ψ) = ψ.φ (h T T' φ) + h T' T'' ψ) (k : K.K)
    (θ : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k))) (hθ : θ = h _ _ (jet0 k) - h _ _ (jet1 k))
    {T : K.Obj} (f₁ f₂ : K.triv k ⟶ T) (n : Fin g → T.C) (d₁ : f₁.deg = 0) (d₂ : f₂.deg = 0)
    (hn : ∀ a, n a ∈ T.J) (hnn : ∀ a b, n a * n b = 0)
    (hf : ∀ x : Hol (K.W k), f₂.φ x = f₁.φ x + ∑ a, f₁.φ (dw a x : Hol (K.W k)) * n a) (u₁ u₂ : T.C)
    (h₁ : u₁ = h _ _ f₁) (h₂ : u₂ = h _ _ f₂) :
    u₁ - u₂ = f₁.φ (θ.fst : Hol (K.W k)) + ∑ a, f₁.φ (θ.snd a : Hol (K.W k)) * n a := by
  obtain ⟨χ, hd, h0, h1, hχ⟩ := exists_jet_factor K f₁ f₂ n (d₁.trans d₂.symm) hn hnn hf
  have e0 := hh _ _ _ (jet0 k) χ rfl (hd.trans d₁)
  have e1 := hh _ _ _ (jet1 k) χ rfl (hd.trans d₁)
  rw [h0] at e0
  rw [h1] at e1
  rw [← hχ θ, hθ, h₁, h₂, e0, e1]
  exact (add_sub_add_right_eq_sub _ _ _).trans (map_sub χ.φ _ _).symm

theorem sum_single {O : Type} [CommRing O] (v : Fin g → O) (a : Fin g) (e : O) :
    ∑ c, v c * (Pi.single a e : Fin g → O) c = v a * e := by
  simp [Pi.single_apply]

theorem diff1 (h : C1 K.Oc) (hh : ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 →
      h T T'' (φ ≫ ψ) = ψ.φ (h T T' φ) + h T' T'' ψ) (k : K.K)
    (θ : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k))) (hθ : θ = h _ _ (jet0 k) - h _ _ (jet1 k)) (h0 : θ.fst = 0)
    {T : K.Obj} (f₁ f₂ : K.triv k ⟶ T) (a : Fin g) (e : T.C) (d₁ : f₁.deg = 0) (d₂ : f₂.deg = 0)
    (he : e ∈ T.J) (hee : e * e = 0)
    (hf : ∀ x : Hol (K.W k), f₂.φ x = f₁.φ x + f₁.φ (dw a x : Hol (K.W k)) * e) (u₁ u₂ : T.C)
    (h₁ : u₁ = h _ _ f₁) (h₂ : u₂ = h _ _ f₂) :
    u₁ - u₂ = f₁.φ (θ.snd a : Hol (K.W k)) * e := by
  have := diff K h hh k θ hθ f₁ f₂ (Pi.single a e) d₁ d₂
    (fun c ↦ by rw [Pi.single_apply]; split_ifs; exacts [he, T.J.zero_mem])
    (fun c d ↦ by
      rw [Pi.single_apply, Pi.single_apply]
      split_ifs
      exacts [hee, mul_zero _, zero_mul _, mul_zero _])
    (fun x ↦ (hf x).trans (congrArg (f₁.φ x + ·) (sum_single (fun c ↦ f₁.φ (dw c x : Hol (K.W k))) a e).symm)) u₁ u₂ h₁ h₂
  rw [this, h0, sum_single (fun c ↦ f₁.φ (θ.snd c : Hol (K.W k)))]
  exact (congrArg (· + _) (map_zero f₁.φ)).trans (zero_add _)

theorem units_mul_relation_rearrange_commRing {C : Type} [CommRing C] (u₀ u₁ u₂ u₃ A B A' B' A₂ B₁ e₁ e₂ : C) (h1 : u₀ - u₁ = A * e₁)
    (h2 : u₁ - u₃ = B₁ * e₂) (h3 : u₀ - u₂ = B * e₂) (h4 : u₂ - u₃ = A₂ * e₁) (h5 : B₁ = B + B' * e₁)
    (h6 : A₂ = A + A' * e₂) : (B' - A') * e₁ * e₂ = 0 := by
  subst h5 h6
  linear_combination -h1 - h2 + h3 + h4

theorem connForm_closed : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F) (h : C1 K.Oc), (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 → h T T'' (φ ≫ ψ) = ψ.φ (h T T' φ) + h T' T'' ψ) → ∀ (k : K.K) (θ : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k))), θ = h _ _ (jet0 k) - h _ _ (jet1 k) → θ.fst = 0 ∧ ∀ a b, dw a (θ.snd b) = dw b (θ.snd a) := by
  intro I _ g Λ _ F K h hh k θ hθ
  have h0 : θ.fst = 0 := by
    have := diff K h hh k θ hθ (𝟙 (K.triv k)) (𝟙 (K.triv k)) (fun _ ↦ 0) rfl rfl (fun _ ↦ (K.triv k).J.zero_mem)
      (fun _ _ ↦ mul_zero _) (fun x ↦ by simp only [mul_zero, Finset.sum_const_zero, add_zero]) _ _ rfl rfl
    simp only [mul_zero, Finset.sum_const_zero, add_zero, sub_self] at this
    exact this.symm
  refine ⟨h0, fun a b ↦ ?_⟩
  obtain ⟨T, φ₀, φ₁, φ₂, φ₃, e₁, e₂, d₀, d₁, d₂, d₃, m₁, m₂, s₁, s₂, p₁, p₂, p₃, p₄, inj⟩ :=
    exists_second_order_nbhd I g Λ F K k a b
  refine sub_eq_zero.1 (inj _ ?_)
  have := units_mul_relation_rearrange_commRing _ _ _ _ _ _ _ _ _ _ e₁ e₂
    (diff1 K h hh k θ hθ h0 φ₀ φ₁ a e₁ d₀ d₁ m₁ s₁ p₁ _ _ rfl rfl)
    (diff1 K h hh k θ hθ h0 φ₁ φ₃ b e₂ d₁ d₃ m₂ s₂ p₃ _ _ rfl rfl)
    (diff1 K h hh k θ hθ h0 φ₀ φ₂ b e₂ d₀ d₂ m₂ s₂ p₂ _ _ rfl rfl)
    (diff1 K h hh k θ hθ h0 φ₂ φ₃ a e₁ d₂ d₃ m₁ s₁ p₄ _ _ rfl rfl) (p₁ _) (p₂ _)
  exact (congrArg (· * e₁ * e₂) (map_sub φ₀.φ _ _)).trans this

end GlobalTheory.AnPer.ClosedSq
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.freeSheafHomValueAt_cechNerveSimplex_bijective : ∀ (R : Type) [CommRing R] (F : Shv R) (Y X : Scheme.{0}) (f : Y ⟶ X) (k : ℕ) (Z : Scheme.{0}) (x : Z ⟶ X) (y : Fin (k + 1) → (Z ⟶ Y)) (h : ∀ i, y i ≫ f = x), IsLimit (WidePullbackCone.mk (f := fun _ : Fin (k + 1) => f) x y h) → Function.Bijective (fun s : (free R).obj ((cech f).obj (op (SimplexCategory.mk k))) ⟶ F => GlobalTheory.EtC.val s Z (cechPt f k x y h)) := by
  intro R _ F Y X f k Z x y h hc
  have e : ∀ U : Scheme.{0}, Function.Bijective
      (fun g : U ⟶ Z => ((cech f).obj (op (SimplexCategory.mk k))).map g.op (cechPt f k x y h)) := by
    intro U
    have hb := CechPts.bij f k x y h hc U
    refine ⟨fun g g' hg => hb.1 ((CechPts.map_cechPt f k x y h g).symm.trans (hg.trans (CechPts.map_cechPt f k x y h g'))), fun v => ?_⟩
    obtain ⟨g, hg⟩ := hb.2 v
    exact ⟨g, (CechPts.map_cechPt f k x y h g).trans hg⟩
  let P := (cech f).obj (op (SimplexCategory.mk k))
  have evaluate (s : (free R).obj P ⟶ F) (U : Scheme.{0}) (v : P.obj (op U)) :
      val s U v =
        ((toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ s.hom).app (op U)).hom
          (ModuleCat.freeMk (ULift.up v)) := rfl
  have hext (s s' : (free R).obj P ⟶ F) (hs : ∀ U v, val s U v = val s' U v) : s = s' := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext _ _ _ F.property
    apply NatTrans.ext
    funext U
    apply ModuleCat.free_hom_ext
    rintro ⟨v⟩
    have hv := hs U.unop v
    rw [evaluate, evaluate] at hv
    exact hv
  have hex (φ : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U)
      (hφ : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (v : P.obj (op U)),
        φ V (P.map g.op v) = Sec.res g (φ U v)) :
      ∃ s : (free R).obj P ⟶ F, ∀ U v, val s U v = φ U v := by
    let s := GlobalTheory.EtC.FreeHom.desc P F φ hφ
    refine ⟨s, ?_⟩
    intro U v
    rw [evaluate]
    have hdesc : toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ s.hom =
        GlobalTheory.EtC.FreeHom.descP P F φ hφ := by
      have h := ((sheafificationAdjunction Scheme.etaleTopology.{0}
        (ModuleCat.{1} (ULift.{1} R))).homEquiv _ _).apply_symm_apply
          (GlobalTheory.EtC.FreeHom.descP P F φ hφ)
      rw [Adjunction.homEquiv_unit] at h
      exact h
    rw [hdesc]
    change (ModuleCat.freeDesc _).hom (ModuleCat.freeMk (ULift.up v)) = _
    erw [ModuleCat.freeDesc_apply]
    rfl
  have hnat (s : (free R).obj P ⟶ F) (V U : Scheme.{0}) (g : V ⟶ U) (v : P.obj (op U)) :
      val s V (P.map g.op v) = Sec.res g (val s U v) := by
    rw [evaluate, evaluate]
    let η := toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ s.hom
    change (η.app (op V)).hom (ModuleCat.freeMk (ULift.up (P.map g.op v))) =
      (F.obj.map g.op).hom ((η.app (op U)).hom (ModuleCat.freeMk (ULift.up v)))
    rw [← GlobalTheory.EtC.FreeHom.freePresheaf_map_freeMk P g.op v]
    exact congrArg (fun m => m.hom (ModuleCat.freeMk (ULift.up v))) (η.naturality g.op)
  constructor
  · intro s s' hs
    change val s Z (cechPt f k x y h) = val s' Z (cechPt f k x y h) at hs
    apply hext
    intro U v
    obtain ⟨g, rfl⟩ := (e U).2 v
    dsimp only
    rw [hnat s U Z g, hnat s' U Z g, hs]
  · intro a
    choose c hc0 using fun (U : Scheme.{0}) (v : ((cech f).obj (op (SimplexCategory.mk k))).obj (op U)) => (e U).2 v
    have hc' : ∀ (U : Scheme.{0}) (v : ((cech f).obj (op (SimplexCategory.mk k))).obj (op U)),
        ((cech f).obj (op (SimplexCategory.mk k))).map (c U v).op (cechPt f k x y h) = v := hc0
    obtain ⟨s, hs⟩ := hex (fun U v => Sec.res (c U v) a) (by
      intro V U g v
      have h1 : c V (((cech f).obj (op (SimplexCategory.mk k))).map g.op v) = g ≫ c U v := by
        apply (e V).1
        change ((cech f).obj (op (SimplexCategory.mk k))).map (c V _).op (cechPt f k x y h) =
          ((cech f).obj (op (SimplexCategory.mk k))).map (g ≫ c U v).op (cechPt f k x y h)
        rw [hc' V, op_comp, Functor.map_comp_apply, hc' U v]
      dsimp only
      rw [h1]
      simp [Sec.res])
    refine ⟨s, ?_⟩
    change val s Z (cechPt f k x y h) = a
    rw [hs]
    have h2 : c Z (cechPt f k x y h) = 𝟙 Z := by
      apply (e Z).1
      change ((cech f).obj (op (SimplexCategory.mk k))).map (c Z _).op (cechPt f k x y h) =
        ((cech f).obj (op (SimplexCategory.mk k))).map (𝟙 Z).op (cechPt f k x y h)
      rw [hc' Z, op_id, P.map_id]
      exact (types_id_apply (P.obj (op Z)) (cechPt f k x y h)).symm
    rw [h2]
    simp [Sec.res]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etaleFaithfullyFlat_descends_of_isColimit : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ (B : CommRingCat.{0}) (g : c.pt ⟶ B), EtFF g → ∃ (j : J) (B' : CommRingCat.{0}) (g' : D.obj j ⟶ B') (h : B' ⟶ B), EtFF g' ∧ IsPushout g' (c.ι.app j) h g := by
  first | (exact @GlobalTheory.EtC.etFF_descends_of_isColimit) | (exact GlobalTheory.EtC.etFF_descends_of_isColimit) | (intros; apply GlobalTheory.EtC.etFF_descends_of_isColimit  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.isEtaleCohomologyEquivalence_iff_elementwise : ∀ (R : Type) [CommRing R] (F : Shv R) (E E' : Spc) (f : E ⟶ E'), Eqv R f F ↔ SurjH ((HC R F).map f.op) ∧ InjH ((HC R F).map f.op) := by
  first | (exact @GlobalTheory.EtC.HCEqv.main) | (exact GlobalTheory.EtC.HCEqv.main) | (intros; apply GlobalTheory.EtC.HCEqv.main  <;> assumption)
end

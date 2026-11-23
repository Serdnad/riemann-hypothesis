module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle367
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle344
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAlgebraMapPadicInt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle321
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsLiftOfMemKO
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle373
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle374
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle016

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun
  GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime.CharDual

theorem exists_char_ne_zero (n : ℕ) (hn : n ≠ 0) {G : Type} [AddCommGroup G]
    (hG : ∀ g : G, n • g = 0) {g : G} (hg : g ≠ 0) : ∃ φ : G →+ ZMod n, φ g ≠ 0 := by
  haveI : NeZero n := ⟨hn⟩
  letI : Module (ZMod n) G := AddCommGroup.zmodModule hG
  obtain ⟨f, hf⟩ := GlobalTheory.ZModPerp.exists_dual_ne_zero (n := n) hg
  exact ⟨f.toAddMonoidHom, hf⟩

variable (A : Type) [CommRing A] (n : ℕ)

def charModule : Module A (A →+ ZMod n) where
  smul a φ := φ.comp (AddMonoidHom.mulLeft a)
  one_smul φ := by
    ext b
    show φ (1 * b) = φ b
    rw [one_mul]
  mul_smul a a' φ := by
    ext b
    show φ (a * a' * b) = φ (a' * (a * b))
    rw [mul_left_comm, mul_assoc]
  smul_zero a := by ext b; rfl
  smul_add a φ ψ := by ext b; rfl
  add_smul a a' φ := by
    ext b
    show φ ((a + a') * b) = φ (a * b) + φ (a' * b)
    rw [add_mul, map_add (f := _)]
  zero_smul φ := by
    ext b
    show φ (0 * b) = 0
    rw [zero_mul, map_zero]

end GlobalTheory.NewPrime.CharDual

namespace GlobalTheory.NewPrime


open GlobalTheory.NewPrime.CharDual in
theorem charDual_cogenerator : ∀ (A : Type) [CommRing A] [Finite A] (n : ℕ), n ≠ 0 → (n : A) = 0 →
    ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module A Y) (_ : Finite Y) (β : Y →+ A →+ ZMod n),
      Perf A β ∧ ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) A) (v : Fin a → A),
        (∀ x : Fin a → Y, matAct Φ x = 0 → ∑ j, v j • x j = 0) → v ∈ what₂ Φ := by
  intro A _ _ n hn hnA
  haveI : NeZero n := ⟨hn⟩
  letI : Module A (A →+ ZMod n) := charModule A n
  haveI : Finite (A →+ ZMod n) :=
    Finite.of_injective (fun φ : A →+ ZMod n => (φ : A → ZMod n)) DFunLike.coe_injective
  refine ⟨A →+ ZMod n, inferInstance, inferInstance, inferInstance, AddMonoidHom.id _, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro a y y'
    rfl
  · intro y hy
    ext b
    exact hy b
  · intro y' hy'
    by_contra h
    obtain ⟨φ, hφ⟩ := exists_char_ne_zero n hn (G := A) (fun g => by
      rw [nsmul_eq_mul, hnA, zero_mul]) h
    exact hφ (hy' φ)
  · intro a Φ v hv
    by_contra hvr
    set Q := (Fin a → A) ⧸ what₂ Φ
    have hQ : ∀ q : Q, n • q = 0 := by
      intro q
      induction q using Submodule.Quotient.induction_on with
      | H w =>
        show n • (Submodule.Quotient.mk w : Q) = 0
        rw [← Nat.cast_smul_eq_nsmul A, ← Submodule.Quotient.mk_smul, hnA, zero_smul,
          Submodule.Quotient.mk_zero]
    have hmk : (Submodule.Quotient.mk v : Q) ≠ 0 := by
      rwa [Ne, Submodule.Quotient.mk_eq_zero]
    obtain ⟨ψ, hψ⟩ := exists_char_ne_zero n hn hQ hmk
    let L : (Fin a → A) →+ ZMod n := ψ.comp (what₂ Φ).mkQ.toAddMonoidHom
    let x : Fin a → (A →+ ZMod n) := fun j => L.comp (AddMonoidHom.single (fun _ => A) j)
    have key : ∀ (w : Fin a → A) (b : A), (∑ j, w j • x j) b = L (fun k => w k * b) := by
      intro w b
      have hsum (s : Finset (Fin a)) : (∑ j ∈ s, w j • x j) b = ∑ j ∈ s, (w j • x j) b := by
        classical
        induction s using Finset.induction_on with
        | empty => simp
        | @insert j s hj ih => simp [hj, ih]
      rw [hsum]
      have : (fun k => w k * b) = ∑ j, Pi.single j (w j * b) := (Finset.univ_sum_single _).symm

      rw [this, map_sum]
      rfl
    have hx : matAct Φ x = 0 := by
      funext i
      ext b
      show (∑ j, Φ i j • x j) b = 0
      rw [key]
      have : (fun k => Φ i k * b) = b • Φ i := by
        funext k
        simp [mul_comm]
      rw [this]
      have hmem : b • Φ i ∈ what₂ Φ := Submodule.smul_mem _ b (Submodule.subset_span ⟨i, rfl⟩)
      show ψ (Submodule.Quotient.mk _) = 0
      rw [(Submodule.Quotient.mk_eq_zero _).2 hmem, map_zero]
    have h1 := congrArg (fun f : A →+ ZMod n => f 1) (hv x hx)
    rw [key] at h1
    simp only [mul_one] at h1
    exact hψ h1

end GlobalTheory.NewPrime
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
open GlobalTheory.ResSel.CoefMap

namespace GlobalTheory.NewPrime.ScalarChange

section General

variable {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {M : Type} [AddCommGroup M] [Module R M] [Module R' M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousConstSMul R M] [ContinuousConstSMul R' M]
  (hs : ∀ (a : R) (m : M), a • m = σ a • m)
  (rho : Representation R Γ M) (rho' : Representation R' Γ M) (he : ∀ g m, rho g m = rho' g m)

def idSl : M →ₛₗ[σ] M where
  toFun m := m
  map_add' _ _ := rfl
  map_smul' c m := hs c m

def tr : H1 rho →ₛₗ[σ] H1 rho' :=
  slH1 rho rho' (idSl σ hs) continuous_id he

def back (z : Z1 rho') : Z1 rho :=
  ⟨z.1, z.2.1, fun g h => by rw [z.2.2, he]⟩

theorem tr_back (z : Z1 rho') :
    tr σ hs rho rho' he (Submodule.Quotient.mk (back rho rho' he z)) = Submodule.Quotient.mk z :=
  congrArg Submodule.Quotient.mk (Subtype.ext rfl)

theorem tr_injective : Function.Injective (tr σ hs rho rho' he) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    have h1 : (Submodule.Quotient.mk (semilinearCoefficientMapCocycles rho rho' (idSl σ hs) continuous_id he z) : H1 rho') = 0 := hx
    rw [Submodule.Quotient.mk_eq_zero] at h1 ⊢
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 h1
    refine (mem_coboundaries1 _ _).2 ⟨m, fun g => ?_⟩
    rw [he]
    exact hm g

theorem res_tr {H : Type} [Group H] [TopologicalSpace H] (phi : H →* Γ) (hphi : Continuous phi) (x : H1 rho) :
    resH1 rho' phi hphi (tr σ hs rho rho' he x) =
      tr σ hs (rho.comp phi) (rho'.comp phi) (fun g m => he (phi g) m) (resH1 rho phi hphi x) :=
  res_slH1 rho rho' (idSl σ hs) continuous_id he phi hphi x

theorem of_tr_mem_ur (J : Subgroup Γ) (x : H1 rho) (hx : tr σ hs rho rho' he x ∈ H1ur rho' J) : x ∈ H1ur rho J := by
  have h0 : resH1 rho' J.subtype continuous_subtype_val (tr σ hs rho rho' he x) = 0 := hx
  have h1 := res_tr σ hs rho rho' he J.subtype continuous_subtype_val x
  exact tr_injective σ hs (rho.comp J.subtype) (rho'.comp J.subtype) (fun g m => he g.1 m)
    (h1.symm.trans (h0.trans (map_zero _).symm))

end General

section Coef

variable {O Λ Λ' : Type} [CommRing O] [CommRing Λ] [Algebra O Λ] [CommRing Λ'] [Algebra O Λ'] (φ : Λ →ₐ[O] Λ')
  {Y : Type} [AddCommGroup Y] [Module Λ Y] [Module Λ' Y] (hY : ∀ (a : Λ) (y : Y), a • y = φ a • y)

include hY in
theorem algebraMap_smul (c : O) (y : Y) : algebraMap O Λ c • y = algebraMap O Λ' c • y := by
  rw [hY, φ.commutes]

include hY in
theorem vec_smul {r : ℕ} (a : Λ) (m : Fin r → Y) : a • m = φ a • m :=
  funext fun c => hY a (m c)

include hY in
theorem repOn_eq_repOn {Γ : Type} [Group Γ] {r : ℕ} (ρ : Γ →* GL (Fin r) O) (κ : Γ →* Λˣ) (κ' : Γ →* Λ'ˣ)
    (hκ : ∀ g, ((κ' g : Λ'ˣ) : Λ') = φ (κ g : Λˣ)) (g : Γ) (m : Fin r → Y) :
    repOn ρ κ Y g m = repOn ρ κ' Y g m := by
  funext a
  change ((κ g : Λˣ) : Λ) • ∑ j, algebraMap O Λ ((ρ g : Matrix (Fin r) (Fin r) O) a j) • m j =
    ((κ' g : Λ'ˣ) : Λ') • ∑ j, algebraMap O Λ' ((ρ g : Matrix (Fin r) (Fin r) O) a j) • m j
  simp only [algebraMap_smul φ hY]
  rw [hY, hκ]

end Coef

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) {r : ℕ} (ρ : GE N →* GL (Fin r) (X.O0 i))
  {Λ Λ' : Type} [CommRing Λ] [Algebra (X.O0 i) Λ] [CommRing Λ'] [Algebra (X.O0 i) Λ']
  (φ : Λ →ₐ[X.O0 i] Λ') (κ : GE N →* Λˣ) (κ' : GE N →* Λ'ˣ) (hκ : ∀ g, ((κ' g : Λ'ˣ) : Λ') = φ (κ g : Λˣ))
  {Y : Type} [AddCommGroup Y] [Module Λ Y] [Module Λ' Y] [TopologicalSpace Y] [DiscreteTopology Y]
  (hY : ∀ (a : Λ) (y : Y), a • y = φ a • y)

abbrev trG : H1 (repOn ρ κ Y) →ₛₗ[(φ : Λ →+* Λ')] H1 (repOn ρ κ' Y) :=
  tr (φ : Λ →+* Λ') (vec_smul φ hY) (repOn ρ κ Y) (repOn ρ κ' Y) (repOn_eq_repOn φ hY ρ κ κ' hκ)

abbrev trL (v : PlE D.host) :
    H1 ((repOn ρ κ Y).comp (DecV N v).subtype) →ₛₗ[(φ : Λ →+* Λ')] H1 ((repOn ρ κ' Y).comp (DecV N v).subtype) :=
  tr (φ : Λ →+* Λ') (vec_smul φ hY) ((repOn ρ κ Y).comp (DecV N v).subtype) ((repOn ρ κ' Y).comp (DecV N v).subtype)
    (fun g m => repOn_eq_repOn φ hY ρ κ κ' hκ g.1 m)

theorem trL_mem_bkOn (v : PlE D.host) (x : H1 ((repOn ρ κ Y).comp (DecV N v).subtype))
    (hx : x ∈ bkOn bkP i ρ κ Y v) : trL i ρ φ κ κ' hκ hY v x ∈ bkOn bkP i ρ κ' Y v := by
  unfold bkOn at hx ⊢
  split_ifs at hx ⊢ with hv
  · induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, c, y, b, hc, hy, hz, rfl⟩ := hx
      refine Submodule.subset_span ⟨semilinearCoefficientMapCocycles _ _ (idSl (φ : Λ →+* Λ') (vec_smul φ hY)) continuous_id
        (fun g m => repOn_eq_repOn φ hY ρ κ κ' hκ g.1 m) z, c, y, b, hc, hy, fun g a => ?_, rfl⟩
      change ((z : ↥(DecV N v) → Fin r → Y) g a) = _
      rw [hz, algebraMap_smul φ hY]
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
  · rw [Submodule.mem_bot] at hx ⊢
    rw [hx, map_zero]

theorem exists_mem_bkOn (v : PlE D.host) (x' : H1 ((repOn ρ κ' Y).comp (DecV N v).subtype))
    (hx : x' ∈ bkOn bkP i ρ κ' Y v) : ∃ w ∈ bkOn bkP i ρ κ Y v, trL i ρ φ κ κ' hκ hY v w = x' := by
  by_cases hv : v ∈ placesOver D.host.E (X.l i)
  · have H : ∀ a : Λ', ∃ w ∈ bkOn bkP i ρ κ Y v, trL i ρ φ κ κ' hκ hY v w = a • x' := by
      unfold bkOn at hx
      rw [dite_eq_left hv] at hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        intro a
        obtain ⟨z, c, y, b, hc, hy, hz, rfl⟩ := hx
        refine ⟨Submodule.Quotient.mk (back ((repOn ρ κ Y).comp (DecV N v).subtype) ((repOn ρ κ' Y).comp (DecV N v).subtype)
          (fun g m => repOn_eq_repOn φ hY ρ κ κ' hκ g.1 m) (a • z)), ?_,
          tr_back _ _ _ _ _ _⟩
        unfold bkOn
        rw [dite_eq_left hv]
        refine Submodule.subset_span ⟨back ((repOn ρ κ Y).comp (DecV N v).subtype) ((repOn ρ κ' Y).comp (DecV N v).subtype)
          (fun g m => repOn_eq_repOn φ hY ρ κ κ' hκ g.1 m) (a • z), c, y, a • b, hc, hy,
            fun g e => ?_, rfl⟩
        change a • ((z : ↥(DecV N v) → Fin r → Y) g e) = _
        rw [hz, algebraMap_smul φ hY, smul_comm]
      | zero => exact fun a => ⟨0, Submodule.zero_mem _, by rw [map_zero, smul_zero]⟩
      | add x y _ _ hx hy =>
        intro a
        obtain ⟨w, hw, e⟩ := hx a
        obtain ⟨w', hw', e'⟩ := hy a
        exact ⟨w + w', Submodule.add_mem _ hw hw', by rw [map_add (f := _), e, e', smul_add]⟩
      | smul c x _ hx =>
        intro a
        obtain ⟨w, hw, e⟩ := hx (a * c)
        exact ⟨w, hw, by rw [e, mul_smul]⟩
    simpa using H 1
  · unfold bkOn at hx
    rw [dite_eq_right hv, Submodule.mem_bot] at hx
    exact ⟨0, Submodule.zero_mem _, by rw [map_zero, hx]⟩

theorem trG_mem_selOn (Q : Finset (PlE D.host)) (x : H1 (repOn ρ κ Y)) (hx : x ∈ selOn bkP i ρ κ Y Q) :
    trG i ρ φ κ κ' hκ hY x ∈ selOn bkP i ρ κ' Y Q := by
  refine (mem_Sel _ _ _ _ _).2 fun v => ?_
  have hv := (mem_Sel _ _ _ _ _).1 hx v
  refine (res_tr (φ : Λ →+* Λ') (vec_smul φ hY) (repOn ρ κ Y) (repOn ρ κ' Y) (repOn_eq_repOn φ hY ρ κ κ' hκ)
    (Dec (F := D.host.E) (N.plOm.1 v)).subtype continuous_subtype_val x) ▸ ?_
  unfold Formalism.GaloisCohomology.bkCond at hv ⊢
  split_ifs at hv ⊢ with h1 h2
  · exact trL_mem_bkOn bkP i ρ φ κ κ' hκ hY v _ hv
  · exact Submodule.mem_top
  · exact slH1_ur _ _ _ _ _ _ _ hv

theorem of_trG_mem_selOn (Q : Finset (PlE D.host)) (x : H1 (repOn ρ κ Y))
    (hx : trG i ρ φ κ κ' hκ hY x ∈ selOn bkP i ρ κ' Y Q) : x ∈ selOn bkP i ρ κ Y Q := by
  refine (mem_Sel _ _ _ _ _).2 fun v => ?_
  have hv := (mem_Sel _ _ _ _ _).1 hx v
  have e := res_tr (φ : Λ →+* Λ') (vec_smul φ hY) (repOn ρ κ Y) (repOn ρ κ' Y) (repOn_eq_repOn φ hY ρ κ κ' hκ)
    (Dec (F := D.host.E) (N.plOm.1 v)).subtype continuous_subtype_val x
  have hv' : trL i ρ φ κ κ' hκ hY v (resH1 (repOn ρ κ Y) (Dec (F := D.host.E) (N.plOm.1 v)).subtype continuous_subtype_val x) ∈
      Formalism.GaloisCohomology.bkCond (repOn ρ κ' Y) N.plOm (X.l i) (Spl i ∪ ↑Q) (bkOn bkP i ρ κ' Y) v := e ▸ hv
  unfold Formalism.GaloisCohomology.bkCond at hv' ⊢
  split_ifs at hv' ⊢ with h1 h2
  · obtain ⟨w, hw, e'⟩ := exists_mem_bkOn bkP i ρ φ κ κ' hκ hY v _ hv'
    rwa [← tr_injective _ _ _ _ _ e']
  · exact Submodule.mem_top
  · exact of_tr_mem_ur _ _ _ _ _ _ _ hv'

theorem selC_transfer : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (Λ : Type) [CommRing Λ] [Algebra (X.O0 i) Λ] (Λ' : Type) [CommRing Λ'] [Algebra (X.O0 i) Λ'] (φ : Λ →ₐ[X.O0 i] Λ') (κ : GE N →* Λˣ) (κ' : GE N →* Λ'ˣ), (∀ g, ((κ' g : Λ'ˣ) : Λ') = φ (κ g : Λˣ)) → ∀ (Y : Type) [AddCommGroup Y] [Module Λ Y] [Module Λ' Y] [TopologicalSpace Y] [DiscreteTopology Y], (∀ (a : Λ) (y : Y), a • y = φ a • y) → (∀ g m, repOn (Tgl i s) κ Y g m = repOn (Tgl i s) κ' Y g m) ∧ ∀ Q f, SelC bkP i s κ Y Q f ↔ SelC bkP i s κ' Y Q f := by
  intro D N X bkP i s Λ _ _ Λ' _ _ φ κ κ' hκ Y _ _ _ _ _ hY
  refine ⟨repOn_eq_repOn φ hY (Tgl i s) κ κ' hκ, fun Q f => ⟨?_, ?_⟩⟩
  · rintro ⟨z, rfl, hz⟩
    exact ⟨semilinearCoefficientMapCocycles _ _ (idSl (φ : Λ →+* Λ') (vec_smul φ hY)) continuous_id (repOn_eq_repOn φ hY (Tgl i s) κ κ' hκ) z, rfl,
      trG_mem_selOn bkP i (Tgl i s) φ κ κ' hκ hY Q _ hz⟩
  · rintro ⟨z, rfl, hz⟩
    refine ⟨back _ _ (repOn_eq_repOn φ hY (Tgl i s) κ κ' hκ) z, rfl,
      of_trG_mem_selOn bkP i (Tgl i s) φ κ κ' hκ hY Q _ ?_⟩
    have e := tr_back (φ : Λ →+* Λ') (vec_smul φ hY) (repOn (Tgl i s) κ Y) (repOn (Tgl i s) κ' Y)
      (repOn_eq_repOn φ hY (Tgl i s) κ κ' hκ) z
    exact e ▸ hz

end GlobalTheory.NewPrime.ScalarChange

end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime.PairEquiv

section General

variable {A : Type} [CommRing A] {Y Y' : Type} [AddCommGroup Y] [Module A Y] [AddCommGroup Y'] [Module A Y'] {n r : ℕ}

theorem vecPair_matAct {β : Y →+ Y' →+ ZMod n} (hβ : Bal A β) (T : Matrix (Fin r) (Fin r) A) (x : Fin r → Y)
    (y : Fin r → Y') : vecPair r β (matAct T x) y = vecPair r β x (matAct T.transpose y) := by
  rw [vecPair_apply, vecPair_apply]
  change ∑ c, β (∑ a, T c a • x a) (y c) = ∑ a, β (x a) (∑ c, T c a • y c)

  simp only [map_sum, AddMonoidHom.finsetSum_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => hβ _ _ _

theorem vecPair_smul {β : Y →+ Y' →+ ZMod n} (hβ : Bal A β) (k : A) (x : Fin r → Y)
    (y : Fin r → Y') : vecPair r β (k • x) y = vecPair r β x (k • y) := by
  rw [vecPair_apply, vecPair_apply]
  exact Finset.sum_congr rfl fun a _ => hβ _ _ _

theorem tors_of_finite [IsLocalRing A] [Finite A] (b : Y) :
    ∃ m, ∀ x ∈ IsLocalRing.maximalIdeal A ^ m, x • b = 0 := by
  obtain ⟨m, hm⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
  rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top] at hm
  refine ⟨m, fun x hx => ?_⟩
  rw [hm, Ideal.zero_eq_bot, Ideal.mem_bot] at hx
  rw [hx, zero_smul]

theorem map_padicInt_eq_val {l : ℕ} [Fact l.Prime] (f : ℤ_[l] →+* A) {m : ℕ} (h : (l : A) ^ m = 0) (a : ℤ_[l]) :
    f a = ((PadicInt.toZModPow m a).val : A) := by
  have h1 : a - ((PadicInt.toZModPow m a).val : ℤ_[l]) ∈ RingHom.ker (PadicInt.toZModPow m) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h1
  obtain ⟨c, hc⟩ := h1
  have h2 := congrArg f hc
  rw [map_sub, map_natCast, map_mul, map_pow, map_natCast, h, zero_mul, sub_eq_zero] at h2
  exact h2

end General

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem transpose_mul_Tdual (i : X.Tw) (s : X.Sig i) (g : GE N) :
    (Tmat i s g).transpose * Tdual i s g = ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) • 1 := by
  have h3 : IsUnit (Tmat i s g).det := by
    rw [← Tgl_coe]; exact Matrix.isUnits_det_units _
  rw [Tdual, Matrix.mul_smul, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ h3, Matrix.transpose_one]

theorem pairing_equivariant : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Setup bkP i s κ Q → Kills i A → IsDual i s ρ → ∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] (Y' : Type) [AddCommGroup Y'] [Module A Y'] [TopologicalSpace Y'] [DiscreteTopology Y'] (β : Y →+ Y' →+ ZMod (X.l i ^ (nu X i + 1))), Bal A β → ContAction (repOn (Tgl i s) κ Y) ∧ ContAction (repOn ρ κ⁻¹ Y') ∧ (∀ g x y, vecPair D.R.r β (repOn (Tgl i s) κ Y g x) (repOn ρ κ⁻¹ Y' g y) = ((cycMod D.host.E N.Om (X.l i) (nu X i + 1) g : (ZMod (X.l i ^ (nu X i + 1)))ˣ) : ZMod (X.l i ^ (nu X i + 1))) * vecPair D.R.r β x y) ∧ ∀ v, v ∉ placesOver D.host.E (X.l i) → v ∉ Spl i → v ∉ Q → ∀ B : ValuationSubring N.Om, IsPlaceOver B v → ∀ τ ∈ Ine (F := D.host.E) B, repOn (Tgl i s) κ Y τ = 1 ∧ repOn ρ κ⁻¹ Y' τ = 1 := by
  intro D N X bkP i s A _ _ _ _ κ Q ρ hS hK hρ Y _ _ _ _ Y' _ _ _ _ β hβ
  have := hS.2.1
  have hκ := hS.2.2.2.1
  refine ⟨?_, ?_, fun g x y => ?_, fun v hl hv hQ B hB τ hτ => ?_⟩
  · refine GlobalTheory.PrimeToInertia.contAction_repOn (X.twistBaseCoefficientRing_isAdic i) _ ?_ κ hκ tors_of_finite
    simp_rw [Tgl_coe]; exact GlobalTheory.PrimeToInertia.continuous_Tmat i s
  · refine GlobalTheory.PrimeToInertia.contAction_repOn (X.twistBaseCoefficientRing_isAdic i) _ ?_ κ⁻¹ ?_ tors_of_finite
    · simp_rw [hρ _]; exact GlobalTheory.PrimeToInertia.continuous_Tdual i s
    · convert hκ using 2
      ext g
      simp [MonoidHom.mem_ker]
  · have hl : ((X.l i : ℕ) : A) ^ (nu X i + 1) = 0 := by
      have := hK ((X.l i : X.O0 i) ^ nu X i * (X.l i : X.O0 i))
        (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) (GlobalTheory.PrimeToInertia.l_mem i))
      rwa [map_mul, map_pow, map_natCast, ← pow_succ] at this
    have he : algebraMap (X.O0 i) A ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) =
        (((cycMod D.host.E N.Om (X.l i) (nu X i + 1) g : (ZMod (X.l i ^ (nu X i + 1)))ˣ) : ZMod (X.l i ^ (nu X i + 1))).val : A) :=
      map_padicInt_eq_val ((algebraMap (X.O0 i) A).comp (algebraMap ℤ_[X.l i] (X.O0 i))) hl _
    change vecPair _ β ((κ g : A) • matAct ((Tgl i s g : Matrix _ _ (X.O0 i)).map (algebraMap (X.O0 i) A)) x)
      (((κ g)⁻¹ : Aˣ).val • matAct ((ρ g : Matrix _ _ (X.O0 i)).map (algebraMap (X.O0 i) A)) y) = _
    rw [vecPair_smul hβ, smul_smul, Units.mul_inv, one_smul, vecPair_matAct hβ, ← Module.End.mul_apply, ← matAct_mul,
      ← Matrix.transpose_map, ← Matrix.map_mul, hρ, Tgl_coe, transpose_mul_Tdual]
    have e : matAct ((((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) • (1 : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i))).map
        (algebraMap (X.O0 i) A)) y =
        ((cycMod D.host.E N.Om (X.l i) (nu X i + 1) g : (ZMod (X.l i ^ (nu X i + 1)))ˣ) : ZMod (X.l i ^ (nu X i + 1))).val • y := by
      funext a
      rw [← Nat.cast_smul_eq_nsmul A, ← he]
      change ∑ b, algebraMap (X.O0 i) A (((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) * (1 : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) a b) • y b = _
      simp [Matrix.one_apply, apply_ite (algebraMap (X.O0 i) A), ite_smul]
    rw [e, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]
  · have h1 := GlobalTheory.SelFun.Colim.tgl_eq_one bkP i s hS.1.1 v hl hv B hB τ hτ
    have h2 := hS.2.2.2.2.2.2.2 v hQ B hB τ hτ
    have h3 : cycZ D.host.E N.Om (X.l i) τ = 1 := by
      refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
      rw [cycZ_toZModPow_eq hl hB (q := 1) (fun x hx => by simpa using hτ.2 x hx) n]
      simp
    have h4 : eps0 X i τ = 1 := by
      rw [eps0, MonoidHom.comp_apply, h3, map_one]
    have h5 : ρ τ = 1 := by
      apply Units.ext
      rw [hρ, Tdual, h4, ← Tgl_coe, h1]
      simp
    exact ⟨LinearMap.ext (GlobalTheory.SelFun.Colim.repOn_eq_of_eq_one _ _ h1 h2),
      LinearMap.ext (GlobalTheory.SelFun.Colim.repOn_eq_of_eq_one _ _ h5 (by simp [h2]))⟩

end GlobalTheory.NewPrime.PairEquiv
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.parabolicInduction_emptySecond_isSubquotient_first : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (r : ℕ) (c : Bool → ℕ) (f : (Σ j, Fin (c j)) ≃ Fin r) (s : ∀ j, IrrRep (GL (Fin (c j)) F)), c true = 0 → ∃ φ : Fin r ≃ Fin (c false), IsSubquotient (multiProd f fun j => (s j).ρ) ((s false).ρ.comp (reix F φ) : Representation ℂ (GL (Fin r) F) (s false).V) := by
  first | exact @GlobalTheory.EmptySecondBlockProd.isSubquotient_multiProd | exact GlobalTheory.EmptySecondBlockProd.isSubquotient_multiProd | (intros; apply GlobalTheory.EmptySecondBlockProd.isSubquotient_multiProd <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.jacquetSubquotient_firstFactor_of_emptySecondBlock : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (r : ℕ) (c : Bool → ℕ) (f : (Σ j, Fin (c j)) ≃ Fin r) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin r) F) V) (s : ∀ j, IrrRep (GL (Fin (c j)) F)), c true = 0 → IsSubquotient (piTensor fun j => (s j).ρ) (jac f π) → ∃ φ : Fin r ≃ Fin (c false), IsSubquotient ((s false).ρ.comp (reix F φ) : Representation ℂ (GL (Fin r) F) (s false).V) π := by
  first | exact @GlobalTheory.EmptySecondBlock.isSubquotient_of_empty_second_block | exact GlobalTheory.EmptySecondBlock.isSubquotient_of_empty_second_block | (intros; apply GlobalTheory.EmptySecondBlock.isSubquotient_of_empty_second_block <;> assumption)
end

section


theorem _root_.GlobalTheory.T.eq_zero_of_forall_letterType_functional : ∀ {L U D F k : Type} [Field L] [Field U] [AddCommGroup D] [Module L D] (m : U →+* Module.End L D) [Field F] [Field k] [Algebra k L] [Algebra k U] [Algebra k F] [Algebra U F] [IsScalarTower k U F] [IsAlgClosed F] [FiniteDimensional k L] [Algebra.IsSeparable k L] [Module U D] [FiniteDimensional U D], (∀ (c : U) (x : D), c • x = m c x) → (∀ (c : k) (x : D), m (algebraMap k U c) x = algebraMap k L c • x) → ∀ x : D, (∀ s : L →ₐ[k] F, ∀ f ∈ GlobalTheory.Pst.LetterDim.letterHom m (s : L →+* F) (algebraMap U F), f x = 0) → x = 0 := by
  first | exact @GlobalTheory.LetterSep.eq_zero_of_forall_letterHom | exact GlobalTheory.LetterSep.eq_zero_of_forall_letterHom | (intros; apply GlobalTheory.LetterSep.eq_zero_of_forall_letterHom <;> assumption)
end

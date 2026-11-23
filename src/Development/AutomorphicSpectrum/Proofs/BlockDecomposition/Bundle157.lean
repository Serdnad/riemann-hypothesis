module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle128
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle132
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle138
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MemBoundariesZeroIff
public import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle093
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle135
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle111
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.InstAddCommGroup
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.FaceMapCompSuccAboveCastSucc
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HarishChandraFormulaStatement
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle136
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageCochainExists
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace GlobalTheory.CompanionTheory.LocBC

variable {R R' : Type} [CommRing R] [CommRing R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {Φ : PDF R C} {Φ' : PDF R' C'} {σ : R →+* R'} (m : SMor Φ Φ' σ)

section Cuts

variable {d : ℕ} (E : Frame (Φ := Φ) (d + 1)) (E' : Frame (Φ := Φ') (d + 1)) (e : E.D ⟶ m.G.obj E'.D)
  (he : m.Fr E E' e) (hρ : ∀ T, Function.Injective (m.ρ T)) (Q : Poly Φ) (Q' : Poly Φ')

theorem le_cover_restrict_compat {c : R'} {a : IdF Φ.A} {a' : IdF Φ'.A} (h : m.LeC c a a') :
    (m1 m E E' e he hρ).LeC c (a.res (Cut.U E)) (a'.res (Cut.U E')) := fun T x hx => h T.T x hx

theorem pull_restrict_first_piece_compat (c : R') {a b : IdF Φ.A} {a' b' : IdF Φ'.A} (ha : m.LeC c a a') (hb : m.LeC c b b') (j : ℕ)
    (x : CH.H (sq (a.res (Cut.U E)) (b.res (Cut.U E))) j) :
    (mP m E E' e he hρ Q Q' c ha hb).pull j
        ((CH.Mor.restrict (sq (a.res (Cut.U E)) (b.res (Cut.U E))) (Cut.P0 Q)).pull j x) =
      (CH.Mor.restrict (sq (a'.res (Cut.U E')) (b'.res (Cut.U E'))) (Cut.P0 Q')).pull j
        (((m1 m E E' e he hρ).sqC c (le_cover_restrict_compat m E E' e he hρ ha) (le_cover_restrict_compat m E E' e he hρ hb)).pull j x) := by
  let μ₁ : CH.Mor (sq (a.res (Cut.U E)) (b.res (Cut.U E))) (Cut.P0 Q' ⋙ Cut.U E' ⋙ sq a' b') σ :=
    (CH.Mor.restrict (sq (a.res (Cut.U E)) (b.res (Cut.U E))) (Cut.P0 Q)).comp (mP m E E' e he hρ Q Q' c ha hb)
  let μ₂ : CH.Mor (sq (a.res (Cut.U E)) (b.res (Cut.U E))) (Cut.P0 Q' ⋙ Cut.U E' ⋙ sq a' b') σ :=
    ((m1 m E E' e he hρ).sqC c (le_cover_restrict_compat m E E' e he hρ ha) (le_cover_restrict_compat m E E' e he hρ hb)).comp
      (CH.Mor.restrict (sq (a'.res (Cut.U E')) (b'.res (Cut.U E'))) (Cut.P0 Q'))
  have h := CrystallineSemistableComparison.P.prism μ₁ μ₂ (eta m E E' e he hρ Q Q') (fun T x => rfl) j x
  exact (CrystallineSemistableComparison.P.pull_comp _ _ j x).1.symm.trans (h.trans (CrystallineSemistableComparison.P.pull_comp _ _ j x).1)

def alpha {d : ℕ} {E : Frame (Φ := Φ) (d + 1)} (Q : Poly Φ) (a b : IdF Φ.A) : Pt.U E ⋙ sq a b ⟶ Cut.P0 Q ⋙ Cut.U E ⋙ sq a b :=
  Functor.whiskerRight (Cut.jNat (E := E) Q) (sq a b)

theorem alpha_τ (c : R') {a b : IdF Φ.A} {a' b' : IdF Φ'.A} (ha : m.LeC c a a') (hb : m.LeC c b b') (X : Pt E')
    (y : sqM a b (m.G.obj X.T)) :
    (mP m E E' e he hρ Q Q' c ha hb).τ X (((alpha Q a b).app ((Gp m E E' e).obj X)).hom y) =
      ((alpha Q' a' b').app X).hom ((mPt m E E' e c ha hb).τ X y) := by
  change (m.sqC c ha hb).τ (Q'.P X.T) (((sq a b).map (etaC m E E' e he hρ Q Q' X).1).hom
      (((sq a b).map (Q.j (m.G.obj X.T))).hom y)) = ((sq a' b').map (Q'.j X.T)).hom ((m.sqC c ha hb).τ X.T y)
  rw [← (m.sqC c ha hb).nat]
  congr 1
  have h2 := congrArg (fun t => ((sq a b).map t).hom y) (j_eta m E E' e he hρ Q Q' X)
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  exact h2

theorem alpha_hom (c : R') {a b : IdF Φ.A} {a' b' : IdF Φ'.A} (ha : m.LeC c a a') (hb : m.LeC c b b') (k : ℕ)
    (x : CH.Cn (Pt.U E ⋙ sq a b) k) :
    (mP m E E' e he hρ Q Q' c ha hb).hom.f k ((CH.Mor.ofNatTrans (alpha Q a b)).hom.f k x) =
      (CH.Mor.ofNatTrans (alpha Q' a' b')).hom.f k ((mPt m E E' e c ha hb).hom.f k x) :=
  funext fun s => alpha_τ m E E' e he hρ Q Q' c ha hb _ _

theorem rho_finsupp_sum_dpow (c : R') {T P' : C'} (jj : T ⟶ P') (η : Q.P (m.G.obj T) ⟶ m.G.obj P') (X' : Φ'.A.obj P')
    (hj : Q.j (m.G.obj T) ≫ η = m.G.map jj) (hx : m.ρ P' ((Φ.A.map η).hom (Q.X (m.G.obj T))) = X')
    (cc : ℕ →₀ Φ.A.obj (m.G.obj T)) :
    algebraMap R' (Φ'.A.obj P') c * m.ρ P' ((Φ.A.map η).hom
        (cc.sum fun k y => (Φ.A.map (Q.j (m.G.obj T))).hom y * Φ.dp k (Q.X (m.G.obj T)))) =
      (cc.mapRange (fun x => algebraMap R' (Φ'.A.obj T) c * m.ρ T x) (by simp)).sum
        fun k y => (Φ'.A.map jj).hom y * Φ'.dp k X' := by
  rw [Finsupp.sum_mapRange_index (by intro k; simp), map_finsuppSum, map_finsuppSum, Finsupp.mul_sum]
  refine Finsupp.sum_congr fun k _ => ?_
  have hX := Q.X_mem (m.G.obj T)
  have hX' := Φ.J.map_mem η hX
  have h1 : (Φ.A.map η).hom ((Φ.A.map (Q.j (m.G.obj T))).hom (cc k)) = (Φ.A.map (m.G.map jj)).hom (cc k) := by
    rw [← Cut.mapA_comp, hj]
  rw [map_mul, map_mul, h1, m.nat, Φ.dp_map _ _ hX, m.dp _ _ hX', hx, map_mul, AlgHom.commutes, mul_assoc]

theorem rho_sum (c : R') (X : Pt E') (cc : ℕ →₀ Φ.A.obj (m.G.obj X.T)) :
    algebraMap R' (Φ'.A.obj (Q'.P X.T)) c * m.ρ (Q'.P X.T) ((Φ.A.map (etaC m E E' e he hρ Q Q' X).1).hom
        (cc.sum fun k y => (Φ.A.map (Q.j (m.G.obj X.T))).hom y * Φ.dp k (Q.X (m.G.obj X.T)))) =
      (cc.mapRange (fun x => algebraMap R' (Φ'.A.obj X.T) c * m.ρ X.T x) (by simp)).sum
        fun k y => (Φ'.A.map (Q'.j X.T)).hom y * Φ'.dp k (Q'.X X.T) :=
  rho_finsupp_sum_dpow m Q c (Q'.j X.T) (etaC m E E' e he hρ Q Q' X).1 (Q'.X X.T) (j_eta m E E' e he hρ Q Q' X)
    (rho_eta m E E' e he hρ Q Q' X) cc

theorem beta_τ {a b : ℤ → IdF Φ.A} {a' b' : ℤ → IdF Φ'.A} {r : ℤ} (c : R')
    (ha : ∀ r', m.LeC c (a r') (a' r')) (hb : ∀ r', m.LeC c (b r') (b' r'))
    (hca : Q.Crit a r) (hca1 : Q.Crit a (r - 1))
    (β : Cut.P0 Q ⋙ Cut.U E ⋙ sq (a r) (b r) ⟶ Cut.P0 Q ⋙ Cut.U E ⋙ sq (a (r - 1)) (b (r - 1)))
    (hβ : ∀ (X : Pt E) (c c' : ℕ →₀ Φ.A.obj X.T) (z : sqM (a r) (b r) (Q.P X.T)) (z' : sqM (a (r - 1)) (b (r - 1)) (Q.P X.T)),
        (∀ k, c' k = c (k + 1)) →
        z.1 = Ideal.Quotient.mk _ (c.sum fun k y => (Φ.A.map (Q.j X.T)).hom y * Φ.dp k (Q.X X.T)) →
        z'.1 = Ideal.Quotient.mk _ (c'.sum fun k y => (Φ.A.map (Q.j X.T)).hom y * Φ.dp k (Q.X X.T)) →
        (β.app X).hom z = z')
    (β' : Cut.P0 Q' ⋙ Cut.U E' ⋙ sq (a' r) (b' r) ⟶ Cut.P0 Q' ⋙ Cut.U E' ⋙ sq (a' (r - 1)) (b' (r - 1)))
    (hβ' : ∀ (X : Pt E') (c c' : ℕ →₀ Φ'.A.obj X.T) (z : sqM (a' r) (b' r) (Q'.P X.T)) (z' : sqM (a' (r - 1)) (b' (r - 1)) (Q'.P X.T)),
        (∀ k, c' k = c (k + 1)) →
        z.1 = Ideal.Quotient.mk _ (c.sum fun k y => (Φ'.A.map (Q'.j X.T)).hom y * Φ'.dp k (Q'.X X.T)) →
        z'.1 = Ideal.Quotient.mk _ (c'.sum fun k y => (Φ'.A.map (Q'.j X.T)).hom y * Φ'.dp k (Q'.X X.T)) →
        (β'.app X).hom z = z')
    (X : Pt E') (y : sqM (a r) (b r) (Q.P (m.G.obj X.T))) :
    (mP m E E' e he hρ Q Q' c (ha (r - 1)) (hb (r - 1))).τ X ((β.app ((Gp m E E' e).obj X)).hom y) =
      (β'.app X).hom ((mP m E E' e he hρ Q Q' c (ha r) (hb r)).τ X y) := by
  obtain ⟨y, hy⟩ := y
  obtain ⟨w, hw, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hy
  obtain ⟨cc, rfl⟩ := Q.span _ w
  have hmem := (hca (m.G.obj X.T) cc).1 hw
  let c' : ℕ →₀ Φ.A.obj (m.G.obj X.T) := cc.comapDomain (· + 1) (fun _ _ _ _ h => Nat.add_right_cancel h)
  have hc' : ∀ k, c' k = cc (k + 1) := fun k => Finsupp.comapDomain_apply _ _ _ _
  have hw' := (hca1 (m.G.obj X.T) c').2 fun k => by
    rw [hc']
    have h := hmem (k + 1)
    rwa [show r - ((k + 1 : ℕ) : ℤ) = r - 1 - (k : ℤ) by push_cast; ring] at h
  have hb1 := hβ ((Gp m E E' e).obj X) cc c' ⟨_, hy⟩ ⟨_, Ideal.mem_map_of_mem _ hw'⟩ hc' rfl rfl
  rw [hb1]
  symm
  refine hβ' X (cc.mapRange (fun x => algebraMap R' (Φ'.A.obj X.T) c * m.ρ X.T x) (by simp))
    (c'.mapRange (fun x => algebraMap R' (Φ'.A.obj X.T) c * m.ρ X.T x) (by simp)) _ _ (fun k => ?_) ?_ ?_
  · rw [Finsupp.mapRange_apply, Finsupp.mapRange_apply, hc']
  · exact congrArg (Ideal.Quotient.mk _) (rho_sum m E E' e he hρ Q Q' c X cc)
  · exact congrArg (Ideal.Quotient.mk _) (rho_sum m E E' e he hρ Q Q' c X c')

end Cuts

end GlobalTheory.CompanionTheory.LocBC
end
end

section

open GroundTheory.Automorphic.HarishChandra GlobalTheory.CompanionTheory.PresRho

theorem _root_.GlobalTheory.T.annihilator_spanned_by_weight_vectors : ∀ {n : ℕ} {A : Type} [AddCommGroup A] [Module ℂ A] (φ : U n →ₐ[ℂ] Module.End ℂ A) (t : A), (∀ k, φ (e (k, k)) t = rhoVec n k • t) → ∀ x : U n, φ x t = 0 → x ∈ Submodule.span ℂ {y : U n | ∃ μ : Fin n → ℤ, IsAdW μ y ∧ φ y t = 0} := by
  first | exact @GlobalTheory.CompanionTheory.PresRho.mem_span_isAdW_of_kills | exact GlobalTheory.CompanionTheory.PresRho.mem_span_isAdW_of_kills | (intros; apply GlobalTheory.CompanionTheory.PresRho.mem_span_isAdW_of_kills <;> assumption)
end

section

open GroundTheory.Automorphic.HarishChandra GlobalTheory.CompanionTheory.PresRho

theorem _root_.GlobalTheory.T.weight_vector_mem_low_span_sup_verma : ∀ {n : ℕ} (μ : Fin n → ℤ) (x : U n), IsAdW μ x → x ∈ lowSpanW μ ⊔ vermaIdeal (rhoVec n) := by
  first | exact @GlobalTheory.CompanionTheory.PresRho.mem_lowSpanW_sup_vermaIdeal_of_isAdW | exact GlobalTheory.CompanionTheory.PresRho.mem_lowSpanW_sup_vermaIdeal_of_isAdW | (intros; apply GlobalTheory.CompanionTheory.PresRho.mem_lowSpanW_sup_vermaIdeal_of_isAdW <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

universe w v u w' v' u'

namespace GlobalTheory.CompanionTheory.CosieveBC

open GlobalTheory.CompanionTheory.CosieveMV

section Cover

variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {C : Type u} [Category.{v} C]
  {C' : Type u'} [Category.{v'} C'] {G : C' ⥤ C} {ι : Type} {N : ι → Type} [∀ i, AddCommGroup (N i)]
  [∀ i, Module R (N i)] {F : ι → (C ⥤ ModuleCat.{w} R)} {F' : C' ⥤ ModuleCat.{w'} R'}
  {τ : ∀ i, N i → ∀ T : C', (F i).obj (G.obj T) →ₛₗ[σ] F'.obj T}
  {hτ : ∀ i n {T T' : C'} (φ : T ⟶ T') x, τ i n T' (((F i).map (G.map φ)).hom x) = (F'.map φ).hom (τ i n T x)}

theorem subsingleton_H {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R)
    {W : ObjectProperty C} (h : ∀ T, ¬ W T) (j : ℕ) : Subsingleton ((cw F W).H j) := by
  have : Subsingleton ((cw F W).X j) := ⟨fun _ _ => funext fun s => (h _ (s.obj 0).property).elim⟩
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨a, ha, rfl⟩ := CrystallineSemistableComparison.CechClassBoundaries.clsSurj x
  refine (CrystallineSemistableComparison.CechClassBoundaries.cls_eq_zero a ha).2 ?_
  rw [Subsingleton.elim a 0]
  exact zero_mem _

theorem bc_congr [DecidableEq ι] {W W₂ : ObjectProperty C} {W' W₂' : ObjectProperty C'} (e : ∀ T, W T ↔ W₂ T)
    (e' : ∀ T, W' T ↔ W₂' T) (h : ∀ T, W' T → W (G.obj T)) (h₂ : ∀ T, W₂' T → W₂ (G.obj T))
    (t : BC (Phi G F F' τ hτ h)) : BC (Phi G F F' τ hτ h₂) := by
  obtain rfl : W = W₂ := funext fun T => propext (e T)
  obtain rfl : W' = W₂' := funext fun T => propext (e' T)
  exact t

theorem Wc_insert {α : Type} [DecidableEq α] {D : Type u} [Category.{v} D] (U : α → ObjectProperty D) (a : α)
    (A S : Finset α) (T : D) : supP (Wc U A S) (capS U (insert a S)) T ↔ Wc U (insert a A) S T := by
  constructor
  · rintro (⟨⟨b, hb, hT⟩, hS⟩ | h)
    · exact ⟨⟨b, Finset.mem_insert_of_mem hb, hT⟩, hS⟩
    · exact ⟨⟨a, Finset.mem_insert_self _ _, h a (Finset.mem_insert_self _ _)⟩,
        fun b hb => h b (Finset.mem_insert_of_mem hb)⟩
  · rintro ⟨⟨b, hb, hT⟩, hS⟩
    rcases Finset.mem_insert.1 hb with rfl | h
    · refine Or.inr fun c hc => ?_
      rcases Finset.mem_insert.1 hc with rfl | h'
      · exact hT
      · exact hS c h'
    · exact Or.inl ⟨⟨b, h, hT⟩, hS⟩

theorem Wc_inf {α : Type} [DecidableEq α] {D : Type u} [Category.{v} D] (U : α → ObjectProperty D) (a : α)
    (A S : Finset α) (T : D) : Wc U A (insert a S) T ↔ infP (Wc U A S) (capS U (insert a S)) T :=
  ⟨fun h => ⟨⟨h.1, fun b hb => h.2 b (Finset.mem_insert_of_mem hb)⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩

theorem wc_le {α : Type} {U : α → ObjectProperty C} {U' : α → ObjectProperty C'}
    (h : ∀ a T, U' a T → U a (G.obj T)) (A S : Finset α) (T : C') (hT : Wc U' A S T) : Wc U A S (G.obj T) := by
  obtain ⟨⟨a, ha, hT⟩, hS⟩ := hT
  exact ⟨⟨a, ha, h a T hT⟩, fun b hb => h b T (hS b hb)⟩

theorem cap_le {α : Type} {U : α → ObjectProperty C} {U' : α → ObjectProperty C'}
    (h : ∀ a T, U' a T → U a (G.obj T)) (S : Finset α) (T : C') (hT : capS U' S T) : capS U S (G.obj T) :=
  fun b hb => h b T (hT b hb)

theorem bc_Wc [Fintype ι] [DecidableEq ι] [∀ i, Module.Flat R (N i)] {α : Type} [DecidableEq α]
    (hadd : ∀ i n n' T x, τ i (n + n') T x = τ i n T x + τ i n' T x)
    (hsm : ∀ i (r : R) n T x, τ i (r • n) T x = σ r • τ i n T x)
    {U : α → ObjectProperty C} {U' : α → ObjectProperty C'} (hU : ∀ a, Cosieve (U a)) (hU' : ∀ a, Cosieve (U' a))
    (h : ∀ a T, U' a T → U a (G.obj T))
    (hcap : ∀ S : Finset α, S.Nonempty → BC (Phi G F F' τ hτ (cap_le h S))) (A : Finset α) :
    ∀ S : Finset α, BC (Phi G F F' τ hτ (wc_le h A S)) := by
  induction A using Finset.induction_on with
  | empty =>
    intro S j
    have e : ∀ {D : Type u} [Category.{v} D] (P : α → ObjectProperty D) (T : D), ¬ Wc P ∅ S T := by
      intro D _ P T hT
      simpa using hT.1
    have e' : ∀ {D : Type u'} [Category.{v'} D] (P : α → ObjectProperty D) (T : D), ¬ Wc P ∅ S T := by
      intro D _ P T hT
      simpa using hT.1
    have s1 := fun i => subsingleton_H (F i) (e U) j
    have s2 := subsingleton_H F' (e' U') j
    exact tens_subsingleton _
  | insert a A ha ih =>
    intro S
    have key := bc_sup (G := G) (F := F) (F' := F') (τ := τ) (hτ := hτ) hadd hsm (cosieve_Wc hU A S)
      (cosieve_capS hU (insert a S)) (cosieve_Wc hU' A S) (cosieve_capS hU' (insert a S))
      (wc_le h A S) (cap_le h (insert a S)) (ih S) (hcap _ (Finset.insert_nonempty _ _))
      (bc_congr (Wc_inf U a A S) (Wc_inf U' a A S) _ _ (ih (insert a S)))
    exact bc_congr (Wc_insert U a A S) (Wc_insert U' a A S) _ _ key

theorem restrict_bij {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R)
    {W : ObjectProperty C} (hall : ∀ T, W T) (n : ℕ) :
    Function.Bijective ((CH.Mor.restrict F W.ι).hom.f n) := by
  have hW : Cosieve W := fun _ _ _ _ => hall _
  refine ⟨fun x y hxy => funext fun s => congrFun hxy (liftCh hW s (hall _)), fun y => ⟨extZ hW y, pull_extZ hW y⟩⟩

def resEquiv {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R)
    {W : ObjectProperty C} (hall : ∀ T, W T) (j : ℕ) : CH.H F j ≃ₗ[R] (cw F W).H j :=
  LinearEquiv.ofBijective ((CH.Mor.restrict F W.ι).hom.mapH j) (CrystallineSemistableComparison.P.mapH_bij _ (restrict_bij F hall) j)

theorem tens_top [Fintype ι] [DecidableEq ι]
    (hadd : ∀ i n n' T x, τ i (n + n') T x = τ i n T x + τ i n' T x)
    (hsm : ∀ i (r : R) n T x, τ i (r • n) T x = σ r • τ i n T x)
    {W : ObjectProperty C} {W' : ObjectProperty C'} (hall : ∀ T, W T) (hall' : ∀ T, W' T)
    (h : ∀ T, W' T → W (G.obj T)) (t : BC (Phi G F F' τ hτ h)) (j : ℕ) :
    Tens R (N := N) (M := fun i => CH.H (F i) j) (M' := CH.H F' j)
      fun i n x => (⟨G, τ i n, hτ i n⟩ : CH.Mor (F i) F' σ).pull j x := by
  have lq : Lin (K := fun i => CH.cx (F i)) (K' := CH.cx F') (σ := σ)
      fun i n => (⟨G, τ i n, hτ i n⟩ : CH.Mor (F i) F' σ).hom :=
    ⟨fun i n n' k x => funext fun s => hadd i n n' _ _, fun i r n k x => funext fun s => hsm i r n _ _⟩
  refine tens_of_bij (bal_mapH (phi_lin hadd hsm h) j) (bal_mapH lq j) (fun i => resEquiv (F i) hall j)
    (resEquiv F' hall' j).toAddEquiv (fun i n x => ?_) (t j)
  obtain ⟨a, ha, rfl⟩ := CrystallineSemistableComparison.CechClassBoundaries.clsSurj x
  rfl

end Cover

theorem base_change_of_cover : ∀ {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {C C' : Type 1} [Category.{0} C] [Category.{0} C']
    (G : C' ⥤ C) {ι : Type} [Fintype ι] [DecidableEq ι] (N : ι → Type) [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    [∀ i, Module.Flat R (N i)] (F : ι → (C ⥤ ModuleCat.{0} R)) (F' : C' ⥤ ModuleCat.{0} R')
    (τ : ∀ i, N i → ∀ T : C', (F i).obj (G.obj T) →ₛₗ[σ] F'.obj T) (hτ : ∀ i n {T T' : C'} (φ : T ⟶ T') x,
      τ i n T' (((F i).map (G.map φ)).hom x) = (F'.map φ).hom (τ i n T x))
    (hadd : ∀ i n n' T x, τ i (n + n') T x = τ i n T x + τ i n' T x) (hsm : ∀ i (r : R) n T x, τ i (r • n) T x = σ r • τ i n T x)
    {A : Type} [Fintype A] (U : A → ObjectProperty C) (U' : A → ObjectProperty C') (hU : ∀ α, Cosieve (U α))
    (hU' : ∀ α, Cosieve (U' α)) (hc : ∀ T, ∃ α, U α T) (hc' : ∀ T, ∃ α, U' α T) (h : ∀ α T, U' α T → U α (G.obj T)),
    (∀ S : Finset A, S.Nonempty → ∀ j, Tens R (N := N) (M := fun i => HU (F i) (capS U S) j) (M' := HU F' (capS U' S) j)
      fun i n x => (morU (⟨G, τ i n, hτ i n⟩ : CH.Mor (F i) F' σ) (U := capS U S) (U' := capS U' S)
        fun T hT α hα => h α T (hT α hα)).pull j x) →
    ∀ j, Tens R (N := N) (M := fun i => CH.H (F i) j) (M' := CH.H F' j)
      fun i n x => (⟨G, τ i n, hτ i n⟩ : CH.Mor (F i) F' σ).pull j x := by
  intro R R' _ _ σ C C' _ _ G ι _ _ N _ _ _ F F' τ hτ hadd hsm A _ U U' hU hU' hc hc' h H j
  classical
  have key := bc_Wc (G := G) (F := F) (F' := F') (τ := τ) (hτ := hτ) hadd hsm hU hU' h
    (fun S hS j => H S hS j) Finset.univ ∅
  refine tens_top hadd hsm (W := Wc U Finset.univ ∅) (W' := Wc U' Finset.univ ∅) (fun T => ?_) (fun T => ?_) _ key j
  · obtain ⟨a, ha⟩ := hc T
    exact ⟨⟨a, Finset.mem_univ _, ha⟩, fun b hb => by simp at hb⟩
  · obtain ⟨a, ha⟩ := hc' T
    exact ⟨⟨a, Finset.mem_univ _, ha⟩, fun b hb => by simp at hb⟩

end GlobalTheory.CompanionTheory.CosieveBC
end
end

section

open ReciprocityTheory.Ty.Fin CategoryTheory

namespace GlobalTheory.CompanionTheory.TyFin

variable {Γ : Type} [Group Γ] [Fintype Γ]

theorem nonempty_iso_iff_equiv (τ σ : FDRep ℂ Γ) :
    Nonempty (τ ≅ σ) ↔ Nonempty (Representation.Equiv τ.ρ σ.ρ) := by
  rw [GlobalTheory.T.simple_iff_irreducible.2 Γ τ σ]
  constructor
  · rintro ⟨e, he⟩
    exact ⟨Representation.Equiv.mk e fun g => LinearMap.ext fun v => he g v⟩
  · rintro ⟨φ⟩
    exact ⟨φ.toLinearEquiv, fun γ v => LinearMap.congr_fun (φ.isIntertwining' γ) v⟩

theorem zIdem_act (τ σ : FDRep ℂ Γ) (hτ : Simple τ) (hσ : Simple σ) :
    Representation.asAlgebraHom σ.ρ (zIdem τ) = (open Classical in if Nonempty (τ ≅ σ) then 1 else 0) := by
  have h := centralIdemAct Γ τ σ τ.ρ σ.ρ ((GlobalTheory.T.simple_iff_irreducible.1 Γ τ).1 hτ) ((GlobalTheory.T.simple_iff_irreducible.1 Γ σ).1 hσ)
  rw [zIdem_eq_centralIdem, h]
  by_cases hc : Nonempty (τ ≅ σ)
  · rw [if_pos hc, if_pos ((nonempty_iso_iff_equiv τ σ).1 hc)]
  · rw [if_neg hc, if_neg (fun h' => hc ((nonempty_iso_iff_equiv τ σ).2 h'))]

theorem eq_of_act (x y : MonoidAlgebra ℂ Γ)
    (h : ∀ τ : FDRep ℂ Γ, Simple τ → Representation.asAlgebraHom τ.ρ x = Representation.asAlgebraHom τ.ρ y) :
    x = y :=
  sub_eq_zero.1 (GlobalTheory.T.separable_irreducible Γ _ fun τ hτ => by rw [map_sub, h τ hτ, sub_self])

theorem zIdemFacts : ReciprocityTheory.Ty.Fin.St.ZIdemFacts := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Γ _ _ τ hτ
    refine ⟨eq_of_act _ _ fun W hW => ?_, fun a => eq_of_act _ _ fun W hW => ?_⟩
    · rw [map_mul, zIdem_act τ W hτ hW]
      split_ifs <;> simp
    · rw [map_mul, map_mul, zIdem_act τ W hτ hW]
      split_ifs <;> simp
  · intro Γ _ _ τ σ hτ hσ hne
    refine eq_of_act _ _ fun W hW => ?_
    rw [map_mul, map_zero, zIdem_act τ W hτ hW, zIdem_act σ W hσ hW]
    by_cases h1 : Nonempty (τ ≅ W)
    · by_cases h2 : Nonempty (σ ≅ W)
      · exact absurd ⟨h1.some ≪≫ h2.some.symm⟩ hne
      · simp [h2]
    · simp [h1]
  · intro Γ _ _ τ σ hτ hσ hiso
    rw [zIdem_act τ σ hτ hσ, if_pos hiso]
  · intro Γ _ _ I _ V hV hinj hex
    classical
    refine eq_of_act _ _ fun W hW => ?_
    obtain ⟨i₀, ⟨e⟩⟩ := hex W hW
    have hact : ∀ i, Representation.asAlgebraHom W.ρ (zIdem (V i)) =
        if i = i₀ then (1 : Module.End ℂ W) else 0 := by
      intro i
      rw [zIdem_act (V i) W (hV i) hW]
      by_cases hi : i = i₀
      · subst hi
        rw [if_pos ⟨e.symm⟩, if_pos rfl]
      · rw [if_neg (fun ⟨f⟩ => hi (hinj _ _ ⟨f ≪≫ e⟩)), if_neg hi]

    rw [map_sum, map_one, Finset.sum_congr rfl fun i _ => hact i]
    simp

end GlobalTheory.CompanionTheory.TyFin
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison

namespace GlobalTheory.CompanionTheory.OmRes

theorem restrict_pull_bijective_of_forall :
    ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R)
      (Q : ObjectProperty C), (∀ T, Q T) →
      ∀ n : ℕ, Function.Bijective ((CH.Mor.restrict F Q.ι).pull n) := by
  intro R _ C _ F Q h n
  haveI : Q.ι.EssSurj := ⟨fun Y => ⟨⟨Y, h Y⟩, ⟨Iso.refl _⟩⟩⟩
  haveI : Q.ι.IsEquivalence := { }
  exact CrystallineSemistableComparison.P.adj F Q.ι Q.ι.inv Q.ι.asEquivalence.toAdjunction n

end GlobalTheory.CompanionTheory.OmRes
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.eval_restrict_section : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} (T : Thick (smFun X q))
    {V W : X.Opens} (h : V ≤ W) (hT : InU V T) (hT' : InU W T) (s : Γ(X, W)), ev T hT (rs h s) = ev T hT' s := by
  first | exact @GlobalTheory.CompanionTheory.ConeEval.ev_rs_eq | exact GlobalTheory.CompanionTheory.ConeEval.ev_rs_eq | (intros; apply GlobalTheory.CompanionTheory.ConeEval.ev_rs_eq <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC
open CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.CompanionTheory.EdgeRep

theorem mul_ev_congr {R : Type} [CommRing R] {I J K : GlobalTheory.EtC.Cx R} (μ : Pair I J K) {X : Scheme.{0}} {n m k s t : ℤ}
    (h : n + m = k) (hst : s + t = k) (hs : -((0 : ℕ) : ℤ) + n = s) (ht : -((0 : ℕ) : ℤ) + m = t)
    (α : Cochain ((chains R).obj (sch.obj X)) I n) (β : Cochain ((chains R).obj (sch.obj X)) J m) :
    μ.mul X s t k hst (ev α 0 s hs X (𝟙 X)) (ev β 0 t ht X (𝟙 X)) =
      μ.mul X n m k h (ev α 0 n (by simp) X (𝟙 X)) (ev β 0 m (by simp) X (𝟙 X)) := by
  obtain rfl : s = n := by simpa using hs.symm
  obtain rfl : t = m := by simpa using ht.symm
  rfl

theorem aw_value {R : Type} [CommRing R] {I J K : GlobalTheory.EtC.Cx R} (μ : Pair I J K) {X : Scheme.{0}} {n m k : ℤ}
    (h : n + m = k) (α : Cochain ((chains R).obj (sch.obj X)) I n) (β : Cochain ((chains R).obj (sch.obj X)) J m)
    (γ : Cochain ((chains R).obj (sch.obj X)) K k) (hγ : μ.IsAW h α β γ) :
    ev γ 0 k (by simp) X (𝟙 X) = μ.mul X n m k h (ev α 0 n (by simp) X (𝟙 X)) (ev β 0 m (by simp) X (𝟙 X)) := by
  have h0 := hγ 0 k (by simp) X (𝟙 X)
  rw [Fin.sum_univ_one] at h0
  rw [h0]
  have hu : (m * ((0 : Fin 1) : ℕ)).negOnePow = 1 := by simp
  rw [hu, one_smul]
  exact mul_ev_congr μ h _ _ _ α β

theorem repCup : CrystallineSemistableComparison.E.EvExt → CrystallineSemistableComparison.E.EvNat → CrystallineSemistableComparison.E.RepBasic → CrystallineSemistableComparison.E.RepConc → CrystallineSemistableComparison.E.InSch → CrystallineSemistableComparison.E.RepCup := by
  intro _ _ _ _ _ R _ I J K μ X n m k h x y a b hx hy
  obtain ⟨α, rfl, rfl⟩ := hx
  obtain ⟨β, rfl, rfl⟩ := hy
  obtain ⟨γ, hγ⟩ := μ.aw_exists (sch.obj X) h α β
  exact ⟨γ, (μ.cup_spec (sch.obj X) h α β γ hγ).symm, aw_value μ h α.1 β.1 γ.1 hγ⟩

end GlobalTheory.CompanionTheory.EdgeRep

end
end

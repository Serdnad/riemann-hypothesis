module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConnectedDieudonneFunctorQuasiLogarithms
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle966
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1173
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1098
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1099
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1161
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle032
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle018
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory

theorem semiHom_dual_transpose : ∀ (p : ℕ) [Fact p.Prime] (B : Base p (fun _ _ G => G.IsConn)) (k k' : Type) [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p] [PerfectRing k' p] [Algebra k k'] (G : PDivGroup p k) (G' : PDivGroup p k') (hd : G.dual.IsConn) (hd' : G'.dual.IsConn) (hb : (G.dual.baseChange k').IsConn) (s : SemiHom (algebraMap k k') G' G) (l : Module.Dual (WittVector p k) (B.M G.dual hd)), ∃! l' : Module.Dual (WittVector p k') (B.M G'.dual hd'), ∃ lb : Module.Dual (WittVector p k') (B.M (G.dual.baseChange k') hb), (∀ x, lb (B.smap hb hd (G.dual.toBase k') x) = WittVector.map (algebraMap k k') (l x)) ∧ ∀ y, l' y = lb (B.map hb hd' ((PerfdLat.dualBaseChange k' G).inv ≫ dualHom G' (G.baseChange k') s.lift) y) := by
  intro p _ B k k' _ _ _ _ _ _ _ G G' hd hd' hb s l
  haveI := B.free G.dual hd
  haveI := B.finite G.dual hd
  let b := Module.Free.chooseBasis (WittVector p k) (B.M G.dual hd)
  obtain ⟨b', hb'⟩ := GlobalTheory.T.dieudonne_baseChange_basis p (fun _ _ G => G.IsConn) B k k' G.dual hd hb _ b
  let lb : Module.Dual (WittVector p k') (B.M (G.dual.baseChange k') hb) :=
    b'.constr (WittVector p k') (fun i => WittVector.map (algebraMap k k') (l (b i)))
  have h1 : ∀ x, lb (B.smap hb hd (G.dual.toBase k') x) = WittVector.map (algebraMap k k') (l x) := by
    intro x
    conv_lhs => rw [← b.sum_repr x]
    conv_rhs => rw [← b.sum_repr x]

    simp only [map_sum, B.smap_smul, map_smul, ← hb', lb, Module.Basis.constr_basis, smul_eq_mul, map_mul]
  refine ⟨lb ∘ₗ B.map hb hd' ((PerfdLat.dualBaseChange k' G).inv ≫ dualHom G' (G.baseChange k') s.lift),
    ⟨lb, h1, fun y => rfl⟩, fun l'' ⟨lb', h1', h2'⟩ => ?_⟩
  have hl : lb' = lb := b'.ext fun i => by
    simp only [lb, Module.Basis.constr_basis]
    rw [hb', h1']
  subst hl
  exact LinearMap.ext fun y => h2' y

end GlobalTheory
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.Dieu

theorem wittMap_frobRing_bijective (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] : Function.Bijective (WittVector.map (p := p) (frobRing (p_eq_zero p k))) := by
  have hb : Function.Bijective (frobRing (p_eq_zero p k)) := by
    have e : ⇑(frobRing (p_eq_zero p k)) = ⇑(frobenius k p) :=
      funext fun r => by rw [frobRing_apply, frobenius_def]
    rw [e]
    exact bijective_frobenius k p
  exact ⟨WittVector.map_injective _ hb.1, WittVector.map_surjective _ hb.2⟩

theorem bijective_of_basis {R R' M M' : Type} [CommRing R] [CommRing R'] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R' M'] (σ : R →+* R') (hσ : Function.Bijective σ) (f : M →+ M')
    (hf : ∀ (a : R) (m : M), f (a • m) = σ a • f m) {ι : Type} [Fintype ι] (b : Module.Basis ι R M)
    (b' : Module.Basis ι R' M') (hb : ∀ i, b' i = f (b i)) : Function.Bijective f := by
  have key : ∀ c : ι → R, f (∑ i, c i • b i) = ∑ i, σ (c i) • b' i := fun c => by
    rw [map_sum f]
    exact Finset.sum_congr rfl fun i _ => by rw [hf, hb]
  refine ⟨(injective_iff_map_eq_zero f).2 fun m hm => ?_, fun x => ?_⟩
  · rw [← b.sum_repr m, key] at hm
    have : ∀ i, b.repr m i = 0 := fun i => by
      have := Fintype.linearIndependent_iff.1 b'.linearIndependent _ hm i
      exact hσ.1 (this.trans (map_zero σ).symm)
    rw [← b.sum_repr m]
    simp [this]
  · obtain ⟨c, hc⟩ : ∃ c : ι → R, ∀ i, σ (c i) = b'.repr x i :=
      ⟨fun i => Function.surjInv hσ.2 (b'.repr x i), fun i => Function.surjInv_eq hσ.2 _⟩
    refine ⟨∑ i, c i • b i, ?_⟩
    rw [key]
    simp only [hc]
    exact b'.sum_repr x

theorem frobTwist_module (p : ℕ) [Fact p.Prime] (B : Base p fun _ _ _ => True)
    (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) :
    Function.Bijective (B.smap trivial trivial (frobProj (p_eq_zero p k) G)) ∧
    (∀ m, B.map trivial trivial (relFrob (p_eq_zero p k) G)
      (B.smap trivial trivial (frobProj (p_eq_zero p k) G) m) = B.F G trivial m) ∧
    ∀ m n, B.smap trivial trivial (frobProj (p_eq_zero p k) G) n =
      B.map trivial trivial (verschiebung (p_eq_zero p k) G) m → B.F G trivial n = p • m := by
  have h2 : ∀ m, B.map trivial trivial (relFrob (p_eq_zero p k) G)
      (B.smap trivial trivial (frobProj (p_eq_zero p k) G) m) = B.F G trivial m := fun m =>
    (B.smap_comp trivial trivial trivial (frobProj (p_eq_zero p k) G)
      (SemiHom.ofHom (relFrob (p_eq_zero p k) G)) (absFrob (p_eq_zero p k) G)
      (fun n a => by rw [SemiHom.ofHom_app, relFrob_app_frobProj, absFrob_app]) m).symm
  refine ⟨?_, h2, fun m n e => ?_⟩
  · haveI := B.free G trivial
    haveI := B.finite G trivial
    letI := (frobRing (p_eq_zero p k)).toAlgebra
    obtain ⟨b', hb'⟩ := GlobalTheory.T.dieudonne_baseChange_basis p (fun _ _ _ => True) B k k G trivial trivial _
      (Module.Free.chooseBasis (WittVector p k) (B.M G trivial))
    exact bijective_of_basis _ (wittMap_frobRing_bijective p k) _
      (fun a m => B.smap_smul trivial trivial _ a m) _ b' hb'
  · obtain ⟨-, hc, -⟩ := GlobalTheory.T.dieudonneFunctorBase_functor_properties p (fun _ _ _ => True) B k G
      (frobTwist (p_eq_zero p k) G) G trivial trivial trivial
    obtain ⟨hid, -, -, -, hp, -⟩ := GlobalTheory.T.dieudonneFunctorBase_functor_properties p (fun _ _ _ => True) B k G G G trivial trivial trivial
    rw [← h2, e, ← LinearMap.comp_apply, ← hc, relFrob_comp_verschiebung, ← pow_one (p : ℤ_[p]), hp,
      pow_one, hid, LinearMap.id_apply]

end GlobalTheory.Dieu
end
end

section

open CategoryTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.exists_connected_dieudonne_functor_quasiLogarithms : ∀ (p : ℕ) [Fact p.Prime], ∃ B : GlobalTheory.Dieu.Base p (fun _ _ G => G.IsConn), B.Katz := by
  first | (exact @GlobalTheory.exists_base_isConn_katz) | (exact GlobalTheory.exists_base_isConn_katz) | (intros; apply GlobalTheory.exists_base_isConn_katz  <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.UG GlobalTheory.PRep GlobalTheory.LFun
open scoped Classical

open GlobalTheory.JSW

theorem GlobalTheory.JSW.shintani_formula : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ψ : AddChar (w.adicCompletion E) ℂ), (∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, ψ (x * y) = 1) ↔ x ∈ Ov E w) → ∀ (W : GL (Fin n) (w.adicCompletion E) → ℂ) (α : Fin n → ℂˣ), (∀ u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin n), ∀ g, W (u * g) = ψ (GlobalTheory.Whittaker.superDiag u) * W g) → (∀ g, ∀ k ∈ KGL w (n := n), W (g * k) = W g) → (∀ ϖ, IsUnifV E w ϖ → ∀ j ≤ n, heckeVec (rightReg ℂ (GL (Fin n) (w.adicCompletion E)) ℂ) (KGL w (n := n)) (Tj ℂ n (Ov E w) ϖ j) W = satEig (qV E w) n (Finset.univ.val.map α) j • W) → ∀ (ϖ : (w.adicCompletion E)ˣ), IsUnifV E w (ϖ : w.adicCompletion E) → ∀ l : Fin n → ℕ, W (Units.map (Matrix.diagonalRingHom (Fin n) (w.adicCompletion E)).toMonoidHom (MulEquiv.piUnits.symm fun i => ϖ ^ l i)) = GlobalTheory.JSW.sphW (qV E w) (fun i => (α i : ℂ)) l * W 1 := by
  intro E _ _ w n ψ hψ W α hN hK hH ϖ hϖ l
  have hvan := GlobalTheory.T.whittaker_diagonal_eq_zero_of_not_antitone E w n ψ hψ W hN hK ϖ hϖ
  have hrec := GlobalTheory.T.sphericalWhittaker_torus_hecke_recursion E w n ψ hψ W α hN hK hH ϖ hϖ
  have hq : ((qV E w : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (GlobalTheory.LFun.qV_ne_zero w)
  have hes : ∀ j, MvPolynomial.eval₂ (Int.castRingHom ℂ) (fun i => (α i : ℂ)) (MvPolynomial.esymm (Fin n) ℤ j) =
      (Finset.univ.val.map fun i => (α i : ℂ)).esymm j := fun j => by
    rw [← MvPolynomial.aeval_esymm_eq_multiset_esymm (Fin n) ℤ]
    rfl
  let V : (Fin n → ℕ) → ℂ := fun m =>
    (qV E w : ℂ) ^ ((∑ k : Fin n, (((n : ℂ) - 1 - 2 * (k : ℕ)) * (((m) k : ℕ) : ℂ))) / 2) *
      W (Units.map (Matrix.diagonalRingHom (Fin n) (w.adicCompletion E)).toMonoidHom
        (MulEquiv.piUnits.symm fun i => ϖ ^ (m) i))
  let U : (Fin n → ℕ) → ℂ := fun m => if Antitone m then schurAt m (fun i => (α i : ℂ)) * W 1 else 0
  have hVU : V = U := by
    refine GlobalTheory.T.eq_of_pieri_recursion_of_eq_zero n (fun j => (Finset.univ.val.map fun i => (α i : ℂ)).esymm j) V U
      (fun m hm => by simp only [V, hvan m hm, mul_zero]) (fun m hm => by simp only [U, if_neg hm])
      (fun m hm j hj => hrec m hm j hj) (fun m hm j hj => ?_) ?_
    · have hp := congrArg (MvPolynomial.eval₂ (Int.castRingHom ℂ) (fun i => (α i : ℂ))) (GlobalTheory.T.esymm_mul_schurPolynomialJacobiTrudi n m hm j hj)
      rw [MvPolynomial.eval₂_mul, hes, MvPolynomial.eval₂_sum] at hp
      simp only [U, if_pos hm]
      rw [← Finset.sum_filter, Finset.filter_filter, ← Finset.sum_mul, ← mul_assoc]
      simp only [schurAt]
      rw [hp]
    · have h1 : (Units.map (Matrix.diagonalRingHom (Fin n) (w.adicCompletion E)).toMonoidHom
          (MulEquiv.piUnits.symm fun i => ϖ ^ (0 : Fin n → ℕ) i)) = 1 := by
        ext i j
        simp [Matrix.one_apply, Matrix.diagonal_apply]
      have h0 : (0 : Fin n → ℕ) = fun _ => 0 := rfl
      have ha0 : Antitone (0 : Fin n → ℕ) := antitone_const
      have hs : schurAt (0 : Fin n → ℕ) (fun i => (α i : ℂ)) = 1 := by
        rw [h0, schurAt, GlobalTheory.JSW.schur_zero, MvPolynomial.eval₂_one]
      have hU : U 0 = W 1 := by
        change (if Antitone (0 : Fin n → ℕ) then schurAt 0 (fun i => (α i : ℂ)) * W 1 else 0) = W 1
        rw [if_pos ha0, hs, one_mul]
      rw [hU]
      change _ * W _ = W 1
      rw [h1]
      simp
  have hl := congrFun hVU l
  simp only [V, U] at hl
  by_cases ha : Antitone l
  · rw [if_pos ha] at hl
    have hne : (qV E w : ℂ) ^ ((∑ k : Fin n, (((n : ℂ) - 1 - 2 * (k : ℕ)) * (((l) k : ℕ) : ℂ))) / 2) ≠ 0 := by
      rw [Complex.cpow_def_of_ne_zero hq]; exact Complex.exp_ne_zero _
    rw [sphW, if_pos ha, neg_div, Complex.cpow_neg, mul_assoc, ← hl, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  · rw [hvan l ha, GlobalTheory.JSW.sphW_of_not_antitone _ _ ha, zero_mul]
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.hasProperSmoothDualRep_of_finite_product_algebras : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → ∀ (n : ℕ) (D : Fin n → Type) [∀ i, CommRing (D i)] [∀ i, Algebra R (D i)], (∀ i, HasRepAF A g (Over.mk (spMap (algebraMap R (D i))))) → HasRepAF A g (Over.mk (spMap (algebraMap R (∀ i, D i)))) := by
  first | exact @GlobalTheory.DualCon.ProdGlue.hasRepAF_pi | exact GlobalTheory.DualCon.ProdGlue.hasRepAF_pi | (intros; apply GlobalTheory.DualCon.ProdGlue.hasRepAF_pi <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon.Zar

variable {S : Scheme.{0}} {A : Over S}

theorem same_comp {T U Y Z : Over S} {N : LB (A ⊗ T).left} {M : LB (A ⊗ U).left} (hN : N.IsLB) (hM : M.IsLB)
    {y : Y ⟶ T} {u : Y ⟶ U} (h : Same A N M y u) (z : Z ⟶ Y) : Same A N M (z ≫ y) (z ≫ u) := by
  rw [same_iff hN hM] at h ⊢
  have e := congrArg (CechPic.pull (lift (fst A Z) (snd A Z ≫ z)).left) h
  simpa only [pull_evc, lift_fst, lift_snd_assoc, Category.assoc] using e

theorem same_ev_iff {T U V Y : Over S} {N : LB (A ⊗ T).left} {M : LB (A ⊗ U).left} (hN : N.IsLB) (hM : M.IsLB)
    (j : V ⟶ T) (y : Y ⟶ V) (u : Y ⟶ U) :
    Same A (ev N (fst A V) (snd A V ≫ j)) M y u ↔ Same A N M (y ≫ j) u := by
  rw [same_iff (pull_isLB hN _) hM, same_iff hN hM, evc_ev hN]
  simp only [lift_fst, lift_snd_assoc, Category.assoc]

theorem exists_restrict {T Y Z : Over S} (y : Y ⟶ T) (z : Z ⟶ T) [IsOpenImmersion z.left] (p : Y.left)
    (hp : y.left p ∈ Set.range z.left) :
    ∃ (Y' : Over S) (i : Y' ⟶ Y) (t : Y' ⟶ Z), IsOpenImmersion i.left ∧ p ∈ Set.range i.left ∧ t ≫ z = i ≫ y := by
  let V := y.left ⁻¹ᵁ z.left.opensRange
  let Y' : Over S := Over.mk (V.ι ≫ Y.hom)
  let i : Y' ⟶ Y := Over.homMk V.ι rfl
  have hr : Set.range (i ≫ y).left ⊆ Set.range z.left := by
    rintro _ ⟨w, rfl⟩
    exact w.2
  let t : Y' ⟶ Z := Over.homMk (IsOpenImmersion.lift z.left (i ≫ y).left hr) (by
    rw [← Over.w z, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w])
  refine ⟨Y', i, t, inferInstanceAs (IsOpenImmersion V.ι), ⟨⟨p, hp⟩, rfl⟩, ?_⟩
  ext1; exact IsOpenImmersion.lift_fac _ _ _

variable [GrpObj A]

theorem exists_same_of_local (hA : IsAbelianScheme A) {T U Y : Over S} {N : LB (A ⊗ T).left}
    {M : LB (A ⊗ U).left} (hN : Fam A N) (hM : Fam A M) (hI : Inj A M) (y : Y ⟶ T)
    (loc : ∀ p : Y.left, ∃ (Z : Over S) (z : Z ⟶ Y) (u : Z ⟶ U), IsOpenImmersion z.left ∧
      p ∈ Set.range z.left ∧ Same A N M (z ≫ y) u) : ∃ u : Y ⟶ U, Same A N M y u := by
  choose Z z u ho hp hs using loc
  let 𝒰 : Y.left.OpenCover := Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) Y.left (fun p ↦ (Z p).left)
    (fun p ↦ (z p).left) (fun p ↦ by obtain ⟨q, hq⟩ := hp p; exact ⟨p, q, hq⟩) ho
  have hc : ∀ p q : Y.left, pullback.fst (z p).left (z q).left ≫ (u p).left =
      pullback.snd (z p).left (z q).left ≫ (u q).left := by
    intro p q
    let P : Over S := Over.mk (pullback.fst (z p).left (z q).left ≫ (Z p).hom)
    let a : P ⟶ Z p := Over.homMk (pullback.fst (z p).left (z q).left) rfl
    let b : P ⟶ Z q := Over.homMk (pullback.snd (z p).left (z q).left) (by
      rw [← Over.w (z q), ← Category.assoc, ← pullback.condition, Category.assoc, Over.w]; rfl)
    have hab : a ≫ z p = b ≫ z q := by ext1; exact pullback.condition
    have h₁ := same_comp hN.isLB hM.isLB (hs p) a
    have h₂ := same_comp hN.isLB hM.isLB (hs q) b
    rw [← Category.assoc, hab, Category.assoc] at h₁
    rw [same_iff hN.isLB hM.isLB] at h₁ h₂
    have h := hI P _ _ ((same_iff hM.isLB hM.isLB _ _).2 (h₁.symm.trans h₂))
    exact congrArg (·.left) h
  have hg : ∀ p, (z p).left ≫ 𝒰.glueMorphisms (fun p ↦ (u p).left) hc = (u p).left :=
    𝒰.ι_glueMorphisms _ hc
  let g : Y ⟶ U := Over.homMk (𝒰.glueMorphisms (fun p ↦ (u p).left) hc) (𝒰.hom_ext _ _ fun (p : Y.left) ↦
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ U.hom) (hg p))).trans
      ((Over.w (u p)).trans (Over.w (z p)).symm))
  refine ⟨g, same_of_local S A T U hA N M hN hM Y y g fun p ↦ ⟨Z p, z p, ho p, hp p, ?_⟩⟩
  have e : z p ≫ g = u p := by ext1; exact hg p
  rw [e]
  exact hs p

theorem fam_ev {T Y : Over S} {N : LB (A ⊗ T).left} (h : Fam A N) (y : Y ⟶ T) :
    Fam A (ev N (fst A Y) (snd A Y ≫ y)) := by
  have hM : (AbDual.ev N (fst A Y) (snd A Y ≫ y)).IsLB := pull_isLB h.isLB _
  refine ⟨hM, (isAdditive_iff hM).2 fun Z a a' t ↦ ?_⟩
  simp only [evc_ev h.isLB, lift_fst, lift_snd_assoc]
  exact (isAdditive_iff h.isLB).1 h.add _ _ _ _

end GlobalTheory.DualCon.Zar

namespace GlobalTheory.DualCon

theorem chartAt_of_affine : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A →
    ∀ (U : Over S) (M : LB (A ⊗ U).left), Fam A M → Inj A M →
    (∀ (T : Over S) [IsAffine T.left] (N : LB (A ⊗ T).left), Fam A N → ChartAt A M N) →
    ∀ (T : Over S) (N : LB (A ⊗ T).left), Fam A N → ChartAt A M N := by
  intro S A _ hA U M hM hI aff T N hN
  let W : Set T.left := {x | ∃ (Z : Over S) (z : Z ⟶ T) (u : Z ⟶ U), IsOpenImmersion z.left ∧
    x ∈ Set.range z.left ∧ Same A N M z u}
  have hW : IsOpen W := by
    rw [isOpen_iff_forall_mem_open]
    rintro x ⟨Z, z, u, ho, hx, hs⟩
    exact ⟨Set.range z.left, fun x' hx' ↦ ⟨Z, z, u, ho, hx', hs⟩, z.left.opensRange.2, hx⟩
  refine ⟨⟨W, hW⟩, fun Y y ↦ ⟨?_, fun h ↦ ?_⟩⟩
  · rintro ⟨u, hu⟩ p
    obtain ⟨i, q, hq⟩ := T.left.affineCover.exists_eq (y.left p)
    let V : Over S := Over.mk (T.left.affineCover.f i ≫ T.hom)
    let j : V ⟶ T := Over.homMk (T.left.affineCover.f i) rfl
    haveI : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion (T.left.affineCover.f i))
    haveI : IsAffine V.left := inferInstanceAs (IsAffine (T.left.affineCover.X i))
    obtain ⟨O, hO⟩ := aff V _ (Zar.fam_ev hN j)
    obtain ⟨Y', c, t, -, ⟨r, hr⟩, ht⟩ := Zar.exists_restrict y j p ⟨q, hq⟩
    have h₁ : t.left r ∈ O := (hO Y' t).1 ⟨c ≫ u, by
      rw [Zar.same_ev_iff hN.isLB hM.isLB, ht]
      exact Zar.same_comp hN.isLB hM.isLB hu c⟩ r
    let Z : Over S := Over.mk (O.ι ≫ V.hom)
    let k : Z ⟶ V := Over.homMk O.ι rfl
    haveI : IsOpenImmersion k.left := inferInstanceAs (IsOpenImmersion O.ι)
    obtain ⟨v, hv⟩ := (hO Z k).2 fun w ↦ w.2
    refine ⟨Z, k ≫ j, v, by rw [Over.comp_left]; infer_instance, ⟨⟨t.left r, h₁⟩, ?_⟩,
      (Zar.same_ev_iff hN.isLB hM.isLB _ _ _).1 hv⟩
    change (t ≫ j).left r = _
    rw [ht, ← hr]
    rfl
  · refine Zar.exists_same_of_local hA hN hM hI y fun p ↦ ?_
    obtain ⟨Z, z, u, ho, hx, hs⟩ := h p
    obtain ⟨Y', c, t, hc, hp, ht⟩ := Zar.exists_restrict y z p hx
    exact ⟨Y', c, t ≫ u, hc, hp, ht ▸ Zar.same_comp hN.isLB hM.isLB hs t⟩

end GlobalTheory.DualCon
end
end

section

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

theorem exists_glue_rigidified (X Y : Scheme.{0}) (p : X ⟶ Y) (e : Y ⟶ X) (hep : e ≫ p = 𝟙 Y) (hp : FnBij p)
    (Ix : Type) (X' : Ix → Scheme.{0}) (f : ∀ i, X' i ⟶ X) (V : Ix → Y.Opens) (c : ∀ i, Pic (X' i))
    (hf : ∀ i, IsOpenImmersion (f i)) (hr : ∀ i x, x ∈ Set.range (f i) ↔ p x ∈ V i) (hV : ∀ y, ∃ i, y ∈ V i)
    (hrig : ∀ (i : Ix) (T : Scheme.{0}) (t : T ⟶ X' i) (s : T ⟶ Y), t ≫ f i = s ≫ e → GlobalTheory.CechPic.pull t (c i) = 0)
    (hov : ∀ (i k : Ix) (T : Scheme.{0}) (a : T ⟶ X' i) (b : T ⟶ X' k), a ≫ f i = b ≫ f k →
      GlobalTheory.CechPic.pull a (c i) = GlobalTheory.CechPic.pull b (c k)) :
    ∃ c₀ : Pic X, GlobalTheory.CechPic.pull e c₀ = 0 ∧ ∀ i, GlobalTheory.CechPic.pull (f i) c₀ = c i := by
  have hpe : ∀ y : Y, p (e y) = y := fun y ↦ by
    rw [← Scheme.Hom.comp_apply, hep]; rfl
  have hrange : ∀ i, (f i).opensRange = p ⁻¹ᵁ V i := fun i ↦ by
    ext x; exact hr i x
  choose M hM hMc using fun i ↦ cls_surj (c i)
  choose L hL hLM using fun i ↦ GlobalTheory.T.exists_cech_lineBundle_ambient_of_openImmersion X (X' i) (f i) (M i) (hM i)
  have hL' : ∀ i, IsOn (p ⁻¹ᵁ V i) (L i) := fun i ↦ hrange i ▸ hL i
  have hfm : ∀ i (z : X' i), f i z ∈ p ⁻¹ᵁ V i := fun i z ↦ (hr i _).1 ⟨z, rfl⟩
  have hfl : ∀ i, ((L i).pull (f i)).IsLB := fun i ↦ GlobalTheory.T.isLineBundle_pull_of_isLineBundleOnOpen X _ _ (L i) (f i) (hL' i) (hfm i)
  have hcl : ∀ i, cls _ (hfl i) = c i := fun i ↦ ((cls_eq_iff (hfl i) (hM i)).2 (hLM i)).trans (hMc i)
  have lifts : ∀ i (T : Scheme.{0}) (g : T ⟶ X), (∀ z, g z ∈ p ⁻¹ᵁ V i) → ∃ t : T ⟶ X' i, t ≫ f i = g :=
    fun i T g hg ↦ ⟨IsOpenImmersion.lift (f i) g (by rintro _ ⟨z, rfl⟩; exact (hr i _).2 (hg z)),
      IsOpenImmersion.lift_fac _ _ _⟩
  have hpl : ∀ i (T : Scheme.{0}) (t : T ⟶ X' i) (g : T ⟶ X), t ≫ f i = g →
      ∃ h : ((L i).pull g).IsLB, cls _ h = GlobalTheory.CechPic.pull t (c i) := by
    rintro i T t _ rfl
    have h : ((L i).pull (t ≫ f i)).IsLB := GlobalTheory.T.isLineBundle_pull_of_isLineBundleOnOpen X _ _ (L i) _ (hL' i) fun z ↦ by
      rw [Scheme.Hom.comp_apply]; exact hfm i _
    refine ⟨h, ?_⟩
    rw [← hcl i, ← cls_pull (hfl i) t (pull_isLB (hfl i) t)]
    exact ((cls_eq_iff _ _).2 (GlobalTheory.T.lineBundleOnOpen_pull_comp_iso X _ _ _ (L i) (f i) t (hL' i) (hfm i))).symm
  have hR : ∀ i, ∃ r : RigD e (L i), RigOn e (L i) r := fun i ↦ by
    refine GlobalTheory.T.exists_pullbackGenerator_of_trivial_on_open X Y e (V i) (L i) (fun a y hy ↦ ?_) ?_
    · have : p (e y) ∈ V i := (hL' i).le a hy
      rwa [hpe] at this
    · obtain ⟨t, ht⟩ := lifts i _ ((V i).ι ≫ e) fun z ↦ by
        rw [Scheme.Hom.comp_apply]
        change p (e _) ∈ V i
        rw [hpe]
        exact z.2
      obtain ⟨h, hc⟩ := hpl i _ t _ ht
      exact (cls_eq_zero_iff h).1 (hc.trans (hrig i _ t _ ht))
  choose r hr' using hR
  have hw : ∀ i k, ∃ w : Cmp (p ⁻¹ᵁ (V i ⊓ V k)) (L i) (L k), IsoOn (p ⁻¹ᵁ (V i ⊓ V k)) (L i) (L k) w ∧
      Norm e (p ⁻¹ᵁ (V i ⊓ V k)) (L i) (L k) w (r i) (r k) := fun i k ↦ by
    obtain ⟨a, ha⟩ := lifts i _ (p ⁻¹ᵁ (V i ⊓ V k)).ι fun z ↦ z.2.1
    obtain ⟨b, hb⟩ := lifts k _ (p ⁻¹ᵁ (V i ⊓ V k)).ι fun z ↦ z.2.2
    obtain ⟨h1, e1⟩ := hpl i _ a _ ha
    obtain ⟨h2, e2⟩ := hpl k _ b _ hb
    obtain ⟨w, hw⟩ := GlobalTheory.T.exists_isLineBundleIsoOnOpen_of_restriction_iso X (p ⁻¹ᵁ (V i ⊓ V k)) (L i) (L k)
      ((cls_eq_iff h1 h2).1 (e1.trans ((hov i k _ a b (ha.trans hb.symm)).trans e2.symm)))
    exact GlobalTheory.T.exists_lineBundleIso_normalisedAlongSection_retraction X Y p e hep (V i ⊓ V k) _ _ (L i) (L k) w (r i) (r k) (hL' i) (hL' k)
      (fun _ h ↦ h.1) (fun _ h ↦ h.2) hw (hr' i) (hr' k)
  choose w hwi hwn using hw
  obtain ⟨N, hN, hv⟩ := GlobalTheory.T.lineBundle_glue_of_openCover_cocycle X Ix (fun i ↦ p ⁻¹ᵁ V i) L w (fun x ↦ hV (p x)) hL' hwi
    fun i j k x a b d ha hb hd ↦ GlobalTheory.T.normalised_lineBundleIso_cocycle_identity X Y p e hep hp (V i ⊓ V j ⊓ V k) _ _ _ _ _ _ (L i) (L j) (L k)
      (w i j) (w j k) (w i k) (r i) (r j) (r k) (hL' i) (hL' j) (hL' k) (fun _ h ↦ h)
      (fun _ h ↦ ⟨⟨h.1, h.1.2, h.2⟩, h.1.1, h.2⟩) (hwi i j) (hwi j k) (hwi i k) (hwn i j) (hwn j k) (hwn i k)
      x a b d ⟨⟨(hL' i).le a ha, (hL' j).le b hb⟩, (hL' k).le d hd⟩ ha hb hd
  have hNc : ∀ i, GlobalTheory.CechPic.pull (f i) (cls N hN) = c i := fun i ↦ by
    obtain ⟨v, hv⟩ := hv i
    rw [← hcl i, ← cls_pull hN (f i) (pull_isLB hN _)]
    exact (cls_eq_iff _ _).2 (GlobalTheory.T.lineBundleIso_pull_of_isLineBundleIsoOnOpen X _ _ N (L i) v (f i) hv (hfm i))
  refine ⟨cls N hN - GlobalTheory.CechPic.pull p (GlobalTheory.CechPic.pull e (cls N hN)), ?_, fun i ↦ ?_⟩
  · rw [map_sub, ← pull_comp e p, hep, pull_id, sub_self]
  · obtain ⟨t, ht⟩ := lifts i _ ((f i ≫ p) ≫ e) fun z ↦ by
      rw [Scheme.Hom.comp_apply]
      change p (e _) ∈ V i
      rw [hpe, Scheme.Hom.comp_apply]
      exact hfm i z
    rw [map_sub, hNc, ← pull_comp (f i) p, ← pull_comp (f i ≫ p) e, ← ht, pull_comp, hNc,
      hrig i _ t _ ht, sub_zero]

end GlobalTheory.PicGlue
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

noncomputable section

namespace GlobalTheory.ConjFrame

theorem comm_tensCastR_symm_map {E : Type} [Field E] [NumberField E] {F1 F2 : Subfield E} (h : F1 = F2)
    (σ : E →ₐ[F1] E) (τ : E →ₐ[F2] E) (hστ : ∀ x, σ x = τ x) (x : E ⊗[F2] FiniteAdeleRing (𝓞 F2) F2) :
    Algebra.TensorProduct.comm F1 (FiniteAdeleRing (𝓞 F1) F1) E
        ((GlobalTheory.StdFrame.tensCastR h).symm (Algebra.TensorProduct.map τ (AlgHom.id F2 (FiniteAdeleRing (𝓞 F2) F2)) x)) =
      Formalism.UG.sigR σ (FiniteAdeleRing (𝓞 F1) F1)
        (Algebra.TensorProduct.comm F1 (FiniteAdeleRing (𝓞 F1) F1) E ((GlobalTheory.StdFrame.tensCastR h).symm x)) := by
  subst h
  have hc : ∀ y, (GlobalTheory.StdFrame.tensCastR (rfl : F1 = F1)).symm y =
      (Algebra.TensorProduct.comm F1 (FiniteAdeleRing (𝓞 F1) F1) E).symm y := fun _ => rfl
  simp only [hc]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [Formalism.UG.sigR, Algebra.TensorProduct.map_tmul, hστ]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem swapAE_conjAL : ∀ {D : D7} (hF : D.host.F = maximalRealSubfield D.host.E) (x : ReciprocityTheory.Aut.AL D.host.E), Formalism.IndefR.Lev.swapAE D ((GlobalTheory.StdFrame.tensCastR hF).symm (ReciprocityTheory.Aut.conjAL D.host.E x)) = Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (Formalism.IndefR.Lev.swapAE D ((GlobalTheory.StdFrame.tensCastR hF).symm x)) := by
  intro D hF x
  exact comm_tensCastR_symm_map hF D.sp.cm.sig ((IsCMField.complexConj D.host.E).toAlgHom) (fun _ => rfl) x

end GlobalTheory.ConjFrame

end
end

module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle292
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle452
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCocycleCoboundaryCommaLocalBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle155
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle157
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle290
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle675
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle503
public import Mathlib.RingTheory.MvPowerSeries.Expand
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle684
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle686
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
import ReciprocityTheory.DualLattices.Bundle010
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CoverO

def counitCoef {R : Type} [CommRing R] {C C' : Type} [Category.{0} C] [Category.{0} C']
    (F : C ⥤ CommAlgCat.{0} R) {G : C' ⥤ C} {H : C ⥤ C'} (adj : G ⊣ H) :
    CoefMap (RingHom.id R) (G ⋙ F) F where
  G := H
  α V := (mp F (adj.counit.app V)).toRingHom
  naturality {V V'} φ b := by
    change mp F (adj.counit.app V') (mp F (G.map (H.map φ)) b) = mp F φ (mp F (adj.counit.app V) b)
    rw [← mp_comp, ← mp_comp]
    have e := adj.counit.naturality φ
    simp only [Functor.comp_map, Functor.id_map] at e
    rw [e]
  smul V r b := by
    change mp F (adj.counit.app V) (r • b) = r • mp F (adj.counit.app V) b
    exact map_smul _ r b

theorem restrict_pull1_bijective_of_adj {R : Type} [CommRing R] {C C' : Type} [Category.{0} C]
    [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) (H : C ⥤ C') (adj : G ⊣ H) :
    Function.Bijective (CoefMap.restrict F G).pull1 := by
  have hl : ∀ c, (counitCoef F adj).pull1 ((CoefMap.restrict F G).pull1 c) = c := by
    intro c
    rw [← CoefMap.pullCohomologyOne_comp]
    exact (CoefMap.pullCohomologyOne_eq_of_natTrans _ (CoefMap.id F) adj.counit (fun T b ↦ rfl) c).trans
      (CoefMap.pullCohomologyOne_id c)
  have hr : ∀ c, (CoefMap.restrict F G).pull1 ((counitCoef F adj).pull1 c) = c := by
    intro c
    rw [← CoefMap.pullCohomologyOne_comp]
    refine ((CoefMap.pullCohomologyOne_eq_of_natTrans (CoefMap.id (G ⋙ F))
      ((counitCoef F adj).comp (CoefMap.restrict F G)) adj.unit (fun T b ↦ ?_) c).symm.trans
      (CoefMap.pullCohomologyOne_id c))
    change mp F (adj.counit.app (G.obj T)) (mp F (G.map (adj.unit.app T)) b) = b
    exact (mp_comp F (G.map (adj.unit.app T)) (adj.counit.app (G.obj T)) b).symm.trans
      ((congrArg (fun ξ ↦ mp F ξ b) (adj.left_triangle_components T)).trans (mp_id F (G.obj T) b))
  exact ⟨Function.LeftInverse.injective hl, Function.RightInverse.surjective hr⟩

theorem restrict_cover_affine_pull1_bijective (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R)
    (J : Type) (U : J → X.Opens) (hU : ⨆ i, U i = ⊤) :
    Function.Bijective (CoefMap.restrict (OAff s) (Monotone.functor
      (f := (Subtype.val : {V : X.affineOpens // ∃ i, V.1 ≤ U i} → X.affineOpens)) fun _ _ h ↦ h).op).pull1 := by
  let G : {V : X.affineOpens // ∃ i, V.1 ≤ U i}ᵒᵖ ⥤ AffOp X := (Monotone.functor
      (f := (Subtype.val : {V : X.affineOpens // ∃ i, V.1 ≤ U i} → X.affineOpens)) fun _ _ h ↦ h).op
  have hcov : ∀ T : AffOp X, ∃ (n : ℕ) (b : Fin n → (OAff s).obj T),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X) (u : T ⟶ S),
        IsUnit (mp (OAff s) u (b i)) →
          ∃ (t : {V : X.affineOpens // ∃ i, V.1 ≤ U i}ᵒᵖ) (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u := by
    intro T
    have hT : IsAffineOpen T.unop.1 := T.unop.2
    let Gs : Set Γ(X, T.unop.1) := {f | ∃ j, X.basicOpen f ≤ U j}
    have hG : Ideal.span Gs = ⊤ := by
      rw [← hT.self_le_iSup_basicOpen_iff]
      intro x hx
      have hxU : x ∈ ⨆ i, U i := by rw [hU]; trivial
      obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hxU
      obtain ⟨f, hf, hxf⟩ := hT.exists_basicOpen_le (V := U j) ⟨x, hj⟩ hx
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, ⟨j, hf⟩⟩, hxf⟩
    obtain ⟨F, hFG, hF⟩ := (Ideal.span_eq_top_iff_finite Gs).1 hG
    refine ⟨F.card, fun i ↦ (F.equivFin.symm i).1, ?_, ?_⟩
    · have hR : Set.range (fun i : Fin F.card ↦ (F.equivFin.symm i).1) = (F : Set Γ(X, T.unop.1)) := by
        ext f
        constructor
        · rintro ⟨i, rfl⟩; exact (F.equivFin.symm i).2
        · intro hf; exact ⟨F.equivFin ⟨f, hf⟩, by simp⟩
      exact hR ▸ hF
    · intro i S u hu
      obtain ⟨j, hj⟩ := hFG (F.equivFin.symm i).2
      set f : Γ(X, T.unop.1) := (F.equivFin.symm i).1
      have hW : IsAffineOpen (X.basicOpen f) := hT.basicOpen f
      have hWT : X.basicOpen f ≤ T.unop.1 := X.basicOpen_le f
      have hSW : S.unop.1 ≤ X.basicOpen f := by
        have h1 : X.basicOpen (X.presheaf.map (homOfLE (leOfHom u.unop)).op f) = S.unop.1 :=
          X.basicOpen_of_isUnit hu
        rw [Scheme.basicOpen_res] at h1
        rw [← h1]; exact inf_le_right
      let t : {V : X.affineOpens // ∃ i, V.1 ≤ U i} := ⟨⟨_, hW⟩, j, hj⟩
      refine ⟨Opposite.op t, (homOfLE (show (⟨_, hW⟩ : X.affineOpens) ≤ T.unop from hWT)).op,
        (homOfLE (show S.unop ≤ (⟨_, hW⟩ : X.affineOpens) from hSW)).op, ?_⟩
      exact Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  have hdir : ∀ (t₁ t₂ : {V : X.affineOpens // ∃ i, V.1 ≤ U i}ᵒᵖ) (S : AffOp X), (G.obj t₁ ⟶ S) →
      (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → (OAff s).obj S), Ideal.span (Set.range b) = ⊤ ∧
        ∀ (i : Fin n) (S' : AffOp X) (u : S ⟶ S'), IsUnit (mp (OAff s) u (b i)) →
          ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S') := by
    intro t₁ t₂ S h₁ h₂
    refine ⟨1, fun _ ↦ 1, ?_, fun _ S' u _ ↦ ?_⟩
    · rw [Ideal.span_eq_top_iff_finite]
      exact ⟨{1}, by simp, by simp⟩
    · obtain ⟨j, hj⟩ := t₁.unop.2
      have hS'S : S'.unop ≤ S.unop := leOfHom u.unop
      have hS1 : S.unop ≤ t₁.unop.1 := leOfHom h₁.unop
      have hS2 : S.unop ≤ t₂.unop.1 := leOfHom h₂.unop
      let t₃ : {V : X.affineOpens // ∃ i, V.1 ≤ U i} := ⟨S'.unop, j, le_trans (hS'S.trans hS1) hj⟩
      refine ⟨Opposite.op t₃, ⟨(homOfLE (show t₃ ≤ t₁.unop from hS'S.trans hS1)).op⟩,
        ⟨(homOfLE (show t₃ ≤ t₂.unop from hS'S.trans hS2)).op⟩, ⟨𝟙 _⟩⟩
  have H := _root_.GlobalTheory.CechDR.hasLoc_OAff s
  have hs := _root_.GlobalTheory.sep_of_factoring_cover (OAff s) G H hcov
  have hg := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (OAff s) G H hcov hdir
  have hv := _root_.GlobalTheory.CatCoh.Desc.Basis.oneCocycle_vanishing_comma_of_basis (OAff s) G H hcov hdir
  exact ⟨_root_.GlobalTheory.CatCoh.CoefMap.restrict_pull1_injective_of_sep_glue _ _ hs hg,
    _root_.GlobalTheory.CatCoh.pull1_restrict_surjective_of_comma _ _ hs hg hv⟩

theorem restrict_bijective : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Type) [Finite J] [SemilatticeInf J] (U : J → X.affineOpens) (hU : Monotone U), (∀ i j, (U (i ⊓ j)).1 = (U i).1 ⊓ (U j).1) → ⨆ i, (U i).1 = ⊤ → Function.Bijective (CoefMap.restrict (OAff s) hU.functor.op).pull1 := by
  intro R _ X s J _ _ U hU hinf hcov
  classical
  haveI := Fintype.ofFinite J
  let B : Type := {V : X.affineOpens // ∃ i, V.1 ≤ (U i).1}
  have hne : ∀ V : B, (Finset.univ.filter fun i => V.1.1 ≤ (U i).1).Nonempty := fun V => by
    obtain ⟨i, hi⟩ := V.2
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩
  let σ : B → J := fun V => (Finset.univ.filter fun i => V.1.1 ≤ (U i).1).inf' (hne V) id
  let u : J → B := fun i => ⟨U i, i, le_rfl⟩
  have hσ : ∀ V : B, V.1.1 ≤ (U (σ V)).1 := fun V =>
    Finset.inf'_induction (p := fun i => V.1.1 ≤ (U i).1) (hne V) id
      (fun a ha b hb => by rw [hinf]; exact le_inf ha hb) fun i hi => (Finset.mem_filter.1 hi).2
  have gc : GaloisConnection σ u := fun V i =>
    ⟨fun h => (hσ V).trans (hU h), fun h =>
      Finset.inf'_le (s := Finset.univ.filter fun i : J => V.1.1 ≤ (U i).1) (id : J → J)
        (Finset.mem_filter.2 ⟨Finset.mem_univ i, h⟩)⟩
  let incl : Bᵒᵖ ⥤ AffOp X := (Monotone.functor (f := (Subtype.val : B → X.affineOpens)) fun _ _ h ↦ h).op
  have b1 : Function.Bijective (CoefMap.restrict (OAff s) incl).pull1 :=
    restrict_cover_affine_pull1_bijective R X s J (fun i => (U i).1) hcov
  have b2 := restrict_pull1_bijective_of_adj (incl ⋙ OAff s) gc.monotone_u.functor.op
    gc.monotone_l.functor.op gc.adjunction.op
  have e : ∀ c, (CoefMap.restrict (OAff s) hU.functor.op).pull1 c =
      (CoefMap.restrict (incl ⋙ OAff s) gc.monotone_u.functor.op).pull1
        ((CoefMap.restrict (OAff s) incl).pull1 c) := fun c =>
    (CoefMap.pullCohomologyOne_eq_of_natTrans (CoefMap.restrict (OAff s) hU.functor.op)
      ((CoefMap.restrict (OAff s) incl).comp (CoefMap.restrict (incl ⋙ OAff s) gc.monotone_u.functor.op))
      (𝟙 _) (fun T b => mp_id (OAff s) _ b) c).trans (CoefMap.pullCohomologyOne_comp _ _ c)
  have := b2.comp b1
  exact (funext e : _ = _) ▸ this

end GlobalTheory.CoverO
end
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat



theorem GlobalTheory.CmpG.comparison : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (U U' X : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (u l : F.B) (Gm : Matrix (Fin h) (Fin d ⊕ Fin k) F.B) (W : Matrix (Fin d ⊕ Fin k) (Fin h) F.B), IsUnit U → IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) → IsNil F.θ F.σ (U * blk d k (p : F.B) 1) → F.τ ∣ u - 1 → X * (U' * blk d k (p : F.B) 1) = U * blk d k (p : F.B) 1 * X.map F.σ → (∀ i j, F.τ ∣ X i j - (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) i j) → F.σ l = u * l → F.τ ∣ l - 1 → U * blk d k (p : F.B) 1 * Gm.transpose.map F.σ = (p : F.B) • Gm.transpose → U' * blk d k (p : F.B) 1 * W.map F.σ = ((p : F.B) * u) • W → (∀ i m, F.τ ∣ W i m - Gm m i) → X * W = l • Gm.transpose := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F d k h U U' X u l Gm W hU hN1 hN2 hu hX hXc hl hlc hG hW hWc
  classical
  haveI := ReciprocityTheory.PGsh.Ainf.O_local O hv
  obtain ⟨c, hc⟩ := hu
  have hue : u = 1 + F.τ * c := by rw [← hc]; ring
  set w : F.B := 1 - F.τ * c with hwdef
  have hwu : w * u = 1 := by rw [hue, hwdef]; linear_combination (-(c * c)) * F.τ_sq
  have hτ0 : F.θ F.τ = 0 := GlobalTheory.WinLift.theta_tau F hv hε
  have hθu : F.θ u = 1 := by rw [hue, map_add (f := _), map_one, map_mul, hτ0, zero_mul, add_zero]
  have hθw : F.θ w = 1 := by rw [hwdef, map_sub, map_one, map_mul, hτ0, zero_mul, sub_zero]
  have hwU : IsUnit w := ⟨⟨w, u, hwu, by rw [mul_comm]; exact hwu⟩, rfl⟩
  set P := blk d k (p : F.B) 1 with hP
  set D : Matrix (Fin d ⊕ Fin k) (Fin h) F.B := X * W - l • Gm.transpose with hDdef
  have hsm : (l • Gm.transpose).map F.σ = F.σ l • Gm.transpose.map F.σ :=
    Matrix.ext fun i j => by simp
  have hsub : D.map F.σ = (X * W).map F.σ - (l • Gm.transpose).map F.σ :=
    by rw [hDdef]; exact Matrix.ext fun i j => by simp only [Matrix.map_apply, Matrix.sub_apply, map_sub]
  have hD : U * P * D.map F.σ = ((p : F.B) * u) • D := by
    rw [hsub, Matrix.map_mul, hsm, Matrix.mul_sub, Matrix.mul_smul, ← Matrix.mul_assoc, ← hX,
      Matrix.mul_assoc, hW, hG, hl, Matrix.mul_smul, smul_smul, hDdef, smul_sub, smul_smul]
    congr 1
    rw [show u * l * (p : F.B) = p * u * l by ring]
  set U₁ := w • U with hU₁
  have hD1 : U₁ * P * D.map F.σ = (p : F.B) • D := by
    rw [hU₁, Matrix.smul_mul, Matrix.smul_mul, hD, smul_smul,
      show w * ((p : F.B) * u) = p by linear_combination (p : F.B) * hwu]
  have hUdet : IsUnit U.det := (Matrix.isUnit_iff_isUnit_det U).1 hU
  have hU₁u : IsUnit U₁ := by
    rw [Matrix.isUnit_iff_isUnit_det, hU₁, Matrix.det_smul]
    exact (hwU.pow _).mul hUdet
  have hinv : U₁.transpose⁻¹ = u • U.transpose⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [hU₁, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hwu, one_smul,
      Matrix.mul_nonsing_inv _ (by rw [Matrix.det_transpose]; exact hUdet)]
  have hp : ¬IsUnit (p : O) := Fact.out
  have hN1' : IsNil F.θ F.σ (U₁.transpose⁻¹ * blk d k 1 (p : F.B)) := by
    refine GlobalTheory.WinLift.isNil_of_theta_eq p F.θ F.σ hp F.σ_pow _ _ (fun i j => ?_) hN1
    rw [hinv, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, map_mul, hθu, one_mul]
  have hN2' : IsNil F.θ F.σ (U₁ * P) := by
    refine GlobalTheory.WinLift.isNil_of_theta_eq p F.θ F.σ hp F.σ_pow _ _ (fun i j => ?_) hN2
    rw [hU₁, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, map_mul, hθw, one_mul]
  have key := (GlobalTheory.TauUniq.eq_zero_of_tau_dvd p C v O hv ε hε F d k h U₁ hU₁u hN1' hN2').2
  have hdec : D = (X - 1) * W + (W - Gm.transpose) - (l - 1) • Gm.transpose := by
    rw [hDdef, Matrix.sub_mul, Matrix.one_mul, sub_smul, one_smul]; abel
  have hτD : ∀ i m, F.τ ∣ D i m := by
    intro i m
    rw [hdec, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.transpose_apply]
    refine dvd_sub (dvd_add (Finset.dvd_sum fun j _ => ?_) (hWc i m)) (Dvd.dvd.mul_right hlc _)
    exact Dvd.dvd.mul_right (hXc i j) _
  have hD0 : D = 0 := by
    refine Matrix.ext fun i m => ?_
    have hcol := key (fun i => D i m) (funext fun i => by
      have := congrArg (fun M => M i m) hD1
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this) (fun i => hτD i m)
    exact congrFun hcol i
  exact sub_eq_zero.1 hD0
end

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog.FrobQL

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q]

theorem in_add {σ : Type} {N : Ideal B} {f g : MvPowerSeries σ Q} (hf : In N f) (hg : In N g) :
    In N (f + g) := fun α => by
  obtain ⟨a, ha, e⟩ := hf α
  obtain ⟨b, hb, e'⟩ := hg α
  exact ⟨a + b, N.add_mem ha hb, by rw [map_add (f := _), e, e', map_add (f := _)]⟩

theorem in_mono {σ : Type} {N N' : Ideal B} (h : N ≤ N') {f : MvPowerSeries σ Q} (hf : In N f) :
    In N' f := fun α => by
  obtain ⟨a, ha, e⟩ := hf α
  exact ⟨a, h ha, e⟩

theorem in_map {σ : Type} (t : B →+* B) (s : Q →+* Q)
    (hs : ∀ b, s (algebraMap B Q b) = algebraMap B Q (t b))
    {N N' : Ideal B} (hN : ∀ b ∈ N, t b ∈ N') {f : MvPowerSeries σ Q} (hf : In N f) :
    In N' (map s f) := fun α => by
  obtain ⟨a, ha, e⟩ := hf α
  exact ⟨t a, hN a ha, by rw [coeff_map, e, hs]⟩

theorem in_expand {σ : Type} (p : ℕ) (hp : p ≠ 0) {N : Ideal B} {f : MvPowerSeries σ Q}
    (hf : In N f) : In N (expand p hp f) := fun α => by
  by_cases h : ∀ i, p ∣ α i
  · obtain ⟨m, hm⟩ : ∃ m : σ →₀ ℕ, p • m = α := ⟨α.mapRange (fun a ↦ a / p) (by simp),
      by ext i; simp [Nat.mul_div_cancel' (h i)]⟩
    rw [← hm, coeff_expand_smul]
    exact hf m
  · push_neg at h
    obtain ⟨i, hi⟩ := h
    exact ⟨0, N.zero_mem, by rw [coeff_expand_of_not_dvd p hp f hi, map_zero]⟩

theorem frob_congr (p : ℕ) [Fact p.Prime] (t : B →+* B) (ht : ∀ b, (p : B) ∣ t b - b ^ p)
    (hu : ¬IsUnit (p : B)) {τ : Type} (w : MvPowerSeries τ B) (α : τ →₀ ℕ) :
    coeff α (w ^ p - expand p (Fact.out : p.Prime).ne_zero (map t w)) ∈
      Ideal.span {(p : B)} := by
  set I : Ideal B := Ideal.span {(p : B)}
  haveI : CharP (B ⧸ I) p := CharP.quotient B p (by simpa [mem_nonunits_iff] using hu)
  haveI : ExpChar (B ⧸ I) p := ExpChar.prime Fact.out
  have hw : map (Ideal.Quotient.mk I) (map t w) =
      map (frobenius (B ⧸ I) p) (map (Ideal.Quotient.mk I) w) := by
    ext n
    simp only [coeff_map, frobenius_def]
    rw [← map_pow, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact ht _
  have key : map (Ideal.Quotient.mk I)
      (w ^ p - expand p (Fact.out : p.Prime).ne_zero (map t w)) = 0 := by
    rw [map_sub, map_pow, map_expand, hw, ← map_expand, map_frobenius_expand, sub_self]
  have := congrArg (coeff α) key
  rwa [coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem] at this

end GlobalTheory.QLog.FrobQL

namespace GlobalTheory.QLog.FrobQL

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q]

theorem frob_eq_expand (p : ℕ) (hp : p ≠ 0) {σ : Type} (s : Q →+* Q) (f : MvPowerSeries σ Q) :
    frob p s f = expand p hp (map s f) := by
  simp only [frob, expand, substAlgHom_apply]

theorem cob1_expand_frobenius_map (p : ℕ) (hp : p ≠ 0) (t : B →+* B) (s : Q →+* Q)
    (hs : ∀ b, s (algebraMap B Q b) = algebraMap B Q (t b)) {d : ℕ}
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) (h0 : ∀ i, constantCoeff (μ i) = 0)
    (f : MvPowerSeries (Fin d) Q) :
    cob1 (up Q μ) (expand p hp (map s f)) =
      (subst (up Q fun i => μ i ^ p) (map s f) -
        subst (up Q fun i => expand p hp (map t (μ i))) (map s f)) +
        expand p hp (map s (cob1 (up Q μ) f)) := by
  have hU : HasSubst (up Q μ) := hasSubst_of_constantCoeff_zero fun i => by
    simp [up, constantCoeff_map, h0]
  have hXp : HasSubst (fun i : Fin d => (X i : MvPowerSeries (Fin d) Q) ^ p) := HasSubst.X_pow hp
  have hL : HasSubst (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) Q)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hR : HasSubst (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) Q)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hexp : ∀ {σ : Type} (g : MvPowerSeries σ Q), expand p hp g = subst (fun i => X i ^ p) g :=
    fun g => by simp only [expand, substAlgHom_apply]
  have hmapU : (fun i => map s (up Q μ i)) = up Q (fun i => map t (μ i)) := by
    funext i; ext n; simp [up, coeff_map, hs]
  have e1 : subst (up Q μ) (expand p hp (map s f)) = subst (up Q fun i => μ i ^ p) (map s f) := by
    rw [hexp, subst_comp_subst_apply hXp hU]
    congr 1
    funext i
    rw [subst_pow hU, subst_X hU]
    simp [up, map_pow]
  have e2 : inL (expand p hp (map s f)) = subst (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) Q) ^ p) (map s f) := by
    rw [inL, hexp, subst_comp_subst_apply hXp hL]
    congr 1
    funext i
    rw [subst_pow hL, subst_X hL]
  have e3 : inR (expand p hp (map s f)) = subst (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) Q) ^ p) (map s f) := by
    rw [inR, hexp, subst_comp_subst_apply hXp hR]
    congr 1
    funext i
    rw [subst_pow hR, subst_X hR]
  have hV : HasSubst (up Q fun i => map t (μ i)) := hasSubst_of_constantCoeff_zero fun i => by
    simp [up, constantCoeff_map, h0]
  have m1 : map s (subst (up Q μ) f) = subst (up Q fun i => map t (μ i)) (map s f) := by
    rw [map_subst hU, hmapU]
  have m2 : map s (subst (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) Q)) f) =
      subst (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) Q)) (map s f) := by
    rw [map_subst hL]; congr 1; funext i; simp
  have m3 : map s (subst (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) Q)) f) =
      subst (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) Q)) (map s f) := by
    rw [map_subst hR]; congr 1; funext i; simp
  have x1 : expand p hp (subst (up Q fun i => map t (μ i)) (map s f)) =
      subst (up Q fun i => expand p hp (map t (μ i))) (map s f) := by
    rw [expand_subst p hp hV]; congr 1; funext i; simp [up, map_expand]
  have x2 : expand p hp (subst (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) Q)) (map s f)) =
      subst (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) Q) ^ p) (map s f) := by
    rw [expand_subst p hp hL]; congr 1; funext i; simp
  have x3 : expand p hp (subst (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) Q)) (map s f)) =
      subst (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) Q) ^ p) (map s f) := by
    rw [expand_subst p hp hR]; congr 1; funext i; simp
  have e4 : expand p hp (map s (cob1 (up Q μ) f)) =
      subst (up Q fun i => expand p hp (map t (μ i))) (map s f) -
        subst (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) Q) ^ p) (map s f) -
        subst (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) Q) ^ p) (map s f) := by
    simp only [cob1, inL, inR, map_sub, m1, m2, m3, x1, x2, x3]
  rw [cob1, e1, e2, e3, e4]
  abel

end GlobalTheory.QLog.FrobQL

namespace GlobalTheory.QLog


open GlobalTheory.QLog.FrobQL in
theorem ql_frob : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O →
    ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ)
    (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' →
    (∀ i, map F.θ (μ' i) = c.μ i) → ∀ f : MvPowerSeries (Fin d) F.Q, QL μ' ⊤ f →
    QL μ' ⊤ (frob p F.s f) ∧
      (In (RingHom.ker F.θ) (cob1 (up F.Q μ') f) →
        QL μ' (Ideal.span {(p : F.B)}) (frob p F.s f)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ ε hε F G d c μ' hμ _ f hf
  have hpp : p.Prime := Fact.out
  have hp : p ≠ 0 := hpp.ne_zero
  have hu : ¬IsUnit (p : F.B) := fun h =>
    (Fact.out : ¬IsUnit (p : O)) (by simpa using h.map F.θ)
  rw [frob_eq_expand p hp]
  have hc0 : constantCoeff (expand p hp (map F.s f)) = 0 := by
    rw [constantCoeff_expand, constantCoeff_map, hf.1, map_zero]
  have hlin : ∀ i, lin (expand p hp (map F.s f)) i = 0 := fun i => by
    unfold lin
    exact coeff_expand_of_not_dvd p hp _ (i := i) (by simpa using hpp.not_dvd_one)
  have hJ : ∀ x ∈ Ideal.span {(p : F.B)}, ∃ y ∈ Ideal.span {(p : F.B)}, x ^ p = p * y := by
    intro x hx
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    have e : (p : F.B) ^ p = p * p ^ (p - 1) := by
      rw [← pow_succ']; congr 1; have := hpp.one_lt; omega
    refine ⟨(p : F.B) ^ (p - 1) * b ^ p, Ideal.mul_mem_right _ _
      (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _ (by have := hpp.one_lt; omega)), ?_⟩
    rw [mul_pow, e]; ring
  have hD : DIn (⊤ : Ideal F.B) (map F.s f) := by
    have h := GlobalTheory.T.divided_in_of_quasi_logarithm p F.B O F.Q F.θ F.frame d μ' hμ ⊤ f hf
    intro α i
    obtain ⟨b, _, e⟩ := h α i
    exact ⟨F.σ b, trivial, by rw [coeff_map, ← map_natCast F.s, ← map_mul, e, F.s_alg]⟩
  have hK := GlobalTheory.T.subst_sub_subst_mem_mul_of_coeff_sub_mem p F.B O F.Q F.θ F.frame _ hJ (Fin d) (Fin d ⊕ Fin d) ⊤ (map F.s f)
    (fun i => μ' i ^ p) (fun i => expand p hp (map F.σ (μ' i))) hD
    (fun i => by rw [map_pow, hμ.const i, zero_pow hp])
    (fun i => by rw [constantCoeff_expand, constantCoeff_map, hμ.const i, map_zero])
    (fun i α => frob_congr p F.σ F.σ_pow hu (μ' i) α)
  rw [Ideal.mul_top] at hK
  simp only [QL]
  rw [cob1_expand_frobenius_map p hp F.σ F.s F.s_alg μ' hμ.const f]
  refine ⟨⟨hc0, fun i => ⟨0, trivial, by rw [hlin, map_zero]⟩,
    in_add (in_mono le_top hK) (in_expand p hp (in_map F.σ F.s F.s_alg (N' := ⊤) (fun _ _ => Submodule.mem_top) hf.2.2))⟩,
    fun hker => ⟨hc0, fun i => ⟨0, Ideal.zero_mem _, by rw [hlin, map_zero]⟩,
      in_add hK (in_expand p hp (in_map F.σ F.s F.s_alg ?_ hker))⟩⟩
  intro b hb
  rw [RingHom.mem_ker] at hb
  obtain ⟨y, _, hy⟩ := F.frame.pd b hb
  obtain ⟨z, hz⟩ := F.σ_pow b
  rw [Ideal.mem_span_singleton]
  exact ⟨z + y, by rw [mul_add, ← hz, ← hy]; ring⟩

end GlobalTheory.QLog
end
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

namespace Katz

theorem existsUnique_semiHom_ev (p : ℕ) (k k' : Type) [CommRing k] [CommRing k'] (σ : k →+* k')
    (d e : ℕ) (G : PDivGroup p k) (G' : PDivGroup p k') (c : Chart G d) (c' : Chart G' e)
    (s : SemiHom σ G' G) :
    ∃! φ : Fin d → MvPowerSeries (Fin e) k', ∀ n j, c'.ev n (φ j) = s.app n (c.x n j) := by
  have h := fun j : Fin d => existsUnique_evA_eq_of_presents k' (Fin e) G'.A c'.x c'.nil
    (fun n => (G'.res n : G'.A (n + 1) →ₐ[k'] G'.A n)) c'.res c'.presents
    (fun n => s.app n (c.x n j)) (fun n => by
      change G'.res n (s.app (n + 1) (c.x (n + 1) j)) = _
      rw [s.res_app, c.res])
  choose φ hφ hu using h
  refine ⟨φ, fun n j => hφ j n, fun ψ hψ => funext fun j => hu j (ψ j) fun n => hψ n j⟩

end Katz

end GlobalTheory
end

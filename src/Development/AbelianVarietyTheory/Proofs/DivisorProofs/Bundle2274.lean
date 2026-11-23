module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle228
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDiagInt
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2251
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
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
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GermConst

theorem germ_constFn_origin : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] (O : G.left.Opens) (hO : origin G ∈ O) (r : R), (G.left.presheaf.germ O (origin G) hO).hom (constFn G.hom O r) = constO G r := by
  intro R _ _ G _ O hO r
  have e := Scheme.Hom.appLE_map G.hom (U := ⊤) (V := ⊤) (fun _ _ => trivial) (homOfLE (le_top : O ≤ ⊤)).op
  have h : constFn G.hom O r = (G.left.presheaf.map (homOfLE (le_top : O ≤ ⊤)).op).hom (constFn G.hom ⊤ r) := by
    unfold constFn
    rw [← e]
    rfl
  rw [h, TopCat.Presheaf.germ_res_apply]
  rfl

end GlobalTheory.GermConst
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechKS.PrismDlog

noncomputable def dl {B : Type} [CommRing B] (a : DualNumber B) : B := a.snd * Ring.inverse a.fst

theorem dl_mul {B : Type} [CommRing B] {a b : DualNumber B} (ha : IsUnit a.fst) (hb : IsUnit b.fst) :
    dl (a * b) = dl a + dl b := by
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  have e : (a * b).fst = ((x * y : Bˣ) : B) := by simp [hx, hy]
  have e2 : (a * b).snd = a.fst * b.snd + a.snd * b.fst := by
    rw [TrivSqZeroExt.snd_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
  have h1 : (x : B) * ((x⁻¹ : Bˣ) : B) = 1 := Units.mul_inv x
  have h2 : (y : B) * ((y⁻¹ : Bˣ) : B) = 1 := Units.mul_inv y
  rw [dl, dl, dl, e, e2, Ring.inverse_unit, ← hx, ← hy, Ring.inverse_unit, Ring.inverse_unit, mul_inv_rev,
    Units.val_mul]
  linear_combination (b.snd * ((y⁻¹ : Bˣ) : B)) * h1 + (a.snd * ((x⁻¹ : Bˣ) : B)) * h2

theorem dl_inl {B : Type} [CommRing B] (b : B) : dl (TrivSqZeroExt.inl b : DualNumber B) = 0 := by
  simp [dl]

theorem dl_one_add {B : Type} [CommRing B] {a : DualNumber B} (ha : a.fst = 0) : dl (1 + a) = a.snd := by
  simp [dl, ha]

theorem dl_map {R B B' : Type} [CommRing R] [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B'] (ρ : B →ₐ[R] B')
    {a : DualNumber B} (ha : IsUnit a.fst) : dl (dualAlg ρ a) = ρ (dl a) := by
  obtain ⟨x, hx⟩ := ha
  have e : (dualAlg ρ a).fst = ((Units.map (ρ : B →* B') x : B'ˣ) : B') := by simp [hx]
  rw [dl, dl, e, ← hx, Ring.inverse_unit, Ring.inverse_unit, snd_dualAlg, map_mul]
  simp

theorem snd_eq_of_mul {B : Type} [CommRing B] {l U X Y : DualNumber B} (hl : l.fst = 0) (hU : IsUnit U.fst)
    (hX : IsUnit X.fst) (hY : IsUnit Y.fst) (h : (1 + l) * U = X * Y) : l.snd = dl X + dl Y - dl U := by
  have h1 : IsUnit (1 + l).fst := by simp [hl]
  have := congrArg dl h
  rw [dl_mul h1 hU, dl_mul hX hY, dl_one_add hl] at this
  rw [← this]; ring

theorem isUnit_fst {B : Type} [CommRing B] {a : DualNumber B} (h : IsUnit a) : IsUnit a.fst :=
  h.map (TrivSqZeroExt.fstHom B B B)

theorem valR_cocycle {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) {C : Type} [CommRing C] (w : Sp C ⟶ X)
    (a b k : L.ι) (h : ⊤ ≤ w ⁻¹ᵁ (L.U a ⊓ L.U b ⊓ L.U k)) :
    valR w _ (L.g a b).val * valR w _ (L.g b k).val = valR w _ (L.g a k).val := by
  have := congrArg (fun z ↦ valR w _ (z : Γ(X, L.U a ⊓ L.U b ⊓ L.U k)ˣ).val) (hL.cocycle a b k)
  simp only [Units.val_mul] at this
  rw [GlobalTheory.Points.valR_mul w _ h] at this
  simp only [res, Units.coe_map, MonoidHom.coe_coe] at this
  rwa [GlobalTheory.Points.valR_res w _ h, GlobalTheory.Points.valR_res w _ h, GlobalTheory.Points.valR_res w _ h] at this

theorem isUnit_valR {X : Scheme.{0}} {C : Type} [CommRing C] (w : Sp C ⟶ X) (U : X.Opens) (h : ⊤ ≤ w ⁻¹ᵁ U)
    (f : Γ(X, U)ˣ) : IsUnit (valR w U f.val) := by
  rw [GlobalTheory.Points.valR_eq w U h]; exact f.isUnit.map _

theorem evalAt_eq_valR {X : Scheme.{0}} {C : Type} [CommRing C] (x : Sp C ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f : Γ(X, U)) : evalAt x U h f = valR x U f := by
  rw [valR, dif_pos h]; rfl

variable {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A]

theorem fst_valR_trx (P : GPt A) {v : epsR K ⟶ A} (hv : IsTangent v) (U : A.left.Opens) (h : P.In U)
    (f : Γ(A.left, U)) : (valR (P.trx v) U f).fst = valR P.x U f := by
  have e := GlobalTheory.Points.valR_spMap_comp (TrivSqZeroExt.fstHom P.B P.B P.B).toRingHom (P.trx v) U (h.tr hv) f
  rw [(P.isTransl_trx v).red hv] at e
  rw [e]; rfl

theorem snd_l (L : LB A.left) (c : Small L.U → L.ι) (hc : ∀ T, ⊤ ≤ T.obj.x ⁻¹ᵁ L.U (c T))
    (u : ∀ T T' : Small L.U, (T ⟶ T') → T'.obj.B) (l : C2 (OSmall L.U))
    (hu : ∀ T T' φ, T'.obj.π (u T T' φ) = evalAt T'.obj.x (L.U (c T') ⊓ L.U (c T))
      (le_inf (hc T') (φ.hom.le_preimage (hc T))) (L.g (c T') (c T)).val)
    (hl : ∀ T T' T'' φ ψ, (l T T' T'' φ ψ : T''.obj.B) ∈ T''.obj.J ∧
      dpExp T''.obj.δ (l T T' T'' φ ψ) * u T T'' (φ ≫ ψ) = ψ.hom.φ (u T T' φ) * u T' T'' ψ)
    (R : GPt A) (hR : ∃ i, R.In (L.U i)) {T T' : Small L.U} (φ : T ⟶ T') (ψ : T' ⟶ ⟨R.ext, hR⟩) :
    TrivSqZeroExt.snd (R := R.B) (l T T' ⟨R.ext, hR⟩ φ ψ : DualNumber R.B) =
      dl (ψ.hom.φ (u T T' φ) : DualNumber R.B) + dl (u T' ⟨R.ext, hR⟩ ψ : DualNumber R.B) -
        dl (u T ⟨R.ext, hR⟩ (φ ≫ ψ) : DualNumber R.B) := by
  have hunit : ∀ (T T' : Small L.U) (φ : T ⟶ T'), IsUnit (T'.obj.π (u T T' φ)) := fun T T' φ ↦ by
    rw [hu]; exact (L.g _ _).isUnit.map _
  obtain ⟨hmem, heq⟩ := hl T T' ⟨R.ext, hR⟩ φ ψ
  rw [dpExp_sqDP _ hmem] at heq
  refine snd_eq_of_mul hmem (hunit T ⟨R.ext, hR⟩ (φ ≫ ψ)) ?_ (hunit T' ⟨R.ext, hR⟩ ψ) heq
  have e := ψ.hom.comm (u T T' φ)
  change _ = TrivSqZeroExt.fst _ at e
  rw [← e]
  exact (hunit T T' φ).map _

theorem snd_l' (L : LB A.left) (c : Small L.U → L.ι) (hc : ∀ T, ⊤ ≤ T.obj.x ⁻¹ᵁ L.U (c T))
    (u : ∀ T T' : Small L.U, (T ⟶ T') → T'.obj.B) (l : C2 (OSmall L.U))
    (hu : ∀ T T' φ, T'.obj.π (u T T' φ) = evalAt T'.obj.x (L.U (c T') ⊓ L.U (c T))
      (le_inf (hc T') (φ.hom.le_preimage (hc T))) (L.g (c T') (c T)).val)
    (hl : ∀ T T' T'' φ ψ, (l T T' T'' φ ψ : T''.obj.B) ∈ T''.obj.J ∧
      dpExp T''.obj.δ (l T T' T'' φ ψ) * u T T'' (φ ≫ ψ) = ψ.hom.φ (u T T' φ) * u T' T'' ψ)
    (R : GPt A) (hR : ∃ i, R.In (L.U i)) {T T' : Small L.U} (φ : T ⟶ T') (ψ : T' ⟶ ⟨R.ext, hR⟩)
    (χ : T ⟶ ⟨R.ext, hR⟩) (hχ : φ ≫ ψ = χ) :
    TrivSqZeroExt.snd (R := R.B) (l T T' ⟨R.ext, hR⟩ φ ψ : DualNumber R.B) =
      dl (ψ.hom.φ (u T T' φ) : DualNumber R.B) + dl (u T' ⟨R.ext, hR⟩ ψ : DualNumber R.B) -
        dl (u T ⟨R.ext, hR⟩ χ : DualNumber R.B) := by
  subst hχ; exact snd_l L c hc u l hu hl R hR φ ψ


open Classical in
noncomputable def Nf (L : LB A.left) (c : Small L.U → L.ι) (u : ∀ T T' : Small L.U, (T ⟶ T') → T'.obj.B)
    {v : epsR K ⟶ A} (hv : IsTangent v) (j : L.ι) : PtFn (A.hom ≫ 𝟙 (Sp K)) := fun P ↦
  if h : P.In (L.U j) then
    dl (u ⟨P.triv, ⟨j, h⟩⟩ ⟨P.ext, ⟨j, h⟩⟩ ⟨P.sec⟩ : DualNumber P.B) -
      dl (u ⟨(P.tr v).triv, ⟨j, h.tr hv⟩⟩ ⟨P.ext, ⟨j, h⟩⟩ ⟨P.tan hv⟩ : DualNumber P.B) -
      dl (valR (P.trx v) _ (L.g (c ⟨(P.tr v).triv, ⟨j, h.tr hv⟩⟩) j).val)
  else 0

end GlobalTheory.CechKS.PrismDlog


open GlobalTheory.CechKS.PrismDlog in
theorem GlobalTheory.CechKS.prism_trivialised : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (L : LB A.left), L.IsLB → ∀ (c : Small L.U → L.ι) (hc : ∀ T, ⊤ ≤ T.obj.x ⁻¹ᵁ L.U (c T)) (u : ∀ T T' : Small L.U, (T ⟶ T') → T'.obj.B) (l : C2 (OSmall L.U)), (∀ T T' φ, T'.obj.π (u T T' φ) = evalAt T'.obj.x (L.U (c T') ⊓ L.U (c T)) (le_inf (hc T') (φ.hom.le_preimage (hc T))) (L.g (c T') (c T)).val) → (∀ T T' T'' φ ψ, (l T T' T'' φ ψ : T''.obj.B) ∈ T''.obj.J ∧ dpExp T''.obj.δ (l T T' T'' φ ψ) * u T T'' (φ ≫ ψ) = ψ.hom.φ (u T T' φ) * u T' T'' ψ) → ∀ (v : epsR K ⟶ A) (hv : IsTangent v), ∃ N : L.ι → PtFn (A.hom ≫ 𝟙 (Sp K)), (∀ (j : L.ι) (P Q : GPt A) (φ : P.Hom Q) (hP : P.In (L.U j)), prism l hv φ ⟨j, hP⟩ = N j Q - φ.ρ (N j P)) ∧ ∀ (j j' : L.ι) (P : GPt A), P.In (L.U j) → P.In (L.U j') → N j P - N j' P = dlog L v j j' P := by
  intro K _ A _ L hL c hc u l hu hl v hv
  have hunit : ∀ (T T' : Small L.U) (φ : T ⟶ T'), IsUnit (T'.obj.π (u T T' φ)) := fun T T' φ ↦ by
    rw [hu]; exact (L.g _ _).isUnit.map _
  refine ⟨Nf L c u hv, ?_, ?_⟩
  · intro j P Q φ hP
    have hQ : Q.In (L.U j) := hP.map φ
    have k1 := snd_l' L c hc u l hu hl Q ⟨j, hQ⟩ (T := ⟨P.triv, ⟨j, hP⟩⟩) (T' := ⟨Q.triv, ⟨j, hQ⟩⟩) ⟨φ.triv⟩ ⟨Q.sec⟩
      ⟨P.sec ≫ φ.dual⟩ (by
        ext1
        apply Thick.Hom.ext'
        ext b
        · show (TrivSqZeroExt.inl (φ.ρ b) : DualNumber Q.B).fst = (dualAlg φ.ρ (TrivSqZeroExt.inl b)).fst
          simp
        · show (TrivSqZeroExt.inl (φ.ρ b) : DualNumber Q.B).snd = (dualAlg φ.ρ (TrivSqZeroExt.inl b)).snd
          simp)
    have k2 := snd_l' L c hc u l hu hl Q ⟨j, hQ⟩ (T := ⟨P.triv, ⟨j, hP⟩⟩) (T' := ⟨P.ext, ⟨j, hP⟩⟩) ⟨P.sec⟩ ⟨φ.dual⟩
      ⟨P.sec ≫ φ.dual⟩ rfl
    have k3 := snd_l' L c hc u l hu hl Q ⟨j, hQ⟩ (T := ⟨(P.tr v).triv, ⟨j, hP.tr hv⟩⟩)
      (T' := ⟨(Q.tr v).triv, ⟨j, hQ.tr hv⟩⟩) ⟨(φ.tr v).triv⟩ ⟨Q.tan hv⟩ ⟨P.tan hv ≫ φ.dual⟩ (by ext1; apply Thick.Hom.ext'; ext b <;> rfl)
    have k4 := snd_l' L c hc u l hu hl Q ⟨j, hQ⟩ (T := ⟨(P.tr v).triv, ⟨j, hP.tr hv⟩⟩)
      (T' := ⟨P.ext, ⟨j, hP⟩⟩) ⟨P.tan hv⟩ ⟨φ.dual⟩ ⟨P.tan hv ≫ φ.dual⟩ rfl
    obtain ⟨a, ha⟩ : ∃ a, a = c ⟨(P.tr v).triv, ⟨j, hP.tr hv⟩⟩ := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b, b = c ⟨(Q.tr v).triv, ⟨j, hQ.tr hv⟩⟩ := ⟨_, rfl⟩
    have hPa : (P.tr v).In (L.U a) := ha ▸ hc ⟨(P.tr v).triv, ⟨j, hP.tr hv⟩⟩
    have hQb : (Q.tr v).In (L.U b) := hb ▸ hc ⟨(Q.tr v).triv, ⟨j, hQ.tr hv⟩⟩
    have hQa : (Q.tr v).In (L.U a) := hPa.map (φ.tr v)
    have e1 : (u ⟨(P.tr v).triv, ⟨j, hP.tr hv⟩⟩ ⟨(Q.tr v).triv, ⟨j, hQ.tr hv⟩⟩ ⟨(φ.tr v).triv⟩ : DualNumber Q.B) =
        valR (Q.trx v) _ (L.g b a).val := by
      subst ha hb
      exact (hu ⟨(P.tr v).triv, ⟨j, hP.tr hv⟩⟩ ⟨(Q.tr v).triv, ⟨j, hQ.tr hv⟩⟩ ⟨(φ.tr v).triv⟩).trans
        (evalAt_eq_valR _ _ _ _)
    have e2 : valR (Q.trx v) _ (L.g a j).val = dualAlg φ.ρ (valR (P.trx v) _ (L.g a j).val) := by
      have e := GlobalTheory.Points.valR_spMap_comp (dualAlg φ.ρ : DualNumber P.B →+* DualNumber Q.B) (P.trx v) _
        (hPa.inf (hP.tr hv)) (L.g a j).val
      have e' : spMap (dualAlg φ.ρ : DualNumber P.B →+* DualNumber Q.B) ≫ P.trx v = Q.trx v := (φ.tr v).pt
      rw [e'] at e
      exact e
    have e3 := valR_cocycle L hL (Q.trx v) b a j ((hQb.inf hQa).inf (hQ.tr hv))
    have e4 : dl (valR (Q.trx v) _ (L.g b j).val) =
        dl (valR (Q.trx v) _ (L.g b a).val) + φ.ρ (dl (valR (P.trx v) _ (L.g a j).val)) := by
      rw [← e3, dl_mul (isUnit_fst (isUnit_valR _ _ (hQb.inf hQa) _))
        (isUnit_fst (isUnit_valR _ _ (hQa.inf (hQ.tr hv)) _)), e2,
        dl_map _ (isUnit_fst (isUnit_valR _ _ (hPa.inf (hP.tr hv)) _))]
    have d1 : dl (Q.sec.φ (u ⟨P.triv, ⟨j, hP⟩⟩ ⟨Q.triv, ⟨j, hQ⟩⟩ ⟨φ.triv⟩) : DualNumber Q.B) = 0 := dl_inl _
    have d2 : dl (φ.dual.φ (u ⟨P.triv, ⟨j, hP⟩⟩ ⟨P.ext, ⟨j, hP⟩⟩ ⟨P.sec⟩) : DualNumber Q.B) =
        φ.ρ (dl (u ⟨P.triv, ⟨j, hP⟩⟩ ⟨P.ext, ⟨j, hP⟩⟩ ⟨P.sec⟩ : DualNumber P.B)) :=
      dl_map φ.ρ (hunit ⟨P.triv, ⟨j, hP⟩⟩ ⟨P.ext, ⟨j, hP⟩⟩ ⟨P.sec⟩)
    have d3 : dl ((Q.tan hv).φ (u ⟨(P.tr v).triv, ⟨j, hP.tr hv⟩⟩ ⟨(Q.tr v).triv, ⟨j, hQ.tr hv⟩⟩
        ⟨(φ.tr v).triv⟩) : DualNumber Q.B) = dl (valR (Q.trx v) _ (L.g b a).val) := congrArg dl e1
    have d4 : dl (φ.dual.φ (u ⟨(P.tr v).triv, ⟨j, hP.tr hv⟩⟩ ⟨P.ext, ⟨j, hP⟩⟩ ⟨P.tan hv⟩) : DualNumber Q.B) =
        φ.ρ (dl (u ⟨(P.tr v).triv, ⟨j, hP.tr hv⟩⟩ ⟨P.ext, ⟨j, hP⟩⟩ ⟨P.tan hv⟩ : DualNumber P.B)) :=
      dl_map φ.ρ (hunit ⟨(P.tr v).triv, ⟨j, hP.tr hv⟩⟩ ⟨P.ext, ⟨j, hP⟩⟩ ⟨P.tan hv⟩)
    have k1' := k1.trans (congrArg (fun z ↦ z + _ - _) d1)
    have k2' := k2.trans (congrArg (fun z ↦ z + _ - _) d2)
    have k3' := k3.trans (congrArg (fun z ↦ z + _ - _) d3)
    have k4' := k4.trans (congrArg (fun z ↦ z + _ - _) d4)
    have key : ∀ {x1 x2 x3 x4 : DualNumber Q.B} {y1 y2 y3 y4 : Q.B}, x1.snd = y1 → x2.snd = y2 → x3.snd = y3 →
        x4.snd = y4 → ((x1 - x2) - (x3 - x4)).snd = (y1 - y2) - (y3 - y4) := by
      rintro x1 x2 x3 x4 _ _ _ _ rfl rfl rfl rfl
      simp
    refine (key k1' k2' k3' k4').trans ?_
    simp only [Nf, dif_pos hP, dif_pos hQ, map_sub]
    rw [← ha, ← hb, e4]
    ring
  · intro j j' P hj hj'
    obtain ⟨b, hb⟩ : ∃ b, b = c ⟨(P.tr v).triv, ⟨j, hj.tr hv⟩⟩ := ⟨_, rfl⟩
    have hPb : (P.tr v).In (L.U b) := hb ▸ hc ⟨(P.tr v).triv, ⟨j, hj.tr hv⟩⟩
    simp only [Nf, dif_pos hj, dif_pos hj']
    rw [← hb]
    have e3 := valR_cocycle L hL (P.trx v) b j j' ((hPb.inf (hj.tr hv)).inf (hj'.tr hv))
    have e4 : dl (valR (P.trx v) _ (L.g b j').val) =
        dl (valR (P.trx v) _ (L.g b j).val) + dl (valR (P.trx v) _ (L.g j j').val) := by
      rw [← e3, dl_mul (isUnit_fst (isUnit_valR _ _ (hPb.inf (hj.tr hv)) _))
        (isUnit_fst (isUnit_valR _ _ ((hj.inf hj').tr hv) _))]
    have e5 : dl (valR (P.trx v) _ (L.g j j').val) = dlog L v j j' P := by
      rw [dl, dlog, fst_valR_trx P hv _ (hj.inf hj')]
      have h1 : valR P.x _ (L.g j j').val * valR P.x _ (L.g j j')⁻¹.val = 1 := by
        rw [← GlobalTheory.Points.valR_mul _ _ (hj.inf hj'), Units.mul_inv, GlobalTheory.Points.valR_eq _ _ (hj.inf hj'), map_one]
      have h2 : Ring.inverse (valR P.x _ (L.g j j').val) = valR P.x _ (L.g j j')⁻¹.val :=
        Ring.inverse_unit (Units.mkOfMulEqOne _ _ h1)
      rw [h2]
    rw [← e5, e4]
    ring
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechKS

variable {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A]

theorem cechPt_over (P : GPt A) : P.x ≫ A.hom = spMap (algebraMap K P.B) :=
  (congrArg (P.x ≫ ·) (Category.comp_id _)).symm.trans P.w

@[reducible] def Pt.cst (P : GPt A) : GPt A where
  B := DualNumber P.B
  x := spMap (algebraMap P.B (DualNumber P.B)) ≫ P.x
  w := (congrArg (_ ≫ ·) (Category.comp_id A.hom)).trans (by
    rw [Category.assoc, cechPt_over, ← Cris.spMap_comp, ← IsScalarTower.algebraMap_eq])

theorem Pt.In.cst {P : GPt A} {U : A.left.Opens} (h : P.In U) : P.cst.In U :=
  fun _ _ ↦ h (Set.mem_univ _)

theorem cst_base (P : GPt A) :
    (dualMap (algebraMap K P.B)).comp (algebraMap K (DualNumber K)) = algebraMap K (DualNumber P.B) := by
  ext r <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.algebraMap_eq_inl']

theorem fst_comp_dualMap (P : GPt A) :
    (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B).comp (algebraMap K (DualNumber P.B)) = algebraMap K P.B := by
  ext r; simp [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.algebraMap_eq_inl']

theorem fst_comp_inl (P : GPt A) :
    (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B).comp (algebraMap P.B (DualNumber P.B)) = RingHom.id _ := by
  ext r; simp [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.algebraMap_eq_inl']

theorem cst_red (P : GPt A) :
    spMap (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B) ≫ P.cst.x = P.x := by
  show _ ≫ spMap _ ≫ P.x = P.x
  rw [← Category.assoc, ← Cris.spMap_comp, fst_comp_inl, Cris.spMap_id, Category.id_comp]

theorem cst_val (P : GPt A) {U : A.left.Opens} (hU : P.In U) (g : Γ(A.left, U)) :
    TrivSqZeroExt.fst (valR P.cst.x U g) = valR P.x U g := by
  show TrivSqZeroExt.fst (valR (spMap _ ≫ P.x) U g) = _
  rw [GlobalTheory.Points.valR_spMap_comp _ _ _ hU]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem cst_trx_val (P : GPt A) {v : epsR K ⟶ A} (hv : IsTangent v) {U : A.left.Opens} (hU : P.In U)
    (g : Γ(A.left, U)) : TrivSqZeroExt.fst (valR (P.cst.trx v) U g).snd = (valR (P.trx v) U g).snd := by
  have hin : ⊤ ≤ P.cst.trx v ⁻¹ᵁ U := hU.cst.tr hv
  have hm := (P.cst.isTransl_trx v).map (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B)
  have e1 : (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B).comp (algebraMap K P.cst.B) = algebraMap K P.B :=
    fst_comp_dualMap P
  rw [e1, cst_red] at hm
  rw [← hm.unique (P.isTransl_trx v), GlobalTheory.Points.valR_spMap_comp _ _ _ hin]
  simp [dualMap]

theorem eps_eq (P : GPt A) :
    letI : Algebra (DualNumber K) (DualNumber P.B) := (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap K P.B)).toAlgebra
    algebraMap (DualNumber K) (DualNumber P.B) DualNumber.eps = TrivSqZeroExt.inr 1 := by
  ext <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, RingHom.algebraMap_toAlgebra]

theorem cechKS_lifts : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (i : A.left ⟶ A'.left) (L : LB A.left) (n : ℕ) (u : Fin n → (epsR K ⟶ A)) (θ : Matrix (Fin n) (Fin n) K), (∀ a, IsTangent (u a)) → IsCechKS A A' i L u θ → ∃ (J : Type) (W : J → A.left.Opens) (c : J → L.ι) (y : J → ∀ P : GPt A, Sp (DualNumber P.B) ⟶ A'.left), ⨆ k, W k = ⊤ ∧ (∀ k, W k ≤ L.U (c k)) ∧ (∀ (k : J) (P : GPt A), P.In (W k) → IsLift i P (y k P)) ∧ (∀ (k : J) (P Q : GPt A) (φ : P.Hom Q), P.In (W k) → spMap (dualMap (φ.ρ : P.B →+* Q.B)) ≫ y k P = y k Q) ∧ ∀ (k k' : J) (P : GPt A) (U : A'.left.Opens) (f : Γ(A'.left, U)), P.In (W k) → P.In (W k') → P.In (i ⁻¹ᵁ U) → valR (y k P) U f - valR (y k' P) U f = (TrivSqZeroExt.inr (∑ a, (∑ b, algebraMap K P.B (θ a b) * dlog L (u b) (c k) (c k') P) * (valR (P.trx (u a)) (i ⁻¹ᵁ U) ((i.app U).hom f)).snd) : DualNumber P.B) := by
  intro K _ A _ A' _ i L n u θ hu h
  obtain ⟨J, W, c, lam, hcov, hWc, hlift, hdiff⟩ := h
  have hx : ∀ P : GPt A, letI : Algebra (DualNumber K) (DualNumber P.B) := (dualMap (algebraMap K P.B)).toAlgebra
      P.cst.x ≫ A.hom = spMap ((algebraMap (DualNumber K) (DualNumber P.B)).comp (algebraMap K (DualNumber K))) :=
    fun P ↦ (cechPt_over P.cst).trans (congrArg spMap (cst_base P).symm)
  refine ⟨J, W, c, fun k P ↦ @lam k (DualNumber P.B) _ (dualMap (algebraMap K P.B)).toAlgebra P.cst.x,
    hcov, hWc, ?_, ?_, ?_⟩
  · intro k P hP
    letI : Algebra (DualNumber K) (DualNumber P.B) := (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap K P.B)).toAlgebra
    obtain ⟨h1, h2, -⟩ := hlift k (DualNumber P.B) P.cst.x (hx P) hP.cst
    refine ⟨(congrArg (_ ≫ ·) (Category.comp_id _)).trans h1, ?_⟩
    let I := Ideal.span {algebraMap (DualNumber K) (DualNumber P.B) DualNumber.eps}
    have hI : ∀ a ∈ I, (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B) a = 0 := by
      intro a ha
      change a ∈ Ideal.span {algebraMap (DualNumber K) (DualNumber P.B) DualNumber.eps} at ha
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [eps_eq P]
      simp
    change spMap (Ideal.Quotient.mk I) ≫ lam k (DualNumber P.B) P.cst.x =
      spMap (Ideal.Quotient.mk I) ≫ P.cst.x ≫ i at h2
    have hq : (Ideal.Quotient.lift I _ hI).comp (Ideal.Quotient.mk I) =
        (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B) := RingHom.ext fun _ ↦ rfl
    calc spMap (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B) ≫ _
        = spMap (Ideal.Quotient.lift I _ hI) ≫ spMap (Ideal.Quotient.mk I) ≫ lam k (DualNumber P.B) P.cst.x := by
          rw [← Category.assoc, ← Cris.spMap_comp, hq]
          rfl
      _ = spMap (Ideal.Quotient.lift I _ hI) ≫ spMap (Ideal.Quotient.mk I) ≫ P.cst.x ≫ i := by rw [h2]
      _ = (spMap (TrivSqZeroExt.fstHom K P.B P.B : DualNumber P.B →+* P.B) ≫ P.cst.x) ≫ i := by
          rw [← Category.assoc, ← Category.assoc, ← Cris.spMap_comp, hq, Category.assoc]
      _ = P.x ≫ i := by rw [cst_red]
  · intro k P Q φ hP
    letI : Algebra (DualNumber K) (DualNumber P.B) := (dualMap (algebraMap K P.B)).toAlgebra
    letI : Algebra (DualNumber K) (DualNumber Q.B) := (dualMap (algebraMap K Q.B)).toAlgebra
    let ρ : DualNumber P.B →ₐ[DualNumber K] DualNumber Q.B :=
      { dualMap (φ.ρ : P.B →+* Q.B) with
        commutes' := fun r ↦ by
          ext <;> simp [dualMap, RingHom.algebraMap_toAlgebra] }
    have h3 := (hlift k (DualNumber P.B) P.cst.x (hx P) hP.cst).2.2 (DualNumber Q.B) ρ
    have hc : spMap (dualMap (φ.ρ : P.B →+* Q.B)) ≫ P.cst.x = Q.cst.x := by
      show spMap _ ≫ spMap _ ≫ P.x = spMap _ ≫ Q.x
      rw [← φ.pt, ← Category.assoc, ← Category.assoc, ← Cris.spMap_comp, ← Cris.spMap_comp, dualMap_comp_algebraMap]
    exact h3.trans (congrArg _ hc)
  · intro k k' P U f hk hk' hU
    letI : Algebra (DualNumber K) (DualNumber P.B) := (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap K P.B)).toAlgebra
    have ht : ∀ a, IsTransl ((algebraMap (DualNumber K) (DualNumber P.B)).comp (algebraMap K (DualNumber K)))
        P.cst.x (u a) (P.cst.trx (u a)) := fun a ↦ by
      rw [show (algebraMap (DualNumber K) (DualNumber P.B)).comp (algebraMap K (DualNumber K)) =
        algebraMap K P.cst.B from cst_base P]
      exact P.cst.isTransl_trx (u a)
    have hd := hdiff k k' (DualNumber P.B) P.cst.x U f (fun a ↦ P.cst.trx (u a)) (hx P) (hk.cst.inf hk'.cst)
      hU.cst ht
    refine hd.trans ?_
    have hg : P.In (L.U (c k) ⊓ L.U (c k')) := (hk.mono (hWc k)).inf (hk'.mono (hWc k'))
    have e1 : ∀ a, TrivSqZeroExt.fst (valR (P.cst.trx (u a)) _ (L.g (c k) (c k')).val).snd =
        (valR (P.trx (u a)) _ (L.g (c k) (c k')).val).snd := fun a ↦ cst_trx_val P (hu a) hg _
    have e2 : ∀ a, TrivSqZeroExt.fst (valR (P.cst.trx (u a)) (i ⁻¹ᵁ U) ((i.app U).hom f)).snd =
        (valR (P.trx (u a)) (i ⁻¹ᵁ U) ((i.app U).hom f)).snd := fun a ↦ cst_trx_val P (hu a) hU _
    have e3 : TrivSqZeroExt.fst (valR P.cst.x _ (L.g (c k) (c k'))⁻¹.val) = valR P.x _ (L.g (c k) (c k'))⁻¹.val :=
      cst_val P hg _
    have e4 : ∀ r : K, TrivSqZeroExt.fst
        (((algebraMap (DualNumber K) (DualNumber P.B)).comp (algebraMap K (DualNumber K))) r) = algebraMap K P.B r := by
      intro r
      rw [show (algebraMap (DualNumber K) (DualNumber P.B)).comp (algebraMap K (DualNumber K)) =
        algebraMap K P.cst.B from cst_base P]
      simp [TrivSqZeroExt.algebraMap_eq_inl']
    rw [eps_eq P]
    have hS : ∀ S : DualNumber P.B, TrivSqZeroExt.inr (1 : P.B) * S = TrivSqZeroExt.inr S.fst := fun S ↦ by
      ext <;> simp
    rw [hS]
    congr 1
    change (TrivSqZeroExt.fstHom K P.B P.B) _ = _

    simp only [map_sum, map_mul, TrivSqZeroExt.fstHom_apply]
    simp only [e1, e2, e3, e4, dlog, Finset.sum_mul]

end GlobalTheory.CechKS
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.diagonalHeisenbergInvariant_form_eq_smul_diagonalIntegral : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (κ : Type) [Fintype κ] (l : ((κ ⊕ κ → AF D.host.F) → ℂ) →ₗ[ℂ] ℂ),
      l ∈ (GlobalTheory.WeilM.adeleClass D.host.F).adm (κ ⊕ κ) →
      (∀ x y : κ → AF D.host.F, ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (κ ⊕ κ),
        l (GlobalTheory.WeilM.schr ψ (Sum.elim x x, Sum.elim y (-y)) Φ) = l Φ) →
      ∀ μ : @MeasureTheory.Measure (κ → AF D.host.F) (borel _),
        @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        ∃ c : ℂ, ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (κ ⊕ κ), l Φ = c * GlobalTheory.DiagSiegel.diagInt μ Φ := by
  first | exact @GlobalTheory.HostDiagUniq.eq_smul_diagInt | exact GlobalTheory.HostDiagUniq.eq_smul_diagInt | (intros; apply GlobalTheory.HostDiagUniq.eq_smul_diagInt <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PoincarePull

theorem exists_hom_triv_iff : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A →
    ∀ (D : Over (Sp R)) [GrpObj D] (Q : LB (A ⊗ D).left), GlobalTheory.AbDual.IsDual A D Q → GlobalTheory.AbDual.IsDual D A (GlobalTheory.AbDual.swap Q) →
    ∀ (L : LB A.left), L.IsLB → Out.RelAmple A L → ∀ P : LB (A ⊗ A).left, P.IsLB →
    HasGen (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left) → HasGen (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left) →
    ∃ x : A ⟶ D, IsMonHom x ∧ ∀ (T : Over (Sp R)) (y : T ⟶ A),
      (HasGen (P.pull (lift (fst A T) (snd A T ≫ y)).left) ↔ y ≫ x = 1) := by
  intro R _ A _ hA D _ Q q q' L hL aL P hP h₁ h₂
  obtain ⟨H, hH, aH⟩ := GlobalTheory.BirigidLift.exists_relAmple_prod hA hA hL aL hL aL
  obtain ⟨a₁, a₂⟩ := GlobalTheory.BirigidLift.additive_of_triv hA hA hH aH hP h₁ h₂
  obtain ⟨x, hx, e⟩ := GlobalTheory.BirigidLift.exists_hom q q'.additive hP a₁ a₂
  refine ⟨x, hx, fun T y ↦ ?_⟩
  have k := GlobalTheory.AbDual.triv_ev_iff hP (fst A T) (snd A T ≫ y)
  rw [GlobalTheory.BirigidLift.evc_of_cls q.isLB hP e, Category.assoc, ← GlobalTheory.AbDual.triv_ev_iff q.isLB] at k
  refine k.trans ⟨fun h ↦ q.eq_one (y ≫ x) h, fun h ↦ ?_⟩
  rw [h, GlobalTheory.AbDual.triv_ev_iff q.isLB, MonObj.comp_one]
  exact GlobalTheory.AbDual.evc_one_right q.isLB q.zero _

end GlobalTheory.PoincarePull
end
end

module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianPartConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2812
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2717
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2690
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2716
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2650
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2814
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2815
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.WtSub

theorem valR_resG' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) {U V : X.Opens} (e : V ≤ U)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(X, U)) : valR x V (resG X e f) = valR x U f := by
  have h' : ⊤ ≤ x ⁻¹ᵁ U := h.trans (x.preimage_mono e)
  simp only [valR, dif_pos h, dif_pos h']
  congr 1
  change (X.presheaf.map (homOfLE e).op ≫ x.appLE V ⊤ h).hom f = _
  rw [Scheme.Hom.map_appLE]

theorem valR_one' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    valR x U (1 : Γ(X, U)) = 1 := by
  simp only [valR, dif_pos h, map_one]

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} {Y : Ray oa}

theorem isWt_res {α : Q.X} {U V : Y.H.left.Opens} (e : V ≤ U) {f : Γ(Y.H.left, U)} (hf : IsWt Y α U f) :
    IsWt Y α V (resG Y.H.left e f) := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  have hU : ⊤ ≤ a ⁻¹ᵁ U := hV.trans (a.preimage_mono e)
  have hU' : ⊤ ≤ a' ⁻¹ᵁ U := hV'.trans (a'.preimage_mono e)
  rw [valR_resG' a' e hV', valR_resG' a e hV]
  exact hf S φ x x' c a a' ha ha' hU hU' hq hc

theorem isWt_inv {V : Y.H.left.Opens} (u : Γ(Y.H.left, V)ˣ) (hu : IsWt Y 0 V u.val) :
    IsWt Y 0 V (u⁻¹ : Γ(Y.H.left, V)ˣ).val := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  have hc0 : c 0 = 1 := WtAlg.c_zero x x' c hc
  have e1 := hu S φ x x' c a a' ha ha' hV hV' hq hc
  rw [hc0, Units.val_one, _root_.one_mul] at e1
  rw [hc0, Units.val_one, _root_.one_mul]
  have m : ∀ b : Sp S ⟶ Y.H.left, ⊤ ≤ b ⁻¹ᵁ V →
      valR b V (u⁻¹ : Γ(Y.H.left, V)ˣ).val * valR b V u.val = 1 := by
    intro b hb
    rw [← WtAlg.valR_mul'' b V hb, Units.inv_mul, valR_one' b V hb]
  have m' : ∀ b : Sp S ⟶ Y.H.left, ⊤ ≤ b ⁻¹ᵁ V →
      valR b V u.val * valR b V (u⁻¹ : Γ(Y.H.left, V)ˣ).val = 1 := by
    intro b hb
    rw [← WtAlg.valR_mul'' b V hb, Units.mul_inv, valR_one' b V hb]
  calc valR a' V (u⁻¹ : Γ(Y.H.left, V)ˣ).val
        = valR a' V (u⁻¹ : Γ(Y.H.left, V)ˣ).val *
            (valR a V u.val * valR a V (u⁻¹ : Γ(Y.H.left, V)ˣ).val) := by rw [m' a hV, _root_.mul_one]
    _ = (valR a' V (u⁻¹ : Γ(Y.H.left, V)ˣ).val * valR a' V u.val) *
            valR a V (u⁻¹ : Γ(Y.H.left, V)ˣ).val := by rw [e1, _root_.mul_assoc]
    _ = valR a V (u⁻¹ : Γ(Y.H.left, V)ˣ).val := by rw [m a' hV', _root_.one_mul]

theorem isRaynaudTorusWeightFunction_zero_pow {V : Y.H.left.Opens} {g : Γ(Y.H.left, V)} (hg : IsWt Y 0 V g) (n : ℕ) : IsWt Y 0 V (g ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero]
    have h1 := WtAlg.isWt_natCast (Y := Y) V 1
    rwa [Nat.cast_one] at h1
  | succ n ih =>
    rw [pow_succ']
    exact WtAlg.isRaynaudTorusWeightFunction_weightZero_mul hg ih

end GlobalTheory.Heat.WtSub

namespace GlobalTheory.Heat.WtSub

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O}

theorem isWt_basicOpen (Y : Ray oa) (V : Q.P.A.left.affineOpens) (d : Fld Y.H.left)
    (hd : IsField (Y.q.left ⁻¹ᵁ V.1) d)
    (hpres : ∀ (α : Q.X) f, IsWt Y α (Y.q.left ⁻¹ᵁ V.1) f → IsWt Y α _ (d _ f))
    (hdec : ∀ (W : Q.P.A.left.Opens), IsAffineOpen W → ∀ f : Γ(Y.H.left, Y.q.left ⁻¹ᵁ W),
      ∃! F : Q.X →₀ Γ(Y.H.left, Y.q.left ⁻¹ᵁ W), (∀ χ, IsWt Y χ _ (F χ)) ∧ f = F.sum (fun _ t => t))
    (hP : IsAffineOpen (Y.q.left ⁻¹ᵁ V.1))
    (g : Γ(Q.P.A.left, V.1)) (α : Q.X) (f : Γ(Y.H.left, Y.q.left ⁻¹ᵁ Q.P.A.left.basicOpen g))
    (hf : IsWt Y α _ f) : IsWt Y α _ (d _ f) := by
  have hle : Y.q.left ⁻¹ᵁ Q.P.A.left.basicOpen g ≤ Y.q.left ⁻¹ᵁ V.1 :=
    Y.q.left.preimage_mono (Q.P.A.left.basicOpen_le g)
  set G : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1) := (Y.q.left.app V.1).hom g with hGdef
  have hG0 : IsWt Y 0 _ G := AbConst.isWt_app Y V.1 g
  have heq : Y.q.left ⁻¹ᵁ Q.P.A.left.basicOpen g = Y.H.left.basicOpen G :=
    Scheme.preimage_basicOpen Y.q.left g
  let _ : Algebra Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1) Γ(Y.H.left, Y.q.left ⁻¹ᵁ Q.P.A.left.basicOpen g) :=
    (Y.H.left.presheaf.map (homOfLE hle).op).hom.toAlgebra
  have : IsLocalization.Away G Γ(Y.H.left, Y.q.left ⁻¹ᵁ Q.P.A.left.basicOpen g) :=
    hP.isLocalization_of_eq_basicOpen G (homOfLE hle) heq
  have halg : ∀ t, algebraMap Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1)
      Γ(Y.H.left, Y.q.left ⁻¹ᵁ Q.P.A.left.basicOpen g) t = resG Y.H.left hle t := fun _ => rfl
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj G f
  rw [← map_pow, halg, halg] at ha
  have hunit : IsUnit (resG Y.H.left hle (G ^ n)) := by
    rw [← halg, map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit G).pow n
  have hGn0 : IsWt Y 0 _ (resG Y.H.left hle (G ^ n)) := isWt_res hle (isRaynaudTorusWeightFunction_zero_pow hG0 n)
  obtain ⟨F, ⟨hFw, hFa⟩, -⟩ := hdec V.1 V.2 a
  obtain ⟨F0, -, huniq⟩ := hdec (Q.P.A.left.basicOpen g) (V.2.basicOpen g) (f * resG Y.H.left hle (G ^ n))
  have hA : Finsupp.mapRange (resG Y.H.left hle) (map_zero _) F = F0 := by
    refine huniq _ ⟨fun χ => ?_, ?_⟩
    · rw [Finsupp.mapRange_apply]
      exact isWt_res hle (hFw χ)
    · rw [Finsupp.sum_mapRange_index (fun _ => rfl), ha, hFa, map_finsuppSum]
  have hB : Finsupp.single α (f * resG Y.H.left hle (G ^ n)) = F0 := by
    refine huniq _ ⟨fun χ => ?_, ?_⟩
    · by_cases hχ : α = χ
      · subst hχ
        rw [Finsupp.single_eq_same, _root_.mul_comm]
        exact WtAlg.isRaynaudTorusWeightFunction_weightZero_mul hGn0 hf
      · rw [Finsupp.single_eq_of_ne' hχ]
        exact WtAlg.isWt_zero _ _
    · rw [Finsupp.sum_single_index rfl]
  have hα : resG Y.H.left hle (F α) = f * resG Y.H.left hle (G ^ n) := by
    have h1 := DFunLike.congr_fun (hA.trans hB.symm) α
    rwa [Finsupp.mapRange_apply, Finsupp.single_eq_same] at h1
  obtain ⟨-, hmul, hres⟩ := hd
  have hdfG : IsWt Y α _ (d _ (f * resG Y.H.left hle (G ^ n))) := by
    rw [← hα, hres _ _ hle le_rfl]
    exact isWt_res hle (hpres α (F α) (hFw α))
  have hdG : IsWt Y 0 _ (d _ (resG Y.H.left hle (G ^ n))) := by
    rw [hres _ _ hle le_rfl]
    exact isWt_res hle (hpres 0 (G ^ n) (isRaynaudTorusWeightFunction_zero_pow hG0 n))
  have hGdf : IsWt Y α _ (resG Y.H.left hle (G ^ n) * d _ f) := by
    have e2 : resG Y.H.left hle (G ^ n) * d _ f =
        d _ (f * resG Y.H.left hle (G ^ n)) - f * d _ (resG Y.H.left hle (G ^ n)) := by
      rw [hmul _ hle]
      ring
    rw [e2, _root_.mul_comm f (d _ (resG Y.H.left hle (G ^ n)))]
    exact WtAlg.isWt_sub hdfG (WtAlg.isRaynaudTorusWeightFunction_weightZero_mul hdG hf)
  obtain ⟨u, hu⟩ := hunit
  have hu0 : IsWt Y 0 _ (u⁻¹ : Γ(Y.H.left, Y.q.left ⁻¹ᵁ Q.P.A.left.basicOpen g)ˣ).val := by
    refine isWt_inv u ?_
    rw [hu]
    exact hGn0
  have h2 := WtAlg.isRaynaudTorusWeightFunction_weightZero_mul hu0 hGdf
  rwa [← hu, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul] at h2

end GlobalTheory.Heat.WtSub

namespace GlobalTheory.Heat.WtSub

theorem isWt_field_of_le : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.affineOpens) (d : Fld Y.H.left), IsField (Y.q.left ⁻¹ᵁ V.1) d → (∀ (α : Q.X) f, IsWt Y α (Y.q.left ⁻¹ᵁ V.1) f → IsWt Y α _ (d _ f)) → ∀ (α : Q.X) (V' : Q.P.A.left.Opens), V' ≤ V.1 → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d _ f) := by
  intro R _ _ Q O _ _ _ oa Y V d hd hpres α V' hV' f hf
  apply GlobalTheory.T.isRaynaudTorusWeightFunction_of_basicOpens R Q O oa Y V V' hV' α (d _ f)
  intro g hg
  have hle : Y.q.left ⁻¹ᵁ V' ≤ Y.q.left ⁻¹ᵁ V.1 := Y.q.left.preimage_mono hV'
  obtain ⟨hadd, hmul, hres⟩ := hd
  rw [← hres _ _ (Y.q.left.preimage_mono hg) hle f]
  exact isWt_basicOpen Y V d ⟨hadd, hmul, hres⟩ hpres (fun W hW => GlobalTheory.T.existsUnique_weightDecomposition_raynaud_affine R Q O oa Y W hW)
    (GlobalTheory.T.isAffineOpen_preimage_projection_abelianPart R Q O oa Y V) g α _ (isWt_res _ hf)

end GlobalTheory.Heat.WtSub
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WtLift

variable {X A : Type} [AddCommGroup X] [CommRing A] (P : X → A → Prop)
  (hadd : ∀ χ a b, P χ a → P χ b → P χ (a + b)) (hzero : ∀ χ, P χ 0)
  (hmul : ∀ χ ψ a b, P χ a → P ψ b → P (χ + ψ) (a * b))
  (hdec : ∀ f : A, ∃! F : X →₀ A, (∀ χ, P χ (F χ)) ∧ f = F.sum (fun _ t => t))


include hdec in
def dec (f : A) : X →₀ A := (hdec f).exists.choose

include hdec in
theorem dec_spec (f : A) : (∀ χ, P χ (dec P hdec f χ)) ∧ f = (dec P hdec f).sum (fun _ t => t) :=
  (hdec f).exists.choose_spec

include hdec in
theorem dec_eq {f : A} {F : X →₀ A} (hF : ∀ χ, P χ (F χ)) (hs : f = F.sum (fun _ t => t)) : dec P hdec f = F :=
  (hdec f).unique (dec_spec P hdec f) ⟨hF, hs⟩

include hadd hdec in
theorem dec_add (a b : A) : dec P hdec (a + b) = dec P hdec a + dec P hdec b := by
  refine dec_eq P hdec (fun χ => ?_) ?_
  · rw [Finsupp.add_apply]; exact hadd _ _ _ ((dec_spec P hdec a).1 χ) ((dec_spec P hdec b).1 χ)
  · rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), ← (dec_spec P hdec a).2, ← (dec_spec P hdec b).2]

include hzero hdec in
theorem dec_single {α : X} {f : A} (hf : P α f) : dec P hdec f = Finsupp.single α f := by
  classical
  refine dec_eq P hdec (fun χ => ?_) ?_
  · rw [Finsupp.single_apply]; split_ifs with h
    · exact h ▸ hf
    · exact hzero χ
  · rw [Finsupp.sum_single_index rfl]

include hzero hdec in
theorem dec_zero : dec P hdec (0 : A) = 0 := by
  rw [dec_single P hzero hdec (hzero 0), Finsupp.single_zero]

include hzero hmul hdec in
theorem dec_mul {χ : X} {f : A} (hf : P χ f) (h : A) (ψ : X) :
    dec P hdec (f * h) (χ + ψ) = f * dec P hdec h ψ := by
  set G : X →₀ A := Finsupp.mapDomain (fun ψ => χ + ψ) ((dec P hdec h).mapRange (f * ·) (mul_zero f)) with hG
  have hinj : Function.Injective (fun ψ : X => χ + ψ) := add_right_injective χ
  have hGv : ∀ ψ, G (χ + ψ) = f * dec P hdec h ψ := fun ψ => by
    rw [hG, Finsupp.mapDomain_apply_of_injective hinj, Finsupp.mapRange_apply]
  have key : dec P hdec (f * h) = G := by
    refine dec_eq P hdec (fun ω => ?_) ?_
    · have e : ω = χ + (ω - χ) := by abel
      rw [e, hGv]; exact hmul _ _ _ _ hf ((dec_spec P hdec h).1 _)
    · rw [hG, Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl),
        Finsupp.sum_mapRange_index (fun _ => rfl), ← Finsupp.mul_sum, ← (dec_spec P hdec h).2]
  rw [key, hGv]

variable (δ₀ : A → A)

def proj (f : A) : A := (dec P hdec f).sum (fun χ t => dec P hdec (δ₀ t) χ)

include hadd hzero hdec in
theorem proj_add (h0 : ∀ a b, δ₀ (a + b) = δ₀ a + δ₀ b) (a b : A) :
    proj P hdec δ₀ (a + b) = proj P hdec δ₀ a + proj P hdec δ₀ b := by
  have hz : δ₀ 0 = 0 := by
    have := h0 0 0; simp only [add_zero] at this; exact left_eq_add.mp this
  unfold proj
  rw [dec_add P hadd hdec, Finsupp.sum_add_index']
  · intro χ; rw [hz, dec_zero P hzero hdec, Finsupp.zero_apply]
  · intro χ s t; rw [h0, dec_add P hadd hdec, Finsupp.add_apply]

include hzero hdec in
theorem proj_of_wt (hz : δ₀ 0 = 0) {α : X} {f : A} (hf : P α f) : proj P hdec δ₀ f = dec P hdec (δ₀ f) α := by
  unfold proj; rw [dec_single P hzero hdec hf, Finsupp.sum_single_index]
  rw [hz, dec_zero P hzero hdec]; rfl


include hzero hdec in
theorem induction_wt (Qp : A → Prop) (q0 : Qp 0) (qadd : ∀ a b, Qp a → Qp b → Qp (a + b))
    (qw : ∀ χ a, P χ a → Qp a) (f : A) : Qp f := by
  rw [(dec_spec P hdec f).2, Finsupp.sum]
  exact Finset.sum_induction _ Qp qadd q0 (fun χ _ => qw χ _ ((dec_spec P hdec f).1 χ))

include hadd hzero hmul hdec in
theorem proj_mul (h0 : ∀ a b, δ₀ (a + b) = δ₀ a + δ₀ b) (h1 : ∀ a b, δ₀ (a * b) = a * δ₀ b + b * δ₀ a) (a b : A) :
    proj P hdec δ₀ (a * b) = a * proj P hdec δ₀ b + b * proj P hdec δ₀ a := by
  have hz : δ₀ 0 = 0 := by
    have := h0 0 0; simp only [add_zero] at this; exact left_eq_add.mp this
  have pz : proj P hdec δ₀ 0 = 0 := by
    unfold proj; rw [dec_zero P hzero hdec, Finsupp.sum_zero_index]
  have hom : ∀ χ ψ x y, P χ x → P ψ y →
      proj P hdec δ₀ (x * y) = x * proj P hdec δ₀ y + y * proj P hdec δ₀ x := by
    intro χ ψ x y hx hy
    rw [proj_of_wt P hzero hdec δ₀ hz (hmul _ _ _ _ hx hy), proj_of_wt P hzero hdec δ₀ hz hy,
      proj_of_wt P hzero hdec δ₀ hz hx, h1, dec_add P hadd hdec, Finsupp.add_apply, dec_mul P hzero hmul hdec hx,
      add_comm χ ψ, dec_mul P hzero hmul hdec hy]
  have padd := proj_add P hadd hzero hdec δ₀ h0

  have step : ∀ ψ y, P ψ y → ∀ x, proj P hdec δ₀ (x * y) = x * proj P hdec δ₀ y + y * proj P hdec δ₀ x := by
    intro ψ y hy
    refine induction_wt P hzero hdec _ ?_ ?_ (fun χ x hx => hom χ ψ x y hx hy)
    · rw [zero_mul, pz, zero_mul, mul_zero, add_zero]
    · intro x x' ex ex'; rw [add_mul, padd, padd, ex, ex']; ring
  revert b
  intro b
  refine induction_wt P hzero hdec (fun y => proj P hdec δ₀ (a * y) = a * proj P hdec δ₀ y + y * proj P hdec δ₀ a)
    ?_ ?_ (fun ψ y hy => step ψ y hy a) b
  · simp only [mul_zero, pz, zero_mul, add_zero]
  · intro y y' ey ey'; rw [mul_add, padd, ey, ey', padd]; ring

include hzero hdec in
theorem proj_wt (hz : δ₀ 0 = 0) {α : X} {f : A} (hf : P α f) : P α (proj P hdec δ₀ f) := by
  rw [proj_of_wt P hzero hdec δ₀ hz hf]; exact (dec_spec P hdec _).1 α

end GlobalTheory.WtLift

namespace GlobalTheory.WtLift

theorem exists_isWt_lift : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.affineOpens) (D : Derivation ℤ R R) (δ₀ : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1) → Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1)), (∀ a b, δ₀ (a + b) = δ₀ a + δ₀ b) → (∀ a b, δ₀ (a * b) = a * δ₀ b + b * δ₀ a) → (∀ r, δ₀ (constFn Y.H.hom _ r) = constFn Y.H.hom _ (D r)) → ∃ δ : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1) → Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1), (∀ a b, δ (a + b) = δ a + δ b) ∧ (∀ a b, δ (a * b) = a * δ b + b * δ a) ∧ (∀ r, δ (constFn Y.H.hom _ r) = constFn Y.H.hom _ (D r)) ∧ ∀ (α : Q.X) f, IsWt Y α _ f → IsWt Y α _ (δ f) := by
  intro R _ _ Q O _ _ _ oa Y V D δ₀ h0 h1 hc
  have hadd : ∀ (χ : Q.X) (a b : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1)), IsWt Y χ _ a → IsWt Y χ _ b → IsWt Y χ _ (a + b) :=
    fun χ a b ha hb => WtAlg.isWt_add ha hb
  have hzero : ∀ χ : Q.X, IsWt Y χ (Y.q.left ⁻¹ᵁ V.1) 0 := fun χ => WtAlg.isWt_zero (Y := Y) χ _
  have hmul : ∀ (χ ψ : Q.X) (a b : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1)), IsWt Y χ _ a → IsWt Y ψ _ b →
      IsWt Y (χ + ψ) _ (a * b) :=
    fun χ ψ a b ha hb => GlobalTheory.T.isRaynaudTorusWeightFunction_mul R Q O oa Y _ χ ψ a b ha hb
  have hdec := GlobalTheory.T.existsUnique_weightDecomposition_raynaud_affine R Q O oa Y V.1 V.2
  have hz : δ₀ 0 = 0 := by
    have := h0 0 0; simp only [add_zero] at this; exact left_eq_add.mp this
  refine ⟨proj (fun χ f => IsWt Y χ _ f) hdec δ₀, proj_add _ hadd hzero hdec δ₀ h0,
    proj_mul _ hadd hzero hmul hdec δ₀ h0 h1, fun r => ?_, fun α f hf => proj_wt _ hzero hdec δ₀ hz hf⟩
  rw [proj_of_wt _ hzero hdec δ₀ hz (WtAlg.isWt_constFn (Y := Y) _ r), hc,
    dec_single _ hzero hdec (WtAlg.isWt_constFn (Y := Y) _ (D r)), Finsupp.single_eq_same]

end GlobalTheory.WtLift
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isInvariantField_dualNumber_of_isInvariant_tangentVector : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (v : TanM (𝟙 (Sp K)) A) (u : epsR K ⟶ A) (dd : Fld A.left), u.left = (tv v).left → IsTangent u → IsInv A v dd → GlobalTheory.KS.IsInvDer u dd := by
  first | exact @GlobalTheory.InvDerBridge.isInvDer_of_isInv | exact GlobalTheory.InvDerBridge.isInvDer_of_isInv | (intros; apply GlobalTheory.InvDerBridge.isInvDer_of_isInv <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat

theorem sval_eq_of_localIdentity : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h h' : Heat Y.H Y.q.left Q.P.L dd ⇑D), IsBasic Y h → IsBasic Y h' → ∀ c : ℕ → Q.X → R, (∀ (i : h.J) (i' : h'.J) (k : ℕ) (α : Q.X) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ h.W i ⊓ h'.W i' → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V) f → op Y.H dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k (Y.q.left ⁻¹ᵁ V) (pbT Y.q.left (Q.P.L.g (h.j i) (h'.j i')).val (Y.q.left ⁻¹ᵁ V) ^ k * f) = pbT Y.q.left (Q.P.L.g (h.j i) (h'.j i')).val (Y.q.left ⁻¹ᵁ V) ^ k * (op Y.H dd h'.Θ h'.u (h'.d i') (h'.p i') (h'.p' i') k (Y.q.left ⁻¹ᵁ V) f + constFn Y.H.hom _ (c k α) * f)) → ∀ (k : ℕ) (α : Q.X) (σ σ' σ'' : Q.SecB k α), TActs Y h k α σ σ' → TActs Y h' k α σ σ'' → ∀ (T : Over (Sp R)) (x : T ⟶ Q.P.A) z J, Good Q.P.L z J → sval σ' x.left z J = sval σ'' x.left z J + gs (𝟙 _) z ⊤ (scal T.hom (c k α)) * sval σ x.left z J := by
  intro R _ _ Q O _ _ _ oa Y n v dd hv D h h' hb hb' c hc k α σ σ' σ'' ⟨τ₁, τ₁', t1, t1', a1⟩ ⟨τ₂, τ₂'', t2, t2'', a2⟩ T x z J hJ
  refine GlobalTheory.T.raynaudProjection_sectionValues_identity R Q O oa Y k α σ σ' σ'' (c k α) ?_ T x z J hJ
  intro y J' hJ'
  have e : ∀ (s : Q.SecB k α) (τ : SecM Y.q.left Q.P.L k), IsTerm Y k α s τ →
      sval τ (𝟙 Y.H.left) y J' = sval s Y.q.left y J' * (val ((Y.Φ Y.H (𝟙 _)).s α) (𝟙 _) y J').val := by
    intro s τ hτ
    have := hτ Y.H (𝟙 _) y J' hJ'
    simpa only [Over.id_left, Category.id_comp] using this
  have key := GlobalTheory.T.heatOperators_related_fourierTerm_images R Q O oa Y n dd D (fun a => (hv a).1) h h' hb hb' k α (c k α) (fun i i' => hc i i' k α) τ₁ τ₁' τ₂ τ₂''
    (fun y J hJ => by
      have a := t1 Y.H (𝟙 _) y J hJ
      have b := t2 Y.H (𝟙 _) y J hJ
      simp only [Over.id_left, Category.id_comp] at a b
      rw [a, b])
    (GlobalTheory.T.raynaudFourierTerm_localFunction_isWeight R Q O oa Y k α σ τ₂ t2) a1 a2 y J' hJ'
  rw [e σ' τ₁' t1', e σ'' τ₂'' t2'', e σ τ₂ t2] at key
  set u := val ((Y.Φ Y.H (𝟙 _)).s α) (𝟙 _) y J'
  have : (sval σ' Y.q.left y J' - (sval σ'' Y.q.left y J' + gs (𝟙 _) y ⊤ (scal Y.H.hom (c k α)) * sval σ Y.q.left y J')) * u.val = 0 := by
    rw [sub_mul, key]; ring
  have h0 := congrArg (· * (u⁻¹ : (Y.H.left.presheaf.stalk y)ˣ).val) this
  simp only [Units.mul_inv_cancel_right, zero_mul] at h0
  exact sub_eq_zero.1 h0

end GlobalTheory.Heat
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.heatRingOperator_conj_by_pow_nonzero : ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] (n : ℕ) (d : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (δ : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (Θ : Matrix (Fin n) (Fin n) (FractionRing Ω)), (2 : FractionRing Ω) ≠ 0 → ∀ (u : Fin n → FractionRing Ω) (p p' c : FractionRing Ω), c ≠ 0 → ∃ (d' : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (u'' : Fin n → FractionRing Ω) (q q' : FractionRing Ω), (∀ y, (∀ a, δ a y = 0) → d' y = d y) ∧ ∀ (k : ℕ) (f : FractionRing Ω), ringOp ⇑d (fun a => ⇑(δ a)) Θ u p p' k (c ^ k * f) = c ^ k * ringOp ⇑d' (fun a => ⇑(δ a)) Θ u'' q q' k f := by
  first | exact @GlobalTheory.Heat.ringOp_conj_pow_gen | exact GlobalTheory.Heat.ringOp_conj_pow_gen | (intros; apply GlobalTheory.Heat.ringOp_conj_pow_gen <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.invariant_vector_fields_basis_tangent : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (g : ℕ) (L : LB B.left), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → L.IsLB → RelAmple B L → KTriv B L → (∀ i, IsAffineOpen (L.U i)) → Finite L.ι → ∀ (v : Fin g → TanM (𝟙 (Sp A)) B) (dd : Fin g → Fld B.left), (∀ a, IsInv B (v a) (dd a)) → (∀ w : TanM (𝟙 (Sp A)) B, ∃! cf : Fin g → A, w = ∑ a, cf a • v a) → ∀ c : C1 L.U, IsCoc L.U c → ∃! cc : Fin g → A, IsCob L.U (fun i j => c i j - ∑ a, constFn B.hom _ (cc a) * dlg B (𝟙 _) L (dd a) i j (L.U i ⊓ L.U j)) := by
  first | exact @GlobalTheory.DlogBasis.main | exact GlobalTheory.DlogBasis.main | (intros; apply GlobalTheory.DlogBasis.main <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.torusInvariant_heatOperator_acts_on_fourierTerms : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D), IsBasic Y h → ∀ (k : ℕ) (α : Dd.toPre.X) (σ : Dd.toPre.SecB k α), ∃ σ', TActs Y h k α σ σ' := by
  first | exact @GlobalTheory.Heat.heat_acts_on_terms | exact GlobalTheory.Heat.heat_acts_on_terms | (intros; apply GlobalTheory.Heat.heat_acts_on_terms <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_integral_sections_thetaShift_triple : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] (Dd : DegData R (maximalIdeal R)) (k : ℕ), 1 ≤ k → ∀ (mu mu' α : Dd.toPre.X), ∃ (σ : Dd.toPre.SecB k α) (σ₁ : Dd.toPre.SecB k (α + k • mu)) (σ₂ : Dd.toPre.SecB k (α + k • mu + k • mu')) (e : Dd.toPre.SecB k (α + k • mu + k • mu') = Dd.toPre.SecB k (α + k • (mu + mu'))), ShiftEq Dd.toPre k mu α σ σ₁ 0 σ₁ ∧ ShiftEq Dd.toPre k mu' (α + k • mu) σ₁ σ₂ 0 σ₂ ∧ ShiftEq Dd.toPre k (mu + mu') α σ (cast e σ₂) 0 (cast e σ₂) ∧ ∃ (z : (DegPre.BF Dd.toPre (FractionRing R)).left) (J : ((DegPre.BF Dd.toPre (FractionRing R)).left ⟶ Dd.toPre.P.A.left) → Dd.toPre.P.L.ι), Good Dd.toPre.P.L z J ∧ IsUnit (sval σ (DegPre.trF Dd.toPre (FractionRing R) (mu + mu') ≫ DegPre.prB Dd.toPre (FractionRing R)).left z J) := by
  first | exact @GlobalTheory.IntegralFamTriple.exists_triple | exact GlobalTheory.IntegralFamTriple.exists_triple | (intros; apply GlobalTheory.IntegralFamTriple.exists_triple <;> assumption)
end

section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.linForm_bilinForms_eq_sum_minimiser_values : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (N : ℕ) [NeZero N], 3 ≤ N → (∃ ε : Fin 8 → ℤ, Nat.Coprime N (2 * (∑ u, ∑ v, W u v * ε u * ε v).natAbs)) → ∀ r : ℕ, ∀ μ : ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ)), (∀ c u i, ((μ c u i : ℤ) : ZMod N) = c u i) → ∀ ℓ : LinearMap.BilinForm ℤ (Fin r → ℤ) →ₗ[ℤ] ℤ, ∃ (D : ℕ) (ν : (Fin 8 → Fin r → ZMod N) → ℤ), 0 < D ∧ ∀ b : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ x y, b x y = b y x) → (D : ℤ) * ℓ b = ∑ c, ν c * qW W b (μ c) := by
  first | exact @GlobalTheory.Poinc.linForm_eq_sum_qW_lifts | exact GlobalTheory.Poinc.linForm_eq_sum_qW_lifts | (intros; apply GlobalTheory.Poinc.linForm_eq_sum_qW_lifts <;> assumption)
end

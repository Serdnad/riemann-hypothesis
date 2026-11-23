module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle427
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle429
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle292
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle426
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle156

@[expose] public section

section

open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
open scoped Simplicial
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.EZ.Cone

theorem homExt {m a : ℕ} {f g : ⦋m⦌ ⟶ ⦋a⦌}
    (h : ∀ j : Fin (m + 1), (f.toOrderHom j : ℕ) = g.toOrderHom j) : f = g :=
  SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun j => Fin.ext (h j)))

def cv {n a : ℕ} (f : ⦋n⦌ ⟶ ⦋a⦌) : ⦋n + 1⦌ ⟶ ⦋a⦌ :=
  SimplexCategory.mkHom ⟨fun j => if h : (j : ℕ) = 0 then 0 else
      f.toOrderHom ⟨(j : ℕ) - 1, by have := j.2; change _ < n + 1; omega⟩, by
    intro i j hij
    have hij' : (i : ℕ) ≤ j := hij
    dsimp only
    split_ifs with hi hj hj
    · exact le_refl _
    · exact Fin.zero_le _
    · omega
    · exact f.toOrderHom.monotone (show ((⟨(i : ℕ) - 1, _⟩ : Fin _) ≤ ⟨(j : ℕ) - 1, _⟩) from by
        rw [Fin.mk_le_mk]; omega)⟩

theorem cv_apply {n a : ℕ} (f : ⦋n⦌ ⟶ ⦋a⦌) (j : Fin (n + 2)) :
    ((cv f).toOrderHom j : ℕ) = if h : (j : ℕ) = 0 then 0 else
      (f.toOrderHom ⟨(j : ℕ) - 1, by have := j.2; change _ < n + 1; omega⟩ : ℕ) := by
  simp only [cv, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk, OrderHom.coe_mk]
  split_ifs <;> rfl

theorem fc_apply (n m i : ℕ) (j : Fin (m + 1)) :
    ((fc n m i).toOrderHom j : ℕ) = min n (faceFun i j) := rfl

theorem idc_apply (n m : ℕ) (j : Fin (m + 1)) :
    ((idc n m).toOrderHom j : ℕ) = min n j := rfl

theorem face_cone_identity_zero {m a : ℕ} (f : ⦋m⦌ ⟶ ⦋a⦌) : fc (m + 1) m 0 ≫ cv f = f := by
  apply homExt; intro j
  rw [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply, cv_apply]
  have h1 : ((fc (m + 1) m 0).toOrderHom j : ℕ) = j + 1 := by
    rw [fc_apply]; unfold faceFun; have := j.2; split_ifs <;> omega
  rw [dite_eq_right (by omega)]
  congr 2; apply Fin.ext; simp only [h1]; omega

theorem fcs_cv {m a : ℕ} (f : ⦋m + 1⦌ ⟶ ⦋a⦌) (k : ℕ) :
    fc (m + 2) (m + 1) (k + 1) ≫ cv f = cv (fc (m + 1) m k ≫ f) := by
  apply homExt; intro j
  rw [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply, cv_apply, cv_apply]
  have hj := j.2
  by_cases h0 : (j : ℕ) = 0
  · rw [dite_eq_left h0]
    have : ((fc (m + 2) (m + 1) (k + 1)).toOrderHom j : ℕ) = 0 := by
      rw [fc_apply]; unfold faceFun; split_ifs <;> omega
    rw [dite_eq_left this]
  · have h1 : ((fc (m + 2) (m + 1) (k + 1)).toOrderHom j : ℕ) ≠ 0 := by
      rw [fc_apply]; unfold faceFun; split_ifs <;> omega
    rw [dite_eq_right h1, dite_eq_right h0, SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply]
    congr 2; apply Fin.ext
    simp only [fc_apply]; unfold faceFun; split_ifs <;> omega

theorem face_cone_identity_one {a : ℕ} (f : ⦋0⦌ ⟶ ⦋a⦌) : fc 1 0 1 ≫ cv f = idc a 0 := by
  apply homExt; intro j
  rw [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply, cv_apply, idc_apply]
  have hj := j.2
  have : ((fc 1 0 1).toOrderHom j : ℕ) = 0 := by
    rw [fc_apply]; unfold faceFun; split_ifs <;> omega
  rw [dite_eq_left this]; omega

theorem bop_comp {n m p q r s : ℕ} (α : ⦋p⦌ ⟶ ⦋n⦌) (β : ⦋q⦌ ⟶ ⦋m⦌) (α' : ⦋r⦌ ⟶ ⦋p⦌)
    (β' : ⦋s⦌ ⟶ ⦋q⦌) : bop α β ≫ bop α' β' = bop (α' ≫ α) (β' ≫ β) := by
  have h := Free.single_comp_single ℤ (SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ)
    (show (op ⦋n⦌, op ⦋m⦌) ⟶ (op ⦋p⦌, op ⦋q⦌) from (α.op, β.op))
    (show (op ⦋p⦌, op ⦋q⦌) ⟶ (op ⦋r⦌, op ⦋s⦌) from (α'.op, β'.op)) 1 1
  rw [mul_one] at h
  exact h

def coneHom {a b n : ℕ} (x : (op ⦋a⦌, op ⦋b⦌) ⟶ (op ⦋n⦌, op ⦋n⦌)) :
    (op ⦋a⦌, op ⦋b⦌) ⟶ (op ⦋n + 1⦌, op ⦋n + 1⦌) :=
  ((cv x.1.unop).op, (cv x.2.unop).op)

def cone (a b n : ℕ) : (bo a b ⟶ bo n n) →+ (bo a b ⟶ bo (n + 1) (n + 1)) :=
  Finsupp.mapDomain.addMonoidHom coneHom

def eps (a b : ℕ) : (bo a b ⟶ bo 0 0) →+ ℤ := Finsupp.liftAddHom (fun _ => AddMonoidHom.id ℤ)

theorem cone_bop {a b n : ℕ} (α : ⦋n⦌ ⟶ ⦋a⦌) (β : ⦋n⦌ ⟶ ⦋b⦌) :
    cone a b n (bop α β) = bop (cv α) (cv β) := by
  exact Finsupp.mapDomain_single

theorem eps_bop {a b : ℕ} (α : ⦋0⦌ ⟶ ⦋a⦌) (β : ⦋0⦌ ⟶ ⦋b⦌) : eps a b (bop α β) = 1 := by
  exact Finsupp.liftAddHom_apply_single _ _ _

theorem single_eq {a b n p : ℕ} (x : (op ⦋a⦌, op ⦋b⦌) ⟶ (op ⦋n⦌, op ⦋p⦌)) (c : ℤ) :
    (Finsupp.single x c : bo a b ⟶ bo n p) = c • bop x.1.unop x.2.unop := by
  have h := map_zsmul (Finsupp.singleAddHom (M := ℤ) x) c (1 : ℤ)
  rw [smul_eq_mul, mul_one] at h
  exact h

theorem ind {a b n p : ℕ} (P : (bo a b ⟶ bo n p) → Prop) (h0 : P 0) (hadd : ∀ f g, P f → P g → P (f + g))
    (hs : ∀ (α : ⦋n⦌ ⟶ ⦋a⦌) (β : ⦋p⦌ ⟶ ⦋b⦌) (c : ℤ), P (c • bop α β)) (r : bo a b ⟶ bo n p) : P r :=
  Finsupp.induction_linear r h0 hadd (fun x c => by have h := hs x.1.unop x.2.unop c; rw [← single_eq] at h; exact h)

theorem key {a b n : ℕ} (α : ⦋n + 1⦌ ⟶ ⦋a⦌) (β : ⦋n + 1⦌ ⟶ ⦋b⦌) :
    cone a b (n + 1) (bop α β) ≫ dD (n + 2) (n + 1) = bop α β - cone a b n (bop α β ≫ dD (n + 1) n) := by
  rw [cone_bop]
  unfold dD
  rw [ite_eq_left rfl, ite_eq_left rfl]

  simp only [Preadditive.comp_sum, Preadditive.comp_zsmul, bop_comp, map_sum, map_zsmul, cone_bop]
  rw [Finset.sum_range_succ' _ (n + 2)]
  have h0 : fc (n + 2) (n + 1) 0 ≫ cv α = α := face_cone_identity_zero α
  have h0' : fc (n + 2) (n + 1) 0 ≫ cv β = β := face_cone_identity_zero β
  simp only [h0, h0', fcs_cv, pow_succ, pow_zero, one_smul, mul_neg, mul_one, neg_smul, Finset.sum_neg_distrib]
  abel

theorem key0 {a b : ℕ} (α : ⦋0⦌ ⟶ ⦋a⦌) (β : ⦋0⦌ ⟶ ⦋b⦌) :
    cone a b 0 (bop α β) ≫ dD 1 0 = bop α β - bop (idc a 0) (idc b 0) := by
  rw [cone_bop]
  unfold dD
  rw [ite_eq_left rfl]
  simp only [Preadditive.comp_sum, Preadditive.comp_zsmul, bop_comp]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, face_cone_identity_one]
  have h0 : fc 1 0 0 ≫ cv α = α := face_cone_identity_zero α
  have h0' : fc 1 0 0 ≫ cv β = β := face_cone_identity_zero β
  simp only [h0, h0', pow_zero, pow_one, one_smul, neg_smul, zero_add]
  abel

theorem coneContraction : ∃ (cone : ∀ a b n : ℕ, (bo a b ⟶ bo n n) →+ (bo a b ⟶ bo (n + 1) (n + 1)))
    (ε : ∀ a b : ℕ, (bo a b ⟶ bo 0 0) →+ ℤ),
    (∀ (a b : ℕ) (α : SimplexCategory.mk 0 ⟶ SimplexCategory.mk a) (β : SimplexCategory.mk 0 ⟶ SimplexCategory.mk b),
      ε a b (bop α β) = 1) ∧
    (∀ (a b : ℕ) (r : bo a b ⟶ bo 0 0), cone a b 0 r ≫ dD 1 0 = r - ε a b r • bop (idc a 0) (idc b 0)) ∧
    ∀ (a b n : ℕ) (r : bo a b ⟶ bo (n + 1) (n + 1)),
      cone a b (n + 1) r ≫ dD (n + 2) (n + 1) = r - cone a b n (r ≫ dD (n + 1) n) := by
  refine ⟨cone, eps, fun a b α β => eps_bop α β, ?_, ?_⟩
  · intro a b r
    refine ind (P := fun r => cone a b 0 r ≫ dD 1 0 = r - eps a b r • bop (idc a 0) (idc b 0)) ?_ ?_ ?_ r
    · rw [map_zero, map_zero, Limits.zero_comp, zero_smul, sub_zero]
    · intro f g hf hg
      simp only [map_add (f := _), Preadditive.add_comp, add_smul, hf, hg]
      abel
    · intro α β c
      rw [map_zsmul, Preadditive.zsmul_comp, key0, map_zsmul, eps_bop, smul_sub, smul_eq_mul, mul_one]
  · intro a b n r
    refine ind (P := fun r => cone a b (n + 1) r ≫ dD (n + 2) (n + 1) = r - cone a b n (r ≫ dD (n + 1) n))
      ?_ ?_ ?_ r
    · rw [map_zero, Limits.zero_comp, Limits.zero_comp, map_zero, sub_zero]
    · intro f g hf hg
      simp only [map_add (f := _), Preadditive.add_comp, hf, hg]
      abel
    · intro α β c
      rw [map_zsmul, Preadditive.zsmul_comp, key, Preadditive.zsmul_comp, map_zsmul, smul_sub]

end GlobalTheory.EZ.Cone
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.PBFc
open GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ

variable {R : Type} [CommRing R]

abbrev BSx (X : SimplicialObject Spc) (a b : ℕ) (U : Scheme.{0}) : Type :=
  ((X.obj (op (SimplexCategory.mk a))).obj (op (SimplexCategory.mk b))).obj (op U)

abbrev BSx.res {X : SimplicialObject Spc} {a b : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (y : BSx X a b U) : BSx X a b V :=
  ((X.obj (op (SimplexCategory.mk a))).obj (op (SimplexCategory.mk b))).map g.op y

theorem biChains_isZero (X : SimplicialObject Spc) (c l : ℤ) (h : 0 < c ∨ 0 < l) :
    IsZero (((biChains R X).X c).X l) := by
  rcases h with h | h
  · exact (HomologicalComplex.eval _ _ l).map_isZero (HomologicalComplex.isZero_extend_X _ _ c (fun i hi => by
      change -((i : ℕ) : ℤ) = c at hi
      omega))
  · by_cases hc : c ≤ 0
    · obtain ⟨a, rfl⟩ : ∃ a : ℕ, c = -(a : ℤ) := ⟨(-c).toNat, by omega⟩
      refine IsZero.of_iso ?_ ((HomologicalComplex.eval _ _ l).mapIso
        (HomologicalComplex.extendXIso _ ComplexShape.embeddingDownNat (i := a) rfl))
      exact HomologicalComplex.isZero_extend_X _ _ l (fun i hi => by
        change -((i : ℕ) : ℤ) = l at hi
        omega)
    · exact (HomologicalComplex.eval _ _ l).map_isZero (HomologicalComplex.isZero_extend_X _ _ c (fun i hi => by
        change -((i : ℕ) : ℤ) = c at hi
        omega))

def evT {X : SimplicialObject Spc} {K : Cx R} {n : ℤ} (γ : Cochain (totChains R X) K n) (a b : ℕ) (s : ℤ)
    (h : -((a + b : ℕ) : ℤ) + n = s) (U : Scheme.{0}) (y : BSx X a b U) : Sec (K.X s) U :=
  Sec.map ((biChainsXIso R X a b).inv ≫ (biChains R X).ιTotal (ComplexShape.up ℤ) (-(a : ℤ)) (-(b : ℤ))
      (-((a + b : ℕ) : ℤ)) (by simp only [ComplexShape.π_def]; push_cast; ring) ≫ γ.v _ s h) (freeGen R _ U y)

theorem evT_ext {X : SimplicialObject Spc} {K : Cx R} {n : ℤ} (γ γ' : Cochain (totChains R X) K n)
    (h : ∀ a b s h U y, evT γ a b s h U y = evT γ' a b s h U y) : γ = γ' := by
  ext t s hs : 1
  apply HomologicalComplex₂.total.hom_ext
  intro c l hcl
  have hcl' : c + l = t := hcl
  by_cases hc : c ≤ 0 ∧ l ≤ 0
  · obtain ⟨a, rfl⟩ : ∃ a : ℕ, c = -(a : ℤ) := ⟨(-c).toNat, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b : ℕ, l = -(b : ℤ) := ⟨(-l).toNat, by omega⟩
    obtain rfl : t = -((a + b : ℕ) : ℤ) := by push_cast; omega
    rw [← cancel_epi (biChainsXIso R X a b).inv]
    exact free_ext _ _ fun U y => h a b s hs U y
  · exact (biChains_isZero X c l (by omega)).eq_of_src _ _

theorem evT_exists {X : SimplicialObject Spc} {K : Cx R} {n : ℤ}
    (f : ∀ (a b : ℕ) (s : ℤ), -((a + b : ℕ) : ℤ) + n = s → ∀ U : Scheme.{0}, BSx X a b U → Sec (K.X s) U)
    (hf : ∀ a b s h (V U : Scheme.{0}) (g : V ⟶ U) (y : BSx X a b U), Sec.res g (f a b s h U y) = f a b s h V (y.res g)) :
    ∃ γ : Cochain (totChains R X) K n, ∀ a b s h U y, evT γ a b s h U y = f a b s h U y := by
  have key : ∀ (c l s : ℤ) (hs : c + l + n = s), ∃ ψ : ((biChains R X).X c).X l ⟶ K.X s,
      ∀ (a b : ℕ) (hc : c = -(a : ℤ)) (hl : l = -(b : ℤ)) U y,
        Sec.map ((biChainsXIso R X a b).inv ≫ eqToHom (by rw [hc, hl]) ≫ ψ) (freeGen R _ U y) =
          f a b s (by push_cast; omega) U y := by
    intro c l s hs
    by_cases hc : c ≤ 0 ∧ l ≤ 0
    · obtain ⟨a, rfl⟩ : ∃ a : ℕ, c = -(a : ℤ) := ⟨(-c).toNat, by omega⟩
      obtain ⟨b, rfl⟩ : ∃ b : ℕ, l = -(b : ℤ) := ⟨(-l).toNat, by omega⟩
      obtain ⟨φ, hφ⟩ := free_exists (R := R) _ _ (f a b s (by push_cast; omega)) (fun V U g y => hf a b s _ V U g y)
      refine ⟨(biChainsXIso R X a b).hom ≫ φ, fun a' b' hc hl U y => ?_⟩
      obtain rfl : a' = a := by omega
      obtain rfl : b' = b := by omega
      rw [eqToHom_refl, Category.id_comp, Iso.inv_hom_id_assoc]
      exact hφ U y
    · exact ⟨0, fun a b hc' hl' => by omega⟩
  choose ψ hψ using key
  refine ⟨Cochain.mk fun t s h => (biChains R X).totalDesc fun c l hcl => ψ c l s (by
      have : c + l = t := hcl
      omega), fun a b s h U y => ?_⟩
  unfold evT
  rw [Cochain.mk_v, HomologicalComplex₂.ι_totalDesc]
  have := hψ (-(a : ℤ)) (-(b : ℤ)) s (by push_cast at h ⊢; omega) a b rfl rfl U y
  rw [eqToHom_refl, Category.id_comp] at this
  exact this

section Cross
variable {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N))

def baseS {a b : ℕ} {U : Scheme.{0}} (y : BSx (twX E V) a b U) : Sx E a U :=
  (show (E.obj (op (SimplexCategory.mk a))).obj (op U) × ((Fib N).obj (op (SimplexCategory.mk b))).obj (op U) from y).1

variable {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B)

def vertS {a b : ℕ} {U : Scheme.{0}} (y : BSx (twX E V) a b U) : Sx B b U :=
  ((ℓ.app (op (SimplexCategory.mk a))).app (op (SimplexCategory.mk b))).app (op U) y

theorem baseS_res {a b : ℕ} {W U : Scheme.{0}} (g : W ⟶ U) (y : BSx (twX E V) a b U) :
    baseS V (y.res g) = (baseS V y).res g := rfl

theorem vertS_res {a b : ℕ} {W U : Scheme.{0}} (g : W ⟶ U) (y : BSx (twX E V) a b U) :
    vertS V ℓ (y.res g) = (vertS V ℓ y).res g :=
  ConcreteCategory.congr_hom (((ℓ.app (op (SimplexCategory.mk a))).app (op (SimplexCategory.mk b))).naturality g.op) y

variable {I J K : Cx R} (μ : Pair I J K) {n m k : ℤ} (hk : n + m = k) (α : Cochain ((chains R).obj E) I n)
  (z : Cochain ((chains R).obj B) J m)

def crossVal (a b : ℕ) (s : ℤ) (h : -((a + b : ℕ) : ℤ) + k = s) (U : Scheme.{0}) (y : BSx (twX E V) a b U) :
    Sec (K.X s) U :=
  (m * (a : ℤ)).negOnePow • μ.mul U (-(a : ℤ) + n) (-(b : ℤ) + m) s (by push_cast at h; omega)
    (_root_.GlobalTheory.EtC.ev (R := R) α a _ rfl U (baseS V y))
    (_root_.GlobalTheory.EtC.ev (R := R) z b _ rfl U (vertS V ℓ y))

theorem crossVal_res (a b : ℕ) (s : ℤ) (h : -((a + b : ℕ) : ℤ) + k = s) {W U : Scheme.{0}} (g : W ⟶ U)
    (y : BSx (twX E V) a b U) :
    Sec.res g (crossVal V ℓ μ hk α z a b s h U y) = crossVal V ℓ μ hk α z a b s h W (y.res g) := by
  unfold crossVal
  rw [Units.smul_def, Units.smul_def, Sec.res, map_zsmul, ← Sec.res, μ.nat, ev_res, ev_res, baseS_res, vertS_res]

def crossT : Cochain (totChains R (twX E V)) K k :=
  (evT_exists (crossVal V ℓ μ hk α z) (fun a b s h W U g y => crossVal_res V ℓ μ hk α z a b s h g y)).choose

theorem evT_crossT (a b : ℕ) (s : ℤ) (h : -((a + b : ℕ) : ℤ) + k = s) (U : Scheme.{0}) (y : BSx (twX E V) a b U) :
    evT (crossT V ℓ μ hk α z) a b s h U y =
      (m * (a : ℤ)).negOnePow • μ.mul U (-(a : ℤ) + n) (-(b : ℤ) + m) s (by push_cast at h; omega)
        (_root_.GlobalTheory.EtC.ev (R := R) α a _ rfl U (baseS V y))
        (_root_.GlobalTheory.EtC.ev (R := R) z b _ rfl U (vertS V ℓ y)) :=
  (evT_exists (crossVal V ℓ μ hk α z) (fun a b s h W U g y => crossVal_res V ℓ μ hk α z a b s h g y)).choose_spec a b s h U y

theorem evT_add {X : SimplicialObject Spc} {L : Cx R} {t : ℤ} (γ γ' : Cochain (totChains R X) L t) (a b : ℕ) (s : ℤ)
    (h : -((a + b : ℕ) : ℤ) + t = s) (U : Scheme.{0}) (y : BSx X a b U) :
    evT (γ + γ') a b s h U y = evT γ a b s h U y + evT γ' a b s h U y := by
  unfold evT
  rw [Cochain.add_v, Preadditive.comp_add, Preadditive.comp_add]
  exact map_add (mapHom _ _ (freeGen R _ U y)) _ _

theorem crossT_add_left (α' : Cochain ((chains R).obj E) I n) :
    crossT V ℓ μ hk (α + α') z = crossT V ℓ μ hk α z + crossT V ℓ μ hk α' z :=
  evT_ext _ _ fun a b s h U y => by
    rw [evT_add, evT_crossT, evT_crossT, evT_crossT, ev_add, map_add (f := _), LinearMap.add_apply, smul_add]

theorem evT_zero {X : SimplicialObject Spc} {L : Cx R} {t : ℤ} (a b : ℕ) (s : ℤ)
    (h : -((a + b : ℕ) : ℤ) + t = s) (U : Scheme.{0}) (y : BSx X a b U) :
    evT (0 : Cochain (totChains R X) L t) a b s h U y = 0 := by
  unfold evT
  rw [Cochain.zero_v, comp_zero, comp_zero]
  exact map_zero (mapHom _ _ (freeGen R _ U y))

theorem crossT_zero_right : crossT V ℓ μ hk α (0 : Cochain ((chains R).obj B) J m) = 0 :=
  evT_ext _ _ fun a b s h U y => by
    rw [evT_crossT, evT_zero, ev_zero, map_zero, smul_zero]

end Cross

def twPairI (q : ℕ) (i j : ℤ) : Pair (res (ZMod q) (tw q (i - j))) (res (ZMod q) (tw q j)) (res (ZMod q) (tw q i)) :=
  Eq.rec (motive := fun k _ => Pair (res (ZMod q) (tw q (i - j))) (res (ZMod q) (tw q j)) (res (ZMod q) (tw q k)))
    (twPair q (i - j) j) (sub_add_cancel i j)

def phi (q : ℕ) {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc}
    (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) (i : ℤ)
    (z : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ)))
    (n : ℤ) :
    (∀ j : Fin N, Cochain ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (n - 2 * ((j : ℕ) : ℤ))) →+
      Cochain (totChains (ZMod q) (twX E V)) (res _ (tw q i)) n :=
  AddMonoidHom.mk' (fun α => ∑ j : Fin N, crossT V ℓ (twPairI q i ((j : ℕ) : ℤ)) (sub_add_cancel n _) (α j) (z j))
    (fun α α' => by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => crossT_add_left V ℓ _ _ _ _ _)

theorem phi_apply (q : ℕ) {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc}
    (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) (i : ℤ)
    (z : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ)))
    (n : ℤ) (α : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (n - 2 * ((j : ℕ) : ℤ))) :
    phi q V ℓ i z n α = ∑ j : Fin N, crossT V ℓ (twPairI q i ((j : ℕ) : ℤ)) (sub_add_cancel n _) (α j) (z j) := rfl

end GlobalTheory.PBFc

end
end

section

open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.TorusFrame
open scoped ENNReal

namespace GlobalTheory.TorusFrame

theorem hasStrictFDerivAt_torus_zero (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (x : Frame Ψ r) : HasStrictFDerivAt (fun θ : Ψ → Fin (r - 1) → ℝ => fun τ a b => (mat x τ * diagonal (fun c => Complex.exp (Complex.I * (angles (θ τ) c : ℂ))) * (mat x τ)⁻¹) a b) (torusDer x) 0 := by
  refine hasStrictFDerivAt_pi'' fun τ => hasStrictFDerivAt_pi'' fun a => hasStrictFDerivAt_pi'' fun b => ?_
  set A : Fin r → ((Ψ → Fin (r - 1) → ℝ) →L[ℝ] ℂ) := fun c =>
    Complex.ofRealCLM.comp ((ContinuousLinearMap.proj c).comp ((LinearMap.toContinuousLinearMap (anglesL r)).comp (ContinuousLinearMap.proj τ))) with hA
  have hAapp : ∀ c θ, A c θ = (angles (θ τ) c : ℂ) := fun c θ => rfl
  have hc : ∀ c : Fin r, HasStrictFDerivAt (fun θ : Ψ → Fin (r - 1) → ℝ => mat x τ a c * Complex.exp (Complex.I * (angles (θ τ) c : ℂ)) * (mat x τ)⁻¹ c b)
      (((mat x τ)⁻¹ c b) • (mat x τ a c • (Complex.exp (Complex.I * (angles ((0 : Ψ → Fin (r - 1) → ℝ) τ) c : ℂ)) • (Complex.I • A c)))) 0 := by
    intro c
    have h1 : HasStrictFDerivAt (fun θ : Ψ → Fin (r - 1) → ℝ => (angles (θ τ) c : ℂ)) (A c) 0 := (A c).hasStrictFDerivAt
    exact ((h1.const_mul Complex.I).cexp.const_mul (mat x τ a c)).mul_const ((mat x τ)⁻¹ c b)
  have hs := HasStrictFDerivAt.sum (u := Finset.univ) (fun c _ => hc c)
  refine (hs.congr_fderiv ?_).congr_of_eventuallyEq ?_
  · ext θ
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.proj_apply, torusDer_apply,
      ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, hAapp,
      angles_zero, Pi.zero_apply, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_smul, smul_eq_mul]
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  · refine Filter.Eventually.of_forall fun θ => ?_
    simp only [Finset.sum_apply]
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal]
end GlobalTheory.TorusFrame
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff

namespace GlobalTheory.WhitBump

theorem psiFin_superDiag_eq_one_of_integral : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ)
    (u : GL (Fin n) (Af E)), u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n) →
    u ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n → psiFin (GlobalTheory.Whittaker.superDiag u) = 1 := by
  intro E _ _ _ n u _ hk
  have hent := ((GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff E n).1 hk).1
  have hs : GlobalTheory.Whittaker.superDiag u ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E := by
    unfold GlobalTheory.Whittaker.superDiag
    exact Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => hent i j
  have hd : sFin E (GlobalTheory.Whittaker.superDiag u) ∈ GroundTheory.Global.invDifferentAdeles E :=
    GroundTheory.Global.mem_invDifferentAdeles.mpr
      (GroundTheory.Global.mem_finiteInvDifferent_of_mem_integralFiniteAdeles hs)
  unfold psiFin
  rw [GroundTheory.Global.adelicChar_of_mem_invDifferentAdeles hd]
  have h0 : (sFin E (GlobalTheory.Whittaker.superDiag u)).1 = 0 := rfl
  rw [h0, map_zero, neg_zero, AddChar.map_zero_eq_one]
  simp

end GlobalTheory.WhitBump
end

section

open CategoryTheory GlobalTheory.CatCoh

namespace GlobalTheory.CatCoh.Desc.VandermondeTwoBasis


open Classical in
theorem coboundary_on_piece : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (T : C) (e : F.obj T) (p : C') (v : T ⟶ G.obj p), (∀ (S : C) (u : T ⟶ S), IsUnit (mp F u e) → Nonempty (G.obj p ⟶ S)) → ∀ (z : ∀ t t' t'', (T ⟶ G.obj t) → (t ⟶ t') → (t' ⟶ t'') → F.obj (G.obj t'')), (∀ t t' t'' t''' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t'') (c : t'' ⟶ t'''), mp F (G.map c) (z t t' t'' u a b) + z t t'' t''' u (a ≫ b) c = z t t' t''' u a (b ≫ c) + z t' t'' t''' (u ≫ G.map a) b c) → ∃ y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t'), ∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), IsUnit (mp F u e) → mp F (G.map b) (y t t' u a) - y t t'' u (a ≫ b) + y t' t'' (u ≫ G.map a) b = z t t' t'' u a b := by
  intro R _ C _ C' _ F G _ _ H hdir T e p v he z hz
  have cov : ∀ (t : C') (u : T ⟶ G.obj t), IsUnit (mp F u e) →
      CovBy F (fun S ↦ ∃ (t' : C') (_ : t ⟶ t'), Nonempty (p ⟶ t') ∧ Nonempty (G.obj t' ⟶ S))
        (G.obj t) := by
    intro t u hu
    obtain ⟨w⟩ := he _ u hu
    obtain ⟨n, b, hb, h⟩ := hdir t p (G.obj t) (𝟙 _) w
    refine ⟨n, b, hb, fun i S' u' hi ↦ ?_⟩
    obtain ⟨t₃, ⟨a⟩, h2, h3⟩ := h i S' u' hi
    exact ⟨t₃, a, h2, h3⟩
  have up : ∀ (t t' t'' : C') (_ : t ⟶ t') (_ : t' ⟶ t''), Nonempty (p ⟶ t') → Nonempty (p ⟶ t'') :=
    fun _ _ _ _ b ⟨α⟩ ↦ ⟨α ≫ b⟩
  exact coboundary_of_restrict (G ⋙ F) (E := fun t ↦ T ⟶ G.obj t) (fun u a ↦ u ≫ G.map a)
    (fun _ _ _ ↦ Subsingleton.elim _ _) (fun t u ↦ IsUnit (mp F u e))
    (fun t _ ↦ Nonempty (p ⟶ t)) (fun _ _ _ a h ↦ isUnit_comp (G.map a) h)
    (fun t u hu ↦ sep_of_covBy F G H hdir t (fun t' _ ↦ Nonempty (p ⟶ t')) (up t) (cov t u hu))
    (fun t u hu ↦ GlobalTheory.T.exists_glued_section_upwardFamily_standardCover F G H hdir t (fun t' _ ↦ Nonempty (p ⟶ t')) (up t) (cov t u hu))
    (fun t u hu ↦ GlobalTheory.T.van1_of_covBy_upward_sieve F G H hdir t (fun t' _ ↦ Nonempty (p ⟶ t')) (up t) (cov t u hu))
    z (fun t t' t'' t''' u a b c _ ↦ hz t t' t'' t''' u a b c)
    (fun t t' _ a ↦ if h : Nonempty (p ⟶ t) then z p t t' v h.some a else 0)
    (fun t t' t'' u a b hp ↦ by
      have hp' := up t t t' (𝟙 t) a hp
      simp only [dif_pos hp, dif_pos hp']
      have k := hz p t t' t'' v hp.some a b
      rw [Subsingleton.elim (v ≫ G.map hp.some) u,
        Subsingleton.elim (hp.some ≫ a) hp'.some] at k
      change mp F (G.map b) (z p t t' v hp.some a) - z p t t'' v hp.some (a ≫ b) +
        z p t' t'' v hp'.some b = z t t' t'' u a b
      linear_combination k)

end GlobalTheory.CatCoh.Desc.VandermondeTwoBasis
end

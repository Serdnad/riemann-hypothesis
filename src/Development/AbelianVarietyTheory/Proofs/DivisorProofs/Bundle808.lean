module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle769
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle774
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle601
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle292
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle452
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle157
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle290
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle102
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle777
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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

@[expose] public section

section

open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechCmp

variable {I : Type} [Finite I] {X : Scheme.{0}} {R : Type} [CommRing R] (s : X ⟶ Sp R) (U : I → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W))

theorem toCech_cocycle_read (f : GlobalTheory.CatCoh.C1 (capF s U hU hinf)) (hf : f ∈ Z1 (capF s U hU hinf))
    (x : I) (P K : NE I) (hxP : P ≤ NE.single x) (hPK : K ≤ P) (hxK : K ≤ NE.single x)
    (W : X.Opens) (hW : W ≤ cap U K) :
    rsT (cv s U hU hinf (op P) (f (op (NE.single x)) (op P) (homOfLE hxP).op)) W =
      rsT (cv s U hU hinf (op K) (f (op (NE.single x)) (op K) (homOfLE hxK).op)) W -
        rsT (cv s U hU hinf (op K) (f (op P) (op K) (homOfLE hPK).op)) W := by
  have e := Z1.comp ⟨f, hf⟩ (homOfLE hxP).op (homOfLE hPK).op
  have hc : (homOfLE hxP).op ≫ (homOfLE hPK).op = (homOfLE hxK).op := Subsingleton.elim _ _
  rw [hc] at e
  have e' := congrArg (fun b => rsT (cv s U hU hinf (op K) b) W) e
  simp only [map_add (f := _), GlobalTheory.KS.rsT_add] at e'
  rw [cv_mp s U hU hinf (homOfLE hPK).op] at e'
  rw [GlobalTheory.KS.rsT_rsT (O₁ := cap U (op K).unop) (cap_mono U hPK) hW] at e'
  rw [e']
  abel

theorem toCech_isCoc (f : GlobalTheory.CatCoh.C1 (capF s U hU hinf)) (hf : f ∈ Z1 (capF s U hU hinf)) :
    IsCoc U (toCech s U hU hinf f) := by
  intro i j k
  let K : NE I := OrderDual.toDual ⟨{i, j, k}, Set.insert_nonempty i {j, k}⟩
  have hi : i ∈ K.set := Set.mem_insert i _
  have hj : j ∈ K.set := Set.mem_insert_of_mem i (Set.mem_insert j _)
  have hk : k ∈ K.set := Set.mem_insert_of_mem i (Set.mem_insert_of_mem j rfl)
  have sgl : ∀ {a : I}, a ∈ K.set → K ≤ NE.single a := fun ha => NE.le_iff.2 (Set.singleton_subset_iff.2 ha)
  have pr : ∀ {a b : I}, a ∈ K.set → b ∈ K.set → K ≤ NE.pair a b :=
    fun ha hb => NE.le_iff.2 (Set.insert_subset ha (Set.singleton_subset_iff.2 hb))
  have hW : U i ⊓ U j ⊓ U k ≤ cap U K := le_iInf₂ fun x hx => by
    rcases hx with rfl | rfl | rfl
    · exact inf_le_left.trans inf_le_left
    · exact inf_le_left.trans inf_le_right
    · exact inf_le_right
  have hij : U i ⊓ U j ⊓ U k ≤ U i ⊓ U j := inf_le_left
  have hjk : U i ⊓ U j ⊓ U k ≤ U j ⊓ U k := le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have hik : U i ⊓ U j ⊓ U k ≤ U i ⊓ U k := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  simp only [toCech_apply, GlobalTheory.KS.rsT_sub]
  rw [GlobalTheory.KS.rsT_rsT (cap_pair U i j).ge hij, GlobalTheory.KS.rsT_rsT (cap_pair U i j).ge hij,
    GlobalTheory.KS.rsT_rsT (cap_pair U j k).ge hjk, GlobalTheory.KS.rsT_rsT (cap_pair U j k).ge hjk,
    GlobalTheory.KS.rsT_rsT (cap_pair U i k).ge hik, GlobalTheory.KS.rsT_rsT (cap_pair U i k).ge hik]
  rw [toCech_cocycle_read s U hU hinf f hf i _ K _ (pr hi hj) (sgl hi) _ hW,
    toCech_cocycle_read s U hU hinf f hf j _ K _ (pr hi hj) (sgl hj) _ hW,
    toCech_cocycle_read s U hU hinf f hf j _ K _ (pr hj hk) (sgl hj) _ hW,
    toCech_cocycle_read s U hU hinf f hf k _ K _ (pr hj hk) (sgl hk) _ hW,
    toCech_cocycle_read s U hU hinf f hf i _ K _ (pr hi hk) (sgl hi) _ hW,
    toCech_cocycle_read s U hU hinf f hf k _ K _ (pr hi hk) (sgl hk) _ hW]
  abel

theorem isCoc_toCech : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R] (s : X ⟶ Sp R) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)), ∀ f : GlobalTheory.CatCoh.C1 (capF s U hU hinf), f ∈ Z1 (capF s U hU hinf) → IsCoc U (toCech s U hU hinf f) :=
  fun _ _ _ _ _ s U hU hinf f hf => toCech_isCoc s U hU hinf f hf

end GlobalTheory.CechCmp
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CechCmp

variable {R : Type} [CommRing R] {Z : Scheme.{0}} (s : Z ⟶ Sp R) {J : Type} (W : J → Z.Opens)

theorem resG_secMap_lin {U V : Z.Opens} (h : V ≤ U) (r : R) :
    resG Z h ((secMap s U).hom r) = (secMap s V).hom r := by
  exact (Sec.res s h).commutes r

theorem resG_sub_sum_lin {U V : Z.Opens} (h : V ≤ U) (x : Γ(Z, U)) {N : ℕ} (r : Fin N → R)
    (y : Fin N → Γ(Z, U)) :
    resG Z h (x - ∑ k, (secMap s U).hom (r k) * y k) =
      resG Z h x - ∑ k, (secMap s V).hom (r k) * resG Z h (y k) := by

  rw [map_sub, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [map_mul, resG_secMap_lin]

theorem isCocycle_sub_sum_lin {c : ∀ i i' : J, Γ(Z, W i ⊓ W i')} (hc : IsCocycle W c) {N : ℕ}
    (r : Fin N → R) {e : Fin N → ∀ i i' : J, Γ(Z, W i ⊓ W i')} (he : ∀ k, IsCocycle W (e k)) :
    IsCocycle W (fun i i' => c i i' - ∑ k, (secMap s (W i ⊓ W i')).hom (r k) * e k i i') := by
  intro i i' i''
  beta_reduce
  rw [resG_sub_sum_lin, resG_sub_sum_lin, resG_sub_sum_lin]
  simp only [← hc i i' i'', ← he _ i i' i'', mul_add,
    Finset.sum_add_distrib]
  ring

theorem fc_sub_sum_lin (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')) {N : ℕ}
    (r : Fin N → R) (e : Fin N → ∀ i i' : J, Γ(Z, W i ⊓ W i')) :
    fc s W (fun i i' => c i i' - ∑ k, (secMap s (W i ⊓ W i')).hom (r k) * e k i i') =
      fc s W c - ∑ k, r k • fc s W (e k) := by
  funext V V' a
  simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply]
  simp only [Algebra.smul_def]
  exact resG_sub_sum_lin s _ _ r _

theorem cmp_sub_sum_lin : ∀ (R : Type) [CommRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (J : Type) (W : J → Z.Opens) (hW : ⨆ i, W i = ⊤) (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')), GlobalTheory.CechCmp.IsCocycle W c → ∀ (N : ℕ) (r : Fin N → R) (e : Fin N → ∀ i i' : J, Γ(Z, W i ⊓ W i')), (∀ k, GlobalTheory.CechCmp.IsCocycle W (e k)) → GlobalTheory.CechCmp.cmp s W hW (fun i i' => c i i' - ∑ k, (GlobalTheory.CechDR.secMap s (W i ⊓ W i')).hom (r k) * e k i i') = GlobalTheory.CechCmp.cmp s W hW c - ∑ k, r k • GlobalTheory.CechCmp.cmp s W hW (e k) := by
  intro R _ Z s J W hW c hc N r e he
  rw [cmp_of_isCocycle s W hW (isCocycle_sub_sum_lin s W hc r he), cmp_of_isCocycle s W hW hc]

  simp only [fun k ↦ cmp_of_isCocycle s W hW (he k), ← map_smul, ← map_sum, ← map_sub]
  congr 2
  refine Subtype.ext ?_
  simp only [Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul]
  exact fc_sub_sum_lin s W c r e

end GlobalTheory.CechCmp
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CechCmp

theorem IsCocycle.res_on {Z : Scheme.{0}} {J : Type} {W : J → Z.Opens}
    {c : ∀ i i' : J, Γ(Z, W i ⊓ W i')} (hc : IsCocycle W c) {U : Z.Opens} {i j k : J}
    (hi : U ≤ W i) (hj : U ≤ W j) (hk : U ≤ W k) :
    resG Z (le_inf hi hj) (c i j) + resG Z (le_inf hj hk) (c j k) =
      resG Z (le_inf hi hk) (c i k) := by
  have e := congrArg (resG Z (le_inf (le_inf hi hj) hk)) (hc i j k)
  simp only [map_add (f := _), resG_resG'] at e
  exact e

theorem exists_coboundary_of_cmp_eq_zero (R : Type) [CommRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R)
    (J : Type) (W : J → Z.Opens) (hW : ⨆ i, W i = ⊤) (hWa : ∀ i, IsAffineOpen (W i))
    (hWb : ∀ i i', IsAffineOpen (W i ⊓ W i')) (c : ∀ i i' : J, Γ(Z, W i ⊓ W i'))
    (hc : IsCocycle W c) (h0 : cmp s W hW c = 0) :
    ∃ h : ∀ i : J, Γ(Z, W i), ∀ i i',
      c i i' = resG Z inf_le_left (h i) - resG Z inf_le_right (h i') := by
  have h1 := restrict_cmp s W hW hc
  rw [h0, map_zero] at h1
  obtain ⟨g, hg⟩ := CatCoh.H1.mk_eq_zero.1 h1.symm
  let g' : ∀ V : Bas W, Γ(Z, V.1.1) := fun V ↦ g (Opposite.op V)
  have key : ∀ (V V' : Bas W) (h : V'.1.1 ≤ V.1.1),
      g' V' - resG Z h (g' V) =
        resG Z (le_inf (h.trans (le_idx V)) (le_idx V')) (c (idx V) (idx V')) := by
    intro V V' h
    exact congrFun (congrFun (congrFun hg (Opposite.op V)) (Opposite.op V'))
      (homOfLE (show V' ≤ V from h)).op
  let Ω : J → Bas W := fun i ↦ ⟨⟨W i, hWa i⟩, i, le_rfl⟩
  have hΩ : ∀ i, W i ≤ W (idx (Ω i)) := fun i ↦ le_idx (Ω i)
  let g₁ : ∀ i, Γ(Z, W i) := fun i ↦ g' (Ω i)
  refine ⟨fun i ↦ resG Z (le_inf le_rfl (hΩ i)) (c i (idx (Ω i))) - g₁ i, fun i i' ↦ ?_⟩
  let Ω₂ : Bas W := ⟨⟨W i ⊓ W i', hWb i i'⟩, i, inf_le_left⟩
  have hd : W i ⊓ W i' ≤ W (idx Ω₂) := le_idx Ω₂
  let g₂ : Γ(Z, W i ⊓ W i') := g' Ω₂
  have k1 : g₂ - resG Z inf_le_left (g₁ i) =
      resG Z (le_inf (inf_le_left.trans (hΩ i)) hd) (c (idx (Ω i)) (idx Ω₂)) :=
    key (Ω i) Ω₂ inf_le_left
  have k2 : g₂ - resG Z inf_le_right (g₁ i') =
      resG Z (le_inf (inf_le_right.trans (hΩ i')) hd) (c (idx (Ω i')) (idx Ω₂)) :=
    key (Ω i') Ω₂ inf_le_right
  have e1 := hc.res_on (inf_le_left : W i ⊓ W i' ≤ _) (inf_le_left.trans (hΩ i)) hd
  have e2 := hc.res_on (inf_le_right : W i ⊓ W i' ≤ _) (inf_le_right.trans (hΩ i')) hd
  have e3 := hc.res_on (inf_le_left : W i ⊓ W i' ≤ _) inf_le_right hd
  have e4 : resG Z (le_inf (inf_le_left : W i ⊓ W i' ≤ _) inf_le_right) (c i i') = c i i' := by
    have : (homOfLE (le_inf (inf_le_left : W i ⊓ W i' ≤ _) inf_le_right)).op = 𝟙 _ := rfl
    simp only [resG, this, CategoryTheory.Functor.map_id]
    rfl
  rw [e4] at e3
  simp only [map_sub, resG_resG']
  linear_combination e3 - e1 + e2 - k1 + k2

end GlobalTheory.CechCmp
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CechCmp

variable {R : Type} [CommRing R] {Z : Scheme.{0}} (s : Z ⟶ Sp R) {J : Type} (W : J → Z.Opens)

def cocVal (z : Z1 (incl W ⋙ OAff s)) (V V' : Bas W) (h : V'.1.1 ≤ V.1.1) : Γ(Z, V'.1.1) :=
  z.1 (Opposite.op V) (Opposite.op V') (homOfLE (show V' ≤ V from h)).op

theorem cocVal_comp (z : Z1 (incl W ⋙ OAff s)) (A B C : Bas W) (h : B.1.1 ≤ A.1.1)
    (h' : C.1.1 ≤ B.1.1) :
    resG Z h' (cocVal s W z A B h) = cocVal s W z A C (h'.trans h) - cocVal s W z B C h' :=
  eq_sub_of_add_eq (Z1.comp z (homOfLE (show B ≤ A from h)).op
    (homOfLE (show C ≤ B from h')).op).symm

theorem exists_isCocycle_cmp_eq (R : Type) [CommRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (J : Type)
    (W : J → Z.Opens) (hW : ⨆ i, W i = ⊤) (h1 : ∀ i, IsAffineOpen (W i))
    (h2 : ∀ i i', IsAffineOpen (W i ⊓ W i'))
    (h3 : ∀ i i' i'', IsAffineOpen (W i ⊓ W i' ⊓ W i'')) (x : GlobalTheory.CechDR.HO1 s) :
    ∃ c : ∀ i i' : J, Γ(Z, W i ⊓ W i'), IsCocycle W c ∧ cmp s W hW c = x := by
  obtain ⟨z, hz⟩ := H1.mk_surjective _ (resEquiv s W hW x)
  let O1 : J → Bas W := fun i ↦ ⟨⟨W i, h1 i⟩, i, le_rfl⟩
  let O2 : J → J → Bas W := fun i i' ↦ ⟨⟨W i ⊓ W i', h2 i i'⟩, i, inf_le_left⟩
  let O3 : J → J → J → Bas W := fun i i' i'' ↦
    ⟨⟨W i ⊓ W i' ⊓ W i'', h3 i i' i''⟩, i, inf_le_left.trans inf_le_left⟩
  let c : ∀ i i' : J, Γ(Z, W i ⊓ W i') := fun i i' ↦
    cocVal s W z (O1 i) (O2 i i') inf_le_left - cocVal s W z (O1 i') (O2 i i') inf_le_right
  have key : ∀ (i i' : J) (V : Bas W) (h : V.1.1 ≤ W i ⊓ W i'),
      resG Z h (c i i') = cocVal s W z (O1 i) V (h.trans inf_le_left) -
        cocVal s W z (O1 i') V (h.trans inf_le_right) := by
    intro i i' V h
    have e1 := cocVal_comp s W z (O1 i) (O2 i i') V inf_le_left h
    have e2 := cocVal_comp s W z (O1 i') (O2 i i') V inf_le_right h
    have e : resG Z h (c i i') =
        resG Z h (cocVal s W z (O1 i) (O2 i i') inf_le_left) -
          resG Z h (cocVal s W z (O1 i') (O2 i i') inf_le_right) := map_sub _ _ _
    rw [e]
    refine (congrArg₂ (· - ·) e1 e2).trans ?_
    ring
  have hc : IsCocycle W c := by
    intro i i' i''
    have e1 := key i i' (O3 i i' i'') inf_le_left
    have e2 := key i' i'' (O3 i i' i'') (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
    have e3 := key i i'' (O3 i i' i'') (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
    refine (congrArg₂ (· + ·) e1 e2).trans (Eq.trans ?_ e3.symm)
    ring
  refine ⟨c, hc, ?_⟩
  rw [cmp_of_isCocycle s W hW hc, LinearEquiv.symm_apply_eq, ← hz, H1.mk_eq_mk]
  refine ⟨fun V ↦ -cocVal s W z (O1 (idx V.unop)) V.unop (le_idx V.unop), ?_⟩
  funext V V' a
  have e1 := key (idx V.unop) (idx V'.unop) V'.unop
    (le_inf ((le_of_hom a).trans (le_idx V.unop)) (le_idx V'.unop))
  have e2 := cocVal_comp s W z (O1 (idx V.unop)) V.unop V'.unop (le_idx V.unop) (le_of_hom a)
  have goal : -cocVal s W z (O1 (idx V'.unop)) V'.unop (le_idx V'.unop) -
      resG Z (le_of_hom a) (-cocVal s W z (O1 (idx V.unop)) V.unop (le_idx V.unop)) =
      resG Z (le_inf ((le_of_hom a).trans (le_idx V.unop)) (le_idx V'.unop))
        (c (idx V.unop) (idx V'.unop)) - cocVal s W z V.unop V'.unop (le_of_hom a) := by
    rw [map_neg, e1, e2]
    ring
  exact goal

end GlobalTheory.CechCmp
end
end

section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false

noncomputable section

open GlobalTheory.CatCoh GlobalTheory.CechDR Opposite

namespace GlobalTheory.CechCmp

abbrev PairCov {Z Y : Scheme.{0}} {J : Type} (W : J → Z.Opens) (ι : Y ⟶ Z) : Type :=
  {p : Pair ι // ∃ i, p.1.2.1 ≤ W i}

abbrev pairCovIncl {Z Y : Scheme.{0}} {J : Type} (W : J → Z.Opens) (ι : Y ⟶ Z) :
    (PairCov W ι)ᵒᵖ ⥤ (Pair ι)ᵒᵖ :=
  (Monotone.functor (f := (Subtype.val : PairCov W ι → Pair ι)) fun _ _ h ↦ h).op

abbrev pairCovSnd {Z Y : Scheme.{0}} {J : Type} (W : J → Z.Opens) (ι : Y ⟶ Z) :
    (PairCov W ι)ᵒᵖ ⥤ (Bas W)ᵒᵖ :=
  (Monotone.functor (f := fun p : PairCov W ι ↦ (⟨p.1.1.2, p.2⟩ : Bas W))
    fun _ _ h ↦ Pair.le_snd (φ := ι) h).op

def pairCovPull {R R' : Type} [CommRing R] [CommRing R'] {Z Y : Scheme.{0}} {J : Type}
    (W : J → Z.Opens) {ι : Y ⟶ Z} {s : Z ⟶ Sp R} {s' : Y ⟶ Sp R'} {σ : R →+* R'}
    (w : ι ≫ s = s' ≫ spMap σ) :
    CoefMap σ (incl W ⋙ OAff s) (pairCovIncl W ι ⋙ OPair ι s') where
  G := pairCovSnd W ι
  α p := GlobalTheory.CechDR.secPull s s' p.unop.1
  naturality {p q} a b := (GlobalTheory.CechDR.pairPull w).naturality ((pairCovIncl W ι).map a) b
  smul p := semiHom_secPull w p.unop.1

theorem pairCov_pull1_eq {R R' : Type} [CommRing R] [CommRing R'] {Z Y : Scheme.{0}} {J : Type}
    (W : J → Z.Opens) {ι : Y ⟶ Z} {s : Z ⟶ Sp R} {s' : Y ⟶ Sp R'} {σ : R →+* R'}
    (w : ι ≫ s = s' ≫ spMap σ) (x : HO1 s) :
    (CoefMap.restrict (OPair ι s') (pairCovIncl W ι)).pull1 ((GlobalTheory.CechDR.pairPull w).pull1 x) =
      (pairCovPull W w).pull1 ((CoefMap.restrict (OAff s) (incl W)).pull1 x) := by
  rw [← CoefMap.pullCohomologyOne_comp, ← CoefMap.pullCohomologyOne_comp]
  exact CoefMap.pullCohomologyOne_eq_of_natTrans _ _ (𝟙 _) (fun T b ↦ by rw [NatTrans.id_app, mp_id]) x

theorem pairCov_restrict_injective {R' : Type} [CommRing R'] {Z Y : Scheme.{0}} [Z.IsSeparated]
    {J : Type} (W : J → Z.Opens) (hW : ⨆ i, W i = ⊤) (hWa : ∀ i, IsAffineOpen (W i)) (ι : Y ⟶ Z)
    (s' : Y ⟶ Sp R') :
    Function.Injective (CoefMap.restrict (OAff s') (pairCovIncl W ι ⋙ pairFst ι)).pull1 := by
  let G : (PairCov W ι)ᵒᵖ ⥤ AffOp Y := pairCovIncl W ι ⋙ pairFst ι
  have hcov : ∀ T : AffOp Y, ∃ (n : ℕ) (b : Fin n → (OAff s').obj T),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp Y) (u : T ⟶ S),
        IsUnit (mp (OAff s') u (b i)) →
          ∃ (t : (PairCov W ι)ᵒᵖ) (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u := by
    intro T
    have hT : IsAffineOpen T.unop.1 := T.unop.2
    let Gs : Set Γ(Y, T.unop.1) := {f | ∃ j, Y.basicOpen f ≤ ι ⁻¹ᵁ W j}
    have hG : Ideal.span Gs = ⊤ := by
      rw [← hT.self_le_iSup_basicOpen_iff]
      intro x hx
      have hxU : ι.base x ∈ ⨆ i, W i := by rw [hW]; trivial
      obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hxU
      obtain ⟨f, hf, hxf⟩ := hT.exists_basicOpen_le (V := ι ⁻¹ᵁ W j) ⟨x, hj⟩ hx
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, ⟨j, hf⟩⟩, hxf⟩
    obtain ⟨F, hFG, hF⟩ := (Ideal.span_eq_top_iff_finite Gs).1 hG
    refine ⟨F.card, fun i ↦ (F.equivFin.symm i).1, ?_, ?_⟩
    · have hR : Set.range (fun i : Fin F.card ↦ (F.equivFin.symm i).1) =
          (F : Set Γ(Y, T.unop.1)) := by
        ext f
        constructor
        · rintro ⟨i, rfl⟩; exact (F.equivFin.symm i).2
        · intro hf; exact ⟨F.equivFin ⟨f, hf⟩, by simp⟩
      exact hR ▸ hF
    · intro i S u hu
      obtain ⟨j, hj⟩ := hFG (F.equivFin.symm i).2
      set f : Γ(Y, T.unop.1) := (F.equivFin.symm i).1
      have hB : IsAffineOpen (Y.basicOpen f) := hT.basicOpen f
      have hBT : Y.basicOpen f ≤ T.unop.1 := Y.basicOpen_le f
      have hSB : S.unop.1 ≤ Y.basicOpen f := by
        have h1 : Y.basicOpen (Y.presheaf.map (homOfLE (leOfHom u.unop)).op f) = S.unop.1 :=
          Y.basicOpen_of_isUnit hu
        rw [Scheme.basicOpen_res] at h1
        rw [← h1]; exact inf_le_right
      let p : Pair ι := ⟨(⟨_, hB⟩, ⟨W j, hWa j⟩), hj⟩
      let t : PairCov W ι := ⟨p, j, le_rfl⟩
      refine ⟨op t, (homOfLE (show (⟨_, hB⟩ : Y.affineOpens) ≤ T.unop from hBT)).op,
        (homOfLE (show S.unop ≤ (⟨_, hB⟩ : Y.affineOpens) from hSB)).op, ?_⟩
      exact Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  have hdir : ∀ (t₁ t₂ : (PairCov W ι)ᵒᵖ) (S : AffOp Y), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) →
      ∃ (n : ℕ) (b : Fin n → (OAff s').obj S), Ideal.span (Set.range b) = ⊤ ∧
        ∀ (i : Fin n) (S' : AffOp Y) (u : S ⟶ S'), IsUnit (mp (OAff s') u (b i)) →
          ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S') := by
    intro t₁ t₂ S h₁ h₂
    refine ⟨1, fun _ ↦ 1, ?_, fun _ S' u _ ↦ ?_⟩
    · rw [Ideal.span_eq_top_iff_finite]
      exact ⟨{1}, by simp, by simp⟩
    · obtain ⟨j, hj⟩ := t₁.unop.2
      have hS'S : S'.unop.1 ≤ S.unop.1 := leOfHom u.unop
      have hS1 : S.unop.1 ≤ t₁.unop.1.1.1.1 := leOfHom h₁.unop
      have hS2 : S.unop.1 ≤ t₂.unop.1.1.1.1 := leOfHom h₂.unop
      let A : Z.affineOpens := ⟨t₁.unop.1.1.2.1 ⊓ t₂.unop.1.1.2.1,
        IsAffineOpen.inf t₁.unop.1.1.2.2 t₂.unop.1.1.2.2⟩
      have hA : S'.unop.1 ≤ ι ⁻¹ᵁ A.1 := fun y hy ↦
        ⟨t₁.unop.1.2 (hS1 (hS'S hy)), t₂.unop.1.2 (hS2 (hS'S hy))⟩
      let p₃ : Pair ι := ⟨(S'.unop, A), hA⟩
      let t₃ : PairCov W ι := ⟨p₃, j, inf_le_left.trans hj⟩
      refine ⟨op t₃, ⟨(homOfLE ?_).op⟩, ⟨(homOfLE ?_).op⟩, ⟨𝟙 _⟩⟩
      · exact ⟨hS'S.trans hS1, (inf_le_left : A.1 ≤ t₁.unop.1.1.2.1)⟩
      · exact ⟨hS'S.trans hS2, (inf_le_right : A.1 ≤ t₂.unop.1.1.2.1)⟩
  have H := _root_.GlobalTheory.CechDR.hasLoc_OAff s'
  have hs := _root_.GlobalTheory.sep_of_factoring_cover (OAff s') G H hcov
  have hg := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (OAff s') G H hcov hdir
  exact _root_.GlobalTheory.CatCoh.CoefMap.restrict_pull1_injective_of_sep_glue _ _ hs hg

end GlobalTheory.CechCmp

namespace GlobalTheory.CechCmp

theorem appLE_resG_eq {Z Y : Scheme.{0}} (ι : Y ⟶ Z) {A V : Z.Opens} {T B : Y.Opens} (hV : V ≤ A)
    (e : T ≤ ι ⁻¹ᵁ V) (e' : B ≤ ι ⁻¹ᵁ A) (hT : T ≤ B) (x : Γ(Z, A)) :
    (ι.appLE V T e).hom (resG Z hV x) = resG Y hT ((ι.appLE A B e').hom x) := by
  simp only [resG, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

theorem pullHO1_cmp_eq_zero_of_coboundary : ∀ (R : Type) [CommRing R] (Z : Scheme.{0}) [Z.IsSeparated]
    (s : Z ⟶ Sp R) (J : Type) (W : J → Z.Opens) (hW : ⨆ i, W i = ⊤), (∀ i, IsAffineOpen (W i)) →
    ∀ (R' : Type) [CommRing R'] (σ : R →+* R') (Y : Scheme.{0}) (s' : Y ⟶ Sp R') (ι : Y ⟶ Z)
    (w : ι ≫ s = s' ≫ spMap σ) (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')), GlobalTheory.CechCmp.IsCocycle W c →
    (∃ h' : ∀ i, Γ(Y, ι ⁻¹ᵁ W i), ∀ i i', (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i')
      (fun _ hx => hx)).hom (c i i') = resG Y inf_le_left (h' i) - resG Y inf_le_right (h' i')) →
    GlobalTheory.CechDR.pullHO1 w (GlobalTheory.CechCmp.cmp s W hW c) = 0 := by
  intro R _ Z _ s J W hW hWa R' _ σ Y s' ι w c hc ⟨h', hh'⟩
  set y := GlobalTheory.CechDR.pullHO1 w (cmp s W hW c)
  have e1 : (GlobalTheory.CechDR.pairPull w).pull1 (cmp s W hW c) = (pairRes ι s').pull1 y :=
    isPullO_pullHO1 w _
  apply pairCov_restrict_injective W hW hWa ι s'
  rw [map_zero]
  have e2 : (CoefMap.restrict (OAff s') (pairCovIncl W ι ⋙ pairFst ι)).pull1 y =
      (CoefMap.restrict (OPair ι s') (pairCovIncl W ι)).pull1 ((pairRes ι s').pull1 y) := by
    rw [← CoefMap.pullCohomologyOne_comp]
    exact CoefMap.pullCohomologyOne_eq_of_natTrans _ _ (𝟙 _) (fun T b ↦ by rw [NatTrans.id_app, mp_id]) y
  rw [e2, ← e1, pairCov_pull1_eq, restrict_cmp s W hW hc, CoefMap.pullCohomologyOne_class, H1.mk_eq_zero]
  let ix : PairCov W ι → J := fun p ↦ idx (⟨p.1.1.2, p.2⟩ : Bas W)
  have hix : ∀ p : PairCov W ι, p.1.1.1.1 ≤ ι ⁻¹ᵁ W (ix p) := fun p y hy ↦
    le_idx (⟨p.1.1.2, p.2⟩ : Bas W) (p.1.2 hy)
  refine ⟨fun p ↦ -resG Y (hix p.unop) (h' (ix p.unop)), ?_⟩
  funext p q a
  have hqp : q.unop.1.1.1.1 ≤ p.unop.1.1.1.1 := Pair.le_fst (leOfHom a.unop)
  change -resG Y (hix q.unop) (h' (ix q.unop)) - resG Y hqp (-resG Y (hix p.unop) (h' (ix p.unop))) =
    (ι.appLE _ _ _).hom (resG Z _ (c (ix p.unop) (ix q.unop)))
  rw [map_neg, resG_resG']
  have hT : q.unop.1.1.1.1 ≤ ι ⁻¹ᵁ W (ix p.unop) ⊓ ι ⁻¹ᵁ W (ix q.unop) :=
    le_inf (hqp.trans (hix p.unop)) (hix q.unop)
  have hV : q.unop.1.1.2.1 ≤ W (ix p.unop) ⊓ W (ix q.unop) :=
    le_inf ((show q.unop.1.1.2.1 ≤ p.unop.1.1.2.1 from Pair.le_snd (leOfHom a.unop)).trans (le_idx (⟨p.unop.1.1.2, p.unop.2⟩ : Bas W)))
      (le_idx (⟨q.unop.1.1.2, q.unop.2⟩ : Bas W))
  have k := appLE_resG_eq ι (A := W (ix p.unop) ⊓ W (ix q.unop))
    (B := ι ⁻¹ᵁ W (ix p.unop) ⊓ ι ⁻¹ᵁ W (ix q.unop)) hV q.unop.1.2 (fun _ hx => hx) hT
    (c (ix p.unop) (ix q.unop))
  refine Eq.trans ?_ k.symm
  rw [hh', map_sub, resG_resG', resG_resG']
  ring

end GlobalTheory.CechCmp
end
end

section

open GlobalTheory.ShFam.Hor.LogCh


theorem _root_.GlobalTheory.T.latticeBasis_realBasis_of_holomorphic_family : ∀ (n g r : ℕ) (B : Set (Fin n → ℂ)) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (b₀ : Fin n → ℂ) (lam : Fin r → Fin g → ℂ), IsLatFam B K → b₀ ∈ B → Submodule.span ℝ (K b₀) = ⊤ → LinearIndependent ℤ lam → (∀ w, w ∈ K b₀ ↔ ∃ k : Fin r → ℤ, w = ∑ j, k j • lam j) → LinearIndependent ℝ lam ∧ Submodule.span ℝ (Set.range lam) = ⊤ := by
  first | exact @GlobalTheory.LatReal.isRealBasis_of_isLatFam | exact GlobalTheory.LatReal.isRealBasis_of_isLatFam | (intros; apply GlobalTheory.LatReal.isRealBasis_of_isLatFam <;> assumption)
end

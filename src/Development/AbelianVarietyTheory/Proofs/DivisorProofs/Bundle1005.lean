module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle028
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle485
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Definitions.Divisors.DividedWeightUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle986
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle987
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
import Development.AbelianVarietyTheory.Definitions.Divisors.LeTwoMulOfForallScale
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

set_option autoImplicit false

namespace GlobalTheory.LogDR

theorem smul_mem_spanForms_of_mul_mem {K : Type} [Field K] {M M' : Set K} {H : Set Ω[K⁄ℤ]} {a : ℕ} (g : K)
    (hg : ∀ c ∈ M, g * c ∈ M') {η : abelian₂ K} (hη : η ∈ spanForms M H a) :
    g • η ∈ spanForms M' H a := by
  induction hη using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, v, hv, rfl⟩ := hx
    rw [smul_smul]
    exact AddSubgroup.subset_closure ⟨g * c, hg c hc, v, hv, rfl⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem mem_logAt_add_iff {X : Scheme.{0}} [IsIntegral X] (Z : Set X) (G D : CartierDiv X) (a : ℕ)
    (y : X) (g : X.functionFieldˣ) (η : abelian₂ X.functionField) (hD : D.IsEqn y g) :
    η ∈ logAt Z (G + D) a y ↔ (g : X.functionField) • η ∈ logAt Z G a y := by
  obtain ⟨e, hG⟩ := G.exists_isEqn y
  have hGD := hG.add hD
  constructor
  · intro h
    refine smul_mem_spanForms_of_mul_mem _ (fun c hc => ?_) h
    change G.RegularAt y _
    change (G + D).RegularAt y c at hc
    rw [hG.regularAt_iff]
    rw [hGD.regularAt_iff, Units.val_mul] at hc
    convert hc using 1
    ring
  · intro h
    have h' := smul_mem_spanForms_of_mul_mem (M' := {c | (G + D).RegularAt y c}) (g : X.functionField)⁻¹
      (fun c hc => ?_) h
    · rwa [inv_smul_smul₀ g.ne_zero] at h'
    · change (G + D).RegularAt y _
      change G.RegularAt y c at hc
      rw [hGD.regularAt_iff, Units.val_mul]
      rw [hG.regularAt_iff] at hc
      convert hc using 1
      field_simp

theorem logtwist : ∀ (X : Scheme.{0}) [IsIntegral X] (Z : Set X) (G D : CartierDiv X) (a : ℕ) (y : X)
    (g : X.functionFieldˣ) (η : abelian₂ X.functionField), D.IsEqn y g →
    (η ∈ logAt Z (G + D) a y ↔ (g : X.functionField) • η ∈ logAt Z G a y) :=
  fun X _ Z G D a y g η hD => mem_logAt_add_iff Z G D a y g η hD

end GlobalTheory.LogDR
end

section

open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory

theorem cartierMap_smul_logWedge : ∀ (K : Type) [Field K] (p : ℕ) (n : ℕ) (x : Fin n → Kˣ) (γ : abelian₂ K →+* abelian₂ K),
    IsCartierMap p x γ → ∀ (c : K) (I : Finset (Fin n)), γ (c • logWedge x I) = c ^ p • logWedge x I := by
  intro K _ p n x γ hγ c I
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, hγ.1]
  congr 1
  unfold logWedge
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact hγ.2 i

end GlobalTheory
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Cartier.Presents

variable {X : Scheme.{0}} [IsIntegral X] {D : CartierDiv X} {L : LB X} {r : L.ι → X.functionFieldˣ}

def genChart (h : Presents D L r) : L.ι := (exists_chart h.isLB (genericPoint X)).choose

theorem gen_mem_genChart (h : Presents D L r) : genericPoint X ∈ L.U h.genChart :=
  (exists_chart h.isLB (genericPoint X)).choose_spec

def secVal (h : Presents D L r) (U : X.Opens) (hU : genericPoint X ∈ U) : Γ(LB.toMod L, U) →+ X.functionField :=
  AddMonoidHom.mk' (fun s => fnOf _ (memInf hU h.gen_mem_genChart) (LB.coord s h.genChart) /
      (r h.genChart : X.functionField)) fun s t => by
    rw [LB.coord_add, map_add (f := _), add_div]

theorem secVal_apply (h : Presents D L r) (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(LB.toMod L, U)) :
    h.secVal U hU s = fnOf _ (memInf hU h.gen_mem_genChart) (LB.coord s h.genChart) /
      (r h.genChart : X.functionField) := rfl

theorem secVal_mul (h : Presents D L r) (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(LB.toMod L, U))
    (i : L.ι) (hi : genericPoint X ∈ U ⊓ L.U i) :
    h.secVal U hU s * r i = fnOf _ hi (LB.coord s i) := by
  have h₀ := h.gen_mem_genChart
  have hW : genericPoint X ∈ U ⊓ L.U i ⊓ L.U h.genChart := ⟨hi, h₀⟩
  have e := congrArg (fnOf _ hW) (LB.coord_rel s i h.genChart
    (inf_le_left : U ⊓ L.U i ⊓ L.U h.genChart ≤ U ⊓ L.U i)
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
    (le_inf (inf_le_left.trans inf_le_right) inf_le_right))
  rw [map_mul, fnOf_resG, fnOf_resG, fnOf_resG] at e
  rw [e, secVal_apply, h.isRatSec i h.genChart (memInf hi.2 h₀), mul_left_comm]
  exact congrArg _ (div_mul_cancel₀ _ (Units.ne_zero _))

theorem secVal_injective (h : Presents D L r) (U : X.Opens) (hU : genericPoint X ∈ U) :
    Function.Injective (h.secVal U hU) := fun s t e =>
  LB.sec_ext fun i => fn_ext fun hi => by rw [← h.secVal_mul U hU s i hi, ← h.secVal_mul U hU t i hi, e]

theorem mem_range_secVal (h : Presents D L r) (U : X.Opens) (hU : genericPoint X ∈ U) (f : X.functionField) :
    f ∈ (h.secVal U hU).range ↔ ∀ y ∈ U, D.RegularAt y f := by
  constructor
  · rintro ⟨s, rfl⟩ y hy
    obtain ⟨i, hi⟩ := exists_chart h.isLB y
    have hyi : y ∈ U ⊓ L.U i := ⟨hy, hi⟩
    refine (h.isEqn i y hi).regularAt_iff.2 ?_
    rw [h.secVal_mul U hU s i (gen_mem hyi)]
    exact regAt_fnOf hyi _ _
  · intro hf
    have key (i : L.ι) : ∃ a : Γ(X, U ⊓ L.U i), ∀ hi, fnOf _ hi a = f * r i := by
      by_cases hi : genericPoint X ∈ U ⊓ L.U i
      · obtain ⟨a, ha⟩ := exists_fnOf_eq hi fun x hx =>
          (h.isEqn i x hx.2).regularAt_iff.1 (hf x hx.1)
        exact ⟨a, fun _ => ha⟩
      · exact ⟨0, fun h' => (hi h').elim⟩
    choose a ha using key
    have hmem : a ∈ secOn L U := fun i j => fn_ext fun hij => by
      rw [map_mul, fnOf_resG, fnOf_resG, fnOf_resG, ha, ha,
        h.isRatSec i j (memInf hij.1.2 hij.2), mul_left_comm]
    refine ⟨LB.mkSec a hmem, ?_⟩
    rw [secVal_apply, LB.coord_mkSec, ha]
    exact mul_div_cancel_right₀ _ (Units.ne_zero _)

def latModel (h : Presents D L r) :
    LatModel (V := X.functionField) (fun y => (D.secOn {y}).toAddSubgroup) (LB.toMod L) where
  val := h.secVal
  inj := h.secVal_injective
  range U hU := by
    ext f
    rw [h.mem_range_secVal U hU f]
    simp only [latSec, AddSubgroup.mem_iInf, Submodule.mem_toAddSubgroup, CartierDiv.mem_secOn,
      Set.mem_singleton_iff, forall_eq]
  res U W e hW s := by
    rw [secVal_apply, secVal_apply, LB.coord_map, fnOf_resG]
  smul U hU a s := by
    rw [secVal_apply, secVal_apply, LB.coord_smul, map_mul, fnOf_resG, smul_eq_mul, mul_div_assoc]

end GlobalTheory.Cartier.Presents

theorem GlobalTheory.Cartier.nonempty_latModel_of_presents : ∀ (X : Scheme.{0}) [IsIntegral X] (D : CartierDiv X) (L : LB X)
    (r : L.ι → X.functionFieldˣ), Presents D L r →
    Nonempty (LatModel (V := X.functionField) (fun y => (D.secOn {y}).toAddSubgroup) (LB.toMod L)) :=
  fun _ _ _ _ _ h => ⟨h.latModel⟩
end
end

section

open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory.LogDR

theorem _root_.GlobalTheory.LogDR.spanForms_eq_bot_of_lt_card : ∀ (K : Type) [Field K] (n : ℕ) (x : Fin n → Kˣ)
    (M : Set K) (H : Set Ω[K⁄ℤ]) (a : ℕ), _root_.GlobalTheory.LogDR.IsCoord x → n < a →
    _root_.GlobalTheory.LogDR.spanForms M H a = ⊥ := by
  intro K _ n x M H a hx hlt
  obtain ⟨hli, hsp⟩ := hx
  let b := Module.Basis.mk hli hsp.ge
  haveI : FiniteDimensional K Ω[K⁄ℤ] := Module.Finite.of_basis b
  have hr : Module.finrank K Ω[K⁄ℤ] = n := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  unfold _root_.GlobalTheory.LogDR.spanForms
  rw [AddSubgroup.closure_eq_bot_iff]
  rintro η ⟨c, -, v, -, rfl⟩
  have hdep : ¬ LinearIndependent K v := fun hv => by
    have := hv.fintype_card_le_finrank
    rw [Fintype.card_fin, hr] at this
    omega
  rw [AlternatingMap.map_linearDependent _ _ hdep, smul_zero]
  rfl

end GlobalTheory.LogDR
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtCoordBasis

open KaehlerDifferential

theorem kaehler_map_bijective (p : ℕ) (L : Type) [CommRing L] [Algebra (ZMod p) L] :
    Function.Bijective (KaehlerDifferential.map ℤ (ZMod p) L L) := by
  refine ⟨?_, KaehlerDifferential.map_surjective ℤ (ZMod p) L⟩
  have hsurj : Function.Surjective (algebraMap ℤ (ZMod p)) := by
    intro x
    obtain ⟨m, rfl⟩ := ZMod.intCast_surjective x
    exact ⟨m, by simp⟩
  have hs : Subsingleton Ω[ZMod p⁄ℤ] := KaehlerDifferential.subsingleton_of_surjective ℤ (ZMod p) hsurj
  have hex := KaehlerDifferential.exact_mapBaseChange_map ℤ (ZMod p) L
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := (hex x).1 hx
  clear hx
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [Subsingleton.elim b 0]
  | add y z hy hz => rw [map_add (f := _), hy, hz, add_zero]

theorem etale_coords_basis : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [IsDomain A] [Algebra (ZMod p) A] {n : ℕ} (t : Fin n → A), (MvPolynomial.aeval (R := ZMod p) t).toRingHom.Etale → ∀ (L : Type) [Field L] [Algebra A L] [IsFractionRing A L] (ht : ∀ j, algebraMap A L (t j) ≠ 0), IsCoord (fun j => Units.mk0 (algebraMap A L (t j)) (ht j)) ∧ ∀ f : A, ∃ c : Fin n → A, KaehlerDifferential.D ℤ L (algebraMap A L f) = ∑ j, algebraMap A L (c j) • KaehlerDifferential.D ℤ L (algebraMap A L (t j)) := by
  intro p _ A _ _ _ n t het L _ _ _ ht
  classical
  let P := MvPolynomial (Fin n) (ZMod p)
  letI : Algebra P A := (MvPolynomial.aeval t).toRingHom.toAlgebra
  haveI : IsScalarTower (ZMod p) P A :=
    .of_algebraMap_eq fun r => ((MvPolynomial.aeval t).commutes r).symm
  haveI : Algebra.Etale P A := het
  letI : Algebra (ZMod p) L := ((algebraMap A L).comp (algebraMap (ZMod p) A)).toAlgebra
  haveI : IsScalarTower (ZMod p) A L := .of_algebraMap_eq fun _ => rfl
  haveI : Algebra.FormallyEtale A L := .of_isLocalization (nonZeroDivisors A)
  let bA : Module.Basis (Fin n) A Ω[A⁄ZMod p] :=
    ((mvPolynomialBasis (ZMod p) (Fin n)).baseChange A).map
      (tensorKaehlerEquivOfFormallyEtale (ZMod p) P A)
  have hbA : ∀ j, bA j = D (ZMod p) A (t j) := by
    intro j
    simp only [bA, Module.Basis.map_apply, Module.Basis.baseChange_apply,
      tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul, one_smul, mvPolynomialBasis_apply, map_D]
    have h : algebraMap P A (MvPolynomial.X j) = t j := by
      change MvPolynomial.aeval t (MvPolynomial.X j) = t j
      exact MvPolynomial.aeval_X t j
    rw [← h, ← map_D (ZMod p) (ZMod p) P A]
    exact (mapBaseChange_tmul (ZMod p) P A 1 _).trans (one_smul _ _)
  let bL : Module.Basis (Fin n) L Ω[L⁄ZMod p] :=
    (bA.baseChange L).map (tensorKaehlerEquivOfFormallyEtale (ZMod p) A L)
  have hbL : ∀ j, bL j = D (ZMod p) L (algebraMap A L (t j)) := by
    intro j
    simp only [bL, Module.Basis.map_apply, Module.Basis.baseChange_apply,
      tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul, one_smul, hbA, map_D]
  let e : Ω[L⁄ℤ] ≃ₗ[L] Ω[L⁄ZMod p] :=
    LinearEquiv.ofBijective (KaehlerDifferential.map ℤ (ZMod p) L L) (kaehler_map_bijective p L)
  have he : ∀ x : L, e.symm (D (ZMod p) L x) = D ℤ L x := by
    intro x
    rw [LinearEquiv.symm_apply_eq]
    exact (KaehlerDifferential.map_D ℤ (ZMod p) L L x).symm
  let b : Module.Basis (Fin n) L Ω[L⁄ℤ] := bL.map e.symm
  have hb : ∀ j, b j = D ℤ L (algebraMap A L (t j)) := by
    intro j
    simp only [b, Module.Basis.map_apply, hbL, he]
  have hfun : (fun i => dK ((Units.mk0 (algebraMap A L (t i)) (ht i) : Lˣ) : L)) = ⇑b := by
    funext i
    simp [hb, dK]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hfun]; exact b.linearIndependent
  · rw [hfun]; exact b.span_eq
  · intro f
    refine ⟨bA.repr (D (ZMod p) A f), ?_⟩
    have h1 := bA.sum_repr (D (ZMod p) A f)
    rw [← he, ← map_D (ZMod p) (ZMod p) A L]
    conv_lhs => rw [← h1]

    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.map_smul, hbA, map_D, ← algebraMap_smul L (bA.repr (D (ZMod p) A f) j), LinearEquiv.map_smul, he]

end GlobalTheory.EtCoordBasis
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DI


open CategoryTheory AlgebraicGeometry TopologicalSpace in
theorem _root_.GlobalTheory.DI.pow_mul_locRing_subset_regularAt {X : Scheme.{0}} [IsIntegral X] (p : ℕ)
    (G H : _root_.GlobalTheory.Cartier.CartierDiv X) (y : X) (h : (H - p • G).Eff) :
    {z : X.functionField | ∃ c ∈ {c : X.functionField | G.RegularAt y c},
      ∃ b ∈ _root_.GlobalTheory.LogDR.locRing y, z = c ^ p * b} ⊆
      {c | H.RegularAt y c} := by
  rintro z ⟨c, ⟨g, hg, hcg⟩, b, hb, rfl⟩
  obtain ⟨k, hk, hk1⟩ := h y
  have hH : H.IsEqn y (k * g ^ p) := by
    have := hk.add (hg.nsmul p)
    simpa using this
  refine ⟨k * g ^ p, hH, ?_⟩
  rw [← _root_.GlobalTheory.LogDR.mem_locRing] at hcg hk1 ⊢
  have hz : c ^ p * b * ((k * g ^ p : (X.functionField)ˣ) : X.functionField) =
      (c * g) ^ p * b * (1 * k) := by
    push_cast
    ring
  rw [hz]
  exact mul_mem (mul_mem (pow_mem hcg p) hb) hk1

end GlobalTheory.DI
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ConjSeq

theorem sec_exists_pow_of_D_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (X : Scheme.{0}) [IsIntegral X] (s : X ⟶ Sp k) [Smooth s] (U : X.affineOpens) (u : GlobalTheory.CechDR.Sec s U.1), KaehlerDifferential.D k (GlobalTheory.CechDR.Sec s U.1) u = 0 → ∃ h : GlobalTheory.CechDR.Sec s U.1, h ^ p = u := by
  intro p _ k _ _ hk X _ s _ U u hu
  haveI hsm : Algebra.Smooth k (GlobalTheory.CechDR.Sec s U.1) := by
    haveI : IsOpenImmersion (GlobalTheory.CechDR.affPt s U) := IsAffineOpen.isOpenImmersion_fromSpec U.2
    have h : Smooth (GlobalTheory.CechDR.affPt s U ≫ s) := inferInstance
    rw [GlobalTheory.CechDR.affPt_w] at h
    exact RingHom.smooth_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @Smooth)).1 h)
  by_cases hU : Nonempty U.1
  · haveI : IsDomain (GlobalTheory.CechDR.Sec s U.1) := IsIntegral.component_integral (X := X) U.1
    exact GlobalTheory.T.exists_pow_eq_of_kaehler_D_eq_zero_of_smooth_domain p k hk _ u hu
  · have e : U.1 = ⊥ := by
      ext x
      exact ⟨fun hx ↦ hU ⟨⟨x, hx⟩⟩, fun hx ↦ hx.elim⟩
    have hs : Subsingleton Γ(X, U.1) := by rw [e]; infer_instance
    haveI : Subsingleton (GlobalTheory.CechDR.Sec s U.1) := hs
    exact ⟨u, Subsingleton.elim _ _⟩

end GlobalTheory.ConjSeq
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.Cartier
open scoped ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CurveDens

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

theorem transDet_trans_chart (c c' c'' : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source)
    (hy' : y ∈ c'.e.source) (hy'' : y ∈ c''.e.source) :
    ChartGlue.transDet c.e c''.e y =
      ChartGlue.transDet c.e c'.e y * ChartGlue.transDet c'.e c''.e y := by
  have ho := ChartGlue.isOpen_over c.e (c'.e.open_source.inter c''.e.open_source)
  have hm : c.e y ∈ c.e.target ∩ c.e.symm ⁻¹' (c'.e.source ∩ c''.e.source) :=
    ChartGlue.mem_over c.e hy ⟨hy', hy''⟩
  have e : c''.e ∘ c.e.symm =ᶠ[𝓝 (c.e y)] (c''.e ∘ c'.e.symm) ∘ (c'.e ∘ c.e.symm) :=
    eventually_of_mem (ho.mem_nhds hm) fun w hw => by
      simp only [Function.comp_apply, c'.e.left_inv hw.2.1]
  have hf : DifferentiableAt ℂ (c'.e ∘ c.e.symm) (c.e y) :=
    (c.holo_trans c').differentiableAt
      ((ChartGlue.isOpen_over c.e c'.e.open_source).mem_nhds (ChartGlue.mem_over c.e hy hy'))
  have hfy : (c'.e ∘ c.e.symm) (c.e y) = c'.e y := by simp [c.e.left_inv hy]
  have hg : DifferentiableAt ℂ (c''.e ∘ c'.e.symm) ((c'.e ∘ c.e.symm) (c.e y)) := by
    rw [hfy]
    exact (c'.holo_trans c'').differentiableAt
      ((ChartGlue.isOpen_over c'.e c''.e.open_source).mem_nhds (ChartGlue.mem_over c'.e hy' hy''))
  rw [ChartGlue.transDet, e.fderiv_eq, fderiv_comp _ hg hf, hfy, ChartGlue.transDet,
    ChartGlue.transDet]
  simp only [ContinuousLinearMap.det]
  exact (LinearMap.det_comp _ _).trans (mul_comm _ _)

theorem transDet_chart_ne_zero (c c' : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source)
    (hy' : y ∈ c'.e.source) : ChartGlue.transDet c.e c'.e y ≠ 0 := by
  intro h
  have := transDet_trans_chart c c' c hy hy' hy
  rw [c.transDet_self hy, h, zero_mul] at this
  exact one_ne_zero this

theorem continuousAt_transDet_chart (c c' : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source)
    (hy' : y ∈ c'.e.source) : ContinuousAt (ChartGlue.transDet c.e c'.e) y := by
  have hW : y ∈ ptsIn p σ (c.U ⊓ c'.U) :=
    mem_ptsIn_inf.2 ⟨c.source_subset hy, c'.source_subset hy'⟩
  have h1 : ContinuousAt (ev p σ _ (c.isFrame.ratio c'.isFrame).val) y :=
    (continuousOn_ev _).continuousAt ((isOpen_ptsIn _).mem_nhds hW)
  refine h1.congr ?_
  filter_upwards [(c.e.open_source.inter c'.e.open_source).mem_nhds ⟨hy, hy'⟩] with z hz
  exact c.ev_ratio c' hz.1 hz.2

end GlobalTheory.CurveDens
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Indef.Tree NumberField GlobalTheory.MeanTop

theorem _root_.GlobalTheory.T.weight_division_l1_bound : ∀ (ι : Type) [Fintype ι] (N : ℕ) (W : Wts ι N), W.Hyp → W.IsDiv → (W.T : ℝ) * l1 W.u1 ≤ l1 W.u + (Fintype.card ι : ℝ) * N * (W.c0 + 4 * N) ∧ l1 W.u' ≤ l1 W.u1 ∧ ∀ τ i, |W.u' τ i| ≤ |W.u1 τ i| := by
  first | exact @GlobalTheory.MeanTop.divided_weight_size | exact GlobalTheory.MeanTop.divided_weight_size | (intros; apply GlobalTheory.MeanTop.divided_weight_size <;> assumption)
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.exists_coboundary_of_pullback_nmul_coboundary : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Katz.Chart G d) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), c.IsLawOf μ → ∀ (κ : MvPowerSeries (Fin d ⊕ Fin d) k) (B : MvPowerSeries (Fin d) k), IsCoc μ κ → cob1 μ B = pull2 (nmul μ p) κ → c.ev 1 B = 0 → ∃ s, κ = cob1 μ s := by
  first | exact @GlobalTheory.Katz.exists_coboundary_of_pullback_nmul_coboundary' | exact GlobalTheory.Katz.exists_coboundary_of_pullback_nmul_coboundary' | (intros; apply GlobalTheory.Katz.exists_coboundary_of_pullback_nmul_coboundary' <;> assumption)
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.rigidifiedExtension_presentation_natural_semilinear : ∀ (p : ℕ) (k k' : Type) [CommRing k] [CommRing k'] (σ : k →+* k') (d e : ℕ) (G : PDivGroup p k) (G' : PDivGroup p k') (c : Chart G d) (c' : Chart G' e) (s : SemiHom σ G' G) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (φ : Fin d → MvPowerSeries (Fin e) k') (ρ : MvPowerSeries (Fin d ⊕ Fin d) k × (Fin d → k) →ₗ[k] ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))) (ρ' : MvPowerSeries (Fin e ⊕ Fin e) k' × (Fin e → k') →ₗ[k'] ((G'.cocycles × G'.omega) ⧸ _root_.LinearMap.range (G'.cob.prod (_root_.LinearMap.codRestrict G'.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G'.A i))).domRestrict G'.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))), c.IsLawOf μ → (∀ n j, c'.ev n (φ j) = s.app n (c.x n j)) → (∀ t w (z : G.cocycles) (u : G.omega), (∀ n, z.1 n = c.ev₂ n t) → (∀ n, u.1 n = ∑ i, w i • dUnit (R := k) (c.x n i)) → ρ (t, w) = G.rigMk (z, u)) → (∀ t w (z : G'.cocycles) (u : G'.omega), (∀ n, z.1 n = c'.ev₂ n t) → (∀ n, u.1 n = ∑ i, w i • dUnit (R := k') (c'.x n i)) → ρ' (t, w) = G'.rigMk (z, u)) → ∀ t w, IsCoc μ t → ρ' (pull2 φ (MvPowerSeries.map σ t), pullLin φ (fun i => σ (w i))) = s.rig (ρ (t, w)) := by
  first | (exact @GlobalTheory.Katz.rig_pull_natural_semi) | (exact GlobalTheory.Katz.rig_pull_natural_semi) | (intros; apply GlobalTheory.Katz.rig_pull_natural_semi  <;> assumption)
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.exists_quasiLog_red_coboundary_and_linear : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (h : IsLaw μ), ∀ c, IsCoc μ c → ∀ w : Fin d → k, ∃ f ∈ quasiLog p h, Red p (cob1 (fun i => Katz.lift p (μ i)) f) c ∧ RedV p (lin f) w := by
  first | exact @GlobalTheory.Katz.exists_quasiLog_red | exact GlobalTheory.Katz.exists_quasiLog_red | (intros; apply GlobalTheory.Katz.exists_quasiLog_red <;> assumption)
end

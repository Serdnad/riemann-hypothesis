module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.PsiWeightZeroLinearCombination
public import Aesop.BuiltinRules
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EqZeroOfSemicharacterMultiplier
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.Inh ReciprocityTheory.ChartRestriction.G.Out.InhTate ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.ToricData

variable {K : Type} [CommRing K] [IsDomain K] {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
variable (q : X → (FractionRing K)ˣ) (F : Type) [Field F] [Algebra (FractionRing K) F]


omit [Module.Free ℤ X] [Module.Finite ℤ X] in
theorem hom_eq_iff {F : Type} [Field F] {t t' : Multiplicative X →* Fˣ} :
    (∀ χ : X, t (Multiplicative.ofAdd χ) = t' (Multiplicative.ofAdd χ)) ↔ t = t' :=
  ⟨fun h => MonoidHom.ext fun χ => h χ.toAdd, fun h _ => h ▸ rfl⟩

theorem isZero_pt (t) : (pt q F t).IsZero ↔ t = 1 :=
  (and_iff_right rfl).trans ((forall_congr' fun (χ : X) =>
    (corr_iff_eq (pt_isConst q F t χ) ((isConst_oneGen _).of_eq unitOn_one.symm)).trans unitOn_inj).trans
    (hom_eq_iff (t' := 1)))

theorem isAdd_pt (t t' t'') : (pt q F t).IsAdd (pt q F t') (pt q F t'') ↔ t'' = t * t' :=
  (and_iff_right (toUnit_unique _ _)).trans ((forall_congr' fun (χ : X) =>
    (corr_iff_eq
      ((isConst_mulGen (pt_isConst q F t'' χ) (cubAt_isConst q F _ _ _)).of_eq (_root_.mul_one _))
      ((isConst_mulGen (pt_isConst q F t χ) (pt_isConst q F t' χ)).of_eq (unitOn_mul _ _).symm)).trans
      unitOn_inj).trans (hom_eq_iff (t' := t * t')))

theorem isNsmul_pt (n : ℕ) (t t') : GtPtF.IsNsmul n (pt q F t) (pt q F t') ↔ t' = t ^ n := by
  constructor
  · rintro ⟨gs, h0, hs, hl⟩
    choose u hu using fun i => (pt_bijective q F).2 (gs i)
    have key : ∀ i : Fin (n + 1), u i = t ^ (i : ℕ) := by
      intro i
      induction i using Fin.induction with
      | zero =>
        rw [← hu] at h0
        exact ((isZero_pt q F _).1 h0).trans (pow_zero t).symm
      | succ i ih =>
        have h := hs i
        rw [← hu, ← hu, isAdd_pt] at h
        rw [h, ih, Fin.val_succ, pow_succ]
        rfl
    rw [← hu] at hl
    exact ((pt_bijective q F).1 hl).symm.trans (key _)
  · rintro rfl
    exact ⟨fun i => pt q F (t ^ (i : ℕ)), (isZero_pt q F _).2 (pow_zero t),
      fun i => (isAdd_pt q F _ _ _).2 (pow_succ t i), rfl⟩

theorem isIota_pt (y : X) (t) : GtPtF.IsIota (D := toricPre K X q) y (pt q F t) ↔
    ∀ χ, (t (Multiplicative.ofAdd χ) : F) = algebraMap (FractionRing K) F (polar q y χ) :=
  (and_iff_right (toUnit_unique _ _)).trans (forall_congr' fun (χ : X) =>
    (corr_iff_eq (pt_isConst q F t χ)
      ((isConst_pullGen (tau_isConst q y χ) (jFK (R := K) F)).of_eq (pullTop_unitOn _ _))).trans
      (unitOn_inj.trans Units.ext_iff))

theorem gtAct_pt (O : Type) [CommRing O] [StarRing O] [Module O X] (h) (a : O) (t t') :
    GtAct (toricOAct q O h) a (pt q F t) (pt q F t') ↔
      ∀ χ : X, t' (Multiplicative.ofAdd χ) = t (Multiplicative.ofAdd (star a • χ)) := by
  refine (and_iff_right (toUnit_unique _ _)).trans ⟨fun H χ => ?_, fun H u _ hu (χ : X) => ?_⟩
  · have hc := H (cg _ _ 1) (cg_isGen _ _ 1)
      (corr_of_isConst ((isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _)) (isConst_oneGen _)) χ
    have e := eq_of_corr
      (isConst_mulGen (pt_isConst q F t (star a • χ)) ((isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _)))
      (pt_isConst q F t' χ) hc
    exact (unitOn_inj.1 ((_root_.mul_one _).symm.trans e)).symm
  · exact corr_of_isConst
      ((isConst_mulGen (pt_isConst q F t (star a • χ))
        ((isConst_pullGen (isConst_one_of_zero2 q u hu) _).of_eq (map_one _))).of_eq
        ((_root_.mul_one _).trans (congrArg unitOn (H χ).symm)))
      (pt_isConst q F t' χ)

theorem zeroF_left_ext {F' : Type} [Field F'] [Algebra (FractionRing K) F'] (f : F →+* F')
    (hf : f.comp (algebraMap (FractionRing K) F) = algebraMap (FractionRing K) F') :
    (DegPre.zeroF (toricPre K X q) F').left = spMap f ≫ (DegPre.zeroF (toricPre K X q) F).left := by
  have w : spMap f ≫ (TF (R := K) F).hom = (TF (R := K) F').hom := by
    change spMap f ≫ jFK (R := K) F ≫ jK K = jFK (R := K) F' ≫ jK K
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hf]
  let φ : TF (R := K) F' ⟶ TF (R := K) F := Over.homMk (spMap f) w
  have e : DegPre.zeroF (toricPre K X q) F' = φ ≫ DegPre.zeroF (toricPre K X q) F := toUnit_unique _ _
  rw [e]
  rfl

theorem qkExt_pt {F' : Type} [Field F'] [Algebra (FractionRing K) F'] (f : F →+* F')
    (hf : f.comp (algebraMap (FractionRing K) F) = algebraMap (FractionRing K) F') {n : ℕ}
    (p : QkPt (toricPre K X q) F n) (p' : QkPt (toricPre K X q) F' n) (t t') (hp : p.g = pt q F t)
    (hp' : p'.g = pt q F' t') :
    QkExt f p p' ↔ p'.y = p.y ∧ ∀ χ, (t' χ : F') = f (t χ) := by
  obtain ⟨y, g, e⟩ := p
  obtain ⟨y', g', e'⟩ := p'
  dsimp only at hp hp'
  subst hp hp'
  refine and_congr_right' ((and_iff_right (zeroF_left_ext q F f hf)).trans ?_)
  refine (forall_congr' fun (χ : X) => (corr_iff_eq (pt_isConst q F' t' χ)
      ((isConst_pullGen (pt_isConst q F t χ) (spMap f)).of_eq (pullTop_unitOn _ _))).trans
      (unitOn_inj.trans Units.ext_iff)).trans ?_
  exact ⟨fun H χ => H χ.toAdd, fun H χ => H _⟩

end GlobalTheory.ToricData
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.Inh ReciprocityTheory.ChartRestriction.G.Out.InhTate ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.ToricData

section Sections

variable {Z Y : Scheme.{0}} {J J₁ J₂ J₃ : Type} [Fintype J] [Fintype J₁] [Fintype J₂] [Fintype J₃]

def secVal {φ : J → (Y ⟶ Z)} {ε : J → ℤ} (s : LB.Sec (LB.LinComb (Inh.trivLB Z) φ ε)) : Γ(Y, ⊤) :=
  (Y.presheaf.map (homOfLE (wchart_triv φ (fun _ => PUnit.unit)).ge).op).hom (s.f (fun _ => PUnit.unit))

theorem map_self {U : Y.Opens} (h : U ≤ U) (x : Γ(Y, U)) : (Y.presheaf.map (homOfLE h).op).hom x = x := by
  rw [Subsingleton.elim (homOfLE h) (𝟙 U), op_id, CategoryTheory.Functor.map_id]
  rfl

theorem sec_f_eq {φ : J → (Y ⟶ Z)} {ε : J → ℤ} (s : LB.Sec (LB.LinComb (Inh.trivLB Z) φ ε))
    (j : J → (Inh.trivLB Z).ι) :
    s.f j = (Y.presheaf.map (homOfLE le_top).op).hom (secVal s) := by
  obtain rfl : j = fun _ => PUnit.unit := rfl
  exact ((map_map _ _ _).trans (map_self _ _)).symm

theorem map_top_inj {V : Y.Opens} (hV : V = ⊤) {a b : Γ(Y, ⊤)}
    (h : (Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom a = (Y.presheaf.map (homOfLE le_top).op).hom b) :
    a = b := by
  subst hV
  rwa [map_self, map_self] at h

theorem secVal_of_secRel {φ₁ : J₁ → (Y ⟶ Z)} {ε₁ : J₁ → ℤ} {s₁ : LB.Sec (LB.LinComb (Inh.trivLB Z) φ₁ ε₁)}
    {φ₂ : J₂ → (Y ⟶ Z)} {ε₂ : J₂ → ℤ} {s₂ : LB.Sec (LB.LinComb (Inh.trivLB Z) φ₂ ε₂)} {h : Y ⟶ Y}
    (hh : h = 𝟙 Y) {φ₃ : J₃ → (Y ⟶ Z)} {ε₃ : J₃ → ℤ} {u : LB.Gen (LB.LinComb (Inh.trivLB Z) φ₃ ε₃)}
    {a : Γ(Y, ⊤)ˣ} (hu : IsConst u a)
    (H : GeneratorPullback.SecRel (Inh.trivLB Z) φ₁ ε₁ s₁ φ₂ ε₂ s₂ h φ₃ ε₃ u) : secVal s₁ = secVal s₂ * a := by
  have := H (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ _ _ => rfl)
  subst hh
  refine map_top_inj (top_unique (le_inf (le_inf (wchart_triv φ₁ _).ge (wchart_triv _ _).ge)
    (wchart_triv φ₃ _).ge)) (Eq.trans ?_ (this.trans ?_))
  · exact (map_map _ _ _).symm.trans (congrArg _ (sec_f_eq s₁ _).symm)
  · rw [map_mul]
    refine congrArg₂ (· * ·) ?_ ?_
    · exact (congrArg _ (congrArg _ (sec_f_eq s₂ _))).trans (app_res _ _ _ _ _)
    · exact (congrArg _ (congrArg Units.val (hu _))).trans (map_map _ _ _)

end Sections

variable {K : Type} [CommRing K] [IsDomain K] {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
variable (q : X → (FractionRing K)ˣ)
variable (F : Type) [Field F] [Algebra (FractionRing K) F]

theorem trPt_eq_id (b : TF (R := K) F ⟶ (toricPre K X q).P.A) :
    DegPre.trPt (toricPre K X q) F b = 𝟙 _ :=
  CartesianMonoidalCategory.hom_ext _ _ ((lift_fst _ _).trans (Category.id_comp _).symm) (toUnit_unique _ _)

def constUnit : Fˣ →* Γ((DegPre.BF (toricPre K X q) F).left, ⊤)ˣ :=
  (pullTop (fst (TF (R := K) F) (toricPre K X q).P.A).left).comp
    (Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom.toMonoidHom)

theorem pullTop_zF_constUnit (c : Fˣ) :
    pullTop (DegPre.zF (toricPre K X q) F).left (constUnit q F c) = unitOn c := by
  have h : (DegPre.zF (toricPre K X q) F).left ≫ (fst (TF (R := K) F) (toricPre K X q).P.A).left = 𝟙 _ := by
    rw [← Over.comp_left, DegPre.zF, lift_fst, Over.id_left]
  ext
  change ((DegPre.zF (toricPre K X q) F).left ≫ (fst (TF (R := K) F) (toricPre K X q).P.A).left).appTop.hom
    (unitOn c).val = _
  rw [h]
  rfl

theorem secVal_of_phiRel {n : ℕ} (p : QkPt (toricPre K X q) F n) (t : Multiplicative X →* Fˣ)
    (hp : p.g = pt q F t)
    (w : LB.Gen (LB.LinComb (toricPre K X q).P.L (DegPre.lineφ _ F p.g.b) (DegPre.lineε n))) (c : Fˣ)
    (hw : IsConst w (unitOn c)) {s s' : Fam (toricPre K X q) F n} (h : PhiRel _ F n p w s s') (α β : X)
    (hβ : β = α + (show X from p.y)) :
    secVal (s'.s β) = secVal (s.s α) * (constUnit q F (t (Multiplicative.ofAdd α) * c)).val := by
  subst hβ
  have hg : IsConst (p.g.s α) (unitOn (t (Multiplicative.ofAdd α))) := by
    rw [hp]
    exact pt_isConst q F t α
  refine secVal_of_secRel (congrArg CommaMorphism.left (trPt_eq_id q F p.g.b)) (cg_isConst _ _ _)
    (h α (cg _ _ (constUnit q F (t (Multiplicative.ofAdd α) * c))) (cg_isGen _ _ _) ?_)
  exact corr_of_isConst
    ((isConst_pullGen (cg_isConst _ _ _) _).of_eq ((pullTop_zF_constUnit q F _).trans (unitOn_mul _ _)))
    (isConst_mulGen hg hw)

theorem weilQkIs_pt {n : ℕ} (p p' : QkPt (toricPre K X q) F n) (t t') (hp : p.g = pt q F t) (hp' : p'.g = pt q F t') :
    WeilQkIs (toricPre K X q) F n p p'
      ((t (Multiplicative.ofAdd (show X from p'.y)) * (t' (Multiplicative.ofAdd (show X from p.y)))⁻¹ : Fˣ) : F) := by
  intro w w' _ _ s s₁ s₂ s₃ s₄ h₁ h₂ h₃ h₄ β j
  obtain ⟨a, ha⟩ := exists_isConst w
  obtain ⟨c, rfl⟩ := unitOn_bijective.2 a
  obtain ⟨a', ha'⟩ := exists_isConst w'
  obtain ⟨c', rfl⟩ := unitOn_bijective.2 a'
  change X at β
  let y : X := p.y
  let y' : X := p'.y
  have e₁ := secVal_of_phiRel q F p' t' hp' w' c' ha' h₁ (β - y - y') (β - y - y' + y') rfl
  have e₂ := secVal_of_phiRel q F p t hp w c ha h₂ (β - y - y' + y') β (show β = β - y - y' + y' + y by abel)
  have e₃ := secVal_of_phiRel q F p t hp w c ha h₃ (β - y - y') (β - y - y' + y) rfl
  have e₄ := secVal_of_phiRel q F p' t' hp' w' c' ha' h₄ (β - y - y' + y) β (show β = β - y - y' + y + y' by abel)
  have e : secVal (s₂.s β) = (constUnit q F (t (Multiplicative.ofAdd y') * (t' (Multiplicative.ofAdd y))⁻¹)).val *
      secVal (s₄.s β) := by
    rw [e₂, e₄, e₁, e₃, _root_.mul_assoc, _root_.mul_assoc, mul_left_comm (Units.val _), ← Units.val_mul, ← Units.val_mul,
      ← Units.val_mul, ← map_mul, ← map_mul, ← map_mul]
    congr 3
    simp only [ofAdd_add, map_mul]
    generalize t (Multiplicative.ofAdd (β - y - y')) = A
    generalize t' (Multiplicative.ofAdd (β - y - y')) = B
    generalize t (Multiplicative.ofAdd y') = C
    generalize t' (Multiplicative.ofAdd y) = D
    ext
    push_cast
    field_simp
  refine (sec_f_eq (s₂.s β) j).trans ?_
  rw [e, map_mul, sec_f_eq (s₄.s β) j]
  rfl

end GlobalTheory.ToricData
end
end

section

noncomputable section

open Matrix ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ThetaBlock

variable {g : ℕ} {S : Finset (Fin g)}

def offEquiv (S : Finset (Fin g)) : {n : Fin g → ℤ // ∀ k ∈ S, n k = 0} ≃ ({k // k ∉ S} → ℤ) where
  toFun n i := n.1 i
  invFun l := ⟨fun k => if h : k ∈ S then 0 else l ⟨k, h⟩, fun k hk => dif_pos hk⟩
  left_inv n := by
    refine Subtype.ext (funext fun k => ?_)
    by_cases h : k ∈ S
    · simp [h, n.2 k h]
    · simp [h]
  right_inv l := by
    funext i
    simp [i.2]

open Matrix in
variable {g : ℕ} {S : Finset (Fin g)} in
private theorem submatrix_mem_siegelH_of_posDef_im (S : Finset (Fin g)) {τ : Matrix (Fin g) (Fin g) ℂ}
    (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef) :
    τ.submatrix (Subtype.val : {k // k ∉ S} → Fin g) Subtype.val ∈ _root_.ReciprocityTheory.PTheta.SiegelH {k // k ∉ S} := by
  unfold _root_.ReciprocityTheory.PTheta.SiegelH
  exact ⟨hs.submatrix _, hp.submatrix Subtype.val_injective⟩

open Matrix in
variable {g : ℕ} {S : Finset (Fin g)} in
private theorem ofReal_re_eq_self_of_eq_zero_or_half {c : ℂ} (h : c = 0 ∨ c = 1 / 2) :
    ((c.re : ℝ) : ℂ) = c := by
  rcases h with rfl | rfl
  · simp
  · apply Complex.ext <;> simp

open Matrix in
variable {g : ℕ} {S : Finset (Fin g)} in
private theorem dotProduct_eq_restrict_of_vanishing (S : Finset (Fin g)) {v : Fin g → ℂ}
    (hv : ∀ k ∈ S, v k = 0) (w : Fin g → ℂ) :
    v ⬝ᵥ w = (fun i : {k // k ∉ S} => v i) ⬝ᵥ (fun i : {k // k ∉ S} => w i) := by
  unfold dotProduct
  rw [← Fintype.sum_subtype_add_sum_subtype (fun k => k ∉ S)]
  have h0 : ∑ i : {k // ¬ k ∉ S}, v i * w i = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [hv i (not_not.1 i.2), zero_mul]
  rw [h0, add_zero]

open Matrix in
variable {g : ℕ} {S : Finset (Fin g)} in
private theorem mulVec_restrict_eq_submatrix_mulVec_of_vanishing (S : Finset (Fin g)) (τ : Matrix (Fin g) (Fin g) ℂ)
    {v : Fin g → ℂ} (hv : ∀ k ∈ S, v k = 0) :
    (fun i : {k // k ∉ S} => (τ *ᵥ v) i) =
      τ.submatrix Subtype.val Subtype.val *ᵥ (fun i : {k // k ∉ S} => v i) := by
  funext i
  simp only [mulVec, submatrix_apply]
  rw [dotProduct_comm, dotProduct_eq_restrict_of_vanishing S hv, dotProduct_comm]

open Matrix in
variable {g : ℕ} {S : Finset (Fin g)} in
private theorem thetaCharOff_eq_theta_submatrix (S : Finset (Fin g)) (τ : Matrix (Fin g) (Fin g) ℂ)
    (c₁ c₂ : Fin g → ℂ) (h₁ : ∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) (h₂ : ∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2)
    (hS : ∀ k ∈ S, c₁ k = 0) (z : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaCharOff S τ c₁ c₂ z = _root_.ReciprocityTheory.PTheta.theta (fun i : {k // k ∉ S} => (c₁ i).re)
      (fun i : {k // k ∉ S} => (c₂ i).re) (fun i : {k // k ∉ S} => z i)
      (τ.submatrix Subtype.val Subtype.val) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaCharOff _root_.ReciprocityTheory.PTheta.theta _root_.ReciprocityTheory.PTheta.thetaTerm _root_.ReciprocityTheory.PTheta.eC _root_.ReciprocityTheory.PTheta.shiftVec _root_.ReciprocityTheory.PTheta.ofRealVec
  rw [← (_root_.GlobalTheory.ThetaBlock.offEquiv S).tsum_eq]
  congr 1
  funext n
  have hv : ∀ k ∈ S, ((fun i => ((n.1 i : ℤ) : ℂ)) + c₁) k = 0 := fun k hk => by
    simp [n.2 k hk, hS k hk]
  have hw : (fun i : {k // k ∉ S} =>
      (((_root_.GlobalTheory.ThetaBlock.offEquiv S n) i : ℤ) : ℂ) + (((c₁ i).re : ℝ) : ℂ)) =
      fun i : {k // k ∉ S} => ((fun i => ((n.1 i : ℤ) : ℂ)) + c₁) i := by
    funext i
    rw [ofReal_re_eq_self_of_eq_zero_or_half (h₁ i)]
    rfl
  have hz : (fun i : {k // k ∉ S} => z i) + (fun i : {k // k ∉ S} => (((c₂ i).re : ℝ) : ℂ)) =
      fun i : {k // k ∉ S} => (z + c₂) i := by
    funext i
    simp [ofReal_re_eq_self_of_eq_zero_or_half (h₂ i)]
  rw [hw, hz, dotProduct_eq_restrict_of_vanishing S hv (τ *ᵥ _), mulVec_restrict_eq_submatrix_mulVec_of_vanishing S τ hv,
    dotProduct_eq_restrict_of_vanishing S hv (z + c₂)]
  congr 1
  ring


open Matrix in
variable {g : ℕ} {S : Finset (Fin g)} in
theorem _root_.GlobalTheory.ThetaBlock.thetaCharOff_ne_zero_differentiable_quasiPeriodic (g : ℕ) (S : Finset (Fin g))
    (τ : Matrix (Fin g) (Fin g) ℂ) (c₁ c₂ : Fin g → ℂ) (hs : τ.IsSymm)
    (hp : (τ.map Complex.im).PosDef) (h₁ : ∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2)
    (h₂ : ∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) (hS : ∀ k ∈ S, c₁ k = 0) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaCharOff S τ c₁ c₂ ≠ 0 ∧ Differentiable ℂ (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaCharOff S τ c₁ c₂) ∧
      ∀ m n : Fin g → ℤ, (∀ k ∈ S, n k = 0) → ∃ a : ℂ, a ≠ 0 ∧ ∀ z,
        _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaCharOff S τ c₁ c₂ (z + ((fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)))) =
          a * Complex.exp (-(2 * Real.pi * Complex.I) * ((fun i => (n i : ℂ)) ⬝ᵥ z)) *
            _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaCharOff S τ c₁ c₂ z := by
  have hτ := submatrix_mem_siegelH_of_posDef_im S hs hp
  have hfun : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaCharOff S τ c₁ c₂ = fun z => _root_.ReciprocityTheory.PTheta.theta (fun i : {k // k ∉ S} => (c₁ i).re)
      (fun i : {k // k ∉ S} => (c₂ i).re) (fun i : {k // k ∉ S} => z i)
      (τ.submatrix Subtype.val Subtype.val) :=
    funext (thetaCharOff_eq_theta_submatrix S τ c₁ c₂ h₁ h₂ hS)
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    obtain ⟨w, hw⟩ := Function.ne_iff.1
      (_root_.GlobalTheory.theta_ne_zero hτ (fun i : {k // k ∉ S} => (c₁ i).re)
        (fun i : {k // k ∉ S} => (c₂ i).re))
    apply hw
    have h := congrFun h0 (fun k => if h : k ∈ S then 0 else w ⟨k, h⟩)
    rw [hfun] at h
    have hr : (fun i : {k // k ∉ S} => (fun k => if h : k ∈ S then 0 else w ⟨k, h⟩) i.1) = w := by
      funext i
      simp [i.2]
    simp only [Pi.zero_apply] at h
    rwa [hr] at h
  · rw [hfun]
    exact (_root_.GlobalTheory.differentiable_theta hτ _ _).comp (by fun_prop)
  · intro m n hn
    set N : Fin g → ℂ := fun i => (n i : ℂ) with hN
    set M : Fin g → ℂ := fun i => (m i : ℂ) with hM
    have hsym : ∀ x y : Fin g → ℂ, x ⬝ᵥ τ *ᵥ y = y ⬝ᵥ τ *ᵥ x := by
      intro x y
      rw [dotProduct_mulVec, ← mulVec_transpose, hs.eq, dotProduct_comm]
    refine ⟨Complex.exp (2 * Real.pi * Complex.I * (c₁ ⬝ᵥ M) -
      Real.pi * Complex.I * (N ⬝ᵥ τ *ᵥ N) - 2 * Real.pi * Complex.I * (N ⬝ᵥ c₂)),
      Complex.exp_ne_zero _, fun z => ?_⟩
    let e : {p : Fin g → ℤ // ∀ k ∈ S, p k = 0} ≃ {p : Fin g → ℤ // ∀ k ∈ S, p k = 0} :=
      { toFun := fun p => ⟨p.1 - n, fun k hk => by simp [p.2 k hk, hn k hk]⟩
        invFun := fun p => ⟨p.1 + n, fun k hk => by simp [p.2 k hk, hn k hk]⟩
        left_inv := fun p => by ext; simp
        right_inv := fun p => by ext; simp }
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaCharOff
    rw [← e.tsum_eq, ← tsum_mul_left]
    congr 1
    funext p
    have hQ : (fun i => (((e p).1 i : ℤ) : ℂ)) = (fun i => ((p.1 i : ℤ) : ℂ)) - N := by
      funext i
      simp [e, hN]
    rw [hQ, ← Complex.exp_add, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
    refine ⟨∑ i, (p.1 i - n i) * m i, ?_⟩
    have hcast : ((∑ i, (p.1 i - n i) * m i : ℤ) : ℂ) =
        (fun i => ((p.1 i : ℤ) : ℂ)) ⬝ᵥ M - N ⬝ᵥ M := by
      simp [dotProduct, hM, hN, Finset.sum_sub_distrib, sub_mul]
    simp only [add_dotProduct, dotProduct_add, sub_dotProduct, dotProduct_sub, mulVec_add,
      mulVec_sub]
    linear_combination (Real.pi * Complex.I) * hsym (fun i => ((p.1 i : ℤ) : ℂ)) N +
      (Real.pi * Complex.I) * hsym c₁ N - (2 * Real.pi * Complex.I) * hcast

end GlobalTheory.ThetaBlock
end
end

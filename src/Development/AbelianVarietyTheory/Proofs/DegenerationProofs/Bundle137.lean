module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle122
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPowerSectionOfChartFunctions
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSumReindex
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationDataTorsionStructureAlgClosed
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle128
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle007

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.Ex.AbPartIso

noncomputable section
namespace GlobalTheory.Ex.AbPartIso
open ThetaInValues

theorem exists_th_scale : AllIso fun {_} _ _ {_} {_} {F} _ _ {N} {N'} ν ν' {_} w f =>
    ∃ lm : F, ∀ x, N'.th (f x) = lm * wVal ν ν' w f x * N.th x := by
  intro R _ _ D D' F _ _ N N' ν ν' φ w f hφ hw hc
  obtain ⟨y⟩ : Nonempty (TF (R := R) F).left := inferInstanceAs (Nonempty (PrimeSpectrum F))
  have hJ := good ν y
  have hJ' := good ν' y
  obtain ⟨th, ρ, hth, vth⟩ := exists_th ν y
  obtain ⟨th', ρ', -, vth'⟩ := exists_th ν' y
  have e : φ.hom.left ≫ (snd (TF (R := R) F) D'.P.A).left = 𝟙 _ ≫ (φ.hom ≫ snd (TF (R := R) F) D'.P.A).left :=
    (Category.id_comp _).symm
  let b := VVRank.pullTo (φ := fun _ : Fin 1 => (snd (TF (R := R) F) D'.P.A).left) (ε := fun _ => 1)
    (φ' := fun _ : Fin 1 => 𝟙 _ ≫ (φ.hom ≫ snd (TF (R := R) F) D'.P.A).left) th' φ.hom.left (fun _ => e)
  obtain ⟨a, ha, -⟩ := (FieldBaseChange.isoRelM_bijective (m := 𝟙 _) (k := 1) (h₁ := 𝟙 _)
    (g₁ := (snd (TF (R := R) F) D.P.A).left) D.P.isLB D'.P.isLB hw rfl (𝟙 _) (Category.id_comp _)
    (Category.id_comp _)).2 b
  obtain ⟨r, hr⟩ := hth a
  obtain ⟨r₀, rfl⟩ : ∃ r₀ : F, r = fnOf r₀ :=
    ⟨(Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom r, (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of F)) r).symm⟩
  refine ⟨r₀ * ρ * ρ'⁻¹.val, fun x => ?_⟩
  have H := BoxExpansion.isoRel_val ha (ptSecT D.P.A (ν.eA x)).left y hJ hJ'
  simp only [Category.comp_id] at H
  have h₁ : sval b (ptSecT D.P.A (ν.eA x)).left y ν'.J = sR y (N'.th (f x) * ρ') := by
    refine (VVRank.sval_pullTo _ _ _ _ y hJ').trans (Eq.trans ?_ (vth' (f x)))
    rw [← Over.comp_left, ptSecT, hc x]
    rfl
  have hm := hJ.mem (fun _ : Fin 1 => (snd (TF (R := R) F) D.P.A).left) (ptSecT D.P.A (ν.eA x)).left
  have h₂ : sval a (ptSecT D.P.A (ν.eA x)).left y ν.J = sR y r₀ * sR y (N.th x * ρ) := by
    refine (congrArg (gs _ y _) (hr _)).trans ((gs_mul _ y _ hm _ _).trans (congrArg₂ (· * ·) ?_ (vth x)))
    refine (gs_res _ y _ hm _).trans ((gs_pull _ (fst (TF (R := R) F) D.P.A).left y ⊤ trivial _).trans ?_)
    rw [← Over.comp_left, ptSecT, lift_fst]
    exact gs_fnOf y r₀
  have p₁ : (ptSecT D.P.A (ν.eA x)).left ≫ (snd (TF (R := R) F) D.P.A).left = (ν.eA x).left := by
    rw [← Over.comp_left, ptSecT, lift_snd]
  have p₂ : (ptSecT D.P.A (ν.eA x)).left ≫ (φ.hom ≫ snd (TF (R := R) F) D'.P.A).left = (ν'.eA (f x)).left := by
    rw [← Over.comp_left, ptSecT, ← Category.assoc, hc x, lift_snd]
  have h₃ : sR y (wVal ν ν' w f x) = (BoxExpansion.pw w (ptSecT D.P.A (ν.eA x)).left y (ν.J (ν.eA x).left)
      (ν'.J (ν'.eA (f x)).left)).val := by
    have m₁ : (snd (TF (R := R) F) D.P.A).left ((ptSecT D.P.A (ν.eA x)).left y) ∈ D.P.L.U (ν.J (ν.eA x).left) :=
      (congrArg (fun q : (TF (R := R) F).left ⟶ D.P.A.left => q y ∈ D.P.L.U (ν.J (ν.eA x).left)) p₁).mpr (hJ _)
    have m₂ : (φ.hom ≫ snd (TF (R := R) F) D'.P.A).left ((ptSecT D.P.A (ν.eA x)).left y) ∈
        D'.P.L.U (ν'.J (ν'.eA (f x)).left) :=
      (congrArg (fun q : (TF (R := R) F).left ⟶ D'.P.A.left => q y ∈ D'.P.L.U (ν'.J (ν'.eA (f x)).left)) p₂).mpr (hJ' _)
    exact toStk_valF (F := F) (ptSecT D.P.A (ν.eA x)).left
      ((D'.P.L.pull (φ.hom ≫ snd (TF (R := R) F) D'.P.A).left).U (fun _ => ν'.J (ν'.eA (f x)).left) ⊓
        (D.P.L.pull (snd (TF (R := R) F) D.P.A).left).U (fun _ => ν.J (ν.eA x).left)) y
      ⟨mem_pull.2 m₂, mem_pull.2 m₁⟩ _
  have H' : sR y (N'.th (f x) * ρ') = sR y (wVal ν ν' w f x) * (sR y r₀ * sR y (N.th x * ρ)) := by
    refine h₁.symm.trans (H.trans (congrArg₂ (· * ·) ?_ h₂))
    rw [h₃, pow_one, p₁, p₂]
  rw [← map_mul, ← map_mul] at H'
  haveI : Nontrivial ((TF (R := R) F).left.presheaf.stalk y) := inferInstance
  have := (sR (R := R) y).injective H'
  rw [← Units.eq_mul_inv_iff_mul_eq] at this
  rw [this]
  ring

end GlobalTheory.Ex.AbPartIso
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.Ex.AbPartIso

noncomputable section
namespace GlobalTheory.Ex.TorsMatch

theorem txT_zero {O : Type} [CommRing O] (N : NumD O) (m : ℕ) (p : N.QT (m ^ 2)) (hp : p.1.1 = 1) :
    N.txT m p 0 = N.uth m p.1.2.b 1 := by
  simp only [NumD.txT, NumD.vt, NumD.wQ, NumB.uth, NumB.mth, NumB.uV, hp, toAdd_one, NumD.ψ_zero, NumD.Gt.s_zero,
    NumD.c_zero, N.cub.N_one, N.cub.face, _root_.one_mul, div_one, NumD.Gt.pow_b, Units.val_one, div_eq_mul_inv,
    Units.val_mul, inv_one]
  ring

variable {C : Type} [NormedField C] {N N' : NumD C} {n : ℕ} (mt : Match N N' n)

theorem exists_partner (hA : mt.A) (i K : ℕ) (hK : K = n ^ i) (p : N.QT K) (hp : p.1.1 = 1) :
    ∃ p', mt.r K p p' ∧ p'.1.1 = 1 := by
  subst hK
  obtain ⟨p', h⟩ := mt.tot i p
  obtain ⟨z, hz⟩ := (hA.2 i p p' h).1.1 ⟨0, by rw [hp, smul_zero, toAdd_one]⟩
  refine ⟨p' * N'.qTriv _ (-z), (mt.eqv _ p p p' _ h ((N.qEq_equivalence _).refl p)).2
    ((N'.qEq_iff _ _).2 ⟨-z, rfl⟩), ?_⟩
  change p'.1.1.toAdd + n ^ i • (-z) = 0
  rw [hz, smul_neg, add_neg_cancel]

theorem partner_b (hn : n ≠ 0) (hA : mt.A) (i K : ℕ) (hK : K = n ^ i) {p q : N.QT K} {p' q' : N'.QT K}
    (h : mt.r K p p') (h' : mt.r K q q') (hp : p.1.1 = 1) (hp' : p'.1.1 = 1) (hq : q.1.1 = 1) (hq' : q'.1.1 = 1)
    (hb : p.1.2.b = q.1.2.b) : p'.1.2.b = q'.1.2.b := by
  subst hK
  obtain ⟨t, ht⟩ := mt.tot i (p⁻¹ * q)
  have hT : N.InT (p⁻¹ * q) := ⟨_, (N.qEq_equivalence _).refl _, by
      change p.1.1⁻¹ * q.1.1 = 1
      rw [hp, hq, inv_mul_cancel], by
      change p.1.2.b⁻¹ * q.1.2.b = 1
      rw [hb, inv_mul_cancel]⟩
  obtain ⟨t', e, t1, t2⟩ := (hA.2 i _ _ ht).2.1 hT
  have r1 := mt.mul _ _ _ _ _ h ((mt.eqv _ _ _ _ _ ht ((N.qEq_equivalence _).refl _)).2 e)
  rw [mul_inv_cancel_left] at r1
  obtain ⟨z, z1, z2⟩ := (mt.eqv _ _ _ _ _ r1 ((N.qEq_equivalence _).refl _)).1 h'
  change _ = p'.1.1.toAdd + t'.1.1.toAdd + _ at z1
  rw [hq', hp', t1, toAdd_one, add_zero, zero_add, ← natCast_zsmul] at z1
  have hz : z = 0 := (smul_eq_zero_iff_right (Int.natCast_ne_zero.2 (pow_ne_zero i hn))).1 z1.symm
  rw [hz, N'.io_zero, _root_.mul_one] at z2
  rw [z2]
  change _ = p'.1.2.b * t'.1.2.b
  rw [t2, _root_.mul_one]

theorem raise {k k' K : ℕ} (hk : k' ≠ 0) (hK : K = k * k') {p : N.QT k} {p' : N'.QT k} (h : mt.r k p p')
    (hp : p.1.1 = 1) (hp' : p'.1.1 = 1) :
    ∃ q q', mt.r K q q' ∧ q.1.1 = 1 ∧ q'.1.1 = 1 ∧ q.1.2 = p.1.2 ∧ q'.1.2 = p'.1.2 := by
  subst hK
  refine ⟨⟨(1, p.1.2), ?_⟩, ⟨(1, p'.1.2), ?_⟩, ?_, rfl, rfl, rfl, rfl⟩
  · rw [NumD.mem_QT, pow_mul, N.mem_QT.1 p.2, hp, toAdd_one, N.io_zero, one_pow]
  · rw [NumD.mem_QT, pow_mul, N'.mem_QT.1 p'.2, hp', toAdd_one, N'.io_zero, one_pow]
  · exact (mt.incl k k' p p' _ _ hk (((congrArg (· ^ k') hp).trans (one_pow k')).symm) rfl
      (((congrArg (· ^ k') hp').trans (one_pow k')).symm) rfl).1 h

theorem exists_pair [IsAlgClosed C] (hn : n ≠ 0) (hA : mt.A) (i K : ℕ) (hK : K = n ^ i) (b : N.A) (hb : b ^ K = 1) :
    ∃ p p', mt.r K p p' ∧ p.1.1 = 1 ∧ p'.1.1 = 1 ∧ p.1.2.b = b := by
  obtain ⟨u, h, h'⟩ := QStr.root_over N (hK ▸ pow_ne_zero i hn : K ≠ 0) 1 b hb
  obtain ⟨p', r, hp'⟩ := exists_partner mt hA i K hK ⟨(1, u), h'.trans N.io_zero.symm⟩ rfl
  exact ⟨_, p', r, rfl, hp', h⟩

theorem exists_map (hn : n ≠ 0) (hA : mt.A) (i : ℕ) : ∃ ρ : N.A → N'.A, ∀ K, K = n ^ i →
    ∀ p p', mt.r K p p' → p.1.1 = 1 → p'.1.1 = 1 → p'.1.2.b = ρ p.1.2.b := by
  classical
  refine ⟨fun b => if h : ∃ x : N.QT (n ^ i) × N'.QT (n ^ i), mt.r _ x.1 x.2 ∧ x.1.1.1 = 1 ∧ x.2.1.1 = 1 ∧ x.1.1.2.b = b
    then h.choose.2.1.2.b else 1, ?_⟩
  rintro K rfl p p' h hp hp'
  have ex : ∃ x : N.QT (n ^ i) × N'.QT (n ^ i), mt.r _ x.1 x.2 ∧ x.1.1.1 = 1 ∧ x.2.1.1 = 1 ∧ x.1.1.2.b = p.1.2.b :=
    ⟨(p, p'), h, hp, hp', rfl⟩
  obtain ⟨a, b, c, d⟩ := ex.choose_spec
  beta_reduce
  rw [dite_eq_left ex]
  exact partner_b mt hn hA i _ rfl h a hp hp' b c d.symm

theorem exists_torsMap : AllMatch fun {_} _ {N} {N'} {n} mt _ _ => mt.A → ∀ e, mt.Term e → ∀ j : ℕ, ∃ ρ : N.A → N'.A, TorsMap N.toNumB N'.toNumB (n ^ j) mt.c₀ ρ ∧ (∀ i, i ≤ 2 * j → ∀ p p', mt.r (n ^ i) p p' → p.1.1 = 1 → p'.1.1 = 1 → p'.1.2.b = ρ p.1.2.b) ∧ ∀ b : N.A, b ^ (n ^ j) ^ 2 = 1 → ∃ p p', mt.r (n ^ (2 * j)) p p' ∧ p.1.1 = 1 ∧ p'.1.1 = 1 ∧ p.1.2.b = b := by
  intro C _ _ _ _ N N' q q' n g g' hp _ _ _ _ _ _ mt hA e hT j
  have hn : n ≠ 0 := hp.ne_zero
  have hK : (n ^ j) ^ 2 = n ^ (2 * j) := by rw [← pow_mul, mul_comm]
  obtain ⟨ρ, hρ⟩ := exists_map mt hn hA (2 * j)
  refine ⟨ρ, ⟨fun b b' hb hb' => ?_, fun b hb => ?_⟩, fun i hi p p' h h1 h1' => ?_, fun b hb => ?_⟩
  · obtain ⟨p, p', h, h1, h2, rfl⟩ := exists_pair mt hn hA _ _ hK b hb
    obtain ⟨r, r', h', h3, h4, rfl⟩ := exists_pair mt hn hA _ _ hK b' hb'
    rw [← hρ _ hK p p' h h1 h2, ← hρ _ hK r r' h' h3 h4]
    refine ⟨(hρ _ hK _ _ (mt.mul _ _ _ _ _ h h') ?_ ?_).symm, ?_⟩
    · change p.1.1 * r.1.1 = 1
      rw [h1, h3, _root_.mul_one]
    · change p'.1.1 * r'.1.1 = 1
      rw [h2, h4, _root_.mul_one]
    · rw [← N.wp_of_eq_zero p r h1 h3, ← N'.wp_of_eq_zero p' r' h2 h4]
      exact mt.wp _ _ _ _ _ h h'
  · obtain ⟨p, p', h, h1, h2, rfl⟩ := exists_pair mt hn hA _ _ hK b hb
    rw [← hρ _ hK p p' h h1 h2]
    refine ⟨by rw [N'.QT_pow_b, h2, toAdd_one, N'.c_zero], ?_⟩
    have t := hT j p p' h h1 h2 0
    rwa [map_zero, txT_zero _ _ _ h1, txT_zero _ _ _ h2] at t
  · obtain ⟨r, r', h', h3, h4, h5, h6⟩ := raise mt (K := n ^ (2 * j)) (pow_ne_zero (2 * j - i) hn)
      (by rw [← pow_add, Nat.add_sub_cancel' hi]) h h1 h1'
    rw [← h5, ← h6]
    exact hρ _ rfl r r' h' h3 h4
  · exact exists_pair mt hn hA _ _ rfl b (hK ▸ hb)

end GlobalTheory.Ex.TorsMatch
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.Ex.AbPartIso

noncomputable section
namespace GlobalTheory.Ex.AbPartIso

theorem exists_prodIso {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {H : Over S'} {Φ : H.left ⟶ G.left}
    (h : IsPullback Φ H.hom G.hom f) :
    ∃ ψ : (Over.mk f ⊗ G).left ≅ H.left, ψ.hom ≫ Φ = (snd (Over.mk f) G).left ∧
      ψ.hom ≫ H.hom = (fst (Over.mk f) G).left := by
  have p : IsPullback (snd (Over.mk f) G).left (fst (Over.mk f) G).left G.hom f :=
    (IsPullback.of_hasPullback f G.hom).flip
  exact ⟨p.isoIsPullback _ _ h, p.isoIsPullback_hom_fst _ _ h, p.isoIsPullback_hom_snd _ _ h⟩

theorem exists_prodIso_of_common {S S' : Scheme.{0}} {f : S' ⟶ S} {G G' : Over S} {H : Over S'}
    [GrpObj G] [GrpObj G'] [GrpObj H] {Φ : H.left ⟶ G.left} {Ψ : H.left ⟶ G'.left}
    (h : IsGrpPullback H G f Φ) (h' : IsGrpPullback H G' f Ψ) :
    ∃ (φ : Over.mk f ⊗ G ≅ Over.mk f ⊗ G') (ψ : (Over.mk f ⊗ G).left ⟶ H.left),
      ψ ≫ Φ = (snd (Over.mk f) G).left ∧ ψ ≫ H.hom = (fst (Over.mk f) G).left ∧
      ψ ≫ Ψ = (φ.hom ≫ snd (Over.mk f) G').left ∧ φ.hom ≫ fst _ _ = fst _ _ ∧
      ∀ (Z : Over S) (t : Z ⟶ Over.mk f) (x y : Z ⟶ G),
        lift t (x * y) ≫ φ.hom ≫ snd _ _ = (lift t x ≫ φ.hom ≫ snd _ _) * (lift t y ≫ φ.hom ≫ snd _ _) := by
  obtain ⟨ψ, e₁, e₂⟩ := exists_prodIso h.1
  obtain ⟨ψ', e₁', e₂'⟩ := exists_prodIso h'.1
  have w : ∀ G₀ : Over S, (fst (Over.mk f) G₀).left ≫ f = (Over.mk f ⊗ G₀).hom := fun G₀ =>
    Over.w (fst (Over.mk f) G₀)
  have k₂ : (ψ ≪≫ ψ'.symm).hom ≫ (fst (Over.mk f) G').left = (fst (Over.mk f) G).left := by
    rw [← e₂', ← e₂]; simp
  have k₁ : (ψ ≪≫ ψ'.symm).hom ≫ (snd (Over.mk f) G').left = ψ.hom ≫ Ψ := by
    rw [← e₁']; simp
  let φ : Over.mk f ⊗ G ≅ Over.mk f ⊗ G' := Over.isoMk (ψ ≪≫ ψ'.symm) (by
    rw [← w, ← w, ← k₂]; exact (Category.assoc _ _ _).symm)
  have k : (φ.hom ≫ snd (Over.mk f) G').left = ψ.hom ≫ Ψ := k₁
  refine ⟨φ, ψ.hom, e₁, e₂, k.symm, Over.OverMorphism.ext k₂, fun Z t x y => ?_⟩
  obtain ⟨Zl, ⟨⟨⟩⟩, Zh⟩ := Z
  have ht : t.left ≫ f = Zh := Over.w t
  let up : (Over.mk Zh ⟶ G) → (Over.mk t.left ⟶ H) := fun z =>
    Over.homMk ((lift t z).left ≫ ψ.hom) (by
      show ((lift t z).left ≫ ψ.hom) ≫ H.hom = t.left
      rw [Category.assoc, e₂]
      exact congrArg CommaMorphism.left (lift_fst t z))
  have hup : ∀ z, (up z).left ≫ Φ = z.left := fun z => by
    show ((lift t z).left ≫ ψ.hom) ≫ Φ = z.left
    rw [Category.assoc, e₁]
    exact congrArg CommaMorphism.left (lift_snd t z)
  have hup' : ∀ z, (up z).left ≫ Ψ = (lift t z ≫ φ.hom ≫ snd _ _).left := fun z => by
    show ((lift t z).left ≫ ψ.hom) ≫ Ψ = (lift t z).left ≫ (φ.hom ≫ snd _ _).left
    rw [Category.assoc, k]
  have hm : up (x * y) = up x * up y := by
    apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · rw [hup, ← h.2 _ (up x) (up y) (pushPt h.1.w (up x)) (pushPt h.1.w (up y)) rfl rfl]
      exact mul_left_congr ht.symm x y _ _ (hup x).symm (hup y).symm
    · rw [Over.w, Over.w]
  apply Over.OverMorphism.ext
  refine (hup' (x * y)).symm.trans ?_
  rw [hm, ← h'.2 _ (up x) (up y) (pushPt h'.1.w (up x)) (pushPt h'.1.w (up y)) rfl rfl]
  exact mul_left_congr ht _ _ _ _ (hup' x) (hup' y)

theorem exists_iso_of_isFib : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (Q Q' : PolAV (Sp F)) (Φ : Q.A.left ⟶ D.P.A.left) (Φ' : Q'.A.left ⟶ D'.P.A.left), IsFib D F Q Φ → IsFib D' F Q' Φ' → ∀ σ : Q.A ≅ Q'.A, IsPolIso Q Q' σ → ∃ (φ : TF (R := R) F ⊗ D.P.A ≅ TF (R := R) F ⊗ D'.P.A) (w : BunIso φ), HomF φ ∧ w.IsGen ∧ ∀ (a : TF (R := R) F ⟶ D.P.A) (a' : TF (R := R) F ⟶ D'.P.A), (∀ x : baseOver (Sp F) ⟶ Q.A, a.left = x.left ≫ Φ → a'.left = (x ≫ σ.hom).left ≫ Φ') → lift (𝟙 _) a ≫ φ.hom = lift (𝟙 _) a' := by
  intro R _ _ D D' F _ _ Q Q' Φ Φ' hΦ hΦ' σ hσ
  have := hσ.1
  have g' : IsGrpPullback Q.A D'.P.A (TF (R := R) F).hom (σ.hom.left ≫ Φ') :=
    ((isGrpPullback_of_iso σ).comp hΦ'.1).congr (Category.id_comp _) rfl
  obtain ⟨φ, ψ, e₁, e₂, e₃, e₄, e₅⟩ := exists_prodIso_of_common hΦ.1 g'
  have l₁ : LBIso (Q'.L.pull σ.hom.left) (D'.P.L.pull (σ.hom.left ≫ Φ')) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull Q'.L _ _ rfl)
      (chartPullSame D'.P.L (fun _ : PUnit => σ.hom.left ≫ Φ') (fun _ => Φ') _ σ.hom.left fun _ => rfl) hΦ'.2.1
  have l₂ : LBIso Q.L (D'.P.L.pull (σ.hom.left ≫ Φ')) :=
    LBIso.trans Q.isLB (pull_isLB Q'.isLB _) (pull_isLB D'.P.isLB _) (LBIso.symm hσ.2) l₁
  have l₃ : LBIso (D.P.L.pull Φ) (D'.P.L.pull (σ.hom.left ≫ Φ')) :=
    LBIso.trans (pull_isLB D.P.isLB _) Q.isLB (pull_isLB D'.P.isLB _) (LBIso.symm hΦ.2.1) l₂
  obtain ⟨w, hw⟩ : LBIso (D.P.L.pull (snd (TF (R := R) F) D.P.A).left)
      (D'.P.L.pull (φ.hom ≫ snd (TF (R := R) F) D'.P.A).left) :=
    LBIso.chartPull
      (chartPullSame D.P.L (fun _ : PUnit => (snd (TF (R := R) F) D.P.A).left) (fun _ => Φ) _ ψ fun _ => e₁.symm)
      (chartPullSame D'.P.L (fun _ : PUnit => (φ.hom ≫ snd (TF (R := R) F) D'.P.A).left)
        (fun _ => σ.hom.left ≫ Φ') _ ψ fun _ => e₃.symm) l₃
  refine ⟨φ, w, ⟨e₄, e₅⟩, hw, fun a a' ha => ?_⟩
  let x : baseOver (Sp F) ⟶ Q.A := Over.homMk ((lift (𝟙 (TF (R := R) F)) a).left ≫ ψ) (by
    refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) e₂).trans ?_)
    exact congrArg CommaMorphism.left (lift_fst (𝟙 (TF (R := R) F)) a))
  have hx : a.left = x.left ≫ Φ := by
    refine Eq.symm ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) e₁).trans ?_))
    exact congrArg CommaMorphism.left (lift_snd (𝟙 (TF (R := R) F)) a)
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, lift_fst]
    exact (congrArg (_ ≫ ·) e₄).trans (lift_fst _ _)
  · rw [Category.assoc, lift_snd]
    apply Over.OverMorphism.ext
    refine Eq.symm ((ha x hx).trans ?_)
    refine Eq.trans ?_ (congrArg ((lift (𝟙 (TF (R := R) F)) a).left ≫ ·) e₃)
    exact (Category.assoc _ _ _).trans (Category.assoc _ _ _)

end GlobalTheory.Ex.AbPartIso
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

namespace GlobalTheory.PsiCoef

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem cT_zero (T : Over (Spec (CommRingCat.of R))) : cT D T 0 = 1 := by
  have h : D.c 0 = D.c 0 * D.c 0 := by
    have := D.c_add 0 0
    rwa [add_zero] at this
  have h1 : D.c 0 = 1 := left_eq_mul.1 h
  rw [cT, h1, MonObj.comp_one]

theorem comp_cT {T T' : Over (Spec (CommRingCat.of R))} (r : T ⟶ T') (α : D.X) : r ≫ cT D T' α = cT D T α := by
  rw [← Category.assoc, comp_toUnit]

theorem exists_untwist (χ : D.X)
    (u : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (hu : u.IsGen)
    (g : SecBT D (𝟙_ _) 1 χ) :
    ∃ g₀ : SecBT D (𝟙_ _) 1 0, ∀ (T : Over (Spec (CommRingCat.of R))) (y : T ⟶ D.P.A) (z : T.left) (J),
      Good D.P.L z J → sval g₀ (lift (toUnit T) (y * cT D T χ)).left z J =
        sval g (lift (toUnit T) y).left z J * ((val u (toUnit T).left z J * rigV D z J)⁻¹).val := by
  let Y : Over (Spec (CommRingCat.of R)) := 𝟙_ _ ⊗ D.P.A
  let τ : Y ⟶ Y := lift (toUnit Y) (snd _ _ * (cT D Y χ)⁻¹)
  have hF : FormEq
      (Sum.elim (fun k => τ.left ≫ famφT D (𝟙_ _) χ k)
        (fun k => (toUnit Y).left ≫ Sum.elim (fun _ : PUnit => (D.c χ).left) (fun _ : PUnit => eSec D.P.A) k))
      (Sum.elim (DegPre.famε 1) (fun k => -(Sum.elim (fun _ => -1) (fun _ => 1) k)))
      (famφT D (𝟙_ _) 0) (DegPre.famε 1) := by
    intro U _ h
    have e₀ : famφT D (𝟙_ _) 0 0 = famφT D (𝟙_ _) 0 1 := by
      change (snd _ _ : Y ⟶ D.P.A).left = (snd _ _ * cT D Y 0).left
      rw [cT_zero, _root_.mul_one]
    have e₀' : famφT D (𝟙_ _) 0 2 = famφT D (𝟙_ _) 0 3 := by
      change (cT D Y 0).left = (1 : Y ⟶ D.P.A).left
      rw [cT_zero]
    have e₁ : τ.left ≫ famφT D (𝟙_ _) χ 1 = famφT D (𝟙_ _) 0 1 := by
      change (τ ≫ (snd _ _ * cT D Y χ)).left = (snd _ _ * cT D Y 0).left
      rw [cT_zero, _root_.mul_one, MonObj.comp_mul, comp_cT, lift_snd, inv_mul_cancel_right]
    have e₂ : τ.left ≫ famφT D (𝟙_ _) χ 2 = famφT D (𝟙_ _) χ 2 := by
      change (τ ≫ cT D Y χ).left = (cT D Y χ).left
      rw [comp_cT]
    have e₃ : τ.left ≫ famφT D (𝟙_ _) χ 3 = famφT D (𝟙_ _) 0 3 := by
      change (τ ≫ (1 : Y ⟶ D.P.A)).left = (1 : Y ⟶ D.P.A).left
      rw [MonObj.comp_one]
    have e₄ : (toUnit Y).left ≫ (D.c χ).left = famφT D (𝟙_ _) χ 2 := rfl
    have e₅ : (toUnit Y).left ≫ eSec D.P.A = famφT D (𝟙_ _) 0 3 := rfl
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, Fin.prod_univ_four,
      e₀, e₀', e₁, e₂, e₃, e₄, e₅]
    simp [DegPre.famε, _root_.mul_assoc]
  obtain ⟨g₀, hg₀⟩ := exists_sec D.P.isLB hF (pullMulSec g τ.left
    (LB.invGen D.P.L _ _ (LB.pullGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ u D.rig) (toUnit Y).left))
    (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ hu D.rig_gen) _)))
  refine ⟨g₀, fun T y z J hJ => ?_⟩
  have e₂ : (lift (toUnit T) (y * cT D T χ)).left ≫ τ.left = (lift (toUnit T) y).left := by
    rw [← Over.comp_left]
    congr 1
    refine (comp_lift _ _ _).trans (congrArg₂ lift (toUnit_unique _ _) ?_)
    rw [MonObj.comp_mul, GrpObj.comp_inv, comp_cT, lift_snd, mul_inv_cancel_right]
  have e₃ : (lift (toUnit T) (y * cT D T χ)).left ≫ (toUnit Y).left = (toUnit T).left := by
    rw [← Over.comp_left]
    exact congrArg _ (toUnit_unique _ _)
  rw [hg₀ _ _ z J hJ, sval_pullMulSec _ _ _ _ _ _ hJ, e₂, val_inv, val_pull hJ, e₃, val_mul hJ]
  congr 5

theorem exists_coef : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (th : SecBT D (𝟙_ _) 1 0), (∀ g : SecBT D (𝟙_ _) 1 0, ∃ b : R, Mult D th g b) → ∀ (χ : D.X) (u : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))), u.IsGen → ∀ g : SecBT D (𝟙_ _) 1 χ, ∃ b : R, Coef D χ u th g b := by
  intro R _ _ D th hth χ u hu g
  obtain ⟨g₀, hg₀⟩ := exists_untwist D χ u hu g
  obtain ⟨b, hb⟩ := hth g₀
  exact ⟨b, fun T y z J hJ => by
    have e₁ : (lift (toUnit T) (y * cT D T χ)).left ≫ (𝟙_ _ ⊗ D.P.A).hom = T.hom := Over.w _
    have h := hb _ (lift (toUnit T) (y * cT D T χ)).left z J hJ
    rw [e₁, hg₀ T y z J hJ, Units.mul_inv_eq_iff_eq_mul] at h
    rw [h]
    ring⟩

end GlobalTheory.PsiCoef
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

namespace GlobalTheory.PsiRing

theorem exists_thick_eq_closedPoint (R : Type) [CommRing R] [IsLocalRing R] (I : Ideal R) (hI : I ≠ ⊤) (e : ℕ) :
    ∃ p, thick R I e p = IsLocalRing.closedPoint R := by
  have h : IsLocalRing.closedPoint R ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (I ^ (e + 1)))) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, PrimeSpectrum.mem_zeroLocus]
    exact fun x hx => IsLocalRing.le_maximalIdeal hI (Ideal.pow_le_self (Nat.succ_ne_zero e) hx)
  exact h

theorem exists_unit_term :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), I ≠ ⊤ → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (k : ℕ) (σ : U.SecGT (𝟙_ _) k) (f : ∀ α, SecBT D (𝟙_ _) k α), U.ExpT (𝟙_ _) k σ f → FibNZ (𝟙_ _ ⊗ G).hom σ → ∃ (T : Over (Spec (CommRingCat.of R))) (y : T ⟶ D.P.A) (z : T.left) (J : (T.left ⟶ D.P.A.left) → D.P.L.ι) (α : D.X), Good D.P.L z J ∧ T.hom z = IsLocalRing.closedPoint R ∧ (∀ b ∈ I, Geo.Tor.cst T.hom z b = 0) ∧ IsUnit (sval (f α) (lift (toUnit T) y).left z J) := by
  intro R _ _ _ I hI D A G _ _ U k σ f hE hF
  obtain ⟨z₀, hz₀, hn⟩ := hF (IsLocalRing.closedPoint R)
  obtain ⟨p, hp⟩ := exists_thick_eq_closedPoint R I hI 0
  have h₁ : G.hom ((snd (𝟙_ _) G).left z₀) = thick R I 0 p := by
    rw [hp, ← hz₀, ← Scheme.Hom.comp_apply, Over.w]
  obtain ⟨z, hz, hz'⟩ := Scheme.Pullback.exists_preimage_pullback _ _ h₁
  let T : Over (Spec (CommRingCat.of R)) := (Over.map (thick R I 0)).obj (thickObj R I 0 G)
  let y : T ⟶ D.P.A := (U.gt 0).pG
  let x : T ⟶ G := fstG I 0 G
  have hG : (lift (toUnit T) x).left ≫ (snd _ G).left = x.left := by rw [← Over.comp_left, lift_snd]
  have hB : (lift (toUnit T) y).left ≫ (snd _ D.P.A).left = y.left := by rw [← Over.comp_left, lift_snd]
  have hf : (lift (toUnit T) y).left ≫ (fst _ D.P.A).left = (lift (toUnit T) x).left ≫ (fst _ G).left := by
    rw [← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]
  have hr : (lift (toUnit T) x).left z = z₀ := by
    have hi : lift (toUnit T) x = x ≫ (λ_ G).inv := by ext1 <;> simp [toUnit_unique]
    have hj : (snd (𝟙_ _) G).left ≫ (λ_ G).inv.left = 𝟙 _ := by
      rw [← Over.comp_left, ← leftUnitor_hom, Iso.hom_inv_id, Over.id_left]
    have hx : x.left z = (snd (𝟙_ _) G).left z₀ := hz
    rw [hi, Over.comp_left, Scheme.Hom.comp_apply, hx, ← Scheme.Hom.comp_apply, hj]
    rfl
  obtain ⟨JG, hJG⟩ := exists_good_pt (Z := T.left) U.P.L.isLB z
  obtain ⟨J, hJ⟩ := exists_good_pt (Z := T.left) D.P.isLB z
  obtain ⟨s, hs⟩ := hE 0
  obtain ⟨-, hsum⟩ := hs T.left (𝟙 _) _ _ (hG.trans (Category.id_comp _).symm) (hB.trans (Category.id_comp _).symm)
    hf z JG J hJG hJ
  have hu : IsUnit (sval σ (lift (toUnit T) x).left z JG) :=
    (MulPullSec.mem_nonzeroLocus_iff σ _ z hJG).1 (hr ▸ hn)
  obtain ⟨α, -, hα⟩ := IsLocalRing.exists_of_isUnit_sum
    ((congrArg IsUnit hsum).mp (((Units.isUnit _).pow k).mul hu))
  refine ⟨T, y, z, J, α, hJ, ?_, fun b hb => ?_, isUnit_of_mul_isUnit_left hα⟩
  · have : T.hom = pullback.snd G.hom (thick R I 0) ≫ thick R I 0 := rfl
    rw [this, Scheme.Hom.comp_apply, hz', hp]
  · refine (Geo.Tor.cst_comp (pullback.snd G.hom (thick R I 0)) (Ideal.Quotient.mk (I ^ (0 + 1))) z b).trans ?_
    rw [Ideal.Quotient.eq_zero_iff_mem.2 (by simpa using hb), Geo.Tor.cst, map_zero, gs_eq _ _ ⊤ trivial, map_zero,
      map_zero]

end GlobalTheory.PsiRing
end

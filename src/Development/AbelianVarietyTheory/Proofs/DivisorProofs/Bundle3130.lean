module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3062
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle145
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle096
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle391
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3067
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007

@[expose] public section

section

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc.UGalAct


open GlobalTheory.Poinc.GalAct in
theorem exists_galLab : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X₁ : USetup C) (D : UDeep X₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁), ∃ a : D.X.S.Gam ≃+ D.X.S.Gam, D.GalLab σ a ∧ ∀ x, a (D.lab x) = D.lab x := by
  intro E _ _ _ H Dw _ l Xo cf C X₁ D σ
  obtain ⟨P₀, a₁, a₂, h₁, h₂, l₁, l₂, hpt⟩ := D.same
  have hs : spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) ≫ spMap ((algebraMap X₁.Ω₁ D.X.Ω₁).comp X₁.S.R.val.toRingHom) =
      spMap ((algebraMap X₁.Ω₁ D.X.Ω₁).comp X₁.S.R.val.toRingHom) :=
    (spMap_comp _ _).symm.trans (congrArg spMap (RingHom.ext fun y => σ.commutes _))
  obtain ⟨t, ht₁, ht₂⟩ : ∃ t : P₀.A.left ⟶ P₀.A.left, t ≫ a₁ = a₁ ∧
      t ≫ P₀.A.hom = P₀.A.hom ≫ spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) :=
    ⟨h₁.1.lift a₁ (P₀.A.hom ≫ spMap (σ : D.X.Ω₁ →+* D.X.Ω₁)) (by rw [Category.assoc, hs, h₁.1.w]),
      h₁.1.lift_fst _ _ _, h₁.1.lift_snd _ _ _⟩
  have ht : IsGrpPullback P₀.A P₀.A (spMap (σ : D.X.Ω₁ →+* D.X.Ω₁)) t := h₁.cancel (h₁.congr hs.symm ht₁.symm) ht₂
  have lt : LBIso (P₀.L.pull t) (X₁.ρ.P.L.pull a₁) :=
    l₁.chartPull (Geo.Tor.chartPullPull P₀.L t t rfl)
      (chartPullSame X₁.ρ.P.L (fun _ => a₁) (fun _ => a₁) _ t fun _ => ht₁.symm)
  obtain ⟨a, ha, ha'⟩ := exists_label_action D.X.ρ h₂ (σ : D.X.Ω₁ →+* D.X.Ω₁) σ.surjective ht
  refine ⟨a, ⟨P₀, a₂, t, h₂, ht, l₂,
    LBIso.trans P₀.isLB (pull_isLB X₁.ρ.P.isLB _) (pull_isLB P₀.isLB _) l₁ lt.symm, ha⟩,
    fun x => ?_⟩
  obtain ⟨w, hw₁, hw₂⟩ := hpt x
  refine ha' _ w hw₂ (h₁.1.hom_ext ?_ ?_)
  · rw [Category.assoc, Category.assoc, ht₁, hw₁, ← Category.assoc, hs]
  · have hw : w ≫ P₀.A.hom = 𝟙 _ := by
      refine eq_id_of_frac D.X.S.R.val.toRingHom (fun y => ?_) _ ?_
      · obtain ⟨c, hc, d, hd, rfl⟩ := D.X.S.frac y
        exact ⟨⟨c, hc⟩, ⟨d, hd⟩, rfl⟩
      · rw [Category.assoc, ← h₂.1.w, ← Category.assoc, hw₂, Category.assoc]
        exact (congrArg _ (Over.w (D.X.ρ.pt _))).trans (Category.comp_id _)
    rw [Category.assoc, Category.assoc, ht₂, hw, ← Category.assoc, hw, Category.id_comp, Category.comp_id]

end GlobalTheory.UPoinc.UGalAct
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

noncomputable section

namespace GlobalTheory.Mum.TensRosMove

theorem rosati_alg {U : Type} [CommGroup U] (g : Fin 6 → U) (u : U) :
    (∏ k, g k ^ rosatiε k) * u * (g 1 * g 2 * g 3) = u * (g 0 * g 4 * g 5) := by
  rw [Fin.prod_univ_six]
  show g 0 ^ (1 : ℤ) * g 1 ^ (-1 : ℤ) * g 2 ^ (-1 : ℤ) * g 3 ^ (-1 : ℤ) * g 4 ^ (1 : ℤ) * g 5 ^ (1 : ℤ) * u *
    (g 1 * g 2 * g 3) = u * (g 0 * g 4 * g 5)
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow]
  abel

theorem rosVT_move : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N') (O : Type) [CommRing O] [StarRing O] (oa : D'.toPre.P.OAct O) (x : O) (ρ' : N'.A → N'.A → F), GlobalTheory.Relabel.RosV ν' oa x ρ' → ∃ ρ'' : N'.A → N'.A → F, GlobalTheory.Mum.TensRos.RosVT T ν ν' (oa.act (star x)) (oa.act x) ρ'' ∧ ∀ a b, ρ'' a b * (wv T ν ν' (GlobalTheory.Relabel.actV ν' oa (star x) a) * wv T ν ν' b * wv T ν ν' (a * GlobalTheory.Relabel.actV ν' oa x b)) = ρ' a b * (wv T ν ν' (GlobalTheory.Relabel.actV ν' oa (star x) a * b) * wv T ν ν' a * wv T ν ν' (GlobalTheory.Relabel.actV ν' oa x b)) := by
  intro R _ _ _ _ D D' n W T F _ _ _ N N' ν ν' O _ _ oa x ρ' hR
  obtain ⟨u, hu, u₀, hρ⟩ := hR
  have := oa.hom x
  have := oa.hom (star x)
  have hL₁ : (LB.LinComb D.toPre.P.L (tensφ T.pr) (tensε W)).IsLB := LB.isLB_linComb D.toPre.P.isLB _ _
  obtain ⟨u'', hu'', hv⟩ := GlobalTheory.WtTower.exists_gen_of_iso (LB.isLB_linComb D'.toPre.P.isLB _ rosatiε)
    (LB.isLB_linComb hL₁ (rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x)) rosatiε)
    (LB.linCombIso T.w _ rosatiε) (DVR.linCombIso_isGen T.w T.w_gen _ _) u hu
  refine ⟨fun a b => vF u'' (lift (ν'.eA a) (ν'.eA b)).left (GlobalTheory.Mum.TensRos.tensJ T ν), ⟨u'', hu'', ?_, fun _ _ => rfl⟩, ?_⟩
  · refine corr_of_val hL₁ fun y J hJ => ?_
    rw [val_pull hJ, val_one]
    have h1 : (η[D'.toPre.P.A] : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.toPre.P.A) = 1 := by
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    have hz : ∀ k, (𝟙 _ ≫ zero2 D'.toPre.P.A) ≫ rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x) k =
        (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.toPre.P.A).left := fun k => by
      rw [Category.id_comp, zero2, h1, ← GlobalTheory.RosMove.rosO_left, ← Over.comp_left, GlobalTheory.RosMove.lift_rosO]
      fin_cases k <;> simp [MonObj.one_comp]
    choose I hI using fun χ : _ ⟶ D'.toPre.P.A.left => exists_chart D'.toPre.P.isLB (χ y)
    have hI' : Good D'.toPre.P.L y I := hI
    have e₀ : val u (𝟙 _ ≫ zero2 D'.toPre.P.A) y I = 1 := by
      have := val_corr hI' u₀ (𝟙 _)
      rwa [val_pull hI', val_one] at this
    have m₁ := hJ.mem (rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x)) (𝟙 _ ≫ zero2 D'.toPre.P.A)
    have m₂ := hI'.mem (rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x)) (𝟙 _ ≫ zero2 D'.toPre.P.A)
    have H := hv _ (𝟙 _ ≫ zero2 D'.toPre.P.A) y _ _ m₁ m₂
    have G := GlobalTheory.WtTower.gm_linCombIso T.w (rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x)) rosatiε (_, _)
      (𝟙 _ ≫ zero2 D'.toPre.P.A) y ⟨m₁, m₂⟩
    refine H.trans (Eq.trans (congrArg₂ (· * ·) G e₀) ?_)
    rw [_root_.mul_one]
    have key : ∀ Fn : (_ ⟶ D'.toPre.P.A.left) → ((𝟙_ (Over (Spec (CommRingCat.of R)))).left.presheaf.stalk y)ˣ,
        ∏ a, Fn ((𝟙 _ ≫ zero2 D'.toPre.P.A) ≫ rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x) a) ^ rosatiε a = 1 := by
      intro Fn
      simp only [hz]
      simp [Fin.prod_univ_succ, rosatiε]
    exact key (fun ψ => gm ψ y (((LB.LinComb D.toPre.P.L (tensφ T.pr) (tensε W)).div D'.toPre.P.L).U (J ψ, I ψ))
      (T.w.s (J ψ, I ψ)))
  · intro a b
    let z : Sp F := IsLocalRing.closedPoint F
    have hN : Good D.toPre.P.L z ν.J := fun q => ν.good q trivial
    have hJ' : Good D'.toPre.P.L z ν'.J := fun q => ν'.good q trivial
    have mT : ∀ y : Sp F ⟶ D'.toPre.P.A.left,
        y z ∈ (LB.LinComb D.toPre.P.L (tensφ T.pr) (tensε W)).U (GlobalTheory.Mum.TensRos.tensJ T ν y) :=
      fun y => Set.mem_iInter.2 fun k => hN (y ≫ tensφ T.pr k)
    have m₁ : (lift (ν'.eA a) (ν'.eA b)).left z ∈ LB.wchart (LB.LinComb D.toPre.P.L (tensφ T.pr) (tensε W))
        (rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x))
        (fun k => GlobalTheory.Mum.TensRos.tensJ T ν ((lift (ν'.eA a) (ν'.eA b)).left ≫
          rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x) k)) := Set.mem_iInter.2 fun k => mT _
    have m₂ := hJ'.mem (rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x)) (lift (ν'.eA a) (ν'.eA b)).left
    have H := hv _ (lift (ν'.eA a) (ν'.eA b)).left z _ _ m₁ m₂
    have G := GlobalTheory.WtTower.gm_linCombIso T.w (rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x)) rosatiε (_, _)
      (lift (ν'.eA a) (ν'.eA b)).left z ⟨m₁, m₂⟩
    let Gp : N'.A → ((Sp F).presheaf.stalk z)ˣ := fun p => gm (ν'.eA p).left z
      (((LB.LinComb D.toPre.P.L (tensφ T.pr) (tensε W)).div D'.toPre.P.L).U
        (GlobalTheory.Mum.TensRos.tensJ T ν (ν'.eA p).left, ν'.J (ν'.eA p).left))
      (T.w.s (GlobalTheory.Mum.TensRos.tensJ T ν (ν'.eA p).left, ν'.J (ν'.eA p).left))
    have hW : ∀ p, toStk z (wv T ν ν' p) = (Gp p).val := fun p => by
      have hm : (ν'.eA p).left z ∈ (((LB.LinComb D.toPre.P.L (tensφ T.pr) (tensε W)).div D'.toPre.P.L).U
          (GlobalTheory.Mum.TensRos.tensJ T ν (ν'.eA p).left, ν'.J (ν'.eA p).left)) := ⟨mT _, hJ' _⟩
      exact toStk_valF _ _ z hm _
    have ea : ∀ y c, ν'.eA (GlobalTheory.Relabel.actV ν' oa y c) = ν'.eA c ≫ oa.act y := fun y c => ν'.eA.apply_symm_apply _
    let pts : Fin 6 → N'.A := ![GlobalTheory.Relabel.actV ν' oa (star x) a * b, GlobalTheory.Relabel.actV ν' oa (star x) a, b,
      a * GlobalTheory.Relabel.actV ν' oa x b, a, GlobalTheory.Relabel.actV ν' oa x b]
    have hp : ∀ k, (lift (ν'.eA a) (ν'.eA b)).left ≫ rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x) k =
        (ν'.eA (pts k)).left := fun k => by
      rw [← GlobalTheory.RosMove.rosO_left, ← Over.comp_left, GlobalTheory.RosMove.lift_rosO]
      fin_cases k <;> simp [pts, ea]
    have key : ∀ Fn : (Sp F ⟶ D'.toPre.P.A.left) → ((Sp F).presheaf.stalk z)ˣ,
        ∏ k, Fn ((lift (ν'.eA a) (ν'.eA b)).left ≫ rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x) k) ^ rosatiε k =
          ∏ k, Fn (ν'.eA (pts k)).left ^ rosatiε k := fun Fn => by simp only [hp]
    have G' := G.trans (key (fun ψ => gm ψ z
      (((LB.LinComb D.toPre.P.L (tensφ T.pr) (tensε W)).div D'.toPre.P.L).U (GlobalTheory.Mum.TensRos.tensJ T ν ψ, ν'.J ψ))
      (T.w.s (GlobalTheory.Mum.TensRos.tensJ T ν ψ, ν'.J ψ))))
    have v'' := toStk_valF _ _ z m₁ (u''.s _)
    have v' : toStk z (ρ' a b) = (gm (lift (ν'.eA a) (ν'.eA b)).left z _ (u.s fun k => ν'.J
        ((lift (ν'.eA a) (ν'.eA b)).left ≫ rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x) k))).val := by
      rw [hρ]; exact toStk_valF _ _ z m₂ _
    have HH := H.trans (congrArg₂ (· * ·) G' rfl)
    apply (toStk z).injective
    show toStk z (vF u'' (lift (ν'.eA a) (ν'.eA b)).left (GlobalTheory.Mum.TensRos.tensJ T ν) * _) = _
    simp only [map_mul, hW, v']
    erw [v'', HH]
    simp only [← Units.val_mul]
    congr 1
    exact rosati_alg (fun k => Gp (pts k)) _

end GlobalTheory.Mum.TensRosMove
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TensBal.SpanPf

variable {r : ℕ}

abbrev S (r : ℕ) : Submodule ℤ (Vec r →₀ ℤ) :=
  Submodule.span ℤ (Set.range fun p : Vec r × Vec r × Vec r => theta p.1 p.2.1 p.2.2)

lemma lam_comm (u v : Vec r) : lam u v = lam v u := by
  unfold lam; rw [add_comm u v]; abel

lemma theta_eq (u u' v : Vec r) : theta u u' v = lam (u + u') v - lam u v - lam u' v := by
  unfold lam theta; abel

lemma theta_mem (a b c : Vec r) : theta a b c ∈ S r := Submodule.subset_span ⟨(a, b, c), rfl⟩

def f (u v : Vec r) : (Vec r →₀ ℤ) ⧸ S r := Submodule.Quotient.mk (lam u v)

lemma f_comm (u v : Vec r) : f u v = f v u := by unfold f; rw [lam_comm]

lemma f_add_left (u u' v : Vec r) : f (u + u') v = f u v + f u' v := by
  unfold f
  rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq]
  have h := theta_mem u u' v
  rw [theta_eq] at h
  convert h using 1; abel

lemma f_add_right (u v v' : Vec r) : f u (v + v') = f u v + f u v' := by
  rw [f_comm, f_add_left, f_comm v, f_comm v']

lemma f_smul_left (c : ℤ) (u v : Vec r) : f (c • u) v = c • f u v :=
  map_zsmul (AddMonoidHom.mk' (fun u => f u v) (fun a b => f_add_left a b v)) c u

lemma f_smul_right (c : ℤ) (u v : Vec r) : f u (c • v) = c • f u v := by
  rw [f_comm, f_smul_left, f_comm]

def B (r : ℕ) : Vec r →ₗ[ℤ] Vec r →ₗ[ℤ] (Vec r →₀ ℤ) ⧸ S r :=
  LinearMap.mk₂ ℤ f f_add_left f_smul_left f_add_right f_smul_right

lemma B_apply (u v : Vec r) : B r u v = Submodule.Quotient.mk (lam u v) := rfl

lemma B_comm (u v : Vec r) : B r u v = B r v u := f_comm u v

lemma axv_eq (A : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) : axv A i = ∑ l, A i l • xv l := by
  funext s
  cases s <;> simp [axv, xv, Finset.sum_apply, Pi.single_apply]

lemma azv_eq (A' : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) : azv A' i = ∑ l, A' i l • zv l := by
  funext s
  cases s <;> simp [azv, zv, Finset.sum_apply, Pi.single_apply]

def P (C : Matrix (Fin r) (Fin r) ℤ) : (Vec r →₀ ℤ) ⧸ S r := ∑ l, ∑ m, C l m • B r (xv l) (zv m)

lemma P_add (C D : Matrix (Fin r) (Fin r) ℤ) : P (C + D) = P C + P D := by
  simp [P, add_smul, Finset.sum_add_distrib]

lemma T1 (A V : Matrix (Fin r) (Fin r) ℤ) :
    ∑ i, ∑ j, V i j • B r (axv A i) (zv j) = P (A.transpose * V) := by

  simp only [P, axv_eq, map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, Matrix.mul_apply,
  Matrix.transpose_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun j _ => Finset.sum_comm).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]

lemma T3 (A' V : Matrix (Fin r) (Fin r) ℤ) :
    ∑ i, ∑ j, V i j • B r (xv i) (azv A' j) = P (V * A') := by

  simp only [P, azv_eq, map_sum, map_zsmul, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

lemma swapW (V : Matrix (Fin r) (Fin r) ℤ) (g : Fin r → Fin r → (Vec r →₀ ℤ) ⧸ S r) :
    ∑ i, ∑ j, V i j • g j i = ∑ i, ∑ j, V.transpose i j • g i j := by
  rw [Finset.sum_comm]; rfl

lemma per (A A' : Matrix (Fin r) (Fin r) ℤ) (i j : Fin r) :
    ∑ a : Fin 6, rosatiε a • B r (rosVec A A' a i) (rosVec A A' a j) =
      B r (axv A i) (zv j) + B r (zv i) (axv A j) - B r (xv i) (azv A' j) - B r (azv A' i) (xv j) := by
  simp [Fin.sum_univ_six, rosVec, rosatiε, map_add (f := _), LinearMap.add_apply]
  abel

theorem main {r : ℕ} (W A A' : Matrix (Fin r) (Fin r) ℤ)
    (h : A.transpose * (W + W.transpose) = (W + W.transpose) * A') :
    GlobalTheory.TensBal.sig W A A' ∈ Submodule.span ℤ
      (Set.range fun p : GlobalTheory.TensBal.Vec r × GlobalTheory.TensBal.Vec r × GlobalTheory.TensBal.Vec r =>
        GlobalTheory.TensBal.theta p.1 p.2.1 p.2.2) := by
  rw [← Submodule.Quotient.mk_eq_zero]
  have e : (Submodule.Quotient.mk (sig W A A') : (Vec r →₀ ℤ) ⧸ S r) =
      ∑ i, ∑ j, W i j • ∑ a : Fin 6, rosatiε a • B r (rosVec A A' a i) (rosVec A A' a j) := by
    rw [sig, ← Submodule.mkQ_apply]

    simp only [map_sum, map_zsmul, Submodule.mkQ_apply, ← B_apply, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => ?_
    rw [mul_comm]
  show (Submodule.Quotient.mk (sig W A A') : (Vec r →₀ ℤ) ⧸ S r) = 0
  rw [e]
  simp only [per, smul_sub, smul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have h2 : ∑ i, ∑ j, W i j • B r (zv i) (axv A j) = P (A.transpose * W.transpose) := by
    rw [← T1]; simp only [B_comm (zv _)]; exact swapW W (fun a b => B r (axv A a) (zv b))
  have h4 : ∑ i, ∑ j, W i j • B r (azv A' i) (xv j) = P (W.transpose * A') := by
    rw [← T3]; simp only [B_comm (azv A' _)]; exact swapW W (fun a b => B r (xv a) (azv A' b))
  rw [T1, h2, T3, h4, ← P_add, sub_sub, ← P_add, ← Matrix.add_mul, ← Matrix.mul_add, h, sub_self]

end GlobalTheory.TensBal.SpanPf

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TensBalUniq

open TopologicalSpace

variable {X X' Y : Scheme.{0}} {M : LB X} {M' : LB X'} {K₀ : Type} [Fintype K₀] {ψ : K₀ → (X' ⟶ X)} {δ : K₀ → ℤ}

theorem w_trans (w : LB.Iso M' (LB.LinComb M ψ δ)) (hw : w.IsGen) {Z : Scheme.{0}} (χ : Z ⟶ X') (z : Z)
    {jj jj' : K₀ → M.ι} {k k' : M'.ι} (h₁ : χ z ∈ LB.wchart M ψ jj) (h₁' : χ z ∈ LB.wchart M ψ jj')
    (h₂ : χ z ∈ M'.U k) (h₂' : χ z ∈ M'.U k') :
    gm χ z (LB.wchart M ψ jj ⊓ M'.U k) (w.s (jj, k)) =
      (∏ i, gm (χ ≫ ψ i) z (M.U (jj i) ⊓ M.U (jj' i)) (M.g (jj i) (jj' i)) ^ δ i) *
        (gm χ z (M'.U k ⊓ M'.U k') (M'.g k k'))⁻¹ * gm χ z (LB.wchart M ψ jj' ⊓ M'.U k') (w.s (jj', k')) := by
  have hm : χ z ∈ LB.wchart M ψ jj ⊓ M'.U k ⊓ (LB.wchart M ψ jj' ⊓ M'.U k') := ⟨⟨h₁, h₂⟩, h₁', h₂'⟩
  have e := congrArg (gm χ z (LB.wchart M ψ jj ⊓ M'.U k ⊓ (LB.wchart M ψ jj' ⊓ M'.U k'))) (hw (jj, k) (jj', k'))
  have d := gm_div M' (LB.LinComb M ψ δ) χ z (jj, k) (jj', k') hm
  have l := gm_linComb M ψ δ χ z jj jj' h₁ h₁'
  exact (gm_res χ z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (d.trans (congrArg₂ (· * ·) l rfl)) (gm_res χ z _ hm _))))

theorem prod_split {G : Type} [CommGroup G] {K : Type} [Fintype K] (ε : K → ℤ) (f : K × K₀ → G) :
    ∏ p, f p ^ (ε p.1 * δ p.2) = ∏ a, (∏ i, f (a, i) ^ δ i) ^ ε a := by
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← zpow_mul, mul_comm]

section Gen

variable {K : Type} [Fintype K] {φ' : K → (Y ⟶ X')} {ε : K → ℤ}

theorem chart_le (j : K × K₀ → M.ι) (q : K → M'.ι) (a : K) :
    LB.wchart M (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) j ⊓ LB.wchart M' φ' q ≤
      φ' a ⁻¹ᵁ (LB.div (LB.LinComb M ψ δ) M').U (fun k => j (a, k), q a) := fun _ hy =>
  ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.1 (a, k), Set.mem_iInter.1 hy.2 a⟩

def locU (w : LB.Iso M' (LB.LinComb M ψ δ)) (t' : LB.Gen (LB.LinComb M' φ' ε)) (j : K × K₀ → M.ι)
    (q : K → M'.ι) : Γ(Y, LB.wchart M (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) j ⊓ LB.wchart M' φ' q)ˣ :=
  (∏ a, res (chart_le j q a) (pullU (φ' a) _ (w.s (fun k => j (a, k), q a))) ^ ε a) * res inf_le_right (t'.s q)

theorem gm_locU (w : LB.Iso M' (LB.LinComb M ψ δ)) (t' : LB.Gen (LB.LinComb M' φ' ε)) (j : K × K₀ → M.ι)
    (q : K → M'.ι) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z)
    (hz : r z ∈ LB.wchart M (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) j ⊓ LB.wchart M' φ' q) :
    gm r z (LB.wchart M (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) j ⊓ LB.wchart M' φ' q) (locU w t' j q) =
      (∏ a, gm (r ≫ φ' a) z (LB.wchart M ψ (fun k => j (a, k)) ⊓ M'.U (q a))
        (w.s (fun k => j (a, k), q a)) ^ ε a) * gm r z (LB.wchart M' φ' q) (t'.s q) := by
  refine (map_mul (gm r z _) _ _).trans (congrArg₂ (· * ·) ((map_prod (gm r z _) _ _).trans
    (Finset.prod_congr rfl fun a _ => ?_)) ?_)
  · refine (map_zpow (gm r z _) _ _).trans (congrArg (· ^ ε a) ?_)
    have hm : r z ∈ φ' a ⁻¹ᵁ (LB.div (LB.LinComb M ψ δ) M').U (fun k => j (a, k), q a) := chart_le (δ := δ) j q a hz
    have h1 := gm_res r z (chart_le (δ := δ) j q a) hz (pullU (φ' a) _ (w.s (fun k => j (a, k), q a)))
    have h2 := gm_pull r (φ' a) z ((LB.div (LB.LinComb M ψ δ) M').U (fun k => j (a, k), q a)) hm
      (w.s (fun k => j (a, k), q a))
    exact h1.trans h2
  · exact gm_res r z (inf_le_right : LB.wchart M (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) j ⊓ LB.wchart M' φ' q ≤
      LB.wchart M' φ' q) hz (t'.s q)

theorem exists_gen_iso (hM : M.IsLB) (hM' : M'.IsLB) (w : LB.Iso M' (LB.LinComb M ψ δ)) (hw : w.IsGen)
    {t' : LB.Gen (LB.LinComb M' φ' ε)} (ht' : t'.IsGen) :
    ∃ u : LB.Gen (LB.LinComb M (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) (fun p => ε p.1 * δ p.2)), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → M.ι) (J' : (Z ⟶ X') → M'.ι), Good M z J →
        Good M' z J' → val u r z J = (∏ a, GlobalTheory.TensBal.isoV w z J J' (r ≫ φ' a) ^ ε a) * val t' r z J' := by
  have tr : ∀ (j : K × K₀ → M.ι) (q q' : K → M'.ι) (y : Y),
      y ∈ (LB.wchart M (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) j ⊓ LB.wchart M' φ' q) ⊓
        (LB.wchart M (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) j ⊓ LB.wchart M' φ' q') →
      gm (𝟙 Y) y _ (locU w t' j q) = gm (𝟙 Y) y _ (locU w t' j q') := by
    intro j q q' y hy
    rw [gm_locU w t' j q (𝟙 Y) y hy.1, gm_locU w t' j q' (𝟙 Y) y hy.2, gen_trans ht' (𝟙 Y) y hy.1.2 hy.2.2]
    simp only [trF, Category.id_comp]
    have e : ∀ a, gm (φ' a) y (LB.wchart M ψ (fun k => j (a, k)) ⊓ M'.U (q a)) (w.s (fun k => j (a, k), q a)) =
        (gm (φ' a) y (M'.U (q a) ⊓ M'.U (q' a)) (M'.g (q a) (q' a)))⁻¹ *
          gm (φ' a) y (LB.wchart M ψ (fun k => j (a, k)) ⊓ M'.U (q' a)) (w.s (fun k => j (a, k), q' a)) := by
      intro a
      have m := chart_le (δ := δ) j q a hy.1
      have m' := chart_le (δ := δ) j q' a hy.2
      rw [w_trans w hw (φ' a) y m.1 m.1 m.2 m'.2, Finset.prod_eq_one fun i _ => ?_, _root_.one_mul]
      exact (congrArg (· ^ δ i) (gm_self hM _ y (Set.mem_iInter.1 hy.1.1 (a, i)))).trans (one_zpow _)
    rw [Finset.prod_congr rfl fun a _ => congrArg (· ^ ε a) (e a)]
    simp only [mul_zpow, inv_zpow, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have glue : ∀ j : K × K₀ → M.ι, ∃ s : Γ(Y, LB.wchart M (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) j)ˣ,
      ∀ q, res inf_le_left s = locU w t' j q := fun j =>
    glue_unit _ (fun q => LB.wchart M (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) j ⊓ LB.wchart M' φ' q)
      (fun _ => inf_le_left) (fun y hy => by
        choose b hb using fun a => exists_chart hM' (φ' a y)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨b, hy, Set.mem_iInter.2 hb⟩) (locU w t' j) (tr j)
  choose s hs using glue
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K × K₀ → M.ι) (q : K → M'.ι)
      (hz : r z ∈ LB.wchart M (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) j ⊓ LB.wchart M' φ' q),
      gm r z _ (s j) = gm r z _ (locU w t' j q) := fun Z r z j q hz =>
    (gm_res r z inf_le_left hz (s j)).symm.trans (congrArg (gm r z _) (hs j q))
  refine ⟨⟨s⟩, fun j j' => unit_ext fun y hy => ?_, fun Z r z J J' hJ hJ' => ?_⟩
  · choose b hb using fun a => exists_chart hM' (φ' a y)
    have hq : y ∈ LB.wchart M' φ' b := Set.mem_iInter.2 hb
    erw [map_mul, gm_res _ y _ hy, gm_res _ y _ hy, gm_linComb M _ (fun p : K × K₀ => ε p.1 * δ p.2) (𝟙 Y) y j j' hy.1 hy.2]
    erw [hv Y (𝟙 Y) y j b ⟨hy.1, hq⟩, hv Y (𝟙 Y) y j' b ⟨hy.2, hq⟩, gm_locU w t' j b (𝟙 Y) y ⟨hy.1, hq⟩,
      gm_locU w t' j' b (𝟙 Y) y ⟨hy.2, hq⟩]
    simp only [Category.id_comp]
    have e : ∀ a, gm (φ' a) y (LB.wchart M ψ (fun k => j (a, k)) ⊓ M'.U (b a)) (w.s (fun k => j (a, k), b a)) =
        (∏ i, gm (φ' a ≫ ψ i) y (M.U (j (a, i)) ⊓ M.U (j' (a, i))) (M.g (j (a, i)) (j' (a, i))) ^ δ i) *
          gm (φ' a) y (LB.wchart M ψ (fun k => j' (a, k)) ⊓ M'.U (b a)) (w.s (fun k => j' (a, k), b a)) := by
      intro a
      have m := chart_le (δ := δ) j b a ⟨hy.1, hq⟩
      have m' := chart_le (δ := δ) j' b a ⟨hy.2, hq⟩
      rw [w_trans w hw (φ' a) y m.1 m'.1 m.2 m.2, gm_self hM' _ y m.2, inv_one, _root_.mul_one]
    rw [Finset.prod_congr rfl fun a _ => congrArg (· ^ ε a) (e a), prod_split ε]
    simp only [mul_zpow, Finset.prod_mul_distrib]
    rw [_root_.mul_assoc]
  · have hz : r z ∈ LB.wchart M (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) (fun p => J (r ≫ φ' p.1 ≫ ψ p.2)) ⊓
        LB.wchart M' φ' (fun a => J' (r ≫ φ' a)) := ⟨hJ.mem _ r, hJ'.mem φ' r⟩
    refine (hv Z r z _ _ hz).trans ((gm_locU w t' _ _ r z hz).trans ?_)
    refine congrArg (· * _) (Finset.prod_congr rfl fun a _ => congrArg (· ^ ε a) ?_)
    unfold GlobalTheory.TensBal.isoV
    have : (fun k => J ((r ≫ φ' a) ≫ ψ k)) = fun k => J (r ≫ φ' a ≫ ψ k) := funext fun k => by rw [Category.assoc]
    rw [this]
    rfl

end Gen

theorem iso_unique : ∀ {X X' Y S₀ : Scheme.{0}} {M : LB X} {M' : LB X'}, M.IsLB → M'.IsLB → ∀ {K₀ : Type} [Fintype K₀] {ψ : K₀ → (X' ⟶ X)} {δ : K₀ → ℤ} (w : LB.Iso M' (LB.LinComb M ψ δ)), w.IsGen → ∀ {K K₁ : Type} [Fintype K] [Fintype K₁] {φ' : K → (Y ⟶ X')} {ε : K → ℤ} {φ : K₁ → (Y ⟶ X)} {ε₁ : K₁ → ℤ}, FormEq (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) (fun p => ε p.1 * δ p.2) φ ε₁ → ∀ {t' : LB.Gen (LB.LinComb M' φ' ε)}, t'.IsGen → ∀ {t : LB.Gen (LB.LinComb M φ ε₁)}, t.IsGen → ∀ (p : Y ⟶ S₀) (e : S₀ ⟶ Y), e ≫ p = 𝟙 _ → Function.Surjective p.appTop.hom → (∀ (y : S₀) (J : (S₀ ⟶ X) → M.ι) (J' : (S₀ ⟶ X') → M'.ι), Good M y J → Good M' y J' → (∏ a, GlobalTheory.TensBal.isoV w y J J' (e ≫ φ' a) ^ ε a) * val t' e y J' = val t e y J) → ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → M.ι) (J' : (Z ⟶ X') → M'.ι), Good M z J → Good M' z J' → (∏ a, GlobalTheory.TensBal.isoV w z J J' (r ≫ φ' a) ^ ε a) * val t' r z J' = val t r z J := by
  intro X X' Y S₀ M M' hM hM' K₀ _ ψ δ w hw K K₁ _ _ φ' ε φ ε₁ hF t' ht' t ht p e he hp h Z r z J J' hJ hJ'
  obtain ⟨u, hu, hv⟩ := exists_gen_iso hM hM' w hw ht'
  have key := gen_unique' hM hF p e he hp ht hu (fun y I hI => by
    choose I' hI' using fun χ : S₀ ⟶ X' => exists_chart hM' (χ y)
    exact (h y I I' hI hI').symm.trans (hv _ e y I I' hI hI').symm) Z r z J hJ
  exact (hv Z r z J J' hJ hJ').symm.trans key.symm

end GlobalTheory.TensBalUniq
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.TrivLocus
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.lineBundleTrivialOnPullbackSquares_of_local : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (N : LB A.left), IsAbelianScheme A → N.IsLB → Out.Rigidified A N → ∀ (T : Scheme.{0}) (t : T ⟶ S), (∀ τ : T, ∃ V : T.Opens, τ ∈ V ∧ TrivCond A N V (V.ι ≫ t)) → TrivCond A N T t := by
  first | (exact @GlobalTheory.TrivLocus.trivCond_of_local) | (exact GlobalTheory.TrivLocus.trivCond_of_local) | (intros; apply GlobalTheory.TrivLocus.trivCond_of_local  <;> assumption)
end

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_semilinear_label_action_of_galois_deeper : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X₁ : USetup C) (D : UDeep X₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁), ∃ a : D.X.S.Gam ≃+ D.X.S.Gam, D.GalLab σ a ∧ ∀ x, a (D.lab x) = D.lab x := by
  first | exact @GlobalTheory.UPoinc.UGalAct.exists_galLab | exact GlobalTheory.UPoinc.UGalAct.exists_galLab | (intros; apply GlobalTheory.UPoinc.UGalAct.exists_galLab <;> assumption)

end
end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor


theorem _root_.GlobalTheory.T.rosatiValue_tensorData_transport_lambdaBundle : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N') (O : Type) [CommRing O] [StarRing O] (oa : D'.toPre.P.OAct O) (x : O) (ρ' : N'.A → N'.A → F), GlobalTheory.Relabel.RosV ν' oa x ρ' → ∃ ρ'' : N'.A → N'.A → F, GlobalTheory.Mum.TensRos.RosVT T ν ν' (oa.act (star x)) (oa.act x) ρ'' ∧ ∀ a b, ρ'' a b * (wv T ν ν' (GlobalTheory.Relabel.actV ν' oa (star x) a) * wv T ν ν' b * wv T ν ν' (a * GlobalTheory.Relabel.actV ν' oa x b)) = ρ' a b * (wv T ν ν' (GlobalTheory.Relabel.actV ν' oa (star x) a * b) * wv T ν ν' a * wv T ν ν' (GlobalTheory.Relabel.actV ν' oa x b)) := by
  first | exact @GlobalTheory.Mum.TensRosMove.rosVT_move | exact GlobalTheory.Mum.TensRosMove.rosVT_move | (intros; apply GlobalTheory.Mum.TensRosMove.rosVT_move <;> assumption)

end
end

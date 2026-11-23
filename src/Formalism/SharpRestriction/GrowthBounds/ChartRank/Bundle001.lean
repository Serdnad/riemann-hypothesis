module

public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.LocalToGlobal.GroupLattices.FockModels.SwRowGenMonomial
public import Formalism.SharpRestriction.GrowthBounds.ChartRank.HypVin
public import Formalism.SharpRestriction.GrowthBounds.ChartComparison.LocCore
import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.SelfDualCongr
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalRingCardinality.DataForms
public import Formalism.LocalRingCardinality.Bundle007
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.IsComplRatCompl
import Formalism.SharpRestriction.GrowthBounds.ChartRank.HypCard
import Formalism.SharpRestriction.GrowthBounds.ChartRank.HypInvLe
import Formalism.SharpRestriction.GrowthBounds.ChartRank.HypRankGe

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.G.CmpJ.PFormsCl

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms MvPolynomial NumberField IsDedekindDomain

section Tr

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem foNat_anti (lam : DomWeight n) : Antitone lam.natW := by
  intro a b hab
  have := lam.anti hab
  unfold DomWeight.natW
  exact Int.toNat_le_toNat (by omega)

theorem foRow_delSq (lam : DomWeight n) (g : Matrix (Fin n) (Fin n) ℂ) {q : MvPolynomial (Fin n × Fin n) ℂ}
    (hq : q ∈ delSq ℂ n lam) : Formalism.GradedWeylDivisibility.rowAct ℂ g q ∈ delSq ℂ n lam := by
  unfold delSq at hq ⊢
  rw [Formalism.L2.G.Model.sw_weyl_eq ℂ n n le_rfl _ (foNat_anti lam)] at hq ⊢
  exact Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ n n _ g q hq

def foTr {Gm : ι → Matrix (Fin n) (Fin n) ℂ} (g : ι → Matrix (Fin n) (Fin n) ℂ) (hg : ∀ τ, IsUnit (g τ).det)
    (y : Formalism.L2.Forms.Frames Gm) : Formalism.L2.Forms.Frames Gm :=
  (⟨fun τ => g τ * y.1 τ, fun τ => by rw [Matrix.det_mul]; exact (hg τ).mul (y.2 τ)⟩ :
    {y : ι → Matrix (Fin n) (Fin n) ℂ // ∀ τ, IsUnit (y τ).det})

def blockRowSubstitutionAlgHom (g : ι → Matrix (Fin n) (Fin n) ℂ) :
    MvPolynomial (ι × Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial (ι × Fin n × Fin n) ℂ :=
  aeval fun x => ∑ c : Fin n, C (g x.1 x.2.1 c) * X (x.1, c, x.2.2)

theorem blockRowSubstitution_X (g : ι → Matrix (Fin n) (Fin n) ℂ) (x : ι × Fin n × Fin n) :
    blockRowSubstitutionAlgHom g (X x) = ∑ c : Fin n, C (g x.1 x.2.1 c) * X (x.1, c, x.2.2) := by
  simp only [blockRowSubstitutionAlgHom, aeval_X]

theorem eval_blockRowSubstitution (g : ι → Matrix (Fin n) (Fin n) ℂ) (z : ι × Fin n × Fin n → ℂ) (P : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    eval z (blockRowSubstitutionAlgHom g P) = eval (fun x => ∑ c, g x.1 x.2.1 c * z (x.1, c, x.2.2)) P := by
  induction P using MvPolynomial.induction_on
  next a => simp [blockRowSubstitutionAlgHom]
  next p q hp hq => simp only [map_add (f := _), hp, hq]
  next p x hp => simp only [map_mul, hp, blockRowSubstitution_X, eval_X, map_sum, eval_C]

theorem blockRowSubstitution_rename (g : ι → Matrix (Fin n) (Fin n) ℂ) (τ : ι) (q : MvPolynomial (Fin n × Fin n) ℂ) :
    blockRowSubstitutionAlgHom g (rename (Prod.mk τ) q) = rename (Prod.mk τ) (Formalism.GradedWeylDivisibility.rowAct ℂ (g τ) q) := by
  have h : (blockRowSubstitutionAlgHom g).comp (rename (Prod.mk τ)) = (rename (Prod.mk τ)).comp (Formalism.GradedWeylDivisibility.rowAct ℂ (r := n) (n := n) (g τ)) := by
    apply MvPolynomial.algHom_ext
    intro v

    simp [blockRowSubstitutionAlgHom, Formalism.GradedWeylDivisibility.rowAct, rename_X, map_sum]
  exact congrArg (fun φ => φ q) h

theorem blockRowSubstitution_tensor (g : ι → Matrix (Fin n) (Fin n) ℂ) (f : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    blockRowSubstitutionAlgHom g (ten f) = ten fun τ => Formalism.GradedWeylDivisibility.rowAct ℂ (g τ) (f τ) := by
  simp only [ten, map_prod, blockRowSubstitution_rename]

theorem blockRowSubstitution_preserves_complexSpan (lam : ι → DomWeight n) (g : ι → Matrix (Fin n) (Fin n) ℂ) {P : MvPolynomial (ι × Fin n × Fin n) ℂ}
    (hP : P ∈ CSpan lam) : blockRowSubstitutionAlgHom g P ∈ CSpan lam := by
  have h : CSpan lam ≤ (CSpan lam).comap (blockRowSubstitutionAlgHom g).toLinearMap := by
    unfold CSpan
    rw [Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    exact Submodule.subset_span ⟨fun τ => Formalism.GradedWeylDivisibility.rowAct ℂ (g τ) (f τ), fun τ => foRow_delSq _ _ (hf τ), blockRowSubstitution_tensor g f⟩
  exact h hP

theorem foValC_tr {Gm : ι → Matrix (Fin n) (Fin n) ℂ} (lam : ι → DomWeight n) (g : ι → Matrix (Fin n) (Fin n) ℂ)
    (hg : ∀ τ, IsUnit (g τ).det) {v : Formalism.L2.Forms.Frames Gm → ℂ} (hv : v ∈ ValC Gm lam) :
    (fun y => v (foTr g hg y)) ∈ ValC Gm lam := by
  obtain ⟨P, hP, rfl⟩ := Submodule.mem_map.1 hv
  have h : (fun y => fnOf Gm (shiftOf lam) 1 P (foTr g hg y)) =
      (∏ τ, (g τ).det ^ shiftOf lam τ) • fnOf Gm (shiftOf lam) 1 (blockRowSubstitutionAlgHom g P) := by
    funext y
    simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul, foTr, Pi.one_apply, Matrix.one_mul, eval_blockRowSubstitution,
      Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib]
    simp only [Matrix.mul_apply]
    ring
  rw [h]
  exact Submodule.smul_mem _ _ (Submodule.mem_map_of_mem (blockRowSubstitution_preserves_complexSpan lam g hP))

end Tr

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T fT : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {ι : Type} [Fintype ι]

theorem foInf_unit (emb : ι → E →+* ℂ) (γ : GL (Fin n) E) (τ : ι) : IsUnit (atInf emb γ.1 τ).det := by
  have h := ((Matrix.isUnit_iff_isUnit_det _).1 γ.isUnit).map (emb τ)
  rwa [RingHom.map_det] at h

theorem foInf_mul (emb : ι → E →+* ℂ) (a b : Matrix (Fin n) (Fin n) E) (τ : ι) :
    atInf emb (a * b) τ = atInf emb a τ * atInf emb b τ := by
  simp [atInf, Matrix.map_mul]

theorem foInf_one (emb : ι → E →+* ℂ) (τ : ι) : atInf emb (1 : Matrix (Fin n) (Fin n) E) τ = 1 := by
  simp [atInf]

def foTrR (emb : ι → E →+* ℂ) (γ : GL (Fin n) E) (y : Formalism.L2.Forms.Frames (gramC J emb)) : Formalism.L2.Forms.Frames (gramC J emb) :=
  foTr (atInf emb γ.1) (foInf_unit emb γ) y

theorem foTrR_val (emb : ι → E →+* ℂ) (γ : GL (Fin n) E) (y : Formalism.L2.Forms.Frames (gramC J emb)) (τ : ι) :
    (foTrR emb γ y).1 τ = atInf emb γ.1 τ * y.1 τ := rfl

theorem foTrR_mul (emb : ι → E →+* ℂ) (γ δ : GL (Fin n) E) (y : Formalism.L2.Forms.Frames (gramC J emb)) :
    foTrR emb (γ * δ) y = foTrR emb γ (foTrR emb δ y) := by
  apply Subtype.ext
  funext τ
  show (foTrR emb (γ * δ) y).1 τ = (foTrR emb γ (foTrR emb δ y)).1 τ
  rw [foTrR_val, foTrR_val, foTrR_val, Units.val_mul, foInf_mul, Matrix.mul_assoc]

theorem foTrR_one (emb : ι → E →+* ℂ) (y : Formalism.L2.Forms.Frames (gramC J emb)) : foTrR emb 1 y = y := by
  apply Subtype.ext
  funext τ
  show (foTrR emb 1 y).1 τ = y.1 τ
  rw [foTrR_val, Units.val_one, foInf_one, Matrix.one_mul]

theorem foIsTr_iff (emb : ι → E →+* ℂ) (γ : GL (Fin n) E) (y' y : Formalism.L2.Forms.Frames (gramC J emb)) :
    IsTr (atInf emb γ) y' y ↔ y = foTrR emb γ y' := by
  constructor
  · intro h
    apply Subtype.ext
    funext τ
    exact h τ
  · intro h τ
    rw [h]
    rfl

def FoInv (S : StepLevel F E σ J T fT bad) (emb : ι → E →+* ℂ) (y0 : UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (v : Formalism.L2.Forms.Frames (gramC J emb) → ℂ) : Prop :=
  ∀ γ : GL (Fin n) E, γ ∈ UJ (σ : E →+* E) J → ∀ κ : S.U,
    y0.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y0.1 * κ.1 →
    ∀ y y' : Formalism.L2.Forms.Frames (gramC J emb), IsTr (atInf emb γ) y' y → v y = (S.chi κ : ℂ) * v y'

variable (S : StepLevel F E σ J T fT bad) (emb : ι → E →+* ℂ)


variable {S emb}

end Adelic

section Rec

open Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.PCard Formalism.MainNotions.G.CmpJ.PRankGe Formalism.MainNotions.G.CmpJ.PInvLe

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ} {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p}

end Rec

section Card

open Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.PCard Formalism.MainNotions.G.CmpJ.PRankGe Formalism.MainNotions.G.CmpJ.PInvLe

variable {D : D7} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}

end Card

end Formalism.MainNotions.G.CmpJ.PFormsCl
end
end

section

noncomputable section

namespace Formalism.MainNotions.G.CmpJ.PValIntN

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.G.RelativeIndexFlags Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.Herm.Herm0 D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w hg)} {Lv : Levels Fl} {j : ℕ}
  (hj : j + 1 ≤ D.R.m) {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P}

structure LatTies (w : D.what₂.places.Pl) (Fo : FormsIn M (j + 1) hj) (β : Fo.Ch)
    (Lb : Submodule (𝓞 D.host.E) (Fin (D.sp.X (j + 1)).rank → D.host.E)) : Prop where
  siteGood_prime_torsion : ¬ D.what₂.places.resChar w ∣ Fo.T
  Lb_eq : (Fo.K β).lev.Lb = reL (rankN D (j + 1) hj) Lb
  lat : ∀ cl : {c // Fo.chOf c = β}, Submodule.IsFullLattice D.host.E (Fo.lat cl.1)
  chi : ∀ κ : (Fo.K β).lev.U, ∃ r ∈ intW D.what₂.places w, r⁻¹ ∈ intW D.what₂.places w ∧
    D.what₂.embLL r = ((Fo.K β).lev.chi κ : ℂ)



theorem latIn_of {Fo : FormsIn M (j + 1) hj} {Lc : LocIn X u w hg Lv j Fo.Ch}
    {pos : (Σ v : Fin (Fl.Pj (j + 1)).nV, Fin ((Fl.Pj (j + 1)).n' v)) ≃ D.what₂.Tau} {β : Fo.Ch}
    (hfr : FrRatJ (Lc.t β) Lc.B) (H : LatTies hj w Fo β (Lc.Lb β)) : LatIn (stepInOf hj Fo Lc pos) w β :=
  { prime := hg.1
    resChar := rfl
    siteGood_prime_torsion := H.siteGood_prime_torsion
    alg := fun v a => (X.g u w hg).spl_alg _ ((X.g u w hg).pl v).2 a
    base := fun v t => frlat_re (rankN D (j + 1) hj) ((X.g u w hg).pl v).1 ((X.g u w hg).spl _ ((X.g u w hg).pl v).2) (Lc.Lb β)
      Lc.B ((Lc.t β).fr _ ((X.g u w hg).pl v).2) (hfr _ _) ((Lc.t β).fr_lat _ ((X.g u w hg).pl v).2) (Fo.K β).lev.Lb H.Lb_eq t
    lat := H.lat
    chi := H.chi }



theorem valIntN_rec {Fo : FormsIn M (j + 1) hj} {Lc : LocIn X u w hg Lv j Fo.Ch}
    {pos : (Σ v : Fin (Fl.Pj (j + 1)).nV, Fin ((Fl.Pj (j + 1)).n' v)) ≃ D.what₂.Tau} (e : D.what₂.LL →+* (D.gat u w hg).Kf)
    (HT : ∀ β, LocTies hj Fo Lc pos e β) (hS : BlockRationalityField) (hfrac : IsFractionRing (D.gat u w hg).O (D.gat u w hg).Kf)
    (hR0 : ∀ x, x ∈ intW D.what₂.places w ↔ e x ∈ Set.range (algebraMap (D.gat u w hg).O (D.gat u w hg).Kf))
    (HL : ∀ β, LatTies hj w Fo β (Lc.Lb β)) : (stepInOf hj Fo Lc pos).ValIntN e w :=
  valIntN_of (stepInOf hj Fo Lc pos) e w (fun β => core_of hj (HT β)) hS hfrac hR0
    (fun β => latIn_of hj (HT β).frRat (HL β))

end Formalism.MainNotions.G.CmpJ.PValIntN

end
end

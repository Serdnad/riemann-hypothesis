module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle070
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DetCondIffOfFieldExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle101
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle107
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle064
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle042
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle086
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyPadicIntRingHomOfIsAdicComplete
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelObjectOfDescendedData
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.TensorProduct.Nontrivial
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.WeilDown

def qf (W : Matrix (Fin 8) (Fin 8) ℤ) (v : Fin 8 → ℤ) : ℤ := ∑ u, ∑ u', W u u' * (v u * v u')

theorem sum_symm (W : Matrix (Fin 8) (Fin 8) ℤ) (v : Fin 8 → ℤ) :
    ∑ u, ∑ u', (W + W.transpose) u u' * (v u * v u') = 2 * qf W v := by
  simp only [Matrix.add_apply, Matrix.transpose_apply, add_mul, Finset.sum_add_distrib, two_mul, qf]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem qf_nonneg {W : Matrix (Fin 8) (Fin 8) ℤ} (hW : IsE8 W) (v : Fin 8 → ℤ) : 0 ≤ qf W v := by
  have h := hW.1.posSemidef.dotProduct_mulVec_nonneg (fun i => (v i : ℝ))
  have e : (((2 * qf W v : ℤ)) : ℝ) = star (fun i => (v i : ℝ)) ⬝ᵥ
      ((W + W.transpose).map (Int.cast : ℤ → ℝ)).mulVec (fun i => (v i : ℝ)) := by
    rw [← sum_symm]
    simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, star_trivial, Finset.mul_sum]
    push_cast
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [← e] at h
  have : (0 : ℤ) ≤ 2 * qf W v := by exact_mod_cast h
  omega

theorem qf_add (W : Matrix (Fin 8) (Fin 8) ℤ) (a b : Fin 8 → ℤ) :
    qf W (a + b) = qf W a + qf W b + b ⬝ᵥ (W + W.transpose).mulVec a := by
  simp only [qf, dotProduct, Matrix.mulVec, Matrix.add_apply, Matrix.transpose_apply, Pi.add_apply, add_mul,
    mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  have e₁ : ∑ u, ∑ u', W u u' * (b u * a u') = ∑ u, ∑ u', b u * (W u u' * a u') :=
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have e₂ : ∑ u, ∑ u', W u u' * (a u * b u') = ∑ u, ∑ u', b u * (W u' u * a u') := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [e₁, e₂]
  ring

theorem exists_qf_one {W : Matrix (Fin 8) (Fin 8) ℤ} (hW : IsE8 W) :
    ∃ a b, qf W (a + b) = qf W a + qf W b + 1 := by
  refine ⟨(W + W.transpose).adjugate.mulVec (Pi.single 0 1), Pi.single 0 1, ?_⟩
  rw [qf_add, Matrix.mulVec_mulVec, Matrix.mul_adjugate, hW.2]
  simp

theorem eq_of_zpow_qf {W : Matrix (Fin 8) (Fin 8) ℤ} (hW : IsE8 W) {U : Type*} [CommGroup U] (a b : U)
    (h : ∀ v, a ^ qf W v = b ^ qf W v) : a = b := by
  obtain ⟨v, w, e⟩ := exists_qf_one hW
  have := h (v + w)
  rw [e, zpow_add, zpow_add, zpow_add, zpow_add, h v, h w, zpow_one, zpow_one] at this
  exact mul_left_cancel this

theorem omegaStd_smul {h : ℕ} (m n : ℤ) (x y : Fin h ⊕ Fin h → ℤ) :
    omegaStd (m • x) (n • y) = m * n * omegaStd x y := by
  simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

section Pairing

open GlobalTheory.CechPic

variable {S : Scheme.{0}} {A : Over S} {T T' : Over S}

def q (π : Pic (A ⊗ A).left) (a b : T ⟶ A) : Pic T.left := pull (lift a b).left π

theorem qp (π : Pic (A ⊗ A).left) (t : T' ⟶ T) (a b : T ⟶ A) : pull t.left (q π a b) = q π (t ≫ a) (t ≫ b) := by
  rw [q, q, ← pull_comp, ← Over.comp_left, comp_lift]

theorem q_comm {π : Pic (A ⊗ A).left} (e : π = pull (lift (snd A A) (fst A A)).left π) (a b : T ⟶ A) :
    q π a b = q π b a := by
  have k : (lift b a).left ≫ (lift (snd A A) (fst A A)).left = (lift a b).left := by
    rw [← Over.comp_left, comp_lift, lift_fst, lift_snd]
  rw [q, q, ← k, pull_comp, ← e]

variable [GrpObj A]

theorem q_mul {P : LB (A ⊗ A).left} (hP : P.IsLB) (a a' b : T ⟶ A)
    (h : ∃ t : (LB.LinComb P (K := Fin 3) ![(lift (a * a') b).left, (lift a b).left, (lift a' b).left]
      ![1, -1, -1]).Gen, t.IsGen) : q (cls P hP) (a * a') b = q (cls P hP) a b + q (cls P hP) a' b := by
  have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 h
  rw [cls_linComb hP, Fin.sum_univ_three] at e
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul] at e
  rw [← sub_eq_zero, ← e, q, q, q]
  abel

theorem cls_theta {D : LB A.left} (hD : D.IsLB) (k : ℤ) (x : T ⟶ A) (h : (Out.thetaLB A D k x).IsLB) :
    cls _ h = k • pull (snd T A).left (cls D hD) + (-k) • pull ((fst T A ≫ x) * snd T A).left (cls D hD) := by
  refine (cls_linComb hD _ _ h).trans ?_
  rw [Fin.sum_univ_two]
  rfl

variable [IsCommMonObj A]

theorem q_zpow {π : Pic (A ⊗ A).left} (ql : ∀ a a' b : T ⟶ A, q π (a * a') b = q π a b + q π a' b)
    (a b : T ⟶ A) (n : ℤ) : q π (a ^ n) b = n • q π a b := by
  have := BilinCalc.map_prod_zpow (fun z => q π z b) (fun s t => ql s t b) (fun _ : Fin 1 => a) (fun _ => n)
  simpa using this

theorem exists_theta {π : Pic (A ⊗ A).left} {D : LB A.left} (hD : D.IsLB) (cD : cls D hD = q π (𝟙 A) (𝟙 A))
    (ql : ∀ a a' b : T ⊗ A ⟶ A, q π (a * a') b = q π a b + q π a' b) (qs : ∀ a b : T ⊗ A ⟶ A, q π a b = q π b a)
    (k : ℕ) (x : T ⟶ A) (hx : x ^ k = 1) (h0 : q π x x = 0) : ∃ θ : Out.ThetaGrp A D k T, θ.pt = x := by
  have hz : cls (Out.thetaLB A D k x) (LB.isLB_linComb hD _ _) = 0 := by
    have e₁ : q π (fst T A ≫ x) (fst T A ≫ x) = 0 := by
      rw [← qp, h0, map_zero]
    have e₂ : (k : ℤ) • q π (fst T A ≫ x) (snd T A) = 0 := by
      rw [← q_zpow ql, zpow_natCast, ← MonObj.comp_pow, hx, MonObj.comp_one, ← zpow_zero 1, q_zpow ql, zero_smul]
    refine (cls_theta hD _ _ _).trans ?_
    rw [cD, qp, qp, Category.comp_id, Category.comp_id, ql, qs (fst _ _ ≫ _), qs (snd _ _) (_ * _),
      ql, ql, e₁, qs (snd _ _) (fst _ _ ≫ _)]
    simp only [smul_add, neg_smul, e₂, smul_zero]
    abel
  obtain ⟨t, ht⟩ := (cls_eq_zero_iff _).1 hz
  exact ⟨⟨x, t, ht⟩, rfl⟩

end Pairing


open GlobalTheory.CechPic in
theorem weilIs_diag : Out.GlobalFnsSt → ∀ (h k : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (S : Scheme.{0}) (G A : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A] (pr : Fin 8 → (G ⟶ A)) (L : LB G.left) (P : LB (G2 A).left) (K : Type) [Field K] (p : Sp K ⟶ S) (lev : (Fin h ⊕ Fin h → ℤ) → (Over.mk p ⟶ A)) (c : Γ((Over.mk p).left, ⊤)ˣ), IsE8 W → IsAbelianScheme G → IsAbelianScheme A → (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) → L.IsLB → P.IsLB → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → (∀ (T : Over S) (x x' y : T ⟶ A), (∃ t : (LB.LinComb P (K := Fin 3) ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]).Gen, t.IsGen) ∧ ∃ t : (LB.LinComb P (K := Fin 3) ![(lift y (x * x')).left, (lift y x).left, (lift y x').left] ![1, -1, -1]).Gen, t.IsGen) → LBIso L (LB.LinComb P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) → (∀ x y, lev (x + y) = lev x * lev y) → (∀ x, lev x ^ k = 1) → (∀ (X Y : Fin 8 → (Fin h ⊕ Fin h → ℤ)) (y y' : Over.mk p ⟶ G), (∀ u, y ≫ pr u = lev (X u)) → (∀ u, y' ≫ pr u = lev (Y u)) → Out.WeilIs G L k y y' (c ^ ∑ u, ∑ v, (W + W.transpose) u v * omegaStd (X u) (Y v))) → ∀ x y, Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) k (lev x) (lev y) (c ^ (2 * omegaStd x y)) := by
  intro hG h k W S G A _ _ _ _ pr L P K _ p lev c hW hGab hA hpr hprod hL hP hsym hbi hLP hadd htor hweil x y
  have hD := pull_isLB hP (lift (𝟙 A) (𝟙 A)).left
  have ql : ∀ {T : Over S} (a a' b : T ⟶ A), q (cls P hP) (a * a') b = q (cls P hP) a b + q (cls P hP) a' b :=
    fun {T} a a' b => q_mul hP a a' b (hbi T a a' b).1
  have qs : ∀ {T : Over S} (a b : T ⟶ A), q (cls P hP) a b = q (cls P hP) b a :=
    q_comm ((cls_eq_iff hP (pull_isLB hP _)).2 hsym)
  have cD : cls _ hD = q (cls P hP) (𝟙 A) (𝟙 A) := rfl
  have q0 : ∀ a b : Over.mk p ⟶ A, q (cls P hP) a b = 0 := fun a b =>
    (cls_eq_zero_iff (pull_isLB hP (lift a b).left)).2 (DVR.exists_gen_of_local (V := K) P hP _ _)
  have lift_ : ∀ z, ∃ θ : Out.ThetaGrp A (P.pull (lift (𝟙 A) (𝟙 A)).left) k (Over.mk p), θ.pt = lev z := fun z =>
    exists_theta hD cD ql qs k _ (htor z) (q0 _ _)
  have loc : ∀ z (s : (Over.mk p).left), ∃ V : (Over.mk p).left.Opens, s ∈ V ∧
      ∃ θ : Out.ThetaGrp A (P.pull (lift (𝟙 A) (𝟙 A)).left) k (Out.overRes V), θ.pt = Out.overResι V ≫ lev z :=
    fun z s => by
      obtain ⟨θ, e⟩ := lift_ z
      obtain ⟨θ', e'⟩ := CommutatorPairing.exists_pull hD θ (Out.overResι ⊤)
      exact ⟨⊤, trivial, θ', by rw [e', e]⟩
  obtain ⟨c₀, hc₀⟩ := CommutatorPairing.exists_weilIs hG hA hD (loc x) (loc y)
  suffices c₀ = c ^ (2 * omegaStd x y) from this ▸ hc₀
  refine eq_of_zpow_qf hW _ _ fun v => ?_
  have levz : ∀ z (n : ℤ), lev (n • z) = lev z ^ n := fun z n => by
    let F : Multiplicative (Fin h ⊕ Fin h → ℤ) →* (Over.mk p ⟶ A) :=
      MonoidHom.mk' (fun w => lev w.toAdd) fun a b => hadd _ _
    exact map_zpow F (Multiplicative.ofAdd z) n
  obtain ⟨ψ, hψ, -⟩ := hprod A fun u => 𝟙 A ^ v u
  have ext : ∀ {T : Over S} (a b : T ⟶ G), (∀ u, a ≫ pr u = b ≫ pr u) → a = b := fun {T} a b e =>
    (hprod T fun u => b ≫ pr u).unique e fun _ => rfl
  have hc : ∀ {T : Over S} (a : T ⟶ A) u, (a ≫ ψ) ≫ pr u = a ^ v u := fun a u => by
    rw [Category.assoc, hψ, GrpObj.comp_zpow, Category.comp_id]
  have hmon : IsMonHom ψ := by
    constructor
    · refine ext _ _ fun u => ?_
      have e₁ : (η[A] : 𝟙_ _ ⟶ A) = 1 := by rw [Hom.one_def]; simp
      rw [hc, IsMonHom.one_hom, e₁, one_zpow]
    · refine ext _ _ fun u => ?_
      have e₁ : μ[A] = fst A A * snd A A := by rw [Hom.mul_def]; simp
      have e₂ : (ψ ⊗ₘ ψ) ≫ μ[G] = (fst A A ≫ ψ) * (snd A A ≫ ψ) := by rw [Hom.mul_def]; congr 1
      rw [hc, e₁, e₂, MonObj.mul_comp, hc, hc, mul_zpow]
  have hd : ((qf W v).toNat : ℤ) = qf W v := Int.toNat_of_nonneg (qf_nonneg hW v)
  have hn : (lbPow (P.pull (lift (𝟙 A) (𝟙 A)).left) (qf W v).toNat).IsLB := LB.isLB_linComb hD _ _
  have hiso : LBIso (lbPow (P.pull (lift (𝟙 A) (𝟙 A)).left) (qf W v).toNat) (L.pull ψ.left) := by

    rw [← cls_eq_iff hn (pull_isLB hL _), cls_lbPow hD, cD, cls_pull hL,
    (cls_eq_iff hL (LB.isLB_linComb hP _ _)).2 hLP, cls_linComb hP, map_sum, ← natCast_zsmul, hd, qf,
    ← Fintype.sum_prod_type', Finset.sum_smul]
    refine Finset.sum_congr rfl fun uv _ => ?_
    rw [map_zsmul]
    refine Eq.trans ?_ (congrArg _ (qp (cls P hP) ψ (pr uv.1) (pr uv.2))).symm
    rw [hψ, hψ, q_zpow ql, qs _ (_ ^ _), q_zpow ql, smul_smul, smul_smul, _root_.mul_assoc]
  have key := (weilIs_along_hom hG S A G ψ _ L _ k _ (lev x) (lev y) c₀ _ hA hGab hD hL hmon hiso
    (hweil (fun u => v u • x) (fun u => v u • y) _ _ (fun u => by rw [hc, levz]) (fun u => by rw [hc, levz]))).2 hc₀
  rw [← hd, zpow_natCast, ← key, hd, ← zpow_mul]
  congr 1
  have e : ∀ a b : ℤ, a * (b * omegaStd x y) = a * b * omegaStd x y := fun a b => (_root_.mul_assoc _ _ _).symm
  simp only [omegaStd_smul, e, ← Finset.sum_mul]
  rw [sum_symm]
  ring

end GlobalTheory.WeilDown
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.PELDesc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

def tateAlong {k : Type} [Field k]
    {Q Q' : Type} [Group Q] [Group Q'] {act : 𝓞 E → Q → Q} {act' : 𝓞 E → Q' → Q'}
    {e : ℕ → Q → Q → kˣ → Prop} {e' : ℕ → Q' → Q' → kˣ → Prop} (Φ : Q ≃* Q')
    (hact : ∀ c x, Φ (act c x) = act' c (Φ x)) (he : ∀ n x y c, e n x y c → e' n (Φ x) (Φ y) c)
    (I : TateIso D k Q act e) : TateIso D k Q' act' e' where
  ζ := I.ζ
  ζ_prim := I.ζ_prim
  ζ_pow := I.ζ_pow
  ev := fun n a => Φ (I.ev n a)
  add := fun n a b => by simp only [I.add, map_mul]
  lin := fun n c a => by rw [← hact, I.lin]
  ker := fun n hn a => (map_eq_one_iff _ Φ.injective).trans (I.ker n hn a)
  onto := fun n hn x => by
    rw [← map_eq_one_iff Φ.symm Φ.symm.injective, map_pow, I.onto n hn]
    exact exists_congr fun a => Φ.eq_symm_apply
  tower := fun n m hn hm a => by rw [← map_pow, I.tower n m hn hm a]
  isom := fun n hn a b => he _ _ _ _ (I.isom n hn a b)

theorem tate_pull {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] [IsCommMonObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB)
    (h : IsGrpPullback G' G f φ) (hI : LBIso L' (L.pull φ)) (act : 𝓞 E → (G ⟶ G)) (act' : 𝓞 E → (G' ⟶ G'))
    (hact : ∀ c, (act' c).left ≫ φ = φ ≫ (act c).left) {k : Type} [Field k] (x : Sp k ⟶ S') (y : Sp k ⟶ S)
    (hy : y = x ≫ f) :
    (∀ I' : TateIso D k (Over.mk x ⟶ G') (fun c z => z ≫ act' c) (fun n z z' c => Out.WeilIs G' L' n z z' (unitOn c)),
      ∃ I : TateIso D k (Over.mk y ⟶ G) (fun c z => z ≫ act c) (fun n z z' c => Out.WeilIs G L n z z' (unitOn c)),
        I.ζ = I'.ζ ∧ ∀ n v, (I.ev n v).left = (I'.ev n v).left ≫ φ) ∧
    (∀ I : TateIso D k (Over.mk y ⟶ G) (fun c z => z ≫ act c) (fun n z z' c => Out.WeilIs G L n z z' (unitOn c)),
      ∃ I' : TateIso D k (Over.mk x ⟶ G') (fun c z => z ≫ act' c) (fun n z z' c => Out.WeilIs G' L' n z z' (unitOn c)),
        I'.ζ = I.ζ ∧ ∀ n v, (I.ev n v).left = (I'.ev n v).left ≫ φ) := by
  subst hy
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.LiePull.exists_pushEquiv h (Over.mk x) (x ≫ f) rfl
  have hA : ∀ (c : 𝓞 E) (z : Over.mk x ⟶ G'), Φ (z ≫ act' c) = Φ z ≫ act c := by
    intro c z
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, hΦ, Category.assoc, hact]
  have hA' : ∀ (c : 𝓞 E) (z : Over.mk (x ≫ f) ⟶ G), Φ.symm (z ≫ act c) = Φ.symm z ≫ act' c := by
    intro c z
    apply Φ.injective
    rw [MulEquiv.apply_symm_apply, hA, MulEquiv.apply_symm_apply]
  have hW : ∀ (n : ℕ) (z z' : Over.mk x ⟶ G') (c : kˣ),
      (Out.WeilIs G' L' n z z' (unitOn c) ↔ Out.WeilIs G L n (Φ z) (Φ z') (unitOn c)) := fun n z z' c =>
    GlobalTheory.weilIs_grpPullback_of_comm S S' G G' f φ L L' hL hL' h hI (Over.mk x) n z z' (Φ z) (Φ z') (unitOn c)
      (hΦ z) (hΦ z')
  refine ⟨fun I' => ⟨tateAlong Φ hA (fun n z z' c hz => (hW n z z' c).1 hz) I', rfl, fun n v => hΦ _⟩,
    fun I => ⟨tateAlong Φ.symm hA' (fun n z z' c hz => ?_) I, rfl, fun n v => ?_⟩⟩
  · rw [hW, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    exact hz
  · show _ = (Φ.symm (I.ev n v)).left ≫ φ
    rw [← hΦ, MulEquiv.apply_symm_apply]

theorem detCond_pull {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (a : OAct (𝓞 E) G) (a' : OAct (𝓞 E) G')
    (hact : ∀ c, (a'.act c).left ≫ φ = φ ≫ (a.act c).left) {k : Type} [Field k] (x : Sp k ⟶ S') (y : Sp k ⟶ S)
    (hy : y = x ≫ f) (ρ : k) : DetCond D a' x ρ ↔ DetCond D a y ρ := by
  subst hy
  have key : ∀ (σ : 𝓞 E →+* k) (n : ℕ), LieMult a' x σ n ↔ LieMult a (x ≫ f) σ n := fun σ n =>
    GlobalTheory.LiePull.lieMult_pull (𝓞 E) S S' G G' f φ a a' h hact k x σ n
  exact forall_congr' fun σ => and_congr (imp_congr_right fun _ => key σ _) (imp_congr_right fun _ => key σ _)

private theorem spMap_comp_var2 {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R')
    (g : R' →+* R'') : spMap g ≫ spMap f = spMap (g.comp f) := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

private theorem exists_algClosed_amalgam_of_charZero {K₀ K K' : Type} [Field K₀] [Field K] [Field K'] [CharZero K'] (i : K₀ →+* K)
    (κ : K₀ →+* K') : ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (_ : CharZero Ω) (iK : K →+* Ω) (iK' : K' →+* Ω),
      iK.comp i = iK'.comp κ := by
  let := i.toAlgebra
  let := κ.toAlgebra
  have : Nontrivial (K ⊗[K₀] K') :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain K₀ K K' i.injective κ.injective
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[K₀] K')
  let : Field (K ⊗[K₀] K' ⧸ m) := Ideal.Quotient.field m
  let q : K ⊗[K₀] K' →+* AlgebraicClosure (K ⊗[K₀] K' ⧸ m) :=
    (algebraMap (K ⊗[K₀] K' ⧸ m) (AlgebraicClosure (K ⊗[K₀] K' ⧸ m))).comp (Ideal.Quotient.mk m)
  let jL : K →+* K ⊗[K₀] K' := (Algebra.TensorProduct.includeLeft : K →ₐ[K₀] K ⊗[K₀] K').toRingHom
  let jR : K' →+* K ⊗[K₀] K' := (Algebra.TensorProduct.includeRight : K' →ₐ[K₀] K ⊗[K₀] K').toRingHom
  refine ⟨AlgebraicClosure (K ⊗[K₀] K' ⧸ m), inferInstance, inferInstance,
    charZero_of_injective_ringHom (q.comp jR).injective, q.comp jL, q.comp jR, ?_⟩
  ext a
  have hL := (Algebra.TensorProduct.includeLeft : K →ₐ[K₀] K ⊗[K₀] K').commutes a
  have hR := (Algebra.TensorProduct.includeRight : K' →ₐ[K₀] K ⊗[K₀] K').commutes a
  exact congrArg q (hL.trans hR.symm)

theorem isPEL_descends : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g k : ℕ) (J : Type) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (o : Type) [CommRing o] (b : TBase o k) (ρ : o) (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (β₀ : o →+* K₀) (s : Sp K ⟶ Sp o) (t₀ : TObj g k J b (spMap β₀)) (t : TObj g k J b s) (τ : SAB H (Sp K)), Subring.closure (Set.range a) = ⊤ → s = spMap i ≫ spMap β₀ → TMap t t₀ (spMap i) → IsPEL D a bas ρ t τ → ∃ τ₀ : SAB H (Sp K₀), IsPEL D a bas ρ t₀ τ₀ := by
  intro hL E _ _ _ H D g k J a bas o _ b ρ K₀ K _ _ i β₀ s t₀ t τ hcl hs hT hP
  obtain ⟨φ, hφ, hLφ, hactφ, hgeo⟩ := hP
  obtain ⟨ψ, hψ, hLψ, hptψ, hactψ⟩ := hT
  have := t₀.ab.comm
  have := hφ

  have hpb : IsGrpPullback τ.G t₀.A (spMap i) (φ.hom.left ≫ ψ) :=
    IsGrpPullback.congr (IsGrpPullback.comp (isGrpPullback_of_iso φ) hψ) (Category.id_comp _) rfl
  have hLc : LBIso τ.PP.L (t₀.L.pull (φ.hom.left ≫ ψ)) := by
    obtain ⟨w, hw⟩ := hLψ
    have h2 : LBIso (t.L.pull φ.hom.left) (t₀.L.pull (φ.hom.left ≫ ψ)) :=
      iso_linComb ((isGen_iff w).1 hw) (K := PUnit) (fun _ => φ.hom.left) (fun _ => 1)
    exact LBIso.trans τ.PP.isLB (pull_isLB t.isLB _) (pull_isLB t₀.isLB _) hLφ h2
  have hφl : ∀ j, (τ.act.act (a j)).left ≫ φ.hom.left = φ.hom.left ≫ (t.act j).left := fun j => by
    rw [← Over.comp_left, hactφ j, Over.comp_left]
  obtain ⟨r, hr1, hr2⟩ := GlobalTheory.oAct_descend_of_generators (𝓞 E) J a K₀ K i t₀.A τ.G (φ.hom.left ≫ ψ) τ.act t₀.act
    hcl hpb (fun j => by rw [← Category.assoc, hφl j, Category.assoc, hactψ j, Category.assoc])
  obtain ⟨τ₀, e, he, hLe, hacte⟩ :=
    GlobalTheory.exists_triple_of_fieldExtension hL E H K₀ K i τ t₀.A (φ.hom.left ≫ ψ) t₀.L r t₀.ab hpb t₀.isLB hLc hr2
  have := he
  have hel : ∀ c, (τ₀.act.act c).left ≫ e.hom.left = e.hom.left ≫ (r.act c).left := fun c => by
    rw [← Over.comp_left, hacte c, Over.comp_left]
  have hpe : IsGrpPullback τ₀.G t₀.A (𝟙 _) e.hom.left := isGrpPullback_of_iso e
  refine ⟨τ₀, e, he, hLe, fun j => by rw [hacte, hr1], ?_⟩
  intro K' _ _ _ x' β hx'

  set κ : K₀ →+* K' := (Spec.preimage x').hom with hκ
  have hxκ : x' = spMap κ := by
    show x' = Spec.map (CommRingCat.ofHom (Spec.preimage x').hom)
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have hβ : κ.comp β₀ = β := by
    have h1 : spMap (κ.comp β₀) = spMap β := by rw [← spMap_comp_var2, ← hxκ, hx']
    have h2 := Spec.map_injective h1
    exact congrArg CommRingCat.Hom.hom h2
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exfalso
      have hu := b.unit.map β
      rw [h0, Nat.cast_zero, map_zero] at hu
      exact not_isUnit_zero hu
    · exact h0

  obtain ⟨Ω, _, _, _, iK, iK', hΩ⟩ := exists_algClosed_amalgam_of_charZero i κ
  have hsq : spMap iK' ≫ x' = spMap iK ≫ spMap i := by
    rw [hxκ, spMap_comp_var2, spMap_comp_var2, hΩ]
  have hsΩ : spMap iK ≫ s = spMap (iK.comp (i.comp β₀)) := by
    rw [hs, ← Category.assoc, spMap_comp_var2, spMap_comp_var2]
  have hbr : ∀ z : o, iK (i (β₀ z)) = iK' (β z) := fun z => by
    rw [← hβ]
    exact congrArg (fun F : K₀ →+* Ω => F (β₀ z)) hΩ
  obtain ⟨hdet, I₀, hI₀ζ, hI₀ev⟩ := hgeo Ω (spMap iK) (iK.comp (i.comp β₀)) hsΩ
  have := t₀.dim
  have : Smooth t₀.A.hom := SmoothOfRelativeDimension.smooth g t₀.A.hom
  refine ⟨?_, ?_⟩
  ·
    have d1 := (detCond_pull hpb r τ.act hr2 (spMap iK) (spMap iK' ≫ x') hsq
      ((iK.comp (i.comp β₀)) ρ)).1 hdet
    have d2 : DetCond D r (spMap iK' ≫ x') (iK' (β ρ)) := by
      rw [← hbr ρ]
      exact d1
    have d3 := (GlobalTheory.detCond_iff_of_field_extension E H D (Sp K₀) t₀.A K' Ω iK' x' r (β ρ) inferInstance).1 d2
    exact (detCond_pull hpe r τ₀.act hel x' x' (Category.comp_id _).symm (β ρ)).2 d3
  ·
    obtain ⟨I₁, hI₁ζ, hI₁ev⟩ := (tate_pull t₀.isLB τ.PP.isLB hpb hLc r.act τ.act.act hr2 (spMap iK)
      (spMap iK' ≫ x') hsq).1 I₀
    obtain ⟨I, hI⟩ := (GlobalTheory.TateIsoFieldExt.tateIso_fieldExt hL E H D (Sp K₀) t₀.pol r.act K' Ω iK' x').2 I₁ r.hom
    obtain ⟨I', hI'ζ, hI'ev⟩ := (tate_pull t₀.isLB τ₀.PP.isLB hpe hLe r.act τ₀.act.act hel x' x'
      (Category.comp_id _).symm).2 I
    refine ⟨I', ?_, fun j => ?_⟩
    · rw [hI'ζ]
      apply iK'.injective
      rw [← (hI k hk).1, hI₁ζ, hI₀ζ]
      simp only [RingHom.comp_apply]
      exact hbr _
    · apply Over.OverMorphism.ext
      rw [Over.comp_left, ← hI'ev]
      show (I.ev k (bas (Pi.single j 1))).left = x' ≫ (t₀.pt j).left
      have ep := ((GlobalTheory.FieldBaseChange.epi_and_isMonHom_iff K' Ω iK').1 (Sp K') (Sp Ω) (𝟙 _) (𝟙 _) (spMap iK')
        IsPullback.of_id_snd).1
      apply ep.left_cancellation
      have e1 : (I₁.ev k (bas (Pi.single j 1))).left = spMap iK' ≫ (I.ev k (bas (Pi.single j 1))).left := by
        rw [(hI k hk).2 (bas (Pi.single j 1)), Over.comp_left]
        rfl
      have e2 : (I₀.ev k (bas (Pi.single j 1))).left ≫ φ.hom.left = spMap iK ≫ (t.pt j).left := by
        rw [← Over.comp_left, hI₀ev j, Over.comp_left]
        rfl
      rw [← e1, hI₁ev, ← Category.assoc, e2, Category.assoc, hptψ j, ← Category.assoc, ← hsq, Category.assoc]
      rfl

end GlobalTheory.PELDesc
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SS

theorem semistablePol_of_padic : GlobalTheory.Published.SemistableReductionSt → GlobalTheory.SS.SemistablePol := by
  intro H V K _ _ _ _ _ _ _ _ hfin A
  obtain ⟨p, hp, K₀, e, e₀, hK₀, he⟩ := GlobalTheory.completeDVR_eq_integralClosure_padicInt.1 V K hfin
  obtain ⟨P, ψ, hψ⟩ : ∃ (P : PolAV (Sp K₀)) (ψ : P.A.left ⟶ A.A.left),
      IsGrpPullback P.A A.A (spMap e.toRingHom) ψ := by
    obtain ⟨P', g, hg, -, hm, -⟩ := GlobalTheory.polBaseChange_holds _ _ (spMap e.toRingHom) A
    refine ⟨P', g, hg, fun T x y x₀ y₀ hx hy => ?_⟩
    rw [(Over.OverMorphism.ext hx : x₀ = Out.toBase hg.w x), (Over.OverMorphism.ext hy : y₀ = Out.toBase hg.w y), ← hm]
    rfl
  obtain ⟨K', h, hloc, hK', G, gG, hG, hE, φ, hφ⟩ :=
    GlobalTheory.exists_semiAbelian_model_split_specialFibre H p K₀ P
  obtain ⟨hdvr, hfr, hc, f, hf, hlf, hfx⟩ := GlobalTheory.completeDVR_eq_integralClosure_padicInt.2 p K₀ K' h hK'
  letI aV : Algebra V (integralClosure ℤ_[p] K') := (f.comp e₀.toRingHom).toAlgebra
  letI aK : Algebra K K' := ((IntermediateField.inclusion h).toRingHom.comp e.toRingHom).toAlgebra
  refine ⟨integralClosure ℤ_[p] K', K', inferInstance, inferInstance, hdvr, inferInstance, aV, inferInstance, aK, hfr,
    ?_, ?_, ?_, hc, G, gG, ?_, hG, hE⟩
  · ext1 x
    change ((f (e₀ x) : integralClosure ℤ_[p] K') : K') = IntermediateField.inclusion h (e (algebraMap V K x))
    rw [hfx, he]
  · exact RingHom.Finite.comp hf (RingHom.Finite.of_surjective _ e₀.surjective)
  · haveI : IsLocalHom e₀.toRingHom := isLocalHom_of_leftInverse e₀.symm.toRingHom e₀.left_inv
    exact RingHom.isLocalHom_comp f e₀.toRingHom
  · obtain ⟨i, hi, -⟩ := grpPullback_iso
      ((hφ.comp hψ).congr (GlobalTheory.SplitReduction.spMap_comp _ _) rfl)
      (isGrpPullback_pullback A.A (spMap (algebraMap K K')))
    exact ⟨i, hi⟩

end GlobalTheory.SS
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem _root_.GlobalTheory.T.exists_siegelObject_of_descended_data : ∀ (h M : ℕ) (o : Type) [CommRing o] (ζ : o) (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (s₀ : Sp K₀ ⟶ Sp o) (s : Sp K ⟶ Sp o) (c : SiegPre h M ζ s) (A₀ : Over (Sp K₀)) [GrpObj A₀] (φ : c.A.left ⟶ A₀.left) (φ₂ : (G2 c.A).left ⟶ (G2 A₀).left) (P₀ : LB (G2 A₀).left) (lev₀ : Fin h ⊕ Fin h → (𝟙_ (Over (Sp K₀)) ⟶ A₀)), s = spMap i ≫ s₀ → IsGrpPullback c.A A₀ (spMap i) φ → IsSquare φ φ₂ → P₀.IsLB → LBIso c.P (P₀.pull φ₂) → (∀ u, (c.lev (Pi.single u 1)).left ≫ φ = spMap i ≫ (lev₀ u).left) → ∃ c₀ : SiegPre h M ζ s₀, SiegPB c c₀ (spMap i) := by
  first | exact @GlobalTheory.exists_siegPre_of_descended_data | exact GlobalTheory.exists_siegPre_of_descended_data | (intros; apply GlobalTheory.exists_siegPre_of_descended_data <;> assumption)
end

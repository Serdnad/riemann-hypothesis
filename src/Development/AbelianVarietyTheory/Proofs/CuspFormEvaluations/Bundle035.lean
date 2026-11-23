module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle030
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle028
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle029
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle031
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle010
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.analyticFrame_of_appellHumbertFramePeriodFamily : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (σ' : KA l →+* ℂ) (F : FamilyUnif Xo σ' ty) (i : Fin F.n) (Pm : (F.Di i).La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ), IsPeriod (F.Di i) ty Pm → y.x = F.u i Pm → AHFrame F i Pm Hm χl fr → (∀ ℓ : Lt1 Dw, IsDerivAt0 (fun z => (F.ex i Pm z).left) (Pi.single (el.symm ℓ) 1) (y.u ℓ.1 ℓ.2)) → ∃ Φ : AnPt y g ty el, Φ.OfFam F i Pm ∧ Φ.Hm = Hm ∧ Φ.χ = χl ∧ Φ.fr = fr ∧ (∀ (α : 𝓞 E) a, Pm (F.t i (α • a)) = tyAct ty α (Pm (F.t i a))) ∧ ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), levPt Xo y.x a = Φ.e ((l.M : ℂ)⁻¹ • Pm (F.t i a)) := by
  first | exact @GlobalTheory.AnVal.anPt_of_family | exact GlobalTheory.AnVal.anPt_of_family | (intros; apply GlobalTheory.AnVal.anPt_of_family <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnVal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal

attribute [local instance] Over.cartesianMonoidalCategory

theorem isHolFam_precomp_clm {Y : Scheme.{0}} {g N : ℕ} (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e)
    (A : (Fin N → ℂ) →L[ℂ] (Fin g → ℂ)) : IsHolFam (fun v => e (A v)) := by
  intro U f
  obtain ⟨h1, h2⟩ := hol U f
  exact ⟨h1.preimage A.continuous, h2.comp A.differentiable.differentiableOn fun _ hv => hv⟩

def colPr (n g : ℕ) (i : Fin n) : (Fin (n * g) → ℂ) →L[ℂ] (Fin g → ℂ) :=
  ContinuousLinearMap.pi fun j =>
    ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n * g) => ℂ) (finProdFinEquiv (i, j))

theorem colPr_apply (n g : ℕ) (i : Fin n) (v : Fin (n * g) → ℂ) (j : Fin g) :
    colPr n g i v j = v (finProdFinEquiv (i, j)) := rfl

theorem anLin_colPr (n g : ℕ) (i : Fin n) (p : Fin 1 × Fin g) :
    anLin (colPr n g i) p = MvPolynomial.X ((0 : Fin 1), finProdFinEquiv (i, p.2)) := by
  rw [anLin, Finset.sum_eq_single (finProdFinEquiv (i, p.2))]
  · rw [colPr_apply, Pi.single_eq_same, map_one, _root_.one_mul]
  · intro k _ hk
    simp [colPr_apply, Ne.symm hk]
  · simp

theorem renN_colPr (n g m : ℕ) (i : Fin n) (a : Jet ℂ (Fin 1 × Fin g) m) :
    renN n g m (jetMap (anLin (colPr n g i)) (anLin_mem _) a) = jetCopy (S := ℂ) g m i a := by
  unfold renN jetCopy
  exact anJetMap_comp _ _ _ _ _ _
    (fun p => by simp only [anLin_colPr, MvPolynomial.aeval_X, Equiv.symm_apply_apply]) a

theorem jetCopy_one_zero (g m : ℕ) (a : Jet ℂ (Fin 1 × Fin g) m) : jetCopy (S := ℂ) g m (0 : Fin 1) a = a := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  show Ideal.Quotient.mk _ (MvPolynomial.aeval (fun q : Fin 1 × Fin g =>
    (MvPolynomial.X ((0 : Fin 1), q.2) : MvPolynomial (Fin 1 × Fin g) ℂ)) p) = _
  have h : (fun q : Fin 1 × Fin g => (MvPolynomial.X ((0 : Fin 1), q.2) : MvPolynomial (Fin 1 × Fin g) ℂ)) =
      MvPolynomial.X := by
    funext q
    congr 1
    exact Prod.ext (Subsingleton.elim _ _) rfl
  rw [h, MvPolynomial.aeval_X_left_apply]

theorem spMap_jetCopy_jetPt {Y : Scheme.{0}} {g : ℕ} (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e)
    (n m : ℕ) (i : Fin n) :
    spMap (jetCopy (S := ℂ) g m i : Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin n × Fin g) m) ≫ jetPt e hol m =
      spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) ≫
        jetPt (fun v => e (colPr n g i v)) (isHolFam_precomp_clm e hol _) m := by
  have hring : ((jetCopy (S := ℂ) g m i : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin n × Fin g) m) :
      Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin n × Fin g) m) =
      (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m).comp
        ((jetMap (anLin (colPr n g i)) (anLin_mem _) :
          Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin 1 × Fin (n * g)) m) :
          Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin 1 × Fin (n * g)) m) :=
    RingHom.ext fun a => (renN_colPr n g m i a).symm
  rw [hring, anSpMap_comp, Category.assoc]
  congr 1
  have := isLocalHom_jetMap (K := ℂ) (m := m) (anLin (colPr n g i)) (anLin_mem _)
  refine jetPt_precompD _ _ hol _ (by show e (colPr n g i 0) = e 0; rw [map_zero]) m _ fun U hU f => ?_
  exact (jetOf_comp_anLin m (contDiffAt_val _ hol hU f) (colPr n g i)).symm

section General

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)

theorem AnFr.e_zero : Φ.e 0 = 1 := (Φ.e_ker 0).mpr Φ.lat.zero_mem

theorem AnFr.jetMap_copy (n m : ℕ) (i : Fin n) :
    Φ.JetMap m (homAt x0 (jetCopy (S := ℂ) g m i) ≫ anJX x0 Φ.e Φ.hol m).left (LinearMap.proj i) :=
  ⟨isHolFam_precomp_clm _ Φ.hol (colPr n g i), spMap_jetCopy_jetPt _ Φ.hol n m i⟩

theorem AnFr.jetMap_self (m : ℕ) :
    Φ.JetMap (n := 1) m (anJX x0 Φ.e Φ.hol m).left (LinearMap.proj 0) := by
  refine ⟨isHolFam_precomp_clm _ Φ.hol (colPr 1 g 0), ?_⟩
  have h := spMap_jetCopy_jetPt _ Φ.hol 1 m 0
  have hid : (jetCopy (S := ℂ) g m (0 : Fin 1) : Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin 1 × Fin g) m) =
      RingHom.id _ := RingHom.ext (jetCopy_one_zero g m)
  rw [hid, spMap, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp] at h
  exact h

theorem AnFr.jetMap_one (n m : ℕ) :
    Φ.JetMap m (1 : overAt x0 (Jet ℂ (Fin n × Fin g) m) ⟶ A).left 0 := by
  have hc : ∀ v : Fin (n * g) → ℂ, (Φ.e ((0 : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (colsOf n g v))).left =
      (1 : Over.mk x0 ⟶ A).left := fun v => by rw [LinearMap.zero_apply, Φ.e_zero]
  have hf := funext hc
  have hol : IsHolFam (fun v : Fin (n * g) → ℂ =>
      (Φ.e ((0 : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (colsOf n g v))).left) := by
    rw [hf]; exact isHolFam_const _
  refine ⟨hol, ?_⟩
  have h1 := jetPt_comp _ (isHolFam_const (g := n * g) (1 : Over.mk x0 ⟶ A).left) (𝟙 _) _ hol
    (fun v => (Category.comp_id _).trans (hc v).symm) m
  rw [← h1, Category.comp_id, ← jetPt_const, ← Category.assoc, spMap_comp_alg]
  let k : overAt x0 (Jet ℂ (Fin n × Fin g) m) ⟶ Over.mk x0 :=
    Over.homMk (spMap (algebraMap ℂ (Jet ℂ (Fin n × Fin g) m))) rfl
  have hk : (1 : overAt x0 (Jet ℂ (Fin n × Fin g) m) ⟶ A) = k ≫ (1 : Over.mk x0 ⟶ A) := (MonObj.comp_one k).symm
  rw [hk]
  rfl

theorem AnFr.jetMap_comp {n m : ℕ} (a : overAt x0 (Jet ℂ (Fin n × Fin g) m) ⟶ A)
    (Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (φ : A ⟶ A) (T : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hT : ∀ z, Φ.e (T z) = Φ.e z ≫ φ) (ha : Φ.JetMap m a.left Λ) : Φ.JetMap m (a ≫ φ).left (T ∘ₗ Λ) := by
  obtain ⟨hol, ha⟩ := ha
  have hc : ∀ v : Fin (n * g) → ℂ, (Φ.e (Λ (colsOf n g v))).left ≫ φ.left =
      (Φ.e ((T ∘ₗ Λ) (colsOf n g v))).left := fun v => by
    rw [LinearMap.comp_apply, hT, Over.comp_left]
  have hol' : IsHolFam (fun v : Fin (n * g) → ℂ => (Φ.e ((T ∘ₗ Λ) (colsOf n g v))).left) := by
    rw [← funext hc]; exact isHolFam_comp _ hol _
  refine ⟨hol', ?_⟩
  rw [Over.comp_left, ha, Category.assoc, jetPt_comp _ hol _ _ hol' hc]

theorem AnFr.jetMap_pair {n m : ℕ} (a b : overAt x0 (Jet ℂ (Fin n × Fin g) m) ⟶ A)
    (Λ Λ' : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (ha : Φ.JetMap m a.left Λ) (hb : Φ.JetMap m b.left Λ') :
    ∃ hq : IsHolFam (fun v : Fin (n * g) → ℂ => (lift (Φ.e (Λ (colsOf n g v))) (Φ.e (Λ' (colsOf n g v)))).left),
      (lift a b).left = spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) ≫
        jetPt _ hq m := by
  obtain ⟨hola, ha⟩ := ha
  obtain ⟨holb, hb⟩ := hb
  have hq : IsHolFam (fun v : Fin (n * g) → ℂ =>
      (lift (Φ.e (Λ (colsOf n g v))) (Φ.e (Λ' (colsOf n g v)))).left) :=
    GlobalTheory.AnVal.isHolFam_pullback_lift S A.left A.left A.hom A.hom (n * g) _ _ x0 (fun v => Over.w (Φ.e (Λ (colsOf n g v))))
      (fun v => Over.w (Φ.e (Λ' (colsOf n g v)))) hola holb
  refine ⟨hq, ?_⟩
  have hf : ∀ v : Fin (n * g) → ℂ, (lift (Φ.e (Λ (colsOf n g v))) (Φ.e (Λ' (colsOf n g v)))).left ≫
      (fst A A).left = (Φ.e (Λ (colsOf n g v))).left := fun v => by rw [← Over.comp_left, lift_fst]
  have hs : ∀ v : Fin (n * g) → ℂ, (lift (Φ.e (Λ (colsOf n g v))) (Φ.e (Λ' (colsOf n g v)))).left ≫
      (snd A A).left = (Φ.e (Λ' (colsOf n g v))).left := fun v => by rw [← Over.comp_left, lift_snd]
  apply pullback.hom_ext
  · show (lift a b).left ≫ (fst A A).left = (_ ≫ jetPt _ hq m) ≫ (fst A A).left
    rw [← Over.comp_left, lift_fst, Category.assoc, jetPt_comp _ hq _ _ hola hf, ha]
  · show (lift a b).left ≫ (snd A A).left = (_ ≫ jetPt _ hq m) ≫ (snd A A).left
    rw [← Over.comp_left, lift_snd, Category.assoc, jetPt_comp _ hq _ _ holb hs, hb]

theorem AnFr.jetMap_mul {n m : ℕ} (a b : overAt x0 (Jet ℂ (Fin n × Fin g) m) ⟶ A)
    (Λ Λ' : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (ha : Φ.JetMap m a.left Λ) (hb : Φ.JetMap m b.left Λ') :
    Φ.JetMap m (a * b).left (Λ + Λ') := by
  obtain ⟨hq, hab⟩ := Φ.jetMap_pair a b Λ Λ' ha hb
  have hc : ∀ v : Fin (n * g) → ℂ, (lift (Φ.e (Λ (colsOf n g v))) (Φ.e (Λ' (colsOf n g v)))).left ≫
      (MonObj.mul : A ⊗ A ⟶ A).left = (Φ.e ((Λ + Λ') (colsOf n g v))).left := fun v => by
    rw [LinearMap.add_apply, Φ.e_add, CategoryTheory.Hom.mul_def, Over.comp_left]
  have hol' : IsHolFam (fun v : Fin (n * g) → ℂ => (Φ.e ((Λ + Λ') (colsOf n g v))).left) := by
    rw [← funext hc]; exact isHolFam_comp _ hq _
  refine ⟨hol', ?_⟩
  rw [CategoryTheory.Hom.mul_def, Over.comp_left, hab, Category.assoc, jetPt_comp _ hq _ _ hol' hc]

end General

theorem jetPts_jetMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), ∀ (n m : ℕ), (∀ i : Fin n, Φ.toAnFr.JetMap m (jpt y g Φ.jx m i).left (LinearMap.proj i)) ∧ Φ.toAnFr.JetMap m (1 : jO y g m n ⟶ Xo.univ.t.G).left 0 ∧ (∀ (a b : jO y g m n ⟶ Xo.univ.t.G) (Λ Λ' : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), Φ.toAnFr.JetMap m a.left Λ → Φ.toAnFr.JetMap m b.left Λ' → Φ.toAnFr.JetMap m (a * b).left (Λ + Λ') ∧ ∃ hq : IsHolFam (fun v : Fin (n * g) → ℂ => (lift (Φ.e (Λ (colsOf n g v))) (Φ.e (Λ' (colsOf n g v)))).left), (lift a b).left = spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) ≫ jetPt _ hq m) ∧ (∀ (a : jO y g m n ⟶ Xo.univ.t.G) (Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (α : 𝓞 E), Φ.toAnFr.JetMap m a.left Λ → Φ.toAnFr.JetMap m (a ≫ Xo.univ.t.act.act α).left (tyAct ty α ∘ₗ Λ)) ∧ Φ.toAnFr.JetMap (n := 1) m (Φ.jx m).left (LinearMap.proj 0) := by
  intro E _ _ _ H Dw l Xo c _ y g ty el Φ n m
  exact ⟨fun i => Φ.toAnFr.jetMap_copy n m i, Φ.toAnFr.jetMap_one n m,
    fun a b Λ Λ' ha hb => ⟨Φ.toAnFr.jetMap_mul a b Λ Λ' ha hb, Φ.toAnFr.jetMap_pair a b Λ Λ' ha hb⟩,
    fun a Λ α ha => Φ.toAnFr.jetMap_comp a Λ _ _ (Φ.lin α) ha, Φ.toAnFr.jetMap_self m⟩

end GlobalTheory.AnVal
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnValThPow

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem telescope (c h : ℂ) (k : ℤ) (f : ℕ → ℂ) (hf : ∀ i, f i ≠ 0) (n : ℕ) :
    ∏ i ∈ Finset.range n, (c * Complex.exp (-((k : ℂ) * Real.pi * (i * h)) - (k : ℂ) * Real.pi * h / 2) *
      (f i ^ k * f (i + 1) ^ (-k))) =
      c ^ n * Complex.exp (-((k : ℂ) * (Real.pi / 2 * (n * n * h)))) * (f 0 ^ k * f n ^ (-k)) := by
  induction n with
  | zero => simp [zpow_neg, mul_inv_cancel₀ (zpow_ne_zero k (hf 0))]
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, pow_succ]
    have h1 : f n ^ (-k) * f n ^ k = 1 := by rw [zpow_neg, inv_mul_cancel₀ (zpow_ne_zero k (hf n))]
    have h2 : Complex.exp (-((k : ℂ) * (Real.pi / 2 * (n * n * h)))) *
        Complex.exp (-((k : ℂ) * Real.pi * (n * h)) - (k : ℂ) * Real.pi * h / 2) =
        Complex.exp (-((k : ℂ) * (Real.pi / 2 * (((n + 1 : ℕ) : ℂ) * ((n + 1 : ℕ) : ℂ) * h)))) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [← h2]
    linear_combination (c ^ n * c * Complex.exp (-((k : ℂ) * (Real.pi / 2 * (n * n * h)))) *
        Complex.exp (-((k : ℂ) * Real.pi * (n * h)) - (k : ℂ) * Real.pi * h / 2) *
        (f 0 ^ k * f (n + 1) ^ (-k))) * h1

theorem herm_smul_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (a : ℂ) (z w : Fin g → ℂ) :
    hermForm Hm (a • z) w = a * hermForm Hm z w := by unfold hermForm; rw [smul_dotProduct, smul_eq_mul]

theorem herm_nat_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (a : ℕ) (z w : Fin g → ℂ) :
    hermForm Hm z ((a : ℂ) • w) = a * hermForm Hm z w := by unfold hermForm; rw [star_smul, star_natCast, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

section

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] {T : Over S}

theorem translPt_mul (x : T ⟶ A) : translPt A x = (fst T A ≫ x) * snd T A := rfl

theorem translT_snd (y : T ⟶ A) : translT A y ≫ snd T A = translPt A y := by unfold translT; exact lift_snd _ _

theorem translT_translPt [IsCommMonObj A] (x y : T ⟶ A) :
    translT A y ≫ translPt A x = translPt A (x * y) := by
  have hf : translT A y ≫ fst T A = fst T A := by unfold translT; exact lift_fst _ _
  rw [translPt_mul, translPt_mul, comp_mul, ← Category.assoc, hf, translT_snd, translPt_mul, comp_mul, _root_.mul_assoc]

theorem pt_translPt (x z : T ⟶ A) : ptSecT A z ≫ translPt A x = x * z := by
  unfold ptSecT translPt
  rw [comp_lift_assoc, lift_fst_assoc, Category.id_comp, lift_snd]
  rfl

theorem pt_translT (x z : T ⟶ A) : ptSecT A z ≫ translT A x = ptSecT A (x * z) := by
  have h := pt_translPt A x z
  unfold ptSecT at h ⊢
  unfold translT
  rw [comp_lift, lift_fst, h]

theorem powφ_zero (x : T ⟶ A) (n : ℕ) (i : Fin n) : powφ A x n (i, 0) = (translPt A (x ^ (i : ℕ))).left := by
  unfold powφ
  dsimp only
  rw [Matrix.cons_val_zero, ← Over.comp_left, translT_snd]

theorem powφ_one [IsCommMonObj A] (x : T ⟶ A) (n : ℕ) (i : Fin n) :
    powφ A x n (i, 1) = (translPt A (x ^ ((i : ℕ) + 1))).left := by
  unfold powφ
  dsimp only
  rw [Matrix.cons_val_one, Matrix.cons_val_fin_one, ← Over.comp_left, translT_translPt, ← pow_succ']

private theorem isChart_choose_and_symm_apply (L : LB A.left) (k : ℤ) (θ : ThetaGrp A L k T) (n : ℕ) (q : Sp ℂ ⟶ (T ⊗ A).left)
    (j : Fin n × Fin 2 → L.ι) (hj : ⊤ ≤ q ⁻¹ᵁ LB.wchart L (powφ A θ.pt n) j) (i : Fin n) :
    ⊤ ≤ (q ≫ (translT A (θ.pt ^ (i : ℕ))).left) ⁻¹ᵁ
      LB.wchart L ![(snd T A).left, (translPt A θ.pt).left] (fun b => j (i, b)) := by
  intro p _
  have hp := hj (show p ∈ (⊤ : (Sp ℂ).Opens) from trivial)
  unfold LB.wchart at hp ⊢
  unfold powφ at hp
  simp at hp ⊢
  exact hp i

private theorem exists_unit_mul_eq_mul_uniformizer_pow {Z Y : Scheme.{0}} (q : Sp ℂ ⟶ Z) (ψ : Z ⟶ Y) (V : Y.Opens) {W W' : Z.Opens}
    (e1 : W ≤ W') (e2 : W' ≤ ψ ⁻¹ᵁ V) (h : ⊤ ≤ q ⁻¹ᵁ W) (h' : ⊤ ≤ (q ≫ ψ) ⁻¹ᵁ V) (u : Γ(Y, V)) :
    (q.appLE W ⊤ h).hom ((Z.presheaf.map (homOfLE e1).op).hom ((Z.presheaf.map (homOfLE e2).op).hom
      ((ψ.app V).hom u))) = ((q ≫ ψ).appLE V ⊤ h').hom u := by
  have key : Z.presheaf.map (homOfLE e2).op ≫ Z.presheaf.map (homOfLE e1).op ≫ q.appLE W ⊤ h =
      q.appLE (ψ ⁻¹ᵁ V) ⊤ h' := by
    simp only [Scheme.Hom.map_appLE]
  rw [Scheme.Hom.comp_appLE, CommRingCat.comp_apply, ← key]
  rfl

private theorem valAt'_prod_res_pullU_eq_prod {Z Y : Scheme.{0}} {n : ℕ} (q : Sp ℂ ⟶ Z) (W : Z.Opens) (h : ⊤ ≤ q ⁻¹ᵁ W)
    (ψ : Fin n → (Z ⟶ Y)) (V : Fin n → Y.Opens) (W' : Fin n → Z.Opens) (e1 : ∀ i, W ≤ W' i)
    (e2 : ∀ i, W' i ≤ ψ i ⁻¹ᵁ V i) (u : ∀ i, Γ(Y, V i)ˣ) (h' : ∀ i, ⊤ ≤ (q ≫ ψ i) ⁻¹ᵁ V i) :
    valAt' q W (∏ i, res (e1 i) (res (e2 i) (pullU (ψ i) (V i) (u i)))).val =
      ∏ i, valAt' (q ≫ ψ i) (V i) (u i).val := by
  unfold valAt'
  rw [dif_pos h]
  simp only [dif_pos (h' _)]
  unfold valAt res pullU
  simp only [Units.coe_prod, map_prod, Units.coe_map, MonoidHom.coe_coe]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [exists_unit_mul_eq_mul_uniformizer_pow q (ψ i) (V i) (e1 i) (e2 i) h (h' i)]

theorem val_powGen (L : LB A.left) (k : ℤ) (θ : ThetaGrp A L k T) (n : ℕ) (q : Sp ℂ ⟶ (T ⊗ A).left)
    (j : Fin n × Fin 2 → L.ι) (hj : ⊤ ≤ q ⁻¹ᵁ LB.wchart L (powφ A θ.pt n) j) :
    valAt' q (LB.wchart L (powφ A θ.pt n) j) ((powGen A L k θ n).s j).val =
      ∏ i : Fin n, valAt' (q ≫ (translT A (θ.pt ^ (i : ℕ))).left)
        (LB.wchart L ![(snd T A).left, (translPt A θ.pt).left] (fun b => j (i, b)))
        (θ.φ.s (fun b => j (i, b))).val := by
  unfold powGen LB.pullGen
  exact valAt'_prod_res_pullU_eq_prod q _ hj _ _ _ _ _ _ (fun i => isChart_choose_and_symm_apply A L k θ n q j hj i)

end

theorem e_nat {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)
    (x : Fin g → ℂ) (i : ℕ) : Φ.e ((i : ℂ) • x) = Φ.e x ^ i := by
  induction i with
  | zero => simpa using (Φ.e_ker 0).mpr Φ.lat.zero_mem
  | succ i ih => rw [Nat.cast_succ, add_smul, one_smul, Φ.e_add, ih, pow_succ]

theorem thConst_pow : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (k : ℤ) (n : ℕ) (U : ThetaGrp A L.L k (Over.mk x0)) (x : Fin g → ℂ) (c : ℂ), Φ.ThConst k U x c → (n : ℂ) • x ∈ Φ.lat → LB.Gen.Corr L.L _ _ _ _ (powGen A L.L k U n) (LB.oneGen L.L) → c ^ n * Φ.χ ((n : ℂ) • x) ^ k = 1 := by
  intro S A _ _ L x0 g Φ k n U x c hT hx hC
  obtain ⟨hpt, hrd⟩ := hT
  have he0 : Φ.e 0 = 1 := (Φ.e_ker 0).mpr Φ.lat.zero_mem
  have hpts : ∀ m : ℕ, (ptSecT A (Φ.e 0)).left ≫ (translPt A (U.pt ^ m)).left = (Φ.e ((m : ℂ) • x)).left := by
    intro m
    rw [← Over.comp_left, pt_translPt, he0, _root_.mul_one, hpt, ← e_nat]
  have hptT : ∀ m : ℕ, (ptSecT A (Φ.e 0)).left ≫ (translT A (U.pt ^ m)).left =
      (ptSecT A (Φ.e ((m : ℂ) • x))).left := by
    intro m
    rw [← Over.comp_left, pt_translT, he0, _root_.mul_one, hpt, ← e_nat]
  have hs : ∀ m : ℕ, (((m + 1 : ℕ)) : ℂ) • x = x + (m : ℂ) • x := by
    intro m; push_cast; rw [add_smul, one_smul, add_comm]
  have hG : Φ.GenRd (powφ A U.pt n) _ (powGen A L.L k U n) (ptSecT A (Φ.e 0)).left
      (fun p => ![((p.1 : ℕ) : ℂ) • x, x + ((p.1 : ℕ) : ℂ) • x] p.2)
      (∏ i : Fin n, c * fock Φ.Hm k x (fun _ => 1) (((i : ℕ) : ℂ) • x)) := by
    refine ⟨?_, ?_⟩
    · rintro ⟨i, b⟩
      rcases (show b = 0 ∨ b = 1 by fin_cases b <;> simp) with rfl | rfl
      · rw [powφ_zero, hpts]; rfl
      · rw [powφ_one, hpts, hs]; rfl
    · intro j hj
      rw [val_powGen A L.L k U n _ j hj, Fintype.prod_prod_type, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      have hc := isChart_choose_and_symm_apply A L.L k U n _ j hj i
      rw [hptT] at hc ⊢
      exact (hrd (((i : ℕ) : ℂ) • x)).2 _ hc
  have h1 : Φ.GenRd _ _ (LB.oneGen L.L) (ptSecT A (Φ.e 0)).left (fun e => e.elim) 1 := by
    refine ⟨fun kk => kk.elim, fun j' hj' => ?_⟩
    unfold valAt'
    rw [dif_pos hj']
    unfold valAt LB.oneGen
    simp only [Units.val_one, Fintype.prod_empty, _root_.mul_one]
    exact (congrArg (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (map_one _)).trans (map_one _)
  obtain ⟨J, hJ, heq⟩ := (GlobalTheory.AnValGenCorr.genRd_corr_mul_inv S A L x0 g Φ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hG h1).1 hC
  simp only [Fintype.prod_empty, _root_.one_mul] at heq
  obtain ⟨f, hfdef⟩ : ∃ f : ℕ → ℂ, f = fun m : ℕ => Φ.fr (J (translPt A (U.pt ^ m)).left) ((m : ℂ) • x) := ⟨_, rfl⟩
  have hf : ∀ m, f m ≠ 0 := by
    intro m
    rw [hfdef]
    have hc := hJ (translPt A (U.pt ^ m)).left
    rw [hpts m] at hc
    exact Φ.fr_ne _ _ hc
  have key : ∏ i ∈ Finset.range n, (c * Complex.exp (-((k : ℂ) * Real.pi * (i * hermForm Φ.Hm x x)) -
      (k : ℂ) * Real.pi * hermForm Φ.Hm x x / 2) * (f i ^ k * f (i + 1) ^ (-k))) = 1 := by
    refine Eq.trans ?_ heq
    rw [Finset.prod_range, Fintype.prod_prod_type, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [Fin.prod_univ_two, powφ_zero, powφ_one, hfdef]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, fock, herm_smul_left, hs,
      _root_.mul_one, powε]
  rw [telescope c (hermForm Φ.Hm x x) k f hf n] at key
  have hpn : U.pt ^ n = U.pt ^ 0 := by rw [pow_zero, hpt, ← e_nat, (Φ.e_ker _).mpr hx]
  have hc0 := hJ (translPt A (U.pt ^ 0)).left
  rw [hpts 0] at hc0
  simp only [Nat.cast_zero, zero_smul] at hc0
  have hper := Φ.fr_per _ hx _ 0 hc0
  have h0 : hermForm Φ.Hm 0 ((n : ℂ) • x) = 0 := by simp [hermForm]
  simp only [h0, mul_zero, zero_add] at hper
  have hfn := hf n
  rw [hfdef] at key hfn
  simp only [hpn, Nat.cast_zero, zero_smul] at key hfn
  rw [hper, mul_zpow, mul_zpow] at key
  have hB : Complex.exp (-((k : ℂ) * (Real.pi / 2 * ((n : ℂ) * (n : ℂ) * hermForm Φ.Hm x x)))) *
      Complex.exp (Real.pi / 2 * hermForm Φ.Hm ((n : ℂ) • x) ((n : ℂ) • x)) ^ k = 1 := by
    rw [← Complex.exp_int_mul, ← Complex.exp_add, herm_smul_left, herm_nat_right, ← Complex.exp_zero]
    congr 1
    ring
  have hnk : Φ.fr (J (translPt A (U.pt ^ 0)).left) ((n : ℂ) • x) ^ k *
      Φ.fr (J (translPt A (U.pt ^ 0)).left) ((n : ℂ) • x) ^ (-k) = 1 := by
    rw [zpow_neg, mul_inv_cancel₀ (zpow_ne_zero _ hfn)]
  linear_combination key - c ^ n * Φ.χ ((n : ℂ) • x) ^ k *
    Complex.exp (-((k : ℂ) * (Real.pi / 2 * ((n : ℂ) * (n : ℂ) * hermForm Φ.Hm x x)))) *
    Complex.exp (Real.pi / 2 * hermForm Φ.Hm ((n : ℂ) • x) ((n : ℂ) • x)) ^ k * hnk -
    c ^ n * Φ.χ ((n : ℂ) • x) ^ k * hB

end GlobalTheory.AnValThPow
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.appellHumbert_frame_semicharacter : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), (∀ a ∈ Φ.lat, ∀ b ∈ Φ.lat, (∃ k : ℤ, (hermForm Φ.Hm a b).im = k) ∧ Φ.χ (a + b) = Φ.χ a * Φ.χ b * Complex.exp (Real.pi * Complex.I * ((hermForm Φ.Hm a b).im : ℂ))) ∧ Φ.χ 0 = 1 ∧ ((∀ a ∈ Φ.lat, Φ.χ a ^ 2 = 1) → ∀ a ∈ Φ.lat, Φ.χ ((2 : ℂ) • a) = 1) := by
  first | exact @GlobalTheory.AnVal.anFr_semichar | exact GlobalTheory.AnVal.anFr_semichar | (intros; apply GlobalTheory.AnVal.anFr_semichar <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.generatorReading_corr_mul_inv : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (Z : Scheme.{0}) (K K' : Type) [Fintype K] [Fintype K'] (φ : K → (Z ⟶ A.left)) (ε : K → ℤ) (φ' : K' → (Z ⟶ A.left)) (ε' : K' → ℤ) (t : LB.Gen (LB.LinComb L.L φ ε)) (t' : LB.Gen (LB.LinComb L.L φ' ε')) (q : Sp ℂ ⟶ Z) (p : K → Fin g → ℂ) (p' : K' → Fin g → ℂ) (v v' : ℂ), Φ.GenRd φ ε t q p v → Φ.GenRd φ' ε' t' q p' v' → (LB.Gen.Corr L.L φ ε φ' ε' t t' → ∃ J : (Z ⟶ A.left) → L.L.ι, (∀ ψ, ⊤ ≤ (q ≫ ψ) ⁻¹ᵁ L.L.U (J ψ)) ∧ v * ∏ k, Φ.fr (J (φ k)) (p k) ^ ε k = v' * ∏ k, Φ.fr (J (φ' k)) (p' k) ^ ε' k) ∧ (LB.Gen.Corr L.L φ ε φ' ε' t t' → LB.SameSum φ ε φ' ε' → (∃ π : (Z ⟶ A.left) → Fin g → ℂ, (∀ k, p k = π (φ k)) ∧ ∀ k, p' k = π (φ' k)) → v = v') ∧ Φ.GenRd (Sum.elim φ φ') (Sum.elim ε ε') (LB.mulGen L.L φ ε φ' ε' t t') q (Sum.elim p p') (v * v') ∧ Φ.GenRd φ (fun k => -ε k) (LB.invGen L.L φ ε t) q p v⁻¹ := by
  first | exact @GlobalTheory.AnValGenCorr.genRd_corr_mul_inv | exact GlobalTheory.AnValGenCorr.genRd_corr_mul_inv | (intros; apply GlobalTheory.AnValGenCorr.genRd_corr_mul_inv <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.analyticFrame_exponential_immersion_at_origin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), Φ.toAnFr.Imm := by
  first | exact @GlobalTheory.FrameImm.anPt_imm | exact GlobalTheory.FrameImm.anPt_imm | (intros; apply GlobalTheory.FrameImm.anPt_imm <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.generatorReading_pullback_period_rigid : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (Z : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Z ⟶ A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L.L φ ε)), (∀ (Z' : Scheme.{0}) (h : Z' ⟶ Z) (q : Sp ℂ ⟶ Z') (p : K → Fin g → ℂ) (v : ℂ), Φ.GenRd (fun k => h ≫ φ k) ε (LB.pullGen L.L φ ε t h) q p v ↔ Φ.GenRd φ ε t (q ≫ h) p v) ∧ (∀ (q : Sp ℂ ⟶ Z) (p a : K → Fin g → ℂ) (v : ℂ), (∀ k, a k ∈ Φ.lat) → Φ.GenRd φ ε t q p v → Φ.GenRd φ ε t q (fun k => p k + a k) (v * ∏ k, Φ.fac (a k) (p k) ^ ε k)) ∧ ∀ k : ℤ, Φ.GenRd (K := PUnit) (fun _ => eSec A) (fun _ => k) (rigPow A L.L L.rig k) x0 (fun _ => 0) 1 := by
  first | exact @GlobalTheory.AnVal.genRd_pull_period_rig | exact GlobalTheory.AnVal.genRd_pull_period_rig | (intros; apply GlobalTheory.AnVal.genRd_pull_period_rig <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.reading_twisted_pullback : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (ψ : Over.mk x0 ⊗ A ⟶ Over.mk x0 ⊗ A) (m : Over.mk x0 ⊗ A ⟶ A) (hm : ψ ≫ snd (Over.mk x0) A = m) (a b : ℤ) (α : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(snd (Over.mk x0) A).left, m.left] ![a, -b])) (s : LB.Sec (LPow A L.L b (Over.mk x0))) (s' : LB.Sec (LPow A L.L a (Over.mk x0))) (θ : (Fin g → ℂ) → ℂ) (p : (Fin g → ℂ) → Fin g → ℂ) (v : (Fin g → ℂ) → ℂ), ψ ≫ fst (Over.mk x0) A = fst (Over.mk x0) A → IsTwistPull A L.L ψ m hm a b α s s' → Φ.Rd b s θ → (∀ z, (ptSecT A (Φ.e z)).left ≫ m.left = (Φ.e (p z)).left ∧ ∃ j : Fin 2 → L.L.ι, ⊤ ≤ (ptSecT A (Φ.e z)).left ⁻¹ᵁ LB.wchart L.L ![(snd (Over.mk x0) A).left, m.left] j ∧ valAt' (ptSecT A (Φ.e z)).left (LB.wchart L.L ![(snd (Over.mk x0) A).left, m.left] j) (α.s j).val = v z * (Φ.fr (j 0) z ^ a * Φ.fr (j 1) (p z) ^ (-b))) → Φ.Rd a s' (fun z => v z * θ (p z)) := by
  first | exact @GlobalTheory.AnVal.AnFr.rd_twistPull | exact GlobalTheory.AnVal.AnFr.rd_twistPull | (intros; apply GlobalTheory.AnVal.AnFr.rd_twistPull <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.section_reading_existsUnique_isTheta : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (k : ℤ) (F : LB.Sec (LPow A L.L k (Over.mk x0))), (∃! θ, Φ.Rd k F θ) ∧ (∀ θ, Φ.Rd k F θ → Φ.IsTh k θ) ∧ ∀ θ, Φ.Rd k F θ ↔ ∀ z, ∃ j, ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U j ∧ valAt' (ptSecT A (Φ.e z)).left ((LPow A L.L k (Over.mk x0)).U (fun _ => j)) (F.f (fun _ => j)) = θ z * Φ.fr j z ^ k := by
  first | exact @GlobalTheory.AnVal.reading_existsUnique_isTh | exact GlobalTheory.AnVal.reading_existsUnique_isTh | (intros; apply GlobalTheory.AnVal.reading_existsUnique_isTh <;> assumption)
end

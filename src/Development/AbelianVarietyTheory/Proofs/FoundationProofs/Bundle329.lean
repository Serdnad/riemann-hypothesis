module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle011
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
public import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EOpEqAsAlgebraHom
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle251
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle325
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle020
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLaw
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle964
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle323
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle012
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.FlatRow

namespace GlobalTheory.EigBasisPrime

theorem eig_localization {R R' O L L' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (S : Submonoid R)
    [IsLocalization S R'] [CommRing O] [Module.Finite ℤ O] [AddCommGroup L] [Module R L] [Module O L]
    [SMulCommClass O R L] [AddCommGroup L'] [Module R' L'] [Module O L'] [SMulCommClass O R' L'] (f : L →+ L')
    (hs : ∀ (r : R) x, f (r • x) = algebraMap R R' r • f x) (ha : ∀ (a : O) x, f (a • x) = a • f x)
    (lift : ∀ y, ∃ q ∈ S, ∃ x, f x = algebraMap R R' q • y) (uniq : ∀ x, f x = 0 → ∃ q ∈ S, q • x = 0)
    (χ : O →+* R) {m : ℕ} (v : Fin m → L)
    (hv : ∀ w : L, (∀ a, a • w = χ a • w) → ∃! c : Fin m → R, w = ∑ i, c i • v i)
    (w : L') (hw : ∀ a, a • w = algebraMap R R' (χ a) • w) : ∃! c : Fin m → R', w = ∑ i, c i • f (v i) := by
  classical
  have unit : ∀ q ∈ S, IsUnit (algebraMap R R' q) := fun q hq => IsLocalization.map_units R' ⟨q, hq⟩
  have inj : ∀ d : Fin m → R', ∑ i, d i • f (v i) = 0 → d = 0 := fun d hd => by
    obtain ⟨⟨q, hq⟩, hqi⟩ := IsLocalization.exist_integer_multiples_of_finite S d
    choose d' hd' using hqi
    have h0 : f (∑ i, d' i • v i) = 0 := by

      simp only [map_sum, hs, hd', Algebra.smul_def, mul_smul]
      rw [← Finset.smul_sum, hd, smul_zero]
    obtain ⟨r, hr, h1⟩ := uniq _ h0
    have h2 : r • d' = 0 := (hv 0 (by simp)).unique
      (by rw [← h1, Finset.smul_sum]; simp [mul_smul]) (by simp)
    funext i
    have h3 := congrArg (algebraMap R R') (congrFun h2 i)
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, hd', Algebra.smul_def, Pi.zero_apply,
      map_zero] at h3
    exact (unit q hq).mul_right_eq_zero.1 ((unit r hr).mul_right_eq_zero.1 h3)
  obtain ⟨q, hq, x, hx⟩ := lift w
  have h1 : ∀ a : O, ∃ r ∈ S, r • (a • x - χ a • x) = 0 := fun a => uniq _ (by
    rw [map_sub, ha, hs, hx, smul_comm a, hw, smul_comm, sub_self])
  choose r hr h1 using h1
  obtain ⟨s, hsp⟩ := Module.Finite.fg_top (R := ℤ) (M := O)
  have hQ : ∏ a ∈ s, r a ∈ S := S.prod_mem fun a _ => hr a
  obtain ⟨c, hc, -⟩ := hv ((∏ a ∈ s, r a) • x) fun a => by
    have : a ∈ Submodule.span ℤ (s : Set O) := hsp ▸ Submodule.mem_top
    induction this using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem r (Finset.mem_coe.1 hb)
      rw [smul_comm b, smul_comm (χ b), ← sub_eq_zero, ← smul_sub, hk, _root_.mul_comm, mul_smul, h1, smul_zero]
    | zero => simp
    | add b b' _ _ e e' => rw [add_smul, e, e', map_add (f := _), add_smul]
    | smul k b _ e => rw [smul_assoc, e, map_zsmul, smul_assoc]
  have h2 := congrArg f hc

  simp only [map_sum, hs, hx, smul_smul] at h2
  obtain ⟨u, hu⟩ := ((unit _ hQ).mul (unit q hq)).exists_left_inv
  have h3 : w = ∑ i, (u * algebraMap R R' (c i)) • f (v i) := by
    simp only [mul_smul u]
    rw [← Finset.smul_sum, ← h2, smul_smul, hu, one_smul]
  refine ⟨_, h3, fun c' hc' => sub_eq_zero.1 (inj _ ?_)⟩
  simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
  rw [← hc', ← h3, sub_self]

theorem isEigBasis_atPrime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (R : Type) [CommRing R] (p : Ideal R) [p.IsPrime] (t : SAB H (Sp R)) (t' : SAB H (Sp (Localization.AtPrime p))) (n : SABMap t' t (spMap (algebraMap R (Localization.AtPrime p)))) (χ : 𝓞 E →+* R) (m : ℕ) (v : Fin m → (epsR R ⟶ t.G)) (v' : Fin m → (epsR (Localization.AtPrime p) ⟶ t'.G)), EigenvectorLieDegree.IsEigBasis t.act χ v → (∀ i, IsVecOver (algebraMap R (Localization.AtPrime p)) n.φ (v i) (v' i)) → EigenvectorLieDegree.IsEigBasis t'.act ((algebraMap R (Localization.AtPrime p)).comp χ) v' := by
  intro E _ _ _ H R _ p _ t t' n χ m v v' hv hv'
  have := t.semi.smooth
  have : ∀ s : R, Smooth (Chart.Gs t.G s).hom := fun s => show Smooth (pullback.snd t.G.hom _) from inferInstance
  let j := algebraMap R (Localization.AtPrime p)
  choose g hg hgu using fun x : epsR R ⟶ t.G => existsUnique_isVecOver (f := j) n.cart.1 x
  let f₀ : Serre.Lie t.act → Serre.Lie t'.act := fun x =>
    Serre.Lie.mk _ (g x.hom) ((hg _).isTangent n.cart x.isTangent)
  have hf : ∀ x y, f₀ x = y ↔ IsVecOver j n.φ x.hom y.hom := fun x y =>
    ⟨fun e => e ▸ hg _, fun e => Serre.Lie.ext (hgu _ _ e).symm⟩
  have comb : ∀ (k : ℕ) (c : Fin k → R) (x : Fin k → Serre.Lie t.act),
      f₀ (∑ i, c i • x i) = ∑ i, j (c i) • f₀ (x i) := fun k c x =>
    (hf _ _).2 ((lieComb_baseChange _ _ j t.G t'.G n.φ n.cart k (fun i => (x i).hom) _ c (fun i => (f₀ (x i)).hom) _
      (fun i => hg _) ((Serre.Lie.isLieComb_iff c x _).2 rfl)).2 ((Serre.Lie.isLieComb_iff _ _ _).2 rfl))
  let f : Serre.Lie t.act →+ Serre.Lie t'.act := AddMonoidHom.mk' f₀ fun x y => by
    simpa using comb 2 1 ![x, y]
  have hs : ∀ (r : R) x, f (r • x) = j r • f x := fun r x => by
    change f₀ _ = _ • f₀ _
    simpa using comb 1 ![r] ![x]
  have ha : ∀ (a : 𝓞 E) x, f (a • x) = a • f x := fun a x => (hf _ _).2 (by
    have := hg x.hom
    simp only [IsVecOver] at this ⊢
    change (g x.hom ≫ t'.act.act a).left ≫ _ = _ ≫ (x.hom ≫ t.act.act a).left
    rw [Over.comp_left, Category.assoc, n.act a, ← Category.assoc, this, Category.assoc, Over.comp_left])
  obtain ⟨e, he⟩ := LiePull.exists_pushEquiv n.cart (epsR (Localization.AtPrime p))
    (spMap (algebraMap R (DualNumber (Localization.AtPrime p)))) (spMap_comp_spMap _ _).symm
  obtain ⟨e₀, he₀⟩ := LiePull.exists_pushEquiv n.cart (𝟙_ (Over (Sp (Localization.AtPrime p)))) (spMap j)
    (Category.id_comp _).symm
  have one : (1 : Over.mk (spMap j) ⟶ t.G).left = η[t'.G].left ≫ n.φ := by
    rw [← map_one e₀, he₀, Hom.one_def, toUnit_unit, Category.id_comp]
  have lift : ∀ y, ∃ q ∈ p.primeCompl, ∃ x, f x = j q • y := fun y => by
    obtain ⟨q, hq, w, hw, hwy⟩ := Chart.tan_prime_lift p (y' := e y.hom) (Over.OverMorphism.ext (by
      refine Eq.trans ?_ one.symm
      rw [Over.comp_left, he, ← y.isTangent]
      exact (Category.assoc _ _ _).symm))
    refine ⟨q, hq, Serre.Lie.mk _ w ((Chart.isTan_iff _).1 hw), (hf _ _).2 ?_⟩
    have := congrArg (fun z => z.left) hwy
    simp only [Over.comp_left, he] at this
    exact (Category.assoc _ _ _).trans this.symm
  have uniq : ∀ x, f x = 0 → ∃ q ∈ p.primeCompl, q • x = 0 := fun x hx => by
    obtain ⟨q, hq, h⟩ := Chart.tan_prime_uniq p (w := x.hom) ((Chart.isTan_iff _).2 x.isTangent)
      (Over.OverMorphism.ext (by
        rw [← map_one e, he]
        exact ((hf _ _).1 hx).symm))
    exact ⟨q, hq, Serre.Lie.ext h⟩
  let y : Fin m → Serre.Lie t.act := fun i => Serre.Lie.mk _ (v i) (hv.1 i).1
  have hy : v' = fun i => (f (y i)).hom := funext fun i => hgu _ _ (hv' i)
  subst hy
  refine ⟨fun i => ⟨Serre.Lie.isTangent _, Serre.Lie.mem_eig_iff_left.1 fun a => ?_⟩, fun w hw => ?_⟩
  · rw [← ha, (Serre.Lie.mem_eig_iff_left (v := y i)).2 (hv.1 i).2 a, hs]
    rfl
  · refine (existsUnique_congr fun c => ?_).1 (eig_localization p.primeCompl f hs ha lift uniq χ y
      (fun z hz => (existsUnique_congr fun c => ?_).1
        (hv.2 z.hom ⟨z.isTangent, (Serre.Lie.mem_eig_iff_left (τ := χ) (v := z)).1 hz⟩))
      (Serre.Lie.mk _ w hw.1) ((Serre.Lie.mem_eig_iff_left (τ := j.comp χ) (v := Serre.Lie.mk _ w hw.1)).2 hw.2))
    · rw [Serre.Lie.isLieComb_iff]
      exact ⟨fun h => congrArg Serre.Lie.hom h, fun h => Serre.Lie.ext h⟩
    · exact (Serre.Lie.isLieComb_iff c y _).trans ⟨fun h => Serre.Lie.ext h, fun h => congrArg Serre.Lie.hom h⟩

end GlobalTheory.EigBasisPrime
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OnTies

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open GlobalTheory.FormTies
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 2000] Submodule.module

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

structure RunData (J : CoreJ D) : Type 1 where

  loc : In66 J.Q

  nab : ∀ j, NabV (J.Q.Xo j) J.Q.c

  dδ : ∀ j n, DeltaDat (J.Q.Xo j) J.Q.c n

  xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ

  half₂ : Ideal (𝓞 D.host.E)

abbrev RunData.full {J : CoreJ D} (r : RunData J) : Full D :=
  ⟨⟨J.toCore, r.loc, r.nab, r.dδ⟩, J.cE, J.chiW, J.x₀, J.iota, r.xi, r.half₂⟩

section Cusp

variable (B : WeightFamilies.Prov D) {j : ℕ} {w : WeightFamilies.Wt D j} {K : Type} [Field K] [NumberField K] [Algebra B.KO K] {n : ℕ}

def supSpan (z : (Fin n → K) ≃ₗ[K] K ⊗[B.KO] B.Cusp j w) : Submodule (𝓞 K) (Fin n → K) := spanK z (B.Mlat j w : Set _)

def shortSpan {P6 : ModuliIntegralCharts.Prov D} (X : WeightAlgebra.PJ D B P6 j) (z : (Fin n → K) ≃ₗ[K] K ⊗[B.KO] B.Cusp j w) :
    Submodule (𝓞 K) (Fin n → K) := spanK z (X.shortTh w : Set _)

def scaledSpan {P6 : ModuliIntegralCharts.Prov D} (X : WeightAlgebra.PJ D B P6 j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ)
    (wL wF : WeightFamilies.Wt D j) (nT : ℕ) (z : (Fin n → K) ≃ₗ[K] K ⊗[B.KO] B.Cusp j w) : Submodule (𝓞 K) (Fin n → K) :=
  spanK z {F | X.inc w F ∈ X.Theta (scalOfP B hinj EX p w wL wF nT) w wL wF nT}




omit [NumberField K] in
theorem exists_cuspRep_of_injective (f : B.Cusp j w →ₗ[B.KO] (Fin n → K)) (hf : Function.Injective f) {P : Type} [Group P]
    (σ : Representation K P (Fin n → K)) (a : P → B.Cusp j w → B.Cusp j w) (ha : ∀ g F, f (a g F) = σ g (f F)) :
    ∃ ρ : Representation B.KO P (B.Cusp j w), ∀ g F, ρ g F = a g F := by
  refine ⟨{ toFun := fun g =>
              { toFun := a g
                map_add' := fun F F' => hf (by rw [map_add (f := _), ha, ha, ha, map_add (f := _), map_add (f := _)])
                map_smul' := fun c F => hf ?_ }
            map_one' := LinearMap.ext fun F => hf ?_
            map_mul' := fun g g' => LinearMap.ext fun F => hf ?_ }, fun _ _ => rfl⟩
  · rw [RingHom.id_apply, map_smul, ha, ha, map_smul, LinearMap.map_smul_of_tower]
  · change f (a 1 F) = f F
    rw [ha, map_one, one_apply_eq_self]
  · change f (a (g * g') F) = f (a g (a g' F))
    rw [ha, ha, ha, map_mul, mul_apply_eq_comp]

end Cusp

variable {T : Full D} [inst : Algebra T.J.Q.c.F D.what₂.LL] {R : RealDat D A T.J.Q.c.F}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

theorem ActionPin.exists_rep {h : LawsP T.toTop} {fw : FWTie T.J R κ v₀} {i : Fin D.R.m}
    {ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)}
    (ha : ActionPin h fw i ℓ) {P : Type} [Group P] (inc : P →* G) :
    ∃ ρ : Representation (recB h.toLawsCore).KO P ((recB h.toLawsCore).Cusp ((i : ℕ) + 1) (κ i)),
      IsLevAct T.toTop h ((i : ℕ) + 1) (κ i) (fun g => ℓ (inc g)) fun g F => ρ g F := by
  obtain ⟨a, h1, h2⟩ := ha
  obtain ⟨ρ, hρ⟩ := exists_cuspRep_of_injective (recB h.toLawsCore) (cuspTo h fw i) (cutTo_spec fw i).1
    ((R.FW i).ρ.comp inc) (fun g => a (inc g)) fun g F => h2 (inc g) F
  exact ⟨ρ, fun g F => (congrArg Subtype.val (hρ g F)).trans (h1 (inc g) F)⟩

section Tied

variable (h : LawsP T.toTop) (fw : FWTie T.J R κ v₀) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D)
  (r : HeightOneSpectrum (𝓞 D.what₂.LL) → RunData T.J) (hr : ∀ v, LawsP (r v).full.toTop)
  (p : HeightOneSpectrum (𝓞 D.what₂.LL) → ℕ)
  {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
  (ι : Bs.J → Fin D.R.m) (wL wF : ∀ i, WeightFamilies.Wt D ((ι i : ℕ) + 1)) (nT : ℕ) (inc : P →* G)
  (ℓ : ∀ i, G → (LaMod (T.Q.Dw ((ι i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((ι i : ℕ) + 1)) T.Q.l))
  (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (ph : HeightOneSpectrum (𝓞 D.what₂.LL) → Bs.J → ℂ)
  (ρ : ∀ i, Representation (recB h.toLawsCore).KO P ((recB h.toLawsCore).Cusp ((ι i : ℕ) + 1) (κ (ι i))))
  (O : OnObj S P oc)
  (z : ∀ i, (Fin (O.nZ i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
    D.what₂.LL ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp ((ι i : ℕ) + 1) (κ (ι i)))


end Tied

def blankObj (D : D7) {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst)
    (n : Bs.J → ℕ) : OnObj S P oc where
  nZ := n
  ρ _ := 1
  U := ⊥
  ψ := 1
  V₀ _ := ⊥
  e _ := 0
  Ms _ := ⊥
  φ _ := 0
  Th1 _ _ := ⊥
  Th _ _ := ⊥
  ThK _ _ := ⊥
  Th0 _ _ := ⊥
  ThJ _ _ := ⊥
  X₃ _ _ := ⊥
  σ := 0
  a := 0
  E := 0
  r1 := 0
  r2 := 0
  pde := D.host.pde
  ε0 := 0
  nX := 0
  θ' _ _ := 0
  eX _ _ := 0
  pr _ _ := 0
  Mt _ _ := ⊥
  nnK := 0
  Jp := 0
  k := D.R.k
  m := D.R.m
  f := D.R.f
  bp := 0
  Sc := 0
  eta := 0
  T := 0
  DF := 0
  X2 := 0
  x := 0
  eps := 0
  vd := 0
  rr := D.R.r
  de2 := 0
  Nc := 0
  wt := 0
  th := 0
  ad := 0
  T2 := D.host.T2.card
  g1 := D.host.g 0
  g2 := D.host.g 1
  q1 := D.host.q
  dd := D.host.d
  sm := D.host.small

section Exists

variable (h : LawsP T.toTop) (fw : FWTie T.J R κ v₀) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D)
  (r : HeightOneSpectrum (𝓞 D.what₂.LL) → RunData T.J) (hr : ∀ v, LawsP (r v).full.toTop)
  (p : HeightOneSpectrum (𝓞 D.what₂.LL) → ℕ)
  {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst)
  (ι : Bs.J → Fin D.R.m) (wL wF : ∀ i, WeightFamilies.Wt D ((ι i : ℕ) + 1)) (nT : ℕ) (inc : P →* G)

end Exists

end GlobalTheory.OnTies
end
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.OnTies
open Formalism.IndefR.Mult Formalism.IndefR.Cx
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TraceIncl

theorem mem_of_mem_span_image {K V H : Type} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V] [AddCommGroup H]
    [Module ℂ H] {σ : K →+* ℂ} (j : V →ₛₗ[σ] H)
    (hj : ∀ (n : ℕ) (b : Fin n → V), LinearIndependent K b → LinearIndependent ℂ fun k => j (b k))
    (N : Submodule K V) {z : V} (hz : j z ∈ Submodule.span ℂ (j '' (N : Set V))) : z ∈ N := by
  by_contra hn
  let b : Fin (Module.finrank K N) → V := fun k => (Module.finBasis K N k : V)
  have hb : LinearIndependent K b := (Module.finBasis K N).linearIndependent.map' N.subtype N.ker_subtype
  have hs : Submodule.span K (Set.range b) ≤ N := Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact (Module.finBasis K N k).2)
  have h1 := hj _ (Fin.cons z b) (linearIndependent_finCons.2 ⟨hb, fun h => hn (hs h)⟩)
  have h2 : (fun k => j ((Fin.cons z b : Fin (Module.finrank K N + 1) → V) k)) =
      (Fin.cons (j z) (fun k => j (b k)) : Fin (Module.finrank K N + 1) → H) := by
    funext k
    refine Fin.cases rfl (fun _ => rfl) k
  rw [h2, linearIndependent_finCons] at h1
  refine h1.2 (Submodule.span_le.2 ?_ hz)
  rintro _ ⟨x, hx, rfl⟩
  have h3 := congrArg (fun z : N => (z : V)) ((Module.finBasis K N).sum_repr ⟨x, hx⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h3

  rw [← h3, map_sum]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem exists_lvlE_eq {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) {G : Type} [Group G] [Fintype G]
    (r : Representation K G S.Forms) (X : Finset (G → K)) (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (P : Subgroup G) (ψ : P →* Kˣ)
    (y : Fin (S.BaseDimension r X P ψ) → K) : ∃ x, (S.lvlE r P ψ).mulVecLin x = (S.V0E r X P ψ).mulVecLin y := by
  obtain ⟨u, hu⟩ := (image_idempotent_spec K _ (S.gaMat r (goodAt X P ψ))).2.le ⟨y, rfl⟩
  have h : S.gaMat r (goodAt X P ψ) = S.gaMat r (lvlIdem P ψ) * S.gaMat r (idemOf X) := by
    rw [← (group_action_matrix_hom K S G r).2, (idempotent_central K G X hX).2]
    rfl
  refine (image_idempotent_spec K _ (S.gaMat r (lvlIdem P ψ))).2.ge ⟨(S.gaMat r (idemOf X)).mulVec u, ?_⟩
  refine Eq.trans ?_ hu
  rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, h]

theorem goodFormsCoordinateMap_apply {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : Formalism.L2.Indef.DefBase K} {Am : Formalism.L2.Indef.DefAmb Bs}
    (X : CxData Am) (b : Bool) (j : Bs.J) (c : Fin (X.dW b j) → ℂ) :
    X.w0C b j c = ∑ k, c k • X.eW b j (X.bW b j Bs.v0 k) := by
  show X.eW b j (∑ k, c k • X.bW b j Bs.v0 k) = _

  rw [map_sum]
  exact Finset.sum_congr rfl fun k _ => map_smul _ _ _

theorem goodFormsCoordinateMap_mem_of_lifts_mem {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : Formalism.L2.Indef.DefBase K} {Am : Formalism.L2.Indef.DefAmb Bs}
    (X : CxData Am) {fc : Formalism.L2.Indef.DefSub Am → Formalism.L2.Indef.DefFace Bs} (cr : Crd Am fc) (b : Bool) (h5 : X.H5 cr b)
    (j : Bs.J) (t : Bs.Tup) (N : Submodule ℂ (X.W j)) (h : ∀ y, X.θ' j t (X.jL j t (cr.toL X.zs b j t y)) ∈ N)
    (c : Fin (X.dW b j) → ℂ) : X.w0C b j c ∈ N := by
  obtain ⟨d, hd⟩ := (h5 j t).2.ge ⟨c, rfl⟩
  rw [← hd]
  show ∑ k, d k • X.θ' j t (X.jL j t (cr.toL X.zs b j t (Pi.single k 1))) ∈ N
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (h _)

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

theorem e_j_eOp (hU : R.LUnif) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (y : Fin (R.nW i) → D.what₂.LL) :
    (R.HW i σ).e ((R.FW i).j σ ((R.FW i).eOp (fun g => (idemOf A.X).coeff g) y)) =
      postOn _ (R.eWf i σ) ((R.HW i σ).e ((R.FW i).j σ y)) := by
  have htw : ∀ g, (R.HW i σ).e ((R.FW i).j σ (GlobalTheory.LevelForms.twRep (R.FW i) g y)) =
      postOn _ (actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g)) ((R.HW i σ).e ((R.FW i).j σ y)) := by
    intro g
    rw [GlobalTheory.LevelForms.twRep_apply, map_smulₛₗ, map_smul, (hU i σ).2.2, smul_smul, ← map_mul, Units.inv_mul, map_one,
      one_smul]

  rw [GlobalTheory.LevelForms.eOp_eq_sum, map_sum, map_sum]
  simp only [map_smulₛₗ, map_smul, htw]
  refine MultilinearMap.ext fun v => ?_
  simp only [RealDat.eWf, gaL, RealDat.eC, LinearMap.sum_apply, LinearMap.smul_apply, MultilinearMap.sum_apply,
    MultilinearMap.smul_apply, postOn_apply, RingHom.id_apply]
  all_goals rfl

theorem exists_w0C_eq (i : Fin D.R.m) {w : (R.HW i (sg0 D A)).H} (h1 : w ∈ R.WS F false i (sg0 D A)) :
    ∃ c, Tw.out (s := twAt D.what₂.embLL A.v0) ((R.toCx F).w0C false i c) = w := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 h1
  have hs : ((Real.sqrt (RealDat.nP F false) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (RealDat.nP_pos (F := F) false)).ne'
  let c' : Fin ((R.toCx F).dW false i) → ℂ :=
    fun k => cj (twAt D.what₂.embLL A.v0) (c k * ((Real.sqrt (RealDat.nP F false) : ℝ) : ℂ)⁻¹)
  have e1 := goodFormsCoordinateMap_apply (R.toCx F) false i c'
  refine ⟨c', (congrArg (Tw.out (s := twAt D.what₂.embLL A.v0)) e1).trans (Eq.trans ?_ hc)⟩
  show ∑ k, cj (twAt D.what₂.embLL A.v0) (c' k) • (((Real.sqrt (RealDat.nP F false) : ℝ) : ℂ) •
    R.bC F false i (sg0 D A) k) = _
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [cj_cj, smul_smul, inv_mul_cancel_right₀ hs]

theorem exists_srcForm_eq (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ) (i : Fin D.R.m) (t : T0)
    (Z : Submodule D.what₂.LL (A.fam.L i t).S.Forms) (y : Fin ((A.fam.L i t).dZ (A.fam.lvlA F.P0 F.ψ0) Z) → D.what₂.LL) :
    ∃ x, srcForm A i t F.P0 F.ψ0⁻¹ x = (A.fam.L i t).toF (A.fam.lvlA F.P0 F.ψ0) Z y := by
  obtain ⟨x, hx⟩ := exists_lvlE_eq (A.MtCSD i t) (A.leftGroupActionLift i t) A.X hX F.P0 F.ψ0⁻¹
    (((A.fam.L i t).zE (A.fam.lvlA F.P0 F.ψ0) Z).mulVecLin y)
  exact ⟨x, congrArg (fun u => (A.MtCSD i t).basis.equivFun.symm u) hx⟩

theorem out_lift_toL (i : Fin D.R.m) (t : T0)
    (y : Fin ((A.fam.L i t).dZ (A.fam.lvlA F.P0 F.ψ0) ((R.toCx F).zs.Zl i t)) → D.what₂.LL) :
    (R.toCx F).θ' i t ((R.toCx F).jL i t (F.cr.toL (R.toCx F).zs false i t y)) =
      Tw.mk (twAt D.what₂.embLL A.v0) (R.thG i t (jVx R i t
        ((A.fam.L i t).toF (A.fam.lvlA F.P0 F.ψ0) ((R.toCx F).zs.Zl i t) y))) := rfl

theorem j_eOp_of_adForm (hW : R.models_HW) (hG : R.thP_thG) (hU : R.LUnif) (i : Fin D.R.m) (t : T0) (ph : ℂ)
    (y : Fin (R.nW i) → D.what₂.LL) (u : (R.HV i t).H) (h0 : adForm R i y = ph • R.thF i t u) :
    (R.FW i).j (sg0 D A) ((R.FW i).eOp (fun g => (idemOf A.X).coeff g) y) = ph • R.thG i t u := by
  have h1 := e_j_eOp R hU i (sg0 D A) y
  unfold adForm at h0
  rw [h0, LinearMap.map_smul, ← hG i t u, ← LinearMap.map_smul] at h1
  exact (hW i _).1 h1

end GlobalTheory.TraceIncl
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

theorem _root_.GlobalTheory.T.thetaOrder_parameterSeries_bounded : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), g.Ok → IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → TaylorLogMetric.discr g.abelian₂ = 1 → AlgEnt (sgStar g.abelian₂) → ∀ v, v ∉ g.abelian₂ → wpF g.abelian₂ v ∈ Qbar → ∀ (k : ℕ) (G : ℂ → ℂ), AlgEnt G → (∀ ω ∈ g.abelian₂, ∀ z, G (z + ω) * sgStar g.abelian₂ z ^ k = G z * sgStar g.abelian₂ (z + ω) ^ k) → ∃ B : PowerSeries ℂ_[p], BddSer B ∧ g.atU G = ePhi1 g.lam g.abelian₂ g.C g.wq ^ k * B := by
  first | exact @GlobalTheory.ThetaOrderBdd.order_bdd | exact GlobalTheory.ThetaOrderBdd.order_bdd | (intros; apply GlobalTheory.ThetaOrderBdd.order_bdd <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

theorem _root_.GlobalTheory.T.thetaFunctions_all_levels_closure : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), (∀ (L : Lat D N) (L' : Lat D N'), SD D L → SD D L' → ∀ F ∈ Th D (tor0 D cc δ) L L', F ∈ TT D (tor0 D cc δ) N N') ∧ (∀ (z : Matrix (Fin N') (Fin N) D.host.E), ∀ F ∈ TT D (tor0 D cc δ) N N', Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) F ∈ TT D (tor0 D cc δ) N N') ∧ (∀ F ∈ TT D (tor0 D cc δ) N N', ∀ G ∈ TT D (tor0 D cc δ) N N', F + G ∈ TT D (tor0 D cc δ) N N') ∧ ∀ (a : ℂ), ∀ F ∈ TT D (tor0 D cc δ) N N', a • F ∈ TT D (tor0 D cc δ) N N' := by
  first | exact @GlobalTheory.ThetaLevels.levels_closed | exact GlobalTheory.ThetaLevels.levels_closed | (intros; apply GlobalTheory.ThetaLevels.levels_closed <;> assumption)
end

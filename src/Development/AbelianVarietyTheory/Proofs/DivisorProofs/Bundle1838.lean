module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1805
public import Formalism.LocalToGlobal.GlobalTheory.Bundle001
public import Formalism.LocalToGlobal.Columns.RowFormsGood
public import Formalism.LocalToGlobal.Columns.ToHLatLemmas
import Formalism.LocalToGlobal.GlobalTheory.HLatOpsP
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1562
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1209
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1804
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1657
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1307
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1806
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1405
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1494
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1807
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualGraph

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem evc_ev_comp {T P Y : Over S} {N : LB (A ⊗ T).left} (hN : N.IsLB) (f : P ⟶ T)
    (h : (ev N (fst A P) (snd A P ≫ f)).IsLB) (a : Y ⟶ A) (p : Y ⟶ P) : evc h a p = evc hN a (p ≫ f) := by
  rw [evc_ev hN, lift_fst, lift_snd_assoc]

theorem fam_ev {T P : Over S} {N : LB (A ⊗ T).left} (hN : Fam A N) (f : P ⟶ T) :
    Fam A (ev N (fst A P) (snd A P ≫ f)) := by
  have h : (ev N (fst A P) (snd A P ≫ f)).IsLB := pull_isLB hN.isLB _
  refine ⟨h, (isAdditive_iff h).2 fun Y a a' p ↦ ?_⟩
  rw [evc_ev_comp hN.isLB f h, evc_ev_comp hN.isLB f h, evc_ev_comp hN.isLB f h]
  exact (isAdditive_iff hN.isLB).1 hN.add Y a a' (p ≫ f)

theorem same_prod_iff {T U Y : Over S} {N : LB (A ⊗ T).left} {M : LB (A ⊗ U).left} (hN : N.IsLB) (hM : M.IsLB)
    (p : Y ⟶ T ⊗ U) :
    Same A (ev N (fst A (T ⊗ U)) (snd A (T ⊗ U) ≫ fst T U)) (ev M (fst A (T ⊗ U)) (snd A (T ⊗ U) ≫ snd T U)) p p ↔
      Same A N M (p ≫ fst T U) (p ≫ snd T U) := by
  have h₁ : (ev N (fst A (T ⊗ U)) (snd A (T ⊗ U) ≫ fst T U)).IsLB := pull_isLB hN _
  have h₂ : (ev M (fst A (T ⊗ U)) (snd A (T ⊗ U) ≫ snd T U)).IsLB := pull_isLB hM _
  rw [same_iff h₁ h₂, same_iff hN hM, evc_ev_comp hN _ h₁, evc_ev_comp hM _ h₂, Category.assoc, Category.assoc]

theorem exists_mono_same : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A →
    ∀ (T U : Over S) [IsLocallyNoetherian T.left] [LocallyOfFiniteType U.hom] (N : LB (A ⊗ T).left)
      (M : LB (A ⊗ U).left), Fam A N → Fam A M → Inj A M → ∃ (G : Over S) (π : G ⟶ T), Mono π.left ∧
        LocallyOfFiniteType π.left ∧ ∀ (Y : Over S) (y : Y ⟶ T),
          (∃ u : Y ⟶ U, Same A N M y u) ↔ ∃ z : Y.left ⟶ G.left, z ≫ π.left = y.left := by
  intro S A _ hA T U _ _ N M hN hM hI
  have hf : LocallyOfFiniteType (fst T U).left := by
    show LocallyOfFiniteType (pullback.fst T.hom U.hom)
    infer_instance
  haveI : IsLocallyNoetherian (T ⊗ U).left := LocallyOfFiniteType.isLocallyNoetherian (fst T U).left
  obtain ⟨G, i, hi, hG⟩ := GlobalTheory.DualLocus.exists_closed_same S A (T ⊗ U) hA _ _ (fam_ev hN (fst T U))
    (fam_ev hM (snd T U))
  have key : ∀ (Y : Over S) (z : Y ⟶ G), Same A N M (z ≫ i ≫ fst T U) (z ≫ i ≫ snd T U) := fun Y z ↦ by
    rw [← Category.assoc, ← Category.assoc, ← same_prod_iff hN.isLB hM.isLB]
    exact (hG Y (z ≫ i)).2 ⟨z, rfl⟩
  have hw : i.left ≫ (fst T U).left ≫ T.hom = G.hom := by
    rw [Over.w (fst T U), Over.w i]
  refine ⟨G, i ≫ fst T U, ⟨fun {W} a b hab ↦ ?_⟩, ?_, fun Y y ↦ ⟨?_, ?_⟩⟩
  · let Y : Over S := Over.mk (a ≫ G.hom)
    let a' : Y ⟶ G := Over.homMk a rfl
    let b' : Y ⟶ G := Over.homMk b (by
      show b ≫ G.hom = a ≫ G.hom
      simp only [Over.comp_left] at hab
      rw [← hw, reassoc_of% hab])
    have e₁ : a' ≫ i ≫ fst T U = b' ≫ i ≫ fst T U := Over.OverMorphism.ext (by
      simpa only [Over.comp_left, a', b', Over.homMk_left] using hab)
    have e₂ : a' ≫ i ≫ snd T U = b' ≫ i ≫ snd T U := by
      refine hI Y _ _ ((same_iff hM.isLB hM.isLB _ _).2 ?_)
      rw [← (same_iff hN.isLB hM.isLB _ _).1 (key Y a'), ← (same_iff hN.isLB hM.isLB _ _).1 (key Y b'), e₁]
    have e : a' ≫ i = b' ≫ i := by
      rw [← Category.assoc, ← Category.assoc] at e₁ e₂
      exact CartesianMonoidalCategory.hom_ext _ _ e₁ e₂
    have e' := congrArg (fun q : Y ⟶ T ⊗ U ↦ q.left) e
    simp only [Over.comp_left, a', b', Over.homMk_left] at e'
    exact (cancel_mono i.left).1 e'
  · rw [Over.comp_left]
    infer_instance
  · rintro ⟨u, hu⟩
    have hs := (same_prod_iff hN.isLB hM.isLB (lift y u)).2 (by rwa [lift_fst, lift_snd])
    obtain ⟨z, hz⟩ := (hG Y (lift y u)).1 hs
    refine ⟨z.left, ?_⟩
    rw [← Over.comp_left, ← Category.assoc, hz, lift_fst]
  · rintro ⟨z, hz⟩
    let z' : Y ⟶ G := Over.homMk z (by
      show z ≫ G.hom = Y.hom
      rw [← hw, ← Over.w y, ← hz, Over.comp_left]
      simp only [Category.assoc])
    have ey : z' ≫ i ≫ fst T U = y := Over.OverMorphism.ext (by
      simpa only [Over.comp_left, z', Over.homMk_left] using hz)
    refine ⟨z' ≫ i ≫ snd T U, ?_⟩
    have := key Y z'
    rwa [ey] at this

end GlobalTheory.DualGraph
end
end

section

namespace GlobalTheory.FamilyFrames

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

theorem posDef_sum_dep {ι γ : Type} {κ : γ → Type} [Fintype ι] [Fintype γ] [∀ c, Fintype (κ c)]
    (G : ∀ c, Matrix (κ c) (κ c) ℂ) (hG : ∀ c, (G c).PosDef) (P : ∀ c, Matrix (κ c) ι ℂ)
    (hinj : ∀ x, (∀ c, P c *ᵥ x = 0) → x = 0) : (∑ c, (P c)ᴴ * G c * P c).PosDef := by
  have hs : ∀ c, ((P c)ᴴ * G c * P c).PosSemidef := fun c =>
    (hG c).posSemidef.conjTranspose_mul_mul_same (P c)
  have hS := Matrix.posSemidef_sum (s := Finset.univ) (fun c _ => hs c)
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hS.1 fun x hx => ?_
  rw [Matrix.sum_mulVec, dotProduct_sum]
  obtain ⟨c, hc⟩ : ∃ c, P c *ᵥ x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx (hinj x hcon)
  refine Finset.sum_pos' (fun c _ => (hs c).dotProduct_mulVec_nonneg x) ⟨c, Finset.mem_univ c, ?_⟩
  have h1 := (hG c).dotProduct_mulVec_pos hc
  have h2 : star x ⬝ᵥ (((P c)ᴴ * G c * P c) *ᵥ x) = star (P c *ᵥ x) ⬝ᵥ (G c *ᵥ (P c *ᵥ x)) := by
    simp only [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  rw [h2]
  exact h1

section Generic

open Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLatticesTheory

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem isSesq_pi {γ : Type} [Fintype γ] {V : γ → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module K (V c)]
    (H : ∀ c, InfinitePlace K → V c → V c → ℂ) (hH : ∀ c, IsSesq (H c)) :
    IsSesq (fun v (x y : ∀ c, V c) => ∑ c, H c v (x c) (y c)) := by
  intro v
  refine ⟨fun x x' y => ?_, fun x y y' => ?_, fun a x y => ?_, fun a x y => ?_⟩
  · simp only [Pi.add_apply, fun c => (hH c v).1, Finset.sum_add_distrib]
  · simp only [Pi.add_apply, fun c => (hH c v).2.1, Finset.sum_add_distrib]
  · simp only [Pi.smul_apply, fun c => (hH c v).2.2.1, Finset.mul_sum]
  · simp only [Pi.smul_apply, fun c => (hH c v).2.2.2, Finset.mul_sum]

theorem posAt_pi {γ : Type} [Fintype γ] [DecidableEq γ] {V : γ → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module K (V c)]
    {κ : γ → Type} [∀ c, Fintype (κ c)] [∀ c, DecidableEq (κ c)] (b : ∀ c, Basis (κ c) K (V c))
    (H : ∀ c, InfinitePlace K → V c → V c → ℂ) (hH : ∀ c, IsSesq (H c)) (hP : ∀ c, PosAt (b c) (H c)) :
    PosAt (Pi.basis b) (fun v (x y : ∀ c, V c) => ∑ c, H c v (x c) (y c)) := by
  intro v
  let P : ∀ c, Matrix (κ c) (Σ c, κ c) ℂ := fun c => Matrix.of fun i s => vecAt (b c) v (Pi.basis b s c) i
  have hgram : gramOf (Pi.basis b) (fun (x y : ∀ c, V c) => ∑ c, H c v (x c) (y c)) =
      ∑ c, (P c)ᴴ * gramOf (b c) (H c v) * P c := by
    ext s t
    simp only [Matrix.sum_apply]
    rw [gramOf, Matrix.of_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [sesq_eq_sum (hH c) (b c) v]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul, P, Matrix.of_apply]
    rw [Finset.sum_comm]
    rfl
  rw [hgram]
  refine posDef_sum_dep _ (fun c => hP c v) P fun x hx => ?_
  funext ⟨c, i⟩
  have h1 := congrFun (hx c) i
  have h2 : ∀ s, P c i s = if s = ⟨c, i⟩ then 1 else 0 := by
    intro s
    have : P c i s = v.embedding ((Pi.basis b).repr (Pi.basis b s) ⟨c, i⟩) := by
      rw [Pi.basis_repr]
      rfl
    rw [this, Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simp
  simpa [Matrix.mulVec, dotProduct, h2] using h1

theorem exists_frames {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (H : InfinitePlace K → V → V → ℂ) (hH : IsSesq H) (hP : PosAt b H) :
    ∃ (n : ℕ) (e : (Fin n → K) ≃ₗ[K] V) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ), (∀ v, IsUnit (X v).det) ∧
      ∀ v x, ((normAt (Pi.basisFun K (Fin n)) X v x ^ 2 : ℝ) : ℂ) = H v (e x) (e x) := by
  let e : (Fin (Fintype.card ι) → K) ≃ₗ[K] V := (b.reindex (Fintype.equivFin ι)).equivFun.symm
  let c := Pi.basisFun K (Fin (Fintype.card ι))
  have hH' := isSesq_comp hH e.toLinearMap
  have hP' := posAt_comp b c hH hP e.toLinearMap e.injective
  have hs := fun v => frameOf_spec (hP' v)
  refine ⟨_, e, fun v => frameOf (gramOf c fun x y => H v (e x) (e y)), fun v => (hs v).1, fun v x => ?_⟩
  rw [← majAt_self]
  have e1 := sesq_eq_sum (isSesq_maj c (fun v => frameOf (gramOf c fun x y => H v (e x) (e y)))) c v x x
  have e2 := sesq_eq_sum hH' c v x x
  rw [gramOf_maj] at e1
  refine e1.trans (Eq.trans ?_ e2.symm)
  have e3 := (hs v).2
  simp only [LinearEquiv.coe_coe] at e3 ⊢
  rw [e3]

theorem famFramed_of_pos (F : Formalism.L2.Col.GFam K) (h : F.Ok)
    (hpos : ∀ b (v : InfinitePlace K), ((F.mem b).gramV.map v.embedding).PosDef) : GlobalTheory.ColRows.FamFramed F h :=
  exists_frames (Pi.basis fun b => (F.mem b).hB (h b)) _
    (isSesq_pi (fun b v (φ ψ : (F.mem b).EqFun) => (F.mem b).ipAt (h b) v φ ψ) fun b => (F.mem b).isSesq_ipAt (h b))
    (posAt_pi _ (fun b v (φ ψ : (F.mem b).EqFun) => (F.mem b).ipAt (h b) v φ ψ) (fun b => (F.mem b).isSesq_ipAt (h b))
      fun b => (F.mem b).posAt_ipAt (h b) (hpos b) _)

end Generic

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef _root_.Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

theorem famFramed_chF : ∀ (X : Fields) (hX : X.Ok) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (I : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (u : Pr.Word) (j : ℕ) (h : (chF W sel mu I u j).Ok), FamFramed (chF W sel mu I u j) h := by
  intro X hX Pr R W _ sel Sg mu I u j h
  exact famFramed_of_pos _ h fun _ v =>
    (roundPk_ratP (W.lamTrue u j) (fun d : DecoSet (E := X.E) (n := R.N j) (ST := Pr.vT u) (SG := Pr.vGs) => d.1.Lsh) hX).pos v

end GlobalTheory.FamilyFrames
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem ratRigid_of_isSemiAbelian : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G →
    ∀ (F : Type) [Field F] [CharZero F] (b : Sp F ⟶ S), RatRigid G b := by
  intro S G _ hG F _ _ b
  let Ω := AlgebraicClosure F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have hE : Nonempty (TorusExtension ((Over.pullback (spMap (algebraMap F Ω) ≫ b)).obj G)) :=
    hG.fibres Ω (spMap (algebraMap F Ω) ≫ b)
  have h1 := GlobalTheory.T.rationalSquaringPathsRigid_of_torusExtension Ω ((Over.pullback (spMap (algebraMap F Ω) ≫ b)).obj G) hE
  have h2 := GlobalTheory.T.rationalSquaringPathsRigid_of_fibre S G Ω (spMap (algebraMap F Ω) ≫ b) h1
  exact GlobalTheory.T.rationalSquaringPathsRigid_descends_field_map S G F Ω (algebraMap F Ω) b h2

end GlobalTheory.Nef
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.conjugateLift_of_characterisationClauses : (∀ {D : D7} {G
    : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks
    : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F
    : Face D A), GlobalTheory.Core5 R F → ∀ (i
    : Fin D.R.m), ∀ gramR c0R c0L, Comparison₂ R gramR c0R c0L → ∀ (σ
    : D.what₂.LL →+* ℂ), OverK σ → ∃ (c : CoefA (Vc D i)) (c₁
    : VsV D i D.what₂.LL →ₛₗ[σ] c.W), CoefAt i σ c c₁) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype
    G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField
    Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i
    : Fin D.R.m), ∀ gramR c0R c0L, Comparison₂ R gramR c0R c0L → ∀ (σ : D.what₂.LL →+* ℂ) (c
    : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W), CoefAt i σ c c₁ → ∃ (H : HMod (Bridge.Gf
    (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), IsConjForms R i σ (c0L
    i) c c₁ H j) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A
    : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks
    D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i
    : Fin D.R.m), ∀ gramR c0R c0L, Comparison₂ R gramR c0R c0L → ∀ gramR' c0R' c0L', Comparison₂ R gramR' c0R' c0L' → ∀ (σ
    : D.what₂.LL →+* ℂ) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H
    : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), IsConjForms R i σ (c0L'
    i) c c₁ H j → ∃ c₁' : VsV D i D.what₂.LL →ₛₗ[σ] c.W, IsConjForms R i σ (c0L
    i) c c₁' H j) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A
    : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks
    D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i
    : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), OverK σ → ∃ f₀ f B, VecData R i σ f₀ f B) ∧ (∀ {D
    : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks
    : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F
    : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ) (μ' η' : (AE
    D)ˣ →* Circle) (c₀ : VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W) (c : CoefA (Vc D i)) (c₁
    : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j
    : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), IsConjForms R i σ c₀ c c₁ H j → ∀ (ω : GA D (Vc D
    i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)) (f₀ f : WO (Vc D i) (Wc D
    i) → ℂ) (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (io : LowT (R.MW i
    σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank), IsWeilDatumO R.ψ (Vc D i) (Wc D
    i) μ' (μ' * η'⁻¹) ω → VecData R i σ f₀ f B → ∃ thP, Lift.IsThetaP (R.νV i A.μ0) (R.fdV i
    A.μ0) (fun g h φ => thetaKO ω h g φ) (ptAt R i σ B f) io (LinearMap.range (c.ext ∘ₗ
    H.e)) thP) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A
    : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks
    D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i
    : Fin D.R.m), ∀ gramR c0R c0L, Comparison₂ R gramR c0R c0L → ∀ (σ
    : D.what₂.LL →+* ℂ), OverK σ → ∀ (μ' η' : (AE D)ˣ →* Circle) (c : CoefA (Vc D i)) (c₁
    : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j
    : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), IsConjForms R i σ (c0L i) c c₁ H j → ∀ (ω : GA D (Vc D
    i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)) (f₀ f : WO (Vc D i) (Wc D
    i) → ℂ) (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (io : LowT (R.MW i
    σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (thP : LinearMap.range (c.ext ∘ₗ
    H.e) →ₗ[ℂ] (LowT (R.MW i σ) →ₗ[ℂ] (GA D (Wc D i) →
    ℂ))), LiftData R i σ μ' η' c H ω f₀ f B io thP → ∀ v : ∀ ρ, lowT (R.MW i σ) ρ, IsExtVec (R.MW i
    σ) (fun ρ => v ρ) → (∀ x, ∃ t : (R.HW i σ).H, (R.HW i σ).e t (fun ρ => v ρ) = thP ((c.ext ∘ₗ
    H.e).rangeRestrict (j x)) (PiTensorProduct.tprod ℂ v)) → ∃ th, IsProjOf R i σ thP th) := by
  first | exact @GlobalTheory.GalLift.conjLift_five | exact GlobalTheory.GalLift.conjLift_five | (intros; apply GlobalTheory.GalLift.conjLift_five <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MultHol

section Local

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {Hm : ι → Mt n}

omit [Fintype ι] [DecidableEq ι] in
theorem one_mem_UG : (1 : ι → Mt n) ∈ UG Hm := fun τ => by
  show (1 : Mt n)ᴴ * Hm τ * 1 = Hm τ
  simp

omit [Fintype ι] [DecidableEq ι] in
theorem mul_mem_UG {u u' : ι → Mt n} (hu : u ∈ UG Hm) (hu' : u' ∈ UG Hm) : u * u' ∈ UG Hm := fun τ => by
  have h1 : (u τ)ᴴ * Hm τ * u τ = Hm τ := hu τ
  have h2 : (u' τ)ᴴ * Hm τ * u' τ = Hm τ := hu' τ
  show (u τ * u' τ)ᴴ * Hm τ * (u τ * u' τ) = Hm τ
  calc _ = (u' τ)ᴴ * ((u τ)ᴴ * Hm τ * u τ) * u' τ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Hm τ := by rw [h1, h2]

omit [Fintype ι] in
theorem mulSingle_mem_UG (τ : ι) {g : Mt n} (hg : g ∈ Formalism.QuantumDeterminants.UH (Hm τ)) :
    (Pi.mulSingle τ g : ι → Mt n) ∈ UG Hm := fun ρ => by
  by_cases h : ρ = τ
  · subst h; simpa using hg
  · rw [Pi.mulSingle_eq_of_ne h]; exact one_mem_UG (Hm := Hm) ρ

omit [Fintype ι] [DecidableEq ι] in
theorem lift_prod {G : Type} [Group G] (L : (ι → Mt n) → G)
    (hL : ∀ u ∈ UG Hm, ∀ u' ∈ UG Hm, L (u * u') = L u * L u') (l : List (ι → Mt n)) (hl : ∀ u ∈ l, u ∈ UG Hm) :
    l.prod ∈ UG Hm ∧ L l.prod = (l.map L).prod := by
  induction l with
  | nil =>
    refine ⟨one_mem_UG, ?_⟩
    have h := hL 1 one_mem_UG 1 one_mem_UG
    rw [mul_one] at h
    simpa using h
  | cons a l ih =>
    have ha := hl a (List.mem_cons_self ..)
    obtain ⟨h1, h2⟩ := ih fun u hu => hl u (List.mem_cons_of_mem _ hu)
    rw [List.prod_cons, List.map_cons, List.prod_cons]
    exact ⟨mul_mem_UG ha h1, by rw [hL a ha _ h1, h2]⟩

theorem parts_mem_lieH {G : Mt n} (hh : G.IsHermitian) (hd : G.det ≠ 0) (Z : Mt n) :
    (1 / 2 : ℂ) • (Z + conjH G Z) ∈ lieH G ∧ (1 / (2 * Complex.I)) • (Z - conjH G Z) ∈ lieH G := by
  have hu : IsUnit G.det := isUnit_iff_ne_zero.2 hd
  have e1 : G * conjH G Z = -(Zᴴ * G) := by
    rw [conjH, Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
  have e2 : (conjH G Z)ᴴ * G = -(G * Z) := by
    have := congrArg conjTranspose e1
    simpa only [conjTranspose_mul, conjTranspose_neg, conjTranspose_conjTranspose, hh.eq] using this
  constructor
  · show _ + _ = _
    have s : star (1 / 2 : ℂ) = 1 / 2 := by simp
    rw [conjTranspose_smul, s, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, conjTranspose_add, Matrix.add_mul,
      Matrix.mul_add, e1, e2]
    simp
  · show _ + _ = _
    have s : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by
      simp
    rw [conjTranspose_smul, s, Matrix.smul_mul, Matrix.mul_smul, neg_smul, ← smul_neg, ← smul_add, conjTranspose_sub,
      Matrix.sub_mul, Matrix.mul_sub, e1, e2]
    have : -(Zᴴ * G - -(G * Z)) + (G * Z - -(Zᴴ * G)) = 0 := by abel
    rw [this, smul_zero]

end Local

theorem holAd_of_isMultMap : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (v : M.Vec), IsInfFam θ → HolShape M → WtIs M w → IsExtVec M v → ∀ (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M), IsMultMap θ M J χ T → HolAd θ M w (T v) := by
  classical
  intro D θ V S M w v hθ hS hw hv J χ T hT g
  obtain ⟨L, -, hmul, -, -, hinv, hat, -, -, hG⟩ := GlobalTheory.RealLift.exists_real_lift D θ V hθ
  have hexp : ∀ τ, ∀ X ∈ lieH (gramAt D V τ), ∀ t : ℝ, NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) :=
    fun τ X hX t => GlobalTheory.SmVec.exp_mem_UH ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (hG τ).2)) hX t
  have hone : ∀ τ, ∀ X ∈ lieH (gramAt D V τ), ∀ t : ℝ,
      L (Pi.mulSingle τ (NormedSpace.exp (t • X))) = oneP θ V τ X t :=
    fun τ X hX t => (hat τ _ (hexp τ X hX t)).symm
  refine ⟨fun u => T v (g * L u), ?_, fun u hu => by simp only [hinv u hu]⟩
  refine GlobalTheory.T.holomorphicType_of_smooth_borelKilled _ _ _ _ _ _ (fun τ => ((GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ).2.2.2 hS).1) _ ?_ ?_
  · intro k τs Xs hX u hu
    have h := (hT.aut v).smooth k τs Xs hX (g * L u)
    convert h using 2 with t
    obtain ⟨h1, h2⟩ := lift_prod L hmul
      (List.ofFn fun i => (Pi.mulSingle (τs i) (NormedSpace.exp (t i • Xs i)) : D.what₂.Tau → Mt V.rank)) (by
        intro x hx
        obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
        exact mulSingle_mem_UG _ (hexp _ _ (hX i) _))
    show T v (g * L (u * _)) = _
    rw [hmul u hu _ h1, h2, List.map_ofFn, mul_assoc]
    exact congrArg (fun F : Fin k → GA D V => T v (g * (L u * (List.ofFn F).prod))) (funext fun i => hone _ _ (hX i) _)
  · intro τ a c hac u hu
    have hder : ∀ X ∈ lieH (gramAt D V τ), der τ X (fun u => T v (g * L u)) u = Rder θ V τ X (T v) (g * L u) := by
      intro X hX
      unfold der Rder
      congr 1
      funext t
      show T v (g * L (u * _)) = _
      rw [hmul u hu _ (mulSingle_mem_UG _ (hexp _ _ hX _)), hone τ X hX, mul_assoc]
    obtain ⟨p1, p2⟩ := parts_mem_lieH (hG τ).1 (hG τ).2 (x0Mat M τ * Matrix.single a c 1 * (x0Mat M τ)⁻¹)
    have hk := (GlobalTheory.T.baseFrameBorel_acts_extremalVector_by_weight D θ V S M w v hθ hS hw hv τ).2 a c hac
    have hd := GlobalTheory.T.multiplicityMap_complexRightDerivative_eq D θ V hθ S M J χ T hT v τ (x0Mat M τ * Matrix.single a c 1 * (x0Mat M τ)⁻¹)
      (if a = c then (w τ a : ℂ) • v τ else 0) (by rw [hk]; split_ifs <;> rfl)
    have e : derC (gramAt D V) τ (x0Mat M τ * Matrix.single a c 1 * (x0Mat M τ)⁻¹) (fun u => T v (g * L u)) u =
        RderC θ V τ (x0Mat M τ * Matrix.single a c 1 * (x0Mat M τ)⁻¹) (T v) (g * L u) := by
      unfold derC
      rw [hder _ p1, hder _ p2]
      rfl
    rw [e, hd]
    split_ifs
    · rw [T.map_update_smul, Function.update_eq_self]
      rfl
    · rw [T.map_update_zero]
      rfl

end GlobalTheory.MultHol
end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

theorem _root_.GlobalTheory.T.exists_archimedean_lift_unitaryGroupProduct : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∃ L : (D.what₂.Tau → Mt V.rank) → GA D V, (∀ u ∈ UG (gramAt D V), L u ∈ GinfC V ∧ ∀ τ, archM V (θ τ) (L u) = u τ) ∧ (∀ u ∈ UG (gramAt D V), ∀ u' ∈ UG (gramAt D V), L (u * u') = L u * L u') ∧ ContinuousOn L (UG (gramAt D V)) ∧ (∀ g, (fun τ => archM V (θ τ) g) ∈ UG (gramAt D V)) ∧ (∀ u ∈ GinfC V, L (fun τ => archM V (θ τ) u) = u) ∧ (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), atTau θ V τ g = L (Pi.mulSingle τ g)) ∧ (∀ g, ∃ a ∈ GfC V, ∃ u ∈ GinfC V, g = a * u) ∧ (∀ a ∈ GfC V, ∀ u ∈ GinfC V, a * u = u * a) ∧ ∀ τ, (gramAt D V τ).IsHermitian ∧ (gramAt D V τ).det ≠ 0 := by
  first | exact @GlobalTheory.RealLift.exists_real_lift | exact GlobalTheory.RealLift.exists_real_lift | (intros; apply GlobalTheory.RealLift.exists_real_lift <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.bounded_automorphic_has_representative : ∀ (D : D7) (V : HSp D), ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (ρ : GA D V →* (Lp ℂ 2 (nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (nuQ V μ 𝓕))), FinPair V μ 𝓕 → IsReg V μ 𝓕 ρ → (∀ φ : GA D V → ℂ, Continuous φ → (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) → (∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C) → ∃ F, Repr V μ 𝓕 F φ) ∧ (∀ F ψ ψ', Continuous ψ → Continuous ψ' → Repr V μ 𝓕 F ψ → Repr V μ 𝓕 F ψ' → ψ = ψ') ∧ (∀ F F' ψ, Repr V μ 𝓕 F ψ → Repr V μ 𝓕 F' ψ → F = F') ∧ (∀ F ψ g, Repr V μ 𝓕 F ψ → Repr V μ 𝓕 (ρ g F) (rTr V g ψ)) ∧ (∀ F F' ψ ψ' (a : ℂ), Repr V μ 𝓕 F ψ → Repr V μ 𝓕 F' ψ' → Repr V μ 𝓕 (a • F + F') (a • ψ + ψ')) ∧ ∀ F F' ψ ψ', Repr V μ 𝓕 F ψ → Repr V μ 𝓕 F' ψ' → IntegrableOn (fun x => star (ψ x) * ψ' x) 𝓕 μ ∧ ⟪F, F'⟫_ℂ = ∫ x in 𝓕, star (ψ x) * ψ' x ∂μ := by
  first | exact @GlobalTheory.HolDict.RepresentativeL2.repr_properties | exact GlobalTheory.HolDict.RepresentativeL2.repr_properties | (intros; apply GlobalTheory.HolDict.RepresentativeL2.repr_properties <;> assumption)
end

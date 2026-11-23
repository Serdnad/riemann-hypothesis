module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle132
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechVanishingFromCover
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonTensor
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

open GroundTheory.Automorphic.HarishChandra

namespace GlobalTheory.CompanionTheory.PresRho

variable {n : ℕ}

namespace Verma

def lowPart (m : Fin n × Fin n →₀ ℕ) : Fin n × Fin n →₀ ℕ := m.filter fun a => IsLower a

theorem lowExp_lowPart (m : Fin n × Fin n →₀ ℕ) : LowExp (lowPart m) := by
  intro a ha
  rw [lowPart, Finsupp.support_filter, Finset.mem_filter] at ha
  exact ha.2

theorem canon_lowPart (m : Fin n × Fin n →₀ ℕ) :
    canon (lowPart m) = word (blockW (lowL n) m) := by
  have hd : ∀ a ∈ diagL n, lowPart m a = 0 := fun a ha => by
    rw [lowPart, Finsupp.filter_apply_neg]
    exact not_lower_of_diag (mem_diagL.1 ha)
  have hu : ∀ a ∈ upL n, lowPart m a = 0 := fun a ha => by
    rw [lowPart, Finsupp.filter_apply_neg]
    exact not_lower_of_upper (mem_upL.1 ha)
  rw [canon_eq_blocks, blockW_eq_nil hd, blockW_eq_nil hu]
  simp only [word_nil, mul_one]
  refine congrArg word (blockW_congr fun a ha => ?_)
  rw [lowPart, Finsupp.filter_apply_pos _ _ (mem_lowL.1 ha)]

theorem wt_lowPart {m : Fin n × Fin n →₀ ℕ} (hu : ¬ HasUpper m) : wt (lowPart m) = wt m := by
  funext k
  rw [wt, wt, lowPart, Finsupp.sum_filter_index, Finsupp.support_filter, Finsupp.sum]
  refine Finset.sum_filter_of_ne fun a ha hne => ?_
  rcases lt_trichotomy a.1 a.2 with h | h | h
  · exact absurd ⟨a, h, Finsupp.mem_support_iff.1 ha⟩ hu
  · exfalso
    apply hne
    have : rootAt a k = 0 := by simp [rootAt, h]
    rw [this, mul_zero]
  · exact h

theorem wt_eq_of_mem_support {μ : Fin n → ℤ} {x : U n} (hx : IsAdW μ x)
    {m : Fin n × Fin n →₀ ℕ} (hm : m ∈ (pbw.repr x).support) : wt m = μ := by
  funext k
  set s := (pbw.repr x).support
  set c := fun m => pbw.repr x m
  have hxs : x = ∑ m ∈ s, c m • canon m := (sum_repr_canon x).symm
  have h0 : ∑ m ∈ s, (c m * ((wt m k : ℂ) - (μ k : ℂ))) • canon m = 0 := by
    have h1 := sub_eq_zero.2 (hx k)
    rw [← h1]
    conv_rhs => rw [hxs]
    rw [Finset.mul_sum, Finset.sum_mul, Finset.smul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, e_diag_mul_canon_sub, smul_smul, smul_smul,
      ← sub_smul, mul_sub, mul_comm (μ k : ℂ)]
  have h2 := linearIndependent_iff'.1 linearIndependent_canon s _ h0 m hm
  have hc : c m ≠ 0 := Finsupp.mem_support_iff.1 hm
  have h3 := sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_left hc)
  exact_mod_cast h3

theorem canon_mem {μ : Fin n → ℤ} {m : Fin n × Fin n →₀ ℕ} (hw : wt m = μ) :
    canon m ∈ lowSpanW μ ⊔ vermaIdeal (rhoVec n) := by
  by_cases hu : HasUpper m
  · exact Submodule.mem_sup_right (nPlusU_le_vermaIdeal _ (canon_mem_nPlusU hu))
  · have hnil : blockW (upL n) m = [] := blockW_eq_nil fun a ha => by
      by_contra h
      exact hu ⟨a, mem_upL.1 ha, h⟩
    set p : MvPolynomial (Fin n) ℂ := MvPolynomial.monomial (diagExp m) 1
    set ev : ℂ := MvPolynomial.eval (rhoVec n) p
    have hdec : canon m = ev • canon (lowPart m) +
        word (blockW (lowL n) m) * (hcEmb p - algebraMap ℂ (U n) ev) := by
      rw [canon_eq_triangular, hnil, canon_lowPart, mul_sub, word_nil, mul_one,
        Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]
      abel
    rw [hdec]
    refine Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨lowPart m, lowExp_lowPart m, (wt_lowPart hu).trans hw, rfl⟩)) ?_
    exact mul_mem_vermaIdeal _ _ (hcEmb_sub_eval_mem_vermaIdeal _ p)

end Verma

theorem mem_lowSpanW_sup_vermaIdeal_of_isAdW {n : ℕ} (μ : Fin n → ℤ) (x : U n) (hx : IsAdW μ x) :
    x ∈ lowSpanW μ ⊔ vermaIdeal (rhoVec n) := by
  rw [← sum_repr_canon x]
  exact Submodule.sum_mem _ fun m hm =>
    Submodule.smul_mem _ _ (Verma.canon_mem (Verma.wt_eq_of_mem_support hx hm))

end GlobalTheory.CompanionTheory.PresRho
end
end

section

noncomputable section

open GroundTheory.Automorphic.HarishChandra GlobalTheory.CompanionTheory.PresRho

namespace GlobalTheory.CompanionTheory.PresRho

theorem eq_zero_of_sum_weightVec {ι κ A : Type} [DecidableEq ι] [AddCommGroup A] [Module ℂ A]
    (T : κ → Module.End ℂ A) (f : ι → κ → ℂ) (hf : Function.Injective f) (s : Finset ι) :
    ∀ v : ι → A, (∀ i ∈ s, ∀ k, T k (v i) = f i k • v i) → ∑ i ∈ s, v i = 0 →
      ∀ i ∈ s, v i = 0 :=
  _root_.UpperTheory.Reformulated.B.P6.r14a.GlobalTheory.CompanionTheory.PresRho.eq_zero_of_sum_weightVec T f hf s

def wtPart {n : ℕ} (x : U n) (w : Fin n → ℤ) : U n :=
  ∑ m ∈ (pbw.repr x).support.filter (fun m => wt m = w), pbw.repr x m • canon m

theorem isAdW_wtPart {n : ℕ} (x : U n) (w : Fin n → ℤ) : IsAdW w (wtPart x w) := by
  intro k
  simp only [wtPart, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, e_diag_mul_canon_sub,
    (Finset.mem_filter.1 hm).2, smul_comm]

theorem sum_wtPart {n : ℕ} (x : U n) :
    ∑ w ∈ (pbw.repr x).support.image wt, wtPart x w = x := by
  simp only [wtPart]
  rw [Finset.sum_fiberwise_of_maps_to (fun m hm => Finset.mem_image_of_mem _ hm)]
  exact sum_repr_canon x

theorem mem_span_isAdW_of_kills {n : ℕ} {A : Type} [AddCommGroup A] [Module ℂ A]
    (φ : U n →ₐ[ℂ] Module.End ℂ A) (t : A) (hd : ∀ k, φ (e (k, k)) t = rhoVec n k • t)
    (x : U n) (hx : φ x t = 0) :
    x ∈ Submodule.span ℂ {y : U n | ∃ μ : Fin n → ℤ, IsAdW μ y ∧ φ y t = 0} := by
  classical
  have hinj : Function.Injective (fun (w : Fin n → ℤ) (k : Fin n) => rhoVec n k + (w k : ℂ)) := by
    intro w w' h
    funext k
    have := congrFun h k
    simpa using this
  have hz := eq_zero_of_sum_weightVec (fun k : Fin n => φ (e (k, k)))
    (fun (w : Fin n → ℤ) k => rhoVec n k + (w k : ℂ)) hinj ((pbw.repr x).support.image wt)
    (fun w => φ (wtPart x w) t)
    (fun w _ k => by
      have h1 : e (k, k) * wtPart x w = wtPart x w * e (k, k) + (w k : ℂ) • wtPart x w := by
        rw [← isAdW_wtPart x w k]; abel
      have h2 := congrArg (fun u => φ u t) h1
      simp only [map_mul, map_add (f := _), map_smul, Module.End.mul_apply, LinearMap.add_apply,
        LinearMap.smul_apply, hd k, add_smul] at h2 ⊢
      rw [h2])
    (by
      have h3 := congrArg (fun u => φ u t) (sum_wtPart x)

      simp only [map_sum, LinearMap.sum_apply] at h3
      rw [h3, hx])
  rw [← sum_wtPart x]
  exact Submodule.sum_mem _ fun w hw => Submodule.subset_span ⟨w, isAdW_wtPart x w, hz w hw⟩

end GlobalTheory.CompanionTheory.PresRho
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

universe w v u

namespace GlobalTheory.CompanionTheory.CosieveBC

open GlobalTheory.CompanionTheory.CosieveMV

section Cochains

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R)

abbrev cw (W : ObjectProperty C) : Cx.{max u v w} R := CH.cx (W.ι ⋙ F)

abbrev supP (U V : ObjectProperty C) : ObjectProperty C := fun T => U T ∨ V T

abbrev infP (U V : ObjectProperty C) : ObjectProperty C := fun T => U T ∧ V T

variable {U V : ObjectProperty C}

theorem le_supL : U ≤ supP U V := fun _ h => Or.inl h
theorem le_supR : V ≤ supP U V := fun _ h => Or.inr h
theorem inf_leL : infP U V ≤ U := fun _ h => h.1
theorem inf_leR : infP U V ≤ V := fun _ h => h.2

def liftW {W P : ObjectProperty C} (hP : Cosieve P) {n : ℕ} (t : ComposableArrows W.FullSubcategory n)
    (h : P (t.obj 0).obj) : ComposableArrows P.FullSubcategory n :=
  liftCh hP (t ⋙ W.ι) h

variable (U V)

def mvF : Cx.Hom (cw F (supP U V)) (prodCx (cw F U) (cw F V)) (RingHom.id R) where
  f n := LinearMap.prod ((resU F le_supL).pullC n) ((resU F le_supR).pullC n)
  comm n x := Prod.ext ((resU F le_supL).d_pullC n x) ((resU F le_supR).d_pullC n x)

def mvG : Cx.Hom (prodCx (cw F U) (cw F V)) (cw F (infP U V)) (RingHom.id R) where
  f n := ((resU F inf_leL).pullC n).comp (LinearMap.fst R _ _) - ((resU F inf_leR).pullC n).comp (LinearMap.snd R _ _)
  comm n x := by
    change CH.d _ n ((resU F inf_leL).pullC n x.1 - (resU F inf_leR).pullC n x.2) =
      (resU F inf_leL).pullC (n + 1) (CH.d _ n x.1) - (resU F inf_leR).pullC (n + 1) (CH.d _ n x.2)
    rw [map_sub, (resU F inf_leL).d_pullC, (resU F inf_leR).d_pullC]

variable {U V}

theorem mvF_inj (hU : Cosieve U) (hV : Cosieve V) (n : ℕ) : Function.Injective ((mvF F U V).f n) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  funext t
  rcases (t.obj 0).property with h | h
  · exact congrFun (congrArg Prod.fst hx) (liftW hU t h)
  · exact congrFun (congrArg Prod.snd hx) (liftW hV t h)

open Classical in
theorem mvFG_exact (hU : Cosieve U) (hV : Cosieve V) (n : ℕ) : Function.Exact ((mvF F U V).f n) ((mvG F U V).f n) := by
  intro y
  constructor
  · intro hy
    obtain ⟨a, b⟩ := y
    have hab : ∀ s : ComposableArrows (infP U V).FullSubcategory n,
        (resU F inf_leL).pullC n a s = (resU F inf_leR).pullC n b s := fun s =>
      sub_eq_zero.1 (congrFun hy s)
    refine ⟨fun t => if h : U (t.obj 0).obj then a (liftW hU t h) else
      b (liftW hV t ((t.obj 0).property.resolve_left h)), Prod.ext ?_ ?_⟩
    · funext s
      exact dif_pos (s.obj 0).property
    · funext s
      by_cases h : U (s.obj 0).obj
      · refine (dif_pos h).trans ?_
        exact hab (liftW (P := infP U V) (fun _ _ f h => ⟨hU f h.1, hV f h.2⟩) s ⟨h, (s.obj 0).property⟩)
      · exact dif_neg h
  · rintro ⟨x, rfl⟩
    refine sub_eq_zero.2 ?_
    rfl


open Classical in
def extV (hU : Cosieve U) (hV : Cosieve V) {n : ℕ} (y : CH.Cn ((infP U V).ι ⋙ F) n) : CH.Cn (U.ι ⋙ F) n :=
  fun t => if h : V (t.obj 0).obj then
    y (liftW (P := infP U V) (fun _ _ f h => ⟨hU f h.1, hV f h.2⟩) t ⟨(t.obj 0).property, h⟩) else 0

theorem mvG_surj (hU : Cosieve U) (hV : Cosieve V) (n : ℕ) : Function.Surjective ((mvG F U V).f n) := by
  intro y
  refine ⟨(extV F hU hV y, 0), funext fun s => ?_⟩
  have e1 : (resU F inf_leL).pullC n (extV F hU hV y) s = y s := dif_pos (s.obj 0).property.2
  have e2 : (resU F inf_leR).pullC n (0 : CH.Cn (V.ι ⋙ F) n) s = 0 := congrFun (map_zero _) s
  change (resU F inf_leL).pullC n (extV F hU hV y) s - (resU F inf_leR).pullC n (0 : CH.Cn (V.ι ⋙ F) n) s = y s
  rw [e1, e2, sub_zero]

end Cochains

section Family

universe w' v' u'

variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {C : Type u} [Category.{v} C]
  {C' : Type u'} [Category.{v'} C'] (G : C' ⥤ C) {ι : Type} {N : ι → Type} [∀ i, AddCommGroup (N i)]
  [∀ i, Module R (N i)] (F : ι → (C ⥤ ModuleCat.{w} R)) (F' : C' ⥤ ModuleCat.{w'} R')
  (τ : ∀ i, N i → ∀ T : C', (F i).obj (G.obj T) →ₛₗ[σ] F'.obj T)
  (hτ : ∀ i n {T T' : C'} (φ : T ⟶ T') x, τ i n T' (((F i).map (G.map φ)).hom x) = (F'.map φ).hom (τ i n T x))

def Phi {W : ObjectProperty C} {W' : ObjectProperty C'} (h : ∀ T, W' T → W (G.obj T)) (i : ι) (n : N i) :
    Cx.Hom (cw (F i) W) (cw F' W') σ :=
  (morU (⟨G, τ i n, hτ i n⟩ : CH.Mor (F i) F' σ) h).hom

variable {G F F' τ hτ}

theorem phi_lin (hadd : ∀ i n n' T x, τ i (n + n') T x = τ i n T x + τ i n' T x)
    (hsm : ∀ i (r : R) n T x, τ i (r • n) T x = σ r • τ i n T x) {W : ObjectProperty C} {W' : ObjectProperty C'}
    (h : ∀ T, W' T → W (G.obj T)) : Lin (Phi G F F' τ hτ h) :=
  ⟨fun i n n' k x => funext fun s => hadd i n n' _ _, fun i r n k x => funext fun s => hsm i r n _ _⟩

theorem lin_prod {K L : ι → Cx.{w} R} {K' L' : Cx.{w'} R'} {φ : ∀ i, N i → Cx.Hom (K i) K' σ}
    {ψ : ∀ i, N i → Cx.Hom (L i) L' σ} (hφ : Lin φ) (hψ : Lin ψ) : Lin fun i n => prodHom (φ i n) (ψ i n) :=
  ⟨fun i n n' k x => Prod.ext (hφ.1 i n n' k x.1) (hψ.1 i n n' k x.2),
    fun i r n k x => Prod.ext (hφ.2 i r n k x.1) (hψ.2 i r n k x.2)⟩

theorem bc_sup [Fintype ι] [DecidableEq ι] [∀ i, Module.Flat R (N i)]
    (hadd : ∀ i n n' T x, τ i (n + n') T x = τ i n T x + τ i n' T x)
    (hsm : ∀ i (r : R) n T x, τ i (r • n) T x = σ r • τ i n T x) {U V : ObjectProperty C} {U' V' : ObjectProperty C'}
    (hU : Cosieve U) (hV : Cosieve V) (hU' : Cosieve U') (hV' : Cosieve V')
    (hu : ∀ T, U' T → U (G.obj T)) (hv : ∀ T, V' T → V (G.obj T))
    (tU : BC (Phi G F F' τ hτ hu)) (tV : BC (Phi G F F' τ hτ hv))
    (tI : BC (Phi G F F' τ hτ (W := infP U V) (W' := infP U' V') fun T h => ⟨hu T h.1, hv T h.2⟩)) :
    BC (Phi G F F' τ hτ (W := supP U V) (W' := supP U' V') fun T h => h.imp (hu T) (hv T)) := by
  refine (bc_ses (fun i => mvF (F i) U V) (fun i => mvG (F i) U V) (mvF F' U' V') (mvG F' U' V')
    (fun i n => mvF_inj _ hU hV n) (fun i n => mvFG_exact _ hU hV n) (fun i n => mvG_surj _ hU hV n)
    (fun n => mvF_inj _ hU' hV' n) (fun n => mvFG_exact _ hU' hV' n) (fun n => mvG_surj _ hU' hV' n)
    _ (fun i n => prodHom (Phi G F F' τ hτ hu i n) (Phi G F F' τ hτ hv i n)) _
    (phi_lin hadd hsm _) (lin_prod (phi_lin hadd hsm _) (phi_lin hadd hsm _)) (phi_lin hadd hsm _)
    ?_ ?_).1 (bc_prod _ _ (phi_lin hadd hsm _) (phi_lin hadd hsm _) tU tV) tI
  · exact fun i m k x => rfl
  · intro i m k x
    funext s
    exact map_sub (τ i m _) _ _

end Family

end GlobalTheory.CompanionTheory.CosieveBC
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EtSpecProof

section Sections

variable {R : Type} [CommRing R]

theorem res_comp {G : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (x : Sec G U) :
    Sec.res (k ≫ g) x = Sec.res k (Sec.res g x) := by
  simp [Sec.res]

theorem map_res {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) := by
  have h := φ.hom.naturality g.op
  exact congrArg (fun m => m.hom x) h

end Sections

variable {q : ℕ} {C : Type 1} [Category.{0} C] {P : Probe C q} {X : Scheme.{0}}

theorem map_glob (Y : P.Pts X) (i : ℤ) (j : ℕ) (a : Sec ((GlobalTheory.EtC.res _ (tw q i)).X (j : ℤ)) X)
    {c c' : C} (φ : c ⟶ c') :
    (((P.res i).K j).map φ).hom (Sec.res (Y.y c) a) = Sec.res (Y.y c') a := by
  change Sec.res (P.S.map φ).unop (Sec.res (Y.y c) a) = _
  rw [← res_comp, Y.nat]

theorem d_glob (Y : P.Pts X) (i : ℤ) (j : ℕ) (a : Sec ((GlobalTheory.EtC.res _ (tw q i)).X (j : ℤ)) X) :
    d ((P.res i).K j) 0 (Y.glob i j a) = 0 := by
  funext s
  have h : ∀ k : Fin 2, (((P.res i).K j).map (GlobalTheory.CatH.toLast k s)).hom (Y.glob i j a (GlobalTheory.CatH.face k s)) =
      Sec.res (Y.y (s.obj (Fin.last 1))) a := fun k => map_glob Y i j a _
  change ∑ k : Fin 2, (-1 : ℤ) ^ (k : ℕ) •
    (((P.res i).K j).map (GlobalTheory.CatH.toLast k s)).hom (Y.glob i j a (GlobalTheory.CatH.face k s)) = 0
  rw [Fin.sum_univ_two, h 0, h 1]
  simp

theorem dvC_glob (Y : P.Pts X) (i : ℤ) (j : ℕ) (a : Sec ((GlobalTheory.EtC.res _ (tw q i)).X (j : ℤ)) X) :
    (P.res i).dvC j 0 (Y.glob i j a) =
      Y.glob i (j + 1) (Sec.map ((GlobalTheory.EtC.res _ (tw q i)).d (j : ℤ) ((j + 1 : ℕ) : ℤ)) a) := by
  funext s
  exact map_res _ _ _

theorem glob_add (Y : P.Pts X) (i : ℤ) (j : ℕ) (a b : Sec ((GlobalTheory.EtC.res _ (tw q i)).X (j : ℤ)) X) :
    Y.glob i j (a + b) = Y.glob i j a + Y.glob i j b := by
  funext s
  exact map_add _ _ _

theorem glob_sub (Y : P.Pts X) (i : ℤ) (j : ℕ) (a b : Sec ((GlobalTheory.EtC.res _ (tw q i)).X (j : ℤ)) X) :
    Y.glob i j (a - b) = Y.glob i j a - Y.glob i j b := by
  funext s
  exact map_sub _ _ _

theorem edge_exists {i : ℤ} {j : ℕ} (hT : (P.res i).Good) (hSE : StEx) (hRB : RepBasic) (Y : P.Pts X)
    {x : Ht q (sch.obj X) j i} {a : Sec ((GlobalTheory.EtC.res _ (tw q i)).X (j : ℤ)) X} (hx : Rep x a) :
    ∃ h, (P.res i).Edge (Y.glob i j a) h := by
  have hcl := (hRB (ZMod q) (GlobalTheory.EtC.res _ (tw q i)) X (j : ℤ)).2.1 x a hx ((j + 1 : ℕ) : ℤ)
  have hdv : (P.res i).dvC j 0 (Y.glob i j a) = 0 := by
    rw [dvC_glob, hcl]
    funext s
    exact map_zero _
  obtain ⟨z, hz, hst⟩ := hSE ℤ C P.L (P.res i) hT j 0 j (add_zero j) (Y.glob i j a) hdv (d_glob Y i j a)
  exact ⟨(cx P.L).cls z hz, z, hz, hst, rfl⟩

theorem edge_unique {i : ℤ} {j : ℕ} (hT : (P.res i).Good) (hEU : EdgeUniq) (hRB : RepBasic) (hRZ : ResZero)
    (Y : P.Pts X) {x : Ht q (sch.obj X) j i} {a a' : Sec ((GlobalTheory.EtC.res _ (tw q i)).X (j : ℤ)) X}
    (hx : Rep x a) (hx' : Rep x a') {h h' : H P.L j} (he : (P.res i).Edge (Y.glob i j a) h)
    (he' : (P.res i).Edge (Y.glob i j a') h') : h = h' := by
  have hB := hRB (ZMod q) (GlobalTheory.EtC.res _ (tw q i)) X (j : ℤ)
  have h0 : Rep (0 : Ht q (sch.obj X) j i) (a - a') := by
    have := (hB.2.2.1 x x a a' hx hx').2
    rwa [sub_self] at this
  have hz := hB.2.2.2.1 (a - a') h0
  have hVB : (P.res i).VB j (Y.glob i j a - Y.glob i j a') := by
    cases j with
    | zero =>
      obtain ⟨b, hb⟩ := hz (-1) (by norm_num)
      have := (hRZ (ZMod q) (tw q i) X).2.2 (-1) (by norm_num)
      have hb0 : b = 0 := Subsingleton.elim _ _
      have hz0 : a - a' = 0 := by
        rw [← hb, hb0]
        exact map_zero _
      change Y.glob i 0 a - Y.glob i 0 a' = 0
      rw [← glob_sub, hz0]
      funext s
      exact map_zero _
    | succ s =>
      obtain ⟨b, hb⟩ := hz (s : ℤ) (by push_cast; rfl)
      refine ⟨Y.glob i s b, d_glob Y i s b, ?_⟩
      rw [dvC_glob, hb, glob_sub]
  exact (hEU ℤ C P.L (P.res i) hT j _ _ h h' he he').2 hVB

theorem etSpec : ResGood → StEx → EdgeUniq → RepBasic → ResZero → EtSpec := by
  intro hRG hSE hEU hRB hRZ hGen q _ C _ P X Y i j x
  have hT := hRG hGen q C P i
  have hB := hRB (ZMod q) (GlobalTheory.EtC.res _ (tw q i)) X (j : ℤ)
  have hex : ∀ x, ∃ h, Y.IsEt i j x h := fun x => by
    obtain ⟨a, ha⟩ := hB.1 x
    obtain ⟨h, hh⟩ := edge_exists hT hSE hRB Y ha
    exact ⟨h, a, ha, hh⟩
  have huniq : ∀ {x h h'}, Y.IsEt i j x h → Y.IsEt i j x h' → h = h' := by
    rintro x h h' ⟨a, ha, he⟩ ⟨a', ha', he'⟩
    exact edge_unique hT hEU hRB hRZ Y ha ha' he he'
  have hall : ∀ x, Y.IsEt i j x (Y.et i j x) := by
    refine pick_spec (P := fun e : Ht q (sch.obj X) j i →+ H P.L j => ∀ x, Y.IsEt i j x (e x)) ?_
    choose f hf using hex
    refine ⟨AddMonoidHom.mk' f fun u v => huniq (hf _) ?_, hf⟩
    obtain ⟨a, ha, he⟩ := hf u
    obtain ⟨b, hb, he'⟩ := hf v
    refine ⟨a + b, (hB.2.2.1 u v a b ha hb).1, ?_⟩
    rw [glob_add]
    exact (hEU ℤ C P.L (P.res i) hT j _ _ _ _ he he').1
  refine ⟨fun a ha => ?_, fun h hh => huniq hh (hall x)⟩
  obtain ⟨h, hh⟩ := edge_exists hT hSE hRB Y ha
  have e : h = Y.et i j x := huniq ⟨a, ha, hh⟩ (hall x)
  rwa [← e]

end GlobalTheory.CompanionTheory.EtSpecProof
end

section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeMap

theorem redRoot_of_rep : CrystallineSemistableComparison.E.RepRoot → CrystallineSemistableComparison.E.RepOp → CrystallineSemistableComparison.E.RepConc → CrystallineSemistableComparison.E.RedRoot := by
  intro hRoot hOp hConc inOp inRed Q q _ _ hq i X ζ ξ hξ
  have h1 : Rep (rootClass i ζ) (resGen i ζ) := (hRoot Q i X ζ).2
  have h2 : Rep (rootClass i ξ) (resGen i ξ) := (hRoot q i X ξ).2
  have h3 := hOp inOp _ _ _ _ (redMap Q q i) X 0 (rootClass i ζ) _ h1
  rw [inRed Q q hq i X ζ ξ hξ] at h3
  exact (hConc (ZMod q) _ X 0 (resGen i ξ)).2.2 _ _ h3 h2

end GlobalTheory.CompanionTheory.EdgeMap
end

module

public import Development.EtaleCohomology.EtaleTrace.Bundle003
public import Development.EtaleCohomology.TateTwists.Bundle004
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
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

section

namespace LateralTheory.EtaleTrace.Cov

open KaehlerDifferential in
theorem JetUnram_of : JetUnram := by
  intro k K O _ _ _ _ φ n w i hwi hspan hk hw
  let _ : Algebra O K := φ.toAlgebra
  show Algebra.FormallyUnramified O K
  constructor
  have hD0 : ∀ z ∈ φ.range, D O K z = 0 := by
    rintro _ ⟨o, rfl⟩
    exact (D O K).map_algebraMap o
  let D' : Derivation k K Ω[K⁄O] := Derivation.mk'
    { toFun := fun x => D O K x
      map_add' := fun x y => (D O K).map_add x y
      map_smul' := fun c x => by
        simp only [RingHom.id_apply]
        rw [Algebra.smul_def, (D O K).leibniz, hD0 _ (hk c), smul_zero, add_zero, algebraMap_smul] }
    (fun a b => (D O K).leibniz a b)
  have hD' : ∀ x, D'.liftKaehlerDifferential (D k K x) = D O K x := fun x =>
    D'.liftKaehlerDifferential_comp_D x
  let G : (K × Ω[K⁄k]) →ₗ[K] Ω[K⁄O] :=
    D'.liftKaehlerDifferential.comp (LinearMap.snd K K Ω[K⁄k]) -
      (LinearMap.fst K K Ω[K⁄k]).smulRight ((w i)⁻¹ • D O K (w i))
  have hG : ∀ j, G (jet k w j) = 0 := by
    intro j
    obtain ⟨u, hu⟩ := hw j
    have hwj : w j = φ u * w i := by rw [hu]; field_simp
    show D'.liftKaehlerDifferential (D k K (w j)) - w j • ((w i)⁻¹ • D O K (w i)) = 0
    rw [hD', hwj, (D O K).leibniz, hD0 _ ⟨u, rfl⟩, smul_zero, add_zero, smul_smul, mul_assoc,
      mul_inv_cancel₀ hwi, mul_one, sub_self]
  have hG0 : G = 0 := LinearMap.ext_on_range hspan (fun j => by rw [hG j]; rfl)
  have hDz : ∀ x : K, D O K x = 0 := by
    intro x
    have h := LinearMap.congr_fun hG0 (0, D k K x)
    have h2 : G (0, D k K x) = D O K x := by
      show D'.liftKaehlerDifferential (D k K x) - (0 : K) • ((w i)⁻¹ • D O K (w i)) = D O K x
      rw [hD', zero_smul, sub_zero]
    rw [← h2, h]; rfl
  suffices (⊤ : Submodule K Ω[K⁄O]) ≤ ⊥ from
    (subsingleton_iff_forall_eq 0).mpr fun y => this trivial
  rw [← span_range_derivation, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  exact hDz x

end LateralTheory.EtaleTrace.Cov
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CochainComplex.HomComplex Opposite

namespace LateralTheory.EtaleTrace

theorem free_ext (R : Type) [CommRing R] (P : PSh) {G : Shv R} (f g : (free R).obj P ⟶ G)
    (h : ∀ (U : Scheme.{0}) (x : P.obj (op U)),
      (f.hom.app (op U)).hom (freeGen R P U x) = (g.hom.app (op U)).hom (freeGen R P U x)) : f = g := by
  apply Sheaf.hom_ext
  refine sheafify_hom_ext (J := Scheme.etaleTopology) (P := (freeP R).obj P) f.hom g.hom G.property ?_
  ext U : 2
  apply ModuleCat.free_hom_ext
  rintro ⟨x⟩
  have := h U.unop x
  simp only [freeGen] at this
  simp only [freeP, ModuleCat.freeMk] at this
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply]
  exact this

theorem cocEq : CocEq := by
  intro R _ F X α β h
  apply Cocycle.ext
  apply Cochain.ext₀
  intro q
  rcases lt_trichotomy q 0 with hq | rfl | hq
  · have : (res R F).IsStrictlyGE 0 := by unfold res; infer_instance
    exact (CochainComplex.isZero_of_isStrictlyGE (res R F) 0 q hq).eq_of_tgt _ _
  · have key : (chainsXIso R (sch.obj X) 0).inv ≫ α.1.v _ _ (show -((0:ℕ):ℤ) + 0 = 0 by simp) =
        (chainsXIso R (sch.obj X) 0).inv ≫ β.1.v _ _ (show -((0:ℕ):ℤ) + 0 = 0 by simp) := by
      apply free_ext
      intro U x
      exact h U x
    have := congrArg (fun φ => (chainsXIso R (sch.obj X) 0).hom ≫ φ) key
    simpa using this
  · apply IsZero.eq_of_src
    apply HomologicalComplex.isZero_extend_X
    intro i hi
    change -(i:ℤ) = q at hi
    omega

theorem CocEq_of : CocEq := cocEq

end LateralTheory.EtaleTrace
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.EtaleTrace.Cov

def GenEtale : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X P : Scheme.{0}} [IsIntegral X] [IsIntegral P] (p : X ⟶ S k)
  (r : P ⟶ S k) (π : X ⟶ P), π ≫ r = p → LocallyOfFiniteType r → IsFinite π → Surjective π →
  (π.stalkMap (genericPoint X)).hom.FormallyUnramified → ∃ V : P.Opens, (V : Set P).Nonempty ∧ Etale (π ∣_ V)

def RatPtIn : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {P : Scheme.{0}} (r : P ⟶ S k), LocallyOfFiniteType r →
  ∀ V : P.Opens, (V : Set P).Nonempty → ∃ t : Pt r, ∀ x, t.1.base x ∈ V

def FibreOfEtale : Prop := ∀ (k : Type) [Field k] {X P : Scheme.{0}} (p : X ⟶ S k) (r : P ⟶ S k) (π : X ⟶ P), π ≫ r = p →
  ∀ V : P.Opens, Etale (π ∣_ V) → ∀ t : Pt r, (∀ x, t.1.base x ∈ V) → Etale (equalizer.ι π (p ≫ t.1) ≫ p)

theorem Fibre_of (h1 : GenEtale) (h2 : RatPtIn) (h3 : FibreOfEtale) : Fibre := by
  intro k _ _ X P _ _ p r π hπ hr hfin hsurj hun
  obtain ⟨V, hV, hE⟩ := h1 k p r π hπ hr hfin hsurj hun
  obtain ⟨t, ht⟩ := h2 k r hr V hV
  exact ⟨t, h3 k p r π hπ V hE t ht⟩

end LateralTheory.EtaleTrace.Cov
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

def FSAffine : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k),
  ∀ (N d : ℕ) (ι : X ⟶ PN k N) (π : X ⟶ PN k d) (v : Fin (N + 1) → X.functionField) (w : Fin (d + 1) → X.functionField),
  IsClosedImmersion ι → Coord p ι v → Coord p π w →
  (∀ i, ∃ c : Fin (N + 1) → k, w i = ∑ j, kHom p (c j) * v j) →
  (∀ x : X, ∃ i, w i ≠ 0 ∧ ∀ j, v j / w i ∈ loc X x) →
  IsAffineHom π

def FSDense : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k),
  ∀ (d : ℕ) (π : X ⟶ PN k d) (w : Fin (d + 1) → X.functionField), Coord p π w →
  (∀ (m : ℕ) (F : MvPolynomial (Fin (d + 1)) k), F.IsHomogeneous m → eval₂ (kHom p) w F = 0 → F = 0) →
  IsDominant π

theorem FinSurj_of (h1 : PNBasic) (hA : FSAffine) (hD : FSDense) : FinSurj := by
  intro k _ X _ p hp N d ι π v w hι hπ cv cw hlin hx hind
  have hsep : IsSeparated (PNto k d) := (h1 k d).2.1
  have : IsProper (π ≫ PNto k d) := by rw [hπ]; exact hp
  have : IsProper π := IsProper.of_comp π (PNto k d)
  have : IsAffineHom π := hA k p N d ι π v w hι cv cw hlin hx
  have : IsDominant π := hD k p d π w cw hind
  refine ⟨IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩, ?_⟩
  exact surjective_of_isDominant_of_isClosed_range π (π.isClosedMap.isClosed_range)
end Cov
end EtaleTrace
end LateralTheory
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

def GenOn {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) {N : ℕ}
    (w : Fin (N + 1) → X.functionField) (U : X.Opens) (πU : U.toScheme ⟶ PN k N) : Prop :=
  ∀ (hη : genericPoint X ∈ U) (n : ℕ), 0 < n → ∀ (f : MvPolynomial (Fin (N + 1)) k)
    (hf : f ∈ homogeneousSubmodule (Fin (N + 1)) k n),
    ((⟨genericPoint X, hη⟩ : U) ∈ πU ⁻¹ᵁ Proj.basicOpen _ f ↔ eval₂ (kHom p) w f ≠ 0) ∧
    ∀ (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k) (hg : g ∈ homogeneousSubmodule (Fin (N + 1)) k (m • n))
      (h : (⟨genericPoint X, hη⟩ : U) ∈ πU ⁻¹ᵁ Proj.basicOpen _ f),
      U.toScheme.presheaf.germ _ ⟨genericPoint X, hη⟩ h (πU.app _
          (Proj.awayToSection _ f (HomogeneousLocalization.Away.mk _ hf m g hg))) *
        (U.ι.stalkMap ⟨genericPoint X, hη⟩).hom (show X.presheaf.stalk (U.ι ⟨genericPoint X, hη⟩) from
          eval₂ (kHom p) w f) ^ m =
        (U.ι.stalkMap ⟨genericPoint X, hη⟩).hom (show X.presheaf.stalk (U.ι ⟨genericPoint X, hη⟩) from eval₂ (kHom p) w g)

def GenOutChart : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ)
  (w : Fin (N + 1) → X.functionField), (∀ x : X, ∃ i, w i ≠ 0 ∧ ∀ j, w j / w i ∈ loc X x) →
  ∀ x : X, ∃ (U : X.Opens) (πU : U.toScheme ⟶ PN k N), x ∈ U ∧ πU ≫ PNto k N = U.ι ≫ p ∧ GenOn p w U πU

def GenOutGlue : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ)
  (w : Fin (N + 1) → X.functionField),
  (∀ x : X, ∃ (U : X.Opens) (πU : U.toScheme ⟶ PN k N), x ∈ U ∧ πU ≫ PNto k N = U.ι ≫ p ∧ GenOn p w U πU) →
  ∃ π : X ⟶ PN k N, π ≫ PNto k N = p ∧ Gen p π w

theorem GenOut_of (h1 : GenOutChart) (h2 : GenOutGlue) : GenOut := by
  intro k _ X _ p N w hw
  exact h2 k p N w (h1 k p N w hw)

end LateralTheory.EtaleTrace.Cov
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.EtaleTrace.LEmptyPf

theorem sec_subsingleton {R : Type} [CommRing R] (X : Scheme.{0}) [IsEmpty X] (F : Shv R) :
    Subsingleton (Sec F X) := by
  have ht : IsTerminal (F.obj.obj (Opposite.op X)) :=
    Sheaf.isTerminalOfBotCover F X (by exact Scheme.bot_mem_grothendieckTopology X)
  have hz : IsZero (F.obj.obj (Opposite.op X)) := ht.isZero
  exact ModuleCat.subsingleton_of_isZero hz

theorem pos_zero (a5 : A5) {R : Type} [CommRing R] (X : Scheme.{0}) [IsEmpty X] (F : Shv R) (n : ℤ)
    (hn : 0 < n) (x : H R (sch.obj X) F n) : x = 0 := by
  obtain ⟨Y, f, -, -, hx⟩ := a5 R X F n hn x
  have : IsEmpty Y := Function.isEmpty f.base
  have : IsIso f := isIso_of_isEmpty f
  have h1 : x = pull R (sch.map (inv f)) F n (pull R (sch.map f) F n x) := by
    rw [← pull_comp, ← Functor.map_comp, IsIso.inv_hom_id, CategoryTheory.Functor.map_id, pull_id]
  rw [h1, hx, map_zero]

theorem LEmpty_of : LateralTheory.EtaleTrace.LPdCut.LEmpty := by
  intro a5 a9 R _ X hX F n
  refine ⟨fun a b => ?_⟩
  rcases lt_trichotomy n 0 with h | rfl | h
  · exact ((a9 R F).1 _ n h).elim a b
  · obtain ⟨e, -⟩ := (a9 R F).2
    have := sec_subsingleton X F
    exact (e X).symm.injective (Subsingleton.elim _ _)
  · rw [pos_zero a5 X F n h a, pos_zero a5 X F n h b]

end LateralTheory.EtaleTrace.LEmptyPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CochainComplex.HomComplex Opposite

namespace LateralTheory.EtaleTrace

theorem freeGen_nat (R : Type) [CommRing R] (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    Sec.res g (freeGen R P U x) = freeGen R P V (P.map g.op x) := by
  have h := congrArg (fun f => f.hom (ModuleCat.freeMk (ULift.up x : uliftFunctor.{1, 0}.obj (P.obj (op U)))))
    ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h
  simp only [Sec.res, freeGen]
  refine h.symm.trans ?_
  exact congrArg (ModuleCat.Hom.hom ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op V)))
    (by simp only [freeP, ModuleCat.freeMk, ModuleCat.free, Functor.comp_obj, Functor.whiskeringRight_obj_obj, Functor.comp_map]
        exact Finsupp.mapDomain_single)

theorem evNat : EvNat := by
  intro R _ F X U α x
  have h := freeGen_nat R ((sch.obj X).obj (op (SimplexCategory.mk 0))) x (𝟙 X : Sx (sch.obj X) 0 X)
  have hx : ((sch.obj X).obj (op (SimplexCategory.mk 0))).map x.op (𝟙 X : Sx (sch.obj X) 0 X) = (x : Sx (sch.obj X) 0 U) :=
    Category.comp_id x
  rw [hx] at h
  simp only [ev]
  rw [← h]
  simp only [Sec.res]
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← NatTrans.naturality]

end LateralTheory.EtaleTrace
end
end

section

noncomputable section
open MvPolynomial

namespace LateralTheory.EtaleTrace.Cov

variable {k K : Type} [Field k] [Field K] [Algebra k K]

theorem jetIndep_chain {n : ℕ} (w : Fin n → K) (F : MvPolynomial (Fin n) k) :
    KaehlerDifferential.D k K (aeval w F) =
      ∑ j, aeval w (pderiv j F) • KaehlerDifferential.D k K (w j) := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => simp [hf, hg, add_smul, Finset.sum_add_distrib]
  | mul_X f i hf =>
    simp only [map_mul, aeval_X, Derivation.leibniz, hf, pderiv_X, Finset.sum_add_distrib, mul_smul, Finset.smul_sum, Derivation.leibniz]
    simp [Pi.single_apply]
    simp only [apply_ite (aeval w), map_zero, add_smul, ite_smul, zero_smul, Finset.sum_add_distrib,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_smul]

theorem jetIndep_pderiv {n : ℕ} (w : Fin n → K) (hw : LinearIndependent K (jet k w)) {m : ℕ}
    (F : MvPolynomial (Fin n) k) (hF : F.IsHomogeneous m) (h0 : aeval w F = 0) (j : Fin n) :
    aeval w (pderiv j F) = 0 := by
  have e1 := congrArg (aeval w) hF.sum_X_mul_pderiv

  simp only [map_sum, map_mul, aeval_X, map_nsmul, h0, smul_zero] at e1
  have e2 := jetIndep_chain w F
  rw [h0, Derivation.map_zero] at e2
  refine Fintype.linearIndependent_iff.1 hw (fun j => aeval w (pderiv j F)) ?_ j
  ext
  · simp only [jet, Prod.fst_sum, Prod.smul_fst, smul_eq_mul, Prod.fst_zero]
    rw [← e1]; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  · simp only [jet, Prod.snd_sum, Prod.smul_snd, Prod.snd_zero]
    exact e2.symm

theorem jetIndep_dvd {n p : ℕ} [CharP k p] (F : MvPolynomial (Fin n) k) (h : ∀ j, pderiv j F = 0)
    (α : Fin n →₀ ℕ) (hα : α ∈ F.support) (i : Fin n) : p ∣ α i := by
  rcases Nat.eq_zero_or_pos (α i) with h0 | hpos
  · simp [h0]
  have hc := congrArg (AddMonoidAlgebra.coeff · (α - Finsupp.single i 1)) (h i)
  rw [coeff_pderiv, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hc
  have hα' : α - Finsupp.single i 1 + Finsupp.single i 1 = α := by
    ext l
    by_cases hl : i = l
    · subst hl; simp; omega
    · simp [hl]
  rw [hα'] at hc
  have hne : AddMonoidAlgebra.coeff F α ≠ 0 := mem_support_iff.1 hα
  have h1 : (((α - Finsupp.single i 1 : Fin n →₀ ℕ) i : ℕ) : k) + 1 = 0 := (mul_eq_zero.1 hc).resolve_left hne
  have e : (α - Finsupp.single i 1 : Fin n →₀ ℕ) i + 1 = α i := by simp; omega
  rw [← CharP.cast_eq_zero_iff k p, ← e]
  exact_mod_cast h1

theorem jetIndep_root {n p : ℕ} [Fact p.Prime] [CharP k p] [PerfectRing k p]
    (F : MvPolynomial (Fin n) k) {m : ℕ} (hF : F.IsHomogeneous m) (hd : ∀ α ∈ F.support, ∀ i, p ∣ α i) :
    ∃ G : MvPolynomial (Fin n) k, G.IsHomogeneous (m / p) ∧ F = G ^ p := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  let q : (Fin n →₀ ℕ) → (Fin n →₀ ℕ) := fun α => Finsupp.mapRange (· / p) (Nat.zero_div p) α
  have hq : ∀ α ∈ F.support, p • q α = α := by
    intro α hα; ext i; simp [q, Nat.mul_div_cancel' (hd α hα i)]
  refine ⟨∑ α ∈ F.support, monomial (q α) ((frobeniusEquiv k p).symm (AddMonoidAlgebra.coeff F α)), ?_, ?_⟩
  · apply IsHomogeneous.sum
    intro α hα
    apply isHomogeneous_monomial
    have hm : α.degree = m := by
      have := hF (mem_support_iff.1 hα)
      rw [Finsupp.degree_eq_weight_one]; exact this
    have : p * (q α).degree = m := by
      have h2 := congrArg Finsupp.degree (hq α hα)
      rw [map_nsmul, smul_eq_mul] at h2
      rw [h2, hm]
    rw [← this, Nat.mul_div_cancel_left _ hp]
  · rw [sum_pow_char]
    conv_lhs => rw [F.as_sum]
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [monomial_pow, frobeniusEquiv_symm_pow_p, hq α hα]

theorem JetIndep_of : JetIndep := by
  intro k K _ _ _ _ n w hw m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro F hF h0
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · by_contra hne
    have ht := hF.totalDegree hne
    rw [totalDegree_eq_zero_iff_eq_C] at ht
    rw [ht, aeval_C, map_eq_zero_iff _ (algebraMap k K).injective] at h0
    exact hne (by rw [ht, h0, C_0])
  have hpd : ∀ j, pderiv j F = 0 := fun j =>
    ih (m - 1) (by omega) _ hF.pderiv (jetIndep_pderiv w hw F hF h0 j)
  obtain ⟨p, hcp⟩ := CharP.exists k
  rcases CharP.char_is_prime_or_zero k p with hpp | rfl
  · have := Fact.mk hpp
    have : ExpChar k p := ExpChar.prime hpp
    have : PerfectRing k p := PerfectField.toPerfectRing p
    obtain ⟨G, hG, rfl⟩ := jetIndep_root F hF (fun α hα i => jetIndep_dvd F hpd α hα i)
    rw [map_pow] at h0
    have hG0 := ih (m / p) (Nat.div_lt_self hm hpp.one_lt) G hG (pow_eq_zero_iff hpp.ne_zero |>.1 h0)
    rw [hG0, zero_pow hpp.ne_zero]
  · ext α
    rw [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    by_contra hc
    have hα0 : α = 0 := by
      ext i; simpa using jetIndep_dvd (p := 0) F hpd α (mem_support_iff.2 hc) i
    have := hF hc
    subst hα0
    simp at this
    omega

end LateralTheory.EtaleTrace.Cov
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC Opposite

namespace LateralTheory.EtaleTrace

theorem tz_sec_eq_of_loc {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (y z : Sec F U)
    (h : Loc U fun V g => Sec.res g y = Sec.res g z) : y = z := by
  obtain ⟨S, hS, hP⟩ := h
  exact Sheaf.isSeparated F U S hS y z (fun _ g hg => hP _ g hg)

theorem tz_twGen_eq_of_pow {q : ℕ} {U : Scheme.{0}} (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ)
    (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) : twGen (q := q) 0 ξ = twGen 0 ζ := by
  unfold twGen
  congr 1
  refine (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨ζ, ξ, a, h, ?_⟩)
  simp
  rfl

def PrimLoc : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)),
  Loc U fun V g => ∃ a : (ZMod q)ˣ, (ξ.map g.appTop.hom).1 = (ζ.map g.appTop.hom).1 ^ (a : ZMod q).val

theorem TwZero_of_primLoc (hTw : LateralTheory.EtaleFoundations.CongruenceLocalDecomposition.TwLoc) (hP : PrimLoc) : TwZero := by
  intro q _ U ζ ξ
  obtain ⟨-, -, T3⟩ := hTw q 0
  apply tz_sec_eq_of_loc
  obtain ⟨S, hS, hP'⟩ := hP q U ζ ξ
  refine ⟨S, hS, fun _ g hg => ?_⟩
  obtain ⟨a, ha⟩ := hP' _ g hg
  rw [T3, T3]
  exact (tz_twGen_eq_of_pow _ _ a ha).symm

end LateralTheory.EtaleTrace
end
end

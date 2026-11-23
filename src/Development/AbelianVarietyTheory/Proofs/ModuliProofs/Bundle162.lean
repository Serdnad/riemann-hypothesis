module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle035
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle049
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle055
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle050
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle159
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle118
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle079
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle128
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle153
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle160
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsBasisOfIsField
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle088
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle161
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrincipallyPolarisedModelLocalizationAway
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.hasTh_eq_classicalThetaFunction_values : Out.Laws → Out.Laws2 → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (t : TObj g (N' ^ 2) J b (spMap em)) (u : HolUnif t.A t.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (θ : (Fin g → ℂ) → ℂ) (lam : Fin (2 * g) → u.Λ), Odd N' → u.IsAH Hm χ → u.IsThetaFn Hm χ 1 θ → θ ≠ 0 → (∀ i, (t.pt i).left = (u.ex (((N' : ℂ) ^ 2)⁻¹ • (lam i : Fin g → ℂ))).left) → t.HasTh (𝟙 _) (fun a => χ (∑ i, ((a i).val : ℤ) • lam i) * Complex.exp (-(Real.pi / 2 / (N' : ℂ) ^ 2) * hermForm Hm (∑ i, ((a i).val : ℂ) • (lam i : Fin g → ℂ)) (∑ i, ((a i).val : ℂ) • (lam i : Fin g → ℂ))) * θ ((N' : ℂ)⁻¹ • ∑ i, ((a i).val : ℂ) • (lam i : Fin g → ℂ))) := by
  first | exact @GlobalTheory.ThetaClassical.hasTh_classical | exact GlobalTheory.ThetaClassical.hasTh_classical | (intros; apply GlobalTheory.ThetaClassical.hasTh_classical <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.thetaConstants_satisfy_closure_equations_of_dense_class : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g n N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (R : Type) [CommRing R] (β : o →+* R) (x : Sp R ⟶ S) (v : Ix g (N' ^ 2) → R), 2 ≤ n → n ∣ N' → Odd N' → IsReduced S → Dense (fromSet em C t) → IsOpenImmersion x → x ≫ s = spMap β → t.HasTh x v → InMM n N' (thIdeal em C) β v := by
  first | exact @GlobalTheory.ZM.inMM_of_dense_fromSet | exact GlobalTheory.ZM.inMM_of_dense_fromSet | (intros; apply GlobalTheory.ZM.inMM_of_dense_fromSet <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.PelTan

theorem finrank_derivation_le : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∀ (N' : ℕ) (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (ρ : o) (R : Type) [CommRing R] [Algebra o R] [Algebra o ℂ] [Algebra R ℂ] [IsScalarTower o R ℂ] (t : TObj g (N' ^ 2) J b (spMap (algebraMap o R))) (τ : SAB H (Sp R)), ρ ^ 2 = -(H.d : o) → IsPEL D a bas ρ t τ → Algebra.FiniteType o R → (∀ (x : Sp (DualNumber ℂ) ⟶ Sp R) (t' : TObj g (N' ^ 2) J b (x ≫ spMap (algebraMap o R))), x ≫ spMap (algebraMap o R) = constPt x ≫ spMap (algebraMap o R) → TMap t' t x → TMap t' t (constPt x) → x = constPt x) → Module.finrank ℂ (Derivation o R ℂ) ≤ D.dim := by
  intro l1 l2 _ hu E _ _ _ H D g J _ a w w' bas _ _ _ _ _ N' o _ b ρ R _ _ _ _ _ t τ hρ hP _ hun
  obtain ⟨t₀, m, u, Hm, χ, κ, hG, ⟨hm, -⟩, hκ, hD⟩ := GlobalTheory.T.tangent_injects_symmetric_antilinear_commuting l1 l2 hu o g (N' ^ 2) J b R t hun
  have hx : spMap (algebraMap R ℂ) ≫ spMap (algebraMap o R) = spMap (algebraMap o ℂ) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  obtain ⟨act, act₀, hc, hdet⟩ := GlobalTheory.FibreAct.exists_fibre_act E H D g (N' ^ 2) J a bas o b ρ _ _ t τ _
    (algebraMap o ℂ) t₀.A m hP hx hm
  obtain ⟨F, hF⟩ := (GlobalTheory.KS.exists_linear_lift_action t₀.pol u Hm χ hG).2 (𝓞 E) act₀
  have hle := GlobalTheory.T.finrank_symm_antilinear_comm_CM_le E H t₀.pol.g D.p D.q (algebraMap o ℂ ρ) Hm F (LinearMap.range κ)
    (by rw [← map_pow, hρ]; simp) hG.ah.1 hG.ah.2.1
    (fun σ => by
      split_ifs with h
      · exact GlobalTheory.T.finrank_eigenspace_of_lieMultiplicity t₀.pol u Hm χ hG (𝓞 E) act₀ F hF σ _ ((hdet σ).1 h)
      · exact GlobalTheory.T.finrank_eigenspace_of_lieMultiplicity t₀.pol u Hm χ hG (𝓞 E) act₀ F hF σ _ ((hdet σ).2 h))
    (by
      rintro _ ⟨d, rfl⟩
      exact ⟨(hD d).1, fun c => (hD d).2 (act.act c) (act₀.act c) (F c) (hc c) (hF c)⟩)
  rw [LinearMap.finrank_range_of_inj hκ] at hle
  exact hle

end GlobalTheory.PelTan
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.SharpAdjoint

section Bundles

variable {X X' Y Y' : Scheme.{0}}

theorem iso_linComb_pull {L : LB X} {L' : LB X'} {F : X' ⟶ X} (H : LBIso L' (L.pull F)) {K : Type} [Fintype K]
    (ψ' : K → (Y' ⟶ X')) (ψ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y) (e : ∀ k, ψ' k ≫ F = h ≫ ψ k) :
    LBIso (LB.LinComb L' ψ' ε) ((LB.LinComb L ψ ε).pull h) := by
  obtain ⟨w, hw⟩ := H
  exact LBIso.chartPull (chartPullId _) (chartPullOut L ψ ε h _ e) (iso_linComb ((isGen_iff w).1 hw) ψ' ε)

theorem iso_up {M N : LB Y} {M' N' : LB Y'} {h : Y' ⟶ Y} (hM : M.IsLB) (hN : N.IsLB) (hM' : M'.IsLB) (hN' : N'.IsLB)
    (a : LBIso M' (M.pull h)) (b : LBIso N' (N.pull h)) (H : LBIso M N) : LBIso M' N' :=
  LBIso.trans hM' (pull_isLB hM h) hN' a (LBIso.trans (pull_isLB hM h) (pull_isLB hN h) hN'
    (H.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull M h h rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull N h h rfl)) b.symm)

end Bundles

section Field

variable {K : Type} [Field K] {S' : Scheme.{0}} (f : S' ⟶ Sp K)

theorem exists_point [Nonempty S'] :
    ∃ (K' : Type) (_ : Field K') (i : K →+* K') (x : Sp K' ⟶ S'), x ≫ f = spMap i := by
  obtain ⟨y⟩ := ‹Nonempty S'›
  obtain ⟨i, hi⟩ := Spec.map_surjective (S'.fromSpecResidueField y ≫ f)
  exact ⟨S'.residueField y, inferInstance, i.hom, S'.fromSpecResidueField y, hi.symm⟩

variable {f}

theorem iso_down [Nonempty S'] {X₀ X : Scheme.{0}} {p₀ : X₀ ⟶ Sp K} {p : X ⟶ S'} {h : X ⟶ X₀}
    (H : IsPullback h p p₀ f) (h₁ : Smooth p₀) (h₂ : IsProper p₀) (h₃ : GeometricallyConnected p₀)
    {M N : LB X₀} {M' N' : LB X} (hM : M.IsLB) (hN : N.IsLB) (hM' : M'.IsLB) (hN' : N'.IsLB)
    (a : LBIso M' (M.pull h)) (b : LBIso N' (N.pull h)) (c : LBIso M' N') : LBIso M N := by
  obtain ⟨K', _, i, x, hx⟩ := exists_point f
  have P : IsPullback (pullback.fst p x ≫ h) (pullback.snd p x) p₀ (spMap i) :=
    hx ▸ (IsPullback.of_hasPullback p x).paste_horiz H
  have d : LBIso (M.pull h) (N.pull h) := LBIso.trans (pull_isLB hM h) hM' (pull_isLB hN h) a.symm
    (LBIso.trans hM' hN' (pull_isLB hN h) c b)
  exact (GlobalTheory.lb_gen_iso_descend_field K K' i X₀ _ p₀ _ _ h₁ h₂ h₃ P).2 M N hM hN (d.chartPull
    (chartPullSame M _ _ _ (pullback.fst p x) fun _ => rfl) (chartPullSame N _ _ _ (pullback.fst p x) fun _ => rfl))

end Field

section Group

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
  (h : IsGrpPullback G' G f φ)

section Points

variable {T : Over S} {T' : Over S'} (U : Over.mk (T'.hom ≫ f) ⟶ T)

theorem push_comp {x' : T' ⟶ G'} {x : T ⟶ G} (hx : pushPt h.1.w x' = U ≫ x) {a' : G' ⟶ G'} {a : G ⟶ G}
    (ha : a'.left ≫ φ = φ ≫ a.left) : pushPt h.1.w (x' ≫ a') = U ≫ x ≫ a := by
  rw [← Category.assoc, ← hx]
  refine Over.OverMorphism.ext ?_
  show (x'.left ≫ _) ≫ _ = (x'.left ≫ _) ≫ _
  rw [Category.assoc, ha, Category.assoc]

theorem iso_cubeLB_pull [IsCommMonObj G] [IsCommMonObj G'] {L : LB G.left} {L' : LB G'.left}
    (H : LBIso L' (L.pull φ)) {a' b' : T' ⟶ G'} {a b : T ⟶ G} (ha : pushPt h.1.w a' = U ≫ a)
    (hb : pushPt h.1.w b' = U ≫ b) : LBIso (cubeLB G' ![a', b'] L') ((cubeLB G ![a, b] L).pull U.left) :=
  iso_linComb_pull H _ _ _ U.left fun I => psum_push h _ _ U (fun i => by
    fin_cases i
    exacts [ha, hb]) I.down

end Points

def sqMap : Over.mk ((G' ⊗ G').hom ≫ f) ⟶ G ⊗ G := lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))

theorem push_fst : pushPt h.1.w (fst G' G') = sqMap h ≫ fst G G := (lift_fst _ _).symm

theorem push_snd : pushPt h.1.w (snd G' G') = sqMap h ≫ snd G G := (lift_snd _ _).symm

theorem isPullback_sqMap : IsPullback (sqMap h).left (G' ⊗ G').hom (G ⊗ G).hom f := by
  have e₁ : (sqMap h).left ≫ (fst G G).left = (fst G' G').left ≫ φ := congrArg (fun q => q.left) (push_fst h).symm
  have e₂ : (sqMap h).left ≫ (snd G G).left = (snd G' G').left ≫ φ := congrArg (fun q => q.left) (push_snd h).symm
  have A : IsPullback (snd G G).left (fst G G).left G.hom G.hom := (IsPullback.of_hasPullback G.hom G.hom).flip
  have A' : IsPullback (snd G' G').left (fst G' G').left G'.hom G'.hom := (IsPullback.of_hasPullback G'.hom G'.hom).flip
  have B := A'.paste_horiz h.1
  rw [← e₂, ← h.1.w] at B
  have C := (IsPullback.of_right B e₁ A).paste_vert h.1
  rwa [Over.w, Over.w] at C

def selfMap : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk φ h.1.w

theorem push_id : pushPt h.1.w (𝟙 G') = selfMap h ≫ 𝟙 G :=
  Over.OverMorphism.ext ((Category.id_comp _).trans (Category.comp_id _).symm)

theorem push_end {a' : G' ⟶ G'} {a : G ⟶ G} (ha : a'.left ≫ φ = φ ≫ a.left) : pushPt h.1.w a' = selfMap h ≫ a :=
  Over.OverMorphism.ext ha

end Group

variable {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k}

theorem isLB_linComb {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] (ψ : K → (Y ⟶ X))
    (ε : K → ℤ) : (LB.LinComb L ψ ε).IsLB := DVR.linComb_isLB _ hL _ _

theorem transfer {K : Type} [Field K] {S₁ S₂ : Scheme.{0}} [Nonempty S₁] {s₀ : Sp K ⟶ Sp o} {s₁ : S₁ ⟶ Sp o}
    {s₂ : S₂ ⟶ Sp o} {f₁ : S₁ ⟶ Sp K} {f₂ : S₂ ⟶ Sp K} {t₀ : TObj g k J b s₀} {t₁ : TObj g k J b s₁}
    {t₂ : TObj g k J b s₂} (H₁ : TMap t₁ t₀ f₁) (H₂ : TMap t₂ t₀ f₂) (w w' : J) :
    (LBIso (cubeLB t₁.A ![fst t₁.A t₁.A ≫ t₁.act w, snd t₁.A t₁.A] t₁.L)
        (cubeLB t₁.A ![fst t₁.A t₁.A, snd t₁.A t₁.A ≫ t₁.act w'] t₁.L) →
      LBIso (cubeLB t₂.A ![fst t₂.A t₂.A ≫ t₂.act w, snd t₂.A t₂.A] t₂.L)
        (cubeLB t₂.A ![fst t₂.A t₂.A, snd t₂.A t₂.A ≫ t₂.act w'] t₂.L)) ∧
    (LBIso t₁.L (cubeLB t₁.A ![𝟙 t₁.A, t₁.act w] t₁.L) → LBIso t₂.L (cubeLB t₂.A ![𝟙 t₂.A, t₂.act w] t₂.L)) := by
  obtain ⟨φ, h, hL, -, hact⟩ := H₁
  obtain ⟨φ', h', hL', -, hact'⟩ := H₂
  let _ := t₀.ab.comm
  let _ := t₁.ab.comm
  let _ := t₂.ab.comm
  have := t₀.ab.smooth
  have := t₀.ab.proper
  have := t₀.ab.geomConnected
  have pr : IsProper (t₀.A ⊗ t₀.A).hom := by
    rw [Over.tensorObj_hom]
    infer_instance
  have i₂ := iso_cubeLB_pull h _ hL (push_comp h _ (push_fst h) (hact w)) (push_snd h)
  have i₃ := iso_cubeLB_pull h _ hL (push_fst h) (push_comp h _ (push_snd h) (hact w'))
  have i₄ := iso_cubeLB_pull h _ hL (push_id h) (push_end h (hact w))
  have j₂ := iso_cubeLB_pull h' _ hL' (push_comp h' _ (push_fst h') (hact' w)) (push_snd h')
  have j₃ := iso_cubeLB_pull h' _ hL' (push_fst h') (push_comp h' _ (push_snd h') (hact' w'))
  have j₄ := iso_cubeLB_pull h' _ hL' (push_id h') (push_end h' (hact' w))
  refine ⟨fun H => ?_, fun H => ?_⟩
  · have d := iso_down (isPullback_sqMap h) (smooth_tensorObj_hom _ _) pr (geometricallyConnected_tensorObj_hom _ _)
      (isLB_linComb t₀.isLB _ _) (isLB_linComb t₀.isLB _ _) (isLB_linComb t₁.isLB _ _) (isLB_linComb t₁.isLB _ _)
      i₂ i₃ H
    exact iso_up (isLB_linComb t₀.isLB _ _) (isLB_linComb t₀.isLB _ _) (isLB_linComb t₂.isLB _ _)
      (isLB_linComb t₂.isLB _ _) j₂ j₃ d
  · have d := iso_down h.1 ‹_› ‹_› ‹_› t₀.isLB (isLB_linComb t₀.isLB _ _) t₁.isLB (isLB_linComb t₁.isLB _ _) hL i₄ H
    exact iso_up t₀.isLB (isLB_linComb t₀.isLB _ _) t₂.isLB (isLB_linComb t₂.isLB _ _) hL' j₄ d

theorem adjoint_primitive_of_dense : Out.GlobalFnsSt → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (em : o →+* ℂ) (S : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp o) (t : TObj g k J b s), Dense (fromSet em (SharpClass (b := b) W a bas em) t) → (∀ j j', (a j).transpose * (W + W.transpose) = (W + W.transpose) * a j' → LBIso (cubeLB t.A ![fst t.A t.A ≫ t.act j, snd t.A t.A] t.L) (cubeLB t.A ![fst t.A t.A, snd t.A t.A ≫ t.act j'] t.L)) ∧ ∀ j, (W + W.transpose) * a j = W → LBIso t.L (cubeLB t.A ![𝟙 t.A, t.act j] t.L) := by
  intro hG cube h g W J a bas k o _ b em S _ s t hd
  let _ := t.ab.comm
  have : Nonempty (Sp ℂ) := inferInstanceAs (Nonempty (PrimeSpectrum ℂ))
  refine ⟨fun j j' hj => GlobalTheory.T.adjoint_endomorphisms_cubeLB_of_dense_fibres hG S t.A t.L _ _ t.ab t.isLB t.ample (t.hom j) (t.hom j') (hd.mono ?_),
    fun j hj => GlobalTheory.T.lbIso_cube_graph_of_dense_fibres hG S t.A t.L _ t.ab t.isLB t.ample t.rigid (t.hom j) (hd.mono ?_)⟩
  · rintro p ⟨K, _, x, hp, K₀, _, β, i, i', t₀, tx, tc, -, -, ⟨φ, hφ, hL, -, hact⟩, m₂, m₁, c, -, pr, hm, hu, hl,
      hmat, -⟩
    exact ⟨K, inferInstance, x, tx.A, inferInstance, tx.ab.comm, φ, tx.L, tx.act j, tx.act j', hp, hφ, tx.isLB, hL,
      hact j, hact j', (transfer m₁ m₂ j j').1 ((PowerAdjoint.matrix_primitive_adjoint cube W ℂ o _ h k _ c tc.pol pr
        hm hu hl (a j) (tc.act j) (hmat j)).2 (a j') (tc.act j') (hmat j') hj)⟩
  · rintro p ⟨K, _, x, hp, K₀, _, β, i, i', t₀, tx, tc, -, -, ⟨φ, hφ, hL, -, hact⟩, m₂, m₁, c, -, pr, hm, hu, hl,
      hmat, -⟩
    exact ⟨K, inferInstance, x, tx.A, inferInstance, tx.ab.comm, φ, tx.L, tx.act j, hp, hφ, tx.isLB, hL,
      hact j, (transfer m₁ m₂ j j).2 ((PowerAdjoint.matrix_primitive_adjoint cube W ℂ o _ h k _ c tc.pol pr
        hm hu hl (a j) (tc.act j) (hmat j)).1 hj)⟩

end GlobalTheory.SharpAdjoint
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV Filter Topology

namespace GlobalTheory.VolEx

theorem tendsto_pow_div_pow {i k : ℕ} (h : i ≤ k) :
    Tendsto (fun e : ℕ => (e : ℝ) ^ i / (e : ℝ) ^ k) atTop (𝓝 (if i = k then 1 else 0)) := by
  split_ifs with hik
  · subst hik
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with e he
    rw [div_self (by positivity)]
  · exact (tendsto_pow_div_pow_atTop_zero (𝕜 := ℝ) (lt_of_le_of_ne h hik)).comp tendsto_natCast_atTop_atTop

theorem tendsto_eval_div_pow (Q : Polynomial ℚ) {k : ℕ} (h : Q.natDegree ≤ k) :
    Tendsto (fun e : ℕ => ((Q.eval (e : ℚ) : ℚ) : ℝ) / (e : ℝ) ^ k) atTop (𝓝 (Q.coeff k : ℝ)) := by
  have h1 : Tendsto (fun e : ℕ => ∑ i ∈ Finset.range (k + 1), (Q.coeff i : ℝ) * ((e : ℝ) ^ i / (e : ℝ) ^ k)) atTop
      (𝓝 (∑ i ∈ Finset.range (k + 1), (Q.coeff i : ℝ) * (if i = k then 1 else 0))) :=
    tendsto_finsetSum _ fun i hi =>
      (tendsto_pow_div_pow (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))).const_mul _
  simp only [mul_ite, _root_.mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_range, Nat.lt_succ_self, if_true] at h1
  refine h1.congr fun e => ?_
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le h)]
  push_cast
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => (mul_div_assoc _ _ _).symm

variable {K : Type} [Field K] {X : Scheme.{0}}

theorem vAmp_of_veryAmpleBy {p : X ⟶ Sp K} {M : LB X} {m : ℕ} {s : Fin (m + 1) → M.Sec}
    (h : AbLaw.VeryAmpleBy p M s) : VAmp p M s := by
  refine ⟨h.1, fun i => ⟨(h.2 i).1, ?_⟩⟩
  obtain ⟨r, hr, hs⟩ := (h.2 i).2
  refine ⟨r, hr, fun f => ?_⟩
  obtain ⟨F, hF⟩ := hs f
  exact ⟨F, hF.symm⟩

theorem vol_of_eventually {p : X ⟶ Sp K} {M : LB X} (hex : ∀ e, ∃ r, SectionsHaveFiniteDimension p (lbPow M e) r) (φ : ℕ → ℝ)
    (hφ : ∀ᶠ e : ℕ in atTop, ∃ r, SectionsHaveFiniteDimension p (lbPow M e) r ∧ (r : ℝ) = φ e) {k : ℕ} {δ : ℝ}
    (hδ : Tendsto (fun e : ℕ => φ e / (e : ℝ) ^ k) atTop (𝓝 δ)) : Vol p M k δ := by
  have : ∀ e, ∃ r, SectionsHaveFiniteDimension p (lbPow M e) r ∧ ((∃ r, SectionsHaveFiniteDimension p (lbPow M e) r ∧ (r : ℝ) = φ e) → (r : ℝ) = φ e) := by
    intro e
    by_cases h : ∃ r, SectionsHaveFiniteDimension p (lbPow M e) r ∧ (r : ℝ) = φ e
    · obtain ⟨r, h1, h2⟩ := h
      exact ⟨r, h1, fun _ => h2⟩
    · obtain ⟨r, h1⟩ := hex e
      exact ⟨r, h1, fun h' => absurd h' h⟩
  choose h h1 h2 using this
  refine ⟨h, h1, hδ.congr' ?_⟩
  filter_upwards [hφ] with e he
  rw [h2 e he]

theorem vol_nonneg {p : X ⟶ Sp K} {M : LB X} {k : ℕ} {δ : ℝ} (h : Vol p M k δ) : 0 ≤ δ := by
  obtain ⟨h, -, hh⟩ := h
  exact ge_of_tendsto' hh fun e => by positivity

theorem exists_vol : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left), M.IsLB → Out.RelAmple P.A M → ∃ δ : ℝ, 0 < δ ∧ Vol P.A.hom M P.g δ := by
  intro hL _ K _ _ P M hM hA
  have hex : ∀ (N : LB P.A.left), N.IsLB → ∀ e, ∃ r, SectionsHaveFiniteDimension P.A.hom (lbPow N e) r := fun N hN e =>
    (GlobalTheory.T.sectionsGrowth_basic_properties_abelianVariety K P (lbPow N e) 0 (LB.isLB_linComb hN _ _)).1
  have : IsProper P.A.hom := P.isAb.proper
  obtain ⟨d, hd, m, s, hs⟩ :=
    ((relAmple_iff_isAmpleLB_of_isAffine P.A hM).1 hA).exists_veryAmpleBy (R := K) P.A.hom
  have hH : (lbPow M d).IsLB := LB.isLB_linComb hM _ _
  obtain ⟨Q, hQ⟩ := GlobalTheory.T.hilbertFunction_vanishingIdeal_veryAmpleSystem K (Fin (m + 1)) _ P.A.hom (lbPow M d) s hH (vAmp_of_veryAmpleBy hs)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have volM : ∀ k, Q.natDegree ≤ k → Vol P.A.hom M k ((Q.coeff k : ℝ) / (d : ℝ) ^ k) := by
    intro k hk
    refine (GlobalTheory.T.sectionsGrowth_basic_properties_abelianVariety K P M k hM).2.2.2.2.1 d _ hd hA ?_
    rw [mul_div_cancel₀ _ (by positivity)]
    refine vol_of_eventually (hex _ hH) _ ?_ (tendsto_eval_div_pow Q hk)
    filter_upwards [hQ] with e ⟨r, h1, h2, _⟩
    exact ⟨r, h1, by rw [← h2]; norm_cast⟩
  have volL : ∀ k, P.g ≤ k → Vol P.A.hom P.L k (if P.g = k then 1 else 0) := by
    intro k hk
    refine vol_of_eventually (hex _ P.isLB) (fun e => (e : ℝ) ^ P.g) ?_ (tendsto_pow_div_pow hk)
    filter_upwards [eventually_ge_atTop 1] with e he
    exact ⟨e ^ P.g, PowSec.exists_basis_sections hL.globalSectionsRank K P e he, by push_cast; rfl⟩
  have dom : ∀ (A B : LB P.A.left), A.IsLB → B.IsLB → Out.RelAmple P.A A → ∃ c : ℕ, ∀ k δ δ',
      Vol P.A.hom B k δ → Vol P.A.hom A k δ' → δ ≤ (c : ℝ) ^ k * δ' := by
    intro A B hA hB ha
    obtain ⟨c, ⟨⟨t, ht⟩, -⟩, hc⟩ := ((GlobalTheory.T.eventually_section_and_relAmple_pow_div K P A B hA hB ha).and (eventually_ge_atTop 1)).exists
    refine ⟨c, fun k δ δ' h1 h2 => ?_⟩
    exact ((GlobalTheory.T.sectionsGrowth_basic_properties_abelianVariety K P B k hB).2.2.2.2.2 (lbPow A c) t (LB.isLB_linComb hA _ _) ht).2 _ _ h1
      ((GlobalTheory.T.sectionsGrowth_basic_properties_abelianVariety K P A k hA).2.2.2.1 c δ' hc h2)
  have hdeg : Q.natDegree ≤ P.g := by
    by_contra hlt
    push Not at hlt
    obtain ⟨c, hc⟩ := dom P.L M P.isLB hM P.ample
    have h1 := hc _ _ _ (volM _ le_rfl) (volL _ hlt.le)
    rw [if_neg hlt.ne, mul_zero] at h1
    have h2 := le_antisymm h1 (vol_nonneg (volM _ le_rfl))
    rw [div_eq_zero_iff] at h2
    rcases h2 with h2 | h2
    · have h3 : Q.leadingCoeff = 0 := by exact_mod_cast h2
      rw [Polynomial.leadingCoeff_eq_zero] at h3
      rw [h3] at hlt
      simp at hlt
    · exact absurd h2 (by positivity)
  refine ⟨_, ?_, volM _ hdeg⟩
  obtain ⟨c, hc⟩ := dom M P.L hM P.isLB hA
  have h1 := hc _ _ _ (volL _ le_rfl) (volM _ hdeg)
  rw [if_pos rfl] at h1
  refine lt_of_le_of_ne (vol_nonneg (volM _ hdeg)) fun h => ?_
  rw [← h, mul_zero] at h1
  exact absurd h1 (by norm_num)

end GlobalTheory.VolEx
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_local_multiplicationPullback_theta_embedding : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (m : ℕ) (R : Type) [CommRing R] (x : Sp R ⟶ S) (v : Ix g (N' ^ 2) → R), m ^ 2 ∣ N' → 2 ≤ m → t.HasTh x v → ∀ p : Sp R, ∃ (R' : Type) (_ : CommRing R') (φ : R →+* R') (σ : _), IsOpenImmersion (spMap φ) ∧ p ∈ Set.range (spMap φ) ∧ t.Emb m (Over.mk (spMap φ ≫ x)) σ ∧ ProjRep (idealOf (fst (Over.mk (spMap φ ≫ x)) t.A).left _ σ (𝟙 _)) (fst (Over.mk (spMap φ ≫ x)) t.A).left _ σ := by
  first | exact @GlobalTheory.ZM.EmbedLocal.exists_emb_projRep | exact GlobalTheory.ZM.EmbedLocal.exists_emb_projRep | (intros; apply GlobalTheory.ZM.EmbedLocal.exists_emb_projRep <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem tangent_eq_constPt_of_tMap : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g n N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (I : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)) (Y : MMPre n N' I) (u : TObj g (N' ^ 2) J b Y.s), Odd N' → (∀ (R : Type) [CommRing R] (x : Sp R ⟶ Y.MM) (v : Ix g (N' ^ 2) → R), u.HasTh x v ↔ SecCoord Y.de Y.th x v) → ∀ (K : Type) [Field K] (x : Sp (DualNumber K) ⟶ Y.MM) (t : TObj g (N' ^ 2) J b (x ≫ Y.s)), x ≫ Y.s = constPt x ≫ Y.s → TMap t u x → TMap t u (constPt x) → x = constPt x := by
  intro hL hL2 o _ g n N' J b I Y u hN hu K _ x t hs h1 h2
  have hsub : Subsingleton (PrimeSpectrum (DualNumber K)) := by
    have key : ∀ p : PrimeSpectrum (DualNumber K),
        p.asIdeal = RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom := by
      intro p
      have hp := p.isPrime
      have hle : RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom ≤ p.asIdeal := by
        intro a ha
        have ha' : a.fst = 0 := ha
        apply hp.mem_of_pow_mem 2
        have : a ^ 2 = 0 := by
          rw [sq]; ext <;> simp [ha']
        rw [this]; exact p.asIdeal.zero_mem
      have hmax : (RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom).IsMaximal :=
        RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨TrivSqZeroExt.inl c, rfl⟩)
      exact (hmax.eq_of_le hp.ne_top hle).symm
    exact ⟨fun p q => PrimeSpectrum.ext ((key p).trans (key q).symm)⟩
  have hsub' : Subsingleton (Sp (DualNumber K)) := hsub
  obtain ⟨p⟩ : Nonempty (Sp (DualNumber K)) := inferInstanceAs (Nonempty (PrimeSpectrum (DualNumber K)))
  obtain ⟨R, _, j, v, hj, ⟨q, _⟩, hv⟩ := GlobalTheory.T.exists_thetaConstants_locally_on_base hL hL2 o g N' J b _ _ t hN p
  have hsurj : Function.Surjective j := fun y => ⟨q, Subsingleton.elim _ _⟩
  have hiso : IsIso j := by
    apply isIso_of_isOpenImmersion_of_opensRange_eq_top
    ext y
    simpa using hsurj y
  have c1 := (hu R _ v).1 ((GlobalTheory.T.hasThetaConstants_iff_of_thetaLevelPullback o g N' J b _ _ u _ _ t x R j v h1).1 hv)
  have c2 := (hu R _ v).1 ((GlobalTheory.T.hasThetaConstants_iff_of_thetaLevelPullback o g N' J b _ _ u _ _ t (constPt x) R j v h2).1 hv)
  obtain ⟨β, hβ⟩ := Spec.map_surjective (R := CommRingCat.of o) (S := CommRingCat.of R) (j ≫ x ≫ Y.s)
  have e1 : (j ≫ x) ≫ Y.s = spMap β.hom := by
    rw [Category.assoc]; exact hβ.symm
  have e2 : (j ≫ constPt x) ≫ Y.s = spMap β.hom := by
    rw [Category.assoc, ← hs]; exact hβ.symm
  have h := (Y.pts R β.hom v (Y.loc R β.hom _ v e1 c1)).unique ⟨e1, c1⟩ ⟨e2, c2⟩
  exact (cancel_epi j).1 h

end GlobalTheory.ZM
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

theorem _root_.GlobalTheory.T.exists_iso_polarisedAbelianSchemes_dvr_of_fieldExtension : Laws → Laws2 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (P P' : PolAV (Sp V)) (C : Type) [Field C] [Algebra (FractionRing V) C] (φ : TF (R := V) C ⊗ P.A ≅ TF (R := V) C ⊗ P'.A), φ.hom ≫ fst _ _ = fst _ _ → lift (𝟙 (TF (R := V) C)) (1 : TF (R := V) C ⟶ P.A) ≫ φ.hom ≫ snd _ _ = 1 → LBIso (P.L.pull (snd (TF (R := V) C) P.A).left) (P'.L.pull (φ.hom ≫ snd (TF (R := V) C) P'.A).left) → ∀ (κ : TF (R := V) C ⟶ TK V) (g : TK V ⊗ P.A ⟶ P'.A), κ ▷ P.A ≫ g = φ.hom ≫ snd _ _ → ∃ Ψ : P.A ≅ P'.A, IsMonHom Ψ.hom ∧ φ.hom ≫ snd _ _ = snd _ _ ≫ Ψ.hom ∧ LBIso P.L (P'.L.pull Ψ.hom.left) := by
  first | exact @GlobalTheory.IsoOverField.exists_iso_over_dvr | exact GlobalTheory.IsoOverField.exists_iso_over_dvr | (intros; apply GlobalTheory.IsoOverField.exists_iso_over_dvr <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem _root_.GlobalTheory.T.exists_principallyPolarised_model_localizationAway : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (P : Out.PolAV (Sp K)), ∃ (f : R) (_ : f ≠ 0) (ψ : (Localization.Away f) →+* K) (P' : Out.PolAV (Sp (Localization.Away f))) (φ : P.A.left ⟶ P'.A.left), ψ.comp (algebraMap R _) = algebraMap R K ∧ P'.g = P.g ∧ IsGrpPullback P.A P'.A (spMap ψ) φ ∧ LBIso P.L (P'.L.pull φ) := by
  first | exact @GlobalTheory.polAV_spread | exact GlobalTheory.polAV_spread | (intros; apply GlobalTheory.polAV_spread <;> assumption)
end

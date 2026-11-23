module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle509
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrisZeroSurjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle523
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle374
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle380
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle559
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle433
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle435
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneMemGoodCT
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommuteRtOfMemZalg
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle516
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle561
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.Bundle001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.Bundle002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle562
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusFactorisation.PullT
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle563
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical


theorem _root_.GlobalTheory.T.swap_twist_compact_part_le : ∀ {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (σ : H →* H) (K : Subgroup H) (d d' : H),
  Continuous σ → (∀ g, σ (σ g) = g) → IsOpen (K : Set H) → IsCompact (K : Set H) → (∀ k ∈ K, σ k ∈ K) →
  PositivityTheory.Rg.BcB.G8.Fin.Good (MonoidHom.id H) K (d * σ d') → ∀ y : H × H,
  twCent (swTw σ) (d, d') ⊓ (K.prod K).map (MulAut.conj y).toMonoidHom ≤ cptPart (twCent (swTw σ) (d, d')) ∧
    (twCent (swTw σ) (d, d') ⊓ (K.prod K).map (MulAut.conj y).toMonoidHom).relIndex (cptPart (twCent (swTw σ) (d, d'))) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.SplitCpt.split_cpt | exact GlobalTheory.CompanionTheory.SplitCpt.split_cpt | (intros; apply GlobalTheory.CompanionTheory.SplitCpt.split_cpt <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.Pb

noncomputable section
namespace GlobalTheory.CompanionTheory.BcAcris

theorem pull_comm {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (M : Model l K) (j n : ℕ)
    (Q' : ObjectProperty (Thick (nlFun (B.DD true (base l) n) l M.X M.p (Mid.κm r n)))) (a : AW r)
    (y : (Wc.HS l (B.schFn M.p) r.ρ j).M n) :
    (toQ Q' ((base l).cris n)).pull j (idA r a • bWL r M n j y) =
      (base l).cris n a • (toQ Q' ((base l).cris n)).pull j
        ((B.omMor ((nm r M n).mor l) r.w (Mid.wn_mk r n)).pull j y) := by
  have e : bWL r M n j y = (B.omMor ((nm r M n).mor l) r.w (Mid.wn_mk r n)).pull j y :=
    congrArg (fun t => CH.Mor.pull t j y) (bWMorL_eq r M n)
  exact (congrArg (fun v => (toQ Q' ((base l).cris n)).pull j (idA r a • v)) e).trans
    (LinearMap.map_smulₛₗ ((toQ Q' ((base l).cris n)).pull j) (idA r a) _)



theorem bc_tens : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (M : Model l K), M.Sm → ∀ j n,
    Tens (WittVector l r.k) (N := fun _ : Unit => AW r) (M := fun _ => (Wc.HS l (B.schFn M.p) r.ρ j).M n)
      (M' := Mid.HM r M n j) fun _ a y => idA r a • bWL r M n j y := by
  intro l _ K r M hM j n
  letI := (Mid.wn r n).toAlgebra
  haveI : Module.Flat (Wc.Wm l r.k n) ((base l).Acr n) := GlobalTheory.T.flat_acris_truncated_witt r n
  obtain ⟨U⟩ := cov_of_sm M hM
  let m := nm r M n
  let Q : ObjectProperty (Thick (nlFun (Wc.pd l r.k n) l M.X M.p ((Wc.res l r.k n).comp r.ρ))) := St ⊤ {⊤}
  let Q' : ObjectProperty (Thick (nlFun (B.DD true (base l) n) l M.X M.p (Mid.κm r n))) := St ⊤ {⊤}
  have hQ : ∀ T, Q T := st_all
  have hQ' : ∀ T, Q' T := st_all
  have h : ∀ T, Q' T → Q ((m.mor l).functor.obj T) := fun T _ => hQ _
  have ha : ∀ a, (m.smor Q Q' h).LeC a (oT Q) (oT Q') := fun a => GlobalTheory.CompanionTheory.BcCov.leC_top _ a _ _ (oT_top Q')
  have hb : ∀ a, (m.smor Q Q' h).LeC a (oB Q) (oB Q') := fun a => GlobalTheory.CompanionTheory.BcCov.leC_bot _ a _ _ fun T => oB_bot Q _
  have T := GlobalTheory.T.nilpotent_identity_morphism_compat (Fact.out : l.Prime).ne_zero (l_nil r n) m rfl rfl U Q Q' rfl rfl h ha hb j
  refine tens_change (A := AW r) (Ideal.Quotient.mk _) ((base l).cris n) (cris_surjective n) (fun w => rfl)
    Ideal.Quotient.mk_surjective ((l : WittVector l r.k) ^ n)
    (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)) ?_
    ((toQ Q (Ideal.Quotient.mk _)).pull j) (toQ_pull_bijective Q _ hQ j)
    ((toQ Q' ((base l).cris n)).pull j).toAddMonoidHom (toQ_pull_bijective Q' _ hQ' j)
    _ _ ?_ T
  · intro a h0
    obtain ⟨b, hb'⟩ := cris_ker n a h0
    refine ⟨b, hb'.trans ?_⟩
    change _ = r.w _ * b
    rw [map_pow, map_natCast]
  · intro a y
    have key := sqC_toQ m Q Q' h (Ideal.Quotient.mk _) ((base l).cris n) r.w (Mid.wn_mk r n) ((base l).cris n a)
      (ha _) (hb _) j y
    exact (pull_comm r M j n Q' a y).trans key.symm

end GlobalTheory.CompanionTheory.BcAcris
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsHorizontal charOf)
open GlobalTheory.CompanionTheory.MPDict

namespace GlobalTheory.CompanionTheory.MixZ.PtDictProof

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem C_mem_ptIdeal_iff (x : MP ℤ m n) (a : ℤ) :
    (C a : MRing (Bk n)) ∈ ptIdeal x ↔ (a : (MP ℤ m n).residueField x) = 0 := by
  rw [ptIdeal, ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal, RingHom.mem_ker, ReciprocityTheory.ChartRestriction.G.Geo.mConeMap,
    MvPolynomial.aeval_C]
  have h : (algebraMap ℤ (MvPolynomial (Fin (m + 1)) ((MP ℤ m n).residueField x)) a) =
      MvPolynomial.C (a : (MP ℤ m n).residueField x) := by
    simp
  rw [h, MvPolynomial.C_eq_zero]

theorem evaluation_generic_injective (Z : Scheme.{0}) [IsIntegral Z] :
    Function.Injective (Z.evaluation ⊤ (genericPoint Z) (Opens.mem_top _)).hom := by
  rw [← Scheme.germ_residue, CommRingCat.hom_comp, RingHom.coe_comp]
  refine Function.Injective.comp ?_ (germ_injective_of_isIntegral Z _ _)
  exact RingHom.injective (Z.residue (genericPoint Z)).hom

theorem dim_closure_image_generic {X Z : Scheme.{0}} [IsIntegral Z] (j : Z ⟶ X) [IsClosedImmersion j] :
    topologicalKrullDim (closure ({j (genericPoint Z)} : Set X)) = topologicalKrullDim Z := by
  have hg := (genericPoint_spec Z).image (f := j) j.isClosedEmbedding.continuous
  have hcl : closure ({j (genericPoint Z)} : Set X) = Set.range j := by
    have h1 : closure ({j (genericPoint Z)} : Set X) = closure (j '' Set.univ) := hg
    rw [h1, Set.image_univ]
    exact j.isClosedEmbedding.isClosed_range.closure_eq
  rw [hcl]
  exact (IsHomeomorph.topologicalKrullDim_eq _
    j.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph).symm

theorem charZero_residueField_iff {Z : Scheme.{0}} [IsIntegral Z] (j : Z ⟶ MP ℤ m n) :
    CharZero ((MP ℤ m n).residueField (j (genericPoint Z))) ↔ CharZero Γ(Z, ⊤) := by
  constructor
  · intro h
    haveI : CharZero (Z.residueField (genericPoint Z)) :=
      charZero_of_injective_ringHom (f := (Scheme.Hom.residueFieldMap j (genericPoint Z)).hom)
        (RingHom.injective _)
    exact RingHom.charZero (Z.evaluation ⊤ (genericPoint Z) (Opens.mem_top _)).hom
  · intro h
    haveI : CharZero (Z.residueField (genericPoint Z)) :=
      charZero_of_injective_ringHom (evaluation_generic_injective Z)
    exact RingHom.charZero (Scheme.Hom.residueFieldMap j (genericPoint Z)).hom

theorem charOf_prime {P : Ideal (MRing (Bk n))} [P.IsPrime] (h : ¬ IsHorizontal P) : (charOf P).Prime := by
  unfold charOf
  rw [← Int.prime_iff_natAbs_prime]
  exact Submodule.IsPrincipal.prime_generator_of_isPrime _ h

theorem C_charOf_mem (P : Ideal (MRing (Bk n))) : (C ((charOf P : ℕ) : ℤ) : MRing (Bk n)) ∈ P := by
  have hg := Submodule.IsPrincipal.generator_mem (P.comap (C : ℤ →+* MRing (Bk n)))
  obtain ⟨c, hc⟩ := Int.dvd_natAbs.mpr
    (dvd_refl (Submodule.IsPrincipal.generator (P.comap (C : ℤ →+* MRing (Bk n)))))
  have hmem : ((charOf P : ℕ) : ℤ) ∈ P.comap (C : ℤ →+* MRing (Bk n)) := by
    unfold charOf
    rw [hc]
    exact Ideal.mul_mem_right c _ hg
  exact Ideal.mem_comap.mp hmem

theorem charOf_cast_eq_zero {Z : Scheme.{0}} [IsIntegral Z] (j : Z ⟶ MP ℤ m n) :
    ((charOf (ptIdeal (j (genericPoint Z))) : ℕ) : Γ(Z, ⊤)) = 0 := by
  have h1 := (C_mem_ptIdeal_iff (j (genericPoint Z)) _).mp (C_charOf_mem _)
  have h2 := congrArg (Scheme.Hom.residueFieldMap j (genericPoint Z)).hom h1
  apply evaluation_generic_injective Z
  rw [map_natCast, map_zero]
  simpa using h2

end GlobalTheory.CompanionTheory.MixZ.PtDictProof

namespace GlobalTheory.CompanionTheory.MixZ


open GlobalTheory.CompanionTheory.MixZ.PtDictProof in
theorem ptDict : PtDict := by
  intro m n Z _ j _ d hd
  have hP := isMultiProjPrime_ptIdeal m n (j (genericPoint Z))
  haveI : (ptIdeal (j (genericPoint Z))).IsPrime := hP.1
  have hH : IsHorizontal (ptIdeal (j (genericPoint Z))) ↔ CharZero Γ(Z, ⊤) :=
    (ptIdeal_isHorizontal_iff m n _).trans (charZero_residueField_iff j)
  refine ⟨hP, hH, fun h => ?_, fun h => ⟨charOf_prime h, charOf_cast_eq_zero j⟩⟩
  have hc : CharZero ((MP ℤ m n).residueField (j (genericPoint Z))) :=
    (ptIdeal_isHorizontal_iff m n _).mp h
  have hdim : topologicalKrullDim (closure ({j (genericPoint Z)} : Set (MP ℤ m n))) = (d : ℕ) := by
    rw [dim_closure_image_generic j, hd]
  exact (GlobalTheory.T.closure_dim_iff_arithmetic_variety m n _ d hc).mp hdim

end GlobalTheory.CompanionTheory.MixZ
end
end

section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin Matrix

noncomputable section
namespace GlobalTheory.CompanionTheory.CTFin.Slice1

theorem slice_mem_genSpace : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (L : Subgroup (GL (Fin (r + s)) (Af E))), IsOpen (L : Set (GL (Fin (r + s)) (Af E))) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Kinf E (r + s)) W), GlobalTheory.Published.AutFin.IsContRep ρ → ∀ J : Set (Module.End ℂ (Sm E (r + s))), Cofin J → ∀ J₁ : Set (Module.End ℂ (Sm E r)), Cofin J₁ → (∀ F : Sm E (r + s), (∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip x * g) = F.1 g) → (∀ z ∈ J, z F = 0) → ∀ G : Sm E r, (∀ m, G.1 m = F.1 (lev (Ad E) r s (m, 1))) → ∀ z ∈ J₁, z G = 0) → ∀ (t : GL (Fin (r + s)) (Af E)) (κ : Kinf E (r + s)), ∃ (L₁ : Subgroup (GL (Fin r) (Af E))) (ρ₁ : Representation ℂ (Kinf E r) W), IsOpen (L₁ : Set (GL (Fin r) (Af E))) ∧ GlobalTheory.Published.AutFin.IsContRep ρ₁ ∧ ∀ F ∈ goodCT L ρ J, ∀ m₂ : GA E s, ∃ G ∈ genSpace L₁ ρ₁ J₁, ∀ m₁ : GA E r, G.1 m₁ = F.1 (lev (Ad E) r s (m₁, m₂) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ)) := by
  intro E _ _ _ r s L hL W _ _ _ ρ hρ J hJ J₁ hJ₁ H3 t κ
  refine ⟨levelOne s L t, ρ.comp (levK E r s), isOpen_levelOne hL t,
    fun ℓ w => (hρ ℓ w).comp continuous_levK, ?_⟩
  intro F hF m₂
  obtain ⟨hN, hM, hLv, hC, hG, hZ⟩ := hF
  let h : GA E (r + s) := lev (Ad E) r s (1, m₂) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ)
  let F' := rt E (r + s) h F
  let G : Sm E r := ⟨_, GlobalTheory.T.levi_restriction_smooth E r s F'.1 F'.2⟩
  have hGv : ∀ m₁, G.1 m₁ = F.1 (lev (Ad E) r s (m₁, m₂) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ)) := by
    intro m₁
    change F.1 (lev (Ad E) r s (m₁, 1) * h) = _
    have e : (m₁, m₂) = ((m₁, 1) * (1, m₂) : GA E r × GA E s) := by simp
    rw [e, map_mul]
    simp only [h, mul_assoc]

  have hcoef : ∀ g : GA E r, (fun k : Kinf E r => (cptRep E r k G).1 g) ∈
      GlobalTheory.Published.AutFin.coeffSpan (ρ.comp (levK E r s)) := by
    intro g
    have key := coeff_comp ρ (levK E r s) κ (hC (lev (Ad E) r s (g, m₂) * finGL E (r + s) t))
    convert key using 1
    funext k
    change G.1 (g * infGL E r (Unitary.toUnits k)) = F.1 (lev (Ad E) r s (g, m₂) * finGL E (r + s) t *
      infGL E (r + s) (Unitary.toUnits (levK E r s k * κ)))
    rw [hGv, lev_infGL_right, ← toUnits_levK (s := s),
      ← map_mul (Unitary.toUnits : _ →* (Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E))ˣ)]

  have hle : (levelOne s L t : Set (GL (Fin r) (Af E))) ⊆ {k | finRep E r k G = G} := by
    intro k hk
    refine Subtype.ext (funext fun m => ?_)
    change G.1 (m * finGL E r k) = G.1 m
    rw [hGv, hGv]
    have hk' : F.1 (lev (Ad E) r s (m, m₂) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ) *
        finGL E (r + s) (t⁻¹ * lev (Af E) r s (k, 1) * t)) =
        F.1 (lev (Ad E) r s (m, m₂) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ)) :=
      congrFun (congrArg Subtype.val (hLv _ (mem_levelOne.1 hk))) _
    rw [← hk', lev_finGL_right]

  have hkill : ∀ z ∈ J₁, z G = 0 := by
    refine H3 F' (fun x g => ?_) (fun z hz => ?_) G (fun m => rfl)
    · change F.1 (unip x * g * h) = F.1 (g * h)
      rw [mul_assoc, hN]
    · change z (rt E (r + s) h F) = 0
      rw [← Module.End.mul_apply, (commute_rt_of_mem_Zalg (hJ.1 hz) h).eq, Module.End.mul_apply, hZ z hz, map_zero]
  refine ⟨G, ⟨⟨fun γ g => ?_, isOpen_stab_of_mem_nhds (finRep E r) G
      (Filter.mem_of_superset ((isOpen_levelOne hL t).mem_nhds (one_mem _)) hle),
    kfin_of_coeff _ G hcoef, zfin_of_cofin hJ₁ hkill, fun g => ?_⟩, fun k hk => hle hk, hcoef, hkill⟩, hGv⟩
  ·
    rw [hGv, hGv]
    have e : lev (Ad E) r s (ratGL E r γ * g, m₂) = lev (Ad E) r s (ratGL E r γ, ratGL E s 1) * lev (Ad E) r s (g, m₂) := by
      rw [← map_mul, Prod.mk_mul_mk, map_one, one_mul]
    simp only [e, mul_assoc]
    exact hM (γ, 1) _
  ·
    obtain ⟨C, N, hb⟩ := hG (lev (Ad E) r s (g, m₂) * finGL E (r + s) t)
    obtain ⟨B, hB0, hB⟩ := GlobalTheory.T.levi_embedding_height_bound E r s (Unitary.toUnits κ)
    refine ⟨|C| * B ^ N, N, fun y => ?_⟩
    have e1 : G.1 (g * infGL E r y) = F.1 (lev (Ad E) r s (g, m₂) * finGL E (r + s) t *
        infGL E (r + s) (lev (Cinf E) r s (y, 1) * Unitary.toUnits κ)) := by
      rw [hGv, lev_infGL_right]
    rw [e1]
    have h1 := hb (lev (Cinf E) r s (y, 1) * Unitary.toUnits κ)
    have h2 := hB y
    have h0 : 0 ≤ height (lev (Cinf E) r s (y, 1) * Unitary.toUnits κ) := zero_le_one.trans (one_le_height _)
    calc _ ≤ C * height (lev (Cinf E) r s (y, 1) * Unitary.toUnits κ) ^ N := h1
      _ ≤ |C| * height (lev (Cinf E) r s (y, 1) * Unitary.toUnits κ) ^ N :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg h0 N)
      _ ≤ |C| * (B * height y) ^ N := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h2 N) (abs_nonneg C)
      _ = |C| * B ^ N * height y ^ N := by rw [mul_pow, mul_assoc]

end GlobalTheory.CompanionTheory.CTFin.Slice1
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Gunr

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gunr
open scoped TensorProduct

theorem inclR_mem_Rv {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ}
    (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (e : E)
    (h : ∀ k, algebraMap F (Fv F v) (bs.repr e k) ∈ v.adicCompletionIntegers F) :
    inclR (F := F) (Fv F v) e ∈ Rv bs v := by
  simp only [Rv, Set.mem_ofPred_eq]
  intro k
  rw [show inclR (F := F) (Fv F v) e = (1 : Fv F v) ⊗ₜ[F] e from rfl,
    Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply]
  exact h k

theorem sigR_inclR {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (v : HeightOneSpectrum (𝓞 F)) (e : E) :
    sigR (Fv F v) σ (inclR (F := F) (Fv F v) e) = inclR (F := F) (Fv F v) (σ e) := by
  show Algebra.TensorProduct.map (AlgHom.id F (Fv F v)) σ ((1 : Fv F v) ⊗ₜ[F] e)
    = (1 : Fv F v) ⊗ₜ[F] σ e
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

theorem coe_det_matS {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {v : HeightOneSpectrum (𝓞 F)} (S : Subring (Fv F v ⊗[F] E)) {m : ℕ} (X : Matrix (Fin m) (Fin m) E)
    (hX : ∀ i j, inclR (F := F) (Fv F v) (X i j) ∈ S) :
    (((matS S X hX).det : S) : Fv F v ⊗[F] E) = inclR (F := F) (Fv F v) X.det := by
  have h1 : S.subtype.mapMatrix (matS S X hX) = (inclR (F := F) (Fv F v)).mapMatrix X := by
    ext i j
    rfl
  rw [show (((matS S X hX).det : S) : Fv F v ⊗[F] E) = S.subtype (matS S X hX).det from rfl,
    RingHom.map_det, h1, ← RingHom.map_det]

theorem locMat : LocMat := by
  unfold LocMat
  intro F E _ _ _ _ _ σ d bs v S σS hS hσS m X hherm hdet hint
  have memS : ∀ e : E, (∀ k, algebraMap F (Fv F v) (bs.repr e k) ∈ v.adicCompletionIntegers F) →
      inclR (F := F) (Fv F v) e ∈ S := by
    intro e he
    have h := inclR_mem_Rv bs v e he
    rw [← hS] at h
    exact h
  have hX : ∀ i j, inclR (F := F) (Fv F v) (X i j) ∈ S := by
    intro i j
    apply memS
    intro k
    apply hint
    simp only [matSet, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inl ⟨(i, j, k), rfl⟩
  have hinv : inclR (F := F) (Fv F v) X.det⁻¹ ∈ S := by
    apply memS
    intro k
    apply hint
    simp only [matSet, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inr ⟨k, rfl⟩
  refine ⟨hX, ?_, ?_⟩
  · ext i j
    show ((σS (matS S X hX j i) : S) : Fv F v ⊗[F] E) = inclR (F := F) (Fv F v) (X i j)
    rw [hσS]
    show sigR (Fv F v) σ (inclR (F := F) (Fv F v) (X j i)) = inclR (F := F) (Fv F v) (X i j)
    rw [sigR_inclR, hherm]
  · refine isUnit_iff_exists_inv.mpr ⟨⟨inclR (F := F) (Fv F v) X.det⁻¹, hinv⟩, ?_⟩
    apply Subtype.ext
    show (((matS S X hX).det : S) : Fv F v ⊗[F] E) * inclR (F := F) (Fv F v) X.det⁻¹ = 1
    rw [coe_det_matS, ← map_mul, mul_inv_cancel₀ hdet, map_one]

end GlobalTheory.CompanionTheory.Gunr

end
end

section

namespace GlobalTheory.CompanionTheory.Gunr

open NumberField IsDedekindDomain Filter

theorem finInt : PositivityTheory.SiegelWeilFormula.Gunr.FinInt := by
  intro F _ _ X
  have hone : ∀ x : F, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      algebraMap F (v.adicCompletion F) x ∈ v.adicCompletionIntegers F := by
    intro x
    have hfin : {v : HeightOneSpectrum (𝓞 F) | 1 < v.valuation F x}.Finite :=
      HeightOneSpectrum.Support.finite (𝓞 F) x
    have hev : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ¬ 1 < v.valuation F x := by
      rw [eventually_cofinite]
      simpa using hfin
    refine hev.mono fun v hv => ?_
    have e : Valued.v (algebraMap F (v.adicCompletion F) x) = v.valuation F x :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, e]
    exact not_lt.mp hv
  have hall : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      ∀ x ∈ X, algebraMap F (v.adicCompletion F) x ∈ v.adicCompletionIntegers F :=
    (Filter.eventually_all_finset X).2 fun x _ => hone x
  exact hall

end GlobalTheory.CompanionTheory.Gunr
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.dictionary_maximal_compact_parts : PositivityTheory.PfSWUS.DictKAOfParts := by
  first | exact @GlobalTheory.CompanionTheory.SWDict.dictKA_of_parts | exact GlobalTheory.CompanionTheory.SWDict.dictKA_of_parts | (intros; apply GlobalTheory.CompanionTheory.SWDict.dictKA_of_parts <;> assumption)
end
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.anisotropy_of_range : PositivityTheory.PfSWUS.AnisoOfRange := by
  first | exact @GlobalTheory.CompanionTheory.AnisoRange.anisoOfRange | exact GlobalTheory.CompanionTheory.AnisoRange.anisoOfRange | (intros; apply GlobalTheory.CompanionTheory.AnisoRange.anisoOfRange <;> assumption)
end
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.whittaker_maximal_compact_general : PositivityTheory.PfSWUS.WhitKAOfGenLt := by
  first | exact @GlobalTheory.CompanionTheory.IwaAd.whitKAOfGenLt | exact GlobalTheory.CompanionTheory.IwaAd.whitKAOfGenLt | (intros; apply GlobalTheory.CompanionTheory.IwaAd.whitKAOfGenLt <;> assumption)
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.teichmuller_mu_galois_compat : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ w, ACris.galCris σ (r.w w) = r.w w) (n j : ℕ) (t : Mid.HM r M n j), B.galHc (B.schFn M.p) (okToOC l K) σ (galOC_okToOC σ) true n j (Mid.mu r M n j hT t) = Mid.mu r M n j hT (galM r M σ hσ n j t) := by
  first | exact @GlobalTheory.CompanionTheory.MuGal.mu_gal | exact GlobalTheory.CompanionTheory.MuGal.mu_gal | (intros; apply GlobalTheory.CompanionTheory.MuGal.mu_gal <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.teichmuller_mu_reduction_compat : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (n j : ℕ) (t : Mid.HM r M (n + 1) j), B.redHc (B.schFn M.p) (okToOC l K) true (Nat.le_succ n) j (Mid.mu r M (n + 1) j hT t) = Mid.mu r M n j hT ((redT r M (Nat.le_succ n)).pull j t) := by
  first | exact @GlobalTheory.CompanionTheory.CrysMid.mu_redHc | exact GlobalTheory.CompanionTheory.CrysMid.mu_redHc | (intros; apply GlobalTheory.CompanionTheory.CrysMid.mu_redHc <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.teichmuller_nu_frobenius_compat : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (n j : ℕ) (x : B.Hc (B.schFn M.p) (okToOC l K) true n j), Mid.nu r M n j hT (B.phiHc (B.schFn M.p) (okToOC l K) n j x) = phiM r M n j (Mid.nu r M n j hT x) := by
  first | exact @GlobalTheory.CompanionTheory.NuPhi.nu_phi | exact GlobalTheory.CompanionTheory.NuPhi.nu_phi | (intros; apply GlobalTheory.CompanionTheory.NuPhi.nu_phi <;> assumption)
end

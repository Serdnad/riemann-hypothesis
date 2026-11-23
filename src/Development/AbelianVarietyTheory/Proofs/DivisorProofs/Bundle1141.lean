module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrincipalSeriesAppendEquivParabolicProduct
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Linter.Style
public import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1103
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle038
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1052
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle274
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1105
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1107
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1113
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1116
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1108
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1110
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleDescentToSubfield

@[expose] public section

section

open NumberField IsDedekindDomain
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.PrinSat

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LFun GlobalTheory.SplitWeil

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

def toFun {n : ℕ} (χ : Fin n → (w.adicCompletion E)ˣ →* ℂˣ) :
    IndSp (points (Fin n)) ((GlobalTheory.SmGL.ofChar (GlobalTheory.SmGL.torusChar χ)).comp (leviTorus (w.adicCompletion E) (Fin n)).symm.toMonoidHom)
      →ₗ[ℂ] (GL (Fin n) (w.adicCompletion E) → ℂ) where
  toFun f := f.1.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem toFun_injective {n : ℕ} (χ : Fin n → (w.adicCompletion E)ˣ →* ℂˣ) : Function.Injective (toFun w χ) :=
  fun _ _ h => Subtype.ext (Subtype.ext h)

theorem toFun_intertwines {n : ℕ} (χ : Fin n → (w.adicCompletion E)ˣ →* ℂˣ) (g) (f) :
    toFun w χ (prinSeries χ g f) = rightReg ℂ _ ℂ g (toFun w χ f) := rfl

theorem hasSatGL_prinSeries {n : ℕ} (α : Fin n → ℂˣ) :
    HasSatGL w (prinSeries fun i => unrChar (w.adicCompletion E) (α i)) (Finset.univ.val.map α) := by
  have hK : KO (w.adicCompletion E) (Fin n) = KGL w (n := n) := SphCompletion.KO_completion w n
  constructor
  · obtain ⟨φ, h, h1, -⟩ := Formalism.UG.Final.SphericalExists E w n (fun i => (α i : ℂ)) fun i => (α i).ne_zero
    obtain ⟨f, hf, rfl⟩ := (SphCompletion.isSpherical_iff E w n α _).1 h
    refine (Submodule.ne_bot_iff _).2 ⟨f, hK ▸ hf, fun h0 => ?_⟩
    subst h0
    simp at h1
  · intro x hx h0
    have hx' : x ∈ fixed (prinSeries fun i => unrChar (w.adicCompletion E) (α i)) (KO (w.adicCompletion E) (Fin n)) :=
      hK ▸ hx
    have hs := (SphCompletion.isSpherical_iff E w n α x.1.1).2 ⟨x, hx', rfl⟩
    exact IsSatVecGL.of_map (toFun w _) (toFun_intertwines w _) (toFun_injective w _)
      (isSatVecGL_of_isSpherical hs fun h => h0 (toFun_injective w _ (h.trans (map_zero _).symm)))

end GlobalTheory.PrinSat

namespace GlobalTheory.PrinSat

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_parab_one (g : GL (Fin 1) k) : g ∈ parab k (points (Fin 1)) :=
  mem_parab_iff.2 fun a b _ _ hab => absurd hab (by rw [Subsingleton.elim a b]; exact lt_irrefl _)

theorem cB_one (μ : kˣ →* ℂˣ) (p : parab k (points (Fin 1))) :
    PrinProd.cB (fun _ : Fin 1 => μ) p = μ (Matrix.GeneralLinearGroup.det (p : GL (Fin 1) k)) := by
  rw [PrinProd.cB_eq, Fin.prod_univ_one, Fin.prod_univ_one]
  have h : PrinProd.dg p 0 = Matrix.GeneralLinearGroup.det (p : GL (Fin 1) k) := by
    ext
    rw [PrinProd.val_dg, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_unique]
    rfl
  rw [h]
  simp

def oneEquiv (μ : kˣ →* ℂˣ) (hμ : IsSmoothChar μ) :
    (detRep (Fin 1) μ).Equiv (prinSeries fun _ : Fin 1 => μ) := by
  let Ψ : ℂ →ₗ[ℂ] IndSp (points (Fin 1))
      ((GlobalTheory.SmGL.ofChar (GlobalTheory.SmGL.torusChar fun _ : Fin 1 => μ)).comp (leviTorus k (Fin 1)).symm.toMonoidHom) :=
    { toFun := fun c => ⟨⟨fun g => (μ (Matrix.GeneralLinearGroup.det g) : ℂ) * c, fun p g => by
          show _ = PrinProd.sB (fun _ : Fin 1 => μ) p _
          rw [PrinProd.sB_apply, cB_one]
          beta_reduce
          rw [map_mul, map_mul, Units.val_mul, mul_assoc]⟩,
        MultiIrr.mem_smooth_of_eventually _ (Filter.mem_of_superset
          (IsOpen.mem_nhds (hμ.detChar (n := Fin 1)) (one_mem _)) fun u hu x => by
            have hu' : detChar (Fin 1) μ u = 1 := hu
            show (μ (Matrix.GeneralLinearGroup.det (x * u)) : ℂ) * c = (μ (Matrix.GeneralLinearGroup.det x) : ℂ) * c
            rw [map_mul (Matrix.GeneralLinearGroup.det), map_mul, ← detChar_apply (n := Fin 1) μ u, hu', mul_one])⟩
      map_add' := fun c d => Subtype.ext (Subtype.ext (funext fun g => mul_add _ _ _))
      map_smul' := fun c d => Subtype.ext (Subtype.ext (funext fun g => mul_left_comm _ _ _)) }
  refine Representation.Equiv.mk' ⟨Ψ, fun g => LinearMap.ext fun c => Subtype.ext (Subtype.ext (funext fun x => ?_))⟩
    (fun F => F.1.1 1) (fun c => ?_) (fun F => Subtype.ext (Subtype.ext (funext fun g => ?_)))
  · show (μ (Matrix.GeneralLinearGroup.det x) : ℂ) * (detRep (Fin 1) μ g c) =
      (μ (Matrix.GeneralLinearGroup.det (x * g)) : ℂ) * c
    simp [detRep, ofChar_apply, mul_assoc]
  · show (μ (Matrix.GeneralLinearGroup.det (1 : GL (Fin 1) k)) : ℂ) * c = c
    simp
  · show (μ (Matrix.GeneralLinearGroup.det g) : ℂ) * F.1.1 1 = F.1.1 g
    have h := parInd_law (points (Fin 1)) _ F ⟨g, mem_parab_one g⟩ 1
    rw [mul_one] at h
    rw [h]
    change _ = PrinProd.sB (fun _ : Fin 1 => μ) ⟨g, mem_parab_one g⟩ _
    rw [PrinProd.sB_apply, cB_one]

end GlobalTheory.PrinSat

namespace GlobalTheory.PrinSat

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LFun GlobalTheory.SplitWeil

theorem hasSatGL_of_equiv {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
    {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V}
    {σ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W}
    (e : ρ.Equiv σ) {B : Multiset ℂˣ} (h : HasSatGL w σ B) : HasSatGL w ρ B := by
  let f : V →ₗ[ℂ] W := e.toLinearEquiv.toLinearMap
  have hi : ∀ g y, f (ρ g y) = σ g (f y) := fun g y => e.toIntertwiningMap.isIntertwining _ _ g y
  have inj : Function.Injective f := e.toLinearEquiv.injective
  constructor
  · obtain ⟨y, hy⟩ := h.exists_vec
    have hfy : f (e.toLinearEquiv.symm y) = y := e.toLinearEquiv.apply_symm_apply y
    have hs : IsSatVecGL w ρ (e.toLinearEquiv.symm y) B := IsSatVecGL.of_map f hi inj (by rw [hfy]; exact hy)
    exact (Submodule.ne_bot_iff _).2 ⟨_, hs.2.1, hs.1⟩
  · intro x hx h0
    have hfx : f x ∈ fixed σ (KGL w (n := n)) :=
      GlobalTheory.LGrp.mem_fixed.2 fun g hg => by rw [← hi, GlobalTheory.LGrp.mem_fixed.1 hx g hg]
    exact IsSatVecGL.of_map f hi inj (h.2 _ hfx fun h1 => h0 (inj (h1.trans (map_zero f).symm)))

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem eq_unrChar_of_ord {χ : kˣ →* ℂˣ} (h : IsUnram χ) {ϖ : kˣ} (hϖ : ord k ϖ = 1) :
    χ = unrChar k (χ ϖ) := by
  let o : kˣ →* Multiplicative ℤ := MonoidHom.mk' (fun x => .ofAdd (ord k x)) fun x y => by
    rw [ord_mul, ofAdd_add]
  refine MonoidHom.ext fun x => ?_
  have h1 : o (x / ϖ ^ ord k x) = 1 := by
    rw [map_div, map_zpow, show o ϖ = .ofAdd 1 from congrArg Multiplicative.ofAdd hϖ, ← ofAdd_zsmul,
      smul_eq_mul, mul_one]
    exact div_self' _
  have h2 := h _ (ord_eq_zero_iff.1 (ofAdd_eq_one.1 h1))
  rw [map_div, map_zpow, div_eq_one] at h2
  exact h2

theorem ord_unif {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    ord (w.adicCompletion E) (Formalism.L2.Host.atFin w (Formalism.L2.Host.unif w)) = 1 := by
  have h : Valued.v ((Formalism.L2.Host.atFin w (Formalism.L2.Host.unif w) : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
      WithZero.exp (-1 : ℤ) := Formalism.L2.Host.unif_spec w
  rw [SphCompletion.ord_completion, h, WithZero.log_exp, neg_neg]

end GlobalTheory.PrinSat
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Serre

attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.HomScheme

variable {O : Type} [CommRing O] {X : Type} [AddCommGroup X] [Module O X]

theorem dualTensorHom_lTensor {N N' : Type} [AddCommGroup N] [Module O N] [AddCommGroup N']
    [Module O N'] (g : N →ₗ[O] N') (z : Module.Dual O X ⊗[O] N) (x : X) :
    dualTensorHom O X N' (g.lTensor _ z) x = g (dualTensorHom O X N z x) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul f n => simp [dualTensorHom_apply]
  | add z w hz hw => simp [map_add (f := _), hz, hw]

variable {S : Scheme.{0}} {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H]
  {a : OAct O G} {b : OAct O H}

def homEquiv [Module.Finite O X] [Module.Projective O X] (h : IsTensor H b G a (Module.Dual O X))
    (T : Over S) : Pts b T ≃ₗ[O] (X →ₗ[O] Pts a T) :=
  (h.equiv T).symm.trans (dualTensorHomEquiv O X (Pts a T))

theorem homEquiv_pre [Module.Finite O X] [Module.Projective O X]
    (h : IsTensor H b G a (Module.Dual O X)) {T T' : Over S} (u : T' ⟶ T) (y : Pts b T) (x : X) :
    homEquiv h T' (Pts.pre b u y) x = Pts.pre a u (homEquiv h T y x) := by
  simp only [homEquiv, LinearEquiv.trans_apply]
  rw [h.natural_symm]
  exact dualTensorHom_lTensor _ _ x

theorem tensorObj_dual_represents {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B]
    {O : Type} [CommRing O] (a : OAct O B) (X : Type) [AddCommGroup X] [Module O X]
    [Module.Finite O X] [Module.Projective O X] :
    ∃ u : X → (tensorObj (Module.Dual O X) a ⟶ B),
      (∀ x, IsMonHom (u x)) ∧ (∀ x y, u (x + y) = u x * u y) ∧
      (∀ (o : O) x, u (o • x) = u x ≫ a.act o) ∧
      ∀ (T : Over S) (f : X → (T ⟶ B)), (∀ x y, f (x + y) = f x * f y) →
        (∀ (o : O) x, f (o • x) = f x ≫ a.act o) →
          ∃! c : T ⟶ tensorObj (Module.Dual O X) a, ∀ x, c ≫ u x = f x := by
  let M := Module.Dual O X
  let C := tensorObj M a
  let b := tensorAct M a
  let h : IsTensor C b B a M := isTensor M a
  let Φ := homEquiv h
  let u : X → (C ⟶ B) := fun x => (Φ C (Pts.mk b (𝟙 C)) x).hom
  have hnat : ∀ (T : Over S) (c : T ⟶ C) (x : X), (Φ T (Pts.mk b c) x).hom = c ≫ u x := by
    intro T c x
    have := congrArg Pts.hom (homEquiv_pre h c (Pts.mk b (𝟙 C)) x)
    rw [Pts.hom_pre] at this
    rw [← this]
    congr 3
  refine ⟨u, fun x => ?_, fun x y => ?_, fun o x => ?_, fun T f hadd hsmul => ?_⟩
  · refine isMonHom_of_mul_comp _ fun T p q => ?_
    rw [← hnat, ← hnat, ← hnat, Pts.mk_mul, map_add (f := _), LinearMap.add_apply, Pts.hom_add]
  · change (Φ C _ (x + y)).hom = _
    rw [map_add (f := _), Pts.hom_add]
  · change (Φ C _ (o • x)).hom = _
    rw [map_smul, Pts.hom_smul]
  · let F : X →ₗ[O] Pts a T :=
      { toFun := fun x => Pts.mk a (f x)
        map_add' := fun x y => by rw [hadd]; rfl
        map_smul' := fun o x => by rw [hsmul]; rfl }
    refine ⟨((Φ T).symm F).hom, fun x => ?_, fun c hc => ?_⟩
    · rw [← hnat, Pts.mk_hom, LinearEquiv.apply_symm_apply]
      rfl
    · have : Φ T (Pts.mk b c) = F := by
        ext1 x
        apply Pts.ext
        rw [hnat, hc]
        rfl
      rw [← this, LinearEquiv.symm_apply_apply]
      rfl

theorem exists_homObj_relDim (S : Scheme.{0}) (B : Over S) [GrpObj B] (hB : IsAbelianScheme B)
    (g : ℕ) (hg : SmoothOfRelativeDimension g B.hom)
    {O : Type} [CommRing O] [IsDomain O] [Module.Finite ℤ O] (a : OAct O B) (X : Type)
    [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] :
    ∃ (C : Over S) (_ : GrpObj C) (u : X → (C ⟶ B)), IsAbelianScheme C ∧
      SmoothOfRelativeDimension (Module.finrank O X * g) C.hom ∧
      (∀ x, IsMonHom (u x)) ∧ (∀ x y, u (x + y) = u x * u y) ∧
      (∀ (o : O) x, u (o • x) = u x ≫ a.act o) ∧
      ∀ (T : Over S) (f : X → (T ⟶ B)), (∀ x y, f (x + y) = f x * f y) →
        (∀ (o : O) x, f (o • x) = f x ≫ a.act o) → ∃! c : T ⟶ C, ∀ x, c ≫ u x = f x := by
  haveI := hB.comm
  obtain ⟨u, h1, h2, h3, h4⟩ := tensorObj_dual_represents B a X
  exact ⟨_, inferInstance, u, (isTensor (Module.Dual O X) a).isAbelianScheme hB,
    GlobalTheory.T.smoothOfRelativeDimension_tensorObj_dual_finrank_mul S B O a X g hg, h1, h2, h3, h4⟩

end GlobalTheory.HomScheme
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PinchLift

theorem whiskerLeft_isPullback_affine_closed (S : Scheme.{0}) (E X X' Z Z' : Over S) (p : X' ⟶ X) (i : Z ⟶ X)
    (i' : Z' ⟶ X') (p' : Z' ⟶ Z) (hc : i' ≫ p = p' ≫ i) (hpb : IsPullback i'.left p'.left p.left i.left)
    [IsAffineHom p.left] [IsClosedImmersion i.left] :
    IsPullback (E ◁ i').left (E ◁ p').left (E ◁ p).left (E ◁ i).left ∧ IsAffineHom (E ◁ p).left ∧
      IsClosedImmersion (E ◁ i).left := by
  have hP := GlobalTheory.DualCon.isPullback_whiskerLeft_snd_left E p
  have hI := GlobalTheory.DualCon.isPullback_whiskerLeft_snd_left E i
  have hP' := GlobalTheory.DualCon.isPullback_whiskerLeft_snd_left E p'
  refine ⟨?_, MorphismProperty.of_isPullback hP.flip ‹_›, MorphismProperty.of_isPullback hI.flip ‹_›⟩
  have hout := hP'.flip.paste_horiz hpb
  refine IsPullback.of_right ?_ ?_ hP.flip
  · have h1 : (E ◁ i').left ≫ (snd E X').left = (snd E Z').left ≫ i'.left := by
      rw [← Over.comp_left, ← Over.comp_left]; simp
    have h2 : (E ◁ i).left ≫ (snd E X).left = (snd E Z).left ≫ i.left := by
      rw [← Over.comp_left, ← Over.comp_left]; simp
    rw [h1, h2]; exact hout
  · rw [← Over.comp_left, ← Over.comp_left, ← whiskerLeft_comp, ← whiskerLeft_comp, hc]

theorem glues_whiskerLeft : ∀ (S : Scheme.{0}) (E X X' Z Z' : Over S) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), Flat E.hom → i' ≫ p = p' ≫ i → IsPullback i'.left p'.left p.left i.left → IsAffineHom p.left → IsClosedImmersion i.left → GlobalTheory.PinchLift.Glues p.left i.left i'.left p'.left → IsPullback (E ◁ i').left (E ◁ p').left (E ◁ p).left (E ◁ i).left ∧ IsAffineHom (E ◁ p).left ∧ IsClosedImmersion (E ◁ i).left ∧ GlobalTheory.PinchLift.Glues (E ◁ p).left (E ◁ i).left (E ◁ i').left (E ◁ p').left := by
  intro S E X X' Z Z' p i i' p' hE hc hpb hp hi hg
  obtain ⟨h1, h2, h3⟩ := whiskerLeft_isPullback_affine_closed S E X X' Z Z' p i i' p' hc hpb
  refine ⟨h1, h2, h3, ?_⟩
  refine GlobalTheory.T.pullback_square_sections_glue_of_basis (E ◁ p).left (E ◁ i).left (E ◁ i').left (E ◁ p').left
    {W | IsAffineOpen W ∧ ∃ V : X.left.Opens, IsAffineOpen V ∧ W ≤ (snd E X).left ⁻¹ᵁ V} ?_ ?_
  · intro W x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := X.left.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ ((snd E X).left x)) isOpen_univ
    obtain ⟨_, ⟨W', hW', rfl⟩, hxW', hle⟩ := (E ⊗ X).left.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ ((W ⊓ (snd E X).left ⁻¹ᵁ V : (E ⊗ X).left.Opens) : Set (E ⊗ X).left) from ⟨hx, hxV⟩)
      (W ⊓ (snd E X).left ⁻¹ᵁ V).isOpen
    exact ⟨W', ⟨hW', V, hV, fun y hy => (hle hy).2⟩, hxW', fun y hy => (hle hy).1⟩
  · rintro W ⟨hW, V, hV, hWV⟩
    exact GlobalTheory.T.pinched_functions_glue_affine_flat_baseChange S E X X' Z Z' p i i' p' hE hc hpb hp hi hg V W hV hW hWV

end GlobalTheory.PinchLift
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.LBDescent GlobalTheory.DescNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.DescNorm

theorem twist_descCompat : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (L : LB X) (φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ) (u : Γ(pullback f f, ⊤)ˣ), DescCompat f L φ → DescCompat f L (twist f L φ u) := by
  intro X Y f L φ u hφ z i i' j j' hi hi' hj hj'
  have m : ∀ a b, pullback.fst f f z ∈ L.U a → pullback.snd f f z ∈ L.U b → (𝟙 (pullback f f)) z ∈ chart f L a b :=
    fun a b ha hb => ⟨ha, hb⟩
  simp only [twist, map_mul]
  rw [gm_res (𝟙 _) z le_top (m i' j' hi' hj'), gm_res (𝟙 _) z le_top (m i j hi hj), hφ z i i' j j' hi hi' hj hj']
  ac_rfl

theorem descentDatum_of_additive : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' B : Over (Sp K)) [GrpObj A] [GrpObj A'] [GrpObj B] (q : A ⟶ A') (P : LB (A ⊗ B).left), IsAbelianScheme A → IsAbelianScheme A' → IsAbelianScheme B → IsMonHom q → IsFinite q.left → Flat q.left → Surjective q.left → P.IsLB → IsAdditive P → Triv (ev P (𝟙 A) (1 : A ⟶ B)) → (∀ (T : Over (Sp K)) (x : T ⟶ A), x ≫ q = 1 → Triv (ev P (fst T B ≫ x) (snd T B))) → ∃ φ : ∀ i j, Γ(pullback (q ▷ B).left (q ▷ B).left, GlobalTheory.LBDescent.chart (q ▷ B).left P i j)ˣ, GlobalTheory.LBDescent.DescCompat (q ▷ B).left P φ ∧ GlobalTheory.LBDescent.DescCocycle (q ▷ B).left P φ := by
  intro K _ _ A A' B _ _ _ q P hA hA' hB hq _ _ _ hP hadd hzero hker
  obtain ⟨φ₀, hφ₀⟩ := GlobalTheory.T.exists_descentDatumCompatible_of_lineBundle_iso _ P hP (GlobalTheory.T.lineBundle_iso_pullback_fst_snd_of_additive_trivial_kernel K A A' B q P hA hA' hB hq hP hadd hker)
  obtain ⟨τ, hτ⟩ := hzero
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_globalUnit_twist_normalise_descent_family K A A' B q P τ hP hτ φ₀ hφ₀
  have hc : DescCompat (q ▷ B).left P (twist (q ▷ B).left P φ₀ u) := twist_descCompat _ P φ₀ u hφ₀
  obtain ⟨D, hD⟩ := GlobalTheory.T.exists_descentCocycleDefect_of_compatible _ P _ hP hc
  have h1 := GlobalTheory.T.descentCocycleDefect_normalised_eq_one K A A' B q P τ hP _ D hu hD
  have h2 := GlobalTheory.T.globalUnit_tripleFibreProduct_invariant_setGroupCoordZero K A A' B q hB D
  refine ⟨twist (q ▷ B).left P φ₀ u, hc, fun w i j k hi hj hk => ?_⟩
  have e := hD _ (𝟙 _) w i j k hi hj hk
  rw [← h2 w, h1 w, _root_.one_mul, Category.id_comp, Category.id_comp, Category.id_comp] at e
  exact e.symm

end GlobalTheory.DescNorm
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Pinch.Semiloc

theorem exists_basicOpen_cover : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (W : X.Opens), IsAffineOpen W → ∃ (J : Type) (_ : Fintype J) (f : J → Γ(X, W)) (k : J → L.ι), (∀ j, X.basicOpen (f j) ≤ L.U (k j)) ∧ ∀ x ∈ W, ∃ j, x ∈ X.basicOpen (f j) := by
  intro X L hL W hW
  classical
  have h : ∀ x : W, ∃ (f : Γ(X, W)) (i : L.ι), X.basicOpen f ≤ L.U i ∧ (x : X) ∈ X.basicOpen f := by
    intro x
    obtain ⟨i, hi⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hL (x : X)
    obtain ⟨f, hf, hxf⟩ := hW.exists_basicOpen_le (V := L.U i) ⟨x, hi⟩ x.2
    exact ⟨f, i, hf, hxf⟩
  choose f i hf hx using h
  obtain ⟨s, hs⟩ := hW.isCompact.elim_finite_subcover (fun x : W => (X.basicOpen (f x) : Set X))
    (fun x => (X.basicOpen (f x)).isOpen) (fun x hxW => Set.mem_iUnion.2 ⟨⟨x, hxW⟩, hx ⟨x, hxW⟩⟩)
  refine ⟨s, inferInstance, fun j => f j, fun j => i j, fun j => hf j, fun x hx => ?_⟩
  obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.1 (hs hx)
  exact ⟨⟨j, hj⟩, hxj⟩

theorem exists_separating : ∀ (X : Scheme.{0}) (W : X.Opens), IsAffineOpen W → ∀ (F : Set X), F.Finite → F ⊆ W → (∀ x ∈ F, ∀ y ∈ F, y ⤳ x → y = x) → ∃ a : X → Γ(X, W), (∀ x ∈ F, x ∈ X.basicOpen (a x)) ∧ ∀ x ∈ F, ∀ y ∈ F, y ≠ x → y ∉ X.basicOpen (a x) := by
  intro X W hW F hF hFW hsp
  classical
  have hb : ∀ x ∈ F, ∀ y ∈ F, y ≠ x → ∃ b : Γ(X, W), x ∈ X.basicOpen b ∧ y ∉ X.basicOpen b := by
    intro x hx y hy hne
    have hn : ¬ y ⤳ x := fun h => hne (hsp x hx y hy h)
    rw [specializes_iff_forall_open] at hn
    push Not at hn
    obtain ⟨O, hO, hxO, hyO⟩ := hn
    obtain ⟨b, hbO, hxb⟩ := hW.exists_basicOpen_le (V := ⟨O, hO⟩) ⟨x, hxO⟩ (hFW hx)
    exact ⟨b, hxb, fun h => hyO (hbO h)⟩
  choose! b hb1 hb2 using hb
  refine ⟨fun x => ∏ y ∈ hF.toFinset.erase x, b x y, fun x hx => ?_, fun x hx y hy hne h => ?_⟩
  · refine Finset.prod_induction _ (fun c => x ∈ X.basicOpen c) (fun c d hc hd => ?_) ?_ (fun y hy => ?_)
    · rw [Scheme.basicOpen_mul]; exact ⟨hc, hd⟩
    · rw [Scheme.basicOpen_of_isUnit _ isUnit_one]; exact hFW hx
    · obtain ⟨hyx, hyF⟩ := Finset.mem_erase.1 hy
      exact hb1 x hx y (hF.mem_toFinset.1 hyF) hyx
  · have hmem : y ∈ hF.toFinset.erase x := Finset.mem_erase.2 ⟨hne, hF.mem_toFinset.2 hy⟩
    dsimp only at h
    rw [← Finset.mul_prod_erase _ _ hmem, Scheme.basicOpen_mul] at h
    exact hb2 x hx y hy hne h.1

theorem exists_locGen_near_finite : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (W : X.Opens), IsAffineOpen W → ∀ F : Set X, F.Finite → F ⊆ W → ∃ (V : X.Opens) (a : ∀ k, Γ(X, V ⊓ L.U k)ˣ), F ⊆ V ∧ GlobalTheory.Pinch.LocGen L V a := by
  intro X L hL W hW F hF hFW
  classical
  obtain ⟨J, _, f, k, hk, hcov⟩ := exists_basicOpen_cover X L hL W hW
  set F' : Set X := {x | x ∈ F ∧ ∀ y ∈ F, x ⤳ y → y = x} with hF'
  have hF'F : F' ⊆ F := fun x hx => hx.1
  have hF'fin : F'.Finite := hF.subset hF'F
  have hup : ∀ x ∈ F, ∃ x' ∈ F', x ⤳ x' := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.Finite.exists_minimalFor (fun y : X => closure ({y} : Set X)) {y | y ∈ F ∧ x ⤳ y}
      (hF.subset fun y hy => hy.1) ⟨x, hx, specializes_rfl⟩
    refine ⟨i, ⟨hi.1.1, fun y hy hiy => ?_⟩, hi.1.2⟩
    have h1 : closure ({y} : Set X) ⊆ closure {i} := specializes_iff_closure_subset.1 hiy
    have h2 := hi.2 ⟨hy, hi.1.2.trans hiy⟩ h1
    exact ((specializes_iff_closure_subset.2 h2).antisymm hiy).eq
  obtain ⟨a, ha, ha'⟩ := exists_separating X W hW F' hF'fin (hF'F.trans hFW)
    (fun x hx y hy hyx => (hy.2 x hx.1 hyx).symm)
  have hE : ∀ x : X, ∃ e : ∀ j, Γ(X, X.basicOpen (f j)), x ∈ W →
      GlobalTheory.Pinch.IsSecFam L (fun j => X.basicOpen (f j)) k hk e ∧
        ∀ j (h : x ∈ X.basicOpen (f j)), IsUnit ((X.presheaf.germ (X.basicOpen (f j)) x h).hom (e j)) := by
    intro x
    by_cases hx : x ∈ W
    · obtain ⟨e, he⟩ := GlobalTheory.T.exists_lineBundleLocalSectionFamily_unit_at_point X L hL W hW J f k hk x hx
      exact ⟨e, fun _ => he⟩
    · exact ⟨fun _ => 0, fun h => absurd h hx⟩
  choose E hE using hE
  obtain ⟨e, he, heu⟩ := GlobalTheory.T.lineBundleLocalSectionFamily_unit_at_finite_points X L W J (fun j => X.basicOpen (f j)) (fun j => X.basicOpen_le (f j)) k hk F'
    hF'fin a ha ha' E (fun x hx => (hE x (hFW (hF'F hx))).1) (fun x hx => (hE x (hFW (hF'F hx))).2)
  obtain ⟨V, u, hV, hgen⟩ := GlobalTheory.T.exists_localUnitGenerator_of_lineBundleLocalSectionFamily X L hL J (fun j => X.basicOpen (f j)) k hk e he
  refine ⟨V, u, fun x hx => ?_, hgen⟩
  obtain ⟨x', hx', hxx'⟩ := hup x hx
  obtain ⟨j, hj⟩ := hcov x' (hFW (hF'F hx'))
  exact hxx'.mem_open V.isOpen (hV j x' hj (heu x' hx' j hj))

end GlobalTheory.Pinch.Semiloc
end
end

section

open MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.HSChoice GlobalTheory.PencilDisc

theorem _root_.GlobalTheory.T.pencilLinePolynomial_natDegree_le_and_coeff : ∀ (F R : Type) [CommRing F] [CommRing R] [Algebra F R] (D N δ : ℕ) (f : MvPolynomial (Fin (D + 1) × Fin N) F), IsMultiHomogeneous (fun _ => δ) f → ∀ (u : Fin D → Fin N → R) (a b : Fin N → R), (GlobalTheory.PencilDisc.line u a b f).natDegree ≤ δ ∧ (GlobalTheory.PencilDisc.line u a b f).coeff δ = MvPolynomial.aeval (GlobalTheory.HSChoice.join u b) f := by
  first | exact @GlobalTheory.PencilDisc.line_natDegree_le_and_coeff | exact GlobalTheory.PencilDisc.line_natDegree_le_and_coeff | (intros; apply GlobalTheory.PencilDisc.line_natDegree_le_and_coeff <;> assumption)
end
